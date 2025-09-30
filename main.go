package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"encoding/binary"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"golang.org/x/time/rate"
)

/* ---------- 全局计数 ---------- */
var (
	total int64
)

/* ---------- 固定宽度进度条（总宽 60） ---------- */
type simpleBar struct {
	total   int64
	current int64
	start   time.Time
}

func newBar(total int64) *simpleBar {
	b := &simpleBar{total: total, start: time.Now()}
	go b.render()
	return b
}

func (b *simpleBar) Add(n int) {
	b.current += int64(n)
}

func (b *simpleBar) render() {
	const barWidth = 40
	for {
		cur := b.current
		if cur > b.total {
			cur = b.total
		}
		percent := float64(cur) * 100 / float64(b.total)
		filled := int(percent / 100 * barWidth)
		bar := strings.Repeat("█", filled) + strings.Repeat(" ", barWidth-filled)
		elapsed := time.Since(b.start).Seconds()
		var speed float64
		if elapsed > 0 {
			speed = float64(cur) / elapsed
		}
		fmt.Printf("\r[%s] %03d/%03d %.1f%% %.1f seg/s",
			bar, cur, b.total, percent, speed)
		if cur >= b.total {
			fmt.Println()
			break
		}
		time.Sleep(2 * time.Second)
	}
}

/* ---------- 1. 递归拉 m3u8（master→media→子media） ---------- */
type m3u8Info struct {
	segments []segment
	keyURL   string
	ivHex    string
	isMedia  bool
}

type segment struct {
	url   string
	key   []byte
	iv    []byte
	index int
	seq   int
}

func fetchM3U8(rawURL string, client *http.Client) (*m3u8Info, error) {
	baseURL, _ := url.Parse(rawURL)

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, "GET", rawURL, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("status=%d", resp.StatusCode)
	}
	body, _ := io.ReadAll(resp.Body)

	var (
		isMaster bool
		maxBW    int64
		mediaURL string
		info     m3u8Info
		idx      int
		key      []byte
		iv       []byte
		mediaSeq int
	)
	sc := bufio.NewScanner(bytes.NewReader(body))
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())

		if strings.HasPrefix(line, "#EXT-X-STREAM-INF:") {
			isMaster = true
			bwStr := bwFromLine(line)
			if bw, _ := strconv.ParseInt(bwStr, 10, 64); bw > maxBW {
				maxBW = bw
				mediaURL = nextNonEmptyLine(sc)
			}
			continue
		}
		if strings.HasPrefix(line, "#EXT-X-MEDIA-SEQUENCE:") {
			if v, err := strconv.ParseInt(strings.TrimPrefix(line, "#EXT-X-MEDIA-SEQUENCE:"), 10, 64); err == nil {
				mediaSeq = int(v)
			}
			continue
		}
		if strings.HasPrefix(line, "#EXT-X-KEY:") {
			info.isMedia = true
			kurl := keyURLFromLine(line)
			ivHex := ivFromLine(line)
			k, _ := fetchKey(kurl, client)
			key = k
			if ivHex != "" {
				iv, _ = hex.DecodeString(ivHex)
			} else {
				iv = nil
			}
			continue
		}
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		segURL, _ := url.Parse(line)
		fullURL := baseURL.ResolveReference(segURL).String()

		u, _ := url.Parse(fullURL)
		path := strings.ToLower(u.Path)
		if strings.HasSuffix(path, ".jpg") || strings.HasSuffix(path, ".jpeg") {
			u.Path = strings.TrimSuffix(u.Path, filepath.Ext(u.Path)) + ".ts"
			fullURL = u.String()
		}

		info.segments = append(info.segments, segment{
			url:   fullURL,
			key:   key,
			iv:    iv,
			index: idx,
			seq:   mediaSeq + idx,
		})
		idx++
	}

	if isMaster && mediaURL != "" {
		absMedia := baseURL.ResolveReference(&url.URL{Path: mediaURL}).String()
		fmt.Printf("检测到 master playlist，自动选择最高码率子流：%s\n", absMedia)
		return fetchM3U8(absMedia, client)
	}
	return &info, nil
}

func bwFromLine(line string) string {
	for _, kv := range strings.Split(line, ",") {
		if strings.HasPrefix(kv, "BANDWIDTH=") {
			return strings.TrimPrefix(kv, "BANDWIDTH=")
		}
	}
	return "0"
}

func keyURLFromLine(line string) string {
	if u := strings.Split(line, `URI="`); len(u) > 1 {
		return strings.Split(u[1], `"`)[0]
	}
	return ""
}

func ivFromLine(line string) string {
	if v := strings.Split(line, `IV=0x`); len(v) > 1 {
		return strings.Split(v[1], `,`)[0]
	}
	return ""
}

func nextNonEmptyLine(sc *bufio.Scanner) string {
	for sc.Scan() {
		if l := strings.TrimSpace(sc.Text()); l != "" && !strings.HasPrefix(l, "#") {
			return l
		}
	}
	return ""
}

/* ---------- 2. 下载 key ---------- */
func fetchKey(keyURL string, client *http.Client) ([]byte, error) {
	if keyURL == "" {
		return nil, fmt.Errorf("empty key url")
	}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, "GET", keyURL, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	return io.ReadAll(resp.Body)
}

/* ---------- 3. AES-128-CBC 解密 ---------- */
func decryptTS(cipherData, key, iv []byte) ([]byte, error) {
	var blockCache struct {
		key   []byte
		block cipher.Block
		sync.Mutex
	}
	blockCache.Lock()
	defer blockCache.Unlock()

	if !bytes.Equal(blockCache.key, key) {
		block, err := aes.NewCipher(key)
		if err != nil {
			return nil, err
		}
		blockCache.key = key
		blockCache.block = block
	}

	if len(iv) != 16 {
		return nil, fmt.Errorf("bad iv")
	}
	if len(cipherData)%16 != 0 {
		return nil, fmt.Errorf("cipher not 16-aligned")
	}
	plain := make([]byte, len(cipherData))
	mode := cipher.NewCBCDecrypter(blockCache.block, iv)
	mode.CryptBlocks(plain, cipherData)
	return plain, nil
}

/* ---------- 4. 缺省 IV（大端 128-bit，后 64 位为 seq） ---------- */
func makeIV(seq uint64) []byte {
	iv := make([]byte, 16)
	binary.BigEndian.PutUint64(iv[8:], seq)
	return iv
}

/* ---------- 5. 下载 + 解密（或原样） ---------- */
var bufferPool = sync.Pool{
	New: func() any {
		return make([]byte, 32*1024) // 32KB 缓冲区
	},
}

func downloadSeg(ctx context.Context, seg segment, dst string, bar *simpleBar, client *http.Client, limiter *rate.Limiter) error {
	var lastErr error
	maxRetries := 3

	for attempt := 1; attempt <= maxRetries; attempt++ {
		if err := limiter.Wait(ctx); err != nil {
			return fmt.Errorf("速率限制错误: %v", err)
		}

		reqCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
		defer cancel()

		req, err := http.NewRequestWithContext(reqCtx, "GET", seg.url, nil)
		if err != nil {
			lastErr = fmt.Errorf("创建请求失败: %v", err)
			continue
		}

		req.Header.Set("User-Agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36")

		resp, err := client.Do(req)
		if err != nil {
			lastErr = fmt.Errorf("下载 %s 失败 (尝试 %d/%d): %v", seg.url, attempt, maxRetries, err)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}

		var cipherData []byte
		buf := bufferPool.Get().([]byte)
		defer bufferPool.Put(buf)

		var data bytes.Buffer
		_, err = io.CopyBuffer(&data, resp.Body, buf)
		if err != nil {
			resp.Body.Close()
			lastErr = fmt.Errorf("读取 %s 响应失败 (尝试 %d/%d): %v", seg.url, attempt, maxRetries, err)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}
		resp.Body.Close()

		cipherData = data.Bytes()
		if len(cipherData) == 0 {
			lastErr = fmt.Errorf("空文件 %s (尝试 %d/%d)", seg.url, attempt, maxRetries)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}

		var plainData []byte
		if seg.key != nil {
			iv := seg.iv
			if iv == nil {
				iv = makeIV(uint64(seg.seq))
			}
			plainData, err = decryptTS(cipherData, seg.key, iv)
			if err != nil {
				lastErr = fmt.Errorf("解密 %s 失败 (尝试 %d/%d): %v", seg.url, attempt, maxRetries, err)
				time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
				continue
			}
		} else {
			plainData = cipherData
		}

		tempDst := dst + ".tmp"
		f, err := os.OpenFile(tempDst, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, 0644)
		if err != nil {
			lastErr = fmt.Errorf("打开 %s 失败 (尝试 %d/%d): %v", tempDst, attempt, maxRetries, err)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}
		writer := bufio.NewWriter(f)
		if _, err := writer.Write(plainData); err != nil {
			f.Close()
			lastErr = fmt.Errorf("写入 %s 失败 (尝试 %d/%d): %v", tempDst, attempt, maxRetries, err)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}
		if err := writer.Flush(); err != nil {
			f.Close()
			lastErr = fmt.Errorf("刷新 %s 失败 (尝试 %d/%d): %v", tempDst, attempt, maxRetries, err)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}
		if err := f.Close(); err != nil {
			lastErr = fmt.Errorf("关闭 %s 失败 (尝试 %d/%d): %v", tempDst, attempt, maxRetries, err)
			time.Sleep(time.Duration(attempt) * 500 * time.Millisecond)
			continue
		}

		if _, err := os.Stat(tempDst); err == nil {
			cleanDst := strings.Split(dst, "?")[0]
			if err := os.Rename(tempDst, cleanDst); err != nil {
				return fmt.Errorf("重命名文件失败: %v", err)
			}
			if bar != nil {
				bar.Add(1)
			}
			return nil
		}
	}

	return fmt.Errorf("下载失败，最终错误: %v", lastErr)
}

/* ---------- 6. 合并为 H.264 + AAC 且保持原比例（清洗 N/A） ---------- */
func mergeToMP4(tsDir, outMP4 string) error {
	if err := os.MkdirAll(filepath.Dir(outMP4), 0755); err != nil {
		return fmt.Errorf("创建输出目录失败: %v", err)
	}

	tempMP4 := strings.TrimSuffix(outMP4, ".mp4") + "_temp.mp4"
	listFile := filepath.Join(tsDir, "ts.list")
	absListFile, err := filepath.Abs(listFile)
	if err != nil {
		return fmt.Errorf("获取文件列表绝对路径失败: %v", err)
	}
	log.Printf("文件列表路径: %s\n", absListFile)

	f, err := os.Create(listFile)
	if err != nil {
		return fmt.Errorf("创建文件列表失败: %v", err)
	}
	defer func() {
		f.Close()
		os.Remove(listFile)
	}()

	tsFiles := getTSFiles(tsDir)
	if len(tsFiles) == 0 {
		return fmt.Errorf("没有找到有效的 TS 文件")
	}

	if err := validateTSFiles(tsDir); err != nil {
		return fmt.Errorf("TS 文件验证失败: %v", err)
	}

	for _, file := range tsFiles {
		absFile, err := filepath.Abs(file)
		if err != nil {
			return fmt.Errorf("获取 TS 文件绝对路径失败: %v", err)
		}
		if _, err := f.WriteString(fmt.Sprintf("file '%s'\n", absFile)); err != nil {
			return fmt.Errorf("写入文件列表失败: %v", err)
		}
	}
	if err := f.Close(); err != nil {
		return fmt.Errorf("关闭文件列表失败: %v", err)
	}

	listContent, err := os.ReadFile(listFile)
	if err != nil {
		return fmt.Errorf("读取文件列表失败: %v", err)
	}
	if len(listContent) == 0 {
		return fmt.Errorf("文件列表为空，没有有效的 TS 文件")
	}
	log.Printf("文件列表内容:\n%s\n", listContent)

	if _, err := exec.LookPath("ffmpeg"); err != nil {
		return fmt.Errorf("未找到 ffmpeg，请确保已安装并在 PATH 中: %v", err)
	}

	log.Println("开始合并 TS 文件...")
	absTempMP4, err := filepath.Abs(tempMP4)
	if err != nil {
		return fmt.Errorf("获取临时 MP4 绝对路径失败: %v", err)
	}

	cmd := exec.Command("ffmpeg",
		"-hide_banner",
		"-loglevel", "error",
		"-f", "concat",
		"-safe", "0",
		"-i", absListFile,
		"-c", "copy",
		"-bsf:a", "aac_adtstoasc",
		"-movflags", "+faststart",
		"-fflags", "+igndts",
		"-f", "mp4",
		"-y",
		absTempMP4,
	)

	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Stdout = &stderr

	log.Printf("执行命令: %s\n", strings.Join(cmd.Args, " "))

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Minute)
	defer cancel()

	cmd = exec.CommandContext(ctx, cmd.Path, cmd.Args[1:]...)
	cmd.Stderr = &stderr
	cmd.Stdout = &stderr

	if err := cmd.Start(); err != nil {
		return fmt.Errorf("启动 ffmpeg 失败: %v", err)
	}

	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case <-ctx.Done():
		if err := cmd.Process.Kill(); err != nil {
			log.Printf("警告: 无法终止 ffmpeg 进程: %v", err)
		}
		return fmt.Errorf("ffmpeg 执行超时")
	case err := <-done:
		if err != nil {
			return fmt.Errorf("ffmpeg 执行失败: %v\nFFmpeg 输出:\n%s", err, stderr.String())
		}
	}

	if stderr.Len() > 0 {
		log.Printf("FFmpeg 输出:\n%s\n", stderr.String())
	}

	if _, err := os.Stat(absTempMP4); os.IsNotExist(err) {
		return fmt.Errorf("FFmpeg 未生成输出文件: %s", absTempMP4)
	}

	if err := os.Rename(tempMP4, outMP4); err != nil {
		return fmt.Errorf("重命名输出文件失败: %v", err)
	}

	log.Printf("合并完成: %s\n", outMP4)
	return nil
}

/* ---------- 7. 探测原始显示比例（严格清洗 N/A） ---------- */
func probeDAR(tsFile string) string {
	out, err := exec.Command("ffprobe", "-v", "error", "-select_streams", "v:0",
		"-show_entries", "stream=display_aspect_ratio", "-of", "csv=p=0", tsFile).Output()
	if err != nil {
		return ""
	}
	dar := strings.TrimSpace(string(out))
	dar = strings.Trim(dar, "\x00\"")
	if dar == "" || dar == "N/A" || !strings.Contains(dar, ":") {
		return ""
	}
	return dar
}

/* ---------- 8. 主流程 ---------- */
func main() {
	var maxConcurrent int
	flag.IntVar(&maxConcurrent, "concurrency", runtime.NumCPU()/2, "最大并发下载数")
	flag.Parse()

	if len(os.Args) < 3 {
		log.Fatalf("用法: %s [-concurrency N] <m3u8_url> <输出文件名.mp4>", os.Args[0])
	}
	m3u8URL := os.Args[len(os.Args)-2]
	outMP4 := os.Args[len(os.Args)-1]

	// 创建共享的 HTTP 客户端
	client := &http.Client{
		Transport: &http.Transport{
			MaxIdleConns:        maxConcurrent,
			MaxIdleConnsPerHost: maxConcurrent,
			IdleConnTimeout:     30 * time.Second,
		},
		Timeout: 30 * time.Second,
	}

	// 设置速率限制：每秒最多 10 个请求
	limiter := rate.NewLimiter(rate.Every(100*time.Millisecond), 10)

	// 1. 递归拉 m3u8
	info, err := fetchM3U8(m3u8URL, client)
	if err != nil {
		log.Fatalf("拉取 m3u8 失败: %v", err)
	}
	total = int64(len(info.segments))
	fmt.Printf("共 %d 片 ts\n", total)

	// 2. 建目录，添加随机后缀
	rand.Seed(time.Now().UnixNano())
	workDir := fmt.Sprintf("%s_%d", strings.TrimSuffix(outMP4, filepath.Ext(outMP4)), rand.Intn(1000000))
	log.Printf("创建临时目录: %s\n", workDir)
	os.RemoveAll(workDir)
	if err := os.MkdirAll(workDir, 0755); err != nil {
		log.Fatalf("创建临时目录失败: %v", err)
	}

	// 设置信号处理
	ctx, cancel := context.WithCancel(context.Background())
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	go func() {
		<-sigCh
		log.Println("收到中断信号，取消下载并清理临时目录")
		cancel()                    // 取消所有下载
		time.Sleep(1 * time.Second) // 等待 goroutine 结束
		if err := removeDirWithRetry(workDir, 3, 500*time.Millisecond); err != nil {
			log.Printf("清理临时目录失败: %v", err)
			// 列出剩余文件以便调试
			if files, err := os.ReadDir(workDir); err == nil {
				log.Printf("临时目录 %s 中剩余文件: %v", workDir, files)
			}
		} else {
			log.Printf("成功清理临时目录: %s", workDir)
		}
		os.Exit(1)
	}()

	// 确保正常退出时清理
	defer func() {
		if err := removeDirWithRetry(workDir, 3, 500*time.Millisecond); err != nil {
			log.Printf("清理临时目录失败: %v", err)
			// 列出剩余文件以便调试
			if files, err := os.ReadDir(workDir); err == nil {
				log.Printf("临时目录 %s 中剩余文件: %v", workDir, files)
			}
		} else {
			log.Printf("成功清理临时目录: %s", workDir)
		}
	}()

	// 3. 进度条
	bar := newBar(total)

	// 4. 并发下载
	errCh := make(chan error, total)
	if maxConcurrent < 2 {
		maxConcurrent = 2 // 最低并发数
	}
	sem := make(chan struct{}, maxConcurrent)

	var wg sync.WaitGroup
	for _, seg := range info.segments {
		sem <- struct{}{}
		wg.Go(func() {
			defer func() { <-sem }()

			baseName := filepath.Base(seg.url)
			if ext := strings.ToLower(filepath.Ext(baseName)); ext == ".jpg" || ext == ".jpeg" {
				baseName = strings.TrimSuffix(baseName, ext) + ".ts"
			}
			baseName = strings.Split(baseName, "?")[0]
			dst := filepath.Join(workDir, fmt.Sprintf("%05d_%s", seg.index, baseName))

			if err := downloadSeg(ctx, seg, dst, bar, client, limiter); err != nil {
				errCh <- err
				cancel()
			}
		})
		time.Sleep(200 * time.Millisecond)
	}

	wg.Wait()
	select {
	case e := <-errCh:
		log.Fatalf("下载出错: %v", e)
	default:
	}

	// 5. 合并
	if err := mergeToMP4(workDir, outMP4); err != nil {
		log.Fatalf("合并失败: %v", err)
	}
	fmt.Printf("完成！Mac 可直接播放：%s\n", outMP4)
}

func getTSFiles(tsDir string) []string {
	files, err := os.ReadDir(tsDir)
	if err != nil {
		log.Fatal(err)
	}
	var tsFiles []string
	for _, file := range files {
		if strings.HasSuffix(file.Name(), ".ts") {
			tsFiles = append(tsFiles, filepath.Join(tsDir, file.Name()))
		}
	}
	sort.Slice(tsFiles, func(i, j int) bool {
		nameI := filepath.Base(tsFiles[i])
		nameJ := filepath.Base(tsFiles[j])
		indexI, _ := strconv.Atoi(strings.Split(nameI, "_")[0])
		indexJ, _ := strconv.Atoi(strings.Split(nameJ, "_")[0])
		return indexI < indexJ
	})
	return tsFiles
}

func validateTSFiles(tsDir string) error {
	files, err := os.ReadDir(tsDir)
	if err != nil {
		return err
	}
	for _, file := range files {
		if !strings.HasSuffix(file.Name(), ".ts") {
			continue
		}
		tsFile := filepath.Join(tsDir, file.Name())
		info, err := os.Stat(tsFile)
		if err != nil {
			return fmt.Errorf("无法访问 TS 文件 %s: %v", tsFile, err)
		}
		if info.Size() == 0 {
			return fmt.Errorf("TS 文件 %s 为空", tsFile)
		}
	}
	return nil
}

// removeDirWithRetry 尝试多次删除目录，处理临时锁定的文件
func removeDirWithRetry(dir string, retries int, delay time.Duration) error {
	var lastErr error
	for i := 0; i < retries; i++ {
		err := os.RemoveAll(dir)
		if err == nil {
			return nil
		}
		lastErr = err
		// 列出剩余文件以便调试
		if files, err := os.ReadDir(dir); err == nil {
			log.Printf("尝试 %d/%d 删除目录 %s 失败，剩余文件: %v", i+1, retries, dir, files)
		}
		time.Sleep(delay)
	}
	return fmt.Errorf("删除目录 %s 失败: %v", dir, lastErr)
}
