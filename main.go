package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

/* ---------- 全局计数 ---------- */
var (
	downloaded int64
	total      int64
)

/* ---------- 固定宽度进度条（总宽 60） ---------- */
type simpleBar struct {
	total   int64
	current *int64
	start   time.Time
}

func newBar(total int64) *simpleBar {
	b := &simpleBar{total: total, current: new(int64), start: time.Now()}
	go b.render()
	return b
}

func (b *simpleBar) Add(n int) { atomic.AddInt64(b.current, int64(n)) }

func (b *simpleBar) render() {
	const barWidth = 40
	for {
		cur := atomic.LoadInt64(b.current)
		if cur > b.total {
			cur = b.total
		}
		percent := float64(cur) * 100 / float64(b.total)
		filled := int(percent / 100 * barWidth)
		bar := strings.Repeat("█", filled) + strings.Repeat(" ", barWidth-filled)
		elapsed := time.Since(b.start).Seconds()
		speed := float64(cur) / elapsed
		fmt.Printf("\r[%s] %03d/%03d %.1f%% %.1f seg/s",
			bar, cur, b.total, percent, speed)
		if cur >= b.total {
			fmt.Println()
			break
		}
		time.Sleep(100 * time.Millisecond)
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

func fetchM3U8(rawURL string) (*m3u8Info, error) {
	baseURL, _ := url.Parse(rawURL)

	resp, err := http.Get(rawURL)
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
		mediaSeq int // EXT-X-MEDIA-SEQUENCE 起始序号，默认 0
	)
	sc := bufio.NewScanner(bytes.NewReader(body))
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())

		// master playlist
		if strings.HasPrefix(line, "#EXT-X-STREAM-INF:") {
			isMaster = true
			bwStr := bwFromLine(line)
			if bw, _ := strconv.ParseInt(bwStr, 10, 64); bw > maxBW {
				maxBW = bw
				mediaURL = nextNonEmptyLine(sc)
			}
			continue
		}
		// media playlist
		if strings.HasPrefix(line, "#EXT-X-MEDIA-SEQUENCE:") {
			// 解析全局的起始序号，用于默认 IV 计算
			if v, err := strconv.ParseInt(strings.TrimPrefix(line, "#EXT-X-MEDIA-SEQUENCE:"), 10, 64); err == nil {
				mediaSeq = int(v)
			}
			continue
		}
		if strings.HasPrefix(line, "#EXT-X-KEY:") {
			info.isMedia = true
			kurl := keyURLFromLine(line)
			ivHex := ivFromLine(line)
			k, _ := fetchKey(kurl)
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
		// TS 行：包含 jpg/jpeg 命名但实际为 TS 的切片
		segURL, _ := url.Parse(line)
		fullURL := baseURL.ResolveReference(segURL).String()
		info.segments = append(info.segments, segment{
			url:   fullURL,
			key:   key,
			iv:    iv,
			index: idx,
			// HLS 默认 IV = 128-bit 序列号（后 64 位为该分片的
			// MediaSequence + 局部 index）。不能直接用 idx。
			seq: mediaSeq + idx,
		})
		idx++
	}

	// 如果是 master，选最高码率子流再递归
	if isMaster && mediaURL != "" {
		absMedia := baseURL.ResolveReference(&url.URL{Path: mediaURL}).String()
		fmt.Printf("检测到 master playlist，自动选择最高码率子流：%s\n", absMedia)
		return fetchM3U8(absMedia)
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
func fetchKey(keyURL string) ([]byte, error) {
	if keyURL == "" {
		return nil, fmt.Errorf("empty key url")
	}
	resp, err := http.Get(keyURL)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	return io.ReadAll(resp.Body)
}

/* ---------- 3. AES-128-CBC 解密 ---------- */
func decryptTS(cipherData, key, iv []byte) ([]byte, error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}
	if len(iv) != 16 {
		return nil, fmt.Errorf("bad iv")
	}
	if len(cipherData)%16 != 0 {
		return nil, fmt.Errorf("cipher not 16-aligned")
	}
	plain := make([]byte, len(cipherData))
	mode := cipher.NewCBCDecrypter(block, iv)
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
func downloadSeg(ctx context.Context, seg segment, dst string, bar *simpleBar) error {
	req, _ := http.NewRequestWithContext(ctx, http.MethodGet, seg.url, nil)
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("status=%d", resp.StatusCode)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return err
	}

	// 解密
	if seg.key != nil {
		iv := seg.iv
		if iv == nil {
			iv = makeIV(uint64(seg.seq))
		}
		data, err = decryptTS(data, seg.key, iv)
		if err != nil {
			return err
		}
	}

	if err := os.WriteFile(dst, data, 0644); err != nil {
		return err
	}
	atomic.AddInt64(&downloaded, 1)
	bar.Add(1)
	return nil
}

/* ---------- 6. 合并为 H.264 + AAC 且保持原比例（清洗 N/A） ---------- */
func mergeToMP4(tsDir, outMP4 string) error {
	listFile := filepath.Join(tsDir, "ts.list")
	f, err := os.Create(listFile)
	if err != nil {
		return err
	}
	defer os.Remove(listFile)

	matches, _ := filepath.Glob(filepath.Join(tsDir, "*.ts"))
	sort.Strings(matches)
	for _, m := range matches {
		abs, _ := filepath.Abs(m)
		fmt.Fprintf(f, "file '%s'\n", abs)
	}
	f.Close()

	args := []string{
		"-hide_banner", "-loglevel", "warning",
		"-analyzeduration", "200M", "-probesize", "200M",
		"-f", "concat", "-safe", "0", "-i", listFile,

		// 视频：H.264 + yuv420p + avc1
		"-c:v", "libx264",
		"-preset", "fast",
		"-crf", "20",
		"-vf", "scale=trunc(iw/2)*2:trunc(ih/2)*2,format=yuv420p",
		"-vtag", "avc1",
		"-pix_fmt", "yuv420p",

		// 音频：AAC 44.1 kHz
		"-c:a", "aac", "-b:a", "128k", "-ar", "44100",

		"-map", "0:v:0", "-map", "0:a:0?",
		"-profile:v", "main", "-level", "4.0",
		"-maxrate", "5000k", "-bufsize", "10000k",
		"-g", "50", "-sc_threshold", "0",
		"-force_key_frames", "expr:gte(t,n_forced*2)",
		"-avoid_negative_ts", "make_zero",
		"-fflags", "+genpts+igndts",
		"-movflags", "+faststart",
		outMP4,
	}

	cmd := exec.Command("ffmpeg", args...)
	if data, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("ffmpeg 重编码失败:%w\n%s", err, data)
	}

	// 二次验证：必须有视频流
	probe := exec.Command("ffprobe", "-v", "error", "-select_streams", "v:0",
		"-show_entries", "stream=codec_name", "-of", "csv=p=0", outMP4)
	if out, err := probe.CombinedOutput(); err != nil || strings.TrimSpace(string(out)) == "" {
		return fmt.Errorf("输出文件缺少有效视频流，只有音频: %s", outMP4)
	}
	return nil
}

/* ---------- 7. 探测原始显示比例（严格清洗 N/A） ---------- */
func probeDAR(tsFile string) string {
	out, err := exec.Command("ffprobe", "-v", "error", "-select_streams", "v:0",
		"-show_entries", "stream=display_aspect_ratio", "-of", "csv=p=0", tsFile).Output()
	if err != nil {
		return ""
	}
	// 1. 去空白、去引号、去空字节
	dar := strings.TrimSpace(string(out))
	dar = strings.Trim(dar, "\x00\"")
	// 2. 只保留「数字:数字」格式，其余视为无效
	if dar == "" || dar == "N/A" || !strings.Contains(dar, ":") {
		return ""
	}
	return dar
}

/* ---------- 8. 主流程 ---------- */
func main() {
	if len(os.Args) != 3 {
		log.Fatalf("用法: %s <m3u8_url> <输出文件名.mp4>", os.Args[0])
	}
	m3u8URL := os.Args[1]
	outMP4 := os.Args[2]

	// 1. 递归拉 m3u8
	info, err := fetchM3U8(m3u8URL)
	if err != nil {
		log.Fatalf("拉取 m3u8 失败: %v", err)
	}
	total = int64(len(info.segments))
	fmt.Printf("共 %d 片 ts\n", total)

	// 2. 建目录
	workDir := strings.TrimSuffix(outMP4, filepath.Ext(outMP4))
	os.RemoveAll(workDir)
	os.MkdirAll(workDir, 0755)
	defer os.RemoveAll(workDir)

	// 3. 进度条
	bar := newBar(total)

	// 4. 并发下载
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	errCh := make(chan error, total)
	const maxConcurrent = 64
	sem := make(chan struct{}, maxConcurrent)

	var wg sync.WaitGroup
	for _, seg := range info.segments {
		wg.Add(1)
		go func(s segment) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()

			baseName := filepath.Base(s.url)
			if ext := strings.ToLower(filepath.Ext(baseName)); ext == ".jpg" || ext == ".jpeg" {
				baseName = strings.TrimSuffix(baseName, ext) + ".ts"
			}
			dst := filepath.Join(workDir, fmt.Sprintf("%05d_%s", s.index, baseName))

			if err := downloadSeg(ctx, s, dst, bar); err != nil {
				errCh <- err
				cancel()
			}
		}(seg)
	}
	wg.Wait()
	select {
	case e := <-errCh:
		log.Fatalf("下载出错: %v", e)
	default:
	}

	// 5. 合并（重编码为 H.264 + AAC，保持原比例）

	if err := mergeToMP4(workDir, outMP4); err != nil {
		log.Fatalf("合并失败: %v", err)
	}
	fmt.Printf("完成！Mac 可直接播放：%s\n", outMP4)
}
