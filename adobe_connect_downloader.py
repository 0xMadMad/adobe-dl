"""
Adobe Connect Recording Downloader; single-file capture -> download -> render pipeline.

default workflow:
  1) log in to Adobe Connect in the Chrome window opened by this script.
  2) open the target class and capture its traffic while seeking through the recording.
  3) sample the beginning, about 25%, 50%, 75%, and near the end; play briefly at each point.
  4) press Enter in this terminal when done to stop capture and start download/render.

requirements: Python 3.10+, websockets, ffmpeg; pymupdf and pillow for PDF/Whiteboard.
"""

import argparse
import asyncio
import base64
import bisect
import builtins
import json
import math
import os
import re
import shutil
import statistics
import struct
import subprocess
import sys
import time
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from importlib.metadata import version
from pathlib import Path
from urllib.parse import unquote, urljoin, urlparse


CHROME_CANDIDATES = [
    r"C:\Program Files\Google\Chrome\Application\chrome.exe",
    r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
    os.path.expandvars(r"%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe"),
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "google-chrome", "google-chrome-stable", "chromium", "chromium-browser",
]


# Adobe Connect recording/room page: https://host/<room-id>/ (optionally with ?query).
# anything else can be targeted with --match.
ROOM_RX = re.compile(r"^https?://[^/?#]+/(?!(?:common|system|api|admin|static|login|logout|signin|sso|auth|account|home)(?:/|$|[?#]))"
                     r"[A-Za-z0-9_.~-]{5,}/?(?:[?#].*)?$")
SKIP_SCHEMES = ("about:", "chrome:", "chrome-extension:", "devtools:", "data:", "blob:")
MEDIA_ASSET_RX = re.compile(r"(?:/output/|/download|/content|/file|/whiteboard|/share|\.(?:pdf|pptx?|docx?|xlsx?|zip|png|jpe?g|gif|svg|mp3|mp4|flv|webm|m3u8|ts)(?:\?|$))", re.I)


def find_chrome(explicit):
    if explicit:
        return explicit
    for c in CHROME_CANDIDATES:
        if os.path.isfile(c) or shutil.which(c):
            return c
    sys.exit("Chrome not found: pass --chrome PATH")

def parse_class_title(title, limit=80):
    s = (title or "").strip()
    if not s or re.match(r"^https?://", s, re.I):  # untitled tab: Chrome shows the URL
        return "", ""
    s = s.replace("ي", "ی").replace("ك", "ک")
    s = re.sub(r"\s*[-|–—]\s*Adobe Connect\s*$", "", s, flags=re.I)
    part = ""
    m = re.search(r"\s*-\s*s\d{4,}.*$", s, re.I)
    if m:
        nums = re.findall(r"\d+", m.group(0))
        if len(nums) > 2:
            part = nums[-1]
        s = s[:m.start()]
    s = re.sub(r'[<>:"/\\|?*\x00-\x1f\u200e\u200f\u202a-\u202e]', " ", s)
    s = re.sub(r"\s+", " ", s).strip(" .")
    s = s.replace(" ", "_")
    if re.fullmatch(r"(?:CON|PRN|AUX|NUL|COM\d|LPT\d)", s, re.I):
        s = "_" + s
    return s[:limit].strip("_."), (part.zfill(2) if part else "")

def _local_ws_kwargs():
    """websockets >= 15 uses the system proxy by default; never do that for Chrome on localhost."""
    try:
        if int(version("websockets").split(".")[0]) >= 15:
            return {"proxy": None}
    except Exception:
        pass
    return {}


class CDP:
    def __init__(self, ws):
        self.ws = ws
        self.next_id = 0
        self.pending = {}

    async def send(self, method, params=None, session=None):
        self.next_id += 1
        i = self.next_id
        msg = {"id": i, "method": method, "params": params or {}}
        if session:
            msg["sessionId"] = session
        fut = asyncio.get_running_loop().create_future()
        self.pending[i] = fut
        try:
            await self.ws.send(json.dumps(msg))
        except Exception:
            self.pending.pop(i, None)
            return {}
        try:
            return await asyncio.wait_for(fut, 30)
        except asyncio.TimeoutError:
            self.pending.pop(i, None)
            return {}


class State:
    def __init__(self, out: Path):
        self.out = out
        self.attached = set()
        self.target_sessions = {}
        self.conns = {}
        self.n = 0
        self.closed = False
        self.room_rx = ROOM_RX
        self.page = None
        self.rooms = []
        self.http = open(out / "http.jsonl", "w", buffering=1, encoding="utf-8")
        self.rooms_log = open(out / "rooms.jsonl", "w", buffering=1, encoding="utf-8")
        self.assets_dir = out / "assets"
        self.assets_dir.mkdir(exist_ok=True)
        self.requests = {}
        self.responses = {}
        self.asset_tasks = set()

    def note_nav(self, url):
        if self.closed or not url or url.startswith(SKIP_SCHEMES):
            return
        if url == self.page:
            return
        self.page = url
        if self.room_rx.match(url):
            clean = url.split("#")[0]
            if clean not in self.rooms:
                self.rooms.append(clean)
                self.rooms_log.write(json.dumps({"t": time.time(), "url": clean}) + "\n")
                print(f"[room] {clean}", flush=True)

    def open_conn(self, sid, rid, url):
        if self.closed:
            return None
        self.n += 1
        n = self.n
        c = {
            "n": n,
            "ok": False,
            "page": self.page,
            "r": open(self.out / f"ws{n}.recv.bin", "wb"),
            "s": open(self.out / f"ws{n}.sent.bin", "wb"),
            "i": open(self.out / f"ws{n}.idx.jsonl", "w", buffering=1),
            "ro": 0,
            "so": 0,
        }
        (self.out / f"ws{n}.meta.json").write_text(json.dumps({"url": url, "page": self.page}))
        self.conns[(sid, rid)] = c
        print(f"[ws{n}] {url}" + (f"   (page: {self.page})" if self.page else ""), flush=True)
        return c

    def frame(self, sid, p, recv):
        if self.closed:
            return
        key = (sid, p["requestId"])
        c = self.conns.get(key) or self.open_conn(sid, p["requestId"], "?")
        if c is None:
            return
        r = p["response"]
        op = r["opcode"]
        pl = r["payloadData"]
        data = base64.b64decode(pl) if op == 2 else pl.encode("utf-8", "replace")
        d = "r" if recv else "s"
        off = c[d + "o"]
        c[d].write(data)
        c[d].flush()  # keep files readable while the capture is still running
        c[d + "o"] += len(data)
        if recv and op == 1 and not c["ok"] and b"NetConnection.Connect.Success" in data:
            c["ok"] = True
            print(f"[ws{c['n']}] RTMP-over-WebSocket session established", flush=True)
        c["i"].write(json.dumps({"d": d, "t": p["timestamp"], "op": op,
                                 "off": off, "len": len(data)}) + "\n")

    def handshake(self, sid, p):
        c = self.conns.get((sid, p["requestId"]))
        if c is None or self.closed:
            return
        hdrs = p.get("request", {}).get("headers", {})
        (self.out / f"ws{c['n']}.handshake.json").write_text(json.dumps(hdrs), encoding="utf-8")

    def log_http(self, p):
        if self.closed:
            return
        req = p.get("request", {})
        rid = p.get("requestId")
        rec = {"t": p.get("wallTime") or time.time(), "requestId": rid,
               "url": req.get("url"), "method": req.get("method"),
               "type": p.get("type")}
        if rid:
            self.requests[rid] = rec
        self.http.write(json.dumps(rec, ensure_ascii=False) + "\n")

    async def save_response_body(self, cdp, sid, p):
        if self.closed:
            return
        r = p.get("response", {})
        rid = p.get("requestId")
        req = self.requests.get(rid, {})
        url = req.get("url") or r.get("url") or ""
        mime = (r.get("mimeType") or "").lower()
        typ = (req.get("type") or "").lower()
        interesting = (typ in {"document", "media", "xhr", "fetch", "other"} or
                       any(x in mime for x in ("pdf", "image/", "video/", "audio/", "zip", "octet-stream", "xml", "json")) or
                       MEDIA_ASSET_RX.search(url))
        if not interesting or re.search(r"\.(js|css|woff2?|ttf|map)(?:\?|$)", url, re.I):
            return
        try:
            body = await cdp.send("Network.getResponseBody", {"requestId": rid}, sid)
            text = body.get("body") if isinstance(body, dict) else None
            if text is None:
                return
            raw = base64.b64decode(text) if body.get("base64Encoded") else text.encode("utf-8", "replace")
            if len(raw) > 64 * 1024 * 1024:
                return
            safe = re.sub(r"[^A-Za-z0-9._-]+", "_", urlparse(url).path.strip("/"))[-180:] or "asset"
            ext = Path(urlparse(url).path).suffix[:12]
            if not ext:
                ext = {"application/pdf":".pdf", "image/png":".png", "image/jpeg":".jpg",
                       "application/json":".json", "application/xml":".xml"}.get(mime, ".bin")
            fn = f"{int(time.time()*1000)}_{safe}{ext}"
            (self.assets_dir / fn).write_bytes(raw)
            meta = {"requestId": rid, "url": url, "mimeType": mime, "status": r.get("status"),
                    "size": len(raw), "file": f"assets/{fn}", "t": req.get("t")}
            with open(self.out / "assets.jsonl", "a", encoding="utf-8") as fh:
                fh.write(json.dumps(meta, ensure_ascii=False) + "\n")
        except Exception:
            pass

    async def finish_assets(self):
        if self.asset_tasks:
            tasks = list(self.asset_tasks)
            await asyncio.gather(*tasks, return_exceptions=True)
            self.asset_tasks.clear()

    def close(self):
        if self.closed:
            return
        self.closed = True
        for c in self.conns.values():
            for k in ("r", "s", "i"):
                c[k].close()
        self.http.close()
        self.rooms_log.close()


async def setup_session(cdp, st, sid, info, waiting):
    tid = info.get("targetId")
    if tid in st.attached:
        if waiting:
            await cdp.send("Runtime.runIfWaitingForDebugger", {}, sid)
        return
    st.attached.add(tid)
    st.target_sessions[tid] = sid
    if info.get("type") == "page":
        st.note_nav(info.get("url"))
        await cdp.send("Page.enable", {}, sid)
    await cdp.send("Network.enable", {}, sid)
    await cdp.send("Target.setAutoAttach",
                   {"autoAttach": True, "waitForDebuggerOnStart": True, "flatten": True}, sid)
    if waiting:
        await cdp.send("Runtime.runIfWaitingForDebugger", {}, sid)


async def handle_event(cdp, st, m):
    meth = m.get("method")
    p = m.get("params", {})
    sid = m.get("sessionId")
    if meth == "Target.attachedToTarget":
        await setup_session(cdp, st, p["sessionId"], p["targetInfo"],
                            p.get("waitingForDebugger", False))
    elif meth == "Page.frameNavigated":
        fr = p.get("frame", {})
        if not fr.get("parentId"):
            st.note_nav(fr.get("url"))
    elif meth == "Page.navigatedWithinDocument":
        st.note_nav(p.get("url"))
    elif meth == "Network.webSocketCreated":
        st.open_conn(sid, p["requestId"], p["url"])
    elif meth == "Network.webSocketWillSendHandshakeRequest":
        st.handshake(sid, p)
    elif meth == "Network.webSocketFrameReceived":
        st.frame(sid, p, True)
    elif meth == "Network.webSocketFrameSent":
        st.frame(sid, p, False)
    elif meth == "Network.requestWillBeSent":
        st.log_http(p)
    elif meth == "Network.responseReceived":
        st.responses[(sid, p.get("requestId"))] = p
    elif meth == "Network.loadingFinished":
        rp = st.responses.pop((sid, p.get("requestId")), None)
        if rp is not None:
            st.asset_tasks.add(asyncio.create_task(st.save_response_body(cdp, sid, rp)))


async def reader(cdp, st):
    try:
        async for raw in cdp.ws:
            m = json.loads(raw)
            if "id" in m:
                fut = cdp.pending.pop(m["id"], None)
                if fut and not fut.done():
                    fut.set_result(m.get("result", m.get("error", {})))
            else:
                asyncio.create_task(handle_event(cdp, st, m))
    except Exception:
        pass  # Chrome closed the connection: normal end of capture
    finally:
        for fut in cdp.pending.values():
            if not fut.done():
                fut.set_result({})


async def capture(args):
    import websockets

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    for stale in list(out.glob("ws*")) + [out / "http.jsonl", out / "rooms.jsonl", out / "assets.jsonl"]:
        try:
            stale.unlink()
        except OSError:
            pass
    assets_dir = out / "assets"
    if assets_dir.exists():
        shutil.rmtree(assets_dir, ignore_errors=True)
    assets_dir.mkdir(parents=True, exist_ok=True)
    profile = Path(args.profile).resolve()
    urls = args.url or ["about:blank"]
    if not args.url:
        print("No URL given: log in and open the recording by hand; it is detected automatically.",
              flush=True)
    proc = subprocess.Popen([
        find_chrome(args.chrome),
        f"--remote-debugging-port={args.port}",
        f"--user-data-dir={profile}",
        "--no-first-run", "--no-default-browser-check",
        *urls,
    ])
    ver = None
    local = urllib.request.build_opener(urllib.request.ProxyHandler({}))  # never use a system proxy for localhost
    last_err = None
    for i in range(80):
        try:
            ver = json.load(local.open(f"http://127.0.0.1:{args.port}/json/version", timeout=2))
            break
        except Exception as e:
            last_err = e
            if i == 10:
                print(f"[CAPTURE] Still waiting for Chrome's debug port {args.port} ({type(last_err).__name__}). "
                      "If Chrome is already open: close ALL Chrome windows (check Task Manager for chrome.exe) "
                      "and run again.", flush=True)
            await asyncio.sleep(0.5)
    if not ver:
        proc.terminate()
        sys.exit(f"Chrome debug port {args.port} did not open ({type(last_err).__name__}: {last_err}). "
                 "Close every Chrome process, or try another --port.")

    st = State(out)
    if args.match:
        st.room_rx = re.compile(args.match)
    try:
        await run_capture(websockets, ver, st, args)
    finally:
        await st.finish_assets()
        st.close()
    if getattr(args, "close_chrome", False):
        try:
            proc.wait(timeout=10)
        except Exception:
            proc.terminate()
    ok = [f"ws{c['n']}" for c in st.conns.values() if c["ok"]]
    print(f"\nCapture saved: {out}")
    print(f"WebSocket count : {len(st.conns)} observed")
    print(f"Connect.Success : {len(ok)} confirmed ({', '.join(ok) if ok else 'none'})")
    print("Connection inventory:")
    for c in sorted(st.conns.values(), key=lambda item: item["n"]):
        meta_file = out / f"ws{c['n']}.meta.json"
        try:
            meta = json.loads(meta_file.read_text(encoding="utf-8"))
        except Exception:
            meta = {}
        recv_size = (out / f"ws{c['n']}.recv.bin").stat().st_size if (out / f"ws{c['n']}.recv.bin").exists() else 0
        sent_size = (out / f"ws{c['n']}.sent.bin").stat().st_size if (out / f"ws{c['n']}.sent.bin").exists() else 0
        state = "usable handshake" if c["ok"] else "no Connect.Success"
        print(f"  ws{c['n']}: {state}; recv={recv_size:,} B; sent={sent_size:,} B; page={meta.get('page') or '?'}")
    print("Note: observed WebSockets are not the same as independent download sessions.")
    if st.rooms:
        for room in st.rooms:
            print(f"  - {room}")
    print(f"Details: python {Path(__file__).name} --tools analyze {out}")


async def _evaluate_page(cdp, session_id, expression, timeout=8):
    """Evaluate a small, non-secret DOM probe in a page target."""
    try:
        result = await asyncio.wait_for(cdp.send("Runtime.evaluate", {
            "expression": expression, "returnByValue": True, "awaitPromise": True,
            "userGesture": True,
        }, session_id), timeout=timeout)
        return (result.get("result") or {}).get("value")
    except Exception:
        return None


DURATION_PROBE_JS = r"""(() => {
  // Player clock: aria-label="Time Elapsed, 01 hours, 19 minutes, 51 seconds of 01 hours, 20 minutes,  19 seconds"
  // Total duration = the part after " of ". The visible text "01:19:51/01:20:19" is only a fallback.
  const hms = (h, m, s) => Number(h || 0) * 3600 + Number(m || 0) * 60 + Number(s || 0);
  const scan = (doc, depth) => {
    const els = doc.querySelectorAll('[aria-label*="Time Elapsed"], [class*="timeText"]');
    for (const el of els) {
      const a = (el.getAttribute('aria-label') || '').match(
        /\bof\s+(?:(\d+)\s*hours?,?\s*)?(?:(\d+)\s*minutes?,?\s*)?(?:(\d+)\s*seconds?)?\s*$/i);
      if (a && (a[1] || a[2] || a[3])) return hms(a[1], a[2], a[3]);
    }
    for (const el of els) {
      const m = (el.textContent || '').match(/(?:\d+:)?\d+:\d+\s*\/\s*(?:(\d+):)?(\d+):(\d+)/);
      if (m) return hms(m[1], m[2], m[3]);
    }
    if (depth < 4) {
      for (const f of doc.querySelectorAll('iframe, frame')) {
        let d = null;
        try { d = f.contentDocument; } catch (e) {}
        const r = d ? scan(d, depth + 1) : null;
        if (r !== null) return r;
      }
    }
    return null;
  };
  return scan(document, 0);
})()"""


async def _get_tab_title(cdp, room_url):
    infos = (await cdp.send("Target.getTargets")).get("targetInfos", [])
    pages = [t for t in infos
             if t.get("type") == "page" and not (t.get("url") or "").startswith(SKIP_SCHEMES)]
    if room_url:
        key = room_url.split("#")[0]
        for t in reversed(pages):
            if (t.get("url") or "").split("#")[0] == key and t.get("title"):
                return t["title"]
    for t in reversed(pages):
        if t.get("title"):
            return t["title"]
    return ""

async def run_capture(websockets, ver, st, args):
    async with websockets.connect(ver["webSocketDebuggerUrl"], max_size=None, **_local_ws_kwargs()) as ws:
        cdp = CDP(ws)
        rd = asyncio.create_task(reader(cdp, st))
        await cdp.send("Target.setAutoAttach",
                       {"autoAttach": True, "waitForDebuggerOnStart": False, "flatten": True})
        await asyncio.sleep(1.5)
        res = await cdp.send("Target.getTargets")
        for t in res.get("targetInfos", []):
            if t.get("type") == "page" and t["targetId"] not in st.attached:
                await cdp.send("Target.attachToTarget",
                               {"targetId": t["targetId"], "flatten": True})
        if getattr(args, "stop_on_enter", False):
            print("CAPTURE ACTIVE.  sniffing starts as soon as Chrome opens.", flush=True)
            print("- Log in and open the target class in the first tab. Let it play briefly so its URL and traffic are captured.", flush=True)
            print("- This build uses one captured session; download connections are managed automatically by the downloader.", flush=True)
            print("- Credentials are entered only in Chrome and are not requested or logged by this script.", flush=True)
            await asyncio.to_thread(input, "When the class is open and has played briefly, press Enter to finish capture...\n")

            room_url = next((u for u in reversed(st.rooms) if st.room_rx.match(u)), None)
            args.class_title = await _get_tab_title(cdp, room_url)
            print(f"[CLASS] Tab title: {args.class_title!r}", flush=True)
            if getattr(args, "length", None) is None:
                page_targets = (await cdp.send("Target.getTargets")).get("targetInfos", [])
                for info in reversed(page_targets):
                    if info.get("type") not in ("page", "iframe"):
                        continue
                    sid = st.target_sessions.get(info["targetId"])
                    if not sid:
                        continue
                    val = await _evaluate_page(cdp, sid, DURATION_PROBE_JS)
                    if isinstance(val, (int, float)) and 60 < val < 86400:
                        args.length = float(val)
                        print(f"[DURATION] Read from player clock: {_format_duration(val)} ({val:.0f}s).", flush=True)
                        break
                else:
                    print("[DURATION] Player clock not found on any page/frame.", flush=True)
            if not room_url:
                print("[CAPTURE] No class URL detected; captured traffic will still be analyzed.", flush=True)
            if getattr(args, "close_chrome", False):
                await st.finish_assets()
                try:
                    await asyncio.wait_for(cdp.send("Browser.close"), 5)
                except Exception:
                    pass
            rd.cancel()
            await asyncio.gather(rd, return_exceptions=True)
        else:
            print("Capturing. Close Chrome or press Ctrl+C to stop.", flush=True)
            await rd


SIGS = {
    "FLV header": b"FLV\x01",
    "Ogg/Opus": b"OggS",
    "ID3 (mp3)": b"ID3",
    "ADTS AAC (FFF1)": b"\xff\xf1",
    "ADTS AAC (FFF9)": b"\xff\xf9",
    "MP4 ftyp": b"ftyp",
    "RTMP-ish 'connect'": b"connect",
    "AMF 'onMetaData'": b"onMetaData",
    "zlib (78 9c)": b"\x78\x9c",
    "gzip (1f 8b)": b"\x1f\x8b",
    "H264 start code": b"\x00\x00\x00\x01",
}


def analyze(args):
    out = Path(args.dir)
    idxs = sorted(out.glob("ws*.idx.jsonl"), key=lambda p: int(re.findall(r"\d+", p.name)[0]))
    if not idxs:
        sys.exit("no ws*.idx.jsonl files found")
    for idx in idxs:
        base = idx.name.split(".")[0]
        meta = json.loads((out / f"{base}.meta.json").read_text())
        rows = [json.loads(line) for line in idx.open()]
        print("=" * 72)
        print(base, meta["url"].split("?")[0])
        for d, label in (("r", "RECV"), ("s", "SENT")):
            rs = [r for r in rows if r["d"] == d]
            if not rs:
                continue
            lens = [r["len"] for r in rs]
            ops = Counter(r["op"] for r in rs)
            dur = rs[-1]["t"] - rs[0]["t"]
            print(f"\n{label}: frames={len(rs)} bytes={sum(lens)} "
                  f"min/med/max={min(lens)}/{int(statistics.median(lens))}/{max(lens)} "
                  f"opcodes={dict(ops)} span={dur:.1f}s")
            data = (out / f"{base}.{'recv' if d == 'r' else 'sent'}.bin").read_bytes()
            sig = {k: data.count(v) for k, v in SIGS.items() if data.count(v)}
            print("signatures:", sig or "none")
            strs = Counter(m.decode() for m in re.findall(rb"[ -~]{6,}", data[:3_000_000]))
            print("top ascii strings:")
            for s, n in strs.most_common(25):
                print(f"  {n:6d}  {s[:100]}")
            print("first frames (hex):")
            for r in rs[:5]:
                print(f"  op={r['op']} len={r['len']}  {data[r['off']:r['off'] + 48].hex(' ')}")
    print("\nhttp.jsonl: non-static requests")
    seen = set()
    for line in (out / "http.jsonl").open():
        u = json.loads(line)["url"] or ""
        u = u.split("?")[0]
        if re.search(r"\.(js|css|png|jpg|gif|svg|woff2?|ico)$", u) or u in seen:
            continue
        seen.add(u)
        print(" ", u)


REDACT_KEYS = re.compile(
    r'("[^"]*(?:session|ticket|token|cookie|auth|passw|secret|apikey|\bsid\b|_sid\b)[^"]*"\s*:\s*)"[^"]*"',
    re.I)
REDACT_TOK = re.compile(r"[A-Za-z0-9_\-]{20,}|breez\w+")


def redact(text):
    text = REDACT_KEYS.sub(r'\1"<R>"', text)
    return REDACT_TOK.sub("<R>", text)


def load_frames(out, base):
    rows = [json.loads(line) for line in (out / f"{base}.idx.jsonl").open()]
    recv = (out / f"{base}.recv.bin").read_bytes()
    sent = (out / f"{base}.sent.bin").read_bytes()
    frames = []
    for r in rows:
        buf = recv if r["d"] == "r" else sent
        frames.append({**r, "data": buf[r["off"]:r["off"] + r["len"]]})
    return frames


def preview(fr, n=300):
    if fr is None:
        return "-"
    if fr["op"] == 1:
        return redact(fr["data"][: n * 2].decode("utf-8", "replace"))[:n]
    return f"<bin {fr['len']}B {fr['data'][:24].hex(' ')}>"


def inspect(args):
    out = Path(args.dir)
    frames = load_frames(out, args.ws)
    if not frames:
        sys.exit("no frames")
    t0 = frames[0]["t"]
    print(f"== {args.ws}: {len(frames)} frames ==")

    print("\n-- SENT frames (redacted) --")
    for i, f in enumerate([x for x in enumerate(frames) if x[1]["d"] == "s"][:80]):
        idx, fr = f
        print(f"[{idx}] t+{fr['t'] - t0:.2f}s op={fr['op']} {preview(fr, 600)}")

    print("\n-- RECV text frames grouped by shape (largest total bytes first) --")
    shapes = {}
    for i, f in enumerate(frames):
        if f["d"] != "r" or f["op"] != 1:
            continue
        txt = f["data"].decode("utf-8", "replace")
        try:
            o = json.loads(txt)
            if isinstance(o, dict):
                key = (str(o.get("method") or o.get("command") or o.get("type") or "?"),
                       ",".join(sorted(o)))
            else:
                key = ("non-dict", type(o).__name__)
        except Exception:
            key = ("unparsable", txt[:16])
        e = shapes.setdefault(key, {"n": 0, "bytes": 0, "first": i})
        e["n"] += 1
        e["bytes"] += f["len"]
    for key, e in sorted(shapes.items(), key=lambda kv: -kv[1]["bytes"])[:25]:
        print(f"\n{e['n']:6d} frames {e['bytes']:9d} B  method={key[0]}  keys={key[1][:120]}")
        print("   e.g.", preview(frames[e["first"]], 350))

    bins = [(i, f) for i, f in enumerate(frames) if f["d"] == "r" and f["op"] == 2]
    print(f"\n-- RECV binary frames: {len(bins)} --")
    if bins:
        lens = [f["len"] for _, f in bins]
        print(f"total={sum(lens)} B  min/med/max={min(lens)}/{int(statistics.median(lens))}/{max(lens)}")
        print("first 4 bytes histogram:",
              Counter(f["data"][:4].hex() for _, f in bins).most_common(10))
        big = sorted(bins, key=lambda b: -b[1]["len"])[:3]
        show = bins[:15] + [b for b in big if b not in bins[:15]]
        for i, f in show:
            prev = frames[i - 1] if i > 0 else None
            print(f"[{i}] t+{f['t'] - t0:.2f}s len={f['len']} hdr={f['data'][:40].hex(' ')}")
            print(f"      prev: {preview(prev, 220)}")


def run_report(fn, args, filename):
    """Run an analysis function, save its output as UTF-8 in <dir>/<filename>, echo it safely."""
    import contextlib
    import io

    buf = io.StringIO()
    err = None
    try:
        with contextlib.redirect_stdout(buf):
            fn(args)
    except SystemExit as e:
        err = e
    text = buf.getvalue()
    path = Path(args.dir) / filename
    path.write_text(text, encoding="utf-8")
    enc = sys.stdout.encoding or "utf-8"
    print(text.encode(enc, "replace").decode(enc, "replace"))
    print(f"Saved: {path.resolve()}")
    if err is not None:
        raise err

# Stream download and rendering

class UI:
    live = False

    @classmethod
    def width(cls):
        return max(40, shutil.get_terminal_size((100, 20)).columns - 2)

    @classmethod
    def clear(cls):
        if cls.live:
            sys.stdout.write("\r" + " " * cls.width() + "\r")
            cls.live = False

    @classmethod
    def line(cls, text):
        w = cls.width()
        sys.stdout.write("\r" + text[:w].ljust(w))
        sys.stdout.flush()
        cls.live = True

    @classmethod
    def end(cls):
        if cls.live:
            sys.stdout.write("\n")
            sys.stdout.flush()
            cls.live = False


def print(*args, **kw):  # noqa: A001  clears the live progress line before any message
    UI.clear()
    builtins.print(*args, **kw)


DROP_HEADERS = {
    "host", "upgrade", "connection", "sec-websocket-key", "sec-websocket-version",
    "sec-websocket-extensions", "sec-websocket-protocol", "accept-encoding",
    "content-length",
}



# Capture Access
def load_capture(cap: Path, ws: str):
    rows = [json.loads(line) for line in (cap / f"{ws}.idx.jsonl").open()]
    recv = (cap / f"{ws}.recv.bin").read_bytes()
    sent = (cap / f"{ws}.sent.bin").read_bytes()
    out = []
    for r in rows:
        buf = recv if r["d"] == "r" else sent
        out.append((r["d"], r["op"], buf[r["off"]:r["off"] + r["len"]]))
    return out


def pick_ws(cap: Path):
    """Pick the richest connection, preferring actual media over control-only sockets."""
    best = None
    best_score = -1
    for ws in list_ws(cap):
        try:
            fr = load_capture(cap, ws)
            nsmap, stats, _, _, _ = scan_ws(fr)
            recv = (cap / f"{ws}.recv.bin").read_bytes()
            score = (100 if b"NetConnection.Connect.Success" in recv else 0)
            score += sum(v[0] for kinds in stats.values() for k, v in kinds.items() if k != 3) * 5
            score += sum(v[1] for kinds in stats.values() for k, v in kinds.items() if k != 3) // 100000
            score += sum(v[0] for kinds in stats.values() for k, v in kinds.items() if k == 3)
            if score > best_score:
                best_score, best = score, ws
        except Exception:
            continue
    return best



def summarize(m):
    if isinstance(m, bytes):
        return f"<binary {len(m)} B>"
    return m[:160].replace("\n", " ")


def load_handshake(cap: Path, ws: str, url: str, cookie):
    headers, subs = {}, None
    hp = cap / f"{ws}.handshake.json"
    if hp.exists():
        raw = json.loads(hp.read_text(encoding="utf-8"))
        for k, v in raw.items():
            if k.lower() == "sec-websocket-protocol":
                subs = [x.strip() for x in v.split(",")]
            elif k.lower() not in DROP_HEADERS:
                headers[k] = v
    else:
        host = urlparse(url).hostname
        headers["Origin"] = f"https://{host}"
        headers["User-Agent"] = "Mozilla/5.0"
    if cookie:
        headers["Cookie"] = cookie
    return headers, subs



# Streams Command
STREAM_RX = re.compile(r"/?(?:cameraVoip|screenshare|camera|screen|ft[a-z]+)\w*?_\d+_\d+")
NAME_RX = re.compile(r'"streamName"\s*:\s*"([^"]+)"')
TIME_NAME = re.compile(r'"startTime"\s*:\s*(\d+)[^{}]{0,200}?"streamName"\s*:\s*"([^"]+)"')
NAME_TIME = re.compile(r'"streamName"\s*:\s*"([^"]+)"[^{}]{0,200}?"startTime"\s*:\s*(\d+)')


def collect_streams(frames):
    names, starts = Counter(), {}
    for d, op, data in frames:
        if op != 1:
            continue  # names the browser itself requested (sent frames) count too
        txt = data.decode("utf-8", "replace")
        for m in STREAM_RX.findall(txt):
            names[m if m.startswith("/") else "/" + m] += 1
        for m in NAME_RX.findall(txt):
            names[m] += 1
        for t, n in TIME_NAME.findall(txt):
            starts.setdefault(n, int(t))
        for n, t in NAME_TIME.findall(txt):
            starts.setdefault(n, int(t))
    return names, starts


def list_ws(cap: Path):
    files = sorted(cap.glob("ws*.idx.jsonl"), key=lambda p: int(re.findall(r"\d+", p.name)[0]))
    return [p.name.split(".")[0] for p in files]


VIDEO_CODECS = {2: "H263", 3: "ScreenVideo", 4: "VP6", 5: "VP6+alpha", 6: "ScreenVideo2", 7: "H264"}
MEDIA_URL_RX = re.compile(r"\.(flv|mp4|f4v|m4v|mp3|zip|swf|xml|m3u8|webm|ts)(\?|$)|/output/|download|/stream",
                          re.I)


def scan_ws(frames):
    """Per nsId: stream name (from frames the browser sent) and what binary kinds it carried."""
    nsmap, stats, shapes, nt, nb = {}, {}, Counter(), 0, 0
    for d, op, data in frames:
        if op == 1:
            nt += 1
            for o in parse_json_objects(data.decode("utf-8", "replace")):
                if not isinstance(o, dict):
                    continue
                shapes[str(o.get("method") or o.get("cmdString") or o.get("type") or "?")] += 1
                if o.get("nsId") and o.get("streamName"):
                    nsmap.setdefault(o["nsId"], o["streamName"])
        elif op == 2 and d == "r":
            nb += 1
            p = parse_binary(data)
            if p is None:
                continue
            kind, ts, ns, payload = p
            e = stats.setdefault(ns, {}).setdefault(kind, [0, 0, ts, ts, payload[0] if payload else None])
            e[0] += 1
            e[1] += len(data)
            e[2], e[3] = min(e[2], ts), max(e[3], ts)
    return nsmap, stats, shapes, nt, nb


def cmd_peek(a):
    """Show what the browser really received for one stream: metadata, first-byte histogram, first frames."""
    cap = Path(a.cap)
    ns = ws = frames = None
    for cand in (list_ws(cap) if a.ws == "auto" else [a.ws]):
        fr = load_capture(cap, cand)
        nm = scan_ws(fr)[0]
        ns = next((k for k, v in nm.items() if v == a.stream), None)
        if ns:
            ws, frames = cand, fr
            break
    if ns is None:
        sys.exit(f"{a.stream} was not requested on any connection in {cap}")
    print(f"{ws}: {a.stream} = {ns}")
    for d, op, data in frames:
        if op != 1:
            continue
        for o in parse_json_objects(data.decode("utf-8", "replace")):
            if isinstance(o, dict) and o.get("nsId") == ns and o.get("cmdString") in ("onMetaData", "onStatus", "onTextData"):
                print(("sent " if d == "s" else "recv ") + json.dumps(o)[:600])
            elif isinstance(o, dict) and o.get("nsId") == ns and o.get("method") in ("onStatus", "play", "createNetStream"):
                print(("sent " if d == "s" else "recv ") + json.dumps(o)[:400])
    rows = []
    for d, op, data in frames:
        if d == "r" and op == 2:
            p = parse_binary(data)
            if p and p[2] == ns:
                rows.append(p)
    print(f"\n{len(rows)} binary frames for this stream")
    hist = Counter((k, pl[0] if pl else None) for k, _, _, pl in rows)
    print("(kind, first payload byte) histogram:",
          [(k, f"0x{b:02x}" if b is not None else None, n) for (k, b), n in hist.most_common(12)])
    print("first frames: kind ts len hex")
    for k, ts, _, pl in rows[:a.n]:
        print(f"  {k} {ts:8d} {len(pl):6d}  {pl[:24].hex(' ')}")
    big = sorted(rows, key=lambda r: -len(r[3]))[:3]
    print("largest frames:")
    for k, ts, _, pl in big:
        print(f"  {k} {ts:8d} {len(pl):6d}  {pl[:24].hex(' ')}")


def cmd_streams(a):
    cap = Path(a.cap)
    wss = list_ws(cap) if a.ws == "auto" else [a.ws]
    if not wss:
        print("no ws*.idx.jsonl in", cap)
        return
    other_kinds, found = Counter(), False
    for ws in wss:
        frames = load_capture(cap, ws)
        url = json.loads((cap / f"{ws}.meta.json").read_text()).get("url", "?").split("?")[0]
        ok = b"NetConnection.Connect.Success" in (cap / f"{ws}.recv.bin").read_bytes()
        nsmap, stats, shapes, nt, nb = scan_ws(frames)
        names, starts = collect_streams(frames)
        print(f"\n{ws}  {url}  text={nt} binary={nb}  Connect.Success={'yes' if ok else 'no'}")
        if names:
            found = True
            print("  stream name, mentions, startTime(ms) if present:")
            for n, c in sorted(names.items()):
                print(f"    {n:38s} {c:5d}  {starts.get(n, '-')}")
        for ns, kinds in sorted(stats.items()):
            found = True
            print(f"  {ns}  stream={nsmap.get(ns, '?')}")
            for k, (n, size, t0, t1, fb) in sorted(kinds.items()):
                vc = VIDEO_CODECS.get(fb & 0x0F) if fb is not None and k != 3 else None
                note = f"  looks like video ({vc})" if vc else ("  audio (default map 3=8)" if k == 3 else "")
                if k != 3:
                    other_kinds[k] += n
                print(f"    kind {k}: {n} frames, {size / 1e6:.1f} MB, ts {t0 / 1000:.0f}-{t1 / 1000:.0f}s{note}")
        if not names and not stats:
            print("  no stream names and no media frames on this connection.")
            if shapes:
                print("  message types:", dict(shapes.most_common(10)))
    hp = cap / "http.jsonl"
    if hp.exists():
        seen = []
        for line in hp.open(encoding="utf-8"):
            u = (json.loads(line).get("url") or "").split("#")[0]
            u0 = u.split("?")[0]
            if MEDIA_URL_RX.search(u) and not re.search(r"\.(js|css|png|jpg|gif|svg|woff2?)$", u0) and u0 not in seen:
                seen.append(u0)
        if seen:
            print("\nHTTP requests that may carry media/content (check these if the picture is not in a stream):")
            for u in seen[:30]:
                print(" ", u)
    if other_kinds:
        k = other_kinds.most_common(1)[0][0]
        print(f"\nnon-audio binary kind seen: {k}. Download the stream that carries it with: --map 3=8,{k}=9")
    elif not found:
        print("\nNothing media-like in this capture. Capture again and let the picture play for a while "
              "(seek to a part where it is visible) before closing Chrome.")



# Flv
def flv_header(audio=True, video=False):
    flags = (4 if audio else 0) | (1 if video else 0)
    return b"FLV\x01" + bytes([flags]) + (9).to_bytes(4, "big") + (0).to_bytes(4, "big")


def flv_tag(tag_type, ts, data):
    n = len(data)
    return (bytes([tag_type]) + n.to_bytes(3, "big") + (ts & 0xFFFFFF).to_bytes(3, "big")
            + bytes([(ts >> 24) & 0xFF]) + b"\x00\x00\x00" + data + (11 + n).to_bytes(4, "big"))


def parse_binary(b: bytes):
    kind = b[0]
    ts = int.from_bytes(b[1:5], "big")
    n = int.from_bytes(b[5:9], "big")
    if n > 64 or 9 + n > len(b):
        return None
    return kind, ts, b[9:9 + n].decode("ascii", "replace"), b[9 + n:]


def parse_json_objects(txt):
    dec = json.JSONDecoder()
    i, out = 0, []
    while i < len(txt):
        try:
            o, j = dec.raw_decode(txt, i)
        except ValueError:
            break
        out.append(o)
        i = j
        while i < len(txt) and txt[i].isspace():
            i += 1
    return out



# Session / Download
def build_ctx(a):
    import websockets  # noqa: F401  (fail early if missing)

    cap = Path(a.cap)
    ws_name = a.ws
    if ws_name == "auto":
        ws_name = pick_ws(cap)
        if not ws_name:
            sys.exit("no connection with Connect.Success found in the capture")
        print("using", ws_name)

    key = "additional_headers" if int(version("websockets").split(".")[0]) >= 14 else "extra_headers"
    kmap = {}
    for pair in a.map.split(","):
        k, v = pair.split("=")
        kmap[int(k)] = int(v)

    def session_data(name):
        frames = load_capture(cap, name)
        received = (cap / f"{name}.recv.bin").read_bytes()
        if b"NetConnection.Connect.Success" not in received:
            return None
        sent = [d.decode("utf-8", "replace") for dr, op, d in frames if dr == "s" and op == 1]
        ci = next((i for i, t in enumerate(sent) if '"NCFunc"' in t and '"connect"' in t), None)
        if ci is None:
            return None
        meta_path = cap / f"{name}.meta.json"
        if not meta_path.exists():
            return None
        url = json.loads(meta_path.read_text(encoding="utf-8"))["url"]
        headers, subs = load_handshake(cap, name, url, a.cookie)
        kw = {key: headers, "max_size": None, "ping_interval": None}
        if subs:
            kw["subprotocols"] = subs
        return {"name": name, "frames": frames, "url": url, "kw": kw, "pre": sent[:ci + 1]}

    primary = session_data(ws_name)
    if primary is None:
        sys.exit(f"{ws_name} has no usable captured Connect.Success session")
    frames = primary["frames"]
    nsmap, stats, _, _, _ = scan_ws(frames)
    observed_duration = {}
    for ns, kinds in stats.items():
        stream_name = nsmap.get(ns)
        if not stream_name:
            continue
        media_ends = [row[3] for kind, row in kinds.items() if kind in (3, 4) and row[0] > 0]
        if media_ends:
            observed_duration[stream_name] = max(media_ends) / 1000.0

    ctx = {
        "session_name": ws_name, "url": primary["url"], "kw": primary["kw"], "pre": primary["pre"], "kmap": kmap,
        "want_video": 9 in kmap.values(), "idle": a.idle, "preload": a.preload,
        "ctimeout": a.connect_timeout, "frames": frames, "frag": not a.no_frag, "bytes": Counter(), "retries": a.retries,
        "conns": a.conns, "texts": {}, "seg": a.seg,
        "overlap": a.overlap, "reuse": a.reuse, "jobs": a.jobs,
        "observed_duration": observed_duration,
    }

    observed_ws = list_ws(cap)
    handshake_ok = []
    for name in observed_ws:
        try:
            if b"NetConnection.Connect.Success" in (cap / f"{name}.recv.bin").read_bytes():
                handshake_ok.append(name)
        except OSError:
            pass
    print(f"[CONNECTIONS] Captured WebSockets: {len(observed_ws)}; successful Connect handshakes: "
          f"{len(handshake_ok)} ({', '.join(handshake_ok) if handshake_ok else 'none'}).", flush=True)
    print(f"[CONNECTIONS] Download will use the selected session '{ws_name}' and automatic connection/worker management.", flush=True)
    return ctx



class Defrag:
    """Video packets arrive fragmented: [2-byte big-endian count of fragments still to come][data].
    A message ends with count 0. The joined data is a normal FLV video tag body."""

    def __init__(self):
        self.buf, self.prev, self.ts = bytearray(), None, 0
        self.bad = 0

    def feed(self, ts, payload):
        if len(payload) < 2:
            return None
        n = int.from_bytes(payload[:2], "big")
        if self.buf and n != self.prev - 1:
            self.bad += 1  # lost or out-of-order fragment: drop the partial message
            self.buf.clear()
        if not self.buf:
            self.ts = ts
        self.buf += payload[2:]
        self.prev = n
        if n:
            return None
        msg, self.buf = bytes(self.buf), bytearray()
        ft, codec = (msg[0] >> 4, msg[0] & 0x0F) if msg else (0, 0)
        if ft not in (1, 2, 3, 4, 5) or codec not in (2, 3, 4, 5, 6, 7):
            self.bad += 1  # does not look like a video tag: began in the middle of a message
            return None
        return self.ts, msg


async def open_session(ctx, label):
    """Open a websocket, replay the captured connect frame, wait for Connect.Success. Retries."""
    import websockets

    last = "unknown"
    # Keep handshake retries bounded; worker-level retries already retry the segment.
    n = max(1, min(ctx["retries"], 3))
    t_open = time.time()
    for attempt in range(1, n + 1):
        seen = []
        ws = None
        try:
            ws = await websockets.connect(ctx["url"], **ctx["kw"])
            for t in ctx["pre"]:
                await ws.send(t)
            t_end = time.time() + ctx["ctimeout"]
            while True:
                left = t_end - time.time()
                if left <= 0:
                    last = f"no Connect response, server sent {len(seen)} message(s): {seen[:3]}"
                    break
                try:
                    m = await asyncio.wait_for(ws.recv(), left)
                except asyncio.TimeoutError:
                    last = f"no Connect response, server sent {len(seen)} message(s): {seen[:3]}"
                    break
                seen.append(summarize(m))
                if isinstance(m, str) and "NetConnection.Connect.Success" in m:
                    print(f"[CONNECT] {label}: connected on attempt {attempt}/{n} after {time.time() - t_open:.1f}s", flush=True)
                    return ws
                if isinstance(m, str) and "NetConnection.Connect" in m:
                    last = f"connect refused: {m[:200]}"
                    break
        except Exception as e:
            last = f"{type(e).__name__}: {e}; server sent {seen[:3]}"
        if ws is not None:
            try:
                await ws.close()
            except Exception:
                pass
        brief = last.split("; server sent", 1)[0]
        if brief.startswith("no Connect response"):
            brief = f"no Connect response ({len(seen)} message(s) received)"
        print(f"[CONNECT] {label}: attempt {attempt}/{n} failed — {brief[:140]}", flush=True)
        if attempt < n:
            await asyncio.sleep(min(3 * attempt, 12))
    raise RuntimeError(
        f"connection was not established after {n} attempts ({last}). "
        "The session ticket may have expired or the server may be limiting parallel connections."
    )



async def _close(ws):
    if ws is not None:
        try:
            await ws.close()
        except Exception:
            pass


async def fetch_segment(ctx, stream, start, length, label, frames, prog, ws=None, nsn=0):
    """Play [start, start+length) of a stream. Frames are appended to `frames` as
    (abs_ms, flv_tag_type, payload). `ws` may be a live session to reuse (--reuse).
    Returns (duration_from_metadata_or_None, ws_still_open_or_None, finished_cleanly)."""
    import websockets

    ns = f"nsID_{nsn}" if ctx["reuse"] else "nsID_0"
    base = int(round(start * 1000))
    end_ms = base + int(length * 1000) if length > 0 else None
    meta = None
    dfrag = Defrag()
    texts = ctx["texts"].setdefault(label, [])
    if ws is None:
        ws = await open_session(ctx, label)
    keep, ka, done = False, None, False
    try:
        async def send(o):
            await ws.send(json.dumps(o, separators=(",", ":")))

        rid = 1
        if ctx["preload"] and not ctx["reuse"]:
            await send({"type": "NCFunc", "method": "call", "method-name": "startLoadEditInfo",
                        "params": {}, "responderId": rid})
            await send({"type": "NCFunc", "method": "call", "method-name": "preloadStreams",
                        "responderId": rid + 1})
            rid += 2
        await send({"type": "NCFunc", "method": "createNetStream", "nsId": ns,
                    "mediaAvailable": True, "streamName": stream})
        await send({"type": "NSFunc", "method": "receiveAudio", "nsId": ns, "action": True})
        if ctx["want_video"]:
            await send({"type": "NSFunc", "method": "receiveVideo", "nsId": ns, "action": True})
        await send({"type": "NSFunc", "method": "play", "nsId": ns, "streamName": stream,
                    "start": start, "length": length, "reset": 1, "mediaAvailable": True})
        await send({"type": "NSFunc", "method": "receiveAudio", "nsId": ns, "action": True})

        async def keepalive():
            n = 0
            while True:
                await asyncio.sleep(5)
                n += 1
                try:
                    await send({"type": "NCFunc", "method": "call", "method-name": "@getStats",
                                "responderId": 1000 + n})
                except Exception:
                    return

        ka = asyncio.create_task(keepalive())
        recent = []
        last_act = time.time()
        while not done:
            try:
                m = await asyncio.wait_for(ws.recv(), ctx["idle"])
            except asyncio.TimeoutError:
                print(f"[{label}] idle {ctx['idle']}s: stopping", flush=True)
                break
            except websockets.ConnectionClosed:
                print(f"[{label}] closed by server after {len(frames)} frames; "
                      f"last text msgs: {recent[-4:]}", flush=True)
                break
            # keep-alive replies must not hide a stream that went silent
            if time.time() - last_act > ctx["idle"]:
                print(f"[{label}] no data for {ctx['idle']}s: stopping", flush=True)
                break
            if isinstance(m, bytes):
                ctx["bytes"]["n"] += len(m)
                p = parse_binary(m)
                if p is None or p[2] != ns:
                    continue
                last_act = time.time()
                kind, ts, _, payload = p
                abs_ms = base + ts
                if end_ms is not None and abs_ms >= end_ms:
                    done = True
                    continue
                tt = ctx["kmap"].get(kind)
                if tt == 9 and ctx["frag"]:
                    out = dfrag.feed(abs_ms, payload)
                    if out:
                        frames.append((out[0], 9, out[1]))
                elif tt is not None:
                    frames.append((abs_ms, tt, payload))
                # RTMP timestamps are relative to this Play request; never let a
                # long-running timestamp inflate progress beyond this segment.
                prog[label] = min(ts, int(length * 1000)) if length > 0 else max(0, ts)
            else:
                if "@getStats" not in m and "_result" not in m[:40]:
                    recent.append(m[:200].replace("\n", " "))
                for o in parse_json_objects(m):
                    if not isinstance(o, dict) or o.get("nsId") != ns:
                        continue
                    last_act = time.time()
                    if o.get("method") == "onStatus":
                        code = (o.get("status") or {}).get("code", "")
                        texts.append(o)
                        if re.search(r"Play\.(Stop|Complete|UnpublishNotify)", code):
                            done = True
                    elif o.get("cmdString") == "onMetaData":
                        arg = (o.get("params") or {}).get("arg_0") or {}
                        if "duration" in arg:
                            meta = float(arg["duration"])
                        texts.append(o)
                    elif o.get("cmdString"):
                        texts.append(o)  # chat / content events etc. for non-media streams
        if done and not frames and not any(o.get("cmdString") not in (None, "onMetaData") for o in texts):
            print(f"[NO MEDIA] {label}: server ended playback without sending audio/video frames. "
                  "This segment will be retried; if it repeats, the stream may end earlier than estimated.",
                  flush=True)
        if length > 0 and done and frames:
            prog[label] = max(prog.get(label, 0), int(length * 1000))
        keep = done and ctx["reuse"]
    finally:
        if ka:
            ka.cancel()
        if not keep:
            await _close(ws)
    return meta, (ws if keep else None), done


async def progress(prog, needed_ms, t0, ctx, limits, total_tasks, completed):
    """Render compact, bounded download progress for narrow Windows terminals."""
    def clock(sec):
        sec = int(max(0, sec))
        h, rem = divmod(sec, 3600)
        m, sec = divmod(rem, 60)
        return f"{h}:{m:02d}:{sec:02d}" if h else f"{m}:{sec:02d}"

    try:
        while True:
            await asyncio.sleep(1)
            done = sum(min(max(0, prog.get(label, 0)), limit)
                       for label, limit in limits.items())
            wall = max(1.0, time.time() - t0)
            mb = ctx["bytes"]["n"] / 1e6
            speed = done / 1000 / wall
            seg_done = len(completed)
            if needed_ms:
                frac = min(1.0, done / needed_ms)
                eta = (needed_ms - done) / 1000 / speed if speed > 0.01 else None
                eta_s = clock(eta) if eta is not None else "--:--"
                bar_width = 16 if UI.width() < 100 else 24
                n = min(bar_width, int(frac * bar_width))
                bar = "=" * n + (">" if n < bar_width else "") + "-" * max(0, bar_width - n - (1 if n < bar_width else 0))
                line = (f"[{bar}] {frac * 100:5.1f}% {seg_done}/{total_tasks} "
                        f"{clock(done / 1000)}/{clock(needed_ms / 1000)} "
                        f"{mb:.1f}MB {speed:.2f}x ETA {eta_s}")
            else:
                line = (f"segments {seg_done}/{total_tasks} {clock(done / 1000)} "
                        f"{mb:.1f}MB {speed:.2f}x")
            UI.line(line)
    finally:
        UI.end()


def is_seq_header(tt, payload):
    if len(payload) < 2 or payload[1] != 0:
        return False
    return (tt == 8 and payload[0] >> 4 == 10) or (tt == 9 and payload[0] & 0x0F == 7)


def script_tag(duration_s):
    """onMetaData with duration, so players show length."""
    amf = (b"\x02\x00\x0aonMetaData" + b"\x08" + (1).to_bytes(4, "big")
           + b"\x00\x08duration" + b"\x00" + struct.pack(">d", duration_s) + b"\x00\x00\x09")
    return flv_tag(18, 0, amf)


def _amf_key(k):
    b = k.encode()
    return len(b).to_bytes(2, "big") + b


def _amf_num(x):
    return b"\x00" + struct.pack(">d", float(x))


def flv_meta_tag(duration, first_byte):
    codec = first_byte >> 4
    rate = {0: 5512, 1: 11025, 2: 22050, 3: 44100}[(first_byte >> 2) & 3]
    size = 16 if (first_byte >> 1) & 1 else 8
    items = [("duration", _amf_num(duration)), ("audiocodecid", _amf_num(codec)),
             ("audiosamplerate", _amf_num(rate)), ("audiosamplesize", _amf_num(size)),
             ("stereo", b"\x01" + bytes([first_byte & 1]))]
    name = b"onMetaData"
    body = (b"\x02" + len(name).to_bytes(2, "big") + name + b"\x08" + len(items).to_bytes(4, "big")
            + b"".join(_amf_key(k) + v for k, v in items) + b"\x00\x00\x09")
    return flv_tag(18, 0, body)


def write_flv(path: Path, frames):
    frames = sorted(frames, key=lambda f: (f[0], 0 if is_seq_header(f[1], f[2]) else 1))
    kept, seen, last_hdr = [], set(), {}
    for ts, tt, payload in frames:
        key = (ts, tt, len(payload), hash(payload))
        if key in seen:
            continue
        seen.add(key)
        if is_seq_header(tt, payload):
            if last_hdr.get(tt) == payload:
                continue
            last_hdr[tt] = payload
        kept.append((ts, tt, payload))
    has_video = any(f[1] == 9 for f in kept)
    vcodec = next((f[2][0] & 0x0F for f in kept if f[1] == 9 and f[2]), None)
    last = kept[-1][0] if kept else 0
    with open(path, "wb") as fh:
        fh.write(flv_header(audio=any(f[1] == 8 for f in kept), video=has_video))
        afirst = next((f[2][0] for f in kept if f[1] == 8 and f[2]), None)
        fh.write(flv_meta_tag(last / 1000, afirst) if afirst is not None else script_tag(last / 1000))
        for ts, tt, payload in kept:
            fh.write(flv_tag(tt, ts, payload))
    gaps = [(kept[i - 1][0], kept[i][0]) for i in range(1, len(kept))
            if kept[i][0] - kept[i - 1][0] > 1500]
    return len(kept), last, gaps, has_video, vcodec


def convert(flv: Path, res, fps=10):
    """Make a playable, seekable file. Screen-share video is VP6/Sorenson (not MP4-compatible):
    re-encode to H.264 at a fixed frame rate (the source is variable and very sparse)."""
    has_video, vcodec = res["video"], res.get("vcodec")
    ff = shutil.which("ffmpeg")
    dst = flv.with_suffix(".mp4" if has_video else ".mp3")
    if not ff:
        print("ffmpeg not found on PATH, so no playable file was made. Install it "
              "(Windows: winget install Gyan.FFmpeg, then reopen the terminal) and run:")
        print("  ffmpeg -i", flv, "-vf fps=10 -c:v libx264 -pix_fmt yuv420p" if has_video
              else "-vn -c:a libmp3lame -q:a 4", dst)
        return
    base = [ff, "-y", "-loglevel", "error", "-i", str(flv)]
    if has_video:
        # Fit the complete source frame into the 1280x720 output canvas,
        # preserving aspect ratio and centering letterbox/pillarbox margins.
        vf = (f"fps={fps:g},scale=1280:720:force_original_aspect_ratio=decrease:"
              "force_divisible_by=2,pad=1280:720:(ow-iw)/2:(oh-ih)/2:color=black")
        cmd = base + ["-vf", vf, "-c:v", "libx264", "-preset", "veryfast", "-tune", "stillimage", "-crf", "28",
                      "-pix_fmt", "yuv420p", "-c:a", "aac", str(dst)]
        if vcodec == 7:  # H.264 can be copied as is
            if subprocess.run(base + ["-c", "copy", str(dst)]).returncode == 0:
                print("converted:", dst)
                return
        subprocess.run(cmd)
    else:
        subprocess.run(base + ["-vn", "-c:a", "libmp3lame", "-q:a", "4", str(dst)])
    print("converted:", dst)


def extract_whiteboard_events(cap: Path):
    """Read playEvent JSON objects from captured WebSocket receive buffers."""
    events = []
    dec = json.JSONDecoder()
    for recv_path in sorted(cap.glob("ws*.recv.bin")):
        raw = recv_path.read_bytes().decode("utf-8", "ignore")
        needle = '{"cmdString":"playEvent"'
        pos = 0
        found = 0
        while True:
            pos = raw.find(needle, pos)
            if pos < 0:
                break
            try:
                obj, end = dec.raw_decode(raw, pos)
            except Exception:
                pos += len(needle)
                continue
            pos = max(end, pos + len(needle))
            if not isinstance(obj, dict) or obj.get("cmdString") != "playEvent":
                continue
            params = obj.get("params")
            if not isinstance(params, dict):
                continue
            event_name = params.get("arg_1")
            arg0 = params.get("arg_0")
            arg2 = params.get("arg_2")
            if not isinstance(event_name, str) or not isinstance(arg2, list):
                continue
            if event_name != "setWBSo" and not re.fullmatch(r"set_WB_So_\d+", event_name):
                continue
            t = arg0.get("time") if isinstance(arg0, dict) else None
            try:
                t = float(t)
            except (TypeError, ValueError):
                continue
            events.append((t, event_name, arg2))
            found += 1
        if found:
            print(f"whiteboard events: {found} from {recv_path.name}")
    # Captures can duplicate the same event in more than one websocket buffer.
    unique = {}
    for t, name, changes in events:
        try:
            key = (t, name, json.dumps(changes, sort_keys=True, separators=(",", ":")))
        except Exception:
            key = (t, name, repr(changes))
        unique[key] = (t, name, changes)
    return sorted(unique.values(), key=lambda e: e[0])



def inspect_pdf_resources(cap: Path):
    """Report PDF descriptors and cached PDF assets without guessing their timeline."""
    descriptors = {}
    dec = json.JSONDecoder()
    for recv_path in sorted(cap.glob("ws*.recv.bin")):
        raw = recv_path.read_bytes().decode("utf-8", "ignore")
        needle = '{"cmdString":"playEvent"'
        pos = 0
        while True:
            pos = raw.find(needle, pos)
            if pos < 0:
                break
            try:
                obj, end = dec.raw_decode(raw, pos)
            except Exception:
                pos += len(needle)
                continue
            pos = max(end, pos + len(needle))
            if not isinstance(obj, dict) or obj.get("cmdString") != "playEvent":
                continue
            params = obj.get("params")
            if not isinstance(params, dict) or params.get("arg_1") != "setContentSo":
                continue
            arg0, changes = params.get("arg_0"), params.get("arg_2")
            t = arg0.get("time") if isinstance(arg0, dict) else None
            try:
                t = float(t) / 1000.0
            except (TypeError, ValueError):
                t = None
            def walk(value):
                if isinstance(value, dict):
                    url = value.get("downloadUrl")
                    name = value.get("theName") or value.get("name") or ""
                    typ = str(value.get("theType") or value.get("type") or "").lower()
                    if isinstance(url, str) and ("pdf" in typ or str(name).lower().endswith(".pdf") or ".pdf" in url.lower()):
                        key = (str(name), url)
                        descriptors.setdefault(key, {"name": str(name), "url": url, "time": t})
                    for v in value.values():
                        walk(v)
                elif isinstance(value, list):
                    for v in value:
                        walk(v)
            walk(changes)
    cached = []
    assets_meta = cap / "assets.jsonl"
    if assets_meta.exists():
        for line in assets_meta.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                row = json.loads(line)
            except Exception:
                continue
            url = str(row.get("url", ""))
            file = row.get("file")
            if file and ("pdf" in str(row.get("mimeType", "")).lower() or ".pdf" in url.lower()):
                path = cap / file
                if path.exists() and path.stat().st_size > 1000:
                    cached.append(path)
    if descriptors:
        print(f"PDF descriptors found: {len(descriptors)}")
        for d in descriptors.values():
            when = f" at {d['time']:.3f}s" if d.get("time") is not None else ""
            print(f"  PDF{when}: {d['name'] or '(unnamed)'}")
    else:
        print("PDF descriptors: none found in captured setContentSo events")
    if cached:
        print(f"cached PDF assets: {len(set(cached))}")
        for path in sorted(set(cached)):
            print("  ", path)
    else:
        print("cached PDF assets: none in cap/assets; a fresh capture while the PDF is open may be needed")
    return list(descriptors.values()), sorted(set(cached))



def download_pdf_descriptors(cap: Path, outdir: Path, descriptors):
    """Download PDFs referenced by setContentSo, not just the viewer's connect.pdf URL."""
    if not descriptors:
        return []
    outdir.mkdir(parents=True, exist_ok=True)
    cookie = capture_cookie(cap)
    allowed = cookie_hosts(cap)
    base = None
    rp = cap / "rooms.jsonl"
    if rp.exists():
        for line in rp.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                base = json.loads(line).get("url")
                if base:
                    break
            except Exception:
                pass
    for mp in ([] if base else sorted(cap.glob("ws*.meta.json"))):
        try:
            base = json.loads(mp.read_text(encoding="utf-8")).get("url")
            if base:
                break
        except Exception:
            pass
    # WebSocket metadata is not guaranteed to contain the room URL. Fall back
    # to the absolute HTTP requests captured from the browser so relative
    # descriptor URLs (for example /system/download?...) become valid URLs.
    host = urlparse(base).hostname if base else None
    scheme = urlparse(base).scheme if base else ""
    if scheme == "wss":
        scheme = "https"
    elif scheme == "ws":
        scheme = "http"
    if not host:
        hp = cap / "http.jsonl"
        if hp.exists():
            for line in hp.read_text(encoding="utf-8", errors="ignore").splitlines():
                try:
                    candidate = json.loads(line).get("url") or ""
                    parsed = urlparse(candidate)
                    if parsed.scheme in ("http", "https") and parsed.hostname:
                        host = parsed.hostname
                        scheme = parsed.scheme
                        break
                except Exception:
                    continue
    origin = f"{scheme or 'https'}://{host}" if host else ""
    saved = []
    for d in descriptors:
        raw_url = d.get("url") or ""
        if not raw_url:
            continue
        url = urljoin(origin + "/", raw_url) if origin else raw_url
        if not urlparse(url).scheme or not urlparse(url).netloc:
            print(f"PDF download skipped for {d.get('name') or 'shared.pdf'}: no server host found; "
                  "check ws*.meta.json or http.jsonl in the capture folder.")
            continue
        name = re.sub(r'[\\/:*?"<>|]+', "_", d.get("name") or "shared.pdf")
        if not name.lower().endswith(".pdf"):
            name += ".pdf"
        dest = outdir / name
        if dest.exists() and dest.stat().st_size > 1000:
            saved.append((d, dest))
            print(f"PDF cached: {dest}")
            continue
        headers = {"User-Agent": "Mozilla/5.0", "Referer": origin + "/"}
        try:
            with open_url(url, headers, cookie, allowed) as r:
                ctype = (r.headers.get("Content-Type") or "").lower()
                data = r.read()
            if "text/html" in ctype or not data.startswith(b"%PDF-"):
                print(f"PDF download failed for {name}: server returned non-PDF ({ctype or 'unknown type'}).")
                continue
            tmp = dest.with_suffix(dest.suffix + ".part")
            tmp.write_bytes(data)
            os.replace(tmp, dest)
            saved.append((d, dest))
            print(f"PDF downloaded: {dest} ({len(data)/1e6:.2f} MB)")
        except Exception as e:
            print(f"PDF download failed for {name}: {type(e).__name__}: {e}")
    return saved


def extract_pdf_page_events(cap: Path, descriptor):
    """Extract explicit PDF page changes from captured playEvent JSON.

    Whiteboard currentPage events are deliberately ignored: they refer to the
    Whiteboard, not the shared PDF. Only events that also look like content/PDF
    events (or contain the matching PDF descriptor) are considered.
    """
    target_name = str(descriptor.get("name") or "").lower()
    target_url = str(descriptor.get("url") or "").lower()
    dec = json.JSONDecoder()
    found = []
    page_keys = {"currentpage", "pagenumber", "pageindex", "currentpagenumber", "pdfpage"}
    for recv_path in sorted(cap.glob("ws*.recv.bin")):
        raw = recv_path.read_bytes().decode("utf-8", "ignore")
        needle = '{"cmdString":"playEvent"'
        pos = 0
        while True:
            pos = raw.find(needle, pos)
            if pos < 0:
                break
            try:
                obj, end = dec.raw_decode(raw, pos)
            except Exception:
                pos += len(needle)
                continue
            pos = max(end, pos + len(needle))
            if not isinstance(obj, dict) or obj.get("cmdString") != "playEvent":
                continue
            params = obj.get("params") or {}
            event_name = str(params.get("arg_1") or "")
            # Whiteboard events use the same field names but have unrelated pages.
            if event_name == "setWBSo" or re.fullmatch(r"set_WB_So_\d+", event_name):
                continue
            arg0, changes = params.get("arg_0"), params.get("arg_2")
            try:
                t = float(arg0.get("time")) / 1000.0
            except (AttributeError, TypeError, ValueError):
                continue
            serialized = json.dumps(changes, ensure_ascii=False).lower()
            looks_related = ("pdf" in serialized or "content" in event_name.lower()
                             or "page" in event_name.lower())
            if target_name and target_name in serialized:
                looks_related = True
            if target_url and target_url in serialized:
                looks_related = True
            if not looks_related:
                continue
            candidates = []
            # Adobe Connect PDF viewer records page navigation inside the
            # memento string (for example: |tPgNum-16|bPgNum-16|).
            # tPgNum is zero-based; convert it to the 1-based page convention
            # used by render_pdf_timeline below.
            if isinstance(changes, list):
                for change in changes:
                    if not isinstance(change, dict) or str(change.get("name", "")).lower() != "memento":
                        continue
                    memento = str(change.get("newValue") or "")
                    match = re.search(r"(?:^|\|)tPgNum-(-?\d+)(?:\||$)", memento)
                    if match:
                        try:
                            candidates.append(int(match.group(1)) + 1)
                        except (TypeError, ValueError):
                            pass
            def walk(value):
                if isinstance(value, dict):
                    for k, v in value.items():
                        if str(k).replace("_", "").lower() in page_keys:
                            try:
                                candidates.append(int(float(v)))
                            except (TypeError, ValueError):
                                pass
                        if str(k).lower() == "name" and str(v).replace("_", "").lower() in page_keys:
                            # Adobe Connect change records store the page in newValue.
                            try:
                                candidates.append(int(float(value.get("newValue"))))
                            except (TypeError, ValueError):
                                pass
                        walk(v)
                elif isinstance(value, list):
                    for item in value:
                        walk(item)
            walk(changes)
            if candidates:
                # Keep the last value in this event; the player uses 1-based page numbers.
                page = candidates[-1]
                if page >= 0:
                    found.append((t, page))
    unique = {}
    for t, page in found:
        unique[(round(t, 3), page)] = (t, page)
    return sorted(unique.values())


def render_pdf_timeline(saved_pdfs, out_path: Path, duration: float, fps: float, cap: Path | None = None):
    """Render PDF pages using recorded page-change timestamps where available.

    Never invent page timing by evenly spreading a document across the whole
    recording. If the capture lacks explicit page changes, hold page 1 and say
    so; this is safer than a convincing but false page timeline.
    """
    if not saved_pdfs:
        return False
    ff = shutil.which("ffmpeg")
    if not ff:
        print("PDF render skipped: ffmpeg not found")
        return False
    try:
        try:
            import pymupdf as fitz  # current PyMuPDF name
        except ImportError:
            import fitz  # older PyMuPDF
        from PIL import Image
    except ImportError:
        print("PDF downloaded, but rendering needs PyMuPDF and Pillow. Run: python -m pip install pymupdf pillow")
        return False
    docs = []
    for desc, path in saved_pdfs:
        try:
            doc = fitz.open(str(path))
            if len(doc):
                start = max(0.0, float(desc.get("time") or 0.0))
                changes = extract_pdf_page_events(cap, desc) if cap else []
                # Only use explicit page changes at/after the document was shared.
                changes = [(t, page) for t, page in changes if t >= start - 0.25 and 1 <= page <= len(doc)]
                docs.append((start, doc, path.name, changes))
        except Exception as e:
            print(f"PDF open failed for {path.name}: {e}")
    if not docs:
        return False
    docs.sort(key=lambda x: x[0])
    origin = docs[0][0]
    local_duration = max(0.1, duration - origin)
    schedule = []
    for di, (recording_start, doc, name, changes) in enumerate(docs):
        start = max(0.0, recording_start - origin)
        end = (docs[di + 1][0] - origin) if di + 1 < len(docs) else local_duration
        end = max(start + 0.1, min(local_duration, end))
        page_events = [(start, 1)]
        if changes:
            page_events.extend((max(start, t - origin), page) for t, page in changes)
            page_events.sort(key=lambda x: x[0])
            compact = []
            for t, page in page_events:
                if compact and abs(compact[-1][0] - t) < 0.02:
                    compact[-1] = (t, page)
                elif not compact or compact[-1][1] != page:
                    compact.append((t, page))
            page_events = compact
            print(f"PDF page timing: {name}, {len(page_events)} timed page states found")
        else:
            print(f"WARNING: no PDF page-change timestamps found for {name}; holding page 1 instead of guessing timing")
        page_events = [(t, max(1, min(len(doc), p)) - 1) for t, p in page_events]
        for pi, (a, page_i) in enumerate(page_events):
            b = page_events[pi + 1][0] if pi + 1 < len(page_events) else end
            a = max(start, min(end, a))
            b = max(a + 0.001, min(end, b))
            if a < end:
                schedule.append((a, b, doc, page_i, name))
        print(f"PDF timeline: {name}, {len(doc)} page(s), {start:.2f}-{end:.2f}s")
    if not schedule:
        return False
    schedule.sort(key=lambda x: x[0])
    width, height = 1280, 720
    cmd = [ff, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
           "-s", f"{width}x{height}", "-r", f"{fps:g}", "-i", "-",
           "-an", "-c:v", "libx264", "-preset", "veryfast", "-crf", "20",
           "-pix_fmt", "yuv420p", "-t", f"{local_duration:g}", "-movflags", "+faststart", str(out_path)]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    try:
        cached_images = {}
        idx = 0
        total = max(1, int(math.ceil(local_duration * fps)))
        for fi in range(total):
            t = fi / fps
            while idx + 1 < len(schedule) and t >= schedule[idx][1]:
                idx += 1
            _, _, doc, page_i, name = schedule[idx]
            key = (id(doc), page_i)
            if key not in cached_images:
                page = doc.load_page(page_i)
                pix = page.get_pixmap(matrix=fitz.Matrix(1.6, 1.6), alpha=False)
                img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                img.thumbnail((width - 48, height - 48))
                canvas = Image.new("RGB", (width, height), "white")
                canvas.paste(img, ((width-img.width)//2, (height-img.height)//2))
                cached_images[key] = canvas.tobytes()
            proc.stdin.write(cached_images[key])
            if fi and fi % max(1, int(fps * 10)) == 0:
                UI.line(f"Rendering PDF: {fi}/{total} frames ({fi * 100 // total}%)")
        UI.end()
        proc.stdin.close()
        rc = proc.wait()
        for _, doc, _, _ in docs:
            doc.close()
        if rc == 0 and out_path.exists() and out_path.stat().st_size > 1000:
            print(f"PDF timeline rendered: {out_path.name}")
            return True
    except Exception as e:
        try:
            proc.kill()
        except Exception:
            pass
        print(f"PDF render failed: {type(e).__name__}: {e}")
    return False

def render_whiteboard_video(cap: Path, out_path: Path, duration: float, fps: float, transparent: bool = False):
    """Render the captured Whiteboard drawing state into a timeline video."""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        print("whiteboard skipped: Pillow is not installed (pip install pillow)")
        return False

    ff = shutil.which("ffmpeg")
    if not ff:
        print("whiteboard skipped: ffmpeg not found")
        return False

    events = extract_whiteboard_events(cap)
    if not events:
        print("whiteboard skipped: no Whiteboard playEvents found in capture")
        return False

    width, height = 1600, 1200
    coord_scale = 2.0
    frame_count = max(1, int(math.ceil(duration * fps)))
    if transparent:
        # Preserve alpha so Whiteboard pen strokes can sit on top of PDF pages.
        cmd = [ff, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgba",
               "-s", f"{width}x{height}", "-r", f"{fps:g}", "-i", "-",
               "-vf", "scale=960:720,pad=1280:720:160:0:color=black@0,format=argb",
               "-an", "-c:v", "qtrle", "-pix_fmt", "argb",
               "-t", f"{duration:g}", str(out_path)]
    else:
        cmd = [ff, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgba",
               "-s", f"{width}x{height}", "-r", f"{fps:g}", "-i", "-",
               "-vf", "scale=960:720,pad=1280:720:160:0:white,format=rgb24",
               "-an", "-c:v", "libx264", "-preset", "veryfast", "-crf", "24",
               "-t", f"{duration:g}", "-movflags", "+faststart", str(out_path)]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    current_page = None
    stores = {}
    ev_i = 0
    cached_frame = None
    dirty = True
    try:
        for frame_i in range(frame_count):
            t_ms = frame_i * 1000.0 / fps
            while ev_i < len(events) and events[ev_i][0] <= t_ms:
                _, event_name, changes = events[ev_i]
                ev_i += 1
                dirty = True
                if event_name == "setWBSo":
                    for change in changes:
                        if not isinstance(change, dict):
                            continue
                        if change.get("name") == "currentPage":
                            try:
                                current_page = int(float(change.get("newValue")))
                            except (TypeError, ValueError):
                                pass
                    continue
                store = event_name.rsplit("_", 1)[-1]
                bucket = stores.setdefault(store, {})
                for change in changes:
                    if not isinstance(change, dict):
                        continue
                    shape_id = str(change.get("name", ""))
                    if not shape_id:
                        continue
                    value = change.get("newValue")
                    code = change.get("code")
                    if code in ("delete", "remove") or value is None:
                        if code in ("delete", "remove") or change.get("oldValue") is not None:
                            bucket.pop(shape_id, None)
                        continue
                    if isinstance(value, dict) and value.get("type"):
                        bucket[shape_id] = value

            if dirty or cached_frame is None:
                img = Image.new("RGBA", (width, height), (0, 0, 0, 0) if transparent else (255, 255, 255, 255))
                draw = ImageDraw.Draw(img)
                for bucket in stores.values():
                    for shape in bucket.values():
                        if shape.get("type") != "pencil":
                            continue
                        try:
                            if current_page is not None and int(float(shape.get("currentPage", current_page))) != current_page:
                                continue
                            x0, y0 = float(shape.get("x", 0)), float(shape.get("y", 0))
                            sw, sh = float(shape.get("width", 0)), float(shape.get("height", 0))
                            pts = shape.get("pts", [])
                            if len(pts) < 2:
                                continue
                            points = [(round((x0 + float(pt.get("x", 0)) * sw) * coord_scale),
                                       round((y0 + float(pt.get("y", 0)) * sh) * coord_scale)) for pt in pts]
                            rgb = int(float(shape.get("strokeCol", 0)))
                            color = ((rgb >> 16) & 255, (rgb >> 8) & 255, rgb & 255)
                            line_width = max(2, round(float(shape.get("strokeWeight", 2)) * coord_scale))
                            draw.line(points, fill=(*color, 255), width=line_width, joint="curve")
                        except (TypeError, ValueError, OverflowError):
                            continue
                cached_frame = img.tobytes()
                dirty = False
            try:
                proc.stdin.write(cached_frame)
            except BrokenPipeError:
                break
            if frame_i and frame_i % max(1, int(fps * 10)) == 0:
                UI.line(f"Rendering Whiteboard: {frame_i}/{frame_count} frames")
        UI.end()
        if proc.stdin:
            proc.stdin.close()
        rc = proc.wait()
    except Exception:
        try:
            if proc.stdin:
                proc.stdin.close()
        except Exception:
            pass
        proc.kill()
        raise
    if rc == 0 and out_path.exists() and out_path.stat().st_size > 1000:
        print(f"Whiteboard rendered: {out_path.name}")
        return True
    print("whiteboard video creation failed")
    return False


def make_class_mp4(audio_items, video_items, out_path: Path, duration, fps=10):
    """Compose every downloaded media stream on one absolute recording timeline."""
    ff = shutil.which("ffmpeg")
    if not ff:
        sys.exit("ffmpeg not found on PATH")
    cmd = [ff, "-y", "-loglevel", "error", "-stats"]
    for path, _ in audio_items:
        cmd += ["-i", str(path)]
    for path, _, _ in video_items:
        cmd += ["-i", str(path)]
    chains, maps = [], []
    audio_labels = []
    for i, (_, start_ms) in enumerate(audio_items):
        delay = max(0, int(round(start_ms)))
        label = f"a{i}"
        chains.append(f"[{i}:a]aresample=48000:async=1000:min_hard_comp=0.1:first_pts=0,adelay={delay}:all=1[{label}]")
        audio_labels.append(f"[{label}]")
    if audio_labels:
        chains.append("".join(audio_labels) +
                      f"amix=inputs={len(audio_labels)}:duration=longest:normalize=0,"
                      "aresample=48000[aout]")
        maps += ["-map", "[aout]"]

    if video_items:
        # Start with a full-duration black canvas. Each source is delayed to its
        # absolute recording start; outside its own frames it contributes nothing,
        # so a later screen-share cannot hide an earlier one with padded black.
        chains.append(f"color=c=black:s=1280x720:r={fps:g}:d={duration:g}[base]")
        cur = "[base]"
        for j, (_, start_ms, name) in enumerate(video_items):
            idx = len(audio_items) + j
            delay = max(0.0, start_ms / 1000.0)
            v = f"sv{j}"
            chains.append(f"[{idx}:v]setpts=PTS-STARTPTS+{delay:.6f}/TB,fps={fps:g},"
                          f"scale=1280:720:force_original_aspect_ratio=decrease:force_divisible_by=2,"
                          f"trim=start=0:end={duration:g}[{v}]")
            nxt = f"mix{j}"
            chains.append(f"{cur}[{v}]overlay=x=(W-w)/2:y=(H-h)/2:eof_action=pass:shortest=0[{nxt}]")
            cur = f"[{nxt}]"
        chains.append(f"{cur}trim=duration={duration:g},setpts=PTS-STARTPTS[vout]")
        maps += ["-map", "[vout]"]

    if not maps:
        print("nothing to mux: no audio or video streams")
        return False
    cmd += ["-filter_complex", ";".join(chains)] + maps
    if video_items:
        cmd += ["-c:v", "libx264", "-preset", "veryfast", "-crf", "26", "-pix_fmt", "yuv420p"]
    if audio_items:
        cmd += ["-c:a", "aac", "-b:a", "128k"]
    cmd += ["-t", str(duration), "-movflags", "+faststart", str(out_path)]
    print(f"Building final video: {out_path.name}")
    ok = subprocess.run(cmd).returncode == 0
    if ok:
        print(f"Final video created: {out_path}")
    else:
        print("Final video creation failed.")
    return ok




# Segment Files On Disk
SEG_REC = struct.Struct(">IBI")  # abs_ms, flv tag type, payload length


def save_seg(path: Path, frames):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "wb") as fh:
        for ts, tt, payload in frames:
            fh.write(SEG_REC.pack(ts & 0xFFFFFFFF, tt, len(payload)))
            fh.write(payload)
    os.replace(tmp, path)  # a .seg file on disk is always complete


def load_seg(path: Path):
    data = path.read_bytes()
    out, i, n = [], 0, len(data)
    while i + SEG_REC.size <= n:
        ts, tt, ln = SEG_REC.unpack_from(data, i)
        i += SEG_REC.size
        out.append((ts, tt, data[i:i + ln]))
        i += ln
    return out


def safe_name(stream):
    return re.sub(r"[^\w.-]+", "_", stream.strip("/")) or "stream"


FT_RX = re.compile(r"^/?ft\w*_\d+_\d+$")



# Planning + Worker Pool
async def plan_stream(ctx, spec, partsdir: Path, sem):
    """Return [(start, length), ...] for one stream. 'split' streams are cut into segments that
    are downloaded in parallel; everything else is a single play to the end."""
    name, kind, start, length = spec
    if kind != "split":
        return [(start, length)]
    durf = partsdir / safe_name(name) / "duration.txt"
    total = None
    if length > 0:
        total = length
    elif durf.exists():
        try:
            total = float(durf.read_text()) - start
        except ValueError:
            pass
    if total is None:
        observed_end = ctx.get("observed_duration", {}).get(name)
        if observed_end is not None and observed_end > start + 5:
            total = observed_end - start
            print(f"[DURATION] {name}: using captured media timestamps ({observed_end:.1f}s); "
                  "skipping connection probes.", flush=True)
    if total is None:
        async with sem:
            meta = None
            for k in range(2):
                try:
                    meta, w, _ = await fetch_segment(ctx, name, start, 5, f"{name}#probe", [], {})
                    await _close(w)
                except Exception as e:
                    print(f"[DURATION] {name}: probe {k + 1}/2 failed ({type(e).__name__}).", flush=True)
                if meta:
                    break
                if k == 0:
                    await asyncio.sleep(2)
        ctx["bytes"].clear()
        if not meta:
            print(f"[DURATION] {name}: no duration metadata or usable timestamp estimate. "
                  "Will try one open-ended download instead of repeatedly probing.", flush=True)
            return [(start, -1)]
        durf.parent.mkdir(parents=True, exist_ok=True)
        durf.write_text(str(meta))
        total = meta - start
    seg = ctx["seg"] if ctx["seg"] and ctx["seg"] > 0 else math.ceil(total / max(1, ctx["jobs"]))
    seg = max(10.0, float(seg))
    ov = max(0.0, float(ctx["overlap"]))
    segs, s = [], start
    while s < start + total - 0.01:
        e = min(start + total, s + seg)
        s0 = max(start, s - ov) if s > start else s
        last = e >= start + total - 0.01
        # the last segment runs to the real end of the stream (metadata duration can be a hair short),
        # unless the user capped the length with --length
        segs.append((s0, -1 if (last and length <= 0) else e - s0))
        s += seg
    return segs


async def worker(ctx, q, prog, failed, completed):
    ws, n = None, 0
    while True:
        try:
            t = q.get_nowait()
        except asyncio.QueueEmpty:
            await _close(ws)
            return
        label, ok = t["label"], False
        for attempt in range(1, 4):
            frames = []
            n += 1
            try:
                meta, ws, done = await fetch_segment(ctx, t["stream"], t["start"], t["length"], label,
                                                     frames, prog, ws, n)
            except Exception as e:
                message = str(e).splitlines()[0]
                print(f"[RETRY] {label}: attempt {attempt}/3 failed — {type(e).__name__}: {message}", flush=True)
                ws = None
                await asyncio.sleep(3 * attempt)
                continue
            if t["kind"] == "text":
                t["path"].parent.mkdir(parents=True, exist_ok=True)
                with open(t["path"], "w", encoding="utf-8") as fh:
                    for o in ctx["texts"].get(label, []):
                        fh.write(json.dumps(o, ensure_ascii=False) + "\n")
                ok = True
                break
            if frames:
                save_seg(t["path"], frames)
                ok = True
                break
            if done:
                # Play.Stop with no media usually means the requested range is beyond
                # the stream's real end. Retrying would consume another ticket/session.
                save_seg(t["path"], [])
                print(f"[END] {label}: server ended playback without media; treating this range as end-of-stream.",
                      flush=True)
                ok = True
                break
            print(f"[RETRY] {label}: received no media frames (attempt {attempt}/3).", flush=True)
            await _close(ws)
            ws = None
            await asyncio.sleep(2 * attempt)
        ctx["texts"].pop(label, None)
        if not ok:
            failed.append(label)
            await _close(ws)
            ws = None
        else:
            if t["length"] > 0:
                prog[label] = max(prog.get(label, 0), int(t["length"] * 1000))
            completed.add(label)


async def run_specs(ctx, specs, partsdir: Path, extras: Path, fresh=False):
    """specs: [(stream, kind, start, length)], kind in split|single|text.
    Plans every stream, then one global pool of ctx['conns'] workers pulls segments from one queue,
    so audio, screen share and extras all download at the same time."""
    if fresh and partsdir.exists():
        shutil.rmtree(partsdir)
    partsdir.mkdir(parents=True, exist_ok=True)
    _drop_empty_holes(partsdir)
    requested = ctx["conns"]
    # Automatic mode scales workers for this capture without requiring multiple browser sessions.
    worker_limit = max(1, min(4, len(specs) if requested <= 0 else requested))
    sem = asyncio.Semaphore(worker_limit)
    plans = await asyncio.gather(*[plan_stream(ctx, sp, partsdir, sem) for sp in specs])
    tasks, parts, needed, unknown, skipped = [], {}, 0, False, 0
    for sp, segs in zip(specs, plans):
        name, kind = sp[0], sp[1]
        plist = parts.setdefault(name, [])
        for i, (s, l) in enumerate(segs):
            if kind == "text":
                path = extras / (safe_name(name) + ".jsonl")
            else:
                path = partsdir / safe_name(name) / f"{i:04d}_{int(s * 1000)}_{int(l * 1000)}.seg"
            plist.append(path)
            if path.exists():
                skipped += 1
                continue
            tasks.append({"stream": name, "kind": kind, "start": s, "length": l,
                          "label": f"{safe_name(name)}#{i}", "path": path})
            if kind != "text":
                if l > 0:
                    needed += int(l * 1000)
                elif kind != "split":
                    unknown = True
    tasks.sort(key=lambda t: (t["kind"] == "split", t["label"]))  # long single streams start first
    segs_total = sum(len(v) for v in parts.values())
    workers = min(worker_limit, len(tasks))
    print(f"{len(specs)} stream(s), {segs_total} segment(s): {skipped} already on disk, "
          f"{len(tasks)} to download, {workers} managed download worker(s) using the selected captured session", flush=True)
    failed = []
    if tasks:
        q = asyncio.Queue()
        for t in tasks:
            q.put_nowait(t)
        prog = {}
        completed = set()
        limits = {t["label"]: int(t["length"] * 1000) for t in tasks if t["length"] > 0}
        t0 = time.time()
        pt = asyncio.create_task(progress(prog, 0 if unknown else needed, t0, ctx,
                                          limits, len(tasks), completed))
        try:
            await asyncio.gather(*[worker(ctx, q, prog, failed, completed) for _ in range(workers)])
        finally:
            pt.cancel()
            await asyncio.sleep(0)
        print(f"download finished in {time.time() - t0:.1f}s, {ctx['bytes']['n'] / 1e6:.0f} MB received", flush=True)
    if failed:
        print(f"[INCOMPLETE] {len(failed)} segment(s) could not be downloaded: {', '.join(failed[:12])}", flush=True)
        print("          Re-run the same command to retry missing segments; completed segments are kept.", flush=True)
    return parts, failed


def merge_stream(parts, out_flv: Path):
    allf, missing = [], 0
    for p in parts:
        if p.exists():
            allf += load_seg(p)
        else:
            missing += 1
    if missing:
        print(f"WARNING {out_flv.name}: {missing} segment(s) missing, the file has holes", flush=True)
    if not allf:
        print(f"no frames for {out_flv.name}; nothing written", flush=True)
        return None
    n, last, gaps, has_video, vcodec = write_flv(out_flv, allf)
    print(f"wrote {out_flv} ({n} frames, {last / 1000:.1f}s, {out_flv.stat().st_size / 1e6:.1f} MB) "
          f"video={'yes' if has_video else 'no'}", flush=True)
    for g in gaps[:5]:
        print(f"  GAP {g[0] / 1000:.1f}s -> {g[1] / 1000:.1f}s", flush=True)
    return {"video": has_video, "vcodec": vcodec}



# Files Shared In The Room (Http)
DOC_RX = re.compile(r"\.(pdf|pptx?|ppsx?|docx?|xlsx?|odp|ods|odt|rtf|txt|csv|zip|rar|7z|mp4|mp3|m4a|flv)$", re.I)
STATIC_RX = re.compile(r"\.(js|css|png|jpe?g|gif|svg|woff2?|ico|map)$", re.I)


def cookie_hosts(cap: Path):
    """Hosts the captured cookie may be sent to: the Connect server seen in the capture."""
    hosts = set()
    for mp in cap.glob("ws*.meta.json"):
        try:
            h = urlparse(json.loads(mp.read_text(encoding="utf-8")).get("url") or "").hostname
            if h:
                hosts.add(h.lower())
        except Exception:
            pass
    for name, only_documents in (("rooms.jsonl", False), ("http.jsonl", True)):
        fp = cap / name
        if not fp.exists():
            continue
        for line in fp.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                row = json.loads(line)
                if only_documents and str(row.get("type") or "").lower() != "document":
                    continue
                h = urlparse(row.get("url") or "").hostname
                if h:
                    hosts.add(h.lower())
            except Exception:
                pass
    return hosts


class _SafeRedirect(urllib.request.HTTPRedirectHandler):
    """Drop the Cookie header when a redirect leaves the allowed hosts."""
    allowed = frozenset()

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new is not None and (urlparse(newurl).hostname or "").lower() not in self.allowed:
            new.headers.pop("Cookie", None)
            new.unredirected_hdrs.pop("Cookie", None)
        return new


def open_url(url, headers, cookie, allowed, timeout=60):
    """urlopen that sends the cookie only to `allowed` hosts (also after redirects)."""
    hdr = dict(headers)
    if cookie and (urlparse(url).hostname or "").lower() in allowed:
        hdr["Cookie"] = cookie
    handler = type("SafeRedirect", (_SafeRedirect,), {"allowed": frozenset(allowed)})()
    return urllib.request.build_opener(handler).open(urllib.request.Request(url, headers=hdr), timeout=timeout)


def capture_cookie(cap: Path):
    """Cookie from a captured handshake. Connections that got Connect.Success come first (newest first):
    early/failed sockets can carry an incomplete session cookie."""
    files = sorted(cap.glob("ws*.handshake.json"), key=lambda p: int(re.findall(r"\d+", p.name)[0]), reverse=True)

    def good(p):
        try:
            return b"NetConnection.Connect.Success" in (cap / (p.name.split(".")[0] + ".recv.bin")).read_bytes()
        except OSError:
            return False

    flags = {p: good(p) for p in files}
    for p in [x for x in files if flags[x]] + [x for x in files if not flags[x]]:
        try:
            for k, v in json.loads(p.read_text(encoding="utf-8")).items():
                if k.lower() == "cookie" and v:
                    return v
        except Exception:
            pass
    return None


def fetch_files(cap: Path, outdir: Path, cookie=None, workers=4):
    """Download documents the browser requested during the capture (pdf, ppt, zip ...),
    replaying the browser's cookie. Only URLs seen in http.jsonl are used."""
    hp = cap / "http.jsonl"
    if not hp.exists():
        print("files: no http.jsonl in the capture, nothing to fetch")
        return []
    cookie = cookie or capture_cookie(cap)
    urls, seen = [], set()
    for line in hp.open(encoding="utf-8"):
        try:
            r = json.loads(line)
        except ValueError:
            continue
        u = (r.get("url") or "").split("#")[0]
        if not u.startswith("http") or (r.get("method") or "GET") != "GET":
            continue
        path = unquote(urlparse(u).path)
        if STATIC_RX.search(path) or u in seen:
            continue
        if DOC_RX.search(path) or re.search(r"download", u, re.I):
            seen.add(u)
            urls.append(u)
    if not urls:
        print("files: no document-like URLs in http.jsonl. Open the shared file in the recording "
              "while capturing, then try again.")
        return []
    outdir.mkdir(parents=True, exist_ok=True)
    host = urlparse(urls[0]).hostname
    hdr = {"User-Agent": "Mozilla/5.0", "Referer": f"https://{host}/"}
    allowed = cookie_hosts(cap)
    used, lock = set(), __import__("threading").Lock()

    def one(u):
        short = u.split("?")[0]
        try:
            with open_url(u, hdr, cookie, allowed) as r:
                ctype = r.headers.get("Content-Type", "")
                cd = r.headers.get("Content-Disposition", "")
                m = re.search(r'filename\*?=(?:UTF-8\'\')?"?([^";]+)', cd)
                name = unquote(m.group(1)) if m else unquote(Path(urlparse(u).path).name) or "file"
                name = re.sub(r'[\\/:*?"<>|]+', "_", name)
                if "text/html" in ctype and not name.lower().endswith((".html", ".htm")):
                    return (short, None, "got an HTML page (login/expired cookie?)")
                with lock:
                    base, ext, k = Path(name).stem, Path(name).suffix, 1
                    final = name
                    while final in used or (outdir / final).exists():
                        k += 1
                        final = f"{base}_{k}{ext}"
                    used.add(final)
                tmp = outdir / (final + ".part")
                with open(tmp, "wb") as fh:
                    shutil.copyfileobj(r, fh)
                os.replace(tmp, outdir / final)
                return (short, final, f"{(outdir / final).stat().st_size / 1e6:.2f} MB")
        except Exception as e:
            return (short, None, f"{type(e).__name__}: {e}")

    print(f"files: {len(urls)} candidate URL(s)", flush=True)
    got = []
    with ThreadPoolExecutor(workers) as ex:
        for short, final, info in ex.map(one, urls):
            print(f"  {'OK  ' if final else 'FAIL'} {short}  -> {final or ''} {info}", flush=True)
            if final:
                got.append(final)
    return got


def cmd_files(a):
    got = fetch_files(Path(a.cap), Path(a.outdir), a.cookie)
    print(f"{len(got)} file(s) saved in {a.outdir}")



# Commands
async def cmd_get(a):
    ctx = build_ctx(a)
    out = Path(a.out)
    if a.jobs > 1:
        ctx["seg"] = 0  # split into --jobs equal segments
    kind = "split" if a.jobs > 1 else "single"
    parts, _ = await run_specs(ctx, [(a.stream, kind, a.start, a.length)],
                               out.with_suffix(".parts"), out.with_suffix(".extras"), a.fresh)
    res = merge_stream(parts[a.stream], out)
    if res:
        convert(out, res, a.fps)


VIDEO_NAME_RX = re.compile(r"screen|camera|video|webcam", re.I)


def pick_video_streams(starts, media_by_name):
    """Every video-looking stream listed in the session (has a startTime), whether or not the browser
    received any of its frames during the capture. Streams with another name are added only if
    non-audio frames were actually seen. Returns [(startTime_ms, name)] sorted by start."""
    out = {}
    for n, t in starts.items():
        if "cameraVoip" in n or FT_RX.match(n):
            continue
        if VIDEO_NAME_RX.search(n):
            out[n] = t
    for n, kinds in media_by_name.items():
        if n in starts and n not in out and any(k != 3 and nf > 0 for k, (nf, *_r) in kinds.items()):
            out[n] = starts[n]
    return sorted((t, n) for n, t in out.items())


def _iter_play_events(cap: Path):
    """Yield (time_s, event_name, changes) for every playEvent in the captured buffers, de-duplicated."""
    dec = json.JSONDecoder()
    needle = '{"cmdString":"playEvent"'
    seen = set()
    for recv_path in sorted(cap.glob("ws*.recv.bin")):
        raw = recv_path.read_bytes().decode("utf-8", "ignore")
        pos = 0
        while True:
            pos = raw.find(needle, pos)
            if pos < 0:
                break
            try:
                obj, end = dec.raw_decode(raw, pos)
            except Exception:
                pos += len(needle)
                continue
            pos = max(end, pos + len(needle))
            params = obj.get("params") if isinstance(obj, dict) else None
            if not isinstance(params, dict):
                continue
            a0, ev, ch = params.get("arg_0"), params.get("arg_1"), params.get("arg_2")
            if not isinstance(a0, dict):
                continue
            try:
                t = float(a0.get("time")) / 1000.0
            except (TypeError, ValueError):
                continue
            if not (isinstance(ev, str) and isinstance(ch, list)):
                # state snapshots (e.g. what was already shared when the recording started)
                snap = [x for x in (ev, ch) if isinstance(x, (dict, list))]
                if not snap:
                    continue
                ev, ch = "__state__", snap
            key = hash((round(t, 3), ev, json.dumps(ch, sort_keys=True, separators=(",", ":"), ensure_ascii=False)))
            if key in seen:
                continue
            seen.add(key)
            yield t, ev, ch

_CONTENT_ID_RX = re.compile(r"/(p[a-z0-9]{11})/")

def _first_content_id(text):
    for m in _CONTENT_ID_RX.finditer(text or ""):
        if any(c.isdigit() for c in m.group(1)):
            return m.group(1)
    return None

def _collect_content(val, t, items, docs):
    """Walk a setContentSo value: content items (ctID) and document descriptors (originatingSco)."""
    if isinstance(val, dict):
        if "ctID" in val and ("shareType" in val or "documentDescriptor" in val):
            try:
                k = int(float(val["ctID"]))
            except (TypeError, ValueError):
                k = None
            if k is not None:
                it = items.setdefault(k, {"kind": "other", "sco": None, "t": t})
                if val.get("shareType") == "wb":
                    it["kind"] = "wb"
                dd = val.get("documentDescriptor")
                if isinstance(dd, dict) and dd.get("scoID") is not None:
                    it["kind"], it["sco"] = "doc", str(dd["scoID"])
        if val.get("originatingSco") is not None:
            info = docs.setdefault(str(val["originatingSco"]),
                                   {"name": "", "playback_id": None, "content_id": None, "t": t})
            if val.get("theName"):
                info["name"] = str(val["theName"])
            for field, slot in (("playbackContentOutputPath", "playback_id"), ("contentOutputPath", "content_id")):
                found_id = _first_content_id(str(val.get(field) or ""))
                if found_id:
                    info[slot] = found_id
        for v in val.values():
            _collect_content(v, t, items, docs)
    elif isinstance(val, list):
        for v in val:
            _collect_content(v, t, items, docs)

def extract_share_state(cap: Path):
    """What the Share pod showed and when, read from the recorded events.
    timeline: [(t, ctID)] active content (-1 = nothing); items: ctID -> wb/doc/other (+ document sco);
    docs: sco -> name + content ids of the PDF; mementos: [(t, 0-based page)]; wb_on: [(t, bool)] overlay."""
    timeline, items, docs, mementos, wb_on = [], {}, {}, [], []
    for t, ev, changes in _iter_play_events(cap):
        if ev == "__state__":
            for obj in changes:
                _collect_content(obj, t, items, docs)
            continue
        if ev not in ("setContentSo", "setPdfContentSo", "setControlsSo"):
            continue
        for c in changes:
            if not isinstance(c, dict):
                continue
            name, val = str(c.get("name")), c.get("newValue")
            if ev == "setContentSo":
                if name == "ctID":
                    try:
                        timeline.append((t, int(float(val))))
                    except (TypeError, ValueError):
                        pass
                else:
                    _collect_content(val, t, items, docs)
            elif ev == "setPdfContentSo" and name == "memento":
                m = re.search(r"(?:^|\|)tPgNum-(\d+)(?:\||$)", str(val))
                if m:
                    mementos.append((t, int(m.group(1))))
            elif ev == "setControlsSo" and name == "wbOn":
                wb_on.append((t, bool(val)))
    timeline.sort(key=lambda x: x[0])
    dedup = []
    for t, k in timeline:
        if not dedup or dedup[-1][1] != k:
            dedup.append((t, k))
    return {"timeline": dedup, "items": items, "docs": docs,
            "mementos": sorted(mementos), "wb_on": sorted(wb_on)}

def _drop_empty_holes(partsdir: Path):
    """An empty .seg means the server sent nothing for that range. That is normal only after the end of an
    audio stream; anywhere else it is a hole (or a failed video download), so delete it and fetch it again."""
    dropped = []
    for d in sorted(p for p in partsdir.iterdir() if p.is_dir()):
        segs = sorted(d.glob("*.seg"))
        sizes = [p.stat().st_size for p in segs]
        last_data = max((i for i, z in enumerate(sizes) if z > 0), default=-1)
        for i, (p, z) in enumerate(zip(segs, sizes)):
            if z == 0 and (i < last_data or not d.name.startswith("cameraVoip")):
                try:
                    p.unlink()
                    dropped.append(f"{d.name}/{p.name[:4]}")
                except OSError:
                    pass
    if dropped:
        print(f"[RETRY] {len(dropped)} empty segment(s) from an earlier run will be downloaded again: "
              f"{', '.join(dropped[:8])}{' ...' if len(dropped) > 8 else ''}", flush=True)

def _flv_last_ts(path: Path):
    try:
        with open(path, "rb") as fh:
            fh.seek(-4, 2)
            size = int.from_bytes(fh.read(4), "big")
            fh.seek(-4 - size, 2)
            hdr = fh.read(8)
        return (int.from_bytes(hdr[4:7], "big") | (hdr[7] << 24)) / 1000.0
    except (OSError, ValueError):
        return None

def report_stream_ends(cap: Path, outdir: Path, audio_t, video_t, duration):
    """Where each downloaded stream starts and ends on the class timeline, to spot a missing tail."""
    print(f"[END-CHECK] class length {duration:.1f}s (player clock or --length)", flush=True)
    audio_end = 0.0
    for name, start_ms in list(audio_t.items()) + list(video_t.items()):
        flv = outdir / (name.strip("/") + ".flv")
        last = _flv_last_ts(flv) if flv.exists() else None
        if last is None:
            continue
        end = start_ms / 1000.0 + last
        if name in audio_t:
            audio_end = max(audio_end, end)
        print(f"  {flv.name}: {start_ms / 1000.0:.1f}s -> {end:.1f}s", flush=True)
    try:
        latest = max(t for t, _, _ in _iter_play_events(cap))
    except ValueError:
        latest = None
    if latest is not None:
        print(f"  last recorded event: {latest:.1f}s", flush=True)
        if latest > duration + 3:
            print(f"[WARN] events run {latest - duration:.0f}s past the class length: the recording is longer than "
                  f"{duration:.0f}s. Enter the full length (or use --length {latest + 5:.0f}).", flush=True)
    if audio_end and audio_end < duration - 15:
        print(f"[WARN] the last audio ends {duration - audio_end:.0f}s before the class end "
              "(missing audio at the tail, or a stream that was never listed).", flush=True)

def _item_label(state, k):
    it = state["items"].get(k)
    if it is None:
        return "nothing shared"
    if it["kind"] == "wb":
        return f"whiteboard #{k}"
    if it["kind"] == "doc":
        name = (state["docs"].get(it["sco"]) or {}).get("name") or f"document sco {it['sco']}"
        return f"PDF #{k}: {name[:60]}"
    return f"other share #{k}"

def print_content_timeline(state):
    print("[CONTENT] what was on screen (from the recording's own events):", flush=True)
    for t, k in state["timeline"][:80]:
        print(f"  {t:8.1f}s  {_item_label(state, k)}", flush=True)

def _server_origin(cap: Path):
    base = None
    rp = cap / "rooms.jsonl"
    if rp.exists():
        for line in rp.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                base = json.loads(line).get("url")
                if base:
                    break
            except Exception:
                pass
    if not base:
        for mp in sorted(cap.glob("ws*.meta.json")):
            try:
                base = json.loads(mp.read_text(encoding="utf-8")).get("url")
                if base:
                    break
            except Exception:
                pass
    if not base:
        return ""
    u = urlparse(base)
    scheme = {"wss": "https", "ws": "http"}.get(u.scheme, u.scheme or "https")
    return f"{scheme}://{u.netloc}" if u.netloc else ""

def _pdf_ok(path: Path):
    try:
        if path.stat().st_size < 1000:
            return False
        with open(path, "rb") as fh:
            if fh.read(5) != b"%PDF-":
                return False
    except OSError:
        return False
    try:
        try:
            import pymupdf as fitz
        except ImportError:
            import fitz
    except ImportError:
        return True
    try:
        doc = fitz.open(str(path))
        n = len(doc)
        doc.close()
        return n > 0
    except Exception:
        return False

def resolve_share_pdfs(cap: Path, outdir: Path, state):
    """sco -> PDF file for every shared document. Order: content id from the descriptor, looked up in the
    capture's cached responses, then downloaded as /<id>/default/connect.pdf (what the player itself loads)
    with the captured cookie. A document without any id is paired only when it is the single unmatched
    document and the player loaded exactly one other PDF (never a guess between several)."""
    by_id, http_ids = {}, set()
    meta = cap / "assets.jsonl"
    if meta.exists():
        for line in meta.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                row = json.loads(line)
            except Exception:
                continue
            url, f = str(row.get("url", "")), row.get("file")
            i = _first_content_id(urlparse(url).path)
            if f and i and ".pdf" in url.lower():
                by_id.setdefault(i, []).append(cap / f)
    hp = cap / "http.jsonl"
    if hp.exists():
        for line in hp.read_text(encoding="utf-8", errors="ignore").splitlines():
            try:
                url = str(json.loads(line).get("url") or "")
            except Exception:
                continue
            i = _first_content_id(urlparse(url).path)
            if i and url.split("?")[0].lower().endswith(".pdf"):
                http_ids.add(i)
    for paths in by_id.values():
        paths.sort(key=lambda p: p.stat().st_size if p.exists() else 0, reverse=True)
    cache = outdir / "pdfs"
    origin = _server_origin(cap)
    auth = {}

    def obtain(ids):
        for i in ids:
            c = cache / f"{i}.pdf"
            if c.exists() and _pdf_ok(c):
                return c, "cached", i
        for i in ids:
            for p in by_id.get(i, []):
                if _pdf_ok(p):
                    return p, "from capture", i
        if origin and ids:
            if not auth:
                auth["cookie"], auth["allowed"] = capture_cookie(cap) or "", cookie_hosts(cap)
            hdr = {"User-Agent": "Mozilla/5.0", "Referer": origin + "/"}
            for i in ids:
                for url in (f"{origin}/{i}/default/connect.pdf", f"{origin}/_a7/{i}/default/connect.pdf"):
                    try:
                        with open_url(url, hdr, auth["cookie"], auth["allowed"]) as r:
                            data = r.read()
                        if not data.startswith(b"%PDF-"):
                            continue
                        cache.mkdir(parents=True, exist_ok=True)
                        dest = cache / f"{i}.pdf"
                        tmp = dest.with_suffix(".part")
                        tmp.write_bytes(data)
                        os.replace(tmp, dest)
                        if _pdf_ok(dest):
                            return dest, f"downloaded {len(data) / 1e6:.1f} MB", i
                    except Exception:
                        continue
        return None, "", None

    out, unresolved, claimed = {}, [], set()
    for it in state["items"].values():
        sco = it.get("sco")
        if it["kind"] != "doc" or not sco or sco in out or any(sco == u[0] for u in unresolved):
            continue
        info = state["docs"].get(sco) or {}
        ids = [i for i in (info.get("playback_id"), info.get("content_id")) if i]
        name = (info.get("name") or f"document sco {sco}")[:50]
        found, how, used = obtain(ids)
        if found:
            out[sco] = found
            claimed.add(used)
            print(f"[PDF] {name}: {how}", flush=True)
        else:
            unresolved.append((sco, name, ids))
    free = sorted((set(by_id) | http_ids) - claimed)
    if unresolved and len(unresolved) == 1 and len(free) == 1:
        sco, name, ids = unresolved[0]
        found, how, used = obtain([free[0]])
        if found:
            out[sco] = found
            print(f"[PDF] {name}: paired with the only PDF the player loaded ({used}); {how}", flush=True)
            unresolved = []
        else:
            print(f"[PDF] the only PDF the player loaded ({free[0]}) could not be read or downloaded", flush=True)
    elif unresolved and free:
        print(f"[PDF] cannot pair safely: {len(unresolved)} document(s) without a file id, "
              f"PDFs loaded by the player: {', '.join(free)}", flush=True)
    for sco, name, ids in unresolved:
        print(f"[PDF] {name}: NOT AVAILABLE (ids tried: {', '.join(ids) or 'none'}); a placeholder is shown", flush=True)
    return out


class _WhiteboardState:
    """Pencil strokes. Each stroke is tagged with the content (ctID) on screen when it was drawn and, on a PDF,
    the page that was showing. A stroke is only drawn on the content it was drawn on."""
    W, H = 960, 720

    def __init__(self):
        self.records = {}          # (ctx, store, shape id) -> {"shape", "ctx", "pg"}
        self.by_ctx = {}           # ctx -> records in drawing order
        self.page, self.scale = None, 1.2      # whiteboard page (setWBSo currentPage)
        self.layer = self.draw = None
        self.view, self.pending, self.need_full, self.drawn = None, [], True, 0

    @staticmethod
    def _abs(shape):
        try:
            x0, y0 = float(shape.get("x", 0)), float(shape.get("y", 0))
            sw, sh = float(shape.get("width", 0)), float(shape.get("height", 0))
            return [(x0 + float(p.get("x", 0)) * sw, y0 + float(p.get("y", 0)) * sh)
                    for p in shape.get("pts", [])]
        except (TypeError, ValueError, AttributeError):
            return None

    @classmethod
    def _extends(cls, old, new):
        if new.get("type") != "pencil" or old.get("type") != "pencil":
            return False
        a, b = cls._abs(old), cls._abs(new)
        return (a is not None and b is not None and len(b) >= len(a)
                and all(abs(p[0] - q[0]) < 0.05 and abs(p[1] - q[1]) < 0.05 for p, q in zip(a, b))
                and old.get("strokeCol") == new.get("strokeCol")
                and old.get("strokeWeight") == new.get("strokeWeight")
                and old.get("currentPage") == new.get("currentPage"))

    def apply(self, event_name, changes, ctx, doc_page):
        """Apply one recorded event. ctx = content on screen when it happened, doc_page = PDF page then.
        Returns (set of contents whose strokes changed, whiteboard page changed)."""
        touched, page_changed = set(), False
        if event_name == "setWBSo":
            for c in changes:
                if not isinstance(c, dict):
                    continue
                if c.get("name") == "nativeWidth":
                    try:
                        self.scale = self.W / float(c.get("newValue"))
                    except (TypeError, ValueError, ZeroDivisionError):
                        pass
                elif c.get("name") == "currentPage":
                    try:
                        page = int(float(c.get("newValue")))
                    except (TypeError, ValueError):
                        continue
                    if page != self.page:
                        self.page, page_changed = page, True
            return touched, page_changed
        store = event_name.rsplit("_", 1)[-1]
        for c in changes:
            if not isinstance(c, dict):
                continue
            sid, val = str(c.get("name", "")), c.get("newValue")
            if not sid:
                continue
            key = (ctx, store, sid)
            if c.get("code") in ("delete", "remove") or val is None:
                if (c.get("code") in ("delete", "remove") or c.get("oldValue") is not None) and key in self.records:
                    rec = self.records.pop(key)
                    self.by_ctx[ctx] = [r for r in self.by_ctx.get(ctx, []) if r is not rec]
                    self.need_full = True
                    touched.add(ctx)
                continue
            if not (isinstance(val, dict) and val.get("type")):
                continue
            old = self.records.get(key)
            if old is None:
                rec = {"shape": val, "ctx": ctx, "pg": doc_page}
                self.records[key] = rec
                self.by_ctx.setdefault(ctx, []).append(rec)
                self.pending.append(rec)
            else:
                if self._extends(old["shape"], val):
                    self.pending.append(old)
                else:
                    self.need_full = True
                old["shape"] = val
            touched.add(ctx)
        if len(self.pending) > 300:
            self.pending, self.need_full = [], True
        return touched, page_changed

    def _matches(self, rec, view):
        if view[0] == "doc":
            return rec["pg"] == view[2]
        if self.page is None:
            return True
        try:
            return int(float(rec["shape"].get("currentPage", self.page))) == self.page
        except (TypeError, ValueError):
            return True

    def _draw_shape(self, shape):
        if shape.get("type") != "pencil":
            return
        try:
            pts = self._abs(shape)
            if not pts or len(pts) < 2:
                return
            s = self.scale
            rgb = int(float(shape.get("strokeCol", 0)))
            self.draw.line([(round(x * s), round(y * s)) for x, y in pts],
                           fill=((rgb >> 16) & 255, (rgb >> 8) & 255, rgb & 255, 255),
                           width=max(2, round(float(shape.get("strokeWeight", 2)) * s)), joint="curve")
            self.drawn += 1
        except (TypeError, ValueError, OverflowError):
            return

    def sync(self, view, Image, ImageDraw):
        """Stroke layer for one view ("wb", ctx, page) or ("doc", ctx, pdf page); incremental when possible."""
        if self.layer is None or view != self.view or self.need_full:
            self.layer = Image.new("RGBA", (self.W, self.H), (0, 0, 0, 0))
            self.draw = ImageDraw.Draw(self.layer)
            self.drawn = 0
            for rec in self.by_ctx.get(view[1], []):
                if self._matches(rec, view):
                    self._draw_shape(rec["shape"])
            self.view, self.pending, self.need_full = view, [], False
        elif self.pending:
            for rec in self.pending:
                if rec["ctx"] == view[1] and self._matches(rec, view):
                    self._draw_shape(rec["shape"])
            self.pending = []
        return self.layer


def render_content_timeline(cap: Path, out_path: Path, duration: float, fps: float, state, pdf_by_sco,
                            draw_wb=True):
    """One pass for everything the Share pod showed:
      screen share      -> black (the screen-share video is laid over it separately)
      PDF               -> the page that was showing, with the pencil strokes drawn on it (transparent layer)
      anything else     -> the whiteboard: white page with the pencil strokes of that whiteboard."""
    ff = shutil.which("ffmpeg")
    if not ff:
        print("content render skipped: ffmpeg not found")
        return False
    try:
        from PIL import Image, ImageDraw, ImageFont
    except ImportError:
        print("content render skipped: Pillow is not installed (pip install pillow)")
        return False
    fitz = None
    if pdf_by_sco:
        try:
            try:
                import pymupdf as fitz
            except ImportError:
                import fitz
        except ImportError:
            print("PDFs found, but showing them needs PyMuPDF: python -m pip install pymupdf")

    W, H = 1280, 720
    WB_X = (W - _WhiteboardState.W) // 2
    events = extract_whiteboard_events(cap) if draw_wb else []
    wb = _WhiteboardState()
    items = state["items"]
    tl_t = [t for t, _ in state["timeline"]]
    tl_k = [k for _, k in state["timeline"]]

    def active(t):
        i = bisect.bisect_right(tl_t, t) - 1
        return tl_k[i] if i >= 0 else None

    def kind_of(k):
        return items.get(k, {}).get("kind") if k is not None else None

    pages = {}                               # ctID -> [(t, page)] page position of that document
    for t, p in state["mementos"]:
        k = active(t)
        if kind_of(k) == "doc":
            pages.setdefault(k, []).append((t, p))
    page_t = {k: [t for t, _ in v] for k, v in pages.items()}

    def doc_page(k, t):
        lst = pages.get(k)
        if not lst:
            return 0
        i = bisect.bisect_right(page_t[k], t) - 1
        return lst[i][1] if i >= 0 else 0

    open_docs, page_cache, notes = {}, {}, {}
    white = Image.new("RGB", (W, H), "white").tobytes()
    black = bytes(W * H * 3)
    try:
        font = ImageFont.load_default(size=30)
    except Exception:
        font = ImageFont.load_default()

    def get_doc(k):
        if k not in open_docs:
            doc = None
            path = pdf_by_sco.get(items.get(k, {}).get("sco"))
            if fitz is not None and path:
                try:
                    doc = fitz.open(str(path))
                except Exception as e:
                    print(f"PDF open failed for {path.name}: {e}")
            open_docs[k] = doc if doc is not None and len(doc) else None
        return open_docs[k]

    def note_frame(k):
        if k not in notes:
            im = Image.new("RGB", (W, H), "white")
            label = _item_label(state, k) + " (file not available)"
            ImageDraw.Draw(im).text((40, 40), label, fill=(120, 120, 120), font=font)
            notes[k] = im.tobytes()
        return notes[k]

    def page_frame(k, p):
        doc = get_doc(k)
        if doc is None:
            return note_frame(k)
        p = max(0, min(len(doc) - 1, p))
        if (k, p) not in page_cache:
            if len(page_cache) >= 8:                  # keep memory small (about 2.7 MB per page)
                page_cache.pop(next(iter(page_cache)))
            pix = doc.load_page(p).get_pixmap(matrix=fitz.Matrix(1.6, 1.6), alpha=False)
            img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
            img.thumbnail((W - 48, H - 48))
            canvas = Image.new("RGB", (W, H), "white")
            canvas.paste(img, ((W - img.width) // 2, (H - img.height) // 2))
            page_cache[(k, p)] = canvas.tobytes()
        return page_cache[(k, p)]

    def with_strokes(base, view):
        layer = wb.sync(view, Image, ImageDraw)
        if not wb.drawn:
            return base
        im = Image.frombytes("RGB", (W, H), base)
        im.paste(layer, (WB_X, 0), layer)
        return im.tobytes()

    cmd = [ff, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
           "-s", f"{W}x{H}", "-r", f"{fps:g}", "-i", "-",
           "-an", "-c:v", "libx264", "-preset", "ultrafast", "-tune", "stillimage", "-crf", "20",
           "-pix_fmt", "yuv420p", "-t", f"{duration:g}", "-movflags", "+faststart", str(out_path)]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    total = max(1, int(math.ceil(duration * fps)))
    ev_i, dirty, cur_key, data = 0, set(), None, white
    try:
        for fi in range(total):
            t = (fi + 0.5) / fps        # state in the middle of this frame's slot: error is +-half a frame
            while ev_i < len(events) and events[ev_i][0] <= t * 1000.0:
                te = events[ev_i][0] / 1000.0
                kc = active(te)
                touched, _ = wb.apply(events[ev_i][1], events[ev_i][2], kc,
                                      doc_page(kc, te) if kind_of(kc) == "doc" else None)
                dirty |= touched
                ev_i += 1
            k = active(t)
            kind = kind_of(k)
            if kind == "other":
                key = ("black",)
            elif kind == "doc":
                key = ("doc", k, doc_page(k, t))
            else:
                key = ("wb", k, wb.page)
            if key != cur_key or (key[0] in ("doc", "wb") and k in dirty):
                if key[0] == "black":
                    data = black
                elif key[0] == "doc":
                    data = page_frame(k, key[2])
                    if draw_wb:
                        data = with_strokes(data, key)
                else:
                    data = with_strokes(white, key) if draw_wb else white
                cur_key = key
                dirty.discard(k)
            try:
                proc.stdin.write(data)
            except BrokenPipeError:
                break
            if fi and fi % max(1, int(fps * 10)) == 0:
                UI.line(f"Rendering content: {fi}/{total} frames ({fi * 100 // total}%)")
        UI.end()
        if proc.stdin:
            proc.stdin.close()
        rc = proc.wait()
    except Exception as e:
        try:
            proc.kill()
        except Exception:
            pass
        print(f"content render failed: {type(e).__name__}: {e}")
        return False
    finally:
        for d in open_docs.values():
            try:
                if d is not None:
                    d.close()
            except Exception:
                pass
    if rc == 0 and out_path.exists() and out_path.stat().st_size > 1000:
        print(f"Content timeline rendered: {out_path.name}")
        return True
    print("content timeline creation failed")
    return False


async def cmd_all(a):
    ctx = build_ctx(a)
    names, starts = collect_streams(ctx["frames"])
    nsmap, stats, _, _, _ = scan_ws(ctx["frames"])

    media_by_name = {}
    for ns, kinds in stats.items():
        name = nsmap.get(ns)
        if name:
            media_by_name[name] = kinds

    cams = sorted(((t, n) for n, t in starts.items() if "cameraVoip" in n), key=lambda x: x[0])
    video_candidates = pick_video_streams(starts, media_by_name)

    if not cams:
        sys.exit("no cameraVoip streams with a startTime in the capture")
    if not video_candidates:
        print("[INFO] No screen-share/video stream is listed in the session. "
              "The final video will use audio plus any captured Whiteboard/PDF content.")

    outdir = Path(a.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    def stream_len(t):
        s = float(t) / 1000.0
        if a.length > 0:
            return None if s >= a.length else max(0.0, a.length - s)
        return -1

    specs, audio_t, video_t = [], {}, {}
    for t, n in cams:
        L = stream_len(t)
        if L is None:
            print(f"skip (starts after requested end): {n}")
            continue
        specs.append((n, "split", 0.0, L))
        audio_t[n] = float(t)
    for t, n in video_candidates:
        L = stream_len(t)
        if L is None:
            print(f"skip video (starts after requested end): {n}")
            continue
        specs.append((n, "split" if a.vsplit else "single", 0.0, L))
        video_t[n] = float(t)
    if not a.no_extras:
        done_names = {s[0] for s in specs}
        for n in sorted(names):
            if FT_RX.match(n) and n not in done_names:
                specs.append((n, "text", 0.0, -1))

    parts, failed = await run_specs(ctx, specs, outdir / "parts", outdir / "extras", a.fresh)

    audio_items, video_items = [], []
    for n, t in audio_t.items():
        flv = outdir / (n.strip("/") + ".flv")
        if merge_stream(parts[n], flv):
            audio_items.append((flv, t))
    for n, t in video_t.items():
        flv = outdir / (n.strip("/") + ".flv")
        if merge_stream(parts[n], flv):
            video_items.append((flv, t, n))

    if not a.no_files:
        try:
            fetch_files(Path(a.cap), outdir / "files", a.cookie)
        except Exception as e:
            print(f"files: skipped ({type(e).__name__}: {e})")

    if not audio_items and not video_items:
        sys.exit("nothing downloaded")

    duration = a.length
    if duration <= 0:
        probe = shutil.which("ffprobe")
        vals = []
        if probe:
            for path, start_ms in [(p, t) for p, t in audio_items] + [(p, t) for p, t, _ in video_items]:
                try:
                    q = subprocess.run(
                        [probe, "-v", "error", "-show_entries", "format=duration",
                         "-of", "default=noprint_wrappers=1:nokey=1", str(path)],
                        capture_output=True, text=True)
                    vals.append(float(q.stdout.strip()) + start_ms / 1000.0)
                except Exception:
                    pass
        if vals:
            duration = max(vals)
        else:
            # ffprobe is optional. Estimate timeline end from the last captured
            # timestamp for each selected stream, offset by its recorded startTime.
            estimates = []
            for name, start_ms in list(audio_t.items()) + list(video_t.items()):
                kinds = media_by_name.get(name, {})
                last_ms = max((row[3] for kind, row in kinds.items() if kind != 3 or name in audio_t), default=0)
                estimates.append(float(start_ms) / 1000.0 + max(0.0, float(last_ms) / 1000.0))
            duration = max(estimates, default=0.0)
            if duration <= 0:
                duration = max((float(row[3]) / 1000.0 for kinds in stats.values() for row in kinds.values()), default=1.0)
            duration = max(1.0, duration)
            print(f"ffprobe not found; estimated class duration from captured frame timestamps: {duration:.1f}s")

    # Everything the Share pod showed (PDFs and whiteboard) comes from the recording's own events.
    report_stream_ends(Path(a.cap), outdir, audio_t, video_t, duration)
    content_ok = False
    state = extract_share_state(Path(a.cap))
    if state["timeline"] and state["items"]:
        print_content_timeline(state)
        t_content = time.time()
        pdf_by_sco = resolve_share_pdfs(Path(a.cap), outdir, state)
        content_path = outdir / "content_timeline.mp4"
        if render_content_timeline(Path(a.cap), content_path, duration, a.fps, state, pdf_by_sco,
                                   draw_wb=not a.no_whiteboard):
            video_items.insert(0, (content_path, 0.0, "content"))
            content_ok = True
        print(f"[TIME] PDF + whiteboard render: {time.time() - t_content:.0f}s", flush=True)
    else:
        print("[CONTENT] no content-switch events in this capture; using the older PDF/whiteboard logic.", flush=True)
    if not content_ok:
        # Resolve and download PDF descriptors from the actual shared-content events.
        descriptors, cached_assets = inspect_pdf_resources(Path(a.cap))
        pdf_files = download_pdf_descriptors(Path(a.cap), outdir / "files", descriptors)

        # Some Adobe Connect rooms expose a descriptor URL (/system/download?...)
        # that returns an HTML error page even though the same PDF was successfully
        # captured from the viewer's connect.pdf endpoint by fetch_files(). In that
        # case, reuse verified PDF files already downloaded into outdir/files.
        # Validate by PDF magic bytes and de-duplicate identical downloads.
        import hashlib
        known_hashes = set()
        for _, existing_pdf in pdf_files:
            try:
                known_hashes.add(hashlib.sha256(existing_pdf.read_bytes()).hexdigest())
            except OSError:
                pass
        fallback_pdfs = []
        files_dir = outdir / "files"
        if files_dir.exists():
            for candidate in sorted(files_dir.glob("*.pdf")):
                try:
                    data = candidate.read_bytes()
                    if len(data) < 1000 or not data.startswith(b"%PDF-"):
                        continue
                    digest = hashlib.sha256(data).hexdigest()
                    if digest in known_hashes:
                        continue
                    known_hashes.add(digest)
                    fallback_pdfs.append(candidate)
                except OSError:
                    continue
        missing_descriptors = [d for d in descriptors
                               if not any(str(d.get("name", "")) == str(saved_d.get("name", ""))
                                          for saved_d, _ in pdf_files)]
        if missing_descriptors and fallback_pdfs:
            # If one unique PDF was fetched from the viewer endpoint, it is the
            # strongest available fallback for the descriptor whose direct URL failed.
            if len(fallback_pdfs) == 1 and len(missing_descriptors) == 1:
                pdf_files.append((missing_descriptors[0], fallback_pdfs[0]))
                print(f"PDF fallback: using verified viewer download {fallback_pdfs[0].name} "
                      f"for {missing_descriptors[0].get('name') or 'shared PDF'}")
            else:
                for desc, candidate in zip(missing_descriptors, fallback_pdfs):
                    pdf_files.append((desc, candidate))
                    print(f"PDF fallback: using verified viewer download {candidate.name} "
                          f"for {desc.get('name') or 'shared PDF'}")
        if cached_assets:
            for asset in cached_assets:
                if asset.suffix.lower() != ".pdf" or asset.stat().st_size <= 1000:
                    continue
                try:
                    data = asset.read_bytes()
                    if not data.startswith(b"%PDF-"):
                        continue
                    digest = hashlib.sha256(data).hexdigest()
                except OSError:
                    continue
                if digest in known_hashes:
                    continue
                known_hashes.add(digest)
                pdf_files.append(({"name": asset.name, "time": 0.0}, asset))
        pdf_path = outdir / "pdf_timeline.mp4"
        pdf_rendered = False
        if pdf_files and render_pdf_timeline(pdf_files, pdf_path, duration, a.fps, Path(a.cap)):
            pdf_rendered = True
            # PDF content sits below Whiteboard annotations and captured screen-share/video.
            video_items.insert(0, (pdf_path, min((float(d.get("time") or 0.0) for d, _ in pdf_files), default=0.0) * 1000.0, "pdf"))

        print(f"[PDF] shared PDFs found: {len(descriptors)}, usable files: {len(pdf_files)}, "
              f"rendered into video: {'yes' if pdf_rendered else 'NO'}", flush=True)
        if not pdf_rendered and (descriptors or pdf_files or cached_assets):
            print("[PDF] WARNING: a PDF was shared but could not be rendered; the white page in the video "
                  "is the Whiteboard background. See the PDF messages above for the reason.", flush=True)

        # Do not infer that Whiteboard is absent just because a PDF was shared too.
        # When both are present, render the Whiteboard strokes with alpha and place
        # them above the PDF so the document remains visible underneath.
        if not a.no_whiteboard:
            transparent_wb = pdf_rendered
            wb_path = outdir / ("whiteboard_timeline.mov" if transparent_wb else "whiteboard_timeline.mp4")
            if render_whiteboard_video(Path(a.cap), wb_path, duration, a.fps, transparent=transparent_wb):
                if pdf_rendered:
                    video_items.insert(1, (wb_path, 0.0, "whiteboard"))
                else:
                    video_items.insert(0, (wb_path, 0.0, "whiteboard"))

    ok = make_class_mp4(audio_items, video_items, Path(a.out), duration, a.fps)
    if failed:
        print("NOTE: some segments failed, the MP4 has holes. Re-run the same command to fill them.")
    return ok



def common(p):
    p.add_argument("cap")
    p.add_argument("--ws", default="auto")
    p.add_argument("--map", default="3=8,4=9", help="binary kind -> FLV tag type")
    p.add_argument("--idle", type=float, default=30)
    p.add_argument("--connect-timeout", type=float, default=20)
    p.add_argument("--cookie")
    p.add_argument("--preload", action="store_true")
    p.add_argument("--jobs", type=int, default=1)
    p.add_argument("--retries", type=int, default=8)
    p.add_argument("--conns", type=int, default=1)
    p.add_argument("--seg", type=float, default=300)
    p.add_argument("--overlap", type=float, default=2)
    p.add_argument("--reuse", action="store_true")
    p.add_argument("--fresh", action="store_true")
    p.add_argument("--no-frag", action="store_true")
    p.add_argument("--fps", type=float, default=15)


def _format_duration(seconds: float) -> str:
    seconds = max(0, int(round(seconds)))
    hours, rem = divmod(seconds, 3600)
    minutes, secs = divmod(rem, 60)
    return f"{hours:02d}:{minutes:02d}:{secs:02d}"


def _captured_timeline_estimate(cap: Path) -> float | None:
    """Estimate class position from captured media and explicit seek/play requests.

    Some Connect sessions reset RTMP timestamps after a seek. In that case the
    maximum media timestamp alone measures only the sampled burst, not class length.
    """
    candidates = []
    max_play_start = 0.0
    media_tail = 0.0
    for ws in list_ws(cap):
        try:
            frames = load_capture(cap, ws)
            names, starts = collect_streams(frames)
            nsmap, stats, *_ = scan_ws(frames)
            for ns, kinds in stats.items():
                name = nsmap.get(ns, "")
                media_ends = [row[3] for kind, row in kinds.items()
                              if kind in (3, 4) and row[0] > 0]
                if media_ends:
                    tail = max(media_ends) / 1000.0
                    media_tail = max(media_tail, tail)
                    start_ms = starts.get(name, 0)
                    candidates.append(start_ms / 1000.0 + tail)
            # The browser's own Play/seek commands can reveal the position jumped to,
            # even when the media timestamp counter restarts at zero after each seek.
            for direction, opcode, data in frames:
                if direction != "s" or opcode != 1:
                    continue
                for obj in parse_json_objects(data.decode("utf-8", "replace")):
                    if not isinstance(obj, dict):
                        continue
                    method = str(obj.get("method", "")).lower()
                    if method not in ("play", "seek") and obj.get("cmdString") != "play":
                        continue
                    raw = obj.get("start")
                    if raw is None:
                        params = obj.get("params")
                        if isinstance(params, dict):
                            raw = params.get("start")
                    try:
                        pos = float(raw)
                    except (TypeError, ValueError):
                        continue
                    # Ignore sentinels, negatives, and implausible units/values.
                    if math.isfinite(pos) and 0 <= pos <= 86400:
                        max_play_start = max(max_play_start, pos)
        except Exception:
            continue
    if max_play_start > 0:
        estimate = max_play_start + media_tail
        # Keep the stronger of seek-derived and ordinary timestamp estimates.
        candidates.append(estimate)
    estimate = max(candidates, default=0.0)
    return estimate if estimate > 1 else None


def _parse_duration_input(raw: str) -> float:
    """Accept seconds or clock notation H:MM:SS / M:SS."""
    raw = raw.strip()
    if ":" not in raw:
        value = float(raw)
    else:
        parts = raw.split(":")
        if len(parts) not in (2, 3) or any(not part.strip().isdigit() for part in parts):
            raise ValueError("Use seconds, M:SS, or H:MM:SS")
        nums = [int(part) for part in parts]
        if len(nums) == 2:
            if nums[1] >= 60:
                raise ValueError("In M:SS notation, seconds must be below 60")
            value = nums[0] * 60 + nums[1]
        else:
            if nums[1] >= 60 or nums[2] >= 60:
                raise ValueError("In H:MM:SS notation, minutes and seconds must be below 60")
            value = nums[0] * 3600 + nums[1] * 60 + nums[2]
    if not math.isfinite(value) or value <= 0:
        raise ValueError("Duration must be positive")
    return value


def _prompt_duration(detected: float | None, from_page: bool) -> float:
    """Always ask for the full duration. Empty Enter = use the detected value; otherwise use what is typed."""
    while True:
        print()
        if detected is not None:
            src = "read from the player clock" if from_page else "estimated from captured media (may be only the sampled part)"
            print(f"[DURATION] Detected: {_format_duration(detected)} ({detected:.0f} seconds), {src}.")
            prompt = "Full class duration (seconds, M:SS, or H:MM:SS; Enter=use_detected): "
        else:
            print("[DURATION] Could not detect the duration.")
            prompt = "Full class duration (seconds, M:SS, or H:MM:SS; e.g. 1:19:23): "
        raw = input(prompt).strip()
        if not raw:
            if detected is None:
                print("[ERROR] Please enter the duration.")
                continue
            length = detected
        else:
            try:
                length = _parse_duration_input(raw)
            except ValueError as exc:
                print(f"[ERROR] Invalid duration: {exc}. Examples: 4763, 79:23, 1:19:23.")
                continue
        print(f"[DURATION] Using: {_format_duration(length)} ({length:.0f} seconds).")
        return length


def _pipeline_main(argv=None):
    if argv is None:
        argv = sys.argv[1:]
    if argv and argv[0] == "--tools":
        return _advanced_main(argv[1:])
    parser = argparse.ArgumentParser(
        prog="adobe_connect_downloader.py",
        description="Adobe Connect: sniff first, then download and render a synchronized MP4.",
        epilog="Advanced commands: streams/get/peek/files/all/analyze/inspect. Use --tools to access them.")
    parser.add_argument("url", nargs="?", default="https://as.kazerunsfu.ac.ir", help="recording/room URL (default: https://as.kazerunsfu.ac.ir)")
    parser.add_argument("--capture-dir", default=None, help="capture directory (default: unique timestamped folder)")
    parser.add_argument("--profile", default="chrome_profile", help="chrome profile directory (keeps login between runs)")
    parser.add_argument("--chrome", help="explicit Chrome executable path")
    parser.add_argument("--port", type=int, default=9222, help="chrome DevTools port")
    parser.add_argument("--length", type=float, default=None, help="duration to process in seconds; asked interactively if omitted")
    parser.add_argument("--out", default=None, help="final MP4 path (default: <class folder>/<name>.mp4)")
    parser.add_argument("--outdir", default=None, help="working directory (default: <class folder>/work)")
    parser.add_argument("--root", default=".", help="parent folder where class folders are created")
    parser.add_argument("--fps", type=float, default=10, help="output frame rate")
    parser.add_argument("--conns", type=int, default=0, help="download worker/connection management (0=automatic; default:auto)")
    parser.add_argument("--jobs", type=int, default=1, help="parallel segments per stream")
    parser.add_argument("--retries", type=int, default=6, help="download retries")
    parser.add_argument("--seg", type=float, default=300, help="audio segment size in seconds")
    parser.add_argument("--overlap", type=float, default=2, help="segment overlap in seconds")
    parser.add_argument("--no-files", action="store_true", help="skip document downloads")
    parser.add_argument("--no-whiteboard", action="store_true", help="skip Whiteboard rendering")
    parser.add_argument("--no-extras", action="store_true", help="skip auxiliary event streams")
    parser.add_argument("--connect-timeout", type=float, default=20.0, help="seconds to wait for each Connect response")
    parser.add_argument("--close-chrome", action="store_true", help="close Chrome when capture ends (frees the browser's own session before downloading)")
    parser.add_argument("--delete-capture", action="store_true", help="delete the capture folder (cookies/session tickets) after a successful run")
    parser.add_argument("--tools", action="store_true", help="run the advanced subcommand interface instead")
    args, remainder = parser.parse_known_args(argv)
    if args.tools:
        return _advanced_main(remainder)
    if remainder:
        parser.error("unknown arguments: " + " ".join(remainder) + " (advanced commands: add --tools)")

    stamp = time.strftime("%Y%m%d_%H%M%S")
    cap = Path(args.capture_dir or f"capture_{stamp}").resolve()  # temporary until class name is known
    cap.mkdir(parents=True, exist_ok=True)
    try:
        os.chmod(cap, 0o700)  # capture holds session cookies/tickets (no effect on Windows)
    except OSError:
        pass

    print()
    print("Adobe Connect Downloader")
    print("=" * 26)
    print(f"Recording URL : {args.url}")
    print()
    print("STEP 1/2 — Capture browser traffic")
    print("Chrome will open. Follow the capture prompt, then press Enter after pausing the recording.")
    capture_args = argparse.Namespace(url=[args.url], match=None, out=str(cap), profile=args.profile,
                                      chrome=args.chrome, port=args.port, stop_on_enter=True,
                                      length=args.length, close_chrome=args.close_chrome)
    try:
        asyncio.run(capture(capture_args))
    except KeyboardInterrupt:
        print()
        print("Capture interrupted; continuing with the data collected so far.")
    except Exception as exc:
        print(f"Capture error: {type(exc).__name__}: {exc}")
        print("If the capture folder contains usable ws*.idx.jsonl files, continuing anyway.")
    if not list_ws(cap):
        print(f"No WebSocket capture files found in {cap}. Nothing to process.")
        return 2

    course, part = parse_class_title(getattr(capture_args, "class_title", ""))
    course = course or f"class_{stamp}"
    class_name = f"{course}-{part}" if part else course
    class_dir = Path(args.root).resolve() / course / (f"قسمت_{part}" if part else "")
    class_dir.mkdir(parents=True, exist_ok=True)
    new_cap = class_dir / "capture"
    if new_cap.exists():
        shutil.rmtree(new_cap, ignore_errors=True)
        if new_cap.exists():   # locked or long-path leftovers: use a fresh name instead of fighting Windows
            new_cap = class_dir / f"capture_{stamp}"
    try:
        shutil.move(str(cap), str(new_cap))
        cap = new_cap
    except OSError as exc:
        print(f"[WARN] Could not move capture folder ({exc}); leaving it at {cap}")
    work = Path(args.outdir).resolve() if args.outdir else class_dir / "work"
    out = Path(args.out).resolve() if args.out else class_dir / f"{class_name}.mp4"
    work.mkdir(parents=True, exist_ok=True)
    print(f"[CLASS] Folder: {class_dir}")
    print(f"        Output: {out}")

    if args.length is None:
        if capture_args.length is not None:
            length = _prompt_duration(capture_args.length, True)
        else:
            length = _prompt_duration(_captured_timeline_estimate(cap), False)
    else:
        if not math.isfinite(args.length) or args.length <= 0:
            print("[ERROR] --length must be a positive number of seconds.")
            return 2
        length = args.length
        print(f"[DURATION] Using command-line duration: {_format_duration(length)} ({length:.0f} seconds).")

    print()
    print("STEP 2/2 — Download and render")
    all_args = argparse.Namespace(
        cap=str(cap), ws="auto", map="3=8,4=9", idle=30.0, connect_timeout=args.connect_timeout, cookie=None,
        preload=False, jobs=args.jobs, retries=args.retries, conns=args.conns, seg=args.seg, overlap=args.overlap,
        reuse=True, fresh=False, no_frag=False, fps=args.fps, outdir=str(work), out=str(out),
        length=length, vsplit=False, no_files=args.no_files, no_extras=args.no_extras,
        no_whiteboard=args.no_whiteboard)
    try:
        render_ok = asyncio.run(cmd_all(all_args))
    except KeyboardInterrupt:
        print()
        print("[STOPPED] Stopped by user. Captured data and completed segments were kept.")
        return 130
    except SystemExit as exc:
        print()
        detail = str(exc).strip() or "processing stopped"
        print(f"[ERROR] {detail}")
        print(f"        Capture data was kept at: {cap}")
        return 1
    except Exception as exc:
        print()
        print(f"[ERROR] Download/render failed: {type(exc).__name__}: {str(exc).splitlines()[0]}")
        print(f"        Capture data was kept at: {cap}")
        print("        For diagnosis, run: python " + Path(__file__).name + " --tools analyze " + str(cap))
        return 1
    print()
    if render_ok and out.is_file() and out.stat().st_size > 1000:
        size_mb = out.stat().st_size / (1024 * 1024)
        print(f"[DONE] Output: {out} ({size_mb:.1f} MB)")
        if args.delete_capture:
            shutil.rmtree(cap, ignore_errors=True)
            print(f"Capture folder deleted: {cap}")
        return 0
    print(f"[INCOMPLETE] A valid new output was not confirmed at: {out}")
    print(f"            Capture data was kept at: {cap}")
    return 1

def _advanced_main(argv=None):
    parser = argparse.ArgumentParser(
        description="Advanced tools for Adobe Connect captures"
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    capture_parser = sub.add_parser("capture")
    capture_parser.add_argument("url", nargs="*")
    capture_parser.add_argument("--match")
    capture_parser.add_argument("--out", default="cap")
    capture_parser.add_argument("--profile", default="chrome_profile")
    capture_parser.add_argument("--chrome")
    capture_parser.add_argument("--port", type=int, default=9222)

    analyze_parser = sub.add_parser("analyze")
    analyze_parser.add_argument("dir")

    inspect_parser = sub.add_parser("inspect")
    inspect_parser.add_argument("dir")
    inspect_parser.add_argument("--ws", default="ws3")

    streams_parser = sub.add_parser("streams")
    streams_parser.add_argument("cap")
    streams_parser.add_argument("--ws", default="auto")

    get_parser = sub.add_parser("get")
    common(get_parser)
    get_parser.add_argument("--stream", required=True)
    get_parser.add_argument("--out", default="stream.flv")
    get_parser.add_argument("--start", type=float, default=0.0)
    get_parser.add_argument("--length", type=float, default=-1)

    peek_parser = sub.add_parser("peek")
    peek_parser.add_argument("cap")
    peek_parser.add_argument("--ws", default="auto")
    peek_parser.add_argument("--stream", required=True)
    peek_parser.add_argument("-n", type=int, default=12)

    files_parser = sub.add_parser("files")
    files_parser.add_argument("cap")
    files_parser.add_argument("--outdir", default="files")
    files_parser.add_argument("--cookie")

    all_parser = sub.add_parser("all")
    common(all_parser)
    all_parser.add_argument("--outdir", default="class")
    all_parser.add_argument("--out", default="class.mp4")
    all_parser.add_argument("--length", type=float, default=-1)
    all_parser.add_argument("--vsplit", action="store_true")
    all_parser.add_argument("--no-files", action="store_true")
    all_parser.add_argument("--no-extras", action="store_true")
    all_parser.add_argument("--no-whiteboard", action="store_true")

    args = parser.parse_args(argv)
    if args.cmd == "capture":
        try:
            asyncio.run(capture(args))
        except KeyboardInterrupt:
            pass
    elif args.cmd == "analyze":
        run_report(analyze, args, "analysis.txt")
    elif args.cmd == "inspect":
        run_report(inspect, args, "inspect.txt")
    elif args.cmd == "streams":
        cmd_streams(args)
    elif args.cmd == "peek":
        cmd_peek(args)
    elif args.cmd == "files":
        cmd_files(args)
    elif args.cmd == "get":
        asyncio.run(cmd_get(args))
    else:
        asyncio.run(cmd_all(args))
    return 0

if __name__ == "__main__":
    raise SystemExit(_pipeline_main())

#MadMad_2586