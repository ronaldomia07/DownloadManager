"""
Personal Download Manager — Power Edition (v6.1)
================================================
Everything from v6, with a rebuilt download core:

  SMART FEATURES
  • 🔑 Browser cookie import (Chrome / Firefox / Edge / Brave / Safari)
      -> downloads from sites that require login
  • 💾 Persistent queue — survives app restarts (saved to JSON)
  • 🕓 Download history with duplicate skipping (never grabs twice)
  • 📋 Clipboard watcher — copy a URL anywhere in your OS and a toast
      pops up: "Add to queue?" (toggleable)
  • ⏰ Scheduled start — delay downloads by N minutes
  • 🔄 Auto-retry with backoff (3 attempts on transient failures)
  • ⬆️ Auto-update yt-dlp on launch (keeps 1,000+ sites working)

  SPEED & CONTROL (v6.1 engine)
  • 🚀 Adaptive segmented engine — auto-scales parallel chunks to the
      file size, per-chunk retry with backoff, and crash-proof resume:
      partial chunk progress persists to disk, so pause / crash /
      network loss never lose bytes
  • 🐢 Token-bucket speed limiter — accurate throttling that stays
      correct across ALL parallel connections (shared rate, thread-safe)
  • Gzip-compressed responses auto-detected and routed to the simple
      downloader (Range requests are invalid for compressed streams)
  • ✏️ Filename template (e.g. %(uploader)s/%(title).60s.%(ext)s)

Requirements:
    pip install yt-dlp requests

Run:
    python download_manager.py
"""

import json
import os
import re
import sys
import time
import shutil
import threading
import queue
import mimetypes
import subprocess
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urljoin, urlparse
from tkinter import (
    Tk, Frame, Label, Entry, Button, StringVar, BooleanVar, DoubleVar,
    IntVar, OptionMenu, Spinbox, Toplevel, filedialog, messagebox, ttk, END
)

try:
    import yt_dlp
    HAS_YTDLP = True
except ImportError:
    HAS_YTDLP = False

try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

# ───────────────────────────────────────────────────── CONFIGURATION
PORT = 8765
MAX_PARALLEL = 3
SEGMENTS = 8                     # max parallel connections per file
SEGMENT_MIN_SIZE = 10 * 1048576  # only segment files > 10 MB
SEGMENT_CHUNK_TARGET = 25 * 1048576  # aim for chunks ≈ 25 MB each

HOME = os.path.expanduser("~")
SETTINGS_FILE = os.path.join(HOME, ".pdm_settings.json")
QUEUE_FILE = os.path.join(HOME, ".pdm_queue.json")
HISTORY_FILE = os.path.join(HOME, ".pdm_history.json")

COLORS = {
    "primary": "#6d4aff", "primary_dark": "#5a3fd4", "primary_light": "#8c7bff",
    "accent": "#00d4aa", "bg": "#fafafa", "surface": "#ffffff",
    "surface_light": "#f5f5f5", "border": "#e8e8e8", "text": "#222222",
    "text_muted": "#666666", "success": "#1a7f37", "warning": "#b8860b",
    "error": "#c62828",
}

QUALITY_PRESETS = {
    "Best available": None,
    "1080p": "bestvideo[height<=1080]+bestaudio/best[height<=1080]/best",
    "720p": "bestvideo[height<=720]+bestaudio/best[height<=720]/best",
    "480p": "bestvideo[height<=480]+bestaudio/best[height<=480]/best",
    "Audio only (mp3)": "bestaudio/best",
}

COOKIE_BROWSERS = ("None", "chrome", "firefox", "edge", "brave", "safari")
SPEED_LIMITS = {"Unlimited": 0, "1 MB/s": 1048576, "5 MB/s": 5 * 1048576,
                "10 MB/s": 10 * 1048576}
URL_RE = re.compile(r"^https?://\S+$", re.I)

MEDIA_EXT = re.compile(
    r"\.(mp4|m4v|mov|mkv|webm|flv|avi|wmv|ts|m3u8|mpd|"
    r"mp3|m4a|aac|ogg|oga|opus|wav|flac|"
    r"pdf|zip|rar|7z|doc|docx|xls|xlsx|ppt|pptx|exe|apk|iso|dmg|epub)"
    r"(\?|#|$)", re.I)

KIND_ICON = {"video": "🎬", "audio": "🎵", "stream": "📺",
             "file": "📦", "generic": "⬇️"}
LIBRARY_FOLDERS = {"video": "Videos", "stream": "Videos", "audio": "Audio",
                   "file": "Documents", "generic": "Other"}


# ──────────────────────────────────────────────────── small utilities
def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def save_json(path, data):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f)
    except Exception:
        pass


class TokenBucket:
    """Thread-safe token-bucket rate limiter.

    Shared by every parallel connection of a job, so the total
    bandwidth across all 8 chunks equals the chosen limit — the old
    per-chunk sleeper over-throttled and was inaccurate.
    Reads the rate dynamically, so changing the dropdown mid-download
    applies on the next chunk without restarting.
    """

    def __init__(self, rate_fn):
        self.rate_fn = rate_fn          # returns bytes/sec (0 = unlimited)
        self.tokens = 1 << 20
        self.timestamp = time.monotonic()
        self.lock = threading.Lock()

    def consume(self, nbytes):
        rate = self.rate_fn() or 0
        if rate <= 0:
            return
        capacity = max(rate, 1 << 16)
        while True:
            with self.lock:
                now = time.monotonic()
                self.tokens = min(capacity, self.tokens +
                                  (now - self.timestamp) * rate)
                self.timestamp = now
                if self.tokens >= nbytes:
                    self.tokens -= nbytes
                    return
                wait = (nbytes - self.tokens) / rate
            time.sleep(min(wait, 0.5))


class MediaSniffer:
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                          "AppleWebKit/537.36 Chrome/124.0 Safari/537.36"})

    def classify(self, url):
        u = url.lower().split("?")[0]
        if u.endswith((".m3u8", ".mpd")):
            return "stream"
        mime, _ = mimetypes.guess_type(u)
        if mime and mime.startswith("video"):
            return "video"
        if mime and mime.startswith("audio"):
            return "audio"
        if u.endswith((".mp4", ".webm", ".mkv", ".mov", ".flv")):
            return "video"
        if u.endswith((".mp3", ".m4a", ".aac", ".ogg", ".opus", ".wav",
                       ".flac")):
            return "audio"
        return "file"

    def sniff(self, page_url):
        resp = self.session.get(page_url, timeout=20)
        resp.raise_for_status()
        ctype = resp.headers.get("content-type", "")
        if MEDIA_EXT.search(page_url) or not ctype.startswith("text/"):
            return [(self.classify(page_url), page_url)]
        html, base, found = resp.text, resp.url, {}
        for m in re.finditer(r"<\s*([a-zA-Z][a-zA-Z0-9-]*)\b([^>]*)>", html):
            tag, attrs = m.group(1).lower(), m.group(2)
            if tag in ("video", "audio", "source", "embed", "a", "iframe"):
                for attr in ("src", "href", "data-src", "data-video",
                             "data-audio", "data-file"):
                    am = re.search(rf'{attr}\s*=\s*["\']([^"\']+)["\']',
                                   attrs, re.I)
                    if am:
                        full = urljoin(base, am.group(1).strip())
                        if MEDIA_EXT.search(full):
                            found[full] = self.classify(full)
        for m in re.finditer(r'https?://[^\s"\'<>\\]+',
                             html.replace("\\/", "/")):
            url = m.group(0).rstrip(",;)")
            if MEDIA_EXT.search(url):
                found.setdefault(url, self.classify(url))
        return sorted(found.items())


class CaptureServer(ThreadingHTTPServer):
    def __init__(self, app):
        self.app = app
        self.daemon_threads = True
        try:
            super().__init__(("127.0.0.1", PORT), self._make_handler())
        except OSError:
            app.log(f"⚠ Port {PORT} busy — realtime capture disabled")

    def _make_handler(self):
        app = self.app

        class Handler(BaseHTTPRequestHandler):
            def _cors(self):
                self.send_header("Access-Control-Allow-Origin", "*")
                self.send_header("Access-Control-Allow-Headers",
                                 "Content-Type")

            def do_OPTIONS(self):
                self.send_response(204)
                self._cors()
                self.end_headers()

            def do_GET(self):
                if self.path == "/ping":
                    self.send_response(200)
                    self._cors()
                    self.end_headers()
                    self.wfile.write(b'{"status":"ok"}')
                else:
                    self.send_response(404)
                    self.end_headers()

            def do_POST(self):
                if self.path != "/push":
                    self.send_response(404)
                    self.end_headers()
                    return
                try:
                    length = int(self.headers.get("Content-Length", 0))
                    data = json.loads(self.rfile.read(length))
                    accepted = app.accept_capture(
                        data.get("url", ""), data.get("kind", "generic"),
                        data.get("page", ""))
                    self.send_response(202 if accepted else 204)
                    self._cors()
                    self.end_headers()
                    self.wfile.write(json.dumps(
                        {"queued": accepted}).encode())
                except Exception:
                    self.send_response(400)
                    self.end_headers()

            def log_message(self, *a):
                pass

        return Handler


class DownloadJob:
    _next_id = 0

    def __init__(self, url, kind="generic", note=""):
        DownloadJob._next_id += 1
        self.uid = DownloadJob._next_id
        self.url = url
        self.kind = kind
        self.note = note
        text = note or url
        self.label = text[:55] + ("..." if len(text) > 55 else "")
        self.status = "Queued"
        self.progress = 0.0
        self.pause_requested = False

    def to_dict(self):
        return {"url": self.url, "kind": self.kind, "note": self.note}


class DownloadManager:
    def __init__(self, root: Tk):
        self.root = root
        root.title("⬇️ Download Manager — Power Edition")
        root.geometry("1060x680")
        root.minsize(860, 560)
        root.configure(bg=COLORS["bg"])

        self.jobs = []
        self.history = set(load_json(HISTORY_FILE, []))
        self.queue_msgs = queue.Queue()
        self.sniffer = MediaSniffer() if HAS_REQUESTS else None
        self.base_dir = os.path.join(HOME, "Downloads")
        self.capture_enabled = True
        self.active_workers = 0
        self.speed_limit_bps = 0
        self._last_clip = ""
        self._schedule_fired = False

        self._load_settings()
        self._restore_queue()
        self._build_ui()
        self._apply_styles()
        self._poll()
        threading.Thread(target=self._serve_capture, daemon=True).start()
        threading.Thread(target=self._auto_update_ytdlp, daemon=True).start()
        self._watch_clipboard()
        root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ───────────────────────────────────────────── persistence
    def _load_settings(self):
        s = load_json(SETTINGS_FILE, {})
        self.base_dir = s.get("base_dir", self.base_dir)
        self.skip_dupes = s.get("skip_dupes", True)

    def _save_settings(self):
        save_json(SETTINGS_FILE, {
            "base_dir": self.base_dir, "skip_dupes": self.skip_dupes})

    def _persist_queue(self):
        pending = [j.to_dict() for j in self.jobs
                   if j.status in ("Queued", "Paused", "Failed ✗")]
        save_json(QUEUE_FILE, pending)

    def _restore_queue(self):
        for item in load_json(QUEUE_FILE, []):
            job = DownloadJob(item["url"], item.get("kind", "generic"),
                              item.get("note", ""))
            self.jobs.append(job)  # UI rows added when UI is built

    def _on_close(self):
        self._persist_queue()
        self._save_settings()
        self.root.destroy()

    # ─────────────────────────────────────────── yt-dlp updater
    def _auto_update_ytdlp(self):
        if not HAS_YTDLP:
            return
        try:
            from importlib.metadata import version
            before = version("yt-dlp")
            if getattr(sys, "frozen", False):
                return  # frozen exe: rebuild with new yt-dlp instead
            subprocess.run(
                [sys.executable, "-m", "pip", "install", "-U", "-q",
                 "yt-dlp"], capture_output=True, timeout=300)
            after = version("yt-dlp")
            if before != after:
                self.log(f"⬆️ yt-dlp updated {before} → {after}. "
                         f"Restart the app to apply.")
        except Exception:
            pass

    # ─────────────────────────────────────────── clipboard watcher
    def _watch_clipboard(self):
        try:
            txt = self.root.clipboard_get().strip()
        except Exception:
            txt = ""
        if (txt and txt != self._last_clip and URL_RE.match(txt)
                and self.clip_var.get()):
            self._last_clip = txt
            self._show_clip_toast(txt)
        self.root.after(1500, self._watch_clipboard)

    def _show_clip_toast(self, url):
        toast = Toplevel(self.root)
        toast.overrideredirect(True)
        toast.attributes("-topmost", True)
        toast.configure(bg=COLORS["primary"])
        x = self.root.winfo_x() + self.root.winfo_width() - 330
        y = self.root.winfo_y() + self.root.winfo_height() - 110
        toast.geometry(f"320x80+{x}+{y}")
        Label(toast, text="📋 Link copied — add to downloads?",
              fg="white", bg=COLORS["primary"], anchor="w",
              padx=12, pady=6).pack(fill="x")
        row = Frame(toast, bg=COLORS["primary"])
        row.pack(fill="x", padx=12, pady=(0, 8))
        Label(row, text=url[:42] + "…", fg="#d9d0ff",
              bg=COLORS["primary"], anchor="w").pack(side="left",
                                                     fill="x", expand=True)

        def add_and_close():
            self._add_job(DownloadJob(url))
            toast.destroy()

        Button(row, text="＋ Add", command=add_and_close,
               bg="white", fg=COLORS["primary"], relief="flat",
               cursor="hand2").pack(side="left")
        Button(row, text="✕", command=toast.destroy,
               bg=COLORS["primary_dark"], fg="white", relief="flat",
               cursor="hand2").pack(side="left", padx=6)
        toast.after(6000, toast.destroy)

    # ───────────────────────────────────────────────────────── UI
    def _apply_styles(self):
        style = ttk.Style()
        if "clam" in style.theme_names():
            style.theme_use("clam")
        style.configure("Modern.Treeview", background=COLORS["surface"],
                        fieldbackground=COLORS["surface"],
                        rowheight=30, borderwidth=0)
        style.configure("Modern.Treeview.Heading", relief="flat",
                        foreground=COLORS["text_muted"], padding=(8, 6))
        style.configure("Accent.Horizontal.TProgressbar",
                        background=COLORS["primary"],
                        troughcolor=COLORS["border"], borderwidth=0)

    def _card(self, parent, title):
        outer = Frame(parent, bg=COLORS["border"], padx=1, pady=1)
        inner = Frame(outer, bg=COLORS["surface"])
        inner.pack(fill="both", expand=True)
        Label(inner, text=title, bg=COLORS["surface"], fg=COLORS["text"],
              anchor="w",
              font=("Segoe UI", 9, "bold")).pack(fill="x", padx=10,
                                                 pady=(8, 2))
        outer.pack(fill="x", pady=(0, 8))
        return inner

    def _build_ui(self):
        header = Frame(self.root, bg=COLORS["primary"], height=54)
        header.pack(fill="x")
        header.pack_propagate(False)
        Label(header, text="⬇️ Download Manager", fg="white",
              bg=COLORS["primary"],
              font=("Segoe UI", 13, "bold")).pack(side="left", padx=16)
        Label(header, text="Power Edition", fg="#d9d0ff",
              bg=COLORS["primary"]).pack(side="left", padx=4)
        self.status_line = Label(header, text="Ready.", fg="#e6ddff",
                                 bg=COLORS["primary"], anchor="e")
        self.status_line.pack(side="right", fill="x", expand=True, padx=16)

        main = Frame(self.root, bg=COLORS["bg"])
        main.pack(fill="both", expand=True, padx=12, pady=10)

        left = Frame(main, bg=COLORS["bg"])
        left.pack(side="left", fill="both", expand=True)

        # -- URL card
        urlc = self._card(left, "🔗 Add URL")
        row = Frame(urlc, bg=COLORS["surface"])
        row.pack(fill="x", padx=10, pady=(0, 8))
        self.url_var = StringVar()
        e = Entry(row, textvariable=self.url_var, relief="flat",
                  highlightthickness=1,
                  highlightcolor=COLORS["primary"],
                  highlightbackground=COLORS["border"])
        e.pack(side="left", fill="x", expand=True, ipady=6)
        e.bind("<Return>", lambda _: self.quick_add())
        Button(row, text="＋ Add", command=self.quick_add, relief="flat",
               bg=COLORS["primary"], fg="white", cursor="hand2",
               activebackground=COLORS["primary_dark"])\
            .pack(side="left", padx=(8, 0), ipadx=14, ipady=5)
        Button(row, text="🔍 Scan Page", command=self.detect_media,
               relief="solid", borderwidth=1, bg="white",
               fg=COLORS["primary"], cursor="hand2")\
            .pack(side="left", padx=(6, 0), ipadx=10, ipady=5)

        # -- options card
        opt = self._card(left, "⚙️ Options")
        r1 = Frame(opt, bg=COLORS["surface"])
        r1.pack(fill="x", padx=10, pady=2)
        Label(r1, text="Quality:", bg=COLORS["surface"],
              fg=COLORS["text_muted"]).pack(side="left")
        self.quality_var = StringVar(value="Best available")
        OptionMenu(r1, self.quality_var, *QUALITY_PRESETS.keys())\
            .pack(side="left", padx=(4, 14))
        Label(r1, text="Cookies:", bg=COLORS["surface"],
              fg=COLORS["text_muted"]).pack(side="left")
        self.cookie_var = StringVar(value="None")
        OptionMenu(r1, self.cookie_var, *COOKIE_BROWSERS)\
            .pack(side="left", padx=4)
        Label(r1, text="Limit:", bg=COLORS["surface"],
              fg=COLORS["text_muted"]).pack(side="left", padx=(14, 0))
        self.speed_var = StringVar(value="Unlimited")
        OptionMenu(r1, self.speed_var, *SPEED_LIMITS.keys(),
                   command=lambda v: self._set_speed(v))\
            .pack(side="left", padx=4)

        r2 = Frame(opt, bg=COLORS["surface"])
        r2.pack(fill="x", padx=10, pady=2)
        Label(r2, text="Filename template:", bg=COLORS["surface"],
              fg=COLORS["text_muted"]).pack(side="left")
        self.template_var = StringVar(value="%(title).60s.%(ext)s")
        Entry(r2, textvariable=self.template_var, width=34, relief="flat",
              highlightthickness=1, highlightbackground=COLORS["border"])\
            .pack(side="left", padx=6, ipady=3)
        Label(r2, text="Start in (min):", bg=COLORS["surface"],
              fg=COLORS["text_muted"]).pack(side="left", padx=(8, 0))
        self.schedule_min = IntVar(value=0)
        Spinbox(r2, from_=0, to=720, textvariable=self.schedule_min,
                width=5, relief="flat").pack(side="left", padx=4)

        r3 = Frame(opt, bg=COLORS["surface"])
        r3.pack(fill="x", padx=10, pady=(2, 8))
        self.clip_var = BooleanVar(value=True)
        self.playlist_var = BooleanVar(value=False)
        self.subs_var = BooleanVar(value=False)
        self.autostart_var = BooleanVar(value=False)
        self.capture_var = BooleanVar(value=True)
        self.dupe_var = BooleanVar(value=self.skip_dupes)
        for text, var in (("📋 Clipboard watch", self.clip_var),
                          ("📋 Playlists", self.playlist_var),
                          ("💬 Subs", self.subs_var),
                          ("⏩ Auto-start", self.autostart_var),
                          ("⚡ Realtime capture", self.capture_var),
                          ("🚫 Skip duplicates", self.dupe_var)):
            ttk.Checkbutton(r3, text=text, variable=var)\
                .pack(side="left", padx=(0, 10))

        # -- downloads card
        dlc = self._card(left, "📥 Downloads")
        tb = Frame(dlc, bg=COLORS["surface"])
        tb.pack(fill="x", padx=10, pady=(0, 6))
        self.start_btn = Button(tb, text="▶ Start", relief="flat",
                                bg=COLORS["primary"], fg="white",
                                cursor="hand2", command=self.start_downloads)
        self.start_btn.pack(side="left", ipadx=16, ipady=5)
        Button(tb, text="⏸ Pause", relief="flat", bg=COLORS["warning"],
               fg="white", cursor="hand2", command=self.pause_selected)\
            .pack(side="left", padx=6, ipadx=10, ipady=5)
        Button(tb, text="⏵ Resume", relief="flat", bg=COLORS["success"],
               fg="white", cursor="hand2", command=self.resume_selected)\
            .pack(side="left", ipadx=10, ipady=5)
        Button(tb, text="✖ Remove", relief="solid", borderwidth=1,
               bg="white", fg=COLORS["error"], cursor="hand2",
               command=self.remove_selected)\
            .pack(side="left", padx=6, ipadx=10, ipady=5)
        Button(tb, text="📂 Library", relief="solid", borderwidth=1,
               bg="white", fg=COLORS["text_muted"], cursor="hand2",
               command=self.open_folder).pack(side="right", ipadx=10,
                                              ipady=5)

        twrap = Frame(dlc, bg=COLORS["surface"])
        twrap.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        cols = ("label", "kind", "status", "progress")
        self.tree = ttk.Treeview(twrap, columns=cols, show="headings",
                                 style="Modern.Treeview")
        for col, text, w in (("label", "File", 400), ("kind", "Type", 45),
                             ("status", "Status", 105),
                             ("progress", "Progress", 80)):
            self.tree.heading(col, text=text)
            self.tree.column(col, width=w, anchor="w")
        self.tree.column("progress", anchor="center")
        sb = ttk.Scrollbar(twrap, orient="vertical",
                           command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        # detected card
        det = self._card(left, "🔎 Detected Media")
        dwrap = Frame(det, bg=COLORS["surface"])
        dwrap.pack(fill="both", expand=True, padx=10, pady=(0, 6))
        dcols = ("type", "url")
        self.det_tree = ttk.Treeview(dwrap, columns=dcols, show="headings",
                                     style="Modern.Treeview", height=5)
        self.det_tree.heading("type", text="Type")
        self.det_tree.column("type", width=70, anchor="center")
        self.det_tree.heading("url", text="URL")
        self.det_tree.column("url", width=600, anchor="w")
        dsb = ttk.Scrollbar(dwrap, orient="vertical",
                            command=self.det_tree.yview)
        self.det_tree.configure(yscrollcommand=dsb.set)
        self.det_tree.pack(side="left", fill="both", expand=True)
        dsb.pack(side="right", fill="y")
        drow = Frame(det, bg=COLORS["surface"])
        drow.pack(fill="x", padx=10, pady=(0, 8))
        Button(drow, text="＋ Add Selected", relief="flat",
               bg=COLORS["primary"], fg="white", cursor="hand2",
               command=self.add_detected).pack(side="left", ipadx=10,
                                               ipady=4)
        Button(drow, text="＋ Add All", relief="flat", bg=COLORS["accent"],
               fg="white", cursor="hand2",
               command=lambda: self.add_detected(True))\
            .pack(side="left", padx=8, ipadx=10, ipady=4)

        # -- right sidebar
        right = Frame(main, bg=COLORS["bg"], width=230)
        right.pack(side="right", fill="y", padx=(10, 0))
        right.pack_propagate(False)

        sc = self._card(right, "📊 Statistics")
        grid = Frame(sc, bg=COLORS["surface"])
        grid.pack(fill="x", padx=10, pady=(0, 10))
        self.stat_labels = {}
        for i, (key, label) in enumerate(
                (("queued", "Queued"), ("active", "Active"),
                 ("done", "Done"))):
            cell = Frame(grid, bg=COLORS["surface"])
            cell.grid(row=0, column=i, padx=10)
            self.stat_labels[key] = Label(cell, text="0", fg=COLORS["primary"],
                                          bg=COLORS["surface"],
                                          font=("Segoe UI", 14, "bold"))
            self.stat_labels[key].pack()
            Label(cell, text=label, fg=COLORS["text_muted"],
                  bg=COLORS["surface"],
                  font=("Segoe UI", 8)).pack()

        pc = self._card(right, "⚡ Overall Progress")
        self.overall_var = DoubleVar()
        ttk.Progressbar(pc, variable=self.overall_var, maximum=100,
                        style="Accent.Horizontal.TProgressbar")\
            .pack(fill="x", padx=10, pady=(0, 4))
        self.overall_label = Label(pc, text="0%", fg=COLORS["primary"],
                                   bg=COLORS["surface"],
                                   font=("Segoe UI", 11, "bold"))
        self.overall_label.pack(pady=(0, 8))

        hc = self._card(right, "🕓 Info")
        Label(hc, text=f"History: {len(self.history)} downloads",
              fg=COLORS["text_muted"], bg=COLORS["surface"],
              anchor="w").pack(fill="x", padx=10, pady=2)
        Label(hc, text=f"Capture port: {PORT}",
              fg=COLORS["text_muted"], bg=COLORS["surface"],
              anchor="w").pack(fill="x", padx=10, pady=2)
        Button(hc, text="🕒 Clear history", relief="flat", bg="white",
               fg=COLORS["error"], cursor="hand2",
               command=self.clear_history).pack(anchor="w", padx=10,
                                                pady=(2, 8))

        # restored queue rows
        for job in self.jobs:
            self.tree.insert("", END, iid=str(job.uid),
                             values=(job.label, KIND_ICON.get(job.kind, ""),
                                     job.status, "—"))

    # ─────────────────────────────────────────── helpers / state
    def log(self, msg):
        self.queue_msgs.put(("log", msg))

    def update_job(self, uid, **fields):
        self.queue_msgs.put(("update", uid, fields))

    def _set_speed(self, label):
        self.speed_limit_bps = SPEED_LIMITS.get(label, 0)

    def _add_job(self, job):
        url_key = job.url.split("#")[0].rstrip("/")
        if self.dupe_var.get():
            if any(j.url.split("#")[0].rstrip("/") == url_key
                   for j in self.jobs):
                self.log(f"🚫 Already in queue: {job.label}")
                return None
            if url_key in self.history:
                self.log(f"🚫 Already downloaded before: {job.label}")
                return None
        self.jobs.append(job)
        self.tree.insert("", END, iid=str(job.uid),
                         values=(job.label, KIND_ICON.get(job.kind, ""),
                                 job.status, "—"))
        self._refresh_stats()
        if self.autostart_var.get():
            self._dispatch()
        return job.uid

    def _refresh_stats(self):
        self.stat_labels["queued"].config(
            text=str(len([j for j in self.jobs if j.status == "Queued"])))
        self.stat_labels["active"].config(
            text=str(len([j for j in self.jobs
                          if j.status == "Downloading"])))
        self.stat_labels["done"].config(
            text=str(len([j for j in self.jobs
                          if j.status in ("Done ✓", "Failed ✗")])))

    def job_by_uid(self, uid):
        for j in self.jobs:
            if j.uid == uid:
                return j
        return None

    def quick_add(self):
        url = self.url_var.get().strip()
        if not url:
            return
        self._add_job(DownloadJob(url, "generic"))
        self.url_var.set("")

    def choose_folder(self):
        folder = filedialog.askdirectory(initialdir=self.base_dir)
        if folder:
            self.base_dir = folder

    def open_folder(self):
        if sys.platform == "win32":
            os.startfile(self.base_dir)          # noqa
        elif sys.platform == "darwin":
            os.system(f'open "{self.base_dir}"')
        else:
            os.system(f'xdg-open "{self.base_dir}"')

    def clear_history(self):
        self.history.clear()
        save_json(HISTORY_FILE, [])
        self.log("🕓 History cleared")

    # ─────────────────────────────────────────── capture server
    def _serve_capture(self):
        try:
            CaptureServer(self).serve_forever()
        except Exception as exc:
            self.log(f"⚠ Capture server error: {exc}")

    def accept_capture(self, url, kind, page):
        if not url or not self.capture_var.get():
            return False
        origin = urlparse(page).hostname if page else ""
        self.queue_msgs.put(("capture", (url, kind, origin)))
        return True

    # ─────────────────────────────────────────── job control
    def start_downloads(self):
        mins = self.schedule_min.get()
        if mins > 0 and not self._schedule_fired:
            self._schedule_fired = True
            self.log(f"⏰ Scheduled: starting in {mins} min")
            threading.Thread(
                target=lambda: (time.sleep(mins * 60),
                                self.queue_msgs.put(("fire", None))),
                daemon=True).start()
            return
        self._dispatch()

    def _dispatch(self):
        while self.active_workers < MAX_PARALLEL:
            nxt = next((j for j in self.jobs if j.status == "Queued"), None)
            if not nxt:
                break
            nxt.status = "Downloading"
            self.update_job(nxt.uid, status="Downloading")
            self.active_workers += 1
            threading.Thread(target=self._run_job, args=(nxt,),
                             daemon=True).start()

    def pause_selected(self):
        for item in self.tree.selection():
            job = self.job_by_uid(int(item))
            if job and job.status == "Downloading":
                job.pause_requested = True
                self.log(f"⏸ Pausing: {job.label}")

    def resume_selected(self):
        for item in self.tree.selection():
            job = self.job_by_uid(int(item))
            if job and job.status == "Paused":
                job.status = "Queued"
                job.pause_requested = False
                self.update_job(job.uid, status="Queued")
        self._dispatch()

    def remove_selected(self):
        for item in self.tree.selection():
            job = self.job_by_uid(int(item))
            if job and job.status == "Downloading":
                messagebox.showwarning("Busy", "Pause the job first.")
                continue
            if job:
                job.status = "Removed"
            self.tree.delete(item)
        self._refresh_stats()

    # ─────────────────────────────────────────── downloading
    def _run_job(self, job):
        bucket = TokenBucket(lambda: self.speed_limit_bps)
        try:
            ok = False
            for attempt in range(3):   # job-level auto-retry
                if job.pause_requested:
                    break
                if attempt:
                    delay = 3 * (2 ** (attempt - 1))
                    self.log(f"🔄 Retry {attempt}/3 in {delay}s: "
                             f"{job.label}")
                    time.sleep(delay)
                self.update_job(job.uid, progress=0)
                ok = self._download_one(job, bucket)
                if ok or job.pause_requested:
                    break
            if ok:
                self.history.add(job.url.split("#")[0].rstrip("/"))
                save_json(HISTORY_FILE, sorted(self.history))
                self.update_job(job.uid, status="Done ✓", progress=100)
            elif job.pause_requested:
                self.update_job(job.uid, status="Paused")
            else:
                self.update_job(job.uid, status="Failed ✗")
        except Exception as exc:
            self.log(f"✗ {job.label}: {exc}")
            self.update_job(job.uid, status="Failed ✗")
        finally:
            self.active_workers -= 1
            self.queue_msgs.put(("worker_done", None))
            self._persist_queue()

    def _download_one(self, job, bucket):
        if HAS_YTDLP:
            try:
                self._ytdlp(job)
                return True
            except Exception as exc:
                if job.pause_requested:
                    return False
                self.log(f"yt-dlp failed ({exc.__class__.__name__}); "
                         f"trying direct HTTP…")
        try:
            self._http(job, bucket)
            return True
        except Exception as exc:
            if not job.pause_requested:
                self.log(f"✗ {job.url} — {exc}")
            return False

    def _ytdlp(self, job):
        preset = QUALITY_PRESETS[self.quality_var.get()]
        outdir = os.path.join(self.base_dir,
                              LIBRARY_FOLDERS.get(job.kind, "Other"))
        os.makedirs(outdir, exist_ok=True)
        template = self.template_var.get().strip() or "%(title).60s.%(ext)s"
        opts = {
            "outtmpl": os.path.join(outdir, template),
            "quiet": True,
            "noplaylist": not self.playlist_var.get(),
            "concurrent_fragment_downloads": 4,
            "continuedl": True,
            "progress_hooks": [lambda d: self._hook(job, d)],
        }
        cookie = self.cookie_var.get()
        if cookie and cookie != "None":
            opts["cookiesfrombrowser"] = (cookie,)
        if self.speed_limit_bps:
            opts["ratelimit"] = self.speed_limit_bps
        if self.subs_var.get():
            opts["writesubtitles"] = True
            opts["subtitleslangs"] = ["en"]
        if preset == "bestaudio/best":
            opts["format"] = preset
            opts["postprocessors"] = [{
                "key": "FFmpegExtractAudio", "preferredcodec": "mp3",
                "preferredquality": "192"}]
        elif preset:
            opts["format"] = preset
        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(job.url, download=True)
            title = info.get("title") if isinstance(info, dict) else "media"
            self.log(f"✓ Saved: {title}")

    def _hook(self, job, d):
        if job.pause_requested:
            raise KeyboardInterrupt()
        if d["status"] == "downloading":
            total = d.get("total_bytes") or d.get("total_bytes_estimate")
            if total:
                self.update_job(job.uid,
                                progress=d["downloaded_bytes"] / total * 100)
        elif d["status"] == "finished":
            self.update_job(job.uid, progress=100)

    # ------------------------------------------------ HTTP engine v6.1
    def _http(self, job, bucket):
        if not HAS_REQUESTS:
            raise RuntimeError("'requests' not installed")
        outdir = os.path.join(self.base_dir,
                              LIBRARY_FOLDERS.get(job.kind, "Other"))
        os.makedirs(outdir, exist_ok=True)
        name = (os.path.basename(urlparse(job.url).path)
                or "download.bin")[:80]
        dest = os.path.join(outdir, name)
        headers = {"User-Agent": "Mozilla/5.0"}

        # Probe: size, range support, compression
        with requests.get(job.url, headers=headers, stream=True,
                          timeout=30) as probe:
            probe.raise_for_status()
            total = int(probe.headers.get("content-length", 0))
            accepts_ranges = probe.headers.get(
                "accept-ranges", "").lower() == "bytes"
            compressed = probe.headers.get("content-encoding",
                                           "identity") not in ("identity",
                                                               None, "")

        use_segments = (total > SEGMENT_MIN_SIZE and accepts_ranges
                        and not compressed)
        if use_segments:
            self._http_segmented(job, dest, total, headers, bucket)
        else:
            self._http_simple(job, dest, headers, total, bucket)
        self.log(f"✓ Saved: {dest}")

    def _http_simple(self, job, dest, headers, total, bucket):
        part = dest + ".part"
        done = 0
        h = dict(headers)
        if os.path.exists(part):
            done = os.path.getsize(part)
            h["Range"] = f"bytes={done}-"
        with requests.get(job.url, headers=h, stream=True,
                          timeout=30) as r:
            if r.status_code == 416:
                shutil.move(part, dest)
                return
            r.raise_for_status()
            if done and r.status_code != 206:
                done = 0
            total = int(r.headers.get("content-length", 0)) + done
            with open(part, "ab" if done else "wb") as f:
                for chunk in r.iter_content(1 << 16):
                    if job.pause_requested:
                        return
                    f.write(chunk)
                    done += len(chunk)
                    bucket.consume(len(chunk))
                    if total:
                        self.update_job(job.uid, progress=done / total * 100)
        shutil.move(part, dest)

    def _http_segmented(self, job, dest, total, headers, bucket):
        """Adaptive segmented download engine (v6.1).

        Improvements over v6:
          • Chunk count scales with file size (≈25 MB per chunk,
            capped at SEGMENTS) instead of always splitting into 8.
          • Each chunk retries independently with backoff — one flaky
            chunk no longer kills the whole file.
          • Chunk progress persists to <file>.segstate.json every
            second; after a pause, crash, or reboot the download
            resumes from exact byte offsets, only refetching what
            was truly lost.
          • Fail-fast: a permanently dead chunk stops its siblings.
        """
        n_seg = max(2, min(SEGMENTS, total // SEGMENT_CHUNK_TARGET))
        tmp = dest + ".tmp"
        state_path = dest + ".segstate.json"
        bounds = [round(i * total / n_seg) for i in range(n_seg + 1)]

        # Resume: load prior chunk offsets if they match this layout
        state = load_json(state_path, {})
        if state.get("total") == total and state.get("bounds") == bounds:
            done = list(state.get("done", [0] * n_seg))
            done += [0] * (n_seg - len(done))     # safety pad
        else:
            done = [0] * n_seg

        lock = threading.Lock()
        errors = []
        stop = threading.Event()
        counter = {"bytes": sum(done)}

        def seg_worker(idx):
            start, end = bounds[idx], bounds[idx + 1] - 1
            try:
                for attempt in range(3):
                    if job.pause_requested or stop.is_set():
                        raise InterruptedError()
                    try:
                        pos = start + done[idx]
                        if pos > end:
                            return          # chunk already complete
                        h = dict(headers)
                        h["Range"] = f"bytes={pos}-{end}"
                        with requests.get(job.url, headers=h, stream=True,
                                          timeout=30) as r:
                            if r.status_code == 416:
                                return
                            r.raise_for_status()
                            with open(tmp, "r+b") as f:
                                f.seek(pos)
                                for chunk in r.iter_content(1 << 16):
                                    if job.pause_requested or stop.is_set():
                                        raise InterruptedError()
                                    f.write(chunk)
                                    n = len(chunk)
                                    pos += n
                                    with lock:
                                        done[idx] = pos - start
                                        counter["bytes"] += n
                                    bucket.consume(n)
                        return
                    except InterruptedError:
                        raise
                    except Exception:
                        if attempt == 2:
                            raise
                        time.sleep(2 * (attempt + 1))
            except InterruptedError:
                stop.set()                   # pause: stop siblings too
            except Exception as exc:
                with lock:
                    errors.append(exc)
                stop.set()                   # fail fast: stop siblings

        threads = [threading.Thread(target=seg_worker, args=(i,),
                                    daemon=True) for i in range(n_seg)]
        for t in threads:
            t.start()

        last_save = 0.0
        try:
            while any(t.is_alive() for t in threads):
                now = time.monotonic()
                if now - last_save > 1.0:
                    with lock:
                        snapshot = list(done)
                    save_json(state_path, {"total": total,
                                           "bounds": bounds,
                                           "done": snapshot})
                    last_save = now
                self.update_job(job.uid,
                                progress=min(counter["bytes"] / total * 100,
                                             100.0))
                time.sleep(0.4)
        finally:
            for t in threads:
                t.join(timeout=2)
            if job.pause_requested:
                # keep tmp + state → resumable later
                with lock:
                    save_json(state_path, {"total": total,
                                           "bounds": bounds,
                                           "done": list(done)})
                raise InterruptedError()

        if errors:
            raise errors[0]
        if os.path.getsize(tmp) != total:
            raise RuntimeError("size mismatch after segmented download")
        if os.path.exists(state_path):
            os.remove(state_path)
        shutil.move(tmp, dest)
        self.update_job(job.uid, progress=100)

    # ─────────────────────────────────────────── page detection
    def detect_media(self):
        url = self.url_var.get().strip()
        if not url:
            messagebox.showinfo("Scan", "Paste a page URL first.")
            return
        if not self.sniffer:
            messagebox.showerror("Missing", "pip install requests")
            return
        self.log(f"🔍 Scanning {url} …")
        threading.Thread(target=self._detect_worker, args=(url,),
                         daemon=True).start()

    def _detect_worker(self, url):
        try:
            self.queue_msgs.put(("detected", self.sniffer.sniff(url)))
        except Exception as exc:
            self.log(f"✗ Detection failed: {exc}")

    def add_detected(self, all_items=False):
        rows = (self.det_tree.get_children() if all_items
                else self.det_tree.selection())
        for row in rows:
            kind, url = self.det_tree.item(row)["values"][:2]
            self._add_job(DownloadJob(str(url), str(kind)))

    # ─────────────────────────────────────────── UI event loop
    def _poll(self):
        try:
            while True:
                msg = self.queue_msgs.get_nowait()
                kind = msg[0]
                if kind == "log":
                    self.status_line.config(text=str(msg[1]))
                elif kind == "fire":
                    self._schedule_fired = False
                    self._dispatch()
                elif kind == "capture":
                    url, cap_kind, origin = msg[1]
                    job = DownloadJob(url, cap_kind, origin)
                    if self._add_job(job):
                        self.log(f"⚡ Captured {KIND_ICON.get(cap_kind, '')} "
                                 f"{url[:60]}")
                elif kind == "detected":
                    self.det_tree.delete(*self.det_tree.get_children())
                    for k_, url in msg[1]:
                        self.det_tree.insert("", END, values=(k_, url))
                    self.log(f"✓ Found {len(msg[1])} item(s)")
                elif kind == "update":
                    _, uid, fields = msg
                    job = self.job_by_uid(uid)
                    if not job:
                        continue
                    for k, v in fields.items():
                        setattr(job, k, v)
                    self.tree.set(str(uid), "status", job.status)
                    if "progress" in fields:
                        self.tree.set(str(uid), "progress",
                                      f"{job.progress:.0f}%")
                    active = [j for j in self.jobs
                              if j.status == "Downloading"]
                    if active:
                        ov = sum(j.progress for j in active) / len(active)
                        self.overall_var.set(ov)
                        self.overall_label.config(text=f"{ov:.0f}%")
                elif kind == "worker_done":
                    self._dispatch()
                    self._refresh_stats()
        except queue.Empty:
            pass
        self.root.after(150, self._poll)


def main():
    root = Tk()
    if sys.platform == "win32":
        try:
            from ctypes import windll
            windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    DownloadManager(root)
    root.mainloop()


if __name__ == "__main__":
    main()
