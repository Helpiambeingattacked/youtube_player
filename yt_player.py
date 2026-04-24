#!/usr/bin/env python3
"""
YT Player  —  robust rewrite
Fixes: generation races, VLC-state drift vs boolean, PiP drag/resize variable
       collision, stream-cache key collision, stale prefetch, error auto-skip,
       double-advance on Ended, socket leak, misplaced import, missing guards,
       PiP volume desync, and assorted UI edge cases.
"""
from __future__ import annotations
 
import io
import json
import os
import random
import socket
import threading
import time
import urllib.request
from typing import Optional
 
import tkinter as tk
from tkinter import ttk
 
import yt_dlp
import vlc
 
try:
    from PIL import Image, ImageTk
    PIL_OK = True
except ImportError:
    PIL_OK = False
 
# ── Config ─────────────────────────────────────────────────────────────────
PLAYLIST_URL     = ""
CACHE_FILE       = "playlist_cache.json"
DOWNLOAD_DIR     = "downloads"
STREAM_CACHE_TTL = 1800  # seconds before a cached stream URL is re-fetched
 
SPEEDS    = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0]
QUALITIES = ["best", "1080p", "720p", "480p", "360p", "240p", "144p", "audio only"]
 
# ── Palette ─────────────────────────────────────────────────────────────────
BG      = "#0f0f0f"
SURFACE = "#1a1a1a"
BORDER  = "#252525"
ACCENT  = "#ff3c3c"
FG      = "#e8e8e8"
FG_DIM  = "#555555"
FG_MID  = "#888888"
PIP_BG  = "#0d0d0d"
PIP_FG  = "#dddddd"
PIP_DIM = "#666666"
 
# ── Layout ──────────────────────────────────────────────────────────────────
WIN_W      = 480
COMPACT_H  = 108
EXPANDED_H = 520
VIDEO_H    = 240
PIP_BAR_H  = 42
PIP_GRIP_H = 14
 
 
# ── Helpers ─────────────────────────────────────────────────────────────────
 
def video_id(url: str) -> Optional[str]:
    """Extract the 11-char YouTube video ID from any URL variant."""
    for sep in ("v=", "youtu.be/", "/embed/", "/shorts/"):
        if sep in url:
            vid = url.split(sep)[-1].split("&")[0].split("?")[0]
            if len(vid) == 11:
                return vid
    return None
 
 
def fetch_thumb(url: str) -> Optional["ImageTk.PhotoImage"]:
    if not PIL_OK:
        return None
    vid = video_id(url)
    if not vid:
        return None
    try:
        thumb_url = f"https://img.youtube.com/vi/{vid}/mqdefault.jpg"
        with urllib.request.urlopen(thumb_url, timeout=5) as r:
            data = r.read()
        img = Image.open(io.BytesIO(data)).resize((80, 56), Image.LANCZOS)
        return ImageTk.PhotoImage(img)
    except Exception:
        return None
 
 
def fmt_ms(ms: int) -> str:
    if ms <= 0:
        return "0:00"
    s = ms // 1000
    return f"{s // 60}:{s % 60:02d}"
 
 
def check_internet(host: str = "8.8.8.8", port: int = 53, timeout: float = 3.0) -> bool:
    """Returns True if the network is reachable. Always closes the socket."""
    sock: Optional[socket.socket] = None
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(timeout)
        sock.connect((host, port))
        return True
    except Exception:
        return False
    finally:
        if sock:
            try:
                sock.close()
            except Exception:
                pass
 
 
# ── Player ──────────────────────────────────────────────────────────────────
 
class YTPlayer:
 
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("YT Player")
        self.root.configure(bg=BG)
        self.root.resizable(True, False)
 
        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
 
        # ── Track state ──────────────────────────────────────────────────
        self.tracks:          list[dict] = []
        self.filtered_tracks: list[dict] = []
        self.current_index               = 0
        self.in_search_mode              = False
 
        # ── Playback state ───────────────────────────────────────────────
        self._seeking            = False   # user is dragging the main seek bar
        self._shuffle            = False
        self._repeat             = False
        self._shuffle_history:   list[int] = []
        # Generation counter: incremented on every new load.  Any in-flight
        # callback captures the gen at the time of dispatch and bails if it
        # no longer matches self._load_gen by the time it runs on the main thread.
        self._load_gen           = 0
        # Prevents _tick from scheduling _next_track more than once per ending.
        self._auto_next_sched    = False
        # URL of the last track that errored, so _tick doesn't re-trigger it.
        self._error_url: Optional[str] = None
 
        # ── Prefetch ─────────────────────────────────────────────────────
        # A separate generation counter for the prefetch thread so a stale
        # prefetch result (e.g. quality changed while prefetching) is discarded.
        self._prefetch_gen                = 0
        self._prefetch_index: Optional[int]  = None
        self._prefetch_cache: Optional[dict] = None  # {"v_url","a_url","title","fingerprint"}
 
        # ── Stream URL cache ─────────────────────────────────────────────
        # Key: (video_url, fingerprint_tuple) → {"v_url","a_url","title","ts"}
        # Using a compound key means a quality/video change never reuses a
        # cache entry from a different format.
        self._stream_cache: dict[tuple, dict] = {}
 
        # ── UI flags ─────────────────────────────────────────────────────
        self._video_enabled  = False
        self._playlist_open  = False
        self._thumb_ref: Optional["ImageTk.PhotoImage"] = None
 
        # ── PiP state ────────────────────────────────────────────────────
        self._pip_win:      Optional[tk.Toplevel]   = None
        self._pip_vframe:   Optional[tk.Frame]      = None
        self._pip_play_btn: Optional[tk.Button]     = None
        self._pip_time_var: Optional[tk.StringVar]  = None
        self._pip_seek_var: Optional[tk.DoubleVar]  = None
        self._pip_seeking   = False
        # Drag and resize use SEPARATE variable pairs to avoid mutual corruption.
        self._drag_ox = self._drag_oy = 0      # drag origin offsets
        self._rsz_ox  = self._rsz_oy  = 0      # resize start pointer coords
        self._rsz_w   = self._rsz_h   = 0      # resize start window size
 
        # ── VLC ──────────────────────────────────────────────────────────
        vout_arg = "--vout=any" if os.name == "nt" \
                   else "--vout=xcb_xv,xcb_x11,x11,any"
        self.vlc_inst = vlc.Instance("--quiet", "--no-video-title-show", vout_arg)
        self.player   = self.vlc_inst.media_player_new()
        em = self.player.event_manager()
        # VLC fires MediaPlayerVout when the output is ready; we use it to
        # (re-)attach the window handle in case VLC created its own window.
        em.event_attach(vlc.EventType.MediaPlayerVout,
                        lambda _: self.root.after(0, self._attach_vout))
 
        self._build_ui()
        self._apply_styles()
        self.root.update_idletasks()
        req_w = max(WIN_W, self.root.winfo_reqwidth())
        req_h = self.root.winfo_reqheight()
        self.root.geometry(f"{req_w}x{req_h}")
        self.root.minsize(req_w, req_h)
        self._load_or_fetch_playlist()
        self._tick()
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Computed properties
    # ═══════════════════════════════════════════════════════════════════════
 
    @property
    def _is_playing(self) -> bool:
        """Ground-truth: ask VLC directly instead of tracking a boolean."""
        return self.player.get_state() == vlc.State.Playing
 
    @property
    def _pip_open(self) -> bool:
        return bool(self._pip_win and self._pip_win.winfo_exists())
 
    # ═══════════════════════════════════════════════════════════════════════
    #  UI construction
    # ═══════════════════════════════════════════════════════════════════════
 
    def _build_ui(self):
        # ── Top bar: thumbnail + meta ─────────────────────────────────────
        top = tk.Frame(self.root, bg=SURFACE)
        top.pack(fill=tk.X)
 
        self.thumb_canvas = tk.Canvas(top, width=80, height=56,
                                      bg=BORDER, highlightthickness=0)
        self.thumb_canvas.pack(side=tk.LEFT)
        self._draw_thumb_placeholder()
 
        meta = tk.Frame(top, bg=SURFACE)
        meta.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=8, pady=4)
 
        self.title_var = tk.StringVar(value="No track loaded")
        tk.Label(meta, textvariable=self.title_var,
                 bg=SURFACE, fg=FG, font=("Helvetica", 9, "bold"),
                 anchor="w", wraplength=260, justify="left").pack(fill=tk.X)
 
        self.status_var = tk.StringVar(value="Starting…")
        tk.Label(meta, textvariable=self.status_var,
                 bg=SURFACE, fg=FG_DIM, font=("Courier", 8),
                 anchor="w").pack(fill=tk.X)
 
        self.time_var = tk.StringVar(value="0:00 / 0:00")
        tk.Label(meta, textvariable=self.time_var,
                 bg=SURFACE, fg=FG_MID, font=("Courier", 8),
                 anchor="w").pack(fill=tk.X)
 
        # ── Seek bar ─────────────────────────────────────────────────────
        self.seek_var = tk.DoubleVar()
        self.seek_bar = ttk.Scale(self.root, from_=0, to=100,
                                  orient=tk.HORIZONTAL, variable=self.seek_var,
                                  style="A.Horizontal.TScale")
        self.seek_bar.pack(fill=tk.X)
        self.seek_bar.bind("<ButtonPress-1>",   lambda _: setattr(self, "_seeking", True))
        self.seek_bar.bind("<ButtonRelease-1>", self._on_seek)
 
        # ── Video frame (hidden until enabled) ───────────────────────────
        # pack_propagate(False) + explicit width/height so the frame keeps its
        # size even when VLC hasn't drawn anything yet.
        self.video_frame = tk.Frame(self.root, bg="black",
                                    width=WIN_W, height=VIDEO_H)
        self.video_frame.pack_propagate(False)
 
        # ── Controls ─────────────────────────────────────────────────────
        self.ctrl_frame = tk.Frame(self.root, bg=BG, pady=4)
        self.ctrl_frame.pack(fill=tk.X, padx=6)
 
        left = tk.Frame(self.ctrl_frame, bg=BG)
        left.pack(side=tk.LEFT)
 
        self.shuffle_btn = self._mkbtn(left, "⇄", self._toggle_shuffle, dim=True)
        self.shuffle_btn.pack(side=tk.LEFT)
        self._mkbtn(left, "⏮", self._prev_track).pack(side=tk.LEFT, padx=2)
        self.play_btn = self._mkbtn(left, "▶", self._toggle_play,
                                    big=True, state=tk.DISABLED)
        self.play_btn.pack(side=tk.LEFT, padx=4)
        self._mkbtn(left, "⏭", self._next_track).pack(side=tk.LEFT, padx=2)
        self.repeat_btn = self._mkbtn(left, "↻", self._toggle_repeat, dim=True)
        self.repeat_btn.pack(side=tk.LEFT)
 
        right = tk.Frame(self.ctrl_frame, bg=BG)
        right.pack(side=tk.RIGHT)
 
        self.dl_btn = self._mkbtn(right, "⬇", self._download_current, dim=True)
        self.dl_btn.pack(side=tk.LEFT, padx=(0, 4))
 
        self.pip_btn = self._mkbtn(right, "⧉", self._toggle_pip, dim=True)
        self.pip_btn.pack(side=tk.LEFT, padx=(0, 4))
 
        self.vid_btn = self._mkbtn(right, "🎬", self._toggle_video, dim=True)
        self.vid_btn.pack(side=tk.LEFT, padx=(0, 6))
 
        tk.Label(right, text="HD", bg=BG, fg=FG_DIM,
                 font=("Courier", 7)).pack(side=tk.LEFT, padx=(0, 2))
        self.quality_var = tk.StringVar(value="best")
        self._make_optmenu(right, self.quality_var, QUALITIES,
                           self._on_quality_change).pack(side=tk.LEFT, padx=(0, 8))
 
        tk.Label(right, text="SPD", bg=BG, fg=FG_DIM,
                 font=("Courier", 7)).pack(side=tk.LEFT, padx=(0, 2))
        self.speed_var = tk.StringVar(value="1.0x")
        self._make_optmenu(right, self.speed_var,
                           [f"{s}x" for s in SPEEDS],
                           lambda _: self._apply_speed()
                           ).pack(side=tk.LEFT, padx=(0, 8))
 
        tk.Label(right, text="🔊", bg=BG, fg=FG_DIM,
                 font=("Helvetica", 9)).pack(side=tk.LEFT)
        # vol_var is SHARED with the PiP volume slider so they always match.
        self.vol_var = tk.IntVar(value=80)
        self.vol_var.trace_add("write", lambda *_: self.player.audio_set_volume(
            self.vol_var.get()))
        ttk.Scale(right, from_=0, to=100, orient=tk.HORIZONTAL,
                  length=72, variable=self.vol_var,
                  style="A.Horizontal.TScale").pack(side=tk.LEFT, padx=(2, 8))
        self.player.audio_set_volume(80)
 
        self.list_btn = self._mkbtn(right, "☰", self._toggle_playlist, dim=True)
        self.list_btn.pack(side=tk.LEFT)
 
        # ── Playlist panel ───────────────────────────────────────────────
        self.playlist_frame = tk.Frame(self.root, bg=BG)
 
        sf = tk.Frame(self.playlist_frame, bg=BG, pady=3, padx=6)
        sf.pack(fill=tk.X)
        tk.Label(sf, text="🔍", bg=BG, fg=FG_DIM,
                 font=("Helvetica", 10)).pack(side=tk.LEFT, padx=(0, 3))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", self._on_search_type)
        se = tk.Entry(sf, textvariable=self.search_var,
                      bg=SURFACE, fg=FG, insertbackground=FG,
                      relief=tk.FLAT, font=("Courier", 9),
                      highlightthickness=1, highlightbackground=BORDER,
                      highlightcolor=ACCENT)
        se.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=3)
        se.bind("<Return>",  self._on_search_enter)
        se.bind("<Escape>",  lambda _: self._back_to_playlist())
 
        self.count_var = tk.StringVar(value="")
        tk.Label(sf, textvariable=self.count_var, bg=BG, fg=FG_DIM,
                 font=("Courier", 8), width=9,
                 anchor="e").pack(side=tk.RIGHT, padx=(4, 0))
 
        self.hint_var = tk.StringVar(value="↵ to search YouTube")
        tk.Label(self.playlist_frame, textvariable=self.hint_var,
                 bg=BG, fg=FG_DIM, font=("Courier", 7),
                 anchor="e").pack(fill=tk.X, padx=8)
 
        lf = tk.Frame(self.playlist_frame, bg=BORDER, padx=1, pady=1)
        lf.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 4))
        inner = tk.Frame(lf, bg=BG)
        inner.pack(fill=tk.BOTH, expand=True)
        sb = tk.Scrollbar(inner, bg=SURFACE, troughcolor=BG,
                          activebackground=ACCENT, highlightthickness=0,
                          relief=tk.FLAT, width=8)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.listbox = tk.Listbox(inner, bg=BG, fg=FG_MID,
                                  selectbackground=ACCENT, selectforeground=FG,
                                  font=("Courier", 9), relief=tk.FLAT, bd=0,
                                  activestyle="none", highlightthickness=0,
                                  yscrollcommand=sb.set)
        self.listbox.pack(fill=tk.BOTH, expand=True)
        sb.config(command=self.listbox.yview)
        self.listbox.bind("<Double-Button-1>", self._on_listbox_dbl)
        self.listbox.bind("<Return>",          self._on_listbox_dbl)
 
        rf = tk.Frame(self.playlist_frame, bg=BG, pady=2)
        rf.pack(fill=tk.X, padx=6)
 
        # back_btn is packed/unpacked dynamically when entering/leaving search mode
        self.back_btn = self._mkbtn(rf, "← playlist", self._back_to_playlist,
                                    dim=True, fnt=("Courier", 8))
        self.dl_all_btn = self._mkbtn(rf, "⬇ All", self._download_all,
                                      dim=True, fnt=("Courier", 8))
        self.dl_all_btn.pack(side=tk.LEFT, padx=(4, 0))
        self._mkbtn(rf, "⟳ Refresh from YouTube", self._refresh_playlist,
                    dim=True, fnt=("Courier", 8)).pack(side=tk.RIGHT)
 
    # ── Widget factories ─────────────────────────────────────────────────
 
    def _mkbtn(self, parent, text, cmd, big=False, dim=False,
               state=tk.NORMAL, fnt=None) -> tk.Button:
        return tk.Button(
            parent, text=text, command=cmd,
            bg=BG, fg=FG_DIM if dim else FG_MID,
            activebackground=BG, activeforeground=ACCENT,
            relief=tk.FLAT, bd=0, cursor="hand2",
            font=fnt or ("Helvetica", 14 if big else 10),
            state=state,
        )
 
    def _make_optmenu(self, parent, var, choices, cmd) -> tk.OptionMenu:
        om = tk.OptionMenu(parent, var, *choices, command=cmd)
        om.config(bg=SURFACE, fg=FG_MID, activebackground=ACCENT,
                  activeforeground=FG, relief=tk.FLAT, highlightthickness=0,
                  font=("Courier", 8), bd=0, indicatoron=False, width=6)
        om["menu"].config(bg=SURFACE, fg=FG_MID, activebackground=ACCENT,
                          activeforeground=FG, font=("Courier", 8), relief=tk.FLAT)
        return om
 
    def _apply_styles(self):
        s = ttk.Style()
        s.theme_use("clam")
        s.configure("A.Horizontal.TScale", background=BG, troughcolor=BORDER,
                    sliderthickness=12, sliderrelief="flat")
        s.map("A.Horizontal.TScale",
              background=[("active", BG)],
              troughcolor=[("active", BORDER)])
 
    def _draw_thumb_placeholder(self):
        self.thumb_canvas.delete("all")
        self.thumb_canvas.create_rectangle(0, 0, 80, 56, fill=BORDER, outline="")
        self.thumb_canvas.create_text(40, 28, text="♪", fill=FG_DIM,
                                      font=("Georgia", 18))
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Geometry helpers
    # ═══════════════════════════════════════════════════════════════════════
 
    def _compact_h(self) -> int:
        """Return the window height that exactly fits the current visible widgets."""
        video_was_packed = self._video_enabled
        if video_was_packed:
            self.video_frame.pack_forget()
        self.root.update_idletasks()
        h = self.root.winfo_reqheight()
        if video_was_packed:
            self.video_frame.pack(fill=tk.BOTH, before=self.ctrl_frame)
        return h

    def _expanded_h(self) -> int:
        """Return the height when the playlist panel is shown."""
        was_open = self._playlist_open
        if not was_open:
            self.playlist_frame.pack(fill=tk.BOTH, expand=True)
        self.root.update_idletasks()
        h = self.root.winfo_reqheight()
        if not was_open:
            self.playlist_frame.pack_forget()
        return h
 
    def _resize(self, h: int):
        self.root.update_idletasks()
        min_h = self.root.winfo_reqheight()
        if h < min_h:
            h = min_h
        self.root.geometry(f"{self.root.winfo_width()}x{h}")
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Playlist loading
    # ═══════════════════════════════════════════════════════════════════════
 
    def _load_or_fetch_playlist(self):
        if os.path.exists(CACHE_FILE):
            try:
                with open(CACHE_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if data.get("url") == PLAYLIST_URL and data.get("tracks"):
                    self.tracks = data["tracks"]
                    self._populate_list(self.tracks)
                    self.status_var.set(f"{len(self.tracks)} tracks · cached")
                    self.play_btn.config(state=tk.NORMAL)
                    self._play_track(0)
                    return
            except Exception:
                pass
        threading.Thread(target=self._fetch_playlist, daemon=True).start()
 
    def _fetch_playlist(self):
        self.root.after(0, lambda: self.status_var.set("Fetching playlist…"))
        try:
            with yt_dlp.YoutubeDL({"extract_flat": True, "quiet": True}) as ydl:
                info = ydl.extract_info(PLAYLIST_URL, download=False)
            entries = info.get("entries") or [info]
            self.tracks = [
                {"url":   e.get("url") or e.get("webpage_url", ""),
                 "title": e.get("title", "Unknown")}
                for e in entries if e
            ]
            try:
                with open(CACHE_FILE, "w", encoding="utf-8") as f:
                    json.dump({"url": PLAYLIST_URL, "tracks": self.tracks},
                              f, ensure_ascii=False, indent=2)
            except Exception:
                pass
            self.root.after(0, self._on_playlist_ready)
        except Exception as exc:
            self.root.after(0, lambda: self.status_var.set(f"Error: {exc}"))
 
    def _on_playlist_ready(self):
        self._populate_list(self.tracks)
        self.status_var.set(f"{len(self.tracks)} tracks loaded")
        self.play_btn.config(state=tk.NORMAL)
        self._play_track(0)
 
    def _refresh_playlist(self):
        if os.path.exists(CACHE_FILE):
            os.remove(CACHE_FILE)
        self.tracks = []
        self.in_search_mode = False
        self.listbox.delete(0, tk.END)
        threading.Thread(target=self._fetch_playlist, daemon=True).start()
 
    def _populate_list(self, track_list: list[dict]):
        self.filtered_tracks = track_list
        self.listbox.delete(0, tk.END)
        for t in track_list:
            self.listbox.insert(tk.END, f"  {t['title']}")
        shown = len(track_list)
        total = len(self.tracks)
        self.count_var.set(f"{shown}/{total}" if shown != total else f"{total} tracks")
 
    def _highlight_row(self, index: int):
        self.listbox.selection_clear(0, tk.END)
        if 0 <= index < self.listbox.size():
            self.listbox.selection_set(index)
            self.listbox.see(index)
 
    # ── Search ───────────────────────────────────────────────────────────
 
    def _on_search_type(self, *_):
        # While showing external search results don't filter on every keystroke.
        if self.in_search_mode:
            return
        q = self.search_var.get().lower().strip()
        filtered = [t for t in self.tracks if q in t["title"].lower()] if q else self.tracks
        self._populate_list(filtered)
 
    def _on_search_enter(self, _event=None):
        q = self.search_var.get().strip()
        if q:
            self._yt_search(q)
 
    def _yt_search(self, query: str):
        self.status_var.set(f'Searching "{query}"…')
        self.hint_var.set("searching YouTube…")
        threading.Thread(target=self._fetch_search, args=(query,), daemon=True).start()
 
    def _fetch_search(self, query: str):
        try:
            with yt_dlp.YoutubeDL({"extract_flat": True, "quiet": True,
                                    "skip_download": True}) as ydl:
                info = ydl.extract_info(f"ytsearch15:{query}", download=False)
            results: list[dict] = []
            for e in (info.get("entries") or []):
                if not e:
                    continue
                vid = e.get("id") or ""
                url = (f"https://www.youtube.com/watch?v={vid}"
                       if len(vid) == 11 else e.get("url", ""))
                if url:
                    results.append({"title": e.get("title", "Unknown"), "url": url})
            self.root.after(0, lambda: self._show_search_results(results, query))
        except Exception as exc:
            self.root.after(0, lambda: (
                self.status_var.set(f"Search error: {exc}"),
                self.hint_var.set("↵ to search YouTube"),
            ))
 
    def _show_search_results(self, results: list[dict], query: str):
        self.in_search_mode  = True
        self.filtered_tracks = results
        self.back_btn.pack(side=tk.LEFT, padx=(0, 4))
        self.listbox.delete(0, tk.END)
        for t in results:
            self.listbox.insert(tk.END, f"  {t['title']}")
        self.count_var.set(f"{len(results)} results")
        self.hint_var.set(f'results for "{query}"')
        self.status_var.set(f"{len(results)} results · ↵ new search")
        self.play_btn.config(state=tk.NORMAL)
 
    def _back_to_playlist(self):
        if not self.in_search_mode:
            return
        self.in_search_mode = False
        self.back_btn.pack_forget()
        self.search_var.set("")
        self.hint_var.set("↵ to search YouTube")
        self._populate_list(self.tracks)
        self.status_var.set(f"{len(self.tracks)} tracks")
 
    def _on_listbox_dbl(self, _event=None):
        sel = self.listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        if 0 <= idx < len(self.filtered_tracks):
            self.current_index = idx
            self._play_track(idx)
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Playback core
    # ═══════════════════════════════════════════════════════════════════════
 
    def _play_track(self, index: int):
        if not self.filtered_tracks:
            return
        index = max(0, min(index, len(self.filtered_tracks) - 1))
        self.current_index = index
 
        # Bump generation.  Every async callback captures 'gen' and will
        # silently bail if self._load_gen has moved on by the time it fires.
        self._load_gen += 1
        gen = self._load_gen
 
        self._auto_next_sched = False
        self._error_url       = None
 
        track = self.filtered_tracks[index]
        self._highlight_row(index)
        self.title_var.set(track["title"])
        self.status_var.set(f"Loading… {index + 1}/{len(self.filtered_tracks)}")
 
        # Clean VLC state before loading the next item.
        self.player.stop()
        self.seek_var.set(0)
        self.time_var.set("0:00 / 0:00")
        self.play_btn.config(text="▶")
        self._sync_pip_play_btn()
 
        self._draw_thumb_placeholder()
        self._thumb_ref = None
        threading.Thread(target=self._load_thumb,
                         args=(track["url"], gen), daemon=True).start()
 
        # Resolution priority: local file → valid prefetch → fresh yt-dlp call.
        local = self._get_local_file(track["url"])
        if local and not self._video_enabled and not self._pip_open:
            self.root.after(0, lambda: self._start_local(local, track["title"], gen))
        elif self._prefetch_ready(index):
            pc = self._prefetch_cache
            self._prefetch_cache = None
            self._prefetch_index = None
            self.root.after(0, lambda: self._start_vlc(
                pc["v_url"], pc["a_url"], pc["title"], gen))
        else:
            threading.Thread(target=self._fetch_and_play,
                             args=(track["url"], gen), daemon=True).start()
 
        # Kick off prefetch for the next track (skip when in search results).
        if not self.in_search_mode and index + 1 < len(self.filtered_tracks):
            self._prefetch_gen += 1
            pg = self._prefetch_gen
            threading.Thread(target=self._prefetch_track,
                             args=(index + 1, pg), daemon=True).start()
 
    def _prefetch_ready(self, index: int) -> bool:
        """True only when the cached prefetch matches both index and current format."""
        if self._prefetch_index != index or not self._prefetch_cache:
            return False
        return self._prefetch_cache.get("fingerprint") == self._format_fingerprint()
 
    def _prefetch_track(self, index: int, pg: int):
        if not check_internet():
            return
        if index >= len(self.filtered_tracks):
            return
        track = self.filtered_tracks[index]
        if self._get_local_file(track["url"]):
            return  # already downloaded, no need to prefetch stream URL
        try:
            v_url, a_url, title = self._resolve_stream(track["url"])
            # Only store result if this prefetch generation is still current.
            if pg == self._prefetch_gen:
                self._prefetch_cache = {
                    "v_url": v_url, "a_url": a_url, "title": title,
                    "fingerprint": self._format_fingerprint(),
                }
                self._prefetch_index = index
        except Exception:
            pass
 
    def _fetch_and_play(self, video_url: str, gen: int):
        try:
            v_url, a_url, title = self._resolve_stream(video_url)
            self.root.after(0, lambda: self._start_vlc(v_url, a_url, title, gen))
        except Exception as exc:
            self.root.after(0, lambda: self._on_load_error(video_url, exc, gen))
 
    def _on_load_error(self, video_url: str, exc: Exception, gen: int):
        if gen != self._load_gen:
            return
        self.status_var.set(f"Error: {str(exc)[:55]}")
        self._error_url = video_url
        self.play_btn.config(text="▶")
        self._sync_pip_play_btn()
 
    def _start_local(self, filepath: str, title: str, gen: int):
        if gen != self._load_gen:
            return
        media = self.vlc_inst.media_new(filepath)
        self.player.set_media(media)
        self._attach_vout()
        self.player.play()
        self._apply_speed()
        self.play_btn.config(text="⏸")
        self._sync_pip_play_btn()
        self.title_var.set(title)
        self.status_var.set(f"{self.current_index + 1} of {len(self.filtered_tracks)} · local")
 
    def _start_vlc(self, v_url: str, a_url: Optional[str], title: str, gen: int):
        if gen != self._load_gen:
            return
        media = self.vlc_inst.media_new(v_url)
        if a_url:
            media.add_option(f":input-slave={a_url}")
        self.player.set_media(media)
        self._attach_vout()
        self.player.play()
        self._apply_speed()
        self.play_btn.config(text="⏸")
        self._sync_pip_play_btn()
        self.title_var.set(title)
        self.status_var.set(f"{self.current_index + 1} of {len(self.filtered_tracks)}")
 
    # ── Stream resolution ────────────────────────────────────────────────
 
    def _format_fingerprint(self) -> tuple:
        """Unique identifier for the current stream format requirements."""
        need_video = self._video_enabled or self._pip_open
        return (need_video, self.quality_var.get())
 
    def _get_format_string(self) -> str:
        need_video, q = self._format_fingerprint()
        if not need_video or q == "audio only":
            return "bestaudio[ext=m4a]/bestaudio/best"
        base = "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio"
        fall = "best[ext=mp4]/best"
        if q == "best":
            return f"{base}/{fall}"
        try:
            h = int(q.rstrip("p"))
            return (f"bestvideo[height<={h}][ext=mp4]+bestaudio[ext=m4a]"
                    f"/bestvideo[height<={h}]+bestaudio/best[height<={h}]/{fall}")
        except ValueError:
            return f"{base}/{fall}"
 
    def _resolve_stream(self, video_url: str) -> tuple[str, Optional[str], str]:
        """Return (video_url, audio_url_or_None, title).
        Uses a compound (url, fingerprint) cache key so format changes never
        return a stale stream from a different quality/mode."""
        key    = (video_url, self._format_fingerprint())
        cached = self._stream_cache.get(key)
        if cached and (time.time() - cached["ts"]) < STREAM_CACHE_TTL:
            return cached["v_url"], cached["a_url"], cached["title"]
 
        fmt = self._get_format_string()
        with yt_dlp.YoutubeDL({"format": fmt, "quiet": True}) as ydl:
            info = ydl.extract_info(video_url, download=False)
 
        title = info.get("title", "Unknown")
        if "requested_formats" in info:
            v_url = info["requested_formats"][0]["url"]
            a_url = info["requested_formats"][1]["url"]
        else:
            v_url = info["url"]
            a_url = None
 
        self._stream_cache[key] = {
            "v_url": v_url, "a_url": a_url,
            "title": title, "ts": time.time(),
        }
        return v_url, a_url, title
 
    def _get_local_file(self, video_url: str) -> Optional[str]:
        vid = video_id(video_url)
        if not vid:
            return None
        for ext in (".m4a", ".mp4", ".webm"):
            path = os.path.join(DOWNLOAD_DIR, f"{vid}{ext}")
            if os.path.exists(path):
                return path
        return None
 
    # ═══════════════════════════════════════════════════════════════════════
    #  VLC output attachment
    # ═══════════════════════════════════════════════════════════════════════
 
    def _attach_vout(self):
        """Route VLC's video output to the correct window (PiP > inline > none)."""
        if self._pip_open and self._pip_vframe:
            self._pip_win.update_idletasks()
            xid = self._pip_vframe.winfo_id()
        elif self._video_enabled:
            self.root.update_idletasks()
            xid = self.video_frame.winfo_id()
        else:
            xid = 0
 
        if os.name == "nt":
            self.player.set_hwnd(xid)
        else:
            self.player.set_xwindow(xid)
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Tick (1 Hz main loop)
    # ═══════════════════════════════════════════════════════════════════════
 
    def _tick(self):
        state = self.player.get_state()
 
        if state == vlc.State.Playing:
            self.play_btn.config(text="⏸")
            self._sync_pip_play_btn()
            if not self._seeking:
                pos    = self.player.get_position()
                length = self.player.get_length()
                cur    = self.player.get_time()
                if 0.0 <= pos <= 1.0:
                    self.seek_var.set(pos * 100)
                if 0 < length < 86_400_000:
                    self.time_var.set(f"{fmt_ms(cur)} / {fmt_ms(length)}")
                if self._pip_open:
                    self._pip_update_seek(pos, cur, length)
 
        elif state == vlc.State.Paused:
            self.play_btn.config(text="▶")
            self._sync_pip_play_btn()
 
        elif state == vlc.State.Ended:
            if not self._auto_next_sched:
                self._auto_next_sched = True
                if self._repeat and not self._shuffle:
                    self.root.after(200, lambda: self._play_track(self.current_index))
                else:
                    self.root.after(200, self._next_track)
 
        elif state == vlc.State.Error:
            # Auto-skip on VLC-level error (e.g. expired stream URL).
            # _error_url guard prevents re-triggering on the same track.
            if not self._auto_next_sched and self._error_url is None:
                url = ""
                if self.filtered_tracks and self.current_index < len(self.filtered_tracks):
                    url = self.filtered_tracks[self.current_index]["url"]
                self._auto_next_sched = True
                self._error_url       = url
                self.status_var.set("Stream error — skipping in 1 s…")
                self.root.after(1500, self._next_track)
 
        self.root.after(1000, self._tick)
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Transport controls
    # ═══════════════════════════════════════════════════════════════════════
 
    def _toggle_play(self):
        state = self.player.get_state()
        if state == vlc.State.NothingSpecial:
            return  # nothing loaded yet; ignore
        if state == vlc.State.Playing:
            self.player.pause()
            self.play_btn.config(text="▶")
        elif state in (vlc.State.Paused, vlc.State.Stopped):
            self.player.play()
            self.play_btn.config(text="⏸")
        elif state == vlc.State.Ended:
            # Rewind and replay current track
            self._play_track(self.current_index)
        self._sync_pip_play_btn()
 
    def _sync_pip_play_btn(self):
        if self._pip_play_btn and self._pip_open:
            try:
                self._pip_play_btn.config(text="⏸" if self._is_playing else "▶")
            except tk.TclError:
                pass
 
    def _next_track(self):
        if not self.filtered_tracks:
            return
        self._auto_next_sched = False
        if self._shuffle:
            self._shuffle_history.append(self.current_index)
            nxt = random.randrange(len(self.filtered_tracks))
        else:
            nxt = self.current_index + 1
            if nxt >= len(self.filtered_tracks):
                if self._repeat:
                    nxt = 0
                else:
                    self.status_var.set("End of playlist")
                    return
        self._play_track(nxt)
 
    def _prev_track(self):
        if not self.filtered_tracks:
            return
        self._auto_next_sched = False
        if self._shuffle and self._shuffle_history:
            self._play_track(self._shuffle_history.pop())
        else:
            self._play_track(max(0, self.current_index - 1))
 
    def _toggle_shuffle(self):
        self._shuffle = not self._shuffle
        self.shuffle_btn.config(fg=ACCENT if self._shuffle else FG_DIM)
        self._shuffle_history.clear()
 
    def _toggle_repeat(self):
        self._repeat = not self._repeat
        self.repeat_btn.config(fg=ACCENT if self._repeat else FG_DIM)
 
    def _on_seek(self, _event=None):
        if self.player.get_length() > 0:
            self.player.set_position(self.seek_var.get() / 100.0)
        self._seeking = False
 
    def _apply_speed(self):
        try:
            self.player.set_rate(float(self.speed_var.get().rstrip("x")))
        except (ValueError, Exception):
            pass
 
    def _on_quality_change(self, _val=None):
        if not self.filtered_tracks or self.current_index >= len(self.filtered_tracks):
            return
        state = self.player.get_state()
        # Don't reload if nothing is actually playing / paused
        if state in (vlc.State.NothingSpecial, vlc.State.Stopped, vlc.State.Error):
            return
        was_playing = self._is_playing
        cur_time    = self.player.get_time()
        track       = self.filtered_tracks[self.current_index]
        self._reload_at(track["url"], cur_time, was_playing)
 
    # ── Reload at position ───────────────────────────────────────────────
 
    def _reload_at(self, video_url: str, seek_ms: int, resume: bool):
        """Reload the stream (new format or PiP toggle) resuming at seek_ms."""
        self._load_gen += 1
        gen = self._load_gen
        self._auto_next_sched = False
        self._error_url       = None
 
        self.status_var.set("Reloading…")
        self.player.stop()
        self.play_btn.config(text="▶")
        self._sync_pip_play_btn()
 
        def fetch():
            try:
                v_url, a_url, title = self._resolve_stream(video_url)
                self.root.after(0, lambda: _apply(v_url, a_url, title))
            except Exception as exc:
                self.root.after(0, lambda: self._on_load_error(video_url, exc, gen))
 
        def _apply(v_url, a_url, title):
            self._start_vlc(v_url, a_url, title, gen)
 
            def restore(attempts: int = 0):
                if self.player.get_state() == vlc.State.Playing:
                    if seek_ms > 0:
                        self.player.set_time(seek_ms)
                    if not resume:
                        self.player.pause()
                        self.play_btn.config(text="▶")
                        self._sync_pip_play_btn()
                elif attempts < 30:
                    self.root.after(100, restore, attempts + 1)
 
            self.root.after(300, restore)
 
        threading.Thread(target=fetch, daemon=True).start()
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Thumbnail
    # ═══════════════════════════════════════════════════════════════════════
 
    def _load_thumb(self, video_url: str, gen: int):
        photo = fetch_thumb(video_url)
        if photo:
            self.root.after(0, lambda: self._show_thumb(photo, gen))
 
    def _show_thumb(self, photo, gen: int):
        # Drop if a newer track has already started loading.
        if gen != self._load_gen:
            return
        self._thumb_ref = photo
        self.thumb_canvas.delete("all")
        self.thumb_canvas.create_image(0, 0, anchor="nw", image=photo)
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Inline video toggle
    # ═══════════════════════════════════════════════════════════════════════
 
    def _toggle_video(self):
        state = self.player.get_state()
        was_playing  = self._is_playing
        cur_time     = self.player.get_time()
        self._video_enabled = not self._video_enabled
        self.vid_btn.config(fg=ACCENT if self._video_enabled else FG_DIM)
        self._update_video_layout()
 
        # Reload to get/drop the video stream only if a track is actually running.
        if (self.filtered_tracks and
                state not in (vlc.State.NothingSpecial, vlc.State.Stopped,
                              vlc.State.Error)):
            track = self.filtered_tracks[self.current_index]
            self._reload_at(track["url"], cur_time, was_playing)
        else:
            self._attach_vout()
 
    def _update_video_layout(self):
        if self._video_enabled:
            self.video_frame.pack(fill=tk.BOTH, before=self.ctrl_frame)
            self.root.resizable(True, True)
        else:
            self.video_frame.pack_forget()
            if os.name == "nt":
                self.player.set_hwnd(0)
            else:
                self.player.set_xwindow(0)
            if not self._playlist_open:
                self.root.resizable(True, False)
 
        min_h = self._compact_h() + (80 if self._playlist_open else 0)
        self.root.minsize(320, min_h)
        if self.root.winfo_height() < self._compact_h():
            self._resize(self._compact_h())
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Playlist panel toggle
    # ═══════════════════════════════════════════════════════════════════════
 
    def _toggle_playlist(self):
        self._playlist_open = not self._playlist_open
        if self._playlist_open:
            self.playlist_frame.pack(fill=tk.BOTH, expand=True)
            self.root.resizable(True, True)
            self._resize(self._expanded_h())
            self.root.minsize(320, self._compact_h() + 80)
            self.list_btn.config(fg=ACCENT)
        else:
            self.playlist_frame.pack_forget()
            if not self._video_enabled:
                self.root.resizable(True, False)
            self._resize(self._compact_h())
            self.root.minsize(320, self._compact_h())
            self.list_btn.config(fg=FG_DIM)
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Picture-in-Picture
    # ═══════════════════════════════════════════════════════════════════════
 
    def _toggle_pip(self):
        if self._pip_open:
            self._close_pip()
        else:
            self._open_pip()
 
    def _open_pip(self):
        win = tk.Toplevel(self.root)
        win.title("")
        win.geometry("360x240+80+80")
        win.configure(bg="black")
        win.attributes("-topmost", True)
        win.overrideredirect(True)
        self._pip_win = win
 
        # ── Control bar ───────────────────────────────────────────────────
        bar = tk.Frame(win, bg=PIP_BG, height=PIP_BAR_H)
        bar.pack(side=tk.TOP, fill=tk.X)
        bar.pack_propagate(False)
        # Bind drag on the bar (not on child widgets)
        bar.bind("<ButtonPress-1>", self._pip_drag_start)
        bar.bind("<B1-Motion>",     self._pip_drag_move)
 
        def pb(text, cmd, big=False) -> tk.Button:
            return tk.Button(bar, text=text, command=cmd,
                             bg=PIP_BG, fg=PIP_FG,
                             activebackground=PIP_BG, activeforeground=ACCENT,
                             relief=tk.FLAT, bd=0, cursor="hand2",
                             font=("Helvetica", 11 if big else 9),
                             padx=0, pady=0)
 
        pb("✕", self._close_pip).pack(side=tk.LEFT, padx=(5, 2))
        pb("⏮", self._prev_track).pack(side=tk.LEFT, padx=2)
        self._pip_play_btn = pb("⏸" if self._is_playing else "▶",
                                self._toggle_play, big=True)
        self._pip_play_btn.pack(side=tk.LEFT, padx=2)
        pb("⏭", self._next_track).pack(side=tk.LEFT, padx=(2, 6))
 
        self._pip_time_var = tk.StringVar(value="0:00")
        tk.Label(bar, textvariable=self._pip_time_var,
                 bg=PIP_BG, fg=PIP_DIM, font=("Courier", 7),
                 width=9, anchor="w").pack(side=tk.LEFT, padx=(0, 2))
 
        self._pip_seek_var = tk.DoubleVar(value=self.seek_var.get())
        pip_seek = ttk.Scale(bar, from_=0, to=100, orient=tk.HORIZONTAL,
                             variable=self._pip_seek_var,
                             style="A.Horizontal.TScale")
        pip_seek.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        pip_seek.bind("<ButtonPress-1>",   lambda _: setattr(self, "_pip_seeking", True))
        pip_seek.bind("<ButtonRelease-1>", self._pip_on_seek)
 
        tk.Label(bar, text="🔊", bg=PIP_BG, fg=PIP_DIM,
                 font=("Helvetica", 8)).pack(side=tk.LEFT)
        # Share self.vol_var so PiP and main volume sliders are always in sync.
        ttk.Scale(bar, from_=0, to=100, orient=tk.HORIZONTAL,
                  length=52, variable=self.vol_var,
                  style="A.Horizontal.TScale").pack(side=tk.LEFT, padx=(2, 8))
 
        # ── Video area ────────────────────────────────────────────────────
        self._pip_vframe = tk.Frame(win, bg="black")
        self._pip_vframe.pack(fill=tk.BOTH, expand=True)
 
        # ── Resize grip ───────────────────────────────────────────────────
        grip_bar = tk.Frame(win, bg=PIP_BG, height=PIP_GRIP_H)
        grip_bar.pack(side=tk.BOTTOM, fill=tk.X)
        grip_bar.pack_propagate(False)
        grip = tk.Label(grip_bar, text="◢", bg=PIP_BG, fg=PIP_DIM,
                        font=("Helvetica", 9), cursor="bottom_right_corner")
        grip.pack(side=tk.RIGHT, padx=2)
        # Resize uses _rsz_* variables — completely separate from drag's _drag_*
        grip.bind("<ButtonPress-1>", self._pip_rsz_start)
        grip.bind("<B1-Motion>",     self._pip_rsz_move)
 
        win.update()
        self.pip_btn.config(fg=ACCENT)
 
        # Reload stream to get video if a track is running.
        state = self.player.get_state()
        if (self.filtered_tracks and
                state not in (vlc.State.NothingSpecial,
                              vlc.State.Stopped, vlc.State.Error)):
            cur_ms      = max(0, self.player.get_time())
            was_playing = self._is_playing
            track       = self.filtered_tracks[self.current_index]
            self._reload_at(track["url"], cur_ms, was_playing)
        else:
            self._attach_vout()
 
    def _close_pip(self):
        if self._pip_open:
            self._pip_win.destroy()
        self._pip_win      = None
        self._pip_vframe   = None
        self._pip_play_btn = None
        self._pip_time_var = None
        self._pip_seek_var = None
        self.pip_btn.config(fg=FG_DIM)

        # Re-attach video: if inline video is enabled and a track is running,
        # reload to force VLC to draw in the main window and preserve position.
        state = self.player.get_state()
        if (self._video_enabled and
                state not in (vlc.State.NothingSpecial, vlc.State.Stopped,
                              vlc.State.Error)):
            cur_ms = max(0, self.player.get_time())
            was_playing = self._is_playing
            track = self.filtered_tracks[self.current_index]
            self._reload_at(track["url"], cur_ms, was_playing)
        else:
            # No video needed - just detach completely.
            self._attach_vout()
 
    def _pip_on_seek(self, _event=None):
        if self.player.get_length() > 0 and self._pip_seek_var:
            pos = self._pip_seek_var.get() / 100.0
            self.player.set_position(pos)
            self.seek_var.set(self._pip_seek_var.get())
        self._pip_seeking = False
 
    def _pip_update_seek(self, pos: float, cur: int, length: int):
        if not self._pip_seeking and self._pip_seek_var:
            try:
                self._pip_seek_var.set(pos * 100)
            except tk.TclError:
                pass
        if self._pip_time_var:
            try:
                txt = (f"{fmt_ms(cur)}/{fmt_ms(length)}"
                       if length > 0 else fmt_ms(cur))
                self._pip_time_var.set(txt)
            except tk.TclError:
                pass
 
    # ── PiP drag (move) — uses _drag_ox / _drag_oy ───────────────────────
    def _pip_drag_start(self, e):
        self._drag_ox = e.x_root - self._pip_win.winfo_x()
        self._drag_oy = e.y_root - self._pip_win.winfo_y()
 
    def _pip_drag_move(self, e):
        self._pip_win.geometry(f"+{e.x_root - self._drag_ox}+{e.y_root - self._drag_oy}")
 
    # ── PiP resize — uses _rsz_* (never overlaps with drag vars) ─────────
    def _pip_rsz_start(self, e):
        self._rsz_ox = e.x_root
        self._rsz_oy = e.y_root
        self._rsz_w  = self._pip_win.winfo_width()
        self._rsz_h  = self._pip_win.winfo_height()
 
    def _pip_rsz_move(self, e):
        nw = max(220, self._rsz_w + (e.x_root - self._rsz_ox))
        nh = max(140, self._rsz_h + (e.y_root - self._rsz_oy))
        self._pip_win.geometry(f"{nw}x{nh}")
 
    # ═══════════════════════════════════════════════════════════════════════
    #  Downloads
    # ═══════════════════════════════════════════════════════════════════════
 
    def _download_current(self):
        if not self.filtered_tracks or self.current_index >= len(self.filtered_tracks):
            return
        t = self.filtered_tracks[self.current_index]
        threading.Thread(target=self._download_one,
                         args=(t["url"], t["title"]), daemon=True).start()
 
    def _download_all(self):
        if not self.filtered_tracks:
            return
        self.status_var.set("Downloading all…")
        threading.Thread(target=self._download_all_thread, daemon=True).start()
 
    def _download_all_thread(self):
        # Snapshot filtered_tracks in case the user navigates while downloading.
        tracks = list(self.filtered_tracks)
        total  = len(tracks)
        for i, t in enumerate(tracks):
            self.root.after(0, lambda n=i: self.status_var.set(
                f"Downloading {n + 1}/{total}…"))
            self._download_one(t["url"], t["title"])
        self.root.after(0, lambda: self.status_var.set(
            f"Download complete ({total} tracks)"))
 
    def _download_one(self, url: str, title: str):
        vid = video_id(url)
        if not vid:
            return
        outtmpl  = os.path.join(DOWNLOAD_DIR, f"{vid}.%(ext)s")
        ydl_opts = {
            "format":      "bestaudio[ext=m4a]/bestaudio/best",
            "outtmpl":     outtmpl,
            "quiet":       True,
            "no_warnings": True,
            "postprocessors": [{
                "key":              "FFmpegExtractAudio",
                "preferredcodec":   "m4a",
                "preferredquality": "128",
            }],
        }
        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            self.root.after(0, lambda: self.status_var.set(
                f"Downloaded: {title[:40]}"))
        except Exception as exc:
            self.root.after(0, lambda: self.status_var.set(
                f"Download error: {str(exc)[:45]}"))
 
 
# ── Entry point ─────────────────────────────────────────────────────────────
 
if __name__ == "__main__":
    root = tk.Tk()
    YTPlayer(root)
    root.mainloop()
