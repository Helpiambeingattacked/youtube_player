import tkinter as tk
from tkinter import ttk
import yt_dlp
import vlc
import threading
import json
import os
import random
import urllib.request
import io
import socket

try:
    from PIL import Image, ImageTk
    PIL_OK = True
except ImportError:
    PIL_OK = False

# ─────────────────────────────────────────────────────────────────────────────
PLAYLIST_URL = ""
CACHE_FILE   = "playlist_cache.json"
DOWNLOAD_DIR  = "downloads"
# ─────────────────────────────────────────────────────────────────────────────

SPEEDS = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0]
QUALITIES = ["best", "1080p", "720p", "480p", "360p", "240p", "144p", "audio only"]

BG      = "#0f0f0f"
SURFACE = "#1a1a1a"
BORDER  = "#252525"
ACCENT  = "#ff3c3c"
FG      = "#e8e8e8"
FG_DIM  = "#555555"
FG_MID  = "#888888"

PIP_OV_BG  = "#0d0d0d"
PIP_OV_FG  = "#dddddd"
PIP_OV_DIM = "#666666"

COMPACT_H  = 155
EXPANDED_H = 520
VIDEO_H    = 240
WIN_W      = 480
PIP_OVERLAY_H = 42
PIP_BOTTOM_H  = 12   # height of resize grip bar


def _video_id(url: str):
    for sep in ("v=", "youtu.be/", "/embed/", "/shorts/"):
        if sep in url:
            vid = url.split(sep)[-1].split("&")[0].split("?")[0]
            if len(vid) == 11:
                return vid
    return None


def _fetch_thumb(video_url: str):
    if not PIL_OK:
        return None
    vid = _video_id(video_url)
    if not vid:
        return None
    try:
        url = f"https://img.youtube.com/vi/{vid}/mqdefault.jpg"
        with urllib.request.urlopen(url, timeout=5) as r:
            data = r.read()
        img = Image.open(io.BytesIO(data)).resize((80, 56), Image.LANCZOS)
        return ImageTk.PhotoImage(img)
    except Exception:
        return None


def _fmt(ms: int) -> str:
    if ms < 0:
        return "0:00"
    s = ms // 1000
    return f"{s // 60}:{s % 60:02d}"


def _check_internet(host="8.8.8.8", port=53, timeout=3):
    try:
        socket.setdefaulttimeout(timeout)
        socket.socket(socket.AF_INET, socket.SOCK_STREAM).connect((host, port))
        return True
    except Exception:
        return False


class YouTubeAudioPlayer:

    def __init__(self, root: tk.Tk):
        self._video_apply_gen = 0
        self.root = root
        self.root.title("YT Player")
        self.root.geometry(f"{WIN_W}x{COMPACT_H}")
        self.root.minsize(320, COMPACT_H)
        self.root.configure(bg=BG)
        self.root.resizable(True, False)

        os.makedirs(DOWNLOAD_DIR, exist_ok=True)

        self.tracks:          list = []
        self.filtered_tracks: list = []
        self.current_index   = 0
        self.is_playing      = False
        self.is_seeking      = False
        self.shuffle_on      = False
        self.repeat_on       = False
        self.shuffle_history: list = []
        self.playlist_open   = False
        self.video_enabled   = False
        self.in_search_mode  = False
        self._thumb_ref      = None

        self.prefetch_v_url  = None
        self.prefetch_a_url  = None
        self.prefetch_title  = None
        self.prefetch_index  = None

        # ── PiP state ──────────────────────────────────────────────────────
        self._pip_win            = None
        self._pip_active         = False
        self._pip_drag_x         = 0
        self._pip_drag_y         = 0
        self._pip_start_w        = 0
        self._pip_start_h        = 0
        self._pip_seeking        = False
        self._pip_play_btn       = None
        self._pip_time_var       = None
        self._pip_seek_var       = None
        self._pip_vol_var        = None
        self._pip_video_frame    = None
        self._pip_controls       = None
        self._pip_bottom_bar     = None

        # ── VLC: on Linux force X11-compatible vout so set_xwindow works.
        if os.name == "nt":
            vout = "--vout=any"
        else:
            vout = "--vout=xcb_xv,xcb_x11,x11,any"

        self.instance = vlc.Instance("--quiet", "--no-video-title-show", vout)
        self.player   = self.instance.media_player_new()
        em = self.player.event_manager()
        em.event_attach(vlc.EventType.MediaPlayerVout, self._on_vlc_vout)
        self._build_ui()
        self._apply_ttk_styles()
        self._load_or_fetch_playlist()
        self._tick()

    # ══════════════════════════════════════════════════════════════════════════
    #  UI CONSTRUCTION
    # ══════════════════════════════════════════════════════════════════════════

    def _on_vlc_vout(self, event):
        self.root.after(0, self._setup_video_output)

    def _build_ui(self):
        top = tk.Frame(self.root, bg=SURFACE)
        top.pack(fill=tk.X)

        self.thumb_canvas = tk.Canvas(top, width=80, height=56,
                                      bg=BORDER, highlightthickness=0)
        self.thumb_canvas.pack(side=tk.LEFT)
        self._draw_placeholder_thumb()

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

        self.seek_var = tk.DoubleVar()
        self.seek_bar = ttk.Scale(self.root, from_=0, to=100,
                                  orient=tk.HORIZONTAL,
                                  variable=self.seek_var,
                                  style="A.Horizontal.TScale")
        self.seek_bar.pack(fill=tk.X)
        self.seek_bar.bind("<ButtonPress-1>",
                           lambda e: setattr(self, "is_seeking", True))
        self.seek_bar.bind("<ButtonRelease-1>", self._on_seek)

        self.video_frame = tk.Frame(self.root, bg="black")
        self.video_frame.pack_propagate(False)

        self.ctrl_frame = tk.Frame(self.root, bg=BG, pady=4)
        self.ctrl_frame.pack(fill=tk.X, padx=6)

        left = tk.Frame(self.ctrl_frame, bg=BG)
        left.pack(side=tk.LEFT)

        self.shuffle_btn = self._btn(left, "⇄", self._toggle_shuffle, dim=True)
        self.shuffle_btn.pack(side=tk.LEFT)
        self._btn(left, "⏮", self._prev_track).pack(side=tk.LEFT, padx=2)
        self.play_btn = self._btn(left, "▶", self._toggle_play,
                                  big=True, state=tk.DISABLED)
        self.play_btn.pack(side=tk.LEFT, padx=4)
        self._btn(left, "⏭", self._next_track).pack(side=tk.LEFT, padx=2)
        self.repeat_btn = self._btn(left, "↻", self._toggle_repeat, dim=True)
        self.repeat_btn.pack(side=tk.LEFT)

        right = tk.Frame(self.ctrl_frame, bg=BG)
        right.pack(side=tk.RIGHT)

        self.download_btn = self._btn(right, "⬇", self._download_current, dim=True)
        self.download_btn.pack(side=tk.LEFT, padx=(0, 4))

        self.pip_btn = self._btn(right, "⧉", self._toggle_pip, dim=True)
        self.pip_btn.pack(side=tk.LEFT, padx=(0, 4))

        self.video_btn = self._btn(right, "🎬", self._toggle_video, dim=True)
        self.video_btn.pack(side=tk.LEFT, padx=(0, 6))

        tk.Label(right, text="HD", bg=BG, fg=FG_DIM,
                 font=("Courier", 7)).pack(side=tk.LEFT, padx=(0, 2))
        self.quality_var = tk.StringVar(value="best")
        qm = tk.OptionMenu(right, self.quality_var, *QUALITIES,
                           command=self._on_quality_change)
        qm.config(bg=SURFACE, fg=FG_MID, activebackground=ACCENT,
                  activeforeground=FG, relief=tk.FLAT,
                  highlightthickness=0, font=("Courier", 8),
                  bd=0, indicatoron=False, width=6)
        qm["menu"].config(bg=SURFACE, fg=FG_MID,
                          activebackground=ACCENT, activeforeground=FG,
                          font=("Courier", 8), relief=tk.FLAT)
        qm.pack(side=tk.LEFT, padx=(0, 8))

        tk.Label(right, text="SPD", bg=BG, fg=FG_DIM,
                 font=("Courier", 7)).pack(side=tk.LEFT, padx=(0, 2))
        self.speed_var = tk.StringVar(value="1.0x")
        om = tk.OptionMenu(right, self.speed_var,
                           *[f"{s}x" for s in SPEEDS],
                           command=self._on_speed)
        om.config(bg=SURFACE, fg=FG_MID, activebackground=ACCENT,
                  activeforeground=FG, relief=tk.FLAT,
                  highlightthickness=0, font=("Courier", 8),
                  bd=0, indicatoron=False, width=3)
        om["menu"].config(bg=SURFACE, fg=FG_MID,
                          activebackground=ACCENT, activeforeground=FG,
                          font=("Courier", 8), relief=tk.FLAT)
        om.pack(side=tk.LEFT, padx=(0, 8))

        tk.Label(right, text="🔊", bg=BG, fg=FG_DIM,
                 font=("Helvetica", 9)).pack(side=tk.LEFT)
        self.vol_var = tk.IntVar(value=80)
        ttk.Scale(right, from_=0, to=100, orient=tk.HORIZONTAL,
                  length=72, variable=self.vol_var,
                  style="A.Horizontal.TScale",
                  command=lambda _: self.player.audio_set_volume(
                      self.vol_var.get())
                  ).pack(side=tk.LEFT, padx=(2, 8))
        self.player.audio_set_volume(80)

        self.list_toggle_btn = self._btn(right, "☰",
                                         self._toggle_playlist, dim=True)
        self.list_toggle_btn.pack(side=tk.LEFT)

        self.playlist_frame = tk.Frame(self.root, bg=BG)

        sf = tk.Frame(self.playlist_frame, bg=BG, pady=3, padx=6)
        sf.pack(fill=tk.X)

        tk.Label(sf, text="🔍", bg=BG, fg=FG_DIM,
                 font=("Helvetica", 10)).pack(side=tk.LEFT, padx=(0, 3))

        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", self._on_search_type)
        self.search_entry = tk.Entry(
            sf, textvariable=self.search_var,
            bg=SURFACE, fg=FG, insertbackground=FG,
            relief=tk.FLAT, font=("Courier", 9),
            highlightthickness=1, highlightbackground=BORDER,
            highlightcolor=ACCENT)
        self.search_entry.pack(fill=tk.X, expand=True, side=tk.LEFT, ipady=3)
        self.search_entry.bind("<Return>", self._on_search_enter)

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
                          activebackground=ACCENT,
                          highlightthickness=0, relief=tk.FLAT, width=8)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.listbox = tk.Listbox(inner, bg=BG, fg=FG_MID,
                                  selectbackground=ACCENT, selectforeground=FG,
                                  font=("Courier", 9), relief=tk.FLAT, bd=0,
                                  activestyle="none", highlightthickness=0,
                                  yscrollcommand=sb.set)
        self.listbox.pack(fill=tk.BOTH, expand=True)
        sb.config(command=self.listbox.yview)
        self.listbox.bind("<Double-Button-1>", self._on_listbox_dbl)

        rf = tk.Frame(self.playlist_frame, bg=BG, pady=2)
        rf.pack(fill=tk.X, padx=6)

        self.back_btn = self._btn(rf, "← playlist",
                                  self._back_to_playlist, dim=True,
                                  fnt=("Courier", 8))

        self.download_all_btn = self._btn(rf, "⬇ All",
                                          self._download_all, dim=True,
                                          fnt=("Courier", 8))
        self.download_all_btn.pack(side=tk.LEFT, padx=(4, 0))

        self._btn(rf, "⟳  Refresh from YouTube",
                  self._refresh_playlist, dim=True,
                  fnt=("Courier", 8)).pack(side=tk.RIGHT)

    # ══════════════════════════════════════════════════════════════════════════
    #  PICTURE-IN-PICTURE (FIXED with visible resize grip)
    # ══════════════════════════════════════════════════════════════════════════

    def _toggle_pip(self):
        if self._pip_win and self._pip_win.winfo_exists():
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
        win.resizable(True, True)
        self._pip_win = win
        self._pip_active = True

        # Control bar at the top
        self._build_pip_control_bar()

        # Video container below the control bar
        self._pip_video_frame = tk.Frame(win, bg="black")
        self._pip_video_frame.pack(fill=tk.BOTH, expand=True)

        # Bottom bar for resize grip (outside video area)
        self._pip_bottom_bar = tk.Frame(win, bg=PIP_OV_BG, height=PIP_BOTTOM_H)
        self._pip_bottom_bar.pack(side=tk.BOTTOM, fill=tk.X)
        self._pip_bottom_bar.pack_propagate(False)

        # Resize grip (bottom-right corner)
        grip = tk.Label(self._pip_bottom_bar, text="◢", bg=PIP_OV_BG, fg=PIP_OV_DIM,
                        font=("Helvetica", 9), cursor="bottom_right_corner")
        grip.pack(side=tk.RIGHT, padx=2, pady=0)
        grip.bind("<ButtonPress-1>", self._pip_resize_start)
        grip.bind("<B1-Motion>", self._pip_resize_move)
        grip.lift()

        win.update()
        self.pip_btn.config(fg=ACCENT)

        # Reload with video stream if needed
        if self.filtered_tracks and self.current_index < len(self.filtered_tracks):
            track = self.filtered_tracks[self.current_index]
            seek_ms = max(0, self.player.get_time())
            was_playing = self.is_playing

            self.player.stop()
            self.is_playing = False
            self.play_btn.config(text="▶")
            self._sync_pip_play_btn()
            self.status_var.set("Loading video for PiP…")

            threading.Thread(
                target=self._reload_for_pip,
                args=(track["url"], seek_ms, was_playing),
                daemon=True,
            ).start()
        else:
            self._do_attach_vlc_to_pip()

    def _reload_for_pip(self, video_url, seek_ms, resume_play):
        try:
            v_url, a_url, title = self._resolve_stream(video_url)
        except Exception as exc:
            self.root.after(0, lambda: self.status_var.set(f"PiP error: {exc}"))
            return

        def apply():
            if not self._pip_active:
                return
            self._start_vlc(v_url, a_url, title)

            def restore(attempts=0):
                state = self.player.get_state()
                if state == vlc.State.Playing:
                    if seek_ms > 0:
                        self.player.set_time(seek_ms)
                    if not resume_play:
                        self.player.pause()
                        self.is_playing = False
                        self.play_btn.config(text="▶")
                        self._sync_pip_play_btn()
                elif state not in (vlc.State.Ended, vlc.State.Error,
                                   vlc.State.NothingSpecial):
                    if attempts < 30:
                        self.root.after(100, restore, attempts + 1)

            self.root.after(300, restore)

        self.root.after(0, apply)

    def _build_pip_control_bar(self):
        bar = tk.Frame(self._pip_win, bg=PIP_OV_BG, height=PIP_OVERLAY_H)
        bar.pack(side=tk.TOP, fill=tk.X)
        bar.pack_propagate(False)
        self._pip_controls = bar

        # Make the bar draggable
        bar.bind("<ButtonPress-1>", self._pip_drag_start)
        bar.bind("<B1-Motion>", self._pip_drag_move)

        def _btn(text, cmd, big=False):
            return tk.Button(
                bar, text=text, command=cmd,
                bg=PIP_OV_BG, fg=PIP_OV_FG,
                activebackground=PIP_OV_BG, activeforeground=ACCENT,
                relief=tk.FLAT, bd=0, cursor="hand2",
                font=("Helvetica", 11 if big else 9),
                padx=0, pady=0,
            )

        _btn("✕", self._close_pip).pack(side=tk.LEFT, padx=(5, 2))
        _btn("⏮", self._prev_track).pack(side=tk.LEFT, padx=2)

        play_txt = "⏸" if self.is_playing else "▶"
        self._pip_play_btn = _btn(play_txt, self._toggle_play, big=True)
        self._pip_play_btn.pack(side=tk.LEFT, padx=2)

        _btn("⏭", self._next_track).pack(side=tk.LEFT, padx=(2, 6))

        self._pip_time_var = tk.StringVar(value="0:00")
        tk.Label(bar, textvariable=self._pip_time_var,
                 bg=PIP_OV_BG, fg=PIP_OV_DIM,
                 font=("Courier", 7), width=9,
                 anchor="w").pack(side=tk.LEFT, padx=(0, 2))

        self._pip_seek_var = tk.DoubleVar(value=self.seek_var.get())
        seek = ttk.Scale(bar, from_=0, to=100, orient=tk.HORIZONTAL,
                         variable=self._pip_seek_var,
                         style="A.Horizontal.TScale")
        seek.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        seek.bind("<ButtonPress-1>", lambda e: setattr(self, "_pip_seeking", True))
        seek.bind("<ButtonRelease-1>", self._pip_on_seek)

        tk.Label(bar, text="🔊", bg=PIP_OV_BG, fg=PIP_OV_DIM,
                 font=("Helvetica", 8)).pack(side=tk.LEFT)
        self._pip_vol_var = tk.IntVar(value=self.vol_var.get())
        ttk.Scale(bar, from_=0, to=100, orient=tk.HORIZONTAL,
                  length=52, variable=self._pip_vol_var,
                  style="A.Horizontal.TScale",
                  command=lambda _: self._pip_sync_volume()
                  ).pack(side=tk.LEFT, padx=(2, 8))

    def _pip_on_seek(self, event=None):
        if self.player.get_length() > 0:
            pos = self._pip_seek_var.get() / 100.0
            self.player.set_position(pos)
            self.seek_var.set(self._pip_seek_var.get())
        self._pip_seeking = False

    def _pip_sync_volume(self):
        v = self._pip_vol_var.get()
        self.vol_var.set(v)
        self.player.audio_set_volume(v)

    def _pip_update_controls(self, pos, cur, length):
        if not (self._pip_win and self._pip_win.winfo_exists()):
            return
        if not self._pip_seeking and pos >= 0 and self._pip_seek_var:
            self._pip_seek_var.set(pos * 100)
        if self._pip_time_var:
            if length > 0:
                self._pip_time_var.set(f"{_fmt(cur)}/{_fmt(length)}")
            else:
                self._pip_time_var.set(_fmt(cur))

    def _do_attach_vlc_to_pip(self):
        if not (self._pip_win and self._pip_win.winfo_exists()):
            return
        self._pip_win.update()
        xid = self._pip_video_frame.winfo_id()
        if os.name == "nt":
            self.player.set_hwnd(xid)
        else:
            self.player.set_xwindow(xid)

    def _close_pip(self):
        self._pip_active = False
        if self._pip_win and self._pip_win.winfo_exists():
            self._pip_win.destroy()
        self._pip_win = None
        self._pip_video_frame = None
        self._pip_controls = None
        self._pip_bottom_bar = None
        self._pip_play_btn = None
        self._pip_time_var = None
        self._pip_seek_var = None
        self._pip_vol_var = None
        self.pip_btn.config(fg=FG_DIM)
        self._setup_video_output()

    def _pip_drag_start(self, event):
        self._pip_drag_x = event.x_root - self._pip_win.winfo_x()
        self._pip_drag_y = event.y_root - self._pip_win.winfo_y()

    def _pip_drag_move(self, event):
        x = event.x_root - self._pip_drag_x
        y = event.y_root - self._pip_drag_y
        self._pip_win.geometry(f"+{x}+{y}")

    def _pip_resize_start(self, event):
        self._pip_drag_x  = event.x_root
        self._pip_drag_y  = event.y_root
        self._pip_start_w = self._pip_win.winfo_width()
        self._pip_start_h = self._pip_win.winfo_height()

    def _pip_resize_move(self, event):
        dw = event.x_root - self._pip_drag_x
        dh = event.y_root - self._pip_drag_y
        nw = max(220, self._pip_start_w + dw)
        nh = max(140, self._pip_start_h + dh)
        self._pip_win.geometry(f"{nw}x{nh}")

    # ══════════════════════════════════════════════════════════════════════════
    #  REST OF METHODS (unchanged except for minor sync)
    # ══════════════════════════════════════════════════════════════════════════

    def _draw_placeholder_thumb(self):
        self.thumb_canvas.delete("all")
        self.thumb_canvas.create_rectangle(0, 0, 80, 56, fill=BORDER, outline="")
        self.thumb_canvas.create_text(40, 28, text="♪", fill=FG_DIM,
                                      font=("Georgia", 18))

    def _btn(self, parent, text, cmd, big=False, dim=False,
             state=tk.NORMAL, fnt=None):
        fg_col = FG_DIM if dim else FG_MID
        fnt    = fnt or ("Helvetica", 14 if big else 10)
        return tk.Button(parent, text=text, command=cmd,
                         bg=BG, fg=fg_col,
                         activebackground=BG, activeforeground=ACCENT,
                         relief=tk.FLAT, bd=0, cursor="hand2",
                         font=fnt, state=state)

    def _apply_ttk_styles(self):
        s = ttk.Style()
        s.theme_use("clam")
        s.configure("A.Horizontal.TScale",
                    background=BG, troughcolor=BORDER,
                    sliderthickness=12, sliderrelief="flat")
        s.map("A.Horizontal.TScale",
              background=[("active", BG)],
              troughcolor=[("active", BORDER)])

    def _compact_h(self):
        return COMPACT_H + (VIDEO_H if self.video_enabled else 0)

    def _expanded_h(self):
        return EXPANDED_H + (VIDEO_H if self.video_enabled else 0)

    def _set_height(self, h):
        self.root.geometry(f"{self.root.winfo_width()}x{h}")

    def _toggle_playlist(self):
        self.playlist_open = not self.playlist_open
        if self.playlist_open:
            self.playlist_frame.pack(fill=tk.BOTH, expand=True)
            self.root.resizable(True, True)
            self._set_height(self._expanded_h())
            self.root.minsize(320, self._compact_h() + 80)
            self.list_toggle_btn.config(fg=ACCENT)
        else:
            self.playlist_frame.pack_forget()
            self.root.resizable(True, self.video_enabled)
            self._set_height(self._compact_h())
            self.root.minsize(320, self._compact_h())
            self.list_toggle_btn.config(fg=FG_DIM)

    def _toggle_video(self):
        was_playing  = self.is_playing
        current_time = self.player.get_time()

        self.video_enabled = not self.video_enabled
        self.video_btn.config(fg=ACCENT if self.video_enabled else FG_DIM)

        if self.video_enabled:
            self.video_frame.pack(fill=tk.BOTH, expand=True,
                                  before=self.ctrl_frame)
            self.root.update_idletasks()
            self.root.resizable(True, True)
        else:
            self.video_frame.pack_forget()
            if os.name == "nt":
                self.player.set_hwnd(0)
            else:
                self.player.set_xwindow(0)
            if not self.playlist_open:
                self.root.resizable(True, False)

        if self.playlist_open:
            self.root.minsize(320, self._compact_h() + 80)
        else:
            self.root.minsize(320, self._compact_h())
            current_h = self.root.winfo_height()
            target_h  = self._compact_h()
            if current_h < target_h:
                self._set_height(target_h)

        if self.filtered_tracks and self.current_index < len(self.filtered_tracks):
            track = self.filtered_tracks[self.current_index]
            self._reload_track_with_position(track["url"], current_time, was_playing)

    def _reload_track_with_position(self, video_url, seek_ms, resume_play):
        self.status_var.set("Switching format…")
        self.is_playing = False
        self.play_btn.config(text="▶")
        self._sync_pip_play_btn()

        def fetch_and_restart():
            try:
                v_url, a_url, title = self._resolve_stream(video_url)
            except Exception as e:
                self.root.after(0, lambda: self.status_var.set(f"Error: {e}"))
                return

            def apply_and_play():
                self._start_vlc(v_url, a_url, title)

                def do_seek_and_state(attempts=0):
                    if self.player.get_state() == vlc.State.Playing:
                        if seek_ms > 0:
                            self.player.set_time(seek_ms)
                        if not resume_play:
                            self.player.pause()
                            self.play_btn.config(text="▶")
                            self.is_playing = False
                            self._sync_pip_play_btn()
                    elif attempts < 20:
                        self.root.after(100, do_seek_and_state, attempts + 1)

                do_seek_and_state()

            self.root.after(0, apply_and_play)

        threading.Thread(target=fetch_and_restart, daemon=True).start()

    def _load_or_fetch_playlist(self):
        if os.path.exists(CACHE_FILE):
            try:
                with open(CACHE_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if data.get("url") == PLAYLIST_URL and data.get("tracks"):
                    self.tracks = data["tracks"]
                    self._populate_list(self.tracks)
                    n = len(self.tracks)
                    self.status_var.set(f"{n} tracks · cached")
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
            entries = info.get("entries", [info])
            self.tracks = [
                {"url":   e.get("url") or e.get("webpage_url", ""),
                 "title": e.get("title", "Unknown")}
                for e in entries if e
            ]
            self._save_cache()
            self.root.after(0, self._on_playlist_ready)
        except Exception as exc:
            self.root.after(0, lambda: self.status_var.set(f"Error: {exc}"))

    def _save_cache(self):
        try:
            with open(CACHE_FILE, "w", encoding="utf-8") as f:
                json.dump({"url": PLAYLIST_URL, "tracks": self.tracks},
                          f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _on_playlist_ready(self):
        n = len(self.tracks)
        self._populate_list(self.tracks)
        self.status_var.set(f"{n} tracks loaded")
        self.play_btn.config(state=tk.NORMAL)
        self._play_track(0)

    def _refresh_playlist(self):
        if os.path.exists(CACHE_FILE):
            os.remove(CACHE_FILE)
        self.tracks = []
        self.listbox.delete(0, tk.END)
        threading.Thread(target=self._fetch_playlist, daemon=True).start()

    def _populate_list(self, track_list):
        self.filtered_tracks = track_list
        self.listbox.delete(0, tk.END)
        for t in track_list:
            self.listbox.insert(tk.END, f"  {t['title']}")
        shown = len(track_list)
        total = len(self.tracks)
        self.count_var.set(f"{shown}/{total}" if shown != total
                           else f"{total} tracks")

    def _highlight_row(self, index):
        self.listbox.selection_clear(0, tk.END)
        if 0 <= index < self.listbox.size():
            self.listbox.selection_set(index)
            self.listbox.see(index)

    def _on_search_type(self, *_):
        q = self.search_var.get().lower()
        if self.in_search_mode:
            return
        filtered = ([t for t in self.tracks if q in t["title"].lower()]
                    if q else self.tracks)
        self._populate_list(filtered)

    def _on_search_enter(self, _event=None):
        q = self.search_var.get().strip()
        if not q:
            return
        self._yt_search(q)

    def _yt_search(self, query):
        self.status_var.set(f'Searching "{query}"…')
        self.hint_var.set("searching YouTube…")
        threading.Thread(target=self._fetch_search,
                         args=(query,), daemon=True).start()

    def _fetch_search(self, query):
        try:
            opts = {"extract_flat": True, "quiet": True, "skip_download": True}
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(f"ytsearch15:{query}", download=False)
            results = []
            for e in info.get("entries", []):
                if not e:
                    continue
                vid_id = e.get("id") or e.get("url", "")
                if len(vid_id) == 11:
                    url = f"https://www.youtube.com/watch?v={vid_id}"
                else:
                    url = e.get("url", "")
                results.append({"title": e.get("title", "Unknown"), "url": url})
            self.root.after(0, lambda: self._show_search_results(results, query))
        except Exception as exc:
            self.root.after(0, lambda: self.status_var.set(f"Search error: {exc}"))
            self.root.after(0, lambda: self.hint_var.set("↵ to search YouTube"))

    def _show_search_results(self, results, query):
        self.in_search_mode    = True
        self.filtered_tracks   = results
        self.back_btn.pack(side=tk.LEFT, padx=(0, 4))
        self.listbox.delete(0, tk.END)
        for t in results:
            self.listbox.insert(tk.END, f"  {t['title']}")
        self.count_var.set(f"{len(results)} results")
        self.hint_var.set(f'results for "{query}"')
        self.status_var.set(f"{len(results)} results · ↵ new search")
        self.play_btn.config(state=tk.NORMAL)

    def _back_to_playlist(self):
        self.in_search_mode = False
        self.back_btn.pack_forget()
        self.search_var.set("")
        self.hint_var.set("↵ to search YouTube")
        self._populate_list(self.tracks)
        self.status_var.set(f"{len(self.tracks)} tracks")

    def _on_listbox_dbl(self, _):
        sel = self.listbox.curselection()
        if sel:
            self.current_index = sel[0]
            self._play_track(self.current_index)

    def _download_current(self):
        if not self.filtered_tracks:
            return
        track = self.filtered_tracks[self.current_index]
        self._download_track(track["url"], track["title"])

    def _download_all(self):
        if not self.filtered_tracks:
            return
        self.status_var.set("Downloading all tracks…")
        threading.Thread(target=self._download_all_thread, daemon=True).start()

    def _download_all_thread(self):
        total = len(self.filtered_tracks)
        for i, track in enumerate(self.filtered_tracks):
            self.root.after(0, lambda idx=i: self.status_var.set(
                f"Downloading {idx+1}/{total}"))
            self._download_track_sync(track["url"], track["title"])
        self.root.after(0, lambda: self.status_var.set(
            f"Download complete ({total} tracks)"))

    def _download_track(self, url, title):
        threading.Thread(target=self._download_track_sync,
                         args=(url, title), daemon=True).start()

    def _download_track_sync(self, url, title):
        vid = _video_id(url)
        if not vid:
            return
        outtmpl  = os.path.join(DOWNLOAD_DIR, f"{vid}.%(ext)s")
        ydl_opts = {
            "format": "bestaudio[ext=m4a]/bestaudio/best",
            "outtmpl": outtmpl,
            "quiet": True,
            "no_warnings": True,
            "postprocessors": [{
                "key": "FFmpegExtractAudio",
                "preferredcodec": "m4a",
                "preferredquality": "128",
            }],
        }
        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.download([url])
            self.root.after(0, lambda: self.status_var.set(
                f"Downloaded: {title[:30]}…"))
        except Exception as e:
            self.root.after(0, lambda: self.status_var.set(
                f"Download error: {e}"))

    def _get_local_file(self, video_url):
        vid = _video_id(video_url)
        if not vid:
            return None
        for ext in [".m4a", ".mp4", ".webm"]:
            path = os.path.join(DOWNLOAD_DIR, f"{vid}{ext}")
            if os.path.exists(path):
                return path
        return None

    def _play_track(self, index):
        if not self.filtered_tracks:
            return
        index = max(0, min(index, len(self.filtered_tracks) - 1))
        self.current_index = index
        track = self.filtered_tracks[index]

        self._highlight_row(index)
        self.title_var.set(track["title"])
        self.status_var.set(f"Loading… {index + 1}/{len(self.filtered_tracks)}")
        self.is_playing = False
        self.play_btn.config(text="▶")
        self._sync_pip_play_btn()

        self._draw_placeholder_thumb()
        self._thumb_ref = None

        threading.Thread(target=self._load_thumb,
                         args=(track["url"],), daemon=True).start()

        local_file = self._get_local_file(track["url"])

        if local_file and not self.video_enabled and not self._pip_active:
            self.root.after(0, lambda: self._start_local_file(
                local_file, track["title"]))
        else:
            if self.prefetch_index == index and self.prefetch_v_url:
                self._start_vlc(self.prefetch_v_url, self.prefetch_a_url,
                                 self.prefetch_title)
                self.prefetch_v_url = self.prefetch_a_url = \
                    self.prefetch_title = self.prefetch_index = None
            else:
                threading.Thread(target=self._fetch_and_play,
                                 args=(track["url"],), daemon=True).start()

        if not self.in_search_mode:
            next_i = index + 1
            if next_i < len(self.filtered_tracks):
                self.prefetch_v_url = self.prefetch_a_url = \
                    self.prefetch_title = self.prefetch_index = None
                threading.Thread(target=self._prefetch,
                                 args=(next_i,), daemon=True).start()

    def _start_local_file(self, filepath, title):
        media = self.instance.media_new(filepath)
        self.player.set_media(media)
        self._setup_video_output()
        self.player.play()
        self.is_playing = True
        self.play_btn.config(text="⏸")
        self._sync_pip_play_btn()
        self.title_var.set(title)
        n = len(self.filtered_tracks)
        self.status_var.set(f"{self.current_index + 1} of {n} (local)")

    def _setup_video_output(self):
        if self._pip_active:
            self._do_attach_vlc_to_pip()
        elif self.video_enabled:
            self.root.update_idletasks()
            hwnd = self.video_frame.winfo_id()
            if os.name == "nt":
                self.player.set_hwnd(hwnd)
            else:
                self.player.set_xwindow(hwnd)
        else:
            if os.name == "nt":
                self.player.set_hwnd(0)
            else:
                self.player.set_xwindow(0)

    def _load_thumb(self, video_url):
        photo = _fetch_thumb(video_url)
        if photo:
            self.root.after(0, lambda: self._show_thumb(photo))

    def _show_thumb(self, photo):
        self._thumb_ref = photo
        self.thumb_canvas.delete("all")
        self.thumb_canvas.create_image(0, 0, anchor="nw", image=photo)

    def _fetch_and_play(self, video_url):
        try:
            v_url, a_url, title = self._resolve_stream(video_url)
            self.root.after(0, lambda: self._start_vlc(v_url, a_url, title))
        except Exception as exc:
            self.root.after(0, lambda: self._on_stream_failure(video_url, exc))

    def _on_stream_failure(self, video_url, exc):
        self.player.stop()
        self.is_playing = False
        self.play_btn.config(text="▶")
        self._sync_pip_play_btn()
        self.status_var.set(f"Failed to load: {str(exc)[:40]}")
        self._highlight_row(self.current_index)

    def _prefetch(self, index):
        track = self.filtered_tracks[index]
        if _check_internet() and not self._get_local_file(track["url"]):
            try:
                v_url, a_url, title = self._resolve_stream(track["url"])
                self.prefetch_v_url   = v_url
                self.prefetch_a_url   = a_url
                self.prefetch_title   = title
                self.prefetch_index   = index
            except Exception:
                pass

    def _get_format_string(self):
        q = self.quality_var.get()
        if not self.video_enabled or q == "audio only":
            return "bestaudio[ext=m4a]/bestaudio/best"
        base_fmt = "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio"
        fallback  = "best[ext=mp4]/best"
        if q == "best":
            return f"{base_fmt}/{fallback}"
        else:
            try:
                height = int(q.replace("p", ""))
                return (f"bestvideo[height<={height}][ext=mp4]+bestaudio[ext=m4a]"
                        f"/bestvideo[height<={height}]+bestaudio"
                        f"/best[height<={height}]/{fallback}")
            except Exception:
                return f"{base_fmt}/{fallback}"

    def _resolve_stream(self, video_url):
        need_video = self.video_enabled or self._pip_active
        if need_video:
            fmt = self._get_format_string()
            if fmt == "bestaudio[ext=m4a]/bestaudio/best":
                fmt = ("bestvideo[ext=mp4]+bestaudio[ext=m4a]"
                       "/bestvideo+bestaudio/best[ext=mp4]/best")
        else:
            fmt = self._get_format_string()

        with yt_dlp.YoutubeDL({"format": fmt, "quiet": True}) as ydl:
            info = ydl.extract_info(video_url, download=False)

        title = info.get("title", "Unknown")
        if "requested_formats" in info:
            v_url = info["requested_formats"][0]["url"]
            a_url = info["requested_formats"][1]["url"]
            return v_url, a_url, title
        else:
            return info["url"], None, title

    def _start_vlc(self, stream_url, audio_url, title):
        media = self.instance.media_new(stream_url)
        if audio_url:
            media.add_option(f":input-slave={audio_url}")
        self.player.set_media(media)
        self._setup_video_output()
        self.player.play()
        try:
            self.player.set_rate(float(self.speed_var.get().rstrip("x")))
        except Exception:
            pass
        self.is_playing = True
        self.play_btn.config(text="⏸")
        self._sync_pip_play_btn()
        self.title_var.set(title)
        n = len(self.filtered_tracks)
        self.status_var.set(f"{self.current_index + 1} of {n}")

    def _on_quality_change(self, val):
        if not self.filtered_tracks or self.current_index >= len(self.filtered_tracks):
            return
        was_playing  = self.is_playing
        current_time = self.player.get_time()
        track = self.filtered_tracks[self.current_index]
        self._reload_track_with_position(track["url"], current_time, was_playing)

    def _toggle_play(self):
        if self.is_playing:
            self.player.pause()
            self.play_btn.config(text="▶")
        else:
            self.player.play()
            self.play_btn.config(text="⏸")
        self.is_playing = not self.is_playing
        self._sync_pip_play_btn()

    def _sync_pip_play_btn(self):
        if (self._pip_play_btn and self._pip_win
                and self._pip_win.winfo_exists()):
            txt = "⏸" if self.is_playing else "▶"
            try:
                self._pip_play_btn.config(text=txt)
            except tk.TclError:
                pass

    def _next_track(self):
        if not self.filtered_tracks:
            return
        if self.shuffle_on:
            self.shuffle_history.append(self.current_index)
            next_i = random.randrange(len(self.filtered_tracks))
        else:
            next_i = self.current_index + 1
            if next_i >= len(self.filtered_tracks):
                if self.repeat_on:
                    next_i = 0
                else:
                    self.status_var.set("End of playlist")
                    return
        self._play_track(next_i)

    def _prev_track(self):
        if not self.filtered_tracks:
            return
        if self.shuffle_on and self.shuffle_history:
            self._play_track(self.shuffle_history.pop())
        else:
            self._play_track(max(0, self.current_index - 1))

    def _toggle_shuffle(self):
        self.shuffle_on = not self.shuffle_on
        self.shuffle_btn.config(fg=ACCENT if self.shuffle_on else FG_DIM)
        self.shuffle_history.clear()

    def _toggle_repeat(self):
        self.repeat_on = not self.repeat_on
        self.repeat_btn.config(fg=ACCENT if self.repeat_on else FG_DIM)

    def _on_seek(self, _):
        if self.player.get_length() > 0:
            self.player.set_position(self.seek_var.get() / 100.0)
        self.is_seeking = False

    def _on_speed(self, val):
        try:
            self.player.set_rate(float(val.rstrip("x")))
        except Exception:
            pass

    def _tick(self):
        if self.is_playing and not self.is_seeking:
            pos    = self.player.get_position()
            length = self.player.get_length()
            cur    = self.player.get_time()

            if pos >= 0:
                self.seek_var.set(pos * 100)
            if length > 0:
                self.time_var.set(f"{_fmt(cur)} / {_fmt(length)}")

            if self._pip_win and self._pip_win.winfo_exists():
                self._pip_update_controls(pos, cur, length)

            if self.player.get_state() == vlc.State.Ended:
                if ("Failed" in self.status_var.get()
                        or "Offline" in self.status_var.get()):
                    return
                if self.repeat_on and not self.shuffle_on:
                    self._play_track(self.current_index)
                else:
                    self._next_track()

        self.root.after(1000, self._tick)


if __name__ == "__main__":
    root = tk.Tk()
    YouTubeAudioPlayer(root)
    root.mainloop()
