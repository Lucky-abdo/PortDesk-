from fastapi import FastAPI, WebSocket, WebSocketDisconnect, Request, UploadFile, File, Form
from fastapi.responses import FileResponse, JSONResponse, StreamingResponse
from fastapi.middleware.cors import CORSMiddleware
from starlette.middleware.base import BaseHTTPMiddleware
from collections import defaultdict

import sys, io, asyncio, json, os, time, ctypes, threading, logging, platform, struct
import queue as _queue
import string as _string
import base64, subprocess, hashlib

try:
    import bcrypt as _bcrypt
    BCRYPT_AVAILABLE = True
except ImportError:
    _bcrypt = None
    BCRYPT_AVAILABLE = False

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', line_buffering=True)

import pyautogui
import socket as _socket

try:
    import numpy as np
    import cv2
    CV2_AVAILABLE = True
    cv2.setNumThreads(2)
except ImportError:
    np = None; cv2 = None; CV2_AVAILABLE = False

try:
    import mss as _mss
    MSS_AVAILABLE = True
except ImportError:
    MSS_AVAILABLE = False

try:
    import dxcam as _dxcam
    DXCAM_AVAILABLE = True
except ImportError:
    _dxcam = None
    DXCAM_AVAILABLE = False

try:
    import uinput
    UINPUT_AVAILABLE = True
except ImportError:
    uinput = None
    UINPUT_AVAILABLE = False

try:
    from aiortc import RTCPeerConnection, RTCSessionDescription, RTCConfiguration, RTCIceServer
    from aiortc.contrib.media import MediaStreamTrack
    import av
    WEBRTC_AVAILABLE = True
except ImportError:
    WEBRTC_AVAILABLE = False

SUBPROCESS_AVAILABLE = True
BASE_DIR      = os.path.dirname(os.path.abspath(__file__))
SECURITY_FILE = os.path.join(BASE_DIR, "portdesk_security.json")

FLAG_WATCH_ONLY   = False
FLAG_NO_EXPLORER  = False
FLAG_NO_MOUSE     = False
FLAG_NO_KEYBOARD  = False
FLAG_NO_WEBRTC    = False
FLAG_GREY         = False
FLAG_SCALE        = 1.0
FLAG_UPLOAD_LIMIT = None
FLAG_BACKEND      = None
FLAG_VERBOSE      = False

def _vprint(*a, **kw):
    if FLAG_VERBOSE: print(*a, **kw)

pyautogui.FAILSAFE = False
pyautogui.PAUSE    = 0

_pyautogui_lock = threading.Lock()
_sec_lock       = threading.Lock()

_loop: asyncio.AbstractEventLoop = None

# ── Group 3: Token Bucket ─────────────────────────────────────────────────────
class _TokenBucket:
    def __init__(self, rate, capacity):
        self.rate     = rate
        self.capacity = capacity
        self._tokens  = {}
        self._last    = {}
        self._lock    = threading.Lock()

    def consume(self, key, tokens=1):
        now = time.time()
        with self._lock:
            if key not in self._tokens:
                self._tokens[key] = self.capacity
                self._last[key]   = now
            elapsed = now - self._last[key]
            self._tokens[key] = min(self.capacity, self._tokens[key] + elapsed * self.rate)
            self._last[key]   = now
            if self._tokens[key] >= tokens:
                self._tokens[key] -= tokens
                return True
        return False

_ws_buckets = {
    'move':         _TokenBucket(rate=150, capacity=200),
    'scroll':       _TokenBucket(rate=60,  capacity=80),
    'selector_move':_TokenBucket(rate=150, capacity=200),
    'selector_start':_TokenBucket(rate=10, capacity=15),
    'selector_end': _TokenBucket(rate=10,  capacity=15),
    'click':        _TokenBucket(rate=20,  capacity=30),
    'key':          _TokenBucket(rate=30,  capacity=40),
    'key_down':     _TokenBucket(rate=80,  capacity=100),
    'key_up':       _TokenBucket(rate=80,  capacity=100),
    'type':         _TokenBucket(rate=20,  capacity=30),
    'shortcut':     _TokenBucket(rate=15,  capacity=20),
    'stream_config':_TokenBucket(rate=2,   capacity=5),
    'set_monitor':  _TokenBucket(rate=2,   capacity=5),
    'screen_start': _TokenBucket(rate=0.5, capacity=2),
    'screen_stop':  _TokenBucket(rate=2,   capacity=4),
    'mic_start':    _TokenBucket(rate=0.5, capacity=2),
    'mic_stop':     _TokenBucket(rate=2,   capacity=4),
    'mic_chunk':    _TokenBucket(rate=100, capacity=150),
    'audio_start':  _TokenBucket(rate=0.5, capacity=2),
    'audio_stop':   _TokenBucket(rate=2,   capacity=4),
    'default':      _TokenBucket(rate=30,  capacity=50),
}

STUN_SERVERS = [
    RTCIceServer(urls=['stun:stun.l.google.com:19302', 'stun:stun1.l.google.com:19302'])
] if WEBRTC_AVAILABLE else []

_webrtc_pcs: set = set()

_webrtc_dc_clients: list = []
_webrtc_dc_lock           = threading.Lock()


class _DataChannelClient:
    _is_dc_client = True

    def __init__(self, channel, host: str):
        self.channel = channel
        self.client  = type('_C', (), {'host': host})()

    async def send_json(self, data: dict):
        try:
            if self.channel.readyState == 'open':
                self.channel.send(json.dumps(data))
        except Exception:
            pass

    async def send_bytes(self, data: bytes):
        pass


class ConnectionManager:
    def __init__(self):
        self.active = []

    async def connect(self, ws: WebSocket):
        await ws.accept()
        self.active.append(ws)

    def disconnect(self, ws):
        if ws in self.active:
            self.active.remove(ws)

    async def broadcast(self, data: dict):
        dead = []
        for ws in self.active:
            try:
                await ws.send_json(data)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self.disconnect(ws)

    async def broadcast_bytes(self, data: bytes):
        dead = []
        for ws in self.active:
            if getattr(ws, '_is_dc_client', False):
                continue
            try:
                await ws.send_bytes(data)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self.disconnect(ws)

    def broadcast_sync(self, data: dict):
        if _loop and not _loop.is_closed() and _loop.is_running():
            asyncio.run_coroutine_threadsafe(self.broadcast(data), _loop)

    async def broadcast_ws_only(self, data: dict):
        dead = []
        for ws in self.active:
            if getattr(ws, '_is_dc_client', False):
                continue
            try:
                await ws.send_json(data)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self.disconnect(ws)

    def broadcast_ws_only_sync(self, data: dict):
        if _loop and not _loop.is_closed() and _loop.is_running():
            asyncio.run_coroutine_threadsafe(self.broadcast_ws_only(data), _loop)

    def broadcast_bytes_sync(self, data: bytes):
        if _loop and not _loop.is_closed() and _loop.is_running():
            asyncio.run_coroutine_threadsafe(self.broadcast_bytes(data), _loop)

manager = ConnectionManager()

_SEC_BACKUP_COUNT = 3

def _security_backup_path(n):
    return f"{SECURITY_FILE}.bak{n}"

def _load_security_from(path):
    with open(path) as f:
        d = json.load(f)
    if "blacklist" not in d: d["blacklist"] = []
    if "lockout"   not in d: d["lockout"]   = {}
    if "pins"      not in d: d["pins"]       = {}
    d.pop("pin_hash", None)
    return d

def _load_security():
    for src in [SECURITY_FILE] + [_security_backup_path(n) for n in range(1, _SEC_BACKUP_COUNT + 1)]:
        try:
            d = _load_security_from(src)
            if src != SECURITY_FILE:
                print(f"  ⚠ Security file recovered from {os.path.basename(src)}", flush=True)
            return d
        except Exception:
            continue
    return {"whitelist": [], "blacklist": [], "pins": {}, "lockout": {}}

def _save_security():
    for n in range(_SEC_BACKUP_COUNT, 1, -1):
        src = _security_backup_path(n - 1)
        dst = _security_backup_path(n)
        try:
            if os.path.exists(src): os.replace(src, dst)
        except Exception: pass
    try:
        if os.path.exists(SECURITY_FILE):
            os.replace(SECURITY_FILE, _security_backup_path(1))
    except Exception: pass
    tmp = SECURITY_FILE + '.tmp'
    with open(tmp, "w") as f: json.dump(security, f, indent=2)
    os.replace(tmp, SECURITY_FILE)

def _restore_security_backup(n=1):
    path = _security_backup_path(n)
    if not os.path.exists(path):
        return False, f"backup .bak{n} not found"
    try:
        d = _load_security_from(path)
        with _sec_lock:
            security.clear()
            security.update(d)
            _save_security()
        _log_event('security_restore', detail=f"restored from .bak{n}", severity='WARNING')
        return True, path
    except Exception as e:
        return False, str(e)

security = _load_security()
if "blacklist" not in security: security["blacklist"] = []
if "pins"      not in security: security["pins"]      = {}
if "lockout"   not in security: security["lockout"]   = {}

_req_counts    = defaultdict(list)
_reject_counts = defaultdict(int)

# ── Restore persisted lockout state ──────────────────────────────────────────
_pin_fails         = defaultdict(int)
_pin_lockout       = {}
_pin_lockout_count = defaultdict(int)
PIN_MAX_TRIES      = 5
PIN_LOCKOUT_STEPS  = [60, 180, 300]

_now = time.time()
for _ip, _ld in security.get("lockout", {}).items():
    if isinstance(_ld, dict) and _ld.get("until", 0) > _now:
        _pin_lockout[_ip]       = _ld["until"]
        _pin_lockout_count[_ip] = _ld.get("count", 1)

def _is_rate_limited(ip):
    now, window, limit = time.time(), 10, 50
    with _sec_lock:
        _req_counts[ip] = [t for t in _req_counts[ip] if now - t < window]
        if len(_req_counts[ip]) >= limit: return True
        _req_counts[ip].append(now)
    return False

def _is_allowed(ip):
    if ip in ('127.0.0.1', '::1', 'localhost'): return True
    if ip in security.get("blacklist", []): return False
    return ip in security.get("whitelist", [])

_pending_ips = []
_pending_ips_lock = threading.Lock()

_lockdown         = False
_lockdown_lock    = threading.Lock()

_active_client_ws   = None
_active_client_ip   = None
_active_client_lock = threading.Lock()

_unknown_attempts      = []
_unknown_attempts_lock = threading.Lock()
ATTACK_THRESHOLD       = 5
ATTACK_WINDOW          = 30

def _record_unknown_attempt(ip):
    now = time.time()
    with _unknown_attempts_lock:
        _unknown_attempts.append((now, ip))
        recent = [(t, i) for t, i in _unknown_attempts if now - t <= ATTACK_WINDOW]
        _unknown_attempts[:] = recent
        unique_ips = {i for _, i in recent}
        if len(unique_ips) >= ATTACK_THRESHOLD:
            return True
    return False

def _trigger_lockdown(reason=''):
    global _lockdown, screen_streaming, audio_streaming, _mic_active
    with _lockdown_lock:
        if _lockdown: return
        _lockdown = True
    screen_streaming = False
    audio_streaming  = False
    _mic_active      = False
    _log_event('lockdown', detail=reason, severity='CRITICAL')
    print(f"\n{'█'*52}", flush=True)
    print(f"  🚨 LOCKDOWN ACTIVATED — {reason}", flush=True)
    print(f"  All clients kicked. New connections blocked.", flush=True)
    print(f"  Type  lockdown off  to resume.", flush=True)
    print(f"{'█'*52}\n", flush=True)
    manager.broadcast_sync({'type': 'lockdown', 'reason': reason})
    if _loop and not _loop.is_closed() and _loop.is_running():
        asyncio.run_coroutine_threadsafe(_kick_all_clients(), _loop)

async def _kick_all_clients():
    for ws in list(manager.active):
        try: await ws.close(1008)
        except: pass
    manager.active.clear()

def _approve_ip(ip, action='allow'):
    with _pending_ips_lock:
        if ip in _pending_ips:
            _pending_ips.remove(ip)
    if action == 'allow':
        with _sec_lock:
            if ip not in security["whitelist"]:
                security["whitelist"].append(ip)
            _reject_counts[ip] = 0
            security.get("pins", {}).pop(ip, None)
            security.get("lockout", {}).pop(ip, None)
            _save_security()
        _pin_lockout.pop(ip, None)
        _pin_fails[ip] = 0
        _pin_lockout_count[ip] = 0
        print(f"  ✅ Approved {ip}", flush=True)
        manager.broadcast_sync({'type': 'ip_approved', 'ip': ip})
    else:
        _reject_counts[ip] += 1
        if _reject_counts[ip] >= 3:
            with _sec_lock:
                if ip not in security["blacklist"]:
                    security["blacklist"].append(ip)
                    _save_security()
            print(f"  ⛔ {ip} blacklisted after 3 rejections", flush=True)
        else:
            print(f"  ✗ Rejected {ip} — {3 - _reject_counts[ip]} attempt(s) remaining", flush=True)

def _stdin_reader():
    print("  ⌨  Terminal ready — type  help  to see all commands", flush=True)
    while True:
        try:
            line = sys.stdin.readline()
            if not line:
                break
            line = line.strip()
        except (EOFError, OSError):
            break
        cmd = line.lower()
        if cmd == 'y':
            with _pending_ips_lock:
                if not _pending_ips:
                    print("  ❓ No pending requests", flush=True); continue
                ip = _pending_ips[-1]
            _approve_ip(ip, 'allow')
        elif cmd == 'n':
            with _pending_ips_lock:
                if not _pending_ips:
                    print("  ❓ No pending requests", flush=True); continue
                ip = _pending_ips[-1]
            _approve_ip(ip, 'deny')
        elif cmd.startswith('unblock '):
            ip = line[8:].strip()
            if not ip:
                print("  ❓ Usage: unblock <ip>", flush=True); continue
            with _sec_lock:
                changed = False
                if ip in security.get('blacklist', []):
                    security['blacklist'].remove(ip)
                    changed = True
                if ip in _reject_counts:
                    _reject_counts[ip] = 0
                if changed:
                    _save_security()
                    print(f"  ✅ {ip} removed from blacklist", flush=True)
                else:
                    print(f"  ❓ {ip} not in blacklist", flush=True)
        elif cmd == 'kick all':
            _log_event('kick_all', ip='system')
            if _loop and not _loop.is_closed() and _loop.is_running():
                asyncio.run_coroutine_threadsafe(_kick_all_clients(), _loop)
            print("  ✅ All clients kicked", flush=True)
        elif cmd == 'lockdown off':
            global _lockdown
            with _lockdown_lock:
                _lockdown = False
            _log_event('lockdown_off', ip='system')
            print("  ✅ Lockdown lifted", flush=True)
        elif cmd.startswith('restore security'):
            parts = cmd.split()
            n = int(parts[2]) if len(parts) >= 3 and parts[2].isdigit() else 1
            ok, info = _restore_security_backup(n)
            if ok:
                print(f"  ✅ Security restored from .bak{n}: {info}", flush=True)
            else:
                print(f"  ❌ Restore failed: {info}", flush=True)
        elif cmd == 'help':
            print(
                "\n  ┌──────────────────────────────────────────────────────────┐\n"
                "  │  PortDesk Terminal Commands                              │\n"
                "  ├──────────────────────────────────────────────────────────┤\n"
                "  │  y                       Approve last pending IP         │\n"
                "  │  n                       Reject last pending IP          │\n"
                "  │  unblock <ip>            Remove IP from blacklist        │\n"
                "  │  kick all                Disconnect all active clients   │\n"
                "  │  lockdown off            Lift active lockdown            │\n"
                "  │  restore security [1-3]  Restore security backup file    │\n"
                "  │  help                    Show this message               │\n"
                "  └──────────────────────────────────────────────────────────┘\n",
                flush=True
            )
        else:
            print("  ❓ Unknown command — type  help  to see all commands", flush=True)

_security_file_mtime = 0

def _security_file_watcher():
    global _security_file_mtime, security
    _cleanup_counter = 0
    while True:
        time.sleep(2)
        _cleanup_counter += 1
        try:
            mtime = os.path.getmtime(SECURITY_FILE)
            if mtime != _security_file_mtime:
                _security_file_mtime = mtime
                new_sec = _load_security()
                with _sec_lock:
                    security.clear()
                    security.update(new_sec)
                now = time.time()
                for ip, ld in new_sec.get("lockout", {}).items():
                    if isinstance(ld, dict) and ld.get("until", 0) > now:
                        _pin_lockout[ip]       = ld["until"]
                        _pin_lockout_count[ip] = ld.get("count", 1)
                    else:
                        _pin_lockout.pop(ip, None)
                _vprint("🔄 Security file reloaded", flush=True)
        except Exception:
            pass
        if _cleanup_counter >= 30:
            _cleanup_counter = 0
            cutoff = time.time() - 10
            with _sec_lock:
                stale = [ip for ip, ts in list(_req_counts.items()) if not ts or ts[-1] < cutoff]
                for ip in stale:
                    del _req_counts[ip]

def _prompt_add_ip(ip):
    if _record_unknown_attempt(ip):
        _trigger_lockdown(f'Multi-IP attack detected ({ATTACK_THRESHOLD}+ unknown IPs in {ATTACK_WINDOW}s)')
        return
    with _pending_ips_lock:
        if ip in _pending_ips: return
        _pending_ips.append(ip)
    count = _reject_counts[ip] + 1
    print(f"\n{'═'*50}\n  🔔 New connection request from: {ip}  (attempt {count}/3)", flush=True)
    print(f"  Type  y  to approve,  n  to reject", flush=True)
    print('═'*50, flush=True)
    manager.broadcast_sync({'type': 'ip_request', 'ip': ip, 'attempt': count})

class SecurityMiddleware(BaseHTTPMiddleware):
    OPEN_PATHS = {'/security/whitelist/request', '/security/whitelist/remove_self'}
    SAFE_METHODS = {'GET', 'HEAD', 'OPTIONS'}
    CSRF_PATHS = {
        '/explorer/delete', '/explorer/upload', '/explorer/rename',
        '/explorer/mkdir',  '/explorer/mkfile', '/explorer/copy',
        '/explorer/move',   '/explorer/shortcut',
        '/tasks/kill',      '/macros/run',       '/macros/delete',
        '/log/clear',       '/auth/set_pin',     '/auth/clear_pin',
        '/scheduled/delete','/scheduled/save',
    }

    async def dispatch(self, request: Request, call_next):
        ip = request.client.host

        with _lockdown_lock:
            if _lockdown and ip not in ('127.0.0.1', '::1', 'localhost'):
                return JSONResponse({"error": "server in lockdown"}, status_code=503)

        if _is_rate_limited(ip):
            return JSONResponse({"error": "rate limited"}, status_code=429)

        if ip in ('127.0.0.1', '::1', 'localhost'):
            response = await call_next(request)
            response.headers['server'] = 'portdesk'
            return response

        if ip in security.get("blacklist", []):
            return JSONResponse({"error": "blacklisted"}, status_code=403)

        if request.url.path in self.OPEN_PATHS:
            response = await call_next(request)
            response.headers['server'] = 'portdesk'
            return response

        if not _is_allowed(ip):
            _prompt_add_ip(ip)
            return JSONResponse({"error": "not whitelisted"}, status_code=403)

        with _active_client_lock:
            _aip = _active_client_ip
        if _aip is not None and _aip != ip:
            return JSONResponse({"error": "session occupied"}, status_code=423)

        # ── Group 6: CSRF Origin check ────────────────────────────────────
        if request.method not in self.SAFE_METHODS and request.url.path in self.CSRF_PATHS:
            origin = request.headers.get('origin', '')
            host   = request.headers.get('host', '')
            allowed_origins = (
                f'http://{host}', f'https://{host}',
                'http://localhost:5000', 'https://localhost:5000',
                'null', ''
            )
            if origin and origin not in allowed_origins:
                return JSONResponse({"error": "invalid origin"}, status_code=403)

        response = await call_next(request)
        response.headers['server'] = 'portdesk'
        return response

from contextlib import asynccontextmanager

@asynccontextmanager
async def _lifespan(app):
    global _loop, _clip_running, _sched_running
    _loop = asyncio.get_event_loop()
    _clip_running  = True
    _sched_running = True
    threading.Thread(target=_clipboard_watcher, daemon=True).start()
    threading.Thread(target=_scheduler_worker, daemon=True).start()
    threading.Thread(target=_stats_pusher, daemon=True).start()
    threading.Thread(target=_stdin_reader, daemon=True).start()
    threading.Thread(target=_security_file_watcher, daemon=True).start()
    for warn in _check_linux_compatibility():
        print(f"⚠️ Linux: {warn}")
    if platform.system() != 'Windows':
        if _init_virtual_keyboard():
            print("✅ Virtual keyboard initialized.")
        else:
            print("⚠️ Virtual keyboard not available; using fallbacks.")
    threading.Thread(target=_detect_ffmpeg_encoder, daemon=True).start()
    _flag_detail = (
        f"watch_only={FLAG_WATCH_ONLY} no_explorer={FLAG_NO_EXPLORER} "
        f"no_mouse={FLAG_NO_MOUSE} no_keyboard={FLAG_NO_KEYBOARD} "
        f"no_webrtc={FLAG_NO_WEBRTC} grey={FLAG_GREY} "
        f"scale={FLAG_SCALE} backend={FLAG_BACKEND or 'auto'} "
        f"upload_limit={FLAG_UPLOAD_LIMIT or 'unlimited'}"
    )
    _log_event('startup', detail=_flag_detail)
    yield
    global _dxcam_camera
    with _dxcam_camera_lock:
        if _dxcam_camera is not None:
            try: _dxcam_camera.stop()
            except: pass
            _dxcam_camera = None

app = FastAPI(lifespan=_lifespan)
app.add_middleware(SecurityMiddleware)
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_methods=["*"], allow_headers=["*"])

class _CoreTempData(ctypes.Structure):
    _fields_ = [
        ("uiLoad",         ctypes.c_uint  * 256),
        ("uiTjMax",        ctypes.c_uint  * 128),
        ("uiCoreCnt",      ctypes.c_uint),
        ("uiCPUCnt",       ctypes.c_uint),
        ("fTemp",          ctypes.c_float * 256),
        ("fVID",           ctypes.c_float),
        ("fCPUSpeed",      ctypes.c_float),
        ("fFSBSpeed",      ctypes.c_float),
        ("fMultiplier",    ctypes.c_float),
        ("sCPUName",       ctypes.c_char  * 100),
        ("ucFahrenheit",   ctypes.c_ubyte),
        ("ucDeltaToTjMax", ctypes.c_ubyte),
    ]

def _get_coretemp():
    system = platform.system()
    if system == 'Windows':
        if not hasattr(ctypes, 'windll'): return None, None
        try:
            k32  = ctypes.windll.kernel32
            hmap = k32.OpenFileMappingW(0x0004, False, "CoreTempMappingObject")
            if not hmap: return None, None
            k32.MapViewOfFile.restype = ctypes.POINTER(_CoreTempData)
            ptr = k32.MapViewOfFile(hmap, 0x0004, 0, 0, ctypes.sizeof(_CoreTempData))
            if not ptr: k32.CloseHandle(hmap); return None, None
            try:
                d     = ptr.contents
                temps = [d.fTemp[i] for i in range(d.uiCoreCnt)]
                if d.ucDeltaToTjMax: temps = [d.uiTjMax[i] - temps[i] for i in range(d.uiCoreCnt)]
                if d.ucFahrenheit:   temps = [(t - 32) * 5/9 for t in temps]
                return (round(max(temps), 1) if temps else None), None
            finally:
                k32.UnmapViewOfFile(ptr); k32.CloseHandle(hmap)
        except: return None, None
    elif system == 'Linux':
        try:
            import psutil
            temps = psutil.sensors_temperatures()
            for key in ('coretemp', 'cpu_thermal', 'k10temp', 'zenpower'):
                if key in temps and temps[key]:
                    return round(max(t.current for t in temps[key]), 1), None
        except: pass
        try:
            import glob
            paths = glob.glob('/sys/class/thermal/thermal_zone*/temp')
            vals = []
            for p in paths:
                with open(p) as f: vals.append(int(f.read().strip()) / 1000.0)
            if vals: return round(max(vals), 1), None
        except: pass
        return None, None
    elif system == 'Darwin':
        try:
            out = subprocess.check_output(
                ['sudo', 'powermetrics', '--samplers', 'smc', '-n', '1', '-i', '1'],
                timeout=2, stderr=subprocess.DEVNULL).decode()
            import re
            m = re.search(r'CPU die temperature: ([\d.]+)', out)
            if m: return round(float(m.group(1)), 1), None
        except: pass
        return None, None
    return None, None

def get_system_stats():
    stats = {"cpu_temp": "N/A", "gpu_temp": "N/A", "cpu_usage": 0, "ram_usage": 0}
    try:
        import psutil
        stats["cpu_usage"] = round(psutil.cpu_percent(interval=0.1), 1)
        stats["ram_usage"] = round(psutil.virtual_memory().percent, 1)
    except: pass
    cpu_t, gpu_t = _get_coretemp()
    if cpu_t: stats["cpu_temp"] = cpu_t
    if gpu_t: stats["gpu_temp"] = gpu_t
    return stats

KEY_MAP = {
    'win':'winleft','windows':'winleft','super':'winleft',
    'cmd':'command','command':'command',
    'ctrl':'ctrl','control':'ctrl','alt':'alt','shift':'shift',
    'printscreen':'printscreen','prtsc':'printscreen',
    'playpause':'playpause','nexttrack':'nexttrack','prevtrack':'prevtrack',
    'volumemute':'volumemute','volumeup':'volumeup','volumedown':'volumedown',
    'esc':'escape','escape':'escape','del':'delete','ins':'insert',
    'backspace':'backspace','enter':'enter','return':'enter',
    'tab':'tab','space':'space',
    'up':'up','down':'down','left':'left','right':'right',
    **{f'f{i}': f'f{i}' for i in range(1, 13)},
}
def map_key(k): return KEY_MAP.get(k.lower(), k.lower())

def type_text(text):
    if not text: return
    with _pyautogui_lock:
        try:
            import pyperclip
            pyperclip.copy(text)
            time.sleep(0.08)
            if platform.system() == 'Darwin': pyautogui.hotkey('command', 'v')
            else:                              pyautogui.hotkey('ctrl', 'v')
            time.sleep(0.05)
        except Exception:
            try: pyautogui.write(text, interval=0.02)
            except Exception as e: _vprint(f"❌ type_text: {e}", flush=True)

_virtual_kb_device = None

def _init_virtual_keyboard():
    global _virtual_kb_device
    if not UINPUT_AVAILABLE or platform.system() != 'Linux': return False
    try:
        events = [
            uinput.KEY_A, uinput.KEY_B, uinput.KEY_C, uinput.KEY_D, uinput.KEY_E,
            uinput.KEY_F, uinput.KEY_G, uinput.KEY_H, uinput.KEY_I, uinput.KEY_J,
            uinput.KEY_K, uinput.KEY_L, uinput.KEY_M, uinput.KEY_N, uinput.KEY_O,
            uinput.KEY_P, uinput.KEY_Q, uinput.KEY_R, uinput.KEY_S, uinput.KEY_T,
            uinput.KEY_U, uinput.KEY_V, uinput.KEY_W, uinput.KEY_X, uinput.KEY_Y,
            uinput.KEY_Z, uinput.KEY_0, uinput.KEY_1, uinput.KEY_2, uinput.KEY_3,
            uinput.KEY_4, uinput.KEY_5, uinput.KEY_6, uinput.KEY_7, uinput.KEY_8,
            uinput.KEY_9, uinput.KEY_SPACE, uinput.KEY_ENTER, uinput.KEY_BACKSPACE,
            uinput.KEY_TAB, uinput.KEY_ESC, uinput.KEY_LEFTSHIFT, uinput.KEY_LEFTCTRL,
            uinput.KEY_LEFTALT, uinput.KEY_LEFTMETA, uinput.KEY_F1, uinput.KEY_F2,
            uinput.KEY_F3, uinput.KEY_F4, uinput.KEY_F5, uinput.KEY_F6, uinput.KEY_F7,
            uinput.KEY_F8, uinput.KEY_F9, uinput.KEY_F10, uinput.KEY_F11, uinput.KEY_F12,
            uinput.KEY_LEFT, uinput.KEY_RIGHT, uinput.KEY_UP, uinput.KEY_DOWN,
            uinput.KEY_DELETE, uinput.KEY_HOME, uinput.KEY_END, uinput.KEY_PAGEUP,
            uinput.KEY_PAGEDOWN, uinput.KEY_CAPSLOCK, uinput.KEY_NUMLOCK,
        ]
        _virtual_kb_device = uinput.Device(events)
        return True
    except Exception as e:
        _vprint(f"Virtual keyboard init failed: {e}", flush=True)
        return False

def _send_virtual_key(key_code, press=True):
    if _virtual_kb_device:
        try:
            _virtual_kb_device.emit(key_code, 1 if press else 0)
        except Exception as e:
            _vprint(f"Virtual key send failed: {e}", flush=True)

def _send_virtual_text(text):
    for char in text:
        if char.isalpha():
            key = getattr(uinput, f'KEY_{char.upper()}', None)
            if key: _send_virtual_key(key, True); time.sleep(0.01); _send_virtual_key(key, False)
        elif char.isdigit():
            key = getattr(uinput, f'KEY_{char}', None)
            if key: _send_virtual_key(key, True); time.sleep(0.01); _send_virtual_key(key, False)
        elif char == ' ':  _send_virtual_key(uinput.KEY_SPACE, True);     time.sleep(0.01); _send_virtual_key(uinput.KEY_SPACE, False)
        elif char == '\n': _send_virtual_key(uinput.KEY_ENTER, True);     time.sleep(0.01); _send_virtual_key(uinput.KEY_ENTER, False)
        elif char == '\t': _send_virtual_key(uinput.KEY_TAB, True);       time.sleep(0.01); _send_virtual_key(uinput.KEY_TAB, False)
        elif char == '\b': _send_virtual_key(uinput.KEY_BACKSPACE, True); time.sleep(0.01); _send_virtual_key(uinput.KEY_BACKSPACE, False)
        time.sleep(0.005)

def _send_xdotool_key(key):
    if SUBPROCESS_AVAILABLE and platform.system() == 'Linux':
        try: subprocess.run(['xdotool', 'key', key], check=True)
        except Exception as e: print(f"xdotool key failed: {e}", flush=True)

def _send_xdotool_text(text):
    if SUBPROCESS_AVAILABLE and platform.system() == 'Linux':
        try: subprocess.run(['xdotool', 'type', '--clearmodifiers', text], check=True)
        except Exception as e: print(f"xdotool text failed: {e}", flush=True)

screen_streaming   = False
screen_thread      = None
_screen_last_error = ''

_dxcam_camera      = None
_dxcam_camera_lock = threading.Lock()

def _get_dxcam_camera(mon_idx=0):
    global _dxcam_camera
    with _dxcam_camera_lock:
        if _dxcam_camera is None and DXCAM_AVAILABLE and platform.system() == 'Windows':
            try:
                _dxcam_camera = _dxcam.create(output_idx=mon_idx, output_color="BGR")
                _dxcam_camera.start(target_fps=60, video_mode=True)
                _vprint("✅ dxcam camera created", flush=True)
            except Exception as e:
                _vprint(f"❌ dxcam create: {e}", flush=True)
        return _dxcam_camera

stream_config = {
    'height': 720, 'quality': 65, 'fps': 30,
    'monitor': 1, 'cursor_color_bgr': (255, 255, 255)
}
_stream_config_lock = threading.Lock()

_ffmpeg_encoder    = None
_ffmpeg_encoder_ok = False

def _detect_ffmpeg_encoder():
    global _ffmpeg_encoder, _ffmpeg_encoder_ok
    import shutil
    if not shutil.which('ffmpeg'):
        _vprint("⚠ FFmpeg not found in PATH — hardware encoding unavailable", flush=True)
        return None
    if not CV2_AVAILABLE:
        return None

    try:
        res = subprocess.run(['ffmpeg', '-encoders', '-hide_banner'],
                             capture_output=True, text=True, timeout=5)
        enc_list = res.stdout + res.stderr
    except Exception:
        enc_list = ''

    sys_name = platform.system()
    if sys_name == 'Windows':
        candidates = [
            ('h264_nvenc', ['-preset', 'p1', '-tune', 'll', '-bf', '0']),
            ('h264_amf',   ['-quality', 'speed', '-bf', '0']),
            ('h264_qsv',   ['-preset', 'veryfast', '-bf', '0']),
            ('libx264',    ['-preset', 'ultrafast', '-tune', 'zerolatency', '-bf', '0']),
        ]
    elif sys_name == 'Linux':
        candidates = [
            ('h264_nvenc', ['-preset', 'p1', '-tune', 'll', '-bf', '0']),
            ('h264_vaapi', []),
            ('libx264',    ['-preset', 'ultrafast', '-tune', 'zerolatency', '-bf', '0']),
        ]
    elif sys_name == 'Darwin':
        candidates = [
            ('h264_videotoolbox', ['-realtime', '1', '-bf', '0']),
            ('libx264',           ['-preset', 'ultrafast', '-tune', 'zerolatency', '-bf', '0']),
        ]
    else:
        candidates = [('libx264', ['-preset', 'ultrafast', '-tune', 'zerolatency', '-bf', '0'])]

    dummy_frame = np.zeros((64, 64, 3), dtype=np.uint8).tobytes()

    for enc, enc_flags in candidates:
        if enc != 'libx264' and enc not in enc_list:
            _vprint(f"  ↳ {enc}: not listed in ffmpeg encoders, skip", flush=True)
            continue
        try:
            if enc == 'h264_vaapi':
                cmd = [
                    'ffmpeg', '-y', '-loglevel', 'error',
                    '-vaapi_device', '/dev/dri/renderD128',
                    '-f', 'rawvideo', '-pix_fmt', 'bgr24', '-s', '64x64', '-r', '1',
                    '-i', 'pipe:0',
                    '-vf', 'format=nv12,hwupload',
                    '-vcodec', 'h264_vaapi',
                    '-frames:v', '1', '-f', 'null', '-'
                ]
            else:
                cmd = [
                    'ffmpeg', '-y', '-loglevel', 'error',
                    '-f', 'rawvideo', '-pix_fmt', 'bgr24', '-s', '64x64', '-r', '1',
                    '-i', 'pipe:0',
                    '-vcodec', enc,
                ] + enc_flags + ['-frames:v', '1', '-f', 'null', '-']

            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            _, _ = proc.communicate(input=dummy_frame, timeout=5)
            if proc.returncode == 0:
                _ffmpeg_encoder    = enc
                _ffmpeg_encoder_ok = True
                hw = enc != 'libx264'
                _vprint(f"✅ FFmpeg encoder: {enc} ({'hardware' if hw else 'software fallback'})", flush=True)
                return enc
            else:
                _vprint(f"  ↳ {enc}: returned error", flush=True)
        except FileNotFoundError:
            _vprint("⚠ FFmpeg not found", flush=True); return None
        except subprocess.TimeoutExpired:
            try: proc.kill()
            except: pass
            _vprint(f"  ↳ {enc}: timeout", flush=True)
        except Exception as e:
            _vprint(f"  ↳ {enc}: {e}", flush=True); continue

    _vprint("⚠ FFmpeg: no encoder detected", flush=True)
    return None


class _FfmpegH264Streamer:
    MSG_H264 = 0x03

    def __init__(self, encoder, width, height, fps):
        self.encoder  = encoder
        self.width    = width
        self.height   = height
        self.fps      = max(1, fps)
        self.proc     = None
        self._running = False
        self._reader  = None

    def _build_cmd(self):
        enc = self.encoder
        fps = self.fps
        gop = fps * 2

        base = [
            'ffmpeg', '-y', '-loglevel', 'error',
            '-f', 'rawvideo', '-pix_fmt', 'bgr24',
            '-s', f'{self.width}x{self.height}',
            '-r', str(fps),
            '-i', 'pipe:0',
        ]

        if enc == 'h264_nvenc':
            enc_args = ['-vcodec', 'h264_nvenc', '-preset', 'p1',
                        '-tune', 'll', '-zerolatency', '1', '-bf', '0', '-g', str(gop)]
        elif enc == 'h264_amf':
            enc_args = ['-vcodec', 'h264_amf', '-quality', 'speed',
                        '-rc', 'cbr', '-bf', '0', '-g', str(gop)]
        elif enc == 'h264_qsv':
            enc_args = ['-vcodec', 'h264_qsv', '-preset', 'veryfast',
                        '-bf', '0', '-g', str(gop)]
        elif enc == 'h264_videotoolbox':
            enc_args = ['-vcodec', 'h264_videotoolbox', '-realtime', '1',
                        '-bf', '0', '-g', str(gop)]
        elif enc == 'h264_vaapi':
            base = [
                'ffmpeg', '-y', '-loglevel', 'error',
                '-vaapi_device', '/dev/dri/renderD128',
                '-f', 'rawvideo', '-pix_fmt', 'bgr24',
                '-s', f'{self.width}x{self.height}',
                '-r', str(fps), '-i', 'pipe:0',
            ]
            enc_args = ['-vf', 'format=nv12,hwupload',
                        '-vcodec', 'h264_vaapi', '-bf', '0', '-g', str(gop)]
        else:
            enc_args = ['-vcodec', 'libx264', '-preset', 'ultrafast',
                        '-tune', 'zerolatency', '-bf', '0', '-g', str(gop)]

        out = ['-f', 'mp4',
               '-movflags', 'frag_keyframe+empty_moov+default_base_moof',
               'pipe:1']
        return base + enc_args + out

    def start(self):
        self._running = True
        try:
            self.proc = subprocess.Popen(
                self._build_cmd(),
                stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL, bufsize=0
            )
            self._reader = threading.Thread(target=self._read_loop, daemon=True)
            self._reader.start()
            return True
        except Exception as e:
            _vprint(f"❌ H264Streamer start: {e}", flush=True)
            self._running = False
            return False

    def _read_loop(self):
        CHUNK = 16384
        while self._running:
            try:
                data = self.proc.stdout.read(CHUNK)
                if not data:
                    break
                if _loop and not _loop.is_closed():
                    msg = struct.pack('>BI', self.MSG_H264, len(data)) + data
                    asyncio.run_coroutine_threadsafe(
                        manager.broadcast_bytes(msg), _loop
                    )
            except Exception as e:
                if self._running:
                    _vprint(f"❌ H264Streamer read: {e}", flush=True)
                break

    def send_frame(self, frame_bgr):
        if self.proc is None or self.proc.poll() is not None:
            return False
        try:
            self.proc.stdin.write(frame_bgr.tobytes())
            self.proc.stdin.flush()
            return True
        except Exception:
            return False

    def close(self):
        self._running = False
        if self.proc:
            try: self.proc.stdin.close()
            except: pass
            try: self.proc.terminate()
            except: pass
            self.proc = None

_mouse_pos      = (0, 0)
_mouse_pos_lock = threading.Lock()

def _mouse_tracker():
    global _mouse_pos
    while True:
        try:
            p = pyautogui.position()
            with _mouse_pos_lock: _mouse_pos = (p.x, p.y)
        except Exception: pass
        time.sleep(0.016)

threading.Thread(target=_mouse_tracker, daemon=True).start()

def _draw_cursor(arr, mx, my, mon_left, mon_top, src_w, src_h, cursor_color):
    nw, nh = arr.shape[1], arr.shape[0]
    sx = int((mx - mon_left) * nw / src_w)
    sy = int((my - mon_top)  * nh / src_h)
    if 0 <= sx < nw and 0 <= sy < nh:
        pts = np.array([[sx, sy], [sx+12, sy+12], [sx, sy+16]], np.int32)
        cv2.fillPoly(arr, [pts], cursor_color)
        cv2.polylines(arr, [pts], True, (0, 0, 0), 1)

def screen_worker():
    global screen_streaming, _screen_last_error
    _screen_last_error = ''

    if not (MSS_AVAILABLE or DXCAM_AVAILABLE):
        _screen_last_error = 'no capture backend available'; return
    if not CV2_AVAILABLE:
        _screen_last_error = 'cv2 not available'; return

    with _stream_config_lock: cfg0 = stream_config.copy()
    use_h264 = _ffmpeg_encoder_ok and _ffmpeg_encoder is not None

    if use_h264:
        target_h = cfg0['height']
        fps      = max(1, cfg0['fps'])
        with _mss.mss() as _sct0:
            mon0   = _sct0.monitors[max(1, min(cfg0['monitor'], len(_sct0.monitors)-1))]
            src_w0 = mon0['width']; src_h0 = mon0['height']
        target_w = int(src_w0 * target_h / src_h0)
        target_w = target_w if target_w % 2 == 0 else target_w + 1
        target_h = target_h if target_h % 2 == 0 else target_h + 1

        h264 = _FfmpegH264Streamer(_ffmpeg_encoder, target_w, target_h, fps)
        if not h264.start():
            use_h264 = False
            _vprint("⚠ H264 streamer failed to start — falling back to JPEG", flush=True)
        else:
            _vprint(f"✅ screen: H264 via {_ffmpeg_encoder} ({target_w}x{target_h} @ {fps}fps)", flush=True)
            asyncio.run_coroutine_threadsafe(
                manager.broadcast({'type': 'stream_mode', 'mode': 'h264',
                                   'encoder': _ffmpeg_encoder,
                                   'width': target_w, 'height': target_h}), _loop
            )

    if not use_h264:
        tj = None; use_turbo = False
        try:
            from turbojpeg import TurboJPEG, TJPF_BGR, TJSAMP_444 as _TJSAMP_444
            tj, use_turbo = TurboJPEG(), True
            _TJPF_BGR = TJPF_BGR
            _vprint("✅ screen: TurboJPEG active", flush=True)
        except Exception as _te:
            _vprint(f"⚠ screen: TurboJPEG not available ({_te}), falling back to cv2", flush=True)
        asyncio.run_coroutine_threadsafe(
            manager.broadcast({'type': 'stream_mode', 'mode': 'jpeg'}), _loop
        )

    _pipe      = asyncio.Queue(maxsize=1)
    fps_frames = 0
    fps_t      = time.perf_counter()

    def _msg_full(fw, fh, jpeg):
        return struct.pack('>BHH', 0x01, fw, fh) + jpeg

    def _msg_patch(fw, fh, px, py, pw, ph, jpeg):
        return struct.pack('>BHHHHHHHI', 0x02, fw, fh, px, py, pw, ph, len(jpeg)) + jpeg

    BLOCK       = 64
    DIFF_THR    = 12
    FORCE_EVERY = 90
    PATCH_LIMIT = 0.45
    _prev_arr   = None
    _frame_ctr  = 0

    def _encode_jpeg(a, q):
        if use_turbo:
            return bytes(tj.encode(a, quality=q, jpeg_subsample=_TJSAMP_444, pixel_format=_TJPF_BGR))
        _, enc = cv2.imencode('.jpg', a, [cv2.IMWRITE_JPEG_QUALITY, q])
        return enc.tobytes()

    def _dirty_bbox(arr, prev, block):
        H, W  = arr.shape[:2]
        diff  = cv2.absdiff(arr, prev)
        gray  = cv2.cvtColor(diff, cv2.COLOR_BGR2GRAY) if diff.ndim == 3 else diff
        ph    = ((H + block - 1) // block) * block
        pw    = ((W + block - 1) // block) * block
        if ph != H or pw != W:
            padded = np.zeros((ph, pw), dtype=np.uint8)
            padded[:H, :W] = gray
            gray = padded
        rows_b    = ph // block
        cols_b    = pw // block
        blocks    = gray.reshape(rows_b, block, cols_b, block)
        block_max = blocks.max(axis=(1, 3))
        dirty     = block_max > DIFF_THR
        if not dirty.any(): return None
        dr = np.where(dirty.any(axis=1))[0]
        dc = np.where(dirty.any(axis=0))[0]
        y0 = int(dr[0])  * block
        y1 = min(int(dr[-1]+1) * block, H) - 1
        x0 = int(dc[0])  * block
        x1 = min(int(dc[-1]+1) * block, W) - 1
        return x0, y0, x1, y1

    async def _encode_emit():
        nonlocal fps_frames, fps_t, _prev_arr, _frame_ctr
        loop = asyncio.get_running_loop()
        while screen_streaming:
            try:
                item = await asyncio.wait_for(_pipe.get(), timeout=0.1)
            except asyncio.TimeoutError:
                continue
            if item is None:
                break
            arr, cfg_snap = item

            if use_h264:
                ok = await loop.run_in_executor(None, h264.send_frame, arr)
                if not ok:
                    _vprint("⚠ H264 send_frame failed", flush=True); break
                fps_frames += 1
                now = time.perf_counter()
                if now - fps_t >= 1.0:
                    await manager.broadcast({'type': 'fps_update', 'fps': round(fps_frames / (now - fps_t), 1)})
                    fps_frames = 0; fps_t = now
                continue

            q  = cfg_snap.get('quality', 65)
            H, W = arr.shape[:2]
            _frame_ctr += 1
            force = (_frame_ctr % FORCE_EVERY == 1) or (_prev_arr is None) or (_prev_arr.shape != arr.shape)

            if force:
                jpeg = await loop.run_in_executor(None, _encode_jpeg, arr, q)
                if jpeg:
                    await manager.broadcast_bytes(_msg_full(W, H, jpeg))
            else:
                bbox = await loop.run_in_executor(None, _dirty_bbox, arr, _prev_arr, BLOCK)
                if bbox is None:
                    _prev_arr = arr
                    continue
                x0, y0, x1, y1 = bbox
                pw_p, ph_p = x1 - x0 + 1, y1 - y0 + 1
                if (pw_p * ph_p) / (W * H) > PATCH_LIMIT:
                    jpeg = await loop.run_in_executor(None, _encode_jpeg, arr, q)
                    if jpeg:
                        await manager.broadcast_bytes(_msg_full(W, H, jpeg))
                else:
                    patch = arr[y0:y1+1, x0:x1+1]
                    jpeg  = await loop.run_in_executor(None, _encode_jpeg, patch, q)
                    if jpeg:
                        await manager.broadcast_bytes(_msg_patch(W, H, x0, y0, pw_p, ph_p, jpeg))

            _prev_arr = arr
            fps_frames += 1
            now = time.perf_counter()
            if now - fps_t >= 1.0:
                await manager.broadcast({'type': 'fps_update', 'fps': round(fps_frames / (now - fps_t), 1)})
                fps_frames = 0; fps_t = now

    emit_future = asyncio.run_coroutine_threadsafe(_encode_emit(), _loop)

    def _put_frame(arr, cfg):
        if not _pipe.empty():
            try: _pipe.get_nowait()
            except: pass
        try: _pipe.put_nowait((arr, cfg))
        except: pass

    use_dxcam = DXCAM_AVAILABLE and platform.system() == 'Windows' and CV2_AVAILABLE
    if FLAG_BACKEND == 'mss': use_dxcam = False
    elif FLAG_BACKEND == 'dxcam' and not (DXCAM_AVAILABLE and platform.system() == 'Windows'): use_dxcam = False

    if use_dxcam:
        try:
            with _stream_config_lock: cfg = stream_config.copy()
            mon_idx_dx = max(0, cfg.get('monitor', 1) - 1)
            camera = _get_dxcam_camera(mon_idx_dx)
            if camera is None:
                use_dxcam = False
            else:
                with _mss.mss() as _sct:
                    _monitors = _sct.monitors[:]
                _vprint("✅ screen: dxcam active", flush=True)
                try:
                    while screen_streaming:
                        try:
                            t0 = time.perf_counter()
                            with _stream_config_lock: cfg = stream_config.copy()
                            fps          = max(1, cfg['fps'])
                            frame_budget = 1.0 / fps
                            target_h     = cfg['height']

                            frame = camera.grab()
                            if frame is None:
                                elapsed = time.perf_counter() - t0
                                sleep_t = frame_budget - elapsed
                                if sleep_t > 0.001: time.sleep(sleep_t)
                                continue

                            src_h, src_w = frame.shape[:2]
                            mon_idx_mss  = min(cfg.get('monitor', 1), len(_monitors) - 1)
                            mon          = _monitors[max(1, mon_idx_mss)]
                            nw = int(src_w * target_h / src_h)
                            if src_h != target_h:
                                interp = cv2.INTER_AREA if target_h < src_h else cv2.INTER_LINEAR
                                arr = cv2.resize(frame, (nw, target_h), interpolation=interp)
                            else:
                                arr = np.ascontiguousarray(frame)
                            if FLAG_SCALE != 1.0:
                                sh, sw = arr.shape[:2]
                                arr = cv2.resize(arr, (int(sw*FLAG_SCALE), int(sh*FLAG_SCALE)), interpolation=cv2.INTER_AREA)
                            if FLAG_GREY:
                                g = cv2.cvtColor(arr, cv2.COLOR_BGR2GRAY)
                                arr = cv2.cvtColor(g, cv2.COLOR_GRAY2BGR)
                            with _mouse_pos_lock: mx, my = _mouse_pos
                            _draw_cursor(arr, mx, my, mon['left'], mon['top'], src_w, src_h,
                                         cfg.get('cursor_color_bgr', (255, 255, 255)))

                            _loop.call_soon_threadsafe(_put_frame, arr, cfg)

                            elapsed = time.perf_counter() - t0
                            sleep_t = frame_budget - elapsed
                            if sleep_t > 0.001: time.sleep(sleep_t)
                        except Exception as e:
                            _screen_last_error = str(e); _vprint(f"❌ dxcam frame: {e}", flush=True); time.sleep(0.1)
                finally:
                    with _dxcam_camera_lock:
                        global _dxcam_camera
                        if _dxcam_camera is not None:
                            try: _dxcam_camera.stop()
                            except: pass
                            _dxcam_camera = None
        except Exception as e:
            _screen_last_error = str(e); _vprint(f"❌ dxcam init: {e}", flush=True)
    else:
        if not MSS_AVAILABLE:
            _screen_last_error = 'mss not available'; return
        try:
            with _mss.mss() as sct:
                while screen_streaming:
                    try:
                        t0 = time.perf_counter()
                        with _stream_config_lock: cfg = stream_config.copy()
                        mon_idx      = min(cfg.get('monitor', 1), len(sct.monitors) - 1)
                        mon          = sct.monitors[max(1, mon_idx)]
                        target_h     = cfg['height']
                        fps          = max(1, cfg['fps'])
                        frame_budget = 1.0 / fps

                        img = sct.grab(mon)
                        arr = np.frombuffer(img.raw, dtype=np.uint8).reshape((img.height, img.width, 4))[:, :, :3]
                        h, w = arr.shape[:2]
                        nw = int(w * target_h / h)
                        if h != target_h:
                            interp = cv2.INTER_AREA if target_h < h else cv2.INTER_LINEAR
                            arr = cv2.resize(arr, (nw, target_h), interpolation=interp)
                        else:
                            arr = np.ascontiguousarray(arr)
                        if FLAG_SCALE != 1.0:
                            sh, sw = arr.shape[:2]
                            arr = cv2.resize(arr, (int(sw*FLAG_SCALE), int(sh*FLAG_SCALE)), interpolation=cv2.INTER_AREA)
                        if FLAG_GREY:
                            g = cv2.cvtColor(arr, cv2.COLOR_BGR2GRAY)
                            arr = cv2.cvtColor(g, cv2.COLOR_GRAY2BGR)
                        with _mouse_pos_lock: mx, my = _mouse_pos
                        _draw_cursor(arr, mx, my, mon['left'], mon['top'], w, h,
                                     cfg.get('cursor_color_bgr', (255, 255, 255)))

                        _loop.call_soon_threadsafe(_put_frame, arr, cfg)

                        elapsed = time.perf_counter() - t0
                        sleep_t = frame_budget - elapsed
                        if sleep_t > 0.001: time.sleep(sleep_t)
                    except Exception as e:
                        _screen_last_error = str(e); _vprint(f"❌ frame: {e}", flush=True); time.sleep(0.1)
        except Exception as e:
            _screen_last_error = str(e); _vprint(f"❌ screen_worker: {e}", flush=True)

    try: _loop.call_soon_threadsafe(_pipe.put_nowait, None)
    except: pass
    try: emit_future.result(timeout=2)
    except: pass
    if use_h264:
        try: h264.close()
        except: pass
    if _screen_last_error:
        manager.broadcast_sync({'type': 'screen_error', 'msg': _screen_last_error})

if WEBRTC_AVAILABLE:
    from fractions import Fraction as _Fraction

    class ScreenCaptureTrack(MediaStreamTrack):
        kind = "video"

        def __init__(self):
            super().__init__()
            self._pts        = 0
            self._time_base  = _Fraction(1, 90000)
            self._fps        = 30
            self._last_arr   = None
            self._sct        = _mss.mss() if MSS_AVAILABLE else None
            self._sct_mon_idx = -1
            self._sct_mon    = None

        async def recv(self):
            loop = asyncio.get_event_loop()
            with _stream_config_lock:
                self._fps = max(1, stream_config.get('fps', 30))
            frame_arr = await loop.run_in_executor(None, self._capture)

            if frame_arr is not None:
                self._last_arr = frame_arr
            elif self._last_arr is not None:
                frame_arr = self._last_arr

            if frame_arr is not None:
                frame = av.VideoFrame.from_ndarray(frame_arr, format='bgr24')
            else:
                frame = av.VideoFrame(width=640, height=480, format='rgb24')

            frame.pts       = self._pts
            frame.time_base = self._time_base
            self._pts      += int(90000 / self._fps)
            await asyncio.sleep(1.0 / self._fps)
            return frame

        def _capture(self):
            if not CV2_AVAILABLE: return None
            try:
                with _stream_config_lock: cfg = stream_config.copy()
                target_h  = cfg['height']
                mon_idx   = min(cfg.get('monitor', 1), len(self._sct.monitors) - 1) if self._sct else 1
                dx = _get_dxcam_camera()
                if dx is not None:
                    frame = dx.grab()
                    if frame is None: return None
                    src_h, src_w = frame.shape[:2]
                    arr = frame
                    if self._sct:
                        if mon_idx != self._sct_mon_idx:
                            self._sct_mon_idx = mon_idx
                            self._sct_mon = self._sct.monitors[max(1, mon_idx)]
                        mon_left, mon_top = self._sct_mon['left'], self._sct_mon['top']
                    else:
                        mon_left, mon_top = 0, 0
                else:
                    if not MSS_AVAILABLE or not self._sct: return None
                    if mon_idx != self._sct_mon_idx:
                        self._sct_mon_idx = mon_idx
                        self._sct_mon = self._sct.monitors[max(1, mon_idx)]
                    img  = self._sct.grab(self._sct_mon)
                    arr  = np.frombuffer(img.raw, dtype=np.uint8).reshape((img.height, img.width, 4))[:, :, :3]
                    src_h, src_w = arr.shape[:2]
                    mon_left, mon_top = self._sct_mon['left'], self._sct_mon['top']

                nw = int(src_w * target_h / src_h)
                if src_h != target_h:
                    interp = cv2.INTER_AREA if target_h < src_h else cv2.INTER_LINEAR
                    arr = cv2.resize(arr, (nw, target_h), interpolation=interp)
                else:
                    arr = np.ascontiguousarray(arr)
                with _mouse_pos_lock: mx, my = _mouse_pos
                _draw_cursor(arr, mx, my, mon_left, mon_top, src_w, src_h,
                             cfg.get('cursor_color_bgr', (255, 255, 255)))
                return arr
            except: return None

_mic_queue  = _queue.Queue(maxsize=40)
_mic_active = False
_mic_worker_thread = None

def _mic_worker():
    global _mic_active
    try:
        import sounddevice as sd
        device_idx = None
        for i, dev in enumerate(sd.query_devices()):
            name = dev['name'].lower()
            if 'cable' in name and dev['max_output_channels'] > 0:
                device_idx = i; break
        if device_idx is None:
            _vprint("❌ mic: CABLE Input not found — start VB-Audio", flush=True)
            _mic_active = False; return
        stream = sd.RawOutputStream(samplerate=44100, channels=1, dtype='int16',
                                    blocksize=2048, latency='low', device=device_idx)
        stream.start()
        while _mic_active:
            try:
                pcm = _mic_queue.get(timeout=0.5)
                if pcm is None: break
                stream.write(pcm)
            except _queue.Empty: continue
            except Exception as e: _vprint(f"mic_worker write: {e}", flush=True)
        stream.stop(); stream.close()
    except Exception as e: _vprint(f"mic_worker: {e}", flush=True)

audio_streaming = False
_audio_thread   = None
_AUDIO_CHUNK    = 4096
_AUDIO_RATE     = 22050

def _audio_worker():
    global audio_streaming
    try:
        import sounddevice as sd
        device_idx = None
        for i, dev in enumerate(sd.query_devices()):
            name = dev['name'].lower()
            if 'cable' in name and dev['max_input_channels'] > 0:
                device_idx = i; break
        if device_idx is None:
            _vprint("❌ audio: CABLE Output not found — start VB-Audio", flush=True)
            audio_streaming = False; return
        with sd.InputStream(samplerate=_AUDIO_RATE, channels=1, dtype='int16',
                            blocksize=_AUDIO_CHUNK, device=device_idx) as stream:
            while audio_streaming:
                data, _ = stream.read(_AUDIO_CHUNK)
                encoded = base64.b64encode(data.tobytes()).decode()
                manager.broadcast_sync({'type': 'audio_chunk', 'data': encoded})
    except Exception as e:
        _vprint(f"❌ audio_worker: {e}", flush=True); audio_streaming = False

_last_clip    = ""
_clip_lock    = threading.Lock()
_clip_running = False

def _clipboard_watcher():
    global _last_clip, _clip_running
    try:
        import pyperclip
    except ImportError:
        _vprint("⚠ pyperclip not available — clipboard sync disabled", flush=True); return
    while _clip_running:
        try:
            current = pyperclip.paste()
            with _clip_lock:
                if current and current != _last_clip:
                    _last_clip = current
                    manager.broadcast_ws_only_sync({'type': 'clipboard_update', 'text': current})
        except: pass
        time.sleep(2)

def _stats_pusher():
    while True:
        time.sleep(5)
        try:
            stats = get_system_stats()
            manager.broadcast_sync({'type': 'stats_push', **stats})
        except: pass

LOG_FILE  = os.path.join(BASE_DIR, "portdesk_events.log")
_log_lock = threading.Lock()

_SEVERITY_MAP = {
    'connect':       'INFO',
    'disconnect':    'INFO',
    'pin_success':   'INFO',
    'pin_fail':      'WARNING',
    'pin_set':       'INFO',
    'pin_cleared':   'INFO',
    'task_kill':     'WARNING',
    'mic_start':     'INFO',
    'mic_stop':      'INFO',
    'audio_start':   'INFO',
    'audio_stop':    'INFO',
    'sched_run':     'INFO',
    'ip_rejected':   'WARNING',
    'ip_blacklisted':'WARNING',
    'lockdown':      'CRITICAL',
    'lockdown_off':  'INFO',
    'intrusion':     'CRITICAL',
    'kick_all':      'WARNING',
    'startup':        'INFO',
    'security_restore':'WARNING',
}

def _log_event(event_type, detail='', ip='system', severity=None):
    with _log_lock:
        last_hash = '0' * 64
        try:
            if os.path.exists(LOG_FILE):
                with open(LOG_FILE, 'rb') as f:
                    lines = f.read().splitlines()
                for line in reversed(lines):
                    if line.strip():
                        try:
                            last_hash = json.loads(line).get('hash', '0' * 64)
                        except: pass
                        break
        except: pass

        sev = severity or _SEVERITY_MAP.get(event_type, 'INFO')
        entry = {
            't':        time.strftime('%Y-%m-%d %H:%M:%S'),
            'type':     event_type,
            'severity': sev,
            'ip':       ip,
            'detail':   detail,
            'prev':     last_hash,
        }
        chain_str     = json.dumps(entry, sort_keys=True, separators=(',', ':'))
        entry['hash'] = hashlib.sha256(chain_str.encode()).hexdigest()

        with open(LOG_FILE, 'a', encoding='utf-8') as f:
            f.write(json.dumps(entry) + '\n')

def _press_win_shortcut(keys):
    system = platform.system()
    try:
        if system == 'Windows':
            VK = {
                'winleft':0x5B,'winright':0x5C,
                'a':0x41,'b':0x42,'c':0x43,'d':0x44,'e':0x45,'f':0x46,'g':0x47,
                'h':0x48,'i':0x49,'j':0x4A,'k':0x4B,'l':0x4C,'m':0x4D,'n':0x4E,
                'o':0x4F,'p':0x50,'q':0x51,'r':0x52,'s':0x53,'t':0x54,'u':0x55,
                'v':0x56,'w':0x57,'x':0x58,'y':0x59,'z':0x5A,
                'tab':0x09,'space':0x20,'enter':0x0D,'escape':0x1B,
                'f1':0x70,'f2':0x71,'f3':0x72,'f4':0x73,'f5':0x74,
                'ctrl':0x11,'alt':0x12,'shift':0x10,
            }
            u32 = ctypes.windll.user32
            vks = [VK.get(k) for k in keys if VK.get(k)]
            if not vks: return False
            for vk in vks: u32.keybd_event(vk, 0, 0, 0)
            time.sleep(0.05)
            for vk in reversed(vks): u32.keybd_event(vk, 0, 0x0002, 0)
            return True
        elif system == 'Darwin':
            mac_keys = ['command' if k in ('winleft','winright','command','cmd') else k for k in keys]
            with _pyautogui_lock: pyautogui.hotkey(*mac_keys)
            return True
        else:
            with _pyautogui_lock: pyautogui.hotkey(*keys)
            return True
    except Exception as e:
        _vprint(f"win shortcut error: {e}", flush=True); return False

SCHED_FILE    = os.path.join(BASE_DIR, "portdesk_scheduled.json")
_sched_lock   = threading.Lock()
_sched_thread = None
_sched_running = False

def _load_scheduled():
    try:
        with open(SCHED_FILE) as f: return json.load(f)
    except: return []

def _save_scheduled(tasks):
    with open(SCHED_FILE, 'w') as f: json.dump(tasks, f, indent=2)

scheduled_tasks = _load_scheduled()

MACROS_FILE = os.path.join(BASE_DIR, "portdesk_macros.json")
_macro_lock = threading.Lock()

def _load_macros():
    try:
        with open(MACROS_FILE) as f: return json.load(f)
    except: return {}

def _save_macros(m):
    with open(MACROS_FILE, 'w') as f: json.dump(m, f, indent=2)

macros = _load_macros()

def _scheduler_worker():
    global _sched_running
    while _sched_running:
        now = time.strftime('%H:%M')
        with _sched_lock:
            for task in scheduled_tasks:
                if not task.get('enabled', True): continue
                if task.get('time') == now and task.get('last_run') != now:
                    task['last_run'] = now
                    _save_scheduled(scheduled_tasks)
                    macro_name = task.get('macro')
                    with _macro_lock: steps = macros.get(macro_name, [])
                    if steps:
                        def _run(s=steps):
                            for step in s:
                                t = step.get('type','')
                                try:
                                    if t == 'type':
                                        type_text(step['text'])
                                    else:
                                        with _pyautogui_lock:
                                            if   t=='key':      pyautogui.press(map_key(step['key']))
                                            elif t=='shortcut': pyautogui.hotkey(*[map_key(k) for k in step['keys']])
                                            elif t=='click':
                                                bt = step.get('btn','left')
                                                if   bt=='left':   pyautogui.click()
                                                elif bt=='right':  pyautogui.rightClick()
                                                elif bt=='double': pyautogui.doubleClick()
                                            elif t=='scroll':   pyautogui.scroll(int(step.get('dy',0)))
                                    delay = step.get('delay', 0.1)
                                    if delay > 0: time.sleep(delay)
                                except Exception as e: _vprint(f"sched step: {e}", flush=True)
                        threading.Thread(target=_run, daemon=True).start()
                        _log_event('sched_run', macro_name)
        time.sleep(10)

_pin_lockout_existing_ = True  # lockout vars already declared above

def _check_linux_compatibility():
    if platform.system() != 'Linux': return []
    errors = []
    if 'DISPLAY' not in os.environ:
        if 'WAYLAND_DISPLAY' in os.environ:
            errors.append('Wayland detected without DISPLAY; run xwayland or use X11 session if pyautogui not working.')
        else:
            errors.append('DISPLAY variable not set; headless mode. Use xvfb-run to start the app.')
    import shutil
    if not shutil.which('xclip') and not shutil.which('xsel'):
        errors.append('xclip/xsel not installed; clipboard sync may not work.')
    if not shutil.which('xdotool'):
        errors.append('xdotool not installed; virtual keyboard may be slower or unavailable on Linux.')
    return errors

async def _dispatch(data: dict, ws):
    global screen_streaming, screen_thread, _mic_active, _mic_worker_thread, audio_streaming, _audio_thread
    t  = data.get('_ev', data.get('type', ''))
    ip = ws.client.host

    # ── Group 3: per-event-type rate limiting ─────────────────────────────
    bucket = _ws_buckets.get(t, _ws_buckets['default'])
    if not bucket.consume(ip):
        return

    _mouse_events = {'move','click','scroll','selector_start','selector_move','selector_end'}
    _keyboard_events = {'key','type','key_down','key_up','shortcut'}
    if t in _mouse_events and (FLAG_NO_MOUSE or FLAG_WATCH_ONLY): return
    if t in _keyboard_events and (FLAG_NO_KEYBOARD or FLAG_WATCH_ONLY): return

    if t == 'move':
        dx, dy = int(data.get('dx',0)), int(data.get('dy',0))
        def _do_move():
            if _pyautogui_lock.acquire(blocking=False):
                try: pyautogui.moveRel(dx, dy, duration=0)
                finally: _pyautogui_lock.release()
        asyncio.get_event_loop().run_in_executor(None, _do_move)

    elif t == 'click':
        ct = data.get('type', 'left')
        loop = asyncio.get_event_loop()
        def _do_click():
            with _pyautogui_lock:
                if   ct=='left':   pyautogui.click()
                elif ct=='right':  pyautogui.rightClick()
                elif ct=='double': pyautogui.doubleClick()
                elif ct=='middle': pyautogui.middleClick()
        await loop.run_in_executor(None, _do_click)

    elif t == 'scroll':
        dy = int(data.get('dy',0))
        loop = asyncio.get_event_loop()
        def _do_scroll():
            with _pyautogui_lock: pyautogui.scroll(dy)
        await loop.run_in_executor(None, _do_scroll)

    elif t == 'selector_start':
        loop = asyncio.get_event_loop()
        def _do_sel_start():
            with _pyautogui_lock: pyautogui.mouseDown()
        await loop.run_in_executor(None, _do_sel_start)
    elif t == 'selector_move':
        dx, dy = int(data.get('dx',0)), int(data.get('dy',0))
        def _do_sel_move():
            if _pyautogui_lock.acquire(blocking=False):
                try: pyautogui.moveRel(dx, dy, duration=0)
                finally: _pyautogui_lock.release()
        asyncio.get_event_loop().run_in_executor(None, _do_sel_move)
    elif t == 'selector_end':
        loop = asyncio.get_event_loop()
        def _do_sel_end():
            with _pyautogui_lock: pyautogui.mouseUp()
        await loop.run_in_executor(None, _do_sel_end)

    elif t == 'shortcut':
        keys   = [map_key(k) for k in data.get('keys',[])]
        system = platform.system()
        loop   = asyncio.get_event_loop()
        if system == 'Linux':
            keys = ['super' if k in ('winleft','winright','command','cmd') else k for k in keys]
        has_win = any(k in ('winleft','winright') for k in keys)
        has_cmd = any(k in ('command','cmd','super') for k in keys)
        try:
            if system == 'Windows' and has_win:
                ok = await loop.run_in_executor(None, _press_win_shortcut, keys)
                if not ok:
                    with _pyautogui_lock: pyautogui.hotkey(*keys)
            elif system == 'Darwin' and (has_win or has_cmd):
                mac_keys = ['command' if k in ('winleft','winright','command','cmd') else k for k in keys]
                with _pyautogui_lock: pyautogui.hotkey(*mac_keys)
            else:
                with _pyautogui_lock: pyautogui.hotkey(*keys)
        except Exception as e: _vprint(f"shortcut error: {e}", flush=True)

    elif t == 'key':
        key    = map_key(data.get('key', ''))
        system = platform.system()
        loop   = asyncio.get_event_loop()
        if system == 'Linux':
            if _virtual_kb_device:
                key_code = getattr(uinput, f'KEY_{key.upper()}', None)
                if key_code:
                    def _vkey_press(_kc=key_code):
                        _send_virtual_key(_kc, True); time.sleep(0.01); _send_virtual_key(_kc, False)
                    await loop.run_in_executor(None, _vkey_press)
            elif SUBPROCESS_AVAILABLE: await loop.run_in_executor(None, _send_xdotool_key, key)
            else:
                try:
                    with _pyautogui_lock: pyautogui.press(key)
                except Exception as e: _vprint(f"key: {e}", flush=True)
        else:
            try:
                with _pyautogui_lock: pyautogui.press(key)
            except Exception as e: _vprint(f"key: {e}", flush=True)

    elif t == 'type':
        text   = data.get('text', '')
        system = platform.system()
        loop   = asyncio.get_event_loop()
        if system == 'Linux':
            if _virtual_kb_device: await loop.run_in_executor(None, _send_virtual_text, text)
            elif SUBPROCESS_AVAILABLE: await loop.run_in_executor(None, _send_xdotool_text, text)
            else: await loop.run_in_executor(None, type_text, text)
        else: await loop.run_in_executor(None, type_text, text)

    elif t == 'key_down':
        _key = map_key(data.get('key',''))
        loop = asyncio.get_event_loop()
        def _do_kd():
            try:
                with _pyautogui_lock: pyautogui.keyDown(_key)
            except Exception as e: _vprint(f"key_down: {e}", flush=True)
        await loop.run_in_executor(None, _do_kd)

    elif t == 'key_up':
        _key = map_key(data.get('key',''))
        loop = asyncio.get_event_loop()
        def _do_ku():
            try:
                with _pyautogui_lock: pyautogui.keyUp(_key)
            except Exception as e: _vprint(f"key_up: {e}", flush=True)
        await loop.run_in_executor(None, _do_ku)

    elif t == 'stream_config':
        with _stream_config_lock:
            if 'height'       in data: stream_config['height']          = int(data['height'])
            if 'quality'      in data: stream_config['quality']         = max(10, min(100, int(data['quality'])))
            if 'fps'          in data: stream_config['fps']             = max(1, min(60, int(data['fps'])))
            if 'monitor'      in data: stream_config['monitor']         = max(1, int(data['monitor']))
            if 'cursor_color' in data:
                hex_c = data['cursor_color'].lstrip('#')
                r, g, b = int(hex_c[0:2],16), int(hex_c[2:4],16), int(hex_c[4:6],16)
                stream_config['cursor_color_bgr'] = (b, g, r)

    elif t == 'set_monitor':
        stream_config['monitor'] = max(1, int(data.get('index', 1)))

    elif t == 'screen_start':
        if screen_thread and screen_thread.is_alive():
            screen_streaming = False; time.sleep(0.1)
        screen_streaming = True
        screen_thread = threading.Thread(target=screen_worker, daemon=True)
        screen_thread.start()

    elif t == 'screen_stop':
        screen_streaming = False

    elif t == 'mic_start':
        if _mic_worker_thread and _mic_worker_thread.is_alive():
            _mic_active = False
            try: _mic_queue.put_nowait(None)
            except: pass
            _mic_worker_thread.join(timeout=1.0)
        while not _mic_queue.empty():
            try: _mic_queue.get_nowait()
            except: break
        _mic_active = True
        _mic_worker_thread = threading.Thread(target=_mic_worker, daemon=True)
        _mic_worker_thread.start()
        _log_event('mic_start', ip=ip)

    elif t == 'mic_stop':
        _mic_active = False
        try: _mic_queue.put_nowait(None)
        except: pass
        _log_event('mic_stop', ip=ip)

    elif t == 'mic_chunk':
        if not _mic_active: return
        raw = data.get('data')
        if not raw: return
        try:
            pcm = base64.b64decode(raw)
            try: _mic_queue.put_nowait(pcm)
            except _queue.Full: pass
        except Exception as e: _vprint(f"mic_chunk: {e}", flush=True)

    elif t == 'audio_start':
        if _audio_thread and _audio_thread.is_alive(): return
        audio_streaming = True
        _audio_thread = threading.Thread(target=_audio_worker, daemon=True)
        _audio_thread.start()
        _log_event('audio_start', ip=ip)

    elif t == 'audio_stop':
        audio_streaming = False
        _log_event('audio_stop', ip=ip)

@app.websocket('/ws')
async def websocket_endpoint(ws: WebSocket):
    global screen_streaming, audio_streaming, _mic_active, _active_client_ws
    ip = ws.client.host

    with _lockdown_lock:
        if _lockdown and ip not in ('127.0.0.1', '::1', 'localhost'):
            await ws.close(1008); return

    if ip not in ('127.0.0.1', '::1', 'localhost'):
        if ip in security.get("blacklist", []):
            await ws.close(1008); return
        if not _is_allowed(ip):
            await ws.close(1008); return

    with _active_client_lock:
        if _active_client_ws is not None:
            await ws.close(1008); return
        _active_client_ws = ws
        globals()['_active_client_ip'] = ip

    await manager.connect(ws)
    _log_event('connect', ip=ip)
    try:
        while True:
            data = await ws.receive_json()
            if not _is_allowed(ip): break
            await _dispatch(data, ws)
    except WebSocketDisconnect:
        pass
    except Exception as e:
        _vprint(f"ws error: {e}", flush=True)
    finally:
        with _active_client_lock:
            if _active_client_ws is ws:
                _active_client_ws = None
                globals()['_active_client_ip'] = None
        manager.disconnect(ws)
        screen_streaming = False
        audio_streaming  = False
        _mic_active      = False
        try: _mic_queue.put_nowait(None)
        except: pass
        for mod in ('ctrl', 'alt', 'shift', 'winleft'):
            try:
                with _pyautogui_lock: pyautogui.keyUp(mod)
            except: pass

@app.post('/webrtc/offer')
async def webrtc_offer(request: Request):
    if not WEBRTC_AVAILABLE or FLAG_NO_WEBRTC:
        return JSONResponse({'error': 'WebRTC disabled'}, status_code=501)

    ip = request.client.host
    with _active_client_lock:
        _aip = _active_client_ip
    if _aip is not None and _aip != ip:
        return JSONResponse({'error': 'session occupied'}, status_code=423)

    params = await request.json()
    offer  = RTCSessionDescription(sdp=params['sdp'], type=params['type'])
    pc     = RTCPeerConnection(configuration=RTCConfiguration(iceServers=STUN_SERVERS))
    _webrtc_pcs.add(pc)

    @pc.on('connectionstatechange')
    async def on_state():
        if pc.connectionState in ('failed', 'closed', 'disconnected'):
            await pc.close()
            _webrtc_pcs.discard(pc)

    try:
        pc.addTrack(ScreenCaptureTrack())
        await pc.setRemoteDescription(offer)
        answer = await pc.createAnswer()
        await pc.setLocalDescription(answer)
        return {'sdp': pc.localDescription.sdp, 'type': pc.localDescription.type}
    except Exception as e:
        await pc.close()
        _webrtc_pcs.discard(pc)
        return JSONResponse({'error': str(e)}, status_code=500)


@app.post('/webrtc/control/offer')
async def webrtc_control_offer(request: Request):
    """WebRTC data channel endpoint — layer 2 fallback for control commands via STUN P2P."""
    if not WEBRTC_AVAILABLE or FLAG_NO_WEBRTC:
        return JSONResponse({'error': 'WebRTC disabled'}, status_code=501)

    ip = request.client.host
    if ip not in ('127.0.0.1', '::1', 'localhost') and not _is_allowed(ip):
        return JSONResponse({'error': 'not whitelisted'}, status_code=403)

    params = await request.json()
    offer  = RTCSessionDescription(sdp=params['sdp'], type=params['type'])
    pc     = RTCPeerConnection(configuration=RTCConfiguration(iceServers=STUN_SERVERS))
    _webrtc_pcs.add(pc)

    dc_client_ref: list = []

    @pc.on('datachannel')
    def on_datachannel(channel):
        with _active_client_lock:
            if _active_client_ws is not None:
                try: channel.close()
                except: pass
                return
        dc = _DataChannelClient(channel, ip)
        dc_client_ref.append(dc)
        with _webrtc_dc_lock:
            _webrtc_dc_clients.append(dc)
        manager.active.append(dc)
        print(f"✅ WebRTC data channel opened from {ip}", flush=True)

        @channel.on('message')
        async def on_message(message):
            try:
                data = json.loads(message)
                await _dispatch(data, dc)
            except Exception as e:
                _vprint(f"DC dispatch error: {e}", flush=True)

        @channel.on('close')
        def on_close():
            with _webrtc_dc_lock:
                if dc in _webrtc_dc_clients:
                    _webrtc_dc_clients.remove(dc)
            if dc in manager.active:
                manager.active.remove(dc)
            print(f"ℹ️  WebRTC data channel closed from {ip}", flush=True)

    @pc.on('connectionstatechange')
    async def on_state():
        if pc.connectionState in ('failed', 'closed', 'disconnected'):
            for dc in dc_client_ref:
                with _webrtc_dc_lock:
                    if dc in _webrtc_dc_clients:
                        _webrtc_dc_clients.remove(dc)
                if dc in manager.active:
                    manager.active.remove(dc)
            await pc.close()
            _webrtc_pcs.discard(pc)

    await pc.setRemoteDescription(offer)
    answer = await pc.createAnswer()
    await pc.setLocalDescription(answer)
    return {'sdp': pc.localDescription.sdp, 'type': pc.localDescription.type}


@app.get('/')
async def index(request: Request):
    path = os.path.join(BASE_DIR, 'portdesk_client.html')
    if not os.path.isfile(path):
        return JSONResponse({'error': 'portdesk_client.html not found'}, status_code=500)
    _log_event('connect', ip=request.client.host)
    return FileResponse(path)

@app.get('/ping')
async def ping():
    return {'pong': time.time()}

@app.get('/stats')
async def stats(request: Request):
    if not _is_allowed(request.client.host):
        return JSONResponse({"error": "forbidden"}, status_code=403)
    return get_system_stats()

@app.get('/screen/status')
async def screen_status():
    return {
        'streaming':    screen_streaming,
        'thread_alive': screen_thread is not None and screen_thread.is_alive(),
        'mss':          MSS_AVAILABLE,
        'dxcam':        DXCAM_AVAILABLE and platform.system() == 'Windows',
        'error':        _screen_last_error,
    }

@app.post('/screen/start')
async def screen_start_http(request: Request):
    global screen_streaming, screen_thread
    with _active_client_lock:
        if _active_client_ws is None:
            return JSONResponse({'error': 'no active client'}, status_code=403)
    if not screen_streaming:
        screen_streaming = True
        screen_thread = threading.Thread(target=screen_worker, daemon=True)
        screen_thread.start()
    return {'ok': True}

@app.post('/screen/stop')
async def screen_stop_http():
    global screen_streaming
    screen_streaming = False
    return {'ok': True}

@app.get('/security/whitelist')
async def get_whitelist(request: Request):
    ip = request.client.host
    return {"approved": ip in security.get("whitelist", []), "ip": ip}

@app.post('/security/whitelist/request')
async def whitelist_request(request: Request):
    ip = request.client.host
    if ip in security.get("blacklist", []):
        return JSONResponse({"error": "blacklisted"}, status_code=403)
    if ip in security.get("whitelist", []):
        return {"ok": True, "already": True}
    _prompt_add_ip(ip)
    return {"ok": True, "pending": True}

@app.post('/security/approve')
async def security_approve(request: Request, ip: str = '', action: str = 'allow'):
    if request.client.host not in ('127.0.0.1', '::1', 'localhost'):
        return JSONResponse({"error": "forbidden"}, status_code=403)
    if not ip:
        return JSONResponse({"error": "ip required"}, status_code=400)
    _approve_ip(ip, action)
    if action == 'allow':
        return {"ok": True, "approved": ip}
    return {"ok": True, "rejected": ip}

@app.post('/security/whitelist/remove_self')
async def whitelist_remove_self(request: Request):
    ip = request.client.host
    with _sec_lock:
        if ip in security.get("whitelist", []):
            security["whitelist"].remove(ip)
        security.get("pins", {}).pop(ip, None)
        security.get("lockout", {}).pop(ip, None)
        _save_security()
    _pin_lockout.pop(ip, None)
    _pin_fails[ip] = 0
    _pin_lockout_count[ip] = 0
    return {"ok": True}

@app.post('/security/blacklist/remove')
async def blacklist_remove(request: Request):
    if request.client.host not in ('127.0.0.1', '::1', 'localhost'):
        return JSONResponse({"error": "forbidden"}, status_code=403)
    d = await request.json()
    ip = d.get("ip", "")
    with _sec_lock:
        if ip in security.get("blacklist", []):
            security["blacklist"].remove(ip)
        _reject_counts[ip] = 0
        _save_security()
    return {"ok": True}

def _list_drives():
    if platform.system() == 'Windows':
        return [d+':\\' for d in _string.ascii_uppercase if os.path.exists(d+':\\')]
    elif platform.system() == 'Darwin':
        vols = ['/Volumes/' + v for v in os.listdir('/Volumes')] if os.path.exists('/Volumes') else []
        return ['/'] + vols
    else:
        return ['/home', '/tmp', '/']

@app.get('/explorer/drives')
async def explorer_drives():
    if FLAG_NO_EXPLORER or FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    return _list_drives()

@app.get('/explorer/list')
async def explorer_list(path: str = ''):
    if FLAG_NO_EXPLORER or FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    if not path: return {'drives': _list_drives()}
    real = os.path.realpath(path)
    _SENSITIVE = ['/proc', '/sys', '/dev', 'C:\\Windows\\System32', 'C:\\Windows']
    if any(real.startswith(os.path.realpath(s)) for s in _SENSITIVE):
        return JSONResponse({'error': 'access denied'}, status_code=403)
    if not os.path.exists(real):
        return JSONResponse({'error': 'Path not found'}, status_code=404)
    try:
        entries = []
        for name in sorted(os.listdir(real), key=lambda x: (not os.path.isdir(os.path.join(real,x)), x.lower())):
            full = os.path.join(real, name)
            try:
                stat = os.stat(full)
                if os.path.isdir(full):
                    entries.append({'name': name, 'type': 'dir', 'size': 0, 'modified': int(stat.st_mtime)})
                else:
                    entries.append({'name': name, 'type': 'file', 'size': stat.st_size, 'modified': int(stat.st_mtime)})
            except PermissionError:
                entries.append({'name': name, 'type': 'dir' if os.path.isdir(full) else 'file', 'size': 0, 'modified': 0, 'denied': True})
        return {'path': real, 'entries': entries}
    except PermissionError: return JSONResponse({'error': 'Permission denied'}, status_code=403)
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)
    except PermissionError: return JSONResponse({'error': 'Permission denied'}, status_code=403)
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.get('/explorer/download')
async def explorer_download(path: str = ''):
    if FLAG_NO_EXPLORER or FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    if not path or not os.path.exists(path):
        return JSONResponse({'error': 'not found'}, status_code=404)
    real = os.path.realpath(path)
    _SENSITIVE = ['/proc', '/sys', '/dev', 'C:\\Windows\\System32', 'C:\\Windows']
    if any(real.startswith(os.path.realpath(s)) for s in _SENSITIVE):
        return JSONResponse({'error': 'access denied'}, status_code=403)
    if os.path.isfile(real):
        return FileResponse(real, filename=os.path.basename(real))
    buf = io.BytesIO()
    import zipfile
    with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
        for root, _, files in os.walk(real):
            for fname in files:
                full = os.path.join(root, fname)
                try: zf.write(full, os.path.relpath(full, os.path.dirname(real)))
                except: pass
    buf.seek(0)
    return StreamingResponse(buf, media_type='application/zip',
                             headers={'Content-Disposition': f'attachment; filename="{os.path.basename(real)}.zip"'})

@app.post('/explorer/download_multi')
async def explorer_download_multi(request: Request):
    if FLAG_NO_EXPLORER or FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    import zipfile
    d = await request.json()
    paths = d.get('paths', [])
    if not paths: return JSONResponse({'error': 'no paths'}, status_code=400)

    _SENSITIVE = ['/proc', '/sys', '/dev', 'C:\\Windows\\System32', 'C:\\Windows']
    def _safe(p):
        if not os.path.exists(p): return False
        r = os.path.realpath(p)
        return not any(r.startswith(os.path.realpath(s)) for s in _SENSITIVE)
    paths = [p for p in paths if _safe(p)]
    if not paths: return JSONResponse({'error': 'access denied'}, status_code=403)
    paths = [os.path.realpath(p) for p in paths]
    if len(paths) == 1 and os.path.isfile(paths[0]):
        return FileResponse(paths[0], filename=os.path.basename(paths[0]))
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
        for p in paths:
            if not os.path.exists(p): continue
            if os.path.isfile(p):
                try: zf.write(p, os.path.basename(p))
                except: pass
            else:
                for root, _, files in os.walk(p):
                    for fname in files:
                        full = os.path.join(root, fname)
                        try: zf.write(full, os.path.relpath(full, p))
                        except: pass
    buf.seek(0)
    return StreamingResponse(buf, media_type='application/zip',
                             headers={'Content-Disposition': 'attachment; filename="pcc_files.zip"'})

@app.post('/explorer/upload')
async def explorer_upload(request: Request, files: list[UploadFile] = File(...), path: str = Form(...)):
    if FLAG_NO_EXPLORER or FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    dest_dir = path or os.path.join(os.path.expanduser('~'), 'Downloads')
    if not os.path.isdir(dest_dir):
        return JSONResponse({'error': 'Folder not found'}, status_code=400)
    saved = []
    CHUNK_SIZE = 65536
    for f in files:
        safe = os.path.basename(f.filename)
        if not safe: continue
        if FLAG_UPLOAD_LIMIT is not None:
            content = await f.read()
            if len(content) > FLAG_UPLOAD_LIMIT:
                return JSONResponse({'error': f'File "{safe}" exceeds upload limit'}, status_code=413)
            dest = os.path.join(dest_dir, safe)
            base, ext = os.path.splitext(safe)
            c = 1
            while os.path.exists(dest):
                dest = os.path.join(dest_dir, f"{base}_{c}{ext}"); c += 1
            with open(dest, 'wb') as out:
                out.write(content)
            saved.append(safe)
            continue
        dest = os.path.join(dest_dir, safe)
        base, ext = os.path.splitext(safe)
        c = 1
        while os.path.exists(dest):
            dest = os.path.join(dest_dir, f"{base}_{c}{ext}"); c += 1
        with open(dest, 'wb') as out:
            while True:
                chunk = await f.read(CHUNK_SIZE)
                if not chunk:
                    break
                out.write(chunk)
        saved.append(safe)
    return {'ok': True, 'saved': saved}

@app.post('/explorer/mkdir')
async def explorer_mkdir(request: Request):
    d = await request.json()
    path, name = d.get('path','').strip(), d.get('name','').strip()
    if not path or not name: return JSONResponse({'error': 'missing params'}, status_code=400)
    target = os.path.join(path, name)
    try:
        os.makedirs(target, exist_ok=False)
        return {'ok': True}
    except FileExistsError: return JSONResponse({'error': 'Name already exists'}, status_code=409)
    except Exception as e:  return JSONResponse({'error': str(e)}, status_code=500)

@app.post('/explorer/mkfile')
async def explorer_mkfile(request: Request):
    d = await request.json()
    path, name = d.get('path','').strip(), d.get('name','').strip()
    if not path or not name: return JSONResponse({'error': 'missing params'}, status_code=400)
    target = os.path.join(path, name)
    if os.path.exists(target): return JSONResponse({'error': 'Name already exists'}, status_code=409)
    try:
        open(target, 'w').close()
        return {'ok': True}
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.post('/explorer/rename')
async def explorer_rename(request: Request):
    d = await request.json()
    src, new_name = d.get('src','').strip(), d.get('name','').strip()
    if not src or not new_name: return JSONResponse({'error': 'missing params'}, status_code=400)
    dst = os.path.join(os.path.dirname(src), new_name)
    if os.path.exists(dst): return JSONResponse({'error': 'Name already exists'}, status_code=409)
    try: os.rename(src, dst); return {'ok': True}
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.post('/explorer/delete')
async def explorer_delete(request: Request):
    import shutil as _shutil
    d = await request.json()
    paths = d.get('paths', [])
    errors = []
    for p in paths:
        if not os.path.exists(p): continue
        try:
            if os.path.isdir(p): _shutil.rmtree(p)
            else: os.remove(p)
        except Exception as e: errors.append(str(e))
    return {'ok': not errors, 'errors': errors}

@app.post('/explorer/copy')
async def explorer_copy(request: Request):
    import shutil as _shutil
    d = await request.json()
    srcs, dst = d.get('paths', []), d.get('dest', '').strip()
    if not srcs or not dst: return JSONResponse({'error': 'missing params'}, status_code=400)
    if not os.path.isdir(dst): return JSONResponse({'error': 'Destination not found'}, status_code=400)
    errors = []
    for s in srcs:
        try:
            name = os.path.basename(s.rstrip('/\\'))
            t    = os.path.join(dst, name)
            if os.path.isdir(s): _shutil.copytree(s, t)
            else:                _shutil.copy2(s, t)
        except Exception as e: errors.append(str(e))
    return {'ok': not errors, 'errors': errors}

@app.post('/explorer/move')
async def explorer_move(request: Request):
    import shutil as _shutil
    d = await request.json()
    srcs, dst = d.get('paths', []), d.get('dest', '').strip()
    if not srcs or not dst: return JSONResponse({'error': 'missing params'}, status_code=400)
    if not os.path.isdir(dst): return JSONResponse({'error': 'Destination not found'}, status_code=400)
    errors = []
    for s in srcs:
        try: _shutil.move(s, os.path.join(dst, os.path.basename(s.rstrip('/\\'))))
        except Exception as e: errors.append(str(e))
    return {'ok': not errors, 'errors': errors}

@app.post('/explorer/shortcut')
async def explorer_shortcut(request: Request):
    d = await request.json()
    src, dest = d.get('src','').strip(), d.get('dest','').strip()
    if not src or not dest: return JSONResponse({'error': 'missing params'}, status_code=400)
    try:
        if platform.system() == 'Windows':
            import win32com.client
            shell = win32com.client.Dispatch("WScript.Shell")
            lnk_name = os.path.splitext(os.path.basename(src))[0] + '.lnk'
            lnk = shell.CreateShortCut(os.path.join(dest, lnk_name))
            lnk.Targetpath = src; lnk.save()
        elif platform.system() == 'Darwin':
            subprocess.run(['ln', '-s', src, os.path.join(dest, os.path.basename(src))], check=True)
        else:
            name    = os.path.splitext(os.path.basename(src))[0]
            desktop = os.path.join(dest, name + '.desktop')
            with open(desktop, 'w') as f:
                f.write(f'[Desktop Entry]\nType=Link\nName={name}\nURL=file://{src}\nIcon=applications-system\n')
            os.chmod(desktop, 0o755)
            try: subprocess.run(['xdg-desktop-icon', 'install', '--novendor', desktop], check=False)
            except: pass
        return {'ok': True}
    except Exception as e:
        logging.exception("Failed to create explorer shortcut")
        return JSONResponse({'error': 'internal error'}, status_code=500)

@app.get('/explorer/properties')
async def explorer_properties(path: str = ''):
    if not path: return JSONResponse({'error': 'not found'}, status_code=404)
    try:
        fullpath = os.path.realpath(path)
        sensitive_dirs = ['/proc', '/sys', '/dev', 'C:\\Windows\\System32', 'C:\\Windows']
        for s in sensitive_dirs:
            if fullpath.startswith(os.path.realpath(s)):
                return JSONResponse({'error': 'access denied'}, status_code=403)
        if not os.path.exists(fullpath): return JSONResponse({'error': 'not found'}, status_code=404)
        stat = os.stat(fullpath)
        info = {
            'name': os.path.basename(fullpath), 'path': fullpath,
            'type': 'folder' if os.path.isdir(fullpath) else 'file',
            'size': stat.st_size, 'modified': int(stat.st_mtime), 'created': int(stat.st_ctime),
        }
        if os.path.isdir(fullpath):
            try:
                info['size'] = sum(os.path.getsize(os.path.join(r, f)) for r, _, fs in os.walk(fullpath) for f in fs if os.path.exists(os.path.join(r, f)))
            except: info['size'] = 0
        return info
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.get('/macros/list')
async def macros_list():
    with _macro_lock: return list(macros.keys())

@app.post('/macros/save')
async def macros_save(request: Request):
    d = await request.json()
    name, steps = d.get('name',''), d.get('steps',[])
    if not name: return JSONResponse({'error': 'no name'}, status_code=400)
    with _macro_lock: macros[name] = steps; _save_macros(macros)
    return {'ok': True}

@app.post('/macros/delete')
async def macros_delete(request: Request):
    d = await request.json()
    name = d.get('name','')
    with _macro_lock:
        macros.pop(name, None)
        _save_macros(macros)
    return {'ok': True}

@app.post('/macros/run')
async def macros_run(request: Request):
    if FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    d    = await request.json()
    name = d.get('name','')
    with _macro_lock: steps = list(macros.get(name, []))
    if not steps: return JSONResponse({'error': 'not found'}, status_code=404)
    def _run():
        for step in steps:
            t = step.get('type','')
            try:
                with _pyautogui_lock:
                    if   t == 'key':      pyautogui.press(map_key(step['key']))
                    elif t == 'shortcut': pyautogui.hotkey(*[map_key(k) for k in step['keys']])
                    elif t == 'type':     type_text(step['text'])
                    elif t == 'click':
                        bt = step.get('btn','left')
                        if   bt=='left':   pyautogui.click()
                        elif bt=='right':  pyautogui.rightClick()
                        elif bt=='double': pyautogui.doubleClick()
                    elif t == 'scroll':   pyautogui.scroll(int(step.get('dy',0)))
                    elif t == 'move':     pyautogui.moveRel(int(step.get('dx',0)), int(step.get('dy',0)), duration=0)
                delay = step.get('delay', 0.1)
                if delay > 0: time.sleep(delay)
            except Exception as e: _vprint(f"macro step error: {e}", flush=True)
    threading.Thread(target=_run, daemon=True).start()
    return {'ok': True}

@app.get('/stream/encoder_info')
async def stream_encoder_info():
    return {
        'ffmpeg_encoder': _ffmpeg_encoder,
        'hardware':       _ffmpeg_encoder not in (None, 'libx264'),
        'mode':           'h264' if _ffmpeg_encoder_ok else 'jpeg',
        'platform':       platform.system(),
    }

@app.get('/monitors/list')
async def monitors_list():
    if not MSS_AVAILABLE: return []
    try:
        with _mss.mss() as sct:
            return [{'index': i, 'w': m['width'], 'h': m['height'], 'x': m['left'], 'y': m['top']}
                    for i, m in enumerate(sct.monitors) if i > 0]
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.get('/tasks/list')
async def tasks_list():
    try:
        import psutil
        procs_raw = []
        for p in psutil.process_iter(['pid','name','memory_info','status']):
            try: p.cpu_percent(interval=None); procs_raw.append(p)
            except: pass
        time.sleep(0.2)
        procs = []
        for p in procs_raw:
            try:
                cpu = round(p.cpu_percent(interval=None) or 0, 1)
                mi  = p.info.get('memory_info')
                procs.append({'pid': p.pid, 'name': p.name(), 'cpu': cpu, 'mem': mi.rss if mi else 0, 'status': p.status()})
            except: pass
        procs.sort(key=lambda x: x['cpu'], reverse=True)
        return procs[:80]
    except ImportError: return JSONResponse({'error': 'psutil not installed'}, status_code=500)
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.post('/tasks/kill')
async def tasks_kill(request: Request):
    if FLAG_WATCH_ONLY: return JSONResponse({'error': 'disabled'}, status_code=403)
    d   = await request.json()
    pid = d.get('pid')
    if not pid: return JSONResponse({'error': 'no pid'}, status_code=400)
    try:
        import psutil
        psutil.Process(int(pid)).terminate()
        _log_event('task_kill', f'pid={pid}')
        return {'ok': True}
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.get('/log/list')
async def log_list():
    try:
        if not os.path.exists(LOG_FILE): return []
        with _log_lock, open(LOG_FILE, encoding='utf-8') as f:
            lines = f.readlines()
        events = []
        for l in reversed(lines[-200:]):
            try: events.append(json.loads(l.strip()))
            except: pass
        return events
    except Exception as e: return JSONResponse({'error': str(e)}, status_code=500)

@app.post('/log/clear')
async def log_clear():
    with _log_lock: open(LOG_FILE, 'w').close()
    return {'ok': True}

@app.post('/audio/start')
async def audio_start_http(request: Request):
    global audio_streaming, _audio_thread
    if audio_streaming: return {'ok': True}
    audio_streaming = True
    _audio_thread = threading.Thread(target=_audio_worker, daemon=True)
    _audio_thread.start()
    _log_event('audio_start', ip=request.client.host)
    return {'ok': True}

@app.post('/audio/stop')
async def audio_stop_http(request: Request):
    global audio_streaming
    audio_streaming = False
    _log_event('audio_stop', ip=request.client.host)
    return {'ok': True}

@app.post('/auth/pin_check')
async def auth_pin_check(request: Request):
    ip  = request.client.host
    now = time.time()
    if ip in _pin_lockout and now < _pin_lockout[ip]:
        rem = int(_pin_lockout[ip] - now)
        return JSONResponse({'error': f'Blocked. Wait {rem} seconds'}, status_code=429)

    d      = await request.json()
    stored = security.get("pins", {}).get(ip)

    if isinstance(stored, str):
        client_hash = stored
        pin_type    = 'pin'
    elif isinstance(stored, dict):
        client_hash = stored.get('hash')
        pin_type    = stored.get('type', 'pin')
    else:
        client_hash = None
        pin_type    = 'pin'

    if d.get('_probe'):
        return {'server_pin': bool(client_hash), 'pin_type': pin_type}

    if client_hash:
        if pin_type == 'pattern':
            secret = str(d.get('pattern', ''))
            if not secret:
                return JSONResponse({'error': 'Pattern required'}, status_code=400)
        else:
            secret = str(d.get('pin', ''))
            if not secret:
                return JSONResponse({'error': 'PIN required'}, status_code=400)
            if len(secret) != 6:
                return JSONResponse({'error': 'PIN must be exactly 6 digits'}, status_code=400)
        try:
            ok = BCRYPT_AVAILABLE and _bcrypt.checkpw(secret.encode(), client_hash.encode())
        except Exception:
            ok = False
    else:
        ok = d.get('ok', False)

    if ok:
        _pin_fails[ip] = 0
        _pin_lockout.pop(ip, None)
        with _sec_lock:
            security.get("lockout", {}).pop(ip, None)
            _save_security()
        _log_event('pin_success', ip=ip)
        return {'ok': True}

    _pin_fails[ip] += 1
    _log_event('pin_fail', f'attempt={_pin_fails[ip]}', ip=ip)
    if _pin_fails[ip] >= PIN_MAX_TRIES:
        step     = _pin_lockout_count[ip]
        duration = PIN_LOCKOUT_STEPS[min(step, len(PIN_LOCKOUT_STEPS) - 1)]
        _pin_lockout_count[ip] += 1
        _pin_lockout[ip] = now + duration
        _pin_fails[ip]   = 0
        with _sec_lock:
            if "lockout" not in security: security["lockout"] = {}
            security["lockout"][ip] = {"until": now + duration, "count": int(_pin_lockout_count[ip])}
            _save_security()
        return JSONResponse({'error': f'Locked for {duration} seconds due to multiple failed attempts'}, status_code=429)
    return {'ok': False, 'remaining': PIN_MAX_TRIES - _pin_fails[ip]}


@app.post('/auth/set_pin')
async def auth_set_pin(request: Request):
    ip       = request.client.host
    d        = await request.json()
    if d.get('_probe'): return {'ok': True}
    pin_type = d.get('type', 'pin')
    if not BCRYPT_AVAILABLE:
        return JSONResponse({'error': 'bcrypt not installed on server'}, status_code=500)
    if pin_type == 'pattern':
        pattern = str(d.get('pattern', ''))
        if len(pattern) < 4:
            return JSONResponse({'error': 'Pattern must connect at least 4 nodes'}, status_code=400)
        if not all(c in '012345678' for c in pattern) or len(set(pattern)) != len(pattern):
            return JSONResponse({'error': 'Invalid pattern'}, status_code=400)
        hashed = _bcrypt.hashpw(pattern.encode(), _bcrypt.gensalt()).decode()
        with _sec_lock:
            if "pins" not in security: security["pins"] = {}
            security["pins"][ip] = {"hash": hashed, "type": "pattern"}
            _save_security()
        _log_event('pattern_set', ip=ip)
    else:
        pin = str(d.get('pin', ''))
        if len(pin) != 6:
            return JSONResponse({'error': 'PIN must be exactly 6 digits'}, status_code=400)
        if not pin.isdigit():
            return JSONResponse({'error': 'PIN must be digits only'}, status_code=400)
        hashed = _bcrypt.hashpw(pin.encode(), _bcrypt.gensalt()).decode()
        with _sec_lock:
            if "pins" not in security: security["pins"] = {}
            security["pins"][ip] = {"hash": hashed, "type": "pin"}
            _save_security()
        _log_event('pin_set', ip=ip)
    return {'ok': True}


@app.post('/auth/clear_pin')
async def auth_clear_pin(request: Request):
    ip = request.client.host
    with _sec_lock:
        security.get("pins", {}).pop(ip, None)
        _save_security()
    _log_event('pin_cleared', ip=ip)
    return {'ok': True}


# ── Group 2: TOFU — expose cert fingerprint ───────────────────────────────────
def _get_cert_fingerprint():
    cert_file = os.path.join(BASE_DIR, 'cert.pem')
    if not os.path.isfile(cert_file):
        return None
    try:
        import ssl
        with open(cert_file) as f:
            pem = f.read()
        der = ssl.PEM_cert_to_DER_cert(pem)
        raw = hashlib.sha256(der).hexdigest()
        return ':'.join(raw[i:i+2].upper() for i in range(0, len(raw), 2))
    except Exception:
        return None

@app.get('/security/fingerprint')
async def security_fingerprint():
    fp = _get_cert_fingerprint()
    return {'fingerprint': fp, 'https': fp is not None}

@app.get('/scheduled/list')
async def scheduled_list():
    with _sched_lock: return list(scheduled_tasks)

@app.post('/scheduled/save')
async def scheduled_save(request: Request):
    d = await request.json()
    task = {'id': str(int(time.time())), 'name': d.get('name',''), 'time': d.get('time',''),
            'macro': d.get('macro',''), 'enabled': True, 'last_run': ''}
    with _sched_lock: scheduled_tasks.append(task); _save_scheduled(scheduled_tasks)
    return {'ok': True}

@app.post('/scheduled/delete')
async def scheduled_delete(request: Request):
    d   = await request.json()
    tid = d.get('id','')
    with _sched_lock:
        scheduled_tasks[:] = [t for t in scheduled_tasks if t.get('id') != tid]
        _save_scheduled(scheduled_tasks)
    return {'ok': True}

@app.post('/scheduled/toggle')
async def scheduled_toggle(request: Request):
    d   = await request.json()
    tid = d.get('id','')
    with _sched_lock:
        for t in scheduled_tasks:
            if t.get('id') == tid: t['enabled'] = not t.get('enabled', True); break
        _save_scheduled(scheduled_tasks)
    return {'ok': True}


import uvicorn as _uvicorn

class _NoDelayServer(_uvicorn.Server):
    async def startup(self, sockets=None):
        await super().startup(sockets)
        for server in self.servers:
            for sock in server.sockets:
                try:
                    sock.setsockopt(_socket.IPPROTO_TCP, _socket.TCP_NODELAY, 1)
                except Exception:
                    pass


if __name__ == '__main__':
    import argparse

    def _parse_size(s):
        s = s.strip().upper()
        if s.endswith('GB'): return int(float(s[:-2]) * 1024**3)
        if s.endswith('MB'): return int(float(s[:-2]) * 1024**2)
        if s.endswith('KB'): return int(float(s[:-2]) * 1024)
        return int(s)

    parser = argparse.ArgumentParser(prog='portdesk-server', description='PortDesk Server')
    parser.add_argument('-p', '--port',         type=int,   default=5000,      metavar='PORT')
    parser.add_argument('-H', '--host',         type=str,   default='0.0.0.0', metavar='HOST')
    parser.add_argument('-s', '--ssl',          action='store_true')
    parser.add_argument('-c', '--cert',         type=str,   default=None,      metavar='PATH')
    parser.add_argument('-k', '--key',          type=str,   default=None,      metavar='PATH')
    parser.add_argument('--stun',               type=str,   default=None,      metavar='HOST:PORT')
    parser.add_argument('--whitelist',          type=str,   default=None,      metavar='PATH')
    parser.add_argument('--watch-only',         action='store_true')
    parser.add_argument('--no-explorer',        action='store_true')
    parser.add_argument('--upload-limit',       type=str,   default=None,      metavar='SIZE')
    parser.add_argument('--backend',            type=str,   default=None,      choices=['dxcam','mss'])
    parser.add_argument('--no-webrtc',          action='store_true')
    parser.add_argument('--scale',              type=float, default=1.0,       metavar='FACTOR')
    parser.add_argument('--grey',               action='store_true')
    parser.add_argument('--tray',               action='store_true')
    parser.add_argument('--no-mouse',           action='store_true')
    parser.add_argument('--no-keyboard',        action='store_true')
    parser.add_argument('--verbose',            action='store_true')
    args = parser.parse_args()

    import __main__ as _main_mod
    _main_mod.FLAG_WATCH_ONLY   = globals()['FLAG_WATCH_ONLY']   = args.watch_only
    _main_mod.FLAG_NO_EXPLORER  = globals()['FLAG_NO_EXPLORER']  = args.no_explorer
    _main_mod.FLAG_NO_MOUSE     = globals()['FLAG_NO_MOUSE']     = args.no_mouse
    _main_mod.FLAG_NO_KEYBOARD  = globals()['FLAG_NO_KEYBOARD']  = args.no_keyboard
    _main_mod.FLAG_NO_WEBRTC    = globals()['FLAG_NO_WEBRTC']    = args.no_webrtc
    _main_mod.FLAG_GREY         = globals()['FLAG_GREY']         = args.grey
    _main_mod.FLAG_SCALE        = globals()['FLAG_SCALE']        = args.scale
    _main_mod.FLAG_BACKEND      = globals()['FLAG_BACKEND']      = args.backend
    _main_mod.FLAG_VERBOSE      = globals()['FLAG_VERBOSE']      = args.verbose
    if args.upload_limit:
        globals()['FLAG_UPLOAD_LIMIT'] = _parse_size(args.upload_limit)

    if args.whitelist:
        globals()['SECURITY_FILE'] = args.whitelist

    if args.stun and WEBRTC_AVAILABLE:
        from aiortc import RTCIceServer as _RIS
        globals()['STUN_SERVERS'].append(_RIS(urls=[f'stun:{args.stun}']))

    _port = args.port
    _host = args.host

    cert_file = args.cert or os.path.join(BASE_DIR, 'cert.pem')
    key_file  = args.key  or os.path.join(BASE_DIR, 'key.pem')
    use_https = args.ssl or (os.path.isfile(cert_file) and os.path.isfile(key_file))
    if use_https and not (os.path.isfile(cert_file) and os.path.isfile(key_file)):
        print('⚠ --ssl specified but cert/key not found — falling back to HTTP', flush=True)
        use_https = False

    _log_level = 'debug' if args.verbose else 'warning'

    if args.tray:
        try:
            import pystray, PIL.Image as _PIm
            _icon_img = _PIm.new('RGB', (16,16), color=(30, 30, 200))
            def _quit_tray(icon, item): icon.stop(); os._exit(0)
            _tray_icon = pystray.Icon('PortDesk', _icon_img, 'PortDesk',
                                      menu=pystray.Menu(pystray.MenuItem('Quit', _quit_tray)))
            threading.Thread(target=_tray_icon.run, daemon=True).start()
        except ImportError:
            print('⚠ --tray requires pystray and Pillow: pip install pystray Pillow', flush=True)

    try:
        s = _socket.socket(_socket.AF_INET, _socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80)); local_ip = s.getsockname()[0]; s.close()
    except: local_ip = '0.0.0.0'

    proto = 'https' if use_https else 'http'
    print(f"\n{'═'*52}", flush=True)
    print(f"  🎮  PortDesk v1.0 ", flush=True)
    print(f"{'─'*52}", flush=True)
    print(f"  ✍  Developed by  :  Lucky_abdo", flush=True)
    print(f"  🔗  GitHub        :  github.com/Lucky-abdo/PortDesk", flush=True)
    print(f"{'─'*52}", flush=True)
    print(f"  ℹ  WebRTC screen streaming: {'✅ available' if WEBRTC_AVAILABLE and not args.no_webrtc else '⚠️ disabled' if args.no_webrtc else '⚠️ aiortc not installed — WS fallback only'}", flush=True)
    print(f"  ℹ  WebRTC STUN layer      : {'✅ enabled' if WEBRTC_AVAILABLE and not args.no_webrtc else '⚠️ unavailable'}", flush=True)
    _be = 'forced: mss' if args.backend == 'mss' else 'forced: dxcam' if args.backend == 'dxcam' else ('dxcam (DirectX)' if DXCAM_AVAILABLE and platform.system() == 'Windows' else 'mss (fallback)')
    print(f"  ℹ  Screen capture backend : {_be}", flush=True)
    if args.watch_only:   print(f"  ℹ  Mode                   : 👁 Watch-only", flush=True)
    if args.no_explorer:  print(f"  ℹ  File explorer          : ⛔ disabled", flush=True)
    if args.upload_limit: print(f"  ℹ  Upload limit           : {args.upload_limit}", flush=True)
    if args.scale != 1.0: print(f"  ℹ  Stream scale           : {args.scale}x", flush=True)
    if args.grey:         print(f"  ℹ  Stream color           : greyscale", flush=True)
    print(f"{'═'*52}", flush=True)
    print(f"  [USB]  adb reverse tcp:{_port} tcp:{_port} → {proto}://localhost:{_port}", flush=True)
    print(f"  [WiFi] {proto}://{local_ip}:{_port}", flush=True)
    if use_https:
        print(f"  🔒 HTTPS enabled", flush=True)
        _fp = _get_cert_fingerprint()
        if _fp:
            print(f"{'─'*52}", flush=True)
            print(f"  🔐 Cert Fingerprint (SHA-256):", flush=True)
            print(f"  {_fp}", flush=True)
            print(f"  ↑ Verify this matches on your mobile client (TOFU)", flush=True)
    else:
        print(f"{'─'*52}", flush=True)
        print(f"  ⚠⚠⚠  HTTP MODE — TRAFFIC IS UNENCRYPTED  ⚠⚠⚠", flush=True)
        print(f"  Screen stream, keyboard input and clipboard", flush=True)
        print(f"  are visible to anyone on your network.", flush=True)
        print(f"  Run gen_cert.py to enable HTTPS.", flush=True)
    print(f"{'═'*50}\n", flush=True)

    if use_https:
        cfg = _uvicorn.Config(app, host=_host, port=_port,
                              ssl_certfile=cert_file, ssl_keyfile=key_file, log_level=_log_level)
    else:
        cfg = _uvicorn.Config(app, host=_host, port=_port, log_level=_log_level)

    _NoDelayServer(cfg).run()
