"""Professional Windows Updater — single-file GUI application.

Manages updates for winget, Chocolatey, Scoop, npm, pip, Oh My Posh,
Windows Update (PSWindowsUpdate), Windows Store, Windows Terminal,
PowerShell 7, Python, and Clink via a flat-modern tkinter interface.

Entry point: main()  —  requires Windows and administrator privileges.
"""
import os, sys, json, csv, ctypes, shutil, subprocess
import threading, queue, platform, re, copy, tempfile
import itertools, operator, concurrent.futures
import math
import datetime
import time
import tkinter as tk
from tkinter import ttk, filedialog
import logging
from logging.handlers import RotatingFileHandler
from typing import Any, Dict

try:
    import winreg
except ImportError:
    winreg = None  # type: ignore[assignment]

try:
    import pystray
    from PIL import Image as _PILImage
    _TRAY_AVAILABLE = True
except ImportError:
    pystray = None  # type: ignore[assignment]
    _PILImage = None  # type: ignore[assignment]
    _TRAY_AVAILABLE = False

# Use a distinct app version scheme (v-prefix) so it can't be visually
# confused with Python version strings (e.g. "Python 3.9.7") in log output.
VERSION = "v3.21.12"

_BASE_DIR   = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(_BASE_DIR, "updconfig.json")
LOG_FILE    = os.path.join(_BASE_DIR, "updlog.txt")
HIST_FILE   = os.path.join(_BASE_DIR, "updhist.json")
_COMP_COLUMNS = 2  # Number of columns in the component checklist

DEFAULT_CONFIG = {
    "retries": 3,
    "retry_delay": 1,
    "delay_between_components": 0,
    "dry_run": False,
    "debug_mode": False,
    "auto_restart": False,
    "dark_mode": False,
    "auto_health_on_start": True,
    "notify_on_complete": True,
    "restart_confirm_timeout": 30,
    "min_python_version": [3, 9],
    "start_minimised":       False,
    "health_refresh_interval": 0,
    "winget_source_update":    True,    # run winget source update before upgrading
    "winget_include_unknown":  False,   # add --include-unknown to winget upgrade --all
    "pip_skip_editable":       True,    # exclude editable installs from pip upgrades
    "window_w": -1,
    "window_h": -1,
    "window_x": -1,
    "window_y": -1,
    "presets":  {},
    "components": {
        "winget": True,
        "choco": True,
        "scoop": True,
        "npm": True,
        "clink": True,
        "pip": True,
        "oh_my_posh": True,
        "windows_update": True,
        "python": True,
        "windows_store":    True,
        "windows_terminal": True,
        "powershell":       True,
        "ps_modules":       True
    }
}

# _config_load_error is no longer a mutable global. load_config() now
# returns a (config, error_string_or_None) tuple so callers receive the error
# without any cross-thread mutation of module-level state.


def load_config():
    """Load and validate config. Returns (cfg_dict, error_str_or_None)."""
    parse_error = None
    cfg = None
    if not os.path.exists(CONFIG_FILE):
        try:
            validate_config(DEFAULT_CONFIG)
        except ValueError as e:
            raise RuntimeError(f"DEFAULT_CONFIG is invalid: {e}") from e
        save_config(DEFAULT_CONFIG)
        return copy.deepcopy(DEFAULT_CONFIG), None
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            cfg = json.load(f)
    except (json.JSONDecodeError, OSError, UnicodeDecodeError) as e:
        parse_error = str(e)
        print(f"Failed to load config ({e}), using defaults.")

    if cfg is None:
        return copy.deepcopy(DEFAULT_CONFIG), parse_error

    merged = copy.deepcopy(DEFAULT_CONFIG)
    for key, file_val in cfg.items():
        if key not in DEFAULT_CONFIG:
            # Carry forward unrecognised keys to support user-extended configs.
            print(f"Warning: unrecognised config key '{key}' — carrying forward as-is.")
            merged[key] = file_val
            continue
        default_val = DEFAULT_CONFIG[key]
        if key == "components" and isinstance(file_val, dict):
            merged["components"] = DEFAULT_CONFIG["components"].copy()
            merged["components"].update({
                k: v for k, v in file_val.items() if isinstance(v, bool)
            })
        elif key == "min_python_version":
            if (isinstance(file_val, list) and len(file_val) >= 2
                    and all(isinstance(x, int) and not isinstance(x, bool) for x in file_val)):
                merged[key] = file_val
        elif isinstance(default_val, bool):
            if isinstance(file_val, bool):
                merged[key] = file_val
        elif isinstance(default_val, (int, float)):
            if not isinstance(file_val, bool) and isinstance(file_val, (int, float)):
                merged[key] = file_val
        else:
            merged[key] = file_val

    try:
        validate_config(merged)
    except ValueError as e:
        print(f"Config validation error: {e}. Using defaults.")
        # Overwrite the invalid config with known-good defaults so the next
        # launch loads cleanly instead of falling back every time.
        # save_config() makes a .bak copy first, so the original is preserved.
        save_config(DEFAULT_CONFIG)
        return copy.deepcopy(DEFAULT_CONFIG), None
    return merged, None


def save_config(cfg):
    """Atomically write cfg to CONFIG_FILE via a temp file + os.replace()."""
    tmp_path = None
    try:
        cfg_dir = os.path.dirname(CONFIG_FILE) or "."
        # Back up the existing config before overwriting.
        if os.path.exists(CONFIG_FILE):
            try:
                shutil.copy2(CONFIG_FILE, CONFIG_FILE + ".bak")
            except OSError:
                pass  # backup failure is non-fatal
        with tempfile.NamedTemporaryFile(
            "w", dir=cfg_dir, delete=False, suffix=".tmp", encoding="utf-8"
        ) as f:
            json.dump(cfg, f, indent=4)
            tmp_path = f.name
        os.replace(tmp_path, CONFIG_FILE)
    except (OSError, TypeError) as e:
        print(f"Warning: could not save config ({e}).")
        if tmp_path:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass


# Keys that must be present in every config dict passed to validate_config().
# Tuple preserves definition order for deterministic "missing key" error messages.
_CONFIG_REQUIRED_KEYS: tuple = (
    'retries', 'retry_delay', 'delay_between_components',
    'dry_run', 'debug_mode', 'auto_restart', 'components',
    'min_python_version', 'restart_confirm_timeout',
    'start_minimised', 'health_refresh_interval',
    'window_w', 'window_h', 'window_x', 'window_y', 'presets',
    'winget_source_update', 'winget_include_unknown', 'pip_skip_editable',
)

# Numeric config bounds: key → (min_inclusive, max_inclusive).
# retry_delay=0 creates a tight CPU loop (0 * 2^n == 0 always).
_CONFIG_BOUNDS: dict = {
    "retries":                  (1,   20),
    "retry_delay":              (1,  300),
    "delay_between_components": (0,  600),
    "restart_confirm_timeout":  (5,  300),
    "health_refresh_interval":  (0, 3600),
}


def validate_config(cfg):
    """Raise ValueError if cfg is missing required keys or has out-of-range values."""
    for key in _CONFIG_REQUIRED_KEYS:
        if key not in cfg:
            raise ValueError(f"Missing required key in config: {key}")
    if not isinstance(cfg["components"], dict):
        raise ValueError("Components section should be a dictionary.")
    if not isinstance(cfg["presets"], dict):
        raise ValueError("'presets' must be a dictionary.")
    for comp, val in cfg["components"].items():
        if not isinstance(val, bool):
            raise ValueError(
                f"Invalid value for component '{comp}': expected bool, got {type(val).__name__}."
            )
    mpv = cfg["min_python_version"]
    if (
        not isinstance(mpv, list)
        or len(mpv) < 2
        or not all(isinstance(x, int) and not isinstance(x, bool) for x in mpv)
    ):
        raise ValueError("min_python_version must be a list of two plain integers, e.g. [3, 9].")

    for key, (min_val, max_val) in _CONFIG_BOUNDS.items():
        val = cfg[key]
        if isinstance(val, bool) or not isinstance(val, (int, float)):
            raise ValueError(f"'{key}' must be a number, got {val!r}.")
        if val < min_val:
            raise ValueError(f"'{key}' must be >= {min_val}, got {val!r}.")
        if val > max_val:
            raise ValueError(f"'{key}' must be <= {max_val}, got {val!r}.")

# ---------------------------------------------------------------------------
# PowerShell resolver — prefers latest (pwsh / PS 7+) over legacy (PS 5).
# Called once by detect_components() and cached in components["windows_update"].
# ---------------------------------------------------------------------------
def _find_powershell() -> str:
    """Return the path to the best available PowerShell executable.

    Search order:
      1. pwsh on PATH — PowerShell 7+ (PATHEXT resolves .exe automatically)
      2. %ProgramFiles%\\PowerShell\\<N>\\pwsh.exe — versioned side-by-side
         installs, sorted by major version descending (e.g. 7.4 beats 7.2)
      3. powershell.exe — Windows PowerShell 5 (always present on Win10/11)
      4. Hard-coded "powershell" — last-resort if PATH is broken.
    """
    # Fast path: pwsh on PATH (most common for PS7+ installs).
    # "pwsh.exe" is intentionally omitted — on Windows, PATHEXT means
    # shutil.which("pwsh") already resolves to pwsh.exe. The slow-path
    # scan handles versioned side-by-side installs that are not on PATH.
    found = shutil.which("pwsh")
    if found:
        return found

    # Slow path: scan %ProgramFiles%\PowerShell for versioned installs.
    # Typical layout: C:\Program Files\PowerShell\7\pwsh.exe
    pf = os.getenv("ProgramFiles") or os.path.join("C:\\", "Program Files")
    ps_root = os.path.join(pf, "PowerShell")
    if os.path.isdir(ps_root):
        versioned: list = []
        try:
            for entry in os.scandir(ps_root):
                if not entry.is_dir():
                    continue
                exe = os.path.join(entry.path, "pwsh.exe")
                if os.path.isfile(exe):
                    # Extract leading integer version for sort key.
                    try:
                        ver = int(entry.name.split(".")[0])
                    except ValueError:
                        ver = 0
                    versioned.append((ver, exe))
        except OSError:
            pass
        if versioned:
            versioned.sort(key=lambda t: t[0], reverse=True)
            return versioned[0][1]

    # Final fallback: Windows PowerShell 5 (powershell.exe).
    return shutil.which("powershell") or "powershell"


#==================== ADMIN =====================
def is_admin():
    """Return True if the current process has administrator privileges."""
    try:
        return ctypes.windll.shell32.IsUserAnAdmin()
    except Exception:
        return False


def elevate():
    """Re-launch the current script with UAC elevation (runas) and exit."""
    exe = sys.executable
    if getattr(sys, "frozen", False):
        parts = [f'"{a}"' for a in sys.argv[1:]]
    else:
        script = os.path.abspath(sys.argv[0])
        parts  = [f'"{script}"'] + [f'"{a}"' for a in sys.argv[1:]]
    params = " ".join(parts) if parts else None
    ret = ctypes.windll.shell32.ShellExecuteW(None, "runas", exe, params, None, 1)
    if ret <= 32:
        # Elevation failed — notify the user then fall through to sys.exit().
        ctypes.windll.user32.MessageBoxW(
            0,
            f"Failed to re-launch with administrator privileges (error code {ret}).\n"
            "Try running the application manually as Administrator.",
            "Elevation Failed",
            0x10,
        )
    # Both success and failure paths exit the non-elevated process; the elevated
    # child (if launched) takes over from here.
    sys.exit()

#==================== LOGGER =====================
# Logger is configured at module level but the file handler is attached
# inside main() after the platform check, so updlog.txt is never created on
# non-Windows systems. The logger object itself is safe to create here because
# it only writes to attached handlers — of which there are none until main().
logger = logging.getLogger("Updater")
logger.setLevel(logging.DEBUG)

# Pre-built log queue prefix strings — avoids tag.upper() + f-string
# construction on every engine.log() call (hot path: thousands per run).
_LOG_QUEUE_PREFIX: dict = {
    "debug": "[DEBUG] ",
    "info":  "[INFO] ",
    "warn":  "[WARN] ",
    "error": "[ERROR] ",
}
# Pre-built logger dispatch — avoids getattr(logger, level) per call.
_LOG_DISPATCH: dict = {
    "debug": logger.debug,
    "info":  logger.info,
    "warn":  logger.warning,
    "error": logger.error,
}

# Platform-safe kwargs dict for subprocess calls — suppresses CMD console
# window flashes on Windows. Applied to every subprocess.run / Popen call.
_NO_WINDOW = ({"creationflags": subprocess.CREATE_NO_WINDOW}
              if platform.system() == "Windows" else {})

#==================== COLOUR HELPERS =====================
_ANSI_RE = re.compile(
    r"\x1b(?:"
    r"\[[0-9;?]*[a-zA-Z]"
    r"|\][^\x07\x9c]*(?:\x07|\x9c|\x1b\\)"
    r")"
    r"|\x9c"
)


def _fmt_cmd(command):
    """Format a command list (or string) as a readable shell-style string for logging."""
    if isinstance(command, list):
        return " ".join(map(str, command))  # map avoids intermediate list allocation
    return str(command)


def strip_ansi(text):
    """Remove ANSI/VT escape sequences from a string.

    Fast-path when the string contains no escape sequences — skips
    the regex engine entirely for the common case.
    """
    if "\x1b" not in text and "\x9c" not in text:
        return text.strip()
    return _ANSI_RE.sub("", text).strip()

#==================== UPDATE ENGINE =====================
_PIP_UPGRADE_TIMEOUT             = 300
_PIP_LIST_TIMEOUT                = 60
_WINDOWS_UPDATE_TIMEOUT          = 3600
_WINDOWS_UPDATE_SCAN_TIMEOUT     = 120
_WINSTORE_BULK_TIMEOUT           = 300
_WINSTORE_PKG_TIMEOUT            = 120
_WINSTORE_SCAN_TIMEOUT           = 60
_PSWINDOWSUPDATE_CHECK_TIMEOUT   = 30
_PSWINDOWSUPDATE_INSTALL_TIMEOUT = 120
_HEALTH_VER_TIMEOUT              = 10
_PROBE_DEADLINE: int             = _HEALTH_VER_TIMEOUT + 5  # future.result() budget per probe
_DETECT_PIP_TIMEOUT              = 10
# _DETECT_PYTHON_TIMEOUT was removed: python detection uses shutil.which()
# which has no timeout — no subprocess call is made.
_PY_INSTALLER_TIMEOUT            = 600   # 10 min — official Python.org installer
_RUN_COMMAND_DEFAULT_TIMEOUT     = 30

# Long-running package-manager commands need their own generous
# timeouts. A full "upgrade --all" across many packages can take 20-30 minutes.
_WINGET_UPGRADE_TIMEOUT          = 3600   # 1 hour
_CHOCO_UPGRADE_TIMEOUT           = 3600
_SCOOP_UPGRADE_TIMEOUT           = 3600
_NPM_UPGRADE_TIMEOUT             = 600    # 10 minutes
# oh-my-posh upgrade downloads a new binary; 30 s is never enough.
_OH_MY_POSH_UPGRADE_TIMEOUT      = 300    # 5 minutes
# winget-based upgrades download full MSIX/MSI installers; 30 s default
# is far too short even on fast connections once the install phase runs.
_WINDOWS_TERMINAL_UPGRADE_TIMEOUT = 300   # 5 minutes
_POWERSHELL_UPGRADE_TIMEOUT       = 300   # 5 minutes
_PS_MODULES_UPGRADE_TIMEOUT       = 600   # 10 minutes — gallery downloads can be slow
_DETECT_WT_TIMEOUT                = 15    # winget list for install-track detection
# Windows Terminal ships on two tracks; the correct upgrade command
# depends on which one is installed.  Store the IDs here so they are
# easy to find and update if Microsoft ever changes them.
_WT_WINGET_ID   = "Microsoft.WindowsTerminal"   # winget source track
_WT_MSSTORE_ID  = "9N0DX20HK701"                # Microsoft Store track (Win11 default)
_PS7_WINGET_ID  = "Microsoft.PowerShell"        # PS7 — winget source only


class UpdateEngine:
    def __init__(self, config, gui_queue=None):
        self.config            = config
        self.config_lock       = threading.Lock()
        self.gui_queue         = gui_queue
        self.stop_event        = threading.Event()
        # Dedicated stop event for health checks so that
        # run_selected()'s stop_event.clear() never silently un-cancels a
        # concurrent health probe, and populate_health's clear() never
        # interferes with a running update.
        self._health_stop_event = threading.Event()
        self.components        = {}
        self._components_ready = threading.Event()
        self._error_lock       = threading.Lock()
        self._error_count      = 0
        self._run_active       = False
        self._rebooting        = False
        # Set just before confirm_restart is queued so the GUI's priority
        # drain only runs on ticks where a reboot dialog is actually pending.
        self._confirm_restart_pending = threading.Event()
        # Track the active subprocess so cancel() can terminate it
        # immediately instead of waiting for a blocking subprocess.run to return.
        self._active_proc: "subprocess.Popen | None" = None
        self._proc_lock = threading.Lock()
        # Cached debug_mode flag — avoids config.get() on every log() call.
        self._debug_mode: bool = bool(config.get("debug_mode", False))
        # Cached notify_on_complete — read by update_gui on every run_complete.
        self._notify_on_complete: bool = bool(config.get("notify_on_complete", True))
        # Last-run failure set — populated by _run_selected_inner so the GUI
        # can offer a "Retry Failed" button.
        self._last_failed: list = []
        # Cached reboot-pending result — written by is_reboot_pending() on the
        # engine thread.  The GUI reads this cached bool instead of calling
        # is_reboot_pending() directly, which would block the GUI thread with
        # registry OpenKey() calls (slow under AV / group-policy enforcement).
        self._reboot_pending_cache: bool = False

    def probe_components(self):
        """Run detect_components in a background thread and signal readiness."""
        _gq = self.gui_queue  # bind once for the completion put()
        try:
            self.components = self.detect_components()
        except Exception as e:
            logger.exception("Component detection failed")
            # use self.config["components"] keys so user-added components
            # are included in the fallback rather than only DEFAULT_CONFIG keys.
            with self.config_lock:
                component_keys = self.config.get("components", DEFAULT_CONFIG["components"])
            self.components = {
                name: {"available": False, "path": None}
                for name in component_keys
            }
        self._components_ready.set()
        if _gq:
            _gq.put(("components_ready", self.components))

    def log(self, message, level="info"):
        """Log a message at the given level and forward it to the GUI queue."""
        # Fast-path: direct lookup for lowercase tags (the common case).
        # Fallback via .lower() handles the rare "warning" alias.
        tag = _LEVEL_MAP.get(level) or _LEVEL_MAP.get(level.lower(), "info")
        if tag == "error":
            with self._error_lock:
                if self._run_active:
                    self._error_count += 1
        # Build the prefixed line once — reused for queue and optional print.
        _line = _LOG_QUEUE_PREFIX[tag] + message
        # Bind once — avoids 3 LOAD_ATTR per call on the hottest engine path.
        _gq = self.gui_queue
        if _gq:
            _gq.put(("log", _line))
        # pre-built dispatch dict — no getattr() per call.
        _LOG_DISPATCH[tag](message)
        if self._debug_mode:
            print(_line)

    def cancel(self):
        """Signal the engine to stop and terminate any active subprocess."""
        # Log a more specific message depending on whether an update run is active.
        if self._run_active:
            self.log("Update process cancelled by user.", "warn")
        else:
            self.log("Operation cancelled.", "warn")
        self.stop_event.set()
        # Also cancel any running health check.
        self._health_stop_event.set()
        # Terminate any blocking subprocess immediately so the user
        # doesn't wait up to the full timeout (e.g. 3600 s for winget) after
        # pressing Cancel.
        with self._proc_lock:
            if self._active_proc is not None:
                try:
                    self._active_proc.terminate()
                except OSError:
                    pass

    def run_command(self, command, timeout=_RUN_COMMAND_DEFAULT_TIMEOUT,
                   success_output: "frozenset | None" = None,
                   retries: "int | None" = None):
        """Run a subprocess with retries, logging, and cancellation support.

        retries=None uses the value from config; pass an explicit int to
        override (e.g. retries=1 for best-effort one-shot commands).
        """
        _log  = self.log         # saves LOAD_ATTR on each of 9 log() calls
        _stop = self.stop_event  # saves LOAD_ATTR on each of 4 stop checks
        with self.config_lock:
            dry_run       = self.config.get("dry_run", False)
            debug_mode    = self.config.get("debug_mode", False)
            _cfg_retries  = self.config["retries"]
            initial_delay = self.config["retry_delay"]
        retries = retries if retries is not None else _cfg_retries
        self._debug_mode = debug_mode   # refresh cache for log() hot path

        # Format command once — reused across dry-run, debug, error, and
        # timeout log messages (up to 5× per invocation).
        _cmd_str = _fmt_cmd(command)
        if dry_run:
            _log(f"[DRY RUN] Would execute: {_cmd_str}", "debug")
            return True

        for attempt in range(1, retries + 1):
            if _stop.is_set():
                return False
            try:
                if debug_mode:
                    _log(f"Executing: {_cmd_str}", "debug")
                # Popen+communicate allows cancel() to terminate immediately.
                # No timeout on Popen itself — budget is on communicate().
                with subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    **_NO_WINDOW,
                ) as proc:
                    with self._proc_lock:
                        self._active_proc = proc
                    # Close the race: if cancel() fired between Popen() and
                    # the assignment above, stop_event is set but terminate()
                    # was called on None. Catch it here before blocking on
                    # communicate().
                    if _stop.is_set():
                        try:
                            proc.terminate()
                        except OSError:
                            pass
                        return False
                    try:
                        try:
                            stdout_data, stderr_data = proc.communicate(timeout=timeout)
                        except subprocess.TimeoutExpired:
                            proc.terminate()
                            try:
                                stdout_data, stderr_data = proc.communicate(timeout=5)
                            except subprocess.TimeoutExpired:
                                proc.kill()
                                # Bound the post-kill drain — orphaned child
                                # processes may keep the pipe open after kill.
                                try:
                                    stdout_data, stderr_data = proc.communicate(timeout=10)
                                except subprocess.TimeoutExpired:
                                    if proc.stdout: proc.stdout.close()
                                    if proc.stderr: proc.stderr.close()
                                    stdout_data, stderr_data = "", ""
                            raise
                    finally:
                        with self._proc_lock:
                            self._active_proc = None
                result_returncode = proc.returncode
                # strip ANSI colour codes — winget/choco/npm emit ESC[...m
                # progress sequences that appear as raw garbage in the log widget.
                for line in stdout_data.splitlines():
                    stripped = strip_ansi(line)
                    if stripped:
                        _log(stripped)
                # Only escalate stderr to 'warn' when the command
                # actually failed. Many tools (winget, choco, npm) write
                # progress/info to stderr even on success, which caused
                # misleading orange colouring in the GUI.
                stderr_level = "warn" if result_returncode != 0 else "debug"
                for line in stderr_data.splitlines():
                    stripped = strip_ansi(line)
                    if stripped:
                        _log(stripped, stderr_level)
                if result_returncode == 0:
                    return True
                # success_output: non-zero exits that indicate "nothing to do"
                # (e.g. winget 0x8A15002B = "No applicable update found.").
                # Treat as quiet success — no retry, no red error in the log.
                # Check both stdout and stderr — some winget builds write the
                # "no update" message to stderr when stdout is redirected.
                if success_output and any(
                        s in stdout_data or s in stderr_data
                        for s in success_output):
                    return True
                # Check stop before logging the failure or scheduling a
                # retry — cancel() terminates the process which causes a
                # non-zero exit, and we must not retry a cancelled run.
                if _stop.is_set():
                    return False
                _log(
                    f"Command exited with code {result_returncode} "
                    f"(attempt {attempt}/{retries}): {_cmd_str}",
                    "warn",
                )
            except subprocess.TimeoutExpired:
                # Use 'warn' on non-final attempts so a red error isn't
                # shown for a timeout that is immediately retried successfully.
                # Only escalate to 'error' on the final attempt.
                timeout_level = "error" if attempt == retries else "warn"
                _log(f"Command timed out after {timeout}s: {_cmd_str}", timeout_level)
                # return immediately on the final attempt to avoid the
                # redundant "failed after N retries" message below.
                if attempt == retries:
                    return False
            except Exception as e:
                _log(f"Error running command: {e}", "error")

            if attempt < retries:
                if _stop.is_set():
                    return False
                next_delay = min(initial_delay * (2 ** (attempt - 1)), 300)
                _log(f"Retrying in {next_delay} s…  (attempt {attempt} of {retries})", "warn")
                if _stop.wait(timeout=next_delay):
                    return False

        _retry_word = "retry" if retries == 1 else "retries"
        _log(f"Command failed after {retries} {_retry_word}: {_cmd_str}", "error")
        return False

    def detect_components(self):
        """Probe the system for all supported tools and return a components dict."""
        comps: Dict[str, Any] = {}

        # Pass 1: everything except windows_store
        for name in _DETECT_PASS1_NAMES:
            exe = None
            if name == "windows_update":
                exe = _find_powershell()
            elif name == "clink":
                exe = self.detect_clink()
            elif name == "oh_my_posh":
                exe = shutil.which("oh-my-posh") or shutil.which("oh-my-posh.exe")
            elif name == "python":
                exe = shutil.which("python") or shutil.which("python3")
            elif name == "pip":
                try:
                    r = subprocess.run(
                        [sys.executable, "-m", "pip", "--version"],
                        capture_output=True, text=True, encoding="utf-8",
                        errors="replace", timeout=_DETECT_PIP_TIMEOUT,
                        **_NO_WINDOW,
                    )
                    exe = sys.executable if r.returncode == 0 else None
                except Exception:
                    exe = None
            else:
                exe = shutil.which(name)
            comps[name] = {"available": exe is not None, "path": exe}

        # Pass 2: windows_store, windows_terminal, and powershell all
        # use the winget path from Pass 1 for their upgrade commands.
        winget_info = comps.get("winget", {})
        ws_exe = winget_info.get("path") if winget_info.get("available") else None
        comps["windows_store"] = {"available": ws_exe is not None, "path": ws_exe}

        # ── Windows Terminal ──────────────────────────────────────────────────
        # Availability is gated on wt.exe being on PATH (put there by the
        # installer regardless of track).  When WT is present we also probe
        # which install track is active so the upgrade command uses the
        # correct package ID and source:
        #   winget track → id Microsoft.WindowsTerminal  --source winget
        #   Store  track → id 9N0DX20HK701               --source msstore
        # (Windows 11 ships WT pre-installed from the Store; users who
        # installed it manually via winget get the winget track.)
        wt_installed = shutil.which("wt") is not None
        wt_id     = None   # set below when wt_installed and ws_exe
        wt_source = None
        if wt_installed and ws_exe:
            try:
                _wt_list = subprocess.run(
                    [ws_exe, "list", "--id", _WT_WINGET_ID,
                     "--source", "winget",
                     "--accept-source-agreements"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=_DETECT_WT_TIMEOUT,
                    **_NO_WINDOW,
                )
                # winget list exits 0 and prints the package row when found.
                # A simple substring check is sufficient — no regex needed.
                if _WT_WINGET_ID in _wt_list.stdout:
                    wt_id, wt_source = _WT_WINGET_ID, "winget"
                else:
                    # Not in winget source → installed from the Store.
                    wt_id, wt_source = _WT_MSSTORE_ID, "msstore"
            except Exception:
                # Detection failed — default to winget track (safer: winget
                # upgrade is a no-op when the package is already up-to-date).
                wt_id, wt_source = _WT_WINGET_ID, "winget"
        comps["windows_terminal"] = {
            "available": ws_exe is not None and wt_installed,
            "path":      ws_exe,     # winget executable path
            "wt_id":     wt_id,      # correct package ID for upgrade
            "wt_source": wt_source,  # "winget" or "msstore"
        }

        # ── PS Modules ───────────────────────────────────────────────────────
        # Always available when any PowerShell executable is present.
        # Uses the windows_update path (best PS available: pwsh or powershell).
        comps["ps_modules"] = {
            "available": True,              # powershell.exe is always present on Win10/11
            "path":      comps.get("windows_update", {}).get("path") or "powershell",
        }

        # ── PowerShell 7 ──────────────────────────────────────────────────────
        # pwsh.exe on PATH confirms PS7 is installed. PS7 is winget-source
        # only (no msstore variant) so no track detection is needed.
        _pwsh_path    = shutil.which("pwsh")   # cached once; reused by _probe_one
        ps7_installed = _pwsh_path is not None
        comps["powershell"] = {
            "available":  ws_exe is not None and ps7_installed,
            "path":       ws_exe,       # winget executable (for upgrade)
            "pwsh_path":  _pwsh_path,   # pwsh binary (for version probe)
        }

        return comps

    def detect_clink(self):
        """Return the path to clink.bat if Clink is installed, else None."""
        pf   = os.getenv("ProgramFiles")      or os.path.join("C:\\", "Program Files")
        pf86 = os.getenv("ProgramFiles(x86)") or os.path.join("C:\\", "Program Files (x86)")
        candidates = [
            shutil.which("clink.bat"),
            os.path.join(pf,   "clink", "clink.bat"),
            os.path.join(pf86, "clink", "clink.bat"),
        ]
        for p in candidates:
            if p and os.path.isfile(p):
                return p
        return None

    #==================== COMPONENT UPDATES =====================
    def update_python(self):
        """Upgrade Python using the official Python.org installer via winget.

        Detection uses the `py` launcher (py.exe) to list installed versions.
        Upgrade is performed by winget, which downloads and runs the official
        Python.org installer silently in the background.

        Steps:
          1. Use `py --list` to log all currently installed Python versions.
          2. Use winget to upgrade to the latest Python 3 (official installer).
        """
        _log  = self.log
        _stop = self.stop_event

        with self.config_lock:
            dry_run = self.config.get("dry_run", False)

        # ── Step 1: Report installed versions via py launcher ─────────────
        _py = shutil.which("py")
        if _py:
            _log("Installed Python versions (py launcher):")
            try:
                _r = subprocess.run(
                    [_py, "--list"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=10, **_NO_WINDOW,
                )
                for _line in (_r.stdout or _r.stderr).splitlines():
                    _s = strip_ansi(_line).strip()
                    if _s:
                        _log(f"  {_s}")
            except Exception as _e:
                _log(f"py --list failed: {_e}", "warn")
        else:
            _log("py launcher not found — install Python from python.org to get it.", "warn")

        if _stop.is_set():
            return

        # ── Step 2: Upgrade via winget (official Python.org installer) ────
        winget_info = self.components.get("winget", {})
        if not winget_info.get("available") or not winget_info.get("path"):
            _log("winget not available — download the latest installer from https://www.python.org/downloads/", "warn")
            return

        _wg = winget_info["path"]

        # winget uses the official Python.org installer package.
        # Python.Python.3 matches the latest stable Python 3.x release.
        if dry_run:
            _log("[DRY RUN] Would run: winget upgrade Python.Python.3 --source winget", "debug")
            return

        _log("Upgrading Python to latest stable 3.x via winget (official Python.org installer)…")
        self.run_command(
            [_wg, "upgrade", "Python.Python.3",
             "--source", "winget",
             "--accept-source-agreements", "--accept-package-agreements"],
            timeout=_PY_INSTALLER_TIMEOUT,
            success_output=_WINGET_NO_UPDATE_PHRASES,
        )
        _log("Python upgrade completed.")
    # Known packaging infrastructure packages that can break the
    # environment if upgraded mid-run. We log a warning instead of silently
    # upgrading them.
    _PIP_INFRA_PACKAGES = frozenset({"pip", "setuptools", "wheel", "distlib", "packaging"})

    def update_pip(self):
        """Upgrade all outdated pip packages, warning on infrastructure packages."""
        _log  = self.log        # 11 calls — saves 10 LOAD_ATTRs
        _stop = self.stop_event
        if _stop.is_set():
            return
        _log("Checking outdated pip packages…")
        with self.config_lock:
            _skip_editable = self.config.get("pip_skip_editable", True)
        _pip_list_cmd = [
            sys.executable, "-m", "pip", "list", "--outdated", "--format=json"
        ]
        if _skip_editable:
            _pip_list_cmd.append("--exclude-editable")
        try:
            result = subprocess.run(
                _pip_list_cmd,
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=_PIP_LIST_TIMEOUT, **_NO_WINDOW,
            )
            if result.returncode != 0:
                _log(f"pip list exited with code {result.returncode} — pip upgrades skipped.", "error")
                # strip_ansi removes ANSI codes pip can emit on stderr.
                _pip_err = strip_ansi(result.stderr)
                if _pip_err:
                    _log(_pip_err, "warn")
                return
            raw = result.stdout.strip()
            if not raw:
                _log("pip returned no output — pip upgrades skipped.", "warn")
                return
            # Locate both the opening '[' and the matching closing ']'
            # so that any warning text pip emits after the JSON array (e.g.
            # deprecation notices) is excluded before parsing.
            json_start = raw.find("[")
            json_end   = raw.rfind("]")
            if json_start == -1 or json_end == -1 or json_end < json_start:
                _log("pip output contained no JSON array — pip upgrades skipped.", "warn")
                return
            packages = json.loads(raw[json_start:json_end + 1])
        except subprocess.TimeoutExpired:
            _log("pip list timed out.", "error")
            return
        except json.JSONDecodeError:
            _log("pip output could not be parsed as JSON — pip upgrades skipped.", "error")
            return
        if not packages:
            _log("All pip packages are up-to-date.")
            return
        for pkg in packages:
            if _stop.is_set():
                return
            pkg_name = pkg.get("name", "")
            if not pkg_name:
                _log("Skipping pip entry with missing 'name' field.", "warn")
                continue
            if pkg_name.lower() in self._PIP_INFRA_PACKAGES:
                _log(
                    f"Upgrading packaging infrastructure package '{pkg_name}' "
                    f"({pkg.get('version', '?')} -> {pkg.get('latest_version', '?')}). "
                    "If the environment breaks afterward, re-install requirements.",
                    "warn",
                )
            else:
                _log(f"Upgrading pip package: {pkg_name} ({pkg.get('version', '?')} -> {pkg.get('latest_version', '?')})")
            self.run_command(
                [sys.executable, "-m", "pip", "install", "--upgrade", pkg_name],
                timeout=_PIP_UPGRADE_TIMEOUT,
            )

    def update_windows_store(self):
        """Update Windows Store apps via winget, with per-package dry-run support."""
        _log  = self.log        # 15 calls — saves 14 LOAD_ATTRs
        _stop = self.stop_event
        _log("Checking Windows Store apps for updates…")
        ws_info = self.components.get("windows_store", {})
        winget  = ws_info.get("path") if ws_info.get("available") else None
        if not winget:
            _log("Winget not found, cannot update Windows Store apps.", "error")
            return

        with self.config_lock:
            dry_run = self.config.get("dry_run", False)
        if dry_run:
            _log("[DRY RUN] Scanning Windows Store apps (read-only — no upgrades will run)…", "debug")

        try:
            list_result = subprocess.run(
                [winget, "list", "--source", "msstore",
                 "--accept-source-agreements"],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=_WINSTORE_SCAN_TIMEOUT, **_NO_WINDOW,
            )
            packages = []
            _json_ok = False
            try:
                stdout      = list_result.stdout
                pos_brace   = stdout.find('{')
                pos_bracket = stdout.find('[')
                candidates  = [p for p in (pos_brace, pos_bracket) if p != -1]
                json_start  = min(candidates) if candidates else -1
                if json_start != -1:
                    # Find the matching close delimiter — trailing winget
                    # output (progress bars, consent text) is excluded.
                    close_char = ']' if stdout[json_start] == '[' else '}'
                    json_end = stdout.rfind(close_char)
                    json_slice = (stdout[json_start:json_end + 1]
                                  if json_end > json_start
                                  else stdout[json_start:])
                    raw = json.loads(json_slice)
                    _json_ok = True
                    _log(f"Windows Store: winget list JSON type: {type(raw).__name__}", "debug")
                    if isinstance(raw, list):
                        packages = [p for p in raw if p.get("Available")]
                    elif isinstance(raw, dict):
                        for source in raw.get("Sources", []):
                            packages.extend(
                                p for p in source.get("Packages", [])
                                if p.get("Available")
                            )
                    else:
                        _log(
                            "Windows Store: winget list returned unexpected JSON type "
                            f"'{type(raw).__name__}' — falling back to bulk upgrade.",
                            "debug",
                        )
                        _json_ok = False
            except json.JSONDecodeError:
                pass

            if not _json_ok:
                if dry_run:
                    _log("[DRY RUN] Could not parse Windows Store package list — would fall back to bulk upgrade.", "debug")
                    return
                _log(
                    "Windows Store: winget list returned no parseable JSON "
                    f"(exit {list_result.returncode}) — falling back to bulk upgrade.",
                    "debug",
                )
                self.run_command(
                    [winget, "upgrade", "--all", "--source", "msstore",
                     "--accept-source-agreements", "--accept-package-agreements"],
                    timeout=_WINSTORE_BULK_TIMEOUT,
                    success_output=_WINGET_NO_UPDATE_PHRASES,
                )
                _log("Windows Store apps update completed.")
                return

            if not packages:
                _log("Windows Store: all apps are up-to-date.")
                return

            _log(f"Windows Store: {len(packages)} app(s) have updates available.")
            for pkg in packages:
                if _stop.is_set():
                    return
                pkg_id = pkg.get("Id") or pkg.get("PackageIdentifier")
                if not pkg_id:
                    continue
                name     = pkg.get("Name", "Unknown")
                cur_ver  = pkg.get("Version", "?")
                new_ver  = pkg.get("Available", "?")
                # dry_run now reaches here after scanning so the
                # user can see exactly which packages would be upgraded.
                if dry_run:
                    _log(f"[DRY RUN] Would upgrade: {name} ({cur_ver} -> {new_ver})", "debug")
                    continue
                _log(f"Updating Windows Store app: {name} ({cur_ver} -> {new_ver})")
                self.run_command(
                    [winget, "upgrade", "--id", pkg_id, "--source", "msstore",
                     "--accept-source-agreements", "--accept-package-agreements"],
                    timeout=_WINSTORE_PKG_TIMEOUT,
                )
            _log("Windows Store apps update completed." if not dry_run else "[DRY RUN] Windows Store scan complete.")
        except subprocess.TimeoutExpired:
            _log("Winget Windows Store list scan timed out.", "error")
        except (subprocess.SubprocessError, OSError, ValueError) as e:
            _log(f"Failed to update Windows Store apps: {e}", "error")

    def _ensure_pswindowsupdate(self):
        """Verify PSWindowsUpdate is installed; force-install if not."""
        _log  = self.log        # 13 calls — saves 12 LOAD_ATTRs
        _stop = self.stop_event
        ps = self.components.get("windows_update", {}).get("path") or "powershell"

        with self.config_lock:
            dry_run = self.config.get("dry_run", False)
        if dry_run:
            _log("[DRY RUN] Would ensure PSWindowsUpdate module is installed.", "debug")
            return True

        if _stop.is_set():
            return False
        _log("Checking for PSWindowsUpdate module…", "debug")
        try:
            chk = subprocess.run(
                [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command",
                 "if (Get-Module -ListAvailable -Name PSWindowsUpdate) { exit 0 } else { exit 1 }"],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=_PSWINDOWSUPDATE_CHECK_TIMEOUT, **_NO_WINDOW,
            )
            if chk.returncode == 0:
                _log("PSWindowsUpdate module is installed.", "debug")
                return True
            _log("PSWindowsUpdate module not found — will attempt installation.", "debug")
        except subprocess.TimeoutExpired:
            _log("PSWindowsUpdate presence check timed out.", "error")
            return False
        except Exception as e:
            _log(f"PSWindowsUpdate presence check error: {e}", "error")
            return False

        if _stop.is_set():
            return False
        _log("PSWindowsUpdate not found — installing from PSGallery (this may take ~30 s)…", "warn")
        install_script = (
            "[Net.ServicePointManager]::SecurityProtocol = "
            "[Net.SecurityProtocolType]::Tls12; "
            "Install-Module -Name PSWindowsUpdate "
            "-Force -SkipPublisherCheck -Scope CurrentUser -ErrorAction Stop"
        )
        try:
            inst = subprocess.run(
                [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", install_script],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=_PSWINDOWSUPDATE_INSTALL_TIMEOUT, **_NO_WINDOW,
            )
            for line in inst.stdout.splitlines():
                # strip_ansi handles ANSI codes from PSGallery output.
                stripped = strip_ansi(line)
                if stripped:
                    _log(stripped, "debug")
            for line in inst.stderr.splitlines():
                stripped = strip_ansi(line)
                if stripped:
                    _log(stripped, "warn")
            if inst.returncode == 0:
                _log("PSWindowsUpdate installed successfully.")
                return True
            _log(
                f"PSWindowsUpdate install failed (exit {inst.returncode}) — "
                "check execution policy and internet access.",
                "error",
            )
            return False
        except subprocess.TimeoutExpired:
            _log("PSWindowsUpdate installation timed out after 120 s.", "error")
            return False
        except Exception as e:
            _log(f"PSWindowsUpdate installation error: {e}", "error")
            return False

    def update_windows(self):
        """Install pending Windows updates using PSWindowsUpdate."""
        _log  = self.log        # 11 calls — saves 10 LOAD_ATTRs
        _stop = self.stop_event
        ps = self.components.get("windows_update", {}).get("path") or "powershell"

        if not self._ensure_pswindowsupdate():
            _log(
                "PSWindowsUpdate is unavailable - cannot run Windows Update. "
                "Verify internet access and PowerShell execution policy.",
                "error",
            )
            return

        if _stop.is_set():
            return

        with self.config_lock:
            dry_run = self.config.get("dry_run", False)
        if dry_run:
            _log("[DRY RUN] Would scan and install Windows Updates via PSWindowsUpdate.", "debug")
            return

        _log("Scanning for pending Windows Updates (PSWindowsUpdate)…")
        scan_script = (
            "Import-Module PSWindowsUpdate -ErrorAction Stop; "
            "$updates = Get-WindowsUpdate -AcceptAll -IgnoreReboot -ErrorAction Stop; "
            "if ($updates.Count -eq 0) { Write-Output 'No updates available.' } "
            "else { "
            "  Write-Output \"Found $($updates.Count) update(s):\"; "
            "  $updates | ForEach-Object { "
            "    $sz = if ($_.Size) { \"$([math]::Round($_.Size/1MB,1)) MB\" } else { 'n/a' }; "
            "    Write-Output \"  [$($_.KB)] $($_.Title) - $sz\" "
            "  } "
            "}"
        )
        try:
            scan = subprocess.run(
                [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", scan_script],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=_WINDOWS_UPDATE_SCAN_TIMEOUT, **_NO_WINDOW,
            )
            for line in scan.stdout.splitlines():
                stripped = strip_ansi(line)
                if stripped:
                    _log(stripped)
            for line in scan.stderr.splitlines():
                stripped = strip_ansi(line)
                if stripped:
                    _log(stripped, "warn")
            if "No updates available." in scan.stdout:
                _log("Windows is already up-to-date.")
                return
        except subprocess.TimeoutExpired:
            _log("Windows Update scan timed out - proceeding to install anyway.", "warn")
        except Exception as e:
            _log(f"Windows Update scan error: {e}", "warn")

        if _stop.is_set():
            return

        _log("Installing Windows Updates via PSWindowsUpdate…")
        install_script = (
            "Import-Module PSWindowsUpdate -ErrorAction Stop; "
            "Install-WindowsUpdate "
            "-AcceptAll -IgnoreReboot -AutoReboot:$false "
            "-ErrorAction Stop"
        )
        self.run_command(
            [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", install_script],
            timeout=_WINDOWS_UPDATE_TIMEOUT,
        )

        _log("Windows Update via PSWindowsUpdate completed.")
        if self.is_reboot_pending():
            _log("A reboot is required to finish applying updates.", "warn")

    def is_reboot_pending(self) -> bool:
        """Return True if a Windows reboot is pending (registry key check).

        Also updates self._reboot_pending_cache so the GUI thread can read
        the last-known result without making a blocking registry call itself.
        """
        if winreg is None:
            return False

        # Key existence alone signals a pending reboot — no value read needed.
        # Both keys use REG_NONE / presence-only semantics.
        checks = [
            (winreg.HKEY_LOCAL_MACHINE,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\WindowsUpdate\Auto Update\RebootRequired"),
            (winreg.HKEY_LOCAL_MACHINE,
             r"SOFTWARE\Microsoft\Windows\CurrentVersion\Component Based Servicing\RebootPending"),
        ]
        for hive, path in checks:
            try:
                with winreg.OpenKey(hive, path):
                    self._reboot_pending_cache = True
                    return True
            except FileNotFoundError:
                continue
            except OSError as e:
                logger.warning(f"is_reboot_pending: could not read registry key '{path}': {e}")
                continue
        self._reboot_pending_cache = False
        return False

    def _probe_one(self, name: str, info: dict) -> dict:
        """Probe a single component's version — run concurrently by health_check()."""
        if not info.get("available"):
            return _PROBE_RESULT_UNAVAILABLE
        _path = info.get("path")
        try:
            version = "unknown"
            if name in _VERSION_FLAG_COMPS:
                if not _path:
                    return _PROBE_RESULT_UNAVAILABLE
                r = subprocess.run(
                    [_path, "--version"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                    **_NO_WINDOW,
                )
                # Some tools (notably winget) write their version to
                # stderr instead of stdout when stdout is redirected
                # (capture_output=True + CREATE_NO_WINDOW).  Fall back
                # to stderr when stdout is empty after stripping.
                # partition() avoids allocating a full split list.
                raw = r.stdout or r.stderr
                version = strip_ansi(raw.partition("\n")[0])
            elif name == "scoop":
                # resolve ps only when needed
                ps = self.components.get("windows_update", {}).get("path") or "powershell"
                _r = subprocess.run(
                    [ps, "-NoProfile", "-Command", "scoop --version"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                    **_NO_WINDOW,
                )
                output = _r.stdout or _r.stderr
                match = _SCOOP_VER_RE.search(strip_ansi(output))
                version = match.group(1) if match else "unknown"
            elif name == "pip":
                version = strip_ansi(subprocess.run(
                    [sys.executable, "-m", "pip", "--version"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                    **_NO_WINDOW,
                ).stdout)
            elif name == "windows_update":
                try:
                    r = subprocess.run(
                        [info["path"], "-NoProfile", "-Command",
                         "(Get-Module -ListAvailable PSWindowsUpdate "
                         "| Sort-Object Version -Descending "
                         "| Select-Object -First 1).Version.ToString()"],
                        capture_output=True, text=True, encoding="utf-8",
                        errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                        **_NO_WINDOW,
                    )
                    # partition("\n")[0] keeps only the first output line —
                    # consistent with other version probes and guards against
                    # multi-line PS output (e.g. auto-import warnings).
                    ver = strip_ansi(r.stdout).partition("\n")[0]
                    version = (f"PSWindowsUpdate {ver}" if ver and r.returncode == 0
                               else "PSWindowsUpdate (not installed - will install on run)")
                except subprocess.TimeoutExpired:
                    raise
                except Exception as e:
                    logger.warning(f"health_check: PSWindowsUpdate probe failed: {e}")
                    version = "PSWindowsUpdate (check failed)"
            elif name == "oh_my_posh":
                _omp_raw = strip_ansi(subprocess.run(
                    [info["path"], "version"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                    **_NO_WINDOW,
                ).stdout).strip()
                # oh-my-posh outputs a bare version number (e.g. "23.4.1");
                # prefix with "v" for consistency with other components.
                version = f"v{_omp_raw}" if _omp_raw and not _omp_raw.startswith("v") else _omp_raw
            elif name == "python":
                r = subprocess.run(
                    [sys.executable, "--version"],
                    capture_output=True, text=True, encoding="utf-8",
                    errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                    **_NO_WINDOW,
                )
                version = strip_ansi(r.stdout or r.stderr)
            elif name == "windows_terminal":
                _wt_src = info.get("wt_source") or "winget"
                _wt_id  = info.get("wt_id")     or _WT_WINGET_ID
                try:
                    r = subprocess.run(
                        [info["path"], "list", "--id", _wt_id,
                         "--source", _wt_src,
                         "--accept-source-agreements"],
                        capture_output=True, text=True, encoding="utf-8",
                        errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                        **_NO_WINDOW,
                    )
                    # Use the track-specific regex: winget-track matches
                    # _WINGET_WT_VER_RE; Store-track output has the msstore
                    # ID so we fall back to a generic version column grab.
                    if _wt_src == "winget":
                        match = _WINGET_WT_VER_RE.search(strip_ansi(r.stdout))
                        version = match.group(1) if match else (
                            "installed" if r.returncode == 0 else "not found")
                    else:
                        # Store-track: ID is 9N0DX20HK701, not the display name.
                        # winget list prints: "<name>  9N0DX20HK701  <ver>  ..."
                        # Grab the first version-like token after the Store ID.
                        _ms_match = _MSSTORE_VER_RE.search(
                            strip_ansi(r.stdout))
                        version = (_ms_match.group(1) if _ms_match
                                   else ("installed (Store)" if r.returncode == 0
                                         else "not found"))
                except subprocess.TimeoutExpired:
                    raise
                except Exception as e:
                    logger.warning(f"health_check: windows_terminal probe failed: {e}")
                    version = "unknown"
            elif name == "powershell":
                # Use pwsh --version directly: faster than winget list, always
                # accurate regardless of install source (winget vs GitHub MSI).
                # pwsh_path was stored by detect_components — no shutil.which().
                _ps7 = info.get("pwsh_path") or shutil.which("pwsh")
                if _ps7:
                    try:
                        r = subprocess.run(
                            [_ps7, "--version"],
                            capture_output=True, text=True, encoding="utf-8",
                            errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                            **_NO_WINDOW,
                        )
                        version = strip_ansi(r.stdout or r.stderr) or "unknown"
                    except subprocess.TimeoutExpired:
                        raise
                    except Exception as e:
                        logger.warning(f"health_check: powershell probe failed: {e}")
                        version = "unknown"
                else:
                    version = "not found"
            elif name == "ps_modules":
                _ps_path = info.get("path") or "powershell"
                try:
                    r = subprocess.run(
                        [_ps_path, "-NoProfile", "-Command",
                         "(Get-Module -ListAvailable | Measure-Object).Count"],
                        capture_output=True, text=True, encoding="utf-8",
                        errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                        **_NO_WINDOW,
                    )
                    _cnt = strip_ansi(r.stdout).partition("\n")[0].strip()
                    version = f"{_cnt} modules" if _cnt.isdigit() else "available"
                except subprocess.TimeoutExpired:
                    raise
                except Exception as e:
                    logger.warning(f"health_check: ps_modules probe failed: {e}")
                    version = "unknown"
            elif name == "windows_store":
                try:
                    r = subprocess.run(
                        [info["path"], "source", "list", "--name", "msstore"],
                        capture_output=True, text=True, encoding="utf-8",
                        errors="replace", timeout=_HEALTH_VER_TIMEOUT,
                        **_NO_WINDOW,
                    )
                    version = "msstore available" if r.returncode == 0 else "msstore unavailable"
                except subprocess.TimeoutExpired:
                    raise
                except Exception as e:
                    logger.warning(f"health_check: windows_store probe failed: {e}")
                    version = "unknown"
            return {"status": "available", "version": version}
        except subprocess.TimeoutExpired:
            return _PROBE_RESULT_TIMED_OUT
        except Exception as e:
            logger.warning(f"health_check version probe failed for '{name}': {e}")
            return _PROBE_RESULT_ERROR

    def health_check(self):
        """Probe all components concurrently, streaming incremental GUI updates."""
        if not self._components_ready.wait(timeout=15):
            logger.warning("health_check: component detection did not finish in 15 s; proceeding with partial data.")
        if not self.components:
            # Nothing to probe — executor would crash with max_workers=0.
            logger.warning("health_check: no components available; skipping.")
            return {}
        dashboard: Dict[str, Any] = {}
        _gq = self.gui_queue  # bind once — 12 × 2 LOAD_ATTR → LOAD_FAST

        # Run all probes in parallel — worst-case drops from (n × timeout) to
        # ~1× timeout regardless of how many components are installed.
        # Do NOT use `with pool:` as a context manager.  ThreadPoolExecutor.
        # __exit__ always calls shutdown(wait=True), which blocks until every
        # daemon thread finishes even after an explicit shutdown(wait=False).
        # Managing the pool manually lets us exit immediately on cancel.
        pool = concurrent.futures.ThreadPoolExecutor(
                max_workers=min(len(self.components), 10),
                thread_name_prefix="health")
        try:
            futures = {
                pool.submit(self._probe_one, name, info): name
                for name, info in self.components.items()
            }
            for future in concurrent.futures.as_completed(futures):
                if self._health_stop_event.is_set():
                    # Cancel unstarted futures then shut the pool down without
                    # waiting — running threads finish in the background.
                    for f in futures:
                        f.cancel()
                    break
                name = futures[future]
                try:
                    result = future.result(timeout=_PROBE_DEADLINE)
                except concurrent.futures.TimeoutError:
                    logger.warning(f"health_check: probe for '{name}' timed out after {_PROBE_DEADLINE}s")
                    result = _PROBE_RESULT_HC_TIMEOUT
                dashboard[name] = result
                if _gq:
                    _gq.put(("health_row", (name, result)))
        finally:
            # cancel_futures=True (Py 3.9+) drops queued-but-not-started work.
            try:
                pool.shutdown(wait=False, cancel_futures=True)
            except TypeError:
                pool.shutdown(wait=False)

        return dashboard

    def update_ps_modules(self):
        """Update all installed PowerShell modules via Get-InstalledModule | Update-Module."""
        _log  = self.log
        _stop = self.stop_event
        ps = (self.components.get("ps_modules", {}).get("path")
              or self.components.get("windows_update", {}).get("path")
              or "powershell")
        with self.config_lock:
            dry_run = self.config.get("dry_run", False)
        if dry_run:
            _log("[DRY RUN] Would run: Get-InstalledModule | Update-Module -Force", "debug")
            return
        if _stop.is_set():
            return
        _log("Updating installed PowerShell modules (this may take a while)…")
        self.run_command(
            [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command",
             "Get-InstalledModule | Update-Module -Force -ErrorAction SilentlyContinue"],
            timeout=_PS_MODULES_UPGRADE_TIMEOUT,
        )
        _log("PowerShell module updates completed.")

    def update_component(self, name):
        """Dispatch a single component update by name."""
        _log  = self.log         # 4 calls
        _stop = self.stop_event  # 1 check in scoop branch
        info = self.components.get(name)
        if not info or not info["available"]:
            _log(f"{_COMP_DISPLAY_NAMES.get(name, name)} is not available, skipping.")
            return
        if name == "python":
            self.update_python()
            return
        if name == "ps_modules":
            self.update_ps_modules()
            return
        if name == "pip":
            self.update_pip()
            return
        if name == "oh_my_posh":
            self.run_command([info["path"], "upgrade"], timeout=_OH_MY_POSH_UPGRADE_TIMEOUT)
            return
        if name == "windows_update":
            self.update_windows()
            return
        if name == "windows_store":
            self.update_windows_store()
            return
        if name == "windows_terminal":
            # Use the install-track ID and source detected at startup.
            # winget track: Microsoft.WindowsTerminal --source winget
            # Store  track: 9N0DX20HK701             --source msstore
            _wt_id  = info.get("wt_id")     or _WT_WINGET_ID
            _wt_src = info.get("wt_source") or "winget"
            _log(f"Upgrading Windows Terminal (id={_wt_id}, source={_wt_src})…")
            self.run_command(
                [info["path"], "upgrade", "--id", _wt_id,
                 "--source", _wt_src,
                 "--accept-source-agreements", "--accept-package-agreements"],
                timeout=_WINDOWS_TERMINAL_UPGRADE_TIMEOUT,
                success_output=_WINGET_NO_UPDATE_PHRASES,
            )
            return
        if name == "powershell":
            _log(f"Upgrading PowerShell 7 (id={_PS7_WINGET_ID}, source=winget)…")
            self.run_command(
                [info["path"], "upgrade", "--id", _PS7_WINGET_ID,
                 "--source", "winget",
                 "--accept-source-agreements", "--accept-package-agreements"],
                timeout=_POWERSHELL_UPGRADE_TIMEOUT,
                success_output=_WINGET_NO_UPDATE_PHRASES,
            )
            return
        # Two-step Scoop update: exit before building cmd_map so the
        # 4-entry dict is never allocated for scoop calls.
        if name == "scoop":
            ps = self.components.get("windows_update", {}).get("path") or "powershell"
            self.run_command(
                [ps, "-NoProfile", "-Command", "scoop update"],
                timeout=_SCOOP_UPGRADE_TIMEOUT,
            )
            if not _stop.is_set():
                self.run_command(
                    [ps, "-NoProfile", "-Command", "scoop update *"],
                    timeout=_SCOOP_UPGRADE_TIMEOUT,
                )
            return
        if name == "winget":
            with self.config_lock:
                _wgu_source  = self.config.get("winget_source_update", True)
                _wgu_unknown = self.config.get("winget_include_unknown", False)
            if _wgu_source:
                _log("Refreshing winget sources…")
                self.run_command(
                    [info["path"], "source", "update"],
                    timeout=60,
                    retries=1,  # best-effort: one attempt, no backoff
                )
                if _stop.is_set():
                    return
            _winget_cmd = [
                info["path"], "upgrade", "--all",
                "--accept-source-agreements", "--accept-package-agreements",
            ]
            if _wgu_unknown:
                _winget_cmd.append("--include-unknown")
            self.run_command(
                _winget_cmd,
                timeout=_WINGET_UPGRADE_TIMEOUT,
                success_output=_WINGET_NO_UPDATE_PHRASES,
            )
            return
        cmd_map = {
            "choco": (
                [info["path"], "upgrade", "all", "-y"],
                _CHOCO_UPGRADE_TIMEOUT,
            ),
            "npm": (
                [info["path"], "update", "-g", "--no-fund", "--no-audit"],
                _NPM_UPGRADE_TIMEOUT,
            ),
            "clink": (
                (["cmd", "/c", info["path"], "update"]
                 if info["path"].endswith(".bat")
                 else [info["path"], "update"]),
                _RUN_COMMAND_DEFAULT_TIMEOUT,
            ),
        }
        entry = cmd_map.get(name)
        if entry:
            command, timeout = entry
            self.run_command(command, timeout=timeout)
        else:
            _log(f"No update handler for component '{name}' — skipping.", "warn")

    def run_selected(self, selected):
        """Run updates for the given list of component names (engine entry point)."""
        self.stop_event.clear()
        # Also reset the health stop event so future probes do not
        # self-cancel on a stale flag from a previous cancellation.
        self._health_stop_event.clear()
        with self._error_lock:
            self._run_active  = True
            self._error_count = 0
        self._rebooting = False
        _t0 = time.monotonic()
        try:
            self._run_selected_inner(selected, _t0=_t0)
        except Exception as e:
            logger.exception("Unexpected error in run_selected")
            self.emit_status("Error - see log")
            self.log(f"Unexpected error during update run: {e}", "error")
            raise
        finally:
            with self._error_lock:
                self._run_active = False

    def _run_selected_inner(self, selected, _t0: float):
        """Inner update loop — iterates selected components and emits GUI progress."""
        # Bind hot attributes first — used throughout this method.
        # All three must appear before any use (including the early-return block).
        _gq   = self.gui_queue   # avoids 5 × LOAD_ATTR (2 in loop, 3 at boundaries)
        _log  = self.log         # avoids 1 LOAD_ATTR on each of 10 log() calls
        _stop = self.stop_event  # avoids 1 LOAD_ATTR on each of 3 stop checks
        total = len(selected)
        if total == 0:
            _log("No components selected or available.", "warn")
            if _gq: _gq.put(("status", "Idle"))
            return

        run_ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        logger.info("=" * 60)
        logger.info(f"=== Run started at {run_ts} - {total} component(s) selected ===")
        logger.info("=" * 60)

        _log(f"Starting updates for {total} component(s).")
        failures = 0
        _comp_states: dict = {}   # comp_name → "done" | "error"
        with self.config_lock:
            inter_delay = self.config["delay_between_components"]
        for idx, comp in enumerate(selected):
            if _stop.is_set():
                if _gq: _gq.put(("status", "Cancelled"))
                return
            _dname = _COMP_DISPLAY_NAMES.get(comp, comp)
            _trail = "-" * max(0, _COMP_HDR_TOTAL - 3 - len(_dname) - 1)
            # Use plain ASCII "-" so every character is guaranteed
            # exactly 1 unit wide in Consolas — U+2500 box-drawing chars
            # can render fractionally wider and break visual alignment.
            _hdr = f"-- {_dname} {_trail}"  # built once; reused for queue, logger, print
            if _gq:
                _gq.put(("log_header", _hdr))
            logger.info(_hdr)
            if self._debug_mode:
                print(_hdr)
            # signal the GUI that this component is now running.
            if _gq:
                _gq.put(("comp_status", (comp, "running")))
            with self._error_lock:
                errors_before = self._error_count
            self.update_component(comp)
            with self._error_lock:
                had_error = self._error_count > errors_before
                if had_error:
                    failures += 1
            # Combine comp_status + progress into a single queue message
            # to halve GUI queue traffic (1 put/get instead of 2 per component).
            _comp_states[comp] = "error" if had_error else "done"
            if _gq:
                _gq.put(("comp_progress", (
                    comp,
                    "error" if had_error else "done",
                    (idx + 1) / total * 100,
                )))
            if inter_delay > 0 and _stop.wait(timeout=inter_delay):
                if _gq: _gq.put(("status", "Cancelled"))
                return

        if _stop.is_set():
            if _gq: _gq.put(("status", "Cancelled"))
            return

        do_restart = False
        with self.config_lock:
            auto_restart = self.config["auto_restart"]
            _rct         = self.config.get("restart_confirm_timeout", 30)
            dry_run      = self.config.get("dry_run", False)
        if auto_restart:
            _log("Auto-restart enabled. Requesting confirmation before reboot…")
            if _gq:
                result_box    = {"answer": False}
                confirm_event = threading.Event()
                # Signal the GUI's priority drain via an engine-level flag
                # so update_gui can skip the O(n) drain on normal ticks.
                self._confirm_restart_pending.set()
                _gq.put(("confirm_restart", (confirm_event, result_box)))
                timed_out = not confirm_event.wait(timeout=_rct)
                if timed_out:
                    _log(f"Reboot confirmation timed out after {_rct}s - skipping restart.", "warn")
                elif not result_box["answer"]:
                    _log("Reboot declined by user - skipping restart.", "warn")
                else:
                    do_restart = True
            else:
                do_restart = True

        if do_restart:
            if failures:
                _log(
                    f"Restarting - {failures} component(s) reported errors. "
                    "Review the log after reboot.",
                    "warn",
                )
            _log("Restarting system in 10 seconds…")
            if dry_run:
                _log("[DRY RUN] Would execute: shutdown /r /f /t 10", "debug")
            else:
                self._rebooting = True
                subprocess.run(["shutdown", "/r", "/f", "/t", "10"],
                               check=False, capture_output=True,
                               encoding="utf-8", errors="replace",
                               **_NO_WINDOW)
            if _gq: _gq.put(("status", "Restarting..." if not dry_run else "Dry-run: reboot skipped"))
            return

        if _gq: _gq.put(("status", "Completed" if failures == 0 else f"Completed with {failures} error(s)"))
        _elapsed_s   = time.monotonic() - _t0
        _elapsed_fmt = (f"{int(_elapsed_s // 60)} m {int(_elapsed_s % 60):02d} s"
                        if _elapsed_s >= 60 else f"{int(_elapsed_s)} s")
        if failures:
            _log(f"Updates finished — {failures} component(s) reported errors "
                 f"in {_elapsed_fmt}.  Check the log for details.", "warn")
        else:
            _log(f"All updates completed successfully in {_elapsed_fmt}.")
        # Notify the GUI so it can show a completion dialog if the
        # user has notify_on_complete enabled in settings.
        # Store per-component failure list so the GUI can offer Retry Failed.
        self._last_failed = [comp for comp, state in _comp_states.items()
                             if state == "error"]
        self._append_run_history(
            selected=selected,
            failures=failures,
            elapsed_s=time.monotonic() - _t0,
            dry_run=dry_run,   # already captured under config_lock above
        )
        if _gq:
            _gq.put(("run_complete", failures))

    def _append_run_history(self, selected: list, failures: int,
                            elapsed_s: float, dry_run: bool) -> None:
        """Append a run record to updhist.json; silently ignore write errors."""
        record = {
            "timestamp": datetime.datetime.now().isoformat(timespec="seconds"),
            "components": selected,   # json.dump serialises synchronously; no copy needed
            "failures":   failures,
            "elapsed_s":  round(elapsed_s, 1),
            "dry_run":    dry_run,
        }
        try:
            try:
                with open(HIST_FILE, "r", encoding="utf-8") as f:
                    history = json.load(f)
                if not isinstance(history, list):
                    history = []
            except (OSError, json.JSONDecodeError):
                history = []
            history.append(record)
            if len(history) > _MAX_HISTORY:
                history = history[-_MAX_HISTORY:]
            # Atomic write: write to a temp file then os.replace() so a crash
            # mid-write never leaves a truncated or partial history file.
            # Mirrors the pattern used by save_config().
            _hist_dir = os.path.dirname(HIST_FILE) or "."
            _tmp_hist = None
            with tempfile.NamedTemporaryFile(
                "w", dir=_hist_dir, delete=False, suffix=".tmp", encoding="utf-8"
            ) as _tf:
                json.dump(history, _tf, indent=2)
                _tmp_hist = _tf.name
            os.replace(_tmp_hist, HIST_FILE)
        except OSError:
            if _tmp_hist:
                try:
                    os.unlink(_tmp_hist)
                except OSError:
                    pass
            pass  # history is convenience data — never raise on failure

    def emit_status(self, status):
        """Put a status string onto the GUI queue."""
        if self.gui_queue is not None:
            self.gui_queue.put(("status", status))

#==================== THEME =====================
# Flat modern palette.
# accent      — Windows-blue highlight used on Start button and selections.
# border      — 1-px divider / card outline colour.
# section_bg  — slightly offset panel background for component / health cards.
# btn_hover   — button background on mouse-enter.
THEMES = {
    "light": {
        "bg":           "#f3f3f3",
        "fg":           "#1a1a1a",
        "widget_bg":    "#ffffff",
        "widget_fg":    "#1a1a1a",
        "log_bg":       "#ffffff",
        "btn_bg":       "#e8e8e8",
        "btn_fg":       "#1a1a1a",
        "btn_hover":    "#d0d0d0",
        "frame_bg":     "#f3f3f3",
        "label_bg":     "#f3f3f3",
        "section_bg":   "#ffffff",
        "border":       "#d0d0d0",
        "scrollbar_thumb": "#b0b0b0",
        "scrollbar_hover": "#888888",
        "scrollbar_trough": "#f0f0f0",
        "accent":       "#0078d4",
        "accent_fg":    "#ffffff",
        "tag_info":     "#1a1a1a",
        "tag_debug":    "#888888",
        "tag_warn":     "#b35c00",
        "tag_error":    "#c42b1c",
        "dot_running":  "#0078d4",
        "dot_done":     "#107c10",
        "dot_error":    "#c42b1c",
        "dot_idle":     "#888888",
        "tree_good":    "#dff6dd",
        "tree_bad":     "#fde7e9",
        "tree_warn":    "#fff4ce",
        "tree_alt":     "#f7f7f7",
    },
    "dark": {
        "bg":           "#1f1f1f",
        "fg":           "#cccccc",
        "widget_bg":    "#2d2d2d",
        "widget_fg":    "#cccccc",
        "log_bg":       "#181818",
        "btn_bg":       "#333333",
        "btn_fg":       "#cccccc",
        "btn_hover":    "#3e3e3e",
        "frame_bg":     "#1f1f1f",
        "label_bg":     "#1f1f1f",
        "section_bg":   "#252526",
        "border":       "#3c3c3c",
        "scrollbar_thumb": "#5a5a5a",
        "scrollbar_hover": "#7a7a7a",
        "scrollbar_trough": "#2a2a2a",
        "accent":       "#0078d4",
        "accent_fg":    "#ffffff",
        "tag_info":     "#cccccc",
        "tag_debug":    "#6a6a6a",
        "tag_warn":     "#e8a04a",
        "tag_error":    "#f47070",
        "dot_running":  "#0078d4",
        "dot_done":     "#6ccb5f",
        "dot_error":    "#f47070",
        "dot_idle":     "#6a6a6a",
        "tree_good":    "#1a3a20",
        "tree_bad":     "#3a1a1c",
        "tree_warn":    "#3a3010",
        "tree_alt":     "#262626",
    },
}

_MAX_HISTORY       = 50    # Maximum run history entries kept in updhist.json
_MAX_MSGS_PER_TICK = 200
_MAX_LOG_LINES     = 2000   # Trim log_widget beyond this to prevent Tk slowdown

# Module-level constants for update_gui's hot log-message path.
_LOG_LEVEL_ORDER: dict = {"debug": 0, "info": 1, "warn": 2, "error": 3}
_LOG_FILTER_MIN:  dict = {"All": 0, "Info+": 1, "Warn+": 2, "Error": 3}
# _LOG_PREFIX_MAP was removed in v3.13.6: the startswith() chain in
# update_gui (added v3.12.19) renders the dict-based prefix parse obsolete.
# Level-tag normalisation map — used by UpdateEngine.log().
# Hoisted from class attribute (v3.13.8): LOAD_GLOBAL is 1 op vs
# LOAD_FAST + LOAD_ATTR = 2 ops; log() is called O(1000) times per run.
_LEVEL_MAP: dict = {
    "debug":   "debug",
    "info":    "info",
    "warn":    "warn",
    "warning": "warn",
    "error":   "error",
}
_COMP_STATUS_SYMBOLS: dict = {"running": "▶", "done": "✔", "error": "✘"}
# Per-state dot foreground colour keys (looked up from the active theme dict).
# Using theme keys rather than hard-coded hex keeps dark/light mode correct.
# Keyword tuples for _set_status dot-colour derivation.
# Module-level so the tuple objects are created once at import.
_STATUS_KW_RUNNING: tuple = (
    "running", "starting", "refreshing", "checking",
    "restarting", "scanning", "upgrading", "installing",
)
_STATUS_KW_DONE:  tuple = ("completed", "up-to-date", "up to date")
_STATUS_KW_ERROR: tuple = (
    "error", "failed", "cancelled", "timeout", "unavailable",
)

_DOT_COLOUR_KEY: dict = {
    "running": "dot_running",
    "done":    "dot_done",
    "error":   "dot_error",
}  # missing key → "dot_idle" via .get() default
# Human-readable display names for component keys used in the GUI
# (checkboxes, health treeview, run log headers).
# Internal dict keys are unchanged everywhere else.
_COMP_DISPLAY_NAMES: dict = {
    "winget":          "WinGet",
    "choco":           "Chocolatey",
    "scoop":           "Scoop",
    "npm":             "npm",
    "clink":           "Clink",
    "pip":             "pip",
    "oh_my_posh":      "Oh My Posh",
    "windows_update":  "Windows Update",
    "python":          "Python",
    "windows_store":    "Windows Store",
    "windows_terminal": "Windows Terminal",
    "powershell":       "PowerShell",
    "ps_modules":       "PS Modules",
}
# Header total width = 44 chars. trailing = 40 - len(name) so every
# header line is the same length with no space-padding (spaces are
# narrower than ─ in proportional fonts and cause visual misalignment).
_COMP_HDR_TOTAL: int = 44
# Gradient constants and _hsv_hex helper removed in v3.17.33 (flat accent bar).

# winget upgrade --id X exits non-zero when the package is already
# at the latest version. These stdout phrases identify that condition
# so run_command can treat it as a quiet success instead of retrying.
_WINGET_NO_UPDATE_PHRASES: frozenset = frozenset({
    "No applicable update found.",
    "No available upgrade found.",
    "All installed packages are up to date.",
    "No newer package versions are available",
    "No installed package found matching input criteria.",
})

# Pre-compiled patterns used in _probe_one version extraction.
# Defined at module level so they are compiled once at import time rather
# than on every health-check call (up to 12 concurrent threads per refresh).
_SCOOP_VER_RE     = re.compile(r"v?(\d+\.\d+\.\d+)")
_WINGET_WT_VER_RE = re.compile(r"Microsoft\.WindowsTerminal\s+(\S+)")
# Windows Store track version extraction for Windows Terminal _probe_one.
_MSSTORE_VER_RE   = re.compile(r"9N0DX20HK701\s+(\S+)")
# Pre-compiled patterns for _show_history sort key.
_HIST_RE_DIGITS:    re.Pattern = re.compile(r"\d+")
_HIST_RE_DUR_PARTS: re.Pattern = re.compile(r"(\d+)\s*([ms])")

# Components that expose --version on their primary executable.
# Module-level frozenset → O(1) membership test, allocated once at import.
_VERSION_FLAG_COMPS: frozenset = frozenset({"winget", "choco", "npm", "clink"})

# Ordered component names for detect_components() Pass 1.
# Defined at module level so no new list is allocated on each startup.
_DETECT_PASS1_NAMES: tuple = (
    "winget", "choco", "scoop", "npm", "clink", "pip",
    "oh_my_posh", "windows_update", "python",
)

# Settings dialog numeric fields — (label, config_key, min, max).
# Pure data; hoisted so open_settings() and _save() never rebuild them.
_SETTINGS_NUMERIC_FIELDS: tuple = (
    ("Retries",                      "retries",                   1,  20),
    ("Retry delay (s)",              "retry_delay",               1, 300),
    ("Delay between components (s)", "delay_between_components",  0, 600),
    ("Restart confirm timeout (s)",  "restart_confirm_timeout",   5, 300),
    ("Health refresh interval (s)",  "health_refresh_interval",   0, 3600),
)
# Pre-built O(1) lookup dicts derived from the above — computed once at
# import time so _save() never allocates three comprehensions per Save click.
_SETTINGS_FIELD_LABEL: dict = {k: lbl for lbl, k, _lo, _hi in _SETTINGS_NUMERIC_FIELDS}
_SETTINGS_FIELD_LO:    dict = {k: lo  for _lbl, k, lo,  _hi in _SETTINGS_NUMERIC_FIELDS}
_SETTINGS_FIELD_HI:    dict = {k: hi  for _lbl, k, _lo, hi  in _SETTINGS_NUMERIC_FIELDS}

# Settings dialog boolean fields — (label, config_key).
_SETTINGS_BOOL_FIELDS: tuple = (
    ("Notify on completion", "notify_on_complete"),
    ("Auto health on start", "auto_health_on_start"),
    ("Start minimised to tray",          "start_minimised"),
    ("Refresh winget sources first",      "winget_source_update"),
    ("winget: include unknown versions",  "winget_include_unknown"),
    ("pip: skip editable installs",       "pip_skip_editable"),
)

# Keyboard shortcuts displayed in the Help dialog.
# Tuple of (key_label, description) pairs — hoisted so _show_shortcuts()
# never allocates this list on each dialog open.
_SHORTCUTS: tuple = (
    ("F5",           "Start Updates"),
    ("F1",           "Help / Keyboard Shortcuts"),
    ("Ctrl + F",     "Focus Search"),
    ("Escape",    "Cancel (during run) / Clear search"),
    ("Ctrl + R",  "Refresh Health"),
    ("Ctrl + L",  "Clear Log"),
    ("Ctrl+Shift+C", "Copy Log to Clipboard"),
    ("Ctrl + D",     "Toggle Dry Run"),
    ("Ctrl + H",     "Run History"),
    ("Ctrl + S",     "Settings"),
    ("Ctrl + A",         "Select All Components"),
    ("Ctrl + Shift+A",   "Deselect All Components"),
    ("Ctrl + Shift+A", "Deselect All Components"),
)

# Candidate log file paths shown in the "▾  Logs" dropdown menu.
# LOG_FILE is assigned once at module init and never mutated, so this
# tuple is safe to compute here — no stale-path risk.
_LOG_FILES: tuple = (
    LOG_FILE,
    f"{LOG_FILE}.1",
    f"{LOG_FILE}.2",
    f"{LOG_FILE}.3",
)

# Maximum number of search highlights drawn simultaneously.
# Prevents lw.search() from making thousands of Tcl calls when the
# user types a single common character (e.g. "e") in a large log.
_MAX_SEARCH_MATCHES: int = 500

# Pre-built probe result dicts — fully static; shared across all health-check
# threads.  Downstream consumers only READ these dicts, never mutate them.
# Eliminates up to 12 dict allocations per health-check refresh (error paths).
_PROBE_RESULT_UNAVAILABLE: dict = {"status": "unavailable", "version": "n/a"}
_PROBE_RESULT_TIMED_OUT:   dict = {"status": "error",       "version": "timed out"}
_PROBE_RESULT_ERROR:       dict = {"status": "error",       "version": "n/a"}
_PROBE_RESULT_HC_TIMEOUT:  dict = {"status": "error",       "version": "probe timed out"}

# Status string → treeview row-tag mapping for the health dashboard.
# Used by _apply_health_row and _apply_health_data; extracted here to
# avoid repeating the three-way ternary at every call site.
_HEALTH_TAG: dict = {"available": "good", "unavailable": "bad"}
# Human-friendly display text for health status strings shown in the
# Status column.  Raw keys drive row colouring; display text is UI-only.
_HEALTH_STATUS_LABEL: dict = {
    "available":    "✓  OK",
    "unavailable":  "—  N/A",
    "error":        "⚠  Error",
}
# Reverse map — used by export_health to recover machine-readable values.
_HEALTH_LABEL_RAW: dict = {v: k for k, v in _HEALTH_STATUS_LABEL.items()}
# Missing key → "warn" via .get() default (covers "error" and anything else).

# Fixed header-background colours for _msgbox warn/error dialogs.
# tag_warn/tag_error in dark mode are bright (chosen to be read ON a dark
# background, not to BE the background).  These darker values maintain
# WCAG AA contrast (≥4.5:1) with white text in both light and dark mode.
_MSGBOX_WARN_HDR:  str = "#b35c00"   # 4.7:1 vs white
_MSGBOX_ERROR_HDR: str = "#c42b1c"   # 5.7:1 vs white

# Sentinel string set by _copy_log — _reset_status only clears the
# status bar if this exact string is still showing (prevents overwriting
# a run-completion or health-check status that arrived during the 2-s window).
_COPY_LOG_SENTINEL: str = "Log copied to clipboard."

# Shared itemgetter for log_batch groupby key — avoids allocating a new
# lambda object on every call (C-level callable, faster than a Python lambda,
# created once at import time).  Note: log_batch is no longer sorted before
# groupby (sort was removed in v3.10.44 to preserve chronological order).
_LOG_BATCH_KEY = operator.itemgetter(1)

# ── Tooltip helper ────────────────────────────────────────────────────────────
class _ToolTip:
    """Lightweight hover tooltip that appears after a short delay.

    theme_getter: optional callable → dict  — queried just before display so
    the popup always matches the current light/dark palette.
    """
    _DELAY = 650   # ms before the tip appears

    def __init__(self, widget: "tk.Widget", text: str,
                 theme_getter=None):
        self._w   = widget
        self._txt = text
        self._tg  = theme_getter
        self._id  = None
        self._win = None
        widget.bind("<Enter>",  self._on_enter, add="+")
        widget.bind("<Leave>",  self._on_leave, add="+")
        widget.bind("<Button>", self._on_leave, add="+")

    def _on_enter(self, _e=None):
        self._cancel()
        self._id = self._w.after(self._DELAY, self._show)

    def _on_leave(self, _e=None):
        self._cancel()
        self._destroy()

    def _cancel(self):
        if self._id:
            try:
                self._w.after_cancel(self._id)
            except Exception:
                pass
            self._id = None

    def _destroy(self):
        if self._win:
            try:
                self._win.destroy()
            except Exception:
                pass
            self._win = None

    def _show(self):
        self._id = None
        if self._win:
            return
        t   = self._tg() if callable(self._tg) else None
        bg  = t["widget_bg"] if t else "#fafafa"
        fg  = t["fg"]        if t else "#1a1a1a"
        brd = t["border"]    if t else "#cccccc"
        try:
            wx = self._w.winfo_rootx()
            wy = self._w.winfo_rooty()
            ww = self._w.winfo_width()
            wh = self._w.winfo_height()
            sx = self._w.winfo_screenwidth()
            sy = self._w.winfo_screenheight()
            tip = tk.Toplevel(self._w)
            tip.wm_overrideredirect(True)
            tip.configure(bg=brd)
            tk.Label(tip, text=self._txt,
                     bg=bg, fg=fg,
                     font=("Segoe UI", 8),
                     padx=7, pady=3).pack(padx=1, pady=1)
            tip.update_idletasks()
            tw = tip.winfo_reqwidth()
            th = tip.winfo_reqheight()
            # Centre below the widget; clamp so the tip never leaves the screen.
            x = wx + ww // 2 - tw // 2
            y = wy + wh + 5
            if x + tw > sx: x = sx - tw - 4
            if x < 0:       x = 4
            if y + th > sy: y = wy - th - 5   # flip above when near taskbar
            tip.wm_geometry(f"+{x}+{y}")
            self._win = tip
        except Exception:
            self._win = None


# Tooltip text for every button in the main toolbar.
# Used by create_widgets to attach _ToolTip instances.
_BUTTON_TOOLTIPS: dict = {
    "start":   "Start selected updates  [F5]",
    "stop":    "Cancel the running update  [Esc]",
    "retry":   "Re-run components that failed last time",
    "health":  "Probe all tools for versions  [Ctrl+R]",
    "viewlog": "Open the current log file in your default editor",
    "logs":    "Browse and open rotated log files",
    "export":  "Save the health dashboard to TXT, CSV, or JSON",
    "clear":   "Erase log panel text (file log unchanged)  [Ctrl+L]",
    "copy":    "Copy all log text to clipboard  [Ctrl+Shift+C]",
    "settings":"Open settings  [Ctrl+S]",
    "history": "View past run history  [Ctrl+H]",
    "help":    "Show keyboard shortcuts  [F1 / ?]",
}


#==================== GUI =====================
class UpdaterGUI:
    def __init__(self, root, engine):
        self.root    = root
        self.engine  = engine
        self.queue   = queue.Queue()
        self.engine.gui_queue = self.queue
        self._running        = False
        self._health_running = False
        # Running tally of lines in log_widget — avoids a Tcl round-trip
        # (widget.index(tk.END)) on every log batch flush.
        self._log_line_count: int = 0
        # Last value drawn on the progress canvas — skip redraw when
        # progress.set() is called with the same value (e.g. repeated 0% resets).
        self._last_drawn_pct: float = -1.0
        self._last_drawn_w:   int   = 0      # explicit init (was getattr fallback)
        self._last_drawn_h:   int   = 0      # tracks canvas height for skip guard
        self._last_drawn_sck: str   = ""     # Bug fix: was missing from __init__
        self._last_drawn_comp: str  = ""     # Bug fix: was missing from __init__
        self._prog_canvas_w:  int   = 0      # cached from <Configure>; avoids winfo_width() per tick
        self._prog_canvas_h:  int   = 0      # cached from <Configure>; avoids winfo_height() per tick
        # Maps widget id → winfo_class() string. Populated on first
        # _recolour pass; subsequent theme switches reuse the cached value.
        self._widget_class_cache: dict = {}
        self._health_row_ids: Dict[str, str] = {}
        # True once the "Checking..." placeholder row has been removed,
        # so _apply_health_row skips the O(n) get_children() scan thereafter.
        self._health_placeholder_removed: bool = False
        self._health_placeholder_id: "str | None" = None
        self._health_sort_hint_ref = None  # for dim-fg theme correction
        # Per-component status dots updated during a run.
        self._comp_status_labels: Dict[str, tk.Label] = {}
        # Theme correction: frames/seps/labels created in _make_section are stored
        # so _apply_theme can restore their colours after _recolour overwrites them.
        self._section_bg_frames: list = []
        self._section_border_seps: list = []
        self._section_title_labels: list = []
        # Checkbuttons in frame_comps tracked here so _apply_theme
        # can include them in _skip instead of double-configuring via correction loop.
        self._comp_checkbox_widgets: list = []
        # Chip frame widgets — one per component, for theme updates.
        self._comp_chip_frames: dict = {}    # comp_name → tk.Frame (chip)
        self._comp_chip_dots:  dict = {}    # comp_name → tk.Label (dot indicator)
        # Cache the _skip frozenset — rebuilt only when widgets change.
        self._skip_cache: "frozenset | None" = None
        # Timestamp of most recent completed health check.
        self._health_last_checked_var: "tk.StringVar | None" = None
        self._run_start_time: float = 0.0   # set by start_updates; used for elapsed display
        self._health_refresh_id: "str | None" = None  # root.after() token for auto-refresh
        # Log search state: empty string = no filter active.
        self._log_search_var: "tk.StringVar | None" = None
        # Reboot-pending banner widget (shown after Windows Update runs).
        self._reboot_banner: "tk.Frame | None" = None
        # Estimated run duration label variable.
        self._est_dur_var: "tk.StringVar | None" = None
        # System-tray icon (pystray.Icon when active, else None).
        # Initialised here so all access sites use plain self._tray_icon
        # instead of the slower getattr(self, "_tray_icon", None).
        self._tray_icon = None
        # Dialog-open flags — prevent stacking the same dialog twice via
        # rapid key presses (Ctrl+H, Ctrl+S, F1) while wait_window is active.
        self._history_open:   bool = False
        self._settings_open:  bool = False
        self._shortcuts_open: bool = False
        # Python-side cache of start_btn enabled state — avoids a Tcl
        # round-trip (.cget("state")) inside _refresh_start_btn_label.
        self._start_btn_enabled: bool = False
        # Accent top stripe (3 px Frame at very top of window).
        self._top_stripe: "tk.Frame | None" = None
        # Keyboard-hint label in the version bar.
        self._ver_hint_label: "tk.Label | None" = None
        # Reference to the "Components to Update" section title label so
        # _on_components_ready can append an availability count badge.
        self._comp_section_title_lbl: "tk.Label | None" = None
        # Keep strong references to _ToolTip instances so they are not GC'd.
        self._tooltips: list = []
        # Coalescing guard: prevents 13 after(0, _refresh) calls from
        # _select_all (one per var.set) all firing as separate configure().
        self._refresh_start_pending: bool = False
        # Estimated-duration tk.Label — None until create_widgets runs.
        self._est_dur_label = None
        # Status indicator dot label — None until create_widgets runs.
        self._status_dot = None
        # Search entry widget — None until create_widgets runs.
        self._search_entry     = None
        self._search_ph_active = [False]  # mutable cell for placeholder state
        self._search_hl_active: bool = False  # True while search_hl tags exist
        self._search_count_var = None  # match count StringVar
        self._search_count_lbl = None  # match count Label
        # Bottom version bar and label.
        self._ver_bar       = None
        self._version_label = None
        # Search container frame (Entry + ✕ docked together).
        self._search_frame    = None
        self._search_clr_btn  = None
        # 🔍 icon label inside search frame — stored so _apply_theme can
        # correct its bg to widget_bg (not label_bg set by _recolour).
        self._search_icon_lbl: "tk.Label | None" = None
        # Last status dot colour key (theme dict key) for theme-switch refresh.
        self._status_colour_key: str = "dot_idle"
        # Segmented progress bar data — populated by start_updates.
        self._prog_segments: list  = []     # [(comp_name, display_name), ...]
        self._prog_seg_states: dict = {}    # comp_name → state string
        self._prog_current_comp: str = ""   # display name of running component
        _dark_mode: bool = bool(self.engine.config.get("dark_mode", False))
        self._dark = tk.BooleanVar(value=_dark_mode)
        # Cached log-filter minimum — avoids a StringVar.get() Tcl call on
        # every update_gui tick. Refreshed by the level-panel pick callback.
        self._cur_min_level: int = 0  # "All" = 0
        # Cached dark-mode flag — avoids BooleanVar.get() Tcl calls inside
        # _make_btn hover callbacks (fires on every mouse-enter/leave event).
        self._is_dark: bool = _dark_mode
        _dr_start = self.engine.config.get("dry_run", False)
        self.root.title(
            f"Windows Updater {VERSION} [DRY RUN]"
            if _dr_start else f"Windows Updater {VERSION}")
        self._setup_geometry()          # DPI-aware size + centred placement
        self._row_height      = int(24 * self._scale)  # treeview row height (DPI-scaled)
        self._prog_font_size  = max(8, int(9  * self._scale))  # progress bar label font size
        self._ttk_style = ttk.Style(self.root)   # cached — avoids Tk lookup on every theme switch
        self._ttk_style.theme_use("clam")
        # Set Treeview layout once — structure is theme-independent;
        # calling this in _apply_theme on every theme switch was wasteful.
        self._ttk_style.layout("Treeview",
                               [("Treeview.treearea", {"sticky": "nswe"})])
        self.create_widgets()
        self._apply_theme()
        self.update_gui()
        # Apply OS titlebar colour now that the window handle exists.
        self.root.update_idletasks()
        self._apply_titlebar_theme()
        threading.Thread(target=self.engine.probe_components,
                         name="probe-components", daemon=True).start()
        # Graceful close — cancel any running update before destroying the window.
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        # Keyboard shortcuts
        self.root.bind("<F5>",      lambda _e: self.start_updates() if not self._running else None)
        self.root.bind("<F1>",      lambda _e: self._show_shortcuts())
        self.root.bind("<Escape>",  lambda _e: self.engine.cancel() if self._running else None)
        self.root.bind("<Control-r>", lambda _e: self.populate_health() if not self._health_running else None)
        self.root.bind("<Control-l>", lambda _e: self._clear_log())
        self.root.bind("<Control-Shift-C>", lambda _e: self._copy_log())
        self.root.bind("<Control-d>",       lambda _e: self._toggle_dry_run())
        self.root.bind("<Control-h>",       lambda _e: self._show_history())
        self.root.bind("<Control-s>",       lambda _e: self.open_settings())
        # Ctrl+A / Ctrl+Shift+A — skip when a text-input widget has focus
        # so the native "select all text" behaviour in Entry/Spinbox is preserved.
        def _ctrl_a(_e):
            if not isinstance(self.root.focus_get(),
                              (tk.Entry, tk.Spinbox, tk.Text)):
                self._select_all_components()
        def _ctrl_shift_a(_e):
            if not isinstance(self.root.focus_get(),
                              (tk.Entry, tk.Spinbox, tk.Text)):
                self._deselect_all_components()
        self.root.bind("<Control-a>", _ctrl_a)
        self.root.bind("<Control-A>", _ctrl_shift_a)
        # Ctrl+F focuses the search entry and selects all text in it.
        def _ctrl_f(_e):
            if self._search_entry is not None:
                if self._search_ph_active[0]:
                    # Clear placeholder — reconnect StringVar (Tk syncs Entry to "")
                    self._search_entry.configure(textvariable="")
                    self._search_entry.delete(0, "end")
                    self._search_entry.configure(
                        textvariable=self._log_search_var,
                        fg=self._theme["widget_fg"])
                    self._search_ph_active[0] = False
                self._search_entry.focus_set()
                self._search_entry.select_range(0, "end")
        self.root.bind("<Control-f>", _ctrl_f)
        # Reveal the window now that geometry, theme, and widgets are all ready.
        # If start_minimised is set and tray is available, go straight to tray.
        if (self.engine.config.get("start_minimised", False) and _TRAY_AVAILABLE):
            self._setup_tray()
        else:
            self.root.deiconify()

    def _on_close(self):
        """Called when the user clicks the window's X button.

        If pystray is available and an update is running, minimise to tray
        so the update can finish silently.  Otherwise confirm and exit.
        """
        if self._running and _TRAY_AVAILABLE:
            self.root.withdraw()
            self._setup_tray()
            return
        if self._running or self._health_running:
            if self._running:
                _msg = "An update run is in progress.\n\nCancel it and close?"
            else:
                _msg = "A health check is in progress.\n\nCancel it and close?"
            if not self._msgbox("yesno", "Close", _msg):
                return
            self.engine.cancel()
        self._cancel_health_refresh()
        self._remove_tray()
        self._save_window_geometry()
        self.root.destroy()

    def _save_window_geometry(self):
        """Persist current window size and position to config.

        Skips saving when the window is maximised ('zoomed') or iconic so we
        never restore to a locked-in maximised size or a pre-iconify stale size.
        """
        try:
            state = self.root.wm_state()
            if state in ("iconic", "withdrawn", "zoomed"):
                return
            geom = self.root.wm_geometry()   # "WxH+X+Y"
            m = re.fullmatch(r"(\d+)x(\d+)\+(-?\d+)\+(-?\d+)", geom)
            if m:
                w, h, x, y = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
                with self.engine.config_lock:
                    self.engine.config.update({
                        "window_w": w, "window_h": h,
                        "window_x": x, "window_y": y,
                    })
                    snap = copy.deepcopy(self.engine.config)
                save_config(snap)
        except Exception:
            pass  # geometry save is best-effort — never crash on close

    def _setup_tray(self):
        """Create a system-tray icon (requires pystray + Pillow)."""
        if not _TRAY_AVAILABLE or self._tray_icon:
            return
        # 64×64 RGBA with rounded corners for crisp display on high-DPI taskbars.
        _sz = 64
        img = _PILImage.new("RGBA", (_sz, _sz), (0, 0, 0, 0))
        try:
            from PIL import ImageDraw as _IDraw
            draw = _IDraw.Draw(img)
            r = _sz // 6          # corner radius
            fill = (0, 120, 212, 255)   # #0078d4 opaque
            draw.rounded_rectangle([0, 0, _sz - 1, _sz - 1], radius=r, fill=fill)
            # Simple white "U" letter as a logo mark
            lw = max(2, _sz // 12)
            lm = _sz // 5
            draw.rectangle([lm, lm, lm + lw, _sz - lm], fill=(255, 255, 255, 255))
            draw.rectangle([_sz - lm - lw, lm, _sz - lm, _sz - lm], fill=(255, 255, 255, 255))
            draw.rectangle([lm, _sz - lm - lw, _sz - lm, _sz - lm], fill=(255, 255, 255, 255))
        except Exception:
            img = _PILImage.new("RGB", (_sz, _sz), color="#0078d4")

        def _show(_icon, _item):
            self.root.after(0, self._restore_from_tray)

        def _quit(_icon, _item):
            self.engine.cancel()
            _icon.stop()
            self.root.after(0, self.root.destroy)

        menu = pystray.Menu(
            pystray.MenuItem("Open", _show, default=True),
            pystray.MenuItem("Quit", _quit),
        )
        self._tray_icon = pystray.Icon(
            "updater", img, f"Windows Updater {VERSION}", menu
        )
        threading.Thread(target=self._tray_icon.run,
                         name="tray-icon", daemon=True).start()

    def _stop_tray_icon(self):
        """Stop the pystray icon and clear the reference (no-op if not running)."""
        icon = self._tray_icon
        if icon:
            try:
                icon.stop()
            except Exception:
                pass
            self._tray_icon = None

    def _restore_from_tray(self):
        """Restore the main window from the system tray."""
        self._stop_tray_icon()
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()

    def _remove_tray(self):
        """Stop the tray icon if active."""
        self._stop_tray_icon()

    @property
    def _theme(self):
        """Return the active theme dict (dark or light) without a Tcl round-trip."""
        # _is_dark is a Python bool kept in sync by _apply_theme and
        # open_settings._save — avoids a BooleanVar.get() Tcl call per access.
        return THEMES["dark"] if self._is_dark else THEMES["light"]

    # ── Resolution / DPI adaptation ───────────────────────────────────────────
    def _setup_geometry(self):
        """Set window size and position based on actual screen dimensions and DPI.

        self._scale: float ratio of actual DPI to the 96-dpi baseline.
        - 96 dpi  → 1.00  (standard laptop / desktop)
        - 120 dpi → 1.25  (125 % Windows scaling)
        - 144 dpi → 1.50  (150 %)
        - 192 dpi → 2.00  (200 %, 4K at native)
        UI elements that specify pixel sizes (canvas height, treeview row height,
        paddings) are multiplied by self._scale so they appear physically consistent
        across displays.
        """
        self.root.update_idletasks()   # ensure winfo values are populated

        # Actual DPI reported by Tk (may differ from Windows "effective" DPI on
        # multi-monitor setups — that's fine; we just need a reasonable scale).
        try:
            dpi = self.root.winfo_fpixels('1i')
        except tk.TclError:
            dpi = 96.0
        self._scale = max(1.0, round(dpi / 96.0, 2))

        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()

        # Target 85 % of screen area; clamp to sensible absolute bounds.
        w = int(min(max(sw * 0.85, 1100 * self._scale), 1600 * self._scale))
        h = int(min(max(sh * 0.85,  720 * self._scale), 1000 * self._scale))

        # Centre the window.
        x = max(0, (sw - w) // 2)
        y = max(0, (sh - h) // 2)

        # Restore saved geometry if the window fits on the current screen.
        _cfg     = self.engine.config
        _saved_w = _cfg.get("window_w", -1)
        _saved_h = _cfg.get("window_h", -1)
        _saved_x = _cfg.get("window_x", -1)
        _saved_y = _cfg.get("window_y", -1)
        if (_saved_w > 0 and _saved_h > 0
                and _saved_x >= 0 and _saved_y >= 0
                and _saved_x + _saved_w <= sw + 50   # allow slight off-edge
                and _saved_y + _saved_h <= sh + 50):
            w, h, x, y = _saved_w, _saved_h, _saved_x, _saved_y
        self.root.geometry(f"{w}x{h}+{x}+{y}")
        self.root.minsize(int(900 * self._scale), int(640 * self._scale))

    def _apply_theme(self):
        """Apply the current dark/light theme to all widgets."""
        if not hasattr(self, "log_widget"):
            return
        # Update _is_dark cache BEFORE reading self._theme: the property uses
        # _is_dark directly (no BooleanVar.get() call), so it must reflect the
        # current dark-mode state before t is bound. Without this ordering,
        # toggling dark mode in Settings causes _apply_theme to apply the OLD
        # theme dict for the entire call, leaving widgets with wrong colours.
        self._is_dark = self._dark.get()  # refresh cache; _theme property reads this
        t = self._theme
        # Pre-bind the most-accessed keys (×6-8 each) to avoid repeated
        # dict lookups across the ~120 t[k] accesses in this method.
        _accent       = t["accent"]
        _accent_fg    = t["accent_fg"]
        _t_fg         = t["fg"]
        _t_border     = t["border"]
        _sb_thumb     = t["scrollbar_thumb"]
        _sb_trough    = t["scrollbar_trough"]
        _sb_hover     = t["scrollbar_hover"]
        _tag_debug    = t["tag_debug"]
        _widget_bg    = t["widget_bg"]
        _widget_fg    = t["widget_fg"]
        _tag_info     = t["tag_info"]
        _btn_hover    = t["btn_hover"]
        _label_bg     = t["label_bg"]
        _section_bg   = t["section_bg"]
        _btn_bg       = t["btn_bg"]
        _t_bg         = t["bg"]
        _frame_bg     = t["frame_bg"]
        self.root.configure(bg=_t_bg)
        style = self._ttk_style   # reuse cached Style object

        # ── Treeview (flat headings, no border) ───────────────────────────────
        style.configure("Treeview",
                        background=_widget_bg,
                        foreground=_widget_fg,
                        fieldbackground=_widget_bg,
                        borderwidth=0,
                        relief="flat",
                        rowheight=self._row_height,
                        font=("Segoe UI", 9))
        style.configure("Treeview.Heading",
                        background=_section_bg,
                        foreground=_t_fg,
                        relief="flat",
                        font=("Segoe UI", 9, "bold"))
        style.map("Treeview",
                  background=[("selected", _accent)],
                  foreground=[("selected", _accent_fg)])
        style.map("Treeview.Heading", background=[("active", _t_border)])

        # ── Flat thin ttk scrollbars (no arrows, full colour control) ─────────
        # arrowsize=0 + arrowcolor=trough visually hides the end-cap buttons.
        # Layout override removes the arrow elements structurally so their
        # allocated space is reclaimed and the trough/thumb colours are not
        # partially overridden by the Windows visual-styles engine.
        for orient, size_kw in (
                ("Vertical",   {"width": 8}),
                ("Horizontal", {"width": 8})):
            sty_name = f"{orient}.TScrollbar"
            style.configure(sty_name,
                            background=_sb_thumb,
                            troughcolor=_sb_trough,
                            darkcolor=_sb_thumb,
                            lightcolor=_sb_thumb,
                            bordercolor=_sb_trough,
                            arrowcolor=_sb_trough,
                            borderwidth=0,
                            relief="flat",
                            arrowsize=0,
                            **size_kw)
            style.map(sty_name,
                      background=[("active",   _sb_hover),
                                  ("pressed",  _sb_hover),
                                  ("disabled", _sb_trough)],
                      darkcolor= [("active",   _sb_hover)],
                      lightcolor=[("active",   _sb_hover)],
                      troughcolor=[("disabled", _sb_trough)])
            # (No layout() call — colours handled by configure/map above.)

        # ── Flat separator ────────────────────────────────────────────────────
        style.configure("TSeparator", background=_t_border)

        # _skip_cache frozenset: rebuilt when None (invalidated by
        # _on_components_ready after new widgets are added).
        if self._skip_cache is None:
            _s: set = set()
            for _w in self._section_bg_frames:
                try: _s.add(_w._w)
                except Exception: pass
            for _w in self._section_border_seps:
                try: _s.add(_w._w)
                except Exception: pass
            for _w in self._section_title_labels:
                try: _s.add(_w._w)
                except Exception: pass
            for _w in self._comp_status_labels.values():
                try: _s.add(_w._w)
                except Exception: pass
            try: _s.add(self._health_ts_label._w)
            except Exception: pass
            for _w in self._comp_checkbox_widgets:
                try: _s.add(_w._w)
                except Exception: pass
            # Search entry + container frame + count label are explicitly themed.
            try:
                if self._search_entry is not None:
                    _s.add(self._search_entry._w)
                if self._search_frame is not None:
                    _s.add(self._search_frame._w)
                if self._search_clr_btn is not None:
                    _s.add(self._search_clr_btn._w)
                if self._search_count_lbl is not None:
                    _s.add(self._search_count_lbl._w)
            except Exception: pass
            self._skip_cache = frozenset(_s)
        self._recolour(self.root, t, self._skip_cache)

        # ── Log widget ────────────────────────────────────────────────────────
        self.log_widget.configure(
            bg=t["log_bg"], fg=_tag_info,
            insertbackground=_t_fg,
            selectbackground=_accent,
            selectforeground=_accent_fg,
            highlightbackground=_t_border,
            highlightthickness=0,
            font=("Consolas", 9),   # monospace keeps columns aligned
            padx=8, pady=6,
            spacing1=1,             # 1 px above each line
            spacing3=1,             # 1 px below each line
        )
        self.log_widget.tag_configure("info",  foreground=_tag_info)
        self.log_widget.tag_configure("debug", foreground=_tag_debug)
        self.log_widget.tag_configure("warn",  foreground=t["tag_warn"])
        self.log_widget.tag_configure("error", foreground=t["tag_error"])
        # IMPORTANT: tag_configure() silently resets elide to False.
        # Re-apply the log-level filter immediately so the chosen level is
        # honoured after a dark/light theme switch.
        self._apply_log_filter()
        # Timestamp tag — same dim colour as debug, narrower font.
        self.log_widget.tag_configure(
            "ts",
            foreground=_tag_debug,
            font=("Consolas", 8),
        )
        # Header tag: accent background + bold, with space above.
        _hdr_bg = t["section_bg"]
        self.log_widget.tag_configure(
            "header",
            foreground=_accent,
            background=_hdr_bg,
            font=("Consolas", 9, "bold"),
            spacing1=6,   # breathing room above section headers
        )
        # Search entry — theme bg/fg/cursor to match dark/light mode.
        if self._search_entry is not None:
            try:
                # Placeholder fg uses tag_debug; real input uses widget_fg.
                _se_fg = _tag_debug if self._search_ph_active[0] else _widget_fg
                self._search_entry.configure(
                    bg=_widget_bg, fg=_se_fg,
                    insertbackground=_t_fg,
                    highlightbackground=_t_border,
                    highlightthickness=0,
                )
                if self._search_frame is not None:
                    _sf_hl = self._theme["accent"] \
                        if self._search_entry == self.root.focus_get() \
                        else _t_border
                    self._search_frame.configure(
                        bg=_widget_bg,
                        highlightbackground=_sf_hl,
                    )
                if self._search_clr_btn is not None:
                    self._search_clr_btn.configure(
                        bg=_widget_bg,
                        activebackground=_btn_hover,
                    )
                if self._search_icon_lbl is not None:
                    self._search_icon_lbl.configure(bg=_widget_bg)
            except tk.TclError:
                pass
        # search_hl: configured here so _on_log_search skips tag_configure
        # (accent colours only change on theme switch, not per keystroke).
        self.log_widget.tag_configure(
            "search_hl",
            background=_accent,
            foreground=_accent_fg,
        )

        # ── Health treeview row tags ──────────────────────────────────────────
        self.tree.tag_configure("good", background=t["tree_good"])
        self.tree.tag_configure("bad",  background=t["tree_bad"])
        self.tree.tag_configure("warn", background=t["tree_warn"])
        self.tree.tag_configure("alt",  background=t["tree_alt"])

        # ── Log-level button ──────────────────────────────────────────────────
        if hasattr(self, "_log_level_btn"):
            try:
                self._log_level_btn.configure(
                    bg=_btn_bg, fg=t["btn_fg"],
                    activebackground=_btn_hover,
                    activeforeground=_t_fg,
                    relief="flat", font=("Segoe UI", 9),
                )
            except tk.TclError:
                pass

        # ── Accent on Start Updates button ────────────────────────────────────
        state = self.start_btn.cget("state")
        if state == "disabled":
            self.start_btn.configure(
                bg=_btn_bg, fg=_t_fg,
                disabledforeground=_tag_debug)
        else:
            self.start_btn.configure(
                bg=_accent, fg=_accent_fg,
                activebackground=_accent, activeforeground=_accent_fg)

        # Pre-bind the two most-accessed theme values for the correction loops.
        # _section_bg appears 9×, _t_fg appears 9× below — binding them
        # once saves 16 dict __getitem__ calls per theme switch.
        _sbg = _section_bg  # alias — same value
        _cfg = _t_fg

        # ── Post-recolour corrections: restore section-card widgets ───────────
        # _recolour sets Frames→frame_bg, Labels→label_bg, Checkbuttons→frame_bg
        # unconditionally, overwriting colours set at creation for widgets inside
        # section cards (section_bg) and their 1-px separators (border).
        # The loops below restore those widgets after _recolour completes.

        # Section inner/hdr/content frames → section_bg
        for f in self._section_bg_frames:
            try:
                f.configure(bg=_sbg)
            except tk.TclError:
                pass
        # 1-px separator frames → border
        for sep in self._section_border_seps:
            try:
                sep.configure(bg=_t_border)
            except tk.TclError:
                pass
        # Section title labels → section_bg
        for lbl in self._section_title_labels:
            try:
                lbl.configure(bg=_sbg, fg=_cfg)
            except tk.TclError:
                pass
        # Component status dot labels → section_bg
        for dot in self._comp_status_labels.values():
            try:
                dot.configure(bg=_sbg, fg=_cfg)
            except tk.TclError:
                pass
        # 'Last checked' timestamp label → section_bg
        try:
            self._health_ts_label.configure(bg=_sbg, fg=_cfg)
        except tk.TclError:
            pass
        # Health sort hint stays dim (secondary text) after _recolour.
        try:
            if self._health_sort_hint_ref is not None:
                self._health_sort_hint_ref.configure(bg=_sbg, fg=_tag_debug)
        except tk.TclError:
            pass
        # Theme pill chips — drive each chip's _refresh by reading comp_vars.
        for _cname, _chip in self._comp_chip_frames.items():
            try:
                _var = self.comp_vars.get(_cname)
                if _var is not None:
                    _var.set(_var.get())  # trigger trace → _refresh
            except Exception:
                pass

        # ── Canvas progress bar ───────────────────────────────────────────────
        self._prog_canvas.configure(bg=_t_bg)

        self._apply_titlebar_theme()
        # Force progress bar to redraw with new theme colours on switch.
        self._last_drawn_pct  = -1.0
        self._last_drawn_w    = 0
        self._last_drawn_h    = 0
        self._last_drawn_sck  = ""
        self._last_drawn_comp = ""
        self._redraw_progress()
        # Status dot — refresh bg AND fg from new theme after switch.
        if self._status_dot is not None:
            try:
                self._status_dot.configure(
                    bg=_label_bg,
                    fg=t.get(self._status_colour_key, t["dot_idle"]),
                )
            except tk.TclError:
                pass
        # Estimated duration label colour.
        if self._est_dur_label is not None:
            try:
                self._est_dur_label.configure(bg=_label_bg, fg=_tag_debug)
            except tk.TclError:
                pass
        # Search match-count label colour.
        if self._search_count_lbl is not None:
            try:
                self._search_count_lbl.configure(bg=_label_bg, fg=_tag_debug)
            except tk.TclError:
                pass
        # Accent top stripe — fixed accent; restored after _recolour overwrites it.
        if self._top_stripe is not None:
            try:
                self._top_stripe.configure(bg=_accent)
            except tk.TclError:
                pass
        # Version bar and label.
        if self._version_label is not None:
            try:
                self._ver_bar.configure(bg=_frame_bg)
                self._version_label.configure(bg=_frame_bg, fg=_tag_debug)
                if self._ver_hint_label is not None:
                    self._ver_hint_label.configure(bg=_frame_bg, fg=_tag_debug)
            except tk.TclError:
                pass
        # Reboot banner — fixed amber; must be re-applied after _recolour
        # visits the banner children (Label + Button) and overwrites them.
        if self._reboot_banner is not None:
            try:
                _banner_children = self._reboot_banner.winfo_children()
                self._reboot_banner.configure(bg="#b35c00")
                for _bw in _banner_children:
                    try:
                        _bw.configure(bg="#b35c00", fg="#ffffff")
                    except tk.TclError:
                        pass
            except tk.TclError:
                pass

    # Widget classes that never have tkinter children — winfo_children()
    # on these always returns [] so we skip the Tcl round-trip entirely.
    _LEAF_CLASSES = frozenset({
        "Label", "Checkbutton", "Button", "Scrollbar",
        "Spinbox", "Canvas", "Text", "Entry", "Listbox",
    })

    def _recolour(self, widget, t, _skip: "frozenset | set | None" = None):
        """Recursively apply theme colours to widget and its children."""
        # Pre-bind hot keys — saves repeated dict lookups across every
        # recursive call (O(widget_count) calls per theme switch).
        _fg        = t["fg"]
        _frm_bg    = t["frame_bg"]
        _wid_bg    = t["widget_bg"]
        _wid_fg    = t["widget_fg"]
        _brd       = t["border"]
        _accent    = t["accent"]
        _btn_bg    = t["btn_bg"]
        # Use widget._w (Tk path string) as cache key — id() recycles
        # addresses after destruction, but _w is unique for widget lifetime.
        wkey = widget._w
        # Resolve class first — needed by both the _skip and normal paths.
        cls  = self._widget_class_cache.get(wkey)
        if cls is None:
            cls = widget.winfo_class()
            # Bound cache size — transient Toplevel dialogs each
            # add ~25 entries; clear at 300 to prevent unbounded growth.
            if len(self._widget_class_cache) > 500:
                self._widget_class_cache.clear()
            self._widget_class_cache[wkey] = cls
        # Skip widgets owned by the correction loops in _apply_theme.
        if _skip and wkey in _skip:
            # Leaf widgets in _skip have no children — skip the
            # winfo_children() Tcl round-trip for them entirely.
            if cls in self._LEAF_CLASSES:
                return
            for child in widget.winfo_children():
                self._recolour(child, t, _skip)
            return
        try:
            if cls == "Frame":
                widget.configure(bg=_frm_bg)
            elif cls == "Labelframe":
                widget.configure(bg=t["section_bg"], fg=_fg)
            elif cls == "Label":
                widget.configure(bg=t["label_bg"], fg=_fg,
                                 font=("Segoe UI", 9))
            elif cls == "Checkbutton":
                widget.configure(bg=_frm_bg, fg=_fg,
                                 selectcolor=_accent,
                                 activebackground=_frm_bg,
                                 activeforeground=_fg,
                                 relief="flat",
                                 font=("Segoe UI", 9))
            elif cls == "Button":
                # Leave start_btn alone — _apply_theme handles accent colouring.
                # start_btn always exists when _recolour runs
                # (create_widgets sets it before _apply_theme calls _recolour).
                # Direct identity check avoids the hasattr() overhead.
                if widget is self.start_btn:
                    return
                widget.configure(bg=_btn_bg, fg=t["btn_fg"],
                                 activebackground=t["btn_hover"],
                                 activeforeground=_fg,
                                 relief="flat", borderwidth=0,
                                 font=("Segoe UI", 9),
                                 padx=10, pady=4)
            elif cls == "Scrollbar":
                widget.configure(bg=t["scrollbar_thumb"],
                                 troughcolor=t["scrollbar_trough"],
                                 activebackground=t["scrollbar_hover"],
                                 relief="flat", borderwidth=0,
                                 width=8)
            elif cls == "Entry":
                widget.configure(bg=_wid_bg, fg=_wid_fg,
                                 insertbackground=_fg,
                                 highlightbackground=_brd,
                                 highlightthickness=1,
                                 relief="flat",
                                 font=("Segoe UI", 9))
            elif cls == "Listbox":
                widget.configure(bg=_wid_bg, fg=_wid_fg,
                                 selectbackground=_accent,
                                 selectforeground=t["accent_fg"],
                                 highlightbackground=_brd,
                                 highlightthickness=1,
                                 relief="flat",
                                 font=("Segoe UI", 9))
            elif cls == "Canvas":
                # Canvases are themed explicitly in _apply_theme.
                # _recolour skips them to avoid overwriting accent/bg colours.
                pass
            elif cls == "Spinbox":
                widget.configure(bg=_wid_bg, fg=_wid_fg,
                                 insertbackground=_fg,
                                 buttonbackground=_btn_bg,
                                 relief="flat", borderwidth=1,
                                 highlightbackground=_brd,
                                 highlightthickness=1,
                                 font=("Segoe UI", 9))
        except tk.TclError:
            pass
        if cls not in self._LEAF_CLASSES:
            for child in widget.winfo_children():
                self._recolour(child, t, _skip)

    # ── Windows dark titlebar ─────────────────────────────────────────────────
    # DWM attribute 20 = DWMWA_USE_IMMERSIVE_DARK_MODE (Windows 11 / Win10 ≥ 2004)
    # Attribute 19 is the undocumented equivalent for older Win10 builds.
    # Silently ignored on non-Windows or when the window handle is unavailable.
    _DWMWA_USE_IMMERSIVE_DARK_MODE   = 20
    _DWMWA_USE_IMMERSIVE_DARK_MODE_OLD = 19

    def _apply_titlebar_theme(self, win=None):
        """Tell DWM to render the titlebar of *win* (or the root) in dark/light mode.

        For tk.Tk() the real Win32 HWND that owns the titlebar is the *parent*
        of Tk's embedded HWND, so we use GetParent().  For tk.Toplevel the Tk
        HWND IS the top-level Win32 window; GetParent() returns 0 (desktop), so
        we fall back to winfo_id() directly.  Both candidates are tried in order.
        """
        if platform.system() != "Windows":
            return
        target = win if win is not None else self.root
        dark   = ctypes.c_int(1 if self._is_dark else 0)
        dwm    = ctypes.windll.dwmapi
        # Collect HWND candidates: parent-window first, then the widget itself.
        try:
            raw_id = target.winfo_id()
            parent = ctypes.windll.user32.GetParent(raw_id)
            hwnds  = [h for h in (parent, raw_id) if h]
            for hwnd in hwnds:
                for attr in (self._DWMWA_USE_IMMERSIVE_DARK_MODE,
                             self._DWMWA_USE_IMMERSIVE_DARK_MODE_OLD):
                    try:
                        dwm.DwmSetWindowAttribute(
                            hwnd, attr,
                            ctypes.byref(dark), ctypes.sizeof(dark)
                        )
                        break
                    except OSError:
                        continue
        except Exception:
            pass  # Silently ignore on unsupported OS/builds

    def _on_prog_resize(self, e):
        """Cache canvas width from the <Configure> event (no Tcl call).

        Replaces the previous `lambda _e: self._redraw_progress()` binding.
        Storing e.width here means _redraw_progress() never needs to call
        c.winfo_width() — eliminating one Tcl round-trip per update_gui tick.
        """
        self._prog_canvas_w = e.width
        self._prog_canvas_h = e.height
        self._redraw_progress()

    def _redraw_progress(self):
        """Repaint the progress bar — flat two-layer design.

        Returns immediately when the window is withdrawn (tray mode) — no
        visible canvas, so all Tcl drawing calls would be wasted work.

        Layout (24 px tall at 1x scale):
          Top 20 px  — transparent label area (bg matches window)
          Bottom 4 px — solid accent-coloured progress stripe

        Idle (pct=0, not running): canvas is blank — takes no visual space.
        Running:
          - Label area: arrow + ComponentName left, N/M right (grey text)
          - Stripe: accent-blue fill proportional to overall progress
        Done / error:
          - Label area: blank
          - Stripe: full-width dot_done green or dot_error red
        """
        c    = self._prog_canvas
        pct  = min(max(self._progress_pct, 0), 100)
        w    = self._prog_canvas_w
        h    = self._prog_canvas_h
        _sck = self._status_colour_key
        _cur = self._prog_current_comp

        if (pct == self._last_drawn_pct and w == self._last_drawn_w
                and h == self._last_drawn_h
                and _sck == self._last_drawn_sck
                and _cur == self._last_drawn_comp):
            return
        if w < 2 or h < 4:
            return

        t = self._theme
        self._last_drawn_pct  = pct
        self._last_drawn_w    = w
        self._last_drawn_h    = h
        self._last_drawn_sck  = _sck
        self._last_drawn_comp = _cur

        c.delete("all")

        # Idle and empty → leave canvas blank (invisible)
        if pct <= 0 and not self._running:
            return

        _bg      = t["bg"]
        _stripe_h = max(3, h // 6)          # bottom stripe: ~4 px at 24px height
        _label_h  = h - _stripe_h            # top label area height
        _mid      = _label_h // 2 + 1        # vertical centre of label area

        # ── Label area background (flush with window bg) ──────────────────
        if self._running and _cur:
            c.create_rectangle(0, 0, w, _label_h, fill=_bg, outline="")

        # ── Progress stripe ────────────────────────────────────────────────
        stripe_y0 = _label_h
        stripe_y1 = h

        # Track (full-width stripe background)
        c.create_rectangle(0, stripe_y0, w, stripe_y1,
                           fill=t["border"], outline="")

        # Fill (proportional, status-aware colour)
        if _sck == "dot_error":
            _fill = t["dot_error"]
            fill_w = w   # full-width on error
        elif _sck == "dot_done" or pct >= 100:
            _fill = t["dot_done"]
            fill_w = w   # full-width on completion
        else:
            _fill  = t["accent"]
            fill_w = max(0, int(w * pct / 100))

        if fill_w > 0:
            c.create_rectangle(0, stripe_y0, fill_w, stripe_y1,
                               fill=_fill, outline="")

        # ── Labels (only while running) ────────────────────────────────────
        if not self._running:
            return

        _font   = ("Segoe UI", self._prog_font_size)
        _fg     = t["tag_debug"]   # muted grey — labels are secondary info

        # Left: arrow + current component name
        if _cur:
            _left = f"▶  {_cur}"
            c.create_text(8, _mid, text=_left, anchor="w",
                          fill=_fg, font=_font)

        # Right: "done / total  47%" — fraction + percentage
        segs   = self._prog_segments
        n_seg  = len(segs)
        _pct_str = f"{pct:.0f}%"
        if n_seg > 0:
            _states = self._prog_seg_states
            done_n  = sum(1 for cn, _ in segs
                          if _states.get(cn, "pending") in ("done", "error"))
            _right  = f"{done_n} / {n_seg}  {_pct_str}"
        else:
            _right  = _pct_str
        c.create_text(w - 8, _mid, text=_right, anchor="e",
                      fill=_fg, font=_font)


    @staticmethod
    def _fmt_elapsed(seconds: float) -> str:
        """Format a duration in seconds as a human-readable string."""
        secs = int(seconds)
        if secs < 60:
            return f"{secs} s"
        mins, secs = divmod(secs, 60)
        return f"{mins} m {secs:02d} s"

    def _set_status(self, text: str, colour: str = "",
                    dot_key: str = "") -> None:
        """Set status text and update the indicator dot colour.

        colour : a hex string, or "" to auto-derive from the text keyword.
        dot_key: theme key ("dot_running", "dot_done", etc.) that overrides
                 both the auto-derived key AND the hex lookup.  Use this when
                 you need the dot to survive a theme switch correctly but the
                 text itself doesn't contain a matching keyword.

        dot_running (blue) : running, starting, refreshing, checking, restarting
        dot_done    (green): completed, up-to-date
        dot_error   (red)  : error, failed, cancelled
        dot_idle    (grey) : everything else
        """
        self.status_var.set(text)
        if dot_key:
            # Caller supplied an explicit key — use it directly so that
            # _apply_theme can restore the correct dot colour after a
            # dark/light switch without re-parsing the text.
            _key = dot_key
        else:
            _t = text.lower()
            if any(k in _t for k in _STATUS_KW_RUNNING):
                _key = "dot_running"
            elif any(k in _t for k in _STATUS_KW_ERROR):
                _key = "dot_error"
            elif any(k in _t for k in _STATUS_KW_DONE):
                _key = "dot_done"
            else:
                _key = "dot_idle"
        self._status_colour_key = _key  # persist for theme-switch refresh
        if not colour:
            colour = self._theme.get(_key, self._theme["dot_idle"])
        if self._status_dot is not None:
            try:
                self._status_dot.configure(fg=colour)
            except tk.TclError:
                pass

    @staticmethod
    def _idle_status(dry_run: bool) -> str:
        """Return the idle status string, prefixed for dry-run mode."""
        return "[DRY RUN] Idle" if dry_run else "Idle"

    # ── Flat-button factory with hover effect ─────────────────────────────────
    def _make_btn(self, parent, text, command, state="normal", accent=False):
        """Create a flat tk.Button with mouse-enter/leave hover colouring."""
        t  = self._theme
        bg = t["accent"]    if accent else t["btn_bg"]
        fg = t["accent_fg"] if accent else t["btn_fg"]
        b  = tk.Button(parent, text=text, command=command, state=state,
                       bg=bg, fg=fg, relief="flat", borderwidth=0,
                       activebackground=t["btn_hover"],
                       activeforeground=t["fg"],
                       font=("Segoe UI", 9), padx=10, pady=4,
                       cursor="hand2")
        def _enter(e):
            if b.cget("state") == "disabled":
                return
            # THEMES direct lookup avoids BooleanVar.get() Tcl call per hover.
            t2 = THEMES["dark" if self._is_dark else "light"]
            b.configure(bg=t2["btn_hover"] if not accent else t2["accent"],
                        fg=t2["fg"]        if not accent else t2["accent_fg"])
        def _leave(e):
            if b.cget("state") == "disabled":
                return
            t2 = THEMES["dark" if self._is_dark else "light"]
            b.configure(bg=t2["accent"] if accent else t2["btn_bg"],
                        fg=t2["accent_fg"] if accent else t2["btn_fg"])
        b.bind("<Enter>", _enter)
        b.bind("<Leave>", _leave)
        return b

    def _make_close_x(self, parent_hdr, on_close, bg, fg_dim, fg_normal):
        """Themed ✕ close button used in every panel/dialog header.

        Single shared factory so every panel (log menu, history, msgbox,
        settings-nested dialogs, ...) gets identical sizing, cursor, and
        hover colouring — dim by default, brightens to fg_normal on hover.
        on_close is called with zero arguments; pass a callable that
        already has its own _e=None default if it is also used as a
        direct <Escape>/<Destroy> binding elsewhere.
        """
        x = tk.Label(parent_hdr, text="✕", bg=bg, fg=fg_dim,
                     font=("Segoe UI", 10), padx=10, pady=6, cursor="hand2")
        x.pack(side="right")
        x.bind("<Button-1>", lambda _e: on_close())
        x.bind("<Enter>", lambda _e: x.configure(fg=fg_normal))
        x.bind("<Leave>", lambda _e: x.configure(fg=fg_dim))
        return x

    def _make_section(self, parent, title, side="bottom"):
        """Flat card: 1-px border frame + inner content frame with section label."""
        t        = self._theme
        border_f = tk.Frame(parent, bg=t["border"], bd=0)
        border_f.pack(side=side, fill="x", padx=10, pady=(0, 8))
        inner    = tk.Frame(border_f, bg=t["section_bg"], bd=0)
        inner.pack(fill="x", padx=1, pady=1)
        hdr      = tk.Frame(inner, bg=t["section_bg"], bd=0)
        hdr.pack(fill="x")
        title_lbl = tk.Label(hdr, text=title,
                             bg=t["section_bg"], fg=t["fg"],
                             font=("Segoe UI", 9, "bold"),
                             padx=8, pady=4)
        title_lbl.pack(side="left")
        sep = tk.Frame(inner, bg=t["border"], height=1, bd=0)
        sep.pack(fill="x")
        content  = tk.Frame(inner, bg=t["section_bg"], bd=0)
        content.pack(fill="x")
        # Register for explicit re-colouring after _recolour() runs in _apply_theme.
        for f in (inner, hdr, content):
            self._section_bg_frames.append(f)
        # track border_f (outer 1-px frame) AND inner sep so both
        # are restored to t["border"] after _recolour sets them to frame_bg.
        self._section_border_seps.append(border_f)
        self._section_border_seps.append(sep)
        self._section_title_labels.append(title_lbl)
        return border_f, content

    def create_widgets(self):
        """Build and lay out all main-window widgets."""

        # ── Hidden state vars (kept in sync by Settings dialog) ───────────────
        self.debug_var        = tk.BooleanVar(value=self.engine.config["debug_mode"])
        self.auto_restart_var = tk.BooleanVar(value=self.engine.config["auto_restart"])
        self.dry_run_var      = tk.BooleanVar(value=self.engine.config["dry_run"])

        # ── Accent top stripe (3 px) ──────────────────────────────────────────
        self._top_stripe = tk.Frame(self.root, height=3,
                                    bg=self._theme["accent"], bd=0)
        self._top_stripe.pack(side="top", fill="x")
        self._top_stripe.pack_propagate(False)
        # Keep it out of _recolour's Frame→frame_bg pass so the accent survives.
        # _apply_theme manually restores it after _recolour.

        # ── Top toolbar: log filter + status ──────────────────────────────────
        frame_opts = tk.Frame(self.root)
        frame_opts.pack(fill="x", padx=12, pady=(8, 2))

        tk.Label(frame_opts, text="Log:",
                 font=("Segoe UI", 9)).pack(side="left", padx=(0, 4))
        self.log_level_var = tk.StringVar(value="All")
        # Fixed-width flat button — same family as toolbar buttons.
        # width=6 prevents the toolbar shifting when the label changes ("All" → "Error").
        # Flag used by _show_log_level_panel to prevent duplicate panels.
        self._log_level_panel_open: bool = False
        self._log_menu_open: bool = False
        self._log_level_btn = tk.Button(
            frame_opts,
            textvariable=self.log_level_var,
            width=6,
            relief="flat", borderwidth=0,
            bg=self._theme["btn_bg"], fg=self._theme["btn_fg"],
            activebackground=self._theme["btn_hover"],
            activeforeground=self._theme["fg"],
            font=("Segoe UI", 9), padx=6, pady=4,
            cursor="hand2",
            command=self._show_log_level_panel,
        )
        self._log_level_btn.pack(side="left")
        def _llbtn_enter(_e):
            t2 = THEMES["dark" if self._is_dark else "light"]
            self._log_level_btn.configure(bg=t2["btn_hover"])
        def _llbtn_leave(_e):
            t2 = THEMES["dark" if self._is_dark else "light"]
            self._log_level_btn.configure(bg=t2["btn_bg"])
        self._log_level_btn.bind("<Enter>", _llbtn_enter)
        self._log_level_btn.bind("<Leave>", _llbtn_leave)
        self._tooltips.append(_ToolTip(
            self._log_level_btn,
            "Filter log messages by severity level",
            theme_getter=lambda: self._theme))

        self.status_var = tk.StringVar(value="Detecting components…")
        # Coloured status indicator dot — updated by _set_status_colour()
        self._status_dot = tk.Label(frame_opts, text="●",
                                    font=("Segoe UI", 8))
        self._status_dot.pack(side="left", padx=(8, 2))
        tk.Label(frame_opts, textvariable=self.status_var,
                 font=("Segoe UI", 9)).pack(side="left", padx=(0, 0))

        # Theme snapshot for widget creation — used for search entry, est-dur, etc.
        _t_cw = self._theme
        # Estimated duration — shown inline after status text once history exists.
        self._est_dur_var = tk.StringVar(value="")
        self._est_dur_label = tk.Label(frame_opts, textvariable=self._est_dur_var,
                                       font=("Segoe UI", 8),
                                       fg=_t_cw["tag_debug"])
        self._est_dur_label.pack(side="left", padx=(6, 4))
        # Log search bar — Entry + ✕ button in a shared container so they
        # appear as one docked widget with a single border.
        self._log_search_var = tk.StringVar()
        self._log_search_var.trace_add("write", self._on_log_search)
        _srch_frame = tk.Frame(
            frame_opts,
            bg=_t_cw["widget_bg"],
            highlightthickness=1,
            highlightbackground=_t_cw["border"],
            bd=0)
        _srch_frame.pack(side="right", padx=(4, 0))
        self._search_frame = _srch_frame  # store for theme updates
        self._search_entry = tk.Entry(
            _srch_frame, textvariable=self._log_search_var,
            width=16, relief="flat", borderwidth=0,
            highlightthickness=0,
            bg=_t_cw["widget_bg"], fg=_t_cw["widget_fg"],
            insertbackground=_t_cw["fg"],
            font=("Segoe UI", 9))
        self._search_entry.pack(side="left", ipady=3, padx=(4, 2))
        # Placeholder "Search..." — show when empty and unfocused.
        _ph_text = "Search..."  # placeholder display text

        # Placeholder design: the StringVar (_log_search_var) always holds the
        # REAL user search term (empty string while placeholder is visible).
        # Placeholder text lives only in the Entry widget — NOT in the StringVar.
        # This means _on_log_search never sees "Search..." and focus-event ordering
        # bugs cannot cause stale placeholder text to be searched.

        def _ph_show():
            """Insert placeholder directly into Entry; StringVar stays empty."""
            if not self._log_search_var.get() and not self._search_ph_active[0]:
                self._search_ph_active[0] = True
                # Read tag_debug from current theme — correct after dark/light switch.
                self._search_entry.configure(fg=self._theme["tag_debug"])
                # Unhook textvariable so insert() does NOT update StringVar
                # and does NOT fire the trace.
                self._search_entry.configure(textvariable="")
                self._search_entry.delete(0, "end")
                self._search_entry.insert(0, _ph_text)
                self._search_entry.configure(textvariable=self._log_search_var)

        def _ph_hide():
            """Remove placeholder text; restore real fg."""
            if self._search_ph_active[0]:
                self._search_ph_active[0] = False
                # Unhook so delete() does NOT clear the StringVar.
                self._search_entry.configure(textvariable="")
                self._search_entry.delete(0, "end")
                self._search_entry.configure(textvariable=self._log_search_var)
                self._search_entry.configure(fg=self._theme["widget_fg"])

        def _ph_on_focus_in(_e):
            _ph_hide()
            try:
                _srch_frame.configure(highlightbackground=self._theme["accent"])
            except Exception:
                pass

        def _ph_on_focus_out(_e):
            _ph_show()
            try:
                _srch_frame.configure(highlightbackground=self._theme["border"])
            except Exception:
                pass

        self._search_entry.bind("<FocusIn>",  _ph_on_focus_in)
        self._search_entry.bind("<FocusOut>", _ph_on_focus_out)
        # Escape clears search and moves focus away from the entry.
        def _search_escape(_e):
            _clr_search()
            try:
                self._log_level_btn.focus_set()
            except Exception:
                self.root.focus_set()
        self._search_entry.bind("<Escape>", _search_escape)
        _ph_show()  # show placeholder on startup
        # ✕ clear-search button — ipady=3 matches the Entry height
        def _clr_search():
            # Clear highlights, then reset entry to placeholder state.
            if hasattr(self, "log_widget"):
                try:
                    self.log_widget.tag_remove("search_hl", "1.0", "end")
                except Exception:
                    pass
                self._search_hl_active = False
            # Clear the real search term (fires trace with empty string — safe).
            self._log_search_var.set("")
            # Reset flag so _ph_show can re-insert the placeholder.
            self._search_ph_active[0] = False
            _ph_show()
        _clr_btn = self._make_btn(_srch_frame, "✕", _clr_search)
        _clr_btn.configure(pady=0, padx=4,
                           bg=_t_cw["widget_bg"],
                           activebackground=_t_cw["btn_hover"])
        _clr_btn.pack(side="left", ipady=3, padx=(0, 2))
        self._search_clr_btn = _clr_btn  # store for theme updates
        self._tooltips.append(_ToolTip(
            _clr_btn, "Clear search",
            theme_getter=lambda: self._theme))
        self._search_count_var = tk.StringVar(value="")
        self._search_count_lbl = tk.Label(
            frame_opts, textvariable=self._search_count_var,
            font=("Segoe UI", 8), anchor="e")
        self._search_count_lbl.pack(side="right", padx=(4, 0))
        self._tooltips.append(_ToolTip(
            self._search_count_lbl,
            f"Matches shown (max {_MAX_SEARCH_MATCHES})",
            theme_getter=lambda: self._theme))
        # 🔍 icon lives inside _srch_frame so the whole search unit looks contained.
        # Store ref so _apply_theme can correct its bg after _recolour.
        self._search_icon_lbl = tk.Label(_srch_frame, text="🔍",
                                          font=("Segoe UI", 9),
                                          bg=_t_cw["widget_bg"])
        self._search_icon_lbl.pack(side="left", padx=(4, 0))
        # ── Progress bar (canvas) — slightly taller for better readability ──────
        _bar_h = int(28 * self._scale)
        self._prog_canvas = tk.Canvas(self.root, height=_bar_h,
                                      bd=0, highlightthickness=0)
        self._prog_canvas.pack(fill="x", padx=12, pady=4)
        self._prog_canvas.bind("<Configure>", self._on_prog_resize)
        # _progress_pct: plain float — avoids a Tcl round-trip on every
        # update_gui tick (~7–20 calls/s idle); no DoubleVar overhead.
        self._progress_pct: float = 0.0

        # ── Pack order: bottom-anchors first so log widget can expand freely ──

        # ── Version bar (very bottom, packed first so it sits below btn_frame)
        # Thin 1-px top border gives the version bar a "footer" feel.
        self._ver_bar_sep = tk.Frame(self.root, height=1, bd=0)
        self._ver_bar_sep.pack(side="bottom", fill="x")
        self._section_border_seps.append(self._ver_bar_sep)
        self._ver_bar = tk.Frame(self.root, height=20)
        self._ver_bar.pack(side="bottom", fill="x")
        self._ver_bar.pack_propagate(False)
        self._version_label = tk.Label(
            self._ver_bar, text=VERSION,
            font=("Segoe UI", 8), anchor="e", cursor="hand2")
        self._version_label.pack(side="right", padx=8)
        # Single-click, double-click, or right-click → open config folder.
        for _btn_evt in ("<Button-1>", "<Double-Button-1>", "<Button-3>"):
            self._version_label.bind(
                _btn_evt, lambda _e: self._open_file(_BASE_DIR))
        # Tooltip: shows version + click hint on hover.
        _ver_tip_text = f"{VERSION}  —  click to open: {_BASE_DIR}"
        self._tooltips.append(
            _ToolTip(self._version_label, _ver_tip_text,
                     theme_getter=lambda: self._theme))
        # Keyboard hint — shown on the left of the version bar as a subtle reminder.
        self._ver_hint_label = tk.Label(
            self._ver_bar,
            text="F5 start  ·  F1 help  ·  Ctrl+R health  ·  Ctrl+F search  ·  Ctrl+D dry-run  ·  Ctrl+H history  ·  Ctrl+A select all",
            font=("Segoe UI", 8), anchor="w")
        self._ver_hint_label.pack(side="left", padx=8)

        # ── Button bar ────────────────────────────────────────────────────────
        btn_frame = tk.Frame(self.root)
        btn_frame.pack(side="bottom", fill="x", padx=12, pady=(4, 8))

        def _sep():
            """Insert a 1-px vertical divider between button groups."""
            s = tk.Frame(btn_frame, width=1, bg=self._theme["border"])
            s.pack(side="left", fill="y", padx=(4, 6), pady=4)
            self._section_border_seps.append(s)

        def _tip(btn, key):
            """Attach a _ToolTip to btn using the key from _BUTTON_TOOLTIPS."""
            tt = _ToolTip(btn, _BUTTON_TOOLTIPS.get(key, ""), self._theme.__get__ if False else lambda: self._theme)
            self._tooltips.append(tt)

        # ── Group 1: Run controls ─────────────────────────────────────────────
        self.start_btn = self._make_btn(btn_frame, "⟳  Detecting…",
                                        self.start_updates, state="disabled",
                                        accent=True)
        self.start_btn.pack(side="left", padx=(0, 4))
        _tip(self.start_btn, "start")

        self.stop_btn = self._make_btn(btn_frame, "■  Cancel",
                                       self.engine.cancel, state="disabled")
        self.stop_btn.pack(side="left", padx=(0, 4))
        _tip(self.stop_btn, "stop")

        self.retry_btn = self._make_btn(btn_frame, "↺  Retry Failed",
                                        self._retry_failed, state="disabled")
        self.retry_btn.pack(side="left", padx=(0, 4))
        _tip(self.retry_btn, "retry")

        self.refresh_btn = self._make_btn(btn_frame, "⟳  Health",
                                          self.populate_health, state="disabled")
        self.refresh_btn.pack(side="left", padx=(0, 4))
        _tip(self.refresh_btn, "health")

        # ── Group 2: Log tools ────────────────────────────────────────────────
        _sep()
        _vl = self._make_btn(btn_frame, "📋  View Log", self.open_log)
        _vl.pack(side="left", padx=(0, 2))
        _tip(_vl, "viewlog")

        _ll = self._make_btn(btn_frame, "▾  Logs", self._show_log_menu)
        _ll.pack(side="left", padx=(0, 4))
        _tip(_ll, "logs")

        _eh = self._make_btn(btn_frame, "📊  Export Health", self.export_health)
        _eh.pack(side="left", padx=(0, 4))
        _tip(_eh, "export")

        _cl = self._make_btn(btn_frame, "🗑  Clear Log", self._clear_log)
        _cl.pack(side="left", padx=(0, 4))
        _tip(_cl, "clear")

        _cp = self._make_btn(btn_frame, "⎘  Copy Log", self._copy_log)
        _cp.pack(side="left", padx=(0, 4))
        _tip(_cp, "copy")

        # ── Group 3: App controls ─────────────────────────────────────────────
        _sep()
        _st = self._make_btn(btn_frame, "⚙  Settings", self.open_settings)
        _st.pack(side="left", padx=(0, 4))
        _tip(_st, "settings")

        _hi = self._make_btn(btn_frame, "📜  History", self._show_history)
        _hi.pack(side="left", padx=(0, 4))
        _tip(_hi, "history")

        _hp = self._make_btn(btn_frame, "❓  Help", self._show_shortcuts)
        _hp.pack(side="left", padx=(0, 4))
        _tip(_hp, "help")

        # ── Health Dashboard card ─────────────────────────────────────────────
        self._border_health, _health_content = self._make_section(
            self.root, "Health Dashboard", side="bottom")
        # Health treeview + scrollbar in a sub-frame so scrollbar
        # hugs the right edge of the tree regardless of window width.
        _health_tree_frame = tk.Frame(_health_content)
        _health_tree_frame.pack(fill="x")
        self._section_bg_frames.append(_health_tree_frame)
        self.tree = ttk.Treeview(_health_tree_frame,
                                 columns=("Component", "Status", "Version"),
                                 show="headings", height=5,
                                 selectmode="browse")
        _health_vsb = ttk.Scrollbar(_health_tree_frame, orient="vertical",
                                    command=self.tree.yview)
        self.tree.configure(yscrollcommand=_health_vsb.set)
        # Column widths: Component narrower, Version stretches to fill space.
        # minwidth prevents columns from being dragged to zero.
        _cw = [160, 95, 0]    # 0 = stretch (fill="x" + expand=True handles it)
        _h_sort_state: dict = {"col": None, "asc": True}
        def _h_sort(col, _st=_h_sort_state):
            asc = not _st["asc"] if _st["col"] == col else True
            _st.update(col=col, asc=asc)
            _rows = [(self.tree.set(k, col), k)
                     for k in self.tree.get_children("")]
            _rows.sort(reverse=not asc, key=lambda x: x[0].lower())
            for _i, (_, k) in enumerate(_rows):
                self.tree.move(k, "", _i)
            for c in ("Component", "Status", "Version"):
                _arr = (" ↑" if asc else " ↓") if c == col else ""
                _anc = "center" if c == "Status" else "w"
                self.tree.heading(c, text=c + _arr, anchor=_anc)
            try:
                self.tree.yview_moveto(0)
            except Exception:
                pass
        for col, w in zip(("Component", "Status", "Version"), _cw):
            self.tree.heading(col, text=col,
                             command=lambda c=col: _h_sort(c))
            if w:
                self.tree.column(col, width=w, minwidth=60, stretch=False)
            else:
                self.tree.column(col, width=280, minwidth=100, stretch=True)
        # Center the Status column — short words look better balanced.
        self.tree.column("Status", anchor="center")
        self.tree.heading("Status", anchor="center")
        self.tree.pack(side="left", fill="x", expand=True)
        _health_vsb.pack(side="right", fill="y")
        def _health_copy_row(_e=None):
            sel = self.tree.selection()
            if not sel: return
            vals = self.tree.item(sel[0], "values")
            try:
                self.root.clipboard_clear()
                self.root.clipboard_append("\t".join(str(v) for v in vals))
                self._set_status("Row copied to clipboard.", "dot_idle")
                def _restore_status():
                    if not self._running and not self._health_running:
                        self._set_status(
                            self._idle_status(
                                self.engine.config.get("dry_run", False)),
                            "dot_idle")
                self.root.after(1500, _restore_status)
            except Exception:
                pass
        self.tree.bind("<Control-c>", _health_copy_row)
        self._health_last_checked_var = tk.StringVar(value="")
        # Hint row: sort hint on left, timestamp on right.
        _health_foot = tk.Frame(_health_content,
                                bg=self._theme["section_bg"])
        _health_foot.pack(fill="x")
        self._section_bg_frames.append(_health_foot)
        _health_sort_hint = tk.Label(
            _health_foot,
            text="Click column header to sort  ·  Ctrl+C copies row",
            font=("Segoe UI", 8), padx=8, pady=2, anchor="w",
            bg=self._theme["section_bg"], fg=self._theme["tag_debug"])
        _health_sort_hint.pack(side="left")
        self._health_sort_hint_ref = _health_sort_hint
        # Registered only for bg correction (not title labels which use main fg).
        self._section_bg_frames.append(_health_sort_hint)
        self._health_ts_label = tk.Label(
            _health_foot, textvariable=self._health_last_checked_var,
            font=("Segoe UI", 8), padx=8, pady=2, anchor="e",
            bg=self._theme["section_bg"], fg=self._theme["fg"])
        self._health_ts_label.pack(side="right")

        # ── Components card ───────────────────────────────────────────────────
        self._border_comps, _comps_content = self._make_section(
            self.root, "Components to Update", side="bottom")
        # Grab the title label just pushed onto _section_title_labels so we can
        # update it in _on_components_ready with an availability count badge.
        self._comp_section_title_lbl = self._section_title_labels[-1]
        self.frame_comps = _comps_content
        frame_comp_btns  = tk.Frame(_comps_content)
        self._section_bg_frames.append(frame_comp_btns)   # theme-correction tracking
        frame_comp_btns.grid(row=0, column=0,
                             columnspan=_COMP_COLUMNS * 2,
                             sticky="w", padx=6, pady=4)
        self._make_btn(frame_comp_btns, "Select All",
                       self._select_all_components).pack(side="left", padx=(0, 4))
        self._make_btn(frame_comp_btns, "Deselect All",
                       self._deselect_all_components).pack(side="left")
        self.comp_vars = {}
        self._comp_placeholder = tk.Label(_comps_content,
                                          text="Detecting components…",
                                          font=("Segoe UI", 9),
                                          bg=self._theme["section_bg"],
                                          fg=self._theme["fg"])
        self._comp_placeholder.grid(row=1, column=0, padx=8, pady=6)

        # ── Log panel (fills remaining space) ─────────────────────────────────
        # 1-px border frame around the log (same treatment as section cards).
        self._border_log = tk.Frame(self.root,
                                    bg=self._theme["border"], bd=0)
        self._border_log.pack(fill="both", expand=True, padx=10, pady=(4, 6))
        self._section_border_seps.append(self._border_log)
        _log_inner = tk.Frame(self._border_log, bd=0)
        _log_inner.pack(fill="both", expand=True, padx=1, pady=1)
        self.log_widget = tk.Text(_log_inner, state="disabled", height=6,
                                  wrap="char", relief="flat",
                                  highlightthickness=0,
                                  font=("Consolas", 9), padx=8, pady=6)
        self._log_scrollbar = ttk.Scrollbar(
            _log_inner, orient="vertical",
            command=self.log_widget.yview)
        self.log_widget.configure(yscrollcommand=self._log_scrollbar.set)
        self._log_scrollbar.pack(side="right", fill="y")
        self.log_widget.pack(side="left", fill="both", expand=True)
        # Note: Ctrl+A select-all on the log widget is intentionally NOT bound
        # here.  The log widget is always state="disabled" so it can never receive
        # keyboard focus via clicks or Tab traversal.  Adding a binding with
        # return "break" would block the root's Ctrl+A handler (select all
        # components) if anything ever redirected focus to it unexpectedly.

    def _on_components_ready(self, components):
        """Populate the component checkboxes once detection completes."""
        _eng = self.engine  # bind once — 4 accesses in this method
        # Guard against a second call.
        if self._comp_placeholder is not None:
            try:
                self._comp_placeholder.destroy()
            except tk.TclError:
                pass
            self._comp_placeholder = None
        else:
            # If comp_vars is already populated a second call would
            # create duplicate checkboxes in the grid and orphan the originals.
            # Return early - the component list is already fully built.
            return

        # ── Update section title with availability count badge ────────────────
        n_avail = sum(1 for info in components.values() if info["available"])
        n_total = len(components)
        if self._comp_section_title_lbl is not None:
            try:
                self._comp_section_title_lbl.configure(
                    text=f"Components to Update  ({n_avail} / {n_total} available)")
            except tk.TclError:
                pass

        t2   = self._theme
        _n   = _COMP_COLUMNS          # 2 columns
        _sbg = t2["section_bg"]
        _acc = t2["accent"]
        _fg  = t2["fg"]
        _dim = t2["tag_debug"]
        _brd = t2["border"]
        # Configure equal columns
        for col in range(_n):
            self.frame_comps.grid_columnconfigure(col, weight=1, uniform="comp")

        items   = list(components.items())
        n_items = len(items)
        # Column-major order: fill left column first, then right.
        # rows_per_col = ceil(n_items / n)
        _rows = math.ceil(n_items / _n)

        def _col_row(i):
            """Map flat index → (column, row) in column-major order."""
            return i // _rows, i % _rows

        for i, (name, info) in enumerate(items):
            enabled = _eng.config["components"].get(name, True)
            avail   = info["available"]
            var     = tk.BooleanVar(value=enabled and avail)
            self.comp_vars[name] = var
            _dname  = _COMP_DISPLAY_NAMES.get(name, name)
            _col, _row = _col_row(i)
            # +1 row offset: row 0 is the Select/Deselect button bar
            _grid_row = _row + 1

            # ── Row frame ──────────────────────────────────────────────
            row_f = tk.Frame(self.frame_comps, bg=_sbg, bd=0)
            row_f.grid(row=_grid_row, column=_col,
                       sticky="ew", padx=(8, 4), pady=1)
            row_f.grid_columnconfigure(1, weight=1)

            # ── Canvas checkbox (14×14 px, drawn in Python) ─────────────
            _csize = 14
            chk_c  = tk.Canvas(row_f, width=_csize, height=_csize,
                                bg=_sbg, bd=0, highlightthickness=0)
            chk_c.grid(row=0, column=0, padx=(0, 6), pady=4)

            def _draw_box(canvas, checked, available, theme):
                canvas.delete("all")
                _a = theme["accent"]; _b = theme["border"]
                _bg2 = theme["section_bg"]
                _r = 3  # corner radius
                if checked and available:
                    # Filled accent square with white tick
                    canvas.create_rectangle(1, 1, _csize-1, _csize-1,
                                            fill=_a, outline=_a)
                    # Tick: two lines forming a check mark
                    canvas.create_line(3, 7, 6, 10, fill="white", width=2)
                    canvas.create_line(6, 10, 11, 4, fill="white", width=2)
                elif available:
                    # Empty square with border
                    canvas.create_rectangle(1, 1, _csize-1, _csize-1,
                                            fill=_bg2, outline=_b)
                else:
                    # Unavailable: dim square
                    canvas.create_rectangle(1, 1, _csize-1, _csize-1,
                                            fill=_bg2, outline=_b)
                    canvas.create_line(4, 7, 10, 7, fill=_b, width=1)

            _draw_box(chk_c, enabled and avail, avail, t2)

            # ── Name label ──────────────────────────────────────────────
            name_lbl = tk.Label(row_f,
                                text=_dname,
                                font=("Segoe UI", 9),
                                bg=_sbg,
                                fg=_fg if avail else _dim,
                                anchor="w")
            name_lbl.grid(row=0, column=1, sticky="ew")

            # ── Status label (right, shows ▶✔✘ during run) ─────────────
            status_lbl = tk.Label(row_f, text="",
                                  font=("Segoe UI", 9),
                                  bg=_sbg, fg=_dim,
                                  width=3, anchor="e")
            status_lbl.grid(row=0, column=2, padx=(4, 4))

            # Hidden Checkbutton for skip-cache compatibility
            cb = tk.Checkbutton(row_f, variable=var, bg=_sbg,
                                bd=0, highlightthickness=0,
                                state="normal" if avail else "disabled",
                                activebackground=_sbg)
            self._comp_checkbox_widgets.append(cb)

            # ── Refresh: redraws canvas + re-styles labels ───────────────
            def _mk_refresh(v_, c_, nl_, av_, sl_=None):
                def _refresh(*_):
                    _t  = self._theme
                    _on = v_.get()
                    _draw_box(c_, _on, av_, _t)
                    nl_.configure(
                        fg=_t["fg"] if av_ else _t["tag_debug"],
                        bg=_t["section_bg"],
                        font=("Segoe UI", 9, "bold" if _on and av_ else ""))
                    c_.configure(bg=_t["section_bg"])
                    row_f.configure(bg=_t["section_bg"])
                    if sl_: sl_.configure(bg=_t["section_bg"])
                    # Keep Start button label count in sync with checkbox state.
                    # Deferred via after(0) — direct configure() inside a write-
                    # trace re-enters Tk on Windows and can swallow key events.
                    # Coalesced: first pending call wins; subsequent var.set()
                    # calls in the same tick (e.g. select-all) are folded in.
                    if not self._refresh_start_pending:
                        self._refresh_start_pending = True
                        self.root.after(0, self._refresh_start_btn_label)
                return _refresh

            _refresh = _mk_refresh(var, chk_c, name_lbl, avail, status_lbl)
            var.trace_add("write", _refresh)

            if avail:
                def _mk_toggle(v_):
                    def _tog(_e=None): v_.set(not v_.get())
                    return _tog
                _tog = _mk_toggle(var)
                for w in (row_f, chk_c, name_lbl):
                    w.bind("<Button-1>", _tog)
                    w.configure(cursor="hand2")

            self._comp_chip_frames[name]   = row_f
            self._comp_chip_dots[name]     = status_lbl
            self._comp_status_labels[name] = status_lbl
        self._skip_cache = None   # invalidate after new widgets added
        self._apply_theme()
        self._refresh_start_btn_label()   # show initial selected count
        # t2 already holds the correct theme dict (set at method top);
        # reuse it rather than calling self._theme again.
        self._start_btn_enabled = True
        self.start_btn.configure(
            text="▶  Start Updates",
            state="normal",
            bg=t2["accent"], fg=t2["accent_fg"],
            activebackground=t2["accent"], activeforeground=t2["accent_fg"])
        self.refresh_btn.configure(state="normal")
        with _eng.config_lock:
            dry_run     = _eng.config.get("dry_run", False)
            auto_health = _eng.config.get("auto_health_on_start", True)
        self._set_status(self._idle_status(dry_run), dot_key="dot_idle")
        if dry_run:
            self.root.title(f"Windows Updater {VERSION} [DRY RUN]")
        self._update_est_duration()
        if auto_health:
            self.populate_health()
        self._schedule_health_refresh()

    def populate_health(self):
        """Start a background health check and stream results into the treeview."""
        if self._health_running:
            return
        # Clear _health_stop_event (not stop_event).
        self.engine._health_stop_event.clear()
        self._health_running = True
        self.refresh_btn.configure(state="disabled", text="⟳  Checking…")
        self._set_status("Checking health…", dot_key="dot_running")
        _ph = self.tree.get_children()   # fetch once; delete in one Tcl call
        if _ph:
            self.tree.delete(*_ph)        # n items → 1 Tcl round-trip (was n)
        self._health_placeholder_id = self.tree.insert(
            "", "end", values=("⟳  Checking…", "", ""))
        # Configure row colours once here so _apply_health_row
        # doesn't need to re-configure them on every single row insertion.
        t = self._theme
        self.tree.tag_configure("good", background=t["tree_good"])
        self.tree.tag_configure("bad",  background=t["tree_bad"])
        self.tree.tag_configure("warn", background=t["tree_warn"])
        self._health_row_ids = {}
        self._health_placeholder_removed = False  # reset for new check
        # Reset column heading arrows — rows will be in original order
        # after a new check so stale ↑/↓ arrows would be misleading.
        _h_anchors = {"Status": "center"}
        for _c in ("Component", "Status", "Version"):
            try:
                self.tree.heading(_c, text=_c,
                                  anchor=_h_anchors.get(_c, "w"))
            except Exception:
                pass

        def _run():
            dashboard = {}
            cancelled = False
            try:
                dashboard = self.engine.health_check()
                cancelled = self.engine._health_stop_event.is_set()
            except Exception as e:
                logger.exception("health_check raised")
            finally:
                self.queue.put(("health_data", (dashboard, cancelled)))

        threading.Thread(target=_run, name="health-check", daemon=True).start()

    def _sort_health_tree(self):
        """Re-order treeview rows to match component definition order.

        health_check() streams results as futures complete, so row arrival
        order is non-deterministic. tree.move() costs one Tcl call per row.

        Uses _health_row_ids {name: item_id} directly — avoids tree.item()
        Tcl calls that the previous implementation needed to recover names.
        """
        if not self._health_row_ids:
            return
        # O(1) rank lookup — avoids O(n) list.index() per row.
        _order = {name: i for i, name in enumerate(self.engine.components)}
        _n     = len(_order)
        for i, name in enumerate(
                sorted(self._health_row_ids, key=lambda n: _order.get(n, _n))):
            self.tree.move(self._health_row_ids[name], "", i)

    def _apply_health_row(self, name: str, info: dict):
        """Insert or update a single health treeview row (incremental streaming).

        Also updates the status bar with a live probe counter so the user
        knows how many components have been checked vs total.
        """
        # Live probe counter in status bar.
        _n_done  = len(self._health_row_ids) + 1   # +1 for this row
        _n_total = len(self.engine.components)
        if _n_total:
            try:
                self._set_status(
                    f"Checking health… {_n_done} / {_n_total}", dot_key="dot_running")
            except Exception:
                pass
        status  = info["status"]
        version = info["version"]
        tag    = _HEALTH_TAG.get(status, "warn")
        slabel = _HEALTH_STATUS_LABEL.get(status, status)  # friendly display text

        # Remove the "Checking..." placeholder on the very first real row.
        # _health_placeholder_id (set in populate_health) allows a direct
        # tree.delete() call — no get_children() scan required.
        if not self._health_placeholder_removed:
            # Delete placeholder directly — id stored in populate_health.
            if self._health_placeholder_id:
                try:
                    self.tree.delete(self._health_placeholder_id)
                except tk.TclError:
                    pass  # already gone (race with bulk _apply_health_data)
                self._health_placeholder_id = None
            self._health_placeholder_removed = True

        # Hoist display-name lookup above the if/else — one dict lookup
        # instead of one per branch (was computed twice before).
        _dname   = _COMP_DISPLAY_NAMES.get(name, name)
        existing = self._health_row_ids.get(name)
        if existing:
            self.tree.item(existing, values=(_dname, slabel, version), tags=(tag,))
        else:
            item_id = self.tree.insert("", "end", values=(_dname, slabel, version), tags=(tag,))
            self._health_row_ids[name] = item_id
        # tag_configure calls removed from here — they are global to
        # the treeview and are set once in populate_health() and _apply_theme()
        # rather than redundantly on every single row insertion (O(n) Tcl calls).

    def _apply_health_data(self, dashboard, cancelled: bool = False):
        """Finalise the health treeview after a check completes or is cancelled."""
        _eng = self.engine  # bind once — 2 accesses in this method
        if not self._health_running:
            return
        if not self._health_row_ids:
            _ch = self.tree.get_children()   # one get_children() call
            if _ch:
                self.tree.delete(*_ch)        # n items → 1 Tcl round-trip (was n)
            if not dashboard:
                msg = "Health check cancelled." if cancelled else "Health check failed - see log"
                self.tree.insert("", "end",
                                 values=("(all components)", msg, ""),
                                 tags=("warn",))
            else:
                # "alt" tag is configured by _apply_theme() which always runs
                # before any health check completes — no t=self._theme lookup
                # or tag_configure("alt") call needed here.
                for comp, info in dashboard.items():
                    status, version = info["status"], info["version"]
                    tag = _HEALTH_TAG.get(status, "warn")
                    slabel = _HEALTH_STATUS_LABEL.get(status, status)
                    # Pass tags= directly to insert() — saves one Tcl
                    # round-trip per row vs a separate tree.item() call.
                    self.tree.insert("", "end",
                                     values=(_COMP_DISPLAY_NAMES.get(comp, comp),
                                             slabel, version),
                                     tags=(tag,))
        elif cancelled:
            # Incremental rows arrived but the check was cancelled
            # before all components were probed. Log a warning so the user
            # knows the results shown are partial — previously silent.
            _eng.log("Health check cancelled — results shown are incomplete.", "warn")

        # Re-order rows to match component definition order.
        try:
            self._sort_health_tree()
        except tk.TclError:
            pass   # treeview destroyed before sort completes — harmless
        finally:
            # Always reset running flag and re-enable button so the user
            # can retry even if a TclError fires inside _sort_health_tree.
            self._health_running = False
            try:
                self.refresh_btn.configure(state="normal", text="⟳  Health")
            except tk.TclError:
                pass
            if not self._running:
                # Show a meaningful summary in the status bar so the
                # user gets instant feedback without reading the table.
                _n_ok  = sum(1 for v in self._health_row_ids
                             if dashboard.get(v, {}).get("status") == "available")
                _n_tot = len(self.engine.components)
                with _eng.config_lock:
                    _dr = _eng.config.get("dry_run", False)
                if _n_tot and not cancelled:
                    _dot = ("dot_done" if _n_ok == _n_tot
                            else "dot_error" if _n_ok == 0 else "dot_idle")
                    _health_str = (
                        "all OK" if _n_ok == _n_tot
                        else f"{_n_ok} / {_n_tot} available")
                    self._set_status(
                        f"{self._idle_status(_dr)}  ·  Health: {_health_str}",
                        dot_key=_dot)
                else:
                    self._set_status(self._idle_status(_dr),
                                     dot_key="dot_idle")
            if self._health_last_checked_var is not None:
                _now = datetime.datetime.now()
                # Include the date when the check spans midnight or
                # when the app has been open across days.
                _ts = (_now.strftime("%H:%M:%S")
                       if _now.date() == datetime.date.today()
                       else _now.strftime("%Y-%m-%d  %H:%M:%S"))
                self._health_last_checked_var.set(f"Last checked: {_ts}")

    def export_health(self):
        """Write the current health dashboard treeview to a text, CSV, or JSON file."""
        rows = []
        for item in self.tree.get_children():
            rows.append(self.tree.item(item, "values"))
        if not rows:
            self._msgbox("info", "Export Health", "No health data to export yet.")
            return
        ts = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[
                ("Text files", "*.txt"),
                ("CSV files",  "*.csv"),
                ("JSON files", "*.json"),
                ("All files",  "*.*"),
            ],
            initialfile=f"health_{ts}.txt",
            title="Export Health Dashboard",
        )
        if not path:
            return
        try:
            ext = os.path.splitext(path)[1].lower()
            # newline="" is only required by the csv module (prevents
            # double \r\n on Windows). txt/json use the default (None) so
            # \n is translated to \r\n and files open correctly in Notepad.
            _nl = "" if ext == ".csv" else None
            with open(path, "w", encoding="utf-8", newline=_nl) as f:
                if ext == ".json":
                    records = [
                        {"component": r[0],
                         "status": _HEALTH_LABEL_RAW.get(r[1], r[1]),
                         "version": r[2]}
                        for r in rows
                    ]
                    json.dump({"exported": str(datetime.datetime.now()),
                               "dashboard": records}, f, indent=2)
                elif ext == ".csv":
                    writer = csv.writer(f)
                    writer.writerow(["Component", "Status", "Version"])
                    writer.writerows(
                        (r[0], _HEALTH_LABEL_RAW.get(r[1], r[1]), r[2])
                        for r in rows
                    )
                else:
                    f.write(f"Health Dashboard - {datetime.datetime.now()}\n")
                    f.write(f"{'Component':<20} {'Status':<15} {'Version'}\n")
                    f.write("-" * 60 + "\n")
                    for row in rows:
                        comp, status, version = row
                        f.write(f"{comp:<20} {status:<15} {version}\n")
            self._msgbox("info", "Export Health", f"Saved to:\n{path}")
        except OSError as e:
            self._msgbox("error", "Export Health", f"Could not write file:\n{e}")

    def start_updates(self):
        """Validate selections, save config, then start an update run."""
        if self._running:
            self._msgbox("warn", "Already Running", "Updates are already in progress.")
            return
        if self._health_running:
            self._msgbox("warn", "Health Check Running",
                "A health check is in progress. Please wait for it to finish.")
            return

        # Read all GUI vars outside the lock — var.get() is a Tcl call
        # and holding config_lock during Tcl calls extends contention.
        _debug   = self.debug_var.get()
        _restart = self.auto_restart_var.get()
        _dry     = self.dry_run_var.get()
        # Pre-read component vars outside the lock for the same reason.
        _comp_vals = {name: var.get() for name, var in self.comp_vars.items()}
        selected = [
            name for name, val in _comp_vals.items()
            if val and self.engine.components.get(name, {}).get("available")
        ]
        with self.engine.config_lock:
            self.engine.config["debug_mode"]   = _debug
            self.engine.config["auto_restart"] = _restart
            self.engine.config["dry_run"]      = _dry
            for name, val in _comp_vals.items():
                self.engine.config["components"][name] = val
            config_snapshot = copy.deepcopy(self.engine.config)
        save_config(config_snapshot)
        if not selected:
            self._msgbox("warn", "Nothing to update", "No components are enabled and available.")
            return

        self._cancel_health_refresh()
        # Clear any status dots left over from a previous run so the UI
        # starts clean — dots are only reset in _unlock (run end) normally,
        # which means a retry run would show old ✔/✘ symbols during the new run.
        for _cn, _dot in self._comp_status_labels.items():
            try:
                _dot.configure(text="", fg=self._theme["tag_debug"])
            except Exception:
                pass
        self._progress_pct = 0.0
        self._run_start_time = time.monotonic()
        # Build segment list in run order for the progress bar.
        self._prog_segments = [
            (c, _COMP_DISPLAY_NAMES.get(c, c)) for c in selected]
        self._prog_seg_states = {c: "pending" for c, _ in self._prog_segments}
        self._last_drawn_pct = -1.0   # force full redraw
        self._last_drawn_sck = ""
        self.retry_btn.configure(state="disabled")
        self._hide_reboot_banner()
        prefix = "[DRY RUN] " if _dry else ""
        _start_ts = datetime.datetime.now().strftime("%H:%M:%S")
        self._set_status(f"{prefix}Running… (started {_start_ts})",
                         dot_key="dot_running")
        # Hide stale estimate — refreshed when run completes.
        if self._est_dur_var is not None:
            self._est_dur_var.set("")
        self._running = True
        self._start_btn_enabled = False
        self.start_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")

        def _run_and_unlock():
            try:
                self.engine.run_selected(selected)
            except Exception as _thread_exc:
                # run_selected re-raises after logging; catch here so the
                # daemon thread exits cleanly instead of printing a bare
                # traceback to stderr.
                logger.error("run_and_unlock: update thread failed: %s",
                             _thread_exc, exc_info=True)
            finally:
                self.queue.put(("_unlock", None))

        try:
            threading.Thread(target=_run_and_unlock,
                             name="update-run", daemon=True).start()
        except Exception as _te:
            # Thread creation failed (extremely rare — e.g. OS resource limit).
            # Reset all run state so the user is not permanently locked out.
            logger.error("start_updates: failed to start update thread: %s",
                         _te, exc_info=True)
            self._running = False
            _t2 = self._theme
            self.start_btn.configure(
                state="normal",
                bg=_t2["accent"], fg=_t2["accent_fg"],
                activebackground=_t2["accent"],
                activeforeground=_t2["accent_fg"])
            self.stop_btn.configure(state="disabled")
            self._msgbox("error", "Error",
                         f"Could not start the update thread:\n{_te}")

    def _handle_confirm_restart(self, value):
        """Show the reboot confirmation dialog and signal the engine thread."""
        confirm_event, result_box = value
        answer = self._msgbox("yesno", "Auto-Restart",
            "All updates are complete.\n\nAuto-restart is enabled. Reboot now?\n\n"
            "(The system will restart in 10 seconds if you click Yes.)")
        result_box["answer"] = answer
        confirm_event.set()

    def update_gui(self):
        """Poll the GUI queue and dispatch all pending engine messages."""
        # Bind module-level constants to locals once per tick.
        # LOAD_FAST (~2× faster than LOAD_GLOBAL) benefits both the
        # drain section and the hot while-loop below.
        _level_order  = _LOG_LEVEL_ORDER
        _dot_colour   = _DOT_COLOUR_KEY      # state→theme-key map for status dots
        _theme        = self._theme           # property: evaluated once per tick
        _max_msgs     = _MAX_MSGS_PER_TICK
        _status_syms  = _COMP_STATUS_SYMBOLS
        _batch_key    = _LOG_BATCH_KEY
        _get          = self.queue.get_nowait  # LOAD_FAST vs 2× LOAD_ATTR in hot loop
        _put          = self.queue.put         # same binding pattern as _get
        _csl          = self._comp_status_labels  # same dict; populated once by _on_components_ready
        _lw           = self.log_widget           # 6 accesses in flush path
        _tk_end       = "end"                     # tk.END constant; avoids 2 LOAD_ATTRs per insert
        _groupby      = itertools.groupby         # 1 LOAD_GLOBAL+LOAD_ATTR per flush
        _max_log      = _MAX_LOG_LINES            # 3 LOAD_GLOBALs per flush
        _fmt_elapsed  = self._fmt_elapsed         # used once in _unlock handler
        _llc          = self._log_line_count      # 4 accesses in flush path
        _root_after   = self.root.after           # every-tick reschedule + tray restore
        _redraw       = self._redraw_progress     # called unconditionally every tick
        _lw_insert    = _lw.insert                # called in the groupby flush loop
        _lw_cfg       = _lw.configure             # 2× per flush (enable/disable)
        _lw_yview     = _lw.yview                 # 1× per flush for auto-scroll guard
        _lw_see       = _lw.see                   # called when at bottom of log
        _lsv          = self._log_search_var      # search-highlight re-run guard
        _search_fn    = self._on_log_search       # called in flush when term active
        _engine       = self.engine               # 7 accesses in _unlock + priority path
        _set_st       = self._set_status          # 2 accesses: status action + _unlock
        _retry_btn    = self.retry_btn            # 2 accesses in _unlock
        _stop_btn     = self.stop_btn             # 1 access in _unlock
        _start_btn    = self.start_btn            # 1 access in _unlock
        _msgbox       = self._msgbox              # 3 accesses: error + run_complete×2
        _status_var   = self.status_var           # 1 access in _unlock (.get())configure)
        _dry_run_var  = self.dry_run_var          # 1 access in run_complete
        _show_dry_run = self._show_dry_run_summary  # 1 access in run_complete
        _show_reboot   = self._show_reboot_banner       # 1 access in _unlock
        _sched_refresh   = self._schedule_health_refresh    # 1 access in _unlock
        _update_est      = self._update_est_duration        # 1 access in _unlock
        _restore_tray    = self._restore_from_tray          # 1 access in _unlock
        _prog_segs       = self._prog_seg_states            # 2 accesses in comp_*
        _delay = 150  # default; overwritten inside try if work was done this tick
        try:
            # Priority pass: drain queue to find confirm_restart before other messages.
            if _engine._confirm_restart_pending.is_set():
                # Drain the entire queue so confirm_restart is always found.
                # A bounded drain (old: 2×_max_msgs = 400) caused a liveness
                # bug: if >400 messages were queued ahead of confirm_restart
                # the dialog was permanently unreachable — each tick read 400
                # messages, failed to find it, re-queued all 400, and retried.
                # The queue is naturally bounded (engine runs at ~human speed;
                # GUI drains 200 msgs/tick), so draining to empty is safe.
                drained = []
                try:
                    while True:
                        drained.append(_get())
                except queue.Empty:
                    pass
                _engine._confirm_restart_pending.clear()

                remainder = []
                found_restart = False
                for action, value in drained:
                    if action == "confirm_restart" and not found_restart:
                        found_restart = True
                        self._handle_confirm_restart(value)
                    else:
                        remainder.append((action, value))

                for item in remainder:
                    _put(item)
                if not found_restart:
                    _engine._confirm_restart_pending.set()

            log_batch = []
            # Track whether any queue work was done this tick.
            # Used to choose adaptive poll delay (50ms busy / 150ms idle).
            _had_work = False
            # _cur_min_level is cached on self and refreshed by the level-panel
            # pick callback — no per-tick Tcl round-trip needed.
            _cur_min_level = self._cur_min_level
            # Count only log messages toward the per-tick cap so that
            # non-log messages (progress, status, health_row, comp_status, etc.)
            # are never starved by a flood of debug output.
            log_count = 0
            while True:
                try:
                    action, value = _get()
                    if action == "log":
                        msg = value
                        # startswith() chain — faster than find()+slice+dict
                        # for the dominant case ("[INFO] ...") and avoids
                        # allocating an intermediate slice for the dict key.
                        # Benchmarked 2.6× faster on info-only batches.
                        if msg.startswith("[INFO] "):
                            level = "info";  msg = msg[7:]
                        elif msg.startswith("[WARN] "):
                            level = "warn";  msg = msg[7:]
                        elif msg.startswith("[ERROR] "):
                            level = "error"; msg = msg[8:]
                        elif msg.startswith("[DEBUG] "):
                            level = "debug"; msg = msg[8:]
                        else:
                            level = "info"
                        if _level_order[level] >= _cur_min_level:
                            if log_count >= _max_msgs:
                                # Only accepted messages count toward cap —
                                # filtered-out messages must not consume budget
                                # or starve higher-priority messages behind them.
                                _put((action, value))
                                break
                            log_count += 1
                            log_batch.append((msg, level))
                            _had_work = True
                    elif action == "log_header":
                        _had_work = True
                        if log_count < _max_msgs:
                            log_count += 1
                            log_batch.append((value, "header"))
                        else:
                            _put((action, value))
                            break
                    elif action == "comp_progress":
                        _had_work = True
                        comp_name, comp_state, pct = value
                        self._progress_pct = pct
                        _prog_segs[comp_name] = comp_state
                        dot = _csl.get(comp_name)
                        if dot:
                            _dk  = _dot_colour.get(comp_state, "dot_idle")
                            _sym = _status_syms.get(comp_state, "")
                            dot.configure(
                                text=_sym,
                                fg=_theme[_dk])
                    elif action == "status":
                        _had_work = True
                        _set_st(value)
                    elif action == "health_data":
                        _had_work = True
                        dashboard, cancelled = value
                        self._apply_health_data(dashboard, cancelled)
                    elif action == "health_row":
                        _had_work = True
                        name, info = value
                        if self._health_running:
                            self._apply_health_row(name, info)
                    elif action == "components_ready":
                        _had_work = True
                        self._on_components_ready(value)
                    elif action == "confirm_restart":
                        _had_work = True
                        # Re-queue through the priority-drain path so that
                        # any in-flight progress/status messages are processed first
                        # and the GUI is visually up-to-date before the dialog blocks.
                        _engine._confirm_restart_pending.set()
                        _put((action, value))
                        break   # stop draining; next tick's priority pass handles it
                    elif action == "error":
                        _had_work = True
                        _msgbox("error", "Error", value)
                    elif action == "_unlock":
                        _had_work = True
                        self._running = False
                        _stop_btn.configure(state="disabled")
                        self._prog_current_comp = ""   # clear name on completion
                        # Append elapsed time to whatever status emit_status set.
                        _cur = _status_var.get()
                        if _cur and not (_cur.endswith("...") or _cur.endswith("…")):
                            _e = _fmt_elapsed(
                                time.monotonic() - self._run_start_time)
                            _clean = ("error" not in _cur.lower() and
                                      "cancel" not in _cur.lower() and
                                      "fail" not in _cur.lower())
                            _pfx = "✔  " if _clean else "✘  "
                            _set_st(f"{_pfx}{_cur}  ({_e})")
                        # Clear status symbols; refresh canvas checkboxes via trace.
                        for _cn, dot in _csl.items():
                            dot.configure(text="", fg=_theme["tag_debug"])
                            _v = self.comp_vars.get(_cn)
                            if _v: _v.set(_v.get())  # retrigger refresh
                        if not _engine._rebooting:
                            t2 = _theme
                            self._start_btn_enabled = True
                            _start_btn.configure(
                                state="normal",
                                bg=t2["accent"], fg=t2["accent_fg"],
                                activebackground=t2["accent"],
                                activeforeground=t2["accent_fg"])
                            # Restore the selected-count label that was
                            # overwritten by configure(text=...) above.
                            self.root.after(0, self._refresh_start_btn_label)
                        # Update estimated duration label from fresh history.
                        _update_est()
                        # Enable Retry Failed when there are errors.
                        if _engine._last_failed:
                            _retry_btn.configure(state="normal")
                        else:
                            _retry_btn.configure(state="disabled")
                        # Show reboot banner if a restart is pending.
                        # Read the engine's cache — avoids a blocking registry
                        # OpenKey() call on the GUI thread (AV / group-policy
                        # can make registry access take several seconds).
                        if _engine._reboot_pending_cache:
                            _show_reboot()
                        _sched_refresh()
                        # If minimised to tray, bubble a notification and restore.
                        _tray = self._tray_icon
                        if _tray and _TRAY_AVAILABLE:
                            try:
                                _tray.notify("Updates complete", f"Windows Updater {VERSION}")
                            except Exception:
                                pass
                            _root_after(1500, _restore_tray)
                    elif action == "comp_status":
                        _had_work = True
                        # Update per-component status dot and current-name label.
                        comp_name, comp_state = value
                        if comp_state == "running":
                            self._prog_current_comp = (
                                _COMP_DISPLAY_NAMES.get(comp_name, comp_name))
                            # Scroll to show the new component header only
                            # when the user is already at the log bottom.
                            # Preserves position when they have scrolled up.
                            if _lw_yview()[1] >= 0.999:
                                _lw_cfg(state="normal")
                                _lw_see(_tk_end)
                                _lw_cfg(state="disabled")
                        self._last_drawn_pct = -1.0  # force segment redraw
                        dot = _csl.get(comp_name)
                        if dot:
                            _dk  = _dot_colour.get(comp_state, "dot_idle")
                            _sym = _status_syms.get(comp_state, "")
                            dot.configure(
                                text=_sym,
                                fg=_theme[_dk])
                    elif action == "run_complete":
                        _had_work = True
                        failures = value
                        # Show dry-run summary when dry_run is active.
                        if _dry_run_var.get():
                            _show_dry_run()
                        # Show completion dialog if notify_on_complete is enabled.
                        elif _engine._notify_on_complete:
                            if failures:
                                _msgbox("warn", "Updates Complete",
                                    f"Updates finished with {failures} error(s).\nCheck the log for details.")
                            else:
                                _msgbox("info", "Updates Complete", "All updates completed successfully.")
                except queue.Empty:
                    break

            if log_batch:
                _lw_cfg(state="normal")
                # One timestamp per flush (seconds granularity is enough).
                _ts = datetime.datetime.now().strftime("%H:%M:%S ")
                # groupby on the *unsorted* batch — preserves chronological order.
                _first_in_flush = True
                for tag, group in _groupby(log_batch, key=_batch_key):
                    lines_in_group = [m for m, _ in group]
                    for i, msg in enumerate(lines_in_group):
                        if tag == "header":
                            # Headers get a blank separator line then the header.
                            _lw_insert(_tk_end, "\n", "info")
                            _lw_insert(_tk_end, msg + "\n", "header")
                        else:
                            # Timestamp prefix on the first line of each flush,
                            # then indent-aligned spaces for subsequent lines.
                            if _first_in_flush and i == 0:
                                _lw_insert(_tk_end, _ts, "ts")
                            else:
                                _lw_insert(_tk_end, " " * len(_ts), "ts")
                            _lw_insert(_tk_end, msg + "\n", tag)
                        _first_in_flush = False
                _llc += len(log_batch)
                if _llc > _max_log:
                    excess = _llc - _max_log
                    _lw.delete("1.0", f"{excess + 1}.0")
                    _llc = _max_log
                self._log_line_count = _llc  # write-back: persist trim result
                # Re-run search after insert AND after trim — trimmed lines
                # may have had highlights, leaving the count label stale.
                if _lsv is not None and _lsv.get():
                    _search_fn()
                # Auto-scroll only when the view is already at the bottom.
                # If the user has scrolled up to review earlier output,
                # do not forcibly jump back down on every flush.
                if _lw_yview()[1] >= 0.999:
                    _lw_see(_tk_end)
                _lw_cfg(state="disabled")

            # Compute wm_state ONCE per tick — used for both:
            #   (a) skipping _redraw when minimised to tray
            #   (b) choosing the adaptive poll delay
            # MUST be assigned before the `if not _withdrawn` guard below.
            try:
                _withdrawn = self.root.wm_state() == "withdrawn"
            except tk.TclError:
                _withdrawn = False

            # Redraw progress once per tick; skip when minimised to tray.
            if not _withdrawn:
                _redraw()

            # Adaptive poll delay:
            #   50 ms  — work done this tick (messages flowing)
            #  150 ms  — idle, window visible
            #  500 ms  — window withdrawn to tray (no UI updates needed)
            _delay = 500 if _withdrawn else (50 if _had_work else 150)
        except Exception as _poll_exc:
            # An unexpected error in the GUI poll loop (e.g. TclError from a
            # destroyed widget) must never kill the reschedule loop.  Log the
            # error at ERROR level and let the finally block restart the poll.
            logger.error("update_gui: unhandled error — %s", _poll_exc, exc_info=True)
        finally:
            # Unconditional reschedule — poll loop survives any exception.
            _root_after(_delay, self.update_gui)

    def _focus_search(self):
        """Focus the search entry and select its current content."""
        if self._search_entry is not None:
            try:
                self._search_entry.focus_set()
                if not self._search_ph_active[0]:
                    self._search_entry.select_range(0, "end")
            except tk.TclError:
                pass

    def _clear_log(self):
        """Erase the in-session log widget contents (file log is unaffected)."""
        lw   = self.log_widget
        _cfg = lw.configure  # bind once — avoids 2 LOAD_ATTR calls
        _cfg(state="normal")
        lw.delete("1.0", "end")
        self._log_line_count = 0  # reset cached counter
        # Remove any active search highlights and reset match count.
        try:
            lw.tag_remove("search_hl", "1.0", "end")
        except Exception:
            pass
        self._search_hl_active = False
        if self._search_count_var is not None:
            self._search_count_var.set("")
        _cfg(state="disabled")
        if self.root.focus_get() is lw:
            try:
                self._log_level_btn.focus_set()
            except Exception:
                self.root.focus_set()
        # Refocus the root only when the log widget itself currently holds
        # keyboard focus — avoids stealing the cursor from the search Entry,
        # Spinbox, or any other widget the user is actively typing into.
        try:
            if self.root.focus_get() is lw:
                self.root.focus_set()
        except tk.TclError:
            pass

    def _copy_log(self):
        """Copy all current log widget text to the system clipboard."""
        text = self.log_widget.get("1.0", "end-1c")
        if not text.strip():
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
        except tk.TclError as _e:
            logger.warning("_copy_log: clipboard operation failed: %s", _e)
            self._msgbox("warn", "Copy Log",
                         "Could not access the clipboard.\n"
                         "Another application may be holding it; try again.")
            return
        # Brief visual acknowledgement in the status bar.
        self._set_status(_COPY_LOG_SENTINEL, dot_key="dot_idle")
        def _reset_status():
            # Only reset if the sentinel is still displayed — a completed
            # run or health refresh may have updated the status bar in the
            # 2-second window, in which case we must not overwrite it.
            if (not self._running
                    and self.status_var.get() == _COPY_LOG_SENTINEL):
                self._set_status(
                    self._idle_status(self.dry_run_var.get()),
                    dot_key="dot_idle")
        self.root.after(2000, _reset_status)

    def _refresh_start_btn_label(self):
        """Update the Start button label to show how many components are selected.

        Called after any checkbox change so the user always knows exactly how
        many components will run before pressing the button.
        """
        self._refresh_start_pending = False  # clear coalescing flag
        if not self.comp_vars or not hasattr(self, "start_btn"):
            return
        try:
            if not self._start_btn_enabled:
                return
            n = sum(
                1 for name, var in self.comp_vars.items()
                if var.get() and self.engine.components.get(name, {}).get("available")
            )
            label = f"▶  Start Updates ({n})" if n else "▶  Start Updates"
            self.start_btn.configure(text=label)
        except tk.TclError:
            pass

    def _select_all_components(self):
        """Check all available components (Ctrl+A)."""
        for name, var in self.comp_vars.items():
            if self.engine.components.get(name, {}).get("available"):
                var.set(True)
        # No direct _refresh_start_btn_label() call here — the trace on each
        # var.set() already queues after(0, _refresh_start_btn_label).
        # A synchronous call from a key-event handler would re-enter
        # widget.configure() inside the key dispatch, risking swallowed events.

    def _deselect_all_components(self):
        """Uncheck all components (Ctrl+Shift+A)."""
        for var in self.comp_vars.values():
            var.set(False)
        # Same reasoning as _select_all_components above.

    def _show_log_menu(self):
        """Show a themed dropdown panel listing log files with metadata.

        Built as an overrideredirect Toplevel so it obeys the app's full
        colour scheme — no platform menu rendering.  Closes on any click
        outside the panel or on Escape.
        """
        if self._log_menu_open:
            return
        self._log_menu_open = True
        t     = self._theme
        _sbg  = t["widget_bg"]
        _hbg  = t["btn_hover"]
        _fg   = t["fg"]
        _dim  = t["tag_debug"]
        _brd  = t["border"]
        _sec  = t["section_bg"]
        panel = tk.Toplevel(self.root)
        panel.withdraw()
        panel.overrideredirect(True)      # no titlebar / window chrome
        panel.transient(self.root)        # keep above main window; no taskbar entry
        panel.configure(bg=_brd)         # 1-px border via outer bg

        inner = tk.Frame(panel, bg=_sbg, bd=0)
        inner.pack(padx=1, pady=1, fill="both", expand=True)

        # ── Header ────────────────────────────────────────────────────────────
        hdr = tk.Frame(inner, bg=_sec, bd=0)
        hdr.pack(fill="x")
        tk.Label(hdr, text="📋  Log Files",
                 bg=_sec, fg=_fg,
                 font=("Segoe UI", 10, "bold"),
                 padx=10, pady=8).pack(side="left")
        def _menu_close(_e=None):
            self._log_menu_open = False
            try: panel.destroy()
            except tk.TclError: pass
        self._make_close_x(hdr, _menu_close, _sec, _dim, _fg)
        tk.Frame(inner, bg=_brd, height=1, bd=0).pack(fill="x")

        # ── File rows ─────────────────────────────────────────────────────────
        added = False
        for path in _LOG_FILES:
            if not os.path.exists(path):
                continue
            added = True
            try:
                size_b = os.path.getsize(path)
                size_s = (f"{size_b / 1024:.1f} KB"
                          if size_b < 1_048_576
                          else f"{size_b / 1_048_576:.1f} MB")
                mtime  = datetime.datetime.fromtimestamp(
                    os.path.getmtime(path)).strftime("%d %b  %H:%M")
                meta   = f"{size_s}  ·  {mtime}"
            except OSError:
                meta = ""
            name = os.path.basename(path)

            row = tk.Frame(inner, bg=_sbg, bd=0, cursor="hand2")
            row.pack(fill="x")

            left = tk.Frame(row, bg=_sbg, bd=0)
            left.pack(side="left", fill="both", expand=True,
                      padx=(12, 8), pady=6)
            lbl_name = tk.Label(left, text=name,
                                bg=_sbg, fg=_fg,
                                font=("Segoe UI", 9, "bold"), anchor="w")
            lbl_name.pack(fill="x")
            if meta:
                lbl_meta = tk.Label(left, text=meta,
                                    bg=_sbg, fg=_dim,
                                    font=("Segoe UI", 8), anchor="w")
                lbl_meta.pack(fill="x")
            else:
                lbl_meta = None

            # Hover highlight — covers the row frame and all its children.
            def _bind_hover(r, children, p=path):
                def _enter(_e):
                    r.configure(bg=_hbg)
                    for c in children:
                        try: c.configure(bg=_hbg)
                        except tk.TclError: pass
                def _leave(_e):
                    r.configure(bg=_sbg)
                    for c in children:
                        try: c.configure(bg=_sbg)
                        except tk.TclError: pass
                def _click(_e):
                    _menu_close()
                    self._open_file(p)
                for w in [r] + children:
                    w.bind("<Enter>",    _enter)
                    w.bind("<Leave>",    _leave)
                    w.bind("<Button-1>", _click)
            _children = [left, lbl_name] + ([lbl_meta] if lbl_meta else [])
            _bind_hover(row, _children)

            tk.Frame(inner, bg=_brd, height=1, bd=0).pack(fill="x")

        if not added:
            tk.Label(inner, text="No log files found",
                     bg=_sbg, fg=_dim,
                     font=("Segoe UI", 9),
                     padx=12, pady=8).pack(fill="x")
            tk.Frame(inner, bg=_brd, height=1, bd=0).pack(fill="x")

        # ── Footer: open folder ───────────────────────────────────────────────
        foot = tk.Frame(inner, bg=_sbg, bd=0, cursor="hand2")
        foot.pack(fill="x")
        lbl_folder = tk.Label(foot, text="📂  Open log folder",
                              bg=_sbg, fg=_dim,
                              font=("Segoe UI", 9),
                              padx=12, pady=7, anchor="w",
                              cursor="hand2")
        lbl_folder.pack(fill="x")

        def _fenter(_e):
            foot.configure(bg=_hbg); lbl_folder.configure(bg=_hbg, fg=_fg)
        def _fleave(_e):
            foot.configure(bg=_sbg); lbl_folder.configure(bg=_sbg, fg=_dim)
        def _fclick(_e):
            _menu_close(); self._open_file(_BASE_DIR)
        for _w in (foot, lbl_folder):
            _w.bind("<Enter>",    _fenter)
            _w.bind("<Leave>",    _fleave)
            _w.bind("<Button-1>", _fclick)

        # ── Position below the pointer, nudge if near screen edges ───────────
        panel.update_idletasks()
        pw = panel.winfo_reqwidth()
        ph = panel.winfo_reqheight()
        sx = self.root.winfo_screenwidth()
        sy = self.root.winfo_screenheight()
        px = self.root.winfo_pointerx()
        py = self.root.winfo_pointery() + 4   # small gap below cursor
        if px + pw > sx:
            px = sx - pw - 4
        if py + ph > sy:
            py = py - ph - 8    # flip above cursor if no room below
        panel.geometry(f"+{px}+{py}")

        # ── Close on Escape or click outside (no grab — non-modal dropdown) ──
        # Log menu is intentionally non-modal: user can dismiss by clicking away
        # (FocusOut) or pressing Escape. grab_set() was removed because it
        # prevented FocusOut from firing, making the panel impossible to dismiss
        # by clicking outside.
        panel.bind("<Escape>", _menu_close)
        panel.bind("<FocusOut>",
                   lambda _e: _menu_close() if _e.widget is panel else None)
        # Note: no mousewheel binding — the log menu shows at most 4 rotated
        # log files and is always short enough to display without scrolling.

        panel.bind("<Destroy>",
                   lambda _e: setattr(self, "_log_menu_open", False)
                   if _e.widget is panel else None)
        self._apply_titlebar_theme(panel)
        panel.deiconify()
        panel.focus_set()

    def _open_file(self, path):
        """Open a file with the system default application."""
        try:
            os.startfile(path)
        except Exception as e:
            self._msgbox("error", "Error", f"Could not open file:\n{e}")

    def _show_shortcuts(self):
        """Keyboard shortcuts — overrideredirect panel, matches all other menus."""
        if self._shortcuts_open:
            return
        self._shortcuts_open = True
        t    = self._theme
        _sbg = t["widget_bg"]
        _sec = t["section_bg"]
        _fg  = t["fg"]
        _dim = t["tag_debug"]
        _brd = t["border"]
        _acc = t["accent"]

        win = tk.Toplevel(self.root)
        win.withdraw()
        win.overrideredirect(True)
        win.configure(bg=_brd)
        win.transient(self.root)
        win.grab_set()

        outer = tk.Frame(win, bg=_sbg, bd=0)
        outer.pack(padx=1, pady=1, fill="both", expand=True)

        # ── Header ────────────────────────────────────────────────────────────
        hdr = tk.Frame(outer, bg=_sec, bd=0)
        hdr.pack(fill="x")
        tk.Label(hdr, text="❓  Keyboard Shortcuts",
                 bg=_sec, fg=_fg,
                 font=("Segoe UI", 10, "bold"),
                 padx=10, pady=8).pack(side="left")
        def _close(_e=None):
            self._shortcuts_open = False
            try:
                win.grab_release(); win.destroy()
            except tk.TclError:
                pass
        self._make_close_x(hdr, _close, _sec, _dim, _fg)
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")

        # ── Shortcut rows ─────────────────────────────────────────────────────
        body = tk.Frame(outer, bg=_sbg, bd=0)
        body.pack(fill="both", expand=True, padx=20, pady=12)
        for i, (key, desc) in enumerate(_SHORTCUTS):
            tk.Label(body, text=key,
                     bg=_sbg, fg=_acc,
                     font=("Segoe UI", 9, "bold"),
                     anchor="w", width=18).grid(
                row=i, column=0, sticky="w", pady=2)
            tk.Label(body, text=desc,
                     bg=_sbg, fg=_fg,
                     font=("Segoe UI", 9),
                     anchor="w").grid(
                row=i, column=1, sticky="w", padx=(8, 12), pady=2)

        # ── Footer ────────────────────────────────────────────────────────────
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")
        foot = tk.Frame(outer, bg=_sbg, bd=0)
        foot.pack(fill="x", padx=20, pady=8)
        self._make_btn(foot, "Close", _close).pack(side="right")

        # ── Position centred over main window ─────────────────────────────────
        win.update_idletasks()
        _ww, _wh = win.winfo_reqwidth(),  win.winfo_reqheight()
        _pw, _ph = self.root.winfo_width(), self.root.winfo_height()
        _px, _py = self.root.winfo_rootx(), self.root.winfo_rooty()
        _sx, _sy = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(
            f"+{max(4, min(_px + (_pw - _ww) // 2, _sx - _ww - 4))}"
            f"+{max(4, min(_py + (_ph - _wh) // 2, _sy - _wh - 4))}")
        win.bind("<Escape>", _close)
        win.bind("<Destroy>",
                 lambda _e: setattr(self, "_shortcuts_open", False)
                 if _e.widget is win else None)
        self._apply_titlebar_theme(win)
        win.deiconify()
        win.focus_set()

    def _show_log_level_panel(self):
        """Log-level filter picker — overrideredirect panel, same style as all other menus.

        Four radio-dot rows (All / Info+ / Warn+ / Error).  Selecting a level
        applies the filter immediately via _apply_log_filter() and closes.

        Does NOT bind <FocusOut> to close: grab_set() keeps focus inside the
        window, so FocusOut would never fire reliably.  Escape + ✕ suffice.
        """
        if self._log_level_panel_open:
            return
        self._log_level_panel_open = True
        t    = self._theme
        _sbg = t["widget_bg"]
        _sec = t["section_bg"]
        _fg  = t["fg"]
        _dim = t["tag_debug"]
        _brd = t["border"]
        _acc = t["accent"]
        _hbg = t["btn_hover"]

        win = tk.Toplevel(self.root)
        win.withdraw()
        win.overrideredirect(True)
        win.configure(bg=_brd)
        win.transient(self.root)
        win.grab_set()

        outer = tk.Frame(win, bg=_sbg, bd=0)
        outer.pack(padx=1, pady=1, fill="both", expand=True)

        # ── Header ────────────────────────────────────────────────────────────
        hdr = tk.Frame(outer, bg=_sec, bd=0)
        hdr.pack(fill="x")
        tk.Label(hdr, text="🔎  Log Level Filter",
                 bg=_sec, fg=_fg,
                 font=("Segoe UI", 10, "bold"),
                 padx=10, pady=8).pack(side="left")
        def _close(_e=None):
            self._log_level_panel_open = False
            try:
                win.grab_release(); win.destroy()
            except tk.TclError:
                pass
            # Return focus to log level button so keyboard
            # navigation continues from a predictable location.
            try:
                self._log_level_btn.focus_set()
            except Exception:
                pass
        self._make_close_x(hdr, _close, _sec, _dim, _fg)
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")

        # ── Section label ─────────────────────────────────────────────────────
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x", pady=(6, 0))
        tk.Label(outer, text="FILTER LEVEL",
                 bg=_sbg, fg=_dim,
                 font=("Segoe UI", 8, "bold"),
                 padx=12, pady=4, anchor="w").pack(fill="x")

        # ── Radio rows ────────────────────────────────────────────────────────
        _levels = (
            ("All",   "Show all messages"),
            ("Info+", "Info, warnings & errors"),
            ("Warn+", "Warnings & errors only"),
            ("Error", "Errors only"),
        )
        _active = self.log_level_var.get()
        _cs = 14

        for key, desc in _levels:
            is_act = (key == _active)
            row = tk.Frame(outer, bg=_sbg, bd=0, cursor="hand2")
            row.pack(fill="x", padx=2)
            dot_c = tk.Canvas(row, width=_cs, height=_cs,
                              bg=_sbg, bd=0, highlightthickness=0)
            dot_c.pack(side="left", padx=(12, 6), pady=5)

            def _draw_dot(c, active, bg=_sbg, acc=_acc, brd=_brd):
                c.delete("all")
                if active:
                    c.create_oval(1, 1, _cs-1, _cs-1, fill=acc, outline=acc)
                    c.create_oval(4, 4, _cs-4, _cs-4, fill="white", outline="")
                else:
                    c.create_oval(1, 1, _cs-1, _cs-1, fill=bg, outline=brd)
            _draw_dot(dot_c, is_act)

            left = tk.Frame(row, bg=_sbg, bd=0)
            left.pack(side="left", fill="x", expand=True, pady=5)
            lbl_key = tk.Label(left, text=key, anchor="w",
                               bg=_sbg, fg=_acc if is_act else _fg,
                               font=("Segoe UI", 9,
                                     "bold" if is_act else "normal"))
            lbl_key.pack(fill="x")
            lbl_desc = tk.Label(left, text=desc, anchor="w",
                                bg=_sbg, fg=_dim, font=("Segoe UI", 8))
            lbl_desc.pack(fill="x")

            def _make_pick(v):
                def _pick(_e=None):
                    self.log_level_var.set(v)
                    self._cur_min_level = _LOG_FILTER_MIN.get(v, 0)
                    self._apply_log_filter()
                    _close()
                    try:
                        self._log_level_btn.focus_set()
                    except Exception:
                        pass
                return _pick

            def _make_hover(r, dc, lk, ld):
                kids = [dc, lk, ld]
                def _enter(_e):
                    r.configure(bg=_hbg)
                    for w in kids:
                        try: w.configure(bg=_hbg)
                        except tk.TclError: pass
                def _leave(_e):
                    r.configure(bg=_sbg)
                    for w in kids:
                        try: w.configure(bg=_sbg)
                        except tk.TclError: pass
                for w in [r] + kids:
                    w.bind("<Enter>", _enter)
                    w.bind("<Leave>", _leave)

            _pick_fn = _make_pick(key)
            for w in (row, dot_c, left, lbl_key, lbl_desc):
                w.bind("<Button-1>", _pick_fn)
            # takefocus=True puts rows in Tab order so keyboard users
            # can navigate here. Return and Space then select the level.
            row.configure(takefocus=True)
            row.bind("<Return>", _pick_fn)
            row.bind("<space>",  _pick_fn)
            # Subtle focus ring: accent border when row is focused.
            row.bind("<FocusIn>",
                     lambda _e, r=row: r.configure(
                         highlightthickness=1,
                         highlightbackground=_acc))
            row.bind("<FocusOut>",
                     lambda _e, r=row: r.configure(
                         highlightthickness=0))
            _make_hover(row, dot_c, lbl_key, lbl_desc)
            tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")

        # ── Footer ────────────────────────────────────────────────────────────
        foot = tk.Frame(outer, bg=_sbg, bd=0)
        foot.pack(fill="x", padx=20, pady=8)
        self._make_btn(foot, "Close", _close).pack(side="right")

        win.update_idletasks()
        _ww, _wh = win.winfo_reqwidth(), win.winfo_reqheight()
        _pw, _ph = self.root.winfo_width(),  self.root.winfo_height()
        _px, _py = self.root.winfo_rootx(),  self.root.winfo_rooty()
        _sx, _sy = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(
            f"+{max(4, min(_px + (_pw - _ww) // 2, _sx - _ww - 4))}"
            f"+{max(4, min(_py + (_ph - _wh) // 2, _sy - _wh - 4))}")
        # Arrow key navigation: Up/Down cycle through the level rows.
        _level_keys = [k for k, _ in _levels]
        def _nav(direction, _e=None):
            cur = self.log_level_var.get()
            try:
                idx = (_level_keys.index(cur) + direction) % len(_level_keys)
            except ValueError:
                idx = 0
            self.log_level_var.set(_level_keys[idx])
            self._cur_min_level = _LOG_FILTER_MIN.get(_level_keys[idx], 0)
            self._apply_log_filter()
            _close()
            # Return focus to the button so repeated arrow presses
            # continue working without requiring a mouse click.
            try:
                self._log_level_btn.focus_set()
            except Exception:
                pass
        win.bind("<Up>",   lambda _e: _nav(-1))
        win.bind("<Down>", lambda _e: _nav(+1))
        win.bind("<Escape>", _close)
        win.bind("<Destroy>",
                 lambda _e: setattr(self, "_log_level_panel_open", False)
                 if _e.widget is win else None)
        self._apply_titlebar_theme(win)
        win.deiconify()
        win.focus_set()

    def _apply_log_filter(self):
        """Retroactively elide/show log lines based on current _cur_min_level.

        Called on level selection and by _apply_theme (tag_configure resets elide).
        """
        if not hasattr(self, "log_widget"):
            return
        lw = self.log_widget
        min_lvl = self._cur_min_level
        for lvl in ("debug", "info", "warn", "error"):
            try:
                lw.tag_configure(lvl, elide=(_LOG_LEVEL_ORDER[lvl] < min_lvl))
            except tk.TclError:
                pass
        # Re-run search so the match count reflects only visible lines.
        # Elided lines still have search_hl tags but are invisible — the
        # count label would otherwise show stale numbers after filter changes.
        if self._log_search_var is not None and self._log_search_var.get():
            self._on_log_search()

    def open_settings(self):
        """Settings panel — overrideredirect, scrollable canvas body.

        Design mirrors open_log_menu / _show_log_level_panel:
          • 1-px t["border"] outer → t["widget_bg"] inner
          • section_bg header with title + ✕
          • ALL-CAPS dim section labels separated by 1-px borders
          • Canvas + scrollbar so it scrolls on small screens
          • Closes on Escape, ✕, Save, Cancel — NOT FocusOut
            (grab_set keeps focus inside; FocusOut fires on Spinbox focus
            and would prematurely destroy the window).
        """
        t    = self._theme
        _sbg = t["widget_bg"]
        _sec = t["section_bg"]
        _fg  = t["fg"]
        _dim = t["tag_debug"]
        _brd = t["border"]
        _acc = t["accent"]
        _afg = t["accent_fg"]

        if self._settings_open:
            return
        self._settings_open = True

        with self.engine.config_lock:
            cfg = copy.deepcopy(self.engine.config)

        win = tk.Toplevel(self.root)
        win.withdraw()
        win.overrideredirect(True)
        win.configure(bg=_brd)
        win.transient(self.root)
        win.grab_set()

        outer = tk.Frame(win, bg=_sbg, bd=0)
        outer.pack(padx=1, pady=1, fill="both", expand=True)

        # ── Header ────────────────────────────────────────────────────────────
        hdr = tk.Frame(outer, bg=_sec, bd=0)
        hdr.pack(fill="x")
        tk.Label(hdr, text="⚙  Settings",
                 bg=_sec, fg=_fg,
                 font=("Segoe UI", 10, "bold"),
                 padx=10, pady=8).pack(side="left")
        def _close(_e=None):
            try:
                win.grab_release(); win.destroy()
            except tk.TclError:
                pass
        self._make_close_x(hdr, _close, _sec, _dim, _fg)
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")

        # ── Scrollable body ───────────────────────────────────────────────────
        _canvas = tk.Canvas(outer, bg=_sbg, bd=0, highlightthickness=0)
        _vsb    = ttk.Scrollbar(outer, orient="vertical", command=_canvas.yview)
        _canvas.configure(yscrollcommand=_vsb.set)
        _vsb.pack(side="right", fill="y")
        _canvas.pack(side="left", fill="both", expand=True)
        body = tk.Frame(_canvas, bg=_sbg, bd=0)
        _bid = _canvas.create_window((0, 0), window=body, anchor="nw")
        body.bind("<Configure>", lambda _e: _canvas.configure(
            scrollregion=_canvas.bbox("all")))
        _canvas.bind("<Configure>", lambda _e: _canvas.itemconfig(
            _bid, width=_e.width))
        def _mw_scroll(e):
            _canvas.yview_scroll(int(-1 * (e.delta / 120)), "units")
        win.bind("<MouseWheel>",    _mw_scroll)
        _canvas.bind("<MouseWheel>", _mw_scroll)
        body.bind("<MouseWheel>",   _mw_scroll)

        # ── Helpers ───────────────────────────────────────────────────────────
        def _section(title):
            tk.Frame(body, bg=_brd, height=1, bd=0).pack(fill="x", pady=(6, 0))
            tk.Label(body, text=title, bg=_sbg, fg=_dim,
                     font=("Segoe UI", 8, "bold"),
                     padx=12, pady=4, anchor="w").pack(fill="x")

        def _toggle_row(label_text, var):
            """Full-width clickable row: canvas checkbox + label + hover."""
            _cs = 14
            row = tk.Frame(body, bg=_sbg, bd=0, cursor="hand2")
            row.pack(fill="x", padx=2)
            chk = tk.Canvas(row, width=_cs, height=_cs,
                            bg=_sbg, bd=0, highlightthickness=0)
            chk.pack(side="left", padx=(12, 6), pady=5)
            lbl = tk.Label(row, text=label_text, bg=_sbg, fg=_fg,
                           font=("Segoe UI", 9), anchor="w")
            lbl.pack(side="left", fill="x", expand=True, pady=5)
            def _draw(v):
                chk.delete("all")
                if v:
                    chk.create_rectangle(1, 1, _cs-1, _cs-1,
                                         fill=_acc, outline=_acc)
                    chk.create_line(3, 7, 6, 10, fill="white", width=2)
                    chk.create_line(6, 10, 11, 4, fill="white", width=2)
                else:
                    chk.create_rectangle(1, 1, _cs-1, _cs-1,
                                         fill=_sbg, outline=_brd)
            _draw(var.get())
            def _toggle(_e=None):
                var.set(not var.get()); _draw(var.get())
            def _enter(_e):
                row.configure(bg=t["btn_hover"])
                chk.configure(bg=t["btn_hover"])
                lbl.configure(bg=t["btn_hover"])
            def _leave(_e):
                row.configure(bg=_sbg)
                chk.configure(bg=_sbg)
                lbl.configure(bg=_sbg)
            for w in (row, chk, lbl):
                w.bind("<Button-1>", _toggle)
                w.bind("<Enter>", _enter)
                w.bind("<Leave>", _leave)

        # ── Section 1: Run Behaviour ──────────────────────────────────────────
        _section("RUN BEHAVIOUR")
        run_flags = [
            ("Debug Mode",   "debug_mode",   self.debug_var),
            ("Dry Run",      "dry_run",      self.dry_run_var),
            ("Auto Restart", "auto_restart", self.auto_restart_var),
            ("Dark Mode",    "dark_mode",    self._dark),
        ]
        flag_vars = {}
        for label, key, src_var in run_flags:
            var = tk.BooleanVar(value=cfg.get(key, src_var.get()))
            _toggle_row(label, var)
            flag_vars[key] = (var, src_var)

        # ── Section 2: Options ────────────────────────────────────────────────
        _section("OPTIONS")
        bool_vars = {}
        for label, key in _SETTINGS_BOOL_FIELDS:
            var = tk.BooleanVar(value=cfg.get(key, DEFAULT_CONFIG.get(key, False)))
            _toggle_row(label, var)
            bool_vars[key] = var

        # ── Section 3: Numeric Settings ───────────────────────────────────────
        _section("NUMERIC SETTINGS")
        spinboxes = {}
        _vcmd = (body.register(lambda s: s.isdigit() or s == ""), "%P")
        for label, key, lo, hi in _SETTINGS_NUMERIC_FIELDS:
            row = tk.Frame(body, bg=_sbg, bd=0)
            row.pack(fill="x", padx=12, pady=3)
            tk.Label(row, text=label, bg=_sbg, fg=_fg,
                     font=("Segoe UI", 9), anchor="w").pack(
                side="left", fill="x", expand=True)
            sb = tk.Spinbox(row, from_=lo, to=hi, width=7,
                            bg=t["widget_bg"], fg=t["widget_fg"],
                            insertbackground=_fg,
                            buttonbackground=t["btn_bg"],
                            relief="flat", borderwidth=1,
                            highlightbackground=_brd, highlightthickness=1,
                            validate="key", validatecommand=_vcmd)
            sb.delete(0, "end"); sb.insert(0, str(cfg.get(key, lo)))
            sb.bind("<FocusIn>", lambda _e, s=sb: s.select_range(0, "end"))
            sb.pack(side="right")
            spinboxes[key] = sb

        # ── Section 4: Min Python Version ─────────────────────────────────────
        _section("MIN PYTHON VERSION")
        _vr = tk.Frame(body, bg=_sbg, bd=0)
        _vr.pack(fill="x", padx=12, pady=3)
        tk.Label(_vr, text="Version", bg=_sbg, fg=_fg,
                 font=("Segoe UI", 9), anchor="w").pack(
            side="left", fill="x", expand=True)
        min_ver = cfg.get("min_python_version", [3, 9])
        _vvcmd  = (_vr.register(lambda s: s.isdigit() or s == ""), "%P")
        major_sb = tk.Spinbox(_vr, from_=3, to=9, width=3,
                              bg=t["widget_bg"], fg=t["widget_fg"],
                              insertbackground=_fg, buttonbackground=t["btn_bg"],
                              relief="flat", borderwidth=1,
                              highlightbackground=_brd, highlightthickness=1,
                              validate="key", validatecommand=_vvcmd)
        major_sb.delete(0, "end"); major_sb.insert(0, str(min_ver[0]))
        major_sb.bind("<FocusIn>",
                      lambda _e, s=major_sb: s.select_range(0, "end"))
        major_sb.pack(side="left", padx=(0, 2))
        tk.Label(_vr, text=".", bg=_sbg, fg=_fg,
                 font=("Segoe UI", 9)).pack(side="left")
        minor_sb = tk.Spinbox(_vr, from_=0, to=20, width=3,
                              bg=t["widget_bg"], fg=t["widget_fg"],
                              insertbackground=_fg, buttonbackground=t["btn_bg"],
                              relief="flat", borderwidth=1,
                              highlightbackground=_brd, highlightthickness=1,
                              validate="key", validatecommand=_vvcmd)
        minor_sb.delete(0, "end"); minor_sb.insert(0, str(min_ver[1]))
        minor_sb.bind("<FocusIn>",
                      lambda _e, s=minor_sb: s.select_range(0, "end"))
        minor_sb.pack(side="left", padx=(2, 0))

        # ── Section 5: Component Presets ──────────────────────────────────────
        _section("COMPONENT PRESETS")
        with self.engine.config_lock:
            _current_presets = dict(self.engine.config.get("presets", {}))

        preset_frame = tk.Frame(body, bg=_sbg, bd=0)
        preset_frame.pack(fill="x", padx=12, pady=(2, 6))
        preset_lb = tk.Listbox(
            preset_frame, height=4, width=22, selectmode="browse",
            bg=t["widget_bg"], fg=t["widget_fg"],
            selectbackground=_acc, selectforeground=_afg,
            relief="flat", highlightthickness=1, highlightbackground=_brd,
            font=("Segoe UI", 9), activestyle="none")
        _preset_vsb = ttk.Scrollbar(preset_frame, orient="vertical",
                                    command=preset_lb.yview)
        preset_lb.configure(yscrollcommand=_preset_vsb.set)
        preset_lb.pack(side="left", fill="y")
        _preset_vsb.pack(side="left", fill="y")

        def _lb_refresh():
            preset_lb.delete(0, "end")
            for _n in _current_presets:
                preset_lb.insert("end", _n)
        _lb_refresh()

        pbf = tk.Frame(preset_frame, bg=_sbg, bd=0)
        pbf.pack(side="left", padx=(6, 0), anchor="n")

        def _preset_load():
            sel = preset_lb.curselection()
            if not sel: return
            data = _current_presets.get(preset_lb.get(sel[0]), {})
            for comp, var in self.comp_vars.items():
                if comp in data: var.set(data[comp])
            _close()

        def _preset_save_new():
            if not self.comp_vars:
                self._msgbox("warn", "Presets",
                             "Components not yet detected.", parent=win)
                return
            nv = tk.StringVar()
            d  = tk.Toplevel(win)
            d.withdraw()
            d.overrideredirect(True)
            d.transient(win); d.grab_set()
            d.configure(bg=_brd)
            _d_outer = tk.Frame(d, bg=_sbg, bd=0)
            _d_outer.pack(padx=1, pady=1, fill="both", expand=True)
            _d_hdr = tk.Frame(_d_outer, bg=_sec, bd=0)
            _d_hdr.pack(fill="x")
            tk.Label(_d_hdr, text="➕ New Preset",
                     bg=_sec, fg=_fg,
                     font=("Segoe UI", 10, "bold"), padx=10).pack(
                side="left", pady=8)
            def _d_close(_e=None):
                try:
                    d.grab_release()
                    d.destroy()
                except tk.TclError:
                    pass
            self._make_close_x(_d_hdr, _d_close, _sec, _dim, _fg)
            tk.Frame(_d_outer, bg=_brd, height=1, bd=0).pack(fill="x")
            b2 = tk.Frame(_d_outer, bg=_sbg); b2.pack(padx=20, pady=12)
            tk.Label(b2, text="Name:", bg=_sbg, fg=_fg,
                     font=("Segoe UI", 9)).grid(row=0, column=0, sticky="w")
            ent = tk.Entry(b2, textvariable=nv, width=18,
                           font=("Segoe UI", 9), relief="flat", bd=1)
            ent.grid(row=0, column=1, padx=(6, 0))
            ent.focus_set()
            def _commit():
                nm = nv.get().strip()
                if not nm: return
                sv = {c: v.get() for c, v in self.comp_vars.items()}
                with self.engine.config_lock:
                    self.engine.config.setdefault("presets", {})[nm] = sv
                    snap = copy.deepcopy(self.engine.config)
                save_config(snap)
                _current_presets[nm] = sv; _lb_refresh(); _d_close()
            br = tk.Frame(b2, bg=_sbg)
            br.grid(row=1, column=0, columnspan=2, pady=(8, 0))
            self._make_btn(br, "Save", _commit, accent=True).pack(
                side="left", padx=(0, 6))
            self._make_btn(br, "Cancel", _d_close).pack(side="left")
            ent.bind("<Return>", lambda _e: _commit())
            d.bind("<Escape>", _d_close)
            d.update_idletasks()
            _dw, _dh   = d.winfo_reqwidth(),   d.winfo_reqheight()
            _wx2, _wy2 = win.winfo_rootx(),    win.winfo_rooty()
            _ww2, _wh2 = win.winfo_width(),    win.winfo_height()
            _sx2, _sy2 = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
            d.geometry(
                f"+{max(4, min(_wx2+(_ww2-_dw)//2, _sx2-_dw-4))}"
                f"+{max(4, min(_wy2+(_wh2-_dh)//2, _sy2-_dh-4))}")
            self._apply_titlebar_theme(d); d.deiconify()

        def _preset_delete():
            sel = preset_lb.curselection()
            if not sel: return
            nm = preset_lb.get(sel[0])
            if not self._msgbox("yesno", "Delete Preset",
                                f"Delete preset \"{nm}\"?", parent=win):
                return
            with self.engine.config_lock:
                self.engine.config.get("presets", {}).pop(nm, None)
                snap = copy.deepcopy(self.engine.config)
            save_config(snap); _current_presets.pop(nm, None); _lb_refresh()

        preset_lb.bind("<Double-Button-1>", lambda _e: _preset_load())
        self._make_btn(pbf, "Load",   _preset_load).pack(fill="x", pady=(0, 3))
        self._make_btn(pbf, "+ New",  _preset_save_new).pack(fill="x", pady=(0, 3))
        self._make_btn(pbf, "Delete", _preset_delete).pack(fill="x")

        # ── Save ──────────────────────────────────────────────────────────────
        def _save():
            try:
                new_cfg = {}
                _fl = _SETTINGS_FIELD_LABEL
                _lo = _SETTINGS_FIELD_LO
                _hi = _SETTINGS_FIELD_HI
                for key, sb in spinboxes.items():
                    raw = sb.get().strip()
                    if not raw:
                        self._msgbox("error", "Validation",
                            f"'{_fl.get(key, key)}' cannot be empty.", parent=win)
                        sb.focus_set(); sb.select_range(0, "end"); return
                    val = int(raw)
                    if not (_lo.get(key, 0) <= val <= _hi.get(key, 9999)):
                        self._msgbox("error", "Validation",
                            f"'{_fl.get(key, key)}' must be between "
                            f"{_lo.get(key, 0)} and {_hi.get(key, 9999)}.",
                            parent=win); return
                    new_cfg[key] = val
                for key, var in bool_vars.items():
                    new_cfg[key] = var.get()
                for fname, (sbw, vlo, vhi) in {
                        "Major": (major_sb, 3, 9),
                        "Minor": (minor_sb, 0, 20)}.items():
                    raw = sbw.get().strip()
                    if not raw:
                        self._msgbox("error", "Validation",
                            f"Python version {fname} cannot be empty.",
                            parent=win)
                        sbw.focus_set(); return
                    vv = int(raw)
                    if not (vlo <= vv <= vhi):
                        self._msgbox("error", "Validation",
                            f"Python version {fname} must be between "
                            f"{vlo} and {vhi}.", parent=win)
                        sbw.focus_set(); sbw.select_range(0, "end"); return
                new_cfg["min_python_version"] = [int(major_sb.get()),
                                                  int(minor_sb.get())]
                dark_changed = dry_changed = False
                for key, (dv, sv) in flag_vars.items():
                    nv2 = dv.get(); new_cfg[key] = nv2
                    if nv2 != sv.get():
                        sv.set(nv2)
                        if key == "dark_mode":  dark_changed = True
                        elif key == "dry_run":  dry_changed  = True
                with self.engine.config_lock:
                    self.engine.config.update(new_cfg)
                    snap = copy.deepcopy(self.engine.config)
                self.engine._notify_on_complete = bool(
                    new_cfg.get("notify_on_complete", True))
                self.engine._debug_mode = bool(new_cfg.get("debug_mode", False))
                save_config(snap)
                if dark_changed:
                    self._apply_theme()
                    # Also update the settings window's own titlebar so it
                    # immediately reflects the new light/dark mode without
                    # requiring the user to reopen the dialog.
                    try:
                        self._apply_titlebar_theme(win)
                    except Exception:
                        pass
                _set_console_visible(bool(new_cfg.get("debug_mode", False)))
                if dry_changed and not self._running:
                    _dr_suffix = " [DRY RUN]" if new_cfg["dry_run"] else ""
                    self.root.title(f"Windows Updater {VERSION}{_dr_suffix}")
                    self._set_status(self._idle_status(new_cfg["dry_run"]),
                                     dot_key="dot_idle")
                if "health_refresh_interval" in new_cfg and not self._running:
                    self._schedule_health_refresh()
                _close()
            except (ValueError, RuntimeError) as e:
                self._msgbox("error", "Validation", f"Invalid value: {e}", parent=win)

        # ── Footer ────────────────────────────────────────────────────────────
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")
        foot = tk.Frame(outer, bg=_sbg, bd=0)
        foot.pack(fill="x", padx=20, pady=8)
        self._make_btn(foot, "Save", _save, accent=True).pack(
            side="right", padx=(6, 0))
        self._make_btn(foot, "Cancel", _close).pack(side="right")
        tk.Label(foot, text="Enter = Save  ·  Esc = Cancel",
                 bg=_sbg, fg=_dim, font=("Segoe UI", 8)).pack(
            side="left")
        # Bind Enter to Save in the settings dialog.
        # Guard: only save when focus is NOT on a Spinbox or Entry widget
        # (those widgets handle Return internally for value confirmation).
        def _win_return(_e):
            focused = win.focus_get()
            if isinstance(focused, (tk.Spinbox, tk.Entry)):
                return   # let the widget handle it
            _save()
        win.bind("<Return>", _win_return)

        # ── Size + position ───────────────────────────────────────────────────
        win.update_idletasks()
        _req_h = body.winfo_reqheight()
        _max_h = int(self.root.winfo_screenheight() * 0.80)
        _canvas.configure(width=380, height=min(_req_h, _max_h - 120))
        win.update_idletasks()
        _ww, _wh = win.winfo_reqwidth(), win.winfo_reqheight()
        _pw, _ph = self.root.winfo_width(),  self.root.winfo_height()
        _px, _py = self.root.winfo_rootx(),  self.root.winfo_rooty()
        _sx, _sy = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(
            f"+{max(4, min(_px + (_pw - _ww) // 2, _sx - _ww - 4))}"
            f"+{max(4, min(_py + (_ph - _wh) // 2, _sy - _wh - 4))}")
        win.bind("<Escape>", _close)
        self._apply_titlebar_theme(win)
        win.deiconify()
        win.focus_set()
        win.wait_window()
        self._settings_open = False

    def _schedule_health_refresh(self):
        """Schedule the next automatic health refresh, if the interval is set."""
        self._cancel_health_refresh()
        with self.engine.config_lock:
            interval = self.engine.config.get("health_refresh_interval", 0)
        if interval > 0:
            self._health_refresh_id = self.root.after(
                interval * 1000, self._auto_refresh_health)

    def _cancel_health_refresh(self):
        """Cancel any pending automatic health refresh."""
        if self._health_refresh_id is not None:
            try:
                self.root.after_cancel(self._health_refresh_id)
            except Exception:
                pass
            self._health_refresh_id = None

    def _auto_refresh_health(self):
        """Fire a background health re-probe if the app is idle."""
        self._health_refresh_id = None
        if not self._running and not self._health_running:
            self.populate_health()
        # Reschedule regardless — populate_health itself will skip if busy.
        self._schedule_health_refresh()

    def _msgbox(self, kind: str, title: str, message: str,
                parent=None) -> "bool | None":
        """Show a themed modal dialog matching the app's dark/light mode.

        kind    'info' | 'warn' | 'error' | 'yesno'
        Returns True/False for 'yesno', None for the others.
        """
        t    = self._theme
        par  = parent if parent is not None else self.root
        _sec = t["section_bg"]
        _fg  = t["fg"]
        _dim = t["tag_debug"]
        _brd = t["border"]
        _wbg = t["widget_bg"]
        # Severity drives an emoji prefix + thin 2-px colour strip below the
        # header.  The header itself is always section_bg so every dialog
        # and panel in the app shares one consistent header treatment.
        if kind == "warn":
            _icon, _strip = "⚠️ ", _MSGBOX_WARN_HDR
        elif kind == "error":
            _icon, _strip = "✘ ", _MSGBOX_ERROR_HDR
        elif kind == "yesno":
            _icon, _strip = "❓ ", t["accent"]
        else:  # info
            _icon, _strip = "ℹ️ ", t["accent"]

        win = tk.Toplevel(par)
        win.withdraw()
        win.overrideredirect(True)
        win.transient(par)
        win.grab_set()
        win.configure(bg=_brd)

        outer = tk.Frame(win, bg=_wbg, bd=0)
        outer.pack(padx=1, pady=1, fill="both", expand=True)

        # Header: section_bg matches every other panel in the app.
        hdr = tk.Frame(outer, bg=_sec, bd=0)
        hdr.pack(fill="x")
        tk.Label(hdr, text=f"{_icon}{title}",
                 bg=_sec, fg=_fg,
                 font=("Segoe UI", 10, "bold"), padx=12).pack(side="left", pady=8)
        def _mb_close():
            try:
                win.grab_release()
                win.destroy()
            except tk.TclError:
                pass  # already destroyed (e.g. rapid double-click)
        self._make_close_x(hdr, _mb_close, _sec, _dim, _fg)
        tk.Frame(outer, bg=_strip, height=3, bd=0).pack(fill="x")

        # Message body
        body = tk.Frame(outer, bg=t["widget_bg"], bd=0)
        body.pack(fill="both", expand=True, padx=20, pady=12)
        tk.Label(body, text=message, bg=t["widget_bg"], fg=t["fg"],
                 font=("Segoe UI", 9), wraplength=340, justify="left"
                 ).pack(anchor="w")

        # Button row — nonlocal bool avoids the list-of-one closure workaround
        _result = False
        tk.Frame(outer, bg=t["border"], height=1, bd=0).pack(fill="x")
        btn_row = tk.Frame(outer, bg=t["widget_bg"], bd=0)
        btn_row.pack(padx=20, pady=8, anchor="e")
        if kind == "yesno":
            def _yes():
                nonlocal _result
                _result = True
                _mb_close()   # releases grab + destroys
            # _no: _mb_close() also handles the "No" case
            # (_result stays False — the nonlocal is never assigned).
            self._make_btn(btn_row, "Yes", _yes, accent=True
                           ).pack(side="left", padx=(0, 6))
            self._make_btn(btn_row, "No",  _mb_close
                           ).pack(side="left")
        else:
            self._make_btn(btn_row, "OK", _mb_close, accent=(kind == "info")
                           ).pack()

        win.update_idletasks()
        _pw, _ph = par.winfo_width(), par.winfo_height()
        _px, _py = par.winfo_rootx(), par.winfo_rooty()
        _ww, _wh = win.winfo_reqwidth(), win.winfo_reqheight()
        _sx, _sy = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(
            f"+{max(4, min(_px + (_pw - _ww) // 2, _sx - _ww - 4))}"
            f"+{max(4, min(_py + (_ph - _wh) // 2, _sy - _wh - 4))}")
        win.bind("<Escape>", lambda _e: _mb_close())
        self._apply_titlebar_theme(win)
        win.deiconify()
        win.wait_window()
        return _result

    def _toggle_dry_run(self):
        """Toggle dry-run mode on/off via Ctrl+D."""
        new_val = not self.dry_run_var.get()
        self.dry_run_var.set(new_val)
        # Mirror into engine config under lock and persist.
        with self.engine.config_lock:
            self.engine.config["dry_run"] = new_val
            _snap = copy.deepcopy(self.engine.config)
        save_config(_snap)
        # Reflect in window title so dry-run is visible even when minimised.
        _suffix = " [DRY RUN]" if new_val else ""
        self.root.title(f"Windows Updater {VERSION}{_suffix}")
        if not self._running:
            self._set_status(self._idle_status(new_val), dot_key="dot_idle")

    # ── Run History ───────────────────────────────────────────────────────────
    def _show_history(self):
        """Open the Run History dialog showing updhist.json contents."""
        if self._history_open:
            return
        self._history_open = True
        try:
            with open(HIST_FILE, "r", encoding="utf-8") as f:
                history = json.load(f)
            if not isinstance(history, list):
                history = []
        except (OSError, json.JSONDecodeError):
            history = []

        t    = self._theme
        _sbg = t["widget_bg"]
        _sec = t["section_bg"]
        _fg  = t["fg"]
        _dim = t["tag_debug"]
        _brd = t["border"]

        win = tk.Toplevel(self.root)
        win.withdraw()
        win.overrideredirect(True)
        win.transient(self.root)
        win.grab_set()
        win.configure(bg=_brd)

        outer = tk.Frame(win, bg=_sbg, bd=0)
        outer.pack(padx=1, pady=1, fill="both", expand=True)

        _hist_count  = len(history)
        _hist_s      = "s" if _hist_count != 1 else ""
        def _safe_fails(r):
            try: return int(r.get("failures", 0))
            except (TypeError, ValueError): return 0
        _total_fails = sum(_safe_fails(r) for r in history)
        _fail_e      = "error" if _total_fails == 1 else "errors"
        _fail_note   = f"  ·  {_total_fails} {_fail_e}" if _total_fails else ""
        _hdr_text    = f"Run History  ({_hist_count} run{_hist_s}{_fail_note})"

        hdr = tk.Frame(outer, bg=_sec, bd=0)
        hdr.pack(fill="x")
        tk.Label(hdr, text=f"📜  {_hdr_text}",
                 bg=_sec, fg=_fg,
                 font=("Segoe UI", 10, "bold"),
                 padx=10, pady=8).pack(side="left")

        if not history:
            body = tk.Frame(outer, bg=_sbg, bd=0)
            body.pack(fill="both", expand=True, padx=20, pady=12)
            tk.Label(body, text="No run history recorded yet.",
                     bg=_sbg, fg=_fg, font=("Segoe UI", 9)).pack()
            tk.Label(body,
                     text="Start an update run to record your first entry.",
                     bg=_sbg, fg=_dim,
                     font=("Segoe UI", 8)).pack(pady=(4, 0))
            self._make_btn(body, "Close", _hist_close).pack(pady=(12, 0))
            
        else:
            tree_frame = tk.Frame(outer, bg=_sbg, bd=0)
            tree_frame.pack(fill="both", expand=True, padx=8, pady=8)
            cols = ("Date/Time", "Components", "Failures", "Duration", "Mode")
            tree = ttk.Treeview(tree_frame, columns=cols, show="headings", height=12)
            widths = [145, 235, 58, 76, 72]  # Date wider for ISO timestamps
            # Sorting state: (col_name, ascending).
            _sort_state = {"col": None, "asc": True}

            def _sort_key(col, val):
                if col == "Failures":
                    m = _HIST_RE_DIGITS.search(val)
                    return int(m.group()) if m else 0
                if col == "Duration":
                    secs = 0
                    for n, unit in _HIST_RE_DUR_PARTS.findall(val):
                        secs += int(n) * 60 if unit == "m" else int(n)
                    return secs
                return val.lower()

            def _sort_by(col, _state=_sort_state):
                # Default: first click on Date/Time sorts newest-first (desc).
                default_asc = col != "Date/Time"
                asc = not _state["asc"] if _state["col"] == col else default_asc
                _state.update(col=col, asc=asc)
                rows = [(tree.set(k, col), k)
                        for k in tree.get_children("")]
                rows.sort(reverse=not asc,
                          key=lambda x: _sort_key(col, x[0]))
                for i, (_, k) in enumerate(rows):
                    tree.move(k, "", i)
                # Update heading text to show sort direction arrow.
                for c in cols:
                    arrow = (" ↑" if asc else " ↓") if c == col else ""
                    tree.heading(c, text=c + arrow)
                try:
                    tree.yview_moveto(0)
                except Exception:
                    pass

            for col, w in zip(cols, widths):
                tree.heading(col, text=col,
                             command=lambda c=col: _sort_by(c))
                tree.column(col, width=w, minwidth=50)
            tree.column("Failures", anchor="center")
            tree.column("Mode", anchor="center")
            sb = ttk.Scrollbar(tree_frame, orient="vertical", command=tree.yview)
            sb_x = ttk.Scrollbar(tree_frame, orient="horizontal", command=tree.xview)
            tree.configure(yscrollcommand=sb.set, xscrollcommand=sb_x.set)
            sb.pack(side="right", fill="y")
            sb_x.pack(side="bottom", fill="x")
            tree.pack(side="left", fill="both", expand=True)
            tree.tag_configure("error", background=t["tree_bad"])
            tree.tag_configure("dry",   background=t["tree_warn"])
            def _copy_sel_row(_e=None):
                sel = tree.selection()
                if not sel: return
                vals = tree.item(sel[0], "values")
                try:
                    win.clipboard_clear()
                    win.clipboard_append("\t".join(str(v) for v in vals))
                except Exception:
                    pass
            tree.bind("<Control-c>", _copy_sel_row)
            for rec in reversed(history):
                ts      = rec.get("timestamp", "?")
                comps   = ", ".join(_COMP_DISPLAY_NAMES.get(c, c)
                                    for c in rec.get("components", []))
                failures = rec.get("failures", 0)
                elapsed  = self._fmt_elapsed(rec.get("elapsed_s", 0))
                mode     = "🔵 Dry Run" if rec.get("dry_run") else "✅ Live"
                tag = "error" if failures else ("dry" if rec.get("dry_run") else "")
                _fail_cell = "✓" if not failures else f"✗ {failures}"
                # Replace the ISO "T" separator with a space for readability.
                _ts_display = ts.replace("T", " ")  if "T" in ts else ts
                tree.insert("", "end",
                            values=(_ts_display, comps, _fail_cell, elapsed, mode),
                            tags=(tag,) if tag else ())

            tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")
            btn_row = tk.Frame(outer, bg=_sbg, bd=0)
            btn_row.pack(fill="x", padx=20, pady=8)

            def _export_hist():
                ts  = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                path = filedialog.asksaveasfilename(
                    defaultextension=".json",
                    filetypes=[("JSON", "*.json"), ("CSV", "*.csv"), ("All", "*.*")],
                    initialfile=f"run_history_{ts}.json",
                    title="Export Run History", parent=win)
                if not path:
                    return
                ext = os.path.splitext(path)[1].lower()
                try:
                    with open(path, "w", encoding="utf-8",
                              newline="" if ext == ".csv" else None) as f:
                        if ext == ".csv":
                            w = csv.writer(f)
                            w.writerow(["Date/Time","Components","Failures",
                                        "Duration (s)","Dry Run"])
                            for r in history:
                                w.writerow([r.get("timestamp","").replace("T"," "),
                                            ";".join(
                                _COMP_DISPLAY_NAMES.get(c, c)
                                for c in r.get("components", [])
                            ),
                                            r.get("failures",0),
                                            r.get("elapsed_s",0),
                                            r.get("dry_run",False)])
                        else:
                            # Export raw history records as-is (JSON is
                            # machine-readable; raw field names are stable).
                            json.dump(history, f, indent=2)
                    self._msgbox("info", "Export History",
                                 f"Saved to:\n{path}", parent=win)
                except OSError as e:
                    self._msgbox("error", "Export History",
                                 f"Could not write file:\n{e}", parent=win)

            def _clear_hist():
                if not self._msgbox("yesno", "Clear History",
                                    "Delete all run history?", parent=win):
                    return
                try:
                    with open(HIST_FILE, "w", encoding="utf-8") as f:
                        json.dump([], f)
                    _hist_close()  # resets flag + releases grab
                except OSError as e:
                    self._msgbox("error", "Clear History",
                                 f"Could not clear history:\n{e}", parent=win)

            self._make_btn(btn_row, "Export…", _export_hist).pack(side="left", padx=(0, 6))
            self._make_btn(btn_row, "Clear History", _clear_hist).pack(side="left")
            self._make_btn(btn_row, "Close", win.destroy).pack(side="right")
            tk.Label(btn_row,
                     text="Click header to sort  ·  Ctrl+C copies row  ·  Esc to close",
                     bg=_sbg, fg=_dim,
                     font=("Segoe UI", 8),
                     anchor="e").pack(side="right", padx=(0, 8))

        win.update_idletasks()
        _pw, _ph = self.root.winfo_width(),   self.root.winfo_height()
        _px, _py = self.root.winfo_rootx(),   self.root.winfo_rooty()
        _sx, _sy = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        _ww = max(720, int(_pw * 0.82))
        _wh = max(440, int(_ph * 0.75))
        _wx = max(4, min(_px + (_pw - _ww) // 2, _sx - _ww - 4))
        _wy = max(4, min(_py + (_ph - _wh) // 2, _sy - _wh - 4))
        win.geometry(f"{_ww}x{_wh}+{_wx}+{_wy}")
        def _hist_close(_e=None):
            self._history_open = False
            try:
                win.grab_release()
                win.destroy()
            except tk.TclError:
                pass  # already destroyed (rapid double-click)
        self._make_close_x(hdr, _hist_close, _sec, _dim, _fg)
        tk.Frame(outer, bg=_brd, height=1, bd=0).pack(fill="x")
        win.bind("<Escape>", lambda _e: _hist_close())
        # WM_DELETE_WINDOW not applicable with overrideredirect=True
        self._apply_titlebar_theme(win)
        win.deiconify()
        win.wait_window()
        self._history_open = False

    # ── Retry Failed ──────────────────────────────────────────────────────────
    def _retry_failed(self):
        """Re-run only the components that failed in the previous run."""
        failed = list(self.engine._last_failed)
        if not failed:
            self._msgbox("info", "Retry Failed",
                         "No failed components from the last run.")
            return
        # Temporarily override the component checkboxes to match failed set.
        _prev = {name: var.get() for name, var in self.comp_vars.items()}
        for name, var in self.comp_vars.items():
            var.set(name in failed)
        self.start_updates()
        # Restore previous selections if start_updates returned early (validation).
        if not self._running:
            for name, val in _prev.items():
                self.comp_vars[name].set(val)

    # ── Reboot Banner ─────────────────────────────────────────────────────────
    def _show_reboot_banner(self):
        """Display a persistent banner below the progress bar when a reboot is needed."""
        if self._reboot_banner is not None:
            return  # already visible
        banner = tk.Frame(self.root, bg="#b35c00", bd=0)
        banner.pack(fill="x", padx=12, pady=(0, 2), before=self._border_health)
        tk.Label(banner, text="⚠  A system restart is required to finish applying updates.",
                 bg="#b35c00", fg="#ffffff",
                 font=("Segoe UI", 9, "bold"), padx=8, pady=4).pack(side="left")
        tk.Button(banner, text="✕", command=self._hide_reboot_banner,
                  bg="#b35c00", fg="#ffffff", relief="flat", borderwidth=0,
                  font=("Segoe UI", 9, "bold"), padx=6, pady=2,
                  cursor="hand2").pack(side="right", padx=4)
        # Register in _section_border_seps so _recolour skips the banner
        # on theme switches, preserving its fixed amber styling.
        self._section_border_seps.append(banner)
        self._skip_cache = None   # force _skip_cache rebuild on next _apply_theme
        self._reboot_banner = banner

    def _hide_reboot_banner(self):
        """Remove the reboot-required banner if visible."""
        if self._reboot_banner is not None:
            try:
                self._reboot_banner.destroy()
            except tk.TclError:
                pass
            self._reboot_banner = None

    # ── Dry-Run Summary ───────────────────────────────────────────────────────
    def _show_dry_run_summary(self):
        """Parse the log to build a concise summary of what a live run would do."""
        text = self.log_widget.get("1.0", "end-1c")
        # Tally "Would upgrade: NAME" lines per component section.
        totals: dict = {}
        current_section = None
        _text_lines = text.splitlines()   # split once; reused for fallback
        for line in _text_lines:
            if line.startswith("-- ") and len(line) > 6 and "---" in line:
                # Strip leading "-- " and trailing " ---..." to get the component name.
                current_section = line[3:].rstrip("- ").strip()
            if current_section and ("[DRY RUN]" in line and ("Would upgrade" in line
                    or "Would execute" in line or "Would scan" in line)):
                totals[current_section] = totals.get(current_section, 0) + 1
        if not totals:
            # Generic summary: just count DRY RUN lines.
            dry_lines = sum(1 for l in _text_lines if "[DRY RUN]" in l)
            summary = f"{dry_lines} dry-run action(s) logged. No live changes were made."
        else:
            lines_out = [f"  • {sec}: {n} action(s)" for sec, n in totals.items()]
            summary = "Dry-run complete — no changes were made.\n\n" + "\n".join(lines_out)
        self._msgbox("info", "Dry-Run Summary", summary)

    # ── Log Search ────────────────────────────────────────────────────────────
    def _on_log_search(self, *_):
        """Highlight / filter log lines matching the search term."""
        if self._log_search_var is None:
            return
        # Guard: not yet initialised.
        if not hasattr(self, "log_widget"):
            return
        # StringVar only holds real user input — never the placeholder text.
        if self._search_ph_active[0]:
            return  # placeholder visible, nothing real to search
        term = self._log_search_var.get().lower()
        lw = self.log_widget
        if self._search_hl_active and self._log_line_count > 0:
            lw.tag_remove("search_hl", "1.0", "end")
            self._search_hl_active = False
        if not term:
            if self._search_count_var is not None:
                self._search_count_var.set("")
            return
        # Highlight all matching lines (tag colours configured in _apply_theme).
        # Bind hot-path methods and term length once — saves LOAD_ATTR + len()
        # per match when the log contains many hits (e.g. searching "warn").
        _lw_search  = lw.search
        _lw_tag_add = lw.tag_add
        _term_len   = len(term)
        _first  = None
        _n_hits = 0
        _capped = False
        idx = "1.0"
        while _n_hits < _MAX_SEARCH_MATCHES:
            idx = _lw_search(term, idx, nocase=True, stopindex="end")
            if not idx:
                break
            if _first is None:
                _first = idx            # capture first match
                self._search_hl_active = True  # set once; not every iteration
            end_idx = f"{idx}+{_term_len}c"
            _lw_tag_add("search_hl", idx, end_idx)
            idx = end_idx
            _n_hits += 1
        else:
            _capped = True   # hit the cap before all matches found
        if self._search_count_var is not None:
            # Use _n_hits counter from the loop — avoids lw.tag_ranges() Tcl call.
            _s = "matches" if _n_hits != 1 else "match"
            _cap_sfx = "+ (limit)" if _capped else ""
            self._search_count_var.set(
                f"{_n_hits}{_cap_sfx} {_s}" if _n_hits else "")
        if _first:
            lw.see(_first)

    # ── Estimated Duration ────────────────────────────────────────────────────
    def _update_est_duration(self):
        """Read run history to estimate the next run duration and update the label."""
        if self._est_dur_var is None:
            return
        _edv = self._est_dur_var   # hoist: 4 LOAD_ATTR → LOAD_FAST
        try:
            with open(HIST_FILE, "r", encoding="utf-8") as f:
                history = json.load(f)
            if not isinstance(history, list) or not history:
                _edv.set("")
                return
            # Take the mean of the last 5 live (non-dry-run) runs.
            live = [r for r in history if not r.get("dry_run") and r.get("elapsed_s", 0) > 0]
            if not live:
                _edv.set("")
                return
            recent = live[-5:]
            def _safe_e(r):
                try: return min(float(r["elapsed_s"]), 3600.0)
                except (TypeError, ValueError, KeyError): return 0.0
            avg_s = sum(_safe_e(r) for r in recent) / len(recent)
            # Compact format for the toolbar: "· ~2 m" instead of the
            # full "· Est. 2 m 14 s" to keep the status row readable.
            _mins = int(avg_s // 60)
            _secs = int(avg_s % 60)
            if _mins == 0:
                _est_str = f"~{_secs} s"
            elif _secs < 30:
                _est_str = f"~{_mins} m"
            else:
                _est_str = f"~{_mins + 1} m"
            _edv.set(f"· {_est_str}")
        except (OSError, json.JSONDecodeError, KeyError):
            _edv.set("")

    # ── Open Log ──────────────────────────────────────────────────────────────
    def open_log(self):
        """Open the current log file in the system default application."""
        if os.path.exists(LOG_FILE):
            try:
                os.startfile(LOG_FILE)
            except Exception as e:
                self._msgbox("error", "Error", f"Could not open log file: {e}")
        else:
            self._msgbox("error", "Error", "Log file not found.")

#==================== MAIN =====================
_SW_HIDE = 0
_SW_SHOW = 5


def _set_console_visible(visible: bool) -> None:
    """Show or hide the Windows console window attached to this process."""
    if platform.system() != "Windows":
        return
    try:
        hwnd = ctypes.windll.kernel32.GetConsoleWindow()
        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd,
                                            _SW_SHOW if visible else _SW_HIDE)
    except Exception:
        pass


def main():
    """Application entry point — checks platform, attaches log handler, and starts the GUI."""
    if platform.system() != "Windows":
        print("This tool only runs on Windows.")
        sys.exit(1)
    if not logger.handlers:
        _fh = RotatingFileHandler(LOG_FILE, maxBytes=5_000_000, backupCount=3, encoding="utf-8")
        _fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
        logger.addHandler(_fh)
    if not is_admin():
        elevate()
    config, config_load_error = load_config()
    # Hide the console window unless debug mode is enabled.
    _set_console_visible(bool(config.get("debug_mode", False)))
    engine = UpdateEngine(config)
    # Enable per-monitor DPI awareness so tkinter receives real pixel
    # coordinates on high-DPI displays instead of virtualised 96-dpi coords.
    # Must be called before tk.Tk() is created.
    if platform.system() == "Windows":
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(2)   # Per-Monitor V2
        except (AttributeError, OSError):
            try:
                ctypes.windll.user32.SetProcessDPIAware()    # legacy fallback
            except (AttributeError, OSError):
                pass
    root   = tk.Tk()
    root.withdraw()          # Hide until fully initialised — prevents empty-window flash.
    gui    = UpdaterGUI(root, engine)
    if config_load_error:
        gui.queue.put((
            "error",
            f"Config file could not be parsed - defaults were used.\n\nDetails: {config_load_error}"
        ))
    root.mainloop()


if __name__ == "__main__":
    main()
