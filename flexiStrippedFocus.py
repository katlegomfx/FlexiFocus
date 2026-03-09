import urllib.request
import urllib.parse
import urllib.error
import signal
import time
import sys
import platform
from datetime import datetime, timedelta
import json
import os
import io
import re
import subprocess
import traceback
import uuid
import queue
from enum import Enum, IntEnum
import shutil
import gzip
import pickle
import py_compile
import difflib
import threading
import functools
import random
import ast
import copy
import base64
import hashlib
import builtins
import sqlite3
import importlib
import importlib.util
import tokenize
import html
from dataclasses import dataclass
from html.parser import HTMLParser
try:
    import readline
    HISTORY_SUPPORT = True
except ImportError:
    try:
        import pyreadline3 as readline
        HISTORY_SUPPORT = True
    except ImportError:
        HISTORY_SUPPORT = False

from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, TimeoutError
from typing import List, Dict, Any, Optional, Callable
from contextlib import redirect_stderr, redirect_stdout

class RestartPolicy(str, Enum):
    NEVER = "never"
    ON_FAILURE = "on_failure"
    ALWAYS = "always"

# --- QA / EVOLUTION CONSTANTS ---
# --- CONFIGURATION ---
# Allow running multiple agent instances by pointing to a custom state dir via env var
# Example: FLEXI_STATE_DIR=.flexi_cli python flexi.py
STATE_DIR = Path(os.environ.get("FLEXI_STATE_DIR", ".flexi/rlm_state"))

# Skills layout should be a sibling of the logical agent root when using the default
# `.flexi/rlm_state` layout, otherwise place skills under the custom state dir.
if STATE_DIR.name == "rlm_state":
    SKILLS_DIR = STATE_DIR.parent / "skills"
else:
    SKILLS_DIR = STATE_DIR / "skills"

STATE_FILE = STATE_DIR / "state.json"
GLOBALS_FILE = STATE_DIR / "globals.pkl"
SNAPSHOT_DIR = STATE_DIR / "snapshots"
BG_TASK_LOG_DIR = STATE_DIR / "bg_task_logs"
DB_PROFILES_FILE = STATE_DIR / "db_profiles.json"
NOTEBOOK_SESSION_FILE = STATE_DIR / "notebook_sessions.json"
ARCHIVE_FILE = STATE_DIR / "full_archive.jsonl"
RESPONSE_TRACE_FILE = STATE_DIR / "response_trace.jsonl"
# maximum size (bytes) before rotating/compressing the legacy JSONL archive
ARCHIVE_MAX_BYTES = 5 * 1024 * 1024  # 5 MiB by default

EVOLUTION_LOG = STATE_DIR / "evolution_log.md"
MAX_SNAPSHOTS = 5
TOKEN_THRESHOLD = 92000 # Your specific requirement for summary trigger

# automatic history summarisation parameters
AUTO_SUMMARY_THRESHOLD = 2000  # if history entries exceed this
AUTO_SUMMARY_KEEP = 500        # keep this many recent entries intact

# Place config next to the logical agent root for discoverability
CONFIG_FILE = (STATE_DIR.parent / "config.json") if STATE_DIR.name == "rlm_state" else (STATE_DIR / "config.json")

TOKEN_CACHE_FILE = "github_token_cache.json"
COPILOT_TOKEN_URL = "https://api.github.com/copilot_internal/v2/token"
DEFAULT_COPILOT_API_BASE_URL = "https://api.individual.githubcopilot.com"

COMMON_HEADERS = {
    "Editor-Version": "vscode/1.85.1",
    "Editor-Plugin-Version": "copilot/1.138.0",
    "User-Agent": "GithubCopilot/1.138.0",
    "Accept": "application/json",
}

RUNTIME_FLAGS = {
    "debug_startup": False,
    "no_dependency_check": False,
}

STARTUP_LOG_FILE = Path("startup.log")

def load_runtime_config() -> dict:
    if CONFIG_FILE.exists():
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def resolve_runtime_flags(argv: list[str] | None = None) -> dict:
    argv = argv if argv is not None else sys.argv[1:]
    config = load_runtime_config()
    debug_startup = bool(config.get("debug_startup", False)) or ("--debug-startup" in argv)
    no_dependency_check = bool(config.get("no_dependency_check", False)) or bool(config.get("dependency_check_disabled", False)) or ("--no-dependency-check" in argv)
    return {
        "debug_startup": debug_startup,
        "no_dependency_check": no_dependency_check,
    }

class StartupTracer:
    """Dedicated startup/debug tracer for boot diagnostics."""

    @staticmethod
    def configure(*, enabled: bool):
        RUNTIME_FLAGS["debug_startup"] = bool(enabled)
        if not enabled:
            return
        try:
            STARTUP_LOG_FILE.write_text("", encoding="utf-8")
        except Exception:
            pass

    @staticmethod
    def enabled() -> bool:
        return bool(RUNTIME_FLAGS.get("debug_startup", False))

    @staticmethod
    def log(message: str, category: str = "STARTUP"):
        if not StartupTracer.enabled():
            return
        stamp = datetime.now().isoformat()
        line = f"{stamp} {category}: {message}"
        try:
            with open(STARTUP_LOG_FILE, "a", encoding="utf-8") as f:
                f.write(line + "\n")
        except Exception:
            pass
        ConsoleOutput.debug(line)

# --- SKILL PLUGIN FRAMEWORK ---

# global registry of skill classes, keyed by name
skill_registry: dict[str, type] = {}

@dataclass
class SkillMetadata:
    name: str
    description: str = ""
    version: str = "0.1.0"
    author: str = ""
    capabilities: list[str] | None = None
    priority: int = 100

@dataclass
class SkillLifecycleContext:
    bot: 'FlexiBot'
    skill_name: str
    metadata: SkillMetadata
    config: dict[str, Any]

@dataclass
class ToolHookContext:
    bot: 'FlexiBot'
    stage: str
    tool_name: str
    payload: str
    skill_name: str = ""
    result: Optional[str] = None

@dataclass
class PromptTemplateSpec:
    name: str
    template: Any
    source_skill: str

def register_skill(name: str, **metadata_kwargs):
    """Decorator for registering a `BaseSkill` subclass under a given name."""
    def deco(cls):
        cls.__skill_registration__ = SkillMetadata(
            name=name,
            description=metadata_kwargs.get("description", getattr(cls, "description", "")),
            version=metadata_kwargs.get("version", getattr(cls, "version", "0.1.0")),
            author=metadata_kwargs.get("author", getattr(cls, "author", "")),
            capabilities=list(metadata_kwargs.get("capabilities", getattr(cls, "capabilities", [])) or []),
            priority=int(metadata_kwargs.get("priority", getattr(cls, "priority", 100))),
        )
        skill_registry[name] = cls
        return cls
    return deco

class BaseSkill:
    """Base class for user-defined skills.

    Skills may declare dependencies via the `dependencies()` classmethod, and
    may provide configuration or prompt templates by overriding methods.
    The agent will instantiate each skill once at startup and may call
    `pre_tool`/`post_tool` hooks during execution.
    """
    def __init__(self, bot: 'FlexiBot'):
        self.bot = bot
        self.skill_config = self._load_validated_config()

    @classmethod
    def metadata(cls) -> SkillMetadata:
        reg = getattr(cls, "__skill_registration__", None)
        if isinstance(reg, SkillMetadata):
            return reg
        return SkillMetadata(
            name=getattr(cls, "name", cls.__name__.lower()),
            description=getattr(cls, "description", ""),
            version=getattr(cls, "version", "0.1.0"),
            author=getattr(cls, "author", ""),
            capabilities=list(getattr(cls, "capabilities", []) or []),
            priority=int(getattr(cls, "priority", 100)),
        )

    @classmethod
    def dependencies(cls) -> list[str]:
        return []

    @classmethod
    def capabilities(cls) -> list[str]:
        return list(cls.metadata().capabilities or [])

    @classmethod
    def config_schema(cls) -> dict[str, Any]:
        return {}

    @classmethod
    def config(cls) -> dict:
        return {}

    def prompt_templates(self) -> dict:
        return {}

    def prompt_injectors(self) -> dict[str, Any]:
        return {}

    def tool_wrappers(self) -> dict[str, Callable[[str, Callable[[str], str]], str]]:
        return {}

    def on_load(self, context: SkillLifecycleContext):
        """Called after the skill has been instantiated and registered."""

    def on_unload(self, context: SkillLifecycleContext):
        """Called before the runtime shuts down."""

    def on_pre_tool(self, context: ToolHookContext):
        """Typed pre-tool hook."""

    def on_post_tool(self, context: ToolHookContext):
        """Typed post-tool hook."""

    def pre_tool(self, tool_name: str, payload: str):
        """Legacy pre-tool hook for backwards compatibility."""

    def post_tool(self, tool_name: str, result: str):
        """Legacy post-tool hook for backwards compatibility."""

    @classmethod
    def _runtime_skill_config(cls) -> dict[str, Any]:
        config = load_runtime_config()
        skills_cfg = config.get("skills", {}) if isinstance(config, dict) else {}
        skill_name = cls.metadata().name
        value = skills_cfg.get(skill_name, {})
        return value if isinstance(value, dict) else {}

    @classmethod
    def _validate_config_schema(cls, cfg: dict[str, Any]) -> dict[str, Any]:
        schema = cls.config_schema() or {}
        if not isinstance(schema, dict):
            raise TypeError(f"Skill '{cls.metadata().name}' config_schema() must return a dict")
        validated = dict(cfg or {})
        for key, rule in schema.items():
            expected_type = None
            required = False
            default = None
            if isinstance(rule, type):
                expected_type = rule
            elif isinstance(rule, dict):
                expected_type = rule.get("type")
                required = bool(rule.get("required", False))
                default = rule.get("default")
            else:
                raise TypeError(f"Skill '{cls.metadata().name}' schema for '{key}' must be a type or dict")

            if key not in validated and default is not None:
                validated[key] = default

            if required and key not in validated:
                raise ValueError(f"Skill '{cls.metadata().name}' missing required config key '{key}'")

            if key in validated and expected_type is not None and validated[key] is not None and not isinstance(validated[key], expected_type):
                raise TypeError(
                    f"Skill '{cls.metadata().name}' config key '{key}' expected {expected_type.__name__}, got {type(validated[key]).__name__}"
                )
        return validated

    def _load_validated_config(self) -> dict[str, Any]:
        base = self.__class__.config() or {}
        if not isinstance(base, dict):
            raise TypeError(f"Skill '{self.metadata().name}' config() must return a dict")
        merged = {**base, **self.__class__._runtime_skill_config()}
        return self.__class__._validate_config_schema(merged)

# --- WINDOWS AUTOMATION HELPERS ---
class SystemAutomation:
    """Encapsulates cross-platform automation logic (Window listing, Capturing)."""

    DEPENDENCY_MATRIX = [
        {
            "id": "pywin32",
            "platforms": {"windows"},
            "module": "win32gui",
            "install": "pip install pywin32",
            "capabilities": ["window-listing", "window-capture"],
            "message": "pywin32 is required for native Windows window automation.",
        },
        {
            "id": "psutil",
            "platforms": {"windows", "linux", "darwin"},
            "module": "psutil",
            "install": "pip install psutil",
            "capabilities": ["process-inspection", "window-listing"],
            "message": "psutil improves process and window inspection features.",
        },
        {
            "id": "quartz",
            "platforms": {"darwin"},
            "module": "Quartz",
            "install": "pip install pyobjc-framework-Quartz",
            "capabilities": ["window-listing"],
            "message": "Quartz bindings are required for native macOS window inspection.",
        },
        {
            "id": "pillow",
            "platforms": {"windows", "linux", "darwin"},
            "module": "PIL",
            "install": "pip install Pillow",
            "capabilities": ["screen-capture", "window-capture"],
            "message": "Pillow is required for screenshot and capture helpers.",
        },
    ]

    @staticmethod
    def _platform_tag() -> str:
        if os.name == 'nt':
            return "windows"
        if sys.platform == 'darwin':
            return "darwin"
        return "linux"

    @staticmethod
    def dependency_check_enabled() -> bool:
        return not bool(RUNTIME_FLAGS.get("no_dependency_check", False))

    @staticmethod
    def get_dependency_warnings() -> list[dict[str, Any]]:
        if not SystemAutomation.dependency_check_enabled():
            StartupTracer.log("dependency checks disabled by runtime flag/config", "DEPCHK")
            return []

        platform_tag = SystemAutomation._platform_tag()
        warnings: list[dict[str, Any]] = []

        for spec in SystemAutomation.DEPENDENCY_MATRIX:
            if platform_tag not in spec.get("platforms", set()):
                continue

            module_name = spec.get("module", "")
            StartupTracer.log(f"checking dependency spec '{spec.get('id')}' via find_spec('{module_name}')", "DEPCHK")
            found = importlib.util.find_spec(module_name) is not None
            if found:
                StartupTracer.log(f"dependency '{spec.get('id')}' available", "DEPCHK")
                continue

            warning = {
                "kind": "missing_dependency",
                "dependency": spec.get("id"),
                "module": module_name,
                "platform": platform_tag,
                "install": spec.get("install", ""),
                "capabilities": list(spec.get("capabilities", []) or []),
                "message": spec.get("message", "Dependency missing."),
            }
            warnings.append(warning)
            StartupTracer.log(f"dependency '{spec.get('id')}' missing", "DEPCHK")

        return warnings
    
    @staticmethod
    def check_dependencies(structured: bool = False):
        warnings = SystemAutomation.get_dependency_warnings()
        if structured:
            return warnings
        return [f"{item['dependency']} ({item['install']})" for item in warnings]

    @staticmethod
    def warn_if_missing():
        warnings = SystemAutomation.get_dependency_warnings()
        for item in warnings:
            ConsoleOutput.warning(json.dumps(item))

    @staticmethod
    def get_open_windows(filter_text: str = None) -> List[Dict[str, Any]]:
        system = platform.system()
        windows = []

        if system == 'Windows':
            try:
                import win32gui, win32process, psutil
                hwnds = []
                def enum_callback(hwnd, _):
                    try:
                        if win32gui.IsWindowVisible(hwnd):
                            hwnds.append(hwnd)
                    except: pass
                    return True
                win32gui.EnumWindows(enum_callback, None)

                for hwnd in hwnds:
                    try:
                        title = win32gui.GetWindowText(hwnd)
                        if not title: continue
                        
                        info = {"title": title, "hwnd": int(hwnd)}
                        try:
                            _, pid = win32process.GetWindowThreadProcessId(hwnd)
                            info["process_id"] = int(pid)
                            try:
                                proc = psutil.Process(pid)
                                info["process_name"] = proc.name()
                            except:
                                info["process_name"] = "Unknown"
                        except: pass
                        windows.append(info)
                    except: pass
            except Exception: pass

        elif system == 'Darwin':
            try:
                from Quartz import CGWindowListCopyWindowInfo, kCGWindowListOptionOnScreenOnly, kCGNullWindowID
                window_list = CGWindowListCopyWindowInfo(kCGWindowListOptionOnScreenOnly, kCGNullWindowID)
                for window in window_list:
                    title = window.get('kCGWindowName', '')
                    owner_name = window.get('kCGWindowOwnerName', '')
                    pid = window.get('kCGWindowOwnerPID', 0)
                    window_id = window.get('kCGWindowNumber', 0)
                    if title:
                        windows.append({
                            "title": title,
                            "process_name": owner_name,
                            "process_id": pid,
                            "hwnd": window_id
                        })
            except Exception: pass

        elif system == 'Linux':
            try:
                import subprocess
                result = subprocess.run(['wmctrl', '-l', '-p'], capture_output=True, text=True)
                if result.returncode == 0:
                    for line in result.stdout.strip().split('\n'):
                        parts = line.split(None, 4)
                        if len(parts) >= 5:
                            windows.append({
                                "title": parts[4],
                                "process_id": int(parts[2]),
                                "hwnd": int(parts[0], 16)
                            })
            except Exception: pass
        
        if filter_text:
            ft = filter_text.lower()
            windows = [w for w in windows if ft in w['title'].lower() or ft in w.get('process_name', '').lower()]
            
        return windows

    @staticmethod
    def find_consuming_port(port: int) -> str:
        """Finds which PID is holding a port and returns details."""
        try:
            if os.name == 'nt':
                # Use shell=True for pipe support in cmd
                cmd = f'netstat -ano | findstr :{port}'
                res = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                if not res.stdout.strip(): return f"No process found consuming port {port}"
                lines = res.stdout.strip().split('\n')
                pids = set()
                for line in lines:
                    parts = line.split()
                    if parts: pids.add(parts[-1])
                
                output = [f"Port {port} is held by PID(s): {', '.join(pids)}"]
                try:
                    import psutil
                    for pid in pids:
                        try:
                            p = psutil.Process(int(pid))
                            output.append(f" - PID {pid}: {p.name()} (Status: {p.status()})")
                        except: pass
                except ImportError: pass
                return "\n".join(output)
            else:
                # Unix/Mac
                cmd = f'lsof -i :{port} -t'
                res = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                if not res.stdout.strip(): return f"No process found consuming port {port}"
                pids = res.stdout.strip().split('\n')
                output = [f"Port {port} is held by PID(s): {', '.join(pids)}"]
                try:
                    import psutil
                    for pid in pids:
                        try:
                            p = psutil.Process(int(pid))
                            output.append(f" - PID {pid}: {p.name()} (Status: {p.status()})")
                        except: pass
                except ImportError: pass
                return "\n".join(output)
        except Exception as e: return f"Port check error: {e}"

    @staticmethod
    def capture_window(query: str = None, output_path: str = None, title_query: str = None, process_query: str = None) -> str:
        """Improved capture logic merged from capture_window.py."""
        if os.name != 'nt': return "Error: Native capture currently only supported on Windows."
        deps = SystemAutomation.check_dependencies()
        if deps: return f"Error: Missing dependencies: {', '.join(deps)}"

        try:
            import win32gui, win32con, win32process, psutil
            from PIL import ImageGrab
        except ImportError:
            return "Imports failed despite check."

        target_hwnd = None
        t_query = (title_query or query)
        p_query = (process_query or query)

        # 1. Find Window (or Full Screen if no query)
        if not t_query and not p_query:
            try:
                img = ImageGrab.grab(all_screens=True)
                path_obj = Path(output_path)
                path_obj.parent.mkdir(parents=True, exist_ok=True)
                img.save(str(path_obj))
                return "Success"
            except Exception as e:
                return f"Full Screen Capture Error: {e}"

        # Collect candidate windows safely
        candidates = []
        def enum_callback(hwnd, _):
            if win32gui.IsWindowVisible(hwnd):
                candidates.append(hwnd)

        win32gui.EnumWindows(enum_callback, None)

        # Search candidates
        for hwnd in candidates:
            title = win32gui.GetWindowText(hwnd)
            
            # Check Title
            if t_query and title and t_query.lower() in title.lower():
                target_hwnd = hwnd
                break
            
            # Check Process
            if p_query:
                try:
                    _, pid = win32process.GetWindowThreadProcessId(hwnd)
                    proc = psutil.Process(pid)
                    pname = proc.name()
                    if p_query.lower() in pname.lower():
                        target_hwnd = hwnd
                        break
                except: pass

        if not target_hwnd:
            return "Window not found."

        # 2. Capture
        try:
            # Restore if minimized
            if win32gui.IsIconic(target_hwnd):
                win32gui.ShowWindow(target_hwnd, win32con.SW_RESTORE)
                time.sleep(0.5)

            # Bring to front
            try:
                win32gui.SetForegroundWindow(target_hwnd)
                time.sleep(0.5)
            except Exception:
                # Sometimes SetForegroundWindow fails if called from a background process
                win32gui.ShowWindow(target_hwnd, win32con.SW_RESTORE)
                time.sleep(0.5)
            
            # Handle possible coordinate issues for minimized/offscreen
            rect = win32gui.GetWindowRect(target_hwnd)
            if rect[0] <= -30000 and rect[1] <= -30000:
                win32gui.ShowWindow(target_hwnd, win32con.SW_RESTORE)
                win32gui.SetForegroundWindow(target_hwnd)
                time.sleep(0.7)
                rect = win32gui.GetWindowRect(target_hwnd)

            img = ImageGrab.grab(bbox=rect, all_screens=True)
            
            # Ensure dir
            path_obj = Path(output_path)
            path_obj.parent.mkdir(parents=True, exist_ok=True)
            img.save(str(path_obj))
            return "Success"
        except Exception as e:
            return f"Capture Error: {e}"

# --- UI HELPERS ---
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'
    DIM = '\033[90m' # Changed from [2m to [90m (Dark Gray) for better Windows compatibility

    @staticmethod
    def fix_windows_console():
        """Enables VT100 support for Windows terminals (colors)."""
        if os.name == 'nt':
            # Check if running in a terminal that likely already supports ANSI (e.g. Git Bash/Mintty)
            if os.environ.get('TERM'): return

            # Otherwise, enable VT processing for CMD/PowerShell
            try:
                from ctypes import windll, c_int, byref
                stdout_handle = windll.kernel32.GetStdHandle(c_int(-11))
                mode = c_int(0)
                if windll.kernel32.GetConsoleMode(stdout_handle, byref(mode)):
                    mode.value |= 0x0004 # ENABLE_VIRTUAL_TERMINAL_PROCESSING
                    windll.kernel32.SetConsoleMode(stdout_handle, mode)
            except Exception:
                pass


    @staticmethod
    def print_logo():
        # Attempt to render a fancy Unicode logo.  Some consoles (and
        # redirected output) use encodings that can't handle the block
        # characters; print() will raise UnicodeEncodeError in that case.
        logo = f"""[96m[1m
    ███████╗██╗     ███████╗██╗  ██╗██╗
    ██╔════╝██║     ██╔════╝╚██╗██╔╝██║
    █████╗  ██║     █████╗   ╚███╔╝ ██║
    ██╔══╝  ██║     ██╔══╝   ██╔██╗ ██║
    ██║     ███████╗███████╗██╔╝ ██╗██║
    ╚═╝     ╚══════╝╚══════╝╚═╝  ╚═╝╚═╝
        [90mFlexible Copilot Agent v4.2[0m
        """
        try:
            print(logo)
        except UnicodeEncodeError:
            # fallback to simple text without blocks or colors
            try:
                print("Flexible Copilot Agent v4.2")
            except Exception:
                pass
    # --- TOKEN TRACKING HELPER ---
    def estimate_tokens(text: str) -> int:
        """Heuristic for token estimation (roughly 4 chars per token)."""
        return len(text) // 4

    # --- ERROR HANDLING FRAMEWORK ---
class ErrorSeverity(Enum):
    RECOVERABLE = "RECOVERABLE"
    CRITICAL = "CRITICAL"
    FATAL = "FATAL"

class ErrorCode(Enum):
    SYS_GENERIC = "SYS_000"
    NET_ERROR = "NET_001"
    IO_ERROR = "IO_001"
    EXEC_ERROR = "EXEC_001"
    AGENT_ERROR = "AGT_001"

class ConsoleOutput:
    """Small CLI output facade with conceptual channels."""

    DEBUG_ENV_VARS = ("FLEXI_DEBUG", "FLEXI_DEBUG_OUTPUT")

    @staticmethod
    def debug_enabled() -> bool:
        if RUNTIME_FLAGS.get("debug_startup", False):
            return True
        for name in ConsoleOutput.DEBUG_ENV_VARS:
            value = os.environ.get(name, "")
            if value.lower() in {"1", "true", "yes", "on", "debug"}:
                return True
        return False

    @staticmethod
    def _emit(message: str = "", *, color: str = "", prefix: str = "", end: str = "\n", flush: bool = False):
        text = f"{prefix}{message}"
        if color:
            builtins.print(f"{color}{text}{Colors.ENDC}", end=end, flush=flush)
        else:
            builtins.print(text, end=end, flush=flush)

    @staticmethod
    def system(message: str, *, end: str = "\n", flush: bool = False):
        ConsoleOutput._emit(message, color=Colors.DIM, prefix="[System] ", end=end, flush=flush)

    @staticmethod
    def warning(message: str, *, end: str = "\n", flush: bool = False):
        ConsoleOutput._emit(message, color=Colors.YELLOW, prefix="[Warning] ", end=end, flush=flush)

    @staticmethod
    def error(message: str, *, end: str = "\n", flush: bool = False):
        ConsoleOutput._emit(message, color=Colors.RED, prefix="[Error] ", end=end, flush=flush)

    @staticmethod
    def debug(message: str, *, end: str = "\n", flush: bool = False):
        if ConsoleOutput.debug_enabled():
            ConsoleOutput._emit(message, color=Colors.BLUE, prefix="[Debug] ", end=end, flush=flush)

    @staticmethod
    def prompt():
        ConsoleOutput._emit("👤 You: ", color=Colors.GREEN + Colors.BOLD, end="", flush=True)

    @staticmethod
    def user_output(message: str, *, end: str = "\n", flush: bool = False):
        ConsoleOutput._emit(message, end=end, flush=flush)

class ErrorHandler:
    ERROR_LOG = STATE_DIR / "error_log.jsonl"
    ERROR_LOG_MAX_BYTES = 2 * 1024 * 1024  # rotate at 2MiB by default
    _error_counts: dict = {}
    
    @staticmethod
    def register_global_handler():
        """Registers system-wide exception hooks."""
        def global_excepthook(exc_type, exc_value, exc_traceback):
            if issubclass(exc_type, KeyboardInterrupt):
                sys.__excepthook__(exc_type, exc_value, exc_traceback)
                return
            ErrorHandler.log(exc_value, ErrorSeverity.FATAL, "Uncaught Exception", ErrorCode.SYS_GENERIC)
        sys.excepthook = global_excepthook
    
    @staticmethod
    def log(error: Exception, severity: ErrorSeverity = ErrorSeverity.RECOVERABLE, context: str = "", code: ErrorCode = ErrorCode.SYS_GENERIC):
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        entry = {
            "timestamp": timestamp,
            "severity": severity.value,
            "code": code.value,
            "error_type": type(error).__name__,
            "message": str(error),
            "context": context,
            "traceback": traceback.format_exc()
        }
        
        # Console output
        color_map = {
            ErrorSeverity.RECOVERABLE: Colors.YELLOW,
            ErrorSeverity.CRITICAL: Colors.RED,
            ErrorSeverity.FATAL: Colors.RED + Colors.BOLD
        }
        color = color_map.get(severity, Colors.RED)

        ConsoleOutput._emit(f"[{severity.value} | {code.value}] {context}: {str(error)}", color=color)
        
        # File logging
        try:
            ErrorHandler.ERROR_LOG.parent.mkdir(parents=True, exist_ok=True)
            with open(ErrorHandler.ERROR_LOG, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry) + "\n")
        except Exception: pass
        
        # rotate error log if needed
        try:
            if ErrorHandler.ERROR_LOG.exists() and ErrorHandler.ERROR_LOG.stat().st_size > ErrorHandler.ERROR_LOG_MAX_BYTES:
                ts = time.strftime("%Y%m%d_%H%M%S")
                dest = ErrorHandler.ERROR_LOG.with_name(f"{ErrorHandler.ERROR_LOG.name}.{ts}.gz")
                with open(ErrorHandler.ERROR_LOG, "rb") as fin, gzip.open(dest, "wb") as fout:
                    shutil.copyfileobj(fin, fout)
                ErrorHandler.ERROR_LOG.unlink()
                ConsoleOutput.system(f"Error log rotated to {dest.name}")
        except Exception:
            pass
        
        # also append a brief alert to the evolution log for visibility
        try:
            alert = f"\n**Error Alert:** [{severity.value} {code.value}] {context}: {str(error)}\n"
            with open(EVOLUTION_LOG, "a", encoding="utf-8") as lf:
                lf.write(alert)
        except Exception:
            pass
        
        # track repeated errors
        key = (code.value, type(error).__name__)
        cnt = ErrorHandler._error_counts.get(key, 0) + 1
        ErrorHandler._error_counts[key] = cnt
        if cnt > 5:
            ConsoleOutput.warning(f"{cnt} occurrences of {key} have been logged.")

    @staticmethod
    def handle(func=None, *, severity=ErrorSeverity.RECOVERABLE, code=ErrorCode.SYS_GENERIC):
        """Decorator to wrap functions with centralized error handling."""
        def decorator(f):
            @functools.wraps(f)
            def wrapper(*args, **kwargs):
                try:
                    return f(*args, **kwargs)
                except Exception as e:
                    ErrorHandler.log(e, severity=severity, context=f"Function {f.__name__}", code=code)
                    return f"Error in {f.__name__} [{code.value}]: {str(e)}"
            return wrapper
        
        if func is None: return decorator
        return decorator(func)

def retry_with_backoff(retries=3, backoff_in_seconds=1):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            x = 0
            while True:
                try:
                    return func(*args, **kwargs)
                except Exception as e:
                    if x == retries:
                        ErrorHandler.log(e, ErrorSeverity.CRITICAL, f"Retry exhaust in {func.__name__}", ErrorCode.NET_ERROR)
                        raise
                    sleep = (backoff_in_seconds * 2 ** x + random.uniform(0, 1))
                    print(f"{Colors.YELLOW}Retrying {func.__name__} in {sleep:.1f}s... ({str(e)}){Colors.ENDC}")
                    time.sleep(sleep)
                    x += 1
        return wrapper
    return decorator


@dataclass
class ExecutionPolicyDecision:
    tool_name: str
    allowed: bool
    reason: str
    timeout_seconds: int
    resource_ceilings: dict[str, Any]
    environment: dict[str, str]
    isolation_rules: dict[str, Any]
    audit_format: dict[str, Any]


class ExecutionPolicyLayer:
    """Central policy layer for tool execution behavior."""

    DEFAULT_ALLOWED_TOOLS = {
        "bash": True,
        "python": True,
        "spawn_background": True,
        "run_python_bg": True,
        "install_python_package": True,
    }
    DEFAULT_TIMEOUTS = {
        "bash": 45,
        "python": 60,
        "spawn_background": 30,
        "run_python_bg": 30,
        "install_python_package": 120,
    }
    DEFAULT_TIMEOUT_OVERRIDES = {
        "bash": 120,
        "python": 180,
        "spawn_background": 300,
        "run_python_bg": 300,
        "install_python_package": 600,
    }
    DEFAULT_RESOURCE_CEILINGS = {
        "default": {
            "max_output_chars": 12000,
            "max_background_processes": 8,
        },
        "bash": {
            "max_input_chars": 4000,
        },
        "python": {
            "max_input_chars": 12000,
            "max_globals": 256,
        },
        "spawn_background": {
            "max_input_chars": 4000,
        },
        "run_python_bg": {
            "max_input_chars": 12000,
        },
        "install_python_package": {
            "max_input_chars": 200,
        },
    }
    DEFAULT_ENVIRONMENT_ISOLATION = {
        "inherit_environment": False,
        "allowed_vars": [
            "PATH", "PATHEXT", "SystemRoot", "COMSPEC", "WINDIR",
            "TEMP", "TMP", "HOME", "USERPROFILE", "USERNAME",
            "APPDATA", "LOCALAPPDATA", "PROGRAMFILES", "PROGRAMFILES(X86)",
            "TERM", "SHELL",
        ],
        "blocked_vars": ["PYTHONPATH", "VIRTUAL_ENV", "CONDA_PREFIX", "PYTHONHOME"],
        "set_vars": {
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONUNBUFFERED": "1",
        },
        "working_directory": ".",
        "readable_roots": ["."],
        "writable_roots": ["."],
        "network_access": "inherit",
        "blocked_command_patterns": [],
        "tool_overrides": {},
    }
    DEFAULT_AUDIT_LOGGING = {
        "format": "jsonl",
        "version": "execution_audit.v1",
        "path": "execution_audit.jsonl",
        "fields": [
            "timestamp", "tool_name", "action", "status", "reason",
            "timeout_seconds", "duration_ms", "resource_ceilings",
            "isolation", "payload_preview", "result_preview",
        ],
    }

    def __init__(self, config: dict[str, Any] | None = None):
        cfg = config if config is not None else load_runtime_config()
        policy_cfg = cfg.get("execution_policy", {}) if isinstance(cfg, dict) else {}
        allowed_tools = policy_cfg.get("allowed_tools", self.DEFAULT_ALLOWED_TOOLS)
        if isinstance(allowed_tools, list):
            allowed_tools = {name: True for name in allowed_tools}
        self.allowed_tools = {**self.DEFAULT_ALLOWED_TOOLS, **dict(allowed_tools or {})}
        self.timeout_defaults = {**self.DEFAULT_TIMEOUTS, **dict(policy_cfg.get("timeout_defaults", {}) or {})}
        self.timeout_overrides = {**self.DEFAULT_TIMEOUT_OVERRIDES, **dict(policy_cfg.get("timeout_overrides", {}) or {})}
        self.resource_ceilings = copy.deepcopy(self.DEFAULT_RESOURCE_CEILINGS)
        for key, value in dict(policy_cfg.get("resource_ceilings", {}) or {}).items():
            if isinstance(value, dict) and isinstance(self.resource_ceilings.get(key), dict):
                self.resource_ceilings[key].update(value)
            else:
                self.resource_ceilings[key] = value
        self.environment_isolation = copy.deepcopy(self.DEFAULT_ENVIRONMENT_ISOLATION)
        self.environment_isolation.update(dict(policy_cfg.get("environment_isolation", {}) or {}))
        self.audit_logging = copy.deepcopy(self.DEFAULT_AUDIT_LOGGING)
        self.audit_logging.update(dict(policy_cfg.get("audit_logging", {}) or {}))
        self.audit_log_path = STATE_DIR / self.audit_logging.get("path", "execution_audit.jsonl")

    def describe(self) -> dict[str, Any]:
        return {
            "allowed_tools": copy.deepcopy(self.allowed_tools),
            "timeout_defaults": copy.deepcopy(self.timeout_defaults),
            "timeout_overrides": copy.deepcopy(self.timeout_overrides),
            "resource_ceilings": copy.deepcopy(self.resource_ceilings),
            "environment_isolation": copy.deepcopy(self.environment_isolation),
            "audit_logging": copy.deepcopy(self.audit_logging),
        }

    def _tool_ceilings(self, tool_name: str) -> dict[str, Any]:
        combined = dict(self.resource_ceilings.get("default", {}))
        combined.update(dict(self.resource_ceilings.get(tool_name, {}) or {}))
        return combined

    def _build_environment(self, tool_name: str) -> tuple[dict[str, str], dict[str, Any]]:
        base_rules = copy.deepcopy(self.environment_isolation)
        tool_overrides = dict(base_rules.get("tool_overrides", {}) or {}).get(tool_name, {}) or {}
        rules = {
            "inherit_environment": tool_overrides.get("inherit_environment", base_rules.get("inherit_environment", False)),
            "allowed_vars": list(tool_overrides.get("allowed_vars", base_rules.get("allowed_vars", [])) or []),
            "blocked_vars": list(tool_overrides.get("blocked_vars", base_rules.get("blocked_vars", [])) or []),
            "set_vars": {**dict(base_rules.get("set_vars", {}) or {}), **dict(tool_overrides.get("set_vars", {}) or {})},
            "working_directory": str(tool_overrides.get("working_directory", base_rules.get("working_directory", ".")) or "."),
            "readable_roots": list(tool_overrides.get("readable_roots", base_rules.get("readable_roots", ["."])) or ["."]),
            "writable_roots": list(tool_overrides.get("writable_roots", base_rules.get("writable_roots", ["."])) or ["."]),
            "network_access": tool_overrides.get("network_access", base_rules.get("network_access", "inherit")),
            "blocked_command_patterns": list(tool_overrides.get("blocked_command_patterns", base_rules.get("blocked_command_patterns", [])) or []),
        }
        source_env = dict(os.environ) if rules["inherit_environment"] else {}
        if rules["allowed_vars"]:
            source_env = {k: v for k, v in os.environ.items() if k in set(rules["allowed_vars"])}
        for name in rules["blocked_vars"]:
            source_env.pop(name, None)
        source_env.update({str(k): str(v) for k, v in rules["set_vars"].items()})
        return source_env, rules

    def _payload_block_reason(self, tool_name: str, payload: str, rules: dict[str, Any]) -> str | None:
        text = str(payload or "")
        for pattern in rules.get("blocked_command_patterns", []):
            try:
                if re.search(pattern, text, re.IGNORECASE):
                    return f"Payload matches blocked execution policy pattern '{pattern}' for '{tool_name}'."
            except re.error:
                if pattern.lower() in text.lower():
                    return f"Payload matches blocked execution policy pattern '{pattern}' for '{tool_name}'."
        return None

    def subprocess_kwargs(self, decision: ExecutionPolicyDecision) -> dict[str, Any]:
        cwd = decision.isolation_rules.get("working_directory", ".") or "."
        return {
            "env": decision.environment,
            "cwd": str(Path(cwd)),
        }

    def evaluate(self, tool_name: str, payload: str, *, requested_timeout: int | None = None,
                 active_background_processes: int = 0) -> ExecutionPolicyDecision:
        if not self.allowed_tools.get(tool_name, False):
            env, rules = self._build_environment(tool_name)
            return ExecutionPolicyDecision(
                tool_name=tool_name,
                allowed=False,
                reason=f"Tool '{tool_name}' is disabled by execution policy.",
                timeout_seconds=0,
                resource_ceilings=self._tool_ceilings(tool_name),
                environment=env,
                isolation_rules=rules,
                audit_format=copy.deepcopy(self.audit_logging),
            )

        ceilings = self._tool_ceilings(tool_name)
        env, rules = self._build_environment(tool_name)
        blocked_reason = self._payload_block_reason(tool_name, payload, rules)
        if blocked_reason:
            return ExecutionPolicyDecision(
                tool_name=tool_name,
                allowed=False,
                reason=blocked_reason,
                timeout_seconds=0,
                resource_ceilings=ceilings,
                environment=env,
                isolation_rules=rules,
                audit_format=copy.deepcopy(self.audit_logging),
            )

        max_input = int(ceilings.get("max_input_chars", 100000))
        if len(payload or "") > max_input:
            return ExecutionPolicyDecision(
                tool_name=tool_name,
                allowed=False,
                reason=f"Input exceeds execution policy limit for '{tool_name}' ({len(payload)} > {max_input}).",
                timeout_seconds=0,
                resource_ceilings=ceilings,
                environment=env,
                isolation_rules=rules,
                audit_format=copy.deepcopy(self.audit_logging),
            )

        max_bg = int(ceilings.get("max_background_processes", self.resource_ceilings.get("default", {}).get("max_background_processes", 8)))
        if tool_name in {"spawn_background", "run_python_bg"} and active_background_processes >= max_bg:
            return ExecutionPolicyDecision(
                tool_name=tool_name,
                allowed=False,
                reason=f"Background process ceiling reached ({active_background_processes}/{max_bg}).",
                timeout_seconds=0,
                resource_ceilings=ceilings,
                environment=env,
                isolation_rules=rules,
                audit_format=copy.deepcopy(self.audit_logging),
            )

        default_timeout = int(self.timeout_defaults.get(tool_name, 30))
        max_timeout = int(self.timeout_overrides.get(tool_name, default_timeout))
        timeout_seconds = default_timeout if requested_timeout is None else min(int(requested_timeout), max_timeout)
        return ExecutionPolicyDecision(
            tool_name=tool_name,
            allowed=True,
            reason="allowed",
            timeout_seconds=max(1, timeout_seconds),
            resource_ceilings=ceilings,
            environment=env,
            isolation_rules=rules,
            audit_format=copy.deepcopy(self.audit_logging),
        )

    def trim_output(self, decision: ExecutionPolicyDecision, text: str) -> str:
        max_output = int(decision.resource_ceilings.get("max_output_chars", 12000))
        if text is None:
            return ""
        if len(text) <= max_output:
            return text
        return text[: max_output // 2] + "\n... [TRUNCATED BY EXECUTION POLICY] ...\n" + text[-(max_output // 3):]

    def audit(self, decision: ExecutionPolicyDecision, *, action: str, status: str,
              payload: str = "", result: str = "", reason: str = "",
              duration_ms: int | None = None, extra: dict[str, Any] | None = None):
        record = {
            "timestamp": datetime.now().isoformat(),
            "format": self.audit_logging.get("version", "execution_audit.v1"),
            "tool_name": decision.tool_name,
            "action": action,
            "status": status,
            "reason": reason or decision.reason,
            "timeout_seconds": decision.timeout_seconds,
            "duration_ms": duration_ms,
            "resource_ceilings": decision.resource_ceilings,
            "isolation": decision.isolation_rules,
            "payload_preview": (payload or "")[:400],
            "result_preview": (result or "")[:400],
        }
        if extra:
            record["extra"] = extra
        try:
            self.audit_log_path.parent.mkdir(parents=True, exist_ok=True)
            with open(self.audit_log_path, "a", encoding="utf-8") as f:
                f.write(json.dumps(record) + "\n")
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="ExecutionPolicyLayer.audit", code=ErrorCode.IO_ERROR)

# --- HELPER FUNCTIONS (RLM STYLE) ---

def _rlm_collect_files(root: str = ".", pattern: str = "*") -> list[Path]:
    root_path = Path(root)
    if not root_path.exists():
        return []
    return [path for path in root_path.rglob(pattern) if path.is_file() and not any(part.startswith('.') for part in path.parts)]


def _rlm_collect_files_multi(root: str = ".", patterns: list[str] | None = None) -> list[Path]:
    seen: set[Path] = set()
    collected: list[Path] = []
    for pattern in patterns or ["*"]:
        for path in _rlm_collect_files(root, pattern):
            if path in seen:
                continue
            seen.add(path)
            collected.append(path)
    return collected


def _rlm_result(tool: str, ok: bool = True, *, data: Any = None,
                warnings: list[Any] | None = None, errors: list[Any] | None = None,
                **extra) -> str:
    payload = {
        "ok": bool(ok),
        "tool": tool,
        "data": data if data is not None else {},
        "warnings": list(warnings or []),
        "errors": list(errors or []),
    }
    payload.update(extra)
    return json.dumps(payload, indent=2)


def _rlm_parse_pattern_list(patterns: str | list[str] | None, default: list[str]) -> list[str]:
    if patterns is None:
        return list(default)
    if isinstance(patterns, str):
        parts = [part.strip() for part in patterns.split(",")]
        return [part for part in parts if part] or list(default)
    return [str(part).strip() for part in patterns if str(part).strip()] or list(default)


def _rlm_python_files(root: str = ".", filepath: str = "") -> list[Path]:
    if filepath:
        path = Path(filepath)
        return [path] if path.exists() and path.is_file() else []
    return _rlm_collect_files_multi(root, ["*.py"])


def _rlm_read_text(path: Path) -> str:
    return path.read_text(encoding='utf-8', errors='replace')


def _rlm_python_symbol_matches(target: str, name: str, qualname: str) -> bool:
    return target == name or target == qualname


def _rlm_infer_simple_annotation(node: ast.AST | None) -> str | None:
    if node is None:
        return None
    if isinstance(node, ast.Constant):
        value = node.value
        if value is None:
            return "None"
        if isinstance(value, bool):
            return "bool"
        if isinstance(value, int) and not isinstance(value, bool):
            return "int"
        if isinstance(value, float):
            return "float"
        if isinstance(value, str):
            return "str"
        if isinstance(value, bytes):
            return "bytes"
    if isinstance(node, ast.List):
        inner = {_rlm_infer_simple_annotation(item) for item in node.elts}
        inner.discard(None)
        if len(inner) == 1:
            return f"list[{next(iter(inner))}]"
        return "list[Any]"
    if isinstance(node, ast.Tuple):
        inner = [_rlm_infer_simple_annotation(item) or "Any" for item in node.elts]
        return f"tuple[{', '.join(inner)}]" if inner else "tuple[Any, ...]"
    if isinstance(node, ast.Set):
        inner = {_rlm_infer_simple_annotation(item) for item in node.elts}
        inner.discard(None)
        if len(inner) == 1:
            return f"set[{next(iter(inner))}]"
        return "set[Any]"
    if isinstance(node, ast.Dict):
        key_types = {_rlm_infer_simple_annotation(item) for item in node.keys if item is not None}
        value_types = {_rlm_infer_simple_annotation(item) for item in node.values if item is not None}
        key_types.discard(None)
        value_types.discard(None)
        key_type = next(iter(key_types)) if len(key_types) == 1 else "Any"
        value_type = next(iter(value_types)) if len(value_types) == 1 else "Any"
        return f"dict[{key_type}, {value_type}]"
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        ctor = node.func.id
        if ctor in {"str", "int", "float", "bool", "list", "dict", "set", "tuple"}:
            return ctor
    return None


def _rlm_collect_python_returns(func_node: ast.AST) -> list[ast.AST | None]:
    returns: list[ast.AST | None] = []

    class _Collector(ast.NodeVisitor):
        def visit_Return(self, node):
            returns.append(node.value)

        def visit_FunctionDef(self, node):
            return

        def visit_AsyncFunctionDef(self, node):
            return

        def visit_ClassDef(self, node):
            return

    collector = _Collector()
    for stmt in getattr(func_node, "body", []):
        collector.visit(stmt)
    return returns


def _rlm_resolve_python_module(module: str, current_file: Path, root: Path, level: int = 0) -> str | None:
    try:
        root = root.resolve()
        if level > 0:
            base = current_file.parent.resolve()
            for _ in range(max(0, level - 1)):
                base = base.parent
            rel_parts = module.split('.') if module else []
            candidate_base = base.joinpath(*rel_parts) if rel_parts else base
            candidates = [candidate_base.with_suffix('.py'), candidate_base / '__init__.py']
        else:
            if not module:
                return None
            parts = module.split('.')
            candidate_base = root.joinpath(*parts)
            candidates = [candidate_base.with_suffix('.py'), candidate_base / '__init__.py']
        for candidate in candidates:
            try:
                resolved = candidate.resolve()
            except Exception:
                resolved = candidate
            if candidate.exists() and str(resolved).startswith(str(root)):
                return str(resolved)
    except Exception:
        return None
    return None


def rlm_search_workspace(query: str, root: str = ".", pattern: str = "*", is_regex: bool = False,
                         case_sensitive: bool = False, max_results: int = 50, context_lines: int = 1):
    results = []
    try:
        flags = 0 if case_sensitive else re.IGNORECASE
        regex = re.compile(query if is_regex else re.escape(query), flags)
        for path in _rlm_collect_files(root, pattern):
            try:
                lines = path.read_text(encoding='utf-8', errors='replace').splitlines()
            except Exception:
                continue
            for idx, line in enumerate(lines, start=1):
                if regex.search(line):
                    start = max(1, idx - context_lines)
                    end = min(len(lines), idx + context_lines)
                    snippet = "\n".join(lines[start - 1:end])
                    results.append({
                        "file": str(path),
                        "line": idx,
                        "match": line[:300],
                        "context": snippet[:1200],
                    })
                    if len(results) >= max_results:
                        return json.dumps(results, indent=2)
        return json.dumps(results, indent=2)
    except Exception as e:
        return json.dumps({"error": f"Workspace search error: {e}"})


def rlm_find_symbol(symbol_name: str, root: str = ".", pattern: str = "*.py", max_results: int = 50):
    results = []
    try:
        py_patterns = [pattern] if pattern else ["*.py"]
        search_patterns = py_patterns if py_patterns != ["*"] else ["*.py", "*.js", "*.jsx", "*.ts", "*.tsx"]
        compiled = [
            re.compile(rf"^\s*def\s+{re.escape(symbol_name)}\b"),
            re.compile(rf"^\s*class\s+{re.escape(symbol_name)}\b"),
            re.compile(rf"^\s*(?:async\s+def)\s+{re.escape(symbol_name)}\b"),
            re.compile(rf"^\s*(?:export\s+)?(?:const|let|var|function)\s+{re.escape(symbol_name)}\b"),
            re.compile(rf"^\s*(?:export\s+)?(?:interface|type|enum)\s+{re.escape(symbol_name)}\b"),
            re.compile(rf"^\s*(?:export\s+default\s+)?class\s+{re.escape(symbol_name)}\b"),
        ]
        seen = set()
        for search_pattern in search_patterns:
            for path in _rlm_collect_files(root, search_pattern):
                if path in seen:
                    continue
                seen.add(path)
                try:
                    lines = path.read_text(encoding='utf-8', errors='replace').splitlines()
                except Exception:
                    continue
                for idx, line in enumerate(lines, start=1):
                    if any(rx.search(line) for rx in compiled):
                        results.append({"file": str(path), "line": idx, "definition": line.strip()[:300]})
                        if len(results) >= max_results:
                            return json.dumps(results, indent=2)
        return json.dumps(results, indent=2)
    except Exception as e:
        return json.dumps({"error": f"Find symbol error: {e}"})


def rlm_python_symbol_doc(symbol_name: str, filepath: str = "", root: str = ".", max_results: int = 10):
    results = []
    try:
        for path in _rlm_python_files(root=root, filepath=filepath):
            source = _rlm_read_text(path)
            try:
                tree = ast.parse(source, filename=str(path))
            except SyntaxError:
                continue
            lines = source.splitlines()

            class _Visitor(ast.NodeVisitor):
                def __init__(self):
                    self.stack: list[str] = []

                def _record(self, node: ast.AST, name: str, kind: str):
                    qualname = ".".join(self.stack + [name]) if self.stack else name
                    if not _rlm_python_symbol_matches(symbol_name, name, qualname):
                        return
                    line_text = lines[node.lineno - 1].strip() if 0 < node.lineno <= len(lines) else ""
                    results.append({
                        "file": str(path),
                        "line": getattr(node, "lineno", 1),
                        "kind": kind,
                        "name": name,
                        "qualname": qualname,
                        "signature": line_text,
                        "docstring": (ast.get_docstring(node) or "")[:2000],
                    })

                def visit_ClassDef(self, node):
                    self._record(node, node.name, "class")
                    self.stack.append(node.name)
                    self.generic_visit(node)
                    self.stack.pop()

                def visit_FunctionDef(self, node):
                    self._record(node, node.name, "function")
                    self.stack.append(node.name)
                    self.generic_visit(node)
                    self.stack.pop()

                def visit_AsyncFunctionDef(self, node):
                    self._record(node, node.name, "async_function")
                    self.stack.append(node.name)
                    self.generic_visit(node)
                    self.stack.pop()

            _Visitor().visit(tree)
            if len(results) >= max_results:
                break
        return _rlm_result("python_symbol_doc", data={"matches": results[:max_results]}, match_count=len(results[:max_results]))
    except Exception as e:
        return _rlm_result("python_symbol_doc", ok=False, errors=[str(e)])


def rlm_python_import_graph(filepath: str, root: str = "."):
    path = Path(filepath)
    if not path.exists():
        return _rlm_result("python_import_graph", ok=False, errors=[f"File not found: {filepath}"])
    try:
        source = _rlm_read_text(path)
        tree = ast.parse(source, filename=str(path))
        root_path = Path(root).resolve()
        imports = []
        local_dependencies = []
        stdlib_modules = set()
        external_modules = set()
        local_set = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    module_name = alias.name
                    top_level = module_name.split('.')[0]
                    resolved = _rlm_resolve_python_module(module_name, path, root_path, 0)
                    record = {
                        "line": node.lineno,
                        "kind": "import",
                        "module": module_name,
                        "alias": alias.asname,
                        "resolved_path": resolved,
                    }
                    imports.append(record)
                    if resolved:
                        local_set.add(resolved)
                    elif top_level in getattr(sys, "stdlib_module_names", set()):
                        stdlib_modules.add(top_level)
                    else:
                        external_modules.add(top_level)
            elif isinstance(node, ast.ImportFrom):
                module_name = node.module or ""
                for alias in node.names:
                    target_name = f"{module_name}.{alias.name}".strip('.') if module_name else alias.name
                    resolved = _rlm_resolve_python_module(module_name or alias.name, path, root_path, node.level)
                    record = {
                        "line": node.lineno,
                        "kind": "from",
                        "module": module_name,
                        "name": alias.name,
                        "alias": alias.asname,
                        "level": node.level,
                        "resolved_path": resolved,
                    }
                    imports.append(record)
                    top_level = (module_name or alias.name or "").split('.')[0]
                    if resolved:
                        local_set.add(resolved)
                    elif top_level in getattr(sys, "stdlib_module_names", set()):
                        stdlib_modules.add(top_level)
                    elif top_level:
                        external_modules.add(top_level)
        local_dependencies = sorted(local_set)
        return _rlm_result(
            "python_import_graph",
            data={
                "file": str(path),
                "imports": imports,
                "local_dependencies": local_dependencies,
                "stdlib_modules": sorted(stdlib_modules),
                "external_modules": sorted(external_modules),
            },
            import_count=len(imports),
        )
    except SyntaxError as e:
        return _rlm_result("python_import_graph", ok=False, errors=[f"SyntaxError: {e}"])
    except Exception as e:
        return _rlm_result("python_import_graph", ok=False, errors=[str(e)])


def rlm_validate_python_snippet(code: str, mode: str = "exec"):
    try:
        ast.parse(code, mode=mode)
        return _rlm_result("validate_python_snippet", data={"mode": mode, "valid": True})
    except SyntaxError as e:
        return _rlm_result(
            "validate_python_snippet",
            ok=False,
            data={
                "mode": mode,
                "valid": False,
                "line": e.lineno,
                "offset": e.offset,
                "text": (e.text or "").rstrip(),
            },
            errors=[f"SyntaxError: {e.msg}"],
        )
    except Exception as e:
        return _rlm_result("validate_python_snippet", ok=False, errors=[str(e)])


def rlm_python_refactor_symbol(filepath: str, old_name: str, new_name: str, apply: bool = False):
    path = Path(filepath)
    if not path.exists():
        return _rlm_result("python_refactor_symbol", ok=False, errors=[f"File not found: {filepath}"])
    if not old_name.isidentifier() or not new_name.isidentifier():
        return _rlm_result("python_refactor_symbol", ok=False, errors=["Both old_name and new_name must be valid Python identifiers."])
    try:
        source = _rlm_read_text(path)
        token_stream = list(tokenize.generate_tokens(io.StringIO(source).readline))
        replacements = []
        rewritten = []
        for tok in token_stream:
            if tok.type == tokenize.NAME and tok.string == old_name:
                replacements.append({"line": tok.start[0], "column": tok.start[1] + 1})
                tok = tokenize.TokenInfo(tok.type, new_name, tok.start, tok.end, tok.line)
            rewritten.append(tok)
        new_source = tokenize.untokenize(rewritten)
        diff_text = "".join(difflib.unified_diff(
            source.splitlines(keepends=True),
            new_source.splitlines(keepends=True),
            fromfile=str(path),
            tofile=str(path),
            n=2,
        ))
        if apply and replacements:
            path.write_text(new_source, encoding='utf-8')
        return _rlm_result(
            "python_refactor_symbol",
            data={
                "file": str(path),
                "old_name": old_name,
                "new_name": new_name,
                "occurrences": len(replacements),
                "locations": replacements[:200],
                "applied": bool(apply and replacements),
                "diff_preview": diff_text[:4000],
            },
            warnings=[] if replacements else [f"No Python identifier tokens named '{old_name}' were found."],
        )
    except Exception as e:
        return _rlm_result("python_refactor_symbol", ok=False, errors=[str(e)])


def rlm_python_cleanup_unused_imports(filepath: str, apply: bool = False):
    path = Path(filepath)
    if not path.exists():
        return _rlm_result("python_cleanup_unused_imports", ok=False, errors=[f"File not found: {filepath}"])
    try:
        source = _rlm_read_text(path)
        tree = ast.parse(source, filename=str(path))
        lines = source.splitlines(keepends=True)
        used_names = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)}
        operations = []
        unused_imports = []
        warnings = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                alias_info = []
                for alias in node.names:
                    bound_name = alias.asname or alias.name.split('.')[0]
                    alias_info.append((alias, bound_name))
                unused = [alias for alias, bound_name in alias_info if bound_name not in used_names]
                if not unused:
                    continue
                unused_imports.extend(alias.name for alias in unused)
                kept = [alias for alias, bound_name in alias_info if bound_name in used_names]
                indent = re.match(r"\s*", lines[node.lineno - 1]).group(0)
                replacement = None if not kept else indent + "import " + ", ".join(
                    f"{alias.name} as {alias.asname}" if alias.asname else alias.name for alias in kept
                ) + "\n"
                operations.append((node.lineno, getattr(node, "end_lineno", node.lineno), replacement))
            elif isinstance(node, ast.ImportFrom):
                if any(alias.name == "*" for alias in node.names):
                    warnings.append(f"Skipped wildcard import at line {node.lineno} in {filepath}.")
                    continue
                alias_info = []
                for alias in node.names:
                    bound_name = alias.asname or alias.name
                    alias_info.append((alias, bound_name))
                unused = [alias for alias, bound_name in alias_info if bound_name not in used_names]
                if not unused:
                    continue
                unused_imports.extend(f"{node.module or ''}.{alias.name}".strip('.') for alias in unused)
                kept = [alias for alias, bound_name in alias_info if bound_name in used_names]
                indent = re.match(r"\s*", lines[node.lineno - 1]).group(0)
                if kept:
                    module_prefix = "." * getattr(node, "level", 0)
                    module_name = node.module or ""
                    replacement = indent + f"from {module_prefix}{module_name} import " + ", ".join(
                        f"{alias.name} as {alias.asname}" if alias.asname else alias.name for alias in kept
                    ) + "\n"
                else:
                    replacement = None
                operations.append((node.lineno, getattr(node, "end_lineno", node.lineno), replacement))

        if not operations:
            return _rlm_result(
                "python_cleanup_unused_imports",
                data={"file": str(path), "unused_imports": [], "applied": False, "diff_preview": ""},
                warnings=warnings,
            )

        new_lines = list(lines)
        for start, end, replacement in sorted(operations, key=lambda item: item[0], reverse=True):
            new_lines[start - 1:end] = [] if replacement is None else [replacement]
        new_source = "".join(new_lines)
        diff_text = "".join(difflib.unified_diff(
            source.splitlines(keepends=True),
            new_source.splitlines(keepends=True),
            fromfile=str(path),
            tofile=str(path),
            n=2,
        ))
        if apply:
            path.write_text(new_source, encoding='utf-8')
        return _rlm_result(
            "python_cleanup_unused_imports",
            data={
                "file": str(path),
                "unused_imports": sorted(set(unused_imports)),
                "applied": bool(apply),
                "diff_preview": diff_text[:4000],
            },
            warnings=warnings,
        )
    except SyntaxError as e:
        return _rlm_result("python_cleanup_unused_imports", ok=False, errors=[f"SyntaxError: {e}"])
    except Exception as e:
        return _rlm_result("python_cleanup_unused_imports", ok=False, errors=[str(e)])


def rlm_python_type_annotation_assist(filepath: str):
    path = Path(filepath)
    if not path.exists():
        return _rlm_result("python_type_annotation_assist", ok=False, errors=[f"File not found: {filepath}"])
    try:
        tree = ast.parse(_rlm_read_text(path), filename=str(path))
        suggestions = []
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                positional_args = list(getattr(node.args, "posonlyargs", [])) + list(node.args.args)
                defaults = list(node.args.defaults)
                default_offset = len(positional_args) - len(defaults)
                for index, arg in enumerate(positional_args):
                    if arg.annotation is not None:
                        continue
                    default_node = defaults[index - default_offset] if index >= default_offset and index - default_offset < len(defaults) else None
                    inferred = _rlm_infer_simple_annotation(default_node)
                    if inferred:
                        suggestions.append({
                            "file": str(path),
                            "line": arg.lineno,
                            "kind": "parameter",
                            "target": f"{node.name}.{arg.arg}",
                            "suggested_annotation": inferred,
                        })
                if node.returns is None:
                    return_types = {_rlm_infer_simple_annotation(ret) for ret in _rlm_collect_python_returns(node)}
                    return_types.discard(None)
                    if len(return_types) == 1:
                        suggestions.append({
                            "file": str(path),
                            "line": node.lineno,
                            "kind": "return",
                            "target": node.name,
                            "suggested_annotation": next(iter(return_types)),
                        })
            elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                inferred = _rlm_infer_simple_annotation(node.value)
                if inferred:
                    suggestions.append({
                        "file": str(path),
                        "line": node.lineno,
                        "kind": "variable",
                        "target": node.targets[0].id,
                        "suggested_annotation": inferred,
                    })
        return _rlm_result(
            "python_type_annotation_assist",
            data={"file": str(path), "suggestions": suggestions[:200]},
            suggestion_count=len(suggestions),
        )
    except SyntaxError as e:
        return _rlm_result("python_type_annotation_assist", ok=False, errors=[f"SyntaxError: {e}"])
    except Exception as e:
        return _rlm_result("python_type_annotation_assist", ok=False, errors=[str(e)])


def rlm_find_references(symbol_name: str, root: str = ".", patterns: str | list[str] | None = None,
                        max_results: int = 100, case_sensitive: bool = False):
    try:
        search_patterns = _rlm_parse_pattern_list(patterns, ["*.py", "*.js", "*.jsx", "*.ts", "*.tsx"])
        flags = 0 if case_sensitive else re.IGNORECASE
        regex = re.compile(rf"\b{re.escape(symbol_name)}\b", flags)
        results = []
        for path in _rlm_collect_files_multi(root, search_patterns):
            try:
                for idx, line in enumerate(_rlm_read_text(path).splitlines(), start=1):
                    if regex.search(line):
                        results.append({"file": str(path), "line": idx, "match": line.strip()[:300]})
                        if len(results) >= max_results:
                            return _rlm_result("find_references", data={"references": results}, match_count=len(results))
            except Exception:
                continue
        return _rlm_result("find_references", data={"references": results}, match_count=len(results))
    except Exception as e:
        return _rlm_result("find_references", ok=False, errors=[str(e)])


def rlm_find_implementations(symbol_name: str, root: str = ".", patterns: str | list[str] | None = None,
                             max_results: int = 100):
    try:
        search_patterns = _rlm_parse_pattern_list(patterns, ["*.py", "*.js", "*.jsx", "*.ts", "*.tsx"])
        matchers = [
            re.compile(rf"^\s*class\s+\w+\s*\((?:[^\)]*\b{re.escape(symbol_name)}\b[^\)]*)\)"),
            re.compile(rf"^\s*(?:export\s+)?class\s+\w+\s+(?:extends|implements)\s+[^{{\n;]*\b{re.escape(symbol_name)}\b"),
            re.compile(rf"^\s*class\s+\w+\s+implements\s+[^{{\n;]*\b{re.escape(symbol_name)}\b"),
        ]
        results = []
        for path in _rlm_collect_files_multi(root, search_patterns):
            try:
                for idx, line in enumerate(_rlm_read_text(path).splitlines(), start=1):
                    if any(rx.search(line) for rx in matchers):
                        results.append({"file": str(path), "line": idx, "implementation": line.strip()[:300]})
                        if len(results) >= max_results:
                            return _rlm_result("find_implementations", data={"implementations": results}, match_count=len(results))
            except Exception:
                continue
        return _rlm_result("find_implementations", data={"implementations": results}, match_count=len(results))
    except Exception as e:
        return _rlm_result("find_implementations", ok=False, errors=[str(e)])


def rlm_preview_symbol_rename(symbol_name: str, new_name: str, root: str = ".",
                              patterns: str | list[str] | None = None, max_results: int = 200):
    if not symbol_name:
        return _rlm_result("preview_symbol_rename", ok=False, errors=["symbol_name is required."])
    if not new_name:
        return _rlm_result("preview_symbol_rename", ok=False, errors=["new_name is required."])
    try:
        search_patterns = _rlm_parse_pattern_list(patterns, ["*.py", "*.js", "*.jsx", "*.ts", "*.tsx"])
        regex = re.compile(rf"\b{re.escape(symbol_name)}\b")
        matches = []
        file_totals: dict[str, int] = {}
        for path in _rlm_collect_files_multi(root, search_patterns):
            try:
                for idx, line in enumerate(_rlm_read_text(path).splitlines(), start=1):
                    count = len(regex.findall(line))
                    if not count:
                        continue
                    file_totals[str(path)] = file_totals.get(str(path), 0) + count
                    if len(matches) < max_results:
                        matches.append({
                            "file": str(path),
                            "line": idx,
                            "before": line.strip()[:300],
                            "after": regex.sub(new_name, line.strip())[:300],
                            "occurrences": count,
                        })
            except Exception:
                continue
        return _rlm_result(
            "preview_symbol_rename",
            data={
                "symbol_name": symbol_name,
                "new_name": new_name,
                "file_totals": file_totals,
                "matches": matches,
            },
            match_count=sum(file_totals.values()),
            warnings=["Preview only; no files were modified."],
        )
    except Exception as e:
        return _rlm_result("preview_symbol_rename", ok=False, errors=[str(e)])


def rlm_read_range(filepath, start_line=1, end_line=100):
    try:
        path = Path(filepath)
        if not path.exists():
            return f"File not found: {filepath}"
        lines = path.read_text(encoding='utf-8', errors='replace').splitlines()
        start = max(1, int(start_line))
        end = max(start, int(end_line))
        selected = lines[start - 1:end]
        numbered = "\n".join(f"{i}: {line}" for i, line in enumerate(selected, start=start))
        return numbered
    except Exception as e:
        return f"Read range error: {e}"


def rlm_create_file(filepath, content="", overwrite=False):
    try:
        path = Path(filepath)
        if path.exists() and not overwrite:
            return f"Create error: File already exists at {filepath}"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding='utf-8')
        return f"Successfully created {filepath}"
    except Exception as e:
        return f"Create error: {e}"


def rlm_delete_file(filepath, missing_ok=True):
    try:
        path = Path(filepath)
        if not path.exists():
            return f"Delete skipped: File not found at {filepath}" if missing_ok else f"Delete error: File not found at {filepath}"
        if path.is_dir():
            return f"Delete error: {filepath} is a directory"
        path.unlink()
        return f"Successfully deleted {filepath}"
    except Exception as e:
        return f"Delete error: {e}"


def rlm_move_file(src, dst, overwrite=False):
    try:
        src_path = Path(src)
        dst_path = Path(dst)
        if not src_path.exists():
            return f"Move error: Source not found at {src}"
        if dst_path.exists() and not overwrite:
            return f"Move error: Destination already exists at {dst}"
        dst_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(src_path), str(dst_path))
        return f"Successfully moved {src} to {dst}"
    except Exception as e:
        return f"Move error: {e}"


def rlm_validate_python(filepath: str = "", code: str = ""):
    try:
        if filepath:
            path = Path(filepath)
            if not path.exists():
                return json.dumps({"ok": False, "tool": "validate_python", "errors": [f"File not found: {filepath}"]}, indent=2)
            py_compile.compile(str(path), doraise=True)
            return json.dumps({"ok": True, "tool": "validate_python", "target": str(path), "errors": []}, indent=2)
        ast.parse(code)
        return json.dumps({"ok": True, "tool": "validate_python", "target": "inline", "errors": []}, indent=2)
    except Exception as e:
        return json.dumps({"ok": False, "tool": "validate_python", "errors": [str(e)]}, indent=2)


def rlm_validate_json(filepath: str = "", content: str = ""):
    try:
        if filepath:
            path = Path(filepath)
            if not path.exists():
                return json.dumps({"ok": False, "tool": "validate_json", "errors": [f"File not found: {filepath}"]}, indent=2)
            json.loads(path.read_text(encoding='utf-8'))
            return json.dumps({"ok": True, "tool": "validate_json", "target": str(path), "errors": []}, indent=2)
        json.loads(content)
        return json.dumps({"ok": True, "tool": "validate_json", "target": "inline", "errors": []}, indent=2)
    except Exception as e:
        return json.dumps({"ok": False, "tool": "validate_json", "errors": [str(e)]}, indent=2)


def rlm_inspect_python_environment():
    try:
        info = {
            "ok": True,
            "tool": "inspect_python_environment",
            "python_executable": sys.executable,
            "python_version": sys.version,
            "prefix": sys.prefix,
            "base_prefix": getattr(sys, "base_prefix", sys.prefix),
            "cwd": os.getcwd(),
            "venv_active": sys.prefix != getattr(sys, "base_prefix", sys.prefix),
            "env": {
                "VIRTUAL_ENV": os.environ.get("VIRTUAL_ENV", ""),
                "CONDA_PREFIX": os.environ.get("CONDA_PREFIX", ""),
                "PYTHONPATH": os.environ.get("PYTHONPATH", ""),
            },
            "site_paths": list(getattr(sys, "path", [])[:20]),
        }
        return json.dumps(info, indent=2)
    except Exception as e:
        return json.dumps({"ok": False, "tool": "inspect_python_environment", "errors": [str(e)]}, indent=2)


def rlm_list_python_packages(limit: int = 500):
    try:
        cmd = [sys.executable, "-m", "pip", "list", "--format=json"]
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=60, encoding='utf-8', errors='replace')
        if res.returncode != 0:
            return json.dumps({"ok": False, "tool": "list_python_packages", "errors": [res.stderr.strip() or res.stdout.strip() or "pip list failed"]}, indent=2)
        data = json.loads(res.stdout or "[]")
        return json.dumps({"ok": True, "tool": "list_python_packages", "count": len(data), "packages": data[: int(limit)]}, indent=2)
    except Exception as e:
        return json.dumps({"ok": False, "tool": "list_python_packages", "errors": [str(e)]}, indent=2)

def get_terminal_environment() -> Dict[str, Any]:
    """Detects the current terminal execution environment."""
    env = os.environ
    info = {
        "platform": os.name, # 'nt' or 'posix'
        "os_system": platform.system(),
        "terminal_type": "unknown",
        "is_termux": False,
        "is_vscode": False,
        "is_windows_terminal": False,
        "program": env.get("TERM_PROGRAM", "unknown"),
        "shell": env.get("SHELL", env.get("COMSPEC", "unknown"))
    }

    # 1. Termux Detection
    if "com.termux" in env.get("PREFIX", ""):
        info["terminal_type"] = "Termux"
        info["is_termux"] = True
    
    # 2. VS Code Detection
    elif "VSCODE_PID" in env or "VSCODE_IPC_HOOK_CLI" in env or env.get("TERM_PROGRAM") == "vscode":
        info["terminal_type"] = "VS Code Integrated"
        info["is_vscode"] = True
    
    # 3. Windows Terminal
    elif "WT_SESSION" in env:
        info["terminal_type"] = "Windows Terminal"
        info["is_windows_terminal"] = True
    
    # 4. Standard Windows CMD/PowerShell (fallback)
    elif os.name == 'nt':
        if "PROMPT" in env: # CMD usually has PROMPT
            info["terminal_type"] = "CMD/PowerShell (Legacy)"
    
    # 5. Standard Linux/Mac
    elif os.name == 'posix':
        info["terminal_type"] = env.get("TERM", "posix-tty")

    return info

def rlm_grep(pattern, filepath, context_lines=2):
    results = []
    try:
        if not os.path.exists(filepath): return f"File not found: {filepath}"
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        for i, line in enumerate(lines):
            if re.search(pattern, line):
                start = max(0, i - context_lines)
                end = min(len(lines), i + context_lines + 1)
                snippet = "".join(lines[start:end])
                results.append(f"--- Match at line {i+1} ---\n{snippet}")
        return "\n".join(results) if results else "No matches found."
    except Exception as e: return f"Grep error: {e}"

def rlm_peek(filepath, start_line=0, end_line=30):
    try:
        if not os.path.exists(filepath): return f"File not found: {filepath}"
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        
        content = "".join(lines[start_line:end_line])
        if len(lines) > end_line:
            content += f"\n... (truncated, total lines: {len(lines)})"
        return content
    except Exception as e: return f"Peek error: {e}"

def rlm_read(filepath):
    try:
        if not os.path.exists(filepath): return f"File not found: {filepath}"
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            return f.read()
    except Exception as e: return f"Read error: {e}"

def rlm_write(filepath, content):
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return f"Successfully wrote to {filepath}"
    except Exception as e: return f"Write error: {e}"

def rlm_patch(filepath, search_block, replace_block, count=1):
    try:
        if not os.path.exists(filepath): return f"File not found: {filepath}"
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            content = f.read()
        
        occ = content.count(search_block)
        if occ == 0: return f"Patch error: Search block not found in {filepath}"
        if count > 0 and occ != count:
            return f"Patch error: Expected {count} occurrence(s), but found {occ} in {filepath}. Patch aborted for safety."
        
        new_content = content.replace(search_block, replace_block, count if count > 0 else -1)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return f"Successfully patched {filepath} ({occ} replacement(s))"
    except Exception as e: return f"Patch error: {e}"

def rlm_edit_lines(filepath, start_line, end_line, new_content):
    """Surgically replaces a range of lines (1-indexed, inclusive)."""
    try:
        if not os.path.exists(filepath): return f"File not found: {filepath}"
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        
        # Adjust to 0-indexed
        s = max(0, start_line - 1)
        e = min(len(lines), end_line)
        
        if s >= len(lines): return f"Edit error: start_line {start_line} is beyond file length"
        
        # Prepare replacement
        if not new_content.endswith('\n') and e < len(lines):
            new_content += '\n'
            
        lines[s:e] = [new_content]
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(lines)
        return f"Successfully edited lines {start_line}-{end_line} in {filepath}"
    except Exception as e: return f"Edit error: {e}"

def rlm_find_files(pattern, root="."):
    matches = []
    try:
        for path in Path(root).rglob(pattern):
            matches.append(str(path))
        return "\n".join(matches) if matches else "No files found."
    except Exception as e: return f"Find error: {e}"

def rlm_tree(root=".", depth=2):
    output = []
    root_path = Path(root)
    try:
        def walk(path, current_depth):
            if current_depth > int(depth): return
            entries = sorted([x for x in path.iterdir()], key=lambda x: (not x.is_dir(), x.name))
            for entry in entries:
                if entry.name.startswith("."): continue # sensitive/hidden skip
                indent = "  " * current_depth
                marker = "[DIR] " if entry.is_dir() else ""
                output.append(f"{indent}{marker}{entry.name}")
                if entry.is_dir():
                    walk(entry, current_depth + 1)
        output.append(f"Root: {root_path.resolve()}")
        walk(root_path, 0)
        return "\n".join(output)
    except Exception as e: return f"Tree error: {e}"

def rlm_read_metadata(filepath):
    try:
        p = Path(filepath)
        if not p.exists(): return f"File not found: {filepath}"
        stat = p.stat()
        return f"File: {filepath}\nSize: {stat.st_size} bytes\nModified: {time.ctime(stat.st_mtime)}"
    except Exception as e: return f"Metadata error: {e}"

def rlm_history_search(query: str, limit: int = 10):
    """Searches the persistent JSONL archive for keywords."""
    results = []
    if not ARCHIVE_FILE.exists(): return "No history archive found."
    try:
        with open(ARCHIVE_FILE, "r", encoding="utf-8") as f:
            for line in f:
                if query.lower() in line.lower():
                    data = json.loads(line)
                    results.append(f"[{time.ctime(data['ts'])}] {data['role'].upper()}: {data['content'][:200]}...")
        
        if not results: return f"No matches found for '{query}' in archive."
        return "\n".join(results[-limit:]) # Return last N matches
    except Exception as e: return f"History search error: {e}"

def rlm_map_dependencies(filepath: str):
    """Uses static analysis (parsing import statements) to show local file dependencies."""
    path = Path(filepath)
    if not path.exists(): return f"Error: File '{filepath}' not found."
    
    deps = []
    ext = path.suffix.lower()
    try:
        content = path.read_text(encoding='utf-8', errors='replace')
        if ext == '.py':
            # Python imports: from x import y, import x.y
            py_imports = re.findall(r'^(?:from|import)\s+([\w\.]+)', content, re.MULTILINE)
            for imp in py_imports:
                parts = imp.split('.')
                potential_path = path.parent / (parts[0] + ".py")
                if potential_path.exists():
                    deps.append(str(potential_path))
                potential_dir = path.parent / parts[0]
                if potential_dir.is_dir():
                    deps.append(str(potential_dir))

        elif ext in ['.ts', '.tsx', '.js', '.jsx']:
            # JS/TS imports: from "./y" or "./y.ts"
            js_imports = re.findall(r"from\s+['\"](\.?\.\/[^'\"]+)['\"]", content)
            for imp in js_imports:
                p = (path.parent / imp).resolve()
                for suffix in ['', '.ts', '.tsx', '.js', '.jsx', '/index.ts', '/index.tsx']:
                    candidate = Path(str(p) + suffix)
                    if candidate.exists():
                        deps.append(str(candidate))
                        break
        
        return sorted(list(set(deps)))
    except Exception as e:
        return f"Error mapping dependencies for {filepath}: {e}"

def rlm_project_summary(root: str = "."):
    """Generates a high-level architectural overview of the workspace."""
    root_path = Path(root)
    summary = []
    summary.append(f"# Project Summary: {root_path.resolve().name}")
    summary.append(f"Location: {root_path.resolve()}")
    
    configs = []
    for cfg in ["package.json", "requirements.txt", "pyproject.toml", "setup.py", "tsconfig.json"]:
        if (root_path / cfg).exists(): configs.append(cfg)
    if configs: summary.append(f"Key Configs: {', '.join(configs)}")

    if (root_path / "package.json").exists():
        summary.append("Primary Stack: Node.js / TypeScript")
        try:
            with open(root_path / "package.json", "r") as f:
                pkg = json.load(f)
                deps = list(pkg.get("dependencies", {}).keys()) + list(pkg.get("devDependencies", {}).keys())
                if "next" in deps: summary.append("Framework: Next.js")
                if "prisma" in deps: summary.append("ORM: Prisma")
        except: pass
    elif (root_path / "requirements.txt").exists() or (root_path / "pyproject.toml").exists():
        summary.append("Primary Stack: Python")

    summary.append("\n## Structure Overview")
    for item in sorted(root_path.iterdir()):
        if item.name.startswith(".") or item.name == "__pycache__": continue
        marker = "[DIR]" if item.is_dir() else "     "
        summary.append(f"{marker} {item.name}")

    return "\n".join(summary)


def _rlm_run_git(repo_path: str, args: list[str], timeout: int = 30) -> tuple[bool, str]:
    repo = Path(repo_path)
    cmd = ["git", "-C", str(repo), *args]
    try:
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, encoding='utf-8', errors='replace')
        output = (res.stdout or "") + (("\n" + res.stderr) if res.stderr else "")
        return res.returncode == 0, output.strip()
    except Exception as e:
        return False, str(e)


def _rlm_git_repo_meta(repo_path: str = ".") -> tuple[bool, dict[str, Any], list[str]]:
    repo = Path(repo_path)
    ok_root, root_out = _rlm_run_git(str(repo), ["rev-parse", "--show-toplevel"])
    if not ok_root:
        return False, {}, [f"Not a git repository: {repo}"]
    ok_branch, branch_out = _rlm_run_git(str(repo), ["rev-parse", "--abbrev-ref", "HEAD"])
    ok_head, head_out = _rlm_run_git(str(repo), ["rev-parse", "--short", "HEAD"])
    full_head_ok, full_head_out = _rlm_run_git(str(repo), ["rev-parse", "--verify", "HEAD"])
    meta = {
        "repo_path": str(repo.resolve()),
        "repo_root": root_out.splitlines()[0].strip() if root_out else str(repo.resolve()),
        "branch": branch_out.splitlines()[0].strip() if ok_branch and branch_out and "fatal:" not in branch_out.lower() else "UNKNOWN",
        "head": head_out.splitlines()[0].strip() if ok_head and head_out and "fatal:" not in head_out.lower() else "UNBORN",
        "has_head": bool(full_head_ok),
    }
    warnings = []
    if not ok_branch and branch_out and "fatal:" not in branch_out.lower():
        warnings.append(branch_out)
    if not ok_head and head_out and "fatal:" not in head_out.lower():
        warnings.append(head_out)
    return True, meta, [w for w in warnings if w]


def rlm_git_changed_files(repo_path: str = ".", include_untracked: bool = True):
    ok_meta, meta, warnings = _rlm_git_repo_meta(repo_path)
    if not ok_meta:
        return _rlm_result("git_changed_files", ok=False, errors=warnings)
    ok, output = _rlm_run_git(repo_path, ["status", "--short"])
    if not ok:
        return _rlm_result("git_changed_files", ok=False, errors=[output], warnings=warnings, data=meta)
    files = []
    counts = {"staged": 0, "unstaged": 0, "untracked": 0, "conflicts": 0}
    for raw_line in output.splitlines():
        if not raw_line.strip():
            continue
        line = raw_line.rstrip("\n")
        if len(line) < 3:
            continue
        x_status = line[0]
        y_status = line[1]
        path_text = line[3:].strip()
        if x_status == "?" and y_status == "?" and not include_untracked:
            continue
        record = {
            "path": path_text,
            "index_status": x_status,
            "worktree_status": y_status,
            "staged": x_status not in {" ", "?"},
            "unstaged": y_status not in {" ", "?"},
            "untracked": x_status == "?" and y_status == "?",
            "conflict": x_status == "U" or y_status == "U" or (x_status == "A" and y_status == "A"),
        }
        if record["staged"]:
            counts["staged"] += 1
        if record["unstaged"]:
            counts["unstaged"] += 1
        if record["untracked"]:
            counts["untracked"] += 1
        if record["conflict"]:
            counts["conflicts"] += 1
        files.append(record)
    return _rlm_result("git_changed_files", data={**meta, "files": files, "counts": counts}, warnings=warnings)


def rlm_git_diff_analysis(repo_path: str = ".", src: str = "HEAD", dst: str = "", max_patch_chars: int = 4000):
    ok_meta, meta, warnings = _rlm_git_repo_meta(repo_path)
    if not ok_meta:
        return _rlm_result("git_diff_analysis", ok=False, errors=warnings)
    empty_tree = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
    base_src = src
    if src == "HEAD" and not meta.get("has_head", False):
        base_src = empty_tree
    ref_args = [base_src] + ([dst] if dst else [])
    ok_numstat, numstat = _rlm_run_git(repo_path, ["diff", "--numstat", *ref_args])
    if not ok_numstat:
        return _rlm_result("git_diff_analysis", ok=False, errors=[numstat], warnings=warnings, data=meta)
    ok_stat, stat_out = _rlm_run_git(repo_path, ["diff", "--stat", *ref_args])
    ok_patch, patch_out = _rlm_run_git(repo_path, ["diff", "--", *([] if src == "HEAD" and not dst else ref_args)]) if False else (True, "")
    # keep patch retrieval independent to avoid ambiguous argument placement
    ok_patch, patch_out = _rlm_run_git(repo_path, ["diff", *ref_args])
    files = []
    total_additions = 0
    total_deletions = 0
    for line in numstat.splitlines():
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        added_raw, deleted_raw, path_text = parts[0], parts[1], parts[2]
        additions = 0 if added_raw == "-" else int(added_raw)
        deletions = 0 if deleted_raw == "-" else int(deleted_raw)
        total_additions += additions
        total_deletions += deletions
        files.append({
            "path": path_text,
            "additions": additions,
            "deletions": deletions,
            "binary": added_raw == "-" or deleted_raw == "-",
        })
    files.sort(key=lambda item: (item["additions"] + item["deletions"]), reverse=True)
    summary = {
        **meta,
        "range": {"src": src, "dst": dst},
        "files_changed": len(files),
        "additions": total_additions,
        "deletions": total_deletions,
        "files": files,
        "stat": stat_out if ok_stat else "",
        "patch_preview": patch_out[:max_patch_chars] if ok_patch else "",
    }
    return _rlm_result("git_diff_analysis", data=summary, warnings=warnings + ([] if ok_patch else [patch_out]))


def rlm_git_blame_context(filepath: str, line: int, repo_path: str = "."):
    """Retrieves blame metadata and the commit message associated with a specific line of code."""
    ok_meta, meta, warnings = _rlm_git_repo_meta(repo_path)
    if not ok_meta:
        return _rlm_result("git_blame_context", ok=False, errors=warnings)
    if not meta.get("has_head", False):
        return _rlm_result("git_blame_context", ok=False, errors=["No commits available for blame context."], warnings=warnings, data=meta)
    try:
        ok, blame_out = _rlm_run_git(repo_path, ["blame", "-L", f"{line},{line}", "--porcelain", filepath])
        if not ok:
            return _rlm_result("git_blame_context", ok=False, errors=[blame_out], warnings=warnings, data=meta)
        lines = blame_out.splitlines()
        if not lines:
            return _rlm_result("git_blame_context", ok=False, errors=["No blame output returned."], warnings=warnings, data=meta)
        commit_hash = lines[0].split()[0]
        info = {"commit": commit_hash, "author": "", "author_time": "", "summary": "", "line": int(line), "file": filepath}
        code_line = ""
        for item in lines[1:]:
            if item.startswith("author "):
                info["author"] = item[len("author "):]
            elif item.startswith("author-time "):
                try:
                    info["author_time"] = datetime.fromtimestamp(int(item[len("author-time "):])).isoformat()
                except Exception:
                    info["author_time"] = item[len("author-time "):]
            elif item.startswith("summary "):
                info["summary"] = item[len("summary "):]
            elif item.startswith("\t"):
                code_line = item[1:]
                break
        ok_msg, msg_out = _rlm_run_git(repo_path, ["show", "-s", "--format=%B", commit_hash])
        info["message"] = msg_out.strip() if ok_msg else ""
        info["code"] = code_line
        return _rlm_result("git_blame_context", data={**meta, **info}, warnings=warnings + ([] if ok_msg else [msg_out]))
    except Exception as e:
        return _rlm_result("git_blame_context", ok=False, errors=[str(e)], warnings=warnings, data=meta if ok_meta else {})


def rlm_git_commit_message_draft(repo_path: str = ".", src: str = "HEAD", dst: str = ""):
    diff_data = json.loads(rlm_git_diff_analysis(repo_path=repo_path, src=src, dst=dst))
    if not diff_data.get("ok"):
        return _rlm_result("git_commit_message_draft", ok=False, errors=diff_data.get("errors", []), warnings=diff_data.get("warnings", []))
    changed = diff_data.get("data", {})
    files = changed.get("files", [])
    if not files:
        return _rlm_result("git_commit_message_draft", data={**changed, "title": "chore: no changes detected", "body": "No diff content found."}, warnings=diff_data.get("warnings", []))
    extensions = [Path(item.get("path", "")).suffix.lower() for item in files]
    ext_counts: dict[str, int] = {}
    for ext in extensions:
        ext_counts[ext or "[no extension]"] = ext_counts.get(ext or "[no extension]", 0) + 1
    dominant_ext = max(ext_counts.items(), key=lambda item: item[1])[0]
    area = "project"
    if dominant_ext in {".py"}:
        area = "python"
    elif dominant_ext in {".ts", ".tsx", ".js", ".jsx"}:
        area = "web"
    elif dominant_ext in {".md"}:
        area = "docs"
    top_files = [item["path"] for item in files[:3]]
    title = f"feat({area}): update {', '.join(Path(path).stem for path in top_files[:2])}" if top_files else f"chore({area}): update repository"
    bullet_lines = []
    for item in files[:6]:
        bullet_lines.append(f"- {item['path']}: +{item['additions']} / -{item['deletions']}")
    body = "\n".join([
        f"Files changed: {changed.get('files_changed', 0)}",
        f"Additions: {changed.get('additions', 0)}",
        f"Deletions: {changed.get('deletions', 0)}",
        "",
        "Highlights:",
        *bullet_lines,
    ])
    return _rlm_result(
        "git_commit_message_draft",
        data={**changed, "title": title[:72], "body": body, "top_files": top_files},
        warnings=diff_data.get("warnings", []),
    )


def _rlm_config_inventory(root: str = ".") -> list[dict[str, Any]]:
    root_path = Path(root)
    config_names = [
        "package.json", "package-lock.json", "pnpm-lock.yaml", "yarn.lock", "tsconfig.json",
        "requirements.txt", "pyproject.toml", "setup.py", "setup.cfg", "Pipfile", "poetry.lock",
        "Dockerfile", "docker-compose.yml", "docker-compose.yaml", ".env", ".env.example",
        "README.md", "Makefile", ".github/workflows",
    ]
    inventory = []
    for name in config_names:
        path = root_path / name
        if path.exists():
            inventory.append({
                "path": str(path),
                "type": "directory" if path.is_dir() else "file",
                "size": path.stat().st_size if path.is_file() else 0,
            })
    return inventory


def _rlm_detect_entrypoints(root: str = ".") -> list[dict[str, Any]]:
    root_path = Path(root)
    entrypoints = []
    candidate_names = {
        "main.py", "app.py", "manage.py", "server.py", "index.js", "index.ts", "main.ts",
        "main.js", "vite.config.ts", "next.config.js", "wsgi.py", "asgi.py",
    }
    for path in _rlm_collect_files_multi(root, ["*.py", "*.js", "*.ts", "*.tsx", "*.jsx"]):
        if path.name in candidate_names:
            entrypoints.append({"path": str(path), "reason": f"well-known filename '{path.name}'"})
            continue
        try:
            text = _rlm_read_text(path)
        except Exception:
            continue
        if path.suffix == ".py" and re.search(r"if\s+__name__\s*==\s*['\"]__main__['\"]", text):
            entrypoints.append({"path": str(path), "reason": "python __main__ guard"})
        elif path.suffix in {".js", ".jsx", ".ts", ".tsx"} and re.search(r"(createServer|app\.listen|ReactDOM\.createRoot|new\s+Vue|bootstrapApplication)", text):
            entrypoints.append({"path": str(path), "reason": "startup/bootstrap pattern"})
    package_json = root_path / "package.json"
    if package_json.exists():
        try:
            pkg = json.loads(package_json.read_text(encoding='utf-8'))
            scripts = pkg.get("scripts", {}) if isinstance(pkg, dict) else {}
            for name, command in scripts.items():
                if name in {"start", "dev", "build", "test"}:
                    entrypoints.append({"path": str(package_json), "reason": f"package.json script '{name}'", "command": command})
        except Exception:
            pass
    return entrypoints


def _rlm_detect_languages(root: str = ".") -> dict[str, int]:
    counts: dict[str, int] = {}
    for path in _rlm_collect_files_multi(root, ["*.py", "*.js", "*.jsx", "*.ts", "*.tsx", "*.json", "*.md", "*.toml", "*.yml", "*.yaml"]):
        ext = path.suffix.lower() or "[no extension]"
        counts[ext] = counts.get(ext, 0) + 1
    return counts


def rlm_project_relationships(root: str = ".", max_nodes: int = 120):
    try:
        nodes = []
        edges = []
        root_path = Path(root).resolve()
        files = _rlm_collect_files_multi(root, ["*.py", "*.js", "*.jsx", "*.ts", "*.tsx"])
        for path in files[:max_nodes]:
            nodes.append(str(path))
            ext = path.suffix.lower()
            try:
                if ext == ".py":
                    graph = json.loads(rlm_python_import_graph(str(path), root=str(root_path)))
                    for dep in graph.get("data", {}).get("local_dependencies", []):
                        edges.append({"from": str(path), "to": dep, "kind": "imports"})
                else:
                    for dep in rlm_map_dependencies(str(path)) if isinstance(rlm_map_dependencies(str(path)), list) else []:
                        edges.append({"from": str(path), "to": dep, "kind": "imports"})
            except Exception:
                continue
        grouped: dict[str, dict[str, Any]] = {}
        for edge in edges:
            parent = Path(edge["from"]).parent.name or "."
            grouped.setdefault(parent, {"module": parent, "outbound": 0, "targets": set()})
            grouped[parent]["outbound"] += 1
            grouped[parent]["targets"].add(Path(edge["to"]).parent.name or ".")
        modules = []
        for item in grouped.values():
            modules.append({
                "module": item["module"],
                "outbound_edges": item["outbound"],
                "target_modules": sorted(item["targets"]),
            })
        return _rlm_result("project_relationships", data={"nodes": nodes, "edges": edges[:300], "modules": sorted(modules, key=lambda m: m["outbound_edges"], reverse=True)})
    except Exception as e:
        return _rlm_result("project_relationships", ok=False, errors=[str(e)])


def rlm_project_map(root: str = "."):
    try:
        root_path = Path(root).resolve()
        configs = _rlm_config_inventory(root)
        entrypoints = _rlm_detect_entrypoints(root)
        languages = _rlm_detect_languages(root)
        structure = []
        for item in sorted(root_path.iterdir()):
            if item.name.startswith('.') or item.name == '__pycache__':
                continue
            structure.append({
                "name": item.name,
                "type": "directory" if item.is_dir() else "file",
            })
        relationships = json.loads(rlm_project_relationships(root))
        return _rlm_result(
            "project_map",
            data={
                "root": str(root_path),
                "configs": configs,
                "entrypoints": entrypoints,
                "language_counts": languages,
                "top_level": structure,
                "relationships": relationships.get("data", {}),
            },
            warnings=relationships.get("warnings", []),
            errors=relationships.get("errors", []),
            ok=relationships.get("ok", True),
        )
    except Exception as e:
        return _rlm_result("project_map", ok=False, errors=[str(e)])


class _RLMHTMLTextExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.title = ""
        self._in_title = False
        self._chunks: list[str] = []
        self._capture_href = ""
        self._current_link_text: list[str] = []
        self.headings: list[dict[str, Any]] = []
        self.links: list[dict[str, Any]] = []
        self.paragraphs: list[str] = []
        self._current_paragraph: list[str] = []
        self._heading_tag = ""
        self._heading_buffer: list[str] = []

    def handle_starttag(self, tag, attrs):
        tag = tag.lower()
        attrs_dict = dict(attrs)
        if tag == "title":
            self._in_title = True
        elif tag in {"h1", "h2", "h3", "h4", "h5", "h6"}:
            self._heading_tag = tag
            self._heading_buffer = []
        elif tag == "a":
            self._capture_href = attrs_dict.get("href", "")
            self._current_link_text = []
        elif tag in {"p", "li", "article", "section"}:
            self._current_paragraph = []

    def handle_endtag(self, tag):
        tag = tag.lower()
        if tag == "title":
            self._in_title = False
        elif tag == self._heading_tag and self._heading_buffer:
            heading_text = " ".join(self._heading_buffer).strip()
            if heading_text:
                self.headings.append({"level": tag, "text": heading_text[:400]})
            self._heading_tag = ""
            self._heading_buffer = []
        elif tag == "a":
            text = " ".join(self._current_link_text).strip()
            if text or self._capture_href:
                self.links.append({"href": self._capture_href[:800], "text": text[:300]})
            self._capture_href = ""
            self._current_link_text = []
        elif tag in {"p", "li", "article", "section"}:
            text = " ".join(self._current_paragraph).strip()
            if text:
                self.paragraphs.append(text[:1200])
            self._current_paragraph = []

    def handle_data(self, data):
        text = data.strip()
        if not text:
            return
        if self._in_title and not self.title:
            self.title = text[:300]
        self._chunks.append(text)
        if self._heading_tag:
            self._heading_buffer.append(text)
        if self._capture_href:
            self._current_link_text.append(text)
        if self._current_paragraph is not None:
            self._current_paragraph.append(text)

    def get_text(self) -> str:
        text = html.unescape("\n".join(self._chunks))
        lines = [re.sub(r"\s+", " ", line).strip() for line in text.splitlines()]
        return "\n".join(line for line in lines if line)


def _rlm_json_safe(value: Any) -> Any:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Path):
        return {"__kind__": "path", "value": str(value)}
    if isinstance(value, dict):
        return {str(k): _rlm_json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [_rlm_json_safe(v) for v in value]
    return {"__kind__": "repr", "type": type(value).__name__, "repr": repr(value)[:1000]}


def _rlm_json_restore(value: Any) -> Any:
    if isinstance(value, list):
        return [_rlm_json_restore(v) for v in value]
    if isinstance(value, dict):
        kind = value.get("__kind__")
        if kind == "path":
            return Path(value.get("value", ""))
        if kind == "repr":
            return value
        return {k: _rlm_json_restore(v) for k, v in value.items()}
    return value


def _rlm_notebook_sessions() -> dict[str, Any]:
    if not NOTEBOOK_SESSION_FILE.exists():
        return {}
    try:
        data = _rlm_load_json_file(NOTEBOOK_SESSION_FILE)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _rlm_save_notebook_sessions(data: dict[str, Any]):
    _rlm_save_json_file(NOTEBOOK_SESSION_FILE, data)


def _rlm_notebook_session_key(path: Path) -> str:
    return str(path.resolve())


def _rlm_get_notebook_session(path: Path) -> dict[str, Any]:
    sessions = _rlm_notebook_sessions()
    return dict(sessions.get(_rlm_notebook_session_key(path), {}))


def _rlm_set_notebook_session(path: Path, session: dict[str, Any]):
    sessions = _rlm_notebook_sessions()
    sessions[_rlm_notebook_session_key(path)] = session
    _rlm_save_notebook_sessions(sessions)


def _rlm_clear_notebook_session(path: Path):
    sessions = _rlm_notebook_sessions()
    sessions.pop(_rlm_notebook_session_key(path), None)
    _rlm_save_notebook_sessions(sessions)


def _rlm_load_json_file(path: Path) -> Any:
    return json.loads(path.read_text(encoding='utf-8'))


def _rlm_save_json_file(path: Path, data: Any):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding='utf-8')


def _rlm_notebook_source_text(cell: dict[str, Any]) -> str:
    source = cell.get("source", "")
    if isinstance(source, list):
        return "".join(source)
    return str(source or "")


def _rlm_notebook_set_source(cell: dict[str, Any], source: str):
    if source and not source.endswith("\n"):
        source = source + "\n"
    cell["source"] = source.splitlines(keepends=True)


def _rlm_load_notebook(filepath: str) -> tuple[Path | None, dict[str, Any] | None, str | None]:
    path = Path(filepath)
    if not path.exists():
        return None, None, f"File not found: {filepath}"
    try:
        data = _rlm_load_json_file(path)
        if not isinstance(data, dict) or "cells" not in data:
            return None, None, f"Invalid notebook structure in {filepath}"
        return path, data, None
    except Exception as e:
        return None, None, str(e)


def _rlm_notebook_language(nb: dict[str, Any]) -> str:
    metadata = nb.get("metadata", {}) if isinstance(nb, dict) else {}
    kernelspec = metadata.get("kernelspec", {}) if isinstance(metadata, dict) else {}
    language_info = metadata.get("language_info", {}) if isinstance(metadata, dict) else {}
    return str(language_info.get("name") or kernelspec.get("language") or "python")


def _rlm_execute_notebook_cell(source: str, env: dict[str, Any]) -> tuple[list[dict[str, Any]], str | None]:
    stdout_buf = io.StringIO()
    stderr_buf = io.StringIO()
    outputs: list[dict[str, Any]] = []
    error_text = None
    try:
        compiled: Any = source
        tree = ast.parse(source, filename="<notebook-cell>", mode="exec")
        last_expr_value = None
        if tree.body and isinstance(tree.body[-1], ast.Expr):
            last_expr = tree.body[-1].value
            tree.body = tree.body[:-1]
            compiled = compile(tree, filename="<notebook-cell>", mode="exec")
            expr_compiled = compile(ast.Expression(last_expr), filename="<notebook-cell>", mode="eval")
        else:
            compiled = compile(tree, filename="<notebook-cell>", mode="exec")
            expr_compiled = None
        with redirect_stdout(stdout_buf), redirect_stderr(stderr_buf):
            exec(compiled, env, env)
            if expr_compiled is not None:
                last_expr_value = eval(expr_compiled, env, env)
        if stdout_buf.getvalue():
            outputs.append({"output_type": "stream", "name": "stdout", "text": stdout_buf.getvalue().splitlines(keepends=True)})
        if stderr_buf.getvalue():
            outputs.append({"output_type": "stream", "name": "stderr", "text": stderr_buf.getvalue().splitlines(keepends=True)})
        if expr_compiled is not None and last_expr_value is not None:
            outputs.append({
                "output_type": "execute_result",
                "data": {"text/plain": repr(last_expr_value)},
                "metadata": {},
                "execution_count": env.get("_execution_count", 1),
            })
    except Exception:
        error_text = traceback.format_exc()
        outputs.append({
            "output_type": "error",
            "ename": "ExecutionError",
            "evalue": error_text.splitlines()[-1] if error_text else "ExecutionError",
            "traceback": error_text.splitlines(),
        })
    return outputs, error_text


def rlm_notebook_summary(filepath: str):
    path, nb, error = _rlm_load_notebook(filepath)
    if error:
        return _rlm_result("notebook_summary", ok=False, errors=[error])
    session = _rlm_get_notebook_session(path)
    cells = []
    for index, cell in enumerate(nb.get("cells", [])):
        source = _rlm_notebook_source_text(cell)
        outputs = cell.get("outputs", []) if isinstance(cell, dict) else []
        cells.append({
            "index": index,
            "cell_type": cell.get("cell_type", "unknown"),
            "language": cell.get("metadata", {}).get("language", _rlm_notebook_language(nb)),
            "execution_count": cell.get("execution_count"),
            "source_preview": source[:300],
            "line_count": len(source.splitlines()),
            "output_count": len(outputs),
            "output_types": [output.get("output_type", "unknown") for output in outputs if isinstance(output, dict)],
        })
    return _rlm_result(
        "notebook_summary",
        data={
            "file": str(path),
            "notebook_format": nb.get("nbformat"),
            "notebook_minor": nb.get("nbformat_minor"),
            "language": _rlm_notebook_language(nb),
            "cell_count": len(cells),
            "cells": cells,
            "session": {
                "session_id": session.get("session_id", ""),
                "execution_count": session.get("execution_count", 0),
                "last_run": session.get("last_run", ""),
                "persistent": bool(session),
            },
        },
    )


def rlm_notebook_edit_cell(filepath: str, index: int, source: str = "", cell_type: str = "code", operation: str = "replace"):
    path, nb, error = _rlm_load_notebook(filepath)
    if error:
        return _rlm_result("notebook_edit_cell", ok=False, errors=[error])
    cells = list(nb.get("cells", []))
    idx = int(index)
    op = str(operation or "replace").lower()
    if op == "delete":
        if idx < 0 or idx >= len(cells):
            return _rlm_result("notebook_edit_cell", ok=False, errors=[f"Cell index out of range: {idx}"])
        removed = cells.pop(idx)
        nb["cells"] = cells
        _rlm_save_json_file(path, nb)
        return _rlm_result("notebook_edit_cell", data={"file": str(path), "operation": op, "index": idx, "removed_type": removed.get("cell_type", "unknown")})
    new_cell = {
        "cell_type": cell_type,
        "metadata": {},
        "source": [],
    }
    if cell_type == "code":
        new_cell["execution_count"] = None
        new_cell["outputs"] = []
    _rlm_notebook_set_source(new_cell, source)
    if op == "replace":
        if idx < 0 or idx >= len(cells):
            return _rlm_result("notebook_edit_cell", ok=False, errors=[f"Cell index out of range: {idx}"])
        existing = cells[idx]
        new_cell["metadata"] = existing.get("metadata", {}) if isinstance(existing, dict) else {}
        if new_cell["cell_type"] == "code":
            new_cell["outputs"] = existing.get("outputs", []) if isinstance(existing, dict) else []
            new_cell["execution_count"] = existing.get("execution_count") if isinstance(existing, dict) else None
        cells[idx] = new_cell
    elif op == "insert_before":
        idx = max(0, idx)
        cells.insert(idx, new_cell)
    elif op == "insert_after":
        idx = min(len(cells), idx + 1)
        cells.insert(idx, new_cell)
    else:
        return _rlm_result("notebook_edit_cell", ok=False, errors=[f"Unsupported operation: {operation}"])
    nb["cells"] = cells
    _rlm_save_json_file(path, nb)
    return _rlm_result("notebook_edit_cell", data={"file": str(path), "operation": op, "index": idx, "cell_type": new_cell["cell_type"]})


def rlm_notebook_run(filepath: str, cell_index: int | None = None, persist_output: bool = True, persist_session: bool = True, reset_session: bool = False):
    path, nb, error = _rlm_load_notebook(filepath)
    if error:
        return _rlm_result("notebook_run", ok=False, errors=[error])
    language = _rlm_notebook_language(nb)
    if language.lower() != "python":
        return _rlm_result("notebook_run", ok=False, errors=[f"Unsupported notebook language: {language}"])
    cells = list(nb.get("cells", []))
    target = None if cell_index is None else int(cell_index)
    if target is not None and (target < 0 or target >= len(cells)):
        return _rlm_result("notebook_run", ok=False, errors=[f"Cell index out of range: {target}"])
    session = {} if reset_session else _rlm_get_notebook_session(path)
    env: dict[str, Any] = {"__name__": "__main__"}
    if session.get("globals"):
        restored = _rlm_json_restore(session.get("globals", {}))
        if isinstance(restored, dict):
            env.update(restored)
    executed = []
    failed = False
    exec_count = int(session.get("execution_count", 0) or 0) + 1
    for index, cell in enumerate(cells):
        if cell.get("cell_type") != "code":
            continue
        if target is not None and index > target:
            break
        source = _rlm_notebook_source_text(cell)
        env["_execution_count"] = exec_count
        outputs, error_text = _rlm_execute_notebook_cell(source, env)
        cell["outputs"] = outputs if persist_output else []
        cell["execution_count"] = exec_count
        executed.append({
            "index": index,
            "execution_count": exec_count,
            "output_count": len(outputs),
            "error": bool(error_text),
        })
        exec_count += 1
        if error_text:
            failed = True
            break
        if target is not None and index == target:
            break
    if persist_output:
        nb["cells"] = cells
        _rlm_save_json_file(path, nb)
    session_id = session.get("session_id") or str(uuid.uuid4())[:12]
    session_summary = {
        "session_id": session_id,
        "execution_count": exec_count - 1,
        "last_run": datetime.now().isoformat(),
        "globals": _rlm_json_safe({
            k: v for k, v in env.items()
            if not k.startswith("__") and k != "_execution_count" and not callable(v) and not isinstance(v, type(sys))
        }),
        "last_target_cell": target,
    }
    if persist_session:
        _rlm_set_notebook_session(path, session_summary)
    return _rlm_result(
        "notebook_run",
        ok=not failed,
        data={
            "file": str(path),
            "language": language,
            "executed_cells": executed,
            "target_cell": target,
            "persist_output": bool(persist_output),
            "persist_session": bool(persist_session),
            "session": {
                "session_id": session_id,
                "execution_count": session_summary["execution_count"],
                "last_run": session_summary["last_run"],
            },
        },
        errors=["Notebook execution stopped due to a cell error."] if failed else [],
    )


def rlm_notebook_kernel_info(filepath: str):
    path, nb, error = _rlm_load_notebook(filepath)
    if error:
        return _rlm_result("notebook_kernel_info", ok=False, errors=[error])
    metadata = nb.get("metadata", {}) if isinstance(nb, dict) else {}
    return _rlm_result(
        "notebook_kernel_info",
        data={
            "file": str(path),
            "kernelspec": metadata.get("kernelspec", {}),
            "language_info": metadata.get("language_info", {}),
            "session": _rlm_get_notebook_session(path),
            "python_environment": json.loads(rlm_inspect_python_environment()),
        },
    )


def rlm_notebook_session_status(filepath: str):
    path, _, error = _rlm_load_notebook(filepath)
    if error:
        return _rlm_result("notebook_session_status", ok=False, errors=[error])
    session = _rlm_get_notebook_session(path)
    return _rlm_result(
        "notebook_session_status",
        data={
            "file": str(path),
            "session_exists": bool(session),
            "session": {
                "session_id": session.get("session_id", ""),
                "execution_count": session.get("execution_count", 0),
                "last_run": session.get("last_run", ""),
                "globals_preview": sorted(list((session.get("globals") or {}).keys()))[:50] if isinstance(session.get("globals"), dict) else [],
                "last_target_cell": session.get("last_target_cell"),
            },
        },
    )


def rlm_notebook_clear_session(filepath: str):
    path, _, error = _rlm_load_notebook(filepath)
    if error:
        return _rlm_result("notebook_clear_session", ok=False, errors=[error])
    _rlm_clear_notebook_session(path)
    return _rlm_result("notebook_clear_session", data={"file": str(path), "cleared": True})


def rlm_notebook_install_package(filepath: str, package: str, upgrade: bool = False):
    result = json.loads(rlm_list_python_packages(limit=5000))
    before = {item.get("name"): item.get("version") for item in result.get("packages", [])} if result.get("ok") else {}
    cmd = [sys.executable, "-m", "pip", "install", package]
    if upgrade:
        cmd.append("--upgrade")
    try:
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=300, encoding='utf-8', errors='replace')
        after_result = json.loads(rlm_list_python_packages(limit=5000))
        after = {item.get("name"): item.get("version") for item in after_result.get("packages", [])} if after_result.get("ok") else {}
        return _rlm_result(
            "notebook_install_package",
            ok=res.returncode == 0,
            data={
                "file": filepath,
                "package": package,
                "upgrade": bool(upgrade),
                "returncode": res.returncode,
                "before_version": before.get(package),
                "after_version": after.get(package),
                "output": ((res.stdout or "") + ("\n" + res.stderr if res.stderr else ""))[:4000],
            },
            errors=[] if res.returncode == 0 else [res.stderr.strip() or res.stdout.strip() or "pip install failed"],
        )
    except Exception as e:
        return _rlm_result("notebook_install_package", ok=False, errors=[str(e)], data={"file": filepath, "package": package, "upgrade": bool(upgrade)})


def _rlm_db_profiles() -> dict[str, Any]:
    if not DB_PROFILES_FILE.exists():
        return {}
    try:
        data = _rlm_load_json_file(DB_PROFILES_FILE)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _rlm_save_db_profiles(data: dict[str, Any]):
    _rlm_save_json_file(DB_PROFILES_FILE, data)


def rlm_db_save_profile(name: str, database_path: str, kind: str = "sqlite", description: str = ""):
    if not name.strip():
        return _rlm_result("db_save_profile", ok=False, errors=["Profile name is required."])
    if kind != "sqlite":
        return _rlm_result("db_save_profile", ok=False, errors=["Only sqlite profiles are currently supported."])
    path = Path(database_path)
    if not path.exists():
        return _rlm_result("db_save_profile", ok=False, errors=[f"Database file not found: {database_path}"])
    profiles = _rlm_db_profiles()
    profiles[name] = {"kind": kind, "database_path": str(path), "description": description}
    _rlm_save_db_profiles(profiles)
    return _rlm_result("db_save_profile", data={"name": name, "profile": profiles[name]})


def rlm_db_list_profiles():
    profiles = _rlm_db_profiles()
    return _rlm_result("db_list_profiles", data={"profiles": profiles, "count": len(profiles)})


def _rlm_db_resolve(profile_name: str = "", database_path: str = "") -> tuple[Path | None, dict[str, Any] | None, str | None]:
    if database_path:
        path = Path(database_path)
        if not path.exists():
            return None, None, f"Database file not found: {database_path}"
        return path, {"kind": "sqlite", "database_path": str(path)}, None
    profiles = _rlm_db_profiles()
    if not profile_name:
        return None, None, "Either profile_name or database_path is required."
    profile = profiles.get(profile_name)
    if not profile:
        return None, None, f"Database profile not found: {profile_name}"
    path = Path(profile.get("database_path", ""))
    if not path.exists():
        return None, profile, f"Database file not found: {path}"
    return path, profile, None


def _rlm_sqlite_connect_readonly(path: Path) -> sqlite3.Connection:
    return sqlite3.connect(f"file:{path}?mode=ro", uri=True)


def rlm_db_schema(profile_name: str = "", database_path: str = ""):
    path, profile, error = _rlm_db_resolve(profile_name=profile_name, database_path=database_path)
    if error:
        return _rlm_result("db_schema", ok=False, errors=[error])
    try:
        conn = _rlm_sqlite_connect_readonly(path)
        conn.row_factory = sqlite3.Row
        objects = []
        tables = []
        with conn:
            rows = conn.execute("SELECT type, name, tbl_name, sql FROM sqlite_master WHERE name NOT LIKE 'sqlite_%' ORDER BY type, name").fetchall()
            for row in rows:
                record = dict(row)
                if record.get("type") == "table":
                    columns = [dict(col) for col in conn.execute(f"PRAGMA table_info('{record['name']}')").fetchall()]
                    tables.append({"name": record["name"], "columns": columns})
                objects.append(record)
        conn.close()
        return _rlm_result("db_schema", data={"database_path": str(path), "profile": profile, "objects": objects, "tables": tables})
    except Exception as e:
        return _rlm_result("db_schema", ok=False, errors=[str(e)], data={"database_path": str(path), "profile": profile})


def _rlm_is_safe_readonly_query(query: str) -> tuple[bool, str]:
    stripped = (query or "").strip().rstrip(';')
    if not stripped:
        return False, "Query is required."
    lowered = stripped.lower()
    dangerous = re.search(r"\b(insert|update|delete|drop|alter|create|replace|truncate|attach|detach|vacuum|reindex|begin|commit|rollback|pragma\s+\w+\s*=)\b", lowered)
    if dangerous:
        return False, f"Read-only database tool rejected potentially mutating SQL near '{dangerous.group(1)}'."
    if not re.match(r"^(select|with|pragma|explain)\b", lowered):
        return False, "Only read-only SELECT/WITH/PRAGMA/EXPLAIN queries are allowed."
    return True, "allowed"


def rlm_db_query(query: str, profile_name: str = "", database_path: str = "", limit: int = 200):
    path, profile, error = _rlm_db_resolve(profile_name=profile_name, database_path=database_path)
    if error:
        return _rlm_result("db_query", ok=False, errors=[error])
    allowed, reason = _rlm_is_safe_readonly_query(query)
    if not allowed:
        return _rlm_result("db_query", ok=False, errors=[reason], data={"database_path": str(path), "profile": profile})
    try:
        conn = _rlm_sqlite_connect_readonly(path)
        conn.row_factory = sqlite3.Row
        with conn:
            cursor = conn.execute(query)
            rows = cursor.fetchmany(max(1, int(limit)))
            columns = [item[0] for item in (cursor.description or [])]
            data_rows = [dict(row) for row in rows]
        conn.close()
        return _rlm_result("db_query", data={"database_path": str(path), "profile": profile, "columns": columns, "rows": data_rows, "row_count": len(data_rows), "limit": int(limit)})
    except Exception as e:
        return _rlm_result("db_query", ok=False, errors=[str(e)], data={"database_path": str(path), "profile": profile})


def rlm_db_migration_status(root: str = "."):
    root_path = Path(root)
    migration_dirs = []
    migration_files = []
    for candidate in ["migrations", "alembic", "db/migrations", "prisma/migrations"]:
        path = root_path / candidate
        if path.exists():
            migration_dirs.append(str(path))
            for file in path.rglob("*"):
                if file.is_file():
                    migration_files.append(str(file))
    database_files = [str(path) for path in _rlm_collect_files_multi(root, ["*.db", "*.sqlite", "*.sqlite3"])[:20]]
    applied = []
    for db_file in database_files[:5]:
        try:
            conn = _rlm_sqlite_connect_readonly(Path(db_file))
            conn.row_factory = sqlite3.Row
            tables = {row[0] for row in conn.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()}
            db_status = {"database_path": db_file, "tables": sorted(tables)}
            if "alembic_version" in tables:
                db_status["alembic_version"] = [dict(row) for row in conn.execute("SELECT * FROM alembic_version").fetchall()]
            if "django_migrations" in tables:
                db_status["django_migrations_count"] = conn.execute("SELECT COUNT(*) FROM django_migrations").fetchone()[0]
            applied.append(db_status)
            conn.close()
        except Exception:
            continue
    return _rlm_result("db_migration_status", data={"migration_dirs": migration_dirs, "migration_files": migration_files[:200], "databases": database_files, "applied": applied})


def _rlm_fetch_url(url: str, timeout: int = 20) -> tuple[bool, dict[str, Any]]:
    try:
        headers = dict(COMMON_HEADERS)
        headers["User-Agent"] = COMMON_HEADERS.get("User-Agent", "FlexiBot/1.0")
        req = urllib.request.Request(url, headers=headers, method="GET")
        with urllib.request.urlopen(req, timeout=timeout) as res:
            raw = res.read()
            content_type = res.headers.get("Content-Type", "")
            charset = res.headers.get_content_charset() or "utf-8"
            text = raw.decode(charset, errors='replace')
            extractor = _RLMHTMLTextExtractor()
            extractor.feed(text)
            return True, {
                "url": url,
                "final_url": res.geturl(),
                "status": getattr(res, "status", 200),
                "content_type": content_type,
                "title": extractor.title,
                "text": extractor.get_text(),
                "headings": extractor.headings[:50],
                "links": extractor.links[:100],
                "paragraphs": extractor.paragraphs[:100],
                "html": text,
            }
    except Exception as e:
        return False, {"url": url, "error": str(e)}


def rlm_fetch_webpage(url: str, timeout: int = 20, max_chars: int = 12000):
    ok, payload = _rlm_fetch_url(url, timeout=timeout)
    if not ok:
        return _rlm_result("fetch_webpage", ok=False, errors=[payload.get("error", "Fetch failed")], data={"url": url})
    return _rlm_result(
        "fetch_webpage",
        data={
            "url": payload["url"],
            "final_url": payload["final_url"],
            "status": payload["status"],
            "content_type": payload["content_type"],
            "title": payload["title"],
            "text": payload["text"][:max_chars],
            "headings": payload.get("headings", [])[:20],
        },
    )


def rlm_extract_web_structure(url: str, timeout: int = 20, max_items: int = 20):
    ok, payload = _rlm_fetch_url(url, timeout=timeout)
    if not ok:
        return _rlm_result("extract_web_structure", ok=False, errors=[payload.get("error", "Fetch failed")], data={"url": url})
    return _rlm_result(
        "extract_web_structure",
        data={
            "url": url,
            "title": payload.get("title", ""),
            "headings": payload.get("headings", [])[:max_items],
            "links": payload.get("links", [])[:max_items],
            "paragraphs": payload.get("paragraphs", [])[:max_items],
        },
    )


def rlm_extract_doc_section(url: str, query: str, timeout: int = 20, max_matches: int = 5):
    ok, payload = _rlm_fetch_url(url, timeout=timeout)
    if not ok:
        return _rlm_result("extract_doc_section", ok=False, errors=[payload.get("error", "Fetch failed")], data={"url": url, "query": query})
    lines = payload.get("text", "").splitlines()
    matches = []
    lowered_query = (query or "").lower().strip()
    for idx, line in enumerate(lines):
        if lowered_query and lowered_query not in line.lower():
            continue
        start = max(0, idx - 2)
        end = min(len(lines), idx + 3)
        matches.append({"line": idx + 1, "excerpt": "\n".join(lines[start:end])[:1200]})
        if len(matches) >= max_matches:
            break
    return _rlm_result("extract_doc_section", data={"url": url, "query": query, "title": payload.get("title", ""), "matches": matches}, warnings=[] if matches else [f"No matches found for '{query}'."])


def rlm_summarize_web_reference(url: str, timeout: int = 20, max_points: int = 8):
    ok, payload = _rlm_fetch_url(url, timeout=timeout)
    if not ok:
        return _rlm_result("summarize_web_reference", ok=False, errors=[payload.get("error", "Fetch failed")], data={"url": url})
    lines = [line for line in payload.get("text", "").splitlines() if len(line.strip()) > 20]
    bullets = []
    for line in lines[:max_points]:
        bullets.append(line[:220])
    return _rlm_result(
        "summarize_web_reference",
        data={
            "url": url,
            "title": payload.get("title", ""),
            "summary_points": bullets,
            "preview": "\n".join(lines[:12])[:2000],
        },
    )


def _rlm_query_terms(query: str) -> list[str]:
    return [term for term in re.findall(r"[A-Za-z0-9_]{3,}", (query or "").lower()) if term]


def _rlm_score_text_relevance(text: str, query_terms: list[str]) -> int:
    lowered = (text or "").lower()
    score = 0
    for term in query_terms:
        if term in lowered:
            score += lowered.count(term)
    return score


def rlm_research_web(query: str, urls: list[str] | None = None, timeout: int = 20, max_sources: int = 5):
    query_terms = _rlm_query_terms(query)
    candidate_urls = [url for url in (urls or []) if url][:max_sources]
    warnings = []
    if not candidate_urls:
        encoded = urllib.parse.quote_plus(query)
        search_url = f"https://duckduckgo.com/html/?q={encoded}"
        ok, payload = _rlm_fetch_url(search_url, timeout=timeout)
        if ok:
            hrefs = []
            for link in payload.get("links", []):
                href = str(link.get("href", ""))
                if href.startswith("http") and href not in hrefs:
                    hrefs.append(href)
                if len(hrefs) >= max_sources:
                    break
            candidate_urls = hrefs
        else:
            warnings.append(payload.get("error", "Search fetch failed"))
    findings = []
    for url in candidate_urls[:max_sources]:
        ok, payload = _rlm_fetch_url(url, timeout=timeout)
        if not ok:
            warnings.append(f"{url}: {payload.get('error', 'Fetch failed')}")
            continue
        paragraphs = payload.get("paragraphs", []) or payload.get("text", "").splitlines()
        ranked = []
        for paragraph in paragraphs:
            score = _rlm_score_text_relevance(paragraph, query_terms)
            if score > 0:
                ranked.append((score, paragraph[:1200]))
        ranked.sort(key=lambda item: item[0], reverse=True)
        findings.append({
            "url": url,
            "title": payload.get("title", ""),
            "score": sum(item[0] for item in ranked[:3]),
            "highlights": [item[1] for item in ranked[:3]],
        })
    findings.sort(key=lambda item: item.get("score", 0), reverse=True)
    summary_points = []
    for finding in findings[:max_sources]:
        if finding.get("highlights"):
            summary_points.append(f"{finding.get('title') or finding.get('url')}: {finding['highlights'][0][:220]}")
    return _rlm_result(
        "research_web",
        data={
            "query": query,
            "sources": findings[:max_sources],
            "summary_points": summary_points,
            "source_count": len(findings),
        },
        warnings=warnings,
    )


def rlm_git_review_summary(repo_path: str = ".", src: str = "HEAD", dst: str = ""):
    changed = json.loads(rlm_git_changed_files(repo_path=repo_path, include_untracked=True))
    diff = json.loads(rlm_git_diff_analysis(repo_path=repo_path, src=src, dst=dst))
    draft = json.loads(rlm_git_commit_message_draft(repo_path=repo_path, src=src, dst=dst))
    if not changed.get("ok"):
        return _rlm_result("git_review_summary", ok=False, errors=changed.get("errors", []), warnings=changed.get("warnings", []))
    files = diff.get("data", {}).get("files", []) if diff.get("ok") else []
    hotspots = sorted(files, key=lambda item: item.get("additions", 0) + item.get("deletions", 0), reverse=True)[:5]
    risk_flags = []
    for item in hotspots:
        path = item.get("path", "")
        total = item.get("additions", 0) + item.get("deletions", 0)
        if any(seg in path.lower() for seg in ["auth", "security", "migration", "config", "policy"]):
            risk_flags.append({"path": path, "reason": "sensitive filename pattern"})
        if total >= 200:
            risk_flags.append({"path": path, "reason": f"large diff ({total} lines changed)"})
    checklist = [
        "Verify tests cover the highest-change files.",
        "Review configuration, policy, and migration-related diffs carefully.",
        "Confirm added files are intentional and correctly placed.",
        "Check whether large diffs should be split into smaller commits.",
    ]
    return _rlm_result(
        "git_review_summary",
        data={
            "repo": repo_path,
            "changed_counts": changed.get("data", {}).get("counts", {}),
            "hotspots": hotspots,
            "risk_flags": risk_flags,
            "commit_draft": draft.get("data", {}),
            "checklist": checklist,
        },
        warnings=changed.get("warnings", []) + diff.get("warnings", []) + draft.get("warnings", []),
        errors=diff.get("errors", []) if not diff.get("ok") else [],
    )

def rlm_git_diff_summary(repo_path: str = ".", src: str = "HEAD", dst: str = ""):
    """Returns a high-level summary of uncommitted changes or branch diffs."""
    try:
        cmd = f"git -C {repo_path} diff --stat {src} {dst}"
        res = subprocess.check_output(cmd, shell=True, text=True, stderr=subprocess.STDOUT)
        return res if res.strip() else "No changes detected."
    except Exception as e:
        return f"Git error: {e}"

def rlm_to_clipboard(text: str):
    """Copies text to the system clipboard."""
    try:
        system = platform.system()
        if system == 'Windows':
            process = subprocess.Popen(['clip'], stdin=subprocess.PIPE, text=True)
            process.communicate(input=text)
        elif system == 'Darwin':
            process = subprocess.Popen(['pbcopy'], stdin=subprocess.PIPE, text=True)
            process.communicate(input=text)
        else: # Linux
            # Try xclip then xsel
            try:
                process = subprocess.Popen(['xclip', '-selection', 'clipboard'], stdin=subprocess.PIPE, text=True)
                process.communicate(input=text)
            except FileNotFoundError:
                process = subprocess.Popen(['xsel', '--clipboard', '--input'], stdin=subprocess.PIPE, text=True)
                process.communicate(input=text)
        return "✓ Successfully copied to clipboard."
    except Exception as e:
        return f"Clipboard error: {e}. Check if xclip/xsel is installed on Linux."

def rlm_from_clipboard():
    """Returns the current content of the system clipboard."""
    try:
        system = platform.system()
        if system == 'Windows':
            # Using PowerShell as a native fallback for clipboard retrieval
            return subprocess.check_output(['powershell', '-Command', 'Get-Clipboard'], text=True).strip()
        elif system == 'Darwin':
            return subprocess.check_output(['pbpaste'], text=True).strip()
        else: # Linux
            try:
                return subprocess.check_output(['xclip', '-selection', 'clipboard', '-o'], text=True).strip()
            except FileNotFoundError:
                return subprocess.check_output(['xsel', '--clipboard', '--output'], text=True).strip()
    except Exception as e:
        return f"Clipboard error: {e}. Check if xclip/xsel is installed on Linux."

# --- VISUAL DIFF LOGGING ---
class DiffLogger:
    def __init__(self, log_path: Path):
        self.log_path = log_path
        if not self.log_path.exists():
            self._write_header()

    def _write_header(self):
        header = "# FlexiBot Evolution Log\n\nTrack the logical state changes and recursive turns.\n\n---\n"
        self.log_path.write_text(header, encoding="utf-8")

    def _summarize_thought(self, thought: str) -> str:
        # If the thought is extremely long or contains large code/tool sections,
        # collapse them so the log stays readable. We remove the body of <bash>
        # and <python> tags, leaving only a placeholder, and truncate overall
        # length if necessary.
        # collapse code blocks first
        def collapse_tag(tag: str, text: str) -> str:
            pattern = re.compile(rf"<{tag}>(.*?)</{tag}>", re.S)
            def repl(m):
                content = m.group(1)
                if len(content) > 100:
                    return f"<{tag}>…[{len(content)} chars]…</{tag}>"
                return m.group(0)
            return pattern.sub(repl, text)

        short = collapse_tag('bash', thought)
        short = collapse_tag('python', short)
        # truncate overall if still huge
        MAX = 1000
        if len(short) > MAX:
            return short[:400] + "\n... [TRUNCATED] ...\n" + short[-400:]
        return short

    def log_user(self, user_text: str):
        """Record a user input event in the evolution log with metadata."""
        try:
            timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
            entry = f"\n## User Input - {timestamp}\n**Meta:** user_prompt:true\n> {user_text}\n---\n"
            with self.log_path.open("a", encoding="utf-8") as f:
                f.write(entry)
        except Exception:
            pass

    def log_turn(self, turn_num: int, thought: str, diff_summary: str, tools: List[str], duration: float | None = None, meta: List[str] | None = None):
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        tool_list = ", ".join(tools) if tools else "None"
        try:
            safe_thought = self._summarize_thought(thought)
            dur_line = f"- **Duration:** {duration:.2f}s\n" if duration is not None else ""
            meta_line = f"**Meta:** {', '.join(meta)}\n" if meta else ""
            entry = (
                f"\n## Turn {turn_num} - {timestamp}\n"
                f"{meta_line}"
                f"**Tools:** `{tool_list}`\n"
                f"{dur_line}"
                f"### Thought\n> {safe_thought}\n"
                f"### State\n```yaml\n{diff_summary}\n```\n---\n"
            )
            with self.log_path.open("a", encoding="utf-8") as f: f.write(entry)
        except Exception as e:
            print(f"Warning: Logging failed: {e}")

    def log_summary_event(self, tokens_before: int, tokens_after: int):
        entry = f"\n## 📉 CONTEXT COMPRESSION EVENT\n- **Tokens Before:** {tokens_before}\n- **Tokens After:** {tokens_after}\n- **Ratio:** {((tokens_before-tokens_after)/tokens_before)*100:.1f}% reduction\n---\n"
        with self.log_path.open("a", encoding="utf-8") as f: f.write(entry)

# --- NEXT-GEN ASYNC STATE MANAGEMENT ---
@dataclass
class MemoryEntry:
    id: str
    content: str
    tags: List[str]
    timestamp: float

class AgentState:
    """
    SQLite-backed agent state with explicit APIs for history, memory, runtime
    settings, background processes, and Python globals.

    A compatibility `data` snapshot remains available for older code paths, but
    new code should prefer the explicit methods and properties on this class.
    """

    WRITE_BATCH_MAX = 64
    WRITE_BATCH_WAIT_SECONDS = 0.20
    DB_BUSY_TIMEOUT_MS = 5000

    def __init__(self, state_file: Path, globals_file: Path, snapshot_dir: Path, max_snapshots: int = 5):
        self.state_file = state_file
        self.db_path = state_file.parent / "brain.db"
        self.globals_file = globals_file
        self.snapshot_dir = snapshot_dir
        self.max_snapshots = max_snapshots
        
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.globals_file.parent.mkdir(parents=True, exist_ok=True)
        self.snapshot_dir.mkdir(parents=True, exist_ok=True)
        SKILLS_DIR.mkdir(parents=True, exist_ok=True)
        
        # Async Machinery
        self._write_queue = queue.Queue()
        self._stop_event = threading.Event()
        self._cache_lock = threading.RLock()
        self._closed = False
        self._db_pragmas_verified = False
        
        # In-memory caches
        self._history_cache: List[Dict] = []
        self._kv_cache: Dict[str, Any] = {}
        self._active_processes: Dict[str, Any] = {}
        self._globals: Dict[str, Any] = {}
        self._runtime_cache: Dict[str, Any] = {
            "total_tokens": 0,
            "compressed_summary": "",
            "safety_always_allow": False,
        }

        # Initialization
        self._init_db()
        self._hydrate_cache()
        self._load_legacy_globals()
        
        # Start Writer Thread
        self._writer_thread = threading.Thread(target=self._writer_loop, daemon=True, name="MemoryWriter")
        self._writer_thread.start()

    def _connect_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path, timeout=self.DB_BUSY_TIMEOUT_MS / 1000)
        conn.row_factory = sqlite3.Row
        self._apply_pragmas(conn, verify=not self._db_pragmas_verified)
        return conn

    def _apply_pragmas(self, conn: sqlite3.Connection, verify: bool = False):
        conn.execute(f"PRAGMA busy_timeout={self.DB_BUSY_TIMEOUT_MS}")
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA temp_store=MEMORY")
        conn.execute("PRAGMA foreign_keys=ON")
        if verify:
            try:
                journal_mode = str(conn.execute("PRAGMA journal_mode").fetchone()[0]).lower()
                busy_timeout = int(conn.execute("PRAGMA busy_timeout").fetchone()[0])
                if journal_mode != "wal":
                    raise RuntimeError(f"SQLite journal_mode verification failed: expected wal, got {journal_mode}")
                if busy_timeout < self.DB_BUSY_TIMEOUT_MS:
                    raise RuntimeError(
                        f"SQLite busy_timeout verification failed: expected >= {self.DB_BUSY_TIMEOUT_MS}, got {busy_timeout}"
                    )
                self._db_pragmas_verified = True
            except Exception as e:
                ErrorHandler.log(e, severity=ErrorSeverity.CRITICAL, context="AgentState._apply_pragmas", code=ErrorCode.IO_ERROR)

    def export_state(self) -> dict[str, Any]:
        with self._cache_lock:
            return {
                "history": copy.deepcopy(self._history_cache),
                "memory": copy.deepcopy(self._kv_cache),
                "structured_memory": copy.deepcopy(self._kv_cache),
                "active_processes": copy.deepcopy(self._active_processes),
                "total_tokens": self._runtime_cache.get("total_tokens", 0),
                "compressed_summary": self._runtime_cache.get("compressed_summary", ""),
                "safety_always_allow": self._runtime_cache.get("safety_always_allow", False),
            }

    @property
    def data(self):
        """Deprecated compatibility snapshot for older code paths."""
        return self.export_state()

    @property
    def history(self) -> list[dict]:
        with self._cache_lock:
            return copy.deepcopy(self._history_cache)

    @property
    def memory(self) -> dict[str, Any]:
        with self._cache_lock:
            return copy.deepcopy(self._kv_cache)

    @property
    def structured_memory(self) -> dict[str, Any]:
        return self.memory

    @property
    def active_processes(self) -> dict[str, Any]:
        with self._cache_lock:
            return copy.deepcopy(self._active_processes)

    @property
    def total_tokens(self) -> int:
        return int(self.get_runtime_value("total_tokens", 0) or 0)

    @total_tokens.setter
    def total_tokens(self, value: int):
        self.set_runtime_value("total_tokens", int(value or 0))

    @property
    def compressed_summary(self) -> str:
        return str(self.get_runtime_value("compressed_summary", "") or "")

    @compressed_summary.setter
    def compressed_summary(self, value: str):
        self.set_runtime_value("compressed_summary", str(value or ""))

    @property
    def globals(self):
        with self._cache_lock:
            return copy.deepcopy(self._globals)

    @globals.setter
    def globals(self, value):
        self.replace_globals(value)

    def get_runtime_value(self, key: str, default: Any = None) -> Any:
        with self._cache_lock:
            return copy.deepcopy(self._runtime_cache.get(key, default))

    def set_runtime_value(self, key: str, value: Any, persist: bool = True):
        with self._cache_lock:
            self._runtime_cache[key] = value
        if persist:
            self._enqueue_write("runtime", {"key": key, "value": value})

    def replace_globals(self, value: dict[str, Any] | None, persist: bool = True):
        if value is None:
            value = {}
        if not isinstance(value, dict):
            raise TypeError("AgentState globals must be a dict")
        with self._cache_lock:
            self._globals = copy.deepcopy(value)
        if persist:
            self._queue_globals_snapshot()

    def set_active_process(self, pid: str, info: dict[str, Any], persist: bool = True):
        with self._cache_lock:
            self._active_processes[str(pid)] = copy.deepcopy(info)
        if persist:
            self._queue_active_processes_snapshot()

    def remove_active_process(self, pid: str, persist: bool = True):
        with self._cache_lock:
            self._active_processes.pop(str(pid), None)
        if persist:
            self._queue_active_processes_snapshot()

    def clear_active_processes(self, persist: bool = True):
        with self._cache_lock:
            self._active_processes = {}
        if persist:
            self._queue_active_processes_snapshot()

    def _enqueue_write(self, op: str, payload: dict[str, Any]):
        if self._closed:
            raise RuntimeError("AgentState is closed")
        self._write_queue.put((op, payload))

    def _init_db(self):
        with self._connect_db() as conn:
            c = conn.cursor()
            c.execute('''CREATE TABLE IF NOT EXISTS history 
                         (id INTEGER PRIMARY KEY AUTOINCREMENT, role TEXT, content TEXT, tags TEXT DEFAULT '', timestamp REAL)''')
            c.execute('''CREATE TABLE IF NOT EXISTS knowledge 
                         (key TEXT PRIMARY KEY, value TEXT, tags TEXT, updated_at REAL)''')
            c.execute('''CREATE TABLE IF NOT EXISTS evolution 
                         (id INTEGER PRIMARY KEY AUTOINCREMENT, version TEXT, summary TEXT, diff TEXT, timestamp REAL)''')
            c.execute('''CREATE TABLE IF NOT EXISTS runtime_state
                         (key TEXT PRIMARY KEY, value TEXT, updated_at REAL)''')
            c.execute('''CREATE INDEX IF NOT EXISTS idx_history_timestamp ON history(timestamp)''')
            conn.commit()

    def _encode_json_safe(self, value: Any) -> Any:
        if value is None or isinstance(value, (bool, int, float, str)):
            return value
        if isinstance(value, Path):
            return {"__flexi_serialized__": "path", "value": str(value)}
        if isinstance(value, dict):
            return {str(k): self._encode_json_safe(v) for k, v in value.items()}
        if isinstance(value, (list, tuple, set)):
            return [self._encode_json_safe(v) for v in value]
        return {
            "__flexi_serialized__": "repr",
            "type": type(value).__name__,
            "repr": repr(value)[:1000],
        }

    def _decode_json_safe(self, value: Any) -> Any:
        if isinstance(value, list):
            return [self._decode_json_safe(v) for v in value]
        if isinstance(value, dict):
            marker = value.get("__flexi_serialized__")
            if marker == "path":
                return Path(value.get("value", ""))
            if marker == "repr":
                return value
            return {k: self._decode_json_safe(v) for k, v in value.items()}
        return value

    def _serialize_globals(self, data: dict[str, Any]) -> dict[str, Any]:
        return {str(key): self._encode_json_safe(value) for key, value in data.items()}

    def _deserialize_globals(self, data: dict[str, Any]) -> dict[str, Any]:
        if not isinstance(data, dict):
            return {}
        return {str(key): self._decode_json_safe(value) for key, value in data.items()}

    def _load_legacy_globals(self):
        with self._cache_lock:
            if self._globals:
                return
        if self.globals_file.exists():
            try:
                with open(self.globals_file, "rb") as f:
                    legacy_globals = pickle.load(f)
                if isinstance(legacy_globals, dict):
                    self.replace_globals(legacy_globals, persist=False)
                    self._queue_globals_snapshot()
                    ConsoleOutput.warning("Loaded legacy pickle globals and queued migration to SQLite-backed safe storage.")
            except Exception as e:
                ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="AgentState._load_legacy_globals", code=ErrorCode.IO_ERROR)

    def _hydrate_cache(self):
        try:
            with self._connect_db() as conn:
                c = conn.cursor()

                c.execute("SELECT role, content, tags, timestamp FROM history ORDER BY id ASC")
                self._history_cache = []
                for row in c.fetchall():
                    item = dict(row)
                    tags = item.get("tags") or "[]"
                    try:
                        item["tags"] = json.loads(tags) if isinstance(tags, str) else tags
                    except Exception:
                        item["tags"] = []
                    self._history_cache.append(item)

                c.execute("SELECT key, value FROM knowledge")
                for row in c.fetchall():
                    val = json.loads(row['value'])
                    if row['key'] == "active_processes":
                        self._active_processes = val
                    else:
                        self._kv_cache[row['key']] = val

                c.execute("SELECT key, value FROM runtime_state")
                for row in c.fetchall():
                    value = json.loads(row["value"])
                    if row["key"] == "python_globals":
                        self._globals = self._deserialize_globals(value)
                    else:
                        self._runtime_cache[row["key"]] = value
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.CRITICAL, context="AgentState._hydrate_cache", code=ErrorCode.IO_ERROR)

    def _queue_active_processes_snapshot(self):
        with self._cache_lock:
            proc_copy = copy.deepcopy(self._active_processes)
        self._enqueue_write("kv", {"key": "active_processes", "value": proc_copy})

    def _queue_globals_snapshot(self):
        with self._cache_lock:
            globals_copy = self._serialize_globals(self._globals)
        self._enqueue_write("runtime", {"key": "python_globals", "value": globals_copy})

    def _drain_write_batch(self, first_task):
        batch = [first_task]
        while len(batch) < self.WRITE_BATCH_MAX:
            try:
                batch.append(self._write_queue.get_nowait())
            except queue.Empty:
                break
        return batch

    def _writer_loop(self):
        conn = self._connect_db()
        try:
            while not self._stop_event.is_set() or not self._write_queue.empty():
                try:
                    task = self._write_queue.get(timeout=self.WRITE_BATCH_WAIT_SECONDS)
                except queue.Empty:
                    continue

                if task is None:
                    self._write_queue.task_done()
                    break

                batch = self._drain_write_batch(task)
                history_rows = []
                kv_rows: dict[str, Any] = {}
                evolution_rows = []
                runtime_rows: dict[str, Any] = {}

                try:
                    for op, payload in batch:
                        if op == "history":
                            history_rows.append(
                                (
                                    payload['role'],
                                    payload['content'],
                                    json.dumps(payload.get('tags', [])),
                                    payload['timestamp'],
                                )
                            )
                        elif op == "kv":
                            kv_rows[payload['key']] = payload['value']
                        elif op == "evolution":
                            evolution_rows.append((payload['version'], payload['summary'], payload['diff'], time.time()))
                        elif op == "runtime":
                            runtime_rows[payload['key']] = payload['value']

                    with conn:
                        if history_rows:
                            conn.executemany(
                                "INSERT INTO history (role, content, tags, timestamp) VALUES (?, ?, ?, ?)",
                                history_rows,
                            )
                        if kv_rows:
                            conn.executemany(
                                "INSERT OR REPLACE INTO knowledge (key, value, tags, updated_at) VALUES (?, ?, ?, ?)",
                                [(key, json.dumps(value), '[]', time.time()) for key, value in kv_rows.items()],
                            )
                        if evolution_rows:
                            conn.executemany(
                                "INSERT INTO evolution (version, summary, diff, timestamp) VALUES (?, ?, ?, ?)",
                                evolution_rows,
                            )
                        if runtime_rows:
                            conn.executemany(
                                "INSERT OR REPLACE INTO runtime_state (key, value, updated_at) VALUES (?, ?, ?)",
                                [(key, json.dumps(value), time.time()) for key, value in runtime_rows.items()],
                            )
                except Exception as e:
                    ErrorHandler.log(e, severity=ErrorSeverity.CRITICAL, context="AgentState._writer_loop", code=ErrorCode.IO_ERROR)
                finally:
                    for _ in batch:
                        self._write_queue.task_done()
        finally:
            conn.close()

    def save(self):
        """Compatibility save trigger that queues current mutable snapshots."""
        self._queue_globals_snapshot()
        self._queue_active_processes_snapshot()

    def flush(self):
        """Queue mutable snapshots and block until the writer drains them."""
        self.save()
        self._write_queue.join()

    def join_writer(self, timeout: float | None = None):
        """Wait for the background writer thread to exit."""
        if self._writer_thread.is_alive():
            self._writer_thread.join(timeout=timeout)

    def close(self):
        """Flush pending writes, stop the writer thread, and close the state lifecycle."""
        if self._closed:
            return
        self.flush()
        self._closed = True
        self._stop_event.set()
        self._write_queue.put(None)
        self.join_writer(timeout=5)

    # --- structured history API ------------------------------------------------
    def _sanitize_content(self, text: str) -> str:
        # strip control characters and limit length
        if not isinstance(text, str):
            return str(text)
        cleaned = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]", "", text)
        if len(cleaned) > 2000:
            return cleaned[:2000] + "..."
        return cleaned

    def append_history(self, role: str, content: str, tags: list[str] | None = None):
        """Add an entry to the history cache and legacy archive.

        Tags are arbitrary strings that can later be used to query the history
        (e.g. "plan", "tool:bash", "user_prompt" etc.).
        """
        tags = tags or []
        clean_content = self._sanitize_content(content)
        entry = {
            "id": str(uuid.uuid4()),
            "role": role,
            "content": clean_content,
            "tags": tags,
            "timestamp": time.time()
        }
        with self._cache_lock:
            self._history_cache.append(entry)
        self._enqueue_write("history", entry)
        # legacy archive for backwards compatibility
        try:
            with open(ARCHIVE_FILE, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry) + "\n")
        except Exception:
            pass
        self._rotate_archive_if_needed()

    def query_history(self, *, role: str = None, tag: str = None,
                      regex: str = None, exclude_tags: list[str] | None = None,
                      since: float = None, until: float = None, limit: int = 20) -> list[dict]:
        """Return history entries matching filters; queries DB if dataset is large.

        Supported filters:
        - role: exact match
        - tag: entry.tags contains this tag
        - regex: regex applied to content
        - exclude_tags: list of tags that must NOT appear
        - since/until: timestamp window
        - limit: return at most this many (from newest)
        """
        # if history size is small, filter in-memory for speed
        if len(self._history_cache) < 1000:
            results = list(self._history_cache)
            if role:
                results = [e for e in results if e.get("role") == role]
            if tag:
                results = [e for e in results if tag in e.get("tags", [])]
            if exclude_tags:
                for t in exclude_tags:
                    results = [e for e in results if t not in e.get("tags", [])]
            if since is not None:
                results = [e for e in results if e.get("timestamp", 0) >= since]
            if until is not None:
                results = [e for e in results if e.get("timestamp", 0) <= until]
            if regex:
                pat = re.compile(regex)
                results = [e for e in results if pat.search(e.get("content", ""))]
            return results[-limit:]

        # otherwise run a SQL query for scalability
        query = "SELECT role, content, tags, timestamp FROM history"
        conds = []
        params = []
        if role:
            conds.append("role=?")
            params.append(role)
        if since is not None:
            conds.append("timestamp>=?")
            params.append(since)
        if until is not None:
            conds.append("timestamp<=?")
            params.append(until)
        if tag:
            conds.append("tags LIKE ?")
            params.append(f"%{tag}%")
        if exclude_tags:
            for t in exclude_tags:
                conds.append("tags NOT LIKE ?")
                params.append(f"%{t}%")
        if regex:
            conds.append("content REGEXP ?")
            params.append(regex)
        if conds:
            query += " WHERE " + " AND ".join(conds)
        query += " ORDER BY timestamp DESC LIMIT ?"
        params.append(limit)
        results = []
        try:
            with self._connect_db() as conn:
                # register regexp function
                conn.create_function("REGEXP", 2, lambda pat, val: 1 if re.search(pat, val or "") else 0)
                c = conn.cursor()
                for row in c.execute(query, params):
                    item = dict(row)
                    tags = item.get("tags")
                    try:
                        item["tags"] = json.loads(tags) if isinstance(tags, str) else tags
                    except Exception:
                        item["tags"] = []
                    results.append(item)
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="AgentState.query_history", code=ErrorCode.IO_ERROR)
        return results

    # keep legacy log_event for compatibility
    def log_event(self, role: str, content: str):
        # simply append without tags
        self.append_history(role, content)

    def history_count(self) -> int:
        with self._cache_lock:
            return len(self._history_cache)

    def replace_history_cache(self, entries: list[dict]):
        with self._cache_lock:
            self._history_cache = copy.deepcopy(entries)

    def _rotate_archive_if_needed(self):
        """If the archive exceeds the maximum bytes, compress and rotate it.
        The old file is gzipped with a timestamp suffix and a new empty archive is created.
        """
        try:
            if ARCHIVE_FILE.exists() and ARCHIVE_FILE.stat().st_size > ARCHIVE_MAX_BYTES:
                timestamp = time.strftime("%Y%m%d_%H%M%S")
                dest = ARCHIVE_FILE.with_name(f"{ARCHIVE_FILE.name}.{timestamp}.gz")
                # compress
                with open(ARCHIVE_FILE, "rb") as fin, gzip.open(dest, "wb") as fout:
                    shutil.copyfileobj(fin, fout)
                ARCHIVE_FILE.unlink()
                ConsoleOutput.system(f"Archive rotated to {dest.name}")
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="AgentState._rotate_archive_if_needed", code=ErrorCode.IO_ERROR)


    def remember(self, key: str, value: Any):
        with self._cache_lock:
            self._kv_cache[key] = value
        self._enqueue_write("kv", {"key": key, "value": value})

    def recall(self, key: str):
        with self._cache_lock:
            return self._kv_cache.get(key)
            
    def take_snapshot(self, label: str = "auto"):
        # Create a consistent SQLite backup snapshot and rotate old ones.
        try:
            if self.db_path.exists():
                timestamp = int(time.time())
                dest = self.snapshot_dir / f"snapshot_{label}_{timestamp}.db"
                with self._connect_db() as source_conn, sqlite3.connect(dest) as dest_conn:
                    source_conn.backup(dest_conn)
                # maintain only MAX_SNAPSHOTS files
                snaps = sorted(self.snapshot_dir.glob("snapshot_*.db"), key=lambda p: p.stat().st_mtime)
                while len(snaps) > self.max_snapshots:
                    try:
                        snaps[0].unlink()
                    except Exception:
                        pass
                    snaps.pop(0)
        except Exception:
            pass

    def calculate_diff(self, old_data, new_data):
        return "Async State - Diffing disabled"

# --- LLM PROVIDER & SUMMARIZER ---
class OllamaProvider:
    def __init__(self, model="lfm2.5-thinking", host="127.0.0.1", port="11434"):
        self.model = model
        self.url = f"http://{host}:{port}/api/chat"

    @retry_with_backoff(retries=3, backoff_in_seconds=2)
    def chat(self, messages: List[Dict[str, str]]) -> Dict[str, Any]:
        payload = {
            "model": self.model,
            "messages": messages,
            "stream": False,
            "options": {"temperature": 0.1}
        }
        headers = {"Content-Type": "application/json"}
        try:
            req = urllib.request.Request(self.url, data=json.dumps(payload).encode("utf-8"), headers=headers, method="POST")
            with urllib.request.urlopen(req) as res:
                data = json.loads(res.read().decode("utf-8"))
                # Map Ollama response to match standard format
                return {"choices": [{"message": {"content": data.get("message", {}).get("content", "")}}]}
        except Exception as e:
            return {"choices": [{"message": {"content": f"Ollama Error: {e}"}}]}

class CopilotClient:
    def __init__(self):
        self.github_token = self._get_github_token()
        self.token_data = None
        self._ensure_session()

    def _ensure_session(self, force_refresh=False):
        """Ensures we have a valid short-lived Copilot session token."""
        now = time.time()
        if not self.token_data or force_refresh or now > self.token_data.get("expires_at", 0) - 300:
            try:
                self.token_data = self._refresh_token()
            except urllib.error.HTTPError as e:
                if e.code == 401:
                    print(f"{Colors.RED}[Auth] GitHub Token (OAuth) is invalid or expired. Re-authenticating...{Colors.ENDC}")
                    self.github_token = self._authenticate_device_flow()
                    with open(TOKEN_CACHE_FILE, "w") as f: json.dump({"access_token": self.github_token}, f)
                    self.token_data = self._refresh_token()
                else: raise e

    @retry_with_backoff(retries=3, backoff_in_seconds=2)
    def _make_request(self, url, method="GET", headers=None, data=None):
        if headers is None: headers = {}
        encoded_data = None
        if data:
            if headers.get("Content-Type") == "application/json":
                encoded_data = json.dumps(data).encode("utf-8")
            else:
                encoded_data = urllib.parse.urlencode(data).encode("utf-8")
        
        req = urllib.request.Request(url, data=encoded_data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req) as res:
                return res.getcode(), json.loads(res.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read().decode("utf-8"))
        except Exception as e:
            return 500, {"error": str(e)}

    def _authenticate_device_flow(self):
        CLIENT_ID = "Iv1.b507a08c87ecfe98"
        print(f"\n{Colors.YELLOW}[Auth]{Colors.ENDC} Requesting device code from GitHub...")
        status, data = self._make_request("https://github.com/login/device/code", method="POST", 
                                         headers={"Accept": "application/json"}, 
                                         data={"client_id": CLIENT_ID, "scope": "read:user"})
        
        if status != 200: raise Exception(f"Auth failed: {data}")
            
        print(f"\n{Colors.CYAN}{'='*40}{Colors.ENDC}")
        print(f"Please visit: {Colors.BOLD}{Colors.UNDERLINE}{data['verification_uri']}{Colors.ENDC}")
        print(f"Enter code:   {Colors.BOLD}{Colors.GREEN}{data['user_code']}{Colors.ENDC}")
        print(f"{Colors.CYAN}{'='*40}{Colors.ENDC}\n")
        
        print("Waiting for authentication...", end="", flush=True)
        interval = data.get("interval", 5)
        while True:
            time.sleep(interval)
            print(".", end="", flush=True)
            status, token_data = self._make_request("https://github.com/login/oauth/access_token", method="POST", 
                                                   headers={"Accept": "application/json"}, 
                                                   data={"client_id": CLIENT_ID, "device_code": data["device_code"], "grant_type": "urn:ietf:params:oauth:grant-type:device_code"})
            
            if "access_token" in token_data:
                print(f"\n{Colors.GREEN}✓ Authenticated!{Colors.ENDC}")
                return token_data["access_token"]
            
            if token_data.get("error") == "slow_down": interval += 2
            elif token_data.get("error") == "expired_token": raise Exception("Code expired.")

    def _get_github_token(self):
        if os.path.exists(TOKEN_CACHE_FILE):
            with open(TOKEN_CACHE_FILE, "r") as f: return json.load(f).get("access_token")
        
        token = os.environ.get("GITHUB_TOKEN")
        if token: return token
        
        # Trigger interactive flow
        token = self._authenticate_device_flow()
        with open(TOKEN_CACHE_FILE, "w") as f: json.dump({"access_token": token}, f)
        return token

    def _refresh_token(self):
        headers = {**COMMON_HEADERS, "Authorization": f"Bearer {self.github_token}"}
        req = urllib.request.Request(COPILOT_TOKEN_URL, headers=headers)
        with urllib.request.urlopen(req) as res:
            data = json.loads(res.read().decode("utf-8"))
            
            # Robust endpoint parsing
            base_url = DEFAULT_COPILOT_API_BASE_URL
            if "token" in data:
                for part in data["token"].split(";"):
                    if part.startswith("proxy-ep="):
                        base_url = f"https://{part.split('=')[1].replace('https://','').replace('proxy.','api.')}"
            
            # Use expires_at from response, or default to 25 mins
            expires_at = data.get("expires_at", time.time() + 1500)
            return {"token": data["token"], "base_url": base_url, "expires_at": expires_at}

    @retry_with_backoff(retries=3, backoff_in_seconds=1)
    def chat(self, messages: List[Dict[str, str]]) -> Dict[str, Any]:
        try:
            self._ensure_session() # Auto-refresh if expired
            
            url = f"{self.token_data['base_url']}/chat/completions"
            headers = {**COMMON_HEADERS, "Authorization": f"Bearer {self.token_data['token']}", "Content-Type": "application/json"}
            payload = {"model": "gpt-5-mini", "messages": messages, "temperature": 0.1}
            req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"), headers=headers, method="POST")
            with urllib.request.urlopen(req) as res: return json.loads(res.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            if e.code == 401:
                # Session token (JWT) is invalid or expired. Force a refresh and let retry decorator handle the rest.
                print(f"{Colors.RED}[Auth] 401 Unauthorized from completions API. Forcing session refresh...{Colors.ENDC}")
                print(f"{Colors.DIM}Hint: If this persists immediately, verify your system clock is correct.{Colors.ENDC}")
                self._ensure_session(force_refresh=True)
            elif e.code == 413:
                # Request Entity Too Large - likely a context issue despite our truncation
                print(f"{Colors.RED}[API Error] 413 Request Entity Too Large. The context is still too big.{Colors.ENDC}")
            raise e
        except Exception as e:
            print(f"{Colors.RED}[API Error] {e}{Colors.ENDC}")
            raise e

# --- SUBAGENT ARCHITECTURE ---
class SubagentStatus(Enum):
    INIT = "INIT"
    RUNNING = "RUNNING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    TERMINATED = "TERMINATED"

class Subagent:
    def __init__(self, task: str, work_dir: Path, bot, system_prompt: str):
        self.id = str(uuid.uuid4())[:8]
        self.task = task
        self.work_dir = work_dir
        self.bot = bot
        self.system_prompt = system_prompt
        self.status = SubagentStatus.INIT
        self.result = None
        self.logs = []
        self._stop_event = False
        self.must_wait_for_observation = False
        self.last_resp = None
        self.repetition_count = 0

    def log(self, msg: str):
        self.logs.append(f"[{time.strftime('%H:%M:%S')}] {msg}")

    def terminate(self):
        self._stop_event = True
        self.status = SubagentStatus.TERMINATED

    def run(self):
        self.status = SubagentStatus.RUNNING
        self.work_dir.mkdir(parents=True, exist_ok=True)
        
        # Create a simplified but robust context for the subagent
        sub_prompt = self.system_prompt + (
            f"\n\n### SUBAGENT CONTEXT ({self.id}) ###\n"
            f"- **Work Dir**: {self.work_dir}\n"
            f"- **Constraint**: You are an autonomous subagent. "
            f"If the task is already finished or 'nothing to do', output <consensus>DONE: Task verify - already completed or unnecessary.</consensus> immediately.\n"
            f"- **Redundancy**: If a command fails, try an alternative (e.g., if 'psutil' is missing, use 'tasklist').\n"
            f"- **Communication**: You communicate only via tool outputs and <consensus>."
        )

        history = [
            {"role": "system", "content": sub_prompt},
            {"role": "user", "content": f"Task: {self.task}"}
        ]
        
        try:
            for turn in range(24): # Increased from 12 to 24
                if self._stop_event: break
                
                resp = self.bot.client.chat(history)["choices"][0]["message"]["content"]
                
                # Check for repetition
                if resp == self.last_resp and "<ack_observation>" not in resp:
                    self.repetition_count += 1
                    if self.repetition_count >= 3:
                        self.status = SubagentStatus.FAILED
                        self.result = "Loop detected: Subagent repeating same output."
                        return
                else:
                    self.repetition_count = 0
                self.last_resp = resp

                # Await acknowledgement lock
                ack = "<ack_observation>" in resp
                if ack:
                    self.must_wait_for_observation = False

                # Parse Tools
                bash = re.findall(r"<bash>(.*?)</bash>", resp, re.S)
                py = re.findall(r"<python>(.*?)</python>", resp, re.S)
                has_tools = bool(bash or py)

                if "<consensus>" in resp:
                    if self.must_wait_for_observation:
                        history.append({"role": "assistant", "content": resp})
                        history.append({"role": "system", "content": "System Error: Awaiting <ack_observation>. You cannot use <consensus> until you acknowledge the previous observation."})
                        continue
                    
                    if has_tools:
                        obs_prefix = "System Warning: <consensus> ignored because tools were used. Wait for output.\n"
                    else:
                        self.result = re.search(r"<consensus>(.*?)</consensus>", resp, re.S).group(1).strip()
                        self.status = SubagentStatus.COMPLETED
                        try: (self.work_dir / "result.txt").write_text(self.result, encoding="utf-8")
                        except: pass
                        return
                else:
                    obs_prefix = ""
                
                obs = ""
                # Use a combined observation to minimize token usage
                for b in bash: 
                     obs += f"Bash Output:\n{self.bot.run_bash(b)}\n"
                for p in py: 
                     obs += f"Python Output:\n{self.bot.run_python(p)}\n" 
                
                if not bash and not py and not ack:
                    obs = "System Notification: No action detected. Please use <bash>, <python>, <ack_observation> or <consensus>."
                
                if obs:
                    self.must_wait_for_observation = True
                
                history.append({"role": "assistant", "content": resp})
                history_obs = obs_prefix + obs
                history.append({"role": "system", "content": f"Observation: {history_obs if len(history_obs) < 8000 else history_obs[:8000] + '... (truncated)'}"})
            
            if self.status != SubagentStatus.COMPLETED:
                self.status = SubagentStatus.FAILED
                self.result = "Max turns reached without consensus."

        except Exception as e:
            self.status = SubagentStatus.FAILED
            self.result = f"Error during subagent execution: {e}"

        # Final side-effect write
        try:
            if self.result: (self.work_dir / "result.txt").write_text(str(self.result), encoding="utf-8")
        except: pass

class SubagentManager:
    def __init__(self, bot):
        self.bot = bot
        self.agents: Dict[str, Subagent] = {}
        
        # --- DYNAMIC POOL CONFIG ---
        self.queue = queue.PriorityQueue() # (priority, timestamp, agent)
        self.executor = ThreadPoolExecutor(max_workers=24) # Hard system limit
        
        self.agent_registry = {"generic": Subagent}
        self.agent_metadata = {"generic": {"description": "Standard recursive agent", "caps": ["bash", "python", "plan"]}}
        
        self._active_count = 0
        self._pool_lock = threading.Lock()

        # Running tasks registry for deduplication: task_hash -> agent_id
        self.running_tasks: Dict[str, str] = {}
        
        # Scaling State
        self.current_capacity = 4 # Start conservative
        self.min_capacity = 2
        self.max_capacity = 20
        self.scale_up_threshold = 3 # Queue size > 3 triggers scale up
        self.scale_down_timer = 0
        
        # Start Dispatcher
        threading.Thread(target=self._dispatcher, daemon=True).start()

    def register_agent_type(self, name: str, cls_ref: Any, description: str, capabilities: List[str]):
        """Registers a new subagent class type at runtime."""
        self.agent_registry[name] = cls_ref
        self.agent_metadata[name] = {"description": description, "caps": capabilities}
        return f"Registered subagent '{name}'"

    def spawn(self, task: str, work_dir: str = ".", priority: int = 2, agent_type: str = "generic") -> str:
        """Priority: 0=CRITICAL, 1=HIGH, 2=NORMAL, 3=LOW"""
        # Compute a stable task hash to deduplicate similar tasks (task + type + workdir)
        task_key = f"{agent_type}:{task}:{str(Path(work_dir).resolve())}"
        task_hash = hashlib.sha256(task_key.encode('utf-8')).hexdigest()

        with self._pool_lock:
            # If we already have this task in-flight or queued, return the existing agent id
            existing = self.running_tasks.get(task_hash)
            if existing and existing in self.agents:
                existing_status = self.agents[existing].status
                if existing_status in [SubagentStatus.RUNNING, SubagentStatus.INIT]:
                    print(f"[SubagentManager] Duplicate spawn detected for task hash {task_hash}. Returning existing agent {existing}.")
                    return existing

        # Resolve Agent Class
        agent_cls = self.agent_registry.get(agent_type, Subagent)
        
        # Instantiate (Expects standard signature)
        try:
            agent = agent_cls(task, Path(work_dir), self.bot, self.bot.get_system_prompt())
        except Exception as e:
            # Fallback to generic if custom init fails
            print(f"Error instantiating {agent_type}: {e}. Falling back to generic.")
            agent = Subagent(task, Path(work_dir), self.bot, self.bot.get_system_prompt())

        agent._task_hash = task_hash
        self.agents[agent.id] = agent

        # Register as in-flight/queued
        with self._pool_lock:
            self.running_tasks[task_hash] = agent.id

        # Priority Queue: Lower number = Higher priority
        self.queue.put((priority, time.time(), agent))
        return agent.id

    def _dispatcher(self):
        """Background loop to manage dynamic scaling and task dispatch."""
        while True:
            # 1. Dynamic Scaling Logic
            q_size = self.queue.qsize()
            with self._pool_lock:
                # Scale UP
                if q_size > self.scale_up_threshold and self.current_capacity < self.max_capacity:
                    self.current_capacity += 1
                    self.scale_down_timer = 0 # Reset cooldown
                
                # Scale DOWN (if idle for a while)
                elif q_size == 0 and self._active_count < (self.current_capacity // 2):
                    self.scale_down_timer += 1
                    if self.scale_down_timer > 10: # ~10 seconds of idleness
                        self.current_capacity = max(self.min_capacity, self.current_capacity - 1)
                        self.scale_down_timer = 0

            # 2. Dispatch Task if slots available
            if self._active_count < self.current_capacity:
                try:
                    # Non-blocking check first
                    prio, ts, agent = self.queue.get(timeout=1)
                    
                    with self._pool_lock:
                        self._active_count += 1
                    
                    self.executor.submit(self._run_wrapper, agent)
                    
                except queue.Empty:
                    time.sleep(1) # Wait for tasks
            else:
                time.sleep(1) # Wait for slots

    def _run_wrapper(self, agent):
        try:
            agent.run()
            # If the agent produced a result, summarise it and inject as a system observation
            try:
                if agent.result:
                    try:
                        summary = self.bot.summarize_observation(str(agent.result))
                        self.bot.state.log_event("system", f"Subagent {agent.id} result summary: {summary}")
                        self.bot.state.log_event("system", f"Subagent {agent.id} result: {agent.result}")
                        # Require explicit acknowledgement before accepting consensus
                        self.bot.must_wait_for_observation = True
                        self.bot.state.log_event("system", "Action completed by subagent. Please acknowledge with <ack_observation> before finalizing.")
                    except Exception as e:
                        print(f"Warning: Failed to summarise subagent result: {e}")
            except Exception:
                pass
        finally:
            with self._pool_lock:
                self._active_count -= 1
                # Cleanup running_tasks registry if present
                try:
                    th = getattr(agent, '_task_hash', None)
                    if th and th in self.running_tasks and self.running_tasks[th] == agent.id:
                        del self.running_tasks[th]
                except Exception:
                    pass

    def get_status(self, agent_id: str):
        return self.agents[agent_id].status if agent_id in self.agents else None

    def get_result(self, agent_id: str):
        return self.agents[agent_id].result if agent_id in self.agents else None

    def list_agents(self):
        return {
            aid: {
                "status": a.status.value, 
                "task": a.task, 
                "result": (a.result[:100] + "...") if a.result else None
            } 
            for aid, a in self.agents.items()
        }

    def get_load_stats(self):
        return {
            "active": self._active_count,
            "queued": self.queue.qsize(),
            "capacity": self.current_capacity,
            "max_configured": self.max_capacity,
            "types": list(self.agent_registry.keys())
        }

    def terminate_agent(self, agent_id: str):
        if agent_id in self.agents:
            self.agents[agent_id].terminate()

# --- THE FlexiBot CORE ---
class Brain:
    """Simple façade over AgentState for external use.

    Skills and subagents can import and use this to read/write memory without
    touching the internal state implementation.
    """
    def __init__(self, state: AgentState):
        self._s = state

    def remember(self, key: str, value: Any):
        self._s.remember(key, value)

    def recall(self, key: str):
        return self._s.recall(key)

    def add(self, role: str, content: str, tags: list[str] | None = None):
        self._s.append_history(role, content, tags)

    def query(self, **kwargs):
        return self._s.query_history(**kwargs)


class BotContext:
    """Helper for constructing prompt messages from a FlexiBot instance.

    This class encapsulates the common patterns used when assembling the
    message list to send to the LLM, e.g. including the system prompt, the
    most recent user messages, previous plans, facts, tool outputs, etc.
    """
    def __init__(self, bot: 'FlexiBot'):
        self.bot = bot

    def build_prompt(self,
                     max_user: int = 3,
                     max_assistant: int = 3,
                     include_tags: list[str] | None = None,
                     since: float | None = None) -> list[dict]:
        """Return a list of messages suitable for passing to `client.chat()`.

        - `max_user`, `max_assistant` limit the number of user/assistant turns.
        - `include_tags` if provided limits entries to those containing any of
          the specified tags.
        - `since` restricts to history entries after the given timestamp.
        """
        prompt = []
        prompt.append({"role": "system", "content": self.bot.get_system_prompt()})

        # get filtered history from state
        hist = self.bot.state.query_history(since=since, limit=1000)
        if include_tags:
            hist = [e for e in hist if any(t in e.get("tags", []) for t in include_tags)]

        # split into recent user/assistant sequences
        user_msgs = [e for e in hist if e.get("role") == "user"]
        asst_msgs = [e for e in hist if e.get("role") == "assistant"]

        for msg in user_msgs[-max_user:]:
            prompt.append({"role": "user", "content": msg.get("content", "")})
        for msg in asst_msgs[-max_assistant:]:
            prompt.append({"role": "assistant", "content": msg.get("content", "")})
        return prompt

    def recent_by_tag(self, tag: str, limit: int = 10) -> list[dict]:
        """Shortcut for getting history entries with a particular tag."""
        return self.bot.state.query_history(tag=tag, limit=limit)

    def all_facts(self) -> list[dict]:
        return self.recent_by_tag("fact", limit=100)


class FlexiBot:
    def __init__(self):
        def _log(msg):
            StartupTracer.log(msg, "BOT_INIT")

        _log("init start")
        # check platform dependencies and warn
        SystemAutomation.warn_if_missing()
        ConsoleOutput.debug("returned from warn_if_missing")
        _log("returned from warn_if_missing")
        _log("warned dependencies")
        
        self.state = AgentState(STATE_FILE, GLOBALS_FILE, SNAPSHOT_DIR, MAX_SNAPSHOTS)
        _log("state created")
        self.brain = Brain(self.state)
        _log("brain created")
        self.logger = DiffLogger(EVOLUTION_LOG)
        _log("logger created")
        self.execution_policy = ExecutionPolicyLayer(load_runtime_config())
        _log("execution policy created")
        # context helper exposes convenient prompt-building utilities
        self.context = BotContext(self)
        _log("context helper created")
        # per-instance summarisation settings (can be overridden)
        self.auto_summary_threshold = AUTO_SUMMARY_THRESHOLD
        self.auto_summary_keep = AUTO_SUMMARY_KEEP
        # skill instances loaded at startup
        self.skills: dict[str, BaseSkill] = {}
        self.skill_prompt_templates: dict[str, PromptTemplateSpec] = {}
        self.skill_prompt_injectors: dict[str, dict[str, Any]] = {}
        self.skill_tool_wrappers: dict[str, dict[str, Any]] = {}
        self.skill_capabilities: dict[str, list[str]] = {}
        _log("loading skills")
        self._load_skills()
        _log("skills loaded")
        _log("setting up client")
        self._setup_client()
        _log("client setup complete")
        self.subagent_manager = SubagentManager(self)
        _log("subagent manager created")
        self._state_lock = threading.Lock()
        _log("state lock created")
        
        # Runtime temp state
        self.last_turn_resp = None
        self.repetition_count = 0
        self.last_tools = {} # Track tool usage for loop detection
        # persistent turn counter used for logging; increments across handle_turn calls
        self.turn_counter = 0
        self.last_observation = ""

        _log("initialized runtime temp state")

        # Control flag: If True, the agent must explicitly acknowledge the last observation
        # using the token <ack_observation> before a <consensus> will be accepted.
        self.must_wait_for_observation = False
        _log("constructor complete")

    # --- event hooks --------------------------------------------------------
    def on_user_input(self, text: str):
        # example: simple fact extraction from user statements
        for m in re.findall(r"I (?:am|have) ([\w ]+)", text, re.I):
            self.brain.remember(m.strip(), True)
        # tag a general fact for later querying
        self.state.append_history("system", f"fact:{text}", tags=["fact"])

    def on_tool_output(self, tool_name: str, output: str):
        # store raw tool output with a tool-specific tag for retrieval
        self.state.append_history("system", output, tags=[f"tool:{tool_name}"])

    def _normalize_tool_payload(self, payload: str) -> str:
        if not isinstance(payload, str):
            payload = str(payload)
        return re.sub(r"\s+", " ", payload).strip()

    def _tool_result_failed(self, result: str) -> bool:
        lowered = (result or "").lower()
        failure_markers = (
            "traceback",
            "error:",
            "execution failed",
            "rejected before execution",
            "syntaxerror",
            "execution blocked",
        )
        return any(marker in lowered for marker in failure_markers)

    def _append_response_trace(self, event_type: str, **payload):
        record = {
            "timestamp": datetime.now().isoformat(),
            "event": event_type,
            **payload,
        }
        try:
            RESPONSE_TRACE_FILE.parent.mkdir(parents=True, exist_ok=True)
            with RESPONSE_TRACE_FILE.open("a", encoding="utf-8") as f:
                f.write(json.dumps(record) + "\n")
        except Exception:
            pass

    def _format_python_syntax_error(self, code: str, err: SyntaxError) -> str:
        line = ""
        if isinstance(getattr(err, "text", None), str):
            line = err.text.rstrip("\r\n")
        elif err.lineno:
            lines = code.splitlines()
            if 0 < err.lineno <= len(lines):
                line = lines[err.lineno - 1]
        pointer = ""
        if line and err.offset:
            caret_col = max(0, min(len(line), int(err.offset) - 1))
            pointer = "\n" + (" " * caret_col) + "^"
        details = f"{line}{pointer}" if line else ""
        suffix = f"\n{details}" if details else ""
        return (
            f"[System] Python payload rejected before execution: {err.msg} "
            f"(line {err.lineno}, column {err.offset}). This usually means the model emitted malformed code or collapsed newlines."
            f"{suffix}"
        )
    def _build_recovery_prompt(self, reason: str) -> list[dict[str, str]]:
        recent_history = self.state.history[-10:]
        history_text = "\n".join(
            f"{entry.get('role', 'unknown')}: {str(entry.get('content', ''))[:500]}"
            for entry in recent_history
        )
        prompt = (
            "You are preparing a handoff note for the user because the agent reached an internal stop condition. "
            "Do not use any tool tags. Respond in plain text only.\n\n"
            f"Reason: {reason}\n"
            f"Last observation: {self.last_observation[:1500] or 'None'}\n\n"
            "Write a concise response with exactly these sections:\n"
            "1. Current work summary\n"
            "2. Progress so far (bullet list)\n"
            "3. Best next step\n"
            "4. User choice\n\n"
            "In 'User choice', ask the user to either continue the same task or switch to something else."
            f"\n\nRecent history:\n{history_text}"
        )
        return [
            {"role": "system", "content": self.get_system_prompt()},
            {"role": "user", "content": prompt},
        ]

    def _recover_from_turn_limit(self, reason: str) -> str:
        fallback = (
            "Current work summary\n"
            f"- The agent paused because: {reason}.\n\n"
            "Progress so far\n"
            f"- Last observation: {self.last_observation[:1000] or 'No observation recorded.'}\n\n"
            "Best next step\n"
            "- Either continue from the last observation or redirect the task.\n\n"
            "User choice\n"
            "- Reply with 'continue' to keep going, or tell me what to do next."
        )
        try:
            recovery_messages = self._build_recovery_prompt(reason)
            resp_data = self.client.chat(recovery_messages)
            recovery_text = resp_data["choices"][0]["message"]["content"].strip()
            if not recovery_text:
                recovery_text = fallback
        except Exception as e:
            recovery_text = fallback + f"\n\n[Recovery note fallback: {e}]"

        self._append_response_trace(
            "recovery_response",
            reason=reason,
            observation=self.last_observation,
            response=recovery_text,
        )
        self.state.log_event("assistant", recovery_text)
        return recovery_text

    # --- convenient getters for prompt assembly ----------------------------
    def recent_user_messages(self, n: int = 3):
        return [e["content"] for e in self.state.query_history(role="user", limit=n)]

    def recent_plans(self, n: int = 5):
        return [e["content"] for e in self.state.query_history(tag="plan", limit=n)]

    def facts_matching(self, pattern: str):
        return [e for e in self.state.query_history(tag="fact") if pattern in e["content"]]

    def _setup_client(self):
        config = {}
        if CONFIG_FILE.exists():
            try:
                with open(CONFIG_FILE, "r") as f: config = json.load(f)
            except: pass
        
        provider = config.get("provider", "copilot")
        
        if provider == "ollama":
            ConsoleOutput.system(f"Using Ollama Provider ({config.get('model', 'lfm2.5-thinking')})")
            self.client = OllamaProvider(
                model=config.get("model", "lfm2.5-thinking"),
                host=config.get("host", "127.0.0.1"),
                port=config.get("port", "11434")
            )
        else:
            ConsoleOutput.system("Using GitHub Copilot Provider")
            self.client = CopilotClient()

    def _build_skill_context(self, skill: BaseSkill) -> SkillLifecycleContext:
        metadata = skill.metadata()
        return SkillLifecycleContext(
            bot=self,
            skill_name=metadata.name,
            metadata=metadata,
            config=dict(getattr(skill, "skill_config", {}) or {}),
        )

    def _register_skill_assets(self, skill: BaseSkill):
        metadata = skill.metadata()
        self.skill_capabilities[metadata.name] = list(metadata.capabilities or [])

        templates = skill.prompt_templates() or {}
        if not isinstance(templates, dict):
            raise TypeError(f"Skill '{metadata.name}' prompt_templates() must return a dict")
        for template_name, template_value in templates.items():
            existing = self.skill_prompt_templates.get(template_name)
            if existing and existing.source_skill != metadata.name:
                ConsoleOutput.warning(
                    f"Skill prompt template conflict for '{template_name}': keeping '{existing.source_skill}', skipping '{metadata.name}'"
                )
                continue
            self.skill_prompt_templates[template_name] = PromptTemplateSpec(
                name=template_name,
                template=template_value,
                source_skill=metadata.name,
            )

        injectors = skill.prompt_injectors() or {}
        if not isinstance(injectors, dict):
            raise TypeError(f"Skill '{metadata.name}' prompt_injectors() must return a dict")
        for injector_name, injector_value in injectors.items():
            existing = self.skill_prompt_injectors.get(injector_name)
            if existing and existing.get("skill") != metadata.name:
                ConsoleOutput.warning(
                    f"Skill prompt injector conflict for '{injector_name}': keeping '{existing.get('skill')}', skipping '{metadata.name}'"
                )
                continue
            self.skill_prompt_injectors[injector_name] = {"skill": metadata.name, "value": injector_value}

        wrappers = skill.tool_wrappers() or {}
        if not isinstance(wrappers, dict):
            raise TypeError(f"Skill '{metadata.name}' tool_wrappers() must return a dict")
        for tool_name, wrapper in wrappers.items():
            existing = self.skill_tool_wrappers.get(tool_name)
            if existing and existing.get("skill") != metadata.name:
                ConsoleOutput.warning(
                    f"Skill tool wrapper conflict for '{tool_name}': keeping '{existing.get('skill')}', skipping '{metadata.name}'"
                )
                continue
            self.skill_tool_wrappers[tool_name] = {"skill": metadata.name, "wrapper": wrapper}

    def _load_skills(self):
        """Import all Python files in SKILLS_DIR and instantiate registered skills."""
        SKILLS_DIR.mkdir(parents=True, exist_ok=True)
        # load any modules placed in the skills directory
        for path in SKILLS_DIR.glob("*.py"):
            try:
                spec = importlib.util.spec_from_file_location(path.stem, path)
                module = importlib.util.module_from_spec(spec)
                # make BaseSkill available to skill modules during import
                module.BaseSkill = BaseSkill
                spec.loader.exec_module(module)  # type: ignore
            except Exception as e:
                ConsoleOutput.warning(f"Failed to import skill {path.name}: {e}")
        # instantiate registered skill classes
        ordered_skills = sorted(skill_registry.items(), key=lambda item: item[1].metadata().priority)
        for name, cls in ordered_skills:
            deps = []
            try:
                deps = cls.dependencies()
            except Exception:
                pass
            for dep in deps:
                try:
                    __import__(dep)
                except Exception:
                    ConsoleOutput.warning(f"Skill '{name}' missing dependency '{dep}'")
            try:
                skill = cls(self)
                self._register_skill_assets(skill)
                self.skills[name] = skill
                try:
                    skill.on_load(self._build_skill_context(skill))
                except Exception as e:
                    ConsoleOutput.warning(f"Skill '{name}' on_load failed: {e}")
            except Exception as e:
                ConsoleOutput.error(f"Error instantiating skill {name}: {e}")

    async def chat_async(self, messages: list[dict]) -> dict:
        """Asynchronous wrapper around the LLM client.
        Currently spins the synchronous client in a thread pool.
        """
        with ThreadPoolExecutor(max_workers=1) as ex:
            future = ex.submit(self.client.chat, messages)
            return future.result()

    def compress_context(self):
        """Performs context summary when token limit is hit."""
        print(f"\n[System]: ⚠️ Token limit ({self.state.total_tokens}) reached. Compressing...")
        old_token_count = self.state.total_tokens
        
        # Heuristic: If we are already crashing (400 Bad Request), asking the API to summarize 
        # the thing that is too big will just crash again.
        # Fallback Strategy: Hard truncation + Local specific summary if possible
        
        try:
            # Attempt 1: Try to summarizing only the last 20 messages if full history is massive
            recent_history = self.state.history[-20:]
            full_history_text = "\n".join([f"{m['role']}: {str(m['content'])[:200]}" for m in recent_history])
            
            prompt = f"Condense the following conversation fragment. Conversation:\n{full_history_text}..."
            
            # Using a very simple prompt to minimize overhead
            res = self.client.chat([{"role": "user", "content": prompt}])
            summary = res["choices"][0]["message"]["content"]
            
        except Exception as e:
            print(f"[System]: ⚠ LLM Summary failed ({e}). Performing hard reset.")
            summary = "Context reset due to overflow. Check archive for details."

    def auto_summarize_history(self):
        """Automatic summarisation of old conversation turns when history grows.

        Moves everything prior to the last `AUTO_SUMMARY_KEEP` entries into a
        single summary system message. This keeps the prompt window small while
        retaining a summarized record of earlier discussion.
        """
        total = self.state.history_count()
        if total <= getattr(self, "auto_summary_threshold", AUTO_SUMMARY_THRESHOLD):
            return

        # pick entries to summarise
        keep = getattr(self, "auto_summary_keep", AUTO_SUMMARY_KEEP)
        history_entries = self.state.history
        old_entries = history_entries[: total - keep]
        remaining = history_entries[total - keep :]

        if not old_entries:
            return

        text = "\n".join(f"{e['role']}: {str(e['content'])}" for e in old_entries)
        prompt = f"Condense the following earlier conversation into a brief summary:\n{text[:2000]}"
        try:
            res = self.client.chat([{"role": "user", "content": prompt}])
            summary = res["choices"][0]["message"]["content"]
        except Exception as e:
            print(f"[System]: auto_summarize_history LLM error: {e}")
            summary = "[Summary failed - see full archive]"

        # rewrite history cache
        summary_entry = {"role": "system", "content": f"Earlier summary: {summary}", "tags": ["summary"], "timestamp": time.time()}
        self.state.replace_history_cache([summary_entry] + remaining)

        # also append summary as a formal event so it's persisted
        self.state.append_history("system", f"Earlier summary: {summary}", tags=["summary"])
        print(f"[System]: Auto-summarized old history ({total - self.auto_summary_keep} entries collapsed)")

    def summarize_observation(self, obs: str, max_len: int = 300) -> str:
        """Produce a short JSON summary for observations to inject into system messages.
        Returns a JSON string with keys: summary, snippet, length, errors."""
        try:
            s = obs.strip()
            lines = s.splitlines()
            snippet = " ".join(lines[:2]) if lines else ""
            err = bool("Traceback" in s or "Error:" in s or "error:" in s.lower())
            data = {
                "summary": (lines[0][:200] + ("..." if len(lines[0]) > 200 else "")) if lines else "",
                "snippet": snippet[:max_len],
                "length": len(s),
                "errors": err
            }
            return json.dumps(data)
        except Exception:
            return json.dumps({"summary": "(Could not summarize observation)", "snippet": "", "length": 0, "errors": True})

    def get_runtime_status(self) -> Dict[str, Any]:
        """Returns metadata about the current agent state."""
        return {
            "status": "active",
            "timestamp": time.time(),
            "metrics": {
                "total_tokens": self.state.total_tokens,
                "snapshots": len(list(self.state.snapshot_dir.glob("*.db"))),
                "threads": threading.active_count(),
                "background_tasks": len(self.state.active_processes),
            },
            "subagents": self.subagent_manager.get_load_stats(),
            "memory_keys": list(self.state.structured_memory.keys()),
            "background_task_ids": sorted(self.state.active_processes.keys()),
            "execution_policy": self.execution_policy.describe(),
        }

    def verify_and_report(self, result: str, context: str = "") -> Dict[str, Any]:
        """Run lightweight verification on textual tool output. Returns a summary dict and logs results.
        Looks for "Traceback", 'Error', 'FAILED', '✗', or other failure markers."""
        try:
            r = (result or "").strip()
            errors = []
            success = True

            if not r:
                success = False
                errors.append("No output returned from verification run.")

            if "Traceback" in r or "Traceback (most recent call last)" in r:
                success = False
                errors.append("Traceback detected in output.")

            lowered = r.lower()
            if "error:" in lowered or "failed" in lowered or "✗" in r:
                success = False
                # Capture a short context line
                first_error_line = next((l for l in r.splitlines() if 'error' in l.lower() or 'fail' in l.lower() or 'traceback' in l.lower()), None)
                if first_error_line:
                    errors.append(first_error_line.strip())

            summary = None
            if errors:
                summary = f"Verification FAILED: {'; '.join(errors)}"
            else:
                summary = "Verification OK: No obvious errors detected."

            # Log to state & evolution log
            self.state.log_event("system", f"Verification ({context}): {summary}")
            self.logger.log_turn(0, f"verify:{context}", summary, ["verify"])

            return {"success": success, "summary": summary, "errors": errors}
        except Exception as e:
            ErrorHandler.log(e, context="verify_and_report")
            return {"success": False, "summary": f"Verification failed: {e}", "errors": [str(e)]}

    def _run_tool_hook(self, stage: str, tool_name: str, payload: str):
        """Internal helper to call skill hooks before/after tool execution."""
        for skill in getattr(self, 'skills', {}).values():
            try:
                context = ToolHookContext(
                    bot=self,
                    stage=stage,
                    tool_name=tool_name,
                    payload=payload,
                    skill_name=skill.metadata().name,
                    result=payload if stage != 'pre' else None,
                )
                if stage == 'pre':
                    skill.on_pre_tool(context)
                    skill.pre_tool(tool_name, payload)
                else:
                    skill.on_post_tool(context)
                    skill.post_tool(tool_name, payload)
            except Exception:
                pass

    def _run_tool_with_wrapper(self, tool_name: str, payload: str, executor: Callable[[str], str]) -> str:
        wrapper_entry = self.skill_tool_wrappers.get(tool_name)
        if not wrapper_entry:
            return executor(payload)
        try:
            return wrapper_entry["wrapper"](payload, executor)
        except Exception as e:
            ConsoleOutput.warning(
                f"Skill wrapper failed for '{tool_name}' from '{wrapper_entry.get('skill', 'unknown')}': {e}"
            )
            return executor(payload)

    def _render_skill_prompt_sections(self) -> str:
        sections: list[str] = []
        for spec in self.skill_prompt_templates.values():
            try:
                content = spec.template(self) if callable(spec.template) else spec.template
                if content:
                    sections.append(f"[{spec.source_skill}:{spec.name}] {str(content).strip()}")
            except Exception as e:
                ConsoleOutput.warning(f"Skill prompt template '{spec.name}' failed: {e}")

        for injector_name, injector in self.skill_prompt_injectors.items():
            try:
                value = injector.get("value")
                content = value(self) if callable(value) else value
                if content:
                    sections.append(f"[{injector.get('skill')}:{injector_name}] {str(content).strip()}")
            except Exception as e:
                ConsoleOutput.warning(f"Skill prompt injector '{injector_name}' failed: {e}")

        if not sections:
            return ""
        return "\n\nSKILL CONTEXT:\n" + "\n".join(f"- {section}" for section in sections)

    def unload_skills(self):
        for skill in list(getattr(self, 'skills', {}).values()):
            try:
                skill.on_unload(self._build_skill_context(skill))
            except Exception as e:
                ConsoleOutput.warning(f"Skill '{skill.metadata().name}' on_unload failed: {e}")

    def run_bash(self, cmd: str) -> str:
        """Run a shell command with smart platform translations and flexible executor selection.
        Returns a string containing STDOUT and STDERR."""
        if not cmd or not cmd.strip():
            return "No command provided."

        decision = self.execution_policy.evaluate("bash", cmd)
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=cmd)
            return f"Execution blocked: {decision.reason}"

        try:
            self._run_tool_hook('pre', 'bash', cmd)
        except Exception:
            pass

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=cmd)

        def _execute_core(raw_cmd: str) -> str:
            translation_note = ""
            cmd_stripped = raw_cmd.strip()
            cmd_parts = cmd_stripped.split()
            if not cmd_parts:
                return "Empty command."
            cmd_base = cmd_parts[0].lower()

            # Determine Preferred Shell
            executor = "cmd" if os.name == "nt" else "sh"
            if os.name == "nt":
                # If the user specifically wants bash, we use it, but otherwise default to CMD/PowerShell 
                # so that agents don't get confused when trying 'dir' on a Windows box with Git Bash installed.
                if os.environ.get("FLEXI_SHELL") == "bash" and shutil.which("bash"):
                    executor = "bash"
                elif shutil.which("powershell"):
                    executor = "powershell"

            # Apply Cross-Platform Translation logic
            mapping = {}
            if executor in ["cmd", "powershell"]:
                mapping = {'ls': 'dir', 'cat': 'type', 'grep': 'findstr', 'rm': 'del', 'mv': 'move', 'cp': 'copy', 'clear': 'cls'}
            else:
                mapping = {'dir': 'ls', 'type': 'cat', 'cls': 'clear', 'findstr': 'grep', 'del': 'rm', 'move': 'mv', 'copy': 'cp'}

            cmd_to_run = raw_cmd
            if cmd_base in mapping:
                new_base = mapping[cmd_base]
                cmd_to_run = cmd_stripped.replace(cmd_parts[0], new_base, 1)
                translation_note = f"[Translated '{cmd_base}' -> '{new_base}' for {executor}] "

            # Prepare Execution Args
            use_shell = True
            exec_args = cmd_to_run
            if os.name == 'nt':
                if executor == "bash" and shutil.which('bash'):
                    exec_args = [shutil.which('bash'), '-c', cmd_to_run]
                    use_shell = False
                elif executor == "powershell" and shutil.which('powershell'):
                    exec_args = [shutil.which('powershell'), '-Command', cmd_to_run]
                    use_shell = False
                # Else: defaults to CMD via subprocess.run(shell=True)

            # Retry loop for transient errors
            retries = 2
            attempt = 0
            while True:
                try:
                    if use_shell:
                        res = subprocess.run(exec_args, shell=True, capture_output=True, text=True, timeout=decision.timeout_seconds, encoding='utf-8', errors='replace', **self.execution_policy.subprocess_kwargs(decision))
                    else:
                        res = subprocess.run(exec_args, capture_output=True, text=True, timeout=decision.timeout_seconds, encoding='utf-8', errors='replace', **self.execution_policy.subprocess_kwargs(decision))

                    stdout = res.stdout or ""
                    stderr = res.stderr or ""

                    not_found = ["not recognized as", "command not found", "No such file or directory"]
                    if any(p in stderr for p in not_found):
                        suggestion = f"Suggestion: use platform-native commands or verify the path. Current executor: {executor}"
                        return self.execution_policy.trim_output(decision, translation_note + f"STDOUT: {stdout}\nSTDERR: {stderr}\n{suggestion}")

                    return self.execution_policy.trim_output(decision, translation_note + f"STDOUT: {stdout}\nSTDERR: {stderr}")

                except subprocess.TimeoutExpired as e:
                    attempt += 1
                    if attempt > retries:
                        return f"Error: Command timed out after {retries} retries ({cmd_to_run})"
                    time.sleep(1 * (2 ** (attempt - 1)))
                    continue
                except Exception as e:
                    return f"Error: Execution failed: {e}"

        result = self._run_tool_with_wrapper('bash', cmd, _execute_core)
        self.execution_policy.audit(
            decision,
            action="finish",
            status="completed" if not result.startswith("Error:") else "failed",
            payload=cmd,
            result=result,
            duration_ms=int((time.time() - start_time) * 1000),
        )
        try:
            self._run_tool_hook('post', 'bash', result)
        except Exception:
            pass
        return result

    def tool_list_processes(self, filter_text: str = None):
        """Returns a list of running processes. Uses psutil if available, otherwise tasklist/ps."""
        try:
            import psutil
            procs = []
            for proc in psutil.process_iter(['pid', 'name', 'username']):
                try:
                    info = proc.info
                    name = str(info['name'] or "")
                    if filter_text and filter_text.lower() not in name.lower(): continue
                    procs.append(info)
                except (psutil.NoSuchProcess, psutil.AccessDenied): pass
            return json.dumps(procs[:100], indent=2) # Limit to 100 for safety
        except ImportError:
            # Fallback to shell
            cmd = "tasklist" if os.name == "nt" else "ps aux"
            if filter_text:
                cmd += f" | findstr /i {filter_text}" if os.name == "nt" else f" | grep -i {filter_text}"
            return self.run_bash(cmd)

    def tool_get_software_versions(self):
        """Checks versions for common development tools."""
        tools = ["python", "node", "npm", "npx", "yarn", "git", "docker", "prisma", "pip", "tsc", "rustc", "cargo"]
        results = {}
        for t in tools:
            # Try --version
            try:
                p = subprocess.run([t, "--version"], capture_output=True, text=True, shell=True, timeout=5, encoding='utf-8', errors='replace')
                if p.returncode == 0:
                    results[t] = p.stdout.strip() or p.stderr.strip()
                else:
                    results[t] = "Not installed or failed"
            except Exception:
                results[t] = "Not found"
        return json.dumps(results, indent=2)

    def tool_inspect_python_environment(self):
        return rlm_inspect_python_environment()

    def tool_list_python_packages(self, limit: int = 500):
        return rlm_list_python_packages(limit=limit)

    def tool_python_symbol_doc(self, symbol_name: str, filepath: str = "", root: str = ".", max_results: int = 10):
        return rlm_python_symbol_doc(symbol_name=symbol_name, filepath=filepath, root=root, max_results=max_results)

    def tool_python_import_graph(self, filepath: str, root: str = "."):
        return rlm_python_import_graph(filepath=filepath, root=root)

    def tool_validate_python_snippet(self, code: str, mode: str = "exec"):
        return rlm_validate_python_snippet(code=code, mode=mode)

    def tool_python_refactor_symbol(self, filepath: str, old_name: str, new_name: str, apply: bool = False):
        return rlm_python_refactor_symbol(filepath=filepath, old_name=old_name, new_name=new_name, apply=apply)

    def tool_python_cleanup_unused_imports(self, filepath: str, apply: bool = False):
        return rlm_python_cleanup_unused_imports(filepath=filepath, apply=apply)

    def tool_python_type_annotation_assist(self, filepath: str):
        return rlm_python_type_annotation_assist(filepath=filepath)

    def tool_find_references(self, symbol_name: str, root: str = ".", patterns: str = "", max_results: int = 100):
        return rlm_find_references(symbol_name=symbol_name, root=root, patterns=patterns or None, max_results=max_results)

    def tool_find_implementations(self, symbol_name: str, root: str = ".", patterns: str = "", max_results: int = 100):
        return rlm_find_implementations(symbol_name=symbol_name, root=root, patterns=patterns or None, max_results=max_results)

    def tool_preview_symbol_rename(self, symbol_name: str, new_name: str, root: str = ".", patterns: str = "", max_results: int = 200):
        return rlm_preview_symbol_rename(symbol_name=symbol_name, new_name=new_name, root=root, patterns=patterns or None, max_results=max_results)

    def tool_git_changed_files(self, repo_path: str = ".", include_untracked: bool = True):
        return rlm_git_changed_files(repo_path=repo_path, include_untracked=include_untracked)

    def tool_git_diff_analysis(self, repo_path: str = ".", src: str = "HEAD", dst: str = "", max_patch_chars: int = 4000):
        return rlm_git_diff_analysis(repo_path=repo_path, src=src, dst=dst, max_patch_chars=max_patch_chars)

    def tool_git_blame_context(self, filepath: str, line: int, repo_path: str = "."):
        return rlm_git_blame_context(filepath=filepath, line=line, repo_path=repo_path)

    def tool_git_commit_message_draft(self, repo_path: str = ".", src: str = "HEAD", dst: str = ""):
        return rlm_git_commit_message_draft(repo_path=repo_path, src=src, dst=dst)

    def tool_project_map(self, root: str = "."):
        return rlm_project_map(root=root)

    def tool_project_relationships(self, root: str = ".", max_nodes: int = 120):
        return rlm_project_relationships(root=root, max_nodes=max_nodes)

    def tool_notebook_summary(self, filepath: str):
        return rlm_notebook_summary(filepath)

    def tool_notebook_edit_cell(self, filepath: str, index: int, source: str = "", cell_type: str = "code", operation: str = "replace"):
        return rlm_notebook_edit_cell(filepath=filepath, index=index, source=source, cell_type=cell_type, operation=operation)

    def tool_notebook_run(self, filepath: str, cell_index: int | None = None, persist_output: bool = True):
        return rlm_notebook_run(filepath=filepath, cell_index=cell_index, persist_output=persist_output)

    def tool_notebook_kernel_info(self, filepath: str):
        return rlm_notebook_kernel_info(filepath)

    def tool_notebook_session_status(self, filepath: str):
        return rlm_notebook_session_status(filepath)

    def tool_notebook_clear_session(self, filepath: str):
        return rlm_notebook_clear_session(filepath)

    def tool_notebook_install_package(self, filepath: str, package: str, upgrade: bool = False):
        return rlm_notebook_install_package(filepath=filepath, package=package, upgrade=upgrade)

    def tool_db_save_profile(self, name: str, database_path: str, kind: str = "sqlite", description: str = ""):
        return rlm_db_save_profile(name=name, database_path=database_path, kind=kind, description=description)

    def tool_db_list_profiles(self):
        return rlm_db_list_profiles()

    def tool_db_schema(self, profile_name: str = "", database_path: str = ""):
        return rlm_db_schema(profile_name=profile_name, database_path=database_path)

    def tool_db_query(self, query: str, profile_name: str = "", database_path: str = "", limit: int = 200):
        return rlm_db_query(query=query, profile_name=profile_name, database_path=database_path, limit=limit)

    def tool_db_migration_status(self, root: str = "."):
        return rlm_db_migration_status(root=root)

    def tool_fetch_webpage(self, url: str, timeout: int = 20, max_chars: int = 12000):
        return rlm_fetch_webpage(url=url, timeout=timeout, max_chars=max_chars)

    def tool_extract_web_structure(self, url: str, timeout: int = 20, max_items: int = 20):
        return rlm_extract_web_structure(url=url, timeout=timeout, max_items=max_items)

    def tool_extract_doc_section(self, url: str, query: str, timeout: int = 20, max_matches: int = 5):
        return rlm_extract_doc_section(url=url, query=query, timeout=timeout, max_matches=max_matches)

    def tool_summarize_web_reference(self, url: str, timeout: int = 20, max_points: int = 8):
        return rlm_summarize_web_reference(url=url, timeout=timeout, max_points=max_points)

    def tool_research_web(self, query: str, urls: list[str] | None = None, timeout: int = 20, max_sources: int = 5):
        return rlm_research_web(query=query, urls=urls, timeout=timeout, max_sources=max_sources)

    def tool_git_review_summary(self, repo_path: str = ".", src: str = "HEAD", dst: str = ""):
        return rlm_git_review_summary(repo_path=repo_path, src=src, dst=dst)

    def tool_install_python_package(self, package: str, upgrade: bool = False):
        package = str(package or "").strip()
        if not package:
            return json.dumps({"ok": False, "tool": "install_python_package", "errors": ["Package name is required."]}, indent=2)
        requested = f"{package} {'--upgrade' if upgrade else ''}".strip()
        decision = self.execution_policy.evaluate("install_python_package", requested)
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=requested)
            return json.dumps({"ok": False, "tool": "install_python_package", "errors": [decision.reason]}, indent=2)
        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=requested)
        cmd = [sys.executable, "-m", "pip", "install", package]
        if upgrade:
            cmd.append("--upgrade")
        try:
            res = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=decision.timeout_seconds,
                encoding='utf-8',
                errors='replace',
                **self.execution_policy.subprocess_kwargs(decision),
            )
            output = self.execution_policy.trim_output(decision, (res.stdout or "") + ("\n" + res.stderr if res.stderr else ""))
            result = {
                "ok": res.returncode == 0,
                "tool": "install_python_package",
                "package": package,
                "upgrade": bool(upgrade),
                "returncode": res.returncode,
                "output": output,
            }
            self.execution_policy.audit(
                decision,
                action="finish",
                status="completed" if res.returncode == 0 else "failed",
                payload=requested,
                result=output,
                duration_ms=int((time.time() - start_time) * 1000),
            )
            return json.dumps(result, indent=2)
        except Exception as e:
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=requested,
                result=str(e),
                duration_ms=int((time.time() - start_time) * 1000),
            )
            return json.dumps({"ok": False, "tool": "install_python_package", "package": package, "errors": [str(e)]}, indent=2)

    def _bg_task_log_path(self, pid: str | int) -> Path:
        BG_TASK_LOG_DIR.mkdir(parents=True, exist_ok=True)
        return BG_TASK_LOG_DIR / f"bg_task_{pid}.log"

    def tool_get_bg_task_details(self, pid: str = ""):
        active = self.state.active_processes
        if pid:
            info = active.get(str(pid))
            if not info:
                return json.dumps({"ok": False, "tool": "get_bg_task_details", "errors": [f"No background task found for PID {pid}"]}, indent=2)
            return json.dumps({"ok": True, "tool": "get_bg_task_details", "task": info}, indent=2)
        return json.dumps({"ok": True, "tool": "get_bg_task_details", "tasks": list(active.values())}, indent=2)

    def tool_read_bg_task_log(self, pid: str, lines: int = 50):
        log_path = self._bg_task_log_path(pid)
        if not log_path.exists():
            return f"No log file found for background task {pid}."
        try:
            content = log_path.read_text(encoding='utf-8', errors='replace').splitlines()
            return "\n".join(content[-max(1, int(lines)):])
        except Exception as e:
            return f"Background log read error: {e}"

    def tool_stop_bg_task(self, pid: str, force: bool = False):
        pid_str = str(pid)
        active = self.state.active_processes
        info = active.get(pid_str)
        if not info:
            return f"No background task found for PID {pid_str}."
        try:
            if os.name == 'nt':
                cmd = ["taskkill", "/PID", pid_str]
                if force:
                    cmd.append("/F")
                subprocess.run(cmd, capture_output=True, text=True, timeout=20, encoding='utf-8', errors='replace')
            else:
                os.kill(int(pid_str), signal.SIGKILL if force else signal.SIGTERM)
            info["status"] = "stopped"
            info["stopped_at"] = time.time()
            self.state.set_active_process(pid_str, info, persist=False)
            self.state.save()
            return f"Stopped background task {pid_str}."
        except Exception as e:
            return f"Failed to stop background task {pid_str}: {e}"

    def tool_restart_bg_task(self, pid: str):
        pid_str = str(pid)
        active = self.state.active_processes
        info = active.get(pid_str)
        if not info:
            return f"No background task found for PID {pid_str}."
        task_type = info.get("type")
        if task_type == "shell":
            self.tool_stop_bg_task(pid_str, force=False)
            return self.tool_spawn_background(info.get("cmd", ""), timeout=30)
        if task_type == "python_bg" and info.get("script_path"):
            try:
                code = Path(info["script_path"]).read_text(encoding='utf-8', errors='replace')
            except Exception as e:
                return f"Failed to reload background script: {e}"
            self.tool_stop_bg_task(pid_str, force=False)
            return self.tool_run_python_bg(code)
        return f"Restart not supported for background task type '{task_type}'."

    def subagent(self, task: str, work_dir: str = ".", priority: int = 2, agent_type: str = "generic") -> str:
        """Isolated subagent loop delegated to SubagentManager."""
        print(f"\\n[Subagent Plan]: {task} (Dir: {work_dir}, Prio: {priority}, Type: {agent_type})")
        agent_id = self.subagent_manager.spawn(task, work_dir, priority, agent_type)
        
        while True:
            status = self.subagent_manager.get_status(agent_id)
            if status in [SubagentStatus.COMPLETED, SubagentStatus.FAILED, SubagentStatus.TERMINATED]:
                res = self.subagent_manager.get_result(agent_id)
                return res if res else "No result returned."
            time.sleep(1)

    # --- TOOL METHODS ---
    def tool_remember(self, tag: str, content: str):
        # Legacy compat: Use KV cache as structured memory
        current = self.state.recall(tag) or []
        if not isinstance(current, list): current = [str(current)]
        current.append(str(content))
        self.state.remember(tag, current)
        return f"✓ Stored in memory under tag '{tag}'"

    def tool_recall(self, tag: str):
        items = self.state.recall(tag)
        if not items: return f"No memory found for tag '{tag}'"
        if isinstance(items, list): return "\n---\n".join(str(i) for i in items)
        return str(items)

    def tool_search_memory(self, query: str):
        # Scan kv cache directly
        results = []
        mem = self.state.memory
        for tag, items in mem.items():
            if tag == "active_processes": continue
            if isinstance(items, list):
                for item in items:
                    if query.lower() in str(item).lower():
                        results.append(f"[{tag}] {item}")
            elif query.lower() in str(items).lower():
                results.append(f"[{tag}] {items}")
        return "\n".join(results) if results else f"No memories found matching '{query}'"

    def tool_save_skill(self, name: str, code: str):
        path = SKILLS_DIR / f"{name}.py"
        path.write_text(code, encoding="utf-8")
        return f"✓ Skill '{name}' saved to {path}"

    def tool_load_skill(self, name: str, env: dict):
        path = SKILLS_DIR / f"{name}.py"
        if not path.exists(): return f"Skill '{name}' not found."
        # We execute the skill code directly into the current environment
        exec(path.read_text(encoding="utf-8"), env, env) 
        return f"✓ Skill '{name}' loaded."

    def tool_validate_python(self, filepath: str = "", code: str = ""):
        return rlm_validate_python(filepath=filepath, code=code)

    def tool_validate_json(self, filepath: str = "", content: str = ""):
        return rlm_validate_json(filepath=filepath, content=content)

    def tool_run_tests(self, command: str = ""):
        test_command = command.strip()
        if not test_command:
            test_candidates = list(Path(".").glob("test_*.py")) + list(Path("tests").glob("**/test*.py")) if Path("tests").exists() else list(Path(".").glob("test_*.py"))
            if not test_candidates:
                return json.dumps({"ok": False, "tool": "run_tests", "errors": ["No tests found and no command provided."]}, indent=2)
            test_command = f'"{sys.executable}" -m unittest discover -v'
        result = self.run_bash(test_command)
        verification = self.verify_and_report(result, context=f"tests:{test_command}")
        return json.dumps({
            "ok": verification.get("success", False),
            "tool": "run_tests",
            "command": test_command,
            "summary": verification.get("summary", ""),
            "errors": verification.get("errors", []),
            "output": result[:4000],
        }, indent=2)

    def tool_run_verification(self, target_script: str = "flexi_temp.py"):
        """Generates and runs an advanced controller verification suite."""
        script_content = f"""import subprocess
    def __init__(self, script_path):
        self.script_path = script_path
        self.process = None
        self.output_queue = queue.Queue()
        self.is_running = False
        # Track service restarts and failures
        self.restart_history = []

    def start(self):
        print(f"[Controller] Launching {{self.script_path}}...")
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        self.process = subprocess.Popen(
            [sys.executable, "-u", self.script_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            env=env
        )
        self.is_running = True
        
        # Stream threads
        threading.Thread(target=self._stream_reader, args=(self.process.stdout, "STDOUT"), daemon=True).start()
        threading.Thread(target=self._stream_reader, args=(self.process.stderr, "STDERR"), daemon=True).start()
        return self

    def _stream_reader(self, stream, label):
        for line in iter(stream.readline, ''):
            self.output_queue.put((label, line.strip()))
            # print(f"[Raw {{label}}] {{line.strip()}}") # Debug echo

    def wait_for_prompt(self, timeout=10):
        # Consume output until we see the "You:" prompt
        start = time.time()
        buffer = ""
        while time.time() - start < timeout:
            try:
                label, line = self.output_queue.get(timeout=0.5)
                buffer += line
                if "You:" in line:
                    return True
            except queue.Empty: pass
        return False

    def send_input(self, text):
        if not self.process: return
        print(f"[Controller] Sending: '{{text}}'")
        self.process.stdin.write(text + "\\n")
        self.process.stdin.flush()

    def get_status(self):
        # Native integration check
        self.send_input("__STATUS__")
        # Collect lines looking for JSON block
        start = time.time()
        json_buffer = ""
        in_json = False
        while time.time() - start < 5:
            try:
                label, line = self.output_queue.get(timeout=0.5)
                if "[STATUS PROBE]" in line:
                    in_json = True
                    continue
                if in_json:
                    json_buffer += line
                    if line.strip() == "}}": # End of JSON
                        try:
                            return json.loads(json_buffer)
                        except: return {{"error": "Invalid JSON status"}}
            except queue.Empty: pass
        return {{"error": "Timeout waiting for status"}}

    def terminate(self):
        if self.process: self.process.terminate()

def run_suite():
    target = "{target_script}"
    if not os.path.exists(target):
        print(f"Target {{target}} not found.")
        return

    agent = AgentController(target)
    agent.start()
    
    try:
        if agent.wait_for_prompt(20):
            print("✓ Agent started and prompted for input.")
        else:
            print("✗ Agent failed to prompt (Startup Timeout).")
            return

        # 1. Test Status Probe
        print("\\n--- Testing Native Status Probe ---")
        status = agent.get_status()
        print(f"Status Result: {{status}}")
        if "metrics" in status:
            print("✓ Native status probe functional.")
        else:
            print("✗ Status probe failed.")

        # 2. Test Basic Interaction
        print("\\n--- Testing Quick Interaction ---")
        agent.wait_for_prompt(5)
        agent.send_input("Hello, this is a verify_work test.")
        
        # We just want to see it acknowledge, not wait for full turn
        # In a real suite we'd parse the response
        time.sleep(2)
        print("✓ Interaction sent (Async check).")

    finally:
        agent.terminate()
        print("\\n[Controller] Test Suite Completed.")

if __name__ == "__main__":
    run_suite()
"""
        try:
            test_dir = Path("development_files")
            test_dir.mkdir(exist_ok=True)
            wrapper_path = test_dir / "wrapper_script.py"
            wrapper_path.write_text(script_content, encoding="utf-8")
            
            print(f"{Colors.YELLOW}[Verification] Running suite against {target_script}...{Colors.ENDC}")
            # Ensure target exists, or create a dummy if missing to prevent crash
            if not Path(target_script).exists():
                return f"Target script '{target_script}' does not exist. Cannot verify."

            res = self.run_bash(f"python \"{wrapper_path}\"")
            verification = self.verify_and_report(res, context=f"verify:{target_script}")
            return f"{res}\n\nVerification Summary: {verification.get('summary')}"
        except Exception as e:
            ErrorHandler.log(e, context="tool_run_verification")
            return f"Verification failed: {e}"

    def tool_see_image(self, image_path: str, question: str = "Describe this image."):
        """Analyzes an image file using the vision capabilities of the LLM."""
        path = Path(image_path)
        if not path.exists(): return f"Image file not found: {image_path}"
        
        try:
            # 1. Base64 Encode
            with open(path, "rb") as image_file:
                base64_image = base64.b64encode(image_file.read()).decode('utf-8')

            # 2. Construct Payload (gpt-5-mini Vision Format)
            messages = [
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": question},
                        {"type": "image_url", "image_url": {"url": f"data:image/jpeg;base64,{base64_image}"}}
                    ]
                }
            ]
            
            # 3. Call API
            print(f"{Colors.YELLOW}[Vision] Analyzing {path.name}...{Colors.ENDC}")
            res = self.client.chat(messages)
            return f"Image Analysis ({path.name}): {res['choices'][0]['message']['content']}"
        except Exception as e:
            ErrorHandler.log(e, context="tool_see_image")
            return f"Vision Error: {e}"

    def tool_list_windows(self, filter_text: str = None):
        """Lists open windows (Windows mostly). Returns JSON. Filter by title optional."""
        
        deps = SystemAutomation.check_dependencies()
        if deps: return f"Missing dependencies: {', '.join(deps)}"

        try:
            windows = SystemAutomation.get_open_windows(filter_text)
            return json.dumps(windows, indent=2)
        except Exception as e:
            ErrorHandler.log(e, context="tool_list_windows")
            return f"Failed to list windows: {e}"

    def tool_capture_window(self, query: str, output_path: str = None):
        """Captures a screenshot of a window by title (query). Returns path."""
        # Backwards-compatible simple capture (Windows-focused)
        if os.name != 'nt': return "Tool only available on Windows."
        
        final_path = output_path if output_path else f"window_capture_{int(time.time())}.png"
        
        try:
            res = SystemAutomation.capture_window(query, final_path)
            if res == "Success":
                 self.must_wait_for_observation = True
                 return f"✓ Screenshot saved to {final_path}. Use <ack_observation> to proceed."
            return f"Capture failed: {res}"
        except Exception as e:
            ErrorHandler.log(e, context="tool_capture_window")
            return f"Failed to run capture_window: {e}"

    def tool_capture_window_advanced(self, title: str = None, process: str = None, output_path: str = None, list_on_miss: bool = False, print_base64: bool = False, base64_single_line: bool = False):
        """Advanced capture that works natively or via system automation. Logic merged from capture_window.py."""
        final_path = output_path if output_path else f"window_capture_{int(time.time())}.png"
        query = title or process

        try:
            # Attempt Native Windows Capture (Currently only Windows supported natively for capture)
            if os.name == 'nt':
                res = SystemAutomation.capture_window(query=query, output_path=final_path, title_query=title, process_query=process)
                if res == "Success":
                    msg = f"✓ Screenshot saved to {final_path} (Native)"
                    
                    # Handle Base64 output if requested
                    b64_str = ""
                    if print_base64:
                        with open(final_path, "rb") as f:
                            b64_bytes = base64.b64encode(f.read())
                            b64_str = b64_bytes.decode("ascii")
                            if not base64_single_line:
                                # Wrap at 76 chars
                                b64_str = "\n".join([b64_str[i:i+76] for i in range(0, len(b64_str), 76)])
                            msg += f"\n--- BASE64 IMAGE START ---\n{b64_str}\n--- BASE64 IMAGE END ---\n"

                    self.must_wait_for_observation = True
                    return {"result": msg, "path": final_path, "base64": b64_str if print_base64 else None}
                else:
                    msg = f"Native capture failed: {res}."
                    if list_on_miss:
                        wins = SystemAutomation.get_open_windows(query)
                        if wins:
                            msg += "\nSimilar windows found:\n" + "\n".join([f" - {w['title']} ({w.get('process_name', 'Unknown')})" for w in wins[:10]])
                        else:
                            all_wins = SystemAutomation.get_open_windows()
                            msg += "\nNo similar windows found. Open windows:\n" + "\n".join([f" - {w['title']}" for w in all_wins[:15]])
                    
                    self.must_wait_for_observation = True
                    return {"result": msg, "path": None}

            return {"result": "Capture not supported on this platform natively.", "path": None}

        except Exception as e:
            ErrorHandler.log(e, context="tool_capture_window_advanced")
            return {"result": f"Capture failed: {e}", "path": None}

    def tool_see_window(self, query: str, question: str = "What is visible in this window?"):
        """Captures a window and immediately analyzes it with vision."""
        temp_path = f"temp_vision_capture_{int(time.time())}.png"
        try:
            print(f"{Colors.YELLOW}[See Window] Capturing '{query}'...{Colors.ENDC}")
            cap_res = SystemAutomation.capture_window(query, temp_path)
            if cap_res != "Success":
                return f"Error: Could not capture window '{query}': {cap_res}"
            
            desc = self.tool_see_image(temp_path, question)
            
            # Clean up temp file
            try: os.remove(temp_path)
            except: pass
            
            return desc
        except Exception as e:
            return f"Error in see_window: {e}"

    def tool_see_screen(self, question: str = "What is visible on the screen?"):
        """Captures the entire screen and immediately analyzes it with vision."""
        temp_path = f"temp_screen_capture_{int(time.time())}.png"
        try:
            print(f"{Colors.YELLOW}[See Screen] Capturing full screen...{Colors.ENDC}")
            cap_res = SystemAutomation.capture_window(output_path=temp_path)
            if cap_res != "Success":
                return f"Error: Could not capture screen: {cap_res}"
            
            desc = self.tool_see_image(temp_path, question)
            
            # Clean up temp file
            try: os.remove(temp_path)
            except: pass
            
            return desc
        except Exception as e:
            return f"Error in see_screen: {e}"

    def tool_list_windows_advanced(self, filter_text: str = None, format: str = 'json'):
        """List open windows using native system automation logic. Logic merged from get_open_windows.py.
        format: 'json', 'table', or 'simple'"""
        try:
            # SystemAutomation now handles Windows, macOS, and Linux
            if not SystemAutomation.check_dependencies():
                wins = SystemAutomation.get_open_windows(filter_text)
                
                # Safety Limit: Only return top 100 windows to prevent context/memory crash
                if len(wins) > 100:
                    wins = wins[:100]
                    note = f"\n(Truncated list: Showing first 100 of {len(wins)} windows)"
                else:
                    note = ""
                
                return json.dumps(wins, indent=2) + note

            return "Required dependencies for native window listing are missing."
        except Exception as e:
            ErrorHandler.log(e, context="tool_list_windows_advanced")
            return f"Failed to list windows: {e}"


    def tool_get_active_terminal(self):
        """Returns metadata about the active terminal environment."""
        info = get_terminal_environment()
        return json.dumps(info, indent=2)

    def tool_find_consuming_port(self, port: int):
        """Finds which PID is holding a port and returns details."""
        return SystemAutomation.find_consuming_port(port)

    def tool_spawn_background(self, cmd: str, stop_marker: str = None, timeout: int = 30):
        """Spawns a background process and waits for a stop_marker (blocking) or just returns PID.
        Registers the process in state for persistence."""
        print(f"\n[System]: Spawning background process: {cmd}")
        decision = self.execution_policy.evaluate(
            "spawn_background",
            cmd,
            requested_timeout=timeout,
            active_background_processes=len(self.state.active_processes),
        )
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=cmd)
            return f"Execution blocked: {decision.reason}"

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=cmd)
        log_path = self._bg_task_log_path(f"shell_{int(start_time * 1000)}")
        try:
            # We use subprocess.Popen to let it run in the background
            p = subprocess.Popen(
                cmd, 
                shell=True, 
                stdout=subprocess.PIPE, 
                stderr=subprocess.STDOUT, 
                text=True, 
                bufsize=1,
                encoding='utf-8',
                errors='replace',
                **self.execution_policy.subprocess_kwargs(decision),
            )
            log_path = self._bg_task_log_path(p.pid)
            
            # Register in state
            pid_str = str(p.pid)
            self.state.set_active_process(pid_str, {
                "cmd": cmd,
                "start_time": time.time(),
                "type": "shell",
                "status": "running",
                "log_path": str(log_path),
                "working_directory": decision.isolation_rules.get("working_directory", "."),
            }, persist=False)
            self.state.save()
            
            if not stop_marker:
                msg = f"✓ Started background process with PID {p.pid} (Registered in State)"
                self.execution_policy.audit(
                    decision,
                    action="finish",
                    status="completed",
                    payload=cmd,
                    result=msg,
                    duration_ms=int((time.time() - start_time) * 1000),
                    extra={"pid": p.pid},
                )
                # Start a non-blocking consumer to keep pipe clear
                def drain(proc):
                    try:
                        with open(log_path, "a", encoding="utf-8", errors="replace") as log_file:
                            while proc.poll() is None:
                                line = proc.stdout.readline()
                                if not line:
                                    break
                                log_file.write(line)
                                log_file.flush()
                    except: pass
                threading.Thread(target=drain, args=(p,), daemon=True).start()
                return msg
            
            # Non-blocking wait logic (Polled for the timeout duration)
            start_time = time.time()
            captured = []
            with open(log_path, "a", encoding="utf-8", errors="replace") as log_file:
                while time.time() - start_time < decision.timeout_seconds:
                    line = p.stdout.readline()
                    if not line:
                        break
                    log_file.write(line)
                    log_file.flush()
                    captured.append(line.strip())
                    if stop_marker in line:
                        msg = f"✓ Process reached '{stop_marker}'. Substituted into memory."
                        self.tool_remember("processes", f"Spawned '{cmd}' - Ready seen at {time.ctime()}")
                        self.state.log_event("system", f"Background process '{cmd}' reached marker '{stop_marker}'.")
                        result = self.execution_policy.trim_output(decision, f"Success: Process reached marker. Last few lines:\n" + "\n".join(captured[-5:]))
                        self.execution_policy.audit(
                            decision,
                            action="finish",
                            status="completed",
                            payload=cmd,
                            result=result,
                            duration_ms=int((time.time() - start_time) * 1000),
                            extra={"pid": p.pid, "stop_marker": stop_marker, "log_path": str(log_path)},
                        )
                        return result
            
            result = f"Started background process (PID {p.pid}), but marker '{stop_marker}' was not seen in {decision.timeout_seconds}s. It continues to run."
            self.execution_policy.audit(
                decision,
                action="finish",
                status="completed",
                payload=cmd,
                result=result,
                duration_ms=int((time.time() - start_time) * 1000),
                extra={"pid": p.pid, "stop_marker": stop_marker, "log_path": str(log_path)},
            )
            return result
        except Exception as e:
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=cmd,
                result=str(e),
                duration_ms=int((time.time() - start_time) * 1000),
            )
            ErrorHandler.log(e, context="tool_spawn_background")
            return f"Spawn error: {e}"

    def tool_run_python_bg(self, code: str):
        """Writes Python code to a temp file and runs it in a detached background process.
        Returns the PID. This is safer for unstable scripts."""
        decision = self.execution_policy.evaluate(
            "run_python_bg",
            code,
            active_background_processes=len(self.state.active_processes),
        )
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=code)
            return f"Execution blocked: {decision.reason}"

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=code)
        try:
            ts = int(time.time())
            task_dir = Path("temp_tasks")
            task_dir.mkdir(exist_ok=True)
            script_path = task_dir / f"task_{ts}.py"
            
            # Add some preamble imports to help standalone scripts
            safe_code = "import sys, os, time\ntry:\n    import flexi\nexcept: pass\n\n" + code
            script_path.write_text(safe_code, encoding="utf-8")
            
            # Launch
            cmd = f'"{sys.executable}" "{script_path}"'
            p = subprocess.Popen(
                cmd, 
                shell=True,
                creationflags=subprocess.CREATE_NEW_CONSOLE if os.name == 'nt' else 0,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding='utf-8',
                errors='replace',
                **self.execution_policy.subprocess_kwargs(decision),
            ) 
            log_path = self._bg_task_log_path(p.pid)
            
            # Register
            self.state.set_active_process(str(p.pid), {
                "cmd": f"python {script_path.name}",
                "start_time": time.time(),
                "type": "python_bg",
                "script_path": str(script_path),
                "status": "running",
                "log_path": str(log_path),
                "working_directory": decision.isolation_rules.get("working_directory", "."),
            }, persist=False)
            self.state.save()
            def drain(proc):
                try:
                    with open(log_path, "a", encoding="utf-8", errors="replace") as log_file:
                        while proc.poll() is None:
                            line = proc.stdout.readline()
                            if not line:
                                break
                            log_file.write(line)
                            log_file.flush()
                except Exception:
                    pass
            threading.Thread(target=drain, args=(p,), daemon=True).start()
            result = f"✓ Started Python Background Task. PID: {p.pid}. Script: {script_path}"
            self.execution_policy.audit(
                decision,
                action="finish",
                status="completed",
                payload=code,
                result=result,
                duration_ms=int((time.time() - start_time) * 1000),
                extra={"pid": p.pid, "script_path": str(script_path), "log_path": str(log_path)},
            )
            return result
        except Exception as e:
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=code,
                result=str(e),
                duration_ms=int((time.time() - start_time) * 1000),
            )
            return f"Failed to spawn background python: {e}"

    def tool_check_bg_tasks(self, clear_finished: bool = True):
        """Checks the status of all registered background processes."""
        active = self.state.active_processes
        if not active: return "No background tasks registered."
        
        report = []
        to_remove = []
        
        try:
            import psutil
            for pid_str, info in active.items():
                pid = int(pid_str)
                try:
                    proc = psutil.Process(pid)
                    status = proc.status()
                    report.append(f"PID {pid} ({info.get('type')}): RUNNING ({status}) | Cmd: {info.get('cmd')}")
                except psutil.NoSuchProcess:
                    report.append(f"PID {pid} ({info.get('type')}): FINISHED/GONE | Cmd: {info.get('cmd')}")
                    to_remove.append(pid_str)
        except ImportError:
            return "Error: psutil missing. Cannot check PIDs."
            
        if clear_finished:
            for pid_str in to_remove:
                self.state.remove_active_process(pid_str, persist=False)
            self.state.save()
            
        return "\n".join(report)

    def _check_code_safety(self, code: str) -> str:
        """Evaluates code safety using heuristics and LLM audit."""
        if not isinstance(code, str):
            code = repr(code)
        # 1. Static Heuristics (Fast path for common automation ops that are risky)
        risky_keywords = ["os.system", "subprocess", "shutil.rmtree", "exec(", "eval("]
        is_risky = any(k in code for k in risky_keywords)
        
        # If it looks simple/safe, skip expensive LLM check? 
        # User requested "runs a check with the llm given the requirement" implies we should verify.
        # But for speed, maybe only verify if heuristics trigger OR users asks for strict mode.
        # For now, let's trigger on risky keywords OR file writes.
        if not is_risky and "open(" not in code and ".write" not in code:
            return "SAFE"

        # 2. LLM Audit
        try:
            # Context: Last user message
            last_msg = next((m["content"] for m in reversed(self.state.history) if m["role"] == "user"), "Unknown Task")
            
            prompt = (
                f"You are a Code Safety Auditor. Analyze this Python code given the user request.\n"
                f"REQUEST: {last_msg[:500]}\n"
                f"CODE:\n{code[:2000]}\n\n"
                f"Task: Determine if this code is malicious or destructive beyond the scope of the request. "
                f"Standard file operations, subprocess calls, and automation tasks explicitly requested by the user are SAFE. "
                f"Only flag unexpected destruction or exfiltration.\n"
                f"Return ONLY the string 'SAFE' or 'UNSAFE: <concise_reason>'."
            )
            
            # Minimal direct call
            resp = self.client.chat([{"role": "system", "content": prompt}])
            # Access response properly based on provider format (all normalized to choices/message/content by client wrapper)
            result = resp["choices"][0]["message"]["content"].strip()
            
            if "UNSAFE" in result.upper():
                return result
            return "SAFE"
        except Exception as e:
            # If audit fails, default to warning user
            return f"UNSAFE: Safety audit failed ({e})"

    PYTHON_EXEC_TIMEOUT = 60  # seconds default

    def run_python(self, code: str) -> str:
        decision = self.execution_policy.evaluate("python", code, requested_timeout=self.PYTHON_EXEC_TIMEOUT)
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=code)
            return f"Execution blocked: {decision.reason}"

        try:
            self._run_tool_hook('pre', 'python', code)
        except Exception:
            pass

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=code)
        try:
            ast.parse(code)
        except SyntaxError as err:
            result = self._format_python_syntax_error(code, err)
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=code,
                result=result,
                duration_ms=int((time.time() - start_time) * 1000),
                extra={
                    "stage": "syntax_precheck",
                    "lineno": err.lineno,
                    "offset": err.offset,
                    "msg": err.msg,
                },
            )
            self._append_response_trace(
                "python_syntax_reject",
                payload=code,
                error=result,
                lineno=err.lineno,
                offset=err.offset,
                message=err.msg,
            )
            return result

        def _execute():
            orig_code = code
            # keep a mutable copy for possible AST transformation
            exec_code = code
            # --- SAFETY CHECK ---
            if not self.state.get_runtime_value("safety_always_allow", False):
                safety_res = self._check_code_safety(orig_code)
                if safety_res.upper() != "SAFE":
                    print(f"\n{Colors.RED}[Safety Check] Warning: Code flagged as potential risk.{Colors.ENDC}")
                    print(f"Reason: {safety_res}")
                    print(f"{Colors.DIM}Code Start:\n{orig_code[:300]}...{Colors.ENDC}")
                    
                    try:
                        print(f"{Colors.YELLOW}Allow execution? (y/n/always): {Colors.ENDC}", end="", flush=True)
                        choice = input().lower().strip()
                    except EOFError:
                        return "Execution blocked (No Input)."
                    
                    if choice == RestartPolicy.ALWAYS:
                        self.state.set_runtime_value("safety_always_allow", True)
                        self.state.save()
                        print(f"{Colors.GREEN}Always-allow enabled for this session.{Colors.ENDC}")
                    elif choice != "y":
                        return "Execution blocked by user."
            
            with self._state_lock:
                current_globals = self.state.globals.copy()
            
            stdout_buf = io.StringIO()
            
            def _bridge_subagent(task, priority=2, agent_type="generic"):
                return self.subagent(task, priority=priority, agent_type=agent_type)
            
            def _register_subagent(name, cls, description, capabilities=[]):
                return self.subagent_manager.register_agent_type(name, cls, description, capabilities)

            def _load_skill_shim(name): return self.tool_load_skill(name, env)

            def guarded_print(*args, **kwargs):
                if "file" in kwargs: builtins.print(*args, **kwargs); return
                sep = kwargs.get('sep', ' '); end = kwargs.get('end', '\n')
                stdout_buf.write(sep.join(map(str, args)) + end)

            env = {
                "print": guarded_print,
                **current_globals,
                "memory": self.state.memory,
                "remember": self.tool_remember,
                "recall": self.tool_recall,
                "search_memory": self.tool_search_memory,
                "save_skill": self.tool_save_skill,
                "load_skill": _load_skill_shim,
                # remaining original execution code continues...
                "register_subagent": _bridge_subagent,
                "verify_work": self.tool_run_verification,
                "see_image": self.tool_see_image,
                "see": self.tool_see_image,
                "see_window": self.tool_see_window,
            "see_screen": self.tool_see_screen,
            "capture_window": self.tool_capture_window,
            "capture_window_advanced": self.tool_capture_window_advanced,
            "list_windows_advanced": self.tool_list_windows_advanced,
            "get_active_terminal": self.tool_get_active_terminal,
            "list_processes": self.tool_list_processes,
            "get_software_versions": self.tool_get_software_versions,
            "spawn_background": self.tool_spawn_background,
            "spawn_bg": self.tool_spawn_background,
            "run_python_bg": self.tool_run_python_bg,
            "check_bg_tasks": self.tool_check_bg_tasks,
                "get_bg_task_details": self.tool_get_bg_task_details,
                "read_bg_task_log": self.tool_read_bg_task_log,
                "stop_bg_task": self.tool_stop_bg_task,
                "restart_bg_task": self.tool_restart_bg_task,
            "find_consuming_port": self.tool_find_consuming_port,
            "find_port": self.tool_find_consuming_port,
                "validate_python": self.tool_validate_python,
                "validate_json": self.tool_validate_json,
                "validate_python_snippet": self.tool_validate_python_snippet,
                "run_tests": self.tool_run_tests,
                "inspect_python_environment": self.tool_inspect_python_environment,
                "list_python_packages": self.tool_list_python_packages,
                "install_python_package": self.tool_install_python_package,
                "python_symbol_doc": self.tool_python_symbol_doc,
                "python_import_graph": self.tool_python_import_graph,
                "python_refactor_symbol": self.tool_python_refactor_symbol,
                "cleanup_unused_imports": self.tool_python_cleanup_unused_imports,
                "python_type_assist": self.tool_python_type_annotation_assist,
                "find_references": self.tool_find_references,
                "find_implementations": self.tool_find_implementations,
                "preview_symbol_rename": self.tool_preview_symbol_rename,
                "git_changed_files": self.tool_git_changed_files,
                "git_diff_analysis": self.tool_git_diff_analysis,
                "git_blame_context": self.tool_git_blame_context,
                "git_commit_message_draft": self.tool_git_commit_message_draft,
                "project_map_tool": self.tool_project_map,
                "project_relationships": self.tool_project_relationships,
                "notebook_summary": self.tool_notebook_summary,
                "notebook_edit_cell": self.tool_notebook_edit_cell,
                "notebook_run": self.tool_notebook_run,
                "notebook_kernel_info": self.tool_notebook_kernel_info,
                "notebook_session_status": self.tool_notebook_session_status,
                "notebook_clear_session": self.tool_notebook_clear_session,
                "notebook_install_package": self.tool_notebook_install_package,
                "db_save_profile": self.tool_db_save_profile,
                "db_list_profiles": self.tool_db_list_profiles,
                "db_schema": self.tool_db_schema,
                "db_query": self.tool_db_query,
                "db_migration_status": self.tool_db_migration_status,
                "fetch_webpage": self.tool_fetch_webpage,
                "extract_web_structure": self.tool_extract_web_structure,
                "extract_doc_section": self.tool_extract_doc_section,
                "summarize_web_reference": self.tool_summarize_web_reference,
                "research_web": self.tool_research_web,
                "git_review_summary": self.tool_git_review_summary,
            # RLM Helpers
            "grep": rlm_grep,
            "search_workspace": rlm_search_workspace,
            "find_symbol": rlm_find_symbol,
            "peek": rlm_peek,
            "read_file": rlm_read,
            "read_range": rlm_read_range,
            "write": rlm_write,
            "create_file": rlm_create_file,
            "delete_file": rlm_delete_file,
            "move_file": rlm_move_file,
            "patch": rlm_patch,
            "edit_lines": rlm_edit_lines,
            "find_files": rlm_find_files,
            "tree": rlm_tree,
            "read_metadata": rlm_read_metadata,
            "history_search": rlm_history_search,
            "map_deps": rlm_map_dependencies,
            "project_map": rlm_project_summary,
            "project_map_structured": rlm_project_map,
            "project_relationships_raw": rlm_project_relationships,
            "validate_python_file": rlm_validate_python,
            "validate_json_file": rlm_validate_json,
            "git_diff": rlm_git_diff_summary,
            "git_summary": rlm_git_diff_summary,
            "git_blame": rlm_git_blame_context,
            "git_changed_files_raw": rlm_git_changed_files,
            "git_diff_analysis_raw": rlm_git_diff_analysis,
            "git_commit_message_draft_raw": rlm_git_commit_message_draft,
            "notebook_summary_raw": rlm_notebook_summary,
            "notebook_edit_cell_raw": rlm_notebook_edit_cell,
            "notebook_run_raw": rlm_notebook_run,
            "notebook_kernel_info_raw": rlm_notebook_kernel_info,
            "notebook_session_status_raw": rlm_notebook_session_status,
            "notebook_clear_session_raw": rlm_notebook_clear_session,
            "notebook_install_package_raw": rlm_notebook_install_package,
            "db_save_profile_raw": rlm_db_save_profile,
            "db_list_profiles_raw": rlm_db_list_profiles,
            "db_schema_raw": rlm_db_schema,
            "db_query_raw": rlm_db_query,
            "db_migration_status_raw": rlm_db_migration_status,
            "fetch_webpage_raw": rlm_fetch_webpage,
            "extract_web_structure_raw": rlm_extract_web_structure,
            "extract_doc_section_raw": rlm_extract_doc_section,
            "summarize_web_reference_raw": rlm_summarize_web_reference,
            "research_web_raw": rlm_research_web,
            "git_review_summary_raw": rlm_git_review_summary,
            "to_clip": rlm_to_clipboard,
            "from_clip": rlm_from_clipboard,
            "python_symbol_doc_raw": rlm_python_symbol_doc,
            "python_import_graph_raw": rlm_python_import_graph,
            "python_refactor_symbol_raw": rlm_python_refactor_symbol,
            "cleanup_unused_imports_raw": rlm_python_cleanup_unused_imports,
            "python_type_assist_raw": rlm_python_type_annotation_assist,
            "find_references_raw": rlm_find_references,
            "find_implementations_raw": rlm_find_implementations,
            "preview_symbol_rename_raw": rlm_preview_symbol_rename,
            "rlm_see": self.tool_see_image,
            "rlm_see_window": self.tool_see_window,
            # New Capabilities
            "subagent": _bridge_subagent,
            "Subagent": Subagent, # Export base class for subclassing
            "ThreadPoolExecutor": ThreadPoolExecutor, # For async patterns
            # Export core helpers for skill writing
            "BaseSkill": BaseSkill,
            "json": json,
            "shutil": shutil,
            "pickle": pickle
        }
            
            # AST Magic to auto-print the last expression (REPL-like behavior) 
            try:
                tree = ast.parse(exec_code)
                if tree.body and isinstance(tree.body[-1], ast.Expr):
                    # Wrap the last expression in print()
                    last_expr = tree.body[-1]
                    print_call = ast.Expr(
                        value=ast.Call(
                            func=ast.Name(id='print', ctx=ast.Load()),
                            args=[last_expr.value],
                            keywords=[]
                        )
                    )
                    ast.fix_missing_locations(print_call)
                    tree.body[-1] = print_call
                    exec_code = compile(tree, filename="<string>", mode="exec")     
            except Exception:
                    # If AST parsing fails, just execute original code (might be syntax error, let exec handle it)
                    pass

            # execute the user code and capture any exception
            try:
                exec(exec_code, env, env)
            except Exception as e:
                # re-raise so the outer executor can catch and report
                raise
            # Persist globals via AgentState's SQLite-backed safe serializer.
            with self._state_lock:
                new_globals = {}
                for k, v in env.items():
                    if k in ["re", "os", "json", "shutil", "pickle", "__builtins__"]:
                        continue
                    if callable(v) or isinstance(v, type(sys)):
                        continue
                    try:
                        new_globals[k] = v
                    except Exception:
                        pass
                max_globals = int(decision.resource_ceilings.get("max_globals", 256))
                if len(new_globals) > max_globals:
                    new_globals = dict(list(new_globals.items())[:max_globals])
                self.state.globals = new_globals
                self.state.save()
            return self.execution_policy.trim_output(decision, stdout_buf.getvalue())
            # end of _execute
        # run with timeout in executor
        def _execute_core(raw_code: str) -> str:
            nonlocal code
            code = raw_code
            result = ""
            with ThreadPoolExecutor(max_workers=1) as executor:
                future = executor.submit(_execute)
                try:
                    result = future.result(timeout=decision.timeout_seconds)
                except Exception as e:
                    if isinstance(e, TimeoutError):
                        result = f"[System] Error: Python execution timed out ({decision.timeout_seconds}s)"
                    else:
                        result = f"[System] Execution failed: {e}"
            return result

        result = self._run_tool_with_wrapper('python', code, _execute_core)
        self.execution_policy.audit(
            decision,
            action="finish",
            status="failed" if self._tool_result_failed(result) else "completed",
            payload=code,
            result=result,
            duration_ms=int((time.time() - start_time) * 1000),
        )
        # post-tool hook
        try:
            self._run_tool_hook('post', 'python', result)
        except Exception:
            pass
        return result
        # end of run_python

    def get_system_prompt(self) -> str:
        summary_text = self.state.compressed_summary
        summary_block = f"\nTECHNICAL BACKGROUND (SUMMARY): {summary_text}" if summary_text else ""
        
        # System Info Injection
        sys_info = f"OS: {os.name} | Platform: {sys.platform}"
        if os.name == 'nt': sys_info += " (Windows)"
        else: sys_info += " (Linux/Unix)"
        
        # Environmental Context
        cwd = os.getcwd()
        py_path = sys.executable
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        try: user = os.getlogin()
        except: user = os.environ.get("USER", "unknown")
        
        env_context = (f"   - **Environment**: CWD='{cwd}' | User='{user}' | Time='{timestamp}'\n"
                       f"   - **Runtime**: Python='{py_path}'")

        # Memory Intelligence
        mem = self.state.structured_memory
        
        available_agents = ", ".join(self.subagent_manager.agent_registry.keys())
        
        mem_keys = list(mem.keys())
        mem_hint = ""
        if mem_keys:
            mem_hint = f"\n   - **🧠 Known Memory Tags**: {', '.join(mem_keys)} (Use `recall(tag)` to read)"
            for key in ["user", "user_profile", "name", "identity"]:
                if key in mem:
                    info = "; ".join(mem[key])
                    mem_hint += f"\n   - **Active Context ({key})**: {info[:300]}"

        # Tool Documentation
        tools_doc = (
            "   - **Terminal**: Use <bash>cmd</bash> for shell commands.\n"
            "   - **Code Engine**: Use <python>code</python> for script logic.\n"
            "   - **Vision**: `see(path, question)`, `see_window(query, question)`, `see_screen(question)`, `capture_window(query)`.\n"
            "   - **Windows/Env**: `list_windows_advanced()`, `list_processes()`, `get_software_versions()`, `find_port(port)`.\n"
            "   - **Background**: `spawn_bg(cmd)`, `run_python_bg(code)`, `check_bg_tasks()`, `get_bg_task_details(pid='')`, `read_bg_task_log(pid)`, `stop_bg_task(pid)`, `restart_bg_task(pid)`.\n"
            "   - **Environment**: `inspect_python_environment()`, `list_python_packages()`, `install_python_package(name, upgrade=False)`, `get_software_versions()`.\n"
            "   - **Python Language**: `python_symbol_doc(name, filepath='', root='.')`, `python_import_graph(filepath, root='.')`, `validate_python_snippet(code, mode='exec')`, `python_refactor_symbol(filepath, old_name, new_name, apply=False)`, `cleanup_unused_imports(filepath, apply=False)`, `python_type_assist(filepath)`.\n"
            "   - **Git/Project**: `git_changed_files(repo='.')`, `git_diff_analysis(repo='.', src='HEAD', dst='')`, `git_commit_message_draft(repo='.')`, `git_blame_context(file, line, repo='.')`, `git_review_summary(repo='.')`, `git_diff(repo, src, dst)`, `git_summary(repo)`, `map_deps(path)`, `project_map(root)`, `project_map_tool(root='.')`, `project_relationships(root='.')`.\n"
            "   - **Notebook**: `notebook_summary(path)`, `notebook_edit_cell(path, index, source='', cell_type='code', operation='replace')`, `notebook_run(path, cell_index=None, persist_output=True)`, `notebook_kernel_info(path)`, `notebook_session_status(path)`, `notebook_clear_session(path)`, `notebook_install_package(path, package, upgrade=False)`.\n"
            "   - **Database**: `db_save_profile(name, database_path, kind='sqlite')`, `db_list_profiles()`, `db_schema(profile_name='', database_path='')`, `db_query(query, profile_name='', database_path='')`, `db_migration_status(root='.')`.\n"
            "   - **Web/Docs**: `fetch_webpage(url)`, `extract_web_structure(url)`, `extract_doc_section(url, query)`, `summarize_web_reference(url)`, `research_web(query, urls=None)`.\n"
            "   - **Utility**: `to_clip(text)`, `from_clip()`.\n"
            "   - **State**: Variables persist; `remember(tag, txt)`, `recall(tag)`, `search_memory(query)`.\n"
            "   - **Search**: `search_workspace(query, root='.', pattern='*')`, `find_symbol(name, root='.', pattern='*.py')`, `find_references(name, root='.', patterns='')`, `find_implementations(name, root='.', patterns='')`, `preview_symbol_rename(old, new, root='.', patterns='')`, `grep(pattern, file)`, `find_files(glob)`, `tree(root)`.\n"
            "   - **Filesystem**: `read_file(path)`, `read_range(path, start, end)`, `write(path, content)`, `create_file(path, content, overwrite=False)`, `move_file(src, dst)`, `delete_file(path)`, `patch(path, old, new)`, `edit_lines(path, s, e, txt)`, `peek(file)`.\n"
            "   - **Validation**: `validate_python(filepath='', code='')`, `validate_python_snippet(code, mode='exec')`, `validate_json(filepath='', content='')`, `run_tests(command='')`, `verify_work(script_path)`.\n"
            "   - **Recursion**: `subagent(task, agent_type='generic')` spawns a bot. Types: [" + available_agents + "].\n"
            "   - **Background**: `batch_implement(proposal_file)` runs tasks in `subies/`; `check_subagents()` to monitor progress."
        )

        capability_lines = []
        for skill_name, capabilities in sorted(self.skill_capabilities.items()):
            if capabilities:
                capability_lines.append(f"   - **Skill `{skill_name}`**: {', '.join(capabilities)}")
        skill_capability_block = "\n" + "\n".join(capability_lines) if capability_lines else ""
        skill_prompt_block = self._render_skill_prompt_sections()

        return (f"You are FlexiBot, a recursive automation agent.\n"
                f"SYSTEM INFO: {sys_info}.\n"
                f"{env_context}\n\n"
                f"AVAILABLE TOOLS (Access via <python>): \n{tools_doc}\n\n"
            f"DECLARED SKILLS:{skill_capability_block}\n"
                f"INSTRUCTIONS:\n"
                f"1. Use <plan> to outline steps.\n"
                f"2. Use <bash> or <python> for execution.\n"
                f"3. **STRICT**: ONLY use <bash>, <python>, or <plan> tags. To run functions, use <python>tool_name()</python>.\n"
                f"4. **LOCKING**: If the system says 'Awaiting Acknowledgement', you MUST output <ack_observation> to unlock the turn.\n"
                f"5. **VALIDATION**: If you write code, you MUST wait for turn output before calling <consensus>.\n"
                f"6. **INTERACTION**: To ask the user a question or present a menu, use <consensus>Question text...</consensus>. DO NOT print menus with <python> and wait.\n"
                f"7. **FINALITY**: Use <consensus>final response</consensus> ONLY when the task is complete.\n"
            f"{summary_block}{mem_hint}{skill_prompt_block}")

    def handle_turn(self, user_input: str):
        # convenience getters for skills/prompts
        def recent_user(n=3):
            return [e["content"] for e in self.state.query_history(role="user", limit=n)]
        def recent_plans(n=5):
            return [e["content"] for e in self.state.query_history(tag="plan", limit=n)]
        def facts_matching(pattern):
            return [e for e in self.state.query_history(tag="fact") if pattern in e["content"]]

        try:
            # Periodic Summary Check
            if self.state.total_tokens > TOKEN_THRESHOLD:
                self.compress_context()

            self.state.take_snapshot(label="pre_turn")
            self.state.log_event("user", user_input)
            # also record the user prompt in the evolution log with metadata
            self.logger.log_user(user_input)
            # trigger any hooks for incoming user text
            try:
                self.on_user_input(user_input)
            except Exception:
                pass

            for _ in range(24):
                # increment global turn counter so each log entry gets a unique number
                self.turn_counter += 1
                turn_num = self.turn_counter
                turn_start = time.time()
                try:
                    turn_start_data = self.state.export_state()
                    
                    # --- CRITICAL FIX: Safe Context ---
                    # Even with compression, the "full" history might be malformed or too big.
                    # We enforce a hard limit on the # of messages passed to the API here.
                    MAX_MESSAGES = 12
                    recent_context = self.state.history[-MAX_MESSAGES:]
                    
                    # Ensure system prompt is always first
                    final_prompt = [{"role": "system", "content": self.get_system_prompt()}] + recent_context
                    
                    try:
                        resp_data = self.client.chat(final_prompt)
                        resp = resp_data["choices"][0]["message"]["content"]
                    except Exception as e:
                        # If we still hit a 400 even with truncated history, it's likely the generated response *request* 
                        # or a specific massive message in the last 12.
                        print(f"[System]: Context Error ({e}). Retrying with minimal context.")
                        # Extreme fallback: Just the system prompt and the very last message
                        resp_data = self.client.chat([
                            {"role": "system", "content": self.get_system_prompt()},
                            self.state.history[-1]
                        ])
                        resp = resp_data["choices"][0]["message"]["content"]

                    # Pretty print the thought process with clear sections
                    sep_line = f"{Colors.DIM}{'-'*60}{Colors.ENDC}"
                    print(f"\n{sep_line}")
                    
                    # Sanitise resp to prevent broken formatting
                    formatted_thought = resp.replace('\n', f'\n{Colors.DIM}| {Colors.ENDC}')
                    
                    print(f"{Colors.YELLOW}{Colors.BOLD}⚡ Thought:{Colors.ENDC}\n{Colors.DIM}| {Colors.ENDC}{formatted_thought}")
                    print(f"{sep_line}")

                    # 1. Extract Tools
                    bash = re.findall(r"<bash>(.*?)</bash>", resp, re.S)
                    py = re.findall(r"<python>(.*?)</python>", resp, re.S)
                    plan = re.findall(r"<plan>(.*?)</plan>", resp, re.S)
                    ack = "<ack_observation>" in resp
                    normalized_bash = [self._normalize_tool_payload(item) for item in bash]
                    normalized_py = [self._normalize_tool_payload(item) for item in py]
                    self._append_response_trace(
                        "llm_response",
                        response=resp,
                        bash_payloads=bash,
                        python_payloads=py,
                        plan_blocks=plan,
                        ack=ack,
                        consensus=("<consensus>" in resp),
                    )

                    # 2. Handle Acknowledgement Lock
                    if ack:
                        self.must_wait_for_observation = False
                        print(f"{Colors.CYAN}✓ Observation Acknowledged.{Colors.ENDC}")

                    # 3. Check for Hallucinated Consensus
                    has_tools = bool(bash or py)
                    if "<consensus>" in resp:
                        if self.must_wait_for_observation:
                            print(f"{Colors.RED}⚠️ Consensus blocked: Awaiting <ack_observation>.{Colors.ENDC}")
                            obs = "System Error: You attempted to finalize while an observation is pending. You MUST acknowledge the previous observation with <ack_observation> before you can use <consensus>."
                            self.state.log_event("system", obs)
                            continue

                        if has_tools:
                            # Agent tried to act and conclude simultaneously
                            print(f"{Colors.RED}⚠️ Mixed Consensus and Action detected. Prioritizing Action.{Colors.ENDC}")
                            obs_prefix = "System Warning: You provided <consensus> but also used tools. The consensus was IGNORED. You must wait for the tool output before finalizing.\n"
                        else:
                            # Valid pure consensus
                            draft = re.search(r"<consensus>(.*?)</consensus>", resp, re.S).group(1).strip()
                            self.state.log_event("assistant", draft)
                            # log consensus turn with metadata
                            dur = time.time() - turn_start
                            meta = ["consensus"]
                            # no tools used for pure consensus
                            self.logger.log_turn(turn_num, resp, self.state.calculate_diff(turn_start_data, self.state.data), ["consensus"], duration=dur, meta=meta)
                            return f"\n{Colors.CYAN}{Colors.BOLD}💡 Answer:{Colors.ENDC}\n{draft}"
                    else:
                        obs_prefix = ""

                    # 4. Execute Tools
                    obs = ""
                    for p in plan: 
                        print(f"{Colors.BLUE}📋 Plan:{Colors.ENDC} {p}")
                        obs += f"Plan: {p}\n" 
                    
                    for b in bash: 
                        print(f"{Colors.CYAN}💻 Bash:{Colors.ENDC} {b}")
                        res = self.run_bash(b)
                        print(f"{Colors.DIM}  -> Tool exit OK.{Colors.ENDC}")
                        obs += f"Bash: {res}\n"
                        try:
                            self.on_tool_output("bash", res)
                        except Exception:
                            pass
                    
                    for p in py:
                        print(f"{Colors.GREEN}🐍 Python:{Colors.ENDC} {p}")
                        out = self.run_python(p)
                        print(f"{Colors.DIM}  -> Tool exit OK.{Colors.ENDC}")
                        obs += f"Python: {out}\n"
                        if self._tool_result_failed(out):
                            print(f"{Colors.RED}❌ Tool Error detected.{Colors.ENDC}")
                            obs += "\nSYSTEM ALERT: ⚠️ An error occurred. Analyze and FIX the code.\n"
                        try:
                            self.on_tool_output("python", out)
                        except Exception:
                            pass
                    
                    if obs_prefix: obs = obs_prefix + obs

                    # 5. Loop Protection
                    is_exact_repeat = (resp == self.last_turn_resp)
                    is_tool_repeat = (has_tools and normalized_bash == self.last_tools.get('bash') and normalized_py == self.last_tools.get('py'))

                    if not ack and (is_exact_repeat or is_tool_repeat):
                        self.repetition_count += 1
                        if self.repetition_count >= 2:
                            print(f"{Colors.RED}⚠️ Repetitive Loop Detected.{Colors.ENDC}")
                            if self.repetition_count >= 4:
                                stop_msg = "System Error: Stopping after repeated identical actions without progress. Review .flexi/rlm_state/execution_audit.jsonl and .flexi/rlm_state/response_trace.jsonl for the last failing payloads."
                                self.state.log_event("system", stop_msg)
                                self.last_observation = stop_msg
                                self._append_response_trace(
                                    "loop_abort",
                                    response=resp,
                                    repetition_count=self.repetition_count,
                                    observation=stop_msg,
                                )
                                recovery = self._recover_from_turn_limit("Repeated identical actions without progress")
                                return f"{stop_msg}\n\n{recovery}"
                            obs = "System Error: You are repeating the same action. You MUST try a different approach or ask the user for help via <consensus>."
                            self.state.log_event("system", obs)
                    else:
                        self.repetition_count = 0
                    
                    self.last_turn_resp = resp
                    self.last_tools = {'bash': normalized_bash, 'py': normalized_py}

                    if not bash and not py and not ack:
                        if plan:
                            obs = "System Notification: You provided a <plan> but no executable tools. You must use <bash> or <python> to implement your plan, or <consensus> if complete."
                        else:
                            obs = "System Notification: No tools used. If done, use <consensus>. If acting, use <bash> or <python>. If an observation was just provided, use <ack_observation>."
                        self.state.log_event("system", obs)
                        continue

                    # --- CONTEXT OVERFLOW PROTECTION ---
                    if len(obs) > 4000:
                        print(f"{Colors.YELLOW}[System]: Observation too large ({len(obs)} chars). Truncating for history safety...{Colors.ENDC}")
                        truncated_obs = obs[:2000] + "\n... [TRUNCATED DUE TO SIZE] ...\n" + obs[-1000:]
                        self.last_observation = truncated_obs
                        self.state.log_event("system", f"Observation (Truncated): {truncated_obs}")
                    else:
                        self.last_observation = obs
                        self.state.log_event("system", f"Observation: {obs}")

                    # 6. Log and Continue
                    self.state.log_event("assistant", resp)
                    # log with the persistent turn number and include turn duration
                    dur = time.time() - turn_start
                    # build metadata tags
                    meta = []
                    if bash:
                        meta.append("tool:bash")
                    if py:
                        meta.append("tool:python")
                    if ack:
                        meta.append("ack:true")
                    if "consensus" in resp:
                        meta.append("consensus")
                    else:
                        meta.append("action")
                    self.logger.log_turn(turn_num, resp, self.state.calculate_diff(turn_start_data, self.state.data), [f"bash:{len(bash)}", f"python:{len(py)}", f"ack:{int(ack)}"], duration=dur, meta=meta)
                    # after recording the turn, maybe summarise old history
                    try:
                        self.auto_summarize_history()
                    except Exception:
                        pass
                except Exception as inner_e:
                    print(f"{Colors.RED}⚠️ Critical Turn Error: {inner_e}{Colors.ENDC}")
                    traceback.print_exc()
                    obs = f"System Error during turn execution: {inner_e}. Please retry."
                    self.state.log_event("system", obs)
            
            stop_msg = "Stopped after max turns without consensus."
            if self.last_observation:
                stop_msg += f"\nLast observation:\n{self.last_observation[:1500]}"
            self._append_response_trace(
                "turn_limit_abort",
                observation=self.last_observation,
                repetition_count=self.repetition_count,
            )
            recovery = self._recover_from_turn_limit("Maximum internal turns reached before consensus")
            return f"{stop_msg}\n\n{recovery}"
        except Exception as outer_e:
            return f"\n{Colors.RED}[CRITICAL HANDLER FAILURE]: {outer_e}{Colors.ENDC}\n{traceback.format_exc()}"

def clear_console():
    """Cross-platform console clear without using os.system directly."""
    try:
        if os.name == 'nt' and not os.environ.get('TERM'):
            # 'cls' is a cmd builtin; call it via cmd /c to avoid shell=True
            subprocess.run(["cmd", "/c", "cls"], check=False)
        else:
            # POSIX: use clear executable
            subprocess.run(["clear"], check=False)
    except Exception:
        # Best-effort: ignore failures to clear
        pass


def check_for_upgrades():
    """No-op in stripped build (self-evolution removed)."""
    pass


def configure_console(log_step):
    log_step("enter configure_console")
    check_for_upgrades()
    log_step("after check_for_upgrades")
    Colors.fix_windows_console()
    log_step("after fix_windows_console")
    clear_console()
    log_step("after clear_console")
    Colors.print_logo()
    log_step("after print_logo")
    ConsoleOutput.debug(f"stdin.isatty() -> {sys.stdin.isatty()}")
    log_step(f"stdin isatty {sys.stdin.isatty()}")


def handle_eof_mode(log_step):
    log_step("non-tty detected")
    ConsoleOutput.warning("stdin is not a TTY; interactive mode disabled.")
    ConsoleOutput.system("Press Ctrl+C to quit.")
    try:
        while True:
            time.sleep(60)
    except KeyboardInterrupt:
        pass


def bootstrap_runtime(log_step):
    log_step("tty confirmed")
    log_step("before history support check")
    if not HISTORY_SUPPORT and os.name == 'nt':
        log_step("history support missing")
        ConsoleOutput.system("Tip: Run `pip install pyreadline3` to enable Up-Arrow command history.")
    else:
        log_step("history support ok")

    log_step("before registering global error hooks")
    ErrorHandler.register_global_handler()
    log_step("after registering global error hooks")

    bot = FlexiBot()
    log_step("bot instantiated")
    ConsoleOutput.system(f"System initialized. Auto-Summary threshold: {TOKEN_THRESHOLD}")
    log_step("after bot init print")
    return bot


def start_input_thread(input_queue: queue.Queue):
    def input_worker():
        while True:
            try:
                input_queue.put(input())
            except EOFError:
                input_queue.put(None)
                break

    t = threading.Thread(target=input_worker, daemon=True)
    t.start()
    return t


def shutdown_runtime(bot: Optional[FlexiBot], reason: str = ""):
    if reason:
        ConsoleOutput.system(reason)
    if bot is not None:
        try:
            bot.unload_skills()
        except Exception:
            pass
        try:
            bot.state.close()
        except Exception:
            pass


def run_interactive_loop(bot: FlexiBot, input_queue: queue.Queue, log_step, idle_timeout: int = 300):
    stdin_closed = False
    log_step("enter input loop")
    while True:
        log_step("loop iteration start")
        ConsoleOutput.user_output("", end="")
        ConsoleOutput.prompt()

        last_activity = time.time()
        user_input = None

        if not stdin_closed:
            while True:
                try:
                    user_input = input_queue.get(timeout=0.5)
                    break
                except queue.Empty:
                    if time.time() - last_activity > idle_timeout:
                        ConsoleOutput.warning(f"User idle for {idle_timeout}s. Resuming...")
                        last_activity = time.time()
                        ConsoleOutput.user_output("", end="")
                        ConsoleOutput.prompt()
        else:
            user_input = None

        if user_input is None:
            log_step("user_input is None")
            if not stdin_closed:
                stdin_closed = True
                log_step("stdin_closed flag set")
                ConsoleOutput.system("stdin closed, continuing to run. Type 'exit' or press Ctrl+C to quit.")
            time.sleep(0.5)
            continue

        if user_input.strip() == "__STATUS__":
            ConsoleOutput.system("STATUS PROBE")
            ConsoleOutput.user_output(json.dumps(bot.get_runtime_status(), indent=2))
            continue

        if user_input.lower() in ["exit", "quit"]:
            break

        try:
            result = bot.handle_turn(user_input)
            ConsoleOutput.user_output(result)
        except Exception as e:
            ConsoleOutput.error(f"FATAL ERROR: {e}")
            traceback.print_exc()
            shutdown_runtime(bot, "Attempting to save state before exit...")


def main():
    runtime_flags = resolve_runtime_flags()
    RUNTIME_FLAGS.update(runtime_flags)
    StartupTracer.configure(enabled=runtime_flags.get("debug_startup", False))

    def log_step(msg):
        StartupTracer.log(msg)

    bot: Optional[FlexiBot] = None

    try:
        log_step("enter main")
        configure_console(log_step)
        log_step("startup complete")
        log_step("before non-tty check")

        if not sys.stdin.isatty():
            handle_eof_mode(log_step)
            return

        bot = bootstrap_runtime(log_step)
        input_queue = queue.Queue()
        start_input_thread(input_queue)
        run_interactive_loop(bot, input_queue, log_step)

    except KeyboardInterrupt:
        ConsoleOutput.warning("👋 Gracefully shutting down... (Ctrl+C detected)")
        shutdown_runtime(bot)
        sys.exit(0)
    except Exception as e:
        log_step(f"main exception: {e}")
        traceback.print_exc()
        shutdown_runtime(bot)
        sys.exit(1)

if __name__ == "__main__": main()
