import urllib.request
import urllib.parse
import urllib.error
import signal
import time
import sys
import platform
from datetime import datetime, timedelta
import csv
import json
import os
import io
import re
import subprocess
import traceback
import asyncio
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
import gc
import warnings
import importlib.util
import tokenize
import html
from dataclasses import asdict, dataclass, field
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple
from contextlib import redirect_stderr, redirect_stdout
from concurrent.futures import ThreadPoolExecutor


def _is_termux_environment() -> bool:
    if platform.system() != "Linux":
        return False
    prefix = os.environ.get("PREFIX", "")
    return "com.termux" in prefix or bool(os.environ.get("TERMUX_VERSION"))


def _safe_import_posix_readline():
    saved_settings = None
    termios_mod = None
    stdin_stream = getattr(sys, "stdin", None)
    should_restore_tty = _is_termux_environment()
    if should_restore_tty and stdin_stream is not None and hasattr(stdin_stream, "fileno"):
        try:
            import termios as termios_mod_local
            termios_mod = termios_mod_local
            saved_settings = termios_mod.tcgetattr(stdin_stream.fileno())
        except Exception:
            saved_settings = None
            termios_mod = None

    try:
        import readline as readline_mod
        return readline_mod, True
    except ImportError:
        return None, False
    finally:
        if saved_settings is not None and termios_mod is not None and stdin_stream is not None:
            try:
                termios_mod.tcsetattr(stdin_stream.fileno(), termios_mod.TCSADRAIN, saved_settings)
            except Exception:
                pass


readline, HISTORY_SUPPORT = _safe_import_posix_readline()

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
COMMAND_HISTORY_FILE = STATE_DIR / "command_history"
COMMAND_HISTORY_LENGTH = 2000
BG_TASK_LOG_DIR = STATE_DIR / "bg_task_logs"
DB_PROFILES_FILE = STATE_DIR / "db_profiles.json"
NOTEBOOK_SESSION_FILE = STATE_DIR / "notebook_sessions.json"
ARCHIVE_FILE = STATE_DIR / "full_archive.jsonl"
RESPONSE_TRACE_FILE = STATE_DIR / "response_trace.jsonl"
# maximum size (bytes) before rotating/compressing the legacy JSONL archive
ARCHIVE_MAX_BYTES = 5 * 1024 * 1024  # 5 MiB by default
REVIEWER_EVENT_KEY = "reviewer_events"
GOAL_RECORDS_KEY = "goal_records"
RUNTIME_HEARTBEAT_KEY = "runtime_heartbeat"
PROJECT_MEMORY_KEY = "project_memory"
TASK_MEMORY_KEY = "task_memory"
FAILURE_MEMORY_KEY = "failure_memory"
PROJECT_BRIEF_KEY = "project_brief"
TASK_GRAPH_KEY = "task_graph"
WORKSPACE_LOCKS_KEY = "workspace_locks"
LAST_TEST_RUN_KEY = "last_test_run"
IDLE_TRIAGE_RECORD_KEY = "idle_triage"
GOAL_STATUS_ACTIVE = "active"
GOAL_STATUS_PENDING = "pending"
GOAL_STATUS_COMPLETED = "completed"
GOAL_STATUS_CANCELLED = "cancelled"
GOAL_STATUS_FAILED = "failed"
OPERATOR_COMMAND_PREFIX = "/"
DEFAULT_HEARTBEAT_INTERVAL_SECONDS = 5
OPERATOR_COMMANDS = {
    "/health",
    "/history",
    "/reviews",
    "/goals",
    "/goal",
    "/help",
}

EVOLUTION_LOG = STATE_DIR / "evolution_log.md"
MAX_SNAPSHOTS = 5
TOKEN_THRESHOLD = 368000 # Your specific requirement for summary trigger
PROMPT_LABEL = "[Awaiting user input] > "

# automatic history summarisation parameters
AUTO_SUMMARY_THRESHOLD = 2000  # if history entries exceed this
AUTO_SUMMARY_KEEP = 500        # keep this many recent entries intact
PROPOSAL_ARTIFACT_KEEP_RECENT = 8
PROPOSAL_ARTIFACT_ARCHIVE_DIRNAME = "archive"
IDLE_REWRITE_SECTION_NAMES = {
    "idle_proposal_workflow",
    "run_proposal_sdlc",
    "run_interactive_loop",
    "_apply_idle_proposal_patch",
}

# Place config next to the logical agent root for discoverability
CONFIG_FILE = (STATE_DIR.parent / "config.json") if STATE_DIR.name == "rlm_state" else (STATE_DIR / "config.json")
RUNTIME_CONFIG_PREFIXES = ("FLEXI_", "AGENT_")

TOKEN_CACHE_FILE = "github_token_cache.json"
COPILOT_TOKEN_URL = "https://api.github.com/copilot_internal/v2/token"
DEFAULT_COPILOT_API_BASE_URL = "https://api.individual.githubcopilot.com"
ALLOWED_BINARIES = {"git", "python", "pip", "npm", "docker", "echo"}
DRY_RUN = os.environ.get("AGENT_DRY_RUN", "true").lower() in ("1", "true", "yes")

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


def _readline_history_available() -> bool:
    return bool(
        HISTORY_SUPPORT
        and readline is not None
        and hasattr(readline, "read_history_file")
        and hasattr(readline, "write_history_file")
    )


def load_command_history() -> bool:
    if not _readline_history_available():
        return False
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        if hasattr(readline, "set_history_length"):
            readline.set_history_length(COMMAND_HISTORY_LENGTH)
        if hasattr(readline, "set_auto_history"):
            try:
                readline.set_auto_history(True)
            except Exception:
                pass
        if hasattr(readline, "parse_and_bind"):
            try:
                readline.parse_and_bind("tab: complete")
            except Exception:
                pass
        if COMMAND_HISTORY_FILE.exists():
            readline.read_history_file(str(COMMAND_HISTORY_FILE))
        return True
    except Exception:
        return False


def _dedupe_readline_history() -> bool:
    if not _readline_history_available():
        return False
    required = ("get_current_history_length", "get_history_item", "clear_history", "add_history")
    if not all(hasattr(readline, attr) for attr in required):
        return False
    try:
        history_length = int(readline.get_current_history_length())
        if history_length <= 1:
            return True
        entries: list[str] = []
        previous_entry: str | None = None
        for index in range(1, history_length + 1):
            entry = readline.get_history_item(index)
            if entry is None:
                continue
            if entry == previous_entry:
                continue
            entries.append(entry)
            previous_entry = entry
        if COMMAND_HISTORY_LENGTH > 0 and len(entries) > COMMAND_HISTORY_LENGTH:
            entries = entries[-COMMAND_HISTORY_LENGTH:]
        readline.clear_history()
        for entry in entries:
            readline.add_history(entry)
        return True
    except Exception:
        return False


def save_command_history() -> bool:
    if not _readline_history_available():
        return False
    try:
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        if hasattr(readline, "set_history_length"):
            readline.set_history_length(COMMAND_HISTORY_LENGTH)
        _dedupe_readline_history()
        readline.write_history_file(str(COMMAND_HISTORY_FILE))
        return True
    except Exception:
        return False

def get_default_runtime_config() -> dict[str, Any]:
    return {
        "idle_proposal_enabled": True,
        "idle_proposal_interval_seconds": 300,
        "idle_proposal_auto_confirm": True,
        "heartbeat_interval_seconds": DEFAULT_HEARTBEAT_INTERVAL_SECONDS,
        "reviewer_pass_enabled": True,
        "reviewer_pass_after_tools": True,
        "reviewer_pass_after_tests": True,
        "debug_startup": False,
        "no_dependency_check": False,
    }


def _parse_runtime_config_value(raw_value: Any, default_value: Any) -> Any:
    if isinstance(default_value, bool):
        if isinstance(raw_value, str):
            return raw_value.strip().lower() in ("1", "true", "yes", "on")
        return bool(raw_value)
    if isinstance(default_value, int):
        try:
            return int(raw_value)
        except (TypeError, ValueError):
            return default_value
    return raw_value


def _apply_env_config_overrides(config: dict[str, Any]) -> dict[str, Any]:
    runtime_config = dict(config)
    for env_name, env_value in os.environ.items():
        for prefix in RUNTIME_CONFIG_PREFIXES:
            if env_name.startswith(prefix):
                key = env_name[len(prefix) :].lower()
                if not key:
                    continue
                runtime_config[key] = _parse_runtime_config_value(env_value, config.get(key))
                break
    return runtime_config


def validate_runtime_config(cfg: dict[str, Any] | None = None) -> dict[str, Any]:
    if cfg is None:
        cfg = {}
    if not isinstance(cfg, dict):
        raise TypeError("Runtime config must be a dictionary.")
    defaults = get_default_runtime_config()
    validated: dict[str, Any] = {}
    for key, default_value in defaults.items():
        if key in cfg:
            validated[key] = _parse_runtime_config_value(cfg[key], default_value)
        else:
            validated[key] = default_value
    return validated


def load_runtime_config() -> dict[str, Any]:
    raw_config: dict[str, Any] = {}
    if CONFIG_FILE.exists():
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                raw = json.load(f)
                if isinstance(raw, dict):
                    raw_config = raw
                else:
                    ErrorHandler.log(
                        TypeError("Runtime config file must contain a JSON object."),
                        severity=ErrorSeverity.RECOVERABLE,
                        context="load_runtime_config",
                        code=ErrorCode.IO_ERROR,
                    )
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="load_runtime_config", code=ErrorCode.IO_ERROR)

    config = validate_runtime_config(raw_config)
    config = _apply_env_config_overrides(config)
    return config


def save_runtime_config(config: dict[str, Any]) -> bool:
    if not isinstance(config, dict):
        raise TypeError("Runtime config must be a dictionary.")
    CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
    try:
        CONFIG_FILE.write_text(json.dumps(validate_runtime_config(config), indent=2), encoding="utf-8")
        return True
    except Exception as e:
        ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="save_runtime_config", code=ErrorCode.IO_ERROR)
        return False


def resolve_runtime_flags(argv: list[str] | None = None) -> dict[str, Any]:
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
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="StartupTracer.configure", code=ErrorCode.IO_ERROR)

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
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="StartupTracer.log", code=ErrorCode.IO_ERROR)
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
        {
            "id": "mss",
            "platforms": {"windows", "linux", "darwin"},
            "module": "mss",
            "install": "pip install mss",
            "capabilities": ["screen-capture"],
            "message": "mss can be used as a fallback for full-screen capture when Pillow ImageGrab is unavailable.",
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
                    except Exception as e:
                        StartupTracer.log(f"Window enumeration inner callback failed: {e}", "SYS_AUTO")
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
                            except Exception as e:
                                StartupTracer.log(f"Could not resolve process name for pid {pid}: {e}", "SYS_AUTO")
                                info["process_name"] = "Unknown"
                        except Exception as e:
                            StartupTracer.log(f"Window PID lookup failed: {e}", "SYS_AUTO")
                        windows.append(info)
                    except Exception as e:
                        StartupTracer.log(f"Window metadata collection failed: {e}", "SYS_AUTO")
            except Exception as e:
                StartupTracer.log(f"Windows window capture failed: {e}", "SYS_AUTO")

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
            except Exception as e:
                StartupTracer.log(f"Darwin window capture failed: {e}", "SYS_AUTO")

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

    @staticmethod
    def capture_screen(output_path: str) -> str:
        """Capture the full screen across platforms, using Pillow first and mss as fallback."""
        path_obj = Path(output_path)
        path_obj.parent.mkdir(parents=True, exist_ok=True)

        try:
            from PIL import ImageGrab

            grab_kwargs = {"all_screens": True} if os.name == 'nt' else {}
            image = ImageGrab.grab(**grab_kwargs)
            image.save(str(path_obj))
            return "Success"
        except Exception as pil_error:
            try:
                import mss
                from PIL import Image

                with mss.mss() as sct:
                    monitor = sct.monitors[0]
                    shot = sct.grab(monitor)
                    image = Image.frombytes("RGB", shot.size, shot.rgb)
                    image.save(str(path_obj))
                return "Success"
            except Exception as mss_error:
                return f"Screen Capture Error: Pillow={pil_error}; mss={mss_error}"

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
        ConsoleOutput._emit(PROMPT_LABEL, color=Colors.GREEN + Colors.BOLD, end="", flush=True)

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

    INSPECTION_PATTERNS = {
        "bash": [
            r"\brg\b",
            r"\bgrep\b",
            r"\bfindstr\b",
            r"\bcat\b",
            r"\btype\b",
            r"\bls\b",
            r"\bdir\b",
            r"\bpwd\b",
            r"\bwhere\b",
            r"\bwhich\b",
            r"git\s+(status|diff|show|log)",
            r"py_compile",
        ],
        "python": [
            r"safe_inspect\(",
            r"inspect_file_chunk\(",
            r"read_file\(",
            r"read_range\(",
            r"peek\(",
            r"grep\(",
            r"find_",
            r"tree\(",
            r"inspect_python_environment\(",
            r"list_python_packages\(",
            r"project_map",
            r"task_graph",
        ],
    }
    MUTATING_PATTERNS = {
        "bash": [
            r"\bpip\s+install\b",
            r"\bnpm\s+(install|update|run)\b",
            r"\bgit\s+(add|commit|push|checkout|switch|reset)\b",
            r"\brm\b",
            r"\bdel\b",
            r"\bmv\b",
            r"\bmove\b",
            r"\bcopy\b",
            r"\bcp\b",
            r"\btaskkill\b",
        ],
        "python": [
            r"write\(",
            r"create_file\(",
            r"delete_file\(",
            r"move_file\(",
            r"patch\(",
            r"edit_lines\(",
            r"spawn_background\(",
            r"run_python_bg\(",
            r"install_python_package\(",
            r"subprocess\.",
        ],
    }

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
            "inspect_max_depth": 2,
            "inspect_max_items": 20,
            "inspect_max_fields": 24,
            "inspect_max_string_chars": 240,
            "inspect_file_chunk_lines": 120,
            "print_max_chars_per_call": 3000,
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
        self.runtime_feedback: dict[str, Any] = {}

    def set_runtime_feedback(self, feedback: dict[str, Any] | None):
        self.runtime_feedback = copy.deepcopy(feedback or {})

    def clear_runtime_feedback(self):
        self.runtime_feedback = {}

    def _feedback_snapshot(self) -> dict[str, Any]:
        return copy.deepcopy(self.runtime_feedback or {})

    def describe(self) -> dict[str, Any]:
        return {
            "allowed_tools": copy.deepcopy(self.allowed_tools),
            "timeout_defaults": copy.deepcopy(self.timeout_defaults),
            "timeout_overrides": copy.deepcopy(self.timeout_overrides),
            "resource_ceilings": copy.deepcopy(self.resource_ceilings),
            "environment_isolation": copy.deepcopy(self.environment_isolation),
            "audit_logging": copy.deepcopy(self.audit_logging),
            "runtime_feedback": self._feedback_snapshot(),
        }

    def _payload_matches(self, tool_name: str, payload: str, patterns: dict[str, list[str]]) -> bool:
        text = str(payload or "")
        for pattern in patterns.get(tool_name, []):
            if re.search(pattern, text, re.IGNORECASE):
                return True
        return False

    def _inspection_like_payload(self, tool_name: str, payload: str) -> bool:
        return self._payload_matches(tool_name, payload, self.INSPECTION_PATTERNS)

    def _mutating_payload(self, tool_name: str, payload: str) -> bool:
        return self._payload_matches(tool_name, payload, self.MUTATING_PATTERNS)

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
        feedback = self._feedback_snapshot()
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

        if feedback.get("redirect_to_inspection") and self._mutating_payload(tool_name, payload):
            return ExecutionPolicyDecision(
                tool_name=tool_name,
                allowed=False,
                reason=(
                    "Reviewer guidance requires inspection before more changes. "
                    f"Blocked mutating {tool_name} payload until stronger evidence is collected."
                ),
                timeout_seconds=0,
                resource_ceilings=ceilings,
                environment=env,
                isolation_rules=rules,
                audit_format=copy.deepcopy(self.audit_logging),
            )

        if feedback.get("severity") == "blocked" and tool_name in {"spawn_background", "run_python_bg", "install_python_package"}:
            return ExecutionPolicyDecision(
                tool_name=tool_name,
                allowed=False,
                reason=(
                    "Reviewer guidance marked the current work blocked. "
                    f"{tool_name} is disabled until inspection or recovery evidence is gathered."
                ),
                timeout_seconds=0,
                resource_ceilings=ceilings,
                environment=env,
                isolation_rules=rules,
                audit_format=copy.deepcopy(self.audit_logging),
            )

        if feedback.get("confidence") == "low" or feedback.get("require_stronger_verification"):
            ceilings = copy.deepcopy(ceilings)
            ceilings["max_output_chars"] = min(int(ceilings.get("max_output_chars", 12000)), 8000)
            if "print_max_chars_per_call" in ceilings:
                ceilings["print_max_chars_per_call"] = min(int(ceilings.get("print_max_chars_per_call", 3000)), 1800)

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
        if feedback.get("confidence") == "low":
            timeout_seconds = max(10, int(timeout_seconds * 0.75))
        elif feedback.get("require_stronger_verification") and not self._inspection_like_payload(tool_name, payload):
            timeout_seconds = max(10, int(timeout_seconds * 0.85))
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
                        return _rlm_result("search_workspace", data={"matches": results}, match_count=len(results))
        return _rlm_result("search_workspace", data={"matches": results}, match_count=len(results))
    except Exception as e:
        return _rlm_result("search_workspace", ok=False, errors=[f"Workspace search error: {e}"])


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
                            return _rlm_result("find_symbol", data={"matches": results}, match_count=len(results))
        return _rlm_result("find_symbol", data={"matches": results}, match_count=len(results))
    except Exception as e:
        return _rlm_result("find_symbol", ok=False, errors=[f"Find symbol error: {e}"])


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
            return _rlm_result("read_range", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath, "start_line": int(start_line), "end_line": int(end_line)})
        lines = path.read_text(encoding='utf-8', errors='replace').splitlines()
        start = max(1, int(start_line))
        end = max(start, int(end_line))
        selected = lines[start - 1:end]
        numbered = "\n".join(f"{i}: {line}" for i, line in enumerate(selected, start=start))
        return _rlm_result("read_range", data={"file": str(path), "start_line": start, "end_line": end, "content": numbered, "line_count": len(selected)})
    except Exception as e:
        return _rlm_result("read_range", ok=False, errors=[f"Read range error: {e}"], data={"file": filepath, "start_line": start_line, "end_line": end_line})


def rlm_create_file(filepath, content="", overwrite=False):
    try:
        path = Path(filepath)
        if path.exists() and not overwrite:
            return _rlm_result("create_file", ok=False, errors=[f"File already exists at {filepath}"], data={"file": filepath, "overwrite": bool(overwrite)})
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding='utf-8')
        return _rlm_result("create_file", data={"file": str(path), "overwrite": bool(overwrite), "bytes_written": len(content.encode('utf-8'))}, summary=f"Created {filepath}")
    except Exception as e:
        return _rlm_result("create_file", ok=False, errors=[f"Create error: {e}"], data={"file": filepath, "overwrite": bool(overwrite)})


def rlm_delete_file(filepath, missing_ok=True):
    try:
        path = Path(filepath)
        if not path.exists():
            if missing_ok:
                return _rlm_result("delete_file", data={"file": filepath, "deleted": False, "missing_ok": True}, warnings=[f"File not found at {filepath}"])
            return _rlm_result("delete_file", ok=False, errors=[f"File not found at {filepath}"], data={"file": filepath, "missing_ok": False})
        if path.is_dir():
            return _rlm_result("delete_file", ok=False, errors=[f"{filepath} is a directory"], data={"file": filepath})
        path.unlink()
        return _rlm_result("delete_file", data={"file": filepath, "deleted": True}, summary=f"Deleted {filepath}")
    except Exception as e:
        return _rlm_result("delete_file", ok=False, errors=[f"Delete error: {e}"], data={"file": filepath, "missing_ok": bool(missing_ok)})


def rlm_move_file(src, dst, overwrite=False):
    try:
        src_path = Path(src)
        dst_path = Path(dst)
        if not src_path.exists():
            return _rlm_result("move_file", ok=False, errors=[f"Source not found at {src}"], data={"src": src, "dst": dst, "overwrite": bool(overwrite)})
        if dst_path.exists() and not overwrite:
            return _rlm_result("move_file", ok=False, errors=[f"Destination already exists at {dst}"], data={"src": src, "dst": dst, "overwrite": bool(overwrite)})
        dst_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(src_path), str(dst_path))
        return _rlm_result("move_file", data={"src": src, "dst": dst, "overwrite": bool(overwrite)}, summary=f"Moved {src} to {dst}")
    except Exception as e:
        return _rlm_result("move_file", ok=False, errors=[f"Move error: {e}"], data={"src": src, "dst": dst, "overwrite": bool(overwrite)})


def rlm_validate_python(filepath: str = "", code: str = ""):
    try:
        if filepath:
            path = Path(filepath)
            if not path.exists():
                return _rlm_result("validate_python", ok=False, errors=[f"File not found: {filepath}"], data={"target": filepath})
            py_compile.compile(str(path), doraise=True)
            return _rlm_result("validate_python", data={"target": str(path), "mode": "file"}, summary="Python validation passed.")
        ast.parse(code)
        return _rlm_result("validate_python", data={"target": "inline", "mode": "inline"}, summary="Python validation passed.")
    except Exception as e:
        return _rlm_result("validate_python", ok=False, errors=[str(e)], data={"target": filepath or "inline"})


def rlm_validate_json(filepath: str = "", content: str = ""):
    try:
        if filepath:
            path = Path(filepath)
            if not path.exists():
                return _rlm_result("validate_json", ok=False, errors=[f"File not found: {filepath}"], data={"target": filepath})
            json.loads(path.read_text(encoding='utf-8'))
            return _rlm_result("validate_json", data={"target": str(path), "mode": "file"}, summary="JSON validation passed.")
        json.loads(content)
        return _rlm_result("validate_json", data={"target": "inline", "mode": "inline"}, summary="JSON validation passed.")
    except Exception as e:
        return _rlm_result("validate_json", ok=False, errors=[str(e)], data={"target": filepath or "inline"})


def rlm_inspect_python_environment():
    try:
        info = {
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
        return _rlm_result("inspect_python_environment", data=info, summary="Collected Python environment details.")
    except Exception as e:
        return _rlm_result("inspect_python_environment", ok=False, errors=[str(e)])


def rlm_list_python_packages(limit: int = 500):
    try:
        cmd = [sys.executable, "-m", "pip", "list", "--format=json"]
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=60, encoding='utf-8', errors='replace')
        if res.returncode != 0:
            return _rlm_result("list_python_packages", ok=False, errors=[res.stderr.strip() or res.stdout.strip() or "pip list failed"])
        data = json.loads(res.stdout or "[]")
        return _rlm_result("list_python_packages", data={"count": len(data), "packages": data[: int(limit)]}, summary=f"Listed {len(data[: int(limit)])} package(s).")
    except Exception as e:
        return _rlm_result("list_python_packages", ok=False, errors=[str(e)])

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
        if not os.path.exists(filepath):
            return _rlm_result("grep", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath, "pattern": pattern})
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        for i, line in enumerate(lines):
            if re.search(pattern, line):
                start = max(0, i - context_lines)
                end = min(len(lines), i + context_lines + 1)
                snippet = "".join(lines[start:end])
                results.append({"line": i + 1, "context": snippet[:1200]})
        return _rlm_result("grep", data={"file": filepath, "pattern": pattern, "matches": results}, match_count=len(results), warnings=[] if results else ["No matches found."])
    except Exception as e:
        return _rlm_result("grep", ok=False, errors=[f"Grep error: {e}"], data={"file": filepath, "pattern": pattern})

def rlm_peek(filepath, start_line=0, end_line=30):
    try:
        if not os.path.exists(filepath):
            return _rlm_result("peek", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath, "start_line": int(start_line), "end_line": int(end_line)})
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        
        content = "".join(lines[start_line:end_line])
        if len(lines) > end_line:
            content += f"\n... (truncated, total lines: {len(lines)})"
        return _rlm_result("peek", data={"file": filepath, "start_line": int(start_line), "end_line": int(end_line), "content": content})
    except Exception as e:
        return _rlm_result("peek", ok=False, errors=[f"Peek error: {e}"], data={"file": filepath, "start_line": start_line, "end_line": end_line})

def rlm_read(filepath):
    try:
        if not os.path.exists(filepath):
            return _rlm_result("read_file", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath})
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            return _rlm_result("read_file", data={"file": filepath, "content": f.read()})
    except Exception as e:
        return _rlm_result("read_file", ok=False, errors=[f"Read error: {e}"], data={"file": filepath})

def _rlm_limit_text(text, max_chars=12000):
    value = str(text)
    if max_chars <= 0 or len(value) <= int(max_chars):
        return value
    clipped = value[: max(0, int(max_chars))]
    return f"{clipped}... (truncated, {len(value)} chars total)"

def _rlm_safe_preview_data(value, max_depth=2, max_items=20, max_fields=24, max_string_chars=240, _depth=0):
    if isinstance(value, str):
        return _rlm_limit_text(value, max_chars=max_string_chars)
    if value is None or isinstance(value, (bool, int, float)):
        return value
    if _depth >= max_depth:
        return f"<{type(value).__name__}>"
    if isinstance(value, dict):
        items = list(value.items())
        preview = {}
        for key, item in items[:max_fields]:
            preview[str(key)] = _rlm_safe_preview_data(
                item,
                max_depth=max_depth,
                max_items=max_items,
                max_fields=max_fields,
                max_string_chars=max_string_chars,
                _depth=_depth + 1,
            )
        if len(items) > max_fields:
            preview["..."] = f"{len(items) - max_fields} more field(s)"
        return preview
    if isinstance(value, (list, tuple, set)):
        seq = list(value)
        preview = [
            _rlm_safe_preview_data(
                item,
                max_depth=max_depth,
                max_items=max_items,
                max_fields=max_fields,
                max_string_chars=max_string_chars,
                _depth=_depth + 1,
            )
            for item in seq[:max_items]
        ]
        if len(seq) > max_items:
            preview.append(f"... ({len(seq) - max_items} more item(s))")
        return preview
    if isinstance(value, Path):
        return str(value)
    if hasattr(value, "read") and hasattr(value, "name"):
        return {"type": type(value).__name__, "name": getattr(value, "name", "")}
    if hasattr(value, "__dict__"):
        try:
            data = vars(value)
        except Exception:
            return repr(value)
        return {
            "type": type(value).__name__,
            "attrs": _rlm_safe_preview_data(
                data,
                max_depth=max_depth,
                max_items=max_items,
                max_fields=max_fields,
                max_string_chars=max_string_chars,
                _depth=_depth + 1,
            ),
        }
    return _rlm_limit_text(repr(value), max_chars=max_string_chars)

def rlm_inspect_file_chunk(filepath, start_line=1, chunk_lines=120, max_chars=12000):
    try:
        if not os.path.exists(filepath):
            return _rlm_result("inspect_file_chunk", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath, "start_line": int(start_line), "chunk_lines": int(chunk_lines)})
        start = max(1, int(start_line))
        chunk = max(1, int(chunk_lines))
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        begin = start - 1
        end = min(len(lines), begin + chunk)
        content = "".join(lines[begin:end])
        limited = _rlm_limit_text(content, max_chars=max_chars)
        next_start = end + 1 if end < len(lines) else None
        summary = f"Read lines {start}-{end} from {filepath}"
        if next_start is not None:
            summary += f"; next_start_line={next_start}"
        return _rlm_result(
            "inspect_file_chunk",
            data={
                "file": filepath,
                "start_line": start,
                "end_line": end,
                "chunk_lines": chunk,
                "next_start_line": next_start,
                "total_lines": len(lines),
                "content": limited,
            },
            summary=summary,
        )
    except Exception as e:
        return _rlm_result("inspect_file_chunk", ok=False, errors=[f"Inspect file chunk error: {e}"], data={"file": filepath, "start_line": start_line, "chunk_lines": chunk_lines})

def rlm_safe_inspect(target=None, label="", start_line=1, chunk_lines=120, max_depth=2, max_items=20, max_fields=24, max_string_chars=240, prefer_file_reads=True, max_chars=12000):
    try:
        file_candidate = None
        if prefer_file_reads:
            if isinstance(target, (str, Path)):
                candidate = Path(target)
                if candidate.exists() and candidate.is_file():
                    file_candidate = str(candidate)
            elif hasattr(target, "name"):
                candidate = Path(str(getattr(target, "name")))
                if candidate.exists() and candidate.is_file():
                    file_candidate = str(candidate)
        if file_candidate:
            result = rlm_inspect_file_chunk(file_candidate, start_line=start_line, chunk_lines=chunk_lines, max_chars=max_chars)
            if label:
                result.setdefault("data", {})["label"] = label
                if result.get("summary"):
                    result["summary"] = f"{label}: {result['summary']}"
            return result
        preview = _rlm_safe_preview_data(
            target,
            max_depth=max_depth,
            max_items=max_items,
            max_fields=max_fields,
            max_string_chars=max_string_chars,
        )
        rendered = _rlm_limit_text(json.dumps(preview, ensure_ascii=False, default=str, indent=2), max_chars=max_chars)
        summary = "Inspected object safely."
        if label:
            summary = f"Inspected {label} safely."
        return _rlm_result(
            "safe_inspect",
            data={"label": label, "preview": rendered},
            summary=summary,
        )
    except Exception as e:
        return _rlm_result("safe_inspect", ok=False, errors=[f"Safe inspect error: {e}"], data={"label": label})

def rlm_write(filepath, content):
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return _rlm_result("write_file", data={"file": filepath, "bytes_written": len(content.encode('utf-8'))}, summary=f"Wrote {filepath}")
    except Exception as e:
        return _rlm_result("write_file", ok=False, errors=[f"Write error: {e}"], data={"file": filepath})

def rlm_patch(filepath, search_block, replace_block, count=1):
    try:
        if not os.path.exists(filepath):
            return _rlm_result("patch_file", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath, "expected_count": int(count)})
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            content = f.read()
        
        occ = content.count(search_block)
        if occ == 0:
            return _rlm_result("patch_file", ok=False, errors=[f"Search block not found in {filepath}"], data={"file": filepath, "expected_count": int(count), "actual_count": occ})
        if count > 0 and occ != count:
            return _rlm_result("patch_file", ok=False, errors=[f"Expected {count} occurrence(s), but found {occ} in {filepath}. Patch aborted for safety."], data={"file": filepath, "expected_count": int(count), "actual_count": occ})
        
        new_content = content.replace(search_block, replace_block, count if count > 0 else -1)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return _rlm_result("patch_file", data={"file": filepath, "replacement_count": occ}, summary=f"Patched {filepath}")
    except Exception as e:
        return _rlm_result("patch_file", ok=False, errors=[f"Patch error: {e}"], data={"file": filepath, "expected_count": int(count)})

def rlm_edit_lines(filepath, start_line, end_line, new_content):
    """Surgically replaces a range of lines (1-indexed, inclusive)."""
    try:
        if not os.path.exists(filepath):
            return _rlm_result("edit_lines", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath, "start_line": int(start_line), "end_line": int(end_line)})
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        
        # Adjust to 0-indexed
        s = max(0, start_line - 1)
        e = min(len(lines), end_line)
        
        if s >= len(lines):
            return _rlm_result("edit_lines", ok=False, errors=[f"start_line {start_line} is beyond file length"], data={"file": filepath, "start_line": int(start_line), "end_line": int(end_line), "line_count": len(lines)})
        
        # Prepare replacement
        if not new_content.endswith('\n') and e < len(lines):
            new_content += '\n'
            
        lines[s:e] = [new_content]
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(lines)
        return _rlm_result("edit_lines", data={"file": filepath, "start_line": int(start_line), "end_line": int(end_line)}, summary=f"Edited lines {start_line}-{end_line} in {filepath}")
    except Exception as e:
        return _rlm_result("edit_lines", ok=False, errors=[f"Edit error: {e}"], data={"file": filepath, "start_line": start_line, "end_line": end_line})

def rlm_find_files(pattern, root="."):
    matches = []
    try:
        for path in Path(root).rglob(pattern):
            matches.append(str(path))
        return _rlm_result("find_files", data={"root": root, "pattern": pattern, "matches": matches}, match_count=len(matches), warnings=[] if matches else ["No files found."])
    except Exception as e:
        return _rlm_result("find_files", ok=False, errors=[f"Find error: {e}"], data={"root": root, "pattern": pattern})

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
        return _rlm_result("tree", data={"root": str(root_path.resolve()), "depth": int(depth), "content": "\n".join(output)})
    except Exception as e:
        return _rlm_result("tree", ok=False, errors=[f"Tree error: {e}"], data={"root": root, "depth": depth})

def rlm_read_metadata(filepath):
    try:
        p = Path(filepath)
        if not p.exists():
            return _rlm_result("read_metadata", ok=False, errors=[f"File not found: {filepath}"], data={"file": filepath})
        stat = p.stat()
        return _rlm_result("read_metadata", data={"file": filepath, "size": stat.st_size, "modified": time.ctime(stat.st_mtime)})
    except Exception as e:
        return _rlm_result("read_metadata", ok=False, errors=[f"Metadata error: {e}"], data={"file": filepath})

def rlm_history_search(query: str, limit: int = 10):
    """Searches the persistent JSONL archive for keywords."""
    results = []
    if not ARCHIVE_FILE.exists():
        return _rlm_result("history_search", data={"query": query, "matches": []}, warnings=["No history archive found."])
    try:
        with open(ARCHIVE_FILE, "r", encoding="utf-8") as f:
            for line in f:
                if query.lower() in line.lower():
                    data = json.loads(line)
                    results.append(f"[{time.ctime(data['ts'])}] {data['role'].upper()}: {data['content'][:200]}...")
        
        return _rlm_result("history_search", data={"query": query, "matches": results[-limit:]}, match_count=len(results), warnings=[] if results else [f"No matches found for '{query}' in archive."])
    except Exception as e:
        return _rlm_result("history_search", ok=False, errors=[f"History search error: {e}"], data={"query": query, "limit": int(limit)})

def rlm_map_dependencies(filepath: str):
    """Uses static analysis (parsing import statements) to show local file dependencies."""
    path = Path(filepath)
    if not path.exists():
        return _rlm_result("map_dependencies", ok=False, errors=[f"File '{filepath}' not found."], data={"file": filepath})
    
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
        
        unique_deps = sorted(list(set(deps)))
        return _rlm_result("map_dependencies", data={"file": filepath, "dependencies": unique_deps}, dependency_count=len(unique_deps))
    except Exception as e:
        return _rlm_result("map_dependencies", ok=False, errors=[f"Error mapping dependencies for {filepath}: {e}"], data={"file": filepath})

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

    def log_proposal_event(self, proposal_path: Path, passed: bool, notes: str = ""):
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        status = "PASSED" if passed else "FAILED"
        entry = (
            f"\n## Proposal Event - {timestamp}\n"
            f"- **Proposal:** {proposal_path}\n"
            f"- **Status:** {status}\n"
            f"- **Notes:** {notes or 'none'}\n---\n"
        )
        with self.log_path.open("a", encoding="utf-8") as f:
            f.write(entry)

    def log_plan_event(self, plan_text: str, context: str = ""):
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        entry = (
            f"\n## Plan Event - {timestamp}\n"
            f"- **Context:** {context or 'N/A'}\n"
            f"- **Plan:**\n{plan_text}\n---\n"
        )
        with self.log_path.open("a", encoding="utf-8") as f:
            f.write(entry)

# --- NEXT-GEN ASYNC STATE MANAGEMENT ---
@dataclass
class MemoryEntry:
    id: str
    content: str
    tags: List[str]
    timestamp: float


@dataclass
class ProjectBrief:
    workspace_path: str = ""
    stack: list[str] = field(default_factory=list)
    entrypoints: list[str] = field(default_factory=list)
    build_commands: list[str] = field(default_factory=list)
    test_commands: list[str] = field(default_factory=list)
    deployment_shape: str = ""
    current_milestone: str = ""
    updated_at: str = ""


@dataclass
class TaskGraphNode:
    id: str = ""
    title: str = ""
    description: str = ""
    target_files: list[str] = field(default_factory=list)
    dependencies: list[str] = field(default_factory=list)
    verification_target: str = ""
    goal_id: str = ""
    status: str = GOAL_STATUS_PENDING


@dataclass
class TaskGraph:
    nodes: list[TaskGraphNode] = field(default_factory=list)
    updated_at: str = ""


@dataclass
class WorkspaceLock:
    id: str = ""
    area: str = ""
    holder: str = ""
    goal_id: str = ""
    reason: str = ""
    acquired_at: str = ""
    expires_at: str = ""
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass
class ProjectMemory:
    workspace_path: str = ""
    architecture: list[str] = field(default_factory=list)
    conventions: list[str] = field(default_factory=list)
    entrypoints: list[str] = field(default_factory=list)
    dependencies: list[str] = field(default_factory=list)
    current_milestones: list[str] = field(default_factory=list)
    brief: ProjectBrief = field(default_factory=ProjectBrief)
    updated_at: str = ""


@dataclass
class TaskMemory:
    request_signature: str = ""
    current_operation: str = ""
    expected_output: str = ""
    active_goal_id: str = ""
    current_phase: str = ""
    touched_files: list[str] = field(default_factory=list)
    last_observations: list[str] = field(default_factory=list)
    updated_at: str = ""


@dataclass
class FailureMemory:
    recurring_errors: list[dict[str, Any]] = field(default_factory=list)
    known_bad_commands: list[dict[str, Any]] = field(default_factory=list)
    missing_dependencies: list[dict[str, Any]] = field(default_factory=list)
    recovery_patterns: list[dict[str, Any]] = field(default_factory=list)
    updated_at: str = ""

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
    DEFAULT_JOURNAL_MODE = "wal"

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
        conn = None
        try:
            conn = sqlite3.connect(self.db_path, timeout=self.DB_BUSY_TIMEOUT_MS / 1000)
            conn.row_factory = sqlite3.Row
            self._apply_pragmas(conn, verify=not self._db_pragmas_verified)
            return conn
        except sqlite3.DatabaseError as e:
            ErrorHandler.log(e, severity=ErrorSeverity.CRITICAL, context="AgentState._connect_db", code=ErrorCode.IO_ERROR)
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
            if self.db_path.exists():
                fallback_path = self.db_path.with_name(f"{self.db_path.name}.corrupt.{int(time.time())}")
                try:
                    self.db_path.rename(fallback_path)
                    ConsoleOutput.warning(f"Repaired corrupted state DB; moved original to {fallback_path}")
                except Exception as rename_error:
                    ErrorHandler.log(rename_error, severity=ErrorSeverity.CRITICAL, context="AgentState._connect_db.rename", code=ErrorCode.IO_ERROR)
            conn = None
            try:
                conn = sqlite3.connect(self.db_path, timeout=self.DB_BUSY_TIMEOUT_MS / 1000)
                conn.row_factory = sqlite3.Row
                self._apply_pragmas(conn, verify=not self._db_pragmas_verified)
                return conn
            except Exception:
                if conn is not None:
                    try:
                        conn.close()
                    except Exception:
                        pass
                raise

    def _apply_pragmas(self, conn: sqlite3.Connection, verify: bool = False):
        conn.execute(f"PRAGMA busy_timeout={self.DB_BUSY_TIMEOUT_MS}")
        journal_mode = self.DEFAULT_JOURNAL_MODE
        try:
            journal_mode = str(conn.execute(f"PRAGMA journal_mode={self.DEFAULT_JOURNAL_MODE}").fetchone()[0]).lower()
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="AgentState._apply_pragmas.journal_mode", code=ErrorCode.IO_ERROR)
            journal_mode = str(conn.execute("PRAGMA journal_mode=DELETE").fetchone()[0]).lower()
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA temp_store=MEMORY")
        conn.execute("PRAGMA foreign_keys=ON")
        if journal_mode == "wal":
            conn.execute("PRAGMA wal_autocheckpoint=1000")
        if verify:
            try:
                current_journal_mode = str(conn.execute("PRAGMA journal_mode").fetchone()[0]).lower()
                busy_timeout = int(conn.execute("PRAGMA busy_timeout").fetchone()[0])
                if current_journal_mode not in {"wal", "delete"}:
                    raise RuntimeError(f"SQLite journal_mode verification failed: unsupported mode {current_journal_mode}")
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

    def _coerce_memory_text_list(self, value: Any, *, limit: int = 20, max_chars: int = 240) -> list[str]:
        if value is None:
            return []
        if isinstance(value, str):
            items = [value]
        elif isinstance(value, (list, tuple, set)):
            items = list(value)
        else:
            items = [value]
        normalized: list[str] = []
        seen: set[str] = set()
        for item in items:
            text = re.sub(r"\s+", " ", str(item or "")).strip()
            if not text:
                continue
            if len(text) > max_chars:
                text = text[: max_chars - 3].rstrip() + "..."
            if text in seen:
                continue
            seen.add(text)
            normalized.append(text)
        return normalized[-max(1, int(limit)):]

    def _coerce_failure_records(self, value: Any, *, limit: int = 25) -> list[dict[str, Any]]:
        if not isinstance(value, (list, tuple)):
            return []
        records: list[dict[str, Any]] = []
        for item in list(value)[-max(1, int(limit)):]:
            if not isinstance(item, dict):
                item = {"value": str(item or "").strip()}
            normalized: dict[str, Any] = {}
            for key, raw in item.items():
                if raw is None:
                    continue
                if isinstance(raw, str):
                    text = re.sub(r"\s+", " ", raw).strip()
                    if text:
                        normalized[str(key)] = text[:400]
                elif isinstance(raw, (int, float, bool)):
                    normalized[str(key)] = raw
                elif isinstance(raw, (list, tuple, set)):
                    normalized[str(key)] = self._coerce_memory_text_list(raw, limit=8, max_chars=240)
                else:
                    text = re.sub(r"\s+", " ", str(raw)).strip()
                    if text:
                        normalized[str(key)] = text[:400]
            if normalized:
                records.append(normalized)
        return records

    def _normalize_project_memory(self, value: Any = None) -> ProjectMemory:
        raw = value if value is not None else self.recall(PROJECT_MEMORY_KEY)
        if isinstance(raw, ProjectMemory):
            memory = copy.deepcopy(raw)
        else:
            payload = raw if isinstance(raw, dict) else {}
            brief_payload = payload.get("brief", {}) if isinstance(payload.get("brief", {}), dict) else {}
            memory = ProjectMemory(
                workspace_path=str(payload.get("workspace_path", "") or "").strip(),
                architecture=self._coerce_memory_text_list(payload.get("architecture", []), limit=16, max_chars=260),
                conventions=self._coerce_memory_text_list(payload.get("conventions", []), limit=16, max_chars=260),
                entrypoints=self._coerce_memory_text_list(payload.get("entrypoints", []), limit=16, max_chars=200),
                dependencies=self._coerce_memory_text_list(payload.get("dependencies", []), limit=24, max_chars=120),
                current_milestones=self._coerce_memory_text_list(payload.get("current_milestones", []), limit=16, max_chars=260),
                brief=ProjectBrief(
                    workspace_path=str(brief_payload.get("workspace_path", payload.get("workspace_path", "")) or "").strip(),
                    stack=self._coerce_memory_text_list(brief_payload.get("stack", []), limit=16, max_chars=160),
                    entrypoints=self._coerce_memory_text_list(brief_payload.get("entrypoints", payload.get("entrypoints", [])), limit=16, max_chars=200),
                    build_commands=self._coerce_memory_text_list(brief_payload.get("build_commands", []), limit=16, max_chars=200),
                    test_commands=self._coerce_memory_text_list(brief_payload.get("test_commands", []), limit=16, max_chars=200),
                    deployment_shape=str(brief_payload.get("deployment_shape", "") or "").strip(),
                    current_milestone=str(brief_payload.get("current_milestone", "") or "").strip(),
                    updated_at=str(brief_payload.get("updated_at", "") or "").strip(),
                ),
                updated_at=str(payload.get("updated_at", "") or "").strip(),
            )
        if not memory.updated_at:
            memory.updated_at = datetime.now().isoformat()
        return memory

    def _normalize_task_memory(self, value: Any = None) -> TaskMemory:
        raw = value if value is not None else self.recall(TASK_MEMORY_KEY)
        if isinstance(raw, TaskMemory):
            memory = copy.deepcopy(raw)
        else:
            payload = raw if isinstance(raw, dict) else {}
            brief_payload = payload.get("brief", {}) if isinstance(payload.get("brief", {}), dict) else {}
            memory = TaskMemory(
                request_signature=str(payload.get("request_signature", "") or "").strip(),
                current_operation=str(payload.get("current_operation", "") or "").strip(),
                expected_output=str(payload.get("expected_output", "") or "").strip(),
                active_goal_id=str(payload.get("active_goal_id", "") or "").strip(),
                current_phase=str(payload.get("current_phase", "") or "").strip(),
                touched_files=self._coerce_memory_text_list(payload.get("touched_files", []), limit=20, max_chars=200),
                last_observations=self._coerce_memory_text_list(payload.get("last_observations", []), limit=8, max_chars=280),
                updated_at=str(payload.get("updated_at", "") or "").strip(),
            )
        if not memory.updated_at:
            memory.updated_at = datetime.now().isoformat()
        return memory

    def _normalize_failure_memory(self, value: Any = None) -> FailureMemory:
        raw = value if value is not None else self.recall(FAILURE_MEMORY_KEY)
        if isinstance(raw, FailureMemory):
            memory = copy.deepcopy(raw)
        else:
            payload = raw if isinstance(raw, dict) else {}
            memory = FailureMemory(
                recurring_errors=self._coerce_failure_records(payload.get("recurring_errors", []), limit=25),
                known_bad_commands=self._coerce_failure_records(payload.get("known_bad_commands", []), limit=25),
                missing_dependencies=self._coerce_failure_records(payload.get("missing_dependencies", []), limit=25),
                recovery_patterns=self._coerce_failure_records(payload.get("recovery_patterns", []), limit=25),
                updated_at=str(payload.get("updated_at", "") or "").strip(),
            )
        if not memory.updated_at:
            memory.updated_at = datetime.now().isoformat()
        return memory

    def project_memory(self) -> ProjectMemory:
        return self._normalize_project_memory()

    def task_memory(self) -> TaskMemory:
        return self._normalize_task_memory()

    def failure_memory(self) -> FailureMemory:
        return self._normalize_failure_memory()

    def remember_project_memory(self, memory: ProjectMemory | dict[str, Any]) -> ProjectMemory:
        normalized = self._normalize_project_memory(memory)
        normalized.updated_at = datetime.now().isoformat()
        self.remember(PROJECT_MEMORY_KEY, asdict(normalized))
        return normalized

    def remember_task_memory(self, memory: TaskMemory | dict[str, Any]) -> TaskMemory:
        normalized = self._normalize_task_memory(memory)
        normalized.updated_at = datetime.now().isoformat()
        self.remember(TASK_MEMORY_KEY, asdict(normalized))
        return normalized

    def remember_failure_memory(self, memory: FailureMemory | dict[str, Any]) -> FailureMemory:
        normalized = self._normalize_failure_memory(memory)
        normalized.updated_at = datetime.now().isoformat()
        self.remember(FAILURE_MEMORY_KEY, asdict(normalized))
        return normalized

    def _normalize_project_brief(self, value: Any = None) -> ProjectBrief:
        raw = value if value is not None else self.recall(PROJECT_BRIEF_KEY)
        if isinstance(raw, ProjectBrief):
            brief = copy.deepcopy(raw)
        else:
            payload = raw if isinstance(raw, dict) else {}
            brief = ProjectBrief(
                workspace_path=str(payload.get("workspace_path", "") or "").strip(),
                stack=self._coerce_memory_text_list(payload.get("stack", []), limit=16, max_chars=160),
                entrypoints=self._coerce_memory_text_list(payload.get("entrypoints", []), limit=16, max_chars=200),
                build_commands=self._coerce_memory_text_list(payload.get("build_commands", []), limit=16, max_chars=200),
                test_commands=self._coerce_memory_text_list(payload.get("test_commands", []), limit=16, max_chars=200),
                deployment_shape=str(payload.get("deployment_shape", "") or "").strip(),
                current_milestone=str(payload.get("current_milestone", "") or "").strip(),
                updated_at=str(payload.get("updated_at", "") or "").strip(),
            )
        if not brief.updated_at:
            brief.updated_at = datetime.now().isoformat()
        return brief

    def project_brief(self) -> ProjectBrief:
        return self._normalize_project_brief()

    def remember_project_brief(self, brief: ProjectBrief | dict[str, Any]) -> ProjectBrief:
        normalized = self._normalize_project_brief(brief)
        normalized.updated_at = datetime.now().isoformat()
        self.remember(PROJECT_BRIEF_KEY, asdict(normalized))
        return normalized

    def _normalize_task_graph(self, value: Any = None) -> TaskGraph:
        raw = value if value is not None else self.recall(TASK_GRAPH_KEY)
        if isinstance(raw, TaskGraph):
            graph = copy.deepcopy(raw)
        else:
            payload = raw if isinstance(raw, dict) else {}
            nodes: list[TaskGraphNode] = []
            for item in payload.get("nodes", []) if isinstance(payload.get("nodes", []), list) else []:
                if not isinstance(item, dict):
                    continue
                nodes.append(TaskGraphNode(
                    id=str(item.get("id", "") or "").strip(),
                    title=str(item.get("title", "") or "").strip(),
                    description=str(item.get("description", "") or "").strip(),
                    target_files=self._coerce_memory_text_list(item.get("target_files", []), limit=24, max_chars=200),
                    dependencies=self._coerce_memory_text_list(item.get("dependencies", []), limit=24, max_chars=200),
                    verification_target=str(item.get("verification_target", "") or "").strip(),
                    goal_id=str(item.get("goal_id", "") or "").strip(),
                    status=str(item.get("status", GOAL_STATUS_PENDING) or GOAL_STATUS_PENDING).strip(),
                ))
            graph = TaskGraph(nodes=nodes, updated_at=str(payload.get("updated_at", "") or "").strip())
        if not graph.updated_at:
            graph.updated_at = datetime.now().isoformat()
        return graph

    def task_graph(self) -> TaskGraph:
        return self._normalize_task_graph()

    def remember_task_graph(self, graph: TaskGraph | dict[str, Any]) -> TaskGraph:
        normalized = self._normalize_task_graph(graph)
        normalized.updated_at = datetime.now().isoformat()
        self.remember(TASK_GRAPH_KEY, asdict(normalized))
        return normalized

    def workspace_locks(self) -> list[WorkspaceLock]:
        raw = self.recall(WORKSPACE_LOCKS_KEY)
        locks: list[WorkspaceLock] = []
        for item in raw if isinstance(raw, list) else []:
            if not isinstance(item, dict):
                continue
            locks.append(WorkspaceLock(
                id=str(item.get("id", "") or "").strip(),
                area=str(item.get("area", "") or "").strip(),
                holder=str(item.get("holder", "") or "").strip(),
                goal_id=str(item.get("goal_id", "") or "").strip(),
                reason=str(item.get("reason", "") or "").strip(),
                acquired_at=str(item.get("acquired_at", "") or "").strip(),
                expires_at=str(item.get("expires_at", "") or "").strip(),
                metadata=item.get("metadata", {}) if isinstance(item.get("metadata", {}), dict) else {},
            ))
        return locks

    def acquire_workspace_lock(self, area: str, holder: str, *, goal_id: str = "", reason: str = "", metadata: dict[str, Any] | None = None, ttl_seconds: int = 300) -> WorkspaceLock:
        locks = self.workspace_locks()
        now = datetime.now().isoformat()
        expires_at = (datetime.now() + timedelta(seconds=int(ttl_seconds))).isoformat() if ttl_seconds > 0 else ""
        lock = WorkspaceLock(
            id=str(uuid.uuid4())[:8],
            area=str(area or "").strip(),
            holder=str(holder or "").strip(),
            goal_id=str(goal_id or "").strip(),
            reason=str(reason or "").strip(),
            acquired_at=now,
            expires_at=expires_at,
            metadata=copy.deepcopy(metadata or {}),
        )
        locks = [asdict(item) for item in locks if item.expires_at and item.expires_at > now or not item.expires_at]
        locks.append(asdict(lock))
        self.remember(WORKSPACE_LOCKS_KEY, locks)
        return lock

    def release_workspace_lock(self, lock_id: str) -> bool:
        locks = self.workspace_locks()
        remaining = [asdict(lock) for lock in locks if str(lock.id) != str(lock_id).strip()]
        self.remember(WORKSPACE_LOCKS_KEY, remaining)
        return len(remaining) != len(locks)

    def clear_workspace_locks(self):
        self.remember(WORKSPACE_LOCKS_KEY, [])

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
            if self._writer_thread.is_alive():
                ErrorHandler.log(
                    RuntimeError("Background writer thread failed to terminate within timeout."),
                    severity=ErrorSeverity.CRITICAL,
                    context="AgentState.join_writer",
                    code=ErrorCode.IO_ERROR,
                )

    def close(self):
        """Flush pending writes, stop the writer thread, and close the state lifecycle."""
        if self._closed:
            return
        self.flush()
        self._closed = True
        self._stop_event.set()
        self._write_queue.put(None)
        self.join_writer(timeout=5)
        if os.name == 'nt':
            time.sleep(0.5)
        for attempt in range(5):
            try:
                with sqlite3.connect(self.db_path, timeout=self.DB_BUSY_TIMEOUT_MS / 1000) as conn:
                    mode = str(conn.execute("PRAGMA journal_mode").fetchone()[0]).lower()
                    if mode == "wal":
                        checkpoint_mode = "TRUNCATE" if os.name == 'nt' else "FULL"
                        conn.execute(f"PRAGMA wal_checkpoint({checkpoint_mode})")
                break
            except sqlite3.DatabaseError as e:
                if attempt == 4:
                    ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="AgentState.close", code=ErrorCode.IO_ERROR)
                time.sleep(0.5)
            except Exception as e:
                ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="AgentState.close", code=ErrorCode.IO_ERROR)
                break
        if os.name == 'nt':
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", ResourceWarning)
                gc.collect()

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

    def list_records(self, key: str) -> list[Any]:
        value = self.recall(key)
        return list(value) if isinstance(value, list) else []

    def append_record(self, key: str, record: Any, limit: int = 200):
        records = self.list_records(key)
        records.append(record)
        if limit > 0 and len(records) > limit:
            records = records[-limit:]
        self.remember(key, records)
        return records

    def replace_records(self, key: str, records: list[Any]):
        self.remember(key, list(records or []))

    def upsert_goal(self, goal_record: dict[str, Any]):
        if not isinstance(goal_record, dict):
            raise TypeError("Goal record must be a dictionary.")
        records = self.list_records(GOAL_RECORDS_KEY)
        goal_id = str(goal_record.get("id", "")).strip()
        if not goal_id:
            raise ValueError("Goal record must include an id.")
        replaced = False
        for index, existing in enumerate(records):
            if isinstance(existing, dict) and str(existing.get("id", "")) == goal_id:
                records[index] = goal_record
                replaced = True
                break
        if not replaced:
            records.append(goal_record)
        self.replace_records(GOAL_RECORDS_KEY, records[-500:])
        return goal_record

    def goal_records(self) -> list[dict[str, Any]]:
        return [item for item in self.list_records(GOAL_RECORDS_KEY) if isinstance(item, dict)]
            
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
    def chat(self, messages: List[Dict[str, str]], temperature: float = 0.1) -> Dict[str, Any]:
        payload = {
            "model": self.model,
            "messages": messages,
            "stream": False,
            "options": {"temperature": float(temperature)}
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
        self.token_data = self._read_token_cache() or {}
        self.github_token = self.token_data.get("access_token") or self._get_github_token()
        self._ensure_session()

    def _read_token_cache(self) -> dict:
        try:
            if os.path.exists(TOKEN_CACHE_FILE):
                with open(TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
                    return json.load(f)
        except Exception:
            pass
        return {}

    def _write_token_cache(self, data: dict) -> None:
        try:
            tmp = TOKEN_CACHE_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f)
            os.replace(tmp, TOKEN_CACHE_FILE)
        except Exception as e:
            print(f"{Colors.YELLOW}[Auth] Warning: failed to write token cache: {e}{Colors.ENDC}")

    def _ensure_session(self, force_refresh=False):
        """Ensures we have a valid short-lived Copilot session token."""
        now = time.time()
        if force_refresh or not self.token_data or now > self.token_data.get("expires_at", 0) - 300:
            try:
                self.token_data = self._refresh_token()
                self.token_data["access_token"] = self.github_token
                self._write_token_cache(self.token_data)
            except urllib.error.HTTPError as e:
                if e.code == 401:
                    print(f"{Colors.RED}[Auth] GitHub Token (OAuth) is invalid or expired. Re-authenticating...{Colors.ENDC}")
                    self.github_token = self._authenticate_device_flow()
                    self.token_data = self._refresh_token()
                    self.token_data["access_token"] = self.github_token
                    self._write_token_cache(self.token_data)
                else:
                    raise e

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
            with urllib.request.urlopen(req, timeout=10) as res:
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
        cache = self._read_token_cache()
        if cache and cache.get("access_token") and cache.get("expires_at", 0) > time.time() + 30:
            return cache.get("access_token")

        token = os.environ.get("GITHUB_TOKEN")
        if token:
            self._write_token_cache({"access_token": token, "expires_at": time.time() + 1500})
            return token

        token = self._authenticate_device_flow()
        self._write_token_cache({"access_token": token, "expires_at": time.time() + 1500})
        return token

    def _refresh_token(self):
        headers = {**COMMON_HEADERS, "Authorization": f"Bearer {self.github_token}"}
        req = urllib.request.Request(COPILOT_TOKEN_URL, headers=headers)
        with urllib.request.urlopen(req, timeout=10) as res:
            data = json.loads(res.read().decode("utf-8"))
            
            # Robust endpoint parsing
            base_url = DEFAULT_COPILOT_API_BASE_URL
            if "token" in data:
                for part in data["token"].split(";"):
                    if part.startswith("proxy-ep="):
                        base_url = f"https://{part.split('=')[1].replace('https://','').replace('proxy.','api.')}"
            
            # Use expires_at from response, or default to 25 mins
            expires_at = data.get("expires_at", time.time() + 1500)
            result = {"token": data["token"], "base_url": base_url, "expires_at": expires_at}
            self._write_token_cache({"access_token": self.github_token, **result})
            return result

    @retry_with_backoff(retries=3, backoff_in_seconds=1)
    def chat(self, messages: List[Dict[str, str]], temperature: float | None = None, **kwargs) -> Dict[str, Any]:
        try:
            self._ensure_session() # Auto-refresh if expired
            
            url = f"{self.token_data['base_url']}/chat/completions"
            headers = {**COMMON_HEADERS, "Authorization": f"Bearer {self.token_data['token']}", "Content-Type": "application/json"}
            payload = {"model": "gpt-5-mini", "messages": messages}
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
        self.agent_type = "generic"
        self.priority = 2
        self.result_path = self.work_dir / "result.txt"
        self.log_path = self.work_dir / f"subagent_{self.id}.log"
        self.spawned_by: dict[str, Any] = {}
        self.goal: dict[str, Any] = {}
        self.ready_condition: dict[str, Any] = {
            "kind": "result_file",
            "path": str(self.result_path),
            "status": "pending",
            "observed_at": "",
        }
        self.lifecycle_policy: dict[str, Any] = {
            "kill": {
                "mode": "terminate_flag",
                "force_supported": False,
                "default_force": False,
            },
            "restart": {
                "supported": True,
                "mode": "manual_respawn",
                "attempts": 0,
            },
        }

    def log(self, msg: str):
        entry = f"[{time.strftime('%H:%M:%S')}] {msg}"
        self.logs.append(entry)
        try:
            self.work_dir.mkdir(parents=True, exist_ok=True)
            with self.log_path.open("a", encoding="utf-8", errors="replace") as fh:
                fh.write(entry + "\n")
        except Exception:
            pass

    def snapshot(self) -> dict[str, Any]:
        result_text = "" if self.result is None else str(self.result)
        if len(result_text) > 100:
            result_preview = result_text[:100] + "..."
        else:
            result_preview = result_text or None
        return {
            "id": self.id,
            "status": self.status.value,
            "task": self.task,
            "agent_type": self.agent_type,
            "priority": self.priority,
            "work_dir": str(self.work_dir),
            "log_path": str(self.log_path),
            "expected_log_path": str(self.log_path),
            "result_path": str(self.result_path),
            "spawned_by": copy.deepcopy(self.spawned_by),
            "goal": copy.deepcopy(self.goal),
            "ready_condition": copy.deepcopy(self.ready_condition),
            "lifecycle_policy": copy.deepcopy(self.lifecycle_policy),
            "result": result_preview,
            "logs_tail": self.logs[-5:],
        }

    def terminate(self):
        self._stop_event = True
        self.status = SubagentStatus.TERMINATED
        self.ready_condition["status"] = "terminated"
        self.log("Termination requested.")

    def run(self):
        self.status = SubagentStatus.RUNNING
        self.work_dir.mkdir(parents=True, exist_ok=True)
        self.ready_condition["status"] = "running"
        self.log(f"Run started for task '{self.task}'.")
        
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
                        self.ready_condition["status"] = "observed"
                        self.ready_condition["observed_at"] = datetime.now().isoformat()
                        self.log("Consensus reached and result captured.")
                        try: self.result_path.write_text(self.result, encoding="utf-8")
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
                self.ready_condition["status"] = "failed"
                self.log(self.result)

        except Exception as e:
            self.status = SubagentStatus.FAILED
            self.result = f"Error during subagent execution: {e}"
            self.ready_condition["status"] = "failed"
            self.log(self.result)

        # Final side-effect write
        try:
            if self.result: self.result_path.write_text(str(self.result), encoding="utf-8")
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

        spawn_meta = self.bot._build_task_spawn_context(
            source="subagent",
            actor="agent",
            source_id="",
        )
        goal_ref = copy.deepcopy(spawn_meta.get("goal", {}))
        lock_area = self.bot._workspace_lock_area(work_dir=work_dir, goal=goal_ref)
        conflict = self.bot._active_workspace_lock(lock_area)
        if conflict:
            holder = str(conflict.get("holder", "") or "").strip()
            if holder.startswith("subagent:"):
                existing_id = holder.split(":", 1)[1]
                if existing_id in self.agents:
                    existing_status = self.agents[existing_id].status
                    if existing_status in [SubagentStatus.RUNNING, SubagentStatus.INIT]:
                        print(f"[SubagentManager] Workspace lock reuse for {lock_area}. Returning existing agent {existing_id}.")
                        return existing_id
            return f"LOCKED:{lock_area}"

        # Resolve Agent Class
        agent_cls = self.agent_registry.get(agent_type, Subagent)
        
        # Instantiate (Expects standard signature)
        try:
            agent = agent_cls(task, Path(work_dir), self.bot, self.bot.get_system_prompt())
        except Exception as e:
            # Fallback to generic if custom init fails
            print(f"Error instantiating {agent_type}: {e}. Falling back to generic.")
            agent = Subagent(task, Path(work_dir), self.bot, self.bot.get_system_prompt())

        agent.agent_type = agent_type
        agent.priority = int(priority)
        agent.result_path = agent.work_dir / "result.txt"
        agent.log_path = agent.work_dir / f"subagent_{agent.id}.log"
        spawn_meta = self.bot._build_task_spawn_context(
            source="subagent",
            actor="agent",
            source_id=agent.id,
        )
        agent.spawned_by = copy.deepcopy(spawn_meta.get("spawned_by", {}))
        agent.goal = copy.deepcopy(spawn_meta.get("goal", {}))
        lock_id, conflict = self.bot._acquire_workspace_lock(
            self.bot._workspace_lock_area(work_dir=work_dir, goal=agent.goal),
            f"subagent:{agent.id}",
            goal=agent.goal,
            reason=f"subagent:{agent_type}",
            metadata={"task": task[:240], "agent_type": agent_type},
        )
        if not lock_id:
            return f"LOCKED:{self.bot._workspace_lock_area(work_dir=work_dir, goal=agent.goal)}"
        agent.workspace_lock_id = lock_id
        agent.ready_condition = {
            "kind": "result_file",
            "path": str(agent.result_path),
            "status": "pending",
            "observed_at": "",
        }
        agent.lifecycle_policy = self.bot._default_task_lifecycle_policy(
            restart_supported=True,
            kill_mode="terminate_flag",
            restart_mode="manual_respawn",
        )
        agent.log(f"Queued with priority={priority} agent_type={agent_type}.")
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
            agent.log(f"Run finished with status={agent.status.value}.")
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
            try:
                lock_id = str(getattr(agent, 'workspace_lock_id', '') or '').strip()
                if lock_id:
                    self.bot._release_workspace_lock(lock_id)
            except Exception:
                pass
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
            aid: a.snapshot()
            for aid, a in self.agents.items()
        }

    def get_load_stats(self):
        return {
            "active": self._active_count,
            "queued": self.queue.qsize(),
            "capacity": self.current_capacity,
            "max_configured": self.max_capacity,
            "types": list(self.agent_registry.keys()),
            "recent_agents": [agent.snapshot() for agent in list(self.agents.values())[-10:]],
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
        self.config = load_runtime_config()
        self.execution_policy = ExecutionPolicyLayer(self.config)
        _log("execution policy created")

        # Idle proposal config controls
        self.idle_proposal_enabled = bool(self.config.get("idle_proposal_enabled", True))
        self.idle_proposal_interval_seconds = int(self.config.get("idle_proposal_interval_seconds", 300))
        self.idle_proposal_auto_confirm = bool(self.config.get("idle_proposal_auto_confirm", True))
        self.heartbeat_interval_seconds = max(1, int(self.config.get("heartbeat_interval_seconds", DEFAULT_HEARTBEAT_INTERVAL_SECONDS) or DEFAULT_HEARTBEAT_INTERVAL_SECONDS))
        self.reviewer_pass_enabled = bool(self.config.get("reviewer_pass_enabled", True))
        self.reviewer_pass_after_tools = bool(self.config.get("reviewer_pass_after_tools", True))
        self.reviewer_pass_after_tests = bool(self.config.get("reviewer_pass_after_tests", True))

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
        self.low_progress_turns = 0
        self.last_progress_evaluation: dict[str, Any] = {}
        self.last_progress_request_signature = ""
        self.current_request_context: dict[str, Any] = {}
        # persistent turn counter used for logging; increments across handle_turn calls
        self.turn_counter = 0
        self.last_observation = ""

        _log("initialized runtime temp state")

        self._heartbeat_lock = threading.Lock()
        self._heartbeat_stop = threading.Event()
        self._runtime_heartbeat = self._load_runtime_heartbeat()
        self._update_runtime_heartbeat(
            current_mode="interactive",
            current_phase="startup",
            current_script_or_project=str(Path.cwd()),
            persist=True,
        )
        self._heartbeat_thread = threading.Thread(target=self._heartbeat_loop, daemon=True)
        self._heartbeat_thread.start()
        _log("heartbeat started")

        # Control flag: If True, the agent must explicitly acknowledge the last observation
        # using the token <ack_observation> before a <consensus> will be accepted.
        self.must_wait_for_observation = False

        # Background proposal agent processes approved proposals and patches core code.
        bg_thread = threading.Thread(target=self._background_proposal_agent, daemon=True)
        bg_thread.start()

        _log("constructor complete")

    # --- event hooks --------------------------------------------------------
    def on_user_input(self, text: str):
        # example: simple fact extraction from user statements
        for m in re.findall(r"I (?:am|have) ([\w ]+)", text, re.I):
            self.brain.remember(m.strip(), True)
        # tag a general fact for later querying
        self.state.append_history("system", f"fact:{text}", tags=["fact"])
        self._update_runtime_heartbeat(
            current_mode="interactive",
            current_phase="inspect",
            last_user_input_at=time.time(),
            current_script_or_project=self._infer_current_script_or_project(text),
            persist=True,
        )
        try:
            self._refresh_project_memory(persist=True)
            self._refresh_task_memory(
                user_input=text,
                current_phase="inspect",
                expected_output=self._expected_output_for_request(text),
            )
        except Exception:
            pass

    def on_tool_output(self, tool_name: str, output: str):
        # store raw tool output with a tool-specific tag for retrieval
        self.state.append_history("system", output, tags=[f"tool:{tool_name}"])
        try:
            detail = self._tool_result_text(output) or str(output or "")
            observation = self._memory_summary_text(f"{tool_name}: {detail}", max_chars=320)
            self._refresh_task_memory(current_phase="verify", observation=observation)
            if self._tool_result_failed(output):
                self._remember_failure_event(observation or detail, command=tool_name)
        except Exception:
            pass

    def _default_runtime_heartbeat(self) -> dict[str, Any]:
        return {
            "heartbeat_at": 0.0,
            "current_mode": "interactive",
            "active_goal_id": "",
            "last_user_input_at": 0.0,
            "last_tool_run_at": 0.0,
            "last_success_at": 0.0,
            "current_phase": "startup",
            "pending_plan_count": 0,
            "current_script_or_project": str(Path.cwd()),
            "last_error_summary": "",
        }

    def _load_runtime_heartbeat(self) -> dict[str, Any]:
        heartbeat = self._default_runtime_heartbeat()
        stored = self.state.get_runtime_value(RUNTIME_HEARTBEAT_KEY, {})
        if isinstance(stored, dict):
            for key in heartbeat:
                if key in stored:
                    heartbeat[key] = copy.deepcopy(stored[key])
        if not heartbeat.get("current_script_or_project"):
            heartbeat["current_script_or_project"] = str(Path.cwd())
        return heartbeat

    def _heartbeat_active_goal_id(self) -> str:
        goals = self.active_goals()
        if not goals:
            return ""
        return str(goals[0].get("id", "") or "")

    def _heartbeat_pending_plan_count(self) -> int:
        try:
            return len(self.state.query_history(tag="plan", limit=20))
        except Exception:
            return 0

    def _trim_heartbeat_text(self, value: str, max_chars: int = 400) -> str:
        text = str(value or "").strip()
        if len(text) <= max_chars:
            return text
        return text[: max_chars - 3].rstrip() + "..."

    def _infer_current_script_or_project(self, text: str) -> str:
        source = str(text or "").strip()
        if not source:
            return str(Path.cwd())

        patterns = [
            r'["\']([^"\']+\.(?:py|ipynb|md|json|ya?ml|txt|sh|bat|ps1|js|ts|tsx|jsx|html|css))["\']',
            r'([A-Za-z]:[\\/][^\s"\']+)',
            r'((?:\.{0,2}[\\/])?[^\s"\']+\.(?:py|ipynb|md|json|ya?ml|txt|sh|bat|ps1|js|ts|tsx|jsx|html|css))',
        ]
        for pattern in patterns:
            match = re.search(pattern, source)
            if match:
                return self._trim_heartbeat_text(match.group(1), max_chars=240)

        lowered = source.lower()
        if any(token in lowered for token in ("pytest", "unittest", "project", "workspace", "repo", "repository")):
            return self._trim_heartbeat_text(str(Path.cwd()), max_chars=240)
        return self._trim_heartbeat_text(source.splitlines()[0], max_chars=240)

    def _update_runtime_heartbeat(self, persist: bool = False, **fields) -> dict[str, Any]:
        with self._heartbeat_lock:
            heartbeat = copy.deepcopy(self._runtime_heartbeat)
            for key, value in fields.items():
                if value is None:
                    continue
                if key == "last_error_summary":
                    heartbeat[key] = self._trim_heartbeat_text(value, max_chars=400)
                elif key == "current_script_or_project":
                    heartbeat[key] = self._trim_heartbeat_text(value, max_chars=240)
                else:
                    heartbeat[key] = value
            heartbeat["active_goal_id"] = self._heartbeat_active_goal_id()
            heartbeat["pending_plan_count"] = self._heartbeat_pending_plan_count()
            if not heartbeat.get("current_script_or_project"):
                heartbeat["current_script_or_project"] = str(Path.cwd())
            if persist:
                heartbeat["heartbeat_at"] = time.time()
            self._runtime_heartbeat = heartbeat
            snapshot = copy.deepcopy(heartbeat)

        if persist:
            try:
                self.state.set_runtime_value(RUNTIME_HEARTBEAT_KEY, snapshot, persist=True)
            except RuntimeError:
                pass
        return snapshot

    def runtime_heartbeat(self) -> dict[str, Any]:
        return self._update_runtime_heartbeat(persist=False)

    def _note_runtime_success(self, summary: str = "", *, current_phase: str = "completed", current_mode: str | None = None, persist: bool = True):
        previous_error = ""
        try:
            previous_error = str(self.runtime_heartbeat().get("last_error_summary", "") or "").strip()
        except Exception:
            previous_error = ""
        fields: dict[str, Any] = {
            "last_success_at": time.time(),
            "current_phase": current_phase,
            "last_error_summary": "",
        }
        if current_mode is not None:
            fields["current_mode"] = current_mode
        if summary:
            fields["current_script_or_project"] = self._infer_current_script_or_project(summary)
        self._update_runtime_heartbeat(persist=persist, **fields)
        try:
            if summary:
                self._refresh_task_memory(current_phase=current_phase, observation=summary)
            if previous_error and summary:
                self._remember_recovery_pattern(previous_error, summary)
        except Exception:
            pass

    def _note_runtime_error(self, summary: str, *, current_phase: str = "blocked", current_mode: str | None = None, persist: bool = True, command: str = ""):
        fields: dict[str, Any] = {
            "current_phase": current_phase,
            "last_error_summary": summary,
        }
        if current_mode is not None:
            fields["current_mode"] = current_mode
        self._update_runtime_heartbeat(persist=persist, **fields)
        try:
            self._refresh_task_memory(current_phase=current_phase, observation=summary)
            self._remember_failure_event(summary, command=command)
        except Exception:
            pass

    def _note_tool_start(self, tool_name: str, payload: str, *, persist: bool = True):
        target = self._infer_current_script_or_project(payload)
        self._update_runtime_heartbeat(
            current_mode="interactive",
            current_phase="act",
            last_tool_run_at=time.time(),
            current_script_or_project=target or tool_name,
            persist=persist,
        )

    def _note_tool_result(self, tool_name: str, result: str, *, persist: bool = True):
        payload = self._parse_tool_result_payload(result)
        ok = bool(payload.get("ok", False)) if payload else not self._tool_result_failed(result)
        if ok:
            summary = self._tool_result_text(result) or (payload.get("summary", "") if payload else "")
            self._note_runtime_success(summary, current_phase="verify", persist=persist)
            return
        detail = self._tool_result_text(result)
        if not detail and payload:
            detail = str(payload.get("summary", "") or "")
        self._note_runtime_error(f"{tool_name}: {detail or 'tool execution failed'}", current_phase="blocked", persist=persist, command=tool_name)

    def _heartbeat_loop(self):
        while not self._heartbeat_stop.wait(self.heartbeat_interval_seconds):
            try:
                self._update_runtime_heartbeat(persist=True)
            except Exception as e:
                ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="FlexiBot._heartbeat_loop", code=ErrorCode.IO_ERROR)

    def stop_runtime_heartbeat(self, reason: str = ""):
        try:
            self._update_runtime_heartbeat(
                current_mode="shutdown",
                current_phase="shutdown",
                last_error_summary=reason if reason and "error" in reason.lower() else self.runtime_heartbeat().get("last_error_summary", ""),
                persist=True,
            )
        except Exception:
            pass
        self._heartbeat_stop.set()
        thread = getattr(self, "_heartbeat_thread", None)
        if isinstance(thread, threading.Thread) and thread.is_alive():
            thread.join(timeout=2)

    def _memory_summary_text(self, value: Any, *, max_chars: int = 240) -> str:
        text = re.sub(r"\s+", " ", str(value or "")).strip()
        if not text:
            return ""
        return self._trim_heartbeat_text(text, max_chars=max_chars)

    def _merge_memory_items(self, current: list[str], additions: list[str], *, limit: int = 12, max_chars: int = 240) -> list[str]:
        merged: list[str] = []
        seen: set[str] = set()
        for raw in list(current or []) + list(additions or []):
            text = self._memory_summary_text(raw, max_chars=max_chars)
            if not text or text in seen:
                continue
            seen.add(text)
            merged.append(text)
        return merged[-max(1, int(limit)):]

    def _default_project_conventions(self) -> list[str]:
        return [
            "Prefer safe_inspect, inspect_file_chunk, read_range, or peek over giant object dumps.",
            "Use actual tool output plus reviewer guidance to finalize or block work instead of speculating.",
            "Keep project, task, and failure memory updated when new durable facts or repeat failures appear.",
        ]

    def _discover_project_entrypoints(self) -> list[str]:
        root = Path.cwd()
        entrypoints = [path.name for path in sorted(root.glob("*.py")) if path.is_file() and not path.name.startswith(".")]
        return entrypoints[:12]

    def _discover_project_architecture(self) -> list[str]:
        root = Path.cwd()
        lines: list[str] = []
        if (root / "flexiFocus.py").exists():
            lines.append("flexiFocus.py is the main agent runtime and orchestration entrypoint.")
        top_dirs = [path.name for path in sorted(root.iterdir()) if path.is_dir() and not path.name.startswith(".")]
        if top_dirs:
            lines.append(f"Top-level directories: {', '.join(top_dirs[:8])}")
        top_py = [path.name for path in sorted(root.glob("*.py")) if path.is_file() and not path.name.startswith(".")]
        if top_py:
            lines.append(f"Top-level Python files: {', '.join(top_py[:8])}")
        if (root / "tests").exists():
            lines.append("Regression coverage lives under tests/.")
        return lines[:8]

    def _discover_project_dependencies(self, *, max_files: int = 80) -> list[str]:
        root = Path.cwd()
        stdlib_modules = set(getattr(sys, "stdlib_module_names", set()))
        local_modules = {path.stem for path in root.glob("*.py")}
        local_modules.update(path.name for path in root.iterdir() if path.is_dir())
        skip_dirs = {".git", ".flexi", "__pycache__", ".pytest_cache", ".mypy_cache", "node_modules"}
        python_files: list[Path] = []
        for current_root, dirs, files in os.walk(root):
            dirs[:] = [name for name in dirs if name not in skip_dirs and not name.startswith(".")]
            for file_name in files:
                if not file_name.endswith(".py") or file_name.startswith("."):
                    continue
                python_files.append(Path(current_root) / file_name)
                if len(python_files) >= max_files:
                    break
            if len(python_files) >= max_files:
                break

        dependencies: set[str] = set()
        for source_path in python_files:
            try:
                tree = ast.parse(source_path.read_text(encoding="utf-8", errors="replace"), filename=str(source_path))
            except Exception:
                continue
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        top_level = str(alias.name or "").split(".", 1)[0].strip()
                        if top_level:
                            dependencies.add(top_level)
                elif isinstance(node, ast.ImportFrom) and node.module:
                    top_level = str(node.module or "").split(".", 1)[0].strip()
                    if top_level:
                        dependencies.add(top_level)

        filtered = sorted(
            dep for dep in dependencies
            if dep and dep not in stdlib_modules and dep not in local_modules and dep != "__future__"
        )
        return filtered[:20]

    def _current_milestones(self) -> list[str]:
        milestones: list[str] = []
        for goal in self.active_goals()[:8]:
            line = f"[{goal.get('id')}] {goal.get('status')}: {goal.get('text')}"
            if goal.get("next_action"):
                line += f" -> {goal.get('next_action')}"
            milestones.append(self._memory_summary_text(line, max_chars=280))
        return [item for item in milestones if item]

    def _refresh_project_memory(self, *, persist: bool = True) -> ProjectMemory:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "project_memory"):
            return ProjectMemory()

        memory = state.project_memory()
        changed = False
        workspace_path = str(Path.cwd())
        if memory.workspace_path != workspace_path:
            memory.workspace_path = workspace_path
            changed = True

        merged_architecture = self._merge_memory_items(memory.architecture, self._discover_project_architecture(), limit=16, max_chars=260)
        if merged_architecture != memory.architecture:
            memory.architecture = merged_architecture
            changed = True

        merged_conventions = self._merge_memory_items(memory.conventions, self._default_project_conventions(), limit=16, max_chars=260)
        if merged_conventions != memory.conventions:
            memory.conventions = merged_conventions
            changed = True

        merged_entrypoints = self._merge_memory_items(memory.entrypoints, self._discover_project_entrypoints(), limit=16, max_chars=200)
        if merged_entrypoints != memory.entrypoints:
            memory.entrypoints = merged_entrypoints
            changed = True

        merged_dependencies = self._merge_memory_items(memory.dependencies, self._discover_project_dependencies(), limit=24, max_chars=120)
        if merged_dependencies != memory.dependencies:
            memory.dependencies = merged_dependencies
            changed = True

        milestones = self._current_milestones()
        if milestones != memory.current_milestones:
            memory.current_milestones = milestones
            changed = True

        if changed and persist:
            return state.remember_project_memory(memory)
        return memory

    def _refresh_project_brief(self, *, persist: bool = True) -> ProjectBrief:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "project_brief"):
            return ProjectBrief()

        brief = state.project_brief()
        if not brief.workspace_path:
            brief.workspace_path = str(Path.cwd())
        if not brief.entrypoints:
            brief.entrypoints = self._discover_project_entrypoints()
        if not brief.stack:
            brief.stack = self._discover_project_dependencies()[:8]
        if not brief.build_commands and not brief.test_commands:
            build_commands, test_commands, deployment_shape = self._discover_project_commands()
            brief.build_commands = build_commands
            brief.test_commands = test_commands
            brief.deployment_shape = deployment_shape
        if not brief.current_milestone:
            milestones = self._current_milestones()
            brief.current_milestone = milestones[0] if milestones else ""
        if persist:
            return state.remember_project_brief(brief)
        return brief

    def _discover_project_commands(self) -> tuple[list[str], list[str], str]:
        root = Path.cwd()
        build_commands: list[str] = []
        test_commands: list[str] = []
        deployment_shape = "unknown"

        if (root / "pyproject.toml").exists():
            build_commands.append("python -m build")
            test_commands.append("pytest")
        if (root / "requirements.txt").exists():
            build_commands.append("pip install -r requirements.txt")
        if (root / "setup.py").exists():
            build_commands.append(f"{sys.executable} setup.py install")
        if (root / "package.json").exists():
            build_commands.append("npm install")
            test_commands.append("npm test")
            deployment_shape = "containerized or Node.js service"
        if (root / "Dockerfile").exists():
            deployment_shape = "Docker container"
        elif (root / "Procfile").exists():
            deployment_shape = "process-based deployment"
        elif (root / "server.py").exists():
            deployment_shape = "Python web service"
        if not test_commands:
            if (root / "tests").exists() or any(root.glob("test_*.py")):
                test_commands.append(f"{sys.executable} -m pytest")
        return build_commands[:8], test_commands[:8], deployment_shape

    def _goal_target_files(self, goal: dict[str, Any], task_memory: TaskMemory | None = None) -> list[str]:
        files: list[str] = []
        workspace_path = str(goal.get("workspace_path", "") or "").strip()
        if workspace_path:
            files.append(workspace_path)
        verification_target = str(goal.get("verification_target", "") or "").strip()
        if verification_target and "/" in verification_target or "\\" in verification_target or verification_target.endswith(".py"):
            files.append(verification_target)
        goal_id = str(goal.get("id", "") or "").strip()
        if task_memory is not None and goal_id and task_memory.active_goal_id == goal_id:
            files.extend(task_memory.touched_files)
        return self._merge_memory_items([], files, limit=12, max_chars=220)

    def _scoped_verification_target(self) -> str:
        node = self._current_task_graph_node()
        if node and str(node.verification_target or "").strip():
            return str(node.verification_target or "").strip()
        goal = self.current_goal()
        if goal and str(goal.get("verification_target", "") or "").strip():
            return str(goal.get("verification_target", "") or "").strip()
        brief = self._refresh_project_brief(persist=True)
        if brief.test_commands:
            return str(brief.test_commands[0] or "").strip()
        return ""

    def _refresh_task_graph(self, *, persist: bool = True) -> TaskGraph:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "task_graph"):
            return TaskGraph()

        graph = state.task_graph()
        task_memory = state.task_memory() if hasattr(state, "task_memory") else TaskMemory()
        nodes: list[TaskGraphNode] = []
        for goal in self.active_goals()[:24]:
            goal_id = str(goal.get("id", "") or "").strip()
            nodes.append(
                TaskGraphNode(
                    id=goal_id,
                    title=str(goal.get("text", "") or "").strip(),
                    description=str(goal.get("done_when", "") or goal.get("blocked_reason", "") or "").strip(),
                    target_files=self._goal_target_files(goal, task_memory=task_memory),
                    dependencies=[str(goal.get("parent_goal_id", "") or "").strip()] if goal.get("parent_goal_id") else [],
                    verification_target=str(goal.get("verification_target", "") or "").strip(),
                    goal_id=goal_id,
                    status=str(goal.get("status", GOAL_STATUS_PENDING) or GOAL_STATUS_PENDING).strip(),
                )
            )
        graph.nodes = nodes
        if persist:
            return state.remember_task_graph(graph)
        return graph

    def _current_task_graph_node(self) -> TaskGraphNode | None:
        graph = self._refresh_task_graph(persist=True)
        current = self.current_goal()
        current_goal_id = str(current.get("id", "") or "").strip() if current else ""
        for node in graph.nodes:
            if str(node.goal_id or "").strip() == current_goal_id:
                return node
        return graph.nodes[0] if graph.nodes else None

    def _expected_output_for_request(self, user_input: str) -> str:
        goal = self.current_goal()
        hints: list[str] = []
        if goal and goal.get("done_when"):
            hints.append(str(goal.get("done_when")))
        if goal and goal.get("verification_target"):
            hints.append(f"Verify against {goal.get('verification_target')}")
        if not hints:
            hints.append(str(user_input or "").strip())
        return self._memory_summary_text("; ".join(hints), max_chars=320)

    def _refresh_task_memory(self, *, user_input: str | None = None, current_phase: str | None = None,
                             expected_output: str | None = None, touched_files: list[str] | None = None,
                             observation: str | None = None) -> TaskMemory | None:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "task_memory"):
            return None

        memory = state.task_memory()
        request_context = copy.deepcopy(getattr(self, "current_request_context", {}) or {})
        request_signature = str(request_context.get("request_signature", "") or memory.request_signature).strip()
        if user_input is not None:
            computed_signature = self._progress_request_signature(user_input)
            if computed_signature and computed_signature != "__continue__":
                request_signature = computed_signature
                if request_signature != memory.request_signature:
                    memory.touched_files = []
                    memory.last_observations = []
                memory.current_operation = self._memory_summary_text(user_input, max_chars=320)
                memory.expected_output = self._memory_summary_text(expected_output or self._expected_output_for_request(user_input), max_chars=320)

        if request_signature and request_signature != "__continue__":
            memory.request_signature = request_signature

        goal = self.current_goal()
        memory.active_goal_id = str(goal.get("id", "") if goal else "")
        if current_phase is not None:
            memory.current_phase = str(current_phase or "").strip()
        if touched_files:
            memory.touched_files = self._merge_memory_items(memory.touched_files, list(touched_files), limit=20, max_chars=200)
        if observation:
            memory.last_observations = self._merge_memory_items(memory.last_observations, [observation], limit=8, max_chars=280)
        return state.remember_task_memory(memory)

    def _normalize_failure_signature(self, text: str) -> str:
        normalized = str(text or "").lower()
        normalized = re.sub(r"[A-Za-z]:[\\/][^\s]+", "<path>", normalized)
        normalized = re.sub(r"[/\\][\w./\\-]+", "<path>", normalized)
        normalized = re.sub(r"\b\d+\b", "<n>", normalized)
        normalized = re.sub(r"\s+", " ", normalized).strip()
        return normalized[:220]

    def _extract_missing_dependency(self, text: str) -> str:
        sample = str(text or "")
        patterns = [
            r"No module named ['\"]([^'\"]+)['\"]",
            r"ModuleNotFoundError: No module named ['\"]([^'\"]+)['\"]",
            r"command not found:?\s*([A-Za-z0-9_.-]+)",
            r"'([^']+)' is not recognized as an internal or external command",
        ]
        for pattern in patterns:
            match = re.search(pattern, sample, re.I)
            if match:
                return str(match.group(1) or "").strip()
        return ""

    def _upsert_failure_record(self, records: list[dict[str, Any]], *, key: str, value: str, defaults: dict[str, Any]) -> list[dict[str, Any]]:
        now = datetime.now().isoformat()
        for record in records:
            if str(record.get(key, "")).strip() != value:
                continue
            record["count"] = int(record.get("count", 0) or 0) + 1
            record["last_seen"] = now
            for field_name, field_value in defaults.items():
                if field_value and not record.get(field_name):
                    record[field_name] = field_value
            return records
        fresh = {key: value, "count": 1, "last_seen": now, **defaults}
        records.append(fresh)
        return records[-25:]

    def _remember_failure_event(self, summary: str, *, command: str = "") -> FailureMemory | None:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "failure_memory"):
            return None

        detail = self._memory_summary_text(summary, max_chars=320)
        if not detail:
            return None
        signature = self._normalize_failure_signature(detail)
        memory = state.failure_memory()
        memory.recurring_errors = self._upsert_failure_record(
            memory.recurring_errors,
            key="signature",
            value=signature,
            defaults={"example": detail},
        )

        command_text = self._memory_summary_text(command, max_chars=260)
        if command_text:
            memory.known_bad_commands = self._upsert_failure_record(
                memory.known_bad_commands,
                key="command",
                value=command_text,
                defaults={"reason": detail},
            )

        missing_dependency = self._extract_missing_dependency(detail)
        if missing_dependency:
            memory.missing_dependencies = self._upsert_failure_record(
                memory.missing_dependencies,
                key="dependency",
                value=missing_dependency,
                defaults={"error": detail},
            )
        return state.remember_failure_memory(memory)

    def _remember_recovery_pattern(self, error_summary: str, recovery_summary: str) -> FailureMemory | None:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "failure_memory"):
            return None
        error_text = self._memory_summary_text(error_summary, max_chars=320)
        recovery_text = self._memory_summary_text(recovery_summary, max_chars=320)
        if not error_text or not recovery_text:
            return None
        signature = self._normalize_failure_signature(error_text)
        memory = state.failure_memory()
        memory.recovery_patterns = self._upsert_failure_record(
            memory.recovery_patterns,
            key="signature",
            value=signature,
            defaults={"recovery": recovery_text, "error": error_text},
        )
        for record in memory.recovery_patterns:
            if str(record.get("signature", "")).strip() == signature:
                record["recovery"] = recovery_text
                break
        return state.remember_failure_memory(memory)

    def _project_memory_payload(self) -> dict[str, Any]:
        memory = self._refresh_project_memory(persist=True)
        return asdict(memory)

    def _task_memory_payload(self) -> dict[str, Any]:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "task_memory"):
            return asdict(TaskMemory())
        return asdict(state.task_memory())

    def _failure_memory_payload(self) -> dict[str, Any]:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "failure_memory"):
            return asdict(FailureMemory())
        return asdict(state.failure_memory())

    def _search_typed_memory(self, query: str) -> list[str]:
        lowered = str(query or "").strip().lower()
        if not lowered:
            return []
        project_payload = self._project_memory_payload()
        task_payload = self._task_memory_payload()
        failure_payload = self._failure_memory_payload()
        matches: list[str] = []

        for section, values in {
            "project.architecture": project_payload.get("architecture", []),
            "project.conventions": project_payload.get("conventions", []),
            "project.entrypoints": project_payload.get("entrypoints", []),
            "project.dependencies": project_payload.get("dependencies", []),
            "project.current_milestones": project_payload.get("current_milestones", []),
            "task.touched_files": task_payload.get("touched_files", []),
            "task.last_observations": task_payload.get("last_observations", []),
        }.items():
            for item in values:
                if lowered in str(item).lower():
                    matches.append(f"[{section}] {item}")

        for field_name in ("current_operation", "expected_output"):
            value = str(task_payload.get(field_name, "") or "")
            if value and lowered in value.lower():
                matches.append(f"[task.{field_name}] {value}")

        for section_name in ("recurring_errors", "known_bad_commands", "missing_dependencies", "recovery_patterns"):
            for record in failure_payload.get(section_name, []):
                rendered = ", ".join(f"{key}={value}" for key, value in record.items() if value not in (None, "", [], {}))
                if rendered and lowered in rendered.lower():
                    matches.append(f"[failure.{section_name}] {rendered}")
        return matches[:40]

    def _render_memory_context(self) -> str:
        state = getattr(self, "state", None)
        if state is None or not hasattr(state, "project_memory"):
            return ""

        project = state.project_memory()
        task = state.task_memory()
        failure = state.failure_memory()
        lines: list[str] = []

        if project.architecture or project.conventions or project.entrypoints or project.dependencies or project.current_milestones:
            lines.append("PROJECT MEMORY:")
            if project.architecture:
                lines.append(f"   - Architecture: {'; '.join(project.architecture[:3])}")
            if project.conventions:
                lines.append(f"   - Conventions: {'; '.join(project.conventions[:3])}")
            if project.entrypoints:
                lines.append(f"   - Entrypoints: {', '.join(project.entrypoints[:6])}")
            if project.dependencies:
                lines.append(f"   - Dependencies: {', '.join(project.dependencies[:8])}")
            if project.current_milestones:
                lines.append(f"   - Milestones: {'; '.join(project.current_milestones[:4])}")

        if task.current_operation or task.expected_output or task.touched_files or task.last_observations:
            lines.append("TASK MEMORY:")
            if task.current_operation:
                lines.append(f"   - Operation: {task.current_operation}")
            if task.expected_output:
                lines.append(f"   - Expected Output: {task.expected_output}")
            if task.touched_files:
                lines.append(f"   - Touched Files: {', '.join(task.touched_files[:8])}")
            if task.last_observations:
                lines.append(f"   - Last Observations: {'; '.join(task.last_observations[:3])}")

        failure_lines: list[str] = []
        if failure.recurring_errors:
            failure_lines.append("recurring errors: " + "; ".join(str(item.get("example") or item.get("signature") or "") for item in failure.recurring_errors[:3] if item))
        if failure.known_bad_commands:
            failure_lines.append("bad commands: " + "; ".join(str(item.get("command") or "") for item in failure.known_bad_commands[:3] if item))
        if failure.missing_dependencies:
            failure_lines.append("missing deps: " + "; ".join(str(item.get("dependency") or "") for item in failure.missing_dependencies[:3] if item))
        if failure.recovery_patterns:
            failure_lines.append("recoveries: " + "; ".join(str(item.get("recovery") or "") for item in failure.recovery_patterns[:2] if item))
        if failure_lines:
            lines.append("FAILURE MEMORY:")
            for line in failure_lines:
                lines.append(f"   - {line}")

        generic_keys = [key for key in self.state.structured_memory.keys() if key not in {PROJECT_MEMORY_KEY, TASK_MEMORY_KEY, FAILURE_MEMORY_KEY, GOAL_RECORDS_KEY, REVIEWER_EVENT_KEY, RUNTIME_HEARTBEAT_KEY}]
        if generic_keys:
            lines.append(f"   - Known Generic Memory Tags: {', '.join(generic_keys[:10])}")
        return ("\n" + "\n".join(lines)) if lines else ""

    def _render_project_brief_block(self, brief: ProjectBrief) -> str:
        if not brief or not (brief.stack or brief.entrypoints or brief.build_commands or brief.test_commands or brief.deployment_shape or brief.current_milestone):
            return ""
        lines = ["PROJECT BRIEF:"]
        if brief.stack:
            lines.append(f"   - Stack: {', '.join(brief.stack[:6])}")
        if brief.entrypoints:
            lines.append(f"   - Entrypoints: {', '.join(brief.entrypoints[:6])}")
        if brief.build_commands:
            lines.append(f"   - Build Commands: {', '.join(brief.build_commands[:4])}")
        if brief.test_commands:
            lines.append(f"   - Test Commands: {', '.join(brief.test_commands[:4])}")
        if brief.deployment_shape:
            lines.append(f"   - Deployment: {brief.deployment_shape}")
        if brief.current_milestone:
            lines.append(f"   - Current Milestone: {brief.current_milestone}")
        return "\n" + "\n".join(lines) + "\n\n"

    def _render_task_graph_block(self, graph: TaskGraph) -> str:
        if not graph or not graph.nodes:
            return ""
        lines = ["TASK GRAPH:"]
        for node in graph.nodes[:4]:
            node_lines = [
                f"   - [{node.id}] {node.title}",
            ]
            if node.target_files:
                node_lines.append(f"     * targets: {', '.join(node.target_files[:5])}")
            if node.dependencies:
                node_lines.append(f"     * deps: {', '.join(node.dependencies[:5])}")
            if node.verification_target:
                node_lines.append(f"     * verify: {node.verification_target}")
            lines.extend(node_lines)
        return "\n" + "\n".join(lines) + "\n\n"

    def _normalize_tool_payload(self, payload: str) -> str:
        if not isinstance(payload, str):
            payload = str(payload)
        return re.sub(r"\s+", " ", payload).strip()

    def _tool_result_failed(self, result: str) -> bool:
        payload = self._parse_tool_result_payload(result)
        if payload is not None:
            return not bool(payload.get("ok", False))
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

    def _report_tool_execution_status(self, result: str) -> bool:
        failed = self._tool_result_failed(result)
        payload = self._parse_tool_result_payload(result) or {}
        summary = str(payload.get("summary", "") or "").strip()
        if not summary:
            summary = self._tool_result_highlight(result, prefer_error=failed, max_chars=160)
        summary = re.sub(r"\s+", " ", summary).strip()
        prefix = "  -> Tool exit FAILED." if failed else "  -> Tool exit OK."
        if summary:
            prefix = f"{prefix} {summary}"
        color = Colors.RED if failed else Colors.DIM
        print(f"{color}{prefix}{Colors.ENDC}")
        return failed

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

    def _progress_request_signature(self, user_input: str) -> str:
        text = self._normalize_tool_payload(user_input or "")
        if not text:
            return ""
        continuation_markers = {
            "continue",
            "retry",
            "again",
            "resume",
            "keep going",
            "go on",
            "proceed",
        }
        lowered = text.lower()
        if lowered in continuation_markers:
            return "__continue__"
        return lowered[:240]

    def _snapshot_workspace_progress(self) -> dict[str, dict[str, int]]:
        root = Path.cwd()
        snapshot: dict[str, dict[str, int]] = {}
        skip_dirs = {".git", ".flexi", "__pycache__", ".pytest_cache", ".mypy_cache", "node_modules"}
        for current_root, dirs, files in os.walk(root):
            dirs[:] = [name for name in dirs if name not in skip_dirs and not name.startswith(".")]
            base = Path(current_root)
            for file_name in files:
                if file_name.startswith("."):
                    continue
                path = base / file_name
                try:
                    stat = path.stat()
                    rel_path = path.relative_to(root).as_posix()
                except Exception:
                    continue
                snapshot[rel_path] = {
                    "size": int(stat.st_size),
                    "mtime_ns": int(getattr(stat, "st_mtime_ns", int(stat.st_mtime * 1_000_000_000))),
                }
        return snapshot

    def _snapshot_state_progress(self) -> dict[str, Any]:
        memory = self.state.memory
        filtered_memory = {
            key: memory[key]
            for key in sorted(memory)
            if key not in {GOAL_RECORDS_KEY, REVIEWER_EVENT_KEY, RUNTIME_HEARTBEAT_KEY}
        }
        return {
            "memory": filtered_memory,
            "active_processes": self.state.active_processes,
        }

    def _snapshot_goal_progress(self) -> dict[str, dict[str, Any]]:
        snapshot: dict[str, dict[str, Any]] = {}
        for goal in self.state.goal_records():
            normalized = self._normalize_goal_record(goal)
            goal_id = str(normalized.get("id", "")).strip()
            if not goal_id:
                continue
            snapshot[goal_id] = {
                "status": normalized.get("status", ""),
                "next_action": normalized.get("next_action", ""),
                "done_when": normalized.get("done_when", ""),
                "verification_target": normalized.get("verification_target", ""),
                "completed_at": normalized.get("completed_at", ""),
                "evidence": list(normalized.get("evidence", []) or []),
            }
        return snapshot

    def _capture_turn_progress_baseline(self) -> dict[str, Any]:
        return {
            "workspace": self._snapshot_workspace_progress(),
            "state": self._snapshot_state_progress(),
            "goals": self._snapshot_goal_progress(),
            "heartbeat": self.runtime_heartbeat(),
            "observation_blocked": self._last_observation_indicates_blocked(),
        }

    def _diff_workspace_progress(self, before: dict[str, dict[str, int]], after: dict[str, dict[str, int]]) -> list[str]:
        changed: list[str] = []
        for rel_path in sorted(set(before) | set(after)):
            if before.get(rel_path) != after.get(rel_path):
                changed.append(rel_path)
        return changed

    def _diff_state_progress(self, before: dict[str, Any], after: dict[str, Any]) -> list[str]:
        changed: list[str] = []
        for key in ("memory", "active_processes"):
            if before.get(key) != after.get(key):
                changed.append(key)
        return changed

    def _goal_advancement_details(self, before: dict[str, dict[str, Any]], after: dict[str, dict[str, Any]]) -> list[str]:
        details: list[str] = []
        status_rank = {
            GOAL_STATUS_PENDING: 0,
            GOAL_STATUS_ACTIVE: 1,
            GOAL_STATUS_COMPLETED: 3,
            GOAL_STATUS_CANCELLED: 2,
            GOAL_STATUS_FAILED: 2,
        }
        for goal_id in sorted(set(before) | set(after)):
            before_goal = before.get(goal_id)
            after_goal = after.get(goal_id)
            if before_goal is None and after_goal is not None:
                details.append(f"goal_added:{goal_id}")
                continue
            if before_goal is None or after_goal is None:
                continue
            if status_rank.get(str(after_goal.get("status", "")), 0) > status_rank.get(str(before_goal.get("status", "")), 0):
                details.append(f"goal_status:{goal_id}:{before_goal.get('status')}->{after_goal.get('status')}")
            if str(after_goal.get("next_action", "")).strip() and after_goal.get("next_action") != before_goal.get("next_action"):
                details.append(f"goal_next_action:{goal_id}")
            if len(after_goal.get("evidence", []) or []) > len(before_goal.get("evidence", []) or []):
                details.append(f"goal_evidence:{goal_id}")
            if str(after_goal.get("completed_at", "")).strip() and after_goal.get("completed_at") != before_goal.get("completed_at"):
                details.append(f"goal_completed:{goal_id}")
        return details

    def _evaluate_turn_progress(self, baseline: dict[str, Any], finalize_meta: dict[str, Any], tool_results: list[str]) -> dict[str, Any]:
        after_workspace = self._snapshot_workspace_progress()
        after_state = self._snapshot_state_progress()
        after_goals = self._snapshot_goal_progress()
        after_heartbeat = self.runtime_heartbeat()

        changed_files = self._diff_workspace_progress(baseline.get("workspace", {}), after_workspace)
        changed_state = self._diff_state_progress(baseline.get("state", {}), after_state)
        goal_advances = self._goal_advancement_details(baseline.get("goals", {}), after_goals)

        before_heartbeat = baseline.get("heartbeat", {}) or {}
        had_error_before = bool(str(before_heartbeat.get("last_error_summary", "")).strip()) or bool(baseline.get("observation_blocked", False))
        has_error_after = bool(str(after_heartbeat.get("last_error_summary", "")).strip()) or bool(finalize_meta.get("blocked"))
        resolved_error = had_error_before and not has_error_after

        score = 0
        if changed_files:
            score += 2
        if changed_state:
            score += 1
        if resolved_error:
            score += 2
        if goal_advances:
            score += 2

        tool_failures = sum(1 for result in tool_results if self._tool_result_failed(result))
        return {
            "score": score,
            "low_progress": score <= 0,
            "changed_files": changed_files,
            "changed_state": changed_state,
            "goal_advances": goal_advances,
            "resolved_error": resolved_error,
            "tool_failures": tool_failures,
        }

    def _low_progress_strategy_message(self, progress_eval: dict[str, Any]) -> str:
        gaps = []
        if not progress_eval.get("changed_files"):
            gaps.append("changed no workspace files")
        if not progress_eval.get("changed_state"):
            gaps.append("changed no meaningful runtime state")
        if not progress_eval.get("resolved_error"):
            gaps.append("resolved no prior error")
        if not progress_eval.get("goal_advances"):
            gaps.append("advanced no active goal")
        gap_text = ", ".join(gaps) if gaps else "made no measurable progress"
        return (
            "Blocked: The last two action turns were low progress. They "
            f"{gap_text}. Switch strategy before acting again: make a targeted file change, update the active goal, "
            "run a narrower verification, or ask the user for missing information instead of repeating inspection attempts."
        )

    def _user_requested_options(self, user_input: str) -> bool:
        text = (user_input or "").lower()
        if not text:
            return False
        option_markers = (
            "option",
            "options",
            "choose",
            "which one",
            "which should",
            "what next",
            "next step",
            "pick one",
            "a/b/c",
            "menu",
        )
        return any(marker in text for marker in option_markers)

    def _last_observation_indicates_blocked(self) -> bool:
        observation = (self.last_observation or "").lower()
        if not observation:
            return False
        blocked_markers = (
            "error",
            "failed",
            "traceback",
            "timed out",
            "execution blocked",
            "must acknowledge",
            "awaiting <ack_observation>",
            "no action detected",
            "stopping after repeated identical actions",
        )
        return any(marker in observation for marker in blocked_markers)

    def _find_followup_cutoff(self, text: str) -> int | None:
        lines = text.splitlines()
        for idx, line in enumerate(lines):
            stripped = line.strip()
            lowered = stripped.lower()
            if not stripped:
                continue
            if lowered.startswith(("would you like", "what would you like next", "next steps", "which would you like")):
                return idx
            if re.match(r"^[A-Z]\)\s", stripped):
                return idx
            if lowered.startswith(("reply with", "please pick", "choose one")):
                return idx
        return None

    def _trim_menu_heavy_followup(self, draft: str, user_input: str) -> tuple[str, bool]:
        if not draft or self._last_observation_indicates_blocked() or self._user_requested_options(user_input):
            return draft, False

        cutoff = self._find_followup_cutoff(draft)
        if cutoff is None:
            return draft, False

        lines = draft.splitlines()
        trimmed = "\n".join(lines[:cutoff]).rstrip()
        if not trimmed:
            return draft, False
        return trimmed, True

    def _extract_consensus_text(self, response: str) -> str:
        match = re.search(r"<consensus>(.*?)</consensus>", response, re.S)
        return match.group(1).strip() if match else ""

    def _trim_finalize_followup(self, draft: str) -> tuple[str, bool]:
        if not draft:
            return "", False
        cutoff = self._find_followup_cutoff(draft)
        if cutoff is None:
            return draft.strip(), False
        lines = draft.splitlines()
        trimmed = "\n".join(lines[:cutoff]).rstrip()
        if not trimmed:
            return draft.strip(), False
        return trimmed.strip(), trimmed.strip() != draft.strip()

    def _summarize_tool_results(self, tool_results: list[str], *, max_chars: int = 4000) -> str:
        sections: list[str] = []
        for index, result in enumerate(tool_results, start=1):
            payload = self._parse_tool_result_payload(result)
            if payload:
                tool_name = str(payload.get("tool", f"tool_{index}"))
                ok = bool(payload.get("ok", False))
                summary = str(payload.get("summary", "")).strip()
                text = self._tool_result_text(result)
                section = [f"Tool {index}: {tool_name}", f"ok={ok}"]
                if summary:
                    section.append(f"summary={summary}")
                if text:
                    section.append("output:")
                    section.append(text[:1200])
                sections.append("\n".join(section).strip())
            else:
                sections.append(f"Tool {index}:\n{str(result)[:1200]}")
        joined = "\n\n".join(section for section in sections if section).strip()
        return joined[:max_chars]

    def _tool_result_highlight(self, result: str, *, prefer_error: bool | None = None, max_chars: int = 700) -> str:
        payload = self._parse_tool_result_payload(result)
        if payload:
            data = payload.get("data") or {}
            errors = [str(item).strip() for item in payload.get("errors", []) if str(item).strip()]
            prefer_error = not bool(payload.get("ok", False)) if prefer_error is None else prefer_error
            candidates = [
                data.get("stderr"),
                "\n".join(errors),
                data.get("stdout"),
                data.get("output"),
                data.get("analysis"),
                payload.get("summary"),
            ] if prefer_error else [
                data.get("stdout"),
                data.get("output"),
                data.get("analysis"),
                payload.get("summary"),
                data.get("stderr"),
                "\n".join(errors),
            ]
            for candidate in candidates:
                if not isinstance(candidate, str):
                    continue
                text = candidate.strip()
                if not text:
                    continue
                lines = [line.rstrip() for line in text.splitlines() if line.strip()]
                condensed = "\n".join(lines[:6]).strip()
                if condensed:
                    return condensed[:max_chars]
            return ""

        raw = str(result or "").strip()
        if not raw:
            return ""
        lines = [line.rstrip() for line in raw.splitlines() if line.strip()]
        condensed = "\n".join(lines[:6]).strip()
        return condensed[:max_chars]

    def _build_action_turn_result(self, tool_results: list[str]) -> str:
        failed = False
        summaries: list[str] = []
        errors: list[str] = []
        for index, result in enumerate(tool_results, start=1):
            payload = self._parse_tool_result_payload(result)
            if payload:
                tool_name = str(payload.get("tool", f"tool_{index}"))
                summary = str(payload.get("summary", "")).strip()
                if summary:
                    summaries.append(f"{tool_name}: {summary}")
                if not bool(payload.get("ok", False)):
                    failed = True
                    payload_errors = [str(item).strip() for item in payload.get("errors", []) if str(item).strip()]
                    if payload_errors:
                        errors.extend(payload_errors[:3])
                    else:
                        detail = self._tool_result_highlight(result, prefer_error=True)
                        errors.append(f"{tool_name}: {detail or 'execution failed'}")
                continue

            if self._tool_result_failed(result):
                failed = True
                detail = self._tool_result_highlight(result, prefer_error=True)
                errors.append(detail or f"Tool {index} failed.")

        summary = "; ".join(summaries[:4]).strip()
        if not summary:
            summary = "Action turn completed." if not failed else "Action turn blocked."

        return self._structured_tool_result(
            "action_turn",
            not failed,
            summary=summary,
            errors=errors[:6],
            data={
                "tool_count": len(tool_results),
                "output": self._summarize_tool_results(tool_results, max_chars=3200),
            },
        )

    def _response_tool_payloads(self, response: str) -> list[tuple[str, str]]:
        payloads: list[tuple[str, str]] = []
        text = str(response or "")
        for raw in re.findall(r"<bash>(.*?)</bash>", text, re.S):
            payloads.append(("bash", self._normalize_tool_payload(raw)))
        for raw in re.findall(r"<python>(.*?)</python>", text, re.S):
            payloads.append(("python", self._normalize_tool_payload(raw)))
        return payloads

    def _inspection_only_turn(self, response: str, tool_results: list[str]) -> bool:
        payloads = self._response_tool_payloads(response)
        if not payloads or len(payloads) != len(tool_results):
            return False
        for index, result in enumerate(tool_results):
            payload = self._parse_tool_result_payload(result) or {}
            tool_name = str(payload.get("tool", payloads[index][0]) or payloads[index][0]).strip() or payloads[index][0]
            payload_tool, raw_payload = payloads[index]
            effective_tool = payload_tool if tool_name in {"bash", "python"} else tool_name
            if effective_tool in {"bash", "python"}:
                if self.execution_policy._mutating_payload(effective_tool, raw_payload):
                    return False
                if not self.execution_policy._inspection_like_payload(effective_tool, raw_payload):
                    return False
                continue
            if effective_tool in {
                "inspect_python_environment",
                "list_python_packages",
                "python_symbol_doc",
                "python_import_graph",
                "list_windows",
                "list_windows_advanced",
                "get_active_terminal",
                "list_processes",
                "get_software_versions",
                "project_memory",
                "task_memory",
                "failure_memory",
                "recall",
                "search_memory",
                "read_bg_task_log",
                "get_bg_task_details",
                "check_bg_tasks",
            }:
                continue
            return False
        return True

    def _normalize_inspection_guidance(self, reviewer_guidance: dict[str, Any] | None,
                                       verification: dict[str, Any], tool_results: list[str]) -> dict[str, Any]:
        guidance = copy.deepcopy(reviewer_guidance or {})
        if any(self._tool_result_failed(result) for result in tool_results):
            return guidance
        if not verification.get("success", False):
            return guidance
        guidance["severity"] = "healthy"
        guidance["confidence"] = "high"
        guidance["verification_level"] = "light"
        guidance["require_stronger_verification"] = False
        guidance["redirect_to_inspection"] = False
        guidance["mark_goal_blocked"] = False
        guidance["blocked_reason"] = ""
        return guidance

    def _action_turn_fallback(self, response: str, tool_results: list[str],
                              verification: dict[str, Any], reviewer_review: str,
                              reviewer_guidance: dict[str, Any] | None = None,
                              stronger_verification: dict[str, Any] | None = None) -> str:
        guidance = reviewer_guidance or {}
        stronger = stronger_verification or {}
        blocked = (
            any(self._tool_result_failed(result) for result in tool_results)
            or not verification.get("success", False)
            or bool(stronger.get("required") and not stronger.get("verified", False))
            or guidance.get("severity") == "blocked"
        )
        if blocked:
            detail = str(stronger.get("reason") or "").strip()
            if not detail:
                failed_result = next((result for result in tool_results if self._tool_result_failed(result)), tool_results[-1] if tool_results else "")
                detail = self._tool_result_highlight(failed_result, prefer_error=True)
            if not detail:
                detail = "; ".join(str(item).strip() for item in verification.get("errors", []) if str(item).strip())
            if not detail:
                detail = str(verification.get("summary", "")).replace("Verification FAILED:", "").strip()
            if not detail:
                detail = str(guidance.get("blocked_reason") or "").strip()
            if not detail and reviewer_review:
                detail = reviewer_review.strip()
            message = f"Blocked: {detail or 'One or more tool actions failed.'}".strip()
        else:
            success_result = next((result for result in reversed(tool_results) if not self._tool_result_failed(result)), tool_results[-1] if tool_results else "")
            detail = self._tool_result_highlight(success_result, prefer_error=False)
            if not detail:
                detail = str(verification.get("summary", "")).replace("Verification OK:", "").strip()
            if not detail:
                detail = self._extract_consensus_text(response)
            message = f"Completed: {detail or 'Tool actions completed successfully.'}".strip()
        finalized, _ = self._trim_finalize_followup(message)
        return finalized or message

    def _finalize_action_turn(self, response: str, user_input: str, tool_results: list[str]) -> tuple[str, dict[str, Any]]:
        self._update_runtime_heartbeat(current_mode="interactive", current_phase="verify", persist=True)
        aggregated_result = self._build_action_turn_result(tool_results)
        verification = self.verify_and_report(aggregated_result, context="action_turn")
        reviewer_review = self._run_reviewer_pass("tools", user_input, aggregated_result, verification=verification)
        reviewer_guidance = self._reviewer_guidance_from_text(reviewer_review)
        inspection_only = self._inspection_only_turn(response, tool_results)
        if inspection_only:
            reviewer_guidance = self._normalize_inspection_guidance(reviewer_guidance, verification, tool_results)
        stronger_verification = {
            "required": False,
            "verified": bool(verification.get("success", False)),
            "confidence": reviewer_guidance.get("confidence", "medium"),
            "reason": "",
            "evidence": [],
            "next_step": reviewer_guidance.get("next_step", ""),
            "review": reviewer_review,
        }
        if reviewer_guidance.get("require_stronger_verification") and not inspection_only:
            runner = getattr(self, "_run_stronger_verification", None)
            if callable(runner):
                stronger_verification = runner(user_input, tool_results, verification, reviewer_guidance)
            else:
                stronger_verification = {
                    **stronger_verification,
                    "required": True,
                    "verified": False,
                    "reason": reviewer_guidance.get("blocked_reason") or reviewer_review.strip(),
                }

        blocked = (
            any(self._tool_result_failed(result) for result in tool_results)
            or not verification.get("success", False)
            or bool(stronger_verification.get("required") and not stronger_verification.get("verified", False))
            or reviewer_guidance.get("severity") == "blocked"
        )
        target_prefix = "Blocked:" if blocked else "Completed:"
        merged_guidance = copy.deepcopy(reviewer_guidance)
        if stronger_verification.get("required") and not stronger_verification.get("verified", False):
            merged_guidance["mark_goal_blocked"] = True
            merged_guidance["redirect_to_inspection"] = merged_guidance.get("redirect_to_inspection") or str(stronger_verification.get("next_step", "")).strip().lower().startswith("inspect")
            if stronger_verification.get("reason"):
                merged_guidance["blocked_reason"] = str(stronger_verification.get("reason"))
        goal_update = self._apply_reviewer_goal_guidance(merged_guidance, stronger_verification)
        policy_feedback = self._update_execution_policy_feedback(merged_guidance, stronger_verification)

        fallback = self._action_turn_fallback(
            response,
            tool_results,
            verification,
            reviewer_review,
            reviewer_guidance=merged_guidance,
            stronger_verification=stronger_verification,
        )
        finalized = fallback
        used_llm = False
        trimmed_menu = False
        self._update_runtime_heartbeat(current_mode="interactive", current_phase="finalize", persist=True)

        result_summary = self._summarize_tool_results(tool_results)
        if result_summary:
            messages = [
                {
                    "role": "system",
                    "content": (
                        "You are the mandatory post-tool finalizer for an agent runtime. "
                        "Tools have already run. Use only the actual execution results below. "
                        "Return exactly one short plain-text message that starts with 'Completed:' or 'Blocked:'. "
                        "Mention the most important stdout or stderr detail. Do not speculate. "
                        "Do not include menus, choices, headings, or next-step lists."
                    ),
                },
                {
                    "role": "user",
                    "content": (
                        f"User request:\n{user_input[:1200]}\n\n"
                        f"Model draft before finalize:\n{self._extract_consensus_text(response)[:1200] or '(none)'}\n\n"
                        f"Verification:\n{json.dumps(verification, ensure_ascii=False)[:1500]}\n\n"
                        f"Reviewer:\n{reviewer_review[:1200] or '(none)'}\n\n"
                        f"Reviewer guidance:\n{json.dumps(merged_guidance, ensure_ascii=False)[:1500]}\n\n"
                        f"Stronger verification:\n{json.dumps(stronger_verification, ensure_ascii=False)[:1500]}\n\n"
                        f"Actual tool results:\n{result_summary}\n\n"
                        f"Write exactly one message starting with '{target_prefix}'. "
                        "If blocked, name the blocker concretely. If completed, state what actually happened."
                    ),
                },
            ]
            try:
                resp = self.client.chat(messages, temperature=0.1)
                candidate = resp["choices"][0]["message"]["content"].strip()
                if candidate:
                    finalized = candidate
                    used_llm = True
            except Exception as e:
                self._append_response_trace(
                    "action_turn_finalize_failed",
                    original=response,
                    user_input=user_input,
                    error=str(e),
                )

        finalized, trimmed_menu = self._trim_finalize_followup(finalized)
        if finalized and not re.match(r'^(Completed|Blocked):', finalized):
            cleaned = finalized.lstrip('-: ').strip()
            finalized = f"{target_prefix} {cleaned}".strip()
        if not finalized:
            finalized = fallback

        if blocked:
            self._note_runtime_error(finalized, current_phase="blocked", persist=True)
        else:
            self._note_runtime_success(finalized, current_phase="completed", persist=True)

        return finalized, {
            "blocked": blocked,
            "used_llm": used_llm,
            "trimmed_menu": trimmed_menu,
            "verification": verification,
            "review": reviewer_review,
            "reviewer_guidance": merged_guidance,
            "stronger_verification": stronger_verification,
            "policy_feedback": policy_feedback,
            "confidence": stronger_verification.get("confidence") or reviewer_guidance.get("confidence", "medium"),
            "redirect_to_inspection": bool(merged_guidance.get("redirect_to_inspection")),
            "goal_update": goal_update,
            "inspection_only": inspection_only,
        }

    def _mixed_consensus_fallback(self, response: str, tool_results: list[str]) -> str:
        verification = {"success": not any(self._tool_result_failed(result) for result in tool_results), "summary": "", "errors": []}
        return self._action_turn_fallback(response, tool_results, verification, "")

    def _finalize_mixed_consensus(self, response: str, user_input: str, tool_results: list[str]) -> tuple[str, bool]:
        if not tool_results or any(self._tool_result_failed(result) for result in tool_results):
            return "", False

        finalized, details = self._finalize_action_turn(response, user_input, tool_results)
        return finalized, bool(details.get("used_llm") or details.get("trimmed_menu"))

    def _accept_mixed_consensus(self, response: str, user_input: str, *, turn_num: int,
                                turn_start: float, turn_start_data: dict[str, Any],
                                tool_results: list[str]) -> str | None:
        if not tool_results or any(self._tool_result_failed(result) for result in tool_results):
            return None

        draft, enriched = self._finalize_mixed_consensus(response, user_input, tool_results)
        if not draft:
            return None

        self.state.log_event("assistant", draft)
        self._append_response_trace(
            "mixed_consensus_accepted",
            original=response,
            accepted=draft,
            user_input=user_input,
            enriched=enriched,
        )
        dur = time.time() - turn_start
        meta = ["consensus", "mixed_consensus"]
        if enriched:
            meta.append("mixed_consensus_enriched")
        self.logger.log_turn(
            turn_num,
            response,
            self.state.calculate_diff(turn_start_data, self.state.data),
            ["consensus", f"tools:{len(tool_results)}"],
            duration=dur,
            meta=meta,
        )
        return f"\n{Colors.CYAN}{Colors.BOLD}💡 Answer:{Colors.ENDC}\n{draft}"

    def _should_return_after_action_turn(self, pending_consensus: str, finalize_meta: dict[str, Any]) -> bool:
        if str(pending_consensus or "").strip():
            return not bool(finalize_meta.get("blocked"))
        if finalize_meta.get("strategy_shift"):
            return True
        return False

    def _build_internal_action_continuation(self, finalized: str, finalize_meta: dict[str, Any]) -> str:
        blocked = bool(finalize_meta.get("blocked"))
        guidance = finalize_meta.get("reviewer_guidance") if isinstance(finalize_meta.get("reviewer_guidance"), dict) else {}
        next_step = str(guidance.get("next_step", "") or "").strip()
        if blocked:
            detail = finalized.strip() or "Blocked action turn."
            suffix = f" Next step hint: {next_step}" if next_step else ""
            return (
                f"Internal Continuation: {detail}{suffix} "
                "Continue working internally if the blocker can be resolved from the workspace or tool output. "
                "Use <consensus> only if you need user input or a decision."
            ).strip()
        return (
            "Internal Continuation: The last action turn made progress but is not yet a user-facing final answer. "
            "Continue with the next concrete step. Use <consensus> only when the task is complete or when you need user input."
        )

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
            "heartbeat": self.runtime_heartbeat(),
            "metrics": {
                "total_tokens": self.state.total_tokens,
                "snapshots": len(list(self.state.snapshot_dir.glob("*.db"))),
                "threads": threading.active_count(),
                "background_tasks": len(self.state.active_processes),
            },
            "subagents": self.subagent_manager.get_load_stats(),
            "memory_keys": list(self.state.structured_memory.keys()),
            "background_task_ids": sorted(self.state.active_processes.keys()),
            "background_task_summaries": [self._normalize_bg_task_record(pid, info) for pid, info in sorted(self.state.active_processes.items())],
            "reviewer_event_count": len(self.state.list_records(REVIEWER_EVENT_KEY)),
            "goal_count": len(self.state.goal_records()),
            "active_goals": [goal for goal in self.state.goal_records() if goal.get("status") in {GOAL_STATUS_ACTIVE, GOAL_STATUS_PENDING}],
            "execution_policy": self.execution_policy.describe(),
        }


    def _structured_tool_result(self, tool: str, ok: bool, *, summary: str = "", data: dict[str, Any] | None = None,
                                errors: list[str] | None = None, warnings: list[str] | None = None) -> str:
        payload = {
            "ok": bool(ok),
            "tool": tool,
            "summary": summary,
            "data": data or {},
            "errors": list(errors or []),
            "warnings": list(warnings or []),
        }
        return json.dumps(payload, indent=2)

    def _parse_tool_result_payload(self, result: str) -> dict[str, Any] | None:
        if not isinstance(result, str):
            return None
        try:
            parsed = json.loads(result)
            if isinstance(parsed, dict) and parsed.get("tool"):
                return parsed
        except Exception:
            return None
        return None

    def _tool_result_text(self, result: str) -> str:
        payload = self._parse_tool_result_payload(result)
        if not payload:
            return result or ""
        data = payload.get("data") or {}
        parts = []
        if isinstance(data.get("stdout"), str) and data.get("stdout"):
            parts.append(data.get("stdout"))
        if isinstance(data.get("stderr"), str) and data.get("stderr"):
            parts.append(data.get("stderr"))
        if isinstance(data.get("output"), str) and data.get("output"):
            parts.append(data.get("output"))
        if isinstance(data.get("analysis"), str) and data.get("analysis"):
            parts.append(data.get("analysis"))
        if isinstance(payload.get("summary"), str) and payload.get("summary"):
            parts.append(payload.get("summary"))
        if isinstance(payload.get("errors"), list) and payload.get("errors"):
            parts.extend(str(item) for item in payload.get("errors") if item)
        return "\n".join(part for part in parts if part).strip()

    def _store_reviewer_event(self, subject: str, request_text: str, result_text: str,
                              verification: dict[str, Any] | None, review: str,
                              guidance: dict[str, Any] | None = None):
        event = {
            "id": str(uuid.uuid4()),
            "timestamp": datetime.now().isoformat(),
            "subject": subject,
            "request": (request_text or "")[:500],
            "result": self._tool_result_text(result_text)[:1000],
            "verification": verification or {},
            "review": review,
            "guidance": copy.deepcopy(guidance or {}),
        }
        self.state.append_record(REVIEWER_EVENT_KEY, event, limit=200)

    def _coerce_goal_evidence(self, evidence: Any) -> list[str]:
        if evidence is None:
            return []
        if isinstance(evidence, str):
            item = evidence.strip()
            return [item] if item else []
        if isinstance(evidence, (list, tuple, set)):
            return [str(item).strip() for item in evidence if str(item).strip()]
        item = str(evidence).strip()
        return [item] if item else []

    def _normalize_goal_record(self, goal_record: dict[str, Any]) -> dict[str, Any]:
        if not isinstance(goal_record, dict):
            raise TypeError("Goal record must be a dictionary.")
        now = datetime.now().isoformat()
        text = str(goal_record.get("text", "") or "").strip()
        status = str(goal_record.get("status", GOAL_STATUS_PENDING) or GOAL_STATUS_PENDING).strip() or GOAL_STATUS_PENDING
        completed_at = str(goal_record.get("completed_at", "") or "").strip()
        if status in {GOAL_STATUS_COMPLETED, GOAL_STATUS_CANCELLED, GOAL_STATUS_FAILED} and not completed_at:
            completed_at = now
        if status in {GOAL_STATUS_PENDING, GOAL_STATUS_ACTIVE}:
            completed_at = ""
        normalized = {
            "id": str(goal_record.get("id", "") or str(uuid.uuid4())[:8]).strip(),
            "text": text,
            "status": status,
            "priority": int(goal_record.get("priority", 2) or 2),
            "created_at": str(goal_record.get("created_at", "") or now),
            "updated_at": str(goal_record.get("updated_at", "") or now),
            "completed_at": completed_at,
            "done_when": str(goal_record.get("done_when", "") or "").strip(),
            "blocked_reason": str(goal_record.get("blocked_reason", "") or "").strip(),
            "evidence": self._coerce_goal_evidence(goal_record.get("evidence", [])),
            "parent_goal_id": str(goal_record.get("parent_goal_id", "") or "").strip(),
            "next_action": str(goal_record.get("next_action", "") or text).strip(),
            "verification_target": str(goal_record.get("verification_target", "") or "").strip(),
            "workspace_path": str(goal_record.get("workspace_path", "") or str(Path.cwd())).strip(),
        }
        if not normalized["next_action"]:
            normalized["next_action"] = normalized["text"]
        return normalized

    def _goal_sort_key(self, goal: dict[str, Any]) -> tuple[int, int, str]:
        status_rank = 0 if goal.get("status") == GOAL_STATUS_ACTIVE else 1
        return (status_rank, int(goal.get("priority", 2)), str(goal.get("created_at", "")))

    def _goal_record(self, text: str, *, status: str = GOAL_STATUS_PENDING, priority: int = 2,
                     done_when: str = "", blocked_reason: str = "", evidence: Any = None,
                     parent_goal_id: str = "", next_action: str = "", verification_target: str = "",
                     workspace_path: str = "") -> dict[str, Any]:
        now = datetime.now().isoformat()
        return self._normalize_goal_record({
            "id": str(uuid.uuid4())[:8],
            "text": text.strip(),
            "status": status,
            "priority": int(priority),
            "created_at": now,
            "updated_at": now,
            "completed_at": "",
            "done_when": done_when,
            "blocked_reason": blocked_reason,
            "evidence": evidence,
            "parent_goal_id": parent_goal_id,
            "next_action": next_action,
            "verification_target": verification_target,
            "workspace_path": workspace_path,
        })

    def add_goal(self, text: str, *, priority: int = 2, status: str = GOAL_STATUS_PENDING,
                 done_when: str = "", blocked_reason: str = "", evidence: Any = None,
                 parent_goal_id: str = "", next_action: str = "", verification_target: str = "",
                 workspace_path: str = "") -> dict[str, Any]:
        goal = self._goal_record(
            text,
            status=status,
            priority=priority,
            done_when=done_when,
            blocked_reason=blocked_reason,
            evidence=evidence,
            parent_goal_id=parent_goal_id,
            next_action=next_action,
            verification_target=verification_target,
            workspace_path=workspace_path,
        )
        self.state.upsert_goal(goal)
        self.state.append_history(
            "system",
            f"Goal added: {goal['id']} status={goal['status']} next_action={goal['next_action']} text={goal['text']}",
            tags=["goal"],
        )
        return goal

    def update_goal(self, goal_id: str, *, status: str | None = None, text: str | None = None,
                    priority: int | None = None, done_when: str | None = None,
                    blocked_reason: str | None = None, evidence: Any = None,
                    parent_goal_id: str | None = None, next_action: str | None = None,
                    verification_target: str | None = None, workspace_path: str | None = None) -> dict[str, Any] | None:
        goal_id = str(goal_id).strip()
        for goal in self.state.goal_records():
            if str(goal.get("id", "")) != goal_id:
                continue
            updated = self._normalize_goal_record(goal)
            if status is not None:
                updated["status"] = status
                if status in {GOAL_STATUS_COMPLETED, GOAL_STATUS_CANCELLED, GOAL_STATUS_FAILED}:
                    updated["completed_at"] = datetime.now().isoformat()
                else:
                    updated["completed_at"] = ""
            if text is not None:
                updated["text"] = text.strip()
            if priority is not None:
                updated["priority"] = int(priority)
            if done_when is not None:
                updated["done_when"] = done_when.strip()
            if blocked_reason is not None:
                updated["blocked_reason"] = blocked_reason.strip()
            if evidence is not None:
                updated["evidence"] = self._coerce_goal_evidence(evidence)
            if parent_goal_id is not None:
                updated["parent_goal_id"] = parent_goal_id.strip()
            if next_action is not None:
                updated["next_action"] = next_action.strip()
            if verification_target is not None:
                updated["verification_target"] = verification_target.strip()
            if workspace_path is not None:
                updated["workspace_path"] = workspace_path.strip()
            updated["updated_at"] = datetime.now().isoformat()
            updated = self._normalize_goal_record(updated)
            self.state.upsert_goal(updated)
            self.state.append_history(
                "system",
                f"Goal updated: {updated['id']} status={updated['status']} next_action={updated['next_action']} text={updated['text']}",
                tags=["goal"],
            )
            return updated
        return None

    def active_goals(self) -> list[dict[str, Any]]:
        goals = [self._normalize_goal_record(goal) for goal in self.state.goal_records() if goal.get("status") in {GOAL_STATUS_PENDING, GOAL_STATUS_ACTIVE}]
        return sorted(goals, key=self._goal_sort_key)

    def current_goal(self) -> dict[str, Any] | None:
        goals = self.active_goals()
        return goals[0] if goals else None

    def _render_current_goal_focus(self, goal: dict[str, Any] | None) -> str:
        if not goal:
            return ""
        lines = [
            "CURRENT EXECUTION TARGET:",
            f"   - Goal: [{goal.get('id')}] {goal.get('text')}",
            f"   - Status/Priority: {goal.get('status')} / {goal.get('priority')}",
            f"   - Next Action: {goal.get('next_action') or goal.get('text')}",
        ]
        if goal.get("done_when"):
            lines.append(f"   - Done When: {goal.get('done_when')}")
        if goal.get("verification_target"):
            lines.append(f"   - Verification Target: {goal.get('verification_target')}")
        if goal.get("workspace_path"):
            lines.append(f"   - Workspace Path: {goal.get('workspace_path')}")
        if goal.get("blocked_reason"):
            lines.append(f"   - Blocked Reason: {goal.get('blocked_reason')}")
        if goal.get("parent_goal_id"):
            lines.append(f"   - Parent Goal: {goal.get('parent_goal_id')}")
        evidence = goal.get("evidence") or []
        if evidence:
            lines.append(f"   - Evidence: {', '.join(str(item) for item in evidence[:3])}")
        return "\n" + "\n".join(lines)

    def render_goal_summary(self) -> str:
        goals = self.state.goal_records()
        if not goals:
            return "No persisted goals."
        lines = []
        for goal in sorted((self._normalize_goal_record(item) for item in goals), key=lambda item: (item.get("status", ""), int(item.get("priority", 2)), item.get("created_at", ""))):
            summary = (
                f"[{goal.get('id')}] status={goal.get('status')} priority={goal.get('priority')} "
                f"next_action={goal.get('next_action')} text={goal.get('text')}"
            )
            if goal.get("done_when"):
                summary += f" done_when={goal.get('done_when')}"
            if goal.get("verification_target"):
                summary += f" verification_target={goal.get('verification_target')}"
            if goal.get("workspace_path"):
                summary += f" workspace_path={goal.get('workspace_path')}"
            if goal.get("blocked_reason"):
                summary += f" blocked_reason={goal.get('blocked_reason')}"
            lines.append(summary)
        return "\n".join(lines)

    def render_reviewer_summary(self, limit: int = 10) -> str:
        events = self.state.list_records(REVIEWER_EVENT_KEY)[-max(1, int(limit)):]
        if not events:
            return "No reviewer events recorded."
        lines = []
        for event in events:
            if not isinstance(event, dict):
                continue
            guidance = event.get("guidance", {}) if isinstance(event.get("guidance"), dict) else {}
            summary = f"[{event.get('timestamp', '')}] {event.get('subject', '')}"
            if guidance:
                summary += f" severity={guidance.get('severity', '')} confidence={guidance.get('confidence', '')}"
            summary += f": {str(event.get('review', ''))[:300]}"
            lines.append(summary)
        return "\n".join(lines) if lines else "No reviewer events recorded."

    def render_history_summary(self, limit: int = 10) -> str:
        entries = self.state.query_history(limit=max(1, int(limit)))
        if not entries:
            return "No history entries."
        return "\n".join(
            f"[{datetime.fromtimestamp(entry.get('timestamp', 0)).isoformat() if entry.get('timestamp') else ''}] {entry.get('role', '')}: {str(entry.get('content', ''))[:300]}"
            for entry in entries
        )

    def render_health_summary(self) -> str:
        status = self.get_runtime_status()
        metrics = status.get("metrics", {})
        return "\n".join([
            f"status={status.get('status')}",
            f"total_tokens={metrics.get('total_tokens')}",
            f"threads={metrics.get('threads')}",
            f"background_tasks={metrics.get('background_tasks')}",
            f"goals={status.get('goal_count')}",
            f"reviewer_events={status.get('reviewer_event_count')}",
        ])

    def handle_operator_command(self, raw_command: str) -> str:
        command = (raw_command or "").strip()
        if not command:
            return ""
        parts = command.split()
        head = parts[0].lower()

        if head == "/health":
            return self.render_health_summary()
        if head == "/history":
            limit = 10
            if len(parts) > 1:
                try:
                    limit = max(1, min(100, int(parts[1])))
                except ValueError:
                    return "Usage: /history [limit]"
            return self.render_history_summary(limit=limit)
        if head == "/reviews":
            limit = 10
            if len(parts) > 1:
                try:
                    limit = max(1, min(100, int(parts[1])))
                except ValueError:
                    return "Usage: /reviews [limit]"
            return self.render_reviewer_summary(limit=limit)
        if head == "/goals":
            return self.render_goal_summary()
        if head == "/goal":
            if len(parts) < 2:
                return "Usage: /goal add <text> | /goal start <id> | /goal done <id> | /goal cancel <id> | /goal fail <id>"
            action = parts[1].lower()
            if action == "add":
                goal_text = command.partition(" add ")[2].strip() if " add " in command else ""
                if not goal_text:
                    return "Usage: /goal add <text>"
                goal = self.add_goal(goal_text)
                return f"Added goal [{goal['id']}] priority={goal['priority']} status={goal['status']} text={goal['text']}"
            if len(parts) < 3:
                return f"Usage: /goal {action} <id>"
            goal_id = parts[2]
            status_map = {
                "start": GOAL_STATUS_ACTIVE,
                "done": GOAL_STATUS_COMPLETED,
                "cancel": GOAL_STATUS_CANCELLED,
                "fail": GOAL_STATUS_FAILED,
            }
            if action not in status_map:
                return "Usage: /goal add <text> | /goal start <id> | /goal done <id> | /goal cancel <id> | /goal fail <id>"
            updated = self.update_goal(goal_id, status=status_map[action])
            if not updated:
                return f"No goal found for id {goal_id}."
            return f"Updated goal [{updated['id']}] status={updated['status']} text={updated['text']}"
        if head == "/help":
            return "\n".join([
                "/health",
                "/history [limit]",
                "/reviews [limit]",
                "/goals",
                "/goal add <text>",
                "/goal start <id>",
                "/goal done <id>",
                "/goal cancel <id>",
                "/goal fail <id>",
                "exit | quit",
            ])
        return f"Unknown operator command: {command}"

    def verify_and_report(self, result: str, context: str = "") -> Dict[str, Any]:
        """Run lightweight verification on textual tool output. Returns a summary dict and logs results.
        Looks for "Traceback", 'Error', 'FAILED', '✗', or other failure markers."""
        if not context:
            goal = self.current_goal()
            if goal and goal.get("verification_target"):
                context = str(goal.get("verification_target") or "").strip()
        try:
            payload = self._parse_tool_result_payload(result)
            errors = []
            success = True
            payload_errors = payload.get("errors", []) if payload else []
            r = self._tool_result_text(result).strip()
            errors = []

            if payload and not payload.get("ok", True):
                success = False
                errors.extend(str(item) for item in payload_errors if item)

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

    def _reviewer_pass_allowed(self, subject: str) -> bool:
        if not self.reviewer_pass_enabled:
            return False
        if subject == "tests":
            return self.reviewer_pass_after_tests
        return self.reviewer_pass_after_tools

    def _reviewer_guidance_from_text(self, review: str) -> dict[str, Any]:
        guidance: dict[str, Any] = {
            "severity": "healthy",
            "confidence": "medium",
            "verification_level": "normal",
            "next_step": "",
            "require_stronger_verification": False,
            "redirect_to_inspection": False,
            "mark_goal_blocked": False,
            "blocked_reason": "",
        }
        text = str(review or "")
        if not text.strip():
            return guidance

        for raw_line in text.splitlines():
            line = raw_line.strip()
            if not line or ":" not in line:
                continue
            label, value = line.split(":", 1)
            key = label.strip().lower()
            payload = value.strip()
            lowered = payload.lower()
            if key == "assessment":
                if "blocked" in lowered:
                    guidance["severity"] = "blocked"
                elif "risk" in lowered or "uncertain" in lowered:
                    guidance["severity"] = "risky"
                elif "healthy" in lowered or "ok" in lowered:
                    guidance["severity"] = "healthy"
                guidance["blocked_reason"] = payload
            elif key == "confidence":
                if "low" in lowered:
                    guidance["confidence"] = "low"
                elif "high" in lowered:
                    guidance["confidence"] = "high"
                else:
                    guidance["confidence"] = "medium"
            elif key == "verification":
                if "strong" in lowered:
                    guidance["verification_level"] = "strong"
                elif "light" in lowered or "weak" in lowered:
                    guidance["verification_level"] = "light"
                else:
                    guidance["verification_level"] = payload or "normal"
            elif key == "next step":
                guidance["next_step"] = payload
                if "inspect" in lowered or "evidence" in lowered or "confirm" in lowered:
                    guidance["redirect_to_inspection"] = True

        guidance["require_stronger_verification"] = (
            guidance["severity"] in {"risky", "blocked"}
            or guidance["confidence"] == "low"
            or guidance["verification_level"] == "strong"
        )
        if guidance["severity"] == "blocked":
            guidance["mark_goal_blocked"] = True
            if not guidance["blocked_reason"]:
                guidance["blocked_reason"] = text.strip()
        return guidance

    def _apply_reviewer_goal_guidance(self, reviewer_guidance: dict[str, Any], stronger_verification: dict[str, Any] | None = None) -> dict[str, Any] | None:
        goal = self.current_goal()
        if not goal:
            return None

        guidance = copy.deepcopy(reviewer_guidance or {})
        stronger = copy.deepcopy(stronger_verification or {})
        updated = copy.deepcopy(goal)
        blocked_reason = str(guidance.get("blocked_reason") or stronger.get("reason") or "").strip()
        next_step = str(guidance.get("next_step") or stronger.get("next_step") or "").strip()

        if guidance.get("mark_goal_blocked") or (stronger.get("required") and not stronger.get("verified", False)):
            updated["status"] = GOAL_STATUS_FAILED
            updated["blocked_reason"] = blocked_reason or updated.get("blocked_reason", "")
        elif blocked_reason and not updated.get("blocked_reason"):
            updated["blocked_reason"] = blocked_reason

        if next_step:
            updated["next_action"] = next_step
        updated["updated_at"] = datetime.now().isoformat()
        self.state.upsert_goal(updated)
        return updated

    def _update_execution_policy_feedback(self, reviewer_guidance: dict[str, Any] | None = None,
                                          stronger_verification: dict[str, Any] | None = None) -> dict[str, Any]:
        guidance = copy.deepcopy(reviewer_guidance or {})
        stronger = copy.deepcopy(stronger_verification or {})
        target = self._scoped_verification_target()
        feedback = {
            "severity": str(guidance.get("severity", "healthy") or "healthy"),
            "confidence": str(stronger.get("confidence") or guidance.get("confidence", "medium") or "medium"),
            "require_stronger_verification": bool(guidance.get("require_stronger_verification") or stronger.get("required", False)),
            "redirect_to_inspection": bool(guidance.get("redirect_to_inspection")),
            "blocked_reason": str(guidance.get("blocked_reason") or stronger.get("reason") or "").strip(),
            "next_step": str(guidance.get("next_step") or stronger.get("next_step") or "").strip(),
            "verification_target": target,
            "updated_at": datetime.now().isoformat(),
        }
        if (
            feedback["severity"] == "healthy"
            and feedback["confidence"] == "high"
            and not feedback["require_stronger_verification"]
            and not feedback["redirect_to_inspection"]
        ):
            self.execution_policy.clear_runtime_feedback()
            return {}
        self.execution_policy.set_runtime_feedback(feedback)
        return feedback

    def _run_stronger_verification(self, user_input: str, tool_results: list[str], verification: dict[str, Any],
                                   reviewer_guidance: dict[str, Any]) -> dict[str, Any]:
        target = self._scoped_verification_target()
        next_step = str(reviewer_guidance.get("next_step", "") or "").strip()
        if not target:
            return {
                "required": True,
                "verified": False,
                "confidence": "low",
                "reason": "Reviewer requested stronger verification, but no scoped verification target is defined.",
                "evidence": [],
                "next_step": next_step or "Inspect the active goal, add a verification_target, and rerun verification.",
                "target": "",
                "review": "",
            }

        target_text = str(target or "").strip()
        target_path = Path(target_text.strip('"'))
        if "pytest" in target_text.lower() or "unittest" in target_text.lower() or "npm test" in target_text.lower() or " -m " in target_text or "::" in target_text:
            verification_result = self.tool_run_tests(target_text)
        elif target_path.exists() and target_path.suffix.lower() == ".py":
            verification_result = self.tool_run_verification(target_script=str(target_path))
        elif target_path.exists():
            verification_result = self.tool_run_tests(f'"{sys.executable}" -m pytest -q "{target_path}"')
        else:
            verification_result = self.run_bash(target_text)

        verification_summary = self.verify_and_report(verification_result, context=f"strong:{target_text}")
        verified = bool(verification_summary.get("success", False)) and not self._tool_result_failed(verification_result)
        evidence: list[str] = []
        highlight = self._tool_result_highlight(verification_result, prefer_error=not verified)
        if highlight:
            evidence.append(highlight)
        if verification_summary.get("summary"):
            evidence.append(str(verification_summary.get("summary")))
        return {
            "required": True,
            "verified": verified,
            "confidence": "high" if verified else str(reviewer_guidance.get("confidence", "low") or "low"),
            "reason": "" if verified else "; ".join(str(item).strip() for item in verification_summary.get("errors", []) if str(item).strip()) or str(verification_summary.get("summary", "") or "").strip(),
            "evidence": evidence[:4],
            "next_step": "" if verified else (next_step or f"Inspect why scoped verification failed for {target_text}."),
            "target": target_text,
            "review": verification_result,
        }

    def _run_reviewer_pass(self, subject: str, request_text: str, result_text: str,
                           verification: dict[str, Any] | None = None) -> str:
        if not self._reviewer_pass_allowed(subject):
            return ""

        truncated_request = (request_text or "")[:1500]
        truncated_result = (result_text or "")[:4000]
        verification_text = json.dumps(verification or {}, ensure_ascii=False)[:1500]
        messages = [
            {
                "role": "system",
                "content": (
                    "You are a concise runtime reviewer. Assess the execution result and decide whether it is healthy, risky, or blocked. "
                    "Return exactly four lines labeled Assessment, Confidence, Verification, and Next step."
                ),
            },
            {
                "role": "user",
                "content": (
                    f"Subject: {subject}\n"
                    f"Request:\n{truncated_request}\n\n"
                    f"Result:\n{truncated_result}\n\n"
                    f"Verification:\n{verification_text}\n\n"
                    "Format exactly as:\n"
                    "Assessment: <healthy|risky|blocked> - <short reason>\n"
                    "Confidence: <high|medium|low>\n"
                    "Verification: <light|normal|strong>\n"
                    "Next step: <short action>"
                ),
            },
        ]

        try:
            resp_data = self.client.chat(messages)
            review = resp_data["choices"][0]["message"]["content"].strip()
            if review:
                guidance = self._reviewer_guidance_from_text(review)
                self._store_reviewer_event(subject, request_text, result_text, verification, review, guidance=guidance)
                self._append_response_trace(
                    "reviewer_pass",
                    subject=subject,
                    request=request_text[:500],
                    result=self._tool_result_text(result_text)[:1000],
                    verification=verification or {},
                    review=review,
                    guidance=guidance,
                )
            return review
        except Exception as e:
            ErrorHandler.log(e, context=f"reviewer_pass:{subject}")
            return ""

    def _append_reviewer_summary(self, result: str, subject: str, request_text: str,
                                 verification: dict[str, Any] | None = None) -> str:
        self._run_reviewer_pass(subject, request_text, result, verification=verification)
        return result

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
            except Exception as e:
                ErrorHandler.log(
                    e,
                    severity=ErrorSeverity.RECOVERABLE,
                    context=f"_run_tool_hook:{tool_name}:{skill.metadata().name}",
                    code=ErrorCode.AGT_ERROR,
                )

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

    @ErrorHandler.handle(severity=ErrorSeverity.CRITICAL, code=ErrorCode.EXEC_ERROR)
    def run_bash(self, cmd: str) -> str:
        """Run a shell command with smart platform translations and flexible executor selection.
        Returns a string containing STDOUT and STDERR."""
        if not cmd or not cmd.strip():
            result = self._structured_tool_result("bash", False, summary="No command provided.", errors=["No command provided."])
            self._note_runtime_error("bash: no command provided", current_phase="blocked", persist=True)
            return result

        self._note_tool_start("bash", cmd, persist=True)
        decision = self.execution_policy.evaluate("bash", cmd)
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=cmd)
            result = self._structured_tool_result("bash", False, summary="Execution blocked.", errors=[decision.reason], data={"command": cmd})
            self._note_tool_result("bash", result, persist=True)
            return result

        try:
            self._run_tool_hook('pre', 'bash', cmd)
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="run_bash.pre_tool", code=ErrorCode.EXEC_ERROR)

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=cmd)
        execution_meta: dict[str, Any] = {"command": cmd, "executor": "", "translated_command": cmd, "translation_note": ""}

        def _execute_core(raw_cmd: str) -> str:
            translation_note = ""
            cmd_stripped = raw_cmd.strip()
            cmd_parts = cmd_stripped.split()
            if not cmd_parts:
                execution_meta.update({"executor": "", "translated_command": raw_cmd, "translation_note": ""})
                return self._structured_tool_result("bash", False, summary="Empty command.", errors=["Empty command."], data={"command": raw_cmd})
            cmd_base = cmd_parts[0].lower()

            # Determine Preferred Shell
            executor = "cmd" if os.name == "nt" else "sh"
            if os.name == "nt":
                preferred_shell = str(os.environ.get("FLEXI_SHELL", "")).strip().lower()
                # Default to cmd.exe on Windows. PowerShell is opt-in because some managed hosts fail to initialize it.
                if preferred_shell == "bash" and shutil.which("bash"):
                    executor = "bash"
                elif preferred_shell == "powershell" and shutil.which("powershell"):
                    executor = "powershell"
            execution_meta["executor"] = executor

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
            execution_meta["translated_command"] = cmd_to_run
            execution_meta["translation_note"] = translation_note

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
                    ok = res.returncode == 0 and not any(p in stderr for p in ["not recognized as", "command not found", "No such file or directory"])
                    summary = "Command completed." if ok else "Command failed."

                    not_found = ["not recognized as", "command not found", "No such file or directory"]
                    if any(p in stderr for p in not_found):
                        suggestion = f"Suggestion: use platform-native commands or verify the path. Current executor: {executor}"
                        stderr = f"{stderr}\n{suggestion}".strip()
                    trimmed_stdout = self.execution_policy.trim_output(decision, stdout)
                    trimmed_stderr = self.execution_policy.trim_output(decision, stderr)
                    return self._structured_tool_result(
                        "bash",
                        ok,
                        summary=summary,
                        errors=[] if ok else [trimmed_stderr or f"Command returned exit code {res.returncode}."] ,
                        data={
                            "command": raw_cmd,
                            "executor": executor,
                            "translated_command": cmd_to_run,
                            "translation_note": translation_note,
                            "returncode": res.returncode,
                            "stdout": trimmed_stdout,
                            "stderr": trimmed_stderr,
                        },
                    )

                except subprocess.TimeoutExpired as e:
                    attempt += 1
                    if attempt > retries:
                        return self._structured_tool_result("bash", False, summary="Command timed out.", errors=[f"Command timed out after {retries} retries ({cmd_to_run})"], data={"command": raw_cmd, "executor": executor, "translated_command": cmd_to_run})
                    time.sleep(1 * (2 ** (attempt - 1)))
                    continue
                except Exception as e:
                    return self._structured_tool_result("bash", False, summary="Execution failed.", errors=[str(e)], data={"command": raw_cmd, "executor": executor, "translated_command": cmd_to_run})

        result = self._run_tool_with_wrapper('bash', cmd, _execute_core)
        self._note_tool_result("bash", result, persist=True)
        result_payload = self._parse_tool_result_payload(result)
        self.execution_policy.audit(
            decision,
            action="finish",
            status="completed" if result_payload and result_payload.get("ok", False) else "failed",
            payload=cmd,
            result=self._tool_result_text(result),
            duration_ms=int((time.time() - start_time) * 1000),
        )
        try:
            self._run_tool_hook('post', 'bash', result)
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="run_bash.post_tool", code=ErrorCode.EXEC_ERROR)
        return self._append_reviewer_summary(result, "bash", cmd)

    def _apply_idle_proposal_patch(self, proposal_path: Path) -> bool:
        """Patch proposal file to implement actionable idle-workflow logic instead of only notes."""
        try:
            content = proposal_path.read_text(encoding='utf-8', errors='replace')
            changed = False

            # 1) Add a global toggle if missing (default OFF; allow env override)
            if "AUTO_IDLE_PROPOSAL_ENABLED" not in content:
                insert_marker = "# --- THE FlexiBot CORE ---"
                insert_pos = content.find(insert_marker)
                # Default to disabled to avoid surprising automatic code edits in deployments.
                # Allow enabling via environment variable (AUTO_IDLE_PROPOSAL_ENABLED=1/true/yes).
                default_line = ("AUTO_IDLE_PROPOSAL_ENABLED = os.environ.get(\"AUTO_IDLE_PROPOSAL_ENABLED\", \"false\").lower()"
                                " in (\"1\", \"true\", \"yes\")\n")
                if insert_pos != -1:
                    # ensure os is available near the top if it's not already imported in the file
                    content = content[:insert_pos] + "import os\n" + default_line + content[insert_pos:]
                else:
                    content = "import os\n" + default_line + content
                changed = True

            # 2) Ensure run_interactive_loop dispatches the workflow during idle condition
            warning_line = "ConsoleOutput.warning(f\"User idle for {idle_timeout}s. Resuming...\")"
            if warning_line in content and "bot.idle_proposal_workflow()" not in content:
                replacement = (warning_line + "\n" +
                               "                        if AUTO_IDLE_PROPOSAL_ENABLED:\n" +
                               "                            try:\n" +
                               "                                workflow_result = bot.idle_proposal_workflow()\n" +
                               "                                ConsoleOutput.system(f\"Idle workflow result: {workflow_result}\")\n" +
                               "                            except Exception as e:\n" +
                               "                                ConsoleOutput.error(f\"Idle workflow error: {e}\")\n")
                content = content.replace(warning_line, replacement)
                changed = True

            # 3) avoid just appending notes at bottom
            content = re.sub(r"(?m)^# Idle workflow note:.*$", "", content)

            if changed:
                proposal_path.write_text(content, encoding='utf-8')

            return changed
        except Exception as e:
            ConsoleOutput.error(f"Failed to apply idle proposal patch: {e}")
            return False

    def generate_improvement_plan(self) -> str:
        base = "Generate a concise plan for improving the current agent codebase without making unsafe changes."
        try:
            resp = self.client.chat([
                {"role": "system", "content": "You are an intelligent assistant that suggests code improvement plans."},
                {"role": "user", "content": base}
            ], temperature=0.5)
            plan_text = resp["choices"][0]["message"]["content"].strip()
        except Exception as e:
            plan_text = "Could not generate plan due to: " + str(e)
        return plan_text

    def _idle_resume_context(self, limit: int = 5) -> dict[str, Any]:
        pending_plans = self.state.query_history(tag="plan", limit=limit)
        recent_user = self.state.query_history(role="user", limit=limit)
        return {
            "pending_plans": [entry.get("content", "") for entry in pending_plans],
            "recent_user_requests": [entry.get("content", "") for entry in recent_user],
        }

    def _idle_last_test_result(self) -> dict[str, Any]:
        value = self.state.get_runtime_value(LAST_TEST_RUN_KEY, {})
        return copy.deepcopy(value) if isinstance(value, dict) else {}

    def _idle_goal_has_known_prerequisite_gap(self, goal: dict[str, Any]) -> bool:
        sample = " ".join(
            str(goal.get(field, "") or "").strip().lower()
            for field in ("blocked_reason", "next_action", "verification_target", "text")
        )
        if not sample:
            return False
        markers = (
            "missing",
            "not installed",
            "dependency",
            "module",
            "package",
            "command not found",
            "prerequisite",
            "credential",
            "token",
            "server",
            "port",
            "log",
            "runtime",
            "environment",
            "evidence",
            "verify",
        )
        return any(marker in sample for marker in markers)

    def _idle_blocked_goals(self) -> list[dict[str, Any]]:
        blocked: list[dict[str, Any]] = []
        for goal in self.active_goals():
            blocked_reason = str(goal.get("blocked_reason", "") or "").strip()
            if not blocked_reason:
                continue
            blocked.append(
                {
                    "id": str(goal.get("id", "") or "").strip(),
                    "text": str(goal.get("text", "") or "").strip(),
                    "blocked_reason": blocked_reason,
                    "next_action": str(goal.get("next_action", "") or "").strip(),
                    "verification_target": str(goal.get("verification_target", "") or "").strip(),
                    "known_missing_prerequisite": self._idle_goal_has_known_prerequisite_gap(goal),
                }
            )
        return blocked

    def _idle_stale_background_tasks(self) -> list[dict[str, Any]]:
        stale: list[dict[str, Any]] = []
        now = time.time()
        try:
            import psutil  # type: ignore
        except Exception:
            psutil = None

        for pid_str, info in sorted(self.state.active_processes.items()):
            task = self._normalize_bg_task_record(pid_str, info)
            ready_condition = task.get("ready_condition", {}) if isinstance(task.get("ready_condition"), dict) else {}
            ready_status = str(ready_condition.get("status", "") or "").strip().lower()
            launch_spec = task.get("launch_spec", {}) if isinstance(task.get("launch_spec"), dict) else {}
            status = str(task.get("status", "") or "").strip().lower()
            start_time = float(task.get("start_time", 0.0) or 0.0)
            timeout_seconds = int(
                ready_condition.get("timeout_seconds", 0) or launch_spec.get("timeout_seconds", 0) or 0
            )
            age_seconds = max(0.0, now - start_time) if start_time else 0.0
            reason = ""

            if psutil is not None:
                try:
                    proc = psutil.Process(int(pid_str))
                    proc_status = str(proc.status()).lower()
                    if proc_status in {"zombie", "dead"}:
                        reason = f"process is {proc_status}"
                except psutil.NoSuchProcess:
                    reason = "registered task is no longer running"
                except Exception:
                    pass

            if not reason and status in {"finished", "stopped", "terminated", "failed"}:
                reason = f"task status is {status}"
            if not reason and ready_status in {"timeout", "terminated", "failed"}:
                reason = f"ready condition is {ready_status}"
            if not reason and timeout_seconds and age_seconds > max(timeout_seconds * 2, 900):
                if ready_status in {"pending", "timeout", "not_configured"}:
                    reason = f"task exceeded readiness window ({int(age_seconds)}s > {timeout_seconds}s)"

            if not reason:
                continue

            stale.append(
                {
                    "pid": str(task.get("pid", "") or pid_str),
                    "type": str(task.get("type", "") or "").strip(),
                    "status": str(task.get("status", "") or "").strip(),
                    "reason": reason,
                    "goal": copy.deepcopy(task.get("goal", {})),
                    "ready_condition": copy.deepcopy(ready_condition),
                    "log_path": str(task.get("log_path", "") or "").strip(),
                    "age_seconds": int(age_seconds),
                }
            )
        return stale

    def _idle_failing_tests(self, active_goals: list[dict[str, Any]]) -> dict[str, Any]:
        result = self._idle_last_test_result()
        if not result or bool(result.get("success", True)):
            return {}

        active_goal_ids = {str(goal.get("id", "") or "").strip() for goal in active_goals if str(goal.get("id", "") or "").strip()}
        recorded_goal = result.get("goal", {}) if isinstance(result.get("goal"), dict) else {}
        recorded_goal_id = str(recorded_goal.get("id", "") or "").strip()
        if active_goal_ids and recorded_goal_id and recorded_goal_id not in active_goal_ids:
            return {}

        timestamp = float(result.get("timestamp", 0.0) or 0.0)
        if timestamp and time.time() - timestamp > 6 * 60 * 60:
            return {}

        return {
            "command": str(result.get("command", "") or "").strip(),
            "summary": str(result.get("summary", "") or "").strip(),
            "errors": [str(item).strip() for item in result.get("errors", []) if str(item).strip()][:5],
            "goal": copy.deepcopy(recorded_goal),
            "timestamp": timestamp,
        }

    def _idle_external_work_scan(self, resume_context: dict[str, Any] | None = None) -> dict[str, Any]:
        active_goals = self.active_goals()
        blocked_goals = self._idle_blocked_goals()
        blocked_with_prereqs = [goal for goal in blocked_goals if goal.get("known_missing_prerequisite")]
        stale_tasks = self._idle_stale_background_tasks()
        failing_tests = self._idle_failing_tests(active_goals)
        pending_plans = list((resume_context or {}).get("pending_plans", []))

        priority = "proposal_fallback"
        if blocked_with_prereqs:
            priority = "blocked_goals"
        elif stale_tasks:
            priority = "stale_background_tasks"
        elif failing_tests:
            priority = "failing_tests"
        elif active_goals:
            priority = "active_goals"

        has_external_work = bool(active_goals or blocked_with_prereqs or stale_tasks or failing_tests)
        return {
            "has_external_work": has_external_work,
            "priority": priority,
            "active_goals": [copy.deepcopy(goal) for goal in active_goals[:5]],
            "blocked_goals": blocked_with_prereqs[:5],
            "stale_background_tasks": stale_tasks[:5],
            "failing_tests": copy.deepcopy(failing_tests),
            "pending_plans": pending_plans[:5],
            "recent_user_requests": list((resume_context or {}).get("recent_user_requests", []))[:5],
        }

    def _idle_external_work_prompt(self, scan: dict[str, Any], resume_context: dict[str, Any] | None = None) -> str:
        lines = [
            "Idle mode detected meaningful external work.",
            "Do not start self-improvement proposals or rewrite the runtime unless all user-facing work is exhausted.",
            "Prioritize the current workspace and active goals.",
            "",
        ]

        active_goals = scan.get("active_goals", []) if isinstance(scan.get("active_goals"), list) else []
        if active_goals:
            lines.append("Active goals:")
            for goal in active_goals[:3]:
                lines.append(
                    f"- [{goal.get('id', '')}] {goal.get('text', '')} | next_action={goal.get('next_action', '')} | blocked_reason={goal.get('blocked_reason', '')}"
                )
            lines.append("")

        blocked_goals = scan.get("blocked_goals", []) if isinstance(scan.get("blocked_goals"), list) else []
        if blocked_goals:
            lines.append("Blocked goals with known missing prerequisites:")
            for goal in blocked_goals[:3]:
                lines.append(
                    f"- [{goal.get('id', '')}] reason={goal.get('blocked_reason', '')} | next_action={goal.get('next_action', '')} | verification_target={goal.get('verification_target', '')}"
                )
            lines.append("")

        stale_tasks = scan.get("stale_background_tasks", []) if isinstance(scan.get("stale_background_tasks"), list) else []
        if stale_tasks:
            lines.append("Stale background tasks:")
            for task in stale_tasks[:3]:
                lines.append(
                    f"- pid={task.get('pid', '')} status={task.get('status', '')} reason={task.get('reason', '')} log_path={task.get('log_path', '')}"
                )
            lines.append("")

        failing_tests = scan.get("failing_tests", {}) if isinstance(scan.get("failing_tests"), dict) else {}
        if failing_tests:
            lines.append("Recent failing tests tied to active work:")
            lines.append(f"- command={failing_tests.get('command', '')}")
            lines.append(f"- summary={failing_tests.get('summary', '')}")
            for error in failing_tests.get("errors", [])[:3]:
                lines.append(f"- error={error}")
            lines.append("")

        pending_plans = list((resume_context or {}).get("pending_plans", []))[:3]
        if pending_plans:
            lines.append("Pending plans from recent history:")
            for item in pending_plans:
                lines.append(f"- {str(item)[:240]}")
            lines.append("")

        lines.extend(
            [
                "Act on the highest-value external work first:",
                "1. unblock blocked goals by inspecting or satisfying missing prerequisites,",
                "2. inspect, stop, or restart stale background tasks if they affect active goals,",
                "3. investigate failing tests before making unrelated changes,",
                "4. if none of the above block progress, continue the highest-priority active goal.",
                "Avoid broad introspection loops and avoid self-rewrite work in this turn.",
            ]
        )
        return "\n".join(lines).strip()

    def _idle_llm_text(self, system_prompt: str, user_prompt: str, fallback: str) -> str:
        try:
            resp = self.client.chat([
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ], temperature=0.3)
            text = resp["choices"][0]["message"]["content"].strip()
            return text or fallback
        except Exception as e:
            return f"{fallback} ({e})"

    def _idle_analyze_proposal(self, proposal_path: Path, plan_text: str, resume_context: dict[str, Any]) -> str:
        proposal_source = proposal_path.read_text(encoding="utf-8", errors="replace")
        source_preview = proposal_source[:12000]
        if len(proposal_source) > len(source_preview):
            source_preview += "\n\n[TRUNCATED SOURCE PREVIEW]"
        return self._idle_llm_text(
            "You are a senior software architect reviewing a Python autonomous agent runtime during an idle self-improvement cycle.",
            (
                f"Improvement plan:\n{plan_text}\n\n"
                f"Resume context:\n{json.dumps(resume_context, indent=2)}\n\n"
                f"Proposal file: {proposal_path.name}\n"
                "Analyze the latest proposal code. Identify the best improvements, useful new features, and the highest-risk weak points. "
                "Respond with three short sections: Strengths, Gaps, Recommended Additions.\n\n"
                f"Proposal source preview:\n{source_preview}"
            ),
            "Idle analysis unavailable.",
        )

    def _idle_audit_proposal(self, proposal_path: Path, analysis_text: str, validation_result: dict[str, Any], compile_result: str) -> str:
        compile_payload = self._parse_tool_result_payload(compile_result) or {"raw": compile_result}
        return self._idle_llm_text(
            "You are a strict code auditor reviewing an idle proposal for a Python runtime.",
            (
                f"Proposal: {proposal_path.name}\n\n"
                f"Analysis:\n{analysis_text}\n\n"
                f"Python validation:\n{json.dumps(validation_result, indent=2)}\n\n"
                f"Compile result:\n{json.dumps(compile_payload, indent=2) if isinstance(compile_payload, dict) else str(compile_payload)}\n\n"
                "Audit this proposal and suggest concrete improvements and features to add. "
                "Respond with three short sections: Audit Findings, Feature Opportunities, Safety Notes."
            ),
            "Idle audit unavailable.",
        )

    def _idle_plan_changes(self, proposal_path: Path, analysis_text: str, audit_text: str) -> str:
        return self._idle_llm_text(
            "You are planning code changes for an idle self-improvement workflow.",
            (
                f"Proposal: {proposal_path.name}\n\n"
                f"Analysis:\n{analysis_text}\n\n"
                f"Audit:\n{audit_text}\n\n"
                "Create an actionable change plan for updating the proposal. Keep it short, concrete, and implementation-oriented. "
                "Return a numbered list of steps."
            ),
            "1. Validate proposal\n2. Apply safe idle workflow improvements\n3. Review and test the updated proposal",
        )

    def _idle_artifact_path(self, proposal_path: Path, suffix: str, extension: str) -> Path:
        return proposal_path.with_name(f"{proposal_path.stem}.{suffix}.{extension}")

    def _idle_artifact_archive_dir(self, proposals_dir: Path, proposal_path: Path) -> Path:
        return proposals_dir / PROPOSAL_ARTIFACT_ARCHIVE_DIRNAME / proposal_path.stem

    def _idle_write_artifact_text(self, proposal_path: Path, suffix: str, title: str, body: str) -> Path | None:
        path = self._idle_artifact_path(proposal_path, suffix, "md")
        try:
            lines = [f"# {title}", "", f"Generated: {datetime.now().isoformat()}", f"Proposal: {proposal_path.name}", "", body or ""]
            path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
            return path
        except Exception as e:
            ConsoleOutput.warning(f"Could not write idle artifact {path.name}: {e}")
            return None

    def _idle_write_artifact_json(self, proposal_path: Path, suffix: str, payload: dict[str, Any]) -> Path | None:
        path = self._idle_artifact_path(proposal_path, suffix, "json")
        try:
            # Write atomically and set restrictive permissions to avoid accidental leakage in working dirs.
            import tempfile, os, hmac, hashlib
            data = (json.dumps(payload, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
            # ensure parent dir exists with conservative permissions
            path.parent.mkdir(parents=True, exist_ok=True)
            try:
                os.chmod(path.parent, 0o700)
            except Exception:
                # best-effort; don't fail on platforms that don't support chmod
                pass

            # Use mkstemp+fdopen to write atomically and control permission setting
            fd, tmpname = tempfile.mkstemp(dir=str(path.parent))
            try:
                try:
                    os.fchmod(fd, 0o600)
                except Exception:
                    # best-effort: platforms may not support fchmod; continue and ensure final chmod below
                    pass
                with os.fdopen(fd, "wb") as tf:
                    tf.write(data)
                    tf.flush()
                    try:
                        os.fsync(tf.fileno())
                    except Exception:
                        pass
                os.replace(tmpname, str(path))
                try:
                    os.chmod(str(path), 0o600)
                except Exception:
                    pass
            finally:
                # Ensure leftover temp file is removed on failure paths
                if os.path.exists(tmpname):
                    try:
                        os.unlink(tmpname)
                    except Exception:
                        pass

            # Optional HMAC signature sidecar to detect tampering of generated artifacts.
            try:
                signing_key = os.environ.get("SIGNING_KEY")
                if signing_key:
                    sig = hmac.new(signing_key.encode("utf-8"), data, hashlib.sha256).hexdigest()
                    sig_path = str(path) + ".sig"
                    with open(sig_path, "w", encoding="utf-8") as sf:
                        sf.write(sig + "\n")
                    try:
                        os.chmod(sig_path, 0o600)
                    except Exception:
                        pass
            except Exception:
                # Non-fatal: signature best-effort only; avoid failing artifact write for environment issues.
                pass

            return path
        except Exception as e:
            ConsoleOutput.warning(f"Could not write idle artifact {path.name}: {e}")
            return None

    def _idle_extract_json_block(self, text: str) -> dict[str, Any] | None:
        if not isinstance(text, str):
            return None
        candidates = [text.strip()]
        fenced = re.findall(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
        candidates.extend(fenced)
        brace_match = re.search(r"(\{.*\})", text, flags=re.DOTALL)
        if brace_match:
            candidates.append(brace_match.group(1))
        for candidate in candidates:
            try:
                parsed = json.loads(candidate)
                if isinstance(parsed, dict):
                    return parsed
            except Exception:
                continue
        return None

    def _idle_rewrite_sections_from_source(self, source: str) -> list[dict[str, Any]]:
        try:
            tree = ast.parse(source)
        except Exception:
            return []

        lines = source.splitlines(keepends=True)
        line_offsets = [0]
        for line in lines:
            line_offsets.append(line_offsets[-1] + len(line))

        sections: list[dict[str, Any]] = []
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            node_name = getattr(node, "name", "")
            if not node_name:
                continue
            if node_name not in IDLE_REWRITE_SECTION_NAMES and not node_name.startswith("_idle_"):
                continue
            start_line = getattr(node, "lineno", None)
            end_line = getattr(node, "end_lineno", None)
            if not start_line or not end_line:
                continue
            start_offset = line_offsets[start_line - 1]
            end_offset = line_offsets[end_line]
            section_text = source[start_offset:end_offset]
            sections.append(
                {
                    "name": node_name,
                    "start_line": start_line,
                    "end_line": end_line,
                    "start_offset": start_offset,
                    "end_offset": end_offset,
                    "text": section_text,
                }
            )

        sections.sort(key=lambda item: (item["start_line"], item["name"]))
        return sections

    def _idle_rewrite_sections(self, proposal_path: Path) -> list[dict[str, Any]]:
        try:
            source = proposal_path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            return []
        return self._idle_rewrite_sections_from_source(source)

    def _idle_rewrite_scope_preview(self, sections: list[dict[str, Any]], limit_per_section: int = 4000) -> str:
        if not sections:
            return "No approved rewrite sections detected."
        previews: list[str] = []
        for section in sections:
            text = section.get("text", "")
            preview = text[:limit_per_section]
            if len(text) > len(preview):
                preview += "\n# [TRUNCATED SECTION PREVIEW]"
            previews.append(
                f"Section: {section['name']} ({section['start_line']}-{section['end_line']})\n"
                f"{preview}"
            )
        return "\n\n".join(previews)

    def _idle_render_artifact_summary(self, proposal_path: Path, artifact_paths: dict[str, str], status: dict[str, Any]) -> str:
        lines = [
            "## Status",
            "",
        ]
        for key, value in status.items():
            lines.append(f"- {key}: {value}")
        lines.extend(["", "## Artifacts", ""])
        for label, path_text in artifact_paths.items():
            if not path_text:
                lines.append(f"- {label}: not generated")
                continue
            artifact_path = Path(path_text)
            rel_target = artifact_path.name.replace(" ", "%20")
            lines.append(f"- [{label}]({rel_target})")
        lines.append("")
        return "\n".join(lines)

    def _idle_rotate_old_proposal_artifacts(self, proposals_dir: Path, keep_recent: int = PROPOSAL_ARTIFACT_KEEP_RECENT) -> dict[str, Any]:
        kept = max(1, keep_recent)
        archived: list[str] = []
        errors: list[str] = []
        try:
            proposals = sorted(proposals_dir.glob("proposalAgent_*.py"), key=lambda path: path.stat().st_mtime, reverse=True)
        except Exception as e:
            return {"ok": False, "archived": archived, "errors": [str(e)]}

        for proposal_path in proposals[kept:]:
            artifact_candidates = [
                artifact_path
                for artifact_path in sorted(proposals_dir.glob(f"{proposal_path.stem}.*"))
                if artifact_path != proposal_path and artifact_path.parent == proposals_dir
            ]
            if not artifact_candidates:
                continue

            archive_dir = self._idle_artifact_archive_dir(proposals_dir, proposal_path)
            try:
                archive_dir.mkdir(parents=True, exist_ok=True)
            except Exception as e:
                errors.append(f"{proposal_path.name}: could not create archive dir: {e}")
                continue

            for artifact_path in artifact_candidates:
                destination = archive_dir / artifact_path.name
                try:
                    if destination.exists():
                        artifact_path.unlink()
                    else:
                        shutil.move(str(artifact_path), str(destination))
                    archived.append(str(destination))
                except Exception as e:
                    errors.append(f"{artifact_path.name}: {e}")

        return {"ok": not errors, "archived": archived, "errors": errors, "kept_recent": kept}

    def _idle_collect_proposal_files(self, proposal_path: Path, artifact_paths: dict[str, str] | None = None) -> list[Path]:
        collected: list[Path] = []
        seen: set[Path] = set()

        def add_path(path: Path | None):
            if path is None:
                return
            try:
                resolved = path.resolve()
            except Exception:
                resolved = path
            if resolved in seen or not path.exists() or not path.is_file():
                return
            seen.add(resolved)
            collected.append(path)

        add_path(proposal_path)
        for candidate in proposal_path.parent.glob(f"{proposal_path.stem}.*"):
            if candidate == proposal_path or candidate.suffix == ".sig":
                add_path(candidate)
                continue
            add_path(candidate)
        for raw_path in (artifact_paths or {}).values():
            if raw_path:
                add_path(Path(raw_path))
                sig_path = Path(str(raw_path) + ".sig")
                add_path(sig_path)
        return collected

    def _idle_promote_proposal(self, proposal_path: Path, artifact_paths: dict[str, str], destination_dir: Path) -> dict[str, Any]:
        destination_dir.mkdir(parents=True, exist_ok=True)
        copied: list[str] = []
        errors: list[str] = []
        for source in self._idle_collect_proposal_files(proposal_path, artifact_paths):
            destination = destination_dir / source.name
            try:
                shutil.copy2(source, destination)
                copied.append(str(destination))
            except Exception as e:
                errors.append(f"{source.name}: {e}")
        return {
            "ok": not errors,
            "destination": str(destination_dir),
            "files": copied,
            "errors": errors,
        }

    def _idle_generate_rewrite_plan(self, proposal_path: Path, analysis_text: str, audit_text: str, change_plan_text: str) -> dict[str, Any]:
        sections = self._idle_rewrite_sections(proposal_path)
        scope_preview = self._idle_rewrite_scope_preview(sections)
        section_catalog = [
            {"name": section["name"], "start_line": section["start_line"], "end_line": section["end_line"]}
            for section in sections
        ]
        fallback = {"edits": [], "notes": ["Rewrite plan unavailable."]}
        raw = self._idle_llm_text(
            "You are generating bounded code rewrites for a Python proposal file. Only return JSON.",
            (
                f"Proposal: {proposal_path.name}\n\n"
                f"Analysis:\n{analysis_text}\n\n"
                f"Audit:\n{audit_text}\n\n"
                f"Change plan:\n{change_plan_text}\n\n"
                f"Approved rewrite sections: {json.dumps(section_catalog, ensure_ascii=False)}\n\n"
                "Return JSON with this exact shape: {\"edits\": [{\"section\": str, \"search\": str, \"replace\": str, \"rationale\": str}], \"notes\": [str]}. "
                "Constraints: at most 3 edits, every edit must target only one approved section, each search string must match exactly one existing code block within that section, each replace string must stay focused and under 4000 characters, do not rewrite unrelated code, do not invent placeholders.\n\n"
                f"Approved section source preview:\n{scope_preview}"
            ),
            json.dumps(fallback),
        )
        parsed = self._idle_extract_json_block(raw)
        if not parsed:
            parsed = fallback
            parsed["notes"] = ["LLM rewrite plan was not valid JSON."]
        edits = parsed.get("edits", []) if isinstance(parsed, dict) else []
        if not isinstance(edits, list):
            edits = []
        bounded_edits = []
        # Denylist of risky runtime operations; any proposed replacement containing these
        # substrings will be skipped to avoid introducing dynamic execution, unsafe
        # deserialization, or unrestricted subprocess/network calls.
        disallowed = [
            "pickle.loads", "pickle.load", "pickle.", "importlib", "exec(", "eval(", "__import__",
            "subprocess", "os.system", "os.exec", "shutil.rmtree", "socket", "ctypes", "requests", "urllib",
        ]
        for item in edits[:3]:
            if not isinstance(item, dict):
                continue
            section = str(item.get("section", "")).strip()
            search = str(item.get("search", ""))
            replace = str(item.get("replace", ""))
            rationale = str(item.get("rationale", ""))
            if not section or not search.strip() or not replace.strip():
                continue
            if len(search) > 4000 or len(replace) > 4000:
                continue
            lower_replace = replace.lower()
            if any(pat in lower_replace for pat in disallowed):
                # Surface skipped edits in the notes so operators can inspect and approve manually.
                try:
                    parsed.setdefault("notes", []).append(f"Skipped edit for section '{section}': contains disallowed pattern.")
                except Exception:
                    pass
                continue
            bounded_edits.append({"section": section, "search": search, "replace": replace, "rationale": rationale})
        notes = parsed.get("notes", []) if isinstance(parsed, dict) else []
        if not isinstance(notes, list):
            notes = [str(notes)]
        return {
            "edits": bounded_edits,
            "notes": [str(note) for note in notes[:20]],
            "allowed_sections": section_catalog,
            "raw": raw[:4000],
        }

    def _idle_apply_rewrite_plan(self, proposal_path: Path, rewrite_plan: dict[str, Any]) -> dict[str, Any]:
        try:
            content = proposal_path.read_text(encoding="utf-8", errors="replace")
        except Exception as e:
            return {"ok": False, "applied": [], "skipped": [{"reason": f"Could not read proposal: {e}"}]}

        applied: list[dict[str, Any]] = []
        skipped: list[dict[str, Any]] = []
        updated = content
        for index, edit in enumerate(rewrite_plan.get("edits", [])[:3], start=1):
            sections = {section["name"]: section for section in self._idle_rewrite_sections_from_source(updated)}
            section_name = str(edit.get("section", "")).strip()
            search = str(edit.get("search", ""))
            replace = str(edit.get("replace", ""))
            rationale = str(edit.get("rationale", ""))
            section = sections.get(section_name)
            if not section:
                skipped.append({"index": index, "reason": f"Section not allowed: {section_name or 'missing'}.", "rationale": rationale})
                continue
            match_count = updated.count(search)
            if match_count != 1:
                skipped.append({"index": index, "reason": f"Expected exactly 1 match, found {match_count}.", "rationale": rationale})
                continue
            match_index = updated.find(search)
            if match_index < 0:
                skipped.append({"index": index, "reason": "Search block not found.", "rationale": rationale})
                continue
            match_end = match_index + len(search)
            if match_index < section["start_offset"] or match_end > section["end_offset"]:
                skipped.append({"index": index, "reason": f"Search block is outside approved section {section_name}.", "rationale": rationale})
                continue
            delta = len(replace) - len(search)
            if abs(delta) > 5000:
                skipped.append({"index": index, "reason": f"Edit size delta too large ({delta}).", "rationale": rationale})
                continue
            updated = updated.replace(search, replace, 1)
            applied.append({"index": index, "section": section_name, "rationale": rationale, "search_length": len(search), "replace_length": len(replace)})

        final_sections = {section["name"]: section for section in self._idle_rewrite_sections_from_source(updated)}

        if applied:
            try:
                # Write updated proposal atomically to avoid corrupting the live source on interruptions.
                import tempfile, os
                data = updated.encode("utf-8")
                proposal_path.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=str(proposal_path.parent), delete=False) as tf:
                    tf.write(data)
                    tf.flush()
                    try:
                        os.fsync(tf.fileno())
                    except Exception:
                        pass
                    tmpname = tf.name
                os.replace(tmpname, str(proposal_path))
                try:
                    os.chmod(str(proposal_path), 0o600)
                except Exception:
                    pass
            except Exception as e:
                return {"ok": False, "applied": [], "skipped": skipped + [{"reason": f"Could not write proposal: {e}"}]}

        return {
            "ok": True,
            "applied": applied,
            "skipped": skipped,
            "applied_count": len(applied),
            "requested_count": len(rewrite_plan.get("edits", [])[:3]),
            "allowed_sections": sorted(final_sections.keys()),
        }

    def _append_idle_proposal_notes(self, proposal_path: Path, sections: list[tuple[str, str]]) -> bool:
        try:
            lines = ["", "# --- IDLE WORKFLOW REPORT ---"]
            for title, body in sections:
                lines.append(f"# {title}:")
                for raw_line in (body or "").splitlines():
                    lines.append(f"# {raw_line}")
            lines.append("# --- END IDLE WORKFLOW REPORT ---")
            with proposal_path.open("a", encoding="utf-8") as fp:
                fp.write("\n".join(lines) + "\n")
            return True
        except Exception as e:
            ConsoleOutput.warning(f"Could not append idle workflow notes to proposal: {e}")
            return False

    def _idle_review_summary(self, proposal_path: Path, stage: str, context_text: str) -> str:
        return self._idle_llm_text(
            "You are a concise reviewer in an autonomous idle-code-improvement pipeline.",
            (
                f"Proposal: {proposal_path.name}\n"
                f"Stage: {stage}\n\n"
                f"Context:\n{context_text}\n\n"
                "Provide a short review with two lines: Assessment: and Next step:."
            ),
            f"Assessment: Review unavailable at stage {stage}.\nNext step: Inspect proposal manually.",
        )

    def run_proposal_sdlc(self, proposal_path: Path, return_details: bool = False) -> bool | dict[str, Any]:
        """Run proposal through lightweight SDLC steps before acceptance."""
        details: dict[str, Any] = {
            "proposal": str(proposal_path),
            "compile": {"ok": False, "result": {}},
            "review": {"ok": False, "result": {}},
            "tests": {"ok": False, "result": {}},
            "overall_ok": False,
        }

        # 1) Build/compile check
        try:
            compile_out = self.run_bash(f'"{sys.executable}" -m py_compile "{proposal_path}"')
            compile_payload = self._parse_tool_result_payload(compile_out) or {"raw": compile_out}
            compile_ok = not self._tool_result_failed(compile_out)
            details["compile"] = {"ok": compile_ok, "result": compile_payload}
            if not compile_ok:
                ConsoleOutput.warning(f"SDLC compile failed for {proposal_path}: {self._tool_result_text(compile_out)}")
                details["overall_ok"] = False
                return details if return_details else False
            ConsoleOutput.system(f"SDLC compile passed for {proposal_path}")
        except Exception as e:
            ConsoleOutput.error(f"SDLC compile exception: {e}")
            details["compile"] = {"ok": False, "result": {"error": str(e)}}
            details["overall_ok"] = False
            return details if return_details else False

        # 2) Code review (lint step)
        try:
            lint_out = self.run_bash(f'"{sys.executable}" -m pylint "{proposal_path}" --disable=C,R')
            lint_payload = self._parse_tool_result_payload(lint_out) or {"raw": lint_out}
            lint_text = self._tool_result_text(lint_out)
            lint_ok = not self._tool_result_failed(lint_out) or "Your code has been rated" in lint_text or "No config file found" in lint_text
            details["review"] = {"ok": lint_ok, "result": lint_payload}
            if lint_ok:
                ConsoleOutput.system(f"SDLC code review passed for {proposal_path}")
            else:
                ConsoleOutput.warning(f"SDLC code review warning/errors for {proposal_path}: {lint_text}")
                # treat as fail unless explicitly non-fatal
                if "error" in lint_text.lower() or "fatal" in lint_text.lower():
                    details["overall_ok"] = False
                    return details if return_details else False
            # continue even if warnings exist
        except Exception as e:
            ConsoleOutput.warning(f"SDLC code review fallback: pylint not available or error ({e})")
            details["review"] = {"ok": True, "result": {"warning": str(e)}}

        # 3) Test run
        try:
            if Path("tests").is_dir():
                test_out = self.tool_run_tests(f'"{sys.executable}" -m pytest -q')
                test_payload = self._parse_tool_result_payload(test_out) or {"raw": test_out}
                test_ok = not self._tool_result_failed(test_out)
                details["tests"] = {"ok": test_ok, "result": test_payload}
                if not test_ok:
                    ConsoleOutput.warning(f"SDLC testing failed: {self._tool_result_text(test_out)}")
                    details["overall_ok"] = False
                    return details if return_details else False
                ConsoleOutput.system("SDLC testing passed")
            else:
                ConsoleOutput.system("No tests directory found; evaluating via py_compile only (minimal tests)")
                details["tests"] = {"ok": True, "result": {"warning": "No tests directory found; py_compile only."}}
        except Exception as e:
            ConsoleOutput.error(f"SDLC testing exception: {e}")
            details["tests"] = {"ok": False, "result": {"error": str(e)}}
            details["overall_ok"] = False
            return details if return_details else False

        details["overall_ok"] = True
        return details if return_details else True

    def _background_proposal_agent(self):
        """Background agent: watch proposals/approved and apply code updates to flexiFocus.py."""
        proposals_dir = Path("proposals")
        applied_dir = proposals_dir / "applied"
        watch_dir = proposals_dir / "approved"
        proposals_dir.mkdir(parents=True, exist_ok=True)
        watch_dir.mkdir(parents=True, exist_ok=True)
        applied_dir.mkdir(parents=True, exist_ok=True)

        while True:
            for proposal_path in watch_dir.glob("proposalAgent_*.py"):
                try:
                    patch_target = Path(__file__).resolve()
                    shutil.copy2(proposal_path, patch_target)
                    ConsoleOutput.system(f"Background agent applied proposal {proposal_path} to flexiFocus.py")

                    # archive applied set
                    dest = applied_dir / proposal_path.name
                    shutil.copy2(proposal_path, dest)
                    proposal_path.unlink(missing_ok=True)
                except Exception as e:
                    ConsoleOutput.error(f"Background proposal agent error applying {proposal_path}: {e}")
            time.sleep(15)


    def idle_proposal_workflow(self, auto_propose: bool = False, auto_confirm: bool | None = None):
        """Idle-triggered workflow that prioritizes external work before self-improvement.

        Flow:
        1. Inspect active goals, blocked goals, stale background tasks, and recent failing tests.
        2. Resume meaningful external work when any of those signals are present.
        3. Only when there is no meaningful external work, fall back to the staged proposal pipeline.
        """
        try:
            workflow_trace: dict[str, Any] = {"steps": []}
            resume_context = self._idle_resume_context(limit=5)
            idle_scan = self._idle_external_work_scan(resume_context)
            self.state.set_runtime_value(IDLE_TRIAGE_RECORD_KEY, idle_scan, persist=True)
            workflow_trace["idle_scan"] = idle_scan
            workflow_trace["steps"].append({"step": "idle_triage", "ok": True, "summary": json.dumps(idle_scan, ensure_ascii=False)[:1200]})

            if idle_scan.get("has_external_work"):
                external_prompt = self._idle_external_work_prompt(idle_scan, resume_context)
                ConsoleOutput.system(f"Idle workflow: prioritizing external work via {idle_scan.get('priority', 'active_goals')}.")
                external_result = self.handle_turn(external_prompt)
                workflow_trace["external_work_prompt"] = external_prompt
                workflow_trace["external_work_result"] = external_result
                workflow_trace["steps"].append(
                    {
                        "step": "resume_external_work",
                        "ok": True,
                        "summary": str(external_result)[:1200],
                    }
                )
                return (
                    f"Idle mode resumed external work ({idle_scan.get('priority', 'active_goals')}): "
                    f"{str(external_result)[:600]}"
                )

            plan_text = self.generate_improvement_plan()
            self.logger.log_plan_event(plan_text, context="idle_proposal_workflow")
            ConsoleOutput.system("Idle workflow plan generated.")
            workflow_trace["steps"].append({"step": "generate_plan", "ok": True, "summary": plan_text[:500]})

            # 2. proposal creation (unique name each run for persistent history)
            source_path = Path(__file__).resolve()
            proposals_dir = Path("proposals")
            proposals_dir.mkdir(parents=True, exist_ok=True)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            proposal_path = proposals_dir / f"proposalAgent_{timestamp}.py"
            shutil.copy2(source_path, proposal_path)
            ConsoleOutput.system(f"Crafted proposal file: {proposal_path}")
            workflow_trace["proposal_path"] = str(proposal_path)
            workflow_trace["steps"].append({"step": "copy_proposal", "ok": True, "summary": str(proposal_path)})

            # 3. analyze proposal and suggest improvements/features
            analysis_text = self._idle_analyze_proposal(proposal_path, plan_text, resume_context)
            ConsoleOutput.system("Idle workflow analysis completed.")
            workflow_trace["analysis"] = analysis_text
            workflow_trace["steps"].append({"step": "analyze_proposal", "ok": True, "summary": analysis_text[:1000]})

            # 4. audit proposal with python validation + compile result + LLM audit
            audit_text = rlm_validate_python(filepath=str(proposal_path))
            try:
                validation_result = json.loads(audit_text)
            except Exception:
                validation_result = {"ok": False, "errors": ["Audit output not JSON"]}

            compile_check = self.run_bash(f'"{sys.executable}" -m py_compile "{proposal_path}"')
            proposal_audit_text = self._idle_audit_proposal(proposal_path, analysis_text, validation_result, compile_check)
            ConsoleOutput.system("Idle workflow audit completed.")
            workflow_trace["audit"] = proposal_audit_text
            workflow_trace["steps"].append({"step": "audit_proposal", "ok": validation_result.get("ok", False) and not self._tool_result_failed(compile_check), "summary": proposal_audit_text[:1000]})

            if not validation_result.get("ok", False):
                ConsoleOutput.warning(f"Proposal audit found issues: {validation_result.get('errors', [])}")
                proposal_ok = False
            else:
                ConsoleOutput.system("Proposal audit passed.")
                proposal_ok = True

            # 5. plan changes from analysis and audit
            change_plan_text = self._idle_plan_changes(proposal_path, analysis_text, proposal_audit_text)
            ConsoleOutput.system("Idle workflow change plan created.")
            workflow_trace["change_plan"] = change_plan_text
            workflow_trace["steps"].append({"step": "plan_changes", "ok": True, "summary": change_plan_text[:1000]})

            # 6. execute planned changes and update proposal
            rewrite_plan = self._idle_generate_rewrite_plan(proposal_path, analysis_text, proposal_audit_text, change_plan_text)
            rewrite_result = self._idle_apply_rewrite_plan(proposal_path, rewrite_plan)
            patch_applied = self._apply_idle_proposal_patch(proposal_path)
            notes_applied = self._append_idle_proposal_notes(
                proposal_path,
                [
                    ("Idle Improvement Plan", plan_text),
                    ("Resume Context", json.dumps(resume_context, indent=2)),
                    ("Proposal Analysis", analysis_text),
                    ("Proposal Audit", proposal_audit_text),
                    ("Change Plan", change_plan_text),
                ],
            )
            artifact_paths = {
                "analysis": str(self._idle_write_artifact_text(proposal_path, "analysis", "Idle Proposal Analysis", analysis_text) or ""),
                "audit": str(self._idle_write_artifact_text(proposal_path, "audit", "Idle Proposal Audit", proposal_audit_text) or ""),
                "change_plan": str(self._idle_write_artifact_text(proposal_path, "change-plan", "Idle Proposal Change Plan", change_plan_text) or ""),
                "rewrite_plan": str(self._idle_write_artifact_json(proposal_path, "rewrite-plan", rewrite_plan) or ""),
                "rewrite_result": str(self._idle_write_artifact_json(proposal_path, "rewrite-result", rewrite_result) or ""),
            }
            ConsoleOutput.system(f"Idle proposal rewrites applied: {rewrite_result.get('applied_count', 0)}; patch applied: {patch_applied}; notes appended: {notes_applied}")
            workflow_trace["rewrite_plan"] = rewrite_plan
            workflow_trace["rewrite_result"] = rewrite_result
            workflow_trace["artifact_paths"] = artifact_paths
            workflow_trace["steps"].append({"step": "execute_changes", "ok": bool(rewrite_result.get("applied_count", 0) or patch_applied or notes_applied), "summary": json.dumps({"rewrite_result": rewrite_result, "patch_applied": patch_applied, "notes_applied": notes_applied, "artifact_paths": artifact_paths})[:1200]})

            # 7. review updated proposal
            pre_test_review = self._idle_review_summary(
                proposal_path,
                "post-update-review",
                f"Analysis:\n{analysis_text}\n\nAudit:\n{proposal_audit_text}\n\nChange plan:\n{change_plan_text}\n\nPatch applied: {patch_applied}\nNotes applied: {notes_applied}",
            )
            workflow_trace["pre_test_review"] = pre_test_review
            workflow_trace["steps"].append({"step": "review_before_test", "ok": True, "summary": pre_test_review[:1000]})

            # 8. evaluation: compile check then SDLC test/review pass
            compile_res = self.run_bash(f'"{sys.executable}" -m py_compile "{proposal_path}"')
            compile_ok = not self._tool_result_failed(compile_res)
            workflow_trace["compile"] = compile_res
            workflow_trace["steps"].append({"step": "compile", "ok": compile_ok, "summary": self._tool_result_text(compile_res)[:1000]})

            sdlc_details = self.run_proposal_sdlc(proposal_path, return_details=True)
            workflow_trace["sdlc"] = sdlc_details
            workflow_trace["steps"].append({"step": "sdlc", "ok": bool(sdlc_details.get("overall_ok", False)), "summary": json.dumps(sdlc_details)[:1200]})

            final_review = self._idle_review_summary(
                proposal_path,
                "post-test-review",
                f"Pre-test review:\n{pre_test_review}\n\nCompile:\n{self._tool_result_text(compile_res)}\n\nSDLC:\n{json.dumps(sdlc_details, indent=2)}",
            )
            workflow_trace["final_review"] = final_review
            workflow_trace["steps"].append({"step": "final_review", "ok": True, "summary": final_review[:1000]})

            evaluation_ok = compile_ok and bool(sdlc_details.get("overall_ok", False))
            approved_dir = proposals_dir / "approved"
            promoted = {"ok": False, "destination": "", "files": [], "errors": []}
            updated = False

            if evaluation_ok and proposal_ok and auto_propose:
                promoted = self._idle_promote_proposal(proposal_path, artifact_paths, approved_dir)
                workflow_trace["promotion"] = promoted
                workflow_trace["steps"].append({"step": "promote_proposal", "ok": bool(promoted.get("ok", False)), "summary": json.dumps(promoted)[:1200]})
                should_apply = bool(auto_confirm)
                if should_apply and promoted.get("ok", False):
                    try:
                        patch_target = Path(__file__).resolve()
                        shutil.copy2(proposal_path, patch_target)
                        updated = True
                        ConsoleOutput.system(f"Idle workflow auto-applied proposal {proposal_path.name} to flexiFocus.py")
                    except Exception as e:
                        ConsoleOutput.error(f"Idle workflow failed to auto-apply proposal: {e}")
                        workflow_trace["steps"].append({"step": "auto_apply", "ok": False, "summary": str(e)[:1000]})
                elif should_apply and not promoted.get("ok", False):
                    ConsoleOutput.warning("Idle workflow wanted to auto-apply but proposal promotion failed.")
            else:
                workflow_trace["steps"].append({"step": "promote_proposal", "ok": False, "summary": "Proposal not promoted (evaluation failed or auto_propose disabled)."})

            rotation = self._idle_rotate_old_proposal_artifacts(proposals_dir)
            workflow_trace["rotation"] = rotation
            workflow_trace["steps"].append({"step": "rotate_artifacts", "ok": bool(rotation.get("ok", False)), "summary": json.dumps(rotation)[:1000]})

            artifact_summary = self._idle_render_artifact_summary(
                proposal_path,
                artifact_paths,
                {
                    "proposal_ok": proposal_ok,
                    "evaluation_ok": evaluation_ok,
                    "updated": updated,
                    "promoted": promoted.get("ok", False),
                },
            )
            summary_path = self._idle_write_artifact_text(proposal_path, "summary", "Idle Proposal Workflow Summary", artifact_summary)
            if summary_path:
                artifact_paths["summary"] = str(summary_path)

            return {
                "proposal_ok": proposal_ok,
                "evaluation_ok": evaluation_ok,
                "updated": updated,
                "promoted": promoted,
                "proposal_path": str(proposal_path),
                "artifact_paths": artifact_paths,
                "review": final_review,
            }
        except Exception as e:
            ConsoleOutput.error(f"Idle proposal workflow failed: {e}")
            return {"proposal_ok": False, "evaluation_ok": False, "updated": False, "error": str(e)}

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
            return self._structured_tool_result("install_python_package", False, summary="Package name is required.", errors=["Package name is required."])
        requested = f"{package} {'--upgrade' if upgrade else ''}".strip()
        decision = self.execution_policy.evaluate("install_python_package", requested)
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=requested)
            return self._structured_tool_result("install_python_package", False, summary="Execution blocked.", errors=[decision.reason], data={"package": package, "upgrade": bool(upgrade)})
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
            return self._structured_tool_result(
                "install_python_package",
                res.returncode == 0,
                summary=f"Package install {'completed' if res.returncode == 0 else 'failed'}.",
                errors=[] if res.returncode == 0 else [output or f"pip install exited with code {res.returncode}"],
                data=result,
            )
        except Exception as e:
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=requested,
                result=str(e),
                duration_ms=int((time.time() - start_time) * 1000),
            )
            return self._structured_tool_result("install_python_package", False, summary="Package install failed.", errors=[str(e)], data={"package": package, "upgrade": bool(upgrade)})

    def tool_inspect_python_environment(self):
        try:
            return rlm_inspect_python_environment()
        except Exception as e:
            return self._structured_tool_result(
                "inspect_python_environment",
                False,
                summary="Failed to inspect Python environment.",
                errors=[str(e)],
            )

    def tool_list_python_packages(self, limit: int = 500):
        try:
            return rlm_list_python_packages(limit=limit)
        except Exception as e:
            return self._structured_tool_result(
                "list_python_packages",
                False,
                summary="Failed to list Python packages.",
                errors=[str(e)],
                data={"limit": int(limit or 500)},
            )

    def tool_python_symbol_doc(self, name: str, filepath: str = "", root: str = "."):
        try:
            return rlm_python_symbol_doc(name=name, filepath=filepath, root=root)
        except Exception as e:
            return self._structured_tool_result(
                "python_symbol_doc",
                False,
                summary="Failed to inspect Python symbol documentation.",
                errors=[str(e)],
                data={"name": name, "filepath": filepath, "root": root},
            )

    def tool_python_import_graph(self, filepath: str, root: str = "."):
        try:
            return rlm_python_import_graph(filepath=filepath, root=root)
        except Exception as e:
            return self._structured_tool_result(
                "python_import_graph",
                False,
                summary="Failed to build Python import graph.",
                errors=[str(e)],
                data={"filepath": filepath, "root": root},
            )

    def _bg_task_log_path(self, pid: str | int) -> Path:
        BG_TASK_LOG_DIR.mkdir(parents=True, exist_ok=True)
        return BG_TASK_LOG_DIR / f"bg_task_{pid}.log"

    def _recent_user_request_text(self) -> str:
        history = getattr(self.state, "history", []) or []
        for entry in reversed(history[-20:]):
            if str(entry.get("role", "")) != "user":
                continue
            text = str(entry.get("content", "") or "").strip()
            if text:
                return text
        return ""

    def _current_goal_reference(self) -> dict[str, Any]:
        goal = self.current_goal()
        if not goal:
            return {}
        return {
            "id": str(goal.get("id", "") or "").strip(),
            "text": str(goal.get("text", "") or "").strip(),
            "status": str(goal.get("status", "") or "").strip(),
            "next_action": str(goal.get("next_action", "") or "").strip(),
            "verification_target": str(goal.get("verification_target", "") or "").strip(),
            "workspace_path": str(goal.get("workspace_path", "") or "").strip(),
        }

    def _current_spawn_request_context(self) -> dict[str, Any]:
        ctx = copy.deepcopy(getattr(self, "current_request_context", {}) or {})
        request_text = str(ctx.get("user_input", "") or "").strip()
        if not request_text:
            request_text = self._recent_user_request_text()
        request_signature = str(ctx.get("request_signature", "") or "").strip()
        if not request_signature and request_text:
            request_signature = self._progress_request_signature(request_text)
        try:
            heartbeat = self.runtime_heartbeat()
        except Exception:
            heartbeat = {}
        return {
            "request_signature": request_signature,
            "request_excerpt": request_text[:240],
            "turn_counter": int(ctx.get("turn_counter", getattr(self, "turn_counter", 0)) or 0),
            "last_user_input_at": float(heartbeat.get("last_user_input_at", 0.0) or 0.0),
        }

    def _build_task_spawn_context(self, *, source: str, actor: str = "agent", source_id: str = "",
                                  goal: dict[str, Any] | None = None, parent: dict[str, Any] | None = None) -> dict[str, Any]:
        request_context = self._current_spawn_request_context()
        spawned_by = {
            "actor": actor,
            "source": source,
            "source_id": str(source_id or "").strip(),
            "request_signature": request_context.get("request_signature", ""),
            "request_excerpt": request_context.get("request_excerpt", ""),
            "turn_counter": int(request_context.get("turn_counter", 0) or 0),
            "spawned_at": datetime.now().isoformat(),
        }
        if parent:
            parent_pid = str(parent.get("pid", "") or "").strip()
            if parent_pid:
                spawned_by["parent_pid"] = parent_pid
        return {
            "spawned_by": spawned_by,
            "goal": copy.deepcopy(goal) if isinstance(goal, dict) else self._current_goal_reference(),
        }

    def _workspace_lock_area(self, *, work_dir: str = ".", goal: dict[str, Any] | None = None) -> str:
        if isinstance(goal, dict):
            workspace_path = str(goal.get("workspace_path", "") or "").strip()
            if workspace_path:
                return str(Path(workspace_path).resolve())
        return str(Path(work_dir or ".").resolve())

    def _workspace_paths_overlap(self, left: str, right: str) -> bool:
        try:
            left_path = os.path.normcase(str(Path(left).resolve()))
            right_path = os.path.normcase(str(Path(right).resolve()))
            common = os.path.commonpath([left_path, right_path])
            return common in {left_path, right_path}
        except Exception:
            return str(left).strip() == str(right).strip()

    def _active_workspace_lock(self, area: str, *, holder: str = "") -> dict[str, Any] | None:
        if not hasattr(self.state, "workspace_locks"):
            return None
        now_iso = datetime.now().isoformat()
        active_locks: list[dict[str, Any]] = []
        conflict: dict[str, Any] | None = None
        for lock in self.state.workspace_locks():
            payload = asdict(lock)
            expires_at = str(payload.get("expires_at", "") or "").strip()
            if expires_at and expires_at <= now_iso:
                continue
            active_locks.append(payload)
            if holder and str(payload.get("holder", "") or "").strip() == holder:
                continue
            if self._workspace_paths_overlap(str(payload.get("area", "") or ""), area):
                conflict = payload
        if len(active_locks) != len(self.state.workspace_locks()):
            self.state.remember(WORKSPACE_LOCKS_KEY, active_locks)
        return conflict

    def _acquire_workspace_lock(self, area: str, holder: str, *, goal: dict[str, Any] | None = None,
                                reason: str = "", metadata: dict[str, Any] | None = None,
                                ttl_seconds: int = 900) -> tuple[str, dict[str, Any] | None]:
        normalized_area = str(Path(area).resolve())
        conflict = self._active_workspace_lock(normalized_area, holder=holder)
        if conflict:
            return "", conflict
        lock = self.state.acquire_workspace_lock(
            normalized_area,
            holder,
            goal_id=str((goal or {}).get("id", "") or "").strip(),
            reason=reason,
            metadata=copy.deepcopy(metadata or {}),
            ttl_seconds=ttl_seconds,
        )
        return str(lock.id), None

    def _release_workspace_lock(self, lock_id: str):
        if lock_id and hasattr(self.state, "release_workspace_lock"):
            self.state.release_workspace_lock(lock_id)

    def _default_task_lifecycle_policy(self, *, restart_supported: bool,
                                       kill_mode: str = "graceful_then_force",
                                       restart_mode: str = "manual") -> dict[str, Any]:
        return {
            "kill": {
                "mode": kill_mode,
                "force_supported": True,
                "default_force": False,
            },
            "restart": {
                "supported": bool(restart_supported),
                "mode": restart_mode,
                "attempts": 0,
            },
        }

    def _default_ready_condition(self, *, marker: str = "", timeout_seconds: int = 0,
                                 kind: str = "output_marker", path: str = "") -> dict[str, Any]:
        marker_text = str(marker or "").strip()
        ready_kind = kind if kind == "result_file" else ("output_marker" if marker_text else "none")
        status = "pending" if ready_kind in {"output_marker", "result_file"} and (marker_text or ready_kind == "result_file") else "not_configured"
        return {
            "kind": ready_kind,
            "marker": marker_text,
            "path": str(path or "").strip(),
            "status": status,
            "timeout_seconds": int(timeout_seconds or 0),
            "observed_at": "",
        }

    def _python_bg_preamble(self) -> str:
        return "import sys, os, time\ntry:\n    import flexi\nexcept Exception:\n    pass\n\n"

    def _recover_python_bg_source(self, code: str) -> str:
        text = str(code or "")
        prefix = self._python_bg_preamble()
        if text.startswith(prefix):
            return text[len(prefix):]
        return text

    def _normalize_bg_task_record(self, pid: str | int, info: dict[str, Any] | None) -> dict[str, Any]:
        record = copy.deepcopy(info or {})
        pid_str = str(pid or record.get("pid", "") or "").strip()
        record["pid"] = pid_str
        log_path = str(record.get("log_path") or record.get("expected_log_path") or self._bg_task_log_path(pid_str or "unknown"))
        record["log_path"] = log_path
        record["expected_log_path"] = str(record.get("expected_log_path") or log_path)
        record["working_directory"] = str(record.get("working_directory") or ".")
        record["type"] = str(record.get("type", "") or "").strip()
        goal = record.get("goal")
        record["goal"] = copy.deepcopy(goal) if isinstance(goal, dict) else {}
        spawned_by = record.get("spawned_by")
        if isinstance(spawned_by, dict):
            record["spawned_by"] = copy.deepcopy(spawned_by)
        else:
            record["spawned_by"] = {
                "actor": "unknown",
                "source": "legacy_task",
                "source_id": pid_str,
                "request_signature": "",
                "request_excerpt": "",
                "turn_counter": 0,
                "spawned_at": "",
            }

        launch_spec = copy.deepcopy(record.get("launch_spec") or {})
        if not launch_spec:
            launch_spec = {
                "tool": "spawn_background" if record.get("type") == "shell" else "run_python_bg" if record.get("type") == "python_bg" else "",
                "cmd": str(record.get("cmd", "") or ""),
                "script_path": str(record.get("script_path", "") or ""),
                "timeout_seconds": int(record.get("timeout_seconds", 0) or 0),
                "stop_marker": str(record.get("stop_marker", "") or ""),
            }
        launch_spec.setdefault("cmd", str(record.get("cmd", "") or ""))
        launch_spec.setdefault("script_path", str(record.get("script_path", "") or ""))
        launch_spec.setdefault("timeout_seconds", int(record.get("timeout_seconds", 0) or 0))
        launch_spec.setdefault("stop_marker", str(record.get("stop_marker", "") or ""))
        record["launch_spec"] = launch_spec

        ready_condition = record.get("ready_condition")
        if isinstance(ready_condition, dict):
            ready = copy.deepcopy(ready_condition)
        else:
            ready = self._default_ready_condition(
                marker=str(launch_spec.get("stop_marker", "") or ""),
                timeout_seconds=int(launch_spec.get("timeout_seconds", 0) or 0),
            )
        ready.setdefault("kind", "output_marker" if ready.get("marker") else "none")
        ready.setdefault("marker", str(launch_spec.get("stop_marker", "") or ""))
        ready.setdefault("path", "")
        ready.setdefault("status", "pending" if ready.get("marker") else "not_configured")
        ready.setdefault("timeout_seconds", int(launch_spec.get("timeout_seconds", 0) or 0))
        ready.setdefault("observed_at", "")
        record["ready_condition"] = ready

        lifecycle_policy = record.get("lifecycle_policy")
        if isinstance(lifecycle_policy, dict):
            policy = copy.deepcopy(lifecycle_policy)
        else:
            policy = self._default_task_lifecycle_policy(restart_supported=record.get("type") in {"shell", "python_bg"})
        policy.setdefault("kill", {})
        policy.setdefault("restart", {})
        policy["kill"].setdefault("mode", "graceful_then_force")
        policy["kill"].setdefault("force_supported", True)
        policy["kill"].setdefault("default_force", False)
        policy["restart"].setdefault("supported", record.get("type") in {"shell", "python_bg"})
        policy["restart"].setdefault("mode", "manual")
        policy["restart"].setdefault("attempts", 0)
        record["lifecycle_policy"] = policy
        return record

    def tool_get_bg_task_details(self, pid: str = ""):
        active = self.state.active_processes
        if pid:
            info = active.get(str(pid))
            if not info:
                return self._structured_tool_result("get_bg_task_details", False, summary="Background task not found.", errors=[f"No background task found for PID {pid}"], data={"pid": str(pid)})
            task = self._normalize_bg_task_record(pid, info)
            return self._structured_tool_result("get_bg_task_details", True, summary=f"Background task details for PID {pid}.", data={"pid": str(pid), "task": task})
        tasks = [self._normalize_bg_task_record(pid_str, info) for pid_str, info in sorted(active.items())]
        return self._structured_tool_result("get_bg_task_details", True, summary=f"Listed {len(active)} background task(s).", data={"tasks": tasks})

    def tool_read_bg_task_log(self, pid: str, lines: int = 50):
        pid_str = str(pid)
        info = self.state.active_processes.get(pid_str)
        task = self._normalize_bg_task_record(pid_str, info) if info else None
        log_path = Path(task.get("log_path")) if task else self._bg_task_log_path(pid)
        if not log_path.exists():
            return self._structured_tool_result("read_bg_task_log", False, summary="Background log not found.", errors=[f"No log file found for background task {pid}."], data={"pid": str(pid), "lines": int(lines)})
        try:
            content = log_path.read_text(encoding='utf-8', errors='replace').splitlines()
            tail_lines = content[-max(1, int(lines)):]
            return self._structured_tool_result("read_bg_task_log", True, summary=f"Read {len(tail_lines)} log line(s) for PID {pid}.", data={"pid": str(pid), "lines": tail_lines, "log_path": str(log_path), "task": task})
        except Exception as e:
            return self._structured_tool_result("read_bg_task_log", False, summary="Background log read failed.", errors=[str(e)], data={"pid": str(pid), "log_path": str(log_path)})

    def tool_stop_bg_task(self, pid: str, force: bool = False):
        pid_str = str(pid)
        active = self.state.active_processes
        info = active.get(pid_str)
        if not info:
            return self._structured_tool_result("stop_bg_task", False, summary="Background task not found.", errors=[f"No background task found for PID {pid_str}."], data={"pid": pid_str, "force": bool(force)})
        try:
            task = self._normalize_bg_task_record(pid_str, info)
            if os.name == 'nt':
                cmd = ["taskkill", "/PID", pid_str]
                if force:
                    cmd.append("/F")
                subprocess.run(cmd, capture_output=True, text=True, timeout=20, encoding='utf-8', errors='replace')
            else:
                os.kill(int(pid_str), signal.SIGKILL if force else signal.SIGTERM)
            task["status"] = "stopped"
            task["stopped_at"] = time.time()
            task["lifecycle_policy"]["kill"]["last_requested_force"] = bool(force)
            task["lifecycle_policy"]["kill"]["last_stop_at"] = datetime.now().isoformat()
            self.state.set_active_process(pid_str, task, persist=False)
            self.state.save()
            return self._structured_tool_result("stop_bg_task", True, summary=f"Stopped background task {pid_str}.", data={"pid": pid_str, "force": bool(force), "task": task})
        except Exception as e:
            return self._structured_tool_result("stop_bg_task", False, summary="Failed to stop background task.", errors=[str(e)], data={"pid": pid_str, "force": bool(force)})

    def tool_restart_bg_task(self, pid: str):
        pid_str = str(pid)
        active = self.state.active_processes
        info = active.get(pid_str)
        if not info:
            return self._structured_tool_result("restart_bg_task", False, summary="Background task not found.", errors=[f"No background task found for PID {pid_str}."], data={"pid": pid_str})
        task = self._normalize_bg_task_record(pid_str, info)
        task_type = task.get("type")
        restart_policy = task.get("lifecycle_policy", {}).get("restart", {})
        if not restart_policy.get("supported", False):
            return self._structured_tool_result("restart_bg_task", False, summary="Restart not supported.", errors=[f"Restart not supported for background task type '{task_type}'."], data={"pid": pid_str, "task": task})

        metadata = {
            "spawned_by": self._build_task_spawn_context(
                source="restart_bg_task",
                actor="agent",
                source_id=pid_str,
                goal=task.get("goal", {}),
                parent=task,
            ).get("spawned_by", {}),
            "goal": copy.deepcopy(task.get("goal", {})),
            "ready_condition": copy.deepcopy(task.get("ready_condition", {})),
            "lifecycle_policy": copy.deepcopy(task.get("lifecycle_policy", {})),
            "launch_spec": copy.deepcopy(task.get("launch_spec", {})),
        }
        metadata["lifecycle_policy"].setdefault("restart", {})
        metadata["lifecycle_policy"]["restart"]["attempts"] = int(metadata["lifecycle_policy"]["restart"].get("attempts", 0) or 0) + 1
        metadata["lifecycle_policy"]["restart"]["last_restart_at"] = datetime.now().isoformat()
        metadata["spawned_by"]["restart_of_pid"] = pid_str
        if task_type == "shell":
            self.tool_stop_bg_task(pid_str, force=False)
            launch_spec = task.get("launch_spec", {})
            restarted = self.tool_spawn_background(
                task.get("cmd", ""),
                stop_marker=str(launch_spec.get("stop_marker", "") or "") or None,
                timeout=int(launch_spec.get("timeout_seconds", 30) or 30),
                metadata=metadata,
            )
            restarted_payload = self._parse_tool_result_payload(restarted) or {"raw": restarted}
            return self._structured_tool_result(
                "restart_bg_task",
                bool(restarted_payload.get("ok", False)),
                summary="Restarted shell background task." if restarted_payload.get("ok", False) else "Failed to restart shell background task.",
                errors=restarted_payload.get("errors", []),
                data={"pid": pid_str, "previous_task": task, "restart_result": restarted_payload},
            )
        if task_type == "python_bg" and task.get("script_path"):
            try:
                code = Path(task["script_path"]).read_text(encoding='utf-8', errors='replace')
                code = self._recover_python_bg_source(code)
            except Exception as e:
                return self._structured_tool_result("restart_bg_task", False, summary="Failed to reload background script.", errors=[str(e)], data={"pid": pid_str, "script_path": task.get("script_path")})
            self.tool_stop_bg_task(pid_str, force=False)
            restarted = self.tool_run_python_bg(code, metadata=metadata)
            restarted_payload = self._parse_tool_result_payload(restarted) or {"raw": restarted}
            return self._structured_tool_result(
                "restart_bg_task",
                bool(restarted_payload.get("ok", False)),
                summary="Restarted python background task." if restarted_payload.get("ok", False) else "Failed to restart python background task.",
                errors=restarted_payload.get("errors", []),
                data={"pid": pid_str, "previous_task": task, "restart_result": restarted_payload},
            )
        return self._structured_tool_result("restart_bg_task", False, summary="Restart not supported.", errors=[f"Restart not supported for background task type '{task_type}'."], data={"pid": pid_str, "task": task})

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
    def tool_project_memory(self):
        payload = self._project_memory_payload()
        return self._structured_tool_result("project_memory", True, summary="Retrieved project memory.", data=payload)

    def tool_task_memory(self):
        payload = self._task_memory_payload()
        return self._structured_tool_result("task_memory", True, summary="Retrieved task memory.", data=payload)

    def tool_failure_memory(self):
        payload = self._failure_memory_payload()
        return self._structured_tool_result("failure_memory", True, summary="Retrieved failure memory.", data=payload)

    def tool_remember(self, tag: str, content: str):
        # Legacy compat: Use KV cache as structured memory
        current = self.state.recall(tag) or []
        if not isinstance(current, list): current = [str(current)]
        current.append(str(content))
        self.state.remember(tag, current)
        return self._structured_tool_result("remember", True, summary=f"Stored memory under tag '{tag}'.", data={"tag": tag, "item_count": len(current)})

    def tool_recall(self, tag: str):
        lowered = str(tag or "").strip().lower()
        if lowered in {"project", "project_memory"}:
            return self.tool_project_memory()
        if lowered in {"task", "task_memory"}:
            return self.tool_task_memory()
        if lowered in {"failure", "failure_memory"}:
            return self.tool_failure_memory()
        items = self.state.recall(tag)
        if not items:
            return self._structured_tool_result("recall", False, summary="No memory found.", errors=[f"No memory found for tag '{tag}'"], data={"tag": tag})
        if isinstance(items, list):
            return self._structured_tool_result("recall", True, summary=f"Recalled {len(items)} memory item(s).", data={"tag": tag, "items": [str(i) for i in items]})
        return self._structured_tool_result("recall", True, summary="Recalled memory value.", data={"tag": tag, "items": [str(items)]})

    def tool_search_memory(self, query: str):
        results = []
        results.extend(self._search_typed_memory(query))
        mem = self.state.memory
        for tag, items in mem.items():
            if tag in {"active_processes", PROJECT_MEMORY_KEY, TASK_MEMORY_KEY, FAILURE_MEMORY_KEY}:
                continue
            if isinstance(items, list):
                for item in items:
                    if query.lower() in str(item).lower():
                        results.append(f"[{tag}] {item}")
            elif query.lower() in str(items).lower():
                results.append(f"[{tag}] {items}")
        return self._structured_tool_result("search_memory", True, summary=f"Found {len(results)} matching memory entr{'y' if len(results) == 1 else 'ies' }.", data={"query": query, "matches": results[:80]}, warnings=[] if results else [f"No memories found matching '{query}'"])

    def tool_save_skill(self, name: str, code: str):
        path = SKILLS_DIR / f"{name}.py"
        path.write_text(code, encoding="utf-8")
        return self._structured_tool_result("save_skill", True, summary=f"Skill '{name}' saved.", data={"name": name, "path": str(path), "bytes_written": len(code.encode('utf-8'))})

    def tool_load_skill(self, name: str, env: dict):
        path = SKILLS_DIR / f"{name}.py"
        if not path.exists():
            return self._structured_tool_result("load_skill", False, summary="Skill not found.", errors=[f"Skill '{name}' not found."], data={"name": name, "path": str(path)})
        # We execute the skill code directly into the current environment
        exec(path.read_text(encoding="utf-8"), env, env) 
        return self._structured_tool_result("load_skill", True, summary=f"Skill '{name}' loaded.", data={"name": name, "path": str(path)})

    def tool_validate_python(self, filepath: str = "", code: str = ""):
        return rlm_validate_python(filepath=filepath, code=code)

    def tool_validate_json(self, filepath: str = "", content: str = ""):
        return rlm_validate_json(filepath=filepath, content=content)

    def tool_run_tests(self, command: str = ""):
        test_command = command.strip()
        if not test_command:
            goal = self.current_goal()
            if goal and goal.get("verification_target"):
                test_command = str(goal.get("verification_target") or "").strip()
        if not test_command:
            test_candidates = list(Path(".").glob("test_*.py")) + list(Path("tests").glob("**/test*.py")) if Path("tests").exists() else list(Path(".").glob("test_*.py"))
            if not test_candidates:
                return self._structured_tool_result("run_tests", False, summary="No tests found.", errors=["No tests found and no command provided."])
            test_command = f'"{sys.executable}" -m unittest discover -v'
        if "pytest" in test_command.lower():
            try:
                import shlex

                pytest_args = shlex.split(test_command, posix=os.name != "nt")
                if len(pytest_args) >= 3 and pytest_args[1:3] == ["-m", "pytest"]:
                    pytest_args[0] = pytest_args[0].strip('"')
                    env = os.environ.copy()
                    env["PYTEST_DISABLE_PLUGIN_AUTOLOAD"] = "1"
                    completed = subprocess.run(
                        pytest_args,
                        capture_output=True,
                        text=True,
                        timeout=180,
                        encoding="utf-8",
                        errors="replace",
                        env=env,
                    )
                    result = self._structured_tool_result(
                        "bash",
                        completed.returncode == 0,
                        summary="Command completed." if completed.returncode == 0 else "Command failed.",
                        errors=[] if completed.returncode == 0 else [completed.stderr.strip() or completed.stdout.strip() or f"Command returned exit code {completed.returncode}."],
                        data={
                            "command": test_command,
                            "executor": "subprocess",
                            "translated_command": test_command,
                            "translation_note": "pytest run with PYTEST_DISABLE_PLUGIN_AUTOLOAD=1",
                            "returncode": completed.returncode,
                            "stdout": completed.stdout or "",
                            "stderr": completed.stderr or "",
                        },
                    )
                else:
                    result = self.run_bash(test_command)
            except Exception as e:
                result = self._structured_tool_result(
                    "bash",
                    False,
                    summary="Command failed.",
                    errors=[str(e)],
                    data={"command": test_command, "executor": "subprocess", "translated_command": test_command},
                )
        else:
            result = self.run_bash(test_command)
        verification = self.verify_and_report(result, context=f"tests:{test_command}")
        self._run_reviewer_pass("tests", test_command, result, verification=verification)
        self.state.set_runtime_value(
            LAST_TEST_RUN_KEY,
            {
                "timestamp": time.time(),
                "command": test_command,
                "success": bool(verification.get("success", False)),
                "summary": str(verification.get("summary", "") or "").strip(),
                "errors": [str(item).strip() for item in verification.get("errors", []) if str(item).strip()][:10],
                "goal": self._current_goal_reference(),
                "result": copy.deepcopy(self._parse_tool_result_payload(result) or {"raw": str(result)[:4000]}),
            },
            persist=True,
        )
        return self._structured_tool_result(
            "run_tests",
            verification.get("success", False),
            summary=verification.get("summary", ""),
            errors=verification.get("errors", []),
            data={
                "command": test_command,
                "result": self._parse_tool_result_payload(result) or {"raw": result[:4000]},
                "verification": verification,
            },
        )

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
                        except Exception as e:
                            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="StatusProbe.get_status.json_parse", code=ErrorCode.IO_ERROR)
                            return {{"error": "Invalid JSON status"}}
            except queue.Empty:
                pass
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
                return self._structured_tool_result("run_verification", False, summary="Target script missing.", errors=[f"Target script '{target_script}' does not exist. Cannot verify."])

            res = self.run_bash(f"python \"{wrapper_path}\"")
            verification = self.verify_and_report(res, context=f"verify:{target_script}")
            return self._structured_tool_result(
                "run_verification",
                verification.get("success", False),
                summary=verification.get("summary", ""),
                errors=verification.get("errors", []),
                data={"target_script": target_script, "runner_result": self._parse_tool_result_payload(res) or {"raw": res[:4000]}, "verification": verification},
            )
        except Exception as e:
            ErrorHandler.log(e, context="tool_run_verification")
            return self._structured_tool_result("run_verification", False, summary="Verification failed.", errors=[str(e)], data={"target_script": target_script})

    def tool_see_image(self, image_path: str, question: str = "Describe this image."):
        """Analyzes an image file using the vision capabilities of the LLM."""
        path = Path(image_path)
        if not path.exists():
            return self._structured_tool_result("see_image", False, summary="Image file not found.", errors=[f"Image file not found: {image_path}"], data={"image_path": image_path})
        
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
            analysis = res['choices'][0]['message']['content']
            return self._structured_tool_result("see_image", True, summary=f"Image analyzed: {path.name}", data={"image_path": str(path), "question": question, "analysis": analysis})
        except Exception as e:
            ErrorHandler.log(e, context="tool_see_image")
            return self._structured_tool_result("see_image", False, summary="Vision error.", errors=[str(e)], data={"image_path": image_path, "question": question})

    def tool_list_windows(self, filter_text: str = None):
        """Lists open windows (Windows mostly). Returns JSON. Filter by title optional."""
        
        deps = SystemAutomation.check_dependencies()
        if deps:
            return self._structured_tool_result("list_windows", False, summary="Missing dependencies.", errors=[f"Missing dependencies: {', '.join(deps)}"], data={"filter_text": filter_text or ""})

        try:
            windows = SystemAutomation.get_open_windows(filter_text)
            return self._structured_tool_result("list_windows", True, summary=f"Listed {len(windows)} window(s).", data={"filter_text": filter_text or "", "windows": windows})
        except Exception as e:
            ErrorHandler.log(e, context="tool_list_windows")
            return self._structured_tool_result("list_windows", False, summary="Failed to list windows.", errors=[str(e)], data={"filter_text": filter_text or ""})

    def tool_capture_window(self, query: str, output_path: str = None):
        """Captures a screenshot of a window by title (query). Returns path."""
        # Backwards-compatible simple capture (Windows-focused)
        if os.name != 'nt':
            return self._structured_tool_result("capture_window", False, summary="Tool only available on Windows.", errors=["Tool only available on Windows."], data={"query": query, "path": output_path or ""})
        
        final_path = output_path if output_path else f"window_capture_{int(time.time())}.png"
        
        try:
            res = SystemAutomation.capture_window(query, final_path)
            if res == "Success":
                 self.must_wait_for_observation = True
                 return self._structured_tool_result("capture_window", True, summary="Window capture saved.", data={"query": query, "path": final_path})
            return self._structured_tool_result("capture_window", False, summary="Window capture failed.", errors=[str(res)], data={"query": query, "path": final_path})
        except Exception as e:
            ErrorHandler.log(e, context="tool_capture_window")
            return self._structured_tool_result("capture_window", False, summary="Window capture failed.", errors=[str(e)], data={"query": query, "path": final_path})

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
                    return self._structured_tool_result("capture_window_advanced", True, summary="Window capture saved.", data={"title": title or "", "process": process or "", "path": final_path, "message": msg, "base64": b64_str if print_base64 else None})
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
                    return self._structured_tool_result("capture_window_advanced", False, summary="Native capture failed.", errors=[str(res)], data={"title": title or "", "process": process or "", "path": None, "message": msg})

            return self._structured_tool_result("capture_window_advanced", False, summary="Capture not supported on this platform natively.", errors=["Capture not supported on this platform natively."], data={"title": title or "", "process": process or "", "path": None})

        except Exception as e:
            ErrorHandler.log(e, context="tool_capture_window_advanced")
            return self._structured_tool_result("capture_window_advanced", False, summary="Capture failed.", errors=[str(e)], data={"title": title or "", "process": process or "", "path": None})

    def tool_capture_screen(self, output_path: str = None):
        """Captures the entire screen and returns the saved path."""
        final_path = output_path if output_path else f"screen_capture_{int(time.time())}.png"
        try:
            res = SystemAutomation.capture_screen(final_path)
            if res == "Success":
                self.must_wait_for_observation = True
                return self._structured_tool_result("capture_screen", True, summary="Screen capture saved.", data={"path": final_path})
            return self._structured_tool_result("capture_screen", False, summary="Screen capture failed.", errors=[str(res)], data={"path": final_path})
        except Exception as e:
            ErrorHandler.log(e, context="tool_capture_screen")
            return self._structured_tool_result("capture_screen", False, summary="Capture screen failed.", errors=[str(e)], data={"path": final_path})

    def tool_analyze_screen(self, question: str = "What is visible on the screen?", output_path: str = None):
        """Captures the screen and immediately analyzes it with vision."""
        temp_path = output_path if output_path else f"temp_screen_capture_{int(time.time())}.png"
        keep_file = bool(output_path)
        try:
            print(f"{Colors.YELLOW}[Analyze Screen] Capturing full screen...{Colors.ENDC}")
            cap_res = SystemAutomation.capture_screen(temp_path)
            if cap_res != "Success":
                return self._structured_tool_result("analyze_screen", False, summary="Could not capture screen.", errors=[str(cap_res)], data={"path": temp_path, "question": question})

            desc = self.tool_see_image(temp_path, question)

            if not keep_file:
                try:
                    os.remove(temp_path)
                except Exception:
                    pass

            vision_payload = self._parse_tool_result_payload(desc) or {"raw": desc}
            ok = bool(vision_payload.get("ok", False)) if isinstance(vision_payload, dict) else False
            return self._structured_tool_result("analyze_screen", ok, summary="Screen analyzed." if ok else "Screen analysis failed.", errors=vision_payload.get("errors", []) if isinstance(vision_payload, dict) else [], data={"path": temp_path if keep_file else "", "question": question, "vision": vision_payload})
        except Exception as e:
            return self._structured_tool_result("analyze_screen", False, summary="Screen analysis failed.", errors=[str(e)], data={"path": temp_path, "question": question})

    def tool_see_window(self, query: str, question: str = "What is visible in this window?"):
        """Captures a window and immediately analyzes it with vision."""
        temp_path = f"temp_vision_capture_{int(time.time())}.png"
        try:
            print(f"{Colors.YELLOW}[See Window] Capturing '{query}'...{Colors.ENDC}")
            cap_res = SystemAutomation.capture_window(query, temp_path)
            if cap_res != "Success":
                return self._structured_tool_result("see_window", False, summary="Could not capture window.", errors=[str(cap_res)], data={"query": query, "question": question})
            
            desc = self.tool_see_image(temp_path, question)
            
            # Clean up temp file
            try: os.remove(temp_path)
            except: pass
            
            vision_payload = self._parse_tool_result_payload(desc) or {"raw": desc}
            ok = bool(vision_payload.get("ok", False)) if isinstance(vision_payload, dict) else False
            return self._structured_tool_result("see_window", ok, summary="Window analyzed." if ok else "Window analysis failed.", errors=vision_payload.get("errors", []) if isinstance(vision_payload, dict) else [], data={"query": query, "question": question, "vision": vision_payload})
        except Exception as e:
            return self._structured_tool_result("see_window", False, summary="Window analysis failed.", errors=[str(e)], data={"query": query, "question": question})

    def tool_see_screen(self, question: str = "What is visible on the screen?"):
        """Captures the entire screen and immediately analyzes it with vision."""
        return self.tool_analyze_screen(question)

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
                    note = f"Truncated list: showing first 100 windows."
                else:
                    note = ""
                
                warnings = [note] if note else []
                return self._structured_tool_result("list_windows_advanced", True, summary=f"Listed {len(wins)} window(s).", data={"filter_text": filter_text or "", "format": format, "windows": wins}, warnings=warnings)

            return self._structured_tool_result("list_windows_advanced", False, summary="Required dependencies are missing.", errors=["Required dependencies for native window listing are missing."], data={"filter_text": filter_text or "", "format": format})
        except Exception as e:
            ErrorHandler.log(e, context="tool_list_windows_advanced")
            return self._structured_tool_result("list_windows_advanced", False, summary="Failed to list windows.", errors=[str(e)], data={"filter_text": filter_text or "", "format": format})


    def tool_get_active_terminal(self):
        """Returns metadata about the active terminal environment."""
        info = get_terminal_environment()
        return self._structured_tool_result("get_active_terminal", True, summary="Collected active terminal metadata.", data=info)

    def tool_list_processes(self, filter_text: str = "", limit: int = 100):
        """Lists running processes with a bounded result size."""
        filter_value = str(filter_text or "").strip().lower()
        try:
            capped_limit = max(1, min(int(limit or 100), 200))
        except Exception:
            capped_limit = 100

        processes = []
        warnings = []
        try:
            import psutil  # type: ignore

            for proc in psutil.process_iter(["pid", "name", "exe", "cmdline"]):
                try:
                    info = proc.info or {}
                except Exception:
                    continue
                name = str(info.get("name") or "").strip()
                exe = str(info.get("exe") or "").strip()
                cmdline_parts = info.get("cmdline") or []
                cmdline = " ".join(str(part) for part in cmdline_parts if str(part or "").strip())
                haystack = " ".join(part for part in [name, exe, cmdline] if part).lower()
                if filter_value and filter_value not in haystack:
                    continue
                processes.append({
                    "pid": int(info.get("pid") or 0),
                    "name": name,
                    "exe": exe,
                    "cmdline": cmdline,
                })
        except Exception:
            command = ["tasklist", "/FO", "CSV"] if os.name == "nt" else ["ps", "-eo", "pid=,comm=,args="]
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=15,
            )
            if completed.returncode != 0:
                stderr_text = str(completed.stderr or "").strip()
                return self._structured_tool_result(
                    "list_processes",
                    False,
                    summary="Failed to list processes.",
                    errors=[stderr_text or "Process listing command failed."],
                    data={"filter_text": filter_text or "", "limit": capped_limit},
                )
            output_lines = [line.strip() for line in str(completed.stdout or "").splitlines() if line.strip()]
            if os.name == "nt":
                reader = csv.reader(output_lines)
                next(reader, None)
                for row in reader:
                    if len(row) < 2:
                        continue
                    name = str(row[0] or "").strip()
                    pid_text = str(row[1] or "0").strip()
                    haystack = name.lower()
                    if filter_value and filter_value not in haystack:
                        continue
                    try:
                        pid_value = int(pid_text)
                    except Exception:
                        pid_value = 0
                    processes.append({
                        "pid": pid_value,
                        "name": name,
                        "exe": "",
                        "cmdline": "",
                    })
            else:
                for line in output_lines:
                    parts = line.split(None, 2)
                    if len(parts) < 2:
                        continue
                    pid_text = str(parts[0] or "0").strip()
                    name = str(parts[1] or "").strip()
                    cmdline = str(parts[2] or "").strip() if len(parts) > 2 else ""
                    haystack = f"{name} {cmdline}".lower()
                    if filter_value and filter_value not in haystack:
                        continue
                    try:
                        pid_value = int(pid_text)
                    except Exception:
                        pid_value = 0
                    processes.append({
                        "pid": pid_value,
                        "name": name,
                        "exe": "",
                        "cmdline": cmdline,
                    })

        total_count = len(processes)
        if total_count > capped_limit:
            warnings.append(f"Truncated process list to first {capped_limit} entries.")
            processes = processes[:capped_limit]
        return self._structured_tool_result(
            "list_processes",
            True,
            summary=f"Listed {len(processes)} process(es).",
            data={"filter_text": filter_text or "", "limit": capped_limit, "total": total_count, "processes": processes},
            warnings=warnings,
        )

    def tool_get_software_versions(self, programs: list[str] | None = None):
        """Collects versions for a bounded set of common developer tools."""
        requested = programs if isinstance(programs, list) and programs else [
            "python",
            "py",
            "git",
            "node",
            "npm",
            "pip",
        ]
        results = []
        for program in requested[:20]:
            name = str(program or "").strip()
            if not name:
                continue
            executable = shutil.which(name)
            if not executable:
                results.append({"program": name, "found": False, "version": "", "path": ""})
                continue
            version_text = ""
            for args in ([name, "--version"], [name, "-V"]):
                try:
                    completed = subprocess.run(
                        args,
                        capture_output=True,
                        text=True,
                        encoding="utf-8",
                        errors="replace",
                        timeout=10,
                    )
                except Exception:
                    continue
                output = str(completed.stdout or completed.stderr or "").strip()
                if completed.returncode == 0 and output:
                    version_text = output.splitlines()[0].strip()
                    break
            results.append({
                "program": name,
                "found": True,
                "version": version_text,
                "path": executable,
            })
        return self._structured_tool_result(
            "get_software_versions",
            True,
            summary=f"Collected version info for {len(results)} program(s).",
            data={"programs": results},
        )

    def tool_find_consuming_port(self, port: int):
        """Finds which PID is holding a port and returns details."""
        result = SystemAutomation.find_consuming_port(port)
        return self._structured_tool_result("find_consuming_port", "error" not in str(result).lower() and "no process found" not in str(result).lower(), summary=f"Port inspection for {port} completed.", errors=[] if "error" not in str(result).lower() else [str(result)], data={"port": int(port), "result": str(result)}, warnings=[str(result)] if "no process found" in str(result).lower() else [])

    @ErrorHandler.handle(severity=ErrorSeverity.CRITICAL, code=ErrorCode.EXEC_ERROR)
    def tool_spawn_background(self, cmd: str, stop_marker: str = None, timeout: int = 30, metadata: dict[str, Any] | None = None):
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
            return self._structured_tool_result("spawn_background", False, summary="Execution blocked.", errors=[decision.reason], data={"cmd": cmd, "stop_marker": stop_marker})

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
            pid_str = str(p.pid)
            spawn_meta = metadata or {}
            default_context = self._build_task_spawn_context(source="spawn_background", actor="agent", source_id=str(p.pid))
            task_record = {
                "pid": pid_str,
                "cmd": cmd,
                "start_time": time.time(),
                "type": "shell",
                "status": "running",
                "log_path": str(log_path),
                "expected_log_path": str(spawn_meta.get("expected_log_path") or log_path),
                "working_directory": decision.isolation_rules.get("working_directory", "."),
                "spawned_by": copy.deepcopy(spawn_meta.get("spawned_by") or default_context.get("spawned_by", {})),
                "goal": copy.deepcopy(spawn_meta.get("goal") or default_context.get("goal", {})),
                "ready_condition": copy.deepcopy(
                    spawn_meta.get("ready_condition")
                    or self._default_ready_condition(marker=stop_marker or "", timeout_seconds=decision.timeout_seconds)
                ),
                "lifecycle_policy": copy.deepcopy(
                    spawn_meta.get("lifecycle_policy")
                    or self._default_task_lifecycle_policy(restart_supported=True)
                ),
                "launch_spec": copy.deepcopy(
                    spawn_meta.get("launch_spec")
                    or {
                        "tool": "spawn_background",
                        "cmd": cmd,
                        "timeout_seconds": decision.timeout_seconds,
                        "stop_marker": stop_marker or "",
                    }
                ),
            }
            
            # Register in state
            self.state.set_active_process(pid_str, task_record, persist=False)
            self.state.save()
            
            if not stop_marker:
                msg = f"Started background process with PID {p.pid}."
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
                    except Exception as e:
                        ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="tool_spawn_background.drain", code=ErrorCode.IO_ERROR)
                threading.Thread(target=drain, args=(p,), daemon=True).start()
                task_record = self._normalize_bg_task_record(pid_str, self.state.active_processes.get(pid_str))
                return self._structured_tool_result("spawn_background", True, summary=msg, data={"pid": p.pid, "cmd": cmd, "status": "running", "log_path": str(log_path), "stop_marker": stop_marker, "task": task_record})
            
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
                        msg = f"Process reached stop marker '{stop_marker}'."
                        self.tool_remember("processes", f"Spawned '{cmd}' - Ready seen at {time.ctime()}")
                        self.state.log_event("system", f"Background process '{cmd}' reached marker '{stop_marker}'.")
                        task_record = self._normalize_bg_task_record(pid_str, self.state.active_processes.get(pid_str))
                        task_record["ready_condition"]["status"] = "observed"
                        task_record["ready_condition"]["observed_at"] = datetime.now().isoformat()
                        self.state.set_active_process(pid_str, task_record, persist=False)
                        self.state.save()
                        result = self.execution_policy.trim_output(decision, "Success: Process reached marker. Last few lines:\n" + "\n".join(captured[-5:]))
                        self.execution_policy.audit(
                            decision,
                            action="finish",
                            status="completed",
                            payload=cmd,
                            result=result,
                            duration_ms=int((time.time() - start_time) * 1000),
                            extra={"pid": p.pid, "stop_marker": stop_marker, "log_path": str(log_path)},
                        )
                        return self._structured_tool_result("spawn_background", True, summary=msg, data={"pid": p.pid, "cmd": cmd, "status": "running", "stop_marker": stop_marker, "log_path": str(log_path), "output": result, "task": task_record})
            
            result = f"Started background process (PID {p.pid}), but marker '{stop_marker}' was not seen in {decision.timeout_seconds}s. It continues to run."
            task_record = self._normalize_bg_task_record(pid_str, self.state.active_processes.get(pid_str))
            task_record["ready_condition"]["status"] = "timeout"
            self.state.set_active_process(pid_str, task_record, persist=False)
            self.state.save()
            self.execution_policy.audit(
                decision,
                action="finish",
                status="completed",
                payload=cmd,
                result=result,
                duration_ms=int((time.time() - start_time) * 1000),
                extra={"pid": p.pid, "stop_marker": stop_marker, "log_path": str(log_path)},
            )
            return self._structured_tool_result("spawn_background", True, summary="Background process started without observing stop marker.", data={"pid": p.pid, "cmd": cmd, "status": "running", "stop_marker": stop_marker, "log_path": str(log_path), "output": result, "task": task_record})
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
            return self._structured_tool_result("spawn_background", False, summary="Background spawn failed.", errors=[str(e)], data={"cmd": cmd, "stop_marker": stop_marker, "log_path": str(log_path)})

    @ErrorHandler.handle(severity=ErrorSeverity.CRITICAL, code=ErrorCode.EXEC_ERROR)
    def tool_run_python_bg(self, code: str, metadata: dict[str, Any] | None = None):
        """Writes Python code to a temp file and runs it in a detached background process.
        Returns the PID. This is safer for unstable scripts."""
        decision = self.execution_policy.evaluate(
            "run_python_bg",
            code,
            active_background_processes=len(self.state.active_processes),
        )
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=code)
            return self._structured_tool_result("run_python_bg", False, summary="Execution blocked.", errors=[decision.reason])

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=code)
        try:
            ts = int(time.time())
            task_dir = Path("temp_tasks")
            task_dir.mkdir(exist_ok=True)
            script_path = task_dir / f"task_{ts}.py"
            
            # Add some preamble imports to help standalone scripts
            safe_code = self._python_bg_preamble() + code
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
            spawn_meta = metadata or {}
            default_context = self._build_task_spawn_context(source="run_python_bg", actor="agent", source_id=str(p.pid))
            task_record = {
                "pid": str(p.pid),
                "cmd": f"python {script_path.name}",
                "start_time": time.time(),
                "type": "python_bg",
                "script_path": str(script_path),
                "status": "running",
                "log_path": str(log_path),
                "expected_log_path": str(spawn_meta.get("expected_log_path") or log_path),
                "working_directory": decision.isolation_rules.get("working_directory", "."),
                "spawned_by": copy.deepcopy(spawn_meta.get("spawned_by") or default_context.get("spawned_by", {})),
                "goal": copy.deepcopy(spawn_meta.get("goal") or default_context.get("goal", {})),
                "ready_condition": copy.deepcopy(
                    spawn_meta.get("ready_condition")
                    or self._default_ready_condition(marker="", timeout_seconds=0)
                ),
                "lifecycle_policy": copy.deepcopy(
                    spawn_meta.get("lifecycle_policy")
                    or self._default_task_lifecycle_policy(restart_supported=True)
                ),
                "launch_spec": copy.deepcopy(
                    spawn_meta.get("launch_spec")
                    or {
                        "tool": "run_python_bg",
                        "cmd": cmd,
                        "script_path": str(script_path),
                        "timeout_seconds": decision.timeout_seconds,
                        "stop_marker": "",
                        "code_sha256": hashlib.sha256(code.encode("utf-8")).hexdigest()[:16],
                    }
                ),
            }
            
            # Register
            self.state.set_active_process(str(p.pid), task_record, persist=False)
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
                except Exception as e:
                    ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="tool_run_python_bg.drain", code=ErrorCode.IO_ERROR)
            threading.Thread(target=drain, args=(p,), daemon=True).start()
            result = f"Started Python background task PID {p.pid}."
            self.execution_policy.audit(
                decision,
                action="finish",
                status="completed",
                payload=code,
                result=result,
                duration_ms=int((time.time() - start_time) * 1000),
                extra={"pid": p.pid, "script_path": str(script_path), "log_path": str(log_path)},
            )
            task_record = self._normalize_bg_task_record(str(p.pid), self.state.active_processes.get(str(p.pid)))
            return self._structured_tool_result("run_python_bg", True, summary=result, data={"pid": p.pid, "script_path": str(script_path), "status": "running", "log_path": str(log_path), "task": task_record})
        except Exception as e:
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=code,
                result=str(e),
                duration_ms=int((time.time() - start_time) * 1000),
            )
            return self._structured_tool_result("run_python_bg", False, summary="Failed to spawn background python.", errors=[str(e)])

    def tool_check_bg_tasks(self, clear_finished: bool = True):
        """Checks the status of all registered background processes."""
        active = self.state.active_processes
        if not active:
            return self._structured_tool_result("check_bg_tasks", True, summary="No background tasks registered.", data={"tasks": []})
        
        report = []
        to_remove = []
        
        try:
            import psutil
            for pid_str, info in active.items():
                pid = int(pid_str)
                task = self._normalize_bg_task_record(pid_str, info)
                try:
                    proc = psutil.Process(pid)
                    status = proc.status()
                    task["status"] = f"running:{status}"
                    report.append(task)
                except psutil.NoSuchProcess:
                    task["status"] = "finished"
                    report.append(task)
                    to_remove.append(pid_str)
        except ImportError:
            return self._structured_tool_result("check_bg_tasks", False, summary="Cannot check background tasks.", errors=["psutil missing. Cannot check PIDs."])
            
        if clear_finished:
            for pid_str in to_remove:
                self.state.remove_active_process(pid_str, persist=False)
            self.state.save()

        return self._structured_tool_result("check_bg_tasks", True, summary=f"Checked {len(report)} background task(s).", data={"tasks": report, "cleared_finished": bool(clear_finished), "removed": to_remove})

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

    @ErrorHandler.handle(severity=ErrorSeverity.CRITICAL, code=ErrorCode.EXEC_ERROR)
    def run_python(self, code: str) -> str:
        self._note_tool_start("python", code, persist=True)
        decision = self.execution_policy.evaluate("python", code, requested_timeout=self.PYTHON_EXEC_TIMEOUT)
        if not decision.allowed:
            self.execution_policy.audit(decision, action="deny", status="blocked", payload=code)
            result = self._structured_tool_result("python", False, summary="Execution blocked.", errors=[decision.reason], data={"code": code[:2000]})
            self._note_tool_result("python", result, persist=True)
            return result

        try:
            self._run_tool_hook('pre', 'python', code)
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="run_python.pre_tool", code=ErrorCode.EXEC_ERROR)

        start_time = time.time()
        self.execution_policy.audit(decision, action="start", status="allowed", payload=code)
        try:
            ast.parse(code)
        except SyntaxError as err:
            result = self._structured_tool_result(
                "python",
                False,
                summary="Python payload rejected before execution.",
                errors=[self._format_python_syntax_error(code, err)],
                data={"code": code[:2000], "stage": "syntax_precheck", "lineno": err.lineno, "offset": err.offset},
            )
            self.execution_policy.audit(
                decision,
                action="finish",
                status="failed",
                payload=code,
                result=self._tool_result_text(result),
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
            self._note_tool_result("python", result, persist=True)
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
                        choice = input(f"{Colors.YELLOW}[Awaiting confirmation] Allow execution? (y/n/always): {Colors.ENDC}").lower().strip()
                    except EOFError:
                        return self._structured_tool_result("python", False, summary="Execution blocked.", errors=["Execution blocked (No Input)."], data={"code": orig_code[:2000]})
                    
                    if choice == "always":
                        self.state.set_runtime_value("safety_always_allow", True)
                        self.state.save()
                        print(f"{Colors.GREEN}Always-allow enabled for this session.{Colors.ENDC}")
                    elif choice != "y":
                        return self._structured_tool_result("python", False, summary="Execution blocked by user.", errors=["Execution blocked by user."], data={"code": orig_code[:2000]})
            
            with self._state_lock:
                current_globals = self.state.globals.copy()
            
            stdout_buf = io.StringIO()
            max_output_chars = int(decision.resource_ceilings.get("max_output_chars", 12000))
            print_max_chars_per_call = int(decision.resource_ceilings.get("print_max_chars_per_call", 3000))
            inspect_max_depth = int(decision.resource_ceilings.get("inspect_max_depth", 2))
            inspect_max_items = int(decision.resource_ceilings.get("inspect_max_items", 20))
            inspect_max_fields = int(decision.resource_ceilings.get("inspect_max_fields", 24))
            inspect_max_string_chars = int(decision.resource_ceilings.get("inspect_max_string_chars", 240))
            inspect_file_chunk_lines = int(decision.resource_ceilings.get("inspect_file_chunk_lines", 120))
            output_truncated = False
            
            def _bridge_subagent(task, priority=2, agent_type="generic"):
                return self.subagent(task, priority=priority, agent_type=agent_type)
            
            def _register_subagent(name, cls, description, capabilities=[]):
                return self.subagent_manager.register_agent_type(name, cls, description, capabilities)

            def _load_skill_shim(name): return self.tool_load_skill(name, env)

            def _render_print_arg(value):
                if isinstance(value, str):
                    return _rlm_limit_text(value, max_chars=print_max_chars_per_call)
                rendered = _rlm_safe_preview_data(
                    value,
                    max_depth=inspect_max_depth,
                    max_items=inspect_max_items,
                    max_fields=inspect_max_fields,
                    max_string_chars=inspect_max_string_chars,
                )
                return _rlm_limit_text(json.dumps(rendered, ensure_ascii=False, default=str, indent=2), max_chars=print_max_chars_per_call)

            def safe_inspect(target=None, *, label="", start_line=1, chunk_lines=None, prefer_file_reads=True):
                return rlm_safe_inspect(
                    target,
                    label=label,
                    start_line=start_line,
                    chunk_lines=chunk_lines or inspect_file_chunk_lines,
                    max_depth=inspect_max_depth,
                    max_items=inspect_max_items,
                    max_fields=inspect_max_fields,
                    max_string_chars=inspect_max_string_chars,
                    prefer_file_reads=prefer_file_reads,
                    max_chars=max_output_chars,
                )

            def inspect_file_chunk(path, start_line=1, chunk_lines=None):
                return rlm_inspect_file_chunk(
                    path,
                    start_line=start_line,
                    chunk_lines=chunk_lines or inspect_file_chunk_lines,
                    max_chars=max_output_chars,
                )

            def guarded_print(*args, **kwargs):
                nonlocal output_truncated
                if "file" in kwargs: builtins.print(*args, **kwargs); return
                sep = kwargs.get('sep', ' '); end = kwargs.get('end', '\n')
                chunk = sep.join(_render_print_arg(arg) for arg in args) + end
                remaining = max_output_chars - stdout_buf.tell()
                if remaining <= 0:
                    if not output_truncated:
                        stdout_buf.write("\n... [PYTHON PRINT OUTPUT TRUNCATED] ...\n")
                        output_truncated = True
                    return
                if len(chunk) <= remaining:
                    stdout_buf.write(chunk)
                    return
                stdout_buf.write(chunk[:remaining])
                if not output_truncated:
                    stdout_buf.write("\n... [PYTHON PRINT OUTPUT TRUNCATED] ...\n")
                    output_truncated = True

            env = {
                "print": guarded_print,
                "safe_inspect": safe_inspect,
                "inspect_file_chunk": inspect_file_chunk,
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
                "analyze_screen": self.tool_analyze_screen,
                "capture_screen": self.tool_capture_screen,
                "capture_window": self.tool_capture_window,
                "capture_window_advanced": self.tool_capture_window_advanced,
                "list_windows_advanced": self.tool_list_windows_advanced,
                "get_active_terminal": self.tool_get_active_terminal,
                "list_processes": getattr(self, "tool_list_processes", lambda *args, **kwargs: self._structured_tool_result("list_processes", False, summary="Process listing tool is unavailable.", errors=["tool_list_processes is not available."], data={"args": list(args), "kwargs": kwargs})),
                "get_software_versions": getattr(self, "tool_get_software_versions", lambda *args, **kwargs: self._structured_tool_result("get_software_versions", False, summary="Software version tool is unavailable.", errors=["tool_get_software_versions is not available."], data={"args": list(args), "kwargs": kwargs})),
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
                "inspect_python_environment": getattr(self, "tool_inspect_python_environment", lambda *args, **kwargs: self._structured_tool_result("inspect_python_environment", False, summary="Python environment inspection tool is unavailable.", errors=["tool_inspect_python_environment is not available."], data={"args": list(args), "kwargs": kwargs})),
                "list_python_packages": getattr(self, "tool_list_python_packages", lambda *args, **kwargs: self._structured_tool_result("list_python_packages", False, summary="Python package listing tool is unavailable.", errors=["tool_list_python_packages is not available."], data={"args": list(args), "kwargs": kwargs})),
                "install_python_package": self.tool_install_python_package,
                "python_symbol_doc": getattr(self, "tool_python_symbol_doc", lambda *args, **kwargs: self._structured_tool_result("python_symbol_doc", False, summary="Python symbol documentation tool is unavailable.", errors=["tool_python_symbol_doc is not available."], data={"args": list(args), "kwargs": kwargs})),
                "python_import_graph": getattr(self, "tool_python_import_graph", lambda *args, **kwargs: self._structured_tool_result("python_import_graph", False, summary="Python import graph tool is unavailable.", errors=["tool_python_import_graph is not available."], data={"args": list(args), "kwargs": kwargs})),
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
            "safe_inspect_raw": rlm_safe_inspect,
            "inspect_file_chunk_raw": rlm_inspect_file_chunk,
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
            except Exception as e:
                    ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="run_python.ast_wrap", code=ErrorCode.EXEC_ERROR)
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
            trimmed_output = self.execution_policy.trim_output(decision, stdout_buf.getvalue())
            return self._structured_tool_result(
                "python",
                True,
                summary="Python execution completed.",
                data={"output": trimmed_output, "code": orig_code[:2000]},
            )
            # end of _execute
        async def _execute_async() -> str:
            loop = asyncio.get_running_loop()
            return await asyncio.wait_for(loop.run_in_executor(None, _execute), timeout=decision.timeout_seconds)

        def _execute_core(raw_code: str) -> str:
            nonlocal code
            code = raw_code
            try:
                return asyncio.run(_execute_async())
            except RuntimeError:
                # Already running in an event loop; fall back to thread-based execution.
                with ThreadPoolExecutor(max_workers=1) as executor:
                    future = executor.submit(_execute)
                    try:
                        return future.result(timeout=decision.timeout_seconds)
                    except TimeoutError:
                        return self._structured_tool_result("python", False, summary="Python execution timed out.", errors=[f"Python execution timed out ({decision.timeout_seconds}s)"], data={"code": raw_code[:2000]})
                    except Exception as e:
                        return self._structured_tool_result("python", False, summary="Python execution failed.", errors=[str(e)], data={"code": raw_code[:2000]})
            except Exception as e:
                return self._structured_tool_result("python", False, summary="Python execution failed.", errors=[str(e)], data={"code": raw_code[:2000]})

        result = self._run_tool_with_wrapper('python', code, _execute_core)
        self._note_tool_result("python", result, persist=True)
        self.execution_policy.audit(
            decision,
            action="finish",
            status="failed" if self._tool_result_failed(result) else "completed",
            payload=code,
            result=self._tool_result_text(result),
            duration_ms=int((time.time() - start_time) * 1000),
        )
        # post-tool hook
        try:
            self._run_tool_hook('post', 'python', result)
        except Exception as e:
            ErrorHandler.log(e, severity=ErrorSeverity.RECOVERABLE, context="run_python.post_tool", code=ErrorCode.EXEC_ERROR)
        return self._append_reviewer_summary(result, "python", code)
        # end of run_python

    def get_system_prompt(self) -> str:
        summary_text = self.state.compressed_summary
        summary_block = f"\nTECHNICAL BACKGROUND (SUMMARY): {summary_text}" if summary_text else ""
        active_goals = self.active_goals()
        current_goal = self.current_goal()
        current_goal_block = self._render_current_goal_focus(current_goal)
        goal_block = ""
        if active_goals:
            goal_lines = [
                f"   - [{goal.get('id')}] priority={goal.get('priority')} status={goal.get('status')} "
                f"next_action={goal.get('next_action')} text={goal.get('text')}"
                for goal in active_goals[:8]
            ]
            goal_block = "\nACTIVE GOALS:\n" + "\n".join(goal_lines)

        sys_info = f"OS: {os.name} | Platform: {sys.platform}"
        if os.name == 'nt':
            sys_info += " (Windows)"
        else:
            sys_info += " (Linux/Unix)"

        cwd = os.getcwd()
        py_path = sys.executable
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        try:
            user = os.getlogin()
        except Exception:
            user = os.environ.get("USER", "unknown")

        env_context = (f"   - **Environment**: CWD='{cwd}' | User='{user}' | Time='{timestamp}'\n"
                       f"   - **Runtime**: Python='{py_path}'")

        try:
            self._refresh_project_memory(persist=True)
            project_brief = self._refresh_project_brief(persist=True)
            task_graph = self._refresh_task_graph(persist=False)
        except Exception:
            project_brief = self.state.project_brief() if hasattr(self.state, "project_brief") else ProjectBrief()
            task_graph = self.state.task_graph() if hasattr(self.state, "task_graph") else TaskGraph()
        memory_block = self._render_memory_context()
        project_brief_block = self._render_project_brief_block(project_brief)
        task_graph_block = self._render_task_graph_block(task_graph)

        available_agents = ", ".join(self.subagent_manager.agent_registry.keys())

        tools_doc = (
            "   - **Terminal**: Use <bash>cmd</bash> for shell commands.\n"
            "   - **Code Engine**: Use <python>code</python> for script logic.\n"
            "   - **Vision**: `see(path, question)`, `see_window(query, question)`, `see_screen(question)`, `capture_window(query)`.\n"
            "   - **Windows/Env**: `list_windows_advanced()`, `list_processes()`, `get_software_versions()`, `find_port(port)`.\n"
            "   - **Background**: `spawn_bg(cmd)`, `run_python_bg(code)`, `check_bg_tasks()`, `get_bg_task_details(pid='')`, `read_bg_task_log(pid)`, `stop_bg_task(pid)`, `restart_bg_task(pid)`.\n"
            "   - **Environment**: `inspect_python_environment()`, `list_python_packages()`, `install_python_package(name, upgrade=False)`, `get_software_versions()`.\n"
            "   - **Python Language**: `python_symbol_doc(name, filepath='', root='.')`, `python_import_graph(filepath, root='.')`, `validate_python_snippet(code, mode='exec')`, `python_refactor_symbol(filepath, old_name, new_name, apply=False)`, `cleanup_unused_imports(filepath, apply=False)`, `python_type_assist(filepath)`, `safe_inspect(obj, label='', start_line=1, chunk_lines=120)`.\n"
            "   - **Git/Project**: `git_changed_files(repo='.')`, `git_diff_analysis(repo='.', src='HEAD', dst='')`, `git_commit_message_draft(repo='.')`, `git_blame_context(file, line, repo='.')`, `git_review_summary(repo='.')`, `git_diff(repo, src, dst)`, `git_summary(repo)`, `map_deps(path)`, `project_map(root)`, `project_map_tool(root='.')`, `project_relationships(root='.')`.\n"
            "   - **Notebook**: `notebook_summary(path)`, `notebook_edit_cell(path, index, source='', cell_type='code', operation='replace')`, `notebook_run(path, cell_index=None, persist_output=True)`, `notebook_kernel_info(path)`, `notebook_session_status(path)`, `notebook_clear_session(path)`, `notebook_install_package(path, package, upgrade=False)`.\n"
            "   - **Database**: `db_save_profile(name, database_path, kind='sqlite')`, `db_list_profiles()`, `db_schema(profile_name='', database_path='')`, `db_query(query, profile_name='', database_path='')`, `db_migration_status(root='.')`.\n"
            "   - **Web/Docs**: `fetch_webpage(url)`, `extract_web_structure(url)`, `extract_doc_section(url, query)`, `summarize_web_reference(url)`, `research_web(query, urls=None)`.\n"
            "   - **Utility**: `to_clip(text)`, `from_clip()`.\n"
            "   - **State**: Variables persist; `remember(tag, txt)`, `recall(tag)`, `search_memory(query)`, `project_memory()`, `task_memory()`, `failure_memory()`.\n"
            "   - **Search**: `search_workspace(query, root='.', pattern='*')`, `find_symbol(name, root='.', pattern='*.py')`, `find_references(name, root='.', patterns='')`, `find_implementations(name, root='.', patterns='')`, `preview_symbol_rename(old, new, root='.', patterns='')`, `grep(pattern, file)`, `find_files(glob)`, `tree(root)`.\n"
            "   - **Filesystem**: `read_file(path)`, `read_range(path, start, end)`, `write(path, content)`, `create_file(path, content, overwrite=False)`, `move_file(src, dst)`, `delete_file(path)`, `patch(path, old, new)`, `edit_lines(path, s, e, txt)`, `peek(file)`, `inspect_file_chunk(path, start_line=1, chunk_lines=120)`.\n"
            "   - **Inspection Guidance**: For inspection, prefer `safe_inspect(...)`, `inspect_file_chunk(...)`, `read_range(...)`, or `peek(...)` over printing giant module dumps, large JSON blobs, or full file contents in one turn.\n"
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
                f"{env_context}{project_brief_block}{task_graph_block}{current_goal_block}\n\n"
                f"AVAILABLE TOOLS (Access via <python>): \n{tools_doc}\n\n"
                f"DECLARED SKILLS:{skill_capability_block}\n"
                f"INSTRUCTIONS:\n"
                f"1. Use <plan> to outline steps.\n"
                f"2. Use <bash> or <python> for execution.\n"
                f"2a. Stay anchored to the CURRENT EXECUTION TARGET. Execute its next action before taking side work unless the user explicitly changes priorities.\n"
                f"3. **STRICT**: Only use these control tags: <plan>, <bash>, <python>, <ack_observation>, and <consensus>. To run functions, use <python>tool_name()</python>.\n"
                f"4. **LOCKING**: If the system says 'Awaiting Acknowledgement', you MUST output <ack_observation> to unlock the turn.\n"
                f"5. **VALIDATION**: If you write code, you MUST wait for turn output before calling <consensus>.\n"
                f"6. **INTERACTION**: To ask the user a question or present a menu, use <consensus>Question text...</consensus>. DO NOT print menus with <python> and wait.\n"
                f"7. **FINALITY**: Use <consensus>final response</consensus> ONLY when the task is complete.\n"
                f"8. **DIRECT ANSWERS**: If the user asks for simple factual information already present in SYSTEM INFO or Environment, answer directly with <consensus> and do not call tools.\n"
                f"9. **FOLLOW-UPS**: After a successful task, end with a concise result. Do NOT append A/B/C menus or next-step option lists unless you are blocked, the request is ambiguous, or the user explicitly asks for choices.\n"
                f"10. **ACTION TURNS**: If you use <bash> or <python>, do the inspection and action only. The runtime will verify and finalize from the actual tool output, so do not add speculative success text or option menus after tool calls.\n"
                f"11. **AUTO-CONTINUE**: After tool output, the runtime may continue internally. If the task is not complete, keep working on the next turn. Use <consensus> only when the task is complete or when you need user input.\n"
                f"{goal_block}{summary_block}{memory_block}{skill_prompt_block}")

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
            request_signature = self._progress_request_signature(user_input)
            self.current_request_context = {
                "user_input": user_input,
                "request_signature": request_signature,
                "turn_counter": self.turn_counter,
            }
            if request_signature and request_signature != "__continue__" and request_signature != self.last_progress_request_signature:
                self.low_progress_turns = 0
                self.last_progress_evaluation = {}
            if request_signature and request_signature != "__continue__":
                self.last_progress_request_signature = request_signature
            # trigger any hooks for incoming user text
            try:
                self.on_user_input(user_input)
            except Exception:
                pass

            # 0. If there are pending plans, complete them first before starting new proposal cycles.
            pending_plans = self.state.query_history(tag="plan", limit=20)
            if pending_plans:
                ConsoleOutput.system("Pending plans detected; resuming existing work before proposing new auto-improvements.")
                try:
                    continue_resp = self.handle_turn("continue")
                    ConsoleOutput.system(f"Continuing pending work result: {continue_resp}")
                except Exception as e:
                    ConsoleOutput.error(f"Error continuing pending plans: {e}")

                # if there are still pending plans, return and wait for next user input.
                if self.state.query_history(tag="plan", limit=20):
                    return "Pending plan work resumed. Continue next turn to keep going."

            for _ in range(24):
                # increment global turn counter so each log entry gets a unique number
                self.turn_counter += 1
                turn_num = self.turn_counter
                self.current_request_context["turn_counter"] = turn_num
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
                    pending_consensus = self._extract_consensus_text(resp) if "<consensus>" in resp else ""
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
                            print(f"{Colors.YELLOW}⚠️ Mixed Consensus and Action detected. Attempting to salvage final answer after tool execution.{Colors.ENDC}")
                            obs_prefix = "System Notice: You provided <consensus> with tools. The consensus will be accepted if the tool results succeed.\n"
                        else:
                            # Valid pure consensus
                            draft = pending_consensus
                            draft, trimmed_menu = self._trim_menu_heavy_followup(draft, user_input)
                            if trimmed_menu:
                                self._append_response_trace(
                                    "consensus_trimmed",
                                    original=resp,
                                    trimmed=draft,
                                    user_input=user_input,
                                )
                            self.state.log_event("assistant", draft)
                            # log consensus turn with metadata
                            dur = time.time() - turn_start
                            meta = ["consensus"]
                            if trimmed_menu:
                                meta.append("trimmed_menu")
                            # no tools used for pure consensus
                            self.logger.log_turn(turn_num, resp, self.state.calculate_diff(turn_start_data, self.state.data), ["consensus"], duration=dur, meta=meta)
                            # Final response should not include the user label prefix
                            return f"\n{Colors.CYAN}{Colors.BOLD}💡 Answer:{Colors.ENDC}\n{draft}"
                    else:
                        obs_prefix = ""

                    progress_baseline = self._capture_turn_progress_baseline() if has_tools else None

                    # 4. Execute Tools
                    obs = ""
                    tool_results: list[str] = []
                    for p in plan: 
                        print(f"{Colors.BLUE}📋 Plan:{Colors.ENDC} {p}")
                        obs += f"Plan: {p}\n" 
                    
                    for b in bash: 
                        print(f"{Colors.CYAN}💻 Bash:{Colors.ENDC} {b}")
                        res = self.run_bash(b)
                        tool_results.append(res)
                        bash_failed = self._report_tool_execution_status(res)
                        obs += f"Bash: {res}\n"
                        if bash_failed:
                            obs += "\nSYSTEM ALERT: ⚠️ A bash tool error occurred. Inspect the result before continuing.\n"
                        try:
                            self.on_tool_output("bash", res)
                        except Exception:
                            pass
                    
                    for p in py:
                        print(f"{Colors.GREEN}🐍 Python:{Colors.ENDC} {p}")
                        out = self.run_python(p)
                        tool_results.append(out)
                        python_failed = self._report_tool_execution_status(out)
                        obs += f"Python: {out}\n"
                        if python_failed:
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
                    if len(obs) > 92000:
                        print(f"{Colors.YELLOW}[System]: Observation too large ({len(obs)} chars). Truncating for history safety...{Colors.ENDC}")
                        truncated_obs = obs[:2000] + "\n... [TRUNCATED DUE TO SIZE] ...\n" + obs[-1000:]
                        self.last_observation = truncated_obs
                        self.state.log_event("system", f"Observation (Truncated): {truncated_obs}")
                    else:
                        self.last_observation = obs
                        self.state.log_event("system", f"Observation: {obs}")

                    if bash or py:
                        finalized, finalize_meta = self._finalize_action_turn(resp, user_input, tool_results)
                        progress_eval = self._evaluate_turn_progress(progress_baseline or {}, finalize_meta, tool_results)
                        if progress_eval.get("low_progress"):
                            self.low_progress_turns += 1
                        else:
                            self.low_progress_turns = 0
                        progress_eval["consecutive_low_progress"] = self.low_progress_turns
                        self.last_progress_evaluation = progress_eval

                        finalize_meta = dict(finalize_meta)
                        finalize_meta["strategy_shift"] = False
                        if progress_eval.get("low_progress") and self.low_progress_turns >= 2:
                            finalized = self._low_progress_strategy_message(progress_eval)
                            finalize_meta["blocked"] = True
                            finalize_meta["strategy_shift"] = True
                            self.last_observation = finalized
                            self.state.log_event("system", finalized)
                            self._note_runtime_error(finalized, current_phase="blocked", persist=True)

                        return_to_user = self._should_return_after_action_turn(pending_consensus, finalize_meta)
                        continuation_note = ""
                        if return_to_user:
                            self.state.log_event("assistant", finalized)
                        else:
                            continuation_note = self._build_internal_action_continuation(finalized, finalize_meta)
                            self.state.log_event("system", continuation_note)
                        self._append_response_trace(
                            "action_turn_finalized",
                            original=resp,
                            finalized=finalized,
                            user_input=user_input,
                            blocked=bool(finalize_meta.get("blocked")),
                            used_llm=bool(finalize_meta.get("used_llm")),
                            trimmed_menu=bool(finalize_meta.get("trimmed_menu")),
                            confidence=str(finalize_meta.get("confidence", "high")),
                            verification=finalize_meta.get("verification", {}),
                            review=finalize_meta.get("review", ""),
                            reviewer_guidance=finalize_meta.get("reviewer_guidance", {}),
                            stronger_verification=finalize_meta.get("stronger_verification", {}),
                            goal_update=finalize_meta.get("goal_update", {}),
                            tool_count=len(tool_results),
                            progress_score=int(progress_eval.get("score", 0)),
                            low_progress=bool(progress_eval.get("low_progress")),
                            consecutive_low_progress=int(progress_eval.get("consecutive_low_progress", 0)),
                            changed_files=progress_eval.get("changed_files", []),
                            changed_state=progress_eval.get("changed_state", []),
                            resolved_error=bool(progress_eval.get("resolved_error")),
                            goal_advances=progress_eval.get("goal_advances", []),
                            redirect_to_inspection=bool(finalize_meta.get("redirect_to_inspection")),
                            strategy_shift=bool(finalize_meta.get("strategy_shift")),
                            returned_to_user=bool(return_to_user),
                            continuation_note=continuation_note,
                        )
                        dur = time.time() - turn_start
                        meta = []
                        if bash:
                            meta.append("tool:bash")
                        if py:
                            meta.append("tool:python")
                        if ack:
                            meta.append("ack:true")
                        meta.append("action")
                        meta.append("finalized_action")
                        meta.append("blocked" if finalize_meta.get("blocked") else "completed")
                        meta.append("low_progress" if progress_eval.get("low_progress") else "progress")
                        if pending_consensus:
                            meta.append("mixed_consensus")
                        if finalize_meta.get("used_llm"):
                            meta.append("finalizer_llm")
                        if finalize_meta.get("trimmed_menu"):
                            meta.append("trimmed_menu")
                        if str(finalize_meta.get("confidence", "high")) != "high":
                            meta.append(f"confidence:{finalize_meta.get('confidence')}")
                        if finalize_meta.get("redirect_to_inspection"):
                            meta.append("inspect_redirect")
                        stronger_verification = finalize_meta.get("stronger_verification", {})
                        if isinstance(stronger_verification, dict) and stronger_verification.get("required"):
                            meta.append("strong_verify")
                        if finalize_meta.get("strategy_shift"):
                            meta.append("strategy_shift")
                        if return_to_user:
                            meta.append("returned_to_user")
                        else:
                            meta.append("continued_internal")
                        self.logger.log_turn(
                            turn_num,
                            resp,
                            self.state.calculate_diff(turn_start_data, self.state.data),
                            [f"bash:{len(bash)}", f"python:{len(py)}", f"ack:{int(ack)}", f"tools:{len(tool_results)}"],
                            duration=dur,
                            meta=meta,
                        )
                        try:
                            self.auto_summarize_history()
                        except Exception:
                            pass
                        if return_to_user:
                            return f"\n{Colors.CYAN}{Colors.BOLD}💡 Answer:{Colors.ENDC}\n{finalized}"
                        continue

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
        if load_command_history():
            log_step("command history loaded")
        else:
            log_step("command history unavailable")

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
                user_text = input()
                input_queue.put(user_text)
                save_command_history()
            except EOFError:
                save_command_history()
                input_queue.put(None)
                break

    t = threading.Thread(target=input_worker, daemon=True)
    t.start()
    return t


def shutdown_runtime(bot: Optional[FlexiBot], reason: str = ""):
    if reason:
        ConsoleOutput.system(reason)
    save_command_history()
    if bot is not None:
        try:
            bot.stop_runtime_heartbeat(reason)
        except Exception:
            pass
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
    # Respect both an explicit bot attribute and a module-level environment-controlled toggle.
    effective_idle = bot.idle_proposal_interval_seconds if (getattr(bot, 'idle_proposal_enabled', False) or globals().get("AUTO_IDLE_PROPOSAL_ENABLED", False)) else idle_timeout
    while True:
        log_step("loop iteration start")
        bot._update_runtime_heartbeat(current_mode="interactive", current_phase="awaiting_input", persist=True)
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
                    if time.time() - last_activity > effective_idle:
                        bot._update_runtime_heartbeat(current_mode="idle", current_phase="idle", persist=True)
                        ConsoleOutput.warning(f"User idle for {effective_idle}s. Resuming...")
                        last_activity = time.time()

                        # trigger auto-proposal workflow and apply confirmed patch (guarded + lightweight safety)
                        # Run the workflow only when explicitly allowed; invoke in a background thread to avoid blocking the input loop.
                        if (getattr(bot, "idle_proposal_enabled", False) or globals().get("AUTO_IDLE_PROPOSAL_ENABLED", False)) and getattr(bot, "idle_proposal_interval_seconds", 0) > 0:
                            import threading

                            def _run_idle_workflow_bg():
                                try:
                                    bot._update_runtime_heartbeat(current_mode="idle", current_phase="idle_workflow", persist=True)
                                    start_time = time.time()
                                    # Force a conservative default: auto_confirm must be explicit on the bot to allow on-disk changes.
                                    # If the attribute is missing or falsy, treat as dry-run to avoid accidental code application.
                                    auto_confirm_attr = bool(getattr(bot, "idle_proposal_auto_confirm", False))
                                    env_allow = os.environ.get("ALLOW_IDLE_AUTO_APPLY", "false").lower() in ("1", "true", "yes")
                                    auto_confirm_arg = auto_confirm_attr and env_allow
                                    if auto_confirm_attr and not env_allow:
                                        ConsoleOutput.warning("idle_proposal_auto_confirm set on bot but ALLOW_IDLE_AUTO_APPLY env var not set; forcing dry-run.")
                                    res = bot.idle_proposal_workflow(auto_propose=False, auto_confirm=auto_confirm_arg)
                                    bot._note_runtime_success(str(res), current_phase="idle", current_mode="idle", persist=True)
                                    if not auto_confirm_arg:
                                        ConsoleOutput.warning("Idle workflow executed in dry-run mode (auto_confirm=False); no code was auto-applied.")
                                    ConsoleOutput.system(f"Idle workflow result: {res}")
                                    elapsed = time.time() - start_time
                                    if elapsed > max(10, effective_idle * 2):
                                        ConsoleOutput.warning(f"Idle workflow completed but took long: {elapsed:.1f}s")
                                except Exception as e:
                                    bot._note_runtime_error(f"Idle workflow error: {e}", current_phase="idle", current_mode="idle", persist=True)
                                    ConsoleOutput.error(f"Idle workflow error: {e}")

                            t = threading.Thread(target=_run_idle_workflow_bg, daemon=True)
                            t.start()
                        else:
                            ConsoleOutput.system("Idle proposal workflow disabled or misconfigured; skipping automated run.")

                        ConsoleOutput.user_output("", end="")
                        ConsoleOutput.prompt()
        else:
            user_input = None

        if user_input is None:
            log_step("user_input is None")
            if not stdin_closed:
                stdin_closed = True
                log_step("stdin_closed flag set")
                bot._update_runtime_heartbeat(current_mode="interactive", current_phase="stdin_closed", persist=True)
                ConsoleOutput.system("stdin closed, continuing to run. Type 'exit' or press Ctrl+C to quit.")
            time.sleep(0.5)
            continue

        if user_input.strip() == "__STATUS__":
            bot._update_runtime_heartbeat(current_mode="interactive", current_phase="status_probe", persist=True)
            ConsoleOutput.system("STATUS PROBE")
            ConsoleOutput.user_output(json.dumps(bot.get_runtime_status(), indent=2))
            continue

        stripped_input = user_input.strip()
        if stripped_input.startswith(OPERATOR_COMMAND_PREFIX):
            try:
                bot._update_runtime_heartbeat(current_mode="interactive", current_phase="operator_command", last_user_input_at=time.time(), persist=True)
                ConsoleOutput.user_output(bot.handle_operator_command(stripped_input))
                bot._note_runtime_success(stripped_input, current_phase="awaiting_input", persist=True)
            except Exception as e:
                bot._note_runtime_error(f"Operator command error: {e}", current_phase="blocked", persist=True)
                ConsoleOutput.error(f"Operator command error: {e}")
            continue

        if user_input.lower() in ["exit", "quit"]:
            bot._update_runtime_heartbeat(current_mode="shutdown", current_phase="shutdown", last_user_input_at=time.time(), persist=True)
            break

        try:
            result = bot.handle_turn(user_input)
            ConsoleOutput.user_output(result)
        except Exception as e:
            bot._note_runtime_error(f"Fatal runtime error: {e}", current_phase="blocked", persist=True)
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
