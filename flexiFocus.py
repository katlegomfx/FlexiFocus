import urllib.request
import urllib.parse
import urllib.error
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
import pickle
import threading
import functools
import random
import ast
import base64
import hashlib
import builtins
import sqlite3
from dataclasses import dataclass
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
from concurrent.futures import ThreadPoolExecutor
from typing import List, Dict, Any, Optional
from contextlib import redirect_stderr, redirect_stdout

class RestartPolicy(str, Enum):
    NEVER = "never"
    ON_FAILURE = "on_failure"
    ALWAYS = "always"

def check_for_upgrades():
    """Scans subies/ for potential upgrades and notifies the user."""
    try:
        root = Path.cwd()
        subies = root / "subies"
        if not subies.exists(): return
        
        candidates = []
        for path in subies.rglob("flexi_source.py"):
            candidates.append(path)
            
        if not candidates: return
        
        # Sort by modification time, newest first
        candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)
        latest = candidates[0]
        
        this_file_mtime = Path(__file__).stat().st_mtime
        if latest.stat().st_mtime > this_file_mtime:
            print(f"\n[Upgrade Available] A newer agent version was found at:\n  {latest.relative_to(root)}\n")
    except Exception:
        pass

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
ARCHIVE_FILE = STATE_DIR / "full_archive.jsonl"
EVOLUTION_LOG = STATE_DIR / "evolution_log.md"
MAX_SNAPSHOTS = 5
TOKEN_THRESHOLD = 92000 # Your specific requirement for summary trigger
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

# --- WINDOWS AUTOMATION HELPERS ---
class SystemAutomation:
    """Encapsulates cross-platform automation logic (Window listing, Capturing)."""
    
    @staticmethod
    def check_dependencies():
        missing = []
        if os.name == 'nt':
            try: import win32gui; import win32con; import win32process
            except ImportError: missing.append("pywin32 (pip install pywin32)")
            try: import psutil
            except ImportError: missing.append("psutil (pip install psutil)")
        elif sys.platform == 'darwin':
            try: from Quartz import CGWindowListCopyWindowInfo
            except ImportError: missing.append("pyobjc-framework-Quartz (pip install pyobjc-framework-Quartz)")
        
        try: from PIL import ImageGrab
        except ImportError: missing.append("Pillow (pip install Pillow)")
        return missing

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
        print(f"""{Colors.CYAN}{Colors.BOLD}
    ███████╗██╗     ███████╗██╗  ██╗██╗
    ██╔════╝██║     ██╔════╝╚██╗██╔╝██║
    █████╗  ██║     █████╗   ╚███╔╝ ██║
    ██╔══╝  ██║     ██╔══╝   ██╔██╗ ██║
    ██║     ███████╗███████╗██╔╝ ██╗██║
    ╚═╝     ╚══════╝╚══════╝╚═╝  ╚═╝╚═╝
        {Colors.DIM}Flexible Copilot Agent v4.2{Colors.ENDC}
        """)

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

class ErrorHandler:
    ERROR_LOG = STATE_DIR / "error_log.jsonl"
    
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
        
        print(f"{color}[{severity.value} | {code.value}] {context}: {str(error)}{Colors.ENDC}")
        
        # File logging
        try:
            ErrorHandler.ERROR_LOG.parent.mkdir(parents=True, exist_ok=True)
            with open(ErrorHandler.ERROR_LOG, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry) + "\n")
        except Exception: pass

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

# --- HELPER FUNCTIONS (RLM STYLE) ---

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

def rlm_git_diff_summary(repo_path: str = ".", src: str = "HEAD", dst: str = ""):
    """Returns a high-level summary of uncommitted changes or branch diffs."""
    try:
        cmd = f"git -C {repo_path} diff --stat {src} {dst}"
        res = subprocess.check_output(cmd, shell=True, text=True, stderr=subprocess.STDOUT)
        return res if res.strip() else "No changes detected."
    except Exception as e:
        return f"Git error: {e}"

def rlm_git_blame_context(filepath: str, line: int):
    """Retrieves the commit message associated with a specific line of code."""
    try:
        cmd = f"git blame -L {line},{line} --porcelain {filepath}"
        res = subprocess.check_output(cmd, shell=True, text=True)
        commit_hash = res.split('\n')[0].split(' ')[0]
        msg_cmd = f"git show -s --format=%B {commit_hash}"
        msg = subprocess.check_output(msg_cmd, shell=True, text=True)
        return f"Commit: {commit_hash}\nMessage: {msg.strip()}"
    except Exception as e:
        return f"Blame error: {e}"

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

    def log_turn(self, turn_num: int, thought: str, diff_summary: str, tools: List[str]):
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        tool_list = ", ".join(tools) if tools else "None"
        try:
            entry = f"\n## Turn {turn_num} - {timestamp}\n**Tools:** `{tool_list}`\n### Thought\n> {thought}\n### State\n```yaml\n{diff_summary}\n```\n---\n"
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
    Async AgentState using SQLite backend with legacy API compatibility.
    Replaces the old JSON-monolith state system.
    """
    def __init__(self, state_file: Path, globals_file: Path, snapshot_dir: Path, max_snapshots: int = 5):
        self.state_file = state_file # Kept for path ref, but we use brain.db
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
        
        # In-Memory Caches (simulating the old .data structure)
        self._history_cache: List[Dict] = [] 
        self._kv_cache: Dict[str, Any] = {}
        self._active_processes: Dict[str, Any] = {}
        self._globals: Dict[str, Any] = {}

        # Initialization
        self._init_db()
        self._load_legacy_globals()
        self._hydrate_cache()
        
        # Start Writer Thread
        self._writer_thread = threading.Thread(target=self._writer_loop, daemon=True, name="MemoryWriter")
        self._writer_thread.start()

    @property
    def data(self):
        """Compatibility shim for old dictionary access."""
        with self._cache_lock:
            return {
                "history": self._history_cache,
                "memory": self._kv_cache,
                "structured_memory": {}, # Deprecated/Empty for Async Core
                "active_processes": self._active_processes,
                "total_tokens": 0,
                "compressed_summary": "" # Fix for KeyError
            }

    @property
    def globals(self):
        return self._globals


    @globals.setter
    def globals(self, value):
        """Setter for globals property to allow assignment like obj.globals = {...}.

        This uses the internal attribute _globals if present; otherwise stores it as _globals.
        """
        try:
            # prefer named internal attribute if it already exists
            if hasattr(self, '_globals'):
                self._globals = value
            else:
                # fallback: set attribute to hold globals
                self._globals = value
        except Exception:
            # last resort: set attribute directly on __dict__
            self.__dict__['_globals'] = value

    def _init_db(self):
        with sqlite3.connect(self.db_path) as conn:
            c = conn.cursor()
            c.execute('''CREATE TABLE IF NOT EXISTS history 
                         (id INTEGER PRIMARY KEY AUTOINCREMENT, role TEXT, content TEXT, timestamp REAL)''')
            c.execute('''CREATE TABLE IF NOT EXISTS knowledge 
                         (key TEXT PRIMARY KEY, value TEXT, tags TEXT, updated_at REAL)''')
            c.execute('''CREATE TABLE IF NOT EXISTS evolution 
                         (id INTEGER PRIMARY KEY AUTOINCREMENT, version TEXT, summary TEXT, diff TEXT, timestamp REAL)''')
            conn.commit()

    def _load_legacy_globals(self):
        if self.globals_file.exists():
            try:
                with open(self.globals_file, "rb") as f: self._globals = pickle.load(f)
            except Exception as e: print(f"Globals Load Error: {e}")

    def _hydrate_cache(self):
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.row_factory = sqlite3.Row
                c = conn.cursor()
                
                # History (Limit 500 for context window)
                c.execute("SELECT role, content, timestamp FROM history ORDER BY id ASC")
                self._history_cache = [dict(row) for row in c.fetchall()]
                
                # Knowledge / Processes
                c.execute("SELECT key, value FROM knowledge")
                for row in c.fetchall():
                    val = json.loads(row['value'])
                    if row['key'] == "active_processes":
                        self._active_processes = val
                    else:
                        self._kv_cache[row['key']] = val
        except Exception: pass

    def _writer_loop(self):
        conn = sqlite3.connect(self.db_path)
        while not self._stop_event.is_set() or not self._write_queue.empty():
            try:
                task = self._write_queue.get(timeout=1.0)
                if task is None: break
                op, d = task
                try:
                    if op == "history":
                        conn.execute("INSERT INTO history (role, content, timestamp) VALUES (?, ?, ?)", 
                                   (d['role'], d['content'], d['timestamp']))
                    elif op == "kv":
                        conn.execute("INSERT OR REPLACE INTO knowledge (key, value, tags, updated_at) VALUES (?, ?, ?, ?)",
                                   (d['key'], json.dumps(d['value']), '[]', time.time()))
                    elif op == "evolution":
                         conn.execute("INSERT INTO evolution (version, summary, diff, timestamp) VALUES (?, ?, ?, ?)",
                                     (d['version'], d['summary'], d['diff'], time.time()))
                    elif op == "globals":
                        # Async Pickle Dump (Risky but better than blocking)
                        with open(self.globals_file, "wb") as f: pickle.dump(d['data'], f)
                    conn.commit()
                except Exception as e: print(f"DB Write Error: {e}")
                finally: self._write_queue.task_done()
            except queue.Empty: continue
        conn.close()

    def save(self):
        # Legacy save trigger - now just queues globals persistence
        # We don't save DB here as it's saved on write
        # Queue globals save
        with self._cache_lock:
            g_copy = self._globals.copy()
        self._write_queue.put(("globals", {"data": g_copy}))
        
        # Persist active processes to DB
        with self._cache_lock:
            proc_copy = self._active_processes.copy()
        self._write_queue.put(("kv", {"key": "active_processes", "value": proc_copy}))

    def log_event(self, role: str, content: str):
        with self._cache_lock:
            entry = {"role": role, "content": content, "timestamp": time.time()}
            self._history_cache.append(entry)
        self._write_queue.put(("history", entry))
        
        # Legacy JSONL Archive
        try:
             with open(ARCHIVE_FILE, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry) + "\n")
        except: pass

    def remember(self, key: str, value: Any):
        with self._cache_lock:
            self._kv_cache[key] = value
        self._write_queue.put(("kv", {"key": key, "value": value}))

    def recall(self, key: str):
        with self._cache_lock:
            return self._kv_cache.get(key)
            
    def take_snapshot(self, label: str = "auto"):
        # Snapshots now just verify DB integrity or backup the DB file
        pass # Database is persistent. Maybe implement DB file copy later.

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
class FlexiBot:
    def __init__(self):
        self.state = AgentState(STATE_FILE, GLOBALS_FILE, SNAPSHOT_DIR, MAX_SNAPSHOTS)
        self.logger = DiffLogger(EVOLUTION_LOG)
        self._setup_client()
        self.subagent_manager = SubagentManager(self)
        self._state_lock = threading.Lock()
        
        # Runtime temp state
        self.last_turn_resp = None
        self.repetition_count = 0
        self.last_tools = {} # Track tool usage for loop detection

        # Control flag: If True, the agent must explicitly acknowledge the last observation
        # using the token <ack_observation> before a <consensus> will be accepted.
        self.must_wait_for_observation = False

    def _setup_client(self):
        config = {}
        if CONFIG_FILE.exists():
            try:
                with open(CONFIG_FILE, "r") as f: config = json.load(f)
            except: pass
        
        provider = config.get("provider", "copilot")
        
        if provider == "ollama":
            print(f"[System]: Using Ollama Provider ({config.get('model', 'lfm2.5-thinking')})")
            self.client = OllamaProvider(
                model=config.get("model", "lfm2.5-thinking"),
                host=config.get("host", "127.0.0.1"),
                port=config.get("port", "11434")
            )
        else:
            print("[System]: Using GitHub Copilot Provider")
            self.client = CopilotClient()

    def compress_context(self):
        """Performs context summary when token limit is hit."""
        print(f"\n[System]: ⚠️ Token limit ({self.state.data['total_tokens']}) reached. Compressing...")
        old_token_count = self.state.data['total_tokens']
        
        # Heuristic: If we are already crashing (400 Bad Request), asking the API to summarize 
        # the thing that is too big will just crash again.
        # Fallback Strategy: Hard truncation + Local specific summary if possible
        
        try:
            # Attempt 1: Try to summarizing only the last 20 messages if full history is massive
            recent_history = self.state.data["history"][-20:]
            full_history_text = "\n".join([f"{m['role']}: {str(m['content'])[:200]}" for m in recent_history])
            
            prompt = f"Condense the following conversation fragment. Conversation:\n{full_history_text}..."
            
            # Using a very simple prompt to minimize overhead
            res = self.client.chat([{"role": "user", "content": prompt}])
            summary = res["choices"][0]["message"]["content"]
            
        except Exception as e:
            print(f"[System]: ⚠ LLM Summary failed ({e}). Performing hard reset.")
            summary = "Context reset due to overflow. Check archive for details."

        # Commit Reduction
        self.state.data["compressed_summary"] = summary
        self.state.data["history"] = [
            {"role": "system", "content": f"Previous Conversation Summary: {summary}"}
        ]
        
        # Clean state metrics to avoid immediate re-trigger
        self.state.data['total_tokens'] = 0 
        self.state.save()
        
        self.logger.log_summary_event(old_token_count, self.state.data['total_tokens'])
        print(f"[System]: Context compressed and reset.")

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
                "total_tokens": self.state.data.get("total_tokens", 0),
                "snapshots": len(list(self.state.snapshot_dir.glob("*.json"))),
                "threads": threading.active_count()
            },
            "subagents": self.subagent_manager.get_load_stats(),
            "memory_keys": list(self.state.data.get("structured_memory", {}).keys())
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

    def run_bash(self, cmd: str) -> str:
        """Run a shell command with smart platform translations and flexible executor selection.
        Returns a string containing STDOUT and STDERR."""
        if not cmd or not cmd.strip():
            return "No command provided."

        translation_note = ""
        cmd_stripped = cmd.strip()
        cmd_parts = cmd_stripped.split()
        if not cmd_parts: return "Empty command."
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

        if cmd_base in mapping:
            new_base = mapping[cmd_base]
            cmd = cmd_stripped.replace(cmd_parts[0], new_base, 1)
            translation_note = f"[Translated '{cmd_base}' -> '{new_base}' for {executor}] "

        # Prepare Execution Args
        use_shell = True
        exec_args = cmd
        if os.name == 'nt':
            if executor == "bash" and shutil.which('bash'):
                exec_args = [shutil.which('bash'), '-c', cmd]
                use_shell = False
            elif executor == "powershell" and shutil.which('powershell'):
                exec_args = [shutil.which('powershell'), '-Command', cmd]
                use_shell = False
            # Else: defaults to CMD via subprocess.run(shell=True)

        # Retry loop for transient errors
        retries = 2
        attempt = 0
        while True:
            try:
                if use_shell:
                    res = subprocess.run(exec_args, shell=True, capture_output=True, text=True, timeout=45, encoding='utf-8', errors='replace')
                else:
                    res = subprocess.run(exec_args, capture_output=True, text=True, timeout=45, encoding='utf-8', errors='replace')

                stdout = res.stdout or ""
                stderr = res.stderr or ""

                not_found = ["not recognized as", "command not found", "No such file or directory"]
                if any(p in stderr for p in not_found):
                    suggestion = f"Suggestion: use platform-native commands or verify the path. Current executor: {executor}"
                    return translation_note + f"STDOUT: {stdout}\nSTDERR: {stderr}\n{suggestion}"

                return translation_note + f"STDOUT: {stdout}\nSTDERR: {stderr}"

            except subprocess.TimeoutExpired as e:
                attempt += 1
                if attempt > retries: return f"Error: Command timed out after {retries} retries ({cmd})"
                time.sleep(1 * (2 ** (attempt - 1)))
                continue
            except Exception as e:
                return f"Error: Execution failed: {e}"

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
        mem = self.state.data.get('memory', {})
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

    def tool_analyze_and_propose(self):
        """Analyzes flexi.py with static checks and generates proposals."""
        print(f"{Colors.YELLOW}[Analysis] self-analyzing codebase...{Colors.ENDC}")
        code = Path(__file__).read_text(encoding="utf-8")
        
        # --- PHASE 1: Static Verification ---
        analysis_report = []
        
        # 1. Syntax Check
        try:
            import ast
            ast.parse(code)
            analysis_report.append("✓ Syntax: Valid Python Code")
        except SyntaxError as e:
            analysis_report.append(f"❌ Syntax Error: {e}")
            
        # 2. Import Audit
        imports = [line for line in code.splitlines() if line.startswith("import ") or line.startswith("from ")]
        analysis_report.append(f"ℹ Imports: Detected {len(imports)} import statements")

        # 3. Security Heuristics
        security_issues = []
        if "os.system" in code: security_issues.append("Avoid `os.system`, use `subprocess.run`")
        if "shell=True" in code and "subprocess" in code: security_issues.append("`shell=True` found in subprocess (potential injection risk)")
        # Simple heuristic check for hardcoded keys (very basic)
        if "api_key =" in code.lower() and "os.environ" not in code.lower(): 
            security_issues.append("Possible hardcoded API key pattern detected")
        
        if security_issues:
            analysis_report.append("⚠ Security Warnings:\n- " + "\n- ".join(security_issues))
        else:
            analysis_report.append("✓ Security: No obvious heuristic issues found")

        report_str = "\n".join(analysis_report)
        print(f"{Colors.CYAN}{report_str}{Colors.ENDC}")

        # --- PHASE 2: LLM Strategic Review ---
        path = Path("flexi_proposals_new.md")

        # Initialize default if missing
        if not path.exists():
            default_content = """# FlexiBot Evolution Proposals\n\nThese proposals focus on enhancing stability, portability, and autonomous capability.\n"""
            try:
                path.write_text(default_content, encoding="utf-8")
                print(f"{Colors.DIM}Created default proposals file at {path.resolve()}{Colors.ENDC}")
            except Exception as e:
                return f"Error creating file {path}: {e}"

        existing_proposals = ""
        action_verb = "Identify"
        if path.exists():
            try:
                existing_proposals = f"\n\nCURRENT PROPOSALS:\n{path.read_text(encoding='utf-8')[:5000]}..."
                action_verb = "Review the current proposals and the code. Refine or Add"
                # Backup
                shutil.copy(path, path.with_name("flexi_proposals_backup.md"))
                print(f"{Colors.DIM}Backed up existing proposals to flexi_proposals_backup.md{Colors.ENDC}")
            except Exception as e:
                print(f"Warning: Could not read/backup proposals: {e}")

        prompt = (f"Analyze this agent code ({len(code)} chars).\n"
                  f"STATIC ANALYSIS REPORT:\n{report_str}\n"
                  f"{action_verb} 3 improvements for modularity, subagent handling, or robustness. "
                  f"Output a Markdown proposal file content. Start with '# FlexiBot Evolution Proposals'.{existing_proposals}")
        
        try:
            res = self.client.chat([{"role": "user", "content": prompt}])
            content = res["choices"][0]["message"]["content"]
            
            # Sanitization: Ensure clean markdown
            if "```markdown" in content: content = content.split("```markdown")[1].split("```")[0].strip()
            elif "```" in content: content = content.split("```")[1].strip()
            
            # Flush to disk immediately
            path.write_text(content, encoding="utf-8")
            print(f"{Colors.DIM}Results written to {path.resolve()}{Colors.ENDC}")
            
            return f"✓ Analysis complete. Report:\n{report_str}"
        except Exception as e:
            ErrorHandler.log(e, context="tool_analyze_and_propose")
            return f"Analysis failed: {e}"

    def tool_finalize_evolution(self):
        """Merges successful subagent work into a new flexi version."""
        today = datetime.now().strftime("%Y/%m/%d")
        today_root = Path("subies") / today
        
        if not today_root.exists(): return "No subagent work found for today."
        
        # 1. Collect Successful Results
        changes = []
        for task_dir in today_root.iterdir():
            result_file = task_dir / "result.txt"
            if result_file.exists():
                content = result_file.read_text(encoding="utf-8")
                # Filter for valid file modifications or code blocks
                if "```python" in content:
                    changes.append(f"### From {task_dir.name}\n{content}")
        
        if not changes: return "No successful code changes found in subagents today."
        
        # 2. Sequential Merging (Iterative Evolution)
        base_code = Path(__file__).read_text(encoding="utf-8")
        current_code = base_code
        
        # Generate timestamped filename (Minute precision to allow rapid iteration)
        ts = datetime.now().strftime("%Y%m%d%H%M")
        new_filename = f"flexi_{ts}.py"
        
        # Resolve collisions (append seconds if needed)
        out_path = Path("subies/ready") / new_filename
        if out_path.exists():
             ts_sec = datetime.now().strftime("%Y%m%d%H%M%S")
             out_path = Path("subies/ready") / f"flexi_{ts_sec}.py"
        
        out_path.parent.mkdir(parents=True, exist_ok=True)
        
        print(f"{Colors.YELLOW}[Evolution] Merging {len(changes)} features into {out_path.name}...{Colors.ENDC}")
        
        # Simple LLM-based merge (Context window risk, but simplest for "smart" merge)
        merge_prompt = (
            f"You are a Senior Lead Developer. We have the current 'flexi.py' and a list of new features/fixes implemented by subagents.\n"
            f"Apply the valid changes to the code. Ensure the resulting code is complete, syntactically correct, and runnable.\n"
            f"CURRENT CODE (Snippet):\n{current_code[:2000]}... (checking header)\n"
            f"CHANGES TO APPLY:\n" + "\n".join(changes[:3]) + # Limit to top 3 to avoid overflow
            f"\n\nOUTPUT ONLY THE FULL VALID PYTHON CODE."
        )
        
        # TODO: For massive files, we'd need a unified diff patcher. 
        # For now, we trust the LLM to rewrite the file if it fits, or we just save the proposed blocks.
        # Given 128k context, we might be able to fit the whole file.
        
        try:
           # Attempt full rewrite
           res = self.client.chat([
               {"role": "system", "content": "You are an automated code integrator. Output only the full python file."},
               {"role": "user", "content": f"Here is the ORIGINAL file content:\n```python\n{current_code}\n```\n\nHere are the PATCHES to apply:\n" + "\n".join(changes)}
           ])
           raw = res["choices"][0]["message"]["content"]
           if "```python" in raw: raw = raw.split("```python")[1].split("```")[0].strip()
           
           out_path.write_text(raw, encoding="utf-8")
           return f"✓ Evolution Complete. New version: {out_path}"
           
        except Exception as e:
            ErrorHandler.log(e, context="tool_finalize_evolution")
            return f"Evolution merge failed: {e}"

    def tool_batch_implement(self, proposal_path: str = "flexi_proposals_new.md", test_script: str = None):
        """Auto-extracts tasks, reviews previous day's work, and runs up to 12 tasks asynchronously."""
        if not Path(proposal_path).exists(): return f"File {proposal_path} not found."
        
        content = Path(proposal_path).read_text(encoding='utf-8')
        if not content.strip(): return f"File {proposal_path} is empty."

        # --- PREVIOUS DAY REVIEW ---
        yesterday = datetime.now() - timedelta(days=1)
        y_path = Path("subies") / yesterday.strftime("%Y/%m/%d")
        context_injection = ""
        if y_path.exists():
            summaries = []
            for task_dir in y_path.iterdir():
                if task_dir.is_dir():
                    res_file = task_dir / "result.txt"
                    if res_file.exists():
                        summaries.append(f"- {task_dir.name}: {res_file.read_text(encoding='utf-8', errors='replace')[:200]}...")
            if summaries:
                context_injection = "PREVIOUS DAY WORK (Review for relevance):\n" + "\n".join(summaries) + "\n"

        # 1. Extract Tasks
        prompt = f"{context_injection}Read this proposal and extract a list of distinct actionable coding tasks. Return ONLY a raw JSON list of strings (e.g. [\"Create x.py\", \"Update y\"]). Content:\n{content[:10000]}"
        try:
            res = self.client.chat([{"role": "system", "content": "You are a Task Extractor. Output JSON only."}, {"role": "user", "content": prompt}])
            raw = res["choices"][0]["message"]["content"]
            if "```" in raw: raw = raw.split("```")[1].replace("json", "").strip()
            tasks = json.loads(raw)
            if not isinstance(tasks, list): return f"Invalid task format: {tasks}"
            if not tasks: return f"No tasks extracted from {proposal_path}. Content might be too vague."
        except Exception as e:
            ErrorHandler.log(e, context="Task Extraction in batch_implement")
            return f"Task extraction failed: {e}"

        # Limit to 12 (User Request)
        tasks = tasks[:12]

        # 2. Execute Async in Subies
        subies_root = Path("subies")
        today = datetime.now().strftime("%Y/%m/%d")
        today_root = subies_root / today
        today_root.mkdir(parents=True, exist_ok=True)
        
        # Deduplication and Indexing logic
        existing_folders = [d for d in today_root.iterdir() if d.is_dir() and d.name.startswith("task_")]
        next_idx = 0
        if existing_folders:
            indices = [int(d.name.split("_")[1]) for d in existing_folders if len(d.name.split("_")) > 1 and d.name.split("_")[1].isdigit()]
            if indices: next_idx = max(indices) + 1
        
        print(f"{Colors.YELLOW}[Batch] Analyzing {len(tasks)} proposed tasks against {len(existing_folders)} already active/done today...{Colors.ENDC}")
        
        spawned_ids = []
        for t in tasks:
            safe_name = re.sub(r'[^a-zA-Z0-9_-]', '_', t)[:40]
            
            # Simple check: Does this safe_name appear in any existing folder?
            if any(safe_name in d.name for d in existing_folders):
                print(f"{Colors.DIM}Skipping duplicate: {safe_name}{Colors.ENDC}")
                continue

            work_dir = today_root / f"task_{next_idx}_{safe_name}"
            next_idx += 1
            
            # Context Propagation: Copy core files to subagent dir
            work_dir.mkdir(parents=True, exist_ok=True)
            try:
                shutil.copy(proposal_path, work_dir / "proposal.md")
                shutil.copy(__file__, work_dir / "flexi_source.py")
                # Create Task File
                (work_dir / "task_instructions.txt").write_text(f"Task: {t}\nContext: Read 'proposal.md' and 'flexi_source.py'. Implement the solution.", encoding='utf-8')
            except Exception as e:
                print(f"{Colors.RED}Failed to propagate context to {work_dir}: {e}{Colors.ENDC}")

            aid = self.subagent_manager.spawn(f"Task: {t}. Read local task_instructions.txt, proposal.md and flexi_source.py to execute.", str(work_dir), priority=2)
            spawned_ids.append(aid)
            
        if not spawned_ids: return "No new tasks spawned (all duplicates)."
            
        return f"✓ Spawned {len(spawned_ids)} subagents. IDs: {spawned_ids}. Use `check_subagents()` to monitor progress."

    def tool_evolve_async(self, task: str):
        """Spawns an async evolution agent to self-improve the codebase."""
        pid = self.subagent(
            task=f"EVOLUTION TASK: {task}. \nTarget: flexi_live.py or flexi.py. \nStandard: Apply improvements using robust patterns.",
            agent_type="generic", 
            priority=1 
        )
        return f"✓ Evolution Agent Spawned. PID: {pid}. Check status with check_subagents()."


    def tool_evolve_async(self, task: str):
        """Spawns an async evolution agent to self-improve the codebase."""
        pid = self.subagent(
            task=f"EVOLUTION TASK: {task}. \nTarget: flexi_live.py or flexi.py. \nStandard: Apply improvements using robust patterns.",
            agent_type="generic", 
            priority=1 
        )
        return f"✓ Evolution Agent Spawned. PID: {pid}. Check status with check_subagents()."

    def tool_check_subagents(self, wait_seconds: int = 0):
        """Checks status of subagents. If wait_seconds > 0, blocks and polls until completion or timeout."""
        start = time.time()
        while True:
            agents = self.subagent_manager.list_agents()
            stats = self.subagent_manager.get_load_stats()
            active = [a for a, d in agents.items() if d['status'] == SubagentStatus.RUNNING.value]
            queued_count = stats["queued"]
            
            # Formatted Header with Load Stats
            header = f"[System Load]: Active={stats['active']} | Queued={stats['queued']} | Capacity={stats['capacity']}/{stats['max_configured']}"

            if (not active and queued_count == 0) or wait_seconds <= 0:
                if not agents: return f"{header}\nNo active subagents."
                report = [header]
                for aid, data in agents.items():
                    res_str = f" | Result: {data['result']}" if data['result'] else ""
                    report.append(f"[{aid}] {data['status']}: {data['task'][:60]}...{res_str}")
                return "\n".join(report)
            
            if time.time() - start > wait_seconds:
                return f"{header}\nWaited {wait_seconds}s. {len(active)} agents running, {queued_count} queued."
            
            time.sleep(2)

    def tool_elevate_project(self, proposal_path: str, test_script: str):
        """Generates a next-gen version of flexi.py based on proposals, tests it, and prepares upgrade."""
        if not Path(proposal_path).exists(): return f"Proposal {proposal_path} not found."
        
        print(f"{Colors.YELLOW}[Elevation] Generating candidate from {proposal_path}...{Colors.ENDC}")
        current_code = Path(__file__).read_text(encoding="utf-8")
        proposal_text = Path(proposal_path).read_text(encoding="utf-8")
        
        # 1. Generate Candidate
        prompt = (f"You are a Senior Python Architect. Rewrite the following 'Current Code' to incorporate the 'Proposals'. "
                  f"Maintain the single-file structure, standard library only constraint, and all existing features. "
                  f"Return ONLY the raw python code for the new file (no markdown).\n\n"
                  f"=== PROPOSALS ===\n{proposal_text}\n\n"
                  f"=== CURRENT CODE ===\n{current_code}")
        
        try:
            res = self.client.chat([{"role": "user", "content": prompt}])
            new_code = res["choices"][0]["message"]["content"]
            if "```python" in new_code: new_code = new_code.split("```python")[1].split("```")[0].strip()
            elif "```" in new_code: new_code = new_code.split("```")[1].strip()
            
            candidate_path = Path("flexi_candidate.py")
            candidate_path.write_text(new_code, encoding="utf-8")
        except Exception as e:
            ErrorHandler.log(e, context="tool_elevate_project: Generation")
            return f"Generation failed: {e}"

        # 2. Test Candidate
        print(f"{Colors.YELLOW}[Elevation] Testing candidate...{Colors.ENDC}")
        try:
            # Basic Syntax Check
            compile(new_code, "flexi_candidate.py", "exec")
            
            # Run Test Script if provided
            if test_script and Path(test_script).exists():
                subprocess.run(f"python flexi_candidate.py --help", shell=True, timeout=5, capture_output=True, encoding='utf-8', errors='replace')
            
        except SyntaxError as e: return f"Candidate failed syntax check: {e}"
        except Exception as e: return f"Candidate failed validation: {e}"

        # 3. Create Upgrader
        upgrader_code = f"""import os, shutil, time, sys
print("Upgrading FlexiBot...")
time.sleep(1)
try:
    if os.path.exists("flexi.py"):
        v = 1
        while os.path.exists(f"flexi_v{{v}}.py"): v += 1
        shutil.move("flexi.py", f"flexi_v{{v}}.py")
        print(f"Backed up current version to flexi_v{{v}}.py")
    
    shutil.move("flexi_candidate.py", "flexi.py")
    print("Upgrade complete! Run 'py flexi.py' to start the new version.")
except Exception as e:
    print(f"Upgrade failed: {{e}}")
    input("Press Enter to exit...")
"""
        Path("finalize_upgrade.py").write_text(upgrader_code, encoding="utf-8")
        return "✓ Candidate generated and verified. Run `python finalize_upgrade.py` to complete the elevation."

    def tool_run_verification(self, target_script: str = "flexi_temp.py"):
        """Generates and runs an advanced controller verification suite."""
        script_content = f"""import subprocess
import sys
import time
import json
import threading
import queue
import os

class AgentController:
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
                errors='replace'
            )
            
            # Register in state
            pid_str = str(p.pid)
            if "active_processes" not in self.state.data:
                self.state.data["active_processes"] = {}
                
            self.state.data["active_processes"][pid_str] = {
                "cmd": cmd,
                "start_time": time.time(),
                "type": "shell",
                "status": "running"
            }
            self.state.save()
            
            if not stop_marker:
                msg = f"✓ Started background process with PID {p.pid} (Registered in State)"
                # Start a non-blocking consumer to keep pipe clear
                def drain(proc):
                    try:
                        while proc.poll() is None:
                            line = proc.stdout.readline()
                            if not line: break
                    except: pass
                threading.Thread(target=drain, args=(p,), daemon=True).start()
                return msg
            
            # Non-blocking wait logic (Polled for the timeout duration)
            start_time = time.time()
            captured = []
            while time.time() - start_time < timeout:
                line = p.stdout.readline()
                if not line: break
                captured.append(line.strip())
                if stop_marker in line:
                    msg = f"✓ Process reached '{stop_marker}'. Substituted into memory."
                    self.tool_remember("processes", f"Spawned '{cmd}' - Ready seen at {time.ctime()}")
                    # Log the observation as well
                    self.state.log_event("system", f"Background process '{cmd}' reached marker '{stop_marker}'.")
                    return f"Success: Process reached marker. Last few lines:\n" + "\n".join(captured[-5:])
            
            return f"Started background process (PID {p.pid}), but marker '{stop_marker}' was not seen in {timeout}s. It continues to run."
        except Exception as e:
            ErrorHandler.log(e, context="tool_spawn_background")
            return f"Spawn error: {e}"

    def tool_run_python_bg(self, code: str):
        """Writes Python code to a temp file and runs it in a detached background process.
        Returns the PID. This is safer for unstable scripts."""
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
                creationflags=subprocess.CREATE_NEW_CONSOLE if os.name == 'nt' else 0
            ) 
            
            # Register
            if "active_processes" not in self.state.data:
                self.state.data["active_processes"] = {}

            self.state.data["active_processes"][str(p.pid)] = {
                "cmd": f"python {script_path.name}",
                "start_time": time.time(),
                "type": "python_bg",
                "script_path": str(script_path),
                "status": "running"
            }
            self.state.save()
            return f"✓ Started Python Background Task. PID: {p.pid}. Script: {script_path}"
        except Exception as e:
            return f"Failed to spawn background python: {e}"

    def tool_check_bg_tasks(self, clear_finished: bool = True):
        """Checks the status of all registered background processes."""
        active = self.state.data.get("active_processes", {})
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
                del self.state.data["active_processes"][pid_str]
            self.state.save()
            
        return "\n".join(report)

    def _check_code_safety(self, code: str) -> str:
        """Evaluates code safety using heuristics and LLM audit."""
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
            last_msg = next((m["content"] for m in reversed(self.state.data["history"]) if m["role"] == "user"), "Unknown Task")
            
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

    def run_python(self, code: str) -> str:
        # --- SAFETY CHECK ---
        if not self.state.data.get("safety_always_allow", False):
            safety_res = self._check_code_safety(code)
            if safety_res.upper() != "SAFE":
                print(f"\n{Colors.RED}[Safety Check] Warning: Code flagged as potential risk.{Colors.ENDC}")
                print(f"Reason: {safety_res}")
                print(f"{Colors.DIM}Code Start:\n{code[:300]}...{Colors.ENDC}")
                
                # We need to capture input from the main thread's input queue if possible?
                # run_python runs in the thread pool if called by `handle_turn`. 
                # Blocking on `input()` here might work if it's the main process or attached terminal.
                try:
                    print(f"{Colors.YELLOW}Allow execution? (y/n/always): {Colors.ENDC}", end="", flush=True)
                    # Note: built-in input() works if we are in the main console thread or if stdin is shared.
                    # Since handle_turn runs sequentially in main thread (mostly), this is fine.
                    choice = input().lower().strip()
                except EOFError:
                    return "Execution blocked (No Input)."
                
                if choice == RestartPolicy.ALWAYS:
                    self.state.data["safety_always_allow"] = True
                    self.state.save()
                    print(f"{Colors.GREEN}Always-allow enabled for this session.{Colors.ENDC}")
                elif choice != "y":
                    return "Execution blocked by user."
        
        with self._state_lock:
            # Refresh globals from state in case another thread updated them
            current_globals = self.state.globals.copy()
            
        stdout_buf = io.StringIO()
        
        # Helper to bridge subagent capability
        def _bridge_subagent(task, priority=2, agent_type="generic"):
            return self.subagent(task, priority=priority, agent_type=agent_type)
        
        # Helper for registration
        def _register_subagent(name, cls, description, capabilities=[]):
            return self.subagent_manager.register_agent_type(name, cls, description, capabilities)

        # Bridge to instance methods
        def _load_skill_shim(name): return self.tool_load_skill(name, env)

        def guarded_print(*args, **kwargs):
            if "file" in kwargs: builtins.print(*args, **kwargs); return
            sep = kwargs.get('sep', ' '); end = kwargs.get('end', '\n')
            stdout_buf.write(sep.join(map(str, args)) + end)

        # Inject RLM helpers and standard modules
        env = {
            "print": guarded_print,
            # Injected Globals from Pickle
            **current_globals,
            # Core State
            "memory": self.state.data["memory"],
            # Structured Memory
            "remember": self.tool_remember,
            "recall": self.tool_recall,
            "search_memory": self.tool_search_memory,
            # Skills
            "save_skill": self.tool_save_skill,
            "load_skill": _load_skill_shim,
            "register_subagent": _register_subagent,
            "batch_implement": self.tool_batch_implement,
            "check_subagents": self.tool_check_subagents,
            "analyze_and_propose": self.tool_analyze_and_propose,
            "elevate_project": self.tool_elevate_project,
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
            "find_consuming_port": self.tool_find_consuming_port,
            "find_port": self.tool_find_consuming_port,
            # RLM Helpers
            "grep": rlm_grep,
            "peek": rlm_peek,
            "read_file": rlm_read,
            "write": rlm_write,
            "patch": rlm_patch,
            "edit_lines": rlm_edit_lines,
            "find_files": rlm_find_files,
            "tree": rlm_tree,
            "read_metadata": rlm_read_metadata,
            "history_search": rlm_history_search,
            "map_deps": rlm_map_dependencies,
            "project_map": rlm_project_summary,
            "git_diff": rlm_git_diff_summary,
            "git_summary": rlm_git_diff_summary,
            "git_blame": rlm_git_blame_context,
            "to_clip": rlm_to_clipboard,
            "from_clip": rlm_from_clipboard,
            "rlm_see": self.tool_see_image,
            "rlm_see_window": self.tool_see_window,
            # New Capabilities
            "subagent": _bridge_subagent,
            "Subagent": Subagent, # Export base class for subclassing
            "ThreadPoolExecutor": ThreadPoolExecutor, # For async patterns
            # Standard Libs
            "re": re,
            "os": os,
            "json": json,
            "shutil": shutil,
            "pickle": pickle
        }
        
        try:
            # AST Magic to auto-print the last expression (REPL-like behavior)
            try:
                tree = ast.parse(code)
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
                    code = compile(tree, filename="<string>", mode="exec")
            except Exception:
                # If AST parsing fails, just execute original code (might be syntax error, let exec handle it)
                pass

            # Threaded execution with timeout (30s) to prevent hanging
            exec_error = []
            def _target():
                try: exec(code, env, env)
                except Exception as e: exec_error.append(e)

            t = threading.Thread(target=_target, daemon=True)
            t.start()
            t.join(timeout=30)
            
            if t.is_alive():
                return f"{stdout_buf.getvalue()}\n[System] Error: Code execution timed out (30s). Infinite loop suspected."
            
            if exec_error: raise exec_error[0]
            
            # Persist globals using Pickle, filtering out non-pickleable injected functions
            # CRITICAL: Lock state updates to prevent race conditions from subagents
            with self._state_lock:
                new_globals = {}
                for k, v in env.items():
                    if k in ["memory", "grep", "peek", "read_file", "write", "patch", "edit_lines", "subagent", "ThreadPoolExecutor", "remember", "recall", "save_skill", "load_skill", "find_files", "tree", "read_metadata", "batch_implement", "elevate_project", "print", "see_image", "see", "see_window", "capture_window", "capture_window_advanced", "list_windows_advanced", "get_active_terminal", "spawn_background", "spawn_bg", "find_consuming_port", "find_port", "map_deps", "project_map", "git_diff", "git_summary", "git_blame", "to_clip", "from_clip", "rlm_see", "rlm_see_window"]: continue
                    if k in ["re", "os", "json", "shutil", "pickle", "__builtins__"]: continue
                    
                    try:
                        pickle.dumps(v)
                        new_globals[k] = v
                    except (pickle.PicklingError, TypeError, AttributeError):
                        # Silently skip unpickleables for now inside logic
                        pass
                
                self.state.globals = new_globals
                self.state.save()

            return stdout_buf.getvalue()
        except Exception: return traceback.format_exc()

    def get_system_prompt(self) -> str:
        summary_block = f"\nTECHNICAL BACKGROUND (SUMMARY): {self.state.data['compressed_summary']}" if self.state.data['compressed_summary'] else ""
        
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
        mem = self.state.data.get("structured_memory", {})
        
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
            "   - **Background**: `spawn_bg(cmd)`, `run_python_bg(code)`, `check_bg_tasks()`. Use these for long-running or unstable tasks.\n"
            "   - **Git/Project**: `git_diff(repo, src, dst)`, `git_summary(repo)`, `git_blame(file, line)`, `map_deps(path)`, `project_map(root)`.\n"
            "   - **Utility**: `to_clip(text)`, `from_clip()`.\n"
            "   - **State**: Variables persist; `remember(tag, txt)`, `recall(tag)`, `search_memory(query)`.\n"
            "   - **Filesystem**: `read_file(path)`, `write(path, content)`, `patch(path, old, new)`, `edit_lines(path, s, e, txt)`, `grep(pattern, file)`, `peek(file)`, `tree(root)`, `find_files(glob)`.\n"
            "   - **Recursion**: `subagent(task, agent_type='generic')` spawns a bot. Types: [" + available_agents + "].\n"
            "   - **Background**: `batch_implement(proposal_file)` runs tasks in `subies/`; `check_subagents()` to monitor progress."
        )

        return (f"You are FlexiBot, a recursive automation agent.\n"
                f"SYSTEM INFO: {sys_info}.\n"
                f"{env_context}\n\n"
                f"AVAILABLE TOOLS (Access via <python>): \n{tools_doc}\n\n"
                f"INSTRUCTIONS:\n"
                f"1. Use <plan> to outline steps.\n"
                f"2. Use <bash> or <python> for execution.\n"
                f"3. **STRICT**: ONLY use <bash>, <python>, or <plan> tags. To run functions, use <python>tool_name()</python>.\n"
                f"4. **LOCKING**: If the system says 'Awaiting Acknowledgement', you MUST output <ack_observation> to unlock the turn.\n"
                f"5. **VALIDATION**: If you write code, you MUST wait for turn output before calling <consensus>.\n"
                f"6. **INTERACTION**: To ask the user a question or present a menu, use <consensus>Question text...</consensus>. DO NOT print menus with <python> and wait.\n"
                f"7. **FINALITY**: Use <consensus>final response</consensus> ONLY when the task is complete.\n"
                f"{summary_block}{mem_hint}")

    def handle_turn(self, user_input: str):
        try:
            # Periodic Summary Check
            if self.state.data.get("total_tokens", 0) > TOKEN_THRESHOLD:
                self.compress_context()

            self.state.take_snapshot(label="pre_turn")
            self.state.log_event("user", user_input)

            for i in range(24):
                try:
                    turn_start_data = json.loads(json.dumps(self.state.data))
                    
                    # --- CRITICAL FIX: Safe Context ---
                    # Even with compression, the "full" history might be malformed or too big.
                    # We enforce a hard limit on the # of messages passed to the API here.
                    MAX_MESSAGES = 12
                    recent_context = self.state.data["history"][-MAX_MESSAGES:]
                    
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
                            self.state.data["history"][-1]
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
                            self.logger.log_turn(i+1, resp, self.state.calculate_diff(turn_start_data, self.state.data), ["consensus"])
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
                    
                    for p in py:
                        print(f"{Colors.GREEN}🐍 Python:{Colors.ENDC} {p}")
                        out = self.run_python(p)
                        print(f"{Colors.DIM}  -> Tool exit OK.{Colors.ENDC}")
                        obs += f"Python: {out}\n"
                        if "Traceback (most recent call last)" in out or "Error:" in out:
                            print(f"{Colors.RED}❌ Tool Error detected.{Colors.ENDC}")
                            obs += "\nSYSTEM ALERT: ⚠️ An error occurred. Analyze and FIX the code.\n"
                    
                    if obs_prefix: obs = obs_prefix + obs

                    # 5. Loop Protection
                    is_exact_repeat = (resp == self.last_turn_resp)
                    is_tool_repeat = (has_tools and bash == self.last_tools.get('bash') and py == self.last_tools.get('py'))

                    if not ack and (is_exact_repeat or is_tool_repeat):
                        self.repetition_count += 1
                        if self.repetition_count >= 2:
                            print(f"{Colors.RED}⚠️ Repetitive Loop Detected.{Colors.ENDC}")
                            if self.repetition_count >= 4:
                                break
                            obs = "System Error: You are repeating the same action. You MUST try a different approach or ask the user for help via <consensus>."
                            self.state.log_event("system", obs)
                    else:
                        self.repetition_count = 0
                    
                    self.last_turn_resp = resp
                    self.last_tools = {'bash': bash, 'py': py}

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
                        self.state.log_event("system", f"Observation (Truncated): {truncated_obs}")
                    else:
                        self.state.log_event("system", f"Observation: {obs}")

                    # 6. Log and Continue
                    self.state.log_event("assistant", resp)
                    self.logger.log_turn(i+1, resp, self.state.calculate_diff(turn_start_data, self.state.data), [f"bash:{len(bash)}", f"python:{len(py)}", f"ack:{int(ack)}"])
                
                except Exception as inner_e:
                    print(f"{Colors.RED}⚠️ Critical Turn Error: {inner_e}{Colors.ENDC}")
                    traceback.print_exc()
                    obs = f"System Error during turn execution: {inner_e}. Please retry."
                    self.state.log_event("system", obs)
            
            return "Max turns reached without consensus."
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


def main():
    check_for_upgrades()
    Colors.fix_windows_console()
    clear_console()
    
    Colors.print_logo()
    
    if not HISTORY_SUPPORT and os.name == 'nt':
        print(f"{Colors.DIM}Tip: Run `pip install pyreadline3` to enable Up-Arrow command history.{Colors.ENDC}")

    # Register Global Error Hooks
    ErrorHandler.register_global_handler()

    try:
        bot = FlexiBot()
        
        print(f"{Colors.DIM}System initialized. Auto-Summary threshold: {TOKEN_THRESHOLD}{Colors.ENDC}")
        
        # Idle Timer Config
        IDLE_TIMEOUT = 300 # 5 minutes
        input_queue = queue.Queue()

        def input_worker():
            while True:
                try:
                    input_queue.put(input())
                except EOFError:
                    input_queue.put(None)
                    break

        # Start permanent input thread
        t = threading.Thread(target=input_worker)
        t.daemon = True
        t.start()

        while True:
            print(f"\n{Colors.GREEN}{Colors.BOLD}👤 You:{Colors.ENDC} ", end="", flush=True)
            
            last_activity = time.time()
            user_input = None

            while True:
                try:
                    # Check for input with short timeout
                    user_input = input_queue.get(timeout=0.5)
                    break
                except queue.Empty:
                    # Check for idle timeout
                    if time.time() - last_activity > IDLE_TIMEOUT:
                        print(f"\n\n{Colors.YELLOW}[System]: User idle for {IDLE_TIMEOUT}s. Triggering autonomous background tasks...{Colors.ENDC}")
                        
                        # Run the batch implementation check
                        autonomous_task = (
                            "System: User is idle. You must perform the following actions using the correct tools:\n"
                            "1. Call <python>analyze_and_propose()</python> to generate improvements.\n"
                            "2. Read the file 'flexi_proposals_new.md' using <bash>cat ...</bash> or <python>peek(...)</python>.\n"
                            "3. Call <python>batch_implement('flexi_proposals_new.md')</python> to build features.\n"
                            "4. Call <python>check_subagents(wait_seconds=60)</python> to monitor progress efficiently.\n"
                            "5. Call <python>verify_work()</python> to verify capabilities.\n"
                            "6. Report final progress in <consensus>...</consensus>."
                        )
                        try:
                            print(bot.handle_turn(autonomous_task))
                        except Exception as e:
                            print(f"\n{Colors.RED}[System]: Autonomous background task failed: {e}{Colors.ENDC}")
                            print(f"{Colors.DIM}Use 'py flexi.py' to restart if this persists.{Colors.ENDC}")
                        
                        # Reset timer and re-print prompt
                        last_activity = time.time()
                        print(f"\n{Colors.GREEN}{Colors.BOLD}👤 You:{Colors.ENDC} ", end="", flush=True)
            
            if user_input is None: break # EOF
            if user_input.strip() == "__STATUS__":
                print(f"\n{Colors.CYAN}[STATUS PROBE]{Colors.ENDC}")
                print(json.dumps(bot.get_runtime_status(), indent=2))
                continue

            if user_input.lower() in ["exit", "quit"]: break
            try:
                result = bot.handle_turn(user_input)
                print(result)
            except Exception as e:
                print(f"\n{Colors.RED}[FATAL ERROR]: {e}{Colors.ENDC}")
                traceback.print_exc()
                print(f"{Colors.DIM}Attempting to save state before exit...{Colors.ENDC}")
                try: bot.state.save()
                except: pass

    except KeyboardInterrupt:
        print(f"\n\n{Colors.YELLOW}👋 Gracefully shutting down... (Ctrl+C detected){Colors.ENDC}")
        sys.exit(0)

if __name__ == "__main__": main()


