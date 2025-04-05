#!/usr/bin/env python3
import socket
import threading
import time
import random
import logging
import os
import json
import collections
import argparse
import sys
import signal
from datetime import datetime
import requests # For HTTP downloads (optional)
from urllib.parse import urljoin # For constructing URLs safely (optional)

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150 # ms
SERVER_OFFLINE_TIMEOUT = 15 # seconds without response
LAST_FILES_DISPLAY_COUNT = 10 # How many recent filenames/URLs/events to show
UI_UPDATE_INTERVAL = 0.5 # How often to refresh the terminal stats (seconds)
HTTP_TIMEOUT = 15 # seconds for HTTP connection/read
DOWNLOAD_LOG_FILENAME = "activity_log.txt" # Unified log for HTTP/Sim/UDP events
UDP_VERIFY_FILENAME_PREFIX = "udp_verify_" # Prefix for temporary UDP verification files

# Simulation constants (used if --fastdl-url is not provided)
CS_FILE_REQUESTS = [ # Base UDP requests for simulation trigger
    b"\xff\xff\xff\xffrcon", b"\xff\xff\xff\xffping\x00",
    b"\xff\xff\xff\xffdetails\x00", b"\xff\xff\xff\xffplayers\x00",
    b"\xff\xff\xff\xffrules\x00", b"\xff\xff\xff\xffchallenge\x00",
]
# Rough simulated sizes
DOWNLOAD_SIZES = { "map": 5*1024*1024, "model": 1*1024*1024, "sound": 256*1024, "sprite": 64*1024, "texture": 512*1024, "other": 128*1024 }

# --- Global logger setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr # Main logs to stderr
)
logger = logging.getLogger('cs_bandwidth_tester')

# --- Activity Logger Setup (File logging) ---
activity_logger = logging.getLogger('activity_logger')
activity_logger.setLevel(logging.INFO)
activity_logger.propagate = False # Don't send to main logger's stream handler

# Global variable to hold the tester instance for signal handling
tester_instance = None

# ==============================================================
# ServerQuery Class (Includes UDP save/delete verification)
# ==============================================================
class ServerQuery:
    def __init__(self, server_ip, server_port=DEFAULT_PORT, storage_dir="."):
        self.server_ip = server_ip
        self.server_port = server_port
        self.storage_dir = storage_dir # For UDP verification files
        self.last_info = None; self.last_rules = None
        self.last_ping = 0; self.sock = None
        self.retry_count = 2; self.timeout = 1.5
        self.last_challenge = None

    def _create_socket(self):
        if self.sock is not None:
            try: self.sock.close()
            except Exception: pass
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.settimeout(self.timeout)
        except Exception as e:
            logger.error(f"Query Socket Create Error: {e}")
            self.sock = None
            raise

    def _log_activity(self, level, message):
        """Helper to log to both main logger and activity file logger."""
        logger.log(level, message)
        activity_logger.log(level, message)

    # --- MODIFIED: _send_recv includes UDP save/verify/delete ---
    def _send_recv(self, request, query_type="unknown"):
        """Sends UDP, receives, verifies (save/delete), returns response, ping."""
        if self.sock is None:
            try: self._create_socket()
            except Exception: return None, 0

        start_time = time.time()
        response = None
        ping = 0
        for attempt in range(self.retry_count):
            try:
                # Use main logger for debug, activity logger maybe only for verification step
                logger.debug(f"Sending UDP {query_type} query (attempt {attempt+1})...")
                self.sock.sendto(request, (self.server_ip, self.server_port))
                response, addr = self.sock.recvfrom(4096)
                end_time = time.time()
                ping = int((end_time - start_time) * 1000)

                if response:
                    logger.debug(f"UDP response received from {addr} for {query_type} ({len(response)} bytes).")

                    # --- UDP Verification: Save and Delete ---
                    verify_filename = f"{UDP_VERIFY_FILENAME_PREFIX}{query_type}_{int(time.time()*1000)}.bin"
                    verify_filepath = os.path.join(self.storage_dir, verify_filename)
                    saved_ok = False
                    verify_msg_prefix = f"[UDP Verify] Query: {query_type}"
                    try:
                        with open(verify_filepath, 'wb') as vf:
                            vf.write(response)
                        saved_ok = True
                        # Log success to activity log file
                        self._log_activity(logging.INFO, f"{verify_msg_prefix} | Status: SAVED | Bytes: {len(response)} | Path: {verify_filepath}")
                    except Exception as e:
                        self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: SAVE_FAILED | Path: {verify_filepath} | Error: {e}")
                    finally:
                        if os.path.exists(verify_filepath):
                            try:
                                os.remove(verify_filepath)
                                if saved_ok: # Only log delete success if save was OK
                                     self._log_activity(logging.INFO, f"{verify_msg_prefix} | Status: DELETED | Path: {verify_filepath}")
                            except Exception as e:
                                self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: DELETE_FAILED | Path: {verify_filepath} | Error: {e}")
                        elif saved_ok:
                            self._log_activity(logging.WARNING, f"{verify_msg_prefix} | Status: DELETE_WARN | Path: {verify_filepath} | File not found after reported save.")
                    # --- End UDP Verification ---

                    return response, ping
                else:
                    logger.debug(f"Received empty UDP response (attempt {attempt+1}) for {query_type}")

            except socket.timeout:
                logger.debug(f"UDP {query_type} query timed out (attempt {attempt+1})")
                if attempt == self.retry_count - 1: return None, 0
                time.sleep(0.1)
            except OSError as e:
                logger.warning(f"UDP Query OSError (attempt {attempt+1}): {e}")
                self.close() # Close potentially broken socket
                return None, 0
            except Exception as e:
                logger.error(f"Unexpected UDP Query Error (attempt {attempt+1}): {e}")
                self.close()
                return None, 0
        return None, 0

    def get_info(self):
        """Gets basic server info (A2S_INFO)."""
        request = b"\xFF\xFF\xFF\xFFTSource Engine Query\x00"
        response, ping = self._send_recv(request, query_type="info")
        if response:
            parsed_info = self._parse_info(response)
            if parsed_info:
                self.last_ping = ping
                parsed_info['ping'] = self.last_ping
                self.last_info = parsed_info
                if response[4:5] == b'A': # Challenge reply
                    self.last_challenge = response[5:9]
                    logger.debug(f"Received challenge: {self.last_challenge.hex()}")
                # GoldSrc might include challenge in 'm' reply footer, handle if needed
                else:
                    self.last_challenge = None # Clear if not explicit challenge
                return parsed_info
            else: logger.debug(f"Failed to parse INFO response.")
        return None

    def get_rules(self):
        """Gets server rules/cvars (A2S_RULES)."""
        challenge_bytes = self.last_challenge
        if challenge_bytes is None:
            # Try a default/common challenge if none received yet
            # Some servers respond to 0xFFFFFFFF or the result of a previous challenge
            logger.debug("No prior challenge key, using default FFFFFFFF for rules query.")
            challenge_bytes = b'\xFF\xFF\xFF\xFF'

        request = b'\xFF\xFF\xFF\xFFV' + challenge_bytes # A2S_RULES request: 0x56
        response, _ = self._send_recv(request, query_type="rules")

        if response and response[4:5] == b'E': # 0x45 A2S_RULES response header
             parsed_rules = self._parse_rules(response)
             if parsed_rules: self.last_rules = parsed_rules
             return parsed_rules
        # Handle challenge request if server requires it for rules
        elif response and response[4:5] == b'A':
             self.last_challenge = response[5:9]
             logger.info(f"Received new challenge {self.last_challenge.hex()} while requesting rules. Retrying rules query.")
             # Retry once with the new challenge
             request = b'\xFF\xFF\xFF\xFFV' + self.last_challenge
             response, _ = self._send_recv(request, query_type="rules_retry")
             if response and response[4:5] == b'E':
                  parsed_rules = self._parse_rules(response)
                  if parsed_rules: self.last_rules = parsed_rules
                  return parsed_rules
             else: logger.warning("Failed to get rules even after challenge retry.")
        elif response:
            logger.debug(f"Received unexpected response type {response[4:5]} for RULES query.")
        return None # Failed to get rules

    # --- Parsers (_parse_info, _parse_rules) ---
    # (Keep the parsing logic from the previous complete script - they seemed okay)
    def _parse_info(self, response):
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF': return None
            header_byte = response[4:5]
            offset = 5
            # Source Engine Info Reply ('I')
            if header_byte == b'I':
                offset += 1 # Skip protocol
                def read_string(data, start_offset):
                    end = data.find(b'\x00', start_offset)
                    if end == -1: raise ValueError("Malformed string")
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1
                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)
                if offset + 9 > len(response): raise ValueError("Too short (Source)")
                offset += 2 # Skip AppID
                player_count = response[offset]; offset += 1
                max_players = response[offset]; offset += 1
                bot_count = response[offset]; offset += 1
                # Could parse more fields here (type, env, visibility, vac, version)
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': bot_count}
            # GoldSrc Info Reply ('m') - Simpler format
            elif header_byte == b'm':
                addr_end = response.find(b'\x00', offset) # Address string first
                if addr_end == -1: raise ValueError("Malformed address (GoldSrc)")
                offset = addr_end + 1
                def read_string_gs(data, start_offset):
                    end = data.find(b'\x00', start_offset)
                    if end == -1: raise ValueError("Malformed string (GoldSrc)")
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1
                server_name, offset = read_string_gs(response, offset)
                map_name, offset = read_string_gs(response, offset)
                game_dir, offset = read_string_gs(response, offset)
                game_desc, offset = read_string_gs(response, offset)
                if offset + 3 > len(response): raise ValueError("Too short (GoldSrc)")
                player_count = response[offset]; offset += 1
                max_players = response[offset]; offset += 1
                # Could parse more: protocol, type, env, visibility, mod, vac, bots
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': 0} # Assume 0 bots if not parsed
            elif header_byte == b'A': return None # Challenge response
            else: logger.debug(f"Unsupported INFO response type: {header_byte}"); return None
        except (IndexError, ValueError) as e: logger.warning(f"Parse INFO error: {e}"); return None
        except Exception as e: logger.error(f"Unexpected parse INFO error: {e}", exc_info=False); return None

    def _parse_rules(self, response):
        try:
            if not response or len(response) < 7 or response[:5] != b'\xFF\xFF\xFF\xFFE': return None
            rules_count = int.from_bytes(response[5:7], 'little')
            offset = 7
            rules = {}
            for _ in range(rules_count):
                name_end = response.find(b'\x00', offset)
                if name_end == -1: raise ValueError("Malformed rule name")
                rule_name = response[offset:name_end].decode('utf-8', errors='ignore')
                offset = name_end + 1
                value_end = response.find(b'\x00', offset)
                if value_end == -1: raise ValueError(f"Malformed rule value for '{rule_name}'")
                rule_value = response[offset:value_end].decode('utf-8', errors='ignore')
                offset = value_end + 1
                rules[rule_name] = rule_value
            logger.debug(f"Parsed {len(rules)} rules. Found sv_downloadurl: {'yes' if 'sv_downloadurl' in rules else 'no'}")
            return rules
        except (IndexError, ValueError) as e: logger.warning(f"Parse RULES error: {e}"); return None
        except Exception as e: logger.error(f"Unexpected parse RULES error: {e}", exc_info=False); return None

    def close(self):
        if self.sock:
            try: self.sock.close()
            except Exception: pass
            self.sock = None

# ==============================================================
# CS16BandwidthTester Class (Handles Both HTTP and Simulation)
# ==============================================================
class CS16BandwidthTester:
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 # Added download_delay back for simulation
                 download_delay, verbose, storage_dir, continuous_mode, no_server_monitor,
                 # fastdl_url is now optional
                 fastdl_url, file_list_path, delete_after_download, activity_log_filename):

        self.server_ip = server_ip; self.server_port = server_port
        self.num_connections = num_connections; self.test_duration = test_duration
        self.download_delay = max(0, download_delay) # Used for simulation
        self.verbose = verbose; self.continuous_mode = continuous_mode
        self.storage_dir = storage_dir; self.no_server_monitor = no_server_monitor
        self.manual_fastdl_url = fastdl_url # Store the provided URL (or None)
        self.file_list_path = file_list_path # Store path to file list
        self.delete_after_download = delete_after_download # For HTTP downloads only
        self.activity_log_filename = activity_log_filename

        # --- Setup Storage and Logging ---
        self.activity_log_filepath = None
        if not os.path.exists(self.storage_dir):
            try: os.makedirs(self.storage_dir); logger.info(f"Created storage directory: {self.storage_dir}")
            except OSError as e: logger.error(f"Failed storage dir '{self.storage_dir}': {e}. Using current."); self.storage_dir = "."

        # Configure activity_logger file handler
        try:
            self.activity_log_filepath = os.path.join(self.storage_dir, self.activity_log_filename)
            file_handler = logging.FileHandler(self.activity_log_filepath, mode='a', encoding='utf-8')
            file_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
            file_handler.setFormatter(file_formatter)
            activity_logger.addHandler(file_handler)
            activity_logger.info(f"--- Activity Log Started ({datetime.now().isoformat()}) ---")
            logger.info(f"Logging activity details to: {self.activity_log_filepath}")
        except Exception as e:
            logger.error(f"Failed to configure activity log file handler: {e}")
            activity_logger.addHandler(logging.NullHandler()) # Prevent errors if logging fails

        # Core state
        self.active = False; self.threads = []; self.connections = []
        self.lock = threading.Lock(); self._stop_event = threading.Event()
        self.start_time = 0; self.end_time = 0

        # Counters (separated for clarity)
        self.bytes_received_http = 0; self.http_download_attempts = 0
        self.http_download_successes = 0; self.http_download_failures = 0
        self.bytes_received_sim = 0; self.simulated_downloads_count = 0
        self.udp_requests_sent_sim = 0 # UDP packets sent by simulation workers
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0

        # Server info tracking
        self.server_query = None
        if not self.no_server_monitor:
             # Pass storage_dir for UDP verification
             self.server_query = ServerQuery(server_ip, server_port, storage_dir=self.storage_dir)
        self.server_info = None; self.server_rules = None
        self.discovered_fastdl_url = None # From rules query
        self.active_fastdl_url = self.manual_fastdl_url # Prioritize manual URL
        self.current_map_file_path = None # Relative path like maps/de_dust2.bsp
        self.files_to_try_http = [] # Loaded from file list

        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN"
        self.server_last_seen = 0
        self.server_info_thread = None; self.server_info_interval = 5
        self.server_status_log = [] # Log of status/ping from ServerQuery

        # Asset/Event tracking
        self.last_activity = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        self.bandwidth_log_points = [] # Tracks combined rate (HTTP or Sim)

        self.display_thread = None
        self.http_session = requests.Session() # Session for potential HTTP Keep-Alive

        self._load_file_list() # Load files for potential HTTP downloads

    def _load_file_list(self):
        """Loads file paths from the specified file for HTTP downloads."""
        if self.file_list_path:
            try:
                with open(self.file_list_path, 'r') as f:
                    for line in f:
                        file = line.strip()
                        if file and not file.startswith('#') and not file.startswith('//'):
                             # Normalize path separators and remove leading slash
                             normalized_path = file.replace('\\', '/').lstrip('/')
                             if '..' not in normalized_path: # Basic path safety check
                                 self.files_to_try_http.append(normalized_path)
                             else:
                                 logger.warning(f"Skipping potentially unsafe path from list: {file}")
                logger.info(f"Loaded {len(self.files_to_try_http)} file paths for HTTP from '{self.file_list_path}'")
            except FileNotFoundError: logger.error(f"File list not found: {self.file_list_path}")
            except Exception as e: logger.error(f"Error reading file list '{self.file_list_path}': {e}")
        else: logger.debug("No file list path specified for HTTP downloads.")

    def _increment_counter(self, counter_name, value=1):
        with self.lock: setattr(self, counter_name, getattr(self, counter_name) + value)
    def _decrement_counter(self, counter_name, value=1): self._increment_counter(counter_name, -value)

    # --- Combined Activity Logging ---
    def _log_activity_event(self, worker_id, event_type, status, identifier, bytes_val=0, error_msg="", detail=""):
        """Logs events (HTTP, SIM, UDP Verify) to activity log file and potentially console."""
        message = f"Worker {worker_id:<3} [{event_type:<10}] | Status: {status:<10} | ID: {identifier}"
        if bytes_val > 0: message += f" | Bytes: {bytes_val:<10}"
        if detail: message += f" | Detail: {detail}"
        if error_msg: message += f" | Error: {error_msg}"

        log_level = logging.INFO # Default for activity log file
        if "FAIL" in status or "ERROR" in status or "TIMEOUT" in status:
            log_level = logging.WARNING
        if status == "INTERRUPT":
             log_level = logging.INFO
        # Special handling for console logging (less verbose)
        console_log_level = log_level if log_level >= logging.WARNING else logging.DEBUG

        activity_logger.log(log_level, message) # Always log to file

        # Log significant events or verbose events to console
        if log_level >= logging.INFO or self.verbose:
             console_msg = f"Worker {worker_id}: {event_type} {status}: {identifier}"
             if bytes_val > 0: console_msg += f" ({bytes_val/1024:.1f}KB)"
             if error_msg: console_msg += f" - {error_msg}"
             # Don't log UDP verify saves/deletes to console unless verbose
             if event_type == "UDP Verify" and status in ["SAVED", "DELETED"] and not self.verbose:
                  pass
             else:
                  logger.log(console_log_level, console_msg)


        # Update UI deque
        with self.lock:
            if event_type != "UDP Verify": # Don't show UDP verify in UI for now
                 ui_entry = f"{identifier} ({bytes_val/1024:.1f}KB)"
                 if event_type == "SIM Download": ui_entry += " [SIM]"
                 elif status != "SUCCESS": ui_entry += f" [{status}]"
                 self.last_activity.append(ui_entry)


    # --- HTTP Download Logic (Optional) ---
    def _perform_http_download(self, conn_info, url, target_filename):
        """Attempts HTTP download, verifies, DELETES file, updates counters."""
        conn_id = conn_info['id']
        timestamp_ms = int(time.time()*1000)
        # Create a safe temp filename for the download
        safe_base = "".join(c for c in os.path.basename(target_filename) if c.isalnum() or c in ('.', '_', '-')).rstrip()
        local_filename = f"http_dl_{conn_id}_{safe_base}_{timestamp_ms}.tmp"
        local_filepath = os.path.join(self.storage_dir, local_filename)

        downloaded_bytes = 0
        conn_info["http_attempts"] += 1
        self._increment_counter("http_download_attempts")

        headers = {'User-Agent': 'CSBandwidthTester/1.1'} # Basic UA

        try:
            conn_info["status"] = "http_downloading"
            conn_info["last_activity_time"] = time.time()
            if self.verbose: logger.debug(f"Worker {conn_id}: GET {url}")

            with self.http_session.get(url, stream=True, timeout=HTTP_TIMEOUT, headers=headers) as response:
                if self.verbose: logger.debug(f"Worker {conn_id}: HTTP Status {response.status_code} for {url}")
                response.raise_for_status() # Raise HTTPError for 4xx/5xx

                with open(local_filepath, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        if self._stop_event.is_set(): raise InterruptedError("Stop event")
                        if chunk:
                            f.write(chunk)
                            chunk_len = len(chunk)
                            downloaded_bytes += chunk_len
                            self._increment_counter("bytes_received_http", chunk_len)
                            conn_info["bytes_received"] += chunk_len # Track per worker too
                            conn_info["last_activity_time"] = time.time()

            # --- Verification (File exists) ---
            conn_info["status"] = "http_verifying"
            if not os.path.exists(local_filepath):
                raise FileNotFoundError(f"Downloaded file missing post-stream: {local_filepath}")

            # Optional: Size check
            content_length = response.headers.get('content-length')
            if content_length and int(content_length) != downloaded_bytes:
                 mismatch_msg = f"Size mismatch Exp={content_length}, Got={downloaded_bytes}"
                 # Log warning but don't necessarily fail the download just for this
                 self._log_activity_event(conn_id, "HTTP Download", "SIZE_WARN", url, downloaded_bytes, mismatch_msg, detail=f"Path: {local_filepath}")

            # --- Success ---
            conn_info["http_successes"] += 1
            self._increment_counter("http_download_successes")
            self._log_activity_event(conn_id, "HTTP Download", "SUCCESS", url, downloaded_bytes, detail=f"Saved temporarily to {local_filepath}")
            return True # Return success *before* deletion

        # --- Exception Handling ---
        except requests.exceptions.Timeout as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "HTTP Download", "TIMEOUT", url, downloaded_bytes, f"{type(e).__name__}")
             conn_info["status"] = "timeout"; return False
        except requests.exceptions.ConnectionError as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "HTTP Download", "CONN_ERR", url, downloaded_bytes, f"{type(e).__name__}")
             conn_info["status"] = "error"; return False
        except requests.exceptions.HTTPError as e:
             self._increment_counter("http_download_failures")
             status_code = e.response.status_code
             self._log_activity_event(conn_id, "HTTP Download", f"HTTP_{status_code}", url, downloaded_bytes, f"{type(e).__name__}")
             conn_info["status"] = "http_error"; return False
        except InterruptedError:
             self._log_activity_event(conn_id, "HTTP Download", "INTERRUPT", url, downloaded_bytes, "Test stopped")
             conn_info["status"] = "stopped"; return False
        except FileNotFoundError as e: # Catch verification failure
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "HTTP Download", "VERIFY_FAIL", url, downloaded_bytes, str(e))
             conn_info["status"] = "error"; return False
        except Exception as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "HTTP Download", "FAILED", url, downloaded_bytes, f"{type(e).__name__}: {str(e)}")
             logger.error(f"Worker {conn_id}: Unhandled HTTP download error for {url}: {e}", exc_info=self.verbose)
             conn_info["status"] = "error"; return False
        finally:
            # --- Cleanup: ALWAYS attempt deletion if requested ---
            if self.delete_after_download and os.path.exists(local_filepath):
                try:
                    os.remove(local_filepath)
                    self._log_activity_event(conn_id, "HTTP Cleanup", "DELETED", url, detail=f"Path: {local_filepath}")
                except Exception as e:
                     self._log_activity_event(conn_id, "HTTP Cleanup", "DELETE_FAIL", url, error_msg=str(e), detail=f"Path: {local_filepath}")
            elif not self.delete_after_download and os.path.exists(local_filepath):
                 logger.debug(f"Worker {conn_id}: Keeping downloaded file (delete not requested): {local_filepath}")


    # --- Simulation Logic (Optional Fallback) ---
    def _simulate_asset_download(self, conn_info):
        """Simulates download by sending UDP and incrementing counters."""
        # This function comes from the *original* script, adapted slightly
        conn_id = conn_info['id']
        sock = conn_info.get("socket")
        if not sock:
            logger.warning(f"Worker {conn_id}: No UDP socket for simulation, attempting recreate.")
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); sock.settimeout(2.0)
                conn_info['socket'] = sock
                logger.info(f"Worker {conn_id}: Recreated UDP socket for simulation.")
            except Exception as e:
                logger.error(f"Worker {conn_id}: FAILED recreate socket: {e}. Stopping worker.")
                conn_info['status'] = "error"; self._increment_counter("runtime_connection_issues"); return False

        conn_info["sim_attempts"] += 1
        try:
            conn_info["status"] = "sim_running"
            conn_info["last_activity_time"] = time.time()

            # --- Select simulated asset ---
            asset_type = random.choice(list(DOWNLOAD_SIZES.keys()))
            asset_size = DOWNLOAD_SIZES[asset_type] # The size we will *simulate* receiving
            asset_id = f"{asset_type}_{random.randint(1000,9999)}" # Unique ID for logging

            # --- Send a trigger UDP packet ---
            base_request = random.choice(CS_FILE_REQUESTS)
            # Maybe add asset_id to request? Not strictly needed for simulation.
            request = base_request + f" simulate_{asset_id}\x00".encode()
            sent_bytes = sock.sendto(request, (self.server_ip, self.server_port))

            self._increment_counter("udp_requests_sent_sim", 1)
            conn_info["bytes_sent"] += sent_bytes # Track UDP bytes sent
            conn_info["requests_sent"] += 1

            # --- Simulate Receiving Data ---
            # NO ACTUAL sock.recv() here for the bulk data
            simulated_bytes_received_for_asset = 0
            remaining_size = asset_size
            while remaining_size > 0 and self.active and not self._stop_event.is_set():
                bytes_this_chunk = min(4096, remaining_size, random.randint(1024, 4096))
                # --- Update SIMULATED bandwidth counters ---
                self._increment_counter("bytes_received_sim", bytes_this_chunk)
                conn_info["bytes_received"] += bytes_this_chunk # Add to worker's total
                simulated_bytes_received_for_asset += bytes_this_chunk
                remaining_size -= bytes_this_chunk
                conn_info["last_activity_time"] = time.time()

                # Apply delay based on simulated chunk size
                if self.download_delay > 0:
                     chunk_delay = self.download_delay / (asset_size / bytes_this_chunk) if asset_size > 0 else 0.001
                     time.sleep(max(0.001, chunk_delay))
                # Maybe send occasional ping?
                if random.random() < 0.02:
                     try: sock.sendto(b"\xff\xff\xff\xffping\x00", (self.server_ip, self.server_port))
                     except Exception: pass # Ignore errors

                if self._stop_event.is_set(): break # Check stop event within loop

            if self._stop_event.is_set():
                 self._log_activity_event(conn_id, "SIM Download", "INTERRUPT", asset_id, simulated_bytes_received_for_asset, "Test stopped")
                 conn_info["status"] = "stopped"; return False

            if remaining_size <= 0:
                 # --- Simulation Success ---
                 self._increment_counter("simulated_downloads_count")
                 self._log_activity_event(conn_id, "SIM Download", "SUCCESS", asset_id, simulated_bytes_received_for_asset)
                 return True
            else:
                 # Should only happen if loop exited unexpectedly without stop event?
                 self._log_activity_event(conn_id, "SIM Download", "INCOMPLETE", asset_id, simulated_bytes_received_for_asset)
                 conn_info["status"] = "error"; return False


        except socket.timeout:
             self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "SIM Download", "TIMEOUT", asset_id, 0, "UDP Send Timeout")
             conn_info["status"] = "timeout"; return False
        except OSError as e:
             self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "SIM Download", "OS_ERROR", asset_id, 0, str(e))
             logger.error(f"Worker {conn_id} OS Error: {e}. Closing socket.")
             try: sock.close(); conn_info["socket"] = None
             except Exception: pass
             conn_info["status"] = "error"; return False
        except Exception as e:
             self._increment_counter("runtime_connection_issues")
             self._log_activity_event(conn_id, "SIM Download", "FAILED", asset_id, 0, f"{type(e).__name__}: {str(e)}")
             logger.error(f"Worker {conn_id} unexpected error during simulation: {e}", exc_info=self.verbose)
             conn_info["status"] = "error"; return False


    # --- Worker Thread ---
    def _connection_worker(self, conn_info):
        """Worker thread: performs HTTP downloads if FastDL URL is set, otherwise simulates."""
        conn_id = conn_info['id']
        mode = "HTTP" if self.active_fastdl_url else "SIMULATION"
        if self.verbose: logger.debug(f"Worker {conn_id}: Started in {mode} mode.")
        self._increment_counter("active_workers_count")

        try:
            while self.active and not self._stop_event.is_set():
                success = False
                # --- Decide Mode ---
                if self.active_fastdl_url:
                    # --- HTTP Download Mode ---
                    file_rel_path = self._get_file_to_download_http()
                    if file_rel_path:
                        try:
                            # Construct full URL (handle potential double slashes, etc.)
                            full_url = urljoin(self.active_fastdl_url, file_rel_path.replace('\\', '/'))
                            success = self._perform_http_download(conn_info, full_url, file_rel_path)
                        except Exception as url_err: # Catch errors in urljoin or path handling
                             self._increment_counter("http_download_failures")
                             self._log_activity_event(conn_id, "HTTP Download", "URL_ERROR", file_rel_path, error_msg=str(url_err))
                             conn_info["status"] = "error" # Mark worker as error state
                    else:
                        # No file available (map unknown and list empty/exhausted?)
                        logger.debug(f"Worker {conn_id}: No HTTP file available, sleeping.")
                        time.sleep(1.5) # Wait a bit longer
                        continue # Skip to next loop iteration

                else:
                    # --- Simulation Mode ---
                    success = self._simulate_asset_download(conn_info)

                # Wait before next attempt
                delay_base = 0.05 if success else 0.2 # Quick retry on success, slower on fail
                worker_delay = random.uniform(delay_base, delay_base + 0.1)
                time.sleep(worker_delay)

        except Exception as e:
            logger.error(f"Worker {conn_id}: Unhandled loop error: {e}", exc_info=self.verbose)
            conn_info["status"] = "error"
            self._increment_counter("runtime_connection_issues")
        finally:
            self._decrement_counter("active_workers_count")
            conn_info["status"] = "stopped"
            # Clean up worker's UDP socket if it exists
            sock = conn_info.get("socket")
            if sock:
                try: sock.close()
                except Exception: pass
            if self.verbose: logger.debug(f"Worker {conn_id}: Finished. Mode={mode}. Received={conn_info['bytes_received']/1024:.1f}KB")


    def _get_file_to_download_http(self):
        """Selects a file path for HTTP download (map or from list)."""
        with self.lock:
            choices = []
            # Add current map if known
            if self.current_map_file_path:
                 choices.append(self.current_map_file_path)
            # Add files from list
            choices.extend(self.files_to_try_http)

            if not choices: return None

            # Weighted choice: prioritize map slightly? Or just random?
            # Let's try random for now.
            return random.choice(choices)


    # --- Server Info Update Thread ---
    def _update_server_info(self):
        """Updates server info (map, rules, fastdl URL) periodically via UDP."""
        if not self.server_query: return
        if self.verbose: logger.debug("Server monitor thread started.")

        query_rules_interval = 30 # How often to query rules (less frequent)
        last_rules_query_time = 0

        while self.active and not self._stop_event.is_set():
            current_status = "UNKNOWN"; ping = -1; map_name = None
            info_success = False

            try:
                # --- Get Server Info (A2S_INFO) ---
                server_info = self.server_query.get_info()
                timestamp = time.time()
                if server_info:
                    info_success = True
                    with self.lock:
                        self.server_info = server_info; self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                        map_name = server_info.get('map')
                        if map_name:
                            self.current_map_file_path = f"maps/{map_name}.bsp"
                        else: self.current_map_file_path = None
                else: # Query failed
                    with self.lock:
                        if self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT):
                             current_status = "OFFLINE"
                        else: current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"
                        self.server_info = None; self.server_status = current_status
                        self.current_map_file_path = None # Clear map if server offline/issues

                # --- Get Server Rules (A2S_RULES) periodically ---
                # Only query rules if info was successful and interval passed and no manual URL set
                if info_success and (time.time() - last_rules_query_time > query_rules_interval) and not self.manual_fastdl_url:
                    logger.debug("Querying server rules...")
                    last_rules_query_time = time.time()
                    rules = self.server_query.get_rules()
                    if rules:
                         with self.lock:
                             self.server_rules = rules
                             # Discover FastDL URL from rules
                             dl_url = rules.get('sv_downloadurl')
                             if dl_url:
                                 # Basic validation/cleanup
                                 dl_url = dl_url.strip()
                                 if dl_url.startswith('http://') or dl_url.startswith('https://'):
                                      # Ensure trailing slash
                                      self.discovered_fastdl_url = dl_url if dl_url.endswith('/') else dl_url + '/'
                                      if self.active_fastdl_url != self.discovered_fastdl_url:
                                            logger.info(f"Discovered FastDL URL via rules: {self.discovered_fastdl_url}")
                                            # Update active URL only if no manual one was set
                                            if not self.manual_fastdl_url:
                                                 self.active_fastdl_url = self.discovered_fastdl_url
                                 else:
                                      logger.warning(f"Rule 'sv_downloadurl' has invalid format: {dl_url}")
                                      self.discovered_fastdl_url = None
                             else:
                                  logger.debug("Rule 'sv_downloadurl' not found.")
                                  self.discovered_fastdl_url = None
                                  # If discovery fails and no manual URL, clear active URL
                                  if not self.manual_fastdl_url: self.active_fastdl_url = None
                    else:
                         logger.debug("Failed to get server rules.")
                         with self.lock:
                             self.server_rules = None
                             self.discovered_fastdl_url = None
                             if not self.manual_fastdl_url: self.active_fastdl_url = None


            except Exception as e: # Catch unexpected errors in this thread
                logger.error(f"Unexpected server info/rules error: {e}", exc_info=self.verbose)
                with self.lock:
                    current_status = "ERROR"; self.server_info = None; self.server_status = current_status
                    self.current_map_file_path = None; self.server_rules = None
                    self.discovered_fastdl_url = None;
                    if not self.manual_fastdl_url: self.active_fastdl_url = None

            # --- Log Status ---
            status_log_entry = {'timestamp': time.time(), 'status': current_status, 'ping': ping, 'map': map_name}
            with self.lock: self.server_status_log.append(status_log_entry)

            # Wait before next query, check stop event frequently
            sleep_interval = 0.1
            sleep_end = time.time() + self.server_info_interval
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval): break # Exit inner loop
            if self._stop_event.is_set(): break # Exit outer loop

        if self.server_query: self.server_query.close()
        if self.verbose: logger.debug("Server monitor thread finished.")


    # --- Realtime Display Thread ---
    def _display_realtime_stats(self):
        """Displays real-time stats (HTTP or Simulation based)."""
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time

        CURSOR_TO_HOME = "\033[H"; CLEAR_LINE = "\033[K"; CLEAR_SCREEN_FROM_CURSOR = "\033[J"
        term_width = 80
        try: term_width = os.get_terminal_size().columns
        except OSError: logger.warning("Could not detect terminal width, using 80."); term_width = 80

        while self.active and not self._stop_event.is_set():
            lines_to_print = []
            try:
                # Gather current stats under lock
                with self.lock:
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    # Counters
                    bytes_http = self.bytes_received_http; http_ok = self.http_download_successes
                    http_fail = self.http_download_failures
                    bytes_sim = self.bytes_received_sim; sim_ok = self.simulated_downloads_count
                    active_workers = self.active_workers_count; runtime_issues = self.runtime_connection_issues
                    initial_fails = self.initial_connection_failures
                    # Server Status
                    current_server_status = self.server_status
                    current_map_path = self.current_map_file_path
                    current_ping = self.server_info.get('ping', -1) if self.server_info else -1
                    # Mode & URLs
                    current_mode = "HTTP" if self.active_fastdl_url else "Simulation"
                    display_fastdl_url = self.active_fastdl_url if self.active_fastdl_url else "N/A (Simulation Mode)"
                    # Activity
                    last_activity = list(self.last_activity)

                # Calculate derived stats outside lock
                recv_http_mb = bytes_http / (1024*1024); recv_sim_mb = bytes_sim / (1024*1024)
                total_recv_mb = recv_http_mb + recv_sim_mb # Combined effective MB
                avg_rate_mbs = total_recv_mb / elapsed if elapsed > 0 else 0

                # Log bandwidth point periodically (combined rate)
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                     with self.lock: self.bandwidth_log_points.append((elapsed, total_recv_mb))
                     last_bw_log_time = current_time

                # --- Format Output Lines ---
                status = "Running" if self.active else "Stopped"
                mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                header = f"--- CS 1.6 Bandwidth Test ({self.server_ip}:{self.server_port} | Mode: {current_mode}) ---".center(term_width)
                lines_to_print.append(header)

                line_status = f" Status: {status} | Test Mode: {mode}"
                line_time = f"Time: {elapsed:.1f}s"
                lines_to_print.append(f"{line_status:<{max(0, term_width - len(line_time))}}{line_time}")

                line_workers = f" Workers: {active_workers}/{self.num_connections}"
                line_issues = f"Issues: Init={initial_fails} Run={runtime_issues}"
                lines_to_print.append(f"{line_workers:<{max(0, term_width - len(line_issues))}}{line_issues}")

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Server Status (UDP Query)]".center(term_width))
                if self.no_server_monitor:
                     lines_to_print.append(" UDP Monitoring Disabled".ljust(term_width))
                     lines_to_print.append(f" Current Map: UNKNOWN".ljust(term_width))
                else:
                    s_status_str = f" Status: {current_server_status}"
                    s_ping_str = f"Ping: {current_ping:>3}ms" if current_ping >= 0 else "Ping: N/A"
                    s_map_str = f"Map Path: {current_map_path if current_map_path else 'UNKNOWN'}"

                    width_status = len(s_status_str)
                    width_ping = len(s_ping_str)
                    spaces1 = max(1, (term_width - width_status - width_ping) // 2)
                    lines_to_print.append(f"{s_status_str}{' '*spaces1}{s_ping_str}".ljust(term_width))
                    lines_to_print.append(s_map_str[:term_width].ljust(term_width)) # Truncate map path

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Download Activity]".center(term_width))
                lines_to_print.append(f" Active FastDL URL: {display_fastdl_url[:term_width-20]}".ljust(term_width)) # Truncate URL

                # Display HTTP stats if run
                if http_ok > 0 or http_fail > 0 or bytes_http > 0:
                     line_http_stats = f" HTTP Recv: {recv_http_mb:>7.2f} MB | OK: {http_ok} Fail: {http_fail}"
                     lines_to_print.append(line_http_stats.ljust(term_width))
                # Display Simulation stats if run
                if sim_ok > 0 or bytes_sim > 0:
                     line_sim_stats = f" SIM Recv:  {recv_sim_mb:>7.2f} MB | OK: {sim_ok}"
                     lines_to_print.append(line_sim_stats.ljust(term_width))

                # Combined Rate
                lines_to_print.append(f" Avg Total Rate: {avg_rate_mbs:>6.2f} MB/s".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append(f"[Last {LAST_FILES_DISPLAY_COUNT} Activities (HTTP/SIM)]".center(term_width))
                if last_activity:
                    for activity in reversed(last_activity): # Show newest first
                        lines_to_print.append(f" {activity[:term_width-2]}".ljust(term_width)) # Truncate long entries
                    # Pad if needed
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_activity))):
                        lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No download/simulation activity yet)".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT -1)):
                       lines_to_print.append(" ".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("(Press Ctrl+C to stop)".center(term_width))

                # --- Perform Screen Update ---
                output_buffer = CURSOR_TO_HOME
                for line in lines_to_print:
                    output_buffer += line[:term_width] + CLEAR_LINE + "\n" # Ensure line truncation
                output_buffer += CLEAR_SCREEN_FROM_CURSOR
                sys.stdout.write(output_buffer)
                sys.stdout.flush()

            except Exception as e:
                logger.error(f"Error in display thread: {e}", exc_info=False)
                time.sleep(1) # Pause briefly on error

            # Wait before next update
            sleep_interval = 0.1
            sleep_end = time.time() + UI_UPDATE_INTERVAL
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval): break
            if self._stop_event.is_set(): break # Exit outer loop

        if self.verbose: logger.debug("Realtime display thread finished.")
        # Clear screen one last time before final report
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
        sys.stdout.flush()

    # --- Start/Stop Methods ---
    def start_test(self):
        if self.active: logger.warning("Test is already running."); return

        # Determine active FastDL URL (Manual > Discovered > None)
        if not self.manual_fastdl_url and not self.no_server_monitor:
            # Try initial rules query if no manual URL and monitoring enabled
            logger.info("No manual FastDL URL, attempting initial rules query...")
            try:
                 if not self.server_query: # Should exist if no_server_monitor is false
                     self.server_query = ServerQuery(self.server_ip, self.server_port, self.storage_dir)
                 rules = self.server_query.get_rules()
                 if rules:
                     dl_url = rules.get('sv_downloadurl', '').strip()
                     if dl_url and (dl_url.startswith('http://') or dl_url.startswith('https://')):
                          self.discovered_fastdl_url = dl_url if dl_url.endswith('/') else dl_url + '/'
                          self.active_fastdl_url = self.discovered_fastdl_url
                          logger.info(f"Using discovered FastDL URL: {self.active_fastdl_url}")
                     else: logger.info("sv_downloadurl not found or invalid in initial query.")
                 else: logger.info("Initial rules query failed.")
            except Exception as e: logger.error(f"Initial rules query error: {e}")
        elif self.manual_fastdl_url:
             self.active_fastdl_url = self.manual_fastdl_url
             logger.info(f"Using manually specified FastDL URL: {self.active_fastdl_url}")
        else:
             logger.info("No FastDL URL specified or discovered. Running in Simulation mode.")
             self.active_fastdl_url = None


        logger.info("="*30 + f" Starting Test (Mode: {'HTTP' if self.active_fastdl_url else 'Simulation'}) " + "="*30)
        self.active = True
        self._stop_event.clear()
        self.start_time = time.time()
        self.end_time = 0

        # Reset counters
        self.bytes_received_http = 0; self.http_download_attempts = 0; self.http_download_successes = 0; self.http_download_failures = 0
        self.bytes_received_sim = 0; self.simulated_downloads_count = 0; self.udp_requests_sent_sim = 0
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0; self.server_status_log = []
        self.last_activity.clear(); self.bandwidth_log_points = []
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0; self.server_info = None; self.current_map_file_path = None
        self.server_rules = None # Reset rules


        self.threads = []

        # Start UDP server monitor first (gets map, rules, potentially FastDL URL)
        if not self.no_server_monitor and self.server_query:
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start()
            self.threads.append(self.server_info_thread)
            time.sleep(0.2) # Small delay for monitor to potentially start

        # Start display thread
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread)

        # Start worker threads
        logger.info(f"Starting {self.num_connections} workers...")
        self.connections = [] # Clear previous connection info structs
        initial_success = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set(): break
            # Create worker structure (includes UDP socket setup attempt for simulation mode)
            conn_info = self._create_connection(i + 1)
            if conn_info:
                 self.connections.append(conn_info)
                 worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
                 worker_thread.start()
                 self.threads.append(worker_thread)
                 initial_success += 1
            else:
                 self._increment_counter("initial_connection_failures") # If _create_connection fails
            if self.num_connections > 20 and (i + 1) % 20 == 0: time.sleep(0.05) # Stagger large numbers

        logger.info(f"Launched {initial_success} workers. Initial Fails: {self.initial_connection_failures}")

        if initial_success == 0 and self.num_connections > 0:
             logger.error("FATAL: No worker connections could be started. Stopping test.")
             # Need to signal stop and potentially join display/monitor threads if they started
             threading.Thread(target=self.stop_test).start() # Stop in separate thread to avoid deadlock
             return


        # Main loop waits for duration or stop signal
        try:
            if self.continuous_mode:
                self._stop_event.wait()
                logger.info("Stop event received, finishing...")
            else:
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early: logger.info("Test stopped early via signal.")
                else: logger.info("Test duration reached."); self.stop_test()

        except Exception as e:
             logger.error(f"Error in main test execution: {e}")
             self.stop_test() # Ensure cleanup on error

    def stop_test(self):
        if not self.active: return
        # Prevent double execution if called rapidly
        if self._stop_event.is_set(): return

        logger.info("Stopping test...")
        self.active = False
        self._stop_event.set() # Signal all threads
        self.end_time = time.time() if self.start_time > 0 else time.time()

        logger.info("Waiting for threads to complete...")
        join_timeout = 5.0

        # Gracefully join threads
        threads_to_join = self.threads[:]
        for thread in threads_to_join:
             if thread is threading.current_thread() or not thread.is_alive(): continue
             try:
                 if self.verbose: logger.debug(f"Joining thread: {thread.name}...")
                 thread.join(join_timeout)
                 if thread.is_alive(): logger.warning(f"Thread {thread.name} did not stop within timeout.")
             except Exception as e: logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("All threads processed.")

        # Close resources
        if self.server_query: self.server_query.close()
        self.http_session.close()
        # Close UDP sockets held by workers (should be closed in worker finally block, but belt-and-suspenders)
        for conn_info in self.connections:
             sock = conn_info.get("socket")
             if sock:
                 try: sock.close()
                 except Exception: pass
        # Close activity log file handler
        if activity_logger and activity_logger.handlers:
             try:
                 activity_logger.handlers[0].stream.write(f"--- Activity Log Ended ({datetime.now().isoformat()}) ---\n")
                 activity_logger.handlers[0].close()
                 activity_logger.removeHandler(activity_logger.handlers[0])
             except Exception as e:
                  logger.warning(f"Error closing activity log handler: {e}")

        # Final Report
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed)

        logger.info("Test finished.")


    # --- Reporting Methods ---
    def _generate_final_report(self, duration):
        print("\n" + "="*30 + " Test Results Summary " + "="*30)
        duration = max(duration, 0.01)

        # Get final stats under lock
        with self.lock:
            bytes_http = self.bytes_received_http; http_ok = self.http_download_successes; http_fail = self.http_download_failures
            bytes_sim = self.bytes_received_sim; sim_ok = self.simulated_downloads_count
            runtime_issues = self.runtime_connection_issues; initial_fails = self.initial_connection_failures
            final_server_status = self.server_status
            final_map = self.current_map_file_path or "UNKNOWN"
            server_log = self.server_status_log[:]
            mode_run = "HTTP" if self.active_fastdl_url else "Simulation"

        # Calculate final rates
        recv_http_mb = bytes_http / (1024*1024); recv_sim_mb = bytes_sim / (1024*1024)
        total_recv_mb = recv_http_mb + recv_sim_mb
        avg_rate_mbs = total_recv_mb / duration

        # Calculate avg ping
        avg_ping = -1; min_ping = -1; max_ping = -1
        if not self.no_server_monitor:
             pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
             if pings: avg_ping = sum(pings)/len(pings); min_ping = min(pings); max_ping = max(pings)

        print(f"[Test Overview]")
        print(f" Target Server:   {self.server_ip}:{self.server_port}")
        print(f" Mode Executed:   {mode_run}")
        print(f" FastDL URL Used: {self.active_fastdl_url if self.active_fastdl_url else 'N/A'}")
        print(f" Duration:        {duration:.2f}s")
        print(f" Config Workers:  {self.num_connections}")
        print(f" Initial Fails:   {initial_fails}")
        print(f" Runtime Issues:  {runtime_issues}")

        if bytes_http > 0 or http_ok > 0 or http_fail > 0:
             print("\n[HTTP Download Results]")
             print(f" Files OK:        {http_ok}")
             print(f" Files Failed:    {http_fail} (Check {self.activity_log_filename})")
             print(f" Received (HTTP): {recv_http_mb:.2f} MB")
             if self.delete_after_download: print(f" Files Deleted:   Yes")

        if bytes_sim > 0 or sim_ok > 0:
             print("\n[Simulation Results]")
             print(f" Sim OK:          {sim_ok}")
             print(f" Received (Sim):  {recv_sim_mb:.2f} MB")
             print(f" Sim Delay Param: {self.download_delay}")

        print("\n[Bandwidth Summary]")
        print(f" Total Received:  {total_recv_mb:.2f} MB (HTTP + Sim)")
        print(f" Avg Total Rate:  {avg_rate_mbs:.2f} MB/s")

        print("\n[Server Status (UDP Query)]")
        if self.no_server_monitor: print(" Monitoring:      Disabled")
        else:
            print(f" Final Status:    {final_server_status}")
            print(f" Last Known Map:  {final_map}")
            print(f" Avg Ping:        {avg_ping:.1f} ms" if avg_ping != -1 else "N/A")
            print(f" Ping Min/Max:    {min_ping} / {max_ping} ms" if min_ping != -1 else "N/A")

        print("="*60)

    def _save_detailed_report_json(self, duration):
         with self.lock:
             duration = max(0.01, duration)
             bytes_http = self.bytes_received_http; http_ok = self.http_download_successes; http_fail = self.http_download_failures
             bytes_sim = self.bytes_received_sim; sim_ok = self.simulated_downloads_count
             total_recv_mb = (bytes_http + bytes_sim) / (1024*1024)
             avg_rate_mbs = total_recv_mb / duration
             server_log = self.server_status_log[:]
             mode_run = "HTTP" if self.active_fastdl_url else "Simulation"

         report_data = {
            "test_info": {
                "test_type": "CS_Bandwidth_Test",
                "execution_mode": mode_run,
                "target_server": f"{self.server_ip}:{self.server_port}",
                "fastdl_url_used": self.active_fastdl_url,
                "timestamp_utc": datetime.utcnow().isoformat() + "Z",
                "duration_seconds": round(duration, 2),
                "configured_workers": self.num_connections,
                "initial_connection_failures": self.initial_connection_failures,
                "runtime_connection_issues": self.runtime_connection_issues,
                "test_run_mode": "Continuous" if self.continuous_mode else "Timed",
                "server_udp_monitoring": not self.no_server_monitor,
                "verbose_logging": self.verbose,
            },
            "bandwidth_summary": {
                "total_received_mb": round(total_recv_mb, 3),
                "avg_total_rate_mbs": round(avg_rate_mbs, 3),
                "http_received_mb": round(bytes_http / (1024*1024), 3),
                "simulated_received_mb": round(bytes_sim / (1024*1024), 3),
                "bandwidth_log_points_sec_mb": [(round(t, 2), round(mb, 3)) for t, mb in self.bandwidth_log_points],
            },
            "http_download_stats": { # Only relevant if HTTP mode ran
                "files_attempted": self.http_download_attempts,
                "files_succeeded": http_ok,
                "files_failed_or_skipped": http_fail,
                "delete_after_download": self.delete_after_download,
                "file_list_used": self.file_list_path,
            } if mode_run == "HTTP" else None,
             "simulation_stats": { # Only relevant if Simulation mode ran
                 "simulations_completed": sim_ok,
                 "simulated_download_delay_param": self.download_delay,
                 "udp_requests_sent_by_sim": self.udp_requests_sent_sim,
            } if mode_run == "Simulation" else None,
            "server_status_log": server_log
         }
         # Remove None sections for cleaner output
         report_data = {k: v for k, v in report_data.items() if v is not None}

         ts = int(time.time())
         report_filename = f"cs_bw_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts}.json"
         report_filepath = os.path.join(self.storage_dir, report_filename)

         try:
            with open(report_filepath, 'w') as f: json.dump(report_data, f, indent=2)
            logger.info(f"Detailed JSON report saved to: {report_filepath}")
         except Exception as e:
            logger.error(f"Failed to save JSON report '{report_filepath}': {e}")


# ==============================================================
# Signal Handling
# ==============================================================
def signal_handler(sig, frame):
    global tester_instance
    if tester_instance and tester_instance.active:
        if not tester_instance._stop_event.is_set():
            print('\n') # Move cursor
            logger.warning("Ctrl+C received! Initiating graceful shutdown...")
            # Run stop in a thread to avoid blocking signal handler
            threading.Thread(target=tester_instance.stop_test, daemon=True).start()
    else:
        print('\nCtrl+C received, but no active test found or test stopping. Exiting.')
        # Attempt to close log file if tester instance not available/active
        handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
        if handler:
             try: handler.close()
             except: pass
        sys.exit(0)

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 Server Bandwidth/Query Test Tool (HTTP or Simulation)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    # --- Essential Arguments ---
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 GAME server.")

    # --- Optional Arguments ---
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="GAME server UDP port.")
    # Make FastDL optional
    parser.add_argument("--fastdl-url", default=None, help="Base URL of the server's FastDL repository (e.g., http://my.fastdl.com/cs/). If provided, enables HTTP download mode. Otherwise, runs in simulation mode.")
    parser.add_argument("-c", "--connections", type=int, default=10, help="Number of concurrent workers (HTTP or Simulation).")
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of timed test in seconds.")
    parser.add_argument("--storage-dir", default="cs_test_data", help="Directory for logs, reports, and temporary files (UDP verify, HTTP tmp).")
    parser.add_argument("--activity-log", default=DOWNLOAD_LOG_FILENAME, help="Filename for logging download/simulation/UDP verify activity details.")
    # Simulation specific
    parser.add_argument("--delay", type=float, default=0.01, help="[Simulation Mode] Simulated delay factor per asset chunk (lower is faster). Ignored in HTTP mode.")
    # HTTP specific
    parser.add_argument("--file-list", help="[HTTP Mode] Path to text file with relative asset paths to download (e.g., maps/de_dust2.bsp).")
    parser.add_argument("--delete-after-download", action="store_true", help="[HTTP Mode] Delete temporary HTTP files immediately after successful download and verification.")
    # General options
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging.")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run continuously until stopped (Ctrl+C). Overrides --duration.")
    parser.add_argument("--no-server-monitor", action="store_true", help="Disable querying game server status via UDP (no map/rules/ping info, no FastDL discovery).")

    args = parser.parse_args()

    # --- Configure Logging Level ---
    if args.verbose: logger.setLevel(logging.DEBUG); activity_logger.setLevel(logging.DEBUG)
    else: logger.setLevel(logging.INFO); activity_logger.setLevel(logging.INFO)

    # --- Display Warnings ---
    logger.warning("="*70)
    if args.fastdl_url:
        logger.warning("⚠️ HTTP DOWNLOAD MODE ENABLED ⚠️")
        logger.warning("This script WILL perform REAL file downloads from the specified FastDL URL.")
        logger.warning("This consumes bandwidth and resources. Ensure you have PERMISSION.")
    else:
        logger.warning("⚠️ SIMULATION MODE ENABLED ⚠️")
        logger.warning("No FastDL URL provided. Bandwidth figures will be SIMULATED.")
        logger.warning("Script will primarily send UDP query packets.")
    logger.warning("You are SOLELY responsible for the use of this tool. Use ethically.")
    logger.warning("="*70)
    time.sleep(2.0)

    try:
        # Ensure storage dir exists before initializing tester
        if not os.path.exists(args.storage_dir):
            try: os.makedirs(args.storage_dir); logger.info(f"Created base directory: {args.storage_dir}")
            except OSError as e: logger.warning(f"Cannot create storage directory '{args.storage_dir}': {e}. Logs/temps might fail.")

        tester_instance = CS16BandwidthTester(
            server_ip=args.server_ip,
            server_port=args.port,
            num_connections=args.connections,
            test_duration=args.duration,
            download_delay=args.delay, # Pass simulation delay
            verbose=args.verbose,
            storage_dir=args.storage_dir,
            continuous_mode=args.continuous,
            no_server_monitor=args.no_server_monitor,
            fastdl_url=args.fastdl_url, # Pass optional URL
            file_list_path=args.file_list, # Pass optional file list
            delete_after_download=args.delete_after_download, # Pass HTTP delete flag
            activity_log_filename=args.activity_log # Pass log filename
        )

        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)

        tester_instance.start_test()

        # start_test handles waiting in timed/continuous mode
        logger.info("Main thread finished.")
        sys.exit(0)

    except ValueError as e: # Catch specific init errors
         logger.error(f"Configuration Error: {e}")
         sys.exit(1)
    except Exception as e:
        logger.error(f"An critical error occurred: {type(e).__name__} - {str(e)}", exc_info=True)
        sys.exit(1)
    finally:
        # Ensure log file handler is closed on unexpected exit
        handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
        if handler:
             try: handler.close()
             except: pass
