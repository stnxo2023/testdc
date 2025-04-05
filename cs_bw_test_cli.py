#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Script focuses on UDP Interaction + Simulation when no FastDL URL is given.
# Includes UDP Response Verification (Save/Delete).

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
# requests is included but only used if --fastdl-url IS provided
import requests
from urllib.parse import urljoin

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150 # ms
SERVER_OFFLINE_TIMEOUT = 15 # seconds without response
LAST_FILES_DISPLAY_COUNT = 10 # How many recent events to show
UI_UPDATE_INTERVAL = 0.5 # How often to refresh the terminal stats (seconds)
# Simulation constants (used if --fastdl-url is not provided)
CS_FILE_REQUESTS = [ # Base UDP requests for simulation trigger
    b"\xff\xff\xff\xffrcon", b"\xff\xff\xff\xffping\x00",
    b"\xff\xff\xff\xffdetails\x00", b"\xff\xff\xff\xffplayers\x00",
    b"\xff\xff\xff\xffrules\x00", b"\xff\xff\xff\xffchallenge\x00",
]
DOWNLOAD_SIZES = { "map": 5*1024*1024, "model": 1*1024*1024, "sound": 256*1024, "sprite": 64*1024, "texture": 512*1024, "other": 128*1024 }
# Log/Temp file config
ACTIVITY_LOG_FILENAME = "activity_log.txt"
UDP_VERIFY_FILENAME_PREFIX = "udp_verify_"
HTTP_TIMEOUT = 15 # For optional HTTP mode

# --- Global logger setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr
)
logger = logging.getLogger('cs_udp_simulator')

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
            self.sock = None; raise

    def _log_activity(self, level, message):
        """Helper to log to both main logger and activity file logger."""
        logger.log(level, message)
        # Ensure activity logger is configured before writing
        if activity_logger.hasHandlers():
            activity_logger.log(level, message)
        elif level >= logging.WARNING: # Log errors/warnings to main log if file log failed
             logger.log(level, f"[Activity Log Disabled] {message}")

    # --- MODIFIED: _send_recv includes UDP save/verify/delete ---
    def _send_recv(self, request, query_type="unknown"):
        if self.sock is None:
            try: self._create_socket()
            except Exception: return None, 0

        start_time = time.time()
        response = None; ping = 0
        for attempt in range(self.retry_count):
            try:
                logger.debug(f"Sending UDP {query_type} query (attempt {attempt+1})...")
                self.sock.sendto(request, (self.server_ip, self.server_port))
                response, addr = self.sock.recvfrom(4096)
                end_time = time.time()
                ping = int((end_time - start_time) * 1000)

                if response:
                    logger.debug(f"UDP response received from {addr} for {query_type} ({len(response)} bytes).")
                    # --- UDP Verification: Save and Delete ---
                    # Ensure storage dir exists for verification files
                    if not os.path.exists(self.storage_dir):
                         try: os.makedirs(self.storage_dir)
                         except OSError: pass # Ignore error if it already exists or fails

                    verify_filename = f"{UDP_VERIFY_FILENAME_PREFIX}{query_type}_{int(time.time()*1000)}.bin"
                    verify_filepath = os.path.join(self.storage_dir, verify_filename)
                    saved_ok = False
                    verify_msg_prefix = f"[UDP Verify] Query: {query_type}"
                    try:
                        with open(verify_filepath, 'wb') as vf: vf.write(response)
                        saved_ok = True
                        self._log_activity(logging.INFO, f"{verify_msg_prefix} | Status: SAVED | Bytes: {len(response)} | Path: {verify_filepath}")
                    except Exception as e:
                        self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: SAVE_FAILED | Path: {verify_filepath} | Error: {e}")
                    finally:
                        if os.path.exists(verify_filepath):
                            try:
                                os.remove(verify_filepath)
                                if saved_ok: self._log_activity(logging.INFO, f"{verify_msg_prefix} | Status: DELETED | Path: {verify_filepath}")
                            except Exception as e: self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: DELETE_FAILED | Path: {verify_filepath} | Error: {e}")
                        elif saved_ok: self._log_activity(logging.WARNING, f"{verify_msg_prefix} | Status: DELETE_WARN | Path: {verify_filepath} | File not found after save.")
                    # --- End UDP Verification ---
                    return response, ping
                else: logger.debug(f"Received empty UDP response (attempt {attempt+1}) for {query_type}")

            except socket.timeout:
                logger.debug(f"UDP {query_type} query timed out (attempt {attempt+1})")
                if attempt == self.retry_count - 1: return None, 0
                time.sleep(0.1)
            except OSError as e: logger.warning(f"UDP Query OSError (attempt {attempt+1}): {e}"); self.close(); return None, 0
            except Exception as e: logger.error(f"Unexpected UDP Query Error (attempt {attempt+1}): {e}"); self.close(); return None, 0
        return None, 0

    # --- Getters using _send_recv ---
    def get_info(self):
        request = b"\xFF\xFF\xFF\xFFTSource Engine Query\x00"
        response, ping = self._send_recv(request, query_type="info")
        if response:
            parsed_info = self._parse_info(response)
            if parsed_info:
                self.last_ping = ping; parsed_info['ping'] = ping; self.last_info = parsed_info
                if response[4:5] == b'A': self.last_challenge = response[5:9]
                else: self.last_challenge = None
                return parsed_info
        return None

    def get_rules(self):
        challenge_bytes = self.last_challenge or b'\xFF\xFF\xFF\xFF' # Use last challenge or default
        request = b'\xFF\xFF\xFF\xFFV' + challenge_bytes
        response, _ = self._send_recv(request, query_type="rules")
        if response and response[4:5] == b'E':
             parsed_rules = self._parse_rules(response)
             if parsed_rules: self.last_rules = parsed_rules
             return parsed_rules
        elif response and response[4:5] == b'A': # Got challenge, retry
             self.last_challenge = response[5:9]
             logger.info(f"Received challenge {self.last_challenge.hex()} for rules. Retrying.")
             request = b'\xFF\xFF\xFF\xFFV' + self.last_challenge
             response, _ = self._send_recv(request, query_type="rules_retry")
             if response and response[4:5] == b'E':
                  parsed_rules = self._parse_rules(response)
                  if parsed_rules: self.last_rules = parsed_rules
                  return parsed_rules
        return None

    # --- Parsers (_parse_info, _parse_rules) ---
    # (Keep the parsing logic from the previous combined script)
    def _parse_info(self, response):
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF': return None
            header_byte = response[4:5]; offset = 5
            if header_byte == b'I': # Source
                offset += 1 # Skip protocol
                def read_string(data, start_offset):
                    end = data.find(b'\x00', start_offset);
                    if end == -1: raise ValueError("Malformed string");
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1
                server_name, offset = read_string(response, offset); map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset); game_desc, offset = read_string(response, offset)
                if offset + 9 > len(response): raise ValueError("Too short")
                offset += 2 # Skip AppID
                player_count = response[offset]; offset += 1; max_players = response[offset]; offset += 1; bot_count = response[offset]
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': bot_count}
            elif header_byte == b'm': # GoldSrc
                addr_end = response.find(b'\x00', offset);
                if addr_end == -1: raise ValueError("Malformed address"); offset = addr_end + 1
                def read_string_gs(data, start_offset):
                    end = data.find(b'\x00', start_offset);
                    if end == -1: raise ValueError("Malformed string");
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1
                server_name, offset = read_string_gs(response, offset); map_name, offset = read_string_gs(response, offset)
                game_dir, offset = read_string_gs(response, offset); game_desc, offset = read_string_gs(response, offset)
                if offset + 3 > len(response): raise ValueError("Too short")
                player_count = response[offset]; offset += 1; max_players = response[offset]
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': 0}
            elif header_byte == b'A': return None # Challenge
            else: return None
        except Exception as e: logger.warning(f"Parse INFO error: {e}"); return None

    def _parse_rules(self, response):
        try:
            if not response or len(response) < 7 or response[:5] != b'\xFF\xFF\xFF\xFFE': return None
            rules_count = int.from_bytes(response[5:7], 'little'); offset = 7
            rules = {}
            for _ in range(rules_count):
                name_end = response.find(b'\x00', offset);
                if name_end == -1: raise ValueError("Malformed rule name");
                rule_name = response[offset:name_end].decode('utf-8', errors='ignore'); offset = name_end + 1
                value_end = response.find(b'\x00', offset);
                if value_end == -1: raise ValueError(f"Malformed rule value for '{rule_name}'");
                rule_value = response[offset:value_end].decode('utf-8', errors='ignore'); offset = value_end + 1
                rules[rule_name] = rule_value
            return rules
        except Exception as e: logger.warning(f"Parse RULES error: {e}"); return None

    def close(self):
        if self.sock:
            try: self.sock.close()
            except Exception: pass
            self.sock = None

# ==============================================================
# CS16BandwidthTester Class (Focuses on Simulation)
# ==============================================================
class CS16BandwidthTester:
    # Removed HTTP specific args from constructor where not needed for sim
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 download_delay, verbose, storage_dir, continuous_mode, no_server_monitor,
                 # --- Optional HTTP args ---
                 fastdl_url=None, file_list_path=None, delete_after_download=False,
                 # --- Logging ---
                 activity_log_filename=ACTIVITY_LOG_FILENAME):

        # Store args
        self.server_ip = server_ip; self.server_port = server_port
        self.num_connections = num_connections; self.test_duration = test_duration
        self.download_delay = max(0, download_delay) # Used for simulation
        self.verbose = verbose; self.continuous_mode = continuous_mode
        self.storage_dir = storage_dir; self.no_server_monitor = no_server_monitor
        self.manual_fastdl_url = fastdl_url # Optional for HTTP mode
        self.file_list_path = file_list_path # Optional for HTTP mode
        self.delete_after_download = delete_after_download # Optional for HTTP mode
        self.activity_log_filename = activity_log_filename

        # --- Setup Storage and Logging ---
        self.activity_log_filepath = None
        if not os.path.exists(self.storage_dir):
            try: os.makedirs(self.storage_dir); logger.info(f"Created storage directory: {self.storage_dir}")
            except OSError as e: logger.error(f"Failed storage dir '{self.storage_dir}': {e}. Using current."); self.storage_dir = "."
        self._configure_activity_logger()

        # Core state
        self.active = False; self.threads = []; self.connections = []
        self.lock = threading.Lock(); self._stop_event = threading.Event()
        self.start_time = 0; self.end_time = 0

        # Counters (focus on simulation)
        self.bytes_received_sim = 0; self.simulated_downloads_count = 0
        self.udp_requests_sent_sim = 0
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0
        # Counters for optional HTTP mode
        self.bytes_received_http = 0; self.http_download_attempts = 0
        self.http_download_successes = 0; self.http_download_failures = 0


        # Server info tracking
        self.server_query = None
        if not self.no_server_monitor:
             self.server_query = ServerQuery(server_ip, server_port, storage_dir=self.storage_dir)
        self.server_info = None; self.server_rules = None
        self.discovered_fastdl_url = None
        self.active_fastdl_url = self.manual_fastdl_url # Determined at start
        self.current_map_file_path = None # Relative path from server info

        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN"
        self.server_last_seen = 0
        self.server_info_thread = None; self.server_info_interval = 5
        self.server_status_log = [] # Log of status/ping from ServerQuery

        # Asset/Event tracking
        self.last_activity = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        self.bandwidth_log_points = [] # Tracks combined rate (primarily Sim)

        self.display_thread = None
        self.http_session = requests.Session() # Used only if in HTTP mode

        # File list for optional HTTP mode
        self.files_to_try_http = []
        self._load_file_list()

    def _configure_activity_logger(self):
        # Configure activity_logger file handler
        # Check if handlers already exist to prevent duplicates during potential restarts
        if activity_logger.hasHandlers():
            # Close existing handlers before adding new ones
            for handler in activity_logger.handlers[:]:
                 try: handler.close(); activity_logger.removeHandler(handler)
                 except Exception as e: logger.warning(f"Could not close existing activity log handler: {e}")
        try:
            self.activity_log_filepath = os.path.join(self.storage_dir, self.activity_log_filename)
            file_handler = logging.FileHandler(self.activity_log_filepath, mode='a', encoding='utf-8')
            file_formatter = logging.Formatter('%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
            file_handler.setFormatter(file_formatter)
            activity_logger.addHandler(file_handler)
            activity_logger.info(f"--- Activity Log Started ({datetime.now().isoformat()}) ---")
            logger.info(f"Logging activity details to: {self.activity_log_filepath}")
        except Exception as e:
            logger.error(f"Failed to configure activity log file handler: {e}")
            activity_logger.addHandler(logging.NullHandler()) # Prevent errors later


    def _load_file_list(self):
        """Loads file paths from the specified file for optional HTTP downloads."""
        self.files_to_try_http = [] # Reset list
        if self.file_list_path and self.active_fastdl_url: # Only load if relevant
            try:
                with open(self.file_list_path, 'r') as f:
                    for line in f:
                        file = line.strip()
                        if file and not file.startswith('#') and not file.startswith('//'):
                             normalized_path = file.replace('\\', '/').lstrip('/')
                             if '..' not in normalized_path: self.files_to_try_http.append(normalized_path)
                             else: logger.warning(f"Skipping unsafe path from list: {file}")
                logger.info(f"Loaded {len(self.files_to_try_http)} file paths for HTTP from '{self.file_list_path}'")
            except FileNotFoundError: logger.error(f"File list not found: {self.file_list_path}")
            except Exception as e: logger.error(f"Error reading file list '{self.file_list_path}': {e}")
        elif self.file_list_path: logger.debug("File list provided but not in HTTP mode, ignoring.")

    def _increment_counter(self, counter_name, value=1):
        with self.lock: setattr(self, counter_name, getattr(self, counter_name) + value)
    def _decrement_counter(self, counter_name, value=1): self._increment_counter(counter_name, -value)

    def _log_activity_event(self, worker_id, event_type, status, identifier, bytes_val=0, error_msg="", detail=""):
        """Logs events (HTTP, SIM, UDP Verify) to activity log file and potentially console."""
        # Use the same logging function from the previous combined script
        message = f"Worker {worker_id:<3} [{event_type:<10}] | Status: {status:<10} | ID: {identifier}"
        if bytes_val > 0: message += f" | Bytes: {bytes_val:<10}"
        if detail: message += f" | Detail: {detail}"
        if error_msg: message += f" | Error: {error_msg}"

        log_level = logging.INFO
        if "FAIL" in status or "ERROR" in status or "TIMEOUT" in status: log_level = logging.WARNING
        if status == "INTERRUPT": log_level = logging.INFO

        # Always log to file if handler is present
        if activity_logger.hasHandlers():
             activity_logger.log(log_level, message)
        elif log_level >= logging.WARNING: # Fallback for critical logs if file handler failed
             logger.log(log_level, f"[Activity Log Disabled] {message}")


        # Log significant/verbose events to console (stderr)
        console_log_level = log_level if log_level >= logging.WARNING else logging.DEBUG
        if log_level >= logging.INFO or self.verbose:
             console_msg = f"Worker {worker_id}: {event_type} {status}: {identifier}"
             if bytes_val > 0: console_msg += f" ({bytes_val/1024:.1f}KB)"
             if error_msg: console_msg += f" - {error_msg}"
             # Filter less important console messages unless verbose
             if event_type == "UDP Verify" and status in ["SAVED", "DELETED"] and not self.verbose: pass
             elif event_type == "HTTP Cleanup" and status == "DELETED" and not self.verbose: pass
             else: logger.log(console_log_level, console_msg)

        # Update UI deque (avoid UDP verify clutter)
        with self.lock:
            if event_type != "UDP Verify":
                 ui_entry = f"{identifier} ({bytes_val/1024:.1f}KB)"
                 if event_type == "SIM Download": ui_entry += " [SIM]"
                 elif status != "SUCCESS" and status != "DELETED": ui_entry += f" [{status}]" # Show status if not success/deleted
                 self.last_activity.append(ui_entry)

    # --- Simulation Logic (Primary mode if no FastDL) ---
    def _simulate_asset_download(self, conn_info):
        """Simulates download by sending UDP and incrementing counters."""
        conn_id = conn_info['id']
        sock = conn_info.get("socket")
        if not sock: # Attempt to create/recreate UDP socket if missing
            try:
                if conn_info.get("socket_creation_failed"): return False # Don't retry if known failure
                logger.debug(f"Worker {conn_id}: Recreating UDP socket for simulation.")
                sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); sock.settimeout(2.0)
                conn_info['socket'] = sock
            except Exception as e:
                logger.error(f"Worker {conn_id}: FAILED recreate socket: {e}. Worker disabled.")
                conn_info["socket_creation_failed"] = True # Mark failure
                conn_info['status'] = "error"; self._increment_counter("runtime_connection_issues"); return False

        conn_info["sim_attempts"] = conn_info.get("sim_attempts", 0) + 1
        simulated_bytes_received_for_asset = 0 # Reset for this attempt
        asset_type = random.choice(list(DOWNLOAD_SIZES.keys()))
        asset_size = DOWNLOAD_SIZES[asset_type]
        asset_id = f"{asset_type}_{random.randint(1000,9999)}"

        try:
            conn_info["status"] = "sim_running"; conn_info["last_activity_time"] = time.time()
            # Send a trigger UDP packet
            base_request = random.choice(CS_FILE_REQUESTS)
            request = base_request + f" simulate_{asset_id}\x00".encode()
            sent_bytes = sock.sendto(request, (self.server_ip, self.server_port))
            self._increment_counter("udp_requests_sent_sim", 1)
            conn_info["bytes_sent"] = conn_info.get("bytes_sent", 0) + sent_bytes
            conn_info["requests_sent"] = conn_info.get("requests_sent", 0) + 1

            # Simulate Receiving Data loop
            remaining_size = asset_size
            while remaining_size > 0 and self.active and not self._stop_event.is_set():
                bytes_this_chunk = min(4096, remaining_size, random.randint(1024, 4096))
                self._increment_counter("bytes_received_sim", bytes_this_chunk) # Global sim counter
                conn_info["bytes_received"] = conn_info.get("bytes_received", 0) + bytes_this_chunk # Worker total
                simulated_bytes_received_for_asset += bytes_this_chunk
                remaining_size -= bytes_this_chunk
                conn_info["last_activity_time"] = time.time()
                # Apply delay
                if self.download_delay > 0:
                     chunk_delay = self.download_delay / (asset_size / bytes_this_chunk) if asset_size > 0 else 0.001
                     # Check stop event during sleep for faster shutdown
                     if self._stop_event.wait(timeout=max(0.001, chunk_delay)): break
                if self._stop_event.is_set(): break # Check again after sleep/wait

            if self._stop_event.is_set():
                 self._log_activity_event(conn_id, "SIM Download", "INTERRUPT", asset_id, simulated_bytes_received_for_asset, "Test stopped")
                 conn_info["status"] = "stopped"; return False # Not a failure but not success

            if remaining_size <= 0:
                 self._increment_counter("simulated_downloads_count")
                 self._log_activity_event(conn_id, "SIM Download", "SUCCESS", asset_id, simulated_bytes_received_for_asset)
                 return True
            else: # Incomplete (shouldn't happen unless loop broken unexpectedly)
                 self._log_activity_event(conn_id, "SIM Download", "INCOMPLETE", asset_id, simulated_bytes_received_for_asset)
                 conn_info["status"] = "error"; return False

        except socket.timeout:
             self._increment_counter("runtime_connection_issues"); conn_info["status"] = "timeout"
             self._log_activity_event(conn_id, "SIM Download", "TIMEOUT", asset_id, simulated_bytes_received_for_asset, "UDP Send Timeout")
             return False
        except OSError as e:
             self._increment_counter("runtime_connection_issues"); conn_info["status"] = "error"
             self._log_activity_event(conn_id, "SIM Download", "OS_ERROR", asset_id, simulated_bytes_received_for_asset, str(e))
             logger.error(f"Worker {conn_id} Sim OS Error: {e}. Closing socket.")
             try: sock.close(); conn_info["socket"] = None # Ensure socket is None
             except Exception: pass
             return False
        except Exception as e:
             self._increment_counter("runtime_connection_issues"); conn_info["status"] = "error"
             self._log_activity_event(conn_id, "SIM Download", "FAILED", asset_id, simulated_bytes_received_for_asset, f"{type(e).__name__}: {str(e)}")
             logger.error(f"Worker {conn_id} unexpected sim error: {e}", exc_info=self.verbose)
             return False


    # --- HTTP Download Logic (Only runs if --fastdl-url provided) ---
    def _perform_http_download(self, conn_info, url, target_filename):
        """Attempts HTTP download, verifies, DELETES file if requested."""
        # Use the same function from the previous combined script
        conn_id = conn_info['id']
        timestamp_ms = int(time.time()*1000)
        safe_base = "".join(c for c in os.path.basename(target_filename) if c.isalnum() or c in ('.', '_', '-')).rstrip()
        local_filename = f"http_dl_{conn_id}_{safe_base}_{timestamp_ms}.tmp"
        local_filepath = os.path.join(self.storage_dir, local_filename)
        downloaded_bytes = 0
        conn_info["http_attempts"] = conn_info.get("http_attempts", 0) + 1
        self._increment_counter("http_download_attempts")
        headers = {'User-Agent': 'CSBandwidthTester/1.1-HTTP'}

        try:
            conn_info["status"] = "http_downloading"; conn_info["last_activity_time"] = time.time()
            if self.verbose: logger.debug(f"Worker {conn_id}: GET {url}")
            with self.http_session.get(url, stream=True, timeout=HTTP_TIMEOUT, headers=headers) as response:
                if self.verbose: logger.debug(f"Worker {conn_id}: HTTP Status {response.status_code} for {url}")
                response.raise_for_status()
                # Ensure directory exists before opening file
                os.makedirs(os.path.dirname(local_filepath), exist_ok=True)
                with open(local_filepath, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        if self._stop_event.is_set(): raise InterruptedError("Stop event")
                        if chunk:
                            f.write(chunk); chunk_len = len(chunk); downloaded_bytes += chunk_len
                            self._increment_counter("bytes_received_http", chunk_len) # Global HTTP counter
                            conn_info["bytes_received"] = conn_info.get("bytes_received", 0) + chunk_len # Worker total
                            conn_info["last_activity_time"] = time.time()

            conn_info["status"] = "http_verifying"
            if not os.path.exists(local_filepath): raise FileNotFoundError(f"DL file missing: {local_filepath}")
            # Optional Size check
            content_length = response.headers.get('content-length')
            if content_length and int(content_length) != downloaded_bytes:
                 mismatch_msg = f"Size mismatch Exp={content_length}, Got={downloaded_bytes}"
                 self._log_activity_event(conn_id, "HTTP Download", "SIZE_WARN", url, downloaded_bytes, mismatch_msg, detail=f"Path: {local_filepath}")

            conn_info["http_successes"] = conn_info.get("http_successes", 0) + 1
            self._increment_counter("http_download_successes")
            self._log_activity_event(conn_id, "HTTP Download", "SUCCESS", url, downloaded_bytes, detail=f"Saved to {local_filepath}")
            return True # Return success before potential deletion

        except requests.exceptions.Timeout as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues"); conn_info["status"] = "timeout"
             self._log_activity_event(conn_id, "HTTP Download", "TIMEOUT", url, downloaded_bytes, f"{type(e).__name__}"); return False
        except requests.exceptions.ConnectionError as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues"); conn_info["status"] = "error"
             self._log_activity_event(conn_id, "HTTP Download", "CONN_ERR", url, downloaded_bytes, f"{type(e).__name__}"); return False
        except requests.exceptions.HTTPError as e:
             self._increment_counter("http_download_failures"); conn_info["status"] = "http_error"
             self._log_activity_event(conn_id, "HTTP Download", f"HTTP_{e.response.status_code}", url, downloaded_bytes, f"{type(e).__name__}"); return False
        except InterruptedError:
             conn_info["status"] = "stopped"; self._log_activity_event(conn_id, "HTTP Download", "INTERRUPT", url, downloaded_bytes, "Test stopped"); return False
        except FileNotFoundError as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues"); conn_info["status"] = "error"
             self._log_activity_event(conn_id, "HTTP Download", "VERIFY_FAIL", url, downloaded_bytes, str(e)); return False
        except Exception as e:
             self._increment_counter("http_download_failures"); self._increment_counter("runtime_connection_issues"); conn_info["status"] = "error"
             self._log_activity_event(conn_id, "HTTP Download", "FAILED", url, downloaded_bytes, f"{type(e).__name__}: {str(e)}")
             logger.error(f"Worker {conn_id}: Unhandled HTTP DL error for {url}: {e}", exc_info=self.verbose); return False
        finally:
            # Cleanup: Delete temp file if requested
            if self.delete_after_download and os.path.exists(local_filepath):
                try:
                    os.remove(local_filepath)
                    self._log_activity_event(conn_id, "HTTP Cleanup", "DELETED", url, detail=f"Path: {local_filepath}")
                except Exception as e:
                     self._log_activity_event(conn_id, "HTTP Cleanup", "DELETE_FAIL", url, error_msg=str(e), detail=f"Path: {local_filepath}")


    # --- Worker Thread ---
    def _connection_worker(self, conn_info):
        conn_id = conn_info['id']
        # Determine mode based on whether a FastDL URL is active
        mode = "HTTP" if self.active_fastdl_url else "Simulation"
        if self.verbose: logger.debug(f"Worker {conn_id}: Started in {mode} mode.")
        self._increment_counter("active_workers_count")

        try:
            while self.active and not self._stop_event.is_set():
                success = False
                if mode == "HTTP":
                    file_rel_path = self._get_file_to_download_http()
                    if file_rel_path:
                        try:
                            full_url = urljoin(self.active_fastdl_url, file_rel_path.replace('\\', '/'))
                            success = self._perform_http_download(conn_info, full_url, file_rel_path)
                        except Exception as url_err:
                             self._increment_counter("http_download_failures")
                             self._log_activity_event(conn_id, "HTTP Download", "URL_ERROR", file_rel_path, error_msg=str(url_err))
                             conn_info["status"] = "error"
                    else: # No file available for HTTP
                        time.sleep(1.5); continue
                else: # Simulation Mode
                    # Check if socket creation failed permanently for this worker
                    if conn_info.get("socket_creation_failed"):
                         logger.debug(f"Worker {conn_id}: Skipping simulation due to prior socket error.")
                         time.sleep(5) # Sleep longer if worker is disabled
                         continue
                    success = self._simulate_asset_download(conn_info)

                # Wait before next attempt
                delay_base = 0.05 if success else 0.2
                worker_delay = random.uniform(delay_base, delay_base + 0.1)
                # Use wait() for stop event checking during sleep
                if self._stop_event.wait(timeout=worker_delay):
                     break # Exit loop if stop event is set during sleep

        except Exception as e:
            logger.error(f"Worker {conn_id}: Unhandled loop error: {e}", exc_info=self.verbose)
            conn_info["status"] = "error"
            self._increment_counter("runtime_connection_issues")
        finally:
            self._decrement_counter("active_workers_count")
            conn_info["status"] = "stopped"
            sock = conn_info.get("socket") # Close UDP socket if exists
            # --- CORRECTED SYNTAX ---
            if sock:
                try:
                    sock.close()
                except Exception:
                    pass # Silently ignore errors during socket close in finally block
            # --- END CORRECTION ---
            if self.verbose: logger.debug(f"Worker {conn_id}: Finished (Mode={mode}).")

    def _get_file_to_download_http(self):
        """Selects a file path for HTTP download (map or from list)."""
        # Only relevant if self.active_fastdl_url is True
        with self.lock:
            choices = []
            if self.current_map_file_path: choices.append(self.current_map_file_path)
            choices.extend(self.files_to_try_http)
            if not choices: return None
            return random.choice(choices)

    # --- Server Info Update Thread ---
    def _update_server_info(self):
        """Updates server info (map, rules) periodically via UDP."""
        # Uses the same logic as the previous combined script
        if not self.server_query: return
        if self.verbose: logger.debug("Server monitor thread started.")
        query_rules_interval = 30; last_rules_query_time = 0

        while self.active and not self._stop_event.is_set():
            current_status = "UNKNOWN"; ping = -1; map_name = None; info_success = False
            try:
                server_info = self.server_query.get_info(); timestamp = time.time()
                if server_info:
                    info_success = True
                    with self.lock:
                        self.server_info = server_info; self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                        map_name = server_info.get('map')
                        if map_name: self.current_map_file_path = f"maps/{map_name}.bsp"
                        else: self.current_map_file_path = None
                else: # Query failed
                    with self.lock:
                        if self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT): current_status = "OFFLINE"
                        else: current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"
                        self.server_info = None; self.server_status = current_status; self.current_map_file_path = None

                # Get Rules periodically if needed (for potential FastDL discovery)
                if info_success and (time.time() - last_rules_query_time > query_rules_interval) and not self.manual_fastdl_url:
                    logger.debug("Querying server rules for potential FastDL URL discovery..."); last_rules_query_time = time.time()
                    rules = self.server_query.get_rules()
                    with self.lock:
                        if rules:
                             self.server_rules = rules; dl_url = rules.get('sv_downloadurl')
                             if dl_url and (dl_url.startswith('http://') or dl_url.startswith('https://')):
                                  self.discovered_fastdl_url = dl_url.strip()
                                  if not self.discovered_fastdl_url.endswith('/'): self.discovered_fastdl_url += '/'
                                  # IMPORTANT: Only activate discovered URL if no manual one exists
                                  if not self.manual_fastdl_url and self.active_fastdl_url != self.discovered_fastdl_url:
                                      logger.info(f"Discovered/Updated FastDL URL via rules: {self.discovered_fastdl_url}")
                                      self.active_fastdl_url = self.discovered_fastdl_url
                                      self._load_file_list() # Reload file list if URL activated
                             else: self.discovered_fastdl_url = None; self.active_fastdl_url = None # Clear if rule missing/invalid and no manual URL
                        else: logger.debug("Rules query failed or returned no rules."); self.server_rules = None; self.discovered_fastdl_url = None; self.active_fastdl_url = None

            except Exception as e:
                logger.error(f"Server info/rules error: {e}", exc_info=self.verbose)
                with self.lock: current_status = "ERROR"; self.server_info = None; self.server_status = current_status; self.current_map_file_path = None; self.server_rules = None; self.discovered_fastdl_url = None; self.active_fastdl_url = self.manual_fastdl_url # Revert to manual on error

            status_log_entry = {'timestamp': time.time(), 'status': current_status, 'ping': ping, 'map': map_name}
            with self.lock: self.server_status_log.append(status_log_entry)
            # Wait/Check Stop Event
            sleep_end = time.time() + self.server_info_interval
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=0.1): break
            if self._stop_event.is_set(): break
        if self.server_query: self.server_query.close()
        if self.verbose: logger.debug("Server monitor thread finished.")


    # --- Realtime Display Thread ---
    def _display_realtime_stats(self):
        """Displays real-time stats (focuses on Simulation if no FastDL)."""
        # Uses the same display logic as the previous combined script
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time
        CURSOR_TO_HOME = "\033[H"; CLEAR_LINE = "\033[K"; CLEAR_SCREEN_FROM_CURSOR = "\033[J"
        term_width = 80
        try: term_width = os.get_terminal_size().columns
        except OSError: logger.warning("Could not detect terminal width, using 80."); term_width = 80

        while self.active and not self._stop_event.is_set():
            lines_to_print = []
            try:
                with self.lock:
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    bytes_http = self.bytes_received_http; http_ok = self.http_download_successes; http_fail = self.http_download_failures
                    bytes_sim = self.bytes_received_sim; sim_ok = self.simulated_downloads_count
                    active_workers = self.active_workers_count; runtime_issues = self.runtime_connection_issues; initial_fails = self.initial_connection_failures
                    current_server_status = self.server_status; current_map_path = self.current_map_file_path
                    current_ping = self.server_info.get('ping', -1) if self.server_info else -1
                    current_mode = "HTTP" if self.active_fastdl_url else "Simulation"
                    display_fastdl_url = self.active_fastdl_url if self.active_fastdl_url else "N/A (Simulation Mode)"
                    last_activity = list(self.last_activity)

                recv_http_mb = bytes_http / (1024*1024); recv_sim_mb = bytes_sim / (1024*1024)
                total_recv_mb = recv_http_mb + recv_sim_mb # Use primary counter based on mode? Or sum? Let's sum for now.
                avg_rate_mbs = total_recv_mb / elapsed if elapsed > 0 else 0

                current_time = time.time() # Log bandwidth point
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                     with self.lock: self.bandwidth_log_points.append((elapsed, total_recv_mb))
                     last_bw_log_time = current_time

                # Format Output Lines
                status = "Running" if self.active else "Stopped"; test_mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                header = f"--- CS 1.6 BW Test ({self.server_ip}:{self.server_port} | Mode: {current_mode}) ---".center(term_width)
                lines_to_print.append(header)
                line_status = f" Status: {status} | Test Mode: {test_mode}"; line_time = f"Time: {elapsed:.1f}s"
                lines_to_print.append(f"{line_status:<{max(0, term_width - len(line_time))}}{line_time}")
                line_workers = f" Workers: {active_workers}/{self.num_connections}"; line_issues = f"Issues: Init={initial_fails} Run={runtime_issues}"
                lines_to_print.append(f"{line_workers:<{max(0, term_width - len(line_issues))}}{line_issues}")
                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Server Status (UDP Query)]".center(term_width))
                if self.no_server_monitor: lines_to_print.append(" UDP Monitoring Disabled".ljust(term_width)); lines_to_print.append(f" Current Map: UNKNOWN".ljust(term_width))
                else:
                    s_status_str = f" Status: {current_server_status}"; s_ping_str = f"Ping: {current_ping:>3}ms" if current_ping >= 0 else "Ping: N/A"
                    s_map_str = f"Map Path: {current_map_path if current_map_path else 'UNKNOWN'}"
                    width_status = len(s_status_str); width_ping = len(s_ping_str); spaces1 = max(1, (term_width - width_status - width_ping) // 2)
                    lines_to_print.append(f"{s_status_str}{' '*spaces1}{s_ping_str}".ljust(term_width))
                    lines_to_print.append(s_map_str[:term_width].ljust(term_width))
                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Activity & Bandwidth]".center(term_width))
                lines_to_print.append(f" Active FastDL URL: {display_fastdl_url[:term_width-20]}".ljust(term_width))
                if http_ok > 0 or http_fail > 0 or bytes_http > 0: lines_to_print.append(f" HTTP Recv: {recv_http_mb:>7.2f} MB | OK: {http_ok} Fail: {http_fail}".ljust(term_width))
                if sim_ok > 0 or bytes_sim > 0: lines_to_print.append(f" SIM Recv:  {recv_sim_mb:>7.2f} MB | OK: {sim_ok}".ljust(term_width))
                lines_to_print.append(f" Avg Total Rate: {avg_rate_mbs:>6.2f} MB/s".ljust(term_width))
                lines_to_print.append("-" * term_width)
                lines_to_print.append(f"[Last {LAST_FILES_DISPLAY_COUNT} Activities]".center(term_width))
                if last_activity:
                    for activity in reversed(last_activity): lines_to_print.append(f" {activity[:term_width-2]}".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_activity))): lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No activity yet)".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT -1)): lines_to_print.append(" ".ljust(term_width))
                lines_to_print.append("-" * term_width)
                lines_to_print.append("(Press Ctrl+C to stop)".center(term_width))

                # Screen Update
                output_buffer = CURSOR_TO_HOME
                for line in lines_to_print: output_buffer += line[:term_width] + CLEAR_LINE + "\n"
                output_buffer += CLEAR_SCREEN_FROM_CURSOR
                sys.stdout.write(output_buffer); sys.stdout.flush()

            except Exception as e: logger.error(f"Display thread error: {e}", exc_info=False); time.sleep(1)
            # Wait/Check Stop Event
            sleep_end = time.time() + UI_UPDATE_INTERVAL
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=0.1): break
            if self._stop_event.is_set(): break
        if self.verbose: logger.debug("Realtime display thread finished.")
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR); sys.stdout.flush()


    # --- Start/Stop Methods ---
    def start_test(self):
        # Same start logic as combined script, determining mode first
        if self.active: logger.warning("Test already running."); return

        # Determine active FastDL URL
        self.active_fastdl_url = self.manual_fastdl_url # Start with manual
        if not self.active_fastdl_url and not self.no_server_monitor:
            logger.info("No manual FastDL URL, attempting initial rules query for discovery...")
            try:
                 if not self.server_query: self.server_query = ServerQuery(self.server_ip, self.server_port, self.storage_dir)
                 rules = self.server_query.get_rules()
                 if rules:
                     dl_url = rules.get('sv_downloadurl', '').strip()
                     if dl_url and (dl_url.startswith('http://') or dl_url.startswith('https://')):
                          self.discovered_fastdl_url = dl_url if dl_url.endswith('/') else dl_url + '/'
                          self.active_fastdl_url = self.discovered_fastdl_url # Use discovered
                          logger.info(f"Using discovered FastDL URL: {self.active_fastdl_url}")
                     else: logger.info("sv_downloadurl not found/invalid in initial query.")
                 else: logger.info("Initial rules query failed.")
            except Exception as e: logger.error(f"Initial rules query error: {e}")
        elif self.manual_fastdl_url: logger.info(f"Using manually specified FastDL URL: {self.active_fastdl_url}")
        # Final check for mode
        mode = "HTTP" if self.active_fastdl_url else "Simulation"
        if mode == "Simulation": logger.info("No FastDL URL active. Running in Simulation mode.")
        # Reload file list if HTTP mode became active via discovery
        if mode == "HTTP": self._load_file_list()

        logger.info("="*30 + f" Starting Test (Mode: {mode}) " + "="*30)
        self.active = True; self._stop_event.clear(); self.start_time = time.time(); self.end_time = 0
        # Reset counters
        self.bytes_received_http = 0; self.http_download_attempts = 0; self.http_download_successes = 0; self.http_download_failures = 0
        self.bytes_received_sim = 0; self.simulated_downloads_count = 0; self.udp_requests_sent_sim = 0
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0; self.active_workers_count = 0
        self.server_status_log = []; self.last_activity.clear(); self.bandwidth_log_points = []
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0; self.server_info = None; self.current_map_file_path = None; self.server_rules = None
        self.threads = [] # Clear thread list

        # Start Monitor Thread (if enabled)
        if not self.no_server_monitor and self.server_query:
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start(); self.threads.append(self.server_info_thread)

        # Start Display Thread
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start(); self.threads.append(self.display_thread)

        # Start Workers
        logger.info(f"Starting {self.num_connections} workers (Mode: {mode})..."); self.connections = []
        initial_success = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set(): break
            # Create worker structure (attempts UDP socket create)
            conn_info = {"id": i + 1, "socket": None, "socket_creation_failed": False} # Simplified init
            self.connections.append(conn_info)
            worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
            worker_thread.start(); self.threads.append(worker_thread); initial_success += 1
            if self.num_connections > 20 and (i + 1) % 20 == 0: time.sleep(0.05)

        logger.info(f"Launched {initial_success} workers.")
        if initial_success == 0 and self.num_connections > 0:
             logger.error("FATAL: No workers launched. Stopping."); threading.Thread(target=self.stop_test).start(); return

        # Main loop waits
        try:
            if self.continuous_mode: self._stop_event.wait(); logger.info("Stop event received...")
            else:
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early: logger.info("Test stopped early.")
                else: logger.info("Test duration reached."); self.stop_test()
        except Exception as e: logger.error(f"Main loop error: {e}"); self.stop_test()


    def stop_test(self):
        # Same stop logic as combined script
        if not self.active or self._stop_event.is_set(): return
        logger.info("Stopping test..."); self.active = False; self._stop_event.set()
        self.end_time = time.time() if self.start_time > 0 else time.time()
        logger.info("Waiting for threads..."); join_timeout = 5.0
        threads_to_join = self.threads[:]
        for thread in threads_to_join:
             if thread is threading.current_thread() or not thread.is_alive(): continue
             try:
                 if self.verbose: logger.debug(f"Joining {thread.name}...")
                 thread.join(join_timeout)
                 if thread.is_alive(): logger.warning(f"{thread.name} did not stop.")
             except Exception as e: logger.warning(f"Error joining {thread.name}: {e}")
        logger.info("Threads processed.")
        # Close resources
        if self.server_query: self.server_query.close()
        self.http_session.close()
        for conn_info in self.connections: # Close any remaining UDP sockets
             sock = conn_info.get("socket")
             if sock:
                 try:
                     sock.close()
                 except Exception:
                    pass
        # Close log file handler
        self._close_activity_logger()
        # Final Report
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed)
        logger.info("Test finished.")

    def _close_activity_logger(self):
        # Find and close the file handler for the activity logger
        handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
        if handler:
            try:
                handler.stream.write(f"--- Activity Log Ended ({datetime.now().isoformat()}) ---\n")
                handler.close()
                activity_logger.removeHandler(handler) # Remove handler to prevent issues on restart
                logger.debug("Activity log handler closed.")
            except Exception as e:
                logger.warning(f"Error closing activity log handler: {e}")


    # --- Reporting Methods ---
    def _generate_final_report(self, duration):
        # Use the same report generation as the combined script
        print("\n" + "="*30 + " Test Results Summary " + "="*30); duration = max(duration, 0.01)
        with self.lock:
            bytes_http = self.bytes_received_http; http_ok = self.http_download_successes; http_fail = self.http_download_failures
            bytes_sim = self.bytes_received_sim; sim_ok = self.simulated_downloads_count
            runtime_issues = self.runtime_connection_issues; initial_fails = self.initial_connection_failures
            final_server_status = self.server_status; final_map = self.current_map_file_path or "UNKNOWN"
            server_log = self.server_status_log[:]; mode_run = "HTTP" if self.active_fastdl_url else "Simulation"
        recv_http_mb = bytes_http/(1024*1024); recv_sim_mb = bytes_sim/(1024*1024); total_recv_mb = recv_http_mb + recv_sim_mb
        avg_rate_mbs = total_recv_mb / duration
        avg_ping = -1; min_ping = -1; max_ping = -1
        if not self.no_server_monitor:
             pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
             if pings: avg_ping=sum(pings)/len(pings); min_ping=min(pings); max_ping=max(pings)
        print(f"[Test Overview]"); print(f" Target Server:   {self.server_ip}:{self.server_port}"); print(f" Mode Executed:   {mode_run}")
        print(f" FastDL URL Used: {self.active_fastdl_url if self.active_fastdl_url else 'N/A'}"); print(f" Duration:        {duration:.2f}s")
        print(f" Config Workers:  {self.num_connections}"); print(f" Initial Fails:   {initial_fails}"); print(f" Runtime Issues:  {runtime_issues}")
        if bytes_http > 0 or http_ok > 0 or http_fail > 0:
             print("\n[HTTP Download Results]"); print(f" Files OK:        {http_ok}"); print(f" Files Failed:    {http_fail} (See {self.activity_log_filename})")
             print(f" Received (HTTP): {recv_http_mb:.2f} MB");
             if mode_run == "HTTP": print(f" Files Deleted:   {'Yes' if self.delete_after_download else 'No'}")
        if bytes_sim > 0 or sim_ok > 0:
             print("\n[Simulation Results]"); print(f" Sim OK:          {sim_ok}"); print(f" Received (Sim):  {recv_sim_mb:.2f} MB")
             print(f" Sim Delay Param: {self.download_delay}")
        print("\n[Bandwidth Summary]"); print(f" Total Received:  {total_recv_mb:.2f} MB (HTTP + Sim)"); print(f" Avg Total Rate:  {avg_rate_mbs:.2f} MB/s")
        print("\n[Server Status (UDP Query)]")
        if self.no_server_monitor: print(" Monitoring:      Disabled")
        else:
            print(f" Final Status:    {final_server_status}"); print(f" Last Known Map:  {final_map}")
            print(f" Avg Ping:        {avg_ping:.1f} ms" if avg_ping != -1 else "N/A"); print(f" Ping Min/Max:    {min_ping} / {max_ping} ms" if min_ping != -1 else "N/A")
        print("="*60)

    def _save_detailed_report_json(self, duration):
         # Use the same JSON report generation as the combined script
         with self.lock:
             duration = max(0.01, duration); bytes_http = self.bytes_received_http; http_ok = self.http_download_successes; http_fail = self.http_download_failures
             bytes_sim = self.bytes_received_sim; sim_ok = self.simulated_downloads_count; total_recv_mb = (bytes_http + bytes_sim) / (1024*1024)
             avg_rate_mbs = total_recv_mb / duration; server_log = self.server_status_log[:]; mode_run = "HTTP" if self.active_fastdl_url else "Simulation"
         report_data = {
            "test_info": {"test_type": "CS_Bandwidth_Test", "execution_mode": mode_run, "target_server": f"{self.server_ip}:{self.server_port}", "fastdl_url_used": self.active_fastdl_url, "timestamp_utc": datetime.utcnow().isoformat() + "Z", "duration_seconds": round(duration, 2), "configured_workers": self.num_connections, "initial_connection_failures": self.initial_connection_failures, "runtime_connection_issues": self.runtime_connection_issues, "test_run_mode": "Continuous" if self.continuous_mode else "Timed", "server_udp_monitoring": not self.no_server_monitor, "verbose_logging": self.verbose},
            "bandwidth_summary": {"total_received_mb": round(total_recv_mb, 3), "avg_total_rate_mbs": round(avg_rate_mbs, 3), "http_received_mb": round(bytes_http / (1024*1024), 3), "simulated_received_mb": round(bytes_sim / (1024*1024), 3), "bandwidth_log_points_sec_mb": [(round(t, 2), round(mb, 3)) for t, mb in self.bandwidth_log_points]},
            "http_download_stats": {"files_attempted": self.http_download_attempts, "files_succeeded": http_ok, "files_failed_or_skipped": http_fail, "delete_after_download": self.delete_after_download, "file_list_used": self.file_list_path} if mode_run == "HTTP" else None,
            "simulation_stats": {"simulations_completed": sim_ok, "simulated_download_delay_param": self.download_delay, "udp_requests_sent_by_sim": self.udp_requests_sent_sim} if mode_run == "Simulation" else None,
            "server_status_log": server_log}
         report_data = {k: v for k, v in report_data.items() if v is not None}
         ts = int(time.time()); report_filename = f"cs_bw_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts}.json"
         report_filepath = os.path.join(self.storage_dir, report_filename)
         try:
            with open(report_filepath, 'w') as f: json.dump(report_data, f, indent=2)
            logger.info(f"Detailed JSON report saved to: {report_filepath}")
         except Exception as e: logger.error(f"Failed to save JSON report '{report_filepath}': {e}")

# ==============================================================
# Signal Handling
# ==============================================================
def signal_handler(sig, frame):
    global tester_instance
    if tester_instance and tester_instance.active and not tester_instance._stop_event.is_set():
        print('\n'); logger.warning("Ctrl+C received! Initiating shutdown...")
        threading.Thread(target=tester_instance.stop_test, daemon=True).start()
    else:
        print('\nCtrl+C received, exiting immediately.')
        # Attempt to close log file even if tester not fully active
        handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
        if handler:
            try:
                handler.close()
            except Exception:
                pass
        sys.exit(0)

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 Server UDP Query/Simulation Tool (Optional HTTP Downloads)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter )
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 GAME server.")
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="GAME server UDP port.")
    parser.add_argument("--fastdl-url", default=None, help="[Optional] Base URL for FastDL to enable HTTP download mode.")
    parser.add_argument("-c", "--connections", type=int, default=10, help="Number of concurrent workers.")
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of timed test in seconds.")
    parser.add_argument("--storage-dir", default="cs_test_data", help="Directory for logs, reports, and temporary files.")
    parser.add_argument("--activity-log", default=ACTIVITY_LOG_FILENAME, help="Filename for logging activity details.")
    parser.add_argument("--delay", type=float, default=0.01, help="[Simulation Mode] Simulated delay factor per chunk.")
    parser.add_argument("--file-list", help="[HTTP Mode] Path to text file with relative asset paths.")
    parser.add_argument("--delete-after-download", action="store_true", help="[HTTP Mode] Delete temp HTTP files after download.")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging.")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run continuously until stopped (Ctrl+C).")
    parser.add_argument("--no-server-monitor", action="store_true", help="Disable querying game server status via UDP.")
    args = parser.parse_args()

    # Configure Logging Level
    if args.verbose: logger.setLevel(logging.DEBUG); activity_logger.setLevel(logging.DEBUG)
    else: logger.setLevel(logging.INFO); activity_logger.setLevel(logging.INFO)

    # Display Warnings
    logger.warning("="*70)
    if args.fastdl_url: logger.warning("⚠️ HTTP DOWNLOAD MODE WILL BE USED (FastDL URL provided). Ensure PERMISSION.")
    else: logger.warning("⚠️ SIMULATION MODE WILL BE USED (No FastDL URL). Bandwidth is SIMULATED.")
    logger.warning("Ensure you have permission before testing ANY server. Use responsibly.")
    logger.warning("="*70)
    time.sleep(1.5)

    try:
        # Ensure storage dir exists before initializing tester
        if not os.path.exists(args.storage_dir):
            try: os.makedirs(args.storage_dir); logger.info(f"Created base directory: {args.storage_dir}")
            except OSError as e: logger.warning(f"Cannot create storage dir '{args.storage_dir}'.")

        tester_instance = CS16BandwidthTester(
            server_ip=args.server_ip, server_port=args.port, num_connections=args.connections, # Fixed typo server_port
            test_duration=args.duration, download_delay=args.delay, verbose=args.verbose,
            storage_dir=args.storage_dir, continuous_mode=args.continuous,
            no_server_monitor=args.no_server_monitor, fastdl_url=args.fastdl_url,
            file_list_path=args.file_list, delete_after_download=args.delete_after_download,
            activity_log_filename=args.activity_log )

        signal.signal(signal.SIGINT, signal_handler); signal.signal(signal.SIGTERM, signal_handler)
        tester_instance.start_test()
        logger.info("Main thread finished.")
        sys.exit(0)
    except ValueError as e: logger.error(f"Configuration Error: {e}"); sys.exit(1)
    except Exception as e: logger.error(f"An critical error occurred: {e}", exc_info=True); sys.exit(1)
    finally: # Ensure log file handler is closed on unexpected exit
        handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
        if handler:
            try:
                handler.close()
            except Exception:
                pass
