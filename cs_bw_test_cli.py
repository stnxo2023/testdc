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
import requests # <--- Added: For HTTP downloads
from urllib.parse import urljoin # <--- Added: For constructing URLs safely

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150 # ms
SERVER_OFFLINE_TIMEOUT = 15 # seconds without response
LAST_FILES_DISPLAY_COUNT = 5 # How many recent filenames/URLs to show in UI
UI_UPDATE_INTERVAL = 0.5 # How often to refresh the terminal stats (seconds)
CONNECTION_CHECK_INTERVAL = 2.0 # How often worker status is checked (less critical now)
HTTP_TIMEOUT = 15 # seconds for HTTP connection/read
DOWNLOAD_LOG_FILENAME = "download_log.txt" # Name for the download details log file

# For simulation fallback
CS_FILE_REQUESTS = [
    b"\xff\xff\xff\xffgetinfo\x00", b"\xff\xff\xff\xffgetstatus\x00",
    b"\xff\xff\xff\xffrcon", b"\xff\xff\xff\xffping\x00",
    b"\xff\xff\xff\xffdetails\x00", b"\xff\xff\xff\xffplayers\x00",
    b"\xff\xff\xff\xffrules\x00", b"\xff\xff\xff\xffchallenge\x00",
]
DOWNLOAD_SIZES = { "map": 20*1024*1024, "model": 2*1024*1024, "sound": 512*1024, "sprite": 128*1024, "texture": 1*1024*1024 }

# --- Global logger setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr # Log messages go to stderr, stats go to stdout
)
logger = logging.getLogger('cs_bandwidth_tester_cli')

# --- Download Logger Setup ---
# Separately log download attempts/results to a file
download_logger = logging.getLogger('download_logger')
download_logger.setLevel(logging.INFO)
download_logger.propagate = False # Prevent double logging to stderr

# Global variable to hold the tester instance for signal handling
tester_instance = None

# ==============================================================
# ServerQuery Class (Updated to fetch rules and sv_downloadurl)
# ==============================================================
class ServerQuery:
    def __init__(self, server_ip, server_port=DEFAULT_PORT):
        self.server_ip = server_ip; self.server_port = server_port
        self.last_info = None; self.last_ping = 0; self.sock = None
        self.retry_count = 2; self.timeout = 1.5 # seconds
        self.last_challenge = None # Store challenge for rules query

    def _create_socket(self):
        # (Same as before)
        if self.sock is not None:
            try: self.sock.close()
            except Exception: pass
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); self.sock.settimeout(self.timeout)
        except Exception as e: logger.error(f"Query Socket Create Error: {e}"); self.sock = None; raise

    def _send_recv(self, request):
        """Helper to send a request and receive response, handling retries."""
        if self.sock is None:
             try: self._create_socket()
             except Exception: return None, 0

        start_time = time.time()
        response = None
        for attempt in range(self.retry_count):
            try:
                self.sock.sendto(request, (self.server_ip, self.server_port))
                response, _ = self.sock.recvfrom(4096) # Might need larger buffer for rules?
                end_time = time.time()
                ping = int((end_time - start_time) * 1000)
                if response:
                    return response, ping
                else:
                    logger.debug(f"Received empty response (attempt {attempt+1}) for request: {request[:20]}")
            except socket.timeout:
                logger.debug(f"Server query timed out (attempt {attempt+1}) for request: {request[:20]}")
                if attempt == self.retry_count - 1: return None, 0 # Return None after final timeout
                time.sleep(0.1) # Wait briefly before retry
            except (OSError) as e:
                logger.warning(f"Query Send/Recv Error (attempt {attempt+1}): {type(e).__name__} - {str(e)}")
                self.close() # Close potentially broken socket
                return None, 0 # Return None on significant errors
            except Exception as e:
                logger.error(f"Unexpected Query Send/Recv Error (attempt {attempt+1}): {type(e).__name__} - {str(e)}")
                self.close()
                return None, 0 # Return None on unexpected errors
        return None, 0 # Explicitly return None if all retries fail

    def get_info(self):
        """Gets basic server info (A2S_INFO)."""
        request = b"\xFF\xFF\xFF\xFFTSource Engine Query\x00" # Standard Source query request
        response, ping = self._send_recv(request)
        if response:
            parsed_info = self._parse_info(response)
            if parsed_info:
                self.last_ping = ping # Use ping from this successful query
                parsed_info['ping'] = self.last_ping # Add ping to the dict
                self.last_info = parsed_info
                # Check for challenge request needed for rules
                if response[4:5] == b'A': # 0x41
                    self.last_challenge = response[5:9]
                    logger.debug(f"Received challenge: {self.last_challenge}")
                else:
                    self.last_challenge = None # GoldSrc or other may not need/provide challenge
                return parsed_info
            else:
                logger.debug(f"Failed to parse INFO response. Response: {response[:100]}...")
                return None
        return None

    def get_rules(self):
        """Gets server rules/cvars (A2S_RULES). Returns dict of rules or None."""
        if self.last_challenge is None:
            # Try getting info first to potentially get a challenge number
            logger.debug("No challenge key, attempting get_info first...")
            self.get_info()
            if self.last_challenge is None:
                 # Still no challenge, GoldSrc servers might use 0xFFFFFFFF or no challenge
                 # Let's try with a default challenge value often used for GoldSrc compatibility
                 logger.debug("No challenge key found, using default challenge for rules query.")
                 challenge_bytes = b'\xFF\xFF\xFF\xFF'
                 # Alternatively: return None - safer if server strictly requires challenge
                 # return None
            else:
                 challenge_bytes = self.last_challenge
        else:
            challenge_bytes = self.last_challenge

        request = b'\xFF\xFF\xFF\xFFV' + challenge_bytes # A2S_RULES request: 0x56
        response, _ = self._send_recv(request) # Ping isn't the primary goal here

        if response and response[4:5] == b'E': # 0x45 A2S_RULES response header
            return self._parse_rules(response)
        elif response:
            logger.debug(f"Received unexpected response type for RULES query: {response[4:5]}. Response: {response[:100]}...")
            return None
        else:
            logger.debug("No response received for RULES query.")
            return None

    def _parse_info(self, response):
        # (Parsing logic remains mostly the same as before)
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF':
                 logger.debug(f"Invalid response header: {response[:10]}")
                 return None
            header_byte = response[4:5] # This is the response TYPE ('I', 'm', 'A', etc.)
            offset = 5

            # Handle different response types if necessary
            if header_byte == b'I': # Source Engine Info Reply
                offset += 1 # Skip protocol version byte
                # --- Source Specific Parsing ---
                def read_string(data, start_offset):
                    end = data.find(b'\x00', start_offset)
                    if end == -1: raise ValueError("Malformed string field (Source)")
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1

                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)

                if offset + 9 > len(response): raise ValueError("Response too short for Source numeric fields")
                # app_id = int.from_bytes(response[offset:offset+2], 'little'); offset += 2 # Skip AppID
                offset += 2 # Skip AppID
                player_count = response[offset]; offset += 1
                max_players = response[offset]; offset += 1
                bot_count = response[offset]; offset += 1
                # Other fields skipped: server_type, environment, visibility, vac
                offset += 4 # Skip server_type(c), environment(c), visibility(b), vac(b)

                # Add more fields if needed (version string, EDF)

                return {
                    'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                    'players': player_count, 'max_players': max_players, 'bots': bot_count,
                    # Ping added later in get_info
                }

            elif header_byte == b'm': # GoldSrc Info Reply (Different format)
                 # Address string first
                addr_end = response.find(b'\x00', offset)
                if addr_end == -1: raise ValueError("Malformed address string (GoldSrc)")
                # server_addr_str = response[offset:addr_end].decode('utf-8', errors='ignore')
                offset = addr_end + 1

                def read_string_gs(data, start_offset):
                    end = data.find(b'\x00', start_offset)
                    if end == -1: raise ValueError("Malformed string field (GoldSrc)")
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1

                server_name, offset = read_string_gs(response, offset)
                map_name, offset = read_string_gs(response, offset)
                game_dir, offset = read_string_gs(response, offset)
                game_desc, offset = read_string_gs(response, offset)

                if offset + 3 > len(response): raise ValueError("Response too short for GoldSrc numeric fields")
                player_count = response[offset]; offset += 1
                max_players = response[offset]; offset += 1
                # protocol_ver = response[offset]; offset += 1 # Skip protocol version
                offset += 1

                # Other fields skipped: server_type, environment, visibility, mod
                # Note: Bot count isn't standard in this reply

                return {
                    'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                    'players': player_count, 'max_players': max_players, 'bots': 0, # Assume 0 bots
                    # Ping added later in get_info
                }
            elif header_byte == b'A': # Challenge response - not info
                 logger.debug("Received challenge response instead of info.")
                 return None # Or handle challenge saving here if needed elsewhere
            else:
                 logger.debug(f"Unsupported INFO response type: {header_byte}")
                 return None

        except (IndexError, ValueError) as e:
             logger.warning(f"Parsing error ({type(e).__name__}) for INFO response: {e}. Response: {response[:100]}...")
             return None
        except Exception as e:
             logger.error(f"Unexpected error parsing server info: {type(e).__name__} - {str(e)}", exc_info=False)
             return None

    def _parse_rules(self, response):
        """Parses A2S_RULES response (0x45)."""
        try:
            if not response or len(response) < 7 or response[:5] != b'\xFF\xFF\xFF\xFFE':
                logger.debug(f"Invalid RULES response header or length: {response[:10]}")
                return None

            rules_count = int.from_bytes(response[5:7], 'little')
            offset = 7
            rules = {}

            for _ in range(rules_count):
                # Read rule name
                name_end = response.find(b'\x00', offset)
                if name_end == -1: raise ValueError("Malformed rule name string")
                rule_name = response[offset:name_end].decode('utf-8', errors='ignore')
                offset = name_end + 1

                # Read rule value
                value_end = response.find(b'\x00', offset)
                if value_end == -1: raise ValueError(f"Malformed rule value string for rule '{rule_name}'")
                rule_value = response[offset:value_end].decode('utf-8', errors='ignore')
                offset = value_end + 1

                rules[rule_name] = rule_value

            logger.debug(f"Parsed {len(rules)} rules. Found sv_downloadurl: {'yes' if 'sv_downloadurl' in rules else 'no'}")
            return rules

        except (IndexError, ValueError) as e:
             logger.warning(f"Parsing error ({type(e).__name__}) for RULES response: {e}. Response: {response[:100]}...")
             return None
        except Exception as e:
             logger.error(f"Unexpected error parsing server rules: {type(e).__name__} - {str(e)}", exc_info=False)
             return None

    def close(self):
        # (Same as before)
        if self.sock:
            try: self.sock.close()
            except Exception: pass
            self.sock = None

# ==============================================================
# CS16BandwidthTester Class (Major Updates)
# ==============================================================
class CS16BandwidthTester:
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 download_delay, verbose, storage_dir, continuous_mode, no_server_monitor,
                 fastdl_url, download_maps_only): # <-- Added arguments

        self.server_ip = server_ip; self.server_port = server_port
        self.num_connections = num_connections; self.test_duration = test_duration
        self.download_delay = max(0, download_delay); self.verbose = verbose
        self.continuous_mode = continuous_mode; self.storage_dir = storage_dir
        self.no_server_monitor = no_server_monitor
        self.manual_fastdl_url = fastdl_url # <-- Store manually provided URL
        self.download_maps_only = download_maps_only # <-- Option to restrict downloads

        # --- Setup Storage and Logging ---
        self.download_log_filepath = None # Will be set in start_test
        if not os.path.exists(self.storage_dir):
            try:
                os.makedirs(self.storage_dir)
                logger.info(f"Created storage directory: {self.storage_dir}")
            except OSError as e:
                logger.error(f"Failed to create storage directory '{self.storage_dir}': {e}. Using current directory.")
                self.storage_dir = "." # Fallback

        # Configure the file handler for download logs
        try:
            self.download_log_filepath = os.path.join(self.storage_dir, DOWNLOAD_LOG_FILENAME)
            file_handler = logging.FileHandler(self.download_log_filepath, mode='a') # Append mode
            file_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
            file_handler.setFormatter(file_formatter)
            download_logger.addHandler(file_handler)
            download_logger.info("--- Download Log Started ---")
        except Exception as e:
            logger.error(f"Failed to configure download log file handler: {e}")
            download_logger.addHandler(logging.NullHandler()) # Prevent errors if logging fails


        self.active = False; self.connections = []; self.threads = []
        self.lock = threading.Lock()
        self._stop_event = threading.Event()

        # Counters remain similar, but 'received' now tracks actual/simulated
        self.bytes_sent = 0; self.bytes_received = 0
        self.start_time = 0; self.end_time = 0
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0
        self.http_download_attempts = 0 # New counter
        self.http_download_successes = 0 # New counter
        self.http_download_failures = 0 # New counter
        self.simulated_downloads_run = 0 # New counter

        # Server info tracking
        self.server_query = ServerQuery(server_ip, server_port) if not self.no_server_monitor else None
        self.server_info = None # Holds result from get_info
        self.server_rules = None # Holds result from get_rules
        self.discovered_fastdl_url = None # URL found via rules query
        self.active_fastdl_url = self.manual_fastdl_url # Prioritize manual URL
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0
        self.server_info_thread = None; self.server_info_interval = 5 # Increase interval slightly
        self.server_status_log = []

        # Asset tracking (includes simulated and potentially real file names/URLs)
        self.asset_downloads = {k: 0 for k in DOWNLOAD_SIZES}; self.asset_bandwidth = {k: 0 for k in DOWNLOAD_SIZES}
        self.downloaded_files = []; self.last_downloaded_files = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT) # Now stores URLs or simulated names
        self.bandwidth_log_points = []

        self.display_thread = None

    # --- Counter Methods (Same as before) ---
    def _increment_counter(self, counter_name, value=1):
        with self.lock: setattr(self, counter_name, getattr(self, counter_name) + value)
    def _decrement_counter(self, counter_name, value=1): self._increment_counter(counter_name, -value)

    def _create_connection(self, conn_id):
        # Create UDP socket for potential simulation fallback or future UDP tasks
        sock = None
        try:
            # Still create UDP socket for potential fallback/other queries
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); sock.settimeout(2.0)
        except Exception as e: logger.error(f"Conn {conn_id}: UDP Socket create error: {e}"); sock = None # Don't fail entirely if UDP fails

        # Return structure, socket might be None
        return {
            "id": conn_id,
            "socket": sock, # UDP socket
            "bytes_sent": 0, # Tracks UDP sends mostly
            "bytes_received": 0, # Tracks ACTUAL HTTP downloads + simulated UDP downloads
            "last_activity_time": 0,
            "requests_sent": 0, # UDP requests
            "http_attempts": 0,
            "http_successes": 0,
            "sim_attempts": 0, # Simulation attempts
            "status": "running"
        }

    def _log_download_event(self, worker_id, url, status, bytes_dl=0, error_msg="", local_path=None):
        """Logs download details to the dedicated file and potentially console."""
        message = f"Worker {worker_id:<3} | URL: {url} | Status: {status:<8}"
        if bytes_dl > 0:
             message += f" | Bytes: {bytes_dl:<10}"
        if local_path:
             message += f" | Path: {local_path}"
        if error_msg:
             message += f" | Error: {error_msg}"

        download_logger.info(message)
        if status == "SUCCESS":
             logger.debug(f"Worker {worker_id}: Download SUCCESS: {url} ({bytes_dl} bytes)")
        elif status != "DELETED": # Don't spam console with delete messages
             logger.warning(f"Worker {worker_id}: Download {status}: {url} - {error_msg}")

        # Also add URL to the deque for UI display (maybe only on success?)
        if status == "SUCCESS":
             with self.lock:
                 self.last_downloaded_files.append(f"{url} ({bytes_dl/1024:.1f}KB)")

    def _perform_http_download(self, conn_info, url, target_filename):
        """Attempts to download a file via HTTP, verifies, and deletes it."""
        conn_id = conn_info['id']
        local_filepath = os.path.join(self.storage_dir, f"worker_{conn_id}_{target_filename}") # Unique temp file per worker
        downloaded_bytes = 0
        conn_info["http_attempts"] += 1
        self._increment_counter("http_download_attempts")

        session = requests.Session() # Use session for potential keep-alive

        try:
            conn_info["status"] = "http_downloading"
            conn_info["last_activity_time"] = time.time()
            # Add User-Agent? Some servers might block default requests agent
            headers = {'User-Agent': 'CSBandwidthTester/1.0'}
            with session.get(url, stream=True, timeout=HTTP_TIMEOUT, headers=headers) as response:
                response.raise_for_status() # Raise HTTPError for bad responses (4xx or 5xx)

                with open(local_filepath, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        if self._stop_event.is_set():
                            raise InterruptedError("Stop event triggered during download")
                        if chunk: # filter out keep-alive new chunks
                            f.write(chunk)
                            chunk_len = len(chunk)
                            downloaded_bytes += chunk_len
                            # --- Update REAL bandwidth counters ---
                            self._increment_counter("bytes_received", chunk_len)
                            conn_info["bytes_received"] += chunk_len
                            conn_info["last_activity_time"] = time.time()
                            # Optional: small sleep to throttle?
                            # time.sleep(0.001)

            # --- Verification ---
            conn_info["status"] = "http_verifying"
            if not os.path.exists(local_filepath):
                raise FileNotFoundError("Downloaded file not found after download completed.")

            # Optional: Check size if header was present
            content_length = response.headers.get('content-length')
            if content_length and int(content_length) != downloaded_bytes:
                 logger.warning(f"Worker {conn_id}: Size mismatch for {url}. Expected {content_length}, got {downloaded_bytes}. Keeping file.")
                 # Don't delete if size mismatch for inspection? Or delete anyway? Let's delete.
                 raise ValueError(f"Size mismatch: Expected {content_length}, Got {downloaded_bytes}")

            # --- Success ---
            conn_info["http_successes"] += 1
            self._increment_counter("http_download_successes")
            self._log_download_event(conn_id, url, "SUCCESS", downloaded_bytes, local_path=local_filepath)
            return True # Indicates success

        except requests.exceptions.Timeout:
             self._increment_counter("http_download_failures")
             self._increment_counter("runtime_connection_issues")
             self._log_download_event(conn_id, url, "TIMEOUT", downloaded_bytes, "Request timed out")
             conn_info["status"] = "timeout"
             return False
        except requests.exceptions.ConnectionError as e:
             self._increment_counter("http_download_failures")
             self._increment_counter("runtime_connection_issues")
             self._log_download_event(conn_id, url, "CONN_ERR", downloaded_bytes, str(e))
             conn_info["status"] = "error"
             return False
        except requests.exceptions.HTTPError as e:
             self._increment_counter("http_download_failures")
             # Don't count HTTP errors (like 404) as generic runtime issues unless desired
             self._log_download_event(conn_id, url, f"HTTP_{e.response.status_code}", downloaded_bytes, str(e))
             conn_info["status"] = "http_error"
             return False
        except InterruptedError:
            logger.info(f"Worker {conn_id}: Download interrupted: {url}")
            self._log_download_event(conn_id, url, "INTERRUPT", downloaded_bytes, "Test stopped")
            conn_info["status"] = "stopped"
            # Don't increment failure counters on graceful stop
            return False
        except Exception as e:
             self._increment_counter("http_download_failures")
             self._increment_counter("runtime_connection_issues")
             logger.error(f"Worker {conn_id}: Unhandled HTTP download error for {url}: {type(e).__name__} - {str(e)}", exc_info=self.verbose)
             self._log_download_event(conn_id, url, "FAILED", downloaded_bytes, f"{type(e).__name__}: {str(e)}")
             conn_info["status"] = "error"
             return False
        finally:
            # --- Cleanup ---
            if os.path.exists(local_filepath):
                try:
                    os.remove(local_filepath)
                    # Only log deletion if download wasn't interrupted/failed badly before logging success
                    if conn_info.get("status") not in ["error", "timeout", "stopped", "http_error", "conn_err"]:
                         self._log_download_event(conn_id, url, "DELETED", local_path=local_filepath)
                except OSError as e:
                    logger.error(f"Worker {conn_id}: Failed to delete temp file {local_filepath}: {e}")
            conn_info["status"] = "idle" # Reset status after attempt

    def _simulate_asset_download(self, conn_info):
        # (Simulation logic remains largely the same, but now logs differently and increments different counter)
        if not self.active or self._stop_event.is_set() or not conn_info or not conn_info.get("socket"):
            if conn_info: conn_info["status"] = "stopped" if self._stop_event.is_set() else "error"
            return False

        sock = conn_info["socket"]; conn_id = conn_info["id"]
        conn_info["status"] = "udp_simulating"; conn_info["sim_attempts"] += 1
        self._increment_counter("simulated_downloads_run") # Track that simulation ran
        conn_info["last_activity_time"] = time.time()

        try:
            # Choose random asset type and size for simulation
            asset_type = random.choice(list(DOWNLOAD_SIZES.keys())); asset_size = DOWNLOAD_SIZES[asset_type]
            asset_id = random.randint(1000, 9999); base_request = random.choice(CS_FILE_REQUESTS)
            # Use a generic request, the filename part doesn't really matter for simulation
            custom_request = base_request # Example: b"\xff\xff\xff\xffping\x00"

            # Send a small UDP packet
            sent_bytes = sock.sendto(custom_request, (self.server_ip, self.server_port))
            conn_info["bytes_sent"] += sent_bytes # Track UDP bytes sent
            self._increment_counter("bytes_sent", sent_bytes)
            conn_info["requests_sent"] += 1

            # --- SIMULATION Part ---
            # No actual recv() loop for bulk data here
            simulated_received_total = asset_size # Assume full download for simulation
            if simulated_received_total > 0:
                 # Increment counters based on simulated size
                 conn_info["bytes_received"] += simulated_received_total
                 self._increment_counter("bytes_received", simulated_received_total)

                 # Store simulated metadata (less useful now, but keep for consistency?)
                 sim_filename = f"sim_{asset_type}_{asset_id}.dat"
                 # self._store_asset_metadata(asset_type, asset_id, simulated_received_total)
                 with self.lock:
                     # Add simulated file to UI deque
                     self.last_downloaded_files.append(f"{sim_filename} ({simulated_received_total/1024:.1f}KB) [SIM]")
                     # Update simulation-specific counters if needed
                     self.asset_downloads[asset_type] += 1
                     self.asset_bandwidth[asset_type] += simulated_received_total

                 # Apply simulated delay if configured
                 if self.download_delay > 0:
                     # Simple delay based on total size
                      time.sleep(max(0.001, self.download_delay * (asset_size / (1024*1024)) )) # Delay proportional to simulated MB

            conn_info["last_activity_time"] = time.time()
            conn_info["status"] = "idle"
            return True # Simulation considered "successful" if it ran

        except socket.timeout:
            if self.verbose: logger.debug(f"Conn {conn_id}: Timeout sending UDP request for simulation.")
            self._increment_counter("runtime_connection_issues"); conn_info["status"] = "timeout"; return False
        except OSError as e:
             logger.error(f"Conn {conn_id} OS Error (UDP Simulation): {e}. Closing UDP socket.")
             try: sock.close()
             except Exception: pass
             conn_info["socket"] = None; conn_info["status"] = "error"; self._increment_counter("runtime_connection_issues"); return False
        except Exception as e:
            logger.error(f"Conn {conn_id} unexpected error during UDP simulation setup: {type(e).__name__} - {str(e)}")
            conn_info["status"] = "error"; self._increment_counter("runtime_connection_issues"); return False

    def _connection_worker(self, conn_info):
        # (Worker logic now decides between HTTP download and Simulation)
        conn_id = conn_info['id']
        if self.verbose: logger.debug(f"Worker {conn_id}: Started")
        self._increment_counter("active_workers_count")
        conn_info["status"] = "idle"

        try:
            while self.active and not self._stop_event.is_set():
                conn_info["status"] = "deciding"
                # --- Decision Logic ---
                fastdl_url_to_use = None
                map_name_to_use = None
                can_attempt_http = False

                with self.lock: # Access shared server info safely
                    fastdl_url_to_use = self.active_fastdl_url # Gets manual or discovered
                    current_map = self.server_info.get('map') if self.server_info else None
                    if fastdl_url_to_use and current_map:
                         map_name_to_use = current_map.replace('\\','/').split('/')[-1] # Basic sanitation
                         if map_name_to_use: # Ensure map name is valid
                             can_attempt_http = True

                # --- Perform Action ---
                success = False
                if can_attempt_http:
                    # Construct target URL (assuming /maps/ structure)
                    # Ensure base URL has trailing slash for urljoin
                    base = fastdl_url_to_use if fastdl_url_to_use.endswith('/') else fastdl_url_to_use + '/'
                    map_filename = f"{map_name_to_use}.bsp"
                    relative_path = f"maps/{map_filename}" # Common structure
                    full_url = urljoin(base, relative_path)

                    if self.verbose: logger.debug(f"Worker {conn_id}: Attempting HTTP download: {full_url}")
                    success = self._perform_http_download(conn_info, full_url, map_filename)
                    if not success:
                        # Optional: Fallback to simulation if HTTP fails? Or just wait?
                        # logger.warning(f"Worker {conn_id}: HTTP download failed, simulating instead.")
                        # success = self._simulate_asset_download(conn_info)
                        pass # Just let it loop and try again later

                else:
                    # Fallback to simulation if no FastDL URL or map known
                    if self.verbose: logger.debug(f"Worker {conn_id}: No FastDL URL/Map available, running simulation.")
                    if conn_info.get("socket"): # Check if UDP socket exists for simulation
                         success = self._simulate_asset_download(conn_info)
                    else:
                         # No UDP socket, maybe try to recreate or just log error?
                         logger.warning(f"Worker {conn_id}: Cannot simulate, UDP socket is unavailable.")
                         conn_info["status"] = "error"
                         self._increment_counter("runtime_connection_issues")
                         time.sleep(5) # Wait longer if in error state

                # --- Wait before next iteration ---
                # Add delay even after failures to prevent spamming
                worker_delay = random.uniform(0.5, 2.0) # Slightly longer base delay?
                conn_info["status"] = "idle"
                time.sleep(worker_delay)

        except Exception as e:
            logger.error(f"Worker {conn_id}: Unhandled loop error: {type(e).__name__} - {str(e)}", exc_info=self.verbose)
            conn_info["status"] = "error"; self._increment_counter("runtime_connection_issues")
        finally:
            self._decrement_counter("active_workers_count")
            conn_info["status"] = "stopped"
            # Close UDP socket if it exists
            sock = conn_info.get("socket")
            if sock:
                try: sock.close()
                except Exception: pass
            if self.verbose: logger.debug(f"Worker {conn_id}: Finished. Sent (UDP): {conn_info['bytes_sent']/1024:.1f}KB, Recv (HTTP+Sim): {conn_info['bytes_received']/1024:.1f}KB")

    def _update_server_info(self):
        # (Updated to also query rules and manage FastDL URL)
        if not self.server_query:
            logger.info("Server monitoring disabled.")
            return

        if self.verbose: logger.debug("Server monitor thread started.")
        last_rules_query_time = 0
        rules_query_interval = 30 # Query rules less frequently than basic info

        while self.active and not self._stop_event.is_set():
            current_status = "UNKNOWN"; ping = -1; info_for_log = {}
            timestamp = time.time()
            rules_updated = False

            try:
                # --- Get Basic Info ---
                server_info = self.server_query.get_info() # Tries to get info and challenge
                if server_info:
                    with self.lock:
                        self.server_info = server_info # Update main info
                        self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': ping,
                                    'players': server_info.get('players', 0), 'max_players': server_info.get('max_players', 0),
                                    'name': server_info.get('name','N/A'), 'map': server_info.get('map', 'N/A')}

                    # --- Get Rules (Less Frequently) ---
                    if (timestamp - last_rules_query_time > rules_query_interval):
                        logger.debug("Querying server rules...")
                        server_rules = self.server_query.get_rules()
                        last_rules_query_time = timestamp
                        if server_rules is not None: # Store even if empty dict
                             rules_updated = True
                             with self.lock:
                                 self.server_rules = server_rules
                                 self.discovered_fastdl_url = server_rules.get('sv_downloadurl')
                                 # Update active URL (prioritize manual)
                                 self.active_fastdl_url = self.manual_fastdl_url if self.manual_fastdl_url else self.discovered_fastdl_url
                                 if self.active_fastdl_url:
                                     logger.info(f"Using FastDL URL: {self.active_fastdl_url}")
                                 elif self.manual_fastdl_url is None:
                                     logger.info("No FastDL URL provided or discovered.")

                        else:
                             logger.warning("Failed to get/parse server rules.")
                             with self.lock: # Clear stale rules/url if query fails
                                self.server_rules = None
                                self.discovered_fastdl_url = None
                                self.active_fastdl_url = self.manual_fastdl_url # Revert to manual if discovery fails


                else: # Info query failed
                    with self.lock:
                        # Update status based on timeout
                        if self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT):
                            current_status = "OFFLINE"
                        else:
                            current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"
                        self.server_info = None # Clear stale info
                        self.server_rules = None # Clear rules if info fails
                        self.discovered_fastdl_url = None
                        self.active_fastdl_url = self.manual_fastdl_url # Revert to manual
                        self.server_status = current_status
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': -1,
                                    'players': -1, 'max_players': -1}

            except Exception as e: # Catch unexpected errors in this thread
                logger.error(f"Unexpected server info/rules error: {type(e).__name__} - {str(e)}", exc_info=self.verbose)
                with self.lock:
                    current_status = "ERROR"; self.server_info = None; self.server_rules = None; self.server_status = current_status
                    self.discovered_fastdl_url = None; self.active_fastdl_url = self.manual_fastdl_url
                info_for_log = {'timestamp': time.time(), 'status': current_status, 'ping': -1}

            # Log status point
            if info_for_log:
                with self.lock:
                    if rules_updated: # Add rules info if updated this cycle
                         info_for_log['rules_count'] = len(self.server_rules) if self.server_rules else 0
                         info_for_log['fastdl_discovered'] = bool(self.discovered_fastdl_url)
                         info_for_log['fastdl_active'] = bool(self.active_fastdl_url)
                    self.server_status_log.append(info_for_log)

            # Wait before next query, check stop event frequently
            sleep_interval = 0.1
            sleep_end = time.time() + self.server_info_interval
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval): break
            if self._stop_event.is_set(): break

        if self.server_query: self.server_query.close()
        if self.verbose: logger.debug("Server monitor thread finished.")

    def _display_realtime_stats(self):
        # (Updated to show HTTP stats and FastDL status)
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time

        CURSOR_TO_HOME = "\033[H"
        CLEAR_LINE = "\033[K"
        CLEAR_SCREEN_FROM_CURSOR = "\033[J"

        term_width = 80
        try: term_width = os.get_terminal_size().columns
        except OSError: pass

        while self.active and not self._stop_event.is_set():
            lines_to_print = []
            try:
                with self.lock:
                    # Gather stats
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    bytes_sent = self.bytes_sent; bytes_received = self.bytes_received
                    active_workers = self.active_workers_count; runtime_issues = self.runtime_connection_issues
                    initial_fails = self.initial_connection_failures
                    last_files = list(self.last_downloaded_files) # Now contains URLs or sim names
                    current_server_status = self.server_status
                    current_server_info = self.server_info.copy() if self.server_info else None
                    last_seen_time = self.server_last_seen
                    current_fastdl_url = self.active_fastdl_url # Get the active URL
                    http_attempts = self.http_download_attempts
                    http_success = self.http_download_successes
                    http_fails = self.http_download_failures
                    sim_runs = self.simulated_downloads_run

                # Calculate derived stats
                sent_mb = bytes_sent / (1024*1024); recv_mb = bytes_received / (1024*1024) # Now potentially real MB
                total_mb = sent_mb + recv_mb
                avg_rate_mbs = total_mb / elapsed if elapsed > 0 else 0
                avg_send_mbs = sent_mb / elapsed if elapsed > 0 else 0
                avg_recv_mbs = recv_mb / elapsed if elapsed > 0 else 0 # Potentially real rate

                # Log bandwidth point
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                     with self.lock: self.bandwidth_log_points.append((elapsed, total_mb))
                     last_bw_log_time = current_time

                # --- Format Output Lines ---
                status = "Running" if self.active else "Stopped"
                mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                header = f"--- CS Bandwidth Test (HTTP/UDP): {self.server_ip}:{self.server_port} ---".center(term_width)
                lines_to_print.append(header)
                lines_to_print.append(f" Status: {status} | Mode: {mode}".ljust(term_width))
                lines_to_print.append(f" Time: {elapsed:.1f}s".ljust(term_width))
                lines_to_print.append(f" Workers: {active_workers}/{self.num_connections} | Issues: Init={initial_fails} Run={runtime_issues}".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Server & FastDL Status]".center(term_width))

                # Server Status (similar to before)
                if self.no_server_monitor: lines_to_print.append(" Server Monitoring Disabled".ljust(term_width))
                else:
                    s_status_str = f" Server Status: {current_server_status}"
                    s_ping_str = "Ping: N/A"; s_players_str = "Players: N/A"
                    if current_server_info:
                        ping_val = current_server_info.get('ping', -1)
                        s_ping_str = f"Ping: {ping_val:>3}ms" if ping_val >= 0 else "Ping: N/A"
                        s_players_str = f"Players: {current_server_info.get('players','?')}/{current_server_info.get('max_players','?')}"
                        if current_server_info.get('bots',0) > 0: s_players_str += f" (B:{current_server_info['bots']})"
                    # Add status details if needed
                    lines_to_print.append(f"{s_status_str} | {s_ping_str} | {s_players_str}".ljust(term_width))

                    s_name_str = " Name: N/A"; s_map_str = " Map: N/A"
                    if current_server_info:
                         max_len = term_width - len(" Name: ") - 1
                         s_name_str = f" Name: {current_server_info.get('name', 'N/A')[:max_len]}"
                         max_len = term_width - len(" Map: ") - 1
                         s_map_str = f" Map: {current_server_info.get('map', 'N/A')[:max_len]}"
                    lines_to_print.append(s_name_str.ljust(term_width))
                    lines_to_print.append(s_map_str.ljust(term_width))
                    last_seen_str = f" Last Seen: {datetime.fromtimestamp(last_seen_time).strftime('%H:%M:%S')}" if last_seen_time > 0 else " Last Seen: Never"
                    lines_to_print.append(last_seen_str.ljust(term_width))

                # FastDL Status
                if current_fastdl_url:
                    url_display = current_fastdl_url[:term_width-15] + ('...' if len(current_fastdl_url) > term_width-15 else '')
                    lines_to_print.append(f" FastDL Active: {url_display}".ljust(term_width))
                elif self.manual_fastdl_url:
                    lines_to_print.append(f" FastDL Manual: {self.manual_fastdl_url} (Not currently used/valid?)".ljust(term_width))
                else:
                    lines_to_print.append(" FastDL Status: Not Provided / Not Discovered".ljust(term_width))


                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Bandwidth Usage (Actual/Sim)]".center(term_width))
                lines_to_print.append(f" Total Sent (UDP): {sent_mb:>7.2f} MB   |   Recv (HTTP+Sim): {recv_mb:>7.2f} MB".ljust(term_width))
                lines_to_print.append(f" Total Data:       {total_mb:>7.2f} MB   |   Avg Total Rate:  {avg_rate_mbs:>7.2f} MB/s".ljust(term_width))
                # lines_to_print.append(f" Avg Rates: Send:{avg_send_mbs:>6.2f} MB/s Recv:{avg_recv_mbs:>6.2f} MB/s".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Download Activity]".center(term_width))
                lines_to_print.append(f" HTTP Attempts: {http_attempts} | Success: {http_success} | Fail: {http_fails}".ljust(term_width))
                lines_to_print.append(f" Simulations Run: {sim_runs}".ljust(term_width))
                lines_to_print.append(f" Last {LAST_FILES_DISPLAY_COUNT} Events:".ljust(term_width))
                if last_files:
                    for i, fname_or_url in enumerate(reversed(last_files)): # Show most recent first
                        max_len = term_width - 4 # Room for " - "
                        lines_to_print.append(f" - {fname_or_url[:max_len]}".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_files))): lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No download events yet)".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT -1)): lines_to_print.append(" ".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("(Press Ctrl+C to stop)".center(term_width))

                # --- Perform Screen Update ---
                output_buffer = CURSOR_TO_HOME
                for line in lines_to_print:
                    output_buffer += line[:term_width] + CLEAR_LINE + "\n"
                output_buffer += CLEAR_SCREEN_FROM_CURSOR
                sys.stdout.write(output_buffer)
                sys.stdout.flush()

            except Exception as e:
                logger.error(f"Error in display thread: {type(e).__name__} - {str(e)}", exc_info=False)
                time.sleep(1)

            # Wait before next update
            sleep_interval = 0.1; sleep_end = time.time() + UI_UPDATE_INTERVAL
            while time.time() < sleep_end:
                if self._stop_event.wait(timeout=sleep_interval): break
            if self._stop_event.is_set(): break

        if self.verbose: logger.debug("Realtime display thread finished.")
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
        sys.stdout.flush()

    def start_test(self):
        # (Updated initialization)
        if self.active:
            logger.warning("Test is already running.")
            return

        logger.info("="*30 + " Starting Test " + "="*30)
        logger.info(f"Storage Directory: {self.storage_dir}")
        logger.info(f"Download Log File: {self.download_log_filepath}")
        if self.manual_fastdl_url:
             logger.info(f"Manual FastDL URL provided: {self.manual_fastdl_url}")
        else:
             logger.info("Attempting FastDL URL discovery via server rules.")

        self.active = True
        self._stop_event.clear()
        self.start_time = time.time()
        self.end_time = 0

        # Reset counters
        self.bytes_sent = 0; self.bytes_received = 0; self.bandwidth_log_points = []
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0; self.server_status_log = []
        self.asset_downloads = {k: 0 for k in DOWNLOAD_SIZES}; self.asset_bandwidth = {k: 0 for k in DOWNLOAD_SIZES}
        self.downloaded_files = []; self.last_downloaded_files.clear()
        self.http_download_attempts = 0; self.http_download_successes = 0; self.http_download_failures = 0
        self.simulated_downloads_run = 0

        # Reset server info state
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0; self.server_info = None; self.server_rules = None
        self.discovered_fastdl_url = None
        self.active_fastdl_url = self.manual_fastdl_url # Reset active URL

        self.connections = []; self.threads = []

        # Start Monitor Thread (if enabled)
        if not self.no_server_monitor and self.server_query:
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start()
            self.threads.append(self.server_info_thread)
            # Give monitor a moment to potentially get initial info/URL
            time.sleep(1.0)

        # Start Display Thread
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread)

        # Start Worker Threads
        logger.info(f"Attempting to establish {self.num_connections} worker connections...")
        initial_success = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set(): break
            conn_info = self._create_connection(i + 1) # Creates UDP socket if possible
            # Note: Connection info doesn't guarantee reachability, workers handle actual comms
            if conn_info: # Success here just means structure created
                worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
                self.connections.append(conn_info)
                worker_thread.start()
                self.threads.append(worker_thread)
                initial_success += 1
            else: # Failure likely means UDP socket creation failed
                self._increment_counter("initial_connection_failures")
            if self.num_connections > 20 and (i + 1) % 20 == 0: time.sleep(0.05) # Slow down worker start slightly

        logger.info(f"Successfully started {initial_success} workers initially. {self.initial_connection_failures} failed (likely UDP socket issue).")

        if initial_success == 0 and self.num_connections > 0:
            logger.error("FATAL: No worker threads could be started. Stopping test.")
            self.stop_test()
            return

        # --- Main Test Loop (Wait for duration or Ctrl+C) ---
        try:
            if self.continuous_mode:
                logger.info("Running in continuous mode. Press Ctrl+C to stop.")
                self._stop_event.wait() # Wait indefinitely until stop_test sets the event
                logger.info("Stop event received, finishing...")
            else:
                logger.info(f"Running timed test for {self.test_duration} seconds. Press Ctrl+C to stop early.")
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early:
                    logger.info("Test stopped early via signal.")
                else:
                    logger.info("Test duration reached.")
                    self.stop_test() # Stop naturally after duration

        except KeyboardInterrupt: # Should be caught by signal handler, but as fallback
              logger.warning("KeyboardInterrupt caught in main loop. Stopping.")
              if not self._stop_event.is_set():
                   self.stop_test()
        except Exception as e:
             logger.error(f"Error in main test execution: {e}", exc_info=self.verbose)
             self.stop_test()

    def stop_test(self):
        # (Stop logic remains mostly the same)
        if not self.active: return
        if self._stop_event.is_set(): # Prevent double stops
            logger.info("Stop process already initiated.")
            return

        logger.info("Stopping test...")
        self.active = False # Set inactive flag first
        self._stop_event.set() # Signal all threads
        self.end_time = time.time() if self.start_time > 0 else time.time()

        logger.info("Waiting for threads to complete...")
        join_timeout = 5.0 # Increase timeout slightly for potential file cleanup

        threads_to_join = self.threads[:] # Copy list
        for thread in threads_to_join:
            if thread is threading.current_thread(): continue
            if thread.is_alive():
                try:
                    if self.verbose: logger.debug(f"Joining thread: {thread.name}...")
                    thread.join(join_timeout)
                    if thread.is_alive():
                        logger.warning(f"Thread {thread.name} did not stop within timeout {join_timeout}s.")
                except Exception as e:
                    logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("All threads processed.")

        if self.server_query: self.server_query.close()

        # Close download log file handler
        if download_logger:
            for handler in download_logger.handlers[:]:
                if isinstance(handler, logging.FileHandler):
                    handler.close()
                    download_logger.removeHandler(handler)
            download_logger.info("--- Download Log Ended ---") # Log end marker (won't go to file now)


        # Final report generation
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed) # Save JSON (needs update)

        logger.info(f"Test finished. Check {self.download_log_filepath} for download details.")

    def _generate_final_report(self, duration):
        # (Updated for new stats)
        print("\n" + "="*30 + " Test Results Summary " + "="*30)
        duration = max(duration, 0.01)

        with self.lock:
            bytes_sent = self.bytes_sent; bytes_received = self.bytes_received
            http_attempts = self.http_download_attempts
            http_success = self.http_download_successes
            http_fails = self.http_download_failures
            sim_runs = self.simulated_downloads_run
            runtime_issues = self.runtime_connection_issues; initial_fails = self.initial_connection_failures
            final_server_status = self.server_status
            final_server_info = self.server_info.copy() if self.server_info else None
            server_log = self.server_status_log[:]
            final_active_url = self.active_fastdl_url

        sent_mb = bytes_sent / (1024*1024); received_mb = bytes_received / (1024*1024); total_mb = sent_mb + received_mb
        avg_rate_mbs = total_mb / duration; avg_send_mbs = sent_mb / duration; avg_recv_mbs = received_mb / duration

        server_name = "N/A"; server_map = "N/A"; avg_ping = -1; min_ping = -1; max_ping = -1
        if not self.no_server_monitor:
            # Logic to get last known name/map (same as before)
            last_valid_log = next((log for log in reversed(server_log) if log.get('status') in ['ONLINE', 'ISSUES'] and log.get('name') not in [None,'N/A','']), None)
            if last_valid_log: server_name = last_valid_log.get('name', 'N/A'); server_map = last_valid_log.get('map', 'N/A')
            elif final_server_info: server_name = final_server_info.get('name', 'N/A'); server_map = final_server_info.get('map', 'N/A')
            # Ping calculation (same as before)
            pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
            if pings: avg_ping = sum(pings)/len(pings); min_ping = min(pings); max_ping = max(pings)

        print(f"[Test Overview]")
        print(f" Target:          {self.server_ip}:{self.server_port}")
        print(f" Duration:        {duration:.2f}s")
        print(f" Mode:            {'Continuous (Stopped)' if self.continuous_mode else 'Timed'}")
        print(f" Connections:     {self.num_connections} (Target)")
        print(f" Initial Fails:   {initial_fails}")
        print(f" Runtime Issues:  {runtime_issues}")

        print("\n[Server & FastDL Status]")
        if self.no_server_monitor: print(" Server Monitoring: Disabled")
        else:
            print(f" Final Status:    {final_server_status}")
            print(f" Last Name:       {server_name}")
            print(f" Last Map:        {server_map}")
            print(f" Avg Ping:        {avg_ping:.1f} ms" if avg_ping != -1 else "N/A")
            print(f" Ping Min/Max:    {min_ping} / {max_ping} ms" if min_ping != -1 else "N/A")
        print(f" Final FastDL URL:{final_active_url if final_active_url else 'None / Not Found'}")

        print("\n[Bandwidth Usage (Actual/Sim)]")
        print(f" Total Sent (UDP):{sent_mb:>8.2f} MB")
        print(f" Total Recv(Mixed):{received_mb:>8.2f} MB")
        print(f" Total Data:      {total_mb:>8.2f} MB")
        print(f" Avg Send Rate:   {avg_send_mbs:>8.2f} MB/s")
        print(f" Avg Recv Rate:   {avg_recv_mbs:>8.2f} MB/s")
        print(f" Avg Total Rate:  {avg_rate_mbs:>8.2f} MB/s")

        print("\n[Download Activity]")
        print(f" HTTP Attempts:   {http_attempts}")
        print(f" HTTP Successes:  {http_success}")
        print(f" HTTP Failures:   {http_fails}")
        print(f" Simulations Run: {sim_runs}")
        print(f" (See {DOWNLOAD_LOG_FILENAME} for details)")

        print("="*60)

    def _save_detailed_report_json(self, duration, initial_fails=None, runtime_issues=None):
         # (Needs significant update to reflect new stats)
         with self.lock:
            duration = max(0.01, duration)
            sent_mb = self.bytes_sent / (1024*1024)
            received_mb = self.bytes_received / (1024*1024) # Mixed recv
            total_mb = sent_mb + received_mb
            avg_rate_mbs = total_mb / duration
            http_attempts = self.http_download_attempts
            http_success = self.http_download_successes
            http_fails = self.http_download_failures
            sim_runs = self.simulated_downloads_run
            server_log = self.server_status_log[:]
            initial_fails = self.initial_connection_failures if initial_fails is None else initial_fails
            runtime_issues = self.runtime_connection_issues if runtime_issues is None else runtime_issues
            final_active_url = self.active_fastdl_url
            manual_url = self.manual_fastdl_url
            discovered_url = self.discovered_fastdl_url

         report_data = {
            "test_info": {
                "target_server": f"{self.server_ip}:{self.server_port}",
                "timestamp_utc": datetime.utcnow().isoformat() + "Z",
                "duration_seconds": round(duration, 2),
                "configured_connections": self.num_connections,
                "initial_connection_failures": initial_fails,
                "runtime_connection_issues": runtime_issues,
                "udp_simulation_delay_config_s": self.download_delay, # Renamed for clarity
                "mode": "Continuous" if self.continuous_mode else "Timed",
                "server_monitoring": not self.no_server_monitor,
                "verbose_logging": self.verbose,
                "fastdl_info": {
                     "manual_url_provided": manual_url,
                     "last_discovered_url": discovered_url,
                     "last_active_url": final_active_url,
                     "http_timeout_s": HTTP_TIMEOUT,
                }
            },
            "bandwidth_summary": {
                "sent_udp_mb": round(sent_mb, 3),
                "received_mixed_mb": round(received_mb, 3),
                "total_mb": round(total_mb, 3),
                "avg_total_rate_mbs": round(avg_rate_mbs, 3),
                "start_time_unix": self.start_time,
                "end_time_unix": self.end_time,
                "bandwidth_log_points_sec_mb": [(round(t, 2), round(mb, 3)) for t, mb in self.bandwidth_log_points],
            },
            "download_activity_summary": {
                "http_attempts": http_attempts,
                "http_successes": http_success,
                "http_failures": http_fails,
                "udp_simulations_run": sim_runs,
                # Note: Detailed per-file logs are in download_log.txt
            },
            "server_status_log": server_log # Contains periodic server info
         }

         ts = int(time.time())
         report_filename = f"cs_bw_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts}.json"
         report_filepath = os.path.join(self.storage_dir, report_filename)

         try:
            with open(report_filepath, 'w') as f:
                json.dump(report_data, f, indent=2)
            logger.info(f"Detailed test report saved to: {report_filepath}")
         except Exception as e:
            logger.error(f"Failed to save detailed report '{report_filepath}': {e}")


# ==============================================================
# Signal Handling (Same as before)
# ==============================================================
def signal_handler(sig, frame):
    global tester_instance
    if tester_instance and tester_instance.active:
        if not tester_instance._stop_event.is_set():
            print('\n')
            logger.warning("Ctrl+C received! Initiating graceful shutdown...")
            # Run stop_test in a thread to prevent blocking the signal handler
            threading.Thread(target=tester_instance.stop_test, daemon=True).start()
    else:
        print('\nCtrl+C received, but no active test found or test already stopping. Exiting.')
        sys.exit(0)

# ==============================================================
# Main execution block (Added arguments)
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 Server Bandwidth Testing Tool (HTTP/UDP CLI Version)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 server.")
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="Server UDP query port.")
    parser.add_argument("-c", "--connections", type=int, default=10, help="Number of concurrent workers (use lower values for HTTP testing).") # Reduced default
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of timed test in seconds.")
    parser.add_argument("-dl", "--delay", type=float, default=0.0, help="Simulated delay factor for UDP simulation fallback (0 = no delay).") # Changed default
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging.")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run continuously until stopped (Ctrl+C).")
    parser.add_argument("--no-server-monitor", action="store_true", help="Disable querying server status/rules.")
    parser.add_argument("--storage-dir", default="cs_test_reports", help="Directory for JSON report and download log files.")
    parser.add_argument("--fastdl-url", default=None, help="Manually specify the base HTTP FastDL URL (e.g., http://my.fastdl.com/cstrike/). Overrides discovered URL.")
    # parser.add_argument("--download-maps-only", action="store_true", help="Currently only map downloads are implemented.") # Not needed as only maps implemented

    # --- Dependency Check ---
    try:
        import requests
    except ImportError:
        print("Error: The 'requests' library is required for HTTP downloads.")
        print("Please install it using: pip install requests")
        sys.exit(1)


    args = parser.parse_args()

    if args.verbose:
        logger.setLevel(logging.DEBUG)
        logger.info("Verbose logging enabled.")
    else:
        logger.setLevel(logging.INFO)

    # --- WARNING --- (Keep the warning)
    logger.warning("="*70)
    logger.warning("⚠️ IMPORTANT RESPONSIBILITY NOTICE ⚠️")
    logger.warning("You are SOLELY responsible for the use of this tool.")
    logger.warning("Performing actual file downloads (HTTP mode) can place significant load")
    logger.warning("on the target server. Obtain EXPLICIT PERMISSION before testing")
    logger.warning("any server you DO NOT own or operate.")
    logger.warning("Misuse can negatively impact server performance, incur bandwidth costs,")
    logger.warning("and is unethical and potentially illegal. Use responsibly.")
    logger.warning("="*70)
    if args.fastdl_url or not args.no_server_monitor:
        logger.warning("HTTP Download mode potentially enabled. Ensure you have permission!")
    else:
        logger.warning("Running in UDP Simulation mode only (no FastDL URL specified and monitoring disabled).")

    time.sleep(2.5) # Longer pause if HTTP might be used

    try:
        tester_instance = CS16BandwidthTester(
            server_ip=args.server_ip,
            server_port=args.port,
            num_connections=args.connections,
            test_duration=args.duration,
            download_delay=args.delay,
            verbose=args.verbose,
            storage_dir=args.storage_dir,
            continuous_mode=args.continuous,
            no_server_monitor=args.no_server_monitor,
            fastdl_url=args.fastdl_url,
            download_maps_only=True # Hardcoded as only maps are implemented
        )

        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)

        tester_instance.start_test()

        # Main thread waits here implicitly because start_test blocks until completion/stop

        logger.info("Main thread exiting.")
        sys.exit(0)

    except Exception as e:
        logger.critical(f"A critical error occurred in the main script: {type(e).__name__} - {str(e)}", exc_info=True)
        sys.exit(1)
