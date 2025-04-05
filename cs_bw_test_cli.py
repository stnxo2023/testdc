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
import requests # <--- Added for HTTP downloads
import shutil # <--- For potential file operations (if needed later)
from datetime import datetime
from urllib.parse import urljoin, urlparse # <--- To handle URLs

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150 # ms
SERVER_OFFLINE_TIMEOUT = 15 # seconds without response
LAST_FILES_DISPLAY_COUNT = 10 # Show more files now
UI_UPDATE_INTERVAL = 0.5 # How often to refresh the terminal stats (seconds)
REQUEST_TIMEOUT = 10 # Timeout for HTTP requests (seconds)
DOWNLOAD_CHUNK_SIZE = 8192 # Bytes to download per chunk

# --- Global logger setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr
)
logger = logging.getLogger('cs_real_downloader_cli')

# --- Dedicated Download Log Setup ---
download_log_file = None
def setup_download_logger(filename="download_attempts.log"):
    global download_log_file
    try:
        # Use 'a' to append if file exists
        download_log_file = open(filename, 'a', encoding='utf-8')
        download_log_file.write(f"\n--- Log Start: {datetime.now().isoformat()} ---\n")
        download_log_file.flush()
        logger.info(f"Logging download attempts to: {filename}")
    except Exception as e:
        logger.error(f"Failed to open download log file '{filename}': {e}")
        download_log_file = None

def log_download_attempt(url, status, bytes_downloaded=0, message=""):
    if download_log_file:
        try:
            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            log_entry = f"{timestamp} | URL: {url} | Status: {status} | Bytes: {bytes_downloaded} | Info: {message}\n"
            download_log_file.write(log_entry)
            download_log_file.flush()
        except Exception as e:
            # Avoid crashing the main script if logging fails
            logger.warning(f"Failed to write to download log: {e}")

# Global variable to hold the tester instance for signal handling
tester_instance = None

# ==============================================================
# ServerQuery Class (Mostly unchanged, used for map name)
# ==============================================================
class ServerQuery:
    # --- (Keep the ServerQuery class exactly as it was in your original script) ---
    # ... (previous ServerQuery code omitted for brevity) ...
    # Make sure it correctly parses the 'map' field.
    def __init__(self, server_ip, server_port=DEFAULT_PORT):
        self.server_ip = server_ip; self.server_port = server_port
        self.last_info = None; self.last_ping = 0; self.sock = None
        self.retry_count = 2; self.timeout = 1.5 # seconds

    def _create_socket(self):
        if self.sock is not None:
            try: self.sock.close()
            except Exception: pass
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); self.sock.settimeout(self.timeout)
        except Exception as e: logger.error(f"Query Socket Create Error: {e}"); self.sock = None; raise

    def get_info(self):
        if self.sock is None:
             try: self._create_socket()
             except Exception: return None
        start_time = time.time(); request = b"\xFF\xFF\xFF\xFFTSource Engine Query\x00" # Standard Source query request
        for attempt in range(self.retry_count):
            try:
                self.sock.sendto(request, (self.server_ip, self.server_port)); response, _ = self.sock.recvfrom(4096)
                end_time = time.time(); self.last_ping = int((end_time - start_time) * 1000)
                if response:
                    parsed_info = self._parse_info(response)
                    if parsed_info:
                        self.last_info = parsed_info; return parsed_info
                    else:
                        logger.debug(f"Failed to parse server response (attempt {attempt+1}). Response: {response[:100]}...") # Log start of response
                else:
                    logger.debug(f"Received empty response (attempt {attempt+1})")

            except socket.timeout:
                logger.debug(f"Server query timed out (attempt {attempt+1})")
                if attempt == self.retry_count - 1: return None # Return None after final timeout
                time.sleep(0.1) # Wait briefly before retry
            except (OSError, ValueError) as e: # ValueError might be raised by parsing attempt
                logger.warning(f"Query Error (attempt {attempt+1}): {type(e).__name__} - {str(e)}")
                self.close() # Close potentially broken socket
                return None # Return None on significant errors
            except Exception as e:
                logger.error(f"Unexpected Query Error (attempt {attempt+1}): {type(e).__name__} - {str(e)}")
                self.close()
                return None # Return None on unexpected errors
        return None # Explicitly return None if all retries fail

    def _parse_info(self, response):
        # THIS PARSING LOGIC MUST CORRECTLY EXTRACT 'map' for the download to work
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF':
                 logger.debug(f"Invalid response header: {response[:10]}")
                 return None
            response_type = response[4:5]
            offset = 5 # Start reading after the 4 x 0xFF and the type byte

            if response_type not in [b'I', b'm']:
                logger.debug(f"Unsupported response type: {response_type}")
                return None

            def read_string(data, start_offset):
                end = data.find(b'\x00', start_offset)
                if end == -1:
                    logger.warning(f"Could not find null terminator for string starting at offset {start_offset}")
                    raise ValueError("Malformed string field") # Indicate parsing failure
                return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1

            server_name, offset = read_string(response, offset)
            map_name, offset = read_string(response, offset) # <-- We need this map_name
            game_dir, offset = read_string(response, offset)
            game_desc, offset = read_string(response, offset)

            if response_type == b'I':
                if offset + 2 > len(response):
                   logger.warning(f"Response too short for AppID (Type 'I') at offset {offset}")
                   raise ValueError("Response truncated before player info")
                offset += 2

            player_count = max_players = bot_count = 0

            if offset < len(response): player_count = response[offset]; offset += 1
            else: raise ValueError("Response truncated before player count")
            if offset < len(response): max_players = response[offset]; offset += 1
            else: raise ValueError("Response truncated before max players")
            if offset < len(response): bot_count = response[offset]; offset += 1

            return {
                'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                'players': player_count, 'max_players': max_players, 'bots': bot_count,
                'ping': self.last_ping
            }
        # Keep original except blocks
        except IndexError:
             logger.warning("Index error during parsing, response might be incomplete or malformed.")
             return None
        except ValueError as e: # Catch our specific parsing errors
             logger.warning(f"Parsing value error: {e}")
             return None
        except Exception as e:
             logger.error(f"Unexpected error parsing server info: {type(e).__name__} - {str(e)}", exc_info=False) # Show traceback if debugging needed
             return None

    def close(self):
        if self.sock:
            try: self.sock.close()
            except Exception: pass
            self.sock = None

# ==============================================================
# CS16RealDownloader Class (Major Changes Here)
# ==============================================================
class CS16RealDownloader:
    def __init__(self, server_ip, server_port, fastdl_url, num_connections, test_duration,
                 storage_dir, continuous_mode, no_server_monitor, delete_after_download,
                 verbose, file_list_path):

        self.server_ip = server_ip; self.server_port = server_port
        self.num_connections = num_connections; self.test_duration = test_duration
        self.verbose = verbose; self.continuous_mode = continuous_mode
        self.storage_dir = storage_dir; self.no_server_monitor = no_server_monitor
        self.delete_after_download = delete_after_download

        # --- FastDL Setup ---
        if not fastdl_url:
            logger.error("FATAL: FastDL URL (--fastdl-url) is required for actual downloads.")
            raise ValueError("FastDL URL is missing.")
        # Ensure URL ends with a slash
        self.fastdl_base_url = fastdl_url if fastdl_url.endswith('/') else fastdl_url + '/'
        logger.info(f"Using FastDL base URL: {self.fastdl_base_url}")

        # --- File List ---
        self.files_to_try = []
        self.current_map_file = None # Will be updated by server monitor
        self._load_file_list(file_list_path)
        # Add some common default files if the list is empty (optional)
        if not self.files_to_try:
             logger.warning("No file list provided or file list empty. Will rely solely on current map.")
             # Example defaults:
             # self.files_to_try.extend([
             #     "sound/ambience/alien_cycletone.wav", "sprites/laserbeam.spr",
             #     "models/player.mdl", "overviews/de_dust2.bmp"
             # ])

        if not os.path.exists(self.storage_dir):
            try:
                os.makedirs(self.storage_dir)
                logger.info(f"Created storage directory: {self.storage_dir}")
            except OSError as e:
                logger.error(f"Failed to create storage directory '{self.storage_dir}': {e}")
                self.storage_dir = "." # Fallback to current dir

        self.active = False; self.threads = []
        self.lock = threading.Lock()
        self._stop_event = threading.Event()

        # --- Counters for REAL bandwidth ---
        self.bytes_sent_http_requests = 0 # Minimal, just request headers
        self.bytes_received_http = 0      # THIS IS THE REAL DOWNLOADED DATA
        self.files_downloaded_count = 0
        self.files_failed_count = 0
        self.start_time = 0; self.end_time = 0
        self.active_workers_count = 0

        self.server_query = ServerQuery(server_ip, server_port) if not self.no_server_monitor else None
        self.server_info = None; self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0
        self.server_info_thread = None; self.server_info_interval = 5 # Query less often maybe
        self.server_status_log = [] # Keep this for context

        # Use deque for recent files display
        self.last_download_activity = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        self.bandwidth_log_points = [] # Track real download rate

        self.display_thread = None
        self.session = requests.Session() # Use a session for potential connection reuse

    def _load_file_list(self, file_path):
        if file_path:
            try:
                with open(file_path, 'r') as f:
                    for line in f:
                        file = line.strip()
                        # Basic validation: remove leading slashes, ignore empty
                        if file and not file.startswith('#'): # Allow comments
                            self.files_to_try.append(file.lstrip('/\\'))
                logger.info(f"Loaded {len(self.files_to_try)} file paths from '{file_path}'")
            except FileNotFoundError:
                logger.error(f"File list not found: {file_path}")
            except Exception as e:
                logger.error(f"Error reading file list '{file_path}': {e}")
        else:
             logger.info("No file list path specified.")


    def _increment_counter(self, counter_name, value=1):
        with self.lock: setattr(self, counter_name, getattr(self, counter_name) + value)
    def _decrement_counter(self, counter_name, value=1): self._increment_counter(counter_name, -value)

    def _get_file_to_download(self):
        """Selects a file path to attempt downloading."""
        with self.lock:
            # Prioritize current map if available
            if self.current_map_file and random.random() < 0.6: # 60% chance to try map
                 # Check if it's already in the list to avoid duplicates if map name was also in file list
                 if self.current_map_file not in self.files_to_try:
                     return self.current_map_file

            # Choose randomly from the provided list
            if self.files_to_try:
                 return random.choice(self.files_to_try)

            # Fallback if list is empty and map isn't set yet
            return None


    def _perform_http_download(self, worker_id, file_rel_path):
        """Attempts to download a single file via HTTP."""
        if not file_rel_path or self._stop_event.is_set():
            return False, 0

        # Construct full URL (handle potential double slashes, etc.)
        # file_rel_path should be like 'maps/de_dust2.bsp'
        try:
             full_url = urljoin(self.fastdl_base_url, file_rel_path.replace('\\', '/'))
        except Exception as e:
             logger.error(f"Worker {worker_id}: Invalid URL construction for path '{file_rel_path}' with base '{self.fastdl_base_url}': {e}")
             log_download_attempt(f"Base:{self.fastdl_base_url} Path:{file_rel_path}", "URL_ERROR", 0, str(e))
             self._increment_counter("files_failed_count")
             with self.lock: self.last_download_activity.append(f"{file_rel_path} - URL ERR")
             return False, 0


        # Construct local path
        # Ensure the path is relative and safe
        if file_rel_path.startswith('/') or '..' in file_rel_path:
             logger.warning(f"Worker {worker_id}: Skipped potentially unsafe file path '{file_rel_path}'")
             log_download_attempt(full_url, "PATH_SKIP", 0, "Unsafe path")
             self._increment_counter("files_failed_count") # Count as failure
             with self.lock: self.last_download_activity.append(f"{file_rel_path} - PATH SKIP")
             return False, 0

        local_filepath = os.path.join(self.storage_dir, file_rel_path)
        local_dir = os.path.dirname(local_filepath)

        if self.verbose: logger.debug(f"Worker {worker_id}: Attempting DL: {full_url} -> {local_filepath}")

        bytes_downloaded = 0
        success = False
        status_code = -1
        error_msg = ""

        try:
            # Create necessary local directories
            os.makedirs(local_dir, exist_ok=True)

            # Perform the download using the session
            with self.session.get(full_url, stream=True, timeout=REQUEST_TIMEOUT) as response:
                status_code = response.status_code
                response.raise_for_status() # Raise HTTPError for bad responses (4xx or 5xx)

                with open(local_filepath, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=DOWNLOAD_CHUNK_SIZE):
                        if self._stop_event.is_set():
                             error_msg = "Download interrupted by stop signal."
                             log_download_attempt(full_url, "INTERRUPTED", bytes_downloaded, error_msg)
                             raise StopIteration("Download stopped") # Custom exception or break

                        if chunk: # filter out keep-alive new chunks
                            f.write(chunk)
                            chunk_len = len(chunk)
                            bytes_downloaded += chunk_len
                            # Update global counter under lock for accuracy
                            self._increment_counter("bytes_received_http", chunk_len)
                            # We don't track HTTP request bytes sent accurately, it's minor
                            # self._increment_counter("bytes_sent_http_requests", ...)

                # If loop completes without error
                success = True
                log_download_attempt(full_url, f"OK ({status_code})", bytes_downloaded)
                if self.verbose: logger.debug(f"Worker {worker_id}: Success DL: {file_rel_path} ({bytes_downloaded} bytes)")

        except requests.exceptions.Timeout:
            error_msg = f"Timeout after {REQUEST_TIMEOUT}s"
            logger.warning(f"Worker {worker_id}: Timeout downloading {full_url}")
            log_download_attempt(full_url, "TIMEOUT", bytes_downloaded, error_msg)
        except requests.exceptions.HTTPError as e:
             error_msg = f"HTTP Error {e.response.status_code}"
             # Log 404s less loudly maybe
             log_level = logging.WARNING if e.response.status_code == 404 else logging.ERROR
             logger.log(log_level, f"Worker {worker_id}: {error_msg} for {full_url}")
             log_download_attempt(full_url, f"HTTP_ERR_{status_code}", bytes_downloaded, str(e.response.reason))
        except requests.exceptions.RequestException as e:
             error_msg = f"Connection Error: {type(e).__name__}"
             logger.error(f"Worker {worker_id}: Failed request for {full_url}: {e}")
             log_download_attempt(full_url, "CONN_ERROR", bytes_downloaded, str(e))
        except (OSError, IOError) as e:
             error_msg = f"File System Error: {e}"
             logger.error(f"Worker {worker_id}: Error writing file {local_filepath}: {e}")
             log_download_attempt(full_url, "FS_ERROR", bytes_downloaded, str(e))
        except StopIteration: # Handle our custom stop signal
             pass # Already logged
        except Exception as e:
             error_msg = f"Unexpected Error: {type(e).__name__}"
             logger.error(f"Worker {worker_id}: Unexpected error downloading {full_url}: {e}", exc_info=self.verbose)
             log_download_attempt(full_url, "UNEXPECTED_ERR", bytes_downloaded, str(e))

        # Update counters and activity log
        with self.lock:
            if success:
                self.files_downloaded_count += 1
                self.last_download_activity.append(f"{file_rel_path} ({bytes_downloaded/1024:.1f}K) OK")
                # --- Optional: Delete after download ---
                if self.delete_after_download:
                    try:
                        os.remove(local_filepath)
                        if self.verbose: logger.debug(f"Worker {worker_id}: Deleted {local_filepath}")
                        self.last_download_activity.append(f"{file_rel_path} - DELETED")
                    except OSError as e:
                        logger.warning(f"Worker {worker_id}: Failed to delete {local_filepath}: {e}")
                        self.last_download_activity.append(f"{file_rel_path} - DEL FAILED")

            else:
                self.files_failed_count += 1
                status_tag = f"ERR {status_code}" if status_code > 0 else "FAILED"
                self.last_download_activity.append(f"{file_rel_path} - {status_tag}")
                 # Attempt to clean up partially downloaded file on failure
                if os.path.exists(local_filepath) and bytes_downloaded > 0:
                    try: os.remove(local_filepath); logger.debug(f"Cleaned up partial file: {local_filepath}")
                    except OSError: logger.warning(f"Could not remove partial file: {local_filepath}")


        return success, bytes_downloaded


    def _connection_worker(self, worker_id):
        """Worker thread that repeatedly tries to download files."""
        if self.verbose: logger.debug(f"Worker {worker_id}: Started")
        self._increment_counter("active_workers_count")
        try:
            while self.active and not self._stop_event.is_set():
                file_to_try = self._get_file_to_download()

                if not file_to_try:
                    # No files available (list empty and map unknown?)
                    logger.debug(f"Worker {worker_id}: No file available to download, sleeping.")
                    time.sleep(2.0) # Wait longer if there's nothing to do
                    continue

                # Perform the actual download attempt
                success, bytes_dl = self._perform_http_download(worker_id, file_to_try)

                # Wait before next attempt
                # Make delay shorter if download failed (e.g. 404), maybe longer if succeeded
                delay_base = 0.1 if success else 0.5
                worker_delay = random.uniform(delay_base, delay_base + 0.2)
                time.sleep(worker_delay)

        except Exception as e:
            logger.error(f"Worker {worker_id}: Unhandled loop error: {type(e).__name__} - {str(e)}", exc_info=self.verbose)
            # Consider incrementing a dedicated worker error counter
        finally:
            self._decrement_counter("active_workers_count")
            if self.verbose: logger.debug(f"Worker {worker_id}: Finished.")


    def _update_server_info(self):
        """Updates server info (esp. map name) periodically."""
        if not self.server_query: return # Skip if monitoring disabled
        if self.verbose: logger.debug("Server monitor thread started.")

        while self.active and not self._stop_event.is_set():
            current_status = "UNKNOWN"; ping = -1; info_for_log = {}
            map_name = None
            try:
                server_info = self.server_query.get_info()
                timestamp = time.time()
                if server_info:
                    with self.lock:
                        self.server_info = server_info; self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                        # --- Get the map name ---
                        map_name = server_info.get('map')
                        if map_name:
                            # Construct the relative path for download
                            self.current_map_file = f"maps/{map_name}.bsp"
                            if self.verbose: logger.debug(f"Server Map Updated: {self.current_map_file}")
                        else:
                            # Map name not found in query? Clear it.
                            self.current_map_file = None
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': ping, 'map': map_name} # Add map to log
                else:
                    with self.lock:
                        if self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT):
                            current_status = "OFFLINE"
                        else: current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"
                        self.server_info = None; self.server_status = current_status
                        self.current_map_file = None # Clear map if server offline/issues
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': -1}

            except Exception as e:
                logger.error(f"Unexpected server info error: {type(e).__name__} - {str(e)}")
                with self.lock:
                    current_status = "ERROR"; self.server_info = None; self.server_status = current_status
                    self.current_map_file = None # Clear map on error
                info_for_log = {'timestamp': time.time(), 'status': current_status, 'ping': -1}

            if info_for_log:
                with self.lock: self.server_status_log.append(info_for_log)

            # Wait before next query
            sleep_interval = 0.1
            sleep_end = time.time() + self.server_info_interval
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval): break
            if self._stop_event.is_set(): break

        if self.server_query: self.server_query.close()
        if self.verbose: logger.debug("Server monitor thread finished.")

    def _display_realtime_stats(self):
        """Displays real-time stats, focusing on actual downloads."""
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time

        CURSOR_TO_HOME = "\033[H"; CLEAR_LINE = "\033[K"; CLEAR_SCREEN_FROM_CURSOR = "\033[J"
        term_width = 80
        try: term_width = os.get_terminal_size().columns
        except OSError: logger.warning("Could not detect terminal width, using default 80."); term_width = 80

        while self.active and not self._stop_event.is_set():
            lines_to_print = []
            try:
                with self.lock:
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    # --- Get REAL download stats ---
                    bytes_received = self.bytes_received_http
                    files_ok = self.files_downloaded_count
                    files_err = self.files_failed_count
                    active_workers = self.active_workers_count
                    last_activity = list(self.last_download_activity) # Copy activity list
                    current_server_status = self.server_status
                    current_map = self.current_map_file # Get current map

                # Calculate derived stats
                recv_mb = bytes_received / (1024*1024)
                avg_recv_mbs = recv_mb / elapsed if elapsed > 0 else 0

                # Log bandwidth point
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                     with self.lock: self.bandwidth_log_points.append((elapsed, recv_mb))
                     last_bw_log_time = current_time

                # --- Format Output Lines ---
                status = "Running" if self.active else "Stopped"
                mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                header = f"--- CS 1.6 REAL Bandwidth Test ({self.server_ip}:{self.server_port}) ---".center(term_width)
                lines_to_print.append(header)
                lines_to_print.append(f" Target FastDL: {self.fastdl_base_url}".ljust(term_width))

                line_status = f" Status: {status} | Mode: {mode}"
                line_time = f"Time: {elapsed:.1f}s"
                lines_to_print.append(f"{line_status:<{max(0, term_width - len(line_time))}}{line_time}")

                line_workers = f" Workers: {active_workers}/{self.num_connections}"
                line_files = f"Files OK: {files_ok} Failed: {files_err}"
                lines_to_print.append(f"{line_workers:<{max(0, term_width - len(line_files))}}{line_files}")

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Server Status (UDP Query)]".center(term_width)) # Clarify source

                if self.no_server_monitor:
                     lines_to_print.append(" UDP Monitoring Disabled".ljust(term_width))
                     lines_to_print.append(f" Current Map: UNKNOWN".ljust(term_width))
                else:
                     # (Keep the server status display logic mostly the same as before)
                     # ... but maybe add the current map derived from it ...
                    s_status_str = f" Status: {current_server_status}"
                    s_ping_str = "Ping: N/A"
                    s_map_str = "Map: UNKNOWN"
                    if self.server_info: # Use locked info if available
                       ping_val = self.server_info.get('ping', -1)
                       s_ping_str = f"Ping: {ping_val:>3}ms" if ping_val >= 0 else "Ping: N/A"
                       map_val = self.server_info.get('map', 'UNKNOWN')
                       s_map_str = f"Map: {map_val[:term_width-5]}" # Truncate map name

                    width_status = len(s_status_str)
                    width_ping = len(s_ping_str)
                    spaces1 = max(1, (term_width - width_status - width_ping) // 2)
                    lines_to_print.append(f"{s_status_str}{' '*spaces1}{s_ping_str}".ljust(term_width))
                    lines_to_print.append(s_map_str.ljust(term_width))


                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Real Bandwidth Usage (HTTP)]".center(term_width)) # Clarify source
                bw_line1 = f" Total Received: {recv_mb:>8.2f} MB"
                bw_line2 = f" Avg Recv Rate:  {avg_recv_mbs:>8.2f} MB/s"
                lines_to_print.append(bw_line1.ljust(term_width))
                lines_to_print.append(bw_line2.ljust(term_width))


                lines_to_print.append("-" * term_width)
                lines_to_print.append(f"[Last {LAST_FILES_DISPLAY_COUNT} Download Activities]".center(term_width))
                if last_activity:
                    for i, activity in enumerate(reversed(last_activity)): # Show newest first
                        max_len = term_width - 2 # Room for padding
                        lines_to_print.append(f" {activity[:max_len]}".ljust(term_width))
                    # Pad if needed
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_activity))):
                        lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No download attempts yet)".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT -1)):
                       lines_to_print.append(" ".ljust(term_width))


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
            sleep_interval = 0.1
            sleep_end = time.time() + UI_UPDATE_INTERVAL
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval): break
            if self._stop_event.is_set(): break

        if self.verbose: logger.debug("Realtime display thread finished.")
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
        sys.stdout.flush()


    def start_test(self):
        if self.active:
            logger.warning("Test is already running.")
            return

        logger.info("="*30 + " Starting REAL Download Test " + "="*30)
        self.active = True
        self._stop_event.clear()
        self.start_time = time.time()
        self.end_time = 0

        # Reset counters
        self.bytes_sent_http_requests = 0; self.bytes_received_http = 0
        self.files_downloaded_count = 0; self.files_failed_count = 0
        self.active_workers_count = 0; self.server_status_log = []
        self.last_download_activity.clear(); self.bandwidth_log_points = []
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0; self.server_info = None; self.current_map_file = None


        self.threads = []

        # Start UDP server monitor first (to get map name)
        if not self.no_server_monitor and self.server_query:
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start()
            self.threads.append(self.server_info_thread)
            # Give it a moment to potentially get the first map name
            time.sleep(0.5)

        # Start display thread
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread)

        # Start worker threads
        logger.info(f"Starting {self.num_connections} download workers...")
        for i in range(self.num_connections):
            if self._stop_event.is_set(): break
            worker_thread = threading.Thread(target=self._connection_worker, args=(i + 1,), name=f"Worker-{i+1}", daemon=True)
            # No initial connection check needed like UDP sockets
            worker_thread.start()
            self.threads.append(worker_thread)
            if self.num_connections > 20 and (i + 1) % 20 == 0: time.sleep(0.05) # Small stagger

        logger.info(f"All {self.num_connections} workers launched.")

        try:
            if self.continuous_mode:
                self._stop_event.wait() # Wait indefinitely until stop signal
                logger.info("Stop event received, finishing...")
            else:
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early:
                    logger.info("Test stopped early via signal.")
                else:
                    logger.info("Test duration reached.")
                    self.stop_test()

        except Exception as e:
             logger.error(f"Error in main test execution: {e}")
             self.stop_test() # Ensure cleanup on error

    def stop_test(self):
        if not self.active: return

        logger.info("Stopping test...")
        self.active = False
        self._stop_event.set()
        self.end_time = time.time() if self.start_time > 0 else time.time()

        logger.info("Waiting for threads to complete...")
        join_timeout = 5.0 # Increase timeout slightly as downloads might take time

        threads_to_join = self.threads[:]
        for thread in threads_to_join:
             if thread is threading.current_thread(): continue
             if thread.is_alive():
                try:
                    if self.verbose: logger.debug(f"Joining thread: {thread.name}...")
                    thread.join(join_timeout)
                    if thread.is_alive(): logger.warning(f"Thread {thread.name} did not stop within timeout.")
                except Exception as e: logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("All threads processed.")

        if self.server_query: self.server_query.close()
        self.session.close() # Close the requests session
        if download_log_file:
            try:
                 download_log_file.write(f"--- Log End: {datetime.now().isoformat()} ---\n")
                 download_log_file.close()
            except: pass # Ignore errors closing log

        # Final Report
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed) # Save JSON report

        logger.info("Test finished.")


    def _generate_final_report(self, duration):
        print("\n" + "="*30 + " REAL Download Test Results " + "="*30)
        duration = max(duration, 0.01)

        with self.lock:
            bytes_received = self.bytes_received_http
            files_ok = self.files_downloaded_count
            files_err = self.files_failed_count
            # Get final server status info if available
            final_server_status = self.server_status
            final_map = self.current_map_file or "UNKNOWN"
            server_log = self.server_status_log[:]

        received_mb = bytes_received / (1024*1024)
        avg_recv_mbs = received_mb / duration

        avg_ping = -1; min_ping = -1; max_ping = -1
        if not self.no_server_monitor:
             pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
             if pings: avg_ping = sum(pings)/len(pings); min_ping = min(pings); max_ping = max(pings)


        print(f"[Test Overview]")
        print(f" Game Server:     {self.server_ip}:{self.server_port}")
        print(f" FastDL URL:      {self.fastdl_base_url}")
        print(f" Duration:        {duration:.2f}s")
        print(f" Mode:            {'Continuous (Stopped)' if self.continuous_mode else 'Timed'}")
        print(f" Workers:         {self.num_connections}")
        print(f" Delete Files:    {self.delete_after_download}")

        print("\n[Download Results (HTTP)]")
        print(f" Files OK:        {files_ok}")
        print(f" Files Failed:    {files_err} (Check download_attempts.log)")
        print(f" Total Received:  {received_mb:.2f} MB")
        print(f" Avg Recv Rate:   {avg_recv_mbs:.2f} MB/s")

        print("\n[Server Status (UDP Query)]")
        if self.no_server_monitor:
            print(" Monitoring:      Disabled")
        else:
            print(f" Final Status:    {final_server_status}")
            print(f" Last Known Map:  {final_map}")
            print(f" Avg Ping:        {avg_ping:.1f} ms" if avg_ping != -1 else "N/A")
            print(f" Ping Min/Max:    {min_ping} / {max_ping} ms" if min_ping != -1 else "N/A")

        print("="*60)

    def _save_detailed_report_json(self, duration):
         # Save a JSON report similar to before, but with real download data
         with self.lock:
            duration = max(0.01, duration)
            received_mb = self.bytes_received_http / (1024*1024)
            avg_recv_mbs = received_mb / duration
            files_ok = self.files_downloaded_count
            files_err = self.files_failed_count
            server_log = self.server_status_log[:]

         report_data = {
            "test_info": {
                "test_type": "REAL_HTTP_DOWNLOAD",
                "game_server": f"{self.server_ip}:{self.server_port}",
                "fastdl_url": self.fastdl_base_url,
                "timestamp_utc": datetime.utcnow().isoformat() + "Z",
                "duration_seconds": round(duration, 2),
                "configured_workers": self.num_connections,
                "delete_files_after_download": self.delete_after_download,
                "mode": "Continuous" if self.continuous_mode else "Timed",
                "server_udp_monitoring": not self.no_server_monitor,
                "verbose_logging": self.verbose,
            },
            "download_summary": {
                "files_downloaded_successfully": files_ok,
                "files_failed_or_skipped": files_err,
                "total_received_mb": round(received_mb, 3),
                "avg_receive_rate_mbs": round(avg_recv_mbs, 3),
                "start_time_unix": self.start_time,
                "end_time_unix": self.end_time,
                "bandwidth_log_points_sec_mb": [(round(t, 2), round(mb, 3)) for t, mb in self.bandwidth_log_points],
            },
             "server_status_log": server_log # Keep UDP query log for context
         }

         ts = int(time.time())
         report_filename = f"cs_real_dl_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts}.json"
         report_filepath = os.path.join(self.storage_dir, report_filename)

         try:
            with open(report_filepath, 'w') as f: json.dump(report_data, f, indent=2)
            logger.info(f"Detailed JSON test report saved to: {report_filepath}")
         except Exception as e:
            logger.error(f"Failed to save detailed JSON report '{report_filepath}': {e}")


# ==============================================================
# Signal Handling
# ==============================================================
def signal_handler(sig, frame):
    global tester_instance
    if tester_instance and tester_instance.active:
        if not tester_instance._stop_event.is_set():
            print('\n')
            logger.warning("Ctrl+C received! Initiating graceful shutdown...")
            # Run stop_test in a thread to prevent potential blocking in signal handler
            threading.Thread(target=tester_instance.stop_test, daemon=True).start()
    else:
        print('\nCtrl+C received, but no active test found or test already stopping. Exiting.')
        if download_log_file: # Try to close log file on immediate exit too
             try: download_log_file.close()
             except: pass
        sys.exit(0)

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 Server REAL Bandwidth Testing Tool (HTTP FastDL)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    # --- Essential Arguments ---
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 GAME server (for UDP queries).")
    parser.add_argument("--fastdl-url", required=True, help="Base URL of the server's FastDL repository (e.g., http://my.fastdl.com/cs/). REQUIRED.")

    # --- Optional Arguments ---
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="GAME server UDP port (for queries).")
    parser.add_argument("-c", "--connections", type=int, default=10, help="Number of concurrent download workers.")
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of timed test in seconds.")
    parser.add_argument("--storage-dir", default="cs_downloads", help="Directory to save downloaded files and reports.")
    parser.add_argument("--file-list", help="Path to a text file containing relative file paths to download (one per line, e.g., maps/de_dust2.bsp).")
    parser.add_argument("--delete-after-download", action="store_true", help="Delete files locally immediately after successful download.")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging.")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run continuously until stopped (Ctrl+C).")
    parser.add_argument("--no-server-monitor", action="store_true", help="Disable querying game server status via UDP (will not get current map automatically).")
    parser.add_argument("--download-log", default="download_attempts.log", help="Filename for logging individual download attempts.")

    args = parser.parse_args()

    if args.verbose: logger.setLevel(logging.DEBUG)
    else: logger.setLevel(logging.INFO)

    # Setup dedicated download logger
    setup_download_logger(os.path.join(args.storage_dir, args.download_log)) # Place log in storage dir

    logger.warning("="*70)
    logger.warning("⚠️ IMPORTANT RESPONSIBILITY NOTICE ⚠️")
    logger.warning("This tool performs REAL file downloads from the specified FastDL URL.")
    logger.warning("This WILL consume bandwidth and resources on the target FastDL host.")
    logger.warning("Ensure you have EXPLICIT PERMISSION before testing any server/FastDL.")
    logger.warning("Misuse can negatively impact services and is unethical. Use responsibly.")
    logger.warning("="*70)
    time.sleep(2.0)

    try:
        # Ensure storage dir exists before initializing tester which might use it
        if not os.path.exists(args.storage_dir):
            try: os.makedirs(args.storage_dir); logger.info(f"Created base directory: {args.storage_dir}")
            except OSError as e: logger.error(f"Cannot create storage directory '{args.storage_dir}': {e}. Reports/logs may fail.")

        tester_instance = CS16RealDownloader(
            server_ip=args.server_ip,
            server_port=args.port,
            fastdl_url=args.fastdl_url,
            num_connections=args.connections,
            test_duration=args.duration,
            storage_dir=args.storage_dir,
            continuous_mode=args.continuous,
            no_server_monitor=args.no_server_monitor,
            delete_after_download=args.delete_after_download,
            verbose=args.verbose,
            file_list_path=args.file_list
        )

        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)

        tester_instance.start_test()

        # Main thread now waits implicitly if start_test blocks (timed mode)
        # or waits on the stop_event (continuous mode) which is handled internally.
        logger.info("Main thread finished waiting for test completion.")
        sys.exit(0)

    except ValueError as e:
         # Catch specific init errors like missing URL
         logger.error(f"Configuration Error: {e}")
         sys.exit(1)
    except Exception as e:
        logger.error(f"An critical error occurred in the main script: {type(e).__name__} - {str(e)}", exc_info=True)
        sys.exit(1)
    finally:
        # Ensure log file is closed even if main crashes early
        if download_log_file and not download_log_file.closed:
            try: download_log_file.close()
            except: pass
