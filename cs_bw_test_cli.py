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
import sys # Required for sys.stdout, sys.stderr
import signal
from datetime import datetime

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150 # ms
SERVER_OFFLINE_TIMEOUT = 15 # seconds without response
LAST_FILES_DISPLAY_COUNT = 5 # How many recent filenames to show in UI
UI_UPDATE_INTERVAL = 0.5 # How often to refresh the terminal stats (seconds)
CONNECTION_CHECK_INTERVAL = 2.0 # How often worker status is checked (less critical now)

# Common CS 1.6 file requests (same as before)
CS_FILE_REQUESTS = [
    b"\xff\xff\xff\xffgetinfo\x00", b"\xff\xff\xff\xffgetstatus\x00",
    b"\xff\xff\xff\xffrcon", b"\xff\xff\xff\xffping\x00",
    b"\xff\xff\xff\xffdetails\x00", b"\xff\xff\xff\xffplayers\x00",
    b"\xff\xff\xff\xffrules\x00", b"\xff\xff\xff\xffchallenge\x00",
]
DOWNLOAD_SIZES = { "map": 20*1024*1024, "model": 2*1024*1024, "sound": 512*1024, "sprite": 128*1024, "texture": 1*1024*1024 }

# --- Global logger setup ---
# Configure logging for terminal output
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr # Log messages go to stderr, stats go to stdout
)
logger = logging.getLogger('cs_bandwidth_tester_cli')

# Global variable to hold the tester instance for signal handling
tester_instance = None

# ==============================================================
# ServerQuery Class (Updated _parse_info)
# ==============================================================
class ServerQuery:
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
        # Forcing old GoldSrc style reply often works too: request = b"\xff\xff\xff\xffgetinfo\x00"
        for attempt in range(self.retry_count):
            try:
                self.sock.sendto(request, (self.server_ip, self.server_port)); response, _ = self.sock.recvfrom(4096)
                end_time = time.time(); self.last_ping = int((end_time - start_time) * 1000)
                if response:
                    parsed_info = self._parse_info(response)
                    if parsed_info:
                        self.last_info = parsed_info; return parsed_info
                    else:
                        # Don't raise ValueError, just log and return None if parsing fails
                        logger.debug(f"Failed to parse server response (attempt {attempt+1}). Response: {response[:100]}...") # Log start of response
                        # Continue to next retry if parsing fails
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
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF':
                 logger.debug(f"Invalid response header: {response[:10]}")
                 return None
            response_type = response[4:5]
            offset = 5 # Start reading after the 4 x 0xFF and the type byte

            # Handle different response types if necessary, focusing on 'I' (Source) and 'm' (GoldSrc)
            if response_type not in [b'I', b'm']:
                logger.debug(f"Unsupported response type: {response_type}")
                return None

            # --- Common String Fields (Name, Map, Folder, GameDesc) ---
            # Read null-terminated strings carefully
            def read_string(data, start_offset):
                end = data.find(b'\x00', start_offset)
                if end == -1:
                    logger.warning(f"Could not find null terminator for string starting at offset {start_offset}")
                    raise ValueError("Malformed string field") # Indicate parsing failure
                return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1

            server_name, offset = read_string(response, offset)
            map_name, offset = read_string(response, offset)
            game_dir, offset = read_string(response, offset)
            game_desc, offset = read_string(response, offset)

            # --- Fields After Strings (Can Vary) ---
            # For Source ('I'): Skip AppID (2 bytes)
            if response_type == b'I':
                if offset + 2 > len(response):
                   logger.warning(f"Response too short for AppID (Type 'I') at offset {offset}")
                   raise ValueError("Response truncated before player info")
                # app_id = int.from_bytes(response[offset:offset+2], 'little') # Example if needed
                offset += 2

            # --- Player Info (Players, Max Players, Bots) ---
            # Read as single bytes
            player_count = max_players = bot_count = 0 # Defaults

            if offset < len(response):
                player_count = response[offset]
                offset += 1
            else:
                 logger.warning(f"Response truncated before player count at offset {offset}")
                 raise ValueError("Response truncated before player info")

            if offset < len(response):
                max_players = response[offset]
                offset += 1
            else:
                 logger.warning(f"Response truncated before max players at offset {offset}")
                 raise ValueError("Response truncated before player info")

            # Bot count might not always be present, handle optional field
            if offset < len(response):
                 # Check for other fields before bot count if protocol specifics are known
                 # Example: Server type, OS might be here in some responses
                 # Assuming bot count is next for simplicity with common CS servers
                 bot_count = response[offset]
                 offset += 1
            # else: # Bot count is optional, don't raise error if missing
            #     logger.debug("Response ended before bot count (optional field).")

            # You might need to parse further fields like server type, OS, visibility, VAC status
            # depending on the exact server and required info. Add parsing here if needed.

            # --- Final Return ---
            return {
                'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                'players': player_count, 'max_players': max_players, 'bots': bot_count,
                'ping': self.last_ping # Ping is measured externally
            }

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
# CS16BandwidthTester Class (Updated _display_realtime_stats)
# ==============================================================
class CS16BandwidthTester:
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 download_delay, verbose, storage_dir, continuous_mode, no_server_monitor):

        self.server_ip = server_ip; self.server_port = server_port
        self.num_connections = num_connections; self.test_duration = test_duration
        self.download_delay = max(0, download_delay); self.verbose = verbose
        self.continuous_mode = continuous_mode; self.storage_dir = storage_dir
        self.no_server_monitor = no_server_monitor

        if not os.path.exists(self.storage_dir):
            try:
                os.makedirs(self.storage_dir)
                logger.info(f"Created storage directory: {self.storage_dir}")
            except OSError as e:
                logger.error(f"Failed to create storage directory '{self.storage_dir}': {e}")
                self.storage_dir = "."

        self.active = False; self.connections = []; self.threads = []
        self.lock = threading.Lock()
        self._stop_event = threading.Event()

        self.bytes_sent = 0; self.bytes_received = 0
        self.start_time = 0; self.end_time = 0
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0

        self.server_query = ServerQuery(server_ip, server_port) if not self.no_server_monitor else None
        self.server_info = None; self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0
        self.server_info_thread = None; self.server_info_interval = 3
        self.server_status_log = []

        self.asset_downloads = {k: 0 for k in DOWNLOAD_SIZES}; self.asset_bandwidth = {k: 0 for k in DOWNLOAD_SIZES}
        self.downloaded_files = []; self.last_downloaded_files = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        self.bandwidth_log_points = []

        self.display_thread = None

    def _increment_counter(self, counter_name, value=1):
        with self.lock: setattr(self, counter_name, getattr(self, counter_name) + value)
    def _decrement_counter(self, counter_name, value=1): self._increment_counter(counter_name, -value)

    def _create_connection(self, conn_id):
        sock = None
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); sock.settimeout(2.0)
        except Exception as e: logger.error(f"Conn {conn_id}: Socket create error: {e}"); return None
        return {"id": conn_id, "socket": sock, "bytes_sent": 0, "bytes_received": 0, "last_request_time": 0, "requests_sent": 0, "assets_downloaded": {k: 0 for k in DOWNLOAD_SIZES}, "asset_bytes": {k: 0 for k in DOWNLOAD_SIZES}, "status": "running"}

    def _store_asset_metadata(self, asset_type, asset_id, size):
        if not self.active: return
        filename = f"{asset_type}_{asset_id}.dat";
        filepath = os.path.join(self.storage_dir, filename)
        metadata = {"filename": filename, "filepath": filepath, "asset_type": asset_type, "size": size, "timestamp": datetime.now().isoformat()}
        with self.lock: self.downloaded_files.append(metadata); self.last_downloaded_files.append(filename)
        if self.verbose: logger.debug(f"Tracked asset: {filename} ({size/1024:.2f} KB)")

    def _simulate_asset_download(self, conn_info):
        # (Simulation logic remains the same as previous CLI version)
        if not self.active or self._stop_event.is_set() or not conn_info or not conn_info["socket"]:
            if conn_info: conn_info["status"] = "stopped" if self._stop_event.is_set() else "error"
            return False

        sock = conn_info["socket"]; conn_id = conn_info["id"]; conn_info["status"] = "running"
        try:
            asset_type = random.choice(list(DOWNLOAD_SIZES.keys())); asset_size = DOWNLOAD_SIZES[asset_type]
            asset_id = random.randint(1000, 9999); base_request = random.choice(CS_FILE_REQUESTS)
            custom_request = base_request + f" get_{asset_type}_{asset_id}.dat\x00".encode()

            sent_bytes = sock.sendto(custom_request, (self.server_ip, self.server_port))
            conn_info["bytes_sent"] += sent_bytes; conn_info["requests_sent"] += 1
            self._increment_counter("bytes_sent", sent_bytes); conn_info["last_request_time"] = time.time()

            received_total_for_asset = 0
            try:
                data, _ = sock.recvfrom(1024)
            except socket.timeout:
                pass
            except Exception as e:
                 pass

            remaining_size = asset_size
            while remaining_size > 0 and self.active and not self._stop_event.is_set():
                bytes_this_chunk = min(4096, remaining_size, random.randint(1024, 4096))
                conn_info["bytes_received"] += bytes_this_chunk
                self._increment_counter("bytes_received", bytes_this_chunk)
                received_total_for_asset += bytes_this_chunk; remaining_size -= bytes_this_chunk
                if self.download_delay > 0:
                     chunk_delay = self.download_delay / (asset_size / bytes_this_chunk) if asset_size > 0 else 0.001
                     time.sleep(max(0.001, chunk_delay))

                if random.random() < 0.05:
                     try: sock.sendto(b"\xff\xff\xff\xffping\x00", (self.server_ip, self.server_port))
                     except Exception: pass

            if remaining_size <= 0:
                with self.lock:
                    self.asset_downloads[asset_type] += 1
                    self.asset_bandwidth[asset_type] += received_total_for_asset
                conn_info["assets_downloaded"][asset_type] += 1
                conn_info["asset_bytes"][asset_type] += received_total_for_asset
                self._store_asset_metadata(asset_type, asset_id, received_total_for_asset)
            return True

        except socket.timeout:
            if self.verbose: logger.debug(f"Conn {conn_id}: Timeout sending request.")
            self._increment_counter("runtime_connection_issues"); conn_info["status"] = "timeout"; return False
        except OSError as e:
             logger.error(f"Conn {conn_id} OS Error: {e}. Closing socket.")
             try: sock.close()
             except Exception: pass
             conn_info["socket"] = None; conn_info["status"] = "error"; self._increment_counter("runtime_connection_issues"); return False
        except Exception as e:
            logger.error(f"Conn {conn_id} unexpected error during simulation: {type(e).__name__} - {str(e)}")
            conn_info["status"] = "error"; self._increment_counter("runtime_connection_issues"); return False

    def _connection_worker(self, conn_info):
        # (Worker logic remains the same as previous CLI version)
        conn_id = conn_info['id']
        if self.verbose: logger.debug(f"Worker {conn_id}: Started")
        self._increment_counter("active_workers_count")
        try:
            while self.active and not self._stop_event.is_set():
                if conn_info.get("socket") is None:
                    if self.verbose: logger.debug(f"Worker {conn_id}: Socket missing, attempting recreation.")
                    try:
                        new_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); new_sock.settimeout(2.0)
                        conn_info['socket'] = new_sock; conn_info['status'] = "running"
                        if self.verbose: logger.debug(f"Worker {conn_id}: Socket recreated.")
                    except Exception as e:
                        logger.error(f"Worker {conn_id}: FAILED recreate socket: {e}. Stopping worker.")
                        conn_info['status'] = "error"; self._increment_counter("runtime_connection_issues"); break

                success = self._simulate_asset_download(conn_info)
                worker_delay = random.uniform(0.01, 0.1)
                time.sleep(worker_delay)

        except Exception as e:
            logger.error(f"Worker {conn_id}: Unhandled loop error: {type(e).__name__} - {str(e)}")
            conn_info["status"] = "error"; self._increment_counter("runtime_connection_issues")
        finally:
            self._decrement_counter("active_workers_count")
            conn_info["status"] = "stopped"
            sock = conn_info.get("socket")
            if sock:
                try: sock.close()
                except Exception: pass
            if self.verbose: logger.debug(f"Worker {conn_id}: Finished. Sent: {conn_info['bytes_sent']/1024:.1f}KB, Recv (Sim): {conn_info['bytes_received']/1024:.1f}KB")

    def _update_server_info(self):
        # (Server info update logic remains the same as previous CLI version)
        if not self.server_query:
            logger.info("Server monitoring disabled.")
            return

        if self.verbose: logger.debug("Server monitor thread started.")
        while self.active and not self._stop_event.is_set():
            current_status = "UNKNOWN"; ping = -1; info_for_log = {}
            try:
                server_info = self.server_query.get_info() # get_info now returns None on failure
                timestamp = time.time()
                if server_info:
                    with self.lock:
                        self.server_info = server_info; self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': ping,
                                    'players': server_info.get('players', 0), 'max_players': server_info.get('max_players', 0),
                                    'name': server_info.get('name','N/A'), 'map': server_info.get('map', 'N/A')}
                else: # Query failed or parsing failed
                    with self.lock:
                        if self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT):
                            current_status = "OFFLINE"
                        else:
                            current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"
                        self.server_info = None # Clear stale info
                        self.server_status = current_status
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': -1,
                                    'players': -1, 'max_players': -1}

            except Exception as e: # Catch unexpected errors in this thread
                logger.error(f"Unexpected server info error: {type(e).__name__} - {str(e)}")
                with self.lock:
                    current_status = "ERROR"; self.server_info = None; self.server_status = current_status
                info_for_log = {'timestamp': time.time(), 'status': current_status, 'ping': -1}

            if info_for_log:
                with self.lock:
                    self.server_status_log.append(info_for_log)

            # Wait before next query, check stop event frequently
            sleep_interval = 0.1
            sleep_end = time.time() + self.server_info_interval
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval):
                      break # Exit inner loop if stop event is set
            if self._stop_event.is_set():
                 break # Exit outer loop if stop event is set

        if self.server_query: self.server_query.close()
        if self.verbose: logger.debug("Server monitor thread finished.")

    def _display_realtime_stats(self):
        """Clears terminal using ANSI codes and redraws stats in a fixed layout."""
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time

        # ANSI Codes
        CURSOR_TO_HOME = "\033[H"
        CLEAR_LINE = "\033[K" # Clears from cursor to end of line
        # CLEAR_ENTIRE_LINE = "\033[2K" # Clears the entire line cursor is on (not needed if using CLEAR_LINE correctly)
        CLEAR_SCREEN_FROM_CURSOR = "\033[J" # Clears from cursor to end of screen

        term_width = 80 # Assume a default terminal width
        try:
            term_width = os.get_terminal_size().columns
        except OSError:
            logger.warning("Could not detect terminal width, using default 80.")
            term_width = 80 # Ensure it's set

        while self.active and not self._stop_event.is_set():
            lines_to_print = [] # Build the output line by line
            try:
                with self.lock:
                    # Gather current stats under lock
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    bytes_sent = self.bytes_sent; bytes_received = self.bytes_received
                    active_workers = self.active_workers_count; runtime_issues = self.runtime_connection_issues
                    initial_fails = self.initial_connection_failures
                    asset_down_copy = self.asset_downloads.copy()
                    last_files = list(self.last_downloaded_files)
                    current_server_status = self.server_status
                    current_server_info = self.server_info.copy() if self.server_info else None
                    last_seen_time = self.server_last_seen

                # Calculate derived stats outside lock
                sent_mb = bytes_sent / (1024*1024); recv_mb = bytes_received / (1024*1024)
                total_mb = sent_mb + recv_mb
                avg_rate_mbs = total_mb / elapsed if elapsed > 0 else 0
                avg_send_mbs = sent_mb / elapsed if elapsed > 0 else 0
                avg_recv_mbs = recv_mb / elapsed if elapsed > 0 else 0

                # Log bandwidth point periodically
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                     with self.lock: self.bandwidth_log_points.append((elapsed, total_mb))
                     last_bw_log_time = current_time

                # --- Format Output Lines ---
                status = "Running" if self.active else "Stopped"
                mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                header = f"--- CS 1.6 Bandwidth Test: {self.server_ip}:{self.server_port} ---".center(term_width)
                lines_to_print.append(header)

                line2_left = f" Status: {status} | Mode: {mode}"
                line2_right = f"Time: {elapsed:.1f}s"
                # Ensure right part doesn't overflow if left part is long
                lines_to_print.append(f"{line2_left:<{max(0, term_width - len(line2_right))}}{line2_right}")

                line3_left = f" Workers: {active_workers}/{self.num_connections}"
                line3_right = f"Issues: Init={initial_fails} Run={runtime_issues}"
                lines_to_print.append(f"{line3_left:<{max(0, term_width - len(line3_right))}}{line3_right}")

                lines_to_print.append("-" * term_width) # Use hyphen for separator
                lines_to_print.append("[Server Status]".center(term_width))

                if self.no_server_monitor:
                     lines_to_print.append(" Monitoring Disabled".ljust(term_width))
                     lines_to_print.append(" ".ljust(term_width)) # Empty line for spacing
                     lines_to_print.append(" ".ljust(term_width)) # Empty line for spacing
                     lines_to_print.append(" ".ljust(term_width)) # Empty line for spacing
                else:
                    s_status_str = f" Status: {current_server_status}"
                    s_ping_str = "Ping: N/A"
                    s_players_str = "Players: N/A"
                    if current_server_info:
                        ping_val = current_server_info.get('ping', -1)
                        s_ping_str = f"Ping: {ping_val:>3}ms" if ping_val >= 0 else "Ping: N/A"
                        s_players_str = f"Players: {current_server_info.get('players','?')}/{current_server_info.get('max_players','?')}"
                        if current_server_info.get('bots',0) > 0:
                           s_players_str += f" (B:{current_server_info['bots']})" # Abbrev

                    elif current_server_status == "OFFLINE":
                         s_status_str += f" (No response >{SERVER_OFFLINE_TIMEOUT}s)"
                    elif current_server_status == "ISSUES":
                         s_status_str += " (Query Failed/Timeout)"
                    elif current_server_status == "ERROR":
                         s_status_str += " (Monitor Error!)"
                    elif current_server_status == "UNKNOWN":
                         s_status_str += " (Querying...)"

                    # Arrange Server Status line
                    # Calculate widths dynamically, ensure positive padding
                    width_status = len(s_status_str)
                    width_ping = len(s_ping_str)
                    width_players = len(s_players_str)
                    spaces1 = max(1, (term_width - width_status - width_ping - width_players) // 2)
                    spaces2 = max(1, term_width - width_status - width_ping - width_players - spaces1)
                    lines_to_print.append(f"{s_status_str}{' '*spaces1}{s_ping_str}{' '*spaces2}{s_players_str}".ljust(term_width))


                    s_name_str = "Name: N/A"
                    s_map_str = "Map: N/A"
                    if current_server_info:
                         # Truncate name/map based on available space
                         max_len = term_width - len("Name: ") - 2 # Allow padding
                         s_name_str = f"Name: {current_server_info.get('name', 'N/A')[:max_len]}"
                         max_len = term_width - len("Map: ") - 2
                         s_map_str = f"Map: {current_server_info.get('map', 'N/A')[:max_len]}"

                    lines_to_print.append(s_name_str.ljust(term_width))
                    lines_to_print.append(s_map_str.ljust(term_width))


                    last_seen_str = "Last Seen: Never"
                    if last_seen_time > 0:
                         last_seen_str = f"Last Seen: {datetime.fromtimestamp(last_seen_time).strftime('%H:%M:%S')}"
                    lines_to_print.append(last_seen_str.ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Bandwidth Usage]".center(term_width))
                # Format bandwidth lines carefully for alignment
                bw_line1 = f" Total Sent: {sent_mb:>8.2f} MB   |   Recv (Sim): {recv_mb:>8.2f} MB"
                lines_to_print.append(bw_line1.ljust(term_width))
                bw_line2 = f" Total Data: {total_mb:>8.2f} MB   |   Avg Rate:   {avg_rate_mbs:>8.2f} MB/s"
                lines_to_print.append(bw_line2.ljust(term_width))
                bw_line3 = f" Avg Rates:  Send:{avg_send_mbs:>7.2f} MB/s   |   Recv:{avg_recv_mbs:>7.2f} MB/s" # Adjusted spacing
                lines_to_print.append(bw_line3.ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Simulated Assets]".center(term_width))
                total_assets = sum(asset_down_copy.values())
                asset_counts_str = ", ".join([f"{k[:3]}:{v}" for k, v in sorted(asset_down_copy.items()) if v > 0]) # Abbrev, Sort
                lines_to_print.append(f" Tracked: {total_assets} | Counts: {asset_counts_str if asset_counts_str else 'None'}".ljust(term_width))
                lines_to_print.append(f" Last {LAST_FILES_DISPLAY_COUNT} Files:".ljust(term_width))
                if last_files:
                    for i, fname in enumerate(last_files):
                        max_fname_len = term_width - 4 # Room for "  - "
                        lines_to_print.append(f"  - {fname[:max_fname_len]}".ljust(term_width))
                    # Add blank lines if fewer than max files displayed, for consistent height
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_files))):
                        lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No files tracked yet)".ljust(term_width))
                    # Add blank lines
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT -1)):
                       lines_to_print.append(" ".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("(Press Ctrl+C to stop)".center(term_width))

                # --- Perform the Screen Update ---
                output_buffer = CURSOR_TO_HOME # Move cursor to top-left
                for line in lines_to_print:
                    # Write line, clear rest of it, add newline
                    # Ensure line doesn't exceed term_width before adding CLEAR_LINE
                    output_buffer += line[:term_width] + CLEAR_LINE + "\n"

                output_buffer += CLEAR_SCREEN_FROM_CURSOR # Clear anything below the last printed line

                # Write buffer to stdout
                sys.stdout.write(output_buffer)
                sys.stdout.flush()

            except Exception as e:
                # Log errors but try to continue display loop
                logger.error(f"Error in display thread: {type(e).__name__} - {str(e)}", exc_info=False)
                time.sleep(1) # Pause briefly after error

            # Wait before next update, check stop event frequently
            sleep_interval = 0.1
            sleep_end = time.time() + UI_UPDATE_INTERVAL
            while time.time() < sleep_end:
                 if self._stop_event.wait(timeout=sleep_interval):
                      break # Exit inner loop if stop event is set
            if self._stop_event.is_set():
                 break # Exit outer loop if stop event is set


        if self.verbose: logger.debug("Realtime display thread finished.")
        # Clear screen one last time before final report prints normally
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
        sys.stdout.flush()

    def start_test(self):
        # (Start logic remains the same as previous CLI version)
        if self.active:
            logger.warning("Test is already running.")
            return

        logger.info("="*30 + " Starting Test " + "="*30)
        self.active = True
        self._stop_event.clear()
        self.start_time = time.time()
        self.end_time = 0

        self.bytes_sent = 0; self.bytes_received = 0; self.bandwidth_log_points = []
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0; self.server_status_log = []
        self.asset_downloads = {k: 0 for k in DOWNLOAD_SIZES}; self.asset_bandwidth = {k: 0 for k in DOWNLOAD_SIZES}
        self.downloaded_files = []; self.last_downloaded_files.clear()
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0; self.server_info = None

        self.connections = []; self.threads = []

        if not self.no_server_monitor and self.server_query:
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start()
            self.threads.append(self.server_info_thread)

        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread)

        logger.info(f"Attempting to establish {self.num_connections} worker connections...")
        initial_success = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set(): break
            conn_info = self._create_connection(i + 1)
            if conn_info:
                worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
                self.connections.append(conn_info)
                worker_thread.start()
                self.threads.append(worker_thread)
                initial_success += 1
            else:
                self._increment_counter("initial_connection_failures")
            if self.num_connections > 50 and (i + 1) % 50 == 0: time.sleep(0.05)

        logger.info(f"Successfully started {initial_success} workers initially. {self.initial_connection_failures} failed.")

        if initial_success == 0 and self.num_connections > 0:
            logger.error("FATAL: No worker connections could be started. Stopping test.")
            self.stop_test()
            return

        try:
            if self.continuous_mode:
                self._stop_event.wait()
                logger.info("Stop event received, finishing...")
            else:
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early:
                    logger.info("Test stopped early via signal.")
                else:
                    logger.info("Test duration reached.")
                    self.stop_test() # Stop naturally after duration

        except Exception as e:
             logger.error(f"Error in main test execution: {e}")
             self.stop_test()

    def stop_test(self):
        # (Stop logic remains the same as previous CLI version)
        if not self.active:
            return

        logger.info("Stopping test...")
        self.active = False # Set inactive flag first
        self._stop_event.set() # Signal threads using the event
        self.end_time = time.time() if self.start_time > 0 else time.time()

        logger.info("Waiting for threads to complete...")
        join_timeout = 3.0

        threads_to_join = self.threads[:]
        for thread in threads_to_join:
            # Don't try to join the current thread if stop_test is called from within one of the threads (unlikely here)
            if thread is threading.current_thread(): continue

            if thread.is_alive():
                try:
                    if self.verbose: logger.debug(f"Joining thread: {thread.name}...")
                    thread.join(join_timeout)
                    if thread.is_alive():
                        logger.warning(f"Thread {thread.name} did not stop within timeout.")
                except Exception as e:
                    logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("All threads processed.")

        if self.server_query:
            self.server_query.close()

        # Final report generation now happens after clearing the screen in _display_realtime_stats finish
        # print(CLEAR_SCREEN) # No longer needed here
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed)

        logger.info("Test finished.")

    def _generate_final_report(self, duration):
        # (Final report generation remains the same as previous CLI version)
        print("\n" + "="*30 + " Test Results Summary " + "="*30) # Add newline before report
        duration = max(duration, 0.01)

        with self.lock:
            bytes_sent = self.bytes_sent; bytes_received = self.bytes_received
            asset_downloads = self.asset_downloads.copy(); asset_bandwidth = self.asset_bandwidth.copy()
            downloaded_files_count = len(self.downloaded_files)
            runtime_issues = self.runtime_connection_issues; initial_fails = self.initial_connection_failures
            final_server_status = self.server_status
            final_server_info = self.server_info.copy() if self.server_info else None
            server_log = self.server_status_log[:]

        sent_mb = bytes_sent / (1024*1024); received_mb = bytes_received / (1024*1024); total_mb = sent_mb + received_mb
        avg_rate_mbs = total_mb / duration; avg_send_mbs = sent_mb / duration; avg_recv_mbs = received_mb / duration
        total_assets = sum(asset_downloads.values()); total_asset_mb = sum(asset_bandwidth.values()) / (1024*1024)

        server_name = "N/A"; server_map = "N/A"; avg_ping = -1; min_ping = -1; max_ping = -1
        if not self.no_server_monitor:
            last_valid_log = next((log for log in reversed(server_log) if log.get('status') in ['ONLINE', 'ISSUES'] and log.get('name') not in [None,'N/A','']), None)
            if last_valid_log:
                server_name = last_valid_log.get('name', 'N/A')
                server_map = last_valid_log.get('map', 'N/A')
            elif final_server_info:
                 server_name = final_server_info.get('name', 'N/A')
                 server_map = final_server_info.get('map', 'N/A')

            pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
            if pings:
                avg_ping = sum(pings)/len(pings); min_ping = min(pings); max_ping = max(pings)

        print(f"[Test Overview]")
        print(f" Target:          {self.server_ip}:{self.server_port}")
        print(f" Duration:        {duration:.2f}s")
        print(f" Mode:            {'Continuous (Stopped)' if self.continuous_mode else 'Timed'}")
        print(f" Connections:     {self.num_connections} (Target)")
        print(f" Initial Fails:   {initial_fails}")
        print(f" Runtime Issues:  {runtime_issues}")
        print("\n[Server Status]")
        if self.no_server_monitor:
            print(" Monitoring:      Disabled")
        else:
            print(f" Final Status:    {final_server_status}")
            print(f" Last Name:       {server_name}")
            print(f" Last Map:        {server_map}")
            print(f" Avg Ping:        {avg_ping:.1f} ms" if avg_ping != -1 else "N/A")
            print(f" Ping Min/Max:    {min_ping} / {max_ping} ms" if min_ping != -1 else "N/A")
        print("\n[Bandwidth Usage]")
        print(f" Total Sent:      {sent_mb:.2f} MB")
        print(f" Total Recv(Sim): {received_mb:.2f} MB")
        print(f" Total Data:      {total_mb:.2f} MB")
        print(f" Avg Send Rate:   {avg_send_mbs:.2f} MB/s")
        print(f" Avg Recv Rate:   {avg_recv_mbs:.2f} MB/s")
        print(f" Avg Total Rate:  {avg_rate_mbs:.2f} MB/s")
        print("\n[Simulated Asset Downloads]")
        print(f" Total Files:     {total_assets} ({total_asset_mb:.2f} MB Simulated)")
        print(f" Metadata Recs:   {downloaded_files_count}")
        if total_assets > 0:
            print(" Type        Count     Sim MB   Avg MB")
            print(" ---------- ------ ---------- ----------")
            for asset_type, count in sorted(asset_downloads.items()):
                 if count > 0:
                     size_mb = asset_bandwidth.get(asset_type, 0) / (1024*1024)
                     avg_size = size_mb / count if count > 0 else 0
                     print(f" {asset_type.capitalize():<10} {count: >6} {size_mb: >10.2f} {avg_size: >10.2f}")
        else:
            print(" (No assets tracked)")

        print("="*60)

    def _save_detailed_report_json(self, duration, initial_fails=None, runtime_issues=None):
         # (JSON saving logic remains the same as previous CLI version)
         with self.lock:
            duration = max(0.01, duration)
            sent_mb = self.bytes_sent / (1024*1024)
            received_mb = self.bytes_received / (1024*1024)
            total_mb = sent_mb + received_mb
            avg_rate_mbs = total_mb / duration
            asset_downloads = self.asset_downloads.copy()
            asset_bandwidth = self.asset_bandwidth.copy()
            downloaded_files_metadata = list(self.downloaded_files)
            server_log = self.server_status_log[:]
            initial_fails = self.initial_connection_failures if initial_fails is None else initial_fails
            runtime_issues = self.runtime_connection_issues if runtime_issues is None else runtime_issues

         report_data = {
            "test_info": {
                "target_server": f"{self.server_ip}:{self.server_port}",
                "timestamp_utc": datetime.utcnow().isoformat() + "Z",
                "duration_seconds": round(duration, 2),
                "configured_connections": self.num_connections,
                "initial_connection_failures": initial_fails,
                "runtime_connection_issues": runtime_issues,
                "download_delay_config_s": self.download_delay,
                "mode": "Continuous" if self.continuous_mode else "Timed",
                "server_monitoring": not self.no_server_monitor,
                "verbose_logging": self.verbose,
            },
            "bandwidth_summary": {
                "sent_mb": round(sent_mb, 3),
                "received_simulated_mb": round(received_mb, 3),
                "total_simulated_mb": round(total_mb, 3),
                "avg_total_simulated_rate_mbs": round(avg_rate_mbs, 3),
                "start_time_unix": self.start_time,
                "end_time_unix": self.end_time,
                "bandwidth_log_points_sec_mb": [(round(t, 2), round(mb, 3)) for t, mb in self.bandwidth_log_points],
            },
            "simulated_assets": {
                "total_files_tracked": sum(asset_downloads.values()),
                "total_simulated_mb": round(sum(asset_bandwidth.values()) / (1024*1024), 3),
                "count_by_type": asset_downloads,
                "simulated_mb_by_type": {k: round(v / (1024*1024), 3) for k, v in asset_bandwidth.items()},
                "tracked_file_metadata_count": len(downloaded_files_metadata),
                "tracked_files_metadata": downloaded_files_metadata
            },
            "server_status_log": server_log
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
# Signal Handling for Ctrl+C
# ==============================================================
def signal_handler(sig, frame):
    # Ensure this handler is robust
    global tester_instance
    if tester_instance and tester_instance.active:
        if not tester_instance._stop_event.is_set(): # Prevent multiple stop calls from signals
            print('\n') # Move cursor to newline after Ctrl+C appears
            logger.warning("Ctrl+C received! Initiating graceful shutdown...")
            # Signal the running test to stop; use a thread if stop_test might block
            # Making stop_test itself non-blocking is preferred
            threading.Thread(target=tester_instance.stop_test, daemon=True).start()
        # else: logger.debug("Shutdown already in progress.") # Optional debug msg
    else:
        print('\nCtrl+C received, but no active test found or test already stopping. Exiting.')
        sys.exit(0) # Exit immediately if no active test

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 Server Bandwidth Testing Tool (CLI Version)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 server.")
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="Server port.")
    parser.add_argument("-c", "--connections", type=int, default=50, help="Number of concurrent connections/workers.")
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of timed test in seconds.")
    parser.add_argument("-dl", "--delay", type=float, default=0.01, help="Simulated delay factor per asset chunk (lower is faster).")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging.")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run continuously until stopped (Ctrl+C).")
    parser.add_argument("--no-server-monitor", action="store_true", help="Disable querying server status.")
    parser.add_argument("--storage-dir", default="cs_test_reports", help="Directory for JSON report files.")
    args = parser.parse_args()

    if args.verbose:
        logger.setLevel(logging.DEBUG)
        # Also configure root logger if other libs use logging
        # logging.getLogger().setLevel(logging.DEBUG)
        logger.info("Verbose logging enabled.")
    else:
        logger.setLevel(logging.INFO)

    logger.warning("="*70)
    logger.warning("⚠️ IMPORTANT RESPONSIBILITY NOTICE ⚠️")
    logger.warning("You are SOLELY responsible for the use of this tool.")
    logger.warning("Obtain EXPLICIT PERMISSION before testing any server you DO NOT own.")
    logger.warning("Misuse can negatively impact server performance, network infrastructure,")
    logger.warning("and is unethical and potentially illegal. Use responsibly.")
    logger.warning("="*70)
    time.sleep(1.5) # Slightly shorter pause

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
            no_server_monitor=args.no_server_monitor
        )

        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler) # Handle termination signal too

        tester_instance.start_test()

        # --- Wait for test completion (handled by start_test/stop_test) ---
        # If start_test finishes (e.g., timed mode ends), the script can exit.
        # In continuous mode, start_test waits on _stop_event, which is set by signal_handler.
        # We might need a final wait here if stop_test runs in a thread?
        # Let's assume stop_test blocks until threads are joined for now.
        # If stop_test is threaded in signal handler, we might need:
        # while tester_instance.active:
        #     time.sleep(0.5)

        logger.info("Main thread exiting.")
        sys.exit(0)

    except Exception as e:
        logger.error(f"An critical error occurred in the main script: {type(e).__name__} - {str(e)}", exc_info=True) # Show traceback for critical errors
        sys.exit(1)
