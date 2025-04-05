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

# --- ANSI escape code for clearing screen ---
CLEAR_SCREEN = "\033[H\033[J"

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
# ServerQuery Class (Unchanged from original, uses global logger)
# ==============================================================
class ServerQuery:
    def __init__(self, server_ip, server_port=DEFAULT_PORT):
        self.server_ip = server_ip; self.server_port = server_port
        self.last_info = None; self.last_ping = 0; self.sock = None
        self.retry_count = 2; self.timeout = 1.5
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
        start_time = time.time(); request = b"\xFF\xFF\xFF\xFFTSource Engine Query\x00"
        for attempt in range(self.retry_count):
            try:
                self.sock.sendto(request, (self.server_ip, self.server_port)); response, _ = self.sock.recvfrom(4096)
                end_time = time.time(); self.last_ping = int((end_time - start_time) * 1000)
                if response:
                    parsed_info = self._parse_info(response)
                    if parsed_info: self.last_info = parsed_info; return parsed_info
                    else: raise ValueError("Invalid server response format")
            except socket.timeout:
                if attempt == self.retry_count - 1: logger.debug("Server query timed out after retries"); return None # Don't raise, just return None
                time.sleep(0.1)
            except (OSError, ValueError) as e: logger.warning(f"Query Error: {type(e).__name__} - {str(e)}"); self.close(); return None # Don't raise
            except Exception as e: logger.error(f"Unexpected Query Error: {type(e).__name__} - {str(e)}"); self.close(); return None # Don't raise
        return None # Explicitly return None if all retries fail
    def _parse_info(self, response):
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF': return None
            response_type = response[4:5]; offset = 5
            if response_type not in [b'I', b'm']: return None # Original GoldSrc 'm' response or Source 'I' info response
            # Protocol might be needed for some games, skip for CS 1.6 basic info
            # protocol = response[offset]; offset += 1
            server_name_end = response.find(b'\x00', offset);
            if server_name_end == -1: return None
            server_name = response[offset:server_name_end].decode('utf-8', errors='ignore'); offset = server_name_end + 1
            map_name_end = response.find(b'\x00', offset);
            if map_name_end == -1: return None
            map_name = response[offset:map_name_end].decode('utf-8', errors='ignore'); offset = map_name_end + 1
            game_dir_end = response.find(b'\x00', offset);
            if game_dir_end == -1: return None
            game_dir = response[offset:game_dir_end].decode('utf-8', errors='ignore'); offset = game_dir_end + 1
            game_desc_end = response.find(b'\x00', offset);
            if game_desc_end == -1: return None
            game_desc = response[offset:game_desc_end].decode('utf-8', errors='ignore'); offset = game_desc_end + 1

            # --- Parsing player count etc. is slightly different for 'm' vs 'I' ---
            # This part might need adjustment based on exact server response type if using 'I' (TSource Engine Query)
            # Assuming GoldSrc ('m' or similar structure after initial fields) for simplicity
            # Need to check length before accessing bytes
            player_count = max_players = bot_count = 0 # Defaults
            if offset < len(response): player_count = response[offset]
            if offset + 1 < len(response): max_players = response[offset+1]
            # Bots might not be present in all responses, handle potential IndexError
            # if offset + 2 < len(response): bot_count = response[offset+2] # Assuming bots are here for CS 1.6

            return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc, 'players': player_count, 'max_players': max_players, 'bots': bot_count, 'ping': self.last_ping}
        except IndexError: logger.warning("Index error parsing server info, response might be incomplete."); return None
        except Exception as e: logger.error(f"Error parsing server info: {type(e).__name__} - {str(e)}"); return None
    def close(self):
        if self.sock:
            try: self.sock.close()
            except Exception: pass
            self.sock = None

# ==============================================================
# CS16BandwidthTester Class (CLI Version)
# ==============================================================
class CS16BandwidthTester:
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 download_delay, verbose, storage_dir, continuous_mode, no_server_monitor):

        self.server_ip = server_ip; self.server_port = server_port
        self.num_connections = num_connections; self.test_duration = test_duration
        self.download_delay = max(0, download_delay); self.verbose = verbose
        self.continuous_mode = continuous_mode; self.storage_dir = storage_dir
        self.no_server_monitor = no_server_monitor

        # Ensure storage directory exists
        if not os.path.exists(self.storage_dir):
            try:
                os.makedirs(self.storage_dir)
                logger.info(f"Created storage directory: {self.storage_dir}")
            except OSError as e:
                logger.error(f"Failed to create storage directory '{self.storage_dir}': {e}")
                # Handle error appropriately, maybe exit or use current dir
                self.storage_dir = "." # Fallback to current directory

        self.active = False; self.connections = []; self.threads = []
        self.lock = threading.Lock()
        self._stop_event = threading.Event() # For graceful shutdown

        # Stats Tracking
        self.bytes_sent = 0; self.bytes_received = 0
        self.start_time = 0; self.end_time = 0
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0

        # Server monitoring
        self.server_query = ServerQuery(server_ip, server_port) if not self.no_server_monitor else None
        self.server_info = None; self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0
        self.server_info_thread = None; self.server_info_interval = 3 # How often to query server
        self.server_status_log = [] # Still useful for final report

        # Asset & Bandwidth Tracking
        self.asset_downloads = {k: 0 for k in DOWNLOAD_SIZES}; self.asset_bandwidth = {k: 0 for k in DOWNLOAD_SIZES}
        self.downloaded_files = []; self.last_downloaded_files = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        self.bandwidth_log_points = [] # Store (timestamp, total_mb) tuples for rate calculation

        # Display thread
        self.display_thread = None

    # --- Helper methods ---
    def _increment_counter(self, counter_name, value=1):
        with self.lock: setattr(self, counter_name, getattr(self, counter_name) + value)
    def _decrement_counter(self, counter_name, value=1): self._increment_counter(counter_name, -value)

    def _create_connection(self, conn_id):
        sock = None
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); sock.settimeout(2.0) # Slightly longer timeout?
        except Exception as e: logger.error(f"Conn {conn_id}: Socket create error: {e}"); return None
        return {"id": conn_id, "socket": sock, "bytes_sent": 0, "bytes_received": 0, "last_request_time": 0, "requests_sent": 0, "assets_downloaded": {k: 0 for k in DOWNLOAD_SIZES}, "asset_bytes": {k: 0 for k in DOWNLOAD_SIZES}, "status": "running"}

    def _store_asset_metadata(self, asset_type, asset_id, size):
        if not self.active: return
        filename = f"{asset_type}_{asset_id}.dat";
        # Use os.path.join for cross-platform compatibility
        filepath = os.path.join(self.storage_dir, filename)
        metadata = {"filename": filename, "filepath": filepath, "asset_type": asset_type, "size": size, "timestamp": datetime.now().isoformat()}
        with self.lock: self.downloaded_files.append(metadata); self.last_downloaded_files.append(filename)
        if self.verbose: logger.debug(f"Tracked asset: {filename} ({size/1024:.2f} KB)")

    # --- Main worker logic ---
    def _simulate_asset_download(self, conn_info):
        if not self.active or self._stop_event.is_set() or not conn_info or not conn_info["socket"]:
            if conn_info: conn_info["status"] = "stopped" if self._stop_event.is_set() else "error"
            return False

        sock = conn_info["socket"]; conn_id = conn_info["id"]; conn_info["status"] = "running"
        try:
            asset_type = random.choice(list(DOWNLOAD_SIZES.keys())); asset_size = DOWNLOAD_SIZES[asset_type]
            asset_id = random.randint(1000, 9999); base_request = random.choice(CS_FILE_REQUESTS)
            # Simulate a file request (server won't actually send the file)
            custom_request = base_request + f" get_{asset_type}_{asset_id}.dat\x00".encode()

            sent_bytes = sock.sendto(custom_request, (self.server_ip, self.server_port))
            conn_info["bytes_sent"] += sent_bytes; conn_info["requests_sent"] += 1
            self._increment_counter("bytes_sent", sent_bytes); conn_info["last_request_time"] = time.time()

            # Simulate receiving data based on expected size - Server likely sends small error/ack
            # We simulate receiving the *expected* size to test bandwidth handling
            received_total_for_asset = 0
            # Maybe receive a small initial packet? Optional.
            try:
                data, _ = sock.recvfrom(1024) # Expect small response/error
                recv_bytes_actual = len(data)
                # Log actual received, but increment counters based on *simulated* size below
                # conn_info["bytes_received"] += recv_bytes_actual
                # self._increment_counter("bytes_received", recv_bytes_actual)
            except socket.timeout:
                pass # Expected if server doesn't respond to fake file req
            except Exception as e:
                 # Ignore most errors here as the request is fake anyway
                 # logger.warning(f"Conn {conn_id}: Initial recv error (ignored): {e}")
                 pass

            # Simulate the time and counter increments for the full download
            # Use the asset_size for counter increments
            remaining_size = asset_size
            while remaining_size > 0 and self.active and not self._stop_event.is_set():
                # Simulate receiving chunks
                bytes_this_chunk = min(4096, remaining_size, random.randint(1024, 4096))
                conn_info["bytes_received"] += bytes_this_chunk # Increment based on simulation
                self._increment_counter("bytes_received", bytes_this_chunk)
                received_total_for_asset += bytes_this_chunk; remaining_size -= bytes_this_chunk
                # Simulate network delay + processing time
                if self.download_delay > 0:
                     chunk_delay = self.download_delay / (asset_size / bytes_this_chunk) if asset_size > 0 else 0.001
                     time.sleep(max(0.001, chunk_delay)) # Sleep proportional to chunk size

                # Occasionally send a real ping to keep connection somewhat active if needed
                if random.random() < 0.05:
                     try: sock.sendto(b"\xff\xff\xff\xffping\x00", (self.server_ip, self.server_port))
                     except Exception: pass # Ignore errors sending intermittent ping

            if remaining_size <= 0: # If simulation completed
                with self.lock:
                    self.asset_downloads[asset_type] += 1
                    self.asset_bandwidth[asset_type] += received_total_for_asset # Use simulated received amount
                conn_info["assets_downloaded"][asset_type] += 1
                conn_info["asset_bytes"][asset_type] += received_total_for_asset
                self._store_asset_metadata(asset_type, asset_id, received_total_for_asset) # Store simulated size
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
                        conn_info['status'] = "error"; self._increment_counter("runtime_connection_issues"); break # Stop this worker

                # Perform the simulated download
                success = self._simulate_asset_download(conn_info)

                # Add a small random delay between operations for this worker
                worker_delay = random.uniform(0.01, 0.1) # Add base delay regardless of download_delay
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

    # --- Server monitoring logic ---
    def _update_server_info(self):
        if not self.server_query:
            logger.info("Server monitoring disabled.")
            return # Exit if monitoring is off

        if self.verbose: logger.debug("Server monitor thread started.")
        while self.active and not self._stop_event.is_set():
            current_status = "UNKNOWN"; ping = -1; info_for_log = {}
            try:
                server_info = self.server_query.get_info()
                timestamp = time.time() # Get timestamp regardless of success
                if server_info:
                    with self.lock: # Protect access to shared server state
                        self.server_info = server_info; self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                    # Prepare log entry outside lock
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': ping,
                                    'players': server_info.get('players', 0), 'max_players': server_info.get('max_players', 0),
                                    'name': server_info.get('name','N/A'), 'map': server_info.get('map', 'N/A')}
                else: # Query failed (timeout or error handled in get_info)
                    with self.lock:
                        # Determine status based on last successful contact
                        if self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT):
                            current_status = "OFFLINE"
                        else:
                            # If never seen or recent failure, mark as issues
                            current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"
                        self.server_info = None # Clear stale info
                        self.server_status = current_status
                    # Prepare log entry outside lock
                    info_for_log = {'timestamp': timestamp, 'status': current_status, 'ping': -1,
                                    'players': -1, 'max_players': -1}

            except Exception as e: # Catch unexpected errors in this thread
                logger.error(f"Unexpected server info error: {type(e).__name__} - {str(e)}")
                with self.lock:
                    current_status = "ERROR"; self.server_info = None; self.server_status = current_status
                info_for_log = {'timestamp': time.time(), 'status': current_status, 'ping': -1}

            # Append to log (do this outside lock if timestamp comes from info_for_log)
            if info_for_log:
                with self.lock: # Lock needed only to append to the shared list
                    self.server_status_log.append(info_for_log)

            # Wait before next query
            time.sleep(self.server_info_interval)

        if self.server_query: self.server_query.close()
        if self.verbose: logger.debug("Server monitor thread finished.")

    # --- Real-time display logic ---
    def _display_realtime_stats(self):
        """Clears terminal and prints current stats."""
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time
        last_total_mb = 0

        while self.active and not self._stop_event.is_set():
            try:
                with self.lock:
                    # Gather current stats under lock
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    bytes_sent = self.bytes_sent; bytes_received = self.bytes_received
                    active_workers = self.active_workers_count; runtime_issues = self.runtime_connection_issues
                    initial_fails = self.initial_connection_failures
                    asset_down_copy = self.asset_downloads.copy()
                    last_files = list(self.last_downloaded_files)
                    # Server info needs safe access too
                    current_server_status = self.server_status
                    current_server_info = self.server_info.copy() if self.server_info else None
                    last_seen_time = self.server_last_seen

                # Calculate derived stats outside lock
                sent_mb = bytes_sent / (1024*1024); recv_mb = bytes_received / (1024*1024)
                total_mb = sent_mb + recv_mb
                avg_rate_mbs = total_mb / elapsed if elapsed > 0 else 0
                avg_send_mbs = sent_mb / elapsed if elapsed > 0 else 0
                avg_recv_mbs = recv_mb / elapsed if elapsed > 0 else 0

                # Log bandwidth point periodically for final report rate calculation
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0): # Log approx every second
                     with self.lock: # Lock only for appending
                         self.bandwidth_log_points.append((elapsed, total_mb))
                     last_bw_log_time = current_time

                # --- Format Output String ---
                display_str = CLEAR_SCREEN # Start with clear screen command
                display_str += f"--- CS 1.6 Bandwidth Test: {self.server_ip}:{self.server_port} ---\n"
                mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                status = "Running" if self.active else "Stopped"
                display_str += f"Status: {status} | Mode: {mode}\n"
                display_str += f"Time Elapsed: {elapsed:.1f}s\n"
                display_str += "="*40 + "\n"

                # Server Status Section
                display_str += "[Server Status]\n"
                if self.no_server_monitor:
                     display_str += " Monitoring Disabled\n"
                elif current_server_status == "ONLINE":
                     si = current_server_info
                     ping_str = f"{si['ping']}ms" if si and si.get('ping', -1) >= 0 else "N/A"
                     players_str = f"{si.get('players','?')}/{si.get('max_players','?')}" if si else "?/?"
                     map_str = si.get('map', 'N/A') if si else 'N/A'
                     name_str = si.get('name', 'N/A')[:30] + ('...' if si and len(si.get('name','')) > 30 else '') if si else 'N/A' # Truncate name
                     display_str += f" Status: ONLINE | Ping: {ping_str} | Players: {players_str}\n"
                     display_str += f" Name: {name_str} | Map: {map_str}\n"
                elif current_server_status == "OFFLINE":
                     display_str += f" Status: OFFLINE (No response > {SERVER_OFFLINE_TIMEOUT}s)\n"
                elif current_server_status == "ISSUES":
                     ping_str = f"{current_server_info['ping']}ms" if current_server_info and current_server_info.get('ping',-1) >= 0 else "N/A"
                     display_str += f" Status: ISSUES | Last Ping: {ping_str} (Check logs for errors)\n"
                elif current_server_status == "ERROR":
                     display_str += f" Status: ERROR (Monitor thread failed, check logs)\n"
                else: # UNKNOWN
                     display_str += " Status: Initializing / Querying...\n"
                if not self.no_server_monitor and last_seen_time > 0:
                     last_seen_str = datetime.fromtimestamp(last_seen_time).strftime('%H:%M:%S')
                     display_str += f" Last Seen: {last_seen_str}\n"
                display_str += "="*40 + "\n"

                # Bandwidth Section
                display_str += "[Bandwidth]\n"
                display_str += f" Total Sent: {sent_mb: >8.2f} MB | Recv (Sim): {recv_mb: >8.2f} MB\n"
                display_str += f" Total Data: {total_mb: >8.2f} MB\n"
                display_str += f" Avg Rate:   {avg_rate_mbs: >8.2f} MB/s (Total)\n"
                display_str += f"             {avg_send_mbs: >8.2f} MB/s (Send) | {avg_recv_mbs: >8.2f} MB/s (Recv)\n"
                display_str += "="*40 + "\n"

                # Connections Section
                display_str += "[Connections]\n"
                display_str += f" Workers Active: {active_workers: >4} / {self.num_connections}\n"
                display_str += f" Initial Fails:  {initial_fails: >4}\n"
                display_str += f" Runtime Issues: {runtime_issues: >4}\n"
                display_str += "="*40 + "\n"

                # Assets Section
                display_str += "[Simulated Assets]\n"
                total_assets = sum(asset_down_copy.values())
                display_str += f" Total Tracked: {total_assets}\n"
                # Simple list of counts
                asset_counts_str = ", ".join([f"{k.capitalize()}: {v}" for k, v in asset_down_copy.items() if v > 0])
                display_str += f" Counts: {asset_counts_str if asset_counts_str else 'None'}\n"
                display_str += f" Last {LAST_FILES_DISPLAY_COUNT} Files:\n"
                if last_files:
                    for fname in last_files:
                        display_str += f"  - {fname}\n"
                else:
                    display_str += "  (No files tracked yet)\n"
                display_str += "="*40 + "\n"
                display_str += "(Press Ctrl+C to stop)"

                # Print to stdout
                print(display_str, flush=True)

            except Exception as e:
                # Log errors in the display thread itself
                logger.error(f"Error in display thread: {type(e).__name__} - {str(e)}")
                # Avoid crashing the display loop if possible
                time.sleep(1) # Pause briefly after error

            # Wait before next update
            time.sleep(UI_UPDATE_INTERVAL)

        if self.verbose: logger.debug("Realtime display thread finished.")


    # --- Test start/stop ---
    def start_test(self):
        if self.active:
            logger.warning("Test is already running.")
            return

        logger.info("="*30 + " Starting Test " + "="*30)
        self.active = True
        self._stop_event.clear() # Ensure stop event is not set
        self.start_time = time.time()
        self.end_time = 0

        # Reset stats (redundant with __init__ but safe)
        self.bytes_sent = 0; self.bytes_received = 0; self.bandwidth_log_points = []
        self.initial_connection_failures = 0; self.runtime_connection_issues = 0
        self.active_workers_count = 0; self.server_status_log = []
        self.asset_downloads = {k: 0 for k in DOWNLOAD_SIZES}; self.asset_bandwidth = {k: 0 for k in DOWNLOAD_SIZES}
        self.downloaded_files = []; self.last_downloaded_files.clear()
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN";
        self.server_last_seen = 0; self.server_info = None

        self.connections = []; self.threads = []

        # Start server monitor thread (if enabled)
        if not self.no_server_monitor and self.server_query:
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start()
            self.threads.append(self.server_info_thread) # Keep track for joining

        # Start display thread
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread) # Keep track

        # Start worker threads
        logger.info(f"Attempting to establish {self.num_connections} worker connections...")
        initial_success = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set(): break # Stop starting if asked
            conn_info = self._create_connection(i + 1)
            if conn_info:
                worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
                self.connections.append(conn_info) # Store connection info
                worker_thread.start()
                self.threads.append(worker_thread) # Add worker thread to list
                initial_success += 1
            else:
                self._increment_counter("initial_connection_failures")
            if self.num_connections > 50 and (i + 1) % 50 == 0: time.sleep(0.05) # Throttle startup

        logger.info(f"Successfully started {initial_success} workers initially. {self.initial_connection_failures} failed.")

        if initial_success == 0 and self.num_connections > 0:
            logger.error("FATAL: No worker connections could be started. Stopping test.")
            self.stop_test() # Trigger cleanup
            return

        # --- Main loop for timed tests or waiting for Ctrl+C ---
        try:
            if self.continuous_mode:
                # In continuous mode, just wait for the stop event (set by signal handler)
                self._stop_event.wait()
                logger.info("Stop event received, finishing...")
            else:
                # In timed mode, wait for duration or stop event
                wait_time = self.test_duration
                stopped_early = self._stop_event.wait(timeout=wait_time)
                if stopped_early:
                    logger.info("Test stopped early via signal.")
                else:
                    logger.info("Test duration reached.")
                    self.stop_test() # Trigger stop if duration completed normally

        except Exception as e: # Catch errors in the main waiting logic
             logger.error(f"Error in main test execution: {e}")
             self.stop_test() # Ensure cleanup on error

        # Final cleanup happens implicitly as stop_test is called either by duration, signal, or error

    def stop_test(self):
        if not self.active:
            # Avoid duplicate stop calls or stopping an inactive test
            # logger.debug("Stop called, but test is not active.")
            return

        logger.info("Stopping test...")
        self.active = False
        self._stop_event.set() # Signal all threads to stop
        self.end_time = time.time() if self.start_time > 0 else time.time()

        # Wait for threads to finish
        logger.info("Waiting for threads to complete...")
        join_timeout = 3.0 # Max time to wait for each thread

        # Iterate backwards to potentially remove threads as they join? No, just join.
        # Make a copy in case the list is modified elsewhere (shouldn't be)
        threads_to_join = self.threads[:]
        for thread in threads_to_join:
            if thread.is_alive():
                try:
                    if self.verbose: logger.debug(f"Joining thread: {thread.name}...")
                    thread.join(join_timeout)
                    if thread.is_alive():
                        logger.warning(f"Thread {thread.name} did not stop within timeout.")
                except Exception as e:
                    logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("All threads processed.")

        # Close server query socket if it exists and wasn't closed by its thread
        if self.server_query:
            self.server_query.close()

        # Final screen clear and report generation
        print(CLEAR_SCREEN) # Clear screen one last time
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed)

        logger.info("Test finished.")
        # Let the main script exit naturally now

    # --- Reporting ---
    def _generate_final_report(self, duration):
        print("="*30 + " Test Results Summary " + "="*30)
        duration = max(duration, 0.01) # Avoid division by zero

        # Get final stats (lock might not be strictly needed if threads are stopped, but safer)
        with self.lock:
            bytes_sent = self.bytes_sent; bytes_received = self.bytes_received
            asset_downloads = self.asset_downloads.copy(); asset_bandwidth = self.asset_bandwidth.copy()
            downloaded_files_count = len(self.downloaded_files)
            runtime_issues = self.runtime_connection_issues; initial_fails = self.initial_connection_failures
            final_server_status = self.server_status
            final_server_info = self.server_info.copy() if self.server_info else None
            server_log = self.server_status_log[:] # Copy log

        # Calculations
        sent_mb = bytes_sent / (1024*1024); received_mb = bytes_received / (1024*1024); total_mb = sent_mb + received_mb
        avg_rate_mbs = total_mb / duration; avg_send_mbs = sent_mb / duration; avg_recv_mbs = received_mb / duration
        total_assets = sum(asset_downloads.values()); total_asset_mb = sum(asset_bandwidth.values()) / (1024*1024)

        # Server Info Summary
        server_name = "N/A"; server_map = "N/A"; avg_ping = -1; min_ping = -1; max_ping = -1
        if not self.no_server_monitor:
            last_valid_log = next((log for log in reversed(server_log) if log.get('status') in ['ONLINE', 'ISSUES'] and log.get('name') != 'N/A'), None)
            if last_valid_log:
                server_name = last_valid_log.get('name', 'N/A')
                server_map = last_valid_log.get('map', 'N/A')
            elif final_server_info: # Fallback to last known info if log is sparse
                 server_name = final_server_info.get('name', 'N/A')
                 server_map = final_server_info.get('map', 'N/A')

            pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
            if pings:
                avg_ping = sum(pings)/len(pings); min_ping = min(pings); max_ping = max(pings)

        # --- Print Summary ---
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
        # Print asset counts table
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
         # Recalculate/get stats if needed, using locked access
         with self.lock:
            duration = max(0.01, duration) # Ensure duration > 0
            sent_mb = self.bytes_sent / (1024*1024)
            received_mb = self.bytes_received / (1024*1024)
            total_mb = sent_mb + received_mb
            avg_rate_mbs = total_mb / duration
            asset_downloads = self.asset_downloads.copy()
            asset_bandwidth = self.asset_bandwidth.copy()
            downloaded_files_metadata = list(self.downloaded_files)
            server_log = self.server_status_log[:]
            # Use locked values if available, otherwise use passed args or recalculate
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
                # Limit metadata in report? Or keep it? Keep for now.
                "tracked_files_metadata": downloaded_files_metadata
            },
            "server_status_log": server_log # Include the raw log
         }

         # Generate filename (use os.path.join)
         ts = int(time.time())
         report_filename = f"cs_bw_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts}.json"
         report_filepath = os.path.join(self.storage_dir, report_filename) # Save in storage dir

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
    print('\n') # Move cursor to newline after Ctrl+C
    logger.warning("Ctrl+C received! Initiating graceful shutdown...")
    if tester_instance and tester_instance.active:
         # Signal the running test to stop, don't block the handler
         # Use a separate thread if stop_test might block for too long
         # For now, assume stop_test is reasonably fast
         tester_instance.stop_test()
    else:
        logger.info("No active test instance found or test already stopping.")
        sys.exit(0) # Exit if no test to stop

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 Server Bandwidth Testing Tool (CLI Version)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    # Required argument
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 server.")

    # Optional arguments
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="Server port.")
    parser.add_argument("-c", "--connections", type=int, default=50, help="Number of concurrent connections/workers to simulate.")
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of the test in seconds (ignored if --continuous is set).")
    parser.add_argument("-dl", "--delay", type=float, default=0.05, help="Simulated delay factor per asset download 'chunk' (adjusts sleep time). Lower is faster simulation.")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging.")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run the test continuously until stopped manually (Ctrl+C). Overrides --duration.")
    parser.add_argument("--no-server-monitor", action="store_true", help="Disable querying server for status/info during the test.")
    parser.add_argument("--storage-dir", default="cs_test_reports", help="Directory to save JSON report files.")

    args = parser.parse_args()

    # Set logging level based on verbose flag
    if args.verbose:
        logger.setLevel(logging.DEBUG)
        logger.info("Verbose logging enabled.")
    else:
        logger.setLevel(logging.INFO)

    # --- Responsibility Warning ---
    logger.warning("="*70)
    logger.warning("⚠️ IMPORTANT RESPONSIBILITY NOTICE ⚠️")
    logger.warning("You are SOLELY responsible for the use of this tool.")
    logger.warning("Obtain EXPLICIT PERMISSION before testing any server you DO NOT own.")
    logger.warning("Misuse can negatively impact server performance, network infrastructure,")
    logger.warning("and is unethical and potentially illegal. Use responsibly.")
    logger.warning("="*70)
    time.sleep(2) # Brief pause to ensure warning is read

    # --- Create and run the tester ---
    try:
        # Instantiate the tester
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

        # Register the signal handler for SIGINT (Ctrl+C)
        signal.signal(signal.SIGINT, signal_handler)

        # Start the test (this will block appropriately based on mode)
        tester_instance.start_test()

        # If we reach here, the test finished (either timed out or was stopped)
        logger.info("Main thread exiting.")
        sys.exit(0)

    except Exception as e:
        logger.error(f"An unexpected error occurred in the main script: {type(e).__name__} - {str(e)}")
        # Optionally print traceback for debugging
        # import traceback
        # traceback.print_exc()
        sys.exit(1)
