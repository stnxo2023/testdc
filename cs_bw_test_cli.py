#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# CS16 UDP File Downloader - Downloads actual files from CS 1.6 server via UDP protocol
# Based on UDP simulation script (paste.txt)

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
import struct
from datetime import datetime
import requests
from urllib.parse import urljoin, unquote
from pathlib import Path

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150  # ms
SERVER_OFFLINE_TIMEOUT = 15  # seconds without response
LAST_FILES_DISPLAY_COUNT = 10  # How many recent events to show
UI_UPDATE_INTERVAL = 0.5  # How often to refresh the terminal stats (seconds)

# UDP protocol constants
HEADER = b"\xFF\xFF\xFF\xFF"
REQUEST_FILE_CMD = b"requestfile"  # Main command for requesting files
FRAGMENT_SIZE = 1024  # Max UDP fragment size to request
DOWNLOAD_TIMEOUT = 30  # Timeout for a single file download (seconds)
MAX_RETRIES = 5  # Max retries for a single fragment

# File types that can be downloaded
FILE_TYPES = [
    "maps/*.bsp",
    "models/*.mdl",
    "sound/*.wav",
    "sprites/*.spr",
    "media/*.mp3",
    "materials/*.vmt",
    "materials/*.vtf"
]

# Common file prefixes for maps
MAP_PREFIXES = ["de_", "cs_", "as_", "fy_", "ka_", "aim_", "awp_", "he_", "zm_", "35hp_", "gg_"]

# Log/Temp file config
ACTIVITY_LOG_FILENAME = "activity_log.txt"
UDP_VERIFY_FILENAME_PREFIX = "udp_verify_"

# --- Global logger setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr
)
logger = logging.getLogger('cs_udp_downloader')

# --- Activity Logger Setup (File logging) ---
activity_logger = logging.getLogger('activity_logger')
activity_logger.setLevel(logging.INFO)
activity_logger.propagate = False  # Don't send to main logger's stream handler

# Global variable to hold the tester instance for signal handling
tester_instance = None

# ==============================================================
# ServerQuery Class (Includes UDP save/delete verification)
# ==============================================================
class ServerQuery:
    def __init__(self, server_ip, server_port=DEFAULT_PORT, storage_dir="."):
        self.server_ip = server_ip
        self.server_port = server_port
        self.storage_dir = storage_dir  # For UDP verification files
        self.last_info = None
        self.last_rules = None
        self.last_ping = 0
        self.sock = None
        self.retry_count = 2
        self.timeout = 1.5
        self.last_challenge = None

    def _create_socket(self):
        if self.sock is not None:
            try:
                self.sock.close()
            except Exception:
                pass
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.settimeout(self.timeout)
        except Exception as e:
            logger.error(f"Query Socket Create Error: {e}")
            self.sock = None
            raise

    def _log_activity(self, level, message):
        """Helper to log to both main logger and activity file logger."""
        # Use the main logger's log method directly to ensure correct level handling
        logger.log(level, message)
        # Ensure activity logger is configured before writing
        if activity_logger.hasHandlers() and not isinstance(activity_logger.handlers[0], logging.NullHandler):
            activity_logger.log(level, message)
        elif level >= logging.WARNING:  # Log errors/warnings to main log if file log failed
            logger.log(level, f"[Activity Log Disabled] {message}")

    # --- MODIFIED: _send_recv includes UDP save/verify/delete ---
    def _send_recv(self, request, query_type="unknown"):
        if self.sock is None:
            try:
                self._create_socket()
            except Exception:
                return None, 0

        start_time = time.time()
        response = None
        ping = 0
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
                    verify_storage_dir = Path(self.storage_dir) / "udp_verify_temp"
                    try:
                        verify_storage_dir.mkdir(parents=True, exist_ok=True)
                    except OSError as e:
                        logger.error(f"Failed to create UDP verification dir '{verify_storage_dir}': {e}. Skipping verification.")
                        continue  # Skip verification for this response if dir fails

                    verify_filename = f"{UDP_VERIFY_FILENAME_PREFIX}{query_type}_{int(time.time()*1000)}.bin"
                    verify_filepath = verify_storage_dir / verify_filename
                    saved_ok = False
                    verify_msg_prefix = f"[UDP Verify] Query: {query_type}"
                    try:
                        with open(verify_filepath, 'wb') as vf:
                            vf.write(response)
                        saved_ok = True
                        # Log save success only if verbose or higher
                        self._log_activity(logging.DEBUG, f"{verify_msg_prefix} | Status: SAVED | Bytes: {len(response)} | Path: {verify_filepath}")
                    except Exception as e:
                        self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: SAVE_FAILED | Path: {verify_filepath} | Error: {e}")
                    finally:
                        if verify_filepath.exists():
                            try:
                                os.remove(verify_filepath)  # Use os.remove for files
                                if saved_ok:
                                    self._log_activity(logging.DEBUG, f"{verify_msg_prefix} | Status: DELETED | Path: {verify_filepath}")
                            except Exception as e:
                                self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: DELETE_FAILED | Path: {verify_filepath} | Error: {e}")
                        elif saved_ok:
                            self._log_activity(logging.WARNING, f"{verify_msg_prefix} | Status: DELETE_WARN | Path: {verify_filepath} | File not found after save.")
                    # --- End UDP Verification ---
                    return response, ping
                else:
                    logger.debug(f"Received empty UDP response (attempt {attempt+1}) for {query_type}")

            except socket.timeout:
                logger.debug(f"UDP {query_type} query timed out (attempt {attempt+1})")
                if attempt == self.retry_count - 1:
                    return None, 0
                time.sleep(0.1)
            except OSError as e:
                logger.warning(f"UDP Query OSError (attempt {attempt+1}): {e}")
                self.close()
                return None, 0
            except Exception as e:
                logger.error(f"Unexpected UDP Query Error (attempt {attempt+1}): {e}")
                self.close()
                return None, 0
        return None, 0

    # --- Getters using _send_recv ---
    def get_info(self):
        request = b"\xFF\xFF\xFF\xFFTSource Engine Query\x00"
        response, ping = self._send_recv(request, query_type="info")
        if response:
            parsed_info = self._parse_info(response)
            if parsed_info:
                self.last_ping = ping
                parsed_info['ping'] = ping
                self.last_info = parsed_info
                # Check for challenge response within info reply (uncommon but possible)
                if len(response) >= 9 and response[4:5] == b'A':
                    self.last_challenge = response[5:9]
                    logger.debug(f"Received challenge {self.last_challenge.hex()} embedded in info response.")
                else:
                    # Check if it's a simple challenge response instead of info
                    if response[4:5] == b'A' and len(response) >= 9:
                        self.last_challenge = response[5:9]
                        logger.debug(f"Received challenge {self.last_challenge.hex()} instead of info. Retrying info might be needed.")
                        return None  # Indicate info wasn't received, only challenge
                    else:
                        self.last_challenge = None  # No challenge in this response
                return parsed_info
            # Handle case where only a challenge was received
            elif response[4:5] == b'A' and len(response) >= 9:
                self.last_challenge = response[5:9]
                logger.debug(f"Received challenge {self.last_challenge.hex()} instead of info. Retrying info might be needed.")
                return None
        return None

    def get_rules(self):
        challenge_bytes = self.last_challenge or b'\xFF\xFF\xFF\xFF'  # Use last challenge or default
        request = b'\xFF\xFF\xFF\xFFV' + challenge_bytes
        response, _ = self._send_recv(request, query_type="rules")
        if response and response[4:5] == b'E':
            parsed_rules = self._parse_rules(response)
            if parsed_rules:
                self.last_rules = parsed_rules
            return parsed_rules
        elif response and response[4:5] == b'A':  # Got challenge, retry
            self.last_challenge = response[5:9]
            logger.info(f"Received challenge {self.last_challenge.hex()} for rules. Retrying.")
            request = b'\xFF\xFF\xFF\xFFV' + self.last_challenge
            response, _ = self._send_recv(request, query_type="rules_retry")
            if response and response[4:5] == b'E':
                parsed_rules = self._parse_rules(response)
                if parsed_rules:
                    self.last_rules = parsed_rules
                return parsed_rules
        # Handle case where get_info might have failed but set a challenge
        elif not response and self.last_challenge:
            logger.debug("Rules query failed, retrying with known challenge.")
            request = b'\xFF\xFF\xFF\xFFV' + self.last_challenge
            response, _ = self._send_recv(request, query_type="rules_retry_known_challenge")
            if response and response[4:5] == b'E':
                parsed_rules = self._parse_rules(response)
                if parsed_rules:
                    self.last_rules = parsed_rules
                return parsed_rules
        return None

    def get_players(self):
        """Request player information from the server."""
        challenge_bytes = self.last_challenge or b'\xFF\xFF\xFF\xFF'  # Use last challenge or default
        request = b'\xFF\xFF\xFF\xFFU' + challenge_bytes
        response, _ = self._send_recv(request, query_type="players")
        
        # If we received a challenge response instead, retry with that challenge
        if response and response[4:5] == b'A':
            self.last_challenge = response[5:9]
            logger.info(f"Received challenge {self.last_challenge.hex()} for players. Retrying.")
            request = b'\xFF\xFF\xFF\xFFU' + self.last_challenge
            response, _ = self._send_recv(request, query_type="players_retry")
            
        if response and response[4:5] == b'D':
            try:
                # Parse player info - this will return usernames which we can use to identify common map names
                offset = 5  # Skip header and command byte
                num_players = response[offset]
                offset += 1
                players = []
                
                for _ in range(num_players):
                    # Skip index byte
                    offset += 1
                    
                    # Read player name
                    name_end = response.find(b'\x00', offset)
                    if name_end == -1:
                        break
                    name = response[offset:name_end].decode('utf-8', errors='ignore')
                    offset = name_end + 1
                    
                    # Skip frags (4 bytes) and time (4 bytes)
                    offset += 8
                    
                    players.append(name)
                
                return players
            except Exception as e:
                logger.error(f"Error parsing player response: {e}")
                
        return []

    # --- Parsers (_parse_info, _parse_rules) ---
    def _parse_info(self, response):
        try:
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF':
                return None
            header_byte = response[4:5]
            offset = 5
            if header_byte == b'I':  # Source / GoldSrc (modern)
                # Protocol byte seems unreliable/optional for GoldSrc sometimes
                # Let's try reading string directly
                def read_string(data, start_offset):
                    end = data.find(b'\x00', start_offset)
                    if end == -1:
                        raise ValueError("Malformed string (null terminator missing)")
                    # Handle potential empty strings if terminator is immediate
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1

                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)

                # Check remaining length, account for different structures
                if offset + 9 <= len(response):  # Source like structure (AppID + counts)
                    offset += 2  # Skip AppID (2 bytes)
                    player_count = response[offset]
                    offset += 1
                    max_players = response[offset]
                    offset += 1
                    bot_count = response[offset]
                    offset += 1
                    # ... potentially more fields like server type, os, password, vac ...
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': player_count, 'max_players': max_players, 'bots': bot_count}
                elif offset + 2 <= len(response):  # Simpler GoldSrc like structure (counts only)
                    player_count = response[offset]
                    offset += 1
                    max_players = response[offset]
                    offset += 1
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': player_count, 'max_players': max_players, 'bots': 0}  # Assume no bots if field missing
                else:
                    # Fallback if too short after strings - might be very old GoldSrc or truncated
                    logger.warning(f"Info response possibly truncated after strings. Len: {len(response)}, Offset: {offset}")
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': 0, 'max_players': 0, 'bots': 0}

            elif header_byte == b'm':  # Older GoldSrc response format (includes address)
                addr_end = response.find(b'\x00', offset)
                if addr_end == -1:
                    raise ValueError("Malformed address string")
                # server_address = response[offset:addr_end].decode('utf-8', errors='ignore')
                offset = addr_end + 1

                def read_string_gs(data, start_offset):
                    end = data.find(b'\x00', start_offset)
                    if end == -1:
                        raise ValueError("Malformed string")
                    return data[start_offset:end].decode('utf-8', errors='ignore'), end + 1

                server_name, offset = read_string_gs(response, offset)
                map_name, offset = read_string_gs(response, offset)
                game_dir, offset = read_string_gs(response, offset)
                game_desc, offset = read_string_gs(response, offset)
                if offset + 2 > len(response):
                    raise ValueError("Too short for player counts")  # Need at least player/max
                player_count = response[offset]
                offset += 1
                max_players = response[offset]  # Removed offset increment, might be end of packet
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': 0}
            elif header_byte == b'A':
                # This means we received a challenge response when expecting info
                logger.debug("Received A2S_CHALLENGE response when expecting A2S_INFO.")
                return None  # Not an error, but not the info we wanted
            else:
                logger.warning(f"Unknown info response header byte: {header_byte.hex()}")
                return None
        except ValueError as e:
            logger.warning(f"Parse INFO ValueError: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except IndexError as e:
            logger.warning(f"Parse INFO IndexError: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except Exception as e:
            logger.error(f"Unexpected Parse INFO error: {e}", exc_info=True)
            return None

    def _parse_rules(self, response):
        try:
            if not response or len(response) < 7 or response[:5] != b'\xFF\xFF\xFF\xFFE':
                return None
            rules_count = int.from_bytes(response[5:7], 'little')
            offset = 7
            rules = {}
            for i in range(rules_count):
                name_end = response.find(b'\x00', offset)
                if name_end == -1:
                    raise ValueError(f"Malformed rule name (rule {i+1}/{rules_count})")
                rule_name = response[offset:name_end].decode('utf-8', errors='ignore')
                offset = name_end + 1
                value_end = response.find(b'\x00', offset)
                if value_end == -1:
                    raise ValueError(f"Malformed rule value for '{rule_name}' (rule {i+1}/{rules_count})")
                rule_value = response[offset:value_end].decode('utf-8', errors='ignore')
                offset = value_end + 1
                rules[rule_name] = rule_value
                if offset > len(response):  # Prevent reading past buffer if last value is malformed
                    if i < rules_count - 1:  # Only warn if it wasn't the last expected rule
                        logger.warning(f"Rule parsing stopped early due to offset exceeding length after rule '{rule_name}'")
                    break
            if len(rules) != rules_count:
                logger.warning(f"Expected {rules_count} rules, but parsed {len(rules)}")
            return rules
        except ValueError as e:
            logger.warning(f"Parse RULES ValueError: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except IndexError as e:
            logger.warning(f"Parse RULES IndexError: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except Exception as e:
            logger.error(f"Unexpected Parse RULES error: {e}", exc_info=True)
            return None

    def close(self):
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None

# ==============================================================
# UDP File Download Class - Core functionality for actual downloads
# ==============================================================
class UDPFileDownloader:
    def __init__(self, server_ip, server_port, save_dir):
        self.server_ip = server_ip
        self.server_port = server_port
        self.save_dir = Path(save_dir)
        self.sock = None
        self.timeout = 5.0  # Initial timeout
        self.current_file = None
        self.current_size = 0
        self.bytes_received = 0
        self.fragment_size = FRAGMENT_SIZE
        
    def _create_socket(self):
        """Create a UDP socket for file download"""
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
                
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.settimeout(self.timeout)
        return self.sock
        
    def download_file(self, file_path):
        """Download a specific file from the server via UDP"""
        if not self.sock:
            try:
                self._create_socket()
            except Exception as e:
                logger.error(f"Failed to create socket: {e}")
                return False, 0
                
        self.current_file = file_path
        self.bytes_received = 0
        
        # Prepare directories
        save_path = self.save_dir / file_path
        save_path.parent.mkdir(parents=True, exist_ok=True)
        
        # For clarity in logging
        file_id = file_path.replace('\\', '/')
        
        try:
            # Create request packet: "\xFF\xFF\xFF\xFFrequestfile" + file_path + null terminator
            request = HEADER + REQUEST_FILE_CMD + b" " + file_path.encode('utf-8') + b"\x00"
            
            logger.debug(f"Requesting file: {file_path}")
            start_time = time.time()
            
            # Send initial request - this could return file size info or first fragment
            self.sock.sendto(request, (self.server_ip, self.server_port))
            
            # Variables for tracking download progress
            fragments = {}
            total_fragments = 0
            file_size = 0
            last_fragment_received = time.time()
            download_complete = False
            
            # Main download loop
            while time.time() - last_fragment_received < DOWNLOAD_TIMEOUT and not download_complete:
                try:
                    data, addr = self.sock.recvfrom(self.fragment_size + 256)  # Extra space for headers
                    
                    if not data:
                        continue
                        
                    last_fragment_received = time.time()
                    
                    # Process response header
                    if data.startswith(HEADER):
                        # Skip over FF FF FF FF header
                        offset = 4
                        
                        # Check response type
                        if len(data) > offset and data[offset:offset+1] == b'R':  # File response
                            # Parse file info - format depends on exact protocol version
                            # This is a simplified implementation
                            offset += 1
                            
                            # Some response types include file size and fragment info
                            if len(data) > offset + 8:
                                file_id_bytes = data[offset:offset+8]
                                offset += 8
                                
                                # Check if this contains file size info
                                if len(data) > offset + 4:
                                    try:
                                        file_size = struct.unpack("<I", data[offset:offset+4])[0]
                                        offset += 4
                                        logger.debug(f"File size reported: {file_size} bytes")
                                    except struct.error:
                                        logger.warning("Could not parse file size")
                                
                                # Fragment number
                                if len(data) > offset + 2:
                                    try:
                                        fragment_number = struct.unpack("<H", data[offset:offset+2])[0]
                                        offset += 2
                                        
                                        # First fragment - determine total fragments
                                        if fragment_number == 0 and total_fragments == 0:
                                            if file_size > 0:
                                                total_fragments = (file_size + self.fragment_size - 1) // self.fragment_size
                                                logger.debug(f"Expected total fragments: {total_fragments}")
                                        
                                        # Fragment data starts after header
                                        fragment_data = data[offset:]
                                        fragment_size = len(fragment_data)
                                        
                                        # Store fragment
                                        fragments[fragment_number] = fragment_data
                                        self.bytes_received += fragment_size
                                        
                                        # Request next fragment if needed
                                        if len(fragments) < total_fragments:
                                            # Request specific fragment
                                            next_fragment = min(set(range(total_fragments)) - set(fragments.keys()), default=None)
                                            if next_fragment is not None:
                                                fragment_request = HEADER + REQUEST_FILE_CMD + b" " + file_path.encode('utf-8')
                                                fragment_request += b" " + str(next_fragment).encode('utf-8') + b"\x00"
                                                self.sock.sendto(fragment_request, (self.server_ip, self.server_port))
                                        else:
                                            # All fragments received
                                            download_complete = True
                                    except struct.error:
                                        logger.warning("Could not parse fragment number")
                            
                            # Handle data directly if no fragment info
                            else:
                                # Simple response with just data
                                fragment_data = data[offset:]
                                fragments[0] = fragment_data
                                self.bytes_received += len(fragment_data)
                                download_complete = True
                                
                        elif len(data) > offset and data[offset:offset+1] == b'E':  # Error
                            error_msg = data[offset+1:].split(b'\x00')[0].decode('utf-8', errors='ignore')
                            logger.error(f"Server returned error: {error_msg}")
                            return False, self.bytes_received
                            
                except socket.timeout:
                    # Request missing fragments
                    if total_fragments > 0 and len(fragments) < total_fragments:
                        missing = set(range(total_fragments)) - set(fragments.keys())
                        if missing:
                            next_fragment = min(missing)
                            fragment_request = HEADER + REQUEST_FILE_CMD + b" " + file_path.encode('utf-8')
                            fragment_request += b" " + str(next_fragment).encode('utf-8') + b"\x00"
                            self.sock.sendto(fragment_request, (self.server_ip, self.server_port))
                            logger.debug(f"Requesting missing fragment {next_fragment}")
                    else:
                        # If we don't know total fragments yet, just retry the main request
                        self.sock.sendto(request, (self.server_ip, self.server_port))
                
            # Check if download was successful
            if download_complete or (total_fragments > 0 and len(fragments) == total_fragments):
                # Assemble file from fragments
                with open(save_path, 'wb') as f:
                    for i in range(len(fragments)):
                        if i in fragments:
                            f.write(fragments[i])
                
                end_time = time.time()
                download_time = end_time - start_time
                download_speed = self.bytes_received / download_time / 1024 if download_time > 0 else 0
                
                logger.info(f"Downloaded {file_path} - {self.bytes_received} bytes in {download_time:.2f}s ({download_speed:.2f} KB/s)")
                return True, self.bytes_received
            else:
                logger.warning(f"Download incomplete for {file_path}: Got {len(fragments)}/{total_fragments} fragments, {self.bytes_received} bytes")
                return False, self.bytes_received
                
        except socket.timeout:
            logger.error(f"Timeout downloading {file_path}")
            return False, self.bytes_received
        except Exception as e:
            logger.error(f"Error downloading {file_path}: {e}")
            return False, self.bytes_received
            
    def close(self):
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
            self.sock = None

# ==============================================================
# CS16BandwidthTester Class (New version with real downloads)
# ==============================================================
class CS16BandwidthTester:
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 verbose, storage_dir, continuous_mode, no_server_monitor,
                 activity_log_filename=ACTIVITY_LOG_FILENAME):

        # Store args
        self.server_ip = server_ip
        self.server_port = server_port
        self.num_connections = num_connections
        self.test_duration = test_duration
        self.verbose = verbose
        self.continuous_mode = continuous_mode
        self.storage_dir = Path(storage_dir)
        self.no_server_monitor = no_server_monitor
        self.activity_log_filename = activity_log_filename

        # --- Setup Storage and Logging ---
        self.activity_log_filepath = None
        self.downloads_dir = self.storage_dir / "downloads"

        try:
            self.storage_dir.mkdir(parents=True, exist_ok=True)
            logger.info(f"Using storage directory: {self.storage_dir}")
            self.downloads_dir.mkdir(parents=True, exist_ok=True)
            logger.info(f"Files will be downloaded to: {self.downloads_dir}")
        except OSError as e:
            logger.error(f"Failed to create storage directory '{self.storage_dir}' or subdir: {e}. Exiting.")
            sys.exit(1)  # Exit if storage cannot be created

        self._configure_activity_logger()

        # Core state
        self.active = False
        self.threads = []
        self.connections = []
        self.lock = threading.Lock()
        self._stop_event = threading.Event()
        self.start_time = 0
        self.end_time = 0

        # Counters
        self.bytes_received = 0
        self.downloads_completed = 0
        self.downloads_failed = 0
        self.initial_connection_failures = 0
        self.runtime_connection_issues = 0
        self.active_workers_count = 0

        # Server info tracking
        self.server_query = None
        if not self.no_server_monitor:
            # Pass the main storage dir, ServerQuery will handle its own temp subdir
            self.server_query = ServerQuery(server_ip, server_port, storage_dir=str(self.storage_dir))
        self.server_info = None
        self.server_rules = None
        self.known_maps = []
        self.discovered_files = []
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN"
        self.server_last_seen = 0
        self.server_info_thread = None
        self.server_info_interval = 5
        self.server_status_log = []  # Log of status/ping from ServerQuery

        # Asset/Event tracking
        self.last_activity = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        self.bandwidth_log_points = []  # Tracks combined rate

        self.display_thread = None

    def _configure_activity_logger(self):
        # Configure activity_logger file handler
        # Check if handlers already exist to prevent duplicates during potential restarts
        if activity_logger.hasHandlers():
            # Close existing handlers before adding new ones
            for handler in activity_logger.handlers[:]:
                try:
                    handler.close()
                    activity_logger.removeHandler(handler)
                except Exception as e:
                    logger.warning(f"Could not close existing activity log handler: {e}")
        try:
            # Ensure the main storage directory exists before creating the log file path
            self.storage_dir.mkdir(parents=True, exist_ok=True)
            self.activity_log_filepath = self.storage_dir / self.activity_log_filename
            file_handler = logging.FileHandler(str(self.activity_log_filepath), mode='a', encoding='utf-8')  # Path object needs conversion
            file_formatter = logging.Formatter('%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
            file_handler.setFormatter(file_formatter)
            activity_logger.addHandler(file_handler)
            activity_logger.info(f"--- Activity Log Started ({datetime.now().isoformat()}) ---")
            logger.info(f"Logging activity details to: {self.activity_log_filepath}")
        except Exception as e:
            logger.error(f"Failed to configure activity log file handler: {e}")
            # Ensure activity_logger doesn't cause errors if file logging fails
            if not activity_logger.hasHandlers():
                activity_logger.addHandler(logging.NullHandler())

    def _increment_counter(self, counter_name, value=1):
        with self.lock:
            setattr(self, counter_name, getattr(self, counter_name) + value)

    def _decrement_counter(self, counter_name, value=1):
        self._increment_counter(counter_name, -value)

    def _log_activity_event(self, worker_id, event_type, status, identifier, bytes_val=0, error_msg="", detail=""):
        """Logs events to activity log file and potentially console."""
        message = f"Worker {worker_id:<3} [{event_type:<10}] | Status: {status:<10} | ID: {identifier}"
        if bytes_val > 0:
            message += f" | Bytes: {bytes_val:<10}"
        if detail:
            message += f" | Detail: {detail}"
        if error_msg:
            message += f" | Error: {error_msg}"

        log_level = logging.INFO
        if "FAIL" in status or "ERROR" in status or "TIMEOUT" in status or "WARN" in status:
            log_level = logging.WARNING
        if status == "INTERRUPT":
            log_level = logging.INFO

        # Log to main logger (console) based on severity or verbosity
        console_log_level = log_level if log_level >= logging.WARNING else logging.DEBUG
        if log_level >= logging.INFO or self.verbose:
            # Simplified console message
            console_msg = f"Worker {worker_id}: {event_type} {status}: {identifier}"
            if bytes_val > 0:
                console_msg += f" ({bytes_val/1024:.1f}KB)"
            if error_msg and log_level >= logging.WARNING:
                console_msg += f" - {error_msg}"  # Show error only for warnings/errors

            logger.log(console_log_level, console_msg)

        # Always log the full message to the activity file if handler is present
        if activity_logger.hasHandlers() and not isinstance(activity_logger.handlers[0], logging.NullHandler):
            activity_logger.log(log_level, message)
        elif log_level >= logging.WARNING:  # Fallback console log for critical messages if file handler failed
            logger.log(log_level, f"[Activity Log Disabled] {message}")

        # Update UI deque
        with self.lock:
            # Add more relevant info to UI entry
            ui_status = ""
            if status not in ["SUCCESS", "DELETED", "SAVED"]:
                ui_status = f" [{status}]"  # Show status if not normal completion

            # Shorten identifier if it's a long path
            display_id = identifier
            if len(identifier) > 40:
                display_id = "..." + identifier[-37:]

            ui_entry = f"{display_id} ({bytes_val/1024:.1f}KB){ui_status}"
            self.last_activity.append(ui_entry)

    # --- Download Logic - Real UDP downloads ---
    def _download_file(self, conn_info):
        """Download a file from the server via UDP protocol."""
        conn_id = conn_info['id']
        
        # Check if we have a downloader instance, create if not
        downloader = conn_info.get("downloader")
        if not downloader:
            try:
                downloader = UDPFileDownloader(self.server_ip, self.server_port, self.downloads_dir)
                conn_info["downloader"] = downloader
            except Exception as e:
                logger.error(f"Worker {conn_id}: Failed to create downloader: {e}")
                self._increment_counter("runtime_connection_issues")
                conn_info["status"] = "error"
                return False
                
        # Get a file to download
        file_to_download = self._get_file_to_download()
        if not file_to_download:
            # No files to download, wait for more
            conn_info["status"] = "waiting_file"
            return False
            
        conn_info["status"] = "downloading"
        conn_info["current_task"] = f"Downloading {file_to_download}"
        conn_info["last_activity_time"] = time.time()
        
        try:
            # Perform the actual download
            success, bytes_received = downloader.download_file(file_to_download)
            
            with self.lock:
                self.bytes_received += bytes_received
                
            if success:
                self._increment_counter("downloads_completed")
                self._log_activity_event(conn_id, "UDP Download", "SUCCESS", file_to_download, bytes_received)
                conn_info["status"] = "idle"
                return True
            else:
                self._increment_counter("downloads_failed")
                self._log_activity_event(conn_id, "UDP Download", "FAILED", file_to_download, bytes_received)
                conn_info["status"] = "error"
                return False
                
        except Exception as e:
            self._increment_counter("downloads_failed")
            self._increment_counter("runtime_connection_issues")
            self._log_activity_event(conn_id, "UDP Download", "ERROR", file_to_download, 0, str(e))
            conn_info["status"] = "error"
            
            # Close and recreate downloader on error
            try:
                downloader.close()
                conn_info["downloader"] = UDPFileDownloader(self.server_ip, self.server_port, self.downloads_dir)
            except:
                conn_info["downloader"] = None
                
            return False

    def _get_file_to_download(self):
        """Selects a file to download - prioritizes maps and discovered content."""
        with self.lock:
            choices = []
            
            # First priority: current map
            if self.server_info and 'map' in self.server_info:
                current_map = self.server_info['map']
                if current_map:
                    map_path = f"maps/{current_map}.bsp"
                    choices.append(map_path)
                    
                    # Also add common files associated with this map
                    choices.append(f"maps/{current_map}.txt")  # Custom map text
                    choices.append(f"maps/{current_map}.res")  # Resource file
                    choices.append(f"gfx/env/{current_map}up.tga")  # Skybox
                    choices.append(f"gfx/env/{current_map}dn.tga")
                    choices.append(f"gfx/env/{current_map}lf.tga")
                    choices.append(f"gfx/env/{current_map}rt.tga")
                    choices.append(f"gfx/env/{current_map}ft.tga")
                    choices.append(f"gfx/env/{current_map}bk.tga")
            
            # Second priority: other known maps
            for map_name in self.known_maps:
                choices.append(f"maps/{map_name}.bsp")
            
            # Third priority: discovered files from .res files
            choices.extend(self.discovered_files)
            
            # Fourth priority: common files with random prefix/suffix
            for file_type in FILE_TYPES:
                base_type = file_type.split('*.')[0]
                extension = file_type.split('*.')[1]
                
                if base_type == "maps/":
                    # Try common map prefixes
                    for prefix in MAP_PREFIXES:
                        num = random.randint(1, 5)
                        choices.append(f"{base_type}{prefix}_{num}.{extension}")
                elif base_type == "models/":
                    model_types = ["player", "v_", "p_", "w_"]
                    for model_type in model_types:
                        choices.append(f"{base_type}{model_type}{random.randint(1, 10)}.{extension}")
                else:
                    # Random number for other file types
                    choices.append(f"{base_type}file_{random.randint(1, 100)}.{extension}")
            
            if not choices:
                return None
                
            # Return a random file path from our choices
            return random.choice(choices)

    # --- Worker Thread ---
    def _connection_worker(self, conn_info):
        conn_id = conn_info['id']
        worker_log_prefix = f"Worker {conn_id}"
        if self.verbose:
            logger.debug(f"{worker_log_prefix}: Started.")
        self._increment_counter("active_workers_count")
        conn_info["status"] = "starting"

        try:
            while self.active and not self._stop_event.is_set():
                conn_info["status"] = "idle"
                success = False
                start_task_time = time.time()

                # Attempt to download a file
                conn_info["current_task"] = "Preparing Download"
                success = self._download_file(conn_info)  # Status set inside

                # Wait before next attempt, potentially longer on failure
                end_task_time = time.time()
                task_duration = end_task_time - start_task_time
                # Base delay slightly longer, add randomness
                delay_base = 0.1 if success else 0.5
                # Add more variability
                worker_delay = random.uniform(delay_base, delay_base + 0.2)

                conn_info["status"] = "sleeping"
                conn_info["current_task"] = f"Sleeping ({worker_delay:.2f}s)"
                if self.verbose:
                    logger.debug(f"{worker_log_prefix}: Task took {task_duration:.3f}s. Sleeping {worker_delay:.3f}s.")
                # Use wait() for stop event checking during sleep
                if self._stop_event.wait(timeout=worker_delay):
                    logger.debug(f"{worker_log_prefix}: Stop event during sleep.")
                    break  # Exit loop if stop event is set during sleep

        except Exception as e:
            logger.error(f"{worker_log_prefix}: Unhandled loop error: {e}", exc_info=self.verbose)
            conn_info["status"] = "error_loop"
            conn_info["current_task"] = "ERROR"
            self._increment_counter("runtime_connection_issues")
        finally:
            final_status = conn_info.get("status", "unknown")
            self._decrement_counter("active_workers_count")
            conn_info["status"] = "stopped"
            conn_info["current_task"] = "Stopped"
            
            # Close downloader
            downloader = conn_info.get("downloader")
            if downloader:
                try:
                    downloader.close()
                except:
                    pass
                    
            if self.verbose or final_status.startswith("error"):
                logger.debug(f"{worker_log_prefix}: Finished (Final Status: {final_status}).")

    # --- Server Info Update Thread ---
    def _update_server_info(self):
        """Updates server info (map, rules) periodically via UDP."""
        if not self.server_query:
            return
        monitor_log_prefix = "(ServerMon)"
        if self.verbose:
            logger.debug(f"{monitor_log_prefix} Thread started.")
        query_rules_interval = 30  # seconds
        query_players_interval = 20  # seconds
        last_rules_query_time = 0
        last_players_query_time = 0
        # Force immediate query on start if not continuous mode, or slight delay otherwise
        next_query_time = time.time() + (0.1 if not self.continuous_mode else 1.0)

        while self.active and not self._stop_event.is_set():
            wait_time = next_query_time - time.time()
            if wait_time > 0:
                # Wait efficiently using the stop event
                if self._stop_event.wait(timeout=wait_time):
                    break  # Exit if stop event is set during wait

            if self._stop_event.is_set():
                break  # Check again after wait

            current_status = "UNKNOWN"
            ping = -1
            map_name = None
            info_success = False

            try:
                logger.debug(f"{monitor_log_prefix} Querying server info...")
                server_info = self.server_query.get_info()
                timestamp = time.time()

                if server_info:
                    info_success = True
                    with self.lock:
                        self.server_info = server_info
                        self.server_last_seen = timestamp
                        ping = server_info.get('ping', -1)
                        current_status = "ISSUES" if ping < 0 or ping > HIGH_PING_THRESHOLD else "ONLINE"
                        self.server_status = current_status
                        new_map_name = server_info.get('map')
                        if new_map_name and new_map_name not in self.known_maps:
                            self.known_maps.append(new_map_name)
                            logger.info(f"{monitor_log_prefix} Added map to known list: {new_map_name}")
                        map_name = new_map_name  # Store for logging
                else:  # Query failed
                    info_success = False  # Ensure flag is false
                    with self.lock:
                        offline_threshold_met = self.server_last_seen > 0 and (timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT)
                        if offline_threshold_met:
                            current_status = "OFFLINE"
                        else:
                            current_status = "ISSUES" if self.server_status != "OFFLINE" else "OFFLINE"  # Stay offline if already marked
                        self.server_status = current_status
                        # Don't clear server_info immediately, keep last known

                # Get Rules periodically if info succeeded
                needs_rules_query = info_success and (time.time() - last_rules_query_time > query_rules_interval)

                if needs_rules_query:
                    logger.debug(f"{monitor_log_prefix} Querying server rules...")
                    rules = self.server_query.get_rules()
                    timestamp_rules = time.time()
                    if rules is not None:  # Distinguish between failed query (None) and empty rules ({})
                        last_rules_query_time = timestamp_rules  # Update time only on successful query
                        with self.lock:
                            self.server_rules = rules
                            
                # Get Players periodically to extract usernames and possible map references
                needs_players_query = info_success and (time.time() - last_players_query_time > query_players_interval)
                
                if needs_players_query:
                    logger.debug(f"{monitor_log_prefix} Querying player info...")
                    players = self.server_query.get_players()
                    last_players_query_time = time.time()
                    
                    # Analyze player names for possible map references
                    for player_name in players:
                        for prefix in MAP_PREFIXES:
                            if prefix in player_name.lower():
                                # Try to extract a map name from the player name
                                name_parts = player_name.lower().split(prefix)
                                if len(name_parts) > 1 and name_parts[1]:
                                    possible_map = name_parts[1].strip().split()[0]
                                    # Clean up potential map name
                                    possible_map = ''.join(c for c in possible_map if c.isalnum() or c == '_')
                                    if possible_map and len(possible_map) >= 3 and possible_map not in self.known_maps:
                                        map_guess = f"{prefix}{possible_map}"
                                        self.known_maps.append(map_guess)
                                        logger.info(f"{monitor_log_prefix} Guessed map from player name: {map_guess}")

            except Exception as e:
                logger.error(f"{monitor_log_prefix} Unhandled error: {e}", exc_info=self.verbose)
                with self.lock:
                    current_status = "ERROR"
                    self.server_status = current_status

            # Log current status snapshot
            status_log_entry = {'timestamp': time.time(), 'status': current_status, 'ping': ping, 'map': map_name}
            with self.lock:
                self.server_status_log.append(status_log_entry)

            # Schedule next query
            next_query_time = time.time() + self.server_info_interval

        # Cleanup query socket when thread exits
        if self.server_query:
            self.server_query.close()
        if self.verbose:
            logger.debug(f"{monitor_log_prefix} Thread finished.")

    # --- Parse Resource Files ---
    def _parse_resource_files(self):
        """Check for .res files in the downloads directory and extract file references"""
        try:
            res_files = list(self.downloads_dir.glob("**/*.res"))
            if not res_files:
                return
                
            logger.info(f"Found {len(res_files)} resource files to parse")
            
            for res_file in res_files:
                try:
                    with open(res_file, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                        
                    new_files = 0
                    # Look for resource entries, typically in format: 
                    # { "file1.ext" } or { "models/file1.mdl" }
                    import re
                    matches = re.findall(r'{\s*"([^"]+)"\s*}', content)
                    
                    for match in matches:
                        file_path = match.strip()
                        if file_path and file_path not in self.discovered_files:
                            self.discovered_files.append(file_path)
                            new_files += 1
                            
                    if new_files > 0:
                        logger.info(f"Added {new_files} new files from {res_file.name}")
                        
                except Exception as e:
                    logger.warning(f"Error parsing {res_file}: {e}")
                    
        except Exception as e:
            logger.error(f"Error scanning for resource files: {e}")

    # --- Realtime Display Thread ---
    def _display_realtime_stats(self):
        """Displays real-time stats"""
        if self.verbose:
            logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time
        CURSOR_TO_HOME = "\033[H"
        CLEAR_LINE = "\033[K"
        CLEAR_SCREEN_FROM_CURSOR = "\033[J"
        term_width = 80
        try:
            term_width = os.get_terminal_size().columns
        except OSError:
            logger.warning("Could not detect terminal width, using 80.")
            term_width = 80

        while self.active and not self._stop_event.is_set():
            lines_to_print = []
            try:
                # --- Gather Data under Lock ---
                with self.lock:
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    bytes_received = self.bytes_received
                    downloads_ok = self.downloads_completed
                    downloads_fail = self.downloads_failed
                    active_workers = self.active_workers_count
                    runtime_issues = self.runtime_connection_issues
                    initial_fails = self.initial_connection_failures
                    current_server_status = self.server_status
                    current_ping = self.server_info.get('ping', -1) if self.server_info else -1
                    current_players = self.server_info.get('players', -1) if self.server_info else -1
                    current_max_players = self.server_info.get('max_players', -1) if self.server_info else -1
                    current_map = self.server_info.get('map', 'UNKNOWN') if self.server_info else 'UNKNOWN'
                    known_maps_count = len(self.known_maps)
                    last_activity = list(self.last_activity)

                # --- Calculate Metrics ---
                recv_mb = bytes_received / (1024*1024)
                avg_rate_mbs = (recv_mb * 8) / elapsed if elapsed > 0 else 0  # Rate in Megabits/sec
                avg_rate_MBs = recv_mb / elapsed if elapsed > 0 else 0  # Rate in MegaBytes/sec

                # Log bandwidth point (MB/s)
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                    with self.lock:
                        self.bandwidth_log_points.append((elapsed, avg_rate_MBs))  # Log MB/s rate
                    last_bw_log_time = current_time

                # --- Format Output Lines ---
                status = "Running" if self.active else "Stopped"
                test_mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"
                header = f"--- CS 1.6 UDP Downloader ({self.server_ip}:{self.server_port}) ---".center(term_width)
                lines_to_print.append(header)

                line_status = f" Status: {status} | Test Mode: {test_mode}"
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
                    s_player_str = f"Plyrs: {current_players}/{current_max_players}" if current_players >= 0 else "Plyrs: N/A"
                    s_map_str = f" Current Map: {current_map}"

                    # Layout: Status | Ping | Players
                    width_status = len(s_status_str)
                    width_ping = len(s_ping_str)
                    width_player = len(s_player_str)
                    spaces_total = max(0, term_width - width_status - width_ping - width_player)
                    spaces1 = spaces_total // 2
                    spaces2 = spaces_total - spaces1
                    lines_to_print.append(f"{s_status_str}{' '*spaces1}{s_ping_str}{' '*spaces2}{s_player_str}".ljust(term_width))
                    lines_to_print.append(s_map_str[:term_width].ljust(term_width))  # Map on next line
                    lines_to_print.append(f" Known Maps: {known_maps_count} | Discovered Files: {len(self.discovered_files)}")

                lines_to_print.append("-" * term_width)
                lines_to_print.append("[Download Activity & Bandwidth]".center(term_width))

                dl_line = f" Total Recv:  {recv_mb:>7.2f} MB | OK: {downloads_ok} | Failed: {downloads_fail}"
                lines_to_print.append(dl_line.ljust(term_width))

                # Display both Mbps and MB/s rates
                rate_line_mbps = f" Avg Rate: {avg_rate_mbs:>6.2f} Mbps"
                rate_line_MBs = f"({avg_rate_MBs:>6.2f} MB/s)"
                lines_to_print.append(f"{rate_line_mbps:<{max(0, term_width - len(rate_line_MBs))}}{rate_line_MBs}")

                lines_to_print.append("-" * term_width)
                lines_to_print.append(f"[Last {LAST_FILES_DISPLAY_COUNT} Activities]".center(term_width))
                if last_activity:
                    for activity in reversed(last_activity):
                        lines_to_print.append(f" {activity[:term_width-2].ljust(term_width-2)}")  # Pad inside line
                    # Fill remaining lines if fewer than display count
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_activity))):
                        lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No activity yet)".ljust(term_width))
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - 1)):
                        lines_to_print.append(" ".ljust(term_width))
                lines_to_print.append("-" * term_width)
                lines_to_print.append("(Press Ctrl+C to stop)".center(term_width))

                # --- Screen Update ---
                output_buffer = CURSOR_TO_HOME
                for line in lines_to_print:
                    # Ensure line fits terminal width, clear rest of line
                    output_buffer += line[:term_width] + CLEAR_LINE + "\n"
                output_buffer += CLEAR_SCREEN_FROM_CURSOR  # Clear anything below the output
                sys.stdout.write(output_buffer)
                sys.stdout.flush()

            except Exception as e:
                logger.error(f"Display thread error: {e}", exc_info=False)
                time.sleep(1)  # Avoid spamming errors

            # Wait efficiently using stop event
            if self._stop_event.wait(timeout=UI_UPDATE_INTERVAL):
                break  # Exit loop if stop event set during wait

        # Cleanup terminal on exit
        if self.verbose:
            logger.debug("Realtime display thread finished.")
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
        sys.stdout.flush()

    # --- Resource Scanner Thread ---
    def _resource_scanner_thread(self):
        """Periodically checks for and parses resource files"""
        logger.debug("Resource scanner thread started")
        
        scan_interval = 15  # Seconds between scans
        
        while self.active and not self._stop_event.is_set():
            # Wait before scanning
            if self._stop_event.wait(timeout=scan_interval):
                break
                
            # Scan for and parse resource files
            self._parse_resource_files()
            
        logger.debug("Resource scanner thread finished")

    # --- Start/Stop Methods ---
    def start_test(self):
        if self.active:
            logger.warning("Test already running.")
            return

        logger.info("=" * 30 + " Starting UDP Download Test " + "=" * 30)
        self.active = True
        self._stop_event.clear()
        self.start_time = time.time()
        self.end_time = 0
        
        # --- Reset Counters ---
        self.bytes_received = 0
        self.downloads_completed = 0
        self.downloads_failed = 0
        self.initial_connection_failures = 0
        self.runtime_connection_issues = 0
        self.active_workers_count = 0
        
        # --- Reset Server State ---
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "STARTING"  # Indicate starting state
        self.server_last_seen = 0
        self.server_info = None
        self.server_rules = None
        self.threads = []  # Clear thread list from previous runs (if any)
        self.connections = []  # Clear connection info list
        
        # Prepopulate known maps with common maps
        self.known_maps = ["de_dust2", "de_inferno", "de_nuke", "de_train", "cs_assault", "cs_office"]
        self.discovered_files = []

        # --- Start Monitor Thread (if enabled) ---
        if not self.no_server_monitor:
            # Recreate ServerQuery if it wasn't created or closed previously
            if not self.server_query:
                self.server_query = ServerQuery(self.server_ip, self.server_port, storage_dir=str(self.storage_dir))
            self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
            self.server_info_thread.start()
            self.threads.append(self.server_info_thread)
        else:
            self.server_info_thread = None  # Ensure it's None if disabled

        # --- Start Display Thread ---
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread)
        
        # --- Start Resource Scanner Thread ---
        self.resource_scanner_thread = threading.Thread(target=self._resource_scanner_thread, name="ResScanner", daemon=True)
        self.resource_scanner_thread.start()
        self.threads.append(self.resource_scanner_thread)

        # --- Start Workers ---
        logger.info(f"Starting {self.num_connections} workers...")
        launched_count = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set():
                logger.warning("Stop event received during worker startup.")
                break
            # Create worker structure
            conn_info = {"id": i + 1, "downloader": None, "status": "init", "current_task": "Initializing"}
            self.connections.append(conn_info)  # Add structure before starting thread

            # Start worker thread
            worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
            try:
                worker_thread.start()
                self.threads.append(worker_thread)
                launched_count += 1
                # Slight delay when launching many workers to avoid overwhelming system/network
                if self.num_connections > 20 and (i + 1) % 10 == 0:
                    time.sleep(0.02 * (i // 10))  # Increasingly small delay
                elif self.num_connections > 5:
                    time.sleep(0.01)

            except threading.ThreadError as e:
                logger.error(f"Failed to start worker {i+1}: {e}")
                self._increment_counter("initial_connection_failures")
                # Remove connection info if thread failed to start? Maybe keep for reporting.
                conn_info["status"] = "start_error"
                conn_info["current_task"] = "Start Failed"

        logger.info(f"Launched {launched_count} of {self.num_connections} workers.")
        if launched_count == 0 and self.num_connections > 0:
            logger.error("FATAL: No workers were successfully launched. Stopping test.")
            # Use a separate thread to stop to avoid deadlock if called from main
            threading.Thread(target=self.stop_test, daemon=True).start()
            return

        # --- Main loop waits for duration or stop signal ---
        try:
            if self.continuous_mode:
                logger.info("Running in continuous mode. Press Ctrl+C to stop.")
                self._stop_event.wait()  # Wait indefinitely until stop_test sets the event
                logger.info("Stop event received by main thread.")
            else:
                logger.info(f"Running timed test for {self.test_duration} seconds. Press Ctrl+C to stop early.")
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early:
                    logger.info("Test stopped early by user or signal.")
                else:
                    logger.info("Test duration reached.")
                    # Call stop_test explicitly if duration completed naturally
                    self.stop_test()  # stop_test handles the active/stop_event checks
        except KeyboardInterrupt:
            # This might be caught here if signal handler is slow, or directly by handler
            logger.warning("KeyboardInterrupt caught in main wait loop. Initiating shutdown...")
            if not self._stop_event.is_set():  # Ensure stop is called only once
                threading.Thread(target=self.stop_test, daemon=True).start()
        except Exception as e:
            logger.error(f"Error in main wait loop: {e}", exc_info=self.verbose)
            if not self._stop_event.is_set():  # Ensure stop is called on error
                threading.Thread(target=self.stop_test, daemon=True).start()

    def stop_test(self):
        # Prevent multiple stop calls and stop if not active
        if not self.active or self._stop_event.is_set():
            logger.debug("Stop test called but already stopping or inactive.")
            return

        logger.info("Stopping test...")
        self.active = False         # Signal loops to stop checking work
        self._stop_event.set()      # Signal waits/sleeps to interrupt

        self.end_time = time.time()  # Record end time accurately

        logger.info("Waiting for threads to finish (max 5s)...")
        join_timeout = 5.0
        start_join_time = time.time()

        # Make a copy of the thread list to avoid modification issues if threads exit early
        threads_to_join = self.threads[:]
        self.threads = []  # Clear original list

        for thread in threads_to_join:
            if thread is threading.current_thread() or not thread.is_alive():
                # logger.debug(f"Thread {thread.name} already stopped or is current thread.")
                continue
            try:
                remaining_timeout = max(0.1, join_timeout - (time.time() - start_join_time))
                if self.verbose:
                    logger.debug(f"Joining {thread.name} (timeout {remaining_timeout:.1f}s)...")
                thread.join(remaining_timeout)
                if thread.is_alive():
                    logger.warning(f"Thread {thread.name} did not stop within timeout.")
            except Exception as e:
                logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("Thread processing complete.")

        # --- Close Resources ---
        if self.server_query:
            logger.debug("Closing server query socket...")
            self.server_query.close()
            self.server_query = None  # Clear reference

        # Ensure all worker downloaders are closed
        logger.debug("Closing downloaders...")
        downloaders_closed = 0
        for conn_info in self.connections:
            downloader = conn_info.get("downloader")
            if downloader:
                try:
                    downloader.close()
                    downloaders_closed += 1
                    conn_info["downloader"] = None  # Clear reference
                except Exception:
                    pass  # Ignore errors here
        if downloaders_closed > 0:
            logger.debug(f"Closed {downloaders_closed} downloaders during stop.")

        # --- Final Actions ---
        # Close log file handler AFTER all threads potentially logging have stopped
        self._close_activity_logger()

        # Generate Final Report
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        # Ensure display is cleared before printing final report
        sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
        sys.stdout.flush()
        print("\n")  # Add a newline for separation
        self._generate_final_report(final_elapsed)
        self._save_detailed_report_json(final_elapsed)

        logger.info("Test finished.")

    def _close_activity_logger(self):
        # Find and close the file handler for the activity logger
        logger.debug("Attempting to close activity log file handler...")
        # Use list comprehension to find all file handlers
        file_handlers = [h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)]
        if not file_handlers:
            logger.debug("No active file handler found for activity logger.")
            return

        for handler in file_handlers:
            handler_name = handler.baseFilename if hasattr(handler, 'baseFilename') else str(handler)
            try:
                # Ensure log buffer is flushed before closing
                handler.flush()
                handler.stream.write(f"--- Activity Log Ended ({datetime.now().isoformat()}) ---\n")
                handler.close()
                activity_logger.removeHandler(handler)  # Remove handler to prevent duplicates on restart
                logger.debug(f"Closed and removed activity log handler: {handler_name}")
            except Exception as e:
                logger.warning(f"Error closing activity log handler ({handler_name}): {e}")

    # --- Reporting Methods ---
    def _generate_final_report(self, duration):
        print("\n" + "=" * 30 + " UDP Download Test Results " + "=" * 30)
        duration = max(duration, 0.01)
        # Gather final stats
        with self.lock:
            bytes_recv = self.bytes_received
            downloads_ok = self.downloads_completed
            downloads_fail = self.downloads_failed
            runtime_issues = self.runtime_connection_issues
            initial_fails = self.initial_connection_failures
            final_server_status = self.server_status
            server_log = self.server_status_log[:]
            known_maps_count = len(self.known_maps)
            discovered_files_count = len(self.discovered_files)
            
            # Get final player count etc. if available
            final_map = self.server_info.get('map', 'UNKNOWN') if self.server_info else 'UNKNOWN'
            final_players = self.server_info.get('players', -1) if self.server_info else -1
            final_max_players = self.server_info.get('max_players', -1) if self.server_info else -1

        recv_mb = bytes_recv / (1024 * 1024)
        avg_rate_mbs = (recv_mb * 8) / duration  # Megabits/sec
        avg_rate_MBs = recv_mb / duration  # MegaBytes/sec

        avg_ping = -1
        min_ping = -1
        max_ping = -1
        online_duration = 0
        last_online_time = -1
        if not self.no_server_monitor:
            pings = [log['ping'] for log in server_log if log.get('ping', -1) >= 0]
            if pings:
                avg_ping = sum(pings) / len(pings)
                min_ping = min(pings)
                max_ping = max(pings)
            # Calculate rough online time
            for i, log in enumerate(server_log):
                if log.get('status') == 'ONLINE':
                    if last_online_time < 0:  # Start of online period
                        last_online_time = log['timestamp']
                    # If last entry is online, count duration to end_time
                    if i == len(server_log) - 1:
                        online_duration += (self.end_time - last_online_time)
                else:  # Status is not ONLINE
                    if last_online_time >= 0:  # End of online period
                        online_duration += (log['timestamp'] - last_online_time)
                    last_online_time = -1  # Reset

        print(f"[Test Overview]")
        print(f" Target Server:   {self.server_ip}:{self.server_port}")
        print(f" Duration:        {duration:.2f}s")
        print(f" Config Workers:  {self.num_connections}")
        print(f" Initial Fails:   {initial_fails}")
        print(f" Runtime Issues:  {runtime_issues}")
        print(f" Download Dir:    {self.downloads_dir}")

        print("\n[Download Results]")
        print(f" Files OK:        {downloads_ok}")
        print(f" Files Failed:    {downloads_fail}")
        print(f" Discovered Maps: {known_maps_count}")
        print(f" Resource Files:  {discovered_files_count}")
        print(f" Total Received:  {recv_mb:.2f} MB")
        print(f" Avg Rate:        {avg_rate_mbs:.2f} Mbps ({avg_rate_MBs:.2f} MB/s)")

        print("\n[Server Status (UDP Query)]")
        if self.no_server_monitor:
            print(" Monitoring:      Disabled")
        else:
            print(f" Final Status:    {final_server_status}")
            print(f" Current Map:     {final_map}")
            print(f" Final Players:   {final_players}/{final_max_players}" if final_players >= 0 else "Players: N/A")
            print(f" Avg Ping:        {avg_ping:.1f} ms" if avg_ping != -1 else "Avg Ping: N/A")
            print(f" Ping Min/Max:    {min_ping} / {max_ping} ms" if min_ping != -1 else "Ping Range: N/A")
            print(f" Est. Online:     {online_duration:.1f}s / {duration:.1f}s ({online_duration/duration*100:.1f}%)" if duration > 0 else "Online Time: N/A")

        print("=" * 72)

    def _save_detailed_report_json(self, duration):
        duration = max(0.01, duration)
        with self.lock:
            bytes_recv = self.bytes_received
            downloads_ok = self.downloads_completed
            downloads_fail = self.downloads_failed
            total_recv_bytes = bytes_recv
            total_recv_mb = total_recv_bytes / (1024 * 1024)
            avg_rate_MBs = total_recv_mb / duration
            server_log = self.server_status_log[:]
            final_server_info_snapshot = self.server_info.copy() if self.server_info else None  # Copy last known info
            known_maps = self.known_maps.copy()
            discovered_files = self.discovered_files.copy()

        report_data = {
            "test_info": {
                "test_type": "CS_UDP_Downloader",
                "version": "1.0",
                "target_server": f"{self.server_ip}:{self.server_port}",
                "timestamp_start_utc": datetime.utcfromtimestamp(self.start_time).isoformat() + "Z" if self.start_time else None,
                "timestamp_end_utc": datetime.utcfromtimestamp(self.end_time).isoformat() + "Z" if self.end_time else None,
                "duration_seconds": round(duration, 2),
                "configured_workers": self.num_connections,
                "initial_connection_failures": self.initial_connection_failures,
                "runtime_connection_issues": self.runtime_connection_issues,
                "test_run_mode": "Continuous" if self.continuous_mode else "Timed",
                "server_udp_monitoring": not self.no_server_monitor,
                "verbose_logging": self.verbose,
                "activity_log_file": str(self.activity_log_filepath) if self.activity_log_filepath else None,
                "download_directory": str(self.downloads_dir)
            },
            "bandwidth_summary": {
                "total_received_bytes": total_recv_bytes,
                "total_received_mb": round(total_recv_mb, 3),
                "avg_total_rate_mbs": round((total_recv_bytes * 8) / (1024 * 1024) / duration, 3),  # Mbps
                "avg_total_rate_MBs": round(avg_rate_MBs, 3),  # MB/s
                "bandwidth_log_points_sec_MBs": [(round(t, 2), round(rate, 3)) for t, rate in self.bandwidth_log_points]
            },
            "download_stats": {
                "files_succeeded": downloads_ok,
                "files_failed": downloads_fail,
                "known_maps": known_maps,
                "discovered_files_count": len(discovered_files)
            },
            "server_status_summary": final_server_info_snapshot,
            "server_status_log": server_log
        }

        # Clean None values recursively (optional, makes JSON cleaner)
        def remove_none_values(d):
            if isinstance(d, dict):
                return {k: remove_none_values(v) for k, v in d.items() if v is not None}
            elif isinstance(d, list):
                return [remove_none_values(item) for item in d if item is not None]
            else:
                return d
                
        report_data = remove_none_values(report_data)

        # Use Path object for report path
        ts = int(time.time())
        report_filename = f"cs_udp_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts}.json"
        report_filepath = self.storage_dir / report_filename
        try:
            with open(report_filepath, 'w', encoding='utf-8') as f:  # Specify encoding
                json.dump(report_data, f, indent=2, ensure_ascii=False)  # Use ensure_ascii=False for non-latin chars in names etc.
            logger.info(f"Detailed JSON report saved to: {report_filepath}")
        except Exception as e:
            logger.error(f"Failed to save JSON report '{report_filepath}': {e}")

# ==============================================================
# Signal Handling
# ==============================================================
def signal_handler(sig, frame):
    global tester_instance
    signal_name = signal.Signals(sig).name
    # Check if stop already in progress to avoid multiple messages/calls
    if tester_instance and tester_instance.active and not tester_instance._stop_event.is_set():
        print('\n')  # Print newline before log message
        logger.warning(f"{signal_name} received! Initiating graceful shutdown...")
        # Run stop_test in a separate thread to avoid blocking the signal handler
        threading.Thread(target=tester_instance.stop_test, daemon=True).start()
    elif tester_instance and tester_instance._stop_event.is_set():
        logger.info(f"{signal_name} received, but shutdown already in progress.")
    else:
        # If tester isn't active or doesn't exist, exit more directly
        print(f'\n{signal_name} received, exiting immediately.')
        # Attempt to close log file even if tester not fully active/created
        handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
        if handler:
            try:
                handler.close()
            except Exception:
                pass
        sys.exit(0)  # Exit directly

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 UDP File Downloader and Bandwidth Test Tool.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    # --- Server Args ---
    parser.add_argument("server_ip", help="IP address or hostname of the CS 1.6 GAME server.")
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="GAME server UDP port.")
    # --- Test Control Args ---
    parser.add_argument("-c", "--connections", type=int, default=5, help="Number of concurrent workers/connections.")
    parser.add_argument("-d", "--duration", type=int, default=60, help="Duration of timed test in seconds (ignored if --continuous is set).")
    parser.add_argument("-cont", "--continuous", action="store_true", help="Run continuously until stopped (Ctrl+C). Overrides --duration.")
    # --- Output & Logging Args ---
    output_group = parser.add_argument_group('Output and Logging')
    output_group.add_argument("--storage-dir", default="cs_udp_downloads", help="Directory for logs, reports, and downloaded files.")
    output_group.add_argument("--activity-log", default=ACTIVITY_LOG_FILENAME, help="Filename within storage-dir for logging detailed activity.")
    output_group.add_argument("-v", "--verbose", action="store_true", help="Enable verbose debug logging to console and activity log.")
    output_group.add_argument("--no-server-monitor", action="store_true", help="Disable querying game server status (info/rules/ping) via UDP.")

    args = parser.parse_args()

    # --- Configure Logging Level ---
    log_level = logging.DEBUG if args.verbose else logging.INFO
    logger.setLevel(log_level)
    # Set activity logger level - it should log everything up to its level regardless of main logger
    activity_logger.setLevel(logging.DEBUG if args.verbose else logging.INFO)
    # Ensure the basicConfig handler respects the logger level
    for handler in logging.getLogger().handlers:  # Get root logger handlers
        if isinstance(handler, logging.StreamHandler):  # Find the console handler
            handler.setLevel(log_level)

    # --- Display Warnings & Info ---
    logger.warning("=" * 70)
    logger.warning("⚠️ UDP DOWNLOAD MODE WILL DOWNLOAD REAL FILES FROM THE SERVER.")
    logger.warning("⚠️ This will generate ACTUAL network traffic through the UDP game port.")
    if args.no_server_monitor:
        logger.warning("⚠️ Server UDP monitoring DISABLED. Ping/Map/Player info unavailable.")
    logger.warning("Ensure you have permission before testing ANY server. Use responsibly.")
    logger.warning("=" * 70)
    time.sleep(1.5)  # Pause for user to read warnings

    # --- Initialize and Run Tester ---
    try:
        tester_instance = CS16BandwidthTester(
            server_ip=args.server_ip, server_port=args.port,
            num_connections=args.connections,
            test_duration=args.duration,
            verbose=args.verbose,
            storage_dir=args.storage_dir,
            continuous_mode=args.continuous,
            no_server_monitor=args.no_server_monitor,
            # Logging
            activity_log_filename=args.activity_log
        )

        # Register signal handlers AFTER tester_instance is created
        signal.signal(signal.SIGINT, signal_handler)   # Ctrl+C
        signal.signal(signal.SIGTERM, signal_handler)  # Kill/Terminate signal
        # On Windows, SIGBREAK might be relevant too, but less common
        if sys.platform == "win32":
            signal.signal(signal.SIGBREAK, signal_handler)

        tester_instance.start_test()
        # Main thread will block in start_test() until test completes or is stopped

        logger.info("Main thread finished execution.")
        sys.exit(0)  # Explicit exit code 0 on normal completion

    except ValueError as e:
        logger.error(f"Configuration Error: {e}")
        sys.exit(1)
    except PermissionError as e:
        logger.error(f"Permission Error: {e}. Check permissions for storage directory: {args.storage_dir}")
        sys.exit(1)
    except Exception as e:
        logger.error(f"A critical error occurred in the main block: {e}", exc_info=True)
        sys.exit(1)
    finally:
        # Final attempt to close log file handler, e.g., if initialization failed after handler creation
        if 'tester_instance' not in locals() or not tester_instance or not tester_instance.active:
            handler = next((h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)), None)
            if handler:
                try:
                    handler.close()
                except Exception:
                    pass
