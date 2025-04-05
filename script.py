#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Enhanced CS16 UDP Downloader & Network Stress Tester

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
import requests # Although imported, seems unused in the final combined script logic. Keep for now.
from urllib.parse import urljoin, unquote # Although imported, seems unused in the final combined script logic. Keep for now.
from pathlib import Path

# --- Constants ---
DEFAULT_PORT = 27015
HIGH_PING_THRESHOLD = 150  # ms
SERVER_OFFLINE_TIMEOUT = 15  # seconds without response
LAST_FILES_DISPLAY_COUNT = 10  # How many recent events to show
UI_UPDATE_INTERVAL = 0.5  # How often to refresh the terminal stats (seconds)

# Terminal control sequences
CURSOR_TO_HOME = "\033[H"
CLEAR_LINE = "\033[K"
CLEAR_SCREEN_FROM_CURSOR = "\033[J"

# UDP protocol constants
HEADER = b"\xFF\xFF\xFF\xFF"
A2S_INFO = b"TSource Engine Query\x00"  # Modern A2S_INFO query
A2S_PING = b"ping\x00"  # Simple ping query
A2S_RULES = b"rules\x00"  # Rules query (partially used, actual request uses 'V')
PING_RESPONSE_PREFIX = b"\xFF\xFF\xFF\xFFj"  # Common ping response prefix

# Download protocol variants
REQUEST_FILE_CMD = b"requestfile"  # Main command for requesting files
REQUEST_FILE_CMD_ALT1 = b"getfile"  # Alternative command used by some servers
REQUEST_FILE_CMD_ALT2 = b"download"  # Another alternative
FRAGMENT_SIZE = 1024  # Max UDP fragment size to request/expect
DOWNLOAD_TIMEOUT = 15  # Timeout for a single file download (seconds)
MAX_RETRIES = 5  # Max retries for a single fragment (used conceptually in download logic)

# File types that can be downloaded (used for generating guesses)
FILE_TYPES = [
    "maps/*.bsp",
    "models/*.mdl",
    "sound/*.wav",
    "sprites/*.spr",
    "media/*.mp3", # Less common via UDP?
    "materials/*.vmt", # Often FastDL
    "materials/*.vtf"  # Often FastDL
]

# Common file prefixes for maps (used for generating guesses)
MAP_PREFIXES = ["de_", "cs_", "as_", "fy_", "ka_", "aim_", "awp_", "he_", "zm_", "35hp_", "gg_", "jail_", "jb_", "hns_", "surf_", "kz_", "bhop_"]

# Log/Temp file config
ACTIVITY_LOG_FILENAME = "activity_log.txt"
DOWNLOAD_LOG_FILENAME = "download_debug.txt"
UDP_VERIFY_FILENAME_PREFIX = "udp_verify_"

# --- Global logger setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr # Log INFO and above to stderr by default
)
logger = logging.getLogger('cs_udp_tester')

# --- Activity Logger Setup (File logging) ---
activity_logger = logging.getLogger('activity_logger')
activity_logger.setLevel(logging.INFO) # Will log INFO and above to file
activity_logger.propagate = False  # Don't send activity logs to the main stderr handler

# --- Download Debug Logger (Separate file) ---
download_logger = logging.getLogger('download_logger')
download_logger.setLevel(logging.DEBUG) # Will log DEBUG and above for downloads to file
download_logger.propagate = False  # Don't send download logs to the main stderr handler

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
        self.retry_count = 2 # Number of times to retry a query on timeout
        self.timeout = 1.5 # Socket timeout in seconds
        self.last_challenge = None # Store the last challenge number received

    def _create_socket(self):
        """Creates or recreates the UDP socket."""
        if self.sock is not None:
            try:
                self.sock.close()
            except Exception:
                pass # Ignore errors closing old socket
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.settimeout(self.timeout)
        except Exception as e:
            logger.error(f"Query Socket Create Error: {e}")
            self.sock = None
            raise # Re-raise the exception

    def _log_activity(self, level, message):
        """Helper to log to both main logger and activity file logger if enabled."""
        # Log to main logger (console/stderr) based on its configured level
        logger.log(level, message)
        # Log to activity file logger if it's configured and level is appropriate
        if activity_logger.hasHandlers() and not isinstance(activity_logger.handlers[0], logging.NullHandler):
            # activity_logger has its own level, check if message level is sufficient
            if level >= activity_logger.level:
                 activity_logger.log(level, message)
        elif level >= logging.WARNING:  # Log errors/warnings to main log if file log isn't working
            logger.log(level, f"[Activity Log Disabled] {message}")

    def _send_recv(self, request, query_type="unknown", save_response=True):
        """Sends a UDP request, waits for response, optionally saves/verifies/deletes it."""
        if self.sock is None:
            try:
                self._create_socket()
            except Exception:
                return None, 0 # Return failure if socket can't be created

        start_time = time.time()
        response = None
        ping = 0
        for attempt in range(self.retry_count):
            try:
                logger.debug(f"Sending UDP {query_type} query (attempt {attempt+1})...")
                self.sock.sendto(request, (self.server_ip, self.server_port))
                response, addr = self.sock.recvfrom(4096) # Buffer size for response
                end_time = time.time()
                ping = int((end_time - start_time) * 1000) # Calculate ping in ms

                if response:
                    logger.debug(f"UDP response received from {addr} for {query_type} ({len(response)} bytes).")
                    # --- UDP Verification: Save and Delete ---
                    if save_response:
                        # Define a temporary subdirectory for these verification files
                        verify_storage_dir = Path(self.storage_dir) / "udp_verify_temp"
                        try:
                            # Create the directory if it doesn't exist
                            verify_storage_dir.mkdir(parents=True, exist_ok=True)
                        except OSError as e:
                            logger.error(f"Failed to create UDP verification dir '{verify_storage_dir}': {e}. Skipping verification.")
                            # Continue without verification if directory creation fails
                        else:
                            # Create a unique filename for the verification file
                            verify_filename = f"{UDP_VERIFY_FILENAME_PREFIX}{query_type}_{int(time.time()*1000)}_{random.randint(100,999)}.bin"
                            verify_filepath = verify_storage_dir / verify_filename
                            saved_ok = False
                            verify_msg_prefix = f"[UDP Verify] Query: {query_type}"
                            try:
                                # Write the received response to the file
                                with open(verify_filepath, 'wb') as vf:
                                    vf.write(response)
                                saved_ok = True
                                # Log save success only at DEBUG level
                                self._log_activity(logging.DEBUG, f"{verify_msg_prefix} | Status: SAVED | Bytes: {len(response)} | Path: {verify_filepath}")
                            except Exception as e:
                                self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: SAVE_FAILED | Path: {verify_filepath} | Error: {e}")
                            finally:
                                # Attempt to delete the file whether save succeeded or failed, if it exists
                                if verify_filepath.exists():
                                    try:
                                        os.remove(verify_filepath)  # Use os.remove for file deletion
                                        if saved_ok:
                                            self._log_activity(logging.DEBUG, f"{verify_msg_prefix} | Status: DELETED | Path: {verify_filepath}")
                                    except Exception as e:
                                        self._log_activity(logging.ERROR, f"{verify_msg_prefix} | Status: DELETE_FAILED | Path: {verify_filepath} | Error: {e}")
                                elif saved_ok:
                                    # This case should ideally not happen if save succeeded
                                    self._log_activity(logging.WARNING, f"{verify_msg_prefix} | Status: DELETE_WARN | Path: {verify_filepath} | File not found after successful save.")
                    # --- End UDP Verification ---
                    return response, ping # Return the received response and ping time
                else:
                    logger.debug(f"Received empty UDP response (attempt {attempt+1}) for {query_type}")
                    # An empty response is treated like a timeout for retry purposes

            except socket.timeout:
                logger.debug(f"UDP {query_type} query timed out (attempt {attempt+1})")
                if attempt == self.retry_count - 1:
                    return None, 0 # Return failure after last retry
                time.sleep(0.1) # Short delay before retrying
            except OSError as e:
                # Handle specific OS-level network errors (e.g., network unreachable)
                logger.warning(f"UDP Query OSError (attempt {attempt+1}) on {query_type}: {e}")
                self.close() # Close the potentially broken socket
                return None, 0 # Return failure
            except Exception as e:
                # Catch any other unexpected errors during send/receive
                logger.error(f"Unexpected UDP Query Error (attempt {attempt+1}) on {query_type}: {e}")
                self.close() # Close the socket on unexpected errors
                return None, 0 # Return failure

        return None, 0 # Should not be reached if retry logic is correct, but acts as a fallback

    # --- Simple UDP Ping ---
    def ping(self):
        """Send a simple A2S_PING request and measure response time"""
        request = HEADER + A2S_PING
        # Don't save the ping response for verification, it's too simple/common
        response, ping_time = self._send_recv(request, query_type="ping", save_response=False)
        if response:
            # Check if the response starts with the expected prefix for a ping reply
            if response.startswith(PING_RESPONSE_PREFIX):
                return ping_time # Return ping time in ms
        return -1 # Return -1 if ping failed or response was invalid

    # --- Getters using _send_recv ---
    def get_info(self):
        """Requests and parses server information (A2S_INFO)."""
        request = HEADER + A2S_INFO
        response, ping = self._send_recv(request, query_type="info")
        if response:
            parsed_info = self._parse_info(response)
            if parsed_info:
                # Successfully parsed info
                self.last_ping = ping
                parsed_info['ping'] = ping # Add ping to the parsed info dict
                self.last_info = parsed_info
                # Check if the response is actually a challenge response (type 'A')
                # Some servers might send a challenge first even for an info request.
                if len(response) >= 9 and response[4:5] == b'A':
                    self.last_challenge = response[5:9] # Store the challenge number
                    logger.debug(f"Received challenge {self.last_challenge.hex()} instead of info. Need challenge for rules/players.")
                    return None # Indicate info wasn't received, only challenge
                else:
                     # If not a challenge response, clear any old challenge
                     self.last_challenge = None
                return parsed_info
            # Handle case where the response was *only* a challenge
            elif response[4:5] == b'A' and len(response) >= 9:
                self.last_challenge = response[5:9]
                logger.debug(f"Received challenge {self.last_challenge.hex()} when requesting info. Retrying info might be needed.")
                return None # Return None as info wasn't actually parsed
        # If response was None (query failed)
        return None

    def get_rules(self):
        """Requests and parses server rules (A2S_RULES). Requires challenge."""
        # Use the last received challenge, or a default challenge value if none known
        challenge_bytes = self.last_challenge or b'\xFF\xFF\xFF\xFF'
        request = HEADER + b'V' + challenge_bytes # A2S_RULES ('V') request requires challenge
        response, _ = self._send_recv(request, query_type="rules")

        if response and response[4:5] == b'E': # 'E' indicates a rules response
            parsed_rules = self._parse_rules(response)
            if parsed_rules:
                self.last_rules = parsed_rules
            return parsed_rules # Return parsed rules dict or None if parsing failed
        elif response and response[4:5] == b'A':  # Received a challenge response instead of rules
            self.last_challenge = response[5:9] # Update the challenge number
            logger.info(f"Received challenge {self.last_challenge.hex()} for rules. Retrying with new challenge.")
            # Retry the rules request immediately with the new challenge
            request = HEADER + b'V' + self.last_challenge
            response, _ = self._send_recv(request, query_type="rules_retry")
            if response and response[4:5] == b'E': # Check if the retry got the rules response
                parsed_rules = self._parse_rules(response)
                if parsed_rules:
                    self.last_rules = parsed_rules
                return parsed_rules
        # Handle case where initial query failed, but we *might* have a challenge from get_info
        elif not response and self.last_challenge:
            logger.debug("Rules query failed, but retrying with previously known challenge.")
            request = HEADER + b'V' + self.last_challenge
            response, _ = self._send_recv(request, query_type="rules_retry_known_challenge")
            if response and response[4:5] == b'E':
                parsed_rules = self._parse_rules(response)
                if parsed_rules:
                    self.last_rules = parsed_rules
                return parsed_rules
        # If all attempts fail or responses are invalid
        return None

    def get_players(self):
        """Requests and parses player information (A2S_PLAYER). Requires challenge."""
        challenge_bytes = self.last_challenge or b'\xFF\xFF\xFF\xFF'
        request = HEADER + b'U' + challenge_bytes # A2S_PLAYER ('U') request
        response, _ = self._send_recv(request, query_type="players")

        # Handle challenge response - update challenge and retry
        if response and response[4:5] == b'A':
            self.last_challenge = response[5:9]
            logger.info(f"Received challenge {self.last_challenge.hex()} for players. Retrying.")
            request = HEADER + b'U' + self.last_challenge
            response, _ = self._send_recv(request, query_type="players_retry")

        if response and response[4:5] == b'D': # 'D' indicates player response
            try:
                offset = 5  # Skip header (4 bytes) and command byte ('D')
                # Read the number of players (1 byte)
                num_players = response[offset]
                offset += 1
                players = [] # List to store player names

                for _ in range(num_players):
                    # Skip player index byte (1 byte)
                    offset += 1

                    # Read null-terminated player name
                    name_end = response.find(b'\x00', offset)
                    if name_end == -1:
                        logger.warning("Malformed player data: missing null terminator for name.")
                        break # Stop parsing if data seems corrupt
                    # Decode name using utf-8, ignore errors
                    name = response[offset:name_end].decode('utf-8', errors='ignore')
                    offset = name_end + 1 # Move offset past the name and null terminator

                    # Skip score/frags (4 bytes signed long) and duration (4 bytes float)
                    offset += 8

                    players.append(name)

                    # Basic check to prevent infinite loops if data is highly corrupt
                    if offset >= len(response) and _ < num_players - 1:
                         logger.warning("Malformed player data: offset reached end prematurely.")
                         break

                return players # Return the list of player names
            except IndexError:
                 logger.error("Error parsing player response: Index out of bounds. Response likely truncated.")
            except Exception as e:
                logger.error(f"Error parsing player response: {e}")

        return [] # Return empty list if query failed or parsing error occurred

    # --- Parsers (_parse_info, _parse_rules) ---
    def _parse_info(self, response):
        """Parses the A2S_INFO response payload."""
        try:
            # Basic validation: must start with standard header
            if not response or response[:4] != b'\xFF\xFF\xFF\xFF':
                logger.warning("Parse INFO failed: Invalid header.")
                return None

            header_byte = response[4:5] # Get the response type indicator
            offset = 5 # Start reading after the header

            # --- Helper function to read null-terminated strings ---
            def read_string(data, start_offset):
                end = data.find(b'\x00', start_offset)
                if end == -1:
                    raise ValueError("Malformed string (null terminator missing)")
                # Decode using utf-8, replace errors to avoid crashes on weird server names
                return data[start_offset:end].decode('utf-8', errors='replace'), end + 1

            # --- Parse based on response type ---
            if header_byte == b'I':  # Source Engine / GoldSrc (Newer format) Response Header 'I'
                # Protocol version byte (often ignored or unreliable)
                # offset += 1 # Skipping protocol version byte

                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)

                # Structure after strings can vary slightly
                # Check remaining length to determine structure
                # Common structure (Source-like): AppID(2), Players(1), MaxPlayers(1), Bots(1), ServerType(1), OS(1), Password(1), VAC(1) [Optional EDF]
                if offset + 9 <= len(response): # Enough bytes for typical Source fields
                    offset += 2  # Skip AppID (short)
                    player_count = response[offset]
                    offset += 1
                    max_players = response[offset]
                    offset += 1
                    bot_count = response[offset]
                    offset += 1
                    # Optional: could parse server_type, environment, visibility, vac etc. if needed
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': player_count, 'max_players': max_players, 'bots': bot_count}
                # Simpler structure (GoldSrc-like, maybe missing bots/other fields): Players(1), MaxPlayers(1)
                elif offset + 2 <= len(response): # Enough bytes for player counts
                    player_count = response[offset]
                    offset += 1
                    max_players = response[offset]
                    offset += 1
                    # Assume 0 bots if the field isn't present
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': player_count, 'max_players': max_players, 'bots': 0}
                else:
                    # Response is too short after reading strings
                    logger.warning(f"Info response possibly truncated after strings. Len: {len(response)}, Offset: {offset}")
                    # Return what we have, default counts to 0
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': 0, 'max_players': 0, 'bots': 0}

            elif header_byte == b'm':  # Older GoldSrc Response Header 'm' (less common now)
                # This format includes the server address string first
                server_address, offset = read_string(response, offset) # Read and discard address

                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)
                # Expect player count and max players bytes after strings
                if offset + 2 > len(response):
                    raise ValueError("Response too short for player counts in older GoldSrc format")
                player_count = response[offset]
                offset += 1
                max_players = response[offset]
                # Assume 0 bots for this older format
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': 0}
            elif header_byte == b'A':
                # This means we received a challenge response when expecting info
                logger.debug("Received A2S_CHALLENGE response when expecting A2S_INFO.")
                # This isn't an error, but it's not the info we wanted. Need to handle challenge logic upstream.
                return None
            else:
                logger.warning(f"Unknown A2S_INFO response header byte: {header_byte.hex()}")
                return None
        except ValueError as e:
            # Errors likely due to malformed strings (missing null terminators)
            logger.warning(f"Parse INFO ValueError: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except IndexError as e:
            # Errors likely due to response being shorter than expected based on format rules
            logger.warning(f"Parse INFO IndexError: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except Exception as e:
            # Catch any other unexpected parsing errors
            logger.error(f"Unexpected Parse INFO error: {e}", exc_info=True) # Log full traceback for unexpected errors
            return None

    def _parse_rules(self, response):
        """Parses the A2S_RULES response payload."""
        try:
            # Basic validation: header 'E' and minimum length
            if not response or len(response) < 7 or response[:5] != b'\xFF\xFF\xFF\xFFE':
                logger.warning("Parse RULES failed: Invalid header or too short.")
                return None

            # Number of rules (short little-endian)
            rules_count = int.from_bytes(response[5:7], 'little')
            offset = 7 # Start reading after rule count
            rules = {} # Dictionary to store rule_name: rule_value

            for i in range(rules_count):
                # Read null-terminated rule name
                name_end = response.find(b'\x00', offset)
                if name_end == -1:
                    raise ValueError(f"Malformed rule name (rule {i+1}/{rules_count}) - missing null terminator")
                # Decode name, replace errors
                rule_name = response[offset:name_end].decode('utf-8', errors='replace')
                offset = name_end + 1 # Move past name and null terminator

                # Read null-terminated rule value
                value_end = response.find(b'\x00', offset)
                if value_end == -1:
                     raise ValueError(f"Malformed rule value for '{rule_name}' (rule {i+1}/{rules_count}) - missing null terminator")
                # Decode value, replace errors
                rule_value = response[offset:value_end].decode('utf-8', errors='replace')
                offset = value_end + 1 # Move past value and null terminator

                rules[rule_name] = rule_value # Add rule to dictionary

                # Check if we've somehow read past the end of the response buffer
                # This can happen with corrupt data where null terminators are missing or rules_count is wrong
                if offset > len(response):
                    if i < rules_count - 1: # Only warn if it wasn't the very last rule expected
                        logger.warning(f"Rule parsing stopped early due to offset exceeding response length after rule '{rule_name}'")
                    break # Stop parsing to prevent further errors

            # Check if the number of parsed rules matches the count header
            if len(rules) != rules_count:
                logger.warning(f"Expected {rules_count} rules according to header, but parsed {len(rules)}. Response might be truncated or malformed.")

            return rules # Return the dictionary of parsed rules
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
        """Closes the UDP socket if it's open."""
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass # Ignore errors on close
            self.sock = None
            logger.debug("ServerQuery socket closed.")

# ==============================================================
# UDP File Download Class - Core functionality for actual downloads
# ==============================================================
class UDPFileDownloader:
    def __init__(self, server_ip, server_port, save_dir):
        self.server_ip = server_ip
        self.server_port = server_port
        self.save_dir = Path(save_dir) # Use pathlib for directory handling
        self.sock = None
        self.timeout = 5.0  # Socket timeout for receiving fragments
        self.current_file = None # Path of the file being downloaded
        self.bytes_received = 0 # Bytes received for the current file
        self.fragment_size = FRAGMENT_SIZE # Expected size of fragments (may vary)

    def _create_socket(self):
        """Create or recreate the UDP socket for downloading."""
        if self.sock:
            try:
                self.sock.close()
            except:
                pass

        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.settimeout(self.timeout)
        return self.sock

    def hexdump(self, data, length=16):
        """Helper function to create a readable hexdump string for debugging."""
        result = []
        for i in range(0, len(data), length):
            chunk = data[i:i+length]
            hex_part = ' '.join(f'{b:02x}' for b in chunk)
            ascii_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            result.append(f"{i:04x}: {hex_part:<{length*3}} {ascii_part}")
        return '\n'.join(result)

    def download_file(self, file_path):
        """Attempts to download a single file from the server using CS1.6 UDP protocol."""
        # Log start using the dedicated download logger
        download_logger.info(f"=== Starting download attempt for: {file_path} ===")

        # Ensure socket exists
        if not self.sock:
            try:
                self._create_socket()
            except Exception as e:
                download_logger.error(f"Socket creation failed: {e}")
                logger.error(f"Socket creation failed for download worker: {e}") # Also log to main logger
                return False, 0 # Return failure

        # Basic validation of the file path argument
        if not file_path or not isinstance(file_path, str):
            download_logger.error(f"Invalid file path provided: {file_path}")
            logger.error(f"Invalid file path provided for download: {file_path}")
            return False, 0

        self.current_file = file_path
        self.bytes_received = 0 # Reset bytes counter for this file

        # Prepare the save path and ensure parent directories exist
        try:
            # Construct the full path where the file will be saved
            save_path = self.save_dir / Path(file_path.lstrip('/\\')) # Ensure relative path
            save_path.parent.mkdir(parents=True, exist_ok=True) # Create directories if needed
        except Exception as e:
            download_logger.error(f"Failed to create directory structure for {save_path}: {e}")
            logger.error(f"Failed to create directory for {file_path}: {e}")
            return False, 0

        # Normalize file path for logging consistency (use forward slashes)
        file_id = file_path.replace('\\', '/')
        download_logger.debug(f"Normalized File ID: {file_id}, Save Path: {save_path}")

        try:
            # --- Prepare potential request commands ---
            file_path_bytes = file_path.encode('utf-8')
            request_primary = HEADER + REQUEST_FILE_CMD + b" " + file_path_bytes + b"\x00"
            request_alt1 = HEADER + REQUEST_FILE_CMD_ALT1 + b" " + file_path_bytes + b"\x00"
            request_alt2 = HEADER + REQUEST_FILE_CMD_ALT2 + b" " + file_path_bytes + b"\x00"
            # Some servers might respond to just the path without a command prefix
            request_alt3 = HEADER + file_path_bytes + b"\x00"

            # Log the request packets being prepared (debug level)
            download_logger.debug(f"Primary Request ({REQUEST_FILE_CMD}): {request_primary[:64]}...")
            download_logger.debug(f"Alt Request 1 ({REQUEST_FILE_CMD_ALT1}): {request_alt1[:64]}...")
            download_logger.debug(f"Alt Request 2 ({REQUEST_FILE_CMD_ALT2}): {request_alt2[:64]}...")
            download_logger.debug(f"Alt Request 3 (Direct Path): {request_alt3[:64]}...")

            logger.info(f"Requesting file: {file_id}") # Log to main console
            download_logger.info(f"Requesting file: {file_id}") # Log to download debug file
            start_time = time.time()

            # Send the primary request command first
            download_logger.debug(f"Sending primary request command: {REQUEST_FILE_CMD.decode()}")
            try:
                bytes_sent = self.sock.sendto(request_primary, (self.server_ip, self.server_port))
                download_logger.debug(f"Sent {bytes_sent} bytes to {self.server_ip}:{self.server_port}")
            except socket.error as e:
                 download_logger.error(f"Socket error sending initial request: {e}")
                 logger.error(f"Socket error sending initial request for {file_id}: {e}")
                 return False, 0

            # --- Download Loop State ---
            response_received = False # Flag if any response packet has been received
            # Time after which we start trying alternative request commands if no response
            alt_request_retry_time = time.time() + 2.0
            request_attempt = 0 # Tracks which request command we are currently using (0=primary, 1=alt1, etc.)
            current_request_cmd_bytes = REQUEST_FILE_CMD # Store the command bytes of the current request format

            fragments = {} # Dictionary to store received fragments {fragment_number: data}
            total_fragments_expected = 0 # Total number of fragments server indicated (if any)
            file_size_reported = 0 # Total file size reported by server (if any)
            last_fragment_received_time = time.time() # Track time of last received fragment for timeout
            download_complete = False # Flag set when all expected fragments are received

            received_packets_log = [] # For debugging, store snippets of received packets
            total_packets_received_count = 0 # Counter for all received UDP packets for this file

            # --- Main Download Loop ---
            # Continue while the timeout hasn't been reached and download isn't complete
            while time.time() - last_fragment_received_time < DOWNLOAD_TIMEOUT and not download_complete:
                try:
                    # Wait for data from the server
                    # Buffer size slightly larger than fragment size to accommodate headers
                    data, addr = self.sock.recvfrom(self.fragment_size + 256)

                    # Check if we received any data
                    if not data:
                        download_logger.debug("Received empty packet, ignoring.")
                        continue # Skip processing if packet is empty

                    # Process received packet
                    total_packets_received_count += 1
                    response_received = True # Mark that we have received something
                    last_fragment_received_time = time.time() # Reset timeout timer

                    # Log received packet details (debug level)
                    download_logger.debug(f"Recv Packet #{total_packets_received_count}: {len(data)} bytes from {addr}")
                    # Log hexdump only if verbose logging is very high (or specifically enabled)
                    # download_logger.debug(f"Hexdump: {self.hexdump(data[:min(64, len(data))])}")
                    if total_packets_received_count <= 5: # Log first few packet snippets for easier debugging
                         received_packets_log.append(data[:64])

                    # --- Packet Parsing ---
                    # Check for standard UDP header
                    if data.startswith(HEADER):
                        offset = 4 # Start parsing after the header

                        # Identify response type byte if present
                        if len(data) > offset:
                            response_type_byte = data[offset:offset+1]
                            download_logger.debug(f"Response Type Byte: 0x{response_type_byte.hex()}")
                            offset += 1

                            # --- Handle File Fragment Response ('R' or sometimes implicitly) ---
                            # The actual response type for fragments can vary or be missing.
                            # We primarily look for the structure (size, fragment num, data).
                            # Assume it's fragment data if structure looks right.
                            is_likely_fragment = False
                            parsed_fragment_num = -1
                            fragment_data = b''

                            # Try parsing common fragment structure: Filesize(4), FragNum(4), Data(...)
                            # Note: Some implementations use 2 bytes for fragment number. Be flexible.
                            try:
                                if len(data) >= offset + 8: # Potential Filesize + FragNum (4+4)
                                    potential_filesize = struct.unpack('<I', data[offset:offset+4])[0]
                                    potential_fragnum = struct.unpack('<I', data[offset+4:offset+8])[0]
                                    if potential_filesize >= 0 and potential_fragnum >= 0:
                                        # Looks plausible
                                        if file_size_reported == 0 and potential_filesize > 0:
                                             file_size_reported = potential_filesize
                                             download_logger.info(f"File size reported by server: {file_size_reported} bytes")
                                             # Estimate total fragments if not known
                                             if total_fragments_expected == 0:
                                                  total_fragments_expected = (file_size_reported + self.fragment_size - 1) // self.fragment_size
                                                  download_logger.info(f"Estimated total fragments: {total_fragments_expected}")

                                        parsed_fragment_num = potential_fragnum
                                        fragment_data = data[offset+8:]
                                        is_likely_fragment = True
                                        download_logger.debug(f"Parsed fragment (4+4 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")

                                elif len(data) >= offset + 6: # Potential Filesize + FragNum (4+2)
                                    potential_filesize = struct.unpack('<I', data[offset:offset+4])[0]
                                    potential_fragnum = struct.unpack('<H', data[offset+4:offset+6])[0] # 2 bytes for frag num
                                    if potential_filesize >= 0 and potential_fragnum >= 0:
                                         if file_size_reported == 0 and potential_filesize > 0:
                                             file_size_reported = potential_filesize
                                             download_logger.info(f"File size reported by server: {file_size_reported} bytes")
                                             if total_fragments_expected == 0:
                                                  total_fragments_expected = (file_size_reported + self.fragment_size - 1) // self.fragment_size
                                                  download_logger.info(f"Estimated total fragments: {total_fragments_expected}")

                                         parsed_fragment_num = potential_fragnum
                                         fragment_data = data[offset+6:]
                                         is_likely_fragment = True
                                         download_logger.debug(f"Parsed fragment (4+2 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")

                                # Fallback: maybe no size, just fragment number (4 bytes)
                                elif len(data) >= offset + 4:
                                     potential_fragnum = struct.unpack('<I', data[offset:offset+4])[0]
                                     if potential_fragnum >= 0:
                                         parsed_fragment_num = potential_fragnum
                                         fragment_data = data[offset+4:]
                                         is_likely_fragment = True
                                         download_logger.debug(f"Parsed fragment (0+4 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")

                                # Fallback: maybe no size, just fragment number (2 bytes)
                                elif len(data) >= offset + 2:
                                     potential_fragnum = struct.unpack('<H', data[offset:offset+2])[0]
                                     if potential_fragnum >= 0:
                                         parsed_fragment_num = potential_fragnum
                                         fragment_data = data[offset+2:]
                                         is_likely_fragment = True
                                         download_logger.debug(f"Parsed fragment (0+2 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")

                                # Simplest case: Assume all data after header+type is fragment 0 if no structure matches
                                else:
                                    # Check if it's NOT an error response first
                                    if response_type_byte != b'E':
                                        parsed_fragment_num = 0 # Assume fragment 0 for simple responses
                                        fragment_data = data[offset:]
                                        is_likely_fragment = True
                                        # If file size wasn't reported, guess based on this fragment
                                        if file_size_reported == 0 and len(fragment_data) < self.fragment_size:
                                            file_size_reported = len(fragment_data)
                                            total_fragments_expected = 1
                                            download_logger.info(f"Assuming single fragment download, size: {file_size_reported} bytes")
                                        elif file_size_reported == 0:
                                            # Cannot determine size or fragments yet
                                             download_logger.debug(f"Received potential fragment 0, size={len(fragment_data)}, but total size unknown.")
                                        else:
                                             download_logger.debug(f"Parsed simple fragment (assumed 0): Size={len(fragment_data)} bytes")

                            except struct.error as unpack_error:
                                download_logger.warning(f"Struct unpack error during fragment parsing: {unpack_error}. Data might be corrupt.")
                                is_likely_fragment = False # Treat as non-fragment if parsing fails

                            # --- Store Fragment and Check Completion ---
                            if is_likely_fragment and parsed_fragment_num >= 0:
                                if parsed_fragment_num not in fragments:
                                    fragments[parsed_fragment_num] = fragment_data
                                    self.bytes_received += len(fragment_data) # Update total bytes received for this file
                                    download_logger.debug(f"Stored fragment {parsed_fragment_num}. Total fragments stored: {len(fragments)}")
                                else:
                                    # Received duplicate fragment
                                    download_logger.debug(f"Received duplicate fragment {parsed_fragment_num}. Ignored.")

                                # Check if download is complete
                                # Completion requires knowing the total fragments *and* having received them all
                                if total_fragments_expected > 0 and len(fragments) == total_fragments_expected:
                                    download_complete = True
                                    download_logger.info(f"All {total_fragments_expected} expected fragments received.")
                                # Also consider complete if file size is known and total bytes match (robustness)
                                elif file_size_reported > 0 and self.bytes_received >= file_size_reported and len(fragments) > 0:
                                      # This handles cases where fragment count might be slightly off, but we got the data
                                      download_complete = True
                                      total_fragments_expected = max(total_fragments_expected, len(fragments)) # Update fragment count if needed
                                      download_logger.info(f"Received bytes ({self.bytes_received}) match/exceed reported size ({file_size_reported}). Assuming complete.")
                                # Single fragment case (common for small files)
                                elif total_fragments_expected == 1 and 0 in fragments:
                                      download_complete = True
                                      download_logger.info("Single fragment download complete.")

                            # --- Handle Error Response ('E') ---
                            elif response_type_byte == b'E':
                                try:
                                    # Error message is usually a null-terminated string after the 'E'
                                    error_msg = data[offset:].split(b'\x00')[0].decode('utf-8', errors='ignore')
                                    download_logger.error(f"Server returned error: '{error_msg}'")
                                    logger.error(f"Server error for file {file_id}: {error_msg}") # Log to main console
                                    return False, self.bytes_received # Download failed
                                except Exception as parse_error:
                                    download_logger.error(f"Failed to parse server error message: {parse_error}")
                                    download_logger.error(f"Raw error data: {data[offset:].hex()}")
                                    return False, self.bytes_received # Assume failure

                            # --- Handle Other/Unknown Response Types ---
                            else:
                                download_logger.warning(f"Unhandled response type byte: 0x{response_type_byte.hex()}.")
                                download_logger.warning(f"Raw response data (partial): {data[:64].hex()}")
                                # Could potentially be a challenge response or something else unexpected.

                        else: # Packet too short after header
                            download_logger.warning("Received packet too short to contain response type byte.")

                    else: # Packet doesn't start with standard header
                        download_logger.warning(f"Received packet without standard header: {data[:64].hex()}...")
                        # Could be unrelated traffic or a very non-standard server response.

                except socket.timeout:
                    # --- Handle Socket Timeout ---
                    download_logger.debug("Socket timeout occurred.")

                    # If we haven't received *any* response yet, try alternative request commands
                    if not response_received and time.time() >= alt_request_retry_time:
                        request_attempt += 1
                        if request_attempt == 1:
                            download_logger.info(f"Primary request timed out. Trying alternative: {REQUEST_FILE_CMD_ALT1.decode()}")
                            logger.info(f"Trying alternative download command 1 for {file_id}")
                            current_request_cmd_bytes = REQUEST_FILE_CMD_ALT1
                            self.sock.sendto(request_alt1, (self.server_ip, self.server_port))
                            alt_request_retry_time = time.time() + 2.0 # Wait another 2s
                        elif request_attempt == 2:
                            download_logger.info(f"Alt 1 timed out. Trying alternative: {REQUEST_FILE_CMD_ALT2.decode()}")
                            logger.info(f"Trying alternative download command 2 for {file_id}")
                            current_request_cmd_bytes = REQUEST_FILE_CMD_ALT2
                            self.sock.sendto(request_alt2, (self.server_ip, self.server_port))
                            alt_request_retry_time = time.time() + 2.0 # Wait another 2s
                        elif request_attempt == 3:
                            download_logger.info("Alt 2 timed out. Trying direct path request.")
                            logger.info(f"Trying direct path download request for {file_id}")
                            current_request_cmd_bytes = b"" # Indicate direct path mode
                            self.sock.sendto(request_alt3, (self.server_ip, self.server_port))
                            alt_request_retry_time = time.time() + 3.0 # Wait a bit longer
                        elif request_attempt == 4:
                            # Last resort: Retry the primary command (maybe initial packet loss)
                            download_logger.info("All alternatives timed out. Retrying primary request.")
                            logger.info(f"Retrying primary download command for {file_id}")
                            current_request_cmd_bytes = REQUEST_FILE_CMD
                            self.sock.sendto(request_primary, (self.server_ip, self.server_port))
                            # Don't reset alt_request_retry_time, if this fails, timeout loop will handle it.
                        else:
                             # All request formats failed to get any response
                             download_logger.warning("All request formats timed out without response.")
                             # Let the main timeout loop break naturally

                    # If we *have* received data but are stalled (waiting for more fragments)
                    elif response_received and not download_complete:
                        # Simple retry: Resend the *last successful* request format.
                        # This acts as a basic re-request mechanism. More complex logic
                        # could request specific missing fragments if the protocol supports it.
                        download_logger.debug("Timeout waiting for more fragments. Re-sending last request.")
                        if current_request_cmd_bytes == REQUEST_FILE_CMD:
                            self.sock.sendto(request_primary, (self.server_ip, self.server_port))
                        elif current_request_cmd_bytes == REQUEST_FILE_CMD_ALT1:
                            self.sock.sendto(request_alt1, (self.server_ip, self.server_port))
                        elif current_request_cmd_bytes == REQUEST_FILE_CMD_ALT2:
                            self.sock.sendto(request_alt2, (self.server_ip, self.server_port))
                        else: # Direct path request
                             self.sock.sendto(request_alt3, (self.server_ip, self.server_port))
                        # Add a small delay after resend to avoid immediate re-timeout loop
                        time.sleep(0.1)

                except socket.error as sock_err:
                    # Handle socket errors during receive
                    download_logger.error(f"Socket error during recv: {sock_err}")
                    logger.error(f"Socket error receiving data for {file_id}: {sock_err}")
                    # Assume fatal for this download attempt
                    return False, self.bytes_received
                except Exception as loop_err:
                    # Catch unexpected errors within the loop
                    download_logger.error(f"Unexpected error in download loop: {loop_err}", exc_info=True)
                    logger.error(f"Unexpected error downloading {file_id}: {loop_err}")
                    # Assume fatal for this download attempt
                    return False, self.bytes_received

            # --- End of Download Loop ---
            download_logger.info(f"Download loop finished for {file_id}.")
            download_logger.info(f"Status: Complete={download_complete}, Total Packets Recv={total_packets_received_count}")
            download_logger.info(f"Fragments Received: {len(fragments)} / {total_fragments_expected if total_fragments_expected > 0 else 'Unknown'} expected")
            download_logger.info(f"Bytes Received: {self.bytes_received} / {file_size_reported if file_size_reported > 0 else 'Unknown'} expected")

            # Log samples of received packets if any were captured
            if received_packets_log:
                download_logger.debug("Sample of first few received packets:")
                for i, pkt_sample in enumerate(received_packets_log):
                    download_logger.debug(f" Sample {i+1}: {pkt_sample.hex()}")

            # --- Assemble File and Final Check ---
            if download_complete:
                # Try to assemble the file from fragments
                try:
                    with open(save_path, 'wb') as f:
                        # Sort fragments by number and write them
                        for i in sorted(fragments.keys()):
                             f.write(fragments[i])

                    end_time = time.time()
                    download_time = max(0.01, end_time - start_time) # Avoid division by zero
                    # Calculate speed in KB/s
                    download_speed_kbs = (self.bytes_received / 1024) / download_time

                    download_logger.info(f"Successfully assembled {file_path} - {self.bytes_received} bytes.")
                    logger.info(f"Downloaded {file_id} ({self.bytes_received / 1024:.1f} KB) in {download_time:.2f}s ({download_speed_kbs:.1f} KB/s)")
                    return True, self.bytes_received # Return success and bytes received

                except IOError as write_error:
                     download_logger.error(f"IOError writing file {save_path}: {write_error}")
                     logger.error(f"Failed to write downloaded file {file_id}: {write_error}")
                     return False, self.bytes_received # Failed to save file
                except Exception as assemble_error:
                     download_logger.error(f"Error assembling file {save_path}: {assemble_error}")
                     logger.error(f"Failed to assemble file {file_id}: {assemble_error}")
                     return False, self.bytes_received # Failed during assembly
            else:
                # Download failed (incomplete or timed out)
                if not response_received:
                    download_logger.error(f"Download failed: No response received from server for any request format.")
                    logger.warning(f"Download failed for {file_id}: Server did not respond.")
                elif time.time() - last_fragment_received_time >= DOWNLOAD_TIMEOUT:
                     download_logger.error(f"Download failed: Timed out after {DOWNLOAD_TIMEOUT}s of inactivity.")
                     logger.warning(f"Download timed out for {file_id}.")
                else:
                     # Loop exited for other reason? Should not happen.
                     download_logger.error(f"Download failed: Incomplete. Reason unclear (Loop exited unexpectedly).")
                     logger.warning(f"Download incomplete for {file_id}.")

                # Log the commands that were attempted
                download_logger.debug(f"Attempted Request Formats:")
                download_logger.debug(f" 1. {REQUEST_FILE_CMD.decode()}: Sent")
                if request_attempt >= 1: download_logger.debug(f" 2. {REQUEST_FILE_CMD_ALT1.decode()}: Sent")
                if request_attempt >= 2: download_logger.debug(f" 3. {REQUEST_FILE_CMD_ALT2.decode()}: Sent")
                if request_attempt >= 3: download_logger.debug(f" 4. Direct Path: Sent")
                if request_attempt >= 4: download_logger.debug(f" 5. Primary Retry: Sent")

                return False, self.bytes_received # Return failure

        except Exception as download_error:
            # Catch errors occurring outside the main loop (e.g., initial send)
            download_logger.error(f"Unhandled error during download setup for {file_path}: {download_error}", exc_info=True)
            logger.error(f"Error setting up download for {file_id}: {download_error}")
            return False, self.bytes_received

    def close(self):
        """Closes the UDP socket."""
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
            self.sock = None
            download_logger.debug("Downloader socket closed.")


# ==============================================================
# UDP Ping Flood Class for stress testing
# ==============================================================
class UDPPingFlooder:
    def __init__(self, server_ip, server_port, rate_limit=10):
        self.server_ip = server_ip
        self.server_port = server_port
        self.sock = None
        self.rate_limit = max(0.1, rate_limit) # Pings per second (ensure positive)
        self.interval = 1.0 / self.rate_limit # Time between pings
        # These stats are typically managed per-worker instance by CS16BandwidthTester
        # self.pings_sent = 0
        # self.pings_received = 0
        # self.ping_times = []

    def _create_socket(self):
        """Create or recreate the UDP socket for pinging."""
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        # Use a relatively short timeout for ping responses
        self.sock.settimeout(max(0.5, min(2.0, self.interval * 0.8))) # Timeout based on rate, capped
        return self.sock

    def _flood_loop(self, stop_event):
        """Internal loop for sending pings and receiving replies."""
        if not self.sock:
            try:
                self._create_socket()
            except Exception as e:
                logger.error(f"Ping Flood: Failed to create socket: {e}")
                return {'pings_sent': 0, 'pings_received': 0, 'response_rate': 0, 'packets_per_sec': 0, 'avg_ping': 0} # Return zero stats on failure

        worker_pings_sent = 0
        worker_pings_received = 0
        worker_ping_times = []
        start_time = time.time()
        last_ping_time = 0

        logger.debug(f"Ping Flood worker starting (Rate: {self.rate_limit:.1f}/s)")

        try:
            while not stop_event.is_set():
                current_time = time.time()
                # --- Rate Limiting ---
                if current_time - last_ping_time >= self.interval:
                    try:
                        # --- Send Ping ---
                        ping_packet = HEADER + A2S_PING
                        send_time = time.time()
                        self.sock.sendto(ping_packet, (self.server_ip, self.server_port))
                        worker_pings_sent += 1
                        last_ping_time = send_time # Record time ping was actually sent

                        # --- Try Receive Reply (Non-blocking check within timeout) ---
                        # We check for reply immediately after sending, but the flood continues
                        # The socket timeout handles waiting for a response.
                        try:
                            response, _ = self.sock.recvfrom(128) # Small buffer for ping reply
                            receive_time = time.time()
                            # Validate reply
                            if response and response.startswith(PING_RESPONSE_PREFIX):
                                worker_pings_received += 1
                                ping_ms = (receive_time - send_time) * 1000
                                worker_ping_times.append(ping_ms)
                            # else: Malformed reply ignored
                        except socket.timeout:
                            pass # No reply received within timeout, continue loop
                        except socket.error as recv_err:
                             logger.warning(f"Ping Flood: Socket error receiving: {recv_err}")
                             # Potential issue, maybe recreate socket? For now, continue.
                             # self.close(); self._create_socket() # More aggressive recovery

                    except socket.error as send_err:
                        logger.error(f"Ping Flood: Socket error sending: {send_err}. Stopping flood for this worker.")
                        break # Stop flood on send error
                    except Exception as send_ex:
                         logger.error(f"Ping Flood: Unexpected error sending: {send_ex}")
                         break # Stop flood on other errors

                # --- Efficient Wait ---
                # Sleep efficiently until the next ping time or if stop event is set
                wait_time = max(0, self.interval - (time.time() - last_ping_time))
                # Use event.wait() which sleeps but wakes immediately if event is set
                if stop_event.wait(timeout=wait_time):
                    break # Exit loop if stop event is set during wait

        except Exception as e:
            logger.error(f"Ping Flood: Unhandled error in flood loop: {e}", exc_info=True)
        finally:
            self.close() # Ensure socket is closed when loop finishes

        # --- Calculate Stats for this Worker's Session ---
        elapsed = max(0.01, time.time() - start_time)
        packets_per_sec = worker_pings_sent / elapsed
        response_rate = (worker_pings_received / worker_pings_sent * 100) if worker_pings_sent > 0 else 0
        avg_ping = sum(worker_ping_times) / len(worker_ping_times) if worker_ping_times else 0

        logger.debug(f"Ping Flood worker finished. Sent: {worker_pings_sent}, Recv: {worker_pings_received} ({response_rate:.1f}%)")
        logger.debug(f"Worker Avg Rate: {packets_per_sec:.1f}/s, Avg Ping: {avg_ping:.1f}ms")

        return {
            'pings_sent': worker_pings_sent,
            'pings_received': worker_pings_received,
            'response_rate': response_rate,
            'packets_per_sec': packets_per_sec,
            'avg_ping': avg_ping
        }

    def close(self):
        """Closes the UDP socket."""
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
            self.sock = None
            # logger.debug("PingFlooder socket closed.") # Less verbose closing

# ==============================================================
# Connection Flood Class for stress testing
# ==============================================================
class ConnectionFlooder:
    # Note: This is a *very basic* simulation. Real CS1.6 connection involves
    # challenge-response, protocol negotiation, sending client info, etc.
    # This simplified version primarily tests the server's ability to handle
    # initial UDP packets that *look like* connection attempts.
    def __init__(self, server_ip, server_port, rate_limit=2):
        self.server_ip = server_ip
        self.server_port = server_port
        # Rate limit connections per second (be conservative to avoid self-DoS/firewall issues)
        self.rate_limit = max(0.1, rate_limit)
        self.interval = 1.0 / self.rate_limit
        # Stats managed per-worker by CS16BandwidthTester
        # self.connections_attempted = 0
        # self.connections_successful = 0 # Success is hard to define here, maybe just got *any* reply?

    def _attempt_connection(self):
        """Attempts a simplified connection sequence (challenge -> connect)."""
        sock = None
        got_reply = False # Track if we received *any* response after sending connect
        try:
            # Create a *new* socket for each connection attempt to mimic new clients
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            # Short timeout for challenge/connect replies
            sock.settimeout(max(0.5, min(2.0, self.interval * 0.8)))

            # --- 1. Send Challenge Request ---
            # Using 'getchallenge' is common, though not strictly A2S protocol standard
            # Some mods/servers might respond to this.
            challenge_request = HEADER + b"getchallenge steam\x00" # Adding 'steam' might help sometimes
            sock.sendto(challenge_request, (self.server_ip, self.server_port))
            challenge_response = None
            challenge_number = b"0" # Default challenge if none received

            # --- 2. Wait for Challenge Response ---
            try:
                challenge_response, _ = sock.recvfrom(1024)
                # Basic check: Does it look like a challenge reply? ('A' type, contains challenge number)
                if challenge_response and challenge_response.startswith(HEADER + b'A'):
                     # Very basic parsing - find numbers after 'A'
                     try:
                          # Example: \xFF\xFF\xFF\xFFA 1234567890\n\x00
                          parts = challenge_response[5:].split(b' ')
                          if len(parts) > 0 and parts[0].isdigit():
                               challenge_number = parts[0]
                               logger.debug(f"Conn Flood: Received challenge {challenge_number.decode()}")
                          else:
                              logger.debug("Conn Flood: Received 'A' response, but couldn't parse challenge number.")
                     except Exception:
                          logger.debug("Conn Flood: Error parsing challenge response.")
                else:
                    logger.debug("Conn Flood: No valid challenge response received.")
            except socket.timeout:
                logger.debug("Conn Flood: Timeout waiting for challenge response.")
            except socket.error as e:
                 logger.warning(f"Conn Flood: Socket error receiving challenge: {e}")
                 # Continue attempt with default challenge

            # --- 3. Send Connect Packet (Simplified) ---
            # Real connect packet is complex (\prot\4\unique\-1\raw\...\cdkey_hash\...\etc)
            # Send a simplified version that might trigger *some* server response/processing
            # Using the received (or default) challenge number
            connect_packet = HEADER + b'connect 48 ' + challenge_number + b' "' # Protocol 48
            # Basic fake cvars - just enough to look somewhat valid
            connect_packet += b'\\prot\\4\\unique\\-1\\raw\\fake\\cdkey_hash\\fakehash'
            connect_packet += b'\\name\\TestClient\\model\\gordon\\topcolor\\0\\bottomcolor\\0"'
            connect_packet += b'\n\x00' # End quote, newline, null terminator
            sock.sendto(connect_packet, (self.server_ip, self.server_port))
            logger.debug(f"Conn Flood: Sent simplified connect packet with challenge {challenge_number.decode()}.")

            # --- 4. Wait for *any* Reply ---
            # Success here just means the server sent *something* back after the connect packet.
            # It doesn't mean the connection was fully established.
            try:
                reply_data, _ = sock.recvfrom(1024)
                if reply_data:
                    logger.debug(f"Conn Flood: Received reply ({len(reply_data)} bytes) after connect.")
                    got_reply = True # Server responded!
                    # Example replies: connection accept, server full, bad password, challenge retry etc.
            except socket.timeout:
                logger.debug("Conn Flood: Timeout waiting for reply after connect.")
            except socket.error as e:
                 logger.warning(f"Conn Flood: Socket error receiving connect reply: {e}")

            return got_reply # Return True if any reply was received after connect

        except socket.error as sock_err:
            logger.error(f"Conn Flood: Socket error during attempt: {sock_err}")
            return False # Failed attempt
        except Exception as e:
            logger.error(f"Conn Flood: Unexpected error during attempt: {e}")
            return False # Failed attempt
        finally:
            # Ensure the temporary socket is closed
            if sock:
                try:
                    sock.close()
                except:
                    pass

    def _flood_loop(self, stop_event):
        """Internal loop for attempting connections."""
        worker_connections_attempted = 0
        worker_connections_successful = 0 # Successful means got *any* reply
        start_time = time.time()
        last_attempt_time = 0

        logger.debug(f"Connection Flood worker starting (Rate: {self.rate_limit:.1f}/s)")

        try:
            while not stop_event.is_set():
                current_time = time.time()
                # --- Rate Limiting ---
                if current_time - last_attempt_time >= self.interval:
                    success = self._attempt_connection()
                    worker_connections_attempted += 1
                    if success:
                        worker_connections_successful += 1
                    last_attempt_time = time.time()

                # --- Efficient Wait ---
                wait_time = max(0, self.interval - (time.time() - last_attempt_time))
                if stop_event.wait(timeout=wait_time):
                    break # Exit if stop event received during wait

        except Exception as e:
             logger.error(f"Connection Flood: Unhandled error in flood loop: {e}", exc_info=True)
        finally:
            pass # No persistent socket to close here

        # --- Calculate Stats for this Worker's Session ---
        elapsed = max(0.01, time.time() - start_time)
        connections_per_sec = worker_connections_attempted / elapsed
        success_rate = (worker_connections_successful / worker_connections_attempted * 100) if worker_connections_attempted > 0 else 0

        logger.debug(f"Connection Flood worker finished. Attempted: {worker_connections_attempted}, Got Reply: {worker_connections_successful} ({success_rate:.1f}%)")
        logger.debug(f"Worker Avg Rate: {connections_per_sec:.1f} attempts/s")

        return {
            'connections_attempted': worker_connections_attempted,
            'connections_successful': worker_connections_successful, # Renamed for clarity
            'success_rate': success_rate,
            'connections_per_sec': connections_per_sec
        }


# ==============================================================
# CS16BandwidthTester Class (Main Orchestrator)
# ==============================================================
class CS16BandwidthTester:
    def __init__(self, server_ip, server_port, num_connections, test_duration,
                 verbose, storage_dir, continuous_mode, no_server_monitor,
                 test_mode="download", ping_rate=10, connection_rate=2,
                 activity_log_filename=ACTIVITY_LOG_FILENAME,
                 download_log_filename=DOWNLOAD_LOG_FILENAME):

        # --- Store Configuration Arguments ---
        self.server_ip = server_ip
        self.server_port = server_port
        self.num_connections = max(1, num_connections) # Ensure at least 1 worker
        self.test_duration = test_duration
        self.verbose = verbose
        self.continuous_mode = continuous_mode # Run indefinitely if True
        self.storage_dir = Path(storage_dir)
        self.no_server_monitor = no_server_monitor # Disable A2S info/rules/ping queries if True
        self.activity_log_filename = activity_log_filename
        self.download_log_filename = download_log_filename
        # Validate test mode
        valid_modes = ["download", "ping_flood", "connection_flood", "combined"]
        if test_mode not in valid_modes:
            raise ValueError(f"Invalid test mode '{test_mode}'. Must be one of {valid_modes}")
        self.test_mode = test_mode
        self.ping_rate = ping_rate # Target pings/sec per worker for ping_flood mode
        self.connection_rate = connection_rate # Target conn attempts/sec per worker for connection_flood mode

        # --- Setup Storage and Logging ---
        self.activity_log_filepath = None # Full path to activity log
        self.download_log_filepath = None # Full path to download debug log
        self.downloads_dir = self.storage_dir / "downloads" # Subdir for downloaded files

        # Create storage directories, exit if permissions fail
        try:
            self.storage_dir.mkdir(parents=True, exist_ok=True)
            logger.info(f"Using storage directory: {self.storage_dir.resolve()}")
            if self.test_mode == "download" or self.test_mode == "combined":
                self.downloads_dir.mkdir(parents=True, exist_ok=True)
                logger.info(f"Files will be downloaded to: {self.downloads_dir.resolve()}")
        except OSError as e:
            logger.error(f"Failed to create storage directory '{self.storage_dir}' or subdir: {e}. Check permissions.")
            sys.exit(1) # Critical error, cannot proceed without storage

        # Configure file loggers
        self._configure_activity_logger()
        self._configure_download_logger()

        # --- Core State Variables ---
        self.active = False # Is the test currently running?
        self.threads = [] # List to keep track of running threads
        # List of dictionaries, one per worker connection, storing state
        # Example: {"id": 1, "downloader": None, "flooder": None, "conn_flooder": None, "status": "idle", "current_task": "Waiting"}
        self.connections = []
        self.lock = threading.Lock() # Lock for protecting shared resources (counters, lists)
        self._stop_event = threading.Event() # Event to signal threads to stop gracefully
        self.start_time = 0 # Timestamp when the test started
        self.end_time = 0 # Timestamp when the test ended

        # --- Test Statistics Counters (Protected by self.lock) ---
        self.bytes_received = 0 # Total bytes received across all download workers
        self.downloads_completed = 0 # Count of successfully downloaded files
        self.downloads_failed = 0 # Count of failed/incomplete file downloads
        self.initial_connection_failures = 0 # Workers that failed to even start
        self.runtime_connection_issues = 0 # Errors encountered during worker operation (e.g., socket errors)
        self.active_workers_count = 0 # Current count of running worker threads

        # Aggregate Ping flood stats (Updated by ping flood workers)
        self.ping_flood_stats = {
            'pings_sent': 0,
            'pings_received': 0,
            'response_rate': 0.0, # Overall %
            'packets_per_sec': 0.0, # Average overall pps
            'avg_ping': 0.0 # Average overall ping ms
            # We might need running totals/counts to calculate accurate averages later
        }
        self._ping_flood_total_ping_ms = 0 # Sum of all avg pings reported by workers
        self._ping_flood_reports = 0       # Count of ping flood reports received

        # Aggregate Connection flood stats (Updated by connection flood workers)
        self.connection_flood_stats = {
            'connections_attempted': 0,
            'connections_successful': 0, # Connections that got any reply
            'success_rate': 0.0, # Overall %
            'connections_per_sec': 0.0 # Average overall attempts/sec
        }
        self._conn_flood_total_rate = 0 # Sum of all rates reported by workers
        self._conn_flood_reports = 0    # Count of conn flood reports received

        # --- Server Info Tracking (Protected by self.lock) ---
        self.server_query = None # Instance of ServerQuery class
        if not self.no_server_monitor:
            # Pass the main storage dir, ServerQuery handles its own temp subdir if needed
            self.server_query = ServerQuery(self.server_ip, self.server_port, storage_dir=str(self.storage_dir))
        self.server_info = None # Last successful A2S_INFO result (dict)
        self.server_rules = None # Last successful A2S_RULES result (dict)
        self.known_maps = [] # List of map names discovered (from info, players, etc.)
        self.discovered_files = [] # List of file paths discovered (from .res files, etc.)
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "UNKNOWN" # Overall status string
        self.server_last_seen = 0 # Timestamp when server last responded to info query
        self.server_info_thread = None # Thread object for server monitoring
        self.server_info_interval = 5 # How often to query server info (seconds)
        # Log of server status changes over time for reporting
        self.server_status_log = [] # List of dicts: {'timestamp': ts, 'status': 'ONLINE', 'ping': 50, 'map': 'de_dust2'}

        # --- UI / Recent Activity Tracking ---
        # Deque for efficient fixed-size list of recent log events for UI
        self.last_activity = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT)
        # List to store bandwidth data points over time for reporting [(timestamp, MB/s), ...]
        self.bandwidth_log_points = []

        self.display_thread = None # Thread object for the real-time terminal display
        self.resource_scanner_thread = None # Thread for scanning downloaded .res files


    def _configure_activity_logger(self):
        """Configures the file handler for the activity logger."""
        # Prevent adding duplicate handlers if this is called multiple times
        if any(isinstance(h, logging.FileHandler) and h.baseFilename == str(self.storage_dir / self.activity_log_filename) for h in activity_logger.handlers):
             logger.debug("Activity log handler already configured.")
             # Ensure filepath variable is set even if handler exists
             self.activity_log_filepath = self.storage_dir / self.activity_log_filename
             return

        # Close existing handlers cleanly before adding new ones (if any)
        for handler in activity_logger.handlers[:]:
            try:
                handler.close()
                activity_logger.removeHandler(handler)
            except Exception as e:
                logger.warning(f"Could not close/remove existing activity log handler: {e}")
        try:
            self.activity_log_filepath = self.storage_dir / self.activity_log_filename
            # Use 'a' mode to append to the log file
            file_handler = logging.FileHandler(str(self.activity_log_filepath), mode='a', encoding='utf-8')
            file_formatter = logging.Formatter('%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
            file_handler.setFormatter(file_formatter)
            activity_logger.addHandler(file_handler)
            # Set level based on verbosity - log DEBUG if verbose, otherwise INFO
            activity_logger.setLevel(logging.DEBUG if self.verbose else logging.INFO)
            activity_logger.info(f"--- Activity Log Started ({datetime.now().isoformat()}) ---")
            logger.info(f"Logging activity details to: {self.activity_log_filepath}")
        except Exception as e:
            logger.error(f"Failed to configure activity log file handler '{self.activity_log_filepath}': {e}")
            # Add NullHandler to prevent errors if file logging fails
            if not activity_logger.hasHandlers():
                activity_logger.addHandler(logging.NullHandler())

    def _configure_download_logger(self):
        """Configures the file handler for the download debug logger."""
         # Prevent adding duplicate handlers
        if any(isinstance(h, logging.FileHandler) and h.baseFilename == str(self.storage_dir / self.download_log_filename) for h in download_logger.handlers):
             logger.debug("Download debug log handler already configured.")
             self.download_log_filepath = self.storage_dir / self.download_log_filename
             return

        # Close existing handlers cleanly
        for handler in download_logger.handlers[:]:
            try:
                handler.close()
                download_logger.removeHandler(handler)
            except Exception as e:
                logger.warning(f"Could not close/remove existing download log handler: {e}")
        try:
            self.download_log_filepath = self.storage_dir / self.download_log_filename
            file_handler = logging.FileHandler(str(self.download_log_filepath), mode='a', encoding='utf-8')
            file_formatter = logging.Formatter('%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
            file_handler.setFormatter(file_formatter)
            download_logger.addHandler(file_handler)
            # Download logger always logs DEBUG and above to file when enabled
            download_logger.setLevel(logging.DEBUG)
            download_logger.info(f"--- Download Debug Log Started ({datetime.now().isoformat()}) ---")
            logger.info(f"Logging detailed download debug info to: {self.download_log_filepath}")
        except Exception as e:
            logger.error(f"Failed to configure download log file handler '{self.download_log_filepath}': {e}")
            if not download_logger.hasHandlers():
                download_logger.addHandler(logging.NullHandler())


    def _increment_counter(self, counter_name, value=1):
        """Thread-safe increment of a counter attribute."""
        with self.lock:
            # Use getattr/setattr for dynamic counter names
            current_value = getattr(self, counter_name, 0)
            setattr(self, counter_name, current_value + value)

    def _decrement_counter(self, counter_name, value=1):
        """Thread-safe decrement of a counter attribute."""
        with self.lock:
            current_value = getattr(self, counter_name, 0)
            setattr(self, counter_name, current_value - value)

    def _log_activity_event(self, worker_id, event_type, status, identifier, bytes_val=0, error_msg="", detail=""):
        """Logs events consistently to activity log file and potentially console, updates UI deque."""
        # Format the detailed log message for the activity file
        message = f"Worker {worker_id:<3} [{event_type:<12}] | Status: {status:<10} | ID: {identifier}"
        if bytes_val > 0:
            message += f" | Bytes: {bytes_val:<10}" # Add byte count if relevant
        if detail:
            message += f" | Detail: {detail}" # Add extra details
        if error_msg:
            message += f" | Error: {error_msg}" # Add error message if present

        # Determine log level based on status
        log_level = logging.INFO # Default level
        if "FAIL" in status or "ERROR" in status or "TIMEOUT" in status or "WARN" in status:
            log_level = logging.WARNING
        elif status == "CRITICAL":
             log_level = logging.CRITICAL
        elif status == "DEBUG":
             log_level = logging.DEBUG

        # Log the detailed message to the activity file logger (respects its level)
        if activity_logger.hasHandlers() and not isinstance(activity_logger.handlers[0], logging.NullHandler):
             activity_logger.log(log_level, message)
        elif log_level >= logging.WARNING: # Fallback console log for important messages if file handler failed
            logger.log(log_level, f"[Activity Log Disabled] {message}")

        # Log a potentially simplified message to the main console logger
        # Show errors/warnings always, info/debug only if verbose mode is enabled
        if log_level >= logging.WARNING or self.verbose:
            console_msg = f"Worker {worker_id}: {event_type} {status}: {identifier}"
            # Add concise byte info to console message if present
            if bytes_val > 0:
                if bytes_val > 1024*1024:
                     console_msg += f" ({bytes_val/(1024*1024):.1f}MB)"
                elif bytes_val > 1024:
                    console_msg += f" ({bytes_val/1024:.1f}KB)"
                else:
                    console_msg += f" ({bytes_val}B)"
            # Add short error to console if it's a warning/error level event
            if error_msg and log_level >= logging.WARNING:
                 short_error = (error_msg[:50] + '...') if len(error_msg) > 50 else error_msg
                 console_msg += f" - Err: {short_error}"

            # Use appropriate level for console log (DEBUG for INFO/DEBUG events, actual level otherwise)
            console_log_level = logging.DEBUG if log_level <= logging.INFO else log_level
            logger.log(console_log_level, console_msg)

        # Update the UI deque with a concise entry
        with self.lock:
            # Add status indicator only if it's not a simple success/completion
            ui_status_indicator = ""
            if status not in ["SUCCESS", "COMPLETE", "DELETED", "SAVED", "OK"]:
                ui_status_indicator = f" [{status}]"

            # Shorten long identifiers (like file paths) for UI display
            display_id = identifier
            if len(identifier) > 40:
                 # Show first few and last part of long IDs
                 display_id = identifier[:15] + "..." + identifier[-22:]

            # Format the entry for the UI deque
            ui_entry = f"W{worker_id:<2}: {display_id}"
            # Add byte info to UI if present
            if bytes_val > 0:
                if bytes_val > 1024*1024:
                    ui_entry += f" ({bytes_val/(1024*1024):.1f}MB)"
                else: # Show KB for smaller amounts
                    ui_entry += f" ({bytes_val/1024:.1f}KB)"

            ui_entry += ui_status_indicator # Append status if needed
            self.last_activity.append(ui_entry) # Add to the deque


    # --- Download Logic Wrapper ---
    def _download_file(self, conn_info):
        """Manages the download process for a worker thread."""
        conn_id = conn_info['id']

        # --- Get or Create Downloader Instance ---
        downloader = conn_info.get("downloader")
        if not downloader:
            try:
                # Pass the dedicated downloads subdirectory
                downloader = UDPFileDownloader(self.server_ip, self.server_port, self.downloads_dir)
                conn_info["downloader"] = downloader
                self._log_activity_event(conn_id, "Setup", "DEBUG", "Downloader initialized")
            except Exception as e:
                self._log_activity_event(conn_id, "Setup", "ERROR", "Downloader init failed", error_msg=str(e))
                self._increment_counter("runtime_connection_issues")
                conn_info["status"] = "error"
                return False # Cannot proceed

        # --- Select a File to Download ---
        file_to_download = self._get_file_to_download()
        if not file_to_download:
            self._log_activity_event(conn_id, "Download", "WAITING", "No files available in queue")
            conn_info["status"] = "waiting_file"
            conn_info["current_task"] = "Waiting for files"
            # Return False to indicate no work done, worker should sleep/retry
            return False

        # --- Perform Download ---
        conn_info["status"] = "downloading"
        conn_info["current_task"] = f"DL: {Path(file_to_download).name}" # Show just filename in task
        conn_info["last_activity_time"] = time.time()
        self._log_activity_event(conn_id, "Download", "START", file_to_download)

        try:
            success, bytes_received = downloader.download_file(file_to_download)

            # Update global byte counter (thread-safe)
            if bytes_received > 0:
                 self._increment_counter("bytes_received", bytes_received)

            # Log result and update counters
            if success:
                self._increment_counter("downloads_completed")
                self._log_activity_event(conn_id, "Download", "SUCCESS", file_to_download, bytes_received)
                conn_info["status"] = "idle" # Worker is ready for next task
                return True # Task successful
            else:
                self._increment_counter("downloads_failed")
                # Log failure reason if available from downloader (e.g., timeout, server error)
                # Downloader logs details to download_debug.log, keep activity log concise.
                self._log_activity_event(conn_id, "Download", "FAILED", file_to_download, bytes_received)
                conn_info["status"] = "idle" # Still idle, but previous task failed
                return False # Task failed

        except Exception as e:
            # Catch unexpected errors during the download call itself
            self._increment_counter("downloads_failed")
            self._increment_counter("runtime_connection_issues")
            self._log_activity_event(conn_id, "Download", "CRITICAL", file_to_download, 0, str(e))
            conn_info["status"] = "error" # Worker encountered critical error

            # Attempt to reset downloader on critical error
            try:
                if conn_info.get("downloader"):
                    conn_info["downloader"].close()
                # Re-creation will happen on next call if worker continues
                conn_info["downloader"] = None
                self._log_activity_event(conn_id, "Setup", "DEBUG", "Downloader reset after error")
            except Exception as close_err:
                 self._log_activity_event(conn_id, "Setup", "WARN", "Error closing downloader after error", error_msg=str(close_err))

            return False # Task failed critically

    # --- Ping Flood Logic Wrapper ---
    def _ping_flood_worker(self, conn_info):
        """Manages the ping flood process for a worker thread."""
        conn_id = conn_info['id']

        # --- Get or Create Flooder Instance ---
        flooder = conn_info.get("flooder")
        if not flooder:
            try:
                flooder = UDPPingFlooder(self.server_ip, self.server_port, self.ping_rate)
                conn_info["flooder"] = flooder
                self._log_activity_event(conn_id, "Setup", "DEBUG", "PingFlooder initialized")
            except Exception as e:
                self._log_activity_event(conn_id, "Setup", "ERROR", "PingFlooder init failed", error_msg=str(e))
                self._increment_counter("runtime_connection_issues")
                conn_info["status"] = "error"
                return False

        # --- Perform Ping Flood ---
        conn_info["status"] = "pinging"
        conn_info["current_task"] = f"Ping Flood ({self.ping_rate}/s)"
        conn_info["last_activity_time"] = time.time()
        self._log_activity_event(conn_id, "Ping Flood", "START", f"Rate: {self.ping_rate}/s")

        try:
            # The flood loop now takes the stop_event directly
            stats = flooder._flood_loop(self._stop_event)

            # --- Update Global Stats (Aggregate) ---
            if stats['pings_sent'] > 0:
                with self.lock:
                    self.ping_flood_stats['pings_sent'] += stats['pings_sent']
                    self.ping_flood_stats['pings_received'] += stats['pings_received']
                    # Recalculate overall averages based on totals
                    if self.ping_flood_stats['pings_sent'] > 0:
                        self.ping_flood_stats['response_rate'] = (self.ping_flood_stats['pings_received'] / self.ping_flood_stats['pings_sent']) * 100

                    # Update running average for rate and ping
                    self._ping_flood_reports += 1
                    self._ping_flood_total_ping_ms += stats['avg_ping'] * stats['pings_received'] # Weighted by received count for avg ping
                    total_received_so_far = self.ping_flood_stats['pings_received']
                    if total_received_so_far > 0:
                         self.ping_flood_stats['avg_ping'] = self._ping_flood_total_ping_ms / total_received_so_far

                    # Average rate based on number of reports
                    self.ping_flood_stats['packets_per_sec'] = ((self.ping_flood_stats['packets_per_sec'] * (self._ping_flood_reports - 1)) + stats['packets_per_sec']) / self._ping_flood_reports


            # Log completion of this worker's session
            self._log_activity_event(conn_id, "Ping Flood", "COMPLETE",
                                   f"{stats['pings_sent']} sent, {stats['pings_received']} recv",
                                   stats['pings_sent'], # Use sent count for "bytes" field conceptually
                                   detail=f"Rate: {stats['packets_per_sec']:.1f}/s, AvgPing: {stats['avg_ping']:.1f}ms")

            conn_info["status"] = "idle"
            return True # Task successful (even if response rate was low)

        except Exception as e:
            # Catch unexpected errors during the flood call itself
            self._increment_counter("runtime_connection_issues")
            self._log_activity_event(conn_id, "Ping Flood", "CRITICAL", "Flood loop error", error_msg=str(e))
            conn_info["status"] = "error"
            # Attempt to reset flooder? Less critical than downloader perhaps.
            try:
                if conn_info.get("flooder"):
                    conn_info["flooder"].close()
                conn_info["flooder"] = None
            except Exception: pass
            return False # Task failed critically

    # --- Connection Flood Logic Wrapper ---
    def _connection_flood_worker(self, conn_info):
        """Manages the connection flood process for a worker thread."""
        conn_id = conn_info['id']

        # --- Get or Create Flooder Instance ---
        flooder = conn_info.get("conn_flooder")
        if not flooder:
            try:
                flooder = ConnectionFlooder(self.server_ip, self.server_port, self.connection_rate)
                conn_info["conn_flooder"] = flooder
                self._log_activity_event(conn_id, "Setup", "DEBUG", "ConnFlooder initialized")
            except Exception as e:
                self._log_activity_event(conn_id, "Setup", "ERROR", "ConnFlooder init failed", error_msg=str(e))
                self._increment_counter("runtime_connection_issues")
                conn_info["status"] = "error"
                return False

        # --- Perform Connection Flood ---
        conn_info["status"] = "connecting"
        conn_info["current_task"] = f"Conn Flood ({self.connection_rate}/s)"
        conn_info["last_activity_time"] = time.time()
        self._log_activity_event(conn_id, "Conn Flood", "START", f"Rate: {self.connection_rate}/s")

        try:
             # The flood loop takes the stop_event directly
            stats = flooder._flood_loop(self._stop_event)

            # --- Update Global Stats (Aggregate) ---
            if stats['connections_attempted'] > 0:
                 with self.lock:
                    self.connection_flood_stats['connections_attempted'] += stats['connections_attempted']
                    self.connection_flood_stats['connections_successful'] += stats['connections_successful']
                    # Recalculate overall averages
                    if self.connection_flood_stats['connections_attempted'] > 0:
                        self.connection_flood_stats['success_rate'] = (self.connection_flood_stats['connections_successful'] /
                                                                       self.connection_flood_stats['connections_attempted']) * 100

                    # Update running average for rate
                    self._conn_flood_reports += 1
                    self.connection_flood_stats['connections_per_sec'] = ((self.connection_flood_stats['connections_per_sec'] * (self._conn_flood_reports - 1)) + stats['connections_per_sec']) / self._conn_flood_reports


            # Log completion
            self._log_activity_event(conn_id, "Conn Flood", "COMPLETE",
                                   f"{stats['connections_attempted']} attempts, {stats['connections_successful']} replies",
                                   stats['connections_attempted'], # Use attempt count for "bytes" field
                                   detail=f"Rate: {stats['connections_per_sec']:.1f}/s, ReplyRate: {stats['success_rate']:.1f}%")

            conn_info["status"] = "idle"
            return True # Task successful

        except Exception as e:
            # Catch unexpected errors
            self._increment_counter("runtime_connection_issues")
            self._log_activity_event(conn_id, "Conn Flood", "CRITICAL", "Flood loop error", error_msg=str(e))
            conn_info["status"] = "error"
            # No persistent resource to reset for ConnFlooder
            return False # Task failed critically

    # --- File Selection Logic ---
    def _get_file_to_download(self):
        """Selects a file to download based on priority and discovered content."""
        with self.lock: # Protect access to shared lists (known_maps, discovered_files, server_info)
            choices = []
            weights = [] # Corresponding weights for weighted random choice

            # --- Priority 1: Current Map Resources (Highest Weight) ---
            if self.server_info and 'map' in self.server_info:
                current_map = self.server_info['map']
                if current_map and current_map not in ['unknown', '']:
                    # Add core map file
                    map_bsp = f"maps/{current_map}.bsp"
                    if map_bsp not in choices: choices.append(map_bsp); weights.append(100)

                    # Add related map resources
                    common_map_files = [
                        f"maps/{current_map}.res", # Resource file (important!)
                        f"maps/{current_map}.txt", # Map description/config
                        f"overviews/{current_map}.bmp", # Overview image
                        f"overviews/{current_map}.txt", # Overview text
                        # Common skybox convention
                        f"gfx/env/{current_map}up.tga", f"gfx/env/{current_map}dn.tga",
                        f"gfx/env/{current_map}lf.tga", f"gfx/env/{current_map}rt.tga",
                        f"gfx/env/{current_map}ft.tga", f"gfx/env/{current_map}bk.tga"
                    ]
                    for f in common_map_files:
                         if f not in choices: choices.append(f); weights.append(80) # Slightly lower weight

            # --- Priority 2: Discovered Files (High Weight) ---
            # Add files discovered from .res files or other means
            for file_path in self.discovered_files:
                 if file_path not in choices:
                     # Weight based on file type? Maybe models/sounds higher?
                     weight = 50
                     if file_path.endswith(".mdl"): weight = 60
                     if file_path.endswith(".wav"): weight = 55
                     if file_path.endswith(".res"): weight = 70 # Prioritize downloading other .res files
                     choices.append(file_path); weights.append(weight)

            # --- Priority 3: Other Known Maps (Medium Weight) ---
            for map_name in self.known_maps:
                 map_bsp = f"maps/{map_name}.bsp"
                 if map_bsp not in choices: choices.append(map_bsp); weights.append(30)
                 map_res = f"maps/{map_name}.res"
                 if map_res not in choices: choices.append(map_res); weights.append(35)

            # --- Priority 4: Generate Guesses (Low Weight) ---
            # Use common prefixes and file types to guess potential files
            if len(choices) < self.num_connections * 5: # Only generate if list is getting small
                 for _ in range(10): # Generate a few guesses
                    file_type_template = random.choice(FILE_TYPES) # e.g., "models/*.mdl"
                    base_dir = file_type_template.split('*')[0] # e.g., "models/"
                    extension = file_type_template.split('.')[-1] # e.g., "mdl"

                    guess_name = ""
                    if base_dir == "maps/":
                        prefix = random.choice(MAP_PREFIXES)
                        num = random.randint(1, 20) # Guess map number
                        guess_name = f"{prefix}random_{num}"
                    elif base_dir == "models/":
                        model_types = ["player", "v_", "p_", "w_"] # Common model prefixes
                        prefix = random.choice(model_types)
                        # Guess common weapon/player model names
                        common_names = ["ak47", "m4a1", "knife", "usp", "gign", "terror", "leet"]
                        guess_name = f"{prefix}{random.choice(common_names)}"
                        if "player" in prefix: guess_name = f"player/{random.choice(common_names)}/{random.choice(common_names)}"
                    else:
                        # Generic guess for other types
                         guess_name = f"generic_{random.randint(1, 100)}"

                    guess_path = f"{base_dir}{guess_name}.{extension}"
                    if guess_path not in choices: choices.append(guess_path); weights.append(5) # Very low weight

            # --- Select File ---
            if not choices:
                return None # No files available to download

            # Use weighted random selection
            try:
                 selected_file = random.choices(choices, weights=weights, k=1)[0]
                 # Optionally, remove selected file to avoid immediate re-download?
                 # Or maybe just lower its weight significantly if selected recently?
                 # For now, allow re-selection.
                 return selected_file
            except IndexError: # Should not happen if choices is not empty
                 return None
            except Exception as e:
                 logger.error(f"Error during weighted file selection: {e}")
                 # Fallback to simple random choice if weighted fails
                 return random.choice(choices) if choices else None

    # --- Worker Thread Main Logic ---
    def _connection_worker(self, conn_info):
        """The main function executed by each worker thread."""
        conn_id = conn_info['id']
        worker_log_prefix = f"Worker {conn_id}" # For cleaner logging

        # Increment active worker count (thread-safe)
        self._increment_counter("active_workers_count")
        conn_info["status"] = "starting"
        self._log_activity_event(conn_id, "Worker", "START", "Thread starting")

        try:
            # --- Initial Staggered Delay ---
            # Prevent all workers hitting server simultaneously at startup
            # Delay proportional to worker ID, capped at a few seconds
            initial_delay = min(conn_id * 0.2, 3.0) # 0.2s per worker, max 3s
            if initial_delay > 0:
                self._log_activity_event(conn_id, "Worker", "DEBUG", f"Initial delay {initial_delay:.1f}s")
                # Use event.wait() for the delay - allows immediate stop if needed
                if self._stop_event.wait(timeout=initial_delay):
                    self._log_activity_event(conn_id, "Worker", "INTERRUPT", "Stopped during initial delay")
                    return # Exit thread if stop event set during delay

            # --- Main Worker Loop ---
            while self.active and not self._stop_event.is_set():
                conn_info["status"] = "idle"
                conn_info["current_task"] = "Idle"
                task_success = False # Track if the chosen task succeeded
                start_task_time = time.time()

                # --- Select Task Based on Test Mode ---
                try:
                    current_mode = self.test_mode
                    # If combined mode, randomly choose a task type
                    if current_mode == "combined":
                        # Weight choices? e.g., more downloads than floods?
                        # Simple random choice for now:
                        current_mode = random.choice(["download", "ping_flood", "connection_flood"])
                        conn_info["current_task"] = f"Selected: {current_mode}"
                        # Add small delay after selection?
                        if self._stop_event.wait(0.05): break

                    # --- Execute Chosen Task ---
                    if current_mode == "download":
                        task_success = self._download_file(conn_info)
                    elif current_mode == "ping_flood":
                        task_success = self._ping_flood_worker(conn_info)
                    elif current_mode == "connection_flood":
                        task_success = self._connection_flood_worker(conn_info)

                except Exception as task_err:
                    # Catch errors within the task execution logic itself
                    self._log_activity_event(conn_id, "Worker", "CRITICAL", f"Error during {current_mode} task", error_msg=str(task_err))
                    self._increment_counter("runtime_connection_issues")
                    task_success = False # Mark task as failed
                    conn_info["status"] = "error"
                    # Add a longer delay after a critical task error
                    if self._stop_event.wait(timeout=random.uniform(2.0, 5.0)): break

                # --- Wait Before Next Task ---
                end_task_time = time.time()
                task_duration = end_task_time - start_task_time

                # Calculate delay: short delay after success, longer after failure/no work
                # Add randomness to spread load
                delay_base = random.uniform(0.1, 0.3) if task_success else random.uniform(0.5, 1.5)
                worker_delay = delay_base

                conn_info["status"] = "sleeping"
                conn_info["current_task"] = f"Sleeping ({worker_delay:.2f}s)"
                self._log_activity_event(conn_id, "Worker", "DEBUG", f"Task took {task_duration:.3f}s. Sleeping {worker_delay:.3f}s.")

                # Use event.wait() for sleeping - allows interruption by stop_event
                if self._stop_event.wait(timeout=worker_delay):
                    self._log_activity_event(conn_id, "Worker", "INTERRUPT", "Stop event received during sleep.")
                    break # Exit loop if stop event is set

        except Exception as loop_error:
            # Catch unexpected errors in the main worker loop itself
            self._log_activity_event(conn_id, "Worker", "CRITICAL", "Unhandled loop error", error_msg=str(loop_error))
            conn_info["status"] = "error_loop"
            conn_info["current_task"] = "LOOP ERROR"
            self._increment_counter("runtime_connection_issues")
        finally:
            # --- Worker Cleanup ---
            final_status = conn_info.get("status", "unknown")
            self._decrement_counter("active_workers_count") # Decrement active count (thread-safe)
            conn_info["status"] = "stopped"
            conn_info["current_task"] = "Stopped"
            self._log_activity_event(conn_id, "Worker", "STOP", f"Thread finished (Final Status: {final_status})")

            # Close resources associated with this worker
            # Downloader
            downloader = conn_info.get("downloader")
            if downloader:
                try: downloader.close()
                except Exception: pass
                conn_info["downloader"] = None
            # Ping Flooder
            flooder = conn_info.get("flooder")
            if flooder:
                try: flooder.close()
                except Exception: pass
                conn_info["flooder"] = None
            # Connection Flooder (no persistent resource typically)
            conn_flooder = conn_info.get("conn_flooder")
            if conn_flooder:
                # No close method defined for ConnectionFlooder in this example
                 conn_info["conn_flooder"] = None


    # --- Server Info Update Thread ---
    def _update_server_info(self):
        """Periodically queries server for info, rules, players using ServerQuery class."""
        if self.no_server_monitor or not self.server_query:
            logger.info("Server monitoring thread disabled.")
            return # Exit if monitoring is disabled

        monitor_log_prefix = "(ServerMon)"
        logger.info(f"{monitor_log_prefix} Thread started (Interval: {self.server_info_interval}s)")

        # --- Query Timing Control ---
        # Time intervals for different query types
        query_rules_interval = 30  # How often to query rules (less frequent)
        query_players_interval = 15 # How often to query players (more frequent for map guessing)
        last_rules_query_time = 0
        last_players_query_time = 0
        # Schedule first query shortly after start
        next_query_time = time.time() + (0.5 if not self.continuous_mode else 1.5)

        while self.active and not self._stop_event.is_set():
            # --- Wait Until Next Query Time ---
            wait_time = next_query_time - time.time()
            if wait_time > 0:
                if self._stop_event.wait(timeout=wait_time):
                    break # Exit if stop event set during wait

            if self._stop_event.is_set(): break # Check again after wait

            current_time = time.time()
            current_status = "UNKNOWN"
            ping = -1
            map_name = None
            player_count = -1
            max_players = -1
            info_success = False # Track if A2S_INFO query succeeded in this cycle

            # --- Query A2S_INFO ---
            try:
                logger.debug(f"{monitor_log_prefix} Querying server info...")
                server_info_result = self.server_query.get_info()
                query_timestamp = time.time() # Record time right after query attempt

                if server_info_result:
                    # Info query succeeded
                    info_success = True
                    with self.lock: # Protect shared server state variables
                        self.server_info = server_info_result
                        self.server_last_seen = query_timestamp
                        ping = server_info_result.get('ping', -1)
                        player_count = server_info_result.get('players', -1)
                        max_players = server_info_result.get('max_players', -1)
                        # Determine status based on ping
                        if ping < 0:
                             current_status = "TIMEOUT"
                        elif ping > HIGH_PING_THRESHOLD:
                             current_status = "HIGH_PING"
                        else:
                             current_status = "ONLINE"
                        self.server_status = current_status # Update overall status

                        # Discover new map from info
                        new_map_name = server_info_result.get('map')
                        if new_map_name and new_map_name not in self.known_maps and new_map_name not in ['', 'unknown', 'N/A']:
                             self.known_maps.append(new_map_name)
                             self._log_activity_event(0, "Discovery", "INFO", f"New map from A2S_INFO: {new_map_name}")
                             # Add potential related files for the new map
                             self._add_map_related_files(new_map_name)

                        map_name = new_map_name # Store map name for logging this cycle
                else:
                    # Info query failed (timeout or error)
                    info_success = False
                    with self.lock:
                        # Check if server has been unresponsive for too long
                        offline_threshold_met = self.server_last_seen > 0 and (query_timestamp - self.server_last_seen > SERVER_OFFLINE_TIMEOUT)
                        if offline_threshold_met:
                            current_status = "OFFLINE"
                            if self.server_status != "OFFLINE": # Log transition
                                 self._log_activity_event(0, "Server Status", "WARN", f"Server OFFLINE (Timeout > {SERVER_OFFLINE_TIMEOUT}s)")
                        elif self.server_status != "OFFLINE": # If not already offline, mark as issues
                             current_status = "TIMEOUT" if self.server_status != "ERROR" else "ERROR" # Keep ERROR if it was set previously
                             self._log_activity_event(0, "Server Status", "WARN", "A2S_INFO query failed")
                        else:
                            current_status = "OFFLINE" # Stay offline if already marked

                        self.server_status = current_status
                        # Keep last known info, don't clear self.server_info immediately on failure

                # --- Query A2S_RULES (Periodically) ---
                needs_rules_query = info_success and (current_time - last_rules_query_time > query_rules_interval)
                if needs_rules_query:
                    logger.debug(f"{monitor_log_prefix} Querying server rules...")
                    rules_result = self.server_query.get_rules()
                    if rules_result is not None: # Query succeeded (even if rules are empty)
                        last_rules_query_time = time.time() # Update time only on success
                        with self.lock:
                            if rules_result != self.server_rules: # Log if rules changed
                                 self._log_activity_event(0, "Server Rules", "INFO", "Rules updated/received")
                            self.server_rules = rules_result
                        # Check specific rules like sv_allowdownload, sv_downloadurl
                        self._check_download_rules(rules_result)
                    else:
                        self._log_activity_event(0, "Server Rules", "WARN", "A2S_RULES query failed")

                # --- Query A2S_PLAYER (Periodically for map guessing) ---
                needs_players_query = info_success and (current_time - last_players_query_time > query_players_interval)
                if needs_players_query:
                    logger.debug(f"{monitor_log_prefix} Querying player info...")
                    player_list = self.server_query.get_players()
                    if player_list: # Query succeeded and returned players
                        last_players_query_time = time.time()
                        # Analyze player names for potential map clues
                        self._guess_maps_from_players(player_list)
                    # else: Player query failed or returned empty list

            except Exception as e:
                # Catch unexpected errors during query process
                logger.error(f"{monitor_log_prefix} Unhandled error during query cycle: {e}", exc_info=self.verbose)
                with self.lock:
                    current_status = "ERROR"
                    self.server_status = current_status

            # --- Log Current Status Snapshot ---
            # Use locked values obtained earlier if query succeeded
            log_map = map_name if info_success else (self.server_info.get('map', 'UNKNOWN') if self.server_info else 'UNKNOWN')
            status_log_entry = {'timestamp': current_time, 'status': current_status, 'ping': ping, 'players': player_count, 'max_players': max_players, 'map': log_map}
            with self.lock:
                self.server_status_log.append(status_log_entry)

            # --- Schedule Next Query ---
            next_query_time = time.time() + self.server_info_interval

        # --- Cleanup ---
        if self.server_query:
            self.server_query.close()
        logger.info(f"{monitor_log_prefix} Thread finished.")

    def _add_map_related_files(self, map_name):
        """Adds common files related to a map name to the discovered_files list."""
        if not map_name: return
        with self.lock:
             files_to_add = [
                 f"maps/{map_name}.bsp",
                 f"maps/{map_name}.res",
                 f"maps/{map_name}.txt",
                 f"overviews/{map_name}.bmp",
                 f"overviews/{map_name}.txt",
                 f"sound/ambience/{map_name}.wav", # Common convention
                 # Skybox
                 f"gfx/env/{map_name}up.tga", f"gfx/env/{map_name}dn.tga",
                 f"gfx/env/{map_name}lf.tga", f"gfx/env/{map_name}rt.tga",
                 f"gfx/env/{map_name}ft.tga", f"gfx/env/{map_name}bk.tga"
             ]
             added_count = 0
             for f in files_to_add:
                 if f not in self.discovered_files:
                     self.discovered_files.append(f)
                     added_count += 1
             if added_count > 0:
                  self._log_activity_event(0, "Discovery", "DEBUG", f"Added {added_count} potential files for map {map_name}")

    def _check_download_rules(self, rules):
         """Checks rules dict for sv_allowdownload and sv_downloadurl."""
         if not rules: return
         dl_setting = rules.get('sv_allowdownload', 'N/A')
         fastdl_url = rules.get('sv_downloadurl', '')

         log_prefix = "(ServerMon)"
         if dl_setting == '0':
             logger.warning(f"{log_prefix} ⚠️ Server has UDP downloads DISABLED (sv_allowdownload=0)")
             # Also log to download logger as it's critical info
             download_logger.warning("Server rule sv_allowdownload=0 - UDP downloads will likely fail!")
         else:
             logger.info(f"{log_prefix} Server UDP download setting: sv_allowdownload={dl_setting}")
             download_logger.info(f"Server download setting: sv_allowdownload={dl_setting}")

         if fastdl_url:
             logger.warning(f"{log_prefix} ⚠️ Server uses FastDL (HTTP): {fastdl_url}")
             download_logger.warning(f"Server uses FastDL URL: {fastdl_url}. UDP downloads might be secondary or disabled.")

    def _guess_maps_from_players(self, player_list):
        """Analyzes player names to guess potential map names."""
        if not player_list: return
        with self.lock:
             added_count = 0
             for name in player_list:
                 name_lower = name.lower()
                 for prefix in MAP_PREFIXES:
                     if prefix in name_lower:
                         # Try to extract map name part after prefix
                         try:
                             potential_map_part = name_lower.split(prefix, 1)[1]
                             # Clean up potential map name (take alphanumeric/_ before space/special char)
                             cleaned_map_part = ""
                             for char in potential_map_part:
                                 if char.isalnum() or char == '_':
                                     cleaned_map_part += char
                                 else:
                                     break # Stop at first invalid character
                             if cleaned_map_part and len(cleaned_map_part) > 1: # Avoid single letters
                                 guessed_map = f"{prefix}{cleaned_map_part}"
                                 if guessed_map not in self.known_maps:
                                     self.known_maps.append(guessed_map)
                                     self._log_activity_event(0, "Discovery", "INFO", f"Guessed map from player '{name}': {guessed_map}")
                                     self._add_map_related_files(guessed_map) # Add related files for guess
                                     added_count += 1
                         except IndexError:
                             continue # Split failed, prefix might be at end
                         except Exception as e:
                              logger.warning(f"Error guessing map from player name '{name}': {e}")
             # if added_count > 0: self._log_activity_event(0, "Discovery", "DEBUG", f"Finished player name map guessing cycle.")


    # --- Parse Resource Files ---
    def _parse_resource_files(self):
        """Scans the downloads directory for *.res files and extracts file references."""
        if not self.downloads_dir.exists():
             return # Nothing to scan if download dir doesn't exist

        res_files_found = 0
        files_added_total = 0
        try:
            # Use rglob to find *.res files recursively
            for res_file in self.downloads_dir.rglob("*.res"):
                res_files_found += 1
                try:
                    logger.debug(f"Parsing resource file: {res_file}")
                    with open(res_file, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()

                    # Simple regex to find quoted file paths (might need refinement)
                    # Looks for "path/to/file.ext" including those inside braces { }
                    # Handles forward and back slashes (normalized later)
                    # Excludes URLs starting with http/https
                    matches = re.findall(r'["\']((?!http[s]?:\/\/)[a-zA-Z0-9_\-\\\/\.]+?\.[a-zA-Z0-9]{2,4})["\']', content)
                    # Alternative: find quoted strings within braces specifically
                    # matches = re.findall(r'{\s*["\']([^"\']+)["\']\s*}', content)

                    newly_discovered_in_file = 0
                    for file_path_raw in matches:
                        # Normalize path (use forward slashes, lowercase?)
                        # Lowercasing might be too aggressive, keep case for now.
                        file_path_normalized = file_path_raw.replace('\\', '/').strip()

                        # Basic validation: non-empty, reasonable length, common extensions?
                        if file_path_normalized and len(file_path_normalized) > 3 and '.' in file_path_normalized:
                            with self.lock: # Protect access to discovered_files list
                                if file_path_normalized not in self.discovered_files:
                                    self.discovered_files.append(file_path_normalized)
                                    newly_discovered_in_file += 1
                                    files_added_total += 1
                                    self._log_activity_event(0, "Discovery", "DEBUG", f"Found in {res_file.name}: {file_path_normalized}")

                    if newly_discovered_in_file > 0:
                        self._log_activity_event(0, "Discovery", "INFO", f"Added {newly_discovered_in_file} new files from {res_file.name}")

                except FileNotFoundError:
                     logger.warning(f"Resource file {res_file} disappeared before parsing.")
                except IOError as e:
                    logger.warning(f"IOError reading resource file {res_file}: {e}")
                except Exception as e:
                    logger.error(f"Unexpected error parsing resource file {res_file}: {e}", exc_info=self.verbose)

        except Exception as scan_err:
            logger.error(f"Error scanning for resource files in {self.downloads_dir}: {scan_err}", exc_info=self.verbose)

        if res_files_found > 0:
             logger.info(f"Resource scan complete. Found {res_files_found} .res files, added {files_added_total} new file references.")


    # --- Realtime Display Thread ---
    def _display_realtime_stats(self):
        """Periodically refreshes the terminal with live statistics."""
        if self.verbose: logger.debug("Realtime display thread started.")
        last_bw_log_time = self.start_time
        term_width = 80 # Default terminal width
        try:
            # Try to get actual terminal width
            term_width = os.get_terminal_size().columns
        except OSError:
            logger.warning("Could not detect terminal width, using default 80.")

        while self.active and not self._stop_event.is_set():
            lines_to_print = [] # List to hold lines for the current screen update
            try:
                # --- Gather Data Under Lock ---
                # Copy necessary data from shared state to local variables
                with self.lock:
                    elapsed = time.time() - self.start_time if self.start_time > 0 else 0
                    # Download stats
                    bytes_received_total = self.bytes_received
                    downloads_ok = self.downloads_completed
                    downloads_fail = self.downloads_failed
                    # Worker stats
                    active_workers = self.active_workers_count
                    runtime_issues = self.runtime_connection_issues
                    initial_fails = self.initial_connection_failures
                    # Server status
                    current_server_status = self.server_status
                    current_ping = self.server_info.get('ping', -1) if self.server_info else -1
                    current_players = self.server_info.get('players', -1) if self.server_info else -1
                    current_max_players = self.server_info.get('max_players', -1) if self.server_info else -1
                    current_map = self.server_info.get('map', 'UNKNOWN') if self.server_info else 'UNKNOWN'
                    # Discovery stats
                    known_maps_count = len(self.known_maps)
                    discovered_files_count = len(self.discovered_files)
                    # Flood stats (copy the dicts)
                    ping_stats = self.ping_flood_stats.copy()
                    conn_stats = self.connection_flood_stats.copy()
                    # UI Activity
                    last_activity_list = list(self.last_activity) # Copy deque to list for safe iteration
                    # Test config
                    current_test_mode = self.test_mode
                    run_mode = "Continuous" if self.continuous_mode else f"Timed ({self.test_duration}s)"

                # --- Calculate Metrics ---
                recv_mb = bytes_received_total / (1024 * 1024)
                # Average rates over the *entire* test duration
                avg_rate_mbs = (recv_mb * 8) / elapsed if elapsed > 0 else 0  # Megabits/sec
                avg_rate_MBs = recv_mb / elapsed if elapsed > 0 else 0      # MegaBytes/sec

                # Log bandwidth point periodically (e.g., every second)
                current_time = time.time()
                if elapsed > 0 and (current_time - last_bw_log_time >= 1.0):
                    with self.lock: # Append to list under lock
                        self.bandwidth_log_points.append((round(elapsed, 2), round(avg_rate_MBs, 3)))
                    last_bw_log_time = current_time

                # --- Format Output Lines ---
                # Header
                header = f"--- CS 1.6 UDP Tester ({self.server_ip}:{self.server_port}) ---".center(term_width)
                lines_to_print.append(header)

                # Status Line
                status = "Running" if self.active else "Stopping..."
                mode_str = f"Mode: {current_test_mode.title()}"
                time_str = f"Time: {elapsed:.1f}s"
                status_line = f" Status: {status} | {run_mode} | {mode_str}"
                lines_to_print.append(f"{status_line:<{max(0, term_width - len(time_str))}}{time_str}") # Right-align time

                # Workers Line
                workers_str = f" Workers: {active_workers}/{self.num_connections}"
                issues_str = f"Issues: InitFails={initial_fails} Runtime={runtime_issues}"
                lines_to_print.append(f"{workers_str:<{max(0, term_width - len(issues_str))}}{issues_str}")

                lines_to_print.append("-" * term_width)

                # Server Status Section
                lines_to_print.append("[Server Status (UDP Query)]".center(term_width))
                if self.no_server_monitor:
                    lines_to_print.append(" UDP Monitoring Disabled".ljust(term_width))
                    lines_to_print.append(" Map: --- | Players: --- | Ping: ---".ljust(term_width))
                else:
                    s_status = f" Status: {current_server_status}"
                    s_ping = f"Ping: {current_ping:>3}ms" if current_ping >= 0 else "Ping: N/A"
                    s_players = f"Plyrs: {current_players}/{current_max_players}" if current_players >= 0 else "Plyrs: N/A"
                    # Combine Status | Ping | Players on one line
                    line1 = f"{s_status:<{term_width//3}} {s_ping:^{term_width//3}} {s_players:>{term_width//3}}"
                    lines_to_print.append(line1[:term_width].ljust(term_width)) # Ensure fits width

                    s_map = f" Map: {current_map}"
                    s_discover = f"Known Maps: {known_maps_count} | Found Files: {discovered_files_count}"
                    lines_to_print.append(s_map[:term_width].ljust(term_width))
                    lines_to_print.append(s_discover[:term_width].ljust(term_width))

                    # Display sv_allowdownload/sv_downloadurl if rules available
                    with self.lock: rules_copy = self.server_rules # Access under lock
                    if rules_copy:
                        dl_setting = rules_copy.get('sv_allowdownload', 'N/A')
                        dl_url = rules_copy.get('sv_downloadurl', '')
                        dl_line = f" sv_allowdownload={dl_setting}"
                        if dl_setting == '0': dl_line += " (UDP DL Disabled!)"
                        if dl_url: dl_line += f" | FastDL: {dl_url[:max(0,term_width-len(dl_line)-12)]}..."
                        lines_to_print.append(dl_line[:term_width].ljust(term_width))

                lines_to_print.append("-" * term_width)

                # Download Stats Section (if applicable)
                if current_test_mode == "download" or current_test_mode == "combined":
                    lines_to_print.append("[Download Activity & Bandwidth]".center(term_width))
                    dl_stats_line = f" Files OK: {downloads_ok} | Failed: {downloads_fail}"
                    dl_bytes_line = f"Total Recv: {recv_mb:>7.2f} MB"
                    lines_to_print.append(f"{dl_bytes_line:<{max(0, term_width - len(dl_stats_line))}}{dl_stats_line}")
                    # Bandwidth line
                    rate_line = f" Avg Rate: {avg_rate_mbs:>6.2f} Mbps ({avg_rate_MBs:>6.2f} MB/s)"
                    lines_to_print.append(rate_line.ljust(term_width))

                # Ping Flood Stats Section (if applicable)
                if current_test_mode == "ping_flood" or current_test_mode == "combined":
                    lines_to_print.append("[Ping Flood Stats]".center(term_width))
                    ping_line = f" Pings: Sent {ping_stats['pings_sent']} | Recv {ping_stats['pings_received']} | Resp {ping_stats['response_rate']:.1f}%"
                    lines_to_print.append(ping_line[:term_width].ljust(term_width))
                    rate_line = f" Rate: {ping_stats['packets_per_sec']:.1f} pings/s | Avg Ping: {ping_stats['avg_ping']:.1f} ms"
                    lines_to_print.append(rate_line[:term_width].ljust(term_width))

                # Connection Flood Stats Section (if applicable)
                if current_test_mode == "connection_flood" or current_test_mode == "combined":
                    lines_to_print.append("[Connection Flood Stats]".center(term_width))
                    conn_line = f" Conns: Attempt {conn_stats['connections_attempted']} | Replies {conn_stats['connections_successful']} | Reply% {conn_stats['success_rate']:.1f}%"
                    lines_to_print.append(conn_line[:term_width].ljust(term_width))
                    rate_line = f" Rate: {conn_stats['connections_per_sec']:.1f} attempts/s"
                    lines_to_print.append(rate_line[:term_width].ljust(term_width))

                lines_to_print.append("-" * term_width)

                # Last Activity Section
                lines_to_print.append(f"[Last {LAST_FILES_DISPLAY_COUNT} Activities]".center(term_width))
                if last_activity_list:
                    # Print activities in reverse order (newest first)
                    for activity in reversed(last_activity_list):
                         # Truncate and pad activity string to fit width
                        lines_to_print.append(f" {activity[:term_width-2].ljust(term_width-2)}")
                    # Fill remaining lines with blanks if fewer activities than display count
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - len(last_activity_list))):
                        lines_to_print.append(" ".ljust(term_width))
                else:
                    lines_to_print.append("  (No activity yet)".ljust(term_width))
                    # Fill remaining lines
                    for _ in range(max(0, LAST_FILES_DISPLAY_COUNT - 1)):
                        lines_to_print.append(" ".ljust(term_width))

                lines_to_print.append("-" * term_width)
                lines_to_print.append("(Press Ctrl+C to stop)".center(term_width))

                # --- Screen Update ---
                output_buffer = CURSOR_TO_HOME # Move cursor to top-left
                for line in lines_to_print:
                    # Ensure line fits terminal width, clear rest of line, add newline
                    output_buffer += line[:term_width] + CLEAR_LINE + "\n"
                # Clear any potential leftover lines below the output area
                output_buffer += CLEAR_SCREEN_FROM_CURSOR
                sys.stdout.write(output_buffer)
                sys.stdout.flush() # Force update to terminal

            except Exception as e:
                # Log errors occurring within the display loop itself
                logger.error(f"Display thread error: {e}", exc_info=False) # Avoid spamming tracebacks
                # Short sleep to prevent tight error loop
                time.sleep(1)

            # Wait efficiently using stop event for the UI update interval
            if self._stop_event.wait(timeout=UI_UPDATE_INTERVAL):
                break # Exit loop immediately if stop event is set during wait

        # --- Cleanup Terminal on Exit ---
        logger.debug("Realtime display thread finished.")
        try:
            # Move cursor home and clear screen from cursor down
            sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
            sys.stdout.flush()
        except Exception as e:
            logger.debug(f"Error clearing screen on display thread exit: {e}")


    # --- Resource Scanner Thread ---
    def _resource_scanner_thread(self):
        """Periodically checks the downloads directory for *.res files and parses them."""
        if not (self.test_mode == "download" or self.test_mode == "combined"):
             logger.debug("Resource scanner disabled (not in download/combined mode).")
             return # Only run if downloading files

        logger.debug("Resource scanner thread started.")
        scan_interval = 15  # Check for new .res files every 15 seconds

        while self.active and not self._stop_event.is_set():
            # Wait for the scan interval, interruptible by stop event
            if self._stop_event.wait(timeout=scan_interval):
                break # Exit if stopped during wait

            if self._stop_event.is_set(): break # Check again after wait

            logger.debug("Resource scanner starting scan...")
            self._parse_resource_files() # Perform the scan and parse logic
            logger.debug("Resource scanner finished scan.")

        logger.debug("Resource scanner thread finished.")


    # --- Start/Stop Methods ---
    def start_test(self):
        """Initializes and starts the test threads."""
        if self.active:
            logger.warning("Test is already running.")
            return

        logger.info("=" * 30 + f" Starting UDP {self.test_mode.title()} Test " + "=" * 30)
        self.active = True # Set test as active
        self._stop_event.clear() # Ensure stop event is not set
        self.start_time = time.time() # Record start time
        self.end_time = 0 # Reset end time

        # --- Reset Counters and State ---
        logger.debug("Resetting statistics and state...")
        self.bytes_received = 0
        self.downloads_completed = 0
        self.downloads_failed = 0
        self.initial_connection_failures = 0
        self.runtime_connection_issues = 0
        self.active_workers_count = 0
        self.bandwidth_log_points = []
        self.last_activity.clear()

        # Reset flood stats aggregators
        self.ping_flood_stats = {'pings_sent': 0, 'pings_received': 0, 'response_rate': 0.0, 'packets_per_sec': 0.0, 'avg_ping': 0.0}
        self._ping_flood_total_ping_ms = 0
        self._ping_flood_reports = 0
        self.connection_flood_stats = {'connections_attempted': 0, 'connections_successful': 0, 'success_rate': 0.0, 'connections_per_sec': 0.0}
        self._conn_flood_total_rate = 0
        self._conn_flood_reports = 0

        # Reset Server State
        self.server_status = "MONITORING_DISABLED" if self.no_server_monitor else "STARTING"
        self.server_last_seen = 0
        self.server_info = None
        self.server_rules = None
        self.server_status_log = []
        self.threads = [] # Clear thread list from previous runs
        self.connections = [] # Clear connection info list

        # --- Initialize File/Map Lists ---
        # Pre-populate known maps with some common ones
        self.known_maps = ["de_dust2", "de_inferno", "cs_office", "cs_assault"] # Start with a few popular maps
        # Pre-populate discovered files (add more variety)
        # Start with common files likely present on many servers
        self.discovered_files = [
            "models/player/arctic/arctic.mdl",
            "models/player/guerilla/guerilla.mdl",
            "models/player/leet/leet.mdl",
            "models/player/gign/gign.mdl",
            "models/player/sas/sas.mdl",
            "models/player/terror/terror.mdl",
            "models/player/urban/urban.mdl",
            "models/player/vip/vip.mdl",
            "sprites/640hud1.spr", "sprites/640hud2.spr", "sprites/640hud7.spr",
            "sprites/hud.txt",
            "sprites/crosshairs.spr",
            "sound/weapons/ak47-1.wav", "sound/weapons/m4a1-1.wav",
            "sound/items/gunpickup.wav",
            "sound/player/die1.wav",
            "maps/de_dust2.res", # Try to grab a common .res file early
        ]
        logger.debug(f"Initialized with {len(self.known_maps)} known maps and {len(self.discovered_files)} common files.")

        # --- Start Monitor Thread (if enabled) ---
        if not self.no_server_monitor:
            # Recreate ServerQuery if it wasn't created or was closed
            if not self.server_query:
                try:
                    self.server_query = ServerQuery(self.server_ip, self.server_port, storage_dir=str(self.storage_dir))
                    logger.debug("ServerQuery instance recreated.")
                except Exception as e:
                     logger.error(f"Failed to recreate ServerQuery instance: {e}. Monitoring disabled.")
                     self.no_server_monitor = True # Disable monitoring if creation fails
                     self.server_status = "MONITORING_DISABLED"

            if not self.no_server_monitor: # Check again in case creation failed
                 self.server_info_thread = threading.Thread(target=self._update_server_info, name="ServerMon", daemon=True)
                 self.server_info_thread.start()
                 self.threads.append(self.server_info_thread)
                 logger.debug("Server monitoring thread started.")
        else:
            self.server_info_thread = None # Ensure it's None if disabled

        # --- Start Display Thread ---
        self.display_thread = threading.Thread(target=self._display_realtime_stats, name="Display", daemon=True)
        self.display_thread.start()
        self.threads.append(self.display_thread)
        logger.debug("Realtime display thread started.")

        # --- Start Resource Scanner Thread (if downloading) ---
        if self.test_mode == "download" or self.test_mode == "combined":
            self.resource_scanner_thread = threading.Thread(target=self._resource_scanner_thread, name="ResScanner", daemon=True)
            self.resource_scanner_thread.start()
            self.threads.append(self.resource_scanner_thread)
            logger.debug("Resource scanner thread started.")

        # --- Initial Server Download Settings Check (if monitoring) ---
        # Do a quick check *before* starting workers if monitoring is enabled
        if not self.no_server_monitor and self.server_query:
            logger.info("Checking server download settings before starting workers...")
            try:
                # Short delay to allow monitor thread to potentially get initial info/rules
                time.sleep(0.5)
                rules = None
                with self.lock: # Access rules safely
                    rules = self.server_rules
                if not rules: # If monitor hasn't got them yet, try a direct query
                    logger.debug("Rules not available yet, attempting direct query...")
                    rules = self.server_query.get_rules()
                    if rules:
                        with self.lock: self.server_rules = rules # Store if successful
                    else:
                         logger.warning("Failed to get server rules for initial check.")

                if rules:
                    self._check_download_rules(rules) # Use helper to log warnings
                else:
                     logger.warning("Could not retrieve server rules to check download settings.")

            except Exception as e:
                logger.error(f"Error during initial check of server download settings: {e}")

        # --- Start Worker Threads ---
        logger.info(f"Starting {self.num_connections} worker threads...")
        launched_count = 0
        for i in range(self.num_connections):
            if self._stop_event.is_set():
                logger.warning("Stop event received during worker startup. Aborting.")
                break

            # Create structure to hold worker state and resources
            conn_info = {"id": i + 1, "downloader": None, "flooder": None, "conn_flooder": None,
                         "status": "init", "current_task": "Initializing", "last_activity_time": 0}
            self.connections.append(conn_info) # Add structure *before* starting thread

            # Create and start the worker thread
            worker_thread = threading.Thread(target=self._connection_worker, args=(conn_info,), name=f"Worker-{i+1}", daemon=True)
            try:
                worker_thread.start()
                self.threads.append(worker_thread) # Add to list of active threads
                launched_count += 1
                # Stagger worker starts slightly, especially for high counts
                if self.num_connections > 10:
                     time.sleep(0.01 + (i * 0.001)) # Increasingly small delay
                elif self.num_connections > 1:
                    time.sleep(0.01)

            except threading.ThreadError as e:
                logger.error(f"Failed to start worker {i+1}: {e}")
                self._increment_counter("initial_connection_failures")
                conn_info["status"] = "start_error"
                conn_info["current_task"] = "Start Failed"
                # Worker structure remains in self.connections for reporting

        logger.info(f"Launched {launched_count} of {self.num_connections} workers.")
        if launched_count == 0 and self.num_connections > 0:
            logger.critical("FATAL: No workers were successfully launched. Stopping test.")
            # Use a separate thread to initiate stop_test to avoid potential deadlocks
            threading.Thread(target=self.stop_test, daemon=True).start()
            return # Exit start_test method

        # --- Main Test Loop (Wait for Duration or Stop Signal) ---
        logger.info(f"Test running... Mode: {run_mode}")
        try:
            if self.continuous_mode:
                # In continuous mode, wait indefinitely until stop_event is set
                logger.info("Running in continuous mode. Press Ctrl+C to stop.")
                self._stop_event.wait() # Blocks until event is set
                logger.info("Stop event received by main thread.")
            else:
                # In timed mode, wait for the specified duration or until stop_event is set
                logger.info(f"Running timed test for {self.test_duration} seconds. Press Ctrl+C to stop early.")
                stopped_early = self._stop_event.wait(timeout=self.test_duration)
                if stopped_early:
                    logger.info("Test stopped early by signal or error.")
                else:
                    logger.info("Test duration reached.")
                    # Explicitly call stop_test if duration completed naturally
                    # Check if already stopping to prevent double call
                    if not self._stop_event.is_set():
                         self.stop_test()

        except KeyboardInterrupt:
            # This might be caught here if signal handler is slow, or directly by the handler
            logger.warning("KeyboardInterrupt caught in main wait loop. Initiating shutdown...")
            # Ensure stop_test is called only once
            if not self._stop_event.is_set():
                # Run stop_test in a thread to avoid blocking signal handler context if applicable
                threading.Thread(target=self.stop_test, daemon=True).start()
        except Exception as e:
            logger.error(f"Error in main test loop: {e}", exc_info=self.verbose)
            # Ensure stop is called on error if not already stopping
            if not self._stop_event.is_set():
                threading.Thread(target=self.stop_test, daemon=True).start()

        logger.debug("Main test execution scope finished.")


    def stop_test(self):
        """Signals all threads to stop and waits for them to finish."""
        # Prevent multiple stop calls or stopping if not active
        # Use lock for atomicity check/set? Small race condition possible otherwise.
        with self.lock:
            if not self.active or self._stop_event.is_set():
                logger.debug("Stop test called but already stopping or inactive.")
                return
            logger.info("Initiating test shutdown...")
            self.active = False         # Signal loops in workers/monitors to stop iterating
            self._stop_event.set()      # Signal threads waiting on the event to wake up

        self.end_time = time.time()  # Record exact end time

        logger.info("Waiting for threads to finish (max 5s)...")
        join_timeout = 5.0
        start_join_time = time.time()

        # Make a copy of the thread list to join - avoids modifying list while iterating
        # Threads might remove themselves or finish concurrently.
        threads_to_join = self.threads[:]
        self.threads = [] # Clear original list

        for thread in threads_to_join:
            if thread is threading.current_thread() or not thread.is_alive():
                # logger.debug(f"Skipping join for thread {thread.name} (current or not alive).")
                continue
            try:
                # Calculate remaining timeout for this thread
                remaining_timeout = max(0.1, join_timeout - (time.time() - start_join_time))
                if self.verbose: logger.debug(f"Joining {thread.name} (Timeout: {remaining_timeout:.1f}s)...")
                thread.join(remaining_timeout)
                if thread.is_alive():
                    logger.warning(f"Thread {thread.name} did not stop within timeout.")
                # else: logger.debug(f"Thread {thread.name} joined successfully.")
            except Exception as e:
                logger.warning(f"Error joining thread {thread.name}: {e}")

        logger.info("Thread joining process complete.")

        # --- Close Resources Held by Workers/Monitors ---
        logger.debug("Closing worker/monitor resources...")
        # Close ServerQuery socket (if monitor was active)
        if self.server_query:
            logger.debug("Closing server query socket...")
            self.server_query.close()
            self.server_query = None # Clear reference

        # Close resources held by worker connection structures
        resources_closed_count = 0
        for conn_info in self.connections:
            # Close downloader
            downloader = conn_info.get("downloader")
            if downloader:
                try:
                    downloader.close()
                    resources_closed_count += 1
                    conn_info["downloader"] = None # Clear reference
                except Exception: pass # Ignore close errors during shutdown

            # Close ping flooder socket
            flooder = conn_info.get("flooder")
            if flooder:
                try:
                    flooder.close()
                    resources_closed_count += 1
                    conn_info["flooder"] = None
                except Exception: pass

            # Connection flooder (doesn't hold persistent socket in this impl)
            conn_flooder = conn_info.get("conn_flooder")
            if conn_flooder:
                conn_info["conn_flooder"] = None # Just clear reference

        if resources_closed_count > 0:
             logger.debug(f"Closed {resources_closed_count} worker resources during shutdown.")

        # --- Final Actions ---
        # Close log file handlers *after* all threads have stopped logging
        self._close_activity_logger()
        self._close_download_logger()

        # Ensure display is cleared *before* printing final report
        try:
            sys.stdout.write(CURSOR_TO_HOME + CLEAR_SCREEN_FROM_CURSOR)
            sys.stdout.flush()
        except Exception as e:
            logger.warning(f"Failed to clear screen for final report: {e}")

        print("\n" + "=" * 72) # Add separation

        # Generate and Print Final Report
        final_elapsed = self.end_time - self.start_time if self.start_time > 0 else 0
        try:
            self._generate_final_report(final_elapsed)
            self._save_detailed_report_json(final_elapsed)
        except Exception as e:
            logger.error(f"Error generating final report: {e}", exc_info=True)

        logger.info("Test finished.")


    def _close_activity_logger(self):
        """Finds and closes the activity log file handler."""
        logger.debug("Attempting to close activity log file handler...")
        closed_count = 0
        # Use list comprehension to find handler(s) and remove safely
        handlers_to_remove = [h for h in activity_logger.handlers if isinstance(h, logging.FileHandler)]

        if not handlers_to_remove:
            logger.debug("No active file handler found for activity logger.")
            return

        for handler in handlers_to_remove:
            handler_name = handler.baseFilename if hasattr(handler, 'baseFilename') else str(handler)
            try:
                # Ensure log buffer is flushed before closing
                handler.flush()
                # Add closing message directly to the stream if possible
                if hasattr(handler, 'stream') and not handler.stream.closed:
                     handler.stream.write(f"\n--- Activity Log Ended ({datetime.now().isoformat()}) ---\n")
                handler.close()
                activity_logger.removeHandler(handler) # Remove handler to prevent duplicates on restart
                logger.debug(f"Closed and removed activity log handler: {handler_name}")
                closed_count += 1
            except Exception as e:
                logger.warning(f"Error closing activity log handler ({handler_name}): {e}")
        if closed_count == 0 and handlers_to_remove:
             logger.warning("Found activity log handlers but failed to close them.")

    def _close_download_logger(self):
        """Finds and closes the download debug log file handler."""
        logger.debug("Attempting to close download log file handler...")
        closed_count = 0
        handlers_to_remove = [h for h in download_logger.handlers if isinstance(h, logging.FileHandler)]

        if not handlers_to_remove:
            logger.debug("No active file handler found for download logger.")
            return

        for handler in handlers_to_remove:
            handler_name = handler.baseFilename if hasattr(handler, 'baseFilename') else str(handler)
            try:
                handler.flush()
                if hasattr(handler, 'stream') and not handler.stream.closed:
                    handler.stream.write(f"\n--- Download Debug Log Ended ({datetime.now().isoformat()}) ---\n")
                handler.close()
                download_logger.removeHandler(handler)
                logger.debug(f"Closed and removed download log handler: {handler_name}")
                closed_count += 1
            except Exception as e:
                logger.warning(f"Error closing download log handler ({handler_name}): {e}")
        if closed_count == 0 and handlers_to_remove:
             logger.warning("Found download log handlers but failed to close them.")


    # --- Reporting Methods ---
    def _generate_final_report(self, duration):
        """Prints a summary report to the console."""
        print(f"\n" + "=" * 30 + f" UDP {self.test_mode.title()} Test Results " + "=" * 30)
        duration = max(duration, 0.01) # Avoid division by zero

        # Gather final stats safely (copy values)
        with self.lock:
            bytes_recv = self.bytes_received
            downloads_ok = self.downloads_completed
            downloads_fail = self.downloads_failed
            runtime_issues = self.runtime_connection_issues
            initial_fails = self.initial_connection_failures
            final_server_status = self.server_status
            server_log = self.server_status_log[:] # Copy list
            known_maps_count = len(self.known_maps)
            discovered_files_count = len(self.discovered_files)
            ping_stats = self.ping_flood_stats.copy()
            conn_stats = self.connection_flood_stats.copy()
            final_map = self.server_info.get('map', 'UNKNOWN') if self.server_info else 'UNKNOWN'
            final_players = self.server_info.get('players', -1) if self.server_info else -1
            final_max_players = self.server_info.get('max_players', -1) if self.server_info else -1
            final_rules = self.server_rules.copy() if self.server_rules else None

        # --- Calculate Overview Metrics ---
        recv_mb = bytes_recv / (1024 * 1024)
        avg_rate_mbs = (recv_mb * 8) / duration  # Megabits/sec
        avg_rate_MBs = recv_mb / duration      # MegaBytes/sec

        # Calculate server ping stats from log
        avg_ping = -1
        min_ping = -1
        max_ping = -1
        online_duration = 0
        last_online_time = -1
        if not self.no_server_monitor and server_log:
            pings = [log['ping'] for log in server_log if log.get('status') == 'ONLINE' and log.get('ping', -1) >= 0]
            if pings:
                avg_ping = sum(pings) / len(pings)
                min_ping = min(pings)
                max_ping = max(pings)

            # Calculate rough online time based on log entries
            start_test_time = self.start_time
            end_test_time = self.end_time if self.end_time > 0 else time.time()
            # Ensure log timestamps are relative to test start/end if possible
            # Assuming timestamps in log are absolute time.time() values
            for i, log in enumerate(server_log):
                current_ts = log['timestamp']
                # Clamp timestamp to test duration for calculation
                current_ts_clamped = max(start_test_time, min(current_ts, end_test_time))

                if log.get('status') == 'ONLINE':
                    if last_online_time < 0: # Start of an online period within the test
                        last_online_time = current_ts_clamped
                    # If this is the last log entry and it's online, count duration to end of test
                    if i == len(server_log) - 1:
                         online_duration += (end_test_time - last_online_time)
                else: # Status is not ONLINE (or first entry is not ONLINE)
                    if last_online_time >= 0: # End of an online period
                        prev_log_ts_clamped = max(start_test_time, min(server_log[i-1]['timestamp'], end_test_time)) if i > 0 else start_test_time
                        online_duration += (current_ts_clamped - last_online_time)
                    last_online_time = -1 # Reset start of online period tracker

            online_duration = max(0, online_duration) # Ensure non-negative


        # --- Print Report Sections ---
        print(f"[Test Overview]")
        print(f" Target Server:   {self.server_ip}:{self.server_port}")
        print(f" Test Mode:       {self.test_mode.title()}")
        print(f" Duration:        {duration:.2f}s")
        print(f" Config Workers:  {self.num_connections}")
        print(f" Initial Fails:   {initial_fails}")
        print(f" Runtime Issues:  {runtime_issues}")
        print(f" Storage Dir:     {self.storage_dir}")

        # --- Download Results ---
        if self.test_mode == "download" or self.test_mode == "combined":
            print(f"\n[Download Results]")
            print(f" Files OK:        {downloads_ok}")
            print(f" Files Failed:    {downloads_fail}")
            print(f" Total Received:  {recv_mb:.2f} MB")
            print(f" Avg Rate:        {avg_rate_mbs:.2f} Mbps ({avg_rate_MBs:.2f} MB/s)")
            print(f" Discovered Maps: {known_maps_count}")
            print(f" Resource Files:  {discovered_files_count}")

        # --- Ping Flood Results ---
        if self.test_mode == "ping_flood" or self.test_mode == "combined":
            print(f"\n[Ping Flood Results]")
            print(f" Pings Sent:      {ping_stats['pings_sent']}")
            print(f" Pings Received:  {ping_stats['pings_received']}")
            print(f" Response Rate:   {ping_stats['response_rate']:.1f}%")
            # Use the final calculated average rate/ping
            print(f" Avg Rate:        {ping_stats['packets_per_sec']:.1f} pings/s")
            print(f" Avg Ping:        {ping_stats['avg_ping']:.1f} ms")

        # --- Connection Flood Results ---
        if self.test_mode == "connection_flood" or self.test_mode == "combined":
            print(f"\n[Connection Flood Results]")
            print(f" Conn Attempts:   {conn_stats['connections_attempted']}")
            print(f" Server Replies:  {conn_stats['connections_successful']}") # Clarify 'successful' means 'got reply'
            print(f" Reply Rate:      {conn_stats['success_rate']:.1f}%")
            print(f" Avg Rate:        {conn_stats['connections_per_sec']:.1f} attempts/s")

        # --- Server Status Summary ---
        print(f"\n[Server Status (UDP Query)]")
        if self.no_server_monitor:
            print(" Monitoring:      Disabled")
        else:
            print(f" Final Status:    {final_server_status}")
            print(f" Final Map:       {final_map}")
            print(f" Final Players:   {final_players}/{final_max_players}" if final_players >= 0 else "Players: N/A")
            print(f" Avg Ping (Live): {avg_ping:.1f} ms" if avg_ping != -1 else "Avg Ping: N/A")
            print(f" Ping Min/Max:    {min_ping}/{max_ping} ms" if min_ping != -1 else "Ping Range: N/A")
            online_perc = (online_duration / duration * 100) if duration > 0 else 0
            print(f" Est. Online:     {online_duration:.1f}s / {duration:.1f}s ({online_perc:.1f}%)")

            # Print relevant download settings from final rules
            if final_rules:
                dl_setting = final_rules.get('sv_allowdownload', 'N/A')
                dl_url = final_rules.get('sv_downloadurl', '')
                print(f" sv_allowdownload:{dl_setting}")
                if dl_url:
                    print(f" sv_downloadurl:  {dl_url}")
            else:
                 print(" Server rules:    Not available")

        print("=" * 72)


    def _save_detailed_report_json(self, duration):
        """Saves a detailed report in JSON format."""
        duration = max(0.01, duration) # Avoid division by zero

        # Gather final stats safely
        with self.lock:
            total_recv_bytes = self.bytes_received
            downloads_ok = self.downloads_completed
            downloads_fail = self.downloads_failed
            initial_fails = self.initial_connection_failures
            runtime_issues = self.runtime_connection_issues
            server_log_copy = self.server_status_log[:]
            # Take snapshot of final server info/rules/files under lock
            final_server_info_snapshot = self.server_info.copy() if self.server_info else None
            final_rules_snapshot = self.server_rules.copy() if self.server_rules else None
            known_maps_copy = self.known_maps[:]
            discovered_files_copy = self.discovered_files[:]
            ping_stats_copy = self.ping_flood_stats.copy()
            conn_stats_copy = self.connection_flood_stats.copy()
            bandwidth_log_copy = self.bandwidth_log_points[:]

        # --- Build Report Dictionary ---
        report_data = {
            "test_info": {
                "test_type": f"CS_UDP_{self.test_mode.title()}_Test",
                "script_version": "2.1", # Example version
                "target_server": f"{self.server_ip}:{self.server_port}",
                "timestamp_start_utc": datetime.utcfromtimestamp(self.start_time).isoformat() + "Z" if self.start_time else None,
                "timestamp_end_utc": datetime.utcfromtimestamp(self.end_time).isoformat() + "Z" if self.end_time else None,
                "duration_seconds": round(duration, 2),
                "configured_workers": self.num_connections,
                "initial_connection_failures": initial_fails,
                "runtime_connection_issues": runtime_issues,
                "test_run_mode": "Continuous" if self.continuous_mode else "Timed",
                "server_udp_monitoring_enabled": not self.no_server_monitor,
                "verbose_logging_enabled": self.verbose,
                "storage_directory": str(self.storage_dir.resolve()),
                "activity_log_file": str(self.activity_log_filepath.resolve()) if self.activity_log_filepath else None,
                "download_log_file": str(self.download_log_filepath.resolve()) if self.download_log_filepath else None,
                "download_directory": str(self.downloads_dir.resolve()) if (self.test_mode=="download" or self.test_mode=="combined") else None
            },
            # Bandwidth summary always included, even if 0 for non-download tests
            "bandwidth_summary": {
                "total_received_bytes": total_recv_bytes,
                "total_received_mb": round(total_recv_bytes / (1024 * 1024), 3),
                "avg_total_rate_mbs": round((total_recv_bytes * 8) / (1024 * 1024) / duration, 3),  # Mbps
                "avg_total_rate_MBs": round((total_recv_bytes / (1024 * 1024)) / duration, 3),  # MB/s
                "bandwidth_log_points_sec_MBs": bandwidth_log_copy # List of [elapsed_sec, rate_MBs]
            },
            # Server status section
             "server_status_summary": {
                 "final_snapshot": final_server_info_snapshot,
                 "final_rules": final_rules_snapshot,
                 "monitoring_log": server_log_copy # Full log of status changes
             },
             # Discovery section
             "discovery_summary": {
                 "known_maps": known_maps_copy,
                 "discovered_files": discovered_files_copy,
                 "known_maps_count": len(known_maps_copy),
                 "discovered_files_count": len(discovered_files_copy)
             }
        }

        # --- Add Module-Specific Sections ---
        if self.test_mode == "download" or self.test_mode == "combined":
            report_data["download_stats"] = {
                "files_succeeded": downloads_ok,
                "files_failed": downloads_fail,
            }

        if self.test_mode == "ping_flood" or self.test_mode == "combined":
            report_data["ping_flood_stats"] = ping_stats_copy

        if self.test_mode == "connection_flood" or self.test_mode == "combined":
            report_data["connection_flood_stats"] = conn_stats_copy

        # Optional: Clean None values recursively for cleaner JSON output
        def remove_none_values(d):
            """Recursively remove keys with None values from dicts/lists."""
            if isinstance(d, dict):
                return {k: remove_none_values(v) for k, v in d.items() if v is not None}
            elif isinstance(d, list):
                # Filter out None items from list too? Or just recurse? Recurse for now.
                return [remove_none_values(item) for item in d] # Keep list structure, remove None within items
            else:
                return d
        # report_data = remove_none_values(report_data) # Uncomment to enable cleaning

        # --- Save JSON File ---
        ts_filename = datetime.now().strftime("%Y%m%d_%H%M%S")
        report_filename = f"cs_udp_{self.test_mode}_report_{self.server_ip.replace('.', '_')}_{self.server_port}_{ts_filename}.json"
        report_filepath = self.storage_dir / report_filename
        try:
            with open(report_filepath, 'w', encoding='utf-8') as f:
                 # indent=2 for readability, ensure_ascii=False for potential non-latin chars in names/maps
                json.dump(report_data, f, indent=2, ensure_ascii=False)
            logger.info(f"Detailed JSON report saved to: {report_filepath.resolve()}")
        except TypeError as e:
             logger.error(f"Failed to serialize report data to JSON: {e}. Check for non-serializable types.")
             # Attempt to save with default=str as fallback
             try:
                 with open(report_filepath, 'w', encoding='utf-8') as f:
                      json.dump(report_data, f, indent=2, ensure_ascii=False, default=str)
                 logger.info(f"Detailed JSON report saved (with string conversion fallback) to: {report_filepath.resolve()}")
             except Exception as e2:
                  logger.error(f"Failed to save JSON report '{report_filepath}' even with fallback: {e2}")
        except Exception as e:
            logger.error(f"Failed to save JSON report '{report_filepath}': {e}")


# ==============================================================
# Signal Handling
# ==============================================================
def signal_handler(sig, frame):
    """Handles Ctrl+C (SIGINT) and SIGTERM for graceful shutdown."""
    global tester_instance
    signal_name = signal.Signals(sig).name
    print('') # Print newline to avoid messing up current log line/UI

    if tester_instance and tester_instance.active and not tester_instance._stop_event.is_set():
        logger.warning(f"{signal_name} received! Initiating graceful shutdown...")
        # Run stop_test in a separate thread to avoid blocking the signal handler
        # and potential deadlocks if lock is held by main thread.
        threading.Thread(target=tester_instance.stop_test, daemon=True).start()
    elif tester_instance and tester_instance._stop_event.is_set():
        logger.info(f"{signal_name} received, but shutdown already in progress.")
        # Force exit if received multiple times? Maybe after a delay.
    else:
        # If tester isn't active or doesn't exist (e.g., error during init)
        logger.warning(f'{signal_name} received, tester not active or instance invalid. Exiting immediately.')
        # Attempt basic cleanup (close log files if possible)
        try:
             for logger_obj in [activity_logger, download_logger, logger]:
                 for handler in logger_obj.handlers[:]:
                     if isinstance(handler, logging.FileHandler):
                         handler.close()
        except Exception: pass # Ignore errors during emergency cleanup
        sys.exit(1) # Exit with error code

# ==============================================================
# Main execution block
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="CS 1.6 UDP File Downloader and Network Stress Tester.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter # Show default values in help
    )

    # --- Server Arguments ---
    server_group = parser.add_argument_group('Server Configuration')
    server_group.add_argument("server_ip", help="IP address or hostname of the CS 1.6 GAME server.")
    server_group.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help="GAME server UDP port.")

    # --- Test Control Arguments ---
    control_group = parser.add_argument_group('Test Control')
    control_group.add_argument("-c", "--connections", type=int, default=5, metavar='N',
                             help="Number of concurrent workers/connections.")
    control_group.add_argument("-d", "--duration", type=int, default=60, metavar='SEC',
                             help="Duration of timed test in seconds. Ignored if --continuous is set.")
    control_group.add_argument("--continuous", action="store_true",
                             help="Run continuously until stopped (Ctrl+C). Overrides --duration.")

    # --- Test Mode Selection ---
    mode_group = parser.add_argument_group('Test Mode Selection')
    mode_group.add_argument("-m", "--mode", choices=["download", "ping_flood", "connection_flood", "combined"],
                           default="download", help="Select the test mode to run.")
    # Mode-specific parameters
    mode_params = parser.add_argument_group('Mode Parameters')
    mode_params.add_argument("--ping-rate", type=float, default=10.0, metavar='PPS',
                           help="Target rate for ping flood (pings per second per worker).")
    mode_params.add_argument("--connection-rate", type=float, default=2.0, metavar='CPS',
                          help="Target rate for connection flood (connection attempts per second per worker).")

    # --- Output & Logging Arguments ---
    output_group = parser.add_argument_group('Output and Logging')
    output_group.add_argument("--storage-dir", default="cs_udp_test_output", metavar='DIR',
                            help="Directory for logs, reports, and downloaded files.")
    output_group.add_argument("--activity-log", default=ACTIVITY_LOG_FILENAME, metavar='FILE',
                            help="Filename within storage-dir for logging detailed activity.")
    output_group.add_argument("--download-log", default=DOWNLOAD_LOG_FILENAME, metavar='FILE',
                            help="Filename within storage-dir for download protocol debug info.")
    output_group.add_argument("-v", "--verbose", action="store_true",
                            help="Enable verbose DEBUG logging to console and activity log.")
    output_group.add_argument("--no-server-monitor", action="store_true",
                            help="Disable querying game server status (info/rules/ping) via UDP.")
    # Example: Add argument to disable UDP verification file saving/deleting
    # output_group.add_argument("--no-udp-verify", action="store_true",
    #                         help="Disable the save/delete verification for UDP query responses.")


    args = parser.parse_args()

    # --- Configure Root Logger Level (Console Output) ---
    # Set level based on verbose flag
    log_level = logging.DEBUG if args.verbose else logging.INFO
    logger.setLevel(log_level)
    # Ensure the default StreamHandler (to stderr) respects the level
    # This assumes the default handler is the first one or the only StreamHandler
    for handler in logging.getLogger().handlers:
        if isinstance(handler, logging.StreamHandler):
            handler.setLevel(log_level)
            # Optional: Add more specific formatting for console
            # console_formatter = logging.Formatter('%(asctime)s [%(levelname)-5s] %(message)s', datefmt='%H:%M:%S')
            # handler.setFormatter(console_formatter)
            break # Assume only one console handler to configure

    # --- Display Startup Warnings & Info ---
    logger.warning("=" * 70)
    logger.warning(" CS 1.6 UDP Network Tester ".center(70))
    logger.warning("=" * 70)
    if args.mode == "download" or args.mode == "combined":
        logger.warning("⚠️ DOWNLOAD mode will attempt to download REAL files from the server.")
        logger.warning("   This consumes server bandwidth and saves files locally.")
    if args.mode == "ping_flood" or args.mode == "combined":
        logger.warning("⚠️ PING FLOOD mode sends rapid UDP packets to test server responsiveness.")
        logger.warning(f"   Target rate: {args.connections} workers * {args.ping_rate:.1f} pps = {args.connections * args.ping_rate:.1f} pps total.")
    if args.mode == "connection_flood" or args.mode == "combined":
        logger.warning("⚠️ CONNECTION FLOOD mode attempts simplified connections rapidly.")
        logger.warning(f"   Target rate: {args.connections} workers * {args.connection_rate:.1f} cps = {args.connections * args.connection_rate:.1f} cps total.")
    if args.no_server_monitor:
        logger.info("   Server UDP monitoring (Info/Rules/Ping) is DISABLED.")
    else:
        logger.info("   Server UDP monitoring (Info/Rules/Ping) is ENABLED.")
    logger.warning("-" * 70)
    logger.warning("❗ Ensure you have permission before testing any server.")
    logger.warning("❗ Use this tool responsibly and ethically.")
    logger.warning("=" * 70)
    time.sleep(2.5) # Pause for user to read warnings

    # --- Initialize and Run Tester ---
    try:
        # Create the main tester instance
        tester_instance = CS16BandwidthTester(
            server_ip=args.server_ip,
            server_port=args.port,
            num_connections=args.connections,
            test_duration=args.duration,
            verbose=args.verbose,
            storage_dir=args.storage_dir,
            continuous_mode=args.continuous,
            no_server_monitor=args.no_server_monitor,
            test_mode=args.mode,
            ping_rate=args.ping_rate,
            connection_rate=args.connection_rate,
            activity_log_filename=args.activity_log,
            download_log_filename=args.download_log
            # Pass other args like --no-udp-verify if added:
            # udp_verify_enabled = not args.no_udp_verify
        )

        # --- Register Signal Handlers *after* tester_instance is created ---
        signal.signal(signal.SIGINT, signal_handler)   # Handle Ctrl+C
        signal.signal(signal.SIGTERM, signal_handler)  # Handle termination signal (e.g., kill)
        # Add SIGBREAK for Windows if needed? Less common.
        if sys.platform == "win32":
             try:
                 signal.signal(signal.SIGBREAK, signal_handler)
             except AttributeError:
                  logger.debug("SIGBREAK not available on this Windows Python version.")


        # --- Start the Test ---
        tester_instance.start_test()
        # The main thread will block within start_test() until the test completes
        # or is interrupted by a signal.

        logger.info("Main thread finished.")
        sys.exit(0) # Explicit exit code 0 for success

    except ValueError as e:
        # Handle configuration errors (e.g., invalid mode from constructor)
        logger.critical(f"Configuration Error: {e}")
        sys.exit(2)
    except PermissionError as e:
        # Handle file system permission errors during setup
        logger.critical(f"Permission Error: {e}. Check permissions for storage directory: {args.storage_dir}")
        sys.exit(3)
    except Exception as e:
        # Catch any other unexpected critical errors during initialization or runtime
        logger.critical(f"A critical error occurred in the main execution block: {e}", exc_info=True)
        sys.exit(1) # General error exit code
    finally:
        # --- Final Cleanup Attempt ---
        # This block executes even if errors occurred above.
        # Attempt to close log files if tester instance might not have done it (e.g., init error).
        if 'tester_instance' in locals() and tester_instance and not tester_instance.active:
             logger.debug("Tester likely stopped cleanly, logs should be closed.")
        else:
             logger.debug("Attempting final log file closure in finally block.")
             try:
                 for logger_obj in [activity_logger, download_logger, logger]:
                      for handler in logger_obj.handlers[:]:
                           if isinstance(handler, logging.FileHandler):
                                try:
                                     handler.close()
                                     logger.debug(f"Closed log handler {handler.baseFilename} in finally block.")
                                except Exception: pass # Ignore errors here
             except Exception: pass # Ignore errors here
