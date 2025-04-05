#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Enhanced CS16 UDP Downloader

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
from urllib.parse import urljoin, unquote
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
                offset += 1 # Skip protocol version byte

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
                    logger.debug(f"Parsed server info: {server_name} | Map: {map_name} | Players: {player_count}/{max_players}")
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
