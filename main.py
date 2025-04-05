#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Enhanced CS16 UDP Downloader / Server Tester

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
from queue import Queue, Empty
from typing import Optional, Dict, List, Tuple, Any

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
# Add sequence to hide cursor (optional, for cleaner UI)
HIDE_CURSOR = "\033[?25l"
SHOW_CURSOR = "\033[?25h"


# UDP protocol constants
HEADER = b"\xFF\xFF\xFF\xFF"
A2S_INFO = b"TSource Engine Query\x00"  # Modern A2S_INFO query
A2S_PING_LEGACY = b"\x69" # Legacy A2S_PING ('i') - Some old servers might need this
A2S_PING = b"\x69\x00" # Slightly more robust simple ping? (Often just 'i' works)
A2S_RULES = b"\x56" # 'V' - Rules query command byte
A2S_PLAYER = b"\x55" # 'U' - Player query command byte
A2S_CHALLENGE_REQUEST_SUFFIX = b"\xFF\xFF\xFF\xFF" # Often appended to player/rules req to get challenge
PING_RESPONSE_PREFIX = b"\xFF\xFF\xFF\xFFj"  # Common ping response prefix ('j')
INFO_RESPONSE_PREFIX = b"\xFF\xFF\xFF\xFFI" # 'I' (or 'm' for older)
RULES_RESPONSE_PREFIX = b"\xFF\xFF\xFF\xFFE" # 'E'
PLAYER_RESPONSE_PREFIX = b"\xFF\xFF\xFF\xFFD" # 'D'
CHALLENGE_RESPONSE_PREFIX = b"\xFF\xFF\xFF\xFFA" # 'A'


# Download protocol variants
REQUEST_FILE_CMD = b"requestfile"  # Main command for requesting files
REQUEST_FILE_CMD_ALT1 = b"getfile"  # Alternative command used by some servers
REQUEST_FILE_CMD_ALT2 = b"download"  # Another alternative
FRAGMENT_SIZE = 1024  # Max UDP fragment size to request/expect
DOWNLOAD_TIMEOUT = 15  # Timeout for a single file download (seconds)
MAX_RETRIES = 3  # Max retries for a single query/initial download request

# File types that can be downloaded (used for generating guesses - implementation TBD)
FILE_TYPES = [
    "maps/*.bsp",
    "models/*.mdl",
    "sound/*.wav",
    "sprites/*.spr",
    "overviews/*.tga",
    "gfx/env/*.tga",
    "*.res", # Map resource file
    "*.wad", # Texture WAD file
    # "media/*.mp3", # Less common via UDP?
    # "materials/*.vmt", # Often FastDL
    # "materials/*.vtf"  # Often FastDL
]

# Common file prefixes for maps (used for generating guesses - implementation TBD)
MAP_PREFIXES = ["de_", "cs_", "as_", "fy_", "ka_", "aim_", "awp_", "he_", "zm_", "35hp_", "gg_", "jail_", "jb_", "hns_", "surf_", "kz_", "bhop_"]

# Log/Temp file config
ACTIVITY_LOG_FILENAME = "activity_log.txt"
DOWNLOAD_LOG_FILENAME = "download_debug.log" # Changed extension to .log
# Removed UDP_VERIFY_FILENAME_PREFIX as verification logic is removed

# --- Global logger setup ---
# Define custom level below DEBUG for trace logging if needed
TRACE_LEVEL_NUM = 5
logging.addLevelName(TRACE_LEVEL_NUM, "TRACE")
def trace(self, message, *args, **kws):
    if self.isEnabledFor(TRACE_LEVEL_NUM):
        self._log(TRACE_LEVEL_NUM, message, args, **kws)
logging.Logger.trace = trace

# Default logging to stderr
logging.basicConfig(
    level=logging.INFO, # Default level, can be changed by args
    format='%(asctime)s [%(levelname)s] (%(threadName)s) %(message)s',
    datefmt='%H:%M:%S',
    stream=sys.stderr
)
logger = logging.getLogger('cs_udp_tester') # Main application logger

# --- Activity Logger Setup (File logging) ---
activity_logger = logging.getLogger('activity_logger')
activity_logger.setLevel(logging.INFO) # Log INFO and above to file
activity_logger.propagate = False  # Don't send activity logs to the main stderr handler

# --- Download Debug Logger (Separate file) ---
download_logger = logging.getLogger('download_logger')
download_logger.setLevel(logging.DEBUG) # Log DEBUG and above for downloads to file
download_logger.propagate = False  # Don't send download logs to the main stderr handler

# Global variable to hold the tester instance for signal handling
tester_instance = None
# Global flag to signal shutdown
shutdown_flag = threading.Event()


# ==============================================================
# Utility Functions
# ==============================================================
def setup_file_logging(log_dir: Path, activity_filename: str, download_filename: str):
    """Configures file handlers for activity and download logs."""
    log_dir.mkdir(parents=True, exist_ok=True)

    # Activity Log File Handler
    activity_log_path = log_dir / activity_filename
    try:
        activity_handler = logging.FileHandler(activity_log_path, mode='a', encoding='utf-8')
        activity_handler.setFormatter(logging.Formatter('%(asctime)s [%(levelname)s] %(message)s', datefmt='%Y-%m-%d %H:%M:%S'))
        activity_logger.addHandler(activity_handler)
        activity_logger.info(f"--- Activity Log Started ({datetime.now()}) ---")
        logger.info(f"Activity logging enabled: {activity_log_path}")
    except Exception as e:
        logger.error(f"Failed to set up activity file logging to {activity_log_path}: {e}")
        activity_logger.addHandler(logging.NullHandler()) # Prevent errors if logging is called later

    # Download Debug Log File Handler
    download_log_path = log_dir / download_filename
    try:
        download_debug_handler = logging.FileHandler(download_log_path, mode='a', encoding='utf-8')
        # More detailed format for debug log
        debug_formatter = logging.Formatter('%(asctime)s [%(levelname)-7s] (%(threadName)s) %(message)s', datefmt='%H:%M:%S.%f')[:-3]
        download_debug_handler.setFormatter(debug_formatter)
        download_logger.addHandler(download_debug_handler)
        download_logger.debug(f"--- Download Debug Log Started ({datetime.now()}) ---")
        logger.info(f"Download debug logging enabled: {download_log_path}")
    except Exception as e:
        logger.error(f"Failed to set up download debug file logging to {download_log_path}: {e}")
        download_logger.addHandler(logging.NullHandler())

# ==============================================================
# ServerQuery Class
# ==============================================================
class ServerQuery:
    def __init__(self, server_ip: str, server_port: int = DEFAULT_PORT):
        self.server_ip = server_ip
        self.server_port = server_port
        self.last_info: Optional[Dict[str, Any]] = None
        self.last_rules: Optional[Dict[str, str]] = None
        self.last_ping: int = -1 # Use -1 to indicate never pinged or failed
        self.sock: Optional[socket.socket] = None
        self.retry_count: int = MAX_RETRIES
        self.timeout: float = 1.5 # Socket timeout in seconds
        self.last_challenge: Optional[bytes] = None # Store the last challenge number received (4 bytes)
        self._lock = threading.Lock() # Lock for thread safety when accessing socket/challenge

    def _create_socket(self):
        """Creates or recreates the UDP socket. Must be called within lock."""
        if self.sock is not None:
            try:
                self.sock.close()
            except Exception:
                pass # Ignore errors closing old socket
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.settimeout(self.timeout)
            logger.debug("Query socket created.")
        except Exception as e:
            logger.error(f"Query Socket Create Error: {e}")
            self.sock = None
            raise # Re-raise the exception

    def _log_activity(self, level: int, message: str):
        """Helper to log to both main logger and activity file logger if enabled."""
        logger.log(level, message)
        # Log to activity file if handler exists (and isn't NullHandler) and level is sufficient
        if activity_logger.hasHandlers() and not isinstance(activity_logger.handlers[0], logging.NullHandler):
            if level >= activity_logger.level:
                 activity_logger.log(level, message) # Use activity_logger's own level setting

    def _send_recv(self, request: bytes, query_type: str = "unknown") -> Tuple[Optional[bytes], int]:
        """Sends a UDP request, waits for response. Returns (response_data, ping_ms). Thread-safe."""
        with self._lock:
            if self.sock is None:
                try:
                    self._create_socket()
                except Exception:
                    return None, 0 # Return failure if socket can't be created

            ping = 0
            for attempt in range(self.retry_count):
                if shutdown_flag.is_set():
                    logger.warning(f"Shutdown signal received during UDP send/recv for {query_type}. Aborting.")
                    return None, 0

                start_time = time.time()
                try:
                    logger.trace(f"Sending UDP {query_type} query (attempt {attempt+1}) {len(request)} bytes: {request[:64].hex()}...")
                    self.sock.sendto(request, (self.server_ip, self.server_port))
                    # Buffer size should be large enough for typical responses
                    response, addr = self.sock.recvfrom(65507) # Max UDP payload size technically possible

                    end_time = time.time()
                    ping = int((end_time - start_time) * 1000) # Calculate ping in ms

                    # Basic validation: Ensure response came from the expected IP
                    if addr[0] != self.server_ip:
                        logger.warning(f"Received UDP response from unexpected IP {addr[0]} (expected {self.server_ip}) for {query_type}. Ignoring.")
                        continue # Treat as timeout/retry

                    if response:
                        logger.trace(f"UDP response received from {addr} for {query_type} ({len(response)} bytes) in {ping}ms.")
                        # Check for multi-packet responses (rare for queries, common for downloads)
                        # GoldSrc/Source queries usually fit in one packet.
                        # Could add logic here if multi-packet query responses were expected.
                        return response, ping # Return the received response and ping time
                    else:
                        logger.debug(f"Received empty UDP response (attempt {attempt+1}) for {query_type}")
                        # Treat as timeout

                except socket.timeout:
                    logger.debug(f"UDP {query_type} query timed out (attempt {attempt+1}, timeout={self.timeout}s)")
                    if attempt == self.retry_count - 1:
                        logger.warning(f"UDP {query_type} query failed after {self.retry_count} attempts.")
                        return None, 0 # Return failure after last retry
                    # No sleep needed here, loop continues to next attempt immediately or times out on recvfrom
                except OSError as e:
                    # Handle specific OS-level network errors (e.g., network unreachable, connection refused)
                    logger.warning(f"UDP Query OSError (attempt {attempt+1}) on {query_type}: {e}")
                    self.close() # Close the potentially broken socket
                    return None, 0 # Return failure
                except Exception as e:
                    # Catch any other unexpected errors during send/receive
                    logger.error(f"Unexpected UDP Query Error (attempt {attempt+1}) on {query_type}: {e}", exc_info=True)
                    self.close() # Close the socket on unexpected errors
                    return None, 0 # Return failure

            # Should only be reached if all retries timed out
            return None, 0

    # --- Public Query Methods ---
    def ping(self) -> int:
        """Send a simple A2S_PING request and measure response time. Returns ping in ms or -1 on failure."""
        # Try legacy ping first as it's simpler
        request_legacy = HEADER + A2S_PING_LEGACY
        response, ping_time = self._send_recv(request_legacy, query_type="ping_legacy")
        if response and response.startswith(PING_RESPONSE_PREFIX):
            self.last_ping = ping_time
            return ping_time

        # If legacy failed, try slightly different format
        # request_alt = HEADER + A2S_PING
        # response, ping_time = self._send_recv(request_alt, query_type="ping_alt")
        # if response and response.startswith(PING_RESPONSE_PREFIX):
        #    self.last_ping = ping_time
        #    return ping_time

        # If all pings fail
        self.last_ping = -1
        return -1

    def get_info(self) -> Optional[Dict[str, Any]]:
        """Requests and parses server information (A2S_INFO). Returns dict or None."""
        request = HEADER + A2S_INFO
        response, ping = self._send_recv(request, query_type="info")

        if response:
            self.last_ping = ping # Update ping even if parsing fails but we got a response
            # Check if it's a challenge response first
            if response.startswith(CHALLENGE_RESPONSE_PREFIX) and len(response) >= 9:
                with self._lock: # Protect access to last_challenge
                    self.last_challenge = response[5:9]
                logger.debug(f"Received challenge {self.last_challenge.hex()} when requesting info. Stored challenge.")
                # We didn't get info, but the server is responding. Return None for info.
                self.last_info = None # Clear previous info if we only got a challenge
                return None
            # Try parsing as info
            elif response.startswith(INFO_RESPONSE_PREFIX):
                 parsed_info = self._parse_info(response)
                 if parsed_info:
                    parsed_info['ping'] = ping # Add ping to the parsed info dict
                    self.last_info = parsed_info
                    # Clear challenge if we successfully got info (it wasn't needed)
                    # with self._lock: self.last_challenge = None # Let challenge persist if rules/players need it next
                    return parsed_info
                 else:
                    # Parsing failed, but it started with 'I'
                    logger.warning("Received potential INFO response, but parsing failed.")
                    self.last_info = None
                    return None
            else:
                logger.warning(f"Received unexpected response type for INFO query: {response[:10].hex()}...")
                self.last_info = None
                return None
        else:
            # Query failed (timeout/error)
            self.last_info = None
            self.last_ping = -1
            return None

    def _get_challenge_if_needed(self) -> Optional[bytes]:
        """Internal helper to acquire a challenge number if we don't have one."""
        with self._lock:
            if self.last_challenge:
                return self.last_challenge

        # We need a challenge. Send a request that typically requires one (like rules).
        # Use a dummy challenge value first.
        logger.debug("No challenge stored, requesting one...")
        request = HEADER + A2S_RULES + A2S_CHALLENGE_REQUEST_SUFFIX
        response, _ = self._send_recv(request, query_type="challenge_request")

        if response and response.startswith(CHALLENGE_RESPONSE_PREFIX) and len(response) >= 9:
            with self._lock:
                self.last_challenge = response[5:9]
                logger.info(f"Acquired challenge: {self.last_challenge.hex()}")
                return self.last_challenge
        else:
            logger.warning(f"Failed to acquire a challenge number. Server response: {response[:10].hex() if response else 'None'}")
            return None

    def get_rules(self) -> Optional[Dict[str, str]]:
        """Requests and parses server rules (A2S_RULES). Returns dict or None."""
        challenge = self._get_challenge_if_needed()
        if not challenge:
            logger.warning("Cannot get rules without a challenge number.")
            self.last_rules = None
            return None

        request = HEADER + A2S_RULES + challenge
        response, _ = self._send_recv(request, query_type="rules")

        # Handle potential new challenge response
        if response and response.startswith(CHALLENGE_RESPONSE_PREFIX) and len(response) >= 9:
            logger.info("Received a new challenge while requesting rules. Retrying with new challenge.")
            with self._lock:
                self.last_challenge = response[5:9]
            request = HEADER + A2S_RULES + self.last_challenge
            response, _ = self._send_recv(request, query_type="rules_retry")

        # Check for rules response
        if response and response.startswith(RULES_RESPONSE_PREFIX):
            parsed_rules = self._parse_rules(response)
            if parsed_rules is not None: # Check for None explicitly, empty dict is valid
                self.last_rules = parsed_rules
                return parsed_rules
            else:
                logger.warning("Received RULES response, but parsing failed.")
                self.last_rules = None
                return None
        else:
            logger.warning(f"Failed to get rules or received unexpected response: {response[:10].hex() if response else 'None'}")
            self.last_rules = None
            return None

    def get_players(self) -> Optional[List[str]]:
        """Requests and parses player information (A2S_PLAYER). Returns list of names or None."""
        challenge = self._get_challenge_if_needed()
        if not challenge:
            logger.warning("Cannot get players without a challenge number.")
            return None

        request = HEADER + A2S_PLAYER + challenge
        response, _ = self._send_recv(request, query_type="players")

        # Handle potential new challenge response
        if response and response.startswith(CHALLENGE_RESPONSE_PREFIX) and len(response) >= 9:
            logger.info("Received a new challenge while requesting players. Retrying with new challenge.")
            with self._lock:
                self.last_challenge = response[5:9]
            request = HEADER + A2S_PLAYER + self.last_challenge
            response, _ = self._send_recv(request, query_type="players_retry")

        # Check for player response
        if response and response.startswith(PLAYER_RESPONSE_PREFIX):
            players = self._parse_players(response)
            # Returns list (possibly empty) or None on parse error
            return players
        else:
            logger.warning(f"Failed to get players or received unexpected response: {response[:10].hex() if response else 'None'}")
            return None # Indicate failure to get data

    # --- Parsers ---
    def _parse_info(self, response: bytes) -> Optional[Dict[str, Any]]:
        """Parses the A2S_INFO response payload ('I' or 'm')."""
        # Assumes response starts with HEADER + TYPE_BYTE already checked by caller
        try:
            header_byte = response[4:5] # Get the response type indicator
            offset = 5 # Start reading after the header + type byte

            # --- Helper function to read null-terminated strings ---
            def read_string(data: bytes, start_offset: int) -> Tuple[str, int]:
                end = data.find(b'\x00', start_offset)
                if end == -1:
                    raise ValueError("Malformed string (null terminator missing)")
                # Decode using utf-8, replace errors to avoid crashes on weird server names
                # Use 'latin-1' as a fallback for older servers that might not use UTF-8
                try:
                    decoded_str = data[start_offset:end].decode('utf-8', errors='ignore')
                except UnicodeDecodeError:
                    decoded_str = data[start_offset:end].decode('latin-1', errors='ignore')
                return decoded_str, end + 1

            # --- Parse based on response type ---
            if header_byte == b'I':  # Source Engine / GoldSrc (Newer format) Response Header 'I'
                protocol_version = response[offset] # Could store this if needed
                offset += 1

                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)

                # Structure after strings can vary
                # Common structure (Source/New GoldSrc): AppID(2), Players(1), MaxPlayers(1), Bots(1), ServerType(1), OS(1), Password(1), VAC(1) ... [EDF]
                if offset + 9 <= len(response): # Enough bytes for typical fields up to VAC
                    app_id = struct.unpack('<H', response[offset:offset+2])[0]
                    offset += 2
                    player_count = response[offset]
                    offset += 1
                    max_players = response[offset]
                    offset += 1
                    bot_count = response[offset]
                    offset += 1
                    server_type = chr(response[offset]) if response[offset] != 0 else '?' # d=dedicated, l=listen, p=proxy
                    offset += 1
                    os_type = chr(response[offset]) if response[offset] != 0 else '?' # l=linux, w=windows, m=mac
                    offset += 1
                    password_required = bool(response[offset])
                    offset += 1
                    vac_enabled = bool(response[offset])
                    offset += 1

                    # Optional: Parse EDF (Extra Data Flag) if present
                    # ... logic to parse EDF based on flags ...

                    logger.trace(f"Parsed server info (I): {server_name} | Map: {map_name} | Players: {player_count}/{max_players} ({bot_count} bots)")
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': player_count, 'max_players': max_players, 'bots': bot_count,
                            'app_id': app_id, 'server_type': server_type, 'os': os_type,
                            'password': password_required, 'vac': vac_enabled, 'protocol': protocol_version}
                else:
                    logger.warning(f"Info response (I) possibly truncated after strings. Len: {len(response)}, Offset: {offset}. Parsing basic info.")
                    # Fallback: assume 0 for missing fields if response is short
                    return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                            'players': 0, 'max_players': 0, 'bots': 0, 'protocol': protocol_version}

            elif header_byte == b'm':  # Older GoldSrc Response Header 'm' (less common)
                server_address, offset = read_string(response, offset) # Read and discard address string

                server_name, offset = read_string(response, offset)
                map_name, offset = read_string(response, offset)
                game_dir, offset = read_string(response, offset)
                game_desc, offset = read_string(response, offset)

                if offset + 2 > len(response):
                    raise ValueError("Response too short for player counts in older GoldSrc format ('m')")
                player_count = response[offset]
                offset += 1
                max_players = response[offset]
                offset += 1

                # Assume defaults for fields not present in this format
                logger.trace(f"Parsed server info (m): {server_name} | Map: {map_name} | Players: {player_count}/{max_players}")
                return {'name': server_name, 'map': map_name, 'game': game_dir, 'description': game_desc,
                        'players': player_count, 'max_players': max_players, 'bots': 0,
                        'app_id': 0, 'server_type': '?', 'os': '?',
                        'password': False, 'vac': False, 'protocol': None} # Protocol not present in 'm'
            else:
                # Should not happen if caller checks prefix, but defensively handle
                logger.error(f"Parser called with unexpected A2S_INFO header byte: {header_byte.hex()}")
                return None
        except (ValueError, IndexError, struct.error) as e:
            logger.warning(f"Parse INFO {type(e).__name__}: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except Exception as e:
            logger.error(f"Unexpected Parse INFO error: {e}", exc_info=True)
            return None

    def _parse_rules(self, response: bytes) -> Optional[Dict[str, str]]:
        """Parses the A2S_RULES response payload ('E')."""
        # Assumes response starts with HEADER + TYPE_BYTE already checked by caller
        try:
            if len(response) < 7: # Need header(4), type(1), count(2)
                 raise ValueError("Response too short for rule count")

            rules_count = struct.unpack('<H', response[5:7])[0]
            offset = 7 # Start reading after rule count
            rules: Dict[str, str] = {}

            # --- Helper function to read null-terminated strings ---
            def read_string(data: bytes, start_offset: int) -> Tuple[str, int]:
                end = data.find(b'\x00', start_offset)
                if end == -1:
                    raise ValueError("Malformed string (null terminator missing)")
                # Use latin-1 for rules as they often contain non-standard characters
                # or simple ASCII. UTF-8 might fail unnecessarily.
                return data[start_offset:end].decode('latin-1', errors='ignore'), end + 1

            parsed_count = 0
            while parsed_count < rules_count:
                # Check remaining length before trying to read strings
                if offset >= len(response):
                    logger.warning(f"Rule parsing stopped early: offset ({offset}) reached end of data ({len(response)}) before expected rule count ({rules_count}) was met. Parsed {parsed_count} rules.")
                    break

                rule_name, offset = read_string(response, offset)

                # Check remaining length again before reading value
                if offset >= len(response):
                     logger.warning(f"Rule parsing stopped early: offset ({offset}) reached end of data ({len(response)}) after reading rule name '{rule_name}'. Incomplete rule.")
                     break

                rule_value, offset = read_string(response, offset)
                rules[rule_name] = rule_value
                parsed_count += 1

            if parsed_count != rules_count:
                logger.warning(f"Expected {rules_count} rules according to header, but parsed {parsed_count}. Response might be truncated or malformed.")

            logger.trace(f"Parsed {len(rules)} rules.")
            return rules # Return the dictionary of parsed rules (possibly less than expected)
        except (ValueError, IndexError, struct.error) as e:
            logger.warning(f"Parse RULES {type(e).__name__}: {e} | Response (partial): {response[:60].hex()}...")
            return None
        except Exception as e:
            logger.error(f"Unexpected Parse RULES error: {e}", exc_info=True)
            return None

    def _parse_players(self, response: bytes) -> Optional[List[str]]:
        """Parses the A2S_PLAYER response payload ('D'). Returns list of names or None on error."""
        # Assumes response starts with HEADER + TYPE_BYTE already checked by caller
        try:
            if len(response) < 6: # Need header(4), type(1), count(1)
                raise ValueError("Response too short for player count")

            num_players = response[5]
            offset = 6 # Start after player count byte
            players: List[str] = []

            for i in range(num_players):
                # Basic check to prevent reading past the end
                if offset >= len(response):
                    logger.warning(f"Player parsing stopped early: offset ({offset}) reached end of data ({len(response)}) before expected player count ({num_players}) was met. Parsed {i} players.")
                    break

                # Read Player Index (1 byte) - discard
                # player_index = response[offset]
                offset += 1
                if offset >= len(response): # Check after incrementing offset
                    logger.warning(f"Player parsing stopped early: truncated data before player name (Player {i+1}/{num_players}).")
                    break

                # Read null-terminated player name
                name_end = response.find(b'\x00', offset)
                if name_end == -1:
                    logger.warning(f"Malformed player data (Player {i+1}/{num_players}): missing null terminator for name.")
                    # Attempt to recover or bail? Bail for now.
                    break
                # Decode name using utf-8 (common) or fallback to latin-1
                try:
                    name = response[offset:name_end].decode('utf-8', errors='ignore')
                except UnicodeDecodeError:
                    name = response[offset:name_end].decode('latin-1', errors='ignore')
                offset = name_end + 1 # Move offset past the name and null terminator

                # Minimum data remaining for score and duration
                if offset + 8 > len(response):
                    logger.warning(f"Malformed player data (Player {i+1}/{num_players}, Name: '{name}'): truncated data before score/duration.")
                    # Include the player name we parsed, but stop further parsing
                    players.append(name)
                    break

                # Read Score (4 bytes signed long) and Duration (4 bytes float) - discard for now
                # score = struct.unpack('<l', response[offset:offset+4])[0]
                # duration = struct.unpack('<f', response[offset+4:offset+8])[0]
                offset += 8

                players.append(name)

            if len(players) != num_players:
                 logger.warning(f"Expected {num_players} players according to header, but parsed {len(players)}. Response might be truncated or malformed.")

            logger.trace(f"Parsed {len(players)} player names.")
            return players # Return the list of parsed player names

        except (ValueError, IndexError, struct.error) as e:
            logger.warning(f"Parse PLAYERS {type(e).__name__}: {e} | Response (partial): {response[:60].hex()}...")
            return None # Indicate parsing failure
        except Exception as e:
            logger.error(f"Unexpected Parse PLAYERS error: {e}", exc_info=True)
            return None # Indicate parsing failure

    def close(self):
        """Closes the UDP socket if it's open."""
        with self._lock:
            if self.sock:
                try:
                    self.sock.close()
                    logger.debug("ServerQuery socket closed.")
                except Exception as e:
                    logger.error(f"Error closing query socket: {e}")
                self.sock = None

# ==============================================================
# UDP File Downloader Class
# ==============================================================
class UDPFileDownloader:
    def __init__(self, server_ip: str, server_port: int, save_dir: Path):
        self.server_ip = server_ip
        self.server_port = server_port
        self.save_dir = save_dir
        self.sock: Optional[socket.socket] = None
        self.timeout: float = 3.0  # Socket timeout for receiving fragments (increased slightly)
        self.current_file: str = "" # Path of the file being downloaded (relative path used as ID)
        self.bytes_received: int = 0 # Bytes received for the current file
        self.fragment_size: int = FRAGMENT_SIZE # Expected size of fragments
        self._lock = threading.Lock() # Lock for thread safety if methods are called concurrently (e.g., close)

    def _create_socket(self):
        """Create or recreate the UDP socket for downloading. Must be called within lock."""
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.settimeout(self.timeout)
            download_logger.debug("Downloader socket created.")
        except Exception as e:
            download_logger.error(f"Downloader socket creation failed: {e}")
            logger.error(f"Socket creation failed for download worker: {e}") # Also log to main logger
            self.sock = None
            raise # Re-raise

    def hexdump(self, data: bytes, length: int = 16) -> str:
        """Helper function to create a readable hexdump string for debugging."""
        result = []
        for i in range(0, len(data), length):
            chunk = data[i:i+length]
            hex_part = ' '.join(f'{b:02x}' for b in chunk)
            ascii_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            result.append(f"{i:04x}: {hex_part:<{length*3}} {ascii_part}")
        return '\n'.join(result)

    def download_file(self, file_path: str) -> Tuple[bool, int]:
        """
        Attempts to download a single file from the server using CS1.6 UDP protocol.
        Returns (success_status, bytes_downloaded). Thread-safe for separate calls.
        """
        with self._lock: # Ensure exclusive access for the entire download attempt
            # Log start using the dedicated download logger
            # Normalize file path for consistency (forward slashes, remove leading)
            file_id = file_path.replace('\\', '/').lstrip('/')
            download_logger.info(f"=== Starting download attempt for: {file_id} ===")

            # Ensure socket exists
            if not self.sock:
                try:
                    self._create_socket()
                except Exception as e:
                    # Error already logged by _create_socket
                    return False, 0 # Return failure

            # Basic validation of the file path argument
            if not file_path: # Check if string is empty
                download_logger.error(f"Invalid file path provided (empty string).")
                logger.error(f"Invalid file path provided for download (empty string).")
                return False, 0

            self.current_file = file_id
            self.bytes_received = 0 # Reset bytes counter for this file

            # Prepare the save path and ensure parent directories exist
            try:
                # Construct the full path where the file will be saved
                # Ensure file_id is treated as relative to save_dir
                save_path = self.save_dir / file_id
                save_path.parent.mkdir(parents=True, exist_ok=True) # Create directories if needed
            except OSError as e:
                 # Handle potential filesystem errors (permissions, invalid chars)
                download_logger.error(f"Failed to create/access directory structure for '{save_path}': {e}")
                logger.error(f"Failed to prepare save path for '{file_id}': {e}")
                return False, 0
            except Exception as e: # Catch other potential path errors
                download_logger.error(f"Unexpected error preparing save path '{save_path}': {e}")
                logger.error(f"Unexpected error preparing save path for '{file_id}': {e}")
                return False, 0

            download_logger.debug(f"File ID: {file_id}, Target Save Path: {save_path}")

            try:
                # --- Prepare potential request commands ---
                # Use file_id (normalized path) for requests
                file_path_bytes = file_id.encode('utf-8', errors='ignore') # Encode normalized path
                # Ensure null termination for commands that expect it
                request_primary = HEADER + REQUEST_FILE_CMD + b" " + file_path_bytes + b"\x00"
                request_alt1 = HEADER + REQUEST_FILE_CMD_ALT1 + b" " + file_path_bytes + b"\x00"
                request_alt2 = HEADER + REQUEST_FILE_CMD_ALT2 + b" " + file_path_bytes + b"\x00"
                # Some servers might respond to just the path without a command prefix
                request_alt3 = HEADER + file_path_bytes + b"\x00"
                request_commands = [request_primary, request_alt1, request_alt2, request_alt3]
                request_names = [REQUEST_FILE_CMD.decode(), REQUEST_FILE_CMD_ALT1.decode(), REQUEST_FILE_CMD_ALT2.decode(), "Direct Path"]

                logger.info(f"Requesting file: {file_id}") # Log to main console
                download_logger.info(f"Requesting file: {file_id}") # Log to download debug file
                start_time = time.time()

                # --- Download Loop State ---
                response_received = False # Flag if *any* valid fragment/response packet has been received
                request_attempt_index = 0 # Tracks which request command format index we are currently trying/using
                current_request_sent = False # Flag to track if the *current* format has been sent
                last_request_sent_time = 0.0 # Time the last request packet was sent

                fragments: Dict[int, bytes] = {} # Dictionary to store received fragments {fragment_number: data}
                total_fragments_expected: int = 0 # Total number of fragments server indicated (if any)
                file_size_reported: int = 0 # Total file size reported by server (if any)
                last_fragment_received_time = time.time() # Track time of last received *valid fragment* for timeout
                download_complete: bool = False # Flag set when all expected fragments are received

                received_packets_log = [] # For debugging, store snippets of received packets
                total_packets_received_count = 0 # Counter for all received UDP packets for this file
                last_logged_fragment_num = -1 # Track last logged fragment number to reduce log spam

                # --- Main Download Loop ---
                while not shutdown_flag.is_set() and time.time() - last_fragment_received_time < DOWNLOAD_TIMEOUT and not download_complete:
                    # --- Request Sending Logic ---
                    # If the current request format hasn't been sent, or if we need to retry due to no response
                    # Send request if not sent OR if some time passed since last send and no response received yet
                    # Retry interval (e.g., every 2 seconds if no response)
                    retry_interval = 2.0
                    if not current_request_sent or \
                       (not response_received and time.time() - last_request_sent_time > retry_interval):

                        if request_attempt_index >= len(request_commands):
                            # We've tried all commands and haven't received anything valid
                            download_logger.warning(f"All request formats timed out without a valid response for {file_id}.")
                            logger.warning(f"No response from server for file {file_id} after trying all methods.")
                            # Break the loop, failure will be handled outside
                            break

                        # Send the current request command format
                        current_request = request_commands[request_attempt_index]
                        current_request_name = request_names[request_attempt_index]

                        if not current_request_sent: # First time sending this format
                            download_logger.info(f"Sending request (Format: {current_request_name})...")
                            if request_attempt_index > 0: logger.info(f"Trying download command format '{current_request_name}' for {file_id}")
                        else: # Resending the same format due to timeout
                            download_logger.debug(f"Re-sending request (Format: {current_request_name}) due to no response...")


                        try:
                            bytes_sent = self.sock.sendto(current_request, (self.server_ip, self.server_port))
                            download_logger.trace(f"Sent {bytes_sent} bytes to {self.server_ip}:{self.server_port}: {current_request[:64].hex()}...")
                            current_request_sent = True
                            last_request_sent_time = time.time()
                        except socket.error as e:
                            download_logger.error(f"Socket error sending request (Format: {current_request_name}): {e}")
                            logger.error(f"Socket error sending request for {file_id}: {e}")
                            # This is likely fatal for this attempt
                            return False, self.bytes_received
                        except Exception as e:
                            download_logger.error(f"Unexpected error sending request (Format: {current_request_name}): {e}", exc_info=True)
                            logger.error(f"Unexpected error sending request for {file_id}: {e}")
                            return False, self.bytes_received

                    # --- Receive Logic ---
                    try:
                        # Wait for data from the server
                        # Use a larger buffer just in case, though fragments should be ~FRAGMENT_SIZE + headers
                        data, addr = self.sock.recvfrom(FRAGMENT_SIZE + 512)

                        # Check if we received any data and if it's from the expected server
                        if not data:
                            download_logger.trace("Received empty packet, ignoring.")
                            continue
                        if addr[0] != self.server_ip:
                            download_logger.warning(f"Received packet from unexpected IP {addr[0]} (expected {self.server_ip}). Ignoring.")
                            continue

                        # Process received packet
                        total_packets_received_count += 1
                        current_time = time.time()
                        # Don't reset last_fragment_received_time here, only when a *valid fragment* is parsed

                        download_logger.trace(f"Recv Packet #{total_packets_received_count}: {len(data)} bytes from {addr}")
                        if logger.level <= TRACE_LEVEL_NUM: # Only hexdump if TRACE is enabled
                             download_logger.trace(f"Hexdump (64 bytes):\n{self.hexdump(data[:min(64, len(data))])}")
                        # Store first few packet snippets for debugging summary later
                        if total_packets_received_count <= 5:
                             received_packets_log.append(data[:64])

                        # --- Packet Parsing ---
                        if not data.startswith(HEADER):
                            download_logger.warning(f"Received packet without standard header: {data[:64].hex()}...")
                            continue # Ignore non-standard packets

                        offset = 4 # Start parsing after the header

                        # --- Handle File Fragment Response ---
                        # Structure can vary: Size(4)+FragNum(4), Size(4)+FragNum(2), FragNum(4), FragNum(2)
                        # May or may not have a type byte ('R' or similar)
                        is_fragment = False
                        parsed_fragment_num = -1
                        fragment_data = b''

                        try:
                            # Common case: Filesize(4), FragNum(4) structure (often implicit type)
                            if len(data) >= offset + 8:
                                potential_filesize = struct.unpack('<I', data[offset:offset+4])[0]
                                potential_fragnum = struct.unpack('<I', data[offset+4:offset+8])[0]
                                # Sanity checks: size non-negative, fragment number non-negative
                                if potential_filesize >= 0 and potential_fragnum >= 0:
                                    if file_size_reported == 0 and potential_filesize > 0:
                                        file_size_reported = potential_filesize
                                        download_logger.info(f"File size reported by server: {file_size_reported} bytes")
                                        if total_fragments_expected == 0: # Estimate only if not known
                                            total_fragments_expected = (file_size_reported + self.fragment_size - 1) // self.fragment_size
                                            download_logger.info(f"Estimated total fragments: {total_fragments_expected}")

                                    parsed_fragment_num = potential_fragnum
                                    fragment_data = data[offset+8:]
                                    is_fragment = True
                                    # Log fragment number only if it changes significantly or is low to reduce spam
                                    if parsed_fragment_num < 10 or parsed_fragment_num % 50 == 0 or parsed_fragment_num != last_logged_fragment_num:
                                        download_logger.debug(f"Parsed fragment (4+4 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")
                                        last_logged_fragment_num = parsed_fragment_num


                            # Alternative: Filesize(4), FragNum(2)
                            elif len(data) >= offset + 6:
                                potential_filesize = struct.unpack('<I', data[offset:offset+4])[0]
                                potential_fragnum = struct.unpack('<H', data[offset+4:offset+6])[0] # 2 bytes frag num
                                if potential_filesize >= 0 and potential_fragnum >= 0:
                                    if file_size_reported == 0 and potential_filesize > 0:
                                        file_size_reported = potential_filesize
                                        download_logger.info(f"File size reported by server: {file_size_reported} bytes")
                                        if total_fragments_expected == 0:
                                            total_fragments_expected = (file_size_reported + self.fragment_size - 1) // self.fragment_size
                                            download_logger.info(f"Estimated total fragments: {total_fragments_expected}")

                                    parsed_fragment_num = potential_fragnum
                                    fragment_data = data[offset+6:]
                                    is_fragment = True
                                    if parsed_fragment_num < 10 or parsed_fragment_num % 50 == 0 or parsed_fragment_num != last_logged_fragment_num:
                                        download_logger.debug(f"Parsed fragment (4+2 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")
                                        last_logged_fragment_num = parsed_fragment_num

                            # Fallback: Maybe just FragNum(4) (size might be implicit or unknown)
                            elif len(data) >= offset + 4:
                                potential_fragnum = struct.unpack('<I', data[offset:offset+4])[0]
                                if potential_fragnum >= 0:
                                    parsed_fragment_num = potential_fragnum
                                    fragment_data = data[offset+4:]
                                    is_fragment = True
                                    if parsed_fragment_num < 10 or parsed_fragment_num % 50 == 0 or parsed_fragment_num != last_logged_fragment_num:
                                        download_logger.debug(f"Parsed fragment (0+4 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")
                                        last_logged_fragment_num = parsed_fragment_num

                            # Fallback: Maybe just FragNum(2)
                            elif len(data) >= offset + 2:
                                potential_fragnum = struct.unpack('<H', data[offset:offset+2])[0]
                                if potential_fragnum >= 0:
                                    parsed_fragment_num = potential_fragnum
                                    fragment_data = data[offset+2:]
                                    is_fragment = True
                                    if parsed_fragment_num < 10 or parsed_fragment_num % 50 == 0 or parsed_fragment_num != last_logged_fragment_num:
                                        download_logger.debug(f"Parsed fragment (0+2 header): Num={parsed_fragment_num}, Size={len(fragment_data)} bytes")
                                        last_logged_fragment_num = parsed_fragment_num

                            # Last resort: Check for specific error messages or assume fragment 0 if small
                            # Example: Check for "ERROR: File not found" or similar common errors
                            elif len(data) > offset:
                                payload = data[offset:]
                                # Simple check for common error strings (case-insensitive)
                                payload_lower = payload.lower()
                                if b"error" in payload_lower or b"not found" in payload_lower or b"doesn't exist" in payload_lower:
                                     try:
                                         error_msg = payload.split(b'\x00')[0].decode('utf-8', errors='ignore')
                                     except Exception:
                                         error_msg = payload.hex() # Fallback to hex if decode fails
                                     download_logger.error(f"Server likely returned error: '{error_msg}'")
                                     logger.error(f"Server error for file {file_id}: {error_msg}")
                                     # Treat as fatal error for this download
                                     return False, self.bytes_received
                                # If not an obvious error, could be a single-fragment file (treat as frag 0)
                                # Or could be an unrecognized response type.
                                # Only assume fragment 0 if the size suggests it might be the whole file
                                elif file_size_reported == 0 and len(payload) < self.fragment_size:
                                    parsed_fragment_num = 0
                                    fragment_data = payload
                                    is_fragment = True
                                    file_size_reported = len(fragment_data) # Assume this is the total size
                                    total_fragments_expected = 1
                                    download_logger.info(f"Assuming single fragment download based on small payload. Size={file_size_reported} bytes.")
                                else:
                                    download_logger.warning(f"Unrecognized packet structure after header: {payload[:64].hex()}...")


                        except struct.error as unpack_error:
                            download_logger.warning(f"Struct unpack error during fragment parsing: {unpack_error}. Data might be corrupt.")
                            is_fragment = False # Treat as non-fragment if parsing fails
                        except Exception as parse_ex:
                             download_logger.error(f"Unexpected error during fragment parsing: {parse_ex}", exc_info=True)
                             is_fragment = False

                        # --- Store Fragment and Check Completion ---
                        if is_fragment and parsed_fragment_num >= 0:
                            response_received = True # Mark that we got a valid response (a fragment)
                            last_fragment_received_time = current_time # Reset timeout timer *only* for valid fragments

                            if parsed_fragment_num not in fragments:
                                fragments[parsed_fragment_num] = fragment_data
                                self.bytes_received += len(fragment_data) # Update total bytes received
                                download_logger.trace(f"Stored fragment {parsed_fragment_num}. Total stored: {len(fragments)}, Bytes: {self.bytes_received}")
                                # Update UI progress if implemented
                            else:
                                download_logger.trace(f"Received duplicate fragment {parsed_fragment_num}. Ignored.")

                            # --- Check if download is complete ---
                            # Condition 1: We know the total fragments and have received exactly that many unique fragments.
                            cond1 = (total_fragments_expected > 0 and len(fragments) == total_fragments_expected)
                            # Condition 2: We know the file size and have received at least that many bytes, AND we have at least one fragment.
                            # This helps with cases where fragment count might be off, or the last fragment is smaller than expected.
                            cond2 = (file_size_reported > 0 and self.bytes_received >= file_size_reported and len(fragments) > 0)
                            # Condition 3: Handle edge case where server reports 0 fragments/size but sends data (treat as complete on first fragment)
                            cond3 = (total_fragments_expected == 0 and file_size_reported == 0 and len(fragments) > 0 and len(fragment_data) < self.fragment_size)

                            if cond1 or cond2 or cond3:
                                download_complete = True
                                # Refine reported size/fragments if cond2 or cond3 triggered completion
                                if file_size_reported == 0: file_size_reported = self.bytes_received
                                if total_fragments_expected == 0: total_fragments_expected = len(fragments)
                                download_logger.info(f"Download completion condition met. Expected Frags: {total_fragments_expected}, Got: {len(fragments)}. Expected Size: {file_size_reported}, Got: {self.bytes_received}")

                    except socket.timeout:
                        # --- Handle Socket Timeout ---
                        download_logger.trace("Socket timeout occurred while waiting for data.")

                        # If we haven't received *any* valid fragment/response yet, try the next request format
                        if not response_received:
                            download_logger.debug(f"Timeout waiting for initial response using format '{request_names[request_attempt_index]}'.")
                            request_attempt_index += 1 # Move to next format
                            current_request_sent = False # Mark that the *new* format needs to be sent
                            # Loop will continue and send the new format if available
                        else:
                            # We *have* received fragments, but stalled waiting for more.
                            # Re-send the *current successful* request format to potentially resume.
                            # Avoid resending too rapidly.
                            if time.time() - last_request_sent_time > retry_interval / 2: # Resend if stalled for ~1 sec
                                download_logger.debug("Timeout waiting for more fragments. Re-sending last successful request format.")
                                current_request = request_commands[request_attempt_index]
                                try:
                                    self.sock.sendto(current_request, (self.server_ip, self.server_port))
                                    last_request_sent_time = time.time()
                                except socket.error as e:
                                    download_logger.error(f"Socket error re-sending request: {e}")
                                    # Maybe retry later or fail? For now, just log.
                                except Exception as e:
                                     download_logger.error(f"Unexpected error re-sending request: {e}", exc_info=True)
                            # Keep waiting for more fragments until the main DOWNLOAD_TIMEOUT expires


except socket.error as sock_err:
                        download_logger.error(f"Socket error during recv: {sock_err}")
                        logger.error(f"Socket error receiving data for {file_id}: {sock_err}")
                        return False, self.bytes_received # Assume fatal for this download attempt
                    except Exception as loop_err:
                        download_logger.error(f"Unexpected error in download loop: {loop_err}", exc_info=True)
                        logger.error(f"Unexpected error downloading {file_id}: {loop_err}")
                        return False, self.bytes_received # Assume fatal

            # --- End of Download Loop ---
            if shutdown_flag.is_set():
                 download_logger.warning(f"Download interrupted by shutdown signal for {file_id}.")
                 logger.warning(f"Download aborted: {file_id}")
                 return False, self.bytes_received

            download_logger.info(f"Download loop finished for {file_id}.")
            download_logger.info(f"Status: Complete={download_complete}, Total Packets Recv={total_packets_received_count}, Using Format Idx={request_attempt_index}")
            download_logger.info(f"Fragments Received: {len(fragments)} / {total_fragments_expected if total_fragments_expected > 0 else 'Unknown'} expected")
            download_logger.info(f"Bytes Received: {self.bytes_received} / {file_size_reported if file_size_reported > 0 else 'Unknown'} expected")

            if received_packets_log:
                download_logger.debug("Sample of first few received packets (hex):")
                for i, pkt_sample in enumerate(received_packets_log):
                    download_logger.debug(f" Sample {i+1}: {pkt_sample.hex()}")

            # --- Assemble File and Final Check ---
            if download_complete and len(fragments) > 0:
                # Try to assemble the file from fragments
                assembled_bytes = 0
                try:
                    with open(save_path, 'wb') as f:
                        # Ensure fragments are sorted correctly by number
                        expected_frag_num = 0
                        sorted_frag_keys = sorted(fragments.keys())

                        # Check for missing fragments (gaps in sequence)
                        for i, frag_num in enumerate(sorted_frag_keys):
                            if frag_num != expected_frag_num:
                                # This case should ideally be caught by completion logic, but double-check
                                download_logger.error(f"Missing fragment detected during assembly! Expected {expected_frag_num}, got {frag_num}. File may be corrupt.")
                                logger.error(f"Download corrupt for {file_id}: Missing fragment {expected_frag_num}.")
                                # Optionally delete incomplete file: os.remove(save_path)
                                if save_path.exists(): save_path.unlink()
                                return False, self.bytes_received # Mark as failed if fragments are missing

                            f.write(fragments[frag_num])
                            assembled_bytes += len(fragments[frag_num])
                            expected_frag_num += 1

                    # Final size verification after assembly
                    if file_size_reported > 0 and assembled_bytes != file_size_reported:
                        download_logger.warning(f"Assembled size ({assembled_bytes}) differs from reported size ({file_size_reported}). File might be incomplete or server report inaccurate.")
                        # Decide if this is critical? For now, log warning but consider success if assembly finished.
                    elif assembled_bytes != self.bytes_received:
                         # Sanity check, should normally match
                         download_logger.warning(f"Assembled size ({assembled_bytes}) differs from tracked received bytes ({self.bytes_received}). Internal logic discrepancy?")


                    end_time = time.time()
                    download_time = max(0.01, end_time - start_time) # Avoid division by zero
                    download_speed_kbs = (assembled_bytes / 1024) / download_time

                    download_logger.info(f"Successfully assembled '{file_id}' to '{save_path}' - {assembled_bytes} bytes.")
                    logger.info(f"Downloaded {file_id} ({assembled_bytes / 1024:.1f} KB) in {download_time:.2f}s ({download_speed_kbs:.1f} KB/s)")
                    # Log activity
                    activity_logger.info(f"DOWNLOAD_SUCCESS | File: {file_id} | Size: {assembled_bytes} | Time: {download_time:.2f}s")
                    return True, assembled_bytes # Return success and actual bytes written

                except IOError as write_error:
                     download_logger.error(f"IOError writing file {save_path}: {write_error}")
                     logger.error(f"Failed to write downloaded file {file_id}: {write_error}")
                     activity_logger.error(f"DOWNLOAD_FAILED | File: {file_id} | Reason: File write error ({write_error})")
                     return False, self.bytes_received # Failed to save file
                except Exception as assemble_error:
                     download_logger.error(f"Error assembling file {save_path}: {assemble_error}", exc_info=True)
                     logger.error(f"Failed to assemble file {file_id}: {assemble_error}")
                     activity_logger.error(f"DOWNLOAD_FAILED | File: {file_id} | Reason: Assembly error ({assemble_error})")
                     return False, self.bytes_received # Failed during assembly
            else:
                # Download failed (incomplete, timed out, no response, or no fragments received)
                failure_reason = "Unknown"
                if not response_received:
                    failure_reason = "No valid response from server"
                    download_logger.error(f"Download failed: {failure_reason} for any request format.")
                    logger.warning(f"Download failed for {file_id}: Server did not respond.")
                elif time.time() - last_fragment_received_time >= DOWNLOAD_TIMEOUT:
                     failure_reason = f"Timeout after {DOWNLOAD_TIMEOUT}s of inactivity"
                     download_logger.error(f"Download failed: {failure_reason}.")
                     logger.warning(f"Download timed out for {file_id}.")
                elif len(fragments) == 0:
                    failure_reason = "No fragments received despite some response"
                    download_logger.error(f"Download failed: {failure_reason}.")
                    logger.warning(f"Download failed for {file_id}: No fragments received.")
                else: # Incomplete fragments
                     failure_reason = f"Incomplete ({len(fragments)}/{total_fragments_expected or '?'} fragments)"
                     download_logger.error(f"Download failed: {failure_reason}.")
                     logger.warning(f"Download incomplete for {file_id}.")

                # Log the commands that were attempted
                download_logger.debug(f"Attempted Request Formats up to index {request_attempt_index}:")
                for i in range(min(request_attempt_index + 1, len(request_names))):
                    download_logger.debug(f" - {request_names[i]}")

                # Log activity
                activity_logger.warning(f"DOWNLOAD_FAILED | File: {file_id} | Reason: {failure_reason} | Bytes Recv: {self.bytes_received}")

                # Clean up potentially partially written file? Optional.
                # if save_path.exists() and self.bytes_received > 0:
                #     try: save_path.unlink()
                #     except OSError: pass

                return False, self.bytes_received # Return failure

        except Exception as download_error:
            # Catch errors occurring outside the main loop (e.g., initial setup)
            download_logger.error(f"Unhandled error during download setup for {file_path}: {download_error}", exc_info=True)
            logger.error(f"Error setting up download for {file_id}: {download_error}")
            activity_logger.error(f"DOWNLOAD_FAILED | File: {file_id} | Reason: Setup error ({download_error})")
            return False, self.bytes_received

    def close(self):
        """Closes the UDP socket."""
        with self._lock:
            if self.sock:
                try:
                    self.sock.close()
                    download_logger.debug("Downloader socket closed.")
                except Exception as e:
                     download_logger.error(f"Error closing downloader socket: {e}")
                self.sock = None

# ==============================================================
# Main Application Logic & UI (Placeholder)
# ==============================================================

class CSDownloaderApp:
    def __init__(self, args):
        self.args = args
        self.server_ip = args.ip
        self.server_port = args.port
        self.save_dir = Path(args.save_dir)
        self.query = ServerQuery(self.server_ip, self.server_port)
        self.downloader = UDPFileDownloader(self.server_ip, self.server_port, self.save_dir)
        self.status = "Initializing..."
        self.server_info: Optional[Dict] = None
        self.last_query_time = 0
        self.last_successful_query_time = 0
        self.download_queue = Queue()
        self.download_results = collections.deque(maxlen=LAST_FILES_DISPLAY_COUNT) # Store (filename, success, size, time)
        self.download_worker_thread = None
        self.query_thread = None
        self.ui_thread = None
        self.current_download_file = None
        self.current_download_bytes = 0

        # Add files from args to queue
        if args.files:
            for file in args.files:
                self.add_to_download_queue(file)

    def add_to_download_queue(self, filepath: str):
        """Adds a normalized file path to the download queue."""
        if not filepath: return
        normalized_path = filepath.replace('\\', '/').lstrip('/')
        self.download_queue.put(normalized_path)
        logger.info(f"Added to queue: {normalized_path}")
        activity_logger.info(f"QUEUE_ADD | File: {normalized_path}")

    def query_server_periodically(self):
        """Target function for the query thread."""
        logger.debug("Query thread started.")
        while not shutdown_flag.is_set():
            try:
                logger.debug("Attempting server query...")
                self.last_query_time = time.time()
                info = self.query.get_info() # This also updates ping and potentially challenge

                if info:
                    self.server_info = info
                    self.status = "Online"
                    self.last_successful_query_time = self.last_query_time
                    logger.debug(f"Server Info Updated: {info.get('name', 'N/A')} ({info.get('ping', -1)}ms)")
                    activity_logger.info(f"SERVER_ONLINE | Name: {info.get('name', 'N/A')} | Map: {info.get('map', 'N/A')} | Players: {info.get('players', '?')}/{info.get('max_players', '?')} | Ping: {info.get('ping', -1)}ms")

                    # Optional: Get rules/players if needed, but less frequently?
                    # self.query.get_rules()
                    # self.query.get_players()

                else:
                    # get_info returning None could mean timeout OR just a challenge response
                    # Check if the server is truly offline vs just responding with challenge
                    if time.time() - self.last_successful_query_time > SERVER_OFFLINE_TIMEOUT:
                         self.status = f"Offline? (No info for {SERVER_OFFLINE_TIMEOUT}s)"
                         logger.warning(f"Server {self.server_ip}:{self.server_port} appears offline (no INFO response).")
                         activity_logger.warning(f"SERVER_OFFLINE | No INFO response received.")
                         # Clear stale info
                         self.server_info = None
                    elif self.query.last_challenge:
                        self.status = "Challenge Received (Querying...)"
                        logger.debug("Received challenge, server is likely online but info pending.")
                    else:
                         self.status = "Query Failed (Timeout?)"
                         logger.debug("get_info failed, no challenge received either.")
                         # Consider server offline only after repeated failures


                # Wait before next query, check shutdown flag frequently
                wait_interval = 5.0 # Query every 5 seconds
                for _ in range(int(wait_interval / 0.1)):
                    if shutdown_flag.is_set(): break
                    time.sleep(0.1)

            except Exception as e:
                logger.error(f"Error in query thread: {e}", exc_info=True)
                self.status = "Query Error"
                time.sleep(5) # Wait longer after an error

        self.query.close()
        logger.debug("Query thread finished.")


    def download_worker(self):
        """Target function for the download worker thread."""
        logger.debug("Download worker thread started.")
        while not shutdown_flag.is_set():
            try:
                file_to_download = self.download_queue.get(timeout=1.0) # Wait 1s for an item
                self.current_download_file = file_to_download
                self.current_download_bytes = 0 # Reset for UI
                download_start_time = time.time()

                logger.info(f"Worker picked up: {file_to_download}")
                success, bytes_dl = self.downloader.download_file(file_to_download)
                download_end_time = time.time()

                # Store result
                result = (file_to_download, success, bytes_dl, download_end_time - download_start_time)
                self.download_results.append(result)

                self.current_download_file = None # Clear current download state
                self.current_download_bytes = 0
                self.download_queue.task_done() # Mark item as processed

            except Empty:
                # Queue is empty, just loop and wait
                self.current_download_file = None
                self.current_download_bytes = 0
                continue
            except Exception as e:
                 logger.error(f"Error in download worker thread: {e}", exc_info=True)
                 # If a download fails exceptionally, ensure we mark task_done if applicable
                 # and maybe put the file back in queue or log as failed.
                 if self.current_download_file:
                     result = (self.current_download_file, False, 0, 0) # Log as failure
                     self.download_results.append(result)
                     activity_logger.error(f"DOWNLOAD_FAILED | File: {self.current_download_file} | Reason: Worker thread exception ({e})")
                     try:
                         self.download_queue.task_done() # Must call even on exception if item was retrieved
                     except ValueError: pass # If task_done already called or not applicable
                 self.current_download_file = None
                 self.current_download_bytes = 0
                 time.sleep(1) # Avoid busy-looping on error

        self.downloader.close()
        logger.debug("Download worker thread finished.")

    def update_ui(self):
        """Target function for the UI update thread."""
        logger.debug("UI thread started.")
        try:
            # Hide cursor for cleaner display
            sys.stdout.write(HIDE_CURSOR)
            sys.stdout.flush()

            while not shutdown_flag.is_set():
                # --- Gather Data ---
                info = self.server_info
                ping = info.get('ping', self.query.last_ping) if info else self.query.last_ping
                server_name = info.get('name', 'N/A') if info else 'N/A'
                map_name = info.get('map', 'N/A') if info else 'N/A'
                players = f"{info.get('players', '?')}/{info.get('max_players', '?')}" if info else "?/?"
                q_size = self.download_queue.qsize()
                current_dl = self.current_download_file
                # Get current bytes for UI (needs modification in downloader if needed live)
                # For now, just use the total bytes received by the downloader instance
                current_bytes = self.downloader.bytes_received if current_dl else 0

                # --- Format Output ---
                lines = []
                lines.append(f"--- CS1.6 UDP Tester --- [{datetime.now().strftime('%H:%M:%S')}]")
                lines.append(f"Target: {self.server_ip}:{self.server_port}")
                lines.append(f"Status: {self.status} | Ping: {f'{ping}ms' if ping >= 0 else 'N/A'}")
                lines.append(f"Server: {server_name}")
                lines.append(f"Map:    {map_name} | Players: {players}")
                lines.append("-" * 30)
                lines.append(f"Download Queue: {q_size} item(s)")
                if current_dl:
                    # Show current download progress (basic)
                    lines.append(f"Downloading: {current_dl} ({current_bytes / 1024:.1f} KB)")
                else:
                    lines.append("Downloading: Idle")
                lines.append("-" * 30)
                lines.append("Recent Activity (Last 10):")

                # Display recent download results
                if not self.download_results:
                    lines.append("  (No downloads completed yet)")
                else:
                    # Iterate in reverse for most recent first
                    for file, success, size, dl_time in reversed(self.download_results):
                        status_sym = "[ OK ]" if success else "[FAIL]"
                        size_kb = size / 1024
                        time_str = f"{dl_time:.2f}s"
                        lines.append(f"  {status_sym} {file:<30} ({size_kb:>6.1f} KB @ {time_str})")

                lines.append("-" * 30)
                lines.append("Press Ctrl+C to exit.")

                # --- Print to Console ---
                # Move cursor to home, clear screen from cursor down
                sys.stdout.write(CURSOR_TO_HOME)
                sys.stdout.write(CLEAR_SCREEN_FROM_CURSOR)
                for line in lines:
                    sys.stdout.write(line + CLEAR_LINE + "\n") # Clear rest of line just in case
                sys.stdout.flush()

                time.sleep(UI_UPDATE_INTERVAL)

        except Exception as e:
            logger.error(f"Error in UI thread: {e}", exc_info=True)
        finally:
            # Ensure cursor is shown on exit
            sys.stdout.write(SHOW_CURSOR)
            sys.stdout.flush()
            logger.debug("UI thread finished.")

    def run(self):
        """Starts the application threads."""
        global tester_instance
        tester_instance = self # Make instance available for signal handler

        # Start query thread
        self.query_thread = threading.Thread(target=self.query_server_periodically, name="QueryThread", daemon=True)
        self.query_thread.start()

        # Start download worker thread
        self.download_worker_thread = threading.Thread(target=self.download_worker, name="DownloadWorker", daemon=True)
        self.download_worker_thread.start()

        # Start UI thread (if not disabled)
        if not self.args.no_ui:
            # Run UI in the main thread or a separate thread
            # If run in main thread, it blocks here. If separate, main thread can wait/join.
            # Running in a separate thread is cleaner for handling Ctrl+C.
             self.ui_thread = threading.Thread(target=self.update_ui, name="UIThread", daemon=True)
             self.ui_thread.start()
             # Keep main thread alive to catch signals
             while not shutdown_flag.is_set():
                 try:
                     time.sleep(0.5) # Keep main thread alive, periodically check flag
                 except KeyboardInterrupt:
                     # This shouldn't normally be caught here if signal handler works, but as fallback
                     logger.info("KeyboardInterrupt caught in main loop.")
                     self.stop()
        else:
            logger.info("UI disabled. Running in background mode. Press Ctrl+C to exit.")
            # Keep main thread alive to wait for downloads or signals
            try:
                 # Wait for queue to empty if files were provided, or just wait for signal
                 if self.args.files:
                     self.download_queue.join() # Wait for worker to process all initial files
                     logger.info("All initial files processed.")
                 else:
                     # If no files, just wait for Ctrl+C
                     while not shutdown_flag.is_set():
                         time.sleep(0.5)
            except KeyboardInterrupt:
                 logger.info("KeyboardInterrupt caught.")
                 self.stop()


        # Wait for threads to finish after shutdown signal is set
        logger.info("Waiting for threads to finish...")
        # No need to explicitly join daemon threads if main exits cleanly after setting flag

    def stop(self):
        """Signals all threads to stop and closes resources."""
        if not shutdown_flag.is_set():
            logger.info("Shutdown requested...")
            shutdown_flag.set()

            # Optionally add short delay to allow threads to see the flag
            time.sleep(0.1)

            # No need to explicitly join daemon threads, but ensure resources are closed
            self.query.close()
            self.downloader.close()

            # Restore cursor if UI was active
            if not self.args.no_ui:
                sys.stdout.write(SHOW_CURSOR)
                sys.stdout.flush()

            logger.info("Shutdown complete.")


# ==============================================================
# Signal Handling
# ==============================================================
def signal_handler(sig, frame):
    print() # Print newline after ^C
    logger.warning(f"Signal {signal.Signals(sig).name} received. Shutting down...")
    if tester_instance:
        tester_instance.stop()
    else:
        # If instance not set yet, just set the global flag
        shutdown_flag.set()
        # And ensure cursor is shown if potentially hidden
        sys.stdout.write(SHOW_CURSOR)
        sys.stdout.flush()
    # Give threads a moment to exit, then force exit if necessary
    # sys.exit(0) # Let the main thread handle clean exit

# ==============================================================
# Entry Point
# ==============================================================
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Enhanced CS1.6 UDP Server Tester and Downloader.")
    parser.add_argument("ip", help="Server IP address.")
    parser.add_argument("-p", "--port", type=int, default=DEFAULT_PORT, help=f"Server port (default: {DEFAULT_PORT}).")
    parser.add_argument("-s", "--save-dir", default="downloads", help="Directory to save downloaded files (default: downloads).")
    parser.add_argument("-f", "--files", nargs='*', help="Specific file paths to download (e.g., maps/de_dust2.bsp sound/ambience/ctbomb.wav).")
    # parser.add_argument("--guess-files", action="store_true", help="Attempt to guess and download common files (maps, sounds, etc.). NOT IMPLEMENTED.") # Placeholder
    parser.add_argument("--no-ui", action="store_true", help="Disable the interactive terminal UI (run in background/log mode).")
    parser.add_argument("-v", "--verbose", action="count", default=0, help="Increase verbosity level (-v for DEBUG, -vv for TRACE).")
    parser.add_argument("--log-dir", default="logs", help="Directory for log files (default: logs).")
    parser.add_argument("--no-activity-log", action="store_true", help="Disable activity logging to file.")
    parser.add_argument("--no-download-log", action="store_true", help="Disable download debug logging to file.")

    args = parser.parse_args()

    # --- Configure Logging Level ---
    if args.verbose == 1:
        logger.setLevel(logging.DEBUG)
    elif args.verbose >= 2:
        logger.setLevel(TRACE_LEVEL_NUM) # Set main logger to TRACE
        # Optionally set download logger to TRACE too for extreme detail
        # download_logger.setLevel(TRACE_LEVEL_NUM)
    else:
        logger.setLevel(logging.INFO)

    # --- Configure File Logging ---
    log_dir = Path(args.log_dir)
    if not args.no_activity_log or not args.no_download_log:
        try:
            log_dir.mkdir(parents=True, exist_ok=True)
            if not args.no_activity_log:
                setup_file_logging(log_dir, ACTIVITY_LOG_FILENAME, DOWNLOAD_LOG_FILENAME)
            elif not args.no_download_log:
                # Need to call setup_file_logging but only enable download log
                # Modifying setup_file_logging or calling parts of it:
                 download_log_path = log_dir / DOWNLOAD_LOG_FILENAME
                 try:
                     download_debug_handler = logging.FileHandler(download_log_path, mode='a', encoding='utf-8')
                     debug_formatter = logging.Formatter('%(asctime)s [%(levelname)-7s] (%(threadName)s) %(message)s', datefmt='%H:%M:%S.%f')[:-3]
                     download_debug_handler.setFormatter(debug_formatter)
                     download_logger.addHandler(download_debug_handler)
                     download_logger.debug(f"--- Download Debug Log Started ({datetime.now()}) ---")
                     logger.info(f"Download debug logging enabled: {download_log_path}")
                 except Exception as e:
                     logger.error(f"Failed to set up download debug file logging to {download_log_path}: {e}")
                     download_logger.addHandler(logging.NullHandler())
                 # Add null handler for activity logger if it's disabled but setup was called
                 if not activity_logger.hasHandlers(): activity_logger.addHandler(logging.NullHandler())

        except Exception as e:
            logger.error(f"Failed to create log directory '{log_dir}': {e}. File logging disabled.")
            # Add null handlers to prevent errors if logging is attempted
            if not activity_logger.hasHandlers(): activity_logger.addHandler(logging.NullHandler())
            if not download_logger.hasHandlers(): download_logger.addHandler(logging.NullHandler())
    else:
         # Add null handlers if both logs are disabled
         activity_logger.addHandler(logging.NullHandler())
         download_logger.addHandler(logging.NullHandler())


    logger.info(f"Starting CS UDP Tester for {args.ip}:{args.port}")
    logger.info(f"Saving files to: {Path(args.save_dir).resolve()}")
    if args.files: logger.info(f"Files scheduled for download: {', '.join(args.files)}")


    # --- Setup Signal Handling ---
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    # --- Create and Run App ---
    try:
        app = CSDownloaderApp(args)
        app.run() # This blocks until Ctrl+C or downloads complete (in no-UI mode)
    except Exception as e:
        logger.critical(f"Unhandled exception in main execution: {e}", exc_info=True)
        # Ensure cursor is shown on crash
        sys.stdout.write(SHOW_CURSOR)
        sys.stdout.flush()
        sys.exit(1)
    finally:
        # Final cleanup, ensure shutdown sequence runs if not already
        if not shutdown_flag.is_set():
             logger.warning("Main execution finished unexpectedly. Triggering shutdown.")
             if tester_instance:
                 tester_instance.stop()
             else:
                 shutdown_flag.set()
                 sys.stdout.write(SHOW_CURSOR)
                 sys.stdout.flush()


    logger.info("Application finished.")
    sys.exit(0)
