#!/usr/bin/env python3
"""
OrangeFox (ffmaxind.sh) replacement backend + admin panel — portable version.

Speaks the EXACT protocol extracted from the client
(~/workspace/ffmaxind-analysis/response_decrypt.md):

  Request : POST <any non-panel path>, application/x-www-form-urlencoded
            body: game=ORANGEFOX&user_key=<KEY>&serial=<HWID>
  Response: Base64( IV[16 random] || AES-256-CBC( JSON ) )
            key = SHA256("ORANGEFOX_VIP_KEY_2024"), PKCS#7 padding
  Success : {"status": true,  "data": {modname, token, exdate,
                                        expired_date, expiry, seller}}
  Failure : {"status": false, "reason": "<text shown to the user>"}

Portability:
  * AES via the openssl CLI when present, else a built-in pure-Python
    AES-256 (verified byte-identical against openssl).
  * Storage: sqlite file panel.db by default; if DATABASE_URL is set and
    psycopg is installed, Postgres is used instead (needed on hosts with an
    ephemeral filesystem such as Render free tier, where local files are
    wiped on restart — keys must live outside the service).
  * PORT env is honoured (Render and most PaaS set it).

Admin panel: /panel/ or /ofpanel/  (password in panel_password.txt,
created on first run; on ephemeral hosts set PANEL_PASSWORD env instead).
"""
import base64, hashlib, hmac, html, json, os, secrets, shutil, sqlite3, subprocess, time
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HERE = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(HERE, "panel.db")
PW_PATH = os.path.join(HERE, "panel_password.txt")
PASSPHRASE = b"ORANGEFOX_VIP_KEY_2024"
AES_KEY = hashlib.sha256(PASSPHRASE).digest()
AES_KEY_HEX = AES_KEY.hex()
GAME = "ORANGEFOX"
MODNAME = "OrangeFox"
SELLER_DEFAULT = "Shahadut Mod FF"
def _load_database_url():
    """DATABASE_URL resolution order: (1) DATABASE_URL env var; (2) the
    contents of db_url.txt next to this file — a local secret slot that must
    NEVER be committed or uploaded; (3) "" (sqlite fallback)."""
    env = os.environ.get("DATABASE_URL", "").strip()
    if env:
        return env
    try:
        with open(os.path.join(HERE, "db_url.txt")) as f:
            return f.read().strip()
    except Exception:
        return ""


DATABASE_URL = _load_database_url()
USE_PG = False
if DATABASE_URL:
    try:
        import psycopg
        from psycopg.rows import dict_row
        USE_PG = True
    except Exception:
        USE_PG = False

# ------------------------------------------------------- pure-Python AES
def _gf_mul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1B
        b >>= 1
    return p

def _build_sboxes():
    def gf_pow(a, n):
        r = 1
        while n:
            if n & 1:
                r = _gf_mul(r, a)
            a = _gf_mul(a, a)
            n >>= 1
        return r
    sbox, inv = [0] * 256, [0] * 256
    for i in range(256):
        x = 0 if i == 0 else gf_pow(i, 254)
        s = x
        for rot in (1, 2, 3, 4):
            s ^= ((x << rot) | (x >> (8 - rot))) & 0xFF
        s = (s ^ 0x63) & 0xFF
        sbox[i] = s
        inv[s] = i
    return sbox, inv

_SBOX, _INV_SBOX = _build_sboxes()
_RCON = [1]
for _ in range(13):
    _RCON.append(_gf_mul(_RCON[-1], 2))

def _key_expansion(key):
    Nk, Nr = len(key) // 4, len(key) // 4 + 6
    w = [list(key[4 * i:4 * i + 4]) for i in range(Nk)]
    for i in range(Nk, 4 * (Nr + 1)):
        t = list(w[i - 1])
        if i % Nk == 0:
            t = [_SBOX[t[1]] ^ _RCON[i // Nk - 1], _SBOX[t[2]], _SBOX[t[3]], _SBOX[t[0]]]
        elif Nk > 6 and i % Nk == 4:
            t = [_SBOX[c] for c in t]
        w.append([w[i - Nk][j] ^ t[j] for j in range(4)])
    return w, Nr

def _aes_block(block, w, Nr, decrypt=False):
    s = [[block[4 * c + r] for c in range(4)] for r in range(4)]  # s[r][c]
    def add_rk(rnd):
        for c in range(4):
            for r in range(4):
                s[r][c] ^= w[4 * rnd + c][r]
    def sub(inv=False):
        box = _INV_SBOX if inv else _SBOX
        for r in range(4):
            for c in range(4):
                s[r][c] = box[s[r][c]]
    def shift(inv=False):
        for r in range(1, 4):
            row = [s[r][c] for c in range(4)]
            n = -r if inv else r
            for c in range(4):
                s[r][c] = row[(c + n) % 4]
    def mixcol(inv=False):
        for c in range(4):
            a = [s[r][c] for r in range(4)]
            if not inv:
                s[0][c] = _gf_mul(a[0], 2) ^ _gf_mul(a[1], 3) ^ a[2] ^ a[3]
                s[1][c] = a[0] ^ _gf_mul(a[1], 2) ^ _gf_mul(a[2], 3) ^ a[3]
                s[2][c] = a[0] ^ a[1] ^ _gf_mul(a[2], 2) ^ _gf_mul(a[3], 3)
                s[3][c] = _gf_mul(a[0], 3) ^ a[1] ^ a[2] ^ _gf_mul(a[3], 2)
            else:
                s[0][c] = _gf_mul(a[0], 14) ^ _gf_mul(a[1], 11) ^ _gf_mul(a[2], 13) ^ _gf_mul(a[3], 9)
                s[1][c] = _gf_mul(a[0], 9) ^ _gf_mul(a[1], 14) ^ _gf_mul(a[2], 11) ^ _gf_mul(a[3], 13)
                s[2][c] = _gf_mul(a[0], 13) ^ _gf_mul(a[1], 9) ^ _gf_mul(a[2], 14) ^ _gf_mul(a[3], 11)
                s[3][c] = _gf_mul(a[0], 11) ^ _gf_mul(a[1], 13) ^ _gf_mul(a[2], 9) ^ _gf_mul(a[3], 14)
    if not decrypt:
        add_rk(0)
        for rnd in range(1, Nr):
            sub(); shift(); mixcol(); add_rk(rnd)
        sub(); shift(); add_rk(Nr)
    else:
        add_rk(Nr)
        for rnd in range(Nr - 1, 0, -1):
            sub(True); shift(True); add_rk(rnd); mixcol(True)
        sub(True); shift(True); add_rk(0)
    return bytes(s[r][c] for c in range(4) for r in range(4))

_W, _NR = _key_expansion(AES_KEY)

def aes256_cbc_encrypt(plain: bytes, iv: bytes) -> bytes:
    pad = 16 - (len(plain) % 16)
    plain = plain + bytes([pad]) * pad
    out, prev = [], iv
    for i in range(0, len(plain), 16):
        blk = bytes(x ^ y for x, y in zip(plain[i:i + 16], prev))
        enc = _aes_block(blk, _W, _NR)
        out.append(enc)
        prev = enc
    return b"".join(out)

def aes256_cbc_decrypt(ct: bytes, iv: bytes) -> bytes:
    out, prev = [], iv
    for i in range(0, len(ct), 16):
        blk = ct[i:i + 16]
        dec = _aes_block(blk, _W, _NR, decrypt=True)
        out.append(bytes(x ^ y for x, y in zip(dec, prev)))
        prev = blk
    plain = b"".join(out)
    if not plain or plain[-1] < 1 or plain[-1] > 16:
        raise ValueError("bad padding")
    return plain[:-plain[-1]]

_HAVE_OPENSSL = shutil.which("openssl") is not None

def _openssl(data: bytes, iv: bytes, decrypt=False) -> bytes:
    args = ["openssl", "enc", "-aes-256-cbc", "-K", AES_KEY_HEX, "-iv", iv.hex()]
    if decrypt:
        args.append("-d")
    p = subprocess.run(args, input=data, capture_output=True)
    if p.returncode != 0:
        raise RuntimeError("openssl failed: " + p.stderr.decode())
    return p.stdout

def encrypt_response(obj) -> bytes:
    plain = json.dumps(obj, separators=(",", ":")).encode()
    iv = os.urandom(16)
    if _HAVE_OPENSSL:
        ct = _openssl(plain, iv)
    else:
        ct = aes256_cbc_encrypt(plain, iv)
    return base64.b64encode(iv + ct)

def decrypt_response(blob_b64: str) -> str:
    raw = base64.b64decode(blob_b64)
    iv, ct = raw[:16], raw[16:]
    if _HAVE_OPENSSL:
        return _openssl(ct, iv, decrypt=True).decode()
    return aes256_cbc_decrypt(ct, iv).decode()

# ---------------------------------------------------------------- storage
class DB:
    def __init__(self):
        if USE_PG:
            self.con = psycopg.connect(DATABASE_URL, row_factory=dict_row, autocommit=True)
        else:
            self.con = sqlite3.connect(DB_PATH)
            self.con.row_factory = sqlite3.Row
        self._ddl()

    def _ddl(self):
        if USE_PG:
            stmts = [
                """CREATE TABLE IF NOT EXISTS keys(
                    id SERIAL PRIMARY KEY,
                    user_key TEXT UNIQUE NOT NULL,
                    serial TEXT, expires TEXT NOT NULL,
                    blocked INTEGER NOT NULL DEFAULT 0,
                    seller TEXT DEFAULT '', note TEXT DEFAULT '',
                    created TEXT NOT NULL, last_login TEXT)""",
                """CREATE TABLE IF NOT EXISTS login_log(
                    id SERIAL PRIMARY KEY,
                    ts TEXT NOT NULL, user_key TEXT, serial TEXT,
                    result TEXT NOT NULL, detail TEXT DEFAULT '')""",
                """CREATE TABLE IF NOT EXISTS ghost_keys(
                    id SERIAL PRIMARY KEY,
                    user_key TEXT UNIQUE NOT NULL,
                    hwid TEXT, expires TEXT NOT NULL,
                    blocked INTEGER NOT NULL DEFAULT 0,
                    seller TEXT DEFAULT '', note TEXT DEFAULT '',
                    created TEXT NOT NULL, last_login TEXT)""",
                """CREATE TABLE IF NOT EXISTS ghost_log(
                    id SERIAL PRIMARY KEY,
                    ts TEXT NOT NULL, user_key TEXT, hwid TEXT,
                    result TEXT NOT NULL, detail TEXT DEFAULT '')""",
                """CREATE TABLE IF NOT EXISTS ghost_tokens(
                    id SERIAL PRIMARY KEY,
                    token TEXT UNIQUE NOT NULL, key_id INTEGER NOT NULL,
                    created TEXT NOT NULL)""",
                """CREATE TABLE IF NOT EXISTS vsp3_debug(
                    id SERIAL PRIMARY KEY,
                    ts TEXT NOT NULL, path TEXT, routing TEXT,
                    headers TEXT, raw_body TEXT, inner_json TEXT,
                    reply TEXT, http_code INTEGER)"""]
        else:
            stmts = [
                """CREATE TABLE IF NOT EXISTS keys(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_key TEXT UNIQUE NOT NULL,
                    serial TEXT, expires TEXT NOT NULL,
                    blocked INTEGER NOT NULL DEFAULT 0,
                    seller TEXT DEFAULT '', note TEXT DEFAULT '',
                    created TEXT NOT NULL, last_login TEXT)""",
                """CREATE TABLE IF NOT EXISTS login_log(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts TEXT NOT NULL, user_key TEXT, serial TEXT,
                    result TEXT NOT NULL, detail TEXT DEFAULT '')""",
                """CREATE TABLE IF NOT EXISTS ghost_keys(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_key TEXT UNIQUE NOT NULL,
                    hwid TEXT, expires TEXT NOT NULL,
                    blocked INTEGER NOT NULL DEFAULT 0,
                    seller TEXT DEFAULT '', note TEXT DEFAULT '',
                    created TEXT NOT NULL, last_login TEXT)""",
                """CREATE TABLE IF NOT EXISTS ghost_log(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts TEXT NOT NULL, user_key TEXT, hwid TEXT,
                    result TEXT NOT NULL, detail TEXT DEFAULT '')""",
                """CREATE TABLE IF NOT EXISTS ghost_tokens(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    token TEXT UNIQUE NOT NULL, key_id INTEGER NOT NULL,
                    created TEXT NOT NULL)""",
                """CREATE TABLE IF NOT EXISTS vsp3_debug(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ts TEXT NOT NULL, path TEXT, routing TEXT,
                    headers TEXT, raw_body TEXT, inner_json TEXT,
                    reply TEXT, http_code INTEGER)"""]
        cur = self.con.cursor()
        for s in stmts:
            cur.execute(s)
        self.con.commit()

    def execute(self, sql, params=()):
        if USE_PG:
            sql = sql.replace("?", "%s")
            if sql.startswith("INSERT OR IGNORE"):
                sql = sql.replace("INSERT OR IGNORE", "INSERT") + " ON CONFLICT DO NOTHING"
        cur = self.con.cursor()
        cur.execute(sql, params)
        return cur

    def commit(self):
        self.con.commit()

    def close(self):
        self.con.close()

def db():
    return DB()

def now_iso():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")

def log_attempt(con, key, serial, result, detail=""):
    con.execute("INSERT INTO login_log(ts,user_key,serial,result,detail) VALUES(?,?,?,?,?)",
                (now_iso(), key or "", serial or "", result, detail))
    con.commit()

# ---------------------------------------------------------------- /connect
def handle_connect(form):
    game = (form.get("game") or [""])[0]
    user_key = (form.get("user_key") or [""])[0].strip()
    serial = (form.get("serial") or [""])[0].strip()
    con = db()
    try:
        if game != GAME:
            log_attempt(con, user_key, serial, "fail", "wrong game")
            return encrypt_response({"status": False, "message": "Invalid game"})
        if not user_key:
            log_attempt(con, user_key, serial, "fail", "empty key")
            return encrypt_response({"status": False, "message": "Invalid JSON format"})
        row = con.execute("SELECT * FROM keys WHERE user_key=?", (user_key,)).fetchone()
        if row is None:
            log_attempt(con, user_key, serial, "fail", "key not found")
            return encrypt_response({"status": False, "reason": "Invalid key"})
        if row["blocked"]:
            log_attempt(con, user_key, serial, "fail", "blocked")
            return encrypt_response({"status": False, "reason": "Key blocked"})
        today = datetime.now(timezone.utc).date().isoformat()
        if row["expires"] < today:
            log_attempt(con, user_key, serial, "fail", "expired")
            return encrypt_response({"status": False, "reason": "Key expired"})
        if row["serial"] and serial and row["serial"] != serial:
            log_attempt(con, user_key, serial, "fail", "serial mismatch")
            return encrypt_response({"status": False, "reason": "Key used on another device"})
        if not row["serial"] and serial:
            con.execute("UPDATE keys SET serial=? WHERE id=?", (serial, row["id"]))
        con.execute("UPDATE keys SET last_login=? WHERE id=?", (now_iso(), row["id"]))
        con.commit()
        log_attempt(con, user_key, serial, "success")
        exp = row["expires"]
        return encrypt_response({
            "status": True,
            "data": {
                "modname": MODNAME,
                "token": secrets.token_hex(16),
                "exdate": exp,
                "expired_date": exp,
                "expiry": exp,
                "seller": row["seller"] or SELLER_DEFAULT,
            },
        })
    finally:
        con.close()


# ------------------------------------------------- Ghost Hack (vsx) API
# Protocol from ~/workspace/vsx-analysis/response_format.md:
#   POST /api/auth1   JSON {key, hwid, ...} ->
#     {"success":true,"expiry":D,"expires_at":D,"seller":S,"session_token":T}
#     {"success":false,"error":"<shown to user>"}
#   GET  /offset      header X-Session-Token ->
#     {"cfg":{},"offsets":{}} for an issued token, empty body otherwise.
GHOST_AUTH_PATHS = ("/api/auth1", "/api/client/auth", "/api/auth12")
GHOST_OFFSET_PATHS = ("/offset", "/api/offsets")
GHOST_CFG = json.loads('{"_credit": "Server-managed GameCfg offsets \\u2014 client har feature ke offsets yahan se fetch karta hai", "head": 1704, "hip": 1712, "spine": 1720, "root": 1744, "left_ankle": 1760, "right_ankle": 1768, "left_shoulder": 1808, "right_shoulder": 1816, "left_hand": 1832, "right_hand": 1824, "collider": 1752, "main_camera": 904, "follow_camera": 1688, "is_firing": 2008, "aim_info": 3672, "aim_start": 76, "aim_dir": 64, "player_rot": 1460, "game_facade_rva": 181833240, "gf_static": 184, "base_game": 8, "match": 144, "match_running": 204, "local_player": 216, "dictionary": 192, "entity_list": 24, "avatar_mgr": 1912, "cam_comp": 48, "cam_intptr": 16, "cam_matrix": 256, "xf_obj": 16, "xf_index": 64, "xf_matrix": 56, "xf_list": 24, "xf_indices": 32, "xf_stride": 48, "avatar_simple": 312, "avatar_visible": 257, "uma_data": 40, "uma_dead": 129, "enemy_dead": 124, "enemy_knock": 0, "enemy_name": 1184, "enemy_bot": 1192, "knock_comp": 7520, "knock_flag": 16, "hp_c0": 112, "hp_c1": 16, "hp_c2": 32, "hp_val": 24, "time_service": 32, "time_scale": 44, "observe_cur": 256, "observe_player": 48, "ghost_hack": 2068, "dict_count": 32, "dict_array_header": 32, "dict_entry_stride": 24, "dict_entry_value": 16, "player_hed_colider": 1752, "player_col_write": 128, "player_death_info": 8848, "uma_data_skip": 129, "main_camera_fallback": 904, "weapon_instance": 1440, "reload_instance": 1800, "inventory_manager": 1864, "status_struct": 7520, "firing_state": 2056, "view_rotation": 1460, "is_spectating": 124, "head_collider": 1752, "aim_target_write": 128, "client_bot_check": 1192, "name_ptr": 1184, "aiming_info": 3672, "aiming_info_start": 76, "aiming_info_dir": 64, "health_chain1": 112, "health_chain2": 16, "health_chain3": 32, "health_value": 24, "is_dead": 124, "time_service_speed": 44, "weapon_data": 136, "recoil_value": 24, "fast_reload_trigger": 217, "status_data": 32, "state_id": 16, "uma_simple": 312, "is_visible": 257, "avatar_is_dead": 129, "active_item": 160, "weapon_component": 128, "no_recoil": 24, "item_data": 40, "weapon_id": 72, "bone_head": 1704, "bone_chest": 1720, "bone_hip": 1712, "bone_feet": 1744, "bone_lshoulder": 1808, "bone_rshoulder": 1816, "bone_lhand": 1832, "bone_rhand": 1824, "bone_lankle": 1760, "bone_rankle": 1768, "xf_enemy_pos_force": 56, "s_aim2": 3664, "s_aim3": 64, "s_aim4": 208, "player_attributes": 1904, "shoot_no_reload": 273, "base_game_ptr": 184, "cam_object": 48, "xf_index_size": 4}')


def ghost_log(con, key, hwid, result, detail=""):
    con.execute("INSERT INTO ghost_log(ts,user_key,hwid,result,detail) VALUES(?,?,?,?,?)",
                (now_iso(), key or "", hwid or "", result, detail))
    con.commit()

def ghost_auth(payload):
    if not isinstance(payload, dict):
        return {"success": False, "error": "Invalid request"}
    user_key = str(payload.get("key") or "").strip()
    hwid = str(payload.get("hwid") or "").strip()
    con = db()
    try:
        if not user_key:
            ghost_log(con, user_key, hwid, "fail", "empty key")
            return {"success": False, "error": "Invalid Key!"}
        row = con.execute("SELECT * FROM ghost_keys WHERE user_key=?", (user_key,)).fetchone()
        if row is None:
            ghost_log(con, user_key, hwid, "fail", "key not found")
            return {"success": False, "error": "Invalid Key!"}
        if row["blocked"]:
            ghost_log(con, user_key, hwid, "fail", "blocked")
            return {"success": False, "error": "Key blocked"}
        today = datetime.now(timezone.utc).date().isoformat()
        if row["expires"] < today:
            ghost_log(con, user_key, hwid, "fail", "expired")
            return {"success": False, "error": "Key expired"}
        if row["hwid"] and hwid and row["hwid"] != hwid:
            ghost_log(con, user_key, hwid, "fail", "hwid mismatch")
            return {"success": False, "error": "Key used on another device"}
        if not row["hwid"] and hwid:
            con.execute("UPDATE ghost_keys SET hwid=? WHERE id=?", (hwid, row["id"]))
        con.execute("UPDATE ghost_keys SET last_login=? WHERE id=?", (now_iso(), row["id"]))
        token = secrets.token_hex(24)
        con.execute("INSERT INTO ghost_tokens(token,key_id,created) VALUES(?,?,?)",
                    (token, row["id"], now_iso()))
        con.commit()
        ghost_log(con, user_key, hwid, "success")
        exp = row["expires"] + " 23:59:59"
        return {"success": True, "expiry": exp, "expires_at": exp,
                "seller": row["seller"] or SELLER_DEFAULT, "session_token": token,
                "file_url": None, "version": None, "announcement": None,
                "is_trial": False}
    finally:
        con.close()

def ghost_offsets(token):
    """Bytes to return for GET offsets; empty body when token is unknown."""
    if not token:
        return b""
    con = db()
    try:
        row = con.execute("SELECT id FROM ghost_tokens WHERE token=?", (token,)).fetchone()
        if row is None:
            return b""
        return json.dumps({"success": True, "cfg": GHOST_CFG, "offsets": GHOST_CFG}).encode()
    finally:
        con.close()

# ------------------------------------------------- VSX new core (VSP3 / VSP-WIRE-2)
# Protocol: ~/workspace/vsx-core-analysis/NEW_PROTOCOL.md (proven spec).
# Two stages multiplexed by body shape on the SAME path (/api/auth1):
#   stage 1: plaintext {"key","hwid", ...}       -> {"success":true,"proto":"VSP-WIRE-2","wire":{...}}
#            (loader 1.3.0 native sends extra game/client_version/version_code
#             fields; its Java side sends the same object with fields appended
#             AFTER the closing brace, which is salvaged, not rejected)
#   stage 2: envelope {"cpk","ct","iv","kid",...} -> encrypted envelope reply, sid = hex(K4)
#   old Ghost: body carrying apk_hash/device_info/lib_hash -> legacy ghost_auth
#            (unchanged; the live team's old client must keep working)
# Crypto is stdlib-only: X25519 (RFC 7748 ladder), HKDF-SHA256 (hmac/hashlib),
# AES-256-GCM built on the pure-Python AES block function above.
PUBLIC_BASE = os.environ.get("PANEL_BASE", "https://ofkey.onrender.com")
VSP3_PRIV_PATH = os.path.join(HERE, "vsp3_privkey.bin")
VSP3_PUB_PATH = os.path.join(HERE, "vsp3_pubkey.hex")
VSP3_KID = 1
_PACK_PATH = os.path.join(HERE, "genuine_pack.json")
if os.path.exists(_PACK_PATH):
    VSP_PACK = json.load(open(_PACK_PATH))
else:
    # No genuine pack was ever captured from the real server (stage-2 success
    # payloads for the Trial key contain no "pack" member at all — see
    # genuine_stage2_response.json). Empty object: the client parses and
    # extracts it fine (proven in emulation, run_resp_valid.log).
    VSP_PACK = {}

_P25519 = 2 ** 255 - 19

def _x25519(scal, u_bytes):
    k = bytearray(scal)
    k[0] &= 248
    k[31] = (k[31] & 63) | 64
    n = int.from_bytes(k, "little")
    x1 = int.from_bytes(u_bytes, "little") & ((1 << 255) - 1)
    x2, z2, x3, z3, swap = 1, 0, x1, 1, 0
    for t in range(254, -1, -1):
        kt = (n >> t) & 1
        swap ^= kt
        if swap:
            x2, x3 = x3, x2
            z2, z3 = z3, z2
        swap = kt
        A = (x2 + z2) % _P25519
        AA = A * A % _P25519
        B = (x2 - z2) % _P25519
        BB = B * B % _P25519
        E = (AA - BB) % _P25519
        C = (x3 + z3) % _P25519
        D = (x3 - z3) % _P25519
        DA = D * A % _P25519
        CB = C * B % _P25519
        x3 = (DA + CB) ** 2 % _P25519
        z3 = x1 * (DA - CB) ** 2 % _P25519
        x2 = AA * BB % _P25519
        z2 = E * (AA + 121665 * E) % _P25519
    if swap:
        x2, x3 = x3, x2
        z2, z3 = z3, z2
    return (x2 * pow(z2, _P25519 - 2, _P25519) % _P25519).to_bytes(32, "little")

def vsp3_keypair():
    """Panel's own X25519 keypair (kid=1).

    If PANEL_PASSWORD is set, the private key is DERIVED deterministically —
    priv = SHA-256(b"VSP3-PRIVKEY-V1|" + PANEL_PASSWORD) — so an ephemeral
    host needs no key file and the patched core stays valid across restarts
    and redeploys. Otherwise: raw 32 B private-key file, mode 600."""
    pw = os.environ.get("PANEL_PASSWORD", "")
    if pw:
        priv = hashlib.sha256(b"VSP3-PRIVKEY-V1|" + pw.encode()).digest()
        return priv, _x25519(priv, (9).to_bytes(32, "little"))
    if not os.path.exists(VSP3_PRIV_PATH):
        priv = os.urandom(32)
        with open(VSP3_PRIV_PATH, "wb") as f:
            f.write(priv)
        os.chmod(VSP3_PRIV_PATH, 0o600)
        with open(VSP3_PUB_PATH, "w") as f:
            f.write(_x25519(priv, (9).to_bytes(32, "little")).hex())
    priv = open(VSP3_PRIV_PATH, "rb").read()
    return priv, _x25519(priv, (9).to_bytes(32, "little"))

def _hkdf(salt, ikm, ctr, kid=VSP3_KID, length=32):
    info = b"VSP-SEC-3" + bytes([ctr]) + kid.to_bytes(4, "big")
    prk = hmac.new(salt, ikm, hashlib.sha256).digest()
    out, t, i = b"", b"", 1
    while len(out) < length:
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        out += t
        i += 1
    return out[:length]

def _aad(kid, t, rid, direction):
    return (b"VSP-SEC-3" + kid.to_bytes(4, "big") + (0).to_bytes(8, "big")
            + int(t).to_bytes(8, "big") + rid + bytes([direction]))

def _gmul(x, y):
    z = 0
    v = y
    for i in range(128):
        if (x >> (127 - i)) & 1:
            z ^= v
        if v & 1:
            v = (v >> 1) ^ 0xE1000000000000000000000000000000
        else:
            v >>= 1
    return z

def _gcm(key, iv, data, aad, decrypt=False, tag=None):
    """AES-256-GCM on the pure-Python AES above. Encrypt -> ct||tag(16).
    Decrypt: data is ciphertext without tag; tag passed separately."""
    w, Nr = _key_expansion(key)
    def enc(b):
        return _aes_block(b, w, Nr)
    H = int.from_bytes(enc(b"\0" * 16), "big")
    def ghash(d):
        y = 0
        for i in range(0, len(d), 16):
            blk = int.from_bytes(d[i:i + 16].ljust(16, b"\0"), "big")
            y = _gmul(y ^ blk, H)
        return y
    def ctr_crypt(d):
        out = bytearray()
        ctr = 1
        for i in range(0, len(d), 16):
            ctr += 1
            ks = enc(iv + ctr.to_bytes(4, "big"))
            out += bytes(a ^ b for a, b in zip(d[i:i + 16], ks))
        return bytes(out)
    pad = lambda b: b + b"\0" * ((16 - len(b) % 16) % 16)
    if not decrypt:
        ct = ctr_crypt(data)
        s = ghash(pad(aad) + pad(ct) + (len(aad) * 8).to_bytes(8, "big") + (len(ct) * 8).to_bytes(8, "big"))
        t = bytes(a ^ b for a, b in zip(s.to_bytes(16, "big"), enc(iv + b"\0\0\0\1")))
        return ct + t
    s = ghash(pad(aad) + pad(data) + (len(aad) * 8).to_bytes(8, "big") + (len(data) * 8).to_bytes(8, "big"))
    t = bytes(a ^ b for a, b in zip(s.to_bytes(16, "big"), enc(iv + b"\0\0\0\1")))
    if not hmac.compare_digest(t, tag or b""):
        raise ValueError("gcm tag mismatch")
    return ctr_crypt(data)

def _ghost_validate(user_key, hwid):
    """ghost_auth's validation semantics, shared by VSP stage 1 and stage 2.
    Returns (row, None) on success or (None, (detail, user_text, code))."""
    con = db()
    try:
        if not user_key:
            ghost_log(con, user_key, hwid, "fail", "empty key")
            return None, ("empty key", "Invalid Key!", "invalid_key")
        row = con.execute("SELECT * FROM ghost_keys WHERE user_key=?", (user_key,)).fetchone()
        if row is None:
            ghost_log(con, user_key, hwid, "fail", "key not found")
            return None, ("key not found", "Invalid Key!", "invalid_key")
        if row["blocked"]:
            ghost_log(con, user_key, hwid, "fail", "blocked")
            return None, ("blocked", "Key blocked", "blocked")
        today = datetime.now(timezone.utc).date().isoformat()
        if row["expires"] < today:
            ghost_log(con, user_key, hwid, "fail", "expired")
            return None, ("expired", "Key expired", "expired")
        if row["hwid"] and hwid and row["hwid"] != hwid:
            ghost_log(con, user_key, hwid, "fail", "hwid mismatch")
            return None, ("hwid mismatch", "Key used on another device", "hwid_mismatch")
        if not row["hwid"] and hwid:
            con.execute("UPDATE ghost_keys SET hwid=? WHERE id=?", (hwid, row["id"]))
        con.execute("UPDATE ghost_keys SET last_login=? WHERE id=?", (now_iso(), row["id"]))
        con.commit()
        ghost_log(con, user_key, hwid, "success")
        return row, None
    finally:
        con.close()

def _wire_obj(row, hwid, cv=""):
    now = int(time.time())
    return {"ok": True, "sid": secrets.token_hex(32),
            "file_url": PUBLIC_BASE + "/api/client/download?token=" + secrets.token_hex(24),
            "lic_exp": row["expires"] + " 23:59:59", "bin_ver": "2.1", "cv": cv,
            "version_active": False, "ttl": 600, "exp_at": now + 600, "st": now,
            "seller": row["seller"] or SELLER_DEFAULT, "note": None, "trial": False}

def vsp_stage1(payload):
    """Plaintext loader stage. Returns (http_code, obj). Mirrors the real
    server's shapes from live_probe_2026-11-17.json, plus the flat
    expiry/seller fields the loader's Java side reads (its native side
    reads success + the wire object)."""
    if not isinstance(payload, dict):
        return 400, {"success": False, "error": "missing_key_or_hwid"}
    user_key = str(payload.get("key") or "").strip()
    hwid = str(payload.get("hwid") or "").strip()
    if not user_key or not hwid:
        return 400, {"success": False, "error": "missing_key_or_hwid"}
    row, err = _ghost_validate(user_key, hwid)
    if err:
        return 200, {"success": False, "error": err[1]}
    wire = _wire_obj(row, hwid)
    return 200, {"success": True, "proto": "VSP-WIRE-2", "wire": wire,
                 "expiry": row["expires"] + " 23:59:59",
                 "expiry_date": row["expires"],
                 "seller": row["seller"] or SELLER_DEFAULT,
                 "message": "Login successful",
                 "_keyId": row["id"], "_hwid": hwid, "_arch": "arm64-v8a"}

def _salvage_json_object(raw):
    """Recover the first complete {...} object from a malformed body.

    Loader 1.3.0's Java side builds {"key","hwid","game":"PUBG"} and then
    appends ,"client_version":...,"version_code":...,"vhash":... AFTER the
    closing brace, so json.loads fails on trailing data. Scan for the first
    balanced object (string-aware) and parse just that slice. Returns a
    dict, or None when nothing parses."""
    try:
        text = raw.decode("utf-8", "replace")
    except Exception:
        return None
    start = text.find("{")
    if start < 0:
        return None
    depth = 0
    in_str = False
    esc = False
    for i in range(start, len(text)):
        ch = text[i]
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                try:
                    obj = json.loads(text[start:i + 1])
                except Exception:
                    return None
                return obj if isinstance(obj, dict) else None
    return None

# Old-Ghost (kamarul-era) client markers: a body carrying any of these is
# the old .sh client's auth call and must keep the legacy ghost_auth reply
# (session_token), even though it also carries key + hwid.
_OLD_GHOST_MARKERS = {"apk_hash", "device_info", "lib_hash"}
# Fields a stage-1 body may carry (core + loader 1.3.0 native/Java shapes).
_STAGE1_FIELDS = {"key", "hwid", "game", "client_version", "version_code", "vhash"}

def _sig_expect(key_bytes, headers, raw_body):
    return hmac.new(key_bytes,
                    (headers.get("X-Req-Ts") or "").encode() + b"."
                    + (headers.get("X-Req-Nonce") or "").encode() + b"." + raw_body,
                    hashlib.sha256).hexdigest()

def _body_sig_ok(headers, raw_body, hwid=None):
    """True iff the request carries a valid VSP X-Body-Sig over the raw body
    (HMAC-SHA256, message "<ts>.<nonce>.<body>"). Two key rules are accepted:
    the h968/spec rule (key = "VSP_BODY_KEY_V2") and the sibling-core rule
    (key = <hwid> + "VSP_BODY_KEY_V2", hwid prepended — see V13_FORMAT.md
    section 4; tried when the request's hwid is known). The new core signs
    EVERY auth request this way; the legacy Ghost client never sends these
    headers, so this cleanly separates the two on the shared path."""
    sig_h = (headers.get("X-Body-Sig") or "").lower()
    if not sig_h:
        return False
    if hmac.compare_digest(_sig_expect(b"VSP_BODY_KEY_V2", headers, raw_body), sig_h):
        return True
    if hwid:
        return hmac.compare_digest(
            _sig_expect((str(hwid) + "VSP_BODY_KEY_V2").encode(), headers, raw_body), sig_h)
    return False

# ------------------------------------------------- V13 inner layer (sibling core)
# The sibling core wraps its auth fields in {"body","iv","key","v":"V13"}
# BEFORE the VSP3 seal, and re-sends the same blob bare as its fallback.
# Recipe (V13_FORMAT.md section 1, verified on captured phone traffic):
#   R = b64decode(key) (32 B raw session key), IV = b64decode(iv) (16 B);
#   ct[i] = b64decode(body)[i] XOR R[i mod 16];
#   fields = AES-256-CBC-decrypt(ct, key=R, iv=IV), PKCS#7 unpad.
def _is_v13_blob(obj):
    return (isinstance(obj, dict) and obj.get("v") == "V13"
            and all(k in obj for k in ("body", "iv", "key")))

def _aes256_cbc_decrypt_any(ct, key, iv):
    """AES-CBC decrypt with an arbitrary key, on the pure-Python AES above
    (decrypt direction), with PKCS#7 unpad. Stdlib-only."""
    if len(key) not in (16, 24, 32) or len(iv) != 16 or not ct or len(ct) % 16:
        raise ValueError("bad aes params")
    w, Nr = _key_expansion(key)
    out, prev = [], iv
    for i in range(0, len(ct), 16):
        blk = ct[i:i + 16]
        dec = _aes_block(blk, w, Nr, decrypt=True)
        out.append(bytes(x ^ y for x, y in zip(dec, prev)))
        prev = blk
    plain = b"".join(out)
    if not plain or plain[-1] < 1 or plain[-1] > 16:
        raise ValueError("bad padding")
    return plain[:-plain[-1]]

def _v13_unwrap(obj):
    """Unwrap a V13 blob to its fields dict; None when it does not open."""
    try:
        R = base64.b64decode(obj["key"])
        iv = base64.b64decode(obj["iv"])
        masked = base64.b64decode(obj["body"])
        if len(R) != 32 or len(iv) != 16 or not masked:
            return None
        ct = bytes(b ^ R[i % 16] for i, b in enumerate(masked))
        fields = json.loads(_aes256_cbc_decrypt_any(ct, R, iv).decode("utf-8"))
        return fields if isinstance(fields, dict) else None
    except Exception:
        return None


def vsp_stage2(env, raw_body, headers, debug=None):
    """Encrypted core stage. Returns (http_code, obj). If debug is a dict,
    it is filled passively for the VSP3 debug capture (decrypted inner
    payload under "inner", reply payload dict under "reply_payload",
    failure reason under "fail"); verdicts and replies are unchanged."""
    try:
        if int(env.get("v") or 0) != 3:
            raise ValueError("bad v")
        kid = int(env.get("kid") or VSP3_KID)
        cpk = base64.b64decode(env["cpk"])
        n_c = base64.b64decode(env["n_c"])
        rid = base64.b64decode(env["rid"])
        iv = base64.b64decode(env["iv"])
        ct = base64.b64decode(env["ct"])
        t = int(env["t"])
        if len(cpk) != 32 or len(n_c) != 16 or len(rid) != 16 or len(iv) != 12 or len(ct) < 16:
            raise ValueError("bad field lengths")
    except Exception:
        if debug is not None:
            debug["fail"] = "bad_envelope"
        return 400, {"success": False, "error": "bad_envelope"}
    # The GCM tag is the gate: open the envelope FIRST. (The sibling core's
    # X-Body-Sig uses an hwid-prefixed key and the hwid only becomes known
    # after the open — inside the V13 layer — so the sig check must follow
    # decryption, not precede it.)
    priv, _pub = vsp3_keypair()
    shared = _x25519(priv, cpk)
    k1 = _hkdf(n_c, shared, 1, kid)
    try:
        pt = _gcm(k1, iv, ct[:-16], _aad(kid, t, rid, 0), decrypt=True, tag=ct[-16:])
        inner = json.loads(pt.decode("utf-8"))
        if not isinstance(inner, dict):
            raise ValueError("inner not an object")
    except Exception:
        if debug is not None:
            debug["fail"] = "decrypt_fail"
        return 400, {"success": False, "error": "decrypt_fail"}
    fields = inner
    if _is_v13_blob(inner):
        fields = _v13_unwrap(inner)
        if fields is None:
            if debug is not None:
                debug["fail"] = "decrypt_fail"
            return 400, {"success": False, "error": "decrypt_fail"}
    sig_h = headers.get("X-Body-Sig") or ""
    if sig_h and not _body_sig_ok(headers, raw_body,
                                  hwid=str(fields.get("hwid") or "")):
        if debug is not None:
            debug["fail"] = "bad_sig"
        return 400, {"success": False, "error": "bad_sig"}
    payload = _stage2_payload(fields)
    if debug is not None:
        if _is_v13_blob(inner):
            debug["inner"] = json.dumps(fields, ensure_ascii=False)
        else:
            debug["inner"] = pt.decode("utf-8", "replace")
        debug["reply_payload"] = payload
    return 200, _stage2_seal_reply(kid, n_c, rid, shared, payload)

def _stage2_payload(inner):
    """Validate the decrypted inner payload against ghost_keys and build the
    reply payload (genuine-server shape + spec success/error vocabulary)."""
    user_key = str(inner.get("key") or "").strip()
    hwid = str(inner.get("hwid") or "").strip()
    row, err = _ghost_validate(user_key, hwid)
    if err:
        payload = {"success": False, "ok": False, "st": "INACTIVE",
                   "error": err[1], "message": err[1]}
        if err[2] == "invalid_key":
            payload["invalid_key"] = True
        return payload
    payload = _wire_obj(row, hwid, cv=str(inner.get("client_version") or ""))
    # NOTE: "st" stays the numeric wire start-time exactly as the genuine
    # server sends it (see genuine_stage2_response.json); the ACTIVE status
    # is carried by ok/success, as in the genuine payload + parser vocabulary.
    payload.update({"success": True, "message": "Login successful",
                    "expiry": row["expires"] + " 23:59:59",
                    "expiry_date": row["expires"], "pack": VSP_PACK})
    return payload

def _stage2_seal_reply(kid, n_c, rid, shared, payload):
    """Encrypt a reply payload into a response envelope (sid = hex(K4))."""
    now = int(time.time())
    n_s = os.urandom(16)
    k3 = _hkdf(n_c + n_s, shared, 3, kid)
    k4 = _hkdf(n_c + n_s, shared, 4, kid)
    riv = os.urandom(12)
    rct = _gcm(k3, riv, json.dumps(payload, separators=(",", ":")).encode(),
               _aad(kid, now, rid, 1))
    return {"v": 3, "kid": kid, "n_s": base64.b64encode(n_s).decode(),
            "sid": k4.hex(), "ctr": 0, "rid": base64.b64encode(rid).decode(),
            "t": now, "iv": base64.b64encode(riv).decode(),
            "ct": base64.b64encode(rct).decode()}

# ------------------------------------------------- VSP3 debug capture
# Passive request/response capture for the client-auth handler: every POST
# to a GHOST_AUTH_PATH is recorded (selected headers, raw body, routing
# decision, decrypted stage-2 payload, reply) in the vsp3_debug table, so a
# failing client can be diagnosed from what it actually sent. Capture is
# observation only — it never alters a verdict, route, or reply — and any
# failure inside the capture itself is swallowed.
_VSP3_DEBUG_HEADERS = ("X-Body-Sig", "X-Client-Signature", "X-Req-Ts",
                       "X-Req-Nonce", "User-Agent", "Content-Type")

def _vsp3_debug_log(entry):
    try:
        con = db()
        con.execute(
            "INSERT INTO vsp3_debug(ts,path,routing,headers,raw_body,inner_json,reply,http_code)"
            " VALUES(?,?,?,?,?,?,?,?)",
            (now_iso(), entry.get("path") or "", entry.get("routing") or "",
             json.dumps(entry.get("headers") or {}, ensure_ascii=False),
             entry.get("raw_body") or "", entry.get("inner") or "",
             entry.get("reply") or "", int(entry.get("http_code") or 0)))
        con.execute("DELETE FROM vsp3_debug WHERE id NOT IN"
                    " (SELECT id FROM vsp3_debug ORDER BY id DESC LIMIT 100)")
        con.commit()
        con.close()
    except Exception:
        pass

def _vsp3_debug_entries(limit=50):
    con = db()
    try:
        rows = con.execute("SELECT * FROM vsp3_debug ORDER BY id DESC LIMIT ?",
                           (int(limit),)).fetchall()
        return [dict(r) for r in rows]
    finally:
        con.close()

# ---------------------------------------------------------------- panel
def panel_password():
    env = os.environ.get("PANEL_PASSWORD", "")
    if env:
        return env
    if not os.path.exists(PW_PATH):
        with open(PW_PATH, "w") as f:
            f.write(secrets.token_urlsafe(9))
        os.chmod(PW_PATH, 0o600)
    return open(PW_PATH).read().strip()

SESSIONS = set()

def page(title, body):
    return ("<!doctype html><meta charset=utf-8>"
            f"<title>{html.escape(title)}</title>"
            "<style>body{font-family:sans-serif;max-width:900px;margin:20px auto;padding:0 10px}"
            "table{border-collapse:collapse;width:100%}td,th{border:1px solid #999;padding:4px 8px}"
            "input,button{padding:6px;margin:2px}</style>"
            f"<h2>{html.escape(title)}</h2>" + body).encode()

def is_panel_path(path):
    return path.startswith("/panel") or path.startswith("/ofpanel")

def norm_panel(path):
    if path.startswith("/ofpanel"):
        return "/panel" + path[len("/ofpanel"):]
    return path

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="text/html; charset=utf-8", extra=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _form(self):
        n = int(self.headers.get("Content-Length") or 0)
        return parse_qs(self.rfile.read(n).decode("utf-8", "replace"))

    def _authed(self):
        cookie = self.headers.get("Cookie") or ""
        return any(part.strip().startswith("sess=") and part.strip()[5:] in SESSIONS
                   for part in cookie.split(";"))

    def do_GET(self):
        path = urlparse(self.path).path
        if path == "/api/client/download":
            core = os.path.join(HERE, "vsx_core_new.bin")
            if os.path.exists(core):
                self._send(200, open(core, "rb").read(), "application/octet-stream")
            else:
                self._send(404, b"no core", "text/plain")
            return
        if path in GHOST_OFFSET_PATHS:
            self._send(200, ghost_offsets(self.headers.get("X-Session-Token") or ""),
                       "application/json")
            return
        if not is_panel_path(path):
            # Any non-panel GET = protocol probe / health check.
            self._send(200, encrypt_response({"status": False, "message": "No data provided"}),
                       "text/plain")
            return
        path = norm_panel(path)
        if path in ("/panel/vsp3log", "/panel/vsp3log.json"):
            if not self._authed():
                self._send(403, b"login first", "text/plain")
                return
            entries = _vsp3_debug_entries(50)
            if path.endswith(".json"):
                self._send(200, json.dumps(entries, ensure_ascii=False).encode(),
                           "application/json")
            else:
                blocks = ""
                for e in entries:
                    disp = dict(e)
                    for k in ("headers", "inner_json", "reply"):
                        try:
                            disp[k] = json.loads(disp.get(k) or "")
                        except Exception:
                            pass
                    blocks += (f"<h3>#{e['id']} {html.escape(e['ts'] or '')} — "
                               f"{html.escape(e['path'] or '')} — "
                               f"{html.escape(e['routing'] or '')} — "
                               f"HTTP {e['http_code']}</h3><pre>"
                               + html.escape(json.dumps(disp, indent=2,
                                                        ensure_ascii=False))
                               + "</pre>")
                self._send(200, page("VSP3 debug log",
                                     blocks or "<p>No entries yet.</p>"))
            return
        if not self._authed():
            self._send(200, page("Panel login",
                '<form method=post action="login">'
                '<input type=password name=pw placeholder="Panel password">'
                '<button>Login</button></form>'))
            return
        con = db()
        rows = con.execute("SELECT * FROM keys ORDER BY id DESC").fetchall()
        logs = con.execute("SELECT * FROM login_log ORDER BY id DESC LIMIT 30").fetchall()
        con.close()
        trs = "".join(
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td>"
            "<td>{}</td><td>{}</td></tr>".format(
                r["id"], html.escape(r["user_key"]), html.escape(r["serial"] or "-"),
                html.escape(r["expires"]), "BLOCKED" if r["blocked"] else "active",
                html.escape(r["seller"] or ""), html.escape(r["last_login"] or "-"))
            for r in rows)
        ltrs = "".join(
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>".format(
                html.escape(r["ts"]), html.escape(r["user_key"] or ""),
                html.escape(r["serial"] or ""), html.escape(r["result"] + " " + (r["detail"] or "")))
            for r in logs)
        con = db()
        grows = con.execute("SELECT * FROM ghost_keys ORDER BY id DESC").fetchall()
        con.close()
        gtrs = "".join(
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td>"
            "<td>{}</td><td>{}</td></tr>".format(
                r["id"], html.escape(r["user_key"]), html.escape(r["hwid"] or "-"),
                html.escape(r["expires"]), "BLOCKED" if r["blocked"] else "active",
                html.escape(r["seller"] or ""), html.escape(r["last_login"] or "-"))
            for r in grows)
        gtrs_table = ("<table><tr><th>ID</th><th>Key</th><th>HWID</th>"
                      "<th>Expires</th><th>State</th><th>Seller</th><th>Last login</th></tr>"
                      + gtrs + "</table>")
        con = db()
        glogs = con.execute("SELECT * FROM ghost_log ORDER BY id DESC LIMIT 30").fetchall()
        con.close()
        gltrs = "".join(
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>".format(
                html.escape(r["ts"]), html.escape(r["user_key"] or ""),
                html.escape(r["hwid"] or ""), html.escape(r["result"] + " " + (r["detail"] or "")))
            for r in glogs)
        body = (
            '<p><a href="vsp3log">VSP3 debug log</a> — what the core sent / what the panel answered</p>'
            '<form method=post action="create">'
            '<input name=user_key placeholder="Custom key (blank = random)">'
            '<input name=days type=number value=30 min=1> days '
            '<input name=seller placeholder="Seller">'
            '<input name=note placeholder="Note">'
            '<button>Create key</button></form>'
            '<form method=post action="action">'
            '<input name=key_id type=number placeholder="Key ID">'
            '<button name=act value=block>Block</button>'
            '<button name=act value=unblock>Unblock</button>'
            '<button name=act value=reset>Reset device</button>'
            '<button name=act value=extend>Extend +30 days</button>'
            '<button name=act value=delete>Delete</button></form>'
            f"<h3>Keys</h3><table><tr><th>ID</th><th>Key</th><th>Serial</th>"
            f"<th>Expires</th><th>State</th><th>Seller</th><th>Last login</th></tr>{trs}</table>"
            f"<h3>Recent logins</h3><table><tr><th>Time</th><th>Key</th><th>Serial</th>"
            f"<th>Result</th></tr>{ltrs}</table>"
            "<h3>Ghost Hack keys</h3>"
            '<form method=post action="gcreate">'
            '<input name=user_key placeholder="Custom key (blank = random)">'
            '<input name=days type=number value=30 min=1> days '
            '<input name=seller placeholder="Seller">'
            '<input name=note placeholder="Note">'
            '<button>Create Ghost key</button></form>'
            '<form method=post action="gaction">'
            '<input name=gkey_id type=number placeholder="Ghost key ID">'
            '<button name=act value=block>Block</button>'
            '<button name=act value=unblock>Unblock</button>'
            '<button name=act value=reset>Reset device</button>'
            '<button name=act value=extend>Extend +30 days</button>'
            '<button name=act value=delete>Delete</button></form>'
            + gtrs_table
            + f"<h3>Ghost recent attempts</h3><table><tr><th>Time</th><th>Key</th><th>HWID</th>"
              f"<th>Result</th></tr>{gltrs}</table>")
        self._send(200, page("OrangeFox Panel", body))

    def do_POST(self):
        path = urlparse(self.path).path
        if path in GHOST_AUTH_PATHS:
            n = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(n) if n else b""
            # VSP3 debug capture (passive): one entry per auth POST.
            dbg = {"path": path,
                   "headers": {h: (self.headers.get(h) or "")
                               for h in _VSP3_DEBUG_HEADERS},
                   "raw_body": raw.decode("utf-8", "replace")[:8192],
                   "routing": "legacy", "inner": "", "reply": "",
                   "http_code": 200}
            salvaged = False
            try:
                payload = json.loads(raw.decode("utf-8", "replace"))
            except Exception:
                # Loader 1.3.0 Java side: valid object + fields appended
                # after the closing brace. Salvage the object, don't reject.
                payload = _salvage_json_object(raw)
                salvaged = payload is not None
            if salvaged:
                dbg["routing"] = "salvage"
            # VSP3 multiplexing on the same path, by body shape:
            if isinstance(payload, dict) and "cpk" in payload:
                dbg["routing"] = "stage2_envelope"
                s2dbg = {}
                code, obj = vsp_stage2(payload, raw, self.headers, s2dbg)
                if s2dbg.get("inner"):
                    dbg["inner"] = s2dbg["inner"][:8192]
                if "reply_payload" in s2dbg:
                    dbg["reply"] = json.dumps(s2dbg["reply_payload"],
                                              ensure_ascii=False)
                elif s2dbg.get("fail"):
                    dbg["reply"] = json.dumps({"error": s2dbg["fail"]})
                dbg["http_code"] = code
                _vsp3_debug_log(dbg)
                self._send(code, json.dumps(obj).encode(), "application/json")
                return
            if _is_v13_blob(payload):
                # Sibling core's bare fallback: the same V13 blob it seals
                # inside the envelope, sent unsealed. Unwrap to the real
                # fields and answer with the stage-1 wire reply.
                fields = _v13_unwrap(payload)
                if not salvaged:
                    dbg["routing"] = "stage1"
                if fields is not None:
                    dbg["inner"] = json.dumps(fields, ensure_ascii=False)[:8192]
                    code, obj = vsp_stage1(fields)
                else:
                    code, obj = 400, {"success": False, "error": "missing_key_or_hwid"}
                dbg["reply"] = json.dumps(obj, ensure_ascii=False)
                dbg["http_code"] = code
                _vsp3_debug_log(dbg)
                self._send(code, json.dumps(obj).encode(), "application/json")
                return
            if (isinstance(payload, dict) and not (_OLD_GHOST_MARKERS & set(payload))
                    and ("key" in payload or "hwid" in payload
                         or set(payload) <= _STAGE1_FIELDS)):
                if not salvaged:
                    dbg["routing"] = "stage1"
                code, obj = vsp_stage1(payload)
                dbg["reply"] = json.dumps(obj, ensure_ascii=False)
                dbg["http_code"] = code
                _vsp3_debug_log(dbg)
                self._send(code, json.dumps(obj).encode(), "application/json")
                return
            if (isinstance(payload, dict) and (_OLD_GHOST_MARKERS & set(payload))
                    and _body_sig_ok(self.headers, raw,
                                     hwid=str(payload.get("hwid") or ""))):
                # New-core plaintext fallback: it reuses the legacy field
                # names (apk_hash/device_info/lib_hash) but every request is
                # body-signed, and its reply parser expects the VSP stage-1
                # wire shape (proto/wire), not the legacy Ghost reply.
                # Route signed marker bodies to stage 1. Legacy clients
                # never sign, so their routing is unchanged.
                if not salvaged:
                    dbg["routing"] = "stage1"
                code, obj = vsp_stage1(payload)
                dbg["reply"] = json.dumps(obj, ensure_ascii=False)
                dbg["http_code"] = code
                _vsp3_debug_log(dbg)
                self._send(code, json.dumps(obj).encode(), "application/json")
                return
            obj = ghost_auth(payload)
            dbg["reply"] = json.dumps(obj, ensure_ascii=False)
            dbg["http_code"] = 200
            _vsp3_debug_log(dbg)
            self._send(200, json.dumps(obj).encode(), "application/json")
            return
        form = self._form()
        if not is_panel_path(path):
            # Client endpoint: ANY non-panel path works, so the patched URL
            # can use whatever path makes its total length fit.
            self._send(200, handle_connect(form), "text/plain")
            return
        path = norm_panel(path)
        if path == "/panel/login":
            if (form.get("pw") or [""])[0] == panel_password():
                tok = secrets.token_urlsafe(24)
                SESSIONS.add(tok)
                self._send(302, b"", extra={"Location": "./", "Set-Cookie": f"sess={tok}; Path=/"})
            else:
                self._send(403, page("Panel login", "Wrong password."))
            return
        if path in ("/panel/gcreate", "/panel/gaction"):
            if not self._authed():
                self._send(403, b"login first", "text/plain")
                return
            con = db()
            if path == "/panel/gcreate":
                key = (form.get("user_key") or [""])[0].strip() or \
                    "GH-" + secrets.token_hex(4).upper() + "-" + secrets.token_hex(4).upper()
                days = int((form.get("days") or ["30"])[0] or 30)
                exp = (datetime.now(timezone.utc).date() + timedelta(days=days)).isoformat()
                con.execute("INSERT OR IGNORE INTO ghost_keys(user_key,expires,seller,note,created) VALUES(?,?,?,?,?)",
                            (key, exp, (form.get("seller") or [""])[0],
                             (form.get("note") or [""])[0], now_iso()))
            else:
                kid = int((form.get("gkey_id") or ["0"])[0] or 0)
                act = (form.get("act") or [""])[0]
                if act == "block":
                    con.execute("UPDATE ghost_keys SET blocked=1 WHERE id=?", (kid,))
                elif act == "unblock":
                    con.execute("UPDATE ghost_keys SET blocked=0 WHERE id=?", (kid,))
                elif act == "reset":
                    con.execute("UPDATE ghost_keys SET hwid=NULL WHERE id=?", (kid,))
                elif act == "delete":
                    con.execute("DELETE FROM ghost_keys WHERE id=?", (kid,))
                elif act == "extend":
                    row = con.execute("SELECT expires FROM ghost_keys WHERE id=?", (kid,)).fetchone()
                    if row:
                        base = max(row["expires"], datetime.now(timezone.utc).date().isoformat())
                        new = (datetime.fromisoformat(base).date() + timedelta(days=30)).isoformat()
                        con.execute("UPDATE ghost_keys SET expires=? WHERE id=?", (new, kid))
            con.commit(); con.close()
            self._send(302, b"", extra={"Location": "./"})
            return
        if path in ("/panel/create", "/panel/action"):
            if not self._authed():
                self._send(403, b"login first", "text/plain")
                return
            con = db()
            if path == "/panel/create":
                key = (form.get("user_key") or [""])[0].strip() or \
                    "OF-" + secrets.token_hex(4).upper() + "-" + secrets.token_hex(4).upper()
                days = int((form.get("days") or ["30"])[0] or 30)
                exp = (datetime.now(timezone.utc).date() + timedelta(days=days)).isoformat()
                con.execute("INSERT OR IGNORE INTO keys(user_key,expires,seller,note,created) VALUES(?,?,?,?,?)",
                            (key, exp, (form.get("seller") or [""])[0],
                             (form.get("note") or [""])[0], now_iso()))
            else:
                kid = int((form.get("key_id") or ["0"])[0] or 0)
                act = (form.get("act") or [""])[0]
                if act == "block":
                    con.execute("UPDATE keys SET blocked=1 WHERE id=?", (kid,))
                elif act == "unblock":
                    con.execute("UPDATE keys SET blocked=0 WHERE id=?", (kid,))
                elif act == "reset":
                    con.execute("UPDATE keys SET serial=NULL WHERE id=?", (kid,))
                elif act == "delete":
                    con.execute("DELETE FROM keys WHERE id=?", (kid,))
                elif act == "extend":
                    row = con.execute("SELECT expires FROM keys WHERE id=?", (kid,)).fetchone()
                    if row:
                        base = max(row["expires"], datetime.now(timezone.utc).date().isoformat())
                        new = (datetime.fromisoformat(base).date() + timedelta(days=30)).isoformat()
                        con.execute("UPDATE keys SET expires=? WHERE id=?", (new, kid))
            con.commit(); con.close()
            self._send(302, b"", extra={"Location": "./"})
            return
        self._send(404, b"not found", "text/plain")

if __name__ == "__main__":
    panel_password()
    db().close()
    port = int(os.environ.get("PORT", "8080"))
    print(f"OrangeFox backend+panel on 0.0.0.0:{port}  (pg={USE_PG}, openssl={_HAVE_OPENSSL})",
          flush=True)
    ThreadingHTTPServer(("0.0.0.0", port), Handler).serve_forever()
