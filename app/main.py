import argparse
import getpass
import hashlib
import hmac
import io
import json
import os
import re
import secrets
import sqlite3
import uuid
from datetime import date, datetime, timedelta
from html import escape
from statistics import mean, median, pstdev
from typing import List, Optional, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, unquote, urlencode, urljoin, urlparse
from urllib.request import urlopen
from xml.etree import ElementTree

import pdfplumber
from bs4 import BeautifulSoup
from fastapi import FastAPI, File, Form, Request, UploadFile
from fastapi.responses import HTMLResponse, RedirectResponse, Response
from starlette.middleware.base import BaseHTTPMiddleware
from fastapi.staticfiles import StaticFiles
from jinja2 import Environment, FileSystemLoader, select_autoescape
from markupsafe import Markup
from starlette.middleware.sessions import SessionMiddleware

APP_TITLE = os.getenv("SKATESTATS_TITLE", "SkateStats")
DB_PATH = os.getenv("SKATESTATS_DB", "/data/skatestats.sqlite")
OWNER_NAME = os.getenv("SKATESTATS_OWNER_NAME", "Remco Land").strip() or "Remco Land"
ADMIN_USERNAME = os.getenv("SKATESTATS_ADMIN_USERNAME", "admin").strip() or "admin"
SESSION_SECRET = os.getenv("SKATESTATS_SESSION_SECRET", "").strip() or "change-me-in-env"
PASSWORD_HASH_ITERATIONS = 600_000
SSR_API_BASE = "https://speedskatingresults.com/api/json"
SSR_XML_API_BASE = "https://speedskatingresults.com/api/xml"
SSR_DISTANCES = (100, 300, 500, 1000, 1500, 3000, 5000, 10000)
OSTA_BASE = "https://www.osta.nl/"
URL_LINE_RE = re.compile(r"^(.*?)(https?://\S+)\s*$")
SOURCE_NOTE_RE = re.compile(r"^(Geïmporteerd van|Geimporteerd van|Rondetijden van)\s+(.+?):\s*(https?://\S+)\s*$")
OSTA_VENUE_MAP = {
    "AK": "Alkmaar (NED)",
    "AM": "Amsterdam (NED)",
    "AS": "Assen (NED)",
    "BR": "Breda (NED)",
    "DN": "Dronten (NED)",
    "DV": "Deventer (NED)",
    "EN": "Enschede (NED)",
    "EV": "Eindhoven (NED)",
    "GR": "Groningen (NED)",
    "HA": "Haarlem (NED)",
    "HV": "Heerenveen (NED)",
    "HR": "Herentals (BEL)",
    "LE": "Leeuwarden (NED)",
    "NI": "Nijmegen (NED)",
    "TB": "Tilburg (NED)",
    "UT": "Utrecht (NED)",
}


def norm_name(s: str) -> str:
    s = s.strip().lower()
    s = re.sub(r"\s+", " ", s)
    return s


MONTHS_NL = {
    "januari": 1,
    "februari": 2,
    "maart": 3,
    "april": 4,
    "mei": 5,
    "juni": 6,
    "juli": 7,
    "augustus": 8,
    "september": 9,
    "oktober": 10,
    "november": 11,
    "december": 12,
}


def parse_date_any(s: str) -> str:
    """
    Accepts:
      - YYYY-MM-DD (from <input type="date">)
      - DD-MM-YYYY
      - DD/MM/YYYY
      - '29 november 2025' (NL)
    Returns: YYYY-MM-DD
    """
    s = (s or "").strip()
    if not s:
        raise ValueError("empty date")

    # YYYY-MM-DD
    try:
        datetime.strptime(s, "%Y-%m-%d")
        return s
    except ValueError:
        pass

    # DD-MM-YYYY
    try:
        d = datetime.strptime(s, "%d-%m-%Y")
        return d.strftime("%Y-%m-%d")
    except ValueError:
        pass

    # DD/MM/YYYY
    try:
        d = datetime.strptime(s, "%d/%m/%Y")
        return d.strftime("%Y-%m-%d")
    except ValueError:
        pass

    # '29 november 2025'
    m = re.match(r"^(\d{1,2})\s+([A-Za-zÀ-ÿ]+)\s+(\d{4})$", s, re.IGNORECASE)
    if m:
        day = int(m.group(1))
        mon_name = m.group(2).lower()
        year = int(m.group(3))
        mon = MONTHS_NL.get(mon_name)
        if mon:
            return datetime(year, mon, day).strftime("%Y-%m-%d")

    raise ValueError(f"invalid date: {s}")


def extract_date_from_text(s: str) -> Optional[str]:
    s = (s or "").strip()
    if not s:
        return None

    candidates = [s]
    candidates.extend(re.findall(r"\d{4}-\d{2}-\d{2}", s))
    candidates.extend(re.findall(r"\d{1,2}-\d{1,2}-\d{4}", s))
    candidates.extend(re.findall(r"\d{1,2}\s+[A-Za-zÀ-ÿ]+\s+\d{4}", s, re.IGNORECASE))

    for candidate in candidates:
        try:
            return parse_date_any(candidate)
        except ValueError:
            continue

    return None


def clean_competition_name(s: str) -> str:
    s = (s or "").strip()
    if not s:
        return s

    s = re.sub(r"\buitslag\b", "", s, flags=re.IGNORECASE)
    s = re.sub(r"\d{4}-\d{2}-\d{2}", "", s)
    s = re.sub(r"\d{1,2}-\d{1,2}-\d{4}", "", s)
    s = re.sub(r"\d{1,2}\s+[A-Za-zÀ-ÿ]+\s+\d{4}", "", s, flags=re.IGNORECASE)
    s = re.sub(r"\s+-\s+", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip(" -")


def fmt_date_ymd_to_dmy(ymd: str | None) -> str:
    if not ymd:
        return "-"
    try:
        d = datetime.strptime(ymd, "%Y-%m-%d")
        return d.strftime("%d-%m-%Y")
    except ValueError:
        return ymd


def current_season_bounds(today: date | None = None) -> Tuple[str, str]:
    today = today or datetime.now().date()
    if today.month >= 9:
        start_year = today.year
        end_year = today.year + 1
    elif today.month <= 4:
        start_year = today.year - 1
        end_year = today.year
    else:
        start_year = today.year - 1
        end_year = today.year
    return f"{start_year}-09-01", f"{end_year}-04-30"


def season_label_for_date(ymd: str) -> str:
    dt = datetime.strptime(ymd, "%Y-%m-%d").date()
    start_year = dt.year if dt.month >= 9 else dt.year - 1
    return f"{start_year}-{start_year + 1}"


def season_bounds_from_label(label: str) -> Tuple[str, str]:
    match = re.match(r"^(\d{4})-(\d{4})$", (label or "").strip())
    if not match:
        raise ValueError(f"invalid season label: {label}")
    start_year = int(match.group(1))
    end_year = int(match.group(2))
    if end_year != start_year + 1:
        raise ValueError(f"invalid season label: {label}")
    return f"{start_year}-09-01", f"{end_year}-04-30"


app = FastAPI(title=APP_TITLE)

BASE_DIR = os.path.dirname(__file__)
templates_env = Environment(
    loader=FileSystemLoader(os.path.join(BASE_DIR, "templates")),
    autoescape=select_autoescape(["html", "xml"]),
)

app.mount("/static", StaticFiles(directory=os.path.join(BASE_DIR, "static")), name="static")


def db() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.execute("PRAGMA foreign_keys = ON")
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    with db() as conn:
        conn.executescript(
            """
            PRAGMA foreign_keys = ON;

            CREATE TABLE IF NOT EXISTS competition (
              id INTEGER PRIMARY KEY AUTOINCREMENT,
              name TEXT NOT NULL,
              venue TEXT,
              competition_date TEXT NOT NULL, -- YYYY-MM-DD
              notes TEXT,
              created_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS skater (
              id INTEGER PRIMARY KEY AUTOINCREMENT,
              name TEXT NOT NULL UNIQUE
            );

            CREATE TABLE IF NOT EXISTS user (
              id INTEGER PRIMARY KEY AUTOINCREMENT,
              username TEXT NOT NULL UNIQUE,
              password_hash TEXT NOT NULL,
              skater_id INTEGER NOT NULL UNIQUE,
              is_admin INTEGER NOT NULL DEFAULT 0,
              theme_preference TEXT NOT NULL DEFAULT 'dark',
              created_at TEXT NOT NULL,
              updated_at TEXT NOT NULL,
              last_login_at TEXT,
              FOREIGN KEY (skater_id) REFERENCES skater(id) ON DELETE RESTRICT
            );

            CREATE TABLE IF NOT EXISTS race (
              id INTEGER PRIMARY KEY AUTOINCREMENT,
              competition_id INTEGER NOT NULL,
              skater_id INTEGER NOT NULL,
              distance_m INTEGER NOT NULL,
              category TEXT,
              class_name TEXT,
              lane TEXT,
              opponent TEXT,
              total_time_ms INTEGER,
              laps_csv TEXT,   -- "30.12,31.00,31.50"
              dnf INTEGER NOT NULL DEFAULT 0,
              notes TEXT,
              created_at TEXT NOT NULL,
              FOREIGN KEY (competition_id) REFERENCES competition(id) ON DELETE CASCADE,
              FOREIGN KEY (skater_id) REFERENCES skater(id) ON DELETE RESTRICT
            );

            CREATE TABLE IF NOT EXISTS goal_target (
              id INTEGER PRIMARY KEY AUTOINCREMENT,
              user_id INTEGER NOT NULL,
              distance_m INTEGER NOT NULL,
              target_time_ms INTEGER,
              target_opening_ms INTEGER,
              target_avg_400_ms INTEGER,
              target_last_400_ms INTEGER,
              target_fade_400_ms INTEGER,
              notes TEXT,
              created_at TEXT NOT NULL,
              updated_at TEXT NOT NULL,
              FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE,
              UNIQUE(user_id, distance_m)
            );

            CREATE TABLE IF NOT EXISTS osta_monitor_config (
              user_id INTEGER PRIMARY KEY,
              search_name TEXT NOT NULL,
              pid TEXT NOT NULL DEFAULT '',
              season TEXT NOT NULL,
              updated_at TEXT NOT NULL,
              FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS osta_import_blacklist (
              id INTEGER PRIMARY KEY AUTOINCREMENT,
              user_id INTEGER NOT NULL,
              comp_signature TEXT NOT NULL,
              comp_name TEXT NOT NULL,
              comp_date TEXT NOT NULL,
              pid TEXT,
              race_count INTEGER NOT NULL DEFAULT 0,
              created_at TEXT NOT NULL,
              FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE,
              UNIQUE(user_id, comp_signature)
            );

            CREATE TABLE IF NOT EXISTS import_preview_batch (
              id TEXT PRIMARY KEY,
              user_id INTEGER NOT NULL,
              source TEXT NOT NULL,
              payload_json TEXT NOT NULL,
              created_at TEXT NOT NULL,
              FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE
            );

            CREATE INDEX IF NOT EXISTS idx_race_competition ON race(competition_id);
            CREATE INDEX IF NOT EXISTS idx_race_skater ON race(skater_id);
            CREATE INDEX IF NOT EXISTS idx_race_distance ON race(distance_m);
            CREATE INDEX IF NOT EXISTS idx_goal_target_user_distance ON goal_target(user_id, distance_m);
            CREATE INDEX IF NOT EXISTS idx_osta_blacklist_user ON osta_import_blacklist(user_id);
            CREATE INDEX IF NOT EXISTS idx_import_preview_user ON import_preview_batch(user_id);
            """
        )
        migrate_db(conn)


def migrate_db(conn: sqlite3.Connection) -> None:
    competition_columns = {row["name"] for row in conn.execute("PRAGMA table_info(competition)").fetchall()}
    if "owner_user_id" not in competition_columns:
        conn.execute("ALTER TABLE competition ADD COLUMN owner_user_id INTEGER")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_competition_owner_user ON competition(owner_user_id)")

    user_columns = {row["name"] for row in conn.execute("PRAGMA table_info(user)").fetchall()}
    if user_columns and "theme_preference" not in user_columns:
        conn.execute("ALTER TABLE user ADD COLUMN theme_preference TEXT NOT NULL DEFAULT 'dark'")

    goal_columns = {row["name"] for row in conn.execute("PRAGMA table_info(goal_target)").fetchall()}
    if goal_columns and "notes" not in goal_columns:
        conn.execute("ALTER TABLE goal_target ADD COLUMN notes TEXT")

    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS osta_monitor_config (
          user_id INTEGER PRIMARY KEY,
          search_name TEXT NOT NULL,
          pid TEXT NOT NULL DEFAULT '',
          season TEXT NOT NULL,
          updated_at TEXT NOT NULL,
          FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS osta_import_blacklist (
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          user_id INTEGER NOT NULL,
          comp_signature TEXT NOT NULL,
          comp_name TEXT NOT NULL,
          comp_date TEXT NOT NULL,
          pid TEXT,
          race_count INTEGER NOT NULL DEFAULT 0,
          created_at TEXT NOT NULL,
          FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE,
          UNIQUE(user_id, comp_signature)
        );

        CREATE INDEX IF NOT EXISTS idx_osta_blacklist_user ON osta_import_blacklist(user_id);

        CREATE TABLE IF NOT EXISTS import_preview_batch (
          id TEXT PRIMARY KEY,
          user_id INTEGER NOT NULL,
          source TEXT NOT NULL,
          payload_json TEXT NOT NULL,
          created_at TEXT NOT NULL,
          FOREIGN KEY (user_id) REFERENCES user(id) ON DELETE CASCADE
        );

        CREATE INDEX IF NOT EXISTS idx_import_preview_user ON import_preview_batch(user_id);
        """
    )


def now_iso() -> str:
    return datetime.utcnow().isoformat()


def hash_password(password: str) -> str:
    if not password:
        raise ValueError("password cannot be empty")
    salt = secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, PASSWORD_HASH_ITERATIONS)
    return f"pbkdf2_sha256${PASSWORD_HASH_ITERATIONS}${salt.hex()}${digest.hex()}"


def verify_password(password: str, password_hash: str) -> bool:
    try:
        algorithm, iterations_raw, salt_hex, digest_hex = password_hash.split("$", 3)
    except ValueError:
        return False
    if algorithm != "pbkdf2_sha256":
        return False
    try:
        iterations = int(iterations_raw)
        salt = bytes.fromhex(salt_hex)
        expected = bytes.fromhex(digest_hex)
    except ValueError:
        return False
    actual = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, iterations)
    return hmac.compare_digest(actual, expected)


def get_or_create_skater(conn: sqlite3.Connection, skater_name: str) -> int:
    conn.execute("INSERT OR IGNORE INTO skater(name) VALUES(?)", (skater_name,))
    row = conn.execute("SELECT id FROM skater WHERE name = ?", (skater_name,)).fetchone()
    return int(row["id"])


def bootstrap_admin_user() -> None:
    with db() as conn:
        skater_id = get_or_create_skater(conn, OWNER_NAME)
        timestamp = now_iso()
        existing = conn.execute(
            """
            SELECT id, skater_id
            FROM user
            WHERE username = ?
            """,
            (ADMIN_USERNAME,),
        ).fetchone()
        if existing:
            if int(existing["skater_id"]) != skater_id:
                conn.execute(
                    """
                    UPDATE user
                    SET skater_id = ?, is_admin = 1, updated_at = ?
                    WHERE id = ?
                    """,
                    (skater_id, timestamp, int(existing["id"])),
                )
            else:
                conn.execute(
                    "UPDATE user SET is_admin = 1, updated_at = ? WHERE id = ?",
                    (timestamp, int(existing["id"])),
                )
            admin_user_id = int(existing["id"])
        else:
            cur = conn.execute(
                """
                INSERT INTO user(username, password_hash, skater_id, is_admin, created_at, updated_at)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    ADMIN_USERNAME,
                    "",
                    skater_id,
                    1,
                    timestamp,
                    timestamp,
                ),
            )
            admin_user_id = int(cur.lastrowid)

        conn.execute(
            """
            UPDATE competition
            SET owner_user_id = ?
            WHERE owner_user_id IS NULL
            """,
            (admin_user_id,),
        )


def get_user_by_id(conn: sqlite3.Connection, user_id: int) -> Optional[sqlite3.Row]:
    return conn.execute(
        """
        SELECT u.*, s.name AS skater_name
        FROM user u
        JOIN skater s ON s.id = u.skater_id
        WHERE u.id = ?
        """,
        (user_id,),
    ).fetchone()


def get_user_by_username(conn: sqlite3.Connection, username: str) -> Optional[sqlite3.Row]:
    return conn.execute(
        """
        SELECT u.*, s.name AS skater_name
        FROM user u
        JOIN skater s ON s.id = u.skater_id
        WHERE LOWER(u.username) = LOWER(?)
        """,
        (username,),
    ).fetchone()


def set_user_password(conn: sqlite3.Connection, user_id: int, new_password: str) -> None:
    conn.execute(
        "UPDATE user SET password_hash = ?, updated_at = ? WHERE id = ?",
        (hash_password(new_password), now_iso(), user_id),
    )


def normalize_theme_preference(raw_value: str) -> str:
    value = (raw_value or "").strip().lower()
    if value == "light":
        return "light"
    if value == "system":
        return "system"
    return "dark"


def resolved_theme(theme_preference: str) -> str:
    return "dark" if normalize_theme_preference(theme_preference) == "system" else normalize_theme_preference(theme_preference)


def update_user_profile(
    conn: sqlite3.Connection,
    user_id: int,
    username: str,
    skater_name: str,
    theme_preference: str,
) -> tuple[bool, str]:
    username_value = username.strip()
    skater_name_value = skater_name.strip()
    theme_value = normalize_theme_preference(theme_preference)

    if not username_value or not skater_name_value:
        return False, "required"

    current_user = get_user_by_id(conn, user_id)
    if not current_user:
        return False, "missing"

    existing_user = get_user_by_username(conn, username_value)
    if existing_user and int(existing_user["id"]) != user_id:
        return False, "username"

    existing_skater = conn.execute("SELECT id FROM skater WHERE name = ?", (skater_name_value,)).fetchone()
    if existing_skater and int(existing_skater["id"]) != int(current_user["skater_id"]):
        return False, "skater"

    conn.execute(
        """
        UPDATE user
        SET username = ?, theme_preference = ?, updated_at = ?
        WHERE id = ?
        """,
        (username_value, theme_value, now_iso(), user_id),
    )
    conn.execute(
        "UPDATE skater SET name = ? WHERE id = ?",
        (skater_name_value, int(current_user["skater_id"])),
    )
    return True, "profile"


def delete_user_account(conn: sqlite3.Connection, user_id: int) -> tuple[bool, str]:
    current_user = get_user_by_id(conn, user_id)
    if not current_user:
        return False, "missing"

    conn.execute("DELETE FROM goal_target WHERE user_id = ?", (user_id,))
    conn.execute("DELETE FROM competition WHERE owner_user_id = ?", (user_id,))
    conn.execute("DELETE FROM user WHERE id = ?", (user_id,))

    skater_row = conn.execute(
        """
        SELECT s.id
        FROM skater s
        LEFT JOIN user u ON u.skater_id = s.id
        LEFT JOIN race r ON r.skater_id = s.id
        WHERE s.id = ?
        GROUP BY s.id
        HAVING COUNT(u.id) = 0 AND COUNT(r.id) = 0
        """,
        (int(current_user["skater_id"]),),
    ).fetchone()
    if skater_row:
        conn.execute("DELETE FROM skater WHERE id = ?", (int(skater_row["id"]),))

    return True, "deleted"


@app.on_event("startup")
def _startup():
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    init_db()
    bootstrap_admin_user()

def render(request: Request, template_name: str, **ctx) -> HTMLResponse:
    tpl = templates_env.get_template(template_name)
    current_user = getattr(request.state, "user", None)
    html = tpl.render(
        app_title=APP_TITLE,
        request=request,
        current_user=current_user,
        owner_name=current_user["skater_name"] if current_user else OWNER_NAME,
        theme_preference=normalize_theme_preference(current_user["theme_preference"]) if current_user else "dark",
        active_theme=resolved_theme(current_user["theme_preference"]) if current_user else "dark",
        **ctx,
    )
    return HTMLResponse(html)


PUBLIC_PATHS = {"/health", "/login"}
PUBLIC_PREFIXES = ("/static/",)


def request_target(request: Request) -> str:
    target = request.url.path
    if request.url.query:
        target = f"{target}?{request.url.query}"
    return target


def login_redirect(next_path: str = "/") -> RedirectResponse:
    return RedirectResponse(f"/login?next={quote(next_path, safe='/%?=&')}", status_code=303)


def require_user(request: Request) -> sqlite3.Row:
    current_user = getattr(request.state, "user", None)
    if current_user is None:
        raise RuntimeError("missing authenticated user")
    return current_user


def require_admin_user(request: Request) -> sqlite3.Row:
    current_user = require_user(request)
    if int(current_user["is_admin"]) != 1:
        raise PermissionError("admin required")
    return current_user


class AuthMiddleware(BaseHTTPMiddleware):
    async def dispatch(self, request: Request, call_next):
        request.state.user = None
        user_id = request.session.get("user_id")
        if user_id:
            with db() as conn:
                request.state.user = get_user_by_id(conn, int(user_id))
            if request.state.user is None:
                request.session.pop("user_id", None)

        if request.url.path not in PUBLIC_PATHS and not request.url.path.startswith(PUBLIC_PREFIXES):
            if request.state.user is None:
                return login_redirect(request_target(request))

        return await call_next(request)


@app.exception_handler(PermissionError)
async def permission_error_handler(request: Request, exc: PermissionError):
    return HTMLResponse("Forbidden", status_code=403)


app.add_middleware(AuthMiddleware)
app.add_middleware(SessionMiddleware, secret_key=SESSION_SECRET, same_site="lax")


def parse_laps_to_ms(laps_str: str) -> Tuple[List[int], Optional[int], Optional[str]]:
    """
    Input: "30.12,31.00,31.50" or tab/newline/space separated seconds per split
    Output: list of split times in ms, total in ms, error message if any
    """
    if not laps_str.strip():
        return [], None, None

    raw = laps_str.replace(";", ",").replace("\t", ",").replace("\r", ",").replace("\n", ",")
    parts = [p.strip() for p in re.split(r"[\s,]+", raw) if p.strip()]
    laps_ms: List[int] = []
    for p in parts:
        try:
            sec = float(p)
            if sec <= 0:
                return [], None, f"Ongeldige rondetijd: {p}"
            laps_ms.append(int(round(sec * 1000)))
        except ValueError:
            return [], None, f"Kon rondetijd niet lezen: {p}"

    total_ms = sum(laps_ms) if laps_ms else None
    return laps_ms, total_ms, None


def fmt_ms(ms: Optional[int]) -> str:
    if ms is None:
        return "-"
    sign = "-" if ms < 0 else ""
    total_seconds = abs(ms) / 1000.0
    minutes = int(total_seconds // 60)
    seconds = total_seconds - (minutes * 60)
    if minutes > 0:
        return f"{sign}{minutes}:{seconds:05.2f}"
    return f"{sign}{seconds:.2f}"


def build_sparkline(
    rows: List[sqlite3.Row],
    range_start: Optional[str] = None,
    range_end: Optional[str] = None,
    width: int = 320,
    height: int = 132,
) -> Optional[dict]:
    month_labels = {
        1: "jan",
        2: "feb",
        3: "mrt",
        4: "apr",
        5: "mei",
        6: "jun",
        7: "jul",
        8: "aug",
        9: "sep",
        10: "okt",
        11: "nov",
        12: "dec",
    }
    valid_rows = [row for row in rows if row["total_time_ms"] is not None]
    values = [row["total_time_ms"] for row in valid_rows]
    if not values:
        return None

    left_padding = 8
    right_padding = 8
    top_padding = 12
    bottom_padding = 28
    plot_width = max(width - left_padding - right_padding, 20)
    plot_height = max(height - top_padding - bottom_padding, 20)

    min_v = min(values)
    max_v = max(values)
    span = max(max_v - min_v, 1)

    data_start = datetime.strptime(valid_rows[0]["competition_date"], "%Y-%m-%d").date()
    data_end = datetime.strptime(valid_rows[-1]["competition_date"], "%Y-%m-%d").date()
    start_date = data_start
    end_date = data_end
    if end_date < start_date:
        start_date, end_date = end_date, start_date
    if start_date == end_date:
        start_date = start_date.replace(day=1)
        if end_date.month == 12:
            end_date = end_date.replace(year=end_date.year + 1, month=1, day=1)
        else:
            end_date = end_date.replace(month=end_date.month + 1, day=1)
        end_date = end_date - timedelta(days=1)

    day_span = max((end_date - start_date).days, 1)

    points = []
    circles = []
    month_ticks = []
    min_tick_spacing_px = 28
    last_tick_x: Optional[float] = None
    seen_months: set[tuple[int, int]] = set()
    for row in valid_rows:
        race_date = datetime.strptime(row["competition_date"], "%Y-%m-%d").date()
        month_key = (race_date.year, race_date.month)
        if month_key in seen_months:
            continue
        seen_months.add(month_key)
        tick_date = race_date.replace(day=1)
        tick_offset = min(max((tick_date - start_date).days, 0), day_span)
        x_ratio = tick_offset / day_span
        x = left_padding + (x_ratio * plot_width)
        if last_tick_x is not None and (x - last_tick_x) < min_tick_spacing_px:
            continue
        last_tick_x = x
        month_ticks.append({"x": f"{x:.1f}", "label": month_labels[race_date.month]})

    for row in valid_rows:
        value = row["total_time_ms"]
        race_date = datetime.strptime(row["competition_date"], "%Y-%m-%d").date()
        x_ratio = (race_date - start_date).days / day_span if day_span else 0
        x = left_padding + (x_ratio * plot_width)
        y = top_padding + plot_height - (((value - min_v) / span) * plot_height)
        points.append(f"{x:.1f},{y:.1f}")
        circles.append(
            {
                "x": f"{x:.1f}",
                "y": f"{y:.1f}",
                "href": f"/races/{row['id']}",
                "tooltip_date": fmt_date_ymd_to_dmy(row["competition_date"]),
                "tooltip_name": row["competition_name"],
                "tooltip_time": fmt_ms(value),
                "tooltip_count": str(len(valid_rows)),
            }
        )

    return {
        "width": width,
        "height": height,
        "points": " ".join(points),
        "circles": circles,
        "month_ticks": month_ticks,
        "baseline_y": top_padding + plot_height,
        "left_padding": left_padding,
        "right_padding": right_padding,
        "min_ms": min_v,
        "max_ms": max_v,
        "delta_ms": values[-1] - values[0],
    }


def build_split_chart(laps: List[float], width: int = 520, height: int = 180) -> Optional[dict]:
    if not laps:
        return None

    top_padding = 18
    right_padding = 18
    bottom_padding = 30
    left_padding = 42
    plot_width = max(width - left_padding - right_padding, 10)
    plot_height = max(height - top_padding - bottom_padding, 10)

    min_v = min(laps)
    max_v = max(laps)
    span = max(max_v - min_v, 0.25)
    x_step = plot_width / max(len(laps) - 1, 1)

    points = []
    circles = []
    y_ticks = []

    for idx, value in enumerate(laps):
        x = left_padding + (idx * x_step if len(laps) > 1 else plot_width / 2)
        y = top_padding + plot_height - (((value - min_v) / span) * plot_height)
        points.append(f"{x:.1f},{y:.1f}")
        circles.append(
            {
                "x": f"{x:.1f}",
                "y": f"{y:.1f}",
                "label": str(idx + 1),
                "time": f"{value:.2f}",
            }
        )

    for idx in range(4):
        tick_value = min_v + ((span / 3) * idx)
        tick_y = top_padding + plot_height - (((tick_value - min_v) / span) * plot_height)
        y_ticks.append({"y": f"{tick_y:.1f}", "label": f"{tick_value:.2f}"})

    return {
        "width": width,
        "height": height,
        "points": " ".join(points),
        "circles": circles,
        "y_ticks": y_ticks,
        "baseline_y": top_padding + plot_height,
        "left_padding": left_padding,
        "right_padding": right_padding,
    }


def laps_from_csv(laps_csv: Optional[str]) -> List[float]:
    if not laps_csv:
        return []
    parts = [p.strip() for p in laps_csv.split(",") if p.strip()]
    out: List[float] = []
    for p in parts:
        try:
            out.append(float(p))
        except ValueError:
            pass
    return out


# -----------------------
# Split distance logic + metrics (opening is not always 400m)
# -----------------------

def opening_split_m(distance_m: int) -> int:
    """
    Typical long-track opening split distances:
    - 500m: 100m
    - 1500m: 300m
    - 100m: 100m
    - most others: 200m
    """
    if distance_m == 500:
        return 100
    if distance_m == 1500:
        return 300
    if distance_m == 100:
        return 100
    return 200


def segment_distances(distance_m: int, n_segments: int) -> List[int]:
    """
    Build segment lengths (meters) to match number of entered splits.
    First is opening split, rest assumed 400m-ish, last adjusted to fit.
    """
    if n_segments <= 0:
        return []

    first = min(opening_split_m(distance_m), distance_m)
    if n_segments == 1:
        return [distance_m]

    remaining_dist = max(distance_m - first, 0)
    remaining_segments = n_segments - 1

    segs = [first]
    if remaining_segments == 1:
        segs.append(remaining_dist)
        return segs

    default = 400
    for _ in range(remaining_segments - 1):
        segs.append(default)

    last = remaining_dist - default * (remaining_segments - 1)
    if last <= 0:
        # fallback: distribute evenly
        even = max(int(round(remaining_dist / remaining_segments)), 1)
        segs = [first] + [even] * remaining_segments
        segs[-1] += remaining_dist - even * remaining_segments
        return segs

    segs.append(last)
    return segs


def per400_times(laps: List[float], distance_m: int) -> List[float]:
    """Normalize each split to a 400m-equivalent time."""
    seg_m = segment_distances(distance_m, len(laps))
    out: List[float] = []
    for t, m in zip(laps, seg_m):
        if m <= 0:
            continue
        out.append(t * 400.0 / m)
    return out


def build_split_rows(laps: List[float], distance_m: int) -> List[dict]:
    segment_m = segment_distances(distance_m, len(laps))
    per_400 = per400_times(laps, distance_m)
    rows: List[dict] = []
    previous_400: Optional[float] = None

    for idx, lap in enumerate(laps):
        normalized = per_400[idx] if idx < len(per_400) else None
        delta_prev = None
        if normalized is not None and previous_400 is not None:
            delta_prev = normalized - previous_400
        rows.append(
            {
                "index": idx + 1,
                "distance_m": segment_m[idx] if idx < len(segment_m) else None,
                "seconds": lap,
                "per_400eq": normalized,
                "delta_prev_400eq": delta_prev,
            }
        )
        if normalized is not None:
            previous_400 = normalized

    return rows


def compute_race_metrics(laps: List[float], distance_m: int) -> dict:
    """Metrics based on 400m-equivalent splits (fair across 500m/1500m openings)."""
    if not laps:
        return {
            "segment_count": 0,
            "opening_m": opening_split_m(distance_m),
            "avg_400": None,
            "first_400eq": None,
            "last_400eq": None,
            "fade_400eq": None,
            "avg_fade_per_segment_400eq": None,
        }

    p400 = per400_times(laps, distance_m)
    if not p400:
        return {
            "segment_count": len(laps),
            "opening_m": opening_split_m(distance_m),
            "avg_400": None,
            "first_400eq": None,
            "last_400eq": None,
            "fade_400eq": None,
            "avg_fade_per_segment_400eq": None,
        }

    avg_400 = sum(p400) / len(p400)
    first = p400[0]
    last = p400[-1]
    fade = last - first
    avg_fade_per_segment = fade / (len(p400) - 1) if len(p400) > 1 else 0.0

    return {
        "segment_count": len(laps),
        "opening_m": opening_split_m(distance_m),
        "avg_400": avg_400,
        "first_400eq": first,
        "last_400eq": last,
        "fade_400eq": fade,
        "avg_fade_per_segment_400eq": avg_fade_per_segment,
    }


def fmt_sec(value: Optional[float]) -> str:
    if value is None:
        return "-"
    return fmt_ms(int(round(value * 1000)))


def parse_optional_time_to_ms(raw_value: str) -> Optional[int]:
    value = (raw_value or "").strip()
    if not value:
        return None
    return parse_time_to_ms(value)


def get_goal_targets(conn: sqlite3.Connection, user_id: int) -> list[sqlite3.Row]:
    return conn.execute(
        """
        SELECT *
        FROM goal_target
        WHERE user_id = ?
        ORDER BY distance_m ASC
        """,
        (user_id,),
    ).fetchall()


def get_goal_target_map(conn: sqlite3.Connection, user_id: int) -> dict[int, sqlite3.Row]:
    return {int(row["distance_m"]): row for row in get_goal_targets(conn, user_id)}


def upsert_goal_target(
    conn: sqlite3.Connection,
    user_id: int,
    distance_m: int,
    target_time_ms: Optional[int],
    target_opening_ms: Optional[int],
    target_avg_400_ms: Optional[int],
    target_last_400_ms: Optional[int],
    target_fade_400_ms: Optional[int],
    notes: str,
) -> None:
    timestamp = now_iso()
    conn.execute(
        """
        INSERT INTO goal_target(
          user_id,
          distance_m,
          target_time_ms,
          target_opening_ms,
          target_avg_400_ms,
          target_last_400_ms,
          target_fade_400_ms,
          notes,
          created_at,
          updated_at
        )
        VALUES(?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(user_id, distance_m) DO UPDATE SET
          target_time_ms = excluded.target_time_ms,
          target_opening_ms = excluded.target_opening_ms,
          target_avg_400_ms = excluded.target_avg_400_ms,
          target_last_400_ms = excluded.target_last_400_ms,
          target_fade_400_ms = excluded.target_fade_400_ms,
          notes = excluded.notes,
          updated_at = excluded.updated_at
        """,
        (
            user_id,
            distance_m,
            target_time_ms,
            target_opening_ms,
            target_avg_400_ms,
            target_last_400_ms,
            target_fade_400_ms,
            notes.strip() or None,
            timestamp,
            timestamp,
        ),
    )


def delete_goal_target(conn: sqlite3.Connection, user_id: int, distance_m: int) -> None:
    conn.execute(
        "DELETE FROM goal_target WHERE user_id = ? AND distance_m = ?",
        (user_id, distance_m),
    )


def build_goal_progress(goal_row: Optional[sqlite3.Row], stat: dict) -> list[dict]:
    if goal_row is None:
        return []

    comparisons = [
        ("Doeltijd", goal_row["target_time_ms"], stat.get("best_time_ms")),
        ("Opening", goal_row["target_opening_ms"], round(stat["best_opening_s"] * 1000) if stat.get("best_opening_s") is not None else None),
        ("Gem. 400-eq", goal_row["target_avg_400_ms"], round(stat["avg_400_s"] * 1000) if stat.get("avg_400_s") is not None else None),
        ("Laatste 400-eq", goal_row["target_last_400_ms"], round(stat["best_last_400_s"] * 1000) if stat.get("best_last_400_s") is not None else None),
        ("Verval", goal_row["target_fade_400_ms"], round(stat["avg_fade_s"] * 1000) if stat.get("avg_fade_s") is not None else None),
    ]

    progress: list[dict] = []
    for label, target_ms, actual_ms in comparisons:
        if target_ms is None:
            continue
        delta_ms = None if actual_ms is None else int(actual_ms) - int(target_ms)
        progress.append(
            {
                "label": label,
                "target_ms": target_ms,
                "actual_ms": actual_ms,
                "delta_ms": delta_ms,
                "met_goal": delta_ms is not None and delta_ms <= 0,
            }
        )
    return progress


def format_delta(delta_ms: Optional[int]) -> str:
    if delta_ms is None:
        return "-"
    sign = "+" if delta_ms > 0 else ""
    return f"{sign}{fmt_ms(delta_ms)}"


def build_vergelijkings_samenvatting(
    total_delta_ms: Optional[int],
    opening_delta_ms: Optional[int],
    slot_delta_ms: Optional[int],
    verval_delta_ms: Optional[int],
    split_deltas_ms: List[int],
) -> str:
    if total_delta_ms is None:
        return "Onvoldoende data om een duidelijke vergelijking te maken."

    if split_deltas_ms:
        faster_count = len([value for value in split_deltas_ms if value < 0])
        faster_ratio = faster_count / len(split_deltas_ms)
    else:
        faster_ratio = 0.0

    if faster_ratio >= 0.75 and total_delta_ms <= -300:
        return "Sneller over vrijwel de hele rit."
    if opening_delta_ms is not None and verval_delta_ms is not None and opening_delta_ms <= -150 and verval_delta_ms >= 250:
        return "Snellere opening, maar veel verval in de slotfase."
    if opening_delta_ms is not None and slot_delta_ms is not None and opening_delta_ms >= 150 and slot_delta_ms <= -120:
        return "Rustigere start met een sterkere finish."
    if total_delta_ms <= -250:
        return "Vergelijkingsrit was overall sneller met stabielere opbouw."
    if total_delta_ms >= 250:
        return "Vergelijkingsrit verloor vooral tijd in meerdere segmenten."
    return "Kleine verschillen: het tempoverloop bepaalt hier het resultaat."


def get_pacing_labels(laps: List[float], distance_m: int) -> List[str]:
    if not laps:
        return []

    per_400 = per400_times(laps, distance_m)
    if not per_400:
        return []

    labels: List[str] = []
    first = per_400[0]
    last = per_400[-1]
    avg = sum(per_400) / len(per_400)
    fade = last - first

    if first <= avg - 0.30:
        labels.append("Snelle opening")
    elif first >= avg + 0.30:
        labels.append("Controleerde start")
    else:
        labels.append("Gelijkmatige opening")

    if last <= avg - 0.15:
        labels.append("Sterke slotronde")
    elif last >= avg + 0.25:
        labels.append("Zwakke slotronde")

    if fade >= 0.50:
        labels.append("Groot verval")
    elif fade <= 0.15:
        labels.append("Gelijkmatige opbouw")

    seen: set[str] = set()
    unique_labels: List[str] = []
    for label in labels:
        if label in seen:
            continue
        seen.add(label)
        unique_labels.append(label)
    return unique_labels


def get_sterkste_en_zwakste_onderdelen(split_rows: List[dict]) -> dict:
    valid_rows = [row for row in split_rows if row.get("split_delta_ms") is not None]
    if not valid_rows:
        return {"sterkste": None, "zwakste": None}

    sterkste = min(valid_rows, key=lambda row: int(row["split_delta_ms"]))
    zwakste = max(valid_rows, key=lambda row: int(row["split_delta_ms"]))
    return {"sterkste": sterkste, "zwakste": zwakste}


def build_split_delta_series(split_rows: List[dict], width: int = 620, height: int = 190) -> Optional[dict]:
    values: List[int] = []
    labels: List[str] = []
    for row in split_rows:
        delta_ms = row.get("split_delta_ms")
        if delta_ms is None:
            continue
        values.append(int(delta_ms))
        labels.append(str(row["index"]))

    if not values:
        return None

    top_padding = 18
    right_padding = 18
    bottom_padding = 30
    left_padding = 52
    plot_width = max(width - left_padding - right_padding, 10)
    plot_height = max(height - top_padding - bottom_padding, 10)

    min_v = min(min(values), 0)
    max_v = max(max(values), 0)
    span = max(max_v - min_v, 120)
    x_step = plot_width / max(len(values) - 1, 1)

    points: List[str] = []
    circles: List[dict] = []
    y_ticks: List[dict] = []
    x_ticks: List[dict] = []

    for idx, value in enumerate(values):
        x = left_padding + (idx * x_step if len(values) > 1 else plot_width / 2)
        y = top_padding + plot_height - (((value - min_v) / span) * plot_height)
        points.append(f"{x:.1f},{y:.1f}")
        circles.append({"x": f"{x:.1f}", "y": f"{y:.1f}", "label": labels[idx], "value": format_delta(value)})
        x_ticks.append({"x": f"{x:.1f}", "label": labels[idx]})

    for idx in range(4):
        tick_value = min_v + ((span / 3) * idx)
        tick_y = top_padding + plot_height - (((tick_value - min_v) / span) * plot_height)
        y_ticks.append({"y": f"{tick_y:.1f}", "label": format_delta(int(round(tick_value)))})

    zero_y = top_padding + plot_height - (((0 - min_v) / span) * plot_height)
    return {
        "width": width,
        "height": height,
        "points": " ".join(points),
        "circles": circles,
        "x_ticks": x_ticks,
        "y_ticks": y_ticks,
        "left_padding": left_padding,
        "right_padding": right_padding,
        "baseline_y": top_padding + plot_height,
        "zero_y": f"{zero_y:.1f}",
    }


def build_cumulative_delta_series(split_rows: List[dict], width: int = 620, height: int = 210) -> Optional[dict]:
    values: List[int] = []
    labels: List[str] = []
    running = 0
    for row in split_rows:
        delta_ms = row.get("split_delta_ms")
        if delta_ms is None:
            continue
        running += int(delta_ms)
        values.append(running)
        labels.append(str(row["index"]))

    if not values:
        return None

    top_padding = 18
    right_padding = 18
    bottom_padding = 30
    left_padding = 52
    plot_width = max(width - left_padding - right_padding, 10)
    plot_height = max(height - top_padding - bottom_padding, 10)

    min_v = min(min(values), 0)
    max_v = max(max(values), 0)
    span = max(max_v - min_v, 120)
    x_step = plot_width / max(len(values) - 1, 1)

    points: List[str] = []
    circles: List[dict] = []
    y_ticks: List[dict] = []
    x_ticks: List[dict] = []

    for idx, value in enumerate(values):
        x = left_padding + (idx * x_step if len(values) > 1 else plot_width / 2)
        y = top_padding + plot_height - (((value - min_v) / span) * plot_height)
        points.append(f"{x:.1f},{y:.1f}")
        circles.append({"x": f"{x:.1f}", "y": f"{y:.1f}", "label": labels[idx], "value": format_delta(value)})
        x_ticks.append({"x": f"{x:.1f}", "label": labels[idx]})

    for idx in range(4):
        tick_value = min_v + ((span / 3) * idx)
        tick_y = top_padding + plot_height - (((tick_value - min_v) / span) * plot_height)
        y_ticks.append({"y": f"{tick_y:.1f}", "label": format_delta(int(round(tick_value)))})

    zero_y = top_padding + plot_height - (((0 - min_v) / span) * plot_height)
    return {
        "width": width,
        "height": height,
        "points": " ".join(points),
        "circles": circles,
        "x_ticks": x_ticks,
        "y_ticks": y_ticks,
        "left_padding": left_padding,
        "right_padding": right_padding,
        "baseline_y": top_padding + plot_height,
        "zero_y": f"{zero_y:.1f}",
    }


def build_lap_overlay_series(base_laps: List[float], compare_laps: List[float], width: int = 620, height: int = 240) -> Optional[dict]:
    if not base_laps and not compare_laps:
        return None

    max_len = max(len(base_laps), len(compare_laps))
    if max_len == 0:
        return None

    all_values = base_laps + compare_laps
    min_v = min(all_values)
    max_v = max(all_values)

    top_padding = 18
    right_padding = 18
    bottom_padding = 30
    left_padding = 42
    plot_width = max(width - left_padding - right_padding, 10)
    plot_height = max(height - top_padding - bottom_padding, 10)
    span = max(max_v - min_v, 0.25)
    x_step = plot_width / max(max_len - 1, 1)

    def map_series(laps: List[float]) -> tuple[str, List[dict]]:
        points: List[str] = []
        circles: List[dict] = []
        for idx, value in enumerate(laps):
            x = left_padding + (idx * x_step if max_len > 1 else plot_width / 2)
            y = top_padding + plot_height - (((value - min_v) / span) * plot_height)
            points.append(f"{x:.1f},{y:.1f}")
            circles.append({"x": f"{x:.1f}", "y": f"{y:.1f}", "label": str(idx + 1), "time": f"{value:.2f}"})
        return " ".join(points), circles

    base_points, base_circles = map_series(base_laps)
    compare_points, compare_circles = map_series(compare_laps)
    y_ticks: List[dict] = []
    x_ticks: List[dict] = []

    for idx in range(4):
        tick_value = min_v + ((span / 3) * idx)
        tick_y = top_padding + plot_height - (((tick_value - min_v) / span) * plot_height)
        y_ticks.append({"y": f"{tick_y:.1f}", "label": f"{tick_value:.2f}"})

    for idx in range(max_len):
        x = left_padding + (idx * x_step if max_len > 1 else plot_width / 2)
        x_ticks.append({"x": f"{x:.1f}", "label": str(idx + 1)})

    return {
        "width": width,
        "height": height,
        "left_padding": left_padding,
        "right_padding": right_padding,
        "baseline_y": top_padding + plot_height,
        "y_ticks": y_ticks,
        "x_ticks": x_ticks,
        "base_points": base_points,
        "base_circles": base_circles,
        "compare_points": compare_points,
        "compare_circles": compare_circles,
    }


def build_comparison_context(base_row: sqlite3.Row, compare_row: Optional[sqlite3.Row]) -> Optional[dict]:
    if compare_row is None:
        return None

    base_laps = laps_from_csv(base_row["laps_csv"])
    compare_laps = laps_from_csv(compare_row["laps_csv"])
    base_metrics = compute_race_metrics(base_laps, int(base_row["distance_m"]))
    compare_metrics = compute_race_metrics(compare_laps, int(compare_row["distance_m"]))
    base_per_400 = per400_times(base_laps, int(base_row["distance_m"]))
    compare_per_400 = per400_times(compare_laps, int(compare_row["distance_m"]))

    base_segments = segment_distances(int(base_row["distance_m"]), len(base_laps))
    compare_segments = segment_distances(int(compare_row["distance_m"]), len(compare_laps))
    split_comparison: list[dict] = []
    row_count = max(len(base_laps), len(compare_laps))
    cumulative_delta_ms = 0
    for idx in range(row_count):
        base_split = base_laps[idx] if idx < len(base_laps) else None
        compare_split = compare_laps[idx] if idx < len(compare_laps) else None
        base_400 = base_per_400[idx] if idx < len(base_per_400) else None
        compare_400 = compare_per_400[idx] if idx < len(compare_per_400) else None
        split_delta_ms = None if base_split is None or compare_split is None else int(round((compare_split - base_split) * 1000))
        eq_delta_ms = None if base_400 is None or compare_400 is None else int(round((compare_400 - base_400) * 1000))
        distance_m = base_segments[idx] if idx < len(base_segments) else (compare_segments[idx] if idx < len(compare_segments) else None)
        cumulative_delta_value = None
        if split_delta_ms is not None:
            cumulative_delta_ms += split_delta_ms
            cumulative_delta_value = cumulative_delta_ms
        split_comparison.append(
            {
                "index": idx + 1,
                "distance_m": distance_m,
                "base_split": base_split,
                "compare_split": compare_split,
                "split_delta_ms": split_delta_ms,
                "cumulative_delta_ms": cumulative_delta_value,
                "base_400": base_400,
                "compare_400": compare_400,
                "eq_delta_ms": eq_delta_ms,
            }
        )

    total_delta_ms = None
    if base_row["total_time_ms"] is not None and compare_row["total_time_ms"] is not None:
        total_delta_ms = int(compare_row["total_time_ms"]) - int(base_row["total_time_ms"])
    opening_delta_ms = None if not base_laps or not compare_laps else int(round((compare_laps[0] - base_laps[0]) * 1000))
    slot_delta_ms = None if not base_laps or not compare_laps else int(round((compare_laps[-1] - base_laps[-1]) * 1000))
    verval_delta_ms = None
    if base_metrics["fade_400eq"] is not None and compare_metrics["fade_400eq"] is not None:
        verval_delta_ms = int(round((compare_metrics["fade_400eq"] - base_metrics["fade_400eq"]) * 1000))

    summary_items = [
        ("Totale tijd", base_row["total_time_ms"], compare_row["total_time_ms"]),
        ("Opening", round(base_laps[0] * 1000) if base_laps else None, round(compare_laps[0] * 1000) if compare_laps else None),
        (
            "Laatste 400-eq",
            round(base_metrics["last_400eq"] * 1000) if base_metrics["last_400eq"] is not None else None,
            round(compare_metrics["last_400eq"] * 1000) if compare_metrics["last_400eq"] is not None else None,
        ),
        (
            "Verval",
            round(base_metrics["fade_400eq"] * 1000) if base_metrics["fade_400eq"] is not None else None,
            round(compare_metrics["fade_400eq"] * 1000) if compare_metrics["fade_400eq"] is not None else None,
        ),
    ]

    summary = []
    for label, base_value, compare_value in summary_items:
        summary.append(
            {
                "label": label,
                "base_ms": base_value,
                "compare_ms": compare_value,
                "delta_ms": None if base_value is None or compare_value is None else int(compare_value) - int(base_value),
            }
        )

    split_deltas_ms = [int(row["split_delta_ms"]) for row in split_comparison if row["split_delta_ms"] is not None]
    samenvatting_tekst = build_vergelijkings_samenvatting(
        total_delta_ms=total_delta_ms,
        opening_delta_ms=opening_delta_ms,
        slot_delta_ms=slot_delta_ms,
        verval_delta_ms=verval_delta_ms,
        split_deltas_ms=split_deltas_ms,
    )
    pacing_basis = get_pacing_labels(base_laps, int(base_row["distance_m"]))
    pacing_vergelijking = get_pacing_labels(compare_laps, int(compare_row["distance_m"]))
    onderdelen = get_sterkste_en_zwakste_onderdelen(split_comparison)

    return {
        "race": compare_row,
        "summary": summary,
        "splits": split_comparison,
        "highlights": {
            "total_delta_ms": total_delta_ms,
            "opening_delta_ms": opening_delta_ms,
            "slot_delta_ms": slot_delta_ms,
            "verval_delta_ms": verval_delta_ms,
        },
        "samenvatting_tekst": samenvatting_tekst,
        "delta_chart": build_split_delta_series(split_comparison),
        "cumulatieve_delta_chart": build_cumulative_delta_series(split_comparison),
        "lap_overlay_chart": build_lap_overlay_series(base_laps, compare_laps),
        "pacing": {
            "basis_labels": pacing_basis,
            "vergelijking_labels": pacing_vergelijking,
            "basis_opening_ms": round(base_laps[0] * 1000) if base_laps else None,
            "vergelijking_opening_ms": round(compare_laps[0] * 1000) if compare_laps else None,
            "basis_slot_ms": round(base_laps[-1] * 1000) if base_laps else None,
            "vergelijking_slot_ms": round(compare_laps[-1] * 1000) if compare_laps else None,
            "basis_verval_ms": round(base_metrics["fade_400eq"] * 1000) if base_metrics["fade_400eq"] is not None else None,
            "vergelijking_verval_ms": round(compare_metrics["fade_400eq"] * 1000) if compare_metrics["fade_400eq"] is not None else None,
        },
        "onderdelen": onderdelen,
    }


def export_user_data(conn: sqlite3.Connection, current_user: sqlite3.Row) -> dict:
    user_payload = {
        "id": int(current_user["id"]),
        "username": current_user["username"],
        "skater_name": current_user["skater_name"],
        "theme_preference": current_user["theme_preference"],
        "created_at": current_user["created_at"],
        "updated_at": current_user["updated_at"],
        "last_login_at": current_user["last_login_at"],
    }

    competitions = [
        dict(row)
        for row in conn.execute(
            """
            SELECT id, name, venue, competition_date, notes, created_at
            FROM competition
            WHERE owner_user_id = ?
            ORDER BY competition_date ASC, id ASC
            """,
            (int(current_user["id"]),),
        ).fetchall()
    ]
    races = [
        dict(row)
        for row in conn.execute(
            """
            SELECT r.*, c.name AS competition_name, c.venue, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()
    ]
    goals = [dict(row) for row in get_goal_targets(conn, int(current_user["id"]))]
    return {
        "exported_at": now_iso(),
        "user": user_payload,
        "goals": goals,
        "competitions": competitions,
        "races": races,
    }


def import_user_data(conn: sqlite3.Connection, current_user: sqlite3.Row, payload: dict) -> dict:
    if not isinstance(payload, dict):
        raise ValueError("Backupbestand heeft een ongeldig formaat.")

    competitions = payload.get("competitions")
    races = payload.get("races")
    goals = payload.get("goals", [])
    user_payload = payload.get("user", {})

    if not isinstance(competitions, list) or not isinstance(races, list) or not isinstance(goals, list):
        raise ValueError("Backup mist competities, ritten of doelen.")

    conn.execute("DELETE FROM goal_target WHERE user_id = ?", (int(current_user["id"]),))
    conn.execute("DELETE FROM competition WHERE owner_user_id = ?", (int(current_user["id"]),))

    if isinstance(user_payload, dict):
        restored_theme = normalize_theme_preference(str(user_payload.get("theme_preference") or "dark"))
        conn.execute(
            "UPDATE user SET theme_preference = ?, updated_at = ? WHERE id = ?",
            (restored_theme, now_iso(), int(current_user["id"])),
        )

    competition_id_map: dict[int, int] = {}
    imported_competitions = 0
    imported_races = 0
    imported_goals = 0

    for item in competitions:
        if not isinstance(item, dict):
            raise ValueError("Een competitie in de backup is ongeldig.")
        cur = conn.execute(
            """
            INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
            VALUES(?,?,?,?,?,?)
            """,
            (
                (item.get("name") or "").strip() or "Onbekende wedstrijd",
                (item.get("venue") or "").strip() or None,
                parse_date_any(str(item.get("competition_date") or "")),
                (item.get("notes") or "").strip() or None,
                str(item.get("created_at") or now_iso()),
                int(current_user["id"]),
            ),
        )
        old_id = int(item.get("id") or 0)
        competition_id_map[old_id] = int(cur.lastrowid)
        imported_competitions += 1

    for item in races:
        if not isinstance(item, dict):
            raise ValueError("Een rit in de backup is ongeldig.")
        old_competition_id = int(item.get("competition_id") or 0)
        new_competition_id = competition_id_map.get(old_competition_id)
        if new_competition_id is None:
            continue
        conn.execute(
            """
            INSERT INTO race(
              competition_id, skater_id, distance_m, category, class_name, lane, opponent,
              total_time_ms, laps_csv, dnf, notes, created_at
            )
            VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
            """,
            (
                new_competition_id,
                int(current_user["skater_id"]),
                int(item.get("distance_m") or 0),
                item.get("category"),
                item.get("class_name"),
                (item.get("lane") or "").strip() or None,
                (item.get("opponent") or "").strip() or None,
                int(item["total_time_ms"]) if item.get("total_time_ms") is not None else None,
                (item.get("laps_csv") or "").strip() or None,
                1 if int(item.get("dnf") or 0) == 1 else 0,
                (item.get("notes") or "").strip() or None,
                str(item.get("created_at") or now_iso()),
            ),
        )
        imported_races += 1

    for item in goals:
        if not isinstance(item, dict):
            raise ValueError("Een doel in de backup is ongeldig.")
        upsert_goal_target(
            conn,
            int(current_user["id"]),
            int(item.get("distance_m") or 0),
            int(item["target_time_ms"]) if item.get("target_time_ms") is not None else None,
            int(item["target_opening_ms"]) if item.get("target_opening_ms") is not None else None,
            int(item["target_avg_400_ms"]) if item.get("target_avg_400_ms") is not None else None,
            int(item["target_last_400_ms"]) if item.get("target_last_400_ms") is not None else None,
            int(item["target_fade_400_ms"]) if item.get("target_fade_400_ms") is not None else None,
            str(item.get("notes") or ""),
        )
        imported_goals += 1

    return {
        "competitions": imported_competitions,
        "races": imported_races,
        "goals": imported_goals,
    }


def collect_season_labels(rows: List[sqlite3.Row]) -> List[str]:
    labels = {season_label_for_date(row["competition_date"]) for row in rows if row["competition_date"]}
    return sorted(labels, reverse=True)


def collect_pr_race_ids(rows: List[sqlite3.Row]) -> set[int]:
    best_by_distance: dict[int, int] = {}
    pr_ids: set[int] = set()
    for row in rows:
        if row["distance_m"] is None or row["total_time_ms"] is None or row["dnf"] == 1:
            continue
        distance = int(row["distance_m"])
        total_time_ms = int(row["total_time_ms"])
        current_best = best_by_distance.get(distance)
        if current_best is None or total_time_ms < current_best:
            best_by_distance[distance] = total_time_ms
            pr_ids.add(int(row["id"]))
    return pr_ids


def build_pr_progress(rows: List[sqlite3.Row]) -> dict[int, dict]:
    progress: dict[int, dict] = {}
    best_by_distance: dict[int, int] = {}

    sorted_rows = sorted(
        rows,
        key=lambda row: (
            row["competition_date"] or "",
            int(row["id"]),
        ),
    )

    for row in sorted_rows:
        race_id = int(row["id"])
        progress[race_id] = {
            "is_pr": False,
            "previous_pr_ms": None,
            "delta_vs_previous_pr_ms": None,
            "delta_abs_ms": None,
        }

        if row["distance_m"] is None or row["total_time_ms"] is None or row["dnf"] == 1:
            continue

        distance = int(row["distance_m"])
        total_time_ms = int(row["total_time_ms"])
        previous_best = best_by_distance.get(distance)
        progress[race_id]["previous_pr_ms"] = previous_best

        if previous_best is None or total_time_ms < previous_best:
            progress[race_id]["is_pr"] = True
            if previous_best is not None:
                progress[race_id]["delta_vs_previous_pr_ms"] = total_time_ms - previous_best
                progress[race_id]["delta_abs_ms"] = abs(total_time_ms - previous_best)
            best_by_distance[distance] = total_time_ms
        elif previous_best is not None:
            progress[race_id]["delta_vs_previous_pr_ms"] = total_time_ms - previous_best
            progress[race_id]["delta_abs_ms"] = abs(total_time_ms - previous_best)

    return progress


def summarize_seasons(rows: List[sqlite3.Row], pr_race_ids: set[int]) -> List[dict]:
    grouped: dict[str, list[sqlite3.Row]] = {}
    for row in rows:
        if not row["competition_date"]:
            continue
        grouped.setdefault(season_label_for_date(row["competition_date"]), []).append(row)

    summaries: list[dict] = []
    for label in sorted(grouped, reverse=True):
        season_rows = grouped[label]
        timed_rows = [row for row in season_rows if row["total_time_ms"] is not None and row["dnf"] != 1]
        split_rows = [row for row in timed_rows if laps_from_csv(row["laps_csv"])]
        venues: dict[str, int] = {}
        for row in season_rows:
            if row["venue"]:
                venues[row["venue"]] = venues.get(row["venue"], 0) + 1

        favorite_venue = "-"
        if venues:
            favorite_venue = sorted(venues.items(), key=lambda item: (-item[1], item[0].lower()))[0][0]

        summaries.append(
            {
                "label": label,
                "competition_count": len({row["competition_id"] for row in season_rows}),
                "race_count": len(timed_rows),
                "distance_count": len({row["distance_m"] for row in timed_rows}),
                "split_count": len(split_rows),
                "pr_count": len([row for row in timed_rows if int(row["id"]) in pr_race_ids]),
                "favorite_venue": favorite_venue,
            }
        )

    return summaries


def build_distance_stats(rows: List[sqlite3.Row], pr_race_ids: set[int]) -> List[dict]:
    grouped: dict[int, list[sqlite3.Row]] = {}
    for row in rows:
        if row["distance_m"] is None:
            continue
        grouped.setdefault(int(row["distance_m"]), []).append(row)

    stats: list[dict] = []
    for distance in sorted(grouped):
        distance_rows = grouped[distance]
        timed_rows = [row for row in distance_rows if row["total_time_ms"] is not None and row["dnf"] != 1]
        if not timed_rows:
            continue

        best_race = min(timed_rows, key=lambda row: row["total_time_ms"])
        latest_race = max(timed_rows, key=lambda row: (row["competition_date"], row["id"]))

        opening_values: list[float] = []
        avg400_values: list[float] = []
        last400_values: list[float] = []
        fade_values: list[float] = []
        segment_counts: list[int] = []

        for row in timed_rows:
            laps = laps_from_csv(row["laps_csv"])
            if not laps:
                continue
            metrics = compute_race_metrics(laps, distance)
            opening_values.append(laps[0])
            segment_counts.append(metrics["segment_count"])
            if metrics["avg_400"] is not None:
                avg400_values.append(metrics["avg_400"])
            if metrics["last_400eq"] is not None:
                last400_values.append(metrics["last_400eq"])
            if metrics["fade_400eq"] is not None:
                fade_values.append(metrics["fade_400eq"])

        stats.append(
            {
                "distance_m": distance,
                "count": len(timed_rows),
                "pr_count": len([row for row in timed_rows if int(row["id"]) in pr_race_ids]),
                "split_race_count": len(opening_values),
                "best_time_ms": best_race["total_time_ms"],
                "best_time_race_id": best_race["id"],
                "best_time_date": best_race["competition_date"],
                "latest_time_ms": latest_race["total_time_ms"],
                "latest_race_id": latest_race["id"],
                "latest_date": latest_race["competition_date"],
                "avg_time_ms": int(round(mean(row["total_time_ms"] for row in timed_rows))),
                "opening_m": opening_split_m(distance),
                "best_opening_s": min(opening_values) if opening_values else None,
                "avg_opening_s": mean(opening_values) if opening_values else None,
                "avg_400_s": mean(avg400_values) if avg400_values else None,
                "best_last_400_s": min(last400_values) if last400_values else None,
                "avg_last_400_s": mean(last400_values) if last400_values else None,
                "avg_fade_s": mean(fade_values) if fade_values else None,
                "avg_segments": mean(segment_counts) if segment_counts else None,
            }
        )

    return stats


@app.get("/health")
def health():
    return {"ok": True}


@app.get("/login", response_class=HTMLResponse)
def login_page(request: Request, next: str = "/", error: str = ""):
    if getattr(request.state, "user", None) is not None:
        return RedirectResponse("/", status_code=303)
    next_path = unquote(next)
    next_path = next_path if next_path.startswith("/") else "/"
    return render(request, "login.html", next_path=next_path, error=error)


@app.post("/login")
def login_post(
    request: Request,
    username: str = Form(...),
    password: str = Form(...),
    next: str = Form("/"),
):
    next_path = unquote(next)
    next_path = next_path if next_path.startswith("/") else "/"
    with db() as conn:
        user = get_user_by_username(conn, username.strip())
        if not user or not user["password_hash"] or not verify_password(password, user["password_hash"]):
            return render(
                request,
                "login.html",
                next_path=next_path,
                error="Onjuiste gebruikersnaam of wachtwoord.",
            )

        request.session["user_id"] = int(user["id"])
        conn.execute("UPDATE user SET last_login_at = ? WHERE id = ?", (now_iso(), int(user["id"])))

    return RedirectResponse(next_path, status_code=303)


@app.post("/logout")
def logout(request: Request):
    request.session.clear()
    return RedirectResponse("/login", status_code=303)


@app.get("/account/password")
def account_password_redirect():
    return RedirectResponse("/account/settings", status_code=303)


@app.get("/account/settings", response_class=HTMLResponse)
def account_settings_page(request: Request, error: str = "", success: str = ""):
    current_user = require_user(request)
    return render(request, "account_password.html", user=current_user, error=error, success=success)


@app.get("/account/export")
def account_export(request: Request):
    current_user = require_user(request)
    with db() as conn:
        payload = export_user_data(conn, current_user)
    filename = f"skatestats-export-{current_user['username']}-{datetime.now().strftime('%Y%m%d')}.json"
    return Response(
        content=json.dumps(payload, ensure_ascii=False, indent=2),
        media_type="application/json",
        headers={"Content-Disposition": f'attachment; filename="{filename}"'},
    )


@app.post("/account/import")
async def account_import(request: Request, backup_file: UploadFile = File(...)):
    current_user = require_user(request)
    if not backup_file.filename or not backup_file.filename.lower().endswith(".json"):
        return RedirectResponse("/account/settings?error=importformat", status_code=303)

    raw_payload = await backup_file.read()
    if not raw_payload:
        return RedirectResponse("/account/settings?error=importformat", status_code=303)

    try:
        payload = json.loads(raw_payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return RedirectResponse("/account/settings?error=importformat", status_code=303)

    try:
        with db() as conn:
            summary = import_user_data(conn, current_user, payload)
    except ValueError:
        return RedirectResponse("/account/settings?error=importformat", status_code=303)

    return RedirectResponse(
        f"/account/settings?success=import&imported_competitions={summary['competitions']}&imported_races={summary['races']}&imported_goals={summary['goals']}",
        status_code=303,
    )


@app.post("/account/settings/profile")
def account_settings_profile_post(
    request: Request,
    username: str = Form(...),
    skater_name: str = Form(...),
    theme_preference: str = Form("dark"),
):
    current_user = require_user(request)
    with db() as conn:
        ok, result = update_user_profile(
            conn,
            int(current_user["id"]),
            username,
            skater_name,
            theme_preference,
        )

    if not ok:
        return RedirectResponse(f"/account/settings?error={result}", status_code=303)
    return RedirectResponse("/account/settings?success=profile", status_code=303)


@app.post("/account/settings/password")
def account_settings_password_post(
    request: Request,
    current_password: str = Form(...),
    new_password: str = Form(...),
    confirm_password: str = Form(...),
):
    current_user = require_user(request)
    if not verify_password(current_password, current_user["password_hash"]):
        return RedirectResponse("/account/settings?error=current", status_code=303)
    if len(new_password) < 8:
        return RedirectResponse("/account/settings?error=length", status_code=303)
    if new_password != confirm_password:
        return RedirectResponse("/account/settings?error=confirm", status_code=303)

    with db() as conn:
        set_user_password(conn, int(current_user["id"]), new_password)

    return RedirectResponse("/account/settings?success=password", status_code=303)


@app.post("/account/delete")
def account_delete_post(
    request: Request,
    confirm_username: str = Form(""),
):
    current_user = require_user(request)
    if confirm_username.strip() != current_user["username"]:
        return RedirectResponse("/account/settings?error=deleteconfirm", status_code=303)

    with db() as conn:
        ok, result = delete_user_account(conn, int(current_user["id"]))

    if not ok:
        return RedirectResponse(f"/account/settings?error={result}", status_code=303)
    request.session.clear()
    return RedirectResponse("/login", status_code=303)


@app.get("/admin/users", response_class=HTMLResponse)
def admin_users_page(request: Request, error: str = "", success: str = ""):
    current_user = require_admin_user(request)
    with db() as conn:
        users = conn.execute(
            """
            SELECT u.*, s.name AS skater_name
            FROM user u
            JOIN skater s ON s.id = u.skater_id
            ORDER BY LOWER(u.username)
            """
        ).fetchall()
    return render(
        request,
        "admin_users.html",
        user=current_user,
        users=users,
        error=error,
        success=success,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/admin/users")
def admin_users_create(
    request: Request,
    username: str = Form(...),
    skater_name: str = Form(...),
    password: str = Form(...),
    confirm_password: str = Form(...),
    is_admin: Optional[str] = Form(None),
):
    require_admin_user(request)
    if len(password) < 8:
        return RedirectResponse("/admin/users?error=length", status_code=303)
    if password != confirm_password:
        return RedirectResponse("/admin/users?error=confirm", status_code=303)

    username_value = username.strip()
    skater_name_value = skater_name.strip()
    if not username_value or not skater_name_value:
        return RedirectResponse("/admin/users?error=required", status_code=303)

    with db() as conn:
        if get_user_by_username(conn, username_value):
            return RedirectResponse("/admin/users?error=username", status_code=303)

        skater_row = conn.execute("SELECT id FROM skater WHERE name = ?", (skater_name_value,)).fetchone()
        if skater_row:
            existing_owner = conn.execute(
                "SELECT id FROM user WHERE skater_id = ?",
                (int(skater_row["id"]),),
            ).fetchone()
            if existing_owner:
                return RedirectResponse("/admin/users?error=skater", status_code=303)
            skater_id = int(skater_row["id"])
        else:
            skater_id = get_or_create_skater(conn, skater_name_value)

        conn.execute(
            """
            INSERT INTO user(username, password_hash, skater_id, is_admin, created_at, updated_at)
            VALUES(?,?,?,?,?,?)
            """,
            (
                username_value,
                hash_password(password),
                skater_id,
                1 if is_admin == "on" else 0,
                now_iso(),
                now_iso(),
            ),
        )

    return RedirectResponse("/admin/users?success=created", status_code=303)


@app.post("/admin/users/{user_id}/password")
def admin_user_password_reset(
    request: Request,
    user_id: int,
    new_password: str = Form(...),
    confirm_password: str = Form(...),
):
    admin_user = require_admin_user(request)
    if len(new_password) < 8:
        return RedirectResponse("/admin/users?error=length", status_code=303)
    if new_password != confirm_password:
        return RedirectResponse("/admin/users?error=confirm", status_code=303)

    with db() as conn:
        target_user = get_user_by_id(conn, user_id)
        if not target_user:
            return HTMLResponse("User not found", status_code=404)
        set_user_password(conn, user_id, new_password)

    if int(admin_user["id"]) == user_id:
        request.session["user_id"] = user_id

    return RedirectResponse("/admin/users?success=password", status_code=303)


@app.post("/admin/users/{user_id}/admin")
def admin_user_role_update(
    request: Request,
    user_id: int,
    is_admin: Optional[str] = Form(None),
):
    admin_user = require_admin_user(request)
    with db() as conn:
        target_user = get_user_by_id(conn, user_id)
        if not target_user:
            return HTMLResponse("User not found", status_code=404)
        if int(admin_user["id"]) == user_id and is_admin != "on":
            return RedirectResponse("/admin/users?error=selfadmin", status_code=303)
        conn.execute(
            "UPDATE user SET is_admin = ?, updated_at = ? WHERE id = ?",
            (1 if is_admin == "on" else 0, now_iso(), user_id),
        )

    return RedirectResponse("/admin/users?success=role", status_code=303)


@app.post("/admin/users/{user_id}/delete")
def admin_user_delete(
    request: Request,
    user_id: int,
    confirm_username: str = Form(""),
):
    admin_user = require_admin_user(request)
    with db() as conn:
        target_user = get_user_by_id(conn, user_id)
        if not target_user:
            return HTMLResponse("User not found", status_code=404)
        if confirm_username.strip() != target_user["username"]:
            return RedirectResponse("/admin/users?error=deleteconfirm", status_code=303)

        ok, result = delete_user_account(conn, user_id)

    if not ok:
        return RedirectResponse(f"/admin/users?error={result}", status_code=303)
    if int(admin_user["id"]) == user_id:
        request.session.clear()
        return RedirectResponse("/login", status_code=303)
    return RedirectResponse("/admin/users?success=deleted", status_code=303)


@app.get("/", response_class=HTMLResponse)
def home(
    request: Request,
    trend_period: str = "season",
    trend_date_from: str = "",
    trend_date_to: str = "",
    osta_notice: str = "",
    osta_count: str = "",
):
    current_user = require_user(request)
    osta_detection = {
        "configured": False,
        "available": [],
        "error_message": "",
        "search_name": "",
        "season": "",
        "pid": "",
    }
    latest_comp = None
    latest_comp_races: list[sqlite3.Row] = []
    with db() as conn:
        competition_count = conn.execute(
            "SELECT COUNT(*) AS count FROM competition WHERE owner_user_id = ?",
            (int(current_user["id"]),),
        ).fetchone()["count"]
        comps = conn.execute(
            """
            SELECT id, name, venue, competition_date
            FROM competition
            WHERE owner_user_id = ?
            ORDER BY competition_date DESC, id DESC
            LIMIT 5
            """,
            (int(current_user["id"]),),
        ).fetchall()
        all_races = conn.execute(
            """
            SELECT r.id, r.competition_id, r.distance_m, r.total_time_ms, r.dnf, r.lane,
                   c.name AS competition_name, c.competition_date, c.venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ? AND r.total_time_ms IS NOT NULL
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()
        latest_comp = conn.execute(
            """
            SELECT c.id, c.name, c.venue, c.competition_date, COUNT(r.id) AS race_count
            FROM competition c
            JOIN race r ON r.competition_id = c.id
            WHERE c.owner_user_id = ? AND r.skater_id = ?
            GROUP BY c.id, c.name, c.venue, c.competition_date
            ORDER BY c.competition_date DESC, c.id DESC
            LIMIT 1
            """,
            (int(current_user["id"]), int(current_user["skater_id"])),
        ).fetchone()
        if latest_comp:
            latest_comp_races = conn.execute(
                """
                SELECT r.id, r.distance_m, r.total_time_ms, r.laps_csv, r.dnf
                FROM race r
                JOIN competition c ON c.id = r.competition_id
                WHERE r.competition_id = ? AND c.owner_user_id = ? AND r.skater_id = ?
                ORDER BY r.distance_m ASC, r.id ASC
                """,
                (int(latest_comp["id"]), int(current_user["id"]), int(current_user["skater_id"])),
            ).fetchall()
        osta_detection = detect_osta_updates_for_user(conn, current_user)

    best_times: dict[int, dict] = {}
    trend_rows: list[dict] = []
    races_by_distance: dict[int, list] = {}
    distance_counts: dict[int, int] = {}
    venue_counts: dict[str, int] = {}
    pr_progress = build_pr_progress(all_races)
    for race in all_races:
        races_by_distance.setdefault(race["distance_m"], []).append(race)
        if race["distance_m"] is not None:
            distance = int(race["distance_m"])
            distance_counts[distance] = distance_counts.get(distance, 0) + 1
        if race["venue"]:
            venue_counts[race["venue"]] = venue_counts.get(race["venue"], 0) + 1
        if race["dnf"] != 1:
            current_best = best_times.get(race["distance_m"])
            if current_best is None or race["total_time_ms"] < current_best["total_time_ms"]:
                best_times[race["distance_m"]] = race

    favorite_venue = "-"
    if venue_counts:
        favorite_venue = sorted(venue_counts.items(), key=lambda item: (-item[1], item[0].lower()))[0][0]
    favorite_distance = "-"
    if distance_counts:
        favorite_distance = f"{sorted(distance_counts.items(), key=lambda item: (-item[1], item[0]))[0][0]}m"

    selected_trend_period = trend_period if trend_period in {"month", "season", "custom"} else "season"
    selected_trend_date_from = trend_date_from.strip()
    selected_trend_date_to = trend_date_to.strip()
    trend_error_message = ""
    pr_race_ids = collect_pr_race_ids(all_races)
    latest_comp_analysis = None
    if latest_comp:
        latest_race_rows: list[dict] = []
        for row in latest_comp_races:
            race_id = int(row["id"])
            pr_ctx = pr_progress.get(
                race_id,
                {"is_pr": False, "previous_pr_ms": None},
            )
            previous_pr_ms = pr_ctx.get("previous_pr_ms")
            total_time_ms = row["total_time_ms"]
            pr_gap_ms = None
            if total_time_ms is not None and row["dnf"] != 1 and previous_pr_ms is not None:
                pr_gap_ms = int(total_time_ms) - int(previous_pr_ms)
            laps = laps_from_csv(row["laps_csv"])
            opening_ms = int(round(laps[0] * 1000)) if laps else None
            latest_race_rows.append(
                {
                    **dict(row),
                    "is_pr": bool(pr_ctx.get("is_pr")),
                    "pr_gap_ms": pr_gap_ms,
                    "opening_ms": opening_ms,
                }
            )
        latest_comp_analysis = {
            **dict(latest_comp),
            "races": latest_race_rows,
        }

    today = datetime.now().date()
    filter_start = None
    filter_end = None

    try:
        if selected_trend_period == "month":
            filter_end = today.strftime("%Y-%m-%d")
            filter_start = (today - timedelta(days=30)).strftime("%Y-%m-%d")
        elif selected_trend_period == "season":
            filter_start, filter_end = current_season_bounds(today)
        elif selected_trend_period == "custom":
            filter_start = parse_date_any(selected_trend_date_from) if selected_trend_date_from else None
            filter_end = parse_date_any(selected_trend_date_to) if selected_trend_date_to else None
    except ValueError:
        trend_error_message = "Ongeldig custom datumbereik."
        selected_trend_period = "season"
        filter_start, filter_end = current_season_bounds(today)

    for distance in sorted(races_by_distance):
        rows = races_by_distance[distance]
        valid_rows = [row for row in rows if row["total_time_ms"] is not None and row["dnf"] != 1]
        if filter_start:
            valid_rows = [row for row in valid_rows if row["competition_date"] >= filter_start]
        if filter_end:
            valid_rows = [row for row in valid_rows if row["competition_date"] <= filter_end]
        if not valid_rows:
            continue

        trend_rows.append(
            {
                "distance_m": distance,
                "count": len(valid_rows),
                "sparkline": build_sparkline(valid_rows, filter_start, filter_end),
            }
        )

    recent_pr_cutoff = (today - timedelta(days=7)).strftime("%Y-%m-%d")
    best_times_rows: list[dict] = []
    for distance in sorted(best_times):
        row = dict(best_times[distance])
        row["is_recent_pr"] = (row.get("competition_date") or "") >= recent_pr_cutoff
        best_times_rows.append(row)

    return render(
        request,
        "index.html",
        osta_notice=(osta_notice or "").strip(),
        osta_notice_count=int(osta_count) if (osta_count or "").isdigit() else 0,
        osta_detection=osta_detection,
        comps=comps,
        competition_count=competition_count,
        race_count=len(all_races),
        pr_count=len(pr_race_ids),
        favorite_venue=favorite_venue,
        favorite_distance=favorite_distance,
        best_times=best_times_rows,
        trend_rows=trend_rows,
        selected_trend_period=selected_trend_period,
        selected_trend_date_from=selected_trend_date_from,
        selected_trend_date_to=selected_trend_date_to,
        trend_filters_open=bool(
            trend_error_message
            or selected_trend_period != "season"
            or selected_trend_date_from
            or selected_trend_date_to
        ),
        trend_filter_label=(
            f"{fmt_date_ymd_to_dmy(filter_start)} t/m {fmt_date_ymd_to_dmy(filter_end)}"
            if filter_start and filter_end
            else "Vrij bereik"
        ),
        trend_error_message=trend_error_message,
        latest_comp_analysis=latest_comp_analysis,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.get("/stats", response_class=HTMLResponse)
def stats_page(
    request: Request,
    season: str = "",
    distance_m: str = "",
):
    current_user = require_user(request)
    with db() as conn:
        rows = conn.execute(
            """
            SELECT r.id, r.competition_id, r.distance_m, r.total_time_ms, r.laps_csv, r.dnf,
                   c.name AS competition_name, c.competition_date, c.venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()

    season_options = collect_season_labels(rows)
    selected_season = season.strip()
    current_season = season_label_for_date(datetime.now().strftime("%Y-%m-%d"))
    if selected_season not in season_options:
        selected_season = current_season if current_season in season_options else ""

    selected_distance = distance_m.strip()
    distance_options = sorted({int(row["distance_m"]) for row in rows if row["distance_m"] is not None})
    filtered_rows = list(rows)
    if selected_season:
        season_start, season_end = season_bounds_from_label(selected_season)
        filtered_rows = [
            row for row in filtered_rows if season_start <= row["competition_date"] <= season_end
        ]
    if selected_distance:
        try:
            selected_distance_value = int(selected_distance)
            filtered_rows = [row for row in filtered_rows if int(row["distance_m"]) == selected_distance_value]
        except ValueError:
            selected_distance = ""

    timed_rows = [row for row in filtered_rows if row["total_time_ms"] is not None and row["dnf"] != 1 and row["distance_m"]]
    sorted_timed_rows = sorted(
        timed_rows,
        key=lambda row: (
            row["competition_date"] or "",
            int(row["id"]),
        ),
    )

    pb_race_ids = collect_pr_race_ids(filtered_rows)

    sb_race_ids: set[int] = set()
    sb_best_by_key: dict[tuple[str, int], int] = {}
    for row in sorted_timed_rows:
        season_label = season_label_for_date(row["competition_date"])
        key = (season_label, int(row["distance_m"]))
        total_ms = int(row["total_time_ms"])
        best_value = sb_best_by_key.get(key)
        if best_value is None or total_ms < best_value:
            sb_best_by_key[key] = total_ms
            sb_race_ids.add(int(row["id"]))

    total_distance_km = sum(int(row["distance_m"]) for row in filtered_rows if row["distance_m"] is not None) / 1000.0

    by_distance: dict[int, list[sqlite3.Row]] = {}
    for row in sorted_timed_rows:
        by_distance.setdefault(int(row["distance_m"]), []).append(row)

    sb_reference_season = selected_season or current_season
    average_rows: list[dict] = []
    split_rows: list[dict] = []
    consistency_rows: list[dict] = []
    progress_rows: list[dict] = []

    for distance in sorted(by_distance):
        rows_for_distance = by_distance[distance]
        times = [int(row["total_time_ms"]) for row in rows_for_distance]
        pb_row = min(rows_for_distance, key=lambda row: (int(row["total_time_ms"]), int(row["id"])))
        pb_ms = int(pb_row["total_time_ms"])
        season_subset = [
            row for row in rows_for_distance if season_label_for_date(row["competition_date"]) == sb_reference_season
        ]
        season_best_row = (
            min(season_subset, key=lambda row: (int(row["total_time_ms"]), int(row["id"])))
            if season_subset
            else None
        )
        season_best_ms = int(season_best_row["total_time_ms"]) if season_best_row is not None else None
        avg_ms = int(round(mean(times)))
        median_ms = int(round(median(times)))

        average_rows.append(
            {
                "distance_m": distance,
                "pb_ms": pb_ms,
                "pb_race_id": int(pb_row["id"]),
                "season_best_ms": season_best_ms,
                "season_best_race_id": int(season_best_row["id"]) if season_best_row is not None else None,
                "average_ms": avg_ms,
                "median_ms": median_ms,
            }
        )

        openings: list[float] = []
        full_laps: list[float] = []
        fades: list[float] = []
        lap_values_by_index: dict[int, list[float]] = {}
        for row in rows_for_distance:
            laps = laps_from_csv(row["laps_csv"])
            if not laps:
                continue
            openings.append(laps[0])
            if len(laps) > 1:
                split_laps = laps[1:]
                full_laps.extend(split_laps)
                fades.append(split_laps[-1] - min(split_laps))
                for idx in range(1, len(laps)):
                    lap_values_by_index.setdefault(idx, []).append(laps[idx])

        if openings or full_laps:
            split_rows.append(
                {
                    "distance_m": distance,
                    "avg_opening_s": mean(openings) if openings else None,
                    "best_opening_s": min(openings) if openings else None,
                    "avg_lap_s": mean(full_laps) if full_laps else None,
                    "best_lap_s": min(full_laps) if full_laps else None,
                    "avg_fade_s": mean(fades) if fades else None,
                    "lap_averages": [
                        {"lap_no": idx, "avg_s": mean(values)}
                        for idx, values in sorted(lap_values_by_index.items())
                    ],
                }
            )

        std_ms = int(round(pstdev(times))) if len(times) >= 2 else 0
        range_ms = max(times) - min(times)
        consistency_rows.append(
            {
                "distance_m": distance,
                "std_dev_ms": std_ms,
                "range_ms": range_ms,
            }
        )

        first_row = rows_for_distance[0]
        latest_row = rows_for_distance[-1]
        last5 = rows_for_distance[-5:]
        last5_avg_ms = int(round(mean(int(row["total_time_ms"]) for row in last5))) if last5 else None
        season_avg_ms = (
            int(round(mean(int(row["total_time_ms"]) for row in season_subset)))
            if season_subset
            else None
        )
        trend = "n.v.t."
        if last5_avg_ms is not None and season_avg_ms is not None:
            if last5_avg_ms <= season_avg_ms - 200:
                trend = "verbeterend"
            elif last5_avg_ms >= season_avg_ms + 200:
                trend = "verslechterend"
            else:
                trend = "stabiel"

        progress_rows.append(
            {
                "distance_m": distance,
                "first_ms": int(first_row["total_time_ms"]),
                "first_race_id": int(first_row["id"]),
                "latest_ms": int(latest_row["total_time_ms"]),
                "latest_race_id": int(latest_row["id"]),
                "improvement_ms": int(latest_row["total_time_ms"]) - int(first_row["total_time_ms"]),
                "last5_avg_ms": last5_avg_ms,
                "season_avg_ms": season_avg_ms,
                "trend": trend,
            }
        )

    track_grouped: dict[str, list[sqlite3.Row]] = {}
    for row in sorted_timed_rows:
        venue = (row["venue"] or "").strip()
        if not venue:
            continue
        track_grouped.setdefault(venue, []).append(row)

    track_rows: list[dict] = []
    all_500eq_values: list[int] = []
    for venue, venue_rows in track_grouped.items():
        per_500eq = [
            int(round((int(row["total_time_ms"]) * 500) / int(row["distance_m"])))
            for row in venue_rows
            if int(row["distance_m"]) > 0
        ]
        if not per_500eq:
            continue
        all_500eq_values.extend(per_500eq)
        track_rows.append(
            {
                "track": venue,
                "race_count": len(venue_rows),
                "avg_500eq_ms": int(round(mean(per_500eq))),
                "best_500eq_ms": min(per_500eq),
            }
        )

    track_rows = sorted(track_rows, key=lambda item: (item["avg_500eq_ms"], item["track"].lower()))
    overall_500eq_ms = int(round(mean(all_500eq_values))) if all_500eq_values else None
    best_track_summary = None
    worst_track_summary = None
    if overall_500eq_ms is not None and track_rows:
        best_track = min(track_rows, key=lambda item: item["avg_500eq_ms"])
        worst_track = max(track_rows, key=lambda item: item["avg_500eq_ms"])
        best_track_summary = {
            "name": best_track["track"],
            "delta_ms": best_track["avg_500eq_ms"] - overall_500eq_ms,
        }
        worst_track_summary = {
            "name": worst_track["track"],
            "delta_ms": worst_track["avg_500eq_ms"] - overall_500eq_ms,
        }

    fastest_lap = None
    fastest_opener = None
    for row in sorted_timed_rows:
        laps = laps_from_csv(row["laps_csv"])
        if not laps:
            continue
        opener_ms = int(round(laps[0] * 1000))
        if fastest_opener is None or opener_ms < fastest_opener["time_ms"]:
            fastest_opener = {
                "time_ms": opener_ms,
                "distance_m": int(row["distance_m"]),
                "venue": row["venue"] or "-",
            }
        for lap in laps[1:]:
            lap_ms = int(round(lap * 1000))
            if fastest_lap is None or lap_ms < fastest_lap["time_ms"]:
                fastest_lap = {
                    "time_ms": lap_ms,
                    "distance_m": int(row["distance_m"]),
                    "venue": row["venue"] or "-",
                }

    month_counts: dict[str, int] = {}
    for row in filtered_rows:
        date_value = (row["competition_date"] or "").strip()
        if len(date_value) >= 7:
            month_key = date_value[:7]
            month_counts[month_key] = month_counts.get(month_key, 0) + 1
    busiest_month = None
    if month_counts:
        month_key, month_count = sorted(month_counts.items(), key=lambda item: (-item[1], item[0]))[0]
        busiest_month = {"month": month_key, "count": month_count}

    distance_counts: dict[int, int] = {}
    for row in filtered_rows:
        if row["distance_m"] is None:
            continue
        distance_value = int(row["distance_m"])
        distance_counts[distance_value] = distance_counts.get(distance_value, 0) + 1
    most_skated_distance = None
    if distance_counts:
        distance_value, count_value = sorted(distance_counts.items(), key=lambda item: (-item[1], item[0]))[0]
        most_skated_distance = {"distance_m": distance_value, "count": count_value}

    closest_pb_miss = None
    best_before_by_distance: dict[int, int] = {}
    for row in sorted_timed_rows:
        distance_value = int(row["distance_m"])
        total_ms = int(row["total_time_ms"])
        prev_best = best_before_by_distance.get(distance_value)
        if prev_best is not None and total_ms > prev_best:
            miss_ms = total_ms - prev_best
            if closest_pb_miss is None or miss_ms < closest_pb_miss["delta_ms"]:
                closest_pb_miss = {
                    "delta_ms": miss_ms,
                    "distance_m": distance_value,
                    "venue": row["venue"] or "-",
                }
        if prev_best is None or total_ms < prev_best:
            best_before_by_distance[distance_value] = total_ms

    return render(
        request,
        "stats.html",
        season_options=season_options,
        selected_season=selected_season,
        distance_options=distance_options,
        selected_distance=selected_distance,
        basic_stats={
            "competition_count": len({row["competition_id"] for row in filtered_rows}),
            "race_count": len(filtered_rows),
            "total_km": total_distance_km,
            "pb_count": len(pb_race_ids),
            "sb_count": len(sb_race_ids),
        },
        average_rows=average_rows,
        split_rows=split_rows,
        consistency_rows=consistency_rows,
        track_rows=track_rows,
        best_track_summary=best_track_summary,
        worst_track_summary=worst_track_summary,
        progress_rows=progress_rows,
        fun_stats={
            "closest_pb_miss": closest_pb_miss,
            "fastest_lap": fastest_lap,
            "fastest_opener": fastest_opener,
            "busiest_month": busiest_month,
            "most_skated_distance": most_skated_distance,
        },
        sb_reference_season=sb_reference_season,
        fmt_ms=fmt_ms,
        fmt_sec=fmt_sec,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.get("/goals", response_class=HTMLResponse)
def goals_page(request: Request, success: str = "", error: str = ""):
    current_user = require_user(request)
    with db() as conn:
        goals = get_goal_targets(conn, int(current_user["id"]))
    return render(
        request,
        "goals.html",
        goals=goals,
        distances=SSR_DISTANCES,
        success=success,
        error=error,
        fmt_ms=fmt_ms,
    )


@app.post("/goals")
def goals_save(
    request: Request,
    distance_m: int = Form(...),
    target_time: str = Form(""),
    target_opening: str = Form(""),
    target_avg_400: str = Form(""),
    target_last_400: str = Form(""),
    target_fade_400: str = Form(""),
    notes: str = Form(""),
):
    current_user = require_user(request)
    try:
        target_time_ms = parse_optional_time_to_ms(target_time)
        target_opening_ms = parse_optional_time_to_ms(target_opening)
        target_avg_400_ms = parse_optional_time_to_ms(target_avg_400)
        target_last_400_ms = parse_optional_time_to_ms(target_last_400)
        target_fade_400_ms = parse_optional_time_to_ms(target_fade_400)
    except ValueError:
        return RedirectResponse("/goals?error=time", status_code=303)

    if not any(
        value is not None
        for value in (
            target_time_ms,
            target_opening_ms,
            target_avg_400_ms,
            target_last_400_ms,
            target_fade_400_ms,
        )
    ) and not notes.strip():
        return RedirectResponse("/goals?error=empty", status_code=303)

    with db() as conn:
        upsert_goal_target(
            conn,
            int(current_user["id"]),
            int(distance_m),
            target_time_ms,
            target_opening_ms,
            target_avg_400_ms,
            target_last_400_ms,
            target_fade_400_ms,
            notes,
        )
    return RedirectResponse("/goals?success=saved", status_code=303)


@app.post("/goals/{distance_m}/delete")
def goals_delete(request: Request, distance_m: int):
    current_user = require_user(request)
    with db() as conn:
        delete_goal_target(conn, int(current_user["id"]), distance_m)
    return RedirectResponse("/goals?success=deleted", status_code=303)


@app.get("/competitions", response_class=HTMLResponse)
def competitions(
    request: Request,
    q: str = "",
    venue: str = "",
    date_from: str = "",
    date_to: str = "",
):
    current_user = require_user(request)
    filters = ["owner_user_id = ?"]
    params: list[object] = [int(current_user["id"])]

    selected_query = q.strip()
    selected_venue = venue.strip()
    selected_date_from = date_from.strip()
    selected_date_to = date_to.strip()

    if selected_query:
        filters.append("(LOWER(name) LIKE ? OR LOWER(COALESCE(venue, '')) LIKE ?)")
        query_like = f"%{selected_query.lower()}%"
        params.extend([query_like, query_like])

    if selected_venue:
        filters.append("LOWER(COALESCE(venue, '')) = ?")
        params.append(selected_venue.lower())

    error_message = ""
    try:
        if selected_date_from:
            filters.append("competition_date >= ?")
            params.append(parse_date_any(selected_date_from))
        if selected_date_to:
            filters.append("competition_date <= ?")
            params.append(parse_date_any(selected_date_to))
    except ValueError:
        error_message = "Ongeldige datumfilter."
        filters = ["owner_user_id = ?"]
        params = [int(current_user["id"])]
        if selected_query:
            filters.append("(LOWER(name) LIKE ? OR LOWER(COALESCE(venue, '')) LIKE ?)")
            query_like = f"%{selected_query.lower()}%"
            params.extend([query_like, query_like])
        if selected_venue:
            filters.append("LOWER(COALESCE(venue, '')) = ?")
            params.append(selected_venue.lower())

    where_sql = " AND ".join(filters)

    with db() as conn:
        comps = conn.execute(
            f"""
            SELECT id, name, venue, competition_date, notes
            FROM competition
            WHERE {where_sql}
            ORDER BY competition_date DESC, id DESC
            """,
            params,
        ).fetchall()
        venue_options = conn.execute(
            """
            SELECT DISTINCT venue
            FROM competition
            WHERE owner_user_id = ? AND venue IS NOT NULL AND TRIM(venue) != ''
            ORDER BY venue
            """,
            (int(current_user["id"]),),
        ).fetchall()
    return render(
        request,
        "competitions.html",
        comps=comps,
        venue_options=venue_options,
        selected_query=selected_query,
        selected_venue=selected_venue,
        selected_date_from=selected_date_from,
        selected_date_to=selected_date_to,
        error_message=error_message,
        filters_open=bool(error_message or selected_venue or selected_date_from or selected_date_to),
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.get("/competitions/new", response_class=HTMLResponse)
def competition_new(request: Request, error: str = ""):
    require_user(request)
    return render(request, "competition_new.html", error=error)


@app.post("/competitions/new")
def competitions_new(
    request: Request,
    name: str = Form(...),
    venue: str = Form(""),
    competition_date: str = Form(...),
    notes: str = Form(""),
):
    current_user = require_user(request)
    try:
        comp_date = parse_date_any(competition_date)
    except ValueError:
        return RedirectResponse("/competitions/new?error=date", status_code=303)

    with db() as conn:
        conn.execute(
            """
            INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
            VALUES(?,?,?,?,?,?)
            """,
            (
                name.strip(),
                venue.strip() or None,
                comp_date,
                notes.strip() or None,
                now_iso(),
                int(current_user["id"]),
            ),
        )

    return RedirectResponse("/competitions", status_code=303)


@app.get("/competitions/{competition_id}/edit", response_class=HTMLResponse)
def competition_edit(request: Request, competition_id: int, error: str = ""):
    current_user = require_user(request)
    with db() as conn:
        comp = conn.execute(
            "SELECT * FROM competition WHERE id = ? AND owner_user_id = ?",
            (competition_id, int(current_user["id"])),
        ).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

    return render(request, "competition_edit.html", comp=comp, error=error, fmt_date=fmt_date_ymd_to_dmy)


@app.post("/competitions/{competition_id}/edit")
def competition_edit_post(
    request: Request,
    competition_id: int,
    name: str = Form(...),
    venue: str = Form(""),
    competition_date: str = Form(...),
    notes: str = Form(""),
):
    current_user = require_user(request)
    try:
        comp_date = parse_date_any(competition_date)
    except ValueError:
        return RedirectResponse(f"/competitions/{competition_id}/edit?error=date", status_code=303)

    with db() as conn:
        comp = conn.execute(
            "SELECT id FROM competition WHERE id = ? AND owner_user_id = ?",
            (competition_id, int(current_user["id"])),
        ).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

        conn.execute(
            """
            UPDATE competition
            SET name = ?, venue = ?, competition_date = ?, notes = ?
            WHERE id = ?
            """,
            (
                name.strip(),
                venue.strip() or None,
                comp_date,
                notes.strip() or None,
                competition_id,
            ),
        )

    return RedirectResponse(f"/competitions/{competition_id}", status_code=303)


@app.get("/competitions/{competition_id}", response_class=HTMLResponse)
def competition_detail(request: Request, competition_id: int):
    current_user = require_user(request)
    with db() as conn:
        comp = conn.execute(
            "SELECT * FROM competition WHERE id = ? AND owner_user_id = ?",
            (competition_id, int(current_user["id"])),
        ).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

        races = conn.execute(
            """
            SELECT r.*
            FROM race r
            WHERE r.competition_id = ? AND r.skater_id = ?
            ORDER BY r.distance_m ASC, r.total_time_ms ASC
            """,
            (competition_id, int(current_user["skater_id"])),
        ).fetchall()

    races_enriched = []
    for r in races:
        laps = laps_from_csv(r["laps_csv"])
        metrics = compute_race_metrics(laps, r["distance_m"])
        races_enriched.append((r, metrics))

    return render(
        request,
        "competition_detail.html",
        comp=comp,
        races=races_enriched,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
        format_notes_html=format_notes_html,
    )


@app.post("/competitions/{competition_id}/delete")
def competition_delete(request: Request, competition_id: int):
    current_user = require_user(request)
    with db() as conn:
        comp = conn.execute(
            "SELECT id FROM competition WHERE id = ? AND owner_user_id = ?",
            (competition_id, int(current_user["id"])),
        ).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

        conn.execute("DELETE FROM competition WHERE id = ?", (competition_id,))

    return RedirectResponse("/competitions", status_code=303)


@app.get("/races", response_class=HTMLResponse)
def races(
    request: Request,
    distance_m: Optional[str] = None,
    lane: str = "",
    venue: str = "",
    date_from: str = "",
    date_to: str = "",
):
    current_user = require_user(request)
    filters = ["r.skater_id = ?", "c.owner_user_id = ?"]
    params: list[object] = [int(current_user["skater_id"]), int(current_user["id"])]

    selected_distance = distance_m.strip() if distance_m else ""
    selected_lane = lane.strip()
    selected_venue = venue.strip()
    selected_date_from = date_from.strip()
    selected_date_to = date_to.strip()

    if selected_distance:
        filters.append("r.distance_m = ?")
        params.append(int(selected_distance))

    if selected_lane:
        filters.append("LOWER(COALESCE(r.lane, '')) = ?")
        params.append(selected_lane.lower())

    if selected_venue:
        filters.append("LOWER(COALESCE(c.venue, '')) = ?")
        params.append(selected_venue.lower())

    error_message = ""
    try:
        if selected_date_from:
            filters.append("c.competition_date >= ?")
            params.append(parse_date_any(selected_date_from))

        if selected_date_to:
            filters.append("c.competition_date <= ?")
            params.append(parse_date_any(selected_date_to))
    except ValueError:
        error_message = "Ongeldige datumfilter."
        params = [int(current_user["skater_id"]), int(current_user["id"])]
        filters = ["r.skater_id = ?", "c.owner_user_id = ?"]
        if selected_distance:
            filters.append("r.distance_m = ?")
            params.append(int(selected_distance))
        if selected_lane:
            filters.append("LOWER(COALESCE(r.lane, '')) = ?")
            params.append(selected_lane.lower())
        if selected_venue:
            filters.append("LOWER(COALESCE(c.venue, '')) = ?")
            params.append(selected_venue.lower())

    where_sql = " AND ".join(filters)

    with db() as conn:
        race_rows = conn.execute(
            f"""
            SELECT r.*, c.name AS competition_name, c.venue, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE {where_sql}
            ORDER BY c.competition_date DESC, r.distance_m ASC, r.total_time_ms ASC, r.id DESC
            """,
            params,
        ).fetchall()
        lane_options = conn.execute(
            """
            SELECT DISTINCT lane
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ? AND lane IS NOT NULL AND TRIM(lane) != ''
            ORDER BY lane
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()
        venue_options = conn.execute(
            """
            SELECT DISTINCT c.venue AS venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ? AND c.venue IS NOT NULL AND TRIM(c.venue) != ''
            ORDER BY c.venue
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()
        all_owner_races = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()

    pr_progress = build_pr_progress(all_owner_races)
    return render(
        request,
        "races.html",
        races=[{**dict(row), **pr_progress.get(int(row["id"]), {})} for row in race_rows],
        lane_options=lane_options,
        venue_options=venue_options,
        selected_distance=selected_distance,
        selected_lane=selected_lane,
        selected_venue=selected_venue,
        selected_date_from=selected_date_from,
        selected_date_to=selected_date_to,
        error_message=error_message,
        filters_open=bool(
            error_message
            or selected_distance
            or selected_lane
            or selected_venue
            or selected_date_from
            or selected_date_to
        ),
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.get("/races/new", response_class=HTMLResponse)
def race_new(request: Request, competition_id: Optional[int] = None):
    current_user = require_user(request)
    with db() as conn:
        comps = conn.execute(
            """
            SELECT id, name, competition_date
            FROM competition
            WHERE owner_user_id = ?
            ORDER BY competition_date DESC, id DESC
            LIMIT 10
            """,
            (int(current_user["id"]),),
        ).fetchall()
        if competition_id and not any(c["id"] == competition_id for c in comps):
            selected_comp = conn.execute(
                """
                SELECT id, name, competition_date
                FROM competition
                WHERE id = ? AND owner_user_id = ?
                """,
                (competition_id, int(current_user["id"])),
            ).fetchone()
            if selected_comp:
                comps = [selected_comp, *comps]
    return render(
        request,
        "race_new.html",
        comps=comps,
        selected_competition_id=competition_id,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/races/new")
def race_new_post(
    request: Request,
    competition_id: Optional[str] = Form(None),
    new_competition_name: str = Form(""),
    new_competition_venue: str = Form(""),
    new_competition_date: str = Form(""),
    distance_m: int = Form(...),
    lane: str = Form(""),
    opponent: str = Form(""),
    laps: str = Form(""),
    dnf: Optional[str] = Form(None),
    notes: str = Form(""),
):
    current_user = require_user(request)
    competition_id = int(competition_id) if competition_id else None
    dnf_val = 1 if dnf == "on" else 0

    # If no competition selected, create one
    if not competition_id:
        if not new_competition_name.strip() or not new_competition_date.strip():
            return RedirectResponse("/races/new?error=competition", status_code=303)

        try:
            comp_date = parse_date_any(new_competition_date)
        except ValueError:
            return RedirectResponse("/races/new?error=date", status_code=303)

        with db() as conn:
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    new_competition_name.strip(),
                    new_competition_venue.strip() or None,
                    comp_date,
                    "Created via new time form",
                    now_iso(),
                    int(current_user["id"]),
                ),
            )
            competition_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]
    else:
        with db() as conn:
            comp = conn.execute(
                "SELECT id FROM competition WHERE id = ? AND owner_user_id = ?",
                (competition_id, int(current_user["id"])),
            ).fetchone()
            if not comp:
                return HTMLResponse("Competition not found", status_code=404)

    laps_ms, total_ms, err = parse_laps_to_ms(laps)
    if err:
        return RedirectResponse("/races/new?error=laps", status_code=303)

    laps_csv = ",".join([f"{(ms/1000.0):.2f}" for ms in laps_ms]) if laps_ms else None

    with db() as conn:
        cur = conn.execute(
            """
            INSERT INTO race(
              competition_id, skater_id, distance_m, category, class_name, lane, opponent,
              total_time_ms, laps_csv, dnf, notes, created_at
            )
            VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
            """,
            (
                competition_id,
                int(current_user["skater_id"]),
                int(distance_m),
                None,
                None,
                lane.strip() or None,
                opponent.strip() or None,
                total_ms,
                laps_csv,
                dnf_val,
                notes.strip() or None,
                now_iso(),
            ),
        )
        race_id = cur.lastrowid

    return RedirectResponse(f"/races/{race_id}", status_code=303)


@app.get("/races/{race_id}", response_class=HTMLResponse)
def race_detail(request: Request, race_id: int):
    current_user = require_user(request)
    with db() as conn:
        r = conn.execute(
            """
            SELECT r.*, c.name AS competition_name, c.venue, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.id = ? AND r.skater_id = ? AND c.owner_user_id = ?
            """,
            (race_id, int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchone()
        history_rows = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()
    if not r:
        return HTMLResponse("Race not found", status_code=404)

    laps = laps_from_csv(r["laps_csv"])
    split_rows = build_split_rows(laps, r["distance_m"])
    metrics = compute_race_metrics(laps, r["distance_m"])
    split_chart = build_split_chart(laps)
    pr_progress = build_pr_progress(history_rows)
    pr_context = pr_progress.get(
        race_id,
        {"is_pr": False, "previous_pr_ms": None, "delta_vs_previous_pr_ms": None, "delta_abs_ms": None},
    )

    return render(
        request,
        "race_detail.html",
        race=r,
        laps=laps,
        split_rows=split_rows,
        metrics=metrics,
        split_chart=split_chart,
        pr_context=pr_context,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
        fmt_sec=fmt_sec,
        format_notes_html=format_notes_html,
    )


@app.get("/races/{race_id}/compare", response_class=HTMLResponse)
def race_compare(request: Request, race_id: int, compare_race_id: str = ""):
    current_user = require_user(request)
    with db() as conn:
        base_race = conn.execute(
            """
            SELECT r.*, c.name AS competition_name, c.venue, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.id = ? AND r.skater_id = ? AND c.owner_user_id = ?
            """,
            (race_id, int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchone()
        if not base_race:
            return HTMLResponse("Race not found", status_code=404)

        comparison_candidates = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.laps_csv, r.dnf, r.lane, r.opponent,
                   c.name AS competition_name, c.venue, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ? AND r.distance_m = ? AND r.id != ?
            ORDER BY c.competition_date DESC, r.id DESC
            """,
            (int(current_user["skater_id"]), int(current_user["id"]), int(base_race["distance_m"]), race_id),
        ).fetchall()

    selected_compare_id = compare_race_id.strip()
    compare_race = None
    if selected_compare_id:
        try:
            compare_id_value = int(selected_compare_id)
            compare_race = next((row for row in comparison_candidates if int(row["id"]) == compare_id_value), None)
        except ValueError:
            compare_race = None

    if compare_race is None:
        selected_compare_id = ""

    comparison = build_comparison_context(base_race, compare_race)
    swap_href = None
    if compare_race is not None:
        swap_href = f"/races/{int(compare_race['id'])}/compare?compare_race_id={int(base_race['id'])}"

    return render(
        request,
        "race_compare.html",
        base_race=base_race,
        compare_race=compare_race,
        comparison_candidates=comparison_candidates,
        selected_compare_id=selected_compare_id,
        auto_open_compare_modal=bool(comparison_candidates) and compare_race is None,
        comparison=comparison,
        swap_href=swap_href,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
        format_delta=format_delta,
    )


@app.post("/races/{race_id}/delete")
def race_delete(request: Request, race_id: int):
    current_user = require_user(request)
    with db() as conn:
        race = conn.execute(
            """
            SELECT r.id, r.competition_id
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.id = ? AND r.skater_id = ? AND c.owner_user_id = ?
            """,
            (race_id, int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchone()
        if not race:
            return HTMLResponse("Race not found", status_code=404)

        conn.execute("DELETE FROM race WHERE id = ?", (race_id,))

    return RedirectResponse(f"/competitions/{race['competition_id']}", status_code=303)


# -----------------------
# Edit race
# -----------------------

@app.get("/races/{race_id}/edit", response_class=HTMLResponse)
def race_edit(request: Request, race_id: int):
    current_user = require_user(request)
    with db() as conn:
        r = conn.execute(
            """
            SELECT r.*, c.name AS competition_name, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.id = ? AND r.skater_id = ? AND c.owner_user_id = ?
            """,
            (race_id, int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchone()

        if not r:
            return HTMLResponse("Race not found", status_code=404)

        comps = conn.execute(
            """
            SELECT id, name, competition_date
            FROM competition
            WHERE owner_user_id = ?
            ORDER BY competition_date DESC
            """,
            (int(current_user["id"]),),
        ).fetchall()

    return render(
        request,
        "race_edit.html",
        race=r,
        comps=comps,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/races/{race_id}/edit")
def race_edit_post(
    request: Request,
    race_id: int,
    competition_id: Optional[str] = Form(None),
    new_competition_name: str = Form(""),
    new_competition_venue: str = Form(""),
    new_competition_date: str = Form(""),
    distance_m: int = Form(...),
    lane: str = Form(""),
    opponent: str = Form(""),
    laps: str = Form(""),
    dnf: Optional[str] = Form(None),
    notes: str = Form(""),
):
    current_user = require_user(request)
    competition_id = int(competition_id) if competition_id else None
    dnf_val = 1 if dnf == "on" else 0

    # Ensure this race belongs to owner
    with db() as conn:
        owns = conn.execute(
            """
            SELECT r.id
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.id = ? AND r.skater_id = ? AND c.owner_user_id = ?
            """,
            (race_id, int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchone()
        if not owns:
            return HTMLResponse("Race not found", status_code=404)

    # Create new competition if needed
    if not competition_id:
        if not new_competition_name.strip() or not new_competition_date.strip():
            return RedirectResponse(f"/races/{race_id}/edit?error=competition", status_code=303)

        try:
            comp_date = parse_date_any(new_competition_date)
        except ValueError:
            return RedirectResponse(f"/races/{race_id}/edit?error=date", status_code=303)

        with db() as conn:
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    new_competition_name.strip(),
                    new_competition_venue.strip() or None,
                    comp_date,
                    "Created via edit form",
                    now_iso(),
                    int(current_user["id"]),
                ),
            )
            competition_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]
    else:
        with db() as conn:
            comp = conn.execute(
                "SELECT id FROM competition WHERE id = ? AND owner_user_id = ?",
                (competition_id, int(current_user["id"])),
            ).fetchone()
            if not comp:
                return HTMLResponse("Competition not found", status_code=404)

    laps_ms, total_ms, err = parse_laps_to_ms(laps)
    if err:
        return RedirectResponse(f"/races/{race_id}/edit?error=laps", status_code=303)

    laps_csv = ",".join([f"{(ms/1000.0):.2f}" for ms in laps_ms]) if laps_ms else None

    with db() as conn:
        conn.execute(
            """
            UPDATE race
            SET competition_id = ?,
                distance_m = ?,
                category = NULL,
                class_name = NULL,
                lane = ?,
                opponent = ?,
                total_time_ms = ?,
                laps_csv = ?,
                dnf = ?,
                notes = ?
            WHERE id = ?
            """,
            (
                competition_id,
                int(distance_m),
                lane.strip() or None,
                opponent.strip() or None,
                total_ms,
                laps_csv,
                dnf_val,
                notes.strip() or None,
                race_id,
            ),
        )

    return RedirectResponse(f"/races/{race_id}", status_code=303)


# -----------------------
# Import
# -----------------------

def parse_time_to_ms(t: str) -> int:
    t = t.strip()
    if ":" in t:
        m, rest = t.split(":", 1)
        sec = float(rest)
        total = int(m) * 60 + sec
    else:
        total = float(t)
    return int(round(total * 1000))


PDF_LANE_MAP = {
    "gl": "Binnen",
    "wt": "Binnen",
    "bl": "Buiten",
    "rd": "Buiten",
}


PDF_STATUS_VALUES = {"DNF", "DNS", "DSQ", "DQ", "WDR", "NC"}


def normalize_pdf_venue(raw_value: str) -> Optional[str]:
    value = (raw_value or "").strip()
    if not value:
        return None
    if " - " in value:
        value = value.split(" - ", 1)[1].strip()
    if re.search(r"\([A-Z]{3}\)\s*$", value):
        return value
    return f"{value} (NED)"


def parse_pdf_skater_line(line: str) -> Optional[dict]:
    match = re.match(
        r"^(gl|bl|wt|rd)\s+\d+\s+(.+?)\s+([A-Z][A-Z0-9]{1,5})\s+([0-9:.]+)\s+([0-9:.]+|DNF|DNS|DSQ|DQ|WDR|NC)\b",
        (line or "").strip(),
        re.IGNORECASE,
    )
    if not match:
        return None
    return {
        "lane_code": match.group(1).lower(),
        "name": match.group(2).strip(),
        "cat": match.group(3).strip(),
        "pr": match.group(4).strip(),
        "time": match.group(5).strip(),
    }


def parse_pdf_timing_line(line: str) -> Optional[dict]:
    dual_match = re.match(
        r"^(\d+)m\s+([0-9:.]+)\s+\(([0-9:.]+)\)\s+(\d+)m\s+([0-9:.]+)\s+\(([0-9:.]+)\)$",
        (line or "").strip(),
    )
    if dual_match:
        return {
            "distance_m": int(dual_match.group(1)),
            "totals": [dual_match.group(2).strip(), dual_match.group(5).strip()],
            "laps": [dual_match.group(3).strip(), dual_match.group(6).strip()],
        }

    single_match = re.match(
        r"^(\d+)m\s+([0-9:.]+)\s+\(([0-9:.]+)\)$",
        (line or "").strip(),
    )
    if single_match:
        return {
            "distance_m": int(single_match.group(1)),
            "single_total": single_match.group(2).strip(),
            "single_lap": single_match.group(3).strip(),
        }

    return None


def active_pdf_timing_index(skaters: list[dict]) -> Optional[int]:
    candidates: list[int] = []
    for idx, skater in enumerate(skaters):
        raw_time = (skater.get("time") or "").strip().upper()
        if raw_time and raw_time not in PDF_STATUS_VALUES:
            candidates.append(idx)
    if len(candidates) == 1:
        return candidates[0]
    return None


def extract_pdf_pair_blocks(page_text: str) -> list[dict]:
    lines = [(line or "").strip() for line in (page_text or "").splitlines()]
    blocks: list[dict] = []
    idx = 0
    while idx < len(lines):
        if lines[idx] != "Naam Cat PR Tijd Info":
            idx += 1
            continue

        if idx + 6 >= len(lines):
            break

        first = parse_pdf_skater_line(lines[idx + 1])
        second = parse_pdf_skater_line(lines[idx + 3])
        pair_line = lines[idx + 2]
        if not first or not second or not re.fullmatch(r"\d+", pair_line):
            idx += 1
            continue

        skaters = [first, second]
        active_index = active_pdf_timing_index(skaters)
        timing_rows: list[dict] = []
        cursor = idx + 5
        while cursor < len(lines):
            parsed_timing = parse_pdf_timing_line(lines[cursor])
            if not parsed_timing:
                break
            if "single_total" in parsed_timing:
                if active_index is None:
                    cursor += 1
                    continue
                totals: list[Optional[str]] = [None, None]
                laps: list[Optional[str]] = [None, None]
                totals[active_index] = parsed_timing["single_total"]
                laps[active_index] = parsed_timing["single_lap"]
                parsed_timing = {
                    "distance_m": int(parsed_timing["distance_m"]),
                    "totals": totals,
                    "laps": laps,
                }
            timing_rows.append(parsed_timing)
            cursor += 1

        if timing_rows:
            blocks.append(
                {
                    "pair_no": int(pair_line),
                    "skaters": skaters,
                    "timings": timing_rows,
                }
            )
            idx = cursor
            continue

        idx += 1

    return blocks


def extract_pdf_page_date(page_text: str, fallback_date: Optional[str] = None) -> Optional[str]:
    text = page_text or ""
    match = re.search(r"\bVan\s+(\d{1,2}-\d{1,2}-\d{4})\b", text, flags=re.IGNORECASE)
    if match:
        try:
            return parse_date_any(match.group(1))
        except ValueError:
            pass

    for candidate in re.findall(r"\b\d{1,2}-\d{1,2}-\d{4}\b", text):
        try:
            return parse_date_any(candidate)
        except ValueError:
            continue

    return fallback_date


def extract_pdf_results_for_skater(pdf_bytes: bytes, skater_name: str, source_filename: str = "") -> dict:
    target_name = (skater_name or "").strip()
    if not target_name:
        raise ValueError("Geen schaatsersnaam ingesteld om in de PDF te zoeken.")
    if not pdf_bytes:
        raise ValueError("Lege PDF upload.")

    try:
        with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
            texts = [(page.extract_text() or "").strip() for page in pdf.pages]
    except Exception as exc:  # pragma: no cover - depends on parser internals
        raise ValueError("Kon de PDF niet lezen.") from exc

    non_empty_pages = [text for text in texts if text]
    if not non_empty_pages:
        raise ValueError("PDF bevat geen leesbare tekst.")

    header_lines = [line.strip() for line in non_empty_pages[0].splitlines() if line.strip()]
    if len(header_lines) < 3:
        raise ValueError("Kon wedstrijdgegevens niet uit de PDF-header halen.")

    competition_name_raw = header_lines[0]
    competition_name = clean_competition_name(competition_name_raw) or competition_name_raw
    header_date = extract_date_from_text(header_lines[2])
    competition_venue = normalize_pdf_venue(header_lines[1])

    target_norm = norm_name(target_name)
    competitions_by_date: dict[str, dict] = {}
    last_page_date = header_date

    for text in non_empty_pages:
        page_date = extract_pdf_page_date(text, last_page_date)
        if page_date:
            last_page_date = page_date

        for block in extract_pdf_pair_blocks(text):
            skaters = block["skaters"]
            timings = block["timings"]
            match_index = -1
            for idx, skater in enumerate(skaters):
                if norm_name(skater["name"]) == target_norm:
                    match_index = idx
                    break
            if match_index < 0:
                continue

            own_skater = skaters[match_index]
            opponent = skaters[1 - match_index]
            final_timing = timings[-1]
            total_raw = final_timing["totals"][match_index] or own_skater["time"]
            total_upper = total_raw.upper()
            if total_upper in PDF_STATUS_VALUES:
                total_time_ms = None
                dnf = 1
            else:
                try:
                    total_time_ms = parse_time_to_ms(total_raw)
                except ValueError:
                    continue
                dnf = 0

            lap_values: list[str] = []
            for timing in timings:
                lap_raw = timing["laps"][match_index]
                if not lap_raw:
                    continue
                try:
                    lap_ms = parse_time_to_ms(lap_raw)
                except ValueError:
                    continue
                lap_values.append(f"{lap_ms / 1000.0:.2f}")

            lane_value = PDF_LANE_MAP.get(own_skater["lane_code"], own_skater["lane_code"].upper())
            opponent_name = opponent["name"]
            if (opponent.get("time") or "").strip().upper() in PDF_STATUS_VALUES:
                opponent_name = ""
            source_hint = (source_filename or "").strip()
            source_text = source_hint if source_hint else "PDF uitslag"
            race_date = page_date or header_date
            if not race_date:
                continue

            competition_item = competitions_by_date.setdefault(
                race_date,
                {
                    "competition": {
                        "name": competition_name,
                        "date": race_date,
                        "venue": competition_venue,
                        "notes": f"Geimporteerd van PDF: {(source_filename or '').strip() or 'uitslag PDF'}",
                    },
                    "results": [],
                },
            )

            competition_item["results"].append(
                {
                    "pair_no": block["pair_no"],
                    "distance_m": int(final_timing["distance_m"]),
                    "lane": lane_value,
                    "opponent": opponent_name,
                    "total_time_ms": total_time_ms,
                    "laps_csv": ",".join(lap_values) if lap_values else None,
                    "dnf": dnf,
                    "notes": f"Geimporteerd van PDF: {source_text}",
                }
            )

    competitions = [competitions_by_date[key] for key in sorted(competitions_by_date)]
    competitions = [item for item in competitions if item["results"]]
    if not competitions:
        raise ValueError(f"Geen ritten gevonden voor '{target_name}' in deze PDF.")

    for item in competitions:
        item["results"].sort(key=lambda row: (int(row["pair_no"]), int(row["distance_m"])))

    response = {"competitions": competitions}
    if len(competitions) == 1:
        response["competition"] = competitions[0]["competition"]
        response["results"] = competitions[0]["results"]
    return response


def append_note(existing_note: Optional[str], extra_note: str) -> str:
    current = (existing_note or "").strip()
    extra = (extra_note or "").strip()
    if not current:
        return extra
    if not extra or extra in current:
        return current
    return f"{current}\n{extra}"


def source_note(source_name: str, url: Optional[str]) -> str:
    url_value = (url or "").strip()
    if not url_value:
        return f"Geïmporteerd van {source_name}"
    return f"Geïmporteerd van {source_name}: {url_value}"


def update_note(source_name: str, url: Optional[str]) -> str:
    url_value = (url or "").strip()
    if not url_value:
        return f"Rondetijden van {source_name}"
    return f"Rondetijden van {source_name}: {url_value}"


def normalize_note_line(line: str) -> str:
    if line.startswith("Imported from OSTA:"):
        return source_note("OSTA", line.split(":", 1)[1].strip())

    if line.startswith("Imported from SpeedSkatingResults:"):
        raw_value = line.split(":", 1)[1].strip()
        if raw_value.startswith("{"):
            try:
                payload = json.loads(raw_value)
            except json.JSONDecodeError:
                payload = None
            if isinstance(payload, dict):
                return source_note("SpeedSkatingResults", str(payload.get("link") or ""))
        url_match = re.search(r"https?://\S+", raw_value)
        if url_match:
            return source_note("SpeedSkatingResults", url_match.group(0))
        return source_note("SpeedSkatingResults", "")

    if line.startswith("Imported from SpeedSkatingResults season "):
        url_match = re.search(r"https?://\S+", line)
        return source_note("SpeedSkatingResults", url_match.group(0) if url_match else "")

    if line.startswith("Imported from OSTA pid "):
        pid_value = line.removeprefix("Imported from OSTA pid ").strip()
        return source_note("OSTA", f"{OSTA_BASE}index.php?pid={quote(pid_value)}" if pid_value else "")

    if line.startswith("OSTA sync via pid "):
        return update_note("OSTA", None)

    return line


def format_notes_html(notes: Optional[str]) -> Markup:
    parts: list[str] = []
    for raw_line in (notes or "").splitlines():
        line = normalize_note_line(raw_line.strip())
        if not line:
            continue
        source_match = SOURCE_NOTE_RE.match(line)
        if source_match:
            prefix, source_name, url = source_match.groups()
            parts.append(
                f'{escape(prefix)} <a href="{escape(url)}" target="_blank" rel="noreferrer">{escape(source_name)}</a>'
            )
            continue
        match = URL_LINE_RE.match(line)
        if match:
            prefix, url = match.groups()
            parts.append(
                f'{escape(prefix)}<a href="{escape(url)}" target="_blank" rel="noreferrer">{escape(url)}</a>'
            )
            continue
        parts.append(escape(line))
    return Markup("<br>".join(parts))


IMPORT_PREVIEW_NEW = "new"
IMPORT_PREVIEW_BLACKLIST = "blacklist"
IMPORT_PREVIEW_OVERLAP = "overlap"
IMPORT_PREVIEW_STATUS_ORDER = (IMPORT_PREVIEW_NEW, IMPORT_PREVIEW_BLACKLIST, IMPORT_PREVIEW_OVERLAP)


def import_source_label(source: str) -> str:
    source_value = (source or "").strip().lower()
    if source_value == "osta":
        return "OSTA"
    if source_value == "ssr":
        return "SpeedSkatingResults"
    if source_value == "pdf":
        return "PDF"
    return source_value or "Import"


def import_competition_signature(source: str, competition: dict, source_meta: Optional[dict] = None) -> str:
    source_value = (source or "").strip().lower()
    comp_date = (competition.get("date") or "").strip()
    comp_name = (competition.get("name") or "").strip()
    source_meta = source_meta or {}

    if source_value == "osta":
        pid_value = str(source_meta.get("pid") or competition.get("source_pid") or "").strip()
        return osta_competition_signature(comp_date, comp_name, pid_value)
    if source_value == "ssr":
        skater_id = str(source_meta.get("ssr_skater_id") or "").strip()
        return f"ssr|{comp_date}|{norm_name(comp_name)}|{skater_id}"
    if source_value == "pdf":
        venue = (competition.get("venue") or "").strip()
        return f"pdf|{comp_date}|{norm_name(comp_name)}|{norm_name(venue)}"
    return f"{source_value}|{comp_date}|{norm_name(comp_name)}"


def fetch_existing_competition_dates(conn: sqlite3.Connection, user_id: int) -> set[str]:
    return {
        row["competition_date"]
        for row in conn.execute(
            """
            SELECT competition_date
            FROM competition
            WHERE owner_user_id = ?
            """,
            (user_id,),
        ).fetchall()
    }


def fetch_blacklisted_signatures(conn: sqlite3.Connection, user_id: int) -> set[str]:
    return {
        row["comp_signature"]
        for row in conn.execute(
            """
            SELECT comp_signature
            FROM osta_import_blacklist
            WHERE user_id = ?
            """,
            (user_id,),
        ).fetchall()
    }


def list_blacklist_items(conn: sqlite3.Connection, user_id: int) -> list[sqlite3.Row]:
    return conn.execute(
        """
        SELECT comp_signature, comp_name, comp_date, pid, race_count, created_at
        FROM osta_import_blacklist
        WHERE user_id = ?
        ORDER BY comp_date DESC, created_at DESC, comp_name COLLATE NOCASE ASC
        """,
        (user_id,),
    ).fetchall()


def build_import_preview_items(
    conn: sqlite3.Connection,
    current_user: sqlite3.Row,
    source: str,
    parsed: dict,
    source_meta: Optional[dict] = None,
) -> list[dict]:
    user_id = int(current_user["id"])
    existing_dates = fetch_existing_competition_dates(conn, user_id)
    blacklisted = fetch_blacklisted_signatures(conn, user_id)
    source_value = (source or "").strip().lower()
    source_meta = source_meta or {}

    competitions = parsed.get("competitions")
    if not competitions and parsed.get("competition"):
        competitions = [{"competition": parsed["competition"], "results": parsed.get("results") or []}]
    competitions = competitions or []

    items: list[dict] = []
    for idx, item in enumerate(competitions):
        competition = item.get("competition") or {}
        results = item.get("results") or []
        signature = import_competition_signature(source_value, competition, source_meta)
        status = IMPORT_PREVIEW_NEW
        if signature in blacklisted:
            status = IMPORT_PREVIEW_BLACKLIST
        elif (competition.get("date") or "").strip() in existing_dates:
            status = IMPORT_PREVIEW_OVERLAP

        items.append(
            {
                "id": str(idx),
                "status": status,
                "selected_default": 1 if status == IMPORT_PREVIEW_NEW else 0,
                "signature": signature,
                "competition": competition,
                "results": results,
                "race_count": len(results),
            }
        )

    return items


def create_import_preview_batch(
    conn: sqlite3.Connection,
    current_user: sqlite3.Row,
    source: str,
    source_meta: dict,
    items: list[dict],
) -> str:
    batch_id = uuid.uuid4().hex
    conn.execute(
        """
        INSERT INTO import_preview_batch(id, user_id, source, payload_json, created_at)
        VALUES(?,?,?,?,?)
        """,
        (
            batch_id,
            int(current_user["id"]),
            (source or "").strip().lower(),
            json.dumps({"meta": source_meta, "items": items}, ensure_ascii=False),
            now_iso(),
        ),
    )
    return batch_id


def load_import_preview_batch(
    conn: sqlite3.Connection,
    current_user: sqlite3.Row,
    batch_id: str,
) -> Optional[dict]:
    row = conn.execute(
        """
        SELECT id, source, payload_json
        FROM import_preview_batch
        WHERE id = ? AND user_id = ?
        """,
        (batch_id, int(current_user["id"])),
    ).fetchone()
    if not row:
        return None
    try:
        payload = json.loads(row["payload_json"])
    except json.JSONDecodeError:
        return None
    return {
        "id": row["id"],
        "source": row["source"],
        "meta": payload.get("meta") or {},
        "items": payload.get("items") or [],
    }


def delete_import_preview_batch(conn: sqlite3.Connection, batch_id: str, user_id: int) -> None:
    conn.execute(
        """
        DELETE FROM import_preview_batch
        WHERE id = ? AND user_id = ?
        """,
        (batch_id, user_id),
    )


def preview_cards(items: list[dict]) -> dict[str, list[dict]]:
    cards = {key: [] for key in IMPORT_PREVIEW_STATUS_ORDER}
    for item in items:
        status = item.get("status") or IMPORT_PREVIEW_OVERLAP
        if status not in cards:
            status = IMPORT_PREVIEW_OVERLAP
        cards[status].append(item)
    return cards


def render_import_preview_page(
    request: Request,
    current_user: sqlite3.Row,
    batch: dict,
    error_message: str = "",
) -> HTMLResponse:
    items = batch.get("items") or []
    cards = preview_cards(items)
    return render(
        request,
        "import_preview.html",
        source_label=import_source_label(batch.get("source", "")),
        fmt_date=fmt_date_ymd_to_dmy,
        fmt_ms=fmt_ms,
        batch_id=batch["id"],
        items=items,
        card_new=cards[IMPORT_PREVIEW_NEW],
        card_blacklist=cards[IMPORT_PREVIEW_BLACKLIST],
        card_overlap=cards[IMPORT_PREVIEW_OVERLAP],
        preview_error_message=error_message,
        upload_owner_name=current_user["skater_name"],
    )


def default_osta_search_name(skater_name: str) -> str:
    return (skater_name or "").strip()


def normalize_osta_venue(raw_value: Optional[str]) -> Optional[str]:
    value = (raw_value or "").strip()
    if not value:
        return None
    upper_value = value.upper()
    return OSTA_VENUE_MAP.get(upper_value, value)


def normalize_osta_season(raw_value: str) -> str:
    value = (raw_value or "").strip().upper()
    if not value:
        return default_ssr_season()
    if value == "ALL":
        return value
    if re.fullmatch(r"\d{4}", value):
        return value
    raise ValueError("OSTA seizoen moet een startjaar zijn, bijvoorbeeld 2025, of ALL.")


def get_osta_monitor_config(conn: sqlite3.Connection, user_id: int) -> Optional[sqlite3.Row]:
    return conn.execute(
        """
        SELECT user_id, search_name, pid, season, updated_at
        FROM osta_monitor_config
        WHERE user_id = ?
        """,
        (user_id,),
    ).fetchone()


def upsert_osta_monitor_config(
    conn: sqlite3.Connection,
    user_id: int,
    search_name: str,
    season: str,
    pid: str = "",
) -> None:
    conn.execute(
        """
        INSERT INTO osta_monitor_config(user_id, search_name, pid, season, updated_at)
        VALUES(?,?,?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
          search_name = excluded.search_name,
          pid = excluded.pid,
          season = excluded.season,
          updated_at = excluded.updated_at
        """,
        (
            user_id,
            default_osta_search_name(search_name),
            (pid or "").strip(),
            normalize_osta_season(season),
            now_iso(),
        ),
    )


def osta_competition_signature(comp_date: str, comp_name: str, pid: str) -> str:
    normalized_name = norm_name(comp_name)
    normalized_pid = (pid or "").strip().lower()
    return f"{comp_date}|{normalized_name}|{normalized_pid}"


def list_new_osta_competitions(
    conn: sqlite3.Connection,
    current_user: sqlite3.Row,
    parsed: dict,
) -> list[dict]:
    existing_dates = {
        row["competition_date"]
        for row in conn.execute(
            """
            SELECT competition_date
            FROM competition
            WHERE owner_user_id = ?
            """,
            (int(current_user["id"]),),
        ).fetchall()
    }
    blacklisted = {
        row["comp_signature"]
        for row in conn.execute(
            """
            SELECT comp_signature
            FROM osta_import_blacklist
            WHERE user_id = ?
            """,
            (int(current_user["id"]),),
        ).fetchall()
    }

    candidates: list[dict] = []
    for item in parsed["competitions"]:
        comp = item["competition"]
        signature = osta_competition_signature(comp["date"], comp["name"], parsed["pid"])
        if comp["date"] in existing_dates or signature in blacklisted:
            continue
        candidates.append(
            {
                "name": comp["name"],
                "date": comp["date"],
                "race_count": len(item["results"]),
                "signature": signature,
                "pid": parsed["pid"],
            }
        )
    return candidates


def detect_osta_updates_for_user(conn: sqlite3.Connection, current_user: sqlite3.Row) -> dict:
    config = get_osta_monitor_config(conn, int(current_user["id"]))
    if not config:
        search_name = default_osta_search_name(current_user["skater_name"])
        season = default_ssr_season()
        pid = ""
    else:
        search_name = default_osta_search_name(config["search_name"] or current_user["skater_name"])
        try:
            season = normalize_osta_season(config["season"] or default_ssr_season())
        except ValueError:
            season = default_ssr_season()
        pid = (config["pid"] or "").strip()

    try:
        parsed = extract_osta_results(search_name, season, pid)
    except ValueError as exc:
        if not config:
            return {
                "configured": False,
                "available": [],
                "error_message": "",
                "search_name": "",
                "season": "",
                "pid": "",
            }
        return {
            "configured": True,
            "available": [],
            "error_message": f"Kon OSTA-check niet uitvoeren: {str(exc)}",
            "search_name": search_name,
            "season": season,
            "pid": pid,
        }

    upsert_osta_monitor_config(
        conn,
        int(current_user["id"]),
        search_name=search_name,
        season=season,
        pid=parsed["pid"],
    )

    return {
        "configured": True,
        "available": list_new_osta_competitions(conn, current_user, parsed),
        "error_message": "",
        "search_name": search_name,
        "season": season,
        "pid": parsed["pid"],
    }


def osta_fetch_soup(path: str, params: Optional[dict[str, object]] = None) -> BeautifulSoup:
    url = urljoin(OSTA_BASE, path)
    if params:
        query = urlencode({key: str(value) for key, value in params.items() if value not in (None, "")})
        if query:
            url = f"{url}?{query}"

    try:
        with urlopen(url, timeout=20) as resp:
            payload = resp.read()
    except HTTPError as exc:
        raise ValueError(f"OSTA fout: HTTP {exc.code}.") from exc
    except URLError as exc:
        raise ValueError("Kon OSTA niet bereiken.") from exc

    return BeautifulSoup(payload, "html.parser")


class OstaMultipleMatchesError(ValueError):
    def __init__(self, query_name: str, candidates: list[dict]):
        self.query_name = query_name
        self.candidates = candidates
        super().__init__(f"Meerdere OSTA profielen gevonden voor '{query_name}'.")


def osta_lookup_candidates(search_name: str) -> list[dict]:
    query_name = default_osta_search_name(search_name)
    if not query_name:
        raise ValueError("Voer een naam in voor OSTA.")

    soup = osta_fetch_soup("index.php", {"ZoekStr": query_name})

    candidates: list[dict] = []
    seen_pids: set[str] = set()

    for row in soup.select("table.naam tr"):
        cells = row.find_all("td")
        if len(cells) < 1:
            continue
        profile_link = cells[0].select_one("a[href]")
        if not profile_link:
            continue

        href_value = profile_link.get("href", "")
        parsed_href = urlparse(urljoin(OSTA_BASE, href_value))
        pid_value = parse_qs(parsed_href.query).get("pid", [""])[0].strip()
        if not pid_value or pid_value in seen_pids:
            continue
        seen_pids.add(pid_value)

        candidates.append(
            {
                "pid": pid_value,
                "name": profile_link.get_text(" ", strip=True),
                "category": cells[1].get_text(" ", strip=True) if len(cells) > 1 else "",
                "seasons": cells[2].get_text(" ", strip=True) if len(cells) > 2 else "",
                "club": cells[3].get_text(" ", strip=True) if len(cells) > 3 else "",
            }
        )

    if candidates:
        return candidates

    pid_input = soup.select_one("form#tijden input[name='pid']")
    heading = soup.select_one("div#main h1")
    if not pid_input or not pid_input.get("value"):
        return []

    pid_value = pid_input["value"].strip()
    if not pid_value:
        return []
    return [
        {
            "pid": pid_value,
            "name": heading.get_text(" ", strip=True) if heading else query_name,
            "category": "",
            "seasons": "",
            "club": "",
        }
    ]


def osta_lookup_pid(search_name: str) -> tuple[str, str]:
    query_name = default_osta_search_name(search_name)
    candidates = osta_lookup_candidates(query_name)
    if not candidates:
        raise ValueError(f"Geen OSTA resultaat gevonden voor '{query_name}'.")
    if len(candidates) > 1:
        raise OstaMultipleMatchesError(query_name, candidates)

    selected = candidates[0]
    return selected["pid"], selected["name"] or query_name


def osta_build_laps_csv(detail_soup: BeautifulSoup) -> Optional[str]:
    rows = detail_soup.select("table.rit tr")
    if not rows:
        return None

    lap_values: list[float] = []
    for row in rows[1:]:
        cells = row.find_all("td")
        if len(cells) < 3:
            continue
        cumulative_text = cells[1].get_text(" ", strip=True)
        lap_text = cells[2].get_text(" ", strip=True)

        source_value = lap_text or cumulative_text
        if not source_value:
            continue

        try:
            lap_ms = parse_time_to_ms(source_value)
        except ValueError:
            continue
        lap_values.append(lap_ms / 1000.0)

    if not lap_values:
        return None
    return ",".join(f"{value:.2f}" for value in lap_values)


def osta_extract_competition_name(detail_soup: BeautifulSoup, fallback_name: str) -> str:
    info = detail_soup.select_one("p.wedinfo")
    if not info:
        return fallback_name

    text = info.get_text(" ", strip=True)
    match = re.match(r"^\d{4}-\d{2}-\d{2}\s+\d+\s+(.+)$", text)
    if match:
        return match.group(1).strip()
    return fallback_name


def extract_osta_results(search_name: str, season: str, pid: str = "") -> dict:
    season_value = normalize_osta_season(season)
    pid_value = (pid or "").strip()
    resolved_name = default_osta_search_name(search_name)
    if not pid_value:
        pid_value, resolved_name = osta_lookup_pid(search_name)

    soup = osta_fetch_soup(
        "index.php",
        {
            "pid": pid_value,
            "Seizoen": season_value,
            "perAfstand": 0,
        },
    )

    competition_groups: dict[tuple[str, str], dict] = {}
    seen_races: set[tuple[tuple[str, str], int, int]] = set()

    for row in soup.select("table.datum tr"):
        cells = row.find_all("td")
        if len(cells) < 6:
            continue

        date_text = cells[0].get_text(" ", strip=True)
        venue_code = cells[1].get_text(" ", strip=True) or None
        distance_text = cells[2].get_text(" ", strip=True)
        time_link = cells[3].find("a")
        competition_link = cells[5].find("a")

        if not time_link or not competition_link:
            continue

        try:
            comp_date = parse_date_any(date_text)
            distance_m = int(distance_text)
            total_time_ms = parse_time_to_ms(time_link.get_text(" ", strip=True))
        except (ValueError, TypeError):
            continue

        competition_name = competition_link.get_text(" ", strip=True)
        detail_href = time_link.get("href", "")
        detail_soup = osta_fetch_soup(detail_href)
        laps_csv = osta_build_laps_csv(detail_soup)
        detail_competition_name = osta_extract_competition_name(detail_soup, competition_name)
        competition_key = (comp_date, detail_competition_name)
        race_key = (competition_key, distance_m, total_time_ms)
        if race_key in seen_races:
            continue
        seen_races.add(race_key)

        competition = competition_groups.setdefault(
            competition_key,
            {
                "competition": {
                    "name": detail_competition_name,
                    "venue": normalize_osta_venue(venue_code),
                    "date": comp_date,
                    "source_pid": pid_value,
                },
                "results": [],
            },
        )
        competition["results"].append(
            {
                "distance_m": distance_m,
                "total_time_ms": total_time_ms,
                "laps_csv": laps_csv,
                "dnf": 0,
                "notes": source_note("OSTA", urljoin(OSTA_BASE, detail_href)),
                "update_notes": update_note("OSTA", urljoin(OSTA_BASE, detail_href)),
            }
        )

    competitions = [competition_groups[key] for key in sorted(competition_groups)]
    if not competitions:
        raise ValueError("Geen OSTA ritten gevonden voor deze naam en dit seizoen.")

    return {
        "pid": pid_value,
        "resolved_name": resolved_name,
        "competitions": competitions,
    }


def import_osta_competitions(
    conn: sqlite3.Connection,
    current_user: sqlite3.Row,
    parsed: dict,
    update_existing: bool,
    force_new_competition: bool = False,
) -> dict:
    imported_competitions = 0
    imported_races = 0
    updated_races = 0
    skipped_dates: list[str] = []

    for item in parsed["competitions"]:
        comp = item["competition"]
        comp_date = comp["date"]
        existing_competitions = conn.execute(
            """
            SELECT id, name, notes
                 , venue
            FROM competition
            WHERE owner_user_id = ? AND competition_date = ?
            ORDER BY id ASC
            """,
            (int(current_user["id"]), comp_date),
        ).fetchall()

        if existing_competitions and not update_existing and not force_new_competition:
            skipped_dates.append(comp_date)
            continue

        if existing_competitions and not force_new_competition:
            comp_id = int(existing_competitions[0]["id"])
            conn.execute(
                """
                UPDATE competition
                SET notes = ?, venue = ?
                WHERE id = ?
                """,
                (
                    append_note(
                        existing_competitions[0]["notes"],
                        update_note("OSTA", None),
                    ),
                    (
                        comp["venue"]
                        if not (existing_competitions[0]["venue"] or "").strip()
                        or (existing_competitions[0]["venue"] or "").strip().upper() in OSTA_VENUE_MAP
                        else existing_competitions[0]["venue"]
                    ),
                    comp_id,
                ),
            )
        else:
            source_pid_value = str(comp.get("source_pid") or parsed.get("pid") or "").strip()
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    comp["name"],
                    comp["venue"],
                    comp_date,
                    source_note(
                        "OSTA",
                        f"{OSTA_BASE}index.php?pid={quote(source_pid_value)}" if source_pid_value else None,
                    ),
                    now_iso(),
                    int(current_user["id"]),
                ),
            )
            comp_id = int(conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"])
            imported_competitions += 1

        for result in item["results"]:
            existing_race = conn.execute(
                """
                SELECT id, notes, laps_csv
                FROM race
                WHERE competition_id = ?
                  AND skater_id = ?
                  AND distance_m = ?
                  AND total_time_ms = ?
                ORDER BY id ASC
                LIMIT 1
                """,
                (
                    comp_id,
                    int(current_user["skater_id"]),
                    int(result["distance_m"]),
                    int(result["total_time_ms"]),
                ),
            ).fetchone()

            if existing_race:
                next_laps = result["laps_csv"] or existing_race["laps_csv"]
                next_notes = append_note(existing_race["notes"], result.get("update_notes") or result["notes"])
                conn.execute(
                    """
                    UPDATE race
                    SET laps_csv = ?, notes = ?
                    WHERE id = ?
                    """,
                    (
                        next_laps,
                        next_notes,
                        int(existing_race["id"]),
                    ),
                )
                updated_races += 1
                continue

            conn.execute(
                """
                INSERT INTO race(
                  competition_id, skater_id, distance_m, category, class_name, lane, opponent,
                  total_time_ms, laps_csv, dnf, notes, created_at
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    comp_id,
                    int(current_user["skater_id"]),
                    int(result["distance_m"]),
                    None,
                    None,
                    None,
                    None,
                    int(result["total_time_ms"]),
                    result["laps_csv"],
                    int(result.get("dnf", 0)),
                    result["notes"],
                    now_iso(),
                ),
            )
            imported_races += 1

    return {
        "imported_competitions": imported_competitions,
        "imported_races": imported_races,
        "updated_races": updated_races,
        "skipped_dates": skipped_dates,
    }


def race_is_duplicate(existing_rows: list[sqlite3.Row], result: dict) -> bool:
    for row in existing_rows:
        same_total = row["total_time_ms"] == result.get("total_time_ms")
        same_lane = (row["lane"] or "").strip().lower() == (result.get("lane") or "").strip().lower()
        same_opponent = (row["opponent"] or "").strip().lower() == (result.get("opponent") or "").strip().lower()
        same_laps = (row["laps_csv"] or "").strip() == (result.get("laps_csv") or "").strip()
        same_dnf = int(row["dnf"] or 0) == int(result.get("dnf") or 0)
        if same_total and same_lane and same_opponent and same_laps and same_dnf:
            return True
    return False


def import_generic_competitions(
    conn: sqlite3.Connection,
    current_user: sqlite3.Row,
    competitions: list[dict],
    force_new_competition: bool = False,
) -> dict:
    imported_competitions = 0
    imported_races = 0
    updated_races = 0

    for item in competitions:
        comp = item.get("competition") or {}
        results = item.get("results") or []
        comp_date = (comp.get("date") or "").strip()
        if not comp_date:
            continue

        existing_comp = conn.execute(
            """
            SELECT id, name, venue, notes
            FROM competition
            WHERE owner_user_id = ? AND competition_date = ?
            ORDER BY CASE WHEN LOWER(name) = LOWER(?) THEN 0 ELSE 1 END, id ASC
            LIMIT 1
            """,
            (
                int(current_user["id"]),
                comp_date,
                (comp.get("name") or "").strip(),
            ),
        ).fetchone()

        if existing_comp and not force_new_competition:
            comp_id = int(existing_comp["id"])
            next_venue = existing_comp["venue"] or comp.get("venue")
            next_notes = append_note(existing_comp["notes"], (comp.get("notes") or "").strip())
            conn.execute(
                """
                UPDATE competition
                SET venue = ?, notes = ?
                WHERE id = ?
                """,
                (next_venue, next_notes, comp_id),
            )
        else:
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    comp.get("name") or "Geimporteerde wedstrijd",
                    comp.get("venue"),
                    comp_date,
                    comp.get("notes"),
                    now_iso(),
                    int(current_user["id"]),
                ),
            )
            comp_id = int(conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"])
            imported_competitions += 1

        for result in results:
            existing_races = conn.execute(
                """
                SELECT id, total_time_ms, lane, opponent, laps_csv, dnf
                FROM race
                WHERE competition_id = ? AND skater_id = ? AND distance_m = ?
                """,
                (
                    comp_id,
                    int(current_user["skater_id"]),
                    int(result["distance_m"]),
                ),
            ).fetchall()
            if race_is_duplicate(existing_races, result):
                updated_races += 1
                continue

            conn.execute(
                """
                INSERT INTO race(
                  competition_id, skater_id, distance_m, category, class_name, lane, opponent,
                  total_time_ms, laps_csv, dnf, notes, created_at
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    comp_id,
                    int(current_user["skater_id"]),
                    int(result["distance_m"]),
                    result.get("category"),
                    result.get("class_name"),
                    (result.get("lane") or "").strip() or None,
                    (result.get("opponent") or "").strip() or None,
                    result.get("total_time_ms"),
                    (result.get("laps_csv") or "").strip() or None,
                    int(result.get("dnf", 0)),
                    result.get("notes"),
                    now_iso(),
                ),
            )
            imported_races += 1

    return {
        "imported_competitions": imported_competitions,
        "imported_races": imported_races,
        "updated_races": updated_races,
        "skipped_dates": [],
    }


def default_ssr_season() -> str:
    return current_season_bounds()[0][:4]


def split_name_parts(full_name: str) -> tuple[str, str]:
    parts = [part for part in (full_name or "").strip().split() if part]
    if not parts:
        return "", ""
    if len(parts) == 1:
        return parts[0], ""
    return parts[0], " ".join(parts[1:])


def parse_ssr_time_value(raw_time: Optional[str]) -> tuple[Optional[int], int]:
    value = (raw_time or "").strip()
    if not value:
        return None, 0

    upper = value.upper()
    if upper in {"DNF", "DNS", "DSQ", "DQ", "WDR", "NC"}:
        return None, 1

    normalized = value.replace(",", ".")
    if normalized.count(".") >= 2 and ":" not in normalized:
        first_dot = normalized.find(".")
        normalized = f"{normalized[:first_dot]}:{normalized[first_dot + 1:]}"

    try:
        return parse_time_to_ms(normalized), 0
    except ValueError:
        return None, 0


def ssr_api_get(path: str, params: dict[str, object]) -> dict:
    query = urlencode({key: str(value) for key, value in params.items() if value not in (None, "")})
    url = f"{SSR_API_BASE}/{path}"
    if query:
        url = f"{url}?{query}"

    try:
        with urlopen(url, timeout=20) as resp:
            return json.load(resp)
    except HTTPError as exc:
        raise ValueError(f"SpeedSkatingResults API fout: HTTP {exc.code}.") from exc
    except URLError as exc:
        raise ValueError("Kon SpeedSkatingResults niet bereiken.") from exc
    except json.JSONDecodeError as exc:
        raise ValueError("Kon antwoord van SpeedSkatingResults niet lezen.") from exc


def ssr_lookup_skater_id(given_name: str, family_name: str) -> dict:
    given_value = (given_name or "").strip()
    family_value = (family_name or "").strip()
    if not given_value or not family_value:
        raise ValueError("Vul zowel voornaam als achternaam in voor een SSR lookup.")

    query = urlencode({"givenname": given_value, "familyname": family_value})
    url = f"{SSR_XML_API_BASE}/skater_lookup.php?{query}"

    try:
        with urlopen(url, timeout=20) as resp:
            payload = resp.read()
    except HTTPError as exc:
        raise ValueError(f"SpeedSkatingResults lookup fout: HTTP {exc.code}.") from exc
    except URLError as exc:
        raise ValueError("Kon SpeedSkatingResults lookup niet bereiken.") from exc

    try:
        root = ElementTree.fromstring(payload)
    except ElementTree.ParseError as exc:
        raise ValueError("Kon XML-antwoord van SpeedSkatingResults niet lezen.") from exc

    candidates = []
    for skater in root.findall(".//skater"):
        skater_id = (skater.findtext("id") or "").strip()
        if not skater_id:
            continue
        candidates.append(
            {
                "id": skater_id,
                "givenname": (skater.findtext("givenname") or "").strip(),
                "familyname": (skater.findtext("familyname") or "").strip(),
                "country": (skater.findtext("country") or "").strip(),
                "gender": (skater.findtext("gender") or "").strip(),
                "category": (skater.findtext("category") or "").strip(),
            }
        )

    if not candidates:
        raise ValueError("Geen SSR schaatser gevonden met deze naam.")
    if len(candidates) > 1:
        labels = ", ".join(
            f"{item['givenname']} {item['familyname']} ({item['country'] or '-'}, id {item['id']})"
            for item in candidates[:5]
        )
        raise ValueError(f"Meerdere SSR schaatsers gevonden: {labels}")

    return candidates[0]


def ssr_competition_key(item: dict) -> tuple[str, str]:
    date_value = (item.get("date") or "").strip()
    link_value = (item.get("link") or "").strip()
    event_id = ""
    if link_value:
        parsed = urlparse(link_value)
        event_id = parse_qs(parsed.query).get("e", [""])[0]
    if event_id:
        return date_value, event_id
    return date_value, f"{(item.get('name') or '').strip()}|{(item.get('location') or '').strip()}"


def extract_ssr_results_for_skater(skater_id: str, season: str) -> dict:
    season_value = (season or "").strip()
    if not re.fullmatch(r"\d{4}", season_value):
        raise ValueError("Seizoen moet een startjaar zijn, bijvoorbeeld 2025.")

    skater_value = (skater_id or "").strip()
    if not re.fullmatch(r"\d+", skater_value):
        raise ValueError("Gebruik een numerieke SpeedSkatingResults skater-id.")

    grouped: dict[tuple[str, str], dict] = {}
    seen_races: set[tuple[tuple[str, str], int, Optional[int], int]] = set()

    for distance in SSR_DISTANCES:
        payload = ssr_api_get(
            "skater_results.php",
            {"skater": skater_value, "season": season_value, "distance": distance},
        )
        if isinstance(payload, list):
            items = payload
        elif isinstance(payload, dict):
            items = payload.get("results") or payload.get("data") or []
        else:
            items = []
        if not isinstance(items, list):
            continue

        for item in items:
            date_raw = (item.get("date") or "").strip()
            if not date_raw:
                continue
            try:
                comp_date = parse_date_any(date_raw)
            except ValueError:
                continue
            comp_key = ssr_competition_key(item)
            competition = grouped.setdefault(
                comp_key,
                {
                    "competition": {
                        "name": (item.get("name") or "SpeedSkatingResults import").strip(),
                        "venue": (item.get("location") or "").strip() or None,
                        "date": comp_date,
                        "source_link": (item.get("link") or "").strip() or None,
                        "notes": source_note("SpeedSkatingResults", item.get("link") or ""),
                    },
                    "results": [],
                },
            )

            try:
                distance_value = int(item.get("distance", distance))
            except (TypeError, ValueError):
                distance_value = distance
            total_time_ms, dnf = parse_ssr_time_value(item.get("time"))
            race_key = (comp_key, distance_value, total_time_ms, dnf)
            if race_key in seen_races:
                continue
            seen_races.add(race_key)

            competition["results"].append(
                {
                    "distance_m": distance_value,
                    "total_time_ms": total_time_ms,
                    "laps_csv": None,
                    "dnf": dnf,
                    "notes": source_note("SpeedSkatingResults", item.get("link") or ""),
                }
            )

    competitions = [grouped[key] for key in sorted(grouped, key=lambda value: value[0])]
    competitions = [item for item in competitions if item["results"]]
    if not competitions:
        raise ValueError("Geen SpeedSkatingResults-uitslagen gevonden voor deze schaatser en dit seizoen.")

    return {"competitions": competitions}


def render_import_page(
    request: Request,
    current_user: sqlite3.Row,
    **ctx,
) -> HTMLResponse:
    monitor_search_name = default_osta_search_name(current_user["skater_name"])
    monitor_pid = ""
    monitor_season = default_ssr_season()
    with db() as conn:
        monitor_config = get_osta_monitor_config(conn, int(current_user["id"]))
        blacklist_items = list_blacklist_items(conn, int(current_user["id"]))
        if monitor_config:
            monitor_search_name = default_osta_search_name(monitor_config["search_name"] or monitor_search_name)
            monitor_pid = (monitor_config["pid"] or "").strip()
            try:
                monitor_season = normalize_osta_season(monitor_config["season"] or monitor_season)
            except ValueError:
                monitor_season = default_ssr_season()

    default_given_name, default_family_name = split_name_parts(current_user["skater_name"])
    defaults = {
        "upload_owner_name": current_user["skater_name"],
        "ssr_skater_id": "",
        "ssr_given_name": default_given_name,
        "ssr_family_name": default_family_name,
        "ssr_season": default_ssr_season(),
        "osta_search_name": monitor_search_name,
        "osta_pid": monitor_pid,
        "osta_season": monitor_season,
        "osta_error_message": "",
        "osta_success_message": "",
        "ssr_error_message": "",
        "ssr_success_message": "",
        "pdf_error_message": "",
        "pdf_success_message": "",
        "blacklist_items": blacklist_items,
        "blacklist_error_message": "",
        "blacklist_success_message": "",
        "fmt_date": fmt_date_ymd_to_dmy,
    }
    defaults.update(ctx)
    return render(request, "import.html", **defaults)


def render_osta_profile_select_page(
    request: Request,
    current_user: sqlite3.Row,
    search_name: str,
    season: str,
    candidates: list[dict],
    error_message: str = "",
) -> HTMLResponse:
    return render(
        request,
        "import_osta_profiles.html",
        upload_owner_name=current_user["skater_name"],
        osta_search_name=search_name,
        osta_season=season,
        osta_candidates=candidates,
        osta_profile_error_message=error_message,
    )


@app.get("/import", response_class=HTMLResponse)
def import_page(request: Request):
    current_user = require_user(request)
    return render_import_page(request, current_user)


@app.get("/import/pdf")
def import_pdf_redirect() -> RedirectResponse:
    return RedirectResponse("/import", status_code=308)


@app.post("/import/pdf")
def import_pdf_post(
    request: Request,
    pdf_file: UploadFile = File(...),
):
    current_user = require_user(request)
    filename = (pdf_file.filename or "").strip()
    if not filename.lower().endswith(".pdf"):
        return render_import_page(
            request,
            current_user,
            pdf_error_message="Upload een PDF-bestand.",
        )

    payload = pdf_file.file.read()
    if not payload:
        return render_import_page(
            request,
            current_user,
            pdf_error_message="Leeg bestand geupload.",
        )

    try:
        parsed = extract_pdf_results_for_skater(payload, current_user["skater_name"], filename)
    except ValueError as exc:
        return render_import_page(
            request,
            current_user,
            pdf_error_message=str(exc),
        )

    with db() as conn:
        items = build_import_preview_items(
            conn,
            current_user,
            "pdf",
            parsed,
            source_meta={"filename": filename},
        )
        if not items:
            return render_import_page(
                request,
                current_user,
                pdf_error_message="Geen importeerbare gegevens gevonden in deze PDF.",
            )
        batch_id = create_import_preview_batch(
            conn,
            current_user,
            "pdf",
            source_meta={"filename": filename},
            items=items,
        )
        batch = load_import_preview_batch(conn, current_user, batch_id)

    if not batch:
        return render_import_page(
            request,
            current_user,
            pdf_error_message="Kon de import-preview niet voorbereiden.",
        )
    return render_import_preview_page(request, current_user, batch)


@app.post("/import/speedskatingresults")
def import_speedskatingresults_post(
    request: Request,
    ssr_skater_id: str = Form(""),
    ssr_given_name: str = Form(""),
    ssr_family_name: str = Form(""),
    ssr_season: str = Form(""),
):
    current_user = require_user(request)
    season_value = ssr_season.strip() or default_ssr_season()
    skater_id_value = ssr_skater_id.strip()

    if not skater_id_value:
        try:
            lookup = ssr_lookup_skater_id(ssr_given_name, ssr_family_name)
            skater_id_value = lookup["id"]
        except ValueError as exc:
            return render_import_page(
                request,
                current_user,
                ssr_skater_id=ssr_skater_id,
                ssr_given_name=ssr_given_name,
                ssr_family_name=ssr_family_name,
                ssr_season=season_value,
                ssr_error_message=str(exc),
            )

    try:
        parsed = extract_ssr_results_for_skater(skater_id_value, season_value)
    except ValueError as exc:
        return render_import_page(
            request,
            current_user,
            ssr_skater_id=skater_id_value,
            ssr_given_name=ssr_given_name,
            ssr_family_name=ssr_family_name,
            ssr_season=season_value,
            ssr_error_message=str(exc),
        )

    with db() as conn:
        items = build_import_preview_items(
            conn,
            current_user,
            "ssr",
            parsed,
            source_meta={"ssr_skater_id": skater_id_value},
        )
        if not items:
            return render_import_page(
                request,
                current_user,
                ssr_skater_id=skater_id_value,
                ssr_given_name=ssr_given_name,
                ssr_family_name=ssr_family_name,
                ssr_season=season_value,
                ssr_error_message="Geen importeerbare SSR-data gevonden.",
            )
        batch_id = create_import_preview_batch(
            conn,
            current_user,
            "ssr",
            source_meta={
                "ssr_skater_id": skater_id_value,
                "ssr_given_name": ssr_given_name,
                "ssr_family_name": ssr_family_name,
                "ssr_season": season_value,
            },
            items=items,
        )
        batch = load_import_preview_batch(conn, current_user, batch_id)

    if not batch:
        return render_import_page(
            request,
            current_user,
            ssr_skater_id=skater_id_value,
            ssr_given_name=ssr_given_name,
            ssr_family_name=ssr_family_name,
            ssr_season=season_value,
            ssr_error_message="Kon de import-preview niet voorbereiden.",
        )
    return render_import_preview_page(request, current_user, batch)


@app.post("/import/osta")
def import_osta_post(
    request: Request,
    osta_search_name: str = Form(""),
    osta_pid: str = Form(""),
    osta_season: str = Form(""),
):
    current_user = require_user(request)
    search_name_value = osta_search_name.strip() or default_osta_search_name(current_user["skater_name"])
    pid_value = osta_pid.strip()

    try:
        season_value = normalize_osta_season(osta_season)
        if not pid_value:
            candidates = osta_lookup_candidates(search_name_value)
            if not candidates:
                raise ValueError(f"Geen OSTA resultaat gevonden voor '{search_name_value}'.")
            if len(candidates) > 1:
                return render_osta_profile_select_page(
                    request,
                    current_user,
                    search_name=search_name_value,
                    season=season_value,
                    candidates=candidates,
                )
            pid_value = candidates[0]["pid"]

        parsed = extract_osta_results(search_name_value, season_value, pid_value)
    except ValueError as exc:
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_pid=pid_value,
            osta_season=osta_season.strip() or default_ssr_season(),
            osta_error_message=str(exc),
        )

    with db() as conn:
        items = build_import_preview_items(
            conn,
            current_user,
            "osta",
            parsed,
            source_meta={"pid": parsed["pid"]},
        )
        if not items:
            return render_import_page(
                request,
                current_user,
                osta_search_name=search_name_value,
                osta_pid=parsed["pid"],
                osta_season=season_value,
                osta_error_message="Geen importeerbare OSTA-data gevonden.",
            )
        upsert_osta_monitor_config(
            conn,
            int(current_user["id"]),
            search_name=search_name_value,
            season=season_value,
            pid=parsed["pid"],
        )
        batch_id = create_import_preview_batch(
            conn,
            current_user,
            "osta",
            source_meta={
                "pid": parsed["pid"],
                "search_name": search_name_value,
                "season": season_value,
            },
            items=items,
        )
        batch = load_import_preview_batch(conn, current_user, batch_id)

    if not batch:
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_pid=parsed["pid"],
            osta_season=season_value,
            osta_error_message="Kon de import-preview niet voorbereiden.",
        )
    return render_import_preview_page(request, current_user, batch)


@app.post("/import/osta/select")
def import_osta_select_post(
    request: Request,
    osta_search_name: str = Form(""),
    osta_season: str = Form(""),
    selected_pids: list[str] = Form([]),
):
    current_user = require_user(request)
    search_name_value = osta_search_name.strip() or default_osta_search_name(current_user["skater_name"])

    try:
        season_value = normalize_osta_season(osta_season)
    except ValueError as exc:
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_season=osta_season.strip() or default_ssr_season(),
            osta_error_message=str(exc),
        )

    selected_pid_values = []
    seen_pid_values = set()
    for pid in selected_pids:
        pid_value = (pid or "").strip()
        if not pid_value or pid_value in seen_pid_values:
            continue
        seen_pid_values.add(pid_value)
        selected_pid_values.append(pid_value)

    if not selected_pid_values:
        try:
            candidates = osta_lookup_candidates(search_name_value)
        except ValueError as exc:
            return render_import_page(
                request,
                current_user,
                osta_search_name=search_name_value,
                osta_season=season_value,
                osta_error_message=str(exc),
            )
        return render_osta_profile_select_page(
            request,
            current_user,
            search_name=search_name_value,
            season=season_value,
            candidates=candidates,
            error_message="Selecteer minimaal een OSTA-profiel.",
        )

    combined_competitions: list[dict] = []
    for pid_value in selected_pid_values:
        try:
            parsed = extract_osta_results(search_name_value, season_value, pid_value)
        except ValueError as exc:
            return render_import_page(
                request,
                current_user,
                osta_search_name=search_name_value,
                osta_season=season_value,
                osta_error_message=f"OSTA profiel {pid_value}: {str(exc)}",
            )
        combined_competitions.extend(parsed.get("competitions") or [])

    if not combined_competitions:
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_season=season_value,
            osta_error_message="Geen importeerbare OSTA-data gevonden voor de gekozen profielen.",
        )

    with db() as conn:
        items = build_import_preview_items(
            conn,
            current_user,
            "osta",
            {"competitions": combined_competitions},
            source_meta={"pid": selected_pid_values[0]},
        )
        if not items:
            return render_import_page(
                request,
                current_user,
                osta_search_name=search_name_value,
                osta_season=season_value,
                osta_error_message="Geen importeerbare OSTA-data gevonden.",
            )
        upsert_osta_monitor_config(
            conn,
            int(current_user["id"]),
            search_name=search_name_value,
            season=season_value,
            pid=selected_pid_values[0],
        )
        batch_id = create_import_preview_batch(
            conn,
            current_user,
            "osta",
            source_meta={
                "pid": selected_pid_values[0],
                "pids": selected_pid_values,
                "search_name": search_name_value,
                "season": season_value,
            },
            items=items,
        )
        batch = load_import_preview_batch(conn, current_user, batch_id)

    if not batch:
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_season=season_value,
            osta_error_message="Kon de import-preview niet voorbereiden.",
        )
    return render_import_preview_page(request, current_user, batch)


@app.post("/import/preview/commit")
def import_preview_commit_post(
    request: Request,
    batch_id: str = Form(""),
    action: str = Form("import"),
    selected_races: list[str] = Form([]),
):
    current_user = require_user(request)
    batch_id_value = (batch_id or "").strip()
    if not batch_id_value:
        return render_import_page(request, current_user, osta_error_message="Import-preview niet gevonden.")

    with db() as conn:
        batch = load_import_preview_batch(conn, current_user, batch_id_value)
        if not batch:
            return render_import_page(request, current_user, osta_error_message="Import-preview is verlopen.")

        if action == "cancel":
            delete_import_preview_batch(conn, batch_id_value, int(current_user["id"]))
            return render_import_page(request, current_user, osta_success_message="Import geannuleerd.")

        selected_keys = {(value or "").strip() for value in selected_races if (value or "").strip()}
        selected_items: list[dict] = []
        for item in (batch.get("items") or []):
            comp_id = str(item.get("id"))
            filtered_results: list[dict] = []
            for idx, result in enumerate(item.get("results") or []):
                race_key = f"{comp_id}:{idx}"
                if race_key in selected_keys:
                    filtered_results.append(result)
            if filtered_results:
                selected_items.append(
                    {
                        "id": comp_id,
                        "competition": item["competition"],
                        "results": filtered_results,
                    }
                )

        if not selected_items:
            return render_import_preview_page(
                request,
                current_user,
                batch,
                error_message="Selecteer minimaal één rit om te importeren.",
            )

        selected_signatures = {
            (item.get("signature") or "").strip()
            for item in selected_items
            if (item.get("signature") or "").strip()
        }
        if selected_signatures:
            placeholders = ",".join("?" for _ in selected_signatures)
            conn.execute(
                f"""
                DELETE FROM osta_import_blacklist
                WHERE user_id = ? AND comp_signature IN ({placeholders})
                """,
                (int(current_user["id"]), *sorted(selected_signatures)),
            )

        source = (batch.get("source") or "").strip().lower()
        force_add_mode = action == "add"
        if source == "osta":
            summary = import_osta_competitions(
                conn,
                current_user,
                {
                    "pid": str((batch.get("meta") or {}).get("pid") or ""),
                    "competitions": [
                        {"competition": item["competition"], "results": item["results"]}
                        for item in selected_items
                    ],
                },
                update_existing=not force_add_mode,
                force_new_competition=force_add_mode,
            )
            success_message = (
                f"{summary['imported_competitions']} wedstrijden aangemaakt, "
                f"{summary['imported_races']} ritten geimporteerd en "
                f"{summary['updated_races']} bestaande ritten bijgewerkt."
            )
            if force_add_mode:
                success_message = (
                    f"{summary['imported_competitions']} wedstrijden aangemaakt en "
                    f"{summary['imported_races']} ritten toegevoegd als nieuwe wedstrijddata."
                )
            context_key = "osta_success_message"
        else:
            summary = import_generic_competitions(
                conn,
                current_user,
                [
                    {"competition": item["competition"], "results": item["results"]}
                    for item in selected_items
                ],
                force_new_competition=force_add_mode,
            )
            if force_add_mode:
                success_message = (
                    f"{summary['imported_competitions']} wedstrijden aangemaakt en "
                    f"{summary['imported_races']} ritten toegevoegd als nieuwe wedstrijddata."
                )
            else:
                success_message = (
                    f"{summary['imported_competitions']} wedstrijden aangemaakt, "
                    f"{summary['imported_races']} ritten geimporteerd en "
                    f"{summary['updated_races']} dubbelen overgeslagen."
                )
            context_key = "ssr_success_message" if source == "ssr" else "pdf_success_message"

        delete_import_preview_batch(conn, batch_id_value, int(current_user["id"]))

    if int(summary["imported_races"]) == 0 and int(summary["imported_competitions"]) == 0:
        if source == "ssr":
            return render_import_page(request, current_user, ssr_error_message="Geen nieuwe data geimporteerd.")
        if source == "pdf":
            return render_import_page(request, current_user, pdf_error_message="Geen nieuwe data geimporteerd.")
        return render_import_page(request, current_user, osta_error_message="Geen nieuwe data geimporteerd.")

    if context_key == "ssr_success_message":
        return render_import_page(request, current_user, ssr_success_message=success_message)
    if context_key == "pdf_success_message":
        return render_import_page(request, current_user, pdf_success_message=success_message)
    return render_import_page(request, current_user, osta_success_message=success_message)


@app.post("/import/blacklist/remove")
def import_blacklist_remove_post(
    request: Request,
    selected_signatures: list[str] = Form([]),
):
    current_user = require_user(request)
    signatures = sorted({(value or "").strip() for value in selected_signatures if (value or "").strip()})
    if not signatures:
        return render_import_page(
            request,
            current_user,
            blacklist_error_message="Selecteer minimaal één item om van de blacklist te halen.",
        )

    deleted = 0
    with db() as conn:
        for signature in signatures:
            result = conn.execute(
                """
                DELETE FROM osta_import_blacklist
                WHERE user_id = ? AND comp_signature = ?
                """,
                (int(current_user["id"]), signature),
            )
            deleted += int(result.rowcount or 0)

    if deleted == 0:
        return render_import_page(
            request,
            current_user,
            blacklist_error_message="Geen blacklist-items verwijderd.",
        )
    if deleted == 1:
        message = "1 item van de blacklist gehaald."
    else:
        message = f"{deleted} items van de blacklist gehaald."
    return render_import_page(
        request,
        current_user,
        blacklist_success_message=message,
    )


@app.post("/osta/detection/ignore")
def osta_detection_ignore_post(
    request: Request,
    comp_signature: str = Form(""),
    comp_name: str = Form(""),
    comp_date: str = Form(""),
    pid: str = Form(""),
    race_count: str = Form("0"),
):
    current_user = require_user(request)
    signature_value = (comp_signature or "").strip()
    name_value = (comp_name or "").strip()
    date_value = (comp_date or "").strip()
    pid_value = (pid or "").strip()
    try:
        parsed_date = parse_date_any(date_value)
    except ValueError:
        return RedirectResponse("/?osta_notice=ignore_error", status_code=303)

    if not signature_value:
        signature_value = osta_competition_signature(parsed_date, name_value, pid_value)

    race_count_value = 0
    try:
        race_count_value = max(0, int(race_count or "0"))
    except ValueError:
        race_count_value = 0

    with db() as conn:
        conn.execute(
            """
            INSERT OR IGNORE INTO osta_import_blacklist(
              user_id, comp_signature, comp_name, comp_date, pid, race_count, created_at
            )
            VALUES(?,?,?,?,?,?,?)
            """,
            (
                int(current_user["id"]),
                signature_value,
                name_value or "OSTA competitie",
                parsed_date,
                pid_value or None,
                race_count_value,
                now_iso(),
            ),
        )

    return RedirectResponse("/?osta_notice=ignored", status_code=303)


@app.post("/osta/detection/import")
def osta_detection_import_post(request: Request):
    current_user = require_user(request)

    with db() as conn:
        config = get_osta_monitor_config(conn, int(current_user["id"]))
        if not config:
            return RedirectResponse("/?osta_notice=import_error", status_code=303)

        search_name = default_osta_search_name(config["search_name"] or current_user["skater_name"])
        try:
            season = normalize_osta_season(config["season"] or default_ssr_season())
        except ValueError:
            season = default_ssr_season()
        pid = (config["pid"] or "").strip()

        try:
            parsed = extract_osta_results(search_name, season, pid)
        except ValueError:
            return RedirectResponse("/?osta_notice=import_error", status_code=303)

        candidates = list_new_osta_competitions(conn, current_user, parsed)
        if not candidates:
            return RedirectResponse("/?osta_notice=nonew", status_code=303)

        candidate_signatures = {item["signature"] for item in candidates}
        filtered_competitions = []
        for item in parsed["competitions"]:
            comp = item["competition"]
            signature = osta_competition_signature(comp["date"], comp["name"], parsed["pid"])
            if signature in candidate_signatures:
                filtered_competitions.append(item)

        summary = import_osta_competitions(
            conn,
            current_user,
            {"pid": parsed["pid"], "competitions": filtered_competitions},
            update_existing=False,
        )
        upsert_osta_monitor_config(
            conn,
            int(current_user["id"]),
            search_name=search_name,
            season=season,
            pid=parsed["pid"],
        )

    imported_total = int(summary["imported_competitions"]) + int(summary["updated_races"])
    if imported_total == 0 and int(summary["imported_races"]) == 0:
        return RedirectResponse("/?osta_notice=nonew", status_code=303)
    return RedirectResponse(
        f"/?osta_notice=imported&osta_count={int(summary['imported_races'])}",
        status_code=303,
    )


def ensure_runtime_ready() -> None:
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    init_db()
    bootstrap_admin_user()


def cli_list_users() -> int:
    ensure_runtime_ready()
    with db() as conn:
        rows = conn.execute(
            """
            SELECT u.username, u.is_admin, s.name AS skater_name
            FROM user u
            JOIN skater s ON s.id = u.skater_id
            ORDER BY LOWER(u.username)
            """
        ).fetchall()
    for row in rows:
        role = "admin" if int(row["is_admin"]) == 1 else "user"
        print(f"{row['username']}\t{role}\t{row['skater_name']}")
    return 0


def cli_set_password(username: str, password: Optional[str]) -> int:
    ensure_runtime_ready()
    new_password = password
    if not new_password:
        first = getpass.getpass("New password: ")
        second = getpass.getpass("Confirm password: ")
        if first != second:
            print("Passwords do not match.")
            return 1
        new_password = first
    if len(new_password) < 8:
        print("Password must be at least 8 characters.")
        return 1

    with db() as conn:
        user = get_user_by_username(conn, username)
        if not user:
            print(f"User '{username}' not found.")
            return 1
        set_user_password(conn, int(user["id"]), new_password)

    print(f"Password updated for '{username}'.")
    return 0


def cli_create_user(username: str, skater_name: str, password: Optional[str], is_admin: bool) -> int:
    ensure_runtime_ready()
    new_password = password
    if not new_password:
        first = getpass.getpass("Password: ")
        second = getpass.getpass("Confirm password: ")
        if first != second:
            print("Passwords do not match.")
            return 1
        new_password = first
    if len(new_password) < 8:
        print("Password must be at least 8 characters.")
        return 1

    with db() as conn:
        if get_user_by_username(conn, username):
            print(f"User '{username}' already exists.")
            return 1
        existing_skater = conn.execute("SELECT id FROM skater WHERE name = ?", (skater_name,)).fetchone()
        if existing_skater:
            existing_owner = conn.execute(
                "SELECT username FROM user WHERE skater_id = ?",
                (int(existing_skater["id"]),),
            ).fetchone()
            if existing_owner:
                print(f"Skater '{skater_name}' is already linked to '{existing_owner['username']}'.")
                return 1
            skater_id = int(existing_skater["id"])
        else:
            skater_id = get_or_create_skater(conn, skater_name)

        conn.execute(
            """
            INSERT INTO user(username, password_hash, skater_id, is_admin, created_at, updated_at)
            VALUES(?,?,?,?,?,?)
            """,
            (
                username,
                hash_password(new_password),
                skater_id,
                1 if is_admin else 0,
                now_iso(),
                now_iso(),
            ),
        )

    print(f"Created user '{username}'.")
    return 0


def build_cli_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="SkateStats administration")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_users_parser = subparsers.add_parser("list-users", help="List configured users")
    list_users_parser.set_defaults(handler=lambda args: cli_list_users())

    set_password_parser = subparsers.add_parser("set-password", help="Set or reset a user's password")
    set_password_parser.add_argument("username")
    set_password_parser.add_argument("password", nargs="?")
    set_password_parser.set_defaults(handler=lambda args: cli_set_password(args.username, args.password))

    create_user_parser = subparsers.add_parser("create-user", help="Create a new user")
    create_user_parser.add_argument("username")
    create_user_parser.add_argument("skater_name")
    create_user_parser.add_argument("password", nargs="?")
    create_user_parser.add_argument("--admin", action="store_true", dest="is_admin")
    create_user_parser.set_defaults(
        handler=lambda args: cli_create_user(args.username, args.skater_name, args.password, args.is_admin)
    )

    return parser


if __name__ == "__main__":
    parser = build_cli_parser()
    cli_args = parser.parse_args()
    raise SystemExit(cli_args.handler(cli_args))
