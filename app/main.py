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
from datetime import date, datetime, timedelta
from html import escape
from statistics import mean
from typing import List, Optional, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, unquote, urlencode, urljoin, urlparse
from urllib.request import urlopen
from xml.etree import ElementTree

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

            CREATE INDEX IF NOT EXISTS idx_race_competition ON race(competition_id);
            CREATE INDEX IF NOT EXISTS idx_race_skater ON race(skater_id);
            CREATE INDEX IF NOT EXISTS idx_race_distance ON race(distance_m);
            CREATE INDEX IF NOT EXISTS idx_goal_target_user_distance ON goal_target(user_id, distance_m);
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


def build_comparison_context(base_row: sqlite3.Row, compare_row: Optional[sqlite3.Row]) -> Optional[dict]:
    if compare_row is None:
        return None

    base_laps = laps_from_csv(base_row["laps_csv"])
    compare_laps = laps_from_csv(compare_row["laps_csv"])
    base_metrics = compute_race_metrics(base_laps, int(base_row["distance_m"]))
    compare_metrics = compute_race_metrics(compare_laps, int(compare_row["distance_m"]))
    base_per_400 = per400_times(base_laps, int(base_row["distance_m"]))
    compare_per_400 = per400_times(compare_laps, int(compare_row["distance_m"]))

    split_comparison: list[dict] = []
    row_count = max(len(base_laps), len(compare_laps))
    for idx in range(row_count):
        base_split = base_laps[idx] if idx < len(base_laps) else None
        compare_split = compare_laps[idx] if idx < len(compare_laps) else None
        base_400 = base_per_400[idx] if idx < len(base_per_400) else None
        compare_400 = compare_per_400[idx] if idx < len(compare_per_400) else None
        split_comparison.append(
            {
                "index": idx + 1,
                "base_split": base_split,
                "compare_split": compare_split,
                "split_delta_ms": None if base_split is None or compare_split is None else int(round((compare_split - base_split) * 1000)),
                "base_400": base_400,
                "compare_400": compare_400,
                "eq_delta_ms": None if base_400 is None or compare_400 is None else int(round((compare_400 - base_400) * 1000)),
            }
        )

    summary_items = [
        ("Totale tijd", base_row["total_time_ms"], compare_row["total_time_ms"]),
        ("Opening", round(base_laps[0] * 1000) if base_laps else None, round(compare_laps[0] * 1000) if compare_laps else None),
        (
            "Gem. 400-eq",
            round(base_metrics["avg_400"] * 1000) if base_metrics["avg_400"] is not None else None,
            round(compare_metrics["avg_400"] * 1000) if compare_metrics["avg_400"] is not None else None,
        ),
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

    return {
        "race": compare_row,
        "summary": summary,
        "splits": split_comparison,
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
):
    current_user = require_user(request)
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
        recent_races = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf,
                   c.name AS competition_name, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ?
            ORDER BY c.competition_date DESC, r.id DESC
            LIMIT 20
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()
        all_races = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf, r.lane,
                   c.name AS competition_name, c.competition_date, c.venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ? AND r.total_time_ms IS NOT NULL
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (int(current_user["skater_id"]), int(current_user["id"])),
        ).fetchall()

    best_times: dict[int, dict] = {}
    trend_rows: list[dict] = []
    races_by_distance: dict[int, list] = {}
    venue_counts: dict[str, int] = {}
    pr_progress = build_pr_progress(all_races)
    for race in all_races:
        races_by_distance.setdefault(race["distance_m"], []).append(race)
        if race["venue"]:
            venue_counts[race["venue"]] = venue_counts.get(race["venue"], 0) + 1
        if race["dnf"] != 1:
            current_best = best_times.get(race["distance_m"])
            if current_best is None or race["total_time_ms"] < current_best["total_time_ms"]:
                best_times[race["distance_m"]] = race

    favorite_venue = "-"
    if venue_counts:
        favorite_venue = sorted(venue_counts.items(), key=lambda item: (-item[1], item[0].lower()))[0][0]

    selected_trend_period = trend_period if trend_period in {"month", "season", "custom"} else "season"
    selected_trend_date_from = trend_date_from.strip()
    selected_trend_date_to = trend_date_to.strip()
    trend_error_message = ""
    pr_race_ids = collect_pr_race_ids(all_races)

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

    return render(
        request,
        "index.html",
        comps=comps,
        competition_count=competition_count,
        race_count=len(all_races),
        pr_count=len(pr_race_ids),
        favorite_venue=favorite_venue,
        best_times=[best_times[d] for d in sorted(best_times)],
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
        recent_races=[{**dict(row), **pr_progress.get(int(row["id"]), {})} for row in recent_races],
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
    pr_race_ids = collect_pr_race_ids(rows)

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

    timed_rows = [row for row in filtered_rows if row["total_time_ms"] is not None and row["dnf"] != 1]
    split_rows = [row for row in timed_rows if laps_from_csv(row["laps_csv"])]

    venues: dict[str, int] = {}
    for row in filtered_rows:
        if row["venue"]:
            venues[row["venue"]] = venues.get(row["venue"], 0) + 1

    favorite_venue = "-"
    if venues:
        favorite_venue = sorted(venues.items(), key=lambda item: (-item[1], item[0].lower()))[0][0]

    season_summaries = summarize_seasons(rows, pr_race_ids)
    distance_stats = build_distance_stats(filtered_rows, pr_race_ids)
    with db() as conn:
        goal_targets = get_goal_target_map(conn, int(current_user["id"]))

    for stat in distance_stats:
        goal_row = goal_targets.get(int(stat["distance_m"]))
        stat["goal"] = goal_row
        stat["goal_progress"] = build_goal_progress(goal_row, stat)

    return render(
        request,
        "stats.html",
        season_options=season_options,
        selected_season=selected_season,
        distance_options=distance_options,
        selected_distance=selected_distance,
        season_summaries=season_summaries,
        distance_stats=distance_stats,
        stats_summary={
            "competition_count": len({row["competition_id"] for row in filtered_rows}),
            "race_count": len(timed_rows),
            "distance_count": len({row["distance_m"] for row in timed_rows}),
            "split_count": len(split_rows),
            "pr_count": len([row for row in timed_rows if int(row["id"]) in pr_race_ids]),
            "favorite_venue": favorite_venue,
        },
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
    venue: str = "",
    date_from: str = "",
    date_to: str = "",
):
    current_user = require_user(request)
    filters = ["owner_user_id = ?"]
    params: list[object] = [int(current_user["id"])]

    selected_venue = venue.strip()
    selected_date_from = date_from.strip()
    selected_date_to = date_to.strip()

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
def race_detail(request: Request, race_id: int, compare_race_id: str = ""):
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
        comparison_candidates = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.laps_csv, r.dnf, c.name AS competition_name, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            WHERE r.skater_id = ? AND c.owner_user_id = ? AND r.distance_m = ? AND r.id != ?
            ORDER BY c.competition_date DESC, r.id DESC
            """,
            (int(current_user["skater_id"]), int(current_user["id"]), int(race_id if r is None else r["distance_m"]), race_id),
        ).fetchall() if r else []

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
    selected_compare_id = compare_race_id.strip()
    compare_row = None
    if selected_compare_id:
        try:
            compare_id_value = int(selected_compare_id)
        except ValueError:
            compare_id_value = 0
        compare_row = next((row for row in comparison_candidates if int(row["id"]) == compare_id_value), None)
        if compare_row is None:
            selected_compare_id = ""
    comparison = build_comparison_context(r, compare_row)

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
        comparison_candidates=comparison_candidates,
        selected_compare_id=selected_compare_id,
        comparison=comparison,
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
# PDF import
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


def osta_lookup_pid(search_name: str) -> tuple[str, str]:
    query_name = default_osta_search_name(search_name)
    if not query_name:
        raise ValueError("Voer een naam in voor OSTA.")

    soup = osta_fetch_soup("index.php", {"ZoekStr": query_name})
    pid_input = soup.select_one("form#tijden input[name='pid']")
    heading = soup.select_one("div#main h1")
    if not pid_input or not pid_input.get("value"):
        raise ValueError(f"Geen OSTA resultaat gevonden voor '{query_name}'.")

    resolved_name = heading.get_text(" ", strip=True) if heading else query_name
    return pid_input["value"].strip(), resolved_name


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

        if existing_competitions and not update_existing:
            skipped_dates.append(comp_date)
            continue

        if existing_competitions:
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
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    comp["name"],
                    comp["venue"],
                    comp_date,
                    source_note("OSTA", f"{OSTA_BASE}index.php?pid={quote(parsed['pid'])}"),
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


PDF_TIME_RE = re.compile(r"(\d+:\d{2}\.\d{2}|\d{1,2}\.\d{2})")
PDF_DISTANCE_RE = re.compile(r"(\d+)\s*meter", re.IGNORECASE)
PDF_LANE_RE = re.compile(r"^(wt|rd|gl|bl)\s+\d+\b", re.IGNORECASE)
PDF_SPLIT_LINE_RE = re.compile(
    r"^(\d+)m\s+(\d+:\d{2}\.\d{2}|\d{1,2}\.\d{2})\s+\((\d+:\d{2}\.\d{2}|\d{1,2}\.\d{2})\)$",
    re.IGNORECASE,
)


def parse_pdf_info_value(line: str) -> Optional[dict]:
    line = (line or "").strip()
    if not line:
        return None

    upper = line.upper()
    if upper in {"DNS", "DNF", "DSQ", "DQ", "WDR"}:
        return {"status": upper, "time": None}

    match = PDF_TIME_RE.search(line)
    if match:
        return {"status": None, "time": match.group(1)}

    return None


def parse_owner_result_from_heat(block_lines: list[str], owner_name: str, distance_m: int) -> Optional[dict]:
    owner_norm = norm_name(owner_name)
    header_idx = None
    info_idx = None

    for idx, line in enumerate(block_lines):
        line_norm = norm_name(line)
        if header_idx is None and "naam" in line_norm and "tijd" in line_norm:
            header_idx = idx
        if "info" == line_norm:
            info_idx = idx
            break

    block_text_norm = norm_name(" ".join(block_lines))
    if header_idx is None or owner_norm not in block_text_norm:
        return None

    entrant_lines: list[str] = []
    current_entrant = ""
    for line in block_lines[:header_idx]:
        if PDF_LANE_RE.match(line):
            if current_entrant:
                entrant_lines.append(current_entrant)
            current_entrant = line
            continue

        if current_entrant and "naam" not in norm_name(line) and "tijd" not in norm_name(line):
            current_entrant = f"{current_entrant} {line}".strip()

    if current_entrant:
        entrant_lines.append(current_entrant)

    owner_position = None
    for idx, line in enumerate(entrant_lines):
        if owner_norm in norm_name(line):
            owner_position = idx
            break

    info_values: list[dict] = []
    if info_idx is not None:
        for line in block_lines[info_idx + 1 :]:
            parsed_info = parse_pdf_info_value(line)
            if parsed_info:
                info_values.append(parsed_info)
            elif info_values:
                break

    owner_info = None
    if owner_position is not None and owner_position < len(info_values):
        owner_info = info_values[owner_position]
    elif len(info_values) == 1:
        owner_info = info_values[0]
    elif owner_position is None:
        timed_info_values = [item for item in info_values if item["time"]]
        if len(timed_info_values) == 1:
            owner_info = timed_info_values[0]

    owner_total_time = owner_info["time"] if owner_info else None
    owner_dnf = 1 if owner_info and owner_info["status"] in {"DNS", "DNF", "DSQ", "DQ", "WDR"} else 0

    if not owner_total_time:
        return None

    return {
        "distance_m": distance_m,
        "total_time_ms": parse_time_to_ms(owner_total_time),
        "laps_csv": None,
        "dnf": owner_dnf,
        "raw": " | ".join(block_lines),
    }


def extract_pdf_results_for_owner(
    pdf_bytes: bytes,
    owner_name: str,
    fallback_name: Optional[str] = None,
    fallback_date: Optional[str] = None,
    fallback_venue: Optional[str] = None,
    source_filename: Optional[str] = None,
) -> dict:
    # Requires pdfplumber in requirements.txt
    import pdfplumber

    owner_norm = norm_name(owner_name)
    results = []
    competition = {"name": None, "venue": None, "date": None}
    current_distance = None
    seen_results = set()

    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for page in pdf.pages:
            text = page.extract_text() or ""
            lines = [l.strip() for l in text.splitlines() if l.strip()]

            # Try parse header info (first relevant page)
            if not competition["name"] and len(lines) >= 1:
                competition["name"] = clean_competition_name(lines[0]) or lines[0]

                # Find a date in first lines
                for h in lines[:10]:
                    parsed_date = extract_date_from_text(h)
                    if parsed_date:
                        competition["date"] = parsed_date
                        break

                # Venue heuristic
                for h in lines[1:10]:
                    if "-" in h and len(h) < 80 and "uitslag" not in h.lower():
                        competition["venue"] = h
                        break

            current_block: list[str] = []

            def flush_current_block() -> None:
                nonlocal current_block
                if not current_block or current_distance is None:
                    current_block = []
                    return

                parsed_result = parse_owner_result_from_heat(current_block, owner_name, current_distance)
                current_block = []
                if not parsed_result:
                    return

                result_key = (
                    parsed_result["distance_m"],
                    parsed_result["total_time_ms"],
                    parsed_result["laps_csv"],
                )
                if result_key in seen_results:
                    return

                seen_results.add(result_key)
                results.append(parsed_result)

            for line in lines:
                distance_match = PDF_DISTANCE_RE.search(line)
                if "uitslag" in line.lower() and distance_match:
                    flush_current_block()
                    current_distance = int(distance_match.group(1))
                    continue

                if current_distance is None:
                    continue

                if PDF_LANE_RE.match(line) and current_block and any(
                    "naam" in norm_name(block_line) and "tijd" in norm_name(block_line)
                    for block_line in current_block
                ):
                    flush_current_block()

                current_block.append(line)

            flush_current_block()

    if not competition["date"] and source_filename:
        competition["date"] = extract_date_from_text(source_filename)

    if fallback_name:
        competition["name"] = fallback_name.strip()
    elif competition["name"]:
        competition["name"] = clean_competition_name(competition["name"])

    if fallback_date:
        competition["date"] = parse_date_any(fallback_date)

    if fallback_venue:
        competition["venue"] = fallback_venue.strip()

    if not competition["name"] or not competition["date"]:
        raise ValueError("Kon wedstrijdnaam/datum niet betrouwbaar uit PDF halen.")
    if not results:
        raise ValueError(f"Geen ritten gevonden voor '{owner_name}'.")

    return {"competition": competition, "results": results}


def render_import_page(
    request: Request,
    current_user: sqlite3.Row,
    **ctx,
) -> HTMLResponse:
    default_given_name, default_family_name = split_name_parts(current_user["skater_name"])
    defaults = {
        "upload_owner_name": current_user["skater_name"],
        "upload_competition_name": "",
        "upload_competition_date": "",
        "upload_competition_venue": "",
        "ssr_skater_id": "",
        "ssr_given_name": default_given_name,
        "ssr_family_name": default_family_name,
        "ssr_season": default_ssr_season(),
        "osta_search_name": default_osta_search_name(current_user["skater_name"]),
        "osta_pid": "",
        "osta_season": default_ssr_season(),
        "osta_update_existing": False,
        "osta_error_message": "",
        "osta_success_message": "",
        "error_message": "",
        "ssr_error_message": "",
        "ssr_success_message": "",
    }
    defaults.update(ctx)
    return render(request, "import_pdf.html", **defaults)


@app.get("/import/pdf", response_class=HTMLResponse)
def import_pdf_page(request: Request):
    current_user = require_user(request)
    return render_import_page(request, current_user)


@app.post("/import/pdf")
async def import_pdf_post(
    request: Request,
    competition_name: str = Form(""),
    competition_date: str = Form(""),
    competition_venue: str = Form(""),
    file: UploadFile = File(...),
):
    current_user = require_user(request)
    upload_owner_name = current_user["skater_name"]
    pdf_bytes = await file.read()
    try:
        parsed = extract_pdf_results_for_owner(
            pdf_bytes,
            upload_owner_name,
            fallback_name=competition_name.strip() or None,
            fallback_date=competition_date.strip() or None,
            fallback_venue=competition_venue.strip() or None,
            source_filename=file.filename,
        )
    except ValueError as exc:
        return render_import_page(
            request,
            current_user,
            upload_owner_name=upload_owner_name,
            upload_competition_name=competition_name,
            upload_competition_date=competition_date,
            upload_competition_venue=competition_venue,
            error_message=str(exc),
        )

    comp = parsed["competition"]
    items = parsed["results"]

    with db() as conn:
        existing = conn.execute(
            """
            SELECT id
            FROM competition
            WHERE owner_user_id = ? AND name = ? AND competition_date = ?
            """,
            (int(current_user["id"]), comp["name"], comp["date"]),
        ).fetchone()

        if existing:
            comp_id = existing["id"]
        else:
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    comp["name"],
                    comp["venue"],
                    comp["date"],
                    f"Imported from PDF: {file.filename}",
                    now_iso(),
                    int(current_user["id"]),
                ),
            )
            comp_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]

        imported_count = 0

        for r in items:
            if int(r["distance_m"]) <= 0:
                continue

            dupe = conn.execute(
                """
                SELECT 1 FROM race
                WHERE competition_id = ? AND skater_id = ? AND distance_m = ? AND total_time_ms = ?
                LIMIT 1
                """,
                (comp_id, int(current_user["skater_id"]), int(r["distance_m"]), int(r["total_time_ms"])),
            ).fetchone()
            if dupe:
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
                    int(r["distance_m"]),
                    None,
                    None,
                    None,
                    None,
                    int(r["total_time_ms"]) if r["total_time_ms"] is not None else None,
                    r["laps_csv"],
                    int(r.get("dnf", 0)),
                    f"Imported from PDF line: {r['raw']}",
                    now_iso(),
                ),
            )
            imported_count += 1

    if imported_count == 0:
        return render_import_page(
            request,
            current_user,
            upload_owner_name=upload_owner_name,
            upload_competition_name=competition_name,
            upload_competition_date=competition_date,
            upload_competition_venue=competition_venue,
            error_message="Alle gevonden ritten stonden al in de database.",
        )

    return RedirectResponse(f"/competitions/{comp_id}", status_code=303)


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

    imported_competitions = 0
    imported_races = 0
    skipped_dates: list[str] = []

    with db() as conn:
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

        for item in parsed["competitions"]:
            comp = item["competition"]
            results = item["results"]
            comp_date = comp["date"]
            if comp_date in existing_dates:
                skipped_dates.append(comp_date)
                continue

            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at, owner_user_id)
                VALUES(?,?,?,?,?,?)
                """,
                (
                    comp["name"],
                    comp["venue"],
                    comp_date,
                    source_note("SpeedSkatingResults", comp.get("source_link")),
                    now_iso(),
                    int(current_user["id"]),
                ),
            )
            comp_id = int(conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"])
            existing_dates.add(comp_date)
            imported_competitions += 1

            for result in results:
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
                        result["total_time_ms"],
                        result["laps_csv"],
                        int(result.get("dnf", 0)),
                        result["notes"],
                        now_iso(),
                    ),
                )
                imported_races += 1

    if imported_competitions == 0:
        return render_import_page(
            request,
            current_user,
            ssr_skater_id=skater_id_value,
            ssr_given_name=ssr_given_name,
            ssr_family_name=ssr_family_name,
            ssr_season=season_value,
            ssr_error_message=(
                "Geen nieuwe wedstrijden geimporteerd. Er bestaat al een wedstrijd op alle gevonden datums."
            ),
        )

    skipped_summary = ""
    if skipped_dates:
        unique_dates = ", ".join(fmt_date_ymd_to_dmy(value) for value in sorted(set(skipped_dates)))
        skipped_summary = f" Overgeslagen datums: {unique_dates}."

    return render_import_page(
        request,
        current_user,
        ssr_skater_id=skater_id_value,
        ssr_given_name=ssr_given_name,
        ssr_family_name=ssr_family_name,
        ssr_season=season_value,
        ssr_success_message=(
            f"{imported_competitions} wedstrijden en {imported_races} ritten geimporteerd voor SSR id {skater_id_value}.{skipped_summary}"
        ),
    )


@app.post("/import/osta")
def import_osta_post(
    request: Request,
    osta_search_name: str = Form(""),
    osta_pid: str = Form(""),
    osta_season: str = Form(""),
    osta_update_existing: Optional[str] = Form(None),
):
    current_user = require_user(request)
    search_name_value = osta_search_name.strip() or default_osta_search_name(current_user["skater_name"])
    pid_value = osta_pid.strip()

    try:
        season_value = normalize_osta_season(osta_season)
        parsed = extract_osta_results(search_name_value, season_value, pid_value)
    except ValueError as exc:
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_pid=pid_value,
            osta_season=osta_season.strip() or default_ssr_season(),
            osta_update_existing=osta_update_existing == "on",
            osta_error_message=str(exc),
        )

    with db() as conn:
        summary = import_osta_competitions(
            conn,
            current_user,
            parsed,
            update_existing=osta_update_existing == "on",
        )

    if (
        summary["imported_competitions"] == 0
        and summary["imported_races"] == 0
        and summary["updated_races"] == 0
    ):
        return render_import_page(
            request,
            current_user,
            osta_search_name=search_name_value,
            osta_pid=parsed["pid"],
            osta_season=season_value,
            osta_update_existing=osta_update_existing == "on",
            osta_error_message=(
                "Geen nieuwe OSTA-data verwerkt. Er bestaat al een wedstrijd op alle gevonden datums."
            ),
        )

    skipped_summary = ""
    if summary["skipped_dates"]:
        unique_dates = ", ".join(fmt_date_ymd_to_dmy(value) for value in sorted(set(summary["skipped_dates"])))
        skipped_summary = f" Overgeslagen datums: {unique_dates}."

    return render_import_page(
        request,
        current_user,
        osta_search_name=search_name_value,
        osta_pid=parsed["pid"],
        osta_season=season_value,
        osta_update_existing=osta_update_existing == "on",
        osta_success_message=(
            f"{summary['imported_competitions']} wedstrijden aangemaakt, "
            f"{summary['imported_races']} ritten geimporteerd en "
            f"{summary['updated_races']} bestaande ritten bijgewerkt voor OSTA pid {parsed['pid']}."
            f"{skipped_summary}"
        ),
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
