import io
import os
import re
import sqlite3
from datetime import date, datetime, timedelta
from statistics import mean
from typing import List, Optional, Tuple

from fastapi import FastAPI, File, Form, UploadFile
from fastapi.responses import HTMLResponse, RedirectResponse
from fastapi.staticfiles import StaticFiles
from jinja2 import Environment, FileSystemLoader, select_autoescape

APP_TITLE = os.getenv("SKATESTATS_TITLE", "SkateStats")
DB_PATH = os.getenv("SKATESTATS_DB", "/data/skatestats.sqlite")
OWNER_NAME = os.getenv("SKATESTATS_OWNER_NAME", "Remco Land").strip() or "Remco Land"


def norm_name(s: str) -> str:
    s = s.strip().lower()
    s = re.sub(r"\s+", " ", s)
    return s


OWNER_NORM = norm_name(OWNER_NAME)

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

            CREATE INDEX IF NOT EXISTS idx_race_competition ON race(competition_id);
            CREATE INDEX IF NOT EXISTS idx_race_skater ON race(skater_id);
            CREATE INDEX IF NOT EXISTS idx_race_distance ON race(distance_m);
            """
        )


@app.on_event("startup")
def _startup():
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    init_db()
    with db() as conn:
        conn.execute("INSERT OR IGNORE INTO skater(name) VALUES(?)", (OWNER_NAME,))


def render(template_name: str, **ctx) -> HTMLResponse:
    tpl = templates_env.get_template(template_name)
    html = tpl.render(app_title=APP_TITLE, owner_name=OWNER_NAME, **ctx)
    return HTMLResponse(html)


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
    total_seconds = ms / 1000.0
    minutes = int(total_seconds // 60)
    seconds = total_seconds - (minutes * 60)
    if minutes > 0:
        return f"{minutes}:{seconds:05.2f}"
    return f"{seconds:.2f}"


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
        }

    avg_400 = sum(p400) / len(p400)
    first = p400[0]
    last = p400[-1]
    fade = last - first

    return {
        "segment_count": len(laps),
        "opening_m": opening_split_m(distance_m),
        "avg_400": avg_400,
        "first_400eq": first,
        "last_400eq": last,
        "fade_400eq": fade,
    }


def fmt_sec(value: Optional[float]) -> str:
    if value is None:
        return "-"
    return fmt_ms(int(round(value * 1000)))


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


@app.get("/", response_class=HTMLResponse)
def home(
    trend_period: str = "season",
    trend_date_from: str = "",
    trend_date_to: str = "",
):
    with db() as conn:
        competition_count = conn.execute("SELECT COUNT(*) AS count FROM competition").fetchone()["count"]
        comps = conn.execute(
            "SELECT id, name, venue, competition_date FROM competition ORDER BY competition_date DESC LIMIT 10"
        ).fetchall()
        recent_races = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf,
                   c.name AS competition_name, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ?
            ORDER BY c.competition_date DESC, r.id DESC
            LIMIT 20
            """,
            (OWNER_NAME,),
        ).fetchall()
        all_races = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf, r.lane,
                   c.name AS competition_name, c.competition_date, c.venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ? AND r.total_time_ms IS NOT NULL
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (OWNER_NAME,),
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
    season: str = "",
    distance_m: str = "",
):
    with db() as conn:
        rows = conn.execute(
            """
            SELECT r.id, r.competition_id, r.distance_m, r.total_time_ms, r.laps_csv, r.dnf,
                   c.name AS competition_name, c.competition_date, c.venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (OWNER_NAME,),
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

    return render(
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


@app.get("/competitions", response_class=HTMLResponse)
def competitions(
    venue: str = "",
    date_from: str = "",
    date_to: str = "",
):
    filters = ["1 = 1"]
    params: list[object] = []

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
        filters = ["1 = 1"]
        params = []
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
            WHERE venue IS NOT NULL AND TRIM(venue) != ''
            ORDER BY venue
            """
        ).fetchall()
    return render(
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
def competition_new(error: str = ""):
    return render("competition_new.html", error=error)


@app.post("/competitions/new")
def competitions_new(
    name: str = Form(...),
    venue: str = Form(""),
    competition_date: str = Form(...),
    notes: str = Form(""),
):
    try:
        comp_date = parse_date_any(competition_date)
    except ValueError:
        return RedirectResponse("/competitions/new?error=date", status_code=303)

    with db() as conn:
        conn.execute(
            """
            INSERT INTO competition(name, venue, competition_date, notes, created_at)
            VALUES(?,?,?,?,?)
            """,
            (
                name.strip(),
                venue.strip() or None,
                comp_date,
                notes.strip() or None,
                datetime.utcnow().isoformat(),
            ),
        )

    return RedirectResponse("/competitions", status_code=303)


@app.get("/competitions/{competition_id}/edit", response_class=HTMLResponse)
def competition_edit(competition_id: int, error: str = ""):
    with db() as conn:
        comp = conn.execute("SELECT * FROM competition WHERE id = ?", (competition_id,)).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

    return render("competition_edit.html", comp=comp, error=error, fmt_date=fmt_date_ymd_to_dmy)


@app.post("/competitions/{competition_id}/edit")
def competition_edit_post(
    competition_id: int,
    name: str = Form(...),
    venue: str = Form(""),
    competition_date: str = Form(...),
    notes: str = Form(""),
):
    try:
        comp_date = parse_date_any(competition_date)
    except ValueError:
        return RedirectResponse(f"/competitions/{competition_id}/edit?error=date", status_code=303)

    with db() as conn:
        comp = conn.execute("SELECT id FROM competition WHERE id = ?", (competition_id,)).fetchone()
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
def competition_detail(competition_id: int):
    with db() as conn:
        comp = conn.execute("SELECT * FROM competition WHERE id = ?", (competition_id,)).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

        races = conn.execute(
            """
            SELECT r.*
            FROM race r
            JOIN skater s ON s.id = r.skater_id
            WHERE r.competition_id = ? AND s.name = ?
            ORDER BY r.distance_m ASC, r.total_time_ms ASC
            """,
            (competition_id, OWNER_NAME),
        ).fetchall()

    races_enriched = []
    for r in races:
        laps = laps_from_csv(r["laps_csv"])
        metrics = compute_race_metrics(laps, r["distance_m"])
        races_enriched.append((r, metrics))

    return render(
        "competition_detail.html",
        comp=comp,
        races=races_enriched,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/competitions/{competition_id}/delete")
def competition_delete(competition_id: int):
    with db() as conn:
        comp = conn.execute("SELECT id FROM competition WHERE id = ?", (competition_id,)).fetchone()
        if not comp:
            return HTMLResponse("Competition not found", status_code=404)

        conn.execute("DELETE FROM competition WHERE id = ?", (competition_id,))

    return RedirectResponse("/competitions", status_code=303)


@app.get("/races", response_class=HTMLResponse)
def races(
    distance_m: Optional[str] = None,
    lane: str = "",
    venue: str = "",
    date_from: str = "",
    date_to: str = "",
):
    filters = ["s.name = ?"]
    params: list[object] = [OWNER_NAME]

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
        params = [OWNER_NAME]
        filters = ["s.name = ?"]
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
            JOIN skater s ON s.id = r.skater_id
            WHERE {where_sql}
            ORDER BY c.competition_date DESC, r.distance_m ASC, r.total_time_ms ASC, r.id DESC
            """,
            params,
        ).fetchall()
        lane_options = conn.execute(
            """
            SELECT DISTINCT lane
            FROM race r
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ? AND lane IS NOT NULL AND TRIM(lane) != ''
            ORDER BY lane
            """,
            (OWNER_NAME,),
        ).fetchall()
        venue_options = conn.execute(
            """
            SELECT DISTINCT c.venue AS venue
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ? AND c.venue IS NOT NULL AND TRIM(c.venue) != ''
            ORDER BY c.venue
            """,
            (OWNER_NAME,),
        ).fetchall()
        all_owner_races = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (OWNER_NAME,),
        ).fetchall()

    pr_progress = build_pr_progress(all_owner_races)
    return render(
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
def race_new(competition_id: Optional[int] = None):
    with db() as conn:
        comps = conn.execute(
            """
            SELECT id, name, competition_date
            FROM competition
            ORDER BY competition_date DESC, id DESC
            LIMIT 10
            """
        ).fetchall()
        if competition_id and not any(c["id"] == competition_id for c in comps):
            selected_comp = conn.execute(
                "SELECT id, name, competition_date FROM competition WHERE id = ?",
                (competition_id,),
            ).fetchone()
            if selected_comp:
                comps = [selected_comp, *comps]
    return render(
        "race_new.html",
        comps=comps,
        selected_competition_id=competition_id,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/races/new")
def race_new_post(
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
                INSERT INTO competition(name, venue, competition_date, notes, created_at)
                VALUES(?,?,?,?,?)
                """,
                (
                    new_competition_name.strip(),
                    new_competition_venue.strip() or None,
                    comp_date,
                    "Created via new time form",
                    datetime.utcnow().isoformat(),
                ),
            )
            competition_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]

    laps_ms, total_ms, err = parse_laps_to_ms(laps)
    if err:
        return RedirectResponse("/races/new?error=laps", status_code=303)

    laps_csv = ",".join([f"{(ms/1000.0):.2f}" for ms in laps_ms]) if laps_ms else None

    with db() as conn:
        sk_id = conn.execute("SELECT id FROM skater WHERE name = ?", (OWNER_NAME,)).fetchone()["id"]
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
                sk_id,
                int(distance_m),
                None,
                None,
                lane.strip() or None,
                opponent.strip() or None,
                total_ms,
                laps_csv,
                dnf_val,
                notes.strip() or None,
                datetime.utcnow().isoformat(),
            ),
        )
        race_id = cur.lastrowid

    return RedirectResponse(f"/races/{race_id}", status_code=303)


@app.get("/races/{race_id}", response_class=HTMLResponse)
def race_detail(race_id: int):
    with db() as conn:
        r = conn.execute(
            """
            SELECT r.*, c.name AS competition_name, c.venue, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE r.id = ? AND s.name = ?
            """,
            (race_id, OWNER_NAME),
        ).fetchone()
        history_rows = conn.execute(
            """
            SELECT r.id, r.distance_m, r.total_time_ms, r.dnf, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE s.name = ?
            ORDER BY c.competition_date ASC, r.id ASC
            """,
            (OWNER_NAME,),
        ).fetchall()

    if not r:
        return HTMLResponse("Race not found", status_code=404)

    laps = laps_from_csv(r["laps_csv"])
    metrics = compute_race_metrics(laps, r["distance_m"])
    split_chart = build_split_chart(laps)
    pr_progress = build_pr_progress(history_rows)
    pr_context = pr_progress.get(
        race_id,
        {"is_pr": False, "previous_pr_ms": None, "delta_vs_previous_pr_ms": None, "delta_abs_ms": None},
    )

    return render(
        "race_detail.html",
        race=r,
        laps=laps,
        metrics=metrics,
        split_chart=split_chart,
        pr_context=pr_context,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/races/{race_id}/delete")
def race_delete(race_id: int):
    with db() as conn:
        race = conn.execute(
            """
            SELECT r.id, r.competition_id
            FROM race r
            JOIN skater s ON s.id = r.skater_id
            WHERE r.id = ? AND s.name = ?
            """,
            (race_id, OWNER_NAME),
        ).fetchone()
        if not race:
            return HTMLResponse("Race not found", status_code=404)

        conn.execute("DELETE FROM race WHERE id = ?", (race_id,))

    return RedirectResponse(f"/competitions/{race['competition_id']}", status_code=303)


# -----------------------
# Edit race
# -----------------------

@app.get("/races/{race_id}/edit", response_class=HTMLResponse)
def race_edit(race_id: int):
    with db() as conn:
        r = conn.execute(
            """
            SELECT r.*, c.name AS competition_name, c.competition_date
            FROM race r
            JOIN competition c ON c.id = r.competition_id
            JOIN skater s ON s.id = r.skater_id
            WHERE r.id = ? AND s.name = ?
            """,
            (race_id, OWNER_NAME),
        ).fetchone()

        if not r:
            return HTMLResponse("Race not found", status_code=404)

        comps = conn.execute(
            "SELECT id, name, competition_date FROM competition ORDER BY competition_date DESC"
        ).fetchall()

    return render(
        "race_edit.html",
        race=r,
        comps=comps,
        fmt_ms=fmt_ms,
        fmt_date=fmt_date_ymd_to_dmy,
    )


@app.post("/races/{race_id}/edit")
def race_edit_post(
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
    competition_id = int(competition_id) if competition_id else None
    dnf_val = 1 if dnf == "on" else 0

    # Ensure this race belongs to owner
    with db() as conn:
        owns = conn.execute(
            """
            SELECT r.id
            FROM race r
            JOIN skater s ON s.id = r.skater_id
            WHERE r.id = ? AND s.name = ?
            """,
            (race_id, OWNER_NAME),
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
                INSERT INTO competition(name, venue, competition_date, notes, created_at)
                VALUES(?,?,?,?,?)
                """,
                (
                    new_competition_name.strip(),
                    new_competition_venue.strip() or None,
                    comp_date,
                    "Created via edit form",
                    datetime.utcnow().isoformat(),
                ),
            )
            competition_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]

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


@app.get("/import/pdf", response_class=HTMLResponse)
def import_pdf_page():
    return render(
        "import_pdf.html",
        upload_owner_name=OWNER_NAME,
        upload_competition_name="",
        upload_competition_date="",
        upload_competition_venue="",
    )


@app.post("/import/pdf")
async def import_pdf_post(
    owner_name: str = Form(...),
    competition_name: str = Form(""),
    competition_date: str = Form(""),
    competition_venue: str = Form(""),
    file: UploadFile = File(...),
):
    upload_owner_name = owner_name.strip() or OWNER_NAME
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
        return render(
            "import_pdf.html",
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
            "SELECT id FROM competition WHERE name = ? AND competition_date = ?",
            (comp["name"], comp["date"]),
        ).fetchone()

        if existing:
            comp_id = existing["id"]
        else:
            conn.execute(
                """
                INSERT INTO competition(name, venue, competition_date, notes, created_at)
                VALUES(?,?,?,?,?)
                """,
                (
                    comp["name"],
                    comp["venue"],
                    comp["date"],
                    f"Imported from PDF: {file.filename}",
                    datetime.utcnow().isoformat(),
                ),
            )
            comp_id = conn.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]

        conn.execute("INSERT OR IGNORE INTO skater(name) VALUES(?)", (upload_owner_name,))
        sk_id = conn.execute("SELECT id FROM skater WHERE name = ?", (upload_owner_name,)).fetchone()["id"]
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
                (comp_id, sk_id, int(r["distance_m"]), int(r["total_time_ms"])),
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
                    sk_id,
                    int(r["distance_m"]),
                    None,
                    None,
                    None,
                    None,
                    int(r["total_time_ms"]) if r["total_time_ms"] is not None else None,
                    r["laps_csv"],
                    int(r.get("dnf", 0)),
                    f"Imported from PDF line: {r['raw']}",
                    datetime.utcnow().isoformat(),
                ),
            )
            imported_count += 1

    if imported_count == 0:
        return render(
            "import_pdf.html",
            upload_owner_name=upload_owner_name,
            upload_competition_name=competition_name,
            upload_competition_date=competition_date,
            upload_competition_venue=competition_venue,
            error_message="Alle gevonden ritten stonden al in de database.",
        )

    return RedirectResponse(f"/competitions/{comp_id}", status_code=303)
