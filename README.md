# SkateStats

SkateStats is a self-hosted web app for tracking and analyzing long-track speed skating results per skater account.

## What SkateStats does

- Stores competitions and races in a local SQLite database.
- Tracks split times, total times, pace/fade, and distance-specific history.
- Lets each user define goals per distance and compare results against those targets.
- Supports race and competition management in the UI (create, edit, delete).
- Imports results from:
  - SpeedSkatingResults (SSR)
  - OSTA
  - Uploaded PDF result sheets
- Supports multi-user accounts with admin tooling.
- Includes account export/import for backup and restore.

## Tech stack

- FastAPI + Jinja templates
- SQLite (`/data/skatestats.sqlite`)
- Docker Compose deployment

## Basic onboarding setup

### 1. Prerequisites

- Docker + Docker Compose
- A free local port (default: `8090`)

### 2. Configure environment

Create or update `.env` in the project root:

```env
SKATESTATS_DB=/data/skatestats.sqlite
SKATESTATS_TITLE=SkateStats
SKATESTATS_OWNER_NAME=Your Name
SKATESTATS_ADMIN_USERNAME=admin
SKATESTATS_SESSION_SECRET=replace-with-a-long-random-secret
```

Generate a secret on Linux/macOS:

```bash
openssl rand -hex 32
```

Generate a secret in PowerShell:

```powershell
[guid]::NewGuid().ToString("N") + [guid]::NewGuid().ToString("N")
```

### 3. Start SkateStats

From the project root:

```bash
docker compose up -d --build
```

Open the app:

`http://localhost:8090`

### 4. Set the admin password (required before login)

An admin user is created automatically on startup, but without a password.
Set it once:

```bash
docker compose exec skatestats python /app/main.py set-password admin
```

Then log in with:

- Username: `admin` (or your `SKATESTATS_ADMIN_USERNAME`)
- Password: the one you just set

### 5. First-use checklist

- Open `Account settings` and verify username/skater profile.
- Add your first competition and race manually, or use `Import`.
- Configure goals per distance in `Goals`.

## Useful admin CLI commands

Run inside the container:

```bash
docker compose exec skatestats python /app/main.py list-users
docker compose exec skatestats python /app/main.py create-user <username> "<Skater Name>" --admin
docker compose exec skatestats python /app/main.py set-password <username>
```

## Local (non-Docker) run

```bash
cd app
pip install -r requirements.txt
uvicorn main:app --host 0.0.0.0 --port 8000
```

If running locally, make sure `SKATESTATS_DB` points to a writable path.
