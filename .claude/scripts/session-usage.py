#!/usr/bin/env python3
"""Session-usage tooling for the /coordinate-phase loop.

Two subcommands:

  limits   Query the live subscription rate-limit state (the same endpoint
           Claude Code's /usage screen reads): 5-hour-window and weekly
           utilization percentages with reset times. Use BEFORE a
           multi-dispatch fan-out and between landings, to avoid being
           interrupted by session limits mid-dispatch.

  tokens   Sum token usage from local Claude Code transcripts, per model,
           over a trailing window (default 5 h). Covers main sessions AND
           subagent transcripts; dedupes by API message id (a message is
           logged once per content block, so raw line sums overcount).

Config-dir resolution (both subcommands): --config-dir, else
$CLAUDE_CONFIG_DIR, else ~/.claude. The OAuth token for `limits` is read
from <config-dir>/.credentials.json when present, else from the macOS
Keychain: the item is "Claude Code-credentials" for the default ~/.claude
config dir, and "Claude Code-credentials-<sha256(config-dir)[:8]>" for a
non-default one — accounts are per config dir, so passing the wrong
--config-dir silently reports a DIFFERENT account's limits. The token is
never printed.

Examples:
  session-usage.py limits
  session-usage.py tokens --hours 5
  session-usage.py tokens --days 1 --by-session
"""

import argparse
import hashlib
import json
import os
import subprocess
import sys
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

USAGE_URL = "https://api.anthropic.com/api/oauth/usage"


def config_dir(args) -> Path:
    return Path(args.config_dir or os.environ.get("CLAUDE_CONFIG_DIR", "~/.claude")).expanduser()


# ---------------------------------------------------------------- limits

def keychain_service(cfg: Path) -> str:
    """Claude Code keys credentials per config dir: the default ~/.claude
    uses the bare service name; any other dir gets a sha256-prefix suffix."""
    if cfg == Path("~/.claude").expanduser():
        return "Claude Code-credentials"
    return "Claude Code-credentials-" + hashlib.sha256(str(cfg).encode()).hexdigest()[:8]


def oauth_token(cfg: Path) -> str:
    cred_file = cfg / ".credentials.json"
    raw = None
    if cred_file.is_file():
        raw = cred_file.read_text()
    else:
        service = keychain_service(cfg)
        try:
            raw = subprocess.run(
                ["security", "find-generic-password", "-s", service, "-w"],
                capture_output=True, text=True, check=True,
            ).stdout
        except (OSError, subprocess.CalledProcessError):
            sys.exit(f"no .credentials.json under {cfg} and no Keychain item '{service}'")
    try:
        return json.loads(raw)["claudeAiOauth"]["accessToken"]
    except (json.JSONDecodeError, KeyError):
        sys.exit("credentials found but no claudeAiOauth.accessToken field")


def cmd_limits(args):
    req = urllib.request.Request(USAGE_URL, headers={
        "Authorization": f"Bearer {oauth_token(config_dir(args))}",
        "anthropic-beta": "oauth-2025-04-20",
    })
    with urllib.request.urlopen(req, timeout=20) as resp:
        data = json.load(resp)

    now = datetime.now(timezone.utc)
    rows = data.get("limits") or []
    if not rows:
        print(json.dumps(data, indent=2))
        return
    hdr = f"{'limit':<14}{'used':>7}  {'severity':<10}{'resets in':<20}resets at (UTC)"
    print(hdr)
    print("-" * len(hdr))
    worst = 0
    for lim in rows:
        pct = lim.get("percent")
        worst = max(worst, pct or 0)
        resets = lim.get("resets_at")
        left = ""
        if resets:
            dt = datetime.fromisoformat(resets)
            left = str(dt - now).split(".")[0]
            resets = dt.strftime("%Y-%m-%d %H:%M")
        print(f"{lim.get('kind', '?'):<14}{pct if pct is not None else '?':>6}%  "
              f"{lim.get('severity', '?'):<10}{left:<20}{resets or ''}")
    extra = data.get("extra_usage") or {}
    print(f"\nextra usage credits: {'enabled' if extra.get('is_enabled') else 'disabled'}")
    if worst >= 80:
        print("WARNING: a limit is above 80% — stagger dispatches rather than fanning out.")


# ---------------------------------------------------------------- tokens

def iter_transcripts(projects_dir: Path):
    for proj in sorted(projects_dir.iterdir()):
        if not proj.is_dir():
            continue
        for f in proj.glob("*.jsonl"):
            yield proj.name, "main", f
        for f in proj.glob("*/subagents/agent-*.jsonl"):
            yield proj.name, "subagent", f


def collect(cfg: Path, since: datetime):
    projects_dir = cfg / "projects"
    if not projects_dir.is_dir():
        sys.exit(f"no projects dir under {cfg}")
    since_ts = since.timestamp()
    seen_ids = set()
    rows = []
    for proj, kind, f in iter_transcripts(projects_dir):
        try:
            if f.stat().st_mtime < since_ts:
                continue  # untouched since window start; nothing newer inside
        except OSError:
            continue
        try:
            with open(f, errors="replace") as fh:
                for line in fh:
                    if '"usage"' not in line:
                        continue
                    try:
                        d = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if d.get("type") != "assistant":
                        continue
                    ts = d.get("timestamp")
                    if not ts:
                        continue
                    if datetime.fromisoformat(ts.replace("Z", "+00:00")) < since:
                        continue
                    m = d.get("message", {})
                    u = m.get("usage")
                    if not u:
                        continue
                    mid = m.get("id") or d.get("uuid")
                    if mid in seen_ids:
                        continue
                    seen_ids.add(mid)
                    rows.append((proj, kind, f.name, m.get("model", "?"), u))
        except OSError:
            continue
    return rows


def cmd_tokens(args):
    window = timedelta(days=args.days) if args.days else timedelta(hours=args.hours)
    since = datetime.now(timezone.utc) - window
    rows = collect(config_dir(args), since)

    per_model, per_file = {}, {}
    for proj, kind, fname, model, u in rows:
        vals = (1, u.get("input_tokens", 0), u.get("cache_creation_input_tokens", 0),
                u.get("cache_read_input_tokens", 0), u.get("output_tokens", 0))
        for key, table in ((model, per_model), ((proj, kind, fname), per_file)):
            t = table.setdefault(key, [0] * 5)
            for i, v in enumerate(vals):
                t[i] += v

    print(f"window: last {window} (since {since.strftime('%Y-%m-%d %H:%M')}Z), "
          f"{len(rows)} deduped messages\n")
    hdr = f"{'model':<28}{'msgs':>6}{'input':>12}{'cache-wr':>12}{'cache-rd':>14}{'output':>12}"
    print(hdr)
    print("-" * len(hdr))
    for model in sorted(per_model, key=lambda k: -per_model[k][4]):
        n, inp, cw, cr, out = per_model[model]
        print(f"{model:<28}{n:>6}{inp:>12,}{cw:>12,}{cr:>14,}{out:>12,}")

    if args.by_session:
        print()
        hdr2 = f"{'session (project / kind / file)':<76}{'msgs':>6}{'output':>12}"
        print(hdr2)
        print("-" * len(hdr2))
        for key in sorted(per_file, key=lambda k: -per_file[k][4]):
            proj, kind, name = key
            label = f"{proj[-38:]} / {kind} / {name[:26]}"
            n, _, _, _, out = per_file[key]
            print(f"{label:<76}{n:>6}{out:>12,}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config-dir", default=None,
                    help="Claude Code config dir (default: $CLAUDE_CONFIG_DIR or ~/.claude)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("limits", help="live 5h/weekly limit utilization (OAuth endpoint)")
    tp = sub.add_parser("tokens", help="local transcript token sums per model")
    tp.add_argument("--hours", type=float, default=5.0, help="trailing window in hours (default 5)")
    tp.add_argument("--days", type=float, default=None, help="trailing window in days (overrides --hours)")
    tp.add_argument("--by-session", action="store_true", help="also break down by session file")
    args = ap.parse_args()
    (cmd_limits if args.cmd == "limits" else cmd_tokens)(args)


if __name__ == "__main__":
    main()
