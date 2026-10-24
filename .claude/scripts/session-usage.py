#!/usr/bin/env python3
"""Session-usage tooling for the /coordinate-phase loop.

Three subcommands:

  limits   Query the live subscription rate-limit state (the same endpoint
           Claude Code's /usage screen reads): 5-hour-window and weekly
           utilization percentages with reset times. Use BEFORE a
           multi-dispatch fan-out and between landings, to avoid being
           interrupted by session limits mid-dispatch.

  tokens   Sum token usage from local Claude Code transcripts, per model,
           over a trailing window (default 5 h). Covers main sessions AND
           subagent transcripts; dedupes by API message id, taking the MAX
           over a message's blocks (a message is logged once per content
           block with CUMULATIVE usage, so raw line sums overcount and the
           first block undercounts subagent output ~4x — see
           notes/harness/incidents.md 2026-09-15).

  gates    Per transcript (default: subagents; --match narrows it), the
           wall-clock span and the time spent in lake gate calls (lake
           build / lint / lean, verify.sh), each call timed from its
           tool_use to its tool_result. With --since/--until (as for
           tokens) it measures one commit of a multi-commit dispatch.

Config-dir resolution (all subcommands): --config-dir, else
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
  session-usage.py gates --hours 3 --match agent-ap41a
"""

import argparse
import hashlib
import json
import os
import re
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


def collect(cfg: Path, since: datetime, until: datetime | None = None):
    projects_dir = cfg / "projects"
    if not projects_dir.is_dir():
        sys.exit(f"no projects dir under {cfg}")
    since_ts = since.timestamp()
    seen = {}  # message id -> index into rows; usage is cumulative across blocks, keep the max
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
                    t = datetime.fromisoformat(ts.replace("Z", "+00:00"))
                    if t < since or (until is not None and t > until):
                        continue
                    m = d.get("message", {})
                    u = m.get("usage")
                    if not u:
                        continue
                    mid = m.get("id") or d.get("uuid")
                    if mid in seen:
                        prev = rows[seen[mid]][4]
                        for k in ("input_tokens", "cache_creation_input_tokens",
                                  "cache_read_input_tokens", "output_tokens"):
                            prev[k] = max(prev.get(k) or 0, u.get(k) or 0)
                        continue
                    seen[mid] = len(rows)
                    rows.append((proj, kind, f.name, m.get("model", "?"), dict(u), t))
        except OSError:
            continue
    return rows


def window_bounds(args):
    """The window's start and end: a trailing --hours/--days window, or --since/--until."""
    window = timedelta(days=args.days) if args.days else timedelta(hours=args.hours)
    since = datetime.now(timezone.utc) - window
    if args.since:
        since = datetime.fromisoformat(args.since).astimezone(timezone.utc)
    until = datetime.fromisoformat(args.until).astimezone(timezone.utc) if args.until else None
    return since, until


def cmd_tokens(args):
    since, until = window_bounds(args)
    window = (until or datetime.now(timezone.utc)) - since
    rows = collect(config_dir(args), since, until)

    per_model, per_file, spans = {}, {}, {}
    for proj, kind, fname, model, u, t in rows:
        lo, hi = spans.get((proj, kind, fname), (t, t))
        spans[(proj, kind, fname)] = (min(lo, t), max(hi, t))
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
        n, inp, cw, cr, out = per_model[model][:5]
        print(f"{model:<28}{n:>6}{inp:>12,}{cw:>12,}{cr:>14,}{out:>12,}")

    if args.by_session:
        print()
        hdr2 = (f"{'session (project / kind / file)':<76}{'msgs':>6}{'cache-wr':>12}"
                f"{'cache-rd':>14}{'output':>12}  {'first-last (UTC)':<12}{'min':>6}")
        print(hdr2)
        print("-" * len(hdr2))
        for key in sorted(per_file, key=lambda k: -per_file[k][4]):
            proj, kind, name = key
            label = f"{proj[-38:]} / {kind} / {name[:26]}"
            n, _, cw, cr, out = per_file[key]
            lo, hi = spans[key]
            span = (hi - lo).total_seconds() / 60
            print(f"{label:<76}{n:>6}{cw:>12,}{cr:>14,}{out:>12,}  "
                  f"{lo:%H:%M}-{hi:%H:%M}  {span:>6.1f}")


# ---------------------------------------------------------------- gates

# A lake invocation at a command position (not inside a grep pattern or a heredoc line's text).
GATE_CLASSES = [
    ("lake build", re.compile(r"(?:^|[;&|(]\s*|\n\s*)(?:\w+=\S*\s+)*lake build\b")),
    ("lake lint", re.compile(r"(?:^|[;&|(]\s*|\n\s*)(?:\w+=\S*\s+)*lake lint\b")),
    ("lake lean", re.compile(r"(?:^|[;&|(]\s*|\n\s*)(?:\w+=\S*\s+)*lake (?:env )?lean\b")),
    ("verify.sh", re.compile(r"(?:^|[;&|(]\s*|\n\s*)\S*verify\.sh\b")),
]


def gate_class(cmd):
    hits = [(m.start(), name) for name, rx in GATE_CLASSES if (m := rx.search(cmd))]
    return min(hits)[1] if hits else None


def cmd_gates(args):
    since, until = window_bounds(args)
    projects_dir = config_dir(args) / "projects"
    for proj, kind, f in iter_transcripts(projects_dir):
        if args.match not in f.name or f.stat().st_mtime < since.timestamp():
            continue
        uses, ends, stamps, mcp = {}, {}, [], 0
        with open(f, errors="replace") as fh:
            for line in fh:
                try:
                    d = json.loads(line)
                except json.JSONDecodeError:
                    continue
                ts = d.get("timestamp")
                content = (d.get("message") or {}).get("content")
                if not ts or not isinstance(content, list):
                    continue
                t = datetime.fromisoformat(ts.replace("Z", "+00:00"))
                if t < since or (until is not None and t > until):
                    continue
                stamps.append(t)
                for c in content:
                    if c.get("type") == "tool_use":
                        mcp += c.get("name", "").startswith("mcp__lean")
                        if c.get("name") == "Bash":
                            uses[c["id"]] = (t, c.get("input", {}).get("command", ""))
                    elif c.get("type") == "tool_result" and c.get("tool_use_id") in uses:
                        ends[c["tool_use_id"]] = t
        if not stamps:
            continue
        totals = {}
        print(f"== {kind} / {f.name[:40]}")
        for i, (t0, cmd) in uses.items():
            cls = gate_class(cmd)
            if cls is None or i not in ends:
                continue
            dur = (ends[i] - t0).total_seconds()
            n, tot = totals.get(cls, (0, 0.0))
            totals[cls] = (n + 1, tot + dur)
            if args.verbose:
                print(f"  {dur:6.0f}s  {cls:<11} {cmd.splitlines()[0][:80]}")
        span = (max(stamps) - min(stamps)).total_seconds() / 60
        gate_min = sum(tot for _, tot in totals.values()) / 60
        print(f"  span {span:.1f} min ({min(stamps):%H:%M}-{max(stamps):%H:%M} UTC); "
              f"gates {gate_min:.1f} min; lean MCP calls {mcp}")
        for cls, (n, tot) in totals.items():
            print(f"    {cls:<11} {n:>3} calls {tot / 60:6.1f} min")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config-dir", default=None,
                    help="Claude Code config dir (default: $CLAUDE_CONFIG_DIR or ~/.claude)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("limits", help="live 5h/weekly limit utilization (OAuth endpoint)")
    tp = sub.add_parser("tokens", help="local transcript token sums per model")
    gp = sub.add_parser("gates", help="per-session wall time and time spent in lake gate calls")
    for p in (tp, gp):
        p.add_argument("--hours", type=float, default=5.0, help="trailing window in hours (default 5)")
        p.add_argument("--days", type=float, default=None,
                       help="trailing window in days (overrides --hours)")
        p.add_argument("--since", default=None,
                       help="window start as an ISO time, e.g. a commit's `git log --format=%%cI` "
                            "(overrides --hours/--days)")
        p.add_argument("--until", default=None,
                       help="window end as an ISO time (default now); with --since, splits a "
                            "multi-commit dispatch at its commits")
    tp.add_argument("--by-session", action="store_true", help="also break down by session file")
    gp.add_argument("--match", default="agent-",
                    help="only session files whose name contains this (default: subagents)")
    gp.add_argument("--verbose", action="store_true", help="also list each gate call")
    args = ap.parse_args()
    {"limits": cmd_limits, "tokens": cmd_tokens, "gates": cmd_gates}[args.cmd](args)


if __name__ == "__main__":
    main()
