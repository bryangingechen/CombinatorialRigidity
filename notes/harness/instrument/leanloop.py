#!/usr/bin/env python3
"""How agents get Lean feedback: lean-lsp MCP calls against `lake` round-trips.

    python3 notes/harness/instrument/leanloop.py                      # by month x agent family
    python3 notes/harness/instrument/leanloop.py --by model           # by month x model
    python3 notes/harness/instrument/leanloop.py --since 2026-09-27 --by model

Added 2026-09-27 (incident line of that date). Reads every local transcript of this
project, main sessions and subagents, and keeps only the transcripts that did Lean work
(at least one `lake build`, `lake env lean` or `lake lean`). For each group it prints how many
of those used the MCP at all, the `lake` round-trips per transcript with and without it, how
many were spike-shaped (`--spike-min` or more `lake env lean` / `lake lean` calls), and how many
spike runs were `lake lean`, the command the 2026-09-27 trial prescribes (the first version
counted only `lake env lean` and `lake build`, so a post-trial spike was invisible to it --
incidents.md, review 2026-09-27). `--since` takes an ISO time; a bare date is local midnight. A tool_use block is
counted once by its id. Bash commands are matched by regex, so a `lake build` quoted inside
an echo counts too; the error is small next to the June-to-September shift it measures.

Transcript dir: <config-dir>/projects/<project slug>, the config dir from --config-dir,
else $CLAUDE_CONFIG_DIR, else ~/.claude (as `.claude/scripts/session-usage.py`).
"""
import argparse, collections, datetime, glob, json, os, re
from pathlib import Path

LAKE_ENV = re.compile(r"lake\s+env\s+lean\b")
LAKE_LEAN = re.compile(r"lake\s+lean\b")
LAKE_BUILD = re.compile(r"lake\s+build\b")
FAMILIES = ("phase-builder", "recon", "attack", "Explore", "general-purpose", "Plan")


def family(meta_path):
    try:
        t = json.load(open(meta_path)).get("agentType", "?")
    except Exception:
        return "sub:?"
    return next((f for f in FAMILIES if t.startswith(f)), "other")


def model_family(m):
    for k in ("opus", "sonnet", "haiku", "fable"):
        if k in m:
            v = re.search(k + r"-(\d+(?:-\d+)?)", m)
            return f"{k}-{v.group(1) if v else '?'}"
    return m[:20]


def scan(path):
    c = collections.Counter(); models = collections.Counter(); start = None; seen = set()
    for line in open(path, errors="replace"):
        try:
            d = json.loads(line)
        except Exception:
            continue
        if start is None and d.get("timestamp"):
            start = d["timestamp"]
        if d.get("type") != "assistant":
            continue
        msg = d.get("message") or {}
        if msg.get("model") and msg["model"] != "<synthetic>":
            models[msg["model"]] += 1
        for b in msg.get("content") or []:
            if not isinstance(b, dict) or b.get("type") != "tool_use" or b.get("id") in seen:
                continue
            seen.add(b.get("id"))
            name = b.get("name", "")
            if name.startswith("mcp__lean-lsp__"):
                c["mcp"] += 1
            elif name == "Bash":
                cmd = (b.get("input") or {}).get("command", "")
                c["env"] += bool(LAKE_ENV.search(cmd))
                c["lean"] += bool(LAKE_LEAN.search(cmd))
                c["build"] += bool(LAKE_BUILD.search(cmd))
    return c, models, start


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--config-dir")
    ap.add_argument("--project-dir", default=os.getcwd())
    ap.add_argument("--by", choices=("family", "model"), default="family")
    ap.add_argument("--since", default="", help="ISO time (a bare date is local midnight); transcripts starting before it are skipped")
    ap.add_argument("--spike-min", type=int, default=3)
    ap.add_argument("--skip", action="append", default=[], help="substring of a transcript path to skip (a running agent)")
    a = ap.parse_args()
    cfg = Path(a.config_dir or os.environ.get("CLAUDE_CONFIG_DIR", "~/.claude")).expanduser()
    root = cfg / "projects" / re.sub(r"[^A-Za-z0-9]", "-", str(Path(a.project_dir).resolve()))
    since = None
    if a.since:
        since = datetime.datetime.fromisoformat(a.since)
        if since.tzinfo is None:
            since = since.astimezone()
    agg = collections.defaultdict(collections.Counter)
    for path in glob.glob(str(root / "**" / "*.jsonl"), recursive=True):
        if any(s in path for s in a.skip):
            continue
        c, models, start = scan(path)
        lake = c["env"] + c["lean"] + c["build"]
        if not lake or not start:
            continue
        if since and datetime.datetime.fromisoformat(start.replace("Z", "+00:00")) < since:
            continue
        sub = "/subagents/" in path
        if a.by == "model":
            g = model_family(models.most_common(1)[0][0]) if models else "?"
        else:
            g = family(path[: -len(".jsonl")] + ".meta.json") if sub else "main"
        r = agg[(start[:7], g)]
        r["n"] += 1
        used = c["mcp"] > 0
        r["mcp_n"] += used; r["mcp_calls"] += c["mcp"]
        r["lake_mcp" if used else "lake_nomcp"] += lake
        spike = c["env"] + c["lean"] >= a.spike_min
        r["spike"] += spike; r["spike_mcp"] += spike and used
        r["lean_runs"] += c["lean"]; r["spike_runs"] += c["env"] + c["lean"]
    print(f"{'month':8} {a.by:16} {'lean-work':>9} {'used MCP':>12} {'MCP calls':>9} "
          f"{'lake/tr no-MCP':>14} {'lake/tr MCP':>11} {'spikes (MCP)':>13} {'lake lean share':>15}")
    for k in sorted(agg):
        r = agg[k]; n = r["n"]; m = r["mcp_n"]
        print(f"{k[0]:8} {k[1]:16} {n:9d} {m:5d} ({100 * m // n:3d}%) {r['mcp_calls']:9d} "
              f"{r['lake_nomcp'] / max(1, n - m):14.1f} {r['lake_mcp'] / max(1, m):11.1f} "
              f"{r['spike']:6d} ({r['spike_mcp']:3d}) {r['lean_runs']:6d}/{r['spike_runs']:<4d}")


if __name__ == "__main__":
    main()
