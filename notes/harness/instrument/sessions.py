#!/usr/bin/env python3
"""List this project's Claude Code sessions and pick out the attack-track ones.

    python3 notes/harness/instrument/sessions.py [--logs-root DIR] [--since YYYY-MM-DD | --since-review]
                                                 [--select attack|lean|all] [--ids]

One row per main-session transcript under the logs root (subagent transcripts
live in per-session subdirectories and are skipped): id, local start -> end,
hours, API requests, model mix, and the session's kind, read from its first
slash command that is not a local setting (/model, /clear, ...): `attack <name>`,
`review <name>`, `lean <N>` (/coordinate-phase), `harness-review`, or the first
prompt's opening words. `--since-review` starts at the last `## review YYYY-MM-DD`
line of notes/harness/incidents.md (the time of the commit that added it). `--select attack` keeps attack and review
sessions; `--select research` adds the free-form sessions that write under notes/pencil/ or
notes/attacks/ (group `research`); an aborted start with fewer than `--min-requests` (2) API requests is
dropped; `--ids` prints only their ids, space-separated, for analyze.py:

    python3 notes/harness/instrument/analyze.py \\
        $(python3 notes/harness/instrument/sessions.py --since-review --select attack --ids) > all.json
    python3 notes/harness/instrument/report.py --attack all.json

The logs root is analyze.py's ($CLAUDE_LOGS_ROOT, else <config dir>/projects/
<cwd with '/' -> '-'>, the config dir from $CLAUDE_CONFIG_DIR); it is printed
to stderr so a wrong root is visible at once. Written 2026-09-17 for the first
/harness-review, which found the sessions by hand.
"""
import os, sys, json, glob, re, datetime, collections, argparse, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyze import default_root
from classify import CMD, kind_of

# A free-form session (no /attack, /coordinate-phase or /harness-review) that writes under the
# research corpus is a research session: the W4 reopening and the X0 design ran that way,
# unseen by `--select attack` (incidents.md 2026-09-26; the PI chose to count them).
WRITE_TOOLS = {'Edit', 'Write', 'NotebookEdit', 'MultiEdit'}
RESEARCH_PATH = re.compile(r'notes/(pencil|attacks)/')

def last_review(incidents='notes/harness/incidents.md'):
    """Where the window after the last `## review YYYY-MM-DD` line opens: the time of the commit
    that added the line, else that date's local midnight; None without a line. (Local midnight
    alone re-listed the sessions that review had counted earlier the same day -- incidents.md
    2026-09-26.)"""
    d = None
    try:
        for l in open(incidents):
            m = re.match(r'## review (\d{4}-\d{2}-\d{2})', l)
            if m: d = m.group(1)
    except OSError:
        pass
    if d is None: return None
    try:
        out = subprocess.run(['git', 'log', '-1', '--format=%cI', '-S', f'## review {d}', '--', incidents],
                             capture_output=True, text=True, timeout=60).stdout.strip()
        if out: return datetime.datetime.fromisoformat(out)
    except Exception:
        pass
    return local_midnight(datetime.date.fromisoformat(d))

def local_midnight(d):
    return datetime.datetime.combine(d, datetime.time()).astimezone()

def scan(path):
    first = last = None; reqs = set(); models = collections.Counter(); cmds = []; prompt = None; rwrites = 0
    for line in open(path, errors='replace'):
        try: d = json.loads(line)
        except Exception: continue
        typ = d.get('type')
        ts = d.get('timestamp')
        if ts and typ in ('assistant', 'user'):
            # not 'system' / 'queue-operation': a terminal left open after the last turn is
            # not work (the 2026-09-23 recovery session listed at 4.70h for 0.97h of turns)
            t = datetime.datetime.fromisoformat(ts.replace('Z', '+00:00'))
            first = first or t; last = t
        if typ == 'assistant':
            m = d.get('message', {}) or {}
            rid = d.get('requestId') or m.get('id')
            if rid not in reqs:
                reqs.add(rid); models[m.get('model') or '?'] += 1
            for b in m.get('content') or []:
                if isinstance(b, dict) and b.get('type') == 'tool_use' and b.get('name') in WRITE_TOOLS \
                        and RESEARCH_PATH.search(str((b.get('input') or {}).get('file_path', ''))):
                    rwrites += 1
        elif typ == 'user' and not d.get('isMeta'):
            c = (d.get('message', {}) or {}).get('content')
            txt = c if isinstance(c, str) else ' '.join(
                b.get('text', '') for b in (c or []) if isinstance(b, dict) and b.get('type') == 'text')
            if not txt: continue
            for m in CMD.finditer(txt): cmds.append((m.group(1).strip(), (m.group(2) or '').strip()))
            if prompt is None and not txt.lstrip().startswith('<'):
                prompt = txt.strip()[:60].replace('\n', ' ')
    return first, last, reqs, models, cmds, prompt, rwrites

def list_sessions(root, since=None, min_requests=2):
    """Main sessions under root, oldest first; an aborted start with fewer than min_requests API requests is dropped."""
    rows = []
    for p in sorted(glob.glob(os.path.join(root, '*.jsonl'))):
        if since and datetime.datetime.fromtimestamp(os.path.getmtime(p), datetime.timezone.utc) < since:
            continue  # untouched since the window opened
        first, last, reqs, models, cmds, prompt, rwrites = scan(p)
        if not first or len(reqs) < min_requests: continue
        if since and first < since: continue
        label, group = kind_of(cmds, prompt)
        if group == 'other' and rwrites: group = 'research'
        rows.append(dict(sid=os.path.basename(p)[:-6], start=first, end=last,
                         hours=(last - first).total_seconds() / 3600, requests=len(reqs),
                         models=models, label=label, group=group))
    rows.sort(key=lambda r: r['start'])
    return rows

def model_mix(models):
    return ' '.join(f"{k.replace('claude-', '')}:{v}" for k, v in models.most_common())

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--logs-root', default=None)
    ap.add_argument('--since', help='YYYY-MM-DD, local midnight')
    ap.add_argument('--since-review', action='store_true', help='start at the last ## review line of incidents.md')
    ap.add_argument('--select', default='all', choices=['all', 'attack', 'research', 'lean'])
    ap.add_argument('--ids', action='store_true', help='print only the ids, space-separated')
    ap.add_argument('--min-requests', type=int, default=2, help='drop sessions with fewer API requests (aborted starts)')
    a = ap.parse_args()
    root = a.logs_root or os.environ.get('CLAUDE_LOGS_ROOT') or default_root()
    since = None
    if a.since_review:
        since = last_review()
        if since is None: sys.exit('no `## review` line in notes/harness/incidents.md; pass --since')
    elif a.since:
        since = local_midnight(datetime.date.fromisoformat(a.since))
    if not os.path.isdir(root): sys.exit(f'no transcripts at logs root {root}')
    print(f'logs root: {root}' + (f' · since {since.astimezone():%Y-%m-%d %H:%M} local' if since else ''), file=sys.stderr)
    keep = {'attack': {'attack'}, 'research': {'attack', 'research'}, 'lean': {'lean'}}.get(a.select)
    rows = [r for r in list_sessions(root, since, a.min_requests) if keep is None or r['group'] in keep]
    if a.ids:
        print(' '.join(r['sid'] for r in rows)); return
    for r in rows:
        s = r['start'].astimezone(); e = r['end'].astimezone()
        print(f"{r['sid'][:8]}  {s:%Y-%m-%d %H:%M}->{e:%H:%M}  {r['hours']:5.2f}h  {r['requests']:4d} req  "
              f"{model_mix(r['models']):<28} {r['label']}")
    print(f'{len(rows)} sessions', file=sys.stderr)

if __name__ == '__main__':
    main()
