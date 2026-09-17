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
line of notes/harness/incidents.md. `--select attack` keeps attack and review
sessions; an aborted start with fewer than `--min-requests` (2) API requests is
dropped; `--ids` prints only their ids, space-separated, for analyze.py:

    python3 notes/harness/instrument/analyze.py \\
        $(python3 notes/harness/instrument/sessions.py --since-review --select attack --ids) > all.json
    python3 notes/harness/instrument/report.py --attack all.json

The logs root is analyze.py's ($CLAUDE_LOGS_ROOT, else <config dir>/projects/
<cwd with '/' -> '-'>, the config dir from $CLAUDE_CONFIG_DIR); it is printed
to stderr so a wrong root is visible at once. Written 2026-09-17 for the first
/harness-review, which found the sessions by hand.
"""
import os, sys, json, glob, re, datetime, collections, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyze import default_root
from classify import CMD, kind_of

def last_review(incidents='notes/harness/incidents.md'):
    """Date of the last `## review YYYY-MM-DD` line, or None."""
    d = None
    try:
        for l in open(incidents):
            m = re.match(r'## review (\d{4}-\d{2}-\d{2})', l)
            if m: d = datetime.date.fromisoformat(m.group(1))
    except OSError:
        pass
    return d

def local_midnight(d):
    return datetime.datetime.combine(d, datetime.time()).astimezone()

def scan(path):
    first = last = None; reqs = set(); models = collections.Counter(); cmds = []; prompt = None
    for line in open(path, errors='replace'):
        try: d = json.loads(line)
        except Exception: continue
        ts = d.get('timestamp')
        if ts:
            t = datetime.datetime.fromisoformat(ts.replace('Z', '+00:00'))
            first = first or t; last = t
        typ = d.get('type')
        if typ == 'assistant':
            m = d.get('message', {}) or {}
            rid = d.get('requestId') or m.get('id')
            if rid not in reqs:
                reqs.add(rid); models[m.get('model') or '?'] += 1
        elif typ == 'user' and not d.get('isMeta'):
            c = (d.get('message', {}) or {}).get('content')
            txt = c if isinstance(c, str) else ' '.join(
                b.get('text', '') for b in (c or []) if isinstance(b, dict) and b.get('type') == 'text')
            if not txt: continue
            for m in CMD.finditer(txt): cmds.append((m.group(1).strip(), (m.group(2) or '').strip()))
            if prompt is None and not txt.lstrip().startswith('<'):
                prompt = txt.strip()[:60].replace('\n', ' ')
    return first, last, reqs, models, cmds, prompt

def list_sessions(root, since=None, min_requests=2):
    """Main sessions under root, oldest first; an aborted start with fewer than min_requests API requests is dropped."""
    rows = []
    for p in sorted(glob.glob(os.path.join(root, '*.jsonl'))):
        if since and datetime.datetime.fromtimestamp(os.path.getmtime(p), datetime.timezone.utc) < since:
            continue  # untouched since the window opened
        first, last, reqs, models, cmds, prompt = scan(p)
        if not first or len(reqs) < min_requests: continue
        if since and first < since: continue
        label, group = kind_of(cmds, prompt)
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
    ap.add_argument('--select', default='all', choices=['all', 'attack', 'lean'])
    ap.add_argument('--ids', action='store_true', help='print only the ids, space-separated')
    ap.add_argument('--min-requests', type=int, default=2, help='drop sessions with fewer API requests (aborted starts)')
    a = ap.parse_args()
    root = a.logs_root or os.environ.get('CLAUDE_LOGS_ROOT') or default_root()
    since = None
    if a.since_review:
        d = last_review()
        if d is None: sys.exit('no `## review` line in notes/harness/incidents.md; pass --since')
        since = local_midnight(d)
    elif a.since:
        since = local_midnight(datetime.date.fromisoformat(a.since))
    if not os.path.isdir(root): sys.exit(f'no transcripts at logs root {root}')
    print(f'logs root: {root}' + (f' · since {since:%Y-%m-%d} local' if since else ''), file=sys.stderr)
    rows = [r for r in list_sessions(root, since, a.min_requests) if a.select == 'all' or r['group'] == a.select]
    if a.ids:
        print(' '.join(r['sid'] for r in rows)); return
    for r in rows:
        s = r['start'].astimezone(); e = r['end'].astimezone()
        print(f"{r['sid'][:8]}  {s:%Y-%m-%d %H:%M}->{e:%H:%M}  {r['hours']:5.2f}h  {r['requests']:4d} req  "
              f"{model_mix(r['models']):<28} {r['label']}")
    print(f'{len(rows)} sessions', file=sys.stderr)

if __name__ == '__main__':
    main()
