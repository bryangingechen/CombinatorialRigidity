#!/usr/bin/env python3
"""Budget checks for the research-side harness (HARNESS.md) and attack state files.

    python3 notes/harness/check.py                       # HARNESS.md: budget, tags, last review, trial age
    python3 notes/harness/check.py --state PATH          # an attack state.md: sections + budgets
    python3 notes/harness/check.py --state PATH --history  # per commit: "Where it breaks" and the signal lines

HARNESS.md rules: <= LINE_BUDGET lines; every bullet is tagged
`[YYYY-MM-DD, standing|trial]` and carries an incident pointer after `<-`
(or the arrow). The last `## review YYYY-MM-DD` line of incidents.md is
printed with the number of research sessions since it (attack track and
free-form, from the transcripts via instrument/sessions.py). A trial rule with more than
TRIAL_REVIEW_SESSIONS research sessions since its date is listed as review-due;
when no transcripts are readable the fallback is TRIAL_REVIEW_DAYS by date.
State files: every section of the template present, none over its
`<!-- budget N -->`, and "Where it breaks" non-empty. `--history` walks the
file's git history oldest first and prints, per commit, the session count,
the open-obligation count and whether "Where it breaks" changed -- a break
that changes every commit over a flat count is a rename treadmill
(HARNESS.md *Attack track*). Exit 1 on any failure; counts are printed either way.
"""
import argparse, datetime, os, re, subprocess, sys, pathlib

LINE_BUDGET = 150
TRIAL_REVIEW_SESSIONS = 3   # research sessions since the rule's date (the defaults in .claude/commands/harness-review.md)
TRIAL_REVIEW_DAYS = 30      # fallback when transcripts are unavailable
INCIDENTS = 'notes/harness/incidents.md'

def last_review_date(incidents=INCIDENTS):
    d = None
    try:
        for l in pathlib.Path(incidents).read_text().splitlines():
            m = re.match(r'## review (\d{4}-\d{2}-\d{2})', l)
            if m: d = datetime.date.fromisoformat(m.group(1))
    except OSError:
        pass
    return d

def review_start():
    """The window's opening after the last review (instrument/sessions.py's last_review), or None."""
    try:
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / 'instrument'))
        import sessions as S
        return S.last_review(INCIDENTS)
    except Exception:
        return None

def attack_session_dates():
    """Start times of every research session (attack track or free-form, sessions.py's groups
    `attack` and `research`) in the transcripts, or None if unreadable."""
    try:
        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent / 'instrument'))
        import sessions as S
        root = os.environ.get('CLAUDE_LOGS_ROOT') or S.default_root()
        if not os.path.isdir(root): return None
        return [r['start'] for r in S.list_sessions(root) if r['group'] in ('attack', 'research')]
    except Exception:
        return None
TAG = re.compile(r"^- \[(\d{4}-\d{2}-\d{2}), (standing|trial)\]")

def check_harness(path):
    lines = pathlib.Path(path).read_text().splitlines()
    fails = []
    if len(lines) > LINE_BUDGET:
        fails.append(f"{path}: {len(lines)} lines > budget {LINE_BUDGET}")
    counts = {"standing": 0, "trial": 0}
    due = []
    today = datetime.date.today()
    lr = last_review_date()
    sess = attack_session_dates()
    rs = review_start()
    since = None if sess is None else [t for t in sess if rs is None or t >= rs]
    i = 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("- "):
            m = TAG.match(l)
            if not m:
                fails.append(f"{path}:{i+1}: bullet without [date, status] tag")
            else:
                d = datetime.date.fromisoformat(m.group(1)); s = m.group(2)
                counts[s] += 1
                # the rule runs to the next bullet/blank/heading; it must carry a pointer
                j = i; block = l
                while j + 1 < len(lines) and lines[j+1].startswith("  "):
                    j += 1; block += " " + lines[j]
                if "←" not in block and "<-" not in block:
                    fails.append(f"{path}:{i+1}: rule has no incident pointer")
                if s == "trial":
                    if sess is not None:
                        n = sum(1 for x in sess if x.astimezone().date() >= d)
                        if n > TRIAL_REVIEW_SESSIONS:
                            due.append(f"{path}:{i+1}: trial since {d}, {n} research sessions since; review due")
                    elif (today - d).days > TRIAL_REVIEW_DAYS:
                        due.append(f"{path}:{i+1}: trial since {d}, review due (day-based fallback; no transcripts)")
                i = j
        i += 1
    print(f"{path}: {len(lines)}/{LINE_BUDGET} lines, {counts['standing']} standing, {counts['trial']} trial")
    print(f"last review: {lr or 'none'} · research sessions since: "
          f"{len(since) if since is not None else 'unknown (no transcripts; day-based trial age)'}")
    for x in due: print("REVIEW-DUE", x)
    return fails

SECTION = re.compile(r"^## (.+?)\s*(?:<!--\s*budget\s+(\d+)\s*-->)?\s*$")

def parse_sections(lines):
    sections, cur = {}, None
    for l in lines:
        m = SECTION.match(l)
        if m:
            cur = m.group(1).strip(); sections[cur] = []
        elif cur is not None and l.strip() and not l.strip().startswith("<!--"):
            sections[cur].append(l)
    return sections

def check_state(path, template="notes/attacks/TEMPLATE-state.md"):
    fails = []
    tlines = pathlib.Path(template).read_text().splitlines()
    budgets = {}
    for l in tlines:
        m = SECTION.match(l)
        if m and m.group(2): budgets[m.group(1).strip()] = int(m.group(2))
    lines = pathlib.Path(path).read_text().splitlines()
    sections = parse_sections(lines)
    for name, b in budgets.items():
        if name not in sections:
            fails.append(f"{path}: missing section '{name}'"); continue
        n = len(sections[name])
        if n > b: fails.append(f"{path}: section '{name}' {n} lines > budget {b} (move overflow to log.md)")
    wb = sections.get("Where it breaks", [])
    if not wb: fails.append(f"{path}: 'Where it breaks' is empty; it is mandatory while the lemma is open")
    total = sum(len(v) for v in sections.values())
    print(f"{path}: {len(sections)} sections, {total} content lines")
    return fails

def state_history(path):
    """Per commit touching the state file, oldest first: sessions-so-far, open-obligation count,
    whether "Where it breaks" changed, and its first words."""
    log = subprocess.run(["git", "log", "--format=%h %ad", "--date=short", "--follow", "--", path],
                         capture_output=True, text=True).stdout.splitlines()
    prev = None
    print(f"{'commit':8} {'date':10} {'sess':>4} {'oblig':>5} {'break':7}  where it breaks")
    for l in reversed([x for x in log if x.strip()]):
        sha, date = l.split()[:2]
        txt = subprocess.run(["git", "show", f"{sha}:{path}"], capture_output=True, text=True).stdout
        secs = parse_sections(txt.splitlines())
        m = re.search(r"Sessions so far:\s*(\d+)", txt); sess = m.group(1) if m else "?"
        wb = " ".join(x.strip() for x in secs.get("Where it breaks", [])).strip()
        m = re.search(r"Open obligations:\s*(\d+)", " ".join(secs.get("Signals", []))); ob = m.group(1) if m else "?"
        ch = "new" if prev is None else ("changed" if wb != prev else "same")
        print(f"{sha:8} {date:10} {sess:>4} {ob:>5} {ch:7}  {wb[:100]}")
        prev = wb
    print("a break that changes every commit over a flat obligation count is a rename treadmill (HARNESS.md *Attack track*)")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--harness", default="HARNESS.md")
    ap.add_argument("--state", help="an attack state.md to check against the template")
    ap.add_argument("--template", default="notes/attacks/TEMPLATE-state.md")
    ap.add_argument("--history", action="store_true", help="with --state: print the file's git history of the break and the signals")
    a = ap.parse_args()
    if a.state and a.history:
        state_history(a.state); sys.exit(0)
    fails = check_state(a.state, a.template) if a.state else check_harness(a.harness)
    for f in fails: print("FAIL", f)
    sys.exit(1 if fails else 0)
