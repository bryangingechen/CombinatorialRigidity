#!/usr/bin/env python3
"""Budget checks for the research-side harness (HARNESS.md) and attack state files.

    python3 notes/harness/check.py                 # HARNESS.md: budget, tags, trial age
    python3 notes/harness/check.py --state PATH    # an attack state.md: sections + budgets

HARNESS.md rules: <= LINE_BUDGET lines; every bullet is tagged
`[YYYY-MM-DD, standing|trial]` and carries an incident pointer after `<-`
(or the arrow). Trial rules older than TRIAL_REVIEW_DAYS are listed as
review-due (expiry is counted in attack sessions by /harness-review; the
date is the coarse fallback). State files: every section of the template
present, none over its `<!-- budget N -->`, and "Where it breaks" non-empty.
Exit 1 on any failure; counts are printed either way.
"""
import argparse, datetime, re, sys, pathlib

LINE_BUDGET = 150
TRIAL_REVIEW_DAYS = 30
TAG = re.compile(r"^- \[(\d{4}-\d{2}-\d{2}), (standing|trial)\]")

def check_harness(path):
    lines = pathlib.Path(path).read_text().splitlines()
    fails = []
    if len(lines) > LINE_BUDGET:
        fails.append(f"{path}: {len(lines)} lines > budget {LINE_BUDGET}")
    counts = {"standing": 0, "trial": 0}
    due = []
    today = datetime.date.today()
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
                if s == "trial" and (today - d).days > TRIAL_REVIEW_DAYS:
                    due.append(f"{path}:{i+1}: trial since {d}, review due")
                i = j
        i += 1
    print(f"{path}: {len(lines)}/{LINE_BUDGET} lines, {counts['standing']} standing, {counts['trial']} trial")
    for x in due: print("REVIEW-DUE", x)
    return fails

SECTION = re.compile(r"^## (.+?)\s*(?:<!--\s*budget\s+(\d+)\s*-->)?\s*$")

def check_state(path, template="notes/attacks/TEMPLATE-state.md"):
    fails = []
    tlines = pathlib.Path(template).read_text().splitlines()
    budgets = {}
    for l in tlines:
        m = SECTION.match(l)
        if m and m.group(2): budgets[m.group(1).strip()] = int(m.group(2))
    lines = pathlib.Path(path).read_text().splitlines()
    sections, cur = {}, None
    for l in lines:
        m = SECTION.match(l)
        if m:
            cur = m.group(1).strip(); sections[cur] = []
        elif cur is not None and l.strip() and not l.strip().startswith("<!--"):
            sections[cur].append(l)
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

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--harness", default="HARNESS.md")
    ap.add_argument("--state", help="an attack state.md to check against the template")
    ap.add_argument("--template", default="notes/attacks/TEMPLATE-state.md")
    a = ap.parse_args()
    fails = check_state(a.state, a.template) if a.state else check_harness(a.harness)
    for f in fails: print("FAIL", f)
    sys.exit(1 if fails else 0)
