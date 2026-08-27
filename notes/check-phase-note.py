#!/usr/bin/env python3
"""Gate: a phase note (`notes/Phase<N>.md` / `notes/Phase<N><letter>.md`) must
stay forward-weighted, under the ~500-line tripwire, with a word-capped
`**Status:**` header and no over-long *Decisions made* entry.

**This script invents no policy.** Every rule it checks is already written
down: the composition ratio, the ~500-line tripwire and the 8-line-per-entry
backstop are `notes/CLAUDE.md` *Forward-weighted note* + *One-screen-per-entry
rule*; "fix it in this commit, not a later cleanup round" is top-level
`CLAUDE.md` *Before each commit -> Compress in-commit*, which also states that
the note's own `**Status:**` header block counts as one of the sections a
commit must keep honest. The word cap on that header is `RESEARCH-ARC.md`
section 6 (mechanical word cap with recompute-not-bump) applied to the other
single status summary the phase owns. What is new here is only *enforcement*.

Why this exists -- the same measured failure `check-gapmap-cells.py` answers
for the gap map. `notes/Phase39.md` sat at ~500 lines from 2026-07-25 to
08-15, then went 660 -> 882 -> **1500** in six days; `35e9ce6e` compressed it
back to 554 (forward 326 / finished 93; the `**Status:**` header 155 -> 57
lines). **Three prose rules already forbade that growth and all three
failed**: the ~500-line tripwire (`notes/CLAUDE.md`); steps 4-5 of
`notes/Pencil-fanout.md`'s Landing checklist ("add a **one-line** *Decisions
made* entry ... keep `notes/Phase39.md` forward-weighted and under the
~500-line tripwire"); and that file's own header rule "Selection provenance is
NOT duplicated here". The one rule that held over the same period is the one
with a script behind it -- `check-gapmap-cells.py`, adopted (in its own words)
after "two prose-only repairs were abandoned in favour of this mechanical
cap". The phase note's `**Status:**` header is the same kind of object as a
gap-map cell with no cap on it, and it failed the same way: one appended
paragraph per landing. `35e9ce6e`'s own *Blockers* entry predicts the
re-breach -- "every landing commit is `+50...100 / -20...30` on this note, so
~10 landings re-breach the tripwire" -- and names the landing checklist as the
gate. This script is that gate, made mechanical.

What is checked, and against which stated rule:

  1. **Total lines** vs the ~500-line tripwire (`LINE_CAPS`). **In-progress
     notes only:** the rule's own phase-close carve-out makes a closed note
     "the compressed archive ROADMAP section N points at", and several closed
     notes are legitimately long (Phase22a 961, Phase21 875, Phase5 805), so
     capping those would be grandfather noise rather than live signal.
  2. **forward > finished** -- the rule's *primary* gate, and the one that had
     no check at all before this script. Forward = the *Current state* /
     *Blockers* / *Hand-off* sections plus every open `[ ]` item anywhere;
     finished = *Decisions made* plus every `[x]` item anywhere. Counted as
     raw line spans (heading line + body, blank lines included), which is how
     `35e9ce6e` reported its own figures -- so they reproduce here exactly
     (326 / 93). A section matching neither side (`## Citations`, `## The
     question and the opening recon`) is NEUTRAL and scores for neither: the
     gate compares the two sides the rule itself names. In-progress notes
     only, same carve-out -- at phase close *Decisions made* is *supposed* to
     dominate. **Calibration note, measured:** at 1500 lines the note's ratio
     was still 926 / 329, i.e. this check alone would NOT have caught the
     incident -- the line cap and the header cap are what fire there. The
     ratio is the rule's own primary gate and catches the opposite failure (a
     winding-down note whose finished log has gone stale), so all four are
     needed; none of them subsumes another.
  3. **`**Status:**` header words** (`STATUS_CAPS`) -- the accretion surface,
     under `RESEARCH-ARC.md` section 6's recompute-not-bump discipline.
  4. **Each *Decisions made* entry <= 8 lines** -- the explicit backstop. An
     "entry" is a top-level list item of that section.

Modes (the same three as `check-gapmap-cells.py` / `check-log-rows.py`):
  (default)  check only the phase notes this commit touched (working tree vs
             HEAD, untracked notes included).
  --all      check every phase note AND print each one's measurements. This is
             the mode the caps below were read off, so a recalibration is
             reproducible without a throwaway script.
  --last     check the notes changed in HEAD vs HEAD~1 (post-commit audit).

Grandfathering, and why it is per-surface rather than per-file. Checks 1 and 2
are properties of the whole note, so they fire on any note this commit
touches. Checks 3 and 4 are properties of one *surface*, and legacy notes are
full of pre-rule breaches (`--all` today reports ~30 notes with a *Decisions
made* entry over 8 lines, and Phase22b's header at 1666 words) -- so in the
two diff modes they fire only on a header or an entry whose text this commit
actually CHANGED. That is `check-gapmap-cells.py`'s rule ("any row you DO
touch must pass") at the granularity this file needs; `--all` still reports
the legacy debt for an audit pass.

Exit 1, listing offenders, if any checked note breaks any of the four. There
is no pre-commit hook: run it by hand (`python3 notes/check-phase-note.py`)
before committing a phase-note edit. The `/coordinate-phase` step-4
verification invokes it.

Caps. Both cap tables follow `check-gapmap-cells.py`'s precedent exactly: the
generic default is the already-stated number, a per-note entry is set at
**that note's own post-compression measurement plus documented headroom** --
not at a round number -- and every later bump carries a date and a one-line
reason in the same commit. Recompute the note first (twice, per that script's
docstring), then bump.

**2026-08-26, `Phase39.md` seeded at the `35e9ce6e` compression's own size.**
Measured there by `--all`: **554 lines, `**Status:**` header 495 words,
forward 326 / finished 93, longest *Decisions made* entry 7 lines.** Caps set
to **580 lines / 525 status words** -- +4.7% and +6.1%, deliberately TIGHT
rather than the ~15% the gap-map caps started at. Two measured reasons: the
note's own *Blockers* bullet prices a landing at `+50...100 / -20...30` lines,
so ~15% headroom (+83) is exactly one bad landing and the cap would buy
nothing; and the F21 lesson recorded in `check-gapmap-cells.py` is that a cap
bounds growth but cannot express purpose, so generous headroom gets coasted
on. The landing checklist already requires a landing's *Decisions made* entry
to be **one line**, which makes a compliant landing roughly net-flat on this
note -- +26 lines is real room, and a landing that needs more is exactly the
case this gate exists to stop.
"""
import os
import re
import subprocess
import sys

NOTE_RE = re.compile(r"^Phase\d+[a-z]?\.md$")  # NOT -design / -cleanup / -perf
DIRNAME = "notes"

LINE_CAP_DEFAULT = 500  # the `notes/CLAUDE.md` tripwire, verbatim
LINE_CAPS = {"Phase39.md": 580}

# Most notes' headers are well under 250 words; the three over 300 today
# (Phase22b 1666, Phase12 350, Phase22c 347) are closed and grandfathered
# unless a commit edits the header itself.
STATUS_CAP_DEFAULT = 300
STATUS_CAPS = {"Phase39.md": 525}

ENTRY_LINE_CAP = 8  # `notes/CLAUDE.md` *One-screen-per-entry rule*

HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
STATUS_RE = re.compile(r"^\*\*Status:\*\*")
ITEM_RE = re.compile(r"^(\s*)[-*+]\s+(\[[ xX]\]\s*)?")
TOP_ITEM_RE = re.compile(r"^[-*+]\s+")
DONE_RE = re.compile(r"^\s*[-*+]\s+\[[xX]\]")
OPEN_RE = re.compile(r"^\s*[-*+]\s+\[ \]")

FORWARD_TITLE = re.compile(
    r"^(current state|hand-?off|open questions?|blockers?\b|"
    r"remaining work|worklist|work-?item checklist|layer plan|"
    r"lemma checklist|investigation checklist|checklist)",
    re.I,
)
FINISHED_TITLE = re.compile(r"^decisions made", re.I)
BLOCKER_TITLE = re.compile(r"blockers?\b", re.I)


def _title_class(title):
    """FORWARD / FINISHED / NEUTRAL for a `## ` section title.

    Only the sections `notes/CLAUDE.md` *Forward-weighted note* actually names
    score; anything else is NEUTRAL and counts for neither side."""
    if FINISHED_TITLE.match(title):
        return "finished"
    if FORWARD_TITLE.match(title) or BLOCKER_TITLE.search(title):
        return "forward"
    return "neutral"


def parse(text):
    """Measurements for one phase note."""
    lines = text.splitlines()
    active = False
    status_lines = []
    in_status = False
    first_section = None

    for i, line in enumerate(lines):
        m = HEADING_RE.match(line)
        if m and len(m.group(1)) >= 2:
            first_section = i
            break
        if STATUS_RE.match(line):
            in_status = True
            body = line
            active = bool(re.search(r"in progress", body, re.I)) and not re.search(
                r"\b(complete|closed)\b", body, re.I
            )
        if in_status:
            status_lines.append(line)
    if first_section is None:
        first_section = len(lines)

    # Section spans: [(start, end_exclusive, class, title)] over `## `+ headings.
    spans = []
    cur = None
    for i in range(first_section, len(lines)):
        m = HEADING_RE.match(lines[i])
        if m and len(m.group(1)) == 2:
            if cur is not None:
                spans.append((cur[0], i, cur[1], cur[2]))
            title = m.group(2)
            cur = (i, _title_class(title), title)
    if cur is not None:
        spans.append((cur[0], len(lines), cur[1], cur[2]))

    # Per-line class: a `[x]` item block is finished and a `[ ]` item block is
    # forward wherever they sit (the rule names "open `[ ]` checklist items"
    # and "done-item notes" independently of section); every other line takes
    # its section's class.
    forward = finished = 0
    for start, end, klass, _title in spans:
        item_klass = None
        for i in range(start, end):
            line = lines[i]
            if DONE_RE.match(line):
                item_klass = "finished"
            elif OPEN_RE.match(line):
                item_klass = "forward"
            elif ITEM_RE.match(line) or HEADING_RE.match(line):
                item_klass = None
            eff = item_klass or klass
            if eff == "forward":
                forward += 1
            elif eff == "finished":
                finished += 1

    # *Decisions made* entries: top-level list items of that section.
    entries = []
    for start, end, klass, _title in spans:
        if klass != "finished":
            continue
        bounds = [i for i in range(start, end) if TOP_ITEM_RE.match(lines[i])]
        for j, b in enumerate(bounds):
            stop = bounds[j + 1] if j + 1 < len(bounds) else end
            for k in range(b + 1, stop):  # a heading also ends an entry
                if HEADING_RE.match(lines[k]):
                    stop = k
                    break
            block = lines[b:stop]
            while block and not block[-1].strip():
                block.pop()
            label = re.sub(r"\s+", " ", lines[b].strip())[:60]
            entries.append((b + 1, len(block), label, "\n".join(block)))

    return {
        "lines": len(lines),
        "active": active,
        "status_text": "\n".join(status_lines),
        "status_words": len("\n".join(status_lines).split()),
        "forward": forward,
        "finished": finished,
        "entries": entries,
    }


def offenders(name, m, base=None):
    """Rule breaches for one note. `base` = its measurements in the commit
    being compared against; when given, the two *surface-local* checks (status
    header, per-entry length) fire only on a surface this commit CHANGED --
    the `check-gapmap-cells.py` grandfathering rule at the granularity that
    matters here. The two whole-file checks (line cap, ratio) always fire on a
    touched note: they are properties of the note, not of one surface."""
    bad = []
    line_cap = LINE_CAPS.get(name, LINE_CAP_DEFAULT)
    status_cap = STATUS_CAPS.get(name, STATUS_CAP_DEFAULT)
    if m["active"] and m["lines"] > line_cap:
        bad.append(f"{m['lines']} lines (+{m['lines'] - line_cap} over cap {line_cap})")
    # `finished > 0` guard: a just-opened note has no *Decisions made* yet, and
    # the rule is "if *Decisions made* OUTGROWS the forward sections" -- an
    # empty finished log outgrows nothing.
    if m["active"] and m["finished"] > 0 and m["finished"] >= m["forward"]:
        bad.append(
            f"not forward-weighted: finished {m['finished']} lines "
            f">= forward {m['forward']} (notes/CLAUDE.md *Forward-weighted note*)"
        )
    if (base is None or m["status_text"] != base["status_text"]) and m[
        "status_words"
    ] > status_cap:
        bad.append(
            f"**Status:** header {m['status_words']} words "
            f"(+{m['status_words'] - status_cap} over cap {status_cap})"
        )
    old_entries = None if base is None else {t for _, _, _, t in base["entries"]}
    for lineno, n, label, textblock in m["entries"]:
        if old_entries is not None and textblock in old_entries:
            continue  # untouched entry: grandfathered, per the modes above
        if n > ENTRY_LINE_CAP:
            bad.append(
                f"*Decisions made* entry at line {lineno} is {n} lines "
                f"(cap {ENTRY_LINE_CAP}): {label}"
            )
    return bad


def all_notes():
    return sorted(f for f in os.listdir(DIRNAME) if NOTE_RE.match(f))


def read_note(name):
    with open(os.path.join(DIRNAME, name), encoding="utf-8") as f:
        return f.read()


def git_show(ref, name):
    try:
        return subprocess.run(
            ["git", "show", f"{ref}:{DIRNAME}/{name}"],
            capture_output=True, text=True, check=True,
        ).stdout
    except Exception:
        return None


def changed(ref_new, ref_old):
    """Phase notes differing between two refs (`None` new ref = working tree)."""
    out = []
    names = set(all_notes()) if ref_new is None else set()
    if ref_new is not None:
        try:
            listing = subprocess.run(
                ["git", "ls-tree", "--name-only", f"{ref_new}:{DIRNAME}"],
                capture_output=True, text=True, check=True,
            ).stdout.split()
        except Exception:
            listing = []
        names = {n for n in listing if NOTE_RE.match(n)}
    for name in sorted(names):
        new = read_note(name) if ref_new is None else git_show(ref_new, name)
        old = git_show(ref_old, name)
        if new is not None and new != old:
            out.append(name)
    return out


def main(argv):
    full = "--all" in argv
    if full:
        names, label = all_notes(), "all phase notes"
        pairs = [(n, read_note(n), None) for n in names]
    elif "--last" in argv:
        names, label = changed("HEAD", "HEAD~1"), "changed HEAD~1..HEAD"
        pairs = [(n, git_show("HEAD", n), git_show("HEAD~1", n)) for n in names]
    else:
        names, label = changed(None, "HEAD"), "changed vs HEAD"
        pairs = [(n, read_note(n), git_show("HEAD", n)) for n in names]

    failed = False
    for name, new, old in pairs:
        m = parse(new)
        base = parse(old) if old is not None else None
        if full:
            print(
                f"  {name:<14} {m['lines']:>5} lines  "
                f"status {m['status_words']:>4}w  "
                f"forward {m['forward']:>4} / finished {m['finished']:>4}  "
                f"max-entry {max([n for _, n, _, _ in m['entries']] or [0]):>2}  "
                f"{'ACTIVE' if m['active'] else ''}"
            )
        bad = offenders(name, m, base)
        if bad:
            failed = True
            print(f"FAIL: {DIRNAME}/{name}", file=sys.stderr)
            for b in bad:
                print(f"  - {b}", file=sys.stderr)

    if failed:
        print(
            "Fix in THIS commit, not a later cleanup round (`CLAUDE.md` "
            "*Compress in-commit*): promote cross-cutting *Decisions made* "
            "entries and collapse the rest to one-line verdicts; recompute the "
            "**Status:** header as a current-state paragraph rather than "
            "appending another landing's clause. Only if the note's FORWARD "
            "part has genuinely grown, bump its entry in LINE_CAPS / "
            "STATUS_CAPS in this script, in the same commit, with a dated "
            "reason -- recompute first, twice.",
            file=sys.stderr,
        )
        return 1
    print(f"OK: {len(names)} phase note(s) checked ({label}); all within cap.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
