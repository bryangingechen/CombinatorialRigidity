#!/usr/bin/env python3
"""Read-only slice reader for `notes/PhaseN.md`: get the next concrete task,
the `**Status:**` header, or the hand-off, without a full-file pass.

Why this exists -- the same ACCESS problem `gapmap.py` solves, on the surface
a coordinator reads FIRST. `notes/Harness-structure.md` D6.1 states the gap
the other way round: section 6's promoted lesson is *cap the cell, but also
ship a READER for it*, and it was applied to the gap map
(`check-gapmap-cells.py` + `gapmap.py`) and NOT to the phase note, which has
`check-phase-note.py` and nothing to read it with.

The shape is the same one `gapmap.py` exists for. Measured 2026-09-10 at
`d8a9e74f`: `notes/Phase39.md` is 579 lines, and its longest physical line --
the *Hand-off* next-task paragraph, the one sentence a coordinator actually
needs -- is **5 878 characters / 879 words on a single line** (it was ~3 700
at `c8efb227` eight commits earlier; it grows). So `grep 'next concrete'`
returns the whole paragraph and `sed -n` cannot cut inside it; one grep in
the 2026-09-10 session returned a 24 178-character result for exactly this
reason. No line number is recorded here on purpose -- `notes/ledger.py`'s own
NO-LINE-COLUMN finding is that a stored line number shifts for every edit
above it. Recompute with:

    awk '{print NR, length($0)}' notes/Phase39.md | sort -k2 -rn | head -1

Why it is worth more than the same reader elsewhere. D7.2: the coordinator's
pre-dispatch reading is not a one-time charge -- 143k loaded before the first
dispatch sat resident for 356 later requests, 27% of that session's
context-turns. The phase note is read BEFORE the first dispatch, so a reader
that halves it is worth ~20x the same reader used afterwards. That is why
this is the first script off D7.8's list and not the cheapest one.

  --next        the next-concrete-task paragraph, sentence-windowed. Prefers
                *Current state* over *Hand-off* when both carry one, per the
                loop's own tie-break, and SAYS SO when they disagree.
  --status      the `**Status:**` header block.
  --handoff     the *Hand-off / next phase* section.
  --section T   any section by title prefix (`--section 'current state'`).
  --list        section index with sizes -- what exists and what is expensive.
  --surfaces    every status surface an F17 sweep must touch, with its
                current first sentence, so the sweep can be checked rather
                than remembered. This is the mode that pays twice: F17 is
                three consecutive landings each leaving a DIFFERENT one stale.
  --selftest    lossless-split audit (no content).

`--head N` / `--tail N` / `--sentences A-B` / `--full` window the output,
exactly as in `gapmap.py`.

Nothing here writes. Reading is not gating: `check-phase-note.py` owns the
caps and this owns access, and D6.9's lesson is that the pair is not
redundant -- the gate bounds a MEASURE and the reader exposes SHAPE.

Parsing is NOT reimplemented. `check-phase-note.py`'s `parse()` is the one
phase-note parser (sections, `**Status:**` block, forward/finished classes)
and `gapmap.py`'s `units()` is the one sentence splitter, with its code-span
masking and abbreviation guards. Both are imported by path -- their filenames
are not Python identifiers -- so a fix to either reaches this reader.
"""

import argparse
import importlib.util
import os
import re
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)


def _load(filename, modname):
    path = os.path.join(_HERE, filename)
    spec = importlib.util.spec_from_file_location(modname, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GATE = _load("check-phase-note.py", "_cpn")      # parse(), caps, section regexes
GM = _load("gapmap.py", "_gapmap")               # units(), emit_units(), sizes

# The corpus's actual vocabulary, counted over every `notes/Phase*.md`
# (2026-09-10): "next concrete commit" 13, "next concrete step" 3, "next
# concrete task" 2, "next concrete unit" 1 -- plus "the next coordinator act".
# A reader that knows one spelling reports a missing sentence that is present,
# which is worse than no reader; keep this list in step with the corpus.
NEXT_RE = re.compile(
    r"next concrete (?:task|commit|step|unit)"
    r"|the next coordinator act"
    r"|THE NEXT CONCRETE",
    re.I,
)
ROADMAP = os.path.join(_ROOT, "ROADMAP.md")


# ---------------------------------------------------------------- sections

def sections(text):
    """[(title, class, body)] over `## ` headings, plus the `**Status:**`
    header as a synthetic leading section. Spans come from the gate's own
    `parse()` view of the file so the two cannot disagree about what a
    section is."""
    lines = text.split("\n")
    out = []
    m = GATE.parse(text)
    if m["status_text"].strip():
        out.append(("**Status:** header", "header", m["status_text"]))
    spans, cur = [], None
    for i, line in enumerate(lines):
        h = GATE.HEADING_RE.match(line)
        if h and len(h.group(1)) == 2:
            if cur is not None:
                spans.append((cur[0], i, cur[1]))
            cur = (i, h.group(2))
    if cur is not None:
        spans.append((cur[0], len(lines), cur[1]))
    for start, end, title in spans:
        body = "\n".join(lines[start + 1:end]).strip("\n")
        out.append((title, GATE._title_class(title), body))
    return out


def find_section(secs, want):
    want = want.strip().lower().lstrip("#").strip()
    for title, klass, body in secs:
        if title.lower().startswith(want):
            return title, klass, body
    for title, klass, body in secs:
        if want in title.lower():
            return title, klass, body
    raise SystemExit(
        f"no section matching {want!r}; try --list "
        f"({', '.join(t for t, _k, _b in secs)})"
    )


def paragraphs(body):
    return [p for p in re.split(r"\n\s*\n", body) if p.strip()]


def next_task_para(body):
    """The paragraph carrying the next-concrete-task sentence, else None."""
    for p in paragraphs(body):
        if NEXT_RE.search(p):
            return p
    return None


# ---------------------------------------------------------------- emitting

def _emit(label, text, args, kind="row"):
    print(f"  [{label}] {GM._size(text)} {GM._tok(len(text))}")
    GM.emit_units(GM.units(text), args, kind, indent="   ")


def _first_sentence(text, n=150):
    u = GM.units(text)
    s = re.sub(r"\s+", " ", (u[0] if u else text).strip())
    return s if len(s) <= n else s[: n - 1] + "…"


# ---------------------------------------------------------------- commands

def cmd_list(disp, text, secs):
    m = GATE.parse(text)
    cap = GATE.LINE_CAPS.get(os.path.basename(disp), GATE.LINE_CAP_DEFAULT)
    scap = GATE.STATUS_CAPS.get(os.path.basename(disp), GATE.STATUS_CAP_DEFAULT)
    print(f"{disp} — {m['lines']} lines (cap {cap}), "
          f"forward {m['forward']} / finished {m['finished']}, "
          f"{'ACTIVE' if m['active'] else 'closed'}")
    print(f"  {'section':<44}{'class':<10}{'size':>18}")
    for title, klass, body in secs:
        note = ""
        if klass == "header":
            note = f"  [{m['status_words']}w / cap {scap}]"
        if next_task_para(body) is not None:
            note += "  ← next-task paragraph"
        print(f"  {title[:43]:<44}{klass:<10}"
              f"{GM._size(body):>18} {GM._tok(len(body))}{note}")
    longest = max(text.split("\n"), key=len)
    print(f"  longest physical line: {len(longest):,}c — "
          f"{_first_sentence(longest, 70)}")
    return 0


def cmd_next(disp, text, secs, args):
    """The next concrete task. *Current state* wins a disagreement, per the
    loop's own tie-break ('when it and *Hand-off* both carry a next-task
    pointer, *Current state* is authoritative; the Hand-off copy drifts
    stale') -- but the disagreement is REPORTED rather than silently
    resolved, because a drifted copy is the F17 surface."""
    hits = []
    for title, klass, body in secs:
        p = next_task_para(body)
        if p is not None:
            hits.append((title, p))
    if not hits:
        if not GATE.parse(text)["active"]:
            print(f"{disp}: no next-task sentence — and none is expected, "
                  f"this note is CLOSED.")
            print("  At phase close the forward part shrinks to the "
                  "next-phase hand-off (`notes/CLAUDE.md`).")
            return 0
        print(f"{disp}: NO next-task sentence anywhere in the note.")
        print("  This breaks the hand-off contract (`CLAUDE.md`: ROADMAP.md "
              "plus the active phase note\n  should be enough to identify the "
              "next concrete task without reading a source file\n  or commit "
              "history). Repair the note; do not work around it here.")
        print("  Read the forward sections with --handoff / "
              "--section 'current state' to see what it says instead.")
        return 1
    order = {"current state": 0, "hand": 1}
    hits.sort(key=lambda h: min(
        (v for k, v in order.items() if h[0].lower().startswith(k)), default=2))
    title, para = hits[0]
    print(f"{disp} — next concrete task, from *{title}*")
    _emit("next-task", para, args)
    if len(hits) > 1:
        others = ", ".join(f"*{t}*" for t, _p in hits[1:])
        print(f"  [ALSO carried by {others} — the loop makes *Current state* "
              f"authoritative; reconcile and collapse the duplicate so it "
              f"cannot drift again]")
    return 0


def cmd_section(disp, text, secs, want, args):
    title, klass, body = find_section(secs, want)
    print(f"{disp} — *{title}* ({klass})")
    _emit(title, body, args)
    return 0


def cmd_surfaces(disp, text, secs, args):
    """Every status surface an F17 sweep must touch. Printed as first
    sentences, not full text: the point is to see all of them beside each
    other and notice the one that disagrees."""
    print(f"{disp} — status surfaces an F17 sweep must touch "
          f"(first sentence of each; --section for the whole one)")
    want = [("**Status:** header", "the roster, the counts, the next-task sentence"),
            ("Current state", "authoritative next-task pointer"),
            ("Hand-off", "next-task slot — RE-AIM it, never delete it")]
    for name, why in want:
        try:
            title, _k, body = find_section(secs, name)
        except SystemExit:
            print(f"  MISSING  {name:<22} — {why}")
            continue
        para = next_task_para(body) or body
        print(f"  {title[:22]:<24} {GM._size(body):>16}  {why}")
        print(f"      {_first_sentence(para)}")
    if not any(next_task_para(b) is not None for _t, _k, b in secs):
        print("  ** NO next-task sentence in ANY surface — the hand-off "
              "contract is unmet. **")
    phase = re.search(r"Phase(\d+[a-z]?)", os.path.basename(disp))
    if phase and os.path.isfile(ROADMAP):
        n = phase.group(1)
        rows = [l for l in open(ROADMAP, encoding="utf-8").read().split("\n")
                if l.startswith("|") and re.match(rf"^\|\s*{n}\.", l)]
        print(f"  {'ROADMAP Status cell':<24} "
              f"{'(' + str(len(rows)) + ' row)':>16}  the at-a-glance surface")
        for r in rows:
            cells = r.split("|")
            print(f"      {_first_sentence(cells[3] if len(cells) > 3 else r)}")
    else:
        print("  ROADMAP Status cell      — not resolved from the filename")
    print("  NOTE: the dispatch-scoping file's own header is the fifth "
          "surface (e.g. notes/pencil/CLAUDE.md); it is corpus-specific, so "
          "this reader names it rather than guessing it.")
    return 0


def cmd_selftest(disp, text, secs):
    bad = 0
    total = 0
    for title, _k, body in secs:
        u = GM.units(body)
        total += len(u)
        if "".join("".join(x.split()) for x in u) != "".join(body.split()):
            print(f"  LOSSY split in *{title}*")
            bad += 1
    print(f"{'FAIL' if bad else 'OK'}: {disp} — {len(secs)} sections, "
          f"{total} units, {GM._size(text)}; "
          f"{'split lossless everywhere' if not bad else str(bad) + ' lossy'}")
    return 1 if bad else 0


# ---------------------------------------------------------------- entry

def resolve(name):
    base = os.path.basename(name)
    if not base.endswith(".md"):
        base = f"Phase{base}.md" if base.isdigit() or re.match(
            r"^\d+[a-z]$", base) else base + ".md"
    for cand in (name, os.path.join(_HERE, base), os.path.join(_ROOT, name)):
        if os.path.isfile(cand):
            return cand, os.path.relpath(cand, _ROOT)
    raise SystemExit(f"no such phase note: {name} (looked for {base})")


def main(argv):
    p = argparse.ArgumentParser(
        prog="phasenote.py",
        description="Read one slice of a phase note (the next-task paragraph "
                    "is one 5 900-character line; see the docstring).",
    )
    p.add_argument("note", help="phase note: 39, Phase39.md, or a path")
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--next", action="store_true",
                      help="the next-concrete-task paragraph")
    mode.add_argument("--status", action="store_true",
                      help="the **Status:** header block")
    mode.add_argument("--handoff", action="store_true",
                      help="the *Hand-off / next phase* section")
    mode.add_argument("--section", metavar="TITLE", help="any section by title")
    mode.add_argument("--list", action="store_true",
                      help="section index with sizes")
    mode.add_argument("--surfaces", action="store_true",
                      help="every status surface an F17 sweep must touch")
    mode.add_argument("--selftest", action="store_true",
                      help="audit the sentence split (lossless)")
    p.add_argument("--head", type=int, metavar="N", help="first N units")
    p.add_argument("--tail", type=int, metavar="N", help="last N units")
    p.add_argument("--sentences", metavar="A-B",
                   help="unit range, 1-based inclusive (A-B, A-, -B, A)")
    p.add_argument("--full", action="store_true", help="no window")
    args = p.parse_args(argv)

    path, disp = resolve(args.note)
    with open(path, encoding="utf-8") as f:
        text = f.read()
    secs = sections(text)

    if args.list:
        return cmd_list(disp, text, secs)
    if args.selftest:
        return cmd_selftest(disp, text, secs)
    if args.surfaces:
        return cmd_surfaces(disp, text, secs, args)
    if args.next:
        return cmd_next(disp, text, secs, args)
    if args.status:
        return cmd_section(disp, text, secs, "**Status:** header", args)
    if args.handoff:
        return cmd_section(disp, text, secs, "hand-off", args)
    return cmd_section(disp, text, secs, args.section, args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
