#!/usr/bin/env python3
"""Gate: model-experiment log-row Notes cells must stay within the
signal-only length cap (the protocol's ~600-char rule — now *enforced*,
not merely advised; see notes/model-experiment-protocol.md *Notes
discipline*).

The Notes cell is the experiment-meta *delta* only (calibration,
rubric-fail cause, cost anomaly, cross-task verdict). The recap of what
the commit did lives in the commit message / design § / phase note — so a
cell that needs more than the cap is almost always recapping.

Modes:
  (default)  check only rows whose Notes changed vs HEAD — the rows this
             commit touches. Grandfathered older rows don't block unrelated
             commits; any row you DO touch must pass (incremental migration).
  --all      check every row (full-table audit / a cleanup pass).
  --last     check rows changed in HEAD vs HEAD~1 (post-commit audit).

Exit 1 (and list offenders) if any checked row exceeds the cap.
Run before committing a log row — the coordinate-phase per-commit step
invokes it.
"""
import io
import re
import subprocess
import sys

# Default target: the live exception log. The model-experiment log this gate
# was written for concluded (its rows are frozen in
# notes/model-experiment-archive.md), so pointing here by default is what makes
# the gate actually gate something -- it silently reported "0 row(s) checked"
# against the empty pointer file from the day the experiment closed until
# 2026-09-03, so its ~600-char cap had never once been enforced.
# Override with --file <path> (e.g. the archive) to check another log.
PATH = "notes/dispatch-log.md"
CAP = 600
# A row's first cell is a date (dispatch log) or an ordinal (experiment log).
ROW_RE = re.compile(r"^\| (\d{4}-\d{2}-\d{2}|\d+) \|")
PIPE = re.compile(r"(?<!\\)\|")  # a column delimiter is an UNescaped pipe


SEP_RE = re.compile(r"^\|(?:\s*:?-{3,}:?\s*\|)+\s*$")


def ncols_of(text):
    """Column count, read off the table's own header separator row.

    Derived rather than hard-coded because this gate serves two logs with
    different shapes (the dispatch log has 5 columns, the model-experiment log
    9). Hard-coding 9 is what silently disabled it against the dispatch log."""
    for line in text.splitlines():
        if SEP_RE.match(line):
            return len([c for c in PIPE.split(line)[1:-1]])
    return None


def notes_cell(line, ncols):
    """Notes (last) cell of a log row, or None if the line isn't a row.

    Splits on unescaped pipes only and takes everything between the
    `ncols`-th delimiter and the row-end pipe, so literal pipes inside Notes
    (|V|, |E|) and escaped pipes elsewhere (\\|V\\|) are measured / handled
    correctly rather than truncating the cell at the first interior pipe. The
    fixed index is what makes interior pipes safe -- do not "generalize" this
    to the last-two-delimiters, which breaks on exactly those rows."""
    s = line.rstrip("\n")
    pos = [m.start() for m in PIPE.finditer(s)]
    if len(pos) < ncols + 1:  # need the structural delimiters of a full row
        return None
    return s[pos[ncols - 1] + 1 : pos[-1]].strip()


def rows_of(text):
    out = {}
    ncols = ncols_of(text)
    if ncols is None:
        return out
    for line in text.splitlines():
        m = ROW_RE.match(line)
        if m:
            nc = notes_cell(line, ncols)
            if nc is not None:
                # Key by the row's non-Notes cells: unique in practice, and
                # robust to insertion in a way a line index would not be.
                cells = [c.strip() for c in PIPE.split(line)]
                out[tuple(cells[:-2])] = nc
    return out


def git_show(ref):
    try:
        return subprocess.run(
            ["git", "show", f"{ref}:{PATH}"],
            capture_output=True, text=True, check=True,
        ).stdout
    except Exception:
        return None


def main(argv):
    global PATH
    if "--file" in argv:
        PATH = argv[argv.index("--file") + 1]
    if "--all" in argv:
        with io.open(PATH, encoding="utf-8") as f:
            cur = rows_of(f.read())
        check, label = set(cur), "full table"
    elif "--last" in argv:
        head, prev = git_show("HEAD"), git_show("HEAD~1")
        if head is None:
            print("cannot read HEAD copy of the log", file=sys.stderr)
            return 2
        cur = rows_of(head)
        base = rows_of(prev) if prev is not None else {}
        check = {n for n, v in cur.items() if base.get(n) != v}
        label = "changed HEAD~1..HEAD"
    else:
        with io.open(PATH, encoding="utf-8") as f:
            cur = rows_of(f.read())
        head = git_show("HEAD")
        if head is None:
            check = set(cur)  # no committed base → check all
        else:
            base = rows_of(head)
            check = {n for n, v in cur.items() if base.get(n) != v}
        label = "changed vs HEAD"

    bad = [(n, len(cur[n])) for n in sorted(check) if len(cur[n]) > CAP]
    bad = [((" | ".join(str(x) for x in n))[:90], c) for n, c in bad]
    if bad:
        print(
            f"FAIL: {len(bad)} log row(s) exceed the {CAP}-char Notes cap "
            f"(protocol *Notes discipline*):",
            file=sys.stderr,
        )
        for n, length in bad:
            print(f"  row {n}: {length} chars (+{length - CAP})", file=sys.stderr)
        print(
            "Compress to the experiment-meta delta — the commit message carries "
            "the recap — before committing.",
            file=sys.stderr,
        )
        return 1
    print(f"OK: {len(check)} row(s) checked ({label}); all within {CAP} chars.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
