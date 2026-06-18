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

PATH = "notes/model-experiment.md"
CAP = 600
ROW_RE = re.compile(r"^\| (\d+) \|")
PIPE = re.compile(r"(?<!\\)\|")  # a column delimiter is an UNescaped pipe


def notes_cell(line):
    """Notes (last) cell of a log row, or None if the line isn't a row.

    Splits on unescaped pipes only and takes everything between the 9th
    delimiter and the row-end pipe, so literal pipes inside Notes (|V|, |E|)
    and escaped pipes in the Task (\\|V\\|) are measured / handled correctly
    rather than truncating the cell at the first interior pipe."""
    s = line.rstrip("\n")
    pos = [m.start() for m in PIPE.finditer(s)]
    if len(pos) < 10:  # need the 10 structural delimiters of a 9-column row
        return None
    return s[pos[8] + 1 : pos[-1]].strip()


def rows_of(text):
    out = {}
    for line in text.splitlines():
        m = ROW_RE.match(line)
        if m:
            nc = notes_cell(line)
            if nc is not None:
                out[int(m.group(1))] = nc
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
