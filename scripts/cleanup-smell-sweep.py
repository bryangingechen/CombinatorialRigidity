#!/usr/bin/env python3
"""Count `CLEANUP.md` §B's code smells over a cleanup round's Lean surface.

Usage (run from the repo root):
    python3 scripts/cleanup-smell-sweep.py --base <rev> --rev <rev> --tree <dir> [--by-file]
    python3 scripts/cleanup-smell-sweep.py ... --sites <smell>

The surface is two parts, read from git at ``--rev`` (not from the working tree):

- every line of every ``.lean`` file under ``--tree``;
- in every other ``.lean`` file under ``CombinatorialRigidity/`` that ``git diff --no-renames
  <base> <rev>`` touches, only the ``+`` side of ``git diff -U0 <base> <rev> -- <file>``, i.e. the
  lines added since ``--base``. Files deleted by ``<rev>`` are skipped.

The patterns are §B's greps, plus ``maxHeartbeats`` and two proxies for §B's manual rows
(``toFinset`` for *Set vs Finset mixing*, ``Fintype.card`` for *Manual Fintype.card chains*).
They were fixed at the post-Phase-40 round's open (`notes/Phase40-cleanup.md`) and must not change,
or before/after figures stop being comparable. Two deviations from §B's literal text, both from
the open: the ``classical`` line pattern allows trailing whitespace, and the ``letI``/``haveI`` row
groups ``(letI|haveI)`` before ``.*`` (§B's grep, once its markdown ``\\|`` table escapes are
undone, would match every ``letI``).

``--sites <smell>`` prints each file's matching line numbers for one smell (at ``--rev``).

Post-Phase-40 round 1 (`40-cleanup`; figures in `notes/Phase40-cleanup.md` task 45):
    open:  --base 'c9d26ef9^' --rev 91fcd24a --tree CombinatorialRigidity/Molecular/Molecule/Pencil/
    close: --base 'c9d26ef9^' --rev c3b6d83a --tree (same)
"""
import argparse
import collections
import re
import subprocess

SMELLS = collections.OrderedDict([
    ("classical", r"^\s*classical\s*$|^\s*classical *--"),
    ("haveI-Fintype", r"(letI|haveI).*(Fintype\.ofFinite|Set\.Finite\.fintype)"),
    ("nolint/linter", r"@\[nolint|set_option linter"),
    ("noncomputable-def", r"noncomputable def"),
    ("change/show", r"^\s*(change|show)\b"),
    ("rw4+", r"rw \[[^]]*,[^]]*,[^]]*,[^]]*\]"),
    ("show-from-rfl", r"show .* from rfl"),
    ("maxHeartbeats", r"maxHeartbeats"),
    ("toFinset", r"toFinset|ncard_coe_finset|ncard_eq_toFinset_card"),
    ("Fintype.card", r"Fintype\.card"),
])

HUNK = re.compile(r"^@@ -\S+ \+(\d+)(?:,(\d+))? @@", re.M)


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def added_lines(base, rev, path):
    out = git("diff", "--no-renames", "-U0", base, rev, "--", path)
    keep = set()
    for m in HUNK.finditer(out):
        start = int(m.group(1))
        count = int(m.group(2)) if m.group(2) is not None else 1
        keep.update(range(start, start + count))
    return keep


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--base", required=True)
    ap.add_argument("--rev", required=True)
    ap.add_argument("--tree", required=True)
    ap.add_argument("--by-file", action="store_true")
    ap.add_argument("--sites", choices=list(SMELLS))
    a = ap.parse_args()
    tree = a.tree.rstrip("/") + "/"

    inside = [f for f in git("ls-tree", "-r", "--name-only", a.rev, "--", tree).split()
              if f.endswith(".lean")]
    touched = git("diff", "--no-renames", "--name-only", "--diff-filter=d", a.base, a.rev,
                  "--", "CombinatorialRigidity/").split()
    outside = [f for f in touched if f.endswith(".lean") and not f.startswith(tree)]

    rows = []
    for f in inside + outside:
        lines = git("show", f"{a.rev}:{f}").split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        keep = None if f in inside else added_lines(a.base, a.rev, f)
        hits = collections.OrderedDict((k, []) for k in SMELLS)
        for i, line in enumerate(lines, 1):
            if keep is not None and i not in keep:
                continue
            for k, p in SMELLS.items():
                if re.search(p, line):
                    hits[k].append(i)
        rows.append((f, keep is None, len(lines), None if keep is None else len(keep), hits))

    if a.sites:
        for f, _, _, _, hits in rows:
            if hits[a.sites]:
                print(f, hits[a.sites])
        return

    def short(f):
        return f.replace("CombinatorialRigidity/", "")

    if a.by_file:
        print("file | lines | counted | " + " | ".join(SMELLS))
        for f, ins, n, k, hits in rows:
            print(f"{short(f)} | {n} | {'all' if ins else k} | "
                  + " | ".join(str(len(v)) for v in hits.values()))
        print()

    n_in = sum(1 for r in rows if r[1])
    lines_in = sum(r[2] for r in rows if r[1])
    n_out = sum(1 for r in rows if not r[1])
    lines_out = sum(r[3] for r in rows if not r[1])
    print(f"surface at {a.rev}: {tree} {n_in} files / {lines_in} lines (every line); "
          f"{n_out} other files / {lines_out} lines added since {a.base}")
    print("smell | tree | other | total")
    for k in SMELLS:
        t_in = sum(len(r[4][k]) for r in rows if r[1])
        t_out = sum(len(r[4][k]) for r in rows if not r[1])
        print(f"{k} | {t_in} | {t_out} | {t_in + t_out}")


if __name__ == "__main__":
    main()
