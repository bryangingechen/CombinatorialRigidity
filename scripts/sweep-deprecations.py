#!/usr/bin/env python3
"""Apply mathlib's deprecation renames across the tree, driven by a build log.

Usage:
    LAKE_CACHE_DIR=<writable-dir> lake build > build.log 2>&1   # see notes/ToolchainBumps.md
    python3 scripts/sweep-deprecations.py build.log             # dry run
    python3 scripts/sweep-deprecations.py build.log --apply     # write

Why a *log*-driven sweep and not a regex over the tree
------------------------------------------------------
Lean's deprecation warning names the *fully qualified* old constant
(``Set.mem_setOf_eq``) but its ``file:line:col`` points at the identifier
**as written in the source**, which is very often the unqualified suffix
(``mem_setOf_eq``, under an ``open Set``). A regex over the qualified name
would silently miss every such site -- in the v4.34.0-rc1 sweep that was
*all* 158 ``Set.mem_setOf_eq`` uses. Editing at the reported position
instead is exact: no boundary heuristics, no false positives inside longer
identifiers (``if_pos`` inside ``dif_pos``), and unqualified uses are
rewritten to the correspondingly unqualified new name.

One position the log cannot give you
-----------------------------------
When the deprecated name sits inside a ``grind only [!a, !b, ...]`` list, Lean
reports the warning at the position of the **``grind`` token**, not the
identifier (which may be lines away). A position-driven sweep cannot fix those:
the script reports them as skips and they are fixed by hand. Expect roughly one
per sweep -- the v4.34.0-rc1 sweep had exactly one, at ``Henneberg.lean:445``.

Renames can also make a line too long
-------------------------------------
``if_neg`` -> ``ite_eq_right`` is six characters longer, and the
``Set.diff_*`` -> ``Set.sdiff_*`` / ``*setOf*`` -> ``*ofPred*`` families one.
Thirteen lines crossed mathlib's 100-character limit in the v4.34.0-rc1 sweep.
The style linter -- i.e. a full ``lake build`` after the sweep -- is what tells
you; the sweep itself cannot.

What is deliberately NOT swept
------------------------------
``EXCLUDED`` below lists renames whose replacement has a *different type*, so
substituting the name is not enough (Lean reports these with a
``Note: The updated constant has a different type:`` line). They need
hand-inspection; the script prints them as a reminder instead of touching
them. Re-derive the list after a bump by grepping the build log for that
note -- do not trust this list to still be complete.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from pathlib import Path

# Renames whose replacement has a different type -- excluded from the sweep.
# Keep the reason with the name; it is what a future reader needs.
EXCLUDED = {
    "SimpleGraph.isClique_iff_induce_eq":
        "the iff is FLIPPED (`induce s G = ⊤ ↔ G.IsClique s`)",
    "cond_true": "argument explicitness changed (explicit -> implicit)",
    "cond_false": "argument explicitness changed (explicit -> implicit)",
}

WARNING = re.compile(
    r"^warning: (?P<file>[^:]+):(?P<line>\d+):(?P<col>\d+): "
    r"`(?P<old>[^`]+)` has been deprecated: Use `(?P<new>[^`]+)` instead\s*$"
)

# A Lean identifier component. Deliberately permissive: Lean allows unicode
# letters, `_`, `'`, `!`, `?` and digits in names.
IDENT_CHAR = re.compile(r"[^\s(){}\[\],:;`\"@$%^&*+=<>/\\|~#-]")


def ident_at(line: str, col: int) -> str:
    """The identifier token starting at 0-indexed codepoint `col`."""
    end = col
    while end < len(line) and IDENT_CHAR.match(line[end]):
        end += 1
    return line[col:end]


def as_written(token: str, old: str) -> str | None:
    """The prefix of `token` that is an as-written form of `old`, if any.

    The token at a warning's position can carry a trailing projection --
    `Set.subset_diff.mpr`, `diff_subset.trans` -- so match the longest
    dot-prefix rather than the whole token.
    """
    parts = token.split(".")
    for depth in range(len(parts), 0, -1):
        cand = ".".join(parts[:depth])
        if cand == old or old.endswith("." + cand):
            return cand
    return None


def replacement_for(old: str, new: str, written: str) -> str | None:
    """The text to substitute for `written`, an as-written form of `old`.

    Preserves the qualification depth the author used: a site that wrote
    `mem_setOf_eq` for `Set.mem_setOf_eq` gets `mem_ofPred_eq`, not the fully
    qualified `Set.mem_ofPred_eq` (the `open Set` that made the short form
    resolve is still in scope). Returns None when that cannot be done safely.
    """
    if written != old and not old.endswith("." + written):
        return None  # position does not hold an as-written form of `old`
    depth = written.count(".") + 1
    old_ns = old.rsplit(".", 1)[0] if "." in old else ""
    new_ns = new.rsplit(".", 1)[0] if "." in new else ""
    if old_ns != new_ns:
        # The namespace itself moved (`cond_true` -> `Bool.cond_true`): a
        # suffix of the new name need not resolve. Use the full name.
        return new
    parts = new.split(".")
    if depth > len(parts):
        return new
    return ".".join(parts[len(parts) - depth:])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", type=Path, help="a `lake build` log with the deprecation warnings")
    ap.add_argument("--apply", action="store_true", help="write the edits (default: dry run)")
    args = ap.parse_args()

    if not args.log.is_file():
        print(f"no such log: {args.log}", file=sys.stderr)
        return 2

    # (file, line, col) -> (old, new, written). Dedup: a warning can be
    # replayed by several build jobs.
    sites: dict[tuple[str, int, int], tuple[str, str]] = {}
    excluded_hits: Counter[str] = Counter()
    for raw in args.log.read_text(encoding="utf-8", errors="replace").splitlines():
        m = WARNING.match(raw)
        if not m:
            continue
        old, new = m["old"], m["new"]
        if old in EXCLUDED:
            excluded_hits[old] += 1
            continue
        sites[(m["file"], int(m["line"]), int(m["col"]))] = (old, new)

    edits: dict[str, list[tuple[int, int, str, str]]] = {}
    skipped: list[str] = []
    renames: Counter[str] = Counter()
    for (fname, lineno, col), (old, new) in sites.items():
        path = Path(fname)
        if not path.is_file():
            skipped.append(f"{fname}:{lineno}:{col}: file not found")
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        if lineno > len(lines):
            skipped.append(f"{fname}:{lineno}:{col}: past end of file")
            continue
        token = ident_at(lines[lineno - 1], col)
        written = as_written(token, old) if token else None
        repl = replacement_for(old, new, written) if written else None
        if written is None or repl is None:
            skipped.append(f"{fname}:{lineno}:{col}: expected `{old}`, found `{token}`")
            continue
        edits.setdefault(fname, []).append((lineno, col, written, repl))
        renames[f"{old} -> {new}"] += 1

    total = sum(len(v) for v in edits.values())
    for fname in sorted(edits):
        per_line: dict[int, list[tuple[int, str, str]]] = {}
        for lineno, col, written, repl in edits[fname]:
            per_line.setdefault(lineno, []).append((col, written, repl))
        path = Path(fname)
        lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        for lineno in sorted(per_line):
            idx = lineno - 1
            # Right-to-left so earlier columns stay valid.
            for col, written, repl in sorted(per_line[lineno], reverse=True):
                lines[idx] = lines[idx][:col] + repl + lines[idx][col + len(written):]
        if args.apply:
            path.write_text("".join(lines), encoding="utf-8")
        print(f"{'wrote' if args.apply else 'would edit'} {fname}: "
              f"{len(edits[fname])} rename(s) on {len(per_line)} line(s)")

    print()
    for pair, n in renames.most_common():
        print(f"  {n:4d}  {pair}")
    print(f"\n{total} rename(s) across {len(edits)} file(s)"
          f"{' -- WRITTEN' if args.apply else ' (dry run; pass --apply to write)'}")

    if excluded_hits:
        print("\nNOT swept (replacement has a different type -- fix by hand):")
        for name, n in excluded_hits.most_common():
            print(f"  {n:4d}  {name}: {EXCLUDED[name]}")
    if skipped:
        print(f"\n{len(skipped)} site(s) skipped:")
        for s in skipped:
            print(f"  {s}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
