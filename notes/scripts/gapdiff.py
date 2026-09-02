#!/usr/bin/env python3
"""Scripted label set-diff for a `notes/Pencil-informal.md` gap-map row.

Why this exists.  F21 requires that a gap-map row recomputed during a landing
**preserve every label it already cited** -- a recompute compresses prose, and
the failure mode is dropping a `(BE-nn)` code along with the sentence that
carried it.  Checking that by eye does not scale past ~100 codes, and the
2026-09-02 BDOUBLE landing recorded that its own probe **was not retained**,
so the next landing had to write one again.  This is that script, kept.

Usage (from the repo root):

    python3 notes/scripts/gapdiff.py [gap-key] [git-ref]

Default `gap-key` is `K-bare`; default `git-ref` is `HEAD`.  It compares the
label set of that row's status cell at `git-ref` against the working tree's,
and exits 1 if any label was DROPPED.  Labels ADDED are reported, never an
error -- a landing is expected to add its own.

What counts as a label (one regex, stated so the number is reproducible):
a parenthesised token of the form `(XX-yyy)` -- an initial capital, then any
run of alphanumerics containing at least one hyphen -- so `(BE-45)`, `(GR-15)`,
`(CH-1)`, `(K-tight)`, `(K-bare-ext)`, `(NO-DOUBLE-PENCIL)` and
`(PENCIL-SATURATES-GEN)` all count, and a bare `(i)`/`(+)`/`(ii)` does not.
A sub-part immediately following a code -- `(BE-45)(ii)` -- is ALSO recorded,
as the finer token `BE-45(ii)`, so a recompute that keeps `(BE-45)` while
silently dropping the `(ii)` it cited is still caught.

The row is located with `check-gapmap-cells.py`'s own parser
(`iter_row_cells`), so this script and the cap gate agree on what a row and a
cell are.  No figure in either workbook is produced here: this is a gate.
"""

import importlib.util
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GATE = os.path.join(ROOT, 'notes', 'check-gapmap-cells.py')
DOC = os.path.join('notes', 'Pencil-informal.md')

CODE = re.compile(r"\(([A-Z][A-Za-z0-9′+]*(?:-[A-Za-z0-9′+]+)+)\)"
                  r"(\((?:[ivx]+|\+|[a-z]\d?|[A-Z]\d?)\))?")


def _gate():
    spec = importlib.util.spec_from_file_location('gapgate', GATE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def labels_of(text, key, gate):
    for _lineno, k, _c1, _c2, _kind, cells in gate.iter_row_cells(text):
        if k != key:
            continue
        cell = ' '.join(cells)
        out = set()
        for m in CODE.finditer(cell):
            out.add(m.group(1))
            if m.group(2):
                out.add(m.group(1) + m.group(2))
        return out, len(cell.split())
    return None, None


def main(argv):
    key = argv[1] if len(argv) > 1 else 'K-bare'
    ref = argv[2] if len(argv) > 2 else 'HEAD'
    gate = _gate()
    old_text = subprocess.run(['git', 'show', f'{ref}:{DOC}'], cwd=ROOT,
                              capture_output=True, text=True, check=True).stdout
    new_text = open(os.path.join(ROOT, DOC)).read()
    old, oldw = labels_of(old_text, key, gate)
    new, neww = labels_of(new_text, key, gate)
    if old is None or new is None:
        print(f'FAIL: gap row `{key}` not found '
              f'({"at " + ref if old is None else "in the working tree"})')
        return 1
    dropped = sorted(old - new)
    added = sorted(new - old)
    print(f'gap row `{key}`  ({ref} -> working tree)')
    print(f'  words : {oldw} -> {neww}   ({neww - oldw:+d})')
    print(f'  labels: {len(old)} in, {len(new)} out, '
          f'{len(dropped)} DROPPED, {len(added)} added')
    if added:
        print('  added  : ' + ', '.join(added))
    if dropped:
        print('  DROPPED: ' + ', '.join(dropped))
        print('FAIL: a recompute must not drop a label the row already cited.')
        return 1
    print('OK: zero dropped.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
