#!/usr/bin/env python3
"""Gate: every `<driver>.py --<flag>` cited in prose must be a flag that
driver actually declares.

Why this exists. `notes/pencil/strategy.md` section 8 is *the* surface a fresh
session reads to choose a direction, and on 2026-09-10 its rank-2 entry named
`packmm.py --hier` when that mode lives in `gridcol.py`. The coordinator's own
diagnosis recorded the defect on ONE surface; direction GCOIND found **four**,
two of them body prose in `grid.md` (`notes/Harness-structure.md` D6.5,
`notes/dispatch-log.md` 2026-09-10). A prose driver-mode citation is a
**mechanically checkable** class of error that no gate covered -- section 8's
own thesis is *gate a surface and it stays correct*, applied here to the one
part of a recommendation that is machine-decidable.

It checks only what it can decide. A citation whose driver cannot be resolved
is reported UNRESOLVED and does not fail the tree -- the driver may have been
renamed or retired, and inventing a verdict about a file that is not there is
the error this project keeps refusing to make.

Flag extraction handles both shapes the harness uses:

  * `ap.add_argument('--mode', ...)`            -- an argparse literal
  * `for f in ('branch', 'hier', ...):`         -- the argparse house pattern,
        `ap.add_argument('--' + f, ...)`           names in the loop's iterable
  * `if '--conj' in sys.argv:`                  -- a bare flag literal

None of the three is an edge case. `gridcol.py` and `packmm.py`, the two
drivers in the original defect, BOTH declare every mode through the loop, so a
checker reading only literal `add_argument` calls finds nothing and reports the
tree clean. And the third shape is the MAJORITY here: only 38 of 143 drivers
use argparse at all, so a checker that knew argparse alone would have failed
most of the tree's correct citations -- red at baseline, hence switched off
rather than obeyed (D6.7).

A driver from which no long flag of any shape can be read is UNDECIDABLE: its
citations are reported, never failed.

Modes:
A line of prose ABOUT a flag -- proposing one, or reporting a past
mis-citation -- carries `<!--driver-refs:exempt-->` and is skipped. The marker
is greppable on purpose.

  (default)  check citations in files changed vs HEAD
  --all      every citation in the tree
  --ref SHA  check the tree as of a git ref (for reproducing a past defect)
  --selftest reproduce the 2026-09-10 defect at its own baseline

Usage (from the repo root):

    python3 notes/check-driver-refs.py --all
    python3 notes/check-driver-refs.py --selftest
"""

import argparse
import ast
import glob
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# `packmm.py --hier`, `notes/scripts/w4/gridcol.py --wide`, `ledger.py --label`.
CITE = re.compile(r"([A-Za-z_][A-Za-z0-9_./-]*\.py)\s+(--[a-z][a-z0-9-]*)")
PROSE = ["notes/**/*.md", "notes/*.md", ".claude/**/*.md", "*.md"]

# Prose ABOUT a flag -- a proposal for one not built yet, or a report of a
# past mis-citation -- is not a citation OF it. Such a line carries this
# marker. It is deliberately ugly and greppable
# (`grep -rn 'driver-refs:exempt' notes/`) so an exemption can never quietly
# accumulate: the gate's value is that a wrong mode name cannot survive, and
# a silent suppression convention would give that back.
EXEMPT = "<!--driver-refs:exempt-->"
SKIP_DIRS = (".ledger-cache",)


FLAGLIT = re.compile(r"^--[a-z][a-z0-9-]*$")


def _flags_of(src):
    """Every long flag a driver declares, all three shapes it uses here."""
    out = set()
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return out

    # module-level string sequences, so `for m in MODES:` can be resolved.
    # `MODES = ('unfence', 'reform', 'r4', ...)` at module scope, fed to
    # `add_argument('--' + mode)`, is a FOURTH shape and a common one -- it is
    # how `gcoind.py` and its siblings declare every mode they have.
    consts = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for t in node.targets:
                if not isinstance(t, ast.Name):
                    continue
                try:
                    v = ast.literal_eval(node.value)
                except Exception:
                    continue
                if isinstance(v, (tuple, list, set)) and v and all(
                        isinstance(x, str) for x in v):
                    consts[t.id] = set(v)

    def strings_of(node):
        """The string set a `for` iterable denotes: a literal, a module
        constant, or a `+` of those. `for f in MODES + ('validate',):` is
        real code here (`gforce.py`), and missing it left that driver with
        NO readable flags at all."""
        if isinstance(node, ast.Name):
            return consts.get(node.id)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            l, r = strings_of(node.left), strings_of(node.right)
            return (l | r) if (l is not None and r is not None) else None
        try:
            lit = ast.literal_eval(node)
        except Exception:
            return None
        if isinstance(lit, (tuple, list, set)) and all(
                isinstance(v, str) for v in lit):
            return set(lit)
        return None

    # shape 2: map a loop variable to the string literals it ranges over.
    loopvars = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.For) and isinstance(node.target, ast.Name):
            vals = strings_of(node.iter)
            if vals:
                loopvars.setdefault(node.target.id, set()).update(vals)

    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call)
                and getattr(node.func, "attr", None) == "add_argument"):
            continue
        for arg in node.args:
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                if arg.value.startswith("--"):
                    out.add(arg.value)
            elif isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Add):
                # `'--' + f`
                lhs, rhs = arg.left, arg.right
                if (isinstance(lhs, ast.Constant) and lhs.value == "--"
                        and isinstance(rhs, ast.Name)):
                    out.update("--" + v for v in loopvars.get(rhs.id, ()))
            elif isinstance(arg, ast.JoinedStr):
                # `f'--{mode}'` -- the commoner spelling of the same thing,
                # and the one `gcoind.py` and `gbal.py` use for EVERY mode
                # they have. Reading only the `+` form left both reporting
                # just `--validate`, and every correct citation of them
                # failing.
                parts = arg.values
                if (len(parts) == 2
                        and isinstance(parts[0], ast.Constant)
                        and parts[0].value == "--"
                        and isinstance(parts[1], ast.FormattedValue)
                        and isinstance(parts[1].value, ast.Name)):
                    out.update("--" + v
                               for v in loopvars.get(parts[1].value.id, ()))
        for kw in node.keywords:          # choices= on a --flag
            if kw.arg == "choices":
                try:
                    for v in ast.literal_eval(kw.value):
                        if isinstance(v, str) and v.startswith("--"):
                            out.add(v)
                except Exception:
                    pass

    # shape 3, and it is the MAJORITY: only 38 of this tree's 143 drivers use
    # argparse at all. The house CLI is `if '--conj' in sys.argv:` -- so any
    # module-level string literal shaped like a long flag counts. This
    # over-collects a little (a `--flag` quoted inside a help string is
    # indistinguishable) and that is the RIGHT direction for a gate: a false
    # pass costs a missed prose typo, a false FAIL costs the gate's
    # credibility and it gets switched off (D6.7).
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if FLAGLIT.match(node.value):
                out.add(node.value)
    return out


def _read(path, ref):
    if ref:
        r = subprocess.run(["git", "show", f"{ref}:{path}"],
                           capture_output=True, text=True, cwd=ROOT)
        return r.stdout if r.returncode == 0 else None
    full = os.path.join(ROOT, path)
    if not os.path.isfile(full):
        return None
    try:
        return open(full, encoding="utf-8").read()
    except Exception:
        return None


def _drivers(ref):
    """basename -> path, for every .py under the tree (drivers and tools)."""
    if ref:
        r = subprocess.run(["git", "ls-tree", "-r", "--name-only", ref],
                           capture_output=True, text=True, cwd=ROOT)
        paths = [p for p in r.stdout.split("\n") if p.endswith(".py")]
    else:
        paths = [os.path.relpath(p, ROOT)
                 for pat in ("notes/**/*.py", "*.py", "scripts/**/*.py")
                 for p in glob.glob(os.path.join(ROOT, pat), recursive=True)]
    out = {}
    for p in paths:
        if any(d in p for d in SKIP_DIRS):
            continue
        out.setdefault(os.path.basename(p), []).append(p)
    return out


def _prose_files(ref, only=None):
    if only is not None:
        return [p for p in only if p.endswith(".md")]
    if ref:
        r = subprocess.run(["git", "ls-tree", "-r", "--name-only", ref],
                           capture_output=True, text=True, cwd=ROOT)
        return [p for p in r.stdout.split("\n")
                if p.endswith(".md") and not any(d in p for d in SKIP_DIRS)]
    seen = []
    for pat in PROSE:
        for p in glob.glob(os.path.join(ROOT, pat), recursive=True):
            rel = os.path.relpath(p, ROOT)
            if rel not in seen and not any(d in rel for d in SKIP_DIRS):
                seen.append(rel)
    return seen


def _changed():
    r = subprocess.run(["git", "diff", "--name-only", "HEAD"],
                       capture_output=True, text=True, cwd=ROOT)
    s = subprocess.run(["git", "diff", "--cached", "--name-only"],
                       capture_output=True, text=True, cwd=ROOT)
    return sorted({p for p in (r.stdout + s.stdout).split("\n") if p.strip()})


def run(ref=None, only=None, quiet=False):
    drivers = _drivers(ref)
    cache = {}
    bad, unresolved, n = [], [], 0
    for path in _prose_files(ref, only):
        text = _read(path, ref)
        if text is None:
            continue
        for i, line in enumerate(text.split("\n"), 1):
            if EXEMPT in line:
                continue
            for name, flag in CITE.findall(line):
                n += 1
                base = os.path.basename(name)
                cands = drivers.get(base)
                if not cands:
                    unresolved.append((path, i, base, flag))
                    continue
                if base not in cache:
                    fl = set()
                    for c in cands:
                        src = _read(c, ref)
                        if src:
                            fl |= _flags_of(src)
                    cache[base] = (fl, cands)
                flags, where = cache[base]
                if not flags:
                    # No long flag of any shape: the driver takes none, or
                    # builds them in a way this cannot read. Undecidable, so
                    # report and move on rather than fail the tree.
                    unresolved.append((path, i, base, flag))
                    continue
                if flag not in flags:
                    bad.append((path, i, base, flag, where, sorted(flags)))
    if not quiet:
        print(f"{n} driver-mode citation(s) checked"
              f"{' at ' + ref if ref else ''}"
              f" across {len(_prose_files(ref, only))} prose file(s).")
        for path, i, base, flag, where, flags in bad:
            owner = [d for d, (f, _w) in cache.items() if flag in f]
            print(f"  FAIL {path}:{i}  `{base} {flag}` — {base} "
                  f"({', '.join(where)}) declares no {flag}", file=sys.stderr)
            if owner:
                print(f"       {flag} IS declared by: {', '.join(owner)}",
                      file=sys.stderr)
            print(f"       {base} has: "
                  f"{' '.join(flags) if flags else '(no long flags found)'}",
                  file=sys.stderr)
        if unresolved:
            u = sorted({(b, f) for _p, _i, b, f in unresolved})
            print(f"  {len(unresolved)} citation(s) name a .py this tree does "
                  f"not have — reported, not failed: "
                  f"{', '.join(f'{b} {f}' for b, f in u[:6])}"
                  f"{' …' if len(u) > 6 else ''}")
    return bad, unresolved, n


def selftest():
    """Reproduce the 2026-09-10 defect at its own baseline.

    `strategy.md` section 8 named `packmm.py --hier` at `c8efb227`; the mode is
    `gridcol.py`'s. Both drivers declare their modes through the loop shape, so
    this doubles as the test that the non-literal extractor works -- a checker
    reading only literal `add_argument` strings finds nothing here.
    """
    fails = []
    src = _read("notes/scripts/w4/packmm.py", None) or ""
    pk = _flags_of(src)
    if "--hier" in pk:
        fails.append("  packmm.py should NOT declare --hier")
    if "--sep" not in pk:
        fails.append("  packmm.py --sep not extracted (loop shape broken)")
    gc = _flags_of(_read("notes/scripts/w4/gridcol.py", None) or "")
    if "--hier" not in gc:
        fails.append("  gridcol.py --hier not extracted (loop shape broken)")
    bad, _u, n = run(ref="c8efb227", quiet=True)
    hits = [b for b in bad if b[2] == "packmm.py" and b[3] == "--hier"]
    if not hits:
        fails.append("  the c8efb227 `packmm.py --hier` defect was NOT caught")
    if n < 100:
        fails.append(f"  only {n} citations found at c8efb227; extractor broken")
    if fails:
        print("FAIL: check-driver-refs selftest", file=sys.stderr)
        print("\n".join(fails), file=sys.stderr)
        return 1
    print(f"OK: selftest — the 2026-09-10 `packmm.py --hier` defect reproduces "
          f"at c8efb227 ({len(hits)} site(s)), and both drivers' loop-declared "
          f"modes extract.")
    return 0


def main(argv):
    p = argparse.ArgumentParser(prog="check-driver-refs.py",
                                description=__doc__.split("\n")[0])
    p.add_argument("--all", action="store_true", help="every citation")
    p.add_argument("--ref", metavar="SHA", help="check the tree at a git ref")
    p.add_argument("--selftest", action="store_true",
                   help="reproduce the 2026-09-10 defect at its baseline")
    a = p.parse_args(argv)
    if a.selftest:
        return selftest()
    only = None if (a.all or a.ref) else _changed()
    if only is not None and not [q for q in only if q.endswith(".md")]:
        print("OK: no prose file changed vs HEAD; nothing to check "
              "(--all for the tree).")
        return 0
    bad, _u, _n = run(a.ref, only)
    if bad:
        print(f"\nFAIL: {len(bad)} prose citation(s) name a flag the driver "
              f"does not declare. Fix the prose, or the driver.", file=sys.stderr)
        return 1
    print("OK: every resolvable driver-mode citation matches a declared flag.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
