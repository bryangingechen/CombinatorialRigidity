#!/usr/bin/env python3
"""List a driver's BLIND AXES: the knobs its own code fixes, so a dispatch can
see in one call what the harness makes it impossible to vary.

Why this exists. `RESEARCH-ARC.md` section 4 instructs *grep the generator for
hardcoded constants*, and that instruction has the best yield-per-word of any
in the loop -- it produced BOTH decisive prep findings of the 2026-09-09
session. It also has no tool, so `notes/Harness-structure.md` D6.4 records the
asymmetry that makes it worth automating: **the rule is promoted and the
reading is manual, so the rule is obeyed exactly as often as a coordinator
remembers to spend twelve calls on it.** This is those twelve calls.

The two findings it must reproduce, both landed:

  * `cflank.LAM6_PLAN = ((6, 9, 1),)` fences the `Λ != ∅` sweep at `|Λ| <= 1`
    -- 24 846 of 142 740 length tuples, 82.6% unswept -- while
    `length_tuples(M, tgt, lamcap=99)` already TAKES the parameter.
  * `gridcol.collapse_search(..., want=1)` returns at the first certificate,
    so a quoted "257 co-independent 4-partitions of 20 967" was a truncation
    artifact; un-fenced it is 3 128 of 175 275, 1 536 certifying.

Both are the BNONUNI shape -- *a hardcoded constant reads like harness
architecture and is usually a keyword argument away from being an axis.*

What it reports, most suspicious first:

  LIMITERS      a parameter with a literal default that also appears in a
                comparison or a break/return guard. `want=1` is one. This is
                the sharpest class: the default does not merely configure, it
                STOPS the search.
  CONSTANTS     module-level assignments to literal values. `LAM6_PLAN` is
                one; its call sites are listed beside it, since a constant
                nothing reads is not a fence.
  DEFAULTS      every other keyword parameter with a literal default -- the
                permissive ones matter too, because a fence is often a CALL
                SITE passing something narrower than the default.
  FENCED CALLS  a call passing a literal to a keyword whose default differs.
                This is `lamcap` exactly: default 99, fenced to 1 elsewhere.

  POPULATION    (`--population`) a different KIND of fence, and the one the
                four classes above structurally cannot see: not a parameter
                at all, but WHERE THE SHAPES COME FROM. It walks the driver's
                iterated calls to the generators that produce them and prints
                each one's docstring and literal ranges.

Why `--population` exists, and it is the second instance that earned it. The
four classes above are all PARAMETERS -- something a call could have passed
differently. Twice now, a dispatch spec has mis-described a population's
STRATUM, and neither time was a parameter involved:

  * `gforce.py` disclosed `Λ != ∅ not measured at all -- the sharpest blind
    axis`, and two strategy passes were written on it. False: the population
    is `sweep` -> `gridcol.pool_shapes` -> `grid.census_shapes`, whose length
    range is `(1, 2, 3, 4, 5)`, so `Λ != ∅` was 604 of its 907 shapes all
    along -- never unreached, only never REPORTED.
  * `aglu._pool8()` was called `a landed exhaustive n_hub = 8 pool` in two
    specs. It is the `Λ = ∅` stratum, because its other source is
    `cflank.excess_profiles`, which distributes length ABOVE 2.

Both are provenance, not configuration, so no keyword expresses them and the
lists above are silent. Recovering the first by hand cost ~12 calls.

It is a LISTER, not a judge. Nothing here knows which axis matters; it knows
which ones exist and puts the ones that stop a search at the top. A driver's
docstring is not evidence either way (top-level `CLAUDE.md`, *Docstrings are
not evidence*) -- read the value, then re-derive with the parameter opened.

Usage (from the repo root):

    python3 notes/scripts/blindaxes.py notes/scripts/w4/gridcol.py
    python3 notes/scripts/blindaxes.py w4/cflank.py --imports   # + siblings
    python3 notes/scripts/blindaxes.py w4/gforce.py --population
    python3 notes/scripts/blindaxes.py --selftest

`--imports` also scans same-package modules the driver imports (depth 1),
which is the "and its read-only imports" half of D6.4's spec.
"""

import argparse
import ast
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SCRIPTS = os.path.join(ROOT, "notes", "scripts")

# A default worth reporting. Strings are excluded by default -- a mode name or
# a path is configuration, not a fence -- but `--strings` puts them back.
def _literal(node, strings=False):
    try:
        v = ast.literal_eval(node)
    except Exception:
        return None
    if isinstance(v, bool) or v is None:
        return None
    if isinstance(v, str):
        return repr(v) if strings else None
    if isinstance(v, (int, float)):
        return repr(v)
    if isinstance(v, (tuple, list, set, frozenset, dict)) and len(str(v)) <= 120:
        return repr(v)
    return None


class Scan(ast.NodeVisitor):
    def __init__(self, src, strings=False):
        self.src = src.split("\n")
        self.strings = strings
        self.consts = []        # (line, name, value)
        self.params = []        # (line, func, param, value)
        self.uses = {}          # name -> [lines]  (comparisons)
        self.span = {}          # (func, lineno) -> end_lineno
        self.calls = []         # (line, func, kw, value)
        self.reads = {}         # name -> [lines]  (any load)
        self.depth = 0

    # module-level constants only: depth 0 assignments
    def visit_Assign(self, node):
        if self.depth == 0:
            for t in node.targets:
                if isinstance(t, ast.Name):
                    v = _literal(node.value, self.strings)
                    if v is not None:
                        self.consts.append((node.lineno, t.id, v))
        self.generic_visit(node)

    def _func(self, node):
        a = node.args
        pos = a.posonlyargs + a.args
        for arg, d in zip(pos[len(pos) - len(a.defaults):], a.defaults):
            v = _literal(d, self.strings)
            if v is not None:
                self.params.append((node.lineno, node.name, arg.arg, v))
        for arg, d in zip(a.kwonlyargs, a.kw_defaults):
            if d is None:
                continue
            v = _literal(d, self.strings)
            if v is not None:
                self.params.append((node.lineno, node.name, arg.arg, v))
        self.span[(node.name, node.lineno)] = getattr(
            node, "end_lineno", node.lineno)
        self.depth += 1
        self.generic_visit(node)
        self.depth -= 1

    visit_FunctionDef = _func
    visit_AsyncFunctionDef = _func

    def visit_Compare(self, node):
        for side in [node.left] + list(node.comparators):
            for n in ast.walk(side):
                if isinstance(n, ast.Name):
                    self.uses.setdefault(n.id, []).append(node.lineno)
        self.generic_visit(node)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load):
            self.reads.setdefault(node.id, []).append(node.lineno)
        self.generic_visit(node)

    def visit_Call(self, node):
        fn = getattr(node.func, "id", None) or getattr(node.func, "attr", None)
        for kw in node.keywords:
            if kw.arg is None:
                continue
            v = _literal(kw.value, self.strings)
            if v is not None:
                self.calls.append((node.lineno, fn, kw.arg, v))
        self.generic_visit(node)


def _guarded(fn, defline, name, scan):
    """Does this parameter gate an early exit? A comparison mentioning it --
    INSIDE ITS OWN FUNCTION -- within two lines of a `break`/`return`/
    `continue`, is the `want=1` shape: `if res['cert'] >= want:` immediately
    above a break.

    Scope is the declaring function's SPAN, and both halves were got wrong
    once. Matching the bare name module-wide put two false rows in this
    tool's highest-signal section: `nash_williams_ok(k=6)` matched a `k` in
    an unrelated comprehension 460 lines away, and `collapse_search(
    budget=90.0)` matched another function's `budget` 130 lines ABOVE its own
    definition. Matching the immediately-enclosing function instead then LOST
    the real one -- `collapse_search`'s guard on `want` lives in a closure
    `rec` nested inside it. A parameter is in scope for its whole body,
    nested defs included, so containment in `[def, end_lineno]` is the test.
    """
    lo, hi = defline, scan.span.get((fn, defline), defline)
    for ln in scan.uses.get(name, []):
        if not (lo <= ln <= hi):
            continue
        for j in range(ln - 1, min(ln + 3, len(scan.src))):
            if j < 0 or j >= len(scan.src):
                continue
            t = scan.src[j].strip()
            if t.startswith(("break", "return", "continue")) or " break" in t:
                return ln
    return None


def report(path, strings=False, quiet=False):
    rel = os.path.relpath(path, ROOT)
    src = open(path, encoding="utf-8").read()
    scan = Scan(src, strings)
    scan.visit(ast.parse(src))

    limiters, plain = [], []
    for ln, fn, arg, val in scan.params:
        g = _guarded(fn, ln, arg, scan)
        (limiters if g else plain).append((ln, fn, arg, val, g))

    # a call passing a literal to a keyword whose declared default differs
    decl = {(fn, arg): val for _l, fn, arg, val in scan.params}
    bykw = {}
    for _l, fn, arg, val in scan.params:
        bykw.setdefault(arg, set()).add(val)
    fenced = []
    for ln, fn, arg, val in scan.calls:
        want = decl.get((fn, arg))
        if want is not None and want != val:
            fenced.append((ln, fn, arg, val, want))
        elif want is None and arg in bykw and val not in bykw[arg]:
            fenced.append((ln, fn or "?", arg, val, "/".join(sorted(bykw[arg]))))

    n = len(limiters) + len(scan.consts) + len(plain) + len(fenced)
    if quiet and not n:
        return 0
    print(f"=== {rel} — {n} blind-axis candidate(s)")
    if limiters:
        print("  LIMITERS — a literal default that also gates an early exit "
              "(the `want=1` shape):")
        for ln, fn, arg, val, g in sorted(limiters, key=lambda r: r[0]):
            print(f"    L{ln:<6} {fn}({arg}={val})   guard at L{g}: "
                  f"{scan.src[g-1].strip()[:70]}")
    if scan.consts:
        print("  CONSTANTS — module-level literals (a constant nothing reads "
              "is not a fence, so read sites are shown):")
        for ln, name, val in sorted(scan.consts, key=lambda r: r[0]):
            rd = [l for l in scan.reads.get(name, []) if l != ln]
            where = (", ".join(f"L{l}" for l in sorted(set(rd))[:4]) or "UNREAD")
            print(f"    L{ln:<6} {name} = {val[:70]}")
            print(f"    {'':<7} read at {where}")
    if fenced:
        print("  FENCED CALLS — a literal passed where the default is wider "
              "(the `lamcap` shape):")
        for ln, fn, arg, val, want in sorted(fenced, key=lambda r: r[0]):
            print(f"    L{ln:<6} {fn}({arg}={val})   default is {want}")
    if plain:
        print("  DEFAULTS — every other keyword parameter with a literal "
              "default:")
        for ln, fn, arg, val, _g in sorted(plain, key=lambda r: r[0]):
            print(f"    L{ln:<6} {fn}({arg}={val})")
    print()
    return n


def sibling_imports(path):
    src = open(path, encoding="utf-8").read()
    here = os.path.dirname(path)
    out = []
    for node in ast.walk(ast.parse(src)):
        names = []
        if isinstance(node, ast.Import):
            names = [a.name.split(".")[-1] for a in node.names]
        elif isinstance(node, ast.ImportFrom):
            names = [a.name for a in node.names]
            if node.module:
                names.append(node.module.split(".")[-1])
        for nm in names:
            cand = os.path.join(here, nm + ".py")
            if os.path.isfile(cand) and os.path.abspath(cand) != os.path.abspath(path):
                out.append(cand)
    return sorted(set(out))


def resolve(name):
    for cand in (name, os.path.join(SCRIPTS, name), os.path.join(ROOT, name),
                 os.path.join(SCRIPTS, "w4", os.path.basename(name))):
        if os.path.isfile(cand):
            return cand
    raise SystemExit(f"no such driver: {name}")


def selftest():
    """The two landed findings, asserted. A lister that stopped surfacing
    these would be worse than none, because the loop would keep citing it."""
    bad = []
    cf = resolve("w4/cflank.py")
    s = Scan(open(cf).read()); s.visit(ast.parse(open(cf).read()))
    if not any(n == "LAM6_PLAN" for _l, n, _v in s.consts):
        bad.append("  cflank: LAM6_PLAN not listed as a module constant")
    if not any(a == "lamcap" for _l, _f, a, _v in s.params):
        bad.append("  cflank: lamcap not listed as a keyword default")
    gc = resolve("w4/gridcol.py")
    s2 = Scan(open(gc).read()); s2.visit(ast.parse(open(gc).read()))
    wants = [(l, f) for l, f, a, _v in s2.params if a == "want"]
    if not wants:
        bad.append("  gridcol: want not listed as a keyword default")
    elif not any(_guarded(f, l, "want", s2) for l, f in wants):
        bad.append("  gridcol: want listed but NOT flagged as a limiter")
    if bad:
        print("FAIL: blindaxes selftest", file=sys.stderr)
        print("\n".join(bad), file=sys.stderr)
        return 1
    print("OK: selftest — cflank LAM6_PLAN + lamcap listed, "
          "gridcol want listed AND flagged as a limiter.")
    return 0


POP_DEPTH = 5


def _defs(path):
    """{name: FunctionDef} for a module's top-level defs."""
    try:
        tree = ast.parse(open(path, encoding="utf-8").read())
    except Exception:
        return {}
    return {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}


def _callee(call):
    f = call.func
    if isinstance(f, ast.Name):
        return f.id
    if isinstance(f, ast.Attribute):
        return f.attr
    return None


# Pass-through iterables: `for i, x in enumerate(census_shapes())` must not
# stop the walk at `enumerate`. Generators of their own (product, combinations)
# are deliberately NOT here -- their literal ranges ARE the population.
_WRAPPERS = {"enumerate", "sorted", "list", "tuple", "set", "reversed",
             "iter", "zip", "chain", "filter", "map", "islice"}


def _unwrap(call):
    """Peel pass-through wrappers, yielding the calls that really produce."""
    if _callee(call) in _WRAPPERS:
        out = []
        for arg in call.args:
            if isinstance(arg, ast.Call):
                out.extend(_unwrap(arg))
        return out
    return [call]


def _iterated_calls(fn):
    """Calls in `fn` whose RESULT IS ITERATED -- directly as a `for` /
    comprehension iterable, or through a local the loop then walks. That is
    what a population IS, and it is why a plain call list would miss
    `aglu._pool8`'s: it assigns `ep = excess_profiles(12, 6)` first and
    iterates `ep`."""
    assigns = {}
    for node in ast.walk(fn):
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            for t in node.targets:
                if isinstance(t, ast.Name):
                    assigns.setdefault(t.id, node.value)
    out, seen = [], set()
    for node in ast.walk(fn):
        it = getattr(node, "iter", None)
        if it is None:
            continue
        call = None
        if isinstance(it, ast.Call):
            call = it
        elif isinstance(it, ast.Name) and it.id in assigns:
            call = assigns[it.id]
        if call is None:
            continue
        for inner in _unwrap(call):
            if id(inner) not in seen:
                seen.add(id(inner))
                out.append(inner)
    return out


def _fmt(call):
    parts = []
    for a in call.args:
        v = _literal(a, strings=True)
        parts.append(v if v is not None else "…")
    for kw in call.keywords:
        v = _literal(kw.value, strings=True)
        parts.append(kw.arg + "=" + (v if v is not None else "…"))
    return _callee(call) + "(" + ", ".join(parts) + ")"


def _table(path):
    """name -> (module, FunctionDef) over the driver and its imports to depth
    2. Depth 2 because the provenance that mattered ran three modules deep:
    `gforce.sweep` -> `gridcol.pool_shapes` -> `grid.census_shapes`."""
    tab = {}
    mods = [path]
    for sib in sibling_imports(path):
        if sib not in mods:
            mods.append(sib)
        for sib2 in sibling_imports(sib):
            if sib2 not in mods:
                mods.append(sib2)
    for p in reversed(mods):          # driver last, so same-file defs win
        for nm, node in _defs(p).items():
            tab[nm] = (p, node)
    return tab


def _body_literals(fn):
    """Literal ranges in a generator's body -- what it CAN produce.

    ONE per line, keeping the widest: a list literal contributes itself and
    every element, and the six sub-tuples of a `K4` edge list would otherwise
    crowd out the length range on the next line, which is the whole point."""
    byline = {}
    for node in ast.walk(fn):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            continue
        if not isinstance(node, (ast.Tuple, ast.List, ast.Constant)):
            continue
        v = _literal(node)
        # empty containers and all-None tuples are accumulators, not ranges
        if v is None or v in ("0", "1", "2", "[]", "()", "{}", "set()"):
            continue
        if set(v) <= set("(),None "):
            continue
        cur = byline.get(node.lineno)
        if cur is None or len(v) > len(cur):
            byline[node.lineno] = v
    return sorted(byline.items())[:8]


def _isgen(fn):
    return any(isinstance(x, (ast.Yield, ast.YieldFrom)) for x in ast.walk(fn))


def _sources(path, fn, tab, seen, depth=0):
    """EVERY population source out of `fn`, as a tree. Not the longest chain:
    `aglu._pool8` draws from `cubic_iso_classes` AND `excess_profiles`, and it
    is the second that fixes the stratum -- a longest-chain walk reports one
    of them and hides the fence."""
    if depth >= POP_DEPTH:
        return []
    out = []
    for call in _iterated_calls(fn):
        nm = _callee(call)
        if not nm or nm in seen or nm not in tab:
            continue
        p2, fn2 = tab[nm]
        out.append((_fmt(call), p2, fn2,
                    _sources(p2, fn2, tab, seen | {nm}, depth + 1)))
    return out


def _emit(nodes, pad, shown):
    for txt, p2, f2, kids in nodes:
        mod = os.path.basename(p2)[:-3]
        key = (p2, f2.name)
        mark = " [generator]" if _isgen(f2) else ""
        if key in shown:
            print(pad + "→ " + mod + "." + txt + mark + "   (shown above)")
            continue
        shown.add(key)
        print(pad + "→ " + mod + "." + txt + mark
              + ("" if kids else "   <- TERMINAL"))
        doc = ast.get_docstring(f2)
        if doc:
            print(pad + "     \"" + " ".join(doc.strip().split())[:150] + "\"")
        lits = _body_literals(f2)
        if lits:
            print(pad + "     ranges: "
                  + ", ".join(v + "@L" + str(ln) for ln, v in lits))
        _emit(kids, pad + "  ", shown)


def population(path, top=4):
    """Name WHERE a driver's shapes come from: every population source, with
    each one's own docstring and literal ranges."""
    tab = _table(path)
    rel = os.path.relpath(path, ROOT)
    roots = []
    for nm, fn in sorted(_defs(path).items()):
        kids = _sources(path, fn, tab, {nm})
        if kids:
            roots.append((nm, kids))
    if not roots:
        print("=== " + rel + " — POPULATION PROVENANCE: no iterated call "
              "resolves\n    to a def in this module or its imports.")
        return 0

    def _size(kv):
        n = [0]

        def rec(ns, d):
            for _t, _p, f, k in ns:
                n[0] += (10 if _isgen(f) else 1) + d
                rec(k, d + 1)
        rec(kv[1], 0)
        return -n[0]

    roots.sort(key=_size)
    print("=== " + rel + " — POPULATION PROVENANCE ("
          + str(len(roots)) + " entry point(s), showing "
          + str(min(top, len(roots))) + ")")
    print("  Where the shapes COME FROM. `blindaxes` proper lists PARAMETER")
    print("  fences; a population's provenance is the fence no keyword can")
    print("  express, and it is the one that cost two dispatch specs their")
    print("  stratum (Harness-structure D8).")
    shown = set()
    for nm, kids in roots[:top]:
        print("")
        print("  " + nm + "()")
        _emit(kids, "    ", shown)
    print("")
    print("  A LISTER, NOT A JUDGE, and a docstring is not evidence: it says")
    print("  which generators produce the population and what literals bound")
    print("  them. Read those ranges, then re-derive with them opened.")
    return 0


def _flatten(nodes, out):
    for txt, p2, f2, kids in nodes:
        out.append((txt, p2, f2))
        _flatten(kids, out)
    return out


def _pop_sources(driver, entry):
    """Flat list of (call text, module, def) reachable from one entry point."""
    path = resolve(driver)
    tab = _table(path)
    fn = _defs(path).get(entry)
    if fn is None:
        return []
    return _flatten(_sources(path, fn, tab, {entry}), [])


def population_selftest():
    """The TWO population findings, asserted — the mirror of `selftest()`'s
    two parameter findings. Both are landed and both were recovered by hand
    at real cost; a mode that stopped surfacing them would be worse than
    none, because the loop would keep citing it."""
    bad = []

    # (1) GFORCE's disclosed "sharpest blind axis" was `Λ ≠ ∅ not measured at
    # all". Its population reaches `grid.census_shapes`, whose length range
    # INCLUDES 1 -- so `Λ ≠ ∅` was in the population all along (604/907).
    src = _pop_sources("w4/gforce.py", "leg_kappa")
    cs = [(t, p, f) for t, p, f in src if f.name == "census_shapes"]
    if not cs:
        bad.append("  gforce: population does not reach grid.census_shapes")
    else:
        lits = [v for _ln, v in _body_literals(cs[0][2])]
        if not any(v.startswith("(1, 2, 3, 4, 5") for v in lits):
            bad.append("  gforce: census_shapes' length range (1,...,5) not "
                       "listed -- the `Λ != ∅` finding would be invisible")

    # (2) `aglu._pool8` is the `Λ = ∅` stratum, and the reason is its OTHER
    # source: `cflank.excess_profiles`, whose lengths are `2 + e`. Two dispatch
    # specs described `_pool8` as a general n_hub = 8 pool.
    src8 = _pop_sources("w4/aglu.py", "_pool8")
    names = {f.name for _t, _p, f in src8}
    if "excess_profiles" not in names:
        bad.append("  aglu: _pool8's population omits cflank.excess_profiles "
                   "-- the `Λ = ∅` fence would be invisible")
    if "cubic_iso_classes" not in names:
        bad.append("  aglu: _pool8's population omits cubic_iso_classes "
                   "-- a single-chain walk is reporting one source of two")

    if bad:
        print("FAIL: blindaxes --population selftest", file=sys.stderr)
        print("\n".join(bad), file=sys.stderr)
        return 1
    print("OK: population selftest — gforce reaches grid.census_shapes with "
          "its\n    (1,...,5) length range listed, and aglu._pool8 shows BOTH "
          "sources\n    including cflank.excess_profiles (the `Λ = ∅` fence).")
    return 0


def main(argv):
    p = argparse.ArgumentParser(prog="blindaxes.py",
                                description=__doc__.split("\n")[0])
    p.add_argument("driver", nargs="?", help="driver path, e.g. w4/cflank.py")
    p.add_argument("--imports", action="store_true",
                   help="also scan same-package modules it imports (depth 1)")
    p.add_argument("--strings", action="store_true",
                   help="include string-valued defaults and constants")
    p.add_argument("--population", action="store_true",
                   help="where the driver's shapes COME FROM: every "
                        "population source, with its ranges")
    p.add_argument("--selftest", action="store_true",
                   help="assert all four landed findings are still surfaced "
                        "(two parameter, two population)")
    a = p.parse_args(argv)
    if a.selftest:
        return selftest() | population_selftest()
    if not a.driver:
        p.error("a driver path is required (or --selftest)")
    path = resolve(a.driver)
    if a.population:
        return population(path)
    report(path, a.strings)
    if a.imports:
        for sib in sibling_imports(path):
            report(sib, a.strings, quiet=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
