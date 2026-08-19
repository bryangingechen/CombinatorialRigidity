"""(K-Lambda) item (vii): does a class shape's length-4 companion carry two or
more hubs on its interior?  Direction LTWO, sixth fan-out, 2026-08-19.

The answer is YES -- all four two-hub-interior patterns are REALIZED -- and
the reason the arc's sweeps found none is a THEOREM plus a CAP:

  (Lambda-4) the branch calculus.  For a feasible 2-edge-connected `G` with
      hub multigraph `G*` and branch lengths `l`, class membership is a
      statement about `G*` ALONE: tight <=> `sum l = 6 c(G*)`; `def = 0`
      <=> `sum_F l >= 6 c(F)` for every branch subset `F`; `hnoRigid` <=>
      that inequality is STRICT for every proper `F`.  Re-derives girth >= 7
      and (SD-6)'s `l <= 5` in one line each.
  (Lambda-5) the companion-cycle lemma.  The split branch plus a length-4
      companion is a proper `C_7` of `G` -- `j + 2` branches, `j + 2` hubs,
      cycle rank 1, total length 7.  Any further branch with BOTH ends on it
      would make cycle rank 2 at total length `7 + l <= 12`, violating
      `hnoRigid`.  So no branch outside the companion cycle joins two of its
      hubs -- the sole exception being `G* = Z + one branch`, which forces
      `j = 0` and `G = theta(3,4,5)`.
  (Lambda-6) the size floor.  Hence `n* >= j + 3` and `c* >= ceil((2j+7)/3)`,
      i.e. `|V| >= 5 c* + 1`: `j = 2` needs `|V| >= 21` and `|V*| >= 5`,
      `j = 3` needs `|V| >= 26` and `|V*| >= 6`.  At `t = 1` non-frame hub
      the hub graph is FORCED to be the wheel on the companion cycle.
  (Lambda-7) the witnesses.  `LT21a` (patterns (1,1,0) and (0,1,1)), `LT21b`
      ((1,0,1)) and `LT26` ((1,1,1)) attain those floors exactly.
  (Lambda-8) the consequence: item (vii) is REALIZED, not vacuous;
      `outer.py --patterns`' "(1,1,0)/(0,1,1)/(1,0,1) unrealized" is a CAP
      artifact inside the very hub multigraph it enumerated, while
      "(1,1,1) unrealized" is the genuine `|V*| <= 5` boundary (Lambda-6).

Naming: `LT21a` / `LT21b` / `LT26` are keyed to `|V|`, NOT to `|E|` -- the
arc's `NT<|E|>` convention would collide (these have `|E| = 24, 24, 30`,
already taken by `NT24` and `NT30`).

Exact integer / rational arithmetic throughout; no floating point.  Every
sampled placement carries the composite genericity guard `repin.star_generic`
through `outer.chart_point`; the single rng is seeded and its seed printed.
Nothing here modifies a tracked driver: `outer`, `kslidecomb`, `nogood_subdiv`
and `pitch` are imported READ-ONLY.

    python3 notes/scripts/w4/ltwo.py --witness
    python3 notes/scripts/w4/ltwo.py --floor
    python3 notes/scripts/w4/ltwo.py --census
    python3 notes/scripts/w4/ltwo.py --validate
"""
import importlib
import itertools
import random
import sys
import time

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import exact_deficiency, is_2ec, verts_of          # noqa: E402
from nogood_subdiv import hcard_ok, triangles                        # noqa: E402
from saferes import treepack_deficiency                              # noqa: E402
from kslidecomb import (candidate_graphs, canon, relabel,            # noqa: E402
                        shape_data, shape_ok)

OUT = importlib.import_module('outer')

SEED = 20260819

# ---------------- the three witnesses (Lambda-7) -----------------------------
#
# Hub labels: `b = 0`, `c = 1`; the companion interior hubs are 2, 3 (, 4);
# the single non-frame hub is the last index.  `specs[0]` is the length-3
# split branch, as `kslidecomb.shape_data` requires.

WITNESSES = [
    ('LT21a', [(0, 1, 3), (0, 2, 1), (2, 3, 1), (3, 1, 2),
               (4, 0, 5), (4, 2, 5), (4, 3, 5), (4, 1, 2)],
     'wheel W4 = K5 minus a perfect matching; companion b-x1-x2-c with '
     'branch lengths (1,1,2)'),
    ('LT21b', [(0, 1, 3), (0, 2, 1), (2, 3, 2), (3, 1, 1),
               (4, 0, 5), (4, 2, 5), (4, 3, 4), (4, 1, 3)],
     'wheel W4 again; companion branch lengths (1,2,1)'),
    ('LT26', [(0, 1, 3), (0, 2, 1), (2, 3, 1), (3, 4, 1), (4, 1, 1),
              (5, 0, 3), (5, 2, 5), (5, 3, 5), (5, 4, 5), (5, 1, 5)],
     'wheel W5; companion branch lengths (1,1,1,1)'),
]


# ---------------- (Lambda-4): the class predicate on the hub multigraph -----

def branch_subsets(n, E0):
    """Every CONNECTED branch subset `F` with cycle rank >= 1, other than the
    whole graph, as `(index tuple, 6 * c(F))`.

    (Lambda-4)(ii)/(iii) quantify over all branch subsets, but `f` is additive
    over components and `f(F) = -sum_F l < 0` whenever `c(F) = 0`, so the
    connected cyclic ones are the only binding constraints.  Ordered by size
    then by threshold, so the cheap short-cycle constraints are tested first.
    """
    m = len(E0)
    out = []
    for r in range(2, m + 1):
        for F in itertools.combinations(range(m), r):
            W = set()
            for i in F:
                W.add(E0[i][0])
                W.add(E0[i][1])
            par = {v: v for v in W}

            def find(x):
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x

            for i in F:
                ra, rb = find(E0[i][0]), find(E0[i][1])
                if ra != rb:
                    par[ra] = rb
            if len({find(v) for v in W}) != 1:
                continue
            c = len(F) - len(W) + 1
            if c < 1:
                continue
            if r == m and len(W) == n:
                continue                      # the whole graph: equality
            out.append((F, 6 * c))
    out.sort(key=lambda z: (len(z[0]), -z[1]))
    return out


def hub_class_ok(n, E0, lens, subs):
    """(Lambda-4) + `hcard`: is the subdivision of `(n, E0)` with branch
    lengths `lens` a class shape?  `subs` is `branch_subsets(n, E0)`.

    Callers must have pinned `sum(lens) == 6 * c(G*)` (tightness) and
    `1 <= l <= 5`; `bounded_comps` does both.  Triangle-freeness and
    simplicity are consequences, not extra tests: `F` a cycle forces
    `sum_F l >= 7`, i.e. girth >= 7.
    """
    d1 = [0] * n
    for (u, w), L in zip(E0, lens):
        if L == 1:
            d1[u] += 1
            d1[w] += 1
            if d1[u] > 2 or d1[w] > 2:
                return False                  # hcard
    for F, thr in subs:
        s = 0
        for i in F:
            s += lens[i]
        if s <= thr:
            return False
    return True


def hub_companions4(E0, lens, k):
    """Every length-4 `b`-`c` companion at the split branch `k = (b, c)`, as
    its hub pattern `(x1 hub, x2 hub, x3 hub)`.

    A companion is a simple `b`-`c` path of `H = G - v - a`; interior branch
    vertices have degree 2, so such a path traverses whole branches and is
    exactly a simple hub path of `G* - k` whose lengths sum to 4.  The
    interior hubs sit at the partial sums, which is the pattern.
    (`outer.companions4` is the same enumeration one level down, on the
    subdivided graph; `--validate` asserts the two agree.)
    """
    b, c = E0[k]
    inc = {}
    for i, (u, w) in enumerate(E0):
        if i == k:
            continue
        inc.setdefault(u, []).append((i, w))
        inc.setdefault(w, []).append((i, u))
    out = []

    def walk(cur, tot, seen, marks):
        if cur == c and tot == 4:
            out.append(tuple(marks))
            return
        for i, nxt in inc.get(cur, ()):
            if nxt in seen:
                continue
            t2 = tot + lens[i]
            if t2 > 4:
                continue
            walk(nxt, t2, seen | {nxt}, marks + ([t2] if nxt != c else []))

    walk(b, 0, {b}, [])
    return [tuple(1 if p in mk else 0 for p in (1, 2, 3)) for mk in out]


def companion_cycle(E0, lens, k):
    """The branch index set `Z` of the split branch plus a length-4 companion,
    for every companion at split `k`.  Yields `(Z, W0, pattern)`."""
    b, c = E0[k]
    inc = {}
    for i, (u, w) in enumerate(E0):
        if i == k:
            continue
        inc.setdefault(u, []).append((i, w))
        inc.setdefault(w, []).append((i, u))
    out = []

    def walk(cur, tot, seen, marks, used):
        if cur == c and tot == 4:
            pat = tuple(1 if p in marks else 0 for p in (1, 2, 3))
            out.append((frozenset(used) | {k}, frozenset(seen), pat))
            return
        for i, nxt in inc.get(cur, ()):
            if nxt in seen:
                continue
            t2 = tot + lens[i]
            if t2 > 4:
                continue
            walk(nxt, t2, seen | {nxt},
                 marks + ([t2] if nxt != c else []), used + [i])

    walk(b, 0, {b}, [], [])
    return out


def lam5_holds(n, E0, lens, Z, W0):
    """(Lambda-5) at one (shape, split, companion): no branch outside `Z` has
    BOTH ends on the companion cycle -- unless the whole graph is `Z` plus
    that one branch."""
    outside = [i for i in range(len(E0)) if i not in Z]
    for i in outside:
        u, w = E0[i]
        if u in W0 and w in W0:
            if len(outside) == 1 and len(W0) == n:
                continue                       # the theta(3,4,5) boundary
            return False
    return True


# ---------------- families ---------------------------------------------------

THETA3 = [(0, 1)] * 3
THETA4 = [(0, 1)] * 4
K4E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
K4PARE = K4E + [(0, 1)]


def families():
    """Exactly the `outer.py --patterns` family list: theta3, theta4, `K4`,
    `K4` plus a parallel branch, and the three simple hub graphs on 5 hubs.

    Every leg is run EXHAUSTIVELY at `lmax = 5`, which is exhaustive outright
    -- (SD-6)/(Lambda-4) cap every class branch length at 5 -- and with NO
    shape-count cap.  `--patterns` runs the same list at `lmax = 8` but caps
    each leg at 400 shapes; that cap is what this mode removes."""
    fam = [('theta3', 2, THETA3), ('theta4', 2, THETA4),
           ('K4', 4, K4E), ('K4+par', 4, K4PARE)]
    for n, E in candidate_graphs(5):
        if n == 5:
            fam.append((f'V5e{len(E)}', n, E))
    return fam


def harness_class_ok(n, E0, lens, k):
    """The tracked oracle: `kslidecomb.shape_ok` (tight + `def = 0` +
    `hnoRigid` at branch granularity) plus triangle-freeness and `hcard`,
    exactly as `outer.shapes_from` applies them."""
    specs = list(relabel(n, E0, list(lens), k))
    if shape_ok(specs) is None:
        return False
    E, _pm = shape_data(specs)
    return (not triangles(E)) and hcard_ok(E)


# ---------------- mode: the witnesses ----------------------------------------

def witness():
    print("== (Lambda-7): three class shapes whose length-4 companion carries "
          "two or more interior hubs ==")
    print(f"   rng: random.Random({SEED}), one per (witness, split); "
          f"chart points via outer.chart_point (repin.star_generic +")
    print("   verify_pencil_witness), up to 12 draws each.")
    print("   Every class claim is the TRACKED oracle's: kslidecomb.shape_ok "
          "+ nogood_subdiv.triangles/hcard_ok.\n")
    seen_pat = set()
    for name, specs, note in WITNESSES:
        nV = shape_ok(list(specs))
        assert nV is not None, f"{name}: not a class shape"
        E, _pm = shape_data(list(specs))
        assert not triangles(E), f"{name}: triangle"
        assert hcard_ok(E), f"{name}: hcard"
        nstar = len({h for s in specs for h in s[:2]})
        estar = len(specs)
        cstar = estar - nstar + 1
        assert sum(s[2] for s in specs) == 6 * cstar, "not tight"
        assert nV == 5 * cstar + 1 == len(verts_of(E))
        print(f"-- {name}: |V| = {nV}, |E| = {len(E)}, |V*| = {nstar}, "
              f"|E*| = {estar}, c* = {cstar}")
        print(f"   {note}")
        print(f"   specs {specs}")
        # Independent class certification: `shape_ok` above is the pebble-game
        # oracle plus `no_rigid_branch_union` (branch granularity).  Add the
        # tree-packing oracle always, and -- where `2^|V|` is affordable -- the
        # partition oracle, which certifies `hnoRigid` over EVERY proper vertex
        # subset rather than over branch unions.  (`notes/scripts/README.md`
        # section 1, "three independent oracles; they agree".)
        assert is_2ec(E), f"{name}: not 2-edge-connected"
        assert treepack_deficiency(E) == 0, f"{name}: treepack def != 0"
        if nV <= 21:
            d, info = exact_deficiency(E)
            assert d == 0 and info['f_full'] == 0
            assert info['n_positive_f_subsets'] == 0, "not 5/6-sparse"
            assert info['zero_f_proper_count'] == 0, "a proper rigid subset"
            assert info['maxf_proper_ge2'] < 0, "f = 0 on a proper subset"
            print(f"   oracles: pebble def = 0, treepack def = 0, "
                  f"partition def = 0 over all 2^{nV} subsets "
                  f"(max f over proper |W| >= 2 is "
                  f"{info['maxf_proper_ge2']}, zero-f proper subsets "
                  f"{info['zero_f_proper_count']}) -- hnoRigid certified "
                  f"beyond branch granularity")
        else:
            print(f"   oracles: pebble def = 0, treepack def = 0; the "
                  f"partition oracle is 2^{nV} and NOT run (budget), so "
                  f"hnoRigid here rests on branch granularity")
        for v in OUT.eligible_splits(E):
            a, b, c, Gp, Hed = OUT.split_data(E, v)
            Ps = OUT.companions4(Hed, b, c)
            if not Ps:
                continue
            rng = random.Random(SEED)
            cp, draws = None, 0
            for draws in range(1, 13):
                cp = OUT.chart_point(Gp, rng)
                if cp is not None:
                    break
            assert cp is not None, f"{name}: no guarded chart point in 12 draws"
            placed, pt, nrm = cp
            st = OUT.stratum_at(E, Gp, placed, a, b)
            assert st is not None, f"{name}: off target rank"
            rk, dimRa = st
            assert OUT.lam0d(placed, nrm, b, c), f"{name}: (Lambda-0d) fails"
            dirs = OUT.chart_dirs(Gp, placed, nrm, a, b, c)
            for P in Ps:
                pat = tuple(int(x) for x in OUT.hub_pattern(Gp, P))
                gc = OUT.geom_checks(placed, nrm, b, c, P)   # asserts (Lambda-0g)
                dg = [d for d in dirs if OUT.dg14(placed, P, d) != 0]
                fe = OUT.free_ends(Gp, P)
                assert gc['g14'] != 0, f"{name}: g14 == 0 at the chart point"
                assert dg, f"{name}: d g14 == 0 on the whole chart tangent space"
                seen_pat.add(pat)
                print(f"   split v={v} (b={b}, c={c}) companion {P}")
                print(f"      hub pattern {pat}  interior hubs {sum(pat)}  "
                      f"(Lambda-0i) free ends {tuple(int(x) for x in fe)}")
                print(f"      chart point at draw {draws}: rank {rk} "
                      f"(target), dim R_a = {dimRa}, (Lambda-0d) OK, "
                      f"(Lambda-0g) asserted both ways")
                print(f"      g14 != 0: True;  d g14 != 0 in "
                      f"{len(dg)}/{len(dirs)} chart tangent directions")
        print()
    want = {(1, 1, 0), (0, 1, 1), (1, 0, 1), (1, 1, 1)}
    assert want <= seen_pat, f"missing patterns {sorted(want - seen_pat)}"
    print("WITNESS OK: all four two-hub-interior patterns "
          "(1,1,0) (0,1,1) (1,0,1) (1,1,1) are REALIZED by class shapes,")
    print("  each at a hard-stratum target-rank guarded chart point with "
          "dim R_a = 1, (Lambda-0d) holding and g14 != 0.")
    print("  Item (vii) of the (K-Lambda) *What would change this* block is "
          "therefore a LIVE case, not a vacuity.")


# ---------------- mode: the (Lambda-6) floor ---------------------------------

def floor_bound(j):
    """(Lambda-6) by exhaustive integer search over the admissible
    `(t, m')`: `t >= 1`, `m' >= j + 2`, `2 m' >= (j + 2) + 3 t`;
    `c* = m' - t + 1`, `n* = j + 2 + t`.  Returns `(min c*, min n*)`."""
    best_c, best_n = None, None
    for t in range(1, 40):
        for mp in range(j + 2, 60):
            if 2 * mp < (j + 2) + 3 * t:
                continue
            c = mp - t + 1
            n = j + 2 + t
            if best_c is None or c < best_c:
                best_c = c
            if best_n is None or n < best_n:
                best_n = n
    return best_c, best_n


def floor():
    print("== (Lambda-6): the size floor for `j` interior hubs, and the "
          "forced `t = 1` structure ==")
    print("   `Z` = split branch + companion branches: `j + 2` branches on "
          "`j + 2` hubs, cycle rank 1, total length 7.")
    print("   By (Lambda-5) every hub of `Z` needs a branch to a hub OFF `Z`, "
          "so `t := n* - (j+2) >= 1`;")
    print("   `m' := e* - (j+2) >= j + 2` (one per `Z`-hub, at most one "
          "`Z`-end each) and `2 m' >= (j+2) + 3t`.\n")
    print("    j   n* >=   c* >=   |V| >=   |E| >=   closed form ceil((2j+7)/3)")
    for j in range(0, 4):
        c, n = floor_bound(j)
        cf = -((-(2 * j + 7)) // 3)
        assert c == cf, f"closed form mismatch at j={j}: {c} vs {cf}"
        print(f"    {j}     {n}       {c}      {5 * c + 1:3d}      "
              f"{6 * c:3d}      {cf}")
    print("   (`j = 0` additionally admits the (Lambda-5) boundary case "
          "`t = 0`, which IS theta(3,4,5): c* = 2, |V| = 11.)")

    print("\n-- the `t = 1` floor, enumerated exhaustively --")
    print("   At `t = 1` (Lambda-5) FORCES the structure: the `j+2` outside "
          "branches all join the unique")
    print("   non-frame hub to the `j+2` cycle hubs, one each -- so `G*` is "
          "the WHEEL on the companion cycle.")
    for j, cyc, spokes, tot_out in ((2, 4, 4, 17), (3, 5, 5, 23)):
        n = j + 3
        hub_cycle = [0, 2, 3, 1] if j == 2 else [0, 2, 3, 4, 1]
        E0 = [(hub_cycle[i], hub_cycle[(i + 1) % cyc]) for i in range(cyc)]
        E0 = [(0, 1)] + [e for e in E0 if set(e) != {0, 1}]
        E0 += [(n - 1, h) for h in hub_cycle]
        assert len(E0) == 2 * j + 4
        # `Z` = branch 0 (the split, length 3) + the cycle branches; the
        # companion lengths are a composition of 4 into `j + 1` parts.
        found = {}
        cand = 0
        subs = branch_subsets(n, E0)
        for comp in itertools.product(range(1, 5), repeat=cyc - 1):
            if sum(comp) != 4:
                continue
            for out_l in itertools.product(range(1, 6), repeat=spokes):
                if sum(out_l) != tot_out:
                    continue
                cand += 1
                lens = [3] + list(comp) + list(out_l)
                if not hub_class_ok(n, E0, lens, subs):
                    continue
                assert harness_class_ok(n, E0, lens, 0), "oracle disagreement"
                for _Z, _W0, pat in companion_cycle(E0, lens, 0):
                    if sum(pat) == j:
                        found[pat] = found.get(pat, 0) + 1
        cst = len(E0) - n + 1
        print(f"   j = {j}: wheel W{cyc} on {n} hubs, e* = {len(E0)}, "
              f"c* = {cst}, |V| = {5 * cst + 1}; {cand} length tuples")
        print(f"      class shapes carrying a j = {j} companion, by pattern: "
              f"{sorted(found.items())}")
        assert found, f"no j = {j} realization at the t = 1 floor"
    print("\nFLOOR OK: the (Lambda-6) floors are attained at `t = 1`, on the "
          "wheel; `j = 2` needs |V| >= 21 (W4 = K5 minus a")
    print("  perfect matching, |V*| = 5) and `j = 3` needs |V| >= 26 "
          "(W5, |V*| = 6) -- so no `j = 3` companion can occur")
    print("  in ANY `|V*| <= 5` family, which is exactly the recorded "
          "`(1,1,1)` boundary.")


# ---------------- mode: the exhaustive census --------------------------------

def census():
    print("== the exhaustive hub-pattern census, uncapped, at lmax = 5 ==")
    print("   Families: exactly the `outer.py --patterns` list.  Lengths run "
          "over [1, 5], which is EXHAUSTIVE")
    print("   outright -- (SD-6)/(Lambda-4) cap every class branch at 5 -- "
          "and NOTHING is capped by a shape count.")
    print("   Convention: one row per (hub multigraph, length assignment, "
          "split BRANCH, companion).  Each length-3 branch")
    print("   carries two eligible splits (the two orientations); this "
          "census counts the branch once, so the mirror patterns")
    print("   (1,1,0)/(0,1,1) are separated by the length assignment, not "
          "by the orientation.\n")
    grand, lam5 = {}, 0
    t0 = time.time()
    for tag, n, E0 in families():
        m = len(E0)
        tot = 6 * (m - n + 1)
        subs = branch_subsets(n, E0)
        nsh, cen = 0, {}
        for k in range(m):
            for lens in OUT.bounded_comps(m, tot, 1, 5, {k: 3}):
                if not hub_class_ok(n, E0, lens, subs):
                    continue
                cc = companion_cycle(E0, lens, k)
                if not cc:
                    continue
                nsh += 1
                for Z, W0, pat in cc:
                    # (Lambda-5)'s premise, per triple: `Z` is a cycle of the
                    # hub multigraph on `j + 2` branches and `j + 2` hubs,
                    # cycle rank 1, total length 7 (the proper `C_7` of (D3)).
                    j = sum(pat)
                    assert len(Z) == j + 2 and len(W0) == j + 2, "Z shape"
                    assert sum(lens[i] for i in Z) == 7, "Z length != 7"
                    assert lam5_holds(n, E0, lens, Z, W0), \
                        f"(Lambda-5) FAILS at {tag} {lens} split {k}"
                    lam5 += 1
                    cen[pat] = cen.get(pat, 0) + 1
                    grand[pat] = grand.get(pat, 0) + 1
        print(f"   {tag:8s} |E*| = {m:2d}: {nsh:6d} (shape, split) pairs "
              f"with a length-4 companion; patterns "
              f"{sorted(cen.items())}")
    print(f"\n   grand total, by pattern: {sorted(grand.items())}")
    print(f"   (Lambda-5) asserted at all {lam5} (shape, split, companion) "
          f"triples: 0 failures")
    real = {p for p in grand}
    allp = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
    print(f"   patterns realized: {len(real)} of 8; "
          f"unrealized here: {sorted(p for p in allp if p not in real)}")
    print(f"   census wall time {time.time() - t0:.1f} s")

    print("\n-- disclosure 1: what this census does NOT cover (a SCOPE "
          "BOUNDARY, disclosed as such) --")
    print("   * hub MULTIgraphs on 3-5 hubs other than theta3 / theta4 / "
          "K4+par are not enumerated.")
    print("   * nothing with |V*| >= 6 is enumerated -- which is exactly "
          "where (Lambda-6) puts the (1,1,1) pattern,")
    print("     and where `LT26` lives.")

    print("\n-- disclosure 2: the `--patterns` cap, made reproducible --")
    E8 = [E for (n, E) in candidate_graphs(5) if n == 5 and len(E) == 8][0]
    t1 = time.time()
    sh, tried, capped = OUT.shapes_from('V5e8', 5, E8, 8, cap=400)
    ksplit = sorted({lab.rsplit(' ', 1)[1] for lab, _E in sh})
    print(f"   outer.shapes_from('V5e8', 5, E0, lmax=8, cap=400) -- the exact "
          f"call `--patterns` makes --")
    print(f"   returns {len(sh)} shapes after {tried} length tuples, "
          f"capped = {capped}, in {time.time() - t1:.1f} s;")
    print(f"   every one of them sits at split index {ksplit} of "
          f"{len(E8)} -- split indices 1..{len(E8) - 1} are never reached.")
    print(f"   The same hub multigraph is the one the `LT21a` / `LT21b` "
          f"witnesses live on (canon match: "
          f"{canon(5, E8) == canon(5, [(0, 1), (0, 2), (2, 3), (3, 1), (4, 0), (4, 2), (4, 3), (4, 1)])}).")
    print("   So the recorded `(1,1,0)/(0,1,1)/(1,0,1) unrealized in scope` "
          "is a CAP artifact, not a |V*| <= 5 boundary.")
    assert capped, "the --patterns cap did not fire; the disclosure is stale"

    print("\nCENSUS OK: 7 of 8 hub patterns are realized inside the swept "
          "family list; only (1,1,1) is absent, and")
    print("  (Lambda-6) proves it CANNOT occur at |V*| <= 5.")


# ---------------- mode: validate ---------------------------------------------

def validate():
    print("== --validate: the (Lambda-4) hub-graph predicate against the "
          "tracked oracle ==")
    print("   oracle = kslidecomb.shape_ok (tight + def = 0 + hnoRigid over "
          "branch unions) AND nogood_subdiv.triangles")
    print("   empty AND nogood_subdiv.hcard_ok -- i.e. exactly "
          "`outer.shapes_from`' class test.\n")
    tot_t, tot_ok = 0, 0
    for tag, n, E0 in [('theta3', 2, THETA3), ('theta4', 2, THETA4),
                       ('K4', 4, K4E), ('K4+par', 4, K4PARE)]:
        m = len(E0)
        S = 6 * (m - n + 1)
        subs = branch_subsets(n, E0)
        cnt, agree, fastok = 0, 0, 0
        for k in range(m):
            for lens in OUT.bounded_comps(m, S, 1, 5, {k: 3}):
                cnt += 1
                f = hub_class_ok(n, E0, lens, subs)
                h = harness_class_ok(n, E0, lens, k)
                assert f == h, f"DISAGREE {tag} {lens} split {k}: {f} vs {h}"
                agree += 1
                fastok += 1 if f else 0
        print(f"   {tag:8s}: {cnt:5d} length tuples, {fastok:5d} class "
              f"shapes, {agree:5d} agreements, 0 disagreements")
        tot_t += cnt
        tot_ok += agree

    # The four families above all have `n* <= 4`.  One STRIDED leg at
    # `n* = 5` -- the size the census' heavy legs run at, and the size the
    # witnesses live at.  Stride 8, split branch 0: deterministic, ~1/8 of
    # the 8135-tuple exhaustive leg (which agrees in full, but at ~28 s).
    STRIDE = 8
    E8 = [E for (n, E) in candidate_graphs(5) if n == 5 and len(E) == 8][0]
    subs = branch_subsets(5, E8)
    cnt, agree, fastok = 0, 0, 0
    for idx, lens in enumerate(OUT.bounded_comps(8, 24, 1, 5, {0: 3})):
        if idx % STRIDE:
            continue
        cnt += 1
        f = hub_class_ok(5, E8, lens, subs)
        h = harness_class_ok(5, E8, lens, 0)
        assert f == h, f"DISAGREE V5e8 {lens} split 0: {f} vs {h}"
        agree += 1
        fastok += 1 if f else 0
    print(f"   {'V5e8':8s}: {cnt:5d} length tuples, {fastok:5d} class "
          f"shapes, {agree:5d} agreements, 0 disagreements "
          f"(STRIDED: every {STRIDE}th tuple of split branch 0)")
    tot_t += cnt
    tot_ok += agree

    print("\n-- the companion enumerator, against outer.companions4 --")
    print("   Every eligible split of every witness -- i.e. every length-3 "
          "branch, in both orientations -- is checked,")
    print("   not just the named one.")
    ncomp = 0
    for name, specs, _note in WITNESSES:
        E0 = [(s[0], s[1]) for s in specs]
        lens = [s[2] for s in specs]
        E, pm = shape_data(list(specs))
        nsp = 0
        for v in OUT.eligible_splits(E):
            a, b, c, Gp, Hed = OUT.split_data(E, v)
            k = next(i for i in pm if v in pm[i][1:-1])
            assert lens[k] == 3 and {b, c} == set(E0[k]), "split/branch map"
            mine = hub_companions4(E0, lens, k)
            if (b, c) != E0[k]:
                mine = [tuple(reversed(p)) for p in mine]
            theirs = [tuple(int(x) for x in OUT.hub_pattern(Gp, P))
                      for P in OUT.companions4(Hed, b, c)]
            assert sorted(mine) == sorted(theirs), \
                f"{name} split {v} (branch {k}): {sorted(mine)} vs " \
                f"{sorted(theirs)}"
            ncomp += len(theirs)
            nsp += 1
        print(f"   {name}: {nsp} eligible splits, hub-graph enumerator "
              f"agrees with outer.companions4 + outer.hub_pattern")

    print("\n-- the named length-4-companion habitats, through the same "
          "predicate --")
    LAM = importlib.import_module('lambda')
    for hname, E, v, comp in LAM.HABITATS4:
        assert OUT.split_data(E, v) is not None, f"{hname}: split unusable"
        print(f"   {hname}: eligible split at v = {v}, "
              f"{len(OUT.companions4(OUT.split_data(E, v)[4], OUT.split_data(E, v)[1], OUT.split_data(E, v)[2]))} "
              f"length-4 companion(s)")

    print(f"\nVALIDATE OK: {tot_ok}/{tot_t} tuples agree with the tracked "
          f"oracle, 0 disagreements; {ncomp} companions cross-checked.")


# ---------------- main -------------------------------------------------------

def main():
    args = sys.argv[1:]
    modes = {'--witness': witness, '--floor': floor,
             '--census': census, '--validate': validate}
    if not args or args[0] not in modes:
        print(__doc__)
        return
    modes[args[0]]()


if __name__ == '__main__':
    main()
