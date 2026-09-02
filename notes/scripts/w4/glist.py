"""
Phase 39 (K-grid) -- direction GLIST: (GR-132)'s hub list-colouring at the
`ell = 2`-rich shapes.

GPACK closed the packing-and-split half of (GR-18)(iii) ((GR-130), a theorem
off `def(G) = 0` alone) and left EXACTLY the class-consistency clause, stated
at `Lambda = 0` as a hub list-colouring ((GR-132)) whose lists `J \\ C_beta`
have size `A(beta)` -- FORCED, size 1 on each side, at every length-2 branch.
This direction attacks that residual where (GR-132)'s own hand-off sends a
successor.

RESULT (2026-09-02), and the deliverable is an ARGUMENT with the search
demoted to an adversarial control:

  * (GR-134) the ORIENTATION NORMAL FORM.  The end pattern can be eliminated:
    (GR-132)'s clauses (a)/(b)/(c) are equivalent to a CSP in two hub
    functions `alpha : hubs -> J`, `gamma : hubs -> J^c` alone, whose whole
    content is "every branch at `u` inside `T_{alpha(u)}` has its `u`-end B,
    and every branch inside `T_{gamma(u)}` has its `u`-end A".  Clause (a),
    the no-monochromatic-hub clause, is then FREE -- implied by (b), because
    each of the six trees is SPANNING, so `deg_{T_{alpha(u)}}(u) >= 1`
    supplies the B-end and `deg_{T_{gamma(u)}}(u) >= 1` the A-end.
  * (GR-135) the LOCAL CRITERION, and the conflict in closed form.  At a hub
    all of whose branches have length 2 (a PURE hub) the local system is
    feasible iff some two of the incident absence-pairs `D_beta` share an
    element; at hub degree 3 that is `J`-FREE and reads *`u` is a leaf of at
    least one of the six trees*, equivalently NOT `deg_{T_j}(u) = 2` for all
    six `j`, equivalently the three `D_beta` do NOT form a PERFECT MATCHING
    of `{1..6}`.
  * (GR-136) the REDUCTION -- and the limit of the local reading.  At `D = 0`
    the pure-hub half of the residual is a LEAF-COVERING condition on the
    6-tree partition; by the excess law (GR-21) there is no all-length-2
    shape at all, so the pure case is LOCAL, never global.  But the local
    conditions are NOT the whole residual: of the infeasible pairs measured
    below, 82% are locally feasible at EVERY hub.
  * (GR-137) the SUPPORT AUDIT of (GR-132)'s own evidence, and it is the
    forced job.  The population DOES present the conflict (6 of the 12
    shapes carry a pure hub) -- but the `229 320/229 320` figure is a rate
    over the ACCEPTED pairs only, and the missing denominator is measured
    here: 229 320 of 472 680 legal pairs, so 243 360 are REJECTED.

Modes.

--support  (GR-137).  The `RESEARCH-ARC.md` section-4 audit of (GR-132)'s
           evidence: rebuild `gpack.py --resid`'s exact population and ask
           which of (GR-132)'s own variables it varies.  Per shape: the
           length-2 subgraph `H`, `t(u) = deg_H(u)`, the pure hubs, and the
           two-length-2-branches-at-a-common-hub configuration the residual's
           difficulty needs.  Then the same measurement on the whole census
           `Lambda = 0` pool and on the `D = 0` stratum at `n_hub in {4, 6}`.
--local    (GR-135).  The local criterion, verified EXHAUSTIVELY over the
           abstract configuration space (every triple / quadruple of
           `J`-split pairs, not merely the realized ones) against a brute
           force, plus the constructed must-REJECT witness and its negative
           control (README section 4 convention 6 / dispatch-log F13).
--csp      (GR-134).  The orientation normal form cross-oracled against
           `gpack.csp_witness` at every (shape, packing, split) of the
           `--resid` population -- the "(a) is free" theorem asserted there,
           the missing denominator supplied, and the local/global split of
           the obstruction measured.
--rich     (GR-136).  The leaf-covering residual decided EXHAUSTIVELY on the
           `n_hub = 4` half of the `D = 0` stratum -- every class shape,
           every 6-tree partition, every split -- then a constructed
           `n_hub = 6` pure-hub control at which a capped search finds NO
           feasible pair and the certificate side exhibits 60.
--validate all four.

Caps, with denominators (README section 4 convention 8; `RESEARCH-ARC.md`
section 5).  `--support`'s census leg is exhaustive over the 907-shape census
pool; its `D = 0` leg is exhaustive over `n_hub in {4, 6}` (every cubic hub
multigraph up to isomorphism x every excess profile), and says NOTHING about
`n_hub >= 8`.  `--local` is exhaustive over the abstract local configuration
space at hub degree 3 and 4.  `--csp` is exhaustive over all 6-tree
partitions and all 20 splits at the 12 `--resid` shapes.  `--rich` legs (i)
and (ii) are exhaustive over the `n_hub = 4` `D = 0` stratum; its leg (iii)
is a SEEDED capped search whose `0 feasible pairs` is reported as NOT FOUND
UNDER CAP and is then shown blind by the certificate side, which is the
convention-8 hazard firing inside this very driver.

Exact throughout: every object here is a finite combinatorial datum (integers
and sets), so no rank, no field, no placement and no `Fraction` arises; the
one rng is seeded from a literal and its seed is printed.

Run (from the repo root):
    python3 notes/scripts/w4/glist.py --support
    python3 notes/scripts/w4/glist.py --local
    python3 notes/scripts/w4/glist.py --csp
    python3 notes/scripts/w4/glist.py --rich
    python3 notes/scripts/w4/glist.py --validate
"""
import random
import sys
from itertools import combinations, product

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                     # noqa: E402
from closure import colourings, cycle_rank                            # noqa: E402
from grid import block_data                                           # noqa: E402
from packmm import fast_triple                                        # noqa: E402
from gridcol import (branch_classes, branch_decomp, class_shape,      # noqa: E402
                     filter_pass, multigraphs)
from cflank import cubic_habitat, excess_profiles                     # noqa: E402
from gpack import (all_packings, csets, csp_witness, legal_splits,    # noqa: E402
                   shape_rows)

L_SEED = 20260902
CUBIC_N = (4, 6)
RICH_NODES = 400000       # node budget for the randomized packing search
RICH_WANT = 4000          # how many legal (packing, split) pairs to collect


# ------------------------------------------------------ local devices -------

def incidence(hubs, ends):
    """Per hub, the branch indices incident to it."""
    inc = {u: [] for u in hubs}
    for i, (u, w) in enumerate(ends):
        inc[u].append(i)
        inc[w].append(i)
    return inc


def tree_deg(inc, C, u):
    """`(deg_{T_j}(u))_{j=0..5}` -- how many branches at `u` lie in tree `j`.

    Local device: this is a HUB-LOCAL degree in one part of the 6-tree
    partition of `Ghat`, deliberately NOT `gridcol.degmap` (which is the
    degree in the hub multigraph itself) and not `packmm`'s class degrees."""
    return [sum(1 for i in inc[u] if j in C[i]) for j in range(6)]


def pure_hubs(hubs, ends, lens):
    """The hubs all of whose branches have length 2 -- where (GR-132)'s lists
    are forced on BOTH sides at BOTH ends and the conflict can live."""
    inc = incidence(hubs, ends)
    return [u for u in hubs if inc[u] and all(lens[i] == 2 for i in inc[u])]


def h_degrees(hubs, ends, lens):
    """`t(u) = deg_H(u)`, the number of length-2 branches at `u`."""
    inc = incidence(hubs, ends)
    return {u: sum(1 for i in inc[u] if lens[i] == 2) for u in hubs}


def split_data(lens, C, J):
    """`(A, P, Q, kind)` for a (packing, split) pair, or None if the split is
    not length-legal.  `P_beta = J & D_beta`, `Q_beta = J^c & D_beta` are the
    two lists of (GR-132)(b); `kind` is 'even', 'AA' or 'BB'."""
    Js, Jc = set(J), set(range(6)) - set(J)
    A, P, Q, kind = [], [], [], []
    for i, L in enumerate(lens):
        a = 3 - len(C[i] & Js)
        D = set(range(6)) - C[i]
        if L % 2 == 0:
            if a != L // 2:
                return None
            kind.append('even')
        elif a == (L + 1) // 2:
            kind.append('AA')
        elif a == (L - 1) // 2:
            kind.append('BB')
        else:
            return None
        A.append(a)
        P.append(D & Js)
        Q.append(D & Jc)
    return A, P, Q, kind


def local_ok_brute(inc, lens, P, Q, J, u):
    """Brute force: is the LOCAL system at hub `u` -- (GR-132)(b) plus (a),
    with the other end of every branch left free -- satisfiable?"""
    Jc = sorted(set(range(6)) - set(J))
    for a in sorted(J):
        for g in Jc:
            eps = []
            ok = True
            for i in inc[u]:
                cand = []
                if a in P[i]:
                    cand.append('A')
                if g in Q[i]:
                    cand.append('B')
                if lens[i] % 2:
                    # an odd branch's end colour is forced by the split
                    forced = 'A' if len(P[i]) == (lens[i] + 1) // 2 else 'B'
                    cand = [c for c in cand if c == forced]
                if not cand:
                    ok = False
                    break
                eps.append(cand)
            if not ok:
                continue
            # (a): some assignment gives `u` both colours
            if any('A' in c for c in eps) and any('B' in c for c in eps):
                return True
    return False


def local_ok_criterion(inc, lens, C, P, J, u):
    """(GR-135): the local criterion.  Exists `(j, k)` in `J x J^c` with no
    forced-A branch at `u` in `T_j`, no forced-B branch in `T_k`, and no even
    branch in BOTH `T_j` and `T_k`."""
    Jc = sorted(set(range(6)) - set(J))
    fA = [i for i in inc[u] if lens[i] % 2 and len(P[i]) == (lens[i] + 1) // 2]
    fB = [i for i in inc[u] if lens[i] % 2 and len(P[i]) != (lens[i] + 1) // 2]
    ev = [i for i in inc[u] if lens[i] % 2 == 0]
    for j in sorted(J):
        if any(j in C[i] for i in fA):
            continue
        for k in Jc:
            if any(k in C[i] for i in fB):
                continue
            if all(not (j in C[i] and k in C[i]) for i in ev):
                return True
    return False


def csp_orient(hubs, ends, lens, C, J):
    """(GR-134): the orientation normal form.  Backtracking search for
    `alpha : hubs -> J`, `gamma : hubs -> J^c` with, per branch `beta = uw`:

      even    (alpha(u) in P & gamma(w) in Q) or (alpha(w) in P & gamma(u) in Q)
      'AA'    alpha(u), alpha(w) in P and alpha(u) != alpha(w)
      'BB'    gamma(u), gamma(w) in Q and gamma(u) != gamma(w)

    Returns `(alpha, gamma)` as dicts, or None.  Clause (a) is NOT imposed --
    (GR-134)(i) says it is implied, and `--csp` asserts exactly that."""
    sd = split_data(lens, C, J)
    if sd is None:
        return None
    _A, P, Q, kind = sd
    Js, Jc = sorted(J), sorted(set(range(6)) - set(J))
    cells = [(a, g) for a in Js for g in Jc]
    hs = list(hubs)
    pos = {u: t for t, u in enumerate(hs)}
    at = {u: [] for u in hs}
    for i, (u, w) in enumerate(ends):
        at[u].append((i, w))
        at[w].append((i, u))
    asg = {}

    def rel(i, cu, cw):
        au, gu = cu
        aw, gw = cw
        if kind[i] == 'even':
            return ((au in P[i] and gw in Q[i]) or
                    (aw in P[i] and gu in Q[i]))
        if kind[i] == 'AA':
            return au in P[i] and aw in P[i] and au != aw
        return gu in Q[i] and gw in Q[i] and gu != gw

    def rec(t):
        if t == len(hs):
            return True
        u = hs[t]
        for cu in cells:
            asg[u] = cu
            if all(rel(i, cu, asg[w]) for (i, w) in at[u]
                   if w in asg and pos[w] < t):
                if rec(t + 1):
                    return True
            del asg[u]
        return False

    if not rec(0):
        return None
    return ({u: asg[u][0] for u in hs}, {u: asg[u][1] for u in hs})


def some_packings(hubs, ends, lens, rng, want, nodes):
    """Up to `want` partitions of `Ghat` into 6 spanning trees of `G^o`,
    found by a SEEDED randomized depth-first search under a node budget.

    Local device, and deliberately not `gpack.all_packings`: that one is
    exhaustive and is the right tool at `m <= 6`, but the shapes that carry a
    PURE hub start at `n_hub = 6`, `m = 9`, where the exhaustive tree is out
    of reach.  This decides EXISTENCE only; the budget is printed."""
    m, n = len(ends), len(hubs)
    idx = {v: i for i, v in enumerate(hubs)}
    ed = [(idx[u], idx[w]) for u, w in ends]
    out = []
    budget = [nodes]

    def acyclic(sel):
        return cycle_rank(list(range(n)), [ed[i] for i in sel]) == 0

    def rec(i, trees):
        if len(out) >= want or budget[0] <= 0:
            return
        budget[0] -= 1
        if i == m:
            if all(len(t) == n - 1 for t in trees):
                out.append([tuple(sorted(t)) for t in trees])
            return
        opts = list(combinations(range(6), 6 - lens[i]))
        rng.shuffle(opts)
        rem = sum(6 - lens[k] for k in range(i + 1, m))
        for Cb in opts:
            nt = [list(t) for t in trees]
            ok = True
            for j in Cb:
                if len(nt[j]) >= n - 1:
                    ok = False
                    break
                nt[j].append(i)
                if not acyclic(nt[j]):
                    ok = False
                    break
            if not ok:
                continue
            if sum((n - 1) - len(nt[j]) for j in range(6)) > rem:
                continue
            rec(i + 1, nt)
            if len(out) >= want or budget[0] <= 0:
                return

    rec(0, [[] for _ in range(6)])
    return out, nodes - budget[0]


# ------------------------------------------- [GL-1] --support: (GR-137) -----

def leg_support():
    """[GL-1] (GR-137): the sampler-support audit of (GR-132)'s evidence."""
    print("[GL-1] (GR-137): the support audit of (GR-132)'s own population "
          "(RESEARCH-ARC section 4)")
    print("  (i) gpack.py --resid's population, rebuilt exactly: the first 12 "
          "census shapes with m <= 6 and Lambda = 0")
    print("      shape                          n   m  lengths                "
          "  n_2  max t(u)  pure hubs")
    tot2 = 0
    worst_t = 0
    npure = 0
    nshape = 0
    for label, edges, hubs, br, ends, lens in shape_rows(
            12, mmax=6, lambda_free=True):
        nshape += 1
        t = h_degrees(hubs, ends, lens)
        ph = pure_hubs(hubs, ends, lens)
        n2 = sum(1 for L in lens if L == 2)
        tot2 += n2
        worst_t = max(worst_t, max(t.values()))
        npure += len(ph)
        print(f"      {label[:29]:29s} {len(hubs):2d} {len(ends):3d}  "
              f"{str(sorted(lens)):22s}  {n2:3d}  {max(t.values()):5d}     "
              f"{len(ph):5d}")
    assert nshape == 12, "the --resid population is not 12 shapes"
    print(f"    totals: {tot2} length-2 branches over {nshape} shapes "
          f"(gpack --resid prints exactly this figure), max_u t(u) = "
          f"{worst_t}, pure hubs = {npure}")
    assert worst_t == 3 and npure == 6, "the --resid population moved"
    print("    VERDICT (and it REFUTES the coordinator's own audit "
          "expectation): the population DOES present the conflict -- 6 of the "
          "12 shapes carry a PURE hub (a K4 length-2 STAR, the opposite "
          "triangle absorbing the whole excess), so quantifier (i) of the "
          "audit is answered POSITIVELY and the conflict is testable "
          "EXHAUSTIVELY right there (--rich)")

    print("  (ii) the same measurement over the WHOLE census Lambda = 0 pool "
          "(exhaustive, no m cap)")
    ncen = ncen2 = ncenpure = 0
    hist = {}
    for label, edges, hubs, br, ends, lens in shape_rows(
            None, mmax=None, lambda_free=True):
        ncen += 1
        t = h_degrees(hubs, ends, lens)
        mt = max(t.values())
        hist[mt] = hist.get(mt, 0) + 1
        if mt >= 2:
            ncen2 += 1
        if pure_hubs(hubs, ends, lens):
            ncenpure += 1
    print(f"    {ncen} census shapes with Lambda = 0; max_u t(u) histogram "
          + ", ".join(f"{k}:{hist[k]}" for k in sorted(hist)))
    print(f"    with some hub carrying t(u) >= 2: {ncen2}/{ncen}; "
          f"with a PURE hub: {ncenpure}/{ncen}")
    assert ncenpure > 0, "the census carries NO pure hub"

    print("  (iii) the D = 0 stratum, exhaustive at n_hub in {4, 6} "
          "(cflank.cubic_habitat, the (GR-25) cut criterion)")
    for n in CUBIC_N:
        M = 3 * n // 2
        gs = multigraphs(n, M)
        profs = excess_profiles(M, 6)
        nsh = npu = nt2 = 0
        for hedges in gs:
            for exc in profs:
                lens = [2 + e for e in exc]
                if not cubic_habitat(n, hedges, lens):
                    continue
                nsh += 1
                hubs = list(range(n))
                t = h_degrees(hubs, hedges, lens)
                if max(t.values()) >= 2:
                    nt2 += 1
                if pure_hubs(hubs, hedges, lens):
                    npu += 1
        print(f"    n_hub={n}, m={M}: {len(gs)} hub multigraphs up to iso x "
              f"{len(profs)} excess profiles -> {nsh} class shapes; "
              f"{nt2} with some t(u) >= 2, {npu} with a PURE hub")
        assert npu > 0, f"n_hub = {n} carries NO pure hub"
    print("    VERDICT: pure hubs are ABUNDANT on the D = 0 stratum, and the "
          "n_hub = 4 half of it is inside the exhaustive-packing reach "
          "(m = 6), so the universal question -- is there a shape whose EVERY "
          "legal pair has a bad pure hub? -- is decidable there and is "
          "decided in --rich")

    print("  (iv) which quantifiers --resid's two legs actually range over "
          "(a reading of the shipped gpack.py, stated so it is checkable):")
    print("    SOUNDNESS ranges over the FULL exchange freedom -- "
          "`for trees in all_packings(...)` then `for J in legal_splits(...)`, "
          "both exhaustive")
    print("    COMPLETENESS does NOT -- it consumes only the "
          "CERTIFICATE-INDUCED packing of each filter-passing colouring, with "
          "`J = (0, 1, 2)` PINNED, and (GR-131) has since shown the "
          "certificate-induced packing is not canonical")
    print()


# --------------------------------------------- [GL-2] --local: (GR-135) -----

def _abstract_local(cells, J):
    """Brute-force local feasibility for an ABSTRACT pure hub: `cells` are the
    `(a, b)` pairs of its length-2 branches, `a in J`, `b in J^c`."""
    Jc = sorted(set(range(6)) - set(J))
    for a in sorted(J):
        for g in Jc:
            eps = []
            for (ab, bb) in cells:
                cand = []
                if a == ab:
                    cand.append('A')
                if g == bb:
                    cand.append('B')
                if not cand:
                    eps = None
                    break
                eps.append(cand)
            if eps is None:
                continue
            if any('A' in c for c in eps) and any('B' in c for c in eps):
                return True
    return False


def _cross_coverable(cells, J):
    """Exists `(a, b)` with every cell in row `a` or column `b`."""
    Jc = sorted(set(range(6)) - set(J))
    return any(all(ab == a or bb == b for (ab, bb) in cells)
               for a in sorted(J) for b in Jc)


def leg_local():
    """[GL-2] (GR-135): the local criterion, exhaustive over configurations."""
    print("[GL-2] (GR-135): the local criterion at a pure hub, verified "
          "EXHAUSTIVELY over the abstract configuration space")
    J = (0, 1, 2)
    Jc = (3, 4, 5)
    grid = [(a, b) for a in J for b in Jc]
    for d in (3, 4):
        n_ok = n_bad = 0
        n_match = 0
        for cells in product(grid, repeat=d):
            ok = _abstract_local(cells, J)
            cross = _cross_coverable(cells, J)
            assert ok == cross, f"criterion != brute force at {cells}"
            rows = {a for (a, _) in cells}
            cols = {b for (_, b) in cells}
            if d == 3:
                # the pairwise-disjoint (perfect-matching) characterization
                disj = (len(rows) == 3 and len(cols) == 3)
                assert ok == (not disj), \
                    f"perfect-matching characterization fails at {cells}"
                if disj:
                    n_match += 1
            n_ok += ok
            n_bad += (not ok)
        print(f"  hub degree {d}: {len(grid) ** d} configurations, "
              f"{n_ok} feasible, {n_bad} infeasible; criterion agrees with "
              f"brute force at {len(grid) ** d}/{len(grid) ** d}")
        if d == 3:
            print(f"    and at degree 3 the infeasible ones are EXACTLY the "
                  f"{n_match} configurations whose three pairs are pairwise "
                  f"DISJOINT, i.e. a perfect matching of the six trees "
                  f"(3! row assignments x 3! column assignments = 36 "
                  f"labelled, 1 up to relabelling)")
            assert n_bad == n_match == 36, "the degree-3 count moved"
        else:
            print("    at degree 4 the minimal infeasible patterns are the "
                  "3-transversal and the 2x2 block: "
                  f"{_cross_coverable([(0, 3), (0, 4), (1, 3), (1, 4)], J)} "
                  "for the block (must be False)")
            assert not _cross_coverable([(0, 3), (0, 4), (1, 3), (1, 4)], J)

    print("  the must-REJECT witness and its negative control (F13):")
    bad = [(0, 3), (1, 4), (2, 5)]
    assert not _abstract_local(bad, J), "the transversal witness is accepted"
    print(f"    transversal {bad}: REJECTED, as (GR-135) requires")
    for k in range(3):
        ctrl = list(bad)
        ctrl[k] = (bad[(k + 1) % 3][0], bad[k][1])
        assert _abstract_local(ctrl, J), f"negative control {ctrl} rejected"
        print(f"    one row moved -> {ctrl}: ACCEPTED (negative control)")
    print("    pinned counter-fact: every one of these four configurations "
          "has the SAME multiset of list sizes (1, 1, 1, 1, 1, 1) and the "
          "same per-branch data, so no size / counting test separates them -- "
          "the criterion is a DISJOINTNESS statement, not a count")

    print("  the tree-degree reading, asserted over the same space: at a "
          "cubic pure hub the six tree degrees sum to 12 and lie in [1, 3], "
          "so `all degrees 2` <=> `some degree 1` <=> `some degree 3`")
    nspan = nskip = 0
    for cells in product(grid, repeat=3):
        deg = [3 - sum(1 for c in cells if j in c) for j in range(6)]
        assert sum(deg) == 12, f"the degree sum moved at {cells}"
        if min(deg) < 1:
            nskip += 1        # some `T_j` would MISS `u` -- no spanning tree
            continue          # can do that, so this configuration is
            # unrealizable by a 6-tree partition of `Ghat`
        nspan += 1
        assert all(1 <= x <= 3 for x in deg)
        allz = all(x == 2 for x in deg)
        assert allz == (not _abstract_local(cells, J)), \
            f"the tree-degree reading fails at {cells}"
        assert allz == (1 not in deg) and allz == (3 not in deg), \
            f"leaf <=> degree-3 fails at {cells}"
    print(f"    {nspan}/729 configurations are realizable at all (the other "
          f"{nskip} give some `T_j` degree 0 at `u`, which no SPANNING tree "
          f"can do), and at every one of them: `u` is a LEAF of some `T_j` "
          f"<=> `u` has degree 3 in some `T_j` <=> the local system is "
          f"feasible")
    print()


# ----------------------------------------------- [GL-3] --csp: (GR-134) -----

def leg_csp():
    """[GL-3] (GR-134): the orientation normal form, cross-oracled."""
    print("[GL-3] (GR-134): the orientation normal form vs gpack.csp_witness, "
          "exhaustive over the --resid population")
    npair = nagree = nfeas = 0
    nhub = nlocal = 0
    nbadhub = nlocfail = 0
    for label, edges, hubs, br, ends, lens in shape_rows(
            12, mmax=6, lambda_free=True):
        inc = incidence(hubs, ends)
        ph = pure_hubs(hubs, ends, lens)
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                sd = split_data(lens, C, J)
                if sd is None:
                    continue
                npair += 1
                _A, P, Q, kind = sd
                mine = csp_orient(hubs, ends, lens, C, J)
                theirs = csp_witness(hubs, ends, lens, C, J)
                assert (mine is None) == (theirs is None), \
                    f"{label}: (GR-134) disagrees with (GR-132) at J={J}"
                nagree += 1
                # (GR-135) is exactly the local relaxation, at every hub
                locok = True
                for u in hubs:
                    nhub += 1
                    b = local_ok_brute(inc, lens, P, Q, J, u)
                    c = local_ok_criterion(inc, lens, C, P, J, u)
                    assert b == c, f"{label}: (GR-135) fails at hub {u}"
                    nlocal += b
                    locok = locok and b
                    if mine is not None:
                        assert b, f"{label}: feasible globally, not at {u}"
                if not locok:
                    nlocfail += 1
                    assert mine is None, "locally infeasible, globally not"
                if any(all(x == 2 for x in tree_deg(inc, C, u)) for u in ph):
                    nbadhub += 1
                    assert mine is None, \
                        f"{label}: a bad pure hub with a feasible CSP"
                if mine is None:
                    continue
                nfeas += 1
                alpha, gamma = mine
                # (GR-134)(i): clause (a) is FREE -- ASSERTED, never imposed
                sides = {u: set() for u in hubs}
                for i, (u, w) in enumerate(ends):
                    if kind[i] == 'AA':
                        sides[u].add('A')
                        sides[w].add('A')
                    elif kind[i] == 'BB':
                        sides[u].add('B')
                        sides[w].add('B')
                    elif alpha[u] in P[i] and gamma[w] in Q[i]:
                        sides[u].add('A')
                        sides[w].add('B')
                    else:
                        sides[w].add('A')
                        sides[u].add('B')
                for u in hubs:
                    assert len(sides[u]) == 2, \
                        f"{label}: hub {u} is monochromatic -- (a) NOT free"
                    td = tree_deg(inc, C, u)
                    assert td[alpha[u]] >= 1 and td[gamma[u]] >= 1, \
                        f"{label}: a tree is not spanning at {u}"
    print(f"  {nagree}/{npair} legal (packing, split) pairs: (GR-134)'s CSP "
          f"and (GR-132)'s list-colouring agree on feasibility, 0 "
          f"disagreements")
    print(f"  THE MISSING DENOMINATOR (RESEARCH-ARC section 4): {nfeas} of "
          f"those {npair} pairs are feasible and {npair - nfeas} are NOT. "
          f"gpack --resid's `229 320/229 320` is a rate over the ACCEPTED "
          f"pairs alone -- its soundness loop does `if pat is None: continue`, "
          f"so the rejected pairs are silently skipped and the figure carries "
          f"no information about how often the conflict fires")
    print(f"  and the obstruction SPLITS: {nlocfail} of the "
          f"{npair - nfeas} infeasible pairs already fail (GR-135) at some "
          f"single hub, while {npair - nfeas - nlocfail} are locally feasible "
          f"at EVERY hub and infeasible only GLOBALLY -- so the residual is "
          f"not a union of local conditions, and a purely local repair "
          f"cannot close it")
    print(f"  {nbadhub} of the infeasible pairs have a PURE HUB whose six "
          f"tree degrees are all 2 -- (GR-135)'s conflict, REALIZED, and at "
          f"every one of them the CSP is asserted infeasible")
    print(f"  clause (a) (no monochromatic hub) ASSERTED at all {nfeas} "
          f"feasible pairs, {nfeas}/{nfeas} -- so (a) is FREE ((GR-134)(i))")
    print(f"  {nlocal}/{nhub} hub-local systems feasible; (GR-135)'s "
          f"criterion agrees with the brute force at {nhub}/{nhub}")
    print()


# ---------------------------------------------- [GL-4] --rich: (GR-136) -----

K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]


def audit_shape(hubs, ends, lens, packs, first=False):
    """Over a family of 6-tree partitions: the legal-pair count, how many
    realize (GR-135)'s conflict at a pure hub, and how many are CSP-feasible.
    With `first=True` it stops at the first feasible pair -- the existence
    question, which is what (GR-18)(iii) actually asks per shape."""
    inc = incidence(hubs, ends)
    ph = pure_hubs(hubs, ends, lens)
    nleg = nbad = ngood = 0
    for trees in packs:
        C = csets(lens, trees)
        for J in legal_splits(lens, C):
            sd = split_data(lens, C, J)
            if sd is None:
                continue
            nleg += 1
            bad = any(all(x == 2 for x in tree_deg(inc, C, u)) for u in ph)
            feas = csp_orient(hubs, ends, lens, C, J) is not None
            if bad:
                nbad += 1
                assert not feas, "a bad pure hub with a feasible CSP"
            if feas:
                ngood += 1
                if first:
                    return len(ph), nleg, nbad, ngood
    return len(ph), nleg, nbad, ngood


def d0_shapes(n):
    """Every class shape of the `D = 0` stratum at `n` hubs: every cubic hub
    multigraph up to isomorphism x every excess profile, filtered by the
    (GR-25) cut criterion.  Exhaustive, never sampled."""
    M = 3 * n // 2
    for hedges in multigraphs(n, M):
        for exc in excess_profiles(M, 6):
            lens = [2 + e for e in exc]
            if cubic_habitat(n, hedges, lens):
                yield hedges, lens


def first_feasible(hubs, ends, lens, nodes=200000):
    """The first CSP-feasible legal (packing, split) pair, by a deterministic
    depth-first enumeration of the 6-tree partitions of `Ghat` with EARLY
    EXIT -- the existence question (GR-18)(iii) actually asks, at a cost that
    does not depend on how many partitions the shape has.

    Local device, and deliberately not `gpack.all_packings`: that one is
    exhaustive by design (it is the (GR-131) enumerator) and materializes the
    whole list, which is ~10 000 partitions per `n_hub = 4` shape."""
    m, n = len(ends), len(hubs)
    idx = {v: i for i, v in enumerate(hubs)}
    ed = [(idx[u], idx[w]) for u, w in ends]
    budget = [nodes]
    found = []

    def rec(i, trees):
        if found or budget[0] <= 0:
            return
        budget[0] -= 1
        if i == m:
            if not all(len(t) == n - 1 for t in trees):
                return
            C = csets(lens, [tuple(sorted(t)) for t in trees])
            for J in legal_splits(lens, C):
                if split_data(lens, C, J) is None:
                    continue
                if csp_orient(hubs, ends, lens, C, J) is not None:
                    found.append(([tuple(sorted(t)) for t in trees], J))
                    return
            return
        rem = sum(6 - lens[k] for k in range(i + 1, m))
        for Cb in combinations(range(6), 6 - lens[i]):
            nt = [list(t) for t in trees]
            ok = True
            for j in Cb:
                if len(nt[j]) >= n - 1:
                    ok = False
                    break
                nt[j].append(i)
                if cycle_rank(list(range(n)), [ed[k] for k in nt[j]]):
                    ok = False
                    break
            if not ok:
                continue
            if sum((n - 1) - len(nt[j]) for j in range(6)) > rem:
                continue
            rec(i + 1, nt)
            if found or budget[0] <= 0:
                return

    rec(0, [[] for _ in range(6)])
    return (found[0] if found else None), nodes - budget[0]


def leg_rich():
    """[GL-4] (GR-136): the leaf-covering reduction, decided EXHAUSTIVELY on
    the `n_hub = 4` half of the `D = 0` stratum, then at a constructed
    `n_hub = 6` pure-hub shape."""
    print("[GL-4] (GR-136): the leaf-covering residual on the D = 0 stratum")
    hubs = list(range(4))
    print("  (i) EXISTENCE, exhaustive over every n_hub = 4 class shape (all "
          "6-tree partitions x all 20 splits, stopping at the first feasible "
          "pair -- which is what (GR-18)(iii) asks)")
    nsh = npu = 0
    pure = []
    worstnodes = 0
    for hedges, lens in d0_shapes(4):
        nsh += 1
        hit, used = first_feasible(hubs, hedges, lens)
        worstnodes = max(worstnodes, used)
        assert hit is not None, \
            f"NO legal pair is CSP-feasible at {list(zip(hedges, lens))}"
        if pure_hubs(hubs, hedges, lens):
            npu += 1
            pure.append((hedges, lens))
    print(f"    {nsh} class shapes, {npu} of them carrying a pure hub; at "
          f"EVERY one some legal (packing, split) pair is CSP-feasible -- so "
          f"(GR-18)(iii) HOLDS, exhaustively, on this stratum (worst-case "
          f"{worstnodes} search nodes to the first witness)")
    print("  (ii) the FULL statistics on the pure-hub shapes (no early exit)")
    tleg = tbad = tgood = 0
    worst = None
    for hedges, lens in pure:
        packs = all_packings(hubs, hedges, lens)
        k, nleg, nbad, ngood = audit_shape(hubs, hedges, lens, packs)
        tleg += nleg
        tbad += nbad
        tgood += ngood
        if worst is None or nbad > worst[3]:
            worst = (hedges, lens, nleg, nbad, ngood, k)
    print(f"    {len(pure)} shapes, {tleg} legal pairs enumerated "
          f"exhaustively: {tbad} REALIZE (GR-135)'s conflict (a pure hub "
          f"with all six tree degrees 2) and every one of those is "
          f"CSP-infeasible; {tgood} are CSP-feasible")
    hedges, lens, nleg, nbad, ngood, k = worst
    print(f"    worst by conflict count: lengths {lens} on "
          f"{[tuple(e) for e in hedges]}, {k} pure hub(s), {nbad} of {nleg} "
          f"pairs conflicted, {ngood} feasible")
    print("  (iii) the constructed n_hub = 6 control (K_3,3, hub 0's star at "
          f"length 2, the other six branches at length 3; seed {L_SEED})")
    lens = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    specs = [(u, w, L) for (u, w), L in zip(K33, lens)]
    edges = class_shape(specs)
    assert edges is not None, "the constructed shape is NOT a class shape"
    assert cubic_habitat(6, K33, lens), "the (GR-25) cut criterion fails"
    hubs6 = list(range(6))
    assert pure_hubs(hubs6, K33, lens) == [0], "the pure hub moved"
    assert sum(L - 2 for L in lens) == 6, "the excess law is not tight here"
    allv = sorted(verts_of(edges), key=str)
    hs, br = branch_decomp(edges)
    ends6 = [(u, w) for (u, w, _) in br]
    lab = {v: i for i, v in enumerate(hs)}
    print(f"    certified by gridcol.class_shape AND cflank.cubic_habitat; "
          f"|V| = {len(allv)}, pure hub 0, Sum(ell-2) = 6 = 2D + 6 so "
          f"(GR-21) is tight")
    rng = random.Random(L_SEED)
    packs, used = some_packings(hs, ends6, lens, rng, RICH_WANT, RICH_NODES)
    assert packs, "no 6-tree partition found under the node budget"
    k, nleg, nbad, ngood = audit_shape(hs, ends6, lens, packs)
    print(f"    randomized DFS: {len(packs)} partitions under a "
          f"{RICH_NODES}-node budget ({used} nodes used) -> {nleg} legal "
          f"pairs, {nbad} conflicted, {ngood} CSP-feasible")
    assert nbad > 0 and ngood == 0, "the control's DFS figures moved"
    print("    READ THAT CORRECTLY (README section 4 convention 8): "
          f"{ngood} feasible pairs is NOT FOUND UNDER CAP, never `none "
          "exists` -- and here the cap is provably blind, because the "
          "certificate side exhibits one:")
    cols, capped = colourings(edges, cap=1 << 16)
    assert not capped, "the colouring enumeration hit its cap"
    ncert = nfeas6 = 0
    for col in cols:
        if not filter_pass(edges, allv, col, hs):
            continue
        trees, ok = [], True
        for mine in ('A', 'B'):
            bd = block_data(edges, allv, col, mine)
            tt, cp = fast_triple(bd)
            if cp or tt is None:
                ok = False
                break
            bc = branch_classes(bd, br)
            for grp in tt:
                gs = set(grp)
                trees.append(tuple(j for j in range(len(ends6))
                                   if not (gs & set(bc[j]))))
        if not ok:
            continue
        ncert += 1
        C = csets(lens, trees)
        J = (0, 1, 2)
        assert J in legal_splits(lens, C), "a certificate's split is illegal"
        mine6 = csp_orient(hs, ends6, lens, C, J)
        assert mine6 is not None, "a certificate-induced pair is infeasible"
        assert csp_witness(hs, ends6, lens, C, J) is not None, \
            "(GR-134) and (GR-132) disagree at n_hub = 6"
        inc6 = incidence(hs, ends6)
        assert not all(x == 2 for x in tree_deg(inc6, C, hs[0])), \
            "a feasible certificate leaves the pure hub bad"
        nfeas6 += 1
    print(f"    {len(cols)} admissible colourings, {ncert} filter-passing "
          f"with a both-block tree-triple; every one induces a legal "
          f"(packing, split) pair, and {nfeas6}/{ncert} of those are "
          f"CSP-FEASIBLE with the pure hub a LEAF of some tree -- so "
          f"(GR-18)(iii) holds at the control and the DFS sample was blind")
    assert ncert > 0 and nfeas6 == ncert, "the certificate side moved"
    print("    the blindness has a mechanism, and it is this arc's own "
          f"lesson one level down: `some_packings` collects the first "
          f"{RICH_WANT} partitions of ONE depth-first subtree, so it varies "
          "the low-index branches and holds the high-index ones nearly "
          "fixed -- a sample whose support misses the very quantifier the "
          "question is about (RESEARCH-ARC section 4)")
    print("  CAP DISCLOSURE: legs (i)/(ii) are EXHAUSTIVE (every cubic hub "
          "multigraph up to isomorphism, every excess profile, every 6-tree "
          "partition, every split) and their verdict is a statement about the "
          "n_hub = 4 D = 0 stratum and NOTHING else. Leg (iii)'s DFS figure "
          "is `not found under cap` and is DISPROVED as a nonexistence claim "
          "in the same breath; its positive figure comes from the "
          "certificate side, which is constructive. n_hub >= 6 is otherwise "
          "UNSWEPT for this question, and n_hub >= 8 entirely so.")
    print()


def verts6(edges):
    return {x for e in edges for x in e}


def main():
    ran = False
    if '--support' in sys.argv or '--validate' in sys.argv:
        leg_support()
        ran = True
    if '--local' in sys.argv or '--validate' in sys.argv:
        leg_local()
        ran = True
    if '--csp' in sys.argv or '--validate' in sys.argv:
        leg_csp()
        ran = True
    if '--rich' in sys.argv or '--validate' in sys.argv:
        leg_rich()
        ran = True
    if not ran:
        print(__doc__)


if __name__ == '__main__':
    main()
