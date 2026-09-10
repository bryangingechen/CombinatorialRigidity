"""§(K-grid) research direction GCOIND (2026-09-09) driver — (GR-161)-(GR-168):
WHICH `r`-co-independent groupings certify `dim W_coll = 0` beyond `r = 3`, and
in what class of conditions the answer is COMBINATORIAL.

A `w4/` leaf beside `gridcol.py`, importing `gridcol.py` / `gridwit.py` /
`grid.py` / `packmm.py` / `closure.py` READ-ONLY (README §2; same precedent as
gridcol -> packmm -> gridwit -> grid).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --unfence  # (GR-161) the un-fenced population at the pinned exemplar
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --reform   # (GR-162) W_coll = (V tensor C) cap (+)_j C_j, asserted against the landed dim_W
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --r4       # (GR-163)/(GR-164) THE r = 4 CRITERION and its value-independence
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --tt       # (GR-165) the uniform necessary condition: 3 disjoint cobases
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --vand     # (GR-166) det M(a) as a product of the differences
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --comb     # (GR-167) which CLASS of combinatorial condition the criterion lives in
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --r5       # (GR-168) blind axis 3: r = 5, never run before
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoind.py --validate # all seven at reduced caps

Argument state: session draft `notes/Pencil-draft-GCOIND.md` (to be merged into
`notes/pencil/workbook/grid.md` §(K-grid) as *Steps G181-G188*; labels
(GR-161)-(GR-168) per the 2026-09-09 GCOIND reservation in
`notes/pencil/labels.md`).

WHAT IS NEW HERE, in one paragraph.  *Step G22* leaves the `r >= 4` collapse
certificate as "a determinant, not a direct sum", with value-independence
MEASURED at one separator over 840 tuples and the successor question -- *`r`
co-independent groups certify iff <combinatorial condition>* -- open.  This
driver carries the REFORMULATION that settles the `r = 4` case.  Writing
`B` for the m x h fundamental-cycle matrix of the block's contracted
multigraph (`grid.fundamental_cycles`, exactly the matrix `gridwit.dim_W`
already builds), `D = diag(a_{j(e)})` and `M(a) = [B | DB | D^2 B]`, one has
`W_coll = ker M(a)` verbatim; the rows of `M` are `B_e tensor (1, a_j, a_j^2)`,
so `det B[S] != 0` iff `E minus S` is a spanning tree, i.e. iff `S` is a COBASE.
Two consequences, both proved and both asserted below:

  * (r = 4)  `V^perp` is ONE divided-difference row with all four entries
    nonzero, so `W_coll = ker( (+)_j C_j -> C )` for the plain sum map, and
    since the counts are square, `dim W_coll = 0` iff `C_1 (+) ... (+) C_4 =
    C(H_+)` -- an INTERNAL direct sum of the four deleted cycle spaces.  That
    condition names no parameter at all, so value-independence at `r = 4` is a
    THEOREM, not a measurement.

  * (any r)  the generalized Laplace expansion of `det M(a)` along the three
    column blocks has one term per ORDERED partition of `E` into three
    cobases, so a certificate at ANY `r` and ANY values forces `H_+` to split
    into three parts with pairwise-union spanning trees -- an UNCONSTRAINED
    tree-triple, i.e. (GR-9)'s condition with the class boundaries forgotten.

WHAT EACH MODE TESTS, one sentence each (README §4 / F11: the driver tests the
exact headline sentence).

--unfence  (GR-161): `gridcol.collapse_search`'s `want` parameter early-returns
           at the first certificate, so *Step G22*'s "257 of 20 967" are counts
           accumulated UP TO the first hit; called with `want` unbounded the
           same landed function reports the full canonical-partition space at
           the pinned exemplar, and `S(11,<=4)` is re-derived independently as
           the exhaustiveness check.

--reform   (GR-162): `dim W_coll` from the landed `gridwit.dim_W` equals
           `3h - rank[B | DB | D^2 B]` and equals `dim ((V tensor C) cap (+)_j
           C_j)` computed from the four deleted cycle spaces, at every
           co-independent 4-partition of the pinned exemplar and at seeded
           random value tuples -- three independent routes to one number.

--r4       (GR-163)/(GR-164): over the FULL population of co-independent
           4-partitions, `dim W_coll(F, a) = 0` iff `sum_j C(H_+ - E_j) =
           C(H_+)`, for EVERY tuple of distinct values -- the certificate is
           value-independent as a theorem, and the criterion is a direct-sum
           condition on four deleted cycle spaces.

--tt       (GR-165): every certifying `(F, a)` at every `r` forces an
           unconstrained partition of `E` into three cobases; the search for
           one is EXHAUSTIVE over ordered triples of cobases, and is
           cross-checked against Edmonds' covering condition `|A| <= 3 r*(A)`
           enumerated over ALL subsets of `E`.

--vand     (GR-166): at `r = 4`, `det M(a) = c * prod_{i<j} (a_i - a_j)^{m_ij}`
           with `m_ij = comp(H_+ - E_i - E_j) - 1`, asserted by dividing out at
           seeded random tuples and checking the quotient is a CONSTANT.

--comb     (GR-167): which class of condition the `r = 4` criterion lives in --
           the counting/connectivity statistics are enumerated on the labelled
           population, every one is tested for a perfect split, and a PAIR of
           co-independent 4-partitions agreeing on all of them and disagreeing
           on certification is hunted (the direction's falsifiable tell).

--r5       (GR-168): blind axis 3 -- `r = 5` has never been run; the mode
           enumerates co-independent 5-partitions, tests certification over
           many value tuples, and reports whether value-independence SURVIVES
           past `r = 4` (the theorem above does not reach it).

Exact throughout (`fractions.Fraction`; no floats).  Ranks are exact ℚ via
`exactcore.rank`; the one local primitive is `_det`, a fraction-exact
Gaussian-elimination determinant, because the harness has only fixed-size
`det3`/`det4`/`det6` and no general-`n` determinant (recorded as a harness-debt
candidate in the draft).  Every rng is seeded from `G_SEED` and the seed is
printed; no `set` is printed.  Nothing here samples a placement: every object
is a partition of the classes of a pinned finite multigraph, so no figure is a
rate over sampled placements (§(K-clos) (AC-9), as for `gridcol.py`).

CAPS, disclosed here and re-printed by each mode that runs under one:
  * one carrier block unless stated -- the pinned `EXEMPLAR`
    (`V6m10(3^10)`, m = 15, n_c = 11, h = 5, 11 classes) that *Step G22*
    pins; `--tt` additionally runs all 18 separators of `gridcol.SEP_SHAPES`.
  * value tuples are drawn from `randint(1, VAL_HI)` with `VAL_HI = 10**4`
    (the landed `collapse_search`'s own range) unless a mode says otherwise.
  * `--comb`'s subset-family scan is over ALL 2^m subsets at the exemplar
    (m = 15, so 32768 -- exhaustive, not sampled).
"""
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace                                 # noqa: E402
from grid import fundamental_cycles                                   # noqa: E402
from gridwit import dim_W                                             # noqa: E402
from packmm import EXEMPLAR, comp_count_nodes, synth_bd               # noqa: E402
from gridcol import T_SEED, collapse_search                           # noqa: E402

G_SEED = 20260909
VAL_HI = 10 ** 4


# ------------------------------------------------------------- primitives ---

def _det(rows):
    """Exact rational determinant of a square matrix, by fraction-exact
    Gaussian elimination.  LOCAL: the harness carries only fixed-size
    `pitch.det3`/`det4`, `oschu.det4x4`, `framedom.det6` and `grid.det4g`;
    there is no general-`n` determinant to import (harness-debt candidate)."""
    n = len(rows)
    A = [[F(x) for x in row] for row in rows]
    assert all(len(r) == n for r in A), "det of a non-square matrix"
    d = F(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c] != 0), None)
        if piv is None:
            return F(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        d *= A[c][c]
        inv = F(1) / A[c][c]
        A[c] = [x * inv for x in A[c]]
        for i in range(c + 1, n):
            if A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return d


def cyc_matrix(bd):
    """The m x h fundamental-cycle matrix `B` of the block's contracted
    multigraph, in the SAME basis `gridwit.dim_W` uses (`B[e][i] = z_i(e)`)."""
    zb = fundamental_cycles(bd['nodes'], bd['ced'])
    assert len(zb) == bd['h']
    m = len(bd['E'])
    return [[F(z.get(k, 0)) for z in zb] for k in range(m)]


def collapse_matrix(B, grp_of_edge, vals):
    """`M(a) = [B | DB | D^2 B]`, row `e` being `B_e tensor (1, a_j, a_j^2)`.
    This is the matrix `gridwit.dim_W` builds; `--reform` asserts that."""
    out = []
    for e, row in enumerate(B):
        a = vals[grp_of_edge[e]]
        out.append([x * a ** p for p in range(3) for x in row])
    return out


def edge_groups(bd, assign, cids, r):
    """(groups as class-id sets, group index per EDGE) for an assignment."""
    pos = {c: i for i, c in enumerate(cids)}
    grps = [set(c for c in cids if assign[pos[c]] == g) for g in range(r)]
    goe = [assign[pos[bd['cls'][k]]] for k in range(len(bd['E']))]
    return grps, goe


def coindependent(bd, grp):
    """`H_+ - E_j` connected, i.e. group `grp` co-independent ((GR-19)(ii),
    §(K-grid)).  Uses the landed `packmm.comp_count_nodes`."""
    rem = [bd['ced'][k] for k in range(len(bd['E']))
           if bd['cls'][k] not in grp]
    return comp_count_nodes(bd['nodes'], rem) == 1


def deleted_cycle_space(B, goe, j):
    """Basis of `C_j = C(H_+ - E_j) = {phi in C : phi_e = 0 for e in E_j}`,
    in the fundamental-cycle coordinates (so a list of h-vectors)."""
    rows = [B[e] for e in range(len(B)) if goe[e] == j]
    if not rows:
        h = len(B[0])
        return [[F(1) if i == k else F(0) for i in range(h)] for k in range(h)]
    return nullspace(rows)


def canonical_assignments(n, r):
    """Every restricted-growth string of length `n` onto AT MOST `r` blocks --
    byte-for-byte the recursion `gridcol.collapse_search` enumerates (its
    `tried` counts these, and rejects the ones with an empty group)."""
    a = [0] * n

    def rec(i, used):
        if i == n:
            yield list(a)
            return
        for g in range(min(used + 1, r)):
            a[i] = g
            yield from rec(i + 1, max(used, g + 1))
    yield from rec(0, 0)


def stirling2(n, k):
    """S(n, k), by the recurrence -- the independent count `--unfence` checks
    the enumeration against."""
    tab = [[0] * (k + 1) for _ in range(n + 1)]
    tab[0][0] = 1
    for i in range(1, n + 1):
        for j in range(1, k + 1):
            tab[i][j] = j * tab[i - 1][j] + tab[i - 1][j - 1]
    return tab[n][k]


def exemplar_bd():
    return synth_bd(EXEMPLAR['nodes'], EXEMPLAR['ced'], EXEMPLAR['cls'])


def distinct_vals(rng, r, hi=VAL_HI):
    vals = []
    while len(set(vals)) < r:
        vals = [F(rng.randint(1, hi)) for _ in range(r)]
    return vals


def coind_population(bd, r):
    """Every co-independent canonical `r`-partition of the block's classes,
    as (assignment, groups, group-of-edge).  EXHAUSTIVE: no early return, no
    time budget -- that is the whole point of this mode."""
    cids = sorted(set(bd['cls']))
    out = []
    tried = 0
    for assign in canonical_assignments(len(cids), r):
        tried += 1
        grps, goe = edge_groups(bd, assign, cids, r)
        if any(not g for g in grps):
            continue
        if all(coindependent(bd, g) for g in grps):
            out.append((assign, grps, goe))
    return tried, out


# --------------------------------------------------- [GCO-1] --unfence ------

def leg_unfence():
    """[GCO-1] (GR-161): *Step G22*'s "257 of 20 967" are early-return counts.
    Re-derived by PARAMETERIZING the landed `collapse_search` (its `want=1`
    default is the fence), never by re-implementing it."""
    print(f"[GCO-1] (GR-161) the un-fenced collapse population "
          f"(gridcol's own seed {T_SEED + 5}, then {G_SEED})")
    bd = exemplar_bd()
    ncls = len(set(bd['cls']))
    print(f"  pinned exemplar {EXEMPLAR['label']}: m = {len(bd['E'])}, "
          f"n_c = {bd['n_c']}, h = {bd['h']}, {ncls} classes")
    # (a) gridcol.leg_hier's EXACT call sequence -- one rng, r = 3 then r = 4
    rng = random.Random(T_SEED + 5)
    f3 = collapse_search(bd, 3, rng)
    f4 = collapse_search(bd, 4, rng)
    print(f"  fenced, gridcol's sequence: r = 3 tried {f3['tried']} coind "
          f"{f3['coind']} cert {f3['cert']}; r = 4 tried {f4['tried']} coind "
          f"{f4['coind']} cert {f4['cert']}")
    assert (f3['tried'], f3['coind'], f3['cert']) == (29525, 0, 0)
    assert (f4['tried'], f4['coind'], f4['cert']) == (20967, 257, 1), \
        "*Step G22*'s quoted r = 4 figures did not reproduce"
    # (b) the same landed function, un-fenced
    rng = random.Random(G_SEED)
    u3 = collapse_search(bd, 3, rng, budget=600.0, want=10 ** 9)
    u4 = collapse_search(bd, 4, rng, budget=600.0, want=10 ** 9)
    assert not u3['timeout'] and not u4['timeout'], "budget hit"
    print(f"  un-fenced (want = 10^9): r = 3 tried {u3['tried']} coind "
          f"{u3['coind']} cert {u3['cert']}; r = 4 tried {u4['tried']} coind "
          f"{u4['coind']} cert {u4['cert']}")
    for r, res in ((3, u3), (4, u4)):
        exp = sum(stirling2(ncls, k) for k in range(1, r + 1))
        assert res['tried'] == exp, \
            f"un-fenced r = {r} not exhaustive: {res['tried']} != {exp}"
        print(f"    S({ncls},<={r}) = {exp} == un-fenced `tried`, so the "
              f"un-fenced run IS the complete space")
    assert u3['tried'] == f3['tried'], \
        "r = 3 was already exhaustive (the fence never fires with 0 certs)"
    assert u4['tried'] > f4['tried'] and u4['coind'] > f4['coind']
    print("  => the fence is `collapse_search`'s `if res['cert'] >= want: "
          "return`.  At r = 3 it never fires (no certificate), so *Step "
          "G22*'s")
    print("     r = 3 figure IS exhaustive; at r = 4 it fires at the first "
          "hit, so 20967/257/1 are PREFIX counts, not the population.")
    print()


# ----------------------------------------------------- [GCO-2] --reform -----

def leg_reform(cap=400):
    """[GCO-2] (GR-162): three independent routes to `dim W_coll`."""
    print(f"[GCO-2] (GR-162) the reformulation (seed {G_SEED + 20})")
    rng = random.Random(G_SEED + 20)
    bd = exemplar_bd()
    B = cyc_matrix(bd)
    cids = sorted(set(bd['cls']))
    h, m = bd['h'], len(bd['E'])
    tried, pop = coind_population(bd, 4)
    print(f"  co-independent 4-partitions: {len(pop)} of {tried} canonical")
    checked = 0
    for assign, grps, goe in pop[:cap]:
        vals = distinct_vals(rng, 4)
        sv = {c: vals[assign[cids.index(c)]] for c in cids}
        # route 1: the landed driver
        d1 = dim_W(bd, sval=sv)
        # route 2: the matrix M(a) = [B | DB | D^2 B]
        M = collapse_matrix(B, goe, vals)
        d2 = 3 * h - rank(M)
        # route 3: (V tensor C) cap (+)_j C_j, built from the four DELETED
        # cycle spaces and the Vandermonde space V = <(1..), (a_j), (a_j^2)>
        bases = [deleted_cycle_space(B, goe, j) for j in range(4)]
        # a vector of (+)_j C_j is (v_0,...,v_3), v_j in C_j; it lies in
        # V tensor C iff the (r-3) divided-difference rows annihilate it
        lam = [F(1) / _prod(vals[i] - vals[k] for k in range(4) if k != i)
               for i in range(4)]
        cols = []
        for j, bas in enumerate(bases):
            for v in bas:
                cols.append((j, v))
        rows = []
        for i in range(h):                       # one row per coordinate of C
            rows.append([lam[j] * v[i] for (j, v) in cols])
        d3 = len(cols) - rank(rows) if cols else 0
        assert d1 == d2 == d3, \
            f"routes disagree: landed {d1}, matrix {d2}, subspace {d3}"
        assert sum(len(b) for b in bases) == 4 * h - m, \
            "co-independence should force dim C_j = h - |E_j|"
        checked += 1
    print(f"  dim_W (landed) == 3h - rank[B|DB|D^2B] == dim((V tensor C) cap "
          f"(+)_j C_j): {checked}/{checked} co-independent 4-partitions")
    print(f"    (cap: the first {cap} of {len(pop)}, one seeded value tuple "
          f"each from randint(1, {VAL_HI}))")
    # the cobase reading of det B[S]
    cob = 0
    for S in itertools.combinations(range(m), h):
        rem = [bd['ced'][k] for k in range(m) if k not in S]
        tree = (comp_count_nodes(bd['nodes'], rem) == 1
                and len(rem) == bd['n_c'] - 1)
        d = _det([B[k] for k in S])
        assert (d != 0) == tree, \
            f"det B[S] != 0 does not read as 'E minus S is a spanning tree'"
        cob += 1 if tree else 0
    print(f"  det B[S] != 0 iff E minus S is a spanning tree: asserted over all "
          f"C({m},{h}) = {len(list(itertools.combinations(range(m), h)))} "
          f"subsets; {cob} cobases")
    print()


def _prod(it):
    out = F(1)
    for x in it:
        out *= x
    return out


# --------------------------------------------------------- [GCO-3] --r4 ----

def sum_deleted_is_full(B, goe, r):
    """`sum_j C(H_+ - E_j) = C(H_+)`?  Computed from the four deleted cycle
    spaces in fundamental-cycle coordinates -- NO parameter enters."""
    h = len(B[0])
    cols = []
    for j in range(r):
        cols.extend(deleted_cycle_space(B, goe, j))
    return (rank(cols) == h) if cols else (h == 0)


def spans_meet_trivially(B, goe, r):
    """`cap_j span{B_e : e in E_j} = 0`?  The dual form of the same test:
    `U_j = C_j^0`, so the sum is full iff the annihilators meet in 0."""
    h = len(B[0])
    cur = [[F(1) if i == k else F(0) for i in range(h)] for k in range(h)]
    for j in range(r):
        Uj = [B[e] for e in range(len(B)) if goe[e] == j]
        if not Uj:
            return False if h else True
        # cur := cur cap U_j, via annihilators: (X cap Y)^0 = X^0 + Y^0
        ann = nullspace(cur) if cur else \
            [[F(1) if i == k else F(0) for i in range(h)] for k in range(h)]
        annU = nullspace(Uj)
        cur = nullspace(ann + annU) if (ann + annU) else \
            [[F(1) if i == k else F(0) for i in range(h)] for k in range(h)]
        if not cur:
            return True
    return not cur


def leg_r4(cap_full=None, tuples=4, cap_840=40):
    """[GCO-3] (GR-163)/(GR-164): the r = 4 criterion, over the FULL
    co-independent population, and its value-independence."""
    print(f"[GCO-3] (GR-163)/(GR-164) the r = 4 criterion (seed {G_SEED + 30})")
    rng = random.Random(G_SEED + 30)
    bd = exemplar_bd()
    B = cyc_matrix(bd)
    cids = sorted(set(bd['cls']))
    tried, pop = coind_population(bd, 4)
    if cap_full is not None:
        pop = pop[:cap_full]
    print(f"  population: {len(pop)} co-independent 4-partitions "
          f"(of {tried} canonical); {tuples} seeded distinct-value tuples "
          f"each from randint(1, {VAL_HI})")
    vt = [distinct_vals(rng, 4) for _ in range(tuples)]
    npos = nneg = 0
    for assign, grps, goe in pop:
        crit = sum_deleted_is_full(B, goe, 4)
        assert crit == spans_meet_trivially(B, goe, 4), \
            "the sum form and the annihilator form of the criterion disagree"
        for vals in vt:
            sv = {c: vals[assign[cids.index(c)]] for c in cids}
            z = (dim_W(bd, sval=sv) == 0)
            assert z == crit, \
                f"criterion fails at {grps} with values {vals}"
        npos += 1 if crit else 0
        nneg += 0 if crit else 1
    print(f"  dim W_coll(F, a) = 0  <=>  sum_j C(H_+ - E_j) = C(H_+)  "
          f"<=>  cap_j span(E_j) = 0")
    print(f"    asserted at every one of {len(pop)} partitions x {tuples} "
          f"value tuples: {npos} certify, {nneg} do not, 0 disagreements")
    print(f"  the split is VALUE-FREE: the criterion mentions no parameter, "
          f"so it is the same at every distinct-value tuple")
    # the 840-tuple check of (GR-19)(v), extended from ONE partition to a
    # sample of BOTH labels
    sub = pop[:cap_840] + pop[-cap_840:]
    bad = 0
    for assign, grps, goe in sub:
        crit = sum_deleted_is_full(B, goe, 4)
        for vals in itertools.permutations(range(1, 8), 4):
            sv = {c: F(vals[assign[cids.index(c)]]) for c in cids}
            if (dim_W(bd, sval=sv) == 0) != crit:
                bad += 1
    print(f"  (GR-19)(v)'s 840-tuple value-independence check, extended from "
          f"its ONE partition to {len(sub)} partitions of BOTH labels: "
          f"{bad} deviations of {len(sub) * 840}")
    assert bad == 0
    print("  => at r = 4 a NEGATIVE is a proof too: `not certified under the")
    print("     draws = 3 cap` and `does not certify` COINCIDE, because the")
    print("     criterion does not mention the values.")
    print()


# --------------------------------------------------------- [GCO-4] --tt ----

def cobases(bd):
    """Every cobase of the block's contracted multigraph -- every `h`-subset
    of `E` whose complement is a spanning tree.  EXHAUSTIVE over C(m, h)."""
    m, h = len(bd['E']), bd['h']
    out = []
    for S in itertools.combinations(range(m), h):
        rem = [bd['ced'][k] for k in range(m) if k not in S]
        if len(rem) == bd['n_c'] - 1 and \
                comp_count_nodes(bd['nodes'], rem) == 1:
            out.append(frozenset(S))
    return out


def unconstrained_tree_triple(bd):
    """A partition of `E` into three cobases, IGNORING the class boundaries
    -- (GR-9)'s tree-triple with the classes forgotten.  EXHAUSTIVE over
    ordered pairs of cobases; returns the first witness or None."""
    cb = set(cobases(bd))
    full = frozenset(range(len(bd['E'])))
    for s0 in sorted(cb):
        for s1 in sorted(cb):
            if s0 & s1:
                continue
            s2 = full - s0 - s1
            if s2 in cb:
                return (sorted(s0), sorted(s1), sorted(s2))
    return None


def edmonds_cover3(bd):
    """Edmonds' covering condition for 3 independent sets in the COGRAPHIC
    matroid: `|A| <= 3 r*(A)` for every `A subset E`, i.e.
    `comp(H_+ - A) <= 1 + 2|A|/3`.  EXHAUSTIVE over all 2^m subsets; returns
    (holds, a violating A or None)."""
    m = len(bd['E'])
    for bits in range(1 << m):
        A = [k for k in range(m) if bits >> k & 1]
        rem = [bd['ced'][k] for k in range(m) if not (bits >> k & 1)]
        if 3 * (comp_count_nodes(bd['nodes'], rem) - 1) > 2 * len(A):
            return False, A
    return True, None


BRIDGE_CTRL = dict(                       # a balance-SHAPED block with a
    label='synthetic bridge control (m = 6, n_c = 5, h = 2)',
    nodes=[0, 1, 2, 3, 4],                # bridge, hence no tree-triple
    ced=[(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (3, 4)],
    cls=[0, 1, 2, 3, 4, 5])


def leg_tt(seps=True):
    """[GCO-4] (GR-165): a certificate at ANY r forces an UNCONSTRAINED
    tree-triple; the class-respecting one is what the 18 separators lack."""
    print(f"[GCO-4] (GR-165) the uniform necessary condition (seed "
          f"{G_SEED + 40})")
    bd = exemplar_bd()
    cb = cobases(bd)
    tt = unconstrained_tree_triple(bd)
    ok, viol = edmonds_cover3(bd)
    print(f"  pinned exemplar: {len(cb)} cobases; UNCONSTRAINED tree-triple "
          f"{'EXISTS' if tt else 'does NOT exist'}: {tt}")
    print(f"    Edmonds cover-by-3 condition |A| <= 3 r*(A) over all "
          f"2^{len(bd['E'])} = {1 << len(bd['E'])} subsets: "
          f"{'holds' if ok else f'VIOLATED at {viol}'}")
    assert (tt is not None) == ok, \
        "the constructive search and Edmonds' condition disagree"
    assert tt is not None, \
        "the exemplar certifies at r = 4, so a tree-triple is FORCED"
    print("    *Step G22* records NO tree-triple at this block -- that is "
          "the CLASS-RESPECTING one ((GR-9)); the unconstrained one exists,")
    print("    and the Laplace expansion of det M(a) makes it NECESSARY for "
          "any certificate at any r.")
    # the constructed negative control: a balance-shaped block with a bridge
    ctl = synth_bd(BRIDGE_CTRL['nodes'], BRIDGE_CTRL['ced'],
                   BRIDGE_CTRL['cls'])
    assert len(ctl['E']) == 3 * ctl['h'] and ctl['n_c'] == 2 * ctl['h'] + 1, \
        "the control is not balance-shaped"
    cok, cviol = edmonds_cover3(ctl)
    ctt = unconstrained_tree_triple(ctl)
    print(f"  {BRIDGE_CTRL['label']}: tree-triple "
          f"{'EXISTS' if ctt else 'does NOT exist'}; Edmonds "
          f"{'holds' if cok else f'VIOLATED at A = {cviol}'}")
    assert ctt is None and not cok
    rng = random.Random(G_SEED + 40)
    tot = 0
    for r in range(3, len(set(ctl['cls'])) + 1):
        res = collapse_search(ctl, r, rng, budget=120.0, want=10 ** 9)
        assert not res['timeout']
        tot += res['cert']
        print(f"    r = {r}: tried {res['tried']:5d}  coind {res['coind']:5d}"
              f"  cert {res['cert']}")
    assert tot == 0, "a bridged block certified -- the necessity claim fails"
    print(f"    => 0 certificates at ANY r up to #classes, EXHAUSTIVELY, on "
          f"a block with no unconstrained tree-triple.")
    if seps:
        print("  the 18 habitat separators of *Step G16*:")
        for label, b in separator_blocks():
            t = unconstrained_tree_triple(b)
            e, _ = edmonds_cover3(b) if len(b['E']) <= 20 else (None, None)
            print(f"    {label}: m = {len(b['E'])}, h = {b['h']}, "
                  f"unconstrained tree-triple "
                  f"{'EXISTS' if t else 'does NOT exist'}"
                  + ("" if e is None else f"; Edmonds {'holds' if e else 'VIOLATED'}"))
            assert t is not None, \
                f"{label} certifies at r = 4 but has no tree-triple"
    print()


def separator_blocks():
    """The 18 habitat separators, re-found exactly as `gridcol.leg_hier`
    does (same seed, same gates) -- imported logic, not re-implemented."""
    import closure
    from closure import colourings, combinatorial_filter
    from grid import block_data, census_shapes, dim_Z_generic
    from kbare_common import verts_of
    from packmm import fast_triple
    from gridcol import SEP_SHAPES
    rng = random.Random(T_SEED + 5)
    out = []
    for label, edges in census_shapes():
        if label not in SEP_SHAPES:
            continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 12)
        assert not odd and cols is not None
        for col in cols:
            if combinatorial_filter(edges, allverts, col):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            for mine in ('A', 'B'):
                b = block_data(edges, allverts, col, mine)
                tt, capped = fast_triple(b)
                if capped or tt is not None:
                    continue
                if dim_Z_generic(b, rng, draws=3) > 0:
                    continue
                if dim_Z_generic(b, rng, draws=8) > 0:
                    continue
                out.append((label, b))
    assert len(out) == 18, f"re-found {len(out)} separators, not 18"
    return out


# ------------------------------------------------------- [GCO-5] --vand ----

def perm_sign(seq):
    """Sign of the permutation given by `seq` (a rearrangement of 0..n-1)."""
    seq = list(seq)
    seen = [False] * len(seq)
    sgn = 1
    for i in range(len(seq)):
        if seen[i]:
            continue
        j, ln = i, 0
        while not seen[j]:
            seen[j] = True
            j = seq[j]
            ln += 1
        if ln % 2 == 0:
            sgn = -sgn
    return sgn


def ordered_tree_triples(bd, B):
    """Every ORDERED partition of `E` into three cobases, with the Laplace
    sign `eps * det B[S_0] * det B[S_1] * det B[S_2]` attached.  These are
    exactly the nonzero terms of the block-Laplace expansion of
    `det [B | DB | D^2 B]` -- EXHAUSTIVE, no cap."""
    cb = sorted(cobases(bd))
    cbset = set(cb)
    dets = {S: _det([B[k] for k in sorted(S)]) for S in cb}
    full = frozenset(range(len(bd['E'])))
    out = []
    for s0 in cb:
        for s1 in cb:
            if s0 & s1:
                continue
            s2 = full - s0 - s1
            if s2 not in cbset:
                continue
            order = sorted(s0) + sorted(s1) + sorted(s2)
            eps = perm_sign(order)
            out.append((sorted(s1), sorted(s2),
                        eps * dets[s0] * dets[s1] * dets[s2]))
    return out


def leg_vand(cap=120):
    """[GCO-5] (GR-166): the block-Laplace expansion of `det M(a)`, and the
    difference-product factorization it forces at r = 4."""
    print(f"[GCO-5] (GR-166) det M(a), combinatorially (seed {G_SEED + 50})")
    rng = random.Random(G_SEED + 50)
    bd = exemplar_bd()
    B = cyc_matrix(bd)
    cids = sorted(set(bd['cls']))
    ott = ordered_tree_triples(bd, B)
    print(f"  ordered tree-triples (= nonzero Laplace terms): {len(ott)}; "
          f"unordered: {len(ott) // 6}")
    tried, pop = coind_population(bd, 4)
    checked = 0
    for assign, grps, goe in pop[:cap]:
        vals = distinct_vals(rng, 4, hi=40)
        d_direct = _det(collapse_matrix(B, goe, vals))
        d_comb = F(0)
        for s1, s2, sgn in ott:
            t = sgn
            for e in s1:
                t *= vals[goe[e]]
            for e in s2:
                t *= vals[goe[e]] ** 2
            d_comb += t
        assert d_direct == d_comb, "the Laplace expansion is wrong"
        checked += 1
    print(f"  det M(a) == sum over ordered tree-triples of "
          f"eps * prod det B[S_i] * prod_{{e in S_1}} a_j(e) * "
          f"prod_{{e in S_2}} a_j(e)^2")
    print(f"    asserted at {checked} co-independent 4-partitions x one "
          f"seeded value tuple each (values from randint(1, 40))")
    # the difference-product factorization at r = 4
    print("  r = 4 factorization  det M(a) = c * prod_{i<j} (a_i - a_j)^m_ij "
          f"with m_ij = comp(H_+ - E_i - E_j) - 1:")
    good = badpos = 0
    degbad = 0
    certs = [x for x in pop if sum_deleted_is_full(B, x[2], 4)]
    step = max(1, len(certs) // cap)
    for assign, grps, goe in certs[::step][:cap]:
        crit = True
        mij = {}
        for i, j in itertools.combinations(range(4), 2):
            rem = [bd['ced'][k] for k in range(len(bd['E']))
                   if goe[k] not in (i, j)]
            mij[(i, j)] = comp_count_nodes(bd['nodes'], rem) - 1
        cs = set()
        for _ in range(4):
            vals = distinct_vals(rng, 4, hi=60)
            d = _det(collapse_matrix(B, goe, vals))
            q = _prod((vals[i] - vals[j]) ** mij[(i, j)]
                      for i, j in itertools.combinations(range(4), 2))
            cs.add(d / q)
        if sum(mij.values()) != 3 * bd['h']:
            degbad += 1
        if len(cs) == 1 and cs != {F(0)}:
            good += 1
        else:
            badpos += 1
    print(f"    quotient constant over 4 seeded tuples at {good} certifying "
          f"partitions; NOT constant at {badpos}")
    print(f"    exponent-sum sum_i<j m_ij != 3h at {degbad} of "
          f"{good + badpos} -- a nonzero count REFUTES the m_ij guess")
    print(f"    (sum_i<j m_ij must be deg det M = 3h = {3 * bd['h']} "
          f"for the factorization to be an identity)")
    print()


# ------------------------------------------------------- [GCO-6] --comb ----

def pair_coranks(bd, goe, r):
    """`m_ij = comp(H_+ - E_i - E_j) - 1` for every pair -- the corank of the
    MERGED (r-1)-group collapse, i.e. the order to which `det M` must vanish
    on `a_i = a_j`."""
    out = {}
    for i, j in itertools.combinations(range(r), 2):
        rem = [bd['ced'][k] for k in range(len(bd['E']))
               if goe[k] not in (i, j)]
        out[(i, j)] = comp_count_nodes(bd['nodes'], rem) - 1
    return out


def comb_stats(bd, B, goe, r):
    """Every purely combinatorial statistic of `(H_+, partition)` this mode
    tests -- no parameter and no linear algebra enters any of them."""
    m = len(bd['E'])
    sizes = tuple(sorted(sum(1 for k in range(m) if goe[k] == j)
                         for j in range(r)))
    mij = pair_coranks(bd, goe, r)
    trip = []
    for T in itertools.combinations(range(r), 3):
        rem = [bd['ced'][k] for k in range(m) if goe[k] not in T]
        trip.append(comp_count_nodes(bd['nodes'], rem) - 1)
    bridges, allbridge = [], False
    br_of = {}
    for j in range(r):
        keep = [k for k in range(m) if goe[k] != j]
        base = comp_count_nodes(bd['nodes'], [bd['ced'][k] for k in keep])
        bset = set()
        for k in keep:
            rem = [bd['ced'][x] for x in keep if x != k]
            if comp_count_nodes(bd['nodes'], rem) > base:
                bset.add(k)
        br_of[j] = bset
        bridges.append(len(bset))
    for e in range(m):
        if all(e in br_of[j] for j in range(r) if j != goe[e]):
            allbridge = True
            break
    return dict(sizes=sizes,
                mij=tuple(sorted(mij.values())),
                mijsum=sum(mij.values()),
                trip=tuple(sorted(trip)),
                bridges=tuple(sorted(bridges)),
                flatmeet=allbridge)


def leg_comb(cap_stats=None, carriers=True, carrier_want=800):
    """[GCO-6] (GR-167): WHICH class of combinatorial condition decides the
    r = 4 criterion -- counting, closure, or neither."""
    print(f"[GCO-6] (GR-167) the class of the criterion (seed {G_SEED + 60})")
    bd = exemplar_bd()
    B = cyc_matrix(bd)
    tried, pop = coind_population(bd, 4)
    if cap_stats is not None:
        pop = pop[::max(1, len(pop) // cap_stats)][:cap_stats]
    rows = []
    for assign, grps, goe in pop:
        st = comb_stats(bd, B, goe, 4)
        st['cert'] = sum_deleted_is_full(B, goe, 4)
        rows.append(st)
    npos = sum(1 for x in rows if x['cert'])
    print(f"  labelled population: {len(rows)} co-independent 4-partitions, "
          f"{npos} certify, {len(rows) - npos} do not")
    keys = ('sizes', 'mij', 'mijsum', 'trip', 'bridges', 'flatmeet')
    for k in keys:
        buckets = {}
        for x in rows:
            buckets.setdefault(x[k], []).append(x['cert'])
        mixed = [v for v in buckets.values() if len(set(v)) > 1]
        nmix = sum(len(v) for v in mixed)
        verdict = ("PERFECT SPLIT" if not mixed
                   else f"{len(mixed)} mixed values covering {nmix} partitions")
        print(f"    {k:9s} ({len(buckets)} distinct values): {verdict}")
    # the composite of all of them
    buckets = {}
    for x in rows:
        buckets.setdefault(tuple(x[k] for k in keys), []).append(x['cert'])
    mixed = {kk: v for kk, v in buckets.items() if len(set(v)) > 1}
    print(f"    COMPOSITE of all {len(keys)} ({len(buckets)} distinct "
          f"values): " + ("PERFECT SPLIT" if not mixed
                          else f"{len(mixed)} mixed values covering "
                               f"{sum(len(v) for v in mixed.values())}"))
    # the counting criterion, stated
    h = bd['h']
    ge = all(x['mijsum'] >= 3 * h for x in rows)
    eq = all((x['mijsum'] == 3 * h) == x['cert'] for x in rows)
    print(f"  THE COUNTING CRITERION.  sum_{{i<j}} [comp(H_+ - E_i - E_j) - 1] "
          f">= 3h at every partition: {ge}")
    print(f"    and  = 3h  EXACTLY at the certifying ones: {eq}")
    if not eq:
        for x in rows:
            if (x['mijsum'] == 3 * h) != x['cert']:
                print(f"      first deviation: mijsum {x['mijsum']}, "
                      f"3h = {3 * h}, cert {x['cert']}")
                break
    # which SUBSETS of the battery already separate, and the simplest rule
    best = None
    for size in range(1, len(keys) + 1):
        found = []
        for sub in itertools.combinations(keys, size):
            bk = {}
            for x in rows:
                bk.setdefault(tuple(x[k] for k in sub), []).append(x['cert'])
            if all(len(set(v)) == 1 for v in bk.values()):
                found.append(sub)
        if found:
            best = (size, found)
            break
    print(f"  MINIMAL separating sub-batteries: "
          + (f"size {best[0]}: " + "; ".join("+".join(f) for f in best[1])
             if best else "none of the 2^6 - 1 subsets separates"))
    # the two-statistic cross-tabulation the split turns on
    tab = {}
    for x in rows:
        tab.setdefault((x['mijsum'], x['flatmeet']), [0, 0])[
            1 if x['cert'] else 0] += 1
    print("  cross-tab (sum m_ij, flat-meet) -> (not-cert, cert):")
    for k in sorted(tab):
        print(f"    sum m_ij = {k[0]:3d}, an edge is a bridge of all three "
              f"other deletions = {str(k[1]):5s} -> {tuple(tab[k])}")
    rule = all((x['mijsum'] == 3 * h and not x['flatmeet']) == x['cert']
               for x in rows)
    print(f"  candidate rule  [sum m_ij = 3h  AND  no edge is a bridge of "
          f"all three other deletions]  <=> certifies: {rule}")
    if carriers:
        check_rule_at_other_carriers(want=carrier_want)
    print()


def sampled_coind(bd, r, rng, want=1500, draws=200000):
    """A SEEDED SAMPLE of co-independent canonical `r`-partitions, for a block
    whose canonical space is too large to enumerate.  Returns
    (distinct partitions sampled, list of (assign, groups, goe))."""
    cids = sorted(set(bd['cls']))
    n = len(cids)
    seen, out = set(), []
    for _ in range(draws):
        a = [rng.randrange(r) for _ in range(n)]
        ren, nxt = {}, 0                       # canonicalize to restricted growth
        for i, g in enumerate(a):
            if g not in ren:
                ren[g], nxt = nxt, nxt + 1
            a[i] = ren[g]
        if nxt != r:
            continue
        t = tuple(a)
        if t in seen:
            continue
        seen.add(t)
        grps, goe = edge_groups(bd, list(a), cids, r)
        if all(coindependent(bd, g) for g in grps):
            out.append((list(a), grps, goe))
            if len(out) >= want:
                break
    return len(seen), out


def check_rule_at_other_carriers(want=800):
    """Bar (a): the rule must be tested BEYOND the pinned exemplar, or it is
    per-shape evidence.  Runs every DISTINCT separator block of *Step G16*;
    the exemplar's space is enumerated exhaustively, the larger carriers are
    SAMPLED (seeded) because S(13, <= 4) is 2.8 M."""
    print("  the same rule at the OTHER carriers -- every distinct separator "
          "block of *Step G16* (blind axis 2, partially opened):")
    rng = random.Random(G_SEED + 61)
    seen = set()
    for label, b in separator_blocks():
        sig = (tuple(b['nodes']), tuple(b['ced']), tuple(b['cls']))
        if sig in seen:
            continue
        seen.add(sig)
        B = cyc_matrix(b)
        h, ncls = b['h'], len(set(b['cls']))
        full = sum(stirling2(ncls, k) for k in range(1, 5))
        if full <= 200000:
            tried, pop = coind_population(b, 4)
            how = f"EXHAUSTIVE over all {tried} canonical"
        else:
            tried, pop = sampled_coind(b, 4, rng, want=want)
            how = (f"SAMPLED: {len(pop)} co-independent from {tried} distinct "
                   f"canonical draws of S({ncls},<=4) = {full}")
        npos = fp = fn = 0
        rows = []
        for assign, grps, goe in pop:
            crit = sum_deleted_is_full(B, goe, 4)
            st = comb_stats(b, B, goe, 4)
            st['cert'] = crit
            st['grps'] = grps
            rows.append(st)
            npos += 1 if crit else 0
            pred = (st['mijsum'] == 3 * h and not st['flatmeet'])
            if pred and not crit:
                fp += 1
            elif crit and not pred:
                fn += 1
        print(f"    {label} m={len(b['E'])} h={h} cls={ncls}: {how}; "
              f"{len(pop)} co-independent, {npos} certify; rule deviations "
              f"{fp + fn} (rule says certify but does not: {fp}; certifies "
              f"but rule says no: {fn})")
        if fp + fn:
            report_witness_pair(rows)
    print(f"    ({len(seen)} distinct separator blocks)")


def report_witness_pair(rows):
    """The direction's own falsifiable tell, in its exact form: TWO
    co-independent 4-partitions of ONE block agreeing on every combinatorial
    statistic in the battery and DISAGREEING on certification."""
    keys = ('sizes', 'mij', 'mijsum', 'trip', 'bridges', 'flatmeet')
    for k in keys + (keys,):
        sub = (k,) if isinstance(k, str) else k
        bk = {}
        for x in rows:
            bk.setdefault(tuple(x[j] for j in sub), []).append(x)
        mixed = [v for v in bk.values() if len({y['cert'] for y in v}) > 1]
        name = k if isinstance(k, str) else "COMPOSITE"
        nm = sum(len(v) for v in mixed)
        print(f"      {name:>10s}: {len(mixed)} mixed values covering {nm}")
        if not isinstance(k, str) and mixed:
            v = mixed[0]
            a = next(y for y in v if y['cert'])
            bb = next(y for y in v if not y['cert'])
            print(f"      *** WITNESS PAIR -- identical on the WHOLE battery, "
                  f"opposite labels:")
            print(f"          certifies:     {a['grps']}")
            print(f"          does NOT:      {bb['grps']}")
            print(f"          shared stats:  sizes={a['sizes']} "
                  f"mij={a['mij']} sum={a['mijsum']} trip={a['trip']} "
                  f"bridges={a['bridges']} flatmeet={a['flatmeet']}")



# --------------------------------------------------------- [GCO-7] --r5 ----

def leg_r5(cap=1200, tuples=6):
    """[GCO-7] (GR-168): BLIND AXIS 3 -- `r = 5`, which `leg_hier` never
    runs.  Does value-independence survive past the r = 4 theorem?"""
    print(f"[GCO-7] (GR-168) r = 5, never run before (seed {G_SEED + 70})")
    rng = random.Random(G_SEED + 70)
    bd = exemplar_bd()
    B = cyc_matrix(bd)
    cids = sorted(set(bd['cls']))
    h = bd['h']
    tried, pop = coind_population(bd, 5)
    print(f"  co-independent 5-partitions: {len(pop)} of {tried} canonical "
          f"(S(11,<=5)); cap: the first {min(cap, len(pop))} scanned, "
          f"{tuples} seeded distinct-value tuples each")
    vt = [distinct_vals(rng, 5) for _ in range(tuples)]
    split = []                      # certifies at some tuple, not at another
    always = never = 0
    for assign, grps, goe in pop[:cap]:
        zs = []
        for vals in vt:
            sv = {c: vals[assign[cids.index(c)]] for c in cids}
            zs.append(dim_W(bd, sval=sv) == 0)
        if all(zs):
            always += 1
        elif not any(zs):
            never += 1
        else:
            split.append((grps, [i for i, z in enumerate(zs) if z]))
    print(f"    certifies at ALL {tuples} tuples: {always};  at NONE: "
          f"{never};  VALUE-DEPENDENT (some yes, some no): {len(split)}")
    if split:
        grps, which = split[0]
        print(f"    WITNESS -- value-dependence at r = 5: {grps}")
        print(f"      certifies at tuple index {which} of "
              f"{list(range(tuples))}")
        print(f"      so past r = 4 a certificate is a property of (F, a), "
              f"NOT of F: the r = 4 theorem does not extend.")
    else:
        print(f"    NO value-dependent 5-partition found under this cap -- "
              f"'not found under cap', never 'does not exist'.")
    # THE RIGHT INSTRUMENT: random tuples are GENERIC, and by (GR-7)
    # remark (i) `dim W` can only go UP at a special point, so a
    # value-dependent partition is one that certifies generically and fails
    # somewhere special.  `prod_{i<j} (a_i - a_j)^{m_ij}` always divides the
    # homogeneous degree-3h `det M`, so the residual factor has degree
    # `3h - sum m_ij`; it is ZERO-FREE off the diagonal exactly when that is
    # 0.  So: scan `sum m_ij` on the generically-certifying partitions.
    resid = {}
    for assign, grps, goe in pop[:cap]:
        zs = all(dim_W(bd, sval={c: v[assign[cids.index(c)]]
                                 for c in cids}) == 0 for v in vt[:2])
        if not zs:
            continue
        ssum = sum(pair_coranks(bd, goe, 5).values())
        resid.setdefault(3 * h - ssum, []).append((assign, goe, grps))
    print(f"    residual-factor degree 3h - sum_{{i<j}} m_ij on the "
          f"generically-certifying 5-partitions: "
          + ", ".join(f"deg {d}: {len(v)}" for d, v in sorted(resid.items())))
    pos = [d for d in resid if d > 0]
    if pos:
        d0 = min(pos)
        assign, goe, grps = resid[d0][0]
        print(f"      a residual factor of degree {d0} means det M is NOT "
              f"the difference product, so it HAS zeros off the diagonal --")
        print(f"      hunting a rational witness at {grps}:")
        found = slice_scan(bd, B, cids, resid, 5)
        found = found or univariate_witness(bd, B, assign, goe, cids, 5)
        if found:
            vals, dw = found
            print(f"      VALUE-DEPENDENT: dim W_coll = {dw} at the DISTINCT "
                  f"rational tuple a = {[str(v) for v in vals]},")
            print(f"      while dim W_coll = 0 at the seeded generic tuples "
                  f"-- so past r = 4 a certificate is a property of (F, a),")
            print(f"      NOT of F, and the r = 4 theorem does NOT extend.")
        else:
            print(f"      no rational root of the residual factor found by "
                  f"univariate interpolation -- not found under that cap")
    else:
        print(f"      every generically-certifying 5-partition has residual "
              f"degree 0, i.e. det M IS the difference product -- so "
              f"value-independence is a THEOREM at r = 5 too, on this block")
    # is the r = 4 criterion's shape still right at r = 5?
    dsum = 0
    for assign, grps, goe in pop[:200]:
        if sum_deleted_is_full(B, goe, 5):
            dsum += 1
    print(f"    (for reference: `sum_j C(H_+ - E_j) = C(H_+)` -- the r = 4 "
          f"criterion's statement -- holds at {dsum} of the first 200; at "
          f"r = 5 it is NOT the criterion, the counts are no longer square)")
    print()


def lagrange_coeffs(xs, ys):
    """Exact coefficients (ascending) of the interpolating polynomial."""
    n = len(xs)
    co = [F(0)] * n
    for i in range(n):
        num = [F(1)]                     # prod_{k != i} (x - x_k)
        den = F(1)
        for k in range(n):
            if k == i:
                continue
            num = [F(0)] + num
            num = [num[j] - (xs[k] * (num[j + 1] if j + 1 < len(num) else 0))
                   for j in range(len(num))]
            den *= xs[i] - xs[k]
        for j, c in enumerate(num):
            co[j] += ys[i] * c / den
    return co


def rational_roots(co):
    """Every rational root of an exact-ℚ polynomial (ascending coeffs), by
    the rational-root theorem on its integer normalization."""
    while co and co[-1] == 0:
        co = co[:-1]
    if len(co) < 2:
        return []
    from math import gcd
    den = 1
    for c in co:
        den = den * c.denominator // gcd(den, c.denominator)
    ic = [int(c * den) for c in co]
    shift = 0
    while ic[shift] == 0:
        shift += 1
    roots = [F(0)] if shift else []
    ic = ic[shift:]
    a0, an = abs(ic[0]), abs(ic[-1])

    def divisors(n):
        out = []
        d = 1
        while d * d <= n:
            if n % d == 0:
                out += [d, n // d]
            d += 1
        return sorted(set(out))
    for pn in divisors(a0):
        for q in divisors(an):
            for sg in (1, -1):
                r = F(sg * pn, q)
                if sum(c * r ** i for i, c in enumerate(ic)) == 0:
                    roots.append(r)
    return sorted(set(roots))


def univariate_witness(bd, B, assign, goe, cids, r, base=(1, 2, 3, 4, 5, 6)):
    """Fix all but one group's value and solve `det M = 0` in the last one.
    `det M` restricted this way is a univariate polynomial of degree
    `2 |E_last|`; interpolate it exactly and take its rational roots."""
    last = r - 1
    dlast = 2 * sum(1 for k in range(len(bd['E'])) if goe[k] == last)
    fixed = [F(v) for v in base[:r - 1]]
    xs = [F(x) for x in range(-1, dlast + 2)]
    ys = []
    for x in xs:
        vals = fixed + [x]
        ys.append(_det(collapse_matrix(B, goe, vals)))
    co = lagrange_coeffs(xs, ys)
    for rt in rational_roots(co):
        if rt in fixed:
            continue
        vals = fixed + [rt]
        sv = {c: vals[assign[cids.index(c)]] for c in cids}
        dw = dim_W(bd, sval=sv)
        if dw != 0:
            return vals, dw
    return None


def deflate(co, roots):
    """Divide out every factor `(x - v)`, `v` in `roots`, to full multiplicity;
    return (quotient coeffs, {v: multiplicity})."""
    co = list(co)
    while co and co[-1] == 0:
        co = co[:-1]
    mult = {}
    for v in roots:
        while len(co) > 1:
            q, rem = [F(0)] * (len(co) - 1), F(0)
            acc = F(0)
            for i in range(len(co) - 1, 0, -1):
                acc = co[i] + acc * v if i < len(co) - 1 else co[i]
                q[i - 1] = acc
            rem = co[0] + q[0] * v
            if rem != 0:
                break
            co = q
            mult[v] = mult.get(v, 0) + 1
    return co, mult


def slice_scan(bd, B, cids, resid, r, cap=60, base=(1, 2, 3, 4, 5, 6)):
    """Value-independence at `r` holds iff `det M(a)` is a constant times a
    product of powers of the DIFFERENCES.  Slice-wise test: fix every group's
    value but one, interpolate `det M` exactly in the free one, and deflate
    by the fixed values; a quotient of positive degree is a zero OFF the
    diagonal, i.e. a value-dependent certificate (over the algebraic
    closure).  Reports the first one and hunts a rational point on it."""
    cands = [x for d, v in sorted(resid.items()) if d > 0 for x in v][:cap]
    print(f"      slice test over {len(cands)} generically-certifying "
          f"5-partitions with a positive residual degree:")
    offdiag = 0
    first = None
    for assign, goe, grps in cands:
        for last in range(r):
            fixed = [F(v) for v in base[:r]]
            free = list(range(r))
            free.remove(last)
            dlast = 2 * sum(1 for k in range(len(bd['E'])) if goe[k] == last)
            xs = [F(x) for x in range(-2, dlast + 2)]
            ys = []
            for x in xs:
                vals = list(fixed)
                vals[last] = x
                ys.append(_det(collapse_matrix(B, goe, vals)))
            co = lagrange_coeffs(xs, ys)
            q, mult = deflate(co, [fixed[i] for i in free])
            if len(q) > 1:
                offdiag += 1
                if first is None:
                    first = (assign, goe, grps, last, q, mult)
                break
    print(f"        partitions whose det M has a zero OFF the diagonal: "
          f"{offdiag} of {len(cands)}")
    if first is None:
        print(f"        => on every one of them det M IS a product of "
              f"powers of the differences, so the certificate is "
              f"value-independent")
        return None
    assign, goe, grps, last, q, mult = first
    print(f"        WITNESS partition {grps}, free group {last}: after "
          f"deflating the fixed values (multiplicities {mult}) the quotient "
          f"still has degree {len(q) - 1}")
    for rt in rational_roots(q):
        vals = [F(v) for v in base[:r]]
        if rt in [vals[i] for i in range(r) if i != last]:
            continue
        vals[last] = rt
        sv = {c: vals[assign[cids.index(c)]] for c in cids}
        dw = dim_W(bd, sval=sv)
        if dw != 0:
            return vals, dw
    print(f"        the off-diagonal zero is IRRATIONAL (no rational root of "
          f"the deflated quotient) -- value-dependence over the algebraic")
    print(f"        closure, not exhibited at a rational tuple")
    return None


# --------------------------------------------------------------- main ------

MODES = ('unfence', 'reform', 'r4', 'tt', 'vand', 'comb', 'r5')

# --validate runs every mode at a REDUCED cap; the caps are here, not buried.
VALIDATE_KW = dict(unfence={}, reform=dict(cap=40),
                   r4=dict(cap_full=300, tuples=2, cap_840=4),
                   tt=dict(seps=False), vand=dict(cap=15),
                   comb=dict(cap_stats=400, carriers=True, carrier_want=120),
                   r5=dict(cap=300, tuples=3))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    for mode in MODES:
        ap.add_argument(f'--{mode}', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    run = [m for m in MODES if getattr(args, m)]
    if args.validate or not run:
        print("--validate: every mode at the reduced caps in VALIDATE_KW\n")
        for m in MODES:
            globals()[f'leg_{m}'](**VALIDATE_KW[m])
        return
    for m in run:
        globals()[f'leg_{m}']()


if __name__ == '__main__':
    main()
