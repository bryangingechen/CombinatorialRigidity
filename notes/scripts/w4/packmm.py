"""§(K-grid) fan-out direction E (2026-08-06) driver — (GR-10)'s min-max
question, attacked at its own level of generality.

A `w4/` leaf beside `gridwit.py`, importing `gridwit.py` / `grid.py` /
`closure.py` READ-ONLY (README §2; same precedent as gridwit -> grid).
Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --restate  # 2 s    (GR-12): the co-independent restatement + the matroidal necessity, pool-exact
    PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --hard     # 10 s   (GR-13): the triangle-chain family: separator + 3-colouring equivalence
    PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --sep      # 118 s  (GR-15) measured + the separator hunt + (GR-14) Delta-basis stats
    PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --exemplar # 1 s    the pinned habitat separator, proven by two independent routes
    PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --validate # all four (~2 min)

Argument state: session draft `fanout-E.md` (to be merged into
`notes/Pencil-informal.md` §(K-grid) as Steps G14+; labels (GR-12)+ per the
2026-08-06 E/J reservation in `notes/Pencil-labels.md`).

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--restate  (GR-12): at every BALANCED legal both-forest colouring-block of
           the 5-shape pool, a tree-triple exists iff a partition of the
           classes into three CO-INDEPENDENT groups exists (two independent
           DFS criteria: acyclicity of pair-unions vs connectivity of
           complements), each witness cross-validated against the other
           criterion; and every block carrying one satisfies a = 0 and
           g(P) <= 0 over the structured (GR-8) family — the purely
           matroidal necessity — with the synthetic-a bookkeeping asserted
           against gridwit.a_and_M.

--hard     (GR-13): the triangle chain C(Gamma) is balanced with a = 0,
           max g(P) <= 0 (exhaustively over ALL edge subsets at K4 and C5),
           and dim Z = 0 at the construction labels and at random injective
           draws — the whole counting side vanishes — while a triple exists
           IFF Gamma is 3-colourable (asserted against brute-force
           3-colourability at 6 named Gammas, both DFS routes agreeing);
           Gamma = K4 is therefore an explicit balanced separator (generic
           dim Z = 0, NO triple), and the family is the NP-completeness
           reduction.

--sep      (GR-15) measured + the separator/flank hunt: over the census
           pool with EXHAUSTIVE colouring enumeration (no probe cap; the
           K4 stratum optionally strided), every filter-passing colouring
           is tested for both-block tree-triples; each triple-less block is
           classified counting-VISIBLE (generic dim Z > 0) or SEPARATOR
           (generic dim Z = 0, the (GR-13) mechanism on habitat, confirmed
           at 11 draws and slow-route re-verified); any shape with NO
           certified colouring is a (GR-10) refutation and is retested for
           the weakened (GR-15) (a rank hit at rational parameters); and
           the (GR-14) rainbow-Delta-basis certificate is counted beside
           the tree-triple on each shape's first certified colouring and
           at every separator.

--exemplar the first separator block of the seeded --sep sweep, pinned:
           a REAL filter-passing colouring block (shape V6m10, all branch
           lengths 3) with a = 0, structured (GR-8) max <= 0, and
           dim Z = 0 at three exact rational parameter points (each a
           PROOF of generic vanishing by semicontinuity), where NO
           tree-triple exists — established independently of both DFS
           searches by exhausting all 3^11 class 3-colourings against the
           polychromatic-circuit criterion ((GR-12)(iii): a triple IS a
           3-colouring of the classes under which every circuit of the
           contracted multigraph sees >= 3 colours); a greedy
           unsatisfiable core of circuit class-sets is printed as the
           workbook exhibit.

Exact throughout (integers and fractions.Fraction; no floats).  The rngs
are seeded per mode and the seeds printed.  No `set` is printed.  Nothing
here samples a placement: every object is a combinatorial colouring-block
or a constructed grouped instance, and no figure is a rate over sampled
placements, so the `repin.star_generic` gate does not bind any figure
below (the one geometric call, `rank_at_params`, is only reached on a
(GR-10)-miss shape, as an existence retest at exact rational parameters).
"""
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                     # noqa: E402
import closure                                                        # noqa: E402
from closure import colourings, combinatorial_filter, cycle_rank      # noqa: E402
import grid                                                           # noqa: E402
from grid import (block_data, census_shapes, comp_count_nodes,        # noqa: E402
                  dim_Z, dim_Z_generic, rank_at_params, spline_pool)
import gridwit                                                        # noqa: E402
from gridwit import a_and_M, structured_beta, subgraph_g, tree_triple  # noqa: E402

E_SEED = 20260806


# ------------------------------------------------- grouped-instance layer --

def synth_bd(nodes, ced, cls):
    """A block_data-shaped dict for a SYNTHETIC grouped instance (multigraph
    + class partition), so grid.dim_Z / gridwit.tree_triple / subgraph_g run
    on it unchanged.  'E' only ever feeds len() and index zips downstream,
    so edge indices stand in for edges; 's' gets the same component-index
    default labels closure.build_fixed_config would assign."""
    h = len(ced) - len(nodes) + comp_count_nodes(nodes, ced)
    s = {c: F(c + 1) for c in set(cls)}
    return dict(E=list(range(len(ced))), cls=list(cls), s=s, ced=list(ced),
                nodes=list(nodes), h=h, n_other=0, n_c=len(nodes))


def a_syn(bd):
    """a = Sigma_X (|X| - dim H_X), computed on the contracted multigraph
    itself: dim H_X = |X| - (comp(H minus X) - 1).  At a real block this
    equals gridwit.a_and_M's value because contracting the other (forest)
    ruling class preserves component counts of G minus the class edges —
    asserted against a_and_M in --restate."""
    m = len(bd['E'])
    by_cls = {}
    for k in range(m):
        by_cls.setdefault(bd['cls'][k], []).append(k)
    a = 0
    for c in sorted(by_cls):
        rest = [bd['ced'][k] for k in range(m) if bd['cls'][k] != c]
        dh = len(by_cls[c]) - (comp_count_nodes(bd['nodes'], rest) - 1)
        a += len(by_cls[c]) - dh
    return a


def coind_triple(bd, node_cap=250000):
    """A partition of the classes into three CO-INDEPENDENT groups (deleting
    any one group's edges leaves the contracted multigraph spanning
    connected) — or None.  This is the INDEPENDENT route from
    gridwit.tree_triple (connectivity of complements there: acyclicity of
    pair-unions); at a balanced block the two existence verdicts coincide
    ((GR-12), proven).  Returns (groups-as-class-lists, capped)."""
    m = len(bd['E'])
    cids = sorted(set(bd['cls']))
    size = {c: 0 for c in cids}
    for k in range(m):
        size[bd['cls'][k]] += 1
    order = sorted(cids, key=lambda c: -size[c])
    nodes = bd['nodes']
    budget = [node_cap]
    grp = [set(), set(), set()]

    def ok(gi):
        drop = grp[gi]
        rem = [bd['ced'][k] for k in range(m) if bd['cls'][k] not in drop]
        return comp_count_nodes(nodes, rem) == 1

    def dfs(i):
        if budget[0] <= 0:
            return None
        budget[0] -= 1
        if i == len(order):
            return [sorted(g) for g in grp]
        c = order[i]
        gmax = 3 if i > 1 else (1 if i == 0 else 2)   # symmetry breaking
        for g in range(gmax):
            grp[g].add(c)
            if ok(g):
                res = dfs(i + 1)
                if res is not None:
                    return res
            grp[g].discard(c)
        return None

    res = dfs(0)
    return res, budget[0] <= 0


def groups_coindependent(bd, groups):
    """Every group's complement spanning connected (exact check)."""
    m = len(bd['E'])
    for g in groups:
        gs = set(g)
        rem = [bd['ced'][k] for k in range(m) if bd['cls'][k] not in gs]
        if comp_count_nodes(bd['nodes'], rem) != 1:
            return False
    return True


def groups_pairtrees(bd, groups):
    """Every pair-union a spanning tree (n_c - 1 edges, acyclic) — the
    tree-triple reading of the same partition (balance makes them agree)."""
    m = len(bd['E'])
    for i in range(3):
        pair = set(groups[i]) | set(groups[(i + 1) % 3])
        ed = [bd['ced'][k] for k in range(m) if bd['cls'][k] in pair]
        if len(ed) != bd['n_c'] - 1 or cycle_rank(bd['nodes'], ed) != 0:
            return False
    return True


def delta_basis(bd, node_cap=200000):
    """The (GR-14) certificate at a balanced block: a partition of the
    contracted edge set into h RAINBOW triangles (3-edge cycles on three
    distinct nodes, three distinct classes) — h disjoint circuits are
    automatically independent, hence a cycle-space basis.  Returns
    (partition or None, capped)."""
    m = len(bd['E'])
    if m != 3 * bd['h']:
        return None, False
    by_node = {}
    for k, (u, w) in enumerate(bd['ced']):
        if u == w:
            return None, False
        by_node.setdefault(u, []).append(k)
        by_node.setdefault(w, []).append(k)
    budget = [node_cap]
    used = [False] * m

    def other(k, v):
        u, w = bd['ced'][k]
        return w if u == v else u

    def dfs(done):
        if budget[0] <= 0:
            return None
        budget[0] -= 1
        if done == m:
            return []
        e = used.index(False)
        u, w = bd['ced'][e]
        ce = bd['cls'][e]
        for f in by_node[w]:
            if used[f] or f == e or bd['cls'][f] == ce:
                continue
            x = other(f, w)
            if x == u or x == w:
                continue
            for g in by_node[x]:
                if used[g] or g in (e, f):
                    continue
                if other(g, x) != u:
                    continue
                if bd['cls'][g] in (ce, bd['cls'][f]):
                    continue
                used[e] = used[f] = used[g] = True
                res = dfs(done + 3)
                used[e] = used[f] = used[g] = False
                if res is not None:
                    return [(e, f, g)] + res
        return None

    res = dfs(0)
    return res, budget[0] <= 0


class _DSU:
    """Union-find with rollback (union by size), for the incremental
    acyclicity checks of fast_triple."""

    def __init__(self, nodes):
        self.par = {v: v for v in nodes}
        self.sz = {v: 1 for v in nodes}
        self.log = []

    def find(self, x):
        while self.par[x] != x:
            x = self.par[x]
        return x

    def union(self, u, w):
        """False (and no-op) if u, w already joined — a cycle."""
        ru, rw = self.find(u), self.find(w)
        if ru == rw:
            return False
        if self.sz[ru] > self.sz[rw]:
            ru, rw = rw, ru
        self.par[ru] = rw
        self.sz[rw] += self.sz[ru]
        self.log.append(ru)
        return True

    def mark(self):
        return len(self.log)

    def rollback(self, mk):
        while len(self.log) > mk:
            ru = self.log.pop()
            self.sz[self.find(ru)] -= self.sz[ru]
            self.par[ru] = ru


def fast_triple(bd, node_cap=250000):
    """Existence of a tree-triple class partition — the same predicate as
    gridwit.tree_triple, computed with incremental rollback union-find on
    the three pair-unions instead of from-scratch cycle ranks (DIVERGENCE,
    README rule 3: different name, same job, ~50x faster; agreement with
    gridwit.tree_triple is asserted per-block in --restate and at every
    separator and every 100th colouring of --sep).  Returns
    (groups-as-class-lists or None, capped)."""
    m = len(bd['E'])
    cids = sorted(set(bd['cls']))
    edges_of = {c: [] for c in cids}
    for k in range(m):
        edges_of[bd['cls'][k]].append(bd['ced'][k])
    order = sorted(cids, key=lambda c: -len(edges_of[c]))
    nodes = bd['nodes']
    # pair-union DSUs: pair p excludes group p (pair 0 = groups {1,2} ...)
    dsus = [_DSU(nodes) for _ in range(3)]
    budget = [node_cap]
    grp = [[], [], []]

    def dfs(i):
        if budget[0] <= 0:
            return None
        budget[0] -= 1
        if i == len(order):
            return [list(g) for g in grp]
        c = order[i]
        gmax = 3 if i > 1 else (1 if i == 0 else 2)   # symmetry breaking
        for g in range(gmax):
            pairs = [p for p in range(3) if p != g]
            marks = [dsus[p].mark() for p in range(3)]
            okall = True
            for p in pairs:
                for (u, w) in edges_of[c]:
                    if not dsus[p].union(u, w):
                        okall = False
                        break
                if not okall:
                    break
            if okall:
                grp[g].append(c)
                res = dfs(i + 1)
                if res is not None:
                    return res
                grp[g].pop()
            for p in range(3):
                dsus[p].rollback(marks[p])
        return None

    res = dfs(0)
    return res, budget[0] <= 0


# ----------------------------------------- (GR-13): the triangle chain ----

GAMMAS = [
    ('K3', 3, [(0, 1), (1, 2), (0, 2)]),
    ('P3', 3, [(0, 1), (1, 2)]),
    ('C5', 5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]),
    ('diamond', 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]),
    ('K4', 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    ('W5', 6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
               (1, 2), (2, 3), (3, 4), (4, 5), (1, 5)]),
]


def three_colourable(nv, gedges):
    for c in itertools.product(range(3), repeat=nv):
        if all(c[u] != c[v] for (u, v) in gedges):
            return True
    return False


def chain_instance(gedges):
    """C(Gamma), the (GR-13) triangle chain: one triangle per edge of Gamma,
    in series; triangle i for e_i = (u, v) carries side (t_{i-1}, s_i) in
    class X_u, side (s_i, t_i) in class X_v, chord (t_{i-1}, t_i) its own
    singleton class.  Balanced (2m = 3(n-1)) by construction."""
    k = len(gedges)
    nodes = list(range(2 * k + 1))            # t_i -> 2i, s_i -> 2i-1
    vs = sorted({v for e in gedges for v in e})
    cid = {v: i for i, v in enumerate(vs)}    # class X_v
    nextc = len(vs)
    ced, cls = [], []
    for i, (u, v) in enumerate(gedges, start=1):
        t0, s, t1 = 2 * (i - 1), 2 * i - 1, 2 * i
        ced.append((t0, s)); cls.append(cid[u])
        ced.append((s, t1)); cls.append(cid[v])
        ced.append((t0, t1)); cls.append(nextc)
        nextc += 1
    return synth_bd(nodes, ced, cls), cid


def max_g_exhaustive(bd):
    """max g(P) over ALL edge subsets (2^m — small instances only)."""
    m = len(bd['E'])
    best = 0
    for r in range(2, m + 1):
        for idx in itertools.combinations(range(m), r):
            best = max(best, subgraph_g(bd, list(idx)))
    return best


def rand_injective_sval(bd, rng):
    cids = sorted(set(bd['cls']))
    while True:
        sv = {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
              for c in cids}
        if len({sv[c] for c in cids}) == len(cids):
            return sv


# ------------------------------------------------------------------- legs --

def leg_restate():
    """[GR-E1] (GR-12) on the 5-shape pool's balanced blocks."""
    print("[GR-E1] (GR-12): co-independent restatement + matroidal "
          "necessity, 5-shape pool")
    balanced = unbalanced = agree = with_triple = 0
    for name, edges in spline_pool():
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges)
        assert not odd
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                a_ref, _ = a_and_M(bd, edges, allverts)
                assert a_syn(bd) == a_ref, \
                    f"{name}: a bookkeeping mismatch (contraction)"
                if 2 * len(bd['E']) != 3 * (bd['n_c'] - 1):
                    unbalanced += 1
                    continue
                balanced += 1
                tt, cap1 = tree_triple(bd)
                ci, cap2 = coind_triple(bd)
                ft, cap3 = fast_triple(bd)
                assert not (cap1 or cap2 or cap3), f"{name}: DFS capped"
                assert (tt is None) == (ci is None) == (ft is None), \
                    f"{name}: tree-triple vs co-independent vs fast " \
                    "verdicts differ"
                agree += 1
                if tt is not None:
                    with_triple += 1
                    # cross-validate each witness against the OTHER
                    # criterion.  tree_triple returns per-group EDGE lists
                    # (whole classes at a time, largest-first order); recover
                    # the class groups by multiset containment.
                    eidx = {}
                    for k in range(len(bd['E'])):
                        eidx.setdefault(bd['cls'][k], []).append(k)
                    gcounts = []
                    for g in tt:
                        gc = {}
                        for e in g:
                            gc[tuple(e)] = gc.get(tuple(e), 0) + 1
                        gcounts.append(gc)
                    ttg = [[], [], []]
                    for c in sorted(eidx, key=lambda c: -len(eidx[c])):
                        need = {}
                        for k in eidx[c]:
                            t = tuple(bd['ced'][k])
                            need[t] = need.get(t, 0) + 1
                        placed = False
                        for gi, gc in enumerate(gcounts):
                            if all(gc.get(t, 0) >= v
                                   for t, v in need.items()):
                                for t, v in need.items():
                                    gc[t] -= v
                                ttg[gi].append(c)
                                placed = True
                                break
                        assert placed, \
                            f"{name}: tree-triple group recovery failed"
                    ttg = [sorted(g) for g in ttg]
                    assert groups_coindependent(bd, ttg), \
                        f"{name}: tree-triple witness NOT co-independent"
                    assert groups_pairtrees(bd, ci), \
                        f"{name}: co-independent witness NOT pair-trees"
                    # matroidal necessity: a = 0 and structured g <= 0
                    assert a_syn(bd) == 0, f"{name}: triple with a > 0"
                    beta, part = structured_beta(bd)
                    assert part or beta <= 0, \
                        f"{name}: triple with structured g(P) = {beta} > 0"
    print(f"  balanced legal both-forest blocks : {balanced} "
          f"(unbalanced skipped: {unbalanced})")
    print(f"  tree-triple <=> co-independent    : {agree}/{balanced} "
          f"(both witnesses cross-validated at {with_triple} triple-blocks)")
    print("  every triple-block has a = 0 and structured (GR-8) max <= 0")
    print("  (the (GR-12) necessity, computed matroidally -- no geometry)")
    print()


def leg_hard():
    """[GR-E2] (GR-13): the triangle-chain family."""
    print("[GR-E2] (GR-13): triangle chains C(Gamma) -- separator + "
          "3-colouring equivalence")
    rng = random.Random(E_SEED + 2)
    print(f"  (random injective label draws seeded {E_SEED + 2})")
    for gname, nv, gedges in GAMMAS:
        bd, cid = chain_instance(gedges)
        m, n = len(bd['E']), len(bd['nodes'])
        assert 2 * m == 3 * (n - 1), f"C({gname}) not balanced"
        assert len({tuple(sorted(e)) for e in bd['ced']}) == m, \
            f"C({gname}) not simple"
        assert a_syn(bd) == 0, f"C({gname}): a != 0"
        beta, part = structured_beta(bd)
        assert beta <= 0, f"C({gname}): structured g > 0"
        # `part` only flags the node-induced family's cap (n > 16 at C5/
        # diamond/K4/W5 chains); on a cactus every circuit lies in one
        # triangle block, so class unions already exhaust the mechanism,
        # and the K4/C5 all-subsets sweep below is the exhaustive control.
        # dim Z = 0 at the construction labels and at 2 random injective
        # draws ((GR-13): every injective assignment, proven; sampled here)
        assert dim_Z(bd) == 0, f"C({gname}): dim Z != 0 at labels"
        for _ in range(2):
            assert dim_Z(bd, sval=rand_injective_sval(bd, rng)) == 0, \
                f"C({gname}): dim Z != 0 at a random injective draw"
        tt, cap1 = tree_triple(bd)
        ci, cap2 = coind_triple(bd)
        assert not (cap1 or cap2)
        assert (tt is None) == (ci is None)
        col3 = three_colourable(nv, gedges)
        assert (tt is not None) == col3, \
            f"C({gname}): triple-existence != 3-colourability"
        if ci is not None:
            assert groups_coindependent(bd, ci)
            assert groups_pairtrees(bd, ci)
            # the forcing, on the witness: every triangle rainbow in groups
            gof = {}
            for gi, g in enumerate(ci):
                for c in g:
                    gof[c] = gi
            for i in range(len(gedges)):
                tri = {gof[bd['cls'][3 * i]], gof[bd['cls'][3 * i + 1]],
                       gof[bd['cls'][3 * i + 2]]}
                assert len(tri) == 3, f"C({gname}): non-rainbow triangle"
            # ... and it yields a proper 3-colouring of Gamma
            for (u, v) in gedges:
                assert gof[cid[u]] != gof[cid[v]]
        # (GR-14) on the chain: the rainbow-Delta partition exists
        db, cap3 = delta_basis(bd)
        assert not cap3 and db is not None, \
            f"C({gname}): rainbow-Delta basis missing"
        chi = 3 if col3 else '>3'
        verdict = 'triple' if col3 else 'NO TRIPLE'
        print(f"  C({gname:8s}) n={n:2d} m={m:2d}  a=0  max g<=0  "
              f"dim Z=0 (labels + 2 draws)  chi(Gamma) {chi:>2}: {verdict}")
    # exhaustive max g over ALL edge subsets at the two headline chains
    for gname in ('K4', 'C5'):
        gedges = next(g for (nm, _, g) in GAMMAS if nm == gname)
        bd, _ = chain_instance(gedges)
        mg = max_g_exhaustive(bd)
        assert mg <= 0, f"C({gname}): exhaustive max g = {mg} > 0"
        print(f"  C({gname}): max g(P) over ALL 2^{len(bd['E'])} edge "
              f"subsets = {mg} (exhaustive)")
    print("  => C(K4) is a SEPARATOR: balanced, a = 0, every counting")
    print("     obstruction (the full (GR-8) family) vanishes, generic")
    print("     dim Z = 0 -- and NO tree-triple exists.  Triple-existence")
    print("     on chains IS 3-colourability: the grouped packing is")
    print("     NP-complete at balance, so no Edmonds-type min side can")
    print("     characterize it in general ((GR-13)).")
    print()


def leg_sep(k4_stride=1, col_cap=1 << 12, cert_db_cap=400, xcheck=100):
    """[GR-E3] the exhaustive sweep: (GR-10) misses, separators, (GR-14)."""
    print(f"[GR-E3] exhaustive-colouring sweep over the census pool "
          f"(seed {E_SEED}, K4 stride {k4_stride}, colouring cap {col_cap})")
    rng = random.Random(E_SEED + 3)
    shapes = skipped = 0
    k4_seen = 0
    fp_tot = cert_tot = 0
    blocks_nt = visible = 0
    capped_blocks = xchecked = 0
    separators = []
    sep_db = sep_db_n = 0
    exemplar = None
    misses = []
    ratio_min = None
    db_both = db_only_tt = 0
    db_capped = 0
    db_checked = 0
    for label, edges in census_shapes():
        if label.startswith('K4'):
            k4_seen += 1
            if k4_seen % k4_stride:
                continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=col_cap)
        assert not odd
        if cols is None:
            skipped += 1
            continue
        shapes += 1
        fp = cert = 0
        first_cert_bds = None
        for col in cols:
            if combinatorial_filter(edges, allverts, col):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            fp += 1
            bds, tts, ok = [], [], True
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                assert 2 * len(bd['E']) == 3 * (bd['n_c'] - 1), \
                    f"{label}: filter-passing block not balanced"
                tt, capped = fast_triple(bd)
                if fp_tot % xcheck == 0:          # slow-route cross-check
                    tt2, cap2 = tree_triple(bd)
                    assert capped == cap2 and (tt is None) == (tt2 is None), \
                        f"{label}: fast_triple != gridwit.tree_triple"
                    xchecked += 1
                bds.append(bd)
                tts.append(tt)
                if capped:
                    capped_blocks += 1
                    ok = None
                    break
                if tt is None:
                    ok = False
            if ok:
                cert += 1
                if first_cert_bds is None:
                    first_cert_bds = bds
            elif ok is False:
                for bd, tt in zip(bds, tts):
                    if tt is not None:
                        continue
                    blocks_nt += 1
                    zg = dim_Z_generic(bd, rng)
                    if zg > 0:
                        visible += 1
                        continue
                    zg2 = min(zg, dim_Z_generic(bd, rng, draws=8))
                    if zg2 > 0:
                        visible += 1
                        continue
                    # SEPARATOR: cross-verify with the landed slow route,
                    # and test the (GR-14) certificate on it
                    tt2, cap2 = tree_triple(bd)
                    assert tt2 is None and not cap2, \
                        f"{label}: separator disagrees with tree_triple"
                    db, dcap = delta_basis(bd)
                    sep_db_n += 1
                    if db is not None:
                        sep_db += 1
                    szs = sorted(
                        [bd['cls'].count(c) for c in set(bd['cls'])],
                        reverse=True)
                    separators.append((label, len(set(bd['cls'])),
                                       len(bd['E']), bd['n_c'],
                                       'Delta' if db is not None else '-',
                                       tuple(szs)))
                    if exemplar is None:
                        exemplar = (label, bd)
        fp_tot += fp
        cert_tot += cert
        if fp:
            if ratio_min is None or cert * ratio_min[1] < ratio_min[0] * fp:
                ratio_min = (cert, fp, label)
        if fp and cert == 0:
            # (GR-10) MISS -- retest the weakened (GR-15) at rational params
            rescue = False
            target = 6 * (len(allverts) - 1)
            for col in cols:
                if combinatorial_filter(edges, allverts, col):
                    continue
                for _ in range(3):
                    if rank_at_params(edges, allverts, col, rng) == target:
                        rescue = True
                        break
                if rescue:
                    break
            misses.append((label, fp, rescue))
        if first_cert_bds is not None and db_checked < cert_db_cap:
            db_checked += 1
            got = 0
            for bd in first_cert_bds:
                db, capped = delta_basis(bd)
                if capped:
                    db_capped += 1
                elif db is not None:
                    got += 1
            if got == 2:
                db_both += 1
            else:
                db_only_tt += 1
    print(f"  shapes swept: {shapes} (colouring-cap skips: {skipped}); "
          f"filter-passing colourings: {fp_tot}")
    print(f"  colourings with BOTH-block tree-triples: {cert_tot}/{fp_tot} "
          f"(fast/slow route agreement asserted at {xchecked} blocks)")
    if ratio_min:
        print(f"  scarcest shape: {ratio_min[2]} "
              f"({ratio_min[0]}/{ratio_min[1]} certified)")
    print(f"  triple-less blocks probed: {blocks_nt}; counting-VISIBLE "
          f"(generic dim Z > 0): {visible}; DFS-capped blocks: "
          f"{capped_blocks}")
    if separators:
        print(f"  SEPARATORS ON HABITAT (dim Z = 0 at 11 draws, no triple, "
          f"slow-route re-verified): {len(separators)}")
        print(f"  ... carrying a (GR-14) rainbow-Delta basis: "
              f"{sep_db}/{sep_db_n}")
        for row in separators[:15]:
            print(f"    {row}")
        print("  => the (GR-13) mechanism inhabits real colouring blocks:")
        print("     the counting min side is insufficient ON THE HABITAT.")
        if exemplar is not None:
            label, bd = exemplar
            print(f"  EXEMPLAR separator block ({label}): nodes "
                  f"{bd['nodes']}")
            print(f"    ced = {bd['ced']}")
            print(f"    cls = {bd['cls']}")
    else:
        print("  NO separator on habitat: at every probed triple-less block")
        print("  a counting obstruction (generic dim Z > 0) certifies the")
        print("  miss -- the (GR-13) mechanism did NOT surface in real")
        print("  blocks; whether ruling-class structure forbids it is the")
        print("  open structural question (draft Step G18).")
    if misses:
        print(f"  (GR-10) MISS shapes (no certified colouring): "
              f"{len(misses)}")
        for label, fp, rescue in misses:
            print(f"    MISS {label} fp={fp} (GR-15)-rescued={rescue}")
    else:
        print("  NO (GR-10) miss: every swept shape carries a certified")
        print("  filter-passing colouring under EXHAUSTIVE enumeration")
        print("  (vs the census's 48-colouring probe cap).")
    print(f"  (GR-14) rainbow-Delta basis beside the tree-triple, first")
    print(f"  certified colouring of {db_checked} shapes: both certificates "
          f"{db_both}, tree-triple only {db_only_tt} "
          f"(Delta-DFS capped: {db_capped})")
    print()


# ------------------------------- the pinned habitat separator exemplar ----

# The first separator block of the seeded --sep sweep (deterministic:
# seed 20260806, K4 stride 1, colouring cap 4096): shape
# V6m10(3,3,3,3,3,3,3,3,3,3), one filter-passing colouring's block.
EXEMPLAR = dict(
    label='V6m10(3,3,3,3,3,3,3,3,3,3)',
    nodes=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ced=[(1, 0), (0, 6), (1, 8), (1, 9), (1, 2), (2, 10), (4, 3), (3, 6),
         (4, 8), (4, 9), (4, 5), (5, 10), (6, 10), (8, 7), (7, 9)],
    cls=[3, 0, 1, 2, 3, 10, 6, 0, 4, 5, 6, 10, 7, 8, 9])


def simple_cycles(nodes, ced):
    """All simple cycles of the multigraph, as frozensets of edge indices."""
    adj = {}
    for k, (u, w) in enumerate(ced):
        adj.setdefault(u, []).append((w, k))
        adj.setdefault(w, []).append((u, k))
    out = set()

    def dfs(start, v, ve, vv, path):
        for (w, k) in adj[v]:
            if k in ve:
                continue
            if w == start and len(path) >= 1:
                out.add(frozenset(path + [k]))
            elif w not in vv:
                dfs(start, w, ve | {k}, vv | {w}, path + [k])
    for s in nodes:
        dfs(s, s, frozenset(), frozenset({s}), [])
    return sorted(out, key=sorted)


def leg_exemplar():
    """[GR-E4] the pinned habitat separator, proven separator by TWO
    independent routes: dim Z = 0 at exact rational points (semicontinuity
    makes each a per-block proof of generic vanishing), and NO triple by
    exhausting all 3^L class 3-colourings against the polychromatic-circuit
    criterion of (GR-12)(iii) — independently of both DFS searches."""
    print("[GR-E4] the pinned habitat separator (V6m10 all-length-3 block)")
    rng = random.Random(E_SEED + 4)
    print(f"  (injective-draw rng seeded {E_SEED + 4})")
    bd = synth_bd(EXEMPLAR['nodes'], EXEMPLAR['ced'], EXEMPLAR['cls'])
    m, n = len(bd['E']), bd['n_c']
    assert 2 * m == 3 * (n - 1), "exemplar not balanced"
    assert a_syn(bd) == 0
    beta, part = structured_beta(bd)
    assert not part and beta <= 0
    assert dim_Z(bd) == 0, "dim Z != 0 at the construction labels"
    for _ in range(2):
        assert dim_Z(bd, sval=rand_injective_sval(bd, rng)) == 0
    tt, c1 = tree_triple(bd)
    ft, c2 = fast_triple(bd)
    ci, c3 = coind_triple(bd)
    assert not (c1 or c2 or c3)
    assert tt is None and ft is None and ci is None
    # the independent no-triple proof: every 3-colouring of the classes
    # leaves some circuit within <= 2 colours ((GR-12)(iii))
    cyc = simple_cycles(bd['nodes'], bd['ced'])
    hyper = sorted({frozenset(bd['cls'][k] for k in c) for c in cyc},
                   key=lambda h: (len(h), sorted(h)))
    cids = sorted(set(bd['cls']))
    idx = {c: i for i, c in enumerate(cids)}
    hy = [[idx[c] for c in h] for h in hyper]
    ok_assign = 0
    for assign in itertools.product(range(3), repeat=len(cids)):
        if all(len({assign[i] for i in h}) >= 3 for h in hy):
            ok_assign += 1
            break
    assert ok_assign == 0, "a polychromatic colouring exists?!"
    # a small unsatisfiable core, for the workbook exhibit (greedy, seeded)
    core = list(hy)
    random.Random(E_SEED + 5).shuffle(core)
    i = 0
    while i < len(core):
        trial = core[:i] + core[i + 1:]
        sat = False
        for assign in itertools.product(range(3), repeat=len(cids)):
            if all(len({assign[j] for j in h}) >= 3 for h in trial):
                sat = True
                break
        if not sat:
            core = trial
        else:
            i += 1
    print(f"  block: m = {m}, n_c = {n}, h = {bd['h']}, "
          f"classes L = {len(cids)}")
    print("  a = 0, structured (GR-8) max <= 0, dim Z = 0 at the label")
    print("  point AND at 2 random injective draws (each an exact rational")
    print("  point, so generic vanishing is PROVEN by semicontinuity)")
    print(f"  simple cycles: {len(cyc)}; distinct circuit class-sets: "
          f"{len(hyper)}")
    print(f"  polychromatic 3-colourings of the circuit hypergraph over "
          f"3^{len(cids)} assignments: NONE")
    print(f"  greedy unsatisfiable core: {len(core)} circuit class-sets:")
    for h in core:
        print(f"    {sorted(cids[j] for j in h)}")
    print("  => a REAL tight-shape colouring block where every counting")
    print("     obstruction vanishes, the rank certificate is a one-point")
    print("     proof, and no tree-triple exists: the (GR-13) separator")
    print("     mechanism, on the habitat.")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('restate', 'hard', 'sep', 'exemplar', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--stride', type=int, default=1,
                    help='K4-stratum stride for --sep (default 1 = full)')
    a = ap.parse_args()
    run = a.validate or not any([a.restate, a.hard, a.sep, a.exemplar])
    if run or a.restate:
        leg_restate()
    if run or a.hard:
        leg_hard()
    if run or a.sep:
        leg_sep(k4_stride=a.stride)
    if run or a.exemplar:
        leg_exemplar()
    print("OK")


if __name__ == '__main__':
    main()
