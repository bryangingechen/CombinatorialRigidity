"""§(K-grid) fan-out direction TCOL (2026-08-07) driver — (GR-15),
colouring-existence on the tight stratum, attacked through a BRANCH-LEVEL
reduction of the obstruction space.

A `w4/` leaf beside `packmm.py`, importing `packmm.py` / `gridwit.py` /
`grid.py` / `closure.py` READ-ONLY (README §2; same precedent as
packmm -> gridwit -> grid).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --branch  # (GR-16) the branch-level reduction, asserted against the landed dim Z
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --runs    # (GR-17) the circuit law, its two-profile binding list, and the constructed kill
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --pack    # (GR-18) the 6-spanning-tree decomposition of Ghat, and (GR-10) as a grouping of it
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --hier    # (GR-19) the r-group collapse hierarchy; collapse order 4 at the 18 separators
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --wide    # THE CHEAP KILL on the strata the census never swept (multigraph G-degree)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --validate  # all five

Argument state: session draft `fanout-TCOL.md` (to be merged into
`notes/Pencil-informal-grid.md` §(K-grid) as Steps G19+; labels (GR-16)+ per the
2026-08-07 PEX/TCOL reservation in `notes/Pencil-labels.md`).

WHAT IS NEW HERE, in one paragraph.  §(K-grid) Steps G1-G18 work inside the
CONTRACTED multigraph `H_+ = G/E_B`, whose size grows with the subdivision.
This driver carries the reduction to the HUB multigraph: at a legal
colouring, `H_+` is the subdivision of `G-degree / Lambda_B` in which branch
`beta` becomes a path of `A(beta) = |E_A cap beta|` edges, its classes are
the hub stars plus private singletons, and (GR-7)'s interpolation space `W`
is

    W_A = { Q in C(G-degree) tensor K[t]_{<=2} : R_beta | Q_beta for all beta },

`R_beta` = prod over the classes met on beta of (t - t_X), of degree
`A(beta)`.  Unknowns 3c, conditions sum_beta A(beta) = 3c at balance: the
system is square on the HUB graph, `c = cycle rank of G-degree`, with no
reference to the subdivision.  Everything below is a statement about
`(G-degree, length profile, branch bits)` -- which is the granularity
*Step G12* says a uniform argument must have.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--branch  (GR-16): at every colouring-block of the census pool, `dim Z`
          computed by the landed `grid.dim_Z` (a 3h x m kernel over the
          contracted EDGE space) equals `a + (M - 3h) + dim W_branch`, with
          `dim W_branch` the kernel of the 3c-column BRANCH system above --
          at the construction labels and at seeded random labels; and the
          predicted class structure (hub stars + singletons, one class per
          A-run) is asserted edge-by-edge.

--runs    (GR-17): for every circuit of the hub multigraph and every
          admissible colouring, the number of distinct A-classes on it
          equals the number of maximal A-runs of the corresponding cycle of
          `G` (equivalently `(L - r + h_neq)/2`) unless two runs are merged
          by a Lambda_A path off the circuit; the same number serves both
          blocks; `dim Z = 0` in a block forces every circuit to carry >= 3
          distinct classes; and the ONLY circuit length-profiles at which
          that can fail are (2,2,3) and (2,2,2,2) -- with a CONSTRUCTED
          class shape carrying a (2,2,3) circuit, a filter-passing colouring
          the criterion must reject, and a negative control.

--pack    (GR-18): at every pool shape the Nash-Williams/Tutte condition for
          6 edge-disjoint spanning trees holds for `Ghat` = the hub
          multigraph with branch `beta` given multiplicity `6 - ell_beta`
          (exhaustively over branch subsets), so `Ghat` partitions into 6
          spanning trees; and every both-block tree-triple ((GR-10)) IS such
          a partition -- its six branch sets are asserted to be spanning
          trees with multiplicity `3 - A(beta)` and `3 - B(beta)`.

--hier    (GR-19): a collapse of the class parameters onto r distinct values
          bounds generic `dim Z` from above ((GR-7) remark (i)), and is zero
          only if all r complements are connected; at r = 3 the family IS
          (GR-9)'s tree-triple, and at r = 4 it CERTIFIES all 18 habitat
          separators of *Step G16* -- where no tree-triple exists -- with the
          pinned exemplar's certificate asserted value-independent over all
          840 distinct integer 4-tuples from {1..7}.

--wide    THE CHEAP KILL, on strata `grid.census_shapes` never reaches:
          `kslidecomb.candidate_graphs` yields only SIMPLE hub graphs, and
          the theta family only at 3 branches, so every hub multigraph with
          a parallel branch pair (and every generalized theta) is outside
          the 907; this mode sweeps them exhaustively over branch bits and
          hunts a tight class shape with NO admissible colouring reaching
          generic `dim Z_+ = dim Z_- = 0`.

Exact throughout (integers and fractions.Fraction; no floats).  Two rank
routes are used: exact ℚ (`exactcore.rank`) for every asserted identity, and
GF(p) (`kbare_common.rank_modp`) as a CERTIFIED LOWER BOUND for the rational
rank in the `--wide` screen -- a full GF(p) rank proves full rational rank,
hence generic `dim Z = 0` by (GR-7) remark (i), and every reported witness is
re-checked in exact ℚ (README §4 convention 2).  The rngs are seeded per mode
and the seeds printed; no `set` is printed.  Nothing here samples a
placement: every object is a colouring of a pinned finite graph, so no figure
is a rate over sampled placements and `repin.star_generic` gates nothing
below (per §(K-clos) (AC-9)'s discipline, as for `gridwit.py`/`packmm.py`).
"""
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank                                            # noqa: E402
from kbare_common import verts_of, rank_modp                          # noqa: E402
from nogood_subdiv import (deficiency, hcard_ok, hub_set,             # noqa: E402
                           rigid_vertex_sets, triangles)
from kslide import no_rigid_branch_union                              # noqa: E402
import closure                                                        # noqa: E402
from closure import (colourings, combinatorial_filter, components,    # noqa: E402
                     cycle_rank, neighbors)
from grid import (block_data, census_shapes, dim_Z, dim_Z_generic,    # noqa: E402
                  fundamental_cycles)
from gridwit import a_and_M, dim_W, tree_triple                       # noqa: E402
from packmm import (EXEMPLAR, comp_count_nodes, fast_triple,          # noqa: E402
                    simple_cycles, synth_bd)

T_SEED = 20260807
P61 = (1 << 61) - 1


# ----------------------------------------------------- local devices --------

def branch_decomp(edges):
    """The branch decomposition WITH NAMED HUB ENDS.

    Local device (README rule 3, different name from any §1 primitive): the
    canonical `closure.alternation_classes` returns a branch as an *edge set
    with parities* and never names its two hub ends, and `grid.block_data`
    works inside the contracted multigraph; the branch model needs the two
    ends and the edge ORDER along the branch.  Returns
    (sorted hubs, [(u, w, [edges in path order from u to w])]) or
    (hubs, None) when `edges` has no hub at all (a bare cycle -- not a tight
    class shape for c >= 2, kept as an explicit early return)."""
    nb = neighbors(edges)
    hubs = {v for v, ns in nb.items() if len(ns) >= 3}
    if not hubs:
        return sorted(nb, key=str), None
    inc = {}
    for e in edges:
        for v in e:
            inc.setdefault(v, []).append(e)
    used, branches = set(), []
    for h in sorted(hubs, key=str):
        for e0 in inc[h]:
            if e0 in used:
                continue
            path = [e0]
            used.add(e0)
            cur = e0[1] if e0[0] == h else e0[0]
            while cur not in hubs:
                nxt = [e for e in inc[cur] if e not in used]
                assert len(nxt) == 1, "degree-2 body with != 2 edges"
                e = nxt[0]
                used.add(e)
                path.append(e)
                cur = e[1] if e[0] == cur else e[0]
            branches.append((h, cur, path))
    assert sum(len(p) for _, _, p in branches) == len(edges)
    return sorted(hubs, key=str), branches


def subdivide(specs):
    """Build the subdivision of a hub multigraph from
    specs = [(u, w, ell)] on hub labels.  Local device: `kslidecomb.
    shape_data` hard-asserts `specs[0] == (0, 1, 3)` (a length-3 SPLIT
    branch), which the widened pool of `--wide` deliberately drops."""
    edges = []
    for i, (u, w, L) in enumerate(specs):
        prev = ('h', u)
        for j in range(L - 1):
            cur = ('i', i, j)
            edges.append((prev, cur))
            prev = cur
        edges.append((prev, ('h', w)))
    return edges


def class_shape(specs):
    """Habitat certification of a hub-multigraph spec, exactly the predicate
    `grid.leg_census` asserts per shape: tight, def = 0, hnoRigid at branch
    granularity (`kslide.no_rigid_branch_union`, the census's own test),
    `hcard`, and no two-hub triangle.  Returns the edge list or None."""
    edges = subdivide(specs)
    V = verts_of(edges)
    if 5 * len(edges) != 6 * (len(V) - 1):
        return None
    if deficiency(edges) != 0:
        return None
    pmap = []
    for i, (u, w, L) in enumerate(specs):
        vs = [('h', u)] + [('i', i, j) for j in range(L - 1)] + [('h', w)]
        pmap.append(vs)
    if not no_rigid_branch_union(edges, pmap):
        return None
    if not hcard_ok(edges):
        return None
    hubs = hub_set(edges)
    if any(len(t & hubs) >= 2 for t in triangles(edges)):
        return None
    return edges


def branch_classes(bd, branches):
    """Per branch, the sorted list of class ids of the block's own-colour
    edges lying on it (`bd` from `grid.block_data`)."""
    cls_of = {e: c for e, c in zip(bd['E'], bd['cls'])}
    return [sorted({cls_of[e] for e in path if e in cls_of})
            for (_, _, path) in branches]


def dim_W_branch(bd, hubs, branches, sval=None, modp=False):
    """dim W in the BRANCH model: quadratic curves Q(t) in the cycle space of
    the HUB multigraph whose branch-beta component vanishes at every class
    parameter met on beta.

    Rows: one per (branch, class-on-that-branch).  Columns: 3c, the
    coefficients of (phi_0, phi_1, phi_2) in a fundamental-cycle basis of the
    hub multigraph.  This is a DIFFERENT matrix from both `grid.dim_Z`
    (3h x m over the contracted edge space) and `gridwit.dim_W` (m x 3h over
    the contracted edge space): its size is set by the hub graph, not by the
    subdivision."""
    s = bd['s'] if sval is None else sval
    ends = [(u, w) for (u, w, _) in branches]
    cyc = fundamental_cycles(hubs, ends)
    c = len(cyc)
    if c == 0:
        return 0
    rows = []
    for k, ks in enumerate(branch_classes(bd, branches)):
        for X in ks:
            t = s[X]
            rows.append([F(z.get(k, 0)) * t ** p
                         for p in range(3) for z in cyc])
    if not rows:
        return 3 * c
    r = rank_modp(rows, P61) if modp else rank(rows)
    return 3 * c - r


def block_generic_zero(bd, hubs, branches, rng, draws=2, modp=True):
    """True iff generic dim Z = 0 is PROVEN for this block: an exact
    rational parameter draw at which the branch system has full rank.  With
    `modp` the rank is a GF(p) lower bound for the rational rank, so a full
    GF(p) rank already proves it (README §4 convention 2); the caller
    re-checks the attaining draw in exact ℚ."""
    for _ in range(draws):
        sv = {c: F(rng.randint(1, 10 ** 4)) for c in set(bd['cls'])}
        if dim_W_branch(bd, hubs, branches, sval=sv, modp=modp) == 0:
            return sv
    return None


def filter_pass(edges, allverts, col, hubs):
    """The (GR-2) filter: balanced, both ruling classes forests, no
    monochromatic hub, all bodies distinct."""
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    if len(EA) != len(EB):
        return False
    if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
        return False
    for v in hubs:
        if len({col[e] for e in edges if v in e}) == 1:
            return False
    return closure.build_fixed_config(edges, allverts, col) is not None


def cycle_walk(branches, ends, cyc):
    """Order a circuit's branches cyclically: [(branch index, u, w)]."""
    ks = sorted(cyc)
    if len(ks) == 1:
        return [(ks[0], ends[ks[0]][0], ends[ks[0]][1])]
    adj = {}
    for k in ks:
        u, w = ends[k]
        adj.setdefault(u, []).append(k)
        adj.setdefault(w, []).append(k)
    k0 = ks[0]
    u0, w0 = ends[k0]
    walk, used, cur = [(k0, u0, w0)], {k0}, w0
    while len(used) < len(ks):
        nxt = [k for k in adj[cur] if k not in used]
        assert len(nxt) == 1
        k = nxt[0]
        a, b = ends[k]
        if a != cur:
            a, b = b, a
        walk.append((k, a, b))
        used.add(k)
        cur = b
    assert cur == u0
    return walk


def cycle_edge_seq(branches, walk):
    """The cycle of `G` as an ordered edge list, following the walk."""
    out = []
    for (k, u, _w) in walk:
        rem, cur = list(branches[k][2]), u
        while rem:
            e = next(e for e in rem if cur in e)
            rem.remove(e)
            out.append(e)
            cur = e[1] if e[0] == cur else e[0]
    return out


# --------------------------------------------- [GRC-1] --branch: (GR-16) ----

def pool_shapes(cap=None):
    for i, (label, edges) in enumerate(census_shapes()):
        if cap is not None and i >= cap:
            return
        yield label, edges


def leg_branch(shape_cap=None, col_cap=1 << 14, per_shape=32):
    """[GRC-1] (GR-16): the branch-level reduction, asserted against the
    landed contracted-space computation."""
    print(f"[GRC-1] (GR-16) branch-level reduction (seed {T_SEED + 1}); "
          f"{shape_cap or 'all'} census shapes, <= {per_shape} blocks each")
    rng = random.Random(T_SEED + 1)
    blocks = ident = bal = 0
    struct = 0
    sizes = {}
    for label, edges in pool_shapes(shape_cap):
        allverts = sorted(verts_of(edges), key=str)
        hubs, branches = branch_decomp(edges)
        if branches is None:
            continue
        ends = [(u, w) for (u, w, _) in branches]
        cG = len(edges) - len(allverts) + 1
        assert len(branches) == cG + len(hubs) - 1, \
            f"{label}: branch count != c + n_hub - 1"
        cols, odd = colourings(edges, cap=col_cap)
        assert not odd, f"{label}: odd alternation cycle at a tight shape"
        if cols is None:
            continue
        done = 0
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            if done >= per_shape:
                break
            done += 1
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                m, h = len(bd['E']), bd['h']
                a, M = a_and_M(bd, edges, allverts)
                # (i) the hub multigraph carries the whole cycle space
                assert h == len(fundamental_cycles(hubs, ends)), \
                    f"{label}: h(H_block) != c(G-degree)"
                # (ii) H_block is the predicted subdivision: one node per
                #      B-component, one edge per own-colour edge, and every
                #      class is a hub star or a private singleton
                bc = branch_classes(bd, branches)
                own = [len([e for e in path if col[e] == mine])
                       for (_, _, path) in branches]
                hset = set(hubs)
                other = 'B' if mine == 'A' else 'A'
                compo = components(allverts, [e for e in edges
                                              if col[e] == other])
                hubnodes = {compo[v] for v in hubs}
                # H_block IS the subdivision of G-degree / Lambda_other:
                #  * one node per hub-component plus A(beta) - 1 interior
                #    nodes per branch,
                #  * every non-hub node of H_block has degree exactly 2,
                #  * every class is a hub star or a private singleton.
                assert len(bd['nodes']) == len(hubnodes) + \
                    sum(max(0, o - 1) for o in own), \
                    f"{label}/{mine}: H_block is not the predicted subdivision"
                degn = {v: 0 for v in bd['nodes']}
                for (x, y) in bd['ced']:
                    degn[x] += 1
                    degn[y] += 1
                for v in bd['nodes']:
                    if v not in hubnodes:
                        assert degn[v] == 2, \
                            f"{label}/{mine}: interior node of degree " \
                            f"{degn[v]} in H_block"
                for k, (u, w, path) in enumerate(branches):
                    assert len(bc[k]) <= own[k]
                    for e in path:
                        if col[e] != mine:
                            continue
                        cid = dict(zip(bd['E'], bd['cls']))[e]
                        touch = [x for x in e if x in hset]
                        siz = bd['cls'].count(cid)
                        assert (touch and siz >= 1) or (not touch and
                                                        siz == 1), \
                            f"{label}/{mine}: a hubless edge in a " \
                            f"non-singleton class"
                assert sum(own) == m
                struct += 1
                # (iii) the identity
                for sv in (None,
                           {c: F(rng.randint(1, 10 ** 5),
                                 rng.randint(1, 313))
                            for c in set(bd['cls'])}):
                    z = dim_Z(bd, sval=sv)
                    w2 = dim_W_branch(bd, hubs, branches, sval=sv)
                    assert z == a + (M - 3 * h) + w2, \
                        f"{label}/{mine}: (GR-16) fails " \
                        f"({z} != {a} + {M - 3 * h} + {w2})"
                    ident += 1
                blocks += 1
                if 2 * m == 3 * (bd['n_c'] - 1):
                    bal += 1
                    assert dim_Z(bd) == dim_W_branch(bd, hubs, branches), \
                        f"{label}/{mine}: dim Z != dim W at balance"
                key = (3 * h, m)
                sizes[key] = sizes.get(key, 0) + 1
    print(f"  colouring-blocks: {blocks} ({bal} balanced); "
          f"(GR-16) identity exact {ident}/{ident}")
    print(f"  class-structure clauses asserted per block: {struct}")
    print(f"  branch system is 3c x (sum_beta |K(beta)|); the landed one is "
          f"3h x m -- distinct matrices, {len(sizes)} distinct (3h, m) shapes")
    print()


# ------------------------------------------------ [GRC-2] --runs: (GR-17) ---

def circuit_profile(branches, ends, cyc):
    return tuple(sorted(len(branches[k][2]) for k in cyc))


def leg_runs(shape_cap=None, col_cap=1 << 13, cyc_cap=120):
    """[GRC-2] (GR-17): the circuit law, its binding list, and the kill."""
    print(f"[GRC-2] (GR-17) the circuit law (seed {T_SEED + 2}); "
          f"{shape_cap or 'all'} census shapes")
    rng = random.Random(T_SEED + 2)
    n_cyc = runs_eq = runs_lt = dab_eq = free = 0
    lam_expl = 0
    binding = {}
    nec = nec_viol = 0
    for label, edges in pool_shapes(shape_cap):
        allverts = sorted(verts_of(edges), key=str)
        hubs, branches = branch_decomp(edges)
        if branches is None:
            continue
        ends = [(u, w) for (u, w, _) in branches]
        cycs = simple_cycles(list(range(len(hubs))),
                             [(hubs.index(u), hubs.index(w)) for u, w in ends])
        if len(cycs) > cyc_cap:
            continue
        # girth: every circuit of the hub multigraph has total length >= 7
        for cyc in cycs:
            assert sum(len(branches[k][2]) for k in cyc) >= 7, \
                f"{label}: a circuit of G-degree shorter than the girth bound"
        cols, odd = colourings(edges, cap=col_cap)
        if cols is None:
            continue
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            if len(EA) != len(EB):
                continue
            bdA = block_data(edges, allverts, col, 'A')
            bdB = block_data(edges, allverts, col, 'B')
            clsA = {e: c for e, c in zip(bdA['E'], bdA['cls'])}
            clsB = {e: c for e, c in zip(bdB['E'], bdB['cls'])}
            lamA = [k for k, (_, _, p) in enumerate(branches)
                    if len(p) == 1 and col[p[0]] == 'A']
            lamB = [k for k, (_, _, p) in enumerate(branches)
                    if len(p) == 1 and col[p[0]] == 'B']
            minD = 99
            for cyc in cycs:
                walk = cycle_walk(branches, ends, cyc)
                eseq = cycle_edge_seq(branches, walk)
                L, r = len(eseq), len(walk)
                cseq = [col[e] for e in eseq]
                nch = sum(1 for i in range(L) if cseq[i] != cseq[i - 1])
                nruns = nch // 2
                # h_neq: the hubs of the walk where the two cycle edges differ
                pos, hn = 0, 0
                for (k, _u, _w) in walk:
                    pos += len(branches[k][2])
                    if cseq[pos % L] != cseq[pos % L - 1]:
                        hn += 1
                assert 2 * nruns == (L - r) + hn, \
                    f"{label}: 2*runs != (L - r) + h_neq"
                DA = len({clsA[e] for e in eseq if col[e] == 'A'})
                DB = len({clsB[e] for e in eseq if col[e] == 'B'})
                n_cyc += 1
                offA = [k for k in lamA if k not in cyc]
                offB = [k for k in lamB if k not in cyc]
                if DA == DB == nruns:
                    runs_eq += 1
                else:
                    runs_lt += 1
                    assert DA <= nruns and DB <= nruns, \
                        f"{label}: more classes than runs on a circuit"
                    # the exact contrapositive of (GR-17)(ii): a shortfall on
                    # a side needs an off-circuit Lambda edge of THAT colour
                    assert (DA == nruns or offA) and (DB == nruns or offB), \
                        f"{label}: runs law fails on a side with no "\
                        f"off-circuit Lambda edge of that colour"
                    lam_expl += 1
                if DA == DB:
                    dab_eq += 1
                prof = circuit_profile(branches, ends, cyc)
                exc = sum(prof) - len(prof)          # sum_beta (ell - 1)
                if exc >= 5:
                    free += 1
                    assert nruns >= 3, \
                        f"{label}: (L - r) >= 5 but fewer than 3 runs"
                if min(DA, DB) < 3:
                    assert exc <= 4, \
                        f"{label}: NC1 fails at profile {prof} with " \
                        f"sum(ell - 1) = {exc} >= 5"
                    binding[prof] = binding.get(prof, 0) + 1
                minD = min(minD, DA, DB)
            # necessity: dim Z = 0 in a block forces every circuit >= 3
            if minD < 3:
                nec += 1
                zA = dim_Z_generic(bdA, rng, draws=2)
                zB = dim_Z_generic(bdB, rng, draws=2)
                if zA == 0 and zB == 0:
                    nec_viol += 1
    print(f"  circuits x colourings tested: {n_cyc}")
    print(f"  2*(A-runs) == (L - r) + h_neq: {n_cyc}/{n_cyc} (asserted)")
    print(f"  D_A == D_B == #runs: {runs_eq}; strictly below: {runs_lt} "
          f"(every one explained by an off-circuit Lambda merge: {lam_expl})")
    print(f"  D_A == D_B: {dab_eq}/{n_cyc}")
    print(f"  circuits with sum(ell - 1) >= 5 (>= 3 runs FORCED): {free}"
          f"/{n_cyc}")
    print(f"  circuits carrying < 3 distinct classes, by length profile:")
    for prof in sorted(binding, key=lambda p: (sum(p), p)):
        print(f"    {prof}  sum(ell) - r = {sum(prof) - len(prof)} : "
              f"{binding[prof]}")
    print(f"  blocks with a < 3 circuit and generic dim Z = 0 in BOTH "
          f"blocks: {nec_viol}/{nec} (0 = the necessity holds)")
    leg_runs_kill()


# The (2,2,3) triangle carrier, CONSTRUCTED: hub multigraph K4 on {0,1,2,3}
# with the triangle 0-1-2 at lengths (2, 2, 3) and the apex legs at
# (4, 4, 3).  Sum = 18, so c = 3 and the subdivision is tight.
KILL_SPECS = [(0, 1, 2), (1, 2, 2), (0, 2, 3), (0, 3, 4), (1, 3, 4), (2, 3, 3)]


def leg_runs_kill():
    """The adversarial witness the (GR-17) criterion must reject, plus the
    negative control (README §4 convention 6 / dispatch-log F13)."""
    edges = class_shape(KILL_SPECS)
    assert edges is not None, \
        "the constructed (2,2,3) carrier is not a class shape"
    # the carrier certified a second way: `class_shape` uses the census's
    # branch-granularity hnoRigid test, which accepts a superset; here the
    # STRICT vertex-set oracle is asserted too
    assert not rigid_vertex_sets(edges), \
        "the constructed carrier has a proper rigid subgraph"
    allverts = sorted(verts_of(edges), key=str)
    hubs, branches = branch_decomp(edges)
    ends = [(u, w) for (u, w, _) in branches]
    cycs = simple_cycles(list(range(len(hubs))),
                         [(hubs.index(u), hubs.index(w)) for u, w in ends])
    tri = [c for c in cycs if circuit_profile(branches, ends, c) == (2, 2, 3)]
    assert len(tri) == 1, "the constructed carrier lost its (2,2,3) circuit"
    rng = random.Random(T_SEED + 3)
    cols, odd = colourings(edges)
    assert not odd
    reject = accept = 0
    wit = ctl = None
    for col in cols:
        if not filter_pass(edges, allverts, col, hubs):
            continue
        walk = cycle_walk(branches, ends, tri[0])
        eseq = cycle_edge_seq(branches, walk)
        bdA = block_data(edges, allverts, col, 'A')
        bdB = block_data(edges, allverts, col, 'B')
        clsA = {e: c for e, c in zip(bdA['E'], bdA['cls'])}
        clsB = {e: c for e, c in zip(bdB['E'], bdB['cls'])}
        DA = len({clsA[e] for e in eseq if col[e] == 'A'})
        DB = len({clsB[e] for e in eseq if col[e] == 'B'})
        zA = dim_Z_generic(bdA, rng, draws=3)
        zB = dim_Z_generic(bdB, rng, draws=3)
        if min(DA, DB) < 3:
            reject += 1
            assert zA > 0 or zB > 0, "a < 3 circuit with dim Z = 0!"
            if wit is None:
                wit = (DA, DB, zA, zB)
        else:
            accept += 1
            if ctl is None and zA == 0 and zB == 0:
                ctl = (DA, DB, zA, zB)
    print(f"  CONSTRUCTED (2,2,3) carrier K4{tuple(L for _,_,L in KILL_SPECS)}"
          f": {reject} filter-passing colourings the criterion REJECTS "
          f"(witness (D_A, D_B, dim Z_+, dim Z_-) = {wit}),")
    print(f"    {accept} it accepts (negative control {ctl}); every rejected "
          f"one measured with dim Z > 0 in a block, as (GR-17) requires")
    assert reject > 0 and ctl is not None, \
        "the constructed carrier failed to exercise both sides of (GR-17)"
    print()


# ------------------------------------------------ [GRC-3] --pack: (GR-18) ---

def nash_williams_ok(hubs, ends, lens, k=6, cap=1 << 16):
    """The Tutte/Nash-Williams condition for `Ghat` (branch beta with
    multiplicity 6 - ell_beta) to have k edge-disjoint spanning trees, in
    its partition form checked over EDGE subsets: for every branch subset F,
    sum_F (6 - ell) <= 6 * r(F) with r the graphic rank of F.  Exhaustive
    when 2^|F| <= cap.  Returns (ok, exhaustive)."""
    m = len(ends)
    if (1 << m) > cap:
        return None, False
    idx = {v: i for i, v in enumerate(hubs)}
    for mask in range(1, 1 << m):
        sel = [i for i in range(m) if mask >> i & 1]
        vs = sorted({idx[ends[i][0]] for i in sel} |
                    {idx[ends[i][1]] for i in sel})
        ed = [(idx[ends[i][0]], idx[ends[i][1]]) for i in sel]
        r = len(vs) - (len(vs) - len(ed) + cycle_rank(vs, ed))
        if sum(6 - lens[i] for i in sel) > k * r:
            return False, True
    return True, True


def leg_pack(shape_cap=None, col_cap=1 << 17):
    """[GRC-3] (GR-18): Ghat packs 6 spanning trees, and (GR-10) IS a
    grouping of such a packing."""
    print(f"[GRC-3] (GR-18) the 6-spanning-tree decomposition of Ghat; "
          f"{shape_cap or 'all'} census shapes")
    nw_ok = nw_skip = 0
    certs = tri_shapes = 0
    mult_ok = 0
    for label, edges in pool_shapes(shape_cap):
        allverts = sorted(verts_of(edges), key=str)
        hubs, branches = branch_decomp(edges)
        if branches is None:
            continue
        ends = [(u, w) for (u, w, _) in branches]
        lens = [len(p) for (_, _, p) in branches]
        assert sum(6 - L for L in lens) == 6 * (len(hubs) - 1), \
            f"{label}: sum(6 - ell) != 6(n_hub - 1)"
        ok, exh = nash_williams_ok(hubs, ends, lens)
        if not exh:
            nw_skip += 1
        else:
            assert ok, f"{label}: Ghat fails Nash-Williams for 6 trees"
            nw_ok += 1
        # (GR-10) certificates ARE such packings
        cols, odd = colourings(edges, cap=col_cap)
        if cols is None:
            continue
        found = False
        for col in cols:
            if not filter_pass(edges, allverts, col, hubs):
                continue
            trees = []
            good = True
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                # `fast_triple` returns the CLASS partition (gridwit.
                # tree_triple returns the three edge lists); existence
                # agreement between the two routes is asserted here too.
                tt, capped = fast_triple(bd)
                tt2, cap2 = tree_triple(bd)
                assert capped == cap2 and (tt is None) == (tt2 is None), \
                    f"{label}: fast_triple != gridwit.tree_triple"
                if capped or tt is None:
                    good = False
                    break
                bc = branch_classes(bd, branches)
                for grp in tt:
                    gs = set(grp)
                    T = [k for k in range(len(branches))
                         if not (gs & set(bc[k]))]
                    trees.append(T)
            if not good:
                continue
            found = True
            certs += 1
            # each T is a spanning tree of the hub multigraph
            idx = {v: i for i, v in enumerate(hubs)}
            for T in trees:
                ed = [(idx[ends[k][0]], idx[ends[k][1]]) for k in T]
                assert len(ed) == len(hubs) - 1 and \
                    cycle_rank(list(range(len(hubs))), ed) == 0, \
                    f"{label}: a (GR-10) group is not a spanning tree of " \
                    f"the hub multigraph"
            # multiplicities: branch beta lies in exactly 6 - ell_beta trees
            cnt = [0] * len(branches)
            for T in trees:
                for k in T:
                    cnt[k] += 1
            for k in range(len(branches)):
                assert cnt[k] == 6 - lens[k], \
                    f"{label}: branch multiplicity {cnt[k]} != 6 - " \
                    f"{lens[k]}"
                assert sum(1 for T in trees[:3] if k in T) == \
                    3 - len([e for e in branches[k][2] if col[e] == 'A']), \
                    f"{label}: A-side multiplicity != 3 - A(beta)"
            mult_ok += 1
            break
        if found:
            tri_shapes += 1
    print(f"  Nash-Williams for 6 trees on Ghat: {nw_ok}/{nw_ok} shapes "
          f"exhaustively over branch subsets ({nw_skip} skipped, 2^m > cap)")
    print(f"  shapes at which a both-block tree-triple was located "
          f"(not a new (GR-10) measurement -- packmm --sep owns that): "
          f"{tri_shapes}; every certificate's six groups asserted to be "
          f"spanning trees of the HUB multigraph with multiplicity "
          f"6 - ell: {mult_ok}")
    print(f"  => the packing half is never the obstruction for (GR-10) "
          f"either; only the 3+3 grouping is (the (C6) analogue).")
    print()


# ------------------------------------------------- [GRC-4] --wide: the kill -

def multigraphs(n, m, cap=4000):
    """Connected loopless multigraphs, min degree >= 3, n nodes, m edges, up
    to isomorphism.  Local device: `kslidecomb.candidate_graphs` yields only
    SIMPLE graphs (it walks subsets of the vertex pairs), which is exactly
    the family gap this mode exists to close."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    seen, out = set(), []

    def rec(i, rem, mult):
        if len(out) >= cap:
            return
        if i == len(pairs):
            if rem:
                return
            deg = [0] * n
            for (u, w), mu in zip(pairs, mult):
                deg[u] += mu
                deg[w] += mu
            if min(deg) < 3:
                return
            adj = {v: set() for v in range(n)}
            for (u, w), mu in zip(pairs, mult):
                if mu:
                    adj[u].add(w)
                    adj[w].add(u)
            st, sv = [0], {0}
            while st:
                v = st.pop()
                for u in adj[v]:
                    if u not in sv:
                        sv.add(u)
                        st.append(u)
            if len(sv) != n:
                return
            best = None
            # permute only WITHIN degree classes (a degree-preserving
            # refinement of the naive n! canonicalisation; at n = 6 it is
            # what makes the enumeration affordable)
            byd = {}
            for v in range(n):
                byd.setdefault(deg[v], []).append(v)
            keys = sorted(byd)
            for combo in itertools.product(
                    *[itertools.permutations(byd[d]) for d in keys]):
                perm = [0] * n
                for d, tup in zip(keys, combo):
                    for src, dst in zip(byd[d], tup):
                        perm[src] = dst
                key = tuple(sorted(
                    (tuple(sorted((perm[u], perm[w]))), mu)
                    for (u, w), mu in zip(pairs, mult) if mu))
                if best is None or key < best:
                    best = key
            if best in seen:
                return
            seen.add(best)
            out.append([e for (e, mu) in zip(pairs, mult) for _ in range(mu)])
            return
        for mu in range(rem + 1):
            rec(i + 1, rem - mu, mult + [mu])
    rec(0, m, [])
    return out


def length_profiles(m, tgt, rng, cap):
    """Up to `cap` length profiles in [1,5]^m summing to `tgt`.

    Exhaustive (bounded recursion) when there are at most `cap` of them;
    otherwise `cap` profiles drawn by SEEDED REJECTION SAMPLING, which is
    unbiased over the solution set — a lexicographic prefix would not be
    (it is all-1-heavy, and `hcard` kills exactly those).  Never enumerated
    by `product(range(1,6), m)`: at m = 11 that is 5^11 draws."""
    out, budget = [], cap * 4
    over = [False]

    def rec(i, rem, acc):
        if len(out) > budget:
            over[0] = True
            return
        if i == m:
            if rem == 0:
                out.append(tuple(acc))
            return
        lo = max(1, rem - 5 * (m - i - 1))
        hi = min(5, rem - (m - i - 1))
        for L in range(lo, hi + 1):
            acc.append(L)
            rec(i + 1, rem - L, acc)
            acc.pop()
    rec(0, tgt, [])
    if not over[0]:
        if len(out) <= cap:
            return out
        return [out[i] for i in sorted(rng.sample(range(len(out)), cap))]
    seen, picked = set(), []
    for _ in range(cap * 400):
        if len(picked) >= cap:
            break
        p = tuple(rng.randint(1, 5) for _ in range(m))
        if sum(p) != tgt or p in seen:
            continue
        seen.add(p)
        picked.append(p)
    return picked


WIDE_PLAN = ((3, 5, 900), (3, 6, 900), (3, 7, 700), (4, 6, 600),
             (4, 7, 500), (4, 8, 300), (5, 8, 300), (5, 9, 200),
             (6, 10, 150), (6, 11, 100))


def wide_families(rng, graph_cap=60):
    """The strata `grid.census_shapes` never reaches.  Yields
    (family, label, specs)."""
    # (a) generalized thetas: n = 2, m parallel branches (the census carries
    #     only m = 3, via grid.theta_class_shapes)
    for m in range(3, 7):
        for lens in length_profiles(m, 6 * (m - 1), rng, 10 ** 6):
            if list(lens) != sorted(lens):
                continue                        # theta lengths up to order
            yield ('theta', f'theta{m}{lens}', [(0, 1, L) for L in lens])
    # (b) hub multigraphs, n = 3..6 -- every one with a parallel branch pair
    #     is outside `kslidecomb.candidate_graphs` (simple graphs only), and
    #     the simple ones at n = 5, 6 are carried by the census at only
    #     1-2 length assignments apiece
    for n, m, cap in WIDE_PLAN:
        tgt = 6 * (m - n + 1)
        gs = multigraphs(n, m)
        if len(gs) > graph_cap:
            gs = [gs[i] for i in sorted(rng.sample(range(len(gs)),
                                                   graph_cap))]
        for gi, hedges in enumerate(gs):
            if (n, m) == (4, 6) and len(set(hedges)) == len(hedges):
                continue          # the exhaustive K4 stratum IS the census
            for lens in length_profiles(m, tgt, rng, cap):
                yield (f'V{n}m{m}', f'V{n}m{m}#{gi}{lens}',
                       [(u, w, L) for (u, w), L in zip(hedges, lens)])


def leg_wide(col_cap=1 << 12):
    """[GRC-4] THE CHEAP KILL over the unswept multigraph strata."""
    print(f"[GRC-4] cheap kill on the unswept strata (seed {T_SEED + 4}); "
          f"hub MULTIgraphs and generalized thetas")
    rng = random.Random(T_SEED + 4)
    fam = {}
    tot = hits = 0
    misses = []
    hist = {}
    for family, label, specs in wide_families(rng):
        edges = class_shape(specs)
        if edges is None:
            continue
        allverts = sorted(verts_of(edges), key=str)
        hubs, branches = branch_decomp(edges)
        if branches is None:
            continue
        cols, odd = colourings(edges, cap=col_cap)
        assert not odd, f"{label}: odd alternation cycle"
        if cols is None:
            continue
        tot += 1
        fam[family] = fam.get(family, 0) + 1
        hit_at = None
        probed = 0
        for col in cols:
            if not filter_pass(edges, allverts, col, hubs):
                continue
            probed += 1
            bdA = block_data(edges, allverts, col, 'A')
            bdB = block_data(edges, allverts, col, 'B')
            svA = block_generic_zero(bdA, hubs, branches, rng)
            if svA is None:
                continue
            svB = block_generic_zero(bdB, hubs, branches, rng)
            if svB is None:
                continue
            # exact-ℚ recheck of the attaining sample (README §4 conv. 2)
            assert dim_W_branch(bdA, hubs, branches, sval=svA) == 0
            assert dim_W_branch(bdB, hubs, branches, sval=svB) == 0
            assert dim_Z(bdA, sval=svA) == 0 and dim_Z(bdB, sval=svB) == 0, \
                f"{label}: branch model and grid.dim_Z disagree at the hit"
            hit_at = probed
            break
        if hit_at is None:
            misses.append((label, probed, specs))
        else:
            hits += 1
            hist[hit_at] = hist.get(hit_at, 0) + 1
    print(f"  class shapes swept: {tot} " +
          ", ".join(f"{k}:{v}" for k, v in sorted(fam.items())))
    print(f"  shapes with an admissible colouring at generic "
          f"dim Z_+ = dim Z_- = 0: {hits}/{tot}")
    top = sorted(hist)[:6]
    print(f"  first-hit histogram (filter-passing colourings tried): " +
          ", ".join(f"{k}:{hist[k]}" for k in top) +
          (" ..." if len(hist) > 6 else ""))
    if misses:
        print(f"  *** (GR-15) MISS at {len(misses)} shapes ***")
        for label, probed, specs in misses[:10]:
            print(f"    MISS {label} (filter-passing colourings: {probed})")
            print(f"      specs = {specs}")
    else:
        print("  NO miss: the cheap kill did not fire on any unswept "
              "stratum.")
    print()


# ------------------------------------------------ [GRC-5] --hier: (GR-19) ---

def collapse_search(bd, r, rng, draws=3, budget=90.0, want=1):
    """Search r-group COLLAPSE certificates of `dim Z = 0` for one block.

    A collapse assigns one value `a_j` to every class of group `F_j`; by
    (GR-7) remark (i) the resulting `dim W` bounds the generic one from
    above, so `dim W_collapse = 0` PROVES generic `dim Z = 0`.  At `r = 3`
    this family is exactly (GR-9)'s tree-triple.  The counting filter is
    exact: `dim W_collapse >= sum_j comp(H_block minus F_j) - r`, so a
    certificate needs every one of the r complements CONNECTED, which is
    checked first."""
    m, nodes = len(bd['E']), bd['nodes']
    cids = sorted(set(bd['cls']))
    t0 = __import__('time').time()
    res = {'tried': 0, 'coind': 0, 'cert': 0, 'first': None,
           'timeout': False}
    assign = [0] * len(cids)
    pos = {c: i for i, c in enumerate(cids)}

    def conn_without(grp):
        rem = [bd['ced'][k] for k in range(m) if bd['cls'][k] not in grp]
        return comp_count_nodes(nodes, rem) == 1

    def rec(i, used):
        if res['cert'] >= want:
            return
        if __import__('time').time() - t0 > budget:
            res['timeout'] = True
            return
        if i == len(cids):
            res['tried'] += 1
            grps = [set(c for c in cids if assign[pos[c]] == g)
                    for g in range(r)]
            if any(not g for g in grps) or \
                    not all(conn_without(g) for g in grps):
                return
            res['coind'] += 1
            for _ in range(draws):
                vals = []
                while len(set(vals)) < r:
                    vals = [F(rng.randint(1, 10 ** 4)) for _ in range(r)]
                sv = {c: vals[assign[pos[c]]] for c in cids}
                if dim_W(bd, sval=sv) != 0:
                    return
            res['cert'] += 1
            if res['first'] is None:
                res['first'] = [sorted(g) for g in grps]
            return
        for g in range(min(used + 1, r)):
            assign[i] = g
            rec(i + 1, max(used, g + 1))
    rec(0, 0)
    return res


SEP_SHAPES = ('V6m10(3, 3, 3, 3, 3, 3, 3, 3, 3, 3)',
              'V6m11(3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4)')


def leg_hier():
    """[GRC-5] (GR-19): the r-group collapse hierarchy, and collapse order 4
    on the 18 habitat separators of *Step G16*."""
    print(f"[GRC-5] (GR-19) the collapse hierarchy (seed {T_SEED + 5})")
    rng = random.Random(T_SEED + 5)
    bd = synth_bd(EXEMPLAR['nodes'], EXEMPLAR['ced'], EXEMPLAR['cls'])
    r3 = collapse_search(bd, 3, rng)
    r4 = collapse_search(bd, 4, rng)
    assert not r3['timeout'] and r3['coind'] == 0 and r3['cert'] == 0, \
        "the pinned exemplar acquired a tree-triple"
    assert r4['cert'] >= 1, "no 4-group collapse at the pinned exemplar"
    print(f"  pinned exemplar ({EXEMPLAR['label']}): r = 3 exhausted over "
          f"{r3['tried']} canonical partitions, {r3['coind']} with all three "
          f"complements connected -- NO tree-triple (Step G16, re-derived)")
    print(f"  r = 4: {r4['coind']} of {r4['tried']} canonical partitions are "
          f"co-independent; the first CERTIFIES dim Z = 0: {r4['first']}")
    # value-independence: the exhibited 4-partition at EVERY distinct
    # integer 4-tuple from {1..7} (840 of them)
    cids = sorted(set(bd['cls']))
    g_of = {c: j for j, g in enumerate(r4['first']) for c in g}
    bad = 0
    for vals in itertools.permutations(range(1, 8), 4):
        sv = {c: F(vals[g_of[c]]) for c in cids}
        if dim_W(bd, sval=sv) != 0:
            bad += 1
    print(f"  value-independence of that certificate: {bad} failures over "
          f"all 840 distinct integer 4-tuples from {{1..7}} -- so it is a "
          f"COMBINATORIAL certificate, not one value point")
    assert bad == 0
    # monotonicity: refining a certifying partition still certifies
    ref = [r4['first'][0], r4['first'][1], r4['first'][2][:1],
           r4['first'][2][1:], r4['first'][3]]
    g5 = {c: j for j, g in enumerate(ref) for c in g}
    vals5 = [F(v) for v in (2, 3, 5, 7, 11)]
    assert dim_W(bd, sval={c: vals5[g5[c]] for c in cids}) == 0, \
        "the collapse hierarchy is not monotone in r"
    print("  monotone in r (a refinement of a certifying partition still "
          "certifies): asserted")
    # all 18 separators
    seps = []
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
                seps.append((label, b))
    ok = 0
    for label, b in seps:
        r = collapse_search(b, 4, rng, budget=60.0)
        if r['cert']:
            ok += 1
        else:
            print(f"    NO r = 4 certificate at {label} "
                  f"(tried {r['tried']}, co-independent {r['coind']}, "
                  f"timeout {r['timeout']})")
    print(f"  separators re-found on the two carrier shapes: {len(seps)} "
          f"(Step G16's 18); r = 4 collapse certifies {ok}/{len(seps)}")
    assert len(seps) == 18 and ok == 18
    print("  => COLLAPSE ORDER 4 suffices at every dim Z = 0 block of the")
    print("     census pool: Step G16 classifies the 1720 triple-less blocks")
    print("     as 1702 counting-visible (dim Z > 0) + these 18, and the")
    print("     other 16600 filter-passing blocks carry tree-triples")
    print("     (order 3).  The certificate theory is NOT stuck where the")
    print("     triple is.")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('branch', 'runs', 'pack', 'hier', 'wide',
              'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.branch, a.runs, a.pack, a.hier,
                                 a.wide])
    if run or a.branch:
        leg_branch()
    if run or a.runs:
        leg_runs()
    if run or a.pack:
        leg_pack()
    if run or a.hier:
        leg_hier()
    if run or a.wide:
        leg_wide()
    print("OK")


if __name__ == '__main__':
    main()
