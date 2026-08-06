"""§(K-grid) driver — the (AC-6) tight-stratum residual, attacked directly.

A `w4/` leaf beside `closure.py`, importing it read-only (README §2: a new
(K)-arc driver goes BESIDE the fan-out leaves).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --mech     # (GR-2) the refutation of the literal (AC-4)(i)-(ii) statement
    PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --spline   # (GR-1) the direction-network/spline reduction, rank identity
    PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --counts   # (GR-3)/(GR-4) the class-union counts vs dim Z
    PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --census   # THE CHEAP KILL: the kslidecomb class pool
    PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --chart    # (GR-5) chart-image membership, verified end to end
    PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --validate # all five

Argument state: `notes/Pencil-informal.md` §(K-grid) (new with this driver;
labels reserved for the 2026-08-06 T/R/M fan-out, `notes/Pencil-labels.md`).

WHAT IS NEW HERE, in one paragraph.  §(K-clos) *Step Z4* left the residual
system of a σ-fixed grid configuration as a "direction network in K³" and did
not attempt its combinatorics.  This driver carries the reduction the section
stopped short of: at a legal colouring the ±-eigen-block rank satisfies

    rank_block = 3·|E_other| + (3·n_c − 3 − dim Z_block),

where n_c = #components of the other ruling class and Z_block is the
OBSTRUCTION SPACE  Z = {c ∈ K^{E_mine} : c, s·c, s²·c ∈ cut(G/E_other)}
(s = the per-ruling-class parameter, one value per class, entrywise product).
Equivalently (the univariate-spline reading): assign each body the quadratic
q_v(t) whose coefficient vector is its block unknown; an edge of class X
demands q_u − q_w ∝ (t − s_X)²; Z is the space of jump assignments realized
by a global spline, mod constants.  Target rank at a tight balanced colouring
⟺ Z₊ = Z₋ = 0.  Both blocks' Z is computed exactly here (3h × m rational
matrix, h = cycle rank of the contracted graph) and the identity is asserted
against the independently-built eigen-block ranks of `closure.py`.

LOCAL VARIANT, deliberately different from a §1 primitive (README rule 3):
`build_fixed_config_params` is `closure.build_fixed_config` with the ruling
parameters as ARGUMENTS instead of the component indices — needed to retest a
rank miss at several parameter draws before calling it structural (a miss at
one parameter point is not a miss of the recipe).  `closure.py` is not
touched; a *Divergences*-table row is flagged in the landing notes.

Exact throughout (ℚ via fractions.Fraction, ℚ(i) via closure.Gauss).  The one
rng (census length draws, mirroring `kslidecomb.driver_sweep`) is seeded and
the seed printed.  No `set` is printed.  σ-fixed configurations are
CONSTRUCTED existence witnesses, never sampled rates — per (AC-9) they are
never composite-guard generic, and nothing here is quoted as a rate, so the
`repin.star_generic` gating rule (README *Harness debt*, CLOSED) does not
bind any figure below; the guard's verdict is still reported by every probe.
"""
import argparse
import itertools
import random
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, nullspace, rank, wedge2                  # noqa: E402
from kbare_common import verts_of                                   # noqa: E402
from pitch import theta_edges                                       # noqa: E402
from hybrid_gates import build_rigidity_extensors                   # noqa: E402
from nogood_subdiv import (deficiency, hcard_ok, hub_set,           # noqa: E402
                           rigid_vertex_sets, triangles)
from kslidecomb import (candidate_graphs, relabel, shape_data,      # noqa: E402
                        shape_ok)
import closure  # noqa: E402  -- the §(K-clos) leaf, imported read-only
from closure import (EIG_M, EIG_P, Gauss, alternation_classes,      # noqa: E402
                     colourings, combinatorial_filter, components,
                     conic_coords, cycle_rank, dsk4, extensors,
                     grid_point, probe, star_sign)

TRIES_SEED = 20260806


# ---------------------------------------------------------- small helpers --

def neighbors_of(edges):
    nb = {}
    for u, w in edges:
        nb.setdefault(u, []).append(w)
        nb.setdefault(w, []).append(u)
    return nb


def comp_count(allverts, edges):
    return len(set(components(allverts, edges).values()))


def proportional(a, b):
    """a ∝ b as nonzero vectors (cross-multiplication, exact)."""
    assert any(x != 0 for x in a) and any(x != 0 for x in b)
    j = next(k for k in range(len(a)) if a[k] != 0)
    if b[j] == 0:
        return False
    return all(a[k] * b[j] == b[k] * a[j] for k in range(len(a)))


# ------------------------------------------- the class / contraction data --

def block_data(edges, allverts, col, mine):
    """The contracted direction-network combinatorics of one eigen-block.

    mine = 'A' (the + block: E_A edges constrain, E_B contracts) or 'B'.
    Returns dict with: m (edges of my colour), their class ids (= components
    of my ruling class — every edge of one class carries the SAME hinge line
    and hence the same parameter), the per-class parameter s_X exactly as
    `closure.build_fixed_config` assigns it (component index + 1), the
    contracted endpoints (components of the OTHER class), n_c, and h (cycle
    rank of the contracted multigraph)."""
    E_mine = [e for e in edges if col[e] == mine]
    E_other = [e for e in edges if col[e] != mine]
    comp_mine = components(allverts, E_mine)
    comp_other = components(allverts, E_other)
    cls = [comp_mine[e[0]] for e in E_mine]
    for e, cid in zip(E_mine, cls):
        assert comp_mine[e[1]] == cid
    sval = {cid: F(cid + 1) for cid in set(cls)}
    ced = [(comp_other[u], comp_other[w]) for (u, w) in E_mine]
    nodes = sorted(set(comp_other.values()))
    h = len(E_mine) - len(nodes) + comp_count_nodes(nodes, ced)
    return dict(E=E_mine, cls=cls, s=sval, ced=ced, nodes=nodes, h=h,
                n_other=len(E_other), n_c=len(nodes))


def comp_count_nodes(nodes, ced):
    par = {v: v for v in nodes}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for u, w in ced:
        ru, rw = find(u), find(w)
        if ru != rw:
            par[ru] = rw
    return len({find(v) for v in nodes})


def fundamental_cycles(nodes, ced):
    """Signed fundamental-cycle vectors of the contracted multigraph, over
    the edge index.  A loop edge contributes the singleton cycle {e: +1}."""
    par = {v: v for v in nodes}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    adj = {v: [] for v in nodes}           # tree adjacency: (nbr, edge, sgn)
    tree = set()
    for k, (u, w) in enumerate(ced):
        if u == w:
            continue
        ru, rw = find(u), find(w)
        if ru != rw:
            par[ru] = rw
            tree.add(k)
            adj[u].append((w, k, +1))
            adj[w].append((u, k, -1))
    out = []
    for k, (u, w) in enumerate(ced):
        if k in tree:
            continue
        if u == w:                          # loop
            out.append({k: 1})
            continue
        # path w -> u in the tree (BFS), then close with edge k (u -> w)
        prev = {w: None}
        queue = [w]
        while queue:
            x = queue.pop(0)
            if x == u:
                break
            for (y, ek, sg) in adj[x]:
                if y not in prev:
                    prev[y] = (x, ek, sg)
                    queue.append(y)
        z = {k: 1}
        x = u
        while prev[x] is not None:
            (px, ek, sg) = prev[x]
            # tree edge ek traversed from px to x carries +sg; we walk u -> w
            # backwards along prev, i.e. from x back to px, so flip.
            z[ek] = z.get(ek, 0) + sg
            x = px
        out.append(z)
    return out


def dim_Z(bd, sval=None):
    """dim Z = dim {c : c, s·c, s²·c all ⊥ every cycle}, exactly.

    Rows: one per (fundamental cycle, power j ∈ {0,1,2}); entry at edge e is
    z_e · s_{cls(e)}^j.  Pure ℚ.  This is the 3h × m matrix whose kernel is
    the obstruction space; rank identity asserted elsewhere.  `sval`
    overrides the per-class parameters (default: the component-index labels
    `closure.build_fixed_config` uses — which are NOT generic; see
    `dim_Z_generic`)."""
    m = len(bd['E'])
    s = bd['s'] if sval is None else sval
    rows = []
    for z in fundamental_cycles(bd['nodes'], bd['ced']):
        for j in range(3):
            rows.append([F(z.get(k, 0)) * s[bd['cls'][k]] ** j
                         for k in range(m)])
    return m - (rank(rows) if rows else 0)


def dim_Z_generic(bd, rng, draws=3):
    """dim Z at generic labels: the minimum over `draws` seeded random
    rational parameter draws (dim Z is upper-semicontinuous in the labels,
    so the generic value is the min, attained at almost every draw).  The
    component-index labels of the concrete construction OVERSHOOT this at
    ~1.5 % of pool instances ([GR-D3]) — a special-value artifact, not a
    property of the recipe."""
    return min(dim_Z(bd, sval={c: F(rng.randint(1, 10 ** 5),
                                    rng.randint(1, 313))
                               for c in set(bd['cls'])})
               for _ in range(draws))


def class_union_bounds(edges, allverts, bd, subset_cap=18):
    """(GR-3): proven lower bounds for dim Z from class-union counts.

    bound_cls = Σ_X (|X| − dim H_X)      (a cut vector inside one class;
                dim H_X = |X| − comp(G∖X) + 1, supports disjoint so they sum)
    bound_cnt = max over unions F of classes of  Σ_{X⊆F}|X| − 3·dim H_F,
                dim H_F = |F| − comp(G∖F) + 1  (the count
                3(comp(G∖F) − 1) ≤ 2|F| in its deficiency form)
    Exhaustive over 2^L class subsets when L ≤ subset_cap, else singletons +
    pairs + the full set only (flagged 'partial').  comp(G∖F) is computed on
    the FULL graph G minus the class edges (the other ruling class intact).
    """
    m = len(bd['E'])
    by_cls = {}
    for k in range(m):
        by_cls.setdefault(bd['cls'][k], []).append(bd['E'][k])
    cids = sorted(by_cls)
    eset = list(edges)

    def dimH(cs):
        Fe = {e for c in cs for e in by_cls[c]}
        rest = [e for e in eset if e not in Fe]
        return len(Fe) - (comp_count(allverts, rest) - 1), len(Fe)

    bound_cls = 0
    for c in cids:
        dh, sz = dimH([c])
        bound_cls += sz - dh
    L = len(cids)
    partial = L > subset_cap
    if partial:
        subsets = [[c] for c in cids] + [list(p) for p in
                                         itertools.combinations(cids, 2)]
        subsets.append(list(cids))
    else:
        subsets = [list(s) for r in range(1, L + 1)
                   for s in itertools.combinations(cids, r)]
    bound_cnt = 0
    for cs in subsets:
        dh, sz = dimH(cs)
        bound_cnt = max(bound_cnt, sz - 3 * dh)
    return bound_cls, bound_cnt, partial


# --------------------------------- parameterized σ-fixed config (variant) --

def dn_sparsity_bound(bd, node_cap=16):
    """(GR-3) second proven family: contracted-multigraph overbracing.

    For any node subset S of the contracted graph, the rows of the edges
    induced inside S span ≤ 3|S| − 3·comp(S) dimensions (constants per
    induced component), and the rows outside span ≤ 2·(m − e_in).  Hence
    dim Z ≥ (3·n_c − 3) − [2(m − e_in) + 3|S| − 3 comp(S)] for every S — the
    class-blind direction-network (2,3)-count, which the class-union counts
    do NOT subsume (witness: two contracted edges of different classes on
    one node pair — a 'mixed digon' — has e_in = 2, |S| = 2, comp = 1).
    Exhaustive over 2^{n_c} node subsets when n_c ≤ node_cap, else pairs and
    triples only (flagged 'partial')."""
    m = len(bd['E'])
    nodes = bd['nodes']
    partial = len(nodes) > node_cap
    if partial:
        subs = [list(p) for p in itertools.combinations(nodes, 2)]
        subs += [list(p) for p in itertools.combinations(nodes, 3)]
    else:
        subs = [list(s) for r in range(2, len(nodes) + 1)
                for s in itertools.combinations(nodes, r)]
    best = 0
    base = 3 * bd['n_c'] - 3 - 2 * m
    for S in subs:
        sset = set(S)
        ein = [(u, w) for (u, w) in bd['ced'] if u in sset and w in sset]
        if not ein:
            continue
        cc = comp_count_nodes(S, ein)
        best = max(best, base + 2 * len(ein) - 3 * len(S) + 3 * cc)
    return best, partial


def build_fixed_config_params(edges, allverts, col, pA, pB):
    """`closure.build_fixed_config` with the ruling parameters supplied.

    pA / pB map ruling-component ids to Fractions.  Distinctness of bodies is
    still checked (None on a coincidence).  DIVERGENCE (README rule 3): same
    job as `closure.build_fixed_config`, different signature — needed to
    retest a rank miss away from the component-index parameter point."""
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    compA = components(allverts, EA)
    compB = components(allverts, EB)
    if len({(pA[compA[v]], pB[compB[v]]) for v in allverts}) != len(allverts):
        return None
    pt = {v: grid_point((1, pA[compA[v]]), (1, pB[compB[v]]))
          for v in allverts}
    return pt, EA, EB


def rank_at_params(edges, allverts, col, rng):
    """Both eigen-block ranks at a random (seeded) parameter draw, or None
    if the draw (or the colouring itself) forces coincident bodies."""
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    compA = components(allverts, EA)
    compB = components(allverts, EB)
    pA = {c: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
          for c in set(compA.values())}
    pB = {c: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
          for c in set(compB.values())}
    built = build_fixed_config_params(edges, allverts, col, pA, pB)
    if built is None:
        return None
    pt, _, _ = built
    for v in allverts:
        assert dot(pt[v], pt[v]) == 0
    for (u, w) in edges:
        assert dot(pt[u], pt[w]) == 0
    ext = extensors(edges, pt)
    rP, _ = closure.eigen_subsystem_contracted(allverts, edges, col, ext, 'P')
    rM, _ = closure.eigen_subsystem_contracted(allverts, edges, col, ext, 'M')
    return rP + rM


# ------------------------------------------------------------------- legs --

def theta_class_shapes():
    """The three tight+hnoRigid theta class shapes (ℓ ≤ 5 forced by (R3):
    every proper cycle ℓ_i + ℓ_j must exceed 6).  θ(2,5,5) is NOT in
    closure.py's pinned pool — it joins the census here."""
    out = []
    for lens in ((2, 5, 5), (3, 4, 5), (4, 4, 4)):
        edges = theta_edges(list(lens))
        allverts = verts_of(edges)
        assert 5 * len(edges) == 6 * (len(allverts) - 1)
        assert deficiency(edges) == 0
        assert not rigid_vertex_sets(edges)
        assert hcard_ok(edges)
        hubs = hub_set(edges)
        assert not any(len(t & hubs) >= 2 for t in triangles(edges))
        out.append((f'theta{lens}', edges))
    return out


def leg_mech():
    """GR-D1 — the literal '(AC-4)(i)–(ii) ⟹ isostatic' is FALSE, and the
    mechanism is a bond of the contracted graph inside ONE ruling class (at
    ds-K4: a monochromatic hub, whose body is a free rotor about its single
    hinge line — the rank-costing case of (AC-9)'s coincidences)."""
    print("[GR-D1] the (AC-4)(i)-(ii) literal statement, refuted at ds-K4")
    name, edges = dsk4()
    allverts = sorted(verts_of(edges))
    target = 6 * (len(allverts) - 1)
    cols, _ = colourings(edges)
    nb = neighbors_of(edges)
    n_bal_forest = n_below = n_mono = n_filter_target = 0
    for col in cols:
        EA = [e for e in edges if col[e] == 'A']
        EB = [e for e in edges if col[e] == 'B']
        if len(EA) != len(EB):
            continue
        if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
            continue
        n_bal_forest += 1
        d = probe(name, edges, col, fast=True)
        assert d is not None
        mono = [v for v, ns in nb.items() if len(ns) >= 3
                and len({col[e] for e in edges if v in e}) == 1]
        if d['rk'] < target:
            n_below += 1
            assert mono, "a balanced both-forest miss WITHOUT a mono hub"
            n_mono += 1
            v = mono[0]
            # the free rotor, exhibited: all hinges at v are ONE ruling line
            pt, _, _ = closure.build_fixed_config(edges, allverts, col)
            ext = dict(extensors(edges, pt))
            star = [tuple(C) for e, C in ext.items() if v in e]
            assert all(proportional(list(C), list(star[0])) for C in star), \
                "mono hub's hinges are not a single projective line"
            # ... and the star cut of v is a bond inside ONE class:
            which = col[[e for e in edges if v in e][0]]
            bd = block_data(edges, allverts, col, which)
            starcls = {bd['cls'][k] for k in range(len(bd['E']))
                       if v in bd['E'][k]}
            assert len(starcls) == 1, "the star is not one class"
            assert dim_Z(bd) >= 1
        else:
            if combinatorial_filter(edges, allverts, col) is None:
                n_filter_target += 1
    print(f"  balanced AND both-forest colourings          : {n_bal_forest}")
    print(f"  ... of which BELOW the Tay target            : {n_below}")
    print(f"  ... every one carrying a monochromatic hub   : {n_mono}")
    print(f"  ... filter-passing (adds: no mono hub) at tgt: {n_filter_target}")
    assert (n_bal_forest, n_below, n_mono) == (20, 8, 8)
    assert n_filter_target == 12
    print("  ⟹ (AC-4)(i)+(ii) do NOT imply isostatic blocks: the pinned")
    print("    --sweep's 8 rank-89 rows are balanced with both classes")
    print("    forests.  Each miss is a BOND OF THE CONTRACTED GRAPH INSIDE")
    print("    ONE RULING CLASS (here: a mono hub = free rotor about its")
    print("    single hinge line).  The corrected hypothesis needs (iii'):")
    print("    no class union violates the count 3(comp(G-F)-1) <= 2|F|,")
    print("    of which the mono hub is the F = one-star-class case.")
    print()


def spline_pool():
    pool = [dsk4(), ('ds-(K5-M)',
                     closure.double_subdivide(closure.K5_minus_matching())[0])]
    pool += theta_class_shapes()
    return pool


def leg_spline():
    """GR-D2 — the reduction identity: for every legal both-forest colouring
    of the pool, and both blocks,  rank_block = 3|E_other| + 3n_c − 3 − dim Z
    with dim Z computed from the 3h × m cycle/parameter matrix — a genuinely
    independent computation from closure's eigen-block rref."""
    print("[GR-D2] the direction-network/spline reduction, rank identity")
    checked = eq = 0
    for name, edges in spline_pool():
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges)
        assert not odd
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            built = closure.build_fixed_config(edges, allverts, col)
            if built is None:
                continue
            pt, _, _ = built
            ext = extensors(edges, pt)
            for which, mine in (('P', 'A'), ('M', 'B')):
                bd = block_data(edges, allverts, col, mine)
                assert comp_count(allverts, edges) == 1
                rk, _ = closure.eigen_subsystem_contracted(
                    allverts, edges, col, ext, which)
                z = dim_Z(bd)
                pred = 3 * bd['n_other'] + 3 * bd['n_c'] - 3 - z
                assert rk == pred, \
                    f"{name}: rank identity fails ({rk} != {pred})"
                checked += 1
                eq += 1
    print(f"  colouring-blocks checked, identity exact: {eq}/{checked}")
    print("  (rank from closure's eigen-block rref over ℚ(i); dim Z from the")
    print("   3h × m rational cycle/parameter matrix — independent routes)")
    print()


def leg_counts():
    """GR-D3 — dim Z vs the proven class-union lower bounds, and the
    equality conjecture (GR-4).  Every instance must satisfy
    dim Z ≥ max(bounds) (proven); the conjecture is equality."""
    print("[GR-D3] class-union + sparsity counts vs dim Z ((GR-4))")
    rng = random.Random(TRIES_SEED + 3)
    inst = agree_g = 0
    overshoot = 0
    filt = filt_zero = 0
    gaps = {}
    for name, edges in spline_pool():
        allverts = sorted(verts_of(edges), key=str)
        cols, _ = colourings(edges)
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            fpass = combinatorial_filter(edges, allverts, col) is None
            if fpass:
                filt += 1
            zboth = 0
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                z0 = dim_Z(bd)
                zg = dim_Z_generic(bd, rng)
                zboth += zg
                b_cls, b_cnt, part1 = class_union_bounds(edges, allverts,
                                                         bd)
                b_dn, part2 = dn_sparsity_bound(bd)
                lo = max(b_cls, b_cnt, b_dn, 0)
                assert zg >= lo, f"{name}: proven bound exceeds generic dimZ"
                assert z0 >= zg, f"{name}: construction labels BELOW generic"
                inst += 1
                if z0 > zg:
                    overshoot += 1
                if zg == lo and not (part1 or part2):
                    agree_g += 1
                elif zg > lo:
                    key = (name, zg - lo)
                    gaps[key] = gaps.get(key, 0) + 1
            if fpass and zboth == 0:
                filt_zero += 1
    print(f"  instances (colouring-blocks): {inst}")
    print(f"  generic dim Z == max(class-union, DN-sparsity) : {agree_g}")
    print(f"  construction (component-index) labels overshoot: {overshoot}")
    print(f"  filter-passing legal colourings: {filt}; with generic "
          f"dim Z = 0 in BOTH blocks: {filt_zero}")
    if gaps:
        print("  UNEXPLAINED instances (shape, gap): count")
        for (nm, g), c in sorted(gaps.items()):
            print(f"    {nm}  gap {g}: {c}")
        print("  a gap here is a THIRD obstruction family beyond (GR-3)'s")
        print("  two proven ones -- workbook §(K-grid) (GR-4) is the owner.")
    else:
        print("  the two proven bound families are EXACT at generic labels")
        print("  on this pool ((GR-4)): no third obstruction mechanism.  The")
        print("  overshoot rows are a special-value artifact of the")
        print("  component-index parameters, not a property of the recipe.")
    print()


def census_shapes():
    """The kslidecomb class-shape pool: exhaustive K4 stratum, |V°| ≤ 5
    sweep (all-{3,4} + seeded draws), |V°| = 6 seeded draws, and the three
    tight thetas.  Yields (label, edges)."""
    for name, edges in theta_class_shapes():
        yield name, edges
    K4E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
        if sum(lens) != 18 or 3 not in lens:
            continue
        specs = relabel(4, K4E, lens, lens.index(3))
        if shape_ok(specs) is None:
            continue
        yield f'K4{lens}', shape_data(specs)[0]
    for nmax, keep, tries in ((5, 2, 400), (6, 1, 600)):
        graphs = 0
        for n, hedges in candidate_graphs(nmax):
            if nmax == 6 and n < 6:
                continue
            m = len(hedges)
            target = 6 * (m - n + 1)
            if not (m <= target <= 5 * m):
                continue
            graphs += 1
            if nmax == 6 and graphs > 40:
                break
            rng = random.Random(TRIES_SEED + 7 * m + n)
            cands = [lens for lens in itertools.product((3, 4), repeat=m)
                     if sum(lens) == target]
            for _ in range(tries):
                lens = tuple(rng.randint(1, 5) for _ in range(m))
                if sum(lens) == target:
                    cands.append(lens)
            kept = 0
            seen = set()
            for lens in cands:
                if 3 not in lens or lens in seen:
                    continue
                seen.add(lens)
                specs = relabel(n, hedges, lens, lens.index(3))
                if shape_ok(specs) is None:
                    continue
                yield f'V{n}m{m}{lens}', shape_data(specs)[0]
                kept += 1
                if kept >= keep:
                    break


def leg_census(cap_probe=48, col_cap=1 << 16, retries=3):
    """GR-D4 — THE CHEAP KILL: hunt a tight class shape where the grid
    recipe misses the Tay target.  ∃-question with early exit; every miss is
    retried at `retries` seeded random parameter draws before being called
    structural, and every structural miss is attributed (dim Z per block +
    the class-union bounds)."""
    print(f"[GR-D4] census over the kslidecomb class pool "
          f"(seed {TRIES_SEED}, probe cap {cap_probe}/shape)")
    print("  every shape below is tight (5|E| = 6(|V|−1), def = 0) and")
    print("  hnoRigid-certified (shape_ok / rigid_vertex_sets); feasibility-")
    print("  necessary conditions asserted per shape.")
    tot = hits = 0
    groups = {}
    miss_rows = []
    hit_at_hist = {}
    for label, edges in census_shapes():
        grp = ('theta' if label.startswith('theta') else
               'K4-stratum' if label.startswith('K4') else
               'V5-sweep' if label.startswith('V5') else 'V6-sweep')
        groups[grp] = groups.get(grp, 0) + 1
        allverts = sorted(verts_of(edges), key=str)
        hubs = hub_set(edges)
        assert hcard_ok(edges)
        assert not any(len(t & hubs) >= 2 for t in triangles(edges))
        target = 6 * (len(allverts) - 1)
        assert deficiency(edges) == 0
        cols, odd = colourings(edges, cap=col_cap)
        assert not odd, f"{label}: a tight shape with an odd alternation " \
            "cycle (impossible: tight shapes have hubs)"
        assert cols is not None, f"{label}: colouring cap hit"
        tot += 1
        probed = 0
        hit_at = None
        fails = []
        for k, col in enumerate(cols):
            if combinatorial_filter(edges, allverts, col):
                continue
            if probed >= cap_probe:
                break
            probed += 1
            d = probe(label, edges, col, fast=True)
            if d is None:
                fails.append((k, 'coincident bodies', None, col))
                continue
            if d['rk'] == target and d['ok']:
                hit_at = probed
                break
            fails.append((k, 'rank gap' if d['ok'] else f"nondeg {d['why']}",
                          target - d['rk'], col))
        if hit_at is not None:
            hits += 1
            hit_at_hist[hit_at] = hit_at_hist.get(hit_at, 0) + 1
            continue
        # a miss: retry every rank-gap colouring at random parameter draws
        structural = True
        rng = random.Random(TRIES_SEED * 31 + len(allverts))
        for (k, why, gap, col) in fails:
            if not why.startswith('rank') and not why.startswith('nondeg'):
                continue
            for _ in range(retries):
                r = rank_at_params(edges, allverts, col, rng)
                if r == target:
                    structural = False
                    break
            if not structural:
                break
        miss_rows.append((label, edges, probed, structural, fails))
    print(f"  shapes censused : {tot}")
    for grp in sorted(groups):
        print(f"    {grp:12s}: {groups[grp]}")
    print(f"  recipe reaches the Tay target at : {hits}/{tot}")
    hist = ', '.join(f"{k}:{v}" for k, v in sorted(hit_at_hist.items()))
    print(f"  first-hit index histogram (probed colouring #): {hist}")
    for (label, medges, probed, structural, fails) in miss_rows:
        mverts = sorted(verts_of(medges), key=str)
        print(f"  MISS {label}  |V|={len(mverts)} |E|={len(medges)} "
              f"probed={probed} structural={structural}")
        for (k, why, gap, col) in fails[:6]:
            print(f"      colouring {k}: {why}"
                  + (f" gap {gap}" if gap else ""))
        # attribution of the first rank-gap colouring, both blocks
        for (k, why, gap, col) in fails:
            if why.startswith('rank'):
                for mine in ('A', 'B'):
                    bd = block_data(medges, mverts, col, mine)
                    z = dim_Z(bd)
                    b_cls, b_cnt, partial = class_union_bounds(
                        medges, mverts, bd)
                    print(f"      block {mine}: dim Z = {z}, class bound "
                          f"{b_cls}, count bound {b_cnt}"
                          f"{' (partial)' if partial else ''}")
                break
    assert not miss_rows, "the census FOUND a tight-stratum miss -- " \
        "the (AC-6) tight-stratum residual has a counterexample; " \
        "update §(K-grid) and the State of (K) map"
    print("  NO tight class shape misses: the recipe reached the target at")
    print("  every censused shape (existence per shape; the ∀-colouring")
    print("  question is [GR-D2]/[GR-D3]'s pool).")
    print()


def closed_hub_nbhd(edges, nb, v):
    """Graph.closedHubNbhd (Motive.lean:82): pencil hubs among v and its
    neighbours (hub = degree ≥ 3)."""
    out = [w for w in sorted({v, *nb[v]}, key=str) if len(nb[w]) >= 3]
    return out


def cross4(x, y, z):
    """cross₃ per Chart.lean:84 / Engine.lean cross₃_apply: coordinate i is
    det of the 4×4 matrix with ROWS x, y, z, e_i."""
    out = []
    for i in range(4):
        ei = [Gauss(1, 0) if j == i else Gauss(0, 0) for j in range(4)]
        out.append(det4g([list(x), list(y), list(z), ei]))
    return out


def det4g(rows):
    """4×4 determinant over ℚ(i) by cofactor expansion (exact)."""
    def det3(r):
        return (r[0][0] * (r[1][1] * r[2][2] - r[1][2] * r[2][1])
                - r[0][1] * (r[1][0] * r[2][2] - r[1][2] * r[2][0])
                + r[0][2] * (r[1][0] * r[2][1] - r[1][1] * r[2][0]))
    tot = Gauss(0, 0)
    sgn = 1
    for c in range(4):
        minor = [[rows[r][cc] for cc in range(4) if cc != c]
                 for r in range(1, 4)]
        tot = tot + sgn * rows[0][c] * det3(minor)
        sgn = -sgn
    return tot


def chart_reproduce(label, edges, col):
    """(GR-5) at one shape+colouring: build the explicit PencilSeed data and
    hub selector; assert selector correctness, point reproduction
    (projective) at EVERY body, normal reproduction at every body, and that
    the rigidity rank built from the CHART-constructed points is the grid's
    rank.  Mirrors Chart.lean's pencilChartPoint / pencilChartNormal and
    Engine.lean's PencilSeed.ofCoord exactly (fills = roles 1..3; only
    points feed pencilRow, Engine.lean:318)."""
    allverts = sorted(verts_of(edges), key=str)
    nb = neighbors_of(edges)
    target = 6 * (len(allverts) - 1)
    pt, _, _ = closure.build_fixed_config(edges, allverts, col)
    hub_normal = {v: pt[v] for v in allverts}      # seed role 0: normal ∝ pt
    chart_pt = {}
    for v in allverts:
        chn = closed_hub_nbhd(edges, nb, v)
        assert len(chn) <= 3, "hcard violated"
        # hubSel v: slots 0..len(chn)-1 = chn (IsFin3SelectorOf: member/
        # cover/injective by construction); remaining slots take fillHub.
        inputs = [hub_normal[w] for w in chn]
        # fills: complete inside pt_v^⊥ (3-dim, contains every input since
        # pt_v is isotropic and conjugate to its hub neighbours)
        perp = nullspace([pt[v]])
        assert len(perp) == 3
        for cand in perp:
            if len(inputs) == 3:
                break
            if rank(inputs + [cand]) == len(inputs) + 1:
                inputs.append(cand)
        assert len(inputs) == 3 and rank(inputs) == 3, \
            f"{label}: no LI fill completion at {v}"
        for w in chn:
            assert dot(pt[v], hub_normal[w]) == 0
        cp = cross4(*inputs)
        assert proportional(cp, pt[v]), \
            f"{label}: chart point at {v} not ∝ the grid point"
        chart_pt[v] = cp
    # normals: hub branch reads the seed (∝ pt_v by choice); non-hub branch
    # is cross₃ of the closedNbhd chart points (Chart.lean:412)
    for v in allverts:
        if len(nb[v]) >= 3:
            continue
        cnb = sorted({v, *nb[v]}, key=str)
        assert len(cnb) == 3, "degree-2 body with |closedNbhd| != 3"
        cn = cross4(*[chart_pt[w] for w in cnb])
        assert proportional(cn, pt[v]), \
            f"{label}: chart normal at non-hub {v} not ∝ the grid normal"
    # rank through the chart: rows built from the CHART points
    ext = [(e, wedge2(chart_pt[e[0]], chart_pt[e[1]])) for e in edges]
    for _, C in ext:
        assert any(c != 0 for c in C)
    rk = rank(build_rigidity_extensors(allverts, ext))
    assert rk == target, f"{label}: chart-built rank {rk} != target {target}"
    return target


def leg_chart():
    """GR-D5 — chart-image membership, upgraded from 'argued' to VERIFIED:
    at each shape's first legal target colouring, an explicit seed
    (hubNormal := the grid point; fillHub := an LI completion inside the
    body's own perp) reproduces every grid point and normal projectively
    through the landed constructions, and the rigidity rank computed FROM
    THE CHART OUTPUT is the Tay target."""
    print("[GR-D5] chart-image membership, end to end")
    pool = spline_pool()
    for label, edges in pool:
        allverts = sorted(verts_of(edges), key=str)
        target = 6 * (len(allverts) - 1)
        cols, _ = colourings(edges)
        done = False
        for col in cols:
            if combinatorial_filter(edges, allverts, col):
                continue
            d = probe(label, edges, col, fast=True)
            if d and d['ok'] and d['rk'] == target:
                t = chart_reproduce(label, edges, col)
                print(f"  {label:16s} |V|={len(allverts):3d}  chart-built "
                      f"rank = target = {t}   OK")
                done = True
                break
        assert done, f"{label}: no target colouring found"
    print("  ⟹ at every pool shape the grid configuration IS a point of the")
    print("    landed chart's image (selector + explicit seed exhibited);")
    print("    the pencilRow rank at that seed is the Tay target, which is")
    print("    hK's conclusion object (Escape.lean:555) at that shape.")
    print("    Nondegeneracy is NOT required by hK and NOT claimed here;")
    print("    the four conjuncts hold anyway (probe), while the composite")
    print("    guard rejects every σ-fixed witness ((AC-9)) -- these are")
    print("    existence witnesses, never rate evidence.")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('mech', 'spline', 'counts', 'census', 'chart', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.mech, a.spline, a.counts, a.census,
                                 a.chart])
    if run or a.mech:
        leg_mech()
    if run or a.spline:
        leg_spline()
    if run or a.counts:
        leg_counts()
    if run or a.census:
        leg_census()
    if run or a.chart:
        leg_chart()
    print("OK")


if __name__ == '__main__':
    main()
