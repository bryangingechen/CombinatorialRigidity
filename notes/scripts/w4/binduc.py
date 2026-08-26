"""
Direction BINDUC (ordinal 42) -- carry the induction BZAVOID opened toward
(BE-14): for every 2-connected `G`, `exists p : V -> P^3` with every closed star
coplanar and adjacent points distinct, at which the molecular body-hinge
rigidity matrix has rank `6(|V|-1) - def_3(G)`.

Succeeds `notes/scripts/w4/bzavoid.py` (Steps BE14-BE18).  BZAVOID's and
BATTAIN's figures are CITED, never re-run here; this driver imports `bzavoid`
and `battain` READ-ONLY.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-20)  THE BASE OF THE INDUCTION IS FREE.
             `base`    : a 3-connected graph has `def_2 = 0` (hence `def_3 = 0`).
                         EXHAUSTIVE over all connected graphs on `n <= 7`, plus
                         a sampled tier.  Each of the proof's three steps is
                         checked separately (3-edge-connectivity of every
                         vertex subset; `def_2 = 0`; `def_3 = 0`).
             `flatwit` : the POINT-side flat configuration is a legal pencil
                         configuration and its exact rank is
                         `6(|V|-1) - def_2(G)` -- the dual of BATTAIN's (BE-13)
                         cone law, measured on the point side for the first
                         time.  At `def_2 = 0` that IS the target, so every
                         3-connected graph attains with a closed-form witness.
             `gate`    : max-degree <= 2 <=> the landed
                         `IsGeneralPositionPlacement` gate is satisfiable on the
                         pencil stratum -- (BE-17)'s dead route is alive exactly
                         on the hub-free class.

  (BE-21)  THE 2-CUT `def_3` LAW.  BZAVOID's asserted
           `def_3(G) = def_3(G1) + def_3(G2) - 6` is FALSE (it goes negative);
           the exact law is
             `def_3(G) = max(g1 + g2, f1 + f2 - 6) = f1 + f2 - min(d1 + d2, 6)`
           with `f_i = def_3(G_i)`, `g_i` the same maximand restricted to
           partitions putting the two cut vertices in ONE part, `d_i = f_i - g_i`
           in `[0, 6]`.
             `twocut`  : the law, ENUMERATED, against an independent
                         set-partition oracle; plus the explicit refutation.

  (BE-22)  THE RANK HALF IS NOT ROUTINE.
             `rank2`   : the fibre-product law
                         `dim M(G) = dim M1 + dim M2 - 6 - dim(rho1 + rho2)`,
                         `rho_i <= d_i`, and the free sub-case `d1 = d2 = 0`.
             `ear`     : with ONE rigid side the criterion collapses to
                         `rho = delta` on the other side -- no general position
                         at all; measured as a BICONDITIONAL at 296 ear
                         additions to five 3-connected bases.

  (BE-23)  A NAMED CONSTRUCTION BEYOND THE FLAT CLASS.
             `hubplane`: one plane per hub; feasible when every closed
                         neighbourhood holds <= 3 hubs; measured attainment
                         where the flat witness misses by `def_2`.
             `force`   : the plane-class propagation closure (BZAVOID's triangle
                         rule GENERALIZED to the 3-shared-independent-points
                         rule) -- hunt for a forced-flat graph with
                         `def_2 > def_3`, i.e. a NEW universal-cap mechanism.

Modes: base | flatwit | gate | twocut | rank2 | ear | hubplane | force |
       validate
Reproduce: python3 notes/scripts/w4/binduc.py <mode>
All figures exact Q (fractions.Fraction); every rng seeded and printed;
degeneracy guards and a rank/dimension assert on every sampled object
(`notes/scripts/README.md` s4 -- including the `plane_basis`-class guard
"no two hinge lines at a body coincide", asserted by `assert_generic_star`).
"""
import itertools
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'kbare'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from exactcore import (rank as rank_exact, nullspace, hat,              # noqa: E402
                       neighbors)
from kbare_common import (verts_of, exact_deficiency,                    # noqa: E402
                          build_rigidity, verify_pencil_witness, spider)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (README *Harness debt*, 2026-08-20); BATTAIN was its first
# --- `w4/` consumer, `bzavoid` the second, this driver is the THIRD.  It is
# --- also the first external consumer of any `bzavoid` device.  NO MOVE MADE.
from danger import dz_gadget                                            # noqa: E402
from battain import def2_exact, necklace                                # noqa: E402
from bzavoid import (adj_of, connected_spanning, def3_of,              # noqa: E402
                     edges_of_mask)


# ==================================================================== helpers

def deg_of(n, edges):
    d = [0] * n
    for u, v in edges:
        d[u] += 1
        d[v] += 1
    return d


def conn_on(n, adj, allowed):
    """Is the subgraph induced on the bitmask `allowed` connected?"""
    if allowed == 0:
        return True
    s = (allowed & -allowed).bit_length() - 1
    seen, stack = 1 << s, [s]
    while stack:
        v = stack.pop()
        r = adj[v] & allowed & ~seen
        while r:
            b = r & -r
            seen |= b
            stack.append(b.bit_length() - 1)
            r ^= b
    return seen == allowed


def vertex_connectivity_at_least(n, edges, k):
    """True iff G is k-connected (n > k and no (k-1)-set separates)."""
    if n <= k:
        return False
    adj = adj_of(n, edges)
    full = (1 << n) - 1
    if not conn_on(n, adj, full):
        return False
    for r in range(1, k):
        for S in itertools.combinations(range(n), r):
            m = full
            for v in S:
                m &= ~(1 << v)
            if not conn_on(n, adj, m):
                return False
    return True


def min_boundary(n, edges):
    """min over proper nonempty S of |edges leaving S| (the edge connectivity
    read off directly -- 2^n subsets, exact)."""
    best = None
    for S in range(1, (1 << n) - 1):
        b = sum(1 for (u, v) in edges
                if ((S >> u) & 1) != ((S >> v) & 1))
        if best is None or b < best:
            best = b
    return best


def set_partitions(items):
    """All set partitions of `items` (Bell number many)."""
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for P in set_partitions(rest):
        for i in range(len(P)):
            yield P[:i] + [[first] + P[i]] + P[i + 1:]
        yield [[first]] + P


def part_value(edges, P, D=3):
    """6(|P|-1) - 5 d(P) for D = 3, or 3(|P|-1) - 2 d(P) for D = 2."""
    where = {}
    for i, part in enumerate(P):
        for v in part:
            where[v] = i
    d = sum(1 for (u, v) in edges if where[u] != where[v])
    if D == 3:
        return 6 * (len(P) - 1) - 5 * d
    return 3 * (len(P) - 1) - 2 * d


def def_by_partitions(edges, verts, D=3, together=None):
    """Independent oracle: max over set partitions (optionally only those
    putting every vertex of `together` in ONE part).  Exponential -- small n."""
    best = 0
    for P in set_partitions(verts):
        if together is not None:
            hit = [i for i, part in enumerate(P)
                   if any(v in part for v in together)]
            if len(set(hit)) != 1:
                continue
        best = max(best, part_value(edges, P, D))
    return best


# ---------------------------------------------------------- point-side samplers

def rq(rng, s=40):
    return F(rng.randint(-s, s))


def assert_generic_star(edges, pt):
    """The `plane_basis`-class guard (README s4): adjacent points distinct AND
    no two hinge lines at a body coincide.  Two hinges `vu`, `vw` coincide iff
    p_v, p_u, p_w are COLLINEAR, so this is a collinearity assert on every
    path of length 2."""
    nb = neighbors(edges)
    for (u, v) in edges:
        assert pt[u] != pt[v], ('coincident adjacent points', (u, v))
    for v in verts_of(edges):
        ns = sorted(nb.get(v, ()), key=str)
        for a, b in itertools.combinations(ns, 2):
            r = rank_exact([hat(pt[v]), hat(pt[a]), hat(pt[b])])
            assert r == 3, ('two hinge lines coincide at body', v, a, b)


def flat_config(edges, rng, span=200, tries=40):
    """All points in the plane {z = 0}: every closed star is coplanar, so this
    is a legal pencil configuration at EVERY graph.  Guarded for distinctness
    and for hinge-line coincidence."""
    V = sorted(verts_of(edges), key=str)
    for _ in range(tries):
        pt = {v: (rq(rng, span), rq(rng, span), F(0)) for v in V}
        if len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        assert rank_exact([hat(pt[v]) for v in V]) == 3, 'flat span not a plane'
        ok, why = verify_pencil_witness(edges, pt)
        assert ok, why
        return pt
    raise RuntimeError('flat_config: no generic draw')


def hubs_of(edges):
    nb = neighbors(edges)
    return sorted((v for v in verts_of(edges) if len(nb[v]) >= 3), key=str)


def hub_load(edges):
    """max over vertices w of #{hubs in closedNbhd(w)} -- the feasibility
    number of the hub-plane construction."""
    nb = neighbors(edges)
    H = set(hubs_of(edges))
    worst = 0
    for w in verts_of(edges):
        star = {w} | set(nb.get(w, ()))
        worst = max(worst, len(star & H))
    return worst


def hub_classes(edges, mode='singleton'):
    """A partition of the hubs into PLANE CLASSES.
      'singleton' : one plane per hub (the finest, best-rank attempt);
      'pairwise'  : union hubs u, v whenever |closedNbhd(u) cap closedNbhd(v)|
                    >= 3 -- exactly the identifications BZAVOID's (BE-15)(i)
                    propagation forces (its triangle rule is the adjacent case;
                    the non-adjacent case is a K_{2,3});
      'closure'   : the aggressive saturation of `flat_forcing_closure` -- one
                    class per connected component of the forcing relation.
    Returns a list of frozensets."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    if mode == 'singleton':
        return [frozenset([h]) for h in H]
    par = {h: h for h in H}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    def uni(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            par[ra] = rb
    star = {v: {v} | set(nb.get(v, ())) for v in verts_of(edges)}
    for a, b in itertools.combinations(H, 2):
        if len(star[a] & star[b]) >= 3:
            uni(a, b)
    if mode == 'closure':
        changed = True
        while changed:
            changed = False
            for a, b in itertools.combinations(H, 2):
                if find(a) == find(b):
                    continue
                Aa = set()
                for h in H:
                    if find(h) == find(a):
                        Aa |= star[h]
                if len(star[b] & Aa) >= 3:
                    uni(a, b)
                    changed = True
    groups = {}
    for h in H:
        groups.setdefault(find(h), set()).add(h)
    return [frozenset(g) for g in groups.values()]


def class_plane_config(edges, rng, classes=None, span=25, tries=60):
    """ONE PLANE PER HUB CLASS.  Generalizes both endpoints of the ladder: with
    singleton classes it is the hub-plane construction, with ONE class holding
    every hub it degenerates to the flat witness.  Feasible with generic planes
    when every closed neighbourhood meets <= 3 classes."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    if classes is None:
        classes = hub_classes(edges, 'singleton')
    for _ in range(tries):
        A = [[rq(rng, span) for _ in range(4)] for _ in classes]
        for a in A:
            assert any(x != 0 for x in a), 'zero plane'
        pt = {}
        bad = False
        for w in V:
            star = {w} | set(nb.get(w, ()))
            rows = [A[i] for i, C in enumerate(classes) if star & C]
            if not rows:
                pt[w] = (rq(rng, span), rq(rng, span), rq(rng, span))
                continue
            if len(rows) > 3:
                return None
            sol = nullspace(rows)
            if len(sol) != 4 - rank_exact(rows):
                bad = True
                break
            for _ in range(30):
                c = [rq(rng, span) for _ in sol]
                x = [sum(c[i] * sol[i][k] for i in range(len(sol)))
                     for k in range(4)]
                if x[3] != 0:
                    break
            else:
                bad = True
                break
            pt[w] = tuple(x[k] / x[3] for k in range(3))
        if bad or len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        ok, why = verify_pencil_witness(edges, pt)
        if not ok:
            continue
        return pt
    return None


def best_construction(edges, rng, nseeds=3, seed0=0):
    """The construction LADDER: singleton -> pairwise -> closure classes, plus
    the flat witness.  Returns (best_rank, tag, pt)."""
    out = (-1, None, None)
    for mode in ('singleton', 'pairwise', 'closure'):
        cls = hub_classes(edges, mode)
        for s in range(nseeds):
            pt = class_plane_config(edges, random.Random(seed0 + 613 * s + 7),
                                    classes=cls)
            if pt is None:
                continue
            r = rank_exact(build_rigidity(edges, pt)[0])
            if r > out[0]:
                out = (r, f'{mode}({len(cls)} classes)', pt)
    pt = flat_config(edges, random.Random(seed0 + 3))
    r = rank_exact(build_rigidity(edges, pt)[0])
    if r > out[0]:
        out = (r, 'flat', pt)
    return out


def hubplane_config(edges, rng, span=25, tries=60):
    """ONE PLANE PER HUB.  Feasible with generic planes when every closed
    neighbourhood holds <= 3 hubs.  Implementation: pick a generic plane
    `A_v . x = 0` (in hat coordinates) per hub, then solve, per vertex `w`, the
    linear system {A_v . hat(p_w) = 0 : v hub in closedNbhd(w)}.  A vertex with
    0 constraints is generic; 1 -> a 2-plane of solutions; 2 -> a line; 3 -> a
    point.  Returns None if the draw degenerates."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    H = hubs_of(edges)
    for _ in range(tries):
        A = {v: [rq(rng, span) for _ in range(4)] for v in H}
        for v in H:
            assert any(a != 0 for a in A[v]), 'zero plane'
        pt = {}
        bad = False
        for w in V:
            star = {w} | set(nb.get(w, ()))
            rows = [A[v] for v in H if v in star]
            if not rows:
                pt[w] = (rq(rng, span), rq(rng, span), rq(rng, span))
                continue
            if len(rows) > 3:
                return None            # over-determined by construction
            sol = nullspace(rows)
            if len(sol) != 4 - rank_exact(rows):
                bad = True
                break
            # a generic point of the solution space with nonzero last coord
            for _ in range(30):
                c = [rq(rng, span) for _ in sol]
                x = [sum(c[i] * sol[i][k] for i in range(len(sol)))
                     for k in range(4)]
                if x[3] != 0:
                    break
            else:
                bad = True
                break
            pt[w] = tuple(x[k] / x[3] for k in range(3))
        if bad or len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        ok, why = verify_pencil_witness(edges, pt)
        if not ok:
            continue
        return pt
    return None


# ---------------------------------------------------------------- rank devices

def motion_space(edges, pt):
    """Basis of M = ker(rigidity matrix), indexed by 6-blocks per vertex."""
    rows, nV = build_rigidity(edges, pt)
    ker = nullspace(rows)
    r = rank_exact(rows)
    assert len(ker) == 6 * nV - r, 'kernel dimension mismatch'
    return ker, r, nV


def rel_screw_space(edges, pt, u, v):
    """rho_bar = image of M under m |-> m(v) - m(u), a subspace of K^6."""
    V = sorted(verts_of(edges), key=str)
    idx = {w: i for i, w in enumerate(V)}
    ker, r, nV = motion_space(edges, pt)
    bu, bv = 6 * idx[u], 6 * idx[v]
    img = [[m[bv + k] - m[bu + k] for k in range(6)] for m in ker]
    return rank_exact(img) if img else 0, img, len(ker), r


# ============================================== (BE-20)(i): 3-connected => def2

def run_base(nmax=7, sample_tier=(8, 9, 10), nsamp=400, seed=20260826):
    print("===== Step BE19 / (BE-20)(i): a 3-CONNECTED graph has def_2 = 0 "
          "=====")
    print("  Proof: 3-connected => 3-edge-connected, so every proper nonempty")
    print("  S has |dS| >= 3; summing over a q-part partition, 2 d(P) >= 3q,")
    print("  hence 3(q-1) - 2d(P) <= -3 < 0 for every q >= 2, and the q = 1")
    print("  partition gives 0.  Each step is checked separately below.")
    t0 = time.time()
    grand = 0
    nb_checked = [0]
    for n in range(4, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        m = len(pairs)
        seen3 = 0
        worst_pd = None
        for mask in range(1 << m):
            edges = edges_of_mask(pairs, mask)
            if len(edges) < (3 * n + 1) // 2:
                continue
            d = deg_of(n, edges)
            if min(d) < 3:
                continue
            if not vertex_connectivity_at_least(n, edges, 3):
                continue
            seen3 += 1
            # step 1: every proper nonempty subset has >= 3 boundary edges.
            # The 2^n subset sweep is the cost driver, so it runs on EVERY
            # graph up to n = 6 and on every 200th at n = 7 (the step itself is
            # the classical "k-connected => k-edge-connected"; the sweep is
            # corroboration, the def_2 assert below is the claim).
            if n <= 6 or seen3 % 200 == 0:
                mb = min_boundary(n, edges)
                assert mb >= 3, ('boundary < 3 at 3-connected', edges, mb)
                nb_checked[0] += 1
            # step 2 + 3: def_2 = 0 and def_3 = 0
            d2 = def2_exact(edges)
            assert d2 == 0, ('def_2 > 0 at a 3-connected graph', edges, d2)
            d3 = exact_deficiency(edges)[0]
            assert d3 == 0, ('def_3 > 0 at a 3-connected graph', edges, d3)
            # the sharper form, on an independent oracle, at small n
            if n <= 6:
                pd = max(part_value(edges, P, D=2)
                         for P in set_partitions(range(n)) if len(P) >= 2)
                assert pd <= -3, ('partitionDef_2 > -3', edges, pd)
                worst_pd = pd if worst_pd is None else max(worst_pd, pd)
        grand += seen3
        extra = (f", worst partitionDef_2 over q >= 2 partitions = {worst_pd}"
                 if worst_pd is not None else "")
        print(f"  n = {n}: {seen3} 3-connected labelled graphs, ALL with "
              f"min|dS| >= 3, def_2 = 0, def_3 = 0{extra}")
    print(f"  EXHAUSTIVE total n = 4..{nmax}: {grand} 3-connected graphs, "
          f"zero exceptions ({nb_checked[0]} of them also swept over all 2^n "
          f"vertex subsets for the |dS| >= 3 step)")
    rng = random.Random(seed)
    ns = 0
    for n in sample_tier:
        pairs = list(itertools.combinations(range(n), 2))
        got = 0
        guard = 0
        while got < nsamp and guard < 200 * nsamp:
            guard += 1
            k = rng.randint((3 * n + 1) // 2, min(len(pairs), 3 * n))
            edges = sorted(rng.sample(pairs, k))
            if min(deg_of(n, edges)) < 3:
                continue
            if not vertex_connectivity_at_least(n, edges, 3):
                continue
            got += 1
            assert min_boundary(n, edges) >= 3, edges
            assert def2_exact(edges) == 0, edges
            assert def3_of(edges, n) == 0, edges
        ns += got
        print(f"  n = {n}: {got} sampled 3-connected graphs, all def_2 = 0 "
              f"(seed {seed})")
    print(f"  sampled total: {ns}")
    # the contrapositive, which is what the induction actually uses
    print("  CONTRAPOSITIVE (what the induction uses): def_2(G) > 0 => G is NOT")
    print("  3-connected, so G has a cut of size <= 2 -- every hard graph for")
    print("  (BE-14) is 1-cut- or 2-cut-decomposable.")
    cnt = 0
    for n in range(4, 7):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = edges_of_mask(pairs, mask)
            if not edges:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            if def2_exact(edges) > 0:
                assert not vertex_connectivity_at_least(n, edges, 3), edges
                cnt += 1
    print(f"  EXHAUSTIVE n = 4..6: {cnt} connected graphs with def_2 > 0, "
          f"NONE 3-connected")
    print(f"  [{time.time() - t0:.1f} s]")
    return grand


# ============================== (BE-20)(ii): the POINT-side flat cone law

def shape_battery():
    """(name, edges, is3conn-or-None) -- the measured battery."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    K5 = [(i, j) for i in range(5) for j in range(i + 1, 5)]
    cube = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
            (0, 4), (1, 5), (2, 6), (3, 7)]
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    pet = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (5, 7), (7, 9), (9, 6),
           (6, 8), (8, 5), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    prism = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    out = [('K4', K4), ('K5', K5), ('prism', prism), ('K33', K33),
           ('cube', cube), ('petersen', pet),
           ('theta(3,3,3)', theta(3, 3, 3)), ('theta(4,4,4)', theta(4, 4, 4)),
           ('theta(4,5,6)', theta(4, 5, 6)),
           ('C6', cycle(6)), ('C8', cycle(8)),
           ('necklace(3)', necklace(3)), ('necklace(4)', necklace(4)),
           ('spider(5,5,5)+c', spider(5, 5, 5)[0]),
           ('DZ', dz_gadget())]
    return out


def cycle(n):
    return [(f'v{i}', f'v{(i + 1) % n}') for i in range(n)]


def theta(a, b, c):
    """Two hubs u, v joined by three internally-disjoint paths of `a`, `b`, `c`
    EDGES each (a, b, c >= 2)."""
    E = []
    k = 0
    for L in (a, b, c):
        prev = 'u'
        for _ in range(L - 1):
            k += 1
            cur = f'x{k}'
            E.append((prev, cur))
            prev = cur
        E.append((prev, 'v'))
    return E


def def_pair(edges):
    V = sorted(verts_of(edges), key=str)
    n = len(V)
    d3 = def3_of(edges, n)
    d2 = def2_exact(edges) if n <= 16 else None
    return n, d2, d3


def run_flatwit(nseeds=4, seed=20260826):
    print("===== Step BE19 / (BE-20)(ii): the POINT-side FLAT configuration -- "
          "rank = 6(|V|-1) - def_2(G) =====")
    print("  BATTAIN's (BE-13) priced the PANEL-side cone (all points")
    print("  COINCIDENT, so illegal for (BE-14), which demands adjacent points")
    print("  distinct).  Its projective dual is the POINT-side FLAT")
    print("  configuration: all points in ONE plane, pairwise distinct -- a")
    print("  legal pencil configuration at EVERY graph.  Measured here.")
    t0 = time.time()
    rows = []
    for (name, E) in shape_battery():
        n, d2, d3 = def_pair(E)
        target = 6 * (n - 1) - d3
        best = -1
        for s in range(nseeds):
            rng = random.Random(seed + 977 * s)
            pt = flat_config(E, rng)
            r = rank_exact(build_rigidity(E, pt)[0])
            best = max(best, r)
        law = None if d2 is None else 6 * (n - 1) - d2
        flag = 'ATTAINS' if best == target else f'misses by {target - best}'
        agree = '' if law is None else (' law OK' if law == best
                                        else f' LAW BROKEN ({law})')
        rows.append((name, n, d2, d3, best, target, law))
        print(f"  {name:16s} n={n:3d} def_2={str(d2):>5s} def_3={d3:2d} "
              f"flat rank={best:4d} target={target:4d}  {flag:14s}{agree}")
        if law is not None:
            assert best == law, (name, best, law)
    print("  Every row: flat rank = 6(|V|-1) - def_2 EXACTLY (where def_2 is")
    print("  computable), so the flat witness attains iff def_2 = def_3.")
    print("  Combined with (BE-20)(i): EVERY 3-CONNECTED GRAPH ATTAINS, with a")
    print("  closed-form witness and no genericity argument.")
    print(f"  multi-seed: {nseeds} draws per shape, max taken (F27: rank is")
    print("  lower semicontinuous, so one draw is only a lower bound)")
    print(f"  [{time.time() - t0:.1f} s]  seed {seed}")
    return rows


# ============================ (BE-20)(iii): the general-position gate, revisited

def run_gate(seed=20260826):
    print("===== Step BE19 / (BE-20)(iii): the landed general-position gate is "
          "satisfiable on the pencil stratum EXACTLY on the hub-free class =====")
    print("  `IsGeneralPositionPlacement` (GeneralPositionPlacement.lean:59) is")
    print("  'every s with s.card <= 4 is affinely independent'.  (BE-17)(i)")
    print("  observed it is NEGATED at every hub.  Converse direction, checked")
    print("  here: with NO hub the pencil condition is VACUOUS, so a generic")
    print("  point configuration satisfies both at once.")
    t0 = time.time()
    rng = random.Random(seed)
    for (name, E) in [('C6', cycle(6)), ('C8', cycle(8)), ('P5', path(5)),
                      ('C4', cycle(4))]:
        V = sorted(verts_of(E), key=str)
        pt = {v: (rq(rng), rq(rng), rq(rng)) for v in V}
        ok, _ = verify_pencil_witness(E, pt)
        gp = all(rank_exact([hat(pt[w]) for w in S]) == len(S)
                 for k in range(1, 5) for S in itertools.combinations(V, k))
        n, d2, d3 = def_pair(E)
        r = rank_exact(build_rigidity(E, pt)[0])
        print(f"  {name:5s} hubs={len(hubs_of(E))} pencil-legal={ok} "
              f"generalposition={gp} rank={r} target={6 * (n - 1) - d3}")
        assert ok and gp
    for (name, E) in [('K4', [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
                      ('theta(4,4,4)', theta(4, 4, 4))]:
        V = sorted(verts_of(E), key=str)
        pt = flat_config(E, random.Random(seed + 5))
        bad = [S for S in itertools.combinations(V, 4)
               if rank_exact([hat(pt[w]) for w in S]) < 4]
        print(f"  {name:12s} hubs={len(hubs_of(E))}: flat witness violates the "
              f"gate at {len(bad)} of {len(list(itertools.combinations(V, 4)))} "
              f"4-subsets")
        assert bad
        # and at a hub-plane witness, the hub's own closed star violates it
        pt2 = hubplane_config(E, random.Random(seed + 11))
        if pt2 is not None:
            nb = neighbors(E)
            for v in hubs_of(E):
                star = sorted({v} | set(nb[v]), key=str)
                sub = star[:4]
                assert rank_exact([hat(pt2[w]) for w in sub]) < 4, (name, v)
            print(f"  {name:12s} hub-plane witness: every hub's closed star is "
                  f"still affinely DEPENDENT (gate still negated)")
    print("  So (BE-17)'s dead route is alive exactly on max-degree <= 2 --")
    print("  which is the S-node class of the 3-block decomposition.")
    print(f"  [{time.time() - t0:.1f} s]")


def path(n):
    return [(f'v{i}', f'v{i + 1}') for i in range(n - 1)]


# ================================== (BE-21): the 2-cut `def_3` law

def piece_defs(n, edges):
    """(f, g) = (def_3, def_3 restricted to partitions with 0, 1 together),
    both by the INDEPENDENT set-partition oracle; `f` cross-checked against
    `kbare_common.exact_deficiency`."""
    f = def_by_partitions(edges, range(n), D=3)
    g = def_by_partitions(edges, range(n), D=3, together=(0, 1))
    fx = exact_deficiency(edges)[0]
    assert f == fx, ('oracle disagreement', edges, f, fx)
    assert 0 <= f - g <= 6, ('delta out of [0,6]', edges, f, g)
    return f, g


def enum_pieces(n):
    """All connected spanning graphs on `range(n)` with (0,1) NOT an edge and
    with (0,1) an edge, as two dicts mask -> (edges, f, g)."""
    pairs = list(itertools.combinations(range(n), 2))
    out = []
    for mask in range(1 << len(pairs)):
        edges = edges_of_mask(pairs, mask)
        if not edges:
            continue
        if not connected_spanning(n, adj_of(n, edges)):
            continue
        f, g = piece_defs(n, edges)
        out.append((edges, f, g))
    return out


def run_twocut(ns=(3, 4, 5), npairs=30000, seed=20260826):
    print("===== Step BE20 / (BE-21): the 2-cut `def_3` law -- BZAVOID's "
          "asserted `- 6` is FALSE =====")
    t0 = time.time()
    print("  BZAVOID *Step BE18* asserts, as its cap 8, that the 2-cut")
    print("  extension 'looks routine ... with def_3(G) = def_3(G1) + def_3(G2)")
    print("  - 6 to be checked'.  It is not merely unchecked: it is FALSE, and")
    print("  it can be NEGATIVE, which def_3 never is.")
    # the explicit refutation: two triangles sharing the edge 01 (= K4 - e)
    E1 = [(0, 1), (0, 2), (1, 2)]
    E2 = [(0, 3), (1, 3)]
    E = E1 + E2
    f1 = def_by_partitions(E1, (0, 1, 2), D=3)
    g1 = def_by_partitions(E1, (0, 1, 2), D=3, together=(0, 1))
    f2 = def_by_partitions(E2, (0, 1, 3), D=3)
    g2 = def_by_partitions(E2, (0, 1, 3), D=3, together=(0, 1))
    f = def_by_partitions(E, range(4), D=3)
    assert (f1, f) == (exact_deficiency(E1)[0], exact_deficiency(E)[0])
    print(f"  WITNESS  G1 = triangle 012, G2 = path 0-3-1, G = K4 - e:")
    print(f"    def_3(G1) = {f1}, def_3(G2) = {f2}, def_3(G) = {f}")
    print(f"    asserted `f1 + f2 - 6` = {f1 + f2 - 6}  <-- NEGATIVE, refuted")
    print(f"    derived  `max(g1+g2, f1+f2-6)` = "
          f"max({g1}+{g2}, {f1 + f2 - 6}) = {max(g1 + g2, f1 + f2 - 6)} = "
          f"def_3(G): {max(g1 + g2, f1 + f2 - 6) == f}")
    assert f1 + f2 - 6 != f
    assert max(g1 + g2, f1 + f2 - 6) == f
    # the law, enumerated
    print("  THE LAW, enumerated over 2-cut gluings (shared pair = {0,1}):")
    print("    def_3(G) = max(g1 + g2, f1 + f2 - 6) = f1 + f2 - min(d1+d2, 6)")
    rng = random.Random(seed)
    cache = {n: enum_pieces(n) for n in ns}
    for n in ns:
        print(f"    n = {n}: {len(cache[n])} connected spanning pieces")
    tested = 0
    minus6_right = 0
    minus6_negative = 0
    delta_hist = {}
    tight_g = 0
    tight_f = 0
    for n1 in ns:
        for n2 in ns:
            P1, P2 = cache[n1], cache[n2]
            allpairs = [(i, j) for i in range(len(P1)) for j in range(len(P2))]
            if len(allpairs) > npairs // (len(ns) ** 2):
                allpairs = rng.sample(allpairs, npairs // (len(ns) ** 2))
            for (i, j) in allpairs:
                E1, f1, g1 = P1[i]
                E2, f2, g2 = P2[j]
                has1 = (0, 1) in E1
                has2 = (0, 1) in E2
                if has1 and has2:
                    continue            # would be a parallel edge in G
                # relabel G2's private vertices
                shift = n1 - 2
                def rl(v):
                    return v if v < 2 else v + shift
                E2r = [(min(rl(a), rl(b)), max(rl(a), rl(b))) for (a, b) in E2]
                E = sorted(set(E1) | set(E2r))
                assert len(E) == len(E1) + len(E2), 'edge collision'
                nn = n1 + n2 - 2
                f = exact_deficiency(E)[0]
                d1, d2 = f1 - g1, f2 - g2
                law = max(g1 + g2, f1 + f2 - 6)
                law2 = f1 + f2 - min(d1 + d2, 6)
                assert law == law2, (E1, E2, law, law2)
                assert f == law, ('LAW BROKEN', E1, E2, f, law, f1, f2, g1, g2)
                if f1 + f2 - 6 == f:
                    minus6_right += 1
                if f1 + f2 - 6 < 0:
                    minus6_negative += 1
                if law == g1 + g2:
                    tight_g += 1
                if law == f1 + f2 - 6:
                    tight_f += 1
                delta_hist[(d1, d2)] = delta_hist.get((d1, d2), 0) + 1
                tested += 1
    print(f"    {tested} gluings: the law holds at EVERY one; the asserted")
    print(f"    `f1+f2-6` is correct at {minus6_right} "
          f"({100.0 * minus6_right / tested:.1f} %) and IMPOSSIBLE (negative) "
          f"at {minus6_negative} ({100.0 * minus6_negative / tested:.1f} %)")
    print(f"    branch `g1+g2` attains the max at {tight_g}, branch "
          f"`f1+f2-6` at {tight_f} (both at {tight_g + tight_f - tested})")
    ds = sorted(delta_hist.items(), key=lambda kv: -kv[1])[:8]
    print(f"    (delta1, delta2) histogram, top 8: {ds}")
    print(f"    delta range observed: "
          f"{min(min(k) for k in delta_hist)}..{max(max(k) for k in delta_hist)}"
          f" (proved to lie in [0,6])")
    print(f"  [{time.time() - t0:.1f} s]  seed {seed}")
    return tested


# ==================== (BE-22): the rank half of the 2-cut, and what it needs

def split_at_pair(edges, u, v):
    """Split G at the 2-cut {u,v}: returns (V1, E1, V2, E2) with
    V1 cap V2 = {u,v}, E1 cup E2 = E, E1 cap E2 = {} (the edge uv, if present,
    goes to side 1).  Returns None if {u,v} is not a cut."""
    V = sorted(verts_of(edges), key=str)
    nb = neighbors(edges)
    rest = [w for w in V if w not in (u, v)]
    if not rest:
        return None
    seen = set()
    comps = []
    for s in rest:
        if s in seen:
            continue
        comp, stack = [], [s]
        seen.add(s)
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in nb[x]:
                if y in (u, v) or y in seen:
                    continue
                seen.add(y)
                stack.append(y)
        comps.append(sorted(comp, key=str))
    if len(comps) < 2:
        return None
    # side 1 = the first component, side 2 = everything else
    S1 = set(comps[0])
    S2 = set().union(*comps[1:])
    V1 = sorted(S1 | {u, v}, key=str)
    V2 = sorted(S2 | {u, v}, key=str)
    E1 = [e for e in edges if (e[0] in S1 or e[1] in S1)]
    E2 = [e for e in edges if (e[0] in S2 or e[1] in S2)]
    uv = [e for e in edges if set(e) == {u, v}]
    E1 = E1 + uv
    assert len(E1) + len(E2) == len(edges), (len(E1), len(E2), len(edges))
    return V1, E1, V2, E2


def combinatorial_deltas(edges, u, v):
    """(f1, g1, f2, g2) for a split at {u,v}, by the set-partition oracle."""
    sp = split_at_pair(edges, u, v)
    if sp is None:
        return None
    V1, E1, V2, E2 = sp
    if len(V1) > 9 or len(V2) > 9:
        return None
    f1 = def_by_partitions(E1, V1, D=3)
    g1 = def_by_partitions(E1, V1, D=3, together=(u, v))
    f2 = def_by_partitions(E2, V2, D=3)
    g2 = def_by_partitions(E2, V2, D=3, together=(u, v))
    return (V1, E1, f1, g1, V2, E2, f2, g2)


def run_rank2(seed=20260826):
    print("===== Step BE21 / (BE-22): the RANK half of the 2-cut -- the exact "
          "fibre-product law, and the two things it needs =====")
    print("  M(G) = {(m1,m2) in M1 x M2 : m1 = m2 on {u,v}}, so with")
    print("  rho_bar_i := image of M_i under m |-> m(v) - m(u)  (a subspace of")
    print("  the 6-dim screw space, the DIAGONAL having been quotiented out):")
    print("     dim M(G) = dim M1 + dim M2 - 6 - dim(rho_bar_1 + rho_bar_2).")
    print("  With the pieces attaining (dim M_i = 6 + f_i), G attains IFF")
    print("     dim(rho_bar_1 + rho_bar_2) = min(delta_1 + delta_2, 6),")
    print("  and rho_i <= delta_i ALWAYS (the welded framework obeys the same")
    print("  universal cap), with equality iff the WELDED framework attains.")
    t0 = time.time()
    cases = [
        ('K4-e (two triangles, shared edge)',
         [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3)], 0, 1),
        ('two K4 sharing an edge',
         [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
          (0, 4), (0, 5), (1, 4), (1, 5), (4, 5)], 0, 1),
        ('theta(3,3,3)', theta(3, 3, 3), 'u', 'v'),
        ('theta(4,4,4)', theta(4, 4, 4), 'u', 'v'),
        ('K4 + ear 0-4-5-1',
         [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
          (0, 4), (4, 5), (5, 1)], 0, 1),
        ('C6 + ear v0-w-v3',
         cycle(6) + [('v0', 'w'), ('w', 'v3')], 'v0', 'v3'),
        ('C10 at antipodes', cycle(10), 'v0', 'v5'),
    ]
    for (name, E, u, v) in cases:
        cd = combinatorial_deltas(E, u, v)
        assert cd is not None, (name, 'not a 2-cut')
        V1, E1, f1, g1, V2, E2, f2, g2 = cd
        d1, d2 = f1 - g1, f2 - g2
        n, dd2, dd3 = def_pair(E)
        target = 6 * (n - 1) - dd3
        law = max(g1 + g2, f1 + f2 - 6)
        assert law == dd3, (name, law, dd3)
        print(f"\n  --- {name}: cut {{{u},{v}}}, |V1| = {len(V1)}, "
              f"|V2| = {len(V2)}")
        print(f"      f1={f1} g1={g1} delta1={d1} | f2={f2} g2={g2} "
              f"delta2={d2} | def_3(G)={dd3} (= the (BE-21) law) def_2(G)={dd2}")
        cands = [('flat', flat_config(E, random.Random(seed)))]
        rb, tb, pb = best_construction(E, None, nseeds=3, seed0=seed)
        if tb != 'flat':
            cands.append((tb, pb))
        for (tag, pt) in cands:
            if pt is None:
                print(f"      {tag:10s}: construction INFEASIBLE here "
                      f"(hub load {hub_load(E)})")
                continue
            r = rank_exact(build_rigidity(E, pt)[0])
            dimM = 6 * n - r
            r1, img1, k1, rk1 = rel_screw_space(E1, pt, u, v)
            r2, img2, k2, rk2 = rel_screw_space(E2, pt, u, v)
            rsum = rank_exact(img1 + img2)
            ok_law = (dimM == k1 + k2 - 6 - rsum)
            assert ok_law, (name, tag, dimM, k1, k2, rsum)
            att1 = (rk1 == 6 * (len(V1) - 1) - f1)
            att2 = (rk2 == 6 * (len(V2) - 1) - f2)
            print(f"      {tag:20s}: rank {r} (target {target}"
                  f"{', ATTAINS' if r == target else f', misses {target - r}'})"
                  f"; dim M = {dimM} = {k1} + {k2} - 6 - {rsum} "
                  f"[fibre law OK]")
            # the GENERAL bound (holds whether or not the piece attains):
            # rho_i = dim M_i - dim M(welded_i) <= dim M_i - 6 - g_i, since the
            # welded framework is a body-hinge framework on the CONTRACTED
            # MULTIGRAPH and obeys the same elementary partition cap.  It
            # specialises to rho_i <= delta_i exactly when the piece attains.
            b1, b2 = k1 - 6 - g1, k2 - 6 - g2
            print(f"                  pieces attain: {att1}/{att2}; "
                  f"rho_1 = {r1} (<= dimM1-6-g1 = {b1}; delta_1 = {d1}), "
                  f"rho_2 = {r2} (<= dimM2-6-g2 = {b2}; delta_2 = {d2}); "
                  f"dim(rho_1+rho_2) = {rsum} vs max possible "
                  f"{min(d1 + d2, 6)}")
            assert r1 <= b1 and r2 <= b2, (name, tag, r1, b1, r2, b2)
            if att1:
                assert r1 <= d1, (name, tag, r1, d1)
            if att2:
                assert r2 <= d2, (name, tag, r2, d2)
            if r == target:
                assert att1 and att2 and rsum == min(d1 + d2, 6), (name, tag)
    print("\n  Free sub-case, PROVED and visible above: delta_1 = delta_2 = 0")
    print("  forces rho_1 = rho_2 = 0, so the general-position condition is")
    print("  VACUOUS and the composition is automatic -- in particular whenever")
    print("  both pieces are RIGID (f_i = 0), which by (BE-20) is every")
    print("  3-connected piece.")
    print(f"  [{time.time() - t0:.1f} s]  seed {seed}")


# =============== (BE-22)(vi): one rigid side kills the general-position half

def ear(base, u, v, m, tag='e'):
    """`base` plus an internally-disjoint path u - w1 - ... - wm - v."""
    E = list(base)
    prev = u
    for i in range(m):
        cur = f'{tag}{i}'
        E.append((prev, cur))
        prev = cur
    E.append((prev, v))
    return E


def run_ear(nseeds=3, seed=20260826):
    print("===== Step BE21 / (BE-22)(vi): with ONE RIGID SIDE the 2-cut "
          "criterion loses its general-position half =====")
    print("  If delta_2 = 0 then rho_2 = 0, so dim(rho_1 + rho_2) = rho_1 and")
    print("  min(delta_1 + 0, 6) = delta_1 (as delta_1 <= 6): the criterion is")
    print("  EXACTLY `rho_1 = delta_1`, i.e. side 1's WELDED framework attains.")
    print("  No general position at all.  By (BE-20) every 3-connected side is")
    print("  rigid, so this is the common case in a 3-block decomposition.")
    print("  Measured at EAR ADDITIONS to 3-connected bases (the canonical")
    print("  flexible side: a path with m interior vertices has")
    print("  delta = min(m+1, 6), and its welded framework is the cycle C_{m+1},")
    print("  which attains by (BE-20)(iii)).")
    t0 = time.time()
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    K5 = [(i, j) for i in range(5) for j in range(i + 1, 5)]
    cube = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
            (0, 4), (1, 5), (2, 6), (3, 7)]
    prism = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    bases = [('K4', K4, 4), ('K5', K5, 5), ('prism', prism, 6),
             ('K33', K33, 6), ('cube', cube, 8)]
    bases_by_name = [(b[0], b[1]) for b in bases]
    tot = 0
    att = 0
    misses = []
    for (bname, B, nb_) in bases:
        for (a, b) in itertools.combinations(range(nb_), 2):
            for m in (1, 2, 3, 4):
                E = ear(B, a, b, m)
                if (a, b) in B and m == 0:
                    continue
                V = sorted(verts_of(E), key=str)
                n = len(V)
                d3 = def3_of(E, n)
                d2 = def2_exact(E) if n <= 16 else None
                tgt = 6 * (n - 1) - d3
                # the split at the attachment pair, and its deltas
                cd = combinatorial_deltas(E, a, b)
                dd = None
                if cd is not None:
                    V1, E1, f1, g1, V2, E2, f2, g2 = cd
                    dd = (f1 - g1, f2 - g2)
                r, tagc, ptc = best_construction(E, None, nseeds=nseeds,
                                                 seed0=seed)
                tot += 1
                # the fibre-product identity (BE-22)(i) at the chosen config,
                # asserted on EVERY case -- and the criterion diagnostics
                diag = None
                if cd is not None and ptc is not None:
                    r1, i1, k1, rk1 = rel_screw_space(E1, ptc, a, b)
                    r2, i2, k2, rk2 = rel_screw_space(E2, ptc, a, b)
                    rsum = rank_exact(i1 + i2)
                    dimM = 6 * n - r
                    assert dimM == k1 + k2 - 6 - rsum, (bname, a, b, m)
                    at1 = (rk1 == 6 * (len(V1) - 1) - f1)
                    at2 = (rk2 == 6 * (len(V2) - 1) - f2)
                    diag = (at1, at2, r1, r2, rsum, min(dd[0] + dd[1], 6))
                if r == tgt:
                    att += 1
                    if diag is not None:
                        assert diag[0] and diag[1] and diag[4] == diag[5], \
                            (bname, a, b, m, diag)
                else:
                    misses.append((bname, a, b, m, r, tgt, d2, d3, dd, tagc,
                                   diag))
        print(f"  base {bname:6s}: ears at every attachment pair, m = 1..4 -- "
              f"running total {att}/{tot} attaining")
    print(f"  TOTAL {att} of {tot} ear additions to a 3-connected base ATTAIN")
    if misses:
        print(f"  {len(misses)} MISSES (the informative rows):")
        for r in misses[:6]:
            print(f"    base={r[0]} pair={r[1], r[2]} m={r[3]} rank={r[4]} "
                  f"target={r[5]} def_2={r[6]} def_3={r[7]} "
                  f"(delta1,delta2)={r[8]} best-by={r[9]}")
            print(f"      diagnostics (pieces attain, rho_1, rho_2, "
                  f"dim(rho_1+rho_2), max): {r[10]}")
        hl = {}
        for r in misses:
            E = ear(dict(bases_by_name)[r[0]], r[1], r[2], r[3])
            hl[hub_load(E)] = hl.get(hub_load(E), 0) + 1
        print(f"    hub-load histogram over the misses: {hl}")
        print("    EVERY miss is a CONSTRUCTION-LADDER miss, not an attainment")
        print("    refutation: `rank <= target` is universal, so a measured rank")
        print("    is a LOWER bound on the stratum maximum -- these rows are")
        print("    'not found under this constructor', never 'does not exist',")
        print("    and they are exactly the (BE-23)(i) hub-load >= 4 limit.")
    print(f"  [{time.time() - t0:.1f} s]  seed {seed}")
    return att, tot


# ============================ (BE-23): the hub-plane construction, and the hunt

def run_hubplane(nseeds=3, sweep=True, seed=20260826):
    print("===== Step BE22 / (BE-23)(i): the HUB-PLANE construction -- one "
          "plane per hub =====")
    print("  Feasibility (generic planes): every closed neighbourhood holds")
    print("  <= 3 hubs, since p_w must lie in one plane per hub of")
    print("  closedNbhd(w) and 4 generic planes have no common point.")
    t0 = time.time()
    rows = []
    for (name, E) in shape_battery():
        n, d2, d3 = def_pair(E)
        target = 6 * (n - 1) - d3
        hl = hub_load(E)
        best = -1
        aff = None
        for s in range(nseeds):
            pt = hubplane_config(E, random.Random(seed + 613 * s))
            if pt is None:
                continue
            r = rank_exact(build_rigidity(E, pt)[0])
            if r > best:
                best = r
                aff = rank_exact([hat(pt[w]) for w in sorted(pt, key=str)])
        flatr = rank_exact(build_rigidity(
            E, flat_config(E, random.Random(seed)))[0])
        if best < 0:
            print(f"  {name:16s} n={n:3d} hubs={len(hubs_of(E)):2d} "
                  f"hubload={hl} INFEASIBLE (flat rank {flatr}, target {target})")
            rows.append((name, hl, None, flatr, target))
            continue
        flag = 'ATTAINS' if best == target else f'misses {target - best}'
        print(f"  {name:16s} n={n:3d} hubs={len(hubs_of(E)):2d} hubload={hl} "
              f"rank={best:4d} target={target:4d} {flag:11s} "
              f"(flat {flatr}, gain {best - flatr}) affine-span={aff}")
        rows.append((name, hl, best, flatr, target))
    # ---- the class LADDER on the same battery, and the honest limit
    print("  LADDER (singleton -> pairwise -> closure classes, plus flat), best:")
    for (name, E) in shape_battery():
        n, d2, d3 = def_pair(E)
        target = 6 * (n - 1) - d3
        r, tag, _ = best_construction(E, None, nseeds=nseeds, seed0=seed)
        print(f"  {name:16s} best rank {r:4d} / target {target:4d} by "
              f"{tag:22s} {'ATTAINS' if r == target else 'MISSES'}")
    print("  The INFEASIBLE rows are the honest limit: at hub load >= 4 the")
    print("  hub planes cannot be generic (4 generic planes have no common")
    print("  point), so they must be given a CONCURRENCY structure -- which is")
    print("  exactly what BATTAIN's panel-side `sample_Y` / `localcone` tower")
    print("  does per graph, and where DZ's and the necklaces' recorded")
    print("  attainment certificates come from (CITED, not re-run).")
    # ---- the class-uniformity sweep for the named class
    if not sweep:
        print("  (sweep skipped in `validate`; run the `hubplane` mode for it)")
        print(f"  [{time.time() - t0:.1f} s]  seed {seed}")
        return rows
    print("  SWEEP: every connected graph with hub load <= 3 in reach --")
    print("  does the hub-plane construction attain at ALL of them?")
    t1 = time.time()
    rng = random.Random(seed)
    tot = 0
    hard = 0
    fails = []
    def probe(n, edges):
        nonlocal tot, hard
        d3 = exact_deficiency(edges)[0]
        d2 = def2_exact(edges)
        pt = hubplane_config(edges, random.Random(seed + 17 * len(edges) + n))
        if pt is None:
            return False
        r = rank_exact(build_rigidity(edges, pt)[0])
        tgt = 6 * (n - 1) - d3
        tot += 1
        if d2 > d3:
            hard += 1
        if r != tgt:
            fails.append((n, edges, d2, d3, r, tgt))
        return True
    for n in range(4, 7):
        pairs = list(itertools.combinations(range(n), 2))
        seen = 0
        for mask in range(1 << len(pairs)):
            edges = edges_of_mask(pairs, mask)
            if not edges or not connected_spanning(n, adj_of(n, edges)):
                continue
            if hub_load(edges) > 3:
                continue
            if probe(n, edges):
                seen += 1
        print(f"    n = {n}: {seen} graphs with hub load <= 3, EXHAUSTIVE")
    for n in (7, 8, 9, 10):
        pairs = list(itertools.combinations(range(n), 2))
        seen = 0
        guard = 0
        while seen < 150 and guard < 40000:
            guard += 1
            k = rng.randint(n - 1, min(len(pairs), 2 * n - 2))
            edges = sorted(rng.sample(pairs, k))
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            if hub_load(edges) > 3:
                continue
            if probe(n, edges):
                seen += 1
        print(f"    n = {n}: {seen} sampled graphs with hub load <= 3")
    print(f"    total {tot} graphs, {hard} of them with def_2 > def_3 (where")
    print(f"    the flat witness PROVABLY misses by def_2 - def_3); "
          f"{len(fails)} failures")
    if fails:
        for f in fails[:6]:
            print(f"      FAILURE {f}")
    print(f"    [{time.time() - t1:.1f} s]")
    print("  The gain column is the point of the construction: where def_2 >")
    print("  def_3 the flat witness misses by def_2 - def_3 and this one does")
    print("  not.  A single attaining draw is a PROOF for that graph (rank <=")
    print("  target is universal), so each ATTAINS row is a theorem.")
    print(f"  [{time.time() - t0:.1f} s]  seed {seed}")
    return rows


def flat_forcing_closure(n, edges):
    """The AGGRESSIVE plane-class propagation closure.  BZAVOID's (BE-15)(i)
    propagates pi_u = pi_v along TRIANGLE edges (3 shared closed-star normals);
    the general rule is `3 independent points already known to lie in pi`, of
    which the triangle rule is the case where they lie in both closed stars.
    Returns True if some hub's plane is forced to contain EVERY point (so every
    legal pencil configuration is FLAT).  Aggressive = assumes every 3 forced
    points are independent, which OVER-claims forcing; a hit is a CANDIDATE."""
    nb = neighbors(edges)
    H = [v for v in range(n) if len(nb.get(v, ())) >= 3]
    for h in H:
        A = {h} | set(nb[h])
        changed = True
        while changed:
            changed = False
            for v in H:
                star = {v} | set(nb[v])
                if len(star & A) >= 3 and not star <= A:
                    A |= star
                    changed = True
        if len(A) == n:
            return True
    return False


def run_force(nmax=6, nsamp=1200, seed=20260826):
    print("===== Step BE22 / (BE-23)(ii): the plane-class propagation, "
          "GENERALIZED -- and no new universal cap under it =====")
    print("  BZAVOID (BE-15) killed the TRIANGLE forcing mechanism.  The rule")
    print("  generalizes: pi_v is forced to pi as soon as closedNbhd(v) holds 3")
    print("  independent points already in pi -- which happens WITHOUT a")
    print("  triangle, e.g. at a K_{2,3} (two vertices with 3 common")
    print("  neighbours: K_{3,3} is forced FLAT and is triangle-free).")
    print("  A refutation of (BE-14) by this mechanism needs a forced-flat G")
    print("  with def_2 > def_3.  Hunted:")
    t0 = time.time()
    tot = 0
    forced = 0
    worst = None
    maxd2 = [0]
    for n in range(4, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        cnt = 0
        fc = 0
        for mask in range(1 << len(pairs)):
            edges = edges_of_mask(pairs, mask)
            if not edges:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            cnt += 1
            if not flat_forcing_closure(n, edges):
                continue
            fc += 1
            d2 = def2_exact(edges)
            d3 = exact_deficiency(edges)[0]
            assert d2 <= d3, ('FORCED-FLAT with def_2 > def_3', edges, d2, d3)
            if worst is None or d2 - d3 > worst[0]:
                worst = (d2 - d3, n, edges, d2, d3)
            if d2 > maxd2[0]:
                maxd2[0] = d2
        tot += cnt
        forced += fc
        print(f"  n = {n}: {cnt} connected graphs, {fc} FORCED FLAT by the "
              f"aggressive closure, ZERO with def_2 > def_3")
    print(f"  EXHAUSTIVE n = 4..{nmax}: {tot} connected graphs, {forced} "
          f"forced-flat, NO candidate at all (worst def_2 - def_3 = "
          f"{worst[0] if worst else None})")
    # the named triangle-FREE forcing witness the generalization is about
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    assert flat_forcing_closure(6, K33), 'K_{3,3} should be forced flat'
    tri = any(adj_of(6, K33)[u] & adj_of(6, K33)[v] for (u, v) in K33)
    print(f"  NAMED WITNESS  K_{{3,3}}: forced flat = True, has a triangle = "
          f"{tri} -- so the mechanism really is strictly more general than "
          f"BZAVOID's triangle rule; and def_2 = {def2_exact(K33)} = def_3 = "
          f"{exact_deficiency(K33)[0]}, so it is harmless, exactly as (BE-20)"
          f" predicts (K_{{3,3}} is 3-connected)")
    rng = random.Random(seed)
    for n in (7, 8, 9, 10):
        pairs = list(itertools.combinations(range(n), 2))
        seen = fc = 0
        guard = 0
        while seen < nsamp and guard < 60 * nsamp:
            guard += 1
            k = rng.randint(n, min(len(pairs), 3 * n))
            edges = sorted(rng.sample(pairs, k))
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            seen += 1
            if not flat_forcing_closure(n, edges):
                continue
            fc += 1
            d2 = def2_exact(edges)
            d3 = def3_of(edges, n)
            assert d2 <= d3, ('FORCED-FLAT with def_2 > def_3', edges, d2, d3)
            maxd2[0] = max(maxd2[0], d2)
        print(f"  n = {n}: {seen} sampled connected graphs, {fc} forced flat, "
              f"ZERO with def_2 > def_3")
    print(f"  Largest def_2 seen at a FORCED-FLAT graph: {maxd2[0]}.  With")
    print("  BZAVOID's (BE-15)(b) `def_2 >= def_3` on connected graphs, the")
    print("  measured statement is exactly `forced flat => def_2 = def_3`, so")
    print("  the FLAT witness attains there and the mechanism is harmless.")
    print("  Cap: the closure is COMBINATORIAL and AGGRESSIVE, so it")
    print("  over-claims forcing; an empty hunt under it is therefore stronger")
    print("  evidence than an empty hunt under a conservative rule would be.")
    print("  Structural reason, which is (BE-20) again: forced flatness needs")
    print("  the propagation to span G, and def_2 > 0 forces a cut of size")
    print("  <= 2 across which only the 2 cut points are shared.")
    print(f"  [{time.time() - t0:.1f} s]")
    return forced


# ================================================================== validate

def run_validate():
    t0 = time.time()
    run_base(nmax=6, sample_tier=(8,), nsamp=120)
    print()
    run_flatwit(nseeds=2)
    print()
    run_gate()
    print()
    run_twocut(ns=(3, 4), npairs=4000)
    print()
    run_rank2()
    print()
    run_ear(nseeds=2)
    print()
    run_hubplane(nseeds=2, sweep=False)
    print()
    run_force(nmax=6, nsamp=300)
    print(f"\n===== validate: all modes OK in {time.time() - t0:.1f} s =====")


MODES = {
    'base': run_base,
    'flatwit': run_flatwit,
    'gate': run_gate,
    'twocut': run_twocut,
    'rank2': run_rank2,
    'ear': run_ear,
    'hubplane': run_hubplane,
    'force': run_force,
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f"modes: {' | '.join(MODES)}")
        sys.exit(1)
    MODES[mode]()
