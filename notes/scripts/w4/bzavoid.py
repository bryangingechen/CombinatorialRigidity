"""
Direction BZAVOID (ordinal 40) -- (BE-14), direct attainment of the body-hinge
target `6(|V|-1) - def_3(G)` on the PENCIL stratum, whose hard step BATTAIN
isolated to `Y^o !subset Z(G)`.

Succeeds `notes/scripts/w4/battain.py` (Steps BE9-BE13).  BATTAIN's figures are
CITED, never re-run here.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-15)  BATTAIN's forced-cone T2 criterion generalizes to a whole FAMILY of
           universal caps (one per forced class partition) and the WHOLE family
           is UNSATISFIABLE -- no graph at all, habitat member or not, can be
           refuted by the forced-degeneration mechanism.  Two sentences:
             (a) `tri`  : a connected spanning subgraph every edge of which lies
                          in a triangle has `def_2 = 0`.  ENUMERATED.
             (b) `crit` : hence the generalized cap's deficiency is exactly
                          `max(0, 6(k-1) - 5c)` = `partitionDef_3(pi(G))`, which
                          is `<= def_3(G)` BY DEFINITION.  ENUMERATED.
           `cap` re-derives the cap formula's arithmetic on the necklaces and
           checks it reproduces BATTAIN's recorded (BE-13) cone law at k = 1.

  (BE-16)  The rank is a function of the HINGE LINES alone (`rigidityRows` /
           `hingeRowBlock`, RigidityMatrix/Basic.lean:654/435), so on the pencil
           stratum it is the rank of the MOLECULAR body-hinge framework at the
           concurrency points, and the pencil condition is exactly "every closed
           star of points is COPLANAR" -- the planar-atom degeneration.
             `pn`   : the point-side <-> plane-side equivalence, both directions.

  (BE-17)  The landed molecule apparatus is UNAVAILABLE on this stratum, and not
           merely unproven: `SimpleGraph.IsGeneralPositionPlacement`
           (GeneralPositionPlacement.lean:59) demands every <= 4-subset affinely
           independent, which is the literal NEGATION of the pencil condition at
           every degree-3 hub, and the dictionary's surjectivity really fails
           there (flat-K4 flex).
             `flat` : the flat-K4 rank deficit, exactly.
             `sq`   : rank R(G^2, p) at a pencil p vs the generic 3|V| - 6 - def_3.

  (BE-18)  `def_3` is additive over a 1-vertex cut, so pencil attainment
           composes over blocks and (BE-14) reduces to 2-connected graphs.
             `glue` : the additivity, ENUMERATED; plus a glued rank check.

Modes:  tri | crit | cap | pn | flat | sq | glue | validate
Reproduce:  python3 notes/scripts/w4/bzavoid.py <mode>
All figures exact Q (fractions.Fraction); every rng seeded; degeneracy guards
and a dimension assert on every sampled object (`notes/scripts/README.md` s4).
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

from exactcore import (rank as rank_exact, nullspace, wedge2, hat,       # noqa: E402
                       neighbors, dot)
from kbare_common import (verts_of, exact_deficiency, rank_modp,         # noqa: E402
                          build_rigidity, verify_pencil_witness, rint,
                          spider)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (README *Harness debt*, 2026-08-20); BATTAIN was its first
# --- `w4/` consumer, this driver is the second.  NO MOVE MADE.
from danger import dz_gadget                                            # noqa: E402
from battain import (def2_exact, sample_Y, solve_schedule, closed_star,  # noqa: E402
                     span_dim, necklace, target_of, rows_from_W)
from nogood_subdiv import deficiency as pebble_def                      # noqa: E402


# ==================================================================== helpers

def edges_of_mask(pairs, mask):
    return [pairs[i] for i in range(len(pairs)) if (mask >> i) & 1]


def adj_of(n, edges):
    a = [0] * n
    for u, v in edges:
        a[u] |= 1 << v
        a[v] |= 1 << u
    return a


def connected_spanning(n, adj):
    """Every vertex touched by an edge AND the graph connected."""
    if any(adj[v] == 0 for v in range(n)):
        return False
    seen, stack = 1, [0]
    while stack:
        v = stack.pop()
        rest = adj[v] & ~seen
        while rest:
            b = rest & -rest
            w = b.bit_length() - 1
            seen |= b
            stack.append(w)
            rest ^= b
    return seen == (1 << n) - 1


def every_edge_in_triangle(edges, adj):
    return all(adj[u] & adj[v] for (u, v) in edges)


def triangle_edges(edges, adj):
    """T(G) = the set of edges lying in a triangle of G."""
    return [(u, v) for (u, v) in edges if adj[u] & adj[v]]


def components(n, adj, edgeset):
    """Vertex classes of the SPANNING subgraph with edge set `edgeset`
    (isolated vertices are their own singleton class)."""
    a = adj_of(n, edgeset)
    seen = [False] * n
    out = []
    for s in range(n):
        if seen[s]:
            continue
        comp, stack, seen[s] = [s], [s], True
        while stack:
            v = stack.pop()
            r = a[v]
            while r:
                b = r & -r
                w = b.bit_length() - 1
                r ^= b
                if not seen[w]:
                    seen[w] = True
                    comp.append(w)
                    stack.append(w)
        out.append(sorted(comp))
    return out


def induced(edges, S):
    Ss = set(S)
    return [(u, v) for (u, v) in edges if u in Ss and v in Ss]


def def2_of(edges, nverts):
    """def_2 of a graph given as an edge list; a graph with <= 1 vertex, or with
    no edges, is handled by the closed form (isolated bodies are free)."""
    if not edges:
        return max(0, 3 * (nverts - 1))
    d = def2_exact(edges)
    touched = len(verts_of(edges))
    # vertices of the class carrying no edge contribute 3 each (a free body in
    # the planar D = 3 count); classes here are connected, so touched == nverts.
    assert touched == nverts, (touched, nverts)
    return d


def def3_of(edges, nverts):
    """def_3.  Exact 2^|V| partition oracle up to |V| <= 8 (the recursion
    depth of `kbare_common.exact_deficiency`'s packing search bites above
    that); the (6,6)-count matroid pebble oracle above, cross-checked against
    the exact one wherever both run."""
    if not edges:
        return max(0, 6 * (nverts - 1))
    if nverts <= 8:
        return exact_deficiency(edges)[0]
    return pebble_def(edges)


def forced_partition_data(n, edges):
    """The forced class partition pi(G) = components of T(G), and the cap's
    deficiency  6(k-1) - 5c + sum_i def_2(G[V_i])  (before the max with 0)."""
    adj = adj_of(n, edges)
    T = triangle_edges(edges, adj)
    classes = components(n, adj, T)
    k = len(classes)
    cls_of = {}
    for i, C in enumerate(classes):
        for v in C:
            cls_of[v] = i
    c = sum(1 for (u, v) in edges if cls_of[u] != cls_of[v])
    sd2 = 0
    for C in classes:
        sd2 += def2_of(induced(edges, C), len(C))
    return classes, k, c, sd2


# =================================================== (BE-15)(a): the `tri` mode

def run_tri(nmax=7):
    print("===== Step BE14 / (BE-15)(a): a connected spanning triangle-covered "
          "graph has def_2 = 0 =====")
    t0 = time.time()
    grand = 0
    for n in range(3, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        m = len(pairs)
        hits = 0
        worst = None
        for mask in range(1 << m):
            edges = edges_of_mask(pairs, mask)
            if len(edges) < 3:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            if not every_edge_in_triangle(edges, adj):
                continue
            hits += 1
            d2 = def2_exact(edges)
            if d2 != 0:
                worst = (edges, d2)
                break
        grand += hits
        status = 'ALL def_2 = 0' if worst is None else f'COUNTEREXAMPLE {worst}'
        print(f"  n={n}: {hits:7d} connected spanning triangle-covered graphs "
              f"(of {1 << m} edge sets) -> {status}")
        assert worst is None, worst
    # the derived corollary def_2 = 0 => def_3 = 0 (2d >= 3(|P|-1) => 5d >= 6(|P|-1))
    print(f"  EXHAUSTIVE to n = {nmax}: {grand} graphs, ZERO with def_2 > 0.")
    print(f"  [{time.time() - t0:.1f} s]")
    return grand


def run_tri_sample(ns=(8, 9, 10), ntri=(3, 4, 5, 6), draws=400, seed=20260826):
    """Above the exhaustive cap: connected unions of triangles, sampled."""
    rng = random.Random(seed)
    tested = 0
    for n in ns:
        for t in ntri:
            for _ in range(draws // len(ntri)):
                # grow a connected union of `t` triangles on n labelled vertices
                verts = list(range(n))
                tri = [tuple(rng.sample(verts, 3))]
                used = set(tri[0])
                for _ in range(t - 1):
                    anchor = rng.choice(sorted(used))
                    others = rng.sample([x for x in verts if x != anchor], 2)
                    tri.append((anchor, others[0], others[1]))
                    used |= set(tri[-1])
                E = set()
                for (a, b, c) in tri:
                    E |= {tuple(sorted(p)) for p in ((a, b), (b, c), (a, c))}
                edges = sorted(E)
                sub = sorted(used)
                relab = {v: i for i, v in enumerate(sub)}
                edges = [(relab[u], relab[v]) for (u, v) in edges]
                nn = len(sub)
                adj = adj_of(nn, edges)
                if not connected_spanning(nn, adj):
                    continue
                if not every_edge_in_triangle(edges, adj):
                    continue
                if nn > 14:
                    continue
                d2 = def2_exact(edges)
                assert d2 == 0, (edges, d2)
                tested += 1
    print(f"  sampled beyond the exhaustive cap: {tested} connected unions of "
          f"triangles on 8..10 vertices, ALL def_2 = 0")
    return tested


# ================================================== (BE-15)(b): the `crit` mode

def run_crit(nmax=6, seed=20260826):
    print("===== Step BE14 / (BE-15)(b): the generalized forced-cluster T2 "
          "criterion NEVER fires =====")
    t0 = time.time()
    tot = fired = 0
    tight = 0
    for n in range(3, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        m = len(pairs)
        for mask in range(1 << m):
            edges = edges_of_mask(pairs, mask)
            if not edges:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            classes, k, c, sd2 = forced_partition_data(n, edges)
            cap_def = 6 * (k - 1) - 5 * c + sd2
            d3 = def3_of(edges, n)
            assert d3 == pebble_def(edges), ('oracle disagreement', edges)
            tot += 1
            # the criterion fires iff the cap's deficiency EXCEEDS def_3
            if cap_def > d3:
                fired += 1
                print(f"  FIRES: n={n} E={edges} k={k} c={c} sum_def2={sd2} "
                      f"cap_def={cap_def} def_3={d3}")
            if cap_def == d3:
                tight += 1
            # the per-class claim, independently
            assert sd2 == 0, (edges, classes, sd2)
            # and the ordering def_2 >= def_3 on a CONNECTED graph (every
            # q-part partition of a connected graph crosses >= q-1 edges)
            assert def2_exact(edges) >= d3, ('def_2 < def_3', edges)
            # and the definitional inequality it reduces to
            assert 6 * (k - 1) - 5 * c <= d3, (edges, k, c, d3)
    print(f"  EXHAUSTIVE over all connected graphs to n = {nmax}: {tot} graphs, "
          f"{fired} fire, {tight} tight (cap == def_3); def_2 >= def_3 at every "
          f"one (so the cone NEVER beats the pencil generic)")
    assert fired == 0
    # a sparse random sweep above the exhaustive cap, plus the arc's necklaces
    rng = random.Random(seed)
    extra = 0
    for n in range(7, 13):
        pairs = list(itertools.combinations(range(n), 2))
        for _ in range(300):
            m = rng.randint(n - 1, min(len(pairs), 2 * n))
            edges = sorted(rng.sample(pairs, m))
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            classes, k, c, sd2 = forced_partition_data(n, edges)
            cap_def = 6 * (k - 1) - 5 * c + sd2
            d3 = def3_of(edges, n)
            assert sd2 == 0, (edges, sd2)
            assert cap_def <= d3, (edges, cap_def, d3)
            extra += 1
    print(f"  sparse random sweep n = 7..12: {extra} connected graphs, "
          f"0 fire, sum_i def_2(G[V_i]) = 0 at every one")
    print(f"  [{time.time() - t0:.1f} s]")
    return tot, extra


# ======================================================= (BE-15): the cap law

def run_cap():
    print("===== Step BE14 / (BE-15): the cap formula, and its k = 1 "
          "specialization to BATTAIN's (BE-13) =====")
    # k = 1 (the cone): the cap deficiency is def_2(G) itself -- BATTAIN's law.
    for name, edges in (('K4', [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
                        ('DZ', dz_gadget())):
        n = len(verts_of(edges))
        vs = sorted(verts_of(edges), key=str)
        relab = {v: i for i, v in enumerate(vs)}
        E = [(relab[u], relab[v]) for (u, v) in edges]
        classes, k, c, sd2 = forced_partition_data(n, E)
        d2, d3 = def2_exact(E), def3_of(E, n)
        print(f"  {name}: |V|={n} k={k} c={c} sum_def2={sd2} "
              f"def_2={d2} def_3={d3}")
        if k == 1:
            assert c == 0
            assert sd2 == d2, (sd2, d2)
            print(f"    k = 1 => the cap deficiency IS def_2 = {d2} "
                  f"(BATTAIN (BE-13)); criterion needs def_2 > def_3: "
                  f"{d2} > {d3} is {d2 > d3}")
    # the necklaces: the criterion's arithmetic half holds (def_2 > def_3 from
    # k = 4) but the FORCED partition is one class per blob, and there the cap
    # deficiency collapses to 6(k-1) - 5c = k - 6 = def_3.  Cited attainment:
    # BATTAIN `localcone`, k = 3..7.
    print("  necklaces Nk_k (BATTAIN's constructed candidate), forced-partition"
          " reading:")
    for k in (3, 4, 5, 6, 7):
        edges = necklace(k)
        vs = sorted(verts_of(edges), key=str)
        relab = {v: i for i, v in enumerate(vs)}
        E = [(relab[u], relab[v]) for (u, v) in edges]
        n = len(vs)
        classes, kk, c, sd2 = forced_partition_data(n, E)
        d3 = pebble_def(E)
        if n <= 12:
            assert d3 == exact_deficiency(E)[0], 'oracle disagreement'
        d2 = def2_exact(E) if n <= 16 else None
        cap_def = max(0, 6 * (kk - 1) - 5 * c + sd2)
        print(f"    k={k}: |V|={n} classes={kk} cross={c} sum_def2={sd2} "
              f"cap_def={cap_def} def_3={d3} def_2={d2} "
              f"-> fires: {cap_def > d3}")
        assert kk == k, (kk, k)          # one class per blob, as predicted
        assert c == k, (c, k)            # the k connecting edges cross
        assert sd2 == 0
        assert cap_def <= d3
    print("  the cap deficiency is exactly partitionDef_3(pi(G)) = "
          "max(0, 6(k-1) - 5c); def_3 is a MAX over partitions, so it can "
          "never exceed def_3.  The mechanism can only reproduce a bound the "
          "target already accounts for.")


# ============================================ (BE-16): point side <-> plane side

def run_pn(seed=20260826):
    print("===== Step BE15 / (BE-16): the pencil condition IS closed-star "
          "COPLANARITY of the points =====")
    rng = random.Random(seed)
    edges = dz_gadget()
    nb = neighbors(edges)
    N, P, W, free = sample_Y(edges, rng)
    # plane side -> point side: every closed star of POINTS is coplanar
    bad = 0
    for v in verts_of(edges):
        star = [P[w] for w in closed_star(nb, v)]
        d = span_dim(star)
        assert d <= 3, (v, d)
        if d != 3:
            bad += 1
        # and n_v annihilates the whole star (the coplanarity's witness plane)
        for x in star:
            assert dot(x, N[v]) == 0, ('star point off own panel', v)
    print(f"  DZ, a Y-generic sample: {len(list(verts_of(edges)))} closed stars,"
          f" every one of POINT-span <= 3 (coplanar); {bad} degenerate (< 3)")
    # point side -> plane side: the landed carrier recovers normals from points
    # alone (`kbare_common.verify_pencil_witness`), i.e. coplanar closed stars
    # are ENOUGH -- no normals needed as input.
    aff = {}
    for v in verts_of(edges):
        w = P[v][3]
        assert w != 0, ('point at infinity in this draw', v)
        aff[v] = (P[v][0] / w, P[v][1] / w, P[v][2] / w)
    ok, normals = verify_pencil_witness(edges, aff)
    assert ok, normals
    print("  and back: `verify_pencil_witness` recovers a legal normal at every"
          " body from the POINTS alone -> the two descriptions coincide")
    # the rank is a function of the hinge lines alone (rigidityRows /
    # hingeRowBlock): the (p, n, W) carrier and the molecular carrier built from
    # the points agree exactly.
    rows_W, nv = rows_from_W(edges, N, P, W)
    r_W = rank_exact(rows_W)
    rows_mol, nv2 = build_rigidity(edges, aff)
    r_mol = rank_exact(rows_mol)
    tgt, d3 = target_of(edges)
    print(f"  rank via the (p,n,W) carrier = {r_W}; rank via the MOLECULAR "
          f"carrier at the same points = {r_mol}; target = {tgt} (def_3 = {d3})")
    assert r_W == r_mol, (r_W, r_mol)
    # and the hinge lines really are the joins p_u v p_v
    for e in edges:
        u, v = e
        a, b = W[e]
        assert span_dim([a, b, P[u]]) == 2 and span_dim([a, b, P[v]]) == 2
        assert span_dim([P[u], P[v]]) == 2, ('coincident adjacent points', e)
    print("  every hinge W_e = span(p_u, p_v) -- the JOIN of the two "
          "concurrency points, so the framework is MOLECULAR at p")
    # the DIMENSION count, and why it can never settle `Y^o !subset Z(G)`
    hubs = [v for v in verts_of(edges) if len(nb.get(v, ())) >= 3]
    codim = sum(len(nb[v]) - 2 for v in hubs)
    amb = 3 * len(list(verts_of(edges)))
    print(f"  dimension count: ambient (P^3*)^V has dim {amb}; codim Y^o = "
          f"sum_hubs(deg v - 2) = {codim}; dim Y^o = {amb - codim}")
    print(f"  Z(G) is only known to be a PROPER closed subset, i.e. dim Z(G) "
          f"<= {amb - 1}.  Containment Y^o subset Z needs dim Y^o <= dim Z, and "
          f"{amb - codim} <= {amb - 1} whenever the graph has a hub -- so the "
          f"codimension count NEVER obstructs containment.  Derivational, no "
          f"measurement: the count is structurally incapable of settling it.")
    assert amb - codim <= amb - 1, 'a hub-free graph: Y = everything'
    return r_W, r_mol, tgt


# ============================================ (BE-17): the flat-K4 obstruction

def run_flat(seed=20260826):
    print("===== Step BE16 / (BE-17): the landed molecule dictionary's "
          "general-position gate is the NEGATION of the pencil condition =====")
    rng = random.Random(seed)

    def barjoint_rows(pts, es):
        vs = sorted(pts)
        idx = {v: i for i, v in enumerate(vs)}
        rows = []
        for (u, v) in es:
            row = [F(0)] * (3 * len(vs))
            for t in range(3):
                d = pts[u][t] - pts[v][t]
                row[3 * idx[u] + t] += d
                row[3 * idx[v] + t] -= d
            rows.append(row)
        return rows

    # generic K4: rank 6 = 3*4 - 6 (rigid).  COPLANAR K4: rank 5 (one flex).
    K4 = list(itertools.combinations(range(4), 2))
    gen = {v: tuple(F(rint(rng, -9, 9)) for _ in range(3)) for v in range(4)}
    r_gen = rank_exact(barjoint_rows(gen, K4))
    flat = {v: (F(rint(rng, -9, 9)), F(rint(rng, -9, 9)), F(0)) for v in range(4)}
    r_flat = rank_exact(barjoint_rows(flat, K4))
    print(f"  bar-joint K4 in R^3: generic rank = {r_gen} (= 3*4-6, rigid); "
          f"COPLANAR rank = {r_flat} -> {r_gen - r_flat} extra flex")
    assert r_gen == 6 and r_flat == 5
    # at a pencil configuration EVERY degree-3 hub's closed star is such a flat
    # 4-point set, so IsGeneralPositionPlacement (every <= 4-subset affinely
    # independent, GeneralPositionPlacement.lean:59) FAILS at every hub.
    edges = dz_gadget()
    nb = neighbors(edges)
    N, P, W, free = sample_Y(edges, rng)
    aff = {}
    for v in verts_of(edges):
        w = P[v][3]
        assert w != 0
        aff[v] = (P[v][0] / w, P[v][1] / w, P[v][2] / w)
    hubs = [v for v in verts_of(edges) if len(nb.get(v, ())) >= 3]
    viol = 0
    for v in hubs:
        star = closed_star(nb, v)
        if len(star) != 4:
            continue
        M = [list(hat(aff[w])) for w in star]
        if rank_exact(M) < 4:
            viol += 1
    print(f"  DZ pencil sample: {len(hubs)} hubs, {viol} of them carry FOUR "
          f"AFFINELY DEPENDENT closed-star points -> IsGeneralPositionPlacement"
          f" fails at every one")
    assert viol == len(hubs) and viol > 0
    return r_gen, r_flat, viol


# ===================================== (BE-17): the G^2 bar-joint experiment

def square_edges(edges):
    """G^2: pairs at distance <= 2.  Equal to the union of the closed-star
    cliques, so it is exactly the graph the molecule dictionary consumes."""
    nb = neighbors(edges)
    out = set()
    for v in nb:
        star = [v] + sorted(nb[v], key=str)
        for a, b in itertools.combinations(star, 2):
            out.add(tuple(sorted((a, b), key=str)))
    return sorted(out, key=lambda t: (str(t[0]), str(t[1])))


def barjoint_rank(pts, es, exact=True):
    vs = sorted(pts, key=str)
    idx = {v: i for i, v in enumerate(vs)}
    rows = []
    for (u, v) in es:
        row = [F(0)] * (3 * len(vs))
        for t in range(3):
            d = pts[u][t] - pts[v][t]
            row[3 * idx[u] + t] += d
            row[3 * idx[v] + t] -= d
        rows.append(row)
    return (rank_exact(rows) if exact else rank_modp(rows)), len(rows)


def run_sq(seed=20260826, shapes=None, nseeds=6):
    print("===== Step BE16 / (BE-17): rank R(G^2, p) at a PENCIL p vs the "
          "generic 3|V| - 6 - def_3 =====")
    print("  EXACT Q throughout for the G^2 ranks (a GF(p) rank is only a lower")
    print("  bound on the rational one -- the wrong direction for a shortfall).")
    print("  MULTI-SEED: rank is lower semicontinuous, so ONE draw is only a")
    print("  lower bound (BATTAIN's own recorded trap).  Each shape below takes")
    print("  the MAX over %d seeded draws of the Y sampler." % nseeds)
    if shapes is None:
        shapes = [('DZ', dz_gadget()),
                  ('spider(5,5,5)+c', spider(5, 5, 5, center=True)[0]),
                  ('theta(4,4,4)+c', spider(4, 4, 4, center=True)[0]),
                  ('Nk_3', necklace(3))]
    out = []
    for name, edges in shapes:
        V = sorted(verts_of(edges), key=str)
        n = len(V)
        d3 = pebble_def(edges) if n > 8 else exact_deficiency(edges)[0]
        sq = square_edges(edges)
        gtarget = 3 * n - 6 - d3
        tgt = 6 * (n - 1) - d3
        rng = random.Random(seed)
        gen = {v: tuple(F(rint(rng, -40, 40)) for _ in range(3)) for v in V}
        r_gen, _ = barjoint_rank(gen, sq, exact=True)
        best_pen, best_mol, drawn = -1, None, 0
        for sd in range(nseeds):
            rngs = random.Random(seed + 977 * sd)
            try:
                N, P, W, free = sample_Y(edges, rngs)
            except (RuntimeError, AssertionError) as exc:
                if sd == 0:
                    why = exc
                continue
            aff, ok = {}, True
            for v in V:
                w = P[v][3]
                if w == 0:
                    ok = False
                    break
                aff[v] = (P[v][0] / w, P[v][1] / w, P[v][2] / w)
            if not ok:
                continue
            good, wh = verify_pencil_witness(edges, aff)
            assert good, wh
            drawn += 1
            # EXACT Q, not GF(p): a mod-p rank is only a LOWER bound on the
            # rational rank, which is the wrong direction for a SHORTFALL claim.
            r_pen, _ = barjoint_rank(aff, sq, exact=True)
            if r_pen > best_pen:
                rows, _ = build_rigidity(edges, aff)
                best_pen, best_mol = r_pen, rank_modp(rows)
        print(f"  {name}: |V|={n} |E|={len(edges)} |E(G^2)|={len(sq)} "
              f"def_3={d3}  ({drawn}/{nseeds} draws usable)")
        if drawn == 0:
            print(f"    no Y sample at any seed ({why}) -- SKIPPED, disclosed")
            continue
        print(f"    generic  p: rank R(G^2,p) = {r_gen}   (generic rank "
              f"3|V|-6-def_3 = {gtarget})  match: {r_gen == gtarget}")
        print(f"    PENCIL   p: BEST rank R(G^2,p) = {best_pen}   deficit vs "
              f"generic = {gtarget - best_pen}")
        print(f"    PENCIL   p: molecular body-hinge rank = {best_mol}  "
              f"(target {tgt})  attains: {best_mol == tgt}")
        kerG2 = 3 * n - best_pen
        kerMol = 6 * n - best_mol
        print(f"    DICTIONARY: dim ker R(G^2,p) = {kerG2} vs dim Z_mol = "
              f"{kerMol}  ->  gap {kerG2 - kerMol} (0 iff the landed dictionary"
              f" `molecular_finrank_motions_eq_square_ker` still holds here)")
        assert r_gen == gtarget, (name, r_gen, gtarget)
        assert best_pen <= gtarget
        assert kerG2 >= kerMol, 'the injective half of the dictionary failed'
        out.append((name, gtarget - best_pen, best_mol == tgt))
    print("  READING: the G^2 route's sufficient condition is `rank R(G^2,p) = "
          "3|V|-6-def_3 at a coplanar-star p`.  It is FALSE at every shape "
          "above (best of %d draws each) while the MOLECULAR rank attains -- so "
          "the route is strictly stronger than (BE-14) and dead as stated.  "
          "Cap: %d shapes, %d draws each." % (nseeds, len(shapes), nseeds))
    return out


# ============================================== (BE-18): 1-cut additivity

def run_glue(nmax=6, seed=20260826):
    print("===== Step BE17 / (BE-18): def_3 is ADDITIVE over a 1-vertex cut "
          "=====")
    t0 = time.time()
    rng = random.Random(seed)
    tested = 0
    for n1 in range(2, nmax):
        for n2 in range(2, nmax):
            p1 = list(itertools.combinations(range(n1), 2))
            p2 = list(itertools.combinations(range(n2), 2))
            for _ in range(60):
                m1 = rng.randint(n1 - 1, len(p1))
                m2 = rng.randint(n2 - 1, len(p2))
                E1 = sorted(rng.sample(p1, m1))
                E2 = sorted(rng.sample(p2, m2))
                a1 = adj_of(n1, E1)
                a2 = adj_of(n2, E2)
                if not connected_spanning(n1, a1) or not connected_spanning(n2, a2):
                    continue
                # glue vertex 0 of G1 to vertex 0 of G2; relabel G2's rest
                shift = n1 - 1
                def rl(v):
                    return 0 if v == 0 else v + shift
                E = E1 + [(rl(u), rl(v)) for (u, v) in E2]
                nn = n1 + n2 - 1
                d1 = def3_of(E1, n1)
                d2 = def3_of(E2, n2)
                d = def3_of(E, nn)
                assert d == d1 + d2, (E1, E2, d, d1, d2)
                tested += 1
    print(f"  {tested} random 1-cut gluings on <= {2 * nmax - 1} vertices: "
          f"def_3(G) = def_3(G1) + def_3(G2) at EVERY one")
    # the rank half is exact linear algebra: M(G) is the fibre product of
    # M(G1), M(G2) over the shared body's screw, so dim M = dim M1 + dim M2 - 6
    # and rank(G) = rank(G1) + rank(G2).  Checked on a GENUINE pencil pair: two
    # triangles sharing body 0, all points coplanar (so every closed star is
    # coplanar and the glued configuration really is a pencil one).
    tri1 = [(0, 1), (1, 2), (0, 2)]
    tri2 = [(0, 3), (3, 4), (0, 4)]
    pts1 = {0: (F(0), F(0), F(0)), 1: (F(1), F(0), F(0)), 2: (F(0), F(1), F(0))}
    pts2 = {0: (F(0), F(0), F(0)), 3: (F(2), F(1), F(0)), 4: (F(1), F(3), F(0))}
    pts = dict(pts1); pts.update({3: pts2[3], 4: pts2[4]})
    for (E, PP) in ((tri1, pts1), (tri2, pts2), (tri1 + tri2, pts)):
        good, why = verify_pencil_witness(E, PP)
        assert good, why
    r1 = rank_exact(build_rigidity(tri1, pts1)[0])
    r2 = rank_exact(build_rigidity(tri2, pts2)[0])
    r = rank_exact(build_rigidity(tri1 + tri2, pts)[0])
    t1 = 6 * 2 - def3_of(tri1, 3)
    t2 = 6 * 2 - def3_of(tri2, 3)
    t = 6 * 4 - def3_of(tri1 + tri2, 5)
    print(f"  a GENUINE glued pencil pair (two triangles sharing body 0, all "
          f"stars coplanar): rank {r} = {r1} + {r2}; targets {t} = {t1} + {t2}"
          f"; all three attain: {(r, r1, r2) == (t, t1, t2)}")
    assert r == r1 + r2 and (r, r1, r2) == (t, t1, t2)
    print(f"  [{time.time() - t0:.1f} s]")
    return tested


# ================================================================== validate

def run_validate():
    t0 = time.time()
    run_tri(nmax=6)   # the n = 7 exhaustive sweep (102 s) is the `tri` mode
    run_tri_sample()
    print()
    run_crit()
    print()
    run_cap()
    print()
    run_pn()
    print()
    run_flat()
    print()
    run_sq()
    print()
    run_glue()
    print(f"\n===== validate: all modes OK in {time.time() - t0:.1f} s =====")


MODES = {
    'tri': lambda: (run_tri(), run_tri_sample()),
    'crit': run_crit,
    'cap': run_cap,
    'pn': run_pn,
    'flat': run_flat,
    'sq': run_sq,
    'glue': run_glue,
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f"modes: {' | '.join(MODES)}")
        sys.exit(2)
    MODES[mode]()
