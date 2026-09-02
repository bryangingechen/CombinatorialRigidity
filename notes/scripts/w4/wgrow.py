"""
Phase 39 W4 — direction WGROW: the seed condition (PAIR-5).

(PAIR-5) claims: every simple, 2EC, triangle-free graph whose closed hub-
neighbourhoods have <= 3 members, whose degree-2 vertices form an INDEPENDENT
set, and which carries a proper rigid subgraph, has a rigid `U` with
`3 <= |U| <= |V| - 2` and `|d_hub U| <= 2` (a SEED).  By (PAIR-3) that implies
(E-pair), hence (V) ((PAIR-6)), hence everything W4 needs short of (K-res).

RESULT (2026-09-02), both halves:

  * (PAIR-5) **as stated is REFUTED** — by `K_{2,3}` ((GROW-5)), which is in
    the class (its `C4` is a proper rigid subgraph) and whose only rigid
    proper vertex set is that `C4`, of size `|V| - 1`.  `K_{2,3}` is **not a
    residual** (a co-1 rigid set is exactly what a residual forbids), so (E)
    is untouched by this refutation.
  * the restriction (E-pair) actually consumes is a **THEOREM** ((GROW-4),
    the SEED DICHOTOMY): every class member has a seed **or** a co-1 rigid
    set.  A residual has no co-1 rigid set, so every residual with an
    independent degree-2 set carries a seed — which (PAIR-3) forbids.  Hence
    **(E-pair) is a THEOREM**, and with (PAIR-6) so is (V).

The engine is a change of carrier ((GROW-1)/(GROW-2)): a class member is the
partial subdivision of its hub multigraph `M`, and both the deficiency and the
hub-boundary are functions of `M` alone.  Write `Lambda` for the un-subdivided
M-edges and give an M-edge WEIGHT 5 when it is a `Lambda`-edge and 4 when it
is subdivided; then for a partition `Q` of the hubs into `k` parts

    exc(Q) := 5*a + 4*b - 6*(k-1) = 6 + a + 2*sum_i (c(X_i) - 3)

(`a`/`b` the crossing Lambda-/subdivided edges, `c(X)` the M-edges leaving
`X`), and `G` is RIGID iff `exc(Q) >= 0` for every `Q`.  The finest partition
gives back (PAIR-1): `exc(finest) = f(V(G)) = 6 + e0 + 2*sigma`.

Run:
    python3 notes/scripts/w4/wgrow.py --validate  # (GROW-1)-(GROW-3) + the readings
    python3 notes/scripts/w4/wgrow.py --dich      # (GROW-4): the seed dichotomy
    python3 notes/scripts/w4/wgrow.py --k23       # (GROW-5): (PAIR-5) as stated is FALSE
    python3 notes/scripts/w4/wgrow.py --pool      # denominator disclosure
"""
import os
import random
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of, neighbors, degrees, is_2ec
from nogood_subdiv import (is_rigid, is_simple, hub_set, hcard_ok, triangles,
                           rigid_vertex_sets, induced_edges, deficiency)
from saferes import treepack_deficiency
from widened import f_of, prime_pool, residuals
from gridcol import cubic_iso_classes
import wpair


# ---------------- the hub-multigraph carrier ((GROW-1)/(GROW-2)) ------------

def to_model(edges):
    """The HUB MODEL of a class member: `(hubs, medges)` where `medges` is the
    list of M-edges `(u, w, mid)` — `mid = None` for a `Lambda`-edge (weight 5)
    and the degree-2 vertex for a subdivided one (weight 4).

    Well defined exactly on the (PAIR-5) class: every degree-2 vertex has two
    HUB neighbours (its degree-2 set is independent), so every edge of `G` is
    either a hub-hub edge or half of a subdivided M-edge."""
    hubs, nb = hub_set(edges), neighbors(edges)
    deg = degrees(edges)
    med = []
    for u, w in edges:
        if u in hubs and w in hubs:
            med.append((u, w, None))
    for v in verts_of(edges):
        if v in hubs:
            continue
        assert deg[v] == 2, f"min degree 2 expected at {v}"
        a, b = sorted(nb[v], key=str)
        assert a in hubs and b in hubs, "degree-2 set is not independent"
        med.append((a, b, v))
    return hubs, med


def weight(m):
    return 5 if m[2] is None else 4


def U_of(hubs_A, med):
    """`U(A)`: the hub set `A` together with every degree-2 vertex both of
    whose neighbours are in `A`.  Every rigid `U` satisfies `U <= U(U ^ W)`
    with the SAME hub boundary ((GROW-2)), so the seed search may be run over
    hub subsets alone."""
    A = set(hubs_A)
    return A | {m[2] for m in med if m[2] is not None and m[0] in A and m[1] in A}


def c_of(A, med):
    """`c(A)`: M-edges with exactly one end in `A` (counted with multiplicity)."""
    A = set(A)
    return sum(1 for m in med if (m[0] in A) != (m[1] in A))


def lam_cut(A, med):
    """The `Lambda`-edges leaving `A`, and the OUTSIDE hubs they land on —
    the latter is `d_hub U(A)` ((PAIR-2)(i))."""
    A = set(A)
    cut = [m for m in med if m[2] is None and (m[0] in A) != (m[1] in A)]
    return len(cut), {m[0] if m[0] not in A else m[1] for m in cut}


def f_pred(A, med, deg):
    """(GROW-1) the LOCALIZED deficit identity:
        `f(U(A)) = 6 + e_Lambda(A) + 2*sigma_A - 2*c(A)`,
    with `e_Lambda(A)` the `Lambda`-edges inside `A` and
    `sigma_A = sum_{z in A} (deg z - 3)`.  (PAIR-1) is the case `A = W`."""
    A = set(A)
    e_lam = sum(1 for m in med if m[2] is None and m[0] in A and m[1] in A)
    sig = sum(deg[z] - 3 for z in A)
    return 6 + e_lam + 2 * sig - 2 * c_of(A, med)


def partitions(items):
    """Every set partition of `items` (restricted growth strings)."""
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for sub in partitions(rest):
        for i in range(len(sub)):
            yield sub[:i] + [[first] + sub[i]] + sub[i + 1:]
        yield [[first]] + sub


def excess(Q, med):
    """(GROW-2) `exc(Q) = 5a + 4b - 6(k-1)`, the partition-connectivity slack of
    the WEIGHTED hub multigraph.  `G[U(A)]` is rigid iff `exc >= 0` for every
    partition of `A`; `exc(finest) = f(U(A))`."""
    idx = {}
    for i, part in enumerate(Q):
        for z in part:
            idx[z] = i
    a = b = 0
    for m in med:
        if m[0] in idx and m[1] in idx and idx[m[0]] != idx[m[1]]:
            if m[2] is None:
                a += 1
            else:
                b += 1
    return 5 * a + 4 * b - 6 * (len(Q) - 1)


def min_excess(A, med, kmin=2):
    """`(exc, Q)` minimizing `exc` over partitions of `A` with `>= kmin` parts."""
    best = None
    for Q in partitions(sorted(A, key=str)):
        if len(Q) < kmin:
            continue
        e = excess(Q, med)
        if best is None or e < best[0]:
            best = (e, Q)
    return best


def rigid_by_partition(A, med):
    """`U(A)` rigid, decided on the hub multigraph alone ((GROW-2))."""
    if len(A) < 2:
        return False
    e, _ = min_excess(A, med, kmin=2)
    return e >= 0


# ---------------- seeds, co-1 sets, and the class predicate -----------------

def seeds(edges, med=None, hubs=None):
    """Every SEED found by the hub-subset search: a rigid `U` with
    `3 <= |U| <= |V| - 2` and `|d_hub U| <= 2`.  Complete by (GROW-2): a rigid
    `U` and `U(U ^ W)` have the same hub boundary, and `A != W` already forces
    `|U(A)| <= |V| - 2`."""
    if med is None:
        hubs, med = to_model(edges)
    V = verts_of(edges)
    out = []
    for r in range(1, len(hubs) + 1):
        for A in combinations(sorted(hubs, key=str), r):
            U = U_of(A, med)
            if len(U) < 3 or len(U) > len(V) - 2:
                continue
            if len(lam_cut(A, med)[1]) > 2:
                continue
            if is_rigid(induced_edges(edges, U), sorted(U, key=str)):
                out.append(tuple(sorted(U, key=str)))
    # the `A = W` stratum: `V` minus two or more degree-2 vertices (hub
    # boundary empty, so a seed as soon as it is rigid)
    mids = [m[2] for m in med if m[2] is not None]
    for r in range(2, len(mids) + 1):
        for drop in combinations(sorted(mids, key=str), r):
            U = set(V) - set(drop)
            if len(U) < 3:
                continue
            if is_rigid(induced_edges(edges, U), sorted(U, key=str)):
                out.append(tuple(sorted(U, key=str)))
        if out:
            break
    return out


def co1_rigid(edges):
    """The co-1 rigid sets `V - {x}`.  Only `x` of degree 2 can give one: a
    hub's removal leaves a degree-1 vertex, which (R1) forbids in a rigid set."""
    V, deg = verts_of(edges), degrees(edges)
    out = []
    for x in V:
        U = [v for v in V if v != x]
        if is_rigid(induced_edges(edges, U), sorted(U, key=str)):
            out.append(x)
            assert deg[x] == 2, "(R1): a co-1 rigid set can only drop a degree-2 vertex"
    return out


def class_ok(edges):
    """The (PAIR-5) class: simple, min degree >= 2, 2EC, triangle-free, `hcard`,
    degree-2 set independent.  (Feasibility is then FREE by the landed
    sufficient L6b — `hcard` + triangle-free.)  The `carries a proper rigid
    subgraph` conjunct is tested separately."""
    if not is_simple(edges):
        return False
    V, deg = verts_of(edges), degrees(edges)
    if len(V) < 3 or any(deg[v] < 2 for v in V) or not is_2ec(edges):
        return False
    return (wpair.indep_deg2(edges) and not triangles(edges) and hcard_ok(edges)
            and bool(hub_set(edges)))


def has_proper_rigid(edges):
    """`G` carries a proper rigid subgraph: some rigid vertex set `U` with
    `2 <= |U| < |V|` (`IsProperRigidSubgraph` asks `V(H) subsetneq V(G)` and
    `2 <= |V(H)|`, `Deficiency.lean:483`, and `G[V(H)] >= H` is rigid too)."""
    V = verts_of(edges)
    if co1_rigid(edges):
        return True
    hubs, med = to_model(edges)
    for r in range(2, len(hubs) + 1):
        for A in combinations(sorted(hubs, key=str), r):
            U = U_of(A, med)
            if len(U) >= len(V):
                continue
            if is_rigid(induced_edges(edges, U), sorted(U, key=str)):
                return True
    return False


# ---------------- generators -----------------------------------------------

def build(base, sub):
    """`G` from a hub multigraph `base` (list of hub pairs) and the index set
    `sub` of edges to subdivide.  `wpair.subdivide` is the canonical device."""
    return wpair.subdivide(base, set(sub))


def lam_valid(base, sub):
    """The un-subdivided edges must form a `Lambda` of max degree <= 2 with no
    `C3` and no edge parallel to another M-edge (both would make `G` carry a
    triangle, and a parallel `Lambda` pair would make it non-simple)."""
    lam = [e for i, e in enumerate(base) if i not in sub]
    d = {}
    seen = set()
    for u, w in lam:
        if frozenset((u, w)) in seen:
            return False
        seen.add(frozenset((u, w)))
        d[u] = d.get(u, 0) + 1
        d[w] = d.get(w, 0) + 1
    if any(v > 2 for v in d.values()):
        return False
    for i, e in enumerate(base):
        if i in sub and frozenset(e) in seen:
            return False
    return True


def ring_family(n, chords):
    """`Lambda` = the hub cycle `z0 ... z_{n-1}` (a `Lambda`-CYCLE of length
    `n`), plus `chords` as once-subdivided branches.  THIS is the configuration
    `wpair.py --hunt`'s pairing-model generator never built (its disclosed cap:
    no `Lambda`-cycle of length >= 7) and that (EL-4) leaves open."""
    base = [(f'z{i}', f'z{(i + 1) % n}') for i in range(n)]
    sub = set()
    for (i, j) in chords:
        base.append((f'z{i}', f'z{j}'))
        sub.add(len(base) - 1)
    return base, sub


def ring_models(rng, count, nmin=7, nmax=13):
    """Random members of the `Lambda`-cycle family: every hub must land on at
    least one chord (min degree 3)."""
    out = []
    for _ in range(count):
        n = rng.randint(nmin, nmax)
        need = list(range(n))
        rng.shuffle(need)
        chords, covered = [], set()
        while len(covered) < n:
            i = next(x for x in need if x not in covered)
            j = rng.randrange(n)
            d = min((i - j) % n, (j - i) % n)
            if d < 2:
                continue
            chords.append((i, j))
            covered |= {i, j}
        out.append(ring_family(n, chords))
    return out


def cubic_models(h):
    """Every connected loopless CUBIC multigraph on `h` hubs (one per iso class,
    `gridcol.cubic_iso_classes`) crossed with every valid `Lambda`."""
    out = []
    for g in cubic_iso_classes(h):
        base = [(f'z{u}', f'z{w}') for (u, w) in g]
        for mask in range(1 << len(base)):
            sub = {i for i in range(len(base)) if mask >> i & 1}
            if lam_valid(base, sub):
                out.append((base, sub))
    return out


def random_models(rng, count, hmin=4, hmax=9):
    """Random min-degree-3 hub multigraphs (`wpair.random_base`) with a random
    valid `Lambda`."""
    out = []
    for _ in range(count):
        h = rng.randint(hmin, hmax)
        base = wpair.random_base(rng, h, extra=rng.choice((0, 0, 1)))
        forced = wpair.forced_subdivisions(base)
        free = [i for i in range(len(base)) if i not in forced]
        rng.shuffle(free)
        sub = set(forced) | {i for i in free if rng.random() < rng.choice((0.4, 0.6, 0.8))}
        if lam_valid(base, sub):
            out.append((base, sub))
    return out


# ---------------- --validate ------------------------------------------------

def validate():
    print("  seed 20260902 (`random.Random`); set generators are sorted before "
          "printing, so no `PYTHONHASHSEED` pin is needed")
    rng = random.Random(20260902)
    models = (cubic_models(2) + cubic_models(4) + cubic_models(6)
              + ring_models(rng, 60) + random_models(rng, 400))
    live = []
    for base, sub in models:
        E = build(base, sub)
        if class_ok(E):
            live.append(E)
    print(f"  class members generated: {len(live)} (from {len(models)} hub models)")

    print("  (GROW-1) the LOCALIZED deficit identity "
          "`f(U(A)) = 6 + e_Lambda(A) + 2*sigma_A - 2*c(A)`:")
    tested = 0
    for E in live:
        hubs, med = to_model(E)
        deg = degrees(E)
        for r in range(1, len(hubs) + 1):
            for A in combinations(sorted(hubs, key=str), r):
                assert f_of(E, U_of(A, med)) == f_pred(A, med, deg), (sorted(E), A)
                tested += 1
        assert f_pred(hubs, med, deg) == f_of(E), "A = W must give back (PAIR-1)"
    print(f"           {tested} hub subsets over {len(live)} class members, "
          f"0 mismatches (and `A = W` gives back (PAIR-1))")

    print("  (GROW-2) the HUB-MULTIGRAPH criterion — `U(A)` rigid iff the weighted "
          "hub\n           multigraph is 6-partition-connected on `A` "
          "(5 per `Lambda`-edge, 4 per subdivided):")
    tested = agree = 0
    for E in live:
        hubs, med = to_model(E)
        if len(hubs) > 7:
            continue
        for r in range(2, len(hubs) + 1):
            for A in combinations(sorted(hubs, key=str), r):
                U = sorted(U_of(A, med), key=str)
                ie = induced_edges(E, U)
                lhs = is_rigid(ie, U)
                assert lhs == (treepack_deficiency(ie, U) == 0), "oracles disagree"
                assert lhs == rigid_by_partition(A, med), (sorted(E), A)
                tested += 1
                agree += 1
    print(f"           {tested} hub subsets, {agree} agreements, 0 mismatches "
          f"(both landed oracles)")

    print("  (GROW-2c) the CO-1 stratum — `V(G) - {x}` at a degree-2 vertex `x` is the\n"
          "            partial subdivision of `M - e_x`, so (GROW-2) decides it too:")
    tested = rigidcnt = 0
    for E in live:
        hubs, med = to_model(E)
        if len(hubs) > 7:
            continue
        V = verts_of(E)
        for m in med:
            if m[2] is None:
                continue
            U = sorted([v for v in V if v != m[2]], key=str)
            lhs = is_rigid(induced_edges(E, U), U)
            rest = [x for x in med if x is not m]
            e, _ = min_excess(hubs, rest, kmin=2) if len(hubs) >= 2 else (0, None)
            assert lhs == (e >= 0), (sorted(E), m)
            tested += 1
            rigidcnt += lhs
    print(f"            {tested} co-1 candidates, {rigidcnt} rigid, 0 mismatches")

    print("  (GROW-2b) HUB-CLOSURE — every rigid `U` has `U <= U(U ^ W)`, `U(U ^ W)` is "
          "rigid,\n            and the two have the SAME hub boundary:")
    tested = 0
    for E in live:
        hubs, med = to_model(E)
        _, br = wpair.branch_decomposition(E)
        if br is None or len(br) > 16:
            continue
        for U in rigid_vertex_sets(E):
            A = set(U) & hubs
            UA = U_of(A, med)
            assert set(U) <= UA, (sorted(E), U)
            assert is_rigid(induced_edges(E, sorted(UA, key=str)), sorted(UA, key=str))
            assert wpair.hub_boundary(E, U) == wpair.hub_boundary(E, sorted(UA, key=str))
            assert wpair.hub_boundary(E, U) == lam_cut(A, med)[1]
            tested += 1
    print(f"            {tested} rigid sets from the branch enumeration, 0 mismatches")

    print("  (GROW-3) every part of a MINIMUM-EXCESS (`k >= 2`) partition of the hubs "
          "induces a\n           rigid `U(X)` — the refinement step of (GROW-4):")
    tested = parts = 0
    for E in live:
        hubs, med = to_model(E)
        if len(hubs) > 7:
            continue
        e, Q = min_excess(hubs, med, kmin=2)
        for X in Q:
            assert rigid_by_partition(X, med) or len(X) == 1, (sorted(E), X)
            parts += 1
        assert e == 6 + sum(1 for m in med if m[2] is None
                            and _cross(m, Q)) + 2 * sum(c_of(X, med) - 3 for X in Q), \
            "the `exc = 6 + a + 2*sum(c - 3)` rewriting"
        tested += 1
    print(f"           {tested} class members, {parts} parts, 0 mismatches "
          f"(and the `exc = 6 + a + 2*sum_i (c(X_i) - 3)` rewriting holds)")

    readings()


def _cross(m, Q):
    idx = {}
    for i, part in enumerate(Q):
        for z in part:
            idx[z] = i
    return idx[m[0]] != idx[m[1]]


def readings():
    """The coordinator's readings (2) and (3), tested (`RESEARCH-ARC.md` §7)."""
    print("  READING (2) — the monotone `|d_hub|` invariant (seed 61): CONFIRMED for "
          "the two\n              (PAIR-3) moves, and REFUTED for ear absorption in "
          "general.")
    rng = random.Random(61)          # seed 61, printed by the header line above
    grew = held = 0
    for base, sub in random_models(rng, 300) + ring_models(rng, 40):
        E = build(base, sub)
        if not class_ok(E):
            continue
        hubs, med = to_model(E)
        nb = neighbors(E)
        for r in range(2, min(len(hubs), 6) + 1):
            for A in combinations(sorted(hubs, key=str), r):
                if not rigid_by_partition(A, med):
                    continue
                U = U_of(A, med)
                hb0 = len(lam_cut(A, med)[1])
                for x in set(verts_of(E)) - U:
                    if x not in hubs:
                        continue
                    two_in_U = [y for y in nb[x] if y in U]
                    A2 = set(A) | {x}
                    hb1 = len(lam_cut(A2, med)[1])
                    if len(two_in_U) >= 2:          # (PAIR-3)'s ear `j = 1`
                        assert hb1 <= hb0, "reading (2) broke at an ear `j = 1`"
                        held += 1
                    elif rigid_by_partition(A2, med) and hb1 > hb0:
                        grew += 1                   # a LONGER ear: `j = 3`
    print(f"              {held} `j = 1` absorptions, all non-increasing; "
          f"{grew} absorptions through\n              TWO SUBDIVIDED branches "
          f"(an ear with `j = 3`) that STRICTLY GROW the hub boundary")

    print("  READING (3) — *Step PR5*'s `<= 2k - 1` ear count and its attachment "
          "convention:")
    for k in range(1, 7):
        direct = 2 * k - 1
        one = 2 * k
        both = 2 * k + 1
        ok = [n for n, j in (('direct', direct), ('one-subdivided', one),
                             ('both-subdivided', both)) if j <= 5]
        print(f"              k = {k} consecutive hubs: j = {direct} / {one} / {both} "
              f"interior vertices; Ear-Lemma-admissible: {', '.join(ok) or 'NONE'}")
    print("              so one ear absorbs at most THREE consecutive hubs (two if "
          "either\n              attachment runs through a subdivided branch) — "
          "reading (3) CONFIRMED")


# ---------------- --dich ----------------------------------------------------

def dichotomy():
    print("  seed 20260903 (`random.Random`)")
    rng = random.Random(20260903)
    models = (cubic_models(2) + cubic_models(4) + cubic_models(6)
              + ring_models(rng, 220, nmin=7, nmax=13)
              + random_models(rng, 900))
    print(f"  (GROW-4) THE SEED DICHOTOMY — every class member has a SEED or a CO-1 "
          f"rigid set.\n           Sweeping {len(models)} hub models:")
    stats = {'seed': 0, 'co1-only': 0, 'both': 0, 'NEITHER': 0}
    lam_cycles = seedless = 0
    vmax = hmax = fmax = 0
    for base, sub in models:
        E = build(base, sub)
        if not class_ok(E):
            continue
        hubs, med = to_model(E)
        if len(hubs) > 10:
            continue
        s = seeds(E, med, hubs)
        c = co1_rigid(E)
        if s and c:
            stats['both'] += 1
        elif s:
            stats['seed'] += 1
        elif c:
            stats['co1-only'] += 1
            seedless += 1
            print(f"           SEEDLESS class member (co-1 only): |V| = "
                  f"{len(verts_of(E))}, f = {f_of(E)}, hubs = {len(hubs)}")
        else:
            stats['NEITHER'] += 1
            print(f"           *** DICHOTOMY VIOLATED *** {sorted(E)}")
        vmax, hmax, fmax = (max(vmax, len(verts_of(E))), max(hmax, len(hubs)),
                            max(fmax, f_of(E)))
        for comp in wpair.lambda_components(E):
            if len(comp) >= 7 and all(sum(1 for m in med if m[2] is None
                                          and z in (m[0], m[1])) == 2 for z in comp):
                lam_cycles += 1
                break
    print(f"           {stats}")
    print(f"           class members carrying a `Lambda`-CYCLE of length >= 7 "
          f"(the configuration\n           (EL-4) leaves open and `wpair.py --hunt` "
          f"could not build): {lam_cycles}")
    print(f"           seedless members: {seedless}; every one of them carries a "
          f"co-1 rigid set,\n           so NONE of them is a residual")
    print(f"           CAP, disclosed: |V| <= {vmax}, hubs <= {hmax}, "
          f"f(V(G)) <= {fmax} over the sweep")
    assert stats['NEITHER'] == 0, "(GROW-4) refuted"

    print("  the residual consequence: a residual has NO co-1 rigid set, so by "
          "(GROW-4) it has a\n  SEED, which (PAIR-3) forbids — hence NO residual has "
          "an independent degree-2 set,\n  i.e. **(E-pair) is a THEOREM**.")


# ---------------- --k23 -----------------------------------------------------

def k23():
    E = wpair.subdivide([('z0', 'z1'), ('z0', 'z1'), ('z0', 'z1')], {0, 1, 2})
    V = verts_of(E)
    print(f"  (GROW-5) `K_{{2,3}}` = {sorted(E)}")
    print(f"           |V| = {len(V)}, |E| = {len(E)}, f = {f_of(E)} "
          f"(= 6 + e0 + 2*sigma = 6 + 0 + 0)")
    assert class_ok(E), "K_{2,3} must be in the (PAIR-5) class"
    print("           in the class: simple, 2EC, triangle-free, `hcard`, degree-2 set "
          "independent")
    c1 = co1_rigid(E)
    assert c1, "K_{2,3} must carry a co-1 rigid set"
    print(f"           carries a proper rigid subgraph: the `C4` `V - {{{c1[0]}}}` "
          f"(a cycle of length 4,\n           rigid by `isKDof_zero_of_cycle`), of size "
          f"{len(V) - 1} = |V| - 1")
    hubs, med = to_model(E)
    print("           every vertex set of size 3 (= |V| - 2), and its deficiency:")
    for U in combinations(sorted(V, key=str), 3):
        ie = induced_edges(E, U)
        print(f"             {U}: |E| = {len(ie)}, f = {f_of(E, U)}, "
              f"def = {deficiency(ie, list(U))}")
    assert not seeds(E, med, hubs), "K_{2,3} must have NO seed"
    print("           NO SEED — so **(PAIR-5) AS STATED IS FALSE**.  `K_{2,3}` is NOT a "
          "residual\n           (a residual forbids exactly the co-1 rigid set that "
          "saves it), so (E) is untouched.")

    print("  the uniqueness sweep (seed 23) — is `K_{2,3}` the ONLY seedless class "
          "member?")
    rng = random.Random(23)
    models = (cubic_models(2) + cubic_models(4) + cubic_models(6)
              + ring_models(rng, 120) + random_models(rng, 700))
    found = []
    for base, sub in models:
        F = build(base, sub)
        if not class_ok(F):
            continue
        hubs, med = to_model(F)
        if len(hubs) > 10:
            continue
        if not seeds(F, med, hubs):
            found.append((len(verts_of(F)), len(hub_set(F)), f_of(F)))
    print(f"           {len(found)} seedless members over the sweep; "
          f"(|V|, hubs, f) multiset: {sorted(set(found))}")
    print("           consistent with the derivation: seedlessness forces "
          "`f(V(G)) <= 7`, hence\n           `e0 + 2*sigma <= 1`, hence a cubic hub "
          "multigraph with `e0 <= 1` — and every hub\n           with `deg = 3`, "
          "`lambda = 0` then yields the seed `U(W - {z})`, leaving `h = 2`.")


# ---------------- --pool ----------------------------------------------------

def pool():
    res = [E for E, _ in residuals(prime_pool())]
    ind = [E for E in res if wpair.indep_deg2(E)]
    print(f"  `saferes.py --prime`'s pool: {len(res)} residual inhabitants, of which "
          f"{len(ind)}\n  have an independent degree-2 set.")
    print(f"  Honest denominator for a (PAIR-5) counterexample search over that pool: "
          f"**{len(ind)}, not {len(res)}** — the pool decides nothing, exactly as "
          f"`wpair.py --pool` reported.")
    print("  The DENOMINATOR THAT MATTERS is (GROW-4)'s: the dichotomy is a THEOREM, "
          "proved on the\n  hub multigraph, so no sweep is load-bearing for it; "
          "`--dich`'s sweep is a CHECK whose cap\n  it discloses in its own last line "
          "(`<= 10` hubs, from the `2^hubs` seed enumeration).")


if __name__ == '__main__':
    args = sys.argv[1:]
    if '--validate' in args:
        validate()
    if '--dich' in args:
        dichotomy()
    if '--k23' in args:
        k23()
    if '--pool' in args:
        pool()
    if not args:
        print(__doc__)
