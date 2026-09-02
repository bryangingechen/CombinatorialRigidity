"""
Phase 39 W4 — direction WPAIR: the gap (E-pair).

(E-pair) claims: every RESIDUAL `G` (simple, 2EC, `PencilNondegFeasible`,
`3 <= |V|`, a proper rigid subgraph, no co-1 rigid subgraph, no rigid
contraction that is Simple AND Feasible) carries TWO ADJACENT DEGREE-2
VERTICES.  That — and nothing more — is what the split arm consumes through
the landed `exists_adjacent_degree_two_pair_of_edgeBound`
(`ReducibleVertex.lean:1068`), so (E-pair) bypasses (E) entirely.

RESULT (2026-09-02): (E-pair) is **REDUCED to a named seed condition**, and
two strata of it are **PROVED**.

  * `--validate` checks the three mechanical claims of *Steps PR1-PR3*:
      (PAIR-1)  `f(V(G)) = 6 + e0 + 2*sigma` for EVERY simple graph of min
                degree >= 2 whose degree-2 vertices are independent, with
                `e0 = |E(G[hubs])|` and `sigma = sum_{hubs}(deg - 3)`.  So
                the negation of (E-pair) forces `f >= 6`, and (E-pair)
                follows from `f <= 5` — one unit WEAKER than (E)'s `f <= 4`.
      (PAIR-2)  at a rigid `U` with a simple contraction, `hcard(G/U)` holds
                IFF at most two outside vertices adjacent to `U` are hubs.
      (PAIR-3)  that hub-boundary count NEVER GROWS along the ear-`j=1` /
                ear-`j=2` growth of *Step EL4*'s chain, and the chain always
                lands on `good-contraction` / `co-1` / `spanning-C3`.
  * `--sub` is the proved stratum (PAIR-4): when the hubs are independent
    (`e0 = 0`, i.e. `G` is a full subdivision) EVERY rigid set has hub-
    boundary 0, so (PAIR-3) applies outright.  Hence a counterexample to
    (E-pair) needs `e0 >= 1` and `f(V(G)) >= 7`.
  * `--hunt` searches for a residual with an independent degree-2 set over
    partial subdivisions of min-degree-3 multigraphs, and tests the seed
    condition (PAIR-5) at every candidate.  Cap disclosed in the output.
  * `--vee` is job 3: (V)'s two `C4`-carrying residues both have hub-
    boundary <= 2, so (PAIR-3) kills them — (V) closes OUTRIGHT once
    (E-pair) does ((PAIR-6)).
  * `--pool` is the denominator disclosure.  Of `saferes.py --prime`'s 255
    residual inhabitants, ZERO have an independent degree-2 set, and the
    pool's `max f(V(G)) = 2` against the `f >= 6` a counterexample needs
    (T32 sits at `f = 4`).  The honest denominator is **0, not 255**.

Oracles.  Rigidity is `nogood_subdiv.deficiency` (Lee-Streinu (6,6) pebble
game), cross-checked against `saferes.treepack_deficiency` (matroid-union
tree packing).  Feasibility verdicts are landed-lemma-certified exactly as
in `weloc.py`: L6b (`hcard` + triangle-free) on the sufficient side, the
`hcard` necessary condition on the infeasible side; no middle zone is ever
counted as a verdict.

Run:
    python3 notes/scripts/w4/wpair.py --validate   # (PAIR-1)/(PAIR-2)/(PAIR-3)
    python3 notes/scripts/w4/wpair.py --sub        # (PAIR-4): the e0 = 0 stratum
    python3 notes/scripts/w4/wpair.py --hunt       # the search + seed condition
    python3 notes/scripts/w4/wpair.py --vee        # job 3: (V)'s two residues
    python3 notes/scripts/w4/wpair.py --pool       # denominator disclosure
"""
import os
import random
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of, neighbors, degrees, is_2ec
from nogood_subdiv import (D_BODY, MULT, is_rigid, is_simple, hub_set, hcard_ok,
                           triangles, provably_feasible, provably_infeasible,
                           rigid_vertex_sets, induced_edges, contraction, classify,
                           branch_decomposition, path_between)
from saferes import treepack_deficiency
from widened import f_of, prime_pool, residuals
import weloc

BR_CAP = 16          # `rigid_vertex_sets`' branch-enumeration cap (2^BR_CAP masks)


# ---------------- the objects of *Steps PR1-PR6* ---------------------------

def indep_deg2(edges):
    """`G`'s degree-2 vertices form an INDEPENDENT set — the exact negation of
    (E-pair)'s conclusion, and (in branch-length form) the statement that
    every branch of `G` carries at most ONE interior vertex."""
    deg = degrees(edges)
    return all(not (deg[u] == 2 and deg[w] == 2) for u, w in edges)


def e0_sigma(edges):
    """`(e0, sigma)`: the number of hub-hub edges (= edges of the hub graph
    `Lambda = G[hubs]`) and the excess hub degree `sum_{hubs}(deg v - 3)`."""
    deg, hubs = degrees(edges), hub_set(edges)
    e0 = sum(1 for u, w in edges if u in hubs and w in hubs)
    return e0, sum(deg[v] - 3 for v in hubs)


def boundary(edges, U):
    """`dU`: the vertices outside `U` with a neighbour in `U`."""
    nb, Us = neighbors(edges), set(U)
    return {x for x in verts_of(edges) if x not in Us and set(nb[x]) & Us}


def hub_boundary(edges, U):
    """`d_hub U`: the HUBS outside `U` adjacent to `U` — by (PAIR-2) the only
    obstruction to `hcard(G/U)`, and (since a degree-2 vertex of a rigid `U`
    has both neighbours in `U`) exactly the outside endpoints of the hub-graph
    edges leaving `U`."""
    hubs = hub_set(edges)
    return {x for x in boundary(edges, U) if x in hubs}


def lambda_components(edges):
    """Components of the hub graph `Lambda = G[hubs]`.  By (EL-1) `Lambda` has
    max degree <= 2, so each is a path or a cycle; by (EL-4) every cycle
    component of a residual's `Lambda` has length >= 7."""
    hubs = hub_set(edges)
    nb = neighbors(induced_edges(edges, hubs))
    seen, out = set(), []
    for v in sorted(hubs, key=str):
        if v in seen:
            continue
        comp, stack = set(), [v]
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x)
            stack += [y for y in nb.get(x, ()) if y not in comp]
        seen |= comp
        out.append(comp)
    return out


def rigid_sets(edges, lo=3):
    """Proper rigid vertex sets of size >= `lo`.  `rigid_vertex_sets` is
    complete at min degree >= 2 (rigid sets are branch-closed); a `Simple`
    graph has no rigid set on 2 vertices (one edge gives `def = 1`), so `lo=3`
    loses nothing."""
    return [U for U in rigid_vertex_sets(edges) if len(U) >= lo]


def seed_sets(edges):
    """The SEEDS of (PAIR-5): proper rigid sets with hub-boundary <= 2.  By
    (PAIR-3) a residual has NONE."""
    return [U for U in rigid_sets(edges) if len(hub_boundary(edges, U)) <= 2]


def chain(edges, U, verbose=False):
    """*Step EL4*'s growth chain, run from an arbitrary rigid seed `U` and
    carrying (PAIR-3)'s invariant.

    At each step ASSERT (i) `G[S]` is rigid, (ii) the hub-boundary has not
    grown, (iii) if the contraction is simple then `hcard(G/S)` agrees with
    `|d_hub S| <= 2` ((PAIR-2)).  Then:
      * `G/S` not simple  -> an `x` with two `S`-neighbours; `S += {x}` (Ear
        Lemma `j = 1`).  Its two `S`-neighbours are hubs, so a hub `x` spends
        both of its (EL-1) hub slots inside `S` and the hub-boundary DROPS.
      * `G/S` carries a triangle through `v*` -> adjacent `x, y` outside both
        attached to `S`; `S += {x, y}` (Ear Lemma `j = 2`).
      * neither, and `|d_hub S| <= 2` -> `G/S` is Simple and L6b-FEASIBLE: a
        good contraction, which a residual forbids.
    Outcomes: `good-contraction`, `co-1`, `spanning-C3` (all three forbidden
    at a residual), `G-triangle` (forbidden by (T)), `stuck-nohcard` (the
    chain left the seed condition — impossible while the invariant holds)."""
    V = set(verts_of(edges))
    nb, deg = neighbors(edges), degrees(edges)
    S = set(U)
    hb_prev = len(hub_boundary(edges, S))
    steps = {'ear j=1': 0, 'ear j=2': 0}
    while True:
        assert is_rigid(induced_edges(edges, S), sorted(S, key=str)), "S not rigid"
        hb = len(hub_boundary(edges, S))
        assert hb <= hb_prev, f"(PAIR-3) invariant broke: hub-boundary {hb_prev} -> {hb}"
        hb_prev = hb
        # every degree-2 vertex of a rigid S has both neighbours inside (the (R1) closure)
        assert all(set(nb[v]) <= S for v in S if deg[v] == 2), "closure broke"
        if len(S) == len(V) - 1:
            return 'co-1', S, steps, hb
        assert S != V, "chain exhausted V without a verdict"
        Q = contraction(edges, S)
        if not is_simple(Q):
            x = next(x for x in V - S if len(set(nb[x]) & S) >= 2)
            if S | {x} == V:
                return 'co-1', S, steps, hb
            S = S | {x}
            steps['ear j=1'] += 1
            if verbose:
                print(f"      ear j=1 at {x}: |S| -> {len(S)}, d_hub -> "
                      f"{len(hub_boundary(edges, S))}")
            continue
        assert hcard_ok(Q) == (hb <= 2), "(PAIR-2) broke at a simple contraction"
        tri = triangles(Q)
        if tri:
            t = next(iter(tri))
            if 'v*' not in t:
                return 'G-triangle', S, steps, hb
            x, y = (t - {'v*'})
            if S | {x, y} == V:
                return 'spanning-C3', S, steps, hb
            S = S | {x, y}
            steps['ear j=2'] += 1
            if verbose:
                print(f"      ear j=2 at {x},{y}: |S| -> {len(S)}, d_hub -> "
                      f"{len(hub_boundary(edges, S))}")
            continue
        if hb <= 2:
            assert provably_feasible(Q), "L6b should certify this contraction"
            return 'good-contraction', S, steps, hb
        return 'stuck-nohcard', S, steps, hb


# ---------------- generators ------------------------------------------------

def subdivide(base, sub):
    """Partial subdivision: subdivide `base[i]` once for every `i in sub`.
    Every branch of the result carries 0 or 1 interior vertices, so the result
    is an (E-pair)-counterexample CANDIDATE by construction."""
    E = []
    for i, (a, b) in enumerate(base):
        if i in sub:
            E += [(a, f'm{i}'), (f'm{i}', b)]
        else:
            E.append((a, b))
    return E


def random_base(rng, h, extra=0):
    """A random multigraph on `h` vertices of min degree >= 3: a union of
    three near-perfect matchings on the pairing model, plus `extra` random
    edges.  Parallel pairs are allowed (they must be subdivided later, since
    the result has to be simple)."""
    base = []
    for _ in range(3 + extra):
        vs = [f'z{i}' for i in range(h)]
        rng.shuffle(vs)
        for i in range(0, h - 1, 2):
            base.append((vs[i], vs[i + 1]))
        if h % 2:
            base.append((vs[-1], vs[rng.randrange(h - 1)]))
    return [(a, b) for a, b in base if a != b]


def forced_subdivisions(base):
    """Indices that MUST be subdivided for the result to be simple: every
    repeat of a vertex pair beyond its first occurrence."""
    seen, forced = set(), set()
    for i, (a, b) in enumerate(base):
        k = frozenset((a, b))
        if k in seen:
            forced.add(i)
        seen.add(k)
    return forced


def octagon_diameters():
    """*Step PR5*'s worked instance, asserted so the prose figure cannot rot: the
    hub graph `Lambda` is an 8-cycle and the four diameters are once-subdivided
    branches.  `|V| = 12`, `|E| = 16`, `f = 14 = 6 + 8 + 2*0`, triangle-free,
    `hcard`, every branch of interior length <= 1 — and the `C6`
    `z0 z1 z2 z3 z4 m0` is a rigid set whose hub part is a `Lambda`-sub-path, so
    its hub-boundary is `{z5, z7}`: a SEED, which (PAIR-3) forbids."""
    E = [(f'z{i}', f'z{(i + 1) % 8}') for i in range(8)]
    for i in range(4):
        E += [(f'z{i}', f'm{i}'), (f'm{i}', f'z{i + 4}')]
    return E, ('z0', 'z1', 'z2', 'z3', 'z4', 'm0')


def candidate(edges):
    """Is `edges` a (E-pair)-counterexample candidate: simple, min degree >= 2,
    2EC, degree-2 set independent, triangle-free, `hcard` (so feasible by
    L6b), and within the branch-enumeration cap?"""
    if not is_simple(edges):
        return False
    V, deg = verts_of(edges), degrees(edges)
    if len(V) < 5 or any(deg[v] < 2 for v in V) or not is_2ec(edges):
        return False
    if not indep_deg2(edges) or triangles(edges) or not hcard_ok(edges):
        return False
    _, br = branch_decomposition(edges)
    return br is not None and len(br) <= BR_CAP


# ---------------- --validate ------------------------------------------------

def validate():
    print("  (PAIR-1) the deficit identity `f = 6 + e0 + 2*sigma` on every simple "
          "min-degree-2 graph\n           whose degree-2 vertices are independent:")
    rng = random.Random(20260902)
    tested = 0
    for _ in range(160000):
        n = rng.randint(4, 11)
        vs = [f'v{i}' for i in range(n)]
        E = [(a, b) for a, b in combinations(vs, 2)
             if rng.random() < rng.choice((0.25, 0.35, 0.5))]
        if not E:
            continue
        V, deg = verts_of(E), degrees(E)
        if len(V) < 4 or any(deg[v] < 2 for v in V) or not is_simple(E):
            continue
        if not indep_deg2(E):
            continue
        e0, sigma = e0_sigma(E)
        assert hub_set(E), "an independent degree-2 set forces a hub"
        assert f_of(E) == 6 + e0 + 2 * sigma, (sorted(E), f_of(E), e0, sigma)
        tested += 1
    print(f"           {tested} instances, 0 mismatches "
          f"(so `f >= 6 + e0 >= 6` always, and `f = 6` iff `e0 = sigma = 0`)")

    print("  (PAIR-2) `hcard(G/U) <-> |d_hub U| <= 2` at a rigid `U` with a simple "
          "contraction,\n           plus the (R1) closure and the hub-attachment claim:")
    rng = random.Random(700)
    inst = sets = simple = 0
    for _ in range(4000):
        n = rng.randint(4, 7)
        vs = [f'p{i}' for i in range(n)]
        E, tag = [], 0
        for (a, b) in combinations(vs, 2):
            if rng.random() < 0.5:
                L = rng.choice((0, 0, 1, 1, 2, 3))
                if L == 0:
                    E.append((a, b))
                else:
                    E += path_between(a, b, L, f't{tag}_')
                    tag += 1
        if not E:
            continue
        V, deg = verts_of(E), degrees(E)
        if len(V) < 5 or any(deg[v] < 2 for v in V) or not is_simple(E) or not is_2ec(E):
            continue
        if not hcard_ok(E):
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > BR_CAP:
            continue
        inst += 1
        nb, tris = neighbors(E), triangles(E)
        for U in rigid_sets(E):
            sets += 1
            Us = set(U)
            assert all(set(nb[v]) <= Us for v in U if deg[v] == 2), "closure"
            assert all(deg[u] >= 3 for u in Us if set(nb[u]) - Us), "attachment not a hub"
            Q = contraction(E, U)
            if not is_simple(Q):
                continue
            simple += 1
            assert hcard_ok(Q) == (len(hub_boundary(E, U)) <= 2), sorted(U)
            bd = boundary(E, U)
            pred = (any(x in bd and y in bd for x, y in E)
                    or any(not (t & Us) for t in tris))
            assert bool(triangles(Q)) == pred, sorted(U)
    print(f"           {inst} graphs, {sets} rigid sets, {simple} simple contractions, "
          f"0 mismatches")

    print("  (PAIR-3) the growth chain from an arbitrary seed: hub-boundary never "
          "grows, and\n           every run lands on a residual-forbidden verdict:")
    rng = random.Random(1111)
    inst = runs = 0
    outcomes = {}
    for _ in range(3000):
        n = rng.randint(4, 7)
        vs = [f'p{i}' for i in range(n)]
        E, tag = [], 0
        for (a, b) in combinations(vs, 2):
            if rng.random() < 0.5:
                L = rng.choice((0, 0, 1, 1, 2, 3, 4))
                if L == 0:
                    E.append((a, b))
                else:
                    E += path_between(a, b, L, f't{tag}_')
                    tag += 1
        if not E:
            continue
        V, deg = verts_of(E), degrees(E)
        if len(V) < 5 or any(deg[v] < 2 for v in V) or not is_simple(E) or not is_2ec(E):
            continue
        if not hcard_ok(E) or triangles(E):
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > BR_CAP:
            continue
        seeds = [U for U in seed_sets(E) if len(U) < len(V) - 1]
        if not seeds:
            continue
        inst += 1
        for U in seeds:
            runs += 1
            out, S, steps, hb = chain(E, U)
            outcomes[out] = outcomes.get(out, 0) + 1
    print(f"           {inst} graphs, {runs} chain runs, outcomes "
          f"{dict(sorted(outcomes.items()))}")
    assert set(outcomes) <= {'good-contraction', 'co-1', 'spanning-C3'}, outcomes
    print("           every outcome is forbidden at a residual, so no residual "
          "carries a seed.")
    print("  VALIDATE: OK")


# ---------------- --sub: the proved stratum (PAIR-4) ------------------------

def sub():
    print("  (PAIR-4) When the hubs are INDEPENDENT (`e0 = 0`) every rigid set has "
          "hub-boundary 0:\n           an outside hub `w` adjacent to `U` would "
          "attach at a degree-2 `u in U`, whose\n           two neighbours are in "
          "`U` by the (R1) closure — so `w in U`.  Hence (PAIR-3)\n           applies "
          "outright and no FULL SUBDIVISION is a residual.  Audited:")
    rng = random.Random(31337)
    inst = zero = 0
    outcomes = {}
    fdist = {}
    for _ in range(260):
        h = rng.choice((4, 5, 6, 6, 7, 8, 8, 9, 10))
        base = random_base(rng, h, extra=rng.choice((0, 0, 1)))
        if len(base) > BR_CAP:
            continue
        E = subdivide(base, set(range(len(base))))     # FULL subdivision: e0 = 0
        if not candidate(E):
            continue
        e0, sigma = e0_sigma(E)
        assert e0 == 0, "a full subdivision has no hub-hub edge"
        rig = rigid_sets(E)
        if not rig:
            continue                                    # no proper rigid subgraph: not a residual
        inst += 1
        fdist[f_of(E)] = fdist.get(f_of(E), 0) + 1
        assert all(not hub_boundary(E, U) for U in rig), "a full subdivision with d_hub > 0"
        zero += len(rig)
        st, _ = classify(E)
        outcomes[st] = outcomes.get(st, 0) + 1
        assert not st.endswith('CANDIDATE'), ("residual full subdivision", sorted(E))
        # and the chain from an arbitrary seed reaches a forbidden verdict
        U = min(rig, key=len)
        if len(U) < len(verts_of(E)) - 1:
            out, _S, _st, _hb = chain(E, U)
            assert out in ('good-contraction', 'co-1', 'spanning-C3'), out
    print(f"           {inst} full subdivisions carrying a proper rigid subgraph; "
          f"{zero} rigid sets,\n           ALL with hub-boundary 0; `classify` "
          f"verdicts {dict(sorted(outcomes.items()))}")
    print(f"           `f(V(G))` distribution {dict(sorted(fdist.items()))} — "
          f"the `f = 6` stratum is\n           exactly the 3-regular case "
          f"(`e0 = sigma = 0`), and it is CLOSED.")
    print("  Consequence: a residual violating (E-pair) has `e0 >= 1`, hence "
          "`f(V(G)) >= 7`.\n  Equivalently: (E-pair) follows from `f(V(G)) <= 6`, "
          "two units weaker than (E).")
    print("  SUB: OK")


# ---------------- --hunt: the search, and the seed condition ----------------

def hunt():
    print("  Searching for a RESIDUAL with an independent degree-2 set (= every "
          "branch of\n  interior length <= 1).  Family: partial subdivisions of "
          "min-degree-3 multigraphs\n  (the shape (PAIR-1) forces), rejected unless "
          "simple, 2EC, triangle-free and `hcard`.")
    E0, U0 = octagon_diameters()
    assert candidate(E0) and f_of(E0) == 14 and e0_sigma(E0) == (8, 0), "PR5 instance"
    assert is_rigid(induced_edges(E0, U0), list(U0)), "PR5's C6 is not rigid"
    hb0 = hub_boundary(E0, U0)
    assert hb0 == {'z5', 'z7'}, sorted(hb0)
    out0 = chain(E0, U0)[0]
    assert out0 in ('good-contraction', 'co-1', 'spanning-C3'), out0
    print(f"  *Step PR5*'s worked instance: |V| = {len(verts_of(E0))}, f = {f_of(E0)}"
          f" = 6 + 8 + 0, the `C6`'s hub-boundary is {sorted(hb0)} — a SEED whose\n"
          f"  chain ends `{out0}`; `classify` returns `{classify(E0)[0]}`.  Asserted, "
          f"not quoted.")
    rng = random.Random(20260902)
    stat = {'built': 0, 'candidates': 0, 'no-rigid': 0, 'residual': 0,
            'seed': 0, 'seedless': 0, 'capped': 0}
    verdicts = {}
    fmax, hmax, chains = -99, 0, {}
    for _ in range(240):
        h = rng.choice((4, 5, 6, 6, 7, 8, 8, 9, 10, 11, 12))
        base = random_base(rng, h, extra=rng.choice((0, 0, 0, 1)))
        if len(base) > BR_CAP:
            stat['capped'] += 1
            continue
        forced = forced_subdivisions(base)
        for _try in range(4):
            p = rng.choice((0.45, 0.6, 0.75, 0.9))
            sub_idx = set(forced) | {i for i in range(len(base))
                                     if i not in forced and rng.random() < p}
            E = subdivide(base, sub_idx)
            stat['built'] += 1
            if not candidate(E):
                continue
            stat['candidates'] += 1
            fmax, hmax = max(fmax, f_of(E)), max(hmax, len(hub_set(E)))
            rig = rigid_sets(E)
            if not rig:
                stat['no-rigid'] += 1
                continue
            st, _info = classify(E)
            verdicts[st] = verdicts.get(st, 0) + 1
            if st.endswith('CANDIDATE'):
                stat['residual'] += 1
                print(f"  !!! COUNTEREXAMPLE to (E-pair): {st}, |V| = "
                      f"{len(verts_of(E))}, f = {f_of(E)}\n      {sorted(E)}")
            seeds = [U for U in seed_sets(E) if len(U) < len(verts_of(E)) - 1]
            if seeds or any(len(U) == len(verts_of(E)) - 1 for U in rig):
                stat['seed'] += 1
                if seeds:
                    out, _S, _steps, _hb = chain(E, min(seeds, key=len))
                    chains[out] = chains.get(out, 0) + 1
            else:
                stat['seedless'] += 1
                print(f"  ??? SEEDLESS candidate (every rigid set has d_hub >= 3): "
                      f"{st}, |V| = {len(verts_of(E))}, f = {f_of(E)}\n      "
                      f"{sorted(E)}")
    print(f"  built {stat['built']}, candidates {stat['candidates']} "
          f"(max `f` = {fmax}, max hubs = {hmax}), of which\n    "
          f"{stat['no-rigid']} carry no proper rigid subgraph (not residuals), "
          f"`classify` {dict(sorted(verdicts.items()))}")
    print(f"  RESIDUALS FOUND: {stat['residual']}")
    print(f"  seed condition (PAIR-5) held at {stat['seed']} candidates, FAILED at "
          f"{stat['seedless']};\n  the chain from the smallest seed ended "
          f"{dict(sorted(chains.items()))}")
    print("  CAP DISCLOSURE.  The sweep is capped by `rigid_vertex_sets`' branch "
          f"enumeration\n  (<= {BR_CAP} branches, i.e. <= {BR_CAP} skeleton edges — "
          "at min degree 3 that is <= 10 hubs)\n  and by the generator's pairing "
          "model, which builds no hub cycle of length >= 7 by\n  design.  An "
          "impossibility claim about ALL residuals does NOT follow from this sweep "
          "—\n  what does the proving is (PAIR-3) plus (PAIR-4); the sweep only "
          "confirms that the\n  seed condition (PAIR-5) is not violated anywhere it "
          "could be tested.")


# ---------------- --vee: job 3, (V)'s two residues --------------------------

def vee():
    print("  Job 3.  (V) needs a branch with `j >= 2` interior vertices — exactly "
          "what (E-pair)\n  supplies — and three residues resist its local choice: "
          "`j = 2` with `u = u'` (a\n  triangle, killed by (T)); `j = 3` with "
          "`u = u'`; `j = 2` with `u ~ u'`.  Both of the\n  latter carry an induced "
          "`C4` whose hub-boundary is <= 2 by (EL-1), so (PAIR-3) kills\n  them: "
          "(PAIR-6).  Audited on explicit carriers:")
    rng = random.Random(4242)
    seen = {'j3-uu': 0, 'j2-adj': 0}
    for _ in range(1400):
        h = rng.choice((4, 5, 6, 7, 8))
        base = random_base(rng, h, extra=rng.choice((0, 1)))
        if len(base) > BR_CAP - 3:
            continue
        forced = forced_subdivisions(base)
        sub_idx = set(forced) | {i for i in range(len(base))
                                 if i not in forced and rng.random() < 0.8}
        E = subdivide(base, sub_idx)
        if not is_simple(E) or not is_2ec(E):
            continue
        hubs = sorted(hub_set(E), key=str)
        if not hubs:
            continue
        u = hubs[rng.randrange(len(hubs))]
        shape = rng.choice(('j3-uu', 'j2-adj'))
        if shape == 'j3-uu':          # a C4 hanging off u: u - x1 - x2 - x3 - u
            F = E + [(u, 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', u)]
            U = (u, 'x1', 'x2', 'x3')
        else:                          # u ~ u' with a 2-interior branch: u - x1 - x2 - u'
            u2 = hubs[rng.randrange(len(hubs))]
            if u2 == u or any(frozenset((a, b)) == frozenset((u, u2)) for a, b in E):
                continue
            F = E + [(u, u2), (u, 'x1'), ('x1', 'x2'), ('x2', u2)]
            U = (u, 'x1', 'x2', u2)
        if not is_simple(F) or not is_2ec(F) or triangles(F) or not hcard_ok(F):
            continue
        _, br = branch_decomposition(F)
        if br is None or len(br) > BR_CAP:
            continue
        ie = induced_edges(F, U)
        assert len(ie) == 4 and is_rigid(ie, list(U)), ("the residue is not an induced C4", U)
        assert treepack_deficiency(ie, list(U)) == 0, "tree-packing oracle disagrees"
        hb = hub_boundary(F, U)
        assert len(hb) <= 2, ("the residue's hub-boundary exceeds 2", sorted(hb))
        st, _ = classify(F)
        assert not st.endswith('CANDIDATE'), ("residual carrying a (V) residue", sorted(F))
        out, _S, _steps, _hb = chain(F, U)
        assert out in ('good-contraction', 'co-1', 'spanning-C3'), out
        seen[shape] += 1
    print(f"           carriers audited: {seen} — every one has residue "
          f"hub-boundary <= 2, is\n           NOT a residual, and its chain ends on a "
          f"residual-forbidden verdict.")
    T32 = weloc.two_core(4, 1, 4)
    deg, nb = degrees(T32), neighbors(T32)
    branches = branch_decomposition(T32)[1]
    long_br = [b for b in branches if len(b[2]) >= 2]
    good = []
    for (h1, h2, ins) in long_br:
        if len(ins) >= 3 and h1 != h2:
            good.append((h1, h2, len(ins)))
    print(f"  (V) at `T32`: {len(long_br)} branches with `j >= 2`, {len(good)} of them "
          f"immediately\n           usable (`j >= 3`, distinct hub ends) — so (V) holds "
          f"there, as WELOC recorded.\n           But that is a WITNESS; what makes (V) "
          f"a THEOREM given (E-pair) is (PAIR-6).")
    print("  VEE: OK")


# ---------------- --pool: denominator disclosure ----------------------------

def pool():
    pl = list(residuals(prime_pool()))
    print(f"  `saferes.py --prime` residual inhabitants: {len(pl)}")
    fhist, indep = {}, 0
    for E, _ in pl:
        f = f_of(E)
        fhist[f] = fhist.get(f, 0) + 1
        if indep_deg2(E):
            indep += 1
        assert f <= 4, E
    T32 = weloc.two_core(4, 1, 4)
    print(f"  `f(V(G))` distribution: {dict(sorted(fhist.items()))}  "
          f"(max {max(fhist)}; `T32` at {f_of(T32)})")
    print(f"  residuals with an INDEPENDENT degree-2 set: {indep}  "
          f"(`T32`: {indep_deg2(T32)})")
    print("  DISCLOSURE: the denominator for (E-pair) over this pool is not 255 — it "
          "is **0**.\n  By (PAIR-1) a counterexample needs `f(V(G)) >= 6 + e0 >= 7` "
          "(>= 7 once (PAIR-4)\n  closes `e0 = 0`), while the pool's maximum is 2 and "
          "`T32`'s is 4.  No pool instance\n  is even a candidate, so the recorded "
          "'(E-pair) holds 255/255' was never evidence\n  about (E-pair): it is a "
          "restatement of `f <= 4` there.  This is NOT (T)'s blind\n  spot — branch "
          "length appears in no feasibility certificate, so a sweep COULD have\n  seen "
          "a failure; the arithmetic is what rules the pool out.")


def main():
    modes = {'--validate': validate, '--sub': sub, '--hunt': hunt,
             '--vee': vee, '--pool': pool}
    args = [a for a in sys.argv[1:] if a in modes] or list(modes)
    for a in args:
        print(f"=== wpair.py {a} ===")
        modes[a]()
        print()


if __name__ == '__main__':
    main()
