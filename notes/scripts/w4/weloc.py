"""
Phase 39 W4 — direction WELOC: the gap (E-loc).

(E-loc) claimed: every RESIDUAL `G` (simple, 2EC, `PencilNondegFeasible`,
`3 <= |V|`, a proper rigid subgraph, no co-1 rigid subgraph, no rigid
contraction that is Simple AND Feasible) has a degree-2 vertex `v0` with
`E(G - v0)` INDEPENDENT in the (6,6) count matroid.  Discharging it would
have given `(E)` — `f(V(G)) = 5|E| - 6(|V|-1) <= 4` — through the landed
`edgeBound_of_noRigid_of_degree_two` verbatim.

RESULT (2026-09-02): **(E-loc) is REFUTED**, and the *other* obstruction
shape is **impossible**.

  * `--witness` exhibits `T32`, a `|V| = 32` residual with TWO DISJOINT
    count-dependent `C4` cores.  No degree-2 vertex lies in both, so every
    `E(G - v)` is count-DEPENDENT.  Both feasibility verdicts are
    landed-lemma-certified exactly as for `W19`/`S29` (L6b for `G`; the
    `hcard` necessary condition for both contractions), so the refutation
    rests on no unproven feasibility fact.  `f(V(T32)) = 4` **exactly**, so
    `T32` satisfies (E) with equality: it refutes the ROUTE, not (E).
  * `--brick` audits the theorem (EL-4): no residual carries a "brick" — a
    count-dependent set all of whose vertices are `G`-hubs.  By (EL-1)
    (feasibility bounds every hub to <= 2 hub neighbours) such a set is a
    `C4` or `C5` of hubs, and the growth chain of *Step EL4* turns one into a
    certified good contraction, a co-1 rigid subgraph or a spanning-`C3`
    contraction — each of them forbidden at a residual.
  * `--pool` is the denominator disclosure.  Of `saferes.py --prime`'s 255
    residual inhabitants, **160 carry no count-dependent set at all** and
    **95 carry exactly one**; **0** carry two.  The pool therefore contains
    ZERO instances of the only configuration that can refute (E-loc), and
    the recorded 255/255 was never evidence about it.

Oracles.  Rigidity is decided by `nogood_subdiv.deficiency` (Lee-Streinu
(6,6) pebble game) and cross-checked against `saferes.treepack_deficiency`
(matroid-union tree packing) and, on small sets, `kbare_common.
exact_deficiency` (partition enumeration).  Count-independence is decided by
`widened.count_indep` (the same pebble game on the 5-fold fiber) and
cross-checked against the direct `f(W) <= 0` sweep in `--validate`.

Run:
    python3 notes/scripts/w4/weloc.py --validate   # mechanical identities
    python3 notes/scripts/w4/weloc.py --witness    # T32, the refutation
    python3 notes/scripts/w4/weloc.py --brick      # the (EL-4) audit
    python3 notes/scripts/w4/weloc.py --pool       # denominator disclosure
    python3 notes/scripts/w4/weloc.py --hunt       # how big the shape-1 family is
"""
import os
import random
import sys
from itertools import combinations

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import exact_deficiency, verts_of, neighbors, degrees, is_2ec
import nogood_subdiv as ns
from nogood_subdiv import (D_BODY, MULT, deficiency, is_rigid, is_simple, hub_set,
                           hcard_ok, triangles, provably_feasible,
                           provably_infeasible, rigid_vertex_sets, induced_edges,
                           contraction, classify, path_between,
                           branch_decomposition)
from saferes import treepack_deficiency, classify2, split_usable, deep_split_vertices
from widened import count_indep, f_of, removeV, prime_pool, residuals


# ---------------- count-matroid combinatorics ------------------------------

def components(edges, W):
    """Connected components of `G[W]` (isolated vertices included)."""
    nb = neighbors(induced_edges(edges, W))
    seen, out = set(), []
    for v in sorted(W, key=str):
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


def cycle_rank(edges, W):
    return len(induced_edges(edges, W)) - len(W) + len(components(edges, W))


def dependent_sets(edges):
    """All MINIMAL count-dependent vertex sets (`f(W) > 0`, no proper subset
    dependent), via the branch enumeration.

    Completeness: a minimal dependent `W` has min degree >= 2 in `G[W]`
    (deleting a `G[W]`-degree-`d <= 1` vertex changes `f` by `6 - 5d >= 1`),
    so every degree-2 vertex of `G` in `W` drags its whole branch and both
    branch endpoints into `W`, and every hub of `W` sits on >= 2 branches of
    `W`.  Hence `W` is branch-closed, exactly as for rigid sets
    (`nogood_subdiv.rigid_vertex_sets`).  `--validate` cross-checks this
    against a brute-force subset sweep."""
    hubs, branches = branch_decomposition(edges)
    V = verts_of(edges)
    if branches is None:                       # a pure cycle
        return [tuple(sorted(V, key=str))] if f_of(edges) > 0 else []
    assert len(branches) <= 22, "too many branches to enumerate"
    cands = set()
    for mask in range(1, 1 << len(branches)):
        A, inter = set(), set()
        for i, (h1, h2, ins) in enumerate(branches):
            if mask >> i & 1:
                A.add(h1)
                A.add(h2)
                inter.update(ins)
        W = frozenset(A | inter)
        if len(W) >= 3:
            cands.add(W)
    dep = []
    for W in cands:
        ie = induced_edges(edges, W)
        dg = degrees(ie)
        if any(dg.get(v, 0) < 2 for v in W):
            continue
        if MULT * len(ie) > D_BODY * (len(W) - 1):
            dep.append(W)
    minimal = [W for W in dep if not any(X < W for X in dep)]
    return sorted((tuple(sorted(W, key=str)) for W in minimal), key=(lambda t: (len(t), t)))


def dependent_sets_bruteforce(edges):
    V = sorted(verts_of(edges), key=str)
    dep = []
    for k in range(2, len(V) + 1):
        for W in combinations(V, k):
            if MULT * len(induced_edges(edges, W)) > D_BODY * (len(W) - 1):
                dep.append(frozenset(W))
    minimal = [W for W in dep if not any(X < W for X in dep)]
    return sorted((tuple(sorted(W, key=str)) for W in minimal), key=(lambda t: (len(t), t)))


def eloc_witnesses(edges):
    """Degree-2 vertices `v0` with `E(G - v0)` count-INDEPENDENT — i.e. the
    vertices (E-loc) asserts exist."""
    deg = degrees(edges)
    return [v for v in sorted(verts_of(edges), key=str)
            if deg[v] == 2 and count_indep(removeV(edges, v))]


def bricks(edges):
    """Minimal count-dependent sets carrying NO degree-2 vertex — obstruction
    shape 2 of §widened kernels *Step 3*, classified by (EL-3) as a `C4` or
    `C5` all of whose vertices are `G`-hubs."""
    deg = degrees(edges)
    return [W for W in dependent_sets(edges) if all(deg[v] >= 3 for v in W)]


def hub_cycles(edges, cap=8):
    """All cycles of length <= cap every vertex of which is a `G`-hub."""
    hubs = hub_set(edges)
    nb = neighbors(edges)
    out = set()

    def walk(start, cur, path):
        for y in nb.get(cur, ()):
            if y not in hubs:
                continue
            if y == start and len(path) >= 3:
                out.add(frozenset(path))
            elif y not in path and len(path) < cap:
                walk(start, y, path + [y])

    for h in hubs:
        walk(h, h, [h])
    return sorted((tuple(sorted(W, key=str)) for W in out), key=len)


# ---------------- the refuting witness -------------------------------------

def two_core(a=4, b=1, m=4):
    """`T32` at the default parameters.

    Two DISJOINT `C_m` cores `c*` and `d*`.  Core 1 carries hub poles `z0, z1`
    on `c0` and `z2` on the opposite `c2`; core 2 carries `w0, w1` on `d0` and
    `w2` on `d2`.  The six poles sit on one ring `z0 z1 z2 w0 w1 w2`, whose
    same-core legs carry `a` interior vertices and whose cross legs carry `b`.

    Why each parameter is what it is:
      * three hub poles per core is what makes `closedHubNbhd(v*) = 4` at the
        contraction, i.e. infeasibility by the LANDED NECESSARY `hcard`
        (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`).  Two
        poles leave `hcard` intact and L6b then certifies the contraction
        FEASIBLE — a good contraction, and no residual.
      * `a >= 4` is the Ear Lemma: the ear `c0 - z0 - [a] - z1 - c0` has
        `a + 2` interior vertices and must have `>= 6`, or the core grows.
      * `b` trades size against `f`: `f(V(G)) = 22 - (4a + 2b)` in this
        family, and `f > 4` always came back `co-1` or `good-contraction`.
        `(a, b) = (4, 1)` is the smallest residual the family reaches, and it
        sits at `f = 4` EXACTLY."""
    E = [(f'c{i}', f'c{(i + 1) % m}') for i in range(m)]
    E += [(f'd{i}', f'd{(i + 1) % m}') for i in range(m)]
    opp = m // 2
    E += [('c0', 'z0'), ('c0', 'z1'), (f'c{opp}', 'z2'),
          ('d0', 'w0'), ('d0', 'w1'), (f'd{opp}', 'w2')]
    ring = ['z0', 'z1', 'z2', 'w0', 'w1', 'w2']
    legs = [a, a, b, a, a, b]
    for i in range(6):
        E += path_between(ring[i], ring[(i + 1) % 6], legs[i], f'r{i}_')
    return E


T32 = two_core(4, 1, 4)


def witness():
    G = T32
    V = verts_of(G)
    deg = degrees(G)
    print(f"  T32: |V| = {len(V)}, |E| = {len(G)}, f(V(G)) = {f_of(G)}, "
          f"def(G) = {deficiency(G)} (tree packing: {treepack_deficiency(G, V)})")
    print(f"  edges: {sorted(G, key=str)}")
    print(f"  simple={is_simple(G)} 2EC={is_2ec(G)} hcard={hcard_ok(G)} "
          f"triangles={triangles(G)}")
    print(f"  => provably feasible (L6b: hcard + triangle-free): "
          f"{provably_feasible(G)}")
    print(f"  hubs ({len(hub_set(G))}): {sorted(hub_set(G))}")
    st, info = classify2(G)
    print(f"  classify2 (every rigidity verdict re-checked on the tree-packing "
          f"oracle): {st}")
    assert st == 'STRONG-CANDIDATE'
    rig = rigid_vertex_sets(G)
    print(f"  proper rigid vertex sets ({len(rig)}, branch enumeration over "
          f"2^{len(branch_decomposition(G)[1])} branch subsets):")
    for W in rig:
        ie = induced_edges(G, W)
        d1 = deficiency(ie, list(W))
        d2 = treepack_deficiency(ie, list(W))
        d3 = exact_deficiency(ie)[0]
        Q = contraction(G, W)
        nb, hq = neighbors(Q), hub_set(Q)
        chn = {w for w in nb['v*'] if w in hq} | ({'v*'} if 'v*' in hq else set())
        print(f"    {W}: f = {f_of(G, W)}, def = {d1}/{d2}/{d3} "
              f"(pebble/packing/partition)")
        print(f"      contraction: simple={is_simple(Q)} "
              f"closedHubNbhd(v*) = {sorted(chn)} (ncard {len(chn)}) "
              f"=> infeasible by '{provably_infeasible(Q)}'")
        assert d1 == d2 == d3 == 0
        assert is_simple(Q) and provably_infeasible(Q) == 'no-hcard'
    assert all(len(W) + 1 != len(V) for W in rig), "co-1 present!"
    print(f"  no co-1 rigid subgraph: max |V(H)| = {max(len(W) for W in rig)} "
          f"<= |V| - 2 = {len(V) - 2}")
    # ---- (E-loc)
    deps = dependent_sets(G)
    print(f"  minimal count-dependent vertex sets: {deps}")
    assert len(deps) == 2 and not (set(deps[0]) & set(deps[1]))
    print(f"    -> DISJOINT, f = {f_of(G, deps[0])} and {f_of(G, deps[1])}, "
          f"so no vertex whatever lies in both")
    hits = eloc_witnesses(G)
    n2 = sum(1 for v in V if deg[v] == 2)
    print(f"  degree-2 vertices: {n2}; of these, ones with E(G - v) "
          f"count-INDEPENDENT: {len(hits)} {hits}")
    assert hits == []
    for v in V:
        if deg[v] == 2:
            W = deps[0] if v not in deps[0] else deps[1]
            assert not count_indep(induced_edges(G, W))
    print("  (E-loc) FAILS at T32: for every degree-2 v, one of the two cores "
          "avoids v and is already count-dependent.")
    # ---- what is NOT refuted
    print(f"  (E) `f(V(G)) <= 4` HOLDS at T32, with EQUALITY (f = {f_of(G)}) — "
          f"so (E) is untouched, and shown TIGHT")
    su, _ = split_usable(G)
    print(f"  (SAFE-RES') survives: deep split vertices {len(deep_split_vertices(G))}, "
          f"split-usable {len(su)}; triangle-free (as (T) requires): "
          f"{not triangles(G)}")
    # ---- the family is not a single point
    print("  the phenomenon is a family, not a point:")
    for (a, b) in ((4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2)):
        H = two_core(a, b)
        stH, _ = classify(H)
        print(f"    (a,b)=({a},{b}): |V|={len(verts_of(H))} f={f_of(H)} "
              f"def={deficiency(H)} -> {stH}, (E-loc) witnesses "
              f"{len(eloc_witnesses(H))}")
        assert stH == 'STRONG-CANDIDATE' and eloc_witnesses(H) == []
    print("  VERDICT: (E-loc) is REFUTED.")


# ---------------- the (EL-4) brick audit -----------------------------------

def hubcycle_star(m, L, R, extra=0, chords=()):
    """A hub cycle `u0..u{m-1}` (unsubdivided, so every `u_i` really is a hub
    with two hub neighbours) whose vertices hang `L`-subdivided branches on an
    outer ring of fresh hubs `v_i` with `R`-subdivided legs.  `L >= 1` and
    `R >= 1` keep `hcard` (a third hub neighbour anywhere on the cycle would
    make `G` itself landed-infeasible, so such graphs are not residual for a
    reason that has nothing to do with (EL-4)).

    `chords` is a list of `(i, j, k)` adding a `k`-interior branch `u_i .. u_j`
    — the two configurations that make the FIRST contraction escape L6b, and
    so the only way to exercise *Step EL4*'s ear-extension branches: `k = 1`
    makes `G/B` non-simple, `k = 2` gives it a `v*`-triangle."""
    E = [(f'u{i}', f'u{(i + 1) % m}') for i in range(m)]
    for i in range(m):
        E += path_between(f'u{i}', f'v{i}', L, f't{i}_')
    for i in range(m):
        E += path_between(f'v{i}', f'v{(i + 1) % m}', R, f'g{i}_')
    for j in range(extra):
        E += path_between(f'u{j % m}', f'v{(j + 2) % m}', L + 1, f'x{j}_')
    for n, (i, j, k) in enumerate(chords):
        E += path_between(f'u{i}', f'u{j}', k, f'k{n}_')
    return E


def random_hubcycle(rng, m, nhub, extra, lo=1, hi=3):
    """A random min-degree-3 base multigraph containing an UNSUBDIVIDED cycle
    `u0..u{m-1}`, every other base edge subdivided by `lo..hi` interior
    vertices — so the `C_m` survives as a cycle all of whose vertices are
    hubs."""
    cyc = [f'u{i}' for i in range(m)]
    rest = [f'h{i}' for i in range(nhub)]
    hubs = cyc + rest
    base = [(cyc[i], cyc[(i + 1) % m]) for i in range(m)]
    deg = {h: 0 for h in hubs}
    for i in range(m):
        deg[cyc[i]] += 2
    other = []
    pairs = [(a, b) for a in hubs for b in hubs if a < b
             and not (a in cyc and b in cyc and
                      abs(cyc.index(a) - cyc.index(b)) in (1, m - 1))]
    rng.shuffle(pairs)
    for (a, b) in pairs:
        if deg[a] >= 3 and deg[b] >= 3:
            continue
        other.append((a, b))
        deg[a] += 1
        deg[b] += 1
    if any(d < 3 for d in deg.values()):
        return None
    for p in pairs[:extra]:
        other.append(p)
    E = list(base)
    for t, (a, b) in enumerate(other):
        E += path_between(a, b, rng.randint(lo, hi), f's{t}_')
    return E


def growth_chain(edges, B, verbose=False):
    """*Step EL4*'s growth chain, run as stated.

    `S := B`; while `S != V(G)`, contract `G[S]` and read the residual's own
    no-good-contraction clause through L6b:
      * every step first ASSERTS the two invariants the proof carries —
        every vertex outside `S` adjacent to `S` has `G`-degree 2, and
        `hcard(G/S)` holds — so the contraction can only escape L6b by being
        non-simple or by carrying a triangle;
      * non-simple  -> a degree-2 `x` with both neighbours in `S`; `S += {x}`
        (Ear Lemma, `j = 1`);
      * a triangle  -> adjacent degree-2 `x, y` attaching at distinct `u, u'`;
        `S += {x, y}` (Ear Lemma, `j = 2`);
      * neither     -> `G/S` is Simple and L6b-FEASIBLE: a good contraction.
    Returns `(outcome, S, steps)` with outcome in `good-contraction`, `co-1`
    (the chain reached `|V| - 1`) and `spanning-C3` (it reached `|V| - 2`
    across an adjacent pair), and `steps` counting the two ear extensions
    actually taken."""
    V = set(verts_of(edges))
    deg = degrees(edges)
    nb = neighbors(edges)
    S = set(B)
    steps = {'ear j=1': 0, 'ear j=2': 0}
    while True:
        boundary = {x for x in V - S if set(nb[x]) & S}
        assert all(deg[x] == 2 for x in boundary), \
            "invariant (I) broke: a boundary vertex is a hub"
        assert is_rigid(induced_edges(edges, S), sorted(S, key=str)), "S not rigid"
        if S == V:
            raise AssertionError("chain exhausted V without a verdict")
        Q = contraction(edges, S)
        assert hcard_ok(Q), "hcard(G/S) failed — the proof's own claim"
        if not is_simple(Q):
            x = next(x for x in V - S if len(set(nb[x]) & S) >= 2)
            if S | {x} == V:
                return 'co-1', S, steps
            S = S | {x}
            steps['ear j=1'] += 1
            if verbose:
                print(f"      ear j=1 at {x}: |S| -> {len(S)}")
            continue
        tri = triangles(Q)
        if tri:
            t = next(iter(tri))
            assert 'v*' in t, "a triangle off v* would refute (T)"
            x, y = (t - {'v*'})
            if S | {x, y} == V:
                return 'spanning-C3', S, steps
            S = S | {x, y}
            steps['ear j=2'] += 1
            if verbose:
                print(f"      ear j=2 at {x},{y}: |S| -> {len(S)}")
            continue
        assert provably_feasible(Q), "L6b should certify this contraction"
        return 'good-contraction', S, steps


def brick():
    """The falsification audit for (EL-4).  Every graph below carries a cycle
    all of whose vertices are hubs.  (EL-4) says none of them is a residual,
    and *Step EL4*'s chain says why: co-1, or a certified good contraction."""
    print("  (EL-3) first: in an `hcard` graph, a count-dependent set with no "
          "degree-2 vertex is a hub `C4`/`C5`.")
    rng = random.Random(20260902)
    checked = shapes = 0
    for _ in range(4000):
        n = rng.randint(4, 9)
        vs = [f'p{i}' for i in range(n)]
        E = []
        for (a, b) in combinations(vs, 2):
            if rng.random() < rng.choice((0.3, 0.4, 0.55)):
                E.append((a, b))
        if not E or len(verts_of(E)) < 4:
            continue
        dg = degrees(E)
        if any(dg.get(v, 0) < 2 for v in verts_of(E)) or not hcard_ok(E):
            continue
        if not is_2ec(E):
            continue
        checked += 1
        for W in bricks(E):
            shapes += 1
            assert len(W) in (3, 4, 5), (W, E)
            ie = induced_edges(E, W)
            assert len(ie) == len(W), (W, E)       # a cycle
            assert all(d == 2 for d in degrees(ie).values())
            assert all(v in hub_set(E) for v in W)
            # length 3 needs (T), which is a theorem for residuals only
            assert len(W) > 3 or triangles(E)
    print(f"    random `hcard` graphs with min degree >= 2 and 2EC: {checked}; "
          f"bricks found: {shapes}; every one a hub cycle of length <= 5: OK")

    print("  (EL-4): structured + random hub-cycle families, classified.")
    fams = []
    for m in (4, 5):
        for L in (1, 2, 3):
            for R in (1, 2, 3):
                for extra in (0, 1, 2):
                    fams.append((f'star m={m} L={L} R={R} x={extra}',
                                 hubcycle_star(m, L, R, extra)))
    # the chorded instances: these are the ONLY way the first contraction can
    # escape L6b, so they are what exercises the chain's ear-extension steps.
    for m in (4, 5):
        for L in (1, 2, 3):
            for R in (1, 2):
                for ch in (((0, 2, 1),), ((0, 1, 2),), ((0, 2, 2),),
                           ((0, 2, 1), (1, 3, 1)) if m >= 4 else (),
                           ((0, 2, 1), (0, 1, 2))):
                    if not ch:
                        continue
                    fams.append((f'chord m={m} L={L} R={R} {ch}',
                                 hubcycle_star(m, L, R, 0, ch)))
    rng = random.Random(11113)
    tries = 0
    while tries < 260:
        m = rng.choice((4, 5))
        E = random_hubcycle(rng, m, rng.randint(2, 6), rng.randint(0, 3))
        if E is None:
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > 15:
            continue
        tries += 1
        fams.append((f'random m={m} |V|={len(verts_of(E))}', E))
    tally, chains, residual_hits = {}, {}, []
    ears, nonzero = {}, [0]
    for tag, E in fams:
        hc = hub_cycles(E)
        assert hc, tag
        st, _ = classify(E)
        tally[st] = tally.get(st, 0) + 1
        if st.endswith('CANDIDATE'):
            residual_hits.append((tag, E))
            continue
        if st in ('not-feasible',):
            continue
        B = next(W for W in hc if len(W) <= 5)
        assert all(deg >= 3 for deg in
                   [degrees(E)[v] for v in B]), tag
        out, S, steps = growth_chain(E, B)
        chains[out] = chains.get(out, 0) + 1
        for k, v in steps.items():
            ears[k] = ears.get(k, 0) + v
        nonzero[0] += (sum(steps.values()) > 0)
        if out == 'good-contraction':
            Q = contraction(E, S)
            assert is_simple(Q) and provably_feasible(Q), tag
        elif out == 'co-1':
            assert any(len(W) + 1 == len(verts_of(E))
                       for W in rigid_vertex_sets(E)), tag
    print(f"    instances carrying a hub cycle: {len(fams)}")
    print(f"    classifier verdicts: {dict(sorted(tally.items()))}")
    print(f"    growth-chain terminations: {dict(sorted(chains.items()))}")
    print(f"    ... ear extensions actually taken: {dict(sorted(ears.items()))} "
          f"across {nonzero[0]} instances (the rest terminate at step 0)")
    print(f"    RESIDUALS among them: {len(residual_hits)}  "
          f"(any one would REFUTE (EL-4))")
    assert not residual_hits
    print("    every step asserted `hcard(G/S)` and invariant (I) as it ran; "
          "0 failures.")


# ---------------- denominator disclosure ------------------------------------

def pool():
    pl = list(residuals(prime_pool()))
    print(f"  `saferes.py --prime` residual inhabitants: {len(pl)}")
    strong = 0
    hist, maxf = {}, -99
    noshared = disj = brickct = hcyc = 0
    for E, _ in pl:
        st, _i = classify(E)
        strong += (st == 'STRONG-CANDIDATE')
        maxf = max(maxf, f_of(E))
        deg = degrees(E)
        ms = dependent_sets(E)
        hist[len(ms)] = hist.get(len(ms), 0) + 1
        if ms:
            inter = set(ms[0])
            for W in ms[1:]:
                inter &= set(W)
            if not any(deg[v] == 2 for v in inter):
                noshared += 1
            if any(not (set(a) & set(b)) for a in ms for b in ms if a != b):
                disj += 1
        if bricks(E):
            brickct += 1
        if hub_cycles(E):
            hcyc += 1
        assert f_of(E) <= 4, E
        assert eloc_witnesses(E), E
    print(f"  ... certified STRONG (no middle-zone contraction): {strong}")
    print(f"  ... max f(V(G)) over the pool: {maxf}   "
          f"(T32 sits at f = {f_of(T32)}, so (E) is TIGHT and the pool never "
          f"reached the extreme)")
    print(f"  #minimal count-dependent sets, distribution: {dict(sorted(hist.items()))}")
    print(f"  ... with TWO OR MORE (the only configuration that can refute "
          f"(E-loc)):        {sum(v for k, v in hist.items() if k >= 2)}")
    print(f"  ... with two DISJOINT dependent sets (shape 1):                   "
          f"       {disj}")
    print(f"  ... whose dependent sets share no degree-2 vertex ((E-loc) fails): "
          f"      {noshared}")
    print(f"  ... carrying a brick / a hub cycle (shape 2):              "
          f"        {brickct} / {hcyc}")
    print("  DISCLOSURE: the pool's structured families (`family_g`, "
          "`family_core_ring`) each build EXACTLY ONE core cycle, and the "
          "random sweeps contribute no residual at all (`saferes.py --search`: "
          "0 residuals from 584 + 343 random instances).  So the denominator "
          "for (E-loc) over this pool is not 255 — it is 0: no instance "
          "carries the configuration that decides the question.")


# ---------------- how big is the shape-1 family ----------------------------

def hunt():
    print("  the two-core family, scanned:  f(V(G)) = 22 - (4a + 2b)")
    best = None
    for m in (4, 5):
        for a in range(3, 7):
            for b in range(0, 5):
                E = two_core(a, b, m)
                st, _ = classify(E)
                n = len(verts_of(E))
                hits = eloc_witnesses(E) if st.endswith('CANDIDATE') else None
                mark = ''
                if st == 'STRONG-CANDIDATE' and hits == []:
                    mark = '  <= (E-loc) REFUTED here'
                    if best is None or n < best[0]:
                        best = (n, m, a, b)
                print(f"    m={m} a={a} b={b}: |V|={n:3d} f={f_of(E):4d} "
                      f"def={deficiency(E):3d} -> {st}{mark}")
    print(f"  smallest refuting instance in this family: |V| = {best[0]} "
          f"at (m, a, b) = {best[1:]}")
    print("  mixed core sizes (a C4 core and a C5 core in one residual):")
    for (m1, m2, a, b) in ((4, 5, 4, 1), (4, 5, 4, 2), (5, 4, 4, 1)):
        E = mixed_core(m1, m2, a, b)
        st, _ = classify(E)
        deps = dependent_sets(E)
        print(f"    m=({m1},{m2}) a={a} b={b}: |V|={len(verts_of(E))} "
              f"f={f_of(E)} -> {st}, minimal dependent sets "
              f"{[len(W) for W in deps]}, (E-loc) witnesses "
              f"{len(eloc_witnesses(E)) if st.endswith('CANDIDATE') else '-'}")
    print("  THREE cores: not run — the construction has 24 branches, past "
          "`rigid_vertex_sets`' 2^22 enumeration cap, so no instance of it "
          "can be CERTIFIED here.  Two disjoint cores already settle (E-loc), "
          "and this is recorded as a cap, not as an absence.")


def mixed_core(m1, m2, a=4, b=1):
    """`two_core` with the two cores of different lengths."""
    E = [(f'c{i}', f'c{(i + 1) % m1}') for i in range(m1)]
    E += [(f'd{i}', f'd{(i + 1) % m2}') for i in range(m2)]
    E += [('c0', 'z0'), ('c0', 'z1'), (f'c{m1 // 2}', 'z2'),
          ('d0', 'w0'), ('d0', 'w1'), (f'd{m2 // 2}', 'w2')]
    ring = ['z0', 'z1', 'z2', 'w0', 'w1', 'w2']
    legs = [a, a, b, a, a, b]
    for i in range(6):
        E += path_between(ring[i], ring[(i + 1) % 6], legs[i], f'r{i}_')
    return E


# ---------------- validation -----------------------------------------------

def validate():
    rng = random.Random(4242)
    print("  identity  f(W) = 5*c(G[W]) - |W| - 5*k(G[W]) + 6  (k = #components)")
    print("  and its connected form  f(W) = 5c - |W| + 1:")
    n_id = n_conn = 0
    for _ in range(2500):
        n = rng.randint(3, 8)
        vs = [f'q{i}' for i in range(n)]
        E = [(a, b) for (a, b) in combinations(vs, 2) if rng.random() < 0.45]
        if not E:
            continue
        V = verts_of(E)
        for _ in range(4):
            W = tuple(v for v in V if rng.random() < 0.7)
            if len(W) < 1:
                continue
            k = len(components(E, W))
            c = cycle_rank(E, W)
            assert f_of(E, W) == 5 * c - len(W) - 5 * k + 6, (E, W)
            n_id += 1
            if k == 1:
                assert f_of(E, W) == 5 * c - len(W) + 1
                n_conn += 1
    print(f"    {n_id} instances ({n_conn} connected), 0 mismatches")

    print("  count_indep (pebble game on the 5-fold fiber)  <->  "
          "f(W) <= 0 for every W:")
    n_ci = 0
    for _ in range(400):
        n = rng.randint(3, 7)
        vs = [f'q{i}' for i in range(n)]
        E = [(a, b) for (a, b) in combinations(vs, 2) if rng.random() < 0.5]
        if not E:
            continue
        V = sorted(verts_of(E), key=str)
        direct = all(f_of(E, W) <= 0
                     for k in range(1, len(V) + 1) for W in combinations(V, k))
        assert count_indep(E) == direct, E
        n_ci += 1
    print(f"    {n_ci} graphs, 0 disagreements")

    print("  minimal dependent sets: connected, min degree >= 2, branch-closed;"
          " and the branch enumeration is complete:")
    n_bf = n_sets = 0
    for _ in range(400):
        E = ns.random_subdivision(rng, rng.randint(3, 5), rng.randint(0, 3), 0, 2)
        if not is_simple(E) or not is_2ec(E):
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > 12 or len(verts_of(E)) > 14:
            continue
        got, want = dependent_sets(E), dependent_sets_bruteforce(E)
        assert got == want, (E, got, want)
        n_bf += 1
        for W in got:
            ie = induced_edges(E, W)
            assert len(components(E, W)) == 1
            assert all(d >= 2 for d in degrees(ie).values())
            n_sets += 1
    print(f"    {n_bf} subdivisions cross-checked against the brute-force "
          f"subset sweep ({n_sets} minimal dependent sets), 0 mismatches")

    print("  Ear Lemma threshold (H rigid + an ear of j interior vertices):")
    for j in range(0, 8):
        H = [('a0', 'a1'), ('a1', 'a2'), ('a2', 'a3'), ('a3', 'a0')]
        assert is_rigid(H)
        E = H + path_between('a0', 'a2', j, 'e_')
        print(f"    j = {j}: rigid = {is_rigid(E)}  (expect {j <= 5})")
        assert is_rigid(E) == (j <= 5)

    print("  (EL-1): a `PencilNondegFeasible` graph has every hub at <= 2 hub "
          "neighbours — this IS `hcard_ok`, restated:")
    n_h = 0
    for _ in range(600):
        E = ns.random_subdivision(rng, rng.randint(3, 6), rng.randint(0, 3), 0, 2)
        if not is_simple(E) or not hcard_ok(E):
            continue
        nb, hubs = neighbors(E), hub_set(E)
        for h in hubs:
            assert len({w for w in nb[h] if w in hubs}) <= 2
        n_h += 1
    print(f"    {n_h} `hcard` graphs, 0 hubs with 3 hub neighbours")
    print("  VALIDATE: OK")


def main():
    ran = False
    if '--validate' in sys.argv:
        print("== mechanical identities =="); validate(); ran = True
    if '--witness' in sys.argv:
        print("== T32: (E-loc) REFUTED =="); witness(); ran = True
    if '--brick' in sys.argv:
        print("== (EL-4): no residual carries a brick =="); brick(); ran = True
    if '--pool' in sys.argv:
        print("== denominator disclosure =="); pool(); ran = True
    if '--hunt' in sys.argv:
        print("== the shape-1 family =="); hunt(); ran = True
    if not ran:
        print(__doc__)


if __name__ == '__main__':
    main()
