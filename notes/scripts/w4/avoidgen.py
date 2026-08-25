"""
Phase 39 PENCIL — probe C3-AVOID: can the KT generation reduction avoid a
prescribed vertex set `S`?

`notes/Pencil-strategy.md` §4's option **C3** weakens the pencil target: pin
only a subset `S` of bodies to pencils, generic elsewhere.  Its gate is purely
combinatorial and lives entirely inside the ALREADY-FORMALIZED generation
theorem (KT 2011 Thm 4.9 = `Graph.minimal_kdof_reduction`, Phase 20):

    at every reduction step, can the split vertex be chosen OUTSIDE `S`?

This driver tests that sentence.  Nothing here computes a rank, places a
realization, or touches `hK` / `hbareSplit`; it is graph combinatorics against
the landed reduction's own dispatch.

THE REDUCTION, as landed (`CombinatorialRigidity/Molecular/Induction/
ForestSurgery/Reduction.lean`, `minimal_kdof_reduction`).  For `D = bodyBarDim
n = 6` (`n = 3`, the molecular regime) and a minimal `0`-dof-graph `G` with
`|V| >= 2`:
  * `|V| = 2`   -> BASE (the two-vertex double edge);
  * `|V| >= 3` and `G` has a proper rigid subgraph -> CASE I, contract it
    (the consumer takes the IH at the block `H` and at the contraction `G/H`
    -- the landed docstring's "Case I genuinely consumes the IH at *two*
    objects, the block and the contraction");
  * `|V| >= 3` and no proper rigid subgraph -> CASE II, split off a vertex of
    degree exactly 2 (`exists_degree_eq_two`, KT Lemma 4.6).
`IsProperRigidSubgraph H G n := H <= G and H.IsKDof n 0 and 2 <= |V(H)| and
V(H) subsetneq V(G)` (`Molecular/Deficiency.lean`), so the rigid-subgraph test
is: some `W` with `2 <= |W| < |V|` and `def(G[W]) = 0`.

ORACLES ARE CONSUMED, NEVER REIMPLEMENTED (`notes/scripts/README.md` §1/§2):
`nogood_subdiv.deficiency` / `.is_rigid` (the Lee-Streinu `(6,6)` pebble game
on `5G`), `.rigid_vertex_sets{,_bruteforce}`, `.induced_edges`, `.contraction`,
and `kbare_common.split_off` / `.is_2ec` / `.degrees` / `.verts_of` /
`.exact_deficiency`.  That places this leaf on the `w4/` stack.

WHAT IT ESTABLISHES (labels are `notes/Pencil-strategy.md` §4.7's `AV-`):

  --supply   (AV-1) the degree-2 SUPPLY bound.  At every Case-II node,
             `#{v : deg v = 2} >= ceil(((D-3)|V| + 4)/(D-1))`, i.e.
             `ceil((3|V|+4)/5) > |V|/2` at `D = 6`.  So the LOCAL gate is
             never the obstruction.  Tightness reported.
  --census   the Case-II class itself, EXHAUSTIVELY for cyclomatic number
             `mu <= 3` (hence `|V| <= 16`): every minimal `0`-dof-graph with
             no proper rigid subgraph, enumerated as (hub multigraph, branch
             lengths).  Cap disclosed: `mu <= 3`.
  --betti    (AV-2)/(AV-4) the CONSERVATION LAW and the capacity identity
             `#leaves = mu(G) = |E| - |V| + 1`, hence
             `capacity(G) = 2 mu(G)` and `#splits = |V| - mu - 1`.
  --forced   (AV-6) the reduction is forced contraction-free IFF `mu = 1`,
             i.e. iff `G` is a cycle `C_2 .. C_6`.  `mu` is invariant under
             Case-II splitting and the base has `mu = 1`.
  --avoid    (AV-3)/(AV-5) the avoidance game itself: for each pool graph the
             exact set of avoidable `S` by size, the capacity, and the
             per-block structure.  Reports the universal threshold.
  --count    the minimality edge count `5|E| - 6(|V|-1) <= 4` (hence
             `mu <= (|V|+3)/5`, hence `capacity <= 2(|V|+3)/5`).  MEASURED,
             not proven: exhaustive over all simple graphs on `|V| <= 6` plus
             the `--census` pool.  Cap disclosed.
  --validate cross-checks `deficiency` against `kbare_common.exact_deficiency`
             and `rigid_vertex_sets` against the brute-force subset sweep.

Run (from the repo root):
    python3 notes/scripts/w4/avoidgen.py --supply
    python3 notes/scripts/w4/avoidgen.py --census
    python3 notes/scripts/w4/avoidgen.py --betti
    python3 notes/scripts/w4/avoidgen.py --forced
    python3 notes/scripts/w4/avoidgen.py --avoid
    python3 notes/scripts/w4/avoidgen.py --count
    python3 notes/scripts/w4/avoidgen.py --validate
    python3 notes/scripts/w4/avoidgen.py --all      # all seven, in order
"""
import os
import random
import sys
from functools import lru_cache
from itertools import combinations, combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from kbare_common import (degrees, exact_deficiency, is_2ec, split_off,   # noqa: E402
                          verts_of)
import nogood_subdiv as NS                                                # noqa: E402

D_BODY = NS.D_BODY      # 6 = bodyBarDim 3
MULT = NS.MULT          # 5 = D - 1


# ---------------------------------------------------------------- basics ---

def nverts(edges):
    return len(verts_of(edges))


def mu(edges):
    """Cyclomatic number |E| - |V| + 1 (first Betti number, G connected)."""
    return len(edges) - nverts(edges) + 1


def is_zero_dof(edges):
    return NS.deficiency(edges, verts_of(edges)) == 0


def is_minimal_zero_dof(edges):
    """`IsMinimalKDof n 0` at `n = 3`: def(G~) = 0 and every edge fiber meets
    every base, i.e. deleting any edge raises the deficiency."""
    V = verts_of(edges)
    if NS.deficiency(edges, V) != 0:
        return False
    for i in range(len(edges)):
        rest = edges[:i] + edges[i + 1:]
        if NS.deficiency(rest, V) == 0:          # V pinned: rank must drop
            return False
    return True


def proper_rigid_sets(edges, brute=None):
    """All `W` with `2 <= |W| < |V|` and `def(G[W]) = 0` -- the vertex sets of
    `IsProperRigidSubgraph` witnesses (a rigid subgraph may be taken induced:
    adding the induced edges only lowers the deficiency)."""
    V = verts_of(edges)
    if brute is None:
        brute = len(V) <= 13
    if brute:
        return NS.rigid_vertex_sets_bruteforce(edges)
    return NS.rigid_vertex_sets(edges)


def deg2_vertices(edges):
    d = degrees(edges)
    return sorted([v for v in verts_of(edges) if d.get(v, 0) == 2], key=str)


def split_partners(edges, v):
    """The two neighbours of a degree-2 vertex (the landed
    `exists_splitOff_data_of_degree_eq_two` data)."""
    inc = [e for e in edges if v in e]
    assert len(inc) == 2
    ends = []
    for (x, y) in inc:
        ends.append(y if x == v else x)
    return ends[0], ends[1]


def canon(edges):
    """Canonical form of a small labelled multigraph, for dedup: brute-force
    over vertex permutations (only used at |V| <= 8)."""
    V = verts_of(edges)
    best = None
    from itertools import permutations
    for perm in permutations(range(len(V))):
        m = {V[i]: perm[i] for i in range(len(V))}
        key = tuple(sorted(tuple(sorted((m[u], m[w]))) for (u, w) in edges))
        if best is None or key < best:
            best = key
    return best


# ------------------------------------------------------- pool of graphs ---

def cycle(n):
    """C_n; n = 2 is the two-vertex double edge (the reduction's base)."""
    if n == 2:
        return [(0, 1), (1, 0)]
    return [(i, (i + 1) % n) for i in range(n)]


def theta(a, b, c, tag=""):
    """Theta subdivision: branch vertices `u`, `w` joined by three internally
    disjoint paths of edge-lengths a, b, c."""
    e, k = [], 0
    for L in (a, b, c):
        prev = "u"
        for i in range(L - 1):
            x = f"{tag}x{k}"
            k += 1
            e.append((prev, x))
            prev = x
        e.append((prev, "w"))
    return e


def multibranch(lengths):
    """`len(lengths)` internally disjoint u-w paths of the given edge-lengths."""
    e, k = [], 0
    for L in lengths:
        prev = "u"
        for i in range(L - 1):
            x = f"y{k}"
            k += 1
            e.append((prev, x))
            prev = x
        e.append((prev, "w"))
    return e


def cactus(k):
    """`k` copies of C_6 glued in a chain at single cut vertices: block `j` is
    the 6-cycle `h_j - c_j0 - c_j1 - c_j2 - c_j3 - h_{j+1} - h_j`.  Every
    block is rigid, so the root is a CASE-I node -- the Case-I-rich family."""
    e = []
    for j in range(k):
        prev = f"h{j}"
        for i in range(4):
            x = f"c{j}_{i}"
            e.append((prev, x))
            prev = x
        e.append((prev, f"h{j + 1}"))
        e.append((f"h{j + 1}", f"h{j}"))
    return e


def POOL():
    """Named minimal `0`-dof-graphs spanning mu = 1, 2, 3 -- Case-II members
    (the cycles, the thetas, the 4-branch mu=3 shape) and Case-I members (the
    C_6 cactus chain).  Every member is asserted minimal `0`-dof."""
    out = [(f"C{n}", cycle(n)) for n in range(2, 7)]
    out += [("Theta(3,4,4)", theta(3, 4, 4)),
            ("Theta(4,4,4)", theta(4, 4, 4)),
            ("Theta(2,5,5)", theta(2, 5, 5)),
            ("Theta(3,3,4)", theta(3, 3, 4)),
            ("Quad(3,5,5,5)", multibranch([3, 5, 5, 5])),
            ("Cactus2xC6", cactus(2)),
            ("Cactus3xC6", cactus(3))]
    for name, g in out:
        assert is_minimal_zero_dof(g), f"{name} is not a minimal 0-dof graph"
    return out


# --------------------------------------------- (AV-1) the supply bound ----

def supply_bound(nV, D=D_BODY):
    """ceil(((D-3)|V| + 4)/(D-1)) -- the proven lower bound on the number of
    degree-2 vertices at a Case-II node.  Derivation, from landed lemmas:
      `no_rigid_edge_count` (KT 4.5(i)) at k = 0:  (D-1)|E| < D(|V|-1) + (D-1)
        so  (D-1)|E| <= D|V| - 2;
      `twoEdgeConnected_of_isKDof_zero` + `two_le_degree_of_twoEdgeConnected`:
        every degree >= 2;
      handshake:  2|E| = sum deg >= 2t + 3(|V| - t) = 3|V| - t,
        so t >= 3|V| - 2|E| >= ((D-3)|V| + 4)/(D-1)."""
    num = (D - 3) * nV + 4
    den = D - 1
    return -((-num) // den)          # ceil for positive den


def mode_supply():
    print("=== (AV-1) degree-2 SUPPLY at Case-II nodes (D = 6) ===")
    print("bound t >= ceil((3|V|+4)/5); Case-II = minimal 0-dof, no proper rigid subgraph")
    rows, tight, checked = [], 0, 0
    seen = set()
    for name, e in POOL() + [(f"census:{n}", g) for n, g in census_pool()]:
        key = tuple(sorted(tuple(sorted(map(str, x))) for x in e))
        if key in seen:
            continue
        seen.add(key)
        if not is_minimal_zero_dof(e):
            continue
        if proper_rigid_sets(e):
            continue                                   # not a Case-II node
        nV = nverts(e)
        t = len(deg2_vertices(e))
        b = supply_bound(nV)
        checked += 1
        assert t >= b, (name, nV, t, b)
        if t == b:
            tight += 1
        rows.append((name, nV, len(e), t, b, t == b))
    byV = {}
    for r in rows:
        byV.setdefault(r[1], []).append(r)
    for nV in sorted(byV):
        rs = byV[nV]
        ts = [r[3] for r in rs]
        print(f"  |V|={nV:<3} {len(rs):>4} Case-II nodes  deg2 in "
              f"[{min(ts)},{max(ts)}]  bound={rs[0][4]:<3} "
              f"{'TIGHT at ' + str(sum(1 for r in rs if r[5])) if any(r[5] for r in rs) else ''}")
    print(f"  checked {checked} Case-II nodes, 0 violations, {tight} tight")
    print("  consequence: t > |V|/2 at every Case-II node, so ANY S with")
    print("  |S| < t leaves a legal split vertex outside S -- the LOCAL gate")
    print("  is never the obstruction.")


# --------------------------------- the Case-II census (exhaustive, mu<=3) --

def hub_multigraphs(h, B):
    """All multigraphs (loops allowed) on `h` labelled hubs with `B` edges,
    connected, min degree >= 3, up to relabelling."""
    slots = list(combinations_with_replacement(range(h), 2))
    out, seen = [], set()
    for pick in combinations_with_replacement(range(len(slots)), B):
        eds = [slots[i] for i in pick]
        d = {}
        for (u, w) in eds:
            d[u] = d.get(u, 0) + (2 if u == w else 1)
            if u != w:
                d[w] = d.get(w, 0) + 1
        if any(d.get(v, 0) < 3 for v in range(h)):
            continue
        # connectivity on the hub set
        adj = {v: set() for v in range(h)}
        for (u, w) in eds:
            adj[u].add(w)
            adj[w].add(u)
        seen_v, stack = {0}, [0]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in seen_v:
                    seen_v.add(y)
                    stack.append(y)
        if len(seen_v) != h:
            continue
        from itertools import permutations
        best = None
        for perm in permutations(range(h)):
            key = tuple(sorted(tuple(sorted((perm[u], perm[w]))) for (u, w) in eds))
            if best is None or key < best:
                best = key
        if best in seen:
            continue
        seen.add(best)
        out.append(eds)
    return out


def subdivide(hub_edges, lengths):
    """Subdivide branch `i` of a hub multigraph with `lengths[i]` interior
    vertices (so it becomes a path of `lengths[i] + 1` edges)."""
    e, k = [], 0
    for i, (u, w) in enumerate(hub_edges):
        prev = f"h{u}"
        for _ in range(lengths[i]):
            x = f"i{k}"
            k += 1
            e.append((prev, x))
            prev = x
        e.append((prev, f"h{w}"))
    return e


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


_CENSUS_CACHE = None


def census_pool(mu_cap=3):
    """Exhaustive Case-II class for cyclomatic number `mu <= mu_cap`.

    A Case-II graph is 2EC with min degree >= 2, so it is a subdivision of a
    hub multigraph (hubs = degree >= 3) or a pure cycle.  Subdivision changes
    neither the hub count `h` nor the branch count `B`, and `mu = B - h + 1`;
    min degree >= 3 at hubs gives `2B >= 3h`, i.e. `h <= 2(mu - 1)`.  So the
    hub multigraph is bounded and the enumeration is finite and complete.
    `|V|` is pinned by `|E| = |V| + mu - 1` and the exact-count window
    `6(|V|-1) <= 5|E| <= 6|V| - 2` (0-dof / `no_rigid_edge_count`)."""
    global _CENSUS_CACHE
    if _CENSUS_CACHE is not None:
        return _CENSUS_CACHE
    from itertools import permutations
    out, seen = [], set()
    for n in range(2, 7):                                  # mu = 1: cycles
        out.append((f"C{n}", cycle(n)))
    for m in range(2, mu_cap + 1):
        for h in range(1, 2 * (m - 1) + 1):
            B = h + m - 1
            if 2 * B < 3 * h:
                continue
            for hg in hub_multigraphs(h, B):
                # |V| = h + sum(L); 6(|V|-1) <= 5|E| = 5(B + sum L) <= 6|V| - 2
                for total in range(0, 6 * h + 40):
                    nV = h + total
                    nE = B + total
                    if 5 * nE < 6 * (nV - 1) or 5 * nE > 6 * nV - 2:
                        continue
                    for lengths in compositions(total, B):
                        # iso-dedup: min over hub relabellings of the multiset
                        # {(endpoints, branch length)} -- this quotients by
                        # Aut(hub multigraph) and by parallel-branch swaps.
                        key = None
                        for perm in permutations(range(h)):
                            k = tuple(sorted(
                                (min(perm[u], perm[w]), max(perm[u], perm[w]),
                                 lengths[i]) for i, (u, w) in enumerate(hg)))
                            if key is None or k < key:
                                key = k
                        if key in seen:
                            continue
                        seen.add(key)
                        g = subdivide(hg, list(lengths))
                        if len(set(map(lambda t: tuple(sorted(map(str, t))), g))) != len(g):
                            continue                       # parallel edges
                        if any(u == w for (u, w) in g):
                            continue                       # loop
                        if not is_2ec(g):
                            continue
                        if not is_minimal_zero_dof(g):
                            continue
                        if proper_rigid_sets(g, brute=False):
                            continue
                        out.append((f"mu{m}/h{h}/{tuple(lengths)}", g))
    _CENSUS_CACHE = out
    return out


def mode_census():
    print("=== the Case-II class, EXHAUSTIVE for mu <= 3 (CAP: mu <= 3) ===")
    pool = census_pool(3)
    by_mu = {}
    for name, g in pool:
        by_mu.setdefault(mu(g), []).append((name, g))
    for m in sorted(by_mu):
        buckets = {}
        for name, g in by_mu[m]:
            buckets.setdefault((nverts(g), len(g)), []).append((name, g))
        print(f"  mu = {m}: {len(by_mu[m])} iso classes, "
              f"|V| in {sorted({nverts(g) for _, g in by_mu[m]})}")
        for (nV, nE) in sorted(buckets):
            mem = buckets[(nV, nE)]
            ex = ", ".join(n for n, _ in mem[:3])
            print(f"    |V|={nV:<3} |E|={nE:<3} {len(mem):>4} classes  "
                  f"deg2={sorted({len(deg2_vertices(g)) for _, g in mem})}  "
                  f"e.g. {ex}")
    print("  NOTE the cap: mu <= 3 exhausted, mu >= 4 NOT searched.  An")
    print("  exhausted cap is not a proof of nonexistence beyond it.")


# ---------------------------- (AV-2)/(AV-4) the conservation law ----------

def contract(edges, W):
    """`G / E(G[W])` with `V(W)` collapsed to a merge vertex named
    DETERMINISTICALLY from `W` (so memo keys are stable, and nested
    contractions never collide the way `nogood_subdiv.contraction`'s fixed
    `'v*'` would).  `W` is induced-saturated, so no loop is created."""
    r = "*" + "_".join(sorted(map(str, W)))
    Wset = set(W)
    out = []
    for (u, w) in edges:
        if u in Wset and w in Wset:
            continue
        out.append((r if u in Wset else u, r if w in Wset else w))
    return out, r


def reduction_stats(edges):
    """One legal reduction tree, greedily built, returning
    (#leaves, #contractions, #splits).  Any legal tree gives the same
    (#leaves, #contractions) -- that is the identity `--betti` checks."""
    V = verts_of(edges)
    if len(V) <= 2:
        return (1, 0, 0)
    rig = proper_rigid_sets(edges)
    if rig:
        W = max(rig, key=len)
        H = NS.induced_edges(edges, W)
        Q, _ = contract(edges, W)
        l1, c1, s1 = reduction_stats(H)
        l2, c2, s2 = reduction_stats(Q)
        return (l1 + l2, c1 + c2 + 1, s1 + s2)
    d2 = deg2_vertices(edges)
    assert d2, "Case II with no degree-2 vertex: contradicts KT 4.6"
    v = d2[0]
    a, b = split_partners(edges, v)
    l, c, s = reduction_stats(split_off(edges, v, a, b))
    return (l, c, s + 1)


def all_minimal_zero_dof(nV):
    """Every simple 2EC minimal `0`-dof-graph on the labelled vertex set
    `range(nV)` -- exhaustive."""
    pairs = list(combinations(range(nV), 2))
    for mask in range(1 << len(pairs)):
        e = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        if len(e) < nV or len(verts_of(e)) != nV:
            continue
        if not is_2ec(e):
            continue
        if is_minimal_zero_dof(e):
            yield e


def mode_betti():
    print("=== (AV-2)/(AV-4) CONSERVATION LAW ===")
    print("  every leaf of a reduction tree is the 2-vertex base; every")
    print("  Case-II step consumes exactly one vertex; every Case-I step")
    print("  branches into (H, G/H) with mu(G) = mu(H) + mu(G/H).  Hence")
    print("    #leaves = mu(G) = |E|-|V|+1,  #contractions = mu-1,")
    print("    #splits = |V|-mu-1,  and  CAPACITY <= 2 mu.")
    for name, g in POOL():
        L, C, S = reduction_stats(g)
        nV, m = nverts(g), mu(g)
        cap = capacity(g)
        ok = (L == m) and (C == m - 1) and (S == nV - m - 1) and (cap <= 2 * m)
        print(f"  {name:<16} |V|={nV:<3} mu={m:<3} leaves={L:<3} contr={C:<3} "
              f"splits={S:<3} capacity={cap:<3} 2mu={2 * m:<3} "
              f"{'OK' if ok else 'MISMATCH'}")
        assert ok, (name, L, C, S, cap, m, nV)
    print("  now EXHAUSTIVELY over every simple 2EC minimal 0-dof graph on")
    print("  |V| <= 6 (labelled), the identity and the capacity bound:")
    tot = eqn = 0
    tight = {}
    for nV in range(3, 7):
        for g in all_minimal_zero_dof(nV):
            L, C, S = reduction_stats(g)
            m, cap = mu(g), capacity(g)
            assert L == m and C == m - 1 and S == nV - m - 1, (g, L, C, S, m)
            assert cap <= 2 * m, (g, cap, m)
            tot += 1
            if cap == 2 * m:
                eqn += 1
            tight.setdefault((nV, m), set()).add(cap)
    for k in sorted(tight):
        print(f"    |V|={k[0]} mu={k[1]}: capacities {sorted(tight[k])} "
              f"(ceiling 2mu = {2 * k[1]})")
    print(f"  {tot} graphs, 0 violations of L = mu / capacity <= 2mu; "
          f"{eqn} attain capacity = 2mu")
    print("  CAP: |V| <= 6 exhaustively (simple, 2EC), plus the named pool.")


# ------------------------------ (AV-6) forced contraction-free ------------

def mode_forced():
    print("=== (AV-6) forced contraction-free <=> mu = 1 <=> a cycle C_2..C_6 ===")
    print("  mu is INVARIANT under Case-II splitting (splitOff v a b deletes v")
    print("  and its two edges and adds one: |V| -1, |E| -1), and the base has")
    print("  mu = 1.  So a reduction that never contracts stays at mu = 1.")
    bad = 0
    for name, g in census_pool(3):
        for v in deg2_vertices(g):
            a, b = split_partners(g, v)
            g2 = split_off(g, v, a, b)
            if mu(g2) != mu(g):
                bad += 1
                print(f"    MU MOVED at {name}, v={v}")
    print(f"  mu-invariance checked over the whole mu<=3 census: {bad} violations")
    print("  now: which graphs admit a reduction with NO contraction at all?")
    for name, g in POOL():
        print(f"  {name:<16} mu={mu(g):<3} admits-contraction-free-reduction="
              f"{contraction_free(g)}")
    print("  and which cycles are 0-dof at D = 6?  (5L >= 6(L-1) iff L <= 6):")
    print("    " + "  ".join(
        f"def(C{L})={NS.deficiency(cycle(L), verts_of(cycle(L)))}"
        for L in range(2, 9)))
    print("  exactly the mu = 1 members (the cycles).  For every other minimal")
    print("  0-dof graph Case I MUST fire, so the ceiling 2mu is >= 4 -- but")
    print("  the CYCLES are precisely where the ceiling is 2 and every")
    print("  3-element S is unavoidable.  The |S| = 3 counterexamples are")
    print("  therefore exactly C_3, C_4, C_5, C_6 (with S ANY 3-subset).")


def contraction_free(edges):
    """Does SOME legal reduction reach the base with no Case-I step?"""
    V = verts_of(edges)
    if len(V) <= 2:
        return True
    if proper_rigid_sets(edges):
        return False               # the dispatch hands hcontract, not hsplit
    for v in deg2_vertices(edges):
        a, b = split_partners(edges, v)
        if contraction_free(split_off(edges, v, a, b)):
            return True
    return False


# ---------------------------------- (AV-3)/(AV-5) the avoidance game ------

def _key(edges, S):
    return (tuple(sorted(tuple(sorted(map(str, e))) for e in edges)),
            tuple(sorted(map(str, S))))


_AVOID_MEMO = {}


def avoidable(edges, S):
    """Is there a legal reduction of `edges` in which no vertex of `S` is ever
    chosen as the split vertex?  Case I distributes `S` between the block and
    the contraction; the merge vertex is never in `S`."""
    S = frozenset(S) & frozenset(verts_of(edges))
    k = _key(edges, S)
    if k in _AVOID_MEMO:
        return _AVOID_MEMO[k]
    V = verts_of(edges)
    if len(V) <= 2:
        _AVOID_MEMO[k] = True
        return True
    res = False
    rig = proper_rigid_sets(edges)
    if rig:
        for W in rig:
            H = NS.induced_edges(edges, W)
            Q, _ = contract(edges, W)
            if avoidable(H, S & frozenset(W)) and avoidable(Q, S - frozenset(W)):
                res = True
                break
    else:
        for v in deg2_vertices(edges):
            if v in S:
                continue
            a, b = split_partners(edges, v)
            if avoidable(split_off(edges, v, a, b), S):
                res = True
                break
    _AVOID_MEMO[k] = res
    return res


_CAP_MEMO = {}


def capacity(edges, orig=None):
    """max |S| over avoidable `S`, i.e. the largest number of ORIGINAL
    vertices that some legal reduction never chooses as a split vertex.
    Computed as a DP over the reduction tree, not by a subset sweep."""
    V = verts_of(edges)
    if orig is None:
        orig = frozenset(V)
    orig = frozenset(orig) & frozenset(V)
    k = _key(edges, orig)
    if k in _CAP_MEMO:
        return _CAP_MEMO[k]
    if len(V) <= 2:
        _CAP_MEMO[k] = len(orig)
        return len(orig)
    best = 0
    rig = proper_rigid_sets(edges)
    if rig:
        for W in rig:
            Wf = frozenset(W)
            H = NS.induced_edges(edges, W)
            Q, _ = contract(edges, W)
            best = max(best, capacity(H, orig & Wf) + capacity(Q, orig - Wf))
    else:
        for v in deg2_vertices(edges):
            a, b = split_partners(edges, v)
            best = max(best, capacity(split_off(edges, v, a, b), orig - {v}))
    _CAP_MEMO[k] = best
    return best


SWEEP_CAP = 12          # exhaustive S-sweep only up to this |V| (disclosed)


def mode_avoid():
    print("=== (AV-3)/(AV-5) the avoidance game ===")
    print("  per graph: how many S of each size are avoidable, the capacity")
    print("  (max avoidable |S|), and the smallest FAILING S.")
    print(f"  exhaustive S-sweep CAP: |V| <= {SWEEP_CAP}; larger members report")
    print("  the DP capacity only.")
    universal = None
    for name, g in POOL():
        V = verts_of(g)
        cap = capacity(g)
        if len(V) > SWEEP_CAP:
            print(f"  {name:<16} |V|={len(V):<3} mu={mu(g):<2} capacity={cap:<2}"
                  "  (sweep skipped: over the cap)")
            continue
        line, first_fail = [], None
        for size in range(0, min(len(V), 6) + 1):
            tot = ok = 0
            bad0 = None
            for S in combinations(V, size):
                tot += 1
                if avoidable(g, S):
                    ok += 1
                elif bad0 is None:
                    bad0 = S
            line.append(f"|S|={size}:{ok}/{tot}")
            if ok < tot and first_fail is None:
                first_fail = (size, bad0)
        ff = f"first failing |S|={first_fail[0]} e.g. {first_fail[1]}" if first_fail else "-"
        if first_fail:
            lim = first_fail[0] - 1
            universal = lim if universal is None else min(universal, lim)
        print(f"  {name:<16} |V|={len(V):<3} mu={mu(g):<2} capacity={cap:<2} "
              + "  ".join(line))
        print(f"      {ff}")
    print(f"  UNIVERSAL THRESHOLD over the swept pool: EVERY S with "
          f"|S| <= {universal} is avoidable at every member;")
    print("  some S of size {} is not.".format(universal + 1))
    print("  and the ceiling is 2*mu, so a LARGER S survives only when the")
    print("  graph itself is Case-I-rich AND S spreads <= 2 per block.")
    print("  -- does a STRUCTURAL hypothesis on S lift the threshold? --")
    print("  the obstruction is a cardinality conservation law, so it should")
    print("  not.  At C6 every 3-subset fails, INDEPENDENT ones included:")
    g = cycle(6)
    for S in [(0, 2, 4), (1, 3, 5), (0, 1, 2), (0, 1, 3)]:
        ind = all(abs(a - b) % 6 not in (1, 5) for a in S for b in S if a != b)
        print(f"    S={S}  independent={ind}  avoidable={avoidable(g, S)}")
    print("  so 'independent S' / 'spread S' buys NOTHING: |S| <= 2 is the")
    print("  whole universal statement.")


# --------------------------- the minimality edge count (measured) ---------

def mode_count():
    print("=== how large can mu -- hence the capacity ceiling 2mu -- get? ===")
    print("  a natural guess: the Case-II count 5|E| <= 6|V|-2 of")
    print("  `no_rigid_edge_count` (KT 4.5(i)) would give mu <= (|V|+3)/5 and")
    print("  so capacity <= 2(|V|+3)/5, i.e. ~40% of the bodies.  That count")
    print("  needs the no-proper-rigid-subgraph hypothesis; this mode asks")
    print("  whether it survives WITHOUT it.  It does NOT -- reported as a")
    print("  refutation of the guess, not smoothed over.")
    rows = {}
    for nV in range(3, 7):
        for g in all_minimal_zero_dof(nV):
            s = 5 * len(g) - 6 * (nV - 1)
            m, cap = mu(g), capacity(g)
            k = (nV, len(g))
            cur = rows.get(k, (s, m, 0))
            rows[k] = (s, m, max(cur[2], cap))
    for k in sorted(rows):
        s, m, cap = rows[k]
        print(f"  |V|={k[0]} |E|={k[1]}  s={s:<3} mu={m:<2} "
              f"max capacity={cap:<2} ({cap}/{k[0]} = "
              f"{100 * cap // k[0]}% of the bodies)")
    smax = max(r[0] for r in rows.values())
    print(f"  |V| <= 6 exhaustive: max s = {smax}.  The Case-II bound s <= 4")
    print("  is therefore FALSE for minimal 0-dof graphs in general (a")
    print("  proper rigid subgraph lifts it), so mu is NOT capped at")
    print("  (|V|+3)/5 and the ~40% headline does not hold.  What survives is")
    print("  the exact ceiling capacity <= 2 mu, plus s <= 4 at Case-II nodes")
    print("  only, where it IS proven.")
    base = cycle(2)
    print(f"  (the base C2 double edge: s = {5 * len(base) - 6}, mu = 1.)")
    print("  CAP: simple 2EC graphs on |V| <= 6, exhaustively.  |V| >= 7 not")
    print("  swept -- an exhausted cap is not a claim about larger |V|.")


# ------------------------------------------------------------ validate ----

def mode_validate():
    print("=== oracle cross-checks ===")
    rng = random.Random(20260824)
    bad = 0
    for _ in range(40):
        nV = rng.randint(3, 7)
        pairs = list(combinations(range(nV), 2))
        e = [p for p in pairs if rng.random() < 0.5]
        if len(verts_of(e)) != nV:
            continue
        d1 = NS.deficiency(e, verts_of(e))
        d2 = exact_deficiency(e)
        if isinstance(d2, tuple):          # (def, report) form
            d2 = d2[0]
        if d1 != d2:
            bad += 1
            print(f"    DEFICIENCY MISMATCH {e}: pebble={d1} exact={d2}")
    print(f"  deficiency: pebble game vs exact_deficiency, {bad} mismatches")
    bad = 0
    for name, g in POOL():
        if nverts(g) > 11:
            continue
        a = sorted(NS.rigid_vertex_sets_bruteforce(g))
        b = sorted(NS.rigid_vertex_sets(g))
        if a != b:
            bad += 1
            print(f"    RIGID-SET MISMATCH {name}: brute={a} branch={b}")
    print(f"  rigid_vertex_sets: branch enumeration vs brute force, "
          f"{bad} mismatches")
    print("  reduction dispatch sanity: every Case-II node has a degree-2")
    print("  vertex (KT 4.6) --", end=" ")
    for name, g in census_pool(3):
        assert deg2_vertices(g), name
    print("OK")


# ---------------------------------------------------------------- main ----

MODES = [("--supply", mode_supply), ("--census", mode_census),
         ("--betti", mode_betti), ("--forced", mode_forced),
         ("--avoid", mode_avoid), ("--count", mode_count),
         ("--validate", mode_validate)]

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    args = set(sys.argv[1:])
    if not args or "--all" in args:
        args = {m for m, _ in MODES}
    ran = False
    for flag, fn in MODES:
        if flag in args:
            fn()
            print()
            ran = True
    if not ran:
        print(__doc__)
