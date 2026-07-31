"""
Phase 39 W4-L4 recon — combinatorial search for residual-branch inhabitants.

The W4 dispatch's vertex-removal branch (design doc, section "W4-L4
identification recon") splits by whether G has a CO-1 proper rigid subgraph
(some vertex v with G - v rigid).  The co-1 case is closed minimality-free
(the identification lemma pinned there).  The residual carried hypothesis
`hnoGood'` covers: G simple, 2EC, feasible, with a proper rigid subgraph,
NO co-1 rigid subgraph, and NO (H, r) whose contraction is simple and
feasible.  This script searches for inhabitants of that residual habitat.

Feasibility proxies (PencilNondegFeasible has no combinatorial
characterization; all directions below are landed-lemma-backed):
  * provably feasible  := hcard (every closedHubNbhd <= 3) AND (triangle-free
    [the L6b sufficient condition] OR the graph is the spanning C3 [the
    landed L7c-3 witness, `pencilPair_of_habitat_ncard_eq_three`'s generic
    half]).
  * provably infeasible := NOT hcard [the landed necessity bound] OR some
    triangle with >= 2 degree->=3 vertices [the landed
    `not_pencilNondegFeasible_of_triangle_two_hubs`].
  * middle zone := neither (e.g. graphs with hcard and only <=1-hub
    triangles beyond C3) -- true feasibility unknown to landed lemmas.
  Candidate classification: STRONG-CANDIDATE = every rigid subgraph's
  contraction is non-simple or provably infeasible (a certified residual
  inhabitant, modulo G's own middle zone); MIDDLE-CANDIDATE = no provably
  good contraction, but some contraction is simple + middle-zone (residual
  membership undecided by landed lemmas).

First-run correction (2026-07-30): the coarse two-way proxy flagged one
candidate (B #351: two adjacent degree-4 hubs joined by three length-3
paths), which dissolves under the refined classifier -- contracting its
rigid 6-vertex theta leaves the spanning C3, a provably GOOD contraction.
Kept as a regression check below (`B351`).

Rigid-subgraph enumeration: a rigid subgraph on vertex set W exists iff the
INDUCED subgraph G[W] has deficiency 0 (induced maximizes edges, deficiency
is antitone in edges).  For the no-good-contraction trigger it suffices to
check induced-saturated H (a non-induced H leaves an inner edge as a LOOP at
v*, so its contraction is never simple).

Families searched:
  * A1: cycle C_m + 3 anchored hub gadgets joined by an outer cycle of
    paths (the hub-concentration mechanism m1 at v*), all small parameter
    combinations.
  * A2: cycle C_m + an adjacent anchored pair w1~w2 + an anchored path
    gadget (the triangle mechanism m2 at v*), small variants.
  * B: random sparse simple 2EC graphs.

Run:  python3 notes/scripts/w4/no_good_search.py [nrandom]
"""
import os
import random
import sys
from itertools import combinations, product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'kbare'))
from kbare_common import (exact_deficiency, verts_of, neighbors, degrees,
                          is_2ec, closed_hub_nbhds)


# ---------------- predicates ----------------

def is_simple(edges):
    seen = set()
    for u, w in edges:
        if u == w:
            return False
        key = frozenset((u, w))
        if key in seen:
            return False
        seen.add(key)
    return True


def has_triangle(edges):
    nb = neighbors(edges)
    for u, w in edges:
        if set(nb.get(u, ())) & set(nb.get(w, ())):
            return True
    return False


def hcard_ok(edges):
    return all(c <= 3 for c in closed_hub_nbhds(edges).values())


def is_spanning_c3(edges):
    V = verts_of(edges)
    if len(V) != 3 or len(edges) != 3:
        return False
    return {frozenset(e) for e in edges} == {frozenset((V[0], V[1])),
                                             frozenset((V[1], V[2])),
                                             frozenset((V[0], V[2]))}


def provably_feasible(edges):
    """L6b (hcard + triangle-free) OR the landed spanning-C3 witness."""
    return hcard_ok(edges) and (not has_triangle(edges)
                                or is_spanning_c3(edges))


def provably_infeasible(edges):
    """NOT hcard, or a triangle with >= 2 hubs (both landed)."""
    if not hcard_ok(edges):
        return True
    deg = degrees(edges)
    nb = neighbors(edges)
    for u, w in edges:
        for x in set(nb.get(u, ())) & set(nb.get(w, ())):
            if sum(1 for y in (u, w, x) if deg.get(y, 0) >= 3) >= 2:
                return True
    return False


def induced_edges(edges, W):
    Wset = set(W)
    return [e for e in edges if e[0] in Wset and e[1] in Wset]


def contraction(edges, W):
    """G / E(G[W]) with W collapsed to 'v*'; returns edge list (may have
    parallel edges / loops, kept as-is for the simplicity check)."""
    Wset = set(W)
    out = []
    for (u, w) in edges:
        if u in Wset and w in Wset:
            continue  # E(G[W]) deleted (induced-saturated H)
        uu = 'v*' if u in Wset else u
        ww = 'v*' if w in Wset else w
        out.append((uu, ww))
    return out


def rigid_induced_subsets(edges):
    """All W subsetneq V, |W| >= 2, with def(G[W]) = 0 and G[W] having a
    nonempty edge set on every vertex... (deficiency of an induced subgraph
    with isolated vertices: an isolated vertex makes a 1-vertex part with no
    crossing edges -> partition def 6(|P|-1) - 5d unbounded? no: isolated
    vertices simply sit in parts; def(G[W]) = 0 still meaningful).  We
    additionally require G[W] connected-ish via 'every vertex has an edge'
    to skip degenerate W (a rigid graph has min degree 2 anyway)."""
    V = verts_of(edges)
    n = len(V)
    out = []
    for k in range(2, n):
        for W in combinations(V, k):
            ie = induced_edges(edges, W)
            deg = degrees(ie)
            if any(deg.get(v, 0) < 2 for v in W):
                continue  # rigid needs min degree 2
            d, _ = exact_deficiency(ie)
            if d == 0 and set(verts_of(ie)) == set(W):
                out.append(W)
    return out


def classify(edges, verbose=False):
    """Returns (status, info).  status in:
    'too-big', 'not-simple', 'not-2ec', 'not-feasible', 'no-rigid', 'co-1',
    'good-contraction', 'MIDDLE-CANDIDATE', 'STRONG-CANDIDATE'."""
    if len(verts_of(edges)) > 13:
        return 'too-big', None
    if not is_simple(edges):
        return 'not-simple', None
    if not is_2ec(edges):
        return 'not-2ec', None
    if not provably_feasible(edges):
        return 'not-feasible', None
    V = verts_of(edges)
    rig = rigid_induced_subsets(edges)
    if not rig:
        return 'no-rigid', None
    if any(len(W) == len(V) - 1 for W in rig):
        return 'co-1', None
    middles = []
    for W in rig:
        c = contraction(edges, W)
        if is_simple(c):
            if provably_feasible(c):
                return 'good-contraction', W
            if not provably_infeasible(c):
                middles.append(W)
    if middles:
        return 'MIDDLE-CANDIDATE', (rig, middles)
    return 'STRONG-CANDIDATE', rig


# ---------------- family A1: cycle + 3 hub gadgets ----------------

def family_a1(m, anchors, lengths):
    """C_m(0..m-1) + hubs u0,u1,u2 anchored at `anchors`, outer paths
    u0-..-u1, u1-..-u2, u2-..-u0 with `lengths` interior vertices."""
    edges = [(i, (i + 1) % m) for i in range(m)]
    for i, a in enumerate(anchors):
        edges.append((f'u{i}', a))
    for i, L in enumerate(lengths):
        a, b = f'u{i}', f'u{(i + 1) % 3}'
        prev = a
        for j in range(L):
            v = f'p{i}_{j}'
            edges.append((prev, v))
            prev = v
        edges.append((prev, b))
    return edges


# ---------------- family A2: cycle + adjacent pair + path gadget ----------

def family_a2(m, a1, a2, a3, L):
    """C_m + w1~w2 (anchored at a1, a2) + path w1-q0-..-q(L-1) with the far
    end anchored at a3 (so v* sees w1, w2, and the far end; the contraction
    has triangle {v*, w1, w2})."""
    edges = [(i, (i + 1) % m) for i in range(m)]
    edges += [('w1', 'w2'), ('w1', a1), ('w2', a2)]
    prev = 'w1'
    for j in range(L):
        v = f'q{j}'
        edges.append((prev, v))
        prev = v
    edges.append((prev, a3))
    return edges


# ---------------- family B: random sparse ----------------

def random_graph(rng, n, m):
    V = list(range(n))
    all_pairs = [(u, w) for u in V for w in V if u < w]
    if m > len(all_pairs):
        return None
    return rng.sample(all_pairs, m)


# ---------------- family C: two adjacent hubs + long paths ----------------

def family_c(k, lengths, hub_edge):
    """Hubs X, Y joined by k paths with `lengths[i]` interior vertices
    (>= 2 kills co-1) and optionally the direct edge X-Y (the B #351
    family generalized)."""
    edges = [('X', 'Y')] if hub_edge else []
    for i in range(k):
        prev = 'X'
        for j in range(lengths[i]):
            v = f'r{i}_{j}'
            edges.append((prev, v))
            prev = v
        edges.append((prev, 'Y'))
    return edges


B351 = [(0, 6), (0, 5), (4, 5), (0, 1), (3, 6), (3, 5), (1, 7), (0, 2),
        (5, 7), (2, 4)]


# ---------------- driver ----------------

def main():
    nrandom = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(3944)
    tallies = {}
    candidates = []

    def record(tag, edges):
        status, info = classify(edges)
        tallies[status] = tallies.get(status, 0) + 1
        if status in ('STRONG-CANDIDATE', 'MIDDLE-CANDIDATE'):
            candidates.append((status, tag, edges, info))
            print(f"  {status} [{tag}]: {edges}")

    print("== regression: B #351 (first run's coarse-proxy candidate) ==")
    status, W = classify(B351)
    print(f"  B351 -> {status} (via rigid subset {W})")
    assert status == 'good-contraction', "B351 regression failed"

    print("== family A1 (cycle + 3 hub gadgets; mechanism m1) ==")
    for m in (5, 6, 7, 8):
        anchor_sets = list(combinations(range(m), 3))
        for anchors in anchor_sets:
            for lengths in product((1, 2, 3), repeat=3):
                record(f"A1 m={m} anc={anchors} L={lengths}",
                       family_a1(m, anchors, lengths))
    print(f"  tallies so far: {tallies}")

    print("== family A2 (cycle + adjacent pair + path; mechanism m2) ==")
    for m in (5, 6, 7):
        for a1 in range(m):
            for a2 in range(m):
                for a3 in range(m):
                    if len({a1, a2, a3}) < 3:
                        continue
                    for L in (1, 2, 3):
                        record(f"A2 m={m} a=({a1},{a2},{a3}) L={L}",
                               family_a2(m, a1, a2, a3, L))
    print(f"  tallies so far: {tallies}")

    print(f"== family B ({nrandom} random sparse graphs) ==")
    for i in range(nrandom):
        n = rng.randint(7, 11)
        m = rng.randint(n, n + 3)
        edges = random_graph(rng, n, m)
        if edges is None:
            continue
        record(f"B #{i} n={n} m={m}", edges)
    print(f"  tallies so far: {tallies}")

    print("== family C (two adjacent hubs + k long paths; B #351 family) ==")
    for k in (3, 4):
        for hub_edge in (True, False):
            for lengths in product((2, 3), repeat=k):
                record(f"C k={k} he={hub_edge} L={lengths}",
                       family_c(k, lengths, hub_edge))

    print(f"final tallies: {tallies}")
    print(f"candidates found: {len(candidates)}")
    for status, tag, edges, info in candidates:
        print(f"  {status} {tag}: |V|={len(verts_of(edges))} |E|={len(edges)}")
        print(f"    edges: {edges}")
        print(f"    info: {info}")


if __name__ == '__main__':
    main()
