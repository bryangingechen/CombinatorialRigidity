"""
Phase 39 W4-L4 follow-up — adversarial search for `hnoGood'` inhabitants over
SUBDIVISION families (arbitrarily long branches).

Why a second search.  `no_good_search.py` (the W4-L4 recon's probe) capped
`|V| <= 13` and used gadget paths with <= 3 interior vertices.  Both caps are
fatal for the residual habitat, because of the

    EAR LEMMA.  If `H` is rigid and `P` is a path with both endpoints in
    `V(H)` and `j <= 5` interior vertices off `V(H)`, then `H + P` is rigid.
    (`5(j+1) - 6j >= 0` iff `j <= 5`; the tree-packing side: each of the 6
    trees omits one of the `j+1` new edges, and each new edge has capacity 5,
    so `j + 1 <= 6`.  Verified numerically by `--validate`.)

A rigid subgraph that is MAXIMAL therefore forces every ear through the
complement to have >= 6 interior vertices (or to span the complement) --
which forces `|V|` well past 13.  Short-path families always merge into a
bigger cluster, and the merged cluster typically has a good contraction; that
is exactly the "contract everything but one path" collapse the first search
kept observing.

Method here.  A 2EC graph of min degree 2 is a subdivision of a multigraph
`G°` on its hubs (deg >= 3).  A rigid `W` has min degree 2 in `G[W]`
(partition `{v}` vs rest gives `6 - 5 deg >= 1 > 0` otherwise), so every
degree-2 vertex of `W` drags its whole branch and both branch endpoints into
`W`.  Hence rigid vertex sets are exactly {endpoints + interiors of a set of
branches}, and enumerating `2^#branches` branch-subsets replaces the
`2^|V|` subset sweep -- so branch lengths are free and `|V|` is unbounded.

Rigidity oracle: `def(H) = 6(|V|-1) - rank_{(6,6)}(5H)`, the matroid-union
rank identity `r = min_P [5 d(P) + 6(|V|-|P|)]` (union of 6 graphic matroids
= the (6,6)-count matroid, Nash-Williams/Tutte), computed by the Lee-Streinu
(k, l) = (6, 6) pebble game on the multigraph `5H`.  Integer-exact.
`--validate` cross-checks it against `kbare_common.exact_deficiency` (the
partition/packing computation used by every earlier Phase-39 gate) on random
graphs, and cross-checks the branch enumeration against a brute-force sweep
of all vertex subsets.

Feasibility proxies: identical to `no_good_search.py` (landed-lemma backed).
  * provably feasible  := hcard AND (triangle-free  [L6b,
    `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`]
    OR spanning C3  [L7c-3, `pencilPair_of_habitat_ncard_eq_three`]).
  * provably infeasible := NOT hcard [`ncard_closedHubNbhd_le_three_of_
    isNondegPencilRealization`] OR a triangle with >= 2 hubs
    [`not_pencilNondegFeasible_of_triangle_two_hubs`].
  * middle zone := neither.

RESULT (2026-08-02): the vacuity conjecture is **REFUTED**.  96 strong
inhabitants across families D and E; the smallest has `|V| = 19` (printed by
`--witness`, independently re-verified against `exact_deficiency` over all
`2^19` vertex subsets).  A 21455-instance sweep with independent path lengths
(`--min`) puts the minimum at 19 and finds every inhabitant carrying two
adjacent degree-2 vertices; a 366-instance short-branch probe (every branch
<= 1 interior vertex) finds none.

Run:
    python3 notes/scripts/w4/nogood_subdiv.py --validate  # oracles (~4 min)
    python3 notes/scripts/w4/nogood_subdiv.py --witness   # the |V|=19 witness
    python3 notes/scripts/w4/nogood_subdiv.py --min       # minimality sweep
    python3 notes/scripts/w4/nogood_subdiv.py             # families D/E/F
"""
import os
import random
import sys
from itertools import combinations, product

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from kbare_common import (exact_deficiency, verts_of, neighbors, degrees,
                          is_2ec)

D_BODY = 6      # bodyBarDim 3
MULT = 5        # D - 1


# ---------------- (6,6) pebble game: rank of the count matroid ----------

def count_matroid_rank(edges, verts=None, k=D_BODY, ell=D_BODY):
    """Rank of `edges` (a multigraph edge list) in the (k, l)-count matroid,
    by the Lee-Streinu pebble game.  Returns the number of accepted edges."""
    if verts is None:
        verts = verts_of(edges)
    peb = {v: k for v in verts}
    out = {v: [] for v in verts}          # directed accepted edges v -> w

    def collect(target, avoid):
        """Try to move one free pebble to `target` along a reversed directed
        path.  `avoid` is the other endpoint: routing THROUGH it is harmless
        (an interior vertex of a reversed path keeps its pebble count) but
        TAKING its pebble is not — that leaves `peb[u] + peb[w]` unchanged and
        loops forever."""
        prev = {target: None}
        stack = [target]
        found = None
        while stack:
            x = stack.pop()
            if peb[x] > 0 and x != target and x != avoid:
                found = x
                break
            for y in out[x]:
                if y not in prev:
                    prev[y] = x
                    stack.append(y)
        if found is None:
            return False
        # reverse the path target -> ... -> found
        x = found
        while prev[x] is not None:
            p = prev[x]
            out[p].remove(x)
            out[x].append(p)
            x = p
        peb[found] -= 1
        peb[target] += 1
        return True

    accepted = 0
    for (u, w) in edges:
        if u == w:
            continue                       # loops: never independent (k < l+1)
        while peb[u] + peb[w] < ell + 1:
            if not (collect(u, w) or collect(w, u)):
                break
        if peb[u] + peb[w] >= ell + 1:
            if peb[u] > 0:
                peb[u] -= 1
                out[u].append(w)
            else:
                peb[w] -= 1
                out[w].append(u)
            accepted += 1
    return accepted


def deficiency(edges, verts=None):
    """def(G, 3) = 6(|V|-1) - rank_{(6,6)}(5G)."""
    if verts is None:
        verts = verts_of(edges)
    n = len(verts)
    if n <= 1:
        return 0
    big = [e for e in edges for _ in range(MULT)]
    return D_BODY * (n - 1) - count_matroid_rank(big, verts)


def is_rigid(edges, verts=None):
    return deficiency(edges, verts) == 0


# ---------------- graph predicates (same proxies as no_good_search) ------

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


def hub_set(edges):
    deg = degrees(edges)
    return {v for v, d in deg.items() if d >= 3}


def hcard_ok(edges):
    """Every closed hub-neighbourhood has <= 3 members.  Equivalently (the
    non-hub case is automatic at min degree 2): every hub has <= 2 hub
    neighbours."""
    nb = neighbors(edges)
    hubs = hub_set(edges)
    for v in verts_of(edges):
        s = {w for w in nb.get(v, ()) if w in hubs}
        if v in hubs:
            s.add(v)
        if len(s) > 3:
            return False
    return True


def triangles(edges):
    nb = neighbors(edges)
    out = set()
    for u, w in edges:
        for x in set(nb.get(u, ())) & set(nb.get(w, ())):
            out.add(frozenset((u, w, x)))
    return out


def is_spanning_c3(edges):
    V = verts_of(edges)
    return (len(V) == 3 and len(edges) == 3 and len(triangles(edges)) == 1)


def provably_feasible(edges):
    return hcard_ok(edges) and (not triangles(edges) or is_spanning_c3(edges))


def provably_infeasible(edges):
    if not hcard_ok(edges):
        return 'no-hcard'
    hubs = hub_set(edges)
    for t in triangles(edges):
        if len(t & hubs) >= 2:
            return 'two-hub-triangle'
    return None


# ---------------- branch decomposition -----------------------------------

def branch_decomposition(edges):
    """Returns (hubs, branches) with branches = list of (h1, h2, [interior]).
    A pure cycle (no hubs) returns (set(), None)."""
    nb = neighbors(edges)
    hubs = hub_set(edges)
    if not hubs:
        return set(), None
    branches = []
    seen_edge = set()

    def ekey(a, b):
        return (a, b) if str(a) <= str(b) else (b, a)

    for h in sorted(hubs, key=str):
        for first in sorted(nb[h], key=str):
            if ekey(h, first) in seen_edge:
                continue
            interior = []
            prev, cur = h, first
            seen_edge.add(ekey(prev, cur))
            while cur not in hubs:
                interior.append(cur)
                nxt = [y for y in nb[cur] if y != prev]
                assert len(nxt) == 1, "degree-2 walk broke"
                prev, cur = cur, nxt[0]
                seen_edge.add(ekey(prev, cur))
            branches.append((h, cur, interior))
    return hubs, branches


def rigid_vertex_sets(edges):
    """All W subsetneq V with |W| >= 2 and def(G[W]) = 0, via the branch
    enumeration.  Complete for graphs of min degree >= 2 (see header)."""
    V = verts_of(edges)
    nV = len(V)
    hubs, branches = branch_decomposition(edges)
    cands = set()
    if branches is None:                      # pure cycle
        return ([] if nV <= 6 else [])        # every proper subset is a path
    assert len(branches) <= 22, "too many branches to enumerate"
    for mask in range(1, 1 << len(branches)):
        A, interior = set(), set()
        for i, (h1, h2, ins) in enumerate(branches):
            if mask >> i & 1:
                A.add(h1)
                A.add(h2)
                interior.update(ins)
        W = frozenset(A | interior)
        if len(W) < 2 or len(W) >= nV:
            continue
        cands.add(W)
    out = []
    for W in cands:
        ie = induced_edges(edges, W)
        deg = degrees(ie)
        if any(deg.get(v, 0) < 2 for v in W):
            continue
        if MULT * len(ie) < D_BODY * (len(W) - 1):
            continue                          # f(W) < 0: cannot be rigid
        if is_rigid(ie, sorted(W, key=str)):
            out.append(tuple(sorted(W, key=str)))
    return out


def rigid_vertex_sets_bruteforce(edges):
    V = verts_of(edges)
    out = []
    for k in range(2, len(V)):
        for W in combinations(V, k):
            ie = induced_edges(edges, W)
            deg = degrees(ie)
            if any(deg.get(v, 0) < 2 for v in W):
                continue
            if is_rigid(ie, list(W)):
                out.append(tuple(sorted(W, key=str)))
    return out


def induced_edges(edges, W):
    Wset = set(W)
    return [e for e in edges if e[0] in Wset and e[1] in Wset]


def contraction(edges, W):
    """G / E(G[W]) with V(W) collapsed to 'v*' (H := G[W], induced-saturated:
    a non-induced H leaves an inner edge as a LOOP at v*, never simple)."""
    Wset = set(W)
    out = []
    for (u, w) in edges:
        if u in Wset and w in Wset:
            continue
        out.append(('v*' if u in Wset else u, 'v*' if w in Wset else w))
    return out


# ---------------- residual classifier ------------------------------------

def classify(edges):
    """status in: 'not-simple', 'not-2ec', 'too-small', 'not-feasible',
    'no-rigid', 'co-1', 'good-contraction', 'MIDDLE-CANDIDATE',
    'STRONG-CANDIDATE'."""
    if not is_simple(edges):
        return 'not-simple', None
    V = verts_of(edges)
    if len(V) < 3:
        return 'too-small', None
    if not is_2ec(edges):
        return 'not-2ec', None
    if not provably_feasible(edges):
        return 'not-feasible', None
    rig = rigid_vertex_sets(edges)
    if not rig:
        return 'no-rigid', None
    if any(len(W) == len(V) - 1 for W in rig):
        return 'co-1', None
    middles, strongs = [], []
    for W in rig:
        c = contraction(edges, W)
        if not is_simple(c):
            continue
        if provably_feasible(c):
            return 'good-contraction', W
        why = provably_infeasible(c)
        if why:
            strongs.append((W, why))
        else:
            middles.append(W)
    if middles:
        return 'MIDDLE-CANDIDATE', (rig, middles)
    return 'STRONG-CANDIDATE', (rig, strongs)


# ---------------- families -----------------------------------------------

def path_between(a, b, L, tag):
    """Edges of a path a - x0 - ... - x(L-1) - b with L interior vertices."""
    edges, prev = [], a
    for j in range(L):
        v = f'{tag}{j}'
        edges.append((prev, v))
        prev = v
    edges.append((prev, b))
    return edges


def family_d(m, anchors, L):
    """Inner cycle C_m; hubs u_i attached to cycle vertex `anchors[i]`; the
    u_i joined in an outer cycle by paths with L interior vertices each.
    (Family A1 of the first search, with the path length freed.)"""
    q = len(anchors)
    edges = [(f'c{i}', f'c{(i + 1) % m}') for i in range(m)]
    for i, a in enumerate(anchors):
        edges.append((f'u{i}', f'c{a}'))
    for i in range(q):
        edges += path_between(f'u{i}', f'u{(i + 1) % q}', L, f'p{i}_')
    return edges


def family_e(L, k1=2, k2=1):
    """C4 core u1..u4 with u2, u4 of degree 2; u1 carries k1 outside hub
    neighbours and u3 carries k2, all joined pairwise by long paths."""
    edges = [('u1', 'u2'), ('u2', 'u3'), ('u3', 'u4'), ('u4', 'u1')]
    xs = [f'x{i}' for i in range(k1)] + [f'y{i}' for i in range(k2)]
    for i in range(k1):
        edges.append(('u1', f'x{i}'))
    for i in range(k2):
        edges.append(('u3', f'y{i}'))
    # outer cycle through all the poles
    for i, a in enumerate(xs):
        edges += path_between(a, xs[(i + 1) % len(xs)], L, f'q{i}_')
    return edges


def family_g(m, attach, lengths):
    """General core+poles instance: core cycle C_m (`c0..c{m-1}`); pole `i` is
    a fresh vertex joined to core vertex `c{attach[i]}`; the poles are joined
    in a cycle by paths with `lengths[i]` interior vertices."""
    q = len(attach)
    edges = [(f'c{i}', f'c{(i + 1) % m}') for i in range(m)]
    for i, a in enumerate(attach):
        edges.append((f'z{i}', f'c{a}'))
    for i in range(q):
        edges += path_between(f'z{i}', f'z{(i + 1) % q}', lengths[i], f'w{i}_')
    return edges


def diagnostics(edges):
    """Facts about a candidate that bear on the fallback routes."""
    deg = degrees(edges)
    nb = neighbors(edges)
    safe_pair = any(deg[u] == 2 and deg[w] == 2 for u, w in edges)
    _, branches = branch_decomposition(edges)
    maxint = max((len(b[2]) for b in branches), default=0)
    return {'def(G)': deficiency(edges), 'safe_pair(2-2 edge)': safe_pair,
            'max branch interior': maxint, 'hubs': len(hub_set(edges)),
            # what the split arm actually needs at a residual G: a degree-2 v
            # strictly inside a branch of >= 3 interior vertices, so that its
            # two neighbours a, b are degree-2, non-adjacent and share no
            # neighbour but v -- i.e. `G.splitOff v a b e0` stays simple and
            # gains no triangle, the two places the landed L7a/L7c-5 chain
            # currently reads those off `hnoRigid`.
            'deep_split_vertex': maxint >= 3}


def random_subdivision(rng, nhub, extra_edges, lo, hi):
    """Random multigraph on `nhub` hubs (a random cubic-ish base), each edge
    subdivided by a random number of interior vertices in [lo, hi]."""
    base = []
    hubs = [f'h{i}' for i in range(nhub)]
    for i in range(nhub):                      # a Hamilton cycle base
        base.append((hubs[i], hubs[(i + 1) % nhub]))
    pairs = [(a, b) for a in hubs for b in hubs if a < b]
    rng.shuffle(pairs)
    for p in pairs[:extra_edges]:
        base.append(p)
    edges = []
    for t, (a, b) in enumerate(base):
        edges += path_between(a, b, rng.randint(lo, hi), f's{t}_')
    return edges


# ---------------- validation ---------------------------------------------

def validate():
    rng = random.Random(20260802)
    print("== validate: pebble-game deficiency vs exact_deficiency ==")
    bad = 0
    for trial in range(400):
        n = rng.randint(3, 9)
        pairs = [(u, w) for u in range(n) for w in range(n) if u < w]
        m = rng.randint(n - 1, min(len(pairs), n + 4))
        edges = rng.sample(pairs, m)
        if len(verts_of(edges)) != n:
            continue
        d1, _ = exact_deficiency(edges)
        d2 = deficiency(edges)
        if d1 != d2:
            bad += 1
            print(f"  MISMATCH n={n} edges={edges}: exact={d1} pebble={d2}")
    print(f"  mismatches: {bad} / 400")
    assert bad == 0

    print("== validate: cycles C_k rigid iff k <= 6 ==")
    for k in range(3, 10):
        cyc = [(i, (i + 1) % k) for i in range(k)]
        r = is_rigid(cyc)
        print(f"  C_{k}: def={deficiency(cyc)} rigid={r}")
        assert r == (k <= 6)

    print("== validate: EAR LEMMA (C4 + ear of j interior vertices) ==")
    for j in range(0, 8):
        e = [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a')]
        e += path_between('a', 'c', j, 'e')
        print(f"  j={j}: def={deficiency(e)}")
        assert is_rigid(e) == (j <= 5)

    print("== validate: branch enumeration vs brute force ==")
    bad = 0
    for trial in range(120):
        n = rng.randint(6, 10)
        pairs = [(u, w) for u in range(n) for w in range(n) if u < w]
        m = rng.randint(n, min(len(pairs), n + 3))
        edges = rng.sample(pairs, m)
        if len(verts_of(edges)) != n or not is_2ec(edges):
            continue
        a = sorted(rigid_vertex_sets(edges))
        b = sorted(rigid_vertex_sets_bruteforce(edges))
        if a != b:
            bad += 1
            print(f"  MISMATCH {edges}\n    branch={a}\n    brute={b}")
    print(f"  mismatches: {bad}")
    assert bad == 0
    print("VALIDATION OK")


# ---------------- driver --------------------------------------------------

def report(tag, edges, verbose=False):
    status, info = classify(edges)
    if status in ('STRONG-CANDIDATE', 'MIDDLE-CANDIDATE'):
        print(f"  {status} [{tag}] |V|={len(verts_of(edges))} "
              f"|E|={len(edges)}")
        if verbose:
            print(f"    edges: {edges}")
            print(f"    info:  {info}")
    return status, info


def minsearch():
    """Sweep core+poles instances with INDEPENDENT path lengths (including 0)
    to locate the smallest residual inhabitant, and probe the fallback
    question: does every inhabitant carry two adjacent degree-2 vertices (the
    split arm's safe-vertex supply)?"""
    best = []
    seen = 0
    for m in (3, 4, 5, 6):
        for q in (3, 4):
            for attach in combinations_with_repetition_sorted(m, q):
                for lengths in product(range(0, 5), repeat=q):
                    if list(lengths) != sorted(lengths):
                        continue                # cycle symmetry: dedupe
                    edges = family_g(m, attach, lengths)
                    if not is_simple(edges):
                        continue
                    seen += 1
                    st, info = classify(edges)
                    if st in ('STRONG-CANDIDATE', 'MIDDLE-CANDIDATE'):
                        best.append((len(verts_of(edges)), st, m, attach,
                                     lengths, edges, info))
    best.sort(key=lambda t: t[0])
    print(f"  instances classified: {seen}; candidates: {len(best)}")
    for n, st, m, attach, lengths, edges, info in best[:6]:
        print(f"  {st} |V|={n} core=C{m} attach={attach} lengths={lengths}")
        print(f"    diagnostics: {diagnostics(edges)}")
        print(f"    rigid sets: {info[0]}  verdicts: {info[1]}")
    if best:
        print(f"  MINIMUM |V| over the sweep: {best[0][0]}")
    nosafe = [b for b in best if not diagnostics(b[5])['safe_pair(2-2 edge)']]
    nodeep = [b for b in best if not diagnostics(b[5])['deep_split_vertex']]
    print(f"  candidates WITHOUT two adjacent degree-2 vertices: {len(nosafe)}")
    print(f"  candidates WITHOUT a deep split vertex: {len(nodeep)}")
    print(f"  candidates with def(G) = 0 / > 0: "
          f"{sum(1 for b in best if diagnostics(b[5])['def(G)'] == 0)} / "
          f"{sum(1 for b in best if diagnostics(b[5])['def(G)'] > 0)}")


def combinations_with_repetition_sorted(m, q):
    """Sorted multisets of core positions, up to the cycle's rotation."""
    out = set()
    for t in product(range(m), repeat=q):
        out.add(tuple(sorted(t)))
    return sorted(out)


def shortbranch_probe(ntrials=600):
    """Adversarial probe of the fallback claim: are there residual
    inhabitants in which EVERY branch has <= 1 interior vertex (so no two
    degree-2 vertices are adjacent and the split arm's safe-vertex supply is
    absent)?"""
    rng = random.Random(80231)
    tallies, hits = {}, 0
    for _ in range(ntrials):
        nhub = rng.randint(4, 9)
        extra = rng.randint(0, 4)
        edges = random_subdivision(rng, nhub, extra, 0, 1)
        if not is_simple(edges):
            continue
        _, br = branch_decomposition(edges)
        if br is None or len(br) > 18:
            continue
        st, _ = classify(edges)
        tallies[st] = tallies.get(st, 0) + 1
        if st.endswith('CANDIDATE'):
            hits += 1
            print(f"    short-branch CANDIDATE: {edges}")
    print(f"  tallies: {tallies}")
    print(f"  short-branch candidates: {hits}")


def witness():
    """The canonical |V| = 19 residual inhabitant, re-verified end to end
    against the independent `exact_deficiency` oracle over ALL vertex
    subsets (2^19, with the `f >= 0` + min-degree-2 prefilter)."""
    G = family_g(4, (0, 0, 2), (4, 4, 4))
    V = verts_of(G)
    n = len(V)
    print(f"  |V| = {n}, |E| = {len(G)}")
    print(f"  edges: {sorted(G, key=str)}")
    print(f"  degrees: {dict(sorted(degrees(G).items()))}")
    print(f"  simple={is_simple(G)} 2EC={is_2ec(G)} hcard={hcard_ok(G)} "
          f"triangles={triangles(G)}")
    print(f"  => provably feasible (L6b: hcard + triangle-free): "
          f"{provably_feasible(G)}")
    idx = {v: i for i, v in enumerate(V)}
    adj = [0] * n
    for u, w in G:
        adj[idx[u]] |= 1 << idx[w]
        adj[idx[w]] |= 1 << idx[u]
    Ein = [0] * (1 << n)
    for S in range(1, 1 << n):
        v = (S & -S).bit_length() - 1
        Ein[S] = Ein[S & (S - 1)] + bin(adj[v] & (S & (S - 1))).count('1')
    rig, tested = [], 0
    for S in range(1, 1 << n):
        k = bin(S).count('1')
        if k < 2 or k >= n or MULT * Ein[S] < D_BODY * (k - 1):
            continue
        W = [V[i] for i in range(n) if S >> i & 1]
        ie = induced_edges(G, W)
        dg = degrees(ie)
        if any(dg.get(x, 0) < 2 for x in W):
            continue
        tested += 1
        d1, d2 = deficiency(ie, list(W)), exact_deficiency(ie)[0]
        assert d1 == d2, (W, d1, d2)
        if d1 == 0:
            rig.append(tuple(sorted(W, key=str)))
    print(f"  brute-force subsets surviving the prefilter: {tested} "
          f"(both oracles agree on every one)")
    print(f"  proper rigid vertex sets: {rig}")
    print(f"  branch enumeration agrees: {sorted(rigid_vertex_sets(G)) == rig}")
    assert rig and all(len(W) != n - 1 for W in rig), "co-1 present!"
    for W in rig:
        Q = contraction(G, W)
        nbq, hq = neighbors(Q), hub_set(Q)
        chn = {w for w in nbq['v*'] if w in hq} | ({'v*'} if 'v*' in hq
                                                   else set())
        print(f"  contract {W}: simple={is_simple(Q)} deg(v*)={degrees(Q)['v*']}"
              f" closedHubNbhd(v*)={sorted(chn)} (ncard {len(chn)}) "
              f"=> infeasible by '{provably_infeasible(Q)}'")
        assert is_simple(Q) and provably_infeasible(Q) == 'no-hcard'
    print(f"  diagnostics: {diagnostics(G)}")
    print("  -- both deficiency regimes are inhabited (lengthening the three "
          "paths keeps every verdict and drives def(G) up):")
    for lengths in ((4, 4, 4), (4, 4, 6), (5, 5, 5)):
        H = family_g(4, (0, 0, 2), lengths)
        st, _ = classify(H)
        print(f"     lengths={lengths}: |V|={len(verts_of(H))} "
              f"def(G)={deficiency(H)} -> {st}")
        assert st == 'STRONG-CANDIDATE'
    print("  VERDICT: residual inhabitant confirmed — `hnoGood'` is NOT vacuous.")


def main():
    if '--validate' in sys.argv:
        validate()
        return
    if '--witness' in sys.argv:
        print("== canonical |V|=19 residual inhabitant ==")
        witness()
        return
    if '--min' in sys.argv:
        print("== minimality sweep (core + 3/4 poles, independent lengths) ==")
        minsearch()
        print("== short-branch probe (every branch <= 1 interior vertex) ==")
        shortbranch_probe()
        return
    tallies = {}
    hits = []

    def run(tag, edges):
        st, info = report(tag, edges)
        tallies[st] = tallies.get(st, 0) + 1
        if st in ('STRONG-CANDIDATE', 'MIDDLE-CANDIDATE'):
            hits.append((st, tag, edges, info))

    print("== family D: inner cycle C_m + q hub gadgets on long outer paths ==")
    for m in range(3, 8):
        for q in (3, 4):
            for anchors in combinations(range(m), q):
                for L in range(1, 8):
                    run(f"D m={m} anc={anchors} L={L}",
                        family_d(m, anchors, L))
    print(f"  tallies: {tallies}")

    print("== family E: C4 core with 3 outside hub poles ==")
    for L in range(1, 8):
        for (k1, k2) in ((2, 1), (2, 2), (3, 0)):
            run(f"E L={L} k=({k1},{k2})", family_e(L, k1, k2))
    print(f"  tallies: {tallies}")

    print("== family F: random subdivisions ==")
    rng = random.Random(390239)
    for i in range(400):
        nhub = rng.randint(3, 6)
        extra = rng.randint(0, 3)
        lo = rng.randint(0, 4)
        hi = lo + rng.randint(0, 4)
        edges = random_subdivision(rng, nhub, extra, lo, hi)
        if not is_simple(edges):
            tallies['not-simple'] = tallies.get('not-simple', 0) + 1
            continue
        run(f"F #{i} nhub={nhub} extra={extra} L=[{lo},{hi}]", edges)
    print(f"  tallies: {tallies}")

    print(f"\nCANDIDATES: {len(hits)}")
    best = None
    for st, tag, edges, info in hits:
        n = len(verts_of(edges))
        if best is None or n < best[0]:
            best = (n, st, tag, edges, info)
    if best:
        n, st, tag, edges, info = best
        print(f"\nSMALLEST CANDIDATE ({st}, |V|={n}): {tag}")
        print(f"  edges: {sorted(edges, key=str)}")
        print(f"  rigid vertex sets: {info[0]}")
        print(f"  contraction verdicts: {info[1]}")


if __name__ == '__main__':
    main()
