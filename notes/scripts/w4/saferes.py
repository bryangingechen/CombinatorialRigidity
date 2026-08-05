"""
Phase 39 W4 — adversarial attack on the (SAFE-RES) conjecture.

(SAFE-RES) claimed: every RESIDUAL graph `G` (simple, 2EC, `PencilNondegFeasible`,
`3 <= |V|`, has a proper rigid subgraph, no co-1 rigid subgraph, no rigid
contraction that is Simple AND Feasible) has a degree-2 vertex strictly interior
to a branch with >= 3 interior vertices (a "deep split vertex").

RESULT (2026-08-02): **REFUTED**.  `witness()` exhibits a `|V| = 29` residual
whose every branch carries exactly <= 2 interior vertices.  Its two feasibility
verdicts are landed-lemma-certified (L6b sufficient for `G`; the `hcard`
necessary condition for the contraction), exactly as for the `W19` inhabitant of
`nogood_subdiv.py`.

The weaker property the split arm actually consumes SURVIVES; see
`split_usable` below and `notes/Pencil-W4-informal.md` §(SAFE-RES) for the
statement (SAFE-RES').

Why a new script.  `nogood_subdiv.py` swept core+poles+LONG PATHS families:
every inhabitant it found had a 4-interior branch, because that is how those
families satisfy the Ear Lemma.  The Ear Lemma constrains EARS, not BRANCHES —
an ear may run through intermediate hubs.  This script sweeps exactly that
blind spot: subdivided multigraphs whose branch interiors are all <= 2, so all
ear length is carried by hub chains.

Oracles.  Two independent integer-exact rigidity oracles are used and
cross-checked on every load-bearing subgraph:
  * `nogood_subdiv.deficiency` — Lee-Streinu (6,6) pebble game.
  * `treepack_deficiency` (here) — matroid-union augmenting paths packing 6
    edge-disjoint spanning forests in `5H` (Nash-Williams/Tutte; Roskind-Tarjan
    style exchange BFS).  Polynomial, so unlike `kbare_common.exact_deficiency`
    (a `2^|V|` partition enumeration) it runs at `|V| = 29`.
`--validate` cross-checks all three against each other on small random graphs.

Run:
    python3 notes/scripts/w4/saferes.py --validate   # 3 oracles agree (~2 min)
    python3 notes/scripts/w4/saferes.py --witness    # the |V|=29 refutation
    python3 notes/scripts/w4/saferes.py --search     # sweeps + minimality
    python3 notes/scripts/w4/saferes.py --prime      # (SAFE-RES') coverage
    python3 notes/scripts/w4/saferes.py --structure  # this argument's steps
"""
import os
import random
import sys
from itertools import combinations, product

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import exact_deficiency, verts_of, neighbors, degrees, is_2ec
from nogood_subdiv import (D_BODY, MULT, deficiency, is_rigid, is_simple,
                           hub_set, hcard_ok, triangles, is_spanning_c3,
                           provably_feasible, provably_infeasible,
                           branch_decomposition, rigid_vertex_sets,
                           induced_edges, contraction, path_between)

BR_CAP = 15   # branch-subset enumeration is 2^b; keep the sweeps tractable


# ---------------- oracle 2: matroid-union tree packing --------------------

class _DSU:
    def __init__(self, verts):
        self.p = {v: v for v in verts}

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        self.p[ra] = rb
        return True


def _forest_cycle(forest, verts, u, w):
    """Edges (as indices into the global edge list) on the u-w path in the
    forest `forest` (a dict idx -> (u, w)); [] if u, w are in different
    components (so the edge can be added)."""
    adj = {}
    for idx, (a, b) in forest.items():
        adj.setdefault(a, []).append((b, idx))
        adj.setdefault(b, []).append((a, idx))
    if u not in adj or w not in adj:
        return None                      # at least one endpoint isolated
    prev = {u: (None, None)}
    stack = [u]
    while stack:
        x = stack.pop()
        if x == w:
            break
        for (y, idx) in adj.get(x, ()):
            if y not in prev:
                prev[y] = (x, idx)
                stack.append(y)
    if w not in prev:
        return None
    out, x = [], w
    while prev[x][0] is not None:
        out.append(prev[x][1])
        x = prev[x][0]
    return out


def union_rank(edges, verts=None, k=D_BODY):
    """Rank of `edges` in the union of `k` graphic matroids, by matroid-union
    augmenting paths (independent of the pebble game)."""
    if verts is None:
        verts = verts_of(edges)
    forests = [dict() for _ in range(k)]     # idx -> (u, w)
    dsus = [_DSU(verts) for _ in range(k)]
    owner = {}                               # idx -> forest index
    rank = 0
    for idx, (u, w) in enumerate(edges):
        if u == w:
            continue
        placed = False
        for i in range(k):
            if dsus[i].union(u, w):
                forests[i][idx] = (u, w)
                owner[idx] = i
                placed = True
                break
        if placed:
            rank += 1
            continue
        # exchange BFS: label[y] = (parent_edge, forest) meaning "y lies on the
        # fundamental cycle of parent_edge in `forest`, and y is in `forest`".
        label = {idx: None}
        queue = [idx]
        aug = None
        qi = 0
        while qi < len(queue) and aug is None:
            x = queue[qi]
            qi += 1
            xu, xw = edges[x]
            for i in range(k):
                if owner.get(x) == i:
                    continue
                cyc = _forest_cycle(forests[i], verts, xu, xw)
                if cyc is None:              # x is addable to forest i
                    aug = (x, i)
                    break
                for y in cyc:
                    if y not in label:
                        label[y] = (x, i)
                        queue.append(y)
        if aug is None:
            continue                          # e is spanned; rank unchanged
        # walk the augmenting path back to the root
        x, i = aug
        while True:
            j = owner.get(x)
            if j is not None:
                del forests[j][x]
            forests[i][x] = edges[x]
            owner[x] = i
            par = label[x]
            if par is None:
                break
            x, i = par[0], j
        for i in range(k):                    # rebuild the DSUs
            dsus[i] = _DSU(verts)
            for (a, b) in forests[i].values():
                dsus[i].union(a, b)
        rank += 1
    return rank


def treepack_deficiency(edges, verts=None):
    """def(H, 3) = 6(|V|-1) - rank_{union of 6 graphic matroids}(5H)."""
    if verts is None:
        verts = verts_of(edges)
    n = len(verts)
    if n <= 1:
        return 0
    big = [e for e in edges for _ in range(MULT)]
    return D_BODY * (n - 1) - union_rank(big, verts)


# ---------------- (SAFE-RES) and (SAFE-RES') diagnostics ------------------

def deep_split_vertices(edges):
    """Degree-2 vertices strictly interior to a branch with >= 3 interior
    vertices — the objects (SAFE-RES) asserts exist."""
    _, br = branch_decomposition(edges)
    if br is None:
        return []
    out = []
    for (_, _, ins) in br:
        if len(ins) >= 3:
            out.extend(ins[1:-1])
    return out


def split_usable(edges):
    """Degree-2 vertices `v` at which the landed L7a chain's `hnoRigid`
    consumption re-derives from local data alone:

      (S1) deg v = 2, its two neighbours a != b;
      (S2) deg a = 2 or deg b = 2                     [`hsafe`, PencilHub];
      (S3) a !~ b                        [`splitOff_simple_of_noRigid_of_card`];
      (S4) N(a) cap N(b) = {v}   [the induced-C4 arm of
                                  `splitOff_triangleFree_of_noRigid`];
      (S5) G triangle-free       [its other arm: a G-triangle survives the
                                  split].
    (S5) is global, so it is returned separately."""
    nb = neighbors(edges)
    deg = degrees(edges)
    tf = not triangles(edges)
    out = []
    for v in verts_of(edges):
        if deg[v] != 2:
            continue
        a, b = list(nb[v])
        if a == b:
            continue
        if deg[a] != 2 and deg[b] != 2:
            continue
        if b in nb[a]:
            continue
        if (set(nb[a]) & set(nb[b])) - {v}:
            continue
        out.append((v, a, b))
    return out, tf


def diag(edges):
    _, br = branch_decomposition(edges)
    maxint = max((len(b[2]) for b in br), default=0)
    usable, tf = split_usable(edges)
    n, m = len(verts_of(edges)), len(edges)
    return {'|V|': n, '|E|': m, 'c': m - n + 1,
            'f(V)=5|E|-6(|V|-1)': 5 * m - 6 * (n - 1),
            'def(G)': deficiency(edges), 'hubs': len(hub_set(edges)),
            'max branch interior': maxint,
            'deep split vertices (SAFE-RES)': len(deep_split_vertices(edges)),
            'triangle-free': tf,
            "split-usable vertices (SAFE-RES')": len(usable)}


# ---------------- the refuting witness ------------------------------------

def w29(spoke=2, outer=2):
    """The `|V| = 29` short-branch residual.

    core   C4  A - m1 - B - m2 - A          (rigid; A deg 4, B deg 3)
    poles  z0, z1 joined to A by HUB EDGES; z2 joined to B by a hub edge
    ring   z0 - y0 - z1 - y1 - z2 - y2 - z0, every leg `outer`-subdivided
    spokes y_i - p, every spoke `spoke`-subdivided (p a fresh degree-3 hub)

    Every branch carries <= 2 interior vertices, yet the ear
    `A - z0 - ... - z1 - A` has 7 interior vertices, so the Ear Lemma cannot
    grow the core: the core stays a MAXIMAL rigid subgraph."""
    E = [('A', 'm1'), ('m1', 'B'), ('B', 'm2'), ('m2', 'A'),
         ('A', 'z0'), ('A', 'z1'), ('B', 'z2')]
    ring = ['z0', 'y0', 'z1', 'y1', 'z2', 'y2']
    for i in range(6):
        E += path_between(ring[i], ring[(i + 1) % 6], outer, f'o{i}_')
    for i, y in enumerate(['y0', 'y1', 'y2']):
        E += path_between(y, 'p', spoke, f'sp{i}_')
    return E


def classify2(edges):
    """`nogood_subdiv.classify` with every rigidity verdict re-checked against
    the independent tree-packing oracle."""
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
    for W in rig:
        assert treepack_deficiency(induced_edges(edges, W), list(W)) == 0, W
    if not rig:
        return 'no-rigid', None
    if any(len(W) == len(V) - 1 for W in rig):
        return 'co-1', None
    strongs, middles = [], []
    for W in rig:
        c = contraction(edges, W)
        if not is_simple(c):
            continue
        if provably_feasible(c):
            return 'good-contraction', W     # a good contraction wins outright
        why = provably_infeasible(c)
        if why:
            strongs.append((W, why))
        else:
            middles.append(W)
    if middles:
        return 'MIDDLE-CANDIDATE', (rig, middles)
    return 'STRONG-CANDIDATE', (rig, strongs)


def witness():
    G = w29()
    V = verts_of(G)
    n = len(V)
    print(f"  |V| = {n}, |E| = {len(G)}")
    print(f"  edges: {sorted(G, key=str)}")
    print(f"  degrees: {dict(sorted(degrees(G).items()))}")
    hubs, br = branch_decomposition(G)
    print(f"  hubs ({len(hubs)}): {sorted(hubs)}")
    print(f"  branches (hub, hub, #interior): "
          f"{sorted((a, b, len(i)) for a, b, i in br)}")
    print(f"  simple={is_simple(G)} 2EC={is_2ec(G)} hcard={hcard_ok(G)} "
          f"triangles={triangles(G)}")
    print(f"  => G provably feasible (L6b: hcard + triangle-free): "
          f"{provably_feasible(G)}")

    print("  -- rigid proper subgraphs (branch enumeration; every verdict "
          "cross-checked on BOTH oracles) --")
    _, brs = branch_decomposition(G)
    checked = 0
    rig = []
    for mask in range(1, 1 << len(brs)):
        A, ins = set(), set()
        for i, (h1, h2, ii) in enumerate(brs):
            if mask >> i & 1:
                A |= {h1, h2}
                ins |= set(ii)
        W = tuple(sorted(A | ins, key=str))
        if len(W) < 2 or len(W) >= n:
            continue
        ie = induced_edges(G, W)
        dg = degrees(ie)
        if any(dg.get(x, 0) < 2 for x in W):
            continue
        d1 = deficiency(ie, list(W))
        d2 = treepack_deficiency(ie, list(W))
        assert d1 == d2, (W, d1, d2)
        checked += 1
        if d1 == 0 and W not in rig:
            rig.append(W)
    print(f"  branch-subset candidates evaluated on both oracles: {checked} "
          f"(0 disagreements)")
    print(f"  proper rigid vertex sets: {rig}")
    assert sorted(rig) == sorted(rigid_vertex_sets(G))

    print("  -- co-1 exclusion, vertex by vertex, on BOTH oracles --")
    worst = None
    for v in V:
        W = [x for x in V if x != v]
        ie = induced_edges(G, W)
        d1, d2 = deficiency(ie, W), treepack_deficiency(ie, W)
        assert d1 == d2, (v, d1, d2)
        assert d1 > 0, f"co-1 at {v}!"
        worst = d1 if worst is None else min(worst, d1)
    print(f"  every G - v is non-rigid ({n}/{n}, both oracles agree): "
          f"min def(G-v) = {worst}")

    print("  -- contraction verdicts --")
    for W in rig:
        Q = contraction(G, W)
        nbq, hq = neighbors(Q), hub_set(Q)
        chn = ({w for w in nbq['v*'] if w in hq}
               | ({'v*'} if 'v*' in hq else set()))
        print(f"  contract {W}: simple={is_simple(Q)} "
              f"deg(v*)={degrees(Q)['v*']} "
              f"closedHubNbhd(v*)={sorted(chn)} (ncard {len(chn)}) "
              f"=> infeasible by '{provably_infeasible(Q)}'")
        assert is_simple(Q) and provably_infeasible(Q) == 'no-hcard'

    print(f"  classify (both oracles): {classify2(G)[0]}")
    d = diag(G)
    print(f"  diagnostics: {d}")
    assert d['max branch interior'] == 2
    assert d['deep split vertices (SAFE-RES)'] == 0
    assert d["split-usable vertices (SAFE-RES')"] > 0
    u, tf = split_usable(G)
    print(f"  a split-usable vertex: {u[0]}  (G triangle-free: {tf})")
    print("  VERDICT: (SAFE-RES) is REFUTED; (SAFE-RES') holds here.")


# ---------------- families with short branches only ------------------------

def family_core_ring(m, attach, ring_extra, outer, spoke):
    """Core C_m (`c0..`), poles `z0..z{q-1}` attached to `c{attach[i]}` by HUB
    EDGES, an outer ring through the poles and `ring_extra` fresh hubs `y_i`,
    every ring leg `outer`-subdivided, every `y_i` joined to a fresh centre `p`
    by a `spoke`-subdivided branch."""
    q = len(attach)
    E = [(f'c{i}', f'c{(i + 1) % m}') for i in range(m)]
    for i, a in enumerate(attach):
        E.append((f'z{i}', f'c{a}'))
    ring = []
    for i in range(q):
        ring.append(f'z{i}')
        if i < ring_extra:
            ring.append(f'y{i}')
    for i in range(len(ring)):
        E += path_between(ring[i], ring[(i + 1) % len(ring)], outer, f'o{i}_')
    for i in range(ring_extra):
        E += path_between(f'y{i}', 'p', spoke, f'sp{i}_')
    return E


def random_short(rng, nhub, extra, lo=0, hi=2):
    """Random 2EC subdivision with every branch carrying in [lo, hi] interior
    vertices — the configuration class (SAFE-RES) is attacked on.

    The base multigraph is forced to **minimum degree 3** (a Hamilton cycle
    plus a random perfect-matching-ish top-up), so that every `h_i` really is
    a hub of the subdivision and `hi` really does cap the branch interiors.
    Returns `None` if the top-up fails."""
    hubs = [f'h{i}' for i in range(nhub)]
    base = [(hubs[i], hubs[(i + 1) % nhub]) for i in range(nhub)]
    deg = {h: 2 for h in hubs}
    pairs = [(a, b) for a in hubs for b in hubs if a < b]
    rng.shuffle(pairs)
    for (a, b) in pairs:                       # raise every hub to degree >= 3
        if deg[a] >= 3 and deg[b] >= 3:
            continue
        base.append((a, b))
        deg[a] += 1
        deg[b] += 1
    if any(d < 3 for d in deg.values()):
        return None
    for (a, b) in pairs[:extra]:
        base.append((a, b))
    E = []
    for t, (a, b) in enumerate(base):
        E += path_between(a, b, rng.randint(lo, hi), f's{t}_')
    return E


def branch_cap(edges, cap):
    """True iff `edges` decomposes into branches each of <= `cap` interior
    vertices (checked on the ACTUAL subdivision, not on the generator's
    intent)."""
    _, br = branch_decomposition(edges)
    return br is not None and all(len(i) <= cap for _, _, i in br)


# ---------------- drivers --------------------------------------------------

def validate():
    rng = random.Random(20260802)
    print("== three oracles agree (pebble / tree-packing / partition) ==")
    bad = 0
    for _ in range(250):
        n = rng.randint(3, 9)
        pairs = [(u, w) for u in range(n) for w in range(n) if u < w]
        m = rng.randint(n - 1, min(len(pairs), n + 4))
        edges = rng.sample(pairs, m)
        if len(verts_of(edges)) != n:
            continue
        d0 = exact_deficiency(edges)[0]
        d1 = deficiency(edges)
        d2 = treepack_deficiency(edges)
        if not (d0 == d1 == d2):
            bad += 1
            print(f"  MISMATCH {edges}: partition={d0} pebble={d1} pack={d2}")
    print(f"  mismatches: {bad} / 250")
    assert bad == 0

    print("== tree-packing oracle: C_k rigid iff k <= 6 ==")
    for k in range(3, 10):
        cyc = [(i, (i + 1) % k) for i in range(k)]
        assert (treepack_deficiency(cyc) == 0) == (k <= 6)
    print("  ok")

    print("== tree-packing oracle: Ear Lemma threshold at j = 5/6 ==")
    for j in range(0, 8):
        e = [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a')]
        e += path_between('a', 'c', j, 'e')
        assert (treepack_deficiency(e) == 0) == (j <= 5), j
    print("  ok")

    print("== tree-packing oracle on sparse SUBDIVISIONS (|V| up to ~30) ==")
    bad = 0
    for _ in range(60):
        edges = random_short(rng, rng.randint(4, 8), rng.randint(0, 3), 0, 3)
        if not is_simple(edges):
            continue
        if deficiency(edges) != treepack_deficiency(edges):
            bad += 1
            print(f"  MISMATCH {edges}")
    print(f"  mismatches: {bad}")
    assert bad == 0
    print("VALIDATION OK")


def search():
    print("== structured short-branch sweep (core + poles + hub ring) ==")
    best, seen, cands = None, 0, []
    for m in (3, 4, 5, 6):
        for q in (3, 4):
            for attach in sorted({tuple(sorted(t))
                                  for t in product(range(m), repeat=q)}):
                for ring_extra in range(0, q + 1):
                    for outer in (0, 1, 2):
                        for spoke in (0, 1, 2):
                            if ring_extra == 0 and spoke != 0:
                                continue
                            E = family_core_ring(m, attach, ring_extra,
                                                 outer, spoke)
                            if not is_simple(E) or not is_2ec(E):
                                continue
                            _, br = branch_decomposition(E)
                            if br is None or len(br) > BR_CAP:
                                continue
                            if max(len(i) for _, _, i in br) > 2:
                                continue
                            seen += 1
                            st, info = classify2(E)
                            if st.endswith('CANDIDATE'):
                                n = len(verts_of(E))
                                cands.append((n, st, m, attach, ring_extra,
                                              outer, spoke, E))
                                if best is None or n < best[0]:
                                    best = cands[-1]
    print(f"  short-branch instances classified: {seen}; "
          f"residual inhabitants: {len(cands)}")
    cands.sort(key=lambda t: t[0])
    for c in cands[:5]:
        print(f"  {c[1]} |V|={c[0]} core=C{c[2]} attach={c[3]} "
              f"ring_extra={c[4]} outer={c[5]} spoke={c[6]}")
        print(f"    {diag(c[7])}")
    if best:
        print(f"  MINIMUM |V| over the structured short-branch sweep: "
              f"{cands[0][0]}")
    for cap, ntrials, tag in ((2, 1800, "short (every branch <= 2 interior)"),
                              (1, 1800, "ULTRA-short (every branch <= 1: no "
                                        "two adjacent degree-2 vertices)")):
        print(f"== random sweep, {tag} ==")
        rng = random.Random(4242 + cap)
        tal, hits = {}, []
        tried = 0
        for _ in range(ntrials):
            E = random_short(rng, rng.randint(4, 11), rng.randint(0, 5),
                             0, cap)
            if E is None or not is_simple(E) or not branch_cap(E, cap):
                continue
            _, br = branch_decomposition(E)
            if len(br) > BR_CAP:
                continue
            tried += 1
            st, info = classify2(E)
            tal[st] = tal.get(st, 0) + 1
            if st.endswith('CANDIDATE'):
                hits.append((len(verts_of(E)), st, E))
        print(f"  instances with a genuine branch cap of {cap}: {tried}")
        print(f"  tallies: {tal}")
        print(f"  residual inhabitants: {len(hits)}")
        hits.sort(key=lambda t: t[0])
        for n, st, E in hits[:4]:
            print(f"  {st} |V|={n}: {diag(E)}")
            if st == 'MIDDLE-CANDIDATE':
                print(f"    edges: {E}")


def prime():
    """(SAFE-RES') coverage: over every residual inhabitant this project has
    produced — the `nogood_subdiv` long-branch families AND the short-branch
    families here — does a split-usable degree-2 vertex always exist, and is
    the graph always triangle-free?"""
    import nogood_subdiv as ns
    pool = []
    for lengths in product(range(0, 6), repeat=3):
        if list(lengths) != sorted(lengths):
            continue
        for m in (3, 4, 5, 6):
            for attach in sorted({tuple(sorted(t))
                                  for t in product(range(m), repeat=3)}):
                pool.append(ns.family_g(m, attach, lengths))
    for m in (3, 4, 5, 6):
        for q in (3, 4):
            for attach in sorted({tuple(sorted(t))
                                  for t in product(range(m), repeat=q)}):
                for ring_extra in range(0, q + 1):
                    for outer in (0, 1, 2):
                        for spoke in (0, 1, 2):
                            pool.append(family_core_ring(m, attach, ring_extra,
                                                         outer, spoke))
    rng = random.Random(99991)
    for _ in range(700):
        E = random_short(rng, rng.randint(4, 10), rng.randint(0, 5), 0, 3)
        if E is not None:
            pool.append(E)
    n_res = n_deep = n_usable = n_tf = n_pair = n_edge = 0
    bad = []
    for E in pool:
        if not is_simple(E) or not is_2ec(E):
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > BR_CAP:
            continue
        st, _ = ns.classify(E)
        if not st.endswith('CANDIDATE'):
            continue
        n_res += 1
        d = diag(E)
        deg = degrees(E)
        n_deep += d['deep split vertices (SAFE-RES)'] > 0
        n_tf += d['triangle-free']
        n_pair += any(deg[u] == 2 and deg[w] == 2 for u, w in E)
        n_edge += d['f(V)=5|E|-6(|V|-1)'] <= 4
        ok = d["split-usable vertices (SAFE-RES')"] > 0 and d['triangle-free']
        n_usable += ok
        if not ok:
            bad.append(E)
    print(f"  residual inhabitants swept:                        {n_res}")
    print(f"  ... with a DEEP split vertex  [(SAFE-RES)]:        {n_deep}")
    print(f"  ... with two adjacent degree-2 vertices:           {n_pair}")
    print(f"  ... satisfying the KT-4.5(i) edge bound f(V) <= 4: {n_edge}")
    print(f"  ... triangle-free:                                 {n_tf}")
    print(f"  ... with a split-usable vertex [(SAFE-RES')]:      {n_usable}")
    for E in bad[:5]:
        print(f"  (SAFE-RES') FAILURE: {E}\n    {diag(E)}")


def structure():
    """Numerical coverage for the steps of the §(SAFE-RES) argument itself.

    (C7)  at a cardinality-maximal rigid proper subgraph of a residual, every
          S-S path through T has >= 6 interior vertices;
    (C8)  that cluster's contraction fails `hcard` at `v*` (case A) or G[T]
          carries a triangle (case B);
    (E-k) if every branch has <= 1 interior vertex then f(V) >= 5 (so the
          KT-4.5(i) edge bound fails) — checked on ALL 2EC min-degree-2
          graphs the generators produce, residual or not;
    (V)   the branch characterization of split-usable vertices agrees with the
          direct `split_usable` scan."""
    import nogood_subdiv as ns
    rng = random.Random(31337)
    pool = [w29(), w29(2, 3), w29(3, 2), ns.family_g(4, (0, 0, 2), (4, 4, 4)),
            ns.family_g(4, (0, 0, 2), (4, 4, 6)), ns.family_g(5, (0, 0, 2),
                                                              (5, 5, 5))]
    for m in (4, 5, 6):
        for attach in ((0, 0, 2), (0, 2, 2), (1, 1, 3)):
            for outer in (1, 2):
                for spoke in (1, 2):
                    pool.append(family_core_ring(m, attach, 3, outer, spoke))
    for lengths in product(range(0, 6), repeat=3):
        if list(lengths) != sorted(lengths):
            continue
        for m in (4, 5, 6):
            for attach in ((0, 0, 2), (0, 2, 2), (0, 0, 3), (1, 1, 3)):
                pool.append(ns.family_g(m, attach, lengths))
    for _ in range(1400):                    # small hub counts: survive BR_CAP
        E = random_short(rng, rng.randint(4, 7), rng.randint(0, 2),
                         0, rng.choice((1, 1, 2, 3)))
        if E is not None:
            pool.append(E)

    n_ek = n_ek_bad = 0
    n_res = n_c7 = n_c8a = n_c8b = n_v = 0
    for E in pool:
        if not is_simple(E) or not is_2ec(E) or len(verts_of(E)) < 3:
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > BR_CAP:
            continue
        # (E-k)
        if all(len(i) <= 1 for _, _, i in br):
            n_ek += 1
            n, m = len(verts_of(E)), len(E)
            if 5 * m - 6 * (n - 1) < 5:
                n_ek_bad += 1
                print(f"  (E-k) VIOLATION: {E}")
        # (V)
        direct = {v for v, _, _ in split_usable(E)[0]}
        pred = set()
        nb = neighbors(E)
        for (u, u2, ins) in br:
            j = len(ins)
            if j >= 4 or (j == 3 and u != u2) or (
                    j == 2 and u != u2 and u2 not in nb[u]):
                pred |= set(ins)
        if not pred <= direct:
            print(f"  (V) characterization too generous on {E}: "
                  f"{sorted(pred - direct)}")
        st, info = ns.classify(E)
        if not st.endswith('CANDIDATE'):
            continue
        n_res += 1
        rig = info[0]
        Wmax = max(rig, key=len)
        S, T = set(Wmax), set(verts_of(E)) - set(Wmax)
        # (C7): distances in G[T] between boundary vertices
        Tedges = induced_edges(E, T)
        nbT = neighbors(Tedges)
        B = [w for w in T if any((w in (u, x) and (u in S or x in S))
                                 for (u, x) in E)]
        ok7 = True
        for w in B:
            dist = {w: 0}
            q = [w]
            qi = 0
            while qi < len(q):
                x = q[qi]
                qi += 1
                for y in nbT.get(x, ()):
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        q.append(y)
            for w2 in B:
                if w2 == w or w2 not in dist:
                    continue
                if dist[w2] + 1 < 6 and len(T) > dist[w2] + 1:
                    ok7 = False
        n_c7 += ok7
        if not ok7:
            print(f"  (C7) VIOLATION at maximal cluster of {E}")
        # (C8)
        Q = contraction(E, Wmax)
        if provably_infeasible(Q) == 'no-hcard':
            n_c8a += 1
        elif triangles(Tedges):
            n_c8b += 1
        else:
            print(f"  (C8) VIOLATION: maximal cluster of {E} -> {Q}")
        n_v += len(split_usable(E)[0]) > 0
    print(f"  (E-k) ultra-short instances tested: {n_ek}; "
          f"violations: {n_ek_bad}")
    print(f"  residual inhabitants tested for (C7)/(C8): {n_res}")
    print(f"  ... (C7) holds (every ear >= 6 interior):  {n_c7}")
    print(f"  ... (C8) case A (no-hcard at v*):          {n_c8a}")
    print(f"  ... (C8) case B (triangle in G[T]):        {n_c8b}")
    print(f"  ... carrying a split-usable vertex:        {n_v}")


def main():
    if '--validate' in sys.argv:
        validate()
    elif '--witness' in sys.argv:
        print("== |V| = 29 short-branch residual: (SAFE-RES) REFUTED ==")
        witness()
    elif '--search' in sys.argv:
        search()
    elif '--prime' in sys.argv:
        print("== (SAFE-RES') coverage over every residual inhabitant ==")
        prime()
    elif '--structure' in sys.argv:
        print("== coverage for the §(SAFE-RES) argument's own steps ==")
        structure()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
