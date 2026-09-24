"""zlemma.py -- §(K-main) Step MC19 (Track E): checks of (MC-129) (the minimal-rigid-subgraph lemma) and of the reduction of
(MC-130), on every simple 2EC graph on <= N vertices and on zstuck-shaped random graphs.

(MC-129): if a feasible (F1, F2) simple graph satisfying (H) has a def2-rigid subgraph on >= 2
vertices, then an inclusion-minimal def2-rigid induced subgraph H0 = G[W0] is a pendant triangle
(a closed 2-chain at a hub), or contains a 1-chain y (both neighbours hubs a, b) with H0 - y
bridgeless, hence def3-rigid, hence delta(G - y; a, b) = 0.  Asserted at every graph.

(MC-130)'s reduction, recursively: at a graph with a def2-rigid subgraph take the lemma's step
(1-ear at delta = 0 -> G - y; pendant triangle at a hub of degree >= 4 -> G - {y1, y2}; at a hub
of degree 3 -> remove the lollipop down to the next hub); stop at a graph with NO def2-rigid
subgraph on >= 2 vertices (the base).  Asserted: every consumed graph is feasible, simple,
satisfies (H), and is smaller.  All exact (pebble-game deficiencies, enumeration of vertex subsets
for minimality -- small graphs only).  PYTHONHASHSEED=0 python3 zlemma.py --exh 8 [--stuck 3000]
"""
import argparse
import itertools
import random

from zcore import F1, F2, hubs_of, def2, def3, verts_of
from exactcore import neighbors
from maincomp import two_ec_graphs
from zears import satisfies_H  # noqa: E402


def induced(E, W):
    W = set(W)
    return [e for e in E if e[0] in W and e[1] in W]


def has_bridge(E):
    V = verts_of(E)

    def conn(Es):
        nb = {}
        for u, w in Es:
            nb.setdefault(u, set()).add(w)
            nb.setdefault(w, set()).add(u)
        if not V:
            return True
        s, st = {V[0]}, [V[0]]
        while st:
            v = st.pop()
            for w in nb.get(v, ()):
                if w not in s:
                    s.add(w)
                    st.append(w)
        return len(s) == len(V)
    return any(not conn(E[:i] + E[i + 1:]) for i in range(len(E)))


def minimal_rigid(E):
    """An inclusion-minimal W (|W| >= 2) with def2(G[W]) = 0, by increasing size; None if none."""
    V = verts_of(E)
    for s in range(2, len(V) + 1):
        for W in itertools.combinations(V, s):
            Ei = induced(E, W)
            if len(verts_of(Ei)) == s and def2(Ei, list(W)) == 0:
                return list(W)
    return None


def lemma_step(E):
    """Return (kind, consumed edge list) per (MC-129), or raise if the lemma fails."""
    W = minimal_rigid(E)
    if W is None:
        return None
    nb = neighbors(E)
    H = hubs_of(E)
    Ei = induced(E, W)
    if len(W) == 3 and len(Ei) == 3:
        hs = [v for v in W if v in H]
        assert len(hs) == 1, ('triangle with != 1 hub', W)
        a = hs[0]
        ys = [v for v in W if v != a]
        assert all(len(nb[y]) == 2 for y in ys)
        if len(nb[a]) >= 4:
            return 'pendant triangle, closed ear', [e for e in E if not (set(e) & set(ys))]
        # lollipop: remove the triangle, a, and the bridge chain down to the next hub
        rem = set(ys) | {a}
        prev, cur = a, [w for w in nb[a] if w not in ys][0]
        while cur not in H:
            rem.add(cur)
            prev, cur = cur, [w for w in nb[cur] if w != prev][0]
        return 'pendant triangle at a degree-3 hub, lollipop', [e for e in E if not (set(e) & rem)]
    for y in W:
        if len(nb[y]) == 2 and all(w in H for w in nb[y]):
            a, b = nb[y]
            if not has_bridge(induced(E, [v for v in W if v != y])):
                Ep = [e for e in E if y not in e]
                assert def3(induced(Ep, [v for v in W if v != y])) == 0
                d = def3(Ep) - def3([(a if u == b else u, a if w == b else w) for u, w in Ep])
                assert d == 0, ('delta != 0', y)
                return '1-ear at delta = 0', Ep
    raise AssertionError(('(MC-129) fails', E, W))


def reduce_to_base(E, trace):
    while True:
        assert F1(E) and F2(E) and satisfies_H(E)
        if all(len(v) == 2 for v in neighbors(E).values()):
            trace.append('BASE (cycle)')
            return
        st = lemma_step(E)
        if st is None:
            trace.append('BASE (no def2-rigid subgraph)')
            return
        kind, Ep = st
        assert len(verts_of(Ep)) < len(verts_of(E))
        trace.append(kind)
        E = Ep


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=8)
    ap.add_argument('--stuck', type=int, default=0)
    a = ap.parse_args()
    pops = [(f'exh{a.exh}', [E for _, E in two_ec_graphs(a.exh)])]
    if a.stuck:
        from zstuck import build
        from kbare_common import is_2ec
        rng = random.Random(1)
        pop = []
        for _ in range(a.stuck):
            E = build(rng, rng.randint(4, 7))
            if len(verts_of(E)) <= 13 and is_2ec(E) and F1(E) and F2(E):
                pop.append(E)
        pops.append((f'zstuck-shaped (seed 1, {a.stuck} draws, |V| <= 13)', pop))
    for pname, pop in pops:
        n = withrigid = 0
        kinds = {}
        for E in pop:
            if not (F1(E) and F2(E)):
                continue
            n += 1
            tr = []
            reduce_to_base(E, tr)
            if len(tr) > 1:
                withrigid += 1
            for t in tr:
                kinds[t] = kinds.get(t, 0) + 1
        print(f'{pname}: {n} feasible graphs, {withrigid} with a def2-rigid subgraph; every one reduced '
              f'to a base graph; steps used {kinds}')


if __name__ == '__main__':
    main()
