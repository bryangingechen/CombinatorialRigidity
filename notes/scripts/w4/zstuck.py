"""zstuck.py -- §(K-main) Step MC19 (Track E): a targeted hunt for A-prime graphs with NO closed-cell ear.

Such a graph has only (a) 1-chains with delta >= 1 and (b) 2-chains with adjacent ends (every other
ear type is a closed cell of the Z-ear induction, writeup (MC-127)).  Seeded random graphs of exactly
that shape: h hubs, a hub skeleton of max degree <= 2, 1-chains between non-adjacent hub pairs and
2-chains between skeleton-adjacent hub pairs, until every hub has degree >= 3; kept iff simple, 2EC,
F1, F2, A-prime.  Reports how many have no closed-cell ear at the top level, and runs zears.Cover.
Sampler support: this construction only.

    PYTHONHASHSEED=0 python3 zstuck.py --n 300 --hubs 4 8 --seed 1
"""
import argparse
import random
from zcore import F1, F2, verts_of
from zsurvey import is_Aprime
from zears import Cover, key, delta, satisfies_H
from kbare_common import is_2ec
from exactcore import neighbors
from nogood_subdiv import branch_decomposition


def build(rng, h):
    H = [('h', i) for i in range(h)]
    E = set()
    deg = {v: 0 for v in H}
    hubnb = {v: set() for v in H}
    for _ in range(rng.randint(1, h + 1)):
        u, w = rng.sample(H, 2)
        if len(hubnb[u]) < 2 and len(hubnb[w]) < 2 and w not in hubnb[u]:
            E.add(tuple(sorted((u, w), key=str))); hubnb[u].add(w); hubnb[w].add(u)
            deg[u] += 1; deg[w] += 1
    c = 0
    for _ in range(200):
        if all(deg[v] >= 3 for v in H):
            break
        u = rng.choice([v for v in H if deg[v] < 3] or H)
        if hubnb[u] and rng.random() < 0.4:
            w = rng.choice(sorted(hubnb[u], key=str)); xs = [('x', c, 0), ('x', c, 1)]
        else:
            cands = [w for w in H if w != u and w not in hubnb[u]]
            if not cands:
                continue
            w = rng.choice(cands); xs = [('x', c, 0)]
        c += 1
        path = [u] + xs + [w]
        for i in range(len(path) - 1):
            E.add(tuple(sorted(path[i:i + 2], key=str)))
        deg[u] += 1; deg[w] += 1
    return sorted(E, key=str)


def has_closed_cell_ear(E):
    hubs, branches = branch_decomposition(E)
    nb = neighbors(E)
    for (a, b, I) in branches:
        k = len(I)
        if k == 0:
            continue
        Ep = [e for e in E if not (set(e) & set(I))]
        if not satisfies_H(Ep):
            continue
        if a == b or k >= 3:
            return True
        if k == 2 and b not in neighbors(Ep).get(a, ()):
            return True
        if k == 1 and delta(Ep, a, b) == 0:
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=300)
    ap.add_argument('--hubs', type=int, nargs=2, default=[4, 8])
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--maxv', type=int, default=16)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    C = Cover()
    seen = set()
    kept = nocell = cov = 0
    unc = []
    for t in range(a.n):
        E = build(rng, rng.randint(*a.hubs))
        if len(verts_of(E)) > a.maxv or not is_2ec(E) or not (F1(E) and F2(E)):
            continue
        k_ = key(E)
        if k_ in seen:
            continue
        seen.add(k_)
        if not is_Aprime(E):
            continue
        kept += 1
        if not has_closed_cell_ear(E):
            nocell += 1
            unc.append(E)
            continue
        ok, info = C.covered(E, f's{kept}')
        cov += ok
        if not ok:
            unc.append(E)
    print(f'seed {a.seed}: {a.n} draws, {kept} distinct A-prime graphs (|V| <= {a.maxv}); '
          f'{nocell} with no closed-cell ear at the top level; {cov} Z-ear covered')
    for E in unc[:5]:
        print('  |V|=%d' % len(verts_of(E)), E)


if __name__ == '__main__':
    main()
