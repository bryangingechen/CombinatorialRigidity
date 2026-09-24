"""zrand.py -- §(K-main) Step MC19 (Track E): a targeted hunt for A-prime graphs the Z-ear induction does not reach.

Seeded random feasible graphs: h hubs, a hub skeleton of max degree <= 2 (random paths/cycles),
then random chains (1..3 interior vertices) between random hub pairs (or closed at one hub) until
every hub has degree >= 3; kept iff simple, 2EC, F1, F2 and A-prime ((MC-14)'s combinatorial test).
Each kept graph is run through zears.Cover (base: non-A-prime or cycle).  Sampler support: the
construction above only (not uniform on any class).  A reported uncovered graph is a graph where
this proof strategy's closed cells do not suffice at any ear -- not a counterexample to anything.

    PYTHONHASHSEED=0 python3 zrand.py --n 200 --hubs 4 6 --seed 1
"""
import argparse
import random
from zcore import F1, F2, verts_of
from zsurvey import is_Aprime
from zears import Cover, key
from kbare_common import is_2ec


def build(rng, h):
    H = [('h', i) for i in range(h)]
    E = set()
    deg = {v: 0 for v in H}
    hubnb = {v: set() for v in H}
    # skeleton: random matching-like hub edges with hub-degree <= 2
    for _ in range(rng.randint(0, h)):
        u, w = rng.sample(H, 2)
        if len(hubnb[u]) < 2 and len(hubnb[w]) < 2 and w not in hubnb[u]:
            E.add(tuple(sorted((u, w)))); hubnb[u].add(w); hubnb[w].add(u); deg[u] += 1; deg[w] += 1
    c = 0
    guard = 0
    while any(deg[v] < 3 for v in H) and guard < 100:
        guard += 1
        u = rng.choice([v for v in H if deg[v] < 3])
        w = rng.choice(H)
        k = rng.choice([1, 1, 2, 2, 3])
        if w == u and k < 2:
            continue
        xs = [('x', c, j) for j in range(k)]
        c += 1
        path = [u] + xs + [w]
        for i in range(len(path) - 1):
            E.add(tuple(sorted(path[i:i + 2], key=str)))
        deg[u] += 1; deg[w] += 1
    return sorted(E, key=str)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=200)
    ap.add_argument('--hubs', type=int, nargs=2, default=[4, 6])
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--maxv', type=int, default=13)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    C = Cover()
    seen = set()
    kept = cov = 0
    unc = []
    tries = 0
    while kept < a.n and tries < 50 * a.n:
        tries += 1
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
        ok, info = C.covered(E, f'r{kept}')
        if ok:
            cov += 1
        else:
            unc.append((E, info))
    print(f'seed {a.seed}: {tries} draws, {kept} distinct A-prime graphs (|V| <= {a.maxv}), Z-ear covered {cov}')
    for E, info in unc:
        print('  UNCOVERED |V|=%d' % len(verts_of(E)), E)
        print('     ', info)


if __name__ == '__main__':
    main()
