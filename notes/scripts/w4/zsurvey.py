"""zsurvey.py -- §(K-main) Step MC19 (Track E): test (MC-123) and the Z-chart attainment question on small graphs.

For every simple 2EC graph on 3..N vertices (maincomp.two_ec_graphs):
  * feasible := F1 (every hub has <= 2 hub neighbours) and F2 (no triangle with two hubs);
  * A' := feasible and some closedHubNbhd has two members in a common def2-rigid subgraph
    (tested as def2(G + x adjacent to u, w) == def2(G), (MC-13)(b)'s argument);
  * at up to --draws seeded draws of the hub-plane chart (zcore.zdraw): the four conjuncts with
    explicit normals, and the rank mod 2^61-1 against 6(|V|-1) - def3.
rank_p == target certifies attainment (an exhibited nondegenerate attaining point when the conjuncts
hold at the same draw).  A shortfall at every draw is a LOWER bound only (semicontinuity).

    PYTHONHASHSEED=0 python3 zsurvey.py --exh 7 [--draws 3] [--list]
"""
import argparse
import random

from zcore import (F1, F2, chn, def2, target, zdraw, complete_normals, nondeg, rank_p,
                   verts_of)
from maincomp import two_ec_graphs


def rigid_pair(edges, u, w):
    x = ('x_new',)
    return def2(edges + [(u, x), (w, x)]) == def2(edges)


def is_Aprime(edges):
    C = chn(edges)
    pairs = set()
    for v, S in C.items():
        for i in range(len(S)):
            for j in range(i + 1, len(S)):
                pairs.add(tuple(sorted((S[i], S[j]), key=str)))
    return [p for p in sorted(pairs, key=str) if rigid_pair(edges, *p)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=7)
    ap.add_argument('--draws', type=int, default=3)
    ap.add_argument('--seed', type=int, default=20260924)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--onlyA', action='store_true', help='only run draws at A-prime graphs')
    a = ap.parse_args()
    pop = two_ec_graphs(a.exh)
    tot = dict(graphs=0, feas=0, middle=0, Ap=0, nd=0, att=0, ndatt=0, Ap_ndatt=0)
    short = []
    for name, E in pop:
        tot['graphs'] += 1
        if not (F1(E) and F2(E)):
            continue
        tot['feas'] += 1
        from zcore import triangles
        if triangles(E) and len(verts_of(E)) > 3:
            tot['middle'] += 1
        bad = is_Aprime(E)
        if bad:
            tot['Ap'] += 1
        if a.onlyA and not bad:
            continue
        tgt = target(E)
        best = (-1, False)
        for d in range(a.draws):
            rng = random.Random(f'{a.seed}:{name}:{d}')
            r = zdraw(E, rng)
            assert r is not None, name
            n, pt = r
            normal = complete_normals(E, n, pt)
            ok, why = nondeg(E, normal, pt)
            rk = rank_p(E, pt)
            best = max(best, (rk, ok))
            if ok and rk == tgt:
                break
        rk, ok = best
        tot['nd'] += ok
        tot['att'] += rk == tgt
        tot['ndatt'] += ok and rk == tgt
        if bad:
            tot['Ap_ndatt'] += ok and rk == tgt
        if not (ok and rk == tgt):
            short.append((name, E, rk, tgt, ok, bad))
        if a.list and bad:
            print(f'  A-prime {name}: |V|={len(verts_of(E))} rigid hub pairs {bad}; '
                  f'Z best draw rank {rk}/{tgt} nondeg={ok}')
    print(f"exh{a.exh}: {tot['graphs']} graphs; feasible (F1 and F2) {tot['feas']} "
          f"(with a triangle, |V|>3: {tot['middle']}); A-prime {tot['Ap']}; "
          f"Z-chart draws: nondegenerate {tot['nd']}, attaining {tot['att']}, both {tot['ndatt']} "
          f"(A-prime: {tot['Ap_ndatt']})")
    for s in short:
        print('  NOT certified:', s[0], 'rank', s[2], '/', s[3], 'nondeg', s[4], 'A-prime pairs', s[5],
              'edges', s[1])


if __name__ == '__main__':
    main()
