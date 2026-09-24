#!/usr/bin/env python3
"""
nondegx0.py -- nondegeneracy on the main component X0, (MC-12)/(MC-13) of
workbook §(K-main).

Claims checked, for a simple connected graph `G` of minimum degree >= 2.

  (MC-13)  At an admissible picture `q`, the planes of the ends of an edge
           `e = uw` coincide on the whole fibre `L(q)` (`omega_e == 0` on
           `F(q)`, i.e. `Psi(z)_u == Psi(z)_w` for every `z in L(q)`) iff
           `def2(G_e) == def2(G)`, where `G_e` is `G` plus one new vertex
           adjacent to `u` and `w` -- equivalently iff `u, w` lie in a common
           def2-rigid subgraph.  (Proof: the workbook; it uses Jackson--Jordan
           at `G_e` for one direction and at `G` for the other, so it is
           asserted only where this `q` exhibits JJ's equality at both,
           `dim L = 3 + def2`; the other draws are counted, not asserted.)
  (MC-12)  X0's generic point satisfies conjunct 3 of
           `IsNondegPencilRealization` iff every `|closedHubNbhd v| <= 3`, no
           hub-hub edge has `omega_e == 0` on `F(q)`, and no degree-2 vertex
           with two hub neighbours has both its edges so.  Conjuncts 1, 2, 4
           hold on the whole X0 chart ((MC-1)).  Asserted against
           `flanks.nondeg_conjuncts` at a drawn point of the fibre: a predicted
           degenerate graph must fail at the drawn point; a predicted
           nondegenerate one must pass at one of up to `--zdraws` drawn `z`.

Sampler support (HARNESS.md *Evidence*): `q` uniform on `[-S, S]^{2|V|}`
integers (`--scale`, default 30), rejected until admissible
(`maincomp.sample_q`); `z` a uniform `[-S, S]` combination of the RREF basis
of `L(q)`.  One `q` per graph and per `G_e` (the new vertex's position drawn
the same way).  Admissible X0 charts only.

    python3 notes/scripts/w4/nondegx0.py --battery
    python3 notes/scripts/w4/nondegx0.py --exh 7
    python3 notes/scripts/w4/nondegx0.py --thetas 12

Prints per population: graphs, edges tested, how many have some edge with
coincident planes, how many are predicted / observed degenerate on X0, and
how many draws were skipped for failing JJ.  Exits nonzero on a mismatch.
Seeded; writes nothing.
"""
import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from maincomp import (sample_q, lifting_space, _interp, def_k,  # noqa: E402
                      battery, two_ec_graphs, thetas)
from flanks import nondeg_conjuncts  # noqa: E402


def fresh(V):
    ints = [v for v in V if isinstance(v, int)]
    return (max(ints) + 1) if len(ints) == len(V) else ('x_new',)


def omega_zero(edges, V, q, L):
    """{edge index: True iff Psi(z)_u == Psi(z)_w for every basis z of L(q)}."""
    Ps = [_interp(edges, V, q, b) for b in L]
    return {i: all(P[u] == P[w] for P in Ps) for i, (u, w) in enumerate(edges)}


def check(name, edges, seed, S, zdraws):
    V = verts_of(edges)
    nb = neighbors(edges)
    d2 = def_k(edges, 3)
    rng = random.Random(f'{seed}:{name}')
    q = sample_q(rng, V, edges, S, tries=2000)
    L = lifting_space(edges, V, q)
    jj = len(L) == 3 + d2
    oz = omega_zero(edges, V, q, L)
    pred = {}
    skipped = 0
    x = fresh(V)
    for i, (u, w) in enumerate(edges):
        Ee = edges + [(u, x), (w, x)]
        pred[i] = def_k(Ee, 3) == d2
        if jj:
            # JJ at G_e, exhibited at a fresh q extending this one
            Ve = V + [x]
            qe = None
            for t in range(50):
                qx = sample_q(random.Random(f'{seed}:{name}:{i}:{t}'), [x], [], S)
                qq = dict(q)
                qq[x] = qx[x]
                try:
                    Le = lifting_space(Ee, Ve, qq)
                except AssertionError:
                    continue                  # new vertex collinear: redraw
                qe = qq
                break
            if qe is not None and len(Le) == 3 + def_k(Ee, 3):
                assert oz[i] == pred[i], ('(MC-13) fails', name, (u, w), oz[i], pred[i])
            else:
                skipped += 1
        else:
            skipped += 1
    hubs = {v for v in nb if len(nb[v]) >= 3}
    hcard = all(len({w for w in list(nb[v]) + [v] if w in hubs}) <= 3 for v in V)
    eidx = {frozenset(e): i for i, e in enumerate(edges)}
    bad = [i for i, (u, w) in enumerate(edges) if u in hubs and w in hubs and pred[i]]
    for v in V:
        if len(nb[v]) == 2 and all(w in hubs for w in nb[v]):
            a, b = sorted(nb[v], key=str)
            if pred[eidx[frozenset((v, a))]] and pred[eidx[frozenset((v, b))]]:
                bad.append(('deg2', v))
    predicted_nondeg = hcard and not bad
    observed = False
    for t in range(zdraws):
        r2 = random.Random(f'{seed}:{name}:z{t}')
        c = [r2.randint(-S, S) for _ in L]
        z = [sum(ci * bb[j] for ci, bb in zip(c, L)) for j in range(len(V))]
        pt = {v: (q[v][0], q[v][1], z[j]) for j, v in enumerate(V)}
        ok, info = nondeg_conjuncts(edges, pt)
        if not ok:
            assert info[0].startswith('conjunct 3'), ('non-conjunct-3 failure on X0', name, info)
        if ok:
            observed = True
            break
        if not predicted_nondeg:
            break
    if jj:
        assert observed == predicted_nondeg, ('(MC-12) fails', name, predicted_nondeg, bad)
    return {'edges': len(edges), 'someoz': any(pred.values()),
            'pdeg': not predicted_nondeg, 'odeg': not observed, 'skip': skipped, 'jj': jj,
            'hcard': hcard, 'pair': bool(bad)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--battery', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--seed', type=int, default=20260924)
    ap.add_argument('--scale', type=int, default=30)
    ap.add_argument('--zdraws', type=int, default=4)
    ap.add_argument('--list', action='store_true',
                    help='list the graphs that pass hcard but are degenerate on X0')
    a = ap.parse_args()
    pops = []
    if a.battery:
        pops.append(('battery', battery()))
    if a.exh:
        pops.append((f'exh{a.exh}', two_ec_graphs(a.exh)))
    if a.thetas:
        pops.append((f'thetas{a.thetas}', thetas(a.thetas)))
    if not pops:
        ap.error('name a population')
    for pname, pop in pops:
        tot = {'edges': 0, 'someoz': 0, 'pdeg': 0, 'odeg': 0, 'skip': 0, 'nojj': 0,
               'hcardpair': 0, 'nohcard': 0}
        for name, edges in pop:
            r = check(name, edges, a.seed, a.scale, a.zdraws)
            for k in ('edges', 'someoz', 'pdeg', 'odeg', 'skip'):
                tot[k] += r[k]
            tot['nojj'] += not r['jj']
            tot['nohcard'] += not r['hcard']
            tot['hcardpair'] += r['hcard'] and r['pair']
            if a.list and r['hcard'] and r['pair']:
                print('  degenerate with hcard (a rigid hub pair):', name)
        print(f"{pname}: {len(pop)} graphs, {tot['edges']} edges; "
              f"{tot['someoz']} graphs with an edge whose planes coincide on X0; "
              f"{tot['pdeg']} predicted / {tot['odeg']} observed conjunct-3-degenerate on X0 "
              f"({tot['nohcard']} fail hcard, {tot['hcardpair']} pass hcard with a rigid hub pair); "
              f"{tot['skip']} edge checks skipped (JJ not exhibited), {tot['nojj']} graphs without JJ at the draw")


if __name__ == '__main__':
    main()
