#!/usr/bin/env python3
"""
aprime.py -- §(K-main) Step MC17 (Track F): targeted checks of (MC-94)/(MC-95) at Step MC16's (a') family
A^u (unit cycles of 4-cycles entered/left at adjacent corners; coverstruct.py
`necklace`), where every chain is in cell (a'): k = 2, a ~ b, delta = 1.

For the chain a - p - q - b of bead 0 (a, p, q, b = 0, 1, 2, 3):
  (1) (delta, delta2) of (G', a, b), G' = A^u - {p, q}              [expect (1, 1)]
  (2) at an X0(G') point where G' attains (rank mod p = target, a certificate):
      r_draw = rank_p(R + weld_ab) - target.  r_draw <= r_generic <= delta, and
      rank_p <= rank_Q, so r_draw = 1 certifies r = 1 at the generic point
      (the hinge ab is not locked);
  (3) the gadget identity of (MC-94) at an X0(G' + x) point w (x ~ a, b): with
      w' = w restricted to G',  dim M_{G'+x}(w) = dim M_weld(G')(w') = 6 + g;
  (4) X0(A^u) itself: rank = target?
Ranks mod 2^61 - 1 (kbare_common.rank_modp); points from maincomp.probe, scale 30,
seed `20260924:aprime:<name>:<draw>`, up to 4 draws.  Writes nothing.

    python3 aprime.py [--u 6 7]
"""
import argparse
import os
import random
import sys

W4 = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(W4))
sys.path.insert(0, W4)
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from maincomp import probe, def_k  # noqa: E402
from kbare_common import build_rigidity, rank_modp, verts_of  # noqa: E402
from earstep import weld_rows  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
from coverstruct import necklace  # noqa: E402

sys.path.insert(0, HERE)
from deltapairs import deltas, contract  # noqa: E402

SEED = 20260924


def attaining_point(E, name):
    V = verts_of(E)
    tgt = 6 * (len(V) - 1) - def_k(E, 6)
    for dr in range(4):
        r = probe(E, random.Random(f'{SEED}:aprime:{name}:{dr}'), 30)
        if r['rank'] == tgt:
            return r, tgt
    return None, tgt


def run(u):
    E, _ = necklace('A' * u)
    a, p, q, b = 0, 1, 2, 3
    Ep = [e for e in E if p not in e and q not in e]
    Vp = verts_of(Ep)
    d2, d3 = deltas(Ep, Vp, a, b)
    f = def_k(Ep, 6)
    g = def_k(contract(Ep, a, b), 6, [v for v in Vp if v != b])
    print(f'A^{u}: |V| = {len(verts_of(E))}; chain {a}-{p}-{q}-{b}; (delta, delta2) = ({d3}, {d2}); '
          f'f = {f}, g = {g}')
    # (2) r at an attaining X0(G') point
    pt, tgt = attaining_point(Ep, f'Gp{u}')
    if pt is None:
        print('  G\' not certified attaining in 4 draws')
    else:
        R = build_rigidity(Ep, pt['pt'])[0]
        rw = rank_modp(R + weld_rows(Vp, a, b))
        print(f'  X0(G\') point: rank {pt["rank"]} = target {tgt}; r_draw = {rw - tgt} '
              f'({"hinge ab NOT locked: r = 1 certified" if rw - tgt == 1 else "not certified"})')
    # (3) the gadget identity at an X0(G' + x) point
    x = max(Vp) + 1
    Ex = Ep + [(a, x), (x, b)]
    ptx, tgtx = attaining_point(Ex, f'Gpx{u}')
    if ptx is None:
        print('  G\' + x not certified attaining in 4 draws')
    else:
        Vx = verts_of(Ex)
        dimMx = 6 * len(Vx) - ptx['rank']
        wp = {v: ptx['pt'][v] for v in Vp}
        Rw = build_rigidity(Ep, wp)[0]
        dimMweld = 6 * len(Vp) - rank_modp(Rw + weld_rows(Vp, a, b))
        print(f'  X0(G\'+x) point: dim M_(G\'+x) = {dimMx}, dim M_weld(G\') at the restriction = '
              f'{dimMweld}, 6 + g = {6 + g}  '
              f'{"OK" if dimMx == dimMweld == 6 + g else "MISMATCH"}')
    # (4) X0(A^u)
    ptG, tgtG = attaining_point(E, f'A{u}')
    print(f'  X0(A^{u}): target {tgtG}, '
          + (f'rank {ptG["rank"]}: ATTAINS (certified)' if ptG else 'not certified in 4 draws'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--u', type=int, nargs='+', default=[6])
    a = ap.parse_args()
    for u in a.u:
        run(u)


if __name__ == '__main__':
    main()
