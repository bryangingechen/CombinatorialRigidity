#!/usr/bin/env python3
"""
splitdu.py -- §(K-main) Step MC17 (Track F): locate the Step MC11 split-off instances where the
recorded dim U exceeds min(delta2, 3).  Replays splitext.py's own IH picture
q' (same RNG stream `f'{SEED}:{name}:{x}'`, same ih_point), then computes, in
exact Q: dim U(q') for G' = G - x, and dim F(G', q') against 3 + def2(G').

(MC-62)'s citation-free half says dim U(q) <= min(delta2, 3) at every q with
dim F(G', q) = 3 + def2(G').  splitext certifies q' for G'' = G' + ab only, so
an excess can only sit at a q' that jumps for G'.

    python3 splitdu.py --exh 8 [--only-delta2 0]
"""
import argparse
import os
import random
import sys
from collections import Counter

W4 = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(W4))
sys.path.insert(0, W4)
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank as rank_exact  # noqa: E402
from maincomp import def_k, two_ec_graphs  # noqa: E402
from kbare_common import verts_of  # noqa: E402
import splitext as sx  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=8)
    ap.add_argument('--only-delta2', type=int, default=-1)
    a = ap.parse_args()
    pop = two_ec_graphs(a.exh, 4)
    tally = Counter()
    excess = []
    for name, E, x, u, w in sx.instances(pop, 10 ** 6):
        Ep = [e for e in E if x not in e]
        V = verts_of(E)
        Vpp = [v for v in V if v != x]
        cab = sx.contract(Ep, u, w)
        vab = [v for v in Vpp if v != w]
        d2p = def_k(Ep, 3, Vpp)
        d2 = d2p - def_k(cab, 3, vab)
        if a.only_delta2 >= 0 and d2 != a.only_delta2:
            continue
        Epp = sx.split_off(E, x, u, w)
        n = len(V)
        d3pp, d2pp = sx.def3_pebble(Epp), def_k(Epp, 3)
        tpp = 6 * (n - 2) - d3pp
        rng = random.Random(f'{sx.SEED}:{name}:{x}')
        ih = sx.ih_point(Epp, Vpp, rng, d2pp, tpp)
        if ih is None:
            tally['IH not certified'] += 1
            continue
        qp = ih[0]
        Fb = sx.flex_space(Ep, Vpp, qp)
        ia, ib = 3 * Vpp.index(u), 3 * Vpp.index(w)
        dU = rank_exact([[P[ia + k] - P[ib + k] for k in range(3)] for P in Fb])
        jumpG = len(Fb) - (3 + d2p)
        tally[(d2, dU, 'jump' if jumpG else 'certified-for-G\'')] += 1
        if dU > min(d2, 3):
            excess.append((name, x, u, w, d2, dU, jumpG))
    print('(delta2, dim U at q\', q\' status for G\'): count')
    for k in sorted(tally, key=str):
        print(f'  {k}: {tally[k]}')
    print(f'instances with dim U(q\') > min(delta2, 3): {len(excess)}')
    for r in excess:
        print(f'  {r[0]} x={r[1]} a={r[2]} b={r[3]} delta2={r[4]} dimU={r[5]} '
              f'dim F(G\',q\') - (3 + def2(G\')) = {r[6]}')


if __name__ == '__main__':
    main()
