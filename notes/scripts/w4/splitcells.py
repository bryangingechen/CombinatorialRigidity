#!/usr/bin/env python3
"""
splitcells.py -- §(K-main) Step MC17 (Track F): the combinatorial (delta2, delta) of every Step MC11
split-off instance on <= N vertices (splitext.py's population and
eligibility, replicated: G simple 2EC, x of degree 2, neighbours a !~ b;
G' = G - x).  Pure partition counts (maincomp.def_k); no geometry; writes
nothing; deterministic.

    python3 splitcells.py --exh 8

Prediction being tested against Step MC11's recorded histogram
(`splitext.py --exh 8`, 4 751 instances: dim U = 0 / 1 / 2 / 3 at
3 247 / 1 017 / 374 / 113, and delta <= 1 wherever dim U = 1):
(MC-62) says dim U = min(delta2, 3) (a !~ b), and (MC-91) says delta <= delta2
when delta2 <= 2.  So the delta2 marginal should be 3 247 / 1 017 / 374 / 113,
and delta <= 1 on the delta2 = 1 row is a theorem.
"""
import argparse
import os
import sys
from collections import Counter

W4 = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(W4))
sys.path.insert(0, W4)
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from maincomp import def_k, two_ec_graphs  # noqa: E402
from exactcore import neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from splitext import instances, contract  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=8)
    a = ap.parse_args()
    pop = two_ec_graphs(a.exh, 4)
    joint = Counter()
    n = 0
    for name, E, x, u, w in instances(pop, 10 ** 6):
        Ep = [e for e in E if x not in e]
        Vp = [v for v in verts_of(E) if v != x]
        cab = contract(Ep, u, w)
        vab = [v for v in Vp if v != w]
        d2 = def_k(Ep, 3, Vp) - def_k(cab, 3, vab)
        d3 = def_k(Ep, 6, Vp) - def_k(cab, 6, vab)
        if d2 <= 2:
            assert d3 <= d2, ('F-2 fails', name, x)
        joint[(d2, d3)] += 1
        n += 1
    print(f'split-off instances on 4..{a.exh} vertices: {n}')
    marg = Counter()
    for (d2, d3), c in joint.items():
        marg[d2] += c
    print('delta2 marginal: ' + ', '.join(f'{k}: {marg[k]}' for k in sorted(marg)))
    print('joint (delta2, delta): ' + ', '.join(f'{k}: {joint[k]}' for k in sorted(joint)))


if __name__ == '__main__':
    main()
