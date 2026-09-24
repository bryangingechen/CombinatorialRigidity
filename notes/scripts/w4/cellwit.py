#!/usr/bin/env python3
"""
cellwit.py -- §(K-main) Step MC17 (Track F): two targeted attainment checks of (MC-101)/(MC-102) at
witnesses above the census range (<= 8 vertices), plus the combinatorial
data the proofs use.  One X0 point per witness (maincomp.probe, scale 30,
seed `20260924:<name>:<draw>`, up to 4 draws); rank mod 2^61-1 equal to the
target 6(|V|-1) - def3 is a certificate that X0(G) attains (rank_p <= rank_Q
<= target).  Writes nothing.

    python3 cellwit.py

W1 (MC-101): G' = triangles 012 - 345 - 678, bridges 2-3 and 5-6, a = 0,
   b = 8: (delta, delta2) = (2, 2).  G = G' + x, x ~ a, b (10 vertices).
W2 (MC-102): G' = C6 (0..5) - bridge 3-6 - vertex 6 - bridge 6-7 - triangle
   789, a = 0, b = 9: (delta, delta2) = (2, 3), the def3-class path
   C6 - {6} - triangle (c = 0).  G = G' + x (11 vertices).
"""
import os
import random
import sys

W4 = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(W4))
sys.path.insert(0, W4)
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from maincomp import probe, def_k  # noqa: E402
from kbare_common import verts_of  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from deltapairs import deltas  # noqa: E402

SEED = 20260924


def check(name, Ep, a, b, want):
    V = verts_of(Ep)
    d2, d3 = deltas(Ep, V, a, b)
    x = max(V) + 1
    E = Ep + [(a, x), (x, b)]
    n = len(V) + 1
    tgt = 6 * (n - 1) - def_k(E, 6)
    best = None
    for dr in range(4):
        r = probe(E, random.Random(f'{SEED}:{name}:{dr}'), 30)
        best = r['rank'] if best is None else max(best, r['rank'])
        if r['rank'] == tgt:
            break
    ok = (d3, d2) == want and best == tgt
    print(f"{name}: (delta, delta2) = ({d3}, {d2}); G on {n} vertices, target {tgt}, "
          f"X0 rank {best}  {'ATTAINS (certified)' if best == tgt else 'not certified'}"
          f"  {'OK' if ok else 'FAIL'}")
    return not ok


def main():
    w1 = [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3), (5, 6),
          (6, 7), (7, 8), (8, 6)]
    c6 = [(i, (i + 1) % 6) for i in range(6)]
    w2 = c6 + [(3, 6), (6, 7), (7, 8), (8, 9), (9, 7)]
    bad = check('W1', w1, 0, 8, (2, 2)) + check('W2', w2, 0, 9, (2, 3))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
