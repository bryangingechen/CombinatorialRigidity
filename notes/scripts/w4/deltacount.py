#!/usr/bin/env python3
"""deltacount.py -- §(K-main) Step MC18 (Track B), a check of the combinatorial claim (MC-111):
for G' satisfying (H) and a !~ b,  delta2 <= 2 => delta <= 2  and
delta2 <= 1 => delta <= 1  (delta = def3(G') - def3(G'/ab), delta2 the
same for def2; pebble-game deficiencies, exact).  Population: every simple
2EC graph on <= N vertices and every non-adjacent pair, plus random sparse
connected min-degree-2 graphs (chordprobe.random_Gp).  Asserts; prints the
(delta2, delta) table.  PYTHONHASHSEED=0; repo root."""
import os, sys, random, itertools
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
import chordprobe as cp
from maincomp import def_k, two_ec_graphs
from kbare_common import verts_of
from earstep import contract

N = int(sys.argv[1]) if len(sys.argv) > 1 else 7
R = int(sys.argv[2]) if len(sys.argv) > 2 else 200
tab = {}
def add(E):
    nb = cp.nbrs(E); V = verts_of(E)
    f, f2 = def_k(E, 6), def_k(E, 3)
    for a, b in itertools.combinations(V, 2):
        if b in nb[a]: continue
        vs = [v for v in V if v != b]
        Eab = contract(E, a, b)
        d = f - def_k(Eab, 6, vs); d2 = f2 - def_k(Eab, 3, vs)
        tab[(d2, d)] = tab.get((d2, d), 0) + 1
        assert not (d2 <= 2 and d > 2), (E, a, b, d2, d)
        assert not (d2 <= 1 and d > 1), (E, a, b, d2, d)
for _, E in two_ec_graphs(N):
    add(E)
rng = random.Random(f'{cp.SEED}:deltacount')
g = 0
while g < R:
    n = rng.randint(8, 16)
    E = cp.random_Gp(rng, n, rng.randint(0, 5))
    if cp.satisfies_H(E):
        g += 1; add(E)
print(f'(delta2, delta): count over 2EC graphs <= {N} and {R} random sparse graphs; asserts held')
for k in sorted(tab): print('  ', k, tab[k])
