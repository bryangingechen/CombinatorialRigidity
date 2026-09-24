"""e3check.py -- sanity check of (MC-125)'s corollary on every simple 2EC graph on <= N vertices:
at a feasible graph that is not A-prime (combinatorial test: no def2-rigid subgraph holds two members
of a common closedHubNbhd), def2 == 3|V| - 3 - 2|E| and no two hubs lie in a common def2-rigid
subgraph.  Exact (pebble-game deficiencies).  PYTHONHASHSEED=0 python3 e3check.py --exh 8"""
import argparse
from zcore import F1, F2, hubs_of, def2, verts_of
from zsurvey import is_Aprime, rigid_pair
from maincomp import two_ec_graphs

ap = argparse.ArgumentParser(); ap.add_argument('--exh', type=int, default=8); a = ap.parse_args()
n_ok = n_na = n_A = 0
bad = []
for name, E in two_ec_graphs(a.exh):
    if not (F1(E) and F2(E)):
        continue
    if is_Aprime(E):
        n_A += 1
        continue
    n_na += 1
    V = verts_of(E); H = sorted(hubs_of(E), key=str)
    s = 3 * len(V) - 3 - 2 * len(E)
    hp = [(u, w) for i, u in enumerate(H) for w in H[i + 1:] if rigid_pair(E, u, w)]
    if def2(E) == s and not hp:
        n_ok += 1
    else:
        bad.append((name, def2(E), s, hp))
print(f'exh{a.exh}: feasible non-A-prime {n_na}, of which def2 = 3|V|-3-2|E| and no rigid hub pair: {n_ok}; A-prime {n_A}')
for b in bad:
    print('  COUNTEREXAMPLE', b)
