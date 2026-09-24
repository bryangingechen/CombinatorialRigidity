#!/usr/bin/env python3
"""thetapairs.py -- §(K-main) Step MC18 (Track B): G' = theta(p1, p2, p3) (every simple one with
p1+p2+p3 <= S), EVERY non-adjacent pair (a, b) with no common neighbour
(so G = G' + a-y-b is not itself a theta graph in general); reports the
chord-point profile (delta, delta2, a'(z0), r(z0), dim(rho cap n^perp)) via
chordprobe.chord_instance.  Exact Q; PYTHONHASHSEED=0; run from repo root."""
import os, sys, random, itertools
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
import chordprobe as cp
from maincomp import thetas, def_k
from kbare_common import verts_of
from earstep import contract

S = int(sys.argv[1]) if len(sys.argv) > 1 else 12
mind = int(sys.argv[2]) if len(sys.argv) > 2 else 0
hist = {}
for name, E in thetas(S):
    if not cp.satisfies_H(E):
        continue
    nb = cp.nbrs(E); V = verts_of(E)
    f, f2 = def_k(E, 6), def_k(E, 3)
    for a, b in itertools.combinations(V, 2):
        if b in nb[a] or nb[a] & nb[b]:
            continue
        vs = [v for v in V if v != b]
        d = f - def_k(contract(E, a, b), 6, vs)
        if d < mind:
            continue
        rec = cp.chord_instance(f'{name}:{a}-{b}', E, a, b,
                                random.Random(f'{cp.SEED}:tp:{name}:{a}-{b}'), nz1=0, want_truth=False)
        if rec['status'] != 'ok':
            key = ('--', d)
        else:
            key = (rec['delta'], rec['delta2'], rec['dU'], 'B' if rec['caseB'] else 'A',
                   rec['ap'], rec['r'], rec['rn'], rec['bar'])
        hist.setdefault(key, []).append(f'{name}:{a}-{b}')
print(f'-- theta pairs, p1+p2+p3 <= {S}, delta >= {mind}: (delta, delta2, dim U, case, a\', r(z0), '
      'dim(rho cap n^perp), rho in n^perp)')
for k in sorted(hist, key=str):
    print('  ', k, len(hist[k]), hist[k][:3])
