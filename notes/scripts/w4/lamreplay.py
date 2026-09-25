#!/usr/bin/env python3
"""lamreplay.py (§(K-main) Step MC20's second reading, 2026-09-25; ported from the reader's scratch): replay `earstep.py --lamcap`'s exact RNG stream (seed f'{SEED}:lamcap', T = 12, the
driver's FLAGS and samplers, same draw order) and report, per orbit and k, the intersection of
Lambda over the SPAN-GENERIC draws only (lambda = the generic value).  Such an intersection is a
valid upper bound (a certificate when it meets the hand-proved lower bound).  Exact Q; imports the
landed driver unchanged.   PYTHONHASHSEED=0 python3 notes/scripts/w4/lamreplay.py   (from the repository root)"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import earstep as es
from exactcore import rank, wedge2, nullspace
GEN = {'i generic': [2, 3, 4, 5], 'ii p_b in pi_a': [2, 3, 4, 5],
       'iii both, pi_a!=pi_b': [1, 3, 4, 5], 'iv pi_a = pi_b': [2, 3, 4, 5]}
HAND = {'i generic': [0, 0, 0, 0], 'ii p_b in pi_a': [1, 0, 0, 0],
        'iii both, pi_a!=pi_b': [1, 0, 0, 0], 'iv pi_a = pi_b': [0, 3, 0, 0]}
rng = random.Random(f'{es.SEED}:lamcap')
valid = 0
for name, (pa, na, pb, nb) in es.FLAGS.items():
    row = []
    for k in range(1, 5):
        perps, used = [], 0
        for _ in range(12):
            if k == 1:
                pts = [pa, es.pt_in(rng, [na, nb]), pb]
            else:
                pts = ([pa, es.pt_in(rng, [na])] + [es.rnd_pt(rng) for _ in range(k - 2)]
                       + [es.pt_in(rng, [nb]), pb])
            L = [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
            if rank(L) != GEN[name][k - 1]:
                continue
            used += 1
            perps.extend(nullspace(L))
        cap = 6 - rank(perps)
        ok = cap == HAND[name][k - 1]
        valid += ok
        row.append(f'k={k}: {cap} over {used}/12 generic draws ({"= hand" if ok else "!= hand " + str(HAND[name][k-1])})')
    print(f'{name:<22} ' + '; '.join(row))
print(f'lamreplay: {valid}/16 cells certified by the driver\'s own span-generic draws')
