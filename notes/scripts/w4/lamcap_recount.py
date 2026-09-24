#!/usr/bin/env python3
"""lamcap_recount.py -- §(K-main) Step MC18 (Track B), claim (MC-115): re-runs earstep.py --lamcap's
exact placement draws (same frames FLAGS, same seed and draw order) and
reports, per orbit and k, the intersection of Lambda_ear over (a) all 12
draws, as earstep.py does, and (b) only the NON-degenerate draws (every hinge
nonzero, i.e. adjacent points distinct).  A degenerate draw has a smaller
Lambda and can only shrink (a); the placement lemma (P_k) is about generic,
hence non-degenerate, placements, so (b) is the relevant figure.  Also a
direct frame computation of the orbit-(ii), k = 1 intersection.  Exact Q;
PYTHONHASHSEED=0; repo root."""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
import scriptpath  # noqa
from fractions import Fraction as F
from exactcore import rank, wedge2, nullspace
import earstep as es

rng = random.Random(f'{es.SEED}:lamcap')
for name, (pa, na, pb, nb) in es.FLAGS.items():
    row = []
    for k in range(1, 5):
        allp, good, degen = [], [], 0
        for _ in range(12):
            if k == 1:
                pts = [pa, es.pt_in(rng, [na, nb]), pb]
            else:
                pts = ([pa, es.pt_in(rng, [na])] + [es.rnd_pt(rng) for _ in range(k - 2)]
                       + [es.pt_in(rng, [nb]), pb])
            L = [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
            ok = all(any(c != 0 for c in l) for l in L)
            allp.extend(nullspace(L))
            if ok:
                good.extend(nullspace(L))
            else:
                degen += 1
        row.append(f'k={k}: all {6 - rank(allp)}, non-degenerate {6 - rank(good)} ({degen} degenerate)')
    print(f'{name:<22} ' + '; '.join(row))
# direct: orbit (ii) frame, k = 1: every placement x on m = pi_a cap pi_b (which
# contains p_b) has the line m = x ^ p_b in Lambda(x)
pa, na, pb, nb = es.FLAGS['ii p_b in pi_a']
m_pts = nullspace([[F(c) for c in na], [F(c) for c in nb]])
m = wedge2(m_pts[0], m_pts[1])
ok = True
for (s, t) in [(1, 2), (3, -1), (-2, 5), (4, 7)]:
    x = [s * u + t * w for u, w in zip(m_pts[0], m_pts[1])]
    Lam = [wedge2(pa, x), wedge2(x, pb)]
    if rank(Lam) == 2:
        ok &= rank(Lam + [m]) == 2
print('orbit (ii), k = 1: the line m = pi_a cap pi_b lies in every non-degenerate Lambda(x):', ok)
