#!/usr/bin/env python3
"""replay_odd.py (§(K-main) Steps MC17-MC18's second reading, 2026-09-25; ported from the reader's scratch) -- replays earstep.py --lamcap's own 12 draws per (orbit, k)
(same RNG stream f'{SEED}:lamcap', same draw order) and prints every draw whose span
lambda is below the generic value OR which has a zero hinge, as (index, lambda,
all-hinges-nonzero).  Shows that lamcap_recount.py's filter (hinge nonzero) differs
from the span guard at (ii) k=3 and (iv) k=1.  Exact; run from the repo root with
PYTHONHASHSEED=0."""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exactcore import rank, wedge2
import earstep as es
rng = random.Random(f'{es.SEED}:lamcap')
for name, (pa, na, pb, nb) in es.FLAGS.items():
    for k in range(1, 5):
        info = []
        for d in range(12):
            if k == 1: pts = [pa, es.pt_in(rng, [na, nb]), pb]
            else: pts = [pa, es.pt_in(rng, [na])] + [es.rnd_pt(rng) for _ in range(k-2)] + [es.pt_in(rng, [nb]), pb]
            L = [wedge2(pts[i], pts[i+1]) for i in range(len(pts)-1)]
            info.append((d, rank(L), all(any(c != 0 for c in l) for l in L)))
        lam0 = 1 if (k == 1 and name.startswith('iii')) else min(k+1, 6)
        odd = [x for x in info if x[1] != lam0 or not x[2]]
        if odd: print(f'{name:<22} k={k} generic lambda {lam0}; odd draws (idx, lambda, hinges nonzero): {odd}')
