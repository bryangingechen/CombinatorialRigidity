#!/usr/bin/env python3
"""thetareplay.py (§(K-main) Step MC20's second reading, 2026-09-25; ported from the reader's scratch): replay `earstep.py --thetas 5`'s exact RNG stream (seed f'{SEED}:theta:<p>:<dr>',
maincomp.probe, S = 30) and report, at the draw the driver accepted, whether that draw's q was
in U (dim L(q) = 3 + def2, the least value by (MC-4)(b)).  Imports the landed drivers unchanged.
    PYTHONHASHSEED=0 python3 notes/scripts/w4/thetareplay.py   (run from the repository root)"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import earstep
from maincomp import probe, def_k
from kbare_common import verts_of
from pitch import theta_edges
inU = notU = 0
for p1 in range(1, 6):
    for p2 in range(max(p1, 2), 6):
        for p3 in range(p2, 6):
            edges = theta_edges([p1, p2, p3])
            V = verts_of(edges)
            d2 = def_k(edges, 3)
            tgt = 6 * (len(V) - 1) - def_k(edges, 6)
            for dr in range(5):
                rng = random.Random(f'{earstep.SEED}:theta:{p1}.{p2}.{p3}:{dr}')
                r = probe(edges, rng, 30)
                if r['rank'] == tgt:
                    break
            ok = r['dimL'] == 3 + d2
            inU += ok
            notU += not ok
            print(f'theta({p1},{p2},{p3}): accepted draw {dr}, rank {r["rank"]}/{tgt}, '
                  f'dim L(q) = {r["dimL"]}, 3 + def2 = {3 + d2}: {"q in U" if ok else "q NOT certified in U"}')
print(f'replay: {inU} accepted draws with q certified in U, {notU} not')
