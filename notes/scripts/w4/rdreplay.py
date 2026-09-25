#!/usr/bin/env python3
"""rdreplay.py (§(K-main) Step MC10's second reading, 2026-09-25; ported from the reader's scratch): replay `earstep.py --rdelta N`'s own RNG stream (seed f'{SEED}:rd:<name>:<dr>',
maincomp.probe, S = 30, draws = 3) and report, at the draw the driver accepts (first attaining draw),
whether its q is certified in U (dim L(q) = 3 + def2, the least value by (MC-4)(b)).  (MC-23)'s
'r_draw <= r_generic' and (MC-18)'s 'a lower bound on dim U' need the draw on X0, i.e. q in U.
Imports the landed drivers unchanged.  Run from the repository root:
    PYTHONHASHSEED=0 python3 notes/scripts/w4/rdreplay.py N"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import earstep
from maincomp import probe, def_k, two_ec_graphs
from kbare_common import verts_of
N = int(sys.argv[1])
inU = notU = short = 0
pairs_notU = 0
for name, edges in two_ec_graphs(N):
    V = verts_of(edges)
    tgt = 6 * (len(V) - 1) - def_k(edges, 6)
    acc = None
    for dr in range(3):
        rng = random.Random(f'{earstep.SEED}:rd:{name}:{dr}')
        r = probe(edges, rng, 30)
        if r['rank'] == tgt:
            acc = r
            break
    if acc is None:
        short += 1
        continue
    d2 = def_k(edges, 3)
    if acc['dimL'] == 3 + d2:
        inU += 1
    else:
        notU += 1
        pairs_notU += len(V) * (len(V) - 1) // 2
        print(f'  {name}: accepted draw {dr} has dim L = {acc["dimL"]} > 3 + def2 = {3 + d2} (q NOT certified in U)')
print(f'rdreplay n <= {N}: graphs with accepted draw: q in U {inU}, not certified {notU} '
      f'({pairs_notU} vertex pairs); no attaining draw {short}')
