#!/usr/bin/env python3
"""dUreplay.py (§(K-main) Step MC10's second reading, 2026-09-25; ported from the reader's scratch): at `earstep.py --rdelta N`'s own accepted draws (same RNG stream), compare the
drawn dim U with the no-citation upper bound min(delta2, 3) (a !~ b) / min(delta2, 1) (a ~ b) of (MC-62),
delta2 = def2(G') - def2(G'/ab).  A draw equal to the bound certifies the generic dim U (q is in U at every
accepted draw, rdreplay.py).  Reports how many of the driver's 'dim U == 1' pairs are certified generic.
    PYTHONHASHSEED=0 python3 notes/scripts/w4/dUreplay.py N   (from the repository root)"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import earstep
from earstep import contract
from maincomp import probe, def_k, two_ec_graphs, lifting_space, _interp
from kbare_common import verts_of
from exactcore import rank as rank_exact
N = int(sys.argv[1])
tot = u1 = u1_cert = above = 0
hist = {}
for name, edges in two_ec_graphs(N):
    V = verts_of(edges)
    tgt = 6 * (len(V) - 1) - def_k(edges, 6)
    for dr in range(3):
        r = probe(edges, random.Random(f'{earstep.SEED}:rd:{name}:{dr}'), 30)
        if r['rank'] == tgt:
            break
    q = r['q']
    L = lifting_space(edges, V, q)
    zs = [_interp(edges, V, q, bb) for bb in L]
    d2 = def_k(edges, 3)
    adj = {frozenset(e) for e in edges}
    for i, a in enumerate(V):
        for b in V[i + 1:]:
            U = [[x - y for x, y in zip(h[a], h[b])] for h in zs]
            dU = rank_exact(U) if U else 0
            ce = contract(edges, a, b)
            g2 = def_k(ce, 3, [v for v in V if v != b])
            dl2 = d2 - g2
            ab = frozenset((a, b)) in adj
            bound = min(dl2, 1 if ab else 3)
            tot += 1
            above += dU > bound
            key = (ab, dU, bound)
            hist[key] = hist.get(key, 0) + 1
            if dU == 1:
                u1 += 1
                u1_cert += dU == bound
print(f'dUreplay n <= {N}: {tot} pairs; drawn dim U above the bound at {above}; '
      f'dim U == 1 drawn at {u1}, certified generic (= bound) at {u1_cert}')
print('  (adjacent, drawn dim U, bound) -> count:', dict(sorted(hist.items())))
