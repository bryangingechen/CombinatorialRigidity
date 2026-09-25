#!/usr/bin/env python3
"""c1check.py -- §(K-main) Step MC21, the second reading of 2026-09-25 ((MC-165); ported from the reader's scratch): (MC-143)'s mechanism at the C'-I chains that sit in
(MC-117)'s open cell (k = 1, delta2 = 3, delta in {3, 4}).

Population: class-S members read as graph6 on stdin (e.g. geng -C -d2 -t -q 13 0:17); every k = 1
chain y that is not usable, has delta >= 3, and is C'-I in earcover.cprime_case (so W = W_Y of
(MC-142), asserted rigid / simple quotient / additive / min degree >= 2 there).  Per chain, as
rigidclose.py does for the necklaces:
  * q certified in U(G): dim L_G(q) = 3 + def2(G), exact Q;
  * restriction onto ((MC-68)(d)): rank of L_G(q) restricted to W equals dim L_{G[W]}(q|W), exact Q;
  * at a random z in L_G(q): rank of G[W]'s rigidity matrix mod 2^61-1 against 6(|W|-1), and rank
    of G's against 6(|V|-1) - def3(G).  Equalities are certificates (rank is lower semicontinuous).
Deterministic: PYTHONHASHSEED=0, seed 20260924 (per-chain stream), repository root.
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coverstruct as cs  # noqa: E402
import earcover as ec  # noqa: E402
from exactcore import rank as rank_exact  # noqa: E402
from kbare_common import build_rigidity, rank_modp  # noqa: E402
from maincomp import sample_q, lifting_space, def_k  # noqa: E402

SEED = 20260924


def certify(name, E, V, y, W, delta):
    rng = random.Random(f'{SEED}:readerC:{name}:{y}')
    d2G = def_k(E, 3, V)
    for _ in range(20):
        q = sample_q(rng, V, E, 30)
        L = lifting_space(E, V, q)
        if len(L) == 3 + d2G:
            break
    else:
        return 'no certified q'
    tgt = 6 * (len(V) - 1) - def_k(E, 6, V)
    co = [rng.randint(-30, 30) for _ in L]
    z = [sum(c * b[t] for c, b in zip(co, L)) for t in range(len(V))]
    pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
    rkG = rank_modp(build_rigidity(E, pt)[0])
    H = cs.induced(E, W)
    LH = lifting_space(H, W, {v: q[v] for v in W})
    idx = [V.index(v) for v in W]
    img = rank_exact([[bb[i] for i in idx] for bb in L])
    rkH = rank_modp(build_rigidity(H, {v: pt[v] for v in W})[0])
    ok = (img == len(LH) and rkH == 6 * (len(W) - 1) and rkG == tgt)
    return (f'delta={delta} |W|={len(W)} onto={img}/{len(LH)} rigid={rkH}/{6 * (len(W) - 1)} '
            f'G={rkG}/{tgt} {"OK" if ok else "NOT CERTIFIED"}')


def main():
    n = nS = nch = nok = 0
    for line in sys.stdin:
        if not line.strip():
            continue
        E, V = cs.g6decode(line)
        n += 1
        if not cs.in_class_S(E, V):
            continue
        nS += 1
        for (a, b, I) in cs.chains(E):
            c = cs.chain_data(E, V, a, b, I)
            if c['usable'] or c['k'] != 1 or c['delta'] < 3:
                continue
            kind, W = ec.cprime_case(E, V, I[0], a, b, c['delta'])
            if kind != 'I':
                continue
            nch += 1
            res = certify(line.strip(), E, V, I[0], W, c['delta'])
            nok += res.endswith(' OK')
            print(line.strip(), 'y', I[0], res, flush=True)
    print(f'graphs {n}, in S {nS}; C\'-I chains with delta >= 3: {nch}; certified: {nok}')


if __name__ == '__main__':
    main()
