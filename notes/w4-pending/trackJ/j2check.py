#!/usr/bin/env python3
"""j2check.py -- Track J, (J-2)'s mechanism checked at the stuck necklaces of (MC-83)/(MC-84).
For each necklace G and each C'-I chain w (earcover.py), with W the (J-1) witness (or the bead):
  * q certified in U(G) (dim L_G = 3 + def2(G)), exact;
  * restriction onto ((MC-68)(d)): dim of the image of L_G(q) in K^W equals dim L_{G[W]}(q|W);
  * at a random z in L_G(q): rank of G[W]'s rigidity matrix mod 2^61-1 against 6(|W|-1) (rigid),
    and rank of G's against its target (attains) -- equalities are certificates.
PYTHONHASHSEED=0, seed 20260924, repository root."""
import os, sys, random
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts'))
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts', 'w4'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
from fractions import Fraction as F
import coverstruct as cs
import earcover as ec
from exactcore import rank as rank_exact
from kbare_common import build_rigidity, rank_modp
from maincomp import sample_q, lifting_space, def_k

SEED = 20260924
for u in ['QsQsQ', 'QsQsQs', 'TsTsTs']:
    E, V = cs.necklace(u)
    rng = random.Random(f'{SEED}:j2:{u}')
    d2G = def_k(E, 3, V)
    for _ in range(20):
        q = sample_q(rng, V, E, 30)
        L = lifting_space(E, V, q)
        if len(L) == 3 + d2G:
            break
    else:
        raise SystemExit('no certified q')
    tgt = 6 * (len(V) - 1) - def_k(E, 6, V)
    co = [rng.randint(-30, 30) for _ in L]
    z = [sum(c * b[t] for c, b in zip(co, L)) for t in range(len(V))]
    pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
    rkG = rank_modp(build_rigidity(E, pt)[0])
    done = set()
    for (a, b, I) in cs.chains(E):
        c = cs.chain_data(E, V, a, b, I)
        if c['usable'] or c['k'] != 1:
            continue
        kind, W = ec.cprime_case(E, V, I[0], a, b)
        if kind != 'I' or tuple(W) in done:
            continue
        done.add(tuple(W))
        H = cs.induced(E, W)
        LH = lifting_space(H, W, {v: q[v] for v in W})
        idx = [V.index(v) for v in W]
        img = rank_exact([[bb[i] for i in idx] for bb in L])
        rkH = rank_modp(build_rigidity(H, {v: pt[v] for v in W})[0])
        print(f'{u}: chain {I[0]} delta={c["delta"]} W={W} |W|={len(W)}: dim img L_G->K^W = {img}, '
              f'dim L_H = {len(LH)} ({"onto" if img == len(LH) else "NOT onto"}); '
              f'rank G[W] = {rkH}/{6 * (len(W) - 1)}; rank G = {rkG}/{tgt}')
