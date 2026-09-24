#!/usr/bin/env python3
"""
kerm0.py -- Track C driver: the exact kernel identity of (MC-69),

    dim ker M0 = dim F(H, delta) + dim F(G/H, q') - 3 - (dim S_H - dim(S_H & T)),

at `coreshrink.recipe` pictures (relaxed variant), exact Q.  S_H = the slopes
(a_c)_{c in W_att} of the core flexes F(H, delta); T = the slopes s realizable
by the outside, Y' = {(s, P_O) : outside pins at q_O, and for each attachment u,
P_u - (s_{c(u)}, 0) in K l_{uQ}}, Q the origin.  Also prints eps :=
def2(H) + def2(G/H) - def2(G) and the jet order (0 = no jump).  ASSERTS the
identity at every instance.

Mode: python3 kerm0.py   (named instances + the n <= 7 hunt pairs; seed 20260924)
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402
from exactcore import rank as rank_exact, nullspace, neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from maincomp import def_k, decode, two_ec_graphs  # noqa: E402
from nogood_subdiv import contraction  # noqa: E402
from splitext import flex_space  # noqa: E402
import coreshrink as CS  # noqa: E402
import x0arms as XA  # noqa: E402

SEED = 20260924


def hat(p):
    return (p[0], p[1], F(1))


def identity(E, W, tag):
    Ws = set(W)
    V = verts_of(E)
    O = [v for v in V if v not in Ws]
    nb = neighbors(E)
    H = [e for e in E if e[0] in Ws and e[1] in Ws]
    Eq = contraction(E, sorted(W, key=str))
    rng = random.Random(f'{SEED}:kerm0:{tag}')
    r = CS.recipe(E, sorted(W, key=str), rng, 30, 'relaxed', (F(1, 10), F(1, 10**4)))
    q, dl = r['q'], r['dl']
    VH = sorted(W, key=str)
    FH = flex_space(H, VH, dl)
    qq = dict(q)
    qq['v*'] = (F(0), F(0))
    Vq = verts_of(Eq)
    FQ = flex_space(Eq, Vq, qq)
    att = {u: next(c for c in nb[u] if c in Ws) for u in O if any(c in Ws for c in nb[u])}
    Watt = sorted(set(att.values()), key=str)
    # S_H
    S = [[v[3 * VH.index(c) + j] for c in Watt for j in (0, 1)] for v in FH]
    # Y': unknowns s (2 per Watt), P_v (3 per outside v)
    ns = 2 * len(Watt)
    N = ns + 3 * len(O)
    oi = {v: ns + 3 * k for k, v in enumerate(O)}
    si = {c: 2 * k for k, c in enumerate(Watt)}
    rows = []
    for (u, w) in E:
        if u in Ws or w in Ws:
            continue
        for p in (q[u], q[w]):
            rr = [F(0)] * N
            for j, x in enumerate(hat(p)):
                rr[oi[u] + j] += x
                rr[oi[w] + j] -= x
            rows.append(rr)
    for u, c in att.items():
        for p in (q[u], (F(0), F(0))):
            rr = [F(0)] * N
            for j, x in enumerate(hat(p)):
                rr[oi[u] + j] += x
            hp = hat(p)
            rr[si[c]] -= hp[0]
            rr[si[c] + 1] -= hp[1]
            rows.append(rr)
    Y = nullspace(rows)
    T = [v[:ns] for v in Y]
    dS = rank_exact(S) if S else 0
    dT = rank_exact(T) if T else 0
    dST = rank_exact(S + T) if (S or T) else 0
    dcap = dS + dT - dST
    pred = len(FH) + len(FQ) - 3 - (dS - dcap)
    eps = def_k(H, 3, VH) + def_k(Eq, 3) - def_k(E, 3)
    assert pred == r['dimK0'], ('kernel identity fails', tag, pred, r['dimK0'])
    return (f'{tag}: dim ker M0 = {r["dimK0"]} = {len(FH)} + {len(FQ)} - 3 - ({dS} - {dcap}); '
            f'eps = {eps}, codim = {dS - dcap}, d = dim ker M(t) = {r["d"]}, jet = {r["jet"]}')


def main():
    cases = [('x7_1716440:256', decode(7, 1716440), {2, 5, 6}),
             ('x7_1716440:0134', decode(7, 1716440), {0, 1, 3, 4})]
    from widened import W19
    from rpool import R20
    cases += [('W19', W19(), {f'c{i}' for i in range(4)}),
              ('R20', R20(), {f'c{i}' for i in range(5)})]
    Ek = [('c0', 'c1'), ('c1', 'c2'), ('c2', 'c3'), ('c3', 'c0'), ('u1', 'u2'), ('u2', 'u3'),
          ('u3', 'u1'), ('u1', 'c0'), ('u2', 'c1'), ('u3', 'c2'), ('u1', 'p1'), ('p1', 'p2'),
          ('p2', 'p3'), ('p3', 'u1')]
    cases.append(('K4pend', Ek, {'c0', 'c1', 'c2', 'c3'}))
    n = 0
    for name, E in two_ec_graphs(7):
        V = verts_of(E)
        nb = neighbors(E)
        rig, _ = XA.rigid_sets(E)
        for W in rig:
            W = set(W)
            if any(len(nb[u] & W) >= 2 for u in set(V) - W):
                continue
            cases.append((f'{name}:{"".join(map(str, sorted(W)))}', E, W))
            n += 1
    print(f'{len(cases)} instances ({n} from the simple 2EC graphs on <= 7 vertices, every proper '
          f'rigid W with G/H simple)')
    stats = {}
    for tag, E, W in cases:
        line = identity(E, W, tag)
        if not tag.startswith('x7_') or tag.startswith('x7_1716440'):
            print(' ', line)
        k = ('eps=0' if 'eps = 0' in line else 'eps>0', 'jet=0' if line.endswith('jet = 0') else 'jet>0')
        stats[k] = stats.get(k, 0) + 1
    print('identity asserted at every instance; (eps, jet) tally:', stats)


if __name__ == '__main__':
    main()
