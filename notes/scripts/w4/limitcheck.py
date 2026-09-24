#!/usr/bin/env python3
"""limitcheck.py -- §(K-main) Step MC18 (Track B), claim (MC-108): the first-order limit of the ear_1
span along z0 + s z1 is Pen(y0, sigma) with sigma = ker((1-t) phi2(z1) alpha -
t phi1(z1) beta).  Compares, exactly over Q, (a) the limit line computed as in
earante.py --chord (derivatives of the two hinge extensors along the curve,
q_y(s) on m(s) through q_y0) with (b) the closed formula, at the k = 1 chains
of theta graphs and a habitat sample, several t and z1 per instance.  Also
checks that the (a)-curve lies in the lifting variety to first order.  Run
from the repository root, PYTHONHASHSEED=0."""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
from fractions import Fraction as F
from exactcore import nullspace, wedge2
from kbare_common import build_rigidity, verts_of, rank_modp
from maincomp import sample_q, lifting_space, _interp, def_k
import chordprobe as cp

SEED = 20260924

def one(label, E, a, b, rng, ntry=3):
    V = verts_of(E); nV = len(V)
    f2 = def_k(E, 3); Ec = E + [(a, b)]; d2c = def_k(Ec, 3)
    for _ in range(8):
        try:
            q = sample_q(rng, V, Ec, 30); L = lifting_space(E, V, q); Lc = lifting_space(Ec, V, q)
        except (AssertionError, RuntimeError):
            continue
        if len(L) == 3 + f2 and len(Lc) == 3 + d2c: break
    else:
        return None
    co = [rng.randint(-30, 30) for _ in Lc]
    z = [sum(c * bb[t] for c, bb in zip(co, Lc)) for t in range(nV)]
    ia, ib = V.index(a), V.index(b)
    h0 = _interp(E, V, q, z)
    D0 = [x - y for x, y in zip(h0[a], h0[b])]
    if (D0[0], D0[1]) == (0, 0):
        return 'caseB'
    pa, pb = cp.hom(q[a], z[ia]), cp.hom(q[b], z[ib])
    n = wedge2(pa, pb)
    alpha = [-h0[a][0], -h0[a][1], F(1), -h0[a][2]]
    beta = [-h0[b][0], -h0[b][1], F(1), -h0[b][2]]
    ok = tot = 0
    for _ in range(ntry):
        t = F(rng.randint(2, 9), rng.randint(12, 19))
        y0 = [(1 - t) * x + t * w for x, w in zip(pa, pb)]
        c1 = [rng.randint(-30, 30) for _ in L]
        z1 = [sum(cc * bb[s] for cc, bb in zip(c1, L)) for s in range(nV)]
        h1 = _interp(E, V, q, z1)
        D1 = [x - y for x, y in zip(h1[a], h1[b])]
        # (a) earante.py's construction
        nn = D0[0] * D0[0] + D0[1] * D0[1]
        lam_ = -cp.ev(D1, y0) / nn
        w = (lam_ * D0[0], lam_ * D0[1])
        zy1 = cp.ev(h1[a], y0) + h0[a][0] * w[0] + h0[a][1] * w[1]
        py1 = [w[0], w[1], zy1, F(0)]
        pa1 = [F(0), F(0), z1[ia], F(0)]; pb1 = [F(0), F(0), z1[ib], F(0)]
        v1 = [x + y for x, y in zip(wedge2(pa1, y0), wedge2(pa, py1))]
        v2 = [x + y for x, y in zip(wedge2(py1, pb), wedge2(y0, pb1))]
        vd = [(1 - t) * x - t * y for x, y in zip(v1, v2)]
        # first-order membership of the curve: (h_a - h_b)(s)(q_y(s)) = O(s^2)
        qy0 = (y0[0], y0[1])
        first = (D0[0] * w[0] + D0[1] * w[1]) + cp.ev(D1, qy0)
        assert first == 0, 'curve not in the lifting variety to first order'
        # (b) the closed formula
        ph1 = z1[ib] - cp.ev(h1[a], q[b]); ph2 = z1[ia] - cp.ev(h1[b], q[a])
        gam = [(1 - t) * ph2 * x - t * ph1 * y for x, y in zip(alpha, beta)]
        if all(x == 0 for x in gam) or cp.dim([n, vd]) < 2:
            continue
        S = nullspace([gam])
        v = next(s for s in S if cp.dim([pa, pb, s]) == 3)
        tot += 1
        ok += (cp.dim([n, vd, wedge2(y0, v)]) == 2)
    return (ok, tot)

if __name__ == '__main__':
    from maincomp import habitats, thetas
    insts = cp.from_members(thetas(14)) + cp.from_members(habitats()[::40])
    agg = [0, 0]; caseB = 0
    for (label, E, a, b) in insts:
        if not cp.satisfies_H(E): continue
        r = one(label, E, a, b, random.Random(f'{SEED}:lim:{label}'))
        if r == 'caseB': caseB += 1; continue
        if r: agg[0] += r[0]; agg[1] += r[1]
    print(f'limit plane: closed formula = earante construction at {agg[0]}/{agg[1]} (instance, t, z1) '
          f'triples; {caseB} case-B instances skipped (pi_a = pi_b at z0)')
