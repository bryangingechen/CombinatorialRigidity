#!/usr/bin/env python3
"""
earstep.py -- the ear step on the main component X0 (W4 reopened, P3 Track 1;
workbook §(K-main) Step MC10, claims (MC-16)-(MC-27)).

Setting.  `G = G' + ear`: new vertices `x_1..x_k` on a path `a - x_1 - ... -
x_k - b` (open ear, `a != b`) or a closed ear `a = b`, `k >= 2`.  At a pencil
configuration the ear's hinge lines are the lines of a polygonal chain
`p_a, p_{x_1}, ..., p_{x_k}, p_b`, where `p_{x_1}` lies in `a`'s plane `pi_a` and
`p_{x_k}` in `b`'s plane `pi_b`, and the middle points are free.  The ear step
needs the span `Lambda_ear` of those lines to have the generic dimension
`min(k+1, 6)`.

Modes (exact arithmetic throughout; seeded; writes nothing):

    python3 notes/scripts/w4/earstep.py --chains
    python3 notes/scripts/w4/earstep.py --thetas 5
    python3 notes/scripts/w4/earstep.py --lamcap
    python3 notes/scripts/w4/earstep.py --rdelta 6 [--draws 3]

`--chains` prints the exact ranks behind the chain-span lemma (MC-19): its
output rows `CH-1`, `CH-2a`/`CH-2b` and `CH-3` are (MC-19)(a), (b) and (c)
(the row names predate the workbook labels and are kept so the output does not
move).  Each is ONE exhibited configuration in a projectively normal
frame, so each full-rank line is a proof for every configuration in that
frame's orbit (rank is lower semicontinuous on an irreducible parameter
space).  The frames:
  * closed polygon, `n = 3..6` generic points (CH-1);
  * open chain, generic flags: `x_1 = e0`, `x_k = e1`, `p_a = e2`, `p_b = e3`,
    middle points random (CH-2a), `k = 2..5`;
  * open chain, coincident planes `pi_a = pi_b`: `p_a, x_1, x_k, p_b` four points
    in general position in the plane `X3 = 0`, middle points random (CH-2b);
  * closed ear: `p_a, x_1, x_k` three points in general position in the plane
    `X3 = 0`, middle points random (CH-3), `k = 2..5`.
Middle points: uniform integers in `[-9, 9]^4`, seed `20260924`.

`--thetas N` exhibits, for every simple theta graph `theta(p1, p2, p3)`,
`p1 <= p2 <= p3 <= N`, an X0 point attaining `6(|V|-1) - def3` (`maincomp.
probe`, rank mod 2^61-1: a certificate).  Sampler support: `maincomp`'s.

`--lamcap` prints, per flag orbit (i)-(iv) in a standard frame (`FLAGS`) and
`k = 1..4`, the dimension of one generic `Lambda_ear` and of the intersection
of `Lambda_ear` over 12 random placements (middle points uniform integers in
`[-9, 9]^4`, seed `20260924`).  An intersection of 0 is a proof that the
intersection over ALL placements is 0 ((MC-25), (MC-26)); a nonzero value is
an upper bound only.

`--rdelta N` (a MEASUREMENT, not a proof).  For every simple 2EC graph `G'` on
3..N vertices (`maincomp.two_ec_graphs`) and every pair `a < b`: draws X0(G')
points (`maincomp.probe`, up to `--draws`), and at the first draw where `G'`
attains reports `r = rank(R + weld_ab) - rank(R)` (exact Q; the relative
screw space of `b` against `a`) against `delta = def3(G') - def3(G'/ab)`, and
`dim U`, `U = {P_a - P_b : P in F(q)}` (the 2D relative motion; the k = 1
dominance criterion is `dim U != 1`).  At a draw where `G'` attains,
`r_draw <= r_generic <= delta`, so `r_draw == delta` CERTIFIES the generic
value; a shortfall at every draw is "not found under cap".
"""
import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact, wedge2, nullspace  # noqa: E402
from kbare_common import build_rigidity, verts_of, rank_modp  # noqa: E402
from maincomp import (probe, lifting_space, _interp, def_k,  # noqa: E402
                      two_ec_graphs)

SEED = 20260924
E = [[F(int(i == j)) for j in range(4)] for i in range(4)]


def rnd_pt(rng):
    return [F(rng.randint(-9, 9)) for _ in range(4)]


def span_rank(pts, closed=False):
    """rank of the Plucker vectors of the chain (or polygon) through `pts`."""
    L = [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
    if closed:
        L.append(wedge2(pts[-1], pts[0]))
    return rank_exact(L), len(L)


def chains():
    rng = random.Random(f'{SEED}:chains')
    out = []
    for n in range(3, 7):                                   # (CH-1)
        pts = [rnd_pt(rng) for _ in range(n)]
        r, m = span_rank(pts, closed=True)
        out.append((f'CH-1 closed polygon n={n}', r, min(m, 6)))
    plane = [[F(1), F(0), F(0), F(0)], [F(0), F(1), F(0), F(0)],
             [F(0), F(0), F(1), F(0)], [F(1), F(1), F(1), F(0)]]
    for k in range(2, 6):
        mid = [rnd_pt(rng) for _ in range(k - 2)]
        # (CH-2a) generic flags: p_a = e2, x_1 = e0, ..., x_k = e1, p_b = e3
        r, m = span_rank([E[2], E[0]] + mid + [E[1], E[3]])
        out.append((f'CH-2a open ear k={k}, generic flags', r, min(m, 6)))
        # (CH-2b) pi_a = pi_b: p_a, x_1, x_k, p_b in general position in X3 = 0
        r, m = span_rank([plane[0], plane[1]] + mid + [plane[2], plane[3]])
        out.append((f'CH-2b open ear k={k}, pi_a = pi_b', r, min(m, 6)))
        # (CH-3) closed ear: p_a, x_1, x_k in general position in X3 = 0
        r, m = span_rank([plane[0], plane[1]] + mid + [plane[2]], closed=True)
        out.append((f'CH-3 closed ear k={k}', r, min(m, 6)))
    bad = 0
    for name, r, want in out:
        ok = r == want
        bad += not ok
        print(f'{name:<34} rank={r} want={want} {"OK" if ok else "FAIL"}')
    return bad


def thetas(N):
    from pitch import theta_edges
    bad = 0
    cnt = 0
    for p1 in range(1, N + 1):
        for p2 in range(max(p1, 2), N + 1):
            for p3 in range(p2, N + 1):
                edges = theta_edges([p1, p2, p3])
                V = verts_of(edges)
                tgt = 6 * (len(V) - 1) - def_k(edges, 6)
                ok = False
                for dr in range(5):
                    rng = random.Random(f'{SEED}:theta:{p1}.{p2}.{p3}:{dr}')
                    r = probe(edges, rng, 30)
                    if r['rank'] == tgt:
                        ok = True
                        break
                cnt += 1
                if not ok:
                    bad += 1
                    print(f'theta({p1},{p2},{p3}) NOT certified, best {r["rank"]}/{tgt}')
    print(f'thetas p3 <= {N}: {cnt} simple theta graphs, {cnt - bad} certified ATTAINS on X0')
    return bad


FLAGS = {  # (p_a, normal of pi_a, p_b, normal of pi_b); pi = {X : n . X = 0}
    'i generic':         (E[0], [0, 1, 0, 0], E[1], [1, 0, 1, 0]),
    'ii p_b in pi_a':    (E[0], [0, 0, 0, 1], E[1], [1, 0, 1, 0]),
    'iii both, pi_a!=pi_b': (E[0], [0, 0, 0, 1], E[1], [0, 0, 1, 0]),
    'iv pi_a = pi_b':    (E[0], [0, 0, 0, 1], E[1], [0, 0, 0, 1]),
}


def pt_in(rng, normals):
    """A random point of the intersection of the planes with these normals."""
    B = nullspace([[F(x) for x in n] for n in normals])
    c = [F(rng.randint(-9, 9)) for _ in B]
    return [sum(ci * b[j] for ci, b in zip(c, B)) for j in range(4)]


def lam_cap(T=12):
    """dim of the intersection of Lambda_ear over T random placements, per flag
    type and k = 1..4 (and the generic dim min(k+1, 6) of one Lambda)."""
    rng = random.Random(f'{SEED}:lamcap')
    for name, (pa, na, pb, nb) in FLAGS.items():
        row = []
        for k in range(1, 5):
            perps = []
            lam = None
            for _ in range(T):
                if k == 1:
                    x = pt_in(rng, [na, nb])
                    pts = [pa, x, pb]
                else:
                    pts = ([pa, pt_in(rng, [na])] + [rnd_pt(rng) for _ in range(k - 2)]
                           + [pt_in(rng, [nb]), pb])
                L = [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
                lam = rank_exact(L)
                perps.extend(nullspace(L))
            cap = 6 - rank_exact(perps)
            row.append(f'k={k}: dim Lambda={lam}, dim cap={cap}')
        print(f'{name:<22} ' + '; '.join(row))
    return 0


def weld_rows(V, a, b):
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for k in range(6):
        r = [F(0)] * (6 * len(V))
        r[6 * idx[a] + k] = F(1)
        r[6 * idx[b] + k] = F(-1)
        rows.append(r)
    return rows


def contract(edges, a, b):
    out = []
    for (u, w) in edges:
        u2 = a if u == b else u
        w2 = a if w == b else w
        if u2 != w2:
            out.append((u2, w2))
    return out


def rdelta(N, draws):
    tot = eq = lt = 0
    u1 = []
    short = []
    for name, edges in two_ec_graphs(N):
        V = verts_of(edges)
        f = def_k(edges, 6)
        tgt = 6 * (len(V) - 1) - f
        pts = []
        for dr in range(draws):
            rng = random.Random(f'{SEED}:rd:{name}:{dr}')
            r = probe(edges, rng, 30)
            if r['rank'] == tgt:
                pts.append(r)
                break
        adj = {frozenset(e) for e in edges}
        for i, a in enumerate(V):
            for b in V[i + 1:]:
                ce = contract(edges, a, b)
                vs = [v for v in V if v != b]
                g = def_k(ce, 6, vs)
                delta = f - g
                tot += 1
                if not pts:
                    short.append((name, a, b, 'G\' short at every draw'))
                    continue
                pr = pts[0]
                R = build_rigidity(edges, pr['pt'])[0]
                rr = rank_exact(R + weld_rows(V, a, b)) - rank_exact(R)
                q = pr['q']
                L = lifting_space(edges, V, q)
                zs = [_interp(edges, V, q, bb) for bb in L]
                U = [[x - y for x, y in zip(h[a], h[b])] for h in zs]
                dU = rank_exact(U) if U else 0
                if dU == 1:
                    u1.append((name, a, b, frozenset((a, b)) in adj))
                if rr == delta:
                    eq += 1
                else:
                    lt += 1
                    short.append((name, a, b, f'r={rr} < delta={delta}'))
    print(f'rdelta n <= {N}: {tot} pairs; r == delta (certified) at {eq}; '
          f'r < delta at the draw at {lt}; G\' short at every draw: '
          f'{sum(1 for s in short if "short" in s[3])}')
    for s in short[:40]:
        print('   ', s)
    na = sum(1 for x in u1 if not x[3])
    print(f'dim U == 1 (k = 1 dominance fails) at {len(u1)} pairs, '
          f'{len(u1) - na} of them adjacent, {na} non-adjacent')
    for x in [x for x in u1 if not x[3]][:20]:
        print('    non-adjacent dim U = 1:', x[:3])
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--chains', action='store_true')
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--rdelta', type=int, default=0)
    ap.add_argument('--draws', type=int, default=3)
    ap.add_argument('--lamcap', action='store_true')
    a = ap.parse_args()
    bad = 0
    if a.chains:
        bad += chains()
    if a.thetas:
        bad += thetas(a.thetas)
    if a.rdelta:
        bad += rdelta(a.rdelta, a.draws)
    if a.lamcap:
        bad += lam_cap()
    if not (a.chains or a.thetas or a.rdelta or a.lamcap):
        ap.error('name a mode')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
