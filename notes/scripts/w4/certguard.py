#!/usr/bin/env python3
"""
certguard.py -- Track I (W4-reopen P1): guarded re-runs of two certificate drivers under (MC-89).

    PYTHONHASHSEED=0 python3 certguard.py --lamcap      (< 5 s)
    PYTHONHASHSEED=0 python3 certguard.py --replay      (< 2 s)
    PYTHONHASHSEED=0 python3 certguard.py --thetas 5    (< 60 s)

--lamcap   `earstep.py --lamcap` with the guard it lacks: a placement enters the intersection
           only if its span has the generic dimension (k = 1: 2, except 1 in orbit (iii);
           k >= 2: k + 1, (MC-19)(b)); deficient draws are rejected and COUNTED.  24 accepted
           placements per cell.  Frames: the driver's own FLAGS (earstep.FLAGS).  Seed
           'trackI:lamcap:20260924'.  Placement sampler: the driver's `pt_in` (uniform [-9, 9]
           combinations of an exact basis of the plane / line) and uniform [-9, 9]^4 middles.
           An intersection of 0 over accepted placements is a proof (each accepted span is a
           generic span; the intersection over all generic-span placements is contained in it);
           a nonzero value is an upper bound, and is compared with the hand-proved value.
--replay   the driver's exact RNG stream (seed f'{SEED}:lamcap', T = 12) and, per cell, the
           number of span-deficient draws it intersected.
--thetas N `earstep.py --thetas N` with the guard it lacks: the drawn picture q is CERTIFIED in
           U by dim L(q) = 3 + def2 (the least value, (MC-4)(b)), so the drawn point lies on B
           and hence on X0; the rank is then computed EXACTLY over Q (not mod p).  Up to 20
           draws per graph (sampler maincomp.sample_q, S = 30; z a uniform [-30, 30]
           combination of the exact basis of L(q)); seed 'trackI:theta:<p>:<draw>'.
           Also prints the data used by the uniform theta argument of §(K-main) Step MC20 (MC-140):
           the ear chosen (longest path), and delta = def3(C_s) - def3(C_s / ab) for k = 2.
"""
import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
import scriptpath  # noqa: F401,E402

from fractions import Fraction as F  # noqa: E402
from exactcore import rank as rank_exact, wedge2, nullspace  # noqa: E402
import earstep  # noqa: E402
from earstep import FLAGS, pt_in, rnd_pt, contract  # noqa: E402
from kbare_common import build_rigidity, verts_of  # noqa: E402
from maincomp import sample_q, lifting_space, def_k  # noqa: E402

GEN = {'i generic': [2, 3, 4, 5], 'ii p_b in pi_a': [2, 3, 4, 5],
       'iii both, pi_a!=pi_b': [1, 3, 4, 5], 'iv pi_a = pi_b': [2, 3, 4, 5]}
HAND = {'i generic': [0, 0, 0, 0], 'ii p_b in pi_a': [1, 0, 0, 0],
        'iii both, pi_a!=pi_b': [1, 0, 0, 0], 'iv pi_a = pi_b': [0, 3, 0, 0]}


def draw(rng, k, pa, na, pb, nb):
    if k == 1:
        return [pa, pt_in(rng, [na, nb]), pb]
    return ([pa, pt_in(rng, [na])] + [rnd_pt(rng) for _ in range(k - 2)]
            + [pt_in(rng, [nb]), pb])


def lines(pts):
    return [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def nz(v):
    return any(x != 0 for x in v)


def lamcap(T=24):
    rng = random.Random('trackI:lamcap:20260924')
    bad = 0
    for name, (pa, na, pb, nb) in FLAGS.items():
        row = []
        for k in range(1, 5):
            perps, acc, rej = [], 0, 0
            while acc < T:
                pts = draw(rng, k, pa, na, pb, nb)
                L = [l for l in lines(pts) if nz(l)]
                lam = rank_exact(L) if L else 0
                if lam != GEN[name][k - 1]:
                    rej += 1
                    continue
                acc += 1
                perps.extend(nullspace(L))
            cap = 6 - rank_exact(perps)
            ok = cap == HAND[name][k - 1]
            bad += not ok
            row.append(f'k={k}: cap={cap} (hand {HAND[name][k - 1]}; rejected {rej})')
        print(f'{name:<22} ' + '; '.join(row))
    print(f'lamcap (guarded): {"every cell equals the hand value" if not bad else f"{bad} MISMATCHES"}')
    return bad


def replay():
    rng = random.Random(f'{earstep.SEED}:lamcap')
    for name, (pa, na, pb, nb) in FLAGS.items():
        row = []
        for k in range(1, 5):
            defic = 0
            perps = []
            for _ in range(12):
                if k == 1:
                    x = pt_in(rng, [na, nb])
                    pts = [pa, x, pb]
                else:
                    pts = ([pa, pt_in(rng, [na])] + [rnd_pt(rng) for _ in range(k - 2)]
                           + [pt_in(rng, [nb]), pb])
                L = lines(pts)
                lam = rank_exact(L)
                defic += lam < GEN[name][k - 1]
                perps.extend(nullspace(L))
            cap = 6 - rank_exact(perps)
            row.append(f'k={k}: driver cap={cap}, deficient draws {defic}/12')
        print(f'{name:<22} ' + '; '.join(row))
    return 0


def theta_edges(p):
    from pitch import theta_edges as te
    return te(list(p))


def thetas(N):
    bad = 0
    cnt = 0
    for p1 in range(1, N + 1):
        for p2 in range(max(p1, 2), N + 1):
            for p3 in range(p2, N + 1):
                E = theta_edges((p1, p2, p3))
                V = verts_of(E)
                n = len(V)
                d2, d3 = def_k(E, 3), def_k(E, 6)
                tgt = 6 * (n - 1) - d3
                res = None
                for dr in range(20):
                    rng = random.Random(f'trackI:theta:{p1}.{p2}.{p3}:{dr}')
                    q = sample_q(rng, V, E, 30)
                    L = lifting_space(E, V, q)
                    if len(L) != 3 + d2:
                        continue                       # q not certified in U: redraw
                    coeff = [rng.randint(-30, 30) for _ in L]
                    z = [sum(c * b[i] for c, b in zip(coeff, L)) for i in range(n)]
                    pt = {v: (q[v][0], q[v][1], z[i]) for i, v in enumerate(V)}
                    if any(pt[u] == pt[w] for (u, w) in E):
                        continue
                    rows, _ = build_rigidity(E, pt)
                    rk = rank_exact(rows)
                    res = (dr, len(L), rk)
                    if rk == tgt:
                        break
                cnt += 1
                # the uniform argument's data: ear = the p3 path, G' = C_s, s = p1 + p2
                s = p1 + p2
                k = p3 - 1
                cyc = [(i, (i + 1) % s) for i in range(s)]
                a, b = 0, p1 % s
                dlt = def_k(cyc, 6) - def_k(contract(cyc, a, b), 6) if s >= 3 else None
                case = ('k>=5 (MC-20)' if k >= 5 else 'k=4 (MC-25)' if k == 4 else
                        'k=3 (MC-45)' if k == 3 else f'k=2 (MC-54), delta={dlt}' if k == 2 else
                        'k=1: L = Aff, (MC-5)(iii)')
                ok = res is not None and res[2] == tgt and (k != 2 or dlt == 0)
                if k == 1:
                    ok = ok and res[1] == 3
                bad += not ok
                print(f'theta({p1},{p2},{p3}) n={n} def2={d2} def3={d3} target={tgt}: '
                      f'{"q certified in U (dim L = 3 + def2 = %d) at draw %d, exact rank %d" % (res[1], res[0], res[2]) if res else "NO certified draw"}'
                      f'  | ear: {case}{"" if ok else "  <-- FAIL"}')
    print(f'thetas (guarded) p3 <= {N}: {cnt} graphs, {cnt - bad} certified on X0 by an exact-rank '
          f'point over a q certified in U')
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lamcap', action='store_true')
    ap.add_argument('--replay', action='store_true')
    ap.add_argument('--thetas', type=int, default=0)
    a = ap.parse_args()
    bad = 0
    if a.lamcap:
        bad += lamcap()
    if a.replay:
        bad += replay()
    if a.thetas:
        bad += thetas(a.thetas)
    raise SystemExit(1 if bad else 0)


if __name__ == '__main__':
    main()
