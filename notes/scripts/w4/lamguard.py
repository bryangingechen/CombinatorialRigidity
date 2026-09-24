#!/usr/bin/env python3
"""
lamguard.py -- §(K-main) Step MC17 (Track F): re-check of `earstep.py --lamcap` (the certificate behind
(MC-25), (MC-26), (MC-45)) with the missing guard: every placement used in the
intersection must have the GENERIC span dimension lambda.  A placement with a
deficient span has a smaller Lambda, so intersecting over it can report 0
artificially.

Exact rational arithmetic; seeded; writes nothing.

    python3 lamguard.py            # guarded intersection, per orbit and k = 1..4
    python3 lamguard.py --replay   # the lambda of each of earstep.py's own draws
    python3 lamguard.py --hand     # the hand placements of (MC-92)'s proof, k = 2

Guarded run: 24 placements per (orbit, k), each with lambda equal to the
generic value (resampling otherwise; resamples are counted).  The
intersection is printed with a basis.  An intersection of 0 over placements
of generic span is a proof that the intersection over the generic placements
is 0 (if w lies in Lambda(y) for y in a dense open set, then
rank[Lambda-rows(y); w] <= lambda everywhere, and at a y of generic span that
says w lies in Lambda(y)).  A nonzero value is an upper bound; where it is
nonzero the claimed exact value is proved by hand in the write-up.
"""
import argparse
import os
import random
import sys

W4 = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(W4))
sys.path.insert(0, W4)
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402
from exactcore import rank as rank_exact, wedge2, nullspace  # noqa: E402
import earstep as es  # noqa: E402

SEED = 20260924


def generic_lambda(name, k):
    if k == 1 and name.startswith('iii'):
        return 1
    return min(k + 1, 6)


def placement(rng, pa, na, pb, nb, k):
    if k == 1:
        return [pa, es.pt_in(rng, [na, nb]), pb]
    return ([pa, es.pt_in(rng, [na])] + [es.rnd_pt(rng) for _ in range(k - 2)]
            + [es.pt_in(rng, [nb]), pb])


def lines(pts):
    return [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def guarded(T=24):
    rng = random.Random(f'{SEED}:lamcap2')
    for name, (pa, na, pb, nb) in es.FLAGS.items():
        out = []
        for k in range(1, 5):
            lam0 = generic_lambda(name, k)
            perps = []
            resampled = 0
            got = 0
            while got < T:
                L = lines(placement(rng, pa, na, pb, nb, k))
                if rank_exact(L) != lam0:
                    resampled += 1
                    continue
                got += 1
                perps.extend(nullspace(L))
            cap = nullspace(perps) if perps else []
            basis = ' '.join('(' + ','.join(str(x) for x in v) + ')' for v in cap)
            out.append(f'  k={k}: lambda={lam0}, dim cap={len(cap)}'
                       + (f', basis {basis}' if cap else '')
                       + f'  [{resampled} deficient draws rejected]')
        print(name)
        print('\n'.join(out))


def replay(T=12):
    """earstep.lam_cap's own RNG sequence, reporting lambda per draw."""
    rng = random.Random(f'{SEED}:lamcap')
    for name, (pa, na, pb, nb) in es.FLAGS.items():
        for k in range(1, 5):
            lams = []
            for _ in range(T):
                L = lines(placement(rng, pa, na, pb, nb, k))
                lams.append(rank_exact(L))
            lam0 = generic_lambda(name, k)
            bad = [i for i, x in enumerate(lams) if x != lam0]
            print(f'{name:<22} k={k}: lambdas {lams}'
                  + (f'  DEFICIENT at draws {bad}' if bad else ''))


def hand():
    """The explicit k = 2 placements of (MC-92)'s proof (frame e0..e3, p_a = e0,
    p_b = e3), and the exact intersection of their spans."""
    e = [[F(int(i == j)) for j in range(4)] for i in range(4)]

    def add(u, v):
        return [x + y for x, y in zip(u, v)]
    frames = {
        # orbit (i): pi_a = <e0,e1,e2>, pi_b = <e1,e2,e3>
        'i': [(e[1], e[2]), (e[2], e[1]), (add(e[0], e[1]), add(e[2], e[3]))],
        # orbit (ii): pi_a = <e0,e2,e3> (contains p_b = e3), pi_b = <e1,e2,e3>
        'ii': [(e[2], e[1]), (add(e[2], e[0]), e[1]), (e[2], add(e[1], e[2])),
               (add(e[3], e[2]), e[1])],
        # orbit (iii): pi_a = <e0,e1,e3>, pi_b = <e0,e2,e3>
        'iii': [(e[1], e[2]), (add(e[1], e[3]), e[2]), (e[1], add(e[2], e[0])),
                (e[1], add(e[2], e[3]))],
    }
    planes = {'i': ([0, 0, 0, 1], [1, 0, 0, 0]),     # normals: X3 = 0, X0 = 0
              'ii': ([0, 1, 0, 0], [1, 0, 0, 0]),    # X1 = 0, X0 = 0
              'iii': ([0, 0, 1, 0], [0, 1, 0, 0])}   # X2 = 0, X1 = 0
    bad = 0
    for orb, pls in frames.items():
        na, nb = planes[orb]
        dot = lambda n, p: sum(F(a) * b for a, b in zip(n, p))  # noqa: E731
        pa, pb = e[0], e[3]
        assert dot(na, pa) == 0 and dot(nb, pb) == 0
        inc = (dot(na, pb) == 0, dot(nb, pa) == 0)
        perps = []
        for (x1, x2) in pls:
            assert dot(na, x1) == 0 and dot(nb, x2) == 0
            L = lines([pa, x1, x2, pb])
            assert rank_exact(L) == 3, (orb, x1, x2)
            perps.extend(nullspace(L))
        cap = nullspace(perps)
        print(f'orbit ({orb}): p_b in pi_a={inc[0]}, p_a in pi_b={inc[1]}; '
              f'{len(pls)} placements, all lambda = 3; dim cap = {len(cap)}')
        bad += len(cap) != 0
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--replay', action='store_true')
    ap.add_argument('--hand', action='store_true')
    a = ap.parse_args()
    if a.replay:
        replay()
    elif a.hand:
        sys.exit(1 if hand() else 0)
    else:
        guarded()


if __name__ == '__main__':
    main()
