#!/usr/bin/env python3
"""earspan.py -- the hinge lines of a long ear span Lambda^2 K^4, at incident flags too
(workbook attack-smark.md S16(iii); the witness S15(v)(d) asked for).

For an ear `w x_1 ... x_m v` with `x_1 in pi_w`, `x_m in pi_v` and `x_2 .. x_{m-1}` free,
the `m + 1` hinge lines `p_w p_{x_1}, p_{x_1} p_{x_2}, ..., p_{x_m} p_v` are computed as
Pluecker vectors in K^6 and their rank is taken exactly (Fractions).  Two flag regimes:

  generic   -- `p_w, p_v` and `pi_w, pi_v` independent draws (the `w !~ v` case);
  incident  -- `p_v in pi_w` and `p_w in pi_v`, `pi_w != pi_v` (the flags forced when the
               chain ends are adjacent, `w ~ v`, possible at `m >= 5`).

Rank is lower semicontinuous, so ONE draw with rank 6 proves that the `m + 1` lines of a
GENERIC ear at that flag regime span Lambda^2 (the ear moduli at fixed flags are an open
subset of a product of a plane, a plane and P^3's -- irreducible).  The run prints, per
`(m, regime)`, the number of draws at rank 6 out of the draws made; `m = 4` (five lines)
is printed as a control and must show rank 5.

    timeout 120 python3 notes/attacks/smark/drivers/earspan.py --seed 20260922 --draws 20

Caps, disclosed: coordinates are integers in [-20, 20]; 20 draws per cell; the flag regimes
are the two named.  Exact arithmetic; no floating point anywhere.
"""
import argparse
import itertools
import random
from fractions import Fraction as F

PAIRS = list(itertools.combinations(range(4), 2))


def v4(rng, s):
    while True:
        x = [F(rng.randint(-s, s)) for _ in range(4)]
        if any(x):
            return x


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def rank(rows):
    M = [list(r) for r in rows]
    r, ncol = 0, len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


def plane_through(rng, s, pts):
    """A normal n with n . p = 0 for every p in pts (|pts| <= 3), drawn at random."""
    while True:
        null = nullspace([list(p) for p in pts])
        if not null:
            continue
        coeffs = [F(rng.randint(-s, s)) for _ in null]
        n = [sum(c * b[i] for c, b in zip(coeffs, null)) for i in range(4)]
        if any(n):
            return n


def nullspace(M):
    """Basis of {x : M x = 0} for M with 4 columns, exact."""
    A = [list(r) for r in M]
    ncol = 4
    pivcols, r = [], 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        A[r] = [a / A[r][c] for a in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        pivcols.append(c)
        r += 1
    free = [c for c in range(ncol) if c not in pivcols]
    basis = []
    for fc in free:
        x = [F(0)] * ncol
        x[fc] = F(1)
        for i, pc in enumerate(pivcols):
            x[pc] = -A[i][fc]
        basis.append(x)
    return basis


def point_in_plane(rng, s, n):
    """A random point p with n . p = 0."""
    null = nullspace([n])
    while True:
        coeffs = [F(rng.randint(-s, s)) for _ in null]
        p = [sum(c * b[i] for c, b in zip(coeffs, null)) for i in range(4)]
        if any(p):
            return p


def pluecker(p, q):
    return [p[i] * q[j] - p[j] * q[i] for i, j in PAIRS]


def draw_flags(rng, s, regime):
    if regime == 'generic':
        pw, pv = v4(rng, s), v4(rng, s)
        nw, nv = plane_through(rng, s, [pw]), plane_through(rng, s, [pv])
    else:  # incident: p_v in pi_w, p_w in pi_v
        pw, pv = v4(rng, s), v4(rng, s)
        nw = plane_through(rng, s, [pw, pv])
        nv = plane_through(rng, s, [pw, pv])
    ok = (rank([pw, pv]) == 2 and rank([nw, nv]) == 2
          and dot(nw, pw) == 0 and dot(nv, pv) == 0)
    if regime == 'generic':
        ok = ok and dot(nw, pv) != 0 and dot(nv, pw) != 0
    else:
        ok = ok and dot(nw, pv) == 0 and dot(nv, pw) == 0
    return (pw, nw, pv, nv) if ok else None


def ear_lines(rng, s, m, flags):
    pw, nw, pv, nv = flags
    xs = [point_in_plane(rng, s, nw)] + [v4(rng, s) for _ in range(m - 2)] \
        + [point_in_plane(rng, s, nv)]
    chain = [pw] + xs + [pv]
    if any(rank([a, b]) != 2 for a, b in zip(chain[:-1], chain[1:])):
        return None
    return [pluecker(a, b) for a, b in zip(chain[:-1], chain[1:])]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, default=20260922)
    ap.add_argument('--draws', type=int, default=20)
    ap.add_argument('--s', type=int, default=20)
    ap.add_argument('--ms', default='4,5,6')
    a = ap.parse_args()
    rng = random.Random(a.seed)
    ms = [int(t) for t in a.ms.split(',')]
    print(f'earspan.py seed={a.seed} draws={a.draws} s={a.s}')
    for m in ms:
        for regime in ('generic', 'incident'):
            got, made = 0, 0
            while made < a.draws:
                flags = draw_flags(rng, a.s, regime)
                if flags is None:
                    continue
                L = ear_lines(rng, a.s, m, flags)
                if L is None:
                    continue
                made += 1
                if rank(L) == min(6, m + 1):
                    got += 1
            want = min(6, m + 1)
            print(f'  m={m} lines={m + 1} regime={regime:8s} '
                  f'rank=={want} at {got}/{made} draws')


if __name__ == '__main__':
    main()
