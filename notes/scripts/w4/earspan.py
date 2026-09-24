#!/usr/bin/env python3
"""
earspan.py -- open-ear hinge spans per flag orbit, an independent re-check (workbook §(K-main),
Step MC14, the reading that (MC-19)(b), (MC-22), (MC-24), (MC-25) need no a ≁ b; and (MC-54)).

Written by the 2026-09-24 second reader of Steps MC12/MC14; it shares no code with earstep.py.
For each of the five flag frames of a pair (p_a, π_a; p_b, π_b) with p_a != p_b -- orbit (i), (ii),
its mirror (ii'), (iii), (iv) -- and k = 1..4 interior ear vertices, at random placements
(x_1 in π_a, x_k in π_b, middle points free in K^4; for k = 1, x in π_a ∩ π_b):
  lambda = rank of the k + 1 Plücker vectors of the ear's hinge lines;
and at k = 4, the dimension of the intersection of Lambda over 12 placements.

Certificates. Rank is lower semicontinuous on the irreducible placement space, so the maximum over
the draws is a lower bound on the generic lambda; for k >= 2 it equals k + 1, the most k + 1 lines
can span, so it is the generic value. The intersection over 12 placements bounds the intersection
over all placements from above; 0 is therefore exact.

Sampler support: the frames are fixed coordinate frames (one per orbit, which suffices since PGL_4
acts transitively on each orbit); placements are integer combinations with coefficients uniform in
[-20, 20] of a basis of the relevant plane (or line, or K^4). Exact rational arithmetic; seed
20260924. Usage (repo root):  PYTHONHASHSEED=0 python3 notes/scripts/w4/earspan.py   (< 1 s)
"""
import random
from fractions import Fraction as F

SEED = 20260924
rng = random.Random(SEED)


def wedge(u, v):
    idx = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    return [u[i] * v[j] - u[j] * v[i] for i, j in idx]


def rank(rows):
    M = [list(r) for r in rows]
    rk, col, n = 0, 0, (len(M[0]) if M else 0)
    while rk < len(M) and col < n:
        piv = next((i for i in range(rk, len(M)) if M[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][col] != 0:
                f = M[i][col] / M[rk][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
        col += 1
    return rk


def nullspace(rows, n):
    M = [list(r) for r in rows]
    piv_cols, rk = [], 0
    for col in range(n):
        piv = next((i for i in range(rk, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        M[rk] = [a / M[rk][col] for a in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        piv_cols.append(col)
        rk += 1
    free = [c for c in range(n) if c not in piv_cols]
    out = []
    for fc in free:
        v = [F(0)] * n
        v[fc] = F(1)
        for r, pc in enumerate(piv_cols):
            v[pc] = -M[r][fc]
        out.append(v)
    return out


def e(i):
    return [F(int(j == i)) for j in range(4)]


def comb(basis):
    c = [F(rng.randint(-20, 20)) for _ in basis]
    return [sum(ci * b[j] for ci, b in zip(c, basis)) for j in range(4)]


def rnd():
    return [F(rng.randint(-20, 20)) for _ in range(4)]


# orbit frames: (p_a, basis of pi_a, p_b, basis of pi_b)
ORBITS = {
    '(i)   p_a notin pi_b, p_b notin pi_a': (e(2), [e(0), e(1), e(2)], e(3), [e(0), e(1), e(3)]),
    '(ii)  p_b in pi_a only':               (e(2), [e(0), e(1), e(2)], e(0), [e(0), e(1), e(3)]),
    '(ii\') p_a in pi_b only':              (e(0), [e(0), e(1), e(2)], e(3), [e(0), e(1), e(3)]),
    '(iii) both, pi_a != pi_b':             (e(0), [e(0), e(1), e(2)], e(1), [e(0), e(1), e(3)]),
    '(iv)  pi_a = pi_b':                    (e(0), [e(0), e(1), e(2)], e(1), [e(0), e(1), e(2)]),
}


def meet_basis(A, B):
    """A basis of span(A) cap span(B) in K^4."""
    # x = sum a_i A_i = sum b_j B_j  <=>  [A | -B] (a, b) = 0
    cols = A + [[-x for x in b] for b in B]
    rows = [[c[j] for c in cols] for j in range(4)]
    ns = nullspace(rows, len(cols))
    out = [[sum(v[i] * A[i][j] for i in range(len(A))) for j in range(4)] for v in ns]
    return out


def placement_lines(orb, k):
    pa, PA, pb, PB = orb
    if k == 1:
        x = comb(meet_basis(PA, PB))
        pts = [pa, x, pb]
    else:
        pts = [pa, comb(PA)] + [rnd() for _ in range(k - 2)] + [comb(PB), pb]
    return [wedge(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def main():
    draws = 6
    for name, orb in ORBITS.items():
        lams = {}
        for k in (1, 2, 3, 4):
            rs = [rank(placement_lines(orb, k)) for _ in range(draws)]
            # rank is lower semicontinuous on the irreducible placement space, so the max over
            # draws certifies a lower bound on the generic value; lower draws are special points
            lams[k] = f'{max(rs)}' + (f'({sum(r < max(rs) for r in rs)} low)' if min(rs) < max(rs) else '')
        # k = 4: intersection of Lambda over 12 placements = orthogonal complement of the normals
        normals = []
        for _ in range(12):
            L = placement_lines(orb, 4)
            ns = nullspace(L, 6)          # Lambda^perp under the dot product
            assert len(ns) == 1, 'lambda != 5 at a k = 4 draw'
            normals.append(ns[0])
        capdim = 6 - rank(normals)
        print(f'{name}: generic lambda k=1..4 >= {lams[1]} {lams[2]} {lams[3]} {lams[4]} (of {draws} draws);'
              f' dim cap_12 Lambda_4 = {capdim}')


if __name__ == '__main__':
    main()
