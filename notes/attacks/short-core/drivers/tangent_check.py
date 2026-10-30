#!/usr/bin/env python3
"""Exact controls for SHORT-CORE workbook S2, S5-S8 (d = 4, V = Q^5).

    python3 notes/attacks/short-core/drivers/tangent_check.py --seed 1 --trials 20

Each trial draws rational base data (Pi_a, Pi_b with a prescribed kappa = dim(Pi_a & Pi_b),
p_a in Pi_a, p_b in Pi_b) and ear data, and checks, in exact arithmetic:
  [T]  dim(T(y) & J(y)°) = 3, 2, 1 at k = 3, 4, 5 (S6-S8's first step);
  [D]  the derivative terms of S6 (curves A, B), S7 (A, B) and S8 lie in J(y)°;
  [I]  S6's independence: dim(<p_a,y1,y3> & <p_b,y1,y3>) = 2 iff kappa <= 2;
  [S2] kappa = 3, k = 3, rho = Pi^V: dim W = 9, W contains both stars, and
       dim(rho + Lambda_G) = 9 at a random placement x2 (S2, S5);
  [A]  adversarial rho at k = 4, 5 and at k = 3 with kappa <= 2: rho is a random subspace that
       contains S(y0) at one datum y0 (so W(y0) contains both stars); at a fresh random datum y
       the implication "W contains S(y) => W = everything" holds.
The sampler varies kappa, k and every coordinate; each figure is one draw per trial, so [A] is
evidence about the sampler's support, not a proof (the proofs are S6-S8). Exit status 1 on any
failed check.
"""
import argparse
import itertools
import random
import sys
from fractions import Fraction as F

N = 5


def rvec(rng, lo=-9, hi=9):
    return [F(rng.randint(lo, hi)) for _ in range(N)]


def comb(vs, rng):
    c = [F(rng.randint(-9, 9)) for _ in vs]
    if all(x == 0 for x in c):
        c[0] = F(1)
    return [sum(ci * v[j] for ci, v in zip(c, vs)) for j in range(N)]


def wedge(*vs):
    """Coefficients of v1 ^ ... ^ vr in the basis e_I, I increasing, as a dict."""
    r = len(vs)
    out = {}
    for I in itertools.combinations(range(N), r):
        # determinant of the r x r minor
        m = [[vs[i][j] for j in I] for i in range(r)]
        out[I] = det(m)
    return out


def det(m):
    m = [row[:] for row in m]
    n = len(m)
    d = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for r in range(c + 1, n):
            f = m[r][c] / m[c][c]
            for j in range(c, n):
                m[r][j] -= f * m[c][j]
    return d


def keys(r):
    return list(itertools.combinations(range(N), r))


def tovec(w, r):
    return [w.get(I, F(0)) for I in keys(r)]


def rank(rows):
    m = [r[:] for r in rows if any(x != 0 for x in r)]
    rk, col, ncol = 0, 0, (len(m[0]) if m else 0)
    while rk < len(m) and col < ncol:
        p = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if p is None:
            col += 1
            continue
        m[rk], m[p] = m[p], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
        col += 1
    return rk


def nullspace(rows, ncol):
    """Basis of {x : rows . x = 0}."""
    m = [r[:] for r in rows]
    piv, rk = [], 0
    for col in range(ncol):
        p = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if p is None:
            continue
        m[rk], m[p] = m[p], m[rk]
        m[rk] = [a / m[rk][col] for a in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        piv.append(col)
        rk += 1
    free = [c for c in range(ncol) if c not in piv]
    basis = []
    for fc in free:
        x = [F(0)] * ncol
        x[fc] = F(1)
        for i, pc in enumerate(piv):
            x[pc] = -m[i][fc]
        basis.append(x)
    return basis


def pair23(c2, w3):
    """c ^ omega in Lambda^5 = Q, for c in Lambda^2, omega in Lambda^3 (coefficient vectors)."""
    tot = F(0)
    for (I, a) in zip(keys(2), c2):
        if a == 0:
            continue
        for (Jx, b) in zip(keys(3), w3):
            if b == 0 or set(I) & set(Jx):
                continue
            seq = list(I) + list(Jx)
            inv = sum(1 for i in range(5) for j in range(i + 1, 5) if seq[i] > seq[j])
            tot += (-1) ** inv * a * b
    return tot


def ann3(span2):
    """Annihilator in Lambda^3 of a span of 2-vectors (list of coefficient vectors)."""
    rows = [[pair23(c, [F(int(i == j)) for j in range(10)]) for i in range(10)] for c in span2]
    return nullspace(rows, 10) if rows else [[F(int(i == j)) for j in range(10)] for i in range(10)]


def inter_dim(A, B):
    if not A or not B:
        return 0
    return rank(A) + rank(B) - rank(A + B)


def star(y):
    return [tovec(wedge(y, [F(int(i == j)) for j in range(N)]), 2) for i in range(N)]


def subspace_basis(rng, dim):
    return [rvec(rng) for _ in range(dim)]


def planes(rng, kappa):
    """Pi_a, Pi_b of dimension 3 meeting in dimension kappa."""
    while True:
        common = [rvec(rng) for _ in range(kappa)]
        A = common + [rvec(rng) for _ in range(3 - kappa)]
        B = common + [rvec(rng) for _ in range(3 - kappa)]
        if rank(A) == 3 and rank(B) == 3 and inter_dim(A, B) == kappa:
            return A, B


def ear(rng, k, Pa, Pb):
    y = {1: comb(Pa, rng)}
    for i in range(3, k):
        y[i] = rvec(rng)
    y[k] = comb(Pb, rng)
    return y


def joins(k, pa, pb, y):
    pts = [pa, y[1]] + [y[i] for i in range(3, k + 1)] + [pb]
    return [tovec(wedge(pts[i], pts[i + 1]), 2) for i in range(len(pts) - 1)]


def T3(y1, y3):
    return [tovec(wedge(y1, y3, [F(int(i == j)) for j in range(N)]), 3) for i in range(N)]


def in_ann(w3, span2):
    return all(pair23(c, w3) == 0 for c in span2)


def trial(rng, kappa, k, fails):
    Pa, Pb = planes(rng, kappa)
    pa, pb = comb(Pa, rng), comb(Pb, rng)
    y = ear(rng, k, Pa, Pb)
    J = joins(k, pa, pb, y)
    Jo = ann3(J)
    T = T3(y[1], y[3])
    # the exact generic invariant [T] needs (S6-S8): y1, y3 (k = 3); y1, y3, y4, p_b (k = 4);
    # y1, y3, y4, y5, p_b (k = 5) independent; a draw violating it is degenerate, not a failure
    guard = {3: [y[1], y[3]], 4: [y[1], y[3], y.get(4), pb],
             5: [y[1], y[3], y.get(4), y.get(5), pb]}[k]
    if rank(guard) < len(guard):
        fails.append(None)
        return Pa, Pb, pa, pb, y, J
    t_dim = inter_dim(T, Jo)
    want = {3: 3, 4: 2, 5: 1}[k]
    if t_dim != want:
        fails.append(f"[T] kappa={kappa} k={k}: dim(T & J°) = {t_dim}, want {want}")
    z0 = comb([y[4], pb], rng) if k == 4 else (y[5] if k == 5 else rvec(rng))
    zp = comb([y[4], pb], rng) if k == 4 else (y[5] if k == 5 else rvec(rng))
    terms = []
    if k == 3:
        terms = [("A", wedge(pa, y[3], z0)), ("B", wedge(y[1], pb, z0))]
    elif k == 4:
        terms = [("A", wedge(pa, y[3], z0)), ("B", wedge(y[1], y[4], z0))]
    else:
        terms = [("S8", wedge(y[1], y[4], y[5]))]
    terms.append(("T-part", wedge(y[1], y[3], zp)))
    for name, w in terms:
        if not in_ann(tovec(w, 3), J):
            fails.append(f"[D] kappa={kappa} k={k}: derivative term {name} not in J°")
    if k == 3:
        a = [pa, y[1], y[3]]
        b = [pb, y[1], y[3]]
        if rank(a) < 3 or rank(b) < 3:  # [I]'s generic invariant: both triples independent
            fails.append(None)
            return Pa, Pb, pa, pb, y, J
        d = inter_dim(a, b)
        if (d == 2) != (kappa <= 2):
            fails.append(f"[I] kappa={kappa}: dim(<p_a,y1,y3> & <p_b,y1,y3>) = {d}")
    return Pa, Pb, pa, pb, y, J


def check_S2(rng, fails):
    Pa, Pb = planes(rng, 3)
    pa, pb = comb(Pa, rng), comb(Pb, rng)
    y = ear(rng, 3, Pa, Pb)
    rho = [tovec(wedge(u, [F(int(i == j)) for j in range(N)]), 2) for u in Pa for i in range(N)]
    J = joins(3, pa, pb, y)
    W = rho + J
    S = star(y[1]) + star(y[3])
    x2 = rvec(rng)
    LG = [tovec(wedge(*e), 2) for e in [(pa, y[1]), (y[1], x2), (x2, y[3]), (y[3], pb)]]
    ok = (rank(rho) == 9 and rank(W) == 9 and rank(W + S) == 9 and rank(rho + LG) == 9)
    if not ok:
        fails.append(f"[S2] rank rho={rank(rho)} W={rank(W)} W+S={rank(W + S)} "
                     f"rho+L_G={rank(rho + LG)}")
    # the same rho at k = 4, 5 (S7, S8 say the obstruction disappears once y3 is free)
    for k in (4, 5):
        y = ear(rng, k, Pa, Pb)
        W = rho + joins(k, pa, pb, y)
        S = star(y[1]) + star(y[3])
        if not (rank(W + S) > rank(W) or rank(W) == 10):
            fails.append(f"[S2] k={k}: rho = Pi^V still obstructs (dim W = {rank(W)})")


def check_A(rng, kappa, k, fails, stats):
    Pa, Pb = planes(rng, kappa)
    pa, pb = comb(Pa, rng), comb(Pb, rng)
    y0 = ear(rng, k, Pa, Pb)
    # rho contains S(y0), plus extra random vectors, so W(y0) holds both stars
    extra = rng.randint(0, 2)
    rho = star(y0[1]) + star(y0[3]) + [[F(rng.randint(-9, 9)) for _ in range(10)]
                                       for _ in range(extra)]
    y = ear(rng, k, Pa, Pb)
    W = rho + joins(k, pa, pb, y)
    S = star(y[1]) + star(y[3])
    holds = rank(W + S) > rank(W) or rank(W) == 10
    stats[(kappa, k)] = stats.get((kappa, k), 0) + 1
    if not holds:
        fails.append(f"[A] kappa={kappa} k={k}: W ⊇ S(y) with dim W = {rank(W)} at a fresh datum")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--trials", type=int, default=20)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    fails, stats = [], {}
    for _ in range(args.trials):
        for kappa in (1, 2, 3):
            for k in (3, 4, 5):
                trial(rng, kappa, k, fails)
                if not (k == 3 and kappa == 3):
                    check_A(rng, kappa, k, fails, stats)
        check_S2(rng, fails)
    n = args.trials
    print(f"seed {args.seed}, {n} trials per (kappa, k) cell; checks [T] [D] [I]: {9 * n} draws, "
          f"[S2]: {n} draws, [A]: {sum(stats.values())} draws over cells {sorted(stats)}")
    degenerate = sum(1 for f in fails if f is None)
    fails = [f for f in fails if f is not None]
    print(f"degenerate draws skipped (guard of [T] or [I] violated): {degenerate}")
    for f in fails:
        print("FAIL", f)
    print("all checks passed" if not fails else f"{len(fails)} failures")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
