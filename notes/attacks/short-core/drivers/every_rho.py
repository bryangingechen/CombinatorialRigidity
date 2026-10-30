#!/usr/bin/env python3
"""SHORT-CORE workbook S26's control: the every-rho obstruction at k = 3, in every d.

    python3 notes/attacks/short-core/drivers/every_rho.py --seed 1 [--dims 4 5 6 7] [--trials 3]

V = K^(d+1), coordinates (x, y, z^1, ..., z^(d-2), w).  Each plane is a graph over the picture,
as in PD-STATE's configuration: Pi_a = {(x0, x1, A x, x2)} and Pi_b likewise with A + B, where B
has rank 3 - kappa, so dim(Pi_a & Pi_b) = kappa (workbook S9 (iii)).  p_a, y1 lie in Pi_a and
p_b, y3 in Pi_b, all affine (w = 1).  With H = Pi_a + Pi_b and rho = H ^ V, the script checks at
each draw, in exact arithmetic:
  (i)   W = rho + span(p_a^y1, y1^y3, y3^p_b) contains star(y1) + star(y3);
  (ii)  dim W = C(d+1, 2) - C(d-5+kappa, 2), so W is proper iff kappa >= 7 - d;
  (iii) the projection Lambda^2 P, P : V -> V/E keeping (x, y, w), maps rho onto Lambda^2 K^3,
        of dimension 3.
Each draw is guarded by the exact invariants the claims need: dim Pi_a = dim Pi_b = 3, the
intersection of dimension kappa, and p_a, y1, y3, p_b with y1, y3 independent.  S26 proves (i)-(iii)
by hand; this script is the control.  Exit status 1 on any mismatch.
"""
import argparse
import itertools
import random
import sys
from fractions import Fraction


def rank(rows):
    m = [[Fraction(v) for v in r] for r in rows]
    r = 0
    ncols = len(m[0]) if m else 0
    for c in range(ncols):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def c2(n):
    return n * (n - 1) // 2 if n >= 2 else 0


def draw(rng, d, kappa):
    n = d + 1
    pairs = list(itertools.combinations(range(n), 2))
    nz = lambda: rng.choice([v for v in range(-9, 10) if v])  # noqa: E731
    wedge = lambda u, v: [u[i] * v[j] - u[j] * v[i] for i, j in pairs]  # noqa: E731
    A = [[nz() for _ in range(3)] for _ in range(d - 2)]
    B = [[0] * 3 for _ in range(d - 2)]
    for _ in range(3 - kappa):
        col, row = [nz() for _ in range(d - 2)], [nz() for _ in range(3)]
        B = [[B[i][j] + col[i] * row[j] for j in range(3)] for i in range(d - 2)]
    Ab = [[A[i][j] + B[i][j] for j in range(3)] for i in range(d - 2)]
    lift = lambda M, x: [x[0], x[1]] + [sum(M[i][j] * x[j] for j in range(3))  # noqa: E731
                                        for i in range(d - 2)] + [x[2]]
    e3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    Pa, Pb = [lift(A, x) for x in e3], [lift(Ab, x) for x in e3]
    aff = lambda: [nz(), nz(), 1]  # noqa: E731
    pa, y1, pb, y3 = lift(A, aff()), lift(A, aff()), lift(Ab, aff()), lift(Ab, aff())
    H = Pa + Pb
    if not (rank(Pa) == 3 and rank(Pb) == 3 and 6 - rank(H) == kappa
            and rank([y1, y3]) == 2 and rank([pa, y1]) == 2 and rank([y3, pb]) == 2):
        return None
    basis = [[1 if i == j else 0 for i in range(n)] for j in range(n)]
    rho = [wedge(h, v) for h in H for v in basis]
    J = [wedge(pa, y1), wedge(y1, y3), wedge(y3, pb)]
    S = [wedge(y1, v) for v in basis] + [wedge(y3, v) for v in basis]
    keep = [pairs.index(pq) for pq in [(0, 1), (0, n - 1), (1, n - 1)]]
    dimW = rank(rho + J)
    return {
        "D": len(pairs),
        "dimW": dimW,
        "stars": rank(rho + J + S) == dimW,
        "proj": rank([[g[t] for t in keep] for g in rho]),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--dims", type=int, nargs="+", default=[4, 5, 6, 7])
    ap.add_argument("--trials", type=int, default=3)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    ok, skipped = True, 0
    for d in args.dims:
        for kappa in range(4):
            if 6 - kappa > d + 1 or 3 - kappa > d - 2:
                continue
            for _ in range(args.trials):
                res = draw(rng, d, kappa)
                if res is None:
                    skipped += 1
                    continue
                want = res["D"] - c2(d - 5 + kappa)
                proper = res["dimW"] < res["D"]
                good = (res["stars"] and res["dimW"] == want
                        and proper == (kappa >= 7 - d) and res["proj"] == 3)
                ok = ok and good
                print(f"d={d} kappa={kappa} D={res['D']} dimW={res['dimW']} "
                      f"stars={res['stars']} proper={proper} proj={res['proj']}"
                      + ("" if good else "  MISMATCH"))
    print(f"degenerate draws skipped (a guard violated): {skipped}")
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
