#!/usr/bin/env python3
"""SHORT-CORE workbook S48: a certificate that a generic path of D edges spans Lambda^2 K^(d+1).

    python3 notes/attacks/short-core/drivers/path_span.py --seed 1 [--d 7]

Draws one path of D + 1 points w_0, ..., w_D in Q^(d+1), D = C(d + 1, 2), with integer coordinates
in [-9, 9] from random.Random(seed), and computes, in exact arithmetic, the rank of its D joins
w_i ^ w_(i+1) in Lambda^2 Q^(d+1).  Rank D at this one draw certifies rank D at a general path
(the rank is lower semicontinuous: a nonzero D-minor at one point is a nonzero polynomial), so a
path of at least D edges whose points are general spans Lambda^2 K^(d+1).  Exit status 1 if the
drawn rank is below D (which proves nothing: a draw is a lower bound).
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir, os.pardir, os.pardir, "scripts"))
from exactcore import rank  # noqa: E402


def join(u, v):
    """Plucker coordinates of u ^ v, indexed by the pairs i < j."""
    return [u[i] * v[j] - u[j] * v[i] for i, j in combinations(range(len(u)), 2)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--d", type=int, default=7)
    args = ap.parse_args()
    n = args.d + 1
    D = n * (n - 1) // 2
    rng = random.Random(args.seed)
    pts = [[F(rng.randint(-9, 9)) for _ in range(n)] for _ in range(D + 1)]
    r = rank([join(pts[i], pts[i + 1]) for i in range(D)])
    print(f"d = {args.d}, D = {D}: rank of the {D} joins of a {D}-edge path = {r}")
    sys.exit(0 if r == D else 1)


if __name__ == "__main__":
    main()
