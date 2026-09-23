#!/usr/bin/env python3
"""
unitcert.py -- integer certificates with UNIT minors: spanning / independence of hinge lines in EVERY
characteristic (workbook attack-smark.md S20; obligations O11 and O10(i)).

A 6 x 6 integer matrix with determinant +-1 has rank 6 over every field; a 6 x 5 integer matrix with
some 5 x 5 minor +-1 has rank 5 over every field.  Hinge lines are Pluecker vectors
p_ij = a_i b_j - a_j b_i (i < j) of integer points a, b in Z^4.  Three certificates are searched:

  (A) ear_5 at EQUAL flags: p = e1, plane pi = {x_4 = 0} (p in pi), x1, x5 in pi, x2, x3, x4 free;
      lines p x1, x1 x2, x2 x3, x3 x4, x4 x5, x5 p.  det = +-1  ==>  the six lines span Lambda^2 K^4 over
      every field K.  This is also a hexagon through p with two vertices in pi.
  (B) pentagon p1..p5 (cyclic lines): some 5 x 5 minor +-1  ==>  the five lines are independent over every K.
  (C) hexagon p1..p6 (cyclic): det +-1  (a second, unconstrained hexagon; (A) already is one).

For each witness the driver also reports, for every consecutive triple of points, the gcd of the 3 x 3 minors
of the 3 x 4 point matrix (gcd 1 ==> the triple is linearly independent over every field) and, for every
adjacent pair, the gcd of the 2 x 2 minors (gcd 1 ==> distinct points over every field); these are the
nondegeneracy conjuncts at the witness itself (not needed for the argument, which is generic, but reported).

Search: seeded random integer coordinates in [-2, 2] (seed 20260923), first hit reported, exact integer
arithmetic (no floats).  A found witness is a proof; "not found" would only be a capped search.
Run from the repository root:  timeout 120 python3 notes/attacks/smark/drivers/unitcert.py [--seed N] [--tries N]
"""
import sys, random, argparse, itertools, math
from fractions import Fraction

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def pluecker(a, b):
    return [a[i] * b[j] - a[j] * b[i] for i, j in PAIRS]

def det(M):
    """exact integer determinant (Bareiss)."""
    n = len(M); A = [row[:] for row in M]; sign = 1; prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if A[i][k] != 0), None)
            if sw is None: return 0
            A[k], A[sw] = A[sw], A[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]

def minors_gcd(rows, k):
    """gcd of all k x k minors of a matrix given as a list of rows (len(rows) = k)."""
    n = len(rows[0]); g = 0
    for cols in itertools.combinations(range(n), k):
        g = math.gcd(g, abs(det([[r[c] for c in cols] for r in rows])))
    return g

def line_matrix(points, cyclic=True):
    """rows = Pluecker vectors of consecutive lines (6 coordinates each)."""
    n = len(points); idx = list(range(n)) + ([0] if cyclic else [])
    return [pluecker(points[idx[i]], points[idx[i + 1]]) for i in range(len(idx) - 1)]

def rank_report(points, closed):
    """nondegeneracy at the witness: consecutive triples (gcd of 3x3 minors), adjacent pairs (gcd of 2x2)."""
    n = len(points); seq = points + (points[:2] if closed else [])
    triples = [minors_gcd([seq[i], seq[i + 1], seq[i + 2]], 3) for i in range(n if closed else n - 2)]
    pairs = [minors_gcd([seq[i], seq[i + 1]], 2) for i in range(n if closed else n - 1)]
    return triples, pairs

def rand_pt(rng, in_plane=False):
    v = [rng.randint(-2, 2) for _ in range(4)]
    if in_plane: v[3] = 0
    return v

def search_ear5(rng, tries):
    p = [1, 0, 0, 0]
    for t in range(tries):
        x1, x5 = rand_pt(rng, True), rand_pt(rng, True)
        x2, x3, x4 = rand_pt(rng), rand_pt(rng), rand_pt(rng)
        pts = [p, x1, x2, x3, x4, x5]
        if any(all(c == 0 for c in q) for q in pts): continue
        M = line_matrix(pts, cyclic=True)          # p x1, x1 x2, ..., x5 p
        d = det(M)
        if abs(d) == 1: return t + 1, pts, M, d
    return None

def search_pentagon(rng, tries):
    for t in range(tries):
        pts = [rand_pt(rng) for _ in range(5)]
        if any(all(c == 0 for c in q) for q in pts): continue
        M = line_matrix(pts, cyclic=True)          # 5 rows x 6
        cols_rows = [[M[r][c] for r in range(5)] for c in range(6)]   # transpose: 6 x 5
        for rows in itertools.combinations(range(6), 5):
            d = det([cols_rows[r] for r in rows])
            if abs(d) == 1: return t + 1, pts, M, (rows, d)
    return None

def search_hexagon(rng, tries):
    for t in range(tries):
        pts = [rand_pt(rng) for _ in range(6)]
        if any(all(c == 0 for c in q) for q in pts): continue
        M = line_matrix(pts, cyclic=True); d = det(M)
        if abs(d) == 1: return t + 1, pts, M, d
    return None

def show(name, res, closed=True):
    if res is None:
        print(f"{name}: NOT FOUND under the cap (nothing follows)"); return False
    t, pts, M, info = res
    print(f"{name}: found at try {t}")
    for i, q in enumerate(pts): print(f"   point {i}: {q}")
    for i, r in enumerate(M): print(f"   line  {i}: {r}")
    print(f"   certificate: {info}")
    triples, pairs = rank_report(pts, closed)
    print(f"   consecutive triples, gcd of 3x3 minors (1 = independent in every char): {triples}")
    print(f"   adjacent pairs, gcd of 2x2 minors (1 = distinct in every char):          {pairs}")
    return True

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260923)
    ap.add_argument("--tries", type=int, default=200000)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    print(f"unitcert.py  seed {a.seed}  tries {a.tries}  coordinates in [-2, 2]  exact integers")
    ok = show("(A) ear_5 at equal flags (p = e1, pi = {x4 = 0}); 6x6 det", search_ear5(rng, a.tries))
    ok &= show("(B) pentagon; a 5x5 minor of the 6x5 Pluecker matrix (rows chosen, value)", search_pentagon(rng, a.tries))
    ok &= show("(C) hexagon; 6x6 det", search_hexagon(rng, a.tries))
    print("VERDICT:", "ALL CERTIFICATES FOUND -- rank statements hold over every field" if ok else "INCOMPLETE")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
