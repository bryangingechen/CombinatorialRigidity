#!/usr/bin/env python3
"""CERT workbook S8: the exact control for S1-S7 (R1's construction, brief sections 5-6).

    PYTHONHASHSEED=0 python3 notes/attacks/cert/drivers/cert_r1.py [--dims 3,4,5,6,7,8,9]

Nothing is drawn and nothing is seeded: the construction is deterministic (first choice in a fixed
order at every step), so the output does not vary with any seed.  Exact rationals throughout.

The construction (S6), over Q, at each d (D = C(d+1, 2)):
  m = 3   the triangle P_0, P_1, P_2 (P_0 = (0,..,0,1), P_i = e_i + P_0).
  m -> m+1, m < D: S4 then S5.  S = span of the vertices.  If S = V, the first pair (i, j) of
          vertices in lexicographic order with Y_i ^ Y_j outside W (S4 asserts one exists); else
          the first standard basis vector e_c outside S, and S4's claim that Y_i ^ e_c is outside W
          for EVERY vertex is asserted; the insertion is at the first such i.  The new vertex is
          Y_i + t u on the edge Y_i Y_(i+1), t the first of 1, 2, 3 with the (m+1)-gon good; S5's
          "at most one bad value" is asserted as "at most one of t = 1, 2, 3 fails".  Vertices are
          kept as integer vectors with positive last coordinate (projective representatives); the
          affine polygon divides each by its last coordinate (S5's rescaling).
  per m   (C1): the affine m-gon is good (its m joins have rank m).  S2 (a) at i = 0: the affine
          map g sending Y_(m-1), Y_0, Y_1 to P_1, P_0, P_2 is built and gY is asserted affine and
          good with those three vertices.  S3: the open ear p_a = p_b = gY_0, p_j = gY_j
          (k = m - 1), its k + 1 joins asserted independent and p_a, p_1, p_k, p_b at height zero.
  m = D   S7: the placements on cycles of D+1 and D+3 bodies and ears of k = D and D+2 interior
          bodies; asserted: exactly D of the links have nonzero joins, they are gY's joins, and
          they are independent; on the ears a, x_1, x_k, b at height zero.

Population: d in --dims (default 3..9); at each d every 3 <= m <= D, every 2 <= k <= D-1, and the
collapsing placements above.  No cap beyond --dims.

Controls (asserted):
  * d = 3, the three P^3 placements of brief section 1, on the chapter's hexagon certPt
    (`strata.CERT_HEXAGON`): of_cycle's closed m-gons m = 3..6 and its collapse at m = 7, 9;
    of_openEar's ears k = 5, 6, 8 (a, b at Y_0, x_k at Y_5); of_openEar_two's a, x_1, x_2, b at
    Y_4, Y_5, Y_0, Y_1 -- each independent over every field (invariant factors all 1), with the
    heights zero where (C2)/(C3) need them.  And S2 (a) applied to the hexagon at i = 0 gives a
    good affine hexagon through P_1, P_0, P_2 (R1's normal form reproduces the P^3 shape).
  * Result 21's certificates at d <= 6 (strata.py T2's cert_search, cert_ear, cert_top),
    re-asserted unimodular.
  * Negative controls: [[1, 1], [1, -1]] has invariant factors 1, 2; the goodness check rejects
    a closed 4-gon in a 3-dimensional subspace (its joins lie in a 3-dimensional Lambda^2), a
    polygon with three consecutive collinear affine points (S1's contrapositive), and the
    insertion at t = 0 (S5's excluded value).
Reported, not asserted: strata.py's `cert_top` (the odd-d detour D-gon of Result 21) at d = 7, 8, 9,
unimodular or not -- the brief's unretained probe, retained here (R2's data, not R1's).
"""
import argparse
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir, os.pardir, os.pardir, "scripts", "strata"))
import strata as st  # noqa: E402  -- read-only reuse
from exactcore import rref  # noqa: E402  -- on the path strata.py bootstraps

ext, rank, unimodular = st.ext, st.rank, st.unimodular
closed_joins, placed, elementary_divisors = st.closed_joins, st.placed, st.elementary_divisors


def unit(n, c):
    return [F(int(i == c)) for i in range(n)]


def basis_P(d):
    """P_0 = (0, .., 0, 1) and P_i = e_i + P_0, i = 1..d."""
    P0 = [F(0)] * d + [F(1)]
    return [P0] + [[F(int(c == i - 1)) for c in range(d)] + [F(1)] for i in range(1, d + 1)]


def good(Y):
    """A closed polygon is good: at least 3 vertices and its joins independent."""
    return len(Y) >= 3 and rank(closed_joins(Y)) == len(Y)


def affine(Y):
    return [[x / y[-1] for x in y] for y in Y]


class Span:
    """An incrementally reduced basis (pivot -> row), for membership tests."""

    def __init__(self, rows=()):
        self.rows = {}
        for r in rows:
            self.add(r)

    def reduce(self, v):
        v = list(v)
        for p, r in self.rows.items():
            if v[p] != 0:
                f = v[p] / r[p]
                v = [a - f * b for a, b in zip(v, r)]
        return v

    def contains(self, v):
        return not any(self.reduce(v))

    def add(self, v):
        v = self.reduce(v)
        p = next((i for i, x in enumerate(v) if x != 0), None)
        if p is None:
            return False
        for q, r in list(self.rows.items()):
            if r[p] != 0:
                f = r[p] / v[p]
                self.rows[q] = [a - f * b for a, b in zip(r, v)]
        self.rows[p] = v
        return True


def s4_choice(Y, d):
    """S4: a vertex index i and a vector u with Y_i ^ u outside W(Y); asserts S4's claims."""
    m, W = len(Y), Span(closed_joins(Y))
    if rank(Y) == d + 1:
        for i in range(m):
            for j in range(m):
                if not W.contains(ext([Y[i], Y[j]])):
                    return i, Y[j], "S=V"
        st.need(False, f"S4: S = V but every star lies in W (d={d}, m={m})")
    S = Span(Y)
    c = next((c for c in range(d + 1) if not S.contains(unit(d + 1, c))), None)
    st.need(c is not None, f"S4: S != V but every e_c lies in S (d={d}, m={m})")
    u = unit(d + 1, c)
    st.need(all(not W.contains(ext([Y[i], u])) for i in range(m)),
            f"S4: S != V but some Y_i ^ e_{c} lies in W (d={d}, m={m})")
    return 0, u, f"e{c}"


def insert(Y, i, u, t):
    y = [a + t * b for a, b in zip(Y[i], u)]
    return Y[:i + 1] + [y] + Y[i + 1:]


def affine_map(Y, i, d):
    """S2 (a): the linear g with last-coordinate functional unchanged sending Y_(i-1), Y_i, Y_(i+1)
    to P_1, P_0, P_2 (Y affine).  g(x, t) = (M (x - t y_i), t), M v_j = e_j for a basis v_1 = y_(i-1)
    - y_i, v_2 = y_(i+1) - y_i, v_3.. standard vectors."""
    m = len(Y)
    yb = [y[:d] for y in Y]
    v1 = [a - b for a, b in zip(yb[(i - 1) % m], yb[i])]
    v2 = [a - b for a, b in zip(yb[(i + 1) % m], yb[i])]
    vs = [v1, v2]
    for c in range(d):
        if len(vs) == d:
            break
        if rank(vs + [unit(d, c)]) == len(vs) + 1:
            vs.append(unit(d, c))
    st.need(len(vs) == d and rank(vs) == d, "S2 (a): v_1, v_2 not independent")
    # M = inverse of the matrix with columns v_j: solve by rref of [V^T | I]
    Vt = [[vs[j][r] for j in range(d)] for r in range(d)]  # columns v_j
    aug = [Vt[r] + unit(d, r) for r in range(d)]
    R, piv = rref(aug)
    st.need(piv == list(range(d)), "S2 (a): basis matrix singular")
    Minv = [row[d:] for row in R]  # inverse of Vt: Minv Vt = I, so Minv v_j = e_j
    yi = yb[i]

    def g(p):
        x = [a - p[-1] * b for a, b in zip(p[:d], yi)]
        return [sum(Minv[r][c] * x[c] for c in range(d)) for r in range(d)] + [p[-1]]
    return g


def heights_zero(p, d):
    return all(x == 0 for x in p[2:d])


def build(d, log):
    """S6's construction at d: the affine good m-gons, m = 3..D."""
    D = (d + 1) * d // 2
    P = basis_P(d)
    Yp = [list(P[0]), list(P[1]), list(P[2])]  # projective representatives, integer entries
    st.need(good(Yp), "S6: the triangle P_0 P_1 P_2 is not good")
    out = {3: affine(Yp)}
    steps = []
    for m in range(3, D):
        i, u, kind = s4_choice(Yp, d)
        fails, chosen = [], None
        for t in (1, 2, 3):
            Z = insert(Yp, i, u, t)
            st.need(Z[i + 1][-1] > 0, "S5: last coordinate not positive")
            if good(Z):
                chosen = chosen or (t, Z)
            else:
                fails.append(t)
        st.need(len(fails) <= 1, f"S5: t = {fails} all fail (d={d}, m={m})")
        st.need(chosen is not None, f"S5: no t in 1, 2, 3 works (d={d}, m={m})")
        t, Yp = chosen
        steps.append(f"{kind}@{i}t{t}" + (f"!{fails[0]}" if fails else ""))
        out[m + 1] = affine(Yp)
    log.append(steps)
    return out


def check_polygon(Y, d, m):
    """(C1), S2 (a), S3 at one m; returns gY."""
    P = basis_P(d)
    st.need(len(Y) == m and all(y[-1] == 1 for y in Y), f"(C1) d={d} m={m}: not affine")
    st.need(good(Y), f"(C1) d={d} m={m}: not good")
    st.need(all(Y[j] != Y[(j + 1) % m] for j in range(m)), f"S1 d={d} m={m}: joined points equal")
    g = affine_map(Y, 0, d)
    gY = [g(y) for y in Y]
    st.need(all(y[-1] == 1 for y in gY) and good(gY), f"S2 (a) d={d} m={m}: gY not affine good")
    st.need(gY[m - 1] == P[1] and gY[0] == P[0] and gY[1] == P[2],
            f"S2 (a) d={d} m={m}: three vertices not at P_1, P_0, P_2")
    k = m - 1
    ear = gY + [gY[0]]  # p_a, p_1, .., p_k, p_b = p_a
    J = [ext([ear[j], ear[j + 1]]) for j in range(k + 1)]
    st.need(rank(J) == k + 1, f"S3 d={d} k={k}: ear joins dependent")
    st.need(all(heights_zero(ear[j], d) for j in (0, 1, k, k + 1)),
            f"S3 d={d} k={k}: a, x_1, x_k, b not at height zero")
    return gY


def check_collapse(gY, d):
    """S7 on the D-gon gY: cycles of D+1, D+3 bodies, ears of k = D, D+2."""
    D = len(gY)
    Js = {tuple(j) for j in closed_joins(gY)}
    for m in (D + 1, D + 3):
        pts = placed(gY, m)
        J = [ext([pts[j], pts[(j + 1) % m]]) for j in range(m)]
        nz = [j for j in J if any(j)]
        st.need(len(nz) == D and {tuple(j) for j in nz} == Js and rank(nz) == D,
                f"S7 (a) d={d} m={m}: the placement's joins are not the D-gon's")
    for k in (D, D + 2):
        pts = placed(gY, k + 1) + [gY[0]]  # a, x_1..x_k, b
        J = [ext([pts[j], pts[j + 1]]) for j in range(k + 1)]
        nz = [j for j in J if any(j)]
        st.need(len(nz) == D and {tuple(j) for j in nz} == Js and rank(nz) == D,
                f"S7 (b) d={d} k={k}: the placement's joins are not the D-gon's")
        st.need(all(heights_zero(pts[j], d) for j in (0, 1, k, k + 1)),
                f"S7 (b) d={d} k={k}: a, x_1, x_k, b not at height zero")


def controls():
    Y = st.CERT_HEXAGON
    for m in range(3, 7):  # of_cycle, m <= 6
        st.need(unimodular(closed_joins(Y[:m])), f"control: certPt {m}-gon")
    for m in (7, 9):  # of_cycle's collapse, x_4..x_k at Y_4
        nz = [j for j in closed_joins(placed(Y, m)) if any(j)]
        st.need(len(nz) == 6 and unimodular(nz), f"control: of_cycle m={m}")
    for k in (5, 6, 8):  # of_openEar: a, b at Y_0; x_1..x_3 at Y_1..Y_3; x_4..x_(k-1) at Y_4
        pts = [Y[0], Y[1], Y[2], Y[3]] + [Y[4]] * (k - 4) + [Y[5], Y[0]]
        J = [ext([pts[j], pts[j + 1]]) for j in range(k + 1)]
        nz = [j for j in J if any(j)]
        st.need(len(nz) == 6 and unimodular(nz), f"control: of_openEar k={k}")
        st.need(all(heights_zero(pts[j], 3) for j in (0, 1, k, k + 1)),
                f"control: of_openEar k={k} heights")
    pts = [Y[4], Y[5], Y[0], Y[1]]  # of_openEar_two
    st.need(unimodular([ext([pts[j], pts[j + 1]]) for j in range(3)])
            and all(heights_zero(p, 3) for p in pts), "control: of_openEar_two")
    g = affine_map(Y, 0, 3)
    gY = [g(y) for y in Y]
    P = basis_P(3)
    st.need(good(gY) and gY[5] == P[1] and gY[0] == P[0] and gY[1] == P[2],
            "control: S2 (a) on the hexagon")
    # Result 21's certificates at d <= 6
    for d in (3, 4, 5, 6):
        D = (d + 1) * d // 2
        for m in range(3, D):
            st.need(unimodular(closed_joins(st.cert_search(d, m)[0])), f"Result 21 d={d} m={m}")
        for k in range(2, D - 1):
            Ye = st.cert_ear(d, k)[0]
            st.need(unimodular([ext([Ye[j], Ye[j + 1]]) for j in range(k + 1)]),
                    f"Result 21 ear d={d} k={k}")
        st.need(unimodular(closed_joins(st.cert_top(d)[0])), f"Result 21 cert_top d={d}")
    # negative controls
    neg = [[F(1), F(1)], [F(1), F(-1)]]
    st.need(elementary_divisors(neg) == [1, 2] and not unimodular(neg), "negative: [[1,1],[1,-1]]")
    P = basis_P(4)
    flat4 = [P[0], P[1], P[2], [a + b - c for a, b, c in zip(P[1], P[2], P[0])]]
    st.need(not good(flat4), "negative: a 4-gon in a 3-space passed")
    col = [P[0], P[1], [2 * a - b for a, b in zip(P[1], P[0])], P[3]]
    st.need(not good(col), "negative: three consecutive collinear points passed")
    tri = [P[0], P[1], P[2]]
    st.need(not good(insert(tri, 0, P[3], 0)), "negative: t = 0 passed")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", default="3,4,5,6,7,8,9")
    a = ap.parse_args()
    dims = [int(x) for x in a.dims.split(",")]
    print("CERT S8: R1's construction (S6), checked exactly over Q; population d in "
          f"{dims}, every 3 <= m <= D, every 2 <= k <= D-1, collapses at m = D+1, D+3 and "
          "k = D, D+2.  Deterministic, no seed.")
    controls()
    print("controls: P^3 placements on certPt (cycle m=3..6, 7, 9; ears k=5, 6, 8; ear k=2), "
          "S2 (a) on the hexagon, Result 21 at d<=6, negative controls: all pass")
    for d in dims:
        D = (d + 1) * d // 2
        log = []
        polys = build(d, log)
        for m in range(3, D + 1):
            gY = check_polygon(polys[m], d, m)
        check_collapse(gY, d)
        steps = log[0]
        nS = sum(s.startswith("S=V") for s in steps)
        fails = [s for s in steps if "!" in s]
        print(f"d={d} D={D:>2}: (C1) m=3..{D}, (C2)/(C3) k=2..{D - 1}, S7 collapses: pass; "
              f"{len(steps)} insertions ({nS} with S = V, {len(steps) - nS} with S != V); "
              f"t chosen: " + "".join(s.split("t")[-1][0] for s in steps)
              + f"; a failing t among 1,2,3 at {len(fails)} steps")
    rep = []
    for d in (7, 8, 9):
        if d in dims:
            Y = st.cert_top(d)[0]
            rep.append(f"d={d}: {len(Y)}-gon, unimodular {unimodular(closed_joins(Y))}")
    if rep:
        print("reported (R2's data): strata.cert_top at " + "; ".join(rep))


if __name__ == "__main__":
    main()
