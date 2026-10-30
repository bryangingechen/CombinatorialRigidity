#!/usr/bin/env python3
"""NONDEG workbook S10: the candidates of brief section 3 at seeded configurations, d = 3, 4, 5.

    python3 notes/attacks/nondeg/drivers/nondeg.py --seed 1 [--dims 3 4 5] [--graphs NAME ...]
    python3 notes/attacks/nondeg/drivers/nondeg.py --steer --seed 1 [--dims 3 4 5] [--graphs ...]
    python3 notes/attacks/nondeg/drivers/nondeg.py --steer --pop d4 --seed 1   (strata's GRAPHS4)

For each graph G and dimension d it draws configurations in the polar form of
`lem:pencil-d-config-realization`: a planar picture q, heights z^1..z^(d-2) in the lifting
space L(q) (`strata.lifting_space`), points b_v = (q_v, z_v, 1) in K^(d+1), the plane Pi_v the span
of b on the closed neighbourhood N[v], and the hinge of uv the line b_u v b_v (its Lambda^2
vector; the rank is that of the polar body-hinge framework, which the polarity keeps).

Two pictures per cell:
  gen  -- every picture point drawn independently (a general picture);
  col  -- for every pair of hubs with three or more common neighbours, those neighbours' picture
          points are put on one line (the locus S5 says C2-same needs); otherwise as gen.

At each draw, in exact rational arithmetic, it reports which candidates hold (workbook S7's
definitions: N1, N3, H3 = every |H[v]| <= 3, C2-same, C2-gp; C1 = N1 & N3) and the rank
against the target D(n-1) - def_D(G).  The rank at one draw is a LOWER bound for the generic rank
on the family drawn; the target is an upper bound for every realization
(`lem:relative-deficiency-rank-bound`), so `rank == target` at a draw that satisfies a candidate is
an exact certificate of that candidate's generic conjunct at G (an exhibited realization), and
`rank < target` certifies nothing.

The S9 control (projection): at every draw satisfying C2-same in d >= 4, a seeded integer
4 x (d+1) matrix pi is applied to b and to every Pi_v, and C2-same is re-checked at d = 3 (S9 says
a general pi keeps it).  Exit status 1 if a C2-same draw fails the projected check at all of
PROJ_TRIES matrices, or if a draw's guards fail (adjacent picture points equal, a closed
neighbourhood not spanning a plane).

--steer (workbook S11): the polar form of `lem:pencil-generic-steer`'s parametrization at d = 3.
Each hub h gets a plane Pi_h = q_h^perp, q_h a random vector of K^4; each body v gets b_v, a
combination with nonzero coefficients of a basis of the meet of the planes of its closed
hub-neighbourhood H[v] (all of K^4 if H[v] is empty); a non-hub v gets Pi_v = span b(N[v]).  Then
b_w in Pi_h whenever h is a hub of N[w], so this is a pencil realization when N1 holds.  It is
written as a configuration over the picture q0_v = (x/w, y/w) with height z/w (guards: w != 0, the
height in L(q0)), and at each d the d - 2 heights are redrawn in L(q0): the rank of the family
{q0} x L(q0)^(d-2) at a draw, against the d-target, with the candidates checked at that draw.

Sampler support: picture coordinates are integers in [-COORD, COORD] (strata's Sampler), heights are
combinations of a basis of L(q) with every coefficient nonzero (`Sampler.comb`); the `col` picture
puts the forced points at q = A + t (B - A) for integers t.  The fenced constants are COORD
(strata), PROJ_TRIES, PROJ_COORD and MAX_N here (a graph on more than MAX_N bodies is listed
without a draw: the default mode needs its deficiency).
"""
import argparse
import os
import sys
from fractions import Fraction as F
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir, os.pardir, os.pardir, "scripts", "strata"))
import strata as st  # noqa: E402  -- read-only reuse

PROJ_TRIES = 3
PROJ_COORD = 50
MAX_N = 20   # the subset DP of `strata.deficiency` is 3^n; larger graphs are listed, not drawn


def graphs():
    th = lambda *ls: st.relabel(st.theta_edges(list(ls)))  # noqa: E731
    G = {"K4": st.complete(4), "K23": st.kbip(2, 3)}
    G.update({f"th222-{k}": th(2, 2, 2, k) for k in range(5, 11)})
    G.update({f"th22-{k}": th(2, 2, k) for k in (4, 7, 10)})
    G["Dwit"] = (7, [(i, (i + 1) % 6) for i in range(6)] + [(0, 3), (6, 1), (6, 4)])
    G["ring6"] = st.diamond_ring(6)
    return G


def population(name):
    """`brief`: the brief's section-3 graphs; `d4`: strata's GRAPHS4, simple graphs only."""
    if name == "d4":
        return {k: v for k, v in st.GRAPHS4.items() if st.simple(v[1])}
    return graphs()


def two_hub_triangle(n, edges):
    nb, hubs, _ = hub_sets(n, edges)
    return any(len({x, y, z} & hubs) >= 2 and y in nb[x] and z in nb[x] and z in nb[y]
               for x, y, z in combinations(range(n), 3))


def nbhd(n, edges):
    nb = {v: set() for v in range(n)}
    for u, v in edges:
        nb[u].add(v)
        nb[v].add(u)
    return nb


def hub_sets(n, edges):
    nb = nbhd(n, edges)
    hubs = {v for v in range(n) if len(nb[v]) >= 3}
    H = {v: sorted(w for w in nb[v] | {v} if w in hubs) for v in range(n)}
    return nb, hubs, H


def forced_lines(n, edges):
    """The sets of common neighbours of two hubs, when three or more (S5)."""
    nb, hubs, _ = hub_sets(n, edges)
    out = []
    for a, b in combinations(sorted(hubs), 2):
        c = sorted(nb[a] & nb[b])
        if len(c) >= 3:
            out.append(c)
    return out


def picture(s, n, edges, collinear):
    q = [(s.num(), s.num()) for _ in range(n)]
    if collinear:
        for c in forced_lines(n, edges):
            A, B = (s.num(), s.num()), (s.num(), s.num())
            for v in c:
                t = s.num()
                q[v] = (A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1]))
    return q


def perp(rows, m):
    return st.nullspace(rows) if rows else [[F(int(i == j)) for i in range(m)] for j in range(m)]


def meet_dim(planes, m):
    """dim of the meet of subspaces (given by spanning rows) of K^m: m - rank(sum of perps)."""
    comp = []
    for P in planes:
        comp += perp(P, m)
    return m - (st.rank(comp) if comp else 0)


def candidates(n, edges, b, Pi, m):
    nb, hubs, H = hub_sets(n, edges)
    d = m - 1
    n1 = all(st.rank([b[u], b[v]]) == 2 for u, v in edges)
    n3 = all(st.rank([b[w] for w in nb[v] | {v}]) == len(nb[v]) + 1
             for v in range(n) if v not in hubs)
    h3 = all(len(H[v]) <= 3 for v in range(n))
    same, gp = h3, h3
    for v in range(n):
        for j in (2, 3):
            for S in combinations(H[v], j):
                md = meet_dim([Pi[w] for w in S], m)
                same = same and md <= 4 - j
                gp = gp and md <= 1 + max(0, 2 * j - (j - 1) * d)
    return {"N1": n1, "N3": n3, "H3": h3, "C1": n1 and n3,
            "C2same": n1 and n3 and same, "C2gp": n1 and n3 and gp}


def draw(s, n, edges, d, collinear):
    q = picture(s, n, edges, collinear)
    for u, v in edges:
        st.need(q[u] != q[v], "picture: adjacent bodies coincide")
    L = st.lifting_space(n, edges, q)
    b, hinges = st.pd_pencil(s, n, edges, d, q, L)
    nb = nbhd(n, edges)
    Pi = {}
    for v in range(n):
        P = [b[w] for w in sorted(nb[v] | {v})]
        st.need(st.rank(P) == 3, f"closed neighbourhood of {v} spans {st.rank(P)}, not a plane")
        Pi[v] = P
    return q, L, b, Pi, hinges


def project(s, n, edges, b, Pi, m):
    R = s.R
    for _ in range(PROJ_TRIES):
        pi = [[F(R.randint(-PROJ_COORD, PROJ_COORD)) for _ in range(m)] for _ in range(4)]
        app = lambda x: [sum((r[i] * x[i] for i in range(m)), F(0)) for r in pi]  # noqa: E731
        pb = [app(x) for x in b]
        pP = {v: [app(x) for x in Pi[v]] for v in Pi}
        if all(st.rank(pP[v]) == 3 for v in pP) and candidates(n, edges, pb, pP, 4)["C2same"]:
            return True
    return False


def steer3(s, n, edges):
    nb, hubs, H = hub_sets(n, edges)
    qn = {h: s.vec(4) for h in hubs}
    b = []
    for v in range(n):
        Q = [qn[w] for w in H[v]]
        st.need(st.rank(Q) == len(Q) if Q else True, f"steer: hub normals dependent at {v}")
        basis = st.nullspace(Q) if Q else [[F(int(i == j)) for i in range(4)] for j in range(4)]
        b.append(s.comb(basis))
    for v in range(n):
        st.need(b[v][3] != 0, "steer: point at infinity")
    q0 = [(b[v][0] / b[v][3], b[v][1] / b[v][3]) for v in range(n)]
    z1 = [b[v][2] / b[v][3] for v in range(n)]
    return q0, z1


def steer_cell(s, n, edges, d, q0, z1):
    L = st.lifting_space(n, edges, q0)
    st.need(st.rank(L + [z1]) == st.rank(L), "steer: height not in L(q0)")
    if d == 3:
        b = [list(q0[v]) + [z1[v], F(1)] for v in range(n)]
        for u, v in edges:
            st.need(st.rank([b[u], b[v]]) == 2, "steer: adjacent points coincide")
        hinges = [st.ext([b[u], b[v]]) for u, v in edges]
    else:
        b, hinges = st.pd_pencil(s, n, edges, d, q0, L)
    nb = nbhd(n, edges)
    Pi = {}
    for v in range(n):
        P = [b[w] for w in sorted(nb[v] | {v})]
        st.need(st.rank(P) == 3, f"steer: closed neighbourhood of {v} spans {st.rank(P)}")
        Pi[v] = P
    return L, b, Pi, hinges


def main_steer(a, s):
    print(f"# nondeg.py --steer seed {a.seed}; COORD {st.COORD}")
    print("graph      d  dimL(q0)  C1 H3 C2same C2gp  rank/target")
    G = population(a.pop)
    for name in (a.graphs or list(G)):
        n, edges = G[name]
        _, _, H = hub_sets(n, edges)
        if any(len(H[v]) > 3 for v in range(n)):
            print(f"{name:10s} -  some |H[v]| > 3: infeasible (lem:pencil-feasible-hub-conditions)")
            continue
        if two_hub_triangle(n, edges):
            print(f"{name:10s} -  a triangle with two hubs: infeasible "
                  f"(lem:pencil-feasible-hub-conditions)")
            continue
        try:
            q0, z1 = steer3(s, n, edges)
            cells = [(d,) + steer_cell(s, n, edges, d, q0, z1) for d in a.dims]
        except st.Degenerate as ex:
            print(f"{name:10s} -  degenerate draw, no conclusion: {ex}")
            continue
        for d, L, b, Pi, hinges in cells:
            D = (d + 1) * d // 2
            target = D * (n - 1) - st.deficiency(n, edges, D)
            c = candidates(n, edges, b, Pi, d + 1)
            r = st.motion_rank(n, edges, hinges)
            st.need(r <= target, f"rank {r} above the deficiency rank {target}")
            yn = lambda t: "y" if t else "n"  # noqa: E731
            print(f"{name:10s} {d}  {len(L):8d}  {yn(c['C1']):2s} {yn(c['H3']):2s} "
                  f"{yn(c['C2same']):6s} {yn(c['C2gp']):4s}  "
                  f"{r:4d}/{target:<4d}{'=' if r == target else '<'}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--dims", type=int, nargs="+", default=[3, 4, 5])
    ap.add_argument("--graphs", nargs="*")
    ap.add_argument("--steer", action="store_true")
    ap.add_argument("--pop", choices=["brief", "d4"], default="brief")
    a = ap.parse_args()
    s = st.Sampler(a.seed)
    if a.steer:
        main_steer(a, s)
        return
    print(f"# nondeg.py seed {a.seed}; COORD {st.COORD}, PROJ_TRIES {PROJ_TRIES}, "
          f"PROJ_COORD {PROJ_COORD}")
    print("graph      d  pic  dimL  C1 H3 C2same C2gp  rank/target  proj")
    bad = 0
    G = graphs()
    for name in (a.graphs or list(G)):
        n, edges = G[name]
        if n > MAX_N:
            print(f"{name:10s} -  {n} bodies > MAX_N = {MAX_N}: not drawn", flush=True)
            continue
        for d in a.dims:
            D = (d + 1) * d // 2
            target = D * (n - 1) - st.deficiency(n, edges, D)
            for col in (False, True):
                if col and not forced_lines(n, edges):
                    continue
                q, L, b, Pi, hinges = draw(s, n, edges, d, col)
                c = candidates(n, edges, b, Pi, d + 1)
                r = st.motion_rank(n, edges, hinges)
                st.need(r <= target, f"rank {r} above the deficiency rank {target}")
                pr = "-"
                if c["C2same"] and d >= 4:
                    ok = project(s, n, edges, b, Pi, d + 1)
                    pr = "ok" if ok else "FAIL"
                    bad += not ok
                yn = lambda t: "y" if t else "n"  # noqa: E731
                print(f"{name:10s} {d}  {'col' if col else 'gen'}  {len(L):4d}  "
                      f"{yn(c['C1']):2s} {yn(c['H3']):2s} {yn(c['C2same']):6s} {yn(c['C2gp']):4s}  "
                      f"{r:4d}/{target:<4d}{'=' if r == target else '<'}  {pr}", flush=True)
    print(f"# projection failures: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
