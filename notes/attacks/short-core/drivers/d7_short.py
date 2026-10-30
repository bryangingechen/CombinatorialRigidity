#!/usr/bin/env python3
"""SHORT-CORE workbook S42: the k = 3 danger cells past T3's dimensions, measured exactly.

    python3 notes/attacks/short-core/drivers/d7_short.py --seed 1 [--d 7] [--per 3] [--tries 3000]
        [--nmax 80] [--fams th3,th4,k4,same,hub,neck]

Population.  strata.py's --short families (`SHORT_FAMS`: th3 a cycle, th4 a theta with hubs a, b,
k4 / same / hub thetas with a, b inside paths, neck a necklace of diamonds), at k = 3 only, at
dimension d (default 7, D = 28).  The cells are `strata.short_danger`'s own box search, seeded by
(family, d, k) alone, so the same at every --seed, with three of its caps raised from the module's
values: SHORT_NMAX = --nmax bodies of G (strata: 40), SHORT_TRIES = --tries box draws (400),
SHORT_PER = --per cells per family (2).  A danger cell is short_danger's: def_3(G) >= d - 2,
f = def_D(G[V1]) > def_D(G) = def_D(G''), 2d - 1 <= 3 + f - def_D(G'') <= D - 1.  Each family's
box (core lengths in [1, D + top], necklaces of 3-6 diamonds with paths of 1-7 edges) is
short_draw's, unchanged.  With --neck-lmax N > 0 the run is the necklace family alone, its paths
widened to 1..N edges (`neck_danger`, short_danger's filter verbatim, seeded by (d, k, N)): the
diamonds K_4 - e are P^2-rigid, so there Case 2's parts (S40) are not all single bodies.

Per cell, `cell` replays `strata.short_cell` call for call (same sampler draws, in order; checked
against short_cell itself from a copy of the sampler), then adds, with no further draws before
short_cell's last:
  kap   dim(Pi_a cap Pi_b), Pi_a, Pi_b the planes of a, b in G'';
  r     dim rho^(2), the P^2 relative motions of a, b in G[V1] (hinges q^_u ^ q^_v);
  hv    dim(rho + H^V) - dim(H^V), H = Pi_a + Pi_b: the dimension of rho's image in
        Lambda^2(V/H), whose full value C(d - 5 + kap, 2) makes SHORT-CORE hold (S34);
  rH    1 if (rho cap H^V) + Lambda^2 H = H^V, S36 (i)'s necessary condition for failure;
  L     dim L_G(q) - (3 + def_3(G)) at the picture q of the configuration of G that shG reads
        (x_1, x_2, x_3 at their own picture points): 0 means q is generic for the lifting space,
        since dim L_G(q) is a kernel dimension, upper semicontinuous on the admissible pictures,
        with generic value 3 + def_3(G) (thm:pencil-jj-equality);
  X     W holds both stars and W != Lambda^2: SHORT-CORE fails at the draw;
  shG   G's target D(n - 1) - def_D(G) minus its rank at the draw (x_2 a general affine point).
        shG = 0 with L = 0 certifies SHORT-CORE at the cell (S41 (b)): the picture is then a main
        picture (def:pencil-main-picture: admissible -- `lifting_space` guards the closed
        neighbourhoods, `cell` the adjacent pairs -- with dim L least), so the general
        configuration of G attains by lem:pencil-d-x0-one-witness (`Graph.x0AttainsGrade_of_exists`),
        and S41 excludes a failure at the cell.
Asserted at every cell (exit 1 otherwise): the replay matches short_cell; the ear rank formula at
G'' and at G (lem:block-rank-ear, as mode_short asserts it); every rank at most its count; dim W =
3 + f - def_D(G'') where G[V1] and G'' are at target; the stars' control.  Reported, and counted in
the closing tally: r = 3 and kap = 0 (S31, S33 at general base data), X, shG = 0, hv, rH.
Each cell is one seeded draw: every rank is a lower bound for its generic value at the cell, so a
cell at target is certified there, and a cell below target is not a proof of anything.
"""
import argparse
import copy
import os
import sys
from fractions import Fraction as F
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir, os.pardir, os.pardir, "scripts", "strata"))
import strata as st  # noqa: E402  -- read-only reuse; it bootstraps the harness path itself
from exactcore import rank  # noqa: E402


def cell(s, spec, d):
    """`strata.short_cell`, replayed, with the extras of the docstring."""
    D, k = (d + 1) * d // 2, spec.k
    n, E, paths, blocks, a, b = spec.graph(k)
    n2, E2, paths2, blocks2, _, _ = spec.graph(k - 1)
    n1, E1, paths1, blocks1 = spec.base()
    dG, d2 = st.def_certified(s, n, E, paths, D, blocks), st.def_certified(s, n2, E2, paths2, D, blocks2)
    f, d3 = st.def_certified(s, n1, E1, paths1, D, blocks1), st.def_certified(s, n, E, paths, 3, blocks)
    q2 = [s.vec(2) for _ in range(n2)]
    L2 = st.lifting_space(n2, E2, q2)
    b2, H2 = st.pd_pencil(s, n2, E2, d, q2, L2)
    st.body_guard(n2, E2, H2)
    base = b2[:n1]
    H1 = [st.ext([base[u], base[v]]) for u, v in E1]
    r1 = st.motion_rank(n1, E1, H1)
    PA, PB = st.plane_of(b2, E2, a), st.plane_of(b2, E2, b)
    st.need(len(PA) == 3 and len(PB) == 3, "the planes of a, b in G''")
    rho = st.rel_screws(n1, E1, H1, a, b)
    y = {1: st.point_over(PA, s.vec(2)), k: st.point_over(PB, s.vec(2))}
    for i in range(3, k):
        y[i] = st.affine_pt(s, d)
    ear2 = [base[a], y[1]] + [y[i] for i in range(3, k + 1)] + [base[b]]
    J2 = [st.ext([p, p2]) for p, p2 in zip(ear2, ear2[1:])]
    W = rho + J2
    dW = rank(W)
    pts2 = base + ear2[1:-1]
    r2 = st.motion_rank(n2, E2, [st.ext([pts2[u], pts2[v]]) for u, v in E2])
    holds = lambda U, V: rank(U + V) == rank(U)  # noqa: E731
    in1, in3 = holds(W, st.star(y[1])), holds(W, st.star(y[3]))
    caps = []
    for yi, R in ((y[1], rho + J2[2:]), (y[3], rho + J2[:1] + J2[3:])):
        caps.append((rank(R) + d - rank(R + st.star(yi)), max(0, rank(R) + d - D)))
    stars = st.star(y[1]) + st.star(y[3])
    ctrl = holds(stars, st.star(y[1])) and holds(stars, st.star(y[3])) and rank(stars) == 2 * d - 1
    img = [rank(stars + U) - rank(stars) for U in (rho, J2[3:], W)]
    ear = [base[a], y[1], st.affine_pt(s, d)] + ear2[2:]
    dI = rank(rho + [st.ext([p, p2]) for p, p2 in zip(ear, ear[1:])])
    pts = base + ear[1:-1]
    rG = st.motion_rank(n, E, [st.ext([pts[u], pts[v]]) for u, v in E])
    gen = ([base[a], st.point_over(PA, s.vec(2))] + [st.affine_pt(s, d) for _ in range(k - 2)]
           + [st.point_over(PB, s.vec(2)), base[b]])
    dGen = rank(rho + [st.ext([p, p2]) for p, p2 in zip(gen, gen[1:])])
    out = dict(D=D, k=k, n=n, d3=d3, dG=dG, d2=d2, f=f, r1=r1, t1=D * (n1 - 1) - f,
               r2=r2, t2=D * (n2 - 1) - d2, rG=rG, tG=D * (n - 1) - dG, dW=dW,
               rho=len(rho), in1=in1, in3=in3, caps=caps, ctrl=ctrl, img=img, dI=dI, dGen=dGen,
               need=k + 1 + f - dG)
    # ---- the extras: no sampler draws below this line ----
    H = PA + PB
    out["kap"] = 6 - rank(H)
    unit = [[F(int(i == j)) for j in range(d + 1)] for i in range(d + 1)]
    HV = [st.ext([h, e]) for h in H for e in unit]
    rHV = rank(HV)
    out["hv"] = rank(HV + rho) - rHV
    L2H = [st.ext([h, h2]) for h, h2 in combinations(H, 2)]
    rhoH = st.span_cap(rho, HV) if rho else []
    out["rH"] = rank(rhoH + L2H) == rHV
    qh = [[p[0], p[1], p[-1]] for p in base]
    out["r"] = len(st.rel_screws(n1, E1, [st.ext([qh[u], qh[v]]) for u, v in E1], a, b))
    # the lifting space at the picture of the configuration of G whose rank is rG (x_1, x_2, x_3
    # at the picture points of y_1, the general point, y_3): S41 (b) asks it generic there
    qG = [[p[0], p[1]] for p in pts]
    st.need(all(qG[u] != qG[v] for u, v in E), "G's picture: adjacent bodies coincide")
    out["L"] = len(st.lifting_space(n, E, qG)) - (3 + d3)
    return out


def neck_danger(d, k, lmax, per, tries, nmax):
    """`strata.short_danger` for the necklace family with its path box widened from 1-7 edges to
    1-lmax: the same filter, line for line, over necklaces of 3-6 diamonds (K_4 - e, P^2-rigid, so
    Case 2's parts are not all single bodies), seeded by (d, k, lmax) alone."""
    D = (d + 1) * d // 2
    R = st.random.Random(7000000 + 10000 * lmax + 100 * d + k)
    found, seen = [], set()
    for _ in range(tries):
        r = R.randint(3, 6)
        spec = st.NecklaceEar([R.randint(1, lmax) for _ in range(r)], R.randint(1, r - 1),
                              R.choice("tuvw"), R.choice("tuvw"), k)
        if spec.key in seen:
            continue
        seen.add(spec.key)
        n, E, paths, blocks, _, _ = spec.graph(k)
        if n > nmax or st.path_partitions_def(n, E, paths, 3, blocks) < d - 2:
            continue
        dG = st.path_partitions_def(n, E, paths, D, blocks)
        n1, E1, paths1, blocks1 = spec.base()
        f = st.path_partitions_def(n1, E1, paths1, D, blocks1)
        n2, E2, paths2, blocks2, _, _ = spec.graph(k - 1)
        d2 = st.path_partitions_def(n2, E2, paths2, D, blocks2)
        if f > dG == d2 and 2 * d - 1 <= k + f - d2 <= D - 1:
            found.append(spec)
            if len(found) == per:
                break
    return found


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--d", type=int, default=7)
    ap.add_argument("--per", type=int, default=3)
    ap.add_argument("--tries", type=int, default=3000)
    ap.add_argument("--nmax", type=int, default=80)
    ap.add_argument("--fams", default=",".join(st.SHORT_FAMS))
    ap.add_argument("--neck-lmax", type=int, default=0,
                    help="if > 0, the necklace family only, paths of 1..N edges (`neck_danger`)")
    args = ap.parse_args()
    st.SHORT_NMAX, st.SHORT_TRIES, st.SHORT_PER = args.nmax, args.tries, args.per
    d, k = args.d, 3
    D = (d + 1) * d // 2
    print(f"d7_short.py --seed {args.seed} --d {d} --per {args.per} --tries {args.tries} "
          f"--nmax {args.nmax} --fams {args.fams} --neck-lmax {args.neck_lmax}   (D = {D}, k = 3; full hv = C(d-5+kap, 2))")
    print(f"{'fam':5}{'lengths':20}{'n':>4}{'d3':>4}{'f':>4}{'dG':>4}{'dG2':>4}{'sh1':>4}{'sh2':>4}"
          f"{'W':>4}{'rho':>4}{'st':>4}{'kap':>4}{'r':>3}{'hv':>4}{'rH':>3}{'L':>3}{'need':>5}"
          f"{'step':>5}{'shG':>4}")
    s = st.Sampler(args.seed)
    bad, tally = 0, dict(cells=0, X=0, certified=0, kap0=0, r3=0, hv_full=0, rH=0, rho_ge=0)
    fams = ["neck"] if args.neck_lmax else args.fams.split(",")
    for fam in fams:
        specs = (neck_danger(d, k, args.neck_lmax, args.per, args.tries, args.nmax) if args.neck_lmax
                 else st.short_danger(fam, d, k))
        for spec in specs:
            for draws in range(st.SHORT_REDRAWS + 1):
                try:
                    s0 = copy.deepcopy(s)
                    c = cell(s, spec, d)
                    ref = st.short_cell(s0, spec, d)
                    break
                except st.Degenerate as e:
                    err = e
            else:
                bad += 1
                print(f"{fam:5}{spec.label():20} degenerate: {err}")
                continue
            bad += any(c[x] != ref[x] for x in ref)
            sh1, sh2, shG = c["t1"] - c["r1"], c["t2"] - c["r2"], c["tG"] - c["rG"]
            bad += min(sh1, sh2, shG) < 0
            bad += c["r2"] != c["r1"] + (D - 1) * (k - 1) + c["dW"] - 1
            bad += c["rG"] != c["r1"] + (D - 1) * k + c["dI"] - 1
            bad += sh1 == sh2 == 0 and c["dW"] != k + c["f"] - c["d2"]
            bad += not c["ctrl"]
            x3 = c["in1"] and c["in3"] and c["dW"] < D
            full = (d - 5 + c["kap"]) * (d - 6 + c["kap"]) // 2
            tally["cells"] += 1
            tally["X"] += x3
            tally["certified"] += shG == 0 and c["L"] == 0
            tally["kap0"] += c["kap"] == 0
            tally["r3"] += c["r"] == 3
            tally["hv_full"] += c["hv"] == full
            tally["rH"] += c["rH"]
            tally["rho_ge"] += c["rho"] >= 6 * (d - 5)
            print(f"{fam:5}{spec.label():20}{c['n']:>4}{c['d3']:>4}{c['f']:>4}{c['dG']:>4}{c['d2']:>4}"
                  f"{sh1:>4}{sh2:>4}{c['dW']:>4}{c['rho']:>4}{int(c['in1']):>3}{int(c['in3'])}"
                  f"{c['kap']:>4}{c['r']:>3}{c['hv']:>4}{int(c['rH']):>3}{c['L']:>3}{c['need']:>5}"
                  f"{c['dI']:>5}{shG:>4} " + ("X" if x3 else "") + "~" * draws, flush=True)
    print("tally: " + ", ".join(f"{key} {v}" for key, v in tally.items())
          + f"  (rho_ge: dim rho >= 6(d-5) = {6 * (d - 5)}, S36's bound for failure)")
    print(f"mismatches (asserted): {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
