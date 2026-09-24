#!/usr/bin/env python3
"""
coreshrink.py -- the contraction step on the main component X0 (W4 reopened,
P3; workbook §(K-main) Step MC12, claims (MC-34)-(MC-42)).

Setting.  `G` satisfies §(K-main)'s (H) and is 2-edge-connected; `W` is a
proper rigid vertex set (`2 <= |W| < |V|`, `def3(G[W]) = 0`,
`nogood_subdiv.rigid_vertex_sets`), `H = G[W]`, and `G/H` is
`nogood_subdiv.contraction(G, W)` (the core becomes `v*`).  A TWO-SCALE FAMILY
is a curve `p(t)` of pencil configurations of `G` whose core points converge to
one point `P` (the core "at scale t around P") while the rest converges to a
configuration of `G/H` with `v*` at `P`.  What the modes check:

  (MC-34) block identity, exact at every configuration: if `(H, p|W)` is
         infinitesimally rigid then
             rank R_G(p) = 6(|W| - 1) + rank R_{G/H}(L_p),
         `L_p` the ACTUAL hinge lines of `p` on the edges of `G/H`.  Asserted
         (on the mod-p ranks, where its field-free proof applies verbatim) at
         every sampled point with a rigid core.
  (MC-35) `def3(G) = def3(G/H)`, so the targets add.  Asserted per (G, W).
  (MC-36)/(MC-37) the limit: the boundary hinges tend to lines through `P`; the
         limit is pencil at every vertex of `G/H` except possibly `v*`
         (asserted); its heights range over `proj_z W0`, and whether that
         space contains `L0(G/H) := {z in L_{G/H}(q') : z_{v*} = 0}` (the
         containment the induction hypothesis needs) is reported as `L0in`.

Modes (exact arithmetic; seed 20260924; writes nothing):

    python3 notes/scripts/w4/coreshrink.py --family
    python3 notes/scripts/w4/coreshrink.py --collapse
    python3 notes/scripts/w4/coreshrink.py --pool NAME[,NAME] [--stride K] [--first N]
                                          [--draws D] [--verbose] [--classify]

`--family` is the recon's recipe (a scratch probe of the 2026-09-24 recon,
ported) on `W19 = family_g(4, (0,0,2), (4,4,4))` and `R20 = family_g(5, (0,0,2),
(4,4,4))`, core `C_m = {c0..c(m-1)}`.  The OUTSIDE is fixed, independent of
`t`, and every closed star of `G` holds exactly at every `t`: `P` is the
origin; each pole plane `pi_zi` contains `P`; `c0` (poles z0, z1) moves on the
line `pi_z0 & pi_z1`; `c0`'s two core neighbours lie in `plane(z0, z1, c0(t))`
within `O(t)` of `P`; `c2` (pole z2) is the foot of the perpendicular from `P`
on `pi_z2 & plane(c1(t), c3(t), z2)`; the other core vertices are
`P + t * (random)`.  Variant `relaxed`: `P, z0, z1, z2` in general position (the
limit is not pencil at `v*`); variant `pencil`: `z2 in plane(P, z0, z1)` (the
limit is a pencil configuration of `G/H`).  4 draws per variant, `t in {1/10,
1/100, 1/10^4, 1/10^8}`; per row it certifies `q(t) in U` (`dim L(q(t)) = 3 +
def2`) and reports the rank of `G`, of the core and of `G/H` with the actual
lines.  A draw failing `repin.star_generic` at `t = 1/10` is redrawn and
reported (the recon's scratch probe had no such guard; two of its draws carry a
coincident hinge at a pole).  Sampler support: pole points and the other
outside points uniform integers in `[-20, 20]^3`; each pole's path neighbours an
integer combination (`[-9, 9]`, zero replaced) of the pole and a random
direction; core offsets uniform in `[-9, 9]^3`; in-plane weights `k/1009`,
`k/1013`, `k` uniform in `[1, 997]`.  `P` and the frame are fenced constants
(the origin; the chart height is the third coordinate).

`--collapse` is the NEGATIVE CONTROL at a 2-cut: `theta(3,4,5)` (hubs 0, 1;
target 60) with its 5-edge path's interior collapsed to a point `Q` of
`M = pi_A & pi_B` (`POINT`: `x_i = Q + t d_i`, `d_17` in `pi_A`'s direction,
`d_20` in `pi_B`'s), against the corpus's slide-in (`SLIDE`, §(K-pitch) Step
6(b): `x_17 -> A` along its ray in `pi_A`, `x_20 -> B` in `pi_B`, the middle
points fixed).  Per family: the rank at `t = 1/10, 1/1000` (at certified points
of `B`); the LEADING-ORDER bound (the rank of the framework whose hinges are the
limit lines); the REFINED bound, with the collapsing path's span replaced by its
Grassmannian limit (valuation Gaussian elimination over Q[t]), via
`dim ker = sum(l_i - r_i) + dim(R1 & R2 & R3)`.  For `POINT` it also checks that
the refined span contains the alpha-plane `Lambda_Q` and equals `X^perp` (Klein
form) for a line `X` through `Q` that is not `M`.  3 draws; the recorded
figures (POINT 60 / 58 / 60, SLIDE 60 / 60 / 60) are compared and a move exits
1.  Sampler: `A, B`, the normals and free points uniform integers in
`[-20, 20]^3`, in-plane points `P0 + n x (random)`, `Q` on `M` shifted by an
integer multiple (`[-5, 5]`) of `M`'s direction.

`--pool` runs the GENERAL recipe (below) on every member of the named pools and
every MAXIMAL proper rigid `W` whose `G/H` is simple (a `W` with an outside
vertex joined to two core vertices -- a parallel class of `G/H` -- is counted
and skipped; `--verbose` lists it).  A member with no such maximal `W` but a
smaller rigid `W` with `G/H` simple is tried on those (relaxed only; the
"fallback").  Pools: `named` (W19, R20, and `K_{2,4}` = gate N3's instance
`C4 + x, y`), `exhN` (every simple 2EC graph on 3..N vertices,
`maincomp.two_ec_graphs`), and maincomp's `residuals`, `peels`, `smark`,
`thetas`, `battery`, plus `witnesses` (the last five of `residuals`).
`--stride K` keeps every K-th member, `--first N` the first N (both printed in
the summary line; README convention 8).  `--classify` skips the recipe and
prints only the per-pool classification (maximal / smaller-only / no rigid `W`
with `G/H` simple, and how many of each have `def2(G) = 0`, i.e. a flat X0).
A member with more than 22 branches (`rigid_vertex_sets`'s enumeration cap) is
skipped and counted.  `--pool exh8 --classify` is NOT in budget (~12 min to the
first capped member in one measurement); none of its figures is recorded.

The general recipe (a linear system, not a hand construction).  `P` is the
origin.  Draw the planar picture -- `q_u` for outside `u`, `delta_c` for core
`c`, uniform integers in `[-30, 30]`, redrawn until the collapsed picture of
`G/H` (`v*` at `(0, 0)`) and `q(1)` are admissible -- and set `q_c(t) = t
delta_c`.  Write core heights `z_c = t zeta_c` and, for every vertex `v` whose
closed star meets the core, the plane's constant term `gamma_v = t gamma~_v`.
The pencil conditions `z_w = alpha_v x_w + beta_v y_w + gamma_v` (`w in N[v]`)
become a HOMOGENEOUS linear system `M(t) = M0 + t M1` in `(z_O, zeta, alpha,
beta, gamma~)`, equivalent to `L(q(t))` for every `t != 0` (asserted:
`dim ker M(t) = dim L(q(t))`).  The family is `x(t)`, the unique solution with
`R x = b` (`R`, `b` uniform integers in `[-9, 9]`, fixed over `t`), so `p(t)` is
a random point of the fibre of `B` over `q(t)`.  Its limit is the point of
`W0 = lim ker M(t)` with `R x = b`; `W0` is exact, as the stable projection of
the jet spaces `{x0 : exists x1..xk, M0 x0 = 0, M0 x_(i+1) + M1 x_i = 0}`,
stopped at the first `k` with `dim = dim ker M(t)` (`k = 0`: no jump,
`W0 = ker M0`).  Asserted: `x(1/10^12)` is within `1e-6 (1 + |x(0)|)` of the
limit.  Variant `pencil` adds, for all `t`, the rows putting every attachment on
one plane through `P` (a sub-family: its points are not generic in `B`, but each
attaining row is still a certificate).  A draw failing `repin.star_generic` at a
sampled `t` is redrawn (counted; at most 5 in a row, else an assert).

Reported per `(G, W, variant)` at `t in {1/10, 1/10^4}`: `U` (certified when
`dim L(q(t)) = 3 + def2(G)`, (MC-4)(b)); the rank of `G` against
`6(|V|-1) - def3(G)`; the core's rank against `6(|W|-1)`; `G/H` with the actual
lines against its target.  At the limit: the rank of `G/H` at `L(0)`;
`pencil@v*`; `L0in`; `Uq` (`q'` in `U(G/H)`); `IH` (the rank of `G/H` at a random
point of `L_{G/H}(q')`: the induction hypothesis at `q'`); the rescaled core
`(delta_c, zeta_c(0))`, its rank (`core0`) and flatness (`flat0`); and `cfree`:
`proj_W L_G(q) = L_H(q|W)` at `q = q(1/10)`, certified only with `q in U(G)` and
`q|W in U(H)` -- hypothesis (i) of (MC-39); `jet = 0` is its hypothesis (ii).  A
run is `OK` iff at both `t` the core is rigid and `G` attains at a
certified-`U` point, and at the limit `G/H` attains and `L0in` holds; otherwise
the failing items are named, with the boundary pattern: `s` = the attachment
counts `|A_c|` over the core vertices (sorted), `pin` = core vertices with
`|A_c| >= 2`, `adj` = adjacent pinned pairs.  The summary tallies features over
runs (a pinned pair, a core vertex with >= 3 attachments, `def2(H) > 0`, a flat
or flexible limit core, (i), (ii)) and how many of those runs were OK.

Exactness.  Every linear-algebra step on the family is exact over Q.  Ranks of
rigidity matrices are mod the Mersenne prime 2^61 - 1 (`rank_modp`): a rank
equal to its target is a CERTIFICATE (rank_p <= rank_Q <= target); every
shortfall is recomputed in exact Q before it is reported, so a reported
shortfall is exact AT THAT POINT (and only a lower bound for the family's
generic rank).  A pool figure counts labelled (member, W) runs over the named
population and its caps; it is not a class statement.

Deterministic at `PYTHONHASHSEED=0` apart from the `-- pool ... built in N s`
timing lines.  Exit status 1 iff (`--family`/`--collapse`) a recorded figure
moves; any failed assert raises.
"""
import argparse
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact, rref, nullspace, wedge2, hat, neighbors, PL  # noqa: E402
from kbare_common import (rank_modp, build_rigidity, verts_of,  # noqa: E402
                          verify_pencil_witness, is_2ec)
from maincomp import def_k, lifting_space, two_ec_graphs  # noqa: E402
from nogood_subdiv import rigid_vertex_sets, contraction, is_simple, family_g  # noqa: E402
from repin import star_generic  # noqa: E402

SEED = 20260924


# ---------------------------------------------------------------- small vector helpers

def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def mul(s, a):
    return tuple(s * x for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def rv(rng, S=20):
    return tuple(F(rng.randint(-S, S)) for _ in range(3))


# ---------------------------------------------------------------- ranks

def targets(E):
    V = verts_of(E)
    return 6 * (len(V) - 1) - def_k(E, 6)


def rank_checked(rows, target):
    """mod-p rank; a shortfall is recomputed exactly.  Returns (rank_p, rank)."""
    rp = rank_modp(rows) if rows else 0
    if rp >= target:
        assert rp == target, ('rank above the partition bound', rp, target)
        return rp, rp
    return rp, (rank_exact(rows) if rows else 0)


def quotient_rows(E, W, pt):
    """R_{G/H} with the ACTUAL hinge lines of `pt`: the rows of G's edges not
    inside W, with the columns of W merged into one body v*."""
    Ws = set(W)
    Vq = [v for v in verts_of(E) if v not in Ws] + ['v*']
    idx = {v: k for k, v in enumerate(Vq)}
    rows = []
    for (u, w) in E:
        if u in Ws and w in Ws:
            continue
        C = wedge2(hat(pt[u]), hat(pt[w]))
        assert any(C), ('zero hinge', u, w)
        uu = 'v*' if u in Ws else u
        ww = 'v*' if w in Ws else w
        for wv in nullspace([C]):
            r = [F(0)] * (6 * len(Vq))
            for k in range(6):
                r[6 * idx[uu] + k] += wv[k]
                r[6 * idx[ww] + k] -= wv[k]
            rows.append(r)
    return rows


def admissible(E, q):
    nb = neighbors(E)
    if any(q[u] == q[w] for (u, w) in E):
        return False
    for v in verts_of(E):
        N = [v] + sorted(nb[v], key=str)
        if rank_exact([[F(1), q[w][0], q[w][1]] for w in N]) < 3:
            return False
    return True


def u_cert(E, pt, def2):
    """(admissible, dim L(q), q in U certified) for the chart picture of pt."""
    q = {v: (pt[v][0], pt[v][1]) for v in pt}
    if not admissible(E, q):
        return False, None, False
    dL = len(lifting_space(E, verts_of(E), q))
    return True, dL, dL == 3 + def2


def coplanar(pts):
    return rank_exact([hat(p) for p in pts]) <= 3


# ================================================================ --family (the recon's recipe)

def plane_normal(a, b, c):
    return cross(sub(b, a), sub(c, a))


def fam_outside(E, m, rng, variant):
    nb = neighbors(E)
    core = [f'c{i}' for i in range(m)]
    P = (F(0), F(0), F(0))
    pt = {}
    poles = ['z0', 'z1', 'z2']
    pt['z0'], pt['z1'] = rv(rng), rv(rng)
    if variant == 'pencil':
        a, b = F(rng.randint(1, 9)), F(rng.randint(1, 9))
        pt['z2'] = add(mul(a, pt['z0']), mul(b, pt['z1']))      # in plane(P, z0, z1)
    else:
        pt['z2'] = rv(rng)
    pole_normal = {}
    for z in poles:
        d = rv(rng)
        n = cross(pt[z], d)                                      # plane through P, z, d
        assert any(n), 'degenerate pole plane'
        pole_normal[z] = n
        for y in sorted(nb[z], key=str):
            if y in core:
                continue
            pt[y] = add(mul(F(rng.randint(-9, 9) or 1), pt[z]), mul(F(rng.randint(-9, 9) or 2), d))
    for v in verts_of(E):
        if v not in pt and v not in core:
            pt[v] = rv(rng)
    return P, pt, pole_normal


def fam_core(E, m, P, pt0, pole_normal, t, rng_state):
    """The core at scale t, every star exact; `rng_state` fixes the choices."""
    pt = dict(pt0)
    nb = neighbors(E)
    rs = random.Random(rng_state)
    n0, n1, n2 = pole_normal['z0'], pole_normal['z1'], pole_normal['z2']
    d0 = cross(n0, n1)                                           # pi_z0 & pi_z1, through P
    assert any(d0), 'pole planes parallel'
    c0 = add(P, mul(t, d0))
    pt['c0'] = c0
    for x in sorted(nb['c0'], key=str):
        if not x.startswith('c'):
            continue
        al, be = F(rs.randint(1, 997), 1009), F(rs.randint(1, 997), 1013)
        pt[x] = add(c0, mul(t, add(mul(al, sub(pt['z0'], c0)), mul(be, sub(pt['z1'], c0)))))
    for i in range(m):
        x = f'c{i}'
        if x not in pt and x != 'c2':
            pt[x] = add(P, mul(t, rv(rs, 9)))
    a, b = [x for x in sorted(nb['c2'], key=str) if x.startswith('c')]
    nplane = plane_normal(pt[a], pt[b], pt['z2'])
    dirl = cross(n2, nplane)
    z2 = pt['z2']
    assert dot(dirl, dirl) != 0, 'degenerate sampler draw (plane(a, b, z2) == pi_z2)'
    s = dot(sub(P, z2), dirl) / dot(dirl, dirl)
    pt['c2'] = add(z2, mul(s, dirl))
    return pt


def family():
    rng = random.Random(SEED)
    bad = 0
    rows_ok = rows_tot = redrawn = 0
    for (nm, m) in (('W19', 4), ('R20', 5)):
        E = family_g(m, (0, 0, 2), (4, 4, 4))
        V = verts_of(E)
        n = len(V)
        W = [f'c{i}' for i in range(m)]
        EH = [e for e in E if e[0] in W and e[1] in W]
        tgt = targets(E)
        d2 = def_k(E, 3)
        Eq = contraction(E, W)
        tq = targets(Eq)
        assert tgt == 6 * (m - 1) + tq, '(MC-35) targets do not add'
        print(f'== {nm}: n={n} |E|={len(E)} def3={def_k(E, 6)} def2={d2} target={tgt}; '
              f'core C{m} target {6 * (m - 1)}; G/H n={len(verts_of(Eq))} target={tq}')
        for variant in ('relaxed', 'pencil'):
            for draw in range(4):
                while True:
                    P, pt0, pn = fam_outside(E, m, rng, variant)
                    st = rng.randint(0, 10**9)
                    if star_generic(E, fam_core(E, m, P, pt0, pn, F(1, 10), st)):
                        break
                    redrawn += 1
                    print(f'  [{variant} draw {draw}] degenerate draw (repin.star_generic '
                          f'fails at t=1/10): redrawn')
                lim = {v: pt0[v] for v in pt0}
                lim['v*'] = P
                okL, _ = verify_pencil_witness(Eq, lim)
                rpL, rL = rank_checked(build_rigidity(Eq, lim)[0], tq)
                print(f'  [{variant} draw {draw}] limit G/H at t=0: rank {rL}/{tq}, '
                      f'pencil at v*: {okL}')
                bad += rL != tq
                for t in (F(1, 10), F(1, 100), F(1, 10**4), F(1, 10**8)):
                    pt = fam_core(E, m, P, pt0, pn, t, st)
                    ok, info = verify_pencil_witness(E, pt)
                    assert ok, info
                    assert star_generic(E, pt), 'degenerate draw (star_generic)'
                    adm, dL, inU = u_cert(E, pt, d2)
                    rpG, rG = rank_checked(build_rigidity(E, pt)[0], tgt)
                    rpH, rH = rank_checked(build_rigidity(EH, pt)[0], 6 * (m - 1))
                    rpQ, rQ = rank_checked(quotient_rows(E, W, pt), tq)
                    if rpH == 6 * (m - 1):
                        assert rpG == rpH + rpQ, '(MC-34) block identity fails'
                    good = rG == tgt and rH == 6 * (m - 1) and inU
                    rows_tot += 1
                    rows_ok += good
                    bad += not good
                    print(f'     t={str(t):>12s} admissible={adm} dimL={dL} U={inU} '
                          f'rank G={rG}/{tgt} core={rH}/{6 * (m - 1)} G/H(t)={rQ}/{tq} '
                          f'{"ATTAINS" if rG == tgt else "short"}')
    print(f'family: {rows_ok}/{rows_tot} (draw, t) rows attain at a certified-U point with the '
          f'core rigid; (MC-34) asserted at every row; {redrawn} degenerate draw(s) redrawn')
    return bad


# ================================================================ --collapse (negative control)

def klein(x, y):
    return x[0] * y[5] - x[1] * y[4] + x[2] * y[3] + x[3] * y[2] - x[4] * y[1] + x[5] * y[0]


def pv_point(c0, c1):
    """the homogeneous point c0 + t c1, as 4 polynomials {power: coeff}."""
    return [{0: F(c0[i]), 1: F(c1[i])} for i in range(3)] + [{0: F(1)}]


def pmul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] = out.get(i + j, 0) + x * y
    return {k: v for k, v in out.items() if v}


def psub(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) - v
    return {k: v for k, v in out.items() if v}


def pwedge(Pp, Qp):
    return [psub(pmul(Pp[i], Qp[j]), pmul(Pp[j], Qp[i])) for (i, j) in PL]


def order(b):
    ks = [k for c in b for k in c]
    return min(ks) if ks else None


def initial(b):
    v = order(b)
    return [c.get(v, F(0)) for c in b]


def shift(b, s, c):
    return [{k + s: c * x for k, x in co.items()} for co in b]


def padd(a, b):
    out = [dict(x) for x in a]
    for i, co in enumerate(b):
        for k, x in co.items():
            out[i][k] = out[i].get(k, 0) + x
    return [{k: x for k, x in co.items() if x} for co in out]


def initial_subspace(vecs):
    """The Grassmannian limit (t -> 0) of span(vecs), vecs over Q[t]."""
    B = [list(b) for b in vecs]
    for _ in range(200):
        ins = [initial(b) for b in B]
        ns = nullspace([list(col) for col in zip(*ins)])
        if not ns:
            return ins
        c = ns[0]
        supp = [i for i, x in enumerate(c) if x]
        vs = {i: order(B[i]) for i in supp}
        vmax = max(vs.values())
        j = next(i for i in supp if vs[i] == vmax)
        new = [dict() for _ in range(6)]
        for i in supp:
            new = padd(new, shift(B[i], vmax - vs[i], c[i]))
        assert order(new) is None or order(new) > vmax
        B[j] = new
    raise RuntimeError('no convergence')


def span_dim(vs):
    return rank_exact(vs) if vs else 0


def intersect(A, B):
    if not A or not B:
        return []
    M = [list(col) for col in zip(*(A + B))]
    ns = nullspace(M)
    out = [[sum(v[i] * A[i][k] for i in range(len(A))) for k in range(6)] for v in ns]
    return [o for o in out if any(o)]


def collapse():
    from pitch import theta_edges
    rng = random.Random(SEED)
    E = theta_edges([3, 4, 5])
    paths = [[0, 10, 11, 1], [0, 13, 14, 15, 1], [0, 17, 18, 19, 20, 1]]
    assert sorted(map(tuple, map(sorted, E))) == sorted(
        tuple(sorted((p[k], p[k + 1]))) for p in paths for k in range(len(p) - 1))
    tgt = targets(E)
    d2 = def_k(E, 3)
    assert tgt == 60 and d2 == 6
    bad = 0
    for draw in range(3):
        A, B = rv(rng), rv(rng)
        nA, nB = rv(rng), rv(rng)

        def in_plane(P0, n):
            return add(P0, cross(n, rv(rng)))
        base = {0: A, 1: B}
        for pth in paths:
            base[pth[1]] = in_plane(A, nA)
            base[pth[-2]] = in_plane(B, nB)
            for x in pth[2:-2]:
                base[x] = rv(rng)
        assert verify_pencil_witness(E, base)[0]
        r_base = rank_modp(build_rigidity(E, base)[0])
        dM = cross(nA, nB)
        assert any(dM)
        a11, a12, a22 = dot(nA, nA), dot(nA, nB), dot(nB, nB)
        b1, b2 = dot(nA, A), dot(nB, B)
        det = a11 * a22 - a12 * a12
        s, u = (b1 * a22 - b2 * a12) / det, (a11 * b2 - a12 * b1) / det
        Q = add(add(mul(s, nA), mul(u, nB)), mul(F(rng.randint(-5, 5)), dM))
        assert dot(nA, Q) == dot(nA, A) and dot(nB, Q) == dot(nB, B), 'Q not on M'
        fam = {}
        d = {17: cross(nA, rv(rng)), 20: cross(nB, rv(rng)), 18: rv(rng), 19: rv(rng)}
        fam['POINT'] = {x: (Q, d[x]) for x in (17, 18, 19, 20)}
        fam['SLIDE'] = {17: (A, sub(base[17], A)), 20: (B, sub(base[20], B)),
                        18: (base[18], (0, 0, 0)), 19: (base[19], (0, 0, 0))}
        print(f'== draw {draw}: generic base rank {r_base}/{tgt}')
        for nm, spec in fam.items():
            def at(t):
                pt = dict(base)
                for x, (c0, c1) in spec.items():
                    pt[x] = add(c0, mul(t, c1))
                return pt
            rts = []
            for t in (F(1, 10), F(1, 1000)):
                pt = at(t)
                ok, info = verify_pencil_witness(E, pt)
                assert ok, (nm, info)
                assert star_generic(E, pt), (nm, 'degenerate draw')
                adm, dL, inU = u_cert(E, pt, d2)
                assert adm and inU, (nm, 'not a certified point of B')
                rts.append(rank_checked(build_rigidity(E, pt)[0], tgt)[1])

            def pvec(x):
                if x in spec:
                    return pv_point(*spec[x])
                return pv_point(base[x], (0, 0, 0))
            Rpoly = [[pwedge(pvec(p[k]), pvec(p[k + 1])) for k in range(len(p) - 1)]
                     for p in paths]
            lim = [[initial(b) for b in R] for R in Rpoly]
            refined = [lim[0], lim[1], initial_subspace(Rpoly[2])]

            def bound(Rs):
                ls = [len(p) - 1 for p in paths]
                rs = [span_dim(R) for R in Rs]
                meet = intersect(intersect(Rs[0], Rs[1]), Rs[2])
                k = sum(l - r for l, r in zip(ls, rs)) + span_dim(meet)
                return 60 - k, rs, span_dim(meet)
            bc, rc, ic = bound(lim)
            br, rr, ir = bound(refined)
            print(f'  {nm:5s}: rank at t=1/10, 1/1000: {rts} (U certified); leading-order '
                  f'(limit lines) bound {bc} (path spans {rc}, triple meet {ic}); refined '
                  f'(Grassmannian limit of the path span) bound {br} (spans {rr}, meet {ir})')
            want = {'POINT': (60, 58, 60), 'SLIDE': (60, 60, 60)}[nm]
            got = (min(rts), bc, br)
            if got != want:
                bad += 1
                print(f'     MOVED: (rank, leading, refined) = {got}, recorded {want}')
            if nm == 'POINT':
                inR3 = refined[2]
                Qh = list(Q) + [F(1)]
                LamQ = [wedge2(Qh, e) for e in ([1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0])]
                cont = span_dim(inR3 + LamQ) == span_dim(inR3)
                Kmat = [[klein(v, [int(i == j) for j in range(6)]) for i in range(6)] for v in inR3]
                X = nullspace(Kmat)
                Xd = X[0] if len(X) == 1 else None
                dec = Xd is not None and klein(Xd, Xd) == 0
                thruQ = Xd is not None and span_dim(LamQ + [Xd]) == 3
                Mh = wedge2(Qh, list(dM) + [F(0)])
                isM = Xd is not None and span_dim([Xd, Mh]) == 1
                print(f'         in(R3) contains Lambda_Q: {cont}; '
                      f'in(R3) = X^perp, X a line: {dec}; '
                      f'X through Q: {thruQ}; X = M: {isM}')
                if not (cont and dec and thruQ and not isM):
                    bad += 1
                    print('     MOVED: the POINT refined-span structure')
    print(f'collapse: POINT leading-order bound 58 < family rank 60 at 3/3 draws (lossy); '
          f'SLIDE lossless; {"all recorded figures reproduced" if not bad else f"{bad} MOVED"}')
    return bad


# ================================================================ --pool (the general recipe)

def maximal_sets(rig):
    sets = [frozenset(W) for W in rig]
    return sorted((W for W in sets if not any(W < X for X in sets)),
                  key=lambda W: sorted(map(str, W)))


def boundary_pattern(E, W):
    Ws = set(W)
    nb = neighbors(E)
    s = {c: sum(1 for u in nb[c] if u not in Ws) for c in W}
    pin = sorted((c for c in W if s[c] >= 2), key=str)
    adj = sum(1 for (u, w) in E if u in pin and w in pin)
    prof = ''.join(str(x) for x in sorted(s.values(), reverse=True))
    return s, f's={prof} pin={len(pin)} adj={adj}'


def jets_limit(M0, M1, d):
    """W0 = lim_{t->0} ker(M0 + t M1), exactly, with the jet order used."""
    N = len(M0[0])
    K = nullspace(M0)
    if len(K) == d:
        return K, 0
    m = len(M0)
    for k in range(1, N + 1):
        big = []
        for i in range(k + 1):
            for r in range(m):
                row = [F(0)] * (N * (k + 1))
                row[i * N:(i + 1) * N] = M0[r]
                if i > 0:
                    row[(i - 1) * N:i * N] = M1[r]
                big.append(row)
        proj = [v[:N] for v in nullspace(big)]
        Rr, piv = rref(proj) if proj else ([], [])
        B = Rr[:len(piv)]                                   # a basis of span(proj)
        if len(B) == d:
            return B, k
        assert len(B) > d
    raise RuntimeError('jets did not stabilize')


def solve_pinned(M, R, b):
    N = len(M[0])
    aug = [row + [F(0)] for row in M] + [row + [bi] for row, bi in zip(R, b)]
    ns = nullspace(aug)
    sols = [v for v in ns if v[N] != 0]
    assert len(ns) == 1 and sols, 'pinned system not uniquely solvable'
    v = sols[0]
    return [x / -v[N] for x in v[:N]]


def draw_picture(E, W, rng, S):
    V = verts_of(E)
    Ws = set(W)
    O = [v for v in V if v not in Ws]
    Eq = contraction(E, W)
    for _ in range(500):
        q = {u: (F(rng.randint(-S, S)), F(rng.randint(-S, S))) for u in O}
        dl = {c: (F(rng.randint(-S, S)), F(rng.randint(-S, S))) for c in W}
        qq = dict(q)
        qq['v*'] = (F(0), F(0))
        if not admissible(Eq, qq):
            continue
        q1 = dict(q)
        q1.update(dl)
        if not admissible(E, q1):
            continue
        return q, dl
    raise RuntimeError('no admissible picture')


def recipe(E, W, rng, S, variant, ts):
    V = verts_of(E)
    Ws = set(W)
    O = [v for v in V if v not in Ws]
    nb = neighbors(E)
    near = {v for v in V if v in Ws or any(w in Ws for w in nb[v])}   # N[W]
    q, dl = draw_picture(E, W, rng, S)
    cols = [('z', u) for u in O] + [('zeta', c) for c in W]
    for v in V:
        cols += [('a', v), ('b', v), ('g', v)]
    if variant == 'pencil':
        cols += [('a', 'P'), ('b', 'P')]
    ci = {c: i for i, c in enumerate(cols)}
    N = len(cols)
    M0, M1 = [], []

    def row(d0, d1=None):
        r0 = [F(0)] * N
        r1 = [F(0)] * N
        for k, x in d0.items():
            r0[ci[k]] += x
        for k, x in (d1 or {}).items():
            r1[ci[k]] += x
        M0.append(r0)
        M1.append(r1)
    for v in V:
        for w in [v] + sorted(nb[v], key=str):
            if w in Ws:                               # then v in N[W]: rescaled
                row({('zeta', w): 1, ('a', v): -dl[w][0], ('b', v): -dl[w][1], ('g', v): -1})
            elif v in near:
                row({('z', w): 1, ('a', v): -q[w][0], ('b', v): -q[w][1]}, {('g', v): -1})
            else:
                row({('z', w): 1, ('a', v): -q[w][0], ('b', v): -q[w][1], ('g', v): -1})
    if variant == 'pencil':
        for u in O:
            if any(c in Ws for c in nb[u]):
                row({('z', u): 1, ('a', 'P'): -q[u][0], ('b', 'P'): -q[u][1]})

    def Mt(t):
        return [[a + t * b for a, b in zip(r0, r1)] for r0, r1 in zip(M0, M1)]
    dims = {t: N - rank_exact(Mt(t)) for t in ts}
    d = dims[ts[0]]
    assert all(x == d for x in dims.values()), ('dim ker M(t) not constant', dims)
    R = [[F(rng.randint(-9, 9)) for _ in range(N)] for _ in range(d)]
    b = [F(rng.randint(-9, 9)) for _ in range(d)]
    W0, jet = jets_limit(M0, M1, d)
    A = [[dot(Rr, w) for w in W0] for Rr in R]
    ns = nullspace([row_ + [-bi] for row_, bi in zip(A, b)])
    assert len(ns) == 1 and ns[0][-1] != 0, 'pinning not transverse to the limit space'
    cs = [x / ns[0][-1] for x in ns[0][:-1]]
    x0 = [sum(c * w[i] for c, w in zip(cs, W0)) for i in range(N)]
    xs = {t: solve_pinned(Mt(t), R, b) for t in ts}
    tc = F(1, 10**12)
    xc = solve_pinned(Mt(tc), R, b)
    scale = 1 + max(abs(x) for x in x0)
    assert max(abs(a - c) for a, c in zip(xc, x0)) <= F(1, 10**6) * scale, \
        'family does not converge to the computed limit'

    def config(x, t):
        pt = {u: (q[u][0], q[u][1], x[ci[('z', u)]]) for u in O}
        for c in W:
            pt[c] = (t * dl[c][0], t * dl[c][1], t * x[ci[('zeta', c)]])
        return pt
    out = {'d': d, 'dimK0': len(nullspace(M0)), 'jet': jet, 'q': q, 'dl': dl,
           'pts': {t: config(xs[t], t) for t in ts}}
    lim = {u: (q[u][0], q[u][1], x0[ci[('z', u)]]) for u in O}
    lim['v*'] = (F(0), F(0), F(0))
    out['lim'] = lim
    out['core0'] = {c: (dl[c][0], dl[c][1], x0[ci[('zeta', c)]]) for c in W}
    out['W0z'] = [[w[ci[('z', u)]] for u in O] for w in W0]
    return out


def run_member(name, E, W, rng, S, variant, ts, stats):
    V = verts_of(E)
    Ws = set(W)
    O = [v for v in V if v not in Ws]
    EH = [e for e in E if e[0] in Ws and e[1] in Ws]
    Eq = contraction(E, W)
    tgt, tq, tH = targets(E), targets(Eq), 6 * (len(W) - 1)
    assert tgt == tH + tq, '(MC-35) targets do not add'
    d2 = def_k(E, 3)
    _, pat = boundary_pattern(E, W)
    r = recipe(E, W, rng, S, variant, ts)
    if not all(star_generic(E, r['pts'][t]) for t in ts):
        return 'REDRAW', None, pat, None
    fails = []
    per_t = []
    for t in ts:
        pt = r['pts'][t]
        ok, info = verify_pencil_witness(E, pt)
        assert ok, ('not a pencil configuration', info)
        adm, dL, inU = u_cert(E, pt, d2)
        assert adm, 'q(t) not admissible'
        if variant == 'relaxed':
            assert dL == r['d'], ('dim ker M(t) != dim L(q(t))', dL, r['d'])
        else:
            assert dL >= r['d']
        rpG, rG = rank_checked(build_rigidity(E, pt)[0], tgt)
        rpH, rH = rank_checked(build_rigidity(EH, pt)[0], tH)
        rpQ, rQ = rank_checked(quotient_rows(E, W, pt), tq)
        if rpH == tH:
            assert rpG == rpH + rpQ, '(MC-34) block identity fails'
        resc = {c: (pt[c][0] / t, pt[c][1] / t, pt[c][2] / t) for c in W}
        assert rank_modp(build_rigidity(EH, resc)[0]) == rpH, 'rescaling changed the core rank'
        per_t.append(f'U={int(inU)} G={rG}/{tgt} core={rH}/{tH} G/H(t)={rQ}/{tq}')
        if not inU:
            fails.append('U-uncertified')
        if rH < tH:
            fails.append('core-flexible')
        if rG < tgt:
            fails.append('G-short')
    # core-free: does the boundary constrain the core's heights?  proj_W L_G(q) vs L_H(q|W)
    qt = {v: (r['pts'][ts[0]][v][0], r['pts'][ts[0]][v][1]) for v in V}
    LG = lifting_space(E, V, qt)
    VH = verts_of(EH)
    assert VH == sorted(W, key=str)
    LH = lifting_space(EH, VH, {c: qt[c] for c in VH})
    prW = rank_exact([[b[V.index(c)] for c in VH] for b in LG])
    uGH = len(LG) == 3 + d2 and len(LH) == 3 + def_k(EH, 3)     # q in U(G), q|W in U(H)
    cfree = prW == len(LH) and uGH
    # the limit
    lim = r['lim']
    Vq = verts_of(Eq)
    nbq = neighbors(Eq)
    for u in Vq:
        if u != 'v*':
            assert coplanar([lim[u]] + [lim[w] for w in nbq[u]]), ('limit not pencil at', u)
    pen = coplanar([lim['v*']] + [lim[w] for w in nbq['v*']])
    rpL, rL = rank_checked(build_rigidity(Eq, lim)[0], tq)
    if rL < tq:
        fails.append('limit-short')
    qq = {u: (lim[u][0], lim[u][1]) for u in Vq}
    Lq = lifting_space(Eq, Vq, qq)
    d2q = def_k(Eq, 3)
    inUq = len(Lq) == 3 + d2q
    iv = Vq.index('v*')
    L0 = nullspace(nullspace(Lq) + [[F(int(i == iv)) for i in range(len(Vq))]]) if Lq else []
    # L0: the z_{v*} = 0 slice of L_{G/H}(q'), as vectors over Vq
    Oq = [u for u in Vq if u != 'v*']
    oidx = [Vq.index(u) for u in Oq]
    L0O = [[v[i] for i in oidx] for v in L0]
    assert [str(u) for u in Oq] == [str(u) for u in O]
    rW = rank_exact(r['W0z']) if r['W0z'] else 0
    contains = rank_exact(r['W0z'] + L0O) == rW if L0O else True
    if not contains:
        fails.append('limit-misses-L0(G/H)')
    coef = [rng.randint(-9, 9) for _ in Lq]
    zq = [sum(c * v[i] for c, v in zip(coef, Lq)) for i in range(len(Vq))]
    ihpt = {u: (qq[u][0], qq[u][1], zq[i]) for i, u in enumerate(Vq)}
    assert verify_pencil_witness(Eq, ihpt)[0]
    rIH = rank_checked(build_rigidity(Eq, ihpt)[0], tq)[1]
    c0 = r['core0']
    rc0 = rank_checked(build_rigidity(EH, c0)[0], tH)[1]
    flat0 = coplanar(list(c0.values()))
    fails = sorted(set(fails))
    verdict = 'OK' if not fails else 'FAIL[' + ','.join(fails) + ']'
    key = (variant, verdict)
    stats[key] = stats.get(key, 0) + 1
    sv, _ = boundary_pattern(E, W)
    pins = {c for c in W if sv[c] >= 2}
    feats = {'adjacent pinned pair': any(u in pins and w in pins for (u, w) in E),
             'a core vertex with >= 3 attachments': max(sv.values()) >= 3,
             'def2(H) > 0': def_k(EH, 3) > 0,
             'limit core flexible': rc0 < tH,
             'limit core flat, def2(H) > 0': flat0 and def_k(EH, 3) > 0,
             'limit pencil at v*': pen,
             '(i) core-free, certified: proj_W L_G(q) = L_H(q|W), q in U(G), q|W in U(H)': cfree,
             '(ii) no jump: dim ker M0 = dim ker M(t)': r['jet'] == 0,
             '(i) and (ii): (MC-39) applies': cfree and r['jet'] == 0}
    line = (f'{name} W={"".join(sorted(map(str, W)))[:40]} |W|={len(W)} def2(H)={def_k(EH, 3)} '
            f'{pat} {variant}: d={r["d"]} dimK0={r["dimK0"]} jet={r["jet"]}; '
            + ' | '.join(per_t)
            + f' | limit G/H={rL}/{tq} pencil@v*={int(pen)} Uq={int(inUq)} '
            f'L0in={int(contains)} (dim {rW}>={len(L0O)}) IH={rIH}/{tq} '
            f'core0={rc0}/{tH} flat0={int(flat0)} cfree={int(cfree)} ({prW}/{len(LH)}) '
            f'-> {verdict}')
    return verdict, line, pat, feats


def pool_members(name, first, stride):
    import maincomp
    if name == 'witnesses':
        return maincomp.residuals()[-5:]
    if name == 'named':
        from widened import W19
        from rpool import R20
        K24 = [(a, b) for a in (1, 3) for b in (2, 4, 'x', 'y')]
        return [('W19', W19()), ('R20', R20()), ('K24', K24)]
    if name.startswith('exh'):
        out = two_ec_graphs(int(name[3:]))
    elif name in ('residuals', 'peels', 'smark', 'thetas', 'battery'):
        out = maincomp.POOLS[name]()
    else:
        raise SystemExit(f'unknown pool {name}')
    out = out[::stride] if stride > 1 else out
    return out[:first] if first else out


def pool(names, first, stride, draws, verbose, classify_only=False):
    S = 30
    ts = (F(1, 10), F(1, 10**4))
    bad = 0
    for pname in names:
        t0 = time.time()
        rng = random.Random(f'{SEED}:{pname}')
        stats = {}
        members = pool_members(pname, first, stride)
        nmem = nrig = nsimple = nany = nnotsimple = redrawn = 0
        cls = {'maximal': [0, 0], 'smaller only': [0, 0], 'none': [0, 0]}   # [members, flat X0]
        fb_fail = []
        capped = []
        some_ok = {'relaxed': 0, 'pencil': 0, 'fallback': 0}
        none_ok = []
        pats_fail = {}
        feat = {}

        def attempt(mname, E, Ws, variant):
            nonlocal redrawn
            for dr in range(draws):
                for _ in range(5):
                    verdict, line, pat, fs = run_member(mname, E, Ws, rng, S, variant, ts, stats)
                    if verdict != 'REDRAW':
                        break
                    redrawn += 1
                assert verdict != 'REDRAW', ('5 degenerate draws in a row', mname)
                for k, v in fs.items():
                    c = feat.setdefault((variant, k), [0, 0])
                    c[0] += v
                    c[1] += v and verdict == 'OK'
                if verdict == 'OK':
                    if verbose:
                        print(line)
                    return True
                print(line)
                pats_fail.setdefault((variant, verdict, pat), []).append(mname)
            return False
        for mname, E in members:
            if not (is_simple(E) and is_2ec(E)):
                continue
            nmem += 1
            try:
                rig = rigid_vertex_sets(E)
            except AssertionError:                    # its > 22-branch enumeration cap
                capped.append(mname)
                continue
            if not rig:
                continue
            nrig += 1
            mx = maximal_sets(rig)
            simple = [W for W in mx if is_simple(contraction(E, sorted(W, key=str)))]
            nnotsimple += len(mx) - len(simple)
            anyW = sorted((frozenset(W) for W in rig
                           if is_simple(contraction(E, sorted(W, key=str)))),
                          key=lambda W: (-len(W), sorted(map(str, W))))
            nany += bool(anyW)
            c = cls['maximal' if simple else 'smaller only' if anyW else 'none']
            c[0] += 1
            c[1] += def_k(E, 3) == 0
            for W in mx:
                if W not in simple and verbose:
                    _, pat = boundary_pattern(E, W)
                    print(f'{mname} W={"".join(sorted(map(str, W)))[:40]} {pat}: NOT-SIMPLE '
                          f'(an outside vertex with two core neighbours)')
            if classify_only:
                continue
            if not simple:
                # KT 2011 Lemma 6.5's case for maximal sets; try a smaller rigid W (relaxed)
                for W in anyW:
                    if attempt(mname, E, sorted(W, key=str), 'relaxed'):
                        some_ok['fallback'] += 1
                        break
                else:
                    if anyW:
                        fb_fail.append(f'{mname}(def2={def_k(E, 3)})')
                continue
            nsimple += 1
            for variant in ('relaxed', 'pencil'):
                anyok = False
                for W in simple:
                    anyok |= attempt(mname, E, sorted(W, key=str), variant)
                some_ok[variant] += anyok
                if not anyok and variant == 'relaxed':
                    none_ok.append(mname)
        cap = (f' [every {stride}th member]' if stride > 1 else '') + \
            (f' [first {first}]' if first else '')
        print(f'-- pool {pname}{cap}: {nmem} simple 2EC members, {nrig} with a proper rigid set, '
              f'{nsimple} with a MAXIMAL one whose G/H is simple ({nnotsimple} maximal sets with '
              f'G/H not simple); {nany} with SOME rigid W whose G/H is simple')
        for variant in ('relaxed', 'pencil'):
            row = ', '.join(f'{v}: {c}' for (vv, v), c in sorted(stats.items()) if vv == variant)
            print(f'   {variant}: (member, W) verdicts {row}; members with some maximal W OK: '
                  f'{some_ok[variant]}/{nsimple}')
            for (vv, k), (c, cok) in sorted(feat.items()):
                if vv == variant and c:
                    print(f'      feature "{k}": {c} runs, {cok} of them OK')
        for k, (c, cf) in cls.items():
            print(f'   members with a proper rigid set whose simple-quotient rigid W is {k}: {c} '
                  f'({cf} of them with def2(G) = 0, i.e. X0 flat: they attain by (MC-5)(iii))')
        print(f'   fallback (no maximal W with G/H simple; a smaller rigid W, relaxed): OK at '
              f'{some_ok["fallback"]}/{nany - nsimple} members'
              + (f'; no W works at {", ".join(fb_fail)}' if fb_fail else ''))
        for (variant, verdict, pat), ms in sorted(pats_fail.items()):
            print(f'   failing pattern [{variant}] {verdict} {pat}: {len(ms)} ({", ".join(ms[:6])}'
                  f'{", ..." if len(ms) > 6 else ""})')
        print(f'   degenerate draws (repin.star_generic fails at a sampled t) redrawn: {redrawn}')
        if capped:
            print(f'   skipped, rigid_vertex_sets branch cap (> 22 branches): {len(capped)}')
        print(f'   members with a maximal simple-quotient W where NO maximal W is OK (relaxed): '
              f'{len(none_ok)}' + (f' ({", ".join(none_ok[:10])})' if none_ok else ''))
        print(f'-- pool {pname}: built in {time.time() - t0:.0f} s')
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--family', action='store_true')
    ap.add_argument('--collapse', action='store_true')
    ap.add_argument('--pool', type=str, default='')
    ap.add_argument('--first', type=int, default=0)
    ap.add_argument('--stride', type=int, default=1)
    ap.add_argument('--draws', type=int, default=1)
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--classify', action='store_true')
    a = ap.parse_args()
    print(f'coreshrink.py seed {SEED}')
    bad = 0
    if a.family:
        bad += family()
    if a.collapse:
        bad += collapse()
    if a.pool:
        bad += pool(a.pool.split(','), a.first, a.stride, a.draws, a.verbose, a.classify)
    if not (a.family or a.collapse or a.pool):
        ap.error('name a mode')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
