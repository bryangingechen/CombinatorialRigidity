"""Phase 39 kernel-(K): the projective polarity `sigma` as a symmetry of the
split, and **route sigma** -- route A run at the dual seed `sigma u`.

Workbook: `notes/Pencil-informal.md` §(K-sigma).  Exact Q throughout; every
sampled placement is star-rank guarded and every span's dimension asserted.
`sigma` is `screwComplementIso` (`Molecular/Molecule/Duality.lean:69`), which
`Meet.lean`'s header records as the Hodge star of the standard dot product;
on a pencil realization it replaces every body's point by that body's own
panel normal (`repin.hodge_star` is the coordinate form).

The whole file works with HOMOGENEOUS data: a body carries a point `P[w]` and
a panel normal `N[w]` in `Q^4` with `P[w] . N[w] = 0`, and the seed `sigma u`
is literally `(points, normals) := (N, P)`.  That is why the affine samplers'
`(placed, nrm)` pair is homogenized once, in `hard_stratum_seed`, and never
used again.

Modes (all four run on one pinned seed pool; see SEED POOL below):

    python3 notes/scripts/w4/sigma.py --transport   # (sigma1)-(sigma6), V0-V5
    python3 notes/scripts/w4/sigma.py --adv         # the adversarial half
    python3 notes/scripts/w4/sigma.py --nondeg      # nondegeneracy at sigma u
    python3 notes/scripts/w4/sigma.py --fixed       # sigma-FIXED is degenerate

SEED POOL.  Two splits of the tight control (the double-subdivided `K4`,
`|V| = 16`, target 90, `G'` target 84): seeds 440-479 at chain 0 and 500-529 at
chain 1.  A seed is *valid* when its draw survives the guards AND lands on the
hard stratum (`s0 = 0`, `dim R_a = 1`); 34 + 29 = 63 of the 70 do.  Every
figure the workbook quotes is over that pool.  `--adv` additionally probes two
`W19` splits (the (K-res) residual habitat), which yield **no** valid
hard-stratum seed in the probed range -- recorded as *unsampled*, never as
*tested and passed*.
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (dot, hat, left_nullspace, neighbors,  # noqa: E402
                       nullspace, rank, wedge2)
from pencil_escape import double_subdivide, rquat                # noqa: E402
from kbare_common import verts_of                                # noqa: E402
from nogood_subdiv import deficiency, hub_set                    # noqa: E402
from widened import W19, orient, place_pencil_general, splitOff  # noqa: E402
from repin import hodge_star, lambda2_through, span_basis        # noqa: E402
from flanks import star_span_ranks                               # noqa: E402
from hybrid_gates import build_rigidity_extensors                # noqa: E402

CHAIN0_SEEDS = range(440, 480)
CHAIN1_SEEDS = range(500, 530)
W19_SEEDS = range(600, 620)
SWEEP_TRIES = 14          # route-A placement draws at sigma u, per seed

# the standard symplectic form on K^4 (the null correlation of --fixed)
J = [[F(0), F(1), F(0), F(0)],
     [F(-1), F(0), F(0), F(0)],
     [F(0), F(0), F(0), F(1)],
     [F(0), F(0), F(-1), F(0)]]


# ---------------- small wrappers (not new primitives) ------------------------

def prop(x, y):
    """`x`, `y` nonzero and projectively equal.  A wrapper on
    `exactcore.rank`, not a new primitive."""
    return (any(t != 0 for t in x) and any(t != 0 for t in y)
            and rank([x, y]) == 1)


def null4(vs):
    """The unique-up-to-scale nonzero 4-vector annihilating every row of `vs`,
    or `None` when that annihilator is not 1-dimensional.  A uniqueness
    wrapper on `exactcore.nullspace`."""
    ns = nullspace(vs)
    return ns[0] if len(ns) == 1 else None


def lambda2_perp(nu):
    """Basis of `Lambda^2 {y : y . nu = 0}` (3-dim) from a HOMOGENEOUS normal
    `nu` -- the `beta` isotropic of the plane `nu^perp`.

    Divergence candidate against `repin.lambda2_plane`, which builds the same
    space from an AFFINE hub point + 3-normal and consumes rng; see
    `notes/scripts/README.md` *Divergences*.  Do not merge them."""
    bs = nullspace([nu])
    assert len(bs) == 3, "a panel normal must be a nonzero 4-covector"
    out = span_basis([wedge2(bs[i], bs[j])
                      for i in range(3) for j in range(i + 1, 3)])
    assert len(out) == 3, "Lambda^2 of a plane is 3-dimensional"
    return out


def rows_from_points(edges, V, P):
    """`(rows, er, C, idx)` for the body-hinge rigidity matrix at HOMOGENEOUS
    points `P`, hinge extensors `C_e = P_u ^ P_w`.  The row bodies come from
    `hybrid_gates.build_rigidity_extensors` (the §1 primitive); this wrapper
    only adds the per-edge row-index map and the extensor map that
    `load_span` needs."""
    C = {e: wedge2(P[e[0]], P[e[1]]) for e in edges}
    rows = build_rigidity_extensors(V, [(e, C[e]) for e in edges])
    idx = {w: k for k, w in enumerate(V)}
    er = {e: list(range(5 * i, 5 * i + 5)) for i, e in enumerate(edges)}
    assert len(rows) == 5 * len(edges), "5 rows per hinge"
    return rows, er, C, idx


def load_span(rows, er, e_ab, idx, a):
    """`R_a`: the span of the boundary loads that the self-stresses of `rows`
    transmit through the split edge `ab` at `a`.  This is `repin.seed_probe`'s
    `R_a` computation (§(K-tight) *Step 2*), lifted from that driver's affine
    model onto the homogeneous one."""
    base_a = 6 * idx[a]
    out = []
    for lam in left_nullspace(rows):
        r = [F(0)] * 6
        for ri in er[e_ab]:
            for k in range(6):
                r[k] += lam[ri] * rows[ri][base_a + k]
        out.append(r)
    return span_basis(out)


# ---------------- the seed frame ---------------------------------------------

def split_setup(E, v):
    """`(a, b, c, Gp, Vp, VG, tgtG, tgtGp)` for the split at `v`, or None."""
    o = orient(E, v)
    if o is None:
        return None
    a, b, c = o
    Gp = splitOff(E, v, a, b)
    nG = len(verts_of(E))
    return (a, b, c, Gp,
            sorted(verts_of(Gp), key=str), sorted(verts_of(E), key=str),
            6 * (nG - 1) - deficiency(E), 6 * (nG - 2) - deficiency(Gp))


def hard_stratum_seed(Gp, Vp, a, b, seed, tgtGp, tally):
    """One `G'` seed on the hard stratum, or `None` with `tally` updated.

    Returns `(P, N, rows, er, C, idx, r)`: homogeneous body points `P`, the
    homogeneous panel normals `N` (= the points of `sigma u`), the rigidity
    data at `P`, and the generator `r` of `R_a`.

    Guards, in order (each rejection is counted, none consumes rng): the
    sampler failing; a closed-star rank below 3 at some body (the
    `plane_basis` genericity guard, `flanks.star_span_ranks`); two adjacent
    points projectively equal; the seed off target rank; a non-hub whose panel
    normal is not unique; and finally the stratum test `(s0, dim R_a) =
    (0, 1)`."""
    pl = place_pencil_general(Gp, random.Random(seed))
    if pl is None:
        tally['rej_sampler'] += 1
        return None
    placed, pt, nrm, hubs, nb = pl
    ranks = star_span_ranks(Gp, placed)
    if any(rk != 3 for rk in ranks.values()):
        tally['rej_star'] += 1
        return None
    P = {w: hat(placed[w]) for w in Vp}
    if any(not prop(P[u], P[u]) for u in Vp) or \
            any(rank([P[u], P[w]]) != 2 for (u, w) in Gp):
        tally['rej_coincident'] += 1
        return None
    rows, er, C, idx = rows_from_points(Gp, Vp, P)
    if rank(rows) != tgtGp:
        tally['rej_rank'] += 1
        return None
    nbp = neighbors(Gp)
    N = {}
    for w in Vp:
        if w in nrm:
            nn = nrm[w]
            N[w] = [nn[0], nn[1], nn[2],
                    -sum(nn[i] * pt[w][i] for i in range(3))]
        else:
            cand = null4([P[w]] + [P[t] for t in sorted(nbp[w], key=str)])
            if cand is None:
                tally['rej_normal'] += 1
                return None
            N[w] = cand
    assert all(any(t != 0 for t in N[w]) for w in Vp), "zero panel normal"
    e_ab = next(e for e in er if set(e) == {a, b})
    Ra = load_span(rows, er, e_ab, idx, a)
    shared = [e for e in Gp if set(e) != {a, b}]
    s0 = 5 * len(shared) - rank(rows_from_points(shared, Vp, P)[0])
    if len(Ra) != 1 or s0 != 0:
        tally['rej_stratum'] += 1
        return None
    return P, N, rows, er, C, idx, Ra[0]


def route_sigma_witness(E, VG, v, a, b, P, N, tgtG, seed):
    """Route A run at the dual seed `sigma u`: sweep `point_{sigma u}(v)`
    inside `Pi_{sigma u}(b) = P[b]^perp` for a target-rank realization of `G`.
    Returns the witness's homogeneous point map `Q`, or `None`."""
    rgs = random.Random(9000 + seed)
    bs = nullspace([P[b]])
    assert len(bs) == 3, "a panel is 3-dimensional"
    for _ in range(SWEEP_TRIES):
        co = [rquat(rgs) for _ in bs]
        x = [sum((co[i] * bs[i][k] for i in range(3)), F(0)) for k in range(4)]
        if all(t == 0 for t in x) or prop(x, N[a]) or prop(x, N[b]):
            continue
        Q = dict(N)
        Q[v] = x
        if rank(rows_from_points(E, VG, Q)[0]) == tgtG:
            return Q
    return None


def dual_points(edges, V, Q):
    """The body points dual to the panel normals `Q`: at each body the unique
    point annihilating its own normal and its neighbours'.  `None` if some
    body's point is not unique."""
    nb = neighbors(edges)
    out = {}
    for w in V:
        cand = null4([Q[w]] + [Q[t] for t in sorted(nb[w], key=str)])
        if cand is None:
            return None
        out[w] = cand
    return out


def nondeg_conjuncts_hom(edges, V, P, N, hubs):
    """The four conjuncts of `IsNondegPencilRealization`
    (`Molecule/Pencil/Motive.lean:110-115`) at HOMOGENEOUS `(P, N)`, returned
    as a 4-tuple of bools:

      1. panel data: every normal nonzero, `P[w] . N[w] = 0`, and
         `P[u] . N[w] = 0` across every edge;
      2. adjacent points projectively distinct;
      3. `LinearIndepOn normal (closedHubNbhd v)` at every body;
      4. `LinearIndepOn point (closedNbhd v)` at every NON-hub body.

    Divergence candidate against `flanks.nondeg_conjuncts`, which tests the
    same four conjuncts but takes an AFFINE placement and derives the normals
    itself -- it cannot express `sigma u`, whose points are another
    configuration's normals.  See `notes/scripts/README.md` *Divergences*."""
    nb = neighbors(edges)
    c1 = (all(any(t != 0 for t in N[w]) for w in V)
          and all(dot(P[w], N[w]) == 0 for w in V)
          and all(dot(P[u], N[w]) == 0 and dot(P[w], N[u]) == 0
                  for (u, w) in edges))
    c2 = all(rank([P[u], P[w]]) == 2 for (u, w) in edges)
    c3 = True
    for w in V:
        chn = sorted([t for t in ({w} | nb.get(w, set())) if t in hubs],
                     key=str)
        if chn and rank([N[t] for t in chn]) != len(chn):
            c3 = False
    c4 = True
    for w in V:
        if w in hubs:
            continue
        cn = sorted({w} | nb.get(w, set()), key=str)
        if rank([P[t] for t in cn]) != len(cn):
            c4 = False
    return c1, c2, c3, c4


def chart_point_equations(edges, V, P, N, hubs):
    """Does every body's point solve the chart's binding point equation --
    i.e. is it the common point of the panels of its closed hub neighbourhood
    (a `cross3` where that set has three members, an orthogonality where it
    has fewer)?  Returns `(ok, n_bound)`.

    This is EVIDENCE FOR, not proof of, chart-image membership: it does not
    perform the `fillHub` solve."""
    nb = neighbors(edges)
    ok, bound = True, 0
    for w in V:
        chn = sorted([t for t in ({w} | nb.get(w, set())) if t in hubs],
                     key=str)
        if len(chn) == 3:
            bound += 1
            cand = null4([N[t] for t in chn])
            if cand is None or not prop(cand, P[w]):
                ok = False
        elif any(dot(P[w], N[t]) != 0 for t in chn):
            ok = False
    return ok, bound


def new_tally(**extra):
    t = dict(seeds=0, rej_sampler=0, rej_star=0, rej_coincident=0,
             rej_rank=0, rej_normal=0, rej_stratum=0)
    t.update(extra)
    return t


def show(label, t):
    print(f"    {label}: " + " ".join(f"{k}={v}" for k, v in t.items()))


# ---------------- mode: --transport ------------------------------------------

def transport(E, v, seeds, label, totals):
    """(sigma1)-(sigma6) at every hard-stratum seed of one split.

      V0  homogeneous pencil data: `N[w].P[w] = 0`, `N[u].P[w] = 0` on edges.
      V1  (sigma4): `N[u] ^ N[w] ~ star(P[u] ^ P[w])` on every edge, i.e.
          `sigma` = "replace every body's point by its own panel normal".
      V2  `rank R(sigma u) = rank R(u) = target`, and `dim R_a`, `s0` agree.
      V3  criterion transport (sigma6): `critA(sigma u)` <-> `r not perp
          alpha_{pt b}`, plus `r(sigma u) ~ star r(u)`.
      V4  the six-dimensional span `beta_{Pi b} + beta_{Pi c} + alpha_{pt b}`
          of the sigma-completeness theorem.
      V5  route sigma's witness, pulled back into `u`'s frame by one more
          `sigma`: a target-rank realization of `G` with `pt(v) = pt(b)` and
          `pt(a)` on `Pi(a) cap Pi(c)`, every other body fixed."""
    a, b, c, Gp, Vp, VG, tgtG, tgtGp = split_setup(E, v)
    print(f"== {label}: v={v} a={a} b={b} c={c} target(G)={tgtG} "
          f"target(G')={tgtGp} ==")
    t = new_tally(V0=0, V1=0, V2=0, V3=0, V4=0, V5=0, six=0)
    for seed in seeds:
        got = hard_stratum_seed(Gp, Vp, a, b, seed, tgtGp, t)
        if got is None:
            continue
        P, N, rows, er, C, idx, r = got
        t['seeds'] += 1
        t['V0'] += (all(dot(N[w], P[w]) == 0 for w in Vp)
                    and all(dot(N[u], P[w]) == 0 and dot(N[w], P[u]) == 0
                            for (u, w) in Gp))
        t['V1'] += all(prop(wedge2(N[u], N[w]), hodge_star(wedge2(P[u], P[w])))
                       for (u, w) in Gp)
        # --- the dual seed sigma u -----------------------------------------
        rows_s, er_s, C_s, idx_s = rows_from_points(Gp, Vp, N)
        e_ab = next(e for e in er if set(e) == {a, b})
        Ra_s = load_span(rows_s, er_s, e_ab, idx_s, a)
        shared = [e for e in Gp if set(e) != {a, b}]
        s0s = 5 * len(shared) - rank(rows_from_points(shared, Vp, N)[0])
        t['V2'] += (rank(rows_s) == tgtGp and len(Ra_s) == 1 and s0s == 0)
        if len(Ra_s) != 1:
            continue
        rs = Ra_s[0]
        beta_b_s, beta_c_s = lambda2_perp(P[b]), lambda2_perp(P[c])
        alpha_b, alpha_c = lambda2_through(P[b]), lambda2_through(P[c])
        assert len(alpha_b) == 3 and len(alpha_c) == 3
        critA_s = any(dot(rs, w) != 0 for w in beta_b_s)
        critB_s = any(dot(rs, w) != 0 for w in beta_c_s)
        predA = any(dot(r, w) != 0 for w in alpha_b)
        predB = any(dot(r, w) != 0 for w in alpha_c)
        t['V3'] += (critA_s == predA and critB_s == predB
                    and prop(rs, hodge_star(r)))
        six = len(span_basis(lambda2_perp(N[b]) + lambda2_perp(N[c])
                             + alpha_b))
        t['V4'] += (six == 6)
        t['six'] += six
        # --- V5: the witness, and its pullback ------------------------------
        Q = route_sigma_witness(E, VG, v, a, b, P, N, tgtG, seed)
        if Q is None:
            continue
        Cpb = {e: hodge_star(wedge2(Q[e[0]], Q[e[1]])) for e in E}
        rk_pb = rank(build_rigidity_extensors(VG, [(e, Cpb[e]) for e in E]))
        pt_pb = dual_points(E, VG, Q)
        if pt_pb is None:
            continue
        joins = all(prop(Cpb[e], wedge2(pt_pb[e[0]], pt_pb[e[1]])) for e in E
                    if not prop(pt_pb[e[0]], pt_pb[e[1]]))
        t['V5'] += (rk_pb == tgtG and prop(pt_pb[v], P[b])
                    and dot(pt_pb[a], N[a]) == 0 and dot(pt_pb[a], N[c]) == 0
                    and all(prop(pt_pb[w], P[w]) for w in VG
                            if w not in (v, a))
                    and joins)
    show("tally", t)
    n = t['seeds']
    for k in ('V0', 'V1', 'V2', 'V3', 'V4', 'V5'):
        assert t[k] == n, (k, t)
    assert t['six'] == 6 * n, t
    totals['seeds'] += n
    return t


# ---------------- mode: --adv ------------------------------------------------

def adversarial(E, v, seeds, label, totals, strict=True):
    """The adversarial half.

      A  `dim(alpha_{pt b} + alpha_{pt c}) = 5`, its Euclidean perp generated
         by `star C(bc)` -- so "route sigma fails uniformly" is exactly
         `star r || C(bc)`.
      B  `dim(beta_{Pi b} + beta_{Pi c}) = 5`, perp `star C(M)`, and
         `C(M)`, `C(bc)` independent ((Lambda 0d) at the sampled seeds).
      C  the `predA` census: is `r not perp alpha_{pt b}` ever FALSE?  Where
         it is, the route-A sweep at `sigma u` must observationally fail --
         the criterion is a biconditional, not a sufficient condition.
      D  pullback legality: the witness's hinges are all nonzero, its dual
         points exist, the incidences hold, and the extensor system has
         target rank.

    Also records the escapes actually observed: route sigma at `sigma u`, and
    routes A/B at `u`.  `strict=False` suppresses the closing asserts, for the
    residual-habitat legs where the valid pool may be empty."""
    su = split_setup(E, v)
    if su is None:
        print(f"== {label}: not a usable split ==")
        return None
    a, b, c, Gp, Vp, VG, tgtG, tgtGp = su
    print(f"== {label}: v={v} a={a} b={b} c={c} ==")
    t = new_tally(A=0, B=0, D=0, predA=0, predAfalse=0, predAfalse_swept=0,
                  esc_sigma=0, esc_ab=0)
    for seed in seeds:
        got = hard_stratum_seed(Gp, Vp, a, b, seed, tgtGp, t)
        if got is None:
            continue
        P, N, rows, er, C, idx, r = got
        t['seeds'] += 1
        alpha_b, alpha_c = lambda2_through(P[b]), lambda2_through(P[c])
        beta_b, beta_c = lambda2_perp(N[b]), lambda2_perp(N[c])
        # (A) alpha_b + alpha_c is 5-dim, perp generated by star C(bc)
        ab_span = span_basis(alpha_b + alpha_c)
        perp = nullspace(ab_span)
        Cbc = wedge2(P[b], P[c])
        t['A'] += (len(ab_span) == 5 and len(perp) == 1
                   and prop(perp[0], hodge_star(Cbc)))
        # (B) the meet line C(M) against C(bc)
        bc_span = span_basis(beta_b + beta_c)
        perpM = nullspace(bc_span)
        CM = hodge_star(perpM[0]) if len(perpM) == 1 else None
        t['B'] += (len(bc_span) == 5 and CM is not None
                   and rank([CM, Cbc]) == 2)
        # (C) the predA census, and the observational check where it is false
        predA = any(dot(r, w) != 0 for w in alpha_b)
        t['predA'] += predA
        Q = route_sigma_witness(E, VG, v, a, b, P, N, tgtG, seed)
        t['esc_sigma'] += (Q is not None)
        if not predA:
            t['predAfalse'] += 1
            t['predAfalse_swept'] += (Q is None)
        # routes A/B at u, observed (independent draws inside Pi(b))
        escAB = False
        for j in range(10):
            rg = random.Random(700 + 97 * seed + j)
            bsb = nullspace([N[b]])
            co = [rquat(rg) for _ in bsb]
            xx = [sum((co[i] * bsb[i][k] for i in range(len(bsb))), F(0))
                  for k in range(4)]
            if all(z == 0 for z in xx) or prop(xx, P[a]) or prop(xx, P[b]):
                continue
            Q2 = dict(P)
            Q2[v] = xx
            if rank(rows_from_points(E, VG, Q2)[0]) == tgtG:
                escAB = True
                break
        t['esc_ab'] += escAB
        # (D) pullback legality
        if Q is not None:
            Cpb = {e: hodge_star(wedge2(Q[e[0]], Q[e[1]])) for e in E}
            nz = all(any(z != 0 for z in Cpb[e]) for e in E)
            pts = dual_points(E, VG, Q)
            incid = pts is not None and all(
                dot(pts[uu], Q[uu]) == 0 and dot(pts[uu], Q[ww]) == 0
                and dot(pts[ww], Q[uu]) == 0 and dot(pts[ww], Q[ww]) == 0
                for (uu, ww) in E)
            rk = rank(build_rigidity_extensors(VG, [(e, Cpb[e]) for e in E]))
            t['D'] += (nz and incid and rk == tgtG)
    show("tally", t)
    n = t['seeds']
    if strict:
        for k in ('A', 'B', 'D', 'predA', 'esc_sigma', 'esc_ab'):
            assert t[k] == n, (k, t)
        assert t['predAfalse'] == 0, t
        totals['seeds'] += n
    return t


# ---------------- mode: --nondeg ---------------------------------------------

def nondegeneracy(E, v, seeds, label, totals):
    """Is route sigma's witness a NONDEGENERATE pencil realization?

    Per hard-stratum seed `u`: the four conjuncts at `u`; the four at
    `sigma u` (reported per conjunct, because they are the obligation);
    route A at `sigma u`; the four conjuncts at that witness; and the chart's
    binding point equations at `u` and at the witness."""
    a, b, c, Gp, Vp, VG, tgtG, tgtGp = split_setup(E, v)
    hubsG, hubsGp = hub_set(E), hub_set(Gp)
    print(f"== {label}: v={v} a={a} b={b} c={c} ==")
    t = new_tally(u_nd=0, u_chart=0, su_nd=0, su_c1=0, su_c2=0, su_c3=0,
                  su_c4=0, wit=0, wit_nd=0, wit_chart=0)
    for seed in seeds:
        got = hard_stratum_seed(Gp, Vp, a, b, seed, tgtGp, t)
        if got is None:
            continue
        P, N, rows, er, C, idx, r = got
        t['seeds'] += 1
        t['u_nd'] += all(nondeg_conjuncts_hom(Gp, Vp, P, N, hubsGp))
        t['u_chart'] += chart_point_equations(Gp, Vp, P, N, hubsGp)[0]
        d1, d2, d3, d4 = nondeg_conjuncts_hom(Gp, Vp, N, P, hubsGp)
        t['su_nd'] += all((d1, d2, d3, d4))
        t['su_c1'] += d1
        t['su_c2'] += d2
        t['su_c3'] += d3
        t['su_c4'] += d4
        Q = route_sigma_witness(E, VG, v, a, b, P, N, tgtG, seed)
        if Q is None:
            continue
        t['wit'] += 1
        M = dual_points(E, VG, Q)
        if M is None:
            continue
        t['wit_nd'] += all(nondeg_conjuncts_hom(E, VG, Q, M, hubsG))
        t['wit_chart'] += chart_point_equations(E, VG, Q, M, hubsG)[0]
    show("tally", t)
    n = t['seeds']
    for k in ('u_nd', 'u_chart', 'su_nd', 'su_c1', 'su_c2', 'su_c3', 'su_c4',
              'wit', 'wit_nd', 'wit_chart'):
        assert t[k] == n, (k, t)
    totals['seeds'] += n
    return t


# ---------------- mode: --fixed ----------------------------------------------

def Jv(x):
    return [sum((J[i][k] * x[k] for k in range(4)), F(0)) for i in range(4)]


def fixed_is_degenerate():
    """sigma-EQUIVARIANT seed recipes are dead, with a proof and a witness.

    Over R the project's own polarity (the Hodge star of the DEFINITE standard
    dot product) has no fixed pencil configuration at all: `normal_w ~ point_w`
    plus the landed incidence conjunct `point w . normal w = 0` forces
    `point_w . point_w = 0`.  That is checked symbolically, not numerically.

    The general correlation is worse than empty, it is degenerate.  For a NULL
    (symplectic) correlation `J` the incidence is automatic and every hinge
    line is forced into the linear line complex of `J`, so `omega_e := c_e
    star S` (`S` = the complex's screw) is a self-stress for every cycle-space
    flow `c` and the rank drops by at least the cycle rank.  Measured on `C6`
    (tight: `5|E| = 30 = 6(|V|-1)`, cycle rank 1): deficit exactly 1."""
    rng = random.Random(2718)
    n = 6
    E = [(i, (i + 1) % n) for i in range(n)]
    V = list(range(n))
    tgt = 6 * (n - 1)
    print(f"C6: |E|={len(E)} 5|E|={5*len(E)} target=6(|V|-1)={tgt} "
          f"cycle rank={len(E) - n + 1}")
    ok = tried = 0
    for trial in range(6):
        P = {0: [rquat(rng) for _ in range(4)]}
        good = True
        for i in range(1, n - 1):
            bs = nullspace([Jv(P[i - 1])])
            co = [rquat(rng) for _ in bs]
            P[i] = [sum((co[k] * bs[k][j] for k in range(len(bs))), F(0))
                    for j in range(4)]
            if all(z == 0 for z in P[i]):
                good = False
        bs = nullspace([Jv(P[n - 2]), Jv(P[0])])
        co = [rquat(rng) for _ in bs]
        P[n - 1] = [sum((co[k] * bs[k][j] for k in range(len(bs))), F(0))
                    for j in range(4)]
        if not good or all(z == 0 for z in P[n - 1]):
            continue
        if any(rank([P[u], P[w]]) != 2 for (u, w) in E):
            continue
        tried += 1
        iso = all(dot(P[u], Jv(P[w])) == 0 for (u, w) in E)
        rows, er, C, idx = rows_from_points(E, V, P)
        rk = rank(rows)
        S = [J[0][1], J[0][2], J[0][3], J[1][2], J[1][3], J[2][3]]
        perp = all(dot(hodge_star(S), C[e]) == 0 for e in E)
        print(f"  trial {trial}: all edges J-isotropic={iso} "
              f"star(S) perp every hinge={perp} rank={rk}/{tgt} "
              f"deficit={tgt - rk}")
        ok += (iso and perp and rk == tgt - 1)
    print(f"  linear-complex placements with deficit exactly 1: {ok}/{tried}")
    assert tried == 6 and ok == 6, (tried, ok)


# ---------------- driver ------------------------------------------------------

def control_split(chain):
    """The tight control (double-subdivided `K4`) and its split vertex on the
    given chain."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, _hubs, chains, _all = double_subdivide(K4)
    return E, chains[chain][1]


def w19_splits(limit=2):
    """The first `limit` usable degree-2 splits of the `W19` residual
    inhabitant -- the (K-res) habitat probe."""
    EW = W19()
    nb = neighbors(EW)
    out = []
    for x in sorted((w for w in nb if len(nb[w]) == 2), key=str):
        if orient(EW, x) is not None:
            out.append((EW, x))
        if len(out) >= limit:
            break
    return out


def main(argv):
    mode = argv[1] if len(argv) > 1 else '--transport'
    print(f"sigma.py {mode}  (exact Q; seed pools "
          f"{CHAIN0_SEEDS.start}-{CHAIN0_SEEDS.stop - 1} / "
          f"{CHAIN1_SEEDS.start}-{CHAIN1_SEEDS.stop - 1}; "
          f"route-A sweep rng 9000+seed, {SWEEP_TRIES} draws)")
    totals = dict(seeds=0)
    E0, v0 = control_split(0)
    E1, v1 = control_split(1)
    if mode == '--transport':
        transport(E0, v0, CHAIN0_SEEDS, "tight control, chain 0", totals)
        transport(E1, v1, CHAIN1_SEEDS, "tight control, chain 1", totals)
    elif mode == '--adv':
        adversarial(E0, v0, CHAIN0_SEEDS, "tight control, chain 0", totals)
        adversarial(E1, v1, CHAIN1_SEEDS, "tight control, chain 1", totals)
        for EW, x in w19_splits():
            r = adversarial(EW, x, W19_SEEDS, f"W19 split at {x}", totals,
                            strict=False)
            assert r is None or r['seeds'] == 0, \
                "W19 leg found hard-stratum seeds: the residual habitat is " \
                "no longer unsampled -- update the workbook before asserting"
        print("  (K-res) residual habitat: 0 valid hard-stratum seeds "
              "in the probed range -- UNSAMPLED, not tested-and-passed")
    elif mode == '--nondeg':
        nondegeneracy(E0, v0, CHAIN0_SEEDS, "tight control, chain 0", totals)
        nondegeneracy(E1, v1, CHAIN1_SEEDS, "tight control, chain 1", totals)
    elif mode == '--fixed':
        fixed_is_degenerate()
        print("OK")
        return
    else:
        print(f"unknown mode {mode}")
        return 2
    assert totals['seeds'] == 63, totals
    print(f"  pool: {totals['seeds']} hard-stratum seeds, every check n/n")
    print("OK")


if __name__ == '__main__':
    sys.exit(main(sys.argv) or 0)
