"""
Phase 39 (K-tight) — the carrier-aware KT pp. 684-691 boundary-load RE-PIN.

The (K) non-constancy recon's SS2 escape criterion (`R_a not subset S^perp`,
`S = Lambda^2 Pihat(a) + pencil(b) + pencil(c)`, dim 5) was derived in KT's
PANEL model and flagged "not yet re-pinned against KT pp. 684-691"; the
widened-kernel recon then found a direct mispredict (tight-control seed 442).
This script validates the CARRIER-CORRECTED criterion, re-derived from KT's
Claims 6.11/6.12 machinery against the pencil carrier
(`HasPencilPanelRealization` pins every hinge to `pt(u) ^ pt(v)`, so KT's
three per-panel line freedoms collapse to point-placement freedoms):

  * KT's M1 (`hinge(vb) := q(ab)`, `hinge(va) := L` swept in `Pi(a)`) is DEAD
    on the carrier: `hinge(vb) = pt(v) ^ pt(b) = q(ab)` forces
    `pt(v) in line(pt a, pt b)` -- the nondegeneracy-forbidden locus.
  * Route A = insert `v`, freedom `pt(v)` in `Pihat(b)` (b hub) / free (else).
  * Route B = KT's p3 via the iso rho: re-place `pt(a)` in `Pihat(c)` with
    `pt(v) := old pt(a)`; its load is `-r` by KT (6.44).
  * Obstruction space `U := {u : (u @ a, -u @ b) in rowspan(shared rows)}`;
    `U cap C(ab)^perp = R_a`, and `dim U = dim R_a + 1` is FORCED by counts.
  * dim R_a = 1, s0 = 0 stratum: route-A failure locus in `Pi(b)` is the
    degenerate conic `line(ab) UNION P'` (a second line!); UNIFORM route-A
    failure iff `r perp Lambda^2 Pihat(b)` (the FULL 3-dim panel span --
    pencil at `pt(b)` PLUS pencil at `pt(a)` inside `Pi(b)`); route-B dually
    with `Pihat(c)`. Combined (K-tight) failure iff
    `r perp (Lambda^2 Pihat(b) + Lambda^2 Pihat(c))` (5-dim) iff `r` is
    parallel to the Euclidean-perp generator, which is star(C(M)) for
    M = the meet line `Pi(b) cap Pi(c)`.
  * s0 >= 1 at a target-rank G' seed forces uniform failure outright
    (corank(R(G)) >= s0), independent of any criterion.

Exact-Q throughout, on top of `widened.py` / `../escape/` machinery.

Drivers:
    python3 notes/scripts/w4/repin.py --control   # tight control incl. seed 442
    python3 notes/scripts/w4/repin.py --theta     # theta(4,4,3), dim R_a = 2
    python3 notes/scripts/w4/repin.py --witness   # W19 / S29 residual splits
    python3 notes/scripts/w4/repin.py --stratum   # the (def 0, dim R_a 1) pool stratum
    python3 notes/scripts/w4/repin.py --pointwise # the per-placement biconditional
    python3 notes/scripts/w4/repin.py --hinge     # the coincident-hinge guard's
                                                  #   adversarial test (2026-08-06)

This module is also where the configuration GENERICITY GUARDS live (moved down
here in the 2026-08-06 re-baselining round, slice S1, since `repin` sits under
the whole `w4/` chain): `star_span_ranks` (from `flanks`, which re-exports it),
and the new `hinge_coincidences` / `coincident_hinges` / `star_generic` that
close the hole (OC-7) found in it.
"""
import itertools
import os
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from widened import (orient, removeV, splitOff, place_pencil_general,
                     split_report, residuals, prime_pool, W19, f_of)
from nogood_subdiv import deficiency, hub_set
from saferes import w29, split_usable
from pencil_escape import (build_rigidity, rank, left_nullspace, nullspace,
                           wedge2, hat, dot, rvec3, rquat, double_subdivide)
from localtest import in_plane_point, meet_line
from kbare_common import verts_of


# ---------------- linear-algebra helpers -----------------------------------

def rank_at_V(edges, placed, V):
    """Rank over an EXPLICIT vertex list (isolated columns kept)."""
    rows, er, C, idx, n = build_rigidity({'edges': edges, 'V': V, 'pt': placed})
    return rank(rows), rows, er, idx


def span_basis(vectors):
    """A basis (list) of the span of `vectors`, via rref pivots."""
    from pencil_escape import rref
    if not vectors:
        return []
    R, piv = rref([v[:] for v in vectors])
    return [R[i] for i in range(len(piv))]


def in_span(vec, basis):
    if all(x == 0 for x in vec):
        return True
    return rank(basis + [vec]) == rank(basis)


def hodge_star(w):
    """star on Lambda^2 R^4 in Plucker order (01,02,03,12,13,23):
    star(p01,p02,p03,p12,p13,p23) = (p23,-p13,p12,p03,-p02,p01)."""
    return [w[5], -w[4], w[3], w[2], -w[1], w[0]]


# ---------------- panel spans ----------------------------------------------

# canonical home `exactcore.cross3`; the local name stays `cross` (2026-08-05).
# `neighbors` arrived with `star_span_ranks` (2026-08-06, round S1).
from exactcore import cross3 as cross, neighbors   # noqa: E402


def robust_plane_basis(n):
    """Two independent in-plane directions, valid for ANY nonzero normal.

    THE canonical in-plane sampler basis.  `localtest.plane_basis` /
    `probe_zero`'s nested clone / `kbare_common.plane_basis` all degenerate
    (return two PARALLEL directions) when a normal coordinate is 0 — the
    defect behind the corrected `widened.py` escape figures.  Prefer this one
    in any new work; see `notes/scripts/README.md` *Divergences*."""
    for e in ([F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), F(0), F(1)]):
        b0 = cross(n, e)
        if any(x != 0 for x in b0):
            return b0, cross(n, b0)
    return None


def rob_in_plane(pt0, n, rng):
    b0, b1 = robust_plane_basis(n)
    s, t = rquat(rng), rquat(rng)
    return [pt0[i] + s * b0[i] + t * b1[i] for i in range(3)]


def plane_pts(pt_h, nrm_h, rng):
    """Three affine points spanning the plane {p : nrm.(p - pt_h) = 0}."""
    p1 = rob_in_plane(pt_h, nrm_h, rng)
    p2 = rob_in_plane(pt_h, nrm_h, rng)
    if rank([hat(pt_h), hat(p1), hat(p2)]) != 3:
        return None
    return pt_h, p1, p2


def lambda2_plane(pt_h, nrm_h, rng):
    """Basis of Lambda^2 Pihat(h) (3-dim) for the affine plane at a hub."""
    for _ in range(8):
        ps = plane_pts(pt_h, nrm_h, rng)
        if ps is not None:
            h0, h1, h2 = (hat(p) for p in ps)
            return [wedge2(h0, h1), wedge2(h0, h2), wedge2(h1, h2)]
    return None


def lambda2_through(phat):
    """Basis of {phat ^ x : x in K^4} (3-dim): all lines through the point."""
    es = [[F(1) if k == i else F(0) for k in range(4)] for i in range(4)]
    return span_basis([wedge2(phat, e) for e in es])


# ---------------- configuration genericity guards ---------------------------
#
# `star_span_ranks` moved down here from `flanks.py:201` on 2026-08-06 (round
# S1) once it had SIX consumers, past section 2 rule 2's own trigger; `flanks`
# re-exports it, so no recorded figure moves and the five importing modules may
# repoint at leisure.  `hinge_coincidences` and the composite `star_generic`
# are the NEW guard the round adds beside it -- see (OC-7) / *Harness debt*
# item 4 for why the old one is not sufficient on its own.

def star_span_ranks(edges, placed):
    """Per vertex, the rank of the hats of `{v} u N(v)`.  Maximal value 3
    everywhere (a hub's star lies in its 3-dim panel; a degree-2 body has
    three points).  Rank 3 at every vertex is `IsNondegPencilRealization`'s
    fourth conjunct.

    NOT a sufficient genericity guard on its own, and its docstring claimed
    otherwise until 2026-08-06: at a hub whose in-plane sampler degenerated it
    still returns 3 whenever a THIRD neighbour spans the panel, so it misses
    the coincident-hinge / free-rotor configuration entirely.  Measured at
    32 of 357 POOL-G frames -- `Pencil-informal.md` §(K-out) (OC-7), and
    `notes/scripts/README.md` *Harness debt* item 4.  Pair it with
    `hinge_coincidences`, or just call `star_generic`."""
    nb = neighbors(edges)
    return {v: rank([hat(placed[v])]
                    + [hat(placed[u]) for u in sorted(nb[v], key=str)])
            for v in sorted(nb, key=str)}


def hinge_coincidences(edges, placed, h, x):
    """The neighbours `u != x` of `h` whose hinge line `C(h, u)` is
    PROJECTIVELY EQUAL to `C(h, x)` -- equivalently, whose point is collinear
    with `pt(h)` and `pt(x)`.

    Two bodies of the hub's star sharing one hinge line is a genuine
    degeneration of a pencil realization -- the hub becomes a free rotor -- and
    it is excluded by NO conjunct of `IsNondegPencilRealization` as
    `flanks.nondeg_conjuncts` implements them, nor by `star_span_ranks` above.
    This is the guard the round adds; `repin.py --hinge` is its adversarial
    test.  (`outerline.hinge_coincidences` is the same predicate, written
    locally when (OC-7) measured the defect; it is repointed at this copy in
    slice S2, which is also where the guard is ADOPTED at the 14 acceptance
    sites.  Nothing in S1 adopts it, so no acceptance set changes.)"""
    nb = neighbors(edges)
    Cx = wedge2(hat(placed[h]), hat(placed[x]))
    assert any(k != 0 for k in Cx), "degenerate hinge extensor"
    return [u for u in sorted(nb[h], key=str) if u != x
            and rank([Cx, wedge2(hat(placed[h]), hat(placed[u]))]) == 1]


def coincident_hinges(edges, placed):
    """Every `(v, x, u)` with `x < u` in `N(v)` sharing one hinge line at `v`.
    Empty iff no two hinge lines coincide anywhere in the configuration."""
    nb = neighbors(edges)
    out = []
    for v in sorted(nb, key=str):
        star = sorted(nb[v], key=str)
        for i, x in enumerate(star):
            for u in hinge_coincidences(edges, placed, v, x):
                if str(x) < str(u):
                    out.append((v, x, u))
    return out


def star_generic(edges, placed):
    """THE composite genericity guard: every closed star spans its panel AND
    no two hinge lines at a body coincide.  `star_span_ranks` alone is the
    version F13 found ineffective; this is what a new sampler or battery
    should test."""
    return (all(r == 3 for r in star_span_ranks(edges, placed).values())
            and not coincident_hinges(edges, placed))


# ---------------- the per-seed probe ----------------------------------------

def seed_probe(edges, v, seed, nplace=6, rng_salt=90000):
    """At one pencil-generic target-rank G' seed: the corrected per-route
    criteria, the legacy predicates, and the OBSERVED escapes (routes A, B).
    Returns None if the seed is invalid / not target-rank."""
    o = orient(edges, v)
    if o is None:
        return None
    a, b, c = o
    Gv, Gp = removeV(edges, v), splitOff(edges, v, a, b)
    nG = len(verts_of(edges))
    tgtG = 6 * (nG - 1) - deficiency(edges)
    tgtGp = 6 * (nG - 2) - deficiency(Gp)
    hubsG = hub_set(edges)
    pl = place_pencil_general(Gp, random.Random(seed))
    if pl is None:
        return None
    placed, pt, nrm, hubs, nb = pl
    Vp = sorted(verts_of(Gp), key=str)
    rkp, rows, er, idx = rank_at_V(Gp, placed, Vp)
    if rkp != tgtGp:
        return None
    out = {'seed': seed, 'a': a, 'b': b, 'c': c,
           'b hub': b in hubsG, 'c hub': c in hubsG}

    # --- stress side: s0 (per seed!), R_a, r -------------------------------
    shared = [e for e in Gp if set(e) != {a, b}]
    rk_sh, rows_sh, er_sh, idx_sh = rank_at_V(shared, placed, Vp)
    s0 = 5 * len(shared) - rk_sh
    out['s0'] = s0
    e_ab = next(e for e in er if set(e) == {a, b})
    base_a = 6 * idx[a]
    Ra = []
    for lam in left_nullspace(rows):
        r = [F(0)] * 6
        for ri in er[e_ab]:
            for k in range(6):
                r[k] += lam[ri] * rows[ri][base_a + k]
        Ra.append(r)
    Ra_basis = span_basis(Ra)
    out['dim R_a'] = len(Ra_basis)
    out['corank Gp'] = 5 * len(Gp) - rkp

    # --- the obstruction space U -------------------------------------------
    motions = nullspace(rows_sh)
    ia, ib = 6 * idx_sh[a], 6 * idx_sh[b]
    D = [[m[ia + k] - m[ib + k] for k in range(6)] for m in motions]
    Db = span_basis(D)
    U = nullspace(Db) if Db else [[F(1) if k == i else F(0) for k in range(6)]
                                  for i in range(6)]
    out['dim U'] = len(U)
    out['dim U = dim R_a + 1'] = (len(U) == len(Ra_basis) + 1)
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab = wedge2(ah, bh)
    # U cap C(ab)^perp == R_a ?  {u in span U : u . Cab = 0}
    # coordinates: u = sum t_i U_i ; condition sum t_i (U_i . Cab) = 0
    coeffs = [dot(u, Cab) for u in U]
    ts = nullspace([coeffs]) if any(x != 0 for x in coeffs) else \
        [[F(1) if k == i else F(0) for k in range(len(U))] for i in range(len(U))]
    UcapCab = span_basis([[sum((t[i] * U[i][k] for i in range(len(U))), F(0))
                           for k in range(6)] for t in ts])
    out['U cap Cab-perp == R_a'] = (
        len(UcapCab) == len(Ra_basis)
        and all(in_span(x, Ra_basis) for x in UcapCab))
    out['R_a subset U'] = all(
        all(dot(r, d) == 0 for d in Db) for r in Ra_basis)

    # --- criteria (dot-tests against explicit spans) ------------------------
    rng = random.Random(rng_salt + 7919 * seed)
    if b in hubsG and b in nrm:
        L2b = lambda2_plane(pt[b], nrm[b], rng)
    else:
        L2b = span_basis(lambda2_through(ah) + lambda2_through(bh))
    if c in hubsG and c in nrm:
        L2c = lambda2_plane(pt[c], nrm[c], rng)
    else:
        Cac_span = span_basis(lambda2_through(ah) + lambda2_through(ch))
        L2c = Cac_span
    critA = any(any(dot(r, w) != 0 for w in L2b) for r in Ra_basis)
    critB = any(any(dot(r, w) != 0 for w in L2c) for r in Ra_basis)
    out['critA'] = critA
    out['critB'] = critB
    # legacy predicates, for the comparison record
    M2pen = any(any(dot(r, wedge2(bh, hat(placed[u]))) != 0
                    for u in nb[b]) for r in Ra_basis)
    L2a = [wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)]
    penb = [wedge2(bh, hat(placed[u])) for u in nb[b]]
    penc = [wedge2(ch, hat(placed[u])) for u in nb[c]]
    Sold = L2a + penb + penc
    Scrit = any(any(dot(r, w) != 0 for w in Sold) for r in Ra_basis)
    out['M2pencil'] = M2pen
    out['Scrit(old SS2)'] = Scrit

    # --- observed escapes ----------------------------------------------------
    escA = False
    for j in range(nplace):
        rg = random.Random(rng_salt + 97 * seed + j)
        pv = (rob_in_plane(pt[b], nrm[b], rg) if b in hubsG and b in nrm
              else rvec3(rg))
        if pv in (placed[a], placed[b]):
            continue
        pl2 = dict(placed)
        pl2[v] = pv
        VG = sorted(verts_of(edges), key=str)
        if rank_at_V(edges, pl2, VG)[0] == tgtG:
            escA = True
            break
    out['escA'] = escA
    escB = False
    for j in range(nplace):
        rg = random.Random(rng_salt + 131 * seed + j)
        pa = (rob_in_plane(pt[c], nrm[c], rg) if c in hubsG and c in nrm
              else rvec3(rg))
        if pa in (placed[a], placed[c]):
            continue
        pl2 = dict(placed)
        pl2[v] = placed[a]
        pl2[a] = pa
        VG = sorted(verts_of(edges), key=str)
        if rank_at_V(edges, pl2, VG)[0] == tgtG:
            escB = True
            break
    out['escB'] = escB
    out['_ctx'] = (placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG)
    return out


def second_line_check(edges, v, probe):
    """At an escaping dim-U-2 seed, EXHIBIT the second failure line P':
    the route-A failure locus is line(ab) UNION P', so a P'-point off
    line(ab) must fail by exactly 1."""
    o = orient(edges, v)
    a, b, c = o
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = probe['_ctx']
    if len(U) != 2 or len(Ra_basis) != 1 or not (b in hubsG and b in nrm):
        return None
    r = Ra_basis[0]
    # w = the U-element transverse to C(ab)^perp
    w = U[0] if dot(U[0], Cab) != 0 else U[1]
    if dot(w, Cab) == 0:
        return None
    kappa = dot(w, Cab)
    ah, bh = hat(placed[a]), hat(placed[b])
    rng = random.Random(31337)
    for _ in range(8):
        y = rob_in_plane(pt[b], nrm[b], rng)
        yh = hat(y)
        if rank([ah, bh, yh]) != 3:
            continue
        Fv = dot(r, wedge2(yh, ah))
        Gv = dot(r, wedge2(yh, bh))
        fw = dot(w, wedge2(yh, ah))
        gw = dot(w, wedge2(yh, bh))
        C2 = Fv * gw - fw * Gv
        if Fv == 0:
            continue
        # P' in basis (ah, bh, yh):  kappa*(alpha*F + beta*G) + gamma*C2 = 0
        alpha, beta, gamma = C2, F(0), -kappa * Fv
        x = [alpha * ah[k] + beta * bh[k] + gamma * yh[k] for k in range(4)]
        if x[3] == 0:
            continue
        pv = [x[k] / x[3] for k in range(3)]
        # must be in Pi(b) (it is: combination of in-plane points) & off line(ab)
        pl2 = dict(placed)
        pl2[v] = pv
        VG = sorted(verts_of(edges), key=str)
        rk = rank_at_V(edges, pl2, VG)[0]
        off_line = rank([hat(pv), ah, bh]) == 3
        return {'P-prime point': pv, 'off line(ab)': off_line,
                'rank': rk, 'target': tgtG, 'fails by': tgtG - rk}
    return None


# ---------------- drivers ---------------------------------------------------

def control():
    print("== tight control (dbl-subdivided K4): per-seed corrected criterion ==")
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    u, x, y, w = chains[0]
    n_ok = agreeA = agreeB = agree_comb = agreeM2 = agreeS = 0
    forced_fail = 0
    exhibited = False
    for seed in range(440, 480):
        p = seed_probe(E, x, seed, nplace=8)
        if p is None:
            continue
        n_ok += 1
        assert p['dim U = dim R_a + 1'], p
        assert p['U cap Cab-perp == R_a'], p
        assert p['R_a subset U'], p
        if p['dim R_a'] == 0:
            forced_fail += 1
            predA = predB = False
        else:
            predA, predB = p['critA'], p['critB']
        agreeA += (predA == p['escA'])
        agreeB += (predB == p['escB'])
        agree_comb += ((predA or predB) == (p['escA'] or p['escB']))
        agreeM2 += (p['M2pencil'] == p['escA'])
        agreeS += (p['Scrit(old SS2)'] == (p['escA'] or p['escB']))
        flag = ' <-- ' if seed == 442 else ''
        print(f"  seed {seed}: s0={p['s0']} dimRa={p['dim R_a']} "
              f"dimU={p['dim U']} critA={p['critA']} critB={p['critB']} "
              f"M2pen={p['M2pencil']} Sold={p['Scrit(old SS2)']} | "
              f"escA={p['escA']} escB={p['escB']}{flag}")
        if seed == 442:
            postmortem(E, x, p)
        if not exhibited and p['s0'] == 0 and p['escA'] and p['dim U'] == 2:
            sl = second_line_check(E, x, p)
            if sl is not None:
                print(f"    P' exhibition at seed {seed}: off-line="
                      f"{sl['off line(ab)']} rank {sl['rank']}/{sl['target']}"
                      f" (fails by {sl['fails by']})")
                assert sl['off line(ab)'] and sl['fails by'] == 1
                exhibited = True
    print(f"  seeds: {n_ok}; corrected criterion agree: "
          f"A {agreeA}/{n_ok}, B {agreeB}/{n_ok}, A|B {agree_comb}/{n_ok}; "
          f"legacy: M2pencil-vs-escA {agreeM2}/{n_ok}, "
          f"S-vs-(A|B) {agreeS}/{n_ok}; s0>0 forced-failure seeds: {forced_fail}")
    assert agreeA == n_ok and agreeB == n_ok and agree_comb == n_ok
    print("CONTROL OK: corrected per-route criterion exact on all seeds")


def postmortem(E, v, p):
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    print(f"    -- seed {p['seed']} post-mortem --")
    print(f"    s0={p['s0']}, dim R_a={p['dim R_a']}, dim U={p['dim U']}")
    if p['s0'] > 0:
        print("    s0 > 0: uniform failure is FORCED (corank(R(G)) >= s0); "
              "no r-criterion needed")
        return
    r = Ra_basis[0]
    rng = random.Random(4242)
    L2b = lambda2_plane(pt[b], nrm[b], rng) if b in nrm else None
    L2c = lambda2_plane(pt[c], nrm[c], rng) if c in nrm else None
    if L2b and L2c:
        both = span_basis(L2b + L2c)
        print(f"    dim(L2 Pihat(b) + L2 Pihat(c)) = {len(both)}")
        wbad = nullspace(both)
        print(f"    bad-line dim = {len(wbad)}; r parallel to it: "
              f"{all(in_span(r, wbad) for r in Ra_basis)}")
        p0, d = meet_line(pt[b], nrm[b], pt[c], nrm[c])
        # section 4 convention 1: with the 2026-08-06 signalling `meet_line`, a
        # zero `d` gives `CM = 0`, and `in_span(0, wbad)` is True by
        # convention -- i.e. the line below would PRINT a spurious True.  This
        # block only prints, so the guard is an assert.
        assert any(x != 0 for x in d), \
            f"panels Pi({b}), Pi({c}) parallel: no meet line M"
        m0, m1 = p0, [p0[i] + d[i] for i in range(3)]
        CM = wedge2(hat(m0), hat(m1))
        sCM = hodge_star(CM)
        print(f"    bad generator == star(C(meet line)): "
              f"{len(wbad) == 1 and in_span(sCM, wbad)}")
        print(f"    r . r (Klein pairing r-tilde null test) = "
              f"{dot(r, hodge_star(r))}")


def theta():
    print("== theta(4,4,3): the dim R_a = 2 stratum (determinantal escape) ==")
    import n9
    E = n9.theta_edges()
    n_ok = 0
    for seed in range(410, 440):
        p = seed_probe(E, 30, seed, nplace=6)
        if p is None:
            continue
        n_ok += 1
        assert p['dim U = dim R_a + 1'], p
        assert p['U cap Cab-perp == R_a'], p
        print(f"  seed {seed}: s0={p['s0']} dimRa={p['dim R_a']} "
              f"dimU={p['dim U']} critA={p['critA']} critB={p['critB']} | "
              f"escA={p['escA']} escB={p['escB']}")
        if n_ok >= 6:
            break
    print(f"  ({n_ok} seeds; dim U = dim R_a + 1 held on all)")


def witness():
    for name, G in (('W19', W19()), ('S29', w29())):
        print(f"== {name}: per-seed corrected criterion at residual splits ==")
        done = set()
        for (v, _, _) in split_usable(G)[0]:
            d = split_report(G, v)
            key = (d['deg b'], d['deg c'], d['s0'], d['corank Gp'])
            if key in done:
                continue
            done.add(key)
            n_ok = agreeA = agreeB = 0
            for seed in range(3000, 3030):
                p = seed_probe(G, v, seed, nplace=6)
                if p is None:
                    continue
                n_ok += 1
                assert p['dim U = dim R_a + 1'], p
                assert p['U cap Cab-perp == R_a'], p
                predA = p['critA'] and p['dim R_a'] >= 1
                predB = p['critB'] and p['dim R_a'] >= 1
                agreeA += (predA == p['escA'])
                agreeB += (predB == p['escB'])
                print(f"  v={v} seed {seed}: s0={p['s0']} dimRa={p['dim R_a']}"
                      f" dimU={p['dim U']} critA={p['critA']} "
                      f"critB={p['critB']} | escA={p['escA']} escB={p['escB']}")
                if n_ok >= 4:
                    break
            print(f"  -- split v={v}: criterion agree A {agreeA}/{n_ok}, "
                  f"B {agreeB}/{n_ok}")


def stratum(per_stratum=6, maxv=22):
    """The (def G = 0, dim R_a = 1) stratum of the residual pool -- the one
    with observed escape failures (10/12 in `widened.py --sample`)."""
    print("== residual pool, stratum (def 0, dim R_a 1): criterion vs observed ==")
    pairs = []
    for E, _ in residuals(prime_pool()):
        if len(verts_of(E)) > maxv or deficiency(E) != 0:
            continue
        for (v, _, _) in split_usable(E)[0]:
            d = split_report(E, v)
            if d is not None and d['dim R_a'] == 1:
                pairs.append((E, v))
    rng = random.Random(4242)
    rng.shuffle(pairs)
    tot = agree = fails_obs = fails_pred = 0
    for (E, v) in pairs[:per_stratum]:
        n_here = 0
        for seed in range(5000, 5030):
            p = seed_probe(E, v, seed, nplace=5)
            if p is None:
                continue
            tot += 1
            n_here += 1
            assert p['dim U = dim R_a + 1'], p
            pred = p['dim R_a'] >= 1 and (p['critA'] or p['critB'])
            obs = p['escA'] or p['escB']
            agree += (pred == obs)
            fails_obs += (not obs)
            fails_pred += (not pred)
            if not obs or not pred:
                print(f"  |V|={len(verts_of(E))} v={v} seed {seed}: "
                      f"s0={p['s0']} dimRa={p['dim R_a']} "
                      f"critA={p['critA']} critB={p['critB']} "
                      f"escA={p['escA']} escB={p['escB']}")
            if n_here >= 4:
                break
    print(f"  seeds probed {tot}; agree {agree}/{tot}; observed failures "
          f"{fails_obs}; predicted failures {fails_pred}")


def pointwise(nseeds=4, nplace=10):
    """The sharpest form: PER-PLACEMENT biconditional.  At a target-rank G'
    seed, a placement `x` attains target(G) IFF the two functionals
    `u -> u . C(va)(x)`, `u -> u . C(vb)(x)` are linearly independent on `U`
    (equivalently corank R(G) = s0 + dim(U cap C_va^perp cap C_vb^perp) is
    minimal).  Checked at the tight control AND at W19 (s0 = 2)."""
    cases = []
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    cases.append(('dbl-subdiv K4', E, chains[0][1], range(440, 460)))
    cases.append(('W19', W19(), 'w0_1', range(3000, 3020)))
    for name, edges, v, seeds in cases:
        a, b, c = orient(edges, v)
        nG = len(verts_of(edges))
        tgtG = 6 * (nG - 1) - deficiency(edges)
        hubsG = hub_set(edges)
        n_ok = agree = 0
        for seed in seeds:
            p = seed_probe(edges, v, seed, nplace=0)
            if p is None:
                continue
            n_ok += 1
            placed, pt, nrm, hubs2, nb, U, Ra_basis, Cab, _, _ = p['_ctx']
            s0 = p['s0']
            VG = sorted(verts_of(edges), key=str)
            for j in range(nplace):
                rg = random.Random(80000 + 97 * seed + j)
                pv = (rob_in_plane(pt[b], nrm[b], rg)
                      if b in hubsG and b in nrm else rvec3(rg))
                if pv in (placed[a], placed[b]):
                    continue
                pl2 = dict(placed)
                pl2[v] = pv
                Cva = wedge2(hat(pv), hat(placed[a]))
                Cvb = wedge2(hat(pv), hat(placed[b]))
                mat = [[dot(u, Cva) for u in U], [dot(u, Cvb) for u in U]]
                pred = (rank(mat) == 2)
                obs = (rank_at_V(edges, pl2, VG)[0] == tgtG)
                agree += (pred == obs)
            if n_ok >= nseeds:
                break
        total = n_ok * nplace
        print(f"  {name} split v={v}: per-placement biconditional "
              f"{agree}/{total} (s0={s0})")
        assert agree == total
    print("POINTWISE OK")


def hinge():
    """The ADVERSARIAL TEST for the coincident-hinge guard (F13: a guard
    observed only passing is untested).

    MUST-REJECT, and CONSTRUCTED rather than sampled on purpose -- it does not
    depend on a lucky seed and it survives any future change to the sampler.
    Take a clean `place_pencil_general` sample; pick a hub `h` with a
    single-hub interior `x` and another neighbour `u`; slide `pt(x)` onto the
    line through `pt(h)` and `pt(u)`.  The slide is LEGAL, because both
    endpoints lie in `Pi(h)` so the whole line does -- the same legality
    argument as `sigma.coplanar_chain_placement` and `outer.slide_x1_onto` --
    and the result is a bona fide pencil realization with `C(h,x) = C(h,u)`.

    THE PINNED COUNTER-FACT, asserted on the same witness: `star_span_ranks`
    returns 3 at EVERY vertex and all four `IsNondegPencilRealization`
    conjuncts hold.  This is what records *why* the documented guard was
    insufficient; without it the test would show only that the new guard
    fires, not that it fires where the old one did not.  Per (OC-7)'s
    mechanism the construction must keep a THIRD neighbour of `h` OFF the line
    `pt(h) pt(u)` -- that neighbour is exactly what lets `h`'s star still span
    its panel -- so the search below demands one.  A failure of the
    counter-fact is a bug in this test (it picked the wrong hub), not a
    finding about the guard.

    NEGATIVE CONTROL: the un-slid sample must PASS."""
    from pencil_escape import K4
    # `flanks` imports `repin`, so this sibling import is deferred to call
    # time.  `nondeg_conjuncts` is section 1's canonical four-conjunct check
    # and is NOT reimplemented here (section 2 rule 3).
    from flanks import nondeg_conjuncts

    print("== the coincident-hinge guard: adversarial test ==")
    SEED, SLIDE = 6, F(2)
    E, _hubs0, _chains, _allv = double_subdivide(K4())
    nb = neighbors(E)
    hubset = {v for v in sorted(nb, key=str) if len(nb[v]) >= 3}
    pl = place_pencil_general(E, random.Random(SEED))
    assert pl is not None, f"dbl-subdiv K4 seed {SEED} no longer samples"
    placed, pt, nrm, hubs, _nb = pl

    # --- negative control: the un-slid sample passes -----------------------
    ranks0 = star_span_ranks(E, placed)
    ok0, info0 = nondeg_conjuncts(E, placed)
    assert ok0, info0
    assert set(ranks0.values()) == {3}, ranks0
    assert coincident_hinges(E, placed) == [], coincident_hinges(E, placed)
    assert star_generic(E, placed)
    print(f"  negative control (dbl-subdiv K4, place_pencil_general seed "
          f"{SEED}): {len(ranks0)} vertices, star ranks all 3, all four "
          f"conjuncts hold, no coincident hinges -- guard PASSES")

    # --- the constructed must-reject witness -------------------------------
    pick = None
    for h in sorted(hubset, key=str):
        for x in sorted(nb[h], key=str):
            if x in hubset or len([t for t in nb[x] if t in hubset]) != 1:
                continue                  # `x` must be a SINGLE-hub interior
            for u in sorted(nb[h], key=str):
                if u == x:
                    continue
                q = [pt[h][i] + SLIDE * (placed[u][i] - pt[h][i])
                     for i in range(3)]
                cand = dict(placed)
                cand[x] = q
                Cu = wedge2(hat(pt[h]), hat(placed[u]))
                third = [w for w in sorted(nb[h], key=str) if w not in (x, u)
                         and rank([Cu, wedge2(hat(pt[h]),
                                              hat(placed[w]))]) != 1]
                if third and set(star_span_ranks(E, cand).values()) == {3}:
                    pick = (h, x, u, third[0], cand, q)
                    break
            if pick:
                break
        if pick:
            break
    assert pick is not None, \
        f"no eligible (hub, single-hub interior, third neighbour) at {SEED}"
    h, x, u, w3, slid, q = pick

    # legality of the slide: it is a genuine pencil realization
    assert dot(nrm[h], [q[i] - pt[h][i] for i in range(3)]) == 0, \
        "the slid point left the hub's panel"
    assert all(dot(nrm[hh], [slid[s][i] - pt[hh][i] for i in range(3)]) == 0
               for hh in hubs for s in nb[hh]), "pencil condition broken"
    assert all(slid[p] != slid[w] for (p, w) in E), \
        "coincident adjacent points"
    okS, infoS = nondeg_conjuncts(E, slid)
    assert okS, ("the slide broke a conjunct: not a bona fide realization",
                 infoS)

    # THE COUNTER-FACT: the documented guard does not fire
    ranksS = star_span_ranks(E, slid)
    assert set(ranksS.values()) == {3}, ranksS

    # the new guard rejects, and names exactly the coincident pair
    co = hinge_coincidences(E, slid, h, x)
    assert co == [u], (co, u)
    pair = (h, min((x, u), key=str), max((x, u), key=str))
    assert coincident_hinges(E, slid) == [pair], coincident_hinges(E, slid)
    assert not star_generic(E, slid)

    print(f"  witness: slide pt({x}), a single-hub interior of hub {h}, onto "
          f"line(pt({h}), pt({u})) at parameter {SLIDE}")
    print(f"    C({h},{x}) == C({h},{u}) projectively; still a bona fide "
          f"pencil realization (all four conjuncts hold)")
    print(f"    THE COUNTER-FACT: star_span_ranks == 3 at all {len(ranksS)} "
          f"vertices, so the DOCUMENTED guard does not fire -- hub {h}'s "
          f"third neighbour {w3} still spans its panel")
    print(f"    the new guard: hinge_coincidences({h}, {x}) = {co}; "
          f"coincident_hinges = {coincident_hinges(E, slid)}; "
          f"star_generic REJECTS")
    print("HINGE OK")


def main():
    if '--pointwise' in sys.argv:
        pointwise()
    elif '--hinge' in sys.argv:
        hinge()
    elif '--control' in sys.argv:
        control()
    elif '--theta' in sys.argv:
        theta()
    elif '--witness' in sys.argv:
        witness()
    elif '--stratum' in sys.argv:
        stratum()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
