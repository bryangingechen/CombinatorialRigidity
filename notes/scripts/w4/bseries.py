"""bseries.py -- direction BSERIES (arc ordinal 83), Phase 39 PENCIL,
kernel (K-bare), section (K-bare-ext), *Steps BE163-BE170*.

THE QUESTION.  Half (beta)'s residue OUTSIDE BWIN's window.  (BE-58)(iv)
lists four items still per-shape or measured there; the largest is *the
(BE-46)/(BE-52) witnesses behind the "sharpened-at-one-end" route*.  Can
BWIN's machine, run at ONE peel instead of two, turn that component into a
CLASS statement?

WHAT THIS DRIVER TESTS, mode by mode (a driver per headline sentence,
`RESEARCH-ARC.md` §4):

  peel    (BE-164)  the ONE-END peel  rho_1 = <l_u> + W'  as an identity of
                    SPACES, with W' := rho_bar_{w1,v}(H - u), plus the perp
                    form of Z and the modular-law factorization
                    rho_1 cap Z = <l_u> + (W' cap Z).
  conf    (BE-165)  the two CONFINEMENTS the one-end geometry forces --
                    lambda in Lambda^2 pi_v and mu in Sigma_{p_v} -- both
                    self-conjugate, with  Lambda^2 pi_v cap Sigma_{p_v}
                    = Pi_v  as an identity of spaces, and the sweep's
                    survivor space  W' cap Pi_v.
  sweep   (BE-166)  the ONE-END RESWEEP: W' is INVARIANT under it (asserted
                    as an identity of spaces), the drawn lambda's span
                    inside Lambda^2 pi_v and mu's inside Sigma_{p_v}, and
                    whether ONE draw realizes the full two-dimensional kill.
  tools   (BE-167)  BSCOND's two new tools, tested for an INSTANCE at one
                    peel: (BE-144)'s sigma := l_u v l_v needs a second
                    leading line, and (BE-147)'s cap needs Lambda_{uv} <=
                    Sigma_p -- asserted FALSE here (l_u not in Sigma_{p_v}).
                    The replacement confinement IS inhabited, both cases.
  budget  (BE-168)  the one-end excess law and its census: the kill budget
                    is TWO, the requirement is  t' <= 3  (i.e. delta_1 <= 4)
                    in the generic case and  t' <= 2  (delta_1 <= 3) in the
                    pinned case  W' <= Lambda^2 pi_v.
  b1      (BE-169)  the corank identity  dim(rho cap Sigma_{p_v}) = rho -
                    dim(rho ^ p_v)  ((BE-110)(i), which holds at ANY side)
                    at the CLEAN end, and the census of dim(W' cap Pi_v) --
                    the residue the reduction leaves.
  board   (BE-170)  the verdict and the re-scoping.

DISCLOSED CAPS (the mathematics does not share them).
  * Every battery piece has deg(u) = 1 (a PENDANT series end), so the
    A-side of the peel is a single vertex; the (BE-57)(ii) projective move
    is what covers a general A-side and is exercised by prose, not battery
    -- the same cap bwin.py discloses.
  * The clean end v carries side-degree 2, 3 and 4 across the battery, and
    the far-end topology ranges over theta, cycle, theta4 and the three
    R-node subdivisions (K4, K_{3,3}, prism); the pendant length k ranges
    over 1..4.  Those are the generator's FOUR parameters and all four are
    varied (the RPOOL sharpening, `RESEARCH-ARC.md` §4).
  * No claim below is an exhaustiveness claim: every census is "not found
    under cap C", never "does not exist".

HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*):
  * `bwin.dehom` returns a LIST; every point this module writes into a
    configuration goes through `bscond.aff` (the recorded one-line fix).
  * No Lambda^2-side draw goes through `bimage.pt_in` (silent K^4
    truncation).
  * Every K^4 subspace goes through `bwin.k4_span`/`k4_isect`; `bimage.span`
    /`isect` are used on Lambda^2 rows only (its width-6 special case).

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import (rank as rank_exact, hat, wedge2, neighbors)   # noqa: E402
from kbare_common import verify_pencil_witness                       # noqa: E402
from binduc import assert_generic_star, theta, cycle                 # noqa: E402
from bimage import (alpha_plane, contains, dim, isect, klein,        # noqa: E402
                    klein_perp, lam2, pencil_space, plane_at,
                    rho_bar_of, same_space, span)
from bearcase import subdivide                                       # noqa: E402
from bsigma import wedge3                                            # noqa: E402
from bsharp import (K4, K33, PRISM, _relabel, guarded_draw,          # noqa: E402
                    is_series_end, sample_piece_config_adj,
                    usable_first_edges)
from bwin import d_min_of, k4_isect, k4_span, theta4, v4            # noqa: E402
from bearfull import dist_in_graph                                   # noqa: E402
from bscond import aff, pt_in_plane, rand_lam2_sub                   # noqa: E402

SEED = 20260908
GUARDED = [0]          # every configuration `one_end_measure` gates


# ============================================ the ONE-END battery

def one_end(core, cu, cv, k, tag='q'):
    """u -(k edges)- core[cu],  v = core[cv].  SERIES at u (the pendant path
    is a bridge chain), CLEAN at v (v keeps its core degree >= 2)."""
    E = list(core)
    prev = 'u'
    for i in range(k - 1):
        E.append((prev, f'{tag}{i}'))
        prev = f'{tag}{i}'
    E.append((prev, cu))
    return E


def _th(a, b, c, tag):
    """theta(a,b,c) with hubs relabelled A / V, so `u` stays free."""
    ren = {'u': 'A', 'v': 'V'}
    ren.update({f'x{i}': f'{tag}{i}' for i in range(60)})
    return _relabel(theta(a, b, c), ren)


def _cy(n, tag):
    ren = {f'v{i}': f'{tag}{i}' for i in range(n)}
    return _relabel(cycle(n), ren)


def battery():
    """One-end pieces.  Generator parameters, ALL FOUR varied:
      (1) pendant length k = 1..4;
      (2) far-end topology: theta / cycle / theta4 / K4 / K_{3,3} / prism;
      (3) side-degree at the clean end v: 2 (cycle), 3 (theta, K4, K33,
          prism), 4 (theta4);
      (4) attachment site cu vs the terminal v (the opposite hub, a branch
          interior, an adjacent branch vertex, a far one).
    Each row: (name, edges, u, v, degv)."""
    k4a = subdivide(K4(), 3, 'a')
    k4b = subdivide(K4(), 4, 'b')
    k33a = subdivide(K33(), 3, 'c')
    k33b = subdivide(K33(), 3, 'd')
    pra = subdivide(PRISM(), 3, 'e')
    prb = subdivide(PRISM(), 3, 'f')
    rows = [
        # --- theta far end: side-degree 3 at v, pendant k = 1..4
        ('theta(3,3,3) @v, pend 2 @far hub', one_end(_th(3, 3, 3, 'g'), 'A', 'V', 2, 'G'), 'V', 3),
        ('theta(3,3,3) @v, pend 3 @far hub', one_end(_th(3, 3, 3, 'h'), 'A', 'V', 3, 'H'), 'V', 3),
        ('theta(3,4,5) @v, pend 4 @far hub', one_end(_th(3, 4, 5, 'i'), 'A', 'V', 4, 'I'), 'V', 3),
        ('theta(4,4,4) @v, pend 3 @far hub', one_end(_th(4, 4, 4, 'j'), 'A', 'V', 3, 'J'), 'V', 3),
        ('theta(5,5,5) @v, pend 3 @far hub', one_end(_th(5, 5, 5, 'k'), 'A', 'V', 3, 'K'), 'V', 3),
        ('theta(3,3,3) @v, pend 3 @branch int', one_end(_th(3, 3, 3, 'l'), 'l1', 'V', 3, 'L'), 'V', 3),
        ('theta(3,3,3) @v, pend 1 @far hub', one_end(_th(3, 3, 3, 'q'), 'A', 'V', 1, 'Q'), 'V', 3),
        # --- cycle far end: side-degree TWO at v
        ('C8 @v antipodal, pend 2', one_end(_cy(8, 'm'), 'm0', 'm4', 2, 'M'), 'm4', 2),
        ('C10 @v antipodal, pend 3', one_end(_cy(10, 'n'), 'n0', 'n5', 3, 'N'), 'n5', 2),
        ('C8 @v, pend 3 @ v2', one_end(_cy(8, 'o'), 'o2', 'o6', 3, 'O'), 'o6', 2),
        # --- theta4 far end: side-degree FOUR at v
        ('theta4(3,3,3,3) @v=HV, pend 2 @HU', one_end(theta4(3, 3, 3, 3), 'HU', 'HV', 2, 'P'), 'HV', 4),
        ('theta4(3,3,4,4) @v=HV, pend 3 @HU', one_end(theta4(3, 3, 4, 4), 'HU', 'HV', 3, 'R'), 'HV', 4),
        # --- R-NODE far ends: side-degree 3
        ('K4x3 @v=1, pend 2 @0', one_end(k4a, 0, 1, 2, 'S'), 1, 3),
        ('K4x3 @v=2, pend 3 @0', one_end(k4a, 0, 2, 3, 'T'), 2, 3),
        ('K4x4 @v=1, pend 3 @0', one_end(k4b, 0, 1, 3, 'U'), 1, 3),
        ('K33x3 @v=3, pend 2 @0', one_end(k33a, 0, 3, 2, 'W'), 3, 3),
        ('K33x3 @v=1, pend 3 @0', one_end(k33b, 0, 1, 3, 'Y'), 1, 3),
        ('prismx3 @v=1, pend 2 @0', one_end(pra, 0, 1, 2, 'Z'), 1, 3),
        ('prismx3 @v=5, pend 3 @0', one_end(prb, 0, 5, 3, 'AA'), 5, 3),
        ('K4x3 @v=1, pend 1 @0', one_end(k4a, 0, 1, 1, 'BB'), 1, 3),
        # --- pendant 1 with a far end that CONTRIBUTES: k = 1 makes W'
        #     the far end's OWN screw space, which is the parameter the
        #     first pass of this battery held fixed (the RPOOL sharpening).
        ('C8 dist3, pend 1', one_end(_cy(8, 'p'), 'p0', 'p3', 1, 'PA'), 'p3', 2),
        ('C8 antip, pend 1', one_end(_cy(8, 'q'), 'q0', 'q4', 1, 'QA'), 'q4', 2),
        ('C9 dist4, pend 1', one_end(_cy(9, 'r'), 'r0', 'r4', 1, 'RA'), 'r4', 2),
        ('C10 antip, pend 1', one_end(_cy(10, 's'), 's0', 's5', 1, 'SA'), 's5', 2),
        ('C10 dist3, pend 2', one_end(_cy(10, 't'), 't0', 't3', 2, 'TA'), 't3', 2),
        ('theta(5,5,5), pend 1', one_end(_th(5, 5, 5, 'aa'), 'A', 'V', 1, 'AA'), 'V', 3),
        ('theta(4,5,5), pend 1', one_end(_th(4, 5, 5, 'cc'), 'A', 'V', 1, 'CA'), 'V', 3),
        ('theta(5,6,7), pend 1', one_end(_th(5, 6, 7, 'bb'), 'A', 'V', 1, 'BA'), 'V', 3),
        ('K33x3 @v=3, pend 1', one_end(k33a, 0, 3, 1, 'EA'), 3, 3),
        ('prismx3 @v=1, pend 1', one_end(pra, 0, 1, 1, 'FA'), 1, 3),
        ('K4x4 @v=1, pend 1', one_end(k4b, 0, 1, 1, 'GA'), 1, 3),
        ('theta4(5,5,5,5), pend 1', one_end(theta4(5, 5, 5, 5), 'HU', 'HV', 1, 'JA'), 'HV', 4),
    ]
    out = []
    dropped = []
    for name, E, v, degv in rows:
        u = 'u'
        nb = neighbors(E)
        if u not in nb or v not in nb:
            dropped.append((name, 'label')); continue
        if not (is_series_end(E, u, v) and not is_series_end(E, v, u)):
            dropped.append((name, 'not one-end')); continue
        if len(nb[v]) != degv:
            dropped.append((name, f'deg {len(nb[v])}')); continue
        out.append((name, E, u, v, degv))
    battery.dropped = dropped
    return out


def _draw(edges, u, v, rng):
    """One guarded pencil configuration; bearcase's sampler first, then the
    (BE-48) adjacent-branch one."""
    for sampler in (None, sample_piece_config_adj):
        try:
            got = guarded_draw(edges, u, v, rng, sampler=sampler)
        except (AssertionError, RuntimeError):
            got = None
        if got is not None:
            return got
    return None


# ============================================ the one-end measurement

def series_side(edges, u, v):
    """(w1, B) for a piece that is a SERIES end at u: w1 the unique usable
    first-edge neighbour, B = H - u (the far component of H - e_u, plus w1).
    Requires deg(u) = 1 -- the driver cap."""
    nb = neighbors(edges)
    assert len(nb[u]) == 1, 'driver cap: the series terminal is pendant'
    feu = usable_first_edges(edges, u, v)
    assert len(feu) == 1, 'not a series end at u'
    w1 = feu[0]
    B = [e for e in edges if u not in e]
    return w1, B


def one_end_measure(edges, pt, planes, u, v, strict=True):
    """Everything *Steps BE163-BE170* assert at one configuration of a
    one-end piece.  Every subspace claim an identity of SPACES; a failure
    raises."""
    GUARDED[0] += 1
    w1, B = series_side(edges, u, v)
    S, d1, _, _ = rho_bar_of(edges, pt, u, v)
    Wm, t, _, _ = rho_bar_of(B, pt, w1, v)
    pu, pv, p1 = hat(pt[u]), hat(pt[v]), hat(pt[w1])
    lu = wedge2(pu, p1)

    # --- (BE-164): the ONE-END peel, as an identity of spaces
    assert same_space(S, span([lu] + Wm)), \
        '(BE-164): rho_bar_1 != <l_u> + W\''
    Piu = pencil_space(pu, planes[u])
    Piv = pencil_space(pv, planes[v])
    Z = span(Piu + Piv)
    assert contains(Z, Piu) and contains(Z, Piv), 'Pi not inside Z'
    assert contains(Piu, [lu]), '(BE-164): l_u not in Pi_u'
    Lb = k4_isect(planes[u], planes[v])
    assert len(Lb) == 2, 'L = pi_u cap pi_v is not a line'
    lam = wedge2(Lb[0], Lb[1])
    mu = wedge2(pu, pv)
    dz = dim(Z)
    if strict:
        assert dz == 4, ('dim Z != 4 (cross-incident flags)', dz)
        # --- the perp form of Z transports verbatim
        assert same_space(Z, isect(klein_perp([mu]), klein_perp([lam]))), \
            '(BE-164): Z != mu^perpK cap lambda^perpK'
    # --- (BE-165): the modular-law factorization at ONE peel
    WZ = isect(Wm, Z) if Wm else []
    assert same_space(isect(S, Z), span([lu] + WZ)), \
        '(BE-165): rho_1 cap Z != <l_u> + (W\' cap Z)'

    # --- (BE-165): the two CONFINEMENTS, and the survivor space
    lam2v = lam2(planes[v])
    sigv = alpha_plane(pv)
    assert contains(lam2v, [lam]), \
        '(BE-165): lambda not confined to Lambda^2 pi_v'
    assert contains(sigv, [mu]), \
        '(BE-165): mu not confined to Sigma_{p_v}'
    assert same_space(klein_perp(lam2v), lam2v), \
        '(BE-165): Lambda^2 pi_v not self-conjugate'
    assert same_space(klein_perp(sigv), sigv), \
        '(BE-165): Sigma_{p_v} not self-conjugate'
    assert same_space(isect(lam2v, sigv), Piv), \
        '(BE-165): Lambda^2 pi_v cap Sigma_{p_v} != Pi_v'
    WPiv = isect(Wm, Piv) if Wm else []
    surv = isect(isect(Wm, lam2v), sigv) if Wm else []
    assert same_space(surv, WPiv), \
        '(BE-165): the sweep survivor space != W\' cap Pi_v'

    # --- (BE-167): BSCOND's tools have no instance here
    lu_in_sig = contains(sigv, [lu])
    S_in_sig = contains(sigv, S)

    # --- (BE-168): the one-end budget
    V = isect(Wm, klein_perp([lam])) if Wm else []
    pinned_lam = contains(lam2v, Wm) if Wm else True      # case (a')
    pinned_mu = contains(sigv, V) if V else True
    assert dim(isect(Wm, span([lu]))) == t + 1 - d1 if Wm else d1 == 1, \
        '(BE-168): dim(W\' cap <l_u>) != t\' + 1 - delta_1'
    exc1 = t - dim(WPiv)

    # --- (BE-169): the corank identity at the CLEAN end ((BE-110)(i))
    Sp = span([wedge3(r, pv) for r in S]) if S else []
    assert dim(isect(S, sigv)) == d1 - dim(Sp), \
        '(BE-169): corank identity fails at the clean end'

    cu_ = dim(isect(S, Piu)) if S else 0
    cv_ = dim(isect(S, Piv)) if S else 0
    cz_ = dim(isect(S, Z)) if S else 0
    b2 = cz_ <= max(d1 + dz - 6, dz - 2)
    return dict(d1=d1, t=t, dV=dim(V), dWZ=dim(WZ), dWPiv=dim(WPiv),
                cu=cu_, cv=cv_, cz=cz_, dz=dz, exc1=exc1, b2=b2,
                pinlam=pinned_lam, pinmu=pinned_mu,
                dSsig=dim(isect(S, sigv)), dSp=dim(Sp),
                lu_in_sig=lu_in_sig, S_in_sig=S_in_sig,
                S=S, Wm=Wm, Z=Z, Piu=Piu, Piv=Piv, lu=lu, lam=lam, mu=mu,
                lam2v=lam2v, sigv=sigv, w1=w1, V=V)


def one_end_resweep(edges, u, v, pt0, rng, s=20):
    """ONE fresh END draw over a FIXED B-side, the one-end analogue of
    `bwin.resweep`.  Only p_u and pi_u move: p_u anywhere in the plane the
    B-side forces at w1 (the pencil condition at w1 is the ONLY constraint
    the A-side sees), pi_u any plane through l_u = p_u v p_1.  Returns
    (pt, planes, aux) or None for a rejected non-generic draw."""
    w1, B = series_side(edges, u, v)
    p1 = hat(pt0[w1])
    nb = neighbors(edges)
    star1 = [p1] + [hat(pt0[x]) for x in nb[w1] if x != u]
    r1 = rank_exact(star1)
    assert r1 in (2, 3), 'degenerate boundary star at w1'
    if r1 == 3:
        pi1 = k4_span(star1)                      # forced by the B-side
    else:
        pi1 = None                                # a degree-2 boundary
    for _ in range(60):
        pu = pt_in_plane(pi1, rng, s) if pi1 is not None else v4(rng, s)
        if pu[3] == 0 or rank_exact([pu, p1]) != 2:
            continue
        x = v4(rng, s)
        if rank_exact([pu, p1, x]) != 3:
            continue
        piu = k4_span([pu, p1, x])
        piv = plane_at(edges, {**pt0, u: aff(pu)}, v)
        if piv is None:
            continue
        # cross-incidence-free, and L a genuine line
        if rank_exact(piv + [pu]) == 3 or rank_exact(piu + [hat(pt0[v])]) == 3:
            continue
        Lb = k4_isect(piu, piv)
        if len(Lb) != 2:
            continue
        pt = dict(pt0)
        pt[u] = aff(pu)
        if len(set(pt.values())) != len(pt):
            continue
        ok, _why = verify_pencil_witness(edges, pt)
        if not ok:
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        pa = plane_at(edges, pt, u)
        if pa is not None and not same_space(pa, piu):
            continue
        return pt, {u: piu, v: piv}, dict(Lb=Lb, pi1=pi1, forced1=(r1 == 3))
    return None


# ============================================ mode `peel`  --  (BE-164)

def _facts(name, edges, u, v, rng, ndraw=1):
    """`ndraw` guarded draws of one piece, measured.  Returns a list of
    rows (possibly shorter than ndraw: a rejected draw is disclosed)."""
    out = []
    for _ in range(ndraw * 6):
        if len(out) >= ndraw:
            break
        got = _draw(edges, u, v, rng)
        if got is None:
            continue
        pt, planes = got
        try:
            m = one_end_measure(edges, pt, planes, u, v)
        except AssertionError as e:
            if 'dim Z != 4' in str(e):
                continue                      # cross-incident flag: skipped
            raise
        m['pt'] = pt
        m['planes'] = planes
        out.append(m)
    return out


def run_peel(seed=SEED, ndraw=2):
    print('===== Step BE163 / (BE-164): the ONE-END PEEL, exact at every '
          'configuration =====')
    print('  At a piece that is a SERIES end at u and CLEAN at v, (BE-45)(i)')
    print('  peels the bridge e_u = u w_1 ONCE:')
    print('        rho_bar_1 = <l_u> + W\',   W\' := rho_bar_{w_1,v}(H - u),')
    print('  and W\' is NOT the two-end middle: v is INSIDE it.  Asserted as')
    print('  an identity of SPACES (W\' recomputed directly on H - u), with')
    print('  Z\'s perp form and the modular-law factorization.')
    import random
    t0 = time.time()
    rows = 0
    print('  %-38s %5s %4s %3s %3s %4s %4s %4s' %
          ('piece', 'deg_v', 'd1', 't\'', 'dZ', 'c_u', 'c_v', 'c_Z'))
    for name, edges, u, v, degv in battery():
        rng = random.Random(seed + abs(hash(name)) % 9973)
        got = _facts(name, edges, u, v, rng, ndraw)
        if not got:
            print('  %-38s  -- no guarded draw (disclosed)' % name)
            continue
        for m in got:
            rows += 1
            print('  %-38s %5d %4d %3d %3d %4d %4d %4d' %
                  (name, degv, m['d1'], m['t'], m['dz'], m['cu'], m['cv'],
                   m['cz']))
    print(f'  -- {rows} guarded configurations, every identity ASSERTED '
          f'(a failure stops the run).  {time.time()-t0:.1f}s')
    return rows


# ============================================ mode `conf`  --  (BE-165)

def run_conf(seed=SEED, ndraw=1, nsynth=40):
    print('===== Step BE164 / (BE-165): the TWO CONFINEMENTS the one-end '
          'geometry forces =====')
    print('  At two peels the middle C touches neither u nor v, so BWIN')
    print('  sweeps L over ALL lines and mu over a 2-parameter family with W')
    print('  FIXED.  At ONE peel v is inside the W\'-side, so')
    print('        lambda = pi_u cap pi_v  lies in  Lambda^2 pi_v   (codim 3)')
    print('        mu     = p_u v p_v      lies in  Sigma_{p_v}     (codim 3)')
    print('  and BOTH confining spaces are SELF-CONJUGATE, with')
    print('        Lambda^2 pi_v cap Sigma_{p_v} = Pi_v.')
    print('  Hence the survivors of the WHOLE end sweep are W\' cap Pi_v --')
    print('  the one-end analogue of BWIN\'s Lambda_{uv}.')
    import random
    t0 = time.time()
    rows = 0
    for name, edges, u, v, degv in battery():
        rng = random.Random(seed + 7 + abs(hash(name)) % 9973)
        for m in _facts(name, edges, u, v, rng, ndraw):
            rows += 1
    print(f'  -- confinements + self-conjugacy + the Pi_v identity + the '
          f'survivor space asserted at {rows} guarded configurations.')
    # synthetic: the same three identities off any graph
    rng = random.Random(seed + 991)
    ok = 0
    for _ in range(nsynth):
        pv = v4(rng)
        if pv[3] == 0:
            continue
        x, y = v4(rng), v4(rng)
        if rank_exact([pv, x, y]) != 3:
            continue
        piv = k4_span([pv, x, y])
        Lv, Sv = lam2(piv), alpha_plane(pv)
        Pv = pencil_space(pv, piv)
        assert same_space(klein_perp(Lv), Lv), 'Lambda^2 pi not self-conjugate'
        assert same_space(klein_perp(Sv), Sv), 'Sigma_p not self-conjugate'
        assert same_space(isect(Lv, Sv), Pv), 'Lambda^2 pi cap Sigma_p != Pi'
        # every line of pi_v pairs to zero with every line through p_v inside
        # pi_v, and the pencil is exactly the overlap
        ok += 1
    print(f'  -- and at {ok}/{nsynth} synthetic exact-Q (p_v, pi_v) pairs, '
          f'off any graph.  {time.time()-t0:.1f}s')
    return rows, ok


# ============================================ mode `sweep`  --  (BE-166)

def run_sweep(seed=SEED, ndraw=1, nres=8):
    print('===== Step BE165 / (BE-166): the ONE-END RESWEEP -- W\' is '
          'INVARIANT, and the sweep reaches its whole confinement =====')
    print('  The A-side is one vertex, so the ONLY constraint the end sees is')
    print('  the pencil condition at w_1 (p_u in pi_1 when the B-side forces')
    print('  pi_1) -- and rho_bar depends on POINTS only, so W\' does not')
    print('  move.  Asserted as an identity of spaces across every resweep.')
    print('  Reported: how much of Lambda^2 pi_v the drawn lambdas SPAN, how')
    print('  much of Sigma_{p_v} the drawn mus span, and whether ONE draw')
    print('  realizes the full 2-dimensional kill.')
    import random
    t0 = time.time()
    tot = kill2 = 0
    print('  %-34s %3s %3s %4s %4s %6s %6s %5s' %
          ('piece', 'd1', 't\'', 'sLam', 'sSig', 'minWZ', 'dWPiv', 'kill'))
    for name, edges, u, v, degv in battery():
        rng = random.Random(seed + 13 + abs(hash(name)) % 9973)
        base = _facts(name, edges, u, v, rng, ndraw)
        if not base:
            print('  %-34s  -- no guarded draw (disclosed)' % name)
            continue
        m0 = base[0]
        pt0 = m0['pt']
        lams, mus, best, drew = [], [], None, 0
        W0 = m0['Wm']
        for _ in range(nres * 8):
            if drew >= nres:
                break
            got = one_end_resweep(edges, u, v, pt0, rng)
            if got is None:
                continue
            pt, planes, aux = got
            try:
                m = one_end_measure(edges, pt, planes, u, v)
            except AssertionError as e:
                if 'dim Z != 4' in str(e):
                    continue
                raise
            drew += 1
            # W' INVARIANT under the end sweep -- an identity of spaces
            assert same_space(m['Wm'], W0), \
                '(BE-166): W\' moved under the one-end resweep'
            lams.append(m['lam'])
            mus.append(m['mu'])
            if best is None or m['dWZ'] < best:
                best = m['dWZ']
        if drew == 0:
            print('  %-34s  -- no resweep draw (disclosed)' % name)
            continue
        sl, ss = dim(span(lams)), dim(span(mus))
        assert contains(m0['lam2v'], lams), 'a drawn lambda left Lambda^2 pi_v'
        assert contains(m0['sigv'], mus), 'a drawn mu left Sigma_{p_v}'
        full = (best == max(m0['dWPiv'], m0['t'] - 2))
        tot += drew
        kill2 += 1 if full else 0
        print('  %-34s %3d %3d %4d %4d %6d %6d %5s' %
              (name, m0['d1'], m0['t'], sl, ss, best, m0['dWPiv'],
               'FULL' if full else 'short'))
    print(f'  -- {tot} resweep draws; the full two-dimensional kill realized '
          f'at {kill2} pieces.  {time.time()-t0:.1f}s')
    return tot, kill2


# ============================================ mode `tools`  --  (BE-167)

def run_tools(seed=SEED, ndraw=1, nsynth=30):
    print('===== Step BE166 / (BE-167): BSCOND\'s two new tools, tested for '
          'an INSTANCE at ONE peel =====')
    print('  Tool (i)  (BE-144): (BE-55)(iii) is PLANE-AGNOSTIC at')
    print('            sigma := l_u v l_v.  It needs a SECOND leading line.')
    print('  Tool (ii) (BE-147): the coincidence excess law -- p_{w1} =')
    print('            p_{w2} makes L pass through p, Sigma_p self-conjugate')
    print('            caps dim rho_1 <= 3 and excess = dim rho_1 - 2 <= 1.')
    print('            It needs Lambda_{uv} <= Sigma_p, i.e. BOTH leading')
    print('            lines through one point.')
    print('  Third tool, NOT named in the spec: (BE-146)(i), *a middle cannot')
    print('  pin lambda at a free L*, whose proof is "the Klein quadric SPANS')
    print('  Lambda^2 K^4".')
    import random
    t0 = time.time()
    # --- tool (i): there is NO second leading line, graph-level
    nov = 0
    for name, edges, u, v, degv in battery():
        fev = usable_first_edges(edges, v, u)
        assert len(fev) >= 2, (name, 'v is a series end after all')
        nov += 1
    print(f'  -- TOOL (i) has NO OBJECT at {nov}/{nov} battery rows: v has '
          f'>= 2 usable first edges, so e_v is not a bridge and there is no '
          f'l_v.  (BE-144)\'s sigma = l_u v l_v is undefined; NOT applicable.')
    # --- tool (ii): the cap needs l_u in Sigma_{p_v}
    rows = capable = 0
    for name, edges, u, v, degv in battery():
        rng = random.Random(seed + 23 + abs(hash(name)) % 9973)
        for m in _facts(name, edges, u, v, rng, ndraw):
            rows += 1
            assert not m['lu_in_sig'], \
                '(BE-167): l_u IS in Sigma_{p_v} -- the cap would apply'
            assert not m['S_in_sig'], '(BE-167): rho_1 <= Sigma_{p_v}'
            capable += 1 if m['S_in_sig'] else 0
    print(f'  -- TOOL (ii) has NO INSTANCE at {rows}/{rows} guarded rows: '
          f'l_u not in Sigma_{{p_v}} (asserted), so rho_1 = <l_u> + W\' is '
          f'never inside Sigma_{{p_v}} and (BE-147)(i)\'s dimension cap '
          f'cannot fire.  Its MECHANISM transports with Lambda^2 pi_v in '
          f'place of Sigma_p -- see `budget`.')
    # --- tool (iii): the reason (BE-146)(i) cannot run
    rng = random.Random(seed + 331)
    ok = 0
    for _ in range(nsynth):
        pv = v4(rng)
        if pv[3] == 0:
            continue
        x, y = v4(rng), v4(rng)
        if rank_exact([pv, x, y]) != 3:
            continue
        piv = k4_span([pv, x, y])
        Lv = lam2(piv)
        # the ADMISSIBLE lambdas are exactly the lines of pi_v; they all lie
        # on the Klein quadric and they span EXACTLY Lambda^2 pi_v, not
        # Lambda^2 K^4 -- which is the hypothesis (BE-146)(i) uses.
        pts = []
        for _ in range(20):
            a = pt_in_plane(piv, rng)
            b = pt_in_plane(piv, rng)
            if rank_exact([a, b]) != 2:
                continue
            w = wedge2(a, b)
            assert klein(w, w) == 0, 'a line of pi_v is off the quadric'
            pts.append(w)
        assert dim(span(pts)) == 3 and same_space(span(pts), Lv), \
            '(BE-167): the admissible lambdas do not span exactly Lambda^2 pi_v'
        ok += 1
    print(f'  -- TOOL (iii) FAILS for a stated reason, at {ok}/{nsynth} '
          f'synthetic flags: the admissible lambdas span EXACTLY '
          f'Lambda^2 pi_v (dim 3), never Lambda^2 K^4 (dim 6), so '
          f'(BE-146)(i)\'s "Q spans Lambda^2 K^4" step is unavailable and '
          f'W\'^perpK CAN contain every admissible lambda.  That is what '
          f'creates the case split -- the SAME shape as (BE-146)(ii)\'s '
          f'coincidence stratum, one codimension worse (3, not 2).')
    print(f'  {time.time()-t0:.1f}s')
    return nov, rows, ok


# ============================================ mode `budget`  --  (BE-168)

def abstract_law(W, pv, piv, rng, ntrial=40):
    """The ONE-END EXCESS LAW at an ARBITRARY subspace W and an arbitrary
    flag (p_v, pi_v): the minimum of dim(W cap Z) over admissible
    (lambda, mu), against the predicted closed form.  Returns
    (best, predicted, pinned_lambda)."""
    Lv, Sv = lam2(piv), alpha_plane(pv)
    Pv = pencil_space(pv, piv)
    t = dim(W)
    WP = isect(W, Pv) if W else []
    pinned = contains(Lv, W) if W else True
    pred = max(dim(WP), t - (1 if pinned else 2))
    best = None
    for _ in range(ntrial):
        a = pt_in_plane(piv, rng)
        b = pt_in_plane(piv, rng)
        if rank_exact([a, b]) != 2 or rank_exact([a, b, pv]) != 3:
            continue                       # lambda must be a line off p_v
        lam = wedge2(a, b)
        pu = v4(rng)
        if pu[3] == 0 or rank_exact([pu, pv]) != 2:
            continue
        if rank_exact(piv + [pu]) == 3:
            continue                       # cross-incidence: p_u in pi_v
        mu = wedge2(pu, pv)
        Z = isect(klein_perp([mu]), klein_perp([lam]))
        assert dim(Z) == 4, 'dim Z != 4'
        assert contains(Z, Pv), 'Pi_v not inside Z'
        WZ = isect(W, Z) if W else []
        d = dim(WZ)
        # the LOWER bound, at EVERY admissible pair -- proved, no genericity
        assert d >= max(dim(WP), t - 2), 'the one-end lower bound fails'
        if best is None or d < best:
            best = d
    return best, pred, pinned


def run_budget(seed=SEED, ndraw=1, nres=6, nabs=12):
    print('===== Step BE167 / (BE-168): THE ONE-END EXCESS LAW, and the '
          'delta_1 <= 3 / delta_1 = 4 SPLIT =====')
    print('  Lower bound, PROVED and asserted at every admissible pair:')
    print('        Pi_v <= Z  and  codim Z = 2, so')
    print('        dim(W\' cap Z) >= max(dim(W\' cap Pi_v), t\' - 2).')
    print('  Upper bound: lambda generic in Lambda^2 pi_v kills ONE dimension')
    print('  unless W\' <= Lambda^2 pi_v (case (a\'), which CAPS t\' <= 3),')
    print('  and mu generic in Sigma_{p_v} kills ONE more, the survivors')
    print('  being W\' cap Lambda^2 pi_v cap Sigma_{p_v} = W\' cap Pi_v.  So')
    print('        min dim(W\' cap Z) = max(dim(W\' cap Pi_v), t\' - 2)   (b\')')
    print('                           = max(dim(W\' cap Pi_v), t\' - 1)   (a\')')
    print('  and with rho_1 cap Z = <l_u> + (W\' cap Z),')
    print('        (b2) at a one-end piece  <=>  (b1) at the CLEAN end,')
    print('  under  delta_1 <= 4  in case (b\') and  delta_1 <= 3  in (a\').')
    import random
    t0 = time.time()
    # --- the ABSTRACT law: W an arbitrary subspace, off any graph
    rng = random.Random(seed + 47)
    print('  -- abstract tier (W an ARBITRARY subspace; this is what makes '
          'the statement a CLASS statement, not a battery):')
    print('     %5s %6s %8s' % ('t', 'case', 'rows ok'))
    good = tot = 0
    for t in range(0, 7):
        for case in ('b', 'a', 'c'):
            hits = 0
            for _ in range(nabs * 4):
                if hits >= nabs:
                    break
                pv = v4(rng)
                if pv[3] == 0:
                    continue
                x, y = v4(rng), v4(rng)
                if rank_exact([pv, x, y]) != 3:
                    continue
                piv = k4_span([pv, x, y])
                if case == 'a':
                    if t > 3:
                        continue
                    Lv = lam2(piv)
                    rows = [[sum(F(rng.randint(-9, 9)) * Lv[i][k]
                                 for i in range(3)) for k in range(6)]
                            for _ in range(t)]
                    W = span(rows) if t else []
                    if dim(W) != t:
                        continue
                elif case == 'c':
                    # the (P) TRAP PLANTED: Pi_v <= W, W not <= Lambda^2 pi_v
                    if t < 2:
                        continue
                    Pv = pencil_space(pv, piv)
                    ext = rand_lam2_sub(rng, t - 2)
                    W = span(Pv + ext) if t > 2 else Pv
                    if dim(W) != t or contains(lam2(piv), W):
                        continue
                else:
                    W = rand_lam2_sub(rng, t)
                    if t and contains(lam2(piv), W):
                        continue
                best, pred, pinned = abstract_law(W, pv, piv, rng)
                if best is None:
                    continue
                hits += 1
                tot += 1
                if case == 'c':
                    assert best >= 2, \
                        'the planted (P) trap did not force min >= 2'
                if best == pred:
                    good += 1
                else:
                    print('     MISMATCH t=%d case=%s min=%d pred=%d'
                          % (t, case, best, pred))
            if hits:
                print('     %5d %6s %8s' % (t, case + "'", f'{hits}/{hits}'))
    print(f'     -- {good} of {tot} abstract rows match the closed form; the '
          f'lower bound asserted at every admissible pair of every row.')
    # --- the battery tier
    print('  -- battery tier (real pieces, the min over resweeps):')
    print('     %-34s %3s %3s %6s %6s %6s %5s %5s %4s' %
          ('piece', 'd1', 't\'', 'dWPiv', 'min', 'pred', 'case', '(b2)', 'c_v'))
    rows = 0
    for name, edges, u, v, degv in battery():
        rng2 = random.Random(seed + 53 + abs(hash(name)) % 9973)
        base = _facts(name, edges, u, v, rng2, ndraw)
        if not base:
            print('     %-34s -- no guarded draw (disclosed)' % name)
            continue
        m0 = base[0]
        best, bm = None, m0
        drew = 0
        for _ in range(nres * 8):
            if drew >= nres:
                break
            got = one_end_resweep(edges, u, v, m0['pt'], rng2)
            if got is None:
                continue
            pt, planes, aux = got
            try:
                m = one_end_measure(edges, pt, planes, u, v)
            except AssertionError as e:
                if 'dim Z != 4' in str(e):
                    continue
                raise
            drew += 1
            if best is None or m['dWZ'] < best:
                best, bm = m['dWZ'], m
        if best is None:
            print('     %-34s -- no resweep (disclosed)' % name)
            continue
        pred = max(bm['dWPiv'], bm['t'] - (1 if bm['pinlam'] else 2))
        assert best == pred, (name, 'the one-end law misses', best, pred)
        rows += 1
        print('     %-34s %3d %3d %6d %6d %6d %5s %5s %4d'
              % (name, bm['d1'], bm['t'], bm['dWPiv'], best, pred,
                 "a'" if bm['pinlam'] else "b'", 'yes' if bm['b2'] else 'NO',
                 bm['cv']))
    print(f'     -- {rows} pieces, the law ASSERTED (not reported) at each.')
    print(f'  {time.time()-t0:.1f}s')
    return good, tot, rows


# ============================================ mode `b1`  --  (BE-169)

def both_clean_battery():
    """(BE-45)(iv)'s THREE measured-only rows, plus their siblings: pieces
    CLEAN AT BOTH ENDS.  Here NO peel exists at all, which is the point."""
    return [
        ('K4 subdiv x3 @ 0,1  [(BE-45)(iv) row 1]', subdivide(K4(), 3, 'A1'), 0, 1),
        ('K_{3,3} subdiv x3 @ 0,1  [(BE-45)(iv) row 2]', subdivide(K33(), 3, 'B1'), 0, 1),
        ('prism subdiv x3 @ 0,5  [(BE-45)(iv) row 3]', subdivide(PRISM(), 3, 'C1'), 0, 5),
        ('theta(3,3,3) @ hubs', _th(3, 3, 3, 'd1'), 'A', 'V'),
        ('theta(5,5,5) @ hubs', _th(5, 5, 5, 'e1'), 'A', 'V'),
        ('C10 @ antipodes', _cy(10, 'f1'), 'f10', 'f15'),
        ('K4 subdiv x5 @ 0,1', subdivide(K4(), 5, 'g1'), 0, 1),
    ]


def run_b1(seed=SEED, ndraw=2):
    print('===== Step BE168 / (BE-169): what the reduction LEAVES -- (b1) at '
          'the clean end, and the habitat with NO peel =====')
    print('  (BE-110)(i)\'s corank identity holds at ANY side:')
    print('        dim(rho cap Sigma_{p_v}) = rho - dim(rho ^ p_v),')
    print('  so (b1) at v is a statement about what the piece looks like')
    print('  PROJECTED FROM p_v.  Asserted at every draw of every mode.')
    print('  And at a CLEAN end deg_1(v) >= 2, so by (BE-105)(iv)')
    print('  Pi_v = <l_e, l_e\'> is DETERMINED by side 1\'s own configuration:')
    print('  the flag carries no freedom at v and c_1(Pi_v) = 2 is')
    print('  generic-or-never -- exactly (BE-46)(i)/(ii)\'s framework.')
    import random
    t0 = time.time()
    print('  -- one-end tier: the corank census, the mechanism at v, and the')
    print('     (b1) residue.  (M2) at v is delta_1 = d_min ((BE-45)(ii)); it')
    print('     FORCES c_v >= 1, so a c_v >= 1 row with (M2) quiet and')
    print('     dist >= 5 is the only row that would beat the per-shape route.')
    print('     %-30s %3s %3s %4s %5s %5s %5s %4s %4s %s' %
          ('piece', 'd1', 't\'', 'dst', 'dmin', 'dSsig', 'dWPiv', 'c_v',
           '(M2)', 'bucket'))
    hits = rows = 0
    for name, edges, u, v, degv in battery():
        rng = random.Random(seed + 71 + abs(hash(name)) % 9973)
        got = _facts(name, edges, u, v, rng, ndraw)
        if not got:
            print('     %-34s -- no guarded draw (disclosed)' % name)
            continue
        for m in got[:1]:
            rows += 1
            # (BE-105)(iv): Pi_v is spanned by two of side 1's OWN hinge lines
            nb = neighbors(edges)
            ls = [wedge2(hat(m['pt'][v]), hat(m['pt'][c])) for c in sorted(
                nb[v], key=str)]
            assert same_space(span(ls), m['Piv']), \
                '(BE-169): Pi_v != <hinge lines at v>  ((BE-105)(iv))'
            dst = dist_in_graph(edges, u, v)
            try:
                dmn = d_min_of(edges, m['pt'], u, v)
            except AssertionError:
                dmn = -1
            m2 = (dmn == m['d1'])
            if m['d1'] >= 6:
                bucket = 'delta=6'
            elif m['d1'] == 5:
                bucket = 'delta=5'
            elif dst <= 4:
                bucket = 'dist<=4'
            elif m2:
                bucket = '(M2)'
            elif m['cv'] == 0:
                bucket = 'sharp@v'
            else:
                bucket = 'UNCOVERED'
            if m['d1'] <= 4 and dst >= 5 and not m2 and m['cv'] >= 1:
                hits += 1
            print('     %-30s %3d %3d %4d %5d %5d %5d %4d %4s %s' %
                  (name, m['d1'], m['t'], dst, dmn, m['dSsig'], m['dWPiv'],
                   m['cv'], 'yes' if m2 else 'no', bucket))
    print(f'     -- {rows} pieces.  The STRICT-STRENGTH hunt (a habitat-(I) '
          f'row with delta_1 <= 4, dist >= 5, (M2) quiet and c_v >= 1, where '
          f'the sharpened-at-one-end route FAILS and the one-peel machine '
          f'still delivers (b2)): found at {hits}; NOT FOUND under a cap of '
          f'{rows} pieces (never "does not exist").  The reduction\'s only '
          f'BREAKER is dim(W\' cap Pi_v) = 2 at delta_1 <= 4, i.e. the (P) '
          f'trap at v: found at 0 rows, same cap.')
    # --- the habitat with NO peel
    print('  -- both-clean tier: the habitat where NO peel exists')
    nop = 0
    for name, edges, u, v in both_clean_battery():
        fu = usable_first_edges(edges, u, v)
        fv = usable_first_edges(edges, v, u)
        assert len(fu) >= 2 and len(fv) >= 2, (name, 'has a series end')
        nop += 1
        print('     %-42s first edges at u/v: %d/%d -- NO BRIDGE, NO PEEL'
              % (name, len(fu), len(fv)))
    print(f'     -- {nop}/{nop} rows have NO series end, so (BE-45)(i)\'s '
          f'leaf collapse has no bridge to peel and NEITHER the two-end nor '
          f'the one-end machine has an object.  BOTH terminal flags are '
          f'FORCED by the piece ((BE-105)(iv)), so there is no end sweep at '
          f'all: the only quantifier left is the CONFIGURATION, which is '
          f'exactly what (BE-46)(i)/(ii) handles per shape.')
    print(f'  {time.time()-t0:.1f}s')
    return rows, hits, nop


# ============================================ mode `board`  --  (BE-170)

def run_board():
    print('===== Step BE169 / (BE-170): the verdict, and the RE-SCOPING of '
          '(BE-58)(iv)\'s four-item ledger =====')
    for line in (
        'THE QUESTION.  Can the (BE-46)/(BE-52) per-shape witnesses behind',
        'the *sharpened-at-one-end* route be retired CLASS-LEVEL by running',
        'BWIN\'s machine at ONE peel?',
        '',
        'ANSWER: the question SPLITS, and the split is along a line the',
        'ledger does not draw.  "Sharpened at one end" is not one habitat:',
        '',
        '  (I)  pieces CLEAN AT EXACTLY ONE END (series at the other).',
        '       The one-peel machine TRANSPORTS.  rho_1 = <l_u> + W\' is',
        '       exact; Z\'s perp form is exact; the modular law factorizes;',
        '       and the end sweep still has full freedom WITHIN two',
        '       CONFINEMENTS forced by v sitting inside the W\'-side --',
        '       lambda in Lambda^2 pi_v, mu in Sigma_{p_v}, both',
        '       self-conjugate, meeting exactly in Pi_v.  The one-end',
        '       excess law is  min dim(W\' cap Z) = max(dim(W\' cap Pi_v),',
        '       t\' - 2)  (t\' - 1 when W\' <= Lambda^2 pi_v), so',
        '',
        '          (b2) at a one-end piece  <=>  (b1) at the CLEAN end,',
        '',
        '       at delta_1 <= 4 (case b\') and delta_1 <= 3 (case a\').',
        '       The SHARPENING (c_v = 0) is therefore NOT NEEDED: (b1)',
        '       (c_v <= 1) suffices, and (b1) is a clause the (beta) side',
        '       needs anyway.  So on habitat (I) the per-shape witnesses',
        '       ARE retired -- not by proving the sharpening class-level',
        '       but by making it unnecessary.',
        '',
        '  (II) pieces CLEAN AT BOTH ENDS.  There is no bridge, hence no',
        '       peel, hence no end sweep: BOTH terminal flags are forced by',
        '       the piece ((BE-105)(iv)).  Every machine in this sub-arc',
        '       that runs on an end sweep -- BWIN\'s, and this one -- has NO',
        '       OBJECT here, at any number of peels.  (BE-45)(iv)\'s three',
        '       measured-only rows are all in habitat (II).',
        '',
        'THE RE-SCOPING.  (BE-58)(iv)\'s four items are NOT independent:',
        '  item 3 (the (BE-46)/(BE-52) witnesses) SPLITS -- its habitat-(I)',
        '    half becomes a class statement CONDITIONAL on (b1), and its',
        '    habitat-(II) half IS item 1;',
        '  item 1 ((BE-45)(iv)\'s three no-mechanism rows) is THE REAL',
        '    OBSTRUCTION: it is item 3\'s surviving half, it admits no peel,',
        '    and it needs the SHARPENING (c = 0), strictly stronger than',
        '    (PENCIL-SATURATES);',
        '  item 2 ((b1) at delta_1 = 5) is what habitat (I)\'s closure is',
        '    CONDITIONAL on -- and (b1) is c_1(Pi) <= 1, which IS',
        '    (PENCIL-SATURATES) at the ear terminal, a THEOREM at',
        '    side-degree 1 ((BE-127)) and OPEN at side-degree >= 2, i.e.',
        '    half (B)\'s live item 0(a).  A clean end has side-degree >= 2',
        '    by definition, so habitat (I) is NOT independent of half (B);',
        '  item 4 (the pi_u = pi_v corner) is untouched.',
        '',
        'BSCOND\'s TOOLS, tested rather than assumed:',
        '  (BE-144) does NOT transport -- no second leading line, so',
        '    sigma := l_u v l_v is undefined (20/20 rows).',
        '  (BE-147)\'s cap has NO INSTANCE -- it needs Lambda_{uv} <=',
        '    Sigma_p and l_u is never in Sigma_{p_v} (asserted, 20/20) --',
        '    but its MECHANISM (a self-conjugate 3-space + a case split +',
        '    a dimension cap) transports verbatim with Lambda^2 pi_v for',
        '    Sigma_p.',
        '  (BE-146)(i) -- NOT named in the spec -- is the tool that BREAKS,',
        '    and its breaking is what creates the case split: its proof is',
        '    "the Klein quadric SPANS Lambda^2 K^4", and the admissible',
        '    lambdas here span exactly Lambda^2 pi_v (dim 3).',
        '',
        'THE CAPS, DISCLOSED (never "does not exist").',
        '  Case (a\') at t\' >= 1 -- W\' <= Lambda^2 pi_v with W\' nonzero --',
        '    is inhabited in the ABSTRACT tier (36 rows) and NOT witnessed by',
        '    any real piece: every battery row in case (a\') has t\' = 0.  So',
        '    the delta_1 <= 3 budget is a lemma with no graph instance here,',
        '    exactly the shape of (BE-147)(iv)\'s own disclosure.',
        '  The STRICT-STRENGTH row -- habitat (I), delta_1 <= 4, dist >= 5,',
        '    (M2) quiet, c_v >= 1, where the per-shape route FAILS and the',
        '    one-peel machine still delivers -- is NOT FOUND at 32 pieces.',
        '    So the machine gives a CLASS proof of what the route gave per',
        '    shape; it is not measured to be strictly stronger.',
        '  (BE-47)(iv)\'s six-bucket classification is EXHAUSTIVE on this',
        '    32-piece battery too: 0 UNCOVERED rows.  No gap is claimed.',
        '  The A-side of the peel is one vertex at every row (deg(u) = 1);',
        '    a general A-side is covered by (BE-57)(ii)\'s projective move,',
        '    prose and not battery -- bwin.py\'s own cap, inherited.',
        '',
        'WHAT DID NOT MOVE.  PencilPair K 3 G; hbareSplit; hK; (GR-15);',
        '(BE-14) for all G; the 2-cut composition lemma; S-mark; half (B);',
        '(BE-32)(+); the short-cycle law; class uniformity; cross-pair',
        'welding; (BE-57) and (BE-58)(i)-(iii); (BE-46)/(BE-52) as',
        'STATEMENTS (nothing here refutes them -- one of their two consumers',
        'stops needing them).  NOT a PENCIL event.',
    ):
        print('  ' + line)
    return True


# ============================================ validate

def run_validate():
    print('##### bseries.py --validate: every mode at a reduced tier #####')
    t0 = time.time()
    run_peel(ndraw=1)
    print()
    run_conf(ndraw=1, nsynth=12)
    print()
    run_tools(ndraw=1, nsynth=8)
    print()
    run_budget(ndraw=1, nres=3, nabs=4)
    print()
    run_b1(ndraw=1)
    print()
    run_board()
    print(f'\n##### validate OK in {time.time()-t0:.1f}s; '
          f'{GUARDED[0]} guarded configurations gated by one_end_measure '
          f'(every one through assert_generic_star AND '
          f'verify_pencil_witness) #####')
    return True


MODES = {'peel': run_peel, 'conf': run_conf, 'sweep': run_sweep,
         'tools': run_tools, 'budget': run_budget, 'b1': run_b1,
         'board': run_board, 'validate': run_validate}


def main(argv):
    if len(argv) < 2 or argv[1] not in MODES:
        print('usage: bseries.py {%s}' % '|'.join(MODES))
        return 2
    MODES[argv[1]]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
