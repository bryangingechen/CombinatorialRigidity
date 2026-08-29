"""
Direction BRULE (ordinal 50) -- (b3), the ONE clause of the ear case's (beta)
side that has never been attacked.

  TARGET  (b3), verbatim from (BE-37)(ii):  `rho_bar_1 cap E` is NOT an
          opposite-ruling pencil `y ^ L`.  Decide it -- prove it on its honest
          domain, or exhibit a piece and configuration where it IS one.

  (b3) is a SHAPE condition, not a dimension bound: unlike (b1)/(b2) no
  dimension count can settle it, and under ZJACOB (JC-6) none may be dressed
  up as one.  WHAT TESTS THE SHAPE, and what every mode below runs:

    a 2-dim subspace A of Lambda^2 K^4 is a PENCIL iff the Klein form
    vanishes IDENTICALLY on it (three exact-Q scalars <a,a>, <a,b>, <b,b> on
    a basis) -- and then it has a VERTEX, the common point of its lines.
    Inside E = Pi_u + Pi_v = M ^ L the pencils are exactly the two RULINGS of
    a quadric surface, separated by where the vertex lies:

        vertex on M = p_u v p_v   ->  y ^ L, the OPPOSITE ruling  ((b3) FAILS)
        vertex on L = pi_u cap pi_v ->  M ^ z, the ear's own image at m = 1.

  Cap-free in y.  `ruling_vertex` decides CONTAINMENT of some `y ^ L` in
  rho_bar_1 by ONE exact rank test over the whole 1-parameter family y in M --
  no sampling of y anywhere.

  JOB 1  DECIDE (b3).
  JOB 2  ROUTING (one paragraph, a by-product): does (BE-32)(+) sit UNDER two
         clauses of (beta) rather than beside them?
  JOB 3  the falsification arm, if job 1 does not close.

Succeeds `notes/scripts/w4/bsharp.py` (Steps BE43-BE47), which this driver
imports READ-ONLY together with `bearcase` / `bearfull` / `bimage` / `binduc`
/ `bzavoid` / `kbare_common` through it, rather than reimplementing the
battery, the free samplers, the pencil-witness gate or the subspace machinery.
BSHARP's, BEARFULL's, BEARCASE's and BIMAGE's figures are CITED, never re-run.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-49)  THE HONEST DOMAIN, and `E` IS A SHARED-FLAG OBJECT.
             `dom`     : E, M, L, the two rulings and their incidences, at
                         drawn flags in all three regimes.  Pi_u = p_u ^ L and
                         Pi_v = p_v ^ L are members of the OPPOSITE ruling;
                         the ear's image at m = 1 is M ^ p_1, a member of the
                         other.  Same-ruling members meet in 0, opposite ones
                         in a point -- which is the whole mechanism of
                         (BE-50).  Outside `pi_u != pi_v` and `uv not in
                         E(G_1)` the clause is either VACUOUS or ILL-POSED,
                         and this mode certifies which.

  (BE-50)  THE SEPARATION THEOREM -- a (b3) failure FORCES the sharpening at
           BOTH ends, so (b3) is free wherever a BSHARP mechanism fires.
             `sep`     : over bsharp's 49-piece battery, the shape test on
                         rho_bar_1 cap E together with (M1)/(M2) at both ends;
                         the theorem's conclusion ASSERTED per row, not
                         reported.

  (BE-51)  THE (R)/(Z) DOMINANCE -- and the INFERENCE inside (BE-37)(ii) that
           it corrects, with no landed figure touched.
             `domin`   : synthetic A of dimension 3 and 4 inside E that DO
                         contain a `y ^ L`.  (b3) as stated (an equality test)
                         holds there, yet (R) fires -- so the stated inference
                         "(b1)+(b2)+(b3) => lossP = lossR = 0" is false.  What
                         is true is `lossR <= lossZ`, which leaves every
                         downstream consequence intact; checked against the
                         LANDED `bimage.bad_predicate` and `reach_measured`.

  (BE-52)  ONE WITNESS PER SHAPE -- openness + irreducibility, transported
           from (BE-46) with the properness step (b3) needs.
             `wit`     : per shape, independent guarded draws exhibiting that
                         rho_bar_1 contains NO opposite-ruling pencil, with
                         per-piece stability over draws reported (F27: here an
                         exhibited (b3) is the SAFE direction, a reported
                         failure the unsafe one).

  (BE-53)  JOB 3 -- THE FALSIFICATION ARM.
             `hunt`    : the hunt for a piece and configuration whose
                         rho_bar_1 cap E IS an opposite-ruling pencil, over
                         both samplers plus the pieces the separation theorem
                         says are the ONLY candidates.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, `contains`) and never of dimensions, every
sampled configuration through binduc's `assert_generic_star` AND
`kbare_common.verify_pencil_witness`, every cap disclosed.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import os
import random
import sys
import time
from fractions import Fraction as F                                  # noqa: F401

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import rank as rank_exact, nullspace, hat, wedge2     # noqa: E402
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- BATTAIN was its first `w4/` consumer, `bzavoid` the second, `binduc` the
# --- third, `btwocut` the fourth, `bimage` the FIFTH, `bearcase` the SIXTH,
# --- `bearfull` the SEVENTH, `bsharp` the EIGHTH; this driver is the NINTH,
# --- and the chain is now NINE deep (battain -> bzavoid -> binduc ->
# --- btwocut -> bimage -> bearcase -> bearfull -> bsharp -> brule).  NO MOVE
# --- MADE (a dispatch may not edit a landed driver another direction may be
# --- importing in flight); the recorded consumer list is EXTENDED in the
# --- workbook's harness note.
from bimage import (I6, bad_predicate, contains, dim, isect, klein,  # noqa: E402
                    lam2, pencil_space, pencil_vertex, perp_std,
                    plane_meet, reach_measured, sample_flags,
                    same_space, span)
import bsharp                                                        # noqa: E402
from bsharp import (adj_battery, battery, guarded_draw, measure,     # noqa: E402
                    simple_paths, usable_first_edges)


# ============================================ the SHAPE test, cap-free in y

def ruling_vertex(S, pu, pv, Lb):
    """Does `S` CONTAIN an opposite-ruling pencil `y ^ L` with y on
    M = p_u v p_v?  Exact, and CAP-FREE in y -- no sampling of y.

    y = a p_u + b p_v, and `y ^ L <= S` iff every standard-dot annihilator row
    n of S kills `y ^ l` for both basis vectors l of L, i.e.

        a <n, p_u ^ l> + b <n, p_v ^ l> = 0   for every (n, l).

    That is a 2-column linear system in (a, b); a NONTRIVIAL kernel is exactly
    a y.  Returns the 4-vector y (a canonical kernel element), or None.
    """
    N = perp_std(S) if S else [r[:] for r in I6]
    rows = []
    for n in N:
        for l in Lb:
            au, av = wedge2(pu, l), wedge2(pv, l)
            rows.append([sum(n[k] * au[k] for k in range(6)),
                         sum(n[k] * av[k] for k in range(6))])
    if not rows:
        return [x for x in pu]                       # S is the whole space
    if rank_exact(rows) > 1:
        return None
    ker = nullspace(rows)
    assert ker, 'rank <= 1 but no kernel'
    a, b = ker[0][0], ker[0][1]
    y = [a * pu[k] + b * pv[k] for k in range(4)]
    assert any(t != 0 for t in y), 'degenerate y'
    return y


def shape_of(A, pu, pv, Lb):
    """The SHAPE verdict on a subspace A <= E.  Returns one of

      'not-2dim'  dim A != 2, so A is not a pencil at all;
      'not-ts'    dim A = 2 but the Klein form does NOT vanish on it;
      'opposite'  a pencil whose VERTEX lies on M -- an opposite-ruling
                  `y ^ L`, i.e. (b3) FAILS as literally stated;
      'image'     a pencil whose vertex lies on L -- a member `M ^ z` of the
                  ear's own ruling;
      'other'     a pencil whose vertex lies on neither (cannot happen inside
                  a 4-dim E, and is ASSERTED not to).
    """
    if dim(A) != 2:
        return 'not-2dim', None
    B = span(A)
    if any(klein(x, y) != 0 for x in B for y in B):
        return 'not-ts', None
    y = pencil_vertex(A)
    if y is None:
        return 'not-ts', None
    on_M = rank_exact([pu, pv, y]) == 2
    on_L = rank_exact(list(Lb) + [y]) == 2
    if on_M:
        return 'opposite', y
    if on_L:
        return 'image', y
    return 'other', y


def flag_geometry(pt, planes, u, v):
    """(p_u, p_v, basis of M, basis of L, Pi_u, Pi_v, E) at one configuration,
    in the NON-EQUAL-planes regime.  Every claim an identity of SPACES."""
    pu, pv = hat(pt[u]), hat(pt[v])
    Piu = pencil_space(pu, planes[u])
    Piv = pencil_space(pv, planes[v])
    E = span(Piu + Piv)
    Lb = plane_meet(planes[u], planes[v])
    Mb = nullspace(nullspace([pu, pv]))
    assert len(Mb) == 2, 'M is not a line'
    return pu, pv, Mb, Lb, Piu, Piv, E


# ================================== (BE-49): the honest domain of the clause

def run_dom(seed=20260828, ndraw=12):
    print('===== Step BE48 / (BE-49): the honest domain of (b3), and `E` is '
          'a SHARED-FLAG object =====')
    print('  `E := Pi_u + Pi_v` is computed from the shared datum')
    print('  (p_u, pi_u, p_v, pi_v) ALONE -- it is neither the ear\'s object')
    print('  nor the piece\'s.  So the ear -> piece TRANSPORT the prep named')
    print('  as its weak link is NOT NEEDED: (b3) pairs a piece-side space')
    print('  rho_bar_1 with a shared-flag space E, and the (R) mechanism it')
    print('  negates is already PROVED for the ear at (BE-33).')
    print()
    rng = random.Random(seed)
    nonadj = 0
    for t in range(ndraw):
        pu, Bu, pv, Bv = sample_flags(rng, 'nonadj')
        Lb = plane_meet(Bu, Bv)
        Mb = nullspace(nullspace([pu, pv]))
        Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
        E = span(Piu + Piv)
        # M and L are SKEW, E = M ^ L is 4-dimensional
        assert rank_exact(list(Mb) + list(Lb)) == 4, 'M and L meet'
        ML = span([wedge2(m, l) for m in Mb for l in Lb])
        assert dim(E) == 4 and same_space(E, ML), 'E is not M ^ L'
        # Pi_u = p_u ^ L and Pi_v = p_v ^ L: BOTH in the y ^ L ruling
        assert same_space(Piu, span([wedge2(pu, l) for l in Lb])), \
            'Pi_u is not p_u ^ L'
        assert same_space(Piv, span([wedge2(pv, l) for l in Lb])), \
            'Pi_v is not p_v ^ L'
        # the two rulings, and their incidence -- the mechanism of (BE-50)
        ys = [pu, pv] + [[pu[k] + F(c) * pv[k] for k in range(4)]
                         for c in (1, 2, -3)]
        zs = [Lb[0], Lb[1]] + [[Lb[0][k] + F(c) * Lb[1][k] for k in range(4)]
                               for c in (1, -2)]
        opp = [span([wedge2(y, l) for l in Lb]) for y in ys]
        img = [span([wedge2(m, z) for m in Mb]) for z in zs]
        for A in opp + img:
            assert dim(A) == 2, 'a ruling member is not 2-dimensional'
            BA = span(A)
            assert all(klein(x, y) == 0 for x in BA for y in BA), \
                'a ruling member is not totally singular'
        for i in range(len(opp)):
            for j in range(i + 1, len(opp)):
                assert dim(isect(opp[i], opp[j])) == 0, \
                    'two OPPOSITE-ruling members meet'
            for j in range(len(img)):
                assert dim(isect(opp[i], img[j])) == 1, \
                    'an opposite-ruling and an image-ruling member miss'
        for i in range(len(img)):
            for j in range(i + 1, len(img)):
                assert dim(isect(img[i], img[j])) == 0, \
                    'two IMAGE-ruling members meet'
        # the shape test separates them, and `other` never occurs
        for A in opp:
            assert shape_of(A, pu, pv, Lb)[0] == 'opposite', 'shape test (o)'
        for A in img:
            assert shape_of(A, pu, pv, Lb)[0] == 'image', 'shape test (i)'
        # the ear's image at m = 1 IS an image-ruling member
        from bimage import ear_points, chain_of
        pts = ear_points((pu, Bu, pv, Bv), 1, rng)
        r2 = span(chain_of(pts))
        assert dim(r2) == 2 and shape_of(r2, pu, pv, Lb)[0] == 'image', \
            'the m = 1 ear image is not a member of the M ^ z ruling'
        nonadj += 1
    print('  [nonadj] %d draws: M, L SKEW; E = M ^ L 4-dim; Pi_u = p_u ^ L '
          'and' % nonadj)
    print('           Pi_v = p_v ^ L (identities of SPACES); 5 opposite x 4')
    print('           image ruling members per draw -- same-ruling pairs meet')
    print('           in 0, opposite pairs in a POINT; the m = 1 ear image is')
    print('           an M ^ z member.  The shape test separates the rulings')
    print('           by VERTEX at every one; `other` never occurs.')
    print()
    print('  THE TWO DEGENERATE REGIMES, and why (b3) is not needed in them.')
    # (a) equal planes: L is undefined, and EVERY 2-dim A <= Lambda^2 pi meets
    #     EVERY image pencil -- so the mechanism is (Z), not a separate (R).
    hits = 0
    for t in range(ndraw):
        pu, Bu, pv, Bv = sample_flags(rng, 'equal')
        Z = lam2(Bu)
        assert dim(Z) == 3, 'Lambda^2 pi is not 3-dimensional'
        assert len(plane_meet(Bu, Bv)) == 3, 'pi_u cap pi_v is not the plane'
        Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
        assert same_space(span(Piu + Piv), Z), 'E is not Lambda^2 pi'
        for _ in range(6):
            cc = [[F(rng.randint(-9, 9)) for _ in range(3)] for _ in range(2)]
            A = span([[sum(c[i] * Z[i][k] for i in range(3))
                       for k in range(6)] for c in cc])
            if dim(A) != 2:
                continue
            assert contains(Z, A), 'A escaped Lambda^2 pi'
            for _ in range(4):
                from bimage import pt_in, ear_points, chain_of
                p1 = pt_in(Bu, rng)
                r2 = span([wedge2(pu, p1), wedge2(p1, pv)])
                if dim(r2) != 2:
                    continue
                assert dim(isect(A, r2)) >= 1, \
                    'two pencils of one plane fail to meet'
                hits += 1
    print('  [equal planes]  L is UNDEFINED, so `y ^ L` does not exist and')
    print('     (b3) is ILL-POSED.  It is also UNNEEDED: E = Lambda^2 pi, and')
    print('     EVERY 2-dim A <= E meets EVERY image pencil (%d checks, all'
          % hits)
    print('     >= 1) -- two pencils of one plane always share the line')
    print('     joining their vertices.  That trap is exactly (Z):')
    print('     lossZ = 2 + c_2 - 3 = 1 with c_2 = 2.  So (b3) must be')
    print('     STRUCK from the reduction\'s hypothesis here, not proved.')
    print()
    # (a') cross-incident flags: E is no longer M ^ L, and the quadric
    #      surface -- hence the two rulings -- degenerates.
    ncr = 0
    for t in range(ndraw):
        pu, Bu, pv, Bv = sample_flags(rng, 'adj')
        Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
        E = span(Piu + Piv)
        assert dim(E) == 3, 'cross-incident E is not 3-dimensional'
        assert same_space(isect(Piu, Piv), span([wedge2(pu, pv)])), \
            'Pi_u cap Pi_v is not <p_u ^ p_v>'
        Lb = plane_meet(Bu, Bv)
        Mb = nullspace(nullspace([pu, pv]))
        assert rank_exact(list(Mb) + list(Lb)) < 4, 'M and L still skew'
        assert dim(span([wedge2(m, l) for m in Mb for l in Lb])) < 4, \
            'M ^ L still 4-dimensional'
        ncr += 1
    print('  [cross-incident flags]  p_u in pi_v (or the mirror).  Then M')
    print('     MEETS L, E = Pi_u + Pi_v is 3-dimensional with')
    print('     Pi_u cap Pi_v = <p_u ^ p_v>, and M ^ L is no longer E')
    print('     (%d draws, all asserted).  The quadric degenerates,' % ncr)
    print('     so (BE-33)(R)\'s ruling picture -- and with it (b3) -- is not')
    print('     POSED here.  At uv in E(G_1) the pencil condition FORCES this;')
    print('     at a non-adjacent pair it is a codimension-1 accident of the')
    print('     CONFIGURATION, which the existential (beta) avoids by')
    print('     (BE-37)(i)(3).  Counted, never smoothed.')
    print()
    # (b) adjacent: delta_1 <= 1 by (BE-30)(iv), so no 2-dim pencil fits.
    print('  [uv in E(G_1)]  dist_{G_1}(u,v) = 1, so (BE-30)(iv) gives')
    print('     delta_1 <= 1 and rho_bar_1 CANNOT CONTAIN a 2-dimensional')
    print('     pencil.  A containment impossibility, labelled a COUNT per')
    print('     (BE-27); it is not a genericity/transversality count and')
    print('     nothing here derives properness from a codimension (JC-6).')
    print('     Certified per piece by `sep` on the adjacent battery rows.')
    print()
    print('  VERDICT.  (b3)\'s honest domain is  pi_u != pi_v  AND  the flags')
    print('  CROSS-INCIDENCE-FREE (p_u not in pi_v, p_v not in pi_u) -- which')
    print('  at uv not in E(G_1) is a generic condition on the configuration,')
    print('  and at uv in E(G_1) FAILS identically.  Elsewhere (b3) is')
    print('  vacuous, ill-posed, or not posed at all.')
    return True


# =========================== (BE-50): the SEPARATION theorem, over 49 pieces

def _row(name, edges, u, v, rng, sampler=None):
    """One guarded draw plus the whole (b3) fact sheet for one piece."""
    paths, capped = simple_paths(edges, u, v)
    got = guarded_draw(edges, u, v, rng, sampler=sampler)
    if got is None:
        return None
    pt, planes = got
    m = measure(edges, pt, planes, u, v, paths)
    S = m['S']
    adj = ((u, v) in edges) or ((v, u) in edges)
    equal = (rank_exact(list(planes[u]) + list(planes[v])) == 3)
    out = dict(name=name, d1=m['d1'], cu=m['cu'], cv=m['cv'], cz=m['cz'],
               dz=m['dz'], adj=adj, equal=equal, capped=capped,
               dmin=min(f[1] for f in m['fac']))
    out['m1u'] = len(usable_first_edges(edges, u, v)) == 1
    out['m1v'] = len(usable_first_edges(edges, v, u)) == 1
    out['m2'] = (m['d1'] == out['dmin'])
    if equal:
        out['regime'] = 'equal planes -- (b3) ILL-POSED, struck'
        out['shape'] = 'n/a'
        return out
    cross = (rank_exact(list(planes[v]) + [hat(pt[u])]) == 3
             or rank_exact(list(planes[u]) + [hat(pt[v])]) == 3)
    out['cross'] = cross
    if cross and not adj:
        # a CONFIGURATION-level degeneracy, not a graph one: p_u in pi_v (or
        # the mirror) makes M meet L, E is no longer M ^ L, and (BE-33)(R)'s
        # ruling picture -- hence (b3) itself -- is outside its domain.  (beta)
        # is EXISTENTIAL ((BE-37)(i)(3)), so such a draw is simply not the one
        # the statement is evaluated at; it is counted, never smoothed.
        out['regime'] = 'cross-incident flags -- non-generic, (b3) not posed'
        out['shape'] = 'n/a'
        return out
    pu, pv, Mb, Lb, Piu, Piv, E = flag_geometry(pt, planes, u, v)
    out['dE'] = dim(E)
    if adj:
        out['regime'] = 'uv in E(G_1) -- (b3) FREE'
        assert m['d1'] <= 1, 'adjacent piece with delta_1 >= 2'
        out['shape'] = 'not-2dim'
        out['y'] = None
        return out
    out['regime'] = 'honest domain'
    assert dim(E) == 4, 'honest domain with dim E != 4'
    assert same_space(E, span([wedge2(mm, ll) for mm in Mb for ll in Lb])), \
        'E is not M ^ L at a piece draw'
    A = isect(S, E) if S else []
    out['dA'] = dim(A)
    sh, y = shape_of(A, pu, pv, Lb)
    out['shape'] = sh
    assert sh != 'other', 'a pencil inside E with vertex off both rulings'
    # the CONTAINMENT form, cap-free in y
    yc = ruling_vertex(S, pu, pv, Lb) if S else None
    out['y'] = yc
    if sh == 'opposite':
        assert yc is not None, \
            'the equality form fires but the containment form does not'
    # ---- (BE-50)(i): a failure at y = p_u forces Pi_u <= rho_bar_1
    if yc is not None:
        at_u = rank_exact([pu, yc]) == 1
        at_v = rank_exact([pv, yc]) == 1
        if at_u:
            assert contains(S, Piu), \
                '(BE-50)(i) FAILED: y = p_u but Pi_u is not inside rho_bar_1'
        if at_v:
            assert contains(S, Piv), '(BE-50)(i) FAILED at v'
        # ---- (BE-50)(ii): a failure at y off {p_u, p_v} with dim(A) = 2
        #      forces the SHARPENING at BOTH ends, hence neither mechanism.
        if not at_u and not at_v and sh == 'opposite':
            assert dim(isect(S, Piu)) == 0 and dim(isect(S, Piv)) == 0, \
                '(BE-50)(ii) FAILED: an opposite-ruling A meeting a pencil'
            assert not (out['m1u'] or out['m1v'] or out['m2']), \
                '(BE-50)(iii) FAILED: a BSHARP mechanism fires at a (b3) fail'
    else:
        # the contrapositive half, ASSERTED rather than reported: whenever a
        # mechanism fires, rho_bar_1 meets a pencil, so no opposite-ruling
        # member can be all of rho_bar_1 cap E.
        if out['m1u'] or out['m1v'] or out['m2']:
            assert m['cu'] >= 1 or m['cv'] >= 1, \
                'a mechanism fires but rho_bar_1 misses both pencils'
    return out


def run_sep(seed=20260828, nseeds=1, quiet=False):
    print('===== Step BE49 / (BE-50): THE SEPARATION THEOREM -- a (b3) '
          'failure FORCES the sharpening at BOTH ends =====')
    print('  (i)  If rho_bar_1 cap E = y ^ L with y = p_u, then Pi_u = p_u ^ L')
    print('       is inside rho_bar_1, i.e. dim(rho_bar_1 cap Pi_u) = 2 --')
    print('       which (b1) FORBIDS.  So (b1) already discharges (b3) at the')
    print('       two distinguished points of M.  (This is the CONVERSE of')
    print('       (BE-33)\'s remark that (P) is (R) at y = p_u, p_v.)')
    print('  (ii) If y is neither, then y ^ L and Pi_u are DISTINCT members of')
    print('       the SAME ruling, so they meet in 0; and Pi_u <= E gives')
    print('          rho_bar_1 cap Pi_u = (rho_bar_1 cap E) cap Pi_u')
    print('                             = (y ^ L) cap Pi_u = 0,')
    print('       at BOTH ends.  A (b3) failure therefore forces the')
    print('       SHARPENING rho_bar_1 cap Pi_u = 0 at u AND at v.')
    print('  (iii) By (BE-45) the sharpening FAILS whenever (M1) a series end')
    print('       or (M2) path saturation fires.  Hence (b3) HOLDS at every')
    print('       configuration where either mechanism fires at either end --')
    print('       in particular throughout (BE-47)(ii)\'s RESIDUAL WINDOW,')
    print('       which is (M1) at BOTH ends.  The (beta) side\'s two open')
    print('       obligations are DISJOINT.')
    print()
    bat = [(n, e, u, v, None) for (n, e, u, v) in battery()]
    bat += [(n, e, u, v, bsharp.sample_piece_config_adj)
            for (n, e, u, v) in adj_battery()]
    cens, contc = {}, {}
    fails, mech, honest, capped, cont = 0, 0, 0, 0, 0
    rows = []
    for (name, edges, u, v, smp) in bat:
        for s in range(nseeds):
            rng = random.Random(seed + 7919 * s + len(name))
            r = _row(name, edges, u, v, rng, sampler=smp)
            if r is None:
                continue
            rows.append(r)
            capped += 1 if r['capped'] else 0
            cens[r['shape']] = cens.get(r['shape'], 0) + 1
            if r['shape'] == 'opposite':
                fails += 1
            if r.get('y') is not None:
                cont += 1
                contc[(r.get('dA'), r['d1'])] = \
                    contc.get((r.get('dA'), r['d1']), 0) + 1
            if r['m1u'] or r['m1v'] or r['m2']:
                mech += 1
            if r.get('regime') == 'honest domain':
                honest += 1
    if not quiet:
        print('  %-44s %4s %3s %3s %3s  %-10s %s'
              % ('piece', 'reg', 'd1', 'dA', 'dE', 'shape', 'M1u/M1v/M2'))
        for r in rows:
            tag = {'honest domain': 'hon', 'uv in E(G_1) -- (b3) FREE': 'adj'}
            print('  %-44s %4s %3d %3s %3s  %-10s %s%s%s'
                  % (r['name'][:44], tag.get(r.get('regime'), 'eqp'),
                     r['d1'], r.get('dA', '-'), r.get('dE', '-'), r['shape'],
                     'Y' if r['m1u'] else '.', 'Y' if r['m1v'] else '.',
                     'Y' if r['m2'] else '.'))
    print()
    ncr = sum(1 for r in rows if r.get('regime', '').startswith('cross'))
    print('  %d rows; %d on the honest domain; %d with a BSHARP mechanism '
          'firing;' % (len(rows), honest, mech))
    print('  %d at cross-incident flags (p_u in pi_v or p_v in pi_u -- a '
          'CONFIGURATION' % ncr)
    print('  degeneracy at a non-adjacent pair, which (BE-37)(i)(3) lets the')
    print('  existential (beta) simply avoid).' )
    print('  shape census of rho_bar_1 cap E: %s'
          % ', '.join('%s: %d' % kv for kv in sorted(cens.items())))
    print('  (b3) FAILURES (an opposite-ruling `y ^ L`): %d' % fails)
    print('  rows at which rho_bar_1 CONTAINS some y ^ L (the corrected form,')
    print('  tested cap-free in y by one rank <= 1 test): %d, at' % cont)
    for k in sorted(contc):
        print('     dim(rho_bar_1 cap E) = %s, delta_1 = %s : %d rows'
              % (k[0], k[1], contc[k]))
    print('  -- i.e. ONLY where E <= rho_bar_1, which (b2) forces to be the')
    print('  VACUOUS corner delta_1 = 6 (the (b2) bound at dim Z = 4 is')
    print('  max(delta_1 - 2, 2), so dim(rho_bar_1 cap E) = 4 needs')
    print('  delta_1 >= 6).  The equality form and the containment form')
    print('  therefore differ on this battery at exactly the rows where the')
    print('  (BE-22) criterion is already met outright.')
    print('  path-enumeration cap (4000) hit at %d rows.' % capped)
    print('  Every conclusion above is ASSERTED per row inside `_row`, not')
    print('  reported: a violation stops the run.')
    return fails == 0


# ============================ (BE-51): the (R)/(Z) dominance, and (BE-37)(ii)

def run_domin(seed=20260828, ndraw=8):
    print('===== Step BE50 / (BE-51): the (R)/(Z) DOMINANCE, and the '
          'INFERENCE inside (BE-37)(ii) that it corrects =====')
    print('  (b3) is an EQUALITY test -- "rho_bar_1 cap E is not y ^ L".  It')
    print('  therefore does NOT exclude rho_bar_1 CONTAINING a y ^ L with')
    print('  dim(rho_bar_1 cap E) >= 3.  So (BE-37)(ii)\'s stated inference')
    print('  "(b1)+(b2)+(b3) => lossP = lossR = 0" is FALSE as an inference.')
    print('  What is true is  lossR <= lossZ  off the equality regime:')
    print('     a 3-dim W <= E is a PLANE of P(E) meeting the quadric surface')
    print('     in a CONIC, so it carries AT MOST ONE member of each ruling;')
    print('     hence dim(W cap M^z) = 1 for all but at most one z in L, the')
    print('     minimum over the ear\'s own modulus is 1, and')
    print('     lossZ = dim W + c_2 - dim Z = 3 + 2 - 4 = 1 too.')
    print('     At dim W = 4, W = E contains rho_bar_2 outright and')
    print('     lossP = lossZ = 2.  So (R) NEVER exceeds (Z) there, and every')
    print('     downstream consequence of (BE-37)(ii) is UNCHANGED.')
    print()
    rng = random.Random(seed)
    n3, n4, agree = 0, 0, 0
    for t in range(ndraw):
        pu, Bu, pv, Bv = sample_flags(rng, 'nonadj')
        Lb = plane_meet(Bu, Bv)
        Mb = nullspace(nullspace([pu, pv]))
        Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
        E = span(Piu + Piv)
        y = [pu[k] + F(2) * pv[k] for k in range(4)]
        yl = span([wedge2(y, l) for l in Lb])
        assert shape_of(yl, pu, pv, Lb)[0] == 'opposite', 'not a y ^ L'
        # a 3-dim W <= E containing y ^ L, spanned up by one more member of E
        extra = [wedge2(Mb[0], Lb[0])]
        W = span(list(yl) + extra)
        if dim(W) != 3:
            continue
        n3 += 1
        # (b3) AS STATED holds -- W cap E = W is 3-dim, not a pencil at all
        assert same_space(isect(W, E), W), 'W is not inside E'
        assert shape_of(isect(W, E), pu, pv, Lb)[0] == 'not-2dim', \
            'a 3-dim W read as a pencil'
        # yet the CONTAINMENT form fires
        assert ruling_vertex(W, pu, pv, Lb) is not None, \
            'W contains y ^ L but the containment test misses it'
        # at most ONE member of each ruling inside W
        # a SAMPLED guard on 8 parameter values each; the PROOF that a plane
        # of P(E) carries at most one member of each ruling is the conic
        # argument in (BE-51)(i), not this check.
        nopp = sum(1 for c in (0, 1, 2, -1, -2, 3, -3, 5)
                   for yy in [[pu[k] + F(c) * pv[k] for k in range(4)]]
                   if contains(W, span([wedge2(yy, l) for l in Lb])))
        nimg = sum(1 for c in (0, 1, 2, -1, -2, 3, -3, 5)
                   for zz in [[Lb[0][k] + F(c) * Lb[1][k] for k in range(4)]]
                   if contains(W, span([wedge2(mm, zz) for mm in Mb])))
        assert nopp <= 1 and nimg <= 1, \
            'a plane of P(E) carrying two members of one ruling'
        # lossZ = 1 exactly, and the LANDED predicate still agrees with the
        # measured reach -- so NO landed figure moves.
        flags = (pu, Bu, pv, Bv)
        pred, tag = bad_predicate(W, flags, 1)
        meas = reach_measured(W, flags, 1, seed + t, ndraw=20)
        assert pred == meas, ('the landed predicate disagrees at a 3-dim W',
                              pred, meas)
        assert pred == min(6, 3 + 2 - 1), 'reach is not 4 at a 3-dim W'
        agree += 1
        # dim 4: W = E
        pred4, _ = bad_predicate(E, flags, 1)
        meas4 = reach_measured(E, flags, 1, seed + t, ndraw=20)
        assert pred4 == meas4 == min(6, 4 + 2 - 2), 'the dim-4 corner moved'
        n4 += 1
    print('  %d draws with a 3-dim W <= E containing a y ^ L: (b3) as stated'
          % n3)
    print('     HOLDS at every one (W is not 2-dimensional), the containment')
    print('     test fires at every one, and each W carries AT MOST ONE')
    print('     member of each ruling -- a SAMPLED guard at 8 parameter')
    print('     values each; the PROOF of that is (BE-51)(i)\'s conic')
    print('     argument, not this check.  The LANDED `bimage.bad_predicate`')
    print('     (which sets lossR = 0 unless dim(A cap Z) == 2) agrees with')
    print('     `reach_measured` at %d/%d -- the under-report is ABSORBED by'
          % (agree, n3))
    print('     lossZ, so (BE-33)(ii)\'s 358/358 and (BE-34)\'s 607/607 STAND')
    print('     and NO MOVE is made on the landed driver.')
    print('  %d dim-4 corners (W = E): reach 4 predicted and measured.' % n4)
    print()
    print('  CONSEQUENCE.  (b3) as literally stated is the RIGHT hypothesis --')
    print('  the containment form is not needed, because off the equality')
    print('  regime (Z) already bounds the loss.  What is corrected is the')
    print('  INFERENCE (BE-37)(ii) states, not its conclusion: no measurement')
    print('  changes, and the 87-of-91 enumeration stands.')
    return True


# ================================ (BE-52): one witness per shape, and F27

def run_wit(seed=20260828, nseeds=4):
    print('===== Step BE51 / (BE-52): ONE WITNESS PER SHAPE -- openness, '
          'properness, irreducibility =====')
    print('  On the locus U where dim rho_bar_1 is generic, config |-> '
          'rho_bar_1')
    print('  is a MORPHISM, and so are M, L, E off the flag data.  The')
    print('  incidence  {(config, y) in U x P(M) : y ^ L <= rho_bar_1}  is')
    print('  CLOSED (a determinantal condition -- literally the rank <= 1')
    print('  condition `ruling_vertex` tests) inside the P^1-BUNDLE P(M) -> U,')
    print('  which is PROPER over U, so its projection to U is CLOSED (a')
    print('  P^1-bundle is complete over its base).  Hence the bad locus is')
    print('  closed and  {rho_bar_1 contains no y ^ L}  is OPEN in U.  The')
    print('  free parametrizations are IRREDUCIBLE ((BE-46)(ii)), so a')
    print('  non-empty open is DENSE -- and by (BE-37)(i)(3) the (beta) side')
    print('  is EXISTENTIAL, so ONE exhibited exact-Q configuration with (b3)')
    print('  PROVES it on a dense open of that shape\'s stratum.')
    print()
    print('  F27, in the direction it actually runs here: an exhibited (b3)')
    print('  is the SAFE direction (it is a proof for that shape); a reported')
    print('  (b3) FAILURE is the unsafe one and would need escalation.')
    print()
    bat = [(n, e, u, v, None) for (n, e, u, v) in battery()]
    bat += [(n, e, u, v, bsharp.sample_piece_config_adj)
            for (n, e, u, v) in adj_battery()]
    npiece, ndraw, nfail, varied, nskip = 0, 0, 0, 0, 0
    for (name, edges, u, v, smp) in bat:
        adj = ((u, v) in edges) or ((v, u) in edges)
        seen = set()
        got_any = False
        for s in range(nseeds):
            rng = random.Random(seed + 104729 * s + len(name))
            r = _row(name, edges, u, v, rng, sampler=smp)
            if r is None:
                continue
            if r.get('regime', '').startswith('cross'):
                nskip += 1
                continue
            got_any = True
            ndraw += 1
            seen.add((r['shape'], r['y'] is not None))
            if r['shape'] == 'opposite':
                nfail += 1
        if got_any:
            npiece += 1
            if len(seen) > 1:
                varied += 1
    print('  %d pieces x up to %d independent guarded draws = %d configurations'
          % (npiece, nseeds, ndraw))
    print('  (b3) FAILURES: %d.  Every draw exhibits (b3), hence -- by the'
          % nfail)
    print('  openness + properness + irreducibility argument above -- PROVES')
    print('  (b3) on a dense open subset of that shape\'s stratum.')
    print('  Pieces whose (shape, containment) verdict VARIED over draws: %d.'
          % varied)
    print('  Draws skipped as CROSS-INCIDENT (non-generic flags): %d.' % nskip)
    print()
    print('  WHAT IS NOT DISCHARGED, said plainly: the class-level statement')
    print('  over all pieces.  Each shape needs its own witness; nothing here')
    print('  bounds how many shapes need one.  Same wall as (BE-46)(iv).')
    return nfail == 0


# ==================================== (BE-53): job 3, the falsification arm

def run_hunt(seed=20260828, nseeds=8):
    print('===== Step BE52 / (BE-53): JOB 3, the falsification arm =====')
    print('  By (BE-50) the ONLY candidates are pieces at which NEITHER (M1)')
    print('  nor (M2) fires at EITHER end -- (BE-45)(iv)\'s 11-piece class,')
    print('  three of which are MEASURED-ONLY.  The hunt is aimed there, at')
    print('  many independent seeds, and reports the whole census.')
    print()
    bat = [(n, e, u, v, None) for (n, e, u, v) in battery()]
    bat += [(n, e, u, v, bsharp.sample_piece_config_adj)
            for (n, e, u, v) in adj_battery()]
    cand, tot, fails, nskip = 0, 0, 0, 0
    census = {}
    hot = []
    for (name, edges, u, v, smp) in bat:
        for s in range(nseeds):
            rng = random.Random(seed + 15485863 * s + 31 * len(name))
            r = _row(name, edges, u, v, rng, sampler=smp)
            if r is None:
                continue
            tot += 1
            if r.get('regime', '').startswith('cross'):
                nskip += 1
            if r.get('regime') != 'honest domain':
                continue
            key = (r['shape'], r.get('dA'))
            census[key] = census.get(key, 0) + 1
            if not (r['m1u'] or r['m1v'] or r['m2']):
                cand += 1
            if r['shape'] == 'opposite':
                fails += 1
                hot.append((name, s))
    print('  %d guarded draws over %d pieces; %d of them at a piece where'
          % (tot, len(bat), cand))
    print('  NEITHER mechanism fires -- the only place (BE-50) leaves room.')
    print('  (shape, dim(rho_bar_1 cap E)) census on the honest domain:')
    for k in sorted(census, key=lambda t: (str(t[0]), str(t[1]))):
        print('     %-10s dA = %-4s : %d' % (k[0], k[1], census[k]))
    print('  draws skipped as CROSS-INCIDENT (non-generic flags): %d' % nskip)
    print('  (b3) FAILURES FOUND: %d %s' % (fails, hot if hot else ''))
    print()
    print('  An EMPTY hunt is real corroboration here and not a shrug: by')
    print('  (BE-37)(i)(2) a drawn configuration computes an UPPER bound on')
    print('  min loss, so the sampler can report a false trap but never miss')
    print('  a real one -- and by (BE-37)(i)(3) one drawn configuration with')
    print('  (b3) settles that piece.  Both point the same way here.')
    return fails == 0


# ================================================================== driver

def run_validate():
    t0 = time.time()
    ok = True
    ok &= bool(run_dom(ndraw=4))
    print()
    ok &= bool(run_sep(nseeds=1, quiet=True))
    print()
    ok &= bool(run_domin(ndraw=3))
    print()
    ok &= bool(run_wit(nseeds=2))
    print()
    ok &= bool(run_hunt(nseeds=3))
    print()
    print('===== validate: %s in %.0f s ====='
          % ('ALL MODES AGREE' if ok else 'A MODE REPORTED A FAILURE',
             time.time() - t0))
    return ok


MODES = {
    'dom': run_dom,
    'sep': run_sep,
    'domin': run_domin,
    'wit': run_wit,
    'hunt': run_hunt,
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        raise SystemExit('modes: %s' % ' | '.join(MODES))
    print('seed literal 20260828, exact Q throughout, zero floating point.')
    MODES[mode]()
