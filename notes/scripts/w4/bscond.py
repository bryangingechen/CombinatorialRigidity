"""
Direction BSCOND (ordinal 76) -- (BE-57)(iv)'s TWO WINDOW CONDITIONS, decided.

  TARGET  Prove or refute the two side conditions the window's class theorem
          (BE-57)(i) carries, stated plainly at (BE-57)(iv):

            (S1)  some delta_1-attaining MIDDLE configuration has
                  p_{w1} != p_{w2};
            (S2)  the meeting-lines regime is handled by (BE-55)(iii) only
                  when the forced equality is of the boundary PLANES; a
                  middle forcing some OTHER algebraic relation between its
                  boundary flags that pins lambda onto W^perpK (defeating
                  (BE-56)(ii)'s generic slice) would need its own argument.

          Open since BWIN (ordinal 51) and attacked by none of the eleven
          (BE-14)-thread landings BONEONE (56) .. BDEGTWO (74).

WHAT THIS DRIVER TESTS -- one mode per headline sentence (RESEARCH-ARC s4).

  (BE-142) `support` : THE EVIDENCE SENTENCE FOR (S1) IS CIRCULAR, and the
          guard it names does not do what it is named for.  At source:
            * `bearcase.sample_piece_config` and
              `bsharp.sample_piece_config_adj` BOTH carry
              `if len(set(pt.values())) != len(V): continue` -- a GLOBAL
              pairwise-distinctness filter.  So "every drawn middle satisfies
              (S1)" is a property of the filter, not of the mathematics
              (the RESEARCH-ARC s4 BSATUR sharpening, verbatim).
            * `binduc.assert_generic_star` rejects coincidence ONLY on
              EDGES, plus collinearity at distance 2.  dist_C(w1,w2) >= 3 in
              the window, so it does NOT reject (S1)'s coincidence.
            * `kbare_common.verify_pencil_witness` -- the pencil predicate
              itself -- rejects only ADJACENT coincidence.  The mathematics
              ADMITS p_{w1} = p_{w2}.
            * `bwin.resweep` rejects `rank(L + [p1, p2]) != 4`, so the END
              sampler cannot draw a single configuration over a coincident
              middle: the case is invisible three layers deep.

  (BE-143) `incid` : THE INCIDENCE LEMMA, and (S1)-failure IS (S2)'s regime.
          The pencil condition at u and at v gives p_{w1} in pi_u and
          p_{w2} in pi_v at EVERY configuration, so
            p_{w1} = p_{w2}  ==>  that point lies on L = pi_u cap pi_v,
          and l_u = p_u v p_{w1}, l_v = p_v v p_{w2} then MEET at it.  So a
          middle that forces (S1) to fail forces the meeting-lines regime --
          (S2)'s feared "other algebraic relation" EXISTS and is exactly
          (S1)'s failure.  Asserted at CONSTRUCTED coincidence configurations
          of real window middles.

  (BE-144) `cover` : THE COPLANAR-BOUNDARY LEMMA -- (BE-55)(iii)'s proof is
          PLANE-AGNOSTIC.  For ANY non-skew pair put sigma := l_u v l_v.
          Then, from cross-incidence-freeness and pi_u != pi_v alone:
            L not inside sigma;  q := L cap sigma is a single point;
            q = l_u cap l_v;  span(l_u ^ l_v) = Lambda^2 sigma;
            (Lambda^2 sigma)^perpK = Lambda^2 sigma;
            lambda^perpK cap Lambda^2 sigma = q ^ sigma = <l_u, l_v>.
          So the rank-one kill step is UNCHANGED at every non-skew
          configuration, in BOTH forcing regimes.

  (BE-145) `crit` : THE EXHAUSTIVE CRITERION.  l_u, l_v are non-skew iff
          L cap pi_1 = L cap pi_2, i.e. iff L MEETS the line pi_1 cap pi_2 --
          a Schubert hyperplane section, codimension 1 in the 4-dimensional
          Grassmannian.  So generic L is skew whenever pi_1 != pi_2, and the
          2x2 table (pi_1 = pi_2?) x (p_1 = p_2?) is ENUMERATED: exactly two
          forcing mechanisms, the (!=, !=) cell provably unable to force
          because a dense open is not inside a proper closed set.  (S2)'s
          first half is PROVED and (BE-55)(iii)'s coverage, read through
          (BE-144), is COMPLETE.

  (BE-146) `pin` : (S2)'s SECOND HALF -- IMPOSSIBLE at a free L, and REAL at
          a coincident middle.  At a FREE L (the (BE-55)(i) domain) the
          admissible lines are a dense open of the 4-dimensional Klein
          quadric Q, and Q cap P(W^perpK) is proper closed for t >= 1 because
          Q SPANS Lambda^2 K^4 -- so no middle can pin lambda there.  But
          p_1 = p_2 forces L THROUGH the shared point p, and the lines
          through p span Sigma_p := p ^ K^4, which is SELF-CONJUGATE, so
            lambda in W^perpK for EVERY admissible L  <=>  W inside Sigma_p,
          asserted as an equivalence.  BOTH branches are inhabited by real
          window middles.  (BE-57)(iv)'s "no such mechanism is known" is
          REFUTED: the mechanism is (S1) failing.

  (BE-147) `law` : THE COINCIDENCE EXCESS LAW -- the budget survives the
          pinning, by a DIMENSION CAP rather than a repaired genericity.
          <l_u, l_v> sits inside Sigma_p (both leading lines pass through p),
          so at a coincident middle either
            (a) W inside Sigma_p -- lambda is pinned and V = W, but
                W + <l_u,l_v> inside the 3-dimensional Sigma_p CAPS
                delta_1 <= 3, and excess = t - (t + 2 - delta_1)
                = delta_1 - 2 <= 1;  or
            (b) W outside Sigma_p -- some line through p pairs nonzero with
                W, so generic L through p restores dim V = t - 1 and
                (BE-56)(iii) runs VERBATIM.
          Either way excess <= 1 in the window.

  (BE-148) `ident` + `board` : (S1) IS REMOVABLE.  The window identity
          rho_bar_1 cap Z = <l_u, l_v> verified END TO END at configurations
          the theorem's own hypothesis excluded -- coincident middles with
          freshly drawn ends -- through both gates, with every step of
          *Steps BE53-BE56* asserted at each; `bwin.full_measure`'s own
          (BE-56)(ii) assert FIRES on the case-(a) rows with t >= 1, which is
          (BE-142)'s support finding measured.  `board` carries the price,
          the support audit and the caps.

Succeeds `notes/scripts/w4/bwin.py` (Steps BE53-BE57); imports `bwin` /
`bsharp` / `bimage` / `binduc` READ-ONLY, and through them `brule` /
`bearfull` / `bearcase` / `btwocut` / `bzavoid` / `kbare_common`.  Landed
figures are CITED, never re-run.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, `contains`) and never of dimensions, every
cap disclosed.

HARNESS HAZARDS OBSERVED (`notes/scripts/README.md` *Harness debt*): no
Lambda^2-side draw goes through `bimage.pt_in` (silent K^4 truncation), and
no K^4-side draw goes through `bimage.span`/`isect` (silent dimension 0 at
full rank) -- `bwin.k4_span`/`k4_isect` are used for every K^4 subspace.

DISCLOSED DRIVER CAPS (the mathematics does not share them): every battery
piece has deg(u) = deg(v) = 1 (bwin's own cap, inherited through
`series_data`); the coincidence sampler supports shapes whose middle branch
set is INDEPENDENT with every free vertex carrying at most one branch
neighbour; and no coincident middle here is claimed to be delta_1-ATTAINING
-- (BE-148) does not need one, which is the point of the removal.  The one
row shape the battery does NOT reach is a case-(b) coincident middle with
delta_1 = 4 (all four measure 5, outside the window); it is covered by
(BE-56)(iii) verbatim, and case (a) makes delta_1 = 4 IMPOSSIBLE rather than
unwitnessed.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import itertools
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import (rank as rank_exact, nullspace, hat, wedge2,   # noqa: E402
                       neighbors)
from kbare_common import verify_pencil_witness                       # noqa: E402
from binduc import assert_generic_star, verts_of                     # noqa: E402
from bimage import (contains, dim, isect, klein, klein_perp,         # noqa: E402
                    pencil_space, rho_bar_of, same_space, span)
from bsharp import barbell                                           # noqa: E402
from bwin import (SEED, boundary_plane, dehom, full_measure,         # noqa: E402
                  k4_isect, k4_span, pt_on_line, resweep, rq,
                  series_data, theta_chain, v4, window_battery)


def aff(x):
    """K^4 point -> the hashable affine 3-tuple every sampler in the tree
    stores.  `bwin.dehom` returns a LIST, which is unhashable and compares
    unequal to the tuples `assert_generic_star` tests -- so every point this
    module writes into a configuration goes through here."""
    return tuple(dehom(x))


def v4aff(rng, s=20, tries=200):
    """A random K^4 point that is not at infinity."""
    for _ in range(tries):
        x = v4(rng, s)
        if x[3] != 0:
            return x
    raise RuntimeError('v4aff: no draw')

# ================================================== small exact helpers


def plane_through(pts, rng, s=20, tries=200):
    """A K^4 plane (3-dim subspace) containing every point of `pts`."""
    assert rank_exact(pts) <= 3, 'points do not fit in a plane'
    for _ in range(tries):
        ext = list(pts)
        while rank_exact(ext) < 3:
            x = v4(rng, s)
            if rank_exact(ext + [x]) > rank_exact(ext):
                ext.append(x)
            else:
                break
        if rank_exact(ext) == 3:
            return k4_span(ext)
    raise RuntimeError('plane_through: no draw')


def pt_in_plane(pi, rng, s=20, tries=200):
    """An affine point of the K^4 plane `pi` (basis of 3)."""
    for _ in range(tries):
        c = [rq(rng, s) for _ in range(3)]
        x = [sum(c[j] * pi[j][k] for j in range(3)) for k in range(4)]
        if x[3] != 0:
            return x
    raise RuntimeError('pt_in_plane: no draw')


def lam2_of(pi):
    """Lambda^2 sigma for a K^4 plane sigma (basis of 3): the 3-dim space of
    lines inside sigma."""
    assert len(pi) == 3, 'not a plane'
    return span([wedge2(pi[i], pi[j]) for i, j in itertools.combinations(
        range(3), 2)])


def line_pencil(p, pi):
    """q ^ sigma: the 2-dim pencil of lines of the plane `pi` through the
    point `p` of it."""
    assert rank_exact(pi + [p]) == 3, 'point not on the plane'
    return pencil_space(p, pi)


def rand_line(rng, s=20, tries=200):
    """A random K^4 line (basis of 2) with its Plucker point."""
    for _ in range(tries):
        a, b = v4(rng, s), v4(rng, s)
        if rank_exact([a, b]) == 2:
            return k4_span([a, b]), wedge2(a, b)
    raise RuntimeError('rand_line: no draw')


def rand_lam2_sub(rng, d, s=12, tries=400):
    """A random d-dimensional subspace of Lambda^2 K^4."""
    if d == 0:
        return []
    for _ in range(tries):
        rows = [[rq(rng, s) for _ in range(6)] for _ in range(d)]
        if rank_exact(rows) == d:
            return span(rows)
    raise RuntimeError('rand_lam2_sub: no draw')


# ================================================== the coincidence sampler


def coin_support(edges, u, v):
    """(w1, w2, C, branch) if the shape is supported, else None + why."""
    w1, w2, C = series_data(edges, u, v)
    nbC = neighbors(C)
    branch = {z for z in verts_of(C) if len(nbC.get(z, ())) >= 3}
    for z in branch:
        for y in nbC.get(z, ()):
            if y in branch:
                return None, 'branch vertices adjacent -- unsupported'
    for w in verts_of(C):
        if w in branch:
            continue
        if len([z for z in nbC.get(w, ()) if z in branch]) > 1:
            return None, 'a free vertex has two branch neighbours'
    if w1 == w2:
        return None, 'w1 = w2 (dist_C < 1)'
    if w2 in nbC.get(w1, ()):
        return None, 'w1 adjacent to w2 (dist_C = 1)'
    return (w1, w2, C, branch), None


def coin_draw(edges, u, v, rng, s=20, tries=400):
    """A pencil configuration of the piece's MIDDLE with p_{w1} = p_{w2}.

    This DELIBERATELY defeats the two landed samplers' global distinctness
    filter -- `bearcase.sample_piece_config` and
    `bsharp.sample_piece_config_adj` both `continue` on
    `len(set(pt.values())) != len(V)`, which is exactly what makes
    (BE-57)(iv)'s "every drawn middle satisfies it" a statement about the
    filter.  Legality here comes from the pencil condition itself -- every
    closed star coplanar ((BE-16)) -- verified by BOTH gates below.

    Construction ((BE-48)'s parametrization, planes first): pick the shared
    point `p`, then choose the plane at every branch vertex, forcing it
    THROUGH `p` at exactly those branch vertices whose star must contain `p`
    (w1, w2 themselves when they are branch, and every branch neighbour of
    either).  Points then drop out.

    Returns (pt, pi1, pi2) or None.  pt has NO entry for u or v -- the ends
    are drawn fresh by `coin_resweep` over the fixed middle.
    """
    got, why = coin_support(edges, u, v)
    if got is None:
        return None, why
    w1, w2, C, branch = got
    nbC = neighbors(C)
    V = sorted(verts_of(C), key=str)
    # which branch planes must contain the shared point
    must = set()
    for w in (w1, w2):
        if w in branch:
            must.add(w)
        must |= {z for z in nbC.get(w, ()) if z in branch}
    for _ in range(tries):
        try:
            p = v4aff(rng, s)
        except RuntimeError:
            continue
        pl = {}
        bad = False
        for z in sorted(branch, key=str):
            try:
                pl[z] = plane_through([p], rng, s) if z in must \
                    else plane_through([v4(rng, s)], rng, s)
            except (RuntimeError, AssertionError):
                bad = True
                break
        if bad:
            continue
        pt = {w1: aff(p), w2: aff(p)}
        for w in V:
            if w in (w1, w2):
                continue
            try:
                if w in branch:
                    pt[w] = aff(pt_in_plane(pl[w], rng, s))
                else:
                    bs = [z for z in nbC.get(w, ()) if z in branch]
                    pt[w] = aff(pt_in_plane(pl[bs[0]], rng, s)) if bs \
                        else aff(v4aff(rng, s))
            except (RuntimeError, AssertionError):
                bad = True
                break
        if bad:
            continue
        # the coincidence is the ONLY repeated point
        if len(set(pt.values())) != len(V) - 1:
            continue
        try:
            assert_generic_star(C, pt)
        except AssertionError:
            continue
        ok, _why = verify_pencil_witness(C, pt)
        if not ok:
            continue
        pi1, f1 = boundary_plane(edges, pt, w1, u, rng)
        pi2, f2 = boundary_plane(edges, pt, w2, v, rng)
        if len(pi1) != 3 or len(pi2) != 3:
            continue
        if same_space(pi1, pi2):
            continue          # keep the two forcing regimes separate
        return (pt, pi1, pi2, f1, f2), None
    return None, 'no coincident draw under the try budget'


def coin_resweep(edges, u, v, pt0, pi1, pi2, rng, s=20):
    """ONE fresh end draw over a FIXED COINCIDENT middle.

    (BE-55)(i)'s parametrization is NOT available here: it sets
    pi_u = L v p_1, which needs p_1 off L, and p_1 = p_2 forces p_1 ON L
    ((BE-143)).  So L is drawn THROUGH the shared point and pi_u, pi_v are
    two distinct planes of the pencil through L -- the honest domain of the
    coincidence regime.  Returns (pt, planes, aux) or None."""
    w1, w2, _C = series_data(edges, u, v)
    p = hat(pt0[w1])
    assert p == hat(pt0[w2]), 'coin_resweep on a non-coincident middle'
    try:
        r = v4aff(rng, s)
    except RuntimeError:
        return None
    if rank_exact([p, r]) != 2:
        return None
    Lb = k4_span([p, r])
    if len(Lb) != 2:
        return None
    # L must miss both boundary planes elsewhere: L inside pi_i would make
    # l_u = L and put p_u on L (a terminal cross-incidence)
    if rank_exact(pi1 + [r]) == 3 or rank_exact(pi2 + [r]) == 3:
        return None
    piu = plane_through(Lb, rng, s)
    piv = plane_through(Lb, rng, s)
    if same_space(piu, piv):
        return None
    if not same_space(k4_isect(piu, piv), Lb):
        return None
    lu_ = k4_isect(piu, pi1)
    lv_ = k4_isect(piv, pi2)
    if len(lu_) != 2 or len(lv_) != 2:
        return None
    if rank_exact(lu_ + lv_) != 3:
        return None            # must MEET and be distinct
    try:
        pu = pt_on_line(lu_, rng, p)
        pv = pt_on_line(lv_, rng, p)
    except RuntimeError:
        return None
    # honest domain: terminal cross-incidence-freeness, M skew to L
    if rank_exact(Lb + [pu]) != 3 or rank_exact(Lb + [pv]) != 3:
        return None
    if rank_exact([pu, pv] + Lb) != 4:
        return None
    pt = dict(pt0)
    pt[u] = aff(pu)
    pt[v] = aff(pv)
    ok, _why = verify_pencil_witness(edges, pt)
    if not ok:
        return None
    try:
        assert_generic_star(edges, pt)
    except AssertionError:
        return None
    return pt, {u: piu, v: piv}, dict(Lb=Lb, p=p, lu=lu_, lv=lv_,
                                      pi1=pi1, pi2=pi2, piu=piu, piv=piv)


def coin_battery():
    """BWIN's own window battery ((BE-58)(i)'s `wide` mode, cited shapes and
    fresh draws), plus two LONGER theta chains.

    Two of BWIN's twelve rows fall outside this sampler's shape guard --
    disclosed rather than dropped, and the longer chains are the repair: a
    3-edge bridge between the two thetas separates the branch vertices and
    leaves every free vertex with one branch neighbour."""
    rows = [(r[0], r[1], r[2], r[3]) for r in window_battery()]
    rows += [
        ('theta-chain 1/(3,3,3)/3/(3,3,3)/1 [longer bridge]',
         theta_chain(1, (3, 3, 3), 3, (3, 3, 3), 1), 'u', 'v'),
        ('theta-chain 1/(3,3,3)/3/(3,3,4)/1 [longer bridge]',
         theta_chain(1, (3, 3, 3), 3, (3, 3, 4), 1), 'u', 'v'),
    ]
    return rows


# ================================================== (BE-144)'s lemma, once


def cover_lemma(Lb, lam, lu_, lv_, tag=''):
    """THE COPLANAR-BOUNDARY LEMMA, asserted as identities of SPACES at one
    non-skew flag datum.  `lu_`, `lv_` are K^4 lines (bases of 2) that MEET
    and are distinct; `Lb`/`lam` are L and its Plucker point, with L not
    inside sigma := l_u v l_v.  Returns (sigma, q, Luv)."""
    assert len(lu_) == 2 and len(lv_) == 2, f'{tag}: not lines'
    assert rank_exact(lu_ + lv_) == 3, f'{tag}: l_u, l_v skew or equal'
    sigma = k4_span(lu_ + lv_)
    assert len(sigma) == 3, f'{tag}: sigma is not a plane'
    lu = wedge2(lu_[0], lu_[1])
    lv = wedge2(lv_[0], lv_[1])
    # (BE-56)(ii), the ONLY input beyond non-skewness: each leading line
    # meets L (it is coplanar with L inside pi_u resp. pi_v)
    assert klein(lu, lam) == 0, f'{tag}: l_u does not meet L'
    assert klein(lv, lam) == 0, f'{tag}: l_v does not meet L'
    # L is not inside sigma -- from pi_u != pi_v and l_u, l_v != L
    assert rank_exact(sigma + Lb) == 4, f'{tag}: L lies inside sigma'
    qs = k4_isect(sigma, Lb)
    assert len(qs) == 1, f'{tag}: L cap sigma is not a single point'
    q = qs[0]
    # ... and then q IS the common point of l_u and l_v, DERIVED: each line
    # meets L inside sigma, and L cap sigma is the single point q
    assert rank_exact(lu_ + [q]) == 2 and rank_exact(lv_ + [q]) == 2, \
        f'{tag}: q is not the meeting point'
    assert same_space(k4_isect(k4_span(lu_), k4_span(lv_)), [q]) or \
        rank_exact(k4_isect(k4_span(lu_), k4_span(lv_)) + [q]) == 1, \
        f'{tag}: l_u cap l_v != q'
    Luv = span([lu, lv])
    assert dim(Luv) == 2, f'{tag}: <l_u, l_v> is not 2-dimensional'
    # survivors of EVERY admissible mu = p_u ^ p_v: span(l_u ^ l_v)
    T = span([wedge2(x, y) for x in lu_ for y in lv_])
    L2s = lam2_of(sigma)
    assert same_space(T, L2s), f'{tag}: span(l_u ^ l_v) != Lambda^2 sigma'
    assert dim(T) == 3, f'{tag}: span(l_u ^ l_v) is not 3-dimensional'
    assert same_space(klein_perp(L2s), L2s), \
        f'{tag}: (Lambda^2 sigma)^perpK != Lambda^2 sigma'
    # the slice: lines of sigma conjugate to lambda are those through q
    slice_ = isect(klein_perp([lam]), L2s)
    assert same_space(slice_, line_pencil(q, sigma)), \
        f'{tag}: lambda^perpK cap Lambda^2 sigma != q ^ sigma'
    assert same_space(slice_, Luv), \
        f'{tag}: q ^ sigma != <l_u, l_v>  (the kill step would fail)'
    return sigma, q, Luv


# ================================================== mode (BE-142)


def run_support(seed=SEED):
    print('===== Step BE141 / (BE-142): THE EVIDENCE SENTENCE FOR (S1) IS '
          'CIRCULAR =====')
    print('  (BE-57)(iv) offers, for (S1): "no arc mechanism forces two')
    print('  distinct vertices onto one point, BOTH SAMPLERS REJECT')
    print('  COINCIDENCE, and every drawn middle satisfies it".  The second')
    print('  clause is what makes the third vacuous (RESEARCH-ARC s4, the')
    print('  BSATUR sharpening: name the support, ask which of the claim\'s')
    print('  own variables it varies).')
    t0 = time.time()
    import inspect
    import bearcase
    import bsharp as _bsharp
    import binduc as _binduc
    import kbare_common as _kb

    # 1. the two samplers carry a GLOBAL distinctness filter
    filt = 'len(set(pt.values())) != len(V)'
    hits = []
    for mod, fn in ((bearcase, 'sample_piece_config'),
                    (_bsharp, 'sample_piece_config_adj')):
        src = inspect.getsource(getattr(mod, fn))
        assert filt in src, f'{fn}: the distinctness filter moved'
        hits.append(f'{mod.__name__}.{fn}')
    print(f'  [1] the GLOBAL distinctness filter `{filt}` is present in BOTH '
          f'landed samplers:')
    for h in hits:
        print(f'        {h}')
    print('      -> every drawn middle has p_{w1} != p_{w2} BY THE FILTER.')

    # 2. assert_generic_star does NOT reject distance->=3 coincidence
    src = inspect.getsource(_binduc.assert_generic_star)
    assert 'for (u, v) in edges' in src, 'assert_generic_star restructured'
    assert filt not in src, 'assert_generic_star gained a global filter'
    rng = __import__('random').Random(seed)
    # a legal FLAT configuration of a path of 3 edges with the ends coincident
    P = [('a', 'b'), ('b', 'c'), ('c', 'd')]
    pt = {'a': (F(0), F(0), F(0)), 'b': (F(3), F(1), F(0)),
          'c': (F(1), F(4), F(0)), 'd': (F(0), F(0), F(0))}
    assert_generic_star(P, pt)                     # accepts it
    ok, why = verify_pencil_witness(P, pt)
    assert ok, why                                 # and so does the predicate
    print('  [2] `binduc.assert_generic_star` asserts distinctness only on '
          'EDGES,')
    print('      plus non-collinearity at distance 2.  dist_C(w1,w2) >= 3 in')
    print('      the window ((BE-47)(ii): dist >= 5), so the guard the clause')
    print('      NAMES does not reach (S1)\'s coincidence.  Witness: a legal')
    print('      pencil configuration of a 3-edge path with its two ENDS at')
    print('      the same point is ACCEPTED by the guard.')
    src = inspect.getsource(_kb.verify_pencil_witness)
    assert "('coincident adjacent points', (u, w))" in src, \
        'verify_pencil_witness restructured'
    print('  [3] `kbare_common.verify_pencil_witness` -- the pencil PREDICATE '
          'itself --')
    print('      rejects only ADJACENT coincidence, and accepted the witness')
    print('      above.  So the MATHEMATICS admits p_{w1} = p_{w2}: there is')
    print('      no mechanism to find, and none was ever excluded.')

    # 4. the END sampler cannot draw over a coincident middle
    src = inspect.getsource(resweep)
    assert 'rank_exact(Lb + [p1, p2]) != 4' in src, 'resweep restructured'
    edges = barbell(1, 3, 3, 3, 1)
    got, why = coin_draw(edges, 'u', 'v', __import__('random').Random(seed))
    assert got is not None, why
    pt0, pi1, pi2, _f1, _f2 = got
    n = 0
    for _ in range(60):
        if resweep(edges, 'u', 'v', pt0, rng) is not None:
            n += 1
    assert n == 0, 'bwin.resweep drew ends over a coincident middle'
    print('  [4] `bwin.resweep` returns None on `rank(L + [p1, p2]) != 4`, '
          'which')
    print('      p1 = p2 makes UNSATISFIABLE: 0 of 60 end draws over a')
    print('      constructed coincident middle survived.  The case is')
    print('      invisible three layers deep -- middle sampler, star guard,')
    print('      end sampler -- and (BE-55)(i)\'s own honest domain')
    print('      (`p1, p2 not on L`) EXCLUDES it by hypothesis.')
    print('  VERDICT: "both samplers reject coincidence" is TRUE and is the')
    print('  REASON "every drawn middle satisfies it" carries no weight.  The')
    print(f'  sentence is struck as evidence.  [{time.time() - t0:.0f} s]')
    return True


# ================================================== mode (BE-143)


def run_incid(seed=SEED, nseeds=2, ndraw=4):
    print('===== Step BE142 / (BE-143): THE INCIDENCE LEMMA -- (S1)-FAILURE '
          'IS (S2)\'s REGIME =====')
    print('  p_{w1} in pi_u and p_{w2} in pi_v at EVERY pencil')
    print('  configuration (w1 ~ u and w2 ~ v, so each is in the terminal\'s')
    print('  own closed star).  Hence p_{w1} = p_{w2} forces that point onto')
    print('  L = pi_u cap pi_v, and l_u = p_u v p_{w1}, l_v = p_v v p_{w2}')
    print('  MEET there.  So (S2)\'s "other algebraic relation between the')
    print('  boundary flags" EXISTS -- it is (S1) failing.')
    t0 = time.time()
    import random
    rows = tot = 0
    for name, edges, u, v in coin_battery():
        for si in range(nseeds):
            rng = random.Random(seed + 977 * si)
            got, why = coin_draw(edges, u, v, rng)
            if got is None:
                print(f'  {name}: no coincident draw ({why}) -- SKIPPED')
                continue
            pt0, pi1, pi2, f1, f2 = got
            w1, w2, _C = series_data(edges, u, v)
            drew = 0
            for _ in range(400):
                if drew >= ndraw:
                    break
                out = coin_resweep(edges, u, v, pt0, pi1, pi2, rng)
                if out is None:
                    continue
                drew += 1
                tot += 1
                pt, planes, aux = out
                p, Lb = aux['p'], aux['Lb']
                # the lemma, at this configuration, as incidences
                assert rank_exact(planes[u] + [hat(pt[w1])]) == 3, \
                    'p_{w1} not on pi_u'
                assert rank_exact(planes[v] + [hat(pt[w2])]) == 3, \
                    'p_{w2} not on pi_v'
                assert hat(pt[w1]) == hat(pt[w2]), 'coincidence lost'
                assert rank_exact(Lb + [p]) == 2, \
                    'the shared point is not on L'
                assert same_space(k4_isect(planes[u], planes[v]), Lb), \
                    'L != pi_u cap pi_v'
                # ... and l_u, l_v MEET at it
                lu_ = [hat(pt[u]), p]
                lv_ = [hat(pt[v]), p]
                assert rank_exact(lu_ + lv_) == 3, \
                    'l_u, l_v are skew at a coincident middle'
                assert same_space(k4_isect(k4_span(lu_), k4_span(lv_)),
                                  [p]), 'l_u cap l_v != the shared point'
                # the boundary planes are DISTINCT here, so this is a
                # forcing mechanism (BE-55)(iii) does not name
                assert not same_space(pi1, pi2), 'pi_1 = pi_2 at this draw'
                assert rank_exact(pi1 + [p]) == 3 and \
                    rank_exact(pi2 + [p]) == 3, \
                    'the shared point misses a boundary plane'
            if drew:
                rows += 1
                print(f'  {name} [seed {si}]: {drew} end draws over a '
                      f'COINCIDENT middle; pi_1 != pi_2 (forced={f1}/{f2}); '
                      'p in L, l_u cap l_v = p  -- all asserted')
    assert rows >= 16, f'fewer than sixteen coincident rows ({rows})'
    print(f'  VERDICT: (S2)\'s feared mechanism is INHABITED, at real window')
    print(f'  middles, with pi_1 != pi_2 throughout -- so it is NOT the')
    print(f'  (BE-55)(iii) case.  (S1) and (S2) are ONE gap, not two.')
    print(f'  [{rows} rows, {tot} coincident configurations, '
          f'{time.time() - t0:.0f} s]')
    return True


# ================================================== mode (BE-144)


def run_cover(seed=SEED, nsynth=60, nseeds=2, ndraw=3):
    print('===== Step BE143 / (BE-144): THE COPLANAR-BOUNDARY LEMMA -- '
          '(BE-55)(iii) IS PLANE-AGNOSTIC =====')
    print('  (BE-55)(iii) is stated for pi_1 = pi_2 = pi and uses sigma = pi,')
    print('  q = L cap pi.  Its PROOF needs only a plane sigma containing')
    print('  both leading lines with L outside it.  sigma := l_u v l_v always')
    print('  is one, and cross-incidence-freeness + pi_u != pi_v give L')
    print('  outside it.  So the rank-one budget survives EVERY non-skew')
    print('  configuration, in both forcing regimes.')
    t0 = time.time()
    import random
    rng = random.Random(seed)

    # (a) the pi_1 = pi_2 regime, synthetically -- (BE-55)(iii)'s own case
    na = 0
    for _ in range(nsynth * 8):
        if na >= nsynth:
            break
        pi = plane_through([v4(rng)], rng)
        Lb, lam = rand_line(rng)
        if rank_exact(pi + Lb) != 4:
            continue                       # need L outside pi
        qs = k4_isect(pi, Lb)
        if len(qs) != 1:
            continue
        p1 = pt_in_plane(pi, rng)
        p2 = pt_in_plane(pi, rng)
        if rank_exact([p1, qs[0]]) != 2 or rank_exact([p2, qs[0]]) != 2:
            continue
        lu_, lv_ = k4_span([p1, qs[0]]), k4_span([p2, qs[0]])
        if rank_exact(lu_ + lv_) != 3:
            continue
        cover_lemma(Lb, lam, lu_, lv_, tag='pi_1 = pi_2')
        na += 1
    assert na == nsynth, f'only {na} of {nsynth} equal-plane trials built'

    # (b) an arbitrary non-skew pair, synthetically: sigma is NOT a boundary
    #     plane and NOT forced by any equality -- the general lemma
    nb_ = 0
    for _ in range(nsynth * 8):
        if nb_ >= nsynth:
            break
        q = v4(rng)
        if q[3] == 0:
            continue
        a, b = v4(rng), v4(rng)
        if rank_exact([q, a, b]) != 3:
            continue
        lu_, lv_ = k4_span([q, a]), k4_span([q, b])
        if rank_exact(lu_ + lv_) != 3:
            continue
        sigma = k4_span(lu_ + lv_)
        # L is NOT free here: (BE-56)(ii) makes both leading lines meet it,
        # and L outside sigma then forces L THROUGH the meeting point q.
        # So L is drawn as q v r with r off sigma -- and that is the whole
        # hypothesis the lemma needs.
        r = v4(rng)
        if rank_exact(sigma + [r]) != 4 or rank_exact([q, r]) != 2:
            continue
        Lb = k4_span([q, r])
        if len(Lb) != 2:
            continue
        lam = wedge2(Lb[0], Lb[1])
        cover_lemma(Lb, lam, lu_, lv_, tag='general non-skew')
        nb_ += 1
    assert nb_ == nsynth, f'only {nb_} of {nsynth} general trials built'

    # (c) at REAL coincident middles with their own drawn ends
    nc = rows = 0
    for name, edges, u, v in coin_battery():
        for si in range(nseeds):
            r2 = random.Random(seed + 613 * si)
            got, _why = coin_draw(edges, u, v, r2)
            if got is None:
                continue
            pt0, pi1, pi2, _f1, _f2 = got
            w1, w2, _C = series_data(edges, u, v)
            drew = 0
            for _ in range(400):
                if drew >= ndraw:
                    break
                out = coin_resweep(edges, u, v, pt0, pi1, pi2, r2)
                if out is None:
                    continue
                drew += 1
                nc += 1
                pt, planes, aux = out
                Lb = aux['Lb']
                lam = wedge2(Lb[0], Lb[1])
                lu_ = k4_span([hat(pt[u]), hat(pt[w1])])
                lv_ = k4_span([hat(pt[v]), hat(pt[w2])])
                sigma, q, Luv = cover_lemma(Lb, lam, lu_, lv_, tag=name)
                # sigma is p v M here -- NOT a boundary plane
                assert not same_space(sigma, pi1) and \
                    not same_space(sigma, pi2), \
                    f'{name}: sigma coincides with a boundary plane'
                assert q == aux['p'] or rank_exact([q, aux['p']]) == 1, \
                    f'{name}: q is not the shared point'
            if drew:
                rows += 1
    assert rows >= 16, f'fewer than sixteen real rows ({rows})'
    print(f'  (a) pi_1 = pi_2 (the landed case): {na}/{na} trials, every')
    print('      identity of SPACES asserted.')
    print(f'  (b) an ARBITRARY non-skew pair, sigma forced by nothing: '
          f'{nb_}/{nb_}.')
    print(f'  (c) REAL coincident window middles: {rows} shapes, {nc} '
          'configurations,')
    print('      sigma = p v M asserted DISTINCT from both boundary planes')
    print('      and q asserted EQUAL to the shared point.')
    print('  VERDICT: the lemma covers the regime whatever forces it.')
    print(f'  [{time.time() - t0:.0f} s]')
    return True


# ================================================== mode (BE-145)


def run_crit(seed=SEED, ntrial=200):
    print('===== Step BE144 / (BE-145): THE EXHAUSTIVE CRITERION -- and the '
          'TWO forcing mechanisms are ALL =====')
    print('  l_u = pi_u cap pi_1 and l_v = pi_v cap pi_2 both meet L inside')
    print('  pi_u, pi_v, and any common point lies in pi_u cap pi_v = L; so')
    print('    l_u, l_v NON-SKEW  <=>  L cap pi_1 = L cap pi_2')
    print('                       <=>  L MEETS the line pi_1 cap pi_2,')
    print('  a Schubert hyperplane section: codimension 1 in the')
    print('  4-dimensional Grassmannian.  Generic L is therefore SKEW')
    print('  whenever pi_1 != pi_2.')
    t0 = time.time()
    import random
    rng = random.Random(seed)
    census = {True: 0, False: 0}
    forced = 0
    built = 0
    for _ in range(ntrial * 12):
        if built >= ntrial:
            break
        pi1 = plane_through([v4(rng)], rng)
        pi2 = plane_through([v4(rng)], rng)
        if same_space(pi1, pi2):
            continue
        p1 = pt_in_plane(pi1, rng)
        p2 = pt_in_plane(pi2, rng)
        Lb, lam = rand_line(rng)
        # (BE-55)(i)'s honest domain
        if rank_exact(Lb + [p1]) != 3 or rank_exact(Lb + [p2]) != 3:
            continue
        if rank_exact(Lb + [p1, p2]) != 4:
            continue
        piu, piv = k4_span(Lb + [p1]), k4_span(Lb + [p2])
        if len(piu) != 3 or len(piv) != 3 or same_space(piu, piv):
            continue
        lu_, lv_ = k4_isect(piu, pi1), k4_isect(piv, pi2)
        if len(lu_) != 2 or len(lv_) != 2:
            continue
        built += 1
        nonskew = rank_exact(lu_ + lv_) == 3
        # the criterion, both readings, asserted EQUAL to the fact
        a1, a2 = k4_isect(Lb, pi1), k4_isect(Lb, pi2)
        assert len(a1) == 1 and len(a2) == 1, 'L inside a boundary plane'
        c1 = rank_exact([a1[0], a2[0]]) == 1
        n = k4_isect(pi1, pi2)
        assert len(n) == 2, 'pi_1 cap pi_2 is not a line'
        c2 = rank_exact(Lb + n) == 3
        assert nonskew == c1, 'criterion 1 (L cap pi_1 = L cap pi_2) failed'
        assert nonskew == c2, 'criterion 2 (L meets pi_1 cap pi_2) failed'
        census[nonskew] += 1
    assert built == ntrial, f'only {built} of {ntrial} trials built'
    assert census[True] == 0, \
        f'{census[True]} random L hit the codimension-1 locus'
    print(f'  [criterion] {built}/{built} draws with pi_1 != pi_2: the two')
    print('      readings of the criterion agree with the SKEWNESS FACT at')
    print(f'      every one; non-skew at {census[True]} of {built} random L')
    print('      (codimension 1, so 0 is what a random draw must give).')

    # THE 2x2 FORCING TABLE, ENUMERATED (RESEARCH-ARC s4: an
    # exhaustiveness claim needs a driver that enumerates).  The criterion is
    # "L meets pi_1 cap pi_2", so a middle forces the regime for EVERY
    # admissible L iff pi_1 cap pi_2 meets every admissible L.  The two
    # independent bits the middle controls are (pi_1 = pi_2?) and
    # (p_1 = p_2?), and the table below is complete because those are the
    # only two data (BE-55)(i)'s domain reads off the middle.
    table = {}
    # cell (!=, !=): NOT forced -- the criterion locus is codimension 1
    table[('pi1!=pi2', 'p1!=p2')] = ('NOT forced',
                                     f'{census[True]} of {built} random '
                                     'admissible L are non-skew')
    # cell (=, !=): forced, mechanism 1
    n1 = 0
    for _ in range(80):
        pi = plane_through([v4aff(rng)], rng)
        Lb, _lam = rand_line(rng)
        if rank_exact(pi + Lb) != 4:
            continue
        a1, a2 = k4_isect(Lb, pi), k4_isect(Lb, pi)
        assert rank_exact([a1[0], a2[0]]) == 1, 'pi_1 = pi_2 not forcing'
        n1 += 1
    assert n1 >= 40, f'only {n1} equal-plane trials'
    table[('pi1==pi2', 'p1!=p2')] = ('FORCED (mechanism 1)',
                                     f'L cap pi_1 = L cap pi_2 at {n1}/{n1} '
                                     'lines L: pi_1 cap pi_2 is a PLANE')
    # cell (!=, =): forced, mechanism 2 -- at real coincident middles
    n2 = shapes = 0
    for name, edges, u, v in coin_battery()[:6]:
        r2 = __import__('random').Random(seed + 41)
        got, _why = coin_draw(edges, u, v, r2)
        if got is None:
            continue
        pt0, pi1, pi2, _f1, _f2 = got
        w1, _w2, _C = series_data(edges, u, v)
        p = hat(pt0[w1])
        n = k4_isect(pi1, pi2)
        assert not same_space(pi1, pi2), f'{name}: pi_1 = pi_2 (wrong cell)'
        assert len(n) == 2 and rank_exact(n + [p]) == 2, \
            f'{name}: the shared point is not on pi_1 cap pi_2'
        drew = 0
        for _ in range(400):
            if drew >= 5:
                break
            out = coin_resweep(edges, u, v, pt0, pi1, pi2, r2)
            if out is None:
                continue
            drew += 1
            n2 += 1
            assert rank_exact(out[2]['Lb'] + n) == 3, \
                f'{name}: L misses pi_1 cap pi_2 at a coincident middle'
        if drew:
            shapes += 1
    assert shapes >= 4, f'mechanism 2 exhibited at only {shapes} shapes'
    table[('pi1!=pi2', 'p1==p2')] = ('FORCED (mechanism 2)',
                                     f'p_1 = p_2 lies on pi_1 cap pi_2 AND '
                                     f'on every admissible L: {n2} '
                                     f'configurations, {shapes} shapes')
    # cell (=, =): forced A FORTIORI by mechanism 1, which needs only pi_1 =
    # pi_2 -- so no separate witness is needed and none is claimed
    table[('pi1==pi2', 'p1==p2')] = ('FORCED (a fortiori by mechanism 1)',
                                     'contained in the pi_1 = pi_2 cell; no '
                                     'independent witness claimed')
    print('  [the 2x2 FORCING TABLE, enumerated -- these are the only two')
    print('   data (BE-55)(i)\'s honest domain reads off the middle]')
    for k in sorted(table):
        verdict, why = table[k]
        print(f'      {k[0]:9s} {k[1]:8s} -> {verdict}')
        print(f'          {why}')
    assert len(table) == 4, 'the table is not complete'
    forced = sum(1 for v in table.values() if v[0].startswith('FORCED'))
    assert forced == 3, 'the forced-cell count moved'
    print('  [why the table is EXHAUSTIVE, and it is an argument not a')
    print('   sample] the admissible L are a DENSE OPEN of the irreducible')
    print('   4-dimensional Grassmannian whenever p_1 != p_2, and')
    print('   {L : L meets pi_1 cap pi_2} is closed of codimension 1 there;')
    print('   a dense open is not contained in a proper closed set, so the')
    print('   (!=, !=) cell CANNOT force.  Hence forcing requires')
    print('   pi_1 = pi_2 or p_1 = p_2 -- exactly the two mechanisms, so')
    print('   (S2a) is PROVED and (BE-55)(iii)\'s coverage, read through')
    print('   (BE-144), is COMPLETE.')
    print(f'  [{time.time() - t0:.0f} s]')
    return True


def sigma_p(p):
    """Sigma_p := p ^ K^4, the 3-dimensional space of lines through the point
    `p`.  Self-conjugate: two lines through one point always meet."""
    E = [[F(1) if i == j else F(0) for i in range(4)] for j in range(4)]
    out = span([wedge2(p, e) for e in E])
    assert dim(out) == 3, 'Sigma_p is not 3-dimensional'
    return out


# ================================================== mode (BE-146)


def run_pin(seed=SEED, ntrial=120, nseeds=2, ndraw=3):
    print('===== Step BE145 / (BE-146): (S2)\'s SECOND HALF -- IMPOSSIBLE at a '
          'FREE L, and REAL at a COINCIDENT middle =====')
    print('  (BE-56)(ii) needs lambda off W^perpK.  Two regimes, opposite')
    print('  answers, and the clause recorded only the first.')
    t0 = time.time()
    import random
    rng = random.Random(seed)

    # Q spans Lambda^2 K^4 -- the whole reason W^perpK cannot contain it
    lines = []
    for _ in range(400):
        _Lb, lam = rand_line(rng)
        lines.append(lam)
        if rank_exact(lines) == 6:
            break
    assert rank_exact(lines) == 6, 'the Klein quadric failed to span'
    print(f'  [Q spans] {len(lines)} Plucker points span Lambda^2 K^4 '
          '(rank 6),')
    print('      so NO proper linear subspace of Lambda^2 K^4 contains the')
    print('      quadric, and Q cap P(W^perpK) is proper closed in Q for')
    print('      every t >= 1.')

    # (A) a FREE L: (BE-55)(i)'s parametrization.  lambda cannot be pinned.
    census = {}
    for t in range(0, 6):
        hit = built = 0
        for _ in range(ntrial * 20):
            if built >= ntrial:
                break
            W = rand_lam2_sub(rng, t)
            Wp = klein_perp(W) if W else span(
                [[F(1) if i == j else F(0) for i in range(6)]
                 for j in range(6)])
            assert dim(Wp) == 6 - t, 'W^perpK has the wrong dimension'
            p1, p2 = v4(rng), v4(rng)
            if rank_exact([p1, p2]) != 2:
                continue
            Lb, lam = rand_line(rng)
            if rank_exact(Lb + [p1]) != 3 or rank_exact(Lb + [p2]) != 3:
                continue
            if rank_exact(Lb + [p1, p2]) != 4:
                continue
            built += 1
            inperp = contains(Wp, [lam])
            if inperp:
                hit += 1
            V = isect(W, klein_perp([lam])) if W else []
            if t == 0:
                assert dim(V) == 0, 't = 0 but V != 0'
            elif not inperp:
                assert dim(V) == t - 1, \
                    'lambda off W^perpK but dim V != t - 1'
            else:
                assert same_space(V, W), 'lambda in W^perpK but V != W'
        assert built == ntrial, f't={t}: only {built} trials built'
        census[t] = hit
        if t >= 1:
            assert hit == 0, \
                f't={t}: {hit} admissible L landed in W^perpK'
    print(f'  [A: FREE L] admissible L with lambda in W^perpK, per t, out of '
          f'{ntrial} each:')
    print(f'      {census}  -- t = 0 is the vacuous corner (W^perpK is')
    print('      everything, V = 0, excess = 0 by (BE-56)(iii)\'s own max);')
    print('      every t >= 1 gives 0.  The middle constrains L ONLY through')
    print('      p_1, p_2, so it cannot reach a proper linear condition on')
    print('      lambda: (S2b) is IMPOSSIBLE in this regime.')

    # (B) a COINCIDENT middle: L is forced through p, and lambda IS pinned
    rowsA = rowsB = tot = 0
    for name, edges, u, v in coin_battery():
        for si in range(nseeds):
            r2 = random.Random(seed + 1009 * si)
            got, _why = coin_draw(edges, u, v, r2)
            if got is None:
                continue
            pt0, pi1, pi2, _f1, _f2 = got
            w1, w2, C = series_data(edges, u, v)
            sp = sigma_p(hat(pt0[w1]))
            # the abstract facts the regime rests on
            assert same_space(klein_perp(sp), sp), \
                'Sigma_p is not self-conjugate'
            drew = ina = 0
            for _ in range(600):
                if drew >= ndraw:
                    break
                out = coin_resweep(edges, u, v, pt0, pi1, pi2, r2)
                if out is None:
                    continue
                drew += 1
                tot += 1
                pt, planes, aux = out
                Wm, t, _, _ = rho_bar_of(C, pt, w1, w2)
                Lb = aux['Lb']
                lam = wedge2(Lb[0], Lb[1])
                inperp = contains(klein_perp(Wm), [lam]) if Wm else True
                inside = contains(sp, Wm) if Wm else True
                # THE EQUIVALENCE: lambda is pinned for every L through p
                # exactly when W sits inside Sigma_p
                assert inperp == inside, \
                    f'{name}: lambda-pinning != W inside Sigma_p'
                if inside:
                    ina += 1
            if drew:
                if ina == drew:
                    rowsA += 1
                elif ina == 0:
                    rowsB += 1
                else:
                    raise AssertionError(f'{name}: mixed case within a middle')
    assert rowsA >= 8, f'case (a) inhabited at only {rowsA} rows'
    assert rowsB >= 2, f'case (b) inhabited at only {rowsB} rows'
    print(f'  [B: COINCIDENT middle] L must pass through p = p_{{w1}} = '
          'p_{w2}')
    print('      ((BE-143)), a codimension-2 restriction the free regime')
    print('      never sees.  Lines through p span Sigma_p, which is')
    print('      SELF-CONJUGATE, so')
    print('        lambda in W^perpK for EVERY admissible L  <=>  W inside '
          'Sigma_p,')
    print(f'      asserted as an equivalence at all {tot} coincident')
    print(f'      configurations.  Case (a) W inside Sigma_p at {rowsA} '
          f'shapes,')
    print(f'      case (b) outside at {rowsB} -- BOTH inhabited by real')
    print('      window middles, R-node middles among case (a).')
    print('  VERDICT: (BE-57)(iv)\'s "no such mechanism is known" is')
    print('  REFUTED.  The mechanism is p_{w1} = p_{w2}, it pins lambda on')
    print('  the nose, and it is (S1) failing -- so the two conditions were')
    print('  never independent.  (BE-146) is what closes it.')
    print(f'  [{time.time() - t0:.0f} s]')
    return True


# ================================================== mode (BE-147)


def coin_measure(edges, pt, planes, u, v, aux):
    """Every (BE-54)/(BE-55)/(BE-56) assertion at ONE coincidence
    configuration, with the COINCIDENCE EXCESS LAW in place of (BE-56)(ii).

    `bwin.full_measure` cannot be reused here: its own
    `(BE-56)(ii): dim V > t - 1` assert FIRES at a coincident middle in case
    (a) -- the landed measurement never reached this stratum, which is the
    quantitative form of (BE-142)'s support finding.  Everything else is
    asserted identically."""
    w1, w2, C = series_data(edges, u, v)
    S, d1, _, _ = rho_bar_of(edges, pt, u, v)
    Wm, t, _, _ = rho_bar_of(C, pt, w1, w2)
    p = hat(pt[w1])
    assert p == hat(pt[w2]), 'coin_measure on a non-coincident middle'
    lu = wedge2(hat(pt[u]), p)
    lv = wedge2(hat(pt[v]), p)
    Luv = span([lu, lv])
    assert dim(Luv) == 2, 'l_u, l_v not independent'
    # (BE-54)(i) the double series peel, as an identity of SPACES
    assert same_space(S, span([lu, lv] + Wm)), \
        '(BE-54)(i): rho_bar_1 != <l_u> + W + <l_v>'
    Piu = pencil_space(hat(pt[u]), planes[u])
    Piv = pencil_space(hat(pt[v]), planes[v])
    Z = span(Piu + Piv)
    Lb = aux['Lb']
    assert same_space(k4_isect(planes[u], planes[v]), Lb), 'L != pi_u cap pi_v'
    lam = wedge2(Lb[0], Lb[1])
    mu = wedge2(hat(pt[u]), hat(pt[v]))
    # (BE-54)(ii) the perp form of Z
    assert same_space(Z, isect(klein_perp([mu]), klein_perp([lam]))), \
        '(BE-54)(ii): Z != mu^perpK cap lambda^perpK'
    # (BE-54)(iii) the modular-law factorization
    WZ = isect(Wm, Z) if Wm else []
    assert same_space(isect(S, Z), span(Luv + WZ)), \
        '(BE-54)(iii): the modular law fails'
    # (BE-55)(i) the functional vanishes on Luv; both leading lines meet L
    assert klein(lu, mu) == 0 and klein(lv, mu) == 0, \
        '(BE-55)(i): phi does not vanish on the leading lines'
    assert klein(lu, lam) == 0 and klein(lv, lam) == 0, \
        '(BE-55)(i): a leading line does not meet L'
    assert contains(Z, Luv), '(BE-55)(i): <l_u,l_v> not inside Z'
    # (BE-144) the coplanar-boundary lemma, at THIS configuration
    sigma, q, Luv2 = cover_lemma(Lb, lam, k4_span([hat(pt[u]), p]),
                                 k4_span([hat(pt[v]), p]), tag='coin')
    assert same_space(Luv, Luv2), '(BE-144): <l_u,l_v> mismatch'
    # (BE-56)(i) the Grassmann count
    V = isect(Wm, klein_perp([lam])) if Wm else []
    exc = dim(V) - dim(isect(V, Luv)) if V else 0
    assert dim(span(Wm + Luv)) == d1, 'delta_1 != dim(W + <l_u,l_v>)'
    if Wm:
        assert dim(isect(Wm, Luv)) == t + 2 - d1, \
            '(BE-56)(i): dim(W cap <l_u,l_v>) != t + 2 - delta_1'
    else:
        assert d1 == 2, '(BE-56)(i): W = 0 but delta_1 != 2'
    # (BE-147) THE COINCIDENCE EXCESS LAW, the two branches
    sp = sigma_p(p)
    assert contains(sp, Luv), '<l_u,l_v> not inside Sigma_p'
    case_a = contains(sp, Wm) if Wm else True
    if case_a:
        assert dim(V) == t, 'case (a) but V != W'
        assert d1 <= 3, 'case (a) but delta_1 > 3'
        assert exc == d1 - 2, 'case (a) but excess != delta_1 - 2'
    else:
        assert dim(V) == t - 1, 'case (b) but dim V != t - 1'
        assert exc <= max(0, d1 - 3), \
            'case (b) but excess > max(0, delta_1 - 3)'
    assert exc <= 1 or d1 >= 5, 'excess > 1 inside the window'
    # W cap Z = ker(phi | V)
    if Wm:
        assert same_space(WZ, isect(V, klein_perp([mu])) if V else []), \
            'W cap Z != ker(phi | V)'
    ident = same_space(isect(S, Z), Luv)
    return dict(d1=d1, t=t, exc=exc, ident=ident, dz=dim(Z), case_a=case_a,
                S=S, Wm=Wm, Luv=Luv, Z=Z, lu=lu, lv=lv, w1=w1, w2=w2,
                Piu=Piu, sigma=sigma, q=q)


def run_law(seed=SEED, nseeds=2, ndraw=4, nsynth=80):
    print('===== Step BE146 / (BE-147): THE COINCIDENCE EXCESS LAW -- the '
          'budget survives the pinning =====')
    print('  Sigma_p := p ^ K^4 is 3-dimensional and SELF-CONJUGATE, and')
    print('  <l_u, l_v> sits inside it (both leading lines pass through p).')
    print('  So, at a coincident middle:')
    print('   (a) W inside Sigma_p -- lambda is pinned and V = W, but')
    print('       W + <l_u,l_v> inside Sigma_p CAPS delta_1 <= 3, and then')
    print('       excess = t - (t + 2 - delta_1) = delta_1 - 2 <= 1;')
    print('   (b) W outside Sigma_p -- some line through p pairs nonzero')
    print('       with W (Sigma_p is self-conjugate), so generic L through p')
    print('       restores dim V = t - 1 and (BE-56)(iii) runs VERBATIM.')
    print('  Either way excess <= 1 in the window: the rank-one budget is')
    print('  UNTOUCHED, by a dimension cap in (a) and by genericity in (b).')
    t0 = time.time()
    import random

    # the pure linear algebra, synthetically, both branches
    rng = random.Random(seed)
    na = nb_ = 0
    for _ in range(nsynth * 40):
        if na >= nsynth and nb_ >= nsynth:
            break
        p = v4aff(rng)
        sp = sigma_p(p)
        assert same_space(klein_perp(sp), sp), 'Sigma_p not self-conjugate'
        d = rng.choice([1, 2, 3])
        rows = []
        want_a = na < nsynth
        for _ in range(d):
            if want_a:
                rows.append(wedge2(p, v4(rng)))
            else:
                rows.append(wedge2(v4(rng), v4(rng)))
        if rank_exact(rows) != d:
            continue
        W = span(rows)
        if want_a and not contains(sp, W):
            continue
        if (not want_a) and contains(sp, W):
            continue
        # lines through p span Sigma_p, so the pinning is the containment
        hits = 0
        trials = 0
        for _ in range(40):
            r = v4(rng)
            if rank_exact([p, r]) != 2:
                continue
            lam = wedge2(p, r)
            trials += 1
            if contains(klein_perp(W), [lam]):
                hits += 1
        if trials < 8:
            continue
        if want_a:
            assert hits == trials, 'case (a) but some L through p is unpinned'
            na += 1
        else:
            assert hits < trials, 'case (b) but every L through p is pinned'
            nb_ += 1
    assert na == nsynth and nb_ == nsynth, \
        f'synthetic branches built {na}/{nb_} of {nsynth}'
    print(f'  [linear algebra] {na} case-(a) and {nb_} case-(b) abstract W')
    print('      per branch: pinning at EVERY line through p iff W inside')
    print('      Sigma_p, asserted both ways.')

    # the law at real coincident window middles
    cens = {}
    rowsA = rowsB = tot = idn = 0
    for name, edges, u, v in coin_battery():
        for si in range(nseeds):
            r2 = random.Random(seed + 1009 * si)
            got, why = coin_draw(edges, u, v, r2)
            if got is None:
                if si == 0:
                    print(f'  {name}: SKIPPED ({why})')
                continue
            pt0, pi1, pi2, _f1, _f2 = got
            drew = na_ = 0
            d1s = set()
            for _ in range(600):
                if drew >= ndraw:
                    break
                out = coin_resweep(edges, u, v, pt0, pi1, pi2, r2)
                if out is None:
                    continue
                drew += 1
                tot += 1
                pt, planes, aux = out
                m = coin_measure(edges, pt, planes, u, v, aux)
                d1s.add((m['d1'], m['t'], m['exc'], m['case_a']))
                key = ('a' if m['case_a'] else 'b', m['d1'], m['t'], m['exc'])
                cens[key] = cens.get(key, 0) + 1
                if m['ident']:
                    idn += 1
                if m['case_a']:
                    na_ += 1
            if drew:
                if na_ == drew:
                    rowsA += 1
                else:
                    rowsB += 1
                tag = 'a' if na_ == drew else 'b'
                print(f'  {name} [seed {si}]: case ({tag}), {drew} draws, '
                      f'(d1,t,exc) {sorted({(x[0], x[1], x[2]) for x in d1s})}')
    assert rowsA >= 8 and rowsB >= 2, \
        f'branches inhabited {rowsA}/{rowsB} at real middles'
    print(f'  [(case, delta_1, t, excess) census over {tot} coincident '
          'configurations]')
    print(f'      {dict(sorted(cens.items()))}')
    print(f'  [case (a) at {rowsA} shape-seeds -- delta_1 <= 3 and')
    print(f'   excess = delta_1 - 2 at EVERY one; case (b) at {rowsB},')
    print('   dim V = t - 1 restored and (BE-56)(iii) verbatim]')
    print(f'  [the identity held at {idn} of {tot}; every failure is a')
    print('   delta_1 >= 5 row, which (BE-56)(iv) REQUIRES to fail]')
    print(f'  [{time.time() - t0:.0f} s]')
    return True


# ================================================== mode (BE-148)


def run_ident(seed=SEED, nseeds=2, ndraw=5):
    print('===== Step BE147 / (BE-148): (S1) IS REMOVABLE -- the window '
          'identity AT the excluded configurations =====')
    print('  (BE-57)(i) used p_1 != p_2 only to make l_u, l_v skew.  With')
    print('  (BE-144) covering the non-skew case and (BE-147) covering the')
    print('  pinning, the hypothesis is DELETABLE.  Here the identity')
    print('  rho_bar_1 cap Z = <l_u, l_v> is verified END TO END at')
    print('  coincident middles -- configurations the theorem\'s own')
    print('  hypothesis excluded -- with every step of *Steps BE53-BE56*')
    print('  asserted at each ((BE-147)\'s `coin_measure`).')
    t0 = time.time()
    import random
    rows = tot = idn = win = 0
    firing = 0
    cens = {}
    for name, edges, u, v in coin_battery():
        for si in range(nseeds):
            rng = random.Random(seed + 1009 * si)
            got, why = coin_draw(edges, u, v, rng)
            if got is None:
                if si == 0:
                    print(f'  {name}: SKIPPED ({why})')
                continue
            pt0, pi1, pi2, _f1, _f2 = got
            drew = 0
            for _ in range(800):
                if drew >= ndraw:
                    break
                out = coin_resweep(edges, u, v, pt0, pi1, pi2, rng)
                if out is None:
                    continue
                pt, planes, aux = out
                m = coin_measure(edges, pt, planes, u, v, aux)
                drew += 1
                tot += 1
                assert m['dz'] == 4, f'{name}: dim Z != 4'
                key = (m['d1'], m['t'], m['exc'])
                cens[key] = cens.get(key, 0) + 1
                if m['ident']:
                    idn += 1
                if m['d1'] <= 4:
                    win += 1
                    assert m['ident'], \
                        f'{name}: delta_1 <= 4 but the identity FAILED'
                    assert same_space(isect(m['S'], m['Piu']),
                                      span([m['lu']])), f'{name}: (b1) failed'
                else:
                    assert not m['ident'], \
                        f'{name}: delta_1 >= 5 but the identity HELD ' \
                        '((BE-56)(iv) requires failure)'
                # the LANDED measurement's own (BE-56)(ii) assert on this row
                try:
                    full_measure(edges, pt, planes, u, v)
                except AssertionError as e:
                    if '(BE-56)(ii)' in str(e):
                        firing += 1
                    else:
                        raise
            if drew:
                rows += 1
                print(f'  {name} [seed {si}]: {drew} draws, dim Z = 4, '
                      f'identity at every delta_1 <= 4 row')
    assert rows >= 16, f'fewer than sixteen rows ({rows})'
    assert win > 0, 'no in-window coincident row was reached'
    print(f'  [(delta_1, t, excess) census over {tot} coincident '
          f'configurations] {dict(sorted(cens.items()))}')
    print(f'  [{win} rows have delta_1 <= 4 and the identity holds at ALL of')
    print(f'   them; {tot - win} have delta_1 >= 5 and it fails at all of')
    print('   them, as (BE-56)(iv) requires -- so the driver is')
    print('   non-vacuous in BOTH directions]')
    print(f'  [{firing} of {tot} rows make `bwin.full_measure`\'s own')
    print('   (BE-56)(ii) assert FIRE -- the landed measurement could not')
    print('   have run here, which is (BE-142)\'s support finding measured]')
    print('  VERDICT: the theorem\'s conclusion holds where its hypothesis')
    print('  said nothing.  (S1) is REMOVABLE, not merely true.')
    print(f'  [{time.time() - t0:.0f} s]')
    return True


def run_board():
    print('===== Step BE147 / (BE-148), continued: the price, the board, and '
          'the support audit =====')
    print('  RESEARCH-ARC s4 + s5.  Every population, what it VARIES, what it')
    print('  HOLDS FIXED, and which of the claim\'s own quantifiers it')
    print('  therefore reaches.')
    pops = [
        ('(BE-142) support',
         'nothing -- it reads the SOURCE of three landed guards and the end '
         'sampler, plus one constructed witness',
         'nothing sampled: `inspect.getsource` on the filter lines',
         'reaches the claim exactly, because the claim is ABOUT the support'),
        ('(BE-143) incid',
         'the middle configuration and the end datum (L, pi_u, pi_v, p_u, '
         'p_v) at 20 shape-seeds',
         'the COINCIDENCE itself (that IS the stratum) and pi_1 != pi_2',
         'reaches "coincidence forces the meeting-lines regime".  It does '
         'NOT reach "some middle FORCES coincidence" -- not claimed anywhere'),
        ('(BE-144) cover',
         'sigma, L and the two leading lines, in THREE independent '
         'populations: pi_1 = pi_2 synthetic / arbitrary non-skew synthetic '
         '/ real coincident middles',
         'only the non-skewness the lemma is about',
         'reaches the lemma.  The second population is the one that shows '
         'sigma is not forced to be a boundary plane, which is the whole '
         'content of "plane-agnostic"'),
        ('(BE-145) crit',
         'pi_1, pi_2, p_1, p_2 and L independently, 200 draws',
         'nothing; both forcing mechanisms are CONSTRUCTED, never drawn',
         'the criterion is reached per draw.  EXHAUSTIVENESS is reached by '
         'the 2x2 enumeration plus a dense-open-vs-proper-closed argument, '
         'NOT by the sample -- a sample can never establish "the only"'),
        ('(BE-146) pin',
         'W at every t = 0..5 and L over the admissible dense open (regime '
         'A); the coincident middle and its ends at 20 shape-seeds '
         '(regime B)',
         'nothing in A; the coincidence in B',
         'regime A reaches "no admissible free L lands in W^perpK" only as '
         'NOT-FOUND-UNDER-CAP -- the PROOF is the proper-closed argument, '
         'and the census corroborates in the safe direction ((BE-37)(i)(2)). '
         'Regime B reaches the EQUIVALENCE (pinned iff W inside Sigma_p) as '
         'a per-draw assertion, and both branches are inhabited'),
        ('(BE-147) law',
         'abstract W in both branches (80 each) and the real coincident '
         'middles',
         'the coincidence',
         'reaches the law.  Case (a) is a THEOREM (a dimension cap), so its '
         'rows corroborate rather than carry it; case (b) is a genericity '
         'statement and its rows exhibit the restored slice'),
        ('(BE-148) ident',
         'the coincident middle and the ends over it, 100 configurations',
         'the coincidence; deg(u) = deg(v) = 1 (bwin\'s own cap)',
         'reaches the identity AT the excluded stratum, which is what the '
         'REMOVAL needs -- and it is non-vacuous in both directions (the '
         'delta_1 >= 5 rows must FAIL, and do)'),
    ]
    for tag, varies, fixed, reach in pops:
        print(f'  {tag}')
        print(f'      varies : {varies}')
        print(f'      fixed  : {fixed}')
        print(f'      reaches: {reach}')
    print('  STANDING CAPS, disclosed rather than smoothed:')
    print('   1. Every battery piece has deg(u) = deg(v) = 1 -- bwin\'s own')
    print('      disclosed cap, inherited through `series_data`.  The general')
    print('      A-side is (BE-57)(ii)\'s PGL(4) move: prose then, prose now.')
    print('   2. The coincidence sampler supports middles whose branch set is')
    print('      INDEPENDENT with every free vertex carrying at most one')
    print('      branch neighbour -- `bearcase.sample_piece_config`\'s shape')
    print('      guard, NOT a claim about the window\'s extent.  TWO of')
    print('      BWIN\'s twelve `wide` rows fall outside it (the two')
    print('      short-bridge theta chains); the two longer-bridge chains')
    print('      added here are the repair, and BOTH R-node middles and the')
    print('      four-branch theta are INSIDE it.')
    print('   3. NO coincident row here has delta_1 = 4.  In case (a) that is')
    print('      a THEOREM, not a gap -- Sigma_p caps delta_1 <= 3.  In case')
    print('      (b) a delta_1 = 4 coincident middle is UNWITNESSED AT A')
    print('      GRAPH MIDDLE under this cap (the four case-(b) rows all')
    print('      measure delta_1 = 5, outside the window), and it is covered')
    print('      by (BE-56)(iii) verbatim rather than by a row.')
    print('   4. NO coincident middle here is claimed delta_1-ATTAINING.')
    print('      (BE-148) does not need one: with (S1) deleted the theorem')
    print('      quantifies over the attaining middle whatever its boundary')
    print('      points do.  Whether the coincidence locus can ATTAIN is')
    print('      OPEN and, after the removal, IMMATERIAL.')
    print('   5. Every figure is a count over CONSTRUCTED populations.  None')
    print('      is a class-level rate, and no shape count is a statement')
    print('      about the window\'s extent ((BE-58)(i) owns that).')
    print('  THE BOARD after this landing:')
    print('   * (S1) -- REMOVABLE.  Not a hypothesis: (BE-57)(i) holds')
    print('     without it, on the window\'s own regime.  Its evidence')
    print('     sentence is STRUCK as circular ((BE-142)).')
    print('   * (S2), first half -- PROVED, mechanism list EXHAUSTIVE at two')
    print('     ((BE-145)), and (BE-55)(iii)\'s argument covers both')
    print('     ((BE-144)).')
    print('   * (S2), second half -- the clause\'s "no such mechanism is')
    print('     known" is REFUTED: p_{w1} = p_{w2} pins lambda onto W^perpK')
    print('     at real window middles ((BE-146)).  It is CLOSED by the')
    print('     coincidence excess law ((BE-147)), which replaces the')
    print('     generic slice by a DIMENSION CAP rather than repairing it.')
    print('   * (BE-57)(iv) as a whole -- SUPERSEDED.  The window\'s class')
    print('     theorem is UNCONDITIONAL on the window\'s own regime')
    print('     (cross-incidence-free flags, dim Z = 4).')
    print('   * WHAT DOES NOT MOVE: half (B) at side-degree >= 2, S-mark,')
    print('     (BE-14), hbareSplit, the 2-cut step, cross-pair welding,')
    print('     (BE-32)(+), (BE-58)(i)-(iv), and EVERY landed measurement.')
    print('   * WHAT (BE-14) STILL NEEDS: half (B) at side-degree >= 2,')
    print('     whose obstruction is the METHOD ((BE-139)).  Closing (S1)')
    print('     and (S2) does NOT close S-mark.')
    return True


MODES = {'support': run_support, 'incid': run_incid, 'cover': run_cover,
         'crit': run_crit, 'pin': run_pin, 'law': run_law,
         'ident': run_ident, 'board': run_board}


def run_validate():
    t0 = time.time()
    for k in ('support', 'incid', 'cover', 'crit', 'pin', 'law', 'ident',
              'board'):
        MODES[k]()
        print()
    print(f'== validate: all eight modes PASSED [{time.time() - t0:.1f}s]')
    return True


def main(argv):
    if not argv or (argv[0] not in MODES and argv[0] != 'validate'):
        print(__doc__)
        print('modes: ' + ' | '.join(sorted(MODES)) + ' | validate')
        return 0
    print(f'bscond.py {argv[0]}  (seed literal {SEED}; exact Q; both gates '
          'on every drawn configuration)')
    if argv[0] == 'validate':
        run_validate()
    else:
        MODES[argv[0]]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
