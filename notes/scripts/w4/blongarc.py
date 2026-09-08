"""
Direction BLONGARC (BRANKV's own named successor) -- DOES THE ARC LADDER
EXTEND PAST LENGTH 3?  The dispatch's question: at `|arc_j| >= 4`, is
`rank(B|_U) <= 2` FORCED on the 4-dimensional `U = <l_j> + W_j` at a legal
chart point?

  THE LITERAL ANSWER IS **NO**, and (BE-193)(iv) named the reason.  But the
  LADDER EXTENDS ANYWAY, by TWO rungs, and past them the stop is EXACT and
  STRUCTURAL rather than a cap.  Said at the top:

  (BE-196) THE OBJECT WAS SLIGHTLY WRONG, and correcting it is free.
           `Pi_x = <l_j, l_{j'}>` where `l_{j'}` is the OTHER star line at
           `x` (the hinge to the other side-neighbour), so `l_j in Pi_x`
           ALREADY and

               Pi_x <= U   <==>   l_{j'} in U,

           ONE membership rather than a 2-space embedding.  And
           `Pi_x <= alpha_x := p_x ^ K^4`, the ALPHA-SPACE of all lines
           through `q_x` -- a 3-dimensional TOTALLY SINGULAR subspace -- so
           the containment lives in `U cap alpha_x` and nowhere else.  The
           general band: `B(l_k, l_k) = B(l_k, l_{k+1}) = 0` along any arc,
           so EVERY consecutive pair spans a totally singular 2-space, of
           which (BE-191)(i) is the `n = 3` case.

  (BE-197) THE DISPATCH'S QUESTION, ANSWERED: **NO**.  At `|arc_j| = 4` the
           Gram matrix on `(l_1, l_2, l_3, l_4)` is

               [[0, 0, a, b], [0, 0, 0, c], [a, 0, 0, 0], [b, c, 0, 0]],
               a = B(l_1, l_3),  b = B(l_1, l_4),  c = B(l_2, l_4),

           so `det = (a c)^2` and `rank(B|_U) = 2 * rank([[a, b], [0, c]])`
           -- always EVEN, never 3, and equal to **4** whenever `a != 0` and
           `c != 0`.  Those vanish exactly when four CONSECUTIVE arc bodies
           are coplanar: a proper closed condition, and one
           `assert_generic_star` does NOT forbid (it forbids COLLINEARITY at
           a body, strictly stronger).  So rank 4 is GENERIC (60/60) and
           `rank(B|_U) <= 2` is NOT forced.

  (BE-198) AND (BE-193)(iv)'s WARRANT IS STRONGER THAN IT WAS STATED.  It
           said a *nondegenerate* rank-4 form "does admit totally singular
           2-spaces (the hyperbolic case)" -- true only IF hyperbolic, which
           over Q is a discriminant condition.  Here the ARC SUPPLIES THE
           SPLITTING: `U = <l_1, l_2> + <l_3, l_4>` with BOTH summands
           totally singular (consecutive hinges meet), so `U` is hyperbolic
           over ANY field with no discriminant condition, `rad(U) = 0`, and
           its totally singular 2-spaces are exactly TWO `P^1`-rulings --
           CONSTRUCTED below, never sampled.  The isotropic 2-plane the
           dispatch asked to see exhibited is the arc's OWN consecutive pair
           `<l_1, l_2>`.

  (BE-199) THE PERP-REDUCTION, and it is where the radical still bites.
           `l_j in Pi_x` and `Pi_x` is totally singular, so
           `Pi_x <= U^(1) := U cap l_j^perp`, with `l_j in rad(U^(1))` for
           free; and `alpha_x <= l_j^perp` too, so
           `U cap alpha_x = U^(1) cap alpha_x`.  The object the radical
           argument wants is `U^(1)`, NOT `U`.  Generically
           `dim U^(1) = n - 1` (n >= 3) and `dim Ubar = n - 2` for
           `Ubar := U^(1)/<l_j>`.

  (BE-200) SO THE RADICAL LADDER EXTENDS TO ARC 4, with a forced incidence of
           (BE-193)(i)'s OWN SHAPE.  At `n = 4` and `a c != 0`, `Ubar` is a
           HYPERBOLIC rank-2 plane, so its isotropic cone is EXACTLY TWO
           lines and `Pi_x` has exactly TWO candidates:
             * `<l_1, l_2>`, which puts `l_{cw} in Pi_x`, i.e. `q_x, q_c,
               q_w` COLLINEAR -- forbidden by `assert_generic_star` at `c`;
             * `<l_1, a l_4 - b l_3>` = `<l_1, p_z ^ (a p_y + b p_w)>`,
               whose second generator is a line through `q_z` and must be a
               line through `q_x`, hence `= q_x v q_z`, hence

                   |arc_j| = 4 and Pi_x <= rho_bar_i
                       ==>  q_z in pi_x AND q_x, q_w, q_z, q_y coplanar,

               `q_z in pi_x` being ONE LINEAR equation of exactly
               (BE-193)(i)'s shape, at the arc's SECOND-TO-LAST body.  The
               confinement is PROPER (the containment locus is empty at a
               generic arc-4 draw, 960/960 second star points) and INHABITED
               (24 of 24 GATED composite chart points, fully planar) -- so
               the POINTWISE clause is FALSE at arc 4 as well, extending
               (BE-192) one arc-edge along.

  (BE-201) AND ONE MASTER INVARIANT SUBSUMES THE WHOLE LADDER:

               dim(U cap alpha_x) = max(1, min(n, 6) - 3)   generically,

           asserted at every n in 2..7.  Since `Pi_x <= alpha_x` always,
           `Pi_x <= U` needs `dim(U cap alpha_x) >= 2`.  So the containment
           is IMPOSSIBLE at a generic arc of length `<= 4`; at `n = 5` it is
           ONE linear condition on the OTHER side-neighbour; and at
           `n >= 6` it is AUTOMATIC, `U cap alpha_x` being all of `alpha_x`.
           Hence (BE-190) (n = 2), (BE-191)/(BE-193) (n = 3), (BE-200)
           (n = 4) and the arc-5 closure are FOUR CASES OF ONE COUNT.

  (BE-202) THE TWO MECHANISMS HAVE DIFFERENT BOUNDARIES, and both are exact.
           The RADICAL/quotient mechanism confines `Pi_x` to a FINITE
           candidate list exactly while `dim Ubar <= 2`, i.e. `n <= 4`
           (0 candidates at n = 2, 1 at n = 3, 2 at n = 4); at `n = 5`
           `Ubar` is a nondegenerate TERNARY form and the locus is a CONIC --
           a `P^1` of candidates, CONSTRUCTED here from the rational point
           `l_2` by the secant parametrization, so the "not finite" claim is
           built rather than asserted.  The ALPHA-SPACE mechanism reaches
           `n = 5`: `Bad <= Z_n := {rank[l_1, .., l_n, l_{j'}] <= n}`, a
           determinantal CLOSED condition, PROPER exactly when rank `n + 1`
           is achievable, i.e. exactly when `n <= 5`.
           **THE BOUNDARY IS `n = 6`, AND IT IS (BE-189)(iii)'s OWN
           THRESHOLD**: `rho_i <= dist` makes the clause's conclusion
           `rho_i = 6` UNREACHABLE at `dist <= 5`, so the path-bound family
           of arguments closes exactly the strata on which the clause is
           VACUOUS and provably cannot reach the strata on which it has
           CONTENT.  A structural stop, not a cap.

  (BE-203) THE CLOSURE, PRICED.  On the same 99-configuration / 783-point
           population BARCH/BGPROP/BRANKV measure (reproduced here at the
           same seeds), arc `<= 4` covers **36 of 99** landed configurations
           and arc `<= 5` covers **48 of 99**, against BRANKV's 15.
           `dist(x, y) = min_j |arc_j|` is ASSERTED, not assumed, so a
           `dist <= 5` configuration really does carry an arc of length
           `<= 5` through a side-neighbour of `x`.  Properness is WITNESSED:
           `l_{j'} in U` fires at 0 of the 378 arc-`<= 5` points and at
           405 of 783 overall -- exactly the 405 points with `dist >= 6`.

  MODES.  form | perp | ladder | pop | validate  (the last runs all four)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.  No `.lean` is touched.

  CONSTRUCT, DO NOT SAMPLE -- the trap BRANKV self-caught and recorded
  (`RESEARCH-ARC.md` section 4).  Every claim below about WHICH subspaces
  exist is tested by BUILDING the candidate family in closed form (the two
  rulings of `U`; the isotropic cone of `Ubar` as a parametrized family; the
  conic at `n = 5` by its explicit rational parametrization) and asserting
  membership on each constructed member.  No claim of the form "no such
  subspace exists" is backed by a random draw anywhere in this file.

  WHICH CONJUNCTS ARE TESTED.  (PENCIL-SATURATES-CHART) at `k = 2` is
  `c_i(Pi_x) = 2  ==>  rho_i = 6`, a two-conjunct hypothesis-plus-conclusion
  reading, and `pop` reads BOTH: `c_i(Pi_x) = 2` as `contains(rho_bar_i,
  Pi_x)` AND `rho_i` from `rho_bar_of`, never dropped.  It ALSO reads the two
  (BE-189) ceilings as asserts, so the population identity with BRANKV's is
  checkable rather than claimed.

  THREE RECORDED HARNESS HAZARDS, all navigated rather than fixed
  (`notes/scripts/README.md` *Harness debt*):
    * `bimage.pt_in` truncates to K^4 with no assert -- every use below is on
      the width-4 fibre basis `bdegtwo.fibre_k` returns, which is what it is
      FOR;
    * `bimage.span`/`dim`/`isect` fire their width-6 special case on RANK,
      not width -- every subspace built here is width 6 (`Lambda^2 K^4`), and
      every width-4 rank question goes through `exactcore.rank` instead;
    * `bwin.dehom` returns a LIST -- `bwin` is not imported and the one
      dehomogenizer used is `barch._aff3`, which returns a TUPLE.
"""

import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, nullspace, rank, wedge2, neighbors            # noqa: E402
from bimage import contains, dim, isect, pt_in, rho_bar_of, span         # noqa: E402
from bimage import plane_at                                              # noqa: E402
from bunif import SEED                                                   # noqa: E402
from pitch import Q, klein                                               # noqa: E402
from bdegtwo import fibre_k                                              # noqa: E402
from barch import _aff3, library, side_row, star_holds, shortest_path    # noqa: E402
from brankv import arc_through, gram, gram_rank, hinge                   # noqa: E402
from kbare_common import verts_of                                        # noqa: E402


# ================================================== structural helpers

def perp_in(U, v):
    """`U cap v^perp` under the KLEIN form -- the (BE-199) reduction.  `U` is
    a width-6 basis; the answer is a width-6 basis of the same subspace type,
    so no width hazard is reachable."""
    if not U:
        return []
    co = [klein(u, v) for u in U]
    if all(x == 0 for x in co):
        return [u[:] for u in U]
    ks = nullspace([co])
    return span([[sum(k[i] * U[i][t] for i in range(len(U)))
                  for t in range(6)] for k in ks])


def radical(U):
    """`rad(B|_U) = {u in U : B(u, U) = 0}`, returned in AMBIENT coordinates."""
    if not U:
        return []
    ks = nullspace(gram(U))
    if not ks:
        return []
    return span([[sum(k[i] * U[i][t] for i in range(len(U)))
                  for t in range(6)] for k in ks])


def quotient_form(U, r):
    """The Gram matrix induced on `U/<r>` for `r` a single radical generator,
    together with the lifted basis.  `U` is a basis of a subspace containing
    `r`; the returned lift is a list of ambient vectors whose classes are a
    basis of the quotient."""
    lift = []
    for u in U:
        if dim(span([r] + lift + [u])) == len(lift) + 2:
            lift.append(u[:])
    return [[klein(a, b) for b in lift] for a in lift], lift


def arc_pts(rng, n, s=9):
    """`n + 1` points in general position: the bodies of an arc of length
    `n`, `q_x = P[0]`, ..., `q_y = P[n]`."""
    for _ in range(60):
        P = [[F(rng.randint(-s, s)) for _ in range(3)] + [F(1)]
             for _ in range(n + 1)]
        if all(rank([P[i], P[j]]) == 2 for i in range(n + 1)
               for j in range(i + 1, n + 1)):
            if all(rank([P[i], P[i + 1], P[i + 2]]) == 3
                   for i in range(n - 1)):
                return P
    return None


def arc_lines(P):
    """The hinge lines of the arc through the points `P`."""
    return [wedge2(P[i], P[i + 1]) for i in range(len(P) - 1)]


# ======================================================== mode: form
# (BE-196)/(BE-197)/(BE-198): the band, the arc-4 Gram, and the
# UNCONDITIONAL hyperbolic splitting.  The dispatch's question is answered
# here.

def run_form(ndraw=60, nmax=6, seed=SEED):
    t0 = time.time()
    print(f'== form: (BE-196)-(BE-198) the band, the arc-4 Gram, the '
          f'splitting, seed {seed}')
    rng = random.Random(seed + 4441)
    # the two harness `klein`s agree -- checked once rather than assumed.
    for _ in range(6):
        u = [F(rng.randint(-5, 5)) for _ in range(6)]
        v = [F(rng.randint(-5, 5)) for _ in range(6)]
        from bimage import klein as klein_bi
        assert klein(u, v) == klein_bi(u, v), \
            'pitch.klein and bimage.klein disagree'

    # ---- (BE-196): the BAND, at every arc length 2..nmax.
    band, ts_pairs, dimU = 0, 0, {}
    for n in range(2, nmax + 1):
        for _ in range(ndraw // 4):
            P = arc_pts(rng, n)
            if P is None:
                continue
            L = arc_lines(P)
            G = gram(L)
            for k in range(n):
                assert G[k][k] == 0, '(BE-196): a hinge is not a line'
                assert Q(L[k]) == 0, '(BE-196): Q of a hinge is not 0'
            for k in range(n - 1):
                assert G[k][k + 1] == 0, \
                    '(BE-196): a consecutive hinge pair failed to meet'
                # ... hence every consecutive PAIR spans a totally singular
                #     2-space.  CONSTRUCTED, over the whole pair family.
                pr = span([L[k], L[k + 1]])
                assert dim(pr) == 2, '(BE-196): a consecutive pair collapsed'
                assert gram_rank(pr) == 0, \
                    '(BE-196): a consecutive pair is not totally singular'
                ts_pairs += 1
            band += 1
            d = dim(span(L))
            dimU[(n, d)] = dimU.get((n, d), 0) + 1
    print(f'  (BE-196) the band `B(l_k,l_k) = B(l_k,l_{{k+1}}) = 0` asserted '
          f'at {band}/{band} arcs of lengths 2..{nmax},')
    print(f'  and EVERY consecutive pair spans a totally singular 2-space at '
          f'{ts_pairs}/{ts_pairs} pairs -- CONSTRUCTED,')
    print('  the whole family, not sampled.  `(n, dim U)` census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dimU.items())))
    assert all(k[1] == min(k[0], 6) for k in dimU), \
        '(BE-202): dim U is not min(n, 6) at a generic arc'

    # ---- (BE-197): the arc-4 Gram, det = (ac)^2, rank in {0,2,4}.
    n4, r4, rk = 0, 0, {}
    for _ in range(ndraw):
        P = arc_pts(rng, 4)
        if P is None:
            continue
        L = arc_lines(P)
        U = span(L)
        if dim(U) != 4:
            continue
        G = gram(L)
        a, b, c = G[0][2], G[0][3], G[1][3]
        assert G[0][1] == G[1][2] == G[2][3] == 0, 'the band failed'
        assert [G[k][k] for k in range(4)] == [F(0)] * 4, 'a diagonal failed'
        # det of [[0,Y],[Y^T,0]] with Y = [[a,b],[0,c]] is (det Y)^2.
        assert _det4(G) == (a * c) ** 2, \
            '(BE-197): det(B|_U) is not (a c)^2'
        rr = rank(G)
        assert rr == 2 * rank([[a, b], [F(0), c]]), \
            '(BE-197): rank(B|_U) is not 2 rank(Y)'
        assert rr in (0, 2, 4), '(BE-197): an ODD Gram rank appeared'
        rk[rr] = rk.get(rr, 0) + 1
        # the vanishing of a / c IS a coplanarity of four consecutive bodies.
        assert (a == 0) == (rank([P[0], P[1], P[2], P[3]]) == 3), \
            '(BE-197): a = 0 is not coplanar(x, c, w, z)'
        assert (c == 0) == (rank([P[1], P[2], P[3], P[4]]) == 3), \
            '(BE-197): c = 0 is not coplanar(c, w, z, y)'
        if rr == 4:
            r4 += 1
            assert radical(U) == [], '(BE-197): rank 4 with a radical'
        n4 += 1
    print(f'  (BE-197) at {n4} generic arc-4 draws: `det(B|_U) = (a c)^2` '
          f'and `rank = 2 rank(Y)` asserted at {n4}/{n4},')
    print('  the rank is EVEN at every draw (never 3), and `a = 0` / `c = 0` '
          'are exactly the coplanarity of')
    print('  four CONSECUTIVE arc bodies.  Rank census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(rk.items())))
    print(f'  ** SO THE DISPATCH\'S QUESTION IS ANSWERED **NO**: '
          f'`rank(B|_U) = 4` at {r4} of {n4} generic draws, and')
    print('  `rank(B|_U) <= 2` is a PROPER CLOSED condition (two coplanarity '
          'determinants), not a forced one.')
    assert r4 == n4 and n4 >= 20, \
        '(BE-197): rank 4 is not generic on this draw set'

    # ---- (BE-198): the UNCONDITIONAL hyperbolic splitting and the two
    #      rulings, CONSTRUCTED.
    nsp, nrul, cross = 0, 0, 0
    for _ in range(ndraw // 2):
        P = arc_pts(rng, 4)
        if P is None:
            continue
        L = arc_lines(P)
        U = span(L)
        if dim(U) != 4 or gram_rank(L) != 4:
            continue
        Pca, Pcb = span([L[0], L[1]]), span([L[2], L[3]])
        assert gram_rank(Pca) == 0 and gram_rank(Pcb) == 0, \
            '(BE-198): a summand is not totally singular'
        assert dim(Pca + Pcb) == 4 and dim(isect(Pca, Pcb)) == 0, \
            '(BE-198): the splitting is not direct'
        nsp += 1
        # THE TWO RULINGS, CONSTRUCTED in the 2x2-matrix model.  Normalize
        # the basis so that `B` pairs `e1 <-> e3` and `e2 <-> e4` and nothing
        # else:  e1 = l_1, e2 = l_2, e3 = l_3, e4 = a l_4 - b l_3.  Then
        # `Q/2 = a (x z + c y w)` in those coordinates, i.e. `Q = det M` for
        # `M = [[x, -c w], [y, z]]`, so the totally singular 2-spaces are
        # exactly the rank-<=1 matrices with a FIXED column space (ruling A)
        # or a FIXED row space (ruling B) -- two `P^1`-families, BUILT below
        # rather than searched for.
        G = gram(L)
        a, b, c = G[0][2], G[0][3], G[1][3]
        e1, e2, e3 = L[0], L[1], L[2]
        e4 = [a * L[3][t] - b * L[2][t] for t in range(6)]
        E = [e1, e2, e3, e4]
        H = [[klein(u, v) for v in E] for u in E]
        assert H[0][2] == a and H[1][3] == a * c, \
            '(BE-198): the normalization did not produce the pairing'
        assert (H[0][1] == H[0][3] == H[1][2] == H[2][3] == 0
                and H[0][0] == H[1][1] == H[2][2] == H[3][3] == 0), \
            '(BE-198): the normalized Gram is not hyperbolic'
        for (u0, u1) in ((F(1), F(0)), (F(0), F(1)), (F(1), F(2)),
                         (F(3), F(-1)), (F(1), F(1))):
            A = [[u0 * e1[t] + u1 * e2[t] for t in range(6)],
                 [c * u1 * e3[t] - u0 * e4[t] for t in range(6)]]
            Bt = [[c * u0 * e1[t] - u1 * e4[t] for t in range(6)],
                  [u0 * e2[t] + u1 * e3[t] for t in range(6)]]
            for W in (A, Bt):
                W = span(W)
                assert dim(W) == 2, '(BE-198): a ruling member collapsed'
                assert gram_rank(W) == 0, \
                    '(BE-198): a CONSTRUCTED ruling member is not totally ' \
                    'singular'
                assert contains(U, W), '(BE-198): a ruling member left U'
                nrul += 1
            assert dim(isect(span(A), span(Bt))) == 1, \
                '(BE-198): the two rulings do not meet in a line'
            cross += 1
    print(f'  (BE-198) the splitting `U = <l_1,l_2> + <l_3,l_4>` into TWO '
          f'totally singular 2-spaces asserted')
    print(f'  at {nsp}/{nsp} nondegenerate arc-4 draws -- so `U` is '
          f'HYPERBOLIC over ANY field, with NO discriminant')
    print(f'  condition, and `rad(U) = 0`.  {nrul} CONSTRUCTED ruling members '
          f'each asserted totally singular and')
    print(f'  inside `U`; the two rulings meet in a line at {cross}/{cross}. '
          f'The isotropic 2-plane the dispatch')
    print('  asked to see exhibited is the arc\'s OWN consecutive pair '
          '`<l_1, l_2>`.')
    assert nsp >= 10 and nrul >= 50, '(BE-198) did not run'
    print(f'  form: {time.time() - t0:.1f}s')
    return n4


def _det4(G):
    """Exact 4x4 determinant by cofactor expansion (no float, no pivoting)."""
    def det3(M):
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    tot = F(0)
    for j in range(4):
        minor = [[G[i][k] for k in range(4) if k != j] for i in range(1, 4)]
        tot += (F(-1) ** j) * G[0][j] * det3(minor)
    return tot


# ======================================================== mode: perp
# (BE-199)/(BE-200): the perp-reduction, and the arc-4 theorem.

def run_perp(ndraw=40, seed=SEED):
    t0 = time.time()
    print(f'== perp: (BE-199)/(BE-200) the perp-reduction and the arc-4 '
          f'theorem, seed {seed}')
    rng = random.Random(seed + 7717)
    npx, nq, nforce, nempty, nsweep = 0, 0, 0, 0, 0
    for _ in range(ndraw):
        P = arc_pts(rng, 4)
        if P is None:
            continue
        L = arc_lines(P)
        U = span(L)
        if dim(U) != 4 or gram_rank(L) != 4:
            continue
        px = P[0]
        G = gram(L)
        a, b, c = G[0][2], G[0][3], G[1][3]
        # ---- (BE-196): `Pi_x` CONTAINS `l_j`, so the containment is ONE
        #      membership.  Built from a second star line at `x`, swept.
        for _try in range(8):
            u = [F(rng.randint(-9, 9)) for _ in range(3)] + [F(1)]
            if rank([px, P[1], u]) == 3:
                break
        Pix = span([L[0], wedge2(px, u)])
        assert dim(Pix) == 2 and gram_rank(Pix) == 0, 'Pi_x is malformed'
        assert contains(Pix, [L[0]]), '(BE-196): l_j is not in Pi_x'
        assert contains(U, Pix) == contains(U, [wedge2(px, u)]), \
            "(BE-196): `Pi_x <= U` is not `l_{j'} in U`"
        # ---- (BE-199): every element of `Pi_x` meets `l_j` (both pass
        #      through `q_x`), so `Pi_x <= l_j^perp`.
        for (s1, s2) in ((F(1), F(0)), (F(0), F(1)), (F(2), F(3)),
                         (F(-1), F(4))):
            m = [s1 * Pix[0][t] + s2 * Pix[1][t] for t in range(6)]
            assert klein(L[0], m) == 0, \
                '(BE-199): an element of Pi_x is not perp to l_j'
        npx += 1
        Uperp = perp_in(U, L[0])
        assert dim(Uperp) == 3, '(BE-199): dim(U cap l_j^perp) is not 3 at n = 4'
        rd = radical(Uperp)
        assert dim(rd) == 1 and contains(rd, [L[0]]), \
            '(BE-199): rad(U cap l_j^perp) is not <l_j>'
        assert gram_rank(Uperp) == 2, '(BE-199): U^(1) is not of rank 2'
        # ---- (BE-200): the quotient `Ubar = U^(1)/<l_j>` on the EXPLICIT
        #      lift `(l_2, vsec)`, `vsec = a l_4 - b l_3`.
        vsec = [a * L[3][t] - b * L[2][t] for t in range(6)]
        assert vsec == wedge2(P[3], [a * P[4][t] + b * P[2][t]
                                   for t in range(4)]), \
            '(BE-200): a l_4 - b l_3 is not p_z ^ (a p_y + b p_w)'
        assert Q(vsec) == 0, '(BE-200): the second lift is not a LINE'
        assert dim(span([L[0], L[1], vsec])) == 3 and \
            contains(Uperp, [L[1], vsec]), '(BE-200): the lift does not span U^(1)'
        Gq = [[klein(z1, z2) for z2 in (L[1], vsec)] for z1 in (L[1], vsec)]
        assert Gq[0][0] == Gq[1][1] == 0 and Gq[0][1] == a * c != 0, \
            '(BE-200): Ubar is not a HYPERBOLIC rank-2 plane'
        nq += 1
        # THE CANDIDATE FAMILY, ENUMERATED rather than sampled.  Every
        # totally singular 2-space of `U^(1)` contains `rad = <l_j>`
        # ((BE-191)(ii)), and `Pi_x` contains `l_j` anyway, so the 2-spaces
        # to check are EXACTLY `<l_j, al l_2 + ga vsec>` over `(al : ga)` in
        # P^1 -- a one-parameter family, swept in closed form.  A random
        # 2-space is never isotropic, which is the trap this sweep avoids.
        iso = []
        for (al, ga) in ([(F(1), F(0)), (F(0), F(1))]
                         + [(F(1), F(k)) for k in range(-7, 8) if k]
                         + [(F(k), F(1)) for k in range(-7, 8) if k]):
            w = [al * L[1][t] + ga * vsec[t] for t in range(6)]
            cand = span([L[0], w])
            assert dim(cand) == 2, 'a candidate collapsed'
            issing = (gram_rank(cand) == 0)
            assert issing == (al * ga == 0), \
                '(BE-200): the isotropic cone of Ubar is not `al ga = 0`'
            if issing:
                iso.append((al, ga))
                assert contains(U, cand), 'a candidate left U'
        assert len(iso) == 2, \
            '(BE-200): the candidate list is not exactly TWO'
        # candidate 1 = `<l_j, l_2>`: it is `Pi_x` only if `l_2 = q_c v q_w`
        # passes through `q_x`, i.e. `q_x, q_c, q_w` COLLINEAR -- which
        # `assert_generic_star` forbids at body `c`.
        assert rank([P[0], P[1], P[2]]) == 3, 'the draw is already collinear'
        assert not contains(span([L[0], L[1]]), [wedge2(px, P[2])]), \
            '(BE-200): candidate 1 carries a line through q_x without ' \
            'collinearity'
        # candidate 2 = `<l_j, vsec>`, `vsec` a line through `q_z`: it is `Pi_x`
        # only if `vsec` also passes through `q_x`, i.e. `q_x` lies on
        # `q_z v [a q_y + b q_w]`, whence `q_x, q_w, q_z, q_y` COPLANAR and
        # `q_z in pi_x`.
        thru_x = contains(span([L[0], vsec]), [wedge2(px, P[3])])
        assert thru_x == (rank([px, P[3], [a * P[4][t] + b * P[2][t]
                                           for t in range(4)]]) == 2), \
            '(BE-200): candidate 2 through q_x is not the collinearity'
        if thru_x:
            assert rank([P[0], P[2], P[3], P[4]]) == 3, \
                '(BE-200): candidate 2 through q_x without coplanarity'
        nforce += 1
        # ---- the theorem TESTED, not restated: at a GENERIC arc the whole
        #      containment locus is EMPTY over the second star point, because
        #      `U cap (p_x ^ K^4) = <l_j>`.  Swept over 24 second points.
        alpha = span([L[0], wedge2(px, P[2]), wedge2(px, P[3])])
        assert dim(isect(U, alpha)) == 1, \
            '(BE-200): U meets the alpha-space at x in more than a line'
        for k in range(24):
            u2 = [F(rng.randint(-11, 11)) for _ in range(3)] + [F(1)]
            if rank([px, P[1], u2]) != 3:
                continue
            Pk = span([L[0], wedge2(px, u2)])
            if dim(Pk) != 2:
                continue
            nsweep += 1
            assert not contains(U, Pk), \
                '(BE-200): containment at a GENERIC arc-4 configuration'
        nempty += 1
    print(f"  (BE-196) `Pi_x` contains `l_j`, so `Pi_x <= U` IS "
          f"`l_{{j'}} in U`: asserted at {npx}/{npx} draws.")
    print(f'  (BE-199) `Pi_x <= U cap l_j^perp`, `dim = 3`, `rad = <l_j>`, '
          f'`rank = 2`: asserted at {nq}/{nq}.')
    print(f'  (BE-200) `Ubar` is a HYPERBOLIC rank-2 plane, so the '
          f'candidate list is EXACTLY TWO -- enumerated')
    print(f'  over a 30-point sweep of `P^1` at every draw ({nq}/{nq}), with '
          f'the cone asserted to be `al ga = 0`:')
    print(f'  `<l_j, l_2>` needs `q_x, q_c, q_w` COLLINEAR (forbidden at '
          f'body `c`), and `<l_j, p_z ^ (a p_y + b p_w)>`')
    print(f'  forces `q_z in pi_x` AND `q_x, q_w, q_z, q_y` coplanar -- '
          f'asserted at {nforce}/{nforce}.')
    print(f'  THE THEOREM TESTED: `U cap (p_x ^ K^4) = <l_j>` at '
          f'{nempty}/{nempty} generic arc-4 draws, so the')
    print(f'  containment locus over the second star point is EMPTY there -- '
          f'asserted at {nsweep}/{nsweep} second')
    print('  star points, a SWEEP of the quantifier the claim is about and '
          'not a single draw.')
    assert npx >= 15 and nq >= 15 and nsweep >= 200, 'perp did not run'
    nh = _gated4(seed)
    print(f'  perp: {time.time() - t0:.1f}s')
    return nh


def arc4_library(ell=(4, 5, 6)):
    """`x`-`y` sides with an arc of length **4** through `c_1` and a longer
    one through `c_2`: the cycle `x - c1 - w - z - y - b_1 - .. - c2 - x`, so
    `|arc_1| = 4` and `|arc_2| = L`.  Total cycle length `4 + L >= 8`, off
    (BE-40)'s `<= 6`-cycle rigidity, and every vertex has degree 2.  This is
    BRANKV's `short_library` with the short arc one edge LONGER -- the axis
    (BE-201) is about, moved by one, which is the generator-parameter
    discipline `RESEARCH-ARC.md` section 4's second instance asks for."""
    out = []
    for L in ell:
        E = [('x', 'c1'), ('c1', 'w'), ('w', 'z'), ('z', 'y')]
        prev = 'y'
        for i in range(L - 1):
            nxt = f'b{i}' if i < L - 2 else 'c2'
            E.append((prev, nxt))
            prev = nxt
        E.append((prev, 'x'))
        out.append((f'arc4-through-c1 + arc{L}-through-c2 '
                    f'(cycle {4 + L})', E, 'x', 'y'))
    return out


def _gated4(seed):
    """(BE-200)'s INHABITATION, on a genuine composite peel with every gate
    `bline.legal_peel` checks -- (CH-1)'s three hypotheses on `H`, `x !~ y`,
    both terminals hubs, side 2 `rnode_shaped` -- and configurations from
    `binduc.flat_config`, whose docstring states it is *a legal pencil
    configuration at EVERY graph* and which asserts `assert_generic_star` and
    `verify_pencil_witness` itself (both re-asserted here, on the
    docstrings-are-not-evidence rule).

    THIS IS BRANKV'S (BE-192) WITNESS ONE ARC-EDGE LONGER, and it says the
    POINTWISE clause is false at arc 4 as well: the fully planar branch is
    where `a = c = 0`, `U = Lambda^2 tau` and `pi_x = tau`, so the
    confinement (BE-200) proves is a PROPER INHABITED closed condition rather
    than an empty one.  The witness is MAXIMALLY DEGENERATE (fully planar) --
    exactly (BE-192)(iii)'s disclosure, unchanged."""
    print('  -- GATED on a composite peel `H`, |arc_1| = 4 --')
    from bline import legal_peel
    from bproper import composite
    from binduc import flat_config
    from kbare_common import verify_pencil_witness
    peels, rows, hits, qz_in, qy_in = 0, 0, 0, 0, 0
    rd, cd = {}, {}
    for (name, Eside, _x0, _y0) in arc4_library():
        lp = legal_peel(Eside)
        if lp is None:
            print(f'     {name}: does NOT glue at non-adjacent terminals '
                  f'-- skipped')
            continue
        EH, x, y, (okh, md, g, dx, dy, rn, sz) = lp
        assert okh and md >= 2 and g >= 4, ('(CH-1) fails on H', name)
        assert dx >= 3 and dy >= 3 and rn, ('peel gates fail', name)
        _EHc, Es1, _Es2, _x, _y = composite('K33', [3] * 9, ('A', 'B'), Eside)
        cs = sorted(neighbors(Es1)[x], key=str)
        assert len(cs) == 2, ('deg_1(x) != 2 on the composite', cs)
        peels += 1
        for d in range(8):
            rng = random.Random(seed + 8831 * d + len(name))
            try:
                aff = flat_config(EH, rng)
            except RuntimeError:
                continue
            okw, _n = verify_pencil_witness(EH, aff)
            assert okw, 'flat_config returned a non-witness'
            pix = plane_at(EH, aff, x)
            assert pix is not None, 'no closed-star plane at x'
            Pix = span([wedge2(hat(aff[x]), hat(aff[cc])) for cc in cs])
            assert dim(Pix) == 2, 'the two hinge lines at x coincide'
            S, rho, _dM, _r = rho_bar_of(Es1, aff, x, y)
            cval = dim(isect(S, Pix)) if S else 0
            arc1 = arc_through(Es1, x, y, cs[0]) or arc_through(Es1, x, y,
                                                                cs[1])
            assert arc1 is not None and len(arc1) - 1 == 4, \
                ('the gated peel does not carry an arc of length 4',
                 name, arc1)
            rows += 1
            rd[rho] = rd.get(rho, 0) + 1
            cd[cval] = cd.get(cval, 0) + 1
            if contains(pix, [hat(aff[arc1[3]])]):
                qz_in += 1
            if contains(pix, [hat(aff[y])]):
                qy_in += 1
            if cval == 2 and rho <= 5:
                hits += 1
                assert contains(pix, [hat(aff[arc1[3]])]), \
                    '(BE-200): a violation without `q_z in pi_x`'
    print(f'     {peels} composite peels (K33 skeleton, profile 3), {rows} '
          f'gated `flat_config` chart points,')
    print(f'     every one carrying an arc of length exactly 4 through a '
          f'side-neighbour of `x` (asserted).')
    print('     `rho_i`: ' + ', '.join(f'{k}: {v}' for k, v in
                                       sorted(rd.items()))
          + ';  `c_i(Pi_x)`: ' + ', '.join(f'{k}: {v}' for k, v in
                                           sorted(cd.items())))
    print(f'     `q_z in pi_x` at {qz_in} of {rows}, `q_y in pi_x` at '
          f'{qy_in} -- (BE-200)\'s forced incidence, asserted at')
    print(f'     every one of the {hits} violations.')
    print(f'     ** CLAUSE VIOLATION (containment AND `rho_i <= 5`) at '
          f'{hits} of {rows} GATED arc-4 chart points, so')
    print('     the POINTWISE clause is FALSE at arc 4 too and (BE-200)\'s '
          'confinement is INHABITED. **')
    assert rows >= 6, 'the gated arc-4 test did not run'
    return hits


# ====================================================== mode: ladder
# (BE-201)/(BE-202): the MASTER INVARIANT `dim(U cap alpha_x)`, the two
# mechanisms' boundaries, and the exact stop at n = 6.

def run_ladder(ndraw=24, seed=SEED):
    t0 = time.time()
    print(f'== ladder: (BE-201)/(BE-202) the master invariant and the exact '
          f'boundary, seed {seed}')
    rng = random.Random(seed + 1229)
    inv, cone, det_arc, det_lj, conic = {}, {}, {}, {}, 0
    for n in range(2, 8):
        got = 0
        for _ in range(ndraw):
            P = arc_pts(rng, n)
            if P is None:
                continue
            L = arc_lines(P)
            U = span(L)
            if dim(U) != min(n, 6):
                continue
            px = P[0]
            # `alpha_x` = the alpha-space `p_x ^ K^4`: ALL lines through
            # `q_x`, a 3-dimensional TOTALLY SINGULAR subspace, and
            # `Pi_x <= alpha_x` always.
            for _try in range(8):
                w1 = [F(rng.randint(-9, 9)) for _ in range(3)] + [F(1)]
                w2 = [F(rng.randint(-9, 9)) for _ in range(3)] + [F(1)]
                if rank([px, P[1], w1, w2]) == 4:
                    break
            alpha = span([wedge2(px, P[1]), wedge2(px, w1), wedge2(px, w2)])
            assert dim(alpha) == 3 and gram_rank(alpha) == 0, \
                'the alpha-space at x is malformed'
            # ---- (BE-201): THE MASTER INVARIANT.
            da = dim(isect(U, alpha))
            assert da == max(1, min(n, 6) - 3), \
                f'(BE-201): dim(U cap alpha_x) is not max(1, min(n,6)-3) ' \
                f'at n = {n}'
            inv[(n, da)] = inv.get((n, da), 0) + 1
            # ---- (BE-199): the perp-reduction and the quotient dimension.
            Uperp = perp_in(U, L[0])
            assert contains(Uperp, alpha) or dim(isect(Uperp, alpha)) == da, \
                '(BE-199): U cap alpha_x is not inside l_j^perp'
            _Gq, lift = quotient_form(Uperp, L[0])
            dq = len(lift)
            assert dq == (1 if n == 2 else min(n, 6) - 2), \
                f'(BE-201): dim Ubar is not min(n,6) - 2 at n = {n}'
            # ---- the CONE of `Ubar`, counted EXACTLY at dim <= 2 and
            #      CONSTRUCTED as an infinite family at dim 3.
            Gq = [[klein(u, v) for v in lift] for u in lift]
            nc = _cone_exact(Gq)
            if dq >= 3:
                assert rank(Gq) == dq, \
                    f'(BE-201): Ubar is degenerate at n = {n}'
                fam = _conic_family(Gq, lift, L[0], U, nwant=6)
                assert len(fam) >= 5, \
                    f'(BE-201): the n = {n} quadric did not yield a family'
                if dq == 3:
                    conic += 1
                nc = 'conic' if dq == 3 else 'quadric'
            cone[(n, nc)] = cone.get((n, nc), 0) + 1
            # ---- (BE-202): the two determinantal readings.
            r_arc = rank(L + alpha)
            det_arc[(n, r_arc)] = det_arc.get((n, r_arc), 0) + 1
            for _try in range(8):
                u2 = [F(rng.randint(-9, 9)) for _ in range(3)] + [F(1)]
                if rank([px, P[1], u2]) == 3:
                    break
            ljo = wedge2(px, u2)
            r_lj = rank(L + [ljo])
            det_lj[(n, r_lj)] = det_lj.get((n, r_lj), 0) + 1
            Pk = span([L[0], ljo])
            if dim(Pk) == 2:
                assert contains(U, Pk) == (n >= 6), \
                    f'(BE-202): the containment verdict flipped at n = {n}'
            got += 1
        if got:
            print(f'  n = {n}: {got} draws;  dim U = {min(n, 6)};  '
                  f'dim(U cap alpha_x) = {max(1, min(n, 6) - 3)};  '
                  f'dim Ubar = {dq};  cone of Ubar: {nc}')
    print('  (BE-201) THE MASTER INVARIANT, asserted: '
          '`dim(U cap alpha_x) = max(1, min(n,6) - 3)`, census '
          + ', '.join(f'{k}: {v}' for k, v in sorted(inv.items())))
    print('  Since `Pi_x <= alpha_x` ALWAYS, `Pi_x <= U` needs '
          '`dim(U cap alpha_x) >= 2`.  So the containment is')
    print('  IMPOSSIBLE at a generic arc of length <= 4; at n = 5 it is ONE '
          'linear condition on the OTHER')
    print('  side-neighbour (`l_{j\'} in U cap alpha_x`, a 2-space); and at '
          'n >= 6 it is AUTOMATIC, `U cap alpha_x`')
    print('  being all of `alpha_x`.')
    print('  (BE-202) the RADICAL mechanism\'s own boundary -- the '
          'CONSTRUCTED cone census of `Ubar`: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cone.items(),
                                                     key=lambda z: str(z))))
    print(f'  finite (<= 2 candidates) exactly at n <= 4, a CONIC at n = 5 '
          f'({conic} draws, each with >= 5 members')
    print('  CONSTRUCTED from the rational point `l_2` by the standard '
          'secant parametrization).  So the RADICAL')
    print('  ladder stops at 4 and the alpha-space ladder stops at 5.')
    print('  Determinantal readings: `rank([l_1..l_n] ++ alpha_x)`: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(det_arc.items()))
          + ';  `rank([l_1..l_n, l_{j\'}])`: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(det_lj.items())))
    print('  ** THE BOUNDARY IS EXACTLY n = 6, and it is (BE-189)(iii)\'s '
          'OWN threshold: `rho_i <= dist` makes')
    print('  the clause\'s conclusion `rho_i = 6` UNREACHABLE at dist <= 5, '
          'so the path-bound family of')
    print('  arguments closes exactly the strata on which the clause is '
          'VACUOUS and provably cannot reach')
    print('  the ones on which it has CONTENT.  A structural stop, not a '
          'cap. **')
    assert set(k[0] for k in inv) == {2, 3, 4, 5, 6, 7}, 'ladder did not run'
    assert conic >= 5, '(BE-201): the n = 5 conic was not constructed'
    print(f'  ladder: {time.time() - t0:.1f}s')
    return len(inv)


def _is_sq(x):
    """Is the nonnegative rational `x` a square in Q?"""
    if x < 0:
        return False
    n, d = x.numerator, x.denominator
    for m in (n, d):
        r = 0
        while (r + 1) * (r + 1) <= m:
            r += 1
        if r * r != m:
            return False
    return True


def _cone_exact(Gq):
    """The EXACT number of isotropic lines of the form `Gq` over Q, in
    dimension 0, 1 or 2 -- solved in closed form, never sampled.  Dimension
    1: the single line is isotropic iff `Gq[0][0] = 0`.  Dimension 2:
    `A x^2 + 2 B x y + C y^2` has 2 / 1 / 0 rational roots according as
    `B^2 - A C` is a nonzero square / zero / a non-square (with the
    degenerate `A = C = 0` case giving 2)."""
    d = len(Gq)
    if d == 0:
        return 0
    if d == 1:
        return 1 if Gq[0][0] == 0 else 0
    if d != 2:
        return None
    A, B, C = Gq[0][0], Gq[0][1], Gq[1][1]
    if A == 0 and B == 0 and C == 0:
        return 'all'
    disc = B * B - A * C
    if A == 0 and C == 0:
        return 2
    if disc == 0:
        return 1
    return 2 if _is_sq(disc) else 0


def _conic_family(Gq, lift, lj, U, nwant=6):
    """CONSTRUCT rational points of the isotropic quadric of a nondegenerate
    `Gq` of dimension >= 3, starting from the known rational point `lift[0]`
    (which is `l_2`, a hinge line, hence isotropic), by the standard secant
    parametrization: `Q(v0 + t d) = t (2 B(v0, d) + t Q(d))`, so
    `t = -2 B(v0, d) / Q(d)` lands back on the quadric.  Each point gives a
    totally singular 2-space `<l_j, w>` of `U`, ASSERTED as such.  This is
    the CONSTRUCTIVE answer to "is the candidate locus finite" -- the family
    is BUILT, never searched for, which is `RESEARCH-ARC.md` section 4's
    shape and the trap BRANKV self-caught at (BE-191)(ii)."""
    d = len(Gq)
    assert d >= 3

    def bil(u, v):
        return sum(u[i] * Gq[i][j] * v[j] for i in range(d)
                   for j in range(d))
    v0 = [F(1)] + [F(0)] * (d - 1)
    assert bil(v0, v0) == 0, 'lift[0] is not isotropic'
    dirs = []
    for i in range(1, d):
        for j in range(1, d):
            if j == i:
                continue
            for k in range(-3, 4):
                v = [F(0)] * d
                v[i] = F(k)
                v[j] = F(1)
                dirs.append(v)
    out, seen = [], set()
    for dd in dirs:
        qd = bil(dd, dd)
        if qd == 0:
            cand = dd
        else:
            tt = -2 * bil(v0, dd) / qd
            cand = [v0[m] + tt * dd[m] for m in range(d)]
        if all(z == 0 for z in cand):
            continue
        assert bil(cand, cand) == 0, 'the secant construction missed'
        w = [sum(cand[m] * lift[m][t2] for m in range(d)) for t2 in range(6)]
        if all(z == 0 for z in w):
            continue
        W = span([lj, w])
        if dim(W) != 2:
            continue
        assert gram_rank(W) == 0, \
            'a CONSTRUCTED quadric member is not totally singular'
        assert contains(U, W), 'a CONSTRUCTED quadric member left U'
        key = tuple(tuple(r) for r in W)
        if key not in seen:
            seen.add(key)
            out.append(W)
        if len(out) >= nwant:
            return out
    return out


# ========================================================= mode: pop
# (BE-203): the closure, priced on BARCH/BGPROP/BRANKV's OWN population.

def run_pop(ndraw=3, ntarget=8):
    t0 = time.time()
    print(f'== pop: (BE-203) the closure, priced on the landed population, '
          f'seed {SEED}')
    cfg, pts = 0, 0
    cfg_dist, contain, viol = {}, 0, 0
    dist_of_contain, lj_in_U = {}, 0
    lj_in_U_short, short_pts = 0, 0
    dimU_by_n, qz_in = {}, 0
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, aff, c1, c2, cs = (row['gd'], row['aff'], row['c1'],
                                   row['c2'], row['cs'])
            d_xy = len(shortest_path(E, x, y)) - 1
            arcs = {}
            for cj in cs:
                p = arc_through(E, x, y, cj)
                if p is not None:
                    arcs[cj] = p
            if not arcs:
                continue
            # `dist` IS `min_j |arc_j|` -- asserted, not assumed, because
            # (BE-195)(i)(e) flagged exactly this reading.
            assert min(len(p) - 1 for p in arcs.values()) == d_xy, \
                '(BE-203): dist is not min_j |arc_j|'
            cj0 = min(arcs, key=lambda k: len(arcs[k]))
            arc0 = arcs[cj0]
            n0 = len(arc0) - 1
            cjo = [v for v in cs if v != cj0]
            if len(cjo) != 1:
                continue
            cjo = cjo[0]
            fib, nh, dW = fibre_k(E, aff, x, cs)
            got = 0
            for j in range(ntarget):
                r2 = random.Random(SEED + 7717 * sd + 29 * j + len(name))
                npx = pt_in(fib, r2, 20)
                if npx[3] == 0:
                    continue
                aff2 = dict(aff)
                aff2[x] = _aff3(npx)
                if not star_holds(E, aff2):
                    continue
                p2 = hat(npx)
                m1, m2 = wedge2(p2, hat(aff2[c1])), wedge2(p2, hat(aff2[c2]))
                Pix = span([m1, m2])
                if dim(Pix) != 2:
                    continue
                got += 1
                pts += 1
                S, rho, _dM, _r = rho_bar_of(E, aff2, x, y)
                assert rho <= d_xy, '(BE-189)(ii) failed'
                # the arc span `U` and the two (BE-196)/(BE-202) readings.
                lj = wedge2(p2, hat(aff2[cj0]))
                ljo = wedge2(p2, hat(aff2[cjo]))
                L = [lj] + [hinge(aff2, a, b)
                            for (a, b) in zip(arc0[1:], arc0[2:])]
                U = span(L)
                dimU_by_n[(n0, dim(U))] = dimU_by_n.get((n0, dim(U)), 0) + 1
                assert contains(Pix, [lj]), '(BE-196): l_j not in Pi_x'
                inU = contains(U, [ljo])
                if inU:
                    lj_in_U += 1
                cl = contains(S, Pix)
                assert (not cl) or inU, \
                    '(BE-196): containment without `l_{j\'} in U`'
                if cl:
                    contain += 1
                    dist_of_contain[d_xy] = dist_of_contain.get(d_xy, 0) + 1
                    if rho <= 5:
                        viol += 1
                if n0 <= 5:
                    short_pts += 1
                    if inU:
                        lj_in_U_short += 1
                if n0 == 4:
                    # `q_z in pi_x` as a width-4 RANK question, never through
                    # `bimage.span` (whose width-6 special case fires on
                    # rank -- the recorded hazard).
                    qz = hat(aff2[arc0[3]])
                    if rank([p2, hat(aff2[c1]), hat(aff2[c2]), qz]) == 3:
                        qz_in += 1
            if got == 0:
                continue
            cfg += 1
            cfg_dist[d_xy] = cfg_dist.get(d_xy, 0) + 1
    cov4 = sum(v for k, v in cfg_dist.items() if k <= 4)
    cov5 = sum(v for k, v in cfg_dist.items() if k <= 5)
    cov3 = sum(v for k, v in cfg_dist.items() if k <= 3)
    print(f'  {cfg} configurations, {pts} swept fibre points -- BARCH\'s '
          f'`side_row` population and seed formula.')
    print('  Per-configuration `dist(x, y)` = `min_j |arc_j|` (asserted): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cfg_dist.items())))
    print(f'  COVERAGE: arc <= 3 (BRANKV) {cov3}/{cfg};  arc <= 4 '
          f'(BE-200) {cov4}/{cfg};  arc <= 5 (BE-202) {cov5}/{cfg}.')
    print('  `(|arc_j|, dim U)` census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dimU_by_n.items())))
    print(f'  (BE-202) properness, WITNESSED: `l_{{j\'}} in U` at '
          f'{lj_in_U_short} of {short_pts} arc-<=5 points, so its')
    print(f'  COMPLEMENT is inhabited at {short_pts - lj_in_U_short} -- '
          f'which is what properness needs.  Over ALL points')
    print(f'  it holds at {lj_in_U} of {pts}.')
    print(f'  BOTH CONJUNCTS: containment `c_i(Pi_x) = 2` at {contain} of '
          f'{pts}; containment AND `rho_i <= 5` -- the')
    print(f'  CLAUSE VIOLATION -- at {viol}.  `dist` at the containment '
          f'points: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dist_of_contain.items())))
    print(f'  (BE-200) `q_z in pi_x` at {qz_in} of the arc-4 points -- the '
          f'incidence the arc-4 theorem FORCES,')
    print('  and it is what confines the bad locus there.')
    assert cfg >= 20 and pts >= 100, 'the sweep did not run'
    assert viol == 0, 'a clause violation on the landed population'
    assert lj_in_U_short == 0, \
        '(BE-202): `l_{j\'} in U` fired on an arc-<=5 point'
    assert all(k[1] == min(k[0], 6) for k in dimU_by_n), \
        '(BE-202): dim U is not min(|arc|, 6) on the population'
    print(f'  pop: {time.time() - t0:.1f}s')
    return pts


def run_validate():
    print('== validate: form + perp + ladder + pop in one process')
    run_form()
    run_perp()
    run_ladder()
    run_pop()
    return 0


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    fns = dict(form=run_form, perp=run_perp, ladder=run_ladder, pop=run_pop,
               validate=run_validate)
    if mode not in fns:
        print(f'usage: {argv[0]} [{" | ".join(sorted(fns))}]')
        return 2
    fns[mode]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
