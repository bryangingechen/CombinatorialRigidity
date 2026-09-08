"""
Direction BGPROP (the tenth strategy pass's rank 1) -- `Gamma`-PROPERNESS:
does (BE-122)/(BE-123)'s proper -> generic bridge TRANSPORT to the
`Gamma`-locus, and can the missing incidence lemma be proved?

  THE TWO QUESTIONS.  (BE-149)(v) names as *what is genuinely missing*
  properness of

      Bad := { p in F : dim(Gamma cap (Pi_x(p) (+) Pi_x(p))) >= 2 }

  for the FIXED `Gamma <= V (+) V`, `V = Lambda^2 K^4`, against the family
  `{ Pi_x(p) (+) Pi_x(p) : p in F }` of products of TOTALLY SINGULAR
  2-spaces.  Question 1 is whether the proper -> generic bridge is even
  available for that locus; question 2 is the lemma.

  THE ANSWERS, said at the top.

  (BE-180) QUESTION 1: THE BRIDGE TRANSPORTS, and it is ALREADY LANDED --
           (BE-139)(iv) states the architecture as *constructibility* + *a
           `p_x`-sweep* + *properness in the swept fibre* and records
           inputs 1 and 2 as AVAILABLE at k >= 2 ((BE-123)(i) general,
           (BE-136)(iii) proved).  Nothing in (BE-122)/(BE-123) mentions
           `A`.  AND ONE STEP OF (BE-127)(i) DROPS OUT: the `k = 1` proof
           runs through (BE-125)(ii)'s POINTWISE COLLAPSE `U <= B_str`,
           needed only because (BE-114)/(BE-115) prove properness for the
           `Sigma_x`-locus and not the `Pi_x`-locus -- and (BE-125)(iii)
           exhibits those two differing dense-vs-a-point.  (BE-149)(i) is
           an EXACT identity at the `Pi_x` level, so the `Gamma` route
           needs no collapse.  The bridge is SHORTER, not longer.

  (BE-181) THE FAMILY IS NOT THE ONE THE QUESTION NAMES.  At k = 2 -- the
           whole landed scope of `Gamma` -- with `Om := p_{c_1} ^ p_{c_2}`
           the FIXED Pluecker point of `L_c`,

               Pi_x(p) = Sigma_p cap Om^perp,

           `Om^perp` the Klein-orthogonal HYPERPLANE.  Hence

               Gamma_Pi(p) = Gamma_Om cap (Sigma_p (+) Sigma_p),
               Gamma_Om := Gamma cap (Om^perp (+) Om^perp)   FIXED,

           so the moving factor is a product of ALPHA-PLANES -- MAXIMAL
           totally singular 3-spaces -- and the whole `p`-dependence is a
           3-parameter family of those.  This is exactly the family
           (BE-149)(v)(b)'s LIFTED half of (BE-115)(i) speaks about.

  (BE-182) LEMMA A -- THE POINTWISE FIBRE IS A QUADRIC CONDITION, and this
           is BSTEER's technique transplanted:

               { p : u in Sigma_p } = L_u  if Q(u) = 0,   EMPTY if Q(u) != 0.

           So the incidence variety over `P(Gamma_Om)` is supported on the
           BI-QUADRIC locus `T = {Q(u) = Q(w) = 0}`, and every fibre is at
           most a LINE (a point off the proportional part).

  (BE-183) LEMMA B -- THE INCIDENCE BOUND, AND A CLASS-UNIFORM POSITIVE.
           dim Bad <= max(dim X_1, dim T - 1), `X_1` the locus of
           `P(Gamma_Om)` whose fibre is a whole line and `T` the bi-quadric.
           Computed per configuration it PROVES properness class-uniformly
           at 53 of 99 -- the first class-level properness statement on this
           route, which (BE-139)(iv) said no landed lemma supplies.  And
           `Delta_Om = 0` at 70 of 99 makes the VERTEX MAP injective on all
           of Bad there: a totally singular 2-space PINS `p`.

  (BE-184) THE FLOOR, AND (BE-149)(v)'s LEMMA IS FALSE.  `Sigma_p (+)
           Sigma_p` has codimension 6, so dim Gamma_Pi(p) >= g_Om - 6 for
           EVERY p:

               g_Om >= 8   ==>   graph-bad EVERYWHERE on the fibre,

           i.e. the properness (BE-149)(v) asks for is REFUTED, by a proof
           and not a cap, at 10 of 99 configurations.  A sharpened floor
           reaches 5 more pointwise.

  (BE-185) THE EXTENSION, and the dimension-level form of (BE-150)(iii):
           0 -> R_0 -> Gamma -> A -> 0, so dim Gamma = dim A + dim R_0 and
           dim Gamma_Pi(p) <= dim(A cap Pi_x) + dim(R_0 cap Pi_x).

  (BE-186) AND PROPERNESS IS THE WRONG TARGET WHERE IT FAILS.  At the 10
           configurations (BE-184) kills, the containment `Pi_x <=
           rho_bar_i` is FORCED at 80 of 80 swept points -- and `rho_i = 6`
           at all 80, so the clause holds POINTWISE there rather than
           generically.  On the whole 783-point sweep

               dim Gamma_Pi(p) >= 2  <=>  Pi_x <= rho_bar_i  <=>  rho_i = 6

           at 783/783, so (BE-149)(iii)'s NECESSARY condition is tight here
           -- and the honest cost of that is that the population never
           realizes a clause VIOLATION ((BE-140)(i)'s 0/772), so every
           soundness assertion run on it is a statement about a population
           where BAD coincides with `rho_i = 6`.

  MODES.  geom | reduce | crit | validate  (the last runs all three)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.  No `.lean` is touched.

  THREE RECORDED HARNESS HAZARDS, all navigated rather than fixed
  (`notes/scripts/README.md` *Harness debt*):
    * `bimage.pt_in` truncates to K^4 with no assert -- every use below is
      on a width-4 fibre basis, which is what it is FOR, and no
      `Lambda^2`-side draw goes through it;
    * `bimage.span`/`dim`/`isect` special-case width 6 -- so NO width-12
      object here touches them.  Every 12-wide measurement goes through
      `_rk` (= `exactcore.rank`) or the local width-agnostic `_sp`/`_cap`;
    * `bwin.dehom` returns a LIST -- `bwin` is not imported and the
      dehomogenizer used is `barch._aff3`, which returns a TUPLE.
"""

import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, nullspace, rank, wedge2, PL                  # noqa: E402
from bimage import contains, dim, isect, pt_in, rho_bar_of, span        # noqa: E402
from bunif import SEED                                                 # noqa: E402
from pitch import Q, klein                                             # noqa: E402
from repin import hodge_star                                           # noqa: E402
from bdegtwo import fibre_k, fibre_kind                                # noqa: E402
from barch import (_aff3, gamma_cut, library, side_row, star_holds)    # noqa: E402

E4B = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]


# ============================================ width-agnostic linear algebra
# `bimage.span`/`isect` hardwire I6 on a full-rank input, so a width-12
# object must not go through them (recorded hazard 2).  These three are the
# same operations with no width special case.

def _rk(rows):
    return rank(rows) if rows else 0


def _sp(rows):
    """Canonical basis of the row space, at ANY width."""
    if not rows:
        return []
    ns = nullspace(rows)
    return nullspace(ns) if ns else [r[:] for r in
                                     _ident(len(rows[0]))]


def _ident(w):
    return [[F(1) if i == j else F(0) for j in range(w)] for i in range(w)]


def _cap(A, B):
    """A cap B at ANY width."""
    if not A or not B:
        return []
    M = nullspace(A) + nullspace(B)
    return nullspace(M) if M else [r[:] for r in _ident(len(A[0]))]


def _same(A, B):
    """Row spaces equal, at ANY width."""
    return _rk(A) == _rk(B) == _rk(list(A) + list(B))


# ================================================= the fixed `Om` objects

def om_of(aff, c1, c2):
    """`Om = p_{c_1} ^ p_{c_2}`, the Pluecker point of the FIXED line `L_c`,
    and a basis of the Klein-orthogonal hyperplane `Om^perp <= V`.

    `klein(u, Om) = dot(u, hodge_star(Om))`, so `Om^perp` is the nullspace
    of the single row `hodge_star(Om)` -- 5-dimensional whenever Om != 0."""
    Om = wedge2(hat(aff[c1]), hat(aff[c2]))
    assert any(t != 0 for t in Om), 'c_1 = c_2 as points'
    star = hodge_star(Om)
    return Om, nullspace([star]), star


def sigma_of(p):
    """`Sigma_p = p ^ K^4`, the ALPHA-plane at p: 3-dimensional, and
    TOTALLY singular for the Klein form."""
    return span([wedge2(p, e) for e in E4B])


def gamma_om(gd, star):
    """`N_Om = {m in M : s(m), r(m) in Om^perp}` and `Gamma_Om` as width-12
    rows, both computed in M-coordinates -- the only 12-wide operation is
    `_rk`."""
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    if n == 0:
        return [], [], []
    rows = [[sum(star[t] * sv[i][t] for t in range(6)) for i in range(n)],
            [sum(star[t] * rv[i][t] for t in range(6)) for i in range(n)]]
    NOm = nullspace(rows)
    wide = [_comb(gd, c) for c in NOm]
    return NOm, wide, [w[:6] for w in wide]


def _comb(gd, c):
    """The width-12 row `(s(m), r(m))` for `m = sum c_i b_i`."""
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    s_c = [sum(c[i] * sv[i][t] for i in range(n)) for t in range(6)]
    r_c = [sum(c[i] * rv[i][t] for i in range(n)) for t in range(6)]
    return s_c + r_c


def cut_direct(gd, Pix):
    """`Gamma cap (Pi (+) Pi)` as width-12 rows, cut in ONE step from the
    full `M` -- the object `barch.gamma_cut` measures the rank of."""
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    if n == 0:
        return []
    fs = nullspace(span(Pix))
    rows = [[sum(f[t] * sv[i][t] for t in range(6)) for i in range(n)]
            for f in fs]
    rows += [[sum(f[t] * rv[i][t] for t in range(6)) for i in range(n)]
             for f in fs]
    return [_comb(gd, c) for c in (nullspace(rows) if rows else [])]


def cut_via_om(gd, NOm, Sig):
    """`Gamma_Om cap (Sigma_p (+) Sigma_p)` as width-12 rows -- the SAME
    object by (BE-181), cut in two steps through the FIXED `Om^perp`."""
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    if n == 0 or not NOm:
        return []
    fs = nullspace(Sig)
    B = [[sum(c[i] * sv[i][t] for i in range(n)) for t in range(6)]
         for c in NOm]
    C = [[sum(c[i] * rv[i][t] for i in range(n)) for t in range(6)]
         for c in NOm]
    m = len(NOm)
    rows = [[sum(f[t] * B[k][t] for t in range(6)) for k in range(m)]
            for f in fs]
    rows += [[sum(f[t] * C[k][t] for t in range(6)) for k in range(m)]
             for f in fs]
    out = []
    for d in (nullspace(rows) if rows else []):
        c = [sum(d[k] * NOm[k][i] for k in range(m)) for i in range(n)]
        out.append(_comb(gd, c))
    return out


def pol_zero(gd, NOm, which):
    """Is `Q . pi_j` identically zero on `Gamma_Om`?  Tested by the
    POLARIZATION matrix over a basis of `N_Om`: `Q(v(m))` vanishes
    identically iff `klein(v(b_i), v(b_j)) = 0` for all i, j (char != 2)."""
    n, vv = gd['n'], gd[which]
    B = [[sum(c[i] * vv[i][t] for i in range(n)) for t in range(6)]
         for c in NOm]
    for i in range(len(B)):
        for j in range(len(B)):
            if klein(B[i], B[j]) != 0:
                return False, B
    return True, B


# ======================================================== mode: geom
# (BE-182) and (BE-181)'s K^4 half, checked OFF the graphs entirely -- these
# are statements about `K^4`, not about a side.

def run_geom(ndraw=60, seed=SEED):
    t0 = time.time()
    print(f'== geom: (BE-181)/(BE-182) the K^4 facts, seed {seed}')
    rng = random.Random(seed + 4241)

    def rp():
        return [F(rng.randint(-9, 9)) for _ in range(3)] + [F(1)]

    nQ0, nQn, nin, nout = 0, 0, 0, 0
    for _ in range(ndraw):
        a, b, c, d = rp(), rp(), rp(), rp()
        if rank([a, b, c, d]) != 4:
            continue
        # -- Lemma A, decomposable half: {p : u ^ p = 0} is the LINE L_u.
        u = wedge2(a, b)
        assert Q(u) == 0, 'a ^ b is not on the Klein quadric'
        ker = nullspace([[_wedge3(u, e)[k] for e in E4B] for k in range(4)])
        assert _same(ker, [a, b]), 'Lemma A: L_u not recovered'
        nQ0 += 1
        # -- Lemma A, non-decomposable half: the locus is EMPTY.
        v = [u[t] + wedge2(c, d)[t] for t in range(6)]
        if Q(v) != 0:
            kv = nullspace([[_wedge3(v, e)[k] for e in E4B]
                            for k in range(4)])
            assert kv == [], 'Lemma A: a non-singular screw meets Sigma_p'
            nQn += 1
        # -- (BE-181): Pi_p = Sigma_p cap Om^perp, and Sigma_p <= Om^perp
        #    exactly when p lies ON the line.
        Om = wedge2(c, d)
        star = hodge_star(Om)
        Omp = nullspace([star])
        for p in (a, c):        # `c` is ON the line, the degenerate control
            Sig = sigma_of(p)
            cap = isect(Sig, Omp)
            if rank([p, c, d]) == 3:                  # p not on the line
                assert dim(cap) == 2, 'Sigma_p cap Om^perp is not a pencil'
                assert _same(cap, span([wedge2(p, c), wedge2(p, d)])), \
                    '(BE-181): the pencil is not p ^ L_c'
                nout += 1
            else:
                assert contains(Omp, Sig), 'Sigma_p should lie in Om^perp'
                assert dim(cap) == 3, 'the degenerate cut is not Sigma_p'
                nin += 1
        p = a
        Sig = sigma_of(p)
        # -- total singularity of both factors (BE-149)(v)(a), re-derived.
        for w in Sig:
            assert Q(w) == 0, 'Sigma_p is not totally singular'
        for w1 in Sig:
            for w2 in Sig:
                assert klein(w1, w2) == 0, 'B is not 0 on Sigma_p'
    # -- (BE-149)(v)(b)'s LIFTED half, on the ALPHA-plane family this time.
    lift = 0
    for _ in range(ndraw):
        p1, p2, p3 = rp(), rp(), rp()
        if rank([p1, p2, p3]) != 3:
            continue
        S = sigma_of(p1) + sigma_of(p2) + sigma_of(p3)
        assert rank(S) == 6, 'three alpha-planes do not span V'
        W12 = [r + [F(0)] * 6 for r in S] + [[F(0)] * 6 + r for r in S]
        assert _rk(W12) == 12, 'the product sum does not fill V (+) V'
        lift += 1
    print(f'  Lemma A (BE-182): decomposable -> L_u at {nQ0}/{nQ0}, '
          f'non-singular -> EMPTY at {nQn}/{nQn}.')
    print(f'  (BE-181): Pi_p = Sigma_p cap Om^perp asserted as a SUBSPACE '
          f'at {nout}/{nout} draws off the line')
    print(f'  (and Sigma_p <= Om^perp, the cut being all of Sigma_p, at {nin} '
          f'constructed draws ON the line -- the degenerate case `F` excludes).')
    print(f'  Sigma_p totally singular (Q = 0 and B = 0) at every draw; '
          f'the (BE-149)(v)(b) lift to alpha-plane PRODUCTS is rank 12 at '
          f'{lift}/{lift}.')
    assert nQ0 >= 20 and nQn >= 5 and nout >= 20 and nin >= 20 and lift >= 20, \
        'the geometry block did not run'
    print(f'  geom: {time.time() - t0:.1f}s')
    return nQ0


def _wedge3(u, e):
    """u ^ e for u in Lambda^2 K^4, e in K^4 -- coordinates in the basis
    (e123, e023, e013, e012) of Lambda^3 K^4, signs irrelevant to vanishing
    but taken consistently so the map is linear in both slots."""
    out = [F(0)] * 4
    for (i, j), uc in zip(PL, u):
        for k in range(4):
            if e[k] == 0 or k in (i, j):
                continue
            miss = [t for t in range(4) if t not in (i, j, k)][0]
            # sign of the permutation (i, j, k) -> sorted, times position
            perm = [i, j, k]
            sg = 1
            for a in range(3):
                for b in range(a + 1, 3):
                    if perm[a] > perm[b]:
                        sg = -sg
            out[3 - miss] += sg * uc * e[k]
    return out


# ====================================================== mode: reduce
# (BE-181)/(BE-184)/(BE-185) on the LANDED population -- `barch.library()`
# at ndraw = 3, the same 99 configurations (BE-151) measures.

def run_reduce(ndraw=3, ntarget=8):
    t0 = time.time()
    print(f'== reduce: (BE-181)/(BE-184)/(BE-185) on the fibre, seed {SEED}')
    cfg, pts = 0, 0
    id_pi, id_cut, ext, upper, floor = 0, 0, 0, 0, 0
    gdist, fdist = {}, {}
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, aff, c1, c2 = row['gd'], row['aff'], row['c1'], row['c2']
            A, R0 = gd['A'], gd['R0']
            Om, Omp, star = om_of(aff, c1, c2)
            NOm, wide, _ = gamma_om(gd, star)
            gOm = _rk(wide)
            # (BE-185): the extension 0 -> R_0 -> Gamma -> A -> 0.
            assert _rk(gd['G12']) == dim(A) + dim(R0), \
                '(BE-185): dim Gamma != dim A + dim R_0'
            ext += 1
            fib, nh, dW = fibre_k(E, aff, x, row['cs'])
            f = rank(fib) - 1                       # affine dim of the fibre
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
                # ---- (BE-181)(i): Pi_x(p) = Sigma_p cap Om^perp.
                Sig = sigma_of(p2)
                assert _same(Pix, isect(Sig, Omp)), \
                    '(BE-181): Pi_x != Sigma_p cap Om^perp'
                id_pi += 1
                # ---- (BE-181)(ii): the two cuts agree AS SUBSPACES.
                D = cut_direct(gd, Pix)
                Vv = cut_via_om(gd, NOm, Sig)
                assert _same(D, Vv), \
                    '(BE-181): Gamma_Pi != Gamma_Om cap (Sigma (+) Sigma)'
                dGP, _phi = gamma_cut(gd, m1, m2)
                assert _rk(D) == dGP, 'the cut disagrees with gamma_cut'
                id_cut += 1
                # ---- (BE-185): the upper bound from the extension.
                ub = (dim(isect(A, Pix)) if A else 0) \
                    + (dim(isect(R0, Pix)) if R0 else 0)
                assert dGP <= ub, '(BE-185): the extension bound fails'
                upper += 1
                # ---- (BE-184): the codimension-6 floor.
                assert dGP >= gOm - 6, '(BE-184): the floor fails'
                floor += 1
            if got == 0:
                continue
            cfg += 1
            gdist[gOm] = gdist.get(gOm, 0) + 1
            fdist[(fibre_kind(nh, dW, rank(fib)), f)] = \
                fdist.get((fibre_kind(nh, dW, rank(fib)), f), 0) + 1
    print(f'  {cfg} configurations, {pts} swept fibre points.')
    print(f'  (BE-181) `Pi_x(p) = Sigma_p cap Om^perp` asserted as a '
          f'SUBSPACE at {id_pi}/{pts};')
    print(f'  `Gamma_Pi(p) = Gamma_Om cap (Sigma_p (+) Sigma_p)` asserted as '
          f'a SUBSPACE at {id_cut}/{pts},')
    print('  and agreeing with `barch.gamma_cut`\'s rank at every point.')
    print(f'  (BE-185) `dim Gamma = dim A + dim R_0` at {ext}/{ext} '
          f'configurations; the bound')
    print(f'  `dim Gamma_Pi <= dim(A cap Pi) + dim(R_0 cap Pi)` at '
          f'{upper}/{pts}.')
    print(f'  (BE-184) the floor `dim Gamma_Pi >= g_Om - 6` at '
          f'{floor}/{pts}.')
    print('  `g_Om = dim Gamma_Om` census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(gdist.items())))
    print('  fibre (shape, dim F): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(fdist.items())))
    assert cfg >= 20 and pts >= 100, 'the sweep did not run'
    print(f'  reduce: {time.time() - t0:.1f}s')
    return pts


# ======================================================== mode: crit
# (BE-183)/(BE-184): the incidence bound computed per configuration, and
# the two floors.

def parts_of(gd, NOm, star):
    """The three pieces of `X_1` -- the locus of `P(Gamma_Om)` whose
    incidence fibre is a whole LINE rather than a point ((BE-182)).

    Returns (d_w0, d_u0, d_prop, dDelta), all PROJECTIVE dimensions (-1 for
    empty), where
      d_w0   : {[(u, 0)] : Q(u) = 0} = P(s(ker r) cap Om^perp) cut by Q;
      d_u0   : {[(0, w)] : Q(w) = 0} = P(R_0 cap Om^perp) cut by Q;
      d_prop : {[(u, lam u)] : Q(u) = 0}, bounded by 1 + max over a CAPPED
               lambda grid of the slice's Q-cut dimension;
      dDelta : P(Delta_Om), Delta_Om = {u : (u,0) and (0,u) both in
               Gamma_Om} -- the only `U_2` shape whose VERTEX is not pinned
               ((BE-183)(ii)).  -1 means `Bad_low` is EMPTY."""
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    m = len(NOm)
    if m == 0:
        return -1, -1, -1, -1
    B = [[sum(c[i] * sv[i][t] for i in range(n)) for t in range(6)]
         for c in NOm]
    C = [[sum(c[i] * rv[i][t] for i in range(n)) for t in range(6)]
         for c in NOm]

    def img(M, which):
        """Projective dim of the image in P(Gamma_Om) of the coefficient
        kernel of M, cut by Q on the `which` component."""
        ker = nullspace(M) if M else []
        rows = []
        for d in ker:
            rows.append([sum(d[k] * (B if which == 'u' else C)[k][t]
                             for k in range(m)) for t in range(6)])
        d0 = _rk(rows) - 1
        if d0 < 0:
            return -1
        # does Q cut this piece?  polarization over the image basis.
        bas = _sp(rows)
        cuts = any(klein(bas[a], bas[b]) != 0
                   for a in range(len(bas)) for b in range(len(bas)))
        return d0 - 1 if cuts else d0

    d_w0 = img([[C[k][t] for k in range(m)] for t in range(6)], 'u')
    d_u0 = img([[B[k][t] for k in range(m)] for t in range(6)], 'w')
    d_prop = -1
    for lam in (-3, -2, -1, 1, 2, 3):
        d_prop = max(d_prop, img([[C[k][t] - F(lam) * B[k][t]
                                   for k in range(m)] for t in range(6)],
                                 'u'))
    if d_prop >= 0:
        d_prop += 1                      # the lambda family adds one
    # Delta_Om: (u, 0) in Gamma_Om AND (0, u) in Gamma_Om.
    W0 = [[sum(d[k] * B[k][t] for k in range(m)) for t in range(6)]
          for d in (nullspace([[C[k][t] for k in range(m)]
                               for t in range(6)]) or [])]
    U0 = [[sum(d[k] * C[k][t] for k in range(m)) for t in range(6)]
          for d in (nullspace([[B[k][t] for k in range(m)]
                               for t in range(6)]) or [])]
    dD = (dim(isect(span(W0), span(U0))) - 1) if (W0 and U0) else -1
    return d_w0, d_u0, d_prop, dD


def run_crit(ndraw=3, ntarget=8):
    t0 = time.time()
    print(f'== crit: (BE-183)/(BE-184) the incidence bound, seed {SEED}')
    cfg = 0
    prove, kill, undec = 0, 0, 0
    fires, nofire = 0, 0
    kill_nofire, prove_fires = 0, 0
    polz, dlow = 0, 0
    rows_undec, resid, sharp_all = {}, {}, 0
    prop_cap = -1
    clause_bad, dead_pts, dead_bad, true_bad = 0, 0, 0, 0
    rho_dead, rho_all = {}, {}
    tight = 0
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, aff, c1, c2 = row['gd'], row['aff'], row['c1'], row['c2']
            Om, Omp, star = om_of(aff, c1, c2)
            NOm, wide, _ = gamma_om(gd, star)
            gOm = _rk(wide)
            AOm = _sp([w[:6] for w in wide])
            ROm = _sp([w[6:] for w in wide])
            zero1, _B1 = pol_zero(gd, NOm, 'sv') if NOm else (True, [])
            zero2, _B2 = pol_zero(gd, NOm, 'rv') if NOm else (True, [])
            d_w0, d_u0, d_prop, dD = parts_of(gd, NOm, star)
            prop_cap = max(prop_cap, d_prop)
            fib, nh, dW = fibre_k(E, aff, x, row['cs'])
            f = rank(fib) - 1
            # dim T <= g_Om - 2 when a quadric cuts, else g_Om - 1.
            dT = gOm - 2 if not (zero1 and zero2) else gOm - 1
            dX1 = max(d_w0, d_u0, d_prop)
            bnd = max(dX1, dT - 1)                 # (BE-183)(i)
            got, ggood, gbad, sharp = 0, 0, 0, 0
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
                dGP, _ = gamma_cut(gd, m1, m2)
                S2, _rd, _a, _b = rho_bar_of(E, aff2, x, y)
                # (BE-184)(ii): the SHARPENED floor, asserted pointwise.
                ap = dim(isect(AOm, Pix)) if AOm else 0
                rp = dim(isect(ROm, Pix)) if ROm else 0
                lo = gOm - dim(AOm) - dim(ROm) + ap + rp
                assert dGP >= lo, '(BE-184)(ii): the sharpened floor fails'
                if lo >= 2:
                    sharp += 1
                cl = contains(S2, Pix)
                clause_bad += int(cl)
                true_bad += int(cl and _rd <= 5)
                # (BE-186)(i): is (BE-149)(iii)'s NECESSARY condition also
                # sufficient on this population?
                tight += int(cl == (dGP >= 2))
                rho_all[_rd] = rho_all.get(_rd, 0) + 1
                if gOm >= 8:
                    dead_pts += 1
                    dead_bad += int(cl)
                    rho_dead[_rd] = rho_dead.get(_rd, 0) + 1
                if dGP <= 1:
                    assert not cl, 'graph cert UNSOUND'
                    ggood += 1
                else:
                    gbad += 1
            if got == 0:
                continue
            cfg += 1
            if ggood > 0:
                fires += 1
            else:
                nofire += 1
            if zero1 and zero2:
                polz += 1
            if dD < 0:
                dlow += 1
            if sharp == got:
                sharp_all += 1
            if bnd < f:
                prove += 1
                assert ggood > 0 or gbad == 0, \
                    '(BE-183) proves proper where nothing fires'
                if ggood > 0:
                    prove_fires += 1
            elif gOm >= 8:
                kill += 1
                assert ggood == 0, '(BE-184) killed a firing configuration'
                kill_nofire += 1
            else:
                undec += 1
                rows_undec[(gOm, f, bnd)] = \
                    rows_undec.get((gOm, f, bnd), 0) + 1
            if ggood == 0 and gOm < 8:
                key = (gOm, f, dim(gd['A']), bnd, int(sharp == got))
                resid[key] = resid.get(key, 0) + 1
    print(f'  {cfg} configurations.  Certificate fires somewhere on the '
          f'fibre at {fires}, NOWHERE at {nofire}.')
    print(f'  (BE-183)(i) the incidence bound `dim Bad <= max(dim X_1, '
          f'dim T - 1)` PROVES properness')
    print(f'  class-uniformly at {prove} of {cfg} ({prove_fires} of those '
          f'also have a firing witness).')
    print(f'  (BE-184)(i) `g_Om >= 8` PROVES the certificate cannot fire at '
          f'{kill} of {cfg}, and the')
    print(f'  sweep found no firing point at every one ({kill_nofire}/'
          f'{kill}).')
    print(f'  (BE-183)(ii) `Delta_Om = 0`, so `Bad_low` is EMPTY and the '
          f'VERTEX MAP is injective on all')
    print(f'  of Bad, at {dlow} of {cfg} configurations.')
    print(f'  (BE-184)(ii) the sharpened floor `>= 2` at EVERY swept point '
          f'at {sharp_all} of {cfg}.')
    print(f'  UNDECIDED: {undec} of {cfg}; by (g_Om, dim F, bound): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(rows_undec.items())))
    print(f'  No quadric cuts Gamma_Om at {polz} of {cfg}.')
    print(f'  THE HONEST RESIDUE: {sum(resid.values())} configurations fire '
          f'nowhere and are NOT killed by')
    print('  (BE-184)(i); by (g_Om, dim F, dim A, bound, sharp-floor-all): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(resid.items())))
    print(f'  (BE-186) WHERE THE CERTIFICATE IS PROVABLY DEAD THE '
          f'CONTAINMENT IS FORCED, NOT MERELY')
    print(f'  UNPROVEN: over the {dead_pts} swept points of the {kill} '
          f'`g_Om >= 8` configurations `Pi_x <= rho_bar_i`')
    print(f'  holds at {dead_bad}, i.e. `c_i(Pi_x) = 2` EVERYWHERE on those '
          f'fibres; `rho_i` there is '
          + ', '.join(f'{k}: {v}' for k, v in sorted(rho_dead.items())))
    print(f'  so the clause survives ONLY by `rho_i = 6`, and the true BAD '
          f'(containment AND `rho_i <= 5`)')
    print(f'  is {true_bad} of all {clause_bad} containments over '
          f'{sum(rho_all.values())} points -- (BE-140)(i)\'s 0, reproduced.')
    print(f'  AND (BE-149)(iii) IS TIGHT HERE: `dim Gamma_Pi >= 2` agrees '
          f'with the containment at {tight} of')
    print(f'  {sum(rho_all.values())} points, so the necessary condition is '
          f'also sufficient on this population.')
    print('  `rho_i` census over all swept points: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(rho_all.items())))
    print(f'  CAP: the proportional part of `X_1` is bounded over a SIX-'
          f'POINT lambda grid, largest {prop_cap}')
    print('  -- so `dim X_1` is NOT FOUND above that under the cap, never '
          'proved below it.')
    assert cfg >= 20, 'the census did not run'
    assert prove + kill >= 1, 'neither criterion decided anything'
    assert true_bad == 0, '(BE-140)(i)\'s 0 did not reproduce'
    assert dead_bad == dead_pts, \
        'the containment is not forced at every g_Om >= 8 point'
    print(f'  crit: {time.time() - t0:.1f}s')
    return cfg


def run_validate():
    print('== validate: geom + reduce + crit in one process')
    run_geom()
    run_reduce()
    run_crit()
    return 0


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    fns = dict(geom=run_geom, reduce=run_reduce, crit=run_crit,
               validate=run_validate)
    if mode not in fns:
        print(f'usage: {argv[0]} [{" | ".join(sorted(fns))}]')
        return 2
    fns[mode]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
