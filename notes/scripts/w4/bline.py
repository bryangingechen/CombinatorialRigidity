"""
Direction BLINE (ordinal 73) -- PROVE OR REFUTE section (K-bare-ext)
(BE-127)(ii)'s `(*)`, half (B)'s last open sub-item.

  THE CONDITION, quoted with its hypotheses from *Step BE126*.  Let `H` be
  an internal R-node peel at {x, y} with x !~ y satisfying (CH-1)'s
  hypotheses, and let side_i have deg_i(x) = k >= 2 with side neighbours
  c_1, ..., c_k.  By (BE-105)(iv) Pi_x = <l_1, l_2>; by (BE-114)(iv)
  rho_bar_i <= <l_1> + A with A the p_x-free core space.  Then
  Pi_x <= rho_bar_i forces `p_x ^ t in A` for some t on the FIXED line
  L_c := p_{c_1} v p_{c_2}, and the bad locus is proper in p_x under

    (*)  Sigma_t is NOT inside A for any t in L_c, AND
         {t in L_c : dim(A cap Sigma_t) >= 2} is FINITE.

  THE ANSWER, said at the top.  `(*)` is DECIDED -- proved on one stratum,
  REFUTED on another, and classified exactly in between.  Write
  z := p_{c_1} ^ p_{c_2} (the Plucker point of L_c), W := z^perp (dim 5,
  and every Sigma_t with t in L_c lies inside it), B := A cap W, and
  b := dim(B + <z>) - 1.  Then:

  (BE-129) THE CLASSIFICATION.  W/<z> is canonically L_c (x) (K^4/L_c), a
           space of 2x2 matrices whose rank-one locus is the Segre quadric,
           and Sigma_t/<z> is the column-space-<t> ruling.  So `(*)` fails
           IFF  [z in A and (b >= 3, or b = 2 with B/<z> a RULING)]  or
           [z not in A and dim B = 4].  The two rulings are exactly
           `Sigma_{t_0} <= A` (t_0 in L_c) and `Lambda^2 pi' <= A`
           (pi' a plane containing L_c), so the whole thing collapses to a
           COMPACT FORM with no case split at all:

             `(*)` HOLDS  <=>  dim(A cap z^perp) <= 3, AND no Sigma_{t_0}
             (t_0 in L_c) and no Lambda^2 pi' (pi' >= L_c) lies inside A.

           Both are asserted, against each other and against the
           brute-force reading of `(*)`.

  (BE-130) `dim A >= 5` REFUTES `(*)` OUTRIGHT -- and kills the route, not
           just the certificate.  W is a hyperplane, so dim B >= dim A - 1
           >= 4, which forces b >= 3 (z in A) or B/<z> = W/<z> (z not in
           A); either way half two fails at EVERY t.  Worse: for every
           p not on L_c, `p ^ L_c` is a 2-space inside W, so it meets A
           inside the 5-space W -- the necessary condition `p_x ^ t in A`
           holds at EVERY p_x and the reduction is VACUOUS.  So
           (BE-127)(ii) dies at exactly the place (BE-119)(i) died.

  (BE-131) `dim A <= 2` PROVES `(*)`, and `dim A = 3` fails only at two
           named degeneracies (A = Sigma_t with t in L_c; A = Lambda^2 pi'
           with L_c inside pi').  At dim A = 4 the failure locus is
           `A <= W` plus one ruling case.  So `(*)`'s truth is a function
           of dim A and two incidences -- nothing else.

  (BE-132) THE 91/91 CERTIFICATION IS A COROLLARY OF (BE-131), NOT
           EVIDENCE.  Every row of (BE-127)(iii)'s population has
           dim A <= 3, so `(*)` there is decided by a theorem; the blind
           draws could not have landed on either degeneracy (both are
           proper closed).  The population is blind to the ONLY regime in
           which `(*)` was ever in doubt.

  (BE-133) THAT REGIME IS REACHABLE.  A side with deg_i(x) = 2 and a
           LONGER core carries dim A = 4, 5 and 6 at chart-legal draws --
           exhibited here on new topologies drawn by the SAME sampler
           (BE-127)(iii) used.  So the refuted stratum is inhabited.

  (BE-134) TWO FURTHER GAPS, neither of them `(*)`.  (a) There is NO
           p_x-sweep lemma at deg_i(x) >= 2: (BE-124)(i) assumes
           deg_i(x) = 1 inside its own derivation.  (b) Even given one, `proper in
           P^3` is not `proper in the fibre`: when a side neighbour is a
           hub the fibre is a PLANE, and `(*)` permits a bad plane.

  MODES.  classify | five | low | pop | reach | fibre
          | validate  (the last runs all six in one process)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.
"""

import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, wedge2, rank, nullspace, neighbors            # noqa: E402
from bimage import (contains, dim, isect, klein_perp, lam2,              # noqa: E402
                    pencil_space, plane_at, rho_bar_of, span, v4, pt_in)
from bpeel import SKELETONS, delta_pair, rnode_shaped                    # noqa: E402
from bdecor import girth, hcard_ok_piece                                 # noqa: E402
from bunif import SEED                                                   # noqa: E402
from bsatur import sigma_at                                              # noqa: E402
from bsigma import sample_side_config                                    # noqa: E402
from bproper import composite, core_of, degx_library                     # noqa: E402
from bopen import sat_locus                                              # noqa: E402

I4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]

# The line-parameter sample used to decide a Zariski-closed condition ON
# THE LINE L_c.  `dim(A cap Sigma_t) >= 2` is cut out by the vanishing of
# 3x3 minors of a 6-column matrix whose rows depend LINEARLY on t, so each
# minor has degree <= 3 in the line parameter; a closed subset of P^1 cut
# out by degree-<= 3 forms is either finite (<= 3 points) or all of P^1.
# Testing NLAM = 9 distinct parameters therefore DECIDES it.  (Cap
# disclosure, RESEARCH-ARC section 5: this is a decision under a stated
# degree bound, not a sample.)
NLAM = 9


# ================================================ the two halves of `(*)`

def line_points(pc1, pc2, n=NLAM):
    """n distinct points of the line L_c = p_{c_1} v p_{c_2}, as vectors:
    p_{c_1}, and p_{c_2} + j p_{c_1} for j = 0 .. n-2."""
    out = [pc1[:]]
    for j in range(n - 1):
        out.append([pc2[i] + F(j) * pc1[i] for i in range(4)])
    return out


def half_one(A, pc1, pc2):
    """(*) half one at (A, L_c): NO t on L_c has Sigma_t <= A.  EXACT --
    {t : Sigma_t <= A} is a linear subspace (bopen.sat_locus), so this is
    one intersection with the line."""
    sat = sat_locus(A) if A else []
    if not sat:
        return True
    return dim(isect(span(sat), span([pc1, pc2]))) == 0


def half_two(A, pc1, pc2):
    """(*) half two: {t in L_c : dim(A cap Sigma_t) >= 2} is FINITE.  The
    set is closed in L_c of degree <= 3 (see NLAM), so it is finite iff it
    misses one of NLAM distinct points."""
    if not A:
        return True
    for t in line_points(pc1, pc2):
        if rank([t]) == 0:
            continue
        if dim(isect(A, sigma_at(t))) <= 1:
            return True
    return False


def star_ok(A, pc1, pc2):
    """`(*)` itself, evaluated by brute force from its own words."""
    return half_one(A, pc1, pc2) and half_two(A, pc1, pc2)


# ============================================ (BE-129): the classification

def beta_locus(A, pc1, pc2):
    """{m in K^4 : p_{c_1} ^ m in A and p_{c_2} ^ m in A}.  Contains L_c
    whenever z = p_{c_1} ^ p_{c_2} lies in A; a THIRD independent m gives a
    plane pi' >= L_c with Lambda^2 pi' <= A."""
    fs = nullspace(A) if A else []
    if not fs:
        return [r[:] for r in I4]
    rows = []
    for f in fs:
        for p in (pc1, pc2):
            rows.append([sum(a * b for a, b in
                             zip(f, wedge2(p, I4[k]))) for k in range(4)])
    return nullspace(rows)


def classify(A, pc1, pc2):
    """(BE-129): decide `(*)` from (dim B, z in A, and the two rulings)
    alone.  Returns (fails, reason)."""
    z = wedge2(pc1, pc2)
    W = klein_perp([z])
    B = isect(A, W) if A else []
    zinA = contains(A, [z]) if A else False
    Lc = span([pc1, pc2])
    dB = dim(B)
    b = dim(span(B + [z])) - 1
    # the two rulings of the Segre quadric in W/<z>
    sat = sat_locus(A) if A else []
    alpha = bool(sat) and dim(isect(span(sat), Lc)) > 0      # Sigma_t <= A
    beta = zinA and dim(beta_locus(A, pc1, pc2)) >= 3        # Lam^2 pi' <= A
    # THE COMPACT FORM, asserted equivalent to the case analysis below:
    #   `(*)` HOLDS  <=>  dim(A cap z^perp) <= 3, and neither Sigma_{t_0} <= A
    #   (some t_0 in L_c) nor Lambda^2 pi' <= A (some plane pi' >= L_c).
    compact = (dB >= 4) or alpha or beta
    if zinA:
        if b >= 3:
            assert compact, 'compact form missed b >= 3'
            return True, 'z in A, b >= 3'
        if b == 2 and alpha:
            assert compact, 'compact form missed the alpha ruling'
            return True, 'z in A, b = 2, alpha ruling (Sigma_t <= A)'
        if b == 2 and beta:
            assert compact, 'compact form missed the beta ruling'
            return True, 'z in A, b = 2, beta ruling (Lam^2 pi\' <= A)'
        assert not compact, 'compact form claimed a failure that is not one'
        return False, f'z in A, b = {b}, no ruling'
    if dB == 4:
        assert compact, 'compact form missed dim(A cap W) = 4'
        return True, 'z not in A, A cap W = W/<z> lifts onto every Sigma_t'
    assert not compact, 'compact form claimed a failure that is not one'
    return False, f'z not in A, dim(A cap W) = {dB}'


def sub_pt(basis, rng, s=9, n=6):
    """A nonzero point of the span of `basis`, whose rows are n-vectors.
    `bimage.pt_in` is hardcoded to n = 4 (it is a K^4 helper) and would
    SILENTLY TRUNCATE a Lambda^2 K^4 row to its first four coordinates --
    so Lambda^2-side draws go through here."""
    for _ in range(60):
        c = [F(rng.randint(-s, s)) for _ in basis]
        x = [sum(c[i] * basis[i][k] for i in range(len(basis)))
             for k in range(n)]
        if any(t != 0 for t in x):
            return x
    raise RuntimeError('sub_pt: no nonzero draw')


def rand_subspace(rng, d, s=9):
    """A random d-dimensional subspace of Lambda^2 K^4."""
    for _ in range(80):
        rows = [[F(rng.randint(-s, s)) for _ in range(6)] for _ in range(d)]
        if dim(rows) == d:
            return span(rows)
    raise RuntimeError('rand_subspace')


def rand_line(rng, s=9):
    for _ in range(80):
        p1, p2 = v4(rng, s), v4(rng, s)
        if rank([p1, p2]) == 2:
            return p1, p2
    raise RuntimeError('rand_line')


def run_classify(nrand=140):
    t0 = time.time()
    print(f'== classify: (BE-129) THE EXACT CLASSIFICATION OF `(*)`, '
          f'seed {SEED}')
    print('  z := p_{c_1} ^ p_{c_2}; W := z^perp (dim 5, and every Sigma_t')
    print('  with t in L_c lies in it); B := A cap W; b := dim(B + <z>) - 1.')
    print('  W/<z> = L_c (x) (K^4/L_c) is a space of 2x2 matrices and')
    print('  Sigma_t/<z> is its column-space-<t> ruling, so `(*)` fails IFF')
    print('    z in A     and (b >= 3, or b = 2 with B/<z> a RULING), or')
    print('    z not in A and dim B = 4.')
    print('  Asserted as an IFF against the brute-force reading of `(*)`.')
    rng = random.Random(SEED + 4211)
    tot, fails, bydim = 0, 0, {}
    for trial in range(nrand):
        d = trial % 7
        A = rand_subspace(rng, d) if d else []
        pc1, pc2 = rand_line(rng)
        bf = not star_ok(A, pc1, pc2)
        cl, why = classify(A, pc1, pc2)
        assert bf == cl, ('the classification DISAGREES with `(*)`',
                          d, why, bf, cl)
        tot += 1
        fails += 1 if bf else 0
        bydim.setdefault(d, [0, 0])
        bydim[d][0] += 1
        bydim[d][1] += 1 if bf else 0
    # ---- the constructed degeneracies, which no random draw ever hits
    built = 0
    for k in range(24):
        r = random.Random(SEED + 77 * k)
        pc1, pc2 = rand_line(r)
        Lc = span([pc1, pc2])
        t0v = pt_in(Lc, r, 9)
        if rank([t0v]) == 0:
            continue
        m = v4(r, 9)
        if rank([pc1, pc2, m]) != 3:
            continue
        pi = span([pc1, pc2, m])
        for (A, tag) in ((sigma_at(t0v), 'A = Sigma_t, t in L_c'),
                         (lam2(pi), "A = Lambda^2 pi', L_c <= pi'")):
            assert dim(A) == 3, tag
            bf = not star_ok(A, pc1, pc2)
            cl, why = classify(A, pc1, pc2)
            assert bf and cl, ('a NAMED dim-3 degeneracy did not fail',
                               tag, bf, cl)
            built += 1
    print(f'  {tot} random (A, L_c) pairs across dim A = 0..6: '
          f'classification == `(*)` at {tot}/{tot}, {fails} of them FAILING')
    print('  per dim A (drawn, failing): ' + ', '.join(
        f'{k}: ({v[0]}, {v[1]})' for k, v in sorted(bydim.items())))
    print(f'  {built} CONSTRUCTED dim-3 degeneracies, all failing, both '
          f'kinds -- no random draw ever hits either')
    print(f'  [{time.time() - t0:.1f}s]')
    return tot


# ================================== (BE-130): dim A >= 5 refutes `(*)`

def reduction_vacuous(A, pc1, pc2, rng, npt=40, s=9):
    """Is the reduction's own necessary condition -- `some t on L_c has
    p ^ t in A` -- satisfied at EVERY p?  Returns (hits, tried)."""
    Lc = span([pc1, pc2])
    hits, tried = 0, 0
    for _ in range(npt):
        p = v4(rng, s)
        if rank([p]) == 0 or dim(isect(span([p]), Lc)) > 0:
            continue
        tried += 1
        pL = span([wedge2(p, pc1), wedge2(p, pc2)])
        if dim(isect(A, pL)) >= 1:
            hits += 1
    return hits, tried


def run_five(ntrial=60):
    t0 = time.time()
    print(f'== five: (BE-130) `dim A >= 5` REFUTES `(*)`, AND THE ROUTE '
          f'WITH IT, seed {SEED}')
    print('  W = z^perp is a HYPERPLANE, so dim(A cap W) >= dim A - 1 >= 4')
    print('  and half two fails at every t.  Worse, `p ^ L_c` is a 2-space')
    print('  inside the 5-space W for every p off L_c, so it MEETS A: the')
    print('  reduction\'s necessary condition holds at EVERY p_x and says')
    print('  nothing at all.  Both asserted below.')
    rng = random.Random(SEED + 5051)
    tot, vac_rows, vac_pts, vac_tried = 0, 0, 0, 0
    for trial in range(ntrial):
        d = 5 + (trial % 2)
        A = rand_subspace(rng, d)
        pc1, pc2 = rand_line(rng)
        assert not star_ok(A, pc1, pc2), \
            ('`(*)` HELD at dim A >= 5 -- (BE-130) is false', d)
        cl, why = classify(A, pc1, pc2)
        assert cl, ('the classification missed a dim >= 5 failure', d, why)
        h, tr = reduction_vacuous(A, pc1, pc2, rng)
        assert h == tr, ('the reduction was NOT vacuous at dim A >= 5',
                         d, h, tr)
        vac_pts += h
        vac_tried += tr
        vac_rows += 1
        tot += 1
    # the contrapositive, stated as the headline consumers will quote
    rng2 = random.Random(SEED + 5052)
    ok4 = 0
    for _ in range(40):
        d = rng2.choice((1, 2, 3, 4))
        A = rand_subspace(rng2, d)
        pc1, pc2 = rand_line(rng2)
        if star_ok(A, pc1, pc2):
            assert dim(A) <= 4, '`(*)` held above dim A = 4'
            ok4 += 1
    print(f'  {tot} random (A, L_c) at dim A in {{5, 6}}: `(*)` FAILS at '
          f'{tot}/{tot} -- never once held')
    print(f'  the reduction is VACUOUS at {vac_rows}/{vac_rows} of them: '
          f'{vac_pts}/{vac_tried} sampled p_x satisfy `p ^ t in A` for '
          f'some t on L_c')
    print(f'  contrapositive re-asserted: every one of {ok4} `(*)`-holding '
          f'draws has dim A <= 4, so `(*)` ENTAILS (BE-119)(i)\'s own '
          f'hypothesis')
    print(f'  [{time.time() - t0:.1f}s]')
    return tot


# ============================== (BE-131): the low-dimensional strata

def run_low(nrand=200):
    t0 = time.time()
    print(f'== low: (BE-131) `dim A <= 2` PROVES `(*)`; dim A = 3 and 4 '
          f'CLASSIFIED, seed {SEED}')
    print('  dim A <= 2: half one needs dim A >= 3; half two needs')
    print('  A <= Sigma_t, and Sigma_{t_1} cap Sigma_{t_2} = <z> is')
    print('  1-dimensional, so at most ONE t qualifies.  `(*)` HOLDS.')
    print('  dim A = 3: `(*)` fails IFF A = Sigma_t (t in L_c) or')
    print('  A = Lambda^2 pi\' (L_c <= pi\').  dim A = 4: IFF A <= W, or')
    print('  z in A with dim(A cap W) = 3 and a ruling.')
    rng = random.Random(SEED + 6101)
    n2, n3, n4, f3, f4 = 0, 0, 0, 0, 0
    pairdims = {}
    for _ in range(nrand):
        d = rng.choice((1, 2))
        A = rand_subspace(rng, d)
        pc1, pc2 = rand_line(rng)
        assert star_ok(A, pc1, pc2), ('`(*)` FAILED at dim A <= 2', d)
        n2 += 1
        # the mechanism, asserted rather than asserted-by-outcome
        ge2 = [t for t in line_points(pc1, pc2)
               if rank([t]) and dim(isect(A, sigma_at(t))) >= 2]
        assert len(ge2) <= 1, ('more than one t with dim >= 2 below dim A '
                               '= 3', d, len(ge2))
    for _ in range(nrand):
        A = rand_subspace(rng, 3)
        pc1, pc2 = rand_line(rng)
        bad = not star_ok(A, pc1, pc2)
        n3 += 1
        f3 += 1 if bad else 0
        if bad:
            z = wedge2(pc1, pc2)
            assert contains(A, [z]) and \
                dim(isect(A, klein_perp([z]))) == 3, \
                'a dim-3 failure that is not inside W with z'
    for _ in range(nrand):
        A = rand_subspace(rng, 4)
        pc1, pc2 = rand_line(rng)
        bad = not star_ok(A, pc1, pc2)
        n4 += 1
        f4 += 1 if bad else 0
        cl, _why = classify(A, pc1, pc2)
        assert bad == cl, 'classification disagreed at dim A = 4'
        z = wedge2(pc1, pc2)
        dB = dim(isect(A, klein_perp([z])))
        pairdims[dB] = pairdims.get(dB, 0) + 1
        if bad:
            assert dB >= 3, 'a dim-4 failure with dim(A cap W) < 3'
    # constructed dim-4 failures of BOTH kinds
    built = 0
    for k in range(16):
        r = random.Random(SEED + 131 * k)
        pc1, pc2 = rand_line(r)
        z = wedge2(pc1, pc2)
        W = klein_perp([z])
        assert dim(W) == 5 and contains(W, [z]), 'W is not z^perp of dim 5'
        A4 = span([sub_pt(W, r, 9) for _ in range(4)])
        if dim(A4) != 4 or not contains(W, A4):
            continue
        assert not star_ok(A4, pc1, pc2), 'a dim-4 A inside W did not fail'
        built += 1
    print(f'  dim A <= 2: `(*)` HOLDS at {n2}/{n2} random draws, and the '
          f'|{{t : dim >= 2}}| <= 1 mechanism is asserted at each')
    print(f'  dim A = 3: {f3}/{n3} random draws FAIL -- the two '
          f'degeneracies are proper closed, so a blind draw never hits them')
    print(f'  dim A = 4: {f4}/{n4} random draws FAIL; dim(A cap W) census '
          + ', '.join(f'{k}: {v}' for k, v in sorted(pairdims.items())))
    print(f'  {built} CONSTRUCTED dim-4 subspaces inside W: `(*)` FAILS at '
          f'every one')
    print(f'  [{time.time() - t0:.1f}s]')
    return n2 + n3 + n4


# ============ (BE-132): the population re-audit, and what it certifies

def which_clause(A, pc1, pc2):
    """Which clause of (BE-131) DECIDES this row -- i.e. would `(*)` here
    have been a theorem before any measurement?"""
    d = dim(A) if A else 0
    if d <= 2:
        return 'theorem: dim A <= 2'
    fails, _why = classify(A, pc1, pc2)
    if d == 3:
        return ('DEGENERATE (a named dim-3 failure)' if fails
                else 'theorem off two proper-closed degeneracies: dim A = 3')
    if d == 4:
        return ('DEGENERATE (A <= W or a ruling)' if fails
                else 'dim A = 4, off the failure locus')
    return 'REFUTED: dim A >= 5'


def degx_rows(lib, ndraw=8, nplant=6):
    """(BE-127)(iii)'s own population routine, re-run: blind draws of each
    deg_i(x) >= 2 side by BSIGMA's `sample_side_config`, the sampler that
    direction used.  Planted rows are dropped here because `plant_side`
    wants a PENDANT terminal; the blind draws are (BE-127)(iii)'s own
    `ndraw` block verbatim."""
    from bproper import plant_side
    from bimage import v4 as _v4
    out = []
    for (name, E, x, y) in lib:
        nb = neighbors(E)
        if len(nb[x]) < 2:
            continue
        cs = sorted(nb[x], key=str)
        c1, c2 = cs[0], cs[1]
        core = core_of(E, x)
        rows = []
        for sd in range(ndraw):
            rng = random.Random(SEED + 8887 * sd + len(name))
            aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
            if aff is not None:
                rows.append(aff)
        for sd in range(nplant):
            rng = random.Random(SEED + 331 * sd + 3 * len(name))
            Ppi = span([_v4(rng, 20) for _ in range(3)])
            if dim(Ppi) != 3:
                continue
            aff = plant_side(E, rng, Ppi, c1)
            if aff is not None:
                rows.append(aff)
        for aff in rows:
            S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
            if not S:
                continue
            A, dA, _d2, _r2 = rho_bar_of(core, aff, c1, y)
            out.append((name, E, x, y, c1, c2, aff, A, dA, S, rho, nb))
    return out


def run_pop():
    t0 = time.time()
    print(f'== pop: (BE-132) WHAT (BE-127)(iii)\'s 91/91 ACTUALLY '
          f'CERTIFIES, seed {SEED}')
    print('  Re-run of (BE-127)(iii)\'s own population -- the same 16')
    print('  topologies, the same sampler, the same seeds -- with one extra')
    print('  column: WHICH CLAUSE OF (BE-131) decides the row.  If the')
    print('  answer is `a theorem` at every row, the certification carries')
    print('  no information about the regime `(*)` was in doubt in.')
    rows = degx_rows(degx_library())
    tot, dAs, byclause, hubs = 0, {}, {}, 0
    for (name, E, x, y, c1, c2, aff, A, dA, S, rho, nb) in rows:
        pc1, pc2 = hat(aff[c1]), hat(aff[c2])
        assert rank([pc1, pc2]) == 2, ('the two side neighbours are '
                                       'collinear with the origin', name)
        ok = star_ok(A, pc1, pc2)
        cl, _why = classify(A, pc1, pc2)
        assert ok == (not cl), ('classification disagreed on the population',
                                name)
        assert ok, ('a population row FAILS `(*)`', name, dA)
        tot += 1
        dAs[dA] = dAs.get(dA, 0) + 1
        w = which_clause(A, pc1, pc2)
        byclause[w] = byclause.get(w, 0) + 1
        hubs += len([v for v in nb[x] if len(nb[v]) >= 3])
    assert max(dAs) <= 3, ('the population reaches dim A >= 4 after all',
                           sorted(dAs))
    assert all(k.startswith('theorem') for k in byclause), \
        ('some row was NOT decided by a theorem', sorted(byclause))
    print(f'  {tot} rows reproduced; dim A census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dAs.items())))
    print(f'  hub side-neighbours of x, summed over rows: {hubs}')
    print('  which clause decides the row:')
    for k, v in sorted(byclause.items()):
        print(f'    {v:4d}  {k}')
    print(f'  `(*)` holds at {tot}/{tot} -- AND at every row it is a '
          f'COROLLARY of (BE-131), never a measurement')
    print(f'  [{time.time() - t0:.1f}s]')
    return tot


# ================= (BE-133): is the refuted stratum reachable at all?

def _arc(E, a, b, L, tag):
    prev = a
    for i in range(L - 1):
        E.append((prev, f'{tag}{i}'))
        prev = f'{tag}{i}'
    E.append((prev, b))


def longcore_library():
    """deg_i(x) >= 2 sides with a LONG core path from c_1 to y -- the axis
    (BE-127)(iii)'s library never varies.  `x` sits on a short cycle (so
    deg_i(x) = 2) and `y` hangs off it down a path of length m, so the core
    is a TREE whose c_1 -> y path has 1 + m edges and dim A can reach 6.
    Every shape keeps girth >= 4 and the degree->=3 vertices an independent
    set, which is `sample_side_config`'s own guard."""
    out = []
    for cyc in (4, 5, 6):
        for m in (1, 2, 3, 4, 5, 6):
            E = []
            # the cycle through x: x - a0 - ... - a(cyc-2) - x, with the
            # branch to y hung on the vertex OPPOSITE-ish to x
            ring = ['x'] + [f'a{i}' for i in range(cyc - 1)]
            for i in range(cyc):
                E.append((ring[i], ring[(i + 1) % cyc]))
            hub = ring[1 + (cyc - 1) // 2]
            _arc(E, hub, 'y', m, f'd{cyc}_{m}_')
            out.append((f'cycle({cyc}) at x + tail({m}) from {hub}',
                        E, 'x', 'y'))
    # THE CONFINED-FIBRE FAMILY: the tail hangs on a0, a NEIGHBOUR of x, so
    # c_1 = a0 is a HUB of the side and the p_x fibre is the PLANE pi_{c_1}
    # rather than A^3.  (BE-127)(iii) reports 0 hub side-neighbours at all
    # 91 of its rows, so this case is unsampled there; it is reachable.
    for cyc in (4, 5, 6):
        for m in (1, 3, 5):
            E = []
            ring = ['x'] + [f'a{i}' for i in range(cyc - 1)]
            for i in range(cyc):
                E.append((ring[i], ring[(i + 1) % cyc]))
            _arc(E, 'a0', 'y', m, f'h{cyc}_{m}_')
            out.append((f'cycle({cyc}) at x + tail({m}) from a0 (c_1 a HUB)',
                        E, 'x', 'y'))
    return out


def legal_peel(side1, skname='K33', xy=('A', 'B')):
    """Glue a long-core side into a COMPOSITE peel and check (CH-1)'s three
    hypotheses ON `H`, plus x !~ y, both terminals hubs of `H`, and side 2
    R-node-shaped.  Returns (E, x, y, report) or None."""
    pr = [3] * len(SKELETONS[skname])
    E, E1, E2, x, y, = composite(skname, pr, xy, side1)
    nb = neighbors(E)
    if y in nb[x]:
        return None
    dp = delta_pair(E, x, y)
    if dp is None:
        return None
    _d1, _d2, Ea, Eb = dp
    s1 = Ea if len(Ea) == len(E1) else Eb
    s2 = Eb if s1 is Ea else Ea
    okh, _W, _br, _ha = hcard_ok_piece(E, x, y)
    md = min(len(nb[w]) for w in {w for e in E for w in e})
    return E, x, y, (okh, md, girth(E), len(nb[x]), len(nb[y]),
                     rnode_shaped(s2, x, y), len(s1) == len(E1))


def run_reach(ndraw=10):
    t0 = time.time()
    print(f'== reach: (BE-133) IS THE REFUTED STRATUM INHABITED? seed '
          f'{SEED}')
    print('  (BE-127)(iii)\'s library is 16 SMALL shapes -- cycles, thetas,')
    print('  two subdivided K4s -- whose cores are short, so dim A never')
    print('  exceeded 3 there.  Here the same sampler draws sides with the')
    print('  SAME deg_i(x) = 2 shape at x and a core path to y of length')
    print('  1 + m, m = 1..6.  dim A grows with m, and the stratum')
    print('  (BE-130) refutes is reached.')
    lib = longcore_library()
    # ---- (CH-1) AT THE COMPOSITE, before a single number is measured
    npeel = 0
    for (name, E0, _x0, _y0) in lib:
        lp = legal_peel(E0)
        assert lp is not None, ('the long-core side does not glue into a '
                                'peel at non-adjacent terminals', name)
        _Ec, _xc, _yc, (okh, md, g, dx, dy, rn, sz) = lp
        assert okh and md >= 2 and g >= 4, \
            ('(CH-1) FAILS on the composite', name, okh, md, g)
        assert dx >= 3 and dy >= 3, ('a terminal is not a hub of H', name)
        assert rn and sz, ('side 2 is not R-node-shaped', name)
        npeel += 1
    print(f'  (CH-1) asserted on {npeel}/{npeel} composites '
          f'(K33 subdivided x3 as side 2, glued at two non-adjacent hubs):')
    print('  hcard, min degree 2, girth >= 4, both terminals hubs, side 2')
    print('  R-node-shaped -- so `Chart(H)` is irreducible at every one.')
    tot, dAs, fails, byfail, whyfail, bytop = 0, {}, 0, {}, {}, {}
    reach4, reach5, hubrows = 0, 0, 0
    clausebad, clausenames, rhocen, live5, skipped = 0, {}, {}, 0, 0
    for (name, E, x, y) in lib:
        nb = neighbors(E)
        assert len(nb[x]) == 2, ('x is not a deg-2 terminal here', name)
        assert girth(E) >= 4, ('girth < 4 -- not a (CH-1) shape', name)
        ch, _W, _br, _ha = hcard_ok_piece(E, x, y)
        assert ch, ('hcard fails on the side', name)
        cs = sorted(nb[x], key=str)
        c1, c2 = cs[0], cs[1]
        core = core_of(E, x)
        for sd in range(ndraw):
            rng = random.Random(SEED + 8887 * sd + len(name))
            aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
            if aff is None:
                continue
            S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
            if not S:
                continue
            A, dA, _d2, rcore = rho_bar_of(core, aff, c1, y)
            pc1, pc2 = hat(aff[c1]), hat(aff[c2])
            # degeneracy guard, README section 4 convention 1: L_c must BE a
            # line.  Skips are counted and reported, never silent.
            if rank([pc1, pc2]) != 2:
                skipped += 1
                continue
            # the core here is a TREE, so its hinge rows are independent at
            # EVERY configuration ((BE-120)(ii)) -- each hinge contributes 5
            # rows, so rank R = 5|E| identically.  Asserted, because that
            # constancy is what makes dim A = rank[R; Q] - rank R LOWER
            # SEMICONTINUOUS, hence what lets ONE draw at dim A = d certify
            # `generically dim A >= d` on that chart.
            assert rcore == 5 * len(core), \
                ('the core is not independent -- semicontinuity argument '
                 'does not apply', name, rcore, 5 * len(core))
            bytop.setdefault(name, [0, 0])
            bytop[name][0] = max(bytop[name][0], dA)
            rhocen[(dA, rho)] = rhocen.get((dA, rho), 0) + 1
            if dA >= 5 and rho <= 5:
                live5 += 1
            tot += 1
            dAs[dA] = dAs.get(dA, 0) + 1
            hubrows += len([v for v in nb[x] if len(nb[v]) >= 3])
            # (BE-114)(iv), re-asserted on the NEW topologies
            l1 = wedge2(hat(aff[x]), pc1)
            assert contains(span((A or []) + [l1]), S), \
                ('(BE-114)(iv) FAILS on a long-core side', name, dA, rho)
            # the CLAUSE ITSELF, on the side, exactly as `bopen.py degx`
            # evaluates it: is this row BAD?
            pix = plane_at(E, aff, x)
            if pix is not None:
                if contains(S, pencil_space(hat(aff[x]), pix)) and rho <= 5:
                    clausebad += 1
                    clausenames.setdefault(name, 0)
                    clausenames[name] += 1
            ok = star_ok(A, pc1, pc2)
            cl, why = classify(A, pc1, pc2)
            assert ok == (not cl), ('classification disagreed', name, why)
            if dA >= 4:
                reach4 += 1
            if dA >= 5:
                reach5 += 1
                assert not ok, ('`(*)` HELD at dim A >= 5 on a chart draw',
                                name, dA)
                h, tr = reduction_vacuous(A, pc1, pc2,
                                          random.Random(SEED + tot))
                assert h == tr, ('the reduction was not vacuous', name, dA)
            if not ok:
                bytop[name][1] += 1
                fails += 1
                byfail[dA] = byfail.get(dA, 0) + 1
                if dA <= 4:
                    whyfail.setdefault(dA, []).append((name, why))
    print(f'  {tot} chart-legal rows over {len(lib)} NEW deg_i(x) = 2 '
          f'topologies, same sampler as (BE-127)(iii) '
          f'({skipped} skipped: p_{{c_1}}, p_{{c_2}} not a line)')
    print('  dim A census: ' + ', '.join(f'{k}: {v}'
                                         for k, v in sorted(dAs.items())))
    print(f'  hub side-neighbours of x, summed over rows: {hubrows}')
    print(f'  rows with dim A >= 4: {reach4};  with dim A >= 5: {reach5}')
    print(f'  rows where `(*)` FAILS: {fails}  (by dim A: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(byfail.items())) + ')')
    for k in sorted(whyfail):
        for (nm, why) in whyfail[k][:4]:
            print(f'    dim A = {k} FAILURE -- {why}   [{nm}]')
    gen5 = [n for n, v in bytop.items() if v[0] >= 5]
    print(f'  per-topology MAX dim A (= a lower bound on the GENERIC value, '
          f'the core being a tree):')
    for n in sorted(bytop):
        print(f'    {bytop[n][0]}   {bytop[n][1]:2d} failing rows   {n}')
    print(f'  topologies whose GENERIC dim A is >= 5, hence at which `(*)` '
          f'fails at a GENERIC chart point: {len(gen5)}/{len(bytop)}')
    print('  (dim A, rho_i) census: ' + ', '.join(
        f'({a},{r}): {v}' for (a, r), v in sorted(rhocen.items())))
    print(f'  rows with dim A >= 5 AND rho_i <= 5 -- where `(*)` is dead '
          f'AND the clause is NOT vacuous: {live5}')
    print(f'  THE CLAUSE ITSELF (Pi_x <= rho_bar_i AND rho_i <= 5), '
          f'evaluated exactly as `bopen.py degx` does it: {clausebad} bad '
          f'rows of {tot}')
    if clausebad == 0:
        print('  -- NOT FOUND under this cap.  What is refuted here is the')
        print('  ROUTE (BE-127)(ii) offers, not the clause: `(*)` is a')
        print('  SUFFICIENT condition, so its failure leaves the clause')
        print('  open, and no shortfall is exhibited (item 0(b) untouched).')
    if reach5:
        print('  at every dim A >= 5 row the reduction is VACUOUS: the')
        print('  necessary condition `p_x ^ t in A` holds at EVERY p_x')
    else:
        print('  NOT FOUND under this cap: no dim A >= 5 row (cap '
              f'disclosure -- {tot} rows, m <= 6)')
    print(f'  [{time.time() - t0:.1f}s]')
    return tot


# ============================ (BE-134): the two gaps that are not `(*)`

def run_fibre(ntry=400):
    t0 = time.time()
    print(f'== fibre: (BE-134) `PROPER IN P^3` IS NOT `PROPER IN THE '
          f'FIBRE`, seed {SEED}')
    print('  (BE-124)(i) derives the p_x-fibre under `deg_i(x) = 1` inside')
    print('  its own derivation ("c is x\'s only side-i neighbour"), so at')
    print('  deg_i(x) >= 2 there is no sweep lemma at all.  And even given')
    print('  one, the fibre is pi_{c_j} whenever c_j is a HUB -- a PLANE,')
    print('  not A^3 -- while `(*)` bounds the bad locus only in P^3.  One')
    print('  t_0 with dim(A cap Sigma_{t_0}) = 2 is PERMITTED by `(*)`')
    print('  (finitely many) and contributes a whole BAD PLANE.')
    rng = random.Random(SEED + 8191)
    built, checked = 0, 0
    for _ in range(ntry):
        pc1, pc2 = rand_line(rng)
        Lc = span([pc1, pc2])
        t0v = pt_in(Lc, rng, 9)
        if rank([t0v]) == 0:
            continue
        Sig = sigma_at(t0v)
        # a 2-dimensional slice of Sigma_{t_0}: exactly the shape `(*)`
        # tolerates at finitely many t
        P2 = span([sub_pt(Sig, rng, 9) for _ in range(2)])
        if dim(P2) != 2:
            continue
        A = P2
        if not star_ok(A, pc1, pc2):
            continue
        checked += 1
        # the bad fibre over t_0 is a PLANE of P^3, and `(*)` holds
        bad = nullspace([[sum(a * b for a, b in
                              zip(f, wedge2(I4[k], t0v))) for k in range(4)]
                         for f in nullspace(A)])
        if dim(bad) != 3:
            continue
        assert dim(A) <= 2, 'the witness A is not the 2-dim slice'
        # every p in that plane is BAD, so a fibre confined to it is
        # entirely bad while `(*)` holds
        allbad = True
        for _k in range(8):
            p = pt_in(bad, rng, 9)
            if rank([p]) == 0:
                continue
            if not contains(A, [wedge2(p, t0v)]):
                allbad = False
        assert allbad, 'the constructed bad plane is not bad'
        built += 1
        if built >= 12:
            break
    assert built >= 1, 'no witness plane built'
    print(f'  {checked} constructed (A, L_c) with `(*)` HOLDING and one')
    print(f'  t_0 carrying dim(A cap Sigma_{{t_0}}) = 2; at {built} of them')
    print('  the bad locus CONTAINS A WHOLE PLANE of P^3, asserted pointwise')
    print('  -- so `(*)` alone does not make the bad locus proper in a')
    print('  fibre confined to a plane.  Whether a chart can put pi_{c_1}')
    print('  on that plane is NOT claimed here; the point is that `(*)` as')
    print('  stated does not exclude it.')
    print(f'  [{time.time() - t0:.1f}s]')
    return built


MODES = {'classify': run_classify, 'five': run_five, 'low': run_low,
         'pop': run_pop, 'reach': run_reach, 'fibre': run_fibre}


def main(argv):
    if len(argv) < 2 or argv[1] not in MODES and argv[1] != 'validate':
        print(__doc__)
        print('usage: bline.py {' + ' | '.join(MODES) + ' | validate}')
        return 2
    if argv[1] == 'validate':
        for name in ('classify', 'five', 'low', 'pop', 'reach', 'fibre'):
            MODES[name]()
            print()
        return 0
    MODES[argv[1]]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
