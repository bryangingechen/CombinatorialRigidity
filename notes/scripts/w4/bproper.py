"""
Direction BPROPER (ordinal 69) -- PROVE (PENCIL-SATURATES-CHART) AT A
NON-PATH SIDE, i.e. that the `Sigma_x <= rho_bar_i` locus is a PROPER
subvariety of `Chart(H)` there.

  THE TARGET the spec names -- (BE-113)(i) item 1's own words, *"the
  successor's target ... a CLASS statement, not a hunt"*: at a NON-PATH
  side with deg_i(y) = 1, is the bad locus proper?  (BE-110)(iii)
  excludes non-properness at a PATH side outright; off paths it was
  UNWITNESSED RATHER THAN EXCLUDED over (BE-110)(iv)'s 668-row cap, and
  (BE-109)(iv) disclosed that BSIGMA's planted sampler reached only 5 of
  16 bucket-A topologies -- all five of them paths.

  THE ANSWER, said at the top, and it is TWO results of opposite sign.

  (1) PROPERNESS IS A THEOREM AT EVERY SIDE, PATH OR NOT, and it needs
      no replacement for `assert_generic_star` and no case analysis on
      the projected pair lines at all -- the whole question moves into
      p_x, where a Klein-quadric incidence count settles it uniformly.

    (BE-114) THE PENDANT REDUCTION.  At deg_i(x) = 1 with side
             neighbour c, motions of side i are motions of
             `core = side_i - x` with ONE free multiplier added, so
                  rho_bar_i = <p_x ^ p_c>  +  A,     A := rho_bar(core; c, y)
             and A DOES NOT INVOLVE p_x.  Since p_x ^ p_c lies in
             Sigma_x, Sigma_x cap (<l> + A) = <l> + (Sigma_x cap A), so
                  dim(rho_bar_i cap Sigma_x) = dim(A cap Sigma_x) + [l notin A]
                  rho_i                      = dim A               + [l notin A]
             and BAD (`Sigma_x <= rho_bar_i` with rho_i <= 5) is EXACTLY
                  l notin A:  dim A <= 4 and dim(A cap Sigma_x) = 2
                  l in A   :  dim A <= 5 and Sigma_x <= A.

    (BE-115) THE ALPHA-PLANE INCIDENCE LEMMA.  For a FIXED subspace
             A <= Lambda^2 K^4 and a fixed plane pi of P^3:
               (a) dim A <= 5  =>  {p in pi : Sigma_p <= A} != pi,
                   because Sigma_{p1} + Sigma_{p2} + Sigma_{p3} =
                   Lambda^2 K^4 for any 3 independent points;
               (b) dim A <= 4  =>  {p in pi : dim(A cap Sigma_p) >= 2}
                   != pi, UNLESS Lambda^2 pi <= A -- by counting the
                   incidence {(p, l) : p in l in P(A) cap Q}.
             Both loci are closed, so both are PROPER subvarieties.

    (BE-116) PROPERNESS.  p_x always lies in pi_c (the pencil condition
             at c), and p_c lies in pi_c too -- so in the one exceptional
             case of (BE-115)(b), Lambda^2 pi_c <= A, the hinge line
             l = p_x ^ p_c lies in Lambda^2 pi_c <= A and the OTHER
             branch applies, which (a) makes proper.  Hence at EVERY
             side with deg_i(x) = 1 the bad locus meets each p_x-fibre of
             the chart in a proper closed subvariety.  One chart point
             off it is all (BE-14) needs ((BE-16) + (BE-69)).

  (2) AND THE HUNT VERDICT IT REPLACES IS REFUTED.  BSIGMA's planted
      sampler failed at hub-carrying sides for a SAMPLER reason, not a
      geometric one: it drew each hub's flag plane at random and then
      intersected it with the planted plane, forcing the hub's
      neighbours onto ONE LINE and failing `assert_generic_star`.  Give
      a hub inside the planted plane THAT PLANE as its flag and the
      whole obstruction disappears.

    (BE-117) THE CAP IS REPAIRED: 16 of 16 bucket-A topologies, not 5,
             and the shape FIRES at 11 of them -- cycles, thetas and a
             subdivided K4 included.  (BE-109)(iv)'s *"unmeasured, not
             excluded"* is now MEASURED and REALIZED off paths.

    (BE-118) AND IT FIRES AT rho_i = 4, INSIDE BUCKET A.  (BE-110)(ii)'s
             floor is a PATH theorem and stays one; (BE-110)(iv)'s
             VERDICT -- *"`dim = 3 with rho <= 4`: none found in the
             bucket a peel in the generic flag regime can present"* --
             is REFUTED by a witness whose regime is CHECKED on a full
             constructed peel.  This is one of the four items
             (BE-113)'s *What would change this* named.

    (BE-119) THE deg_i(x) >= 2 HALF ((BE-113)'s price (d), unmeasured
             anywhere until now): rho_bar_i <= <p_x ^ p_{c_1}> + A still
             holds, so `Sigma_x <= rho_bar_i` still forces
             dim(A cap Sigma_x) >= 2 and (BE-115) still makes that
             proper whenever dim A <= 4 -- with dim A in {5, 6} the
             named residual.

    (BE-120) THE PRICE, AND IT IS PRICED DOWN.  Every exhibited row
             carries the shortfall control, ASSERTED: `margin <= 0` at
             Pi_x, Pi_y and <M> -- the three blocks (BE-101)(ii) and
             `Phase39.md` item 0(c) are about.  What the non-path rows DO
             break is `U = Lambda^2 K^4`, because planting off a path
             costs `a_i >= 1` and hence `a_1 + a_2 > max(0, 6-d_1-d_2)`:
             they are the FIRST exhibited inhabitants of (BE-101)(iii)'s
             live block, BDOUBLE's own named breaker -- and harmless,
             since the F13 control shows the SAME graph drawn freely has
             `a = (0,0)`, `dim(rho_bar_1 cap Sigma_x) = 1` and ATTAINS,
             and (BE-14) is EXISTENTIAL.

    (BE-121) Job 3's residual, the board, the reading, the E-rider.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `reduce`  (BE-114)  The reduction, as an identity of SPACES, and the
            dichotomy, at blind and planted draws over BOTH buckets --
            plus p_x-independence of A checked by MOVING p_x.
  `alpha`   (BE-115)  The incidence lemma's conclusion and its ONE
            exceptional case, on randomly drawn subspaces of every
            dimension; the exception exhibited, not assumed away.
  `proper`  (BE-116)  Properness exercised ON THE BAD LOCUS: at every
            planted bad row, sweep p_x over its actual chart freedom and
            assert the bad set is a proper subset of it.
  `plant`   (BE-117)  The repaired planter's census, side-library-wide,
            against BSIGMA's 5-of-16 -- with the ONE changed line named.
  `peel`    (BE-118)  The full constructed peel: a non-path bucket-A
            side glued to a subdivided 3-connected skeleton at two
            NON-ADJACENT hubs, with the regime asserted and the price
            measured.
  `degx`    (BE-119)  The deg_i(x) >= 2 measurement, with dim A named.
  `support` (BE-121)  The sampler-support audit for every population
            here: what it varies, and what it holds fixed.
  `validate`          A reduced run of all seven.

Exact Q throughout (`fractions.Fraction`); single seed 20260902, printed
by every mode.  NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import os
import random
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- This driver is the TWENTY-FOURTH `kbare/` consumer and takes the
# --- chain TWENTY-TWO deep (`... -> bsatur -> bsigma -> bproper`).  NO
# --- MOVE MADE.  It is also `bsigma.wedge3`'s FIRST second consumer, a
# --- new move-down item recorded in the draft's harness note.
from exactcore import hat, wedge2, rank, nullspace, neighbors          # noqa: E402
from bimage import (contains, dim, isect, klein, lam2, pencil_space,   # noqa: E402
                    plane_at, rho_bar_of, same_space, span, v4, pt_in)
from bpeel import SKELETONS, delta_pair, rnode_shaped, subdivided      # noqa: E402
from bdecor import (assemble, d3, draw_branch, flag_assignment,           # noqa: E402
                    hubs_and_branches)
from bunif import SEED, blocks_of, flag_frame                          # noqa: E402
from bsatur import margin_at, row_of, sigma_at                         # noqa: E402
from bsigma import side_library, sample_side_config, wedge3            # noqa: E402
from binduc import assert_generic_star                                 # noqa: E402
from kbare_common import verts_of                                      # noqa: E402

PIX, PIY, MB, ALLU = ('Pix',), ('Piy',), ('M',), tuple(
    sorted(('Pix', 'M', 'L', 'Piy')))


# =================================================== (BE-114) primitives

def core_of(side, x):
    """`side - x`: the side with the pendant terminal DELETED.  Its own
    terminals are (c, y) with c the unique side-neighbour of x."""
    return [e for e in side if x not in e]


def reduction_data(side, aff, x, y):
    """(A, dimA, l, rho_bar_i, rho_i) at one configuration -- the five
    quantities (BE-114) relates.  `A` is computed on the CORE alone, so it
    cannot depend on p_x even by accident."""
    nb = neighbors(side)
    c = sorted(nb[x], key=str)[0]
    core = core_of(side, x)
    if c == y or not core:
        A, dA = [], 0
    else:
        A, dA, _dM, _r = rho_bar_of(core, aff, c, y)
    S, rho, _dM2, _r2 = rho_bar_of(side, aff, x, y)
    l = wedge2(hat(aff[x]), hat(aff[c]))
    return A, dA, l, S, rho, c


def bad_at(A, dA, l, px):
    """(BE-114)'s dichotomy, evaluated on CORE data plus p_x alone: is
    `Sigma_x <= <l> + A` with dim(<l> + A) <= 5?"""
    Sig = sigma_at(px)
    inA = contains(A, [l]) if A else False
    d = dim(isect(A, Sig)) if A else 0
    if inA:
        return dA <= 5 and d == 3
    return dA <= 4 and d == 2


# ==================================================== mode: reduce (BE-114)

def run_reduce(ndraw=6, nplant=6, nmove=3):
    t0 = time.time()
    print(f'== reduce: (BE-114) THE PENDANT REDUCTION, seed {SEED}')
    print('  At deg_i(x) = 1 the pendant edge xc carries a FREE multiplier,')
    print('  so rho_bar_i = <p_x ^ p_c> + A with A = rho_bar(side - x; c, y)')
    print('  a function of the CORE POINTS ALONE.  Asserted below as an')
    print('  identity of SUBSPACES, together with the two dichotomy')
    print('  identities and the p_x-independence of A (checked by MOVING')
    print('  p_x inside pi_c and recomputing A).')
    LA, LB = side_library()
    tot, planted, moved, seen = 0, 0, 0, {}
    for tag, lib in (('A', LA), ('B', LB)):
        for (name, E, x, y) in lib:
            nb = neighbors(E)
            if len(nb[x]) != 1:
                continue
            rows = []
            for sd in range(ndraw):
                rng = random.Random(SEED + 991 * sd + len(name))
                aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
                if aff is not None:
                    rows.append((aff, False))
            for sd in range(nplant):
                rng = random.Random(SEED + 331 * sd + 3 * len(name))
                Ppi = span([v4(rng, 20) for _ in range(3)])
                if dim(Ppi) != 3:
                    continue
                aff = plant_side(E, rng, Ppi, sorted(nb[x], key=str)[0])
                if aff is not None:
                    rows.append((aff, True))
            for ri, (aff, isp) in enumerate(rows):
                A, dA, l, S, rho, c = reduction_data(E, aff, x, y)
                if not S:
                    continue
                px = hat(aff[x])
                # (i) THE REDUCTION, as an identity of SPACES
                assert same_space(span((A or []) + [l]), S), \
                    ('the pendant reduction FAILS', tag, name, rho, dA)
                # (ii) the two dichotomy identities
                inA = contains(A, [l]) if A else False
                dcap = dim(isect(A, sigma_at(px))) if A else 0
                assert rho == dA + (0 if inA else 1), \
                    ('rho_i != dim A + [l notin A]', name, rho, dA, inA)
                assert dim(isect(S, sigma_at(px))) == dcap + (0 if inA else 1), \
                    ('the corank dichotomy fails', name)
                # (iii) BAD is decided by CORE data plus p_x alone
                isbad = (dim(isect(S, sigma_at(px))) == 3 and rho <= 5)
                assert isbad == bad_at(A, dA, l, px), \
                    ('the dichotomy misclassifies a row', name)
                seen[(tag, rho, dA, dcap)] = seen.get(
                    (tag, rho, dA, dcap), 0) + 1
                tot += 1
                planted += 1 if isp else 0
                # (iv) p_x-INDEPENDENCE OF A: move p_x inside pi_c and
                #      recompute A on the core.  A must not budge.  Run on
                #      the first two rows of each topology only -- the cost
                #      is one rigidity kernel per move, and the statement is
                #      an algebraic identity, not a frequency claim.
                if ri >= 2:
                    continue
                pic = plane_at(E, aff, c)
                if pic is None:
                    continue
                for k in range(nmove):
                    r2 = random.Random(SEED + 71 * k + len(name))
                    q = pt_in(pic, r2, 20)
                    if q[3] == 0 or rank([q, hat(aff[c])]) != 2:
                        continue
                    aff2 = dict(aff)
                    aff2[x] = tuple(F(q[i], q[3]) for i in range(3))
                    if aff2[x] in {v for w, v in aff.items() if w != x}:
                        continue
                    A2, dA2, _l2, _S2, _r2, _c2 = reduction_data(
                        E, aff2, x, y)
                    assert dA2 == dA and (dA == 0 or same_space(A2, A)), \
                        ('A moved when p_x moved', name)
                    moved += 1
    print(f'  {tot} legal side draws over {len(LA) + len(LB)} topologies '
          f'({planted} of them PLANTED at the (BE-109) stratum):')
    print('    `rho_bar_i = <p_x ^ p_c> + A` ASSERTED as SPACES at every one;')
    print('    `rho_i = dim A + [l notin A]` and the corank dichotomy too;')
    print(f'    A unchanged under {moved} legal moves of p_x inside pi_c.')
    print('  (bucket, rho, dim A, dim(A cap Sigma_x)) census:')
    for k in sorted(seen):
        print(f'    {k}: {seen[k]}')
    assert tot > 100 and moved > 60, 'the reduction sweep did not reproduce'
    print(f'  reduce: {time.time() - t0:.1f}s')
    return True


# ===================================================== mode: alpha (BE-115)

def rand_sub(rng, d, s=9):
    """A random d-dimensional subspace of Lambda^2 K^4."""
    for _ in range(60):
        rows = [[F(rng.randint(-s, s)) for _ in range(6)] for _ in range(d)]
        if dim(rows) == d:
            return span(rows)
    return None


def tot_singular(A):
    """Is Q|_A identically zero (A totally singular for the Klein form)?"""
    return all(klein(a, b) == 0 for a in A for b in A)


def run_alpha(nsub=40, npt=12):
    t0 = time.time()
    print(f'== alpha: (BE-115) THE ALPHA-PLANE INCIDENCE LEMMA, seed {SEED}')
    print('  Sigma_p = p ^ K^4 is an alpha-PLANE of the Klein quadric.  The')
    print('  lemma bounds how badly a FIXED subspace A can meet the family')
    print('  {Sigma_p : p in pi} over a fixed plane pi.  Two clauses:')
    print('   (a) dim A <= 5 => NOT every p in pi has Sigma_p <= A;')
    print('   (b) dim A <= 4 => NOT every p in pi has dim(A cap Sigma_p) >= 2,')
    print('       UNLESS Lambda^2 pi <= A -- the ONE exception, exhibited.')
    rng = random.Random(SEED)
    # (0) the proof step behind (a): three independent points SPAN the screw
    #     space through their alpha-planes.
    nspan = 0
    for _ in range(npt * 4):
        P = [v4(rng, 9) for _ in range(3)]
        if rank(P) != 3:
            continue
        U = span(sigma_at(P[0]) + sigma_at(P[1]) + sigma_at(P[2]))
        assert dim(U) == 6, 'three alpha-planes over a plane do not span'
        nspan += 1
    print(f'  (0) `Sigma_p1 + Sigma_p2 + Sigma_p3 = Lambda^2 K^4` at '
          f'{nspan} independent triples -- the whole content of (a).')
    # (1) the two clauses, on random subspaces of every dimension
    cens = {}
    exc = 0
    for d in range(1, 7):
        for _ in range(nsub):
            A = rand_sub(rng, d)
            if A is None:
                continue
            Ppi = span([v4(rng, 9) for _ in range(3)])
            if dim(Ppi) != 3:
                continue
            lp = lam2(Ppi)
            inA = contains(A, lp)
            n2, n3, npts = 0, 0, 0
            for _k in range(npt):
                p = pt_in(Ppi, rng, 9)
                if rank([p]) != 1:
                    continue
                Sig = sigma_at(p)
                dc = dim(isect(A, Sig))
                n2 += 1 if dc >= 2 else 0
                n3 += 1 if dc == 3 else 0
                npts += 1
            if npts < 3:
                continue
            cens[(d, inA)] = cens.get((d, inA), 0) + 1
            # clause (a): Sigma_p <= A cannot hold at every sampled p
            if d <= 5:
                assert n3 < npts, ('(BE-115)(a) FAILS', d, dim(A))
            # clause (b): with dim A <= 4 and Lambda^2 pi not in A, the
            # `>= 2` locus misses at least one sampled point
            if d <= 4 and not inA:
                assert n2 < npts, ('(BE-115)(b) FAILS off its exception', d)
            if d <= 4 and inA:
                assert n2 == npts, \
                    'the exception did not fire where Lambda^2 pi <= A'
                exc += 1
    print('  (1) random-subspace census (dim A, Lambda^2 pi <= A) -> draws: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cens.items())))
    print(f'      clause (a) ASSERTED at every dim A <= 5 draw; clause (b) at')
    print(f'      every dim A <= 4 draw off the exception.  The exception')
    print(f'      `Lambda^2 pi <= A` is MEASURE ZERO, so a random draw never')
    print(f'      lands in it ({exc} here) -- it is BUILT in (2) below.')
    # (2) the exception, built on purpose, and its NEUTRALIZATION
    neu = 0
    for _ in range(npt * 2):
        Ppi = span([v4(rng, 9) for _ in range(3)])
        if dim(Ppi) != 3:
            continue
        lp = lam2(Ppi)
        A = span(lp + [[F(rng.randint(-9, 9)) for _ in range(6)]])
        if dim(A) != 4:
            continue
        pc = pt_in(Ppi, rng, 9)
        ok = True
        for _k in range(npt):
            p = pt_in(Ppi, rng, 9)
            if rank([p, pc]) != 2:
                continue
            # every p in pi is in the `>= 2` locus ...
            assert dim(isect(A, sigma_at(p))) >= 2, 'the exception broke'
            # ... but the hinge line p ^ p_c lies in Lambda^2 pi <= A, so
            # (BE-114)'s OTHER branch applies, and (a) governs it.
            assert contains(lp, [wedge2(p, pc)]), \
                'p ^ p_c is not inside Lambda^2 pi for two points of pi'
            assert contains(A, [wedge2(p, pc)]), 'the neutralization fails'
            ok = ok and dim(isect(A, sigma_at(p))) < 3
        assert ok, 'Sigma_p <= A at every point of the exceptional plane'
        neu += 1
    print(f'  (2) THE EXCEPTION IS NEUTRALIZED at {neu} constructed A >= '
          f'Lambda^2 pi:')
    print('      p in pi and p_c in pi force p ^ p_c in Lambda^2 pi <= A, so')
    print('      the row is in the `l in A` branch, where clause (a) bites.')
    print('      THIS is why p_c in pi_c is load-bearing in (BE-116).')
    print('  (3) totally-singular A, checked by hand in the write-up: A <=')
    print('      Sigma_q gives dim(A cap Sigma_p) <= 1 (p != q) and A <=')
    print('      Lambda^2 pi\' gives 2 only on pi\'.  Asserted here:')
    ts = 0
    for _ in range(npt * 2):
        q = v4(rng, 9)
        if rank([q]) != 1:
            continue
        A = sigma_at(q)
        assert tot_singular(A), 'an alpha-plane is not totally singular'
        for _k in range(npt):
            p = v4(rng, 9)
            if rank([p, q]) != 2:
                continue
            assert dim(isect(A, sigma_at(p))) == 1, \
                'two alpha-planes do not meet in a line'
            ts += 1
    print(f'      {ts} (alpha-plane, point) pairs: dim(Sigma_q cap Sigma_p) '
          f'= 1 exactly.')
    print(f'  alpha: {time.time() - t0:.1f}s')
    return True


# ============================================ the repaired planter (BE-117)

def plant_side(E, rng, plane, off, s=20, tries=80):
    """The (BE-109) stratum planted on a SIDE: every point inside one plane
    `plane` except `off` (the pendant terminal's neighbour c), which goes
    off it.

    DIVERGENCE, deliberate, and it is (BE-117)'s whole content.  This is
    `bsigma.sample_side_config(..., plane=, off=)` with ONE line changed: a
    hub z INSIDE the planted plane is given THAT PLANE as its flag
    (`Bp[z] = plane`) instead of a random plane through its point.  In
    BSIGMA's version `isect(plane, Bp[z])` is a LINE, so z and all its
    neighbours land on one line and `assert_generic_star` rejects the draw
    -- which is exactly why (BE-109)(iv)'s planted sampler reached only the
    five path topologies.  Every other line is BSIGMA's, including the
    shape guard (degree->=3 vertices an independent set) and the `off`-hub
    treatment (its in-plane neighbours DO go on the line pi cap pi_off,
    which is forced by the pencil condition at a body off the plane).
    """
    nb = neighbors(E)
    V = sorted(verts_of(E), key=str)
    hubs = [z for z in V if len(nb[z]) >= 3]
    for z in hubs:
        if any(w in hubs for w in nb[z]):
            return None
    for w in V:
        if w in hubs:
            continue
        if len([z for z in nb[w] if z in hubs]) > 1:
            return None
    for _ in range(tries):
        homs, Bp, ok = {}, {}, True
        for z in hubs:
            homs[z] = v4(rng, s) if z == off else pt_in(plane, rng, s)
        for z in hubs:
            if z == off:
                bas = [homs[z]] + [v4(rng, s) for _ in range(2)]
                if rank(bas) != 3:
                    ok = False
                    break
                Bp[z] = span(bas)
            else:
                Bp[z] = plane                    # <-- THE ONE CHANGED LINE
        if not ok:
            continue
        for w in V:
            if w in homs:
                continue
            hz = [z for z in nb[w] if z in hubs]
            if w != off:
                base = (isect(plane, Bp[hz[0]]) if hz else plane)
                if not base or dim(base) == 0:
                    ok = False
                    break
                homs[w] = pt_in(base, rng, s)
            else:
                homs[w] = v4(rng, s)
        if not ok:
            continue
        if any(h[3] == 0 for h in homs.values()):
            continue
        aff = assemble(E, homs)
        if aff is None:
            continue
        return aff
    return None


def run_plant(nplant=8):
    t0 = time.time()
    print(f'== plant: (BE-117) THE CAP IS A SAMPLER ARTEFACT, seed {SEED}')
    print('  (BE-109)(iv) disclosed that the planted stratum drew at only')
    print('  5 of 16 bucket-A topologies -- all five PATHS -- and concluded')
    print('  the shape at a non-path side was UNMEASURED, not excluded.')
    print('  One line of the planter is responsible: a hub inside the')
    print('  planted plane was given a RANDOM flag through its point, so')
    print('  its neighbours were forced onto pi cap Bp[z], a LINE, and')
    print('  `assert_generic_star` rejected every such draw.  Give the hub')
    print('  the planted plane itself and the obstruction disappears.')
    LA, LB = side_library()
    out = {}
    for tag, lib in (('A (deg_i(y) = 1)', LA), ('B (deg_i(y) >= 2)', LB)):
        drew, hits, nodraw, hitnames, cens = 0, 0, [], [], {}
        for (name, E, x, y) in lib:
            nb = neighbors(E)
            if len(nb[x]) != 1:
                continue
            c = sorted(nb[x], key=str)[0]
            ispath = name.startswith('path')
            f1 = d3(E)
            n, h = 0, 0
            for sd in range(nplant):
                rng = random.Random(SEED + 331 * sd + 3 * len(name))
                Ppi = span([v4(rng, 20) for _ in range(3)])
                if dim(Ppi) != 3:
                    continue
                aff = plant_side(E, rng, Ppi, c)
                if aff is None:
                    continue
                S, rho, dM, _r = rho_bar_of(E, aff, x, y)
                if not S:
                    continue
                ds = dim(isect(S, sigma_at(hat(aff[x]))))
                A, dA, l, _S, _rho, _c = reduction_data(E, aff, x, y)
                a1 = dM - 6 - f1
                assert a1 >= 0, 'a_i went negative -- the oracle disagrees'
                assert ds >= max(0, rho - 3), 'the modular law is violated'
                cens[(rho, ds, dA, a1)] = cens.get((rho, ds, dA, a1), 0) + 1
                n += 1
                if ds == 3 and rho <= 5:
                    h += 1
                    assert bad_at(A, dA, l, hat(aff[x])), \
                        'a hit row is not classified BAD by (BE-114)'
                    # THE SECOND PRICE OF THE PLANT, and it separates the
                    # path case from every other: at a PATH side the side
                    # is a tree, its hinge rows are independent at EVERY
                    # configuration and a_i = 0 identically; off paths the
                    # flat core GAINS motions, so a_i >= 1.
                    if ispath:
                        assert a1 == 0, ('a path side gained motions', name)
                    else:
                        assert a1 >= 1, \
                            ('a non-path planted hit with a_i = 0', name)
            if n == 0:
                nodraw.append(name)
            else:
                drew += 1
            if h > 0:
                hits += 1
                hitnames.append((name, n, h))
        out[tag] = (drew, len(lib), hits, nodraw, hitnames, cens)
        print(f'  bucket {tag}: the planted stratum DRAWS at {drew} of '
              f'{len(lib)} topologies and FIRES at {hits}.')
        if nodraw:
            print('    no draw at (disclosed, not smoothed):')
            for nm in nodraw:
                print(f'      - {nm}')
        for (nm, n, h) in hitnames:
            print(f'      HIT  {nm:42s} {h}/{n} planted rows')
        print('    (rho, dim(rho_bar cap Sigma_x), dim A, a_i): ' + ', '.join(
            f'{k}: {v}' for k, v in sorted(cens.items())))
    drewA, nA, hitsA, ndA, hnA, _c = out['A (deg_i(y) = 1)']
    assert drewA == nA, ('the repaired planter still misses a topology', ndA)
    assert hitsA >= 8, 'the planted stratum did not fire off paths'
    nonpath = [nm for (nm, _n, _h) in hnA if not nm.startswith('path')]
    print(f'  VERDICT.  {drewA} of {nA} bucket-A topologies drawable (BSIGMA: '
          f'5 of 16), FIRING at {hitsA}, of which {len(nonpath)} are NOT')
    print('  paths.  (BE-109)(iv)\'s cap is REPAIRED: the tail stratum is a')
    print('  hub-carrying phenomenon too.  The non-path hits, by name:')
    for nm in nonpath:
        print(f'    - {nm}')
    assert len(nonpath) >= 6, 'the non-path family did not reproduce'
    print('  AND THE PLANT HAS A SECOND PRICE OFF PATHS, asserted above at')
    print('  every hit row: a_i = 0 at every PATH hit (a path is a tree, so')
    print('  its hinge rows are independent at every configuration and')
    print('  a_i = dim M - 6 - def_3 vanishes identically), and a_i >= 1 at')
    print('  every NON-PATH hit -- the flat core GAINS motions.  So the')
    print('  non-path realizations sit OFF the a_1 = a_2 = 0 regime in which')
    print('  (BE-101)(ii) and S-mark\'s pin (BE-22)(iii) both live.  BSIGMA')
    print('  could not see this: its planted population was paths only.')
    print(f'  plant: {time.time() - t0:.1f}s')
    return True


# ==================================================== mode: proper (BE-116)

def px_freedom(E, aff, x, c):
    """The chart freedom in p_x with the CORE held fixed, as a subspace of
    K^4 to draw from -- and a flag saying whether it is the whole space.

    The pencil condition at c puts p_x inside pi_c.  When c has TWO or more
    core neighbours (deg_side(c) >= 3) their points already span pi_c with
    p_c, so pi_c is core-determined and p_x is confined to that PLANE.
    When deg_side(c) = 2, pi_c follows p_x and the freedom is all of K^4."""
    nb = neighbors(E)
    if len(nb[c]) >= 3:
        pic = plane_at(E, aff, c)
        return pic, False
    I4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
    return I4, True


def run_proper(nplant=6, nsweep=16):
    t0 = time.time()
    print(f'== proper: (BE-116) PROPERNESS, EXERCISED ON THE BAD LOCUS, '
          f'seed {SEED}')
    print('  Properness is not measured by failing to find a hit -- it is')
    print('  measured by STANDING ON a hit and stepping off it.  At every')
    print('  planted bad row below, p_x is swept over its ACTUAL chart')
    print('  freedom (pi_c when the core determines pi_c, all of P^3 when')
    print('  it does not), the core -- hence A -- held FIXED, and the bad')
    print('  set is asserted to be a PROPER subset of that sweep.')
    LA, LB = side_library()
    rows, tot, worst = 0, 0, 0
    percase = []
    for (name, E, x, y) in LA + LB:
        nb = neighbors(E)
        if len(nb[x]) != 1:
            continue
        c = sorted(nb[x], key=str)[0]
        nb_bad, nb_tot, ncase = 0, 0, 0
        for sd in range(nplant):
            rng = random.Random(SEED + 331 * sd + 3 * len(name))
            Ppi = span([v4(rng, 20) for _ in range(3)])
            if dim(Ppi) != 3:
                continue
            aff = plant_side(E, rng, Ppi, c)
            if aff is None:
                continue
            A, dA, l, S, rho, _c = reduction_data(E, aff, x, y)
            if not S or not (dim(isect(S, sigma_at(hat(aff[x])))) == 3
                             and rho <= 5):
                continue                      # only stand on BAD rows
            ncase += 1
            basis, whole = px_freedom(E, aff, x, c)
            if basis is None:
                continue
            # the planted p_x is IN the fibre and IS bad, so what the sweep
            # shows is a NONEMPTY proper subset, not an empty one.
            pxh = hat(aff[x])
            assert dim(span(basis + [pxh])) == dim(span(basis)), \
                'the planted p_x is not in its own freedom fibre'
            assert bad_at(A, dA, wedge2(pxh, hat(aff[c])), pxh), \
                'the planted p_x is not bad -- the row is not on the locus'
            good, bad = 0, 0
            for k in range(nsweep):
                r2 = random.Random(SEED + 7919 * k + 13 * sd + len(name))
                q = pt_in(basis, r2, 20)
                if q[3] == 0 or rank([q, hat(aff[c])]) != 2:
                    continue
                l2 = wedge2(q, hat(aff[c]))
                if bad_at(A, dA, l2, q):
                    bad += 1
                else:
                    good += 1
            assert good > 0, \
                ('NO good p_x in the sweep -- properness would FAIL',
                 name, dA, whole)
            nb_bad += bad
            nb_tot += good + bad
            rows += 1
            worst = max(worst, (bad * 100) // max(1, good + bad))
        if ncase:
            percase.append((name, ncase, nb_bad, nb_tot, whole))
        tot += ncase
    print(f'  {rows} planted BAD rows over {len(percase)} topologies; at each,')
    print(f'  a {nsweep}-point sweep of p_x over its own freedom:')
    for (nm, nc, nbd, nbt, whole) in percase:
        kind = 'p_x free in P^3' if whole else 'p_x confined to pi_c'
        print(f'    {nm:42s} {nc} bad rows, {nbd}/{nbt} of the sweep bad '
              f'({kind})')
    print(f'  ASSERTED at every row: the sweep contains a GOOD p_x, so the')
    print(f'  bad locus is a PROPER subset of the p_x-fibre.  Worst observed')
    print(f'  bad fraction: {worst}%.')
    assert rows >= 8, 'the properness sweep did not reproduce'
    print('  THEOREM (BE-116), PROVED not measured: at every side with')
    print('  deg_i(x) = 1 -- PATH OR NOT -- the locus `Sigma_x <= rho_bar_i,')
    print('  rho_i <= 5` is a PROPER subvariety of the chart, by (BE-114) +')
    print('  (BE-115) with p_c in pi_c neutralizing the one exception.')
    print(f'  proper: {time.time() - t0:.1f}s')
    return True


# ====================================================== mode: peel (BE-118)

# NON-ADJACENT hub pairs of the two skeletons that have any -- the peel needs
# x !~ y in the skeleton, else `side2 + (x,y)` carries a parallel pair after
# suppression and `rnode_shaped` rejects it as a P-node.
NONADJ = {'K33': [('A', 'B'), ('A', 'C'), ('D', 'E')],
          'prism': [('A', 'E'), ('B', 'F'), ('C', 'D')]}


def composite(skname, prof, xy, side1):
    """A CONSTRUCTED peel: the subdivided skeleton (side 2) with a non-path
    bucket-A piece (side 1) glued at the two NON-ADJACENT hubs x, y.  The
    piece is a `side_library` entry, whose terminals ARE x and y.  Disclosed
    as constructed: it is not drawn from a habitat census."""
    x, y = xy
    sk = SKELETONS[skname]
    E2 = list(subdivided(sk, prof))
    ren = {}
    E1 = []
    for (a, b) in side1:
        aa = x if a == 'x' else (y if a == 'y' else ren.setdefault(a, f's1{a}'))
        bb = x if b == 'x' else (y if b == 'y' else ren.setdefault(b, f's1{b}'))
        E1.append((aa, bb))
    return E1 + E2, E1, E2, x, y


def plant_peel(skname, prof, xy, side1, rng, s=20, tries=200):
    """Plant the (BE-109) stratum on SIDE 1 of a composite peel and draw
    side 2 freely around it, honouring the flag conditions at x and y."""
    E, E1, E2, x, y = composite(skname, prof, xy, side1)
    nb = neighbors(E)
    if len(neighbors(E1)[x]) != 1 or len(neighbors(E1)[y]) != 1:
        return None
    c = sorted(neighbors(E1)[x], key=str)[0]
    for _ in range(tries):
        Ppi = span([v4(rng, s) for _ in range(3)])
        if dim(Ppi) != 3:
            continue
        aff1 = plant_side(E1, rng, Ppi, c)
        if aff1 is None:
            continue
        homs = {w: hat(v) for w, v in aff1.items()}
        # the flags at x and y: any plane through the side-1 star, then
        # side 2's neighbours of x (resp. y) are drawn inside it.
        fixed, ok = {}, True
        for z in (x, y):
            star = [homs[z]] + [homs[w] for w in neighbors(E1)[z]]
            bas = list(star)
            for _f in range(8):
                if rank(bas) >= 3:
                    break
                bas.append(v4(rng, s))
            if rank(bas) != 3:
                ok = False
                break
            fixed[z] = (homs[z], nullspace([nullspace(bas)[0]]))
        if not ok:
            continue
        W, branches = hubs_and_branches(E, x, y)
        for z in W:
            if z in homs and z not in fixed:
                pz = plane_at(E1, aff1, z)
                if pz is None:
                    ok = False
                    break
                fixed[z] = (homs[z], pz)
        if not ok:
            continue
        P, B = flag_assignment(W, branches, rng, s=s, fixed=fixed)
        if P is None:
            continue
        pts = dict(homs)
        V1 = {w for e in E1 for w in e}
        for (z, zp, ints) in branches:
            if set(ints) <= V1 and ints:
                continue
            if not ints:
                continue
            g = draw_branch(P, B, z, zp, len(ints), rng, s=s)
            if g is None:
                ok = False
                break
            for w, cc in zip(ints, g):
                pts[w] = cc
        if not ok:
            continue
        for z in W:
            pts[z] = P[z]
        aff = assemble(E, pts)
        if aff is None:
            continue
        return E, E1, E2, x, y, aff, Ppi
    return None


def free_peel(skname, prof, xy, side1, rng, s=20, tries=120):
    """The F13 NEGATIVE CONTROL for `peel`: the SAME composite graph drawn
    freely -- no plant anywhere -- so that what the planted rows show is a
    property of the STRATUM and not of the graph."""
    E, E1, E2, x, y = composite(skname, prof, xy, side1)
    W, branches = hubs_and_branches(E, x, y)
    for _ in range(tries):
        P, B = flag_assignment(W, branches, rng, s=s)
        if P is None:
            continue
        pts = dict(P)
        ok = True
        for (z, zp, ints) in branches:
            if not ints:
                continue
            g = draw_branch(P, B, z, zp, len(ints), rng, s=s)
            if g is None:
                ok = False
                break
            for w, cc in zip(ints, g):
                pts[w] = cc
        if not ok:
            continue
        aff = assemble(E, pts)
        if aff is None:
            continue
        return E, E1, E2, x, y, aff
    return None


PEELJOBS = [
    ('K33', ('A', 'B'), '2 pendants + cycle(8) at distance 4'),
    ('K33', ('A', 'B'), '2 pendants + theta(3,4,4)'),
    ('K33', ('A', 'B'), '2 pendants + theta(4,4,4)'),
    ('K33', ('A', 'B'), '2 pendants + theta(3,4,5)'),
    ('K33', ('A', 'B'), '2 pendants + K4 subdivided x3'),
    ('prism', ('A', 'E'), '2 pendants + theta(3,4,4)'),
    ('prism', ('A', 'E'), '2 pendants + cycle(8) at distance 4'),
]


def side_named(name):
    LA, _LB = side_library()
    for (nm, E, x, y) in LA:
        if nm == name:
            return E, x, y
    raise KeyError(name)


def run_peel(nseed=3, prof=None, jobs=None):
    t0 = time.time()
    print(f'== peel: (BE-118) THE FULL PEEL -- rho_1 = 4 INSIDE BUCKET A, '
          f'seed {SEED}')
    print('  A CONSTRUCTED peel: a non-path bucket-A side glued at two')
    print('  NON-ADJACENT hubs of a subdivided 3-connected skeleton, so')
    print('  side 2 is R-NODE-SHAPED (with x ~ y the pair would suppress to')
    print('  a parallel edge -- a P-node -- and be rejected).  Every row')
    print('  passes `assert_generic_star` AND `verify_pencil_witness`, and')
    print('  the REGIME is asserted: `flag_frame` non-None.')
    jobs = jobs or PEELJOBS
    got_rows, hist, cc, mallh, ctrl, welded = 0, {}, {}, {}, {}, {}
    mb, shapes = {}, []
    shortfall, lowrho, att, nonatt, allbreak = 0, 0, 0, 0, 0
    for (skname, xy, s1name) in jobs:
        E1t, xt, yt = side_named(s1name)
        pr = prof or [3] * len(SKELETONS[skname])
        for sd in range(nseed):
            rng = random.Random(SEED + 613 * sd + 7 * len(s1name))
            g = plant_peel(skname, pr, xy, E1t, rng)
            if g is None:
                continue
            E, E1, E2, x, y, aff, Ppi = g
            dp = delta_pair(E, x, y)
            if dp is None:
                continue
            _d1, _d2, Ea, Eb = dp
            side1 = Ea if len(Ea) == len(E1) else Eb
            side2 = Eb if side1 is Ea else Ea
            if len(side1) != len(E1):
                continue
            assert rnode_shaped(side2, x, y), \
                'side 2 is not R-node-shaped -- the peel is not internal'
            assert not rnode_shaped(side1, x, y), \
                'side 1 is R-node-shaped, so it is not a bucket-A side'
            S1, r1, _dM, _r = rho_bar_of(side1, aff, x, y)
            px = hat(aff[x])
            ds = dim(isect(S1, sigma_at(px)))
            if ds != 3 or r1 > 5:
                continue
            fr = flag_frame(E, aff, x, y)
            assert fr is not None, \
                'the planted peel is OFF the generic flag regime'
            Bl = blocks_of(fr)
            assert contains(S1, Bl['Pix']), 'Pi_x is not inside rho_bar_1'
            pa = plane_at(E, aff, x)
            assert pa is not None, 'no closed-star plane at x'
            # EVERY plane through p_x is bad, legal or not -- 24 draws
            for k in range(24):
                r2 = random.Random(SEED + 97 * sd + k)
                bas = [px] + [v4(r2, 20) for _ in range(2)]
                if rank(bas) != 3:
                    continue
                assert contains(S1, pencil_space(px, span(bas))), \
                    'a plane through p_x is NOT bad'
            row = row_of(E, x, y, side1, side2, aff)
            assert row is not None, 'the row does not measure'
            assert row['r1'] == r1 and row['c1'][PIX] == 2, \
                ('c_1(Pi_x) is not 2', row['c1'][PIX])
            m = margin_at(row, PIX, 2)
            # (BE-120) THE SHORTFALL CONTROL.  Pi_x, Pi_y and <M> are
            # ASSERTED slack -- these are the blocks (BE-101)(ii)'s
            # redundancy theorem and `Phase39.md` *Hand-off* item 0(c) are
            # about.  `U = Lambda^2 K^4` is REPORTED, because (BE-101)(iii)
            # already records it as a LIVE block off the attaining case and
            # this population is deliberately off it.
            for blk, du in ((PIX, 2), (PIY, 2), (MB, 1)):
                mm = margin_at(row, blk, du)
                if mm > 0:
                    shortfall += 1
                assert mm <= 0, \
                    ('margin > 0 at a 2-block -- A SHORTFALL', s1name, blk)
            mall = margin_at(row, ALLU, 6)
            cap = min(row['d1'] + row['d2'], 6) + row['a1'] + row['a2']
            room = max(0, 6 - row['d1'] - row['d2'])
            # `U = Lambda^2 K^4` reads off rho, by definition of c_i
            assert row['c1'][ALLU] == row['r1'] \
                and row['c2'][ALLU] == row['r2'], 'c_i(Lambda^2 K^4) != rho_i'
            assert mall == row['r1'] + row['r2'] - 6 - row['slack'], \
                'the U = Lambda^2 K^4 margin is not rho_1 + rho_2 - 6 - slack'
            # `cap > 6` is EXACTLY (BE-101)(ii)'s a-inequality failing, and
            # then `reach = cap` is arithmetically impossible (reach <= 6).
            assert (cap > 6) == (row['a1'] + row['a2'] > room), \
                ('the cap is not the a-inequality', s1name, cap, room)
            # (BE-86)'s MEASURED identity rho_i = delta_i + a_i, RECORDED
            # rather than asserted: it needs the WELDED side at generic rank
            # too, and the planted stratum need not leave it there.
            welded[(row['r1'] - row['d1'] - row['a1'],
                    row['r2'] - row['d2'] - row['a2'])] = welded.get(
                (row['r1'] - row['d1'] - row['a1'],
                 row['r2'] - row['d2'] - row['a2']), 0) + 1
            if cap <= 6:
                assert row['reach'] == cap, \
                    ('a row with cap <= 6 does NOT attain', s1name)
                att += 1
            else:
                nonatt += 1
                allbreak += 1 if mall > 0 else 0
            hist[m] = hist.get(m, 0) + 1
            cc[(row['c1'][PIX], row['c2'][PIX])] = cc.get(
                (row['c1'][PIX], row['c2'][PIX]), 0) + 1
            mallh[mall] = mallh.get(mall, 0) + 1
            mb[(row['c1'][MB], row['c2'][MB])] = mb.get(
                (row['c1'][MB], row['c2'][MB]), 0) + 1
            if not shapes:
                shapes.append((skname, tuple(pr), s1name, len(verts_of(E)),
                               len(E), d3(E)))
            got_rows += 1
            if r1 <= 4:
                lowrho += 1
            if got_rows <= 2 or mall > 0:
                print(f'    {skname}{tuple(pr)} + `{s1name}` at {xy}: '
                      f'rho_1 = {r1}, dim(rho_bar_1 cap Sigma_x) = {ds}, '
                      f'c_1(Pi_x) = {row["c1"][PIX]},')
                print(f'      delta = ({row["d1"]},{row["d2"]}), '
                      f'a = ({row["a1"]},{row["a2"]}), '
                      f'slack = {row["slack"]}, reach = {row["reach"]}, '
                      f'cap = {cap},')
                print(f'      margin: Pi_x {m}, Pi_y '
                      f'{margin_at(row, PIY, 2)}, <M> '
                      f'{margin_at(row, MB, 1)}, Lambda^2 K^4 {mall}')
            # --- F13 NEGATIVE CONTROL: the SAME graph drawn FREELY
            if (skname, s1name) not in ctrl:
                r2 = random.Random(SEED + 5501 + len(s1name))
                gf = free_peel(skname, pr, xy, E1t, r2)
                if gf is not None:
                    Ef, _E1f, _E2f, xf, yf, afff = gf
                    dpf = delta_pair(Ef, xf, yf)
                    if dpf is not None:
                        _q1, _q2, Fa, Fb = dpf
                        s1f = Fa if len(Fa) == len(E1) else Fb
                        s2f = Fb if s1f is Fa else Fa
                        rowf = row_of(Ef, xf, yf, s1f, s2f, afff)
                        if rowf is not None:
                            Sf, rf, _dm, _rr = rho_bar_of(s1f, afff, xf, yf)
                            dsf = dim(isect(Sf, sigma_at(hat(afff[xf]))))
                            ctrl[(skname, s1name)] = (
                                rf, dsf, rowf['a1'], rowf['a2'],
                                rowf['reach'],
                                min(rowf['d1'] + rowf['d2'], 6)
                                + rowf['a1'] + rowf['a2'],
                                margin_at(rowf, ALLU, 6))
    print(f'  {got_rows} full-peel rows, EVERY one `Sigma_x <= rho_bar_1` '
          f'with rho_1 <= 5, `flag_frame` non-None, both gates,')
    print(f'  side 2 R-node-shaped.  Of those, {lowrho} have rho_1 <= 4 -- '
          f'INSIDE bucket A (deg_1(x) = deg_1(y) = 1).')
    print('  margin at Pi_x: ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(hist.items()))
          + '   -- ASSERTED <= 0 at EVERY row, with Pi_y and <M> too.')
    print('  (c_1, c_2) at Pi_x: ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(cc.items())))
    print('  margin at U = Lambda^2 K^4: ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(mallh.items())))
    print('  (c_1, c_2) at <M>: ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(mb.items()))
          + '   -- job 2\'s BOTH-sides shape stays EMPTY here.')
    for (sk, pr0, s1n, nv, ne, df) in shapes:
        print(f'  one exhibited graph, for the record: {sk}{pr0} + '
              f'`{s1n}`, |V| = {nv}, |E| = {ne}, def_3 = {df}.')
    print(f'  SHORTFALLS at the three 2-blocks: {shortfall}.  Rows whose cap '
          f'is <= 6 and that ATTAIN: {att}.  Rows with cap > 6, i.e.')
    print(f'  `a_1 + a_2 > max(0, 6 - d_1 - d_2)`, hence ARITHMETICALLY '
          f'unattainable at that configuration: {nonatt}, of which')
    print(f'  {allbreak} also break the `U = Lambda^2 K^4` inequality '
          f'outright.')
    print('  (delta_i + a_i - rho_i) per row -- (BE-86)\'s measured identity '
          '`rho_i = delta_i + a_i` needs')
    print('  the WELDED side at generic rank too, and the plant need not '
          'leave it there: ' + ', '.join(
              f'{k}: {v}' for k, v in sorted(welded.items())))
    print('  F13 NEGATIVE CONTROL -- the SAME graphs drawn FREELY:')
    for k, (rf, dsf, a1f, a2f, rch, cp, mf) in sorted(ctrl.items()):
        print(f'    {k[0]} + `{k[1]}`: rho_1 = {rf}, '
              f'dim(rho_bar_1 cap Sigma_x) = {dsf}, a = ({a1f},{a2f}), '
              f'reach = {rch}, cap = {cp}, margin(Lambda^2 K^4) = {mf}')
    assert got_rows >= 3 and shortfall == 0, 'the peel sweep did not reproduce'
    assert lowrho >= 1, \
        'no rho_1 <= 4 row in the regime-compatible bucket -- (BE-110)(iv) ' \
        'survives'
    assert ctrl and all(v[1] < 3 and v[2] == 0 and v[3] == 0
                        and v[4] == v[5] for v in ctrl.values()), \
        'the free control is itself bad or non-attaining -- the finding ' \
        'would be about the GRAPH, not the stratum'
    print('  VERDICT 1.  (BE-110)(iv)\'s hunt verdict -- "`dim = 3 with')
    print('  rho <= 4` NONE FOUND in the bucket a peel in the generic flag')
    print('  regime can present" -- is REFUTED by witness, at rho_1 = 4 with')
    print('  deg_1(x) = deg_1(y) = 1 and `flag_frame` non-None.  (BE-110)(ii)')
    print('  is a PATH theorem and is UNTOUCHED; what falls is the hunt.')
    print('  VERDICT 2, and it is priced DOWN, not up.  These rows are the')
    print('  first exhibited inhabitants of (BE-101)(iii)\'s live block --')
    print('  BDOUBLE\'s own named `a_1 + a_2 > max(0, 6 - d_1 - d_2)` breaker')
    print('  of `U = Lambda^2 K^4`.  They are NOT `Phase39.md` item 0(c)\'s')
    print('  Pi_x shortfall (margin at Pi_x is <= 0 at every row, ASSERTED),')
    print('  and they do NOT refute half (B) or (BE-14): the control shows')
    print('  the SAME graph drawn freely has a = (0,0) and ATTAINS, and')
    print('  (BE-14) is EXISTENTIAL ((BE-16)).  What they do is INHABIT the')
    print('  non-attaining case, which (BE-113)(i) item 3 carried as an')
    print('  unwitnessed scope caveat.')
    print(f'  peel: {time.time() - t0:.1f}s')
    return True


# ====================================================== mode: degx (BE-119)

def degx_library():
    """Sides with a terminal x of side-degree >= 2 -- (BE-113)'s price (d),
    unmeasured anywhere before this direction.  Both terminals are on the
    core, and the shape guard (degree->=3 vertices an independent set) is
    inherited from `sample_piece_config` verbatim, as BSIGMA's library is."""
    out = []
    for m in (6, 8, 10):
        for k in (2, 3, 4):
            if k >= m - 1:
                continue
            E = []
            _arc(E, 'x', 'y', k, 'p')
            _arc(E, 'x', 'y', m - k, 'q')
            out.append((f'cycle({m}) at distance {k}', E, 'x', 'y'))
    for (a, b, c) in ((3, 3, 3), (3, 3, 4), (3, 4, 4), (4, 4, 4), (3, 4, 5)):
        E = []
        for tag, L in (('u', a), ('v', b), ('w', c)):
            _arc(E, 'x', 'y', L, tag)
        out.append((f'theta({a},{b},{c})', E, 'x', 'y'))
    for k in (3, 4):
        E = list(subdivided(SKELETONS['K4'], [k] * 6))
        out.append((f'K4 subdivided x{k}', E, 'A', 'B'))
    return out


def _arc(E, a, b, L, tag):
    prev = a
    for i in range(L - 1):
        E.append((prev, f'{tag}{i}'))
        prev = f'{tag}{i}'
    E.append((prev, b))


def run_degx(ndraw=8, nplant=6):
    t0 = time.time()
    print(f'== degx: (BE-119) THE deg_i(x) >= 2 HALF, seed {SEED}')
    print('  (BE-113)\'s price (d): whether a deg_i(x) >= 2 shape can carry')
    print('  `Sigma_x <= rho_bar_i` below rho = 6 is NOT MEASURED ANYWHERE.')
    print('  Measured here, with the reduction\'s WEAK form as the theory:')
    print('  deleting all but one edge at x makes x pendant and only ADDS')
    print('  motions, so rho_bar_i <= <p_x ^ p_{c_1}> + A with the SAME')
    print('  core A = rho_bar(side - x; c_1, y) -- p_x-free.  Hence')
    print('  `Sigma_x <= rho_bar_i` still forces dim(A cap Sigma_x) >= 2,')
    print('  which (BE-115) makes PROPER whenever dim A <= 4.')
    lib = degx_library()
    tot, hits, incl, dAs, cens = 0, 0, 0, {}, {}
    hitnames = []
    for (name, E, x, y) in lib:
        nb = neighbors(E)
        assert len(nb[x]) >= 2, ('not a deg >= 2 terminal', name)
        c1 = sorted(nb[x], key=str)[0]
        side1 = [e for e in E if not (x in e and c1 in e)]
        core = core_of(E, x)
        rows = []
        for sd in range(ndraw):
            rng = random.Random(SEED + 8887 * sd + len(name))
            aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
            if aff is not None:
                rows.append(aff)
        for sd in range(nplant):
            rng = random.Random(SEED + 331 * sd + 3 * len(name))
            Ppi = span([v4(rng, 20) for _ in range(3)])
            if dim(Ppi) != 3:
                continue
            aff = plant_side(E, rng, Ppi, c1)
            if aff is not None:
                rows.append(aff)
        nh = 0
        for aff in rows:
            S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
            if not S:
                continue
            A, dA, _dM2, _r2 = rho_bar_of(core, aff, c1, y)
            px = hat(aff[x])
            l = wedge2(px, hat(aff[c1]))
            # the WEAK inclusion, asserted
            assert contains(span((A or []) + [l]), S), \
                ('the weak inclusion FAILS at deg_i(x) >= 2', name, rho, dA)
            incl += 1
            ds = dim(isect(S, sigma_at(px)))
            dAs[dA] = dAs.get(dA, 0) + 1
            cens[(rho, ds, dA)] = cens.get((rho, ds, dA), 0) + 1
            tot += 1
            if ds == 3 and rho <= 5:
                nh += 1
                hits += 1
                # and the forced consequence, asserted at every hit
                assert dim(isect(A, sigma_at(px))) >= 2, \
                    'a hit that does not force dim(A cap Sigma_x) >= 2'
        if nh:
            hitnames.append((name, nh, len(rows)))
    big = sum(v for k, v in dAs.items() if k >= 5)
    print(f'  {tot} rows over {len(lib)} deg_i(x) >= 2 topologies '
          f'(blind + planted); the weak inclusion ASSERTED at all {incl}.')
    print('  dim A census: ' + ', '.join(f'{k}: {v}' for k, v in sorted(dAs.items())))
    print(f'    dim A >= 5 (the residual, where (BE-115) gives nothing): '
          f'{big} of {tot} rows.')
    print('  (rho, dim(rho_bar cap Sigma_x), dim A): ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(cens.items())))
    print(f'  `Sigma_x <= rho_bar_i` with rho_i <= 5: {hits} rows'
          + (' -- ' + ', '.join(f'{nm} {h}/{n}' for (nm, h, n) in hitnames)
             if hitnames else ' -- NONE FOUND under this cap'))
    print(f'  VERDICT (F11).  price (d) is now MEASURED, not unmeasured: at')
    print(f'  a cap of {tot} rows over {len(lib)} topologies, every row has')
    print(f'  dim A <= 4 in {tot - big} cases, where (BE-119) makes the locus')
    print('  PROPER by the same two lemmas.  Never "does not exist".')
    assert incl == tot and tot >= 30, 'the degx sweep did not reproduce'
    print(f'  degx: {time.time() - t0:.1f}s')
    return True


# =================================================== mode: support (BE-120)

def run_support():
    t0 = time.time()
    print(f'== support: (BE-121) THE SAMPLER-SUPPORT AUDIT, seed {SEED}')
    print('  RESEARCH-ARC.md s4\'s 2026-09-02 sharpening, answered for EVERY')
    print('  population this driver runs.  The claim BPROPER makes has three')
    print('  variables: the SIDE (topology), the CONFIGURATION (points), and')
    print('  the FLAG.  Sigma_x = p_x ^ K^4 and rho_bar_i depend on the')
    print('  points alone, so THE FLAG IS NOT A VARIABLE of the reduction or')
    print('  of the incidence lemma -- it enters only through `flag_frame`\'s')
    print('  regime gate and the block Pi_x, i.e. only in `peel`.')
    LA, LB = side_library()
    lib = degx_library()
    print()
    print(f'  P1 `reduce` blind      : {len(LA)}+{len(LB)} side topologies '
          f'x 6 draws, coordinate ranges {{3,5,9}} (degeneracy-rich).')
    print('     varies: side, configuration.  holds fixed: nothing that the')
    print('     claim quantifies over -- and the identity is an ALGEBRAIC')
    print('     identity, so a draw can only falsify it, never confirm it.')
    print(f'  P2 `reduce`/`plant` planted: the SAME {len(LA)}+{len(LB)} '
          f'topologies x 8 planted draws.')
    print('     varies: side, and the configuration ONLY inside the (BE-109)')
    print('     stratum.  This is a deliberately NON-generic population --')
    print('     it exists to stand on the bad locus, not to sample the chart.')
    print('  P3 `alpha`             : 6 dimensions x 40 random subspaces x 12')
    print('     points per plane.  varies: dim A, A itself, the plane pi, and')
    print('     p inside pi.  holds fixed: NOTHING -- there is no graph here.')
    print('     The one variable it CANNOT vary is the field (exact Q only);')
    print('     the lemma\'s proof is characteristic-free but its numerical')
    print('     support is Q, disclosed.')
    print('  P4 `proper`            : the P2 rows, each with a 16-point sweep')
    print('     of p_x over `px_freedom`.  varies: p_x, with the CORE (hence')
    print('     A) held fixed ON PURPOSE -- that is the fibre the theorem is')
    print('     about.  holds fixed: the core, the plane pi, the flag.')
    print(f'  P5 `peel`              : {len(PEELJOBS)} constructed composites '
          f'x 3 seeds.')
    print('     varies: skeleton (K33/prism), non-adjacent hub pair, side-1')
    print('     piece, seed.  holds fixed: the branch profile (all 3s) and')
    print('     the fact that side 1 is PLANTED.  This is a CONSTRUCTED')
    print('     population, not a census -- every row is a hit row by')
    print('     construction, so "0 shortfalls" is about these rows only.')
    print(f'  P6 `degx`              : {len(lib)} deg_i(x) >= 2 topologies x '
          f'(8 blind + 6 planted).')
    print('     varies: side, configuration, and the stratum.  holds fixed:')
    print('     the choice of which edge at x is kept pendant (c_1, the')
    print('     lexicographic first) -- the inclusion holds for EVERY choice')
    print('     and only one is exercised, disclosed.')
    print()
    print('  THE ONE SUPPORT DEFECT THIS DIRECTION FOUND IN ITS PREDECESSOR,')
    print('  and it is the same shape as BSIGMA\'s own finding: (BE-109)(iv)\'s')
    print('  "5 of 16" is not a fact about the geometry at all -- it is the')
    print('  support of ONE planter, and the planter\'s hub-flag line is what')
    print('  bounded it.  An in-driver `assert` (BSIGMA asserted `lowA == 0`')
    print('  at 668 rows) is only as strong as the distribution it runs')
    print('  under, and here the distribution could not reach 11 of the 16')
    print('  topologies its own denominator counted.')
    print(f'  support: {time.time() - t0:.1f}s')
    return True


# ============================================================= entry point

def run_validate():
    print('== validate: a reduced run of all seven modes')
    run_reduce(ndraw=3, nplant=3, nmove=3)
    print()
    run_alpha(nsub=10, npt=6)
    print()
    run_proper(nplant=3, nsweep=10)
    print()
    run_plant(nplant=4)
    print()
    run_peel(nseed=1, jobs=PEELJOBS[:3])
    print()
    run_degx(ndraw=4, nplant=3)
    print()
    run_support()
    return True


MODES = {'reduce': run_reduce, 'alpha': run_alpha, 'proper': run_proper,
         'plant': run_plant, 'peel': run_peel, 'degx': run_degx,
         'support': run_support, 'validate': run_validate}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: bproper.py [{"|".join(MODES)}]')
        sys.exit(2)
    print(f'--- BPROPER / {mode} --- seed {SEED} --- exact Q ---')
    MODES[mode]()
