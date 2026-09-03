"""
Direction BOPEN (ordinal 72) -- CLOSE half (B)'s item 1 by making
(PENCIL-SATURATES-CHART) a THEOREM: discharge the passage from PROPER to
GENERIC for the saturation locus, plus the two inputs BPROPER's properness
proof left MEASURED.

  WHAT BPROPER LEFT ((BE-116)(iii), (BE-121)(i) item 1), in its own words:
    (a) the `p_x`-sweep is MEASURED, not proved;
    (b) (BE-69)'s openness is CITED for this locus, not re-derived, and
        `a_i = 0` generically is MEASURED;
  and the clause is stated at `Pi_x = p_x ^ pi_x`, while (BE-116) proves
  properness of the STRICTLY SMALLER locus `Sigma_x <= rho_bar_i`.

  THE ANSWER, said at the top, and it is FOUR results.

  (BE-122) (BE-69) READ AT SOURCE.  Its ambient IS `Chart(H)` -- the
           citation is not a category error -- but its LOCUS is
           `Good = A_1 cap A_2 cap GP`, an ATTAINMENT locus cut out by rank
           LOWER bounds, and its openness proof is exactly a lower-bound
           argument (semicontinuity of dim(rho_bar_1 + rho_bar_2)).  The
           saturation good locus is `{rho_i = 6} u {dim(rho_bar_i cap
           Pi_x) <= 1}`, an UPPER bound on an intersection dimension, which
           is upper-semicontinuous only on a constant-rank stratum.  So
           (BE-69)(i) DOES NOT TRANSPORT -- and it does not have to, because
           openness is not what "generic" needs.

  (BE-123) WHAT IT NEEDS INSTEAD IS CONSTRUCTIBILITY.  Bad is a finite union
           of locally closed rank strata, hence CONSTRUCTIBLE; on an
           IRREDUCIBLE variety a constructible set that contains no nonempty
           open is NOWHERE DENSE.  So `proper on the fibres of one dominating
           family` already gives `the complement contains a DENSE OPEN`.
           (BE-69) contributes exactly one thing: irreducibility -- which is
           (CH-1)(a), one level down, and which the PIECE inherits.

  (BE-124) THE `p_x`-SWEEP IS DISCHARGED BY THE TOWER.  In (CH-2)'s tower
           (= (BE-65)(ii)'s parametrization) hub points are stage 1 (FREE),
           hub normals stage 2, non-hub points stage 4 (on the hub planes).
           The ONLY constraints coupling `q_x` to the FIXED core are
           `q_x in pi_c` (when c is a hub) and `p_c in pi_x` (when it is
           not) -- so with side 2 rebuilt from scratch, `p_x` ranges over
           the PLANE pi_c, resp. over ALL of A^3.  Those are exactly the two
           ambients (BE-116) proves properness in.

  (BE-125) THE FLAG-ROTATION FIBRE COLLAPSES THE CHART CLAUSE ONTO
           (BE-116)'s LOCUS -- POINTWISE.  Rotating pi_x through the line
           p_x v p_c leaves rho_bar_i CONSTANT, and the union of the
           `p_x ^ pi` over that pencil is Sigma_x.  So a nonempty OPEN set of
           bad chart points is contained in `{Sigma_x <= rho_bar_i}`, at
           EVERY ONE of its points.  This is what makes (BE-116) the right
           locus after all -- and it is load-bearing: mode `weak` builds an
           `A` at which every point of a FIXED-flag p_x-plane is bad while
           Sigma_x is NOT inside rho_bar_i.

  (BE-126) `a_i = 0` GENERICALLY IS (BE-69)(i)'s OWN OPEN LOCUS `A_i`.
           `a_i = dim M_i - 6 - f_i` (`bunif.measure_row`, read at source)
           and (BE-22)(ii)'s partition cap gives `dim M_i >= 6 + f_i` at
           EVERY configuration, so `a_i >= 0` always and `{a_i = 0}` IS
           `A_i = {rank R_i maximal}` -- OPEN.  Nonempty is (BE-14) for the
           side, the 2-cut induction's own hypothesis ((BE-69)(iii)).  Open
           + nonempty + irreducible = DENSE.  PROVED, not measured.

  MODES.  hyp | weak | amax | fibre | slide | degx | price | support
          | validate  (the last runs all eight in one process)
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
from bimage import (contains, dim, isect, lam2, pencil_space,           # noqa: E402
                    plane_at, rho_bar_of, span, v4, pt_in)
from bpeel import SKELETONS, delta_pair, rnode_shaped                   # noqa: E402
from bdecor import (assemble, d3, draw_branch, flag_assignment,         # noqa: E402
                    girth, hcard_ok_piece, hubs_and_branches,
                    hub_adjacency, weld_d3)
from bunif import SEED, blocks_of, flag_frame                           # noqa: E402
from bsatur import margin_at, row_of, sigma_at                          # noqa: E402
from bsigma import side_library, sample_side_config                     # noqa: E402
from bproper import (PEELJOBS, composite, core_of, degx_library,        # noqa: E402
                     free_peel, plant_peel, plant_side, reduction_data,
                     side_named)
from kbare_common import verts_of, verify_pencil_witness               # noqa: E402

PIX, PIY, MB, ALLU = ('Pix',), ('Piy',), ('M',), tuple(
    sorted(('Pix', 'Piy', 'M', 'L')))
I4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]

# BPROPER's seven constructed composites, plus two PATH-side composites so
# that the OTHER fibre kind -- c a NON-hub, p_x free in all of A^3 -- is
# exercised too.  The path sides are (BE-110)(ii)'s own class; they are here
# for the FIBRE question, not for the hunt.
def _xy_path(L):
    """A path side x - t1 - ... - t(L-1) - y, in `composite`'s own
    'x'/'y' terminal convention (`side_library`'s paths are keyed v0/vL and
    would NOT be glued).  Here so the c-a-NON-hub fibre kind is exercised."""
    E, prev = [], 'x'
    for i in range(1, L):
        E.append((prev, f'pt{i}'))
        prev = f'pt{i}'
    E.append((prev, 'y'))
    return E


LOCAL_SIDES = {f'xy-path L={L}': _xy_path(L) for L in (4, 5)}

FIBREJOBS = list(PEELJOBS) + [
    ('K33', ('A', 'B'), 'xy-path L=4'),
    ('prism', ('A', 'E'), 'xy-path L=5'),
]


# ==================================================== the tower slide

def branch_side(br, side1set):
    """Which side a topological branch lives on.  (BE-70)(i): no branch
    crosses the 2-cut, so this is well defined -- asserted by the caller."""
    (z, zp, ints) = br
    path = [z] + list(ints) + [zp]
    es = {frozenset((path[i], path[i + 1])) for i in range(len(path) - 1)}
    if es <= side1set:
        return 1
    assert not (es & side1set), ('a branch CROSSES the 2-cut', br)
    return 2


def plane_through(p, q, rng, s=20, tries=40):
    """A plane (3-dim subspace basis) containing the two points p, q."""
    for _ in range(tries):
        bas = [p, q, v4(rng, s)]
        if rank(bas) == 3:
            return nullspace([nullspace(bas)[0]])
    return None


def slide(E, x, y, side1, W, branches, P, B, pts, newpx, newBx, rng,
          s=20, tries=60):
    """Rebuild the chart point with `x`'s flag replaced by (newpx, newBx),
    the WHOLE of side 1 held fixed -- points, hub flags and branch interiors
    -- and side 2 rebuilt from scratch by (CH-2)'s tower.

    This is the honest form of BPROPER's `p_x`-sweep: side 2 is not
    perturbed but RE-DRAWN, which is what the tower's stage order licenses.
    """
    side1set = {frozenset(e) for e in side1}
    V1 = {w for e in side1 for w in e}
    fixed = {z: (P[z], B[z]) for z in W if z in V1 and z not in (x,)}
    fixed[x] = (newpx, newBx)
    for _ in range(tries):
        P2, B2 = flag_assignment(W, branches, rng, s=s, fixed=fixed)
        if P2 is None:
            continue
        pts2, ok = dict(P2), True
        for br in branches:
            (z, zp, ints) = br
            if not ints:
                continue
            if branch_side(br, side1set) == 1:
                for w in ints:
                    pts2[w] = pts[w]
                continue
            g = draw_branch(P2, B2, z, zp, len(ints), rng, s=s)
            if g is None:
                ok = False
                break
            for w, cc in zip(ints, g):
                pts2[w] = cc
        if not ok:
            continue
        aff2 = assemble(E, pts2)
        if aff2 is None:
            continue
        return P2, B2, pts2, aff2
    return None


def bad_plane(px, V):
    """(BE-105)(i)'s q^{-1}(rho_bar cap Sigma_x): the set of t with
    p_x ^ t in V.  At dim V = 2 it is a 3-space, i.e. THE unique bad plane
    of the legal pencil -- CONSTRUCTED, because no sampler reaches it
    ((BE-105)(iii))."""
    if not V:
        return None
    fs = nullspace(V)                       # functionals vanishing on V
    rows = []
    for f in fs:
        rows.append([sum(a * b for a, b in zip(f, wedge2(px, e)))
                     for e in I4])
    ker = nullspace(rows) if rows else [r[:] for r in I4]
    return ker


def fibre_of(E, aff, x, c):
    """The `p_x` fibre with the CORE fixed, computed from the TOWER and not
    from a sampler: `pi_c` when c is a HUB of the piece (stage 2 at c is
    `q_x in pi_c`), all of K^4 when it is not (c is then a stage-4 point and
    its only constraint, `q_c in pi_x`, is met by choosing pi_x through
    p_x v p_c).  Returns (basis, c_is_hub)."""
    nb = neighbors(E)
    if len(nb[c]) >= 3:
        pic = plane_at(E, aff, c)
        assert pic is not None, 'no closed-star plane at the hub c'
        return pic, True
    return I4, False


def peel_of_job(skname, xy, s1name, prof=None):
    """(E, E1, E2, x, y, E1template) for one PEELJOBS entry.  The TEMPLATE
    is what `plant_peel`/`free_peel` want (they call `composite` themselves);
    `E1` is the renamed copy inside `E`."""
    if s1name in LOCAL_SIDES:
        E1t = LOCAL_SIDES[s1name]
    else:
        E1t, _xt, _yt = side_named(s1name)
    pr = prof or [3] * len(SKELETONS[skname])
    E, E1, E2, x, y = composite(skname, pr, xy, E1t)
    return E, E1, E2, x, y, E1t


def sides_of(E, E1, x, y):
    dp = delta_pair(E, x, y)
    if dp is None:
        return None
    _d1, _d2, Ea, Eb = dp
    side1 = Ea if len(Ea) == len(E1) else Eb
    side2 = Eb if side1 is Ea else Ea
    if len(side1) != len(E1):
        return None
    return side1, side2


def chart_data(E, aff, W):
    """(P, B, pts) read off a configuration: hub points, hub flag planes
    (`plane_at`, the plane through the closed star) and all points, all
    homogeneous.  The flags are DETERMINED by the configuration, so this is
    a read, not a choice."""
    P, B = {}, {}
    for z in W:
        P[z] = hat(aff[z])
        pz = plane_at(E, aff, z)
        if pz is None:
            return None
        B[z] = pz
    pts = {w: hat(v) for w, v in aff.items()}
    return P, B, pts


def core_pts(side1, x, aff):
    return {w: aff[w] for w in verts_of(side1) if w != x}


# ============================================== mode: fibre  ((BE-124))

def run_fibre(nseed=2, ntarget=6):
    t0 = time.time()
    print(f'== fibre: (BE-124) THE `p_x`-SWEEP, DISCHARGED BY THE TOWER, '
          f'seed {SEED}')
    print('  BPROPER swept `p_x` over its CLAIMED freedom with the core')
    print('  fixed and could not check that a swept point is a CHART point')
    print('  at all (`bproper.run_proper` draws SIDES, never a piece).  Here')
    print('  every target is REBUILT into a full legal chart point of the')
    print('  piece: side 1 -- points, hub flags and branch interiors -- held')
    print('  BYTE-FIXED, side 2 re-drawn from scratch by (CH-2)\'s tower.')
    print('  Asserted at every realized target: both gates; the core')
    print('  UNCHANGED; `A` unchanged AS A SUBSPACE; and (BE-114)(i)\'s')
    print('  identity rho_bar_1 = <p_x ^ p_c> + A at the NEW p_x.')
    tot, real, rows, hubs, nonhubs = 0, 0, 0, 0, 0
    for (skname, xy, s1name) in FIBREJOBS:
        E, E1, E2, x, y, E1t = peel_of_job(skname, xy, s1name)
        ss = sides_of(E, E1, x, y)
        if ss is None:
            continue
        side1, side2 = ss
        nb1 = neighbors(side1)
        c = sorted(nb1[x], key=str)[0]
        W, branches = hubs_and_branches(E, x, y)
        pr = [3] * len(SKELETONS[skname])
        for sd in range(nseed):
            rng = random.Random(SEED + 613 * sd + 7 * len(s1name))
            g = free_peel(skname, pr, xy, E1t, rng)
            if g is None:
                continue
            aff = g[5]
            cd = chart_data(E, aff, W)
            if cd is None:
                continue
            P, B, pts = cd
            rows += 1
            A0, dA0, l0, S0, r0, c0 = reduction_data(side1, aff, x, y)
            assert c0 == c, 'the side neighbour of x moved'
            assert dim(span(A0 + [l0])) == r0, \
                '(BE-114)(i) fails at the base point'
            fib, chub = fibre_of(E, aff, x, c)
            hubs += int(chub)
            nonhubs += int(not chub)
            core0 = core_pts(side1, x, aff)
            for k in range(ntarget):
                r2 = random.Random(SEED + 9901 * sd + 31 * k + len(s1name))
                npx = pt_in(fib, r2, 20)
                if npx[3] == 0 or rank([npx, hat(aff[c])]) != 2:
                    continue
                nBx = plane_through(npx, hat(aff[c]), r2)
                if nBx is None:
                    continue
                tot += 1
                got = slide(E, x, y, side1, W, branches, P, B, pts,
                            npx, nBx, r2)
                if got is None:
                    continue
                _P2, _B2, _pts2, aff2 = got
                real += 1
                ok, _n = verify_pencil_witness(E, aff2)
                assert ok, 'the rebuilt point fails the pencil witness'
                assert core_pts(side1, x, aff2) == core0, \
                    'the CORE moved under the slide'
                A1, dA1, l1, S1, r1, _c1 = reduction_data(side1, aff2, x, y)
                assert dA1 == dA0 and dim(isect(A0, A1)) == dA0, \
                    '`A` is not the same SUBSPACE after the slide'
                assert dim(span(A1 + [l1])) == r1, \
                    '(BE-114)(i) fails at the slid point'
                assert contains(S1, [l1]), 'l is not in rho_bar_1'
    print(f'  peels {rows}, targets attempted {tot}, REALIZED {real}')
    print(f'  fibre kind: pi_c (c a HUB) at {hubs} rows, all of A^3 at '
          f'{nonhubs}')
    assert rows > 0 and real > 0, 'no slide realized'
    assert real == tot, (
        'a target failed to realize -- the tower construction is incomplete',
        real, tot)
    print('  ASSERTED: every attempted target realized as a legal chart')
    print('  point, with the core fixed and `A` the same subspace.')
    print(f'  [{time.time() - t0:.1f}s]')
    return real, tot


# ============================================== mode: slide  ((BE-125))

def run_slide(nseed=2, npencil=10):
    t0 = time.time()
    print(f'== slide: (BE-125) THE FLAG-ROTATION FIBRE, seed {SEED}')
    print('  Rotate pi_x through the LINE p_x v p_c, side 1 held fixed and')
    print('  side 2 rebuilt.  rho_bar_1 is CONSTANT along the rotation, and')
    print('  the union of the `p_x ^ pi` over the pencil is Sigma_x, so')
    print('    bad at EVERY pi  <=>  Sigma_x <= rho_bar_1,')
    print('  which is exactly (BE-116)\'s locus.  Both halves are asserted,')
    print('  on FREE rows (Sigma_x NOT inside: at most ONE bad plane) and on')
    print('  PLANTED rows (Sigma_x inside: EVERY plane bad).')
    good, bad, badplanes, dhist, built = 0, 0, {}, {}, 0
    for (skname, xy, s1name) in FIBREJOBS:
        E, E1, E2, x, y, E1t = peel_of_job(skname, xy, s1name)
        ss = sides_of(E, E1, x, y)
        if ss is None:
            continue
        side1, side2 = ss
        nb1 = neighbors(side1)
        c = sorted(nb1[x], key=str)[0]
        W, branches = hubs_and_branches(E, x, y)
        pr = [3] * len(SKELETONS[skname])
        for planted in (False, True):
            for sd in range(nseed):
                rng = random.Random(SEED + 613 * sd + 7 * len(s1name))
                if planted:
                    g = plant_peel(skname, pr, xy, E1t, rng)
                    aff = None if g is None else g[5]
                else:
                    g = free_peel(skname, pr, xy, E1t, rng)
                    aff = None if g is None else g[5]
                if aff is None:
                    continue
                cd = chart_data(E, aff, W)
                if cd is None:
                    continue
                P, B, pts = cd
                S1, r1, _dM, _r = rho_bar_of(side1, aff, x, y)
                px, pc = hat(aff[x]), hat(aff[c])
                sat = contains(S1, sigma_at(px))
                nbad, ntried = 0, 0
                for k in range(npencil):
                    r2 = random.Random(SEED + 7717 * sd + 41 * k
                                       + len(s1name) + 5 * int(planted))
                    nBx = plane_through(px, pc, r2)
                    if nBx is None:
                        continue
                    got = slide(E, x, y, side1, W, branches, P, B, pts,
                                px, nBx, r2)
                    if got is None:
                        continue
                    _P2, _B2, _pts2, aff2 = got
                    S2, r2d, _d2, _r2 = rho_bar_of(side1, aff2, x, y)
                    assert r2d == r1 and dim(isect(S1, S2)) == r1, \
                        'rho_bar_1 MOVED under a pure flag rotation'
                    assert hat(aff2[x]) == px, 'p_x moved under the rotation'
                    ntried += 1
                    if contains(S2, pencil_space(px, nBx)):
                        nbad += 1
                if ntried == 0:
                    continue
                if sat:
                    bad += 1
                    assert nbad == ntried, \
                        ('Sigma_x <= rho_bar_1 but a legal plane is GOOD',
                         nbad, ntried)
                else:
                    good += 1
                    assert nbad <= 1, \
                        ('Sigma_x NOT inside rho_bar_1 but TWO legal planes '
                         'are bad -- (BE-105)(i) fails', nbad, ntried)
                    badplanes[nbad] = badplanes.get(nbad, 0) + 1
                    dsig = dim(isect(S1, sigma_at(px)))
                    dhist[dsig] = dhist.get(dsig, 0) + 1
                    if dsig == 2:
                        bp = bad_plane(px, isect(S1, sigma_at(px)))
                        if bp is not None and dim(bp) == 3 \
                                and rank(bp + [px]) == 3:
                            built += 1
                            assert contains(
                                S1, pencil_space(px, bp)), \
                                'the CONSTRUCTED bad plane is not bad'
                            assert rank(bp + [pc]) == 3, \
                                'the constructed plane misses p_c, so it is '\
                                'not in the LEGAL pencil'
    print(f'  rows with Sigma_x <= rho_bar_1 (planted): {bad} -- EVERY '
          f'rotated plane bad at all of them')
    print(f'  rows with Sigma_x NOT inside: {good}; SAMPLED bad-plane '
          f'histogram {dict(sorted(badplanes.items()))}')
    print(f'  dim(rho_bar_1 cap Sigma_x) on those rows: '
          f'{dict(sorted(dhist.items()))}; CONSTRUCTED bad planes asserted '
          f'bad at {built} of them')
    print('  (a sampled rotation NEVER meets the bad plane -- it is one')
    print('   member of a 1-parameter pencil, (BE-105)(iii).  That is why')
    print('   the middle case is CONSTRUCTED, not sampled.)')
    assert bad > 0 and good > 0, 'one of the two halves was never exercised'
    print('  ASSERTED both halves, so the CHART clause\'s bad locus and')
    print('  (BE-116)\'s locus agree on any open set -- POINTWISE.')
    print(f'  [{time.time() - t0:.1f}s]')
    return good, bad


# ============================================== mode: weak  ((BE-125) control)

def run_weak():
    t0 = time.time()
    print(f'== weak: (BE-125) IS LOAD-BEARING -- the CONSTRUCTED control, '
          f'seed {SEED}')
    print('  If pi_x is held FIXED and only p_x moves, the bad locus can be')
    print('  DENSE in the plane while Sigma_x is NOWHERE inside rho_bar_i.')
    print('    pi = <e1,e2,e3>,  A = <e1^e3, e2^e3, e3^e4>,  p_c = e1.')
    print('  A cap Lambda^2 pi is the PENCIL z ^ pi at z = e3, so for p in pi')
    print('    Pi_p cap (<l> + A) = <l> + (Pi_p cap A)  and  Pi_p cap A =')
    print('    <p ^ z>,  which is <l> exactly when z lies on p v p_c.')
    print('  Hence BAD <=> z is OFF the line p v p_c (or p = z, where')
    print('  Pi_p = A cap Lambda^2 pi outright): the complement of ONE line')
    print('  of pi, so bad on a nonempty OPEN set.  Asserted as an IFF')
    print('  below, not as a rate.')
    e = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
    e1, e2, e3, e4 = e
    pi = [e1, e2, e3]
    A = span([wedge2(e1, e3), wedge2(e2, e3), wedge2(e3, e4)])
    z, pc = e3, e1
    assert dim(A) == 3, 'the constructed A is not 3-dimensional'
    assert dim(isect(A, lam2(pi))) == 2, \
        'A cap Lambda^2 pi is not the pencil z ^ pi'
    assert dim(isect(A, pencil_space(z, pi))) == 2, \
        'A cap Lambda^2 pi is not EXACTLY z ^ pi'
    nbad, nsat, npts, noff = 0, 0, 0, 0
    for s in range(-4, 5):
        for t in range(-4, 5):
            for u in (0, 1):
                p = [F(u), F(s), F(t), F(0)] if u else [F(0), F(s), F(t), F(0)]
                if rank([p]) == 0 or rank([p, pc]) != 2:
                    continue
                npts += 1
                l = wedge2(p, pc)
                rho = span(A + [l])
                assert dim(rho) <= 5, 'the constructed rho_bar exceeds 5'
                bad = contains(rho, pencil_space(p, pi))
                # GOOD  <=>  z lies on the line p v p_c  AND  p != z
                off = not (rank([p, pc, z]) == 2 and rank([p, z]) == 2)
                assert bad == off, \
                    ('BAD is not equivalent to `z off p v p_c, or p = z`',
                     s, t, u, bad, off)
                nbad += int(bad)
                noff += int(off)
                if contains(rho, sigma_at(p)):
                    nsat += 1
                    assert rank([p, z]) == 1, \
                        ('Sigma_p <= rho_bar away from p = z', s, t, u)
    print(f'  points swept in pi: {npts}; BAD {nbad} (= the geometric '
          f'criterion: {noff}); Sigma_x <= rho_bar at {nsat}')
    assert npts > 0 and nbad > 0, 'the control never fired'
    assert nbad == noff, 'the IFF failed in aggregate'
    assert nsat > 0, 'the Sigma_x locus was never exercised'
    print('  ASSERTED, and the two loci differ MAXIMALLY on one fibre:')
    print('  (BE-116)\'s locus `Sigma_p <= rho_bar` is EXACTLY the single')
    print('  point p = z (asserted at every one of its hits), while the')
    print('  CHART clause\'s locus `Pi_p <= rho_bar` is the complement of')
    print('  ONE LINE -- proper vs DENSE in the same plane.  So (BE-116)')
    print('  does NOT by itself give the CHART clause: the flag rotation')
    print('  (BE-125) is what does.')
    print(f'  [{time.time() - t0:.1f}s]')
    return npts


# ============================================== mode: amax  ((BE-126))

def run_amax(ndraw=5):
    t0 = time.time()
    print(f'== amax: (BE-126) `a_i = 0` GENERICALLY IS (BE-69)(i)\'s A_i, '
          f'seed {SEED}')
    print('  a_i := dim M_i - 6 - f_i (`bunif.measure_row`, read at source),')
    print('  and (BE-22)(ii)\'s partition cap is dim M_i >= 6 + f_i at EVERY')
    print('  configuration -- so a_i >= 0 always and {a_i = 0} IS the locus')
    print('  A_i = {rank R_i maximal} that (BE-69)(i) proves OPEN.  Asserted')
    print('  below: a_i >= 0 at every draw, and the FIRST draw attains the')
    print('  minimum over all draws -- (BE-69)(iii)\'s own openness')
    print('  signature, here for a_i rather than for reach.')
    LA, LB = side_library()
    rowsn, firstmin, zero, hist = 0, 0, 0, {}
    for (name, E, x, y) in LA + LB:
        vals = []
        for sd in range(ndraw):
            rng = random.Random(SEED + 1777 * sd + 3 * len(name))
            aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
            if aff is None:
                continue
            _S, _r, dM, _rk = rho_bar_of(E, aff, x, y)
            f = d3(E)
            a = dM - 6 - f
            assert a >= 0, ('a_i < 0 -- the partition cap FAILS', name, a)
            vals.append(a)
        if not vals:
            continue
        rowsn += 1
        hist[min(vals)] = hist.get(min(vals), 0) + 1
        if vals[0] == min(vals):
            firstmin += 1
        if min(vals) == 0:
            zero += 1
    print(f'  sides measured {rowsn}; generic a_i histogram '
          f'{dict(sorted(hist.items()))}')
    print(f'  first draw attains the minimum at {firstmin}/{rowsn}; '
          f'a_i = 0 generically at {zero}/{rowsn}')
    assert rowsn > 0, 'no side measured'
    assert firstmin == rowsn, \
        'a draw BELOW the first draw exists -- the openness signature fails'
    print('  ASSERTED.  Note the arithmetic is a DEFINITION plus the cap:')
    print('  no genericity is measured here, it is PROVED from (BE-69)(i)')
    print('  plus irreducibility, with A_i != 0 the induction\'s own (BE-14).')
    print(f'  [{time.time() - t0:.1f}s]')
    return rowsn, firstmin


# ============================================== mode: hyp  ((BE-123))

def run_hyp():
    t0 = time.time()
    print(f'== hyp: (BE-123) (CH-1) AT THE PIECE, and the d_x census, '
          f'seed {SEED}')
    print('  (CH-1)(a) needs `hcard`, min degree 2 and girth >= 4 AT THE')
    print('  PIECE.  All three are inherited by any subgraph whose terminals')
    print('  keep degree >= 3: degrees only DROP, so a hub of H is a hub of')
    print('  G and N_H(h) <= N_G(h), whence d_h(H) <= d_h(G) <= 2.  Checked')
    print('  here at every constructed peel -- BPROPER\'s escape item 2.')
    print(f"  {'peel':52s} {'hcard':>5} {'mindeg':>6} {'girth':>5} "
          f"{'c hub':>6} {'dx2':>4}")
    n, chub, dx2 = 0, 0, 0
    for (skname, xy, s1name) in FIBREJOBS:
        E, E1, E2, x, y, E1t = peel_of_job(skname, xy, s1name)
        ss = sides_of(E, E1, x, y)
        if ss is None:
            continue
        side1, side2 = ss
        nb = neighbors(E)
        c = sorted(neighbors(side1)[x], key=str)[0]
        okh, W, br, ha = hcard_ok_piece(E, x, y)
        md = min(len(nb[w]) for w in verts_of(E))
        g = girth(E)
        ish = len(nb[c]) >= 3
        h2 = len([w for w in nb[x] if len(nb[w]) >= 3 and w != c])
        n += 1
        chub += int(ish)
        dx2 += int(h2 > 0)
        assert okh, ('hcard FAILS at the piece', skname, s1name)
        assert md >= 2, ('min degree < 2 at the piece', skname, s1name)
        assert g >= 4, ('girth < 4 at the piece', skname, s1name)
        assert len(nb[x]) >= 3 and len(nb[y]) >= 3, \
            'a terminal is not a hub of the piece -- (BE-70)(i) fails'
        nm = f'{skname} + {s1name}'
        print(f'  {nm:52s} {str(okh):>5} {md:>6} {g:>5} '
              f'{str(ish):>6} {h2:>4}')
    print(f'  peels {n}; c a HUB at {chub}; x with a side-2 hub neighbour '
          f'at {dx2}')
    assert n > 0, 'no peel checked'
    print('  ASSERTED (CH-1)\'s three hypotheses at every one, so')
    print('  `Chart(H)` is irreducible there -- BPROPER escape item 2 CLOSED.')
    print(f'  [{time.time() - t0:.1f}s]')
    return n, chub, dx2


# ============================================== mode: price

def run_price(nseed=3):
    t0 = time.time()
    print(f'== price: THE SHORTFALL CONTROL on every exhibited row, '
          f'seed {SEED}')
    print('  `margin <= 0` at Pi_x, Pi_y and <M> is ASSERTED at every row')
    print('  this direction exhibits -- planted and free -- and')
    print('  `reach = min(d1+d2,6) + a1 + a2` at every FREE row.  A')
    print('  `margin > 0` row at Pi_x would be Phase39 item 0(c), the arc\'s')
    print('  first shortfall, and OUTRANKS this direction\'s target.')
    npl, nfr, sh = 0, 0, 0
    mh = {}
    for (skname, xy, s1name) in FIBREJOBS:
        E, E1, E2, x, y, E1t = peel_of_job(skname, xy, s1name)
        ss = sides_of(E, E1, x, y)
        if ss is None:
            continue
        side1, side2 = ss
        pr = [3] * len(SKELETONS[skname])
        for sd in range(nseed):
            for planted in (True, False):
                rng = random.Random(SEED + 613 * sd + 7 * len(s1name))
                if planted:
                    g = plant_peel(skname, pr, xy, E1t, rng)
                    aff = None if g is None else g[5]
                else:
                    g = free_peel(skname, pr, xy, E1t, rng)
                    aff = None if g is None else g[5]
                if aff is None:
                    continue
                row = row_of(E, x, y, side1, side2, aff)
                if row is None:
                    continue
                for blk, du in ((PIX, 2), (PIY, 2), (MB, 1)):
                    m = margin_at(row, blk, du)
                    if m > 0:
                        sh += 1
                    assert m <= 0, \
                        ('SHORTFALL: margin > 0 -- Phase39 item 0(c)',
                         skname, s1name, blk, m)
                m = margin_at(row, PIX, 2)
                mh[m] = mh.get(m, 0) + 1
                if planted:
                    npl += 1
                else:
                    nfr += 1
                    assert row['reach'] == min(row['d1'] + row['d2'], 6) \
                        + row['a1'] + row['a2'], \
                        ('a FREE row does not attain', skname, s1name)
    print(f'  rows: planted {npl}, free {nfr}; shortfalls {sh}')
    print(f'  margin histogram at Pi_x: {dict(sorted(mh.items()))}')
    assert npl + nfr > 0, 'no row measured'
    assert sh == 0, 'a shortfall was exhibited -- report it as the HEADLINE'
    print(f'  [{time.time() - t0:.1f}s]')
    return npl, nfr



# ============================================== mode: degx  ((BE-127))

def sat_locus(A):
    """{t in K^4 : Sigma_t <= A}, computed EXACTLY -- it is LINEAR in t,
    because f(t ^ e_j) = sum_k t_k f(e_k ^ e_j) for every functional f
    vanishing on A.  Returns a basis (possibly empty)."""
    fs = nullspace(A) if A else []
    if not fs:
        return [r[:] for r in I4]           # A = Lambda^2 K^4: every t
    rows = []
    for f in fs:
        for j in range(4):
            rows.append([sum(a * b for a, b in
                             zip(f, wedge2(I4[k], I4[j]))) for k in range(4)])
    return nullspace(rows)


def star_finite(A, Lc, rng, ntry=8):
    """Certify that {t in Lc : dim(A cap Sigma_t) >= 2} is FINITE, by
    exhibiting ONE t on the line with dim <= 1.  The set is Zariski-closed
    in the line, so one point outside it proves it proper, hence finite.
    Exact, not a rate."""
    for _ in range(ntry):
        t = pt_in(Lc, rng, 20)
        if rank([t]) == 0:
            continue
        if dim(isect(A, sigma_at(t))) <= 1:
            return t
    return None


def run_degx(ndraw=8, nplant=6):
    t0 = time.time()
    print(f'== degx: (BE-127) THE deg_i(x) >= 2 HALF -- price (d), '
          f'SHARPENED, seed {SEED}')
    print('  At deg_i(x) >= 2 with side neighbours c_1, c_2, (BE-105)(iv)')
    print('  gives Pi_x = <l_1, l_2> and (BE-114)(iv) gives')
    print('  rho_bar_i <= <l_1> + A, so the CHART clause\'s bad condition')
    print('  Pi_x <= rho_bar_i forces  p_x ^ t in A  for some t on the FIXED')
    print('  LINE L_c = p_{c_1} v p_{c_2}.  The incidence J = {(p,t)} then')
    print('  has dim <= max(1 + 1, 0 + 2) = 2 < 3 -- PROPER in p_x -- under')
    print('    (*)  Sigma_t is NOT inside A for any t in L_c, AND')
    print('         {t in L_c : dim(A cap Sigma_t) >= 2} is FINITE.')
    print('  Both halves of (*) are certified EXACTLY below: the first is a')
    print('  LINEAR condition on t, the second by one witness t on the line')
    print('  (the set is Zariski-closed in L_c, so one point outside it')
    print('  proves it proper).  This is stronger than (BE-119)(i), which')
    print('  needed dim A <= 4 and reached only the Sigma_x locus.')
    lib = degx_library()
    tot, ok1, ok2, red, hubs, dAs, bads = 0, 0, 0, 0, 0, {}, 0
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
            Ppi = span([v4(rng, 20) for _ in range(3)])
            if dim(Ppi) != 3:
                continue
            aff = plant_side(E, rng, Ppi, c1)
            if aff is not None:
                rows.append(aff)
        for ri, aff in enumerate(rows):
            S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
            if not S:
                continue
            A, dA, _d2, _r2 = rho_bar_of(core, aff, c1, y)
            px, pc1, pc2 = (hat(aff[x]), hat(aff[c1]), hat(aff[c2]))
            pix = plane_at(E, aff, x)
            if pix is None:
                continue
            tot += 1
            dAs[dA] = dAs.get(dA, 0) + 1
            hubs += len([w for w in nb[x] if len(nb[w]) >= 3])
            l1, l2 = wedge2(px, pc1), wedge2(px, pc2)
            # (BE-105)(iv), re-asserted at THIS population
            assert dim(span([l1, l2])) == 2 and \
                dim(isect(span([l1, l2]), pencil_space(px, pix))) == 2, \
                ('Pi_x is not <l_1, l_2> at a deg >= 2 terminal', name)
            Lc = span([pc1, pc2])
            assert dim(Lc) == 2, 'the two side neighbours coincide'
            # (*) half one: Sigma_t <= A nowhere on L_c -- EXACT, linear
            sat = sat_locus(A)
            if not sat or dim(isect(span(sat), Lc)) == 0:
                ok1 += 1
            else:
                continue
            # (*) half two: one t on L_c with dim(A cap Sigma_t) <= 1
            rng2 = random.Random(SEED + 77 * ri + len(name))
            if star_finite(A, Lc, rng2) is not None:
                ok2 += 1
            # the REDUCTION, asserted whenever the row is bad
            if contains(S, pencil_space(px, pix)) and rho <= 5:
                bads += 1
                found = None
                for k in range(12):
                    r3 = random.Random(SEED + 13 * k + ri)
                    t = pt_in(Lc, r3, 20)
                    if A and contains(A, [wedge2(px, t)]):
                        found = t
                        break
                if found is None:
                    # the forced t is p_{c_2} - lam p_{c_1}; solve for lam
                    for lam in range(-9, 10):
                        t = [pc2[i] - F(lam) * pc1[i] for i in range(4)]
                        if rank([t]) and A and contains(A, [wedge2(px, t)]):
                            found = t
                            break
                assert found is not None, \
                    ('a BAD row with no t on L_c -- the reduction FAILS',
                     name)
                red += 1
    print(f'  {tot} rows over {len(lib)} deg_i(x) >= 2 topologies '
          f'(blind + planted); hub side-neighbours of x: {hubs}')
    print('  dim A census: ' + ', '.join(f'{k}: {v}'
                                         for k, v in sorted(dAs.items())))
    print(f"  (*) half one (Sigma_t not inside A on L_c) certified EXACTLY "
          f"at {ok1}/{tot}")
    print(f'  (*) half two (the >= 2 set finite on L_c) certified at '
          f'{ok2}/{ok1}')
    print(f'  bad rows (Pi_x <= rho_bar_i, rho_i <= 5): {bads}; the '
          f'reduction asserted at {red} of them')
    if bads == 0:
        print('  DISCLOSED (F13): the reduction assert NEVER FIRED here --')
        print('  this population carries no bad row at all, reproducing')
        print('  (BE-119)(ii)\'s `none found under that cap`.  The reduction')
        print('  is PROVED ((BE-127)(i)); what is measured is only (*).')
    assert tot >= 30, 'the degx sweep did not reproduce'
    assert ok1 == tot and ok2 == ok1, \
        '(*) failed somewhere -- report the row, it is the named residual'
    print('  VERDICT.  (*) holds at every row of this population, so there')
    print('  the CHART clause\'s bad locus is PROPER at deg_i(x) >= 2 too.')
    print(f'  CAP: a constructed {len(lib)}-topology library, not a census;')
    print('  (*) is a CONDITION, certified here, never proved in general.')
    print(f'  [{time.time() - t0:.1f}s]')
    return tot, ok1


# ============================================== mode: support

def run_support():
    print('== support: the RESEARCH-ARC.md s4 SAMPLER-SUPPORT AUDIT')
    print('  For each population: what it VARIES, what it HOLDS FIXED, and')
    print('  which of the claim\'s own quantifiers it therefore reaches.')
    print()
    print('  (1) `fibre` -- BPROPER\'s 7 constructed composites (K33/prism +')
    print('      a bucket-A side) PLUS 2 xy-path composites, so that BOTH')
    print('      fibre kinds occur; 2 free draws each, 6 targets per draw.')
    print('      VARIES: p_x over its tower fibre, and ALL of side 2.')
    print('      FIXED: side 1 (points, hub flags, branch interiors), the')
    print('      skeleton profile [3]*|E(sk)|, the pair (x,y).')
    print('      REACHES: the sweep-realizability quantifier ONLY -- it says')
    print('      nothing about whether a target is GOOD.  Properness is')
    print('      (BE-115), which is proved, not sampled.')
    print()
    print('  (2) `slide` -- the same composites, PLANTED and FREE.')
    print('      VARIES: pi_x over the pencil through p_x v p_c; side 2.')
    print('      FIXED: p_x, the entire side 1, hence rho_bar_1 (ASSERTED')
    print('      constant, so the population cannot smuggle in a')
    print('      configuration change).')
    print('      REACHES: the FLAG quantifier at x, at a fixed configuration')
    print('      -- exactly the variable BSATUR\'s samplers never ranged')
    print('      over ((BE-105)(iii)) and BSIGMA\'s cap was about.')
    print()
    print('  (3) `weak` -- CONSTRUCTED, not sampled: one A, one plane, a')
    print('      160-point grid of p in pi.  VARIES p only; A and pi fixed by')
    print('      hand.  REACHES: the existence of the shape.  It is a')
    print('      control on an ARGUMENT, and a constructed control cannot')
    print('      be a lucky seed.')
    print()
    print('  (4) `amax` -- BSIGMA\'s 29-topology side library, 5 blind draws')
    print('      per side, coordinate range 9.  VARIES: the configuration of')
    print('      ONE side.  FIXED: the topology, and the OTHER side does not')
    print('      exist (these are side draws).  REACHES: a_i at a generic')
    print('      configuration of a side -- NOT a_i on Chart(H), which is')
    print('      what (BE-126) PROVES rather than measures.  Disclosed')
    print('      because the two are one quantifier apart.')
    print()
    print('  (5) `hyp` -- the 9 composites, no randomness at all: a')
    print('      COMBINATORIAL check of (CH-1)\'s three hypotheses and of')
    print('      the d_x census.  REACHES: those 9 shapes.  The INHERITANCE')
    print('      argument in (BE-123) is what covers the class; this only')
    print('      exhibits that the hypotheses are not vacuously satisfied.')
    print()
    print('  (6) `degx` -- BPROPER\'s OWN 16-topology deg_i(x) >= 2 library,')
    print('      its own seeds: 91 rows, reproducing (BE-119)(ii) exactly.')
    print('      VARIES: the configuration of one side.  FIXED: the')
    print('      topology; and `x` has NO hub side-neighbour at ANY row')
    print('      (measured 0), so the p_x fibre there is all of A^3 -- a')
    print('      fact about the library, disclosed, not about the class.')
    print('      REACHES: the condition (*) at a generic configuration.  It')
    print('      does NOT reach the BAD rows, of which there are none here')
    print('      -- the reduction is proved, not sampled.')
    print()
    print('  (7) `price` -- the same composites, 3 seeds, planted AND free.')
    print('      VARIES: the configuration. FIXED: the profile [3]*, the')
    print('      pair (x,y), the side library entry.  REACHES: the shortfall')
    print('      question on THOSE rows only -- "0 shortfalls" is a')
    print('      statement about this constructed population, never a census.')
    print()
    print('  THE CAP, stated once and travelling with every figure above:')
    print('  every population here is CONSTRUCTED (9 composites, 29 library')
    print('  sides), never a habitat census; every "N of N" is a statement')
    print('  about that construction under its seed, and never about the')
    print('  class.  RESEARCH-ARC.md s5.')
    return 6


# ============================================== mode: validate

def run_validate():
    t0 = time.time()
    print('===== BOPEN validate: all EIGHT modes in one process =====')
    run_hyp()
    print()
    run_weak()
    print()
    run_amax()
    print()
    run_fibre()
    print()
    run_slide()
    print()
    run_degx()
    print()
    run_price()
    print()
    run_support()
    print()
    print(f'===== BOPEN validate DONE [{time.time() - t0:.1f}s] =====')


MODES = {'fibre': run_fibre, 'slide': run_slide, 'weak': run_weak,
         'amax': run_amax, 'hyp': run_hyp, 'degx': run_degx,
         'price': run_price, 'support': run_support,
         'validate': run_validate}

if __name__ == '__main__':
    if len(sys.argv) < 2 or sys.argv[1] not in MODES:
        print('usage: bopen.py {' + ' | '.join(MODES) + '}')
        sys.exit(2)
    MODES[sys.argv[1]]()
