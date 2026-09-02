"""
Direction BSATUR (ordinal 65) -- IS (PENCIL-SATURATES) TRUE?

  THE TARGET the spec names, the clause BDOUBLE's redundancy theorem
  ((BE-101)) is CONDITIONAL on:

    (PENCIL-SATURATES).  For a side of an internal R-node peel,
    dim(rho_bar_i cap Pi) = 2  =>  rho_i = 6 -- at Pi = Pi_x and at
    Pi = Pi_y.

  It is (BE-38)(iii)'s THIRD clause ("never 2 below rho_1 = 6"), whose
  own sentence's MIDDLE clause was refuted by (BE-45)(iii).

  THE ANSWER, said at the top: (PENCIL-SATURATES) IS FALSE.  It fails at
  EXACTLY rho_i = 5, at a flag that is legal, inside the GENERIC flag
  regime, at an internal R-node peel, through both gates.  And the
  failure is SLACK, not a shortfall: at every exhibited bad-flag row
  the peel still ATTAINS and no block inequality is broken.

    (BE-104) THE REFUTATION.  Witness `K4(5,3,3,3,3,3)` peeled at its
             5-branch: side 1 is that branch (deg_1(x) = 1), rho_1 = 5,
             and there is a plane pi_x -- the closed-star plane of x in
             the WHOLE graph, asserted as such -- with Pi_x <= rho_bar_1,
             i.e. c_1(Pi_x) = 2 at rho_1 = 5 < 6.

    (BE-105) THE MECHANISM, and why the 24 x 14 run could not fire.  At
             a terminal of side-degree 1 the legal planes at x form a
             PENCIL (those through the line p_x v p_{c_1}), and exactly
             one of them is bad -- the one carrying `t` where
             rho_bar_i cap Sigma_x = <l_1, p_x ^ t>.  That intersection
             has dimension max(1, rho_i - 3), so a bad plane exists IFF
             rho_i >= 5.  Every sampler in the corpus draws that plane
             at random, so the bad plane is a measure-zero event no
             sampled run can reach.  The middle clause over-read a
             SUFFICIENT condition as a characterization; the third
             clause over-read a GENERIC statement as a universal one.

    (BE-106) THE PRICE.  0 shortfalls at the bad-flag rows `scan`
             exhibits over three skeletons; every row ATTAINS.  But the
             Pi_x inequality is TIGHT (margin 0) at 43 % of them, and
             there (BE-101)(i)'s
             implication has no proof: with the clause replaced by its
             measured floor `c_i(Pi) = 2 => rho_i >= 5`, Pi_x violations
             ESCAPE the U = Lambda^2 K^4 inequality.

    (BE-107) THE REPAIR, and it is FREE.  Bad flags are a proper closed
             subset of the legal pencil (codimension 1) exactly when
             Sigma_x is not inside rho_bar_i, measured true at every
             side with rho_i <= 5.  Since (BE-14) is EXISTENTIAL
             ((BE-16)) and the good locus is dense on an irreducible
             chart ((BE-69)), reading the clause AT THE GENERIC FLAG
             costs the arc nothing, and (BE-101) survives verbatim
             there.  At a terminal of side-degree >= 2 there is no flag
             freedom at all and the clause needs no repair.

    (BE-108) Job 2 (the <M> hunt), job 3 (the residual + the E-rider),
             and the coordinator's reading, classified.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `witness` (BE-104)  The pinned refutation at independent seeds, every
            line an ASSERT: the peel is R-node-shaped, the flag pair is
            in the GENERIC regime, `assert_generic_star` and
            `verify_pencil_witness` both pass, `plane_at` at x IS the
            constructed plane, rho_1 = 5, Pi_x <= rho_bar_1 AS SPACES,
            and the peel ATTAINS.  F13 negative control: the SAME
            configuration read at the sampler's own random plane gives
            c_1(Pi_x) = 1.

  `mech`  (BE-105)  The threshold, on the corpus battery: at every
            deg-1 terminal `dim(rho_bar cap Sigma_x) = max(1, rho - 3)`
            ASSERTED, so the bad plane exists iff rho >= 5 and is
            UNIQUE; and at every deg->=2 terminal Pi_x is the span of
            two of the side's OWN hinge lines (asserted as spaces), so
            no flag freedom exists there.

  `scan`  (BE-106)  The bad-flag scan over subdivided K4 / prism /
            K_{3,3} skeletons: every row's margin at Pi_x, `margin <= 0`
            and `reach = min(delta_1+delta_2, 6) + a_1 + a_2` ASSERTED
            at every row, the tight rows counted.

  `arith` (BE-106)  Pure enumeration, no sampling: (BE-101)(i) re-run
            with the REFUTED clause replaced by the measured floor, and
            the escaping Pi_x violations counted and exhibited.

  `mhunt` (BE-108)  Job 2: the `c_i(<M>) = 1 on BOTH sides` hunt over
            BUNIF's two populations, with its cap and denominator.

Succeeds `notes/scripts/w4/bdouble.py` (Steps BE98-BE102) and, through
the chain, `bunif` / `bearcase` / `bpeel` / `bdecor` / `bimage` /
`binduc` / `kbare_common`, all imported READ-ONLY rather than
reimplemented: no deficiency oracle, no rho_bar, no peel scan, no
sampler, no R-node stand-in and no block decomposition is rewritten
here.

Conventions inherited verbatim (`notes/scripts/README.md`): exact
integer / rational arithmetic throughout (`fractions.Fraction`, no
floating point), the single rng seed printed below, every cap disclosed
WITH ITS DENOMINATOR.

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import os
import sys
import time
import random
import itertools
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- This driver is the TWENTY-SECOND `kbare/` consumer and takes the
# --- chain TWENTY deep (`... -> bunif -> bdouble -> bsatur`).  NO MOVE MADE.
from exactcore import hat, wedge2, rank, nullspace, rref, neighbors   # noqa: E402
from binduc import split_at_pair                                     # noqa: E402
from bimage import (contains, dim, isect, pencil_space, plane_at,    # noqa: E402
                    rho_bar_of, same_space, span)
from bearcase import piece_battery, sample_piece_config              # noqa: E402
from bpeel import SKELETONS, delta_pair, rnode_shaped, subdivided    # noqa: E402
from bdecor import (assemble, d3, draw_branch, flag_assignment,      # noqa: E402
                    hubs_and_branches, weld_d3)
from bunif import (SEED, battery_rows, blocks_of, flag_frame,        # noqa: E402
                   measure_row, profile, tier_rows)

PIX, PIY, MB, ALLU = ('Pix',), ('Piy',), ('M',), tuple(
    sorted(('Pix', 'M', 'L', 'Piy')))

# The pinned witness, named so the mode does not depend on a scan.
WIT_SKEL = 'K4'
WIT_PROF = [5, 3, 3, 3, 3, 3]
WIT_EDGE = 0                       # the peeled skeleton edge, ('A','B')


# ======================================================= small primitives

def sigma_at(p):
    """Sigma_x = p ^ K^4, the 3-dimensional space of lines through p."""
    out = span([wedge2(p, [F(1) if i == j else F(0) for i in range(4)])
                for j in range(4)])
    assert dim(out) == 3, ('the star of a point is not 3-dimensional', dim(out))
    return out


def point_of(px, beta):
    """The `t` with beta = p_x ^ t, for beta in Sigma_x.  ASSERTS the wedge
    back, so a wrong solve cannot pass silently."""
    rows = [wedge2(px, [F(1) if i == j else F(0) for i in range(4)])
            for j in range(4)]
    A = [[rows[j][i] for j in range(4)] + [beta[i]] for i in range(6)]
    R, piv = rref(A)
    t = [F(0)] * 4
    for ri, p in enumerate(piv):
        if p < 4:
            t[p] = R[ri][4]
    back = [sum(t[j] * rows[j][i] for j in range(4)) for i in range(6)]
    assert back == list(beta), 'the Sigma_x solve did not invert the wedge'
    return t


def bad_plane(S, px, pc1):
    """(BE-105): THE BAD PLANE at a terminal of side-degree 1.  Returns a
    basis of the unique plane pi_x through p_x and p_{c_1} with
    Pi_x <= S, or None when rho <= 4 leaves no room for one."""
    l1 = wedge2(px, pc1)
    assert contains(S, [l1]), \
        '(M1) fails: the series-end hinge line is not in rho_bar'
    inter = isect(S, sigma_at(px))
    assert contains(inter, [l1]), 'l_1 is not in rho_bar cap Sigma_x'
    if dim(inter) < 2:
        return None
    beta = next((b for b in inter if dim([l1, b]) == 2), None)
    assert beta is not None, 'a 2-dimensional space with no second vector'
    t = point_of(px, beta)
    if rank([px, pc1, t]) != 3:
        return None
    B = nullspace([nullspace([px, pc1, t])[0]])
    assert dim(B) == 3 and rank(B + [px]) == 3, \
        'the constructed plane does not carry p_x'
    Pi = pencil_space(px, B)
    assert contains(S, Pi), 'the constructed plane is not bad'
    return B


def peel_of(skname, prof, ei):
    """(E, x, y, side1, side2) with side 1 = the PEELED BRANCH itself, or
    None when the pair is not a 2-cut or the peel is not R-node-shaped."""
    sk = SKELETONS[skname]
    E = subdivided(sk, prof)
    x, y = sk[ei]
    got = delta_pair(E, x, y)
    if got is None:
        return None
    _d1, _d2, Ea, Eb = got
    if not (rnode_shaped(Ea, x, y) or rnode_shaped(Eb, x, y)):
        return None
    if len(Ea) == prof[ei]:
        side1, side2 = Ea, Eb
    elif len(Eb) == prof[ei]:
        side1, side2 = Eb, Ea
    else:
        return None
    return E, x, y, side1, side2


def draw_peel(E, x, y, rng):
    """One legal pencil configuration of the whole graph, through BOTH
    gates, plus the hub flags it was built from."""
    W, branches = hubs_and_branches(E, x, y)
    P, B = flag_assignment(W, branches, rng)
    if P is None:
        return None
    pts = dict(P)
    for (z, zp, ints) in branches:
        g = draw_branch(P, B, z, zp, len(ints), rng)
        if g is None:
            return None
        for w, c in zip(ints, g):
            pts[w] = c
    aff = assemble(E, pts)
    if aff is None:
        return None
    return P, B, pts, aff, branches


def reflag(E, x, side1, P, B, pts, badB, branches, rng, tries=120):
    """Re-place the SIDE-2 branches at x so that the closed-star plane of
    x becomes `badB`, leaving side 1 -- and hence rho_bar_1 -- untouched."""
    B2 = dict(B)
    B2[x] = badB
    V1 = {w for e in side1 for w in e}
    for _ in range(tries):
        new = dict(pts)
        ok = True
        for (z, zp, ints) in branches:
            if x not in (z, zp) or set(ints) <= V1:
                continue
            g = draw_branch(P, B2, z, zp, len(ints), rng)
            if g is None:
                ok = False
                break
            for w, c in zip(ints, g):
                new[w] = c
        if not ok:
            continue
        aff = assemble(E, new)
        if aff is None:
            continue
        pa = plane_at(E, aff, x)
        if pa is not None and same_space(pa, badB):
            return aff
    return None


def row_of(E, x, y, side1, side2, aff):
    """The measured row at one configuration, in BUNIF's own vocabulary."""
    fr = flag_frame(E, aff, x, y)
    if fr is None:
        return None
    Bl = blocks_of(fr)
    S1, r1, dM1, _ = rho_bar_of(side1, aff, x, y)
    S2, r2, dM2, _ = rho_bar_of(side2, aff, x, y)
    f1, g1 = d3(side1), weld_d3(side1, x, y)
    f2, g2 = d3(side2), weld_d3(side2, x, y)
    d1, d2 = f1 - g1, f2 - g2
    return dict(c1=profile(S1, Bl), c2=profile(S2, Bl), r1=r1, r2=r2,
                d1=d1, d2=d2, a1=dM1 - 6 - f1, a2=dM2 - 6 - f2,
                reach=dim(S1 + S2), slack=max(0, d1 + d2 - 6), S1=S1, S2=S2,
                blocks=Bl)


def margin_at(row, blk, du):
    return row['c1'][blk] + row['c2'][blk] - du - row['slack']


# ================================================ mode: witness  ((BE-104))

def run_witness(nseed=6):
    t0 = time.time()
    print(f'== witness: (BE-104) (PENCIL-SATURATES) IS FALSE -- the pinned '
          f'refutation, seed {SEED}')
    print(f'  The peel: `{WIT_SKEL}{tuple(WIT_PROF)}` at skeleton edge '
          f'{SKELETONS[WIT_SKEL][WIT_EDGE]}, side 1 = the 5-branch.')
    got = peel_of(WIT_SKEL, WIT_PROF, WIT_EDGE)
    assert got is not None, 'the pinned witness is not an R-node peel'
    E, x, y, side1, side2 = got
    assert len(side1) == 5, 'side 1 is not the 5-branch'
    nb1 = neighbors(side1)
    assert len(nb1[x]) == 1, 'the terminal is not of side-degree 1'
    assert rnode_shaped(side1, x, y) or rnode_shaped(side2, x, y), \
        'the peel is not R-node-shaped'
    print('  ASSERTED already: {x,y} is a 2-cut, the peel is R-NODE-SHAPED,')
    print('  side 1 is the 5-edge branch and deg_1(x) = 1 (a SERIES END).')
    c1v = sorted(nb1[x], key=str)[0]
    drawn = 0
    for sd in range(nseed):
        rng = random.Random(SEED + 1013 * sd)
        d = draw_peel(E, x, y, rng)
        if d is None:
            continue
        P, B, pts, aff, branches = d
        S1, r1, _dM, _ = rho_bar_of(side1, aff, x, y)
        if r1 != 5:
            continue
        px, pc1 = hat(aff[x]), hat(aff[c1v])
        badB = bad_plane(S1, px, pc1)
        if badB is None:
            continue
        # --- F13 NEGATIVE CONTROL: the sampler's OWN plane is not bad.
        pa0 = plane_at(E, aff, x)
        assert pa0 is not None, 'the drawn configuration has no plane at x'
        c0 = dim(isect(S1, pencil_space(px, pa0)))
        assert c0 == 1, ('the sampler already drew a bad plane', c0)
        assert not same_space(pa0, badB), 'the bad plane was the drawn one'
        aff2 = reflag(E, x, side1, P, B, pts, badB, branches, rng)
        if aff2 is None:
            continue
        row = row_of(E, x, y, side1, side2, aff2)
        if row is None:
            continue                      # off the generic flag regime
        S1b, r1b, _d, _ = rho_bar_of(side1, aff2, x, y)
        assert same_space(S1b, S1) and r1b == 5, 'side 1 moved under the reflag'
        Pi = pencil_space(px, badB)
        assert contains(S1b, Pi), 'Pi_x is NOT inside rho_bar_1'
        assert row['c1'][PIX] == 2 and row['r1'] == 5, \
            ('the refutation did not land', row['c1'][PIX], row['r1'])
        # the peel still ATTAINS, and Pi_x is not violated.
        assert row['reach'] == min(row['d1'] + row['d2'], 6) \
            + row['a1'] + row['a2'], ('the peel does not attain', row['reach'])
        assert margin_at(row, PIX, 2) <= 0, 'a shortfall at Pi_x'
        drawn += 1
        if drawn == 1:
            print(f'    rho_1 = {row["r1"]}, c_1(Pi_x) = {row["c1"][PIX]}, '
                  f'c_1(Pi_y) = {row["c1"][PIY]}')
            print(f'    rho_2 = {row["r2"]}, c_2(Pi_x) = {row["c2"][PIX]}')
            print(f'    delta = ({row["d1"]}, {row["d2"]}), '
                  f'a = ({row["a1"]}, {row["a2"]}), slack = {row["slack"]}')
            print(f'    reach = {row["reach"]} = min(delta_1+delta_2, 6) '
                  f'+ a_1 + a_2  -- the peel ATTAINS')
            print(f'    margin at Pi_x = {margin_at(row, PIX, 2)}  '
                  f'-- SLACK, not a shortfall')
    print(f'  {drawn} of {nseed} seeds produced the witness; at every one, '
          f'ASSERTED:')
    print('    the constructed plane IS `plane_at`\'s closed-star plane of x')
    print('      in the WHOLE graph (so the pencil condition at x holds with')
    print('      SIDE 2\'s neighbours of x inside it too)')
    print('    `assert_generic_star` AND `verify_pencil_witness` both pass')
    print('      (they are `bdecor.assemble`\'s two gates)')
    print('    the flag pair is in the GENERIC regime (`flag_frame` non-None:')
    print('      pi_x != pi_y, p_x notin pi_y, p_y notin pi_x)')
    print('    Pi_x <= rho_bar_1 AS SPACES with rho_1 = 5 -- so')
    print('      (PENCIL-SATURATES) IS FALSE')
    print('    F13 negative control: at the SAME side-1 configuration the')
    print('      sampler\'s own random plane gives c_1(Pi_x) = 1, which is')
    print('      why 24 x 14 draws never saw this')
    assert drawn >= 2, 'fewer than two independent witnesses'
    print(f'  witness: {time.time() - t0:.1f}s')
    return True


# =================================================== mode: mech  ((BE-105))

def run_mech(nseeds=6):
    t0 = time.time()
    print(f'== mech: (BE-105) THE MECHANISM AND ITS EXACT THRESHOLD, '
          f'seed {SEED}')
    print('  At a terminal of side-degree 1 the legal planes at x form a')
    print('  PENCIL (those through the line p_x v p_{c_1}); a plane is BAD')
    print('  exactly when it carries a `t` with p_x ^ t in rho_bar.  So the')
    print('  bad planes correspond to  (rho_bar cap Sigma_x) / <l_1>, and')
    print('  there is EXACTLY ONE iff dim(rho_bar cap Sigma_x) = 2.')
    print('  CLAIM, asserted below: that dimension is max(1, rho - 3), so a')
    print('  bad plane exists IFF rho >= 5 -- which is why the failure sits')
    print('  at rho = 5 and nowhere lower.')
    one, two, skipped = [], [], 0
    for (name, edges, u, v) in piece_battery():
        nb = neighbors(edges)
        got = None
        for sd in range(nseeds):
            rng = random.Random(SEED + 7919 * sd + len(name))
            g, _why = sample_piece_config(edges, u, v, rng)
            if g is None:
                break
            pt, planes = g
            S, r, _dM, _ = rho_bar_of(edges, pt, u, v)
            got = (pt, planes, S, r) if (got is None or r > got[3]) else got
        if got is None:
            skipped += 1
            continue
        pt, planes, S, r = got
        px = hat(pt[u])
        ds = dim(isect(S, sigma_at(px))) if S else 0
        deg = len(nb[u])
        if deg == 1:
            assert ds == max(1, r - 3), \
                ('the threshold moved at a deg-1 terminal', name, r, ds)
            one.append((name, r, ds))
        else:
            # Pi_u is the span of TWO of the side's OWN hinge lines: no
            # flag freedom exists at this terminal at all.
            ws = sorted(nb[u], key=str)[:2]
            L = span([wedge2(px, hat(pt[w])) for w in ws])
            assert same_space(L, pencil_space(px, planes[u])), \
                ('Pi_u is not the span of two own hinge lines', name)
            c = dim(isect(S, pencil_space(px, planes[u]))) if S else 0
            assert not (c == 2 and r < 6), \
                ('c = 2 below rho = 6 at a deg->=2 terminal', name, r)
            two.append((name, r, c))
        assert ds >= max(0, r - 3), 'the modular law is violated'
    print(f'  deg_1(x) = 1 terminals: {len(one)} pieces, '
          f'`dim(rho_bar cap Sigma_x) = max(1, rho - 3)` ASSERTED at each.')
    print('    rho -> dim(rho_bar cap Sigma_x): '
          + ', '.join(f'{r}->{d}' for (_n, r, d) in sorted(
              {(None, r, d) for (_n, r, d) in one}, key=lambda z: z[1])))
    print(f'    so a bad plane exists at exactly the '
          f'{sum(1 for (_n, r, _d) in one if r >= 5)} pieces with rho >= 5, '
          f'and at none of the {sum(1 for (_n, r, _d) in one if r < 5)} below.')
    print(f'  deg_1(x) >= 2 terminals: {len(two)} pieces.  `Pi_u = <l_e, l_e\'>`'
          f' for the side\'s')
    print('    OWN two hinge lines ASSERTED as spaces -- so the flag carries')
    print('    NO freedom at x and the bad-plane mechanism cannot run.  On')
    print('    that class `c = 2 => rho = 6` is ASSERTED and holds.')
    print(f'  CAP.  {len(one) + len(two)} pieces of BEARCASE\'s 24-piece '
          f'battery ({skipped} rejected by its own shape guard), one guarded')
    print('  draw each at the measured max rho over '
          f'{nseeds} seeds.  This is a')
    print('  statement about that battery, not a theorem about all pieces.')
    print(f'  mech: {time.time() - t0:.1f}s')
    return True


# =================================================== mode: scan  ((BE-106))

def K4_PROFILES(step=7):
    """Deterministic slice of the K4 profile cube with the peeled branch at
    5: every `step`-th profile of {1..4}^5, so the mode is reproducible and
    fits the foreground budget."""
    out = []
    for k, rest in enumerate(itertools.product(range(1, 5), repeat=5)):
        if k % step == 0:
            out.append([5] + list(rest))
    return out


def OTHER_PROFILES(name, n, seed=SEED):
    rng = random.Random(seed + len(name))
    out = []
    for _ in range(n):
        prof = [rng.randint(1, 4) for _ in range(len(SKELETONS[name]))]
        prof[rng.randrange(len(prof))] = 5
        out.append(prof)
    return out


def run_scan(step=3, nother=16, nseed=2, minhit=50):
    t0 = time.time()
    print(f'== scan: (BE-106) THE BAD-FLAG SCAN -- how far the refutation '
          f'reaches, and what it costs.  seed {SEED}')
    jobs = [('K4', p, 0) for p in K4_PROFILES(step)]
    for nm in ('prism', 'K33'):
        for p in OTHER_PROFILES(nm, nother):
            jobs.append((nm, p, p.index(5)))
    ntot = nhit = ntight = nviol = 0
    hist, cpair, dpair = {}, {}, {}
    for (nm, prof, ei) in jobs:
        got = peel_of(nm, prof, ei)
        if got is None:
            continue
        E, x, y, side1, side2 = got
        nb1 = neighbors(side1)
        if len(nb1[x]) != 1:
            continue
        c1v = sorted(nb1[x], key=str)[0]
        for sd in range(nseed):
            rng = random.Random(SEED + 1013 * sd + 17 * ei)
            d = draw_peel(E, x, y, rng)
            if d is None:
                continue
            P, B, pts, aff, branches = d
            S1, r1, _dM, _ = rho_bar_of(side1, aff, x, y)
            ntot += 1
            if r1 != 5:
                continue
            badB = bad_plane(S1, hat(aff[x]), hat(aff[c1v]))
            if badB is None:
                continue
            aff2 = reflag(E, x, side1, P, B, pts, badB, branches, rng)
            if aff2 is None:
                continue
            row = row_of(E, x, y, side1, side2, aff2)
            if row is None:
                continue
            S1b, _r, _d2, _ = rho_bar_of(side1, aff2, x, y)
            assert same_space(S1b, S1), 'side 1 moved under the reflag'
            assert row['c1'][PIX] == 2 and row['r1'] == 5, 'not a bad-flag row'
            m = margin_at(row, PIX, 2)
            assert m <= 0, ('A SHORTFALL at Pi_x', nm, prof, m)
            assert row['reach'] == min(row['d1'] + row['d2'], 6) \
                + row['a1'] + row['a2'], ('non-attaining row', nm, prof)
            for sub in (PIX, PIY, MB, ALLU):
                du = sum({'Pix': 2, 'Piy': 2, 'M': 1, 'L': 1}[b] for b in sub)
                assert margin_at(row, sub, du) <= 0, ('a shortfall', sub)
            nhit += 1
            ntight += (m == 0)
            nviol += (m > 0)
            hist[m] = hist.get(m, 0) + 1
            cpair[(row['c1'][PIX], row['c2'][PIX])] = \
                cpair.get((row['c1'][PIX], row['c2'][PIX]), 0) + 1
            dpair[(row['d1'], row['d2'])] = dpair.get((row['d1'], row['d2']),
                                                      0) + 1
    print(f'  {ntot} drawn peel rows; {nhit} BAD-FLAG rows exhibited '
          f'(c_1(Pi_x) = 2 with rho_1 = 5).')
    print(f'  margin at Pi_x: ' + ', '.join(f'{k}: {hist[k]}'
                                            for k in sorted(hist)))
    print(f'  SHORTFALLS: {nviol}.  `margin <= 0` and `reach = '
          f'min(delta_1+delta_2,6) + a_1 + a_2` ASSERTED at every row, and')
    print('  the same `margin <= 0` at Pi_y, <M> and Lambda^2 K^4 too.')
    print(f'  TIGHT rows (margin exactly 0 at Pi_x): {ntight} of {nhit}.  '
          f'There Pi_x')
    print('  is the binding block WITHOUT rho_1 = 6, which is exactly what')
    print('  (BE-101)(i)\'s proof needed and no longer has.')
    print('  (c_1, c_2) at Pi_x: '
          + ', '.join(f'{k}: {cpair[k]}' for k in sorted(cpair)))
    print('  (delta_1, delta_2): '
          + ', '.join(f'{k}: {dpair[k]}' for k in sorted(dpair)))
    print(f'  CAP.  {len(jobs)} skeleton profiles (K4 every {step}-th of the '
          f'4^5 cube with the')
    print(f'  peeled branch at 5, plus {nother} seeded profiles each of the '
          f'prism and K_{{3,3}}),')
    print(f'  {nseed} draws each.  "0 shortfalls" is a statement about these '
          f'{nhit} rows.')
    assert nhit >= minhit, \
        'the scan exhibited too few bad-flag rows to speak'
    assert nviol == 0, 'a shortfall was found -- half (B) would be at risk'
    print(f'  scan: {time.time() - t0:.1f}s')
    return True


# ================================================== mode: arith  ((BE-106))

def run_arith():
    t0 = time.time()
    print('== arith: (BE-106) WHAT THE REFUTATION COSTS (BE-101)(i) '
          '[no sampling]')
    print('  (BE-101)(i): "assume (PENCIL-SATURATES); then a failure at')
    print('  U = Pi_x is a failure at U = Lambda^2 K^4."  Re-run over the')
    print('  SAME tuple space with the clause replaced by the measured')
    print('  floor  `c_i(Pi) = 2 => rho_i >= 5`  ((BE-105)).')

    def tuples():
        for d1 in range(7):
            for d2 in range(7):
                for a1 in range(7 - d1):
                    for a2 in range(7 - d2):
                        r1, r2 = d1 + a1, d2 + a2
                        for c1 in range(min(2, r1) + 1):
                            for c2 in range(min(2, r2) + 1):
                                yield d1, d2, a1, a2, r1, r2, c1, c2

    def viol_pix(c1, c2, d1, d2):
        return c1 + c2 > 2 + max(0, d1 + d2 - 6)

    def viol_all(r1, r2, d1, d2):
        return r1 + r2 > 6 + max(0, d1 + d2 - 6)

    for floor, tag in ((6, 'the LANDED clause, rho_i = 6'),
                       (5, 'the MEASURED floor, rho_i >= 5'),
                       (0, 'NO clause at all (F13 negative control)')):
        tot = pv = esc = 0
        smallest = None
        for (d1, d2, a1, a2, r1, r2, c1, c2) in tuples():
            if floor == 6 and ((c1 == 2 and r1 != 6) or (c2 == 2 and r2 != 6)):
                continue
            if floor == 5 and ((c1 == 2 and r1 < 5) or (c2 == 2 and r2 < 5)):
                continue
            tot += 1
            if not viol_pix(c1, c2, d1, d2):
                continue
            pv += 1
            if not viol_all(r1, r2, d1, d2):
                esc += 1
                if smallest is None:
                    smallest = (d1, d2, a1, a2, c1, c2)
        print(f'  {tag}: {tot} admissible tuples, {pv} Pi_x violations, '
              f'{esc} ESCAPE U = Lambda^2 K^4.')
        if smallest is not None:
            print(f'    smallest escapee: delta = ({smallest[0]}, '
                  f'{smallest[1]}), a = ({smallest[2]}, {smallest[3]}), '
                  f'c = ({smallest[4]}, {smallest[5]})')
        if floor == 6:
            assert esc == 0, 'the landed theorem should have no escapees'
        else:
            assert esc > 0, 'the weakened clause should let violations escape'
    print('  READ THIS THE RIGHT WAY.  The escapees are ARITHMETIC: they say')
    print('  the theorem\'s PROOF is gone under the corrected clause, not')
    print('  that any of them is realized.  `scan` found NONE realized at')
    print('  any exhibited bad-flag row, which is why the price is a lost')
    print('  and not a lost result.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return True


# ================================================== mode: mhunt  ((BE-108))

def run_mhunt(ndraw=2, njobs=40):
    t0 = time.time()
    print(f'== mhunt: (BE-108) JOB 2 -- the `c_i(<M>) = 1 on BOTH sides` '
          f'hunt, seed {SEED}')
    print('  (BE-97)(iv) names this as the one shape that would put a SECOND')
    print('  block in play at once: both relative screw spaces containing')
    print('  the virtual edge\'s own line M = p_x v p_y.  The GENERIC value')
    print('  of c_i(<M>) is max(0, rho_i - 5), so "exceeding the generic')
    print('  profile" at <M> means c_i(<M>) = 1 with rho_i <= 5.')
    rng = random.Random(SEED)
    rows = list(battery_rows(rng, ndraw)) + list(tier_rows(rng, njobs))
    n = nboth = nexc = nsingle = 0
    pairs = {}
    for (nm, H, pt, x, y, s1, s2, kind) in rows:
        got = measure_row(H, pt, x, y, s1, s2)
        if got is None:
            continue
        c1, c2, r1, r2, d1, d2, a1, a2, reach, B, S1, S2, fr = got
        n += 1
        k = (c1[MB], c2[MB])
        pairs[k] = pairs.get(k, 0) + 1
        for (cc, rr) in ((c1, r1), (c2, r2)):
            assert cc[MB] <= 1, 'c(<M>) exceeds dim <M>'
            assert cc[MB] >= max(0, rr - 5), 'the modular law fails at <M>'
            if cc[MB] == 1 and rr <= 5:
                nexc += 1
        if c1[MB] == 1 and c2[MB] == 1:
            nboth += 1
            m = c1[MB] + c2[MB] - 1 - max(0, d1 + d2 - 6)
            print(f'    BOTH-SIDES <M> HIT: {nm} rho = ({r1}, {r2}), '
                  f'delta = ({d1}, {d2}), margin at <M> = {m}')
            assert m <= 0, 'a shortfall at <M>'
        elif c1[MB] + c2[MB] == 1:
            nsingle += 1
    print(f'  {n} peel rows (BUNIF populations A and B, {ndraw} draws / '
          f'{njobs} tier jobs).')
    print('  (c_1(<M>), c_2(<M>)) census: '
          + ', '.join(f'{k}: {pairs[k]}' for k in sorted(pairs)))
    print(f'  BOTH-SIDES hits: {nboth}.  One-sided: {nsingle}.  Sides '
          f'EXCEEDING the generic profile at <M>: {nexc}.')
    print('  VERDICT (F11): none found under this cap.  This is')
    print('  "no both-sides <M> row in these populations", NEVER "does not')
    print(f'  exist" -- the denominator is {n} rows, and the hunt is an')
    print('  EXISTENCE search.  It is the FIRST measurement of the 12-block')
    print('  residue (BE-103)(i) left unwitnessed-not-excluded.')
    print('  STRUCTURAL NOTE, offered as the reason the shape is hard rather')
    print('  than as a proof: M in rho_bar_i <= <P> for EVERY x-y path P of')
    print('  side i, and the two cheap constructions that force M into a')
    print('  side -- putting a neighbour of x, or of y, on the line M --')
    print('  each put p_y in pi_x (resp. p_x in pi_y) and so leave the')
    print('  GENERIC FLAG REGIME, where the whole block law lives ((BE-98)).')
    print(f'  mhunt: {time.time() - t0:.1f}s')
    return True


def run_validate():
    ok = True
    ok &= run_witness(nseed=4)
    ok &= run_mech(nseeds=4)
    ok &= run_arith()
    ok &= run_mhunt(ndraw=1, njobs=25)
    ok &= run_scan(step=13, nother=8, nseed=1, minhit=20)
    print(f'\nVALIDATE: {"ALL MODES PASS" if ok else "FAILURE"}')
    return ok


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    fn = {'witness': run_witness, 'mech': run_mech, 'scan': run_scan,
          'arith': run_arith, 'mhunt': run_mhunt,
          'validate': run_validate}[mode]
    fn()
