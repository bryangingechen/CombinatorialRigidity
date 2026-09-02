"""
Direction BDOUBLE (ordinal 64) -- IS (NO-DOUBLE-PENCIL) TRUE?

  THE TARGET the spec names, BUNIF's own named residue ((BE-97)(iii)):

    (NO-DOUBLE-PENCIL).  At no internal R-node peel does one side have
    dim(rho_bar_i cap Pi_x) = 2 while the other has
    dim(rho_bar_j cap Pi_x) >= 1 -- and the same at Pi_y.

  Its two clauses were said to be "already priced" by (BE-44)(ii) and
  (BE-45), and BUNIF's named attack was to seek them TOGETHER.

  THE ANSWER, said at the top: (NO-DOUBLE-PENCIL) IS FALSE, and the
  double pencil it forbids is HARMLESS -- it carries SLACK, not a
  shortfall.  The two clauses are not merely compatible: ONE landed
  lemma, (BE-45)(ii), produces BOTH of them, and it named the corner
  itself.

    (BE-99)  THE REFUTATION.  (BE-45)(ii) (M2, path saturation) at its own
             explicitly-flagged VACUOUS CORNER d_min = 6 gives
             rho_bar_i = <P> of dimension 6, i.e. rho_bar_i = Lambda^2 K^4,
             hence c_i(U) = dim U at EVERY stable U -- in particular
             c_i(Pi_x) = c_i(Pi_y) = 2.  (BE-45)(i)/(ii) at the other side
             gives c_j(Pi_x) >= 1.  The conjunction is exactly what
             (NO-DOUBLE-PENCIL) forbids, and it is realized INSIDE BUNIF's
             own 92-row population: `K4 + th(6,6,6)/ab + ear4/ua` at peel
             (a,b), side 2 the theta (d_min = 6), side 1 the two-path side
             (d_min = 2).

    (BE-100) IT IS SLACK, NOT A SHORTFALL, and reading (1) is CONFIRMED.
             (NO-DOUBLE-PENCIL) <=> c_1(Pi_x) + c_2(Pi_x) <= 2, which is
             the block inequality only at delta_1 + delta_2 <= 6.  Every
             double pencil produced by the vacuous corner has delta_j = 6,
             hence slack = delta_i >= c_i whenever side i attains.  So the
             exhibited double pencil has margin -1, and half (B) survives.

    (BE-101) THE REDUNDANCY THEOREM -- the tight block is REDUCED, not
             merely re-measured.  Under (PENCIL-SATURATES) -- "c_i(Pi) = 2
             forces rho_i = 6", which is (BE-38)(iii)'s third clause read
             contrapositively -- a violation at U = Pi_x IS a violation at
             U = Lambda^2 K^4.  So Pi_x and Pi_y are IMPLIED by the
             all-of-it inequality and drop out of the fourteen; in the
             attaining case they are FREE.

    (BE-102) READING (2)'s WEAK LINK IS REFUTED, its conclusion RECOVERED
             by a different route, and job 2 FIRES on both citations.

    (BE-103) Job 3, the honest residual in (BE-97)(iv)'s terms, and the
             E-rider.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `arith` (BE-100)/(BE-101)  Pure enumeration, no sampling.  Reading (1)'s
            equivalence over every (c_1, c_2); the delta_1 + delta_2 <= 6
            threshold; the count of double pencils that are NOT violations
            (the gap between the condition and the obligation); the
            REDUNDANCY THEOREM checked exhaustively over every
            (delta, a, c) the caps allow, WITH its negative control (drop
            (PENCIL-SATURATES) and the surviving Pi_x violations are
            printed); and the scope correction to (BE-97)(i)'s own
            enumeration, which used c_i <= delta_i and so spoke about the
            ATTAINING case only.

  `hunt`  (BE-99)  The measured double-pencil hunt over BUNIF's two
            populations: every row's profile at Pi_x and Pi_y, the rows
            carrying c_1 + c_2 >= 3 named and CLASSIFIED violation-vs-slack,
            `margin <= 0` ASSERTED at every row, and `slack` ASSERTED at
            every double pencil.  (PENCIL-SATURATES) asserted at every side
            reaching c_i(Pi) = 2.

  `price` (BE-102)  Reading (2)'s weak link `dist_i >= 6 => delta_i = 6`,
            tested per side against `bimage.dist_in`: (BE-30)'s
            rho_i <= min(dist_i, 6) ASSERTED at every side (the inequality
            runs the OTHER way, which is why the reading fails), and the
            refuting sides -- dist = 6 with delta = 1 -- named.

  `witness` (BE-99)  The exhibited double pencil PINNED at independent
            seeds: side 2's d_min = 6 and rho_bar_2 = Lambda^2 K^4 as a
            SPACE, Pi_x and Pi_y CONTAINED in it, side 1 path-saturated at
            d_min = 2 with c_1 = 1, the margin -1 at both blocks, and the
            F13-style negative control that side 1 does NOT reach 2.

Succeeds `notes/scripts/w4/bunif.py` (Steps BE93-BE97) and, through the
chain, `bbase` / `bgenuine` / `boneone` / `bspread` / `bpeel` / `bdecor` /
`bimage` / `btwocut` / `binduc` / `bwin` / `kbare_common`, all imported
READ-ONLY rather than reimplemented: no deficiency oracle, no rho_bar, no
peel scan, no sampler, no R-node stand-in and no block decomposition is
rewritten here.  The block frame, the profile and the two bounds are
`bunif`'s and are imported, not copied.

Conventions inherited verbatim (`notes/scripts/README.md`): exact integer /
rational arithmetic throughout (`fractions.Fraction`, no floating point), the
single rng seed printed below, every cap disclosed WITH ITS DENOMINATOR.

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import os
import sys
import random
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20) and
# --- BONEONE's (BE-83)(iii) recorded the standing verdict that `w4/` is a
# --- de-facto shared LAYER, not a device chain.  This driver is the
# --- TWENTY-FIRST `kbare/` consumer and takes the chain NINETEEN deep
# --- (`... -> bbase -> bunif -> bdouble`).  NO MOVE MADE.
from bunif import (SEED, SUBS, CAP, battery_peels, battery_rows,        # noqa: E402
                   measure_row, tier_rows)
from bimage import contains, dim, dist_in, same_space                   # noqa: E402
from bdecor import sample_by_branches                                   # noqa: E402
from bpeel import peel_sides                                            # noqa: E402

PIX, PIY, ALL = ('Pix',), ('Piy',), tuple(sorted(('Pix', 'M', 'L', 'Piy')))

# The witness piece and peel, named so the mode does not depend on a scan.
WIT_PIECE = 'K4 + th(6,6,6)/ab + ear4/ua'
WIT_PEEL = ('a', 'b')


def slack_of(d1, d2):
    """max(0, delta_1 + delta_2 - 6) -- the block inequality's own slack."""
    return max(0, d1 + d2 - 6)


def violates(c1, c2, du, d1, d2):
    """Is `c_1(U) + c_2(U) <= dim U + max(0, delta_1+delta_2-6)` BROKEN?
    By (BE-95)(i) a broken instance IS a shortfall, not evidence of one."""
    return c1 + c2 > du + slack_of(d1, d2)


def double_pencil(c1, c2):
    """(NO-DOUBLE-PENCIL) as written: one side at 2, the other at >= 1."""
    return (c1 == 2 and c2 >= 1) or (c2 == 2 and c1 >= 1)


# ================================================== mode: arith  ((BE-100)/(BE-101))

def run_arith(seed=SEED):
    t0 = time.time()
    print(f'== arith: (BE-100)/(BE-101) THE CONDITION vs THE OBLIGATION, '
          f'and the REDUNDANCY THEOREM  [no sampling; seed {seed} unused]')

    # ---- (1) reading (1)'s equivalence, over every profile pair.
    print('  Pass 1 -- reading (1): (NO-DOUBLE-PENCIL) at Pi_x is EXACTLY')
    print('  `c_1 + c_2 <= 2`, because c_i <= dim Pi_x = 2.')
    for c1 in range(3):
        for c2 in range(3):
            assert double_pencil(c1, c2) == (c1 + c2 >= 3), \
                ('reading (1) fails as arithmetic', c1, c2)
    print('    asserted at all 9 profile pairs (c_1, c_2) in {0,1,2}^2.')

    # ---- (2) the threshold: where the condition IS the obligation.
    eq, ne = [], []
    for d1 in range(7):
        for d2 in range(7):
            s = slack_of(d1, d2)
            same = all(double_pencil(c1, c2) == violates(c1, c2, 2, d1, d2)
                       for c1 in range(3) for c2 in range(3))
            (eq if same else ne).append((d1, d2, s))
    assert all(s == 0 for (_a, _b, s) in eq), 'threshold misidentified'
    assert all(s > 0 for (_a, _b, s) in ne), 'threshold misidentified'
    print(f'  Pass 2 -- the THRESHOLD: the condition equals the obligation at')
    print(f'    {len(eq)} of {len(eq) + len(ne)} pairs (delta_1, delta_2) in')
    print(f'    {{0..6}}^2, EXACTLY those with delta_1 + delta_2 <= 6.  Above')
    print(f'    it ({len(ne)} pairs) the inequality has slack the condition')
    print('    never uses, so an exhibited double pencil there is NOT a')
    print('    shortfall.  ASSERTED both ways.')

    # ---- (3) the gap itself, counted over what the caps allow.
    tot, dp, dpviol, viol = 0, 0, 0, 0
    for d1 in range(7):
        for d2 in range(7):
            for a1 in range(7 - d1):
                for a2 in range(7 - d2):
                    r1, r2 = d1 + a1, d2 + a2
                    for c1 in range(min(2, r1) + 1):
                        for c2 in range(min(2, r2) + 1):
                            tot += 1
                            v = violates(c1, c2, 2, d1, d2)
                            p = double_pencil(c1, c2)
                            dp += p
                            viol += v
                            dpviol += (p and v)
    print(f'  Pass 3 -- the GAP, over all {tot} tuples '
          f'(delta_1,delta_2,a_1,a_2,c_1,c_2) the caps rho_i = delta_i + a_i')
    print(f'    <= 6 and c_i <= min(2, rho_i) allow: {dp} are double pencils,')
    print(f'    {viol} are Pi_x violations, and {dpviol} are BOTH.  So')
    print(f'    (NO-DOUBLE-PENCIL) forbids {dp - dpviol} tuples the class')
    print('    statement does not: it is STRICTLY STRONGER than what half (B)')
    print('    needs, and that is where it is refuted.')
    assert viol == dpviol, 'a violation that is not a double pencil'

    # ---- (4) THE REDUNDANCY THEOREM, exhaustively, and its negative control.
    def sweep(law):
        """Pi_x violations, split by whether U = Lambda^2 K^4 also breaks."""
        caught, escaped, att = 0, [], 0
        for d1 in range(7):
            for d2 in range(7):
                for a1 in range(7 - d1):
                    for a2 in range(7 - d2):
                        r1, r2 = d1 + a1, d2 + a2
                        for c1 in range(min(2, r1) + 1):
                            for c2 in range(min(2, r2) + 1):
                                if law and 2 in (c1, c2):
                                    if (c1 == 2 and r1 != 6) or \
                                            (c2 == 2 and r2 != 6):
                                        continue
                                if not violates(c1, c2, 2, d1, d2):
                                    continue
                                if a1 == a2 == 0:
                                    att += 1
                                if violates(r1, r2, 6, d1, d2):
                                    caught += 1
                                else:
                                    escaped.append((d1, d2, a1, a2, c1, c2))
        return caught, escaped, att

    caught, escaped, att = sweep(law=True)
    print('  Pass 4 -- THE REDUNDANCY THEOREM.  Impose (PENCIL-SATURATES),')
    print('    "c_i(Pi) = 2 forces rho_i = 6" ((BE-38)(iii)\'s third clause,')
    print('    contrapositive).  Then every Pi_x violation is ALSO a')
    print(f'    Lambda^2 K^4 violation: {caught} caught, {len(escaped)}')
    print('    escaped.  So the Pi_x inequality is IMPLIED by the')
    print('    all-of-it one, and Pi_x drops out of the fourteen.')
    assert not escaped, ('a Pi_x violation escapes Lambda^2 K^4', escaped[:4])
    print(f'    And in the ATTAINING case a_1 = a_2 = 0 there are {att} Pi_x')
    print('    violations at all -- the block is FREE there.')
    assert att == 0, 'a Pi_x violation survives at a_1 = a_2 = 0'

    caught0, escaped0, att0 = sweep(law=False)
    print('  Pass 4b -- the NEGATIVE CONTROL (F13): DROP (PENCIL-SATURATES)')
    print(f'    and the theorem fails -- {len(escaped0)} Pi_x violations')
    print(f'    escape Lambda^2 K^4 ({att0} of them at a_1 = a_2 = 0).  The')
    print('    smallest, by delta_1 + delta_2:')
    assert escaped0, 'the negative control found nothing to reject'
    assert att0 > 0, 'the negative control is vacuous in the attaining case'
    for row in sorted(escaped0, key=lambda t: (t[0] + t[1], t))[:3]:
        (d1, d2, a1, a2, c1, c2) = row
        print(f'      delta=({d1},{d2}) a=({a1},{a2}) c=({c1},{c2}) '
              f'rho=({d1 + a1},{d2 + a2})')
    print('    so the theorem REALLY rests on the clause, and the clause is')
    print('    the whole residual.')

    # ---- (5) the scope correction to (BE-97)(i)'s own enumeration.
    def live(cap_by_rho):
        out = []
        for sub in SUBS:
            du = sum(CAP[b] for b in sub)
            hit = False
            for d1 in range(7):
                for d2 in range(7):
                    for a1 in range(7 - d1 if cap_by_rho else 1):
                        for a2 in range(7 - d2 if cap_by_rho else 1):
                            u1 = min(du, d1 + a1) if cap_by_rho else min(du, d1)
                            u2 = min(du, d2 + a2) if cap_by_rho else min(du, d2)
                            if violates(u1, u2, du, d1, d2):
                                hit = True
            if hit:
                out.append(sub)
        return out

    lo, hi = live(False), live(True)
    print(f'  Pass 5 -- SCOPE of (BE-97)(i)\'s triage.  Its enumeration bounds')
    print(f'    c_i by delta_i, which is the ATTAINING case: {len(lo)} of 16')
    print(f'    blocks live.  Bounding c_i by rho_i = delta_i + a_i instead --')
    print(f'    the true cap -- gives {len(hi)} of 16: only U = () still dies,')
    print(f'    and U = the whole screw space JOINS the live list, which is')
    print('    exactly the redundancy theorem\'s target.  So "14 of 16 live"')
    print('    is an a_1 = a_2 = 0 statement; the conclusion "the arithmetic')
    print('    does not triage the list" is unchanged and strengthened, and')
    print('    its DENOMINATOR is corrected.')
    assert len(lo) == 14 and len(hi) == 15, (len(lo), len(hi))
    assert ALL not in lo and ALL in hi, 'the whole screw space did not move'
    assert () not in hi, 'the empty subspace bites'
    print(f'  arith: {time.time() - t0:.1f}s')
    return True


# ==================================================== mode: hunt  ((BE-99))

def run_hunt(seed=SEED, ndraw=2, njobs=60):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== hunt: (BE-99) THE DOUBLE-PENCIL HUNT, seed {seed}')
    print('  BUNIF named the attack -- seek (BE-44)(ii)\'s clause and')
    print('  (BE-45)\'s clause TOGETHER.  Run over BUNIF\'s OWN two')
    print('  populations, reading c_1(Pi) + c_2(Pi) rather than the')
    print('  "exceeds the generic profile" census that hid it: a side with')
    print('  rho_i = 6 sits at c_i = 2 GENERICALLY, so it never counted as')
    print('  exceeding, and the double pencil was invisible.')
    nrow, hits, sat2, satbad = 0, [], 0, 0
    perblock = {PIX: 0, PIY: 0}
    for label, gen in (('A', battery_rows(rng, ndraw)),
                       ('B', tier_rows(rng, njobs))):
        for (nm, H, pt, x, y, side1, side2, kind) in gen:
            got = measure_row(H, pt, x, y, side1, side2)
            if got is None:
                continue
            (c1, c2, r1, r2, d1, d2, a1, a2, meas, B, S1, S2, fr) = got
            nrow += 1
            for blk in (PIX, PIY):
                u1, u2 = c1[blk], c2[blk]
                assert not violates(u1, u2, 2, d1, d2), \
                    ('A VIOLATION at a 2-block -- a SHORTFALL', nm, blk)
                if double_pencil(u1, u2):
                    perblock[blk] += 1
                    hits.append((label, nm, x, y, blk[0], u1, u2, r1, r2,
                                 d1, d2, a1, a2))
            for (c, r) in ((c1, r1), (c2, r2)):
                for blk in (PIX, PIY):
                    if c[blk] == 2:
                        sat2 += 1
                        if r != 6:
                            satbad += 1
    print(f'  rows {nrow}; DOUBLE PENCILS found: {len(hits)} '
          f'({perblock[PIX]} at Pi_x, {perblock[PIY]} at Pi_y)')
    assert hits, 'no double pencil found -- the refutation is not reproduced'
    for h in hits:
        (label, nm, x, y, blk, u1, u2, r1, r2, d1, d2, a1, a2) = h
        s = slack_of(d1, d2)
        print(f'    [{label}] {nm} peel({x},{y}) U={blk}: c=({u1},{u2}) '
              f'rho=({r1},{r2}) delta=({d1},{d2}) a=({a1},{a2}) '
              f'slack={s} margin={u1 + u2 - 2 - s}')
        assert u1 + u2 - 2 - s < 0, 'a double pencil with NO slack'
    print('  CLASSIFIED (job 1): every one carries SLACK -- margin < 0 at')
    print('  each, ASSERTED.  So (NO-DOUBLE-PENCIL) is REFUTED and half (B)')
    print('  is UNTOUCHED: the condition forbade a harmless configuration.')
    print(f'  (PENCIL-SATURATES) stress: sides reaching c_i(Pi) = 2: {sat2}; '
          f'of those with rho_i != 6: {satbad}')
    assert satbad == 0, '(PENCIL-SATURATES) FAILS -- report this, it is the residual'
    print('  F11 -- the DENOMINATORS.  Population A = BDECOR\'s 7 R-node')
    print(f'  pieces + BPEEL\'s nested one at {ndraw} draws; population B =')
    print(f'  `bpeel.constructed_tier(maxlen=3, nsamp=60)` filtered by')
    print(f'  `rnode_shaped`, capped at {njobs} peels.  Both are CONSTRUCTED')
    print('  populations, not censuses; "no violation" is evidence about')
    print('  them, never about the class ((BE-97)(iv)).')
    print(f'  hunt: {time.time() - t0:.1f}s')
    return True


# =================================================== mode: price  ((BE-102))

def run_price(seed=SEED, ndraw=2, njobs=60):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== price: (BE-102) READING (2)\'s WEAK LINK, TESTED, seed {seed}')
    print('  Reading (2) needs `dist_i(x,y) >= 6  =>  delta_i = 6`.  But')
    print('  (BE-30) bounds rho by dist from ABOVE: rho_i <= min(dist_i, 6).')
    print('  A large dist REMOVES a constraint; it never supplies one.  So')
    print('  the step is not merely unproved, it points the wrong way.')
    hist, bad, nside = {}, [], 0
    for label, gen in (('A', battery_rows(rng, ndraw)),
                       ('B', tier_rows(rng, njobs))):
        for (nm, H, pt, x, y, side1, side2, kind) in gen:
            got = measure_row(H, pt, x, y, side1, side2)
            if got is None:
                continue
            (c1, c2, r1, r2, d1, d2, a1, a2, meas, B, S1, S2, fr) = got
            for (side, r, d) in ((side1, r1, d1), (side2, r2, d2)):
                D = dist_in(side, x, y)
                assert D is not None, 'a side with no x-y path'
                nside += 1
                assert r <= min(D, 6), \
                    ('(BE-30) rho <= dist VIOLATED', nm, D, r)
                hist[(D, d)] = hist.get((D, d), 0) + 1
                if D >= 6 and d != 6:
                    bad.append((label, nm, x, y, D, r, d))
    print(f'  sides {nside}; (BE-30) `rho_i <= min(dist_i, 6)` ASSERTED at')
    print('  every one.  The (dist, delta) histogram:')
    for k in sorted(hist):
        print(f'    dist {k[0]}  delta {k[1]}   {hist[k]:4d}')
    print(f'  sides with dist >= 6 and delta != 6 -- each REFUTES reading')
    print(f'  (2)\'s weak link: {len(bad)}')
    for b in bad:
        print(f'    [{b[0]}] {b[1]} peel({b[2]},{b[3]}) dist={b[4]} '
              f'rho={b[5]} delta={b[6]}')
    assert bad, 'the refutation is not reproduced on this population'
    print('  So reading (2) FAILS at its named step.  Its CONCLUSION is')
    print('  recovered by a shorter route that never mentions dist:')
    print('  (PENCIL-SATURATES) gives rho_i = 6 directly, and in the')
    print('  attaining case delta_i = rho_i = 6, whence slack = delta_j and')
    print('  a violation needs c_j > delta_j, i.e. a_j >= 1 -- side j')
    print('  NON-ATTAINING, which is exactly what reading (2) predicted.')
    print(f'  price: {time.time() - t0:.1f}s')
    return True


# ================================================= mode: witness  ((BE-99))

def run_witness(seed=SEED, nseed=6):
    t0 = time.time()
    print(f'== witness: (BE-99) THE DOUBLE PENCIL, PINNED, seeds '
          f'{seed}..{seed + nseed - 1}')
    print(f'  Piece `{WIT_PIECE}` at peel {WIT_PEEL} -- a member of BUNIF\'s')
    print('  OWN population A, so the refutation needs no new construction.')
    print('  Side 2 is the theta(6,6,6): d_min = 6, which is (BE-45)(ii)\'s')
    print('  own VACUOUS CORNER.  Side 1 is the two-path side {a-v-b,')
    print('  a-e1-...-u-b}: d_min = 2, path-saturated, so (M2) fires there')
    print('  too.  ONE lemma, both clauses.')
    pc = None
    for nm, cand in battery_peels():
        if nm == WIT_PIECE:
            pc = cand
    assert pc is not None, ('witness piece not in the battery', WIT_PIECE)
    idx = [i for i, (x0, y0, _ce, k0) in enumerate(pc['children'])
           if (x0, y0) == WIT_PEEL and k0 != 'leaf']
    assert len(idx) == 1, ('witness peel not unique', idx)
    x, y, side1, side2, kind = peel_sides(pc, idx[0])
    assert (x, y) == WIT_PEEL, (x, y)
    d1min, d2min = dist_in(side1, x, y), dist_in(side2, x, y)
    print(f'  combinatorics (configuration-free): kind={kind}, '
          f'd_min(side 1) = {d1min}, d_min(side 2) = {d2min}')
    assert (d1min, d2min) == (2, 6), (d1min, d2min)
    drawn = 0
    for s in range(nseed):
        rng = random.Random(seed + s)
        got0 = sample_by_branches(pc['H'], pc['u'], pc['v'], rng)
        if got0 is None:
            continue
        pt = got0[0]
        got = measure_row(pc['H'], pt, x, y, side1, side2)
        if got is None:
            continue
        (c1, c2, r1, r2, d1, d2, a1, a2, meas, B, S1, S2, fr) = got
        drawn += 1
        # side 2: the vacuous corner, as SPACES.
        assert (r2, d2, a2) == (6, 6, 0), ('side 2 off the corner', r2, d2, a2)
        assert same_space(S2, [[1 if i == j else 0 for j in range(6)]
                               for i in range(6)]), \
            'rho_bar_2 is not the whole screw space AS A SPACE'
        assert contains(S2, B['Pix']) and contains(S2, B['Piy']), \
            'the vacuous corner does not contain the pencils'
        assert c2[PIX] == c2[PIY] == 2, (c2[PIX], c2[PIY])
        # side 1: path saturation at d_min = 2, and it does NOT reach 2.
        assert (r1, d1, a1) == (2, 2, 0), ('side 1 not saturated', r1, d1, a1)
        assert c1[PIX] == c1[PIY] == 1, (c1[PIX], c1[PIY])
        # the double pencil, and its classification.
        for blk in (PIX, PIY):
            assert double_pencil(c1[blk], c2[blk]), 'no double pencil'
            m = c1[blk] + c2[blk] - 2 - slack_of(d1, d2)
            assert m == -1, ('margin moved', blk, m)
        # no shortfall: the peel ATTAINS.
        assert meas == min(d1 + d2, 6) + a1 + a2 == 6, (meas, d1, d2)
        # and the two sides DO meet, which is what the condition feared.
        assert dim(S1) + dim(S2) - dim(S1 + S2) == 2, 'the meet moved'
    print(f'  {drawn} of {nseed} seeds drew a generic-regime configuration; '
          f'at every one, ASSERTED:')
    print('    rho_bar_2 = Lambda^2 K^4 AS A SPACE, Pi_x and Pi_y CONTAINED')
    print('      in it, c_2(Pi_x) = c_2(Pi_y) = 2   ((BE-45)(ii), d_min = 6)')
    print('    rho_1 = delta_1 = 2 = d_min, c_1(Pi_x) = c_1(Pi_y) = 1')
    print('      ((BE-45)(ii) again, at d_min = 2)')
    print('    the DOUBLE PENCIL at both 2-blocks, margin exactly -1')
    print('    dim(rho_bar_1 + rho_bar_2) = 6 = min(delta_1+delta_2, 6)')
    print('      + a_1 + a_2 -- the peel ATTAINS, so NO shortfall')
    print('    dim(rho_bar_1 cap rho_bar_2) = 2 -- the two sides DO meet,')
    print('      in the whole pencil Pi_x, which is precisely the')
    print('      intersection (NO-DOUBLE-PENCIL) was written to forbid')
    assert drawn >= 2, 'fewer than two independent witnesses'
    print('  NEGATIVE CONTROL (F13): the SAME assertions with c_1 = 2 in')
    print('  place of 1 must fail, and they do -- side 1 is at rho_1 = 2 and')
    print('  contains only ONE line of Pi_x, so the "both sides at 2" shape')
    print('  is NOT what is exhibited here.  It stays unwitnessed, and by')
    print('  (BE-101) it would be caught at U = Lambda^2 K^4 anyway.')
    print(f'  witness: {time.time() - t0:.1f}s')
    return True


def run_validate():
    ok = True
    ok &= run_arith()
    ok &= run_witness(nseed=3)
    ok &= run_hunt(ndraw=1, njobs=25)
    ok &= run_price(ndraw=1, njobs=25)
    print(f'\nVALIDATE: {"ALL MODES PASS" if ok else "FAILURE"}')
    return ok


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    fn = {'arith': run_arith, 'hunt': run_hunt, 'price': run_price,
          'witness': run_witness, 'validate': run_validate}[mode]
    fn()
