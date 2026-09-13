"""BNEST (ordinal 119) -- IS `rho_bar_i` EVER NESTED WITH `<P_0> cap U` AT
THE TWO SURVIVING PROFILES?

The dispatch asks whether nestedness can occur at the two profiles BGPLAW's
`bgplaw.py targets` leaves standing -- `U = L+M+Pi_x` and `U = L+M+Pi_y` at
`dim <P_0> = 5`, `rho_i = 3` -- on the reading that a "never nested" lemma
would then close (BLOCK-GP) entire.

`arith` answers it draw-free and the answer DISSOLVES the question: the two
survivors are the two targets DEFINED by NOT being the nested extreme, so
nestedness there is excluded by the profile's own `c_i`, at no cost, and
excluding it buys nothing.  `bgplaw.run_targets` already says so in band
("NON-NESTEDNESS kills 30 of the 32 targets and is NOT sufficient").

`perp` supplies the replacement.  `Pi_x` is totally singular for the Klein
form and the four blocks sum directly, so `L + M + Pi_x` IS `Pi_x^perp`;
hence, at EVERY configuration,

    c_i(L+M+Pi_x) = rho_i - rank K(rho_bar_i, Pi_x)
                  = rho_i - 2 + dim(Pi_x cap rho_bar_i^perp),

and at the surviving profiles (`rho_i = 3`, allowance `1`) (BLOCK-GP) is
EXACTLY `rho_bar_i^perp cap Pi_x = 0`.  That is (BE-279)(ii)'s Klein
annihilator read against `rho_bar_i` instead of `<P>`, which is the
instrument the dispatch named.

`fifth` spends the probe (BE-302)(iii) names as the cheapest unspent one:
`bgoodempty.skeleton_pairs`, the fifth side family, scored against the 32
printed targets.  BGPLAW did not run it.

CAPS are printed in band by every mode.  Exact Q throughout; every random
draw is seeded off `SEED = 20260912`, the corpus's own integer.
"""

import os
import sys
import time
import random

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank as rank_exact                        # noqa: E402
from bimage import (dim, span, isect, klein, klein_perp,        # noqa: E402
                    rho_bar_of, is_decomposable)
from bdecor import sample_by_branches                           # noqa: E402
import bunif                                                    # noqa: E402
import bgoodempty as BG                                         # noqa: E402
import bsixteen as BS                                           # noqa: E402
import bgplaw as BGP                                            # noqa: E402

SEED = BS.SEED                  # 20260912
SUBS = BS.SUBS
DIMV = BS.DIMV

# the two blocks the residue sits at, and their x/y mirror pairing
SURV = (tuple(sorted(('L', 'M', 'Pix'))), tuple(sorted(('L', 'M', 'Piy'))))
PERP_OF = {SURV[0]: 'Pix', SURV[1]: 'Piy'}


def nested_value(m, S, rho):
    """`min(rho_i, B(m,U))` -- the dimension `dim(rho_bar_i cap <P_0> cap U)`
    takes IFF one of the two spaces contains the other.  Both sit inside
    `<P_0>`, so `dim(A cap B) = min(dim A, dim B)` iff nested."""
    return min(rho, BS.Bbound(m, S))


# ================================================= mode: arith   (draw-free)

def run_arith(dmax=7):
    """THE QUESTION, ANSWERED FROM THE TARGET LIST ITSELF.

    CAP: `dmax=7` is `bsixteen.run_arith`'s own; the `>= dmax` class is the
    `dmax` cell, so the cap is not a truncation.  Seedless, draw-free."""
    t0 = time.time()
    print('== arith: nestedness at the two surviving profiles, draw-free, '
          'seedless')
    print(f'   CAP: dmax={dmax} (bsixteen.run_arith\'s own).  No sampling: '
          f'every figure below is')
    print('   an enumeration over `bsixteen._tuples`.')
    per = BGP.run_targets(dmax)          # the landed target list, recomputed
    print('   ---- BNEST from here ----')
    assert len(per) == 32, ('the target list is not 32 -- BGPLAW\'s (BE-301)'
                            '(i) figure moved', len(per))

    nested, nonnested = [], []
    for (S, m, r, c) in sorted(per, key=lambda k: (k[1], BS.label(k[0]),
                                                   k[2], k[3])):
        (nested if c == nested_value(m, S, r) else nonnested).append(
            (S, m, r, c))
    print(f'   THE NESTED EXTREME `c_i = min(rho_i, B(m,U))` holds at '
          f'{len(nested)} of {len(per)} targets.')
    print(f'   THE {len(nonnested)} TARGETS AT WHICH IT DOES NOT -- the '
          f'survivors of a "never nested" lemma:')
    for (S, m, r, c) in nonnested:
        print(f'       m={m}  {BS.label(S):<12} rho={r}  c={c}   '
              f'nested extreme would be {nested_value(m, S, r)}   '
              f'LG allows {BGP.lg_rhs(S, m, r)}')
    assert len(nonnested) == 2, ('not exactly two non-nested targets',
                                 nonnested)
    assert {S for (S, m, r, c) in nonnested} == set(SURV), \
        ('the two non-nested targets are not at L+M+Pi_x / L+M+Pi_y',
         nonnested)
    for (S, m, r, c) in nonnested:
        assert (m, r, c) == (5, 3, 2), ('a survivor is not (m,rho,c)='
                                        '(5,3,2)', S, m, r, c)

    print('   ANSWER TO THE DISPATCH QUESTION, and it is ARITHMETIC, not '
          'geometric:')
    print('   at each surviving target `c_i = 2` and `min(rho_i, B) = 3`, '
          'so `rho_bar_i` and')
    print('   `<P_0> cap U` are NOT nested THERE BY THE PROFILE\'S OWN '
          '`c_i`.  A lemma')
    print('   "never nested" is SATISFIED at both survivors and therefore '
          'excludes NEITHER.')
    print('   The two are exactly the residue of that lemma; they cannot '
          'also be its targets.')

    # the region reading: drop `c` and ask what nestedness WOULD be
    print('   THE REGION READING (drop `c_i`, keep `(U, dim<P_0>, rho_i)`).  '
          'At `rho_i = 3` and')
    print('   `B(5, L+M+Pi_x) = 3` both spaces are 3-dimensional, so nested '
          '<=> EQUAL <=> `c_i = 3`:')
    for S in SURV:
        tg = sorted((m, r, c) for (T, m, r, c) in per if T == S)
        print(f'       {BS.label(S):<12} targets {tg}')
        assert (5, 3, 3) in tg and (5, 3, 2) in tg, \
            ('the region does not carry both a nested and a non-nested '
             'target', S, tg)
    print('   so a draw with `c_i = 3` in the region IS a nested '
          'configuration and IS a')
    print('   (BLOCK-GP) violation -- but it is one of the 30 the lemma '
          'already kills, and the')
    print('   TWO SURVIVORS ARE AT `c_i = 2`, WHICH THE TELL CANNOT SEE.')

    # what the floor contributes at each target
    print('   WHAT THE FLOOR `f(U)` CONTRIBUTES, per target '
          '(`LG = max(f, rho+B-m)`):')
    tie = flo = gp = 0
    for (S, m, r, c) in sorted(per, key=lambda k: (k[1], BS.label(k[0]),
                                                   k[2], k[3])):
        f, z = BS.forced(S), r + BS.Bbound(m, S) - m
        if f > z:
            flo += 1
        elif f == z:
            tie += 1
        else:
            gp += 1
    print(f'       floor STRICTLY above the general-position term at {flo} '
          f'targets, EQUAL at {tie},')
    print(f'       strictly below at {gp}.')
    for (S, m, r, c) in nonnested:
        f, z = BS.forced(S), r + BS.Bbound(m, S) - m
        assert f == z == 1, ('the floor does not tie the gp term at a '
                             'survivor', S, m, r, f, z)
    print('   AT BOTH SURVIVORS `f(U) = rho_i + B(m,U) - m = 1`, so '
          '(BLOCK-GP)\'s floor contributes')
    print('   NOTHING there: the residue statement is `c_i <= 1`, which is '
          'the UNFLOORED law L7')
    print('   / (BE-294)(iv)\'s `gpP` at that cell, not a floored one.')

    # why THIS block, and not another: the characterization
    print('   WHY `L+M+Pi_x` AND NO OTHER BLOCK.  A target is non-nested '
          'iff `c_i < min(rho_i, B)`;')
    print('   a profile is a target iff `c_i > max(f, rho_i+B-m)`.  Both '
          'at once needs')
    print('   `max(f, rho_i+B-m) + 1 < min(rho_i, B)`, i.e. a GAP of at '
          'least 2 between the')
    print('   allowance and the nested extreme.  The residue lives at '
          '`dim<P_0> <= 5` on both')
    print('   sides ((BE-280)(iv)), so the sweep below runs `m = 2..5`; the '
          '`m = 6` cells are')
    print('   listed after it and are NOT targets, because L6 pins `c_i` '
          'to the general-position')
    print('   value exactly once the confinement is vacuous.  Over all 14 '
          'non-trivial blocks:')
    gap2, gap6 = [], []
    for S in SUBS:
        if S in BS.DEAD:
            continue
        for m in range(2, DIMV + 1):
            for r in range(0, min(m, DIMV) + 1):
                a, n = BGP.lg_rhs(S, m, r), nested_value(m, S, r)
                if n - a >= 2:
                    (gap6 if m >= DIMV else gap2).append(
                        (BS.label(S), m, r, a, n))
    for g in gap2:
        print(f'       {g[0]:<16} m={g[1]} rho={g[2]}   allows {g[3]}   '
              f'nested extreme {g[4]}')
    assert gap2, 'no cell has a gap of 2'
    assert {g[0] for g in gap2} == {'L+M+Pix', 'L+M+Piy'}, \
        ('the gap-2 cells at m <= 5 are not confined to the survivor '
         'blocks', gap2)
    assert {(g[1], g[2]) for g in gap2} == {(5, 3)}, \
        ('a gap-2 cell at m <= 5 outside (m, rho) = (5, 3)', gap2)
    print(f'   -- and ONLY THERE: {len(gap2)} cells at `m <= 5`, both at '
          f'`(m, rho_i) = (5, 3)`.')
    print(f'   (At `m = 6` the gap reaches 2 at {len(gap6)} further cells '
          f'-- {sorted({g[0] for g in gap6})} --')
    print('   none of which is a target, because `dim<P_0> = 6` makes the '
          'confinement vacuous and')
    print('   L6 pins `c_i` to the general-position value; (BE-280)(iv) '
          'reports the same fact as')
    print('   "every +L6 survivor has `m_i <= 5` on BOTH sides".  This '
          'assert refuted a draft of')
    print('   this clause that omitted the `m <= 5` restriction.)')
    print('   The mechanism is a FLOOR/DIMENSION ASYMMETRY, not '
          'superadditivity:')
    print('   `L+M+Pi_x` is the unique block (up to the x<->y mirror) that '
          'is 4-DIMENSIONAL --')
    print('   so `B(5,U) = 3` is large enough for `min(rho_i, B) = 3` at '
          '`rho_i = 3` -- while')
    print('   containing only ONE end pencil, so `f(U) = 1` keeps the '
          'allowance at 1.  The other')
    print('   4-dimensional block `Pi_x+Pi_y` has `f = 2`, which raises the '
          'allowance to 2 and')
    print('   makes `c_i = 2` LEGAL there; the 3-dimensional blocks have '
          '`B(5,U) = 2`, which drops')
    print('   the nested extreme to 2 and makes `c_i = 2` NESTED there.  '
          'Printed above, not argued.')
    for S in SUBS:
        if S in BS.DEAD:
            continue
        if BS.dU(S) == 4 and BS.forced(S) == 1:
            assert S in SURV, ('a 4-dim f=1 block outside the survivor '
                               'pair', S)
    print(f'   [{time.time() - t0:.1f}s]')
    return per, nonnested


# ================================================= mode: perp   (exact Q)

def _region_row(E, x, y, pt, fr, cap, maxlen):
    """`(dim<P_0>, rho, {S: c}, {S: dim(Pi cap rho_bar^perp)})` plus the
    asserts that make the identity a measurement rather than a recall."""
    st = BGP.side_stats(E, pt, x, y, fr, cap, maxlen)
    if st is None:
        return None
    dd, rho, dp, c, cp = st
    B = BS.blocks(fr)
    Srho, rho2, _dM, _r = rho_bar_of(E, pt, x, y)
    assert rho2 == rho, ('rho disagrees between two reads', rho, rho2)
    assert dim(Srho) == rho, ('rho_bar has the wrong dimension', rho)
    # `klein_perp([])` is the whole of Lambda^2 K^4, which is the right
    # answer at `rho_i = 0`; guarding it with `if Srho` made `k = 0` where
    # it must be `2`, and the identity assert below caught it on the first
    # run.  Recorded because the guard looked harmless.
    ann = klein_perp(Srho)
    kdim = {}
    for S in SURV:
        blk = PERP_OF[S]
        Pi = B[blk]
        assert dim(Pi) == 2, ('the end pencil is not 2-dimensional', blk)
        # (1) the block IS the Klein perp of the pencil
        U = BS.usub(B, S)
        assert dim(U) == 4, ('L+M+Pi is not 4-dimensional', S)
        Pp = klein_perp(Pi)
        assert dim(Pp) == 4 and dim(span(list(U) + list(Pp))) == 4, \
            ('L+M+Pi is NOT the Klein perp of Pi', S)
        # (2) the pencil is totally singular -- why (1) can hold at all
        assert all(klein(a, b) == 0 for a in Pi for b in Pi), \
            ('the end pencil is not totally singular', blk)
        assert all(is_decomposable(a) for a in Pi), \
            ('a basis vector of the end pencil is not a line', blk)
        # (3) the rank identity
        rk = rank_exact([[klein(a, u) for u in Pi] for a in Srho]) \
            if Srho else 0
        k = dim(isect(ann, Pi)) if ann else 0
        assert rk == 2 - k, ('the two rank readings disagree', rk, k)
        assert c[S] == rho - rk, ('THE PERP IDENTITY FAILS', S, c[S], rho,
                                  rk)
        kdim[S] = k
    return dp, rho, c, cp, kdim


def run_perp(ndraw=3, seed=SEED, maxarc=8, maxtheta=7, cap=400, maxlen=9,
             nlad=40):
    """`c_i(L+M+Pi_x) = rho_i - 2 + dim(Pi_x cap rho_bar_i^perp)`, asserted
    at every draw, and the region's own distribution.

    CAPS: ndraw={ndraw} (`run_side` fences to 2, `run_pix` to 3 -- this is
    `run_pix`'s and BGPLAW `reach`'s value); maxarc={maxarc},
    maxtheta={maxtheta}, nlad={nlad} (`run_side`'s committed values);
    `xy_paths(cap={cap}, maxlen={maxlen})`; ONE shortest path per side,
    so `dim<P_0>` is an upper bound on the intersected confinement.
    F27: `c_i` is UPPER semicontinuous, so a draw is an UPPER bound on the
    generic value -- a draw OBEYING an upper-bound law is conservative
    evidence, a draw VIOLATING one is a proof."""
    t0 = time.time()
    print(f'== perp: the Klein identity at the survivor blocks.  seed '
          f'{seed}, exact Q')
    print(f'   CAPS: ndraw={ndraw} (run_side 2, run_pix 3), maxarc={maxarc},'
          f' maxtheta={maxtheta}, nlad={nlad},')
    print(f'   xy_paths(cap={cap}, maxlen={maxlen}); ONE shortest path per '
          f'side.')
    print('   F27: every `c_i` below is an UPPER bound on the generic '
          'value at its row.')
    lib = list(BG.side_library(maxarc, maxtheta, nlad, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in BG.side1_library()]
    rows = ndr = 0
    joint = {}          # (S, dp, rho) -> {(c, k): count}
    region = {}         # (S,) -> {c: count} at dp=5, rho=3
    viol = []
    for (tag, E, x, y) in lib:
        seen = 0
        for k in range(ndraw):
            rng = random.Random(seed + 733 * k + len(E))
            got = sample_by_branches(E, x, y, rng)
            if got is None:
                continue
            pt = got[0]
            fr = bunif.flag_frame(E, pt, x, y)
            if fr is None:
                continue
            try:
                r = _region_row(E, x, y, pt, fr, cap, maxlen)
            except AssertionError:
                raise
            if r is None:
                continue
            dp, rho, c, cp, kdim = r
            seen += 1
            ndr += 1
            for S in SURV:
                joint.setdefault((S, dp, rho), {})
                key = (c[S], kdim[S])
                joint[(S, dp, rho)][key] = joint[(S, dp, rho)].get(key, 0) + 1
                if c[S] > BGP.lg_rhs_measured(S, rho, cp[S], dp):
                    viol.append((tag, BS.label(S), dp, rho, c[S], cp[S]))
                if (dp, rho) == (5, 3):
                    region.setdefault(S, {})
                    region[S][c[S]] = region[S].get(c[S], 0) + 1
        if seen:
            rows += 1
    print(f'   library rows with a generic-regime draw {rows}; draws {ndr}.')
    print('   ASSERTED at every draw, 0 failures (an AssertionError would '
          'have stopped the run):')
    print('     * `Pi_x` totally singular and spanned by LINES;')
    print('     * `L+M+Pi_x` = `Pi_x^perp` as SPACES (not as dimensions);')
    print('     * `rank K(rho_bar_i, Pi_x) = 2 - dim(Pi_x cap '
          'rho_bar_i^perp)`;')
    print('     * `c_i(L+M+Pi_x) = rho_i - rank K(rho_bar_i, Pi_x)`.')
    print('   THE JOINT `(dim<P_0>, rho_i) -> {(c_i, dim(Pi cap '
          'rho_bar^perp)): count}` at `L+M+Pi_x`:')
    S0 = SURV[0]
    for key in sorted(k for k in joint if k[0] == S0):
        print(f'       dim<P_0>={key[1]} rho={key[2]}   '
              f'{dict(sorted(joint[key].items()))}')
    print('   THE QUESTION\'S REGION `dim<P_0>=5, rho_i=3`:')
    for S in SURV:
        h = region.get(S)
        print(f'       {BS.label(S):<12} observed c_i {dict(sorted(h.items()))}'
              if h else
              f'       {BS.label(S):<12} NOT REACHED UNDER CAP C')
    print(f'   (BLOCK-GP) violations at the two survivor blocks, '
          f'`dim(<P_0> cap U)` MEASURED per cell: {len(viol)}')
    for v in viol[:20]:
        print(f'       {v}')
    print(f'   [{time.time() - t0:.1f}s]')
    return rows, ndr, joint, region, viol


# ================================================= mode: fifth  (the probe)

def run_fifth(ndraw=3, seed=SEED, maxlen=4, nsamp=12, cap=400, pmaxlen=9,
              dmin=3, distmin=5, rowcap=400):
    """THE FIFTH SIDE FAMILY, which (BE-302)(iii) names as the cheapest
    unspent probe and which BGPLAW did not run: `bgoodempty.skeleton_pairs`,
    scored against the 32 printed targets exactly as `bgplaw.run_reach`
    scores the other four.

    CAPS: `skeleton_pairs(maxlen={maxlen}, nsamp={nsamp})` -- `nsamp` is
    FENCED below its own default (120) because `K4` alone enumerates
    `maxlen^6` profiles at 6 vertex pairs each; rows are then filtered to
    `delta_xy >= {dmin}` and `dist >= {distmin}` (both DERIVED from the two
    surviving targets, see `run_delta`) and capped at {rowcap};
    ndraw={ndraw};
    `xy_paths(cap={cap}, maxlen={pmaxlen})`; ONE shortest path per side.
    A miss here is NOT FOUND UNDER CAP C, never an absence."""
    t0 = time.time()
    print(f'== fifth: `bgoodempty.skeleton_pairs` against the 32 targets.  '
          f'seed {seed}, exact Q')
    print(f'   CAPS: skeleton_pairs(maxlen={maxlen}, nsamp={nsamp}) -- '
          f'`maxlen` AT its own default (4),')
    print(f'   `nsamp` FENCED below its own (120);')
    print(f'   ndraw={ndraw}; xy_paths(cap={cap}, maxlen={pmaxlen}); ONE '
          f'shortest path per side.')
    lib0 = list(BG.skeleton_pairs(maxlen, nsamp, seed))
    lib = []
    for (tag, E, x, y) in lib0:
        dd = BG.dist_of(E, x, y)
        if dd is None or dd < distmin:
            continue
        if BG.delta_of(E, x, y) < dmin:
            continue
        lib.append((tag, E, x, y))
    print(f'   library rows offered {len(lib0)}; ELIGIBLE after the '
          f'`delta >= {dmin}`, `dist >= {distmin}` filter: {len(lib)}')
    print(f'   (the filter is DERIVED, not chosen: the two surviving '
          f'targets need `rho_i = 3` and')
    print(f'   `dim<P_0> = 5`, and `rho_i <= delta_i + a_i`, '
          f'`dim<P_0> <= dist`.)  ROW CAP {rowcap}.')
    if len(lib) > rowcap:
        rng0 = random.Random(seed + 11)
        lib = rng0.sample(lib, rowcap)
        print(f'   row cap applied: {rowcap} rows sampled, seeded.')
    rows = ndr = 0
    mrho, cbym = {}, {}
    viol = []
    for (tag, E, x, y) in lib:
        if BG.dist_of(E, x, y) is None:
            continue
        seen = 0
        for k in range(ndraw):
            rng = random.Random(seed + 733 * k + len(E))
            got = sample_by_branches(E, x, y, rng)
            if got is None:
                continue
            pt = got[0]
            fr = bunif.flag_frame(E, pt, x, y)
            if fr is None:
                continue
            try:
                st = BGP.side_stats(E, pt, x, y, fr, cap, pmaxlen)
            except AssertionError:
                st = None
            if st is None:
                continue
            dd, rho, dp, c, cp = st
            seen += 1
            ndr += 1
            mrho[(dp, rho)] = mrho.get((dp, rho), 0) + 1
            for S in SUBS:
                if S in BS.DEAD:
                    continue
                cbym.setdefault((S, dp, rho), {})
                cbym[(S, dp, rho)][c[S]] = \
                    cbym[(S, dp, rho)].get(c[S], 0) + 1
                if c[S] > BGP.lg_rhs_measured(S, rho, cp[S], dp):
                    viol.append((tag, BS.label(S), dp, rho, c[S], cp[S]))
        if seen:
            rows += 1
    print(f'   rows with a generic-regime draw {rows}; draws {ndr}.')
    print(f'   THE `(dim<P_0>, rho_i)` SUPPORT: '
          f'{dict(sorted(mrho.items()))}')
    tg = _targets(7)
    hit = [k for k in tg if k[3] in cbym.get((k[0], k[1], k[2]), {})]
    print(f'   TARGET PROFILES REACHED: {len(hit)} of {len(tg)}.')
    for k in sorted(hit, key=lambda k: (k[1], BS.label(k[0]), k[2], k[3])):
        print(f'       m={k[1]} {BS.label(k[0]):<16} rho={k[2]} c={k[3]}   '
              f'observed {dict(sorted(cbym[(k[0], k[1], k[2])].items()))}')
    print('   THE SURVIVOR REGION `L+M+Pi_x / L+M+Pi_y` at '
          '`dim<P_0>=5, rho_i=3`:')
    for S in SURV:
        h = cbym.get((S, 5, 3))
        print(f'       {BS.label(S):<12} '
              f'{dict(sorted(h.items())) if h else "NOT FOUND UNDER CAP C"}')
    print(f'   (BLOCK-GP) violations, measured `dim(<P_0> cap U)`: '
          f'{len(viol)}')
    for v in viol[:20]:
        print(f'       {v}')
    print(f'   [{time.time() - t0:.1f}s]')
    return rows, ndr, mrho, cbym, viol


def run_delta(maxlen=4, nsamp=12, seed=SEED):
    """WHY the fifth family misses: a DRAW-FREE census of `delta_{xy}` over
    `bgoodempty.skeleton_pairs`.  `rho_i <= delta_i` ((BE-22)(ii) at
    `a_i = 0`, and unconditionally `rho_i <= delta_i + a_i`), so a family
    with `delta = 0` everywhere cannot reach a target at any `rho_i >= 1`,
    at any number of draws.  This is a combinatorial statement and carries
    no configuration cap -- only the generator fence below.

    CAPS: `skeleton_pairs(maxlen={maxlen}, nsamp={nsamp})`; `delta_of` is
    `bgoodempty`'s own landed oracle (`d3 - weld_d3`)."""
    t0 = time.time()
    print(f'== delta: draw-free `delta_xy` census over skeleton_pairs.  '
          f'seed {seed}')
    print(f'   CAPS: skeleton_pairs(maxlen={maxlen}, nsamp={nsamp}); '
          f'`bgoodempty.delta_of`, no draws.')
    hist, per_len = {}, {}
    n = 0
    for (tag, E, x, y) in BG.skeleton_pairs(maxlen, nsamp, seed):
        if BG.dist_of(E, x, y) is None:
            continue
        d = BG.delta_of(E, x, y)
        hist[d] = hist.get(d, 0) + 1
        nm = tag.split('(')[0]
        per_len.setdefault(nm, {})
        per_len[nm][d] = per_len[nm].get(d, 0) + 1
        n += 1
    print(f'   rows {n}.  `delta_xy` histogram: {dict(sorted(hist.items()))}')
    for nm in sorted(per_len):
        print(f'       {nm:<10} {dict(sorted(per_len[nm].items()))}')
    mx = max(hist)
    print(f'   MAX `delta_xy` over the family: {mx}.  Since `rho_i <= '
          f'delta_i + a_i` and the')
    print(f'   targets need `rho_i >= 2`, the family reaches a target only '
          f'if `delta_i + a_i >= 2`.')
    print(f'   [{time.time() - t0:.1f}s]')
    return hist, per_len


def _targets(dmax=7):
    """The 32 target profiles, recomputed silently from `bgplaw`'s own
    enumeration (its `run_targets` prints; this does not)."""
    per = {}
    base = list(BS._tuples(dmax))
    for S in SUBS:
        if S in BS.DEAD:
            continue
        d = BS.dU(S)
        for (d1, d2, t1, t2, r1, r2) in base:
            m1, m2 = min(t1, DIMV), min(t2, DIMV)
            for c1 in range(0, min(r1, d) + 1):
                for c2 in range(0, min(r2, d) + 1):
                    if c1 + c2 <= d:
                        continue
                    if c1 > BS.Bbound(m1, S) or c2 > BS.Bbound(m2, S):
                        continue
                    g6 = [max(0, r1 + d - DIMV), max(0, r2 + d - DIMV)]
                    if (t1 >= DIMV and c1 != g6[0]) or \
                       (t2 >= DIMV and c2 != g6[1]):
                        continue
                    for (m, c, r) in ((m1, c1, r1), (m2, c2, r2)):
                        if c > BGP.lg_rhs(S, m, r):
                            per[(S, m, r, c)] = per.get((S, m, r, c), 0) + 1
    return per


def run_validate():
    print('== validate: arith + reduced perp + reduced fifth')
    print('   FENCED: perp(ndraw=1, maxarc=4, maxtheta=4, nlad=6) against '
          '3/8/7/40;')
    print('   fifth(maxlen=2, nsamp=4) against its own 2/12.  arith is '
          'draw-free at full default.')
    run_arith()
    run_perp(ndraw=1, maxarc=4, maxtheta=4, nlad=6)
    run_fifth(nsamp=4)
    run_delta(maxlen=2, nsamp=4)


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode == 'arith':
        run_arith()
    elif mode == 'perp':
        run_perp()
    elif mode == 'fifth':
        run_fifth()
    elif mode == 'delta':
        run_delta()
    elif mode == 'wide':
        # the same probe with the filter RELAXED to the m=4 targets'
        # requirements (`rho_i >= 2`, `dist >= 4`); a committed entry point,
        # so the figure is reproducible in one command.
        run_fifth(dmin=2, distmin=4, rowcap=200)
    elif mode == 'validate':
        run_validate()
    else:
        print(f'unknown mode {mode!r}')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
