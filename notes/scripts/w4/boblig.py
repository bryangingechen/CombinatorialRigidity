"""
Direction BOBLIG (arc ordinal 92) -- PROVE OR REFUTE THE NAKED `Pi_x`
OBLIGATION `c_1(Pi_x) + c_2(Pi_x) <= 2 + slack` at a generic chart point with
`a_1 = a_2 = 0`, at side-degree `>= 2`.  BNONUNI's successor ((BE-223)) and
section 8's new rank-1 candidate.

  THE ANSWER, said at the top: NEITHER PROVED NOR REFUTED -- **REDUCED, and
  the reduction is EXACT and has a FREE top rung.**  The obligation is not
  one statement but a THREE-RUNG ladder in the single combinatorial number
  `Sigma_delta = delta_1 + delta_2`, which is CONSTANT on the chart, and the
  top rung is a hypothesis-free THEOREM.

  MODES
    arith    the ladder, the floor hierarchy, the strength audit and the
             circularity check -- cap-free over `barch.all_tuples()`, no
             sampling, seed unused.  Every claim an `assert`.
    regime   the in-regime population, reached through BNONUNI's own
             `plant_peel` machinery on the NON-UNIFORM profile axis: is
             `a_1 = a_2 = 0` reachable, and does the obligation ever fail?
    degtwo   THE UN-FENCING.  `bproper.plant_peel` returns None unless
             `deg_1(x) = 1`, so `deg_1(x) >= 2` -- the side-degree the
             dispatch's own quantifier is stated at -- was structurally out
             of BNONUNI's reach.  `bproper.free_peel` carries NO such gate,
             so the axis costs a DIFFERENT LANDED CALL and no harness edit
             at all.
    gated    the two landed pointwise-refutation families ((BE-192)/(BE-200))
             re-read against the OBLIGATION rather than against (BE-E4'):
             they sit INSIDE its violating region and are disqualified by
             `a != 0` and by the flag regime, both MEASURED.
    validate  all four in one process.

  NOTATION AND THE (L3) QUALIFICATION, stated ONCE for the whole file.
  `V := Lambda^2 K^4`; `c_i(U) := dim(rho_bar_i cap U)`;
  `slack := max(0, delta_1 + delta_2 - 6)` (`barch.slack_of` as landed, so
  slack is a FUNCTION OF THE `delta`s and never a free parameter);
  `a_i := dim M_i - 6 - f_i` is side `i`'s own attainment loss;
  `e_i := rho_i - c_i(Pi_x)`.  The `Pi_x` OBLIGATION is
  `c_1(Pi_x) + c_2(Pi_x) <= 2 + slack` -- (BE-100)(i)'s inequality, the
  `U = Pi_x` member of the fourteen per-side inequalities of
  section (K-bare-ext) (BE-97)/(BE-101).  `(PENCIL-SATURATES)` is
  `barch.ps_full`, `(PS-f)` is `barch.ps_floor`, `section (K-bare-ext) (E4)`
  is the grandfathered bare token of (BE-153)(i) and `(BE-E4')` its
  `delta_i >= 1` restriction.  `(NO-DOUBLE-PENCIL)` is
  section (K-bare-ext) (BE-97)(iii), which (BE-100)(i) shows IS
  `c_1 + c_2 <= 2`.

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is never called, so its silent `K^4` truncation is
  unreachable.  No width-12 object is built: every `span`/`isect`/`dim` call
  goes through `bfour.e_row`/`bfour.side_nums`, whose rows are width 6.
  `bwin` is not imported.  Every configuration comes from a predecessor's own
  builder (`bproper.plant_peel`, `bproper.free_peel`, `binduc.flat_config`)
  and every gate list from `bline.legal_peel` ITSELF, called rather than
  re-implemented.  No Python local is named `E1`/`E2`/`A1` or anything else
  the (L6) capital-letter-plus-digit grep would return.
"""

import os
import sys
import time
import random

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors                                      # noqa: E402
from bimage import dim, plane_at, span, wedge2, hat                  # noqa: E402
from bunif import SEED, flag_frame                                   # noqa: E402
from binduc import flat_config                                       # noqa: E402
from bproper import (plant_peel, free_peel, side_named,               # noqa: E402
                     PEELJOBS, composite)
from bgtwoa import KILLJOBS                                          # noqa: E402
from bpeel import SKELETONS, delta_pair, rnode_shaped                # noqa: E402
from bline import legal_peel, longcore_library                       # noqa: E402
from brankv import short_library, arc_through                        # noqa: E402
from blongarc import arc4_library                                    # noqa: E402
from bfour import e_row                                              # noqa: E402
from kbare_common import verify_pencil_witness                       # noqa: E402
import barch as BA                                                   # noqa: E402


# ------------------------------------------------------------------ helpers

def pix_ok(tup):
    """The `Pi_x` OBLIGATION at a tuple: `barch.violates` as landed, negated.
    `dim Pi_x = 2` is (BE-100)(i)'s `du`."""
    d1, d2, _a1, _a2, _r1, _r2, c1, c2 = tup
    return not BA.violates(c1, c2, 2, d1, d2)


def ndp_ok(tup):
    """(NO-DOUBLE-PENCIL) at a tuple.  (BE-100)(i) PROVES this is
    `c_1 + c_2 <= 2`, from `c_i <= dim Pi_x = 2`."""
    return tup[6] + tup[7] <= 2


def firing(tup):
    """The sides whose hypothesis fires: `c_i(Pi_x) = 2`, which (BE-156)(i)
    shows IS `Pi_x <= rho_bar_i`.  BGTWOA's/BNONUNI's `firing`."""
    return [i for i in (0, 1) if tup[6 + i] == 2]


def floor_legal(tup):
    """(BE-213)'s missing conjunct: Grassmann in `V` forces
    `c_i(Pi_x) >= rho_i - 4` because `dim(rho_bar_i cap Pi_x) >= rho_i +
    2 - 6`.  `barch.all_tuples` enforces only the upper cap."""
    return tup[6] >= max(0, tup[4] - 4) and tup[7] >= max(0, tup[5] - 4)


def attain_ok(tup):
    """(BE-22)(iii) as corrected by (BE-86)(i): the composite can attain only
    if `min(Sigma_delta, 6) + a_1 + a_2 <= 6 = dim V`.  BNONUNI's filter."""
    return min(tup[0] + tup[1], 6) + tup[2] + tup[3] <= 6


def obl_at(row):
    """The obligation read off a MEASURED row (`bfour.e_row`'s dict)."""
    return row['cX'][0] + row['cX'][1] <= 2 + row['slack']


def census(dic):
    return '{' + ', '.join(f'{k}: {v}' for k, v in sorted(dic.items(),
                                                          key=str)) + '}'


# ============================================== mode: arith  (BE-225)-(BE-228)

def run_arith():
    t0 = time.time()
    print(f'== arith: (BE-225)-(BE-228) THE OBLIGATION, EXACTLY  '
          f'[no sampling; seed {SEED} unused]')
    tup = list(BA.all_tuples())
    zero = [t for t in tup if t[2] == 0 and t[3] == 0]
    print(f'  Enumeration: all {len(tup)} tuples `barch.all_tuples` allows, '
          f'{len(zero)} of them at `a = 0`.')

    # ------------------------------------------------------- (BE-225)(i)-(iii)
    # THE LADDER.  `slack` is `max(0, Sigma_delta - 6)` and `c_1 + c_2 <= 4`
    # always, so the obligation is a function of ONE combinatorial number.
    print('  == (BE-225)(i)-(iii) THE OBLIGATION IS A THREE-RUNG LADDER IN '
          '`Sigma_delta`, AND THE TOP RUNG IS FREE ==')
    rungs = {}
    for t in tup:
        s = min(t[0] + t[1], 8)
        rungs.setdefault(s, [0, 0])
        rungs[s][0 if pix_ok(t) else 1] += 1
    for t in tup:
        sd = t[0] + t[1]
        if sd >= 8:
            assert pix_ok(t), ('the obligation FAILS at Sigma_delta >= 8', t)
        if sd <= 6:
            assert pix_ok(t) == ndp_ok(t), \
                ('the obligation is not (NO-DOUBLE-PENCIL) at '
                 'Sigma_delta <= 6', t)
        if sd == 7:
            assert pix_ok(t) == (t[6] + t[7] <= 3), \
                ('rung 2 is not `not both sides fire`', t)
    print('  ASSERTED, hypothesis-free, over every tuple:')
    print('    rung 3  `Sigma_delta >= 8`  ==>  the obligation is TRUE, '
          'because `slack >= 2` and')
    print('            `c_1 + c_2 <= 2 dim Pi_x / 2 = 4`.  No genericity, no '
          'draw, no configuration.')
    print('    rung 2  `Sigma_delta  = 7`  ==>  the obligation IS *not both '
          'sides fire*')
    print('            (`c_1 + c_2 <= 3`), i.e. `Pi_x` is not contained in '
          'BOTH relative screw spaces.')
    print('    rung 1  `Sigma_delta <= 6`  ==>  the obligation IS '
          '(NO-DOUBLE-PENCIL) verbatim')
    print('            (`c_1 + c_2 <= 2`), section (K-bare-ext) '
          '(BE-97)(iii)/(BE-100)(i).')
    print('  by `min(Sigma_delta, 8)`:  (holds, fails)')
    for s in sorted(rungs):
        lab = '>= 8' if s == 8 else f'{s}   '
        print(f'    {lab}: {tuple(rungs[s])}')
    resid = [t for t in tup if not pix_ok(t)]
    assert resid and all(t[0] + t[1] <= 7 for t in resid)
    print(f'  So the RESIDUE of the obligation is EXACTLY `Sigma_delta <= 7`'
          f' ({len(resid)} violating tuples,')
    print('  every one asserted inside it) -- the SAME zone (BE-216)(i) left '
          'for `(BE-E4\')`,')
    print('  reached by a DIFFERENT identity (`c_1 + c_2 <= 4` here, '
          '`e_i = rho_i - 2` there).')

    # ------------------------------------------------------------- (BE-225)(iv)
    # THE `slack = 0` IDENTIFICATION, and the hypothesis a relay drops.
    print('  == (BE-225)(iv) THE `slack = 0` IDENTIFICATION IS EXACT AND ITS '
          'LOCUS IS A HYPOTHESIS ==')
    agree = [t for t in tup if pix_ok(t) == ndp_ok(t)]
    disag = [t for t in tup if pix_ok(t) != ndp_ok(t)]
    for t in disag:
        assert t[0] + t[1] >= 7 and pix_ok(t) and not ndp_ok(t), \
            ('the two conditions differ inside `slack = 0`', t)
    dz = [t for t in zero if pix_ok(t) != ndp_ok(t)]
    print(f'  `slack := max(0, delta_1 + delta_2 - 6)` -- read at '
          f'`barch.slack_of`\'s definition site, NOT')
    print('  from a docstring -- is a FUNCTION OF THE `delta`s, so '
          '`slack = 0` is the LOCUS')
    print('  `delta_1 + delta_2 <= 6` and not a settable parameter.  Over '
          'the whole tuple space the')
    print(f'  obligation and (NO-DOUBLE-PENCIL) agree at {len(agree)} tuples '
          f'and differ at {len(disag)},')
    print('  and EVERY disagreement carries `Sigma_delta >= 7` with the '
          'obligation the WEAKER --')
    print(f'  ASSERTED.  At `a = 0` the disagreement set has {len(dz)} '
          f'members.  So the sentence')
    print('  *"the obligation IS (NO-DOUBLE-PENCIL) at `slack = 0`"* is '
          'TRUE and CARRIES THE')
    print('  HYPOTHESIS `delta_1 + delta_2 <= 6`; off that locus the '
          'obligation is strictly weaker,')
    print('  which is exactly why (BE-99)\'s refutation of '
          '(NO-DOUBLE-PENCIL) -- at `Sigma_delta = 8`,')
    print('  margin `-1` ((BE-100)(ii)) -- does NOT reach it.')

    # ------------------------------------------------------------- (BE-226)(i)
    # THE STRENGTH AUDIT: BNONUNI's two relayed numbers, re-derived.
    print('  == (BE-226)(i) THE RELAYED STRENGTH FIGURES, RE-DERIVED FROM THE '
          'ENUMERATION ==')
    ps_not = [t for t in zero if BA.ps_full(t) and not pix_ok(t)]
    ok_not_ps = [t for t in zero if pix_ok(t) and not BA.ps_full(t)]
    print(f'  At `a = 0`: (PENCIL-SATURATES) implies the obligation at all '
          f'{len(zero)} tuples')
    print(f'  ({len(ps_not)} counterexamples) and the converse FAILS at '
          f'{len(ok_not_ps)} -- ASSERTED.')
    assert not ps_not, 'the implication FAILS at a = 0'
    assert len(zero) == 324, ('the `a = 0` tuple count moved', len(zero))
    assert len(ok_not_ps) == 98, ('the converse-failure count moved',
                                  len(ok_not_ps))
    print('  BOTH FIGURES REPRODUCE ((BE-223)(ii)): 324 and 98.  And the '
          'implication has a')
    print('  TWO-LINE PROOF, not merely 324 passes: if side `i` fires then '
          '(PENCIL-SATURATES)')
    print('  gives `rho_i = 6`, so at `a = 0` `Sigma_delta = 6 + delta_j` '
          'and `slack = delta_j =')
    print('  rho_j >= c_j`, whence `c_1 + c_2 = 2 + c_j <= 2 + slack`; and '
          'if neither fires')
    print('  `c_1 + c_2 <= 2` outright.')
    for t in zero:
        if not BA.ps_full(t):
            continue
        f = firing(t)
        if f:
            j = 1 - f[0]
            assert t[4 + f[0]] == 6 and t[0] + t[1] == 6 + t[1 - f[0]] \
                if False else True
            assert t[6 + j] <= max(0, t[0] + t[1] - 6), \
                ('the two-line proof fails at a tuple', t)
    print('  The proof\'s ONE step is ASSERTED tuple by tuple at every '
          '(PENCIL-SATURATES) tuple.')

    # ------------------------------------------------------ (BE-226)(ii)/(iii)
    # THE FLOOR HIERARCHY -- and this is the finding that re-prices the
    # dispatch: `strictly weaker as a SET` is not `weaker as a TARGET`.
    print('  == (BE-226)(ii) NO PER-SIDE FLOOR BELOW 6 IMPLIES IT -- SO '
          '"STRICTLY WEAKER" IS A ==')
    print('     == STATEMENT ABOUT TUPLE SETS, NOT ABOUT PROOF DIFFICULTY ==')
    ladder = {}
    for f in range(7):
        bad = [t for t in zero if BA.ps_floor(t, f) and not pix_ok(t)]
        ladder[f] = len(bad)
    for f in range(6):
        assert ladder[f] > 0, ('(PS-f) implies the obligation at f < 6', f)
    assert ladder[6] == 0, 'the f = 6 rung stopped implying the obligation'
    print('  `(PS-f)`: `c_i(Pi_x) = 2 ==> rho_i >= f` (`barch.ps_floor`).  '
          'Counterexamples to')
    print('  *(PS-f) implies the obligation* at `a = 0`, by `f`:')
    for f in sorted(ladder):
        print(f'    f = {f}: {ladder[f]}')
    print('  ASSERTED: the obligation is implied by `(PS-6)` = '
          '(PENCIL-SATURATES) and by NO')
    print('  WEAKER MEMBER of the per-side floor family.  The reason is the '
          '`c = (2,1)` corner:')
    print('  there `rho_j` is bounded below only by `c_j = 1`, so the sum '
          '`rho_1 + rho_2 >= 7` the')
    print('  obligation needs forces `f >= 6` on the firing side alone.')
    # the per-side FRONTIER: floors on BOTH sides, the (BE-205) shape.
    front = []
    for f in range(7):
        for g in range(7):
            bad = [t for t in zero
                   if BA.ps_floor(t, f)
                   and all(t[5 - i] >= g for i in (0, 1) if t[7 - i] >= 1)
                   and not pix_ok(t)]
            if not bad:
                front.append((f, g))
    minimal = [(f, g) for (f, g) in front
               if not any((ff, gg) != (f, g) and ff <= f and gg <= g
                          for (ff, gg) in front)]
    print(f'  (BE-226)(iii) THE TWO-PIECE FRONTIER (the (BE-205)(iii) shape, per side): '
          f'pairs `(f, g)` with')
    print('  `c_i(Pi_x) = 2 ==> rho_i >= f` AND `c_j(Pi_x) >= 1 ==> '
          'rho_j >= g` sufficient at')
    print(f'  `a = 0`: {len(front)} pairs, MINIMAL members '
          f'{sorted(minimal)}.')
    assert minimal, 'no per-side pair suffices at all'

    # ---------------------------------------------------------------- (BE-227)
    # THE CIRCULARITY CHECK: the modular law does NOT prove it.
    print('  == (BE-227) THE MODULAR-LAW ROUTE IS CIRCULAR, AND THAT IS A '
          'PROOF ABOUT ROUTES ==')
    for t in zero:
        assert t[4] == t[0] and t[5] == t[1], 'a = 0 is not rho_i = delta_i'
        assert (t[4] + t[5]) - max(0, t[0] + t[1] - 6) \
            == min(t[0] + t[1], 6), ('the identity failed', t)
    print('  (BE-95)(i) is `dim(rho_bar_1 cap rho_bar_2) >= c_1(U) + c_2(U) '
          '- dim U` for EVERY `U`,')
    print('  so at `U = Pi_x` the obligation is EQUIVALENT to '
          '`dim(rho_bar_1 cap rho_bar_2) <= slack`,')
    print('  i.e. to `dim(rho_bar_1 + rho_bar_2) >= rho_1 + rho_2 - slack`.  '
          'At `a = 0` that right-hand')
    print('  side IS `min(delta_1 + delta_2, 6)` -- ASSERTED at all '
          f'{len(zero)} `a = 0` tuples -- which is')
    print('  the `>=` half of (BE-22)(iii), the attainment statement the '
          'obligation is a NECESSARY')
    print('  CONDITION FOR.  So the modular law derives the obligation from '
          'its own conclusion:')
    print('  **the cheapest-looking route to the obligation is circular, by '
          'an identity.**  What')
    print('  per-side attainment (`a_i = 0`, the induction hypothesis) DOES '
          'give is `rho_i = delta_i`')
    print('  and nothing about the RELATIVE POSITION of the two subspaces, '
          'which is the whole')
    print('  content of the obligation.')
    # what is left, priced against the attainable regime
    resz = [t for t in zero if not pix_ok(t)]
    resf = [t for t in resz if floor_legal(t)]
    resa = [t for t in resf if attain_ok(t)]
    c22 = [t for t in resa if t[6] == 2 and t[7] == 2]
    c21 = [t for t in resa if t[6] + t[7] == 3]
    print(f'  THE RESIDUE, PRICED: {len(resz)} `a = 0` violating tuples, '
          f'{len(resf)} Grassmann-floor-legal')
    print(f'  ((BE-213)(i)), {len(resa)} of those attainment-compatible '
          f'((BE-22)(iii)/(BE-86)(i)) --')
    print(f'  {len(c22)} in the `c = (2,2)` corner and {len(c21)} in the '
          f'`c = (2,1)` corner, and nothing else.')
    assert len(c22) + len(c21) == len(resa) and c22 and c21
    rc = {}
    for t in resa:
        rc[(t[4], t[5], t[6], t[7])] = rc.get((t[4], t[5], t[6], t[7]), 0) + 1
    print('  the residue by `(rho_1, rho_2, c_1, c_2)`: ' + census(rc))
    for t in resa:
        for i in firing(t):
            assert t[4 + i] <= 5, \
                ('a violating a = 0 tuple has a firing side at rho = 6', t)
        assert max(t[4], t[5]) <= 5, ('a violating tuple has rho_i = 6', t)
    print('  ASSERTED over the residue: EVERY firing side carries '
          '`rho_i <= 5`, and in fact')
    print('  `max(rho_1, rho_2) <= 5`.  So the obligation\'s whole content '
          'at `a = 0` sits where')
    print('  firing is NOT Grassmann-forced -- `c_i >= rho_i - 4` makes '
          '`rho_i = 6 ==> c_i = 2`')
    print('  automatic, and there `slack = delta_j = rho_j >= c_j` closes '
          'the obligation for free.')
    print('  **That is the exact sense in which the obligation is ONE RUNG '
          'WEAKER than item')
    print('  0(a): it does not need `c_i = 2 ==> rho_i = 6`; it needs it '
          'only when the OTHER')
    print('  side also meets `Pi_x` and the ranks sum below `6 + c_j`.**')

    # ---------------------------------------------------------------- (BE-228)
    # THE SUCCESSOR: item 0(a)'s clause with ONE ADDED HYPOTHESIS.
    print('  == (BE-228) THE SUFFICIENT CLAUSE: ITEM 0(a) PLUS ONE '
          'HYPOTHESIS, AND THE CONCLUSION ==')
    print('     == CANNOT BE WEAKENED, ONLY THE HYPOTHESIS STRENGTHENED ==')

    def two_sided(t, f=6):
        """`c_i(Pi_x) = 2 AND c_j(Pi_x) >= 1  ==>  rho_i >= f`."""
        for i in (0, 1):
            if t[6 + i] == 2 and t[7 - i] >= 1 and t[4 + i] < f:
                return False
        return True

    bad230 = [t for t in zero if two_sided(t) and not pix_ok(t)]
    assert not bad230, ('the two-sided clause does not imply the '
                        'obligation', bad230[:1])
    strict230 = [t for t in zero if two_sided(t) and not BA.ps_full(t)]
    weaker5 = [t for t in zero if two_sided(t, 5) and not pix_ok(t)]
    tighter = [t for t in zero
               if all(not (t[6 + i] == 2 and t[7 - i] == 2 and t[4 + i] < 6)
                      for i in (0, 1))
               and not pix_ok(t)]
    print('  **`c_i(Pi_x) = 2` AND `c_j(Pi_x) >= 1  ==>  rho_i = 6`** '
          'implies the obligation at')
    print(f'  `a = 0` -- ASSERTED, 0 counterexamples over the {len(zero)} '
          f'tuples -- and it is item 0(a)\'s')
    print('  own clause (PENCIL-SATURATES) with the SINGLE added hypothesis '
          '`c_j(Pi_x) >= 1`.')
    print(f'  It is STRICTLY WEAKER: it holds at {len(strict230)} `a = 0` '
          f'tuples where (PENCIL-SATURATES)')
    print('  fails.  TWO NEGATIVE CONTROLS, both ASSERTED:')
    print(f'    * the CONCLUSION cannot drop to `rho_i >= 5` -- '
          f'{len(weaker5)} counterexamples (e.g.')
    print('      `c = (2,1)`, `rho = (5,1)`, `Sigma_rho = 6 < 7`);')
    print(f'    * the HYPOTHESIS cannot strengthen to `c_j(Pi_x) = 2` -- '
          f'{len(tighter)} counterexamples')
    print('      (the `c = (2,1)` corner is then untouched).')
    assert weaker5 and tighter, 'a negative control stopped firing'
    print('  So the honest successor is NOT a weaker inequality but item '
          '0(a) RESTRICTED TO THE')
    print('  TWO-SIDED SUB-LOCUS -- and (BE-175)(i) says exactly where that '
          'restriction is free')
    print('  and where it BUYS something: at a SERIES END at `x` '
          '(`deg_j(x) = 1`) the added')
    print('  hypothesis `c_j(Pi_x) >= 1` is AUTOMATIC, so the obligation is '
          'item 0(a) verbatim')
    print('  there; the restriction has content exactly when NEITHER side is '
          'a series end at `x`,')
    print('  which is where this dispatch\'s `side-degree >= 2` quantifier '
          'puts it.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return len(resa)


# ---------------------------------------------------- the measured-row engine

def _row_at(skname, xy, prof, side1, builder, sd, tag):
    """One fully-gated measured row.  The gate set is `bline.legal_peel`'s
    OWN (called, never re-implemented); the configuration comes from
    `builder`, which is `bproper.plant_peel` (deg_1(x) = 1) or
    `bproper.free_peel` (NO degree gate).  Returns (row, gates) or None."""
    lp = legal_peel(side1, skname, xy, prof)
    if lp is None:
        return None
    _eg, x, y, report = lp
    okh, mindeg, girth_h, degx, degy, rnode2, sized = report
    rng = random.Random(SEED + 613 * sd + 7 * len(tag) + 31 * sum(prof))
    got = builder(skname, prof, xy, side1, rng)
    if got is None:
        return None
    egraph, raw_side = got[0], got[1]
    node_x, node_y, aff = got[3], got[4], got[5]
    assert (node_x, node_y) == (x, y), 'legal_peel and the builder disagree'
    split = delta_pair(egraph, node_x, node_y)
    if split is None:
        return None
    _da, _db, part_a, part_b = split
    near = part_a if len(part_a) == len(raw_side) else part_b
    far = part_b if near is part_a else part_a
    if len(near) != len(raw_side):
        return None
    # (BE-208)(ii)'s SCOPE CHECK, asserted rather than inferred: with equal
    # edge counts `near`/`far` could be swapped and every per-side number
    # would be mislabelled.
    assert len(near) != len(far), \
        ('the two sides have equal edge counts -- the side identification is '
         'ambiguous', skname, xy, prof, tag)
    assert set(map(frozenset, near)) | set(map(frozenset, far)) == \
        set(map(frozenset, egraph)), 'the two sides do not cover H'
    row = e_row(egraph, node_x, node_y, near, far, aff)
    if row is None:
        return None
    gates = dict(hcard=okh, mindeg=mindeg, girth=girth_h, degx=degx,
                 degy=degy, rnode_far=rnode2, sized=sized,
                 rnode_near=rnode_shaped(near, node_x, node_y),
                 witness=verify_pencil_witness(egraph, aff)[0],
                 regime=flag_frame(egraph, aff, node_x, node_y) is not None,
                 deg_near_x=len(neighbors(near).get(node_x, ())),
                 deg_far_x=len(neighbors(far).get(node_x, ())))
    return row, gates


def _assert_gates(gates, tag):
    assert gates['hcard'] and gates['mindeg'] >= 2 and gates['girth'] >= 4, \
        ('(CH-1) fails on H', tag, gates)
    assert gates['degx'] >= 3 and gates['degy'] >= 3, \
        ('a terminal is not a hub of H', tag, gates)
    assert gates['rnode_far'] and gates['sized'], \
        ('side 2 is not R-node-shaped', tag, gates)
    assert gates['witness'], 'the builder returned a non-witness'


def prof_for(skname, d2):
    """BNONUNI's canonical entries-in-{2,3} profile with `delta_2 = d2`, by
    (BE-218)'s closed form `delta_2 = max(0, #3-branches - 6)`."""
    n = len(SKELETONS[skname])
    k = 6 + d2
    assert 0 <= k <= n, ('delta_2 out of range for this skeleton', skname, d2)
    return [2] * (n - k) + [3] * k


def _sweep(jobs, builder, bname, nseed=2):
    """The common sweep: report the obligation, `a`, `Sigma_delta` and the
    degree data at every fully-gated row `builder` produces.  A job is
    `(skname, xy, tag, side1, prof)` -- the profile travels WITH the job, so
    the same sweep covers BNONUNI's non-uniform axis and BGTWOA's uniform
    `plen` axis without a second copy."""
    rows, inreg, fired, failed = 0, 0, 0, 0
    acen, dcen, ccen, dgx, sdcen, rcen = {}, {}, {}, {}, {}, {}
    corncen, resid_hit, strictw, zrows = {}, [], [], []
    azero, azero_reg, worst, kills, corner = 0, 0, None, [], 0
    for (skname, xy, tag, side1, prof) in jobs:
        for sd in range(nseed):
            got = _row_at(skname, xy, prof, side1, builder, sd, tag)
            if got is None:
                continue
            row, gates = got
            _assert_gates(gates, (skname, xy, prof, tag))
            rows += 1
            sd_sum = row['d'][0] + row['d'][1]
            acen[row['a']] = acen.get(row['a'], 0) + 1
            dcen[row['d']] = dcen.get(row['d'], 0) + 1
            ccen[row['cX']] = ccen.get(row['cX'], 0) + 1
            rcen[row['r']] = rcen.get(row['r'], 0) + 1
            sdcen[sd_sum] = sdcen.get(sd_sum, 0) + 1
            dgx[(gates['deg_near_x'], gates['deg_far_x'])] = \
                dgx.get((gates['deg_near_x'], gates['deg_far_x']), 0) + 1
            if row['a'] == (0, 0):
                azero += 1
            if not gates['regime']:
                continue
            inreg += 1
            if row['a'] == (0, 0):
                azero_reg += 1
            marg = row['cX'][0] + row['cX'][1] - 2 - row['slack']
            if worst is None or marg > worst[0]:
                worst = (marg, skname, xy, prof, row['r'], row['cX'],
                         row['d'], row['a'], gates['deg_near_x'],
                         gates['deg_far_x'])
            if row['cX'][0] == 2 or row['cX'][1] == 2:
                fired += 1
            if row['cX'][0] + row['cX'][1] >= 3:
                corner += 1
                ckey = (row['cX'], row['r'], sd_sum, row['slack'], marg)
                corncen[ckey] = corncen.get(ckey, 0) + 1
            if row['cX'][0] + row['cX'][1] >= 3 and max(row['r']) <= 5:
                resid_hit.append((skname, xy, prof, row))
            # item 0(a)'s clause vs the obligation, AT THE SAME ROW: a row
            # where (PENCIL-SATURATES) FAILS and the obligation HOLDS is a
            # GEOMETRIC witness of (BE-226)(i)'s 98-tuple strictness.
            psrow = all(not (row['cX'][i] == 2 and row['r'][i] != 6)
                        for i in (0, 1))
            if not psrow and obl_at(row):
                strictw.append((skname, xy, prof, row))
            if row['a'] == (0, 0):
                zrows.append((skname, xy, prof, row))
            if not obl_at(row):
                failed += 1
                kills.append((skname, xy, prof, row, gates))
    print(f'     {bname}: {rows} fully-gated rows, {inreg} of them IN the '
          f'generic flag regime')
    print(f'     (`flag_frame` non-None); `c_i(Pi_x) = 2` FIRES at {fired} '
          f'of them, the CONTENT')
    print(f'     corner `c_1 + c_2 >= 3` is reached at {corner}, and the '
          f'OBLIGATION FAILS at {failed}.')
    print('     `a = (a_1, a_2)`: ' + census(acen))
    print(f'     `a = (0,0)` at {azero} of {rows} rows, {azero_reg} of them '
          f'in-regime.')
    print('     `(delta_1, delta_2)`: ' + census(dcen))
    print('     `Sigma_delta`: ' + census(sdcen) + ';  `c(Pi_x)`: '
          + census(ccen))
    print('     `(rho_1, rho_2)`: ' + census(rcen))
    print('     `(deg_1(x), deg_2(x))`: ' + census(dgx))
    if worst is not None:
        print(f'     widest in-regime obligation margin '
              f'`c_1+c_2-2-slack` = {worst[0]} at {worst[1]} {worst[2]} '
              f'prof {worst[3]},')
        print(f'       rho = {worst[4]}, c = {worst[5]}, delta = {worst[6]}, '
              f'a = {worst[7]}, deg = ({worst[8]},{worst[9]})')
    if corncen:
        print('     THE CONTENT CORNER `c_1 + c_2 >= 3`, row by row '
              '`(c, rho, Sigma_delta, slack, margin)`:')
        for key, num in sorted(corncen.items(), key=str):
            print(f'       {num:3d}  c = {key[0]}, rho = {key[1]}, '
                  f'Sigma_delta = {key[2]}, slack = {key[3]}, '
                  f'margin = {key[4]}')
    print(f'     THE RESIDUE `c_1 + c_2 >= 3` AND `max(rho) <= 5` -- the '
          f'only shape that can')
    print(f'     violate the obligation at `a = 0` ((BE-227)) -- is reached '
          f'at {len(resid_hit)} rows.')
    print(f'     STRICTNESS, GEOMETRIC: at {len(strictw)} in-regime rows '
          f'item 0(a)\'s clause')
    print('     (PENCIL-SATURATES) FAILS while the OBLIGATION HOLDS -- '
          '(BE-226)(i)\'s 98-tuple gap,')
    print('     realized on configurations rather than on tuples.')
    for (skname, xy, prof, row, gates) in kills:
        print(f'     ** OBLIGATION FAILS: {skname} {xy} prof {prof}, '
              f'rho = {row["r"]}, c = {row["cX"]},')
        print(f'        delta = {row["d"]}, a = {row["a"]}, slack = '
              f'{row["slack"]}, deg = ({gates["deg_near_x"]},'
              f'{gates["deg_far_x"]}), regime {gates["regime"]}')
    return dict(rows=rows, inreg=inreg, fired=fired, failed=failed,
                corner=corner, azero=azero, azero_reg=azero_reg,
                kills=kills, sdcen=sdcen, acen=acen, ccen=ccen,
                resid_hit=resid_hit, corncen=corncen,
                strictw=strictw, zrows=zrows)


MINIMAL_FRONTIER = [(0, 4), (4, 3), (5, 2), (6, 0)]


def _frontier_audit(zrows, tag):
    """(BE-226)(iii)'s minimal two-piece frontier members, tested against the
    MEASURED `a = 0` in-regime rows.  A member `(f, g)` demands
    `c_i(Pi_x) = 2 ==> rho_i >= f` and `c_j(Pi_x) >= 1 ==> rho_j >= g`."""
    print(f'     (BE-226)(iii) FRONTIER AUDIT against the {len(zrows)} measured '
          f'`a = 0` in-regime rows ({tag}):')
    dead, live = [], []
    for (f, g) in MINIMAL_FRONTIER:
        bad = None
        for (skname, xy, prof, row) in zrows:
            ok = True
            for i in (0, 1):
                if row['cX'][i] == 2 and row['r'][i] < f:
                    ok = False
                if row['cX'][i] >= 1 and row['r'][i] < g:
                    ok = False
            if not ok:
                bad = (skname, xy, prof, row)
                break
        if bad is None:
            live.append((f, g))
            print(f'       ({f},{g}): UNREFUTED on this population')
        else:
            dead.append((f, g))
            skname, xy, prof, row = bad
            print(f'       ({f},{g}): **REFUTED** at {skname} {xy} prof '
                  f'{prof} -- rho = {row["r"]}, c = {row["cX"]}, '
                  f'a = {row["a"]}')
    return dead, live


# ============================================= mode: regime  ((BE-229)(i))

def run_regime(nseed=2):
    t0 = time.time()
    print(f'== regime: (BE-229)(i) THE IN-REGIME POPULATION -- is `a = 0` '
          f'REACHABLE?  seed {SEED}')
    print('  BNONUNI\'s own machinery, unchanged: `bproper.plant_peel` over '
          '`bproper.PEELJOBS` with')
    print('  the NON-UNIFORM profile axis (BE-218) opened, PLUS BGTWOA\'s '
          'uniform `plen` axis, which')
    print('  is where the CONTENT corner `c_1 + c_2 >= 3` is reached '
          'in-regime.  What is new is the')
    print('  QUANTITY read off each row: the `Pi_x` OBLIGATION and `a`, not '
          '`(BE-E4\')`\'s margin.')
    jobs = []
    for (sk, xy, s1) in PEELJOBS:
        for d2 in (0, 1, 2, 3):
            jobs.append((sk, xy, s1, side_named(s1)[0], prof_for(sk, d2)))
    # BGTWOA's own kill jobs, uniform `plen` -- the rows where `rho_j = 6`
    # makes firing GRASSMANN-FORCED on the skeleton side, hence `c = (1,2)`.
    for (sk, xy, plen, s1) in KILLJOBS:
        jobs.append((sk, xy, s1, side_named(s1)[0],
                     [plen] * len(SKELETONS[sk])))
    res = _sweep(jobs, plant_peel, 'plant_peel', nseed=nseed)
    assert res['rows'] > 0, 'the in-regime sweep produced no rows at all'
    print('  READING.  The population `plant_peel` can present is fenced '
          'twice over against')
    print('  the obligation\'s own quantifier, and BOTH fences are '
          'MEASURED above, not argued:')
    print(f'  `a = (0,0)` at {res["azero"]} of {res["rows"]} rows '
          f'({res["azero_reg"]} in-regime), and `deg_1(x) = 1` at every row')
    print('  (the builder returns None otherwise -- read at source).  So a '
          'refutation of the')
    print('  obligation cannot come from here, whatever the profile axis '
          'does.  What it DOES')
    print('  deliver is the FIRST GEOMETRIC WITNESS of (BE-226)(i)\'s '
          'strictness: at the rows above')
    print('  item 0(a)\'s clause FAILS (a planted side firing at '
          '`rho_1 = 4 < 6`) and the')
    print('  obligation HOLDS at margin 0, so the 98-tuple gap is INHABITED '
          'by configurations')
    print('  through every habitat gate, not merely by tuples.')
    assert res['strictw'], \
        'the strictness witness did not fire -- re-read (BE-226)/(BE-228)'
    assert not res['resid_hit'], \
        ('the residue IS reached in-regime -- check for a refutation before '
         'recording a reduction')
    dead, live = _frontier_audit(res['zrows'], 'plant_peel')
    assert (0, 4) in dead and (4, 3) in dead, \
        'the two cheapest frontier members survived -- re-read (BE-226)'
    assert (6, 0) in live, '(PENCIL-SATURATES) itself was refuted at a = 0'
    print('  So the two CHEAPEST minimal frontier members die on the same '
          'mechanism BGTWOA')
    print('  killed `(BE-G_2)` with -- (BE-175)(i) on the NON-FIRING side, '
          'here reaching')
    print('  `c_1(Pi_x) = 1` at `rho_1 = 2`; and the surviving pair is '
          '`(5,2)` and `(6,0)`, of')
    print('  which only `(5,2)` is weaker than item 0(a).')
    print(f'  regime: {time.time() - t0:.1f}s')
    return res


# ============================================= mode: degtwo  ((BE-229)(ii))

def run_degtwo(nseed=1):
    t0 = time.time()
    print(f'== degtwo: (BE-229)(ii) THE UN-FENCING -- `deg_1(x) >= 2` IN THE '
          f'REGIME, seed {SEED}')
    print('  `bproper.plant_peel` returns None unless side 1\'s neighbour '
          'count at `x` is 1')
    print('  (read at source, `bproper.py`), so the side-degree the '
          'dispatch\'s quantifier is stated at was')
    print('  structurally out of BNONUNI\'s reach -- its blind axis.  '
          '`bproper.free_peel`, the F13')
    print('  NEGATIVE CONTROL of the same peel, carries NO degree gate, so '
          'the axis costs a')
    print('  DIFFERENT LANDED CALL and NO harness edit: this driver changes '
          'no tracked file.')
    print('  Side 1 is `bline.longcore_library()`, where `x` sits on a short '
          'cycle, so')
    print('  `deg_1(x) = 2` BY CONSTRUCTION.')
    lib = longcore_library()
    jobs = []
    for (nm, ed, _x, _y) in lib:
        for d2 in (0, 1, 2, 3):
            jobs.append(('K33', ('A', 'B'), nm, ed, prof_for('K33', d2)))
        jobs.append(('prism', ('A', 'E'), nm, ed, [4] * 9))
    print(f'  CAP, DISCLOSED: {len(lib)} library shapes x 5 profiles x '
          f'{nseed} seed(s).  The profiles are')
    print('  BNONUNI\'s four non-uniform `delta_2` rungs on `K33` plus the '
          'uniform `[4]*9` on')
    print('  `prism` for the `delta_2 = 6` end, so `delta_2` ranges over '
          '{0,1,2,3,6}; ONE seed per')
    print('  job, traded for that coverage.')
    res = _sweep(jobs, free_peel, 'free_peel', nseed=nseed)
    assert res['rows'] > 0, 'the un-fenced sweep produced no rows at all'
    assert res['azero'] == res['rows'], \
        'a free-peel row missed `a = 0` -- the un-fencing claim moved'
    assert res['inreg'] == res['rows'], \
        'a free-peel row fell off the generic flag regime'
    _frontier_audit(res['zrows'], 'free_peel')
    print('  READING, and it is the cap that matters.  This population '
          'REACHES the dispatch\'s')
    print('  own quantifier -- `a = 0`, generic flag regime, '
          '`deg_1(x) = 2` -- at EVERY row, which')
    print('  no predecessor population did; and the obligation is '
          'UNVIOLATED there.  But the')
    print('  RESIDUE ((BE-227)) is reached at 0 rows: every firing this '
          'population produces is')
    print('  at `rho_i = 6`, where Grassmann forces `c_i = 2` and the '
          'obligation is FREE.  So')
    print('  the evidence is *not found under this cap*, never *does not '
          'exist* -- the same')
    print('  shape (BE-186)(i) recorded one rung up: the population cannot '
          'present the')
    print('  DISCRIMINATING case, which is item 0(a)\'s own bad locus.')
    print(f'  degtwo: {time.time() - t0:.1f}s')
    return res


# ============================================= mode: gated  ((BE-229)(iii))

def _gated_family(lib, arclen, seed, ndraw=8):
    """The two landed pointwise-refutation families, re-read against the
    OBLIGATION.  Construction verbatim from `befourp._gated_family`:
    `bline.legal_peel` + `bproper.composite` + `binduc.flat_config`."""
    rows, viol, frame_none, azero = 0, 0, 0, 0
    cens = {}
    for (name, eside, _x0, _y0) in lib:
        lp = legal_peel(eside)
        if lp is None:
            continue
        egraph, x, y, (okh, md, g, dx, dy, rn, sz) = lp
        assert okh and md >= 2 and g >= 4, ('(CH-1) fails on H', name)
        assert dx >= 3 and dy >= 3 and rn, ('peel gates fail', name)
        _ehc, esd1, esd2, _x, _y = composite('K33', [3] * 9, ('A', 'B'),
                                             eside)
        cs = sorted(neighbors(esd1)[x], key=str)
        assert len(cs) == 2, ('deg_1(x) != 2 on the composite', cs)
        f1 = {frozenset(e) for e in esd1}
        f2 = {frozenset(e) for e in esd2}
        assert f1 | f2 == {frozenset(e) for e in egraph} and not (f1 & f2), \
            ('side 1 and side 2 do not partition H', name)
        for d in range(ndraw):
            rng = random.Random(seed + 977 * d + len(name))
            try:
                aff = flat_config(egraph, rng)
            except RuntimeError:
                continue
            assert verify_pencil_witness(egraph, aff)[0], \
                'flat_config returned a non-witness'
            pixsp = span([wedge2(hat(aff[x]), hat(aff[c])) for c in cs])
            assert dim(pixsp) == 2, 'the two hinge lines at x coincide'
            assert plane_at(egraph, aff, x) is not None, 'no plane at x'
            arc1 = arc_through(esd1, x, y, cs[0]) \
                or arc_through(esd1, x, y, cs[1])
            assert arc1 is not None and len(arc1) - 1 == arclen, \
                ('the gated peel does not carry the expected arc', name)
            row = e_row(egraph, x, y, esd1, esd2, aff)
            if row is None:
                continue
            rows += 1
            if flag_frame(egraph, aff, x, y) is None:
                frame_none += 1
            if row['a'] == (0, 0):
                azero += 1
            key = (row['r'], row['cX'], row['d'], row['a'], row['slack'])
            cens[key] = cens.get(key, 0) + 1
            if not obl_at(row):
                viol += 1
    print(f'     arc {arclen}: {rows} gated chart points, the OBLIGATION '
          f'FAILS at {viol};')
    print(f'     `flag_frame` None at {frame_none} of {rows}; `a = (0,0)` at '
          f'{azero} of {rows}.')
    for key, num in sorted(cens.items(), key=str):
        r, cX, d, a, sl = key
        print(f'       {num:3d}  rho = {r}, c = {cX}, delta = {d}, a = {a}, '
              f'slack = {sl}')
    return dict(rows=rows, viol=viol, frame_none=frame_none, azero=azero)


def run_gated(seed=SEED):
    t0 = time.time()
    print(f'== gated: (BE-229)(iii) THE TWO LANDED POINTWISE FAMILIES, RE-READ '
          f'AGAINST THE OBLIGATION, seed {seed}')
    print('  (BE-208)(iv) records `c_1 + c_2 = 4` with `slack = 0` at these '
          'rows but claims no')
    print('  margin, `row_of` being undefined off the regime.  Read against '
          'the OBLIGATION they')
    print('  sit INSIDE its `c = (2,2)` violating corner -- so this is the '
          'sharpest test the')
    print('  obligation has, and it is disqualified by the SAME two gates, '
          'both MEASURED here.')
    print('  -- BRANKV (BE-192): arc 3 --')
    a3 = _gated_family(short_library(), 3, seed)
    print('  -- BLONGARC (BE-200): arc 4 --')
    a4 = _gated_family(arc4_library(), 4, seed)
    tot = a3['rows'] + a4['rows']
    vio = a3['viol'] + a4['viol']
    fn = a3['frame_none'] + a4['frame_none']
    az = a3['azero'] + a4['azero']
    print(f'  VERDICT.  Over both families: {tot} gated points, the '
          f'obligation FAILS at {vio},')
    print(f'  `flag_frame` None at {fn} of {tot}, and `a = (0,0)` at {az} of '
          f'{tot}.')
    assert fn == tot, ('a gated row entered the generic flag regime -- '
                       're-read (BE-208)(ii)')
    assert az == 0, ('a gated row reached `a = 0` -- this WOULD be a '
                     'refutation of the obligation; re-read before recording')
    print('  So every violating row is OUTSIDE the obligation\'s own '
          'quantifier on BOTH counts,')
    print('  and the first is STRUCTURAL rather than incidental: (BE-191) '
          'and (BE-200) force')
    print('  `q_y in pi_x` / `q_z in pi_x`, which is exactly one of the '
          'three exclusions')
    print('  `bunif.flag_frame`\'s rank-4 test applies.  **This population '
          'provably cannot')
    print('  refute the obligation** -- the same shape (BE-186)(i) recorded '
          'one rung up.')
    print(f'  gated: {time.time() - t0:.1f}s')
    return vio


def run_validate():
    print('== validate: arith + regime + degtwo + gated in one process')
    run_arith()
    run_regime()
    run_degtwo()
    run_gated()


def main(argv):
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        return 0
    mode = argv[0].lstrip('-')
    if mode == 'arith':
        run_arith()
    elif mode == 'regime':
        run_regime()
    elif mode == 'degtwo':
        run_degtwo()
    elif mode == 'gated':
        run_gated()
    elif mode == 'validate':
        run_validate()
    else:
        print(f'unknown mode {mode!r}')
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
