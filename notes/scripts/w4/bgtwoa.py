"""
Direction BGTWOA (arc ordinal 89) -- CAN BSTEER's DEGREE COUNT BE LIFTED OFF
ITS `rho_2 = 1` HYPOTHESIS?  The slice BEFOURP named, `(BE-G_2a)`.

  THE ANSWER, said at the top: NO.  The lift does NOT go through, and the
  obstruction is the deliverable.  `(BE-G_2a)` -- and with it `(BE-G_2)` and
  BEFOURP's whole five-member frontier -- is REFUTED three independent ways,
  the third of which is BSTEER's own (BE-175)(i) mechanism turned around.

  (BE-210) THE AMBIENT CAP DOES MOST OF THE WORK, AND IT IS FREE.
           `c_j(Pi_x) = dim(rho_bar_j cap Pi_x) <= dim Pi_x = 2`, so
              `e_j = rho_j - c_j(Pi_x) >= rho_j - 2`
           at EVERY row, with no hypothesis of any kind -- no `rnode_shaped`,
           no flag regime, no residual cap, no degree count.  Hence
           `(BE-G_2)` (`e_j >= 2`) is a THEOREM at `rho_j >= 4`, is FALSE at
           `rho_j <= 1`, and its entire content is the two rungs
           `rho_j in {2, 3}`.  BSTEER's habitat is `rho_j = 1` -- exactly the
           rung where `(BE-G_2)` cannot hold -- so the theorem's habitat and
           the target's content habitat are DISJOINT.

  (BE-211) AND `(BE-G_2a)` AS STATED IS UNSATISFIABLE AT `rho_j >= 5`.
           Grassmann in `Lambda^2 K^4` gives `c_j(Pi_x) >= rho_j - 4`, so
           `c_j(Pi_x) = 0` is impossible at `rho_j >= 5` and `= 2` is FORCED
           at `rho_j = 6`.  The realizable range is EXACTLY
              `max(0, rho - 4) <= c <= min(2, rho)`,
           constructed here shape by shape, never sampled.  This is a THIRD
           `c_j(Pi_x) >= 1` mechanism -- the ambient one -- and it is not a
           mechanism a hypothesis can exclude.

  (BE-212) (BE-206)'s FOUR-RUNG GRADING IS A TAUTOLOGY WHERE IT IS VERIFIED
           AND FALSE WHERE IT IS NOT.  `befourp.run_peel` asserts
           `e_i = dim(rho_bar_i ^ p_x) + [Sigma_x <= rho_bar_i]` only under
           `c_i(Pi_x) = 2`, where it reduces to `dim(rho_bar_i cap Sigma_x)
           in {2, 3}` and says nothing beyond `e_i = rho_i - 2`.  Off that
           branch it FAILS, at 8 of 23 constructed shapes.  So `(BE-F_4)` IS
           the floor `rho_i >= 4`, and `q_hat` adds no leverage to it.

  (BE-213) THE 6 400-TUPLE SPACE OMITS THE GRASSMANN FLOOR -- 2 800 of its
           tuples are geometrically unrealizable -- BUT THE FRONTIER DOES NOT
           MOVE: all 245 escapes are floor-legal and the 25-cell grid is
           identical.  A negative result that PROTECTS BEFOURP's enumeration.

  (BE-214) THE KILL.  `(BE-G_2)` is REFUTED at fully-gated peels INSIDE the
           generic flag regime with side 2 R-node-shaped and both sides
           flexible: `rho = (2, 6)`, `c(Pi_x) = (1, 2)`, `e = (1, 4)`.  The
           firing side is side 2; the OTHER side is side 1, which carries a
           SERIES END at `x` -- so `ell = p_x ^ p_c` lands in
           `rho_bar_1 cap Pi_x` by **(BE-175)(i) itself**.  (BE-175)(ii)'s
           `rnode_shaped` exclusion and the flag-regime gate are both indexed
           to SIDE 2; `(BE-G_g)`'s subject is the NON-FIRING side.  The two
           coincide only when the firing side is the non-R-node one, which is
           BEFOURP's 21 rows but not the general peel.

  (BE-215) SO THE FRONTIER IS EXHAUSTED, not merely thinned.  `(5,1)` and
           `(6,0)` need `(BE-F_5)`/`(BE-F_6)`, both already refuted; `(4,2)`,
           `(3,3)` and `(2,4)` each IMPLY `(BE-G_2)`.  BEFOURP's kill
           condition FIRED -- its consequence was right and its trigger was
           wrong: `c_j(Pi_x) >= 1` is forced and harmless at `rho_j >= 5`;
           the operative condition is `e_j <= 1`, which needs `rho_j <= 3`.

  (BE-216) THE REPLACEMENT, PROVED AND HYPOTHESIS-FREE.  At a firing side
           `e_i = rho_i - 2` exactly, so with (BE-210)'s cap
              `(BE-E4')  <==  rho_1 + rho_2 >= 8`,
           and 0 of the 245 escapes reach it (census `{3:8, 4:32, 5:76,
           6:85, 7:44}`).  A SUM condition, which is (BE-204)'s own
           two-sidedness arriving at `rho` instead of `dist`.  And (BE-E4')
           itself is NOT refuted: it holds at every in-regime row measured
           here, including all four kill witnesses (margin `+1`).

  MODES
    arith   (BE-210)/(BE-213)/(BE-215)/(BE-216)  exhaustive over the 6 400
            tuples; no sampling, seed unused.
    rungs   (BE-211)/(BE-212)  the realizability table and the grading
            counterexample, CONSTRUCTED in exact Q shape by shape -- never a
            random 2-space (`RESEARCH-ARC.md` section 4's vacuous-assert trap,
            which fired at BRANKV and at one of BEFOURP's own drafts).
    hunt    (BE-214)  the kill witnesses, every habitat gate asserted, plus
            the in-regime census sweep the verdict's caps are stated over.
    validate  all three in one process.

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is never called, so its silent `K^4` truncation is
  unreachable rather than merely avoided.  No width-12 object is built: every
  `span`/`isect`/`dim`/`contains` call here takes width-6 (`Lambda^2 K^4`)
  rows, which is `bimage.span`'s `d == 6` branch, and every `K^4`-side
  dimension goes through the width-agnostic `exactcore.rank`.  `bwin` is not
  imported, so `dehom`'s list-vs-tuple guard defeat is unreachable.  Every
  configuration comes from a predecessor's own builder (`bproper.plant_peel`)
  rather than being written here.  No tracked driver is modified: the
  Grassmann floor of (BE-213) is applied as a FILTER over
  `barch.all_tuples()`, never as an edit to it.
"""

import os
import sys
import time
import random
import itertools
from fractions import Fraction as Frac

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, wedge2, rank, neighbors                   # noqa: E402
from bimage import dim, isect, span, contains, pencil_space       # noqa: E402
from bunif import SEED, flag_frame                                   # noqa: E402
from bsatur import sigma_at                                          # noqa: E402
from bsigma import wedge3                                            # noqa: E402
from bproper import plant_peel, side_named                        # noqa: E402
from bpeel import SKELETONS, delta_pair, rnode_shaped, girth      # noqa: E402
from bline import hcard_ok_piece                                     # noqa: E402
from bfour import e_row                                              # noqa: E402
from kbare_common import verify_pencil_witness                       # noqa: E402
import barch as BA                                                   # noqa: E402


# ------------------------------------------------------------------ helpers

def firing(tup):
    """The sides whose (BE-E4') hypothesis fires: `c_i(Pi_x) = 2`, which
    (BE-156)(i) shows IS `Pi_x <= rho_bar_i`.  BEFOURP's `firing`, recomputed
    so `arith` stays a pure enumeration."""
    return [i for i in (0, 1) if tup[6 + i] == 2]


def e_of(tup):
    """`(e_1, e_2)`, `e_i = rho_i - c_i(Pi_x)` -- (BE-153)(v)'s definition."""
    return (tup[4] - tup[6], tup[5] - tup[7])


def flexible(tup):
    """(BE-162)(i)'s added hypothesis: both sides non-rigid."""
    return tup[0] >= 1 and tup[1] >= 1


def e4prime(tup):
    """(BE-E4'): section (K-bare-ext) (E4) restricted to `delta_i >= 1` --
    the (L3) qualification, (E4) being a grandfathered bare token with a
    recorded collision."""
    if not flexible(tup):
        return True
    return BA.e4(tup)


def floor_legal(tup):
    """(BE-213)'s missing conjunct: Grassmann in `Lambda^2 K^4` forces
    `c_i(Pi_x) >= dim rho_bar_i + dim Pi_x - 6 = rho_i - 4`.
    `barch.all_tuples` enforces only the UPPER cap `c_i <= min(2, rho_i)`."""
    return tup[6] >= max(0, tup[4] - 4) and tup[7] >= max(0, tup[5] - 4)


def piece_floor(tup, f):
    """(BE-F_f): every FIRING side has `rho_i >= f`."""
    return all(tup[4 + i] >= f for i in firing(tup))


def piece_other(tup, g):
    """(BE-G_g): for every FIRING side `i`, the OTHER side has `e_j >= g`."""
    es = e_of(tup)
    return all(es[1 - i] >= g for i in firing(tup))


def g2a_raw(tup):
    """`(BE-G_2a)` AS BEFOURP STATES IT: `c_j(Pi_x) = 0` on the non-firing
    side, with no `rho_j` restriction.  Paired with `(BE-G_2b)` (`rho_j >= 2`)
    it is (BE-209)(i)'s sufficient condition for `(BE-G_2)`."""
    return all(tup[6 + (1 - i)] == 0 and tup[4 + (1 - i)] >= 2
               for i in firing(tup))


def g2a_restricted(tup):
    """The REPAIR: `rho_j >= 2`, and `c_j(Pi_x) <= rho_j - 2` only where the
    ambient does not already give it, i.e. at `rho_j <= 3`.  (BE-210) asserts
    this is EQUIVALENT to `(BE-G_2)`, not merely sufficient for it."""
    for i in firing(tup):
        other = 1 - i
        if tup[4 + other] < 2:
            return False
        if tup[4 + other] <= 3 and tup[6 + other] > tup[4 + other] - 2:
            return False
    return True


def census(pairs):
    return ', '.join(f'{k}: {v}' for k, v in sorted(pairs.items()))


# ============================== mode: arith  (BE-210/213/215/216)

def run_arith():
    t0 = time.time()
    print(f'== arith: (BE-210)/(BE-213)/(BE-215)/(BE-216)  THE LIFT\'S '
          f'ARITHMETIC  [no sampling; seed {SEED} unused]')
    tuples = list(BA.all_tuples())
    print(f'  Enumeration: all {len(tuples)} tuples the caps allow -- '
          f'`barch.all_tuples`, BEFOURP\'s own space.')
    viol = [t for t in tuples if not e4prime(t)]
    assert len(viol) == 245, ('(BE-162)(iii)\'s 245 moved', len(viol))
    print(f'  (BE-162)(iii) REPRODUCED: {len(viol)} tuples violate (BE-E4\').')

    # ---- pass 1: (BE-210) the ambient cap, and what it already gives.
    print('  Pass 1 -- (BE-210) THE AMBIENT CAP `c_j(Pi_x) <= dim Pi_x = 2`.')
    assert max(max(t[6], t[7]) for t in tuples) == 2, \
        'the tuple space does not cap c_i at dim Pi_x = 2'
    assert all(e_of(t)[j] >= t[4 + j] - 2 for t in tuples for j in (0, 1)), \
        'e_j >= rho_j - 2 FAILED -- the cap is not what it is'
    free = [t for t in tuples if firing(t)
            and all(t[4 + (1 - i)] >= 4 for i in firing(t))]
    assert all(piece_other(t, 2) for t in free), \
        '(BE-G_2) is not free at rho_j >= 4 after all'
    dead = [t for t in tuples if firing(t)
            and any(t[4 + (1 - i)] <= 1 for i in firing(t))]
    assert not any(piece_other(t, 2) for t in dead), \
        '(BE-G_2) held somewhere with rho_j <= 1'
    print(f'    `e_j >= rho_j - 2` at all {len(tuples)} tuples, ASSERTED.  '
          f'Hence `(BE-G_2)` is')
    print(f'    TRUE at the {len(free)} firing tuples with `rho_j >= 4` and '
          f'FALSE at all {len(dead)} with')
    print('    `rho_j <= 1` -- both ASSERTED.  So its content is exactly '
          '`rho_j in {2, 3}`, and')
    print('    BSTEER\'s `rho_j = 1` habitat is DISJOINT from that content.')
    assert all(g2a_restricted(t) == piece_other(t, 2)
               for t in tuples if firing(t)), \
        'the restricted repair is NOT equivalent to (BE-G_2)'
    nfire = sum(1 for t in tuples if firing(t))
    print(f'    THE REPAIR IS AN EQUIVALENCE, not a sufficiency: '
          f'`rho_j >= 2 & (rho_j <= 3 => c_j <= rho_j - 2)`')
    print(f'    <=> `(BE-G_2)` at all {nfire} firing tuples, ASSERTED.')

    # ---- pass 2: (BE-213) the missing Grassmann floor.
    print('  Pass 2 -- (BE-213) THE MISSING GRASSMANN FLOOR '
          '`c_i(Pi_x) >= rho_i - 4`.')
    legal = [t for t in tuples if floor_legal(t)]
    print(f'    `barch.all_tuples` yields {len(tuples)}; only {len(legal)} '
          f'satisfy the floor, so {len(tuples) - len(legal)}')
    print('    are geometrically UNREALIZABLE in `Lambda^2 K^4` '
          '(`rungs` constructs the range).')
    assert all(floor_legal(t) for t in viol), \
        'an escape violates the Grassmann floor'
    print(f'    BUT every one of the {len(viol)} escapes is floor-legal, '
          f'ASSERTED -- so the frontier')
    print('    CANNOT move.  Enumerated both ways to be sure:')
    grids = {}
    for tag, pop in (('raw', tuples), ('floor-legal', legal)):
        grid = {}
        for f in range(2, 7):
            for g in range(0, 5):
                grid[(f, g)] = sum(1 for t in pop if piece_floor(t, f)
                                   and piece_other(t, g) and not e4prime(t))
        grids[tag] = grid
    assert grids['raw'] == grids['floor-legal'], \
        'the Grassmann floor MOVED the frontier grid'
    for f in range(2, 7):
        row = '  '.join(f'{grids["raw"][(f, g)]:4d}' for g in range(0, 5))
        print(f'      (BE-F_{f}) x (BE-G_g), g = 0..4:  {row}')
    frontier = [(f, g) for (f, g), n in sorted(grids['raw'].items())
                if n == 0 and grids['raw'].get((f, g - 1), 1) != 0
                and grids['raw'].get((f - 1, g), 1) != 0]
    assert frontier == [(2, 4), (3, 3), (4, 2), (5, 1), (6, 0)], \
        ('(BE-205)(iii)\'s frontier moved', frontier)
    print(f'    Minimal pairs IDENTICAL under both: {frontier} -- '
          f'ASSERTED equal, so (BE-205)(iii)')
    print('    is PROTECTED rather than corrected by this defect.')

    # ---- pass 3: (BE-215) the frontier is exhausted, member by member.
    print('  Pass 3 -- (BE-215) EVERY SURVIVING MEMBER IMPLIES `(BE-G_2)`.')
    for (f, g) in frontier:
        if g >= 2:
            assert all(piece_other(t, 2) for t in tuples
                       if firing(t) and piece_other(t, g)), \
                (f'(BE-G_{g}) does not imply (BE-G_2)', f, g)
    need = [(f, g) for (f, g) in frontier if g >= 2]
    print(f'    Members needing `g >= 2`: {need} -- each ASSERTED to imply '
          f'`(BE-G_2)`.')
    print('    The other two need `(BE-F_5)` ((BE-207)(i): REFUTED) and '
          '`(BE-F_6)` = (PENCIL-SATURATES)')
    print('    ((BE-205)(ii)/(BE-104): REFUTED).  So `hunt`\'s witness '
          'retires the WHOLE frontier.')
    print('    AND THE TRIGGER WAS WRONG: `e_j <= 1` needs `c_j >= rho_j - 1` '
          'with `c_j <= 2`, hence')
    assert not any(e_of(t)[1 - i] <= 1 for t in tuples for i in firing(t)
                   if t[4 + (1 - i)] >= 4), \
        'e_j <= 1 occurred at rho_j >= 4'
    print('    `rho_j <= 3` -- ASSERTED, so a `c_j(Pi_x) >= 1` mechanism at '
          '`rho_j >= 4` is HARMLESS.')

    # ---- pass 4: (BE-216) the replacement, and it is a SUM.
    print('  Pass 4 -- (BE-216) THE REPLACEMENT `rho_1 + rho_2 >= 8`, '
          'HYPOTHESIS-FREE.')
    assert all(e_of(t)[i] == t[4 + i] - 2 for t in tuples
               for i in firing(t)), 'e_i = rho_i - 2 fails at a firing side'
    big = [t for t in tuples if firing(t) and flexible(t)
           and t[4] + t[5] >= 8]
    assert all(e4prime(t) for t in big), \
        '(BE-E4\') fails somewhere with rho_1 + rho_2 >= 8'
    sumh = {}
    for t in viol:
        sumh[t[4] + t[5]] = sumh.get(t[4] + t[5], 0) + 1
    assert max(t[4] + t[5] for t in viol) == 7, \
        'an escape reaches rho_1 + rho_2 >= 8'
    print(f'    At a firing side `e_i = rho_i - 2` EXACTLY (asserted), so '
          f'with (BE-210)\'s cap')
    print(f'    `e_1 + e_2 >= rho_1 + rho_2 - 4`.  (BE-E4\') therefore HOLDS '
          f'at all {len(big)} firing')
    print('    both-flexible tuples with `rho_1 + rho_2 >= 8`, ASSERTED, and '
          'the escapes\' own')
    print(f'    `rho_1 + rho_2` census is {census(sumh)} -- MAXIMUM 7, '
          f'asserted.  The open zone is')
    print('    exactly `rho_1 + rho_2 <= 7`, and the condition is a SUM: '
          '(BE-204)\'s two-sidedness')
    print('    arriving at `rho` rather than at `dist`.')

    # ---- pass 5: how far the raw slice overshoots.
    over = [t for t in tuples if firing(t) and floor_legal(t)
            and piece_other(t, 2) and not g2a_raw(t)]
    assert over, 'the raw slice and (BE-G_2) never differ'
    imposs = [t for t in legal for j in (0, 1)
              if t[4 + j] >= 5 and t[6 + j] == 0]
    assert not imposs, 'a floor-legal tuple has rho_j >= 5 with c_j = 0'
    hi = sum(1 for t in viol for i in firing(t) if t[4 + (1 - i)] >= 5)
    print(f'  Pass 5 -- the raw slice OVERSHOOTS: `(BE-G_2)` holds but '
          f'`(BE-G_2a) & (BE-G_2b)` fails at')
    print(f'    {len(over)} floor-legal firing tuples; and `c_j = 0` at '
          f'`rho_j >= 5` is realized {len(imposs)} times')
    print(f'    (ASSERTED zero), while {hi} of the 245 escapes sit at '
          f'`rho_j >= 5` on the non-firing side.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return len(viol)


# ================================== mode: rungs  (BE-211/212)

def _basis_vec(i):
    return [Frac(1) if k == i else Frac(0) for k in range(4)]


def _klein(vec):
    """The Klein form in `exactcore.wedge2`'s basis order (12,13,14,23,24,34):
    `Q(w) = 2(w12 w34 - w13 w24 + w14 w23)`.  Verified against the basis in
    this mode rather than assumed."""
    return 2 * (vec[0] * vec[5] - vec[1] * vec[4] + vec[2] * vec[3])


def run_rungs():
    t0 = time.time()
    print('== rungs: (BE-211)/(BE-212) THE REALIZABLE RANGE and the GRADING, '
          'CONSTRUCTED')
    print('  Everything below is BUILT from a named basis in exact Q.  '
          'Nothing is sampled: a')
    print('  random 2-space is never isotropic, which is how a predecessor\'s '
          'assert went VACUOUS')
    print('  (`RESEARCH-ARC.md` section 4; BRANKV\'s rank-2 draft and one of '
          'BEFOURP\'s own).')
    point = _basis_vec(0)
    star_plane = [_basis_vec(0), _basis_vec(1), _basis_vec(2)]
    sigx = sigma_at(point)
    pix = pencil_space(point, star_plane)
    assert dim(sigx) == 3 and dim(pix) == 2, 'Sigma_x / Pi_x dimensions moved'
    assert contains(sigx, pix), 'Pi_x is not inside Sigma_x'
    inner = [wedge2(point, _basis_vec(k)) for k in (1, 2, 3)]
    outer = [wedge2(_basis_vec(1), _basis_vec(2)),
             wedge2(_basis_vec(1), _basis_vec(3)),
             wedge2(_basis_vec(2), _basis_vec(3))]
    vals = set()
    for one in inner:
        vals.add(_klein(one))
        for two in inner:
            vals.add(_klein([a + b for a, b in zip(one, two)]))
    assert vals == {Frac(0)}, ('Sigma_x is NOT totally singular', vals)
    print(f'  `Sigma_x = p_x ^ K^4` dim {dim(sigx)}, TOTALLY SINGULAR '
          f'(Klein form 0 on its basis and every')
    print(f'  pairwise sum, {len(vals)} distinct value asserted); '
          f'`Pi_x = p_x ^ pi_x` dim {dim(pix)}, INSIDE it at')
    print('  codimension 1.  That codimension is the whole reason '
          '`c` and `dim(rho_bar cap Sigma_x)`')
    print('  can differ by 1 -- which is (BE-212)\'s counterexample.')

    # every subspace of Sigma_x, by (dim, dim cap Pi_x), CONSTRUCTED
    inside = {(0, 0): [], (1, 1): [inner[0]], (1, 0): [inner[2]],
              (2, 2): [inner[0], inner[1]], (2, 1): [inner[0], inner[2]],
              (3, 2): [inner[0], inner[1], inner[2]]}
    print('  The six subspaces of `Sigma_x` up to the pair '
          '`(dim, dim cap Pi_x)`, each BUILT:')
    print('    ' + ', '.join(f'({a},{b})' for (a, b) in sorted(inside)))
    shapes, broken, realized = 0, [], {}
    for (dsig, cwant), core in sorted(inside.items()):
        for extra in range(0, 4):
            rho = dsig + extra
            if rho == 0 or rho > 6:
                continue
            for pick in itertools.combinations(range(3), extra):
                sub = span(core + [outer[k] for k in pick])
                assert dim(sub) == rho, ('construction lost a dimension',
                                         rho, dim(sub))
                got_s = dim(isect(sub, sigx))
                got_c = dim(isect(sub, pix))
                assert (got_s, got_c) == (dsig, cwant), \
                    ('the constructed shape is not the intended one',
                     got_s, dsig, got_c, cwant)
                proj = rank([wedge3(v, point) for v in sub])
                assert got_s == rho - proj, \
                    ('rank-nullity for q_hat FAILED', rho, got_s, proj)
                measured = rho - got_c
                predicted = proj + (1 if got_s >= 3 else 0)
                shapes += 1
                realized.setdefault(rho, set()).add(got_c)
                if measured != predicted:
                    broken.append((rho, got_s, got_c, measured, predicted))
                break
    print(f'  {shapes} shapes CONSTRUCTED, spanning every realizable '
          f'`(rho, dim cap Sigma_x, c)` triple.')

    # ---- (BE-211): the realizable range
    print('  (BE-211) THE REALIZABLE RANGE of `c_j(Pi_x)`, by `rho_j`:')
    for rho in sorted(realized):
        lo, hi = max(0, rho - 4), min(2, rho)
        assert realized[rho] == set(range(lo, hi + 1)), \
            ('the realizable range is not the Grassmann interval',
             rho, sorted(realized[rho]), lo, hi)
        print(f'    rho = {rho}:  c in {sorted(realized[rho])}   '
              f'= [max(0, rho-4), min(2, rho)] = [{lo}, {hi}]  ASSERTED')
    assert 0 not in realized[5] and 0 not in realized[6], \
        'c = 0 is realizable at rho >= 5 after all'
    assert realized[6] == {2}, 'rho = 6 does not force c = 2'
    print('    So `(BE-G_2a)` (`c_j(Pi_x) = 0`) is UNSATISFIABLE at '
          '`rho_j >= 5` and `c_j = 2` is')
    print('    FORCED at `rho_j = 6` -- a THIRD containment mechanism, the '
          'AMBIENT one, which no')
    print('    hypothesis can exclude.  It is also HARMLESS: `e_j = rho_j - '
          'c_j >= 3` there.')

    # ---- (BE-212): the grading
    print(f'  (BE-212) (BE-206)\'s GRADING `e_i = dim(rho_bar_i ^ p_x) + '
          f'[Sigma_x <= rho_bar_i]`:')
    print(f'    it FAILS at {len(broken)} of the {shapes} constructed shapes '
          f'-- exactly the branch where')
    print('    `c = dim(rho_bar cap Sigma_x) - 1` with '
          '`dim(rho_bar cap Sigma_x) <= 2`:')
    for row in broken:
        print(f'      rho={row[0]} dim cap Sigma_x={row[1]} c={row[2]}:  '
              f'e = {row[3]} but the grading predicts {row[4]}')
    assert broken, 'the grading did not fail anywhere -- re-read (BE-206)'
    assert all(r[2] < 2 for r in broken), \
        'the grading failed somewhere with c = 2'
    print('    EVERY failure has `c < 2`, ASSERTED -- so the grading is '
          'sound exactly on the')
    print('    FIRING branch `c_i(Pi_x) = 2`, which is the only branch '
          '`befourp.run_peel` asserts it')
    print('    on; and there `dim(rho_bar_i cap Sigma_x) in {2,3}` is forced, '
          'so the grading says')
    print('    no more than `e_i = rho_i - 2`.  Hence `(BE-F_4)` IS the floor '
          '`rho_i >= 4`, and')
    print('    `q_hat` is a change of variables rather than a new handle on '
          'it.')
    print(f'  rungs: {time.time() - t0:.1f}s')
    return len(broken)


# ========================================= mode: hunt  (BE-214)

KILLJOBS = [
    ('K33', ('A', 'B'), 4, '2 pendants + theta(3,3,3)'),
    ('prism', ('A', 'E'), 4, '2 pendants + theta(3,3,3)'),
    ('K33', ('D', 'E'), 4, '2 pendants + theta(3,3,3)'),
    ('K33', ('A', 'B'), 5, '2 pendants + theta(3,3,3)'),
]

SWEEP_SIDES = ['2 pendants + theta(3,3,3)', '2 pendants + theta(3,3,4)',
               '2 pendants + theta(3,4,4)',
               '2 pendants + cycle(6) at distance 3',
               '2 pendants + cycle(8) at distance 4',
               '2 pendants + K4 subdivided x3']
SWEEP_HUBS = {'K33': [('A', 'B'), ('A', 'C'), ('D', 'E')],
              'prism': [('A', 'E'), ('B', 'D')]}
SWEEP_PROFS = {'K33': [2, 3, 4], 'prism': [2, 3, 4]}


def _one_peel(skname, hubs, plen, sidename):
    """One `bproper.plant_peel` row with EVERY habitat gate reported.  The
    construction is the predecessor's; what is new is the uniform profile
    length `plen` (BEFOURP and `bline.legal_peel` both hardcode 3) and the
    measurement of the NON-FIRING side's containment."""
    prof = [plen] * len(SKELETONS[skname])
    edges_side, _xt, _yt = side_named(sidename)
    rng = random.Random(SEED + 7 * len(sidename) + plen * 31)
    got = plant_peel(skname, prof, hubs, edges_side, rng)
    if got is None:
        return None
    egraph, raw_side, _other_raw, node_x, node_y, aff, _ppi = got
    split = delta_pair(egraph, node_x, node_y)
    if split is None:
        return None
    _da, _db, part_a, part_b = split
    side_near = part_a if len(part_a) == len(raw_side) else part_b
    side_far = part_b if side_near is part_a else part_a
    if len(side_near) != len(raw_side):
        return None
    row = e_row(egraph, node_x, node_y, side_near, side_far, aff)
    if row is None:
        return None
    nb = neighbors(egraph)
    okh, _ws, _br, _ha = hcard_ok_piece(egraph, node_x, node_y)
    gates = dict(
        hcard=okh,
        mindeg=min(len(nb[w]) for w in {w for e in egraph for w in e}),
        girth=girth(egraph),
        nonadj=node_y not in nb[node_x],
        degx=len(nb[node_x]), degy=len(nb[node_y]),
        rnode_far=rnode_shaped(side_far, node_x, node_y),
        rnode_near=rnode_shaped(side_near, node_x, node_y),
        partition=len(side_near) + len(side_far) == len(egraph),
        witness=verify_pencil_witness(egraph, aff)[0],
        regime=flag_frame(egraph, aff, node_x, node_y) is not None,
        deg_near_x=len(neighbors(side_near).get(node_x, ())),
        deg_far_x=len(neighbors(side_far).get(node_x, ())),
    )
    return egraph, node_x, node_y, aff, row, gates, side_near


def run_hunt():
    t0 = time.time()
    print(f'== hunt: (BE-214) THE KILL -- `(BE-G_2)` INSIDE the regime at an '
          f'R-node-shaped side 2, seed {SEED}')
    print('  BEFOURP\'s kill condition, CORRECTED by (BE-215): not any '
          '`c_j(Pi_x) >= 1` mechanism (the')
    print('  ambient forces one at `rho_j >= 5` harmlessly) but `e_j <= 1`, '
          'i.e. `c_j >= rho_j - 1`')
    print('  with `rho_j <= 3`.  BEFOURP\'s own 21 in-regime rows and '
          '`bline.legal_peel` both hardcode')
    print('  the profile length 3; this varies it, which is the ONLY change '
          'to the construction.')
    kills, checked = [], 0
    for (skname, hubs, plen, sidename) in KILLJOBS:
        got = _one_peel(skname, hubs, plen, sidename)
        assert got is not None, ('the peel did not build', skname, hubs, plen)
        egraph, node_x, node_y, aff, row, gates, side_near = got
        checked += 1
        # EVERY gate a predecessor asserts, asserted here.
        assert gates['hcard'] and gates['mindeg'] >= 2 \
            and gates['girth'] >= 4, ('(CH-1) fails on H', skname, gates)
        assert gates['nonadj'], ('x ~ y', skname)
        assert gates['degx'] >= 3 and gates['degy'] >= 3, \
            ('a terminal is not a hub of H', skname, gates)
        assert gates['rnode_far'], ('side 2 is not R-node-shaped', skname)
        assert gates['partition'], ('the sides do not partition H', skname)
        assert gates['witness'], 'plant_peel returned a non-witness'
        assert gates['regime'], \
            ('the row is OFF the generic flag regime', skname)
        assert row['d'][0] >= 1 and row['d'][1] >= 1, \
            ('a side is rigid -- (BE-E4\') is vacuous here', skname)
        fires = [i for i in (0, 1) if row['cX'][i] == 2]
        assert fires, ('the (BE-E4\') hypothesis does not fire', skname)
        # (BE-175)(i)'s mechanism, on the NON-FIRING side, measured.
        point = hat(aff[node_x])
        near_nbrs = sorted(neighbors(side_near).get(node_x, ()), key=str)
        assert gates['deg_near_x'] == 1, \
            ('side 1 is not a series end at x', skname, gates)
        hinge = wedge2(point, hat(aff[near_nbrs[0]]))
        assert contains(row['S1'], [hinge]), \
            '(BE-175)(i): ell is NOT in rho_bar_1'
        assert contains(row['Pix'], [hinge]), \
            '(BE-175)(i): ell is NOT in Pi_x'
        holds_g2 = all(row['e'][1 - i] >= 2 for i in fires)
        holds_e4 = row['e'][0] + row['e'][1] >= 4
        assert not holds_g2, ('(BE-G_2) HOLDS here', skname, row['e'])
        assert holds_e4, ('(BE-E4\') FAILS here -- a bigger claim', skname)
        assert 0 not in fires, \
            'the firing side is side 1 -- the asymmetry is not exhibited'
        kills.append((skname, hubs, plen, row['t'], row['e'],
                      row['r'], row['cX'], row['d']))
        print(f'  -- {skname} {hubs} profile {plen}, side 1 '
              f'`{sidename}`  |V| = '
              f'{len({w for e in egraph for w in e})}, |E| = {len(egraph)}')
        print(f'     (CH-1): hcard {gates["hcard"]}, min deg '
              f'{gates["mindeg"]} >= 2, girth {gates["girth"]} >= 4;  '
              f'x !~ y {gates["nonadj"]};')
        print(f'     deg_H(x) = {gates["degx"]} >= 3, deg_H(y) = '
              f'{gates["degy"]} >= 3;  side 2 R-node-shaped '
              f'{gates["rnode_far"]},')
        print(f'     side 1 R-node-shaped {gates["rnode_near"]};  pencil '
              f'witness {gates["witness"]};  flag_frame NON-None '
              f'{gates["regime"]}.')
        print(f'     rho = {row["r"]}, c(Pi_x) = {row["cX"]}, e = '
              f'{row["e"]}, delta = {row["d"]}, a = {row["a"]};  firing side '
              f'= {[i + 1 for i in fires]}.')
        print(f'     deg_1(x) = {gates["deg_near_x"]} (SERIES END), deg_2(x) '
              f'= {gates["deg_far_x"]};  `ell = p_x ^ p_c` in '
              f'`rho_bar_1 cap Pi_x` ASSERTED.')
        print(f'     ** `(BE-G_2)` FALSE (e_j = {row["e"][0]}); (BE-E4\') '
              f'HOLDS, margin '
              f'{row["e"][0] + row["e"][1] - 4}; rho_1 + rho_2 = '
              f'{row["r"][0] + row["r"][1]}. **')
    print(f'  `(BE-G_2)` is REFUTED at {len(kills)} of {checked} fully-gated '
          f'peels, on TWO skeletons,')
    print('  THREE hub pairs and TWO profile lengths, every row inside the '
          'generic flag regime.')
    print('  THE MECHANISM IS (BE-175)(i) ITSELF: side 1 carries the series '
          'end at `x`, so (BE-45)(i)')
    print('  + (CH-1) put `ell = p_x ^ p_c` into `rho_bar_1 cap Pi_x`.  '
          '(BE-175)(ii)\'s `rnode_shaped`')
    print('  exclusion is indexed to SIDE 2; `(BE-G_g)`\'s subject is the '
          'NON-FIRING side.  The two')
    print('  coincide only when the FIRING side is the non-R-node one -- '
          'BEFOURP\'s 21 rows -- and')
    print('  here the firing side is the SKELETON side, so neither added '
          'hypothesis reaches side 1.')

    # ---- the census the caps are stated over
    print('  -- the in-regime census the verdict\'s cap is stated over --')
    rows, g2bad, e4bad, cens = 0, 0, 0, {}
    for skname in ('K33', 'prism'):
        for hubs in SWEEP_HUBS[skname]:
            for plen in SWEEP_PROFS[skname]:
                for sidename in SWEEP_SIDES:
                    got = _one_peel(skname, hubs, plen, sidename)
                    if got is None:
                        continue
                    _eg, _nx, _ny, _aff, row, gates, _sn = got
                    if not gates['regime'] or not gates['rnode_far']:
                        continue
                    rows += 1
                    key = (row['r'], row['cX'], row['e'])
                    cens[key] = cens.get(key, 0) + 1
                    fires = [i for i in (0, 1) if row['cX'][i] == 2]
                    if not fires or row['d'][0] < 1 or row['d'][1] < 1:
                        continue
                    if not all(row['e'][1 - i] >= 2 for i in fires):
                        g2bad += 1
                    if row['e'][0] + row['e'][1] < 4:
                        e4bad += 1
    print(f'     {rows} rows in-regime with side 2 R-node-shaped '
          f'(2 skeletons x 5 hub pairs x 3 profile')
    print(f'     lengths x {len(SWEEP_SIDES)} bucket-A side-1 pieces, one '
          f'seed each).  `(rho, c, e)` census:')
    for key, num in sorted(cens.items(), key=str):
        print(f'       {num:3d}  rho = {key[0]}, c(Pi_x) = {key[1]}, '
              f'e = {key[2]}')
    print(f'     `(BE-G_2)` FAILS at {g2bad} firing both-flexible rows; '
          f'**(BE-E4\') FAILS at {e4bad}**.')
    assert g2bad > 0, 'the sweep did not reproduce the kill'
    assert e4bad == 0, \
        '(BE-E4\') FAILED in the regime -- that is a BIGGER claim than this ' \
        'direction makes; re-read before recording it'
    print('     So (BE-E4\') is NOT refuted here, and the reason is '
          '(BE-210)\'s own cap: at')
    print('     `rho_i = 6` the firing side already supplies `e_i = 4`.  '
          'The SAME elementary bound')
    print('     that makes `(BE-G_2)` free at `rho_j >= 4` is what saves the '
          'clause where it fails.')
    print(f'  hunt: {time.time() - t0:.1f}s')
    return len(kills)


def run_validate():
    print('== validate: arith + rungs + hunt in one process')
    run_arith()
    run_rungs()
    run_hunt()


def main(argv):
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        return 0
    mode = argv[0].lstrip('-')
    if mode == 'arith':
        run_arith()
    elif mode == 'rungs':
        run_rungs()
    elif mode == 'hunt':
        run_hunt()
    elif mode == 'validate':
        run_validate()
    else:
        print(f'unknown mode {mode!r}')
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
