"""
Direction BCORNER (arc ordinal 93) -- PROVE OR REFUTE `(BE-OBL)`: at an
internal R-node peel in the generic flag regime, `c_i(Pi_x) = 2` AND
`c_j(Pi_x) >= 1` ==> `rho_i = 6`.  BOBLIG's successor ((BE-230)(ii)), section 8's
named smallest first slice for the naked `Pi_x` obligation at `a = 0`.

  THE ANSWER, said at the top: `(BE-OBL)` is **REFUTED**, as stated, on a
  population that has been TRACKED AND LANDED since BSIGMA and that no
  direction re-read against it -- `bsigma.degenerate_peel` over
  `bsigma.price_jobs()`.  Every row there carries `rho_1 = 5` and
  `c_1(Pi_x) = 2` BY ASSERTION (BSIGMA's own, `bsigma.run_price`), is in the
  generic flag regime (`bsatur.row_of` returns None otherwise) and is an
  internal R-node peel (`bsatur.peel_of`'s gate).  What no one measured is
  `c_2(Pi_x)`, and it is `>= 1` at 62 of 78 rows.  That is `(BE-OBL)`'s
  hypothesis met and its conclusion false.

  AND, INDEPENDENTLY OF THE REFUTATION -- the arithmetic half, which stands
  even if a reader rejects the witness: `(BE-OBL)` is NOT a reduction of the
  obligation on the rung that carries the obligation's content.  Split the
  324 `a = 0` tuples by BOBLIG's own ladder ((BE-225)):

    rung 3  `Sigma_delta <= 6`  141 tuples, 26 of the 30 residue violations
            -- `(BE-OBL)` and the obligation are THE SAME PREDICATE, 0
            disagreements, and there is a two-line proof that they must be.
    rung 2  `Sigma_delta = 7`    48 tuples,  4 residue violations
            -- `(BE-OBL)` is strictly stronger; 8 over-strength tuples.
            THIS IS THE ONLY RUNG ON WHICH IT IS A REDUCTION AT ALL.
    rung 1  `Sigma_delta >= 8`  135 tuples,  0 residue violations
            -- the obligation is a hypothesis-free THEOREM ((BE-225)(i)) and
            `(BE-OBL)` still demands `rho_i = 6`: 34 over-strength tuples,
            pure surplus.  47% of its failure set lives here.

  MODES
    arith    the rung decomposition, the over-strength census, the rung-3
             identity and the Grassmann-free locus of the added hypothesis
             -- cap-free over `barch.all_tuples()`, no sampling, no seed.
             Every claim an `assert`.
    kill     THE REFUTATION.  `bsigma.degenerate_peel` over
             `bsigma.price_jobs()`, re-read against `(BE-OBL)`'s OWN
             predicate rather than against the obligation's margin, with the
             full row `(rho, c, delta, a, slack, deg_1(x), deg_2(x))`
             reported at every row and the habitat gates asserted.
    degfree  THE SCOPE OF THE KILL.  Which of the dispatch's NARROWER
             hypotheses -- `a = (0,0)`, side-degree `>= 2` on the FIRING
             side -- the refuting rows meet, measured rather than argued,
             and how `c_2(Pi_x) >= 1` is supplied at each.
    cell     the proposed `(K-bare)` gap-map RECOMPUTE (the row is at 2 828
             of a 2 856-word cap, so a landing here cannot append) and its
             F21 label-preservation check, against the LIVE row read through
             `check-gapmap-cells.iter_row_cells`.  Re-takeable at landing
             time, which is the point: a sibling may move the row first.
    validate  all four in one process.

  NOTATION, stated ONCE for the whole file, and read at the definition sites
  rather than from a docstring (`barch.slack_of`, `barch.all_tuples`,
  `barch.ps_full`, `bsatur.row_of`, `bsatur.peel_of`, `bsigma.degenerate_peel`,
  `bsigma.price_jobs`, `bpeel.rnode_shaped`, `bunif.flag_frame`).
  `V := Lambda^2 K^4`; `c_i(U) := dim(rho_bar_i cap U)`; `dim Pi_x = 2`;
  `slack := max(0, delta_1 + delta_2 - 6)`; `a_i := dim M_i - 6 - f_i`;
  `rho_i = delta_i + a_i`.  The `Pi_x` OBLIGATION is
  `c_1(Pi_x) + c_2(Pi_x) <= 2 + slack` -- (BE-100)(i)'s inequality.
  `(PENCIL-SATURATES)` is `barch.ps_full`.  `(BE-OBL)` is section
  (K-bare-ext) (BE-228)(i)'s clause, quoted there WITH its hypotheses:
  *at an internal R-node peel in the generic flag regime, `c_i(Pi_x) = 2`
  and `c_j(Pi_x) >= 1` implies `rho_i = 6`* -- note that it carries NO
  `a = 0` hypothesis and NO side-degree hypothesis, which is exactly the
  gap between the clause and the dispatch's quantifier that `degfree`
  measures.  The GRASSMANN FLOOR, hypothesis-free and BOBLIG's own standing
  notation: `dim(rho_bar_i cap Pi_x) >= rho_i + 2 - 6`, so
  `c_i >= max(0, rho_i - 4)`.

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is NEVER called from this file -- its silent
  `Lambda^2 K^4 -> K^4` truncation is therefore unreachable here.  (It IS
  called inside `bsigma.degenerate_peel`, but only on `K^4` subspaces --
  the plane `Ppi` and the hub flags `B[z]`, all of `dim <= 3` in `K^4` --
  so the truncation cannot fire there either; checked at the call sites.)
  No width-12 object is built: every measured number comes from
  `bsatur.row_of`, whose rows are `bunif.profile`/`bimage.rho_bar_of`
  output.  `bwin` is not imported.  NO TRACKED SCRIPT IS MODIFIED: every
  configuration comes from a predecessor's own builder, called and never
  re-implemented, so the figure-invariance obligation discharges by
  `git diff --name-only -- '*.py'` naming only this new file.  No Python
  local is named with a capital letter followed by a digit, so the registry's
  capital-letter-plus-digit grep returns nothing minted here.  Two NAMED
  labels are minted in the draft this file backs -- `BE-OBL7` and `BE-OBLK`,
  the rung-restricted and habitat-restricted successors -- and both are
  verified 0-hit as raw substrings corpus-wide at the baseline.

  CAPS AND BLIND AXES, disclosed up front and repeated at each mode.
  `kill` inherits `bsigma.price_jobs()`'s support ENTIRELY: 39 constructed
  profiles over the three `bpeel.SKELETONS`, peeled branch fixed at 5 and
  every other branch in {3, 4, 5}, two seeds each, `s = 20`, `tries = 400`.
  A profile that fails to draw within `tries` is SILENTLY DROPPED, which is
  a population-selection effect and not a null result.  The peeled branch
  being fixed at 5 is `degenerate_peel`'s own construction (it realizes
  `Sigma_x <= rho_bar_1` at `rho_1 = 5`), so `rho_1 != 6` is BUILT IN, not
  found -- which is precisely why the population is a legitimate witness
  for a REFUTATION and worthless as evidence for a proof.
"""

import os
import sys
import time
import random

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors, hat                                 # noqa: E402
from bimage import contains, dim                                     # noqa: E402
from bunif import SEED, flag_frame                                   # noqa: E402
from bpeel import rnode_shaped                                       # noqa: E402
from bsatur import peel_of, row_of, sigma_at                         # noqa: E402
from bsigma import degenerate_peel, price_jobs                       # noqa: E402
from kbare_common import verify_pencil_witness                       # noqa: E402
import barch as BA                                                   # noqa: E402

PIX = ('Pix',)


# ------------------------------------------------------------------ helpers

def obl_tup(t):
    """The `Pi_x` OBLIGATION at a tuple: `barch.violates` as landed, negated.
    `du = dim Pi_x = 2` is (BE-100)(i)'s."""
    d1, d2, _a1, _a2, _r1, _r2, c1, c2 = t
    return not BA.violates(c1, c2, 2, d1, d2)


def beobl_tup(t):
    """`(BE-OBL)` at a tuple, BOTH orderings of `(i, j)`: `c_i = 2` and
    `c_j >= 1` ==> `rho_i = 6`.  Cross-check that this predicate is BOBLIG's:
    `(BE-228)(i)` reports `(BE-OBL)` holding at 56 `a = 0` tuples where
    `(PENCIL-SATURATES)` fails, and `arith` asserts that number."""
    _d1, _d2, _a1, _a2, r1, r2, c1, c2 = t
    return not ((c1 == 2 and c2 >= 1 and r1 != 6)
                or (c2 == 2 and c1 >= 1 and r2 != 6))


def gfloor_ok(t):
    """(BE-213)(i)'s Grassmann conjunct, BOBLIG's `floor_legal`:
    `c_i >= max(0, rho_i - 4)`.  `barch.all_tuples` enforces only the cap."""
    return t[6] >= max(0, t[4] - 4) and t[7] >= max(0, t[5] - 4)


def beobl_row(row):
    """`(BE-OBL)` read off a MEASURED row (`bsatur.row_of`'s dict)."""
    c1, c2 = row['c1'][PIX], row['c2'][PIX]
    r1, r2 = row['r1'], row['r2']
    return not ((c1 == 2 and c2 >= 1 and r1 != 6)
                or (c2 == 2 and c1 >= 1 and r2 != 6))


def obl_row(row):
    return row['c1'][PIX] + row['c2'][PIX] <= 2 + row['slack']


def census(dic):
    return '{' + ', '.join(f'{k}: {v}' for k, v in sorted(dic.items(),
                                                          key=str)) + '}'


# ================================================ mode: arith  (BE-234)-(BE-236)

def run_arith():
    t0 = time.time()
    print('== arith: (BE-234)-(BE-236) THE RUNG DECOMPOSITION OF `(BE-OBL)` '
          '-- cap-free')
    print('  `barch.all_tuples()` in full, then the `a = 0` slice.  No '
          'sampler, no seed, no')
    print('  draw: every sentence below is an `assert` over a complete '
          'enumeration.')
    allt = list(BA.all_tuples())
    zt = [t for t in allt if t[2] == 0 and t[3] == 0]
    print(f'  {len(allt)} tuples in all; {len(zt)} at `a = (0,0)`.')
    assert len(zt) == 324, ('the `a = 0` tuple count moved', len(zt))

    # ---- the predicate is BOBLIG's.  (BE-228)(i)'s own strictness figure.
    psfail = [t for t in zt if not BA.ps_full(t)]
    bofail = [t for t in zt if not beobl_tup(t)]
    agree = len(psfail) - len(bofail)
    print(f'  CROSS-CHECK that this file\'s `(BE-OBL)` predicate IS BOBLIG\'s:'
          f' (PENCIL-SATURATES)')
    print(f'  fails at {len(psfail)} of the 324, `(BE-OBL)` fails at '
          f'{len(bofail)}, so `(BE-OBL)` holds at')
    print(f'  {agree} tuples where item 0(a)\'s clause fails -- '
          f'(BE-228)(i)\'s own "56", reproduced.')
    assert agree == 56, ('(BE-228)(i)\'s strictness figure did not '
                         'reproduce -- the predicate is not BOBLIG\'s', agree)
    # every (BE-OBL) failure is a (PENCIL-SATURATES) failure: it is strictly weaker
    assert all(not BA.ps_full(t) for t in bofail), \
        '`(BE-OBL)` failed where (PENCIL-SATURATES) holds -- not weaker'

    # ---- SOUNDNESS: (BE-228)(i)'s implication, re-asserted.
    unsound = [t for t in zt if beobl_tup(t) and not obl_tup(t)]
    assert not unsound, ('(BE-228)(i) is WRONG: `(BE-OBL)` holds and the '
                         'obligation fails', unsound[:3])
    viol = [t for t in zt if not obl_tup(t)]
    assert len(viol) == 30, ('(BE-227)(ii)\'s residue moved', len(viol))
    assert all(max(t[4], t[5]) <= 5 for t in viol), \
        '(BE-227)(ii)\'s `max rho <= 5` did not reproduce'
    print(f'  (BE-228)(i) re-asserted: `(BE-OBL)` implies the obligation at '
          f'all 324, 0 escapes;')
    print(f'  (BE-227)(ii) re-asserted: the residue is {len(viol)} tuples, '
          f'every one at `max rho <= 5`.')

    # ---- (BE-235): the rung decomposition.
    print()
    print('  (BE-235) THE RUNG DECOMPOSITION.  BOBLIG\'s own ladder '
          '((BE-225)) applied to its own')
    print('  successor.  "over-strength" = `(BE-OBL)` FAILS while the '
          'obligation HOLDS: a tuple')
    print('  where refuting `(BE-OBL)` costs the obligation NOTHING.')
    rungs = (('rung 3  Sd <= 6', 0, 6), ('rung 2  Sd  = 7', 7, 7),
             ('rung 1  Sd >= 8', 8, 12))
    tally = {}
    for (nm, lo, hi) in rungs:
        sub = [t for t in zt if lo <= t[0] + t[1] <= hi]
        v = [t for t in sub if not obl_tup(t)]
        b = [t for t in sub if not beobl_tup(t)]
        over = [t for t in sub if not beobl_tup(t) and obl_tup(t)]
        tally[nm] = (len(sub), len(v), len(b), len(over))
        print(f'    {nm}: {len(sub):3d} tuples | obligation fails '
              f'{len(v):2d} | `(BE-OBL)` fails {len(b):2d} | '
              f'OVER-STRENGTH {len(over):2d}')
    assert tally['rung 3  Sd <= 6'] == (141, 26, 26, 0), \
        ('rung 3 moved', tally['rung 3  Sd <= 6'])
    assert tally['rung 2  Sd  = 7'] == (48, 4, 12, 8), \
        ('rung 2 moved', tally['rung 2  Sd  = 7'])
    assert tally['rung 1  Sd >= 8'] == (135, 0, 34, 34), \
        ('rung 1 moved', tally['rung 1  Sd >= 8'])

    # ---- (BE-234)(i): the rung-3 IDENTITY, enumerated then proved.
    r3 = [t for t in zt if t[0] + t[1] <= 6]
    dis = [t for t in r3 if obl_tup(t) != beobl_tup(t)]
    assert not dis, ('rung 3 is NOT an identity', dis[:3])
    print()
    print(f'  (BE-234) THE RUNG-3 IDENTITY.  On `Sigma_delta <= 6` at '
          f'`a = 0` the two predicates')
    print(f'  AGREE AT ALL {len(r3)} TUPLES -- 0 disagreements -- so on the '
          f'rung that carries')
    print(f'  {tally["rung 3  Sd <= 6"][1]} of the 30 residue violations '
          f'`(BE-OBL)` IS the obligation, not a reduction of it.')
    print('  PROOF, two lines, so the enumeration is a check and not the '
          'evidence.  At `a = 0`,')
    print('  `Sigma_delta <= 6` gives `slack = 0`, so the obligation is '
          '`c_1 + c_2 <= 2` ((BE-225)(iii)).')
    print('  (<==) If the obligation holds and `c_i = 2` then `c_j = 0`, so '
          '`(BE-OBL)`\'s hypothesis')
    print('  is never met.  (==>) If `(BE-OBL)` holds and `c_1 + c_2 >= 3` '
          'then some `c_i = 2` with')
    print('  `c_j >= 1`, so `rho_i = 6`; but `rho_i = delta_i <= '
          'Sigma_delta <= 6` forces `delta_j = 0`,')
    print('  hence `c_j <= rho_j = 0`, contradicting `c_j >= 1`.  QED')
    # the proof's own step, asserted rather than trusted
    for t in r3:
        if beobl_tup(t) and t[6] + t[7] >= 3:
            raise AssertionError(('the rung-3 proof is wrong', t))

    # ---- (BE-236): the over-strength census.
    over = [t for t in zt if not beobl_tup(t) and obl_tup(t)]
    assert len(over) == 42, ('the over-strength count moved', len(over))
    assert min(t[0] + t[1] for t in over) == 7, \
        'an over-strength tuple appeared below rung 2'
    overg = [t for t in over if gfloor_ok(t)]
    from collections import Counter
    print()
    print(f'  (BE-236) THE OVER-STRENGTH CENSUS.  `(BE-OBL)` fails at '
          f'{len(bofail)} of the 324; at {len(over)}')
    print(f'  of those the obligation HOLDS.  Grassmann-floor-legal '
          f'((BE-213)(i)): {len(overg)} of {len(over)}.')
    print('    by Sigma_delta: ' + census(dict(Counter(
        t[0] + t[1] for t in over))))
    print('    by c(Pi_x)    : ' + census(dict(Counter(
        (t[6], t[7]) for t in over))))
    # NOT derived from the Grassmann-legal count printed above: that is a
    # different subset that happens to have the same size.  Counted separately
    # from `tally`, and the connective says so.
    print(f'  SEPARATELY COUNTED: {tally["rung 1  Sd >= 8"][3]} of `(BE-OBL)`\'s '
          f'{len(bofail)} failure tuples -- '
          f'{100 * tally["rung 1  Sd >= 8"][3] // len(bofail)}% -- sit on '
          f'rung 1, where')
    print('  (BE-225)(i) has ALREADY made the obligation a hypothesis-free '
          'theorem.  A refutation')
    print('  of `(BE-OBL)` there costs the obligation nothing at all, which '
          'is why one was cheap.')

    # ---- the added hypothesis is free on a SECOND locus (BE-234)(ii).
    print()
    print('  (BE-234)(ii) THE ADDED HYPOTHESIS HAS A SECOND FREE MECHANISM.  '
          '(BE-228)(iii) names')
    print('  one -- a series end at `x` on side `j`, where (BE-175)(i) gives '
          '`c_j >= 1`.  The')
    print('  GRASSMANN FLOOR gives a second, with no series end, no degree '
          'hypothesis and no')
    print('  genericity: `c_j >= max(0, rho_j - 4)`, so `rho_j >= 5 ==> '
          'c_j >= 1` at EVERY')
    print('  configuration.  On that locus `(BE-OBL)` IS (PENCIL-SATURATES), '
          'verbatim.')
    gf = [t for t in zt if gfloor_ok(t)]
    for t in gf:
        for (ci, cj, rj) in ((t[6], t[7], t[5]), (t[7], t[6], t[4])):
            if ci == 2 and rj >= 5:
                assert cj >= 1, ('the Grassmann floor did not fire', t)
    gfree = [t for t in gf if not beobl_tup(t) and obl_tup(t)
             and ((t[6] == 2 and t[5] >= 5) or (t[7] == 2 and t[4] >= 5))]
    print(f'  Over-strength tuples on which the added hypothesis is '
          f'GRASSMANN-FREE: {len(gfree)}.')
    print('    ' + census(dict(Counter(
        f'rho={(t[4], t[5])} c={(t[6], t[7])}' for t in gfree))))
    assert gfree, 'the Grassmann-free over-strength locus is empty'
    assert all(t[0] + t[1] >= 7 for t in gfree), \
        'a Grassmann-free over-strength tuple below rung 2'

    # ---- the restricted successor, for (BE-237).
    def beobl7(t):
        return (t[0] + t[1] >= 8) or beobl_tup(t)
    assert all(obl_tup(t) for t in zt if beobl7(t)), \
        'the rung-restricted successor is NOT sufficient'
    r7fail = sum(1 for t in zt if not beobl7(t))
    r7over = sum(1 for t in zt if not beobl7(t) and obl_tup(t))
    print()
    print(f'  (BE-237) THE REPAIR THAT COSTS NOTHING.  `(BE-OBL)` restricted '
          f'to `Sigma_delta <= 7`')
    print(f'  is STILL sufficient for the obligation at `a = 0` (asserted '
          f'over all 324, 0 escapes),')
    print(f'  because rung 1 is (BE-225)(i).  It fails at {r7fail} tuples '
          f'against {len(bofail)}, and its')
    print(f'  over-strength drops from {len(over)} to {r7over}.  And it '
          f'SURVIVES the `kill` witness:')
    print('  every refuting row there sits at `Sigma_delta` in {10, 11}, '
          'i.e. on rung 1, which the')
    print('  restriction excludes -- asserted in `kill`, not assumed here.  '
          'On rung <= 2 the added')
    print('  hypothesis cannot come from the Grassmann floor at all: '
          '`rho_j >= 5` with `c_i = 2`')
    print('  forces `rho_i <= 2`, hence `rho_bar_i = Pi_x` exactly.  So the '
          'restricted successor')
    print('  is the honest one, and it is UNREFUTED rather than proved.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return dict(over=len(over), bofail=len(bofail), tally=tally,
                gfree=len(gfree), r7fail=r7fail, r7over=r7over)


# ------------------------------------------------------- the measured rows

def _kill_rows(nseed=2, cap=None):
    """Every fully-gated row `bsigma.degenerate_peel` produces over
    `bsigma.price_jobs()`, with `(BE-OBL)`'s own predicate read off it.

    THE SAMPLER'S SUPPORT, named as clause 3 requires.  `price_jobs()` is
    39 constructed profiles over `bpeel.SKELETONS` -- `K4` with the peeled
    branch at 5 and the others in {3,4,5}, plus `prism`/`K33` at uniform
    {3,4} with one branch at 5 -- and `nseed` draws each at `s = 20`,
    `tries = 400`.  WHICH OF `(BE-OBL)`'s OWN VARIABLES IT VARIES:
    `c_2(Pi_x)`, `rho_2`, `delta_2`, `a_2` and `deg_2(x)` all vary; `rho_1`
    is PINNED AT 5 and `c_1(Pi_x)` at 2 by the construction, and
    `deg_1(x) = 1` is forced because side 1 is the peeled branch, a path.
    Those three are the axes this population CANNOT vary, and they are
    exactly why it is a refutation witness and not evidence for a proof."""
    jobs = price_jobs()
    if cap:
        jobs = jobs[:cap]
    out = []
    for (skname, prof, ei) in jobs:
        for sd in range(nseed):
            rng = random.Random(SEED + 613 * sd + 7 * sum(prof) + ei)
            got = degenerate_peel(skname, prof, ei, rng)
            if got is None:
                continue
            egraph, node_x, node_y, side1, side2, aff, _ppi = got
            row = row_of(egraph, node_x, node_y, side1, side2, aff)
            if row is None:          # `flag_frame` is None: off the regime
                continue
            # ---- BSIGMA's own two asserts, re-run here rather than trusted.
            assert row['r1'] == 5, ('rho_1 moved off the construction',
                                    skname, prof, row['r1'])
            assert contains(row['S1'], sigma_at(hat(aff[node_x]))), \
                ('Sigma_x is not inside rho_bar_1', skname, prof)
            assert row['c1'][PIX] == 2, ('c_1(Pi_x) is not 2', skname, prof)
            # ---- the habitat gates, asserted and not inferred.
            assert flag_frame(egraph, aff, node_x, node_y) is not None, \
                'row_of returned a row off the generic flag regime'
            okw, _ = verify_pencil_witness(egraph, aff)
            assert okw, ('the builder returned a non-witness', skname, prof)
            assert set(map(frozenset, side1)) | set(map(frozenset, side2)) \
                == set(map(frozenset, egraph)), 'the sides do not cover H'
            assert len(side1) != len(side2), \
                ('equal edge counts -- the side identification is ambiguous',
                 skname, prof)
            # ---- rank/dimension guards on the sampled object.
            assert dim(row['S1']) == row['r1'] and dim(row['S2']) == row['r2'], \
                'rho_bar dimensions disagree with the reported rho'
            gates = dict(
                rnode1=rnode_shaped(side1, node_x, node_y),
                rnode2=rnode_shaped(side2, node_x, node_y),
                deg1x=len(neighbors(side1).get(node_x, ())),
                deg2x=len(neighbors(side2).get(node_x, ())))
            assert gates['rnode1'] or gates['rnode2'], \
                'neither side is R-node-shaped -- not an internal R-node peel'
            out.append((skname, tuple(prof), ei, sd, row, gates))
    return out


# ================================================== mode: kill  ((BE-231)-(BE-233))

def run_kill(nseed=2, cap=None):
    t0 = time.time()
    print(f'== kill: (BE-231)-(BE-233) `(BE-OBL)` IS REFUTED, seed {SEED}')
    print('  The population is `bsigma.degenerate_peel` over '
          '`bsigma.price_jobs()` -- (BE-109)\'s')
    print('  own construction, TRACKED AND LANDED since BSIGMA, run here '
          'with NO harness edit')
    print('  and NO new builder.  What is new is the QUANTITY read off each '
          'row: `(BE-OBL)`\'s')
    print('  predicate rather than the obligation\'s margin.  BSIGMA\'s '
          '`run_price` prints the')
    print('  `(c_1, c_2)` census that contains the kill and reads it against '
          'the obligation only.')
    rows = _kill_rows(nseed=nseed, cap=cap)
    assert rows, 'the degenerate-peel population produced no rows at all'
    kills = [r for r in rows if not beobl_row(r[4])]
    oblfail = [r for r in rows if not obl_row(r[4])]
    from collections import Counter
    ccen = Counter((r[4]['c1'][PIX], r[4]['c2'][PIX]) for r in rows)
    rcen = Counter((r[4]['r1'], r[4]['r2']) for r in rows)
    acen = Counter((r[4]['a1'], r[4]['a2']) for r in rows)
    dcen = Counter((r[4]['d1'], r[4]['d2']) for r in rows)
    gcen = Counter((r[5]['deg1x'], r[5]['deg2x']) for r in rows)
    print()
    print(f'  {len(rows)} fully-gated rows over {len(price_jobs())} '
          f'constructed profiles ({nseed} draws each).')
    print(f'  EVERY row: `rho_1 = 5` asserted, `c_1(Pi_x) = 2` asserted, '
          f'`Sigma_x <= rho_bar_1`')
    print(f'  asserted, `flag_frame` non-None asserted, '
          f'`verify_pencil_witness` asserted,')
    print(f'  R-node-shaped asserted.')
    print('    `c(Pi_x)`      : ' + census(dict(ccen)))
    print('    `(rho_1,rho_2)`: ' + census(dict(rcen)))
    print('    `(delta_1,d_2)`: ' + census(dict(dcen)))
    print('    `(a_1, a_2)`   : ' + census(dict(acen)))
    print('    `(deg_1(x),deg_2(x))`: ' + census(dict(gcen)))
    print()
    print(f'  ** `(BE-OBL)` FAILS AT {len(kills)} OF {len(rows)} ROWS. **   '
          f'(the obligation fails at {len(oblfail)})')
    assert kills, \
        ('`(BE-OBL)` was NOT refuted on this population -- the direction\'s '
         'headline is wrong')
    # ---- the witness, printed in full so the draft can quote one row.
    wit = sorted(kills, key=lambda r: (r[4]['c2'][PIX], str(r[0]), r[1]))[0]
    skname, prof, ei, sd, row, gates = wit
    print(f'  THE WITNESS (lexicographically first of {len(kills)}): '
          f'`{skname}{prof}` peeled at skeleton edge {ei}, draw {sd}')
    print(f'    rho = ({row["r1"]}, {row["r2"]}), '
          f'c(Pi_x) = ({row["c1"][PIX]}, {row["c2"][PIX]}), '
          f'delta = ({row["d1"]}, {row["d2"]}), '
          f'a = ({row["a1"]}, {row["a2"]}), slack = {row["slack"]}')
    print(f'    deg_1(x) = {gates["deg1x"]}, deg_2(x) = {gates["deg2x"]}, '
          f'rnode(side 1) = {gates["rnode1"]}, rnode(side 2) = '
          f'{gates["rnode2"]}')
    print(f'    `(BE-OBL)` hypothesis: c_1(Pi_x) = 2 and c_2(Pi_x) = '
          f'{row["c2"][PIX]} >= 1.  Conclusion demanded: rho_1 = 6.')
    print(f'    MEASURED: rho_1 = {row["r1"]}.  FALSE.')
    # ---- and the obligation is untouched at every kill row.
    safe = [r for r in kills if obl_row(r[4])]
    print()
    print(f'  (BE-232) WHAT THE KILL COSTS THE OBLIGATION: at {len(safe)} of '
          f'the {len(kills)} refuting rows the')
    print('  OBLIGATION ITSELF STILL HOLDS.  So this refutes the successor '
          'without touching the')
    print('  target -- exactly the `arith` over-strength region, realized on '
          'configurations.')
    assert len(safe) == len(kills), \
        ('a refuting row ALSO violates the obligation -- that would be a '
         'shortfall and a far bigger event; check it before recording')
    # ---- WHICH RUNG the kill lives on.  This is the claim `arith`'s
    # ---- closing paragraph rests on, so it is asserted here and not there.
    sdk = sorted({r[4]['d1'] + r[4]['d2'] for r in kills})
    print(f'  (BE-232)(ii) THE RUNG OF THE KILL: every refuting row sits at '
          f'`Sigma_delta` in {sdk} --')
    print('  all of them on RUNG 1 (`Sigma_delta >= 8`), where (BE-225)(i) '
          'has already made the')
    print('  obligation a hypothesis-free theorem.  So `(BE-OBL)` '
          'RESTRICTED TO `Sigma_delta <= 7`')
    print('  SURVIVES this witness, and that restriction is still '
          'sufficient for the obligation.')
    assert min(sdk) >= 8, \
        ('a refuting row sits at Sigma_delta <= 7 -- the rung-restricted '
         'successor is refuted too, and `arith`\'s closing paragraph must '
         'be rewritten', sdk)
    print(f'  kill: {time.time() - t0:.1f}s')
    return dict(rows=rows, kills=kills, ccen=dict(ccen), rcen=dict(rcen),
                acen=dict(acen), gcen=dict(gcen))


# ============================================== mode: degfree  ((BE-233))

def run_degfree(nseed=2, cap=None):
    t0 = time.time()
    print(f'== degfree: (BE-233) THE SCOPE OF THE KILL, measured, seed {SEED}')
    print('  `(BE-OBL)` AS STATED ((BE-228)(i)) carries NO `a = 0` hypothesis '
          'and NO side-degree')
    print('  hypothesis; the DISPATCH\'s quantifier adds both.  This mode '
          'measures which of the')
    print('  narrower hypotheses the refuting rows meet, rather than '
          'arguing it.')
    rows = _kill_rows(nseed=nseed, cap=cap)
    kills = [r for r in rows if not beobl_row(r[4])]
    assert kills, 'no refuting rows to scope'
    azero = [r for r in kills if (r[4]['a1'], r[4]['a2']) == (0, 0)]
    firing_deg2 = []
    for r in kills:
        row, g = r[4], r[5]
        # a refutation whose FIRING side has side-degree >= 2 at x
        if row['c2'][PIX] == 2 and row['c1'][PIX] >= 1 and row['r2'] != 6 \
                and g['deg2x'] >= 2:
            firing_deg2.append(r)
    print(f'  {len(kills)} refuting rows.')
    print(f'    `a = (0,0)` at {len(azero)} of them.')
    print(f'    refuting with the FIRING side at side-degree >= 2 at `x`: '
          f'{len(firing_deg2)}.')
    print(f'    side 1 is the peeled branch, a path, so `deg_1(x) = 1` at '
          f'every row BY CONSTRUCTION')
    print('    (`bsatur.peel_of` makes side 1 the branch itself) -- that '
          'axis is fenced here, and')
    print('    un-fencing it is NOT this direction\'s claim.')
    # ---- WHERE does `c_2(Pi_x) >= 1` come from?  Three candidate mechanisms.
    from collections import Counter
    src = Counter()
    for r in kills:
        row, g = r[4], r[5]
        c2, r2 = row['c2'][PIX], row['r2']
        if c2 < 1:
            continue
        if r2 >= 5:
            src['Grassmann floor (rho_2 >= 5)'] += 1
        elif g['deg2x'] == 1:
            src['(BE-175)(i) series end on side 2'] += 1
        else:
            src['NEITHER -- incidental, at rho_2 <= 4 and deg_2(x) >= 2'] += 1
    print()
    print('  HOW `c_2(Pi_x) >= 1` IS SUPPLIED AT THE REFUTING ROWS:')
    for k, v in sorted(src.items(), key=str):
        print(f'    {v:3d}  {k}')
    print('  (BE-228)(iii) names only the series-end mechanism; `arith` adds '
          'the Grassmann floor.')
    print('  Any count in the third bucket is a THIRD mechanism neither '
          'names -- the added')
    print('  hypothesis is simply MET, with no structural reason, which is '
          'the honest reading')
    print('  of why the restriction bought less protection than it looked '
          'like it would.')
    print(f'  degfree: {time.time() - t0:.1f}s')
    return dict(kills=len(kills), azero=len(azero),
                firing_deg2=len(firing_deg2), src=dict(src))


# ================================================ mode: cell  (the F21 gate)

# The THREE edits this direction proposes to the `(K-bare)` gap-map row's
# combined status cell.  Kept HERE, in the driver, because the word count and
# the label-preservation figure are figures like any other and the standing
# rule is that a figure comes from a committed script.  `gapdiff.py` is the
# canonical gate and the coordinator runs it AFTER applying these; this mode
# is what lets the proposal be checked BEFORE, from a read-only tree.
CELL_EDITS = [
    # (1) BOBLIG's block, compressed, plus BCORNER's own findings.
    ("**AND THE NAKED OBLIGATION IS DECOMPOSED (BOBLIG).**",
     "**OPEN** ((BE-230)).",
     "**THE NAKED OBLIGATION DECOMPOSED (BOBLIG), ITS SUCCESSOR THEN KILLED "
     "(BCORNER).** `c₁+c₂ ≤ 4` free: `Σδ ≥ 8` "
     "⟹ TRUE, `= 7` ⟹ *not both fire*, `≤ 6` **IS** "
     "(NO-DOUBLE-PENCIL), residue EXACTLY `Σδ ≤ 7` ((BE-225)); "
     "no per-side floor below 6 suffices, two cheapest members **REFUTED** by "
     "(BE-175)(i) ((BE-226)); modular law **CIRCULAR**, residue **30** "
     "`a = 0` tuples at `max ρ ≤ 5` ((BE-227)); successor "
     "**`(BE-OBL)`** = item 0(a) ∧ `c_j(Π_x) ≥ 1` ((BE-228)), "
     "un-fenced at `deg₁(x) = 2`, 0 violations at 135/135 "
     "((BE-229)/(BE-230)). **`(BE-OBL)` IS REFUTED**: 62 of 78 in-regime "
     "`a = (0,0)` R-node rows of BSIGMA's landed `degenerate_peel`, "
     "`ρ₁ = 5`, `c(Π_x) = (2,≥1)` ((BE-231)), the "
     "obligation HOLDING 62/62 ((BE-232)); `c_j ≥ 1` GRASSMANN-FREE at "
     "`ρ_j ≥ 5` ((BE-213)(i)) — the mechanism (BE-228)(iii) "
     "omits — supplies it 62/62 ((BE-233)/(BE-234)). `(BE-OBL)` **IS** "
     "the obligation at `Σδ ≤ 6` (0 disagreements, 26 of 30), "
     "stronger at `= 7`, surplus at `≥ 8` ((BE-235)/(BE-236)); the "
     "`Σδ ≤ 7` restriction stays sufficient, SURVIVES "
     "((BE-237)); (BE-227)(i)'s *equivalent* one-directional ((BE-238)). "
     "**STILL OPEN.**"),
    # (2) the duplicated one-line recap in the closing survey unit.
    ("now **DECOMPOSED** to a `Σδ` ladder, a 30-tuple residue and "
     "`(BE-OBL)` ((BE-225)–(BE-230)).", None,
     "**DECOMPOSED**, then `(BE-OBL)` **REFUTED** ((BE-225)–(BE-238))."),
    # (3) BGTWOA's frontier detail.  The frontier is DEAD ("all FIVE die")
    # and its successor is now dead too, so the intermediate rungs compress
    # to their verdicts.  Every label token is kept -- asserted below.
    ("`c_j(Π_x) ≤ dim Π_x = 2` gives",
     "so all FIVE die ((BE-215)).",
     "`c_j(Π_x) ≤ 2` gives `e_j ≥ ρ_j − 2` FREE, so "
     "`(BE-G_2)` is a THEOREM at `ρ_j ≥ 4`, FALSE at "
     "`ρ_j ≤ 1`, content the rungs `ρ_j ∈ {2,3}`, DISJOINT "
     "from BSTEER's ((BE-210)); `(BE-G_2a)` UNSATISFIABLE at "
     "`ρ_j ≥ 5`, realizable range EXACTLY "
     "`max(0,ρ−4) ≤ c ≤ min(2,ρ)` ((BE-211)); "
     "(BE-206)'s grading a TAUTOLOGY where asserted, so **`(BE-F_4)` IS the "
     "floor `ρ_i ≥ 4`** ((BE-212)); `barch.all_tuples` omits "
     "`c_i ≥ ρ_i − 4`, frontier PROTECTED ((BE-213)); "
     "**`(BE-G_2)` FALSE at 4/4 gated in-regime peels** "
     "(`ρ = (2,6)`, `c = (1,2)`), by **(BE-175)(i) ITSELF** on the "
     "NON-FIRING side ((BE-214)); every survivor implies it, all FIVE die "
     "((BE-215))."),
]

# `gapdiff.py`'s OWN label regex, copied verbatim from its source so this
# mode and the canonical gate agree on what a label is.
CODE_RE = __import__('re').compile(
    r"\(([A-Z][A-Za-z0-9′+]*(?:-[A-Za-z0-9′+]+)+)\)"
    r"(\((?:[ivx]+|\+|[a-z]\d?|[A-Z]\d?)\))?")

WORD_CAP, WORD_TARGET = 2856, 2780


def _labels(text):
    out = set()
    for mt in CODE_RE.finditer(text):
        out.add(mt.group(1))
        if mt.group(2):
            out.add(mt.group(1) + mt.group(2))
    return out


def _live_cell():
    """The `(K-bare)` combined status cell, read through
    `notes/check-gapmap-cells.py`'s OWN parser (`iter_row_cells`) -- the same
    one `gapdiff.py` and `notes/gapmap.py` use, so all three agree on what a
    row and a cell are.  NEVER `sed`/`grep`: the row is one 19 000-character
    line."""
    import importlib.util
    # four levels: notes/scripts/w4/bcorner.py -> repo root.  (`gapdiff.py`
    # uses three because it sits one directory shallower.)
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__)))))
    gate = os.path.join(root, 'notes', 'check-gapmap-cells.py')
    doc = os.path.join(root, 'notes', 'pencil', 'workbook', 'gapmap.md')
    spec = importlib.util.spec_from_file_location('gapcells', gate)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    with open(doc, encoding='utf-8') as fh:
        text = fh.read()
    for (_ln, key, _c1, _c2, kind, cells) in mod.iter_row_cells(text):
        if key == 'K-bare':
            assert kind == 'combined' and len(cells) == 1, \
                ('the (K-bare) row changed shape', kind, len(cells))
            return cells[0]
    raise AssertionError('the (K-bare) row was not found')


def run_cell():
    t0 = time.time()
    print('== cell: the proposed `(K-bare)` RECOMPUTE and its F21 '
          'label-preservation check')
    print('  The deciding row is at 2 828 of a 2 856-word cap, so a landing '
          'here is a RECOMPUTE,')
    print('  not an append.  The three edits are constants in this file; '
          '`gapdiff.py` remains the')
    print('  canonical gate and the coordinator runs it after applying '
          'them.')
    cell = _live_cell()
    print(f'  live cell: {len(cell)} chars / {len(cell.split())} words '
          f'(cap {WORD_CAP})')
    new, applied, already = cell, 0, 0
    for (head, tail, repl) in CELL_EDITS:
        if repl in new:
            already += 1
            continue
        idx = new.find(head)
        assert idx >= 0, ('an edit anchor is not in the live cell -- the row '
                          'moved under this proposal; re-take it', head[:48])
        end = (idx + len(head)) if tail is None else \
            (new.find(tail, idx) + len(tail))
        assert end > idx, ('the closing anchor is missing', tail)
        old = new[idx:end]
        print(f'    edit {applied + already + 1}: {len(old.split()):3d} -> '
              f'{len(repl.split()):3d} words')
        new = new[:idx] + repl + new[end:]
        applied += 1
    if already:
        print(f'  {already} of {len(CELL_EDITS)} edits are ALREADY APPLIED '
              f'in the working tree.')
    nw = len(new.split())
    print(f'  proposed : {len(new)} chars / {nw} words   '
          f'(target <= {WORD_TARGET}, cap {WORD_CAP})')
    old_l, new_l = _labels(cell), _labels(new)
    dropped, added = sorted(old_l - new_l), sorted(new_l - old_l)
    print(f'  labels {len(old_l)} -> {len(new_l)};  DROPPED: '
          f'{dropped or "NONE"}')
    print(f'  ADDED  : {added}')
    assert not dropped, ('F21 VIOLATED: the recompute drops labels', dropped)
    if applied:
        assert nw <= WORD_TARGET, \
            ('the recompute misses its own word target', nw, WORD_TARGET)
    assert nw <= WORD_CAP, ('the recompute BUSTS the cap', nw, WORD_CAP)
    print(f'  cell: {time.time() - t0:.1f}s')
    return dict(words_before=len(cell.split()), words_after=nw,
                dropped=dropped, added=added)


# ============================================================= entry point

def run_validate():
    print('== validate: a reduced run of all four modes')
    run_arith()
    print()
    run_kill(nseed=1, cap=10)
    print()
    run_degfree(nseed=1, cap=10)
    print()
    run_cell()
    return True


MODES = {'arith': run_arith, 'kill': run_kill, 'degfree': run_degfree,
         'cell': run_cell, 'validate': run_validate}


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: bcorner.py [{"|".join(MODES)}]')
        return 2
    print(f'--- BCORNER / {mode} --- seed {SEED} --- exact Q ---')
    MODES[mode]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
