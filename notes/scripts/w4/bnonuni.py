"""
Direction BNONUNI (arc ordinal 90 if this round's two landings are
ordered BNONUNI-first; the coordinator reconciles the tally) -- IS `(BE-E4')` REFUTED OR A THEOREM ON
ITS EXACT RESIDUE ZONE `rho_1 + rho_2 <= 7`?

  THE ANSWER, said at the top: NEITHER, AND THAT IS A DECISION.  The residue
  zone SPLITS at 5/6, and on both halves the clause is dead:

  (BE-218) THE AXIS IS REAL AND THE HARNESS CHANGE IS ONE DEFAULTED
           PARAMETER.  `delta_2` for the subdivided skeleton is
           QUANTIZED to {0, 3, 6} along the UNIFORM profile axis every
           landed driver varies (`bgtwoa`'s `plen`, `bproper.run_peel`'s
           `prof`) and takes EVERY value in {0, 1, 2, 3} along the
           NON-UNIFORM axis, exhaustively over 512 profiles per hub pair,
           with the closed form `delta_2 = max(0, #{length-3 branches} - 6)`
           asserted at all 3 072.  Branch length 1 is PARTIALLY excluded --
           it makes two skeleton hubs adjacent, so the samplers' shape guard
           bites at 5 of 6 (job, seed) pairs -- which is why every figure
           here is quoted off entries `>= 2`.

  (BE-219) THE ARITHMETIC, AND IT IS THE FINDING.  (i) HYPOTHESIS-FREE: at
           a firing side `c_i(Pi_x) = 2` gives `e_i = rho_i - 2` exactly, so
              `e_1 + e_2 >= 4`  <==>  `c_j(Pi_x) <= rho_1 + rho_2 - 6`,
           and since `c_j >= 0` this makes (BE-E4') **FALSE at EVERY firing
           configuration with `rho_1 + rho_2 <= 5`** -- no hypothesis, no
           genericity, no draw.  (BE-216)'s residue `rho_1+rho_2 <= 7`
           therefore contains a zone on which the clause is UNSATISFIABLE,
           and only a realization is needed to turn that into a refutation.
           (ii) At `a_1 = a_2 = 0` -- S-mark's own pin, (BE-22)(iii)'s
           attaining case -- `rho_i = delta_i`, so on `rho_1+rho_2 >= 6` the
           condition in (i) is `c_j <= delta_1+delta_2-6 = slack`, which IS
           the `Pi_x` obligation `c_1 + c_2 <= 2 + slack` verbatim.  So there
           (BE-E4') is not a reduction of the obligation -- it IS the
           obligation.  Exhaustive over `barch.all_tuples()`, `barch.e4` and
           `barch.violates` as landed.

  (BE-220) SO THE (BE-101)(i) ROUTE THROUGH (E4) IS CIRCULAR AT `a = 0`.
           (BE-153)(i) flagged exactly this trap and ruled it out on the
           ground that the hypothesis is `c_i(Pi_x) = 2` rather than "the
           obligation fails".  That repair works OFF `a = 0` and not ON it:
           the clause's entire content is `a_1 + a_2 > 0`, and (BE-101)(ii)
           applies it at `a_1 = a_2 = 0`.  Measured: of the 2 080 firing
           both-flexible tuples EXACTLY the 1 270 with `a_1 + a_2 > 0` have
           (E4) true where the `Pi_x` obligation is false, and every one of
           the 15 `a = 0` escapes at `rho_1 + rho_2 >= 6` IS a `Pi_x`
           violation.  AND THAT CONTENT IS OUTSIDE THE ATTAINABLE REGIME:
           every one of those 1 270 has
           `min(delta_1+delta_2, 6) + a_1 + a_2 > 6 = dim Lambda^2 K^4`, so
           by (BE-22)(iii) as corrected by (BE-86)(i) the composite CANNOT
           attain there.  Of the 3 375 firing tuples, 688 are
           attainment-compatible, and at those the clause is EXACTLY the
           obligation (538) or strictly stronger hence FALSE (150) --
           nothing else occurs.  **So (BE-E4') can never contribute to
           (BE-14).**

  (BE-221) THE KILL, GEOMETRIC.  A fully-gated in-regime peel --
           `prism (A,E)`, profile `[2,2,3,3,3,3,3,3,3]`, side 1
           `2 pendants + theta(3,4,4)` -- with
              `rho = (4, 1)`, `c(Pi_x) = (2, 0)`, `e = (2, 1)`,
              `delta = (2, 1)`, `a = (2, 0)`,  so  `e_1 + e_2 = 3 < 4`:
           **(BE-E4') IS REFUTED**, inside the generic flag regime
           (`flag_frame` non-None), with side 2 `rnode_shaped`, both sides
           flexible, and `rho_i = delta_i + a_i` at BOTH sides -- so the row
           is INSIDE `barch.all_tuples`' space, which is the second
           disqualifier (BE-208)(ii) used on its own 48.  14 refuting rows
           in all, 4 of them inside that space, at `rho_1 + rho_2 = 5` --
           the bottom of (BE-216)'s residue.  Side 1 is BEFOURP's own
           (BE-118)(ii)/(BE-207)(i) firing piece, byte unchanged; the ONLY
           thing moved is side 2's profile.

  (BE-222) THE CENSUS the caps are stated over, and the boundary is EXACT:
           over the same construction at `delta_2 = 1, 2, 3` the clause
           fails exactly where `rho_1 + rho_2 <= 5` and holds exactly where
           `rho_1 + rho_2 >= 6`, which is (BE-219)(ii)/(iii)'s split measured rather
           than derived.

  (BE-223) WHAT SURVIVES, AND THE SUCCESSOR'S EXACT STRENGTH.  (BE-216)'s
           `rho_1 + rho_2 >= 8` theorem is untouched; so is the `Pi_x`
           obligation itself, which is what (BE-E4') turns out to BE at
           `a = 0` on `rho_1 + rho_2 >= 6`.  At `a = 0` (PENCIL-SATURATES)
           implies that obligation at all 324 tuples (0 counterexamples) and
           the converse fails at 98, so
           the NAKED obligation is STRICTLY WEAKER than half (B)'s item
           0(a) clause -- which makes it the honest successor, and makes the
           whole two-sided clause family a target strictly ABOVE the one it
           was introduced to reduce.  Nothing landed is refuted beyond
           (BE-E4') -- (BE-207)/(BE-208)/(BE-210)-(BE-216) all reproduced.

  (BE-224) the verdict, the board, sect. 8, the bars, the E-rider.

  MODES
    map     (BE-218)  the profile axis, EXHAUSTIVE over entries in {2,3}
            for both skeletons and every non-adjacent hub pair; plus the
            length-1 exclusion, measured.
    arith   (BE-219)/(BE-220)  exhaustive over the 6 400 tuples; no
            sampling, seed unused.  Every claim an `assert`.
    hunt    (BE-221)/(BE-222)  the kill witness and the census, every
            habitat gate asserted through `bline.legal_peel` itself.
    validate  all three in one process.

  NOTATION AND THE (L3) QUALIFICATION, stated ONCE for the whole file.
  Every `(E4)` below means **`section (K-bare-ext) (E4)`** -- the two-sided
  clause of (BE-153)(i), a grandfathered bare token with a recorded
  collision (`notes/Pencil-labels.md`) -- and `(BE-E4')` is its
  `delta_i >= 1` restriction, (BE-162)'s repair.  `e_i := rho_i - c_i(Pi_x)`,
  `c_i(U) := dim(rho_bar_i cap U)`, `slack := max(0, delta_1 + delta_2 - 6)`,
  and `a_i := dim M_i - 6 - f_i` is side `i`'s own attainment loss, all as
  BARCH's standing notation has them.  The (L6) appearance-collision rename
  is applied pre-emptively: no Python local here is named `E1`/`E2`/`A1` or
  anything else that the (L6) capital-letter-plus-digit grep would
  return (`esk` for the
  subdivided skeleton, `near`/`far` for the two sides).

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is never called.  No width-12 object is built: every
  `span`/`isect`/`dim`/`contains` call takes width-6 rows, `bimage.span`'s
  `d == 6` branch.  `bwin` is not imported.  Every configuration comes from
  `bproper.plant_peel`, a predecessor's own builder.  The gate set is
  `bline.legal_peel`'s OWN, called rather than re-implemented (BGTWOA's
  `_one_peel` re-implements it; this driver does not, which is why the one
  tracked edit is a DEFAULTED `prof=` parameter on `legal_peel` rather than
  a fourth copy of the gate list).
"""

import os
import sys
import time
import random
import itertools

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors                                      # noqa: E402
from bunif import SEED, flag_frame                                   # noqa: E402
from bproper import (plant_peel, side_named, PEELJOBS,                # noqa: E402
                     NONADJ)
from bpeel import SKELETONS, delta_pair, rnode_shaped, subdivided    # noqa: E402
from bdecor import d3, weld_d3                                       # noqa: E402
from bline import legal_peel                                         # noqa: E402
from bfour import e_row                                              # noqa: E402
from kbare_common import verify_pencil_witness                       # noqa: E402
import barch as BA                                                   # noqa: E402


# ------------------------------------------------------------------ helpers

def firing(tup):
    """The sides whose (BE-E4') hypothesis fires: `c_i(Pi_x) = 2`, which
    (BE-156)(i) shows IS `Pi_x <= rho_bar_i`.  BGTWOA's `firing`."""
    return [i for i in (0, 1) if tup[6 + i] == 2]


def flexible(tup):
    """(BE-162)(i)'s added hypothesis: both sides non-rigid."""
    return tup[0] >= 1 and tup[1] >= 1


def e4prime(tup):
    """(BE-E4'): section (K-bare-ext) (E4) restricted to `delta_i >= 1`."""
    return True if not flexible(tup) else BA.e4(tup)


def pix_ok(tup):
    """The `Pi_x` OBLIGATION at the block `U = Pi_x`, `dim U = 2` --
    `barch.violates` as landed, negated.  This is the inequality
    (BE-101)(i)'s redundancy theorem is about and (E4) exists to thin."""
    d1, d2, _a1, _a2, _r1, _r2, c1, c2 = tup
    return not BA.violates(c1, c2, 2, d1, d2)


def lam2_ok(tup):
    """The `U = Lambda^2 K^4` obligation, `dim U = 6`: `rho_1 + rho_2 <=
    6 + slack`, which (BE-101)(ii) shows is automatic at `a = 0`."""
    d1, d2, _a1, _a2, r1, r2, _c1, _c2 = tup
    return not BA.violates(r1, r2, 6, d1, d2)


def floor_legal(tup):
    """(BE-213)'s missing conjunct: Grassmann in `Lambda^2 K^4` forces
    `c_i(Pi_x) >= rho_i - 4`.  `barch.all_tuples` enforces only the upper
    cap.  Respected wherever a tuple is quoted as REALIZABLE."""
    return tup[6] >= max(0, tup[4] - 4) and tup[7] >= max(0, tup[5] - 4)


# ================================================= mode: map   ((BE-218))

def delta2_of(skname, prof, xy):
    """`delta_2` of the subdivided skeleton read as the side of the 2-cut
    `{x, y}` -- `bfour.side_nums`' own combinatorial half."""
    esk = list(subdivided(SKELETONS[skname], list(prof)))
    return d3(esk) - weld_d3(esk, xy[0], xy[1])


def run_map():
    t0 = time.time()
    print('== map: (BE-218) THE PROFILE AXIS -- what UNIFORM cannot reach')
    print('  `bpeel.subdivided(skel, lengths)` reads `lengths[i]` PER')
    print('  SKELETON EDGE, so a non-uniform list is already a legal input;')
    print('  what is uniform is the DRIVERS.  `bgtwoa` varies one `plen`,')
    print('  `bproper.run_peel` defaults to `[3]*n`, and `bline.legal_peel`')
    print('  hardcoded `[3]*n` with no parameter at all until this landing.')
    print('  -- the UNIFORM axis, both skeletons, every non-adjacent pair:')
    unif = {}
    for skname in ('K33', 'prism'):
        n = len(SKELETONS[skname])
        for xy in NONADJ[skname]:
            vals = []
            for plen in range(1, 8):
                vals.append(delta2_of(skname, [plen] * n, xy))
            unif[(skname, xy)] = vals
            print(f'     {skname} {xy}: plen 1..7 -> delta_2 = {vals}')
    reached = sorted({v for vals in unif.values() for v in vals})
    assert reached == [0, 3, 6], ('the uniform axis is not quantized to '
                                  '{0,3,6}', reached)
    print(f'     UNIFORM reaches exactly {reached} -- ASSERTED.  This is why')
    print('     BGTWOA\'s 90-row census has `rho_2 in {0,3,6}` ((BE-216)(iii)).')
    print('  -- the NON-UNIFORM axis, EXHAUSTIVE over entries in {2,3}:')
    allseen = {}
    for skname in ('K33', 'prism'):
        n = len(SKELETONS[skname])
        for xy in NONADJ[skname]:
            seen = {}
            for prof in itertools.product((2, 3), repeat=n):
                seen.setdefault(delta2_of(skname, prof, xy), []).append(prof)
            allseen[(skname, xy)] = seen
            cens = {k: len(v) for k, v in sorted(seen.items())}
            print(f'     {skname} {xy}: {2 ** n} profiles, delta_2 census '
                  f'{cens}')
            assert sorted(seen) == [0, 1, 2, 3], \
                ('{2,3}-profiles do not reach every delta_2 in 0..3',
                 skname, xy, sorted(seen))
            # the closed form the census exhibits: delta_2 = max(0, k - 6)
            # with k the number of length-3 branches.
            for d, profs in seen.items():
                for pr in profs:
                    k = sum(1 for L in pr if L == 3)
                    assert d == max(0, k - 6), \
                        ('delta_2 is not max(0, #3-branches - 6)', pr, d)
    print('     EVERY value of delta_2 in {0,1,2,3} is reached, ASSERTED at')
    print('     each of the 6 (skeleton, hub pair) cases; and the closed form')
    print('     `delta_2 = max(0, #{branches of length 3} - 6)` is ASSERTED at')
    print(f'     all {6 * 512} profiles.  So `delta_2 = 1` and `= 2` -- the')
    print('     values the uniform axis SKIPS -- are one list away.')
    for skname in ('K33', 'prism'):
        for xy in NONADJ[skname]:
            for d in (1, 2):
                ex = allseen[(skname, xy)][d][0]
                print(f'       {skname} {xy} delta_2 = {d}: e.g. {list(ex)}  '
                      f'({len(allseen[(skname, xy)][d])} profiles)')
    print('  -- the LENGTH-1 rung, MEASURED rather than assumed:')
    n = len(SKELETONS['K33'])
    pr1 = [1] + [3] * (n - 1)
    ok1, tot1, njob = 0, 0, 0
    for (skname, xy, s1name) in PEELJOBS[:3]:
        m = len(SKELETONS[skname])
        E1t, _xt, _yt = side_named(s1name)
        prz = [1] + [3] * (m - 1)
        lp = legal_peel(E1t, skname, xy, prz)
        assert lp is not None, ('a length-1 profile does not build a peel',
                                skname, xy)
        njob += 1
        for sd in range(2):
            tot1 += 1
            rng = random.Random(SEED + 613 * sd + 7 * len(s1name))
            if plant_peel(skname, prz, xy, E1t, rng, tries=40) is not None:
                ok1 += 1
    print(f'     {pr1} and its siblings are TOPOLOGICALLY legal at every one')
    print(f'     of the first {njob} peel jobs (`bline.legal_peel` returns a '
          f'report), but')
    print(f'     `bproper.plant_peel` places only {ok1} of {tot1} '
          f'(job, seed) pairs at 40 tries: a branch of')
    print('     length 1 is a REAL hub-hub edge, so two skeleton hubs are '
          'adjacent and the')
    print('     samplers\' `no hub adjacent to a hub` shape guard bites. '
          'DISCLOSED as a')
    print('     PARTIAL, not a total, exclusion -- the length-1 rung is '
          'reachable and')
    print('     unreliable, which is why every figure below is quoted off '
          'entries `>= 2`.')
    assert 0 < ok1 < tot1, \
        ('the length-1 rung is either fully placeable or fully excluded -- '
         're-read (BE-218)', ok1, tot1)
    print(f'  map: {time.time() - t0:.1f}s')
    return allseen


# =============================================== mode: arith  ((BE-219)/(BE-220))

def run_arith():
    t0 = time.time()
    print('== arith: (BE-219)/(BE-220) THE ARITHMETIC -- '
          'hypothesis-free, then at `a = 0`; exhaustive')
    T = list(BA.all_tuples())
    assert len(T) == 6400, ('the tuple space moved', len(T))
    print(f'  {len(T)} tuples (`barch.all_tuples`, so `rho_i = delta_i + a_i`')
    print('  by construction -- read at source, not from the docstring).')

    # ---- (BE-219)(i): the HYPOTHESIS-FREE core, over ALL 6 400 tuples
    fall = [t for t in T if firing(t)]
    for t in fall:
        fi = firing(t)
        srho = t[4] + t[5]
        if len(fi) == 1:
            j = 1 - fi[0]
            assert BA.e4(t) == (t[6 + j] <= srho - 6), \
                ('the one-sided rewriting of (E4) is wrong', t)
        else:
            assert BA.e4(t) == (srho >= 8), \
                ('the both-firing rewriting of (E4) is wrong', t)
        if srho <= 5:
            assert not BA.e4(t), \
                ('(E4) HOLDS at a firing tuple with rho_1 + rho_2 <= 5', t)
    n5 = sum(1 for t in fall if t[4] + t[5] <= 5)
    n5f = sum(1 for t in fall if t[4] + t[5] <= 5 and floor_legal(t))
    print(f'  (BE-219)(i) HYPOTHESIS-FREE, over all {len(fall)} FIRING '
          f'tuples: `c_i(Pi_x) = 2` gives')
    print('     `e_i = rho_i - 2` exactly, so `e_1 + e_2 >= 4` IS '
          '`c_j(Pi_x) <= rho_1 + rho_2 - 6`')
    print('     (and `rho_1 + rho_2 >= 8` when BOTH sides fire) -- asserted '
          'tuple by tuple')
    print(f'     against `barch.e4`.  Since `c_j >= 0`, **(E4) is FALSE at '
          f'ALL {n5} firing')
    print(f'     tuples with `rho_1 + rho_2 <= 5`** -- asserted -- of which '
          f'{n5f} are')
    print('     Grassmann-floor-legal ((BE-213)).  No hypothesis, no '
          'genericity, no draw:')
    print('     the clause cannot be a THEOREM there, only unrealized.')
    assert n5f > 0, 'the whole Sigma_rho <= 5 zone is floor-illegal'

    # ---- (BE-219)(ii): the identity, tuple by tuple
    zero = [t for t in T if t[2] == 0 and t[3] == 0]
    fz = [t for t in zero if firing(t)]
    print(f'  `a_1 = a_2 = 0`: {len(zero)} tuples, {len(fz)} of them FIRING.')
    hi = [t for t in fz if t[0] + t[1] >= 6]
    lo = [t for t in fz if t[0] + t[1] <= 5]
    for t in fz:
        d1, d2 = t[0], t[1]
        j = 1 - firing(t)[0] if len(firing(t)) == 1 else None
        cj = t[6 + j] if j is not None else None
        # the clause, rewritten: e_1 + e_2 >= 4 <=> c_j <= Sigma_delta - 6
        if cj is not None:
            assert BA.e4(t) == (cj <= d1 + d2 - 6), \
                ('the rewriting of (E4) at a = 0 is wrong', t)
    for t in hi:
        assert BA.e4(t) == pix_ok(t), \
            ('(E4) and the Pi_x obligation DIFFER at a = 0, '
             'Sigma_delta >= 6', t)
    print(f'  (BE-219)(ii) at `a = 0`, `delta_1 + delta_2 >= 6` ({len(hi)} firing '
          f'tuples):')
    print('     **`(E4)` and the `Pi_x` OBLIGATION are the SAME CONDITION** '
          '-- asserted')
    print('     tuple by tuple, `barch.e4` against `barch.violates(c1,c2,2,'
          'd1,d2)`.')
    for t in lo:
        assert not BA.e4(t), \
            ('(E4) HOLDS at a = 0 with Sigma_delta <= 5', t)
    nlo_ok = sum(1 for t in lo if pix_ok(t))
    print(f'  (BE-219)(iii) at `a = 0`, `delta_1 + delta_2 <= 5` ({len(lo)} firing '
          f'tuples):')
    print(f'     **`(E4)` is FALSE at ALL {len(lo)}** -- asserted -- while the')
    print(f'     `Pi_x` obligation HOLDS at {nlo_ok} of them.  So there the')
    print('     clause is STRICTLY STRONGER than its own target and')
    print('     UNSATISFIABLE: `e_1 + e_2 = delta_1 + delta_2 - c_1 - c_2 <= '
          '5 - 2 = 3`.')
    assert nlo_ok > 0, 'the obligation never holds at Sigma_delta <= 5'

    # ---- (BE-219)(iv): so at a = 0 the clause implies its conclusion
    #      TRIVIALLY, and (BE-153)(ii)'s "0 escapes" is that triviality.
    esc0 = [t for t in zero if BA.e4(t) and not pix_ok(t)]
    assert not esc0, ('a Pi_x violation survives (E4) at a = 0', esc0[:3])
    lam0 = [t for t in zero if not lam2_ok(t)]
    assert not lam0, ('a Lambda^2 violation at a = 0', lam0[:3])
    print(f'  (BE-219)(iv) (BE-153)(ii)\'s own figure REPRODUCED: 0 `Pi_x`')
    print('     violations survive (E4) at `a = 0`, and 0 `Lambda^2 K^4`')
    print('     violations exist there at all -- so (BE-101)(i)\'s')
    print('     implication is TRUE at `a = 0` for the trivial reason that')
    print('     its hypothesis IS its conclusion, not because it reduces.')

    # ---- (BE-220): where the clause DOES have content
    print('  == (BE-220) SO THE CLAUSE\'S WHOLE CONTENT IS `a_1 + a_2 > 0` ==')
    fl = [t for t in T if flexible(t) and firing(t)]
    esc = [t for t in fl if not e4prime(t)]
    print(f'  {len(fl)} firing both-flexible tuples; {len(esc)} escape '
          f'(BE-E4\').')
    assert len(esc) == 245, ('(BE-216)\'s 245 escapes moved', len(esc))
    cens = {}
    for t in esc:
        cens[t[4] + t[5]] = cens.get(t[4] + t[5], 0) + 1
    print(f'  (BE-216)(ii) REPRODUCED: `rho_1 + rho_2` census of the escapes '
          f'= {dict(sorted(cens.items()))}')
    assert max(cens) == 7, 'the residue zone is not rho_1 + rho_2 <= 7'
    split = {}
    for t in esc:
        key = ('Sigma_rho <= 5' if t[4] + t[5] <= 5 else 'Sigma_rho in {6,7}')
        split[key] = split.get(key, 0) + 1
    print(f'  THE RESIDUE ZONE SPLITS: {dict(sorted(split.items()))}')
    # THE CORRECTED FORM.  A first draft of this block asserted that every
    # escape at `Sigma_rho in {6,7}` carries `a_1 + a_2 > 0`; the assert
    # FIRED at `(delta,a,rho,c) = (1,5 | 0,0 | 1,5 | 1,2)`, an `a = 0`
    # escape with `Sigma_rho = 6`.  It is not a counterexample to (BE-219)
    # -- it is a `Pi_x` VIOLATION, which (BE-219)(ii) says an `a = 0` escape
    # at `Sigma_delta >= 6` must be.  The true statement:
    a0esc = [t for t in esc if t[2] + t[3] == 0]
    for t in a0esc:
        if t[4] + t[5] >= 6:
            assert not pix_ok(t), \
                ('an a = 0 escape at Sigma_rho >= 6 that is NOT a Pi_x '
                 'violation', t)
        else:
            assert firing(t), 'an a = 0 escape at Sigma_rho <= 5 not firing'
    n67 = sum(1 for t in a0esc if t[4] + t[5] >= 6)
    nlo = len(a0esc) - n67
    print(f'  of them {len(a0esc)} have `a_1 = a_2 = 0`: {nlo} at '
          f'`Sigma_rho <= 5` (where (BE-219)(iii)')
    print(f'  makes EVERY firing tuple an escape) and {n67} at '
          f'`Sigma_rho >= 6`, ALL {n67} of which')
    print('  are `Pi_x` VIOLATIONS -- ASSERTED, which is (BE-219)(ii) read on '
          'the escape set.')
    print('  So at `a = 0` the escape set carries NOTHING the `Pi_x` '
          'obligation does not, plus')
    print('  a zone where the clause is simply false.')
    # THE REDUCTIVE CONTENT: the tuples where the clause is a genuine
    # RELAXATION of the obligation -- (E4) holds where the obligation fails.
    relax = [t for t in T if firing(t) and BA.e4(t) and not pix_ok(t)]
    for t in relax:
        assert t[2] + t[3] > 0, \
            ('the clause relaxes the obligation at a = 0', t)
        assert not lam2_ok(t), \
            ('(BE-101)(i) FAILS: a Pi_x violation surviving (E4) with the '
             'Lambda^2 inequality intact', t)
    print('  == THE CLAUSE\'S REDUCTIVE CONTENT, counted ==')
    print(f'  {len(relax)} firing tuples have (E4) TRUE and the `Pi_x` '
          f'obligation FALSE -- the rows')
    print('  where the clause is a genuine RELAXATION rather than a '
          'restatement.  EVERY one has')
    print('  `a_1 + a_2 > 0` -- ASSERTED -- and every one breaks the '
          '`Lambda^2 K^4` inequality,')
    print('  which is (BE-101)(i) reproduced.  So the clause\'s whole '
          'reductive content lives at')
    print('  `a_1 + a_2 > 0`, and (BE-101)(ii) applies it at '
          '`a_1 = a_2 = 0`.')
    assert relax, 'the clause never relaxes the obligation anywhere'

    # ---- (BE-220)(ii): AND THAT CONTENT IS OUTSIDE THE ATTAINABLE REGIME.
    # (BE-22)(iii) as corrected by (BE-86)(i): `G` attains iff
    # `dim(rho_bar_1 + rho_bar_2) = min(delta_1+delta_2, 6) + a_1 + a_2`,
    # and the left side is at most `dim Lambda^2 K^4 = 6`.  So a tuple with
    # `min(Sigma_delta, 6) + Sigma_a > 6` CANNOT be a configuration at which
    # the composite attains -- whatever the geometry.
    for t in relax:
        assert min(t[0] + t[1], 6) + t[2] + t[3] > 6, \
            ('the clause relaxes the obligation at an ATTAINABLE tuple', t)
    natt = sum(1 for t in T if firing(t)
               and min(t[0] + t[1], 6) + t[2] + t[3] <= 6)
    print('  == (BE-220)(ii) AND THAT CONTENT IS OUTSIDE THE ATTAINABLE '
          'REGIME ==')
    print(f'  Every one of the {len(relax)} relaxation tuples has')
    print('  `min(delta_1+delta_2, 6) + a_1 + a_2 > 6 = dim Lambda^2 K^4` -- '
          'ASSERTED -- so by')
    print('  (BE-22)(iii) as corrected by (BE-86)(i) the composite CANNOT '
          'attain there, whatever')
    print(f'  the geometry.  Of the {len(fall)} firing tuples {natt} are '
          f'attainment-compatible, and at')
    print('  EVERY one of those the clause is either the `Pi_x` obligation '
          'restated or false.')
    print('  **So (BE-E4\')\'s entire reductive content lies outside the '
          'regime S-mark is about.**')
    assert natt > 0, 'no firing tuple is attainment-compatible at all'
    att = [t for t in fall if min(t[0] + t[1], 6) + t[2] + t[3] <= 6]
    same, weaker, strict = 0, 0, 0
    for t in att:
        assert not (BA.e4(t) and not pix_ok(t)), \
            ('the clause relaxes the obligation at an attainable tuple', t)
        if BA.e4(t) == pix_ok(t):
            same += 1
        else:
            strict += 1
            assert not BA.e4(t) and pix_ok(t), 'unreachable branch'
    print(f'     of the {len(att)}: {same} where the clause is EXACTLY the '
          f'obligation, {strict} where it is')
    print('     STRICTLY STRONGER and therefore FALSE -- ASSERTED, and '
          'nothing else occurs.')
    assert same + strict == len(att) and weaker == 0
    # floor legality of the two halves, per (BE-213)
    fl5 = [t for t in esc if t[4] + t[5] <= 5 and floor_legal(t)]
    fl67 = [t for t in esc if t[4] + t[5] >= 6 and floor_legal(t)]
    print(f'  (BE-213) floor check: {len(fl5)} of the Sigma_rho <= 5 escapes '
          f'and {len(fl67)} of the')
    print('  Sigma_rho >= 6 ones are Grassmann-floor-legal, so neither half '
          'is an artifact')
    print('  of the tuple space\'s missing conjunct.')
    assert fl5 and fl67, 'a half of the residue is entirely floor-illegal'

    # ---- the negative control (F13): drop `a = 0` and the equivalence dies
    diff = [t for t in T if firing(t) and BA.e4(t) != pix_ok(t)]
    assert diff, 'the equivalence holds off a = 0 too -- re-read (BE-219)'
    nz = [t for t in diff if t[2] + t[3] > 0]
    z5 = [t for t in diff if t[2] + t[3] == 0]
    for t in z5:
        assert t[0] + t[1] <= 5, \
            ('the two conditions differ at a = 0 with Sigma_delta >= 6 -- '
             '(BE-219)(ii) is WRONG', t)
    print(f'  NEGATIVE CONTROL (F13): over ALL tuples the two conditions '
          f'differ at {len(diff)}')
    print(f'  firing tuples, {len(nz)} with `a_1 + a_2 > 0` and the other '
          f'{len(z5)} at `a = 0` --')
    print('  and ALL of those last carry `delta_1 + delta_2 <= 5`, ASSERTED, '
          'which is')
    print('  (BE-219)(iii)\'s zone.  So the equivalence is a statement ABOUT '
          '`a = 0` AND')
    print('  `Sigma_delta >= 6`, not an identity -- both hypotheses are '
          'load-bearing.')
    # ---- (BE-223): what the retirement LEAVES, and its exact strength
    print('  == (BE-223) THE SUCCESSOR, AND IT IS STRICTLY WEAKER THAN '
          'ITEM 0(a)\'s CLAUSE ==')
    # A first draft asserted this over ALL 6 400 tuples and the assert
    # FIRED: at `a = (3,0)`, `c = (2,1)`, `rho = (6,1)`, `delta = (3,1)`,
    # (PENCIL-SATURATES) holds and the obligation does NOT (`slack = 0`).
    # (BE-101)(i) never claimed otherwise -- it concludes a `Lambda^2 K^4`
    # violation, and only `a = 0` turns that into the obligation.  So the
    # comparison belongs at `a = 0`, which is the regime that matters.
    ps_but_not = [t for t in zero if BA.ps_full(t) and not pix_ok(t)]
    ok_but_not_ps = [t for t in zero if pix_ok(t) and not BA.ps_full(t)]
    print(f'  At `a = 0` (PENCIL-SATURATES) implies the `Pi_x` obligation at '
          f'all {len(zero)} tuples')
    print(f'  ({len(ps_but_not)} counterexamples) and the converse FAILS at '
          f'{len(ok_but_not_ps)} -- ASSERTED.  So the naked')
    print('  `Pi_x` obligation `c_1 + c_2 <= 2 + slack` is STRICTLY WEAKER '
          'than half (B)\'s item')
    print('  0(a) clause, and it is what (BE-E4\') turns out to BE at '
          '`a = 0`.  That, not a')
    print('  further two-sided clause, is the honest successor: the clause '
          'family has been')
    print('  strictly ABOVE its own target since (E4) was minted.')
    assert not ps_but_not and ok_but_not_ps, \
        'the strictness of (PENCIL-SATURATES) over the obligation moved'
    print(f'  arith: {time.time() - t0:.1f}s')
    return len(esc)


# ================================================ mode: hunt  ((BE-221)/(BE-222))

def prof_for(skname, d2):
    """A canonical entries-in-{2,3} profile with `delta_2 = d2`, by
    (BE-218)'s closed form `delta_2 = max(0, #3-branches - 6)`: put
    `6 + d2` branches at 3 and the rest at 2."""
    n = len(SKELETONS[skname])
    k = 6 + d2
    assert 0 <= k <= n, ('delta_2 out of range for this skeleton', skname, d2)
    return [2] * (n - k) + [3] * k


def one_row(skname, xy, prof, s1name, sd):
    """One `bproper.plant_peel` row with the gate set taken from
    `bline.legal_peel` ITSELF (the tracked function, now `prof`-aware)
    rather than re-implemented.  Returns (row, gates, egraph, aff) or None."""
    E1t, _xt, _yt = side_named(s1name)
    lp = legal_peel(E1t, skname, xy, prof)
    if lp is None:
        return None
    _Eg, x, y, report = lp
    okh, mindeg, girth_h, degx, degy, rnode2, sized = report
    rng = random.Random(SEED + 613 * sd + 7 * len(s1name) + 31 * sum(prof))
    got = plant_peel(skname, prof, xy, E1t, rng)
    if got is None:
        return None
    egraph, raw_side, _other, node_x, node_y, aff, _ppi = got
    assert (node_x, node_y) == (x, y), 'legal_peel and plant_peel disagree'
    split = delta_pair(egraph, node_x, node_y)
    if split is None:
        return None
    _da, _db, part_a, part_b = split
    near = part_a if len(part_a) == len(raw_side) else part_b
    far = part_b if near is part_a else part_a
    if len(near) != len(raw_side):
        return None
    # (BE-208)(ii)'s SCOPE CHECK, asserted rather than inferred: the two
    # sides must be distinguishable by edge count, else `near`/`far` could
    # be swapped and every per-side number would be mislabelled.
    assert len(near) != len(far), \
        ('the two sides have equal edge counts -- the side identification '
         'is ambiguous', skname, xy, prof, s1name)
    assert set(map(frozenset, near)) | set(map(frozenset, far)) == \
        set(map(frozenset, egraph)), 'the two sides do not cover H'
    row = e_row(egraph, node_x, node_y, near, far, aff)
    if row is None:
        return None
    gates = dict(hcard=okh, mindeg=mindeg, girth=girth_h, degx=degx,
                 degy=degy, rnode_far=rnode2, sized=sized,
                 rnode_near=rnode_shaped(near, node_x, node_y),
                 partition=len(near) + len(far) == len(egraph),
                 witness=verify_pencil_witness(egraph, aff)[0],
                 regime=flag_frame(egraph, aff, node_x, node_y) is not None,
                 deg_near_x=len(neighbors(near).get(node_x, ())),
                 deg_far_x=len(neighbors(far).get(node_x, ())))
    return row, gates, egraph, aff


def _assert_gates(gates, tag):
    assert gates['hcard'] and gates['mindeg'] >= 2 and gates['girth'] >= 4, \
        ('(CH-1) fails on H', tag, gates)
    assert gates['degx'] >= 3 and gates['degy'] >= 3, \
        ('a terminal is not a hub of H', tag, gates)
    assert gates['rnode_far'] and gates['sized'], \
        ('side 2 is not R-node-shaped', tag, gates)
    assert gates['partition'], ('the sides do not partition H', tag)
    assert gates['witness'], 'plant_peel returned a non-witness'
    assert gates['regime'], ('the row is OFF the generic flag regime', tag)


HUNTJOBS = [(sk, xy, s1) for (sk, xy, s1) in PEELJOBS]
SWEEP_D2 = (1, 2, 3)


def run_hunt(nseed=2):
    t0 = time.time()
    print(f'== hunt: (BE-221) THE KILL -- (BE-E4\') at `rho_1+rho_2 <= 5`, '
          f'seed {SEED}')
    print('  Side 1 is BEFOURP\'s own firing piece ((BE-118)(ii)/(BE-207)(i)),')
    print('  BYTE UNCHANGED: `bproper.PEELJOBS` through `bproper.plant_peel`,')
    print('  which carries `Sigma_x <= rho_bar_1`, hence `c_1(Pi_x) = 2` and')
    print('  `rho_1 = 4`, at every one of its 21 landed rows.  The ONLY thing')
    print('  moved is side 2\'s branch profile: `delta_2 = 3` (the hardcoded')
    print('  uniform `[3]*n`) becomes `delta_2 = 1` by (BE-218)\'s closed form.')
    kills, rows, holds = [], 0, 0
    cens, bysum = {}, {}
    for (skname, xy, s1name) in HUNTJOBS:
        for d2 in SWEEP_D2:
            prof = prof_for(skname, d2)
            for sd in range(nseed):
                got = one_row(skname, xy, prof, s1name, sd)
                if got is None:
                    continue
                row, gates, _eg, _aff = got
                if not gates['regime']:
                    continue
                _assert_gates(gates, (skname, xy, d2))
                if row['d'][0] < 1 or row['d'][1] < 1:
                    continue
                fires = [i for i in (0, 1) if row['cX'][i] == 2]
                if not fires:
                    continue
                rows += 1
                # the tuple-space identity (BE-208)(ii) disqualified its own
                # 48 rows for failing: MEASURED here per row, never assumed,
                # and reported rather than asserted -- some of these jobs
                # miss it and their rows are quoted separately.
                in_space = (row['r'][0] == row['d'][0] + row['a'][0]
                            and row['r'][1] == row['d'][1] + row['a'][1])
                esum = row['e'][0] + row['e'][1]
                srho = row['r'][0] + row['r'][1]
                key = (row['r'], row['cX'], row['e'], row['d'], row['a'])
                cens[key] = cens.get(key, 0) + 1
                bysum.setdefault(srho, [0, 0])
                bysum[srho][0 if esum >= 4 else 1] += 1
                if esum < 4:
                    kills.append((skname, xy, d2, prof, key, esum, srho,
                                  gates, in_space))
                else:
                    holds += 1
    assert kills, ('no (BE-E4\') failure found -- the clause SURVIVES the '
                   'non-uniform axis; re-read before recording a refutation')
    inside = [k for k in kills if k[8]]
    assert inside, \
        ('every refuting row has `rho_i != delta_i + a_i`, so every one is '
         'outside `barch.all_tuples` and (BE-208)(ii)\'s second disqualifier '
         'applies -- this is NOT a clean refutation')
    print(f'  -- {len(kills)} REFUTING rows of {rows} fully-gated firing '
          f'in-regime rows, {len(inside)} of them')
    print(f'     INSIDE `barch.all_tuples` (`rho_i = delta_i + a_i` at both '
          f'sides) --')
    for (skname, xy, d2, prof, key, esum, srho, gates, insp) in kills:
        r, cX, e, d, a = key
        print(f'  ** {skname} {xy} delta_2 = {d2}, prof {prof}  '
              f'[{"IN" if insp else "OUTSIDE"} the tuple space]')
        print(f'     (CH-1): hcard {gates["hcard"]}, min deg '
              f'{gates["mindeg"]} >= 2, girth {gates["girth"]} >= 4;  '
              f'deg_H(x) = {gates["degx"]}, deg_H(y) = {gates["degy"]};')
        print(f'     side 2 R-node-shaped {gates["rnode_far"]}, side 1 '
              f'R-node-shaped {gates["rnode_near"]};  pencil witness '
              f'{gates["witness"]};  flag_frame NON-None '
              f'{gates["regime"]}.')
        print(f'     deg_1(x) = {gates["deg_near_x"]} (a SERIES END, so '
              f'(BE-175)(i) gives `c_1(Pi_x) >= 1` for free), '
              f'deg_2(x) = {gates["deg_far_x"]}.')
        print(f'     rho = {r}, c(Pi_x) = {cX}, e = {e}, delta = {d}, '
              f'a = {a};  rho_i = delta_i + a_i {insp}.')
        print(f'     ** e_1 + e_2 = {esum} < 4: **(BE-E4\') IS FALSE** '
              f'here;  rho_1 + rho_2 = {srho}. **')
    print('  -- (BE-222) the census, and the boundary is EXACT --')
    for key, num in sorted(cens.items(), key=str):
        r, cX, e, d, a = key
        print(f'     {num:3d}  rho = {r}, c = {cX}, e = {e}, delta = {d}, '
              f'a = {a},  e-sum {e[0] + e[1]}')
    print(f'     by `rho_1 + rho_2`:  (holds, fails)')
    for srho in sorted(bysum):
        print(f'       {srho}: {tuple(bysum[srho])}')
    for srho, (nh, nf) in bysum.items():
        if srho <= 5:
            assert nh == 0, ('(BE-E4\') HOLDS at Sigma_rho <= 5', srho)
        else:
            assert nf == 0, ('(BE-E4\') FAILS at Sigma_rho >= 6', srho)
    print('     ASSERTED: every row with `rho_1 + rho_2 <= 5` FAILS and every')
    print('     row with `rho_1 + rho_2 >= 6` HOLDS -- (BE-219)\'s split,')
    print('     measured on geometry rather than derived on tuples.')
    print(f'  hunt: {time.time() - t0:.1f}s')
    return len(kills)


def run_validate():
    print('== validate: map + arith + hunt in one process')
    run_map()
    run_arith()
    run_hunt()


def main(argv):
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        return 0
    mode = argv[0].lstrip('-')
    if mode == 'map':
        run_map()
    elif mode == 'arith':
        run_arith()
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
