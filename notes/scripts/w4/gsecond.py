r"""§(K-grid) fan-out direction GSECOND (2026-09-12) driver -- WHAT is the
SECOND obstruction behind the `1 282` weak-lift failures (GR-227)(i)'s
balance law does NOT explain, and is it avoidable by the parent's choice of
re-length?

A `w4/` leaf sitting directly on `gcoltrans.py` (READ-ONLY: it re-uses that
driver's `Census`, `frames_of`, `out_key`, `strong_key`, `C_SEED` and its
exact iteration order, and reimplements nothing).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsecond.py --split   # [GS-1] the FINE partition of every weak-lift failure, exhaustive at n_hub = 6
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsecond.py --rule    # [GS-2] does an EXPLICIT choice function of the re-length always avoid failure?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsecond.py --deeper  # [GS-3] the cap control: re-run EVERY triple at a deeper draw count, both verdict directions
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsecond.py --sets    # [GS-4] the 3-cube STRUCTURE of the four restriction sets, not just their sizes

WHAT IS NEW HERE, in one paragraph.  (GR-232)(ii) reports the weak lift
failing at `1 890` of `194 325` triples and (GR-227)(iii) explains `608` of
them by the balance law.  Nothing in the corpus decomposes the remaining
`1 282`.  The decomposition this driver makes is NOT a new predicate: it is
already latent in `gcoltrans.transport_at`'s own return value, which reports
the missed-restriction set `up_good = cg - pg` and the admissibility-level
set `up_adm = ca - pa` but never intersects them.  A weak-lift failure at a
triple is a nonempty `cg - pg`; each missed restriction `k` is of exactly
one of two kinds --

    (A)  k NOT IN pa   -- the parent has NO admissible colouring at all on
         that out-restriction.  Decided by `gridcol.filter_pass`, an EXACT
         predicate: CAP-FREE, and no number of extra draws can repair it.
    (B)  k IN pa       -- the parent DOES admit that out-restriction, but no
         admissible parent colouring at it was found GOOD in `--draws`
         draws.  CAPPED, and repairable in principle by drawing deeper.

-- and a triple is class A if at least one missed restriction is of kind
(A), class B if every one of them is of kind (B).  That is the
ADMISSIBILITY / GOOD-NESS split, and (GR-227)(iii)'s `594` cap-free
refutations are exactly class A inside the adversarial slice.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--split  [GS-1] the fine partition, EXHAUSTIVE over `gisland.stratum(6,
         lamcap=99)`: every interior-frame triple cross-tabulated by the
         (GR-227)(i) balance class (adversarial / safe) against the
         admissibility / good-ness class, with `gcoltrans`' own `w_up`,
         `s_up`, `f_up_all`, `f_up_some` reproduced as a control so the
         population is provably the one (GR-232)(ii) measured.

--rule   [GS-2] the AVOIDABILITY question as a constructive one: not "does
         SOME re-length work" (measured `100 %` and already landed) but
         "does an EXPLICIT, parent-computable choice function of the
         re-length always pick a working one" -- tested for a menu of
         candidate rules over every frame, with each rule's AVAILABILITY
         (is it defined at every frame) and SUFFICIENCY (does what it picks
         lift) reported separately.

--deeper [GS-3] the cap control in BOTH directions: re-census EVERY triple
         of the region at `--draws` and again at `--deep`, and report how
         many failures were REPAIRED and how many HOLDINGS were BROKEN --
         because `cg - pg = EMPTY` is a difference of two sets that are both
         LOWER bounds, so the lift HOLDING is capped too, in the opposite
         direction.  Uses `PerShapeCensus`, so it also opens the
         iteration-order blind axis; `--only` aims it at named shapes.

--sets   [GS-4] the STRUCTURE, not the size: the four sets `pa`, `pg`, `ca`,
         `cg` live in the `8`-element cube `{0,1}^O` (asserted: `|O| = 3` at
         every interior `|A| = 3` frame of `n_hub = 6`), every one of them
         is closed under the global `A <-> B` swap `b -> b ^ (2^M - 1)`
         (asserted over the whole census), and so every deficiency is a
         union of ANTIPODAL pairs -- which is why the lift reduces to a
         question about ONE pair.

CAPS AND BLIND AXES, disclosed in the driver (F13).

 * `n_hub = 6` only, `|A| = 3` (interior) only.  Every figure is about the
   `n_hub 6 -> 4` size step and nothing else; (GR-232)(iv) already says a
   proof of `T-up-exists-exists` closes the induction only on the part of
   the stratum the move family reaches.
 * `--shapes N` takes a PREFIX of `gisland.stratum(6, lamcap=99)` in
   generator order, NOT a random sample, and one `random.Random(C_SEED)`
   feeds every census, so a capped run is NOT bit-identical to the full one
   (`gcoltrans`' own disclosure).  The landed figures are `--shapes 7892`.
 * GOOD is decided by `--draws` exact rational draws (default 8, the value
   (GR-232)(ii) ran at).  A colouring called GOOD is PROVEN good -- an
   attaining draw is a witness.  A colouring called NOT-GOOD is "no
   vanishing draw found under `--draws`".  THE CONSEQUENCE FOR THE LIFT,
   and it is the one this direction had to correct: the lift predicate
   `cg - pg = EMPTY` compares two sets that are BOTH lower bounds, so
   deeper draws can turn a HOLDING triple into a FAILING one (by growing
   `cg`) as well as a failing one into a holding one (by growing `pg`).
   Neither verdict of the weak lift is cap-free.  Only the class-A part of
   a failure is cap-free, because `pa` is exact.
 * Class A is cap-free in the FAILURE direction only in the sense that the
   missed restriction is not parent-admissible; the fact that the CHILD
   colouring exhibiting it is GOOD is itself a witness, so class A is a
   genuine refutation of the map-form at that triple.  Class B is capped on
   both sides.
 * `--rule`'s candidate rules are a MENU chosen by the author; "no rule in
   the menu is both available and sufficient" is never "no rule exists",
   and symmetrically a rule scoring `0` is "not refuted under the cap the
   records were taken at".  `--rule` separates a rule's PRINCIPLE from its
   arbitrary TIEBREAK and reports the argmin-SET test for the principle,
   because two rules on the same principle disagreed (`minodd` `0/808`,
   `minodd_bal` `4/808`) and the tiebreak was doing the work.
 * `--sets` is run at a PREFIX (`--shapes 200` in the reported figures),
   never exhaustively: it is the structural probe, and the exhaustive
   figures come from `--split` + `--rule`, whose records carry the SIZES of
   the four sets but not the sets themselves.
"""

import argparse
import json
import os
import random
import sys
import time
import zlib
from math import comb

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from gisland import stratum                                          # noqa: E402
from gnonadd import y_reductions                                     # noqa: E402
from gcoltrans import (C_SEED, Census, frames_of, out_key,           # noqa: E402
                       strong_key)

RECORD_FIELDS = (
    'si', 'fi', 'rl', 'nodd_par', 'nodd_ch', 'o', 'budget',
    'npa', 'npg', 'nca', 'ncg',
    'w_miss', 'w_missA', 'w_adm',
    's_miss', 's_missA', 's_adm')


def transport_fine(cen, n, hedges, lens, A, ins, bd, out, che0, cle):
    """`gcoltrans.transport_at` and `transport_strong` at ONE triple, with
    the missed-restriction set SPLIT against the parent's ADMISSIBLE set.

    Local device (README rule 3): `transport_at` returns `up_good = cg - pg`
    and `up_adm = ca - pa` but never intersects them, and `pa` -- the set
    this direction needs -- is not in its return value.  The two `cen.get`
    calls are made in the SAME order as `transport_at`/`transport_strong`
    make them, so the shared `random.Random(C_SEED)` stream is consumed
    identically and the control figures reproduce bit-for-bit."""
    _pm, padm, pgood = cen.get(list(hedges), list(lens))
    _cm, cadm, cgood = cen.get(list(che0), list(cle))
    no, As = len(out), set(A)

    # -- the WEAK datum: the out-branch restriction.
    pa = {out_key(b, out) for b in padm}
    pg = {out_key(b, out) for b in pgood}
    ca = {out_key(b, range(no)) for b in cadm}
    cg = {out_key(b, range(no)) for b in cgood}
    w_missed = cg - pg
    w = (len(w_missed), len(w_missed - pa), 1 if (ca - pa) else 0)

    # -- the STRONG datum: out-branches + the three outside boundary darts.
    def P(bs):
        return {strong_key(b, out, bd, hedges, lens, As, False, cle, no)
                for b in bs}

    def C(bs):
        return {strong_key(b, out, bd, hedges, lens, As, True, cle, no)
                for b in bs}
    spa, spg, sca, scg = P(padm), P(pgood), C(cadm), C(cgood)
    s_missed = scg - spg
    s = (len(s_missed), len(s_missed - spa), 1 if (sca - spa) else 0)

    # The nesting this direction asserts rather than assumes: a cap-free
    # (class-A) missed restriction lies in `cg` and outside `pa`, hence in
    # `ca - pa`.  So class A IMPLIES the admissibility-level failure -- the
    # `1 246` count is not nested in the `1 890` one, but the CAP-FREE part
    # of the `1 890` IS nested in the `1 246`.
    assert w[1] == 0 or w[2] == 1, "class A outside up_adm (weak)"
    assert s[1] == 0 or s[2] == 1, "class A outside up_adm (strong)"
    assert cg <= ca and pg <= pa, "GOOD set not inside ADMISSIBLE set"
    return (len(pa), len(pg), len(ca), len(cg)), w, s


def leg_split(shape_cap=400, draws=8, out_path=None):
    """[GS-1] the fine partition of every weak-lift failure at `n_hub = 6`."""
    print(f"[GS-1] the ADMISSIBILITY / GOOD-NESS split of the weak-lift "
          f"failures, n_hub = 6 interior frames, first {shape_cap} shapes, "
          f"{draws} draws (seed {C_SEED})")
    t0 = time.time()
    cen = Census(random.Random(C_SEED), draws=draws)
    rec = []
    ctl = dict(triples=0, frames=0, shapes=0, w_up=0, s_up=0,
               up_adm=0, f_up_all=0, f_up_some=0)
    fi = 0
    for si, (hedges, lens, _m, _a) in enumerate(stratum(6, lamcap=99)):
        if shape_cap is not None and si >= shape_cap:
            break
        ctl['shapes'] += 1
        nodd_par = sum(1 for L in lens if L % 2)
        for (A, ins, bd, out, glob) in frames_of(6, hedges, (3,)):
            if glob:
                continue
            per, rows = [], []
            o = sum(1 for i in out if lens[i] % 2)
            budget = (sum(lens[i] for i in bd) + sum(lens[i] for i in ins)
                      - 3 * (len(A) - 1))
            for (_A2, _b, che0, cle, _nl) in y_reductions(
                    6, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                sizes4, w, s = transport_fine(
                    cen, 6, hedges, lens, A, ins, bd, out, che0, cle)
                ctl['triples'] += 1
                ctl['w_up'] += 1 if w[0] else 0
                ctl['s_up'] += 1 if s[0] else 0
                ctl['up_adm'] += w[2]
                no = len(out)
                rows.append((si, fi, list(cle[no:no + 3]), nodd_par,
                             sum(1 for L in cle if L % 2), o, budget)
                            + sizes4 + w + s)
                per.append(bool(w[0]))
            if not per:
                continue
            ctl['frames'] += 1
            ctl['f_up_all'] += 1 if not any(per) else 0
            ctl['f_up_some'] += 1 if not all(per) else 0
            rec.extend(rows)
            fi += 1
    print(f"  CONTROL (must match (GR-232)(ii) at --shapes 7892): "
          f"shapes {ctl['shapes']}, frames {ctl['frames']}, triples "
          f"{ctl['triples']}, w_up {ctl['w_up']}, s_up {ctl['s_up']}, "
          f"up_adm {ctl['up_adm']}, f_up_all {ctl['f_up_all']}, f_up_some "
          f"{ctl['f_up_some']}")
    print(f"  censuses: {cen.nshape} shapes, {cen.ncol} admissible "
          f"colourings, {cen.ngood} of them GOOD (each by an exact witness "
          f"draw -- a proof)")
    _report_split(rec)
    if out_path:
        with open(out_path, 'w') as fh:
            json.dump(dict(fields=list(RECORD_FIELDS), control=ctl,
                           shape_cap=shape_cap, draws=draws, seed=C_SEED,
                           rows=rec), fh)
        print(f"  records -> {out_path}")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def _report_split(rec):
    """The 2x2 the direction exists to print: balance class against
    admissibility / good-ness class, over the weak-lift failures."""
    F = {k: i for i, k in enumerate(RECORD_FIELDS)}
    for tag, mi, ai in (('WEAK', F['w_miss'], F['w_missA']),
                        ('STRONG', F['s_miss'], F['s_missA'])):
        cell = {}
        for r in rec:
            if not r[mi]:
                continue
            adv = r[F['nodd_ch']] > r[F['nodd_par']]
            cls = 'A' if r[ai] else 'B'
            cell[(adv, cls)] = cell.get((adv, cls), 0) + 1
        tot = sum(cell.values())
        adv_t = sum(v for (a, _), v in cell.items() if a)
        print(f"  {tag} lift failures: {tot} triples "
              f"({adv_t} ADVERSARIAL by (GR-227)(i), {tot - adv_t} SAFE)")
        for a in (True, False):
            nA = cell.get((a, 'A'), 0)
            nB = cell.get((a, 'B'), 0)
            lab = 'ADVERSARIAL' if a else 'BALANCE-SAFE'
            print(f"    {lab:12s}: A (missed restriction NOT parent-"
                  f"admissible -- CAP-FREE) {nA}; B (parent-admissible but "
                  f"no GOOD parent colouring under the draw cap) {nB}")
    return 0


# ---------------------------------------------------- [GS-2] --rule --------

def _rules():
    """The candidate CHOICE FUNCTIONS of the re-length, as (name, key,
    doc).  Each is a parent-computable total order on the re-lengths
    available at one frame; the rule picks the minimum.  Every one is
    AVAILABLE at every frame by construction (it is a min over a nonempty
    finite list), so `--rule` reports SUFFICIENCY."""
    F = {k: i for i, k in enumerate(RECORD_FIELDS)}
    return [
        ('minodd', lambda r: (r[F['nodd_ch']], tuple(r[F['rl']])),
         'fewest odd branches in the child ((GR-227)(i)"s balance law, '
         'pushed as far as it goes), ties lexicographic'),
        ('maxodd', lambda r: (-r[F['nodd_ch']], tuple(r[F['rl']])),
         'MOST odd branches in the child -- the control, the balance law '
         'read backwards'),
        ('balanced', lambda r: (max(r[F['rl']]) - min(r[F['rl']]),
                                tuple(r[F['rl']])),
         'the three invented branch lengths as EQUAL as the budget allows'),
        ('lexmin', lambda r: tuple(r[F['rl']]),
         'lexicographically least re-length -- the null rule'),
        ('minodd_bal', lambda r: (r[F['nodd_ch']],
                                  max(r[F['rl']]) - min(r[F['rl']]),
                                  tuple(r[F['rl']])),
         'fewest odd child branches, ties broken by the most EQUAL split'),
        ('maxpg', lambda r: (-r[F['npg']], -r[F['ncg']],
                             tuple(r[F['rl']])),
         'the re-length whose PARENT GOOD set is largest -- not '
         'parent-computable without the census, reported as an ORACLE '
         'upper bound on what any rule can do'),
        ('minncg', lambda r: (r[F['ncg']], tuple(r[F['rl']])),
         'the re-length with the FEWEST distinct GOOD child restrictions '
         'to match -- also an oracle rule'),
    ]


def _principles():
    """The candidate statistics a choice rule could RANK on, with the
    tiebreak removed -- see the PRINCIPLE test in `leg_rule`."""
    F = {k: i for i, k in enumerate(RECORD_FIELDS)}
    return [
        ('minodd', lambda r: r[F['nodd_ch']],
         'fewest odd branches in the child ((GR-227)(i) pushed to its '
         'extreme: not band CONTAINMENT but band MINIMIZATION)'),
        ('maxspread', lambda r: -(max(r[F['rl']]) - min(r[F['rl']])),
         'the most SKEWED split of the budget among the three new branches'),
        ('minspread', lambda r: max(r[F['rl']]) - min(r[F['rl']]),
         'the most EQUAL split'),
        ('minodd_sp', lambda r: (r[F['nodd_ch']],
                                 -(max(r[F['rl']]) - min(r[F['rl']]))),
         'fewest odd child branches, then most skewed'),
        ('minncg', lambda r: r[F['ncg']],
         'fewest distinct GOOD child out-restrictions -- ORACLE (needs the '
         'child census), reported to NAME the mechanism, not as a rule'),
        ('minnca', lambda r: r[F['nca']],
         'fewest distinct ADMISSIBLE child out-restrictions -- EXACT (no '
         'draw cap) and PARENT-COMPUTABLE: it is `filter_pass` over the '
         'child\'s 2^6 colourings, no rank and no draw, so unlike `minncg` '
         'this one is a genuine explicit choice rule'),
    ]


def leg_rule(rec_path):
    """[GS-2] is the residual avoidable by an EXPLICIT choice of re-length?"""
    print("[GS-2] avoidability as a CONSTRUCTIVE question: does an explicit "
          "choice function of the re-length always pick a lifting one?")
    t0 = time.time()
    with open(rec_path) as fh:
        blob = json.load(fh)
    rec, F = blob['rows'], {k: i for i, k in enumerate(blob['fields'])}
    byframe = {}
    for r in rec:
        byframe.setdefault(r[F['fi']], []).append(r)
    nfr = len(byframe)
    print(f"  loaded {len(rec)} triples over {nfr} interior frames "
          f"(--shapes {blob['shape_cap']}, {blob['draws']} draws, seed "
          f"{blob['seed']})")
    # The frame invariants, asserted rather than assumed: `pa` and `pg` are
    # functions of (parent shape, frame) ALONE -- the re-length changes only
    # the CHILD -- so at a fixed frame the weak lift `cg <= pg` compares a
    # MOVING left side against a FIXED right side.
    for fi, rs in byframe.items():
        assert len({r[F['npa']] for r in rs}) == 1, "|pa| moved within a frame"
        assert len({r[F['npg']] for r in rs}) == 1, "|pg| moved within a frame"
    nrl = {}
    for rs in byframe.values():
        nrl[len(rs)] = nrl.get(len(rs), 0) + 1
    print(f"  re-lengths per frame: {dict(sorted(nrl.items()))}")
    pgd = {}
    for rs in byframe.values():
        pgd[rs[0][F['npg']]] = pgd.get(rs[0][F['npg']], 0) + 1
    print(f"  |pg| (the FIXED target set, {{0,1}}^|O| with |O| = 3) over "
          f"frames: {dict(sorted(pgd.items()))}")
    some = sum(1 for rs in byframe.values() if any(not r[F['w_miss']]
                                                   for r in rs))
    allf = sum(1 for rs in byframe.values() if all(not r[F['w_miss']]
                                                   for r in rs))
    print(f"  landed control: weak lift at SOME re-length {some}/{nfr}; at "
          f"EVERY re-length {allf}/{nfr}; so {nfr - allf} frames carry a "
          f"failure at all and are where a choice rule has to work")
    hard = {fi: rs for fi, rs in byframe.items()
            if any(r[F['w_miss']] for r in rs)}
    hd = {}
    for rs in hard.values():
        k = (len(rs), sum(1 for r in rs if r[F['w_miss']]))
        hd[k] = hd.get(k, 0) + 1
    print(f"  at the {len(hard)} frames carrying a failure, "
          f"(re-lengths, failing) -> count: {dict(sorted(hd.items()))}")
    print(f"  |pg| at those frames: "
          f"{sorted(rs[0][F['npg']] for rs in hard.values())}")
    pad = {}
    for rs in byframe.values():
        pad[rs[0][F['npa']]] = pad.get(rs[0][F['npa']], 0) + 1
    print(f"  |pa| (the parent's ADMISSIBLE out-restrictions) over frames: "
          f"{dict(sorted(pad.items()))}")
    # WHY the sizes are quantized: (GR-227)(i)'s band `I(n_odd)` constrains
    # the A-majority count on the `o` ODD out-branches, so the admissible
    # out-restrictions are exactly the bit patterns whose odd-branch weight
    # lies in `I`.  With |O| = 3 that predicts |pa| = 2^(3-o) * #{w in I}.
    band = {}
    for rs in byframe.values():
        r = rs[0]
        o, npar = r[F['o']], r[F['nodd_par']]
        lo, hi = max(0, o - npar // 2), min(o, npar // 2)
        pred = 2 ** (3 - o) * sum(comb(o, j) for j in range(lo, hi + 1))
        band[(o, npar, lo, hi, pred, r[F['npa']], r[F['npg']])] = \
            band.get((o, npar, lo, hi, pred, r[F['npa']], r[F['npg']]), 0) + 1
    print("  (o, n_odd(parent), band I=[lo,hi], band-PREDICTED |pa| upper "
          "bound, actual |pa|, |pg|) -> frames:")
    for k in sorted(band):
        print(f"    {k} -> {band[k]}")
    sat = sum(v for k, v in band.items() if k[4] == 8)
    print(f"  frames at which the PARENT's balance band is SATURATED (allows "
          f"all 8 out-restrictions): {sat}/{nfr}")
    # The CHILD side, where the band is not vacuous: `n_odd(child)` moves
    # with the re-length, so the band bounds |ca| from above and is the only
    # part of (GR-227)(i) that constrains anything at these frames.
    cb = {}
    for r in rec:
        o, nch = r[F['o']], r[F['nodd_ch']]
        lo, hi = max(0, o - nch // 2), min(o, nch // 2)
        pred = 2 ** (3 - o) * sum(comb(o, j) for j in range(lo, hi + 1))
        cb[(pred, r[F['nca']], bool(r[F['w_miss']]))] = \
            cb.get((pred, r[F['nca']], bool(r[F['w_miss']])), 0) + 1
    print("  CHILD side (band-predicted |ca| upper bound, actual |ca|, "
          "weak-lift FAILS) -> triples:")
    for k in sorted(cb):
        print(f"    {k} -> {cb[k]}")
    assert all(k[1] <= k[0] for k in cb), \
        "a child's |ca| exceeded (GR-227)(i)'s band bound"
    assert all(k[1] <= k[5] or True for k in band), "unreachable"
    for k in band:
        assert k[5] <= k[4], "a parent's |pa| exceeded the band bound"

    for name, key, doc in _rules():
        bad = [fi for fi, rs in byframe.items()
               if min(rs, key=key)[F['w_miss']]]
        badh = [fi for fi in bad if fi in hard]
        print(f"  rule {name:11s}: picks a FAILING re-length at "
              f"{len(bad)}/{nfr} frames ({len(badh)} of them among the "
              f"{len(hard)} frames that carry any failure) -- {doc}")
    # A rule's verdict conflates the PRINCIPLE it ranks on with the ARBITRARY
    # tiebreak it settles ties by; `minodd` and `minodd_bal` rank on the same
    # principle and disagree, so the tiebreak is doing the work.  Test the
    # PRINCIPLE instead: over the ARGMIN SET of a statistic, does a working
    # re-length always survive, and does every member of it work?
    # The SUFFICIENT CONDITION, over every triple: does a child that does
    # NOT saturate the shared cube ever fail to lift?
    for tag, fld in (('|ca| (ADMISSIBLE, exact)', 'nca'),
                     ('|cg| (GOOD, draw-capped)', 'ncg')):
        tb = {}
        for r in rec:
            adv = r[F['nodd_ch']] > r[F['nodd_par']]
            k = (r[F[fld]], bool(r[F['w_miss']]), adv)
            tb[k] = tb.get(k, 0) + 1
        print(f"  {tag} against (weak-lift FAILS, ADVERSARIAL) -> triples: "
              f"{dict(sorted(tb.items()))}")
        for adv in (False, True):
            lo = sum(v for k, v in tb.items()
                     if k[0] < 8 and k[1] and k[2] == adv)
            nlo = sum(v for k, v in tb.items() if k[0] < 8 and k[2] == adv)
            lab = 'ADVERSARIAL' if adv else 'BALANCE-SAFE'
            print(f"    => on the {lab} slice, failures among the {nlo} "
                  f"NON-SATURATED triples ({fld} < 8): {lo}")
    # AVAILABILITY of the `minnca` rule, which is what its sufficiency
    # really rests on: is a re-length with a NON-SATURATED child reachable
    # at every frame, and especially at the frames whose `pg` is deficient?
    av = {}
    for rs in byframe.values():
        mn = min(r[F['nca']] for r in rs)
        defic = rs[0][F['npg']] < 8
        av[(defic, mn)] = av.get((defic, mn), 0) + 1
    print("  AVAILABILITY (`pg` deficient?, min |ca| over the frame's "
          "re-lengths) -> frames:")
    for k in sorted(av):
        print(f"    {k} -> {av[k]}")
    nsat = sum(v for k, v in av.items() if k[0] and k[1] == 8)
    print(f"  frames where `pg` is DEFICIENT and EVERY re-length saturates "
          f"the cube (|ca| = 8) -- the frames at which the `minnca` rule has "
          f"nothing safe to pick: {nsat}")
    print("  -- the PRINCIPLE test (argmin SET, tiebreak removed): "
          "`all-fail` frames REFUTE the principle as a choice rule; "
          "`mixed` frames say it needs a tiebreak that is itself a rule")
    for name, stat, doc in _principles():
        allf = mixed = clean = 0
        ntr = nbad = 0
        for rs in byframe.values():
            vals = [stat(r) for r in rs]
            m = min(vals)
            arg = [r for r, v in zip(rs, vals) if v == m]
            nb = sum(1 for r in arg if r[F['w_miss']])
            ntr += len(arg)
            nbad += nb
            if nb == len(arg):
                allf += 1
            elif nb:
                mixed += 1
            else:
                clean += 1
        print(f"    principle {name:10s}: argmin set has {nbad}/{ntr} "
              f"failing triples; frames all-fail {allf}, mixed {mixed}, "
              f"clean {clean} -- {doc}")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# -------------------------------------------------- [GS-3] --deeper --------

class PerShapeCensus(Census):
    """`gcoltrans.Census` with the draw stream keyed on the SHAPE instead of
    on the iteration order.

    `gcoltrans`' own disclosure says one `random.Random(C_SEED)` feeds every
    census in a run, so the draws a shape receives depend on `--shapes` and
    on generator order.  That is a blind axis, and `--deeper` opens it: here
    each shape gets `random.Random(seed ^ hash-of-its-spec)`, so a verdict
    is a function of the SHAPE alone and a run restricted to a subset of
    shapes reproduces the verdicts the full run would have given them.  This
    is a DIFFERENT sampling scheme from the one (GR-232)(ii) ran under and
    is used only as a cap / order control, never to restate a landed
    figure."""

    def __init__(self, seed, draws=8):
        super().__init__(random.Random(seed), draws=draws)
        self.seed = seed

    def get(self, hedges, lens):
        key = (tuple(map(tuple, hedges)), tuple(lens))
        if key not in self.memo:
            self.rng = random.Random(
                (self.seed * 1000003) ^ (zlib.crc32(repr(key).encode())))
        return super().get(hedges, lens)


def leg_deeper(shape_cap=400, draws=8, deep=64, only=None):
    """[GS-3] the cap control, in BOTH directions."""
    print(f"[GS-3] the draw cap, both directions: {draws} draws vs {deep} "
          f"draws over the first {shape_cap} shapes, n_hub = 6 interior "
          f"(PER-SHAPE seeding, so order-independent -- see PerShapeCensus)"
          + (f"; restricted to shapes {sorted(only)[:8]}... ({len(only)})"
             if only else ""))
    t0 = time.time()
    base = PerShapeCensus(C_SEED, draws=draws)
    deepc = PerShapeCensus(C_SEED, draws=deep)
    stats = dict(triples=0, w_base=0, w_deep=0, A_base=0, A_deep=0,
                 repaired=0, broken=0, cg_grew=0, pg_grew=0)
    for si, (hedges, lens, _m, _a) in enumerate(stratum(6, lamcap=99)):
        if shape_cap is not None and si >= shape_cap:
            break
        if only is not None and si not in only:
            continue
        for (A, ins, bd, out, glob) in frames_of(6, hedges, (3,)):
            if glob:
                continue
            for (_A2, _b, che0, cle, _nl) in y_reductions(
                    6, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                s1, w1, _ = transport_fine(base, 6, hedges, lens, A, ins,
                                           bd, out, che0, cle)
                s2, w2, _ = transport_fine(deepc, 6, hedges, lens, A, ins,
                                           bd, out, che0, cle)
                stats['triples'] += 1
                stats['w_base'] += 1 if w1[0] else 0
                stats['w_deep'] += 1 if w2[0] else 0
                stats['A_base'] += 1 if w1[1] else 0
                stats['A_deep'] += 1 if w2[1] else 0
                if w1[0] and not w2[0]:
                    stats['repaired'] += 1
                if not w1[0] and w2[0]:
                    stats['broken'] += 1
                if s2[3] > s1[3]:
                    stats['cg_grew'] += 1
                if s2[1] > s1[1]:
                    stats['pg_grew'] += 1
    print(f"  censuses: {base.nshape}/{deepc.nshape} shapes, "
          f"{base.ncol}/{deepc.ncol} admissible colourings, "
          f"{base.ngood}/{deepc.ngood} GOOD at {draws}/{deep} draws "
          f"-- EQUAL GOOD counts mean the draw cap is not binding anywhere "
          f"in this region, and then every lift verdict is cap-stable here")
    assert base.nshape == deepc.nshape and base.ncol == deepc.ncol, \
        "the two censuses disagree on the ADMISSIBLE population"
    print(f"  {stats['triples']} triples; weak-lift failures {stats['w_base']}"
          f" at {draws} draws vs {stats['w_deep']} at {deep}")
    print(f"    cap-free (class A) failures {stats['A_base']} vs "
          f"{stats['A_deep']} -- these MUST agree, `pa` is exact")
    print(f"    failures REPAIRED by deeper draws: {stats['repaired']}; "
          f"HOLDINGS BROKEN by deeper draws: {stats['broken']}")
    print(f"    triples whose CHILD GOOD set grew: {stats['cg_grew']}; "
          f"whose PARENT GOOD set grew: {stats['pg_grew']}")
    assert stats['A_base'] == stats['A_deep'], \
        "the exact admissibility predicate moved under a draw change"
    print("  => the cap binds on the weak lift in BOTH directions if either "
          "of `cg_grew` / `pg_grew` is nonzero; class A is cap-free.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ---------------------------------------------------- [GS-4] --sets --------

CUBE = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]


def _shape_of(S):
    """Name the complement of a subset of the 3-cube: ANTIPODAL means the
    two missing patterns are `k` and its bitwise complement."""
    miss = [k for k in CUBE if k not in S]
    if not miss:
        return 'FULL'
    if len(miss) == 2:
        a, b = miss
        return ('ANTIPODAL' if all(x != y for x, y in zip(a, b))
                else f'pair{miss}')
    return f'{len(miss)} missing'


def leg_sets(shape_cap=200, draws=8):
    """[GS-4] the STRUCTURE of the out-restriction sets, not just their
    sizes: is the deficiency always the ANTIPODAL pair?"""
    print(f"[GS-4] the 3-cube structure of `pa`, `pg`, `ca`, `cg` over the "
          f"first {shape_cap} shapes, n_hub = 6 interior, {draws} draws "
          f"(seed {C_SEED})")
    t0 = time.time()
    cen = Census(random.Random(C_SEED), draws=draws)
    fr, tr, miss = {}, {}, {}
    for si, (hedges, lens, _m, _a) in enumerate(stratum(6, lamcap=99)):
        if shape_cap is not None and si >= shape_cap:
            break
        for (A, ins, bd, out, glob) in frames_of(6, hedges, (3,)):
            if glob:
                continue
            first = True
            for (_A2, _b, che0, cle, _nl) in y_reductions(
                    6, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                _pm, padm, pgood = cen.get(list(hedges), list(lens))
                _cm, cadm, cgood = cen.get(list(che0), list(cle))
                no = len(out)
                assert no == 3, "|O| != 3 at an interior |A| = 3 frame"
                pa = {out_key(b, out) for b in padm}
                pg = {out_key(b, out) for b in pgood}
                ca = {out_key(b, range(no)) for b in cadm}
                cg = {out_key(b, range(no)) for b in cgood}
                if first:
                    k = (_shape_of(pa), _shape_of(pg))
                    fr[k] = fr.get(k, 0) + 1
                    first = False
                bad = cg - pg
                k2 = (_shape_of(ca), _shape_of(cg), bool(bad))
                tr[k2] = tr.get(k2, 0) + 1
                if bad:
                    mk = (_shape_of(pg), tuple(sorted(bad)),
                          len(bad), _shape_of(ca))
                    miss[mk] = miss.get(mk, 0) + 1
    # WHY the deficiencies are antipodal, checked rather than argued: the
    # global A<->B swap is `b -> b ^ (2^M - 1)` (flipping every branch bit
    # flips the start colour of every branch, hence every edge), and
    # `filter_pass` is symmetric in the two ruling classes while GOOD asks
    # for `dim Z = 0` in BOTH blocks.  So `padm`, `pgood`, `cadm`, `cgood`
    # should be closed under complementation -- and then so are their
    # images in the cube, whose complements are therefore unions of
    # ANTIPODAL pairs.
    nsym = nviol = ngviol = 0
    for (hed, ln), (mod, adm, good) in cen.memo.items():
        full = (1 << mod['M']) - 1
        aset, gset = set(adm), set(good)
        nsym += len(adm)
        nviol += sum(1 for b in aset if (b ^ full) not in aset)
        ngviol += sum(1 for b in gset if (b ^ full) not in gset)
    print(f"  A<->B swap closure over {len(cen.memo)} censused shapes and "
          f"{nsym} admissible colourings: ADMISSIBLE violations {nviol}, "
          f"GOOD violations {ngviol} (both `0` => every one of `pa`, `pg`, "
          f"`ca`, `cg` is complement-closed, so its deficiency is a union "
          f"of ANTIPODAL pairs -- which is the structure observed below)")
    assert nviol == 0, "the admissible set is not A<->B symmetric"
    print("  per FRAME (shape of `pa`, shape of `pg`) -> frames:")
    for k in sorted(fr, key=str):
        print(f"    {k} -> {fr[k]}")
    print("  per TRIPLE (shape of `ca`, shape of `cg`, weak lift FAILS) "
          "-> triples:")
    for k in sorted(tr, key=str):
        print(f"    {k} -> {tr[k]}")
    print("  the FAILURES (shape of `pg`, the MISSED restrictions, how "
          "many, shape of `ca`) -> triples:")
    for k in sorted(miss, key=str):
        print(f"    {k} -> {miss[k]}")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--split', action='store_true')
    ap.add_argument('--rule', action='store_true')
    ap.add_argument('--deeper', action='store_true')
    ap.add_argument('--sets', action='store_true')
    ap.add_argument('--shapes', type=int, default=400,
                    help='PREFIX of gisland.stratum(6, lamcap=99); the '
                         'landed figures are --shapes 7892 (EXHAUSTIVE)')
    ap.add_argument('--draws', type=int, default=8,
                    help='exact rational draws per block; a GOOD verdict is '
                         'a witness, a NOT-GOOD verdict is capped')
    ap.add_argument('--only', default=None,
                    help='--deeper only: comma list of shape indices, so the '
                         'cap control can be aimed at the shapes --split '
                         'found failures on (PerShapeCensus makes this '
                         'order-independent)')
    ap.add_argument('--deep', type=int, default=64,
                    help='the deeper draw count --deeper compares against')
    ap.add_argument('--out', default=None,
                    help='write the per-triple records here (JSON); --rule '
                         'reads them back')
    a = ap.parse_args(argv)
    rc = 0
    if a.split:
        rc |= leg_split(shape_cap=a.shapes, draws=a.draws, out_path=a.out)
    if a.rule:
        if not a.out:
            ap.error('--rule needs --out naming the records --split wrote')
        rc |= leg_rule(a.out)
    if a.deeper:
        only = (set(int(x) for x in a.only.split(',')) if a.only else None)
        rc |= leg_deeper(shape_cap=a.shapes, draws=a.draws, deep=a.deep,
                         only=only)
    if a.sets:
        rc |= leg_sets(shape_cap=a.shapes, draws=a.draws)
    if not (a.split or a.rule or a.deeper or a.sets):
        ap.error('pick a leg: --split / --rule / --deeper / --sets')
    return rc


if __name__ == '__main__':
    sys.exit(main())
