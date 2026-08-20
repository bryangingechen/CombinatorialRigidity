"""
Phase 39, section (K-out) CONTINUATION (direction ZNEQ) -- (OC-19) INPUT (a),
`Z != empty`, as a statement in its own right.

WHY THIS DRIVER EXISTS.  `notes/Pencil-informal.md` section (K-out) *Step O15*
factors (OC-8) at a (shape, split) into three inputs, of which **(a) `Z !=
empty`** -- the chart carries a hard-stratum target-rank point -- is *"a
prerequisite of the whole (K-tight) criterion, not of (OUT)"*, and *Step O18*
item 2 asks for it *"as a statement in its own right"*:

    at every class (shape, split), the pencil chart of `G' = G - v + ab`
    carries a target-rank point with `s_0 = 0`.

By (OC-17), `dim R_a = corank(G') - s_0` at every legal chart point, so at
`index(G) = 0`, `def(G') = 0` that locus is
`Z = {rank R(G') = tgt} cap {rank R(G-v) = 5|E(G-v)|}` -- two maximal-rank
conditions, Zariski OPEN.  Nobody has measured it unfiltered, and the probe
*Step O18*/(*What would change this* item 1) names verbatim is *"extend
`--control`'s unfiltered leg to a POOL-S-style shape pool and report the `s_0`
histogram per (shape, split) rather than per seed"*.  This driver runs that
probe and tests the four sentences the pass mints on top of it.

  (OC-23) THE PENDANT-EDGE REDUCTION:  `s_0 = corank R(H)`.
    In `widened.orient`'s frame the chain is `b - v - a - c` with `v`, `a`
    interior (degree 2) and `b`, `c` hubs, so `E(G-v) = E(H) + {ac}` with
    `H = G - v - a` and `a` of degree ONE in `G - v`.  The five `ac` rows
    restricted to the `a` block span `C(ac)^perp` (5-dimensional whenever
    `pt(a) != pt(c)`), so every stress of `G - v` vanishes on them: hence
    `corank R(G-v) = corank R(H)` at EVERY chart point.  The `s_0` half of
    input (a) therefore contains no `v`, no `a`, no split edge and no
    `lambda`: it is INDEPENDENCE of the far framework `H`.  (Same one-line
    argument (OC-17) runs on the `ab` rows; here it is run on a pendant edge.)

  (OC-25) INPUT (a) IS AN INSTANCE OF THE (K-tight) CRITERION, ONE SPLIT DOWN.
    Section (K-tight) *Step 2* item 1 at the substituted instance
    `(G, v, a, b) -> (G', a, b, c)` reads, at every chart point with `pt(a)
    not in {pt(b), pt(c)}`,
        corank R(G')  =  corank R(H)  +  dim(U_H cap C(ab)^perp cap C(ac)^perp)
    with `U_H = {u : <u, m(b) - m(c)> = 0 for every motion m of H}`; and
    `dim{m(b) - m(c)} = 3 + sigma`, `dim U_H = 3 - sigma` for
    `sigma := corank R(H)`.  Hence
        a chart point lies in `Z`
          <=>  sigma = 0  AND  the two functionals `<., C(ab)>`, `<., C(ac)>`
               are linearly INDEPENDENT on the 3-space `U_H`,
    which is *Step 2* item 1's own attainment criterion.  So the prerequisite
    of the criterion is an instance of the criterion, one split down the chain
    -- and the regress terminates in ONE step, because `orient`'s chain has
    exactly two interior vertices.

  (OC-26) THE MEET-LINE FIBRE.  `pt(a)` is confined to the meet line
    `M = Pi(b) cap Pi(c)` (its two `G'`-neighbours are the hubs `b`, `c`), and
    on `M` both `C(ab)` and `C(ac)` are AFFINE-LINEAR in the parameter `t`.
    At `sigma = 0` the functional matrix is 2 x 3, so its THREE 2x2 minors are
    quadratics in `t` and the bad set is their COMMON zero locus: three
    conditions on one parameter, hence generically EMPTY -- and when it is
    empty the whole `pt(a)`-fibre over a `sigma = 0` point of the chart lies
    in `Z`.  Bad at EVERY `t` has an exact closed form, an EQUIVALENCE and a
    DISJUNCTION (the first reading of it, "a pencil inside D", is REFUTED by
    Case C below):
        bad at every t  <=>  dim(D cap (M^ ^ W)) >= 3   OR   M^ ^ w
                             subseteq D for some `w` in `W`,
    where `D = {m(b) - m(c) : m in Mot(H)} = U_H^perp` is the 3-dimensional
    relative twist space of `H`, `M^` the 2-space of the meet line and
    `W = <pt(b)^, pt(c)^>` that of the hub line.  Both disjuncts force
    `dim(D cap (M^ ^ W)) >= 2`, a codimension-2 Schubert jump off the generic
    value 1 (measured 1 at every frame).  The weaker degeneracy
    `D cap (M^ ^ b^) != 0` makes ONE point of `M` bad, not the whole line.
    `--factor` computes the exact `Q[t]` GCD of the three minors per frame
    (degree 0 = no bad `t` at all, over any extension), asserts the closed
    form against it at every frame, and CONSTRUCTS all three configurations
    synthetically as the must-reject witnesses (README section 4
    convention 6), with 60 negative controls.

  (OC-27) THE MEASUREMENT.  `--sweep` searches, per (shape, split), for a
    chart point CERTIFIED in `Z` by exact rank computations, and reports the
    `(target rank?, s_0)` histogram per (shape, split), never per seed.  Each
    success is a WITNESS, not a rate: `Z != empty` at that (shape, split) is
    PROVEN by one point (the (OC-7) standing rule leaves positive existence
    witnesses unharmed and forbids the rate reading, which this mode does not
    take).

  (OC-28) THE `s_0` HALF IS DOMINATED BY THE GRID ROUTE.  `H` omits both `v`
    and `a`, so the `H`-part of a pencil configuration of `G` extends to a
    `G'`-chart point by re-placing `pt(a)` anywhere on `M` -- which
    `--transfer` performs as a CONSTRUCTION, guards and all; and at a
    configuration where `G` attains its Tay target, `corank R(G) = 0` (tight,
    `def = 0`), hence `corank R(H) = 0`.  `--reject` exhibits the converse
    boundary: at `P21` (a (K-res) shape, `hnoRigid` FAILING) the arc's five
    recorded `dim R_a = 0` seeds have `s_0 = corank R(H) = 1`, so `{s_0 = 0}`
    is a PROPER open with a non-thin complement -- the `s_0` half is not
    vacuous, and `hnoRigid` is the only tool the arc has against it.

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --factor
    PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --sweep
    PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --reject
    PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --transfer

POOLS.  Every figure is over exactly one pool.  NOTHING here is aggregated
with POOL-C/G/S/B (`outerline`), POOL-CW/A/W/SL (`outerwide`) or
POOL-OV/OC/OZ (`ocon`); in particular POOL-G and POOL-S are pinned and are
neither re-sampled nor extended by this pass.

  POOL-ZF (--factor)  the 4 `lambda.habitat_specs` habitats x placement seeds
                      300-303, UNFILTERED but guard-accepted through
                      `outer.chart_point` (`repin.star_generic` +
                      `verify_pencil_witness`), every eligible split.
  POOL-ZQ (--factor)  synthetic exact-Q subspaces of `Lambda^2 K^4` from
                      `random.Random(20260819)` plus the TWO CONSTRUCTED
                      identical-badness witnesses and their negative controls.
                      No graph, no placement.
  POOL-ZN (--sweep)   `outer.named_inventory()` (19 named class shapes) plus
                      the first 4 shapes of each `outer.sweep_shapes()` family
                      -- the same shape construction POOL-S uses, at a
                      DIFFERENT seed window and with no stratum filter -- at
                      every eligible split carrying a length-4 companion (90),
                      plus a disclosed stride subsample of the remaining
                      eligible splits.  CAP DISCLOSED (README section 4
                      convention 8): the per-family shape cap is 4 and the
                      per-split seed window is 6 seeds; the 190 non-companion
                      eligible splits are covered only at the stride below.
  POOL-ZT (--transfer)
                      the 4 habitats x every eligible split x placement seeds
                      500-507 of the WHOLE graph `G`, guard-accepted for `G`,
                      then `pt(a)` slid onto `M` at the first of 8 pinned
                      rational parameters the `G'` guards accept.
  POOL-ZR (--reject)  `P21` (`flanks.P21_SPECS`), split `v = pmap[0][1]`,
                      seeds 101-140 -- the same window section (K-flank)
                      *F5(d)* used, re-read in `s_0`/`corank(H)` coordinates.

CONVENTIONS (`notes/scripts/README.md` section 4).  Exact Q only; `rank_modp`
appears ONLY as a certified lower bound to SCREEN a seed, and every accepted
witness is rechecked in exact Q (convention 2).  A rank/dimension assert on
every sampled object.  Every rng is `random.Random(<literal>)` and the seeds
are printed.  No bare `set` is printed.  Nothing existing is modified:
`outer.py`, `outerline.py`, `ocon.py`, `repin.py`, `flanks.py`, `widened.py`,
`kslidecomb.py` are all READ.

LAYERING (`notes/scripts/README.md` section 2).  A `w4/` leaf ABOVE `ocon`,
which it imports read-only (`meet`, the dimension-asserting wrapper of
`lambda.span_meet`) together with
`outerline` (`weld_motions`, `rel_span`), `outer` (`split_data`,
`eligible_splits`, `named_inventory`, `sweep_shapes`, `companions4`,
`chart_point`, `stratum_at`, `panel_frame`), `flanks` (`P21_SPECS`) and
`kslidecomb` (`shape_data`); everything else is a catalogued section-1
primitive.  DEBT NOTE for a successor: `ocon.meet` (the dimension-asserting
`span_meet` wrapper) now has two consumers, which is section-2 rule 2's trigger
to move it down beside `lambda.span_meet`; this pass may not modify a landed
file, so the move is recorded, not made.
"""
import importlib
import random
import sys
import time
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, hat, nullspace, rank, wedge2            # noqa: E402
from kbare_common import (rank_modp, verify_pencil_witness,        # noqa: E402
                          verts_of)
from nogood_subdiv import deficiency                               # noqa: E402
from pencil_escape import build_rigidity                           # noqa: E402
from repin import rank_at_V, span_basis, star_generic              # noqa: E402
from widened import orient, split_report                           # noqa: E402
import outer                                                       # noqa: E402
import outerline as OL                                             # noqa: E402
import ocon                                                        # noqa: E402

LAM = importlib.import_module('lambda')

FACTOR_SEEDS = range(300, 304)
SWEEP_SEEDS = range(400, 406)
SWEEP_SHAPE_CAP = 4          # per sweep_shapes family (POOL-S's construction)
SWEEP_OTHER_STRIDE = 4       # the disclosed stride on non-companion splits
REJECT_SEEDS = range(101, 141)
SYNTH_SEED = 20260819


# ---------------- the primitives this pass added -----------------------------

# SIX OF THEM MOVED DOWN to `ocon` on 2026-08-20 (the harness move-down
# round, slice 2): `corank_at`, `u_space`, `poly_gcd`, `schubert_data`,
# `meet_param_of` and `bad_t_polys` each gained a second consumer (`oschu`)
# past README §2 rule 2's trigger, and `ocon` -- the §(K-out) continuation
# module this one already imports -- is the layer under both.  Their private
# helpers `func_matrix` / `aff_mul` / `poly_trim` went with them.  All nine are
# re-exported here, so this module's own modes and `oschu`'s `zneq.<name>`
# call sites are unchanged and no recorded figure moves.  `corank_modp` stays:
# it is the GF(p) SCREEN, it needs `build_rigidity` + `rank_modp`, and it has
# one consumer.
from ocon import (aff_mul, bad_t_polys, corank_at,      # noqa: E402,F401
                  func_matrix, meet_param_of, poly_gcd,
                  poly_trim, schubert_data, u_space)


def corank_modp(edges, placed, V):
    """`5|edges| - rank_modp`, an UPPER bound for the exact corank (README
    section 4 convention 2: `rank_modp <= rank_Q`).  Used only to SCREEN a
    seed; every accepted witness is rechecked in exact Q."""
    rows, _er, _C, _idx, _n = build_rigidity({'edges': edges, 'V': V,
                                              'pt': placed})
    return 5 * len(edges) - rank_modp(rows)


def ledger(E, v, a, b, c, Gp, Hed, placed, Vp, VH, dfp, exact=True,
           deep=True):
    """The whole input-(a) ledger at ONE chart point: target rank, `s_0`,
    `corank(H)`, and -- when `exact` -- (OC-23)'s identity `s_0 = corank(H)`
    and (OC-25)'s corank identity, both asserted."""
    nG = len(verts_of(E))
    tgt = 6 * (nG - 2) - dfp
    shared = [e for e in Gp if set(e) != {a, b}]
    assert len(shared) == len(Hed) + 1, \
        "E(G-v) is not E(H) + one pendant edge"
    if not exact:
        ck = corank_modp(Gp, placed, Vp)
        sg = corank_modp(Hed, placed, VH)
        return {'tgt': tgt, 'rkp': 5 * len(Gp) - ck, 'corankGp': ck,
                'sigma': sg, 's0': None,
                'inZ': (5 * len(Gp) - ck == tgt and sg == 0), 'exact': False}
    ckp, rkp = corank_at(Gp, placed, Vp)
    s0, _ = corank_at(shared, placed, Vp)
    sigma, _ = corank_at(Hed, placed, VH)
    assert placed[a] != placed[c], "pt(a) = pt(c): C(ac) degenerate"
    assert s0 == sigma, \
        f"(OC-23) FAILED: s_0 = {s0} != corank(H) = {sigma}"
    if not deep:
        return {'tgt': tgt, 'rkp': rkp, 'corankGp': ckp, 's0': s0,
                'sigma': sigma, 'inZ': (rkp == tgt and s0 == 0),
                'exact': True, 'deep': False}
    U, D = u_space(Hed, VH, placed, b, c, sigma)
    Cab = wedge2(hat(placed[a]), hat(placed[b]))
    Cac = wedge2(hat(placed[a]), hat(placed[c]))
    assert rank([Cab, Cac]) == 2, "the two chain hinge lines are dependent"
    _A, rkA, dimW = func_matrix(U, Cab, Cac)
    assert ckp == sigma + dimW, \
        f"(OC-25) FAILED: corank(G') = {ckp} != {sigma} + {dimW}"
    inZ = (rkp == tgt and s0 == 0)
    assert inZ == (sigma == 0 and rkA == 2), \
        "(OC-25) FAILED: the Z-membership equivalence"
    return {'tgt': tgt, 'rkp': rkp, 'corankGp': ckp, 's0': s0, 'sigma': sigma,
            'dimU': len(U), 'dimD': len(D), 'dimW': dimW, 'rkA': rkA,
            'inZ': inZ, 'exact': True, 'U': U}


# ---------------- --factor: the reduction, and the off-Z construction -------

def synthetic():
    """(OC-26)'s two identical-badness cases, CONSTRUCTED (POOL-ZQ), with
    negative controls -- README section 4 convention 6: a criterion observed
    only passing is untested, and no graph frame realizes these."""
    print("\n   POOL-ZQ: (OC-26)'s identical-badness cases, CONSTRUCTED "
          "synthetically.")
    print(f"     rng: random.Random({SYNTH_SEED}); no graph, no placement.")
    rng = random.Random(SYNTH_SEED)
    e = [[F(1) if k == i else F(0) for k in range(4)] for i in range(4)]
    # the meet line M = <e0, e1>; the two hub points off it; W = <b, c>
    P0, Pd, pb, pc = e[0], e[1], e[2], e[3]
    Mhat = [P0, Pd]
    assert rank(Mhat + [pb, pc]) == 4, "the synthetic frame is degenerate"

    def minors_of(U):
        A0 = [[dot(u, wedge2(P0, pb)) for u in U],
              [dot(u, wedge2(P0, pc)) for u in U]]
        A1 = [[dot(u, wedge2(Pd, pb)) for u in U],
              [dot(u, wedge2(Pd, pc)) for u in U]]
        n = len(U)
        ent = [[(A0[r][j], A1[r][j]) for j in range(n)] for r in range(2)]
        out = []
        for i in range(n):
            for j in range(i + 1, n):
                p = aff_mul(ent[0][i], ent[1][j])
                q = aff_mul(ent[0][j], ent[1][i])
                out.append(tuple(p[k] - q[k] for k in range(3)))
        return out

    # CASE A: D contains the pencil M^ ^ w for w = c - 2b on the line bc.
    w = [pc[k] - 2 * pb[k] for k in range(4)]
    penc = [wedge2(P0, w), wedge2(Pd, w)]
    assert rank(penc) == 2, "the constructed pencil is not 2-dimensional"
    while True:
        extra = [F(rng.randint(-6, 6)) for _ in range(6)]
        D = span_basis(penc + [extra])
        if len(D) == 3:
            break
    U = span_basis(nullspace(D))
    assert len(U) == 3, "U is not the 3-dim perp of a 3-dim D"
    mA = minors_of(U)
    assert all(p == (0, 0, 0) for p in mA), \
        "(OC-26) Case A FAILED: the pencil containment did not make every " \
        "minor vanish identically"
    sdA = schubert_data(U, Mhat, [pb, pc])
    assert sdA['pencil'] and sdA['dimK'] >= 2, \
        f"Case A: expected a pencil inside D and dimK >= 2, got {sdA}"
    print("     CASE A (the first identical-badness disjunct)  "
          "M^ ^ w subseteq D,")
    print(f"       w = pt(c) - 2 pt(b):  all {len(mA)} minors vanish "
          f"IDENTICALLY in t, so the WHOLE meet")
    print("       line is bad and `sigma = 0` does NOT by itself put a chart "
          f"point in Z.\n       (dim(D cap M^ ^ W) = {sdA['dimK']}, pencil "
          f"= {sdA['pencil']}.)")

    # CASE B: D meets the pencil M^ ^ b^ (the f-pair dependent), constructed
    # by putting ONE line of that pencil into D.
    while True:
        extra1 = [F(rng.randint(-6, 6)) for _ in range(6)]
        extra2 = [F(rng.randint(-6, 6)) for _ in range(6)]
        DB = span_basis([wedge2([P0[k] + Pd[k] for k in range(4)], pb),
                         extra1, extra2])
        if len(DB) == 3:
            break
    UB = span_basis(nullspace(DB))
    assert len(UB) == 3
    A0 = [dot(u, wedge2(P0, pb)) for u in UB]
    A1 = [dot(u, wedge2(Pd, pb)) for u in UB]
    assert rank([A0, A1]) == 1, \
        "(OC-26) Case B FAILED: the f-pair is not dependent on U"
    assert len(ocon.meet(DB, span_basis([wedge2(P0, pb), wedge2(Pd, pb)]))) >= 1, \
        "Case B: D misses the pencil M^ ^ b^"
    mB = minors_of(UB)
    gB = poly_gcd(mB)
    assert gB and len(gB) == 2, \
        "(OC-26) Case B: the weaker degeneracy did not make exactly one " \
        "point of M bad"
    print("     CASE B (the WEAKER degeneracy)  D cap (M^ ^ b^) != 0:  the "
          "`b`-side functional pair\n       is dependent on U_H at every t "
          f"(rank 1 asserted), and the bad-t GCD has degree "
          f"{len(gB) - 1} --")
    print("       exactly ONE bad point of M, not the whole line.  So `D "
          "meets ONE pencil of\n       M^ ^ b^` is strictly weaker than "
          "identical badness.")

    # CASE C -- THE REFUTATION ATTEMPT.  Is `Mhat ^ w subseteq D for some w`
    # the ONLY identical-badness configuration?  NO: take `D` = a hyperplane of
    # `Mhat ^ W` whose 2x2 matrix is NONSINGULAR.  Then `rank Phi = 1`, so the
    # whole meet line is bad, and yet NO pencil lies inside `D`.  So the
    # tempting equivalence "identically bad <=> a pencil inside D" is FALSE,
    # and the correct statement is the DISJUNCTION.
    DC = span_basis([wedge2(P0, pc), wedge2(Pd, pb),
                     [wedge2(P0, pb)[k] - wedge2(Pd, pc)[k] for k in range(6)]])
    assert len(DC) == 3, "Case C's D is not 3-dimensional"
    UC = span_basis(nullspace(DC))
    assert len(UC) == 3, "Case C's U is not 3-dimensional"
    sdC = schubert_data(UC, Mhat, [pb, pc])
    mC = minors_of(UC)
    assert all(p == (0, 0, 0) for p in mC), \
        "Case C: rank Phi = 1 did not make the whole line bad"
    assert sdC['dimK'] == 3 and not sdC['pencil'], \
        f"Case C: expected (dimK, pencil) = (3, False), got " \
        f"({sdC['dimK']}, {sdC['pencil']})"
    print("     CASE C (the REFUTATION of the tempting equivalence)  "
          "D a NONSINGULAR hyperplane")
    print("       of M^ ^ W:  dim(D cap M^ ^ W) = 3, NO pencil M^ ^ w inside "
          "D, and yet all")
    print(f"       {len(mC)} minors vanish identically.  So `identically bad "
          "<=> a pencil inside D`\n       is FALSE; the correct closed form "
          "is the DISJUNCTION `dimK >= 3 or a pencil`,\n       and both "
          "disjuncts force the codimension-2 jump `dimK >= 2`.")

    # NEGATIVE CONTROLS: random 3-spaces D realize NONE of the cases, and their
    # bad-t GCD is a nonzero CONSTANT -- no bad t in any extension of Q.
    ncon, gdeg = 0, {}
    for _ in range(60):
        while True:
            Dr = span_basis([[F(rng.randint(-6, 6)) for _ in range(6)]
                             for _ in range(3)])
            if len(Dr) == 3:
                break
        Ur = span_basis(nullspace(Dr))
        if len(Ur) != 3:
            continue
        g = poly_gcd(minors_of(Ur))
        gdeg[len(g) - 1 if g else 'all-zero'] = \
            gdeg.get(len(g) - 1 if g else 'all-zero', 0) + 1
        sdr = schubert_data(Ur, Mhat, [pb, pc])
        assert sdr['dimK'] == 1 and not sdr['pencil'], \
            f"a random D hit a Schubert degeneracy: {sdr}"
        assert g and len(g) == 1, \
            "a random D produced a common bad t -- the control failed"
        ncon += 1
    print(f"     NEGATIVE CONTROL  {ncon} random 3-spaces D: bad-t GCD degree "
          f"-> count {dict(sorted(gdeg.items(), key=str))}")
    print("       (degree 0 = the three minors have NO common root in any "
          "extension of Q,\n        so EVERY point of the meet line is good "
          "-- the generic behaviour.)")


def factor():
    print("== (OC-23)/(OC-25)/(OC-26): input (a) FACTORED, POOL-ZF ==")
    print(f"   POOL-ZF: the 4 lambda.habitat_specs habitats x placement seeds "
          f"{FACTOR_SEEDS.start}-{FACTOR_SEEDS.stop - 1}, every eligible")
    print("   split, UNFILTERED (no target-rank / stratum filter) but "
          "guard-accepted through")
    print("   outer.chart_point -- repin.star_generic + "
          "verify_pencil_witness.")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    hist, tally, nfr, nsplit, nrej = {}, {}, 0, 0, 0
    slidefull = 0
    for name, E, _v0, _cmp in LAM.HABITATS4:
        for v in outer.eligible_splits(E):
            a, b, c, Gp, Hed = outer.split_data(E, v)
            Vp, VH = (sorted(verts_of(Gp), key=str),
                      sorted(verts_of(Hed), key=str))
            dfp = deficiency(Gp)
            nsplit += 1
            for seed in FACTOR_SEEDS:
                cp = outer.chart_point(Gp, random.Random(seed))
                if cp is None:
                    nrej += 1
                    continue
                placed, _pt, nrm = cp
                d = ledger(E, v, a, b, c, Gp, Hed, placed, Vp, VH, dfp)
                nfr += 1
                key = (d['rkp'] == d['tgt'], d['s0'], d['sigma'],
                       d['dimU'], d['dimW'], d['inZ'])
                hist[key] = hist.get(key, 0) + 1
                # (OC-17) cross-check against the catalogued stratum oracle
                st = outer.stratum_at(E, Gp, placed, a, b)
                if d['rkp'] == d['tgt']:
                    assert st is not None and st[1] == 1 - d['s0'], \
                        "(OC-17) FAILED against outer.stratum_at"
                else:
                    assert st is None, "stratum_at accepted an off-target point"
                fr = outer.panel_frame(placed, nrm, b, c)
                assert fr is not None, "panels parallel at a chart point"
                M0, Md, _CM = fr
                ta = meet_param_of(placed, M0, Md, a)
                assert ta is not None, \
                    "pt(a) is OFF the meet line M at a chart point"
                if d['sigma'] != 0:
                    continue
                # (OC-26): the bad set on M, exactly, via the Q[t] GCD
                polys = bad_t_polys(d['U'], M0, Md, placed[b], placed[c])
                g = poly_gcd(polys)
                deg = (len(g) - 1) if g else 'all-zero'
                nzero = sum(1 for p in polys if p == (0, 0, 0))
                Mhat = [hat(M0), [Md[0], Md[1], Md[2], F(0)]]
                assert rank(Mhat) == 2, "the meet-line 2-space is degenerate"
                sd = schubert_data(d['U'], Mhat,
                                   [hat(placed[b]), hat(placed[c])])
                # (OC-26)(ii): identical badness <=> dimK >= 3 or a pencil
                assert (deg == 'all-zero') == (sd['dimK'] >= 3
                                               or sd['pencil']), \
                    "(OC-26)(ii) FAILED: the closed form disagrees with the " \
                    "GCD test"
                tally[(len(polys), nzero, deg, sd['dimK'], sd['pencil'])] = \
                    tally.get((len(polys), nzero, deg, sd['dimK'],
                               sd['pencil']), 0) + 1
                assert g, "(OC-26): every minor vanishes identically on M -- " \
                          "IDENTICAL BADNESS realized at a chart point"
                if len(g) == 1:
                    slidefull += 1
                # the sampled pt(a) is one point of the good set, consistently
                assert all(p[0] + ta * p[1] + ta * ta * p[2] == 0
                           for p in polys) == (not d['inZ']), \
                    "(OC-26): the sampled t's goodness disagrees with Z"
    print(f"   splits probed: {nsplit};  chart points accepted: {nfr};  "
          f"draws rejected by the guards: {nrej}")
    print("   (target rank?, s_0, corank(H), dim U_H, dim W, in Z) -> count:")
    for k in sorted(hist, key=str):
        print(f"       {k} : {hist[k]}")
    print("   asserted per frame: (OC-23) s_0 = corank(H); (OC-25)'s corank "
          "identity and its\n     Z-membership equivalence; (OC-17) against "
          "outer.stratum_at; pt(a) ON the meet line.")
    print("\n   (OC-26) the meet-line fibre: (2x2 minors, identically-zero "
          "minors, deg GCD,\n     dim(D cap M^ ^ W), a pencil M^ ^ w "
          "inside D?) -> count:")
    for k in sorted(tally, key=str):
        print(f"       {k} : {tally[k]}")
    print(f"     GCD degree 0 at {slidefull} of {sum(tally.values())} "
          f"`sigma = 0` frames: at each, the three minors have\n     NO "
          f"common root in ANY extension of Q, so EVERY point of the meet "
          f"line `M`\n     gives a target-rank point -- the whole `pt(a)`-"
          f"fibre over that `H`-part lies in `Z`.")
    synthetic()
    print("\nFACTOR OK.")


# ---------------- --sweep: the cheap probe OCON named -----------------------

def sweep_pool():
    """POOL-ZN's (family, label, E) list: POOL-S's shape construction --
    `outer.named_inventory()` plus the first SWEEP_SHAPE_CAP shapes of each
    `outer.sweep_shapes()` family.  The cap is DISCLOSED wherever a figure
    from this pool is quoted (README section 4 convention 8)."""
    fams = [('named', outer.named_inventory())]
    for fname, fam in outer.sweep_shapes():
        fams.append((fname.split(' ')[0], fam[:SWEEP_SHAPE_CAP]))
    return fams


def sweep():
    t_start = time.time()
    print("== (OC-27): is `Z != empty` at every (shape, split)?  POOL-ZN ==")
    print(f"   POOL-ZN: outer.named_inventory() (19 named class shapes) plus "
          f"the first\n            {SWEEP_SHAPE_CAP} shapes of each "
          f"outer.sweep_shapes() family -- POOL-S's SHAPE construction,")
    print(f"            at the DIFFERENT seed window "
          f"{SWEEP_SEEDS.start}-{SWEEP_SEEDS.stop - 1} and with NO stratum "
          f"filter.\n            Neither POOL-S nor POOL-G is re-sampled, "
          f"extended or aggregated with.")
    print("   Population: every eligible split carrying a length-4 companion "
          "(where a\n   `Z = empty` shape would be a (K-tight) event), plus "
          f"every {SWEEP_OTHER_STRIDE}th of the remaining\n   eligible "
          "splits.  CAPS DISCLOSED: shape cap "
          f"{SWEEP_SHAPE_CAP}/family, seed window "
          f"{len(list(SWEEP_SEEDS))},\n   stride {SWEEP_OTHER_STRIDE} on the "
          "non-companion splits; nothing here reports on the\n   families "
          "beyond those bounds.")
    print("   Each success is a WITNESS (one exact-Q chart point in Z), never "
          "a rate: the\n   (OC-7) standing rule forbids the rate reading and "
          "leaves existence unharmed.\n")
    fams = sweep_pool()
    hist, per_family, misses, ncomp, nother, ndraw = {}, {}, [], 0, 0, 0
    seedhist = {}
    for fname, fam in fams:
        tally = {'splits': 0, 'inZ': 0}
        others = []
        jobs = []
        for label, E in fam:
            for v in outer.eligible_splits(E):
                a, b, c, Gp, Hed = outer.split_data(E, v)
                if outer.companions4(Hed, b, c):
                    jobs.append((label, E, v, True))
                else:
                    others.append((label, E, v, False))
        jobs += others[::SWEEP_OTHER_STRIDE]
        for label, E, v, has4 in jobs:
            a, b, c, Gp, Hed = outer.split_data(E, v)
            Vp, VH = (sorted(verts_of(Gp), key=str),
                      sorted(verts_of(Hed), key=str))
            dfp = deficiency(Gp)
            tally['splits'] += 1
            ncomp, nother = (ncomp + 1, nother) if has4 else (ncomp, nother + 1)
            got, ndrawn = None, 0
            for seed in SWEEP_SEEDS:
                cp = outer.chart_point(Gp, random.Random(seed))
                if cp is None:
                    continue
                ndrawn += 1
                ndraw += 1
                scr = ledger(E, v, a, b, c, Gp, Hed, cp[0], Vp, VH, dfp,
                             exact=False)
                if not scr['inZ']:
                    hist[('screened off Z', scr['rkp'] == scr['tgt'],
                          scr['sigma'])] = \
                        hist.get(('screened off Z', scr['rkp'] == scr['tgt'],
                                  scr['sigma']), 0) + 1
                    continue
                # exact-Q recheck of the attaining sample (convention 2);
                # the (OC-25) leg runs at the FIRST witness of each family
                # (disclosed), `--factor` running it at every POOL-ZF frame
                d = ledger(E, v, a, b, c, Gp, Hed, cp[0], Vp, VH, dfp,
                           deep=(tally['inZ'] == 0))
                assert d['inZ'], "the GF(p) screen mispredicted membership"
                got = (seed, d)
                break
            key = ('WITNESS in Z' if got else 'NO witness in scope', has4)
            hist[key] = hist.get(key, 0) + 1
            if got:
                tally['inZ'] += 1
                seedhist[got[0]] = seedhist.get(got[0], 0) + 1
            else:
                misses.append((fname, label, v, has4, ndrawn))
        per_family[fname] = tally
        print(f"   {fname:8s}: {tally['splits']:3d} splits probed, "
              f"{tally['inZ']:3d} with a certified point in Z"
              f"   [{round(time.time() - t_start)} s]")
    print(f"\n   splits probed: {ncomp} carrying a length-4 companion + "
          f"{nother} others = {ncomp + nother}")
    print(f"   chart points drawn (unfiltered): {ndraw}")
    print("   per-(shape, split) outcome -> count:")
    for k in sorted(hist, key=str):
        print(f"       {k} : {hist[k]}")
    print(f"   seed of the first witness -> count: "
          f"{dict(sorted(seedhist.items()))}")
    if misses:
        print("   (shape, split) with NO certified point in Z in scope "
              "(family, label, split, carries a length-4 companion, draws):")
        for r in misses:
            print(f"       {r}")
        print("   READ THIS CORRECTLY: a miss at a length-4-companion split "
              "is a candidate\n   (K-tight) EVENT -- it would make (OC-8) "
              "false there and kill routes A and B at\n   that split by "
              "(K-tight) *Step 2* item 3 -- but within a 6-seed window it is "
              "a\n   candidate only, not a `Z = empty` proof.")
    else:
        print("   NO miss: every (shape, split) probed carries an exact-Q "
              "certified point of Z,\n   so `Z != empty` is PROVEN at each "
              "of them individually (one witness suffices;\n   openness is "
              "(OC-17)'s, irreducibility is not needed for a witness).")
    print("\n   asserted per witness: exact-Q rank R(G') = tgt and "
          "corank R(G-v) = 0, plus (OC-23)'s\n     s_0 = corank(H).  "
          "(OC-25)'s corank identity and Z-membership equivalence run at the "
          "FIRST\n     witness of each family here (disclosed) and at every "
          "POOL-ZF frame in --factor.")
    print(f"\nSWEEP OK  [{round(time.time() - t_start)} s]")


# ---------------- --reject: the must-reject witness at P21 ------------------

def reject():
    print("== (OC-28)'s boundary: `{s_0 = 0}` is a PROPER open.  POOL-ZR ==")
    from flanks import P21_SPECS
    from kslidecomb import shape_data
    edges, pmap = shape_data(P21_SPECS)
    v = pmap[0][1]
    a, b, c = orient(edges, v)
    Gp = [e for e in edges if v not in e] + [(a, b)]
    Hed = [e for e in edges if v not in e and a not in e]
    Vp, VH = sorted(verts_of(Gp), key=str), sorted(verts_of(Hed), key=str)
    dfp = deficiency(Gp)
    nG = len(verts_of(edges))
    tgt = 6 * (nG - 2) - dfp
    sr = split_report(edges, v)
    print(f"   POOL-ZR: P21 (flanks.P21_SPECS), split v = {v}, a = {a}, "
          f"b = {b}, c = {c}, seeds "
          f"{REJECT_SEEDS.start}-{REJECT_SEEDS.stop - 1}.")
    print("   P21 is a (K-res) shape: it FAILS `hnoRigid`, so it is NOT a "
          "tight class member\n   (section (K-pure) P4/P7).  It is here as "
          "the arc's only recorded `s_0 = 1` witness.")
    print(f"   PINNED COUNTER-FACT (README section 4 convention 6): the "
          f"count-theoretic\n   prediction `widened.split_report` = "
          f"{sr['dim R_a (identity)']} = 5 + def(G') - def(G-v), i.e. the "
          f"COUNT\n   predicts s_0 = 0 at every placement.  Geometry "
          f"disagrees on a non-thin locus.\n")
    from repin import seed_probe
    jump, fine, invalid = [], 0, 0
    for s in REJECT_SEEDS:
        p = seed_probe(edges, v, s, nplace=0)
        if p is None:
            invalid += 1
            continue
        placed = p['_ctx'][0]
        sigma, _ = corank_at(Hed, placed, VH)
        s0, _ = corank_at([e for e in Gp if set(e) != {a, b}], placed, Vp)
        assert s0 == p['s0'], "s_0 disagrees with repin.seed_probe"
        assert s0 == sigma, \
            f"(OC-23) FAILED at P21 seed {s}: s_0 = {s0} != corank(H) = {sigma}"
        if p['dim R_a'] >= 1:
            assert s0 == 0, "dim R_a >= 1 at target rank with s_0 > 0"
            fine += 1
            continue
        assert p['s0'] == 1 and p['dim U'] == 1, (s, p['s0'], p['dim U'])
        U, D = u_space(Hed, VH, placed, b, c, sigma)
        rkp, _r, _e, _i = rank_at_V(Gp, placed, Vp)
        assert rkp == tgt, "the jump seed is off target rank"
        Cab = wedge2(hat(placed[a]), hat(placed[b]))
        Cac = wedge2(hat(placed[a]), hat(placed[c]))
        _A, rkA, dimW = func_matrix(U, Cab, Cac)
        assert 5 * len(Gp) - rkp == sigma + dimW, \
            "(OC-25) FAILED at the P21 jump seed"
        jump.append((s, s0, sigma, len(U), len(D), rkA, dimW))
    print("   (seed, s_0, corank(H), dim U_H, dim{m(b)-m(c)}, rank of the two "
          "functionals, dim W)\n   at every `dim R_a = 0` seed:")
    for r in jump:
        print(f"       {r}")
    print(f"   seeds {REJECT_SEEDS.start}-{REJECT_SEEDS.stop - 1}: {fine} "
          f"with s_0 = 0 (in Z), {len(jump)} with s_0 = 1 (OFF Z), "
          f"{invalid} invalid")
    assert jump and fine, (len(jump), fine)
    print("   => `{s_0 = 0}` is a PROPER open of the chart, its complement "
          "NOT thin in the\n      sampler's rational range, and (OC-23) "
          "holds at the rejecting points too:\n      the `s_0` half of input "
          "(a) is a genuine INDEPENDENCE statement about `H`,\n      not an "
          "arithmetic identity.  The mechanism is section (K-flank) *F5(d)*'s "
          "theta\n      sub-multigraph stress -- a self-stress of a "
          "SUBframework of `H`, i.e. the\n      combinatorially-certifiable "
          "direction of `Pencil-strategy.md` section 2.3.")
    print("\nREJECT OK.")


# ---------------- --transfer: (OC-28)(i)/(ii) CONSTRUCTED --------------------

TRANSFER_SEEDS = range(500, 508)
SLIDE_TS = (F(1), F(-1), F(2), F(1, 2), F(-3), F(3), F(5), F(-1, 3))


def transfer():
    """(OC-28)(i)/(ii) as a CONSTRUCTION rather than an argument: take a chart
    point of the WHOLE graph `G` (so `v` is placed and `pt(a)` sits in `Pi(c)`
    only), keep the `H`-part verbatim, drop `v`, and re-place `pt(a)` on the
    meet line `M`.  If the harness's own chart-point guards accept the result
    for `G'`, then the `H`-part of a `G`-chart point IS the `H`-part of a
    `G'`-chart point, and `corank R(H)` cannot have moved -- both asserted."""
    from widened import place_pencil_general
    print("== (OC-28)(i)/(ii) CONSTRUCTED: G-chart point -> G'-chart point, "
          "POOL-ZT ==")
    print(f"   POOL-ZT: the 4 lambda.habitat_specs habitats x every eligible "
          f"split x placement\n            seeds {TRANSFER_SEEDS.start}-"
          f"{TRANSFER_SEEDS.stop - 1} of the WHOLE graph `G` (not of `G'`), "
          f"guard-accepted for `G`,\n            then `pt(a)` slid to "
          f"`M = Pi(b) cap Pi(c)` at the first of "
          f"{len(SLIDE_TS)} pinned rational\n            parameters the "
          f"`G'` guards accept.")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    hist, built, nG_ok, nfail = {}, 0, 0, []
    for name, E, _v0, _cmp in LAM.HABITATS4:
        VG = sorted(verts_of(E), key=str)
        tgtG = 6 * (len(VG) - 1) - deficiency(E)
        for v in outer.eligible_splits(E):
            a, b, c, Gp, Hed = outer.split_data(E, v)
            Vp, VH = (sorted(verts_of(Gp), key=str),
                      sorted(verts_of(Hed), key=str))
            dfp = deficiency(Gp)
            for seed in TRANSFER_SEEDS:
                pl = place_pencil_general(E, random.Random(seed))
                if pl is None:
                    continue
                placed, _pt, nrm, _hubs, _nb = pl
                if not star_generic(E, placed):
                    continue
                okG, _i = verify_pencil_witness(E, placed)
                if not okG:
                    continue
                # the G-side ledger: corank(G) = 0 forces corank(H) = 0
                ckG, rkG = corank_at(E, placed, VG)
                sigma0, _ = corank_at(Hed, placed, VH)
                assert sigma0 <= ckG, \
                    "corank(H) exceeds corank(G): H is not a subgraph?"
                if rkG == tgtG:
                    nG_ok += 1
                    assert ckG == 0, \
                        "G at the Tay target but corank(G) != 0 (not tight?)"
                    assert sigma0 == 0, \
                        "(OC-28)(ii) FAILED: corank(G) = 0 yet corank(H) > 0"
                fr = outer.panel_frame(placed, nrm, b, c)
                if fr is None:
                    continue
                M0, Md, _CM = fr
                landed = None
                for t in SLIDE_TS:
                    pl2 = {x: placed[x] for x in Vp}
                    pl2[a] = [M0[k] + t * Md[k] for k in range(3)]
                    if pl2[a] in (placed[b], placed[c]):
                        continue
                    if not star_generic(Gp, pl2):
                        continue
                    ok2, _i2 = verify_pencil_witness(Gp, pl2)
                    if not ok2:
                        continue
                    landed = (t, pl2)
                    break
                if landed is None:
                    nfail.append((name, v, seed))
                    continue
                t, pl2 = landed
                d = ledger(E, v, a, b, c, Gp, Hed, pl2, Vp, VH, dfp)
                # the H-part was copied verbatim, so sigma CANNOT have moved:
                assert all(pl2[x] == placed[x] for x in VH), \
                    "the H-part was not copied verbatim"
                assert d['sigma'] == sigma0, \
                    "(OC-28)(i) FAILED: sliding pt(a) moved corank(H)"
                built += 1
                key = (rkG == tgtG, sigma0, d['rkp'] == d['tgt'], d['inZ'])
                hist[key] = hist.get(key, 0) + 1
                break
    print(f"   G-chart points at the Tay target: {nG_ok};  transfers "
          f"CONSTRUCTED and guard-accepted for G': {built}")
    print("   (G at target rank?, corank(H) at the G-point, G' at target rank "
          "after the slide,\n    in Z) -> count:")
    for k in sorted(hist, key=str):
        print(f"       {k} : {hist[k]}")
    if nfail:
        print(f"   (shape, split, seed) where no pinned slide parameter was "
              f"accepted: {len(nfail)}")
        for r in nfail:
            print(f"       {r}")
    assert built, "no transfer constructed -- (OC-28)(i)/(ii) untested"
    print("   asserted per transfer: the `H`-part copied VERBATIM; "
          "`corank R(H)` unchanged by the\n     slide; `corank R(G) = 0` "
          "==> `corank R(H) = 0` at every target-rank `G`-point; and the "
          "full\n     (OC-23)/(OC-25) ledger at the landed `G'`-chart point.")
    print("\n   So the `H`-part of a `G`-chart point IS the `H`-part of a "
          "`G'`-chart point, by\n   CONSTRUCTION at every probed (shape, "
          "split) -- (OC-28)(i)'s content in the only form\n   a driver can "
          "test, and (OC-28)(ii)'s transfer with it.")
    print("\nTRANSFER OK.")


def main():
    modes = {'--factor': factor, '--sweep': sweep, '--reject': reject,
             '--transfer': transfer}
    args = [x for x in sys.argv[1:] if x in modes]
    if not args:
        print(__doc__)
        print("pick one of: " + "  ".join(sorted(modes)))
        return
    for x in args:
        modes[x]()


if __name__ == '__main__':
    main()
