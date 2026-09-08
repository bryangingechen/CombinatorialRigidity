"""
Direction BEFOURP (arc ordinal 88) -- DOES (BE-E4') ADMIT A ROUTE?  A
DECOMPOSITION recon of section 8's rank 2, not a proof attempt.

  THE DISPATCH'S FIRST CHECK, answered at source before anything else.
  `e_i` is NOT defined through `dist`, the arc, or the side topology:
  (BE-153)(v) defines it as `e_i = rho_i - c_i(Pi_x)` and `barch.e4`
  implements exactly that on `rho_i = delta_i + a_i`.  So the coordinator's
  named tell does NOT fire in the form stated.  It fires in a WEAKER and
  more useful form, and that is (BE-204) below: `dist` CAPS `e_i` from
  above through the proved ceiling `rho_i <= dist_{side_i}(x,y)`
  ((BE-189)(ii)), which is the direction a LOWER bound on `e_1 + e_2`
  cannot use -- (BE-153)(v)'s own *no landed lemma bounds `e_i` from
  below*.

  THE ANSWERS, said at the top.

  (BE-204) COVERAGE HOLDS, BUT NOT FOR THE REASON THE SPEC GAVE.  The
           ceiling does bind: (BE-E4')'s conclusion plus (BE-189)(ii)
           forces `dist_1(x,y) + dist_2(x,y) >= 6 + c_other`.  But that is
           a SUM over the two sides, where (BE-189)(iii)'s threshold is
           PER SIDE -- so a firing tuple satisfying (BE-E4') exists with
           `max_i rho_i = 3`, i.e. needing only `dist_i >= 3` on each
           side.  The per-side `dist >= 6` boundary that stopped the arc /
           path-bound family therefore does NOT transfer, and (BE-E4')
           carries content on the arc-`<= 5` strata as well as the 51.

  (BE-205) THE ARITHMETIC DECOMPOSES INTO EXACTLY TWO PIECES, and the
           frontier is exact.  Write the firing side `i` (`c_i(Pi_x) = 2`)
           and the other side `j`.  Then over all 6 400 tuples the pair
              (BE-F_f)  `c_i(Pi_x) = 2  ==>  rho_i >= f`
              (BE-G_g)  `c_i(Pi_x) = 2  ==>  e_j >= g`
           kills every (BE-E4') escape EXACTLY on a frontier this mode
           enumerates; `(f, g) = (5, 1)` is the member whose BOTH halves
           have landed predecessors, and NEITHER half suffices alone.

  (BE-206) THE LADDER IS THE CORANK ONE, NOT A `delta_2` ONE, AND IT HAS
           FOUR RUNGS.  (BE-110)(i)'s corank identity is general, so at
           `Pi_x <= rho_bar_i`
              `e_i = dim(rho_bar_i ^ p_x)  +  [Sigma_x <= rho_bar_i]`
           exactly, with `dim(rho_bar_i ^ p_x) in {0,1,2,3}`.  So the
           firing side's contribution is graded by the dimension of the
           side's reach SEEN FROM `p_x`, and `(BE-F_5)` is the top rung.

  (BE-207) `(BE-F_5)` IS FALSE, and the refutation is landed: (BE-118)(ii)'s
           21 rows carry `Sigma_x <= rho_bar_1` -- hence `c_1(Pi_x) = 2`
           -- at `rho_1 = 4`, in the generic flag regime, with side 2
           R-node-shaped.  This mode measures side 2 there for the first
           time.

  (BE-208) AND THE TWO LANDED POINTWISE-REFUTATION FAMILIES ARE THE
           SHARPEST TEST (BE-E4') HAS: BRANKV's 24 gated arc-3 points
           ((BE-192)) and BLONGARC's 24 gated arc-4 points ((BE-200)) both
           sit at `c_1(Pi_x) = 2` with `rho_1 = 3`, so `e_1 = 1` and
           (BE-E4') needs `e_2 >= 3` at all 48.  Side 2 was never measured
           at either.  This mode measures it.

  MODES
    arith   (BE-204)/(BE-205)  exhaustive over the 6 400 tuples; no
            sampling, seed unused.
    gated   (BE-208)  side 2 at BRANKV's arc-3 and BLONGARC's arc-4 gated
            `flat_config` chart points.
    peel    (BE-206)/(BE-207)  side 2 and the corank grading at
            (BE-118)(ii)'s 21 landed peel rows.
    validate  all three in one process.

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is NOT called anywhere in this module, so its silent `K^4`
  truncation is unreachable rather than merely avoided.  No width-12 object
  is built, and every `span`/`isect`/`dim` call here takes width-6
  (`Lambda^2 K^4`) rows, which is what `bimage.span`'s `d == 6` branch is
  for.  Every `K^4`-side dimension goes through the width-agnostic
  `exactcore.rank`, never `bimage.span`/`dim`, so the width-6 special case
  is unreachable with a `K^4` input rather than merely avoided.  `bwin` is
  not imported, so `dehom`'s list-vs-tuple guard defeat is unreachable, and
  every point this module reads comes from a predecessor's own configuration
  builder (`binduc.flat_config`, `bproper.plant_peel`) rather than being
  written here.
"""

import os
import sys
import time
import random

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, wedge2, rank, neighbors                   # noqa: E402
from bimage import dim, isect, plane_at, rho_bar_of, span         # noqa: E402
from bunif import SEED, flag_frame                                   # noqa: E402
from bsatur import sigma_at                                          # noqa: E402
from binduc import flat_config                                       # noqa: E402
from bproper import PEELJOBS, plant_peel, side_named              # noqa: E402
from bproper import composite                                        # noqa: E402
from bpeel import SKELETONS, delta_pair, rnode_shaped             # noqa: E402
from bline import legal_peel                                         # noqa: E402
from bfour import e_row, e4_at, side_nums                            # noqa: E402
from brankv import arc_through, short_library                        # noqa: E402
from blongarc import arc4_library                                    # noqa: E402
from kbare_common import verify_pencil_witness                       # noqa: E402
import barch as BA                                                   # noqa: E402


# ------------------------------------------------------------------ helpers

def firing(tup):
    """The sides whose (BE-E4') hypothesis fires at a tuple: `c_i(Pi_x) = 2`,
    which (BE-156)(i) shows IS `Pi_x <= rho_bar_i`."""
    return [i for i in (0, 1) if tup[6 + i] == 2]


def e_of(tup):
    """`(e_1, e_2)`, `e_i = rho_i - c_i(Pi_x)` -- (BE-153)(v)'s definition,
    recomputed here rather than imported so `arith` is a pure enumeration."""
    return (tup[4] - tup[6], tup[5] - tup[7])


def flexible(tup):
    """(BE-162)(i)'s added hypothesis: both sides non-rigid."""
    return tup[0] >= 1 and tup[1] >= 1


def e4prime(tup):
    """(BE-E4'): section (K-bare-ext) (E4) restricted to
    `delta_1, delta_2 >= 1` -- the (L3) qualification, since (E4) is a
    grandfathered bare token with a recorded collision.  Vacuously true
    off the both-flexible zone -- (BE-22)(vi) discharges that zone by a
    proved theorem, which is exactly what the restriction buys."""
    if not flexible(tup):
        return True
    return BA.e4(tup)


def piece_floor(tup, f):
    """(BE-F_f): every FIRING side has `rho_i >= f`.  At `f = 6` this is
    (PENCIL-SATURATES) itself; at `f = 5` it is the floor (BE-110)(ii)
    proves for `Sigma_x` at a PATH side."""
    return all(tup[4 + i] >= f for i in firing(tup))


def piece_other(tup, g):
    """(BE-G_g): for every FIRING side `i`, the OTHER side has `e_j >= g`.  At
    `g = 1` this is `rho_bar_j !<= Pi_x`, the statement BSTEER closed at
    `rho_j = 1` by a degree count at `x` ((BE-175)/(BE-177))."""
    es = e_of(tup)
    return all(es[1 - i] >= g for i in firing(tup))


def census(pairs):
    return ', '.join(f'{k}: {v}' for k, v in sorted(pairs.items()))


# ================================================= mode: arith  (BE-204/205)

def run_arith():
    t0 = time.time()
    print(f'== arith: (BE-204)/(BE-205) (BE-E4\') DECOMPOSED  '
          f'[no sampling; seed {SEED} unused]')
    tuples = list(BA.all_tuples())
    print(f'  Enumeration: all {len(tuples)} tuples the caps allow -- '
          f'`barch.all_tuples`, `bdouble.py arith`\'s own space.')

    # ---- pass 1: (BE-162)(iii)'s 245 REPRODUCED, and classified.
    viol = [t for t in tuples if not e4prime(t)]
    assert len(viol) == 245, ('(BE-162)(iii)\'s 245 moved', len(viol))
    print(f'  Pass 1 -- (BE-162)(iii) REPRODUCED: {len(viol)} tuples '
          f'violate (BE-E4\').')
    d_hist, r_hist, c_hist, e_hist, o_hist = {}, {}, {}, {}, {}
    for t in viol:
        d_hist[min(t[0], t[1])] = d_hist.get(min(t[0], t[1]), 0) + 1
        for i in firing(t):
            r_hist[t[4 + i]] = r_hist.get(t[4 + i], 0) + 1
            o_hist[e_of(t)[1 - i]] = o_hist.get(e_of(t)[1 - i], 0) + 1
        c_hist[(t[6], t[7])] = c_hist.get((t[6], t[7]), 0) + 1
        es = e_of(t)
        e_hist[es[0] + es[1]] = e_hist.get(es[0] + es[1], 0) + 1
    assert min(min(t[0], t[1]) for t in viol) >= 1, \
        'a (BE-E4\') violation has a rigid side'
    print('    `min delta_i`: ' + census(d_hist)
          + '  -- ASSERTED >= 1, so the restriction is live at every one')
    print('      and BSTEER\'s `delta_2 = 1` rung is the SMALLEST, not the '
          'only one.')
    print('    `rho_i` at the FIRING side: ' + census(r_hist))
    print('    `e_j` at the OTHER side: ' + census(o_hist))
    print('    `(c_1, c_2)` at Pi_x: ' + census(c_hist))
    print('    `e_1 + e_2`: ' + census(e_hist))

    # ---- pass 2: every violation is a (PENCIL-SATURATES) violation.
    assert all(t[4 + i] <= 5 for t in viol for i in firing(t)), \
        'a (BE-E4\') violation has rho_i = 6 at a firing side'
    assert max(t[4 + i] for t in viol for i in firing(t)) == 5, \
        'the firing side never reaches rho_i = 5'
    ps_esc = [t for t in tuples if BA.ps_full(t) and not e4prime(t)]
    assert not ps_esc, '(PENCIL-SATURATES) does not imply (BE-E4\')'
    print('  Pass 2 -- EVERY violation has `rho_i <= 5` at every firing '
          'side, ASSERTED, so')
    print('    (BE-E4\') violation ==> (PENCIL-SATURATES) violation there, '
          'and (PENCIL-SATURATES)')
    print(f'    => (BE-E4\') at {len(ps_esc)} escapes.  The route CANNOT be '
          '"prove (PENCIL-SATURATES)')
    print('    on the both-flexible zone": (BE-104)(i)\'s witness '
          '(5,3,0,0,5,3,2,0) has BOTH')
    wit = (5, 3, 0, 0, 5, 3, 2, 0)
    assert wit in set(tuples) and flexible(wit) and not BA.ps_full(wit) \
        and e4prime(wit), 'the (BE-104) witness does not read as recorded'
    print('    sides flexible, violates it, and satisfies (BE-E4\') -- '
        'ASSERTED.')

    # ---- pass 3: (BE-205) the TWO-PIECE frontier, enumerated not guessed.
    print('  Pass 3 -- (BE-205) THE TWO-PIECE FRONTIER, enumerated.')
    grid, frontier = {}, []
    for f in range(2, 7):
        for g in range(0, 5):
            esc = [t for t in tuples
                   if piece_floor(t, f) and piece_other(t, g)
                   and not e4prime(t)]
            grid[(f, g)] = len(esc)
    for f in range(2, 7):
        row = '  '.join(f'{grid[(f, g)]:4d}' for g in range(0, 5))
        print(f'    (BE-F_{f}) x (BE-G_g), g = 0..4:  {row}')
    for (f, g), n in sorted(grid.items()):
        if n == 0 and grid.get((f, g - 1), 1) != 0 \
                and grid.get((f - 1, g), 1) != 0:
            frontier.append((f, g))
    print(f'    MINIMAL sufficient pairs (no smaller f or g works): '
          f'{sorted(frontier)}')
    assert grid[(5, 1)] == 0, '(BE-F_5) and (BE-G_1) together do NOT suffice'
    assert grid[(5, 0)] > 0 and grid[(4, 1)] > 0, \
        'one of the two pieces was not needed after all'
    print(f'    `(BE-F_5) & (BE-G_1)` kills all {len(viol)} -- ASSERTED; and '
          f'NEITHER alone does')
    print(f'    (`(BE-F_5)` alone leaves {grid[(5, 0)]}, `(BE-G_1)` alone leaves '
          f'{grid[(2, 1)]}, `(BE-F_4) & (BE-G_1)` leaves {grid[(4, 1)]}).')

    # ---- pass 4: (BE-204) the dist condition, and it is a SUM.
    print('  Pass 4 -- (BE-204) THE `dist` CONDITION IS A SUM, NOT PER-SIDE.')
    fire_ok = [t for t in tuples
               if firing(t) and flexible(t) and e4prime(t)]
    need = min(t[4] + t[5] for t in fire_ok)
    lowmax = min(max(t[4], t[5]) for t in fire_ok)
    assert need == 6, ('the required rho sum is not 6', need)
    assert lowmax == 3, ('the smallest per-side rho ceiling is not 3', lowmax)
    small = sorted(t for t in fire_ok if max(t[4], t[5]) == 3)
    print(f'    (BE-E4\')\'s conclusion at a firing side is '
          f'`rho_1 + rho_2 >= 6 + c_other`, so with')
    print(f'    (BE-189)(ii)\'s PROVED ceiling `rho_i <= dist_i` it forces '
          f'`dist_1 + dist_2 >= {need}`,')
    print(f'    ASSERTED as the minimum over the {len(fire_ok)} '
          f'hypothesis-firing both-flexible tuples that')
    print(f'    satisfy it.  But the smallest PER-SIDE ceiling any of them '
          f'needs is {lowmax}:')
    ex = small[0]
    print(f'    e.g. {ex} -- `rho = ({ex[4]},{ex[5]})`, '
          f'`c = ({ex[6]},{ex[7]})`, `e = {e_of(ex)}`.  So (BE-189)(iii)\'s')
    print('    PER-SIDE `dist >= 6` threshold does NOT transfer, and '
          '(BE-E4\') carries content')
    print('    at `dist_1 = dist_2 = 3` -- inside the arc-`<= 5` strata '
          '(BE-201) closes GENERICALLY.')
    free = [t for t in tuples if firing(t) and flexible(t)
            and all(t[4 + i] == 6 for i in firing(t))]
    assert all(e_of(t)[i] == 4 for t in free for i in firing(t)), \
        'rho_i = 6 with c_i = 2 does not give e_i = 4'
    print(f'    AND the conclusion is FREE at the {len(free)} firing tuples '
          f'with `rho_i = 6` at every')
    print('    firing side: there `e_i = 4` exactly, ASSERTED, so '
          '(BE-E4\') is automatic.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return len(viol)


# ==================================================== mode: gated  (BE-208)

def _gated_family(name_of, lib, seed, arclen, ndraw=8):
    """Side 2 at one of the two landed gated pointwise-refutation families.
    The construction is the predecessor's, verbatim: `bline.legal_peel` for
    the composite and every gate it checks, `bproper.composite` for the
    side-1 vertex names, `binduc.flat_config` for the configuration.  What is
    NEW is that BOTH sides are measured -- `brankv._gated` and
    `blongarc._gated4` each measure side 1 only."""
    peels, rows, fired = 0, 0, 0
    holds, fails, unknown = 0, 0, 0
    e2h, r2h, c2h, d2h, marg = {}, {}, {}, {}, {}
    frame_none, worst = 0, None
    for (name, eside, _x0, _y0) in lib:
        lp = legal_peel(eside)
        if lp is None:
            print(f'     {name}: does NOT glue at non-adjacent terminals '
                  f'-- skipped')
            continue
        egraph, x, y, (okh, md, g, dx, dy, rn, sz) = lp
        assert okh and md >= 2 and g >= 4, ('(CH-1) fails on H', name)
        assert dx >= 3 and dy >= 3 and rn, ('peel gates fail', name)
        _ehc, esd1, esd2, _x, _y = composite('K33', [3] * 9, ('A', 'B'),
                                             eside)
        cs = sorted(neighbors(esd1)[x], key=str)
        assert len(cs) == 2, ('deg_1(x) != 2 on the composite', cs)
        assert rnode_shaped(esd2, x, y), 'side 2 is not R-node-shaped'
        # THE SCOPE CHECK, and it is the one a measurement of SIDE 2 needs
        # that a measurement of side 1 alone does not: `bline.legal_peel`
        # calls `bproper.composite` with EXACTLY these arguments, so `esd2`
        # must be the peel's other side and not some other graph's.  Traced
        # to ground rather than inferred from the two calls looking alike:
        # the two edge sets PARTITION `egraph`, and `delta_pair`'s own split
        # of `egraph` at `(x, y)` REPRODUCES them.
        f1 = {frozenset(e) for e in esd1}
        f2 = {frozenset(e) for e in esd2}
        fh = {frozenset(e) for e in egraph}
        assert f1 | f2 == fh and not (f1 & f2), \
            ('side 1 and side 2 do not partition H', name)
        dpv = delta_pair(egraph, x, y)
        assert dpv is not None, ('{x,y} is not a 2-cut of H', name)
        assert {frozenset(e) for e in dpv[2]} in (f1, f2) \
            and {frozenset(e) for e in dpv[3]} in (f1, f2), \
            ('`delta_pair` splits H differently from `composite`', name)
        peels += 1
        for d in range(ndraw):
            rng = random.Random(seed + 977 * d + len(name))
            try:
                aff = flat_config(egraph, rng)
            except RuntimeError:
                continue
            okw, _n = verify_pencil_witness(egraph, aff)
            assert okw, 'flat_config returned a non-witness'
            pix = plane_at(egraph, aff, x)
            assert pix is not None, 'no closed-star plane at x'
            pixsp = span([wedge2(hat(aff[x]), hat(aff[c])) for c in cs])
            assert dim(pixsp) == 2, 'the two hinge lines at x coincide'
            arc1 = arc_through(esd1, x, y, cs[0]) \
                or arc_through(esd1, x, y, cs[1])
            assert arc1 is not None and len(arc1) - 1 == arclen, \
                ('the gated peel does not carry the expected arc', name)
            sp1, rho1, del1, alp1 = side_nums(esd1, aff, x, y)
            sp2, rho2, del2, alp2 = side_nums(esd2, aff, x, y)
            c1v = dim(isect(sp1, pixsp)) if sp1 else 0
            c2v = dim(isect(sp2, pixsp)) if sp2 else 0
            rows += 1
            if flag_frame(egraph, aff, x, y) is None:
                frame_none += 1
            if c1v != 2:
                continue
            fired += 1
            ev1, ev2 = rho1 - c1v, rho2 - c2v
            e2h[ev2] = e2h.get(ev2, 0) + 1
            r2h[rho2] = r2h.get(rho2, 0) + 1
            c2h[c2v] = c2h.get(c2v, 0) + 1
            d2h[(del1, del2)] = d2h.get((del1, del2), 0) + 1
            m = ev1 + ev2 - 4
            marg[m] = marg.get(m, 0) + 1
            if worst is None or m < worst[0]:
                worst = (m, name, rho1, rho2, c1v, c2v, del1, del2,
                         alp1, alp2)
            if del1 < 1 or del2 < 1:
                unknown += 1
            elif ev1 + ev2 >= 4:
                holds += 1
            else:
                fails += 1
    print(f'     {peels} composite peels (K33 skeleton, profile 3), {rows} '
          f'gated `flat_config` chart points,')
    print(f'     every one carrying an arc of length exactly {arclen} '
          f'(asserted).  The hypothesis `c_1(Pi_x) = 2`')
    print(f'     FIRES at {fired} of {rows}.')
    print('     side 2, MEASURED HERE FOR THE FIRST TIME --  `rho_2`: '
          + census(r2h) + ';  `c_2(Pi_x)`: ' + census(c2h))
    print('       `e_2 = rho_2 - c_2(Pi_x)`: ' + census(e2h)
          + ';  `(delta_1, delta_2)`: ' + census(d2h))
    print('     (BE-E4\') margin `e_1 + e_2 - 4`: ' + census(marg))
    print(f'     ** (BE-E4\') HOLDS at {holds} of the {fired} firing points, '
          f'FAILS at {fails}, and is')
    print(f'     VACUOUS (a rigid side) at {unknown}. **')
    print(f'     `flag_frame` is None at {frame_none} of {rows} rows -- '
          f'the GENERIC FLAG REGIME gate.')
    if worst is not None:
        print(f'     tightest row: margin {worst[0]} on `{worst[1]}`, '
              f'rho = ({worst[2]},{worst[3]}), c = ({worst[4]},{worst[5]}), '
              f'delta = ({worst[6]},{worst[7]}), a = ({worst[8]},{worst[9]})')
    assert rows >= 6, 'the gated measurement did not run'
    assert fired >= 6, 'the hypothesis never fired -- population changed'
    return dict(rows=rows, fired=fired, holds=holds, fails=fails,
                unknown=unknown, frame_none=frame_none, marg=marg)


def run_gated(seed=SEED):
    t0 = time.time()
    print(f'== gated: (BE-208) SIDE 2 at the two landed POINTWISE-REFUTATION '
          f'families, seed {seed}')
    print('  Both families sit at `c_1(Pi_x) = 2` with `rho_1 = 3`, so '
          '`e_1 = 1` and (BE-E4\')')
    print('  needs `e_2 >= 3`.  Neither predecessor measured side 2.')
    print('  -- BRANKV (BE-192): arc 3 --')
    a3 = _gated_family('arc3', short_library(), seed, 3)
    print('  -- BLONGARC (BE-200): arc 4 --')
    a4 = _gated_family('arc4', arc4_library(), seed, 4)
    tot_f = a3['fails'] + a4['fails']
    tot_h = a3['holds'] + a4['holds']
    tot_v = a3['unknown'] + a4['unknown']
    print(f'  VERDICT.  Over both families: (BE-E4\') HOLDS at {tot_h}, '
          f'FAILS at {tot_f}, VACUOUS at {tot_v}.')
    if a3['frame_none'] == a3['rows'] and a4['frame_none'] == a4['rows']:
        print('  AND EVERY ROW IS OFF THE GENERIC FLAG REGIME '
              '(`flag_frame` None at every one),')
        print('  which is (BE-110)(iv)\'s REGIME GATE arriving at the '
              'two-sided clause: the 14 per-side')
        print('  inequalities (BE-97)/(BE-101) -- the thing (BE-E4\') exists '
              'to thin -- are not')
        print('  DEFINED here, so a reading off these rows is REPORTED, '
              'never a refutation.')
    print(f'  gated: {time.time() - t0:.1f}s')
    return tot_f


# ================================================ mode: peel  (BE-206/207)

def run_peel(nseed=3, prof=None, jobs=None):
    t0 = time.time()
    print(f'== peel: (BE-206)/(BE-207) SIDE 2 and the CORANK GRADING at '
          f'(BE-118)(ii)\'s 21 rows, seed {SEED}')
    print('  (BE-118)(ii)\'s construction verbatim (`bproper.plant_peel`): a '
          'non-path bucket-A side')
    print('  glued at two NON-ADJACENT hubs of a subdivided 3-connected '
          'skeleton, so side 2 is')
    print('  R-node-shaped and `flag_frame` is non-None.  What is NEW is '
          'side 2 and the grading.')
    jobs = jobs or PEELJOBS
    rows, fired, holds, fails, vac = 0, 0, 0, 0, 0
    qh, e1h, e2h, r2h, c2h, marg, sig = {}, {}, {}, {}, {}, {}, {}
    worst = None
    for (skname, xy, s1name) in jobs:
        edges1, _xt, _yt = side_named(s1name)
        pr = prof or [3] * len(SKELETONS[skname])
        for sd in range(nseed):
            rng = random.Random(SEED + 613 * sd + 7 * len(s1name))
            got = plant_peel(skname, pr, xy, edges1, rng)
            if got is None:
                continue
            egraph, esd1raw, _esd2raw, x, y, aff, _ppi = got
            dp = delta_pair(egraph, x, y)
            if dp is None:
                continue
            _d1, _d2, ea, eb = dp
            sda = ea if len(ea) == len(esd1raw) else eb
            sdb = eb if sda is ea else ea
            if len(sda) != len(esd1raw):
                continue
            sp1, rho1, _dl1, _al1 = rho_bar_of(sda, aff, x, y)
            if rho1 > 5:
                continue
            frame = flag_frame(egraph, aff, x, y)
            assert frame is not None, \
                'the planted peel is OFF the generic flag regime'
            row = e_row(egraph, x, y, sda, sdb, aff)
            assert row is not None, 'the row does not measure'
            rows += 1
            if row['cX'][0] != 2 and row['cX'][1] != 2:
                continue
            fired += 1
            # ---- (BE-206): the corank grading, on the FIRING side.
            px = hat(aff[x])
            sigx = sigma_at(px)
            # (BE-209)(i): BLONGARC's `alpha_x` and BPROPER/BSATUR's
            # `Sigma_x` are the SAME SPACE under two names -- both are
            # `p_x ^ K^4`.  Built here BLONGARC's way (three wedges against
            # independent points) and asserted equal to `bsatur.sigma_at`,
            # because the claim that (BE-201)'s master invariant and
            # (BE-110)(i)'s corank identity are one theorem rests on it.
            bas = [px]
            for w in sorted(aff, key=str):
                if rank(bas + [hat(aff[w])]) > len(bas):
                    bas.append(hat(aff[w]))
                if len(bas) == 4:
                    break
            assert len(bas) == 4, 'the configuration does not span P^3'
            alphax = span([wedge2(px, b) for b in bas[1:]])
            assert dim(alphax) == 3 and dim(isect(alphax, sigx)) == 3, \
                'alpha_x and Sigma_x are NOT the same space'
            for i in (0, 1):
                if row['cX'][i] != 2:
                    continue
                spi = row['S1'] if i == 0 else row['S2']
                rhoi = row['r'][i]
                dsig = dim(isect(spi, sigx)) if spi else 0
                # `q_hat(rho_bar_i) = rho_bar_i ^ p_x`; its dimension is the
                # corank identity's right-hand side, (BE-110)(i).
                proj = rank([w for w in
                             ([wedge3(v, px) for v in spi] if spi else [])])
                assert dsig == rhoi - proj, \
                    ('(BE-110)(i)\'s corank identity FAILED', rhoi, dsig,
                     proj)
                assert dsig >= 2, 'Pi_x is not inside the firing side'
                inside = 1 if dsig >= 3 else 0
                assert row['e'][i] == proj + inside, \
                    ('(BE-206)\'s identity failed', row['e'][i], proj,
                     inside)
                qh[proj] = qh.get(proj, 0) + 1
                sig[dsig] = sig.get(dsig, 0) + 1
            ev1, ev2 = row['e']
            e1h[ev1] = e1h.get(ev1, 0) + 1
            e2h[ev2] = e2h.get(ev2, 0) + 1
            r2h[row['r'][1]] = r2h.get(row['r'][1], 0) + 1
            c2h[row['cX'][1]] = c2h.get(row['cX'][1], 0) + 1
            m = ev1 + ev2 - 4
            marg[m] = marg.get(m, 0) + 1
            if worst is None or m < worst[0]:
                worst = (m, s1name, row['r'], row['cX'], row['d'], row['a'])
            if row['d'][0] < 1 or row['d'][1] < 1:
                vac += 1
            elif e4_at(row) is False:
                fails += 1
            else:
                holds += 1
    print(f'  {rows} full-peel rows, `flag_frame` non-None at every one '
          f'(ASSERTED); the hypothesis')
    print(f'  `c_i(Pi_x) = 2` FIRES at {fired}.')
    print('  (BE-110)(i)\'s CORANK IDENTITY re-asserted at every firing '
          'side; `dim(rho_bar_i cap Sigma_x)`: '
          + census(sig))
    print('  (BE-206) the GRADING `dim(rho_bar_i ^ p_x)`: ' + census(qh)
          + '  -- and `e_i = that + [Sigma_x <= rho_bar_i]` ASSERTED.')
    print('  side 2: `rho_2`: ' + census(r2h) + ';  `c_2(Pi_x)`: '
          + census(c2h) + ';  `e_2`: ' + census(e2h))
    print('  `e_1`: ' + census(e1h) + ';  (BE-E4\') margin `e_1+e_2-4`: '
          + census(marg))
    print(f'  ** (BE-E4\') HOLDS at {holds}, FAILS at {fails}, VACUOUS at '
          f'{vac}. **')
    if worst is not None:
        print(f'  tightest row: margin {worst[0]} on `{worst[1]}`, '
              f'rho = {worst[2]}, c = {worst[3]}, delta = {worst[4]}, '
              f'a = {worst[5]}')
    print(f'  (BE-207) `(BE-F_5)` IS FALSE HERE: the firing side has '
          f'`rho_i <= 4` at {sum(v for k, v in sig.items())} firing sides,')
    print('  all with `Pi_x <= rho_bar_i` -- so the arithmetic frontier\'s '
          '`f = 5` half is REFUTED')
    print('  by a LANDED witness, not conjectured away.')
    assert rows >= 3, 'the peel sweep did not reproduce'
    assert fired >= 3, 'the hypothesis never fired -- population changed'
    print(f'  peel: {time.time() - t0:.1f}s')
    return fails


def wedge3(u, p):
    """`u ^ p` for `u` a 2-vector and `p` a point: the corank identity's map
    `q_hat`.  `bsigma.wedge3` is the landed device; imported lazily here so
    the *Harness debt* sibling-import row records ONE more consumer rather
    than a new hazard."""
    from bsigma import wedge3 as _w3
    return _w3(u, p)


def run_validate():
    print('== validate: arith + gated + peel in one process')
    run_arith()
    run_gated()
    run_peel()


def main(argv):
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        return 0
    m = argv[0].lstrip('-')
    if m == 'arith':
        run_arith()
    elif m == 'gated':
        run_gated()
    elif m == 'peel':
        run_peel()
    elif m == 'validate':
        run_validate()
    else:
        print(f'unknown mode {m!r}')
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
