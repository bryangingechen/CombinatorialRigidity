"""
Direction BFOUR (arc ordinal 81) -- (BE-154)(iv): DOES A PEEL EXIST WITH
`c_i(Pi_x) = 2` AND `e_1 + e_2 <= 3`?  I.e. is the two-sided clause (E4)
FALSE?

  THE QUESTION, verbatim from (BE-154)(iii)/(iv).  BARCH proposed

      (E4)   c_i(Pi_x) = 2  =>  e_1 + e_2 >= 4,
             e_i := rho_i - c_i(Pi_x),

  as the two-sided substitute for (PENCIL-SATURATES-CHART) that delivers
  14 -> 12, priced it UNPROVED, and named the cheapest decisive move: a
  FALSIFICATION.  Its own criterion for the falsifier, quoted: "That needs
  `rho_i <= 5` AND `rho_j <= c_j(Pi_x) + (5 - rho_i)`, so on BSATUR's own
  `rho_i = 5` witness it needs `rho_bar_j <= Pi_x` outright, i.e.
  `rho_j <= 2`.  If that configuration exists, (E4) dies and the bar should
  come back down for the whole clause family."

  THE ANSWER, said at the top, and it is SIX results.

  (BE-156) THE CONTAINMENT THEOREM -- the hunt is a STRICT SUB-HUNT.
           `c_i(Pi_x) = 2` IS `Pi_x <= rho_bar_i`, and `e_i = rho_i - 2`
           there, so `e_1 + e_2 <= 3` forces `rho_i <= 5`.  Hence EVERY
           (E4) falsifier is a (PENCIL-SATURATES-CHART) counterexample:
           535 of 535 by exhaustion over the 6 400 tuples.  385 of the 535
           are ALSO [MARGIN] shortfalls; only 150 are clean.

  (BE-157) AND THE POPULATION (BE-154)(iv) NAMES CANNOT DECIDE IT.  At
           every one of the composite chart points `bdegtwo.sweep_points`
           produces -- all four fibre shapes, all three skeletons, every
           legal hub pair -- side 2's signature is CONSTANT,
           `(delta_2, a_2, rho_2, c_2(Pi_x)) = (3, 0, 3, 0)`, so `e_2 = 3`
           IDENTICALLY and (E4) collapses to the ONE-sided sentence
           `c_1(Pi_x) = 2 => rho_1 >= 3`.  Exactly 3 of the 535 falsifying
           tuples are reachable, all demanding `rho_bar_1 = Pi_x` at
           `rho_1 = 2` -- a STRICT special case of the clause condition
           the same sweep already returned 0/772 on ((BE-140)).

  (BE-158) WHAT THE POPULATIONS REACH -- and `Gamma_Pi` is an (E4) PROVER.
           `dim Gamma_Pi(p) <= 1` bounds `c_1(Pi_x)` from above, so
           wherever (BE-151)'s certificate fires it PROVES (E4) at that
           point.  Measured on the composite chart points, which is the
           population (BE-151) explicitly does not reach.

  (BE-159) THE GENERATOR AUDIT (the RPOOL sharpening).  `sweep_points` has
           THREE side-2 axes: `skname` and `xy` are PARAMETERS and were
           never moved (defaults `'K33'`, `('A','B')`); `pr = [3]*n` is
           HARDCODED.  Moving the first two changes nothing.  Moving the
           third changes everything.

  (BE-160) (E4) IS FALSE.  `K4(5,2,2,2,2,2)` peeled at ('A','B'), side 1
           the 5-branch, REFLAGGED to BSATUR's bad plane:

               (delta, a, rho, c(Pi_x)) = (5,0 | 0,0 | 5,0 | 2,0),
               e = (3, 0),   e_1 + e_2 = 3  <  4.

           `verify_pencil_witness` TRUE, girth 6, `hcard` TRUE,
           `rnode_shaped(side2)` TRUE, x and y hubs, y not adjacent x,
           margins at Pi_x/Pi_y/<M> all <= 0 so NOT a shortfall,
           `a_1 = a_2 = 0` so the ATTAINING case, and the F13 control
           clean (c = 1 at the sampler's own plane).  Exact Q, 7/7
           draws; 15 more rows at delta_2 = 0 over three skeletons in
           `repair`.

  (BE-161) AND THE REFUTATION IS CONFINED TO (BE-22)(vi)'s COLLAPSE.  The
           `pr` ladder, at all three skeletons: `delta_2 = 0/1/2/3` gives
           `e_2 = 0/1/2/3` and `e_1 + e_2 = 3/4/5/6`.  (E4) fails at
           `delta_2 = 0` and holds TIGHTLY at `delta_2 = 1`.  A rigid side
           is exactly where (BE-22)(vi) -- PROVEN -- collapses the 2-cut
           criterion to `rho_1 = delta_1` with NO general-position content,
           so the 14 inequalities (E4) serves are vacuous there.

  (BE-162) THE REPAIR, AND ITS EXACT PRICE.  (E4') := (E4) restricted to
           `delta_1, delta_2 >= 1` leaves 158 escapes of 6 400 -- and ALL
           158 have `min(delta_1, delta_2) = 0`, i.e. every one is
           discharged by (BE-22)(vi) rather than by the clause.  So 14 ->
           12 survives on the both-flexible zone.  (E4') is UNPROVED, and
           it is TIGHT at `delta_2 = 1` (`e_1 + e_2 = 4` exactly), so it is
           refutable by ONE further mechanism: `rho_bar_2 <= Pi_x` at
           `delta_2 = 1`.

  MODES.  arith | chart | charta | chartb | gen | wit | repair |
          support | validate  (the last runs all six in one process)
  `--chart` is the commissioned 411-target population and measures ~780 s,
  which does NOT fit a 600 s foreground budget: run it as the two halves
  `--charta` then `--chartb` (~430 s each), the YLOC / GGLOB precedent in
  `notes/scripts/README.md` section 0.  `--validate` runs `chart` at a
  70-point sample instead, and says so in its own output.
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.  Caps DISCLOSED per mode (RESEARCH-ARC section 5): every negative
  below is "not found under cap C", never "does not exist".

  READ-ONLY WITH RESPECT TO EVERY LANDED DRIVER.  `barch.py` and
  `bdegtwo.py` are IMPORTED, not edited; no tracked driver is modified, so
  the "figures do not move" gate discharges by
  `git diff --name-only -- '*.py' '*.m2'` plus
  `git status --porcelain notes/scripts/` (`notes/scripts/README.md`
  *Harness debt*, "No tracked driver modified").

  THREE RECORDED HARNESS HAZARDS, all navigated rather than fixed
  (`notes/scripts/README.md` *Harness debt*):
    * `bimage.pt_in` truncates a `Lambda^2`-side input to `K^4` with NO
      assert -- it is not called here at all.  The only calls in the import
      closure are `sweep_points`' own, on the width-4 `p_x` fibre, which is
      what it is FOR;
    * `bimage.span`'s width-6 special case fires on RANK, not width, so it
      returns `I6` on a width-12 input of rank 6 -- no width-12 object goes
      through `span`/`dim`/`isect` here.  The one 12-wide measurement is
      inside `barch.gamma_cut`, which routes it through `exactcore.rank`;
    * `bwin.dehom` returns a LIST, defeating `assert_generic_star`'s edge
      check -- `bwin` is not imported.
"""

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import itertools                                                      # noqa: E402
import random                                                         # noqa: E402

from exactcore import hat, neighbors, wedge2                          # noqa: E402
from bimage import (contains, dim, isect, pencil_space, plane_at,      # noqa: E402
                    rho_bar_of, same_space, span)
from bpeel import SKELETONS, delta_pair, rnode_shaped                 # noqa: E402
from bdecor import d3, girth, hcard_ok_piece, weld_d3                  # noqa: E402
from bunif import SEED                                                 # noqa: E402
from bsatur import bad_plane, draw_peel, reflag, row_of                # noqa: E402
from bproper import core_of, free_peel                                 # noqa: E402
from bopen import sides_of                                            # noqa: E402
from kbare_common import verify_pencil_witness, verts_of               # noqa: E402

import barch as BA                                                    # noqa: E402
import bdegtwo as BD                                                  # noqa: E402

PIX, PIY, MB = ('Pix',), ('Piy',), ('M',)


# `bsatur.peel_of` and `bdegtwo.peel_of` are same-named-but-DIFFERENT (a
# *Divergences* pair: different signatures, different side orientation).
# Both are used below, each reached under its own name, never interchanged.
def _bs_peel(skname, prof, ei):
    """`bsatur.peel_of` reached through its own module, so the name cannot be
    confused with `bdegtwo.peel_of` (a *Divergences* pair: same job, different
    signature and side orientation)."""
    import bsatur
    return bsatur.peel_of(skname, list(prof), ei)


# ===================================================== the lean per-point row

def side_nums(side, aff, x, y):
    """`(rho_bar_i, rho_i, delta_i, a_i)` for one side, from the canonical
    primitives only -- `bimage.rho_bar_of` for the space and its `dim M`,
    `bdecor.d3`/`weld_d3` for the two combinatorial numbers.

    This is `bsatur.row_of`'s per-side arithmetic WITHOUT its 16-block
    `profile` call, which costs ~16 subspace intersections a row and is what
    makes `row_of` cost seconds.  `chart` below cross-asserts this against
    `row_of` itself at the first swept point of every peel, so the two cannot
    silently diverge."""
    S, rho, dM, _r = rho_bar_of(side, aff, x, y)
    f = d3(side)
    return S, rho, f - weld_d3(side, x, y), dM - 6 - f


def e_row(E, x, y, s1, s2, aff):
    """The (E4) datum at one configuration: the tuple `bdouble`/`barch`'s
    arithmetic speaks in, plus `c_i` at BOTH pencil blocks and `e_i` at
    `Pi_x`.  Returns None off the generic flag regime (no plane at x or y)."""
    Bx, By = plane_at(E, aff, x), plane_at(E, aff, y)
    if Bx is None or By is None:
        return None
    Pix = pencil_space(hat(aff[x]), Bx)
    Piy = pencil_space(hat(aff[y]), By)
    if dim(Pix) != 2 or dim(Piy) != 2:
        return None
    S1, r1, d1, a1 = side_nums(s1, aff, x, y)
    S2, r2, d2, a2 = side_nums(s2, aff, x, y)
    cX = (dim(isect(S1, Pix)) if S1 else 0, dim(isect(S2, Pix)) if S2 else 0)
    cY = (dim(isect(S1, Piy)) if S1 else 0, dim(isect(S2, Piy)) if S2 else 0)
    MBk = span([wedge2(hat(aff[x]), hat(aff[y]))])
    cM = (dim(isect(S1, MBk)) if S1 else 0, dim(isect(S2, MBk)) if S2 else 0)
    return dict(t=(d1, d2, a1, a2, r1, r2, cX[0], cX[1]),
                cX=cX, cY=cY, cM=cM, r=(r1, r2), d=(d1, d2), a=(a1, a2),
                e=(r1 - cX[0], r2 - cX[1]),
                eY=(r1 - cY[0], r2 - cY[1]),
                slack=max(0, d1 + d2 - 6), S1=S1, S2=S2, Pix=Pix, Piy=Piy)


def e4_at(row, blk='X'):
    """(E4) evaluated at a measured row, at `Pi_x` (`blk='X'`) or `Pi_y`."""
    c = row['cX'] if blk == 'X' else row['cY']
    e = row['e'] if blk == 'X' else row['eY']
    if 2 not in c:
        return None                     # hypothesis not met: no content here
    return e[0] + e[1] >= 4


# ============================================== mode: arith  ((BE-156))

def _clause_bad(t):
    """(PENCIL-SATURATES-CHART) violated at a tuple: `Pi_x <= rho_bar_i`
    (i.e. `c_i(Pi_x) = 2`) with `rho_i <= 5`."""
    _d1, _d2, _a1, _a2, r1, r2, c1, c2 = t
    return (c1 == 2 and r1 <= 5) or (c2 == 2 and r2 <= 5)


def _margin(t):
    d1, d2, _a1, _a2, _r1, _r2, c1, c2 = t
    return c1 + c2 - 2 - BA.slack_of(d1, d2)


def run_arith():
    t0 = time.time()
    print(f'== arith: (BE-156) THE CONTAINMENT THEOREM, seed {SEED}')
    print('  (BE-154)(iv) prices the hunt as "the cheapest decisive move".')
    print('  The first thing to establish is what its search space IS.')
    print('  `c_i(Pi_x) = 2` and dim Pi_x = 2 give `Pi_x <= rho_bar_i`, so')
    print('  `e_i = rho_i - 2` there, and `e_1 + e_2 <= 3` with `e_j >= 0`')
    print('  forces `rho_i <= 5`.  That is EXACTLY the clause condition.')
    T = list(BA.all_tuples())
    assert len(T) == 6400, ('the tuple space moved', len(T))
    bad = [t for t in T if not BA.e4(t)]
    cb = [t for t in bad if _clause_bad(t)]
    assert len(cb) == len(bad), 'a falsifier that is NOT a clause violation'
    print(f'  {len(T)} tuples; (E4)-violating {len(bad)}; of those,')
    print(f'  (PENCIL-SATURATES-CHART)-violating {len(cb)} -- ASSERTED at')
    print(f'  {len(cb)}/{len(bad)}.  So the (E4) falsification hunt is a')
    print('  STRICT SUB-HUNT of the clause-violation hunt.')
    mh = {}
    for t in bad:
        mh[_margin(t)] = mh.get(_margin(t), 0) + 1
    clean = sum(1 for t in bad if _margin(t) <= 0)
    print(f'  margin at Pi_x over the {len(bad)}: {dict(sorted(mh.items()))}')
    print(f'  -- so {len(bad) - clean} of {len(bad)} are ALSO [MARGIN]')
    print('  SHORTFALLS (Phase39 item 0(b), never exhibited); only')
    print(f'  {clean} are clean (E4) falsifiers.')
    att = sum(1 for t in bad if t[2] == 0 and t[3] == 0)
    print(f'  attaining (a_1 = a_2 = 0), where S-mark\'s pin carries: {att}')
    print('  Reachability of the (BE-154)(iv) population, computed here and')
    print('  MEASURED in `chart` below: side 2 fixed at')
    print('  (delta_2, a_2, rho_2, c_2) = (3, 0, 3, 0).')
    sig = [t for t in bad
           if (t[1], t[3], t[5], t[7]) == (3, 0, 3, 0)]
    print(f'  falsifying tuples with that side-2 signature: {len(sig)}')
    for t in sorted(sig):
        print(f'    (d,a,rho,c) = ({t[0]},{t[1]} | {t[2]},{t[3]} | '
              f'{t[4]},{t[5]} | {t[6]},{t[7]})   e = '
              f'({t[4]-t[6]},{t[5]-t[7]})')
    assert len(sig) == 3, ('the reachable falsifier count moved', len(sig))
    assert all(t[4] == 2 and t[6] == 2 for t in sig), \
        'a reachable falsifier that does not force rho_bar_1 = Pi_x'
    print('  ALL THREE force `rho_1 = c_1(Pi_x) = 2`, i.e.')
    print('  `rho_bar_1 = Pi_x` EXACTLY -- a clause violation at rho_1 = 2,')
    print('  which is STRICTLY inside what (BE-140) swept at 0/772.')
    # BARCH's own four figures, reproduced as the divergence guard.
    sep = sum(1 for t in T if BA.e4(t) and not BA.ps_full(t)
              and BA.violates(t[6], t[7], 2, t[0], t[1]))
    assert sep == 970, ('(BE-153)(ii)\'s 970 moved', sep)
    assert len(BA.escapes(BA.e4)) == 0, '(BE-153)(i)\'s 0 moved'
    assert len(BA.escapes(BA.ps_full)) == 0, '(BE-101)(i)\'s 0 moved'
    assert len(BA.escapes(BA.pair_patch)) == 287, '(BE-153)(iv)\'s 287 moved'
    print('  BARCH cross-check REPRODUCED: 970 separating, escapes 0 / 0,')
    print('  pair-patch 287.')
    print('  VERDICT.  The hunt cannot be cheaper than the clause hunt it')
    print('  sits inside: every falsifier is a clause counterexample, 72%')
    print('  of the falsifier space would additionally be the arc\'s FIRST')
    print('  shortfall, and the chart population reaches 3 of 535.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return len(bad), len(sig)


# ============================================== mode: chart  ((BE-157)/(BE-158))

def run_chart(nseed=2, ntarget=6, half=None, floor=60):
    t0 = time.time()
    print(f'== chart: (BE-157)/(BE-158) THE COMMISSIONED SWEEP -- BOTH SIDES '
          f'AT THE COMPOSITE CHART POINTS, seed {SEED}')
    print('  (BE-154)(iv), verbatim: extend the `cert` sweep to composite')
    print('  chart points and evaluate `dim Gamma_Pi(p)` and `(e_1, e_2)` at')
    print('  BOTH sides of the peel.  `barch.run_cert` measures ONE side of')
    print('  a bare side configuration; `bdegtwo.run_direct` measures side 1')
    print('  of the composite.  Neither has ever measured side 2.')
    JOBS = BD.all_jobs()
    if half is not None:
        cut = len(JOBS) // 2
        JOBS = JOBS[:cut] if half == 'a' else JOBS[cut:]
    print(f'  population: nseed {nseed}, ntarget {ntarget}, side-1 jobs '
          f'{len(JOBS)} of {len(BD.all_jobs())}'
          + (f' (half {half})' if half else ''))
    tot, peels, kinds = 0, 0, {}
    ecen, ccen, cycen, sig2 = {}, {}, {}, {}
    gcen, gfire, gid, gid_ok, gbound = {}, 0, 0, 0, 0
    e4x, e4y, e4hyp, fals = 0, 0, 0, []
    xcheck = 0
    seen = set()
    for job in JOBS:
        for row in BD.sweep_points(job, nseed, ntarget):
            (name, aff, aff2, kind, cs, s1, s2, E, x, y,
             _fib, _nh, _dW, pkey) = row
            r = e_row(E, x, y, s1, s2, aff2)
            if r is None:
                continue
            tot += 1
            if pkey not in seen:
                seen.add(pkey)
                peels += 1
                kinds[kind] = kinds.get(kind, 0) + 1
                # THE DIVERGENCE GUARD: the lean row against `row_of` itself,
                # once per peel (row_of costs seconds a row -- disclosed).
                rr = row_of(E, x, y, s1, s2, aff2)
                if rr is not None:
                    assert (rr['r1'], rr['r2']) == r['r'], 'rho disagrees'
                    assert (rr['d1'], rr['d2']) == r['d'], 'delta disagrees'
                    assert (rr['a1'], rr['a2']) == r['a'], 'a disagrees'
                    assert (rr['c1'][PIX], rr['c2'][PIX]) == r['cX'], \
                        'c(Pi_x) disagrees with row_of'
                    assert (rr['c1'][PIY], rr['c2'][PIY]) == r['cY'], \
                        'c(Pi_y) disagrees with row_of'
                    assert rr['slack'] == r['slack'], 'slack disagrees'
                    for b, du in ((PIX, 2), (PIY, 2), (MB, 1)):
                        m = rr['c1'][b] + rr['c2'][b] - du - rr['slack']
                        assert m <= 0, ('SHORTFALL: margin > 0', name, b, m)
                    xcheck += 1
            ecen[r['e']] = ecen.get(r['e'], 0) + 1
            ccen[r['cX']] = ccen.get(r['cX'], 0) + 1
            cycen[r['cY']] = cycen.get(r['cY'], 0) + 1
            k2 = (r['d'][1], r['a'][1], r['r'][1], r['cX'][1])
            sig2[k2] = sig2.get(k2, 0) + 1
            # ---- (E4) at BOTH blocks, at BOTH sides
            for blk, ctr in (('X', 'x'), ('Y', 'y')):
                v = e4_at(r, blk)
                if v is None:
                    continue
                e4hyp += 1
                if blk == 'X':
                    e4x += 1
                else:
                    e4y += 1
                if not v:
                    fals.append((name, blk, r['t'], r['e']))
            # ---- the graph certificate, and its (BE-149) identity
            core = core_of(s1, x)
            gd = BA.graph_data(core, aff2, cs[0], cs[1], y)
            px = hat(aff2[x])
            l1 = wedge2(px, hat(aff2[cs[0]]))
            l2 = wedge2(px, hat(aff2[cs[1]]))
            if dim(span([l1, l2])) != 2:
                continue
            dGP, PHI = BA.gamma_cut(gd, l1, l2)
            gcen[dGP] = gcen.get(dGP, 0) + 1
            gfire += int(dGP <= 1)
            # the bound holds at EVERY k: N_full <= r^{-1}(Pi_x).
            assert r['cX'][0] <= dGP, \
                ('c_1(Pi_x) exceeds dim Gamma_Pi', name, r['cX'][0], dGP)
            gbound += 1
            if len(cs) == 2:
                gid += 1
                if same_space(PHI, isect(r['S1'], r['Pix'])) or (
                        dim(PHI) == 0 and dim(isect(r['S1'], r['Pix'])) == 0):
                    gid_ok += 1
                else:
                    raise AssertionError(
                        ('(BE-149)(i) FAILS on the composite', name,
                         dim(PHI), dim(isect(r['S1'], r['Pix']))))
    print(f'  {tot} swept composite chart points over {peels} peels;')
    print('  fibre kinds: ' + ', '.join(f'{k}: {v}'
                                        for k, v in sorted(kinds.items())))
    print(f'  `row_of` cross-check (the lean row against the canonical one,')
    print(f'  plus the three margin controls) at {xcheck} of {peels} peels.')
    print('  SIDE 2\'s SIGNATURE (delta_2, a_2, rho_2, c_2(Pi_x)): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(sig2.items())))
    assert len(sig2) == 1 and (3, 0, 3, 0) in sig2, \
        ('side 2 is NOT constant on this population', sig2)
    print('  -- ONE value.  So `e_2 = 3` IDENTICALLY and (E4) degenerates')
    print('  to the ONE-sided `c_1(Pi_x) = 2 => rho_1 >= 3` here.')
    print(f'  (e_1, e_2) census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(ecen.items())))
    print(f'  (c_1, c_2) at Pi_x: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(ccen.items())))
    print(f'  (c_1, c_2) at Pi_y: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cycen.items())))
    print(f'  (E4)\'s HYPOTHESIS is met at {e4hyp} block-instances '
          f'({e4x} at Pi_x, {e4y} at Pi_y) -- so the sweep is NOT vacuous.')
    print(f'  (E4) FALSIFIERS FOUND: {len(fals)}')
    for f in fals[:8]:
        print(f'    {f}')
    print('  dim Gamma_Pi census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(gcen.items())))
    print(f'  `dim Gamma_Pi <= 1` fires at {gfire} of {gbound} points, and')
    print('  where it fires it PROVES (E4): it bounds `c_1(Pi_x) <= 1`, so')
    print('  (E4)\'s hypothesis cannot hold at side 1 there.  The bound')
    print(f'  `c_1(Pi_x) <= dim Gamma_Pi` is ASSERTED at {gbound}/{gbound},')
    print(f'  at EVERY k; the exact (BE-149)(i) identity at {gid_ok}/{gid}')
    print('  of the k = 2 points -- (BE-149)\'s 99 bare-side rows extended')
    print('  to the COMPOSITE chart population for the first time.')
    assert tot >= floor, ('the chart sweep did not run', tot, floor)
    assert e4hyp >= 1, '(E4)\'s hypothesis was never met -- sweep vacuous'
    assert gid_ok == gid and gid >= 1, '(BE-149)(i) did not reproduce'
    print(f'  VERDICT (cap disclosure, RESEARCH-ARC section 5).  (E4) is')
    print(f'  NOT FALSIFIED at any of {tot} composite chart points -- "not')
    print(f'  found under this cap", never "cannot happen".  And the cap is')
    print('  the point: side 2 is CONSTANT here, so this population can')
    print('  only reach 3 of (BE-156)\'s 535 falsifying tuples, each of')
    print('  which demands `rho_bar_1 = Pi_x` at `rho_1 = 2` -- STRICTLY')
    print('  inside the clause condition the same sweep returned 0/772 on.')
    print('  (BE-154)(iv)\'s population therefore CANNOT decide (E4).')
    print(f'  chart: {time.time() - t0:.1f}s')
    return tot, len(fals), gfire


# ============================================== mode: gen  ((BE-159))

def run_gen(nseed=1, ntarget=1):
    t0 = time.time()
    print(f'== gen: (BE-159) THE GENERATOR AUDIT -- THREE SIDE-2 AXES, seed '
          f'{SEED}')
    print('  RESEARCH-ARC section 4, the RPOOL sharpening: enumerate the')
    print('  generator\'s parameters and say which ones the evidence varied.')
    print('  `bdegtwo.sweep_points(job, nseed, ntarget, skname, xy)` exposes')
    print('  TWO side-2 axes and HARDCODES a third (`pr = [3]*n`, in both')
    print('  `peel_of` and `sweep_points`).  All three are moved here.')
    job = BD.all_jobs()[2]
    print(f'  side-1 job held fixed at: {job[0]}')
    print()
    print('  AXIS 1+2 -- `skname` x `xy`, both PARAMETERS, both never moved')
    print('  (defaults \'K33\', (\'A\',\'B\')).  Every legal combination:')
    sigs, nc = {}, 0
    for skn in ('K4', 'prism', 'K33'):
        hubs = sorted({v for e in SKELETONS[skn] for v in e})
        for xy in itertools.combinations(hubs, 2):
            if BD.peel_of(job[1], skn, xy) is None:
                continue
            for row in BD.sweep_points(job, nseed, ntarget, skn, xy):
                (_n, _a, aff2, _k, _cs, s1, s2, E, x, y, *_z) = row
                r = e_row(E, x, y, s1, s2, aff2)
                if r is None:
                    continue
                nc += 1
                k2 = (r['d'][1], r['a'][1], r['r'][1], r['cX'][1])
                sigs.setdefault(k2, []).append((skn, xy))
    print(f'    {nc} realized (skeleton, hub-pair) chart points;')
    for k in sorted(sigs):
        v = sigs[k]
        print(f'    (delta_2,a_2,rho_2,c_2) = {k} at {len(v)} of them, '
              f'skeletons {sorted({s for (s, _p) in v})}')
    assert len(sigs) == 1, ('skname x xy DOES move side 2', sigs)
    real = sorted({s for v in sigs.values() for (s, _p) in v})
    print(f'    ONE signature, over every skeleton that realizes at all')
    print(f'    ({real}) and every legal hub pair inside it.  DISCLOSED: of')
    print(f'    the three skeletons, {sorted(set(("K4", "prism", "K33")) - set(real))}')
    print('    realize NO peel for this side-1 job (`peel_of` returns None --')
    print('    the k >= 2 side does not glue at two non-adjacent hubs there),')
    print('    so the axis is exercised at the skeletons above, not all 3.')
    print('    MOVING THESE TWO AXES CHANGES NOTHING.')
    print()
    print('  AXIS 3 -- `pr`, HARDCODED at `[3]*n`.  Reached here through')
    print('  `bproper.free_peel(skname, prof, xy, side1, rng)`, the same')
    print('  canonical generator `sweep_points` itself calls, with `prof`')
    print('  moved.  DISCLOSED: this leg draws the sampler\'s own `p_x` and')
    print('  does NOT sweep the fibre -- it moves `pr` and nothing else.')
    skn, xy = 'K33', ('A', 'B')
    n = len(SKELETONS[skn])
    lad = {}
    for m in (1, 2, 3, 4, 5, 6):
        prof = [m] * n
        hit = None
        for sd in range(6):
            rng = random.Random(SEED + 613 * sd + 7 * len(job[0]) + 41 * m)
            g = free_peel(skn, prof, xy, job[1], rng)
            if g is None:
                continue
            E, E1, _E2, x, y, aff = g
            ss = sides_of(E, E1, x, y)
            if ss is None or y in neighbors(E)[x]:
                continue
            r = e_row(E, x, y, ss[0], ss[1], aff)
            if r is None:
                continue
            hit = (r['d'][1], r['a'][1], r['r'][1], r['cX'][1], r['e'][1])
            break
        lad[m] = hit
        print(f'    pr = [{m}]*{n}: (delta_2,a_2,rho_2,c_2,e_2) = {hit}')
    got = [v for v in lad.values() if v is not None]
    assert len({v[4] for v in got}) >= 3, \
        'the pr axis did not move e_2 -- the audit has no content'
    print(f'    e_2 takes {len({v[4] for v in got})} distinct values on this')
    print('    axis alone, INCLUDING 0 at `pr = [2]*n` -- and `e_2 = 0` is')
    print('    exactly what (BE-154)(iii)\'s falsifier criterion needs.')
    print('  VERDICT.  Of the three side-2 axes the generator has, the two')
    print('  that are PARAMETERS are inert and the one that is HARDCODED is')
    print('  the whole question.  (BE-151)\'s and (BE-140)\'s populations')
    print('  both hold it fixed, which is why neither could see (BE-160).')
    print(f'  gen: {time.time() - t0:.1f}s')
    return nc, lad


# ============================================== mode: wit  ((BE-160))

# The falsifier, NAMED so the mode does not depend on a scan.  It is
# BSATUR's own witness generator with ONE parameter moved: side-2 branch
# length 3 -> 2 ((BE-104)'s `K4(5,3,3,3,3,3)` becomes `K4(5,2,2,2,2,2)`).
FAL_SKEL, FAL_PROF, FAL_EDGE = 'K4', (5, 2, 2, 2, 2, 2), 0
BSA_SKEL, BSA_PROF, BSA_EDGE = 'K4', (5, 3, 3, 3, 3, 3), 0


def gates_of(E, x, y, side1, side2):
    """Every (CH-1)/peel legality gate the clause's own regime asserts, as a
    dict, so the witness is disclosed gate by gate rather than in prose."""
    nb = neighbors(E)
    okh, _W, _b, _h = hcard_ok_piece(E, x, y)
    dp = delta_pair(E, x, y)
    return dict(
        nV=len(verts_of(E)), nE=len(E), girth=girth(E),
        mindeg=min(len(nb[w]) for w in verts_of(E)),
        degx=len(nb[x]), degy=len(nb[y]), adj=(y in nb[x]),
        hcard=okh, is2cut=(dp is not None),
        rnode1=rnode_shaped(side1, x, y), rnode2=rnode_shaped(side2, x, y),
        deg1x=len(neighbors(side1)[x]), deg2x=len(neighbors(side2)[x]))


def witness_rows(skname, prof, ei, nseed=10, tag=''):
    """Draw the peel, reflag onto (BE-105)'s bad plane, and measure BOTH
    sides.  Yields (row, gates, aff, aff2, extras) for every draw that gets
    through -- including the F13 negative control at the sampler's own
    plane, which is what makes the row evidence rather than an artefact."""
    got = _bs_peel(skname, prof, ei)
    if got is None:
        return
    E, x, y, side1, side2 = got
    if len(neighbors(side1)[x]) != 1:
        return
    c1v = sorted(neighbors(side1)[x], key=str)[0]
    gates = gates_of(E, x, y, side1, side2)
    for sd in range(nseed):
        rng = random.Random(SEED + 1013 * sd + 17 * len(prof) + sum(prof))
        d = draw_peel(E, x, y, rng)
        if d is None:
            continue
        P, B, pts, aff, branches = d
        S1, r1, _dM, _ = rho_bar_of(side1, aff, x, y)
        px, pc1 = hat(aff[x]), hat(aff[c1v])
        if not contains(S1, [wedge2(px, pc1)]):
            continue                     # (M1) fails at this draw
        try:
            badB = bad_plane(S1, px, pc1)
        except AssertionError:
            continue
        if badB is None:
            continue
        # --- F13 NEGATIVE CONTROL, `bsatur.run_witness`'s own: the SAMPLER's
        # --- plane must not already be bad, and must not BE the bad plane.
        pa0 = plane_at(E, aff, x)
        if pa0 is None:
            continue
        c0 = dim(isect(S1, pencil_space(px, pa0)))
        if c0 >= 2 or same_space(pa0, badB):
            continue
        aff2 = reflag(E, x, side1, P, B, pts, badB, branches, rng)
        if aff2 is None:
            continue
        ok, _n = verify_pencil_witness(E, aff2)
        if not ok:
            continue
        r = e_row(E, x, y, side1, side2, aff2)
        if r is None:
            continue
        yield (r, gates, dict(c0=c0, r1=r1, sd=sd,
                              moved=[w for w in verts_of(side1)
                                     if aff2[w] != aff[w]],
                              tag=tag or f'{skname}{tuple(prof)}'))


def run_wit(nseed=10):
    t0 = time.time()
    print(f'== wit: (BE-160) (E4) IS FALSE -- THE WITNESS, seed {SEED}')
    print('  (BE-153)(iii) reads BSATUR\'s refuting peel ASSERTED at its own')
    print('  recorded numbers and finds `e = (3,3)`, so (E4) holds there.')
    print('  Step one: MEASURE that geometrically rather than read it.')
    print('  Step two: move the ONE generator parameter (BE-153)(iii)\'s')
    print('  reasoning depends on -- side 2 -- and measure again.')
    print()
    print(f'  (a) BSATUR\'s own witness {BSA_SKEL}{BSA_PROF}, reflagged:')
    nb_, base = 0, None
    for (r, g, ex) in witness_rows(BSA_SKEL, BSA_PROF, BSA_EDGE, nseed):
        nb_ += 1
        base = (r, g, ex)
        if nb_ == 1:
            print(f'      gates {g}')
        assert ex['moved'] == [], 'the reflag moved side 1'
        assert r['r'][0] == 5 and r['cX'][0] == 2, \
            ('the witness is not (BE-104)\'s corner', r['t'])
        assert e4_at(r, 'X') is True, '(E4) fails at BSATUR\'s witness'
    assert nb_ >= 3, ('BSATUR\'s witness did not reproduce', nb_)
    r0 = base[0]
    print(f'      (delta,a,rho,c(Pi_x)) = ({r0["d"][0]},{r0["d"][1]} | '
          f'{r0["a"][0]},{r0["a"][1]} | {r0["r"][0]},{r0["r"][1]} | '
          f'{r0["cX"][0]},{r0["cX"][1]}),  e = {r0["e"]},  '
          f'e_1+e_2 = {sum(r0["e"])}')
    print(f'      MEASURED at {nb_}/{nb_} draws, F13 control c = '
          f'{base[2]["c0"]} < 2 at the sampler\'s own plane.')
    print('      (BE-153)(iii) UPGRADED from ASSERTED-at-its-own-numbers to')
    print('      MEASURED: (E4) does hold at BSATUR\'s witness, and the')
    print('      reason is `rho_2 = 3` -- a fact about SIDE 2, which no')
    print('      per-side refutation and no landed sweep ever moved.')
    print()
    print(f'  (b) THE SAME GENERATOR, ONE PARAMETER ALONG: '
          f'{FAL_SKEL}{FAL_PROF}.')
    nf, fal = 0, None
    for (r, g, ex) in witness_rows(FAL_SKEL, FAL_PROF, FAL_EDGE, nseed):
        if nf == 0:
            print(f'      gates {g}')
            assert g['girth'] >= 4 and g['mindeg'] >= 2, '(CH-1) fails'
            assert g['hcard'] and g['is2cut'], 'hcard or the 2-cut fails'
            assert g['degx'] >= 3 and g['degy'] >= 3, 'a terminal is no hub'
            assert not g['adj'], 'x and y are adjacent'
            assert g['rnode2'], 'side 2 is not R-node-shaped'
            assert g['deg1x'] == 1, 'side 1 is not a series end'
        nf += 1
        fal = (r, g, ex)
        assert ex['moved'] == [], 'the reflag moved side 1'
        assert contains(r['S1'], r['Pix']), 'Pi_x is not inside rho_bar_1'
        assert e4_at(r, 'X') is False, '(E4) HOLDS here -- no falsifier'
    assert nf >= 3, ('the falsifier did not reproduce', nf)
    r1, g1, ex1 = fal
    for b, du, cc in (('Pi_x', 2, r1['cX']), ('Pi_y', 2, r1['cY']),
                      ('<M>', 1, r1['cM'])):
        m = cc[0] + cc[1] - du - r1['slack']
        assert m <= 0, ('the witness is a SHORTFALL at ' + b, m)
    print(f'      (delta,a,rho,c(Pi_x)) = ({r1["d"][0]},{r1["d"][1]} | '
          f'{r1["a"][0]},{r1["a"][1]} | {r1["r"][0]},{r1["r"][1]} | '
          f'{r1["cX"][0]},{r1["cX"][1]}),  e = {r1["e"]},  '
          f'e_1+e_2 = {sum(r1["e"])}  <  4')
    print(f'      margins: Pi_x '
          f'{r1["cX"][0]+r1["cX"][1]-2-r1["slack"]}, Pi_y '
          f'{r1["cY"][0]+r1["cY"][1]-2-r1["slack"]}, <M> '
          f'{r1["cM"][0]+r1["cM"][1]-1-r1["slack"]}  -- all <= 0, so this')
    print('      is NOT a [MARGIN] shortfall; item 0(b) stays unexhibited.')
    print(f'      a_1 = a_2 = 0: {r1["a"] == (0, 0)} -- the ATTAINING case.')
    both = (r1['S1'] + r1['S2']) if r1['S2'] else r1['S1']
    quot = dim(both + r1['Pix']) - 2
    assert quot < 4, ('(E4)\'s "equivalently" reading HOLDS here', quot)
    assert quot == sum(r1['e']) or quot <= sum(r1['e']), \
        'the quotient exceeds e_1 + e_2'
    print(f'      reach dim(rho_bar_1 + rho_bar_2) = {dim(both)}, so')
    print('      the quotient `(rho_bar_1+rho_bar_2+Pi_x)/Pi_x` has')
    print(f'      dimension {quot} < 4: (E4)\'s OWN "equivalently"')
    print('      reading -- the two sides together fill Lambda^2K^4/Pi_x --')
    print('      fails as well, not only its arithmetic form.')
    print(f'      REPRODUCED at {nf}/{nf} draws, exact Q, F13 control')
    print(f'      c = {ex1["c0"]} < 2.')
    print('  And (BE-154)(iii)\'s own falsifier criterion is met VERBATIM:')
    print(f'  `rho_i <= 5` ({r1["r"][0]} <= 5) and, at that `rho_i = 5`,')
    print(f'  `rho_bar_j <= Pi_x` outright with `rho_j <= 2` '
          f'({r1["r"][1]} <= 2).')
    print('  VERDICT.  (E4) AS STATED IS REFUTED.  This is a BAR-LIFT')
    print('  REVERSAL: (BE-154)(iii) lifted strategy section 8\'s bar for')
    print('  (E4) as "the cheaper of the two", and (E4) is now dead as a')
    print('  clause, so the bar comes back down over it.  What it does NOT')
    print('  reverse is the lift for `Gamma`-properness ((BE-149)(v)),')
    print('  which this refutation does not touch.')
    print(f'  wit: {time.time() - t0:.1f}s')
    return nb_, nf, r1['t']


# ============================================== mode: repair  ((BE-161)/(BE-162))

LADDER = [
    ('K4', (5, 2, 2, 2, 2, 2), 0), ('K4', (5, 2, 2, 3, 3, 3), 0),
    ('K4', (5, 2, 3, 3, 3, 3), 0), ('K4', (5, 3, 3, 3, 3, 3), 0),
    ('prism', (5, 2, 2, 2, 2, 2, 2, 2, 2), 0),
    ('prism', (5, 2, 2, 2, 2, 2, 3, 3, 3), 0),
    ('prism', (5, 2, 2, 2, 2, 3, 3, 3, 3), 0),
    ('prism', (5, 3, 3, 3, 3, 3, 3, 3, 3), 0),
    ('K33', (5, 2, 2, 2, 2, 2, 2, 2, 2), 0),
    ('K33', (5, 2, 2, 2, 2, 2, 3, 3, 3), 0),
    ('K33', (5, 2, 2, 2, 2, 3, 3, 3, 3), 0),
    ('K33', (5, 2, 2, 2, 3, 3, 3, 3, 3), 0),
]


def e4_prime(t):
    """(E4') -- (E4) restricted to the both-flexible zone `delta_i >= 1`,
    i.e. off (BE-22)(vi)'s collapse."""
    if t[0] == 0 or t[1] == 0:
        return True
    return BA.e4(t)


def run_repair(nseed=8):
    t0 = time.time()
    print(f'== repair: (BE-161)/(BE-162) WHERE THE REFUTATION LIVES, AND '
          f'THE REPAIR, seed {SEED}')
    print('  The witness has `delta_2 = 0`.  (BE-22)(vi) -- PROVEN -- says')
    print('  that when one side is rigid the 2-cut criterion collapses to')
    print('  `rho_1 = delta_1` with NO general-position content, so the 14')
    print('  per-side inequalities (E4) exists to thin are VACUOUS there.')
    print('  So: walk `delta_2` up and see where (E4) starts holding.')
    lad, rows = {}, 0
    for (skn, prof, ei) in LADDER:
        best = None
        n = 0
        for (r, g, _ex) in witness_rows(skn, prof, ei, nseed):
            n += 1
            rows += 1
            v = e4_at(r, 'X')
            key = (r['d'][1], r['r'][1], r['cX'][1], r['e'][1], sum(r['e']))
            best = (key, v, g['rnode2'])
            assert r['cX'][0] == 2, 'the reflag did not make side 1 bad'
        if best is None:
            print(f'    {skn}{prof}: no row drawn')
            continue
        key, v, rn2 = best
        lad.setdefault(key[0], []).append((skn, prof, key, v))
        print(f'    {skn}{prof}: delta_2={key[0]} rho_2={key[1]} '
              f'c_2(Pi_x)={key[2]} e_2={key[3]} e_1+e_2={key[4]} '
              f'rnode2={rn2}  (E4) '
              f'{"FAILS" if v is False else "holds"}  [{n} draws]')
    print()
    print('  THE LADDER, by delta_2:')
    for d2 in sorted(lad):
        vs = lad[d2]
        e2s = sorted({k[3] for (_s, _p, k, _v) in vs})
        sums = sorted({k[4] for (_s, _p, k, _v) in vs})
        verd = sorted({str(v) for (_s, _p, _k, v) in vs})
        print(f'    delta_2 = {d2}: e_2 in {e2s}, e_1+e_2 in {sums}, '
              f'(E4) {verd} over {len(vs)} skeleton(s)')
    assert 0 in lad and all(v is False for (_s, _p, _k, v) in lad[0]), \
        '(E4) did not fail at delta_2 = 0'
    for d2 in sorted(k for k in lad if k >= 1):
        assert all(v is True for (_s, _p, _k, v) in lad[d2]), \
            ('(E4) FAILS at delta_2 >= 1 -- report as the HEADLINE', d2)
    tight = [k for (_s, _p, k, _v) in lad.get(1, []) if k[4] == 4]
    print(f'  At delta_2 = 1 the sum is EXACTLY 4 at {len(tight)} of '
          f'{len(lad.get(1, []))} -- (E4) is TIGHT at its own boundary.')
    print()
    print('  (E4\') -- (E4) plus `delta_1, delta_2 >= 1`.  The arithmetic:')
    T = list(BA.all_tuples())
    esc = BA.escapes(e4_prime)
    coll = [t for t in esc if min(t[0], t[1]) == 0]
    print(f'    escapes {len(esc)} of {len(T)}  [(E4) gives 0]')
    print(f'    of those, with min(delta_1, delta_2) = 0: {len(coll)}')
    assert len(coll) == len(esc), \
        'an (E4\') escape OUTSIDE (BE-22)(vi)\'s collapse'
    print('    ASSERTED at {0}/{0} -- EVERY escape (E4\') admits sits in'
          .format(len(esc)))
    print('    the regime (BE-22)(vi) discharges by a PROVED theorem, not')
    print('    by the clause.  So 14 -> 12 survives on the both-flexible')
    print('    zone, with the rigid-side remainder carried by (BE-22)(vi).')
    sep = sum(1 for t in T if e4_prime(t) and not BA.ps_full(t)
              and BA.violates(t[6], t[7], 2, t[0], t[1]))
    piv = sum(1 for t in T if e4_prime(t) and t[2] == 0 and t[3] == 0
              and BA.violates(t[6], t[7], 2, t[0], t[1]))
    print(f'    strictly weaker than (PENCIL-SATURATES): {sep} separating')
    print(f'    tuples (BARCH measured 970 for (E4)); Pi_x violations at')
    print(f'    a_1 = a_2 = 0 under (E4\'): {piv}')
    assert piv == 0, '(BE-101)(ii)\'s corollary FAILS under (E4\')'
    assert sep > 970, 'the repair is not strictly weaker than the clause'
    viol = [t for t in T if not e4_prime(t)]
    print(f'    (E4\')-violating tuples still in the space: {len(viol)}, '
          f'delta_2 down to {min(t[1] for t in viol)}')
    print(f'  VERDICT (cap disclosure).  (E4) fails at delta_2 = 0 at '
          f'{len(lad[0])} skeleton(s) and holds at every')
    print(f'  delta_2 >= 1 point drawn here ({rows} rows total) -- NOT')
    print('  FOUND under this cap, never "cannot happen".  The repair')
    print('  (E4\') is UNPROVED and, being TIGHT at delta_2 = 1, is')
    print('  refutable by ONE further mechanism: `rho_bar_2 <= Pi_x` at')
    print('  `delta_2 = 1`, where rho_bar_2 is a single line and Pi_x is')
    print('  already pinned to (BE-105)\'s bad plane.  THAT is the')
    print('  successor, and it is cheaper than this direction was.')
    print(f'  repair: {time.time() - t0:.1f}s')
    return len(esc), len(coll), rows


# ========================================================= mode: support

def run_support():
    print('== support: the RESEARCH-ARC section 4 support audit')
    print('  Every population named, with what it VARIES, what it HOLDS')
    print('  FIXED, and which quantifier of its own claim it reaches.')
    print('  BSATUR\'s sharpening binds (an in-driver assert is only as')
    print('  strong as its distribution) and so does RPOOL\'s (name the')
    print('  generator parameters the evidence moved).')
    rows = [
        ('arith / (BE-156)',
         'ALL 6 400 tuples of `barch.all_tuples()` -- EXHAUSTIVE, no sampler',
         'nothing; it is an enumeration',
         'the arithmetic quantifier fully. It reaches NO geometry: a tuple '
         'being allowed by the caps is not a tuple being realized'),
        ('chart / (BE-157)',
         '`bdegtwo.sweep_points` over `all_jobs()`: 30 side-1 shapes, 2 '
         'seeds, 6 fibre targets, all FOUR fibre kinds, `p_x` swept inside '
         'its own fibre with the core byte-fixed',
         'side 2 ENTIRELY -- `skname=K33`, `xy=(A,B)`, `pr=[3]*9`. Measured '
         'consequence: `(delta_2,a_2,rho_2,c_2) = (3,0,3,0)` at 100% of '
         'points',
         'ONLY the side-1 half of a TWO-sided clause. (E4) is quantified '
         'over the PAIR; this population has one point in the side-2 '
         'factor, so 3 of 535 falsifying tuples are reachable and every one '
         'of the 3 is a strict special case of a condition already swept '
         'at 0/772'),
        ('gen / (BE-159)',
         '`skname` (3 skeletons) x `xy` (every legal hub pair) x `pr` '
         '([m]*n for m = 1..6, through `bproper.free_peel`)',
         'side 1 (one job), and the fibre sweep on the `pr` leg -- that leg '
         'draws the sampler\'s own `p_x`',
         'the generator-parameter question exactly: which axes move `e_2`. '
         'It does NOT re-run the fibre sweep at a moved `pr`, which is the '
         'named residue'),
        ('wit / (BE-160)',
         'the flag at x, ADVERSARIALLY -- `bsatur.bad_plane` constructs the '
         'plane that makes `Pi_x <= rho_bar_1`, and `reflag` re-places side '
         '2 into it. 10 configuration seeds per peel',
         'the two peels are NAMED, not sampled',
         'the EXISTENTIAL sentence "a peel exists with c_i = 2 and '
         'e_1+e_2 <= 3" -- which is all a falsification needs. One exact-Q '
         'witness through every gate settles it'),
        ('repair / (BE-161)',
         '`delta_2` through 0/1/2/3 by moving `pr`, at three skeletons, with '
         'the flag adversarial at every rung',
         '`delta_1 = 5` (side 1 is the 5-branch), and `c_2(Pi_x)` is left to '
         'the sampler rather than steered',
         'the LOCATION of the refutation, not (E4\')\'s truth. The residue '
         'is exactly the unsteered coordinate: `c_2(Pi_x) = 1` at '
         '`delta_2 = 1` would refute (E4\') and no draw here targets it'),
    ]
    for (nm, var, fix, reach) in rows:
        print(f'  --- {nm}')
        print(f'      VARIES : {var}')
        print(f'      FIXED  : {fix}')
        print(f'      REACHES: {reach}')
    print('  THE ONE SENTENCE THIS AUDIT EXISTS FOR.  `bdegtwo.run_direct`')
    print('  asserts the clause unviolated at 0/772 and `barch.run_cert`')
    print('  asserts both certificates sound at 663 firings; BOTH are true')
    print('  statements about every draw those runs made, and BOTH hold')
    print('  side 2 at a single point of its parameter space.  The')
    print('  refutation of (E4) sits one step along that axis -- `pr` from')
    print('  3 to 2 -- exactly the shape RPOOL\'s sharpening predicts.')
    return len(rows)


def run_validate():
    a = run_arith()
    print()
    # DISCLOSED: `--validate` runs `chart` at the FITTING sample (nseed 1,
    # ntarget 2 -> ~70 points, ~200 s).  The commissioned 411-target
    # population at (2, 6) measures ~780 s and does NOT fit a 600 s
    # foreground budget, so it is run as TWO foreground invocations,
    # `--charta` then `--chartb` -- the YLOC / GGLOB precedent in
    # `notes/scripts/README.md` section 0, not a waiver.
    c = run_chart(1, 2, floor=60)
    print()
    g = run_gen()
    print()
    w = run_wit()
    print()
    r = run_repair()
    print()
    s = run_support()
    print()
    print(f'== validate: arith {a}, chart {c}, gen {g[0]}, wit {w[:2]}, '
          f'repair {r}, support {s}')


def main(argv):
    modes = [a for a in argv[1:] if a.startswith('--')]
    if not modes or '--validate' in modes:
        run_validate()
        return
    for m in modes:
        {'--arith': run_arith,
         '--chart': lambda: run_chart(2, 6, None, 380),
         '--charta': lambda: run_chart(2, 6, 'a', 150),
         '--chartb': lambda: run_chart(2, 6, 'b', 150),
         '--gen': run_gen, '--wit': run_wit, '--repair': run_repair,
         '--support': run_support}[m]()
        print()


if __name__ == '__main__':
    main(sys.argv)
