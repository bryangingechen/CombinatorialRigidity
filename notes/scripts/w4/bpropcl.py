"""
Direction BPROPCL (Phase 39 PENCIL, section (K-bare-ext)) -- IS `U <= rho_bar_i`
A PROPER CLOSED CONDITION at `rho_i <= 5` once the path confinement has gone
vacuous?  That is the residue (BE-259)(ii) leaves at `Pi_x` (`dim <P_0> in
{5,6}`) and the residue (BE-277)(iii) leaves at `<M>` (`dim <P_0> = 6`), and
both landed clauses assert the two are ONE question.

  THE ANSWER, said at the top, in three parts.

  (1) THE RESIDUE IS NOT A LEMMA -- IT IS A ONE-DRAW CERTIFICATE, and the
      certificate is already available from the corpus's own semicontinuity
      ledger.  `rho_i` is LOWER semicontinuous ((BE-255)(i) row 2) and
      bounded above by the COMBINATORIAL constant `delta_i` ((BE-22)(ii) at
      `a_i = 0`).  So `{rho_i = delta_i}` is OPEN, and nonempty exactly when
      one draw attains it -- whereupon it is DENSE (`Chart(H)` irreducible,
      (BE-65)(ii)).  On that dense open `c_i(U) = dim(rho_bar_i cap U)` is
      UPPER semicontinuous ((BE-255)(i) row 4), so its generic value is its
      MINIMUM there.  Hence:

        ONE draw `q` with `a_i(q) = 0`, `rho_i(q) = delta_i <= 5` and
        `c_i(U)(q) < dim U` PROVES that `U <= rho_bar_i` is a proper closed
        condition on `Chart(H)`.

      The `a_i = 0` clause is what makes the cap `rho_i <= delta_i` hold on a
      NEIGHBOURHOOD rather than at the point: `a_i` is UPPER semicontinuous
      ((BE-255)(i) row 3), so one draw with `a_i = 0` proves `a_i = 0`
      generically, and only then is `{rho_i = delta_i}` open.  All three
      clauses are semicontinuous in the direction that makes ONE draw a
      theorem, and rows 2, 3 and 4 of the ledger are used TOGETHER, which the
      corpus has not done.  A witness, not a search: no cap attaches to it.
      Reported by mode `gp`.

  (2) THE TWO RESIDUES ARE NOT THE SAME QUESTION, and the mechanism both
      clauses name -- "`rho_bar_i` in general position against a stable
      block" -- is FALSE at `Pi_x` and unviolated at `<M>` on the very
      population the clauses cite.  `Pi_x = p_x ^ pi_x` is spanned by side
      `i`'s OWN hinge lines at `x` (`bimage.plane_at` builds `pi_x` from the
      CLOSED STAR of `x`, so every hinge at `x` lies in `Pi_x`), while `<M>`
      is the hinge line of an edge that is ABSENT from both sides and sits
      in the direct complement of both pencils (`bunif.blocks_of`'s own
      direct-sum assert).  So `Pi_x` has a structural mechanism forcing
      `c_i(Pi_x) >= 1` and `<M>` has none.  This mode is `gp`.

  (3) THE RESIDUE CORNER'S ARITHMETIC HAS NEVER BEEN PRICED.
      `bmblock.run_reach` COMPUTES the joint `((delta_1, delta_2),
      (dist_1, dist_2))` distribution and PRINTS only the `dist` marginal --
      the same dropped-field shape (BE-273)(iii) found at `cM`.  Printed
      here for the first time, draw-free, over the same committed job list.
      This mode is `pop`.

  MODES
    pop    draw-free.  The residue corner (`dist_i >= 6` on BOTH sides) of
           `bgoodempty.run_block`'s committed job list, with its `(delta_1,
           delta_2)` profile and the per-block arithmetic gate a bite would
           need.  No configuration is sampled anywhere.
    gp     the GENERAL-POSITION test, per draw, on the side library: the
           joint `(dist, rho, c(U))` distribution that `run_pix` and
           `bmblock.run_side` compute and never print, the count of draws at
           which `c(U) != bunif.generic_c(rho, dim U)`, and the HINGE test
           that names the mechanism of every excess at `Pi_x`.
           `gp` also carries the one-draw properness CERTIFICATE of (1):
           rows at which `rho = delta <= 5` and `c(U) < dim U` at a draw,
           hence rows at which properness is PROVED rather than measured.
    validate  pop + a reduced gp.

  NOTATION, stated ONCE.  `V := Lambda^2 K^4`; `Pi_x := p_x ^ pi_x` (dim 2),
  `<M> := <p_x ^ p_y>` (dim 1); `c_i(U) := dim(rho_bar_i cap U)`;
  `U <= rho_bar_i` iff `c_i(U) = dim U`.  `generic_c(r, du) = max(0, r + du
  - 6)` is `bunif.generic_c`, the general-position value.  RUNG 3 is
  `Sigma_delta <= 6`.

  CAPS ARE DISCLOSED IN-MODE and travel with every figure.  A capped search
  reports NOT FOUND UNDER CAP C, never "does not exist".  A one-draw
  CERTIFICATE is not a search and carries no cap -- said separately each
  time, because the two kinds of figure appear side by side here.
"""

import os
import sys
import time
import random

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import wedge2, hat, rank as rank_exact        # noqa: E402
from bimage import dim, span, isect, rho_bar_of, plane_at    # noqa: E402
from bdecor import sample_by_branches, d3                    # noqa: E402
import bunif                                                 # noqa: E402
import bproper                                               # noqa: E402
import bgoodempty as BG                                      # noqa: E402
import bmblock as BM                                         # noqa: E402

SEED = 20260912
RUNG3 = 6
PIXDIM, MDIM = 2, 1


# ------------------------------------------------------------------ helpers

def _hinges_at(E, pt, v):
    """The hinge lines of the SIDE at `v`: `p_v ^ p_z` for every side
    neighbour `z`.  Every one of them lies in `Pi_v` because `pi_v` is the
    plane of the CLOSED STAR (`bimage.plane_at`)."""
    pv = hat(pt[v])
    return [wedge2(pv, hat(pt[z])) for z in sorted(BG.neighbors(E).get(v, ()),
                                                   key=str)]


def _in_span(w, basis):
    """Is the vector `w` inside the span of `basis`?"""
    if not basis:
        return False
    return rank_exact(list(basis) + [w]) == rank_exact(list(basis))


# ================================================================ mode: pop

def run_pop(seed=SEED, maxlen=5):
    """THE RESIDUE CORNER, PRICED DRAW-FREE -- and the field
    `bmblock.run_reach` computes and drops.

    `run_reach` builds `dd_delta[((d1,d2),(t1,t2))]` and prints only the
    `(t1,t2)` marginal.  `delta_i` is COMBINATORIAL (`bgoodempty.delta_of` =
    `d3 - weld_d3`), so the joint needs no configuration either.  It decides
    something the `dist` marginal cannot: whether a residue-corner peel can
    carry a `Pi_x` or `<M>` bite AT ALL.

      * a `Pi_x` bite needs `c_1 + c_2 >= 3` with `c_i <= min(rho_i, 2) <=
        min(delta_i, 2)`, i.e. `min(d1,2) + min(d2,2) >= 3`;
      * an `<M>` bite needs `c_1 = c_2 = 1`, i.e. `d1 >= 1` AND `d2 >= 1`.

    Either gate FAILING on a peel closes that peel with NO properness lemma
    and no draw.  CAP: `bgoodempty.run_block`'s committed job list, replayed
    through `bmblock._jobs(seed, maxlen)` -- every job, no `njob`, no
    `quick`."""
    t0 = time.time()
    print(f'== pop: the residue corner priced DRAW-FREE, seed {seed}')
    print('   CAP: `bmblock._jobs()` = `bgoodempty.run_block`\'s committed '
          'job list, every job.')
    jobs = BM._jobs(seed, maxlen)
    rows = 0
    dh, joint, corner = {}, {}, {}
    pixgate = mgate = 0
    cpix_open = cm_open = 0
    for (skname, prof, xy, s1name, s1E) in jobs:
        x, y = xy
        try:
            E, E1, E2, x, y = bproper.composite(skname, list(prof), xy, s1E)
        except Exception:
            continue
        if len({frozenset(e) for e in E}) != len(E):
            continue
        nbH = BG.neighbors(E)
        if y in nbH.get(x, ()):
            continue
        if len(nbH.get(x, ())) < 3 or len(nbH.get(y, ())) < 3:
            continue
        if min(len(v) for v in nbH.values()) < 2 or BG.girth(E) < 4:
            continue
        if not BG.hcard_ok_piece(E, x, y):
            continue
        if not BG.rnode_shaped(E2, x, y):
            continue
        if len(BG.neighbors(E1).get(x, ())) < 2 or \
           len(BG.neighbors(E2).get(x, ())) < 2:
            continue
        if len(BG.neighbors(E1).get(y, ())) < 2 or \
           len(BG.neighbors(E2).get(y, ())) < 2:
            continue
        d1, d2 = BG.delta_of(E1, x, y), BG.delta_of(E2, x, y)
        if d1 + d2 > RUNG3:
            continue
        t1, t2 = BG.dist_of(E1, x, y), BG.dist_of(E2, x, y)
        rows += 1
        assert min(t1, t2) >= 2, ('an in-region peel with dist = 1', t1, t2)
        assert d1 <= t1 and d2 <= t2, \
            ('(BE-256)(ii) `delta <= dist` FAILS in-region', d1, t1, d2, t2)
        dh[(t1, t2)] = dh.get((t1, t2), 0) + 1
        joint[((d1, d2), (t1, t2))] = joint.get(((d1, d2), (t1, t2)), 0) + 1
        if min(t1, t2) >= 6:
            corner[(d1, d2)] = corner.get((d1, d2), 0) + 1
            # the two arithmetic gates, at the SIDE-degree cap `delta`
            gp = min(d1, PIXDIM) + min(d2, PIXDIM) >= PIXDIM + 1
            gm = d1 >= 1 and d2 >= 1
            pixgate += 1 if gp else 0
            mgate += 1 if gm else 0
            # and the RESIDUE gate proper: the properness lemma is needed
            # only where the block can reach `dim U` on a side at `rho <= 5`
            if gp and (min(d1, PIXDIM) == PIXDIM or min(d2, PIXDIM) == PIXDIM):
                cpix_open += 1
            if gm:
                cm_open += 1
    both6 = sum(corner.values())
    print(f'  in-region peels {rows}  (jobs offered {len(jobs)}) -- NO '
          f'configuration was drawn')
    print(f'  `(dist_1, dist_2)` -> count: {dict(sorted(dh.items()))}')
    print(f'  residue corner (`dist_i >= 6` on BOTH sides): {both6}')
    print(f'  ITS `(delta_1, delta_2)` PROFILE -- the field `run_reach` '
          f'computes and drops:')
    print(f'     {dict(sorted(corner.items()))}')
    print(f'  of those {both6}: `Pi_x` arithmetic gate '
          f'`min(d1,2)+min(d2,2) >= 3` passes at {pixgate}')
    print(f'                     `<M>`  arithmetic gate `d1 >= 1 and '
          f'd2 >= 1` passes at {mgate}')
    print(f'  peels where the PROPERNESS residue is therefore LIVE: '
          f'Pi_x {cpix_open}, <M> {cm_open}')
    if pixgate == 0 and mgate == 0:
        print('  BOTH gates are EMPTY on the corner: on this population the '
              'residue is')
        print('  VACUOUS and neither landed clause needs the properness '
              'lemma at all.')
    print(f'  full `((delta_1,delta_2),(dist_1,dist_2))` joint, all '
          f'{rows} peels:')
    print(f'     {dict(sorted(joint.items()))}')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, corner, (pixgate, mgate)


# ================================================================= mode: gp

def _lib(seed, maxarc, maxtheta):
    lib = list(BG.side_library(maxarc, maxtheta, 40, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in BG.side1_library()]
    return lib


def _rows(lib, ndraw, seed):
    """Per-DRAW rows on the side library, at `run_pix`'s own seed ladder so
    the rows are the SAME rows (BE-258)(iii)/(BE-273)(i) report.  Yields
    (tag, E, x, y, delta, dist, rho, Pix, Mspc, S, pt)."""
    for (tag, E, x, y) in lib:
        d = BG.delta_of(E, x, y)
        dd = BG.dist_of(E, x, y)
        paths, _tr = BG.xy_paths(E, x, y, cap=400, maxlen=9)
        short = [P for P in paths if len(P) == dd]
        if not short:
            continue
        for s in range(ndraw):
            rng = random.Random(seed + 733 * s + len(E))
            got = sample_by_branches(E, x, y, rng)
            if got is None:
                continue
            pt = got[0] if isinstance(got, tuple) else got
            try:
                S, rho, dM, _r = rho_bar_of(E, pt, x, y)
            except AssertionError:
                continue
            Bx = plane_at(E, pt, x)
            if Bx is None:
                continue
            px, py = hat(pt[x]), hat(pt[y])
            Pix = span([wedge2(px, b) for b in Bx])
            if dim(Pix) != PIXDIM:
                continue
            if rank_exact([px, py]) != 2:
                continue
            Mspc = span([wedge2(px, py)])
            # `a_i = dim M_i - 6 - f_i` with `f_i = d3(side)` -- the same
            # arithmetic `bproper.run_proper` uses (`a1 = dM - 6 - f1`).
            # `a_i` is UPPER semicontinuous ((BE-255)(i) row 3), so `a_i = 0`
            # at a draw PROVES `a_i = 0` generically -- which is what makes
            # the pointwise cap `rho_i <= delta_i` hold on a NEIGHBOURHOOD
            # and hence `{rho_i = delta_i}` open.  Without it the certificate
            # of (BE-293) has no cap to attain.
            a = dM - 6 - d3(E)
            assert a >= 0, ('a_i went negative -- the oracle disagrees', tag)
            yield (tag, E, x, y, d, dd, rho, Pix, Mspc, S, pt, short[0], a)


def run_gp(ndraw=3, seed=SEED, maxarc=8, maxtheta=7):
    """THE GENERAL-POSITION TEST, PER DRAW -- the mechanism both residue
    clauses name, tested rather than inherited.

    `bgoodempty.run_pix` and `bmblock.run_side` both compute `rho` and
    `c(U)` at every draw and print only the `(dist, c)` marginal, so the
    joint `(dist, rho, c)` -- which is what "general position" is a
    statement about -- has never been reported.  Here it is, per draw, with
    the general-position residual `c(U) - generic_c(rho, dim U)`.

    Also: the HINGE test.  `pi_x` is the plane of the CLOSED STAR of `x`
    (`bimage.plane_at`), so EVERY side hinge line at `x` lies in `Pi_x`; and
    a side with `deg_i(x) >= 2` whose two hinges at `x` are non-coincident
    SPANS `Pi_x`.  Asserted at every draw.  Where `c(Pi_x) >= 1` the mode
    reports whether the intersection line IS one of those hinge lines --
    which names the mechanism of the excess.

    CAP: `side_library(maxarc, maxtheta, nlad=40)` + `side1_library()`,
    `xy_paths(cap=400, maxlen=9)`, `ndraw` draws per row -- `run_pix`'s own
    committed cap, taken here so the rows are comparable."""
    t0 = time.time()
    print(f'== gp: the GENERAL-POSITION mechanism, tested per draw, seed '
          f'{seed}, ndraw {ndraw}')
    print(f'   CAP: `side_library(maxarc={maxarc}, maxtheta={maxtheta}, '
          f'nlad=40)` + `side1_library()`, `xy_paths(cap=400, maxlen=9)`.')
    lib = _lib(seed, maxarc, maxtheta)
    draws = 0
    jp, jm = {}, {}
    viol_p, viol_m = [], []
    short_p, short_m = 0, 0
    hinge_span = 0
    # the hinge counter is scoped to the EXCESS draws and to the rest
    # SEPARATELY.  (First run of this mode printed one counter under the
    # excess headline while it in fact ranged over every `c = 1` draw --
    # 126, not 102.  Self-caught; the split is the fix.)
    hx_exc, ho_exc, hx_gen, ho_gen = 0, 0, 0, 0
    sat, sat_c1 = 0, 0
    degx = {}
    certp, certm, live, tight, seen, azero = {}, {}, {}, {}, {}, {}
    avals, jP0 = {}, {}
    corner_p, corner_m = {}, {}
    for (tag, E, x, y, d, dd, rho, Pix, Mspc, S, pt, P0e, a) in \
            _rows(lib, ndraw, seed):
        draws += 1
        # THE ROW KEY CARRIES THE EDGE SET, not just the tag.  `side_library`
        # and `side1_library` both emit `cyc(...)`/`gtheta(...)`/`ladder(...)`
        # shapes, so `(tag, x, y)` alone COLLIDES: the first run of this mode
        # reported 400 rows for 427 library rows and under-counted every
        # row-level figure by the 27 collisions.  Self-caught by the
        # draws/rows arithmetic at `ndraw = 1` (427 draws, 400 rows).
        key = (tag, x, y, frozenset(frozenset(e) for e in E))
        seen[key] = True
        Hx = _hinges_at(E, pt, x)
        degx[len(Hx)] = degx.get(len(Hx), 0) + 1
        for h in Hx:
            assert _in_span(h, Pix), \
                ('a SIDE hinge line at x is NOT in Pi_x -- the closed-star '
                 'reading of `plane_at` FAILS', tag)
        if dim(span(Hx)) == PIXDIM:
            hinge_span += 1
        cp = dim(isect(S, Pix)) if S else 0
        cm = dim(isect(S, Mspc)) if S else 0
        assert cp <= PIXDIM and cm <= MDIM, 'c(U) exceeds dim U'
        assert rho <= d, ('(BE-22)(ii) `rho <= delta` FAILS', tag, rho, d)
        assert rho <= dd, ('(BE-256)(ii) `rho <= dist` FAILS', tag, rho, dd)
        # THE SATURATION MECHANISM.  `rho_bar <= <P_0>` pointwise
        # ((BE-30)(iv)); at `rho = dim <P_0>` the containment is an EQUALITY,
        # so `rho_bar` contains the path's FIRST hinge line `l_1 = p_x ^ p_1`
        # -- which is a hinge at `x`, hence lies in `Pi_x`.  So `c(Pi_x) >= 1`
        # POINTWISE whenever the path confinement is saturated.
        P0 = span([wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in P0e])
        if S and rho == dim(P0):
            sat += 1
            assert dim(isect(S, P0)) == rho, ('(BE-30)(iv) fails', tag)
            l1 = wedge2(hat(pt[P0e[0][0]]), hat(pt[P0e[0][1]]))
            assert _in_span(l1, Pix), ('l_1 is not in Pi_x', tag)
            assert _in_span(l1, S), \
                ('!! SATURATION does not give `l_1 in rho_bar`', tag)
            assert cp >= 1, ('!! saturation without `c(Pi_x) >= 1`', tag)
            sat_c1 += 1
        # BSIXTEEN (111, landed `0bd802e7` DURING this direction's run) says
        # in (BE-281)(iii) that the unified lemma should be stated relative
        # to `<P_0>` and not to `Lambda^2 K^4`.  TESTED HERE: the
        # `<P_0>`-relative general-position value is
        #     gpP(U) = max(0, rho + dim(<P_0> cap U) - dim <P_0>),
        # which coincides with `bunif.generic_c` exactly when `dim <P_0> = 6`.
        dP0 = dim(P0)
        kpix, km = dim(isect(P0, Pix)), dim(isect(P0, Mspc))
        gpP_p, gpP_m = max(0, rho + kpix - dP0), max(0, rho + km - dP0)
        assert cp == gpP_p, \
            ('!! the `<P_0>`-RELATIVE general position FAILS at Pi_x',
             tag, dd, rho, dP0, kpix, cp, gpP_p)
        assert cm == gpP_m, \
            ('!! the `<P_0>`-RELATIVE general position FAILS at <M>',
             tag, dd, rho, dP0, km, cm, gpP_m)
        jP0[(dP0, kpix, rho, cp)] = jP0.get((dP0, kpix, rho, cp), 0) + 1
        gp_p, gp_m = bunif.generic_c(rho, PIXDIM), bunif.generic_c(rho, MDIM)
        # THE EXACT LAW, asserted rather than read off the histogram.  The
        # `>=` half at a saturated draw is PROVED above; the claim here is
        # that saturation is the ONLY excess and that `<M>` has none.
        satq = bool(S) and rho == dim(P0)
        assert cp == gp_p + (1 if (satq and rho <= 4) else 0), \
            ('!! `c(Pi_x) = gp + [saturated and rho <= 4]` FAILS',
             tag, dd, rho, cp, gp_p, satq)
        assert cm == gp_m, \
            ('!! `c(<M>)` is NOT the general-position value -- an excess at '
             '`<M>` is a live `Good = EMPTY` route', tag, dd, rho, cm, gp_m)
        jp[(min(dd, 7), rho, cp)] = jp.get((min(dd, 7), rho, cp), 0) + 1
        jm[(min(dd, 7), rho, cm)] = jm.get((min(dd, 7), rho, cm), 0) + 1
        exc = cp > gp_p
        if exc:
            viol_p.append((tag, dd, d, rho, cp, gp_p))
        if cp < gp_p:
            short_p += 1
        if cm > gp_m:
            viol_m.append((tag, dd, d, rho, cm, gp_m))
        if cm < gp_m:
            short_m += 1
        if cp == 1 and S:
            onh = any(_in_span(w, [h]) for w in isect(S, Pix) for h in Hx)
            if exc:
                hx_exc, ho_exc = hx_exc + onh, ho_exc + (not onh)
            else:
                hx_gen, ho_gen = hx_gen + onh, ho_gen + (not onh)
        # ---- the one-draw properness CERTIFICATE (see `run_cert`)
        avals[a] = avals.get(a, 0) + 1
        if a == 0:
            azero[key] = True
        if a == 0 and rho == d:
            tight[key] = True
        if a == 0 and rho == d and rho <= 5:
            if cp < PIXDIM:
                certp[key] = True
            if cm < MDIM:
                certm[key] = True
        if dd >= 6:
            live[key] = True
            if rho <= 5:
                corner_p[(rho, cp)] = corner_p.get((rho, cp), 0) + 1
                corner_m[(rho, cm)] = corner_m.get((rho, cm), 0) + 1
    print(f'  draws {draws}   rows {len(seen)}   '
          f'(side degree at x: {dict(sorted(degx.items()))})')
    print(f'  EVERY side hinge line at x lies in `Pi_x`: ASSERTED at all '
          f'{draws} draws.')
    print(f'  the side\'s OWN hinges at x SPAN `Pi_x` at {hinge_span} of '
          f'{draws} draws.')
    print(f'  `(dist, rho, c(Pi_x))` -> count: {dict(sorted(jp.items()))}')
    print(f'  `(dist, rho, c(<M>))`  -> count: {dict(sorted(jm.items()))}')
    print(f'  `(dim <P_0>, dim(<P_0> cap Pi_x), rho, c(Pi_x))` -> count: '
          f'{dict(sorted(jP0.items()))}')
    print(f'  BSIXTEEN (BE-281)(iii): the `<P_0>`-RELATIVE general position '
          f'`c(U) = max(0, rho + dim(<P_0> cap U) - dim <P_0>)` is ASSERTED '
          f'at all {draws} draws, BOTH blocks.')
    print(f'  general position `c(U) = max(0, rho + dim U - 6)`:')
    print(f'     Pi_x : EXCEEDED at {len(viol_p)} draws, short at '
          f'{short_p}, equal at {draws - len(viol_p) - short_p}')
    print(f'     <M>  : EXCEEDED at {len(viol_m)} draws, short at '
          f'{short_m}, equal at {draws - len(viol_m) - short_m}')
    print(f'  SATURATION `rho = dim <P_0>` at {sat} draws; at EVERY one of '
          f'them `l_1 in rho_bar cap Pi_x` and `c(Pi_x) >= 1`: {sat_c1}.')
    if viol_p:
        print(f'  !! general position is FALSE at `Pi_x`.  First rows '
              f'(tag, dist, delta, rho, c, generic_c):')
        for b in viol_p[:6]:
            print(f'     {b}')
        print(f'     EXCESS draws with `c(Pi_x) = 1`: intersection line IS a '
              f'side hinge at x at {hx_exc}, is NOT at {ho_exc}.')
        print(f'     NON-excess draws with `c(Pi_x) = 1` (general position '
              f'attained): hinge at {hx_gen}, NOT a hinge at {ho_gen}.')
    if not viol_m:
        print('  <M> : general position is NEVER exceeded on this '
              'population.')
    print(f'  -- THE RESIDUE REGIME (`dist >= 6`, `rho <= 5`) --')
    print(f'  `(rho, c(Pi_x))` -> count: {dict(sorted(corner_p.items()))}')
    print(f'  `(rho, c(<M>))`  -> count: {dict(sorted(corner_m.items()))}')
    print(f'  -- THE ONE-DRAW CERTIFICATE --')
    print(f'  `a_i` over draws: {dict(sorted(avals.items()))}; rows with an '
          f'`a_i = 0` draw: {len(azero)} of {len(seen)}')
    print(f'  rows where SOME draw has `a_i = 0` AND `rho = delta`: '
          f'{len(tight)} of {len(seen)}')
    print(f'  PROPERNESS CERTIFIED (theorem, cap-free at the row): '
          f'Pi_x {len(certp)}, <M> {len(certm)}')
    print(f'  rows in the residue regime `dist >= 6`: {len(live)}; '
          f'certified there: Pi_x {len([k for k in certp if k in live])}, '
          f'<M> {len([k for k in certm if k in live])}')
    print(f'  [{time.time() - t0:.1f}s]')
    return draws, viol_p, viol_m, (hx_exc, ho_exc, hx_gen, ho_gen)


# ============================================== the certificate, documented

# THE ONE-DRAW PROPERNESS CERTIFICATE, stated once and computed inside `gp`
# (it reads the same draws, and a second pass over the library would be a
# second eight-minute run for numbers already in hand).
#
#   `rho_i <= delta_i` pointwise ((BE-22)(ii) at `a_i = 0`) and `rho_i` is
#   LOWER semicontinuous ((BE-255)(i) row 2), so `{rho_i = delta_i}` is an
#   OPEN subset of `Chart(H)`; nonempty -- one draw attains it -- it is
#   DENSE, `Chart(H)` being irreducible ((BE-65)(ii)).  `c_i(U)` is UPPER
#   semicontinuous on the locus where `rho_i` is constant ((BE-255)(i) row
#   4), so on that dense open its generic value is its MINIMUM.  And `a_i`
#   is UPPER semicontinuous (row 3), so `a_i = 0` at ONE draw proves it
#   generically -- which is what puts `rho_i <= delta_i` on a NEIGHBOURHOOD
#   instead of at the point.  Hence one draw `q` with
#
#       a(q) = 0   and   rho(q) = delta <= 5   and   c(U)(q) < dim U
#
#   PROVES that `U <= rho_bar_i` is a PROPER closed condition at that peel.
#   A WITNESS, not a search: no cap attaches to the certificate itself.
#   What IS capped is the DENOMINATOR -- how many library rows carry one.
#   A row that does not certify is NOT a counterexample; it is a row at
#   which no `rho = delta <= 5` draw was obtained.


def run_validate():
    run_pop()
    run_gp(ndraw=2, maxarc=6, maxtheta=5)


MODES = {'pop': run_pop, 'gp': run_gp, 'validate': run_validate}


def main(argv):
    if len(argv) < 2 or argv[1] not in MODES:
        print(f'usage: bpropcl.py [{" | ".join(MODES)}]')
        return 1
    MODES[argv[1]]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
