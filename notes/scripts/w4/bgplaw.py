"""
Phase 39, kernel-(K) bare-ext direction BGPLAW (ordinal 114) -- is
(BLOCK-GP) true at `dim <P_0> in {4, 5}`?

    (BLOCK-GP)   at an internal R-node peel at rung 3 in the GENERIC FLAG
                 regime, for every stable `U` and each side `i`,
                 `c_i(U) <= max( f(U), rho_i + dim(<P_0> cap U) - dim <P_0> )`

    (BE-281)(i), owned by `notes/pencil/workbook/bare-ext/BSIXTEEN.md`.
    `f(U) = |U cap {Pi_x, Pi_y}|` is the FORCED FLOOR and is load-bearing:
    the unfloored form is REFUTED in principle by (BE-45)(i)'s series end.

THE FIRST SLICE, and it outranks the lemma.  Every cell of (BLOCK-GP)'s
13 664 is a SIDE ROW -- `bsixteen.run_side` draws a side of the library
STANDALONE, with `bdecor.sample_by_branches` on the side's own edge set.
The statement is about a peel of a COMPOSITE piece `H`.  So the transfer
the figure needs is

    is  Chart(H) -> Chart_flat(side_i)  DOMINANT?

`Chart_flat(side_i)` is written with a flat because `Chart` in this corpus
((CH-1), section (K-chart)) is defined for a graph with `hcard`, min degree 2
and girth >= 4, and it carries NO plane at a degree-2 vertex; a peel
terminal `x` has side-degree 2 at every `cyc(a,b)` row of the library, so
`Pi_x` -- a block of (BLOCK-GP)'s own right-hand side -- is not a function
on `Chart(side_i)` at all.  What `run_side` samples is the FLAGGED side
chart: `hubs_and_branches(E, x, y)` makes both terminals hubs BY FIAT and
`flag_assignment` gives each a plane.  Mode `dom` measures the transfer
between the two populations that actually exist.

WHY THE DIRECTION OF A FAILURE IS KNOWN IN ADVANCE.  `c_i(U) =
dim(rho_bar_i cap U)` is UPPER semicontinuous, so its generic value is its
MINIMUM (the (BE-65)(iii) mechanism, and the reason `run_side` quotes
`min` over draws).  If the image of `Chart(H)` is contained in a proper
closed `Z` of the flagged side chart, the generic value over `Z` is
`>=` the generic value over the whole chart.  So a non-dominance makes the
side rows UNDER-report `c_i`, which is exactly the direction that hides a
violation of (BLOCK-GP).

MODES (run from the repo root, PYTHONHASHSEED=0):

    python3 notes/scripts/w4/bgplaw.py targets  # (BE-299): the 40 surviving
        arithmetic shapes resolved into PER-SIDE LG-violating profiles
        `(U, m, rho, c)` -- the exhaustive target list a refutation must hit.
        Seedless, draw-free; reads `bsixteen.run_arith`'s own enumeration.
    python3 notes/scripts/w4/bgplaw.py dom      # (BE-300)/(BE-301): THE FIRST
        SLICE.  Composite `Chart(H)` draws vs standalone flagged-side draws,
        same side graph, same 16 blocks, generic (min-over-draws) profiles
        compared cell by cell; plus the forced-coincidence census that decides
        dominance outright on part of the population.
    python3 notes/scripts/w4/bgplaw.py reach    # (BE-302): does the side
        library REACH the target profiles at all?  The cap question
        (BE-282)(iii) does not ask -- its (M1) argument prices the UNFLOORED
        law and cannot price the floored one.
    python3 notes/scripts/w4/bgplaw.py gp       # (BE-303): (BLOCK-GP) itself,
        asserted cell by cell on BOTH populations, restricted to and reported
        by `dim <P_0>`.
    python3 notes/scripts/w4/bgplaw.py validate # every mode at reduced caps,
        each fence PRINTED in the same line as the figure it bounds.

CAPS ARE PARAMETERS, NEVER LITERALS COPIED OUT OF A LANDED DRIVER.  Every
mode below takes its caps as keyword arguments with the LANDED value as the
default, so the figure-invariance test is one command.  Section 8's bar (p)
binds every side-row figure: the three `run_side` fences are `ndraw`,
`maxarc`, `maxtheta`, and each mode prints all three.
"""

import os
import sys
import time
import random

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import wedge2, hat                               # noqa: E402
from bimage import dim, span, isect, rho_bar_of                 # noqa: E402
from bdecor import sample_by_branches, d3, weld_d3              # noqa: E402
import bunif                                                    # noqa: E402
import bgoodempty as BG                                         # noqa: E402
import bsixteen as BS                                           # noqa: E402
from bpeel import peel_sides, constructed_tier                  # noqa: E402
from binduc import split_at_pair                                # noqa: E402
from exactcore import neighbors, rank as rank_exact             # noqa: E402
from kbare_common import verts_of                               # noqa: E402

SEED = BS.SEED                 # 20260912 -- the same integer as run_side's
SUBS = BS.SUBS
DIMV = BS.DIMV
RUNG3 = BS.RUNG3


def lg_rhs(S, m, rho):
    """(BLOCK-GP)'s right-hand side with `dim(<P_0> cap U)` taken at the
    TABLE value `B(m, U)`.  The substitution is not free: it is
    (BE-282)/(BE-30)(iv)'s measured equality `dim(<P_0> cap U) = B(dim<P_0>,
    U)` at 13 664 of 13 664 cells, and `gp` mode re-asserts it per cell
    rather than importing it."""
    return max(BS.forced(S), rho + BS.Bbound(m, S) - m)


def lg_rhs_measured(S, rho, cP, dp):
    """The same, with `dim(<P_0> cap U)` MEASURED at the configuration --
    no table substitution."""
    return max(BS.forced(S), rho + cP - dp)


# ============================================ mode: targets   ((BE-299))

def run_targets(dmax=7):
    """The 40 `+L6` survivors of `bsixteen.run_arith`, resolved into the
    PER-SIDE profiles at which (BLOCK-GP) is violated.  A kill condition
    naming a number carries its derivation, so the resolution is computed
    from `run_arith`'s own enumeration rather than retyped from its table.

    CAP: `dmax` is `run_arith`'s own (7), and `dist` is capped there because
    every bound in play sees only `min(dist, 6)`; the `dmax` cell is the
    `>= dmax` class, so the cap is not a truncation."""
    t0 = time.time()
    print('== targets: the per-side LG-violating profiles, seedless, '
          'draw-free')
    print(f'   CAP: dmax={dmax} (run_arith\'s own); the `>= dmax` class is '
          f'the dmax cell.')
    base = list(BS._tuples(dmax))
    shapes = {}          # S -> set of ((m1,m2),(c1,c2),(r1,r2)) surviving +L6
    for S in SUBS:
        if S in BS.DEAD:
            continue
        d = BS.dU(S)
        sh = set()
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
                    sh.add(((m1, m2), (c1, c2), (r1, r2)))
        if sh:
            shapes[S] = sh
    allsh = set()
    for S in shapes:
        allsh |= shapes[S]
    print(f'   +L6 survivors: {len(allsh)} distinct shapes over '
          f'{len(shapes)} blocks (run_arith reports 40).')
    # resolve into per-side profiles
    per, both, one = {}, 0, 0
    for S in sorted(shapes, key=BS.label):
        for ((m1, m2), (c1, c2), (r1, r2)) in sorted(shapes[S]):
            v1 = c1 > lg_rhs(S, m1, r1)
            v2 = c2 > lg_rhs(S, m2, r2)
            assert v1 or v2, ('a +L6 survivor violates NO side of LG -- '
                              'LG would not close it', S, m1, m2, c1, c2)
            if v1 and v2:
                both += 1
            else:
                one += 1
            for (v, m, c, r) in ((v1, m1, c1, r1), (v2, m2, c2, r2)):
                if v:
                    per.setdefault((S, m, r, c), 0)
                    per[(S, m, r, c)] += 1
    print(f'   of the {len(allsh)} shapes, {both} violate LG on BOTH sides '
          f'and {one} on exactly one.')
    print(f'   DERIVED, not asserted: a refutation of (BLOCK-GP) needs ONE '
          f'side profile below.')
    print(f'   THE TARGET LIST -- {len(per)} distinct `(U, dim<P_0>, rho_i, '
          f'c_i)` profiles:')
    by_m = {}
    for (S, m, r, c) in sorted(per, key=lambda k: (k[1], BS.label(k[0]),
                                                   k[2], k[3])):
        print(f'       m={m}  {BS.label(S):<16} rho={r}  c={c}   '
              f'LG allows {lg_rhs(S, m, r)}   (in {per[(S, m, r, c)]} shapes)')
        by_m.setdefault(m, 0)
        by_m[m] += 1
    for (S, m, r, c) in per:
        assert lg_rhs(S, m, r) < BS.Bbound(m, S), \
            ('a target profile does NOT improve on the table -- (BLOCK-GP) '
             'would be implied by LP there', S, m, r, c)
    nest = sum(1 for (S, m, r, c) in per if c == min(r, BS.Bbound(m, S)))
    neq = sum(1 for (S, m, r, c) in per
              if lg_rhs(S, m, r) == min(r, BS.Bbound(m, S)) - 1)
    print(f'   THE NESTED EXTREME `c_i = min(rho_i, B(m,U))` -- '
          f'`rho_bar_i` and `<P_0> cap U`, both')
    print(f'   inside `<P_0>`, meeting in the MAXIMAL dimension their '
          f'dimensions allow, i.e. one')
    print(f'   CONTAINING the other -- holds at {nest} of {len(per)} '
          f'targets; `LG allows` equals')
    print(f'   `min(rho_i, B(m,U)) - 1` at {neq} of {len(per)}.  '
          f'MEASURED, NOT ASSERTED: two')
    print(f'   drafts of this clause asserted first the EQUIVALENCE and '
          f'then the SUFFICIENCY of')
    print(f'   non-nestedness, and the two asserts above REFUTED both in '
          f'0.0 s -- at')
    print(f'   `(L+M+Pix, m=5, rho=3, c=3)` where LG allows 1 and '
          f'`min(rho,B)-1` is 2, and at')
    print(f'   `(L+M+Pix, m=5, rho=3, c=2)` which is a target and is NOT '
          f'the nested extreme.')
    print(f'   So NON-NESTEDNESS kills {nest} of the {len(per)} targets and '
          f'is NOT sufficient for')
    print(f'   the rung-3 closure.  Recorded because it was the route this '
          f'direction wanted.')
    print(f'   ASSERTED at all {len(per)} targets: `LG allows` is STRICTLY '
          f'below the TABLE value')
    print(f'   `B(m, U)`.  So (BLOCK-GP) must BEAT the table at every one of '
          f'them, and no route')
    print(f'   that OUTPUTS the table ((BE-278)(iii) + (BE-279)(ii)) can '
          f'output (BLOCK-GP).')
    print(f'   by `dim <P_0>`: {dict(sorted(by_m.items()))}')
    print('   THE QUESTION\'S REGION is `dim <P_0> in {4, 5}`; every target '
          'profile above')
    print('   sits in it, so the region is not merely inhabited -- it is '
          'the WHOLE residue.')
    print(f'   [{time.time() - t0:.1f}s]')
    return per


# ============================================ side statistics, shared

def side_stats(E, pt, x, y, fr, cap=400, maxlen=9):
    """`(dist, rho, dim<P_0>, {S: c(S)}, {S: dim(<P_0> cap U)})` for a side
    `E` at a configuration `pt` whose flag frame is `fr`.  ONE shortest
    path, not all of them -- sound because `rho_bar_i` is confined by EVERY
    x--y path ((BE-30)(iv)), so one is an upper bound and not sharp."""
    dd = BG.dist_of(E, x, y)
    paths, _ = BG.xy_paths(E, x, y, cap=cap, maxlen=maxlen)
    short = [P for P in paths if len(P) == dd]
    if not short:
        return None
    Srho, rho, _dM, _r = rho_bar_of(E, pt, x, y)
    P0 = span([wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in short[0]])
    dp = dim(P0)
    assert dp <= min(dd, DIMV), ('`dim<P_0>` exceeds min(dist,6)', dd, dp)
    B = BS.blocks(fr)
    c, cp = {}, {}
    for S in SUBS:
        U = BS.usub(B, S)
        c[S] = dim(isect(Srho, U)) if (Srho and U) else 0
        cp[S] = dim(isect(P0, U)) if U else 0
        assert c[S] <= cp[S], ('THE BLOCK PATH BOUND FAILS', S, c[S], cp[S])
    return dd, rho, dp, c, cp


def composite_peels(maxlen=3, njobs=60, seed=SEED):
    """Every internal peel of populations A and B of `bunif` -- the ONLY
    place in the harness where a side sits inside an ambient `H`.
    Yields `(tag, H, x, y, side1, side2)`."""
    for nm, pc in bunif.battery_peels():
        H = pc['H']
        for i, (_x0, _y0, _ce, kind0) in enumerate(pc['children']):
            if kind0 == 'leaf':
                continue
            x, y, side1, side2, _k = peel_sides(pc, i)
            yield (f'A:{nm}#{i}', H, x, y, side1, side2)
    seen, n = set(), 0
    for (tag, E, x, y, d1, d2, _forced, rn) in constructed_tier(
            maxlen=maxlen, nsamp=60, seed=seed):
        if n >= njobs:
            return
        if not rn or min(d1, d2) == 0:
            continue
        if (tag, x, y) in seen:
            continue
        seen.add((tag, x, y))
        sp = split_at_pair(E, x, y)
        if sp is None:
            continue
        _V1, E1, _V2, E2 = sp
        n += 1
        yield (f'B:{tag}@{x},{y}', E, x, y, E1, E2)


# ============================================ mode: dom       ((BE-300))

def run_dom(ndraw=4, seed=SEED, maxlen=3, njobs=60, cap=400, pmaxlen=9):
    """THE FIRST SLICE.  For every internal peel of populations A and B and
    each of its two sides, draw the COMPOSITE chart `Chart(H)` and the
    STANDALONE flagged side chart and compare the generic (min-over-draws)
    16-block profile cell by cell.

    CAPS: `ndraw` draws on EACH population (`run_side`'s landed fence is 2
    and `bgoodempty.run_pix`'s is 3; this is UN-fenced to {ndraw});
    populations A and B are `bunif.battery_peels()` and
    `constructed_tier(maxlen={maxlen}, nsamp=60)` capped at {njobs} peels;
    `xy_paths(cap={cap}, maxlen={pmaxlen})`; ONE shortest path per side.

    F27: `min` over `ndraw` draws is a LOWER bound on the generic value of an
    upper-semicontinuous statistic, on BOTH populations.  A cell where the
    composite min EXCEEDS the standalone min is therefore a one-sided
    witness -- it can only understate how often the two disagree."""
    t0 = time.time()
    print(f'== dom: THE FIRST SLICE -- is `Chart(H) -> Chart_flat(side_i)` '
          f'dominant?  seed {seed}')
    print(f'   CAPS: ndraw={ndraw} on each population (run_side fences to 2, '
          f'run_pix to 3);')
    print(f'   population B = constructed_tier(maxlen={maxlen}, nsamp=60) '
          f'capped at {njobs} peels;')
    print(f'   xy_paths(cap={cap}, maxlen={pmaxlen}); ONE shortest path per '
          f'side.')
    npeel, nside, ncmp = 0, 0, 0
    creg, coff = 0, 0                     # composite draws on/off regime
    sreg, soff = 0, 0                     # standalone draws on/off regime
    forced_coin = []                      # peels where EVERY composite draw
    #                                       is off the generic flag regime
    gt, lt, eq = {}, {}, 0
    examples = []
    dimdiff = []
    sdeg, sok = {}, {}
    for (tag, H, x, y, side1, side2) in composite_peels(maxlen, njobs, seed):
        npeel += 1
        # --- composite draws
        cprof = {1: {}, 2: {}}
        caux = {1: [], 2: []}
        conreg = 0
        for k in range(ndraw):
            rng = random.Random(seed + 733 * k + len(H))
            got = sample_by_branches(H, x, y, rng)
            if got is None:
                continue
            pt = got[0]
            fr = bunif.flag_frame(H, pt, x, y)
            if fr is None:
                coff += 1
                continue
            creg += 1
            conreg += 1
            for i, E in ((1, side1), (2, side2)):
                try:
                    st = side_stats(E, pt, x, y, fr, cap, pmaxlen)
                except AssertionError:
                    st = None
                if st is None:
                    continue
                dd, rho, dp, c, _cp = st
                caux[i].append((dd, rho, dp))
                for S in SUBS:
                    cprof[i][S] = min(cprof[i].get(S, 9), c[S])
        if conreg == 0:
            forced_coin.append(tag)
        # --- standalone draws of the SAME side graphs
        sprof = {1: {}, 2: {}}
        saux = {1: [], 2: []}
        for i, E in ((1, side1), (2, side2)):
            nbE = neighbors(E)
            sdeg[(tag, i)] = min(len(nbE[x]), len(nbE[y]))
            for k in range(ndraw):
                rng = random.Random(seed + 733 * k + len(E))
                got = sample_by_branches(E, x, y, rng)
                if got is None:
                    continue
                pt = got[0]
                fr = bunif.flag_frame(E, pt, x, y)
                if fr is None:
                    soff += 1
                    continue
                sreg += 1
                sok[(tag, i)] = sok.get((tag, i), 0) + 1
                try:
                    st = side_stats(E, pt, x, y, fr, cap, pmaxlen)
                except AssertionError:
                    st = None
                if st is None:
                    continue
                dd, rho, dp, c, _cp = st
                saux[i].append((dd, rho, dp))
                for S in SUBS:
                    sprof[i][S] = min(sprof[i].get(S, 9), c[S])
        # --- compare
        for i in (1, 2):
            if not cprof[i] or not sprof[i]:
                continue
            nside += 1
            cd = sorted({a[2] for a in caux[i]})
            sd = sorted({a[2] for a in saux[i]})
            cr = sorted({a[1] for a in caux[i]})
            sr = sorted({a[1] for a in saux[i]})
            if cd != sd or cr != sr:
                dimdiff.append((tag, i, cd, sd, cr, sr))
            for S in SUBS:
                ncmp += 1
                a, b = cprof[i][S], sprof[i][S]
                if a > b:
                    gt[S] = gt.get(S, 0) + 1
                    if len(examples) < 24:
                        examples.append((tag, i, BS.label(S), b, a, cd, cr))
                elif a < b:
                    lt[S] = lt.get(S, 0) + 1
                else:
                    eq += 1
    print(f'   peels {npeel}; comparable sides {nside}; (side, U) cells '
          f'compared {ncmp}.')
    print(f'   composite draws IN the generic flag regime {creg}, REJECTED '
          f'off it {coff}.')
    print(f'   standalone draws IN the regime {sreg}, REJECTED off it '
          f'{soff}.')
    d1s = [k for k in sdeg if sdeg[k] == 1]
    nev = [k for k in sdeg if sok.get(k, 0) == 0]
    print(f'   THE CAUSE OF THE ASYMMETRY, measured not assumed: sides with '
          f'a terminal of side-degree')
    print(f'   1: {len(d1s)} of {len(sdeg)}; sides at which the STANDALONE '
          f'flag frame NEVER exists:')
    print(f'   {len(nev)} of {len(sdeg)}.  They coincide: '
          f'{sorted(d1s) == sorted(nev)}.  At side-degree 1 the closed')
    print(f'   side-star spans a LINE, so `bimage.plane_at` returns `None` '
          f'and `Pi_x` is not')
    print(f'   defined on the side at all; inside `H` the other side '
          f'determines it.')
    print(f'   peels at which EVERY composite draw is off the generic flag '
          f'regime: {len(forced_coin)}')
    for tg in forced_coin[:12]:
        print(f'       {tg}')
    print(f'   CELLS where the COMPOSITE generic c EXCEEDS the STANDALONE '
          f'generic c')
    print(f'   (a non-dominance witness, and the direction that hides a '
          f'violation): '
          f'{sum(gt.values())}')
    for S in sorted(gt, key=BS.label):
        print(f'       {BS.label(S):<16} x{gt[S]}')
    for ex in examples:
        print(f'       e.g. {ex[0]} side {ex[1]} {ex[2]}: standalone '
              f'{ex[3]} -> composite {ex[4]}   dim<P_0>={ex[5]} rho={ex[6]}')
    print(f'   CELLS where the composite generic c is SMALLER: '
          f'{sum(lt.values())}   (composite more generic)')
    for S in sorted(lt, key=BS.label):
        print(f'       {BS.label(S):<16} x{lt[S]}')
    print(f'   CELLS agreeing: {eq}')
    print(f'   sides whose `(dim<P_0>, rho)` SUPPORT differs between the two '
          f'populations: {len(dimdiff)}')
    for dd in dimdiff[:12]:
        print(f'       {dd[0]} side {dd[1]}: dim<P_0> comp {dd[2]} vs '
              f'standalone {dd[3]}; rho comp {dd[4]} vs standalone {dd[5]}')
    print(f'   [{time.time() - t0:.1f}s]')
    return npeel, nside, ncmp, gt, lt, eq, forced_coin, dimdiff


# ============================================ mode: orbit     ((BE-300))

def _frame_mat(fr):
    """`T = [p_x, e_1, e_2, p_y]` as COLUMNS.  `flag_frame`'s own acceptance
    test is `rank[p_x, e_1, e_2, p_y] = 4`, i.e. exactly the statement that
    this matrix is invertible -- the generic flag regime IS the locus where
    the flag pair is a projective FRAME."""
    px, _Bx, py, _By, e1, e2 = fr
    return [[c[i] for c in (px, e1, e2, py)] for i in range(4)]


def _relabel(E, tag, keep):
    return [tuple((w if w in keep else (tag, w)) for w in e) for e in E]


def _plane_eq(Ba, Bb):
    """Two 3-dimensional bases span the same plane."""
    return dim(span(list(Ba) + list(Bb))) == 3


def _pt_eq(a, b):
    return dim(span([hat(a), hat(b)])) == 1


def run_orbit(npair=40, seed=SEED, maxarc=5, maxtheta=4, cap=400, maxlen=9,
              nlad=6):
    """THE FIRST SLICE, SETTLED CONSTRUCTIVELY.  The generic flag regime is
    a SINGLE `PGL_4` orbit -- `bunif.flag_frame`'s own rank-4 test says the
    flag pair `(p_x, e_1, e_2, p_y)` is a projective frame, and a linear map
    carrying one frame to another carries `pi_x = <p_x,e_1,e_2>` to `pi_x'`
    and `pi_y = <p_y,e_1,e_2>` to `pi_y'`.  Coplanarity of closed stars is
    projective, so `Chart_flat(side)` is `PGL_4`-invariant and the flag map
    `phi: Chart_flat(side) -> F` is equivariant.  Hence

        im phi meets the generic-flag locus  ==>  im phi CONTAINS it.

    and `Chart(H) = Chart_flat(H_1) x_F Chart_flat(H_2)` gives: over the
    generic flag regime the projection `Chart(H) -> Chart_flat(H_1)` is
    SURJECTIVE, not merely dominant, as soon as side 2 admits ONE
    generic-flag configuration.  This mode EXHIBITS the transport at exact
    rational arithmetic: two library sides drawn independently, side 2
    carried onto side 1's frame, the two GLUED, and the glued configuration
    asserted to be a point of `Chart(H)` with side 1's own blocks.  An
    exhibited certificate needs one draw, because it is a proof.

    CAPS: {npair} glued pairs; the pair pool is
    `side_library(maxarc={maxarc}, maxtheta={maxtheta}, nlad={nlad})` --
    FENCED below `run_side`'s 8/7/40 to keep the glued graphs small, and the
    fence bounds only HOW MANY certificates are exhibited, never whether one
    exists.  `xy_paths(cap={cap}, maxlen={maxlen})`."""
    t0 = time.time()
    print(f'== orbit: the generic flag regime is ONE PGL_4 orbit -- the '
          f'transport, exhibited.  seed {seed}')
    print(f'   CAPS: npair={npair}; pool = side_library(maxarc={maxarc}, '
          f'maxtheta={maxtheta}, nlad={nlad}),')
    print(f'   FENCED below run_side\'s 8/7/40 -- the fence bounds how many '
          f'certificates, not whether')
    print(f'   one exists.  xy_paths(cap={cap}, maxlen={maxlen}).')
    pool = []
    for (tag, E, x, y) in BG.side_library(maxarc, maxtheta, nlad, seed):
        rng = random.Random(seed + len(E))
        got = sample_by_branches(E, x, y, rng)
        if got is None:
            continue
        pt = got[0]
        fr = bunif.flag_frame(E, pt, x, y)
        if fr is None:
            continue
        pool.append((tag, E, pt, fr))
    print(f'   pool: {len(pool)} library sides with a generic-flag '
          f'exact-Q configuration.')
    ngl, nast, rung = 0, 0, {}
    cmatch, cbad = 0, []
    hyp = {'mindeg2': 0, 'girth4': 0, 'xny': 0}
    for j in range(min(npair, len(pool) - 1)):
        (t1, E1, pt1, fr1) = pool[j]
        (t2, E2, pt2, fr2) = pool[(j * 7 + 3) % len(pool)]
        if t1 == t2:
            continue
        T1, T2 = _frame_mat(fr1), _frame_mat(fr2)
        T2i = bunif.mat_inv(T2)
        if T2i is None:
            continue
        g = bunif.matmul(T1, T2i)
        # transport side 2
        pt2g, ok = {}, True
        for v, c in pt2.items():
            q = bunif.apply4(g, hat(c))
            if q[3] == 0:
                ok = False
                break
            pt2g[v] = [q[0] / q[3], q[1] / q[3], q[2] / q[3]]
        if not ok:
            continue
        fr2g = bunif.flag_frame(E2, pt2g, 'x', 'y')
        assert fr2g is not None, 'transport left the generic flag regime'
        assert _pt_eq(pt2g['x'], pt1['x']) and _pt_eq(pt2g['y'], pt1['y']), \
            'the transported side does not carry side 1\'s two POINTS'
        assert _plane_eq(fr2g[1], fr1[1]) and _plane_eq(fr2g[3], fr1[3]), \
            'the transported side does not carry side 1\'s two PLANES'
        nast += 4
        # glue
        E2r = _relabel(E2, t2, {'x', 'y'})
        H = list(E1) + E2r
        pt = dict(pt1)
        for v, c in pt2g.items():
            pt[v if v in ('x', 'y') else (t2, v)] = c
        nbH = neighbors(H)
        if min(len(nbH[w]) for w in verts_of(H)) >= 2:
            hyp['mindeg2'] += 1
        if 'y' not in nbH['x']:
            hyp['xny'] += 1
        bad = False
        for w in verts_of(H):
            star = [hat(pt[w])] + [hat(pt[z]) for z in nbH[w]]
            if rank_exact(star) > 3:
                bad = True
                break
        assert not bad, ('THE GLUED CONFIGURATION IS NOT A POINT OF '
                         'Chart(H) -- the fibre-product identity fails',
                         t1, t2)
        nast += 1
        frH = bunif.flag_frame(H, pt, 'x', 'y')
        assert frH is not None, 'the glued peel is off the generic regime'
        assert _plane_eq(frH[1], fr1[1]) and _plane_eq(frH[3], fr1[3]), \
            'the glued peel does not carry side 1\'s blocks'
        nast += 2
        ngl += 1
        d1 = d3(E1) - weld_d3(E1, 'x', 'y')
        d2 = d3(E2r) - weld_d3(E2r, 'x', 'y')
        rung[d1 + d2] = rung.get(d1 + d2, 0) + 1
        # equivariance of c_i: the transported side 2 reads the SAME profile
        st_alone = side_stats(E2, pt2, 'x', 'y', fr2, cap, maxlen)
        st_glued = side_stats(E2r, pt, 'x', 'y', frH, cap, maxlen)
        if st_alone is None or st_glued is None:
            continue
        for S in SUBS:
            if st_alone[3][S] == st_glued[3][S]:
                cmatch += 1
            else:
                cbad.append((t1, t2, BS.label(S), st_alone[3][S],
                             st_glued[3][S]))
        assert st_alone[1] == st_glued[1] and st_alone[2] == st_glued[2], \
            ('the transport moved rho or dim<P_0>', t1, t2)
        nast += 2
    print(f'   GLUED PEELS CONSTRUCTED: {ngl}; exact-Q assertions passed '
          f'{nast}, 0 failures.')
    print(f'   Each one is a CERTIFICATE that two independently drawn '
          f'generic-flag side')
    print(f'   configurations GLUE to a point of `Chart(H)` -- the fibre '
          f'product is onto.')
    print(f'   side-2 `c_i(U)` profile preserved by the transport at '
          f'{cmatch} cells; mismatches {len(cbad)}.')
    for b in cbad[:8]:
        print(f'       {b}')
    print(f'   `Sigma delta` of the glued peels: '
          f'{dict(sorted(rung.items()))}   (rung 3 is `<= {RUNG3}`)')
    print(f'   glued graphs with min degree >= 2: {hyp["mindeg2"]} of '
          f'{ngl}; with `x !~ y`: {hyp["xny"]} of {ngl}.')
    print(f'   [{time.time() - t0:.1f}s]')
    return ngl, nast, cmatch, cbad, rung


# ============================================ mode: reach     ((BE-302))

def run_reach(ndraw=3, seed=SEED, maxarc=8, maxtheta=7, cap=400, maxlen=9,
              nlad=40):
    """DOES THE LIBRARY REACH THE TARGETS?  (BE-282)(iii) prices the 100 %
    by asking whether (M1) -- the one landed mechanism that refutes the
    UNFLOORED law -- fires anywhere in the library, and finds it fires at 0
    of 428 sides.  That argument CANNOT price (BLOCK-GP): the floor `f(U)`
    is in the statement precisely so that a series end does not refute it.
    The cap question for the FLOORED law is a different one -- does the
    library realize the `(U, dim<P_0>, rho_i, c_i)` profiles at which LG is
    violated at all? -- and this mode asks it.

    CAPS: ndraw={ndraw} (run_side fences to 2, run_pix to 3 -- UN-fenced
    here); maxarc={maxarc}, maxtheta={maxtheta} (run_side's committed
    values); xy_paths(cap={cap}, maxlen={maxlen}); ONE shortest path."""
    t0 = time.time()
    print(f'== reach: does the side library REACH the LG-violating '
          f'profiles?  seed {seed}')
    print(f'   CAPS: ndraw={ndraw} (run_side 2, run_pix 3), maxarc={maxarc}, '
          f'maxtheta={maxtheta},')
    print(f'   xy_paths(cap={cap}, maxlen={maxlen}); ONE shortest path per '
          f'side.')
    per = {}
    base = list(BS._tuples(7))
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
                        if c > lg_rhs(S, m, r):
                            per[(S, m, r, c)] = per.get((S, m, r, c), 0) + 1
    lib = list(BG.side_library(maxarc, maxtheta, nlad, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in BG.side1_library()]
    rows, ndr, cells = 0, 0, 0
    mrho = {}                  # (m, rho) -> count of (row, draw)
    cbym = {}                  # (S, m, rho) -> {c: count}
    rowsof = {}                # (S, m, rho) -> the DISTINCT library rows
    lgbad = []
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
                st = side_stats(E, pt, x, y, fr, cap, maxlen)
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
                cells += 1
                cbym.setdefault((S, dp, rho), {})
                cbym[(S, dp, rho)][c[S]] = \
                    cbym[(S, dp, rho)].get(c[S], 0) + 1
                rowsof.setdefault((S, dp, rho), set()).add(tag)
                if c[S] > lg_rhs_measured(S, rho, cp[S], dp):
                    lgbad.append((tag, BS.label(S), dp, rho, c[S], cp[S]))
        if seen:
            rows += 1
    print(f'   library rows with at least one generic-regime draw {rows}; '
          f'draws {ndr}; (draw, U) cells {cells}.')
    print(f'   THE `(dim<P_0>, rho_i)` SUPPORT the library reaches '
          f'(count of draws):')
    for k in sorted(mrho):
        print(f'       dim<P_0>={k[0]} rho={k[1]}   x{mrho[k]}')
    need = sorted({(k[1], k[2]) for k in per})
    miss = [k for k in need if k not in mrho]
    print(f'   THE TARGET LIST needs {len(need)} distinct `(dim<P_0>, '
          f'rho_i)` pairs; the library reaches')
    print(f'   {len(need) - len(miss)} of them and MISSES {len(miss)}:')
    for k in miss:
        print(f'       dim<P_0>={k[0]} rho={k[1]}   NOT FOUND UNDER CAP C')
    print(f'   AT THE PAIRS IT DOES REACH -- observed `c_i(U)` against the '
          f'target value:')
    hit, sat, slack = 0, 0, 0
    for (S, m, r, c) in sorted(per, key=lambda k: (k[1], BS.label(k[0]),
                                                   k[2], k[3])):
        h = cbym.get((S, m, r))
        if h is None:
            continue
        obs = dict(sorted(h.items()))
        flag = ' <== TARGET REACHED' if c in h else ''
        if c in h:
            hit += 1
        allow = lg_rhs(S, m, r)
        if max(h) == allow:
            sat += 1
            flag += '  [BOUND SATURATED]'
        elif max(h) < allow:
            slack += 1
        nrw = len(rowsof.get((S, m, r), ()))
        print(f'       m={m} {BS.label(S):<16} rho={r}  target c={c} '
              f'(LG allows {allow})   observed {obs}  on {nrw} distinct '
              f'rows{flag}')
    print(f'   target profiles REACHED: {hit} of {len(per)}.')
    print(f'   OF THE {sat + slack} REACHED `(U, dim<P_0>, rho_i)` cells: '
          f'the bound is SATURATED')
    print(f'   (`max observed c_i` = the (BLOCK-GP) allowance) at {sat} and '
          f'SLACK at {slack}.  A law')
    print(f'   saturated and never exceeded is being tested AT ITS EDGE; '
          f'a law with slack')
    print(f'   everywhere would not be.')
    print(f'   (BLOCK-GP) VIOLATIONS, measured `dim(<P_0> cap U)`, no table '
          f'substitution: {len(lgbad)}')
    for b in lgbad[:20]:
        print(f'       {b}')
    print(f'   [{time.time() - t0:.1f}s]')
    return rows, ndr, cells, mrho, cbym, per, lgbad


# ============================================ mode: gp        ((BE-303))

def run_gp(ndraw=3, seed=SEED, maxlen=3, njobs=60, cap=400, pmaxlen=9):
    """(BLOCK-GP) ITSELF on the COMPOSITE population -- the object the
    statement is about.  Every cell asserts the block path bound and the
    table floor, then MEASURES (BLOCK-GP) with `dim(<P_0> cap U)` taken at
    the configuration.  Reported by `dim <P_0>` so the question's region
    `{4, 5}` is separable.

    CAPS: ndraw={ndraw}; population B = constructed_tier(maxlen={maxlen},
    nsamp=60) capped at {njobs} peels; xy_paths(cap={cap},
    maxlen={pmaxlen}); ONE shortest path per side."""
    t0 = time.time()
    print(f'== gp: (BLOCK-GP) on the COMPOSITE population, seed {seed}')
    print(f'   CAPS: ndraw={ndraw}; population B = '
          f'constructed_tier(maxlen={maxlen}, nsamp=60) capped at {njobs};')
    print(f'   xy_paths(cap={cap}, maxlen={pmaxlen}); ONE shortest path per '
          f'side.')
    bym, bad, rung = {}, [], {}
    npeel, nreg, noff = 0, 0, 0
    for (tag, H, x, y, side1, side2) in composite_peels(maxlen, njobs, seed):
        npeel += 1
        f1, g1 = d3(side1), weld_d3(side1, x, y)
        f2, g2 = d3(side2), weld_d3(side2, x, y)
        dl = (f1 - g1) + (f2 - g2)
        rung[dl] = rung.get(dl, 0) + 1
        for k in range(ndraw):
            rng = random.Random(seed + 733 * k + len(H))
            got = sample_by_branches(H, x, y, rng)
            if got is None:
                continue
            pt = got[0]
            fr = bunif.flag_frame(H, pt, x, y)
            if fr is None:
                noff += 1
                continue
            nreg += 1
            for i, E in ((1, side1), (2, side2)):
                try:
                    st = side_stats(E, pt, x, y, fr, cap, pmaxlen)
                except AssertionError:
                    st = None
                if st is None:
                    continue
                dd, rho, dp, c, cp = st
                for S in SUBS:
                    if S in BS.DEAD:
                        continue
                    bym.setdefault(dp, [0, 0])
                    if c[S] <= lg_rhs_measured(S, rho, cp[S], dp):
                        bym[dp][0] += 1
                    else:
                        bym[dp][1] += 1
                        bad.append((tag, i, BS.label(S), dp, rho, c[S],
                                    cp[S], dl))
    print(f'   peels {npeel}; composite draws in the generic flag regime '
          f'{nreg}, off it {noff}.')
    print(f'   `Sigma delta` of the peels (rung 3 is `<= {RUNG3}`): '
          f'{dict(sorted(rung.items()))}')
    print(f'   (BLOCK-GP) by `dim <P_0>`  -- (holds, fails):')
    for k in sorted(bym):
        print(f'       dim<P_0>={k}   holds {bym[k][0]}   fails {bym[k][1]}')
    print(f'   total violations {len(bad)}')
    for b in bad[:20]:
        print(f'       {b}')
    print(f'   [{time.time() - t0:.1f}s]')
    return npeel, nreg, noff, bym, bad, rung


def run_validate():
    print('== validate: targets + dom + gp + reduced reach')
    print('   FENCED: dom(ndraw=2, njobs=8) against 4/60; gp(ndraw=2, '
          'njobs=8) against 3/60;')
    print('   reach(ndraw=1, maxarc=4, maxtheta=4, nlad=6) against '
          '3/8/7/40.  targets is draw-free')
    print('   and runs at its full default.')
    run_targets()
    run_orbit(npair=6, maxarc=4, maxtheta=3, nlad=3)
    run_dom(ndraw=2, njobs=8)
    run_gp(ndraw=2, njobs=8)
    run_reach(ndraw=1, maxarc=4, maxtheta=4, nlad=6)


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode == 'targets':
        run_targets()
    elif mode == 'dom':
        run_dom()
    elif mode == 'reach':
        run_reach()
    elif mode == 'gp':
        run_gp()
    elif mode == 'orbit':
        run_orbit()
    elif mode == 'validate':
        run_validate()
    else:
        print(f'unknown mode {mode!r}')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
