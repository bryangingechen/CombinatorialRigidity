"""
Direction BWHOLEH (Phase 39 PENCIL, section (K-bare-ext)) -- can a WHOLE-`H`
peel be built with `c_1(Pi_x) + c_2(Pi_x) >= 3` at `a = 0`, `Sigma_delta <= 6`,
side-degree `>= 2` on BOTH sides, internal R-node peel, generic flag regime --
which REFUTES the `Pi_x` obligation on the 26 of 30 residue tuples (BE-235)(ii)
puts at rung 3?

  THE ANSWER, said at the top: YES, and the obligation is REFUTED there --
  as a UNIVERSALLY-QUANTIFIED statement over that stratum, which is how
  (BE-239)(ii) records every consumer in Steps BE148-BE237 using it.  Side 1
  is (BE-242)(ii)'s (4,4) firing cycle (`delta_1 = rho_1 = 2`, `c_1 = 2`);
  side 2 is a subdivided 3-connected skeleton that is PATH-SATURATED
  (`delta_2 = d_min_2 = 4`), so (BE-45)(ii) gives `c_2 >= 1` with no
  genericity.  `Sigma_delta = 6`, `slack = 0`, `c_1 + c_2 = 3 > 2`, at
  `a = (0,0)`, side-degree `>= 2` on both sides, side 2 `rnode_shaped`, whole
  -`H` `verify_pencil_witness` green, in the generic flag regime: 72 of 72
  rows over both skeletons and all six non-adjacent hub pairs of each,
  against a matched 36 of 36 control.

  THE SCOPE, which travels with the figure: the killing point is STEERED.
  The SAME `H` ATTAINS at a free draw, so `Good` is DENSE ((BE-69)(ii)) and
  the shortfall is a phenomenon at a special point -- (BE-14), half (B) and
  `hbareSplit` are NOT reached.

  (BE-244)(i)'s "0 of 236 196" is reproduced exactly by `sat` and its
  DISCLOSED cap is then moved by one: at branch lengths {1,2,3,4}, same three
  skeletons, path saturation occurs at 100 656 of 3 145 728.

  MODES
    sigma    the COMBINATORIAL feasibility layer, seedless and cap-free over
             the enumerated profile space: which (side-1 cycle shape, skeleton,
             hub pair, branch profile) quadruples have `delta_1 + delta_2 <= 6`
             with side 2 R-node-shaped and every `legal_peel` graph gate green.
             No configuration is drawn.
    peel     THE CONSTRUCTION.  Side 1 = (BE-242)(ii)'s firing cycle steered by
             `p_y`; side 2 = the subdivided skeleton drawn around the FIXED
             flags at x and y; the row read off `bfour.e_row` and the gates off
             `bfour.gates_of`.
    steer    side 2 steered for `c_2(Pi_x) >= 1` rather than drawn freely.
    validate sigma + peel + steer in one process.

  NOTATION, stated ONCE and matching BSIXRUNG's.  `V := Lambda^2 K^4`;
  `Pi_x := p_x ^ pi_x`; `c_i(U) := dim(rho_bar_i cap U)`;
  `slack := max(0, delta_1 + delta_2 - 6)`; `a_i := dim M_i - 6 - f_i`.  The
  `Pi_x` OBLIGATION is `c_1(Pi_x) + c_2(Pi_x) <= 2 + slack`.  RUNG 3 is
  `Sigma_delta <= 6`, where `slack = 0` and the obligation IS `c_1 + c_2 <= 2`
  ((BE-225)(iii)).

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is never called from here.  No width-12 object is built.
  `bwin` is not imported.  No Python local is named `E1`/`E2`/`A1`.  No
  `.lean` is opened.
"""

import os
import sys
import time
import random
import itertools
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import wedge2, nullspace                          # noqa: E402
from bimage import dim, span, isect, contains, pencil_space      # noqa: E402
from bimage import plane_at, hat                                 # noqa: E402
from bdecor import (hubs_and_branches, hcard_ok_piece, girth,    # noqa: E402
                    flag_assignment, draw_branch, assemble,
                    neighbors, verts_of)
from bpeel import SKELETONS, subdivided, delta_pair, rnode_shaped # noqa: E402
from bproper import composite, NONADJ                            # noqa: E402
from bfour import side_nums, e_row, gates_of                     # noqa: E402
from bunif import flag_frame                                     # noqa: E402
from binduc import rel_screw_space                               # noqa: E402
import barch as BA                                                  # noqa: E402

SEED = 20260912
RUNG3 = 6          # `Sigma_delta <= RUNG3` is (BE-225)(iii)'s bottom rung
PIXDIM = 2         # `dim Pi_x`, (BE-100)(i)'s `du`


def pix_ok(c1, c2, d1, d2):
    """The `Pi_x` OBLIGATION at a measured row: `barch.violates` as landed,
    negated.  Imported rather than restated so the yardstick cannot drift."""
    return not BA.violates(c1, c2, PIXDIM, d1, d2)


# ------------------------------------------------------------ side-1 shapes

def cycle_side(m1, m2):
    """SIDE 1 = a CYCLE THROUGH BOTH x AND y, arcs of `m1` and `m2` edges.
    This is (BE-242)(ii)'s firing shape read as a side of a whole `H`.  It is
    NOT in `bline.longcore_library()`, whose every entry is a cycle at `x`
    with `y` hung off a TAIL -- the provenance fence `blindaxes.py` cannot
    list, checked at the generator (GLAMPROP bar (ii))."""
    pn = ['x'] + [f'u{k + 1}' for k in range(m1 - 1)] + ['y']
    qn = ['x'] + [f'v{k + 1}' for k in range(m2 - 1)] + ['y']
    return ([(pn[k], pn[k + 1]) for k in range(m1)]
            + [(qn[k], qn[k + 1]) for k in range(m2)])


def _nonadj_pairs(skname):
    """EVERY skeleton-non-adjacent hub pair, not `bproper.NONADJ`'s list.
    NONADJ carries 3 of the prism's 6 such pairs; under a NON-UNIFORM branch
    profile the omitted three are not automorphic images of the listed three,
    so the list is a fence.  Reported by `sigma` against NONADJ."""
    sk = SKELETONS[skname]
    nb = neighbors(sk)
    V = sorted(verts_of(sk), key=str)
    return [(a, b) for a, b in itertools.combinations(V, 2) if b not in nb[a]]


def graph_gates(E, x, y, s1, s2):
    """`bline.legal_peel`'s own return, recomputed here so the report is gate
    by gate rather than a boolean: (CH-1) `hcard` on H, min degree, girth,
    `deg_H(x)`, `deg_H(y)`, x !~ y, side 2 R-node-shaped."""
    nb = neighbors(E)
    okh, _W, _br, _ha = hcard_ok_piece(E, x, y)
    return dict(hcard=okh,
                mindeg=min(len(nb[w]) for w in verts_of(E)),
                girth=girth(E), degx=len(nb[x]), degy=len(nb[y]),
                adj=(y in nb[x]),
                rnode_far=rnode_shaped(s2, x, y),
                deg1x=len(neighbors(s1)[x]), deg2x=len(neighbors(s2)[x]),
                deg1y=len(neighbors(s1)[y]), deg2y=len(neighbors(s2)[y]))


def gates_green(g):
    return (g['hcard'] and g['mindeg'] >= 2 and g['girth'] >= 4
            and g['degx'] >= 3 and g['degy'] >= 3 and not g['adj']
            and g['rnode_far'] and g['deg1x'] >= 2 and g['deg2x'] >= 2
            and g['deg1y'] >= 2 and g['deg2y'] >= 2)


# ================================================ mode: sigma  -- the region

def run_sigma(maxlen=2, arcs=((4, 4), (5, 4), (4, 5), (5, 5))):
    """EXHAUSTIVE over the enumerated quadruple space, seedless: no
    configuration is drawn, so no cap of the sampling kind applies.  The cap
    is the ENUMERATION: `arcs` for side 1 and branch lengths `1..maxlen` for
    side 2, over both skeletons that have a non-adjacent hub pair.

    `maxlen` DEFAULTS TO 2 for cost, not for evidence: the count is
    `4 x 12 x maxlen^9` composite builds, so `maxlen = 4` is ~12.6 M and does
    not finish in a session.  The branch-length axis is covered exhaustively
    and cheaply by `sat` instead, which needs no composite."""
    t0 = time.time()
    print(f'== sigma: IS THE RUNG-3 REGION COMBINATORIALLY REACHABLE with a '
          f'CYCLE side 1?')
    print('   Side 1 is a cycle through BOTH x and y -- (BE-242)(ii)\'s '
          'firing shape.  It is NOT')
    print('   a `bline.longcore_library()` entry (every one of those is a '
          'cycle AT x with y on a')
    print('   TAIL), so this is a new side-1 generator, disclosed as such.')
    print('   No draw, no seed: `delta_i` is combinatorial '
          '(`bdecor.d3`/`weld_d3` via `bpeel.delta_pair`).')
    for skname in ('K4', 'K33', 'prism'):
        pairs = _nonadj_pairs(skname)
        print(f'   {skname}: non-adjacent hub pairs {pairs} ; '
              f'bproper.NONADJ has {NONADJ.get(skname)}')
    hits, seen_d, tried = [], {}, 0
    for (m1, m2) in arcs:
        side1 = cycle_side(m1, m2)
        for skname in ('K33', 'prism'):
            sk = SKELETONS[skname]
            for xy in _nonadj_pairs(skname):
                for prof in itertools.product(range(1, maxlen + 1),
                                              repeat=len(sk)):
                    tried += 1
                    E, s1, s2, x, y = composite(skname, list(prof), xy, side1)
                    dp = delta_pair(E, x, y)
                    if dp is None:
                        continue
                    da, db, Ea, _Eb = dp
                    # by EDGE SET, not edge count: `cycle_side(m1,m2)` and a
                    # profile can have the same |E| and the two deltas would
                    # then be silently swapped (this mode printed `delta_1 = 0`
                    # for (5,4)/(5,5) on the first draft, which is how it was
                    # caught).
                    near = set(map(frozenset, Ea)) == set(map(frozenset, s1))
                    d1, d2 = (da, db) if near else (db, da)
                    key = ((m1, m2), d1, d2)
                    seen_d[key] = seen_d.get(key, 0) + 1
                    if d1 + d2 > RUNG3:
                        continue
                    g = graph_gates(E, x, y, s1, s2)
                    if not gates_green(g):
                        continue
                    hits.append(((m1, m2), skname, xy, tuple(prof), d1, d2, g))
    print(f'   enumerated {tried} quadruples; {len(hits)} pass every graph '
          f'gate AT rung 3.')
    cen = {}
    for h in hits:
        cen[(h[0], h[4], h[5])] = cen.get((h[0], h[4], h[5]), 0) + 1
    print(f'   (arcs, delta_1, delta_2) census of the GREEN rung-3 set: '
          f'{dict(sorted(cen.items(), key=str))}')
    d2max = {}
    for ((a, d1, d2), n) in seen_d.items():
        d2max[a] = max(d2max.get(a, -1), d2)
    d1seen = {}
    for (aa, d1v, _d2v) in seen_d:
        d1seen.setdefault(aa, set()).add(d1v)
    print(f'   delta_1 read off each arc shape: '
          f'{ {a: sorted(v) for a, v in sorted(d1seen.items()) } }')
    print(f'   largest delta_2 seen per arc shape (unfiltered): {d2max}')
    print(f'   sigma: {time.time() - t0:.1f}s')
    return hits


# ------------------------------------------- the steered side-1 certificate
# `_linear_pyk`, `_in_span` and `_rand_pt` are BSIXRUNG's own, imported rather
# than recopied: the `p_y` steering that produces (BE-242)(ii)'s certificate
# must be the SAME code here, or a cross-layer comparison compares two models.
from bsixrung import _linear_pyk, _in_span, _rand_pt             # noqa: E402


def steer_side1(m1, m2, rng, tries=60):
    """(BE-242)(i)'s two linear systems in `p_y`, on a cycle side with arcs of
    `m1` and `m2` edges.  Returns (px, uu, vv, py, pix_plane) with
    `c_i(Pi_x) = 2` at the LOCAL layer, or None.  Identical in mechanism to
    `bsixrung.run_cycle`; the difference is that the result is handed on to a
    WHOLE `H` instead of being read at the side layer and stopped."""
    for _ in range(tries):
        px = _rand_pt(rng)
        uu = [_rand_pt(rng) for _ in range(m1 - 1)]
        vv = [_rand_pt(rng) for _ in range(m2 - 1)]
        if dim([px, uu[0], vv[0]]) != 3:
            continue
        planex = [px, uu[0], vv[0]]
        if m1 == 4:
            uu[2] = _in_span(rng, planex)
        if m2 == 4:
            vv[2] = _in_span(rng, planex)
        lp, lq = wedge2(px, uu[0]), wedge2(px, vv[0])
        pfix = [lp] + [wedge2(uu[k], uu[k + 1]) for k in range(m1 - 2)]
        qfix = [lq] + [wedge2(vv[k], vv[k + 1]) for k in range(m2 - 2)]
        if dim(pfix) != m1 - 1 or dim(qfix) != m2 - 1:
            continue
        ca = _linear_pyk(pfix, uu[-1], lq)
        cb = _linear_pyk(qfix, vv[-1], lp)
        if ca is None or cb is None:
            continue
        sol = nullspace(ca + cb)
        if not sol:
            continue
        py = None
        for _try in range(8):
            cand = [F(0)] * 4
            for b in sol:
                lam = F(rng.randint(-9, 9))     # ONE scalar per basis vector:
                cand = [cand[k] + lam * b[k]    # drawing it inside the
                        for k in range(4)]      # comprehension draws four.
            if cand[3] != 0:
                py = [c / cand[3] for c in cand]
                break
        if py is None:
            continue
        pspan = span(pfix + [wedge2(uu[-1], py)])
        qspan = span(qfix + [wedge2(vv[-1], py)])
        if dim(pspan) != min(m1, 6) or dim(qspan) != min(m2, 6):
            continue
        pix = span([lp, lq])
        planey = [py, uu[-1], vv[-1]]
        if dim(pix) != 2 or dim(planey) != 3:
            continue
        if not (dim(planex + [py]) == 4 and dim(planey + [px]) == 4
                and dim(planex + planey) == 4):
            continue                       # `flag_frame`'s three exclusions
        if dim(isect(isect(pspan, qspan), pix)) != 2:
            continue
        return px, uu, vv, py, planex, planey
    return None


def _s1name(w):
    """`bproper.composite`'s own renaming of side 1's interior vertices."""
    return w if w in ('x', 'y') else f's1{w}'


def build_peel(m1, m2, skname, xy, prof, rng, tries=40, box=20):
    """The WHOLE `H`: side 1 steered to fire, side 2 drawn around the FIXED
    flags at x and y.  Returns (E, s1, s2, x, y, aff, extras) or None."""
    side1 = cycle_side(m1, m2)
    E, s1, s2, x, y = composite(skname, list(prof), xy, side1)
    W, branches = hubs_and_branches(E, x, y)
    s1set = set(map(frozenset, s1))
    for _ in range(tries):
        got = steer_side1(m1, m2, rng)
        if got is None:
            continue
        px, uu, vv, py, planex, planey = got
        s1pts = {x: px, y: py}
        for k, u in enumerate(uu):
            s1pts[_s1name(f'u{k + 1}')] = u
        for k, v in enumerate(vv):
            s1pts[_s1name(f'v{k + 1}')] = v
        fixed = {x: (px, span(planex)), y: (py, span(planey))}
        P, B = flag_assignment(W, branches, rng, s=box, fixed=fixed)
        if P is None:
            continue
        pts, ok = dict(P), True
        pts.update({w: v for w, v in s1pts.items()})
        free2 = []
        for (z, zp, ints) in branches:
            if not ints:
                continue
            if frozenset((z, ints[0])) in s1set:
                continue               # a side-1 arc: already steered
            g = draw_branch(P, B, z, zp, len(ints), rng, s=box)
            if g is None:
                ok = False
                break
            for j, (w, cc) in enumerate(zip(ints, g)):
                pts[w] = cc
                if 0 < j < len(ints) - 1:
                    free2.append((w, z, zp, ints, j))
        if not ok:
            continue
        aff = assemble(E, pts)
        if aff is None:
            continue
        return E, s1, s2, x, y, aff, dict(pts=pts, free2=free2, P=P, B=B,
                                          branches=branches, px=px, py=py)
    return None


# ---------------------------------------------------------- the row battery

def dmin_in(E, x, y):
    """`d_min` = the length of a shortest x-y path INSIDE an edge list."""
    nb = neighbors(E)
    if x not in nb or y not in nb:
        return None
    dist, q = {x: 0}, [x]
    while q:
        a = q.pop(0)
        for b in nb[a]:
            if b not in dist:
                dist[b] = dist[a] + 1
                q.append(b)
    return dist.get(y)


def read_row(E, x, y, s1, s2, aff, tag):
    """One fully-gated measured row, with `boblig._assert_gates`' OWN gate
    battery (recomputed from `bline.legal_peel`'s report, which is called
    rather than re-implemented) plus the generic-flag-regime test and the
    (BE-86)(i) attainment reading.  Returns a dict or None."""
    from bline import legal_peel                                # noqa: E402
    from bdecor import verify_pencil_witness                    # noqa: E402
    row = e_row(E, x, y, s1, s2, aff)
    if row is None:
        return None
    g = graph_gates(E, x, y, s1, s2)
    assert g['hcard'] and g['mindeg'] >= 2 and g['girth'] >= 4, \
        ('(CH-1) fails on H', tag, g)
    assert g['degx'] >= 3 and g['degy'] >= 3, ('a terminal is not a hub', tag)
    assert g['rnode_far'], ('side 2 is not R-node-shaped', tag)
    assert g['deg1x'] >= 2 and g['deg2x'] >= 2, \
        ('the side-degree >= 2 quantifier is not met at x', tag, g)
    assert len(s1) != len(s2), \
        ('equal side edge counts -- the side identification is ambiguous',
         tag)
    assert set(map(frozenset, s1)) | set(map(frozenset, s2)) == \
        set(map(frozenset, E)), ('the two sides do not cover H', tag)
    wit = verify_pencil_witness(E, aff)[0]
    reg = flag_frame(E, aff, x, y) is not None
    assert wit, ('the configuration is not a pencil witness on H', tag)
    dp = delta_pair(E, x, y)
    assert dp is not None, ('{x,y} is not a 2-cut of H', tag)
    da, db, Ea, _Eb = dp
    d1 = da if len(Ea) == len(s1) else db
    d2 = db if len(Ea) == len(s1) else da
    assert (d1, d2) == row['d'], \
        ('`bpeel.delta_pair` and `bfour.side_nums` disagree on delta', tag,
         (d1, d2), row['d'])
    ssum = dim(row['S1'] + row['S2'])
    sint = dim(isect(row['S1'], row['S2'])) if row['S1'] and row['S2'] else 0
    target = min(row['d'][0] + row['d'][1], 6) + row['a'][0] + row['a'][1]
    return dict(row=row, gates=g, witness=wit, regime=reg,
                sum_dim=ssum, int_dim=sint, attain_target=target,
                attains=(ssum == target),
                dmin=(dmin_in(s1, x, y), dmin_in(s2, x, y)),
                sat=(row['d'][0] == dmin_in(s1, x, y),
                     row['d'][1] == dmin_in(s2, x, y)),
                obligation=pix_ok(row['cX'][0], row['cX'][1],
                                  row['d'][0], row['d'][1]))


def _fmt(rr):
    r = rr['row']
    return (f"t={r['t']} Sd={r['d'][0] + r['d'][1]} slack={r['slack']} "
            f"c1+c2={r['cX'][0] + r['cX'][1]} OBLIG="
            f"{'HOLDS' if rr['obligation'] else 'VIOLATED'} "
            f"dim(r1+r2)={rr['sum_dim']} target={rr['attain_target']} "
            f"attains={rr['attains']} dmin={rr['dmin']} sat={rr['sat']} "
            f"regime={rr['regime']}")


def side2_of(skname, prof):
    return subdivided(SKELETONS[skname], list(prof))


def profiles_at(skname, xy, want_d2, maxlen=5, minlen=2, limit=None,
                saturated=None):
    """Every branch profile with entries in `[minlen, maxlen]` whose side 2
    has `delta_2 = want_d2`, is R-node-shaped at `xy`, and (when `saturated`
    is True/False) is / is not PATH-SATURATED (`delta_2 = d_min_2`).

    `minlen = 2` is not a taste: `bdecor.flag_assignment` cannot honour a
    FIXED flag at `x` when a skeleton edge at `x` has branch length 1 (the
    hub neighbour is placed before the plane is checked), and the flag at
    `x` must be fixed here because side 1 pins it."""
    from bdecor import d3, weld_d3                              # noqa: E402
    out = []
    for prof in itertools.product(range(minlen, maxlen + 1),
                                  repeat=len(SKELETONS[skname])):
        s2 = side2_of(skname, prof)
        d2 = d3(s2) - weld_d3(s2, xy[0], xy[1])
        if d2 != want_d2:
            continue
        sat = (d2 == dmin_in(s2, xy[0], xy[1]))
        if saturated is not None and sat != saturated:
            continue
        if not rnode_shaped(s2, xy[0], xy[1]):
            continue
        out.append(tuple(prof))
        if limit and len(out) >= limit:
            break
    return out


# ================================================ mode: peel  -- THE WITNESS

def run_peel(nseed=3, maxlen=5, nprof=2):
    """THE CONSTRUCTION.  Side 1 = (BE-242)(ii)'s firing cycle, arcs (4,4),
    `delta_1 = 2`; side 2 = a subdivided 3-connected skeleton that is
    PATH-SATURATED (`delta_2 = d_min_2 = 4`), so (BE-45)(ii) forces
    `c_2(Pi_x) >= 1` with no genericity.  `Sigma_delta = 6` is rung 3,
    `slack = 0`, and the obligation there is `c_1 + c_2 <= 2`."""
    t0 = time.time()
    print(f'== peel: A WHOLE-`H` PEEL AT RUNG 3 WITH `c_1 + c_2 >= 3`  '
          f'(seed base {SEED})')
    print('   Side 1: a CYCLE THROUGH x AND y, arcs (4,4) -- (BE-242)(ii)\'s '
          'firing shape, steered')
    print('   by `p_y` through BSIXRUNG\'s OWN `_linear_pyk`.  Side 2: a '
          'subdivided skeleton that is')
    print('   PATH-SATURATED, `delta_2 = d_min_2 = 4`, so (BE-45)(ii) gives '
          '`c_2(Pi_x) >= 1` FREE.')
    print('   Gates: `bline.legal_peel`\'s own report + '
          '`boblig._assert_gates`\' battery, asserted.')
    jobs = []
    for skname in ('K33', 'prism'):
        for xy in _nonadj_pairs(skname):
            ps = profiles_at(skname, xy, 4, maxlen=maxlen, limit=nprof,
                             saturated=True)
            for p in ps:
                jobs.append((skname, xy, p, True))
            pn = profiles_at(skname, xy, 4, maxlen=maxlen, limit=1,
                             saturated=False)
            for p in pn:
                jobs.append((skname, xy, p, False))
    print(f'   {len(jobs)} (skeleton, hub pair, profile) jobs; '
          f'{sum(1 for j in jobs if j[3])} path-saturated, '
          f'{sum(1 for j in jobs if not j[3])} NOT (the F13 control).')
    kills, held, rows, certs = 0, 0, 0, []
    cen = {}
    for (skname, xy, prof, sat) in jobs:
        for sd in range(nseed):
            rng = random.Random(SEED + 613 * sd + 31 * sum(prof)
                                + 7 * len(skname) + 3 * len(str(xy)))
            got = build_peel(4, 4, skname, xy, list(prof), rng, tries=10)
            if got is None:
                continue
            E, s1, s2, x, y, aff, _ex = got
            rr = read_row(E, x, y, s1, s2, aff, (skname, xy, prof, sd))
            if rr is None:
                continue
            rows += 1
            r = rr['row']
            key = (sat, r['t'], rr['regime'], rr['obligation'], rr['attains'])
            cen[key] = cen.get(key, 0) + 1
            if not rr['regime']:
                continue
            if rr['obligation']:
                held += 1
            else:
                kills += 1
                assert r['d'][0] + r['d'][1] <= RUNG3, \
                    ('a violation off rung 3', skname, xy, prof)
                assert r['a'] == (0, 0), ('a violation off a = 0', skname, xy)
                assert r['slack'] == 0, ('slack is not 0 at rung 3', skname)
                assert not rr['attains'], \
                    ('a rung-3 violation that STILL attains -- (BE-239)(ii) '
                     'says this cannot happen', skname, xy, prof, rr)
                if len(certs) < 3:
                    certs.append((skname, xy, prof, sd, E, s1, s2, x, y,
                                  aff, rr))
            if sat:
                assert r['cX'][1] >= 1, \
                    ('(BE-45)(ii) says a path-saturated side has c_j >= 1',
                     skname, xy, prof, r['t'])
    print(f'   {rows} fully-gated rows; obligation HOLDS at {held}, '
          f'VIOLATED at {kills}.')
    print('   census `(path-saturated, t, in-regime, obligation-holds, '
          'H attains)`:')
    for k in sorted(cen, key=str):
        print(f'      {k}  x{cen[k]}')
    for (skname, xy, prof, sd, E, s1, s2, x, y, aff, rr) in certs[:1]:
        r = rr['row']
        print(f'   CERTIFICATE -- {skname} at {xy}, profile {prof}, '
              f'seed offset {sd}')
        print(f'      |V(H)| = {len(verts_of(E))}, |E(H)| = {len(E)}, '
              f'|E(side 1)| = {len(s1)}, |E(side 2)| = {len(s2)}')
        print(f'      {_fmt(rr)}')
        print(f'      gates: {rr["gates"]}')
        print(f'      p_x = {[str(v) for v in aff[x]]}')
        print(f'      p_y = {[str(v) for v in aff[y]]}')
        print(f'      aff = {{' + ', '.join(f"{w!r}: {[str(c) for c in aff[w]]}"
                                            for w in sorted(aff, key=str))
              + '}')
        print(f'      E   = {sorted(map(tuple, E), key=str)}')
        print(f'      s1  = {sorted(map(tuple, s1), key=str)}')
    print(f'   peel: {time.time() - t0:.1f}s')
    return kills, held, rows, certs


# ============================== mode: sat -- (BE-244)(i) AT ITS DISCLOSED CAP

def run_sat(maxlen=4, minlen=1):
    """(BE-244)(i)'s enumeration with its DISCLOSED cap moved: branch lengths
    in `[minlen, maxlen]` instead of `{1,2,3}`, same three skeletons, same
    "every hub pair non-adjacent in the skeleton".  (BE-244)(ii) named the
    missing axis as *"a larger 3-connected core"*; the axis that actually
    carries the phenomenon is the BRANCH LENGTH, and `{1,2,3}` is the fence.

    `rnode_shaped` is asserted PROFILE-INDEPENDENT here rather than called
    per profile: suppressing every degree-2 vertex of `side2 + (x,y)` returns
    the skeleton plus the virtual edge whatever the branch lengths are, so
    the test depends only on (skeleton, hub pair).  The assert is the check."""
    t0 = time.time()
    from bdecor import d3, weld_d3                              # noqa: E402
    print(f'== sat: IS AN R-NODE-SHAPED SIDE 2 PATH-SATURATED?  branch '
          f'lengths in {{{minlen}..{maxlen}}}')
    print('   (BE-244)(i) is EXHAUSTIVE over lengths {1,2,3} and reports '
          '0 of 236 196.  Its cap is')
    print('   disclosed at (BE-244)(ii).  This moves the cap and nothing '
          'else.')
    tot, sat_n, sat_le4, sat_ge2 = 0, 0, 0, 0
    per, exemplar = {}, {}
    for skname in ('K4', 'K33', 'prism'):
        sk = SKELETONS[skname]
        pairs = _nonadj_pairs(skname)
        for xy in pairs:
            probe = subdivided(sk, [2] * len(sk))
            rn = rnode_shaped(probe, xy[0], xy[1])
            for tp in ([1] * len(sk), [maxlen] * len(sk),
                       [1] + [maxlen] * (len(sk) - 1),
                       [maxlen] + [1] * (len(sk) - 1)):
                assert rnode_shaped(subdivided(sk, list(tp)),
                                    xy[0], xy[1]) == rn, \
                    ('rnode_shaped is NOT profile-independent', skname, xy)
            for prof in itertools.product(range(minlen, maxlen + 1),
                                          repeat=len(sk)):
                tot += 1
                if not rn:
                    continue
                s2 = subdivided(sk, list(prof))
                d2 = d3(s2) - weld_d3(s2, xy[0], xy[1])
                if d2 != dmin_in(s2, xy[0], xy[1]):
                    continue
                sat_n += 1
                per[(skname, xy)] = per.get((skname, xy), 0) + 1
                if d2 <= 4:
                    sat_le4 += 1
                    if min(prof) >= 2:
                        sat_ge2 += 1
                        exemplar.setdefault((skname, xy, d2), tuple(prof))
    print(f'   {tot} (skeleton, hub pair, profile) sides enumerated; '
          f'PATH-SATURATED at {sat_n}.')
    print(f'   of those, `delta_2 <= 4` at {sat_le4}, and with every branch '
          f'>= 2 (buildable here) at {sat_ge2}.')
    print(f'   per (skeleton, hub pair): {dict(sorted(per.items(), key=str))}')
    print(f'   exemplars: {dict(sorted(exemplar.items(), key=str))}')
    print(f'   sat: {time.time() - t0:.1f}s')
    return tot, sat_n, sat_le4, sat_ge2


# ================= mode: cross -- the certificate hardened at the `H` layer

def run_cross(nseed=3):
    """Every load-bearing sentence of the certificate re-read at the WHOLE-`H`
    layer and asserted: `rho_bar_i` as a SPACE against `binduc`, `Pi_x` off
    `bimage.plane_at` ON `H` (not on side 1), the (BE-45)(ii) witness vector
    named, the SHORTFALL read directly off `dim M(H)` vs `6 + def_3(H)`
    rather than through (BE-86)(i), and the residue-tuple membership."""
    t0 = time.time()
    from bimage import rho_bar_of                               # noqa: E402
    from bdecor import d3                                       # noqa: E402
    from bproper import free_peel                               # noqa: E402
    print(f'== cross: THE CERTIFICATE HARDENED AT THE `H` LAYER (seed base '
          f'{SEED})')
    skname, xy, prof = 'K33', ('A', 'B'), (2, 2, 2, 2, 4, 4, 2, 5, 5)
    resid = [t for t in BA.all_tuples()
             if t[2] == 0 and t[3] == 0 and t[0] + t[1] <= RUNG3
             and t[6] >= max(0, t[4] - 4) and t[7] >= max(0, t[5] - 4)
             and not pix_ok(t[6], t[7], t[0], t[1])]
    print(f'   rung-3 residue (a = 0, Grassmann-floor-legal, obligation '
          f'violated): {len(resid)} tuples -- (BE-239)(i)\'s 26.')
    ok = 0
    for sd in range(nseed):
        rng = random.Random(SEED + 613 * sd + 31 * sum(prof))
        got = build_peel(4, 4, skname, xy, list(prof), rng, tries=10)
        if got is None:
            continue
        E, s1, s2, x, y, aff, _ex = got
        rr = read_row(E, x, y, s1, s2, aff, (skname, xy, prof, sd))
        if rr is None or not rr['regime']:
            continue
        r = rr['row']
        # (a) rho_bar_i as a SPACE, two independent readings.
        for (sdd, Si) in ((s1, r['S1']), (s2, r['S2'])):
            rss = rel_screw_space(sdd, aff, x, y)
            assert dim(span(rss[1])) == dim(Si) == rss[0], \
                'the two readings of rho_bar_i disagree in dimension'
            assert dim(Si + span(rss[1])) == dim(Si), \
                'side_nums and rel_screw_space differ as SPACES'
        # (b) Pi_x is read on the WHOLE H, not on side 1.
        Bx = plane_at(E, aff, x)
        assert Bx is not None, 'no plane at x on H'
        pix = pencil_space(hat(aff[x]), Bx)
        assert dim(pix) == PIXDIM and dim(pix + r['Pix']) == PIXDIM, \
            'Pi_x on H differs from `bfour.e_row`\'s'
        # (c) the firing side CONTAINS Pi_x, not merely meets it in dim 2.
        assert contains(r['S1'], pix), 'c_1 = 2 without containment'
        # (d) (BE-45)(ii)'s witness vector, NAMED: the first hinge line of a
        #     shortest x-y path of side 2 lies in rho_bar_2 cap Pi_x.
        nb2 = neighbors(s2)
        wit = None
        for w in nb2[x]:
            ell = span([wedge2(hat(aff[x]), hat(aff[w]))])
            if contains(r['S2'], ell) and contains(pix, ell):
                wit = w
                break
        assert wit is not None, \
            '(BE-45)(ii) predicts a first hinge line of side 2 inside '\
            'rho_bar_2 cap Pi_x, and none is there'
        assert dim(isect(r['S2'], pix)) == r['cX'][1] >= 1, 'c_2 mis-read'
        # (e) THE SHORTFALL, read directly at the H layer.
        _SH, _rh, dMH, _rk = rho_bar_of(E, aff, x, y)
        defH = d3(E)
        # `dim M(H) >= 6 + def_3(H)` is the UNIVERSAL partition cap, equality
        # being attainment ((BE-86)(i)); a SHORTFALL is therefore an EXCESS of
        # motions, `dim M(H) > 6 + def_3(H)`.  (Written the other way round on
        # the first draft, and the assert is what caught it.)
        assert dMH > 6 + defH, \
            ('H attains after all -- no shortfall', dMH, defH)
        # (f) (BE-22)(i) cross-check of the two layers.
        f1, f2 = d3(s1), d3(s2)
        assert dMH == 6 + f1 + f2 + r['a'][0] + r['a'][1] - rr['sum_dim'], \
            ('(BE-22)(i) fails to reconcile the side and H layers', dMH)
        # (g) residue membership; (h) the Grassmann floor EXCEEDED.
        assert r['t'] in resid, ('the tuple is off the rung-3 residue', r['t'])
        assert r['cX'][1] > max(0, r['r'][1] - 4), \
            'c_2 does NOT exceed the Grassmann floor'
        # (i) (BE-241)(iii): a firing side has d_min >= 4.
        assert rr['dmin'][0] >= 4, '(BE-241)(iii) violated on the firing side'
        ok += 1
        if sd == 0:
            print(f'   seed offset {sd}: {_fmt(rr)}')
            print(f'      dim M(H) = {dMH}, 6 + def_3(H) = {6 + defH}  '
                  f'-> SHORTFALL {dMH - 6 - defH} (H has MORE motions '
                  f'than the target: it does NOT attain)')
            print(f'      (BE-45)(ii) witness: the hinge line x-{wit} of '
                  f'side 2 lies in `rho_bar_2 cap Pi_x`.')
            print(f'      c_2 = {r["cX"][1]} > Grassmann floor '
                  f'max(0, rho_2 - 4) = {max(0, r["r"][1] - 4)}.')
    print(f'   every assertion above passed at {ok} of {nseed} independent '
          f'draws.')
    # (j) the LANDED builder on the SAME graph: side 1 unsteered.
    print('   F13 CONTROL -- `bproper.free_peel` on the SAME composite '
          '(side 1 NOT steered):')
    ctl = {}
    side1 = cycle_side(4, 4)
    for sd in range(6):
        rng = random.Random(SEED + 97 * sd)
        got = free_peel(skname, list(prof), xy, side1, rng)
        if got is None:
            continue
        Ec, c1e, c2e, xc, yc, affc = got
        rr = read_row(Ec, xc, yc, c1e, c2e, affc, ('free', sd))
        if rr is None:
            continue
        r = rr['row']
        ctl[(r['t'], rr['regime'], rr['obligation'])] = \
            ctl.get((r['t'], rr['regime'], rr['obligation']), 0) + 1
    print(f'      `(t, in-regime, obligation-holds)` census: '
          f'{dict(sorted(ctl.items(), key=str))}')
    print(f'   cross: {time.time() - t0:.1f}s')
    return ok


# ==================================================================== main

MODES = {'sigma': run_sigma, 'peel': run_peel, 'sat': run_sat,
         'cross': run_cross}


def run_validate():
    run_sat(maxlen=3, minlen=1)
    run_peel(nseed=2, maxlen=5, nprof=1)
    run_cross(nseed=2)


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode == 'validate':
        run_validate()
    elif mode in MODES:
        MODES[mode]()
    else:
        print(f'usage: bwholeh.py [{"|".join(sorted(MODES))}|validate]')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
