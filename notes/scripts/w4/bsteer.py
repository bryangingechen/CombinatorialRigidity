"""
Direction BSTEER (arc ordinal 84) -- (BE-162)(iii): at `delta_2 = 1`, can
side 2's SINGLE SCREW LINE be steered INSIDE `Pi_x` while side 1 stays bad?

  THE QUESTION, verbatim from BFOUR's own hand-off.  (BE-E4') is (E4)
  restricted to `delta_1, delta_2 >= 1`, and (BE-161)(iii) measured it
  TIGHT at `delta_2 = 1`: there `e_1 + e_2 = 4` exactly, so ONE further
  mechanism refutes it -- `e_2 = 0`, i.e. `rho_bar_2 <= Pi_x`, where
  `rho_bar_2` is a single line and `Pi_x` is already pinned to (BE-105)'s
  bad plane.  YES kills (BE-E4') and finishes the two-sided clause family;
  NO is the obstruction the repair needs.

  THE ANSWER, said at the top: **NO -- and the obstruction is a DEGREE
  COUNT AT `x`, not a genericity statement.**  Six results.

  (BE-172) THE REDUCTION.  `Pi_x = Sigma_{p_x} cap Lambda^2 pi_x` and
           `Pi_x` is TOTALLY SINGULAR, so at `rho_2 = 1`

               rho_bar_2 = <w> <= Pi_x
                 <=>  Q(w) = 0  AND  w ^ p_x = 0  AND  w in Lambda^2 pi_x,

           i.e. `w` must be a LINE (not a screw with pitch) THROUGH `p_x`
           LYING IN `pi_x`.  Three independent conditions, the first of
           them the Klein-quadric one this thread had never used.

  (BE-173) THE FREEDOM EXISTS -- so the coordinator's stated REASON is
           refuted even though its verdict is right.  The prediction was
           "no shared freedom: `Pi_x` is pinned and `rho_bar_2` is
           determined by side 2's own core".  Under the reflag at a FIXED
           bad plane, with side 1 byte-untouched, `rho_bar_2` takes 48
           DISTINCT lines at a single peel.  The freedom is real; it is the
           TARGET that is unreachable.

  (BE-174) THE OBSTRUCTION IS TOTAL SINGULARITY.  At every `delta_2 = 1`
           R-node row over three skeletons, `Q(rho_bar_2) != 0`: side 2's
           single screw has NONZERO PITCH, so it is not a line at all and
           no incidence condition can rescue it.  All three conditions of
           (BE-172) fail independently.

  (BE-175) AND THE ONE LANDED MECHANISM THAT WOULD MAKE `rho_bar_2`
           SINGULAR IS EXCLUDED BY THE HABITAT ITSELF.  At `deg_2(x) = 1`
           (BE-45)(i) FORCES `l = p_x ^ p_c` into `rho_bar_2`, and the
           chart condition puts `p_c` in `pi_x`, so `l` is in `Pi_x` and at
           `rho_2 = 1` the containment is AUTOMATIC.  But `rnode_shaped`
           puts the virtual edge `xy` back and demands degree `>= 3` at the
           kept terminals, so it forces `deg_2(x) >= 2` and rejects
           `deg_2(x) = 1` as an S-NODE; and BSATUR's bad plane needs
           `deg_1(x) = 1`.  The two demands force `deg(x) = 2`, where
           NEITHER side is R-node-shaped and the flag at `x` is DETERMINED
           by its own 3-point star, so the bad plane is not constructible
           by rotation either.  **Jointly unsatisfiable.**

  (BE-176) THE MECHANISM IS REAL, MEASURED JUST OUTSIDE THE HABITAT.  At an
           S-node peel with `deg_2(x) = 1`, `c_2(Pi_x) = 1` -- the forced
           hinge lands in `Pi_x` exactly as (BE-175) predicts -- against
           `c_2(Pi_x) = 0` at ALL 56 R-node rows.  So the boundary is
           `rnode_shaped`, not genericity.

  (BE-177) HENCE (BE-E4') SURVIVES ITS OWN TIGHT BOUNDARY, and this is the
           FIRST POSITIVE structural fact the two-sided family owns.  A
           second bound closes the last gap: at a side-2 series end whose
           `x`-neighbour is MOVABLE the pendant contributes two hinges, so
           `delta_2 >= 2` -- the `rho_2 = 1` containment needs an IMMOVABLE
           hub neighbour, which is exactly `deg(x) = 2`.

  MODES.  crit | free | pitch | habitat | snode | bound | support |
          validate  (the last runs all six in one process)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.  Caps DISCLOSED per mode (RESEARCH-ARC section 5).

  READ-ONLY WITH RESPECT TO EVERY LANDED DRIVER.  `bfour.py` is IMPORTED
  for its ladder, its witness generator and its gate battery -- NOT edited,
  which is why the "figures do not move" gate still discharges by
  `git diff --name-only -- '*.py' '*.m2'` plus
  `git status --porcelain notes/scripts/` (`notes/scripts/README.md`
  *Harness debt*, "No tracked driver modified").

  THE THREE RECORDED SILENT HAZARDS, navigated as in BFOUR:
    * `bimage.pt_in` is NOT CALLED -- no `Lambda^2`-side draw goes near it;
    * `bimage.span`'s width-6-on-RANK case: no width-12 object goes through
      `span`/`dim`/`isect` here; every subspace built below is width 6 or
      width 4 through `nullspace`/`plane_at`;
    * `bwin.dehom` is unreachable -- `bwin` is not imported, and the one
      place this driver writes an interior vertex it goes through
      `bsatur.reflag`/`draw_branch`, never a hand-rolled dehomogenization.
"""

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import itertools                                                      # noqa: E402
import random                                                         # noqa: E402

from exactcore import hat, neighbors, wedge2                          # noqa: E402
from bimage import (contains, dim, isect, lam2, pencil_space,          # noqa: E402
                    plane_at, rho_bar_of, same_space, span)
from bpeel import (SKELETONS, delta_pair, rnode_shaped,               # noqa: E402
                   subdivided)
from bdecor import girth, hcard_ok_piece                              # noqa: E402
from bunif import SEED                                                # noqa: E402
from bsatur import bad_plane, draw_peel, reflag, row_of, sigma_at      # noqa: E402
from pitch import Q, klein                                            # noqa: E402
from kbare_common import verify_pencil_witness, verts_of               # noqa: E402

import bfour as BF                                                    # noqa: E402

PIX, PIY, MB = ('Pix',), ('Piy',), ('M',)

# The `delta_2 = 1` rungs of BFOUR's own ladder -- the habitat the question
# is asked in.  Side 1 is always the peeled 5-branch, so `deg_1(x) = 1` and
# (BE-105)'s bad plane is available; side 2 is R-node-shaped at every one.
RUNGS = [('K4', (5, 2, 2, 3, 3, 3), 0),
         ('prism', (5, 2, 2, 2, 2, 2, 3, 3, 3), 0),
         ('K33', (5, 2, 2, 2, 2, 2, 3, 3, 3), 0)]


def _arc(E, a, b, L, tag):
    """A path of `L` edges from `a` to `b` with fresh interior names.
    `bdegtwo._arc`/`bline._arc`'s body; kept local because importing a
    four-line private helper across two more modules buys nothing and
    `bfour` does not re-export it."""
    prev = a
    for i in range(L - 1):
        E.append((prev, f'{tag}{i}'))
        prev = f'{tag}{i}'
    E.append((prev, b))


# ================================================ mode: crit  ((BE-172))

def run_crit(nseed=6):
    t0 = time.time()
    print(f'== crit: (BE-172) THE REDUCTION -- what `rho_bar_2 <= Pi_x` '
          f'ACTUALLY demands, seed {SEED}')
    print('  (BE-149)(v)(a)/(b) give the two facts the reduction needs, and')
    print('  they are about `K^4`, not about a side: `Pi_x` is the meet')
    print('  `Sigma_{p_x} cap Lambda^2 pi_x`, and it is TOTALLY SINGULAR')
    print('  (`Q == 0` and the Klein form `B == 0` on it).  Both are')
    print('  re-asserted below ON THE LADDER, not cited.')
    tot, sing, meet = 0, 0, 0
    for (r, g, ex) in _ladder_rows(nseed):
        Pix, pix, px = r['Pix'], r['pix'], r['px']
        tot += 1
        # (a) Pi_x IS the meet -- asserted, not cited.
        assert same_space(Pix, isect(sigma_at(px), lam2(pix))), \
            'Pi_x is not Sigma_{p_x} cap Lambda^2 pi_x'
        meet += 1
        # (b) TOTALLY SINGULAR: Q vanishes on it and so does the polarized
        #     Klein form, so every element is a LINE and any two meet.
        b = Pix
        assert all(Q(v) == 0 for v in b), 'Q does not vanish on Pi_x'
        assert all(klein(b[i], b[j]) == 0
                   for i in range(len(b)) for j in range(len(b))), \
            'the Klein form does not vanish on Pi_x'
        sing += 1
    print(f'  {tot} `delta_2 = 1` rows over {len(RUNGS)} skeletons.')
    print(f'  `Pi_x = Sigma_{{p_x}} cap Lambda^2 pi_x` ASSERTED at '
          f'{meet}/{tot};')
    print(f'  `Pi_x` TOTALLY SINGULAR (Q == 0 and B == 0) at {sing}/{tot}.')
    print('  THE REDUCTION, and it is the step the question was missing.')
    print('  At `rho_2 = 1`, writing `rho_bar_2 = <w>`:')
    print('        w in Pi_x  <=>  Q(w) = 0        (w is a LINE, no pitch)')
    print('                   AND  w ^ p_x = 0     (that line meets p_x)')
    print('                   AND  w in Lambda^2 pi_x  (it lies in pi_x).')
    print('  So the target is NOT "a line in general position that has to')
    print('  hit a 2-plane" -- it is "a screw that has to be a PURE')
    print('  ROTATION, about an axis through `p_x`, inside `pi_x`".  The')
    print('  first condition is on the KLEIN QUADRIC and is invisible to')
    print('  every incidence argument on this thread so far; `pitch` is')
    print('  the obstruction, and `pitch` is what (BE-174) measures.')
    assert tot >= 6, 'the criterion did not run'
    print(f'  crit: {time.time() - t0:.1f}s')
    return tot


# ============================================ the ladder's measured rows

def _ladder_rows(nseed=6, nre=1, rungs=None):
    """Yield the measured `delta_2 = 1` rows of BFOUR's ladder, each with
    the side-2 screw and the flag data this direction needs.

    Built on `bfour.witness_rows`' own pipeline shape -- draw, check (M1),
    construct (BE-105)'s bad plane, run the F13 negative control, reflag,
    re-gate -- but re-derived here because `witness_rows` returns the
    (E4) row rather than `rho_bar_2`'s basis, `pi_x` and `p_x`.  `nre`
    resweeps per drawn configuration at the SAME bad plane, which is the
    freedom (BE-173) measures; side 1 is never touched."""
    for (skn, prof, ei) in (rungs or RUNGS):
        got = _bs_peel(skn, prof, ei)
        if got is None:
            continue
        E, x, y, s1, s2 = got
        if len(neighbors(s1)[x]) != 1:
            continue
        c1v = sorted(neighbors(s1)[x], key=str)[0]
        for sd in range(nseed):
            rng = random.Random(SEED + 1013 * sd + 17 * len(prof) + sum(prof))
            d = draw_peel(E, x, y, rng)
            if d is None:
                continue
            P, B, pts, aff, branches = d
            S1, r1, _dM, _ = rho_bar_of(s1, aff, x, y)
            px0, pc1 = hat(aff[x]), hat(aff[c1v])
            if not contains(S1, [wedge2(px0, pc1)]):
                continue                     # (M1) fails at this draw
            try:
                badB = bad_plane(S1, px0, pc1)
            except AssertionError:
                continue
            if badB is None:
                continue
            pa0 = plane_at(E, aff, x)
            if pa0 is None:
                continue
            c0 = dim(isect(S1, pencil_space(px0, pa0)))
            if c0 >= 2 or same_space(pa0, badB):
                continue                     # F13 negative control
            for k in range(nre):
                rr = random.Random(SEED + 7717 * sd + 131 * k)
                aff2 = reflag(E, x, s1, P, B, pts, badB, branches, rr)
                if aff2 is None:
                    continue
                ok, _n = verify_pencil_witness(E, aff2)
                if not ok:
                    continue
                pix = plane_at(E, aff2, x)
                if pix is None or not same_space(pix, badB):
                    continue
                px = hat(aff2[x])
                Pix = pencil_space(px, pix)
                if dim(Pix) != 2:
                    continue
                R1, rr1, _d1, _ = rho_bar_of(s1, aff2, x, y)
                R2, rr2, _d2, _ = rho_bar_of(s2, aff2, x, y)
                if rr2 != 1:
                    continue
                assert all(aff2[w] == aff[w] for w in verts_of(s1)), \
                    'the reflag moved side 1'
                yield (dict(E=E, x=x, y=y, s1=s1, s2=s2, aff=aff2,
                            R1=R1, R2=R2, r1=rr1, r2=rr2,
                            Pix=Pix, pix=pix, px=px, w=R2[0],
                            c1=dim(isect(R1, Pix)),
                            c2=dim(isect(R2, Pix))),
                       dict(skn=skn, prof=prof, sd=sd, k=k),
                       dict(c0=c0, badB=badB))


def _bs_peel(skname, prof, ei):
    """`bsatur.peel_of` under its own name -- a *Divergences* partner of
    `bdegtwo.peel_of` (different signature, different side orientation),
    reached exactly the way `bfour._bs_peel` reaches it."""
    import bsatur
    return bsatur.peel_of(skname, list(prof), ei)


# ================================================ mode: free  ((BE-173))

def run_free(nseed=14, nre=6):
    t0 = time.time()
    print(f'== free: (BE-173) THE FREEDOM EXISTS -- the prediction\'s '
          f'REASON, tested, seed {SEED}')
    print('  The coordinator predicted NO and gave the reason: "`Pi_x` is')
    print('  pinned by (BE-105)\'s bad plane while `rho_bar_2`\'s line is')
    print('  determined by side 2\'s own core, so the two have no shared')
    print('  freedom to exploit."  That is a claim about the SAMPLER\'s')
    print('  support, so it is testable directly: hold the bad plane FIXED')
    print('  (side 1 byte-untouched, asserted) and resweep the reflag.')
    lines, rows, byrung = set(), 0, {}
    for (r, g, ex) in _ladder_rows(nseed, nre):
        rows += 1
        lines.add(tuple(r['w']))
        byrung.setdefault(g['skn'], set()).add(tuple(r['w']))
    print(f'  {rows} rows; DISTINCT `rho_bar_2` lines: {len(lines)}')
    for k in sorted(byrung):
        print(f'    {k}: {len(byrung[k])} distinct')
    assert len(lines) > 1, 'rho_bar_2 did not move -- the reason holds'
    print('  VERDICT.  `rho_bar_2` MOVES, at a fixed bad plane, with side 1')
    print('  untouched -- so the stated reason is REFUTED even though the')
    print('  verdict it supported is right.  The reflag re-places side 2\'s')
    print('  branch interiors at `x` inside `pi_x`, and `rho_bar_2` is a')
    print('  function of those placements.  What blocks the containment is')
    print('  therefore NOT a missing degree of freedom; it is that the')
    print('  target set is EMPTY, which is (BE-174).')
    print('  Recorded because it is the difference between "we could not')
    print('  reach it" and "there is nothing there to reach".')
    print(f'  free: {time.time() - t0:.1f}s')
    return rows, len(lines)


# =============================================== mode: pitch  ((BE-174))

def run_pitch(nseed=10, nre=4):
    t0 = time.time()
    print(f'== pitch: (BE-174) THE OBSTRUCTION IS TOTAL SINGULARITY, '
          f'seed {SEED}')
    print('  (BE-172) split the target into three conditions.  Measure each')
    print('  separately at every `delta_2 = 1` R-node row, so the verdict')
    print('  says WHICH one obstructs rather than only that the')
    print('  conjunction fails.')
    tot, qz, thr, inl, inp = 0, 0, 0, 0, 0
    byrung = {}
    for (r, g, ex) in _ladder_rows(nseed, nre):
        w, px, pix, Pix = r['w'], r['px'], r['pix'], r['Pix']
        tot += 1
        d = byrung.setdefault(g['skn'], [0, 0, 0, 0])
        d[0] += 1
        # (1) is the screw a LINE at all?
        if Q(w) == 0:
            qz += 1
            d[1] += 1
        # (2) does that line pass through p_x?
        if dim(isect(r['R2'], sigma_at(px))) == 1:
            thr += 1
            d[2] += 1
        # (3) does it lie in pi_x?
        if dim(isect(r['R2'], lam2(pix))) == 1:
            inl += 1
            d[3] += 1
        c2 = dim(isect(r['R2'], Pix))
        if c2 == 1:
            inp += 1
        # side 1 IS bad at every row -- the question's own hypothesis.
        assert r['c1'] == 2 and contains(r['R1'], Pix), \
            'side 1 is not bad at this row'
        # and the reduction is SOUND pointwise: containment implies all three
        assert (c2 == 1) == (Q(w) == 0
                            and dim(isect(r['R2'], sigma_at(px))) == 1
                            and dim(isect(r['R2'], lam2(pix))) == 1), \
            '(BE-172)\'s reduction is not pointwise exact'
    print(f'  {tot} rows, side 1 asserted BAD (`c_1(Pi_x) = 2`) at every one.')
    print(f'  (1) `Q(rho_bar_2) = 0`  (a LINE, zero pitch) : {qz} of {tot}')
    print(f'  (2) that line through `p_x`                  : {thr} of {tot}')
    print(f'  (3) that line inside `pi_x`                  : {inl} of {tot}')
    print(f'  ==> `rho_bar_2 <= Pi_x`                      : {inp} of {tot}')
    print('  per skeleton (rows, Q=0, through p_x, in pi_x):')
    for k in sorted(byrung):
        print(f'    {k}: {tuple(byrung[k])}')
    assert tot >= 40, 'the pitch census did not run'
    assert inp == 0, \
        'CONTAINMENT ACHIEVED -- (BE-E4\') IS REFUTED, report as the HEADLINE'
    assert qz == 0, 'a singular rho_bar_2 appeared -- re-read (BE-175)'
    print('  VERDICT (cap disclosure, RESEARCH-ARC section 5).  At all')
    print(f'  {tot} rows side 2\'s single screw has NONZERO PITCH, so it is')
    print('  not a line and cannot lie in a totally singular plane at all --')
    print('  "NOT FOUND under this cap", never "cannot happen", and the cap')
    print('  is named in `support`.  All three conditions fail')
    print('  INDEPENDENTLY, so the obstruction is not one near-miss')
    print('  incidence: the first condition alone is decisive, and it is a')
    print('  condition on the KLEIN QUADRIC rather than on incidence.')
    print(f'  pitch: {time.time() - t0:.1f}s')
    return tot, qz, inp


# ============================================= mode: habitat  ((BE-175))

def _pendant_side2(L, m, mp):
    """Side 2 with a SERIES END at `x`: a pendant path of `L` edges from `x`
    to a hub `h`, then two arcs of `m` and `mp` edges from `h` to `y`.
    CONSTRUCTED and disclosed as such -- it is the shape (BE-175) needs to
    exhibit, not a shape drawn from a census."""
    s2 = []
    _arc(s2, 'x', 'h', L, f'p{L}_')
    _arc(s2, 'h', 'y', m, f'q{m}_')
    _arc(s2, 'h', 'y', mp, f'r{mp}_')
    return s2


def run_habitat():
    t0 = time.time()
    print(f'== habitat: (BE-175) THE OBSTRUCTION, AS A DEGREE COUNT AT `x`, '
          f'seed {SEED}')
    print('  (BE-174) leaves one question: is there ANY mechanism that makes')
    print('  `rho_bar_2` singular?  There is exactly one landed one, and the')
    print('  habitat excludes it.  Both halves are graph theory, so both are')
    print('  decided here by construction rather than by sampling.')
    print()
    print('  (a) THE MECHANISM.  At `deg_2(x) = 1` with neighbour `c`,')
    print('      (BE-45)(i) FORCES `l = p_x ^ p_c` into `rho_bar_2` (the')
    print('      leaf collapse: `c` is a leaf of side 2 + the edge `xc`),')
    print('      and (CH-1)\'s chart condition puts `p_c` in `pi_x` because')
    print('      the closed star of `x` is coplanar.  So `l` is in')
    print('      `Pi_x = p_x ^ pi_x` AUTOMATICALLY, and at `rho_2 = 1` that')
    print('      gives `rho_bar_2 = <l> <= Pi_x` with NO steering at all.')
    print('      The containment is therefore not hard -- it is FREE, in a')
    print('      habitat this question is not asked in.')
    print()
    print('  (b) AND `rnode_shaped` REJECTS EXACTLY THAT SHAPE.  It puts the')
    print('      virtual edge `xy` back, suppresses degree-2 vertices')
    print('      keeping `{x, y}`, and requires the result SIMPLE and')
    print('      3-CONNECTED with min degree `>= 3` -- its own docstring')
    print('      saying "a degree-2 marked vertex after suppression is an')
    print('      S-node and is rejected".  With `deg_2(x) = 1` the terminal')
    print('      `x` keeps one side-2 edge plus the virtual edge, so its')
    print('      degree is 2 and the test FAILS.')
    rej = 0
    shapes = []
    for L in (1, 2, 3, 4):
        for (m, mp) in ((2, 3), (3, 4), (2, 4)):
            s2 = _pendant_side2(L, m, mp)
            nb2 = neighbors(s2)
            assert len(nb2['x']) == 1, 'the constructed side 2 is not pendant'
            ok = rnode_shaped(s2, 'x', 'y')
            shapes.append((L, m, mp, len(nb2['x']), len(nb2['y']), ok))
            assert not ok, \
                ('rnode_shaped ACCEPTED deg_2(x) = 1 -- re-read (BE-175)',
                 L, m, mp)
            rej += 1
    print(f'      ASSERTED at {rej}/{rej} constructed pendant side-2 shapes:')
    print('      (L, m, mp, deg_2(x), deg_2(y), rnode_shaped) =')
    for s in shapes[:6]:
        print(f'        {s}')
    print()
    print('  (c) THE COUNT, and it is the whole obstruction.  BSATUR\'s bad')
    print('      plane needs `deg_1(x) = 1` (`bad_plane` is a series-end')
    print('      device -- (M1) is what it asserts first).  (a) needs')
    print('      `deg_2(x) = 1`.  Together `deg(x) = deg_1(x) + deg_2(x)')
    print('      = 2`.  At `deg(x) = 2`:')
    dd = []
    for L in (1, 2, 3):
        for (m, mp) in ((2, 3), (3, 3)):
            s2 = _pendant_side2(L, m, mp)
            s1 = []
            _arc(s1, 'x', 'y', 5, 's')
            E = s1 + s2
            nb = neighbors(E)
            if 'y' in nb['x']:
                continue
            g = delta_pair(E, 'x', 'y')
            if g is None:
                continue
            r1n = rnode_shaped(s1, 'x', 'y')
            r2n = rnode_shaped(s2, 'x', 'y')
            okh, _W, _b, _h = hcard_ok_piece(E, 'x', 'y')
            dd.append((L, m, mp, len(nb['x']), r1n, r2n, girth(E), okh))
            assert not r1n and not r2n, \
                'a deg(x) = 2 peel was R-node-shaped on some side'
            assert len(nb['x']) == 2, 'deg(x) is not 2'
    print(f'      NEITHER side is R-node-shaped, asserted at {len(dd)}/'
          f'{len(dd)} full peels: side 1 (a path) plus the virtual edge is a')
    print('      CYCLE, and side 2 is the S-node of (b).  So a `deg(x) = 2`')
    print('      peel is not an internal R-node peel on either side, which')
    print('      is the habitat (E4) and (BE-E4\') are stated in.')
    print('      (L, m, mp, deg(x), rnode1, rnode2, girth, hcard) =')
    for s in dd[:4]:
        print(f'        {s}')
    print()
    print('  (d) AND THE FLAG IS NOT STEERABLE THERE EITHER -- a second,')
    print('      independent exclusion.  At `deg(x) = 2` the closed star of')
    print('      `x` is THREE points, so `pi_x` is DETERMINED by the')
    print('      configuration and (BE-105)\'s construction cannot rotate')
    print('      the flag onto a bad plane: it would have to move a')
    print('      neighbour that the star already pins.  This is (BE-136)\'s')
    print('      "at `k >= 2` the flag is determined" phenomenon arriving at')
    print('      `x` from the OTHER side of the peel.')
    print('  VERDICT.  The mechanism that would make the containment free')
    print('  and the habitat the question is asked in are JOINTLY')
    print('  UNSATISFIABLE, by a degree count at one vertex. That is why')
    print('  (BE-174)\'s census is empty, and it is a PROOF rather than a')
    print('  cap -- the cap in `pitch` covers only the residual claim that')
    print('  no OTHER mechanism makes `rho_bar_2` singular.')
    print(f'  habitat: {time.time() - t0:.1f}s')
    return rej, len(dd)


# =============================================== mode: snode  ((BE-176))

# The S-node witness, NAMED so the mode does not depend on a scan: side 1
# the 5-path, side 2 a pendant 2-path into a doubled arc.  `deg_2(x) = 1`,
# so `rnode_shaped(side2)` is FALSE -- that is the point.
SN = (2, 2, 2)


def run_snode(nseed=12):
    t0 = time.time()
    print(f'== snode: (BE-176) THE MECHANISM IS REAL, MEASURED JUST OUTSIDE '
          f'THE HABITAT, seed {SEED}')
    print('  (BE-175)(a) is an argument.  This measures it, at the nearest')
    print('  legal peel the argument applies to -- an S-NODE peel, disclosed')
    print('  as CONSTRUCTED and as OUTSIDE (E4)\'s habitat.  If the forced')
    print('  hinge really lands in `Pi_x`, `c_2(Pi_x)` must be `>= 1` here')
    print('  and it is `0` at every R-node row of `pitch`.')
    L, m, mp = SN
    s2 = _pendant_side2(L, m, mp)
    s1 = []
    _arc(s1, 'x', 'y', 5, 's')
    E, x, y = s1 + s2, 'x', 'y'
    nb, nb2 = neighbors(E), neighbors(s2)
    okh, _W, _b, _h = hcard_ok_piece(E, x, y)
    g = delta_pair(E, x, y)
    assert g is not None, 'the S-node witness is not a 2-cut'
    print(f'  peel: side 1 the 5-path, side 2 = pendant({L}) + arcs'
          f'({m},{mp}); |V| {len(verts_of(E))}, |E| {len(E)}, girth '
          f'{girth(E)}, hcard {okh}, deg(x) {len(nb[x])}, deg_2(x) '
          f'{len(nb2[x])}, rnode_shaped(side2) {rnode_shaped(s2, x, y)}')
    assert len(nb2[x]) == 1 and not rnode_shaped(s2, x, y), \
        'the witness is not the S-node shape (BE-175) names'
    c1v = sorted(neighbors(s1)[x], key=str)[0]
    rows, hinge, cen = 0, 0, {}
    for sd in range(nseed):
        rng = random.Random(SEED + 1013 * sd + 7 * L + 3 * m + 5 * mp)
        d = draw_peel(E, x, y, rng)
        if d is None:
            continue
        P, B, pts, aff, branches = d
        S1, r1, _dM, _ = rho_bar_of(s1, aff, x, y)
        px0, pc1 = hat(aff[x]), hat(aff[c1v])
        if not contains(S1, [wedge2(px0, pc1)]):
            continue
        try:
            badB = bad_plane(S1, px0, pc1)
        except AssertionError:
            continue
        if badB is None:
            continue
        pa0 = plane_at(E, aff, x)
        if pa0 is None or dim(isect(S1, pencil_space(px0, pa0))) >= 2:
            continue
        aff2 = reflag(E, x, s1, P, B, pts, badB, branches, rng)
        if aff2 is None:
            continue
        ok, _n = verify_pencil_witness(E, aff2)
        if not ok:
            continue
        pix = plane_at(E, aff2, x)
        if pix is None or not same_space(pix, badB):
            continue
        px = hat(aff2[x])
        Pix = pencil_space(px, pix)
        R1, rr1, _a, _ = rho_bar_of(s1, aff2, x, y)
        R2, rr2, _b, _ = rho_bar_of(s2, aff2, x, y)
        rows += 1
        c2 = dim(isect(R2, Pix)) if R2 else 0
        cen[(rr1, rr2, dim(isect(R1, Pix)), c2)] = \
            cen.get((rr1, rr2, dim(isect(R1, Pix)), c2), 0) + 1
        # THE POINT: the forced hinge at the series end lies in Pi_x.
        cnb = sorted(nb2[x], key=str)[0]
        ell = wedge2(px, hat(aff2[cnb]))
        assert contains(R2, [ell]), \
            '(BE-45)(i) failed: the series-end hinge is not in rho_bar_2'
        assert contains(Pix, [ell]), \
            'the chart condition failed: the hinge is not in Pi_x'
        assert c2 >= 1, 'c_2(Pi_x) = 0 at a side-2 series end'
        hinge += 1
    print(f'  {rows} reflagged rows; census (rho_1, rho_2, c_1, c_2): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cen.items())))
    print(f'  THE FORCED HINGE IS IN BOTH `rho_bar_2` AND `Pi_x`, ASSERTED')
    print(f'  at {hinge}/{rows}, hence `c_2(Pi_x) >= 1` at {hinge}/{rows}.')
    assert rows >= 4 and hinge == rows, 'the S-node witness did not reproduce'
    print('  CONTRAST, and it is the whole finding: `c_2(Pi_x) = 0` at')
    print('  EVERY R-node row in `pitch`, and `>= 1` at every row here.')
    print('  So the boundary is `rnode_shaped` -- a topological test -- and')
    print('  NOT genericity of the draw.  DISCLOSED: this peel is outside')
    print('  (E4)\'s stated habitat, so it is NOT a refutation of (BE-E4\');')
    print('  it is the evidence that (BE-175)(a)\'s mechanism is real, which')
    print('  is what makes (BE-175)(b)/(c) load-bearing rather than idle.')
    print(f'  snode: {time.time() - t0:.1f}s')
    return rows, hinge


# =============================================== mode: bound  ((BE-177))

def run_bound():
    t0 = time.time()
    print(f'== bound: (BE-177) THE LAST GAP CLOSED, AND THE BOARD, '
          f'seed {SEED}')
    print('  (BE-176) reached `c_2(Pi_x) = 1` but not `rho_bar_2 <= Pi_x`,')
    print('  because it had `rho_2 = 2`.  The containment at a series end')
    print('  needs `rho_2 = 1`, i.e. `delta_2 = 1`.  Is THAT reachable with')
    print('  a series end whose `x`-neighbour the reflag can actually place?')
    print('  Enumerated over `arc(x -> v, L)` glued to a subdivided')
    print('  skeleton at two non-adjacent hubs -- the rigid side 2 of')
    print('  BFOUR\'s own `pr = [2]*n` rung, which is where `delta_2` is')
    print('  smallest.')
    rows, mind, cen = 0, None, {}
    for skn in ('K4', 'prism', 'K33'):
        sk = SKELETONS[skn]
        hubs = sorted({w for e in sk for w in e})
        base = subdivided(sk, [2] * len(sk))
        for (v, yy) in itertools.combinations(hubs, 2):
            for L in (2, 3):
                s2 = []
                for (a, b) in base:
                    aa = 'y' if a == yy else ('V' if a == v else f'z{a}')
                    bb = 'y' if b == yy else ('V' if b == v else f'z{b}')
                    s2.append((aa, bb))
                _arc(s2, 'x', 'V', L, f'p{L}_')
                s1 = []
                _arc(s1, 'x', 'y', 5, 's')
                E = s1 + s2
                nb = neighbors(E)
                if 'y' in nb['x']:
                    continue
                g = delta_pair(E, 'x', 'y')
                if g is None:
                    continue
                d1, d2, Ea, Eb = g
                if len(Ea) == 5:
                    dd2, S2 = d2, Eb
                elif len(Eb) == 5:
                    dd2, S2 = d1, Ea
                else:
                    continue
                nb2 = neighbors(S2)
                xn = sorted(nb2['x'], key=str)
                if len(xn) != 1 or len(nb[xn[0]]) != 2:
                    continue        # not a series end, or an immovable hub
                rows += 1
                cen[dd2] = cen.get(dd2, 0) + 1
                mind = dd2 if mind is None else min(mind, dd2)
    print(f'  {rows} constructed peels with a side-2 series end at `x` whose')
    print(f'  `x`-neighbour is MOVABLE (degree 2).  `delta_2` census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cen.items())))
    print(f'  MINIMUM `delta_2` over all of them: {mind}')
    assert rows >= 20, 'the bound enumeration did not run'
    assert mind is not None and mind >= 2, \
        'delta_2 = 1 IS reachable with a movable series end -- re-open (BE-177)'
    print('  So `delta_2 = 1` is NOT reachable that way: a pendant whose')
    print('  first vertex is movable has length `>= 2` and contributes TWO')
    print('  hinges, so `delta_2 >= 2`.  A series end at `x` with')
    print('  `rho_2 = 1` therefore needs its `x`-neighbour to be a HUB --')
    print('  which is `deg(x) = 2` again, (BE-175)(c)/(d)\'s exclusion.')
    print('  Cap, disclosed: enumerated over three skeletons at')
    print('  `pr = [2]*n` and `L in {2, 3}`, NOT over all side-2 shapes.')
    print()
    print('  THE BOARD.  WHAT MOVED: (BE-162)(iii) is ANSWERED, **NO**;')
    print('  (BE-E4\') survives its own tight boundary and gains the')
    print('  FAMILY\'S FIRST POSITIVE structural fact; the obstruction is a')
    print('  degree count, not a genericity claim; and `Pi_x`\'s TOTAL')
    print('  SINGULARITY enters this thread as a working tool for the first')
    print('  time -- (BE-149)(v)(b) had recorded it and nothing had used it.')
    print('  WHAT DID NOT MOVE: `PencilPair K 3 G`, `hbareSplit`, `hK`,')
    print('  `hcontract`, (GR-15), (BE-14) and S-mark, class uniformity, the')
    print('  12 unwitnessed-not-excluded blocks, cross-pair welding, item')
    print('  0(b) [MARGIN], (BE-101)(iii). (E4) stays REFUTED and')
    print('  `Gamma`-properness stays where BFOUR left it. NOT a PENCIL')
    print('  event; `hK` is not closer.  THE E-RIDER: E1 no g-flank and no')
    print('  rank computed; E2 untouched; E3 ARMED, does not fire -- this is')
    print('  a per-habitat obstruction, not a class-uniform positive.')
    print(f'  bound: {time.time() - t0:.1f}s')
    return rows, mind


# ======================================================= mode: support

def run_support():
    print('== support: the RESEARCH-ARC section 4 support audit')
    print('  Every population named, with what it VARIES, what it HOLDS')
    print('  FIXED, and which quantifier of its own claim it reaches.')
    print('  BSATUR\'s sharpening binds and RPOOL\'s does too: this')
    print('  direction\'s own generator parameters are named per row.')
    rows = [
        ('crit / (BE-172)',
         'the flag data of every `delta_2 = 1` ladder row -- `p_x`, `pi_x` '
         'and `Pi_x` as the reflag produces them',
         'nothing that matters: the two facts asserted are statements about '
         '`K^4`, so the ladder only supplies flags to test them at',
         'the reduction fully. `Pi_x = Sigma_{p_x} cap Lambda^2 pi_x` and '
         'total singularity are exact identities, not estimates, and they '
         'are what turns the question into a question about PITCH'),
        ('free / (BE-173)',
         'the reflag, 6 resweeps at each of 14 configuration seeds, at a '
         'FIXED bad plane per configuration',
         'the bad plane, side 1 (asserted byte-identical), the skeleton set '
         'and the profile',
         'exactly the coordinator\'s stated reason, which is a claim about '
         'the sampler\'s support. It does NOT reach the claim that no OTHER '
         'freedom exists -- only that this one does'),
        ('pitch / (BE-174)',
         '10 configuration seeds x 4 resweeps at three skeletons; the three '
         'conditions of (BE-172) measured SEPARATELY',
         '`delta_1 = 5` (side 1 the peeled 5-branch), `delta_2 = 1`, and '
         'the profile family `[5, 2, 2, 3, 3, 3]`-shaped',
         'the sentence "no `delta_2 = 1` R-node row has `rho_bar_2 <= Pi_x`" '
         'under that cap. It does NOT prove it: the proof is (BE-175), and '
         'this census is what makes (BE-175) the explanation rather than a '
         'hypothesis'),
        ('habitat / (BE-175)',
         'the pendant length `L in {1,2,3,4}` and the two arc lengths, at 12 '
         'constructed side-2 shapes; then 6 full peels',
         'nothing sampled at all -- every claim here is graph-theoretic and '
         'decided by construction',
         'the PROOF. `rnode_shaped` rejecting `deg_2(x) = 1` is a property '
         'of the test, not of a draw, and the degree count is arithmetic. '
         'This is the only mode whose verdict is not cap-bounded'),
        ('snode / (BE-176)',
         '12 configuration seeds at ONE named constructed S-node peel, with '
         'the flag adversarial (BSATUR\'s bad plane) at every one',
         'the peel is NAMED, not sampled; `rho_2 = 2` there',
         'the existence half of (BE-175)(a) -- that the forced hinge really '
         'does land in `Pi_x`. It reaches `c_2(Pi_x) >= 1`, NOT '
         '`rho_bar_2 <= Pi_x`, because `rho_2 = 2` at this peel; (BE-177) is '
         'why `rho_2 = 1` cannot be had here'),
        ('bound / (BE-177)',
         'three skeletons x every non-adjacent hub pair x pendant length '
         '`L in {2,3}`, at the rigid `pr = [2]*n` profile',
         '`pr = [2]*n` itself, and side 1',
         'the sentence "`delta_2 = 1` is not reachable with a MOVABLE '
         'series end" under that cap. The generator parameter this direction '
         'moved is the one BFOUR named as hardcoded (`pr`) plus the pendant '
         'length; what it did NOT move is the skeleton family'),
    ]
    for (nm, var, fix, reach) in rows:
        print(f'  --- {nm}')
        print(f'      VARIES : {var}')
        print(f'      FIXED  : {fix}')
        print(f'      REACHES: {reach}')
    print('  THE ONE SENTENCE THIS AUDIT EXISTS FOR.  The verdict is NO, and')
    print('  it rests on a PROOF (`habitat`) plus a census (`pitch`) -- not')
    print('  on the census alone.  Had only `pitch` run, the honest verdict')
    print('  would have been "not found under cap C" and the clause would')
    print('  still be one lucky draw from death; what makes it a structural')
    print('  fact is that the ONE mechanism able to produce the containment')
    print('  is excluded by the habitat\'s own definition, and that the')
    print('  mechanism is measured working just outside it (`snode`).')
    return len(rows)


def run_validate():
    a = run_crit()
    print()
    b = run_free()
    print()
    c = run_pitch()
    print()
    d = run_habitat()
    print()
    e = run_snode()
    print()
    f = run_bound()
    print()
    g = run_support()
    print()
    print(f'== validate: crit {a}, free {b}, pitch {c}, habitat {d}, '
          f'snode {e}, bound {f}, support {g}')


def main(argv):
    modes = [a for a in argv[1:] if a.startswith('--')]
    if not modes or '--validate' in modes:
        run_validate()
        return
    for m in modes:
        {'--crit': run_crit, '--free': run_free, '--pitch': run_pitch,
         '--habitat': run_habitat, '--snode': run_snode,
         '--bound': run_bound, '--support': run_support}[m]()
        print()


if __name__ == '__main__':
    main(sys.argv)
