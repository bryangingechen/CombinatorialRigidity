"""
Direction BMBLOCK (Phase 39 PENCIL, section (K-bare-ext)) -- THE `<M>` BLOCK
at rung 3.  Can `c_1(<M>) = c_2(<M>) = 1` occur at an internal R-node peel
with `Sigma_delta <= 6`, `a = (0,0)`, side-degree `>= 2` on both sides, in the
generic flag regime?  At `dim <M> = 1` that pair is a violation by `2 > 1` --
the CHEAPEST the arithmetic allows -- and (BE-262)(ii) calls it the cheapest
remaining route to a rung-3 `Good = EMPTY` piece.

  THE ANSWER, said at the top: CLOSED BY PROOF on the whole region except
  one named corner, and the proof does NOT transport (BE-258)'s method.

  `<M> = <p_x ^ p_y>` is the Pluecker point of the line `p_x v p_y` -- in
  THIS carrier that line is exactly the hinge line the virtual edge `xy`
  would carry (`bimage.chain_of`: `l_i = p_{i-1} ^ p_i`).  So `c_i(<M>) = 1`
  says: side `i`'s relative screw space contains the VIRTUAL EDGE's own
  hinge line.  By (BE-30)(iv) (`rho_bar_i <= <P>` POINTWISE, every x--y path
  `P` of side `i`) that forces `p_x ^ p_y in <P>` for every such `P`.

  The key asymmetry with `Pi_x`, and the reason (BE-258)'s rank-3 operator
  does NOT transport: `alpha_x = ker(omega |-> omega ^ p_x)` is attached to
  ONE point and has a rank DEFECT (`rank phi = 3 < 6`), which yields a
  LOWER bound `dim(<P_0> cap alpha_x) >= d - 3` and hence only an upper
  bound `max(1, d-3)` on `c_i(Pi_x)`.  `<M>` is a single LINE attached to
  BOTH points; there is no operator and no rank defect.  What replaces the
  rank count is a TRANSVERSAL: a bivector `eta` with `l_j ^ eta = 0` for
  every hinge line of the path and `(p_x ^ p_y) ^ eta != 0`.  For
  `dist_i in {2,3,4}` such an `eta` is EXPLICIT and DECOMPOSABLE, giving a
  POINTWISE exclusion under a named non-degeneracy; for `dist_i = 5` no
  decomposable transversal exists generically and the exclusion is a
  non-vanishing `6 x 6` determinant, witnessed exactly over Q.

  MODES
    path   the `<M>` path lemma.  `dim(<P> cap <M>)` as a function of the
           path length `m`, exact over Q: the generic column, the explicit
           transversal certificates at `m = 3, 4`, the pointwise `m = 2`
           argument with its collinear control, the `m = 5` determinant
           witness, and the `m >= 6` saturation.  Seeded.
    side   the `bgoodempty.run_pix` analogue at `<M>`: over the side
           library, `dim(<P_0> cap <M>)` and `c_i(<M>)` against `dist_i`,
           with `c_i(<M>) = 1 ==> rho_i = 6` asserted.
    reach  the RESIDUE'S POPULATION, priced with NO DRAWS: `(dist_1,
           dist_2)` is combinatorial, so whether the path lemma's open
           corner can occur in-region is decided over the WHOLE `block` job
           list without sampling.
    block  the TWO-SIDED census.  `bgoodempty.block_row` computes `cM` and
           `run_block` never prints it; this mode reports the JOINT
           distribution of `(c_1(<M>), c_2(<M>))` with `(dist_1, dist_2)`
           on the same composite population.
    arith  the rung-3 arithmetic closure at `<M>`, cap-free: enumerate every
           `(delta_1, delta_2, dist_1, dist_2, rho_1, rho_2)` the landed
           constraints allow and check that `(1,1)` at `<M>` survives in
           EXACTLY ONE corner.  Seedless.
    validate  path + arith + a reduced `side` and `block`.

  NOTATION, stated ONCE.  `V := Lambda^2 K^4`; `<M> := <p_x ^ p_y>`, the
  `bunif.BLK` block `'M'` with `bunif.CAP['M'] = 1`; `c_i(U) :=
  dim(rho_bar_i cap U)`; `slack := max(0, delta_1 + delta_2 - 6)`; RUNG 3
  is `Sigma_delta <= 6`, where `slack = 0` and the `<M>` OBLIGATION is
  `c_1(<M>) + c_2(<M>) <= 1`.  `<P>` is the span of the hinge lines of an
  x--y path `P`, and `m = |P|` its EDGE count, so `dim <P> <= min(m, 6)`.

  CAPS ARE DISCLOSED IN-MODE and travel with every figure.  A capped search
  reports NOT FOUND UNDER CAP C, never "does not exist".
"""

import os
import sys
import time
import random
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import wedge2, hat, rank as rank_exact        # noqa: E402
from bimage import dim, span, isect, rho_bar_of               # noqa: E402
from bdecor import sample_by_branches                         # noqa: E402
import bunif                                                  # noqa: E402
import bproper                                                # noqa: E402
import bgoodempty as BG                                       # noqa: E402

SEED = 20260912
RUNG3 = 6          # `Sigma_delta <= RUNG3` is (BE-225)(iii)'s bottom rung
MDIM = 1           # `dim <M>` -- and `bunif.CAP['M']`


# ------------------------------------------------------------------ helpers

def _rand_pt(rng, lo=-97, hi=97):
    return [F(rng.randint(lo, hi)) for _ in range(3)] + [F(1)]


def _pspan(pts):
    """`<P>`: the span of the hinge lines `p_{j-1} ^ p_j` of the path."""
    return span([wedge2(pts[j], pts[j + 1]) for j in range(len(pts) - 1)])


def _mspace(p0, pm):
    """`<M> = <p_0 ^ p_m>`, the virtual edge's own hinge line."""
    out = span([wedge2(p0, pm)])
    assert dim(out) == MDIM, ('<M> is not 1-dimensional -- p_x = p_y?',
                              dim(out))
    return out


def _klein(a, b):
    """The Klein pairing `a ^ b in Lambda^4 K^4 = K`, in `exactcore.PL`
    order.  `PL` is the list of index pairs, so `a ^ b` picks out the three
    complementary products with the Plueckerian signs."""
    from exactcore import PL
    tot = F(0)
    for i, (p, q) in enumerate(PL):
        for j, (r, s) in enumerate(PL):
            if {p, q, r, s} != {0, 1, 2, 3}:
                continue
            # sign of the permutation (p, q, r, s)
            perm = [p, q, r, s]
            sg = 1
            for u in range(4):
                for v in range(u + 1, 4):
                    if perm[u] > perm[v]:
                        sg = -sg
            tot += sg * a[i] * b[j]
    return tot


def _annihilates(eta, rows):
    return all(_klein(eta, r) == 0 for r in rows)


def _ann1(rows):
    """A generator of the Klein-annihilator of `span(rows)` when that span is
    5-dimensional: solve `<eta, r> = 0` for every `r` in `rows`."""
    from exactcore import PL, rref
    n = len(PL)
    # <e_I, e_J> is nonzero only for complementary index pairs, so the
    # pairing matrix is a signed permutation; build the linear system.
    basis = [[F(1) if k == j else F(0) for k in range(n)] for j in range(n)]
    A = [[_klein(b, r) for b in basis] for r in rows]
    R, piv = rref([row[:] + [F(0)] for row in A])
    free = [j for j in range(n) if j not in piv]
    if len(free) != 1:
        return None
    f = free[0]
    out = [F(0)] * n
    out[f] = F(1)
    for i, j in enumerate(piv):
        out[j] = -R[i][f]
    return out


def _hinges(pts):
    return [wedge2(pts[j], pts[j + 1]) for j in range(len(pts) - 1)]


# ------------------------------------------------------- mode: path

def run_path(ndraw=60, mmax=8, seed=SEED):
    """THE `<M>` PATH LEMMA.  Caps: `ndraw` exact-Q draws per path length
    `m = 1..mmax`, points drawn uniformly from a 195-cube of Q^3 (affine
    chart), seeded.  Every claim an assert."""
    t0 = time.time()
    print(f'== path: `dim(<P> cap <M>)` AS A FUNCTION OF THE PATH LENGTH, '
          f'exact over Q, seed {seed}')
    print(f'   CAP: {ndraw} draws per `m = 1..{mmax}`, free points (NOT on '
          f'`Chart(H)`); the')
    print('   `Chart(H)` reading is `side`/`block`.  (BE-30)(iv) is PROVED '
          'and POINTWISE:')
    print('   `rho_bar_i <= <P>` for EVERY x--y path `P`, so '
          '`c_i(<M>) <= dim(<P> cap <M>)`')
    print('   at EVERY configuration -- no semicontinuity is used in this '
          'step.')

    rng = random.Random(seed)
    gen, nonsat = {}, 0
    for m in range(1, mmax + 1):
        for _ in range(ndraw):
            pts = [_rand_pt(rng) for _ in range(m + 1)]
            if rank_exact([pts[0], pts[-1]]) != 2:
                continue
            P = _pspan(pts)
            M = _mspace(pts[0], pts[-1])
            dp, dc = dim(P), dim(isect(P, M))
            gen[(m, dp, dc)] = gen.get((m, dp, dc), 0) + 1
            assert dp <= min(m, 6), ('`dim<P>` exceeded `min(|P|,6)`', m, dp)
            if dp == min(m, 6):
                assert dc == (0 if 2 <= m <= 5 else 1), \
                    ('the generic `c(<M>)` is not the lemma\'s', m, dp, dc)
            else:
                nonsat += 1
    print(f'   (a) GENERIC column, `(m, dim<P>, dim(<P> cap <M>))`:')
    for key in sorted(gen):
        print(f'       m={key[0]}  dim<P>={key[1]}  c={key[2]}   x{gen[key]}')
    tot = sum(gen.values())
    print(f'       ASSERTED at every draw reaching `dim<P> = min(m,6)` '
          f'({tot - nonsat} of {tot}):')
    print('       `dim(<P> cap <M>) = 0` for `2 <= m <= 5`, `= 1` for '
          '`m = 1` and `m >= 6`.')
    print('       So the `<M>` confinement is TOTAL below m = 6, where the '
          '`Pi_x` one only')
    print('       gives `max(1, d-3)` -- the methods do NOT match, and this '
          'one is stronger.')

    # ---- (b) m = 1: <P> = <M> exactly.  The virtual edge IS the hinge line.
    hits = 0
    for _ in range(ndraw):
        pts = [_rand_pt(rng) for _ in range(2)]
        if rank_exact(pts) != 2:
            continue
        assert _pspan(pts) == _mspace(pts[0], pts[1]) or \
            dim(isect(_pspan(pts), _mspace(pts[0], pts[1]))) == 1
        hits += 1
    print(f'   (b) m = 1.  `<P> = <M>` identically ({hits}/{hits}).  A side '
          f'carrying the REAL edge')
    print('       `xy` therefore has `rho_bar_i <= <M>`, so `rho_i <= 1`.  '
          'IN-REGION THIS IS')
    print('       VACUOUS: an internal R-node peel needs `x !~ y` '
          '(`bgoodempty.block_row`')
    print('       gates it, `bproper.NONADJ` is built on it), so '
          '`dist_i >= 2` on BOTH sides.')

    # ---- (c) m = 2: POINTWISE, and the only degeneration is collinearity.
    hits, coll = 0, 0
    for _ in range(ndraw):
        p0, p1, p2 = (_rand_pt(rng) for _ in range(3))
        if rank_exact([p0, p1, p2]) != 3:
            continue
        assert dim(isect(_pspan([p0, p1, p2]), _mspace(p0, p2))) == 0, \
            'm = 2 non-collinear did not exclude <M>'
        hits += 1
    for _ in range(ndraw):
        p0, p1 = _rand_pt(rng), _rand_pt(rng)
        lam = F(rng.randint(1, 9))
        p2 = [p0[k] + lam * (p1[k] - p0[k]) for k in range(4)]
        P = _pspan([p0, p1, p2])
        assert dim(P) == 1 and dim(isect(P, _mspace(p0, p2))) == 1, \
            'collinear m = 2 did not collapse onto <M>'
        coll += 1
    print(f'   (c) m = 2.  EVERY element of `<P>` is `p_1 ^ w`, a line '
          f'THROUGH `p_1`; `p_0 ^ p_2`')
    print('       is a line through `p_1` iff `p_0, p_1, p_2` are '
          'COLLINEAR.  So `dim(<P> cap <M>)')
    print(f'       = 0` at EVERY configuration with the three points '
          f'non-collinear ({hits}/{hits}),')
    print(f'       and the one degeneration collapses `dim<P>` to 1 '
          f'({coll}/{coll}).  Non-collinearity')
    print('       of three CONSECUTIVE points is the carrier\'s own '
          'hinge-coincidence gate')
    print('       (`bimage.legal_chain`, (BE-30)(ii)/(iii)), so at '
          '`dist_i = 2` the exclusion is')
    print('       POINTWISE ON THE HABITAT, not merely generic.')

    # ---- (d) m = 3, 4: EXPLICIT DECOMPOSABLE TRANSVERSALS.
    for m, (ia, ib) in ((3, (1, 2)), (4, (1, 3))):
        hits, bad = 0, 0
        for _ in range(ndraw):
            pts = [_rand_pt(rng) for _ in range(m + 1)]
            eta = wedge2(pts[ia], pts[ib])
            ls = _hinges(pts)
            assert _annihilates(eta, ls), \
                ('the transversal fails to annihilate a hinge line', m)
            key = [pts[0], pts[m], pts[ia], pts[ib]]
            pair = _klein(eta, wedge2(pts[0], pts[m]))
            if rank_exact(key) == 4:
                assert pair != 0, ('the transversal FAILS to separate <M>',
                                   m)
                assert dim(isect(_pspan(pts), _mspace(pts[0], pts[m]))) == 0
                hits += 1
            else:
                bad += 1
        print(f'   (d) m = {m}.  TRANSVERSAL `eta = p_{ia} ^ p_{ib}`: it '
              f'meets every path edge (shares')
        print(f'       an endpoint with each), so `l_j ^ eta = 0` for all '
              f'`j` -- ASSERTED at all')
        print(f'       {ndraw} draws.  And `(p_0 ^ p_{m}) ^ eta = '
              f'det[p_0, p_{m}, p_{ia}, p_{ib}]`, NONZERO')
        print(f'       exactly when those four points SPAN.  So '
              f'`dim(<P> cap <M>) = 0` POINTWISE under')
        print(f'       that named hypothesis: {hits}/{hits} spanning draws '
              f'asserted, {bad} degenerate.')

    # ---- (e) m = 5: no decomposable transversal; a 6x6 determinant instead.
    hits, wit, decomp = 0, None, 0
    for _ in range(ndraw):
        pts = [_rand_pt(rng) for _ in range(6)]
        ls = _hinges(pts)
        M6 = ls + [wedge2(pts[0], pts[5])]
        if rank_exact(ls) != 5:
            continue
        assert rank_exact(M6) == 6, \
            'the m = 5 determinant VANISHED -- <M> is inside <P>'
        # the annihilator of a 5-dim <P> is 1-dimensional; a DECOMPOSABLE
        # generator would be a transversal line.  Plueckerian test: eta ^ eta.
        ann = _ann1(ls)
        assert ann is not None and _annihilates(ann, ls), \
            'the annihilator computation failed'
        if _klein(ann, ann) == 0:
            decomp += 1
        if wit is None:
            wit = [[int(c) for c in p] for p in pts]
        hits += 1
    print(f'   (e) m = 5.  No decomposable transversal exists generically '
          f'(a line meeting all')
    print('       five path edges must pass through `p_1` or lie in '
          '`<p_0,p_1,p_2>`, AND through')
    print('       `p_4` or lie in `<p_3,p_4,p_5>`, AND meet `p_2 p_3` -- '
          'all four combinations')
    print('       fail generically).  The exclusion is instead the '
          'NON-VANISHING of the `6 x 6`')
    print(f'       determinant `det[l_1..l_5, p_0 ^ p_5]`, a POLYNOMIAL in '
          f'the point coordinates:')
    print(f'       rank 6 asserted at {hits}/{hits} draws with '
          f'`dim<P> = 5`.  One nonzero value at')
    print(f'       ONE exhibited point PROVES the generic statement -- '
          f'non-vanishing is open.')
    print(f'       AND THE NO-TRANSVERSAL REMARK IS MEASURED, not just '
          f'argued: the annihilator of')
    print(f'       `<P>` is DECOMPOSABLE (`eta ^ eta = 0`, i.e. a genuine '
          f'transversal LINE) at')
    print(f'       {decomp} of {hits} draws.')
    print(f'       WITNESS (affine, integer): {wit}')

    # ---- (f) m >= 6: the confinement is VACUOUS, and that is the corner.
    sat = 0
    for _ in range(ndraw):
        pts = [_rand_pt(rng) for _ in range(7)]
        if dim(_pspan(pts)) == 6:
            assert dim(isect(_pspan(pts), _mspace(pts[0], pts[6]))) == 1
            sat += 1
    print(f'   (f) m >= 6.  `dim<P> = 6` generically ({sat}/{ndraw} at '
          f'm = 6), so `<P> = V` and the')
    print('       confinement says NOTHING.  This is the `<M>` analogue of '
          '(BE-258)(iv)\'s')
    print('       regime split, and it is the ONLY corner the path lemma '
          'leaves open.')
    print(f'  [{time.time() - t0:.1f}s]')
    return gen


# ------------------------------------------------------- mode: side

def run_side(ndraw=3, seed=SEED, maxarc=8, maxtheta=7):
    """The `bgoodempty.run_pix` analogue at `<M>`, on the SAME side library
    and at the SAME landed defaults (`maxarc=8`, `maxtheta=7`, `nlad=40`,
    `xy_paths(cap=400, maxlen=9)`, `ndraw=3`).  CAP: that library, those
    draws.  `<M>` needs only the two hub POINTS, not the flags -- unlike
    `Pi_x`, which needs `pi_x` -- so no flag-regime gate is applied here."""
    t0 = time.time()
    print(f'== side: `dim(<P_0> cap <M>)` and `c_i(<M>)` against `dist_i`, '
          f'seed {seed}, ndraw {ndraw}')
    print(f'   CAP: `side_library(maxarc={maxarc}, maxtheta={maxtheta}, '
          f'nlad=40)` + `side1_library()`,')
    print('   `xy_paths(cap=400, maxlen=9)`, `sample_by_branches` draws on '
        '`Chart(side)`.')
    rows, hist, hist_p, big, ptwise = 0, {}, {}, [], 0
    lib = list(BG.side_library(maxarc, maxtheta, 40, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in BG.side1_library()]
    for (tag, E, x, y) in lib:
        d = BG.delta_of(E, x, y)
        dd = BG.dist_of(E, x, y)
        paths, _tr = BG.xy_paths(E, x, y, cap=400, maxlen=9)
        short = [P for P in paths if len(P) == dd]
        if not short:
            continue
        cmin_m, cmin_p0, cmin_rho, seen = 9, 9, 9, 0
        for s in range(ndraw):
            rng = random.Random(seed + 733 * s + len(E))
            got = sample_by_branches(E, x, y, rng)
            if got is None:
                continue
            pt = got[0] if isinstance(got, tuple) else got
            try:
                S, rho, _dM, _r = rho_bar_of(E, pt, x, y)
            except AssertionError:
                continue
            px, py = hat(pt[x]), hat(pt[y])
            if rank_exact([px, py]) != 2:
                continue
            M = _mspace(px, py)
            P0 = span([wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in short[0]])
            cm = dim(isect(S, M)) if S else 0
            cp0 = dim(isect(P0, M))
            assert cm <= cp0, ('the (BE-30)(iv) chain `c(<M>) <= '
                               'dim(<P_0> cap <M>)` FAILS', tag, cm, cp0)
            assert cm <= MDIM, 'c(<M>) exceeds dim <M>'
            assert dim(P0) <= min(len(short[0]), 6), \
                ('dim <P_0> exceeded min(|P_0|, 6)', tag)
            if 2 <= dim(P0) <= 5:
                assert cp0 == 0, \
                    ('!! `<M>` INSIDE a proper path span -- the path lemma '
                     'FAILS on Chart', tag, dd, dim(P0))
                ptwise += 1
            if cm == 1:
                assert rho == 6, \
                    ('!! c(<M>) = 1 with rho < 6 -- the shape a rung-3 '
                     '`Good = EMPTY` needs', tag, rho, dd, d)
            assert (dim(isect(S, P0)) == rho) if S else True, \
                ('(BE-30)(iv) fails at the shortest path', tag)
            seen += 1
            cmin_m = min(cmin_m, cm)
            cmin_p0 = min(cmin_p0, cp0)
            cmin_rho = min(cmin_rho, rho)
        if seen == 0:
            continue
        rows += 1
        hist[(min(dd, 7), cmin_m)] = hist.get((min(dd, 7), cmin_m), 0) + 1
        kp = (min(dd, 7), cmin_p0)
        hist_p[kp] = hist_p.get(kp, 0) + 1
        if cmin_m == 1 and cmin_rho < 6:
            big.append((tag, dd, d, cmin_m, cmin_rho))
    print(f'  rows {rows}')
    print(f'  (dist, generic c(<M>)) -> count: {dict(sorted(hist.items()))}')
    print(f'  (dist, generic dim(<P_0> cap <M>)) -> count: '
          f'{dict(sorted(hist_p.items()))}')
    print(f'  the POINTWISE path-lemma assert fired at {ptwise} draws with '
          f'`2 <= dim<P_0> <= 5`.')
    if big:
        print(f'  !! {len(big)} rows with generic `c(<M>) = 1` and '
              f'`rho < 6`:')
        for b in big[:10]:
            print(f'     {b}')
    else:
        print('  0 rows with generic `c(<M>) = 1` and `rho < 6`.  Every')
        print('  `c(<M>) = 1` row has `rho = 6`, hence `delta = 6`, hence')
        print('  `Sigma_delta = 6` ALONE on that side at rung 3.')
    return rows, big, hist, hist_p


# ------------------------------------------------------- mode: block

def run_block(ndraw=3, seed=SEED, maxlen=5, njob=None, quick=False):
    """The TWO-SIDED `<M>` census.  `bgoodempty.block_row` already computes
    `cM`; `bgoodempty.run_block` histograms only `cPix` and never prints it.
    This mode calls the LANDED row function unchanged and reports the
    figure it dropped, joined with `(dist_1, dist_2)`.

    CAP: the same job list as `bgoodempty.run_block` at its COMMITTED
    defaults (`ndraw=3`, `maxlen=5`, all six non-adjacent hub pairs via
    `bgoodempty.nonadj_pairs`, the full `side1_library()`), `njob` as
    passed (None = no truncation)."""
    t0 = time.time()
    print(f'== block: the TWO-SIDED `<M>` census, seed {seed}, ndraw {ndraw},'
          f' maxlen {maxlen}, njob {njob}')
    print('   Same population and same row function as '
          '`bgoodempty.run_block`; `cM` is the')
    print('   field that function computes and its own printer drops.')
    rng = random.Random(seed)
    lib = BG.side1_library()
    if quick:
        lib = lib[::4]
    jobs = []
    for skname in ('K33', 'prism'):
        pairs = BG.nonadj_pairs(skname)
        n = len(BG.SKELETONS[skname])
        for d2 in (2, 3, 4):
            k = 6 + d2
            if k > n:
                continue
            base = [2] * (n - k) + [3] * k
            profs = [base]
            for _ in range(2 if not quick else 1):
                profs.append([rng.randint(2, maxlen) for _ in range(n)])
            for prof in profs:
                for xy in pairs:
                    for (s1name, s1E) in lib:
                        jobs.append((skname, tuple(prof), xy, s1name, s1E))
    rng2 = random.Random(seed + 99)
    rng2.shuffle(jobs)
    if njob:
        jobs = jobs[:njob]
    rows, cmh, dmh, both6, hits = 0, {}, {}, 0, []
    distb = {}
    for (skname, prof, xy, s1name, s1E) in jobs:
        r = BG.block_row(skname, prof, xy, s1name, s1E, rng, ndraw=ndraw)
        if r is None:
            continue
        E, E1, E2, x, y = bproper.composite(skname, list(prof), xy, s1E)
        dd = (BG.dist_of(E1, x, y), BG.dist_of(E2, x, y))
        rows += 1
        cmh[r['cM']] = cmh.get(r['cM'], 0) + 1
        distb[dd] = distb.get(dd, 0) + 1
        dmh[(dd, r['cM'])] = dmh.get((dd, r['cM']), 0) + 1
        assert min(dd) >= 2, ('an in-region peel with dist = 1 -- x ~ y?',
                              r['tag'], dd)
        for i in (0, 1):
            if 2 <= dd[i] <= 5:
                assert r['cM'][i] == 0, \
                    ('!! c_i(<M>) = 1 at 2 <= dist_i <= 5 -- the path lemma '
                     'FAILS in-region', r['tag'], dd, r['cM'])
        if min(dd) >= 6:
            both6 += 1
        if sum(r['cM']) >= 2:
            hits.append((r['tag'], dd, r['d'], r['r'], r['cM']))
    print(f'  in-region rows {rows}   (jobs offered {len(jobs)})')
    print(f'  `(c_1(<M>), c_2(<M>))` generic over free draws: '
          f'{dict(sorted(cmh.items()))}')
    print(f'  `(dist_1, dist_2)` -> count: {dict(sorted(distb.items()))}')
    print(f'  rows with `dist_i >= 6` on BOTH sides (the open corner): '
          f'{both6}')
    if hits:
        print(f'  !! {len(hits)} rows with `c_1(<M>) + c_2(<M>) >= 2`:')
        for h in hits[:10]:
            print(f'     {h}')
    else:
        print('  0 rows with `c_1(<M>) + c_2(<M>) >= 2`.  NOT FOUND under '
              'this cap -- and by')
        print('  the path lemma that is now a CONSEQUENCE on every row with '
              'a side at')
        print('  `2 <= dist_i <= 5`, not independent evidence.')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, cmh, both6, hits


# ------------------------------------------------------- mode: arith

def run_arith(dmax=9):
    """THE RUNG-3 ARITHMETIC CLOSURE AT `<M>`.  Cap-free over the tuple
    layer: `dmax` bounds only the `dist` COORDINATE, and every `dist >= 6`
    behaves identically (the confinement is vacuous there), so the layer is
    exhaustive in the mathematical sense.  Seedless, no sampling.

    The laws, each with its status:
      L0  `delta_1 + delta_2 <= 6`               RUNG 3, (BE-225)(iii)
      L1  `rho_i <= delta_i`                     (BE-22)(ii) at `a_i = 0`
      L2  `rho_i <= dist_i`                      (BE-256)(ii), POINTWISE
      L3  `c_i <= min(rho_i, 1)`                 trivial, `dim <M> = 1`
      L4  `dist_i >= 2`                          the region: `x !~ y`
      L5  `2 <= dist_i <= 5  ==>  c_i = 0`       THE PATH LEMMA -- PROVED
      L6  `dist_i >= 6 and c_i = 1 ==> rho_i = 6`  general position,
                                                  MEASURED (`side` mode)
    """
    t0 = time.time()
    print('== arith: the rung-3 `<M>` obligation `c_1 + c_2 <= 1`, cap-free '
          'over the tuple layer')
    print(f'   dist coordinate run to {dmax}; every `dist >= 6` is one '
          f'regime (confinement vacuous).')
    allt, raw, withL5, withL56 = 0, [], [], []
    for d1 in range(0, 7):
        for d2 in range(0, 7 - d1):
            for t1 in range(2, dmax + 1):
                for t2 in range(2, dmax + 1):
                    for r1 in range(0, min(d1, t1, 6) + 1):
                        for r2 in range(0, min(d2, t2, 6) + 1):
                            for c1 in range(0, min(r1, MDIM) + 1):
                                for c2 in range(0, min(r2, MDIM) + 1):
                                    allt += 1
                                    t = (d1, d2, t1, t2, r1, r2, c1, c2)
                                    if c1 + c2 <= MDIM:
                                        continue
                                    raw.append(t)
                                    if (2 <= t1 <= 5 and c1) or \
                                       (2 <= t2 <= 5 and c2):
                                        continue
                                    withL5.append(t)
                                    if (c1 and r1 != 6) or (c2 and r2 != 6):
                                        continue
                                    withL56.append(t)
    print(f'   tuples enumerated: {allt}')
    print(f'   (a) RAW arithmetic (L0-L4 only): {len(raw)} tuples violate '
          f'`c_1 + c_2 <= 1`.')
    print('       So the arithmetic does NOT triage `<M>` -- (BE-97)(i) read '
          'at this block.')
    print(f'   (b) + L5, THE PATH LEMMA (PROVED): {len(withL5)} survive.')
    if withL5:
        dd = sorted({(t[2] if t[2] < 6 else 6, t[3] if t[3] < 6 else 6)
                     for t in withL5})
        print(f'       every survivor has `(dist_1, dist_2)` in {dd} -- i.e. '
              f'BOTH sides at')
        print('       `dist_i >= 6`, the one corner where `<P_0> = V` and '
              'the lemma is vacuous.')
        rr = sorted({(t[4], t[5]) for t in withL5})
        print(f'       survivor `(rho_1, rho_2)` values: {rr}')
        assert all(t[2] >= 6 and t[3] >= 6 for t in withL5), \
            'a survivor of the path lemma has a side at dist <= 5'
    print(f'   (c) + L6, general position at `dist >= 6` (MEASURED): '
          f'{len(withL56)} survive.')
    assert not withL56, ('a rung-3 `<M>` violation survives BOTH laws',
                         withL56[:5])
    print('       0 survive.  DERIVATION of the 0: `c_i = 1` at `dist_i >= 6`')
    print('       forces `rho_i = 6` (L6), hence `delta_i = 6` (L1 with '
          '`rho_i <= delta_i <= 6`),')
    print('       on BOTH sides, hence `Sigma_delta = 12 > 6`, contradicting '
          'rung 3 (L0). *')
    print('   So at rung 3 the `<M>` block CANNOT bind, and the residue is '
          'exactly L6 at')
    print('   `dist_i >= 6` on BOTH sides.')
    print(f'  [{time.time() - t0:.1f}s]')
    return len(raw), len(withL5), len(withL56)


# ------------------------------------------------------- mode: reach

def _jobs(seed=SEED, maxlen=5, quick=False):
    """`bgoodempty.run_block`'s job list, verbatim at its COMMITTED
    defaults."""
    rng = random.Random(seed)
    lib = BG.side1_library()
    if quick:
        lib = lib[::4]
    jobs = []
    for skname in ('K33', 'prism'):
        pairs = BG.nonadj_pairs(skname)
        n = len(BG.SKELETONS[skname])
        for d2 in (2, 3, 4):
            k = 6 + d2
            if k > n:
                continue
            base = [2] * (n - k) + [3] * k
            profs = [base]
            for _ in range(2 if not quick else 1):
                profs.append([rng.randint(2, maxlen) for _ in range(n)])
            for prof in profs:
                for xy in pairs:
                    for (s1name, s1E) in lib:
                        jobs.append((skname, tuple(prof), xy, s1name, s1E))
    return jobs


def run_reach(seed=SEED, maxlen=5):
    """THE RESIDUE'S POPULATION, PRICED WITHOUT A SINGLE DRAW.  `(dist_1,
    dist_2)` at an internal R-node peel is COMBINATORIAL -- it needs no
    configuration -- so the question *can the path lemma's open corner
    (`dist_i >= 6` on BOTH sides) even occur in-region?* is decided by graph
    theory, not by sampling.  This mode replays `bgoodempty.run_block`'s
    ENTIRE job list at its committed defaults, applies the SAME region gates
    (up to and including `d1 + d2 <= 6`), and reports `(dist_1, dist_2)`.
    CAP: that job list -- every job, no `njob` truncation, no `quick`."""
    t0 = time.time()
    print(f'== reach: `(dist_1, dist_2)` over the WHOLE `block` job list, '
          f'NO DRAWS, seed {seed}')
    jobs = _jobs(seed, maxlen)
    rows, dh, dd_delta, both6, one5 = 0, {}, {}, 0, 0
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
        if d1 + d2 > 6:
            continue
        t1, t2 = BG.dist_of(E1, x, y), BG.dist_of(E2, x, y)
        rows += 1
        assert min(t1, t2) >= 2, ('an in-region peel with dist = 1', t1, t2)
        assert d1 <= t1 and d2 <= t2, \
            ('(BE-256)(ii) `delta <= dist` FAILS in-region', d1, t1, d2, t2)
        dh[(t1, t2)] = dh.get((t1, t2), 0) + 1
        dd_delta[((d1, d2), (t1, t2))] = \
            dd_delta.get(((d1, d2), (t1, t2)), 0) + 1
        if min(t1, t2) >= 6:
            both6 += 1
        if min(t1, t2) <= 5:
            one5 += 1
    print(f'  in-region peels {rows}   (jobs offered {len(jobs)}) '
          f'-- NO configuration was drawn')
    print(f'  `(dist_1, dist_2)` -> count: {dict(sorted(dh.items()))}')
    print(f'  peels with SOME side at `2 <= dist_i <= 5` '
          f'(the PROVED half of (BE-274)): {one5}')
    print(f'  peels with `dist_i >= 6` on BOTH sides '
          f'(the corner L6 is needed for): {both6}')
    if both6 == 0:
        print('  0 -- NOT FOUND under this cap.  So on this whole population '
              'the `<M>` closure')
        print('  is the PROVED half alone and L6 is never invoked.  NEVER '
              '"cannot occur":')
        print('  the cap is `bgoodempty.run_block`\'s job list, two '
              'skeletons, branch lengths')
        print('  `<= 5`, all six non-adjacent hub pairs, a 66-shape side-1 '
              'library.')
    print(f'  `delta <= dist` ASSERTED at all {rows} in-region peels '
          f'((BE-256)(ii), re-verified).')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, dh, both6


# ------------------------------------------------------- mode: dbl

def run_dbl(seed=20260902, nseed=6):
    """THE SPEC'S MECHANISM, REFUTED AT ITS OWN BEST CASE.  The dispatch
    proposed that `(1,1)` at `<M>` comes from (BE-45)'s dichotomy firing on
    both sides, "exactly as at (BE-97)(iii)'s `Pi_x` tightness".  (BE-99)(iii)
    already exhibits the ONE landed configuration where both clauses of
    (BE-45) fire at one peel -- side 2 at the vacuous corner `d_min = 6`
    (so `rho_bar_2 = Lambda^2 K^4` and `c_2(U) = dim U` at EVERY `U`),
    side 1 path-saturated at `d_min = 2`.  This mode re-reads THAT
    configuration at the `<M>` block.  CAP: the single pinned piece
    `bdouble.WIT_PIECE` at peel `bdouble.WIT_PEEL`, `nseed` seeds, at
    `bdouble`'s own landed seed.  No new construction."""
    t0 = time.time()
    import bdouble as BD
    from bimage import dist_in
    from bpeel import peel_sides
    print(f'== dbl: (BE-99)(iii)\'s DOUBLE PENCIL re-read at `<M>`, seeds '
          f'{seed}..{seed + nseed - 1}')
    print(f'   piece `{BD.WIT_PIECE}` at peel {BD.WIT_PEEL} -- the one '
          f'landed peel where BOTH')
    print('   clauses of (BE-45) fire.  If the spec\'s mechanism produced '
          '`(1,1)` at `<M>`, it')
    print('   would produce it HERE.')
    pc = None
    for nm, cand in BD.battery_peels():
        if nm == BD.WIT_PIECE:
            pc = cand
    assert pc is not None, ('witness piece not in the battery', BD.WIT_PIECE)
    idx = [i for i, (x0, y0, _ce, k0) in enumerate(pc['children'])
           if (x0, y0) == BD.WIT_PEEL and k0 != 'leaf']
    assert len(idx) == 1, ('witness peel not unique', idx)
    x, y, side1, side2, kind = peel_sides(pc, idx[0])
    d1min, d2min = dist_in(side1, x, y), dist_in(side2, x, y)
    assert (d1min, d2min) == (2, 6), (d1min, d2min)
    print(f'   combinatorics (configuration-free): d_min(side 1) = {d1min}, '
          f'd_min(side 2) = {d2min}')
    drawn, prof = 0, {}
    for s in range(nseed):
        rng = random.Random(seed + s)
        got0 = sample_by_branches(pc['H'], pc['u'], pc['v'], rng)
        if got0 is None:
            continue
        got = BD.measure_row(pc['H'], got0[0], x, y, side1, side2)
        if got is None:
            continue
        (c1, c2, r1, r2, d1, d2, a1, a2, meas, B, S1, S2, fr) = got
        drawn += 1
        MB = ('M',)
        assert c1[BD.PIX] == 1 and c2[BD.PIX] == 2, \
            ('the (BE-99) Pi_x profile moved', c1[BD.PIX], c2[BD.PIX])
        assert c2[MB] == 1, \
            ('the vacuous corner does not contain <M>', c2[MB])
        assert c1[MB] == 0, \
            ('!! (BE-45)(ii) at d_min = 2 DID reach <M> -- the path lemma '
             'fails on a landed witness', c1[MB])
        prof[(c1[MB], c2[MB])] = prof.get((c1[MB], c2[MB]), 0) + 1
    print(f'   {drawn} of {nseed} seeds drew a generic-regime configuration; '
          f'at every one, ASSERTED:')
    print('     `(c_1(Pi_x), c_2(Pi_x)) = (1, 2)`  -- (BE-99)(iii) '
          'reproduced, the DOUBLE PENCIL')
    print(f'     `(c_1(<M>), c_2(<M>))` = {dict(prof)}  -- '
          f'`c_1 + c_2 = 1 = dim <M>`, NOT 2')
    print('   WHY, and it is the whole refutation of the spec\'s mechanism:')
    print('     * (M1), a SERIES END at `x`, puts the bridge hinge line '
          '`l_e = p_x ^ p_{w_1}`')
    print('       into `rho_bar_i cap Pi_x` ((BE-45)(i)).  That line is '
          '`<M>` iff `w_1 = y`, i.e.')
    print('       iff `dist_i = 1` -- excluded in-region by `x !~ y`.  So '
          '(M1) NEVER reaches `<M>`.')
    print('     * (M2), PATH SATURATION, gives `rho_bar_i = <P>` as SPACES '
          '((BE-45)(ii)).  By the')
    print('       path lemma `<P> cap <M> = 0` for `2 <= d_min <= 5`, so '
          '(M2) is a mechanism for')
    print('       `c_i(<M>) = 0`, NOT for `= 1`, on that whole range.  Its '
          'ONLY `<M>`-reaching')
    print('       case is the vacuous corner `d_min = 6`, where '
          '`delta_i = 6` forces `delta_j = 0`')
    print('       at rung 3 and the OTHER side is rigid.')
    print('   So the two clauses of (BE-45) are mechanisms for `Pi_x`, and '
          'at `<M>` they are')
    print('   MUTUALLY EXCLUSIVE at rung 3.  MECHANISM REFUTED.')
    assert drawn >= 2, 'fewer than two independent witnesses'
    print(f'  [{time.time() - t0:.1f}s]')
    return drawn, prof


# ------------------------------------------------------- mode: validate

def run_validate():
    print('== validate: path + arith at full caps, side + block REDUCED.')
    print('   THE REDUCED CALLS ARE FENCED AND SAID SO HERE: '
          'run_side(ndraw=2, maxarc=6,')
    print('   maxtheta=5) against defaults 3/8/7, and run_block(ndraw=2, '
          'njob=40) against')
    print('   3/None.  NO FIGURE IN THE DRAFT IS TAKEN FROM THIS PATH.')
    run_path(ndraw=20, mmax=7)
    run_arith()
    run_reach()
    run_dbl()
    run_side(ndraw=2, maxarc=6, maxtheta=5)
    run_block(ndraw=2, njob=40)


MODES = {'path': run_path, 'side': run_side, 'block': run_block,
         'arith': run_arith, 'dbl': run_dbl, 'reach': run_reach,
         'validate': run_validate}


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: {argv[0]} [{"|".join(MODES)}]')
        return 2
    MODES[mode]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
