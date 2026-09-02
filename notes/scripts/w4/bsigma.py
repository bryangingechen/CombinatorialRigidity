"""
Direction BSIGMA (ordinal 67) -- IS (BE-107)(iii)'s RESIDUAL REALIZED?

  THE TARGET the spec names, BSATUR's own named-not-excluded residual
  ((BE-107)(iii)), the one shape that kills the repair as well:

    Sigma_x <= rho_bar_i  with  rho_i <= 5 -- every legal plane at x is
    then BAD, so no genericity in the FLAG saves (PENCIL-SATURATES-GEN).

  THE ANSWER, said at the top: THE RESIDUAL IS REALIZED, at exactly
  rho_i = 5, on BSATUR's OWN pinned witness peel `K4(5,3,3,3,3,3)`, in
  the GENERIC FLAG REGIME, through both gates -- so
  (PENCIL-SATURATES-GEN) is FALSE as stated.  And, exactly as BDOUBLE's
  and BSATUR's refutations were, it is SLACK, NOT A SHORTFALL: the peel
  still ATTAINS.  Half (B) is NOT refuted.

    (BE-109) THE HIT.  Take BSATUR's witness peel and place the peeled
             5-branch's points so that p_x, p_{b_1}, p_{b_2}, p_{b_3},
             p_y are COPLANAR in a plane pi and only p_{b_0} -- the
             neighbour of x -- is off it.  Then
             rho_bar_1 = <l_1, l_2> (+) Lambda^2 pi has rho_1 = 5 and
             contains p_x ^ pi (dim 2, inside Lambda^2 pi because
             p_x in pi) TOGETHER WITH l_1 = p_x ^ p_{b_0}, whose span is
             p_x ^ (pi + <p_{b_0}>) = p_x ^ K^4 = Sigma_x.  So
             Sigma_x <= rho_bar_1 AS SPACES at rho_1 = 5, and
             c_1(Pi_x) = 2 at EVERY plane through p_x -- legal or not.

    (BE-110) THE MECHANISM AND THE FLOOR.  Projecting from p_x turns
             dim(rho_bar cap Sigma_x) into a corank: for a PATH side
             dim(rho_bar cap Sigma_x) = rho - dim<L_2, ..., L_L>, where
             L_j is the line of the projected consecutive pair.  Corank
             3 needs dim<L_j> = rho - 3, and dim <= 1 forces EVERY point
             of the path into one plane with p_x, which caps rho at 3.
             Hence at a PATH side `Sigma_x <= rho_bar_i => rho_i >= 5`,
             PROVED -- the residual sits at ONE value of rho_i, exactly
             as the original failure did.

    (BE-111) THE SUPPORT AUDIT (the spec's forced job 2).  (BE-105)(ii)'s
             battery has exactly FIVE deg-1 terminals and they are the
             FIVE PATH PIECES of `bearcase.piece_battery()` -- one
             topological family.  `run_mech` takes ONE configuration per
             piece (the arg-max of rho over <= 6 random draws of
             `sample_piece_config`, whose coordinates are uniform on a
             box), so it varies the PIECE and, inside a piece, only
             GENERIC configurations.  The flag is not a variable of
             Sigma_x at all (Sigma_x = p_x ^ K^4 depends on p_x alone),
             so the quantifier BSIGMA rides is the CONFIGURATION
             STRATUM, not the flag.  On the generic stratum the identity
             is upgraded here from MEASURED to PROVED for path sides
             ((BE-110)(iii)).

    (BE-112) THE PRICE.  Over a constructed population of degenerate-side
             peels: `margin <= 0` at Pi_x, Pi_y, <M> and Lambda^2 K^4 and
             `reach = min(d_1+d_2,6) + a_1 + a_2` ASSERTED at every row --
             0 shortfalls.  What it costs is (BE-107)(i)'s licence read
             POINTWISE IN THE CONFIGURATION, and the replacement is
             (PENCIL-SATURATES-CHART), free by the SAME (BE-16) + (BE-69)
             argument because the bad locus is now proved proper.

    (BE-113) Job 3's residual, the board, the E-rider, the reading.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `witness` (BE-109)  The hit at independent seeds, every line an ASSERT.
  `mech`    (BE-110)  The corank identity and the rho >= 5 floor.
  `support` (BE-111)  The support audit, executable: which battery pieces
            carry a deg-1 terminal, and the identity holding on the
            generic stratum and FAILING on the coplanar one.
  `floor`   (BE-110)  The two-bucket census at degeneracy-rich coordinates:
            no `dim = 3 at rho <= 4` row where the peel could be in the
            generic flag regime, with the denominator named.
  `price`   (BE-112)  The scan: margins and attainment at every row.
  `validate`          A reduced run of all five.

Exact Q throughout (`fractions.Fraction`); single seed 20260902.
"""

import os
import random
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- This driver is the TWENTY-THIRD `kbare/` consumer and takes the
# --- chain TWENTY-ONE deep (`... -> bunif -> bdouble -> bsatur -> bsigma`).
# --- NO MOVE MADE.
from exactcore import hat, wedge2, rank, nullspace, neighbors        # noqa: E402
from bimage import (contains, dim, isect, pencil_space, plane_at,    # noqa: E402
                    rho_bar_of, same_space, span, v4, pt_in)
from bearcase import piece_battery, sample_piece_config              # noqa: E402
from bpeel import SKELETONS, delta_pair, rnode_shaped, subdivided    # noqa: E402
from bdecor import assemble, hubs_and_branches                       # noqa: E402
from bunif import SEED, blocks_of, flag_frame, profile               # noqa: E402
from bsatur import peel_of, row_of, margin_at, sigma_at              # noqa: E402
from binduc import assert_generic_star                               # noqa: E402
from kbare_common import verts_of                                    # noqa: E402
from binduc import path as _path                                    # noqa: E402

PIX, PIY, MB, ALLU = ('Pix',), ('Piy',), ('M',), tuple(
    sorted(('Pix', 'M', 'L', 'Piy')))

WIT_SKEL = 'K4'
WIT_PROF = [5, 3, 3, 3, 3, 3]
WIT_EDGE = 0                       # the peeled skeleton edge, ('A','B')


# ======================================================= the construction

def degenerate_peel(skname, prof, ei, rng, s=20, tries=400):
    """(BE-109)'s configuration: a LEGAL pencil configuration of the whole
    subdivided skeleton whose PEELED branch is placed so that p_x and every
    interior point EXCEPT the one adjacent to x lie in one plane `pi`, with
    p_y in `pi` too.  Everything else is drawn freely.  Returns
    (E, x, y, side1, side2, aff, pi) or None.

    Nothing here is special-cased to the witness: the same routine runs the
    `price` population.  The peeled branch must have >= 4 edges (so that
    Lambda^2 pi is spanned) and every other branch >= 3 edges (so that its
    two flag-constrained interiors are distinct vertices)."""
    got = peel_of(skname, prof, ei)
    if got is None:
        return None
    E, x, y, side1, side2 = got
    W, branches = hubs_and_branches(E, x, y)
    peel = None
    for br in branches:
        z, zp, ints = br
        if {z, zp} == {x, y} and len(ints) == prof[ei] - 1:
            peel = br
    if peel is None:
        return None
    z0, _z0p, pints = peel
    if z0 == y:
        pints = list(reversed(pints))          # orient x -> y
    if len(pints) < 3:
        return None
    for br in branches:
        if br is not peel and len(br[2]) < 2:
            return None
    for _ in range(tries):
        Ppi = span([v4(rng, s) for _ in range(3)])
        if dim(Ppi) != 3:
            continue
        pts = {}
        pts[x] = pt_in(Ppi, rng, s)
        pts[y] = pt_in(Ppi, rng, s)
        b0 = v4(rng, s)
        if rank(Ppi + [b0]) != 4:              # the ONE point off pi
            continue
        pts[pints[0]] = b0
        for w in pints[1:]:
            pts[w] = pt_in(Ppi, rng, s)
        for z in W:
            if z not in pts:
                pts[z] = v4(rng, s)
        B, ok = {}, True
        for z in W:                            # the hub flags
            if z == x:
                bas = [pts[x], b0, v4(rng, s)]
            elif z == y:
                bas = [pts[y], pts[pints[-1]], v4(rng, s)]
            else:
                bas = [pts[z], v4(rng, s), v4(rng, s)]
            if rank(bas) != 3:
                ok = False
                break
            B[z] = span(bas)
        if not ok:
            continue
        for br in branches:                    # every OTHER branch
            if br is peel:
                continue
            z, zp, ints = br
            k = len(ints)
            seq = ([pt_in(B[z], rng, s)] + [v4(rng, s) for _ in range(k - 2)]
                   + [pt_in(B[zp], rng, s)])
            for w, c in zip(ints, seq):
                pts[w] = c
        aff = assemble(E, pts)                 # BOTH gates
        if aff is None:
            continue
        return E, x, y, side1, side2, aff, Ppi
    return None


# ==================================================== mode: witness (BE-109)

def run_witness(nseed=6):
    t0 = time.time()
    print(f'== witness: (BE-109) (BE-107)(iii)\'s RESIDUAL IS REALIZED, '
          f'seed {SEED}')
    print(f'  The peel is BSATUR\'s OWN: `{WIT_SKEL}{tuple(WIT_PROF)}` at '
          f'skeleton edge {SKELETONS[WIT_SKEL][WIT_EDGE]}, side 1 = the')
    print('  5-branch.  What is new is the CONFIGURATION, not the peel: the')
    print('  branch is placed with p_x, p_{b_1}, p_{b_2}, p_{b_3}, p_y in one')
    print('  plane pi and only p_{b_0} (the neighbour of x) off it.')
    got0 = peel_of(WIT_SKEL, WIT_PROF, WIT_EDGE)
    assert got0 is not None, 'the pinned peel is not an R-node peel'
    E0, x0, y0, side1_0, side2_0 = got0
    assert len(side1_0) == 5, 'side 1 is not the 5-branch'
    assert len(neighbors(side1_0)[x0]) == 1, 'the terminal is not side-degree 1'
    assert len(neighbors(side1_0)[y0]) == 1, 'the OTHER terminal is not deg 1'
    assert rnode_shaped(side1_0, x0, y0) or rnode_shaped(side2_0, x0, y0), \
        'the peel is not R-node-shaped'
    print('  ASSERTED already: {x,y} is a 2-cut, the peel is R-NODE-SHAPED,')
    print('  side 1 is the 5-edge branch and deg_1(x) = deg_1(y) = 1 -- BOTH')
    print('  terminals are SERIES ENDS, which is why the stratum does not')
    print('  force pi_y and the flag pair stays in the GENERIC regime.')
    hits, drawn = 0, 0
    for sd in range(nseed):
        rng = random.Random(SEED + 1013 * sd)
        got = degenerate_peel(WIT_SKEL, WIT_PROF, WIT_EDGE, rng)
        if got is None:
            continue
        E, x, y, side1, side2, aff, Ppi = got
        drawn += 1
        px = hat(aff[x])
        S1, r1, dM1, _ = rho_bar_of(side1, aff, x, y)
        Sig = sigma_at(px)
        # --- the seven identities, every one an ASSERT
        assert r1 == 5, ('rho_1 is not 5', r1)
        assert contains(S1, Sig) and dim(isect(S1, Sig)) == 3, \
            'Sigma_x is NOT inside rho_bar_1 -- the hit does not hold'
        fr = flag_frame(E, aff, x, y)
        assert fr is not None, 'the flag pair is OFF the generic regime'
        assert side_star_plane(side1, aff, y) is None, \
            'side 1 already forces pi_y -- the regime would be lost'
        Bl = blocks_of(fr)
        assert contains(S1, Bl['Pix']), 'Pi_x is not inside rho_bar_1'
        pa = plane_at(E, aff, x)
        assert pa is not None and same_space(
            pencil_space(px, pa), Bl['Pix']), \
            'the block Pi_x is not the closed-star pencil at x'
        # EVERY plane through p_x is bad, legal or not -- 24 random draws
        for k in range(24):
            r2 = random.Random(SEED + 97 * sd + k)
            bas = [px, v4(r2, 20), v4(r2, 20)]
            if rank(bas) != 3:
                continue
            assert contains(S1, pencil_space(px, span(bas))), \
                'a plane through p_x is NOT bad -- Sigma_x <= rho_bar_1 failed'
        row = row_of(E, x, y, side1, side2, aff)
        assert row is not None, 'the row does not measure'
        assert row['c1'][PIX] == 2, ('c_1(Pi_x) is not 2', row['c1'][PIX])
        assert row['r1'] == 5 and row['a1'] == 0, 'the witness moved'
        assert row['reach'] == min(row['d1'] + row['d2'], 6) \
            + row['a1'] + row['a2'], 'the peel does NOT attain'
        for blk, du in ((PIX, 2), (PIY, 2), (MB, 1), (ALLU, 6)):
            assert margin_at(row, blk, du) <= 0, ('margin > 0', blk)
        hits += 1
        if sd == 0:
            print(f'    seed {sd}: rho_1 = {row["r1"]}, '
                  f'dim(rho_bar_1 cap Sigma_x) = 3, c_1(Pi_x) = 2, '
                  f'c_2(Pi_x) = {row["c2"][PIX]},')
            print(f'      delta = ({row["d1"]},{row["d2"]}), '
                  f'a = ({row["a1"]},{row["a2"]}), reach = {row["reach"]} '
                  f'= min(d1+d2,6)+a1+a2  -- the peel ATTAINS.')
    print(f'  THE HIT: {hits} / {drawn} drawn seeds carry '
          f'`Sigma_x <= rho_bar_1` AS SPACES at rho_1 = 5,')
    print('  in the GENERIC FLAG REGIME, through both gates, at an')
    print('  R-NODE-SHAPED peel.  (PENCIL-SATURATES-GEN) IS FALSE.')
    assert hits == drawn and hits >= min(4, nseed), \
        'the witness did not reproduce'
    # F13 negative control: the SAME peel drawn generically is NOT a hit
    ctrl_bad, ctrl_tot = 0, 0
    from bsatur import draw_peel
    for sd in range(nseed):
        rng = random.Random(SEED + 7919 * sd)
        g = draw_peel(E0, x0, y0, rng)
        if g is None:
            continue
        _P, _B, _pts, aff, _br = g
        S1, r1, _dM, _ = rho_bar_of(side1_0, aff, x0, y0)
        ds = dim(isect(S1, sigma_at(hat(aff[x0]))))
        ctrl_tot += 1
        assert ds == max(1, r1 - 3), ('the generic threshold moved', r1, ds)
        if ds == 3 and r1 <= 5:
            ctrl_bad += 1
    print(f'  F13 NEGATIVE CONTROL: the SAME peel at {ctrl_tot} GENERIC draws '
          f'gives dim = max(1, rho-3) at every one')
    print(f'  and {ctrl_bad} hits -- which is the whole explanation of '
          f'(BE-105)(ii)\'s measurement.')
    assert ctrl_bad == 0, 'the control found a hit -- the audit is wrong'
    print(f'  witness: {time.time() - t0:.1f}s')
    return True


# ======================================================= mode: mech (BE-110)

def proj_lines(pxv, pts_seq):
    """The projected consecutive-pair lines L_j = bar p_{j-1} ^ bar p_j, read
    inside Lambda^2 K^4 as `l_j ^ p_x` -- the image of the chain under the
    projection FROM p_x, which has kernel exactly Sigma_x."""
    out = []
    for i in range(len(pts_seq) - 1):
        lj = wedge2(pts_seq[i], pts_seq[i + 1])
        out.append(wedge3(lj, pxv))
    return out


def wedge3(l, p):
    """l ^ p in Lambda^3 K^4 ~ K^4, for l in Lambda^2 (PL order 01,02,03,12,
    13,23).  Coordinates in the basis (e123, e023, e013, e012) with signs
    fixed so that the map has kernel exactly p ^ K^4."""
    # (a^b)^c, expanded: component I of Lambda^3 omitting index k.
    # l = sum_{i<j} l_ij e_i^e_j ; l ^ p = sum_{i<j,k} l_ij p_k e_i^e_j^e_k.
    idx = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    out = [F(0)] * 4          # coefficient of e_{012}, e_{013}, e_{023}, e_{123}
    tri = {(0, 1, 2): 0, (0, 1, 3): 1, (0, 2, 3): 2, (1, 2, 3): 3}
    for (i, j), lij in zip(idx, l):
        if lij == 0:
            continue
        for k in range(4):
            if k in (i, j) or p[k] == 0:
                continue
            t = tuple(sorted((i, j, k)))
            perm = [i, j, k]
            # sign of the permutation taking (i,j,k) to sorted order
            sgn = 1
            for a in range(3):
                for b in range(a + 1, 3):
                    if perm[a] > perm[b]:
                        sgn = -sgn
            out[tri[t]] += sgn * lij * p[k]
    return out


def run_mech(npath=(3, 4, 5, 6, 7), ndraw=6):
    t0 = time.time()
    print(f'== mech: (BE-110) THE CORANK IDENTITY AND THE rho >= 5 FLOOR, '
          f'seed {SEED}')
    print('  Projection from p_x is the linear map w |-> w ^ p_x on')
    print('  Lambda^2 K^4, whose KERNEL is exactly Sigma_x.  So for ANY side')
    print('        dim(rho_bar cap Sigma_x) = rho - dim(rho_bar ^ p_x),')
    print('  and for a PATH side rho_bar is the chain span, so the image is')
    print('  <L_2, ..., L_L> with L_j the line of the projected pair.')
    print('  ASSERTED below at every draw, together with the two steps of')
    print('  the floor: dim<L_j> = 0 is excluded by `assert_generic_star`,')
    print('  and dim<L_j> = 1 forces EVERY point into one plane with p_x,')
    print('  which caps rho at 3 -- so corank 3 needs rho >= 5.')
    tot, flat = 0, 0
    for L in npath:
        E = _path(L + 1)
        V = [f'v{i}' for i in range(L + 1)]
        x, y = V[0], V[-1]
        for sd in range(ndraw):
            rng = random.Random(SEED + 311 * sd + 17 * L)
            pt = {w: (rng.randint(-6, 6), rng.randint(-6, 6),
                      rng.randint(-6, 6)) for w in V}
            pt = {w: (F(a), F(b), F(c)) for w, (a, b, c) in pt.items()}
            if len(set(pt.values())) != len(V):
                continue
            try:
                assert_generic_star(E, pt)
            except AssertionError:
                continue
            S, rho, _dM, _ = rho_bar_of(E, pt, x, y)
            px = hat(pt[x])
            ds = dim(isect(S, sigma_at(px)))
            seq = [hat(pt[w]) for w in V]
            Ls = proj_lines(px, seq)
            di = rank([r for r in Ls if any(t != 0 for t in r)]) if Ls else 0
            assert ds == rho - di, ('the corank identity fails', L, rho, ds, di)
            assert di >= 1, 'dim<L_j> = 0 survived assert_generic_star'
            if di == 1:
                flat += 1
                assert rank(seq) == 3, \
                    'dim<L_j> = 1 without every point coplanar with p_x'
                assert rho <= 3, ('the flat cap failed', rho)
            if ds == 3:
                assert rho >= 5, ('THE FLOOR IS BROKEN', L, rho, ds)
            tot += 1
    # the two named strata, drawn ON PURPOSE so both steps of the floor run
    flatrows, tailrows = 0, 0
    for L in npath:
        E = _path(L + 1)
        V = [f'v{i}' for i in range(L + 1)]
        x, y = V[0], V[-1]
        for sd in range(ndraw):
            rng = random.Random(SEED + 5501 * sd + 29 * L)
            # (1) FLAT: every point in one plane WITH p_x
            pt = flat_path(V, rng)
            if pt is not None:
                try:
                    assert_generic_star(E, pt)
                except AssertionError:
                    pt = None
            if pt is not None:
                S, rho, _dM, _ = rho_bar_of(E, pt, x, y)
                px = hat(pt[x])
                ds = dim(isect(S, sigma_at(px)))
                Ls = proj_lines(px, [hat(pt[w]) for w in V])
                di = rank([r for r in Ls if any(t != 0 for t in r)]) or 0
                assert ds == rho - di, 'the corank identity fails (flat)'
                assert di == 1 and rho <= 3, ('the flat cap failed', rho, di)
                assert ds <= 2, ('a flat row reached corank 3', ds)
                flatrows += 1
                tot += 1
            # (2) COPLANAR TAIL: p_x and every point but p_{v1} in one plane
            pt = coplanar_tail_path(V, rng)
            if pt is None:
                continue
            try:
                assert_generic_star(E, pt)
            except AssertionError:
                continue
            S, rho, _dM, _ = rho_bar_of(E, pt, x, y)
            px = hat(pt[x])
            ds = dim(isect(S, sigma_at(px)))
            Ls = proj_lines(px, [hat(pt[w]) for w in V])
            di = rank([r for r in Ls if any(t != 0 for t in r)]) or 0
            assert ds == rho - di, 'the corank identity fails (tail)'
            assert di == 2, ('the tail stratum is not corank 2', di)
            assert ds == min(3, rho - 2), ('the tail stratum moved', rho, ds)
            assert rho <= 5, ('the tail stratum reached rho = 6', L, rho)
            if ds == 3:
                assert rho >= 5, 'THE FLOOR IS BROKEN on the tail stratum'
            tailrows += 1
            tot += 1
    print(f'  {tot} legal path draws (L = {min(npath)}..{max(npath)}, '
          f'small-coordinate so degenerate strata are HIT, plus '
          f'{flatrows} FLAT and {tailrows} COPLANAR-TAIL draws):')
    print(f'    `dim(rho_bar cap Sigma_x) = rho - dim<L_j>` ASSERTED at every '
          f'one;')
    print(f'    `dim<L_j> = 1 => all points coplanar with p_x and rho <= 3` '
          f'ASSERTED at {flat + flatrows} rows;')
    print(f'    `dim<L_j> = 2 at the coplanar-tail stratum, dim = min(3,rho-2)`'
          f' ASSERTED at {tailrows} rows;')
    print(f'    `dim(rho_bar cap Sigma_x) = 3 => rho >= 5` ASSERTED at every '
          f'one.')
    print('  THEOREM (BE-110)(ii), PROVED not measured: at a deg-1 terminal')
    print('  whose side is a PATH, Sigma_x <= rho_bar_i forces rho_i >= 5.')
    print(f'  mech: {time.time() - t0:.1f}s')
    return True


# ==================================================== mode: support (BE-111)

def run_support(nseeds=6, ndeg=6):
    t0 = time.time()
    print(f'== support: (BE-111) WHAT (BE-105)(ii)\'s BATTERY RANGES OVER, '
          f'seed {SEED}')
    print('  Read off `bearcase.piece_battery()` and `run_mech`\'s own loop,')
    print('  not off any docstring.')
    one, other = [], []
    for (name, edges, u, v) in piece_battery():
        nb = neighbors(edges)
        (one if len(nb[u]) == 1 else other).append((name, len(nb[u])))
    print(f'  {len(one) + len(other)} pieces; deg(u) = 1 at EXACTLY '
          f'{len(one)} of them, and they are:')
    for (name, _d) in one:
        print(f'    - {name}')
    assert len(one) == 5, 'the battery no longer has 5 deg-1 terminals'
    assert all('path of' in n for (n, _d) in one), \
        'a deg-1 terminal of the battery is not a path piece'
    print('  So the threshold identity\'s SUPPORT is ONE topological family --')
    print('  paths of 3..7 edges -- and inside each piece ONE configuration:')
    print('  `run_mech` keeps the arg-max of rho over <= 6 draws of')
    print('  `sample_piece_config`, whose coordinates are UNIFORM ON A BOX,')
    print('  so every kept configuration is GENERIC.  Sigma_x = p_x ^ K^4')
    print('  does not involve the flag at all, so the quantifier this')
    print('  direction rides is the CONFIGURATION STRATUM, not the flag.')
    # (a) the generic stratum: reproduce the landed identity
    gen = []
    for (name, edges, u, v) in piece_battery():
        nb = neighbors(edges)
        if len(nb[u]) != 1:
            continue
        got = None
        for sd in range(nseeds):
            rng = random.Random(SEED + 7919 * sd + len(name))
            g, _why = sample_piece_config(edges, u, v, rng)
            if g is None:
                break
            pt, _planes = g
            S, r, _dM, _ = rho_bar_of(edges, pt, u, v)
            got = (pt, S, r) if (got is None or r > got[2]) else got
        assert got is not None, ('no draw at', name)
        pt, S, r = got
        ds = dim(isect(S, sigma_at(hat(pt[u]))))
        assert ds == max(1, r - 3), ('the generic threshold moved', name, r, ds)
        gen.append((r, ds))
    print(f'  (a) GENERIC stratum, {len(gen)} pieces: '
          + ', '.join(f'{r}->{d}' for (r, d) in sorted(set(gen))))
    print('      `max(1, rho-3)` ASSERTED -- (BE-105)(ii) REPRODUCED verbatim.')
    # (b) the coplanar stratum: the identity FAILS
    bad = 0
    for L in (5,):
        E = _path(L + 1)
        V = [f'v{i}' for i in range(L + 1)]
        x, y = V[0], V[-1]
        for sd in range(ndeg):
            rng = random.Random(SEED + 4441 * sd)
            pt = coplanar_tail_path(V, rng)
            if pt is None:
                continue
            try:
                assert_generic_star(E, pt)
            except AssertionError:
                continue
            S, rho, _dM, _ = rho_bar_of(E, pt, x, y)
            ds = dim(isect(S, sigma_at(hat(pt[x]))))
            assert rho == 5 and ds == 3, ('the stratum did not fire', rho, ds)
            bad += 1
    print(f'  (b) COPLANAR stratum (p_x, p_2, p_3, p_4, p_5 in one plane, p_1 '
          f'off it), {bad} draws at L = 5:')
    print('      rho = 5 and dim(rho_bar cap Sigma_x) = 3 ASSERTED at every')
    print('      one -- `max(1, rho-3)` is FALSE off the sampler\'s support.')
    assert bad >= min(4, ndeg), 'the coplanar stratum did not reproduce'
    print('  VERDICT.  The `rho = 5 -> 2, never 3` readout is a statement')
    print('  about GENERIC configurations of a PATH piece.  It is true there')
    print('  ((BE-110)(ii) proves it) and false one stratum away.')
    print(f'  support: {time.time() - t0:.1f}s')
    return True


def flat_path(V, rng, s=20, tries=80):
    """A legal path configuration with EVERY point (p_x included) in one
    plane -- the `dim<L_j> = 1` stratum, where rho is capped at 3."""
    for _ in range(tries):
        Ppi = span([v4(rng, s) for _ in range(3)])
        if dim(Ppi) != 3:
            continue
        homs = {w: pt_in(Ppi, rng, s) for w in V}
        if any(h[3] == 0 for h in homs.values()):
            continue
        pt = {w: tuple(F(h[i], h[3]) for i in range(3)) for w, h in homs.items()}
        if len(set(pt.values())) != len(V):
            continue
        return pt
    return None


def coplanar_tail_path(V, rng, s=20, tries=80):
    """A legal path configuration with p_{v0}, p_{v2}, ..., p_{vL} in one
    plane and p_{v1} off it -- (BE-109)'s stratum, read on the bare path."""
    for _ in range(tries):
        Ppi = span([v4(rng, s) for _ in range(3)])
        if dim(Ppi) != 3:
            continue
        homs = {}
        homs[V[0]] = pt_in(Ppi, rng, s)
        for w in V[2:]:
            homs[w] = pt_in(Ppi, rng, s)
        b0 = v4(rng, s)
        if rank(Ppi + [b0]) != 4:
            continue
        homs[V[1]] = b0
        if any(h[3] == 0 for h in homs.values()):
            continue
        pt = {w: tuple(F(h[i], h[3]) for i in range(3)) for w, h in homs.items()}
        if len(set(pt.values())) != len(V):
            continue
        return pt
    return None


# ====================================================== mode: floor (BE-111)

def _arc(E, a, b, L, tag):
    prev = a
    for i in range(L - 1):
        E.append((prev, f'{tag}{i}'))
        prev = f'{tag}{i}'
    E.append((prev, b))


def side_library():
    """Sides carrying a deg-1 terminal `x`, in TWO buckets.

    Bucket A -- `deg_i(y) = 1` as well, so y's side-`i` closed star is TWO
    points and does NOT determine pi_y.  This is the regime-compatible class:
    the (BE-109) witness lives here.

    Bucket B -- `deg_i(y) >= 2`, so y's side-`i` star already spans a plane
    and pi_y is FORCED by side `i` alone.

    Every entry keeps the degree->=3 vertices an INDEPENDENT set, the shape
    restriction `bearcase.sample_piece_config` also imposes; disclosed."""
    A, B = [], []
    for L in (3, 4, 5, 6, 7):
        A.append((f'path L={L}', _path(L + 1), 'v0', f'v{L}'))
    # A: pendants at BOTH ends of a cycle
    for (m, k) in ((6, 3), (8, 4), (8, 3), (10, 5)):
        E = [('x', 'c'), ('d', 'y')]
        _arc(E, 'c', 'd', k, 'p')
        _arc(E, 'c', 'd', m - k, 'q')
        A.append((f'2 pendants + cycle({m}) at distance {k}', E, 'x', 'y'))
    # A: pendants at BOTH hubs of a theta
    for (a, b, c) in ((3, 3, 3), (3, 3, 4), (3, 4, 4), (4, 4, 4), (3, 4, 5)):
        E = [('x', 'c'), ('d', 'y')]
        for tag, L in (('u', a), ('v', b), ('w', c)):
            _arc(E, 'c', 'd', L, tag)
        A.append((f'2 pendants + theta({a},{b},{c})', E, 'x', 'y'))
    # A: pendants at two hubs of a subdivided K4
    for k in (3, 4):
        E = list(subdivided(SKELETONS['K4'], [k] * 6))
        E += [('x', 'A'), ('B', 'y')]
        A.append((f'2 pendants + K4 subdivided x{k}', E, 'x', 'y'))
    # B: ONE pendant, y an interior vertex of the core
    for (m, ) in ((4, ), (6, ), (8, )):
        E = [('x', 'c')]
        _arc(E, 'c', 'y', m // 2, 'p')
        _arc(E, 'c', 'y', m - m // 2, 'q')
        B.append((f'pendant + cycle({m})', E, 'x', 'y'))
    for (a, b, c) in ((3, 3, 3), (3, 3, 4), (3, 4, 4), (4, 4, 4)):
        E = [('x', 'c')]
        for tag, L in (('u', a), ('v', b), ('w', c)):
            _arc(E, 'c', 'y', L, tag)
        B.append((f'pendant + theta({a},{b},{c})', E, 'x', 'y'))
    for k in (2, 3):
        for (a, b) in ((3, 3), (3, 4), (4, 4)):
            E = []
            _arc(E, 'x', 'h', k, 'e')
            _arc(E, 'h', 'y', a, 'u')
            _arc(E, 'h', 'y', b, 'v')
            B.append((f'pendant at distance {k} + theta({a},{b})', E, 'x', 'y'))
    return A, B


def sample_side_config(E, rng, s=20, tries=60, plane=None, off=None):
    """A legal pencil configuration of a side whose degree->=3 vertices form
    an INDEPENDENT set: a point and a plane at each such vertex, every other
    vertex placed inside its (unique) hub neighbour's plane, the rest free.
    `plane` plants the (BE-109) stratum: every point except `off` is drawn
    inside it (inside its intersection with the hub plane where both bind)."""
    nb = neighbors(E)
    V = sorted(verts_of(E), key=str)
    hubs = [z for z in V if len(nb[z]) >= 3]
    for z in hubs:
        if any(w in hubs for w in nb[z]):
            return None
    for w in V:
        if w in hubs:
            continue
        if len([z for z in nb[w] if z in hubs]) > 1:
            return None
    for _ in range(tries):
        homs, Bp, ok = {}, {}, True
        for z in hubs:
            homs[z] = (pt_in(plane, rng, s) if (plane is not None and z != off)
                       else v4(rng, s))
        for z in hubs:
            bas = [homs[z]] + [v4(rng, s) for _ in range(2)]
            if rank(bas) != 3:
                ok = False
                break
            Bp[z] = span(bas)
        if not ok:
            continue
        for w in V:
            if w in homs:
                continue
            hz = [z for z in nb[w] if z in hubs]
            if plane is not None and w != off:
                base = (isect(plane, Bp[hz[0]]) if hz else plane)
                if not base or dim(base) == 0:
                    ok = False
                    break
                homs[w] = pt_in(base, rng, s)
            elif hz:
                homs[w] = pt_in(Bp[hz[0]], rng, s)
            else:
                homs[w] = v4(rng, s)
        if not ok:
            continue
        if any(h[3] == 0 for h in homs.values()):
            continue
        aff = assemble(E, homs)
        if aff is None:
            continue
        return aff
    return None


def side_star_plane(E, aff, z):
    """The plane the SIDE alone forces on the flag at `z`, or None when the
    side's closed star at `z` does not span one (then the flag is free for
    the other side to move -- (BE-70)(ii))."""
    nb = neighbors(E)
    star = [hat(aff[z])] + [hat(aff[w]) for w in nb.get(z, ())]
    if rank(star) != 3:
        return None
    return span([r for r in nullspace([nullspace(star)[0]])])


def run_floor(ndraw=40, sr=(3, 5, 9), nplant=8):
    t0 = time.time()
    print(f'== floor: (BE-110) THE rho <= 4 HUNT, AND THE REGIME GATE, '
          f'seed {SEED}')
    print('  Two sweeps over the side library:')
    print('  (a) DEGENERACY-RICH, coordinate ranges {-3,-5,-9}, so')
    print('      coincidences and coplanarities are HIT, not avoided;')
    print('  (b) PLANTED at the (BE-109) stratum -- every point but the')
    print('      neighbour of x drawn inside ONE plane through p_x.')
    print('  Every draw passes `assert_generic_star` AND')
    print('  `verify_pencil_witness` (via `bdecor.assemble`).  Each row also')
    print('  carries the REGIME PROBE: whether the SIDE alone already forces')
    print('  pi_y, and if so whether p_x lies in it -- because `p_x in pi_y`')
    print('  is exactly what puts the peel OFF the generic flag regime.')
    LA, LB = side_library()
    out = {}
    for tag, lib in (('A (deg_i(y) = 1)', LA), ('B (deg_i(y) >= 2)', LB)):
        census, planted, nodraw = {}, {}, []
        tot, ptot, low, lowoff = 0, 0, 0, 0
        for (name, E, x, y) in lib:
            nb = neighbors(E)
            assert len(nb[x]) == 1, ('no deg-1 terminal', name)
            if tag.startswith('A'):
                assert len(nb[y]) == 1, ('bucket A entry with deg(y) > 1', name)
            else:
                assert len(nb[y]) >= 2, ('bucket B entry with deg(y) = 1', name)
            rows = []
            for sd in range(ndraw):
                rng = random.Random(SEED + 8887 * sd + len(name))
                aff = sample_side_config(E, rng, s=sr[sd % len(sr)])
                if aff is not None:
                    rows.append((aff, census))
            c1 = sorted(nb[x], key=str)[0]
            nplanted = 0
            for sd in range(nplant):
                rng = random.Random(SEED + 331 * sd + 3 * len(name))
                Ppi = span([v4(rng, 20) for _ in range(3)])
                if dim(Ppi) != 3:
                    continue
                aff = sample_side_config(E, rng, s=20, plane=Ppi, off=c1)
                if aff is not None:
                    rows.append((aff, planted))
                    nplanted += 1
            if nplanted == 0:
                nodraw.append(name)
            for (aff, box) in rows:
                S, rho, _dM, _ = rho_bar_of(E, aff, x, y)
                if not S:
                    continue
                ds = dim(isect(S, sigma_at(hat(aff[x]))))
                box[(rho, ds)] = box.get((rho, ds), 0) + 1
                if box is census:
                    tot += 1
                else:
                    ptot += 1
                assert ds >= max(0, rho - 3), 'the modular law is violated'
                if ds == 3 and rho <= 4:
                    low += 1
                    Py = side_star_plane(E, aff, y)
                    if Py is not None and rank(Py + [hat(aff[x])]) == 3:
                        lowoff += 1
        out[tag] = (tot, ptot, census, planted, low, lowoff, nodraw)
        print(f'  bucket {tag}: {len(lib)} topologies, {tot} blind rows, '
              f'{ptot} planted rows.')
        print(f'    the PLANTED stratum drew NOTHING at {len(nodraw)} of '
              f'{len(lib)} topologies -- disclosed, not smoothed:')
        for nm in nodraw:
            print(f'      - {nm}')
        print('    blind   (rho, dim): ' + ', '.join(
            f'({r},{d}): {n}' for (r, d), n in sorted(census.items())))
        print('    planted (rho, dim): ' + ', '.join(
            f'({r},{d}): {n}' for (r, d), n in sorted(planted.items())))
        print(f'    rows with `dim = 3 and rho <= 4`: {low}; of those, '
              f'{lowoff} have p_x INSIDE the plane the side forces on y.')
    tA, pA, _cA, _plA, lowA, _oA, ndA = out['A (deg_i(y) = 1)']
    tB, pB, _cB, _plB, lowB, offB, _ndB = out['B (deg_i(y) >= 2)']
    assert lowA == 0, 'a bucket-A row broke the floor'
    assert tA + pA > 60 and tB + pB > 40, 'the sweep did not reproduce'
    print(f'  VERDICT (F11).  In bucket A -- the only bucket a peel in the')
    print(f'  GENERIC FLAG REGIME can present -- `dim = 3 with rho <= 4` is')
    print(f'  NONE FOUND under a cap of {tA + pA} rows over {len(LA)} '
          f'topologies, never "does not exist";')
    print(f'  and at a PATH side it is IMPOSSIBLE ((BE-110)(ii), proved).')
    print(f'  In bucket B it IS reached -- {lowB} rows at rho = 4 -- but at')
    print(f'  {offB} of them p_x lies in the plane the side itself forces on')
    print('  y, i.e. `p_x in pi_y`: those configurations are OFF the generic')
    print('  flag regime, where the whole block law lives ((BE-98)).')
    print(f'  CAP, disclosed: the planted stratum is drawable at only '
          f'{len(LA) - len(ndA)} of the {len(LA)} bucket-A topologies -- every')
    print('  hub-carrying side rejects it under this sampler, so what the')
    print('  stratum does at a NON-path side is UNMEASURED, not excluded.')
    assert lowB > 0 and offB == lowB, 'the bucket-B regime probe did not hold'
    print(f'  floor: {time.time() - t0:.1f}s')
    return True


# ====================================================== mode: price (BE-112)

def price_jobs(nother=2):
    """(peeled branch = 5, every other branch in {3,4,5}) over the three
    skeletons -- the SAME shape of constructed population BSATUR's scan used,
    restricted to the profiles this construction can place."""
    jobs = []
    K4 = SKELETONS['K4']
    for a in (3, 4, 5):
        for b in (3, 4):
            for c in (3, 4):
                jobs.append(('K4', [5, a, b, c, a, b], 0))
                jobs.append(('K4', [5, a, b, b, c, a], 0))
    for ei in range(1, 6):
        prof = [3] * 6
        prof[ei] = 5
        jobs.append(('K4', prof, ei))
    for name in ('prism', 'K33'):
        sk = SKELETONS[name]
        for k in (3, 4):
            for ei in range(3):
                prof = [k] * len(sk)
                prof[ei] = 5
                jobs.append((name, prof, ei))
    seen, out = set(), []
    for j in jobs:
        key = (j[0], tuple(j[1]), j[2])
        if key in seen:
            continue
        seen.add(key)
        out.append(j)
    return out


def run_price(nseed=2, cap=None):
    t0 = time.time()
    print(f'== price: (BE-112) THE SCAN -- SLACK, NOT A SHORTFALL, '
          f'seed {SEED}')
    print('  Every row is a peel whose side 1 carries (BE-109)\'s degenerate')
    print('  placement, so `Sigma_x <= rho_bar_1` at rho_1 = 5 is ASSERTED at')
    print('  each; then `margin <= 0` at Pi_x, Pi_y, <M>, Lambda^2 K^4 and')
    print('  `reach = min(d1+d2,6)+a1+a2` are ASSERTED too.')
    hist, cc = {}, {}
    rows, tight, shortfall = 0, 0, 0
    jobs = price_jobs()
    if cap:
        jobs = jobs[:cap]
    for (skname, prof, ei) in jobs:
        for sd in range(nseed):
            rng = random.Random(SEED + 613 * sd + 7 * sum(prof) + ei)
            got = degenerate_peel(skname, prof, ei, rng)
            if got is None:
                continue
            E, x, y, side1, side2, aff, _Ppi = got
            row = row_of(E, x, y, side1, side2, aff)
            if row is None:
                continue
            S1 = row['S1']
            assert row['r1'] == 5, ('rho_1 moved', row['r1'])
            assert contains(S1, sigma_at(hat(aff[x]))), \
                'Sigma_x is not inside rho_bar_1 at a scan row'
            assert row['c1'][PIX] == 2, 'c_1(Pi_x) is not 2 at a scan row'
            m = margin_at(row, PIX, 2)
            for blk, du in ((PIX, 2), (PIY, 2), (MB, 1), (ALLU, 6)):
                mm = margin_at(row, blk, du)
                if mm > 0:
                    shortfall += 1
                assert mm <= 0, ('margin > 0 -- A SHORTFALL', skname, prof, blk)
            assert row['reach'] == min(row['d1'] + row['d2'], 6) \
                + row['a1'] + row['a2'], ('the peel does NOT attain',
                                          skname, prof)
            hist[m] = hist.get(m, 0) + 1
            key = (row['c1'][PIX], row['c2'][PIX])
            cc[key] = cc.get(key, 0) + 1
            rows += 1
            tight += 1 if m == 0 else 0
    print(f'  {rows} drawn rows over {len(jobs)} constructed profiles '
          f'({nseed} draws each), EVERY one a bad-configuration row')
    print(f'  (`Sigma_x <= rho_bar_1`, rho_1 = 5).')
    print('  margin at Pi_x: ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(hist.items())))
    print('  (c_1, c_2) at Pi_x: ' + ', '.join(
        f'{k}: {v}' for k, v in sorted(cc.items())))
    print(f'  SHORTFALLS: {shortfall}.  Pi_x exactly TIGHT at {tight} of '
          f'{rows} rows.')
    print('  So the hit is SLACK, exactly as BDOUBLE\'s and BSATUR\'s were:')
    print('  half (B) is NOT refuted by it.  What it costs is measured by')
    print('  (BE-106)(ii)\'s enumeration, unchanged -- what BSIGMA moves is')
    print('  WHICH ROW of that table applies at a GENERIC FLAG.')
    assert rows >= 8 and shortfall == 0, 'the scan did not reproduce'
    print(f'  price: {time.time() - t0:.1f}s')
    return True


# ============================================================= entry point

def run_validate():
    print('== validate: a reduced run of all five modes')
    run_witness(nseed=3)
    print()
    run_mech(npath=(3, 4, 5), ndraw=4)
    print()
    run_support(nseeds=6, ndeg=3)
    print()
    run_floor(ndraw=18, sr=(3, 5), nplant=4)
    print()
    run_price(nseed=1, cap=8)
    return True


MODES = {'witness': run_witness, 'mech': run_mech, 'support': run_support,
         'floor': run_floor, 'price': run_price, 'validate': run_validate}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: bsigma.py [{"|".join(MODES)}]')
        sys.exit(2)
    print(f'--- BSIGMA / {mode} --- seed {SEED} --- exact Q ---')
    MODES[mode]()
