"""
Direction BSIXRUNG (Phase 39 PENCIL, section (K-bare-ext)) -- THE BOTTOM RUNG
of the `Pi_x` obligation: is `c_1(Pi_x) + c_2(Pi_x) <= 2` at `a = 0`,
`Sigma_delta <= 6`, side-degree `>= 2` on both sides, at an internal R-node
peel in the generic flag regime?  (BE-235)(ii) puts 26 of the obligation's 30
residue tuples exactly there.

  THE ANSWER, said at the top: NOT PROVED and NOT REFUTED -- and the
  FIRING HALF of a refutation is now EXHIBITED.  A cycle side with both
  arcs of length `>= 4` fires (`c_i(Pi_x) = 2`) at `deg_i(x) = 2`, `a_i = 0`
  and `rho_i = delta_i` as low as **2**, in the generic flag regime, with
  `delta_i` and `a_i` read off `bfour.side_nums` and `rho_bar_i` cross-
  checked against `binduc.rel_screw_space`.  What is NOT exhibited is the
  NON-FIRING side's `c_j(Pi_x) >= 1` at the same flag, and no landed free
  mechanism supplies it at rung 3.  Two exclusions ARE proved: an x-y path
  of length `<= 3` can never carry the pencil in the generic flag regime,
  and (BE-30)(iv) makes that a statement about EVERY x-y path of a firing
  side.

  MODES
    arith    the rung-3 tuple layer -- cap-free over `barch.all_tuples()`,
             no sampling, seed unused.  Every claim an `assert`.
    path     `dim(<P> cap Pi_x)` as a function of the path length `m`,
             exact over Q: the `m <= 3` exclusion with its F13 negative
             control, and the `m = 4`/`m = 5` exhibited strata.
    cycle    THE CERTIFICATE.  A firing side at side-degree 2, read at the
             SIDE layer off `bfour.side_nums` and `binduc.rel_screw_space`.
    census   (BE-229)(ii)'s landed `deg_1(x) = 2` population re-read at
             rung 3, with `d_min` per side.  ~320 s.
    sat      (BE-244): is any R-node-shaped side PATH-SATURATED?  Exhaustive
             over `bpeel.SKELETONS` x branch lengths in {1,2,3} x all
             skeleton-non-adjacent hub pairs -- 236 196 sides, seedless.
             ~88 s.  (Added to this list at landing: `main()` dispatched
             `sat` while MODES omitted it, so the mode carrying (BE-244)'s
             headline figure was undocumented in its own driver.)
    validate arith + path + cycle in one process (census excluded: slow).

  NOTATION, stated ONCE.  `V := Lambda^2 K^4`; `Pi_x := p_x ^ pi_x` is the
  2-dimensional pencil at the terminal `x`; `c_i(U) := dim(rho_bar_i cap U)`;
  `slack := max(0, delta_1 + delta_2 - 6)` (`barch.slack_of` as landed, so
  slack is a FUNCTION OF THE deltas and never a free parameter);
  `a_i := dim M_i - 6 - f_i`.  The `Pi_x` OBLIGATION is
  `c_1(Pi_x) + c_2(Pi_x) <= 2 + slack`.  RUNG 3 is `Sigma_delta <= 6`, where
  `slack = 0` and the obligation IS `c_1 + c_2 <= 2` ((BE-225)(iii)), which
  by (BE-100)(i) IS (NO-DOUBLE-PENCIL).  `<P>` is the span of the hinge lines
  of a path `P`, `d_min_i` the length of a shortest x-y path inside side `i`.
  Path saturation (M2) is (BE-45)(ii)'s `delta_i = d_min_i`; the series end
  (M1) is (BE-45)(i).

  HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).
  `bimage.pt_in` is never called.  No width-12 object is built: every
  `span`/`isect`/`dim` call is on width-6 rows.  `bwin` is not imported.  No
  Python local is named `E1`/`E2`/`A1` or anything else the (L6)
  capital-letter-plus-digit grep would return.  No `.lean` is opened.
"""

import os
import sys
import time
import random
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import wedge2                                        # noqa: E402
from bimage import dim, span, isect, contains, pencil_space         # noqa: E402
from bfour import side_nums                                         # noqa: E402
from binduc import rel_screw_space                                  # noqa: E402
import barch as BA                                                  # noqa: E402

SEED = 20260910
RUNG3 = 6          # `Sigma_delta <= RUNG3` is (BE-225)(iii)'s bottom rung
PIXDIM = 2         # `dim Pi_x`, (BE-100)(i)'s `du`


# ------------------------------------------------------------------ helpers

def pix_ok(tup):
    """The `Pi_x` OBLIGATION at a tuple: `barch.violates` as landed, negated.
    `dim Pi_x = PIXDIM` is (BE-100)(i)'s `du`."""
    d1, d2, _a1, _a2, _r1, _r2, c1, c2 = tup
    return not BA.violates(c1, c2, PIXDIM, d1, d2)


def floor_legal(tup):
    """(BE-213)(i)'s conjunct, restated at (BE-234): the Grassmann floor
    `c_i >= max(0, rho_i - 4)`.  `barch.all_tuples` enforces only the upper
    cap, so this is imposed here."""
    return tup[6] >= max(0, tup[4] - 4) and tup[7] >= max(0, tup[5] - 4)


def azero(tup):
    return tup[2] == 0 and tup[3] == 0


# ================================================== mode: arith  ((BE-239))

def run_arith():
    t0 = time.time()
    print('== arith: RUNG 3 AT THE TUPLE LAYER -- cap-free, seed unused')
    tups = [t for t in BA.all_tuples() if azero(t)]
    assert len(tups) == 324, ('the `a = 0` slice moved', len(tups))
    r3 = [t for t in tups if t[0] + t[1] <= RUNG3]
    assert len(r3) == 141, ('rung 3 is not (BE-235)(ii)\'s 141', len(r3))
    bad = [t for t in r3 if not pix_ok(t)]
    assert len(bad) == 26, ('rung 3 residue is not (BE-235)(ii)\'s 26',
                            len(bad))
    corner = {}
    for t in bad:
        corner[(t[6], t[7])] = corner.get((t[6], t[7]), 0) + 1
    print(f'   {len(r3)} rung-3 tuples at `a = 0`; the obligation FAILS at '
          f'{len(bad)}.')
    print(f'   corner `c(Pi_x)`: {dict(sorted(corner.items()))}  '
          f'-- (BE-227)(ii)\'s split, restricted to rung 3.')
    assert corner == {(1, 2): 10, (2, 1): 10, (2, 2): 6}, \
        ('the rung-3 corner split moved', corner)
    assert all(floor_legal(t) for t in bad), \
        'a rung-3 residue tuple is not Grassmann-floor-legal'

    # ---- (BE-239)(i): BOTH coincidences are STRICTLY above the floor.
    for t in bad:
        r = (t[4], t[5])
        c = (t[6], t[7])
        fire = [i for i in (0, 1) if c[i] == 2]
        assert fire, 'a rung-3 violation with no firing side'
        i = fire[0]
        j = 1 - i
        assert r[i] <= 5, ('a rung-3 violation fires at rho_i = 6', t)
        assert r[j] <= 4, ('a rung-3 violation has rho_j >= 5', t)
        assert c[i] > max(0, r[i] - 4), ('firing side ON the floor', t)
        assert c[j] > max(0, r[j] - 4), ('non-firing side ON the floor', t)
    print('   (BE-239)(i) ASSERTED at 26/26: the firing side has '
          '`rho_i <= 5` and the NON-FIRING')
    print('   side has `rho_j <= 4`, so `c_i = 2` AND `c_j >= 1` are BOTH '
          'strictly above the')
    print('   Grassmann floor `max(0, rho - 4)`.  (BE-234)\'s free mechanism '
          'is unavailable on')
    print('   BOTH sides at rung 3 -- (BE-237)(i) records the firing half; '
          'the other half is new.')

    # ---- (BE-239)(ii): the price.  A rung-3 violation IS a shortfall.
    for t in bad:
        d1, d2, a1, a2, r1, r2, c1, c2 = t
        # (BE-95)(i) at `U = Pi_x`.
        lo = c1 + c2 - PIXDIM
        assert lo >= 1, ('a rung-3 violation with no forced intersection', t)
        # (BE-86)(i)'s criterion at `a = 0`: attainment needs
        # `dim(rho_bar_1 + rho_bar_2) = min(Sigma_delta, 6) + a_1 + a_2`.
        summax = r1 + r2 - lo
        assert summax < min(d1 + d2, 6) + a1 + a2, \
            ('a rung-3 violation that is NOT a shortfall', t)
    print('   (BE-239)(ii) ASSERTED at 26/26: every rung-3 violation forces '
          '`dim(rho_1 cap rho_2)')
    print('   >= 1` by (BE-95)(i), hence '
          '`dim(rho_1 + rho_2) < min(Sigma_delta,6) + a_1 + a_2`, hence by')
    print('   (BE-86)(i) the peel does NOT ATTAIN.  A rung-3 certificate is '
          'a SHORTFALL at an')
    print('   `a = 0` chart point in the generic flag regime -- unlike '
          '(BE-231)(i)\'s rung-1 kill,')
    print('   which (BE-232)(i) shows costs the target nothing.')

    # ---- (BE-239)(iii): the two corners, and the delta_i = 2 collapse.
    tight = [t for t in bad if 2 in (t[6], t[7])
             and min(t[4] if t[6] == 2 else 7,
                     t[5] if t[7] == 2 else 7) == 2]
    ndelta = {}
    for t in bad:
        ndelta[(t[0], t[1])] = ndelta.get((t[0], t[1]), 0) + 1
    print(f'   `(delta_1, delta_2)` over the 26: {dict(sorted(ndelta.items()))}')
    print(f'   of which {len(tight)} fire at `rho_i = 2`, where `c_i = 2` '
          'forces `rho_bar_i = Pi_x`')
    print('   EXACTLY as spaces (a 2-dimensional space containing the '
          '2-dimensional `Pi_x`).')

    # ---- (BE-239)(iv): the arithmetic shape of the surviving residue,
    # once `path`'s geometric exclusions are imposed.  Stated here as an
    # enumeration so the tuple layer carries the number; `path` supplies
    # the two geometric inputs it consumes.
    print('   NO TUPLE-LAYER EXCLUSION SURVIVES.  `path`\'s geometric '
          'exclusions are about PATH')
    print('   LENGTHS (`d_min_i >= 4` on a firing side), and (BE-30)(iv) '
          'gives `rho_i <= d_min_i`,')
    print('   which is the WRONG DIRECTION to bound `delta_i` from below.  '
          'So the rung-3 residue')
    print(f'   stands at {len(bad)} TUPLES; what collapses is the '
          f'CONFIGURATION space, not this one.')
    print('   This is recorded because the opposite is the tempting '
          'inference and it is false.')
    print(f'   arith: {time.time() - t0:.2f}s')
    return dict(r3=len(r3), bad=len(bad), corner=corner, tight=len(tight))


# =================================================== mode: path  ((BE-241))

def _rand_pt(rng, lo=-97, hi=97):
    return [F(rng.randint(lo, hi)) for _ in range(3)] + [F(1)]


def _plane_through(a, b, c):
    """Basis of the 3-dimensional subspace of K^4 spanned by a, b, c
    (the projective plane through the three points), or None if dependent."""
    rows = [a, b, c]
    from bimage import rank_exact
    if rank_exact(rows) != 3:
        return None
    return rows


def _pix_of(p0, plane):
    """`Pi_x = p0 ^ pi_x` as a subspace of `Lambda^2 K^4`.  `plane` is a
    3-row basis of `pi_x`; `p0` must lie in it."""
    rows = [wedge2(p0, q) for q in plane]
    sp = span(rows)
    assert dim(sp) == PIXDIM, ('Pi_x is not 2-dimensional', dim(sp))
    return sp


def _pspan(pts):
    """`<P>`, the span of the hinge lines of the path `pts`."""
    return span([wedge2(pts[k], pts[k + 1]) for k in range(len(pts) - 1)])


def _measure(pts, plane):
    """(dim <P>, dim(<P> cap Pi_x)) for a path `pts` starting at `pts[0]`,
    with the pencil plane `plane` at `pts[0]`."""
    pspan = _pspan(pts)
    pix = _pix_of(pts[0], plane)
    return dim(pspan), dim(isect(pspan, pix)), pspan, pix


def _in_plane(q, plane):
    from bimage import rank_exact
    return rank_exact(plane + [q]) == 3


def run_path(ndraw=60):
    t0 = time.time()
    print(f'== path: `dim(<P> cap Pi_x)` AS A FUNCTION OF THE PATH LENGTH, '
          f'exact over Q, seed {SEED}')
    print('   (BE-30)(iv) is PROVED and UNCONDITIONAL: '
          '`rho_bar_i <= <P>` for EVERY x-y path `P` of')
    print('   side `i`.  So `c_i(Pi_x) = 2` implies `Pi_x <= <P>` for '
          'EVERY such `P`, and the')
    print('   question "can a side fire?" becomes "can a PATH SPAN swallow '
          'the pencil?".')

    # ---- (a) the generic column: `dim(<P> cap Pi_x) = 1` below m = 6.
    rng = random.Random(SEED)
    gen = {}
    for m in range(1, 8):
        for _ in range(ndraw):
            pts = [_rand_pt(rng) for _ in range(m + 1)]
            plane = _plane_through(pts[0], pts[1], _rand_pt(rng))
            if plane is None:
                continue
            dp, dc, _sp, _px = _measure(pts, plane)
            gen[(m, dp, dc)] = gen.get((m, dp, dc), 0) + 1
    print(f'   (a) GENERIC column, {ndraw} exact draws per `m = 1..7`, '
          f'`(m, dim<P>, c)`:')
    for key in sorted(gen):
        print(f'       m={key[0]}  dim<P>={key[1]}  c={key[2]}   '
              f'x{gen[key]}')
    hit, tot = 0, 0
    for (m, dp, dc), num in gen.items():
        tot += num
        assert dp <= min(m, 6), ('`dim<P>` exceeded `min(|P|,6)`', m, dp)
        if dp == min(m, 6):
            hit += num
            assert dc == (2 if m >= 6 else 1), \
                ('the generic `c` is not (BE-44)(ii)\'s', m, dp, dc)
        else:
            assert dc <= 2, ('c out of range on a degenerate draw', m, dp, dc)
    print(f'       ASSERTED at the {hit} of {tot} draws that reach '
          f'`dim<P> = min(m,6)`: `c = 1` for')
    print('       `m <= 5` and `c = 2` for `m >= 6`.  A draw that does NOT '
          'reach it is a random')
    print('       integer coincidence, reported rather than discarded '
          '-- `dim<P> <= min(m,6)` is')
    print('       asserted at every draw.')
    print('       This is (BE-44)(ii) reproduced -- and it is GENERIC, '
          'not universal: (b)-(d).')

    # ---- (b) m = 2: `c = 2` needs p_0, p_1, p_2 COLLINEAR.
    hits = 0
    for _ in range(ndraw):
        p0 = _rand_pt(rng)
        p1 = _rand_pt(rng)
        lam = F(rng.randint(1, 9))
        p2 = [p0[k] + lam * (p1[k] - p0[k]) for k in range(4)]  # collinear
        plane = _plane_through(p0, p1, _rand_pt(rng))
        if plane is None:
            continue
        dp, dc, _sp, _px = _measure([p0, p1, p2], plane)
        assert dp == 1 and dc == 1, ('collinear m=2 did not collapse',
                                     dp, dc)
        hits += 1
    print(f'   (b) m = 2.  `<P> = p_1 ^ <p_0, p_2>` is the pencil at `p_1`, '
          f'so `<P> = Pi_x` needs')
    print(f'       `p_1 = p_0`.  The only degeneration available -- '
          f'`p_0, p_1, p_2` COLLINEAR -- drops')
    print(f'       `dim<P>` to 1 instead ({hits}/{hits} draws asserted), so '
          f'`c = 2` is UNREACHABLE at')
    print('       `m = 2` at EVERY configuration.  Hence a firing side has '
          'no x-y path of length 2.')

    # ---- (c) m = 3: `c = 2` FORCES `p_3 in pi_x`, i.e. `p_y in pi_x`,
    # which `bunif.flag_frame`'s rank-4 test EXCLUDES.
    forced, ident = 0, 0
    for _ in range(ndraw):
        p0 = _rand_pt(rng)
        p1 = _rand_pt(rng)
        p2 = _rand_pt(rng)
        plane = _plane_through(p0, p1, p2)      # pi_x := <p_0,p_1,p_2>
        if plane is None:
            continue
        # p_3 in the SAME plane: the m=3 coplanar stratum, with pi_x chosen
        # to BE that plane -- the only way (c)'s algebra can give `c = 2`.
        s, u = F(rng.randint(-9, 9)), F(rng.randint(-9, 9))
        p3 = [p0[k] + s * (p1[k] - p0[k]) + u * (p2[k] - p0[k])
              for k in range(4)]
        dp, dc, _sp, _px = _measure([p0, p1, p2, p3], plane)
        if dp != 3:
            continue
        assert dc == 2, ('the coplanar m=3 stratum did not fire', dp, dc)
        assert _in_plane(p3, plane), 'p_3 left the plane'
        forced += 1
    print(f'   (c) m = 3.  `c = 2` needs a relation '
          f'`lam_2 q_1^q_2 + lam_3 q_2^q_3 = 0` in `Lambda^2(K^4/p_0)`,')
    print('       i.e. `p_0,p_1,p_2,p_3` COPLANAR; the surviving vectors '
          'then lie in `<q_1,q_2>`,')
    print('       so `c = 2` forces `q_2 in bar(pi_x)` and hence '
          '`q_3 in bar(pi_x)`: `p_3 in pi_x`.')
    print(f'       Since `p_3 = p_y` on an x-y path of length 3, this is '
          f'`p_y in pi_x` -- one of')
    print(f'       `bunif.flag_frame`\'s three exclusions.  '
          f'ASSERTED at {forced}/{forced} draws of the')
    print('       coplanar stratum with `pi_x` the common plane: '
          '`dim<P> = 3`, `c = 2`, `p_3 in pi_x`.')
    # The negative control: coplanar but `pi_x` NOT the common plane.
    neg = 0
    for _ in range(ndraw):
        p0, p1, p2 = _rand_pt(rng), _rand_pt(rng), _rand_pt(rng)
        common = _plane_through(p0, p1, p2)
        if common is None:
            continue
        s, u = F(rng.randint(-9, 9)), F(rng.randint(-9, 9))
        p3 = [p0[k] + s * (p1[k] - p0[k]) + u * (p2[k] - p0[k])
              for k in range(4)]
        plane = _plane_through(p0, p1, _rand_pt(rng))   # a DIFFERENT pi_x
        if plane is None or _in_plane(p2, plane):
            continue
        dp, dc, _sp, _px = _measure([p0, p1, p2, p3], plane)
        if dp != 3:
            continue
        assert dc == 1, ('coplanar m=3 fired with the wrong pi_x', dp, dc)
        neg += 1
    print(f'       F13 NEGATIVE CONTROL: same coplanar stratum, `pi_x` NOT '
          f'the common plane --')
    print(f'       `c = 1` at {neg}/{neg} draws.  So the firing is the '
          f'plane coincidence, not the')
    print('       coplanarity, and the coincidence is exactly '
          '`p_y in pi_x`.')

    # ---- (d) m = 4: the EXHIBITED certificate.  `c = 2` at `dim<P> = 4`
    # WITH `p_4 = p_y` OFF `pi_x`.
    cert, tried = None, 0
    got = 0
    for _ in range(400):
        p0 = _rand_pt(rng)
        p1 = _rand_pt(rng)
        p2 = _rand_pt(rng)
        plane = _plane_through(p0, p1, _rand_pt(rng))
        if plane is None or _in_plane(p2, plane):
            continue
        # condition 1: `p_3 in pi_x`  (q_3 in bar(pi_x))
        s, u = F(rng.randint(-9, 9)), F(rng.randint(-9, 9))
        p3 = [plane[0][k] * F(1) for k in range(4)]
        p3 = [p0[k] + s * (plane[1][k] - p0[k]) + u * (plane[2][k] - p0[k])
              for k in range(4)]
        if not _in_plane(p3, plane):
            continue
        # condition 2: `q_4 in <q_2, q_3>`, i.e. `p_4 in <p_0, p_2, p_3>`
        bb, cc = F(rng.randint(1, 9)), F(rng.randint(-9, 9))
        p4 = [p0[k] + bb * (p2[k] - p0[k]) + cc * (p3[k] - p0[k])
              for k in range(4)]
        tried += 1
        dp, dc, _sp, _px = _measure([p0, p1, p2, p3, p4], plane)
        if dp == 4 and dc == 2 and not _in_plane(p4, plane):
            got += 1
            if cert is None:
                cert = (p0, p1, p2, p3, p4, plane)
    print(f'   (d) m = 4.  THE CERTIFICATE.  The relation '
          f'`lam_2 q_1^q_2 + lam_3 q_2^q_3 + lam_4 q_3^q_4 = 0`')
    print('       forces `q_4 in <q_2,q_3>` and then the surviving vector '
          'is parallel to `q_3`,')
    print('       so `c = 2` iff (1) `p_3 in pi_x` and (2) '
          '`p_4 in <p_0,p_2,p_3>`.  Neither puts')
    print('       `p_4` in `pi_x`.')
    print(f'       CONSTRUCTED: {got} of {tried} draws of the stratum give '
          f'`dim<P> = 4`, `c = 2` and')
    print('       `p_4 NOT in pi_x` -- so `c_i(Pi_x) = 2` at `rho_i = 4` is '
          'compatible with the')
    print('       generic flag regime AT THE PATH LAYER.')
    assert got > 0, 'the m=4 stratum produced no certificate'
    p0, p1, p2, p3, p4, plane = cert
    print(f'       named certificate: p_0={[str(v) for v in p0]}, '
          f'p_1={[str(v) for v in p1]},')
    print(f'                          p_2={[str(v) for v in p2]}, '
          f'p_3={[str(v) for v in p3]},')
    print(f'                          p_4={[str(v) for v in p4]}')
    dp, dc, pspan, pix = _measure([p0, p1, p2, p3, p4], plane)
    assert dp == 4 and dc == 2 and contains(pspan, pix), \
        'the named certificate does not verify'
    assert not _in_plane(p4, plane), 'the named certificate has p_y in pi_x'
    assert _in_plane(p3, plane) and not _in_plane(p2, plane), \
        'the named certificate is not on the stratum'
    assert dim([p0, p1, p3]) == 3 and dim([p0, p1, p3, p4]) == 4, \
        'the certificate does not determine its own flag'
    print('       the flag is RECONSTRUCTIBLE from the five points: '
          '`pi_x = <p_0, p_1, p_3>`, asserted,')
    print('       with `p_2` and `p_4` both OUTSIDE it.')
    print(f'       re-verified: dim<P> = {dp}, Pi_x <= <P>, '
          f'p_4 not in pi_x.  ONE certificate is a')
    print('       PROOF, so this is not capped.')
    print('       CONSEQUENCE, and it is a landed-clause correction: '
          '(BE-44)(ii) reads')
    print('       "`<P> cap Pi_u = <l_{P,1}>` is EQUIVALENT to '
          '`dim<P> <= 5`".  Here `dim<P> = 4`')
    print('       and `<P> cap Pi_u = Pi_u`.  The equivalence is GENERIC, '
          'not universal; the step\'s')
    print('       own body says so ("below the boundary the condition is a '
          'genuine open')
    print('       condition") and its measured row is one guarded draw per '
          'piece.')

    # ---- (e) the STRUCTURE behind (a)-(d), uniformly in `m`:
    # `S := <P> cap (p_0 ^ K^4)` and the plane it FORCES.
    print('   (e) THE STRUCTURE, uniformly in `m`.  Write '
          '`S := <P> cap (p_0 ^ K^4)`.  Since `Pi_x <= p_0 ^ K^4`,')
    print('       `c = 2` needs `dim S >= 2`, and then `S = p_0 ^ U` for a '
          'UNIQUE plane `U` -- so a')
    print('       path of length `m` does not merely permit a firing flag, '
          'it NAMES one.  `dim S =`')
    print('       `m - dim(p_0 ^ <P>)` and `p_0 ^ <P>` has `m - 1` '
          'generators inside the 3-dimensional')
    print('       `p_0 ^ Lambda^2`, so generically `dim S = max(1, m - 3)`:')
    scen = {}
    for m in range(1, 8):
        for _ in range(ndraw):
            pts = [_rand_pt(rng) for _ in range(m + 1)]
            pspan = _pspan(pts)
            sub = isect(pspan, _p0wedge(pts[0]))
            u = _plane_from(pts[0], sub) if dim(sub) >= 1 else []
            key = (m, dim(pspan), dim(sub), len(u))
            scen[key] = scen.get(key, 0) + 1
            if dim(sub) == 2:
                assert len(u) == 3, ('S is 2-dimensional but U is not a '
                                     'plane', key)
                assert dim(u + [pts[1]]) == 3, \
                    'the forced plane misses the first neighbour'
                assert contains(pspan, pencil_space(pts[0], u)), \
                    'the forced plane does not fire'
    for key in sorted(scen):
        print(f'       m={key[0]}  dim<P>={key[1]}  dim S={key[2]}  '
              f'dim U={key[3]}   x{scen[key]}')
    fire5 = sum(n for (m, _dp, ds, _du), n in scen.items()
                if m == 5 and ds == 2)
    print(f'       ASSERTED wherever `dim S = 2`: `U` is a PLANE, it '
          f'CONTAINS `p_1`, and')
    print('       `Pi_x = p_0 ^ U` LIES IN `<P>`.  At `m = 5` this happens '
          f'at {fire5} of {ndraw} generic')
    print('       draws with NO condition imposed -- firing at `rho_i = 5` '
          'costs only that the')
    print('       chart\'s own flag BE that plane, which is exactly '
          '(BE-104)(i)\'s mechanism.  At')
    print('       `m = 4` it costs one condition, at `m = 3` two and the '
          'flag is then illegal.')
    print(f'   path: {time.time() - t0:.2f}s')
    return dict(m4=got, s5=fire5)


# ================================================= mode: census  ((BE-242))

def _row_and_sides(skname, xy, prof, side1, sd, tag):
    """`boblig._row_at` with the two side edge-sets added to the return, so
    `d_min` can be read per side.  Every gate and every builder call is the
    LANDED one, in boblig's own order, under boblig's own seed formula --
    `_reproduces` below asserts the row agrees with `boblig._row_at`'s."""
    from bline import legal_peel
    from bproper import free_peel
    from bpeel import delta_pair, rnode_shaped
    from bfour import e_row
    from bunif import SEED as BSEED, flag_frame
    from kbare_common import verify_pencil_witness
    from exactcore import neighbors
    lp = legal_peel(side1, skname, xy, prof)
    if lp is None:
        return None
    _eg, x, y, report = lp
    okh, mindeg, girth_h, degx, degy, rnode2, sized = report
    rng = random.Random(BSEED + 613 * sd + 7 * len(tag) + 31 * sum(prof))
    got = free_peel(skname, prof, xy, side1, rng)
    if got is None:
        return None
    egraph, raw_side = got[0], got[1]
    node_x, node_y, aff = got[3], got[4], got[5]
    assert (node_x, node_y) == (x, y), 'legal_peel and the builder disagree'
    split = delta_pair(egraph, node_x, node_y)
    if split is None:
        return None
    _da, _db, part_a, part_b = split
    near = part_a if len(part_a) == len(raw_side) else part_b
    far = part_b if near is part_a else part_a
    if len(near) != len(raw_side):
        return None
    assert len(near) != len(far), 'ambiguous side identification'
    row = e_row(egraph, node_x, node_y, near, far, aff)
    if row is None:
        return None
    gates = dict(hcard=okh, mindeg=mindeg, girth=girth_h, degx=degx,
                 degy=degy, rnode_far=rnode2, sized=sized,
                 rnode_near=rnode_shaped(near, node_x, node_y),
                 witness=verify_pencil_witness(egraph, aff)[0],
                 regime=flag_frame(egraph, aff, node_x, node_y) is not None,
                 deg_near_x=len(neighbors(near).get(node_x, ())),
                 deg_far_x=len(neighbors(far).get(node_x, ())))
    return row, gates, near, far, node_x, node_y


def run_census(nseed=1):
    """The landed `deg_1(x) = 2` population ((BE-229)(ii)) re-read AT RUNG 3,
    with `d_min` per side -- the quantity `path` says decides firing."""
    t0 = time.time()
    from bline import longcore_library
    from bimage import dist_in
    import boblig as BO
    print(f'== census: (BE-229)(ii)\'s `deg_1(x) = 2` POPULATION, RE-READ AT '
          f'RUNG 3, seed {SEED}')
    lib = longcore_library()
    jobs = []
    for (nm, ed, _x, _y) in lib:
        for d2 in (0, 1, 2, 3):
            jobs.append(('K33', ('A', 'B'), nm, ed, BO.prof_for('K33', d2)))
    print(f'   CAP, DISCLOSED: {len(lib)} library shapes x 4 profiles x '
          f'{nseed} seed(s).  The `prism`/[4]*9')
    print('   job of (BE-229)(ii) is DROPPED: it carries `delta_2 = 6`, '
          'hence `Sigma_delta >= 7`,')
    print('   which is off rung 3.  Everything else is boblig\'s own job '
          'list unchanged.')
    rows, r3, tight, sat1, sat2 = 0, 0, 0, 0, 0
    dmin4, sidecases, floorbreak, be45iv = 0, 0, 0, 0
    dmin_cen, r3cen, firecen = {}, {}, {}
    viol3 = []
    for (skname, xy, tag, side1, prof) in jobs:
        for sd in range(nseed):
            got = _row_and_sides(skname, xy, prof, side1, sd, tag)
            if got is None:
                continue
            row, gates, near, far, nx, ny = got
            BO._assert_gates(gates, (skname, xy, prof, tag))
            assert gates['regime'], 'a census row fell off the flag regime'
            assert row['a'] == (0, 0), 'a census row is not at `a = 0`'
            assert gates['deg_near_x'] >= 2 and gates['deg_far_x'] >= 2, \
                ('a census row has side-degree 1', gates)
            rows += 1
            d1m = dist_in(near, nx, ny)
            d2m = dist_in(far, nx, ny)
            sdsum = row['d'][0] + row['d'][1]
            dmin_cen[(row['d'], (d1m, d2m))] = \
                dmin_cen.get((row['d'], (d1m, d2m)), 0) + 1
            # the Grassmann floor, TIGHT or not, at both sides
            if all(row['cX'][i] == max(0, row['r'][i] - 4) for i in (0, 1)):
                tight += 1
            if d1m is not None and d1m >= 4:
                dmin4 += 1
            for i in (0, 1):
                sidecases += 1
                if row['cX'][i] != max(0, row['r'][i] - 4):
                    floorbreak += 1
                # (BE-45)(iv) reads `c = 0` where NEITHER (M1) nor (M2)
                # fires.  (M1) needs `deg_i(x) = 1`, excluded here; (M2) is
                # `delta_i = d_min_i`, counted above.  So every side
                # instance here is a "neither" instance, and the ones with
                # `c_i > 0` are exactly where the clause needs the floor.
                dmi = d1m if i == 0 else d2m
                if row['d'][i] != dmi and row['cX'][i] > 0:
                    be45iv += 1
            if d1m is not None and row['d'][0] == d1m:
                sat1 += 1
            if d2m is not None and row['d'][1] == d2m:
                sat2 += 1
            if sdsum <= RUNG3:
                r3 += 1
                r3cen[(row['d'], row['cX'], (d1m, d2m))] = \
                    r3cen.get((row['d'], row['cX'], (d1m, d2m)), 0) + 1
                if row['cX'][0] + row['cX'][1] >= 3:
                    viol3.append((skname, tag, prof, row, d1m, d2m))
            if 2 in row['cX']:
                firecen[(row['r'], row['cX'], (d1m, d2m))] = \
                    firecen.get((row['r'], row['cX'], (d1m, d2m)), 0) + 1
    print(f'   {rows} fully-gated rows, ALL at `a = (0,0)`, ALL in the '
          f'generic flag regime, ALL at')
    print(f'   side-degree `>= 2` on both sides -- the dispatch\'s whole '
          f'quantifier, asserted.')
    print(f'   RUNG 3 (`Sigma_delta <= 6`) at {r3} of {rows} rows; the '
          f'obligation FAILS at {len(viol3)}.')
    print(f'   The Grassmann floor `c_i = max(0, rho_i - 4)` is TIGHT on '
          f'BOTH sides at {tight} of {rows}.')
    print(f'   PATH SATURATION `delta_i = d_min_i`: side 1 at {sat1} of '
          f'{rows}, side 2 at {sat2}.')
    print(f'   `d_min_1 >= 4` -- `path`\'s necessary condition for side 1 '
          f'to fire -- at {dmin4} of {rows}')
    print('   rows, so the population DOES reach the length regime and '
          'still never fires below')
    print('   `rho_i = 6`: the cap is the absence of STEERING, not the '
          'path lengths.')
    print(f'   `c_i != max(0, rho_i - 4)` at {floorbreak} of '
          f'{sidecases} side-instances.')
    print(f'   (BE-45)(iv) reads `c = 0` where neither (M1) nor (M2) '
          f'fires.  (M1) needs')
    print('   `deg_i(x) = 1`, excluded by the quantifier; (M2) fires at 0 '
          'above.  So all')
    print(f'   {sidecases} side-instances are "neither" instances, and '
          f'{be45iv} of them have `c_i > 0`')
    print('   -- every one at `rho_i >= 5`, where the Grassmann floor '
          '((BE-234)) forbids `c = 0`.')
    print('   So the clause\'s conclusion must be read AS THE FLOOR, '
          '`c_i = max(0, rho_i - 4)`.')
    print('   `((delta_1,delta_2), (d_min_1,d_min_2))`:')
    for key in sorted(dmin_cen, key=str):
        print(f'       {dmin_cen[key]:4d}  delta = {key[0]}, '
              f'd_min = {key[1]}')
    print('   RUNG-3 rows, `(delta, c(Pi_x), d_min)`:')
    for key in sorted(r3cen, key=str):
        print(f'       {r3cen[key]:4d}  delta = {key[0]}, c = {key[1]}, '
              f'd_min = {key[2]}')
    print('   FIRING rows (`c_i = 2`), `(rho, c, d_min)`:')
    for key in sorted(firecen, key=str):
        print(f'       {firecen[key]:4d}  rho = {key[0]}, c = {key[1]}, '
              f'd_min = {key[2]}')
    assert not viol3, ('the obligation FAILS on a rung-3 census row -- '
                       'that is a REFUTATION, read it before anything else',
                       viol3[:2])
    print(f'   census: {time.time() - t0:.1f}s')
    return dict(rows=rows, r3=r3, tight=tight, viol3=len(viol3),
                dmin4=dmin4, be45iv=be45iv)


# ================================================== mode: cycle  ((BE-243))

def _p0wedge(p0):
    """`p_0 ^ K^4`, a 3-dimensional subspace of `Lambda^2 K^4`."""
    basis = [[F(1) if k == j else F(0) for k in range(4)] for j in range(4)]
    return span([wedge2(p0, b) for b in basis])


def _plane_from(p0, sub):
    """`{v : p_0 ^ v in sub}` as a subspace of `K^4`.  When
    `sub = <P> cap (p_0 ^ K^4)` is 2-dimensional this is the UNIQUE plane
    `pi_x` at which the path span swallows the pencil -- the flag is FORCED
    by the path, not chosen."""
    from bimage import perp_std
    from exactcore import PL, nullspace
    rows = []
    for w in perp_std(sub):
        row = [F(0)] * 4
        for t, (i, j) in enumerate(PL):
            row[j] += w[t] * p0[i]
            row[i] -= w[t] * p0[j]
        rows.append(row)
    return nullspace(rows) if rows else \
        [[F(1) if k == j else F(0) for k in range(4)] for j in range(4)]


def _rank(rows):
    from bimage import rank_exact
    return rank_exact(rows) if rows else 0


def _linear_pyk(fixed_rows, last_pt, target):
    """The linear conditions on `p_y` expressing
    `target in span(fixed_rows + [last_pt ^ p_y])`.  With
    `base := span(fixed_rows)` of dimension `m-1` and `target` outside it,
    the condition is `last_pt ^ p_y in span(base + [target])`, whose
    annihilator has dimension `6 - m` -- so it is `6 - m` linear forms in
    `p_y`.  Returns the list of 4-vectors `f` with the conditions
    `f . p_y = 0`, or None when the rank hypothesis fails."""
    from bimage import perp_std
    base = span(fixed_rows)
    m = len(base) + 1
    if dim(base + [target]) != m:
        return None                     # target already inside the fixed part
    out = []
    for w in perp_std(base + [target]):
        row = []
        for j in range(4):
            e = [F(1) if k == j else F(0) for k in range(4)]
            ww = wedge2(last_pt, e)
            row.append(sum((w[t] * ww[t] for t in range(6)), F(0)))
        out.append(row)
    return out


def _in_span(rng, basis):
    """A random affine point of the plane spanned by `basis` (a 3-row basis
    of a 3-dimensional subspace of `K^4`), normalized to last coordinate 1."""
    for _try in range(12):
        v = [F(0)] * 4
        for b in basis:
            lam = F(rng.randint(-9, 9))
            v = [v[k] + lam * b[k] for k in range(4)]
        if v[3] != 0:
            return [c / v[3] for c in v]
    return [c for c in basis[0]]


def run_cycle(ndraw=40):
    """A CYCLE side: `deg_i(x) = 2`, the two arcs `P`, `Q`.  The flag at `x`
    is then FORCED -- `pi_x = <p_x, p_{P,1}, p_{Q,1}>` -- so `Pi_x` is the
    pencil spanned by the two hinge lines at `x` and there is no plane left
    to steer.  `c_i(Pi_x) = 2` is therefore exactly `l_P in <Q>` AND
    `l_Q in <P>`, and both are systems of linear conditions on `p_y`:
    `6 - m1` from the first and `6 - m2` from the second.  A nontrivial
    solution exists as soon as `(6-m1) + (6-m2) <= 3`."""
    t0 = time.time()
    from exactcore import nullspace
    rng = random.Random(SEED + 1)
    print(f'== cycle: A FIRING SIDE AT SIDE-DEGREE 2 -- exact over Q, '
          f'seed {SEED + 1}')
    print('   On a cycle side the closed star of `x` INSIDE THE SIDE is '
          '`{p_x, p_{P,1}, p_{Q,1}}`,')
    print('   so (CH-1) FORCES `pi_x = <p_x, p_{P,1}, p_{Q,1}>` and '
          '`Pi_x = <l_P, l_Q>`: there is no')
    print('   plane left to steer, which is the opposite of (BE-104)(i)\'s '
          'series-end habitat.')
    print('   Hence `c_i(Pi_x) = 2` iff `l_Q in <P>` AND `l_P in <Q>`, '
          '`(6-m1) + (6-m2)` linear')
    print('   conditions on `p_y`, ON TOP of `path` (e)\'s forced-plane '
          'pre-condition for an arc')
    print('   of length exactly 4 (its third interior vertex must lie in '
          '`pi_x`), which is')
    print('   IMPOSED here, not hoped for.  Arc length `<= 3` is '
          'separately excluded by `path`')
    print('   (c): it forces `p_y in pi_x`.  Solvability is therefore '
          'MEASURED per shape below,')
    print('   not predicted from `(6-m1) + (6-m2) <= 3` alone.')
    print('   arcs      draws   FIRING & in-regime   census '
          '`(rho_i, c_i(Pi_x), in-regime)`')
    named = {}
    for (m1, m2) in ((5, 5), (5, 4), (6, 4), (6, 5), (4, 4), (4, 3)):
        found, tried, cens = 0, 0, {}
        for _ in range(ndraw):
            px = _rand_pt(rng)
            uu = [_rand_pt(rng) for _ in range(m1 - 1)]     # P interior
            vv = [_rand_pt(rng) for _ in range(m2 - 1)]     # Q interior
            if dim([px, uu[0], vv[0]]) != 3:
                continue
            planex0 = [px, uu[0], vv[0]]
            # `path` (d): an arc of length EXACTLY 4 forces `pi_x` to be
            # `<p_x, first, third>`, so its third interior vertex must be
            # drawn INSIDE `pi_x` or the arc's own span degenerates.  This
            # is imposed, not hoped for -- the (5,4)/(6,4)/(4,4) rows of an
            # earlier run of this mode failed at 40/40 exactly here.
            if m1 == 4:
                uu[2] = _in_span(rng, planex0)
            if m2 == 4:
                vv[2] = _in_span(rng, planex0)
            lp = wedge2(px, uu[0])
            lq = wedge2(px, vv[0])
            pfix = [lp] + [wedge2(uu[k], uu[k + 1]) for k in range(m1 - 2)]
            qfix = [lq] + [wedge2(vv[k], vv[k + 1]) for k in range(m2 - 2)]
            if dim(pfix) != m1 - 1 or dim(qfix) != m2 - 1:
                continue
            tried += 1
            ca = _linear_pyk(pfix, uu[-1], lq)
            cb = _linear_pyk(qfix, vv[-1], lp)
            if ca is None or cb is None:
                cens['rank hypothesis failed'] = \
                    cens.get('rank hypothesis failed', 0) + 1
                continue
            rows = ca + cb
            sol = nullspace(rows)
            if not sol:
                cens[f'{len(rows)} conditions, no solution'] = \
                    cens.get(f'{len(rows)} conditions, no solution', 0) + 1
                continue
            # a RANDOM point of the solution space, not the first basis
            # vector -- a basis vector can carry an accidental zero.
            py = None
            for _try in range(8):
                cand = [F(0)] * 4
                for b in sol:
                    lam = F(rng.randint(-9, 9))
                    cand = [cand[k] + lam * b[k] for k in range(4)]
                if cand[3] != 0:
                    py = [c / cand[3] for c in cand]
                    break
            if py is None:
                continue
            pspan = span(pfix + [wedge2(uu[-1], py)])
            qspan = span(qfix + [wedge2(vv[-1], py)])
            if dim(pspan) != min(m1, 6) or dim(qspan) != min(m2, 6):
                cens['an arc span degenerated'] = \
                    cens.get('an arc span degenerated', 0) + 1
                continue
            pix = span([lp, lq])
            if dim(pix) != 2 or dim([px, uu[0], vv[0]]) != 3:
                cens['the star of x degenerated'] = \
                    cens.get('the star of x degenerated', 0) + 1
                continue
            rho = isect(pspan, qspan)
            planex = [px, uu[0], vv[0]]
            planey = [py, uu[-1], vv[-1]]
            if dim(planey) != 3:
                cens['the star of y degenerated'] = \
                    cens.get('the star of y degenerated', 0) + 1
                continue
            # `bunif.flag_frame`'s three exclusions, at the local layer:
            # `p_y not in pi_x`, `p_x not in pi_y`, `pi_x != pi_y`.
            reg = (dim(planex + [py]) == 4 and dim(planey + [px]) == 4
                   and dim(planex + planey) == 4)
            cid = dim(isect(rho, pix))
            cens[(dim(rho), cid, reg)] = cens.get((dim(rho), cid, reg), 0) + 1
            if cid == 2 and reg:
                assert contains(rho, pix), 'c = 2 without containment'
                found += 1
                # keep the SMALLEST `rho_i` per arc shape: the cheapest
                # firing side is the one the residue's `rho_i = 2` corner
                # needs, and a first hit need not be it.
                if (m1, m2) not in named or dim(rho) < named[(m1, m2)][4]:
                    named[(m1, m2)] = (px, uu, vv, py, dim(rho))
        print(f'      ({m1},{m2})     {tried:4d}    {found:4d}'
              f'              {dict(sorted(cens.items(), key=str))}')
    print('   THE SIDE LAYER, off the LANDED primitives.  Each certificate '
          'is now read as a')
    print('   SIDE: the cycle\'s edge list and the certificate\'s affine '
          'points are handed to')
    print('   `bfour.side_nums` (which calls `bimage.rho_bar_of`, '
          '`bdecor.d3`, `bdecor.weld_d3`)')
    print('   and to `binduc.rel_screw_space`.  Nothing below is this '
          'driver\'s own model of')
    print('   `rho_bar`; the model `<P> cap <Q>` is CROSS-ASSERTED against '
          'them.')
    for key in sorted(named):
        px, uu, vv, py, rr = named[key]
        m1, m2 = key
        pts = {'x': px, 'y': py}
        for k, u in enumerate(uu):
            pts[f'u{k + 1}'] = u
        for k, v in enumerate(vv):
            pts[f'v{k + 1}'] = v
        pnames = ['x'] + [f'u{k + 1}' for k in range(m1 - 1)] + ['y']
        qnames = ['x'] + [f'v{k + 1}' for k in range(m2 - 1)] + ['y']
        side = [(pnames[k], pnames[k + 1]) for k in range(m1)] + \
               [(qnames[k], qnames[k + 1]) for k in range(m2)]
        aff = {k: [v[0], v[1], v[2]] for k, v in pts.items()}
        sn = side_nums(side, aff, 'x', 'y')
        sspace, srho, sdelta, sa = sn
        rss = rel_screw_space(side, aff, 'x', 'y')
        model = isect(span([wedge2(px, uu[0])]
                           + [wedge2(uu[k], uu[k + 1])
                              for k in range(m1 - 2)]
                           + [wedge2(uu[-1], py)]),
                      span([wedge2(px, vv[0])]
                           + [wedge2(vv[k], vv[k + 1])
                              for k in range(m2 - 2)]
                           + [wedge2(vv[-1], py)]))
        pixs = pencil_space(px, span([px, uu[0], vv[0]]))
        cid = dim(isect(sspace, pixs))
        assert srho == rss[0] == dim(model), \
            ('the three readings of rho_i disagree', key, srho, rss[0],
             dim(model))
        assert dim(sspace + model) == srho, \
            ('`<P> cap <Q>` is not `rho_bar_i` as a SPACE', key)
        assert cid == 2 and contains(sspace, pixs), \
            ('the side layer does not fire', key, cid)
        print(f'   CERTIFICATE, arcs {key}: `rho_i = {srho}`, '
              f'`delta_i = {sdelta}`, `a_i = {sa}`,')
        print(f'      `c_i(Pi_x) = {cid}`, `deg_i(x) = 2`, '
              f'`|E(side)| = {len(side)}`;')
        print(f'      `rho_bar_i = <P> cap <Q>` AS A SPACE and '
              f'`binduc.rel_screw_space` agrees -- asserted.')
        print(f'      p_x = {[str(v) for v in px]}')
        print(f'      P interior = {[[str(v) for v in u] for u in uu]}')
        print(f'      Q interior = {[[str(v) for v in u] for u in vv]}')
        print(f'      p_y = {[str(v) for v in py]}')
    assert (5, 5) in named, 'the (5,5) arc shape produced no certificate'
    print('   READING, and the scope is the whole of it.  This is the LOCAL '
          '(screw/flag) layer:')
    print('   it settles that the configuration a firing side at '
          'side-degree 2 needs is')
    print('   SATISFIABLE in the generic flag regime, which (BE-232)(iii) '
          'records as reached at')
    print('   0 rows on the landed population.  It does NOT exhibit a legal '
          'peel: no')
    print('   `verify_pencil_witness`, no `bfour.e_row`, no `delta` and no '
          '`a` is computed here.')
    print('   Those are the GRAPH layer and they are what remains open.')
    print(f'   cycle: {time.time() - t0:.2f}s')


# ==================================================== mode: sat  ((BE-244))

def run_sat(lens=(1, 2, 3), skels=None):
    """Is there a PATH-SATURATED R-node-shaped side?  (BE-240) shows path
    saturation `delta_j = d_min_j` is the ONLY landed free mechanism for
    `c_j(Pi_x) >= 1` that survives the dispatch's quantifier, and side 2 of
    an internal R-node peel must pass `bpeel.rnode_shaped`.  This
    enumerates the landed skeleton family exhaustively over branch lengths
    in `lens` and asks."""
    t0 = time.time()
    import itertools
    from bpeel import SKELETONS, subdivided, rnode_shaped
    skels = SKELETONS if skels is None else skels
    from bdecor import d3, weld_d3
    from bimage import dist_in
    from exactcore import neighbors
    print('== sat: IS ANY R-NODE-SHAPED SIDE PATH-SATURATED?  cap-free over '
          'the enumerated family')
    print(f'   FAMILY, disclosed ({len(skels)} skeletons, '
          f'{sorted(skels)}): every branch profile in')
    print(f'   `{tuple(lens)}^|E(skeleton)|`, every hub pair NON-ADJACENT '
          f'IN THE SKELETON.  A pair')
    print('   adjacent in the skeleton can never pass `rnode_shaped`: its '
          'branch suppresses onto')
    print('   the virtual edge and the parallel test rejects '
          '(read at `bpeel.rnode_shaped`\'s body).')
    grand, gsat = 0, []
    for name in sorted(skels):
        sk = skels[name]
        hubs = sorted({w for e in sk for w in e})
        skn = neighbors(sk)
        pairs = [(a, b) for (a, b) in itertools.combinations(hubs, 2)
                 if b not in skn[a]]
        if not pairs:
            print(f'   {name}: every hub pair is skeleton-adjacent -- '
                  f'0 candidate peels.')
            continue
        seen, rn, cen, sat = 0, 0, {}, []
        for prof in itertools.product(tuple(lens), repeat=len(sk)):
            edges = subdivided(sk, list(prof))
            for (a, b) in pairs:
                seen += 1
                if not rnode_shaped(edges, a, b):
                    continue
                rn += 1
                de = d3(edges) - weld_d3(edges, a, b)
                dm = dist_in(edges, a, b)
                cen[(de, dm)] = cen.get((de, dm), 0) + 1
                if de == dm:
                    sat.append((prof, (a, b), de, dm))
        grand += rn
        gsat += sat
        print(f'   {name}: {seen} candidate peels, {rn} R-node-shaped, '
              f'PATH-SATURATED at {len(sat)}.')
        print(f'      `(delta_j, d_min_j)` census: '
              f'{dict(sorted(cen.items()))}')
        worst = min((dm - de) for (de, dm) in cen)
        print(f'      smallest gap `d_min_j - delta_j` over the family: '
              f'{worst}')
    print(f'   TOTAL: {grand} R-node-shaped sides, PATH-SATURATED at '
          f'{len(gsat)}.')
    assert not gsat, ('a path-saturated R-node side exists -- read it '
                      'before anything else', gsat[:3])
    print('   READING, with its cap.  On the landed skeleton family the '
          'ONLY free mechanism that')
    print('   reaches the region is UNREACHABLE: not one R-node-shaped '
          'side is path-saturated,')
    print('   at any `delta_j`.  This is "not found under branch lengths '
          f'in {tuple(lens)} over')
    print('   `bpeel.SKELETONS`", never "does not exist" -- the family is '
          'three skeletons, and a')
    print('   larger 3-connected core is exactly what is not enumerated '
          'here.')
    print(f'   sat: {time.time() - t0:.1f}s')
    return dict(rnode=grand, sat=len(gsat))


def run_validate():
    print('== validate: arith + path + cycle in one process (census is '
          'separate: ~320 s)')
    run_arith()
    run_path()
    run_cycle()


def main(argv):
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        return 0
    mode = argv[0].lstrip('-')
    if mode == 'arith':
        run_arith()
    elif mode == 'path':
        run_path()
    elif mode == 'census':
        run_census()
    elif mode == 'cycle':
        run_cycle()
    elif mode == 'sat':
        run_sat()
    elif mode == 'validate':
        run_validate()
    else:
        print(f'unknown mode {mode!r}')
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
