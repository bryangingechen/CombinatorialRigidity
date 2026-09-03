"""
Direction BDEGTWO (ordinal 74) -- DOES half (B)'s item 1 close at side
degree >= 2, and what exactly is missing?  BLINE named two gaps that are
NOT `(*)` ((BE-134)); this direction settles BOTH.

  WHAT BLINE LEFT ((BE-134)), in its own words:
    (i)  there is NO `p_x`-sweep at deg_i(x) >= 2 -- (BE-124)(i) assumes
         `deg_i(x) = 1` inside its own derivation, and at k >= 2 moving
         `p_x` MOVES `pi_x`, so every side-2 neighbour must be re-placed.
         "No lemma in the section covers that."
    (ii) `proper in P^3` is not `proper in the FIBRE`: the fibre is the
         PLANE pi_{c_j} when a side-neighbour is a hub and a LINE when two
         are, while `(*)` permits finitely many bad PLANES.

  THE ANSWER, said at the top, and it is FIVE results.

  (BE-136) THE SWEEP EXISTS AT EVERY k >= 2 -- gap (i) is a WRITE-UP gap,
           not an obstruction.  `n_x` is no longer FREE, but it is
           DETERMINED AND RATIONAL in `q_x`:
           `n_x = (q_{c_1} - q_x) x (q_{c_2} - q_x)`, nonzero off the fixed
           line `q_{c_1} v q_{c_2}`.  Nothing else in (BE-124)(ii)'s
           completion used the pencil's DIMENSION -- only that a plane
           through the fixed side-`i` star exists -- so the rest runs
           verbatim.  The fibre has FOUR shapes, not (BE-134)(ii)'s three:
           A^3 / the plane pi_{c_1} / the line pi_{c_1} cap pi_{c_2}, and
           at k >= 3 the plane pi_x ITSELF, with pi_x CONSTANT along the
           fibre -- a case (BE-134) does not mention.  All four are
           REALIZED as legal chart points here.

  (BE-137) THE EXACT REDUCTION, AND WHY "keep xc_2..xc_k" IS MOOT.
           `Pi_x = p_x ^ L_{jk}` for EVERY pair of side-neighbours, so all
           C(k,2) instances of (BE-127)(ii) are the SAME condition
           `Pi_x cap A != 0`.  Two consequences.  (a) `dim A >= 5` makes
           EVERY `p_x` bad by a one-line count (2 + 5 > 6) -- (BE-130)
           without the Segre analysis.  (b) What (BE-127)(ii) needs is
           `Bad != P^3`, which is STRICTLY WEAKER than `(*)`: at the
           beta-ruling `Lambda^2 pi' <= A` with `L_c <= pi'`, `(*)` FAILS
           while `Bad` is the proper plane `pi'`.  So BLINE refuted a
           condition STRONGER than the route needs -- and the exact
           criterion is closed-form (2x2 minors of a matrix linear in p).

  (BE-138) GAP (ii) IS SETTLED IN CLOSED FORM, at all four fibre shapes.
           A fibre is ENTIRELY bad iff `A` contains a 2-dimensional
           totally singular family adapted to it:
             pi_{c_1}  (one hub) : Bad = P^3  or  Pi_{c_1} <= A;
             pi_x      (k >= 3)  : dim(A cap Lambda^2 pi_x) >= 2;
             the LINE  (two hubs): dim(A cap (M ^ L_c)) >= 3  or
                                   M ^ t_0 <= A for some t_0 in L_c.
           Each is asserted as an IFF against the exact minor test.

  (BE-139) AND THAT IS WHERE THE ARCHITECTURE STOPS.  At k = 1 the pendant
           edge's multiplier `omega` is FREE, which is the whole of
           (BE-114)(i).  At k >= 2 `omega` is DETERMINED by the core
           motion, and the exact relative screw space is
             rho_bar_i = { s(m) + a(m) l_1 : m in r^{-1}(Pi_x) },
           `r(m) = m(c_1) - m(c_2)`, `s(m) = m(y) - m(c_1)`.  The
           `p_x`-free subspace `A` is recovered only by DROPPING the
           constraint `r(m) in Pi_x`, and the sharp replacement
           `A_sharp = s(r^{-1}(Pi_x))` DEPENDS ON `p_x`.  So the technique
           (BE-114)(iii) names -- "a condition on a POINT against a FIXED
           subspace" -- is provably unavailable at k >= 2.

  (BE-140) THE PRICE, MEASURED ALONG THE SWEEP: at the swept chart points
           the relaxed condition holds at EVERY point of the fibre on a
           large fraction of peels, while the clause ITSELF is violated at
           NONE.  The relaxation is vacuous exactly where a generic chart
           point lives.

  MODES.  sweep | exact | fibrebad | sharp | direct | support | validate
          (the last runs all six in one process)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.
"""

import itertools
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, wedge2, rank, nullspace, neighbors, rref     # noqa: E402
from bimage import (contains, dim, isect, lam2, pencil_space,           # noqa: E402
                    plane_at, pt_in, rho_bar_of, span, v4)
from binduc import motion_space                                        # noqa: E402
from bpeel import SKELETONS, rnode_shaped                              # noqa: E402
from bdecor import girth, hcard_ok_piece, hubs_and_branches            # noqa: E402
from bunif import SEED                                                 # noqa: E402
from bsatur import margin_at, row_of, sigma_at                         # noqa: E402
from bsigma import sample_side_config                                  # noqa: E402
from bproper import composite, core_of, free_peel                      # noqa: E402
from bopen import chart_data, sides_of, slide                           # noqa: E402
from bline import longcore_library, rand_line, rand_subspace, star_ok  # noqa: E402
from kbare_common import verts_of, verify_pencil_witness               # noqa: E402

I4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
PIX, PIY, MB = ('Pix',), ('Piy',), ('M',)


# ============================================ K^4-side span, done SAFELY
#
# HAZARD, found this pass and recorded in `notes/scripts/README.md`:
# `bimage.span` is a Lambda^2 K^4 helper.  It special-cases width 6 and
# otherwise returns `nullspace(nullspace(rows))`, which is EMPTY -- i.e.
# dimension 0 -- on any FULL-RANK input of width != 6.  `span(I4)` is `[]`.
# Every K^4-side rank test below therefore goes through `rank`, and
# `k4span` never round-trips a full-rank K^4 space.

def k4span(rows):
    """A basis of the row space of width-4 rows -- safe at full rank."""
    if not rows:
        return []
    if rank(rows) == 4:
        return [r[:] for r in I4]
    return span(rows)


def k4meet(A, B):
    """A cap B for width-4 subspaces, safe when either is all of K^4."""
    if rank(A) == 4:
        return [r[:] for r in B]
    if rank(B) == 4:
        return [r[:] for r in A]
    return isect(A, B)


# ================================================= the reduction's objects

def pi_L(px, pc1, pc2):
    """`Pi_x = p_x ^ L_c`, the 2-space of hinge lines at x along the fixed
    line L_c = p_{c_1} v p_{c_2}."""
    return span([wedge2(px, pc1), wedge2(px, pc2)])


def relaxed_bad(A, px, pc1, pc2):
    """(BE-127)(ii)'s necessary condition, in its (BE-137)(i) form:
    `Pi_x cap A != 0`."""
    if not A:
        return False
    return dim(isect(span(A), pi_L(px, pc1, pc2))) >= 1


def bad_on(A, pc1, pc2, bas):
    """EXACT: is EVERY p of span(`bas`) bad?  Bad(p) says the (6 - dim A)
    x 2 matrix `M(p)_{ij} = f_i(p ^ t_j)` drops rank to <= 1; its entries
    are LINEAR in p, so each 2x2 minor is a QUADRATIC FORM in the
    coordinates of p along `bas`, and the whole of span(`bas`) is bad iff
    every one of them vanishes IDENTICALLY.  No sampling."""
    if not A:
        return False
    fs = nullspace(A)
    if not fs:
        return True                          # A = Lambda^2 K^4
    n = len(bas)
    mon = list(itertools.combinations_with_replacement(range(n), 2))

    def col(t):
        return [[sum(a * b for a, b in zip(f, wedge2(bas[k], t)))
                 for k in range(n)] for f in fs]

    c1, c2 = col(pc1), col(pc2)
    for i in range(len(fs)):
        for j in range(i + 1, len(fs)):
            q = {m: F(0) for m in mon}
            for a in range(n):
                for b in range(n):
                    key = (a, b) if a <= b else (b, a)
                    q[key] += c1[i][a] * c2[j][b] - c1[j][a] * c2[i][b]
            if any(q[m] != 0 for m in mon):
                return False
    return True


def bad_everywhere(A, pc1, pc2):
    """`Bad = P^3` -- the condition (BE-127)(ii) actually has to exclude."""
    return bad_on(A, pc1, pc2, I4)


def tloc(A, M, L):
    """{t in L : M ^ t <= A} -- LINEAR in t, so exact."""
    fs = nullspace(A) if A else []
    if not fs:
        return k4span(L)
    rows = []
    for f in fs:
        for m in M:
            rows.append([sum(a * b for a, b in zip(f, wedge2(m, I4[k])))
                         for k in range(4)])
    T = nullspace(rows)
    if not T:
        return []
    return k4meet(T, k4span(L))


# ======================================= the k >= 2 fibre, from the tower

def fibre_k(E, aff, x, cs):
    """(BE-136)(ii): the `p_x` fibre at deg_i(x) = k >= 2, read off (CH-2)'s
    tower and NOT from a sampler.

    With the core FIXED, `q_x` meets exactly two families of equations:
      * `q_x in pi_{c_j}` for every side-neighbour `c_j` that is a HUB
        (its normal is core data);
      * `n_x . (q_{c_j} - q_x) = 0` for EVERY side-neighbour, which at
        k >= 2 no longer leaves a pencil: `pi_x` must contain the whole
        fixed set {q_{c_1}, .., q_{c_k}}.
    So if the c_j span a LINE (always, at k = 2) then `pi_x` is determined
    by `q_x` and `q_x` is free off that line; if they span a PLANE (k >= 3,
    generically) then `pi_x` is that plane and `q_x` is CONFINED to it.
    Returns (fibre basis, #hub side-neighbours, dim span of the c_j)."""
    nb = neighbors(E)
    fib = [r[:] for r in I4]
    nh = 0
    for c in cs:
        if len(nb[c]) >= 3:
            pic = plane_at(E, aff, c)
            assert pic is not None, 'no closed-star plane at a hub c_j'
            fib = k4meet(fib, pic)
            nh += 1
    W = [hat(aff[c]) for c in cs]
    dW = rank(W)
    if dW >= 3:
        fib = k4meet(fib, k4span(W))
    return fib, nh, dW


def fibre_kind(nh, dW, dfib):
    if dW >= 3:
        return 'plane pi_x (k >= 3)'
    if dfib == 4:
        return 'A^3 (no hub c_j)'
    if nh == 1:
        return 'plane pi_{c_1} (one hub c_j)'
    return 'line pi_{c_1} cap pi_{c_2} (two hub c_j)'


def _arc(E, a, b, L, tag):
    prev = a
    for i in range(L - 1):
        E.append((prev, f'{tag}{i}'))
        prev = f'{tag}{i}'
    E.append((prev, b))


def wide_library():
    """Sides that exercise the TWO fibre shapes `longcore_library` does not
    reach: k >= 3 (the c_j span a plane, so `pi_x` is CONSTANT along the
    fibre) and k = 2 with BOTH side-neighbours hubs (the fibre is a LINE).
    Disclosed as CONSTRUCTED, exactly as BLINE's own library is."""
    out = []
    for (a, b, c) in ((3, 4, 4), (3, 4, 5), (4, 4, 4)):
        E = []
        for tag, L in (('u', a), ('v', b), ('w', c)):
            _arc(E, 'x', 'y', L, tag)
        out.append((f'theta({a},{b},{c}) -- k = 3', E))
    for (a, b, c, d) in ((3, 4, 4, 5), (4, 4, 5, 5)):
        E = []
        for tag, L in (('u', a), ('v', b), ('w', c), ('z', d)):
            _arc(E, 'x', 'y', L, tag)
        out.append((f'K(2,4)-subdivided({a},{b},{c},{d}) -- k = 4', E))
    for (m, mp) in ((2, 2), (2, 3), (3, 3)):
        E = []
        ring = ['x', 'a0', 'a1', 'a2']
        for i in range(4):
            E.append((ring[i], ring[(i + 1) % 4]))
        _arc(E, 'a0', 'y', m, f'e{m}_')
        _arc(E, 'a2', 'y', mp, f'f{mp}_')
        out.append((f'ring(4) at x + tails({m},{mp}) -- BOTH c_j hubs', E))
    return out


def all_jobs():
    return ([(n, E) for (n, E, _x, _y) in longcore_library()]
            + wide_library())


def peel_of(E1t, skname='K33', xy=('A', 'B')):
    """(E, side1, side2, x, y, cs, W, branches) for one k >= 2 side glued
    into a composite peel, or None."""
    pr = [3] * len(SKELETONS[skname])
    E, E1, E2, x, y = composite(skname, pr, xy, E1t)
    ss = sides_of(E, E1, x, y)
    if ss is None:
        return None
    side1, side2 = ss
    cs = sorted(neighbors(side1)[x], key=str)
    if len(cs) < 2:
        return None
    W, branches = hubs_and_branches(E, x, y)
    return E, side1, side2, x, y, cs, W, branches


def sweep_points(job, nseed=2, ntarget=6, skname='K33', xy=('A', 'B')):
    """Yield (aff0, aff2, kind, cs, side1, E, x, y) -- a base chart point of
    the composite and a REBUILT one with `p_x` moved inside its own fibre,
    the whole core held byte-fixed and side 2 re-drawn by (CH-2)'s tower."""
    name, E1t = job
    pk = peel_of(E1t, skname, xy)
    if pk is None:
        return
    E, side1, side2, x, y, cs, W, branches = pk
    pr = [3] * len(SKELETONS[skname])
    for sd in range(nseed):
        rng = random.Random(SEED + 613 * sd + 7 * len(name))
        g = free_peel(skname, pr, xy, E1t, rng)
        if g is None:
            continue
        aff = g[5]
        cd = chart_data(E, aff, W)
        if cd is None:
            continue
        P, B, pts = cd
        fib, nh, dW = fibre_k(E, aff, x, cs)
        kind = fibre_kind(nh, dW, rank(fib))
        pcs = [hat(aff[c]) for c in cs]
        for j in range(ntarget):
            r2 = random.Random(SEED + 9901 * sd + 31 * j + len(name))
            npx = pt_in(fib, r2, 20)
            if npx[3] == 0 or rank([npx] + pcs) != 3:
                continue
            ns = nullspace([npx] + pcs)
            if len(ns) != 1:
                continue
            nBx = nullspace([ns[0]])
            got = slide(E, x, y, side1, W, branches, P, B, pts,
                        npx, nBx, r2)
            if got is None:
                continue
            yield (name, aff, got[3], kind, cs, side1, side2, E, x, y,
                   fib, nh, dW, (name, sd))


# ==================================================== mode: sweep (BE-136)

def run_sweep(nseed=2, ntarget=6):
    t0 = time.time()
    print(f'== sweep: (BE-136) THE `p_x`-SWEEP EXISTS AT k >= 2, seed {SEED}')
    print('  (BE-134)(i): "No lemma in the section covers that."  The')
    print('  missing lemma is built here.  At k >= 2 `n_x` is no longer')
    print('  FREE -- it is DETERMINED, `n_x = (q_c1 - q_x) x (q_c2 - q_x)`')
    print('  -- but it is RATIONAL in q_x and nonzero off the fixed line')
    print('  q_c1 v q_c2, and (BE-124)(ii)\'s completion never used the')
    print('  pencil\'s DIMENSION.  Every target below is REBUILT into a full')
    print('  legal chart point: the whole core byte-fixed, side 2 re-drawn.')
    tot, real, peels, cens, hyp = 0, 0, 0, {}, 0
    seen = set()
    for job in all_jobs():
        name, E1t = job
        pk = peel_of(E1t)
        if pk is None:
            continue
        E, side1, side2, x, y, cs, W, branches = pk
        # (CH-1) ON THE COMPOSITE, before a single target is drawn
        nb = neighbors(E)
        okh, _W, _b, _h = hcard_ok_piece(E, x, y)
        md = min(len(nb[w]) for w in verts_of(E))
        assert okh and md >= 2 and girth(E) >= 4, \
            ('(CH-1) FAILS on the composite', name)
        assert len(nb[x]) >= 3 and len(nb[y]) >= 3, \
            ('a terminal is not a hub of H', name)
        assert y not in nb[x] and rnode_shaped(side2, x, y), \
            ('side 2 is not R-node-shaped at non-adjacent terminals', name)
        hyp += 1
        for row in sweep_points(job, nseed, ntarget):
            (_nm, aff, aff2, kind, cs2, s1, _s2, Ec, xx, yy,
             fib, nh, dW, pkey) = row
            if pkey not in seen:
                seen.add(pkey)
                peels += 1
                cens[kind] = cens.get(kind, 0) + 1
            tot += 1
            ok, _n = verify_pencil_witness(Ec, aff2)
            assert ok, 'the rebuilt k >= 2 point fails the pencil witness'
            assert all(aff2[w] == aff[w] for w in verts_of(s1) if w != xx), \
                'the CORE moved under the k >= 2 slide'
            # the flag at x is DETERMINED by p_x and the fixed c_j
            pix = plane_at(s1, aff2, xx)
            assert pix is not None, 'no flag plane at x after the slide'
            assert rank(pix) == 3 and all(
                rank(pix + [hat(aff2[c])]) == 3 for c in cs2), \
                'pi_x does not carry the fixed side-i star'
            # and the fibre is UNCHANGED (it is core data)
            f2, nh2, dW2 = fibre_k(Ec, aff2, xx, cs2)
            assert (nh2, dW2) == (nh, dW) and rank(f2) == rank(fib), \
                'the fibre moved under its own sweep'
            real += 1
    print(f'  (CH-1) asserted on {hyp}/{hyp} composites (K33 subdivided x3')
    print('  as side 2, glued at two non-adjacent hubs), so every row sits')
    print('  on an irreducible Chart(H) ((BE-123)(iii)).')
    print(f'  peels {peels}, targets REALIZED {real} of {tot} attempted')
    print(f'  fibre kinds over the peels: {dict(sorted(cens.items()))}')
    assert real == tot and real >= 200, 'the k >= 2 sweep did not reproduce'
    assert len(cens) == 4, 'not all four fibre shapes were exercised'
    print('  VERDICT.  (BE-134)(i) is a GAP IN THE WRITE-UP, not an')
    print('  obstruction: the sweep exists at every k >= 2 and at every one')
    print('  of the FOUR fibre shapes -- three of them (BE-134)(ii)\'s, plus')
    print('  the k >= 3 shape it does not mention, where `pi_x` is CONSTANT.')
    print(f'  sweep: {time.time() - t0:.1f}s')
    return real


# ==================================================== mode: exact (BE-137)

def run_exact(ndraw=6, nrand=300):
    t0 = time.time()
    print(f'== exact: (BE-137) THE EXACT REDUCTION, AND WHAT IT REALLY '
          f'NEEDS, seed {SEED}')
    print('  (a) `Pi_x = p_x ^ L_{jk}` for EVERY pair of side-neighbours,')
    print('      so the hand-off\'s "exact k >= 2 reduction keeping')
    print('      xc_2..xc_k" is MOOT: all C(k,2) instances of (BE-127)(ii)')
    print('      are ONE condition, `Pi_x cap A != 0`.')
    print('  (b) `dim A >= 5` makes EVERY p_x bad by 2 + 5 > 6.')
    print('  (c) What the route needs is `Bad != P^3`, STRICTLY WEAKER')
    print('      than `(*)`: the beta ruling separates them.')
    # ---- (a) pair-independence, on real side configurations
    rows, pairs = 0, 0
    for (name, E1t) in all_jobs():
        E = list(E1t)
        nb = neighbors(E)
        cs = sorted(nb['x'], key=str)
        if len(cs) < 2:
            continue
        for sd in range(ndraw):
            rng = random.Random(SEED + 8887 * sd + len(name))
            aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
            if aff is None:
                continue
            px = hat(aff['x'])
            pix = plane_at(E, aff, 'x')
            if pix is None:
                continue
            Pix = pencil_space(px, pix)
            rows += 1
            for i, j in itertools.combinations(range(len(cs)), 2):
                P2 = pi_L(px, hat(aff[cs[i]]), hat(aff[cs[j]]))
                assert dim(P2) == 2 and contains(Pix, P2) and contains(P2, Pix), \
                    ('Pi_x is NOT p_x ^ L_{jk}', name, cs[i], cs[j])
                pairs += 1
    print(f'  (a) `Pi_x = p_x ^ L_{{jk}}` asserted at {pairs} pairs over '
          f'{rows} side configurations')
    # ---- (b) the dimension count
    rng = random.Random(SEED + 5511)
    nb5 = 0
    for _ in range(nrand):
        A = rand_subspace(rng, rng.choice([5, 6]))
        p1, p2 = rand_line(rng)
        assert bad_everywhere(A, p1, p2), 'dim A >= 5 is not universally bad'
        for _ in range(4):
            p = v4(rng, 9)
            if rank([p]):
                assert relaxed_bad(A, p, p1, p2), 'a dim A >= 5 escapee'
        nb5 += 1
    print(f'  (b) `dim A >= 5 ==> every p_x bad` asserted at {nb5} draws '
          f'(2 + 5 > 6; no Segre analysis needed)')
    # ---- (c) `(*)` vs `Bad = P^3`
    agree, cens = 0, {}
    for _ in range(nrand):
        d = rng.choice([0, 1, 2, 3, 4, 5, 6])
        A = rand_subspace(rng, d) if d else []
        p1, p2 = rand_line(rng)
        be = bad_everywhere(A, p1, p2)
        so = star_ok(A, p1, p2) if A else True
        assert not (so and be), '`(*)` held while Bad = P^3'
        cens[(d, so, be)] = cens.get((d, so, be), 0) + 1
        agree += 1
    print(f'  (c) {agree} random (A, L_c): (dim A, `(*)`, Bad = P^3) -> '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cens.items())))
    nbeta, nalpha = 0, 0
    for _ in range(4000):
        p1, p2 = rand_line(rng)
        u = v4(rng, 9)
        if rank([p1, p2, u]) != 3:
            continue
        pi = k4span([p1, p2, u])
        A = lam2(pi)
        assert not star_ok(A, p1, p2), 'the beta ruling did not fail `(*)`'
        assert not bad_everywhere(A, p1, p2), \
            'the beta ruling made Bad = P^3'
        assert bad_on(A, p1, p2, pi), 'the beta plane is not bad'
        nbeta += 1
        t0v = pt_in(k4span([p1, p2]), rng, 9)
        if rank([t0v]):
            Aa = sigma_at(t0v)
            assert not star_ok(Aa, p1, p2) and bad_everywhere(Aa, p1, p2), \
                'the alpha ruling is not universally bad'
            nalpha += 1
        if nbeta >= 30 and nalpha >= 30:
            break
    print(f'      beta ruling (Lambda^2 pi\' <= A, L_c <= pi\'): {nbeta} '
          f'CONSTRUCTED -- `(*)` FAILS, Bad = the PLANE pi\', PROPER')
    print(f'      alpha ruling (Sigma_{{t_0}} <= A, t_0 in L_c): {nalpha} '
          f'CONSTRUCTED -- `(*)` FAILS and Bad = P^3, genuinely vacuous')
    # ---- (d) the recount on BLINE's own 270 rows
    tot, sfail, bfail, rec, dAc = 0, 0, 0, 0, {}
    for (name, E, x, y) in longcore_library():
        nb = neighbors(E)
        cs = sorted(nb[x], key=str)
        core = core_of(E, x)
        for sd in range(10):
            rng2 = random.Random(SEED + 8887 * sd + len(name))
            aff = sample_side_config(E, rng2, s=(3, 5, 9)[sd % 3])
            if aff is None:
                continue
            A, dA, _dM, _r = rho_bar_of(core, aff, cs[0], y)
            p1, p2 = hat(aff[cs[0]]), hat(aff[cs[1]])
            tot += 1
            dAc[dA] = dAc.get(dA, 0) + 1
            so = star_ok(A, p1, p2) if A else True
            be = bad_everywhere(A, p1, p2)
            sfail += int(not so)
            bfail += int(be)
            if (not so) and (not be):
                rec += 1
                assert dA <= 4, 'a dim A >= 5 row recovered -- impossible'
    print(f'  (d) BLINE\'s own population re-audited: {tot} rows, dim A '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dAc.items())))
    print(f'      `(*)` FAILS at {sfail}; `Bad = P^3` at {bfail}; so '
          f'{rec} rows are RECOVERED by the correct condition')
    assert tot >= 250, 'the BLINE population did not reproduce'
    assert bfail == sum(v for k, v in dAc.items() if k >= 5), \
        'Bad = P^3 is not exactly the dim A >= 5 stratum here'
    print('  VERDICT.  `(*)` is SUFFICIENT, NOT NECESSARY, and the gap is')
    print('  invisible to any sampler (the beta ruling is measure zero).')
    print('  But the correction does NOT reach the `dim A >= 5` stratum,')
    print('  which is where (BE-133)(iii) puts a GENERIC chart point at 14')
    print('  of 27 topologies -- so the route stays dead there.')
    print(f'  exact: {time.time() - t0:.1f}s')
    return tot


# ================================================= mode: fibrebad (BE-138)

def run_fibrebad(ntest=300):
    t0 = time.time()
    print(f'== fibrebad: (BE-138) GAP (ii), SETTLED IN CLOSED FORM AT ALL '
          f'FOUR FIBRE SHAPES, seed {SEED}')
    print('  `(*)` bounds Bad in P^3; the fibre can be a PLANE or a LINE.')
    print('  Each criterion below is asserted as an IFF against the exact')
    print('  quadratic-minor test -- no sampling of the fibre.')
    rng = random.Random(SEED + 3301)

    def comb(bas, s=5):
        c = [F(rng.randint(-s, s)) for _ in bas]
        return [sum(c[i] * bas[i][k] for i in range(len(bas)))
                for k in range(len(bas[0]))]

    # ---- one-hub fibre: the plane pi_{c_1}, with L_c NOT inside it
    n1, planted = 0, 0
    for _ in range(40000):
        pc1, pc2 = rand_line(rng)
        u1, u2 = v4(rng, 7), v4(rng, 7)
        if rank([pc1, u1, u2]) != 3:
            continue
        pic = k4span([pc1, u1, u2])
        if rank(pic + [pc2]) != 4:
            continue                          # girth >= 4 gives this: c1 !~ c2
        d = rng.choice([1, 2, 3, 4])
        if rng.random() < 0.5:
            P = pencil_space(pc1, pic)
            A = span(P + [[F(rng.randint(-7, 7)) for _ in range(6)]
                          for _ in range(max(0, d - 2))])
            planted += 1
        else:
            A = rand_subspace(rng, d)
        lhs = bad_on(A, pc1, pc2, pic)
        rhs = bad_everywhere(A, pc1, pc2) or contains(A, pencil_space(pc1, pic))
        assert lhs == rhs, ('one-hub criterion FAILS', dim(A), lhs, rhs)
        n1 += 1
        if n1 >= ntest:
            break
    print(f'  ONE HUB, fibre = pi_{{c_1}}:  pi_{{c_1}} <= Bad  <=>  '
          f'Bad = P^3  or  Pi_{{c_1}} <= A   [{n1}/{n1}, {planted} planted]')

    # ---- k >= 3 fibre: the plane pi_x, with L_c INSIDE it
    n2, planted2 = 0, 0
    for _ in range(40000):
        pc1, pc2 = rand_line(rng)
        u = v4(rng, 7)
        if rank([pc1, pc2, u]) != 3:
            continue
        pix = k4span([pc1, pc2, u])
        d = rng.choice([1, 2, 3, 4, 5])
        if rng.random() < 0.5:
            base = lam2(pix)[:rng.choice([1, 2, 3])]
            A = span(base + [[F(rng.randint(-7, 7)) for _ in range(6)]
                             for _ in range(max(0, d - len(base)))])
            planted2 += 1
        else:
            A = rand_subspace(rng, d)
        lhs = bad_on(A, pc1, pc2, pix)
        rhs = dim(isect(A, lam2(pix))) >= 2
        assert lhs == rhs, ('k >= 3 criterion FAILS', dim(A), lhs, rhs)
        n2 += 1
        if n2 >= ntest:
            break
    print(f'  k >= 3, fibre = pi_x:        pi_x <= Bad  <=>  '
          f'dim(A cap Lambda^2 pi_x) >= 2   [{n2}/{n2}, {planted2} planted]')

    # ---- two-hub fibre: the LINE M = pi_{c_1} cap pi_{c_2}, M cap L_c = 0
    n3, byB, byT, cens = 0, 0, 0, {}
    for _ in range(60000):
        pc1, pc2 = rand_line(rng)
        m1, m2 = rand_line(rng)
        Lc, M = [pc1, pc2], [m1, m2]
        if rank(Lc + M) != 4:
            continue
        ML = span([wedge2(a, b) for a in M for b in Lc])
        if dim(ML) != 4:
            continue
        r = rng.random()
        if r < 0.30:                            # plant M ^ t_0 <= A
            t0v = pt_in(k4span(Lc), rng, 7)
            if rank([t0v]) == 0:
                continue
            A = span([wedge2(m1, t0v), wedge2(m2, t0v)]
                     + [[F(rng.randint(-7, 7)) for _ in range(6)]
                        for _ in range(rng.choice([0, 1, 2]))])
        elif r < 0.55:                          # plant dim(A cap M^L_c) = 3
            A = span([comb(ML) for _ in range(3)])
            if dim(A) != 3:
                continue
        else:
            A = rand_subspace(rng, rng.choice([1, 2, 3, 4]))
        B = isect(A, ML) if A else []
        lhs = bad_on(A, pc1, pc2, M)
        hasT = len(tloc(A, M, Lc)) > 0
        rhs = dim(B) >= 3 or hasT
        assert lhs == rhs, ('two-hub criterion FAILS', dim(A), dim(B), lhs, rhs)
        if lhs:
            byB += int(dim(B) >= 3)
            byT += int(hasT)
        cens[(dim(A), dim(B), lhs)] = cens.get((dim(A), dim(B), lhs), 0) + 1
        n3 += 1
        if n3 >= ntest:
            break
    print(f'  TWO HUBS, fibre = the LINE:  M <= Bad  <=>  '
          f'dim(A cap (M ^ L_c)) >= 3  or  M ^ t_0 <= A   [{n3}/{n3}]')
    print(f'      of the bad-fibre draws, {byB} by the dimension branch and '
          f'{byT} by the ruling branch (both exercised)')
    print('      (dim A, dim(A cap M^L_c), all bad): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cens.items())))
    assert byB >= 1 and byT >= 1, 'a branch of the two-hub criterion is unexercised'
    print('  VERDICT.  Gap (ii) is CLOSED AS A CRITERION at every shape: a')
    print('  fibre is entirely bad exactly when `A` swallows a 2-dimensional')
    print('  TOTALLY SINGULAR family adapted to it (a pencil at c_1, the')
    print('  beta-plane of pi_x, a ruling M ^ t_0) -- or a dimension count')
    print('  forces it.  What is NOT settled here is whether a chart can')
    print('  realize one; that is (BE-140)\'s measurement.')
    print(f'  fibrebad: {time.time() - t0:.1f}s')
    return n1 + n2 + n3


# ==================================================== mode: sharp (BE-139)

def blk(m, idx, w):
    b = 6 * idx[w]
    return m[b:b + 6]


def _sub6(a, b):
    return [a[i] - b[i] for i in range(6)]


def sharp_data(core, aff, c1, c2, y, px):
    """(BE-139)(i): the EXACT relative screw space at deg_i(x) = 2.

    A motion of `side_i` is a motion `m` of the core plus a screw at x with
    `m(x) - m(c_j) in <l_j>`; subtracting, `m(c_1) - m(c_2) in Pi_x`, and
    THAT DETERMINES the multiplier at x.  So

        rho_bar_i = { s(m) + a(m) l_1 : m in N },  N = r^{-1}(Pi_x),

    with `r(m) = m(c_1) - m(c_2)`, `s(m) = m(y) - m(c_1)` and
    `r(m) = a(m) l_1 + b(m) l_2`.  Returns (that image, A_sharp = s(N))."""
    V = sorted(verts_of(core), key=str)
    idx = {w: i for i, w in enumerate(V)}
    ker, _r, nV = motion_space(core, aff)
    l1, l2 = wedge2(px, hat(aff[c1])), wedge2(px, hat(aff[c2]))
    Pix = span([l1, l2])
    assert dim(Pix) == 2, 'the two hinge lines at x coincide'
    fs = nullspace(Pix)
    rows = []
    for m in ker:
        rv = _sub6(blk(m, idx, c1), blk(m, idx, c2))
        rows.append([sum(a * b for a, b in zip(f, rv)) for f in fs])
    Ncoef = nullspace([[rows[i][j] for i in range(len(ker))]
                       for j in range(len(fs))]) if ker else []
    img, Ash = [], []
    for cc in Ncoef:
        m = [sum(cc[i] * ker[i][t] for i in range(len(ker)))
             for t in range(6 * nV)]
        rv = _sub6(blk(m, idx, c1), blk(m, idx, c2))
        sv = _sub6(blk(m, idx, y), blk(m, idx, c1))
        R, piv = rref([[l1[t], l2[t], rv[t]] for t in range(6)])
        assert 2 not in piv, 'r(m) escaped Pi_x'
        a = F(0)
        for ri, pcol in enumerate(piv):
            if pcol == 0:
                a = R[ri][2]
        img.append([sv[t] + a * l1[t] for t in range(6)])
        Ash.append(sv)
    return (span(img) if img else []), (span(Ash) if Ash else [])


def run_sharp(ndraw=6):
    t0 = time.time()
    print(f'== sharp: (BE-139) WHERE THE ARCHITECTURE STOPS, seed {SEED}')
    print('  (BE-114)(i) works because the PENDANT edge xc carries a FREE')
    print('  multiplier.  At k >= 2 the multiplier is DETERMINED by the')
    print('  core motion, and the exact space is the image of')
    print('  N = r^{-1}(Pi_x) -- a subspace that MOVES WITH p_x.  `A` is')
    print('  recovered only by DROPPING that constraint.  Asserted below as')
    print('  an identity of SUBSPACES, with the (dim A, dim A_sharp) loss.')
    tot, ok, loss, drop, rescue = 0, 0, {}, 0, 0
    for (name, E, x, y) in longcore_library():
        nb = neighbors(E)
        cs = sorted(nb[x], key=str)
        if len(cs) != 2:
            continue
        c1, c2 = cs
        core = core_of(E, x)
        for sd in range(ndraw):
            rng = random.Random(SEED + 8887 * sd + len(name))
            aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
            if aff is None:
                continue
            px = hat(aff[x])
            S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
            A, dA, _d2, _r2 = rho_bar_of(core, aff, c1, y)
            IMG, ASH = sharp_data(core, aff, c1, c2, y, px)
            tot += 1
            assert dim(IMG) == rho and contains(S, IMG) and contains(IMG, S), \
                ('the exact k = 2 structure FAILS', name, dim(IMG), rho)
            ok += 1
            assert contains(A, ASH) if ASH else True, \
                'A_sharp is not inside A'
            loss[(dA, dim(ASH))] = loss.get((dA, dim(ASH)), 0) + 1
            drop += int(dim(ASH) < dA)
            rescue += int(dA >= 5 and dim(ASH) <= 4)
    print(f'  {tot} rows over the long-core library; the exact identity')
    print(f'  rho_bar_i = span{{ s(m) + a(m) l_1 : m in r^-1(Pi_x) }}')
    print(f'  ASSERTED at {ok}/{tot}.')
    print('  (dim A, dim A_sharp): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(loss.items())))
    print(f'  A_sharp STRICTLY smaller than A at {drop} of {tot} rows.')
    print(f'  AND THE POSITIVE HALF: `dim A >= 5` (where (BE-137)(ii) makes')
    print(f'  the RELAXED condition vacuous) but `dim A_sharp <= 4` (where')
    print(f'  the SHARP one is not) at {rescue} of {tot} rows -- so the')
    print('  sharp reduction has content exactly where the relaxed one has')
    print('  none.  What it does NOT have is `p_x`-freeness.')
    assert ok == tot and tot >= 40, 'the sharp structure did not reproduce'
    assert rescue >= 1, 'the sharp reduction never beat the relaxed one'
    print('  VERDICT.  The k = 1 case is the DEGENERATE one: `r` imposes no')
    print('  constraint on a pendant, so N = M and A_sharp = A is')
    print('  `p_x`-free.  At k >= 2 the only `p_x`-free object left is A')
    print('  itself, which (BE-137) shows is vacuous at dim A >= 5 -- and')
    print('  the sharp object is NOT `p_x`-free.  So (BE-114)(iii)\'s')
    print('  "a point against a FIXED subspace" is provably unavailable.')
    print(f'  sharp: {time.time() - t0:.1f}s')
    return tot


# =================================================== mode: direct (BE-140)

def run_direct(nseed=2, ntarget=6):
    t0 = time.time()
    print(f'== direct: (BE-140) THE CLAUSE ITSELF ALONG THE SWEEP, seed '
          f'{SEED}')
    print('  The decisive control, and it is what no earlier population')
    print('  could run: at each of the swept k >= 2 CHART points, both the')
    print('  TRUE clause (Pi_x <= rho_bar_i with rho_i <= 5) and the')
    print('  RELAXED necessary condition (Pi_x cap A != 0) are evaluated,')
    print('  and `margin <= 0` is ASSERTED at Pi_x, Pi_y and <M>.')
    print('  DISCLOSED: `row_of` costs seconds a row, so the margin control')
    print('  runs on the FIRST swept point of each peel and the clause')
    print('  evaluation on ALL of them.')
    tot, truebad, relbad, peels, allrel, sh = 0, 0, 0, 0, 0, 0
    dAc, mh, bykind = {}, {}, {}
    for job in all_jobs():
        cur, nrel, nsw = None, 0, 0
        for row in sweep_points(job, nseed, ntarget):
            (name, aff, aff2, kind, cs, s1, s2, E, x, y,
             _fib, _nh, _dW, pkey) = row
            if cur is not None and pkey != cur:
                if nsw:
                    peels += 1
                    allrel += int(nrel == nsw)
                nrel, nsw = 0, 0
            cur = pkey
            core = core_of(s1, x)
            px = hat(aff2[x])
            pix = plane_at(s1, aff2, x)
            if pix is None:
                continue
            Pix = pencil_space(px, pix)
            S, rho, _dM, _r = rho_bar_of(s1, aff2, x, y)
            A, dA, _d2, _r2 = rho_bar_of(core, aff2, cs[0], y)
            tot += 1
            nsw += 1
            dAc[dA] = dAc.get(dA, 0) + 1
            tb = contains(S, Pix) and rho <= 5
            rb = relaxed_bad(A, px, hat(aff2[cs[0]]), hat(aff2[cs[1]]))
            truebad += int(tb)
            relbad += int(rb)
            nrel += int(rb)
            d = bykind.setdefault(kind, [0, 0, 0])
            d[0] += 1
            d[1] += int(rb)
            d[2] += int(tb)
            r = row_of(E, x, y, s1, s2, aff2) if nsw == 1 else None
            if r is not None:
                for b, du in ((PIX, 2), (PIY, 2), (MB, 1)):
                    m = margin_at(r, b, du)
                    if m > 0:
                        sh += 1
                    assert m <= 0, \
                        ('SHORTFALL: margin > 0 -- Phase39 item 0(c)',
                         name, b, m)
                m = margin_at(r, PIX, 2)
                mh[m] = mh.get(m, 0) + 1
        if nsw:
            peels += 1
            allrel += int(nrel == nsw)
    print(f'  {tot} swept chart points over {peels} peels')
    print('  dim A census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dAc.items())))
    print('  per fibre kind (points, relaxed-bad, TRUE-bad):')
    for k in sorted(bykind):
        print(f'    {k}: {tuple(bykind[k])}')
    print(f'  TRUE clause violations: {truebad}')
    print(f'  RELAXED condition holds at: {relbad} of {tot}')
    print(f'  peels whose ENTIRE swept fibre is relaxed-bad: {allrel} of '
          f'{peels}')
    print(f'  margin histogram at Pi_x: {dict(sorted(mh.items()))}; '
          f'shortfalls {sh}')
    assert sh == 0, 'a shortfall was exhibited -- report it as the HEADLINE'
    assert tot >= 200, 'the direct control did not reproduce'
    print(f'  VERDICT (cap disclosure, RESEARCH-ARC section 5).  The clause')
    print(f'  is violated at 0 of {tot} swept chart points -- NOT FOUND')
    print('  UNDER THIS CAP, never "cannot happen".  What IS shown is the')
    print(f'  relaxation\'s cost: at {allrel} of {peels} peels it holds at')
    print('  EVERY point of the fibre, so it can prove properness NOWHERE')
    print('  there, while the clause itself is violated at none of them.')
    print(f'  direct: {time.time() - t0:.1f}s')
    return tot, truebad, relbad


# ========================================================= mode: support

def run_support():
    print('== support: the RESEARCH-ARC section 4 support audit')
    print('  Every population named, with what it VARIES, what it HOLDS')
    print('  FIXED, and which quantifier of its own claim it therefore')
    print('  reaches.  BSATUR\'s sharpening binds: an in-driver assert is')
    print('  only as strong as the distribution it runs under.')
    rowsx = [
        ('sweep / (BE-136)',
         'the target p_x inside its OWN fibre, over 4 fibre shapes',
         'the whole core (byte-fixed); the skeleton and its profile',
         'the EXISTENCE quantifier only -- it is a CONSTRUCTION, and the '
         'four shapes are enumerated from the tower, not sampled'),
        ('exact (a) / (BE-137)(i)',
         'the side configuration and the PAIR (c_j, c_k)',
         'the topology library',
         'the pair quantifier EXHAUSTIVELY (all C(k,2) at every row); the '
         'configuration only by sampling'),
        ('exact (b),(c) / (BE-137)(ii),(iii)',
         'A and L_c at random, plus CONSTRUCTED alpha/beta rulings',
         'nothing -- but random A never meets a ruling (measure zero), '
         'which is exactly why both are BUILT',
         'the `Bad = P^3` test is EXACT (identically-vanishing quadrics), '
         'so it is not a sample at all'),
        ('exact (d) / (BE-137)(iv)',
         'BLINE\'s own 27 topologies x 10 draws x 3 coordinate ranges',
         'the composite skeleton',
         'reproduces (BE-133)(ii) and re-decides each row EXACTLY'),
        ('fibrebad / (BE-138)',
         'A (random AND planted), L_c, and the fibre subspace',
         'nothing; each branch of each criterion is separately planted',
         'the criteria are asserted as IFFs against an EXACT test, so the '
         'draw only chooses WHICH instance is certified'),
        ('sharp / (BE-139)',
         'the side configuration over the long-core library',
         'the k = 2 shape at x',
         'the identity is PROVED; the (dim A, dim A_sharp) census is a '
         'sample and is quoted as one'),
        ('direct / (BE-140)',
         'p_x over its own fibre at real composite chart points',
         'the core, the skeleton, and the seed set',
         'the CONFIGURATION quantifier along one fibre; it does NOT reach '
         'the class, and the 0 violations are a CAP, not a theorem'),
    ]
    for (nm, var, fix, reach) in rowsx:
        print(f'  * {nm}')
        print(f'      varies: {var}')
        print(f'      fixed : {fix}')
        print(f'      reach : {reach}')
    print('  STANDING CAP.  Every population here is CONSTRUCTED (a')
    print('  hand-built side glued into a hand-built composite); no figure')
    print('  is a class-level rate, and none is offered as one.')
    return True


MODES = {'sweep': run_sweep, 'exact': run_exact, 'fibrebad': run_fibrebad,
         'sharp': run_sharp, 'direct': run_direct, 'support': run_support}


def run_validate():
    t0 = time.time()
    for k in ('sweep', 'exact', 'fibrebad', 'sharp', 'direct', 'support'):
        MODES[k]()
        print()
    print(f'== validate: all six modes PASSED [{time.time() - t0:.1f}s]')
    return True


def main(argv):
    if not argv or argv[0] not in MODES and argv[0] != 'validate':
        print(__doc__)
        print('modes: ' + ' | '.join(sorted(MODES)) + ' | validate')
        return 0
    if argv[0] == 'validate':
        run_validate()
        return 0
    MODES[argv[0]]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
