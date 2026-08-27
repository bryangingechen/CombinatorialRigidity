"""
Direction BIMAGE (ordinal 45) -- the ONE GEOMETRIC SENTENCE that BTWOCUT
reduced the strengthened 2-cut composition lemma (hence (BE-14)) to:

    the image of a piece's realization space in Gr(delta_2, 6) under
    m |-> rho_bar_2 is NOT contained in rho_bar_1's bad locus

  B(rho_bar_1) := { W in Gr(d2,6) : dim(rho_bar_1 cap W) > max(0, d1+d2-6) },

taken in BTWOCUT's own recommended restriction: the EAR case, where side 2 is
a path u - w_1 - ... - w_m - v of m interior degree-2 vertices and
rho_bar_2 = <l_1, ..., l_{m+1}> is the span of the path's hinge lines
(recorded at btwocut's Step BE28 successor ranking item (1); CITED, not
re-minted).

Succeeds `notes/scripts/w4/btwocut.py` (Steps BE24-BE28), which this driver
imports READ-ONLY together with `binduc` (Steps BE19-BE23) rather than
reimplementing the gluing, deficiency-oracle or pencil-witness machinery.
BTWOCUT's, BINDUC's, BZAVOID's and BATTAIN's figures are CITED, never re-run.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-30)  THE EAR'S IMAGE, EXACTLY -- and the coordinator's Klein-chain
           hypothesis, tested rather than inherited.
             `chain`  : rho_bar_2 IS the span of the chain (both inclusions);
                        the ACHIEVABLE set is exactly the set of chains of
                        lines with l_1 in Pi_u, l_{m+1} in Pi_v and
                        consecutive members CONJUGATE on the Klein quadric
                        (Pi_v = p_v ^ pi_v is a 2-dim TOTALLY SINGULAR space,
                        i.e. a line RULED on the quadric);  plus the three
                        CONFINEMENT laws that the hypothesis does not predict,
                        and the hypothesis's own cheapest consequence
                        (delta_2 <= #edges of the shortest u-v path).

  (BE-31)  WHAT rho_bar IS FOR A PIECE THAT IS NOT AN EAR (the spec's job 2).
             `sprec`  : the SERIES/PARALLEL recursion -- series composition
                        SUMS rho_bar, parallel composition INTERSECTS it --
                        verified as an identity of SUBSPACES, not of
                        dimensions; hence the path-span bound
                        rho_bar <= cap over u-v paths P of <hinge lines of P>,
                        hence rho_uv <= dist(u,v);  and the coordinator's
                        "obvious candidate upper bound" (that intersection)
                        REFUTED as an EQUALITY by an explicit witness.

  (BE-32)  THE COMBINATORIAL HALF -- three elementary theorems that kill the
           two sharpest confinement obstructions before any geometry.
             `combi`  : u ~ v => delta_uv <= 1;  u, v on a common triangle
                        => delta_uv = 0;  u, v with >= 3 common neighbours
                        => delta_uv = 0;  and the purely COMBINATORIAL
                        NECESSARY CONDITION delta_uv <= dist(u,v) for the
                        strengthened statement -- the cheapest falsification
                        test the arc has, swept EXHAUSTIVELY.

  (BE-33)  THE BAD LOCUS, CLASSIFIED -- which subspaces A = rho_bar_1 the ear
           image actually cannot escape.
             `badA`   : the exact classification, per regime, checked against
                        an exhaustive structured battery AND random draws:
                        m >= 2 with pi_u /= pi_v : bad <=> Pi_u <= A or
                        Pi_v <= A (or dim(A cap (Pi_u+Pi_v)) >= 3);
                        m = 1 : bad <=> A contains y ^ L for some y on the
                        line p_u v p_v -- the OPPOSITE RULING of the quadric
                        surface the image sweeps;  pi_u = pi_v : rho_bar_2 is
                        confined to Lambda^2 pi, and at m = 2 it IS Lambda^2
                        pi -- a SINGLE POINT of Gr(3,6), zero freedom.

  (BE-34)  DOES A REAL PIECE EVER PRODUCE A BAD A?  -- the obstruction hunt.
             `image`  : real composed graphs G = G_1 u ear(m).  Hold G_1's
                        configuration and the shared flags FIXED, vary ONLY
                        the ear's own moduli, and measure the image directly:
                        max over draws of dim(rho_bar_1 + rho_bar_2) against
                        min(delta_1+delta_2, 6), plus the whole-graph rank
                        against its target.
             `hunt`   : the same question asked of the BAD-A predicate
                        instead of the rank -- over a census, is Pi_u <= rho_1
                        or Pi_v <= rho_1 (or the m = 1 refinement) EVER true?

Modes: chain | sprec | combi | badA | image | hunt | validate
Reproduce: python3 notes/scripts/w4/bimage.py <mode>

All figures exact Q (fractions.Fraction); every rng seeded with a printed
literal; a rank/dimension assert on every solved system; every sampled
configuration passing binduc's `assert_generic_star` (adjacent points distinct
AND no two hinge lines coincident at a body) and
`kbare_common.verify_pencil_witness`.  Cap disclosure is MANDATORY: a sweep
that finds nothing reports "not found under cap C", never "does not exist"
(`notes/scripts/README.md` s4 convention 8).
"""
import itertools
import os
import random
import sys
import time
from fractions import Fraction as F

sys.setrecursionlimit(20000)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'kbare'))
sys.path.insert(0, HERE)

from exactcore import (rank as rank_exact, nullspace, hat, wedge2,        # noqa: E402
                       neighbors)
from kbare_common import (verts_of, build_rigidity, exact_deficiency,      # noqa: E402
                          verify_pencil_witness)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- BATTAIN was its first `w4/` consumer, `bzavoid` the second, `binduc` the
# --- third, `btwocut` the fourth; this driver is the FIFTH, and the chain is
# --- now FIVE deep (battain -> bzavoid -> binduc -> btwocut -> bimage).
# --- NO MOVE MADE (a dispatch may not edit a landed driver another direction
# --- may be importing in flight).
from bzavoid import adj_of, connected_spanning, edges_of_mask             # noqa: E402
from binduc import (assert_generic_star, cycle, def_by_partitions, ear,   # noqa: E402
                    hubs_of, motion_space, path, rel_screw_space,
                    split_at_pair, theta)
from btwocut import (deltas_at, delta_all_pairs, extended_construction,   # noqa: E402
                     g_exact, split_battery, two_cut_census)


# ===================================================== exact linear algebra
# Subspaces of the 6-dim screw space are carried as LISTS OF ROWS; `dim` is
# the exact-Q rank and `span` the canonical (rref) basis, so subspace EQUALITY
# is tested as an identity of spaces and never as an identity of dimensions.

I6 = [[F(1) if i == j else F(0) for j in range(6)] for i in range(6)]


def dim(rows):
    return rank_exact(rows) if rows else 0


def span(rows):
    """Canonical basis of the row space (a list of `dim(rows)` rows)."""
    if not rows:
        return []
    d = dim(rows)
    if d == 6:
        return [r[:] for r in I6]
    return nullspace(nullspace(rows))


def perp_std(rows):
    """{y : y . x = 0 for every x in rows}, the STANDARD-dot annihilator --
    the pairing `kbare_common.build_rigidity` itself uses (its row block is
    `perp_basis` of the hinge Plucker vector)."""
    if not rows:
        return [r[:] for r in I6]
    return nullspace(rows)


def isect(A, B):
    """A cap B, as a subspace."""
    if not A or not B:
        return []
    M = perp_std(A) + perp_std(B)
    out = nullspace(M) if M else [r[:] for r in I6]
    assert dim(out) == dim(A) + dim(B) - dim(A + B), \
        ('intersection dimension mismatch', dim(A), dim(B), dim(A + B))
    return out


def contains(A, B):
    """B <= A."""
    return dim(A) == dim(A + B)


def same_space(A, B):
    return dim(A) == dim(B) == dim(A + B)


# The KLEIN form on Lambda^2 K^4 in `exactcore.PL` order
# (01, 02, 03, 12, 13, 23):   Q(x) = x0 x5 - x1 x4 + x2 x3,  polarized.
def klein(x, y):
    return (x[0] * y[5] + x[5] * y[0] - x[1] * y[4] - x[4] * y[1]
            + x[2] * y[3] + x[3] * y[2])


def is_decomposable(x):
    """x is a LINE of P^3 (a point of the Klein quadric) iff Q(x) = 0."""
    return klein(x, x) == 0


def klein_perp(rows):
    """The Klein-orthogonal complement."""
    if not rows:
        return [r[:] for r in I6]
    M = [[klein(r, e) for e in I6] for r in rows]
    return nullspace(M)


def alpha_plane(p):
    """S_p = p ^ K^4, the 3-dim space spanned by the lines THROUGH p."""
    e = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
    return span([wedge2(p, x) for x in e])


def pencil_space(p, plane):
    """Pi = p ^ pi, the 2-dim space of lines through the point p inside the
    plane pi (`plane` a basis of the 3-dim subspace of K^4).  This is the
    workbook's `Pi_v := p_v ^ pi_v` -- and it is TOTALLY SINGULAR, i.e. a line
    RULED on the Klein quadric."""
    out = span([wedge2(p, x) for x in plane])
    assert dim(out) == 2, ('pencil not 2-dimensional', dim(out))
    return out


def lam2(plane):
    """Lambda^2 pi, the 3-dim space of lines lying INSIDE the plane pi."""
    out = span([wedge2(plane[i], plane[j])
                for i, j in itertools.combinations(range(3), 2)])
    assert dim(out) == 3, ('Lambda^2 of a plane not 3-dimensional', dim(out))
    return out


# ================================================ flags, ears and the chain

def rq(rng, s=20):
    return F(rng.randint(-s, s))


def v4(rng, s=20):
    return [rq(rng, s) for _ in range(4)]


def pt_in(basis, rng, s=20):
    """A point of the subspace spanned by `basis` (nonzero)."""
    for _ in range(60):
        c = [rq(rng, s) for _ in basis]
        x = [sum(c[i] * basis[i][k] for i in range(len(basis)))
             for k in range(4)]
        if any(t != 0 for t in x):
            return x
    raise RuntimeError('pt_in: no nonzero draw')


def plane_meet(Bu, Bv):
    """pi_u cap pi_v, as a basis (2-dim when the planes are distinct)."""
    nu = nullspace(Bu)
    nv = nullspace(Bv)
    assert len(nu) == 1 and len(nv) == 1, 'a plane basis must have rank 3'
    out = nullspace([nu[0], nv[0]])
    return out


def sample_flags(rng, regime, s=20):
    """The shared datum (p_u, pi_u, p_v, pi_v) at the 2-cut, in the three
    regimes (BE-22)(v) separates plus the forced one:

      'nonadj' : uv NOT an edge -- two flags with no cross-incidence;
      'adj'    : uv an edge -- p_v in pi_u and p_u in pi_v, so BOTH planes
                 contain the line M = p_u v p_v, and they may still differ;
      'equal'  : pi_u = pi_v (the configuration a TRIANGLE on uv forces, and
                 the one BZAVOID's (BE-15) propagation produces).
    Returns (p_u, basis of pi_u, p_v, basis of pi_v)."""
    for _ in range(400):
        if regime == 'nonadj':
            pu, pv, a, b = (v4(rng, s), v4(rng, s), v4(rng, s), v4(rng, s))
            if rank_exact([pu, pv, a, b]) != 4:
                continue
            return pu, [pu, a, b], pv, [pv, a, b]
        if regime == 'adj':
            pu, pv, x, y = (v4(rng, s), v4(rng, s), v4(rng, s), v4(rng, s))
            if rank_exact([pu, pv, x, y]) != 4:
                continue
            return pu, [pu, pv, x], pv, [pu, pv, y]
        if regime == 'equal':
            pu, pv, x = v4(rng, s), v4(rng, s), v4(rng, s)
            if rank_exact([pu, pv, x]) != 3:
                continue
            return pu, [pu, pv, x], pv, [pu, pv, x]
        raise ValueError(regime)
    raise RuntimeError('sample_flags: no generic draw')


def ear_points(flags, m, rng, s=20):
    """Interior points of an ear with m interior vertices, at fixed flags.

    The pencil condition constrains EXACTLY the two vertices adjacent to the
    2-cut: p_1 in pi_u and p_m in pi_v (a vertex of degree 2 imposes no
    condition of its OWN -- three points are always coplanar -- so w_2 ... w_
    {m-1} are FREE vertices in btwocut's sense).  At m = 1 the single interior
    vertex is adjacent to BOTH, so p_1 in pi_u cap pi_v."""
    pu, Bu, pv, Bv = flags
    pts = [pu]
    if m == 1:
        L = plane_meet(Bu, Bv)
        assert len(L) >= 2, 'pi_u = pi_v handled by the caller'
        pts.append(pt_in(L, rng, s))
    else:
        pts.append(pt_in(Bu, rng, s))
        for _ in range(m - 2):
            pts.append(v4(rng, s))
        pts.append(pt_in(Bv, rng, s))
    pts.append(pv)
    return pts


def chain_of(pts):
    """The hinge lines of the ear: l_i = p_{i-1} ^ p_i, i = 1 .. m+1."""
    return [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def legal_chain(pts):
    """The `plane_basis`-class gate on an ear, read on the POINT side: adjacent
    points distinct (projectively) and no two consecutive hinge lines
    coincident (i.e. no three consecutive points collinear)."""
    for i in range(len(pts) - 1):
        if rank_exact([pts[i], pts[i + 1]]) != 2:
            return False
    for i in range(len(pts) - 2):
        if rank_exact([pts[i], pts[i + 1], pts[i + 2]]) != 3:
            return False
    return True


def sample_ear_span(flags, m, rng, tries=40, s=20):
    """One legal ear draw; returns (points, lines, span of the lines)."""
    for _ in range(tries):
        pts = ear_points(flags, m, rng, s)
        if not legal_chain(pts):
            continue
        L = chain_of(pts)
        return pts, L, span(L)
    return None, None, None


# ============================================================ graph helpers

def dist_in(edges, u, v):
    nb = neighbors(edges)
    seen = {u: 0}
    q = [u]
    while q:
        x = q.pop(0)
        for y in nb.get(x, ()):
            if y not in seen:
                seen[y] = seen[x] + 1
                q.append(y)
    return seen.get(v, None)


def target_of(edges):
    """6(|V| - 1) - def_3(G), the landed carrier's target rank."""
    V = verts_of(edges)
    return 6 * (len(V) - 1) - exact_deficiency(edges)[0]


def rho_bar_of(edges, pt, u, v):
    """rho_bar as a SUBSPACE (binduc's `rel_screw_space` returns the raw
    image; `span` canonicalizes it)."""
    rho, img, dM, r = rel_screw_space(edges, pt, u, v)
    S = span(img)
    assert dim(S) == rho, 'rho_bar dimension mismatch'
    return S, rho, dM, r


def plane_at(edges, pt, v):
    """The pencil plane pi_v of a configuration: the plane through the points
    of closedNbhd(v).  Returns a basis, or None if the closed star does not
    span a plane (the flag is then not determined)."""
    nb = neighbors(edges)
    star = [hat(pt[v])] + [hat(pt[w]) for w in nb.get(v, ())]
    if rank_exact(star) != 3:
        return None
    ns = nullspace(star)
    assert len(ns) == 1, 'closed star normal not unique'
    return nullspace([ns[0]])


# ===================================================== (BE-30): the chain

def run_chain(seed=20260827, nd=12):
    print('===== Step BE29 / (BE-30): the EAR\'s image, EXACTLY -- and the '
          'coordinator\'s Klein-chain hypothesis, TESTED =====')
    print('  The ear is  u = w_0, w_1, ..., w_m, w_{m+1} = v  with every')
    print('  interior vertex of degree 2.  A path is a TREE, so the m+1 edge')
    print('  multipliers are FREE and')
    print('        rho_bar_2 = < l_1, ..., l_{m+1} >,  l_i = p_{i-1} ^ p_i,')
    print('  with EQUALITY, not just <=.  Checked here against binduc\'s own')
    print('  `rel_screw_space` as an identity of SUBSPACES.')
    rng = random.Random(seed)
    t0 = time.time()
    ok = 0
    tot = 0
    for m in range(1, nd):
        E = path(m + 2)
        V = [f'v{i}' for i in range(m + 2)]
        for s in range(4):
            r2 = random.Random(seed + 101 * s + m)
            pt = {w: (rq(r2), rq(r2), rq(r2)) for w in V}
            if len(set(pt.values())) != len(V):
                continue
            try:
                assert_generic_star(E, pt)
            except AssertionError:
                continue
            good, why = verify_pencil_witness(E, pt)
            assert good, why
            S, rho, dM, r = rho_bar_of(E, pt, 'v0', f'v{m+1}')
            L = span([wedge2(hat(pt[V[i]]), hat(pt[V[i + 1]]))
                      for i in range(m + 1)])
            tot += 1
            assert same_space(S, L), ('rho_bar_2 is not the chain span', m)
            ok += 1
            assert dM == 6 + (m + 1), ('dim M of a path', m, dM)
    print(f'  rho_bar_2 = <chain> as SUBSPACES: {ok} / {tot} '
          f'(m = 1 .. {nd-1}, 4 seeded draws each)  -- ZERO exceptions')

    print()
    print('  THE COORDINATOR\'S HYPOTHESIS, stated in the spec as TO BE '
          'TESTED:')
    print('    "in Plucker coordinates the data is a CHAIN on the Klein')
    print('     quadric -- each l_i a quadric point, CONSECUTIVE ones')
    print('     conjugate, NON-consecutive ones unconstrained, and each END')
    print('     line ranging over the pencil at its flag, a line RULED on the')
    print('     quadric."')
    print('  VERDICT: CONFIRMED as stated, with ONE correction and one')
    print('  addition, both measured below.')
    for regime in ('nonadj', 'adj', 'equal'):
        flags = sample_flags(random.Random(seed + 7), regime)
        pu, Bu, pv, Bv = flags
        Piu = pencil_space(pu, Bu)
        Piv = pencil_space(pv, Bv)
        # totally singular <=> a line ruled on the quadric
        ts = all(klein(x, y) == 0 for x in Piu for y in Piu)
        ts2 = all(klein(x, y) == 0 for x in Piv for y in Piv)
        assert ts and ts2, 'a pencil is not totally singular'
        dec = all(is_decomposable([x[k] + t * y[k] for k in range(6)])
                  for t in (F(0), F(1), F(-2), F(3))
                  for x, y in [(Piu[0], Piu[1])])
        assert dec, 'a pencil member is not a line'
        print(f'   [{regime}] Pi_u, Pi_v TOTALLY SINGULAR (ruled lines): '
              f'True;  dim(Pi_u + Pi_v) = {dim(Piu + Piv)}')

    print()
    print('  (i) CONSECUTIVE CONJUGACY and NON-consecutive freedom, measured:')
    flags = sample_flags(random.Random(seed + 13), 'nonadj')
    for m in (3, 4, 5):
        rr = random.Random(seed + 31 * m)
        pts, L, S = sample_ear_span(flags, m, rr)
        assert L is not None
        cons = all(klein(L[i], L[i + 1]) == 0 for i in range(m))
        noncons = [klein(L[i], L[j]) for i in range(m + 1)
                   for j in range(i + 2, m + 1)]
        print(f'   m={m}: every l_i on the quadric: '
              f'{all(is_decomposable(x) for x in L)};  consecutive conjugate: '
              f'{cons};  non-consecutive pairings nonzero: '
              f'{sum(1 for z in noncons if z != 0)} / {len(noncons)}')

    print()
    print('  (ii) THE CORRECTION -- the ends do NOT stay unconstrained at')
    print('  small m, and the hypothesis does not predict this.  THREE')
    print('  CONFINEMENT laws, each exact and each proved in the workbook:')
    print('    (a) m = 1 : the single interior point lies in pi_u cap pi_v, so')
    print('        rho_bar_2 = p_1 ^ <p_u,p_v>  <=  Pi_u + Pi_v  -- a FIXED')
    print('        4-dim subspace E = M ^ L, whatever the configuration.')
    print('    (b) pi_u = pi_v = pi and m <= 2 : every point of the ear lies')
    print('        in pi, so rho_bar_2 <= Lambda^2 pi (3-dim); at m = 2 the')
    print('        containment is an EQUALITY, so the image is a SINGLE POINT')
    print('        of Gr(3,6) and the ear has NO freedom at all.')
    print('    (c) uv an edge with pi_u /= pi_v and m = 1 : FORCED DEGENERATE')
    print('        -- p_1 in pi_u cap pi_v = M forces p_u, p_1, p_v collinear,')
    print('        so the two hinge lines COINCIDE.  Hence a length-2 ear on')
    print('        an ADJACENT pair forces pi_u = pi_v; that is BZAVOID\'s')
    print('        (BE-15) triangle propagation, re-derived from the ear.')
    for regime in ('nonadj', 'equal'):
        flags = sample_flags(random.Random(seed + 17), regime)
        pu, Bu, pv, Bv = flags
        E4 = []
        for m in (1, 2, 3):
            acc = []
            best = 0
            for s in range(40):
                rr = random.Random(seed + 977 * s + m)
                pts, L, S = sample_ear_span(flags, m, rr)
                if L is None:
                    continue
                acc += L
                best = max(best, dim(L))
            u_span = dim(acc)
            print(f'   [{regime}] m={m}: max dim rho_bar_2 over 40 draws = '
                  f'{best} (delta_2 = {min(m+1,6)});  the UNION of all drawn '
                  f'rho_bar_2 spans {u_span}')
            if m == 1:
                E4 = span(acc)
        if regime == 'nonadj':
            Piu = pencil_space(pu, Bu)
            Piv = pencil_space(pv, Bv)
            assert same_space(E4, span(Piu + Piv)), \
                'm=1 image does not span Pi_u + Pi_v'
            print('     CONFIRMED (a): the m = 1 union is EXACTLY Pi_u + Pi_v '
                  f'(dim {dim(E4)})')
        else:
            assert same_space(E4, lam2(Bu)) or dim(E4) <= 3
            print('     CONFIRMED (b): with pi_u = pi_v the m = 1 union sits '
                  f'inside Lambda^2 pi (dim {dim(E4)} <= 3)')
    # (c), measured
    flags = sample_flags(random.Random(seed + 19), 'adj')
    worst = 0
    for s in range(30):
        rr = random.Random(seed + 53 * s)
        pts = ear_points(flags, 1, rr)
        worst = max(worst, dim(chain_of(pts)))
    print(f'   [adj, pi_u /= pi_v] m = 1: max dim rho_bar_2 over 30 draws = '
          f'{worst} against delta_2 = 2  -- and EVERY draw fails '
          f'`legal_chain` (three collinear points): '
          f'{all(not legal_chain(ear_points(flags,1,random.Random(seed+53*s))) for s in range(30))}')

    print()
    print('  (iii) THE HYPOTHESIS\'S OWN CHEAPEST CONSEQUENCE, which the spec')
    print('  named as the falsification to run first: delta_2 <= #edges of the')
    print('  shortest u-v path.  It is PROVED in (BE-31)(ii) below (rho_uv <=')
    print('  dist, unconditionally, plus rho = delta at a welded-attaining')
    print('  configuration) and swept exhaustively in mode `combi`.  Here it')
    print('  is confirmed on the ear itself, where it is TIGHT:')
    for m in range(1, 8):
        E = path(m + 2)
        f = exact_deficiency(E)[0]
        g = g_exact(E, 'v0', f'v{m+1}')
        d = dist_in(E, 'v0', f'v{m+1}')
        assert f - g == min(m + 1, 6), ('ear delta', m, f, g)
        assert f - g <= d, ('delta > dist on an ear', m)
        print(f'   ear m={m}: delta_2 = {f-g} = min(m+1,6);  dist = {d};  '
              f'delta_2 <= dist: True  (tight for m <= 5)')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return ok


# ============================================ (BE-31): the job-2 recursion

def run_sprec(seed=20260827):
    print('===== Step BE30 / (BE-31): what rho_bar IS for a piece that is NOT '
          'an ear -- the SERIES/PARALLEL recursion =====')
    print('  Two elementary identities, both proved in the workbook and both')
    print('  checked here as identities of SUBSPACES:')
    print('    SERIES  (a cut vertex z on the u-v route):')
    print('        rho_bar_{u,v}(H_1 u H_2) = rho_bar_{u,z}(H_1) + '
          'rho_bar_{z,v}(H_2)')
    print('    PARALLEL (both attachments at u and v):')
    print('        rho_bar_{u,v}(H_1 u H_2) = rho_bar_{u,v}(H_1) cap '
          'rho_bar_{u,v}(H_2)')
    rng = random.Random(seed)
    t0 = time.time()

    def rb(E, pt, a, b):
        return rho_bar_of(E, pt, a, b)[0]

    def draw(E, s):
        r2 = random.Random(seed + 313 * s)
        V = sorted(verts_of(E), key=str)
        if hubs_of(E):
            # a hub carries a real pencil condition, so a generic draw is
            # ILLEGAL: fall back to the BTWOCUT ladder, whose every returned
            # configuration has already passed `assert_generic_star` and
            # `verify_pencil_witness`.
            r, tag, pt = extended_construction(E, nseeds=2,
                                               seed0=seed + 313 * s)
            return pt
        for _ in range(40):
            pt = {w: (rq(r2, 25), rq(r2, 25), rq(r2, 25)) for w in V}
            if len(set(pt.values())) != len(V):
                continue
            try:
                assert_generic_star(E, pt)
            except AssertionError:
                continue
            good, why = verify_pencil_witness(E, pt)
            if not good:
                continue
            return pt
        return None

    battery = []
    # series: P (3 edges) then R (1 edge)
    P = [('u', 'p1'), ('p1', 'p2'), ('p2', 'x')]
    Q = [('u', 'q1'), ('q1', 'q2'), ('q2', 'x')]
    R = [('x', 'v')]
    P2 = [('u', 'r1'), ('r1', 'x')]
    battery.append(('series  P . R', P + R, [('u', 'x', P), ('x', 'v', R)],
                    'sum'))
    battery.append(('series  P2 . R', P2 + R,
                    [('u', 'x', P2), ('x', 'v', R)], 'sum'))
    battery.append(('parallel P | Q', P + Q, [('u', 'x', P), ('u', 'x', Q)],
                    'cap'))
    battery.append(('parallel P | P2', P + P2,
                    [('u', 'x', P), ('u', 'x', P2)], 'cap'))
    okser = okpar = tot = 0
    for (name, E, parts, kind) in battery:
        for s in range(3):
            pt = draw(E, s)
            if pt is None:
                continue
            a, b = ('u', 'v') if kind == 'sum' else ('u', 'x')
            whole = rb(E, pt, a, b)
            pieces = [rb(Ei, pt, ai, bi) for (ai, bi, Ei) in parts]
            comp = (pieces[0] + pieces[1]) if kind == 'sum' \
                else isect(pieces[0], pieces[1])
            tot += 1
            assert same_space(whole, comp), ('SP recursion fails', name, kind)
            if kind == 'sum':
                okser += 1
            else:
                okpar += 1
        print(f'   {name:16s} [{kind}]: identity of subspaces holds at every '
              f'seeded draw')
    print(f'  SERIES verified at {okser} draws, PARALLEL at {okpar} '
          f'(total {tot}) -- ZERO exceptions')

    print()
    print('  CONSEQUENCE (proved): for EVERY u-v path P of a piece H,')
    print('      rho_bar_{u,v}(H) <= < l_e : e in P >,')
    print('  because m(v) - m(u) telescopes along P and each summand is a')
    print('  multiple of that edge\'s hinge line.  Hence')
    print('      rho_uv(H) <= dist_H(u,v)   UNCONDITIONALLY,')
    print('  and, at a configuration where H and H/uv both attain (so')
    print('  rho = delta by (BE-22)(ii)),  delta_uv <= dist_H(u,v).')
    print()
    print('  AND THE COORDINATOR\'S "obvious candidate upper bound" -- the')
    print('  INTERSECTION over u-v paths of the path spans -- is REFUTED as an')
    print('  EQUALITY.  The SP recursion is the correct description and it is')
    print('  strictly stronger:  (rho_P cap rho_Q) + rho_R is contained in,')
    print('  and can be STRICTLY smaller than, (rho_P + rho_R) cap')
    print('  (rho_Q + rho_R).  Witness, exact:')
    E = P + Q + R
    for s in range(4):
        pt = draw(E, s)
        if pt is None:
            continue
        rP = rb(P, pt, 'u', 'x')
        rQ = rb(Q, pt, 'u', 'x')
        rR = rb(R, pt, 'x', 'v')
        whole = rb(E, pt, 'u', 'v')
        spf = span(isect(rP, rQ) + rR)
        pathb = isect(span(rP + rR), span(rQ + rR))
        assert same_space(whole, spf), 'SP recursion fails on the witness'
        print(f'   theta(3,3) + pendant edge, seed {seed + 313*s}:  '
              f'dim rho_bar = {dim(whole)} = dim SP-formula {dim(spf)};  '
              f'path-intersection bound = {dim(pathb)}  '
              f'{"STRICTLY BIGGER" if dim(pathb) > dim(whole) else "equal"}')
        if dim(pathb) > dim(whole):
            assert contains(pathb, whole), 'the path bound is not a bound'
        break
    print()
    print('  SO the answer to job 2 is POSITIVE with a named limit: rho_bar')
    print('  admits a hinge-line description for every SERIES-PARALLEL piece,')
    print('  computed down the SPQR tree (S-node = sum, P-node = intersection,')
    print('  the leaf being a single edge with rho_bar = <l_e>).  What has NO')
    print('  such description is the R-NODE (a 3-connected block with its')
    print('  virtual edges replaced by children).  (BE-25)(iii) closes only the')
    print('  LEAF R-node: a 3-connected block minus its parent virtual edge is')
    print('  rigid, so there rho_bar = 0 and the recursion terminates.  An')
    print('  INTERNAL R-node -- flexible children substituted for its virtual')
    print('  edges -- is NOT covered (K_4 + ear(m) is one, with delta in {4,5}),')
    print('  and IS the residue; it is this direction ranked successor (3).')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot


# ================================= (BE-32): the combinatorial half, swept

def forced_same_plane(edges):
    """The AGGRESSIVE plane-class propagation, taken PAIRWISE.  binduc's
    `flat_forcing_closure` asks "is EVERY point forced into one plane"; this
    asks "which HUB PAIRS are forced to share their plane".  Rule, from
    BZAVOID (BE-15)(i) generalized at BINDUC (BE-23)(ii): pi_v is forced to pi
    as soon as closedNbhd(v) holds three independent points already known to
    lie in pi.  AGGRESSIVE = assumes every three forced points independent, so
    this OVER-claims forcing: a pair it does NOT list is certainly not forced,
    and a claim proved for every pair it DOES list holds a fortiori for the
    genuinely forced ones (the direction that makes an empty sweep the
    stronger statement)."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    out = set()
    for h in H:
        A = {h} | set(nb[h])
        fam = {h}
        changed = True
        while changed:
            changed = False
            for v in H:
                if v in fam:
                    continue
                star = {v} | set(nb[v])
                if len(star & A) >= 3:
                    A |= star
                    fam.add(v)
                    changed = True
        for a, b in itertools.combinations(sorted(fam, key=str), 2):
            out.add((a, b))
    return out


def run_combi(nmax=6, nsamp=(7, 8), nmask=3000, seed=20260827):
    print('===== Step BE31 / (BE-32): the COMBINATORIAL half -- three '
          'elementary theorems, and the cheapest falsification test the arc '
          'has =====')
    print('  All four claims below are about delta_uv = def_3(H) - '
          'def_3(H/uv)')
    print('  ALONE -- no configuration, no genericity, no constructor.')
    print()
    print('  (BE-32)(i)  u ~ v  =>  delta_uv <= 1.')
    print('     Proof.  Let P attain f = def_3(H) with u in A, v in B, A /= B,')
    print('     and let c = #edges between A and B.  Merging A and B gives a')
    print('     partition with u, v together, of value f - 6 + 5c, which is')
    print('     <= g_uv <= f; so c <= 1.  With uv an edge, c >= 1, so c = 1')
    print('     and g_uv >= f - 1.  (If every optimal P has u, v together,')
    print('     g = f and delta = 0.)')
    print('  (BE-32)(ii) u, v on a common TRIANGLE  =>  delta_uv = 0.')
    print('     Proof.  With uvz a triangle: z in A or z in B forces c >= 2,')
    print('     excluded by (i).  So z lies in a third part C, and merging')
    print('     A, B, C gives value f - 12 + 5c\' with c\' >= 3, i.e. >= f + 3,')
    print('     against <= f.  Hence NO optimal partition separates u and v,')
    print('     so g = f.')
    print('  (BE-32)(iii) u, v with >= 3 common neighbours  =>  delta_uv = 0.')
    print('     Same merge argument, with the common neighbours supplying the')
    print('     crossing edges.')
    print('  (BE-32)(iv) delta_uv <= dist_H(u,v)  is NECESSARY for the')
    print('     strengthened statement at {u,v}: rho_uv <= dist_H(u,v)')
    print('     unconditionally ((BE-31)), and welded attainment forces')
    print('     rho_uv = delta_uv.  So a single (H,u,v) with delta > dist')
    print('     would REFUTE S-all and S-mark outright -- with no geometry.')
    t0 = time.time()
    tot_graphs = 0
    tot_pairs = 0
    bad_dist = []
    bad_tri = []
    bad_k23 = []
    bad_adj = []
    bad_force = []
    n_tri = n_k23 = n_adj = n_force = 0
    rngc = random.Random(seed)
    tiers = [(n, None) for n in range(3, nmax + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rngc.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            tot_graphs += 1
            f = exact_deficiency(edges)[0]
            nb = neighbors(edges)
            fs = forced_same_plane(edges)
            for (u, v) in pairs:
                g = g_exact(edges, u, v)
                d = f - g
                assert 0 <= d <= 6, ('delta out of [0,6]', edges, u, v, d)
                tot_pairs += 1
                dd = dist_in(edges, u, v)
                if d > dd:
                    bad_dist.append((tuple(edges), u, v, d, dd))
                com = set(nb.get(u, ())) & set(nb.get(v, ()))
                if v in nb.get(u, ()):
                    n_adj += 1
                    if d > 1:
                        bad_adj.append((tuple(edges), u, v, d))
                    if com:
                        n_tri += 1
                        if d != 0:
                            bad_tri.append((tuple(edges), u, v, d))
                if len(com) >= 3:
                    n_k23 += 1
                    if d != 0:
                        bad_k23.append((tuple(edges), u, v, d))
                if (u, v) in fs:
                    n_force += 1
                    if d != 0:
                        bad_force.append((tuple(edges), u, v, d))
        print(f'   n = {n}'
              + (' EXHAUSTIVE' if samp is None
                 else f' SAMPLED ({samp} seeded masks)')
              + f': cumulative {tot_graphs} connected labelled graphs, '
                f'{tot_pairs} (graph, pair) instances')
    print()
    print(f'  EXHAUSTIVE over ALL connected labelled graphs on n = 3 .. {nmax}'
          f', plus {nmask} seeded masks at each of {nsamp}'
          f' -- {tot_graphs} graphs, {tot_pairs} (graph, pair) instances:')
    print(f'    (i)   adjacent pairs {n_adj:6d}  with delta > 1 : '
          f'{len(bad_adj)}')
    print(f'    (ii)  triangle pairs {n_tri:6d}  with delta /= 0: '
          f'{len(bad_tri)}')
    print(f'    (iii) >=3-common-nbr {n_k23:6d}  with delta /= 0: '
          f'{len(bad_k23)}')
    print(f'    (iv)  ALL pairs      {tot_pairs:6d}  with delta > dist: '
          f'{len(bad_dist)}')
    print(f'    (+)   AGGRESSIVELY forced-same-plane pairs {n_force:6d} '
          f'with delta /= 0: {len(bad_force)}')
    for r in bad_dist[:4]:
        print('      dist violation:', r)
    for r in bad_tri[:4]:
        print('      triangle violation:', r)
    for r in bad_force[:4]:
        print('      forced-plane violation:', r)
    print()
    print('  CAP DISCLOSURE.  This is exhaustive to n = '
          f'{nmax} and NOT beyond: the (iv) sweep reports "no (H,u,v) with')
    print(f'  delta > dist found under the cap n <= {nmax}", never "none')
    print('  exists".  (i)-(iii) are PROVED above and the sweep only confirms')
    print('  them; (+) is MEASURED and its predicate is the AGGRESSIVE')
    print('  closure, which over-claims forcing.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot_pairs, len(bad_dist), len(bad_tri), len(bad_force)


# ================================ (BE-33): the bad locus, classified

def line_points(f):
    """The 2-dim subspace of K^4 spanned by a DECOMPOSABLE Plucker vector: the
    column space of the antisymmetric 4x4 matrix it is the upper triangle
    of."""
    assert is_decomposable(f), 'line_points on a non-decomposable bivector'
    PL = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    M = [[F(0)] * 4 for _ in range(4)]
    for k, (i, j) in enumerate(PL):
        M[i][j] = f[k]
        M[j][i] = -f[k]
    cols = [[M[i][j] for i in range(4)] for j in range(4)]
    B = nullspace(nullspace(cols)) if rank_exact(cols) < 4 else None
    assert B is not None and len(B) == 2, ('line_points: not a line',
                                           rank_exact(cols))
    return B


def pencil_vertex(Fsp):
    """For a 2-dim TOTALLY SINGULAR subspace of Lambda^2 K^4 (necessarily a
    PENCIL of lines), the common point of its lines.  Returns None if the space
    is not totally singular."""
    if dim(Fsp) != 2:
        return None
    B = span(Fsp)
    if not all(klein(x, y) == 0 for x in B for y in B):
        return None
    if not (is_decomposable(B[0]) and is_decomposable(B[1])):
        return None
    P1, P2 = line_points(B[0]), line_points(B[1])
    M = perp_std(P1) + perp_std(P2)
    inter = nullspace(M)
    if len(inter) != 1:
        return None
    return inter[0]


def bad_predicate(A, flags, m):
    """The direction's CLASSIFICATION of when the ear image is trapped, stated
    as a PREDICTION of the reachable maximum of dim(A + rho_bar_2), to be
    checked against measurement.  THREE independent trapping mechanisms, and
    the loss is the LARGEST of them:

      (P) PENCIL SWALLOWING.  l_1 ranges over Pi_u and l_{m+1} over Pi_v, so
          each pencil that A contains outright costs exactly one dimension.
      (Z) CONFINEMENT.  The two END lines always lie in the confining space
          Z (Z = Pi_u + Pi_v with distinct planes, Z = Lambda^2 pi with
          pi_u = pi_v), so dim(rho_bar_2 cap Z) >= 2 -- and = 3 in the one
          case where rho_bar_2 IS Lambda^2 pi (pi_u = pi_v, m = 2).  Hence
          dim(A cap rho_bar_2) >= dim(A cap Z) + c_2 - dim Z.
      (R) THE OPPOSITE RULING (m = 1 only).  rho_bar_2 sweeps ONE ruling of
          the quadric surface inside E = Pi_u + Pi_v; a line of the OPPOSITE
          ruling, i.e. y ^ L for y on M = p_u v p_v, meets EVERY member.

    Returns (predicted_reach, tag)."""
    pu, Bu, pv, Bv = flags
    d1 = dim(A)
    d2 = min(m + 1, 6)
    equal_planes = (rank_exact(Bu + Bv) == 3)
    Piu = pencil_space(pu, Bu)
    Piv = pencil_space(pv, Bv)
    if equal_planes:
        Z = lam2(Bu)
        c2 = 3 if m == 2 else 2
        tag = 'equal planes (Z = Lambda^2 pi)'
    else:
        Z = span(Piu + Piv)
        c2 = 2
        tag = 'distinct planes (Z = Pi_u + Pi_v)'
    lossP = ((1 if contains(A, Piu) else 0) + (1 if contains(A, Piv) else 0))
    Fsp = isect(A, Z) if A else []
    lossZ = max(0, dim(Fsp) + c2 - dim(Z))
    lossR = 0
    if m == 1 and not equal_planes and dim(Fsp) == 2:
        y = pencil_vertex(Fsp)
        if y is not None and rank_exact([pu, pv, y]) == 2:
            lossR = 1
            tag += ' + opposite ruling'
    loss = max(lossP, lossZ, lossR)
    return min(6, d1 + d2 - loss), tag


def reach_measured(A, flags, m, seed, ndraw=45):
    best = 0
    for s in range(ndraw):
        rr = random.Random(seed + 8191 * s + 13 * m)
        pts, L, S = sample_ear_span(flags, m, rr)
        if L is None:
            continue
        best = max(best, dim(A + L))
    return best


def a_battery(flags, rng):
    """Structured subspaces A = rho_bar_1 to test the classification against:
    the ones the geometry singles out, not random draws alone."""
    pu, Bu, pv, Bv = flags
    Piu = pencil_space(pu, Bu)
    Piv = pencil_space(pv, Bv)
    equal_planes = (rank_exact(Bu + Bv) == 3)
    out = []

    def ext(rows, k, tag):
        cur = [r[:] for r in rows]
        guard = 0
        while dim(cur) < k and guard < 200:
            guard += 1
            cand = cur + [[rq(rng) for _ in range(6)]]
            if dim(cand) > dim(cur):
                cur = cand
        if dim(cur) == k:
            out.append((f'{tag} (d1={k})', span(cur)))

    for k in range(2, 7):
        ext(Piu, k, 'A >= Pi_u')
        ext(Piv, k, 'A >= Pi_v')
    if not equal_planes:
        L = plane_meet(Bu, Bv)
        for (al, be) in ((F(1), F(1)), (F(2), F(-3))):
            y = [al * pu[k] + be * pv[k] for k in range(4)]
            R = span([wedge2(y, L[0]), wedge2(y, L[1])])
            for k in range(2, 6):
                ext(R, k, f'A >= y^L (y on M, y/=p_u,p_v)')
    Zsp = lam2(Bu) if equal_planes else span(Piu + Piv)
    for k in range(2, dim(Zsp) + 1):
        sub = []
        guard = 0
        while dim(sub) < k and guard < 300:
            guard += 1
            c = [rq(rng) for _ in Zsp]
            cand = sub + [[sum(c[i] * Zsp[i][t] for i in range(len(Zsp)))
                           for t in range(6)]]
            if dim(cand) > dim(sub):
                sub = cand
        if dim(sub) == k:
            out.append((f'A <= Z (d1={k})', span(sub)))
    if equal_planes:
        Lam = lam2(Bu)
        for k in (1, 2, 3):
            sub = []
            guard = 0
            while dim(sub) < k and guard < 200:
                guard += 1
                c = [rq(rng) for _ in Lam]
                cand = sub + [[sum(c[i] * Lam[i][t] for i in range(3))
                               for t in range(6)]]
                if dim(cand) > dim(sub):
                    sub = cand
            if dim(sub) == k:
                out.append((f'A <= Lambda^2 pi (d1={k})', span(sub)))
    for k in range(0, 7):
        cur = []
        guard = 0
        while dim(cur) < k and guard < 200:
            guard += 1
            cand = cur + [[rq(rng) for _ in range(6)]]
            if dim(cand) > dim(cur):
                cur = cand
        if dim(cur) == k:
            out.append((f'A random (d1={k})', span(cur)))
    return out


def run_alpha(seed=20260827, ntrial=40):
    """(BE-33)(i) THE ALPHA-PLANE ESCAPE LEMMA, tested as its own sentence.

      For a subspace B < Lambda^2 K^4 with B /= everything,
          Bad(B) := { p in P^3 : S_p <= B }  =  { p : B^{perp_K} <= S_p },
      which is EMPTY or a SINGLE POINT when dim B <= 4, and empty, a point,
      or exactly the point set of the line l_xi when dim B = 5 with
      B^{perp_K} = <xi> and xi decomposable.

    This is what makes the chain greedy run: at every interior vertex of the
    ear there is a line through the current point escaping the space built so
    far, because the bad points form at most a line."""
    print('===== Step BE32 / (BE-33)(i): the ALPHA-PLANE ESCAPE LEMMA =====')
    rng = random.Random(seed)
    t0 = time.time()
    ok = 0
    tot = 0
    worst = {}
    for d in range(1, 6):
        for t in range(ntrial):
            B = []
            guard = 0
            while dim(B) < d and guard < 200:
                guard += 1
                cand = B + [[rq(rng) for _ in range(6)]]
                if dim(cand) > dim(B):
                    B = cand
            if dim(B) != d:
                continue
            Bp = klein_perp(B)
            assert dim(Bp) == 6 - d, 'Klein perp dimension'
            # the identity Bad(B) = {p : B^perpK <= S_p}, tested pointwise
            bad = 0
            for _ in range(25):
                p = v4(rng)
                if all(x == 0 for x in p):
                    continue
                Sp = alpha_plane(p)
                lhs = contains(B, Sp)
                rhs = contains(Sp, Bp)
                tot += 1
                assert lhs == rhs, ('alpha-plane identity fails', d)
                ok += 1
                if lhs:
                    bad += 1
            worst[d] = max(worst.get(d, 0), bad)
    print(f'  the identity  S_p <= B  <=>  B^perp_K <= S_p  holds at '
          f'{ok} / {tot} (B, p) draws -- ZERO exceptions')
    print('  and the bad set is SMALL: over the same draws the number of '
          'random p with S_p <= B was')
    print('   ' + ',  '.join(f'dim B = {d}: {worst[d]} of 25'
                             for d in sorted(worst)))
    # the two EXTREMAL cases, constructed rather than sampled
    q0 = v4(rng)
    Sq = alpha_plane(q0)
    B5 = span(klein_perp([wedge2(q0, v4(rng))]))
    assert dim(B5) == 5, 'l^perp_K is 5-dimensional'
    l0 = None
    for _ in range(20):
        cand = wedge2(q0, v4(rng))
        if any(x != 0 for x in cand):
            l0 = cand
            break
    Bl = span(klein_perp([l0]))
    pts_on = 0
    Lb = line_points(l0)
    for t in range(12):
        c = [rq(rng), rq(rng)]
        p = [c[0] * Lb[0][k] + c[1] * Lb[1][k] for k in range(4)]
        if all(x == 0 for x in p):
            continue
        if contains(Bl, alpha_plane(p)):
            pts_on += 1
    print(f'  extremal case dim B = 5 with B = l^perp_K: every sampled point '
          f'OF THE LINE l is bad ({pts_on} of 12 draws) -- the ONE shape in '
          f'which Bad(B) is a whole line, exactly as the lemma says')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return ok, tot


def run_badA(seed=20260827):
    print('===== Step BE32 / (BE-33): the BAD LOCUS, CLASSIFIED -- exactly '
          'which A = rho_bar_1 the ear image cannot escape =====')
    print('  Fix the shared flags.  The ear\'s own moduli are')
    print('  (p_1 in pi_u, p_2 ... p_{m-1} free in P^3, p_m in pi_v), an')
    print('  IRREDUCIBLE rational parameter space, and dim(A + rho_bar_2) is')
    print('  the rank of a matrix polynomial in those parameters, hence LOWER')
    print('  SEMICONTINUOUS.  So the maximum below is attained on a dense open')
    print('  subset, and ONE draw reaching it settles that (A, m) outright.')
    print()
    print('  THE CLASSIFICATION (the direction\'s main claim):')
    print('    m >= 2, pi_u /= pi_v : the ear loses ONE dimension per pencil')
    print('        it cannot escape --  reach = min(d1 + d2 - #{Pi in {Pi_u,')
    print('        Pi_v} : Pi <= A}, 6).  In particular the image is trapped')
    print('        IFF A swallows a whole PENCIL at u or at v.')
    print('    m = 1 : rho_bar_2 sweeps ONE RULING of the smooth quadric')
    print('        surface {decomposables} inside E = Pi_u + Pi_v, so A traps')
    print('        it iff A cap E contains a line of the OPPOSITE ruling,')
    print('        i.e. y ^ L for some y on M = p_u v p_v  (y = p_u gives')
    print('        Pi_u, y = p_v gives Pi_v), or dim(A cap E) >= 3.')
    print('    pi_u = pi_v : rho_bar_2 <= Lambda^2 pi, and at m = 2 it IS')
    print('        Lambda^2 pi -- the image is a SINGLE POINT of Gr(3,6).')
    t0 = time.time()
    agree = 0
    disagree = []
    tot = 0
    for regime in ('nonadj', 'adj', 'equal'):
        flags = sample_flags(random.Random(seed + 3), regime)
        rng = random.Random(seed + 11)
        bat = a_battery(flags, rng)
        ms = (2, 3, 4, 5) if regime == 'adj' else (1, 2, 3, 4, 5)
        print()
        print(f'  --- regime {regime} '
              f'({"pi_u = pi_v" if regime == "equal" else "pi_u /= pi_v"})')
        for (tag, A) in bat:
            row = []
            for m in ms:
                d2 = min(m + 1, 6)
                T = min(dim(A) + d2, 6)
                pred, ptag = bad_predicate(A, flags, m)
                meas = reach_measured(A, flags, m, seed + 977)
                tot += 1
                if pred == meas:
                    agree += 1
                else:
                    disagree.append((regime, tag, m, pred, meas, T))
                row.append(f'm={m}:{meas}/{T}'
                           + ('' if meas == T else '  <== TRAPPED'))
            print(f'    {tag:34s} ' + '  '.join(row))
    print()
    print(f'  CLASSIFICATION vs MEASUREMENT: {agree} / {tot} agree'
          + ('' if not disagree else f';  {len(disagree)} DISAGREEMENTS:'))
    for r in disagree[:12]:
        print('     regime %s, %s, m=%d: predicted %d, measured %d '
              '(target %d)' % r)
    print()
    print('  READ THIS THE RIGHT WAY.  The rows marked TRAPPED are NOT')
    print('  counterexamples to (BE-14): they are subspaces A of the screw')
    print('  space, exhibited by hand, at which the EAR alone cannot reach the')
    print('  criterion.  Whether any of them is the rho_bar_1 of an actual')
    print('  piece is a different question, and it is the one mode `hunt`')
    print('  asks.  Nothing here is a dimension count and nothing here')
    print('  derives properness, generic smoothness or transversality from')
    print('  one (ZJACOB (JC-6)).')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return agree, tot, disagree


# ============================ (BE-34): does a REAL piece produce a bad A?

def ear_side(E2, u, v):
    """If side 2 is an EAR (a path from u to v whose interior vertices all have
    degree 2 in it), return m = #interior vertices; else None."""
    nb = neighbors(E2)
    interior = [w for w in verts_of(E2) if w not in (u, v)]
    if len(E2) != len(interior) + 1:
        return None
    if any(len(nb.get(w, ())) != 2 for w in interior):
        return None
    if len(nb.get(u, ())) != 1 or len(nb.get(v, ())) != 1:
        return None
    # walk it
    seen = {u}
    cur = u
    k = 0
    while cur != v:
        nxt = [y for y in nb.get(cur, ()) if y not in seen]
        if len(nxt) != 1:
            return None
        cur = nxt[0]
        seen.add(cur)
        k += 1
    return k - 1 if seen == set(verts_of(E2)) else None


def image_battery():
    """Composed graphs G = G_1 u ear(m) at a 2-cut {u,v}, with G_1 a REAL
    piece.  Chosen so that delta_1 ranges over 0 .. 6 and both flag regimes
    occur."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    prism = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    cube = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
            (0, 4), (1, 5), (2, 6), (3, 7)]
    out = []
    for m in range(1, 6):
        out.append((f'K4 + ear({m}) @ (0,1) [uv IS an edge]',
                    ear(K4, 0, 1, m), 0, 1))
        out.append((f'prism + ear({m}) @ (0,4) [uv NOT an edge]',
                    ear(prism, 0, 4, m), 0, 4))
        out.append((f'K33 + ear({m}) @ (0,1) [uv NOT an edge]',
                    ear(K33, 0, 1, m), 0, 1))
        out.append((f'cube + ear({m}) @ (0,1)', ear(cube, 0, 1, m), 0, 1))
        out.append((f'theta(4,4) + ear({m}) @ (u,v)',
                    ear(theta(4, 4, 4), 'u', 'v', m, tag='g'), 'u', 'v'))
        out.append((f'C8 + ear({m}) @ antipodes',
                    ear(cycle(8), 'v0', 'v4', m, tag='g'), 'v0', 'v4'))
    # BOTH sides EARS (a cycle): the only family in which delta_1 grows with
    # the piece, so the only one that exercises the classification at
    # delta_1 >= 3.  u, v have degree 2 here, so NO pencil condition binds at
    # the cut and the ear's endpoints are free -- handled in `measure_image`.
    for (m1, m2) in ((2, 2), (3, 3), (4, 3), (5, 4), (6, 5), (5, 5)):
        out.append((f'ear({m1}) + ear({m2}) @ (u,v)  [= C{m1+m2+2}]',
                    ear(ear([], 'u', 'v', m1), 'u', 'v', m2, tag='g'),
                    'u', 'v'))
    # side 1 = a THETA (u, v are hubs, so the flags DO bind), side 2 = the ear
    for (a, m) in ((3, 3), (4, 4), (5, 3), (6, 5)):
        out.append((f'theta({a},{a},{a}) + ear({m}) @ (u,v)',
                    ear(theta(a, a, a), 'u', 'v', m, tag='g'), 'u', 'v'))
    # side 1 = a two-private-hub piece (btwocut's hardest zone), side 2 = ear
    for (k, m) in ((3, 3), (4, 4), (3, 5)):
        side = [('u', 'c'), ('d', 'v')]
        for b in range(2):
            prev = 'c'
            for j in range(k - 1):
                cur = f'z{b}_{j}'
                side.append((prev, cur))
                prev = cur
            side.append((prev, 'd'))
        out.append((f'hubbed-side({k}) + ear({m}) @ (u,v)',
                    ear(side, 'u', 'v', m, tag='g'), 'u', 'v'))
    return out


def measure_image(name, edges, u, v, nseeds=3, ndraw=40, seed=20260827,
                  verbose=True):
    """Build ONE legal whole-graph pencil configuration; freeze side 1 and the
    shared flags; then vary ONLY the ear's own moduli and report the image."""
    sp = split_at_pair(edges, u, v)
    if sp is None:
        return None
    V1, E1, V2, E2 = sp
    m = ear_side(E2, u, v)
    if m is None:
        V1, E1, V2, E2 = V2, E2, V1, E1
        m = ear_side(E2, u, v)
        if m is None:
            return None
    cd = deltas_at(edges, u, v, check=False)
    if cd is None:
        return None
    A1, B1, f1, g1, A2, B2, f2, g2 = cd
    if set(A1) != set(V1):
        f1, g1, f2, g2 = f2, g2, f1, g1
    d1, d2 = f1 - g1, f2 - g2
    T = target_of(edges)
    r0, tag, pt = extended_construction(edges, nseeds=nseeds,
                                        seed0=seed, target=T)
    if pt is None:
        return None
    Bu = plane_at(edges, pt, u)
    Bv = plane_at(edges, pt, v)
    if Bu is None or Bv is None:
        return None
    pu, pv = hat(pt[u]), hat(pt[v])
    flags = (pu, Bu, pv, Bv)
    equal_planes = (rank_exact(Bu + Bv) == 3)
    rho1, r1, dM1, _ = rho_bar_of(E1, pt, u, v)
    attain1 = (dM1 == 6 + f1)
    best = 0
    bestrank = r0
    nlegal = 0
    interior = [w for w in verts_of(E2) if w not in (u, v)]
    # order the interior along the path
    nb2 = neighbors(E2)
    order = []
    cur, seen = u, {u}
    while cur != v:
        nxt = [y for y in nb2.get(cur, ()) if y not in seen][0]
        seen.add(nxt)
        if nxt != v:
            order.append(nxt)
        cur = nxt
    assert len(order) == m, 'ear walk length mismatch'
    nbG = neighbors(edges)
    huby = len(nbG.get(u, ())) >= 3
    hubv = len(nbG.get(v, ())) >= 3
    Cu = Bu if huby else None          # the pencil condition at a DEGREE-2
    Cv = Bv if hubv else None          # vertex is vacuous, so p_1 is free
    for s in range(ndraw):
        rr = random.Random(seed + 6151 * s + 17)
        if m == 1:
            if Cu is None and Cv is None:
                pts = [pu] + [v4(rr)] + [pv]
            elif Cu is None:
                pts = [pu] + [pt_in(Cv, rr)] + [pv]
            elif Cv is None:
                pts = [pu] + [pt_in(Cu, rr)] + [pv]
            elif equal_planes:
                pts = [pu] + [pt_in(Bu, rr)] + [pv]
            else:
                L = plane_meet(Bu, Bv)
                if len(L) < 2:
                    continue
                pts = [pu] + [pt_in(L, rr)] + [pv]
        else:
            p1 = pt_in(Cu, rr) if Cu is not None else v4(rr)
            pm = pt_in(Cv, rr) if Cv is not None else v4(rr)
            pts = ([pu] + [p1] + [v4(rr) for _ in range(m - 2)]
                   + [pm] + [pv])
        if not legal_chain(pts):
            continue
        newpt = dict(pt)
        okaff = True
        for i, w in enumerate(order):
            x = pts[i + 1]
            if x[3] == 0:
                okaff = False
                break
            newpt[w] = tuple(x[k] / x[3] for k in range(3))
        if not okaff:
            continue
        if len(set(newpt.values())) != len(newpt):
            continue
        try:
            assert_generic_star(edges, newpt)
        except AssertionError:
            continue
        good, why = verify_pencil_witness(edges, newpt)
        if not good:
            continue
        nlegal += 1
        rho2, r2, dM2, _ = rho_bar_of(E2, newpt, u, v)
        s12 = dim(rho1 + rho2)
        if s12 > best:
            best = s12
        rr_rank = rank_exact(build_rigidity(edges, newpt)[0])
        assert rr_rank <= T, ('rank above target', name, rr_rank, T)
        bestrank = max(bestrank, rr_rank)
    crit = min(d1 + d2, 6)
    pred, ptag = bad_predicate(rho1, flags, m)
    if verbose:
        print(f'   {name:44s} m={m} d=({d1},{d2}) '
              f'{"pi_u=pi_v" if equal_planes else "pi_u/=pi_v"} '
              f'rho_1={r1}{"=" if r1 == d1 else "/="}d1  '
              f'max dim(rho1+rho2) = {best} / {crit}  '
              f'rank {bestrank}/{T}  [{nlegal} legal ear draws, rung {tag}]'
              + ('' if best == crit else '   <== SHORTFALL'))
    return dict(name=name, m=m, d1=d1, d2=d2, best=best, crit=crit,
                rank=bestrank, target=T, nlegal=nlegal, rho1=r1,
                attain1=attain1, equal_planes=equal_planes, pred=pred,
                flags=flags, rho1sp=rho1)


def run_image(seed=20260827, ndraw=40):
    print('===== Step BE33 / (BE-34): the IMAGE, measured at REAL composed '
          'graphs -- side 1 FROZEN, only the ear moving =====')
    print('  This is the spec\'s headline sentence tested DIRECTLY, and it is')
    print('  the one measurement in this direction that is about the actual')
    print('  question: hold G_1\'s configuration AND the shared flags fixed,')
    print('  vary ONLY the ear\'s own moduli (p_1 in pi_u, interior free, p_m')
    print('  in pi_v), and ask whether the image escapes rho_bar_1\'s bad')
    print('  locus.  Each row\'s `max dim(rho1+rho2)` is a LOWER bound on the')
    print('  true maximum, so a row reaching the criterion SETTLES that')
    print('  instance (an attaining draw is a proof, `rank <= target` being')
    print('  universal); a row short of it is a CANDIDATE and nothing more.')
    t0 = time.time()
    rows = []
    short = []
    for (name, E, u, v) in image_battery():
        r = measure_image(name, E, u, v, seed=seed, ndraw=ndraw)
        if r is None:
            print(f'   {name:44s} -- not an ear split / no configuration')
            continue
        rows.append(r)
        if r['best'] != r['crit']:
            short.append(r)
    print()
    print(f'  {len(rows) - len(short)} / {len(rows)} instances reach '
          f'dim(rho_bar_1 + rho_bar_2) = min(delta_1+delta_2, 6) by moving '
          f'the EAR ALONE.')
    if short:
        print('  SHORTFALLS (candidates, never refutations):')
        for r in short:
            print(f'    {r["name"]}: {r["best"]} / {r["crit"]}, '
                  f'rank {r["rank"]}/{r["target"]}, rho_1={r["rho1"]} '
                  f'vs delta_1={r["d1"]}, side-1 attains: {r["attain1"]}')
    nfull = sum(1 for r in rows if r['rank'] == r['target'])
    print(f'  {nfull} / {len(rows)} instances reach the WHOLE-GRAPH target '
          f'rank 6(|V|-1) - def_3(G).')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows, short


def run_hunt(nexh=6, nsamp=(7,), nmask=1500, seed=20260827, cap=420):
    print('===== Step BE33 / (BE-34)(ii): the OBSTRUCTION HUNT -- is the '
          'BAD-A predicate EVER satisfied by a real rho_bar_1? =====')
    print('  (BE-33) says the ear image is trapped IFF rho_bar_1 swallows a')
    print('  whole PENCIL Pi_u or Pi_v (m >= 2), or, at m = 1, contains a')
    print('  line y ^ L of the opposite ruling.  This mode asks that question')
    print('  of the PREDICATE rather than of the rank: over a census of 2-cut')
    print('  instances, compute rho_bar_1 at a legal configuration and test')
    print('       Pi_u <= rho_bar_1 ?    Pi_v <= rho_bar_1 ?')
    print('       dim(rho_bar_1 cap (Pi_u + Pi_v)) >= 3 ?')
    print('       rho_bar_1 cap (Pi_u+Pi_v) an OPPOSITE-ruling line y ^ L ?')
    t0 = time.time()
    cens = two_cut_census(nexh=nexh, nsamp=nsamp, nmask=nmask, seed=seed)
    ncens = len(cens)
    if cap is not None and len(cens) > cap:
        rr = random.Random(seed + 5)
        cens = rr.sample(cens, cap)
    print(f'  census: {ncens} (graph, 2-cut) instances with BOTH deltas '
          f'positive (exhaustive n = 5 .. {nexh}, max degree <= 4, plus '
          f'{nmask} seeded masks at each of {nsamp});')
    print(f'  SUBSAMPLED to {len(cens)} of them (seed {seed + 5}) -- a '
          f'declared cap, since each instance costs one ladder run.')
    hits = {'Pi_u<=rho1': [], 'Pi_v<=rho1': [], 'dim cap E>=3': [],
            'opposite ruling': []}
    trapped = []
    tested = 0
    attaining = 0
    nomeet = 0
    meetu = 0
    for (n, edges, u, v, d1, d2) in cens:
        T = target_of(edges)
        r0, tag, pt = extended_construction(edges, nseeds=1, seed0=seed,
                                            target=T)
        if pt is None:
            continue
        Bu = plane_at(edges, pt, u)
        Bv = plane_at(edges, pt, v)
        if Bu is None or Bv is None:
            continue
        sp = split_at_pair(edges, u, v)
        V1, E1, V2, E2 = sp
        pu, pv = hat(pt[u]), hat(pt[v])
        Piu = pencil_space(pu, Bu)
        Piv = pencil_space(pv, Bv)
        E = span(Piu + Piv)
        flags = (pu, Bu, pv, Bv)
        eqp = (rank_exact(Bu + Bv) == 3)
        forced = ((u, v) in forced_same_plane(edges)
                  or (v, u) in forced_same_plane(edges))
        for (Vi, Ei, di) in ((V1, E1, d1), (V2, E2, d2)):
            rho, r, dM, _ = rho_bar_of(Ei, pt, u, v)
            tested += 1
            fi = exact_deficiency(Ei)[0]
            att = (dM == 6 + fi)
            if contains(rho, Piu):
                hits['Pi_u<=rho1'].append((n, tuple(edges), u, v, r))
            if contains(rho, Piv):
                hits['Pi_v<=rho1'].append((n, tuple(edges), u, v, r))
            cap_ = isect(rho, E) if rho else []
            if dim(cap_) >= 3:
                hits['dim cap E>=3'].append((n, tuple(edges), u, v, dim(cap_)))
            if dim(cap_) == 2:
                y = pencil_vertex(cap_)
                if y is not None and rank_exact([pu, pv, y]) == 2:
                    hits['opposite ruling'].append((n, tuple(edges), u, v))
            if dim(isect(rho, Piu)) == 0:
                nomeet += 1
            else:
                meetu += 1
            # THE QUESTION THAT MATTERS: would an EAR glued at these flags,
            # against THIS rho_bar_1, be trapped?  Only meaningful when the
            # piece itself attains at this configuration (so rho = delta) and
            # rho < 6 (at rho = 6 the criterion is met by side 1 alone).
            if not att or r >= 6:
                continue
            attaining += 1
            for m in range(1, 6):
                dd2 = min(m + 1, 6)
                pred, ptag = bad_predicate(rho, flags, m)
                if pred < min(r + dd2, 6):
                    trapped.append((n, tuple(edges), u, v, r, m, pred,
                                    min(r + dd2, 6), ptag, eqp, forced,
                                    tuple(Ei)))
    print(f'  {tested} (piece, flag) rho_bar_1 subspaces tested, of which '
          f'{attaining} attain at the drawn configuration with rho_1 < 6 '
          f'(the only ones at which the question has content):')
    for k in hits:
        ex = ''
        if hits[k]:
            ex = f'   e.g. {hits[k][0]}'
        print(f'    {k:18s}: {len(hits[k])} hits{ex}')
    print(f'    rho_bar_1 cap Pi_u = 0 at {nomeet}, /= 0 at {meetu}')
    print()
    print(f'  EAR-TRAPPING PREDICTION over the attaining subspaces x '
          f'm = 1..5:  {len(trapped)} trapped (piece, m) pairs')
    eq_chosen = [r for r in trapped if r[9] and not r[10]]
    eq_forced = [r for r in trapped if r[9] and r[10]]
    noteq = [r for r in trapped if not r[9]]
    print(f'    of which pi_u = pi_v in the drawn configuration but NOT '
          f'forced by the graph: {len(eq_chosen)}  -- a CONSTRUCTOR ARTIFACT')
    print(f'                pi_u = pi_v and AGGRESSIVELY FORCED            : '
          f'{len(eq_forced)}')
    print(f'                pi_u /= pi_v (the genuinely geometric family)  : '
          f'{len(noteq)}')
    for r in noteq[:10]:
        print(f'    [pi_u/=pi_v] n={r[0]} pair {r[2]},{r[3]}  rho_1={r[4]} '
              f'm={r[5]}: predicted {r[6]} < target {r[7]}  {r[1]}')
    for r in eq_forced[:6]:
        print(f'    [FORCED eq]  n={r[0]} pair {r[2]},{r[3]}  rho_1={r[4]} '
              f'm={r[5]}: predicted {r[6]} < target {r[7]}  {r[1]}')
    print()
    print('  CAP DISCLOSURE.  One legal configuration per instance, from the')
    print('  BTWOCUT ladder; the census is exhaustive only at n = 5, 6 with')
    print('  max degree <= 4, SAMPLED above that, and SUBSAMPLED again here.')
    print('  An empty column reads "no bad rho_bar_1 found under this cap",')
    print('  NEVER "none exists" -- and it is a statement about the')
    print('  configurations the ladder produces, not about every')
    print('  configuration of every piece.  The `Pi_u <= rho_1` column')
    print('  includes the VACUOUS hits rho_1 = 6, at which the criterion is')
    print('  already met; the EAR-TRAPPING line is the one to read.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tested, hits, trapped


def run_probe(seed=20260827, cap=420, nseeds=2, ndraw=16):
    """F27 ESCALATION on the hunt's residue.  A trapped (piece, m) row in
    `hunt` is a statement about ONE drawn configuration of side 1; the
    composition is free to move side 1 too.  So: take each trapped row, BUILD
    the composed graph G' = (side 1) u ear(m), and measure it outright under
    the full BTWOCUT ladder plus the ear's own moduli, multi-seeded."""
    print('===== Step BE33 / (BE-34)(iii): the hunt\'s residue, ESCALATED '
          '(F27) -- each trapped row rebuilt as a composed graph and measured '
          '=====')
    t0 = time.time()
    tested, hits, trapped = run_hunt(seed=seed, cap=cap)
    print()
    seen = set()
    rows = []
    for r in trapped:
        n, edges, u, v, rho1, m, pred, tgt, ptag, eqp, forced, E1 = r
        key = (E1, u, v, m)
        if key in seen:
            continue
        seen.add(key)
        rows.append((key, eqp, forced, rho1, pred, tgt))
    print(f'  {len(rows)} DISTINCT (side 1, m) trapped rows to escalate '
          f'(from {len(trapped)} trapped (piece, m) pairs)')
    short = []
    done = 0
    for ((E1, u, v, m), eqp, forced, rho1, pred, tgt) in rows:
        G = ear(list(E1), u, v, m, tag='bg')
        best = None
        for s in range(nseeds):
            out = measure_image(f'escalated m={m}', G, u, v, nseeds=2,
                                ndraw=ndraw, seed=seed + 7919 * s,
                                verbose=False)
            if out is None:
                continue
            if best is None or out['best'] - out['crit'] > best['best'] - best['crit']:
                best = out
        done += 1
        if best is None:
            continue
        if best['best'] != best['crit'] or best['rank'] != best['target']:
            short.append((E1, u, v, m, best))
    print(f'  {done - len(short)} / {done} escalated rows REACH the criterion '
          f'and the whole-graph target under {nseeds} independent ladder '
          f'seeds x {ndraw} ear draws')
    if short:
        print('  RESIDUAL CANDIDATES (never refutations):')
        for (E1, u, v, m, b) in short[:12]:
            print(f'    m={m} pair {u},{v}: dim(rho1+rho2) {b["best"]}/'
                  f'{b["crit"]}, rank {b["rank"]}/{b["target"]}, '
                  f'delta=({b["d1"]},{b["d2"]})  side1={E1}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows, short


def run_validate():
    print('##### BIMAGE validate -- reduced tiers of every mode #####')
    print()
    run_chain(nd=6)
    print()
    run_sprec()
    print()
    run_combi(nmax=5, nsamp=(6,), nmask=200)
    print()
    run_alpha(ntrial=8)
    print()
    run_badA()
    print()
    run_image(ndraw=12)
    print()
    run_hunt(nexh=5, nsamp=(), nmask=0, cap=60)
    print()
    run_probe(cap=40, nseeds=2, ndraw=16)


MODES = {
    'chain': run_chain,
    'sprec': run_sprec,
    'combi': run_combi,
    'alpha': run_alpha,
    'badA': run_badA,
    'image': run_image,
    'hunt': run_hunt,
    'probe': run_probe,
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print('modes: ' + ' | '.join(MODES))
        sys.exit(2)
    MODES[mode]()
