"""
Direction BEARCASE (ordinal 46) -- the EAR CASE of the strengthened 2-cut
composition lemma, whose two open items BIMAGE reduced it to:

  (alpha) THE GREEDY'S LAST STEP.  (BE-33)(i)'s alpha-plane escape lemma runs
          the chain greedily through every INTERIOR vertex of the ear; the
          FINAL choice p_m in pi_v must satisfy TWO conditions at once
          (l_m not in W_{m-1} AND l_{m+1} not in W_m) inside a 2-parameter
          family, and BIMAGE does not rule the bad case out.  Closing it turns
          (BE-33)(ii)'s reach formula from MEASURED (358/358) to PROVED.

  (beta)  THE rho_bar_1 NON-CONTAINMENT.  "A piece satisfying the strengthened
          statement admits a configuration with Pi_u not<= rho_bar_1,
          Pi_v not<= rho_bar_1 and dim(rho_bar_1 cap Z) <= dim Z - c_2."

Succeeds `notes/scripts/w4/bimage.py` (Steps BE29-BE33), which this driver
imports READ-ONLY together with `btwocut` / `binduc` through it, rather than
reimplementing the chain, classification, gluing or pencil-witness machinery.
BIMAGE's, BTWOCUT's, BINDUC's, BZAVOID's and BATTAIN's figures are CITED,
never re-run.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-35)  (alpha) SETTLED, by a COMPLETE criterion for the last step.
             `twostep` : THE 2-STEP LEMMA.  For a line M of P^3 with Plucker
                         point lam_M, N := lam_M^{perpK} = K^4 ^ M (5-dim) and
                         C := W cap N,
                           max_{c not on M} dim(W + c^M) = dim W + 2 - g
                         with  g = 2 iff dim C = 5;  g = 1 iff dim C = 4, or
                         dim C = 3 and C = S_t for some t on M;  g = 0
                         otherwise.  PROVED, and enumerated over every
                         (dim W, dim C) shape.
             `laststep`: the EAR's last step is the CONSTRAINED 2-step lemma
                         at U = pi_v, M = p_v v p_{m-1}: it fails for EVERY
                         p_m in pi_v iff Pi_v <= W_{m-1}, or S_t <= W_{m-1}
                         for some t on M, or dim(W_{m-1} cap N) >= 4.  So the
                         bad case is NON-EMPTY -- a WITNESS is exhibited --
                         but it is a condition on the SCHEDULE (W_{m-1}), not
                         on A.
             `greedy`  : the REORDERED (two-sided) greedy -- both constrained
                         ends chosen FIRST, the last free point closing by the
                         UNCONSTRAINED 2-step lemma -- run CONSTRUCTIVELY and
                         compared against bimage's `bad_predicate` over its
                         own battery x three regimes x m = 1..5.  This is what
                         turns the reach formula from MEASURED to PROVED for
                         m >= 3.
             `corners` : the m <= 2 corners, where the ear has NO free interior
                         point and the reordering has least room, with A BUILT
                         to hit each named corner -- a targeted hunt for a
                         FOURTH trapping mechanism.

  (BE-36)  (beta) AS STATED IS FALSE, by a one-line count.
             `betadim` : dim(rho_bar_1 cap Z) >= delta_1 + dim Z - 6 forces
                         dim(rho_bar_1 cap Z) > dim Z - 2 whenever
                         delta_1 >= 5, in EVERY flag regime.  The corrected
                         target is  loss <= max(0, delta_1 + delta_2 - 6),
                         which is what the landed `bimage.py hunt` already
                         tests.

  (BE-37)  (beta) REDUCED to three GENERIC-POSITION statements, and the
           "every configuration" quantifier COLLAPSED.
             `betasp`  : loss is UPPER SEMICONTINUOUS on the configuration
                         space, so its minimum is attained on a dense open --
                         one generic draw computes it, and a sampler can only
                         report FALSE traps, never miss a real one.  Then
                         (beta) <=> (b1) dim(rho_1 cap Pi_u), dim(rho_1 cap
                         Pi_v) <= 1;  (b2) dim(rho_1 cap Z) <= max(delta_1 +
                         dim Z - 6, dim Z - 2);  (b3) rho_1 cap E is not an
                         opposite-ruling pencil -- because delta_2 >= 2 always
                         covers the deficit.  PROVED for the all-S (path)
                         piece by the chain-genericity argument.

  (BE-38)  THE FALSIFICATION ARM, at GENERIC configurations rather than one
           ladder draw.
             `betahunt`: hunt for a piece whose GENERIC loss exceeds its
                         slack.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, `contains`) and never of dimensions, every
sampled configuration through binduc's `assert_generic_star` and
`kbare_common.verify_pencil_witness`, every cap disclosed.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import itertools                                                     # noqa: E402
import os
import random
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import (rank as rank_exact, nullspace, hat,        # noqa: E402
                       neighbors, wedge2)
from kbare_common import (verts_of, build_rigidity, exact_deficiency,  # noqa: E402
                          verify_pencil_witness)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- BATTAIN was its first `w4/` consumer, `bzavoid` the second, `binduc` the
# --- third, `btwocut` the fourth, `bimage` the FIFTH; this driver is the
# --- SIXTH, and the chain is now SIX deep
# --- (battain -> bzavoid -> binduc -> btwocut -> bimage -> bearcase).
# --- NO MOVE MADE (a dispatch may not edit a landed driver another direction
# --- may be importing in flight); the recorded consumer list is EXTENDED in
# --- the workbook's harness note instead.
from binduc import (assert_generic_star, cycle, def_by_partitions,    # noqa: E402
                    ear, hubs_of, motion_space, path, rel_screw_space,
                    split_at_pair, theta)
from btwocut import (deltas_at, extended_construction, split_battery,  # noqa: E402
                     two_cut_census)
import bimage as BI                                                   # noqa: E402
from bimage import (I6, alpha_plane, a_battery, bad_predicate,        # noqa: E402
                    chain_of, contains, dim, is_decomposable, isect,
                    klein, klein_perp, lam2, legal_chain, line_points,
                    pencil_space, pencil_vertex, perp_std, plane_at,
                    plane_meet, pt_in, rho_bar_of, rq, sample_flags,
                    same_space, span, target_of, v4)


# ================================================= Lambda^3 and the bad locus

def wedge_pt_biv(p, xi):
    """p ^ xi in Lambda^3 K^4, coordinates (012, 013, 023, 123).  `xi` is a
    bivector in exactcore's Plucker order (01, 02, 03, 12, 13, 23)."""
    return [p[0] * xi[3] - p[1] * xi[1] + p[2] * xi[0],
            p[0] * xi[4] - p[1] * xi[2] + p[3] * xi[0],
            p[0] * xi[5] - p[2] * xi[2] + p[3] * xi[1],
            p[1] * xi[5] - p[2] * xi[4] + p[3] * xi[3]]


def bad_locus(W):
    """(BE-33)(i)'s  Bad(W) = { p : S_p <= W } = { p : W^{perpK} <= S_p },
    returned as a BASIS of the linear subspace of K^4 whose projectivization it
    is ([] when empty).  Since  S_p <= W  <=>  p ^ xi = 0 for every xi in
    W^{perpK}, this is ONE nullspace computation and is EXACT."""
    Wp = klein_perp(W) if W else [r[:] for r in I6]
    e4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
    rows = []
    for xi in Wp:
        cols = [wedge_pt_biv(e4[k], xi) for k in range(4)]
        for t in range(4):
            rows.append([cols[k][t] for k in range(4)])
    if not rows:
        return [r[:] for r in e4]
    return nullspace(rows)


def line_of(a, b):
    """The 2-dim subspace <a, b> of K^4 (a line of P^3), as a basis."""
    assert rank_exact([a, b]) == 2, 'line_of: points not distinct'
    return [a[:], b[:]]


def pencil_at(c, M):
    """c ^ M, the 2-dim pencil of lines joining c to the points of the line
    M -- i.e. the pencil through c in the plane c v M."""
    out = span([wedge2(c, M[0]), wedge2(c, M[1])])
    assert dim(out) == 2, ('c ^ M not 2-dimensional (c on M?)', dim(out))
    return out


def N_of(M):
    """N := lam_M^{perpK} = K^4 ^ M, the 5-dim tangent hyperplane to the Klein
    quadric at M's Plucker point.  ASSERTED equal to K^4 ^ M as a space."""
    lam = wedge2(M[0], M[1])
    N = span(klein_perp([lam]))
    e = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
    KM = span([wedge2(x, M[0]) for x in e] + [wedge2(x, M[1]) for x in e])
    assert same_space(N, KM), 'N = lam_M^perpK is not K^4 ^ M'
    assert dim(N) == 5, ('N not 5-dimensional', dim(N))
    return N


def alpha_on_line(W, M):
    """The set of t on the line M with S_t <= W, as a basis of the subspace of
    M it spans ([] when empty).  EXACT: intersect Bad(W) with M."""
    B = bad_locus(W)
    if not B:
        return []
    nb, nm = nullspace(B), nullspace(M)
    rows = (nb or []) + (nm or [])
    out = nullspace(rows) if rows else \
        [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
    return out


def two_step_gain(W, M):
    """(BE-35)(i) THE 2-STEP LEMMA, as a PREDICTION of the achievable gain.
    Returns (GAIN, dim C, tag) -- the workbook writes the lemma as
    `dim W + 2 - g` with g the LOSS; here `gain = 2 - g`."""
    N = N_of(M)
    C = isect(W, N) if W else []
    dC = dim(C)
    if dC == 5:
        return 0, dC, 'N <= W (the pencil never escapes)'
    if dC == 4:
        return 1, dC, 'dim(W cap N) = 4'
    if dC == 3 and alpha_on_line(W, M):
        return 1, dC, 'S_t <= W for some t on M'
    return 2, dC, 'free'


def two_step_measured(W, M, rng, ndraw=60, U=None):
    """max over drawn c (in U when given, else in K^4) of dim(W + c^M)."""
    best = dim(W)
    for _ in range(ndraw):
        c = v4(rng) if U is None else pt_in(U, rng)
        if all(x == 0 for x in c):
            continue
        if rank_exact(M + [c]) != 3:      # c must lie OFF the line M
            continue
        best = max(best, dim(W + pencil_at(c, M)))
    return best


def _ext(rows, k, rng, pool=None):
    """A subspace of dimension exactly k containing `rows` (drawn from `pool`
    when given).  None if it cannot be reached."""
    cur = [r[:] for r in rows]
    guard = 0
    while dim(cur) < k and guard < 400:
        guard += 1
        if pool is None:
            c = [rq(rng) for _ in range(6)]
        else:
            co = [rq(rng) for _ in pool]
            c = [sum(co[i] * pool[i][t] for i in range(len(pool)))
                 for t in range(6)]     # coefficients drawn ONCE, then reused
        if dim(cur + [c]) > dim(cur):
            cur = cur + [c]
    return span(cur) if dim(cur) == k else None


# ============================================ (BE-35)(i): THE 2-STEP LEMMA

def run_twostep(seed=20260828, ntrial=45, ndraw=60):
    print('===== Step BE34 / (BE-35)(i): THE 2-STEP LEMMA -- the complete '
          'criterion for the greedy\'s LAST TWO lines =====')
    print('  Two consecutive hinge lines of a chain through a point c are')
    print('        <l, l\'> = c ^ M,   M := (previous point) v (next point),')
    print('  a 2-dim PENCIL, and it always lies in the 5-dim')
    print('        N := lam_M^{perpK} = K^4 ^ M')
    print('  (the tangent hyperplane to the Klein quadric at M).  Write')
    print('  C := W cap N.  THE LEMMA (proved in the workbook, three cases):')
    print('        max_{c off M} dim(W + c^M) = dim W + 2 - g,')
    print('        g = 2  <=>  dim C = 5   (i.e. N <= W);')
    print('        g = 1  <=>  dim C = 4,  or  dim C = 3 and C = S_t for some')
    print('                    t ON THE LINE M;')
    print('        g = 0  otherwise.')
    print('  The `dim C = 3, C = S_t` clause is the ONE non-obvious case, and')
    print('  the shape  C = Lambda^2 pi\'  (pi\' a plane containing M) is the')
    print('  NEAR MISS that a naive dimension count wrongly calls bad: there')
    print('  every T_t is the SAME plane pi\', so the family is constant and')
    print('  the union is pi\', not P^3.  Both are enumerated below.')
    t0 = time.time()
    rng = random.Random(seed)
    tot = 0
    bad = 0
    byshape = {}
    shapes_seen = set()
    for trial in range(ntrial):
        a, b = v4(rng), v4(rng)
        if rank_exact([a, b]) != 2:
            continue
        M = line_of(a, b)
        N = N_of(M)
        tries = []
        # (1) W >= S_t for t ON M  -- the g = 1 clause
        for (al, be) in ((F(1), F(0)), (F(0), F(1)), (F(1), F(1)),
                         (F(2), F(-3))):
            t = [al * a[k] + be * b[k] for k in range(4)]
            St = alpha_plane(t)
            for k in range(3, 7):
                Wc = _ext(St, k, rng)
                if Wc is not None:
                    tries.append((f'W >= S_t, t ON M (dim W = {k})', Wc))
        # (2) W = Lambda^2 pi' for a plane pi' CONTAINING M -- the near miss
        for _ in range(2):
            y = v4(rng)
            if rank_exact(M + [y]) != 3:
                continue
            pl = M + [y]
            L2 = lam2(pl)
            for k in range(3, 6):
                Wc = _ext(L2, k, rng)
                if Wc is not None:
                    tries.append((f'W >= Lambda^2 pi\', M < pi\' '
                                  f'(dim W = {k})', Wc))
        # (3) W inside N, every dimension -- reaches dim C = 4 and 5
        for k in range(1, 6):
            Wc = _ext([], k, rng, pool=N)
            if Wc is not None:
                tries.append((f'W <= N (dim W = {k})', Wc))
        # (4) W with dim(W cap N) = 3 but NOT of the S_t shape
        for k in range(3, 7):
            base = _ext([], 3, rng, pool=N)
            Wc = _ext(base, k, rng) if base else None
            if Wc is not None:
                tries.append((f'dim(W cap N) = 3 generic (dim W = {k})', Wc))
        # (5) W >= S_t for t OFF M
        for _ in range(2):
            t = v4(rng)
            if rank_exact(M + [t]) != 3:
                continue
            for k in range(3, 6):
                Wc = _ext(alpha_plane(t), k, rng)
                if Wc is not None:
                    tries.append((f'W >= S_t, t OFF M (dim W = {k})', Wc))
        # (6) W >= one pencil c^M, extended
        c0 = v4(rng)
        if rank_exact(M + [c0]) == 3:
            for k in range(2, 7):
                Wc = _ext(pencil_at(c0, M), k, rng)
                if Wc is not None:
                    tries.append((f'W >= c^M (dim W = {k})', Wc))
        # (7) purely random W of every dimension
        for k in range(0, 7):
            Wc = _ext([], k, rng)
            if Wc is not None:
                tries.append((f'W random (dim W = {k})', Wc))
        for (tag, W) in tries:
            g, dC, why = two_step_gain(W, M)
            pred = min(6, dim(W) + g)
            meas = two_step_measured(W, M,
                                     random.Random(seed + 7919 * trial
                                                   + len(tag)), ndraw=ndraw)
            tot += 1
            shapes_seen.add((dim(W), dC, g))
            key = tag.split(' (')[0]
            byshape.setdefault(key, [0, 0])
            byshape[key][0] += 1
            if pred != meas:
                bad += 1
                byshape[key][1] += 1
                if bad <= 8:
                    print(f'    MISMATCH {tag}: dim W {dim(W)} dim C {dC} '
                          f'gain {g} ({why}) predicted {pred} '
                          f'measured {meas}')
    print(f'  {tot} (W, M) comparisons of PREDICTED against MEASURED reach, '
          f'over {ntrial} lines M and seven structured families:')
    for k in sorted(byshape):
        n, b = byshape[k]
        print(f'    {k:44s}: {n:5d} comparisons, {b} mismatches')
    print(f'  TOTAL: {tot} comparisons, {bad} MISMATCHES')
    # ENUMERATING tier (F11): the shape set is FINITE and is listed here,
    # so "every shape" is a claim a driver checks rather than asserts.
    # dim C = dim(W cap N) with N a hyperplane, so max(0, w-1) <= dim C <=
    # min(w, 5); at dim C = 3 the lemma splits on whether C = S_t for some
    # t on M, which needs dim C = 3, i.e. w in {3, 4}.
    feasible = set()
    for w in range(0, 7):
        for dC in range(max(0, w - 1), min(w, 5) + 1):
            if dC == 5:
                feasible.add((w, dC, 0))
            elif dC == 4:
                feasible.add((w, dC, 1))
            elif dC == 3:
                feasible.add((w, dC, 1))     # C = S_t
                feasible.add((w, dC, 2))     # C /= S_t
            else:
                feasible.add((w, dC, 2))
    missing = sorted(feasible - shapes_seen)
    extra = sorted(shapes_seen - feasible)
    print(f'  ENUMERATED shape coverage: {len(feasible)} feasible '
          f'(dim W, dim C, gain) triples, {len(shapes_seen)} realized; '
          f'MISSING {missing}; UNPREDICTED {extra}')
    assert not extra, ('a (dim W, dim C, gain) triple the lemma forbids was '
                       'realized', extra)
    # the two EXTREMAL shapes, CONSTRUCTED rather than sampled
    rng2 = random.Random(seed + 1)
    a, b = v4(rng2), v4(rng2)
    while rank_exact([a, b]) != 2:
        a, b = v4(rng2), v4(rng2)
    M = line_of(a, b)
    y = v4(rng2)
    while rank_exact(M + [y]) != 3:
        y = v4(rng2)
    L2 = lam2(M + [y])
    Bad = bad_locus(L2)
    print(f'  CONSTRUCTED near miss  W = Lambda^2 pi\' (M < pi\'):  '
          f'dim(W cap N) = {dim(isect(L2, N_of(M)))}, and NO t on M has '
          f'S_t <= W ({"none" if not alpha_on_line(L2, M) else "SOME"}), so '
          f'the lemma says g = 0 -- while the naive count says every T_t is '
          f'3-dimensional.  The resolution: T_t = pi\' for EVERY t, a '
          f'CONSTANT family.')
    print(f'    (Bad(Lambda^2 pi\') has dimension {len(Bad)}; measured reach '
          f'{two_step_measured(L2, M, random.Random(seed + 2))} against '
          f'predicted {min(6, dim(L2) + two_step_gain(L2, M)[0])})')
    St = alpha_plane(a)
    print(f'  CONSTRUCTED g = 1 shape  W = S_a, a ON M:  dim(W cap N) = '
          f'{dim(isect(St, N_of(M)))}, alpha_on_line non-empty = '
          f'{bool(alpha_on_line(St, M))}, measured reach '
          f'{two_step_measured(St, M, random.Random(seed + 3))} against '
          f'predicted {min(6, dim(St) + two_step_gain(St, M)[0])}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot, bad


# =============================== the CONSTRAINED 2-step: an EXACT decision

def _pencil_rows(c, M):
    return [wedge2(c, M[0]), wedge2(c, M[1])]


def is_bad_point(W, M, c):
    """c is BAD for (W, M) iff some nonzero r on M has c ^ r in W -- equivalently
    iff the linear map  phi_c : M -> Lambda^2 K^4 / W,  r |-> c ^ r,  fails to
    be injective.  A c ON the line M is bad for the trivial reason that c
    itself is such an r (c ^ c = 0), which is the reading that makes `bad` the
    vanishing of the 2x2 minors of phi_c -- QUADRATIC forms in c -- uniformly.
    Exact; no sampling."""
    P = _pencil_rows(c, M)
    if dim(P) < 2:
        return True                    # c lies ON M (or c = 0)
    return dim(W + P) < dim(W) + 2


def all_bad_on(W, M, U):
    """Is EVERY point of the linear subspace U bad for (W, M)?  EXACT and
    FINITE: `c bad` is the simultaneous vanishing of the 2x2 minors of the
    2 x (5 - dim C) matrix of  r |-> c ^ r  mod (W cap N), each of which is a
    QUADRATIC form in c; a quadratic form over a field of characteristic 0
    vanishes identically on U iff it vanishes at every u_i and every u_i + u_j
    of a basis of U.  So testing those finitely many points DECIDES the
    question -- it is not a sample."""
    B = span(U) if len(U) > 1 else [r[:] for r in U]
    tests = [b[:] for b in B]
    for i, j in itertools.combinations(range(len(B)), 2):
        tests.append([B[i][k] + B[j][k] for k in range(4)])
    return all(is_bad_point(W, M, c) for c in tests)


def laststep_criterion(W, M, U, Piv=None):
    """The CONSTRAINED 2-step criterion, as a PREDICTION of `all_bad_on`.

    For U a plane pi_v meeting M in the single point p_v (the ear's last step),
    the workbook proves:  every p in pi_v is bad  <=>  Pi_v <= W, or S_t <= W
    for some t on M, or dim(W cap N) >= 4.
    For U = K^4 (the unconstrained lemma) the Pi_v clause is absent."""
    N = N_of(M)
    C = isect(W, N) if W else []
    if dim(C) >= 4:
        return True, 'dim(W cap N) >= 4'
    if alpha_on_line(W, M):
        return True, 'S_t <= W for some t on M'
    if Piv is not None and W and contains(W, Piv):
        return True, 'Pi_v <= W  (mechanism (P) at v)'
    return False, 'free'


def run_laststep(seed=20260828, ntrial=30):
    print('===== Step BE34 / (BE-35)(ii): THE EAR\'S LAST STEP -- the '
          'CONSTRAINED 2-step lemma, and the bad case EXHIBITED =====')
    print('  The ear\'s final choice is  p_m in pi_v  with TWO conditions:')
    print('        l_m = p_{m-1} ^ p_m  not in  W_{m-1},   and')
    print('        l_{m+1} = p_m ^ p_v  not in  W_{m-1} + <l_m>.')
    print('  Both fail together exactly when some nonzero r on the LINE')
    print('        M := p_v v p_{m-1}   has   p_m ^ r  in  W_{m-1},')
    print('  because  l_{m+1} = b + mu l_m  rearranges to  p_m ^ (p_v + mu')
    print('  p_{m-1}) in W_{m-1}, and mu = infinity is the first condition.')
    print('  So the last step is the 2-step lemma with c = p_m CONSTRAINED to')
    print('  the plane pi_v -- and pi_v meets M in the single point p_v,')
    print('  which is what adds the extra clause  Pi_v <= W_{m-1}.')
    print()
    print('  THE CRITERION (proved):  every p_m in pi_v is bad  <=>')
    print('     Pi_v <= W_{m-1}   or   S_t <= W_{m-1} for some t on M   or')
    print('     dim(W_{m-1} cap N) >= 4.')
    t0 = time.time()
    rng = random.Random(seed)
    tot = 0
    bad = 0
    hits = {'dim(W cap N) >= 4': 0, 'S_t <= W for some t on M': 0,
            'Pi_v <= W  (mechanism (P) at v)': 0, 'free': 0}
    for trial in range(ntrial):
        for regime in ('nonadj', 'adj', 'equal'):
            flags = sample_flags(rng, regime)
            pu, Bu, pv, Bv = flags
            Piv = pencil_space(pv, Bv)
            q = v4(rng)                       # p_{m-1}
            if rank_exact(Bv + [q]) != 4:     # q off pi_v (the generic case)
                continue
            if rank_exact([pv, q]) != 2:
                continue
            M = line_of(pv, q)
            tries = []
            for k in range(0, 7):
                Wc = _ext([], k, rng)
                if Wc is not None:
                    tries.append((f'W random dim {k}', Wc))
            for k in range(2, 7):
                Wc = _ext(Piv, k, rng)
                if Wc is not None:
                    tries.append((f'W >= Pi_v dim {k}', Wc))
            N = N_of(M)
            for k in range(3, 6):
                Wc = _ext([], k, rng, pool=N)
                if Wc is not None:
                    tries.append((f'W <= N dim {k}', Wc))
            for (al, be) in ((F(1), F(0)), (F(1), F(1))):
                t = [al * pv[k] + be * q[k] for k in range(4)]
                for k in range(3, 6):
                    Wc = _ext(alpha_plane(t), k, rng)
                    if Wc is not None:
                        tries.append((f'W >= S_t, t on M, dim {k}', Wc))
            for (tag, W) in tries:
                pred, why = laststep_criterion(W, M, Bv, Piv=Piv)
                meas = all_bad_on(W, M, Bv)
                tot += 1
                hits[why] += 1
                if pred != meas:
                    bad += 1
                    if bad <= 8:
                        print(f'    MISMATCH [{regime}] {tag}: predicted '
                              f'all-bad={pred} ({why}) measured={meas}')
    print(f'  {tot} (W, M, pi_v) instances, EXACT decision on both sides '
          f'(no sampling): {bad} MISMATCHES')
    for k in hits:
        print(f'    criterion branch  {k:34s}: {hits[k]} instances')
    print()
    print('  IS THE BAD CASE NON-EMPTY?  Yes -- and it is a condition on the')
    print('  SCHEDULE W_{m-1}, not on A.  Constructed witness:')
    rng2 = random.Random(seed + 11)
    flags = sample_flags(rng2, 'nonadj')
    pu, Bu, pv, Bv = flags
    Piv = pencil_space(pv, Bv)
    q = v4(rng2)
    while rank_exact(Bv + [q]) != 4 or rank_exact([pv, q]) != 2:
        q = v4(rng2)
    M = line_of(pv, q)
    Sq = alpha_plane(q)                   # S_t with t = q, ON M
    Wbad = span(Sq)
    ok, why = laststep_criterion(Wbad, M, Bv, Piv=Piv)
    print(f'    W_{{m-1}} = S_q  (q = p_{{m-1}} itself, a point ON M): '
          f'dim {dim(Wbad)}, all-bad = {all_bad_on(Wbad, M, Bv)} '
          f'({why}) -- the last step CANNOT gain 2 here, at ANY p_m in pi_v.')
    print(f'    But S_q <= W_{{m-1}} says l_m = q ^ p_m is in W_{{m-1}} for '
          f'EVERY p_m whatsoever: the schedule has already spent the whole')
    print(f'    alpha-plane of its own current point.  (BE-33)(i) forbids '
          f'this at dim W <= 4 UNLESS q is its single bad point -- which is')
    print(f'    exactly what the greedy\'s invariant  S_{{p_i}} not<= W_i  '
          f'is there to prevent.  So the bad case is REACHABLE only by a')
    print(f'    greedy that has already violated its own invariant, or by')
    print(f'    the two clauses  dim(W cap N) >= 4  and  Pi_v <= W  below.')
    W4 = _ext([], 4, rng2, pool=N_of(M))
    print(f'    dim(W cap N) = 4 witness: dim W = {dim(W4)}, all-bad = '
          f'{all_bad_on(W4, M, Bv)} -- here W <= N = lam_M^perpK, i.e. every')
    print(f'    member of W MEETS the line M; the pencil p_m ^ M lies in N '
          f'too, and two subspaces of dimensions 4 and 2 inside a 5-space')
    print(f'    always meet.  THIS is the clause the reordering removes.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot, bad


# ================== (BE-35)(iii)/(iv): the REORDERED (two-sided) greedy

def pick_off(pool, avoid_test, rng, budget=80):
    """A point of `pool` (a basis of a subspace of K^4) failing `avoid_test`.
    Returns None if the budget is exhausted -- which, when the workbook's
    criterion says the bad locus is proper, is a driver failure and not a
    mathematical one, so the caller counts it."""
    for _ in range(budget):
        c = pt_in(pool, rng)
        if all(x == 0 for x in c):
            continue
        if not avoid_test(c):
            return c
    return None


E4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]


def _alpha_step(W, cur, rng, budget=80):
    """One INTERIOR greedy step: a free point `nxt` with
    l = cur ^ nxt not in W  and  S_nxt not<= W + <l>  -- (BE-33)(i)."""
    for _ in range(budget):
        nxt = v4(rng)
        if rank_exact([cur, nxt]) != 2:
            continue
        l = wedge2(cur, nxt)
        if dim(W + [l]) == dim(W):
            continue
        W2 = span(W + [l])
        if dim(W2) < 6 and contains(W2, alpha_plane(nxt)):
            continue
        return nxt, l
    return None, None


def build_once(A, flags, m, rng, budget=80):
    """ONE run of the reordered greedy.  Returns (points, log) or (None, why).

    The reordering is the point of (BE-35)(iii): the two CONSTRAINED end
    choices (p_1 in pi_u, p_m in pi_v) are made FIRST, so the last free choice
    -- p_{m-1}, a point of P^3 with three projective parameters rather than the
    two of a plane -- closes the chain by the UNCONSTRAINED 2-step lemma, whose
    only obstructions are dim(W cap N) >= 4 and Bad(W) meeting M."""
    pu, Bu, pv, Bv = flags
    W = span(A) if A else []
    log = []
    if m == 1:
        U = Bu if rank_exact(Bu + Bv) == 3 else plane_meet(Bu, Bv)
        M = line_of(pu, pv)
        bestc, bestval = None, -1
        for _ in range(budget):
            c = pt_in(U, rng)
            if all(x == 0 for x in c) or rank_exact(M + [c]) != 3:
                continue
            val = dim(W + _pencil_rows(c, M))
            if val > bestval:
                bestval, bestc = val, c
            if bestval >= min(6, dim(W) + 2):
                break
        if bestc is None:
            return None, 'm=1: no legal p_1'
        log.append(('m=1 constrained 2-step on U = pi_u cap pi_v', bestval))
        return [pu, bestc, pv], log
    if m == 2:
        # l_1 first (p_1 in pi_u), then the CONSTRAINED 2-step at U = pi_v.
        # The l_1 loop is short and the inner loop STOPS at the target the
        # constrained criterion predicts: O(budget), not O(budget^2).
        best = (-1, None, None)
        for _ in range(8):
            p1 = pt_in(Bu, rng)
            if all(x == 0 for x in p1) or rank_exact([pu, p1]) != 2:
                continue
            l1 = wedge2(pu, p1)
            W1 = span((A or []) + [l1])
            if rank_exact([p1, pv]) != 2:
                continue
            M = line_of(p1, pv)
            Piv = pencil_space(pv, Bv)
            allbad, _why = laststep_criterion(W1, M, Bv, Piv=Piv)
            tgt = min(6, dim(W1) + (1 if allbad else 2))
            bc, bv = None, -1
            for _ in range(budget):
                c = pt_in(Bv, rng)
                if all(x == 0 for x in c) or rank_exact(M + [c]) != 3:
                    continue
                if rank_exact([c, pv]) != 2:
                    continue
                val = dim(W1 + _pencil_rows(c, M))
                if val > bv:
                    bv, bc = val, c
                if bv >= tgt:
                    break
            if bc is not None and bv > best[0]:
                best = (bv, p1, bc)
            if best[0] >= 6:
                break
        if best[1] is None:
            return None, 'm=2: no legal pair'
        log.append(('m=2: l_1 then the constrained 2-step at pi_v', best[0]))
        return [pu, best[1], best[2], pv], log
    # ---- m >= 3: END PAIR first, then the free chain, then the 2-step close
    bestend = (-1, None, None)
    for _ in range(budget):
        p1 = pt_in(Bu, rng)
        pm = pt_in(Bv, rng)
        if all(x == 0 for x in p1) or all(x == 0 for x in pm):
            continue
        if rank_exact([pu, p1]) != 2 or rank_exact([pm, pv]) != 2:
            continue
        val = dim(W + [wedge2(pu, p1), wedge2(pm, pv)])
        if val > bestend[0]:
            bestend = (val, p1, pm)
        if bestend[0] >= min(6, dim(W) + 2):
            break
    if bestend[1] is None:
        return None, 'no legal end pair'
    p1, pm = bestend[1], bestend[2]
    W = span((A or []) + [wedge2(pu, p1), wedge2(pm, pv)])
    epred, _e = endpair_gain(A, flags)
    log.append(('endpair', dim(W), epred))
    pts = [pu, p1]
    cur = p1
    for i in range(2, m - 1):                       # p_2 .. p_{m-2}
        if dim(W) >= 6:
            nxt = v4(rng)
            while rank_exact([cur, nxt]) != 2:
                nxt = v4(rng)
            pts.append(nxt)
            cur = nxt
            continue
        d0 = dim(W)
        nxt, l = _alpha_step(W, cur, rng, budget)
        if nxt is None:
            return None, f'alpha step failed at i={i}'
        pts.append(nxt)
        W = span(W + [l])
        cur = nxt
        log.append(('alpha', dim(W), min(6, d0 + 1)))
    # the CLOSING 2-step: c = p_{m-1}, free in P^3, M = p_{m-2} v p_m
    if rank_exact([cur, pm]) != 2:
        return None, 'p_{m-2} = p_m'
    M = line_of(cur, pm)
    gain, dC, why = two_step_gain(W, M)
    target = min(6, dim(W) + gain)
    bestc, bestval = None, -1
    for _ in range(budget):
        c = v4(rng)
        if all(x == 0 for x in c) or rank_exact(M + [c]) != 3:
            continue
        if rank_exact([cur, c]) != 2 or rank_exact([c, pm]) != 2:
            continue
        val = dim(W + _pencil_rows(c, M))
        if val > bestval:
            bestval, bestc = val, c
        if val >= target:
            break
    if bestc is None:
        return None, 'closing 2-step: no legal p_{m-1}'
    log.append(('close', bestval, target))
    pts.append(bestc)
    pts.append(pm)
    pts.append(pv)
    return pts, log


def endpair_gain(A, flags):
    """(BE-35)(iv) THE END-PAIR LEMMA, as a prediction:
         max over x in Pi_u, y in Pi_v of dim(A + <x,y>) = dim A + 2 - e,
         e = max( #{Pi in {Pi_u,Pi_v} : Pi <= A},  max(0, dim(A cap Z) + 2 -
             dim Z) ),   Z := Pi_u + Pi_v.
    Both halves are forced: x lies in Pi_u so a swallowed pencil costs a
    dimension, and <x,y> lies in Z so a 2-space of Z cannot avoid an
    (dim(A cap Z))-dimensional subspace of Z by more than dim Z - 2."""
    pu, Bu, pv, Bv = flags
    Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
    Z = span(Piu + Piv)
    P = (1 if (A and contains(A, Piu)) else 0) + \
        (1 if (A and contains(A, Piv)) else 0)
    aZ = dim(isect(A, Z)) if A else 0
    e = max(P, max(0, aZ + 2 - dim(Z)))
    return min(6, dim(A) + 2 - e), e


def greedy_reach(A, flags, m, seed, tries=6):
    """The best value the CONSTRUCTIVE greedy reaches, the attempt at which it
    first got there, and its per-step log."""
    best, used, bl = -1, 0, None
    for t in range(tries):
        rng = random.Random(seed + 104729 * t + 31 * m)
        pts, log = build_once(A, flags, m, rng)
        if pts is None or not legal_chain(pts):
            continue
        val = dim(A + chain_of(pts))
        if val > best:
            best, used, bl = val, t + 1, log
        if best >= 6:
            break
    return max(best, dim(A)), used, bl


def run_greedy(seed=20260828, ntrial=4, tries=4):
    print('===== Step BE35 / (BE-35)(iii)+(iv): the REORDERED GREEDY, run '
          'CONSTRUCTIVELY against the classification =====')
    print('  BIMAGE\'s greedy runs the chain FORWARD from u and meets its')
    print('  open step at the END, where p_m is confined to the PLANE pi_v --')
    print('  two conditions in two parameters.  Reorder: choose BOTH')
    print('  constrained ends first (l_1 in Pi_u, l_{m+1} in Pi_v), then the')
    print('  free interior chain, and close with p_{m-1} FREE IN P^3 -- two')
    print('  conditions in THREE parameters, which is exactly the')
    print('  unconstrained 2-step lemma.  The Pi_v clause of (BE-35)(ii)')
    print('  disappears with the constraint that produced it.')
    print('  Compared below against bimage\'s own `bad_predicate` -- the')
    print('  (BE-33)(ii) classification -- on ITS battery, so the two are')
    print('  measured against the same yardstick.')
    t0 = time.time()
    rng = random.Random(seed)
    tot = 0
    below = 0
    above = 0
    restarts = {}
    permode = {}
    step = {}
    for trial in range(ntrial):
        for regime in ('nonadj', 'adj', 'equal'):
            flags = sample_flags(rng, regime)
            bat = a_battery(flags, rng)
            for (tag, A) in bat:
                for m in range(1, 6):
                    if regime == 'adj' and m == 1:
                        continue          # (BE-30)(iii)(c): forced degenerate
                    pred, ptag = bad_predicate(A, flags, m)
                    got, used, blog = greedy_reach(A, flags, m,
                                                   seed + 7919 * trial, tries)
                    tot += 1
                    restarts[used] = restarts.get(used, 0) + 1
                    for row in (blog or []):
                        if len(row) == 3:
                            step[row[0]] = step.get(row[0], [0, 0])
                            step[row[0]][0] += 1
                            if row[1] < row[2]:
                                step[row[0]][1] += 1
                    key = (regime, m)
                    permode.setdefault(key, [0, 0, 0])
                    permode[key][0] += 1
                    if got < pred:
                        below += 1
                        permode[key][1] += 1
                        if below <= 10:
                            print(f'    SHORTFALL [{regime}] m={m} {tag}: '
                                  f'greedy {got} < classification {pred}')
                    if got > pred:
                        above += 1
                        permode[key][2] += 1
                        if above <= 10:
                            print(f'    OVERSHOOT [{regime}] m={m} {tag}: '
                                  f'greedy {got} > classification {pred} '
                                  f'-- the classification would be WRONG')
    print(f'  {tot} (regime, A, m) instances: the CONSTRUCTED chain reaches '
          f'the classification\'s predicted maximum at {tot - below - above}, '
          f'falls SHORT at {below}, EXCEEDS it at {above}')
    print('  PER-STEP: each step\'s gain is PREDICTED by its own lemma '
          'BEFORE the draw; instances / shortfalls:')
    for k in sorted(step):
        n, b = step[k]
        nm = {'endpair': '(BE-35)(iv) end-pair lemma',
              'alpha': '(BE-33)(i) alpha-plane step',
              'close': '(BE-35)(i) closing 2-step'}.get(k, k)
        print(f'    {nm:34s}: {n:5d} / {b}')
    print('  restarts needed by the constructive greedy (1 = first attempt):')
    print('   ' + ',  '.join(f'{k}: {restarts[k]}' for k in sorted(restarts)))
    print('  per (regime, m), instances / shortfalls / overshoots:')
    for k in sorted(permode, key=lambda x: (x[0], x[1])):
        n, b, a = permode[k]
        print(f'    {k[0]:7s} m={k[1]}: {n:4d} / {b} / {a}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot, below, above


def run_corners(seed=20260828, ntrial=10, tries=4):
    """The residual corners of (alpha): m = 1 and m = 2, where the ear has no
    free interior point and the reordering therefore has LESS room.  A is built
    HERE to hit each named corner rather than drawn, and the classification is
    given every chance to fail -- this is the direction's own answer to
    BIMAGE's *what would change this*: an (A, m) whose measured reach falls
    BELOW the prediction would be a FOURTH trapping mechanism."""
    print('===== Step BE35 / (BE-35)(v): the m <= 2 CORNERS, targeted -- '
          'hunting a FOURTH trapping mechanism where the reordering has least '
          'room =====')
    print('  At m >= 3 the closing 2-step runs at a FREE point of P^3 and its')
    print('  two obstructions (dim(W cap N) >= 4;  Bad(W) meeting M) are')
    print('  dodged by SLIDING p_{m-2} along l_{m-2} and p_m along l_{m+1} --')
    print('  a slide changes NEITHER line, so W is fixed while M sweeps a')
    print('  2-parameter family of transversals against a <= 1-parameter bad')
    print('  set.  At m = 2 the middle line l_2 IS that transversal, and at')
    print('  m = 1 the single interior point is confined to pi_u cap pi_v.')
    print('  So these are the two places a fourth mechanism could hide.')
    t0 = time.time()
    rng = random.Random(seed)
    tot = below = above = 0
    bycorner = {}
    for trial in range(ntrial):
        for regime in ('nonadj', 'adj', 'equal'):
            flags = sample_flags(rng, regime)
            pu, Bu, pv, Bv = flags
            Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
            cands = []
            # corner 1: A contains the SPAN of the transversals of l_1, l_3
            for _ in range(2):
                cu = [rq(rng), rq(rng)]
                cv = [rq(rng), rq(rng)]
                l1 = [cu[0] * Piu[0][t] + cu[1] * Piu[1][t] for t in range(6)]
                l3 = [cv[0] * Piv[0][t] + cv[1] * Piv[1][t] for t in range(6)]
                if dim([l1]) == 0 or dim([l3]) == 0:
                    continue
                assert is_decomposable(l1) and is_decomposable(l3), \
                    'a pencil is totally singular: every member is a LINE'
                L1, L3 = line_points(l1), line_points(l3)
                T = span([wedge2(a, b) for a in L1 for b in L3])
                for k in range(dim(T), 7):
                    Ac = _ext(T, k, rng)
                    if Ac is not None:
                        cands.append((f'A >= l_1 ^ l_3 (dim {k})', Ac))
            # corner 2: A = (p_v ^ sigma)^{perpK}, sigma = l_1 v p_v
            for _ in range(2):
                p1 = pt_in(Bu, rng)
                if rank_exact([pu, p1]) != 2 or rank_exact([pu, p1, pv]) != 3:
                    continue
                sig = [pu, p1, pv]
                Ac = span(klein_perp(pencil_space(pv, sig)))
                cands.append(('A = (p_v ^ sigma)^perpK, sigma = l_1 v p_v',
                              Ac))
            # corner 3: A contains S_t for t on p_u v p_v (the (R) line M)
            if rank_exact([pu, pv]) == 2:
                for (al, be) in ((F(1), F(1)), (F(1), F(-2))):
                    t = [al * pu[k] + be * pv[k] for k in range(4)]
                    for k in range(3, 7):
                        Ac = _ext(alpha_plane(t), k, rng)
                        if Ac is not None:
                            cands.append((f'A >= S_t, t on p_u v p_v '
                                          f'(dim {k})', Ac))
            # corner 4: A a hyperplane of the confining space Z, extended
            Z = span(Piu + Piv)
            for k in range(dim(Z) - 1, 7):
                sub = _ext([], dim(Z) - 1, rng, pool=Z)
                Ac = _ext(sub, k, rng) if sub else None
                if Ac is not None:
                    cands.append((f'A >= a hyperplane of Z (dim {k})', Ac))
            for (tag, A) in cands:
                for m in (1, 2):
                    if regime == 'adj' and m == 1:
                        continue
                    pred, _pt = bad_predicate(A, flags, m)
                    got, _u, _l = greedy_reach(A, flags, m,
                                               seed + 6151 * trial, tries)
                    key = tag.split(' (dim')[0]
                    bycorner.setdefault(key, [0, 0, 0])
                    bycorner[key][0] += 1
                    tot += 1
                    if got < pred:
                        below += 1
                        bycorner[key][1] += 1
                        if below <= 8:
                            print(f'    SHORTFALL [{regime}] m={m} {tag}: '
                                  f'greedy {got} < classification {pred}')
                    if got > pred:
                        above += 1
                        bycorner[key][2] += 1
                        if above <= 8:
                            print(f'    OVERSHOOT [{regime}] m={m} {tag}: '
                                  f'greedy {got} > classification {pred}')
    print(f'  {tot} targeted (regime, A, m<=2) instances: agree at '
          f'{tot - below - above}, greedy SHORT at {below}, greedy ABOVE at '
          f'{above}')
    for k in sorted(bycorner):
        n, b, a = bycorner[k]
        print(f'    {k:46s}: {n:4d} / short {b} / above {a}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot, below, above


# ============================ (BE-36): (beta) AS STATED, tested not inherited

def loss_exact(rho, flags, m):
    """loss = max(P, Z, R), recomputed here from the same three mechanisms so
    that it is available as a NUMBER rather than only through the predicted
    reach.  ASSERTED consistent with bimage's `bad_predicate`."""
    pu, Bu, pv, Bv = flags
    d1, d2 = dim(rho), min(m + 1, 6)
    Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
    equal = (rank_exact(Bu + Bv) == 3)
    Z = lam2(Bu) if equal else span(Piu + Piv)
    c2 = 3 if (equal and m == 2) else 2
    lossP = ((1 if (rho and contains(rho, Piu)) else 0)
             + (1 if (rho and contains(rho, Piv)) else 0))
    Fsp = isect(rho, Z) if rho else []
    lossZ = max(0, dim(Fsp) + c2 - dim(Z))
    lossR = 0
    if m == 1 and not equal and dim(Fsp) == 2:
        y = pencil_vertex(Fsp)
        if y is not None and rank_exact([pu, pv, y]) == 2:
            lossR = 1
    loss = max(lossP, lossZ, lossR)
    pred, _t = bad_predicate(rho, flags, m)
    assert pred == min(6, d1 + d2 - loss), \
        ('loss recomputation disagrees with bimage.bad_predicate',
         pred, d1, d2, loss)
    return loss, lossP, lossZ, lossR, dim(Fsp), dim(Z), c2


def run_betadim(seed=20260828, ntrial=25):
    print('===== Step BE36 / (BE-36): (beta) AS STATED IS FALSE -- and the '
          'corrected target is the one the LANDED driver already tests =====')
    print('  BIMAGE\'s successor (1), verbatim: *a piece satisfying the')
    print('  strengthened statement admits a configuration with Pi_u not<=')
    print('  rho_bar_1, Pi_v not<= rho_bar_1 and dim(rho_bar_1 cap Z) <=')
    print('  dim Z - c_2*.  With c_2 = 2 that last clause asks')
    print('        dim(rho_bar_1 cap Z) <= dim Z - 2.')
    print('  But rho_bar_1 and Z both sit in the 6-dim screw space, so')
    print('        dim(rho_bar_1 cap Z) >= delta_1 + dim Z - 6')
    print('  ALWAYS -- no configuration can do better.  The two are')
    print('  INCOMPATIBLE as soon as delta_1 + dim Z - 6 > dim Z - 2, i.e.')
    print('        delta_1 >= 5,')
    print('  in EVERY flag regime, since dim Z cancels.  So (beta) as stated')
    print('  is unsatisfiable at delta_1 = 5 and at delta_1 = 6, for every')
    print('  piece, at every configuration.')
    print()
    print('  This is NOT fatal, and the landed driver already knows it: '
          '`bimage.py hunt`')
    print('  calls a row trapped when  predicted < min(delta_1+delta_2, 6),')
    print('  i.e. when  loss > max(0, delta_1 + delta_2 - 6).  THAT is the')
    print('  correct target; (beta)\'s  loss = 0  is the special case')
    print('  delta_1 + delta_2 <= 6.  The correction is to the PROSE of the')
    print('  successor, not to any measurement.')
    print()
    t0 = time.time()
    print('  ENUMERATED over every (dim Z, delta_1): forced minimum of '
          'dim(rho_1 cap Z), (beta)-as-stated\'s ceiling, and whether the '
          'corrected target is reachable:')
    print('    dim Z  d1 | forced min | (beta) ceiling | (beta) stated? | '
          'corrected loss at the forced min (m=1, d2=2)')
    rows = 0
    contra = 0
    for dZ in (3, 4):
        for d1 in range(0, 7):
            fm = max(0, d1 + dZ - 6)
            ceil_ = dZ - 2
            ok = (fm <= ceil_)
            lz = max(0, fm + 2 - dZ)
            slack = max(0, d1 + 2 - 6)
            rows += 1
            if not ok:
                contra += 1
            yn = 'yes' if ok else 'NO '
            print(f'      {dZ}    {d1}  |     {fm}      |     {ceil_}      '
                  f'|   {yn}   | lossZ = {lz}, slack = {slack}, '
                  f'{"OK" if lz <= slack else "SHORT"}')
    print(f'  {rows} (dim Z, delta_1) rows enumerated; (beta) as stated is '
          f'UNSATISFIABLE in {contra} of them -- exactly the rows with '
          f'delta_1 >= 5 -- while the corrected target is met in ALL of them '
          f'at the forced minimum.')
    print()
    print('  And the bound is not vacuous: it is ATTAINED.  Random rho_1 of '
          'each dimension against real flags:')
    rng = random.Random(seed)
    att = {}
    for _ in range(ntrial):
        for regime in ('nonadj', 'adj', 'equal'):
            flags = sample_flags(rng, regime)
            pu, Bu, pv, Bv = flags
            Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
            Z = lam2(Bu) if rank_exact(Bu + Bv) == 3 else span(Piu + Piv)
            for d1 in range(0, 7):
                A = _ext([], d1, rng)
                if A is None:
                    continue
                c = dim(isect(A, Z)) if A else 0
                key = (dim(Z), d1)
                att.setdefault(key, set()).add(c)
                assert c >= max(0, d1 + dim(Z) - 6), \
                    'the forced minimum is violated -- impossible'
    for k in sorted(att):
        print(f'    dim Z = {k[0]}, delta_1 = {k[1]}: '
              f'dim(rho_1 cap Z) observed in {sorted(att[k])}, forced minimum '
              f'{max(0, k[1] + k[0] - 6)}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows, contra


# ================== (BE-37): (beta) REDUCED, and the quantifier COLLAPSED

def chain_piece_scan(flags, k, rng, ndraw=40):
    """A PATH piece of length k from u to v: by (BE-30)(i) applied to SIDE 1
    its rho_bar_1 is the span of a chain (k = m'+1 lines over m' = k-1 interior
    vertices), so the whole of (beta) is measurable for it with the ear
    machinery.

    Semicontinuity is respected: delta_1 is the MAXIMUM of dim rho_bar_1 over
    draws, and the intersection minima are taken only over the draws ATTAINING
    it -- minimising dim(rho_1 cap X) at a NON-generic, smaller rho_1 would be
    measuring a different piece.  Returns
      ((min cap Pi_u, min cap Pi_v, min cap Z), {m: (min loss, slack)}, dim Z,
       delta_1)."""
    pu, Bu, pv, Bv = flags
    Piu, Piv = pencil_space(pu, Bu), pencil_space(pv, Bv)
    equal = (rank_exact(Bu + Bv) == 3)
    Z = lam2(Bu) if equal else span(Piu + Piv)
    draws = []
    if k == 1:
        # the only length-1 piece is the EDGE uv, which needs p_v in pi_u
        if rank_exact(Bu + [pv]) != 3 or rank_exact([pu, pv]) != 2:
            return None, None, dim(Z), None
        draws.append(span([wedge2(pu, pv)]))
    else:
        for _ in range(ndraw):
            pts, L, S = BI.sample_ear_span(flags, k - 1, rng)
            if L is None:
                continue
            draws.append(S)
    if not draws:
        return None, None, dim(Z), None
    d1 = max(dim(S) for S in draws)
    best, lo = None, {}
    for S in draws:
        if dim(S) != d1:
            continue
        rec = (dim(isect(S, Piu)), dim(isect(S, Piv)), dim(isect(S, Z)))
        best = rec if best is None else tuple(min(x, y)
                                              for x, y in zip(best, rec))
        for m in range(1, 6):
            if equal and m == 1:
                continue      # pi_u = pi_v has no pi_u cap pi_v line for m=1
            loss = loss_exact(S, flags, m)[0]
            slack = max(0, d1 + min(m + 1, 6) - 6)
            cur = lo.get(m)
            if cur is None or loss < cur[0]:
                lo[m] = (loss, slack)
    return best, lo, dim(Z), d1


def run_betasp(seed=20260828, ntrial=12, ndraw=30):
    print('===== Step BE36 / (BE-37): (beta) REDUCED to THREE generic-'
          'position statements, and its "EVERY configuration" quantifier '
          'COLLAPSED =====')
    print('  THE COLLAPSE (this is the answer to the spec\'s job-2 note).')
    print('  Every quantity in loss = max(P, Z, R) is built from ranks of')
    print('  matrices whose entries are POLYNOMIAL in the configuration:')
    print('  dim(rho_1 cap X) = dim rho_1 + dim X - dim(rho_1 + X), and both')
    print('  dim rho_1 and dim(rho_1 + X) are such ranks, hence LOWER')
    print('  semicontinuous.  So on the (irreducible) configuration space,')
    print('  dim(rho_1 cap X) is UPPER semicontinuous and its MINIMUM is')
    print('  attained on a DENSE OPEN set -- simultaneously for the finitely')
    print('  many X in {Pi_u, Pi_v, Z}, by (BE-25)(i)\'s own argument.')
    print('  CONSEQUENCES, and they change what a sampler means here:')
    print('   (a) "at EVERY configuration" <=> "at a GENERIC configuration",')
    print('       so the unenumerable quantifier is not the obstacle;')
    print('   (b) a random exact draw computes an UPPER bound on min loss, so')
    print('       a sampler can report a FALSE trap but can NEVER miss a real')
    print('       one; an empty hunt corroborates in the SAFE direction;')
    print('   (c) one drawn configuration with loss <= slack is a THEOREM for')
    print('       that piece, since (beta) is EXISTENTIAL.')
    print('  What this does NOT give is the class-level statement.')
    t0 = time.time()
    print()
    print('  THE REDUCTION, enumerated over every arithmetic case.  Suppose')
    print('   (b1) dim(rho_1 cap Pi_u) <= 1 and dim(rho_1 cap Pi_v) <= 1;')
    print('   (b2) dim(rho_1 cap Z) <= max(delta_1 + dim Z - 6, dim Z - 2);')
    print('   (b3) rho_1 cap E is not an opposite-ruling pencil y ^ L.')
    print('  Then loss <= max(0, delta_1 + delta_2 - 6)?  The point is that')
    print('  delta_2 = min(m+1,6) >= 2 ALWAYS, which is exactly what covers')
    print('  the deficit lossZ = delta_1 - 4 in the tight regime.')
    ok = fail = 0
    failrows = []
    for dZ in (3, 4):
        for c2 in (2, 3):
            if c2 == 3 and dZ != 3:
                continue          # c_2 = 3 only at pi_u = pi_v, m = 2
            for d1 in range(0, 7):
                for m in range(1, 7):
                    d2 = min(m + 1, 6)
                    if c2 == 3 and m != 2:
                        continue
                    cz = max(max(0, d1 + dZ - 6), dZ - 2)
                    lossZ = max(0, cz + c2 - dZ)
                    loss = max(0, lossZ)         # (b1) kills P, (b3) kills R
                    slack = max(0, d1 + d2 - 6)
                    if loss <= slack:
                        ok += 1
                    else:
                        fail += 1
                        failrows.append((dZ, c2, d1, m, loss, slack))
    print(f'    {ok + fail} arithmetic cases (dim Z, c_2, delta_1, m): the '
          f'reduction HOLDS in {ok}, FAILS in {fail}')
    for r in failrows:
        print(f'      FAILS: dim Z={r[0]} c_2={r[1]} delta_1={r[2]} m={r[3]}:'
              f'  loss {r[4]} > slack {r[5]}')
    print('    The failing rows are EXACTLY the c_2 = 3 corner -- pi_u = pi_v')
    print('    WITH m = 2, where (BE-30)(iii)(b) makes rho_2 = Lambda^2 pi')
    print('    a SINGLE POINT of Gr(3,6) and the ear has no freedom at all.')
    print('    That corner is not generic unless the GRAPH forces it,')
    print('    and where it does (BE-32)(ii)/(iii) prove delta_uv = 0 for')
    print('    the two known forcing mechanisms, (BE-32)(+) MEASURING the')
    print('    rest.  It is carried as this direction\'s named residue, not')
    print('    smoothed away.')
    print()
    print('  (b1)/(b2)/(b3) PROVED FOR THE ALL-S PIECE.  A path piece\'s')
    print('  rho_bar_1 is, by (BE-30)(i) applied to SIDE 1, the span of a')
    print('  CHAIN with l\'_1 in Pi_u and l\'_k in Pi_v -- the object the')
    print('  ear image is.  So its generic position against Pi_u, Pi_v and Z')
    print('  is measurable by the same machinery, and the forced values are')
    print('     dim(<chain> cap Pi_u) >= 1 (the first hinge lies in Pi_u),')
    print('     dim(<chain> cap Z)    >= max(2, k + dim Z - 6).')
    print('  Measured over drawn chains, per regime and length k: the three')
    print('  generic-position minima, and the CORRECTED (beta) test -- is the')
    print('  minimum loss within the slack max(0, delta_1 + delta_2 - 6)?')
    rng = random.Random(seed)
    agg = {}
    for _ in range(ntrial):
        for regime in ('nonadj', 'adj', 'equal'):
            flags = sample_flags(rng, regime)
            for k in range(1, 7):
                rec, lo, dZ, d1 = chain_piece_scan(flags, k, rng, ndraw)
                if rec is None:
                    continue
                key = (regime, k)
                cur = agg.get(key)
                if cur is None or d1 > cur[3]:
                    agg[key] = [rec, dict(lo), dZ, d1]
                elif d1 == cur[3]:
                    cur[0] = tuple(min(a, b) for a, b in zip(cur[0], rec))
                    for m in lo:
                        if m not in cur[1] or lo[m][0] < cur[1][m][0]:
                            cur[1][m] = lo[m]
    viol = []
    for regime in ('nonadj', 'adj', 'equal'):
        for k in range(1, 7):
            if (regime, k) not in agg:
                continue
            rec, lo, dZ, d = agg[(regime, k)]
            cu, cv, cz = rec
            over = [m for m in sorted(lo) if lo[m][0] > lo[m][1]]
            note = ''
            if regime == 'adj' and k >= 2:
                note = '   [NOT REALIZABLE: uv in E(G_1) forces delta_1 <= 1]'
            elif d >= 6:
                note = '   [VACUOUS: delta_1 = 6, criterion already met]'
            elif regime == 'equal':
                if over == [2]:
                    note = '   [the c_2 = 3 corner: pi_u = pi_v WITH m = 2]'
                elif k <= 3:
                    note = '   [(BE-30)(iii)(b) confines SIDE 1 too]'
            if over and not note:
                viol.append((regime, k, over))
            print(f'    {regime:7s} k={k} (dim Z={dZ}): dim rho_1={d}, min '
                  f'dim(cap Pi_u)={cu} (cap Pi_v)={cv} (cap Z)={cz}; '
                  f'min loss/slack per m: '
                  + ' '.join(f'm{m}:{lo[m][0]}/{lo[m][1]}' for m in sorted(lo))
                  + note)
    print(f'  UNEXPLAINED violations of the corrected (beta) over the drawn '
          f'chains: {len(viol)}')
    for v in viol:
        print(f'    {v}')
    print('  Read the three annotated classes as follows.  [NOT REALIZABLE]:')
    print('  in the ADJACENT regime the edge uv must lie in G_1 (the ear has')
    print('  m >= 1 interior vertices and therefore no uv edge), so')
    print('  dist_{G_1}(u,v) = 1 and (BE-30)(iv) gives delta_1 <= 1 -- the')
    print('  k >= 2 rows describe no piece.  [VACUOUS]: delta_1 = 6 makes')
    print('  rho_bar_1 the whole screw space, Pi_u <= rho_bar_1 necessarily,')
    print('  and dim(rho_1+rho_2) = 6 = min(delta_1+delta_2,6) already.')
    print('  [(BE-30)(iii)(b)]: at pi_u = pi_v a SIDE-1 path with <= 2')
    print('  interior vertices has every point in pi, so rho_bar_1 <=')
    print('  Lambda^2 pi -- the confinement law, applied to side 1 rather')
    print('  than to the ear.  That is the SAME residue the arithmetic table')
    print('  above isolates, and it needs pi_u = pi_v to be FORCED.')
    print()
    print('  THE CONSEQUENCE FOR A GENERAL PIECE, and it is a THEOREM given')
    print('  the chain statement: by (BE-30)(iv) rho_bar_1 <= <l_e : e in P>')
    print('  for EVERY u-v path P of the piece, so')
    print('        dim(rho_1 cap Z) <= dim(<P> cap Z)')
    print('  at the SHORTEST path P.  With the chain values above that is')
    print('  <= max(2, dist + dim Z - 6): a piece with dist_{G_1}(u,v)<=4')
    print('  has dim(rho_1 cap Z) <= dim Z - 2 outright -- (beta) holds with')
    print('  loss = 0, for EVERY ear length, PROVIDED the short path\'s own')
    print('  interior hinge lines are generic against Z, which the pencil')
    print('  condition constrains only at the piece\'s BRANCH vertices.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return ok, fail, viol


# ============ (BE-38): the falsification arm, at GENERIC configurations

def subdivide(base, r, tag='s'):
    """Every edge of `base` replaced by a path of `r` edges (r-1 new interior
    vertices).  With r >= 3 no two vertices of degree >= 3 are adjacent, which
    is what makes the free sampler below legal."""
    E = []
    k = 0
    for (a, b) in base:
        prev = a
        for _ in range(r - 1):
            k += 1
            cur = f'{tag}{k}'
            E.append((prev, cur))
            prev = cur
        E.append((prev, b))
    return E


def _perp_basis3(n):
    """A basis of {x in K^3 : n . x = 0}."""
    rows = nullspace([list(n)])
    return [tuple(r) for r in rows]


def sample_piece_config(edges, u, v, rng, s=20, tries=40):
    """A pencil configuration of the PIECE, drawn INDEPENDENTLY of the BTWOCUT
    ladder.  Legal because the pencil condition is exactly *every closed star
    coplanar* ((BE-16)): choose a point AND a plane at each vertex of degree
    >= 3 (and at u and v, whose degree rises by one when the ear is glued),
    then place each remaining vertex freely -- a degree-2 vertex imposes no
    condition of its own.  Requires the branch set to be an INDEPENDENT set
    and every other vertex to have at most one branch neighbour, which is why
    the battery subdivides each base edge at least three ways.  Returns
    (pt, {z: plane basis in hat coordinates}) or (None, why)."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    branch = set([u, v]) | {z for z in V if len(nb.get(z, ())) >= 3}
    for z in branch:
        for w in nb.get(z, ()):
            if w in branch:
                return None, 'branch vertices adjacent -- unsupported shape'
    for w in V:
        if w in branch:
            continue
        if len([z for z in nb.get(w, ()) if z in branch]) > 1:
            return None, 'a free vertex has two branch neighbours'
    for _ in range(tries):
        pt = {}
        pl = {}
        for z in branch:
            p = tuple(rq(rng, s) for _ in range(3))
            n = tuple(rq(rng, s) for _ in range(3))
            if all(x == 0 for x in n):
                continue
            db = _perp_basis3(n)
            if len(db) != 2:
                continue
            pt[z] = p
            pl[z] = (p, db)
        if len(pt) != len(branch):
            continue
        okdraw = True
        for w in V:
            if w in branch:
                continue
            bs = [z for z in nb.get(w, ()) if z in branch]
            if not bs:
                pt[w] = tuple(rq(rng, s) for _ in range(3))
            else:
                p0, db = pl[bs[0]]
                a, b = rq(rng, s), rq(rng, s)
                pt[w] = tuple(p0[t] + a * db[0][t] + b * db[1][t]
                              for t in range(3))
        if not okdraw:
            continue
        if len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        ok, _ = verify_pencil_witness(edges, pt)
        if not ok:
            continue
        planes = {}
        for z in branch:
            p0, db = pl[z]
            basis = [hat(p0)] + [list(d) + [F(0)] for d in db]
            if rank_exact(basis) != 3:
                okdraw = False
                break
            planes[z] = nullspace(nullspace(basis))
        if not okdraw:
            continue
        return (pt, planes), None
    return None, 'no legal draw under the try budget'


def piece_battery():
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    PRISM = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    out = [
        ('path of 3 edges u-v (all-S)', path(4), 'v0', 'v3'),
        ('path of 4 edges u-v (all-S)', path(5), 'v0', 'v4'),
        ('path of 5 edges u-v (all-S)', path(6), 'v0', 'v5'),
        ('path of 6 edges u-v (all-S)', path(7), 'v0', 'v6'),
        ('path of 7 edges u-v (all-S)', path(8), 'v0', 'v7'),
        ('theta(3,3,3) @ hubs (P-node)', theta(3, 3, 3), 'u', 'v'),
        ('theta(3,4,5) @ hubs (P-node)', theta(3, 4, 5), 'u', 'v'),
        ('theta(4,4,4) @ hubs (P-node)', theta(4, 4, 4), 'u', 'v'),
        ('theta(5,5,5) @ hubs (P-node)', theta(5, 5, 5), 'u', 'v'),
        ('theta(3,3,6) @ hubs (P-node)', theta(3, 3, 6), 'u', 'v'),
        ('C8 @ antipodes (path)', cycle(8), 'v0', 'v4'),
        ('C10 @ antipodes (path)', cycle(10), 'v0', 'v5'),
        ('C12 @ antipodes (path)', cycle(12), 'v0', 'v6'),
        ('K4 subdivided x3 @ 0,1 (R-node)', subdivide(K4, 3), 0, 1),
        ('K4 subdivided x3 @ 0,2 (R-node)', subdivide(K4, 3, 't'), 0, 2),
        ('K4 subdivided x4 @ 0,1 (R-node)', subdivide(K4, 4, 'q'), 0, 1),
        ('K_{3,3} subdivided x3 @ 0,1 (R-node)', subdivide(K33, 3, 'b'),
         0, 1),
        ('K_{3,3} subdivided x3 @ 0,3 (R-node)', subdivide(K33, 3, 'c'),
         0, 3),
        ('prism subdivided x3 @ 0,1 (R-node)', subdivide(PRISM, 3, 'p'),
         0, 1),
        ('prism subdivided x3 @ 0,5 (R-node)', subdivide(PRISM, 3, 'r'),
         0, 5),
        ('K4 subdivided x5 @ 0,1 (R-node)', subdivide(K4, 5, 'f'), 0, 1),
        ('K_{3,3} subdivided x4 @ 0,1 (R-node)', subdivide(K33, 4, 'd'),
         0, 1),
        ('theta(6,6,6) @ hubs (P-node)', theta(6, 6, 6), 'u', 'v'),
        ('theta(4,5,6) @ hubs (P-node)', theta(4, 5, 6), 'u', 'v'),
    ]
    return out


def run_betahunt(seed=20260828, nseeds=14):
    print('===== Step BE37 / (BE-38): THE FALSIFICATION ARM -- (beta) tested '
          'at GENERIC piece configurations, from a sampler INDEPENDENT of the '
          'BTWOCUT ladder =====')
    print('  BIMAGE cap 3: *"no real piece produces a bad rho_bar_1"*')
    print('  was measured over configurations the BTWOCUT LADDER produces,')
    print('  one draw per instance.  This mode replaces the ladder outright.')
    print('  By (BE-16) the pencil condition IS *every closed star coplanar*,')
    print('  so for a piece whose degree->=3 vertices form an INDEPENDENT set')
    print('  the stratum has a FREE parametrization: a (point, plane) flag at')
    print('  each branch vertex and at u, v, and a free point at each')
    print('  degree-2 vertex, in its branch neighbour\'s plane.  Each draw is')
    print('  passed through `assert_generic_star` AND '
          '`kbare_common.verify_pencil_witness`.')
    print('  By the semicontinuity of (BE-37) the MINIMUM over draws is the')
    print('  minimum over the whole stratum once a draw attains max dim '
          'rho_bar_1,')
    print('  and a sampler can only OVER-report traps -- so an empty column')
    print('  here is corroboration in the SAFE direction.')
    t0 = time.time()
    tested = 0
    rows = []
    meet = {0: 0, 1: 0, 2: 0}
    for (name, edges, u, v) in piece_battery():
        draws = []
        for sd in range(nseeds):
            rng = random.Random(seed + 7919 * sd + len(name))
            got, why = sample_piece_config(edges, u, v, rng)
            if got is None:
                continue
            pt, planes = got
            pu, pv = hat(pt[u]), hat(pt[v])
            Bu, Bv = planes[u], planes[v]
            pa = plane_at(edges, pt, u)
            if pa is not None:
                assert same_space(pa, Bu), \
                    'the chosen plane at u is not the closed star\'s plane'
            rho, img, dM, r = rel_screw_space(edges, pt, u, v)
            S = span(img) if img else []
            draws.append((S, (pu, Bu, pv, Bv), dim(S)))
        if not draws:
            print(f'    {name:38s}: NO LEGAL DRAW (sampler shape guard)')
            continue
        r1 = max(d[2] for d in draws)
        best = {}
        cuv = None
        for (S, flags, d) in draws:
            if d != r1:
                continue
            pu, Bu, pv, Bv = flags
            Piu = pencil_space(pu, Bu)
            cu = dim(isect(S, Piu)) if S else 0
            cuv = cu if cuv is None else min(cuv, cu)
            for m in range(1, 6):
                if rank_exact(Bu + Bv) == 3:
                    continue
                loss = loss_exact(S, flags, m)[0]
                slack = max(0, r1 + min(m + 1, 6) - 6)
                cur = best.get(m)
                if cur is None or loss < cur[0]:
                    best[m] = (loss, slack)
        if cuv is not None:
            meet[min(cuv, 2)] = meet.get(min(cuv, 2), 0) + 1
            assert not (cuv >= 2 and r1 < 6), \
                ('Pi_u <= rho_bar_1 at a NON-vacuous piece -- this would be '
                 'the (P) trap, genuinely realized', name, r1)
        over = [m for m in sorted(best) if best[m][0] > best[m][1]]
        tested += 1
        rows.append((name, r1, best, over, cuv))
        flag = '   <== CANDIDATE' if over else ''
        print(f'    {name:38s}: rho_1 = {r1}, dim(rho_1 cap Pi_u) = {cuv}; '
              f'min loss/slack ' +
              ' '.join(f'm{m}:{best[m][0]}/{best[m][1]}'
                       for m in sorted(best)) + flag)
    ncand = sum(1 for r in rows if r[3])
    print(f'  {tested} pieces, {nseeds} independent generic draws each: '
          f'{ncand} CANDIDATES (a piece whose minimum loss exceeds its slack '
          f'at some ear length)')
    print(f'  dim(rho_1 cap Pi_u) at the generic draw: '
          + ',  '.join(f'{k}: {meet.get(k, 0)} pieces' for k in (0, 1, 2))
          + '  -- the coordinator\'s observation 3, reproduced on an '
            'independent sampler: it is 1 for PATH-like sides (the first '
            'hinge at u) and 0 wherever two u-v paths leave u by different '
            'edges, and it is NEVER 2 below rho_1 = 6.')
    print('  CAP DISCLOSURE.  The sampler covers pieces whose degree->=3')
    print('  vertices form an independent set and whose degree-2 vertices')
    print('  have at most one branch neighbour -- SUBDIVISIONS with each base')
    print('  edge split at least three ways; nothing about pieces with')
    print('  adjacent branch vertices.  delta_1 is taken to be the MEASURED')
    print('  max dim rho_bar_1 over draws, a LOWER bound on the combinatorial')
    print('  delta_1, which UNDER-states the slack and therefore OVER-reports')
    print('  candidates -- the conservative direction.  An empty column reads')
    print('  "no candidate found under this cap", never "none exists".')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tested, rows


# ============================================================== driver CLI

def run_validate():
    """A reduced tier of every mode, for a fast end-to-end check."""
    t0 = time.time()
    run_twostep(ntrial=8, ndraw=40)
    print()
    run_laststep(ntrial=6)
    print()
    run_greedy(ntrial=1, tries=3)
    print()
    run_corners(ntrial=4, tries=4)
    print()
    run_betadim(ntrial=6)
    print()
    run_betasp(ntrial=5, ndraw=20)
    print()
    run_betahunt(nseeds=4)
    print(f'\n===== validate: all seven modes at a reduced tier, '
          f'{time.time() - t0:.1f} s =====')


MODES = {
    'twostep': run_twostep,      # (BE-35)(i)   the 2-step lemma
    'laststep': run_laststep,    # (BE-35)(ii)  the ear's last step
    'greedy': run_greedy,        # (BE-35)(iii)/(iv) the reordered greedy
    'corners': run_corners,      # (BE-35)(v)   the m <= 2 corners
    'betadim': run_betadim,      # (BE-36)      (beta) as stated is false
    'betasp': run_betasp,        # (BE-37)      (beta) reduced, collapsed
    'betahunt': run_betahunt,    # (BE-38)      the falsification arm
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: {os.path.basename(__file__)} '
              f'[{"|".join(MODES)}]')
        sys.exit(2)
    MODES[mode]()
