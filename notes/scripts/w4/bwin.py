"""
Direction BWIN (ordinal 51) -- BSHARP's window identity as a CLASS statement.

  TARGET  (BE-47)(iii) for EVERY window piece -- (M1) at both ends, (M2) at
          neither, delta_1 <= 4, dim Z = 4:  rho_bar_1 cap Z = <l_u, l_v>
          EXACTLY.  By (BE-47)(iii), proved as an equivalence, that IS (b2)
          in the window; the identity also gives (b1) there, and (BE-50)(iii)
          gives (b3), so closing it gives (BE-37)(ii) all three clauses and
          proves the ear case's (beta) side on the reduction's 87-of-91
          domain.

  THE CRUX (spec)  The arc's one-witness machinery ((BE-46)(i)/(ii) +
          (BE-52)) CANNOT deliver a class statement -- (BE-46)(iv) says so in
          its own words -- so a sixth exhibited witness is NOT a HIT.  The
          deliverable is a UNIFORM argument, and this driver VERIFIES one:
          the workbook's *Steps BE53-BE57* prove the identity for every
          both-ends-series piece with delta_1 <= 4 by a RANK-ONE BUDGET
          argument, quantifying over the middle's screw space W as an
          ARBITRARY subspace -- no graph enumeration, which is how the F11
          exhaustiveness rider is met by an argument rather than a driver.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-54)  THE REFORMULATION.
             `dec`   : at every battery piece, as identities of SPACES:
                       the double series peel rho_bar_1 = <l_u> + W + <l_v>
                       (W = rho_bar of the MIDDLE, recomputed directly);
                       Z = mu^perpK cap lambda^perpK  (mu = Plucker of
                       M = p_u v p_v, lambda = Plucker of L = pi_u cap pi_v);
                       and the MODULAR-LAW factorization
                       rho_bar_1 cap Z = <l_u,l_v> + (W cap Z), so the target
                       is EQUIVALENT to  W cap Z <= <l_u,l_v>.  This is the
                       job-2 answer: the identity does NOT factor through the
                       middle alone, and the whole coupling is (lambda, mu).

  (BE-55)  THE END-CHOICE LEMMA and the RANK-ONE BUDGET.
             `sweep` : the functional phi = <., mu>_K kills exactly one
                       dimension and vanishes on <l_u,l_v> identically; a
                       fixed x survives EVERY admissible mu iff
                       x in (span l_u ^ l_v)^perpK, which for skew l_u, l_v
                       is <l_u,l_v> itself (asserted per draw), and in the
                       meeting-lines regime is Lambda^2 sigma with
                       V cap Lambda^2 sigma <= q ^ sigma = <l_u,l_v>
                       (synthetic trials).  Consequence, asserted at control
                       shapes: excess >= 2  =>  the identity fails at EVERY
                       end choice over that L (the per-L criterion).

  (BE-56)  THE EXCESS LAW -- why delta_1 <= 4 is exactly enough.
             `exc`   : with V := W cap lambda^perpK and
                       excess := dim V - dim(V cap <l_u,l_v>):
                       dim(W cap <l_u,l_v>) = t + 2 - delta_1 and
                       dim V <= t - 1 at generic L, hence
                       excess <= max(0, delta_1 - 3) -- asserted per draw.
                       delta_1 <= 4 gives excess <= 1: ONE functional's
                       budget.  identity <=> excess <= 1, asserted.

  (BE-57)  THE THEOREM, END TO END.
             `cls`   : for every window piece, the construction of the
                       workbook's proof run literally: fix the middle from a
                       guarded draw, REDRAW the ends (L, p_u, p_v) fresh,
                       verify legality through BOTH gates, and assert
                       rho_bar_1 cap Z = <l_u,l_v>, (b1), dim Z = 4 and
                       cross-incidence-freeness at every draw.

  (BE-58)  JOB 3 -- the window is NOT exactly the barbells.
             `wide`  : five NON-barbell window pieces (theta chains, a
                       four-branch theta, K4-subdivision middles -- an
                       R-NODE middle among them), each verified IN the
                       window (series both ends, delta_1 <= 4 < d_min,
                       dim Z = 4, dist >= 5), with the trichotomy data
                       (t, T_i <= W?, dim(W cap <l_u,l_v>)) reported.

Succeeds `notes/scripts/w4/brule.py` (Steps BE48-BE52); imports `bsharp` /
`brule` / `bimage` READ-ONLY, and through them `bearfull` / `bearcase` /
`btwocut` / `binduc` / `bzavoid` / `kbare_common` -- the `kbare/`
sibling-import chain gains its TENTH consumer and is TEN deep (recorded,
NO MOVE MADE).  Landed figures are CITED, never re-run.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, `contains`) and never of dimensions, every
sampled configuration through binduc's `assert_generic_star` AND
`kbare_common.verify_pencil_witness`, every cap disclosed.

DISCLOSED DRIVER CAP (the theorem does not share it): every battery piece has
deg(u) = deg(v) = 1, so the A-sides of the series peel are the terminals
themselves; the workbook's Step BE56 handles a general A-side by a PGL(4)
move, which a numeric driver does not need to instantiate.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import random
import sys
import time
from fractions import Fraction as F

import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import (rank as rank_exact, nullspace, hat, wedge2,   # noqa: E402
                       neighbors)
from kbare_common import verify_pencil_witness                       # noqa: E402
from binduc import assert_generic_star, path, theta                  # noqa: E402
from bimage import (contains, dim, isect, klein, klein_perp, lam2,   # noqa: E402
                    pencil_space, rho_bar_of, same_space, span)
from bearcase import subdivide                                       # noqa: E402
from bsharp import (K4, K33, _relabel, barbell, guarded_draw,        # noqa: E402
                    lines_of_path, sample_piece_config_adj,
                    simple_paths, usable_first_edges)

SEED = 20260829

# ===================================================== small exact helpers

def rq(rng, s=20):
    return F(rng.randint(-s, s))


def v4(rng, s=20):
    return [rq(rng, s) for _ in range(4)]


def k4_span(rows):
    """Canonical basis of a subspace of K^4."""
    return nullspace(nullspace(rows)) if rows else []


def k4_isect(A, B):
    """Intersection of two subspaces of K^4 (bases in, basis out)."""
    M = nullspace(A) + nullspace(B)
    return nullspace(M) if M else k4_span(A)


def dehom(x):
    """Q^4 point with x[3] != 0  ->  the affine Q^3 point `hat` recovers."""
    assert x[3] != 0, 'point at infinity cannot be dehomogenized'
    return [x[0] / x[3], x[1] / x[3], x[2] / x[3]]


def pt_on_line(t, rng, avoid, s=20):
    """An affine point of the K^4-line `t` (basis of 2), independent of
    `avoid`."""
    for _ in range(200):
        a, b = rq(rng, s), rq(rng, s)
        x = [a * t[0][k] + b * t[1][k] for k in range(4)]
        if x[3] == 0:
            continue
        if rank_exact([x, avoid]) == 2:
            return x
    raise RuntimeError('pt_on_line: no draw')


# ===================================================== the series peel

def series_data(edges, u, v):
    """(w1, w2, middle edges).  Requires deg(u) = deg(v) = 1 (the driver cap
    disclosed in the module docstring) and u, v series ends."""
    nb = neighbors(edges)
    assert len(nb[u]) == 1 and len(nb[v]) == 1, \
        'driver cap: battery pieces have pendant terminals'
    feu = usable_first_edges(edges, u, v)
    fev = usable_first_edges(edges, v, u)
    assert len(feu) == 1 and len(fev) == 1, 'not series at both ends'
    w1, w2 = feu[0], fev[0]
    C = [e for e in edges if u not in e and v not in e]
    return w1, w2, C


def d_min_of(edges, pt, u, v, cap=4000):
    """min over u-v paths of dim<l_e : e in P> at this configuration."""
    paths, hit = simple_paths(edges, u, v, cap=cap)
    assert not hit, 'path cap hit (disclose)'
    return min(dim(span(lines_of_path(pt, P))) for P in paths)


def full_measure(edges, pt, planes, u, v):
    """Everything *Steps BE53-BE56* assert at one configuration.  Every
    subspace claim an identity of SPACES; a failure raises."""
    w1, w2, C = series_data(edges, u, v)
    S, d1, _, _ = rho_bar_of(edges, pt, u, v)
    Wm, t, _, _ = rho_bar_of(C, pt, w1, w2)
    lu = wedge2(hat(pt[u]), hat(pt[w1]))
    lv = wedge2(hat(pt[v]), hat(pt[w2]))
    Luv = span([lu, lv])
    assert dim(Luv) == 2, 'l_u, l_v not independent'
    # --- (BE-54)(i): the double series peel, as an identity of spaces
    assert same_space(S, span([lu, lv] + Wm)), \
        '(BE-54)(i): rho_bar_1 != <l_u> + W + <l_v>'
    # --- flags and Z
    Piu = pencil_space(hat(pt[u]), planes[u])
    Piv = pencil_space(hat(pt[v]), planes[v])
    Z = span(Piu + Piv)
    Lb = k4_isect(planes[u], planes[v])
    assert len(Lb) == 2, 'L = pi_u cap pi_v is not a line'
    lam = wedge2(Lb[0], Lb[1])
    mu = wedge2(hat(pt[u]), hat(pt[v]))
    # --- (BE-54)(ii): Z = mu^perpK cap lambda^perpK
    assert same_space(Z, isect(klein_perp([mu]), klein_perp([lam]))), \
        '(BE-54)(ii): Z != mu^perp cap lambda^perp'
    # --- (BE-54)(iii): the modular-law factorization
    WZ = isect(Wm, Z) if Wm else []
    assert same_space(isect(S, Z), span(Luv + WZ)), \
        '(BE-54)(iii): the modular law fails'
    # --- (BE-55)(i): phi = <., mu>_K vanishes on <l_u,l_v>; Luv <= Z
    assert klein(lu, mu) == 0 and klein(lv, mu) == 0, \
        '(BE-55)(i): phi does not vanish on the leading lines'
    assert klein(lu, lam) == 0 and klein(lv, lam) == 0, \
        '(BE-55)(i): a leading line does not meet L'
    assert contains(Z, Luv), '(BE-55)(i): <l_u,l_v> not inside Z'
    # --- (BE-56): the excess law
    V = isect(Wm, klein_perp([lam])) if Wm else []
    exc = dim(V) - dim(isect(V, Luv))
    assert dim(span(Wm + Luv)) == d1, 'delta_1 != dim(W + <l_u,l_v>)'
    assert dim(isect(Wm, Luv)) == t + 2 - d1 if Wm else d1 == 2, \
        '(BE-56)(i): dim(W cap <l_u,l_v>) != t + 2 - delta_1'
    assert dim(V) <= max(0, t - 1), '(BE-56)(ii): dim V > t - 1 (lambda not generic)'
    assert exc <= max(0, d1 - 3), '(BE-56)(iii): excess > max(0, delta_1 - 3)'
    # --- W cap Z = V cap mu^perp (the kernel of the budget functional)
    if Wm:
        assert same_space(WZ, isect(V, klein_perp([mu])) if V else []), \
            'W cap Z != ker(phi | V)'
    ident = same_space(isect(S, Z), Luv)
    b1 = same_space(isect(S, Piu), span([lu])) if ident else None
    if ident:
        assert b1, '(b1) does not follow from the identity'
    return dict(d1=d1, t=t, exc=exc, ident=ident, dz=dim(Z),
                szi=dim(isect(S, Z)), wluv=dim(isect(Wm, Luv)) if Wm else 0,
                S=S, Wm=Wm, Luv=Luv, Z=Z, lu=lu, lv=lv, w1=w1, w2=w2)


# ===================================================== the batteries

def theta_chain(k1, t1abc, s, t2abc, k2):
    """u -(k1 edges)- theta(t1abc) -(s-edge bridge)- theta(t2abc) -(k2)- v:
    TWO parallel blocks in series -- a piece that is NOT a barbell."""
    E = []
    prev = 'u'
    for i in range(k1 - 1):
        E.append((prev, f'q{i}')); prev = f'q{i}'
    E.append((prev, 'A'))
    E += _relabel(theta(*t1abc),
                  {'u': 'A', 'v': 'B'} | {f'x{i}': f's{i}' for i in range(30)})
    prev = 'B'
    for i in range(s - 1):
        E.append((prev, f'm{i}')); prev = f'm{i}'
    E.append((prev, 'C'))
    E += _relabel(theta(*t2abc),
                  {'u': 'C', 'v': 'D'} | {f'x{i}': f't{i}' for i in range(30)})
    prev = 'D'
    for i in range(k2 - 1):
        E.append((prev, f'r{i}')); prev = f'r{i}'
    E.append((prev, 'v'))
    return E


def theta4(a, b, c, d):
    """FOUR internally-disjoint paths between two hubs HU, HV."""
    E = []
    for tag, n in (('a', a), ('b', b), ('c', c), ('d', d)):
        prev = 'HU'
        for i in range(n - 1):
            E.append((prev, f'{tag}{i}')); prev = f'{tag}{i}'
        E.append((prev, 'HV'))
    return E


def pendant_wrap(core, cu, cv, k1=1, k2=1):
    """u -(k1 edges)- core[cu] ... core[cv] -(k2 edges)- v."""
    E = list(core)
    prev = 'u'
    for i in range(k1 - 1):
        E.append((prev, f'q{i}')); prev = f'q{i}'
    E.append((prev, cu))
    prev = cv
    for i in range(k2 - 1):
        E.append((prev, f'r{i}')); prev = f'r{i}'
    E.append((prev, 'v'))
    return E


def window_battery():
    """BSHARP's five window barbells ((BE-47)(iii)) PLUS five shapes that are
    NOT barbells -- job 3's answer lives in the second half."""
    k4s = subdivide(K4(), 3)
    return [
        # -- the five landed barbells, re-carried (cited shapes, fresh draws)
        ('barbell 1+th(3,3,3)+1', barbell(1, 3, 3, 3, 1), 'u', 'v', True),
        ('barbell 1+th(3,3,4)+1', barbell(1, 3, 3, 4, 1), 'u', 'v', True),
        ('barbell 1+th(4,4,4)+1', barbell(1, 4, 4, 4, 1), 'u', 'v', True),
        ('barbell 2+th(3,3,3)+2', barbell(2, 3, 3, 3, 2), 'u', 'v', True),
        ('barbell 1+th(3,3,3)+2', barbell(1, 3, 3, 3, 2), 'u', 'v', True),
        # -- NOT barbells: two parallel blocks in series
        ('theta-chain 1/(3,3,3)/1/(3,3,3)/1',
         theta_chain(1, (3, 3, 3), 1, (3, 3, 3), 1), 'u', 'v', False),
        ('theta-chain 1/(3,3,3)/2/(3,3,4)/1',
         theta_chain(1, (3, 3, 3), 2, (3, 3, 4), 1), 'u', 'v', False),
        # -- NOT a barbell: a four-branch parallel block
        ('theta4(3,3,3,3) wrapped 1,1',
         pendant_wrap(theta4(3, 3, 3, 3), 'HU', 'HV', 1, 1), 'u', 'v', False),
        # -- NOT barbells: an R-NODE middle (K4 subdivision)
        ('K4x3 wrapped 1,1 [R-node middle]',
         pendant_wrap(k4s, 0, 1, 1, 1), 'u', 'v', False),
        ('K4x3 wrapped 2,1 [R-node middle]',
         pendant_wrap(k4s, 0, 1, 2, 1), 'u', 'v', False),
    ]


def control_battery():
    """Shapes the theorem also covers (path4: series both ends, delta_1 = 4,
    (M2) FIRES -- the window excludes it but the theorem does not) and shapes
    it must REFUSE (delta_1 >= 5: excess >= 2, the per-L criterion) -- an
    R-NODE middle among the refusals: K33x3 between adjacent base vertices
    peels to delta_1 = 5, so the refusal is not a path artifact."""
    k33s = subdivide(K33(), 3, 'y')
    return [
        ('K33x3 wrapped 1,1 [delta=5: MUST FAIL]',
         pendant_wrap(k33s, 0, 3, 1, 1), 'u', 'v', False),
        ('path of 4 edges [M2, delta=4: THEOREM APPLIES]',
         path(5), 'v0', 'v4', True),
        ('path of 5 edges [delta=5: MUST FAIL]',
         path(6), 'v0', 'v5', False),
        ('barbell 3+th(3,3,3)+3 [delta=6: MUST FAIL]',
         barbell(3, 3, 3, 3, 3), 'u', 'v', False),
    ]


# ============================== the END RESWEEP (the theorem's construction)

def boundary_plane(edges, pt, w, exclude, rng):
    """The plane the middle FORCES at its boundary vertex `w` (the terminal
    `exclude` removed): forced when the middle star spans a plane, else a
    generic legal completion (a degree-2 boundary imposes nothing).  Returns
    (basis, forced)."""
    nb = neighbors(edges)
    star = [hat(pt[w])] + [hat(pt[x]) for x in nb[w] if x != exclude]
    r = rank_exact(star)
    assert r in (2, 3), 'degenerate boundary star'
    if r == 3:
        return k4_span(star), True
    for _ in range(60):
        x = v4(rng)
        if rank_exact(star + [x]) == 3:
            return k4_span(star + [x]), False
    raise RuntimeError('boundary_plane: no completion')


def resweep(edges, u, v, pt0, rng):
    """ONE fresh end draw over a FIXED middle: draw L, set pi_u = L v p1 and
    pi_v = L v p2, take p_u on t1 = pi_u cap pi_1 and p_v on t2 = pi_v cap
    pi_2, re-glue, and pass the glued configuration through BOTH gates.
    Returns (pt, planes, aux) or None (a rejected non-generic draw)."""
    w1, w2, C = series_data(edges, u, v)
    p1, p2 = hat(pt0[w1]), hat(pt0[w2])
    pi1, _f1 = boundary_plane(edges, pt0, w1, u, rng)
    pi2, _f2 = boundary_plane(edges, pt0, w2, v, rng)
    l1, l2 = v4(rng), v4(rng)
    if rank_exact([l1, l2]) != 2:
        return None
    Lb = [l1, l2]
    # genericity of L: p1, p2 off L; L, p1, p2 not coplanar; L not in pi_i
    if rank_exact(Lb + [p1]) != 3 or rank_exact(Lb + [p2]) != 3:
        return None
    if rank_exact(Lb + [p1, p2]) != 4:
        return None
    piu = k4_span(Lb + [p1])
    piv = k4_span(Lb + [p2])
    t1 = k4_isect(piu, pi1)
    t2 = k4_isect(piv, pi2)
    if len(t1) != 2 or len(t2) != 2:
        return None
    skew = rank_exact(t1 + t2) == 4
    try:
        pu = pt_on_line(t1, rng, p1)
        pv = pt_on_line(t2, rng, p2)
    except RuntimeError:
        return None
    # honest domain: cross-incidence-free, M skew to L
    if rank_exact(Lb + [pu]) != 3 or rank_exact(Lb + [pv]) != 3:
        return None
    if rank_exact([pu, pv] + Lb) != 4:
        return None
    pt = dict(pt0)
    pt[u] = dehom(pu)
    pt[v] = dehom(pv)
    ok, _why = verify_pencil_witness(edges, pt)
    if not ok:
        return None
    try:
        assert_generic_star(edges, pt)
    except AssertionError:
        return None
    planes = {u: piu, v: piv}
    return pt, planes, dict(t1=t1, t2=t2, skew=skew, Lb=Lb)


def end_choice_check(aux, pt, u, v, w1, w2):
    """(BE-55)(ii) at one resweep draw: for SKEW l_u, l_v, the span of
    {p ^ q : p in t1, q in t2} is 4-dimensional with Klein-perp EXACTLY
    <l_u, l_v> -- so x survives every admissible mu iff x is a combination
    of the two leading lines."""
    if not aux['skew']:
        return False
    t1, t2 = aux['t1'], aux['t2']
    T12 = span([wedge2(x, y) for x in t1 for y in t2])
    assert dim(T12) == 4, '(BE-55)(ii): t1 ^ t2 not 4-dimensional'
    lu = wedge2(hat(pt[u]), hat(pt[w1]))
    lv = wedge2(hat(pt[v]), hat(pt[w2]))
    assert same_space(klein_perp(T12), span([lu, lv])), \
        '(BE-55)(ii): (t1 ^ t2)^perpK != <l_u, l_v>'
    return True


def meeting_case_trial(rng):
    """(BE-55)(ii), the MEETING-LINES regime, synthetic: t1, t2 distinct
    coplanar lines through q spanning sigma.  Asserts
    span(t1 ^ t2) = Lambda^2 sigma,  (Lambda^2 sigma)^perpK = itself,  and
    <tau1, tau2> = q ^ sigma (the pencil at the meet), so the survivors
    V cap Lambda^2 sigma land inside <l_u, l_v> whenever V <= lambda^perpK
    with L meeting sigma at q."""
    sig = [v4(rng) for _ in range(3)]
    if rank_exact(sig) != 3:
        return False
    L2 = lam2(sig)
    assert same_space(klein_perp(L2), L2), \
        'Lambda^2 sigma is not its own Klein-perp'

    def ptin(B):
        for _ in range(60):
            c = [rq(rng) for _ in B]
            x = [sum(c[i] * B[i][k] for i in range(len(B))) for k in range(4)]
            if any(t != 0 for t in x):
                return x
        raise RuntimeError('ptin')
    q, a, b = ptin(sig), ptin(sig), ptin(sig)
    if rank_exact([q, a, b]) != 3:
        return False
    t1, t2 = [q, a], [q, b]
    T12 = span([wedge2(x, y) for x in t1 for y in t2])
    assert same_space(T12, L2), 'span(t1 ^ t2) != Lambda^2 sigma'
    pen = span([wedge2(q, sig[i]) for i in range(3)])
    assert dim(pen) == 2, 'q ^ sigma not a pencil'
    assert same_space(span([wedge2(q, a), wedge2(q, b)]), pen), \
        '<tau1, tau2> != the pencil at the meet'
    return True


# ===================================================== modes

def _draw(edges, u, v, rng):
    return guarded_draw(edges, u, v, rng, sampler=sample_piece_config_adj)


def run_dec(seed=SEED, nseeds=2):
    print('===== Step BE53 / (BE-54): the REFORMULATION -- the peel, the')
    print('  perp form of Z, and the modular-law factorization =====')
    print('  Asserted at every draw, as identities of SPACES:')
    print('    rho_bar_1 = <l_u> + W + <l_v>          (BE-31)(i)+(BE-45)(i)')
    print('    Z = mu^perpK cap lambda^perpK')
    print('    rho_bar_1 cap Z = <l_u,l_v> + (W cap Z)  [the modular law]')
    print('  JOB 2, answered by the third line: the target is EQUIVALENT to')
    print('  W cap Z <= <l_u,l_v>.  It does NOT factor through the middle')
    print('  alone -- Z, l_u, l_v are END objects -- and the whole coupling')
    print('  is ONE hyperplane (lambda^perpK) and ONE functional (<., mu>).')
    t0 = time.time()
    nd = 0
    for name, E, u, v, isbar in window_battery() + control_battery():
        rng = random.Random(seed + 101 * len(name))
        rows = []
        for _ in range(nseeds):
            got = _draw(E, u, v, rng)
            if got is None:
                continue
            m = full_measure(E, got[0], got[1], u, v)
            rows.append(m)
            nd += 1
        assert rows, f'no draw at {name}'
        r = rows[0]
        print(f'  {name}: d1={r["d1"]} t={r["t"]} exc={r["exc"]} '
              f'dim(rho cap Z)={r["szi"]} ident={r["ident"]}')
    print(f'  [{nd} guarded draws through both gates; every assert held; '
          f'{time.time() - t0:.0f} s]')


def run_sweep(seed=SEED, nseeds=2, ndraw=6, ntrial=12):
    print('===== Step BE54 / (BE-55): the END-CHOICE LEMMA and the RANK-ONE')
    print('  BUDGET -- one functional, one kill; excess >= 2 fails at EVERY')
    print('  end choice =====')
    t0 = time.time()
    nskew = nmeet = 0
    rows = ([(n, E, u, v, True) for (n, E, u, v, _b) in window_battery()]
            + control_battery())
    for name, E, u, v, expect in rows:
        rng = random.Random(seed + 211 * len(name))
        got = _draw(E, u, v, rng)
        assert got is not None, f'no draw at {name}'
        pt0 = got[0]
        w1, w2, _C = series_data(E, u, v)
        idents, excs = [], []
        for _ in range(ndraw):
            rs = resweep(E, u, v, pt0, rng)
            if rs is None:
                continue
            pt, planes, aux = rs
            if end_choice_check(aux, pt, u, v, w1, w2):
                nskew += 1
            m = full_measure(E, pt, planes, u, v)
            idents.append(m['ident'])
            excs.append(m['exc'])
        assert idents, f'no resweep draw at {name}'
        ok = sum(idents)
        exc = max(excs)
        # the per-L criterion: excess >= 2 <=> identity fails, per draw
        for e, i in zip(excs, idents):
            assert (e <= 1) == i, 'per-L criterion violated'
        print(f'  {name}: resweeps={len(idents)} ident={ok}/{len(idents)} '
              f'max excess={exc}' + ('' if expect else '  [MUST-FAIL row]'))
        if expect:
            assert ok == len(idents), f'{name}: identity failed in-window'
        else:
            assert ok == 0, f'{name}: a MUST-FAIL row passed'
    for _ in range(ntrial * 4):
        if nmeet >= ntrial:
            break
        rng2 = random.Random(seed + 7919 * (nmeet + 1))
        if meeting_case_trial(rng2):
            nmeet += 1
    assert nmeet >= ntrial, 'too few meeting-lines trials'
    print(f'  [end-choice lemma asserted at {nskew} skew resweeps; '
          f'meeting-lines regime asserted at {nmeet} synthetic trials; '
          f'{time.time() - t0:.0f} s]')


def run_exc(seed=SEED, nseeds=3):
    print('===== Step BE55 / (BE-56): the EXCESS LAW -- delta_1 <= 4 is')
    print('  EXACTLY the budget one functional can pay =====')
    print('  Asserted per draw: dim(W cap <l_u,l_v>) = t + 2 - delta_1;')
    print('  dim V <= t - 1;  excess <= max(0, delta_1 - 3);  and')
    print('  identity <=> excess <= 1.')
    t0 = time.time()
    tab = {}
    for name, E, u, v, isbar in window_battery() + control_battery():
        rng = random.Random(seed + 307 * len(name))
        for _ in range(nseeds):
            got = _draw(E, u, v, rng)
            if got is None:
                continue
            m = full_measure(E, got[0], got[1], u, v)
            assert m['ident'] == (m['exc'] <= 1), 'identity <=> excess <= 1'
            key = (m['d1'], m['t'], m['exc'])
            tab[key] = tab.get(key, 0) + 1
    print('  census of (delta_1, t, excess) over all draws:')
    for k in sorted(tab):
        print(f'    delta_1={k[0]} t={k[1]} excess={k[2]}: {tab[k]} draws')
    assert all(k[2] <= max(0, k[0] - 3) for k in tab), 'excess law violated'
    print(f'  [every assert held; {time.time() - t0:.0f} s]')


def run_cls(seed=SEED, nseeds=2, ndraw=8):
    print('===== Step BE56 / (BE-57): THE THEOREM, END TO END -- the')
    print('  construction of the class proof, run literally =====')
    print('  For each WINDOW piece: fix a guarded middle, redraw the ends')
    print('  (L, p_u, p_v) fresh, re-gate, and assert the identity, (b1),')
    print('  dim Z = 4 and cross-incidence-freeness at EVERY draw.')
    t0 = time.time()
    tot = 0
    for name, E, u, v, isbar in window_battery():
        rng = random.Random(seed + 401 * len(name))
        nid = 0
        for _s in range(nseeds):
            got = _draw(E, u, v, rng)
            if got is None:
                continue
            pt0 = got[0]
            for _ in range(ndraw):
                rs = resweep(E, u, v, pt0, rng)
                if rs is None:
                    continue
                pt, planes, _aux = rs
                m = full_measure(E, pt, planes, u, v)
                assert m['dz'] == 4, 'dim Z != 4'
                assert m['ident'], f'{name}: identity FAILED in-window'
                nid += 1
        assert nid > 0, f'no draws at {name}'
        tot += nid
        print(f'  {name}: identity + (b1) asserted at {nid} end draws')
    print(f'  [the identity held at {tot}/{tot} guarded window draws; '
          f'{time.time() - t0:.0f} s]')


def run_wide(seed=SEED, nseeds=2):
    print('===== Step BE57 / (BE-58): JOB 3 -- the window is NOT exactly')
    print('  the barbells =====')
    print('  For each piece: series both ends?, delta_1, d_min, dist,')
    print('  (M2)?, dim Z -- the window test -- plus the trichotomy data')
    print('  (t, T_1 <= W?, T_2 <= W?, dim(W cap <l_u,l_v>)).')
    t0 = time.time()
    nonbar = 0
    from bimage import plane_at
    for name, E, u, v, isbar in window_battery():
        rng = random.Random(seed + 503 * len(name))
        got = _draw(E, u, v, rng)
        assert got is not None, f'no draw at {name}'
        pt, planes = got
        m = full_measure(E, pt, planes, u, v)
        w1, w2, C = series_data(E, u, v)
        dmin = d_min_of(E, pt, u, v)
        nbg = neighbors(E)
        dist = {u: 0}
        q = [u]
        i = 0
        while i < len(q):
            x = q[i]; i += 1
            for y in nbg.get(x, ()):
                if y not in dist:
                    dist[y] = dist[x] + 1
                    q.append(y)
        d = dist[v]
        m2 = (m['d1'] == dmin)
        inwin = (m['d1'] <= 4 and not m2 and m['dz'] == 4 and d >= 5)
        # trichotomy data: the boundary pencils against W
        p1 = plane_at(C, pt, w1)
        p2 = plane_at(C, pt, w2)
        t1in = bool(p1 is not None and m['Wm'] and
                    contains(m['Wm'], pencil_space(hat(pt[w1]), p1)))
        t2in = bool(p2 is not None and m['Wm'] and
                    contains(m['Wm'], pencil_space(hat(pt[w2]), p2)))
        print(f'  {name}: WINDOW={inwin} [d1={m["d1"]} dmin={dmin} dist={d} '
              f'dimZ={m["dz"]}] t={m["t"]} T1<=W={t1in} T2<=W={t2in} '
              f'dim(W cap Luv)={m["wluv"]} barbell={isbar}')
        assert inwin, f'{name}: not in the window'
        if not isbar:
            nonbar += 1
    assert nonbar >= 5, 'fewer than five non-barbell window pieces'
    print(f'  [{nonbar} NON-barbell pieces verified IN the window, an R-node')
    print('   middle among them: "barbell" is a sampler artifact, not the')
    print('   window; every one is covered by the (BE-57) theorem anyway;')
    print(f'   {time.time() - t0:.0f} s]')


def run_validate():
    """Reduced tier of all five modes."""
    t0 = time.time()
    run_dec(nseeds=1)
    run_sweep(nseeds=1, ndraw=3, ntrial=6)
    run_exc(nseeds=1)
    run_cls(nseeds=1, ndraw=3)
    run_wide(nseeds=1)
    print(f'===== validate: all five modes at reduced tier, every assert '
          f'held ({time.time() - t0:.0f} s) =====')


MODES = dict(dec=run_dec, sweep=run_sweep, exc=run_exc, cls=run_cls,
             wide=run_wide, validate=run_validate)

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    print(f'bwin.py {mode}  (seed literal {SEED}; exact Q; both gates on '
          'every draw)')
    MODES[mode]()
