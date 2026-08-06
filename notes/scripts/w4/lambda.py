"""
Phase 39, direction B -- (K-Lambda): the quadric-avoidance gap of the (T5)
Lambda-compression, settled.  Exact-Q, on top of `pitch.py`.

Setting (as in `pitch.py`): hard-stratum split chain b - v - a - c with b, c
hubs, G' = G - v + ab, target-rank pencil-generic seed, dim R_a = 1,
H := G - v - a, V_bc := {m(b) - m(c) : m a motion of H} (3-dim generically),
T := <C_ab, C_ac> (the pencil of lines through pt(a) in plane(a,b,c)),
z spans V_bc cap T^{perp B}, Q(x) = B(x,x) the pitch quadric.  A length-k
companion b - x_1 - ... - x_{k-1} - c in H gives S := <C_1..C_k> with
V_bc <= S (path-sum containment); for k = 4 the far data enters only through
the annihilator covector lambda of V_bc in S, and Phi_loc(lambda) := Q(z).

What this driver establishes (each mode tests the sentence it is cited for).
The headline is a CORRECTION of the framing: "a point off a quadric" is not
the content, and neither is the non-degeneracy of Phi_loc.

  (L1) --witt    Phi_loc is NEVER the zero form, and is never a full-rank
                 quadric either: {x in T^{perp B} : Q(x) = 0} = Lambda^2
                 alpha(pt a) cup Lambda^2 beta(plane a,b,c) (Witt: T^{perp B}/T
                 is a hyperbolic plane), so at k = 4 the "local quadric" is a
                 pair of DISTINCT rational HYPERPLANES {lambda . w+ = 0} cup
                 {lambda . w- = 0}, with
                    w+ = cof(m, n, s)  the unique companion-span line through pt(a),
                    w- = cof(m, n, q)  the unique companion-span line in plane(a,b,c),
                 and Phi_loc = c (lambda.w+)(lambda.w-), c = -2 B(w+,w-)/(q.w+)^2.
                 All entries are 4-point brackets in {b, x1, x2, x3, c, a}.
                 So the workbook's flagged degeneration ("Phi_loc the zero
                 form") is IMPOSSIBLE -- but lambda is a FAR datum, not a free
                 point, so that closes nothing by itself.
  (L2) --span    Sweeping pt(a) = p0 + t*d along the meet line M (V_bc is
                 a-free), w+(t) has degree <= 3 and w-(t) degree <= 2, and
                 BOTH projective spans are 3-dimensional -- NOT 4:
                    span w+(t) = S cap C(M)^{perp B},  annihilator <p+>,
                                 p+_i = B(C_i, C(M));
                    span w-(t) = S cap C(bc)^{perp B}, annihilator <q>.
                 So exactly TWO far covectors are bad for the whole a-line.
  (L3) --dichot  Hence the a-line dichotomy: Q(z(t)) == 0 identically iff
                 lambda ~ p+ (i.e. V_bc <= C(M)^{perp B} -- which by (T3) IS
                 the genuine escape failure) or lambda ~ q (i.e.
                 V_bc <= C(bc)^{perp B}, whereupon (T1) forces star(r) ~ C(bc)
                 and route A escapes because pt(c) notin Pi(b)).
                 Corollary: (K-Lambda) at a length-4-companion split is
                 EQUIVALENT to (K-wit) there.  The pitch certificate is blind
                 only where the escape actually fails.
  (L4) --habitat End-to-end at real habitats (theta(3,4,5), NT21 and three new
                 length-4-companion shapes NT24 / NT30, plus theta(3,3,6) for
                 the k = 3 corollary): lambda off both bad points, Q(z) != 0,
                 the (T2) sign law against the independently computed stress,
                 and (T3) agreement.  At k = 3, S cap Lambda^2 alpha =
                 S cap Lambda^2 beta = 0 -- which is WHY Step 5's monomial is
                 nonzero, and why k = 3 closes locally and k >= 4 cannot.
  (L5) --l56     dim(S cap Lambda^2 alpha) = k - 3, so k = 4 is the LAST length
                 at which "V_bc meets it" = "V_bc contains it" and the (L2)
                 span argument applies.  At k = 5 the (F-A) bad locus acquires
                 a second component of the same dimension (a smooth conic of
                 2-planes U <= S cap C(M)^perp meeting every P_alpha(t)), which
                 is neither the (T3) failure nor the route-A branch; at k = 6
                 additionally C(M) in S always.  So the frame does NOT reach
                 ell = 5, 6.
  (L6) --adv     The refutation hunt: lambda ~ p+, lambda ~ q, Q(z) = 0,
                 off-pattern spans, C(M) in S, rank Q|V_bc.

Drivers (foreground, one at a time; run from the repo root):
    PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --witt
    PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --span
    PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --dichot
    PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --habitat
    PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --l56
    PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --adv

Conventions (`notes/scripts/README.md` section 4): exact Q only; every sampled
object carries a rank/dimension assert; every rng is `random.Random(<literal>)`
and the seed is printed.

Harness notes for the landing coordinator:
  * `sample_local_frame` is a NEW arc-specific device, not a reimplementation
    of `widened.place_pencil_general`: that function places a whole graph and
    cannot express a local frame with SYNTHETIC far hub-neighbour constraints
    (which is exactly what the class-uniformity claim (L2) needs).  It also
    uses the ROBUST in-plane sampler `repin.rob_in_plane`, whereas
    `place_pencil_general` routes single-hub interiors through the degenerate
    `localtest.in_plane_point` (README *Divergences*, the `plane_basis` row).
    A README *Divergences* row for it should be added when this file lands.
  * `span_meet` (subspace intersection) is likewise new; README section 1 lists
    `span_basis` / `in_span` / `nullspace` but no meet.
"""
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, dot, wedge2, hat, PL        # noqa: E402
from repin import (span_basis, in_span, hodge_star, robust_plane_basis,  # noqa: E402
                   rob_in_plane, lambda2_through, seed_probe)
from localtest import meet_line                                    # noqa: E402
from pitch import (klein, Q, det4, cross4, coords_in, H_motions_vbc,  # noqa: E402
                   z_from, theta_edges, paths_graph, lagrange_coeffs)
from pencil_escape import rquat, rvec3                             # noqa: E402
from nogood_subdiv import deficiency, hcard_ok, triangles           # noqa: E402
from kslide import no_rigid_branch_union                           # noqa: E402


# ---------------- small exact primitives (arc-specific) ---------------------

def br(p, q, r, s):
    """The bracket [p,q,r,s] on four affine Q^3 points."""
    return det4([hat(p), hat(q), hat(r), hat(s)])


def span_meet(A, B):
    """A basis of span(A) cap span(B) inside Q^6.  Both inputs are lists of
    Q^6 vectors.  Solves sum a_i A_i - sum b_j B_j = 0 and returns the
    resulting vectors (as a basis)."""
    if not A or not B:
        return []
    nA, nB = len(A), len(B)
    rows = [[A[i][r] for i in range(nA)] + [-B[j][r] for j in range(nB)]
            for r in range(6)]
    out = []
    for sol in nullspace(rows):
        v = [sum((sol[i] * A[i][k] for i in range(nA)), F(0)) for k in range(6)]
        if any(x != 0 for x in v):
            out.append(v)
    return span_basis(out)


def lambda2_plane_pts(p0, p1, p2):
    """Basis of Lambda^2 (the plane through three affine points) -- three
    lines of the plane.  Asserts the points span it."""
    h0, h1, h2 = hat(p0), hat(p1), hat(p2)
    assert rank([h0, h1, h2]) == 3, "degenerate plane triple"
    bas = [wedge2(h0, h1), wedge2(h0, h2), wedge2(h1, h2)]
    assert rank(bas) == 3, "Lambda^2 beta not 3-dim"
    return bas


def is_line_extensor(x):
    """x in Lambda^2 Q^4 is decomposable iff Q(x) = 0 (Pluecker relation)."""
    return any(k != 0 for k in x) and Q(x) == 0


def poly_of(fn, ts):
    """Interpolate a vector-valued function of t through the sample points
    `ts` (exact).  Returns the list of coefficient vectors, low -> high."""
    vals = [fn(t) for t in ts]
    dim = len(vals[0])
    cols = []
    for k in range(dim):
        cols.append(lagrange_coeffs([(t, v[k]) for t, v in zip(ts, vals)]))
    return [[cols[k][j] for k in range(dim)] for j in range(len(ts))]


def scal_poly_of(fn, ts):
    """Interpolate a scalar function of t (exact); coefficients low -> high."""
    return lagrange_coeffs([(t, fn(t)) for t in ts])


def poly_deg(coeffs):
    d = -1
    for j, c in enumerate(coeffs):
        if (c if not isinstance(c, list) else max(abs(x) for x in c)) != 0:
            d = j
    return d


def vec_poly_deg(coeffs):
    d = -1
    for j, v in enumerate(coeffs):
        if any(x != 0 for x in v):
            d = j
    return d


# ---------------- the local frame of a companion split ----------------------

def sample_local_frame(seed, complen=4, hubpat=None, farhub=(0, 0),
                       tries=40):
    """One LOCAL frame of a companion split: the hub pair (b, c) with panels,
    the companion path b - x_1 - .. - x_{complen-1} - c, and the meet line M
    carrying pt(a).  NOTHING far is sampled: the far part of H enters the
    (T5) picture only through the covector lambda, which this frame leaves
    free -- that is exactly what makes the (L2) claims class-uniform.

    `hubpat[i]` says whether x_{i+1} is a hub.  `farhub` is the number of FAR
    hub neighbours per frame node -- either a 2-tuple `(kb, kc)` (only b and c
    carry far hub neighbours) or a tuple of length `complen + 1` covering
    `b, x_1, .., x_{complen-1}, c`.  Each count is capped at `2 - (local hub
    neighbours)` by `hcard`, and is modelled by that many generic normal
    constraints -- the same rule `widened.place_pencil_general` applies.  The
    x-side counts matter: a companion hub with two far hub neighbours has its
    normal pinned up to scale, the tightest stratum of the local chart.

    Every sampled object is rank/dimension asserted; a degenerate draw is
    rejected and redrawn.  Returns a dict or None."""
    if hubpat is None:
        hubpat = tuple([False] * (complen - 1))
    assert len(hubpat) == complen - 1
    rng = random.Random(seed)
    path = ['b'] + [f'x{i}' for i in range(1, complen)] + ['c']
    ishub = {'b': True, 'c': True}
    for i, h in enumerate(hubpat):
        ishub[f'x{i+1}'] = bool(h)
    nbr = {path[i]: [u for u in (path[i - 1] if i else None,
                                 path[i + 1] if i + 1 < len(path) else None)
                     if u is not None] for i in range(len(path))}
    hubs = [u for u in path if ishub[u]]
    for _ in range(tries):
        pt, nrm = {}, {}
        for h in hubs:
            pt[h] = rvec3(rng)
        if len(set(tuple(pt[h]) for h in hubs)) != len(hubs):
            continue
        ok = True
        for h in hubs:
            cons = [[pt[u][i] - pt[h][i] for i in range(3)]
                    for u in nbr[h] if ishub[u]]
            if len(farhub) == len(path):
                nfar = farhub[path.index(h)]
            else:
                nfar = {'b': farhub[0], 'c': farhub[1]}.get(h, 0)
            # hcard: at most two hub neighbours in all
            nfar = min(nfar, 2 - len(cons))
            cons = cons + [rvec3(rng) for _ in range(max(nfar, 0))]
            if cons:
                bas = nullspace(cons)
                if not bas:
                    ok = False
                    break
                assert rank(bas) == len(bas), "normal space basis dependent"
                co = [rquat(rng) for _ in bas]
                nrm[h] = [sum((k * bb[i] for k, bb in zip(co, bas)), F(0))
                          for i in range(3)]
            else:
                nrm[h] = rvec3(rng)
            if all(x == 0 for x in nrm[h]):
                ok = False
                break
            assert robust_plane_basis(nrm[h]) is not None
            b0, b1 = robust_plane_basis(nrm[h])
            assert rank([b0, b1]) == 2, "in-plane basis degenerate"
        if not ok:
            continue
        if rank([nrm['b'], nrm['c']]) != 2:      # panels parallel
            continue
        # panels non-incident (the Step-6a chart condition):
        if dot(nrm['b'], [pt['c'][i] - pt['b'][i] for i in range(3)]) == 0:
            continue
        if dot(nrm['c'], [pt['b'][i] - pt['c'][i] for i in range(3)]) == 0:
            continue
        placed = dict(pt)
        for u in path:
            if ishub[u]:
                continue
            hn = [w for w in nbr[u] if ishub[w]]
            if len(hn) >= 2:
                p0, d = meet_line(pt[hn[0]], nrm[hn[0]], pt[hn[1]], nrm[hn[1]])
                if all(x == 0 for x in d):
                    ok = False
                    break
                tt = rquat(rng)          # ONE parameter, not one per coordinate
                placed[u] = [p0[i] + tt * d[i] for i in range(3)]
            elif len(hn) == 1:
                placed[u] = rob_in_plane(pt[hn[0]], nrm[hn[0]], rng)
            else:
                placed[u] = rvec3(rng)
        if not ok:
            continue
        # the pencil condition, restated as an assert (not a filter):
        for h in hubs:
            for u in nbr[h]:
                assert dot(nrm[h], [placed[u][i] - pt[h][i]
                                    for i in range(3)]) == 0, "pencil broken"
        if len(set(tuple(placed[u]) for u in path)) != len(path):
            continue
        # the meet line M and its parametrization
        Mp0, Md = meet_line(pt['b'], nrm['b'], pt['c'], nrm['c'])
        if all(x == 0 for x in Md):
            continue
        # the companion lines
        C = [wedge2(hat(placed[path[i]]), hat(placed[path[i + 1]]))
             for i in range(complen)]
        if rank(C) != min(complen, 6):
            continue
        CM = wedge2(hat(Mp0), hat([Mp0[i] + Md[i] for i in range(3)]))
        assert is_line_extensor(CM), "C(M) not a line extensor"
        return {'seed': seed, 'complen': complen, 'hubpat': tuple(hubpat),
                'bl': 'b', 'cl': 'c',
                'farhub': tuple(farhub), 'path': path, 'placed': placed,
                'pt': pt, 'nrm': nrm, 'C': C, 'M': (Mp0, Md), 'CM': CM,
                'rng': rng}
    return None


def a_of(fr, t):
    p0, d = fr['M']
    return [p0[i] + t * d[i] for i in range(3)]


def rows_mnqs(fr, t, waux):
    """The four bracket rows of the (T5) frame at pt(a) = p0 + t d:
    m_i = B(C_i, C_ab), n_i = B(C_i, C_ac), q_i = B(C_i, C_bc),
    s_i = B(C_i, C(a,w)).  q is a-free; the others are linear in t."""
    C, pl = fr['C'], fr['placed']
    ah, bh, ch, wh = (hat(a_of(fr, t)), hat(pl[fr['bl']]), hat(pl[fr['cl']]),
                      hat(waux))
    Cab, Cac, Cbc, Caw = (wedge2(ah, bh), wedge2(ah, ch),
                          wedge2(bh, ch), wedge2(ah, wh))
    return ([klein(Ci, Cab) for Ci in C], [klein(Ci, Cac) for Ci in C],
            [klein(Ci, Cbc) for Ci in C], [klein(Ci, Caw) for Ci in C],
            (Cab, Cac, Cbc, Caw))


def in_S(fr, x):
    return in_span(x, span_basis(fr['C']))


# ---------------- (L1) the Witt structure and the factorization -------------

def witt_at(fr, t, waux, verbose=False):
    """The (L1) battery at one local frame + one pt(a).  All asserts."""
    C = fr['C']
    k = fr['complen']
    m, n, q, s, (Cab, Cac, Cbc, Caw) = rows_mnqs(fr, t, waux)
    T = [Cab, Cac]
    assert rank(T) == 2, "T not 2-dim"
    assert Q(Cab) == 0 and Q(Cac) == 0 and klein(Cab, Cac) == 0, \
        "T not totally isotropic"
    # T^{perp B} = {x : <x, star Cab> = <x, star Cac> = 0}
    Tp = nullspace([hodge_star(Cab), hodge_star(Cac)])
    assert len(Tp) == 4, "T^perp not 4-dim"
    assert all(in_span(x, span_basis(Tp)) for x in T), "T not inside T^perp"
    # the two maximal isotropics through T: alpha(pt a) and beta(plane abc)
    La = lambda2_through(hat(a_of(fr, t)))
    Lb = lambda2_plane_pts(a_of(fr, t), fr['placed'][fr['bl']],
                           fr['placed'][fr['cl']])
    assert len(La) == 3 and len(Lb) == 3
    for W in (La, Lb):
        for i in range(3):
            for j in range(3):
                assert klein(W[i], W[j]) == 0, "not totally isotropic"
        assert all(in_span(x, span_basis(Tp)) for x in W), "not inside T^perp"
    assert len(span_meet(La, Lb)) == 2, "alpha cap beta != T"
    # Q vanishes on T^perp exactly on alpha cup beta: check the rank-2 shape
    # of the induced form on T^perp/T (a hyperbolic plane).
    quot = [x for x in Tp if not in_span(x, span_basis(T))]
    G4 = [[klein(x, y) for y in Tp] for x in Tp]
    assert rank(G4) == 2, "Q|T^perp not rank 2"
    rad = nullspace(G4)
    radv = span_basis([[sum((u[i] * Tp[i][kk] for i in range(4)), F(0))
                        for kk in range(6)] for u in rad])
    assert len(radv) == 2 and all(in_span(x, span_basis(T)) for x in radv), \
        "radical of Q|T^perp is not T"
    # N = S cap T^perp
    S = span_basis(C)
    N = span_meet(S, Tp)
    assert len(N) == max(k + 4 - 6, 1), f"dim N = {len(N)} (k = {k})"
    ST = span_meet(S, T)
    Pa, Pb = span_meet(S, La), span_meet(S, Lb)
    assert len(Pa) == k - 3 and len(Pb) == k - 3, \
        f"S cap alpha/beta dims {len(Pa)}/{len(Pb)} at k = {k}"
    GN = [[klein(x, y) for y in N] for x in N]
    out = {'dim N': len(N), 'dim S cap T': len(ST), 'rank Q|N': rank(GN),
           'dim S cap alpha': len(Pa), 'dim S cap beta': len(Pb)}
    if k == 4:
        assert len(ST) == 0, "S cap T != 0 at k = 4"
        assert rank([m, n]) == 2, "m, n dependent"
        # the two isotropic directions of the hyperbolic plane N
        wp, wm = cross4(m, n, s), cross4(m, n, q)
        for w, nm in ((wp, 'w+'), (wm, 'w-')):
            assert any(x != 0 for x in w), f"{nm} = 0"
            xx = [sum((w[i] * C[i][kk] for i in range(4)), F(0))
                  for kk in range(6)]
            assert Q(xx) == 0, f"{nm} not isotropic"
            assert is_line_extensor(xx), f"{nm} not a line"
        wpv = [sum((wp[i] * C[i][kk] for i in range(4)), F(0))
               for kk in range(6)]
        wmv = [sum((wm[i] * C[i][kk] for i in range(4)), F(0))
               for kk in range(6)]
        assert in_span(wpv, span_basis(Pa)), "w+ is not S cap alpha"
        assert in_span(wmv, span_basis(Pb)), "w- is not S cap beta"
        assert rank([wpv, wmv]) == 2, "w+ ~ w-"
        Bpm = klein(wpv, wmv)
        assert Bpm != 0, "Q|N degenerate (w+ = w-)"
        assert rank(GN) == 2, "Q|N not rank 2 at k = 4"
        # Phi_loc as a 4x4 symmetric matrix, via the linear map lambda -> omega
        Lmat = []
        for i in range(4):
            e = [F(1) if j == i else F(0) for j in range(4)]
            Lmat.append(cross4(e, m, n))          # row i = omega(e_i)
        Gram = [[klein(C[i], C[j]) for j in range(4)] for i in range(4)]
        # Phi(lambda) = omega(lambda)^T Gram omega(lambda); omega linear:
        PhiM = [[sum((Lmat[i][p] * Gram[p][r] * Lmat[j][r]
                      for p in range(4) for r in range(4)), F(0))
                 for j in range(4)] for i in range(4)]
        assert any(x != 0 for row in PhiM for x in row), "Phi_loc == 0"
        assert rank(PhiM) == 2, f"rank Phi_loc = {rank(PhiM)}"
        # the factorization identity, as polynomials in lambda:
        qw = dot(q, wp)
        assert qw != 0, "q . w+ = 0"
        RHS = [[-Bpm * (wp[i] * wm[j] + wm[i] * wp[j]) for j in range(4)]
               for i in range(4)]
        LHS = [[qw * qw * PhiM[i][j] * 2 for j in range(4)] for i in range(4)]
        # Phi(l) = l^T PhiM l ; RHS form -2 Bpm (l.w+)(l.w-) has matrix
        # -Bpm (w+ w-^T + w- w+^T).  Scale-match by one evaluation:
        assert LHS is not None
        num = None
        for i in range(4):
            for j in range(4):
                if RHS[i][j] != 0:
                    num = (qw * qw * PhiM[i][j]) / RHS[i][j]
                    break
            if num is not None:
                break
        assert num == 1, f"factorization scalar {num} != 1"
        for i in range(4):
            for j in range(4):
                assert qw * qw * PhiM[i][j] == RHS[i][j], \
                    "Phi_loc does not factor as (l.w+)(l.w-)"
        out['factor scalar'] = num
        out['Phi rank'] = rank(PhiM)
        # the Gram determinant of Q|S: (g1 g2)^2
        g1, g2 = klein(C[0], C[2]), klein(C[1], C[3])
        out['g1 g2 != 0'] = (g1 != 0 and g2 != 0)
        assert rank(Gram) == 4, "Q|S degenerate at k = 4"
    if verbose:
        print("   ", out)
    return out


def witt():
    print("== (L1) the Witt structure of the (T5) local quadric ==")
    print("   seeds: local frames 4000.., habitats via pitch's seed_probe")
    n_ok = 0
    strata = [((False, False, False), (0, 0)),
              ((True, False, False), (1, 0)),
              ((False, True, False), (0, 0)),
              ((True, True, True), (0, 0)),
              ((False, False, True), (2, 2))]
    for hp, fh in strata:
        got = 0
        for seed in range(4000, 4120):
            fr = sample_local_frame(seed, 4, hp, fh)
            if fr is None:
                continue
            waux = rvec3(fr['rng'])
            if rank([hat(a_of(fr, F(1))), hat(fr['placed'][fr['bl']]),
                     hat(fr['placed'][fr['cl']]), hat(waux)]) != 4:
                continue
            try:
                o = witt_at(fr, F(1), waux)
            except AssertionError as e:
                print(f"  FAIL stratum hub={hp} far={fh} seed {seed}: {e}")
                raise
            got += 1
            n_ok += 1
            if got >= 3:
                print(f"  stratum hub={hp} far={fh}: 3/3 seeds -- dim N = 2, "
                      f"rank Q|N = 2, S cap T = 0, Phi_loc rank 2 and factors")
                break
        assert got >= 3, f"stratum {hp} {fh}: too few valid frames"
    # the same at the two habitats already validated by pitch --companion4
    for name, E, v, comp in HABITATS4:
        got = 0
        for seed in range(200, 340):
            d = habitat_frame(E, v, seed, comp)
            if d is None:
                continue
            fr, lam = d['fr'], d['lam']
            waux = rvec3(random.Random(77000 + seed))
            if rank([hat(d['a']), hat(fr['placed'][fr['bl']]),
                     hat(fr['placed'][fr['cl']]), hat(waux)]) != 4:
                continue
            witt_at(fr, d['t_a'], waux)
            got += 1
            n_ok += 1
            if got >= 2:
                break
        print(f"  habitat {name}: {got} seeds -- same structure")
        assert got >= 2
    print(f"WITT OK: {n_ok} frames; Phi_loc is never zero, always rank 2, "
          f"always factors into two distinct rational hyperplanes")


# ---------------- habitat frames (real graphs) ------------------------------

def nt24():
    """A second non-theta tight habitat with a length-4 b-c companion, built
    the same way as `pitch.nt21` (hubs b=0, c=1, u=2, w=3): b-c paths of
    length 3 (the split chain) and 4 (the companion), plus b-u:3, u-c:4,
    b-w:4, w-c:3, u-w:3.  sum ell = 24 = 6 * c(G-hub) with c = 4: tight."""
    return paths_graph([3, 4], [(0, 2, 3), (2, 1, 4), (0, 3, 4),
                                (3, 1, 3), (2, 3, 3)])


def theta_like(lengths):
    """theta with the given path lengths (sum 12 = tight); the split chain is
    the FIRST path (length 3), the companion the SECOND."""
    E = theta_edges(lengths)
    return E


def habitat_specs():
    """(name, edges, split vertex v, companion vertex list) for every
    length-4-companion habitat this driver uses.  Each carries a `def = 0`
    assert at load time (`nogood_subdiv.deficiency`, the polynomial oracle).

    The split chain is always the FIRST b-c path (length 3, interiors v and
    a) and the companion the SECOND (length 4)."""
    out = []
    E = theta_edges((3, 4, 5))
    out.append(('theta(3,4,5)', E, 10, [0, 13, 14, 15, 1],
                {0: [0, 10, 11, 1], 1: [0, 13, 14, 15, 1],
                 2: [0, 17, 18, 19, 20, 1]}))
    for name, rest in (
            ('NT21', [(0, 2, 4), (2, 1, 4), (0, 3, 3), (3, 1, 3), (2, 3, 3)]),
            ('NT24', [(0, 2, 3), (2, 1, 4), (0, 3, 4), (3, 1, 3), (2, 3, 3)]),
            ('NT30', [(0, 2, 4), (2, 1, 3), (0, 3, 3), (3, 1, 3), (2, 4, 4),
                      (4, 1, 3), (3, 4, 3)]),
    ):
        Ei, pmi = paths_graph([3, 4], rest)
        out.append((name, Ei, pmi[0][1], pmi[1], pmi))
    # the class predicate, per shape: def = 0, hnoRigid at branch granularity
    # (`kslide.no_rigid_branch_union`), hcard, triangle-free
    for name, E, v, comp, pm in out:
        assert deficiency(E) == 0, f"{name}: def != 0"
        assert no_rigid_branch_union(E, pm), f"{name}: proper rigid branch union"
        assert hcard_ok(E), f"{name}: hcard fails"
        assert not triangles(E), f"{name}: has a triangle"
    return [(n, E, v, c) for (n, E, v, c, pm) in out]


HABITATS4 = habitat_specs()


def habitat_frame(edges, v, seed, comp, need_dimVbc=3):
    """A real habitat seed re-expressed in the local-frame dict shape, plus
    the far covector lambda.  Returns None on an invalid / off-stratum seed.

    Reuses `repin.seed_probe` (hence `widened.place_pencil_general`) for the
    placement, and adds the rank asserts the (L1)-(L4) claims need."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None or p['dim R_a'] != 1:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab0, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if not (b in hubsG and c in hubsG and b in nrm and c in nrm):
        return None
    assert comp[0] == b and comp[-1] == c
    k = len(comp) - 1
    C = [wedge2(hat(placed[comp[i]]), hat(placed[comp[i + 1]]))
         for i in range(k)]
    if rank(C) != min(k, 6):
        return None
    # panels MUTUALLY non-incident (the Step-6a chart condition, BOTH ways --
    # pt(b) in Pi(c) alone already makes plane(a(t),b,c) constant along M and
    # collapses span w-(t) to 1; witness theta(3,4,5) seed 345, see --adv)
    if dot(nrm[b], [placed[c][i] - placed[b][i] for i in range(3)]) == 0:
        return None
    if dot(nrm[c], [placed[b][i] - placed[c][i] for i in range(3)]) == 0:
        return None
    Mp0, Md = meet_line(pt[b], nrm[b], pt[c], nrm[c])
    if all(x == 0 for x in Md):
        return None
    ts = [(placed[a][i] - Mp0[i]) / Md[i] for i in range(3) if Md[i] != 0]
    t_a = ts[0]
    assert all(t == t_a for t in ts), "pt(a) not on the meet line M"
    Vbc, ndim, _ = H_motions_vbc(edges, v, a, b, c, placed)
    if len(Vbc) != need_dimVbc:
        return None
    Sb = span_basis(C)
    for x in Vbc:
        assert in_span(x, Sb), "V_bc escapes the companion span"
    Vco = [coords_in(C, x) for x in Vbc]
    assert all(x is not None for x in Vco)
    assert rank(Vco) == len(Vbc), "V_bc coordinate rank drop"
    lam_space = nullspace(Vco)
    lam = lam_space[0] if len(lam_space) == 1 else None
    fr = {'seed': seed, 'complen': k, 'hubpat': None, 'farhub': None,
          'bl': b, 'cl': c,
          'path': list(comp), 'placed': placed, 'pt': pt, 'nrm': nrm,
          'C': C, 'M': (Mp0, Md),
          'CM': wedge2(hat(Mp0), hat([Mp0[i] + Md[i] for i in range(3)])),
          'rng': random.Random(31337 + seed)}
    return {'fr': fr, 'lam': lam, 'lam space': lam_space, 'Vbc': Vbc,
            'Vco': Vco, 'a': placed[a], 't_a': t_a, 'abc': (a, b, c),
            'r': Ra_basis[0], 'probe': p, 'nmotions': ndim}


# ---------------- (L2) the a-line spans of w+ and w- ------------------------

TS = [F(1), F(2), F(3), F(5), F(-1), F(-3), F(7), F(1, 2)]
def omega_curves(fr, waux, ts=None, strict=True):
    """The two isotropic-direction curves along the meet line M, at k = 4.

    With pt(a) = p0 + t*d on M, w+(t) := cof(m(t), n(t), s(t)) spans
    S cap Lambda^2 alpha(pt a) and w-(t) := cof(m(t), n(t), q) spans
    S cap Lambda^2 beta(plane a,b,c).  Asserted here (this is (L2)):

      * every sample nonzero; deg w+ <= 3, deg w- <= 2 (exact interpolation);
      * the PROJECTIVE span of {w+(t)} is 3-dimensional, equal to
        S cap C(M)^{perp B}, with annihilator <p+>, p+_i = B(C_i, C(M));
      * the projective span of {w-(t)} is 3-dimensional, equal to
        S cap C(bc)^{perp B}, with annihilator <q>;
      * p+ and q are independent, and both are nonzero.

    So the set of far covectors lambda that are bad for the WHOLE a-line is
    exactly the two points [p+], [q] of P^3.  Returns a dict.

    The bracket criterion for the two 3-dimensional spans is the WIDENED
    (Lambda-0f'), not the recorded (Lambda-0f) -- see the comment at the two
    asserts below.  With `strict=False` an off-pattern frame is returned
    instead of raising, and its dict carries `gram = (g13, g14, g24)` so a
    consumer can tell a middle-bracket failure from a Gram one."""
    ts = list(ts or TS)
    C, CM = fr['C'], fr['CM']
    assert fr['complen'] == 4
    good = []
    for t in ts:
        m, n, q, s, _ = rows_mnqs(fr, t, waux)
        if rank([m, n]) != 2:
            continue
        wp, wm = cross4(m, n, s), cross4(m, n, q)
        if all(x == 0 for x in wp) or all(x == 0 for x in wm):
            continue
        good.append((t, wp, wm, q))
    assert len(good) >= 6, f"too few valid t ({len(good)})"
    q0 = good[0][3]
    for (_, _, _, qq) in good:
        assert qq == q0, "q depends on t"
    assert any(x != 0 for x in q0), "q = 0"
    assert q0[0] == 0 and q0[3] == 0, "q structural zeros"
    pplus = [klein(Ci, CM) for Ci in C]
    assert any(x != 0 for x in pplus), "p+ = 0 (C(M) in S^{perp B})"
    assert rank([pplus, q0]) == 2, "p+ ~ q"
    # structural zeros of p+: C1 lies in Pi(b) and C4 in Pi(c), both of which
    # CONTAIN M, and two lines of a common plane always meet.
    assert pplus[0] == 0 and pplus[3] == 0, "p+ structural zeros"
    WP = [g[1] for g in good]
    WM = [g[2] for g in good]
    rp, rm = rank(WP), rank(WM)
    # (Lambda-0f') in explicit bracket form -- the WIDENED criterion proven at
    # the generic point by `m2/lambda0.m2` (workbook (K-Lambda) Step 3), which
    # supersedes the recorded (Lambda-0f) this driver used to code:
    #
    #     span_t w+ = 3  <=>  Pi+ := p+_2 p+_3 g13 g14 g24 != 0
    #     span_t w- = 3  <=>  Pi- := q_2  q_3  g13 g14 g24 != 0
    #
    # with g_ij = B(C_i, C_j) the three surviving entries of the banded Gram
    # of S.  The middle-bracket factors are the recorded (Lambda-0f): neither
    # middle companion line C2 = C(x1 x2), C3 = C(x2 x3) meets M (resp.
    # line(bc)).  The three Gram factors are what (Lambda-0f) MISSED --
    # `g13 g24 != 0` is `rank Q|_S = 4` (asserted by --witt, never linked to
    # the span) and `g14 = [b, x1, x3, c] != 0` -- the two OUTER companion
    # lines must not meet -- was asserted nowhere.  That last clause is
    # reachable: `outer.py --geom` constructs a chart point with g14 = 0 at
    # all four habitats, and the superseded equivalence raised at every one
    # (`notes/scripts/README.md` *Harness debt* item 2, cleared here).  Both
    # directions asserted; the middle-bracket necessity half is constructed in
    # --adv (`degeneracy_witnesses`), the g14 half in `outer.py --geom`.
    g13, g14, g24 = (klein(C[0], C[2]), klein(C[0], C[3]), klein(C[1], C[3]))
    gram = g13 * g14 * g24
    assert (rp == 3) == (pplus[1] != 0 and pplus[2] != 0 and gram != 0), \
        (f"span w+ = {rp} but p+ middle entries "
         f"{(pplus[1] != 0, pplus[2] != 0)}, (g13, g14, g24) nonzero "
         f"{(g13 != 0, g14 != 0, g24 != 0)}")
    assert (rm == 3) == (q0[1] != 0 and q0[2] != 0 and gram != 0), \
        (f"span w- = {rm} but q middle entries "
         f"{(q0[1] != 0, q0[2] != 0)}, (g13, g14, g24) nonzero "
         f"{(g13 != 0, g14 != 0, g24 != 0)}")
    if not strict:
        # the hunt mode records off-pattern frames instead of raising; the
        # bracket equivalence above is still asserted, so an off-pattern frame
        # always carries a vanishing middle bracket OR a vanishing Gram
        # bracket, and `gram` says which.
        if (rp, rm) != (3, 3):
            return {'span w+': rp, 'span w-': rm, 'p+': pplus, 'q': q0,
                    'gram': (g13, g14, g24), 'off-pattern': True}
    assert (rp, rm) == (3, 3), f"OFF-PATTERN spans ({rp}, {rm})"
    annP, annM = nullspace(WP), nullspace(WM)
    assert len(annP) == 1 and rank([annP[0], pplus]) == 1, \
        "annihilator of span(w+) is not <p+>"
    assert len(annM) == 1 and rank([annM[0], q0]) == 1, \
        "annihilator of span(w-) is not <q>"
    # the two spans, as subspaces of Lambda^2, are S cap C(M)^perp and
    # S cap C(bc)^perp:
    Sb = span_basis(C)
    bh, ch = hat(fr['placed'][fr['bl']]), hat(fr['placed'][fr['cl']])
    Cbc = wedge2(bh, ch)
    for (W, L, nm) in ((WP, CM, 'w+ / C(M)'), (WM, Cbc, 'w- / C(bc)')):
        amb = span_basis([[sum((w[i] * C[i][k] for i in range(4)), F(0))
                           for k in range(6)] for w in W])
        assert len(amb) == 3
        for x in amb:
            assert klein(x, L) == 0, f"{nm}: span not inside the perp"
        cut = span_meet(Sb, nullspace([hodge_star(L)]))
        assert len(cut) == 3 and all(in_span(x, cut) for x in amb), \
            f"{nm}: span != S cap perp"
    six = good[:6]
    cp = poly_of(lambda t: cross4(*rows_mnqs(fr, t, waux)[:2],
                                  rows_mnqs(fr, t, waux)[3]),
                 [g[0] for g in six])
    cm = poly_of(lambda t: cross4(*rows_mnqs(fr, t, waux)[:2],
                                  rows_mnqs(fr, t, waux)[2]),
                 [g[0] for g in six])
    dp, dm = vec_poly_deg(cp), vec_poly_deg(cm)
    assert dp <= 3 and dm <= 2, f"degrees ({dp}, {dm})"
    qw = scal_poly_of(lambda t: dot(rows_mnqs(fr, t, waux)[2],
                                    cross4(*rows_mnqs(fr, t, waux)[:2],
                                           rows_mnqs(fr, t, waux)[3])),
                      [g[0] for g in six])
    assert poly_deg(qw) >= 0, "q.w+(t) == 0 identically"
    return {'span w+': rp, 'span w-': rm, 'deg w+': dp, 'deg w-': dm,
            'p+': pplus, 'q': q0, 'deg q.w+': poly_deg(qw)}


HUBPATS = [(False, False, False), (True, False, False),
           (False, True, False), (False, False, True),
           (True, True, False), (False, True, True),
           (True, False, True), (True, True, True)]

# 24 strata with far hub neighbours at b, c only, plus -- for every hub pattern
# that HAS a companion hub -- two more with far hub neighbours on the
# companion hubs as well (1 each, and the maximum 2 each: the tightest
# stratum, where each such normal is pinned up to scale).
STRATA4 = [(hp, fh) for hp in HUBPATS for fh in [(0, 0), (1, 1), (2, 2)]]
STRATA4X = [(hp, tuple([2] + [kx if h else 0 for h in hp] + [2]))
            for hp in HUBPATS if any(hp) for kx in (1, 2)]


def span():
    print("== (L2) the a-line spans of the two isotropic directions ==")
    print("   claim: span w+(t) = S cap C(M)^perp (3-dim, annihilator p+),")
    print("          span w-(t) = S cap C(bc)^perp (3-dim, annihilator q).")
    print("   local frames seeded 5000.., aux point w seeded 880000+seed")
    tot = 0
    for hp, fh in STRATA4 + STRATA4X:
        got, res = 0, []
        for seed in range(5000, 5200):
            fr = sample_local_frame(seed, 4, hp, fh)
            if fr is None:
                continue
            assert not in_S(fr, fr['CM']), f"C(M) in S at seed {seed}"
            waux = rvec3(random.Random(880000 + seed))
            if rank([hat(a_of(fr, F(1))), hat(fr['placed'][fr['bl']]),
                     hat(fr['placed'][fr['cl']]), hat(waux)]) != 4:
                continue
            o = omega_curves(fr, waux)
            res.append((o['span w+'], o['span w-'], o['deg w+'], o['deg w-']))
            got += 1
            tot += 1
            if got >= 4:
                break
        assert got >= 3, f"stratum {hp} {fh}: only {got} frames"
        print(f"  hub={hp} far={fh}: {got} frames, (span w+, span w-, "
              f"deg w+, deg w-) = {sorted(set(res))}")
    for name, E, v, comp in HABITATS4:
        got, res = 0, []
        for seed in range(200, 400):
            d = habitat_frame(E, v, seed, comp)
            if d is None:
                continue
            fr = d['fr']
            assert not in_S(fr, fr['CM']), f"{name} seed {seed}: C(M) in S"
            waux = rvec3(random.Random(990000 + seed))
            if rank([hat(d['a']), hat(fr['placed'][fr['bl']]),
                     hat(fr['placed'][fr['cl']]), hat(waux)]) != 4:
                continue
            o = omega_curves(fr, waux)
            res.append((o['span w+'], o['span w-']))
            got += 1
            tot += 1
            if got >= 3:
                break
        assert got >= 2
        print(f"  habitat {name}: {got} seeds, (span w+, span w-) "
              f"= {sorted(set(res))}")
    print(f"SPAN OK: {tot} frames -- both spans 3-dimensional, identified as "
          f"S cap C(M)^perp and S cap C(bc)^perp, annihilators <p+> and <q>. "
          f"So exactly TWO far covectors are bad for the whole a-line.")


# ---------------- (L3) the a-line dichotomy ---------------------------------

def z_of(fr, t, lam):
    """The reciprocal twist from (lambda, m(t), n(t)) alone -- the (T5)
    Lambda-compression, at k = 4."""
    m, n, q, s, _ = rows_mnqs(fr, t, F_ZERO_PT)
    om = cross4(lam, m, n)
    z = [sum((om[i] * fr['C'][i][k] for i in range(4)), F(0))
         for k in range(6)]
    return z, om


F_ZERO_PT = [F(0), F(0), F(1)]     # the aux point is irrelevant to m, n, q


def qpoly(fr, lam, ts=None):
    """The (T4) quartic in the (T5) normalization: q(t) = Q(z(t)) with
    z(t) = sum cof(lambda, m(t), n(t))_i C_i.  Exact interpolation on six
    points; degree asserted <= 4."""
    ts = list(ts or TS)[:6]
    co = scal_poly_of(lambda t: Q(z_of(fr, t, lam)[0]), ts)
    assert poly_deg(co) <= 4, f"deg q(t) = {poly_deg(co)}"
    return co


def dichot():
    print("== (L3) the a-line dichotomy, and the two bad branches ==")
    print("   local frames seeded 6000..; the two synthetic bad lambdas are")
    print("   p+ = (B(C_i, C(M)))_i  and  q = (B(C_i, C(bc)))_i")
    n_ok = 0
    for hp, fh in STRATA4[:6] + STRATA4[-3:]:
        got = 0
        for seed in range(6000, 6200):
            fr = sample_local_frame(seed, 4, hp, fh)
            if fr is None:
                continue
            waux = rvec3(random.Random(770000 + seed))
            if rank([hat(a_of(fr, F(1))), hat(fr['placed'][fr['bl']]),
                     hat(fr['placed'][fr['cl']]), hat(waux)]) != 4:
                continue
            o = omega_curves(fr, waux)
            pplus, q0 = o['p+'], o['q']
            C = fr['C']
            bh, ch = hat(fr['placed'][fr['bl']]), hat(fr['placed'][fr['cl']])
            Cbc, CM = wedge2(bh, ch), fr['CM']
            # (a) the two bad branches: q(t) == 0 identically
            for lam, L, nm in ((pplus, CM, 'p+ (C(M))'), (q0, Cbc, 'q (C(bc))')):
                co = qpoly(fr, lam)
                assert poly_deg(co) == -1, f"{nm}: q(t) not identically 0"
                # V_bc = ker lam inside S is exactly S cap L^{perp B}
                V = span_meet(span_basis(C),
                              nullspace([hodge_star(L)]))
                assert len(V) == 3
                for x in V:
                    assert klein(x, L) == 0
                Vco = [coords_in(C, x) for x in V]
                assert all(dot(lam, cc) == 0 for cc in Vco), \
                    f"{nm}: ker lambda != S cap perp"
            # (b) a GENERIC lambda: q(t) is NOT identically zero
            rng2 = random.Random(660000 + seed)
            for _ in range(3):
                lam = [rquat(rng2) for _ in range(4)]
                if rank([lam, pplus]) == 1 or rank([lam, q0]) == 1:
                    continue
                co = qpoly(fr, lam)
                assert poly_deg(co) >= 0, "generic lambda: q(t) == 0"
            # (c) the factorization, per t: q(t) = 0 iff lam.w+ = 0 or lam.w- = 0
            for t in TS[:5]:
                m, n, q_, s, _ = rows_mnqs(fr, t, waux)
                if rank([m, n]) != 2:
                    continue
                wp, wm = cross4(m, n, s), cross4(m, n, q_)
                rng3 = random.Random(550000 + seed + int(t * 7))
                lam = [rquat(rng3) for _ in range(4)]
                if rank([lam, m, n]) != 3:
                    continue
                zz, om = z_of(fr, t, lam)
                qw = dot(q_, wp)
                Bpm = klein([sum((wp[i] * fr['C'][i][k] for i in range(4)),
                                 F(0)) for k in range(6)],
                            [sum((wm[i] * fr['C'][i][k] for i in range(4)),
                                 F(0)) for k in range(6)])
                assert qw != 0 and Bpm != 0
                assert (Q(zz) == 0) == (dot(lam, wp) == 0
                                        or dot(lam, wm) == 0), \
                    "per-t factorization broken"
            # (d) branch (iii): V_bc = S cap C(bc)^perp forces star(r) ~ C(bc),
            #     and route A escapes because pt(c) notin Pi(b).
            V = span_meet(span_basis(C), nullspace([hodge_star(Cbc)]))
            for t in TS[:3]:
                ah = hat(a_of(fr, t))
                Cab, Cac = wedge2(ah, bh), wedge2(ah, ch)
                W = span_basis(list(V) + [Cab, Cac])
                assert len(W) == 5, f"dim W = {len(W)} (V_bc cap T != 0?)"
                st = hodge_star(Cbc)
                assert all(dot(st, x) == 0 for x in W), \
                    "star C(bc) not perp to W"
                perp = nullspace(W)
                assert len(perp) == 1 and rank([perp[0], st]) == 1, \
                    "W^perp != <star C(bc)>"
            # route A: C(bc) is not a line of the panel Pi(b)
            L2b = lambda2_plane_pts(fr['placed'][fr['bl']],
                                    rob_in_plane(fr['pt'][fr['bl']],
                                                 fr['nrm'][fr['bl']],
                                                 fr['rng']),
                                    rob_in_plane(fr['pt'][fr['bl']],
                                                 fr['nrm'][fr['bl']],
                                                 fr['rng']))
            assert not in_span(Cbc, span_basis(L2b)), \
                "C(bc) inside Lambda^2 Pihat(b) -- panels incident"
            got += 1
            n_ok += 1
            if got >= 2:
                break
        assert got >= 2, f"stratum {hp} {fh}: only {got} frames"
        print(f"  hub={hp} far={fh}: {got} frames -- both bad branches "
              f"reproduce q(t) == 0; generic lambda gives q(t) != 0; "
              f"branch (iii) gives star(r) ~ C(bc) and route A")
    print(f"DICHOT OK: {n_ok} frames.  q(t) == 0 identically iff "
          f"lambda ~ p+ (the (T3) escape failure) or lambda ~ q (route A "
          f"escapes anyway).")


# ---------------- (L4) end-to-end at real habitats --------------------------

def habitat():
    print("== (L4) end-to-end at real length-4-companion habitats ==")
    print("   seeds 200.. via repin.seed_probe (widened.place_pencil_general)")
    for name, E, v, comp in HABITATS4:
        got = 0
        for seed in range(200, 420):
            d = habitat_frame(E, v, seed, comp)
            if d is None or d['lam'] is None:
                continue
            fr, lam, Vbc = d['fr'], d['lam'], d['Vbc']
            C = fr['C']
            b, c = fr['bl'], fr['cl']
            bh, ch = hat(fr['placed'][b]), hat(fr['placed'][c])
            Cbc, CM = wedge2(bh, ch), fr['CM']
            pplus = [klein(Ci, CM) for Ci in C]
            q0 = [klein(Ci, Cbc) for Ci in C]
            assert any(x != 0 for x in pplus) and any(x != 0 for x in q0)
            # the two bad points, and the distance of the realized lambda
            bad_p = (rank([lam, pplus]) == 1)
            bad_q = (rank([lam, q0]) == 1)
            # the pitch certificate at this seed, and the (T2) sign law
            ah = hat(d['a'])
            Cab, Cac = wedge2(ah, bh), wedge2(ah, ch)
            z, om = z_of(fr, d['t_a'], lam)
            zz, _ = z_from(Vbc, Cab, Cac)
            assert zz is not None and in_span(z, span_basis([zz])), \
                "Lambda-compressed z != computed z"
            r = d['r']
            Qr, Qz = Q(r), Q(z)
            assert (Qr == 0) == (Qz == 0), "(T2) sign law: vanishing"
            if Qr != 0:
                assert Qr * Qz < 0, "(T2) sign law: signs"
            # (T3) cross-check: escape iff V_bc not B-perp to C(M)
            esc = any(klein(x, CM) != 0 for x in Vbc)
            assert esc == (not bad_p), \
                "(T3) escape criterion vs lambda ~ p+"
            assert (Qz != 0) or bad_p or bad_q, \
                "Q(z) = 0 with lambda off both bad points"
            got += 1
            if got == 1:
                print(f"  {name} seed {seed}: lambda ~ p+ ? {bad_p}; "
                      f"lambda ~ q ? {bad_q}; Q(z) != 0: {Qz != 0}; "
                      f"escape (T3): {esc}; sign law OK")
            if got >= 4:
                break
        assert got >= 3, f"{name}: only {got} valid seeds"
        print(f"  {name}: {got} seeds, all with lambda off both bad points, "
              f"Q(z) != 0, (T2) sign law and (T3) agreement")
    # the k = 3 corollary: at a length-3 companion, S cap alpha = S cap beta = 0
    print("  -- k = 3 corollary (why Step 5 closes): S cap Lambda^2 alpha(a)")
    print("     = S cap Lambda^2 beta(abc) = 0, so Q(z) != 0 is automatic")
    E3 = theta_edges((3, 3, 6))
    got = 0
    for seed in range(200, 300):
        d = habitat_frame(E3, 10, seed, [0, 13, 14, 1])
        if d is None:
            continue
        fr = d['fr']
        C = fr['C']
        assert len(C) == 3 and rank(C) == 3
        ah = hat(d['a'])
        La = lambda2_through(ah)
        Lb = lambda2_plane_pts(d['a'], fr['placed'][fr['bl']],
                               fr['placed'][fr['cl']])
        assert len(span_meet(span_basis(C), La)) == 0, "S cap alpha != 0 at k=3"
        assert len(span_meet(span_basis(C), Lb)) == 0, "S cap beta != 0 at k=3"
        assert Q(d['r']) != 0
        got += 1
        if got >= 3:
            break
    assert got >= 3
    print(f"     theta(3,3,6): {got} seeds, both intersections 0, Q(r) != 0")
    print("HABITAT OK")


# ---------------- (L5) companion lengths 5 and 6 ----------------------------

def pluck_of(bas, sub):
    """The Pluecker point (in `exactcore.PL` index order) of `sub` expressed in
    the ordered basis `bas` of a 4-dim space; `sub` must be 2-dimensional."""
    assert len(bas) == 4 and len(sub) == 2
    co = []
    for v in sub:
        rows = [[bas[i][r] for i in range(4)] + [-v[r]] for r in range(6)]
        c = None
        for x in nullspace(rows):
            if x[-1] != 0:
                c = [xi / x[-1] for xi in x[:-1]]
                break
        assert c is not None, "sub not inside the span of bas"
        co.append(c)
    assert rank(co) == 2, "sub coordinate rank drop"
    r0, r1 = co
    return [r0[i] * r1[j] - r0[j] * r1[i] for (i, j) in PL]


def l56():
    print("== (L5) does the (T5) frame reach companion lengths 5 and 6? ==")
    print("   the pivot: dim(S cap Lambda^2 alpha(a)) = k - 3, so k = 4 is the")
    print("   last length at which 'V_bc MEETS it' = 'V_bc CONTAINS it'.")
    print("   local frames seeded 7000..")
    for k in (3, 4, 5, 6):
        got = 0
        for seed in range(7000, 7400):
            fr = sample_local_frame(seed, k, tuple([False] * (k - 1)), (0, 0))
            if fr is None:
                continue
            Sb = span_basis(fr['C'])
            assert len(Sb) == min(k, 6)
            t = F(1)
            ah = hat(a_of(fr, t))
            bh = hat(fr['placed'][fr['bl']])
            ch = hat(fr['placed'][fr['cl']])
            Cab, Cac, Cbc = wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)
            T = [Cab, Cac]
            Tp = nullspace([hodge_star(Cab), hodge_star(Cac)])
            La = lambda2_through(ah)
            Lb = lambda2_plane_pts(a_of(fr, t), fr['placed'][fr['bl']],
                                   fr['placed'][fr['cl']])
            N = span_meet(Sb, Tp)
            Pa, Pb = span_meet(Sb, La), span_meet(Sb, Lb)
            ST = span_meet(Sb, T)
            GN = [[klein(x, y) for y in N] for x in N]
            radc = nullspace(GN)
            rad = span_basis([[sum((u[i] * N[i][kk] for i in range(len(N))),
                                   F(0)) for kk in range(6)] for u in radc])
            # at k = 3, dim N = 1 and rank Q|N = 1 IS the escape: z is
            # non-isotropic because S meets neither maximal isotropic.
            assert rank(GN) == min(2, len(N)), \
                f"k={k}: rank Q|N = {rank(GN)}, dim N = {len(N)}"
            assert len(Pa) == max(k - 3, 0) and len(Pb) == max(k - 3, 0), \
                f"k={k}: dim S cap alpha/beta = {len(Pa)}/{len(Pb)}"
            assert len(rad) == len(ST), "radical of Q|N != S cap T"
            cm_in = in_S(fr, fr['CM'])
            assert cm_in == (k >= 6), f"k={k}: C(M) in S is {cm_in}"
            if got == 0:
                print(f"  k = {k}: dim N = {len(N)}, "
                      f"rank Q|N = {rank(GN)}, "
                      f"dim S cap alpha = dim S cap beta = {len(Pa)}, "
                      f"dim(S cap T) = dim radical = {len(ST)}, "
                      f"C(M) in S: {cm_in}")
            if k == 5:
                # THE k = 5 test.  A bad V_bc with V_bc not inside Y :=
                # S cap C(M)^{perp B} must meet every P_alpha(t) inside the
                # 2-plane U := V_bc cap Y.  Two 2-planes of the 4-dim Y meet
                # iff their Pluecker points pair to 0 under Lambda^4 Y (= the
                # Klein form in PL coordinates).  So such U exist iff
                # W^{perp}, W := span{p(P_alpha(t))}, holds a nonzero
                # DECOMPOSABLE point -- i.e. iff the conic {Q = 0} in P(W^perp)
                # is nonempty, which for a rank-3 form is a smooth conic.
                for L, nm in ((fr['CM'], 'alpha / C(M)'),
                              (Cbc, 'beta / C(bc)')):
                    Y = span_meet(Sb, nullspace([hodge_star(L)]))
                    assert len(Y) == 4, f"dim Y = {len(Y)}"
                    W = []
                    for tt in TS + [F(4), F(-5), F(2, 3), F(11)]:
                        Lat = (lambda2_through(hat(a_of(fr, tt)))
                               if nm.startswith('alpha')
                               else lambda2_plane_pts(
                                   a_of(fr, tt), fr['placed'][fr['bl']],
                                   fr['placed'][fr['cl']]))
                        P = span_meet(Sb, Lat)
                        if len(P) != 2:
                            continue
                        assert all(in_span(x, Y) for x in P), \
                            f"{nm}: P_alpha(t) not inside Y"
                        W.append(pluck_of(Y, P))
                    assert len(W) >= 8
                    dW = rank(W)
                    Wp = nullspace([hodge_star(w) for w in W])
                    GW = [[klein(u, w) for w in Wp] for u in Wp]
                    rk = rank(GW) if Wp else 0
                    if got == 0:
                        print(f"    k = 5, {nm}: dim W = {dW}, "
                              f"dim W^perp = {len(Wp)}, rank Q|W^perp = {rk}"
                              f"  -> the extra bad component is a "
                              f"{'smooth conic (1-dim over Qbar), nonempty' if rk == 3 else 'degenerate case'}")
                    assert dW == 3 and len(Wp) == 3 and rk == 3, \
                        f"k=5 {nm}: (dim W, dim W^perp, rank) = ({dW}, {len(Wp)}, {rk})"
                    # and the containment component IS bad (dimension count)
                    rng = random.Random(202000 + seed)
                    for _ in range(4):
                        co = [[rquat(rng) for _ in range(4)] for _ in range(3)]
                        if rank(co) != 3:
                            continue
                        V = [[sum((co[j][i] * Y[i][kk] for i in range(4)),
                                  F(0)) for kk in range(6)] for j in range(3)]
                        if rank(V) != 3:
                            continue
                        for tt in TS[:4]:
                            Lat = (lambda2_through(hat(a_of(fr, tt)))
                                   if nm.startswith('alpha')
                                   else lambda2_plane_pts(
                                       a_of(fr, tt), fr['placed'][fr['bl']],
                                       fr['placed'][fr['cl']]))
                            P = span_meet(Sb, Lat)
                            assert span_meet(V, P), \
                                f"{nm}: V inside Y fails to meet P(t)"
            got += 1
            if got >= 3:
                break
        assert got >= 3, f"k = {k}: too few frames ({got})"
    print("L56: k = 4 is the boundary.  At k = 5 the (F-A) bad locus has a "
          "SECOND component (a smooth conic's worth of 2-planes U, dim 1 + 2 "
          "= 3, the same dimension as the containment component), and it is "
          "neither the (T3) failure nor the route-A branch; at k = 6, "
          "C(M) in S removes even the local guard.  The frame does NOT reach "
          "ell = 5, 6.")


# ---------------- (L6) the refutation hunt ----------------------------------

def incidence_witness():
    """The necessity of the panel-non-incidence hypothesis, both ways.  At
    theta(3,4,5) seed 345 the sampler happens to put pt(b) IN Pi(c), so
    pt(b) lies on the meet line M, plane(a(t),b,c) is constant along M, and
    span w-(t) collapses from 3 to 1 -- the (L2) claim's hypothesis is not
    decorative.  (Route A still escapes there: pt(c) notin Pi(b).)"""
    E, v, comp = HABITATS4[0][1], HABITATS4[0][2], HABITATS4[0][3]
    p = seed_probe(E, v, 345, nplace=0)
    assert p is not None
    placed, pt, nrm, hubs, nb, U, Ra, Cab0, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    assert dot(nrm[c], [placed[b][i] - placed[c][i] for i in range(3)]) == 0, \
        "seed 345 is not the panel-incidence witness any more"
    assert dot(nrm[b], [placed[c][i] - placed[b][i] for i in range(3)]) != 0
    Mp0, Md = meet_line(pt[b], nrm[b], pt[c], nrm[c])
    # section 4 convention 1.  The other three `meet_line` sites in this module
    # (`:260`, `:280`, `:565`) already test the zero direction; this one did
    # not, and the `rank(...) == 2` assert below does NOT stand in for it --
    # with `Md == 0` its second entry equals its first, so it passes vacuously
    # at rank 2.  Since 2026-08-06 `meet_line` signals instead of raising, so
    # the test has to be explicit (unreachable on any recorded run).
    assert any(x != 0 for x in Md), \
        f"panels Pi({b}), Pi({c}) parallel: no meet line M"
    fr = {'complen': 4, 'path': list(comp), 'placed': placed, 'pt': pt,
          'nrm': nrm, 'bl': b, 'cl': c, 'M': (Mp0, Md),
          'C': [wedge2(hat(placed[comp[i]]), hat(placed[comp[i + 1]]))
                for i in range(4)],
          'CM': wedge2(hat(Mp0), hat([Mp0[i] + Md[i] for i in range(3)]))}
    assert rank([hat(Mp0), hat([Mp0[i] + Md[i] for i in range(3)]),
                 hat(placed[b])]) == 2, "pt(b) not on M"
    waux = rvec3(random.Random(440345))
    WM = []
    for t in TS:
        m, n, q, s_, _ = rows_mnqs(fr, t, waux)
        if rank([m, n]) != 2:
            continue
        wm = cross4(m, n, q)
        if any(x != 0 for x in wm):
            WM.append(wm)
    assert len(WM) >= 6 and rank(WM) == 1, f"span w- = {rank(WM)}"
    print(f"  panel-incidence witness theta(3,4,5) seed 345: pt(b) in Pi(c), "
          f"pt(b) on M, span w-(t) = 1 (not 3) -- the hypothesis is load-bearing")


def _move_x3(fr, target, uval=F(3)):
    """A copy of the local frame with pt(x3) moved inside Pi(c) so that the
    bracket `target` vanishes: 'p3' = [x2, x3, M0, M1] (C3 meets M), 'q3' =
    [x2, x3, b, c] (C3 meets line(bc)).  Both are affine-linear in pt(x3)
    within Pi(c), so this is an exact solve.  Returns None if degenerate."""
    pl = dict(fr['placed'])
    pc, nc = fr['pt'][fr['cl']], fr['nrm'][fr['cl']]
    b0, b1 = robust_plane_basis(nc)
    assert rank([b0, b1]) == 2
    M0 = fr['M'][0]
    M1 = [fr['M'][0][i] + fr['M'][1][i] for i in range(3)]
    x2 = pl['x2']
    ref = ((M0, M1) if target == 'p3'
           else (pl[fr['bl']], pl[fr['cl']]))
    g = br(x2, pc, *ref)
    A = br(x2, [pc[i] + b0[i] for i in range(3)], *ref) - g
    Bc = br(x2, [pc[i] + b1[i] for i in range(3)], *ref) - g
    if A == 0 and Bc == 0:
        return None
    if A != 0:
        sv, uv = -(g + Bc * uval) / A, uval
    else:
        sv, uv = uval, -g / Bc
    x3 = [pc[i] + sv * b0[i] + uv * b1[i] for i in range(3)]
    assert dot(nc, [x3[i] - pc[i] for i in range(3)]) == 0, "x3 left Pi(c)"
    assert br(x2, x3, *ref) == 0, "bracket not forced to zero"
    pl['x3'] = x3
    out = dict(fr)
    out['placed'] = pl
    out['C'] = [wedge2(hat(pl[fr['path'][i]]), hat(pl[fr['path'][i + 1]]))
                for i in range(4)]
    if rank(out['C']) != 4 or in_S(out, out['CM']):
        return None
    return out


def degeneracy_witnesses():
    """(Lambda-0f) is a genuine hypothesis: forcing the ONE non-structural
    bracket [x2, x3, M0, M1] = 0 (C3 meets M) collapses span w+(t) from 3 to
    2, and forcing [x2, x3, b, c] = 0 (C3 meets line(bc)) collapses
    span w-(t).  Exact, constructed (not searched for)."""
    for target, which in (('p3', 'w+'), ('q3', 'w-')):
        got = 0
        for seed in range(9000, 9080):
            fr = sample_local_frame(seed, 4, (False, False, False), (0, 0))
            if fr is None:
                continue
            fr2 = _move_x3(fr, target)
            if fr2 is None:
                continue
            waux = rvec3(random.Random(9990 + seed))
            if rank([hat(a_of(fr2, F(1))), hat(fr2['placed'][fr2['bl']]),
                     hat(fr2['placed'][fr2['cl']]), hat(waux)]) != 4:
                continue
            WP, WM = [], []
            for t in TS:
                m, n, q_, s_, _ = rows_mnqs(fr2, t, waux)
                if rank([m, n]) != 2:
                    continue
                wp, wm = cross4(m, n, s_), cross4(m, n, q_)
                if any(x != 0 for x in wp):
                    WP.append(wp)
                if any(x != 0 for x in wm):
                    WM.append(wm)
            rp, rm = rank(WP), rank(WM)
            assert (rp, rm) == ((2, 3) if target == 'p3' else (3, 2)), \
                f"{target}: spans ({rp}, {rm})"
            got += 1
            if got >= 4:
                break
        assert got >= 4, f"{target}: only {got} constructed frames"
        print(f"  (Lambda-0f) necessity, {target}: 4/4 constructed frames with "
              f"the one non-structural bracket forced to 0 have "
              f"span {which}(t) = 2, not 3")


def adv():
    print("== (L6) the refutation hunt ==")
    incidence_witness()
    degeneracy_witnesses()
    print("   looking for: lambda ~ p+ or lambda ~ q at a real habitat seed;")
    print("   span w+(t) != 3; rank Q|V_bc < 3; C(M) in S; Q(z) = 0.")
    print("   pools: seeds 200-299 per habitat (4 habitats); local strata "
          "seeds 8000-8029 over all 38 strata.")
    hits = {'lam~p+': 0, 'lam~q': 0, 'C(M) in S': 0, 'rank Q|Vbc': {},
            'Q(z)=0': 0, 'span': {}, 'seeds': 0, 'off': []}
    for name, E, v, comp in HABITATS4:
        for seed in range(200, 300):          # the hunt pool, per habitat
            d = habitat_frame(E, v, seed, comp)
            if d is None or d['lam'] is None:
                continue
            fr, lam, Vbc = d['fr'], d['lam'], d['Vbc']
            C = fr['C']
            bh = hat(fr['placed'][fr['bl']])
            ch = hat(fr['placed'][fr['cl']])
            Cbc, CM = wedge2(bh, ch), fr['CM']
            pplus = [klein(Ci, CM) for Ci in C]
            q0 = [klein(Ci, Cbc) for Ci in C]
            hits['seeds'] += 1
            if rank([lam, pplus]) == 1:
                hits['lam~p+'] += 1
                print(f"   HIT lambda ~ p+ at {name} seed {seed}")
            if rank([lam, q0]) == 1:
                hits['lam~q'] += 1
                print(f"   HIT lambda ~ q at {name} seed {seed}")
            if in_S(fr, CM):
                hits['C(M) in S'] += 1
            GV = [[klein(x, y) for y in Vbc] for x in Vbc]
            rk = rank(GV)
            hits['rank Q|Vbc'][rk] = hits['rank Q|Vbc'].get(rk, 0) + 1
            z, _ = z_of(fr, d['t_a'], lam)
            if Q(z) == 0:
                hits['Q(z)=0'] += 1
            waux = rvec3(random.Random(440000 + seed))
            if rank([hat(d['a']), bh, ch, hat(waux)]) == 4:
                o = omega_curves(fr, waux, strict=False)
                key = (o['span w+'], o['span w-'])
                hits['span'][key] = hits['span'].get(key, 0) + 1
                if o.get('off-pattern'):
                    hits['off'].append((name, seed, key,
                                        [x == 0 for x in o['p+']],
                                        [x == 0 for x in o['q']]))
    for hp, fh in STRATA4 + STRATA4X:
        for seed in range(8000, 8030):
            fr = sample_local_frame(seed, 4, hp, fh)
            if fr is None:
                continue
            waux = rvec3(random.Random(330000 + seed))
            if rank([hat(a_of(fr, F(1))), hat(fr['placed'][fr['bl']]),
                     hat(fr['placed'][fr['cl']]), hat(waux)]) != 4:
                continue
            if in_S(fr, fr['CM']):
                hits['C(M) in S'] += 1
                continue
            o = omega_curves(fr, waux, strict=False)
            key = (o['span w+'], o['span w-'])
            hits['span'][key] = hits['span'].get(key, 0) + 1
            if o.get('off-pattern'):
                hits['off'].append(('local', (hp, fh, seed), key,
                                    [x == 0 for x in o['p+']],
                                    [x == 0 for x in o['q']]))
            hits['seeds'] += 1
    print(f"  seeds examined: {hits['seeds']}")
    print(f"  lambda ~ p+ : {hits['lam~p+']}    lambda ~ q : {hits['lam~q']}")
    print(f"  Q(z) = 0 : {hits['Q(z)=0']}    C(M) in S : {hits['C(M) in S']}")
    print(f"  rank Q|V_bc histogram : {dict(sorted(hits['rank Q|Vbc'].items()))}")
    print(f"  (span w+, span w-) histogram : {dict(hits['span'])}")
    for row in hits['off']:
        print(f"   off-pattern frame: {row[0]} {row[1]} spans {row[2]}, "
              f"p+ zeros {row[3]}, q zeros {row[4]}")
    assert hits['lam~p+'] == 0 and hits['lam~q'] == 0 and hits['Q(z)=0'] == 0
    # every off-pattern frame in THIS SAMPLE carries a vanishing MIDDLE
    # bracket.  Under the widened (Lambda-0f') a Gram factor (g13, g14, g24)
    # could break the span instead -- the frame's dict now records which --
    # and none of the sampled frames does; the g14 branch is realized only by
    # `outer.py --geom`'s CONSTRUCTED chart point, never by a draw here:
    for row in hits['off']:
        assert row[3][1] or row[3][2] or row[4][1] or row[4][2], \
            f"off-pattern frame with all middle brackets nonzero: {row}"
    print("ADV OK: hunt negative -- no lambda ~ p+, no lambda ~ q, no "
          "Q(z) = 0; every off-pattern frame has a vanishing middle bracket "
          "(the named (Lambda-0f) failure), and nothing else")


def main():
    if '--witt' in sys.argv:
        witt()
    elif '--span' in sys.argv:
        span()
    elif '--dichot' in sys.argv:
        dichot()
    elif '--habitat' in sys.argv:
        habitat()
    elif '--l56' in sys.argv:
        l56()
    elif '--adv' in sys.argv:
        adv()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
