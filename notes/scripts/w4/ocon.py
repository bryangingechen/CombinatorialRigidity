"""
Phase 39, section (K-out) CONTINUATION (direction OCON) -- the containment
residue (OC-8), and why its `hard-stratum target-rank` qualifier is FREE.

WHY THIS DRIVER EXISTS.  `notes/Pencil-informal.md` section (K-out) records
(OC-8) as *at every class shape, the whole-graph pencil chart carries a
HARD-STRATUM TARGET-RANK point with `L_b subseteq/ R_1` or `L_c subseteq/
R_4`*, and section (K-frame) (FR-7) names the residual ingredient as the
IRREDUCIBILITY of that hard-stratum target-rank locus -- "un-owned".  This
driver tests the four linear-algebra sentences that together strike that
ingredient:

  (OC-17) THE HARD STRATUM AT TARGET RANK IS AN *OPEN* SUBVARIETY OF THE
    CHART.  At ANY legal chart point (no genericity),
        dim R_a  =  corank(G')  -  s_0,
    because the stress space of `G'` maps onto `R_a` with kernel exactly the
    stresses of `G' - ab = G - v` (the five `ab` rows are independent on the
    `a` block whenever `pt(a) != pt(b)`).  With `index(G) = 0` and
    `def(G') = 0` this is `dim R_a = 1 - s_0`, so
        Z := {target rank} cap {dim R_a = 1}
           = {rank R(G') = tgt} cap {rank R(G-v) = 5|E(G-v)|},
    an intersection of TWO MAXIMAL-RANK conditions -- Zariski OPEN.  `--check`
    asserts the identity and both maximal-rank readings per frame; `--control`
    exhibits placements OFF `Z` and asserts the identity's other side there
    (a guard is untested until something is rejected -- README section 4
    convention 6).

  (OC-18) `H/X` INFINITESIMALLY RIGID AT A CHART POINT ==> `lambda_1 != 0`.
    `W_1 = {m(b) - m(v*)}` in `H/X` (the weld of `X = {x_1,x_2,x_3,c}`, `e_1`
    NOT deleted) is (OC-1)'s space, and `lambda_1 = 0 <=> dim W_1 = 1`.  If
    `H/X` is infinitesimally rigid at the point then every motion is trivial,
    so `W_1 = 0` and `lambda_1 != 0` -- hence `C_1 in/ R_1` and `L_b subseteq/
    R_1`.  `{H/X infinitesimally rigid}` is `{rank = 6|V(H)| - 6}`, a
    MAXIMAL-RANK hence Zariski-OPEN condition, and `def(H/X) = 0` ((OC-10))
    makes it nonempty in the AMBIENT placement space.  No degree hypothesis:
    this applies at BOTH ends of every class (split, companion) pair.

  (OC-20) THE PANEL-ANNIHILATOR IDENTITY.  `beta_h` is a MAXIMAL totally
    `B`-isotropic 3-space, so `beta_h^{perp_B} = beta_h` and for any subspace
    `T`,
        dim(T cap beta_h)  =  dim T + 3 - 6 + dim(T^{perp_B} cap beta_h).
    At `dim T_u = 4` this reads `dim(T_u cap beta_h) = 1 + dim(T_u^{perp_B}
    cap beta_h)`, so (OC-13)'s shape-level bad case `dim(T_u cap beta_h) = 2`
    is EXACTLY `T_u^{perp_B} cap beta_h != 0`.  Also `R^{perp_B} = <rho>` is a
    line of `Lambda^2 K^4` and (OC-11)'s marked point `p` is the point of
    `Pi(h)` cut out by `B(rho, -)|_{beta_h}` -- i.e. `rho cap Pi(h)` when
    `rho` is decomposable.

  (OC-21) `x_1` LEAVES THE STATEMENT.  At a degree-3 hub with `pt(b)`,
    `pt(u)`, `pt(a)` non-collinear, `L_b = <C(b,u), C(b,a)>` and `C(b,u) in
    R_1` unconditionally ((OC-12)), so
        L_b subseteq R_1   <=>   C(b,a) in R_1,
    a condition on the SPLIT-EDGE hinge line alone.

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --validate
    PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --check
    PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --control

POOLS.  Every figure is over exactly one pool and nothing is aggregated with
`outerline.py`'s POOL-C/G/S/B or `outerwide.py`'s POOL-CW/A/W/SL.

  POOL-OV (--validate)  synthetic exact-Q subspaces from `random.Random(
                        20260819)`, plus TWO CONSTRUCTED witnesses (a `T` with
                        `T^{perp_B} cap beta != 0`, and its negative control).
                        No graph, no placement.
  POOL-OC (--check)     the 4 `lambda.habitat_specs` habitats x placement
                        seeds 200-201, accepted exactly as
                        `outerline.frame_at` accepts them.  Deliberately tiny:
                        this is a DERIVATION pass and the sentences under test
                        are identities, not rates.
  POOL-OZ (--control)   theta(3,4,5) x placement seeds 200-214, UNFILTERED,
                        plus up to 3 CONSTRUCTED points -- (OC-14)'s hub slide
                        ONTO `C_0`, rebuilt here as the adversarial witness
                        that `Z != empty` alone does NOT give (OC-8) and that
                        (OC-18)'s open condition must REJECT.

CONVENTIONS (`notes/scripts/README.md` section 4): exact Q only; a rank /
dimension assert on every sampled object; every rng is `random.Random(<literal>)`
and its seed is printed; no bare `set` is printed.  Nothing existing is
modified -- `outerline.py`, `outerwide.py`, `outer.py`, `repin.py`, `pitch.py`
and `lambda.py` are all READ.

LAYERING (`notes/scripts/README.md` section 2).  A `w4/` leaf ABOVE
`outerwide`, which it imports read-only (`panel_line_space`, `far_twist_space`,
`hub_free_end`, `collinear`, `klein_point_on`, `pencil_centre`) together with
`outerline` (`frame_at`, `weld_motions`, `rel_span`, `line_pencil`); everything
else is a catalogued section-1 primitive.
"""
import importlib
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (dot, hat, neighbors, nullspace,             # noqa: E402
                       rank, wedge2)
from kbare_common import verts_of                                  # noqa: E402
from nogood_subdiv import deficiency                               # noqa: E402
from pitch import klein                                            # noqa: E402
from repin import (hodge_star, in_span, rank_at_V,                 # noqa: E402
                   span_basis)
import outer                                                       # noqa: E402
import outerline as OL                                             # noqa: E402
import outerwide as OW                                             # noqa: E402

LAM = importlib.import_module('lambda')

VALIDATE_SEED = 20260819
CHECK_SEEDS = range(200, 202)
CONTROL_SEEDS = range(200, 215)


# ---------------- the two primitives this pass adds -------------------------

def perp_B(V):
    """A basis of `V^{perp_B} = {x : B(v, x) = 0 for all v in V}` inside
    `Lambda^2 K^4`, `B = pitch.klein` the Klein form.  `B(v, x) = <x, star v>`
    (B is symmetric), so the defining rows are `star v`."""
    if not V:
        return [[F(1) if k == i else F(0) for k in range(6)] for i in range(6)]
    rows = [hodge_star(v) for v in V]
    out = span_basis(nullspace(rows))
    assert len(out) == 6 - rank(V), \
        f"perp_B dimension {len(out)} != 6 - {rank(V)} (B degenerate?)"
    return out


# `meet` MOVED DOWN to `lambda` on 2026-08-20 (the harness move-down round,
# slice 2): it had three consumers -- this module, `zneq` and `oschu` -- past
# README §2 rule 2's trigger, and it belongs beside the `span_meet` it wraps.
# Re-exported here, so `ocon.meet` still resolves for both importers and no
# recorded figure moves.
meet = LAM.meet

# ---------------- the ZNEQ primitives, moved down here 2026-08-20 -----------
#
# `corank_at`, `u_space`, `poly_gcd`, `schubert_data`, `meet_param_of` and
# `bad_t_polys` moved down here from `zneq.py:185ff` in the harness move-down
# round (slice 2): each had gained a second consumer (`oschu`), past README §2
# rule 2's trigger, and this module is the layer under both `zneq` and `oschu`.
# Their private helpers `func_matrix` / `aff_mul` / `poly_trim` came with them,
# since a moved body may not reach back up.  `zneq` re-exports all nine, so
# every `zneq.<name>` call site and every recorded figure is unchanged.  The
# text below is verbatim, `zneq`'s own §(K-out) *Steps O19–O24* devices; two of
# them (`poly_gcd` / `poly_trim`) are pure ℚ[t] algebra and would belong in
# `exactcore` the day a non-(K-out) consumer appears.

def corank_at(edges, placed, V):
    """`corank R(edges) = 5|edges| - rank` in exact Q at an explicit vertex
    list, with the rank asserted against its own row bound."""
    rk, _rows, _er, _idx = rank_at_V(edges, placed, V)
    assert 0 <= rk <= 5 * len(edges), "rank outside its row bound"
    return 5 * len(edges) - rk, rk


def u_space(Hed, VH, placed, b, c, sigma):
    """`(U_H, D)` at one chart point: `D` a basis of the relative twist space
    `{m(b) - m(c)}` of `H` and `U_H = D^perp` in the Euclidean pairing --
    section (K-tight) *Step 2*'s obstruction space `U` at the substituted
    instance `(G', a)`.  Computed by the motion-perp formula
    `repin.seed_probe` uses inline (that code is not exported, so this is a
    second site, not a reimplementation of a catalogued name); the name
    differs because the instance does.

    Asserts *Step 2* item 3's counts at the substituted instance:
    `dim D = 3 + sigma` and `dim U_H = 3 - sigma`."""
    mot, idx = OL.weld_motions(Hed, VH, placed, [])
    D = OL.rel_span(mot, idx, b, c)
    U = nullspace(D) if D else [[F(1) if k == i else F(0) for k in range(6)]
                                for i in range(6)]
    U = span_basis(U)
    assert len(U) == 6 - len(D), "U_H is not the perp of D"
    assert len(D) == 3 + sigma, \
        f"dim{{m(b)-m(c)}} = {len(D)} != 3 + corank(H) = {3 + sigma}"
    assert len(U) == 3 - sigma, \
        f"dim U_H = {len(U)} != 3 - corank(H) = {3 - sigma}"
    return U, D


def func_matrix(U, Cab, Cac):
    """The 2 x dim(U_H) matrix of the two placement functionals
    `u -> <u, C(ab)>`, `u -> <u, C(ac)>` in the `U_H` basis, and the
    dimension of `U_H cap C(ab)^perp cap C(ac)^perp`."""
    A = [[dot(u, Cab) for u in U], [dot(u, Cac) for u in U]]
    rk = rank(A)
    assert rk <= min(2, len(U)), "functional matrix rank out of range"
    return A, rk, len(U) - rk


def aff_mul(p, q):
    """(a0 + a1 t)(b0 + b1 t) as `(c0, c1, c2)`."""
    return (p[0] * q[0], p[0] * q[1] + p[1] * q[0], p[1] * q[1])


def poly_trim(p):
    """Drop trailing zero coefficients (little-endian coefficient list)."""
    q = list(p)
    while q and q[-1] == 0:
        q.pop()
    return q


def poly_gcd(polys):
    """The monic GCD in `Q[t]` of a list of little-endian coefficient tuples,
    as a coefficient list; `[]` when every polynomial is identically zero.
    Degree 0 means the polynomials have NO common root in any extension of
    `Q`; degree d > 0 means the common root set is that GCD's."""
    def gcd2(u, w):
        u, w = poly_trim(u), poly_trim(w)
        while w:
            # u mod w
            while len(u) >= len(w):
                f = u[-1] / w[-1]
                sh = len(u) - len(w)
                for i in range(len(w)):
                    u[sh + i] -= f * w[i]
                u = poly_trim(u)
                if not u:
                    break
            u, w = w, u
        return poly_trim(u)
    g = []
    for p in polys:
        g = gcd2(g, list(p)) if g else poly_trim(list(p))
    if g:
        lead = g[-1]
        g = [x / lead for x in g]
    return g


def schubert_data(U, Mhat, W):
    """(OC-26)'s Schubert quantities at one frame, from `U = U_H` (so
    `D = U^perp`), the meet-line 2-space `Mhat` and the hub-line 2-space
    `W = <pt(b)^, pt(c)^>`:

      `dimK`   dim(D cap (Mhat ^ W)) -- generically 1 in `Gr(3,6)`;
      `pencil` whether some `w` in `W` has `Mhat ^ w subseteq D`, decided
               EXACTLY by one rank computation: the map
               `w -> (Phi(P0 ^ w), Phi(Pd ^ w))` on the 2-space `W` has a
               kernel iff its rank is <= 1.

    `Phi(x) := <., x>|_U`, so `x in D <=> Phi(x) = 0`.  By (OC-26)(ii) the
    meet line is bad at EVERY `t` iff `dimK >= 3` (rank Phi <= 1) or
    `pencil`; both force `dimK >= 2`, a codimension-2 Schubert jump."""
    MW = span_basis([wedge2(q, w) for q in Mhat for w in W])
    assert len(MW) == 4, f"Mhat ^ W is {len(MW)}-dimensional, not 4"
    D = span_basis(nullspace(U)) if U else []
    assert len(D) == 6 - len(U), "D is not U^perp"
    dimK = len(D) + len(MW) - rank(list(D) + list(MW))
    A = [[dot(u, wedge2(Mhat[0], w)) for w in W] for u in U] + \
        [[dot(u, wedge2(Mhat[1], w)) for w in W] for u in U]
    return {'dimK': dimK, 'pencil': rank(A) <= 1}


def meet_param_of(placed, M0, Md, x):
    """The parameter `t` with `placed[x] = M0 + t*Md`, asserted exactly, or
    None when `placed[x]` is off the meet line."""
    i = next((k for k in range(3) if Md[k] != 0), None)
    assert i is not None, "degenerate meet-line direction"
    t = (placed[x][i] - M0[i]) / Md[i]
    if any(placed[x][k] != M0[k] + t * Md[k] for k in range(3)):
        return None
    return t


def bad_t_polys(U, M0, Md, pb, pc):
    """(OC-26): the 2x2 minors of the functional matrix as QUADRATICS in the
    meet-line parameter `t`, exploiting that `C(ab)` and `C(ac)` are
    affine-linear along `M` -- so the matrix is recovered from its values at
    `t = 0` and `t = 1` with no symbolic wedge.  Returns the list of minors as
    `(c0, c1, c2)`, each asserted to reproduce the exact rank at `t = 0`."""
    def mat(t):
        p = [M0[k] + t * Md[k] for k in range(3)]
        return func_matrix(U, wedge2(hat(p), hat(pb)),
                           wedge2(hat(p), hat(pc)))[0]
    A0, A1 = mat(F(0)), mat(F(1))
    n = len(U)
    ent = [[(A0[r][j], A1[r][j] - A0[r][j]) for j in range(n)]
           for r in range(2)]
    # a spot check that the affine reconstruction is exact, at t = 2
    A2 = mat(F(2))
    for r in range(2):
        for j in range(n):
            assert ent[r][j][0] + 2 * ent[r][j][1] == A2[r][j], \
                "C(ab)/C(ac) are not affine-linear along M"
    out = []
    for i in range(n):
        for j in range(i + 1, n):
            p = aff_mul(ent[0][i], ent[1][j])
            q = aff_mul(ent[0][j], ent[1][i])
            out.append(tuple(p[k] - q[k] for k in range(3)))
    return out


# ---------------- --validate: the pure algebra ------------------------------

def rand_span(rng, k):
    """A `k`-dimensional exact-Q subspace of `K^6`, dimension asserted."""
    while True:
        V = [[F(rng.randint(-6, 6)) for _ in range(6)] for _ in range(k)]
        if rank(V) == k:
            return span_basis(V)


def std_beta():
    """`beta` for the plane `Pi = {x_3 = 0} = <e_0, e_1, e_2>`: the three
    lines `e_0^e_1, e_0^e_2, e_1^e_2` in `exactcore.PL` order.  Asserted
    3-dimensional and totally `B`-isotropic."""
    B = [wedge2([F(1), F(0), F(0), F(0)], [F(0), F(1), F(0), F(0)]),
         wedge2([F(1), F(0), F(0), F(0)], [F(0), F(0), F(1), F(0)]),
         wedge2([F(0), F(1), F(0), F(0)], [F(0), F(0), F(1), F(0)])]
    assert rank(B) == 3, "beta is not 3-dimensional"
    for x in B:
        for y in B:
            assert klein(x, y) == 0, "beta is not totally B-isotropic"
    return B


def validate():
    print("== (OC-17)/(OC-20) pure algebra: POOL-OV ==")
    print(f"   rng: random.Random({VALIDATE_SEED}); no graph, no placement.\n")
    rng = random.Random(VALIDATE_SEED)
    beta = std_beta()
    assert len(perp_B(beta)) == 3 and all(in_span(x, beta) for x in perp_B(beta)), \
        "beta is not self-perp under B"
    print("   beta = Lambda^2 of a 3-space: dim 3, totally B-isotropic, "
          "beta^{perp_B} = beta   OK")

    # the Grassmann-with-perp identity, on random spans of every dimension
    hist = {}
    for _ in range(200):
        k = rng.randint(1, 5)
        A = rand_span(rng, k)
        lhs = len(meet(A, beta))
        rhs = k + 3 - 6 + len(meet(perp_B(A), beta))
        assert lhs == rhs, f"dim(A cap beta) = {lhs} != {rhs}"
        hist[(k, lhs)] = hist.get((k, lhs), 0) + 1
    print("   dim(A cap beta) = dim A + 3 - 6 + dim(A^{perp_B} cap beta) at "
          "200 random spans")
    print(f"     (dim A, dim(A cap beta)) -> count: "
          f"{dict(sorted(hist.items()))}")

    # CONSTRUCTED witness (README section 4 convention 6): a 4-space `T` whose
    # B-perp meets beta, i.e. the SHAPE-LEVEL bad case `dim(T cap beta) = 2`.
    C = beta[0]
    assert klein(C, C) == 0, "the chosen panel line is not B-isotropic"
    Cperp = perp_B([C])
    assert len(Cperp) == 5, "C^{perp_B} is not a hyperplane"
    found = None
    for _ in range(400):
        co = [[F(rng.randint(-6, 6)) for _ in range(5)] for _ in range(4)]
        T = span_basis([[sum((co[i][j] * Cperp[j][k] for j in range(5)), F(0))
                         for k in range(6)] for i in range(4)])
        if len(T) == 4:
            found = T
            break
    assert found is not None, "no 4-dimensional subspace of C^{perp_B} drawn"
    T = found
    assert in_span(C, perp_B(T)), "the construction lost its own witness"
    assert len(meet(perp_B(T), beta)) >= 1, "T^{perp_B} misses beta"
    assert len(meet(T, beta)) == 2, \
        f"constructed bad case has dim(T cap beta) = {len(meet(T, beta))}"
    print("   CONSTRUCTED bad case  T subseteq C^{perp_B}, C in beta:  "
          "T^{perp_B} cap beta != 0")
    print("     and dim(T cap beta) = 2  -- the shape-level `L_b subseteq "
          "R_1 for every pt(b)` case   OK")

    # NEGATIVE CONTROL: a generic 4-space misses beta in the perp, and meets
    # it in dimension 1.
    neg = 0
    for _ in range(60):
        T2 = rand_span(rng, 4)
        if not meet(perp_B(T2), beta):
            assert len(meet(T2, beta)) == 1, \
                "generic 4-space with empty perp-meet has dim(T cap beta) != 1"
            neg += 1
    assert neg > 0, "no negative control drawn"
    print(f"   NEGATIVE CONTROL {neg} random 4-spaces with "
          f"T^{{perp_B}} cap beta = 0, every one\n     with "
          f"dim(T cap beta) = 1   OK")
    print("\nVALIDATE OK.")


# ---------------- --check: (OC-17)/(OC-20)/(OC-21) at frames ----------------

def stratum_numbers(E, v, Gp, placed, a, b):
    """`(index(G), def(G'), rank R(G'), tgt, corank(G'), s_0, rank shared,
    5|E(G-v)|, def(G-v))` at ONE placement -- the whole (OC-17) ledger.
    Recomputed here from the catalogued primitives rather than read off
    `outer.stratum_at`, because the point is the IDENTITY between them."""
    nG, mG = len(verts_of(E)), len(E)
    Vp = sorted(verts_of(Gp), key=str)
    tgt = 6 * (nG - 2) - deficiency(Gp)
    rkp, _rows, _er, _idx = rank_at_V(Gp, placed, Vp)
    shared = [e for e in Gp if set(e) != {a, b}]
    rk_sh, _r2, _e2, _i2 = rank_at_V(shared, placed, Vp)
    return {
        'index': 5 * mG - 6 * (nG - 1),
        'defGp': deficiency(Gp),
        'rkp': rkp, 'tgt': tgt,
        'corankGp': 5 * len(Gp) - rkp,
        's0': 5 * len(shared) - rk_sh,
        'rk_sh': rk_sh, 'rows_sh': 5 * len(shared),
        'defshared': deficiency(shared),
    }


def weld_rigidity(d, side):
    """(OC-18) at one frame and one companion end: `dim Mot(H/X)` at the chart
    point, the outer coordinate, and the implication under test.

    `H/X` welds `X = {x_1, x_2, x_3, c}` into one body `v*` WITHOUT deleting
    `e_1 = b x_1`, so `W_1 = {m(b) - m(v*)}` there is (OC-1)'s space and
    `lambda_1 = 0 <=> dim W_1 = 1`.  `H/X` infinitesimally rigid means
    `dim Mot(H/X) = 6`, which forces `W_1 = 0`, hence `lambda_1 != 0`."""
    Hed, VH, placed, P = d['Hed'], d['VH'], d['placed'], d['P']
    if side == 'b':
        h, inner, W, ei = d['b'], P[1], set(P[1:]), 0
    else:
        h, inner, W, ei = d['c'], P[3], set(P[:4]), 3
    mot, idx = OL.weld_motions(Hed, VH, placed, [sorted(W, key=str)])
    W1 = OL.rel_span(mot, idx, h, inner)
    lam0 = (d['lam'][ei] == 0)
    assert len(mot) >= 6, f"welded motion space is {len(mot)} < 6"
    assert lam0 == (len(W1) == 1), \
        "(OC-1) FAILED: lambda_i = 0 is not dim W_i = 1"
    assert len(W1) <= len(mot) - 6, "dim W_i exceeds the flex count"
    if len(mot) == 6:
        assert not lam0, \
            "(OC-18) REFUTED: H/X rigid at the chart point yet lambda_i = 0"
    return {'side': side, 'dimMot': len(mot), 'rigid': len(mot) == 6,
            'dimW': len(W1), 'lam0': lam0}


def panel_row(d, side):
    """(OC-20)/(OC-21) at one frame and one companion end.  Returns a dict, or
    None when the end is not a degree-3 hub (where (OC-12)/(OC-13) do not
    apply and this pass says nothing)."""
    Hed, VH, placed, nrm, P = d['Hed'], d['VH'], d['placed'], d['nrm'], d['P']
    a = d['a']
    if side == 'b':
        h, inner, W = d['b'], P[1], set(P[1:])
    else:
        h, inner, W = d['c'], P[3], set(P[:4])
    nbH = neighbors(Hed)
    others = sorted(set(nbH[h]) - {inner}, key=str)
    if len(others) != 1:
        return None
    u = others[0]
    e = next(ee for ee in Hed if set(ee) == {h, inner})
    mot, idx = OL.weld_motions(Hed, VH, placed, [sorted(W, key=str)], drop=[e])
    R = OL.rel_span(mot, idx, h, inner)
    assert len(R) == 5, f"dim R != 5 at a chart point: {len(R)}"
    beta, pts = OW.panel_line_space(placed, nrm, h)
    T = OW.far_twist_space(Hed, placed, W, h, u, inner)
    assert len(T) == 4, f"dim T_u = {len(T)} != 4"
    Ch, Cu = hat(placed[h]), hat(placed[u])
    Ca = hat(placed[a])
    Cbu, Cba = wedge2(Ch, Cu), wedge2(Ch, Ca)

    # (OC-21): L_h = <C(h,u), C(h,a)> and C(h,u) in R, so L_h subseteq R is a
    # statement about the SPLIT-EDGE line alone.
    Lh, _dirs = OL.line_pencil(placed, nrm, h)
    noncol = not OW.collinear(Ch, Cu, Ca)
    assert in_span(Cbu, R), "(OC-12) FAILED: C(h,u) is not a relative twist"
    if noncol:
        assert rank([Cbu, Cba]) == 2 and len(span_basis(Lh + [Cbu, Cba])) == 2, \
            "(OC-21) FAILED: <C(h,u), C(h,a)> is not L_h"
        lsub = all(in_span(x, R) for x in Lh)
        assert lsub == in_span(Cba, R), \
            "(OC-21) FAILED: L_h subseteq R is not C(h,a) in R"
    else:
        lsub = all(in_span(x, R) for x in Lh)

    # (OC-20): the perp identity, and R^{perp_B} = <rho>.
    Tperp = perp_B(T)
    assert len(Tperp) == 2, f"dim T_u^{{perp_B}} = {len(Tperp)} != 2"
    dTb, dTpb = len(meet(T, beta)), len(meet(Tperp, beta))
    assert dTb == 1 + dTpb, \
        f"(OC-20) FAILED: dim(T cap beta) = {dTb} != 1 + {dTpb}"
    Rperp = perp_B(R)
    assert len(Rperp) == 1, f"dim R^{{perp_B}} = {len(Rperp)} != 1"
    rho = Rperp[0]
    dRb = len(meet(R, beta))
    assert dRb == 1 + dTb, "(OC-13) FAILED: dim(R cap beta) != 1 + dim(T cap beta)"
    assert (dRb == 3) == in_span(rho, beta), \
        "(OC-20) FAILED: dim(R cap beta) = 3 is not rho in beta"

    # (OC-20), the marked point: `p` is cut out by `B(rho, -)` on beta.
    row = {'side': side, 'dimRcapbeta': dRb, 'dimTcapbeta': dTb,
           'dimTperpcapbeta': dTpb, 'Lsub': lsub, 'noncol': noncol,
           'rho_null': klein(rho, rho) == 0, 'hubfree': OW.hub_free_end(d['Gp'], h)}
    if dRb == 2:
        p = OW.pencil_centre(beta, pts, meet(R, beta))
        prho = OW.pencil_centre(beta, pts, meet(perp_B([rho]), beta))
        assert rank([p, prho]) == 1, \
            "(OC-20) FAILED: the marked point is not rho's panel trace"
        if row['rho_null']:
            assert OW.klein_point_on(p, rho), \
                "(OC-20) FAILED: rho decomposable but p is off it"
        row['p_is_h'] = (rank([p, Ch]) == 1)
        assert row['p_is_h'] == lsub, "(OC-11) FAILED: L_h subseteq R vs p = pt(h)"
    return row


def check():
    print("== (OC-17)/(OC-20)/(OC-21) at chart points: POOL-OC ==")
    print(f"   POOL-OC: the 4 lambda.habitat_specs habitats x placement seeds "
          f"{CHECK_SEEDS.start}-{CHECK_SEEDS.stop - 1},")
    print("   accepted exactly as outerline.frame_at accepts them (target "
          "rank, dim R_a = 1,")
    print("   dim V_bc = 3, rank{C_i} = 4, closed-star ranks green).")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    nfr, rows, ledger, rig = 0, [], {}, {}
    for name, E, v, _cmp in LAM.HABITATS4:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        VH = sorted(verts_of(Hed), key=str)
        P = outer.companions4(Hed, b, c)[0]
        for seed in CHECK_SEEDS:
            d, why = OL.frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
            if d is None:
                continue
            nfr += 1
            s = stratum_numbers(E, v, Gp, d['placed'], a, b)
            st = outer.stratum_at(E, Gp, d['placed'], a, b)
            assert st is not None, "frame_at accepted an off-target-rank point"
            dimRa = st[1]
            # (OC-17), the identity -- exact, at the point, no genericity:
            assert dimRa == s['corankGp'] - s['s0'], \
                f"(OC-17) FAILED: dim R_a = {dimRa} != {s['corankGp']} - {s['s0']}"
            assert s['index'] == 0, f"{name}: index(G) = {s['index']} != 0"
            assert s['defGp'] == 0, f"{name}: def(G') = {s['defGp']} != 0"
            assert s['defshared'] == 4, \
                f"{name}: def(G - v) = {s['defshared']} != 4"
            assert s['corankGp'] == 1 + s['defGp'], \
                "corank(G') != index(G) + 1 + def(G')"
            # (OC-17), the OPEN form: both conditions are maximal-rank.
            assert s['rkp'] == s['tgt'], "not target rank"
            assert s['rk_sh'] == s['rows_sh'], \
                "s_0 = 0 is not `the shared rows are independent`"
            assert s['s0'] == 0 and dimRa == 1, "off the hard stratum"
            ledger[(s['index'], s['defGp'], s['corankGp'], s['s0'], dimRa)] = \
                ledger.get((s['index'], s['defGp'], s['corankGp'], s['s0'],
                            dimRa), 0) + 1
            for side in ('b', 'c'):
                w = weld_rigidity(d, side)
                k = (w['dimMot'], w['rigid'], w['dimW'], w['lam0'])
                rig[k] = rig.get(k, 0) + 1
                r = panel_row(d, side)
                if r is not None:
                    r['habitat'] = name
                    rows.append(r)
        print(f"   {name:14s} seeds {CHECK_SEEDS.start}-"
              f"{CHECK_SEEDS.stop - 1} done")
    print(f"\n   POOL-OC frames: {nfr}")
    print(f"   (index(G), def(G'), corank(G'), s_0, dim R_a) -> count: "
          f"{dict(sorted(ledger.items()))}")
    print("\n   (OC-18) at all "
          f"{2 * nfr} companion ends: (dim Mot(H/X), H/X rigid, dim W_i, "
          "lambda_i = 0) -> count:")
    for k in sorted(rig, key=str):
        print(f"       {k} : {rig[k]}")
    print("     the implication `H/X rigid ==> lambda_i != 0` is ASSERTED "
          "per end, not\n     observed as a rate; so is (OC-1)'s "
          "`lambda_i = 0 <=> dim W_i = 1`.")
    agg = {}
    for r in rows:
        k = (r['dimRcapbeta'], r['dimTcapbeta'], r['dimTperpcapbeta'],
             r['Lsub'], r['noncol'], r['rho_null'], r['hubfree'])
        agg[k] = agg.get(k, 0) + 1
    print(f"\n   degree-3-hub ends: {len(rows)} of {2 * nfr}")
    print("   (dim(R cap beta), dim(T cap beta), dim(T^perp cap beta), "
          "L_h subseteq R,\n    pt(h)/pt(u)/pt(a) non-collinear, rho "
          "B-isotropic, hub-neighbour-free) -> count:")
    for k in sorted(agg, key=str):
        print(f"       {k} : {agg[k]}")
    assert rows, "no degree-3 end in POOL-OC -- nothing was tested"
    print("\nCHECK OK.  dim R_a = corank(G') - s_0 exactly at every frame; "
          "with index(G) = 0\n  and def(G') = 0 that is dim R_a = 1 - s_0, so "
          "the hard stratum at target rank\n  is the intersection of TWO "
          "MAXIMAL-RANK loci -- Zariski OPEN in the chart.\n  At every "
          "degree-3 end: dim(T cap beta) = 1 + dim(T^{perp_B} cap beta), "
          "R^{perp_B}\n  is a line rho whose panel trace IS (OC-11)'s marked "
          "point p, and L_h subseteq R\n  is exactly C(h,a) in R -- x_1 has "
          "left the statement.")


# ---------------- --control: placements OFF Z -------------------------------

def control():
    print("== (OC-17)/(OC-19)'s controls: POOL-OZ ==")
    print(f"   POOL-OZ: theta(3,4,5) x placement seeds {CONTROL_SEEDS.start}-"
          f"{CONTROL_SEEDS.stop - 1}, UNFILTERED, plus")
    print("   ONE CONSTRUCTED point -- the (OC-14) hub slide ONTO C_0, "
          "rebuilt here.")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    from widened import place_pencil_general
    name, E, v, _cmp = LAM.HABITATS4[0]
    a, b, c, Gp, Hed = outer.split_data(E, v)
    VH = sorted(verts_of(Hed), key=str)
    P = outer.companions4(Hed, b, c)[0]
    print(f"   shape: {name}   split: {v}   ends: {b}, {c}   companion: {P}")
    hist, offZ, onZ = {}, 0, 0
    for seed in CONTROL_SEEDS:
        pl = place_pencil_general(Gp, random.Random(seed))
        if pl is None:
            hist['no placement'] = hist.get('no placement', 0) + 1
            continue
        placed = pl[0]
        s = stratum_numbers(E, v, Gp, placed, a, b)
        st = outer.stratum_at(E, Gp, placed, a, b)
        inZ = (st is not None and st[1] == 1)
        if st is not None:
            # the identity holds at EVERY target-rank placement, on or off Z:
            assert st[1] == s['corankGp'] - s['s0'], \
                f"(OC-17) FAILED off the filter: {st[1]} != " \
                f"{s['corankGp']} - {s['s0']}"
            assert (s['s0'] == 0) == (st[1] == 1), \
                "(OC-17) FAILED: dim R_a = 1 is not s_0 = 0 at target rank"
        key = ('target rank' if s['rkp'] == s['tgt'] else 'rank drop',
               'shared independent' if s['rk_sh'] == s['rows_sh']
               else 'shared dependent',
               None if st is None else st[1])
        hist[key] = hist.get(key, 0) + 1
        onZ, offZ = (onZ + 1, offZ) if inZ else (onZ, offZ + 1)
    print("   (rank R(G') maximal?, rank R(G-v) maximal?, dim R_a) -> count:")
    for k in sorted(hist, key=str):
        print(f"       {k} : {hist[k]}")
    print(f"     in Z: {onZ}    off Z: {offZ}")
    if offZ == 0:
        print("   BOUNDARY, stated as one: no SAMPLED placement of this "
              "pinned window falls off\n     Z, which is what an open dense "
              "Z predicts; the identity is asserted at every\n     placement "
              "reaching target rank, and the off-Z side is NOT exercised "
              "here.")

    # THE CONTROL THAT MATTERS FOR (OC-19): `Z != empty` alone does NOT give
    # (OC-8).  Rebuild (OC-14)'s slide ONTO C_0 and assert the landed point is
    # IN Z and has `L_b subseteq R_1` -- so Z genuinely meets the bad divisor,
    # and the argument must go through OPENNESS + density + one witness.
    print("\n   CONSTRUCTED: the (OC-14) hub slide ONTO C_0 (side b), "
          "deterministic targets.")
    nb = neighbors(Gp)
    landed = []
    for seed in CONTROL_SEEDS:
        d, _why = OL.frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
        if d is None:
            continue
        placed, nrm = d['placed'], d['nrm']
        h, inner, W = b, P[1], set(P[1:])
        if not OW.hub_free_end(Gp, h):
            continue
        others = sorted(set(neighbors(Hed)[h]) - {inner}, key=str)
        if len(others) != 1:
            continue
        T = OW.far_twist_space(Hed, placed, W, h, others[0], inner)
        beta, pts = OW.panel_line_space(placed, nrm, h)
        C0 = meet(T, beta)
        if len(C0) != 1:
            continue
        avoid = [placed[x] for x in nb[h]] + [placed[h]]
        on, _off = OW.slide_targets(beta, pts, C0[0], placed, nrm, h, avoid)
        for q in on:
            d2, why2 = OW.check_slid(E, v, P, a, b, c, Gp, Hed, VH,
                                     OW.slide_placement(placed, h, q), nrm, 'b')
            if d2 is None:
                continue
            # check_slid ACCEPTED it, so it is target rank with dim R_a = 1:
            assert d2['st'][1] == 1, "check_slid let an off-stratum point in"
            r = OW.wrench_row(d2, 'b')
            assert r['Lsub'], "the slide onto C_0 did not reach L_b subseteq R"
            pr = panel_row(d2, 'b')
            assert pr is not None and pr['Lsub'], "panel_row disagrees"
            # (OC-18)'s ADVERSARIAL WITNESS: a point of Z where `H/X` is
            # FLEXIBLE, so the open condition of (OC-18) must reject it.
            wr = weld_rigidity(d2, 'b')
            assert wr['lam0'] and not wr['rigid'] and wr['dimMot'] >= 7, \
                "(OC-18)'s guard did not reject the constructed bad point"
            landed.append((seed, d2['st'], r['Lsub'], r['coinc'],
                           d2['generic'], wr['dimMot'], wr['rigid']))
            break
        if len(landed) >= 3:
            break
    assert landed, "the constructed control did not land -- nothing tested"
    print("     (seed, (rank, dim R_a), L_b subseteq R_1, coincident hinge "
          "at b, star_generic,\n      dim Mot(H/X), H/X rigid):")
    for row in landed:
        print(f"       {row}")
    print(f"     landed: {len(landed)} constructed points, EVERY ONE in Z "
          f"with L_b subseteq R_1.")
    print("     So `Z != empty` does NOT imply (OC-8): Z meets the bad "
          "divisor, and the\n     reduction must run through OPENNESS of Z "
          "+ irreducibility + one witness.")
    print("\nCONTROL OK.")


def main():
    modes = {'--validate': validate, '--check': check, '--control': control}
    args = [x for x in sys.argv[1:] if x in modes]
    if not args:
        print(__doc__)
        print("pick one of: " + "  ".join(sorted(modes)))
        return
    for x in args:
        modes[x]()


if __name__ == '__main__':
    main()
