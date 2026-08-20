"""
Phase 39, section (K-out) CONTINUATION (direction OSCHU) -- (OC-19) input
(a)'s TARGET-RANK half (a_1) attacked class-uniformly, and the (a_2)
cross-pool re-keying leg.

WHY THIS DRIVER EXISTS.  `notes/Pencil-informal.md` section (K-out)
*Where this leaves input (a)* (direction ZNEQ, (OC-23)-(OC-28)) factors
input (a) into

  (a_2)  `H = G - v - a` has independent rows at some pencil chart point
         -- NECESSARY for `hK` at the shape ((OC-24)(ii)) and DOMINATED by
         section (K-grid) (GR-10) ((OC-28)(iii));
  (a_1)  at such a point the relative twist space
         `D = {m(b) - m(c) : m in Mot(H)}` contains no pencil `M^ ^ w`
         with `w` on the hub line `pt(b) pt(c)` -- measured to fail
         nowhere, but with NO RECIPE.

This pass supplies the recipe's first two links and names the residue.

  (OC-29) THE RULING DICTIONARY.  `M^ ^ W` -- `M^` the 2-space of the meet
    line `M = Pi(b) cap Pi(c)`, `W = <pt(b)^, pt(c)^>` that of the hub line
    -- is NOT a new object: it is `L_b (+) L_c`, the direct sum of section
    (K-out)'s own two hub pencils ((OC-3)'s `L_h`, `outerline.line_pencil`).
    Its Klein perp is the 2-space `Pi := <C(M), C(bc)>` spanned by the meet
    line and the hub line, so

        dim(D cap (M^ ^ W))  =  1 + dim(D^{perp_B} cap Pi),

    and the Klein form restricted to `M^ ^ W` is the DETERMINANT of the
    2 x 2 matrix picture `M^ (x) W`.  Consequently: `beta_b = <C(M)> (+)
    L_b`, `beta_b + beta_c` is the 5-space of section (K-tight) *Step 2*
    item 5 and `(beta_b + beta_c)^{perp_B} = <C(M)>` -- that item's own
    `*r || C(M)` criterion, re-derived inside this dictionary.

  (OC-30) THE EXACT BAD SET ON `M`.  With `K := D cap (M^ ^ W)` read as a
    space of 2 x 2 matrices (rows indexed by `M^`, columns by `W`):
    `pt(a) = q_t` is BAD (the chart point leaves `Z`) iff `K` contains a
    nonzero matrix of column space `<q_t>` -- equivalently iff `D` contains
    a LINE joining `q_t` to a point of the hub line.  So the bad set is the
    image of the DECOMPOSABLE elements of `K` under `x -> x cap M`, and the
    whole line `M` is bad iff `dim K >= 3` or `K` contains a ruling
    `M^ ^ w`.  This reproduces (OC-26)(ii) from a different route and
    refines it: OFF the all-bad case the bad set has at most 2 points, and
    it is EMPTY exactly when `K` carries no decomposable.

  (OC-31) `dim K <= 2` AT EVERY TARGET-RANK `G`-CHART POINT.  In `G`'s own
    chart `pt(v) in Pi(b)` and `pt(a) in Pi(c)` (each chain interior has
    exactly one hub neighbour), so `C(vb) in L_b` and `C(ac) in L_c`
    AUTOMATICALLY -- two lines of a common plane always meet.  Section
    (K-tight) *Step 2* item 1 at `(G, v, a, b)` with `corank R(G) = 0` says
    `D (+) <C(ac), C(va), C(vb)> = K^6`; hence `dim(D + L_b + L_c) >= 5`,
    i.e. `dim K <= 2`, and neither ruling `L_b`, `L_c` lies in `D`.  So the
    `dim K >= 3` disjunct of (OC-26)(ii) is KILLED by `hK`-at-a-point.

  (OC-32) THE THIRD GENERATOR IS STRUCTURALLY UNAVAILABLE.  `C(va)` is a
    transversal of `M` and `bc` at NO legal `G`-chart placement with target
    rank: forcing it makes `C(va)` equal to `C(vb)` (or to `C(ac)`), so the
    three generators collapse.  CONSTRUCTED here.  `dim K <= 2` is
    therefore exactly what this method yields.

  (OC-33) THE RESIDUE, IN THE ARC'S OWN OBJECT CLASS.  A ruling inside `D`
    is a 2-dimensional totally Klein-isotropic subspace of the 3-space `D`,
    so it forces `rank(Q|_D) <= 2`: the PITCH FORM on the relative twist
    space is degenerate.  Hence at a target-rank `G`-chart point

        rank(Q|_D) = 3   ==>   input (a) holds at that (shape, split),

    a single 3 x 3 determinant, one-point decidable, `x_1`-free,
    `lambda`-free, stratum-free.  Sufficiency is NOT necessity, and
    `--restate` constructs the separating witness.

  (OC-34) THE (a_2) RE-KEYING.  Section (K-grid)'s 907 certified shapes and
    section (K-out)'s class-shape population are labelled-instance pools
    with different keys ((OC-28)(a)).  `--rekey` keys both by the
    isomorphism class of the length-labelled hub multigraph and reports the
    containment, certifying every miss directly with `gridwit.tree_triple`.

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --restate
    PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --gtarget
    PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --rekey

POOLS, pinned and disjoint from every earlier pool of this section
(POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A / POOL-W / POOL-SL /
POOL-OV / POOL-OC / POOL-OZ / POOL-ZF / POOL-ZQ / POOL-ZN / POOL-ZT /
POOL-ZR).  Nothing below is aggregated with any of them.

  POOL-OS (`--restate`) -- the 4 `lambda.habitat_specs` habitats x every
    eligible split x placement seeds 600-603 of `G'`, UNFILTERED, guard-
    accepted through `outer.chart_point`.  A derivation pool: every
    sentence under test is an identity, so it is a witness set and NO
    figure from it is a rate.
  POOL-OQ (`--restate`) -- synthetic exact-Q subspaces of `Lambda^2 K^4`
    from `random.Random(20260820)`, plus SIX constructed configurations
    covering `dim K = 0..4` and the sufficiency-is-not-necessity witness,
    plus 60 negative controls.  No graph, no placement.
  POOL-OG (`--gtarget`) -- the 4 habitats x every eligible split x
    placement seeds 700-711 of the WHOLE graph `G` (not `G'`), guard-
    accepted for `G` by `repin.star_generic` + `verify_pencil_witness`.
    Plus, per (shape, split), the two CONSTRUCTED (OC-32) placements.
  POOL-OR (`--rekey`) -- section (K-out)'s class-shape population
    (`outer.named_inventory()` + every shape of `outer.sweep_shapes()`)
    keyed against section (K-grid)'s `grid.census_shapes()`.  Purely
    combinatorial; `sweep_shapes`' own caps are disclosed in the output and
    every count is a LABELLED-INSTANCE count (README section 4
    convention 7).

(OC-7) RULE.  No figure here is a rate, and none is evidence about a
generic chart point; POOL-G / POOL-S are neither re-sampled nor extended.

LAYERING (`notes/scripts/README.md` section 2).  A `w4/` leaf ABOVE `zneq`,
which it imports read-only (`u_space`, `corank_at`, `ledger`,
`schubert_data`, `bad_t_polys`, `poly_gcd`, `meet_param_of`) together with
`ocon` (`meet`, `perp_B`), `outerline` (`line_pencil`, `weld_motions`,
`rel_span`), `outer` (`split_data`, `eligible_splits`, `named_inventory`,
`sweep_shapes`, `chart_point`, `stratum_at`, `panel_frame`, `companions4`),
`grid` (`census_shapes`, `block_data`, `colourings`, `combinatorial_filter`,
`cycle_rank`, `rank_at_params`, `TRIES_SEED`), `gridwit` (`tree_triple`),
`nogood_subdiv` (`deficiency`, `branch_decomposition`, `hub_set`),
`widened` (`place_pencil_general`), `flanks` and catalogued section-1
primitives.  NOTHING EXISTING IS MODIFIED.

HARNESS DEBT, recorded not paid (this pass may not modify a landed file).
  * `ocon.meet` now has a THIRD consumer (OCON, ZNEQ, this pass) --
    section-2 rule 2's move-down trigger, first recorded by ZNEQ
    2026-08-19; RE-DATED here, still UNPAID.
  * `zneq.u_space` / `bad_t_polys` / `poly_gcd` / `corank_at` /
    `schubert_data` / `meet_param_of` each gain a SECOND consumer with this
    pass -- the same trigger, a NEW unpaid item.
  * `gridwit.tree_triple` gains a SECOND consumer -- same trigger, new
    unpaid item.
"""
import importlib
import random
import sys
import time
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, hat, nullspace, rank, wedge2            # noqa: E402
from kbare_common import (verify_pencil_witness, verts_of)         # noqa: E402
from nogood_subdiv import (branch_decomposition, deficiency,       # noqa: E402
                           hub_set)
from pitch import Q, klein                                        # noqa: E402
from repin import in_span, span_basis, star_generic               # noqa: E402
from widened import place_pencil_general                          # noqa: E402
import outer                                                       # noqa: E402
import outerline as OL                                             # noqa: E402
import ocon                                                        # noqa: E402
import zneq                                                        # noqa: E402

LAM = importlib.import_module('lambda')

RESTATE_SEEDS = range(600, 604)
GTARGET_SEEDS = range(700, 712)
SYNTH_SEED = 20260820


# ---------------- (OC-29): the ruling dictionary ----------------------------

def ruling_data(placed, nrm, b, c):
    """(OC-29) at one chart point.  Returns a dict carrying

      Mhat  a basis of the meet line's 2-space `M^`  (hat(M0), (Md, 0))
      W     a basis of the hub line's 2-space        (hat(pt b), hat(pt c))
      Lb    `L_b` = the pencil of lines through `pt(b)` in `Pi(b)`
      Lc    `L_c` likewise at `c`
      MW    a basis of `M^ ^ W`
      CM    the meet line's Plucker point, Cbc the hub line's
      Pi    a basis of `<C(M), C(bc)> = (M^ ^ W)^{perp_B}`

    and ASSERTS every identity (OC-29) claims: the dimensions, the ruling
    decomposition `M^ ^ W = L_b (+) L_c`, the perp identity, the two panel
    identities `beta_h = <C(M)> (+) L_h`, the 5-space `beta_b + beta_c` of
    section (K-tight) *Step 2* item 5 and its Klein perp `<C(M)>`."""
    fr = outer.panel_frame(placed, nrm, b, c)
    assert fr is not None, "panels parallel at a chart point"
    M0, Md, CM = fr
    Mhat = [hat(M0), [Md[0], Md[1], Md[2], F(0)]]
    assert rank(Mhat) == 2, "the meet-line 2-space is degenerate"
    pb, pc = hat(placed[b]), hat(placed[c])
    W = [pb, pc]
    assert rank(W) == 2, "the hub-line 2-space is degenerate"
    assert rank(Mhat + W) == 4, \
        "(Lambda-0d) FAILS: M^ and W are not complementary in K^4"
    Cbc = wedge2(pb, pc)
    MW = span_basis([wedge2(q, w) for q in Mhat for w in W])
    assert len(MW) == 4, f"M^ ^ W is {len(MW)}-dimensional, not 4"
    Lb, _db = OL.line_pencil(placed, nrm, b)
    Lc, _dc = OL.line_pencil(placed, nrm, c)
    # (OC-29)(i): the ruling decomposition M^ ^ W = L_b (+) L_c
    assert rank(list(Lb) + list(Lc)) == 4, "L_b + L_c is not 4-dimensional"
    assert rank(list(MW) + list(Lb) + list(Lc)) == 4, \
        "(OC-29)(i) FAILED: M^ ^ W != L_b (+) L_c"
    # L_b IS the ruling M^ ^ pt(b)^, elementwise
    for lb in Lb:
        assert in_span(lb, [wedge2(q, pb) for q in Mhat]), \
            "(OC-29)(i) FAILED: L_b is not the ruling M^ ^ pt(b)^"
    for lc in Lc:
        assert in_span(lc, [wedge2(q, pc) for q in Mhat]), \
            "(OC-29)(i) FAILED: L_c is not the ruling M^ ^ pt(c)^"
    # (OC-29)(ii): the Klein perp of M^ ^ W is <C(M), C(bc)>
    Pi = ocon.perp_B(MW)
    assert len(Pi) == 2, "the perp of a 4-space is not 2-dimensional"
    assert rank([CM, Cbc]) == 2 and rank(list(Pi) + [CM, Cbc]) == 2, \
        "(OC-29)(ii) FAILED: (M^ ^ W)^{perp_B} != <C(M), C(bc)>"
    assert Q(CM) == 0 and Q(Cbc) == 0, "a line has nonzero pitch"
    assert klein(CM, Cbc) != 0, \
        "C(M) and C(bc) are Klein-orthogonal: the two lines MEET"
    # (OC-29)(iii): the panel identities, and (K-tight) *Step 2* item 5
    beta_b = span_basis([wedge2(x, y) for x in Mhat + [pb]
                         for y in Mhat + [pb]])
    beta_c = span_basis([wedge2(x, y) for x in Mhat + [pc]
                         for y in Mhat + [pc]])
    assert len(beta_b) == 3 and len(beta_c) == 3, "beta_h is not 3-dimensional"
    assert rank(list(beta_b) + [CM] + list(Lb)) == 3, \
        "(OC-29)(iii) FAILED: beta_b != <C(M)> (+) L_b"
    assert rank(list(beta_b) + list(beta_c)) == 5, \
        "beta_b + beta_c is not the 5-space of (K-tight) *Step 2* item 5"
    rad = ocon.perp_B(list(beta_b) + list(beta_c))
    assert len(rad) == 1 and rank([rad[0], CM]) == 1, \
        "(OC-29)(iii) FAILED: (beta_b + beta_c)^{perp_B} != <C(M)>"
    return dict(M0=M0, Md=Md, Mhat=Mhat, W=W, Lb=Lb, Lc=Lc, MW=MW,
                CM=CM, Cbc=Cbc, Pi=Pi, beta_b=beta_b, beta_c=beta_c)


def mw_coords(x, rd):
    """The 2 x 2 matrix of `x in M^ ^ W` in the basis `Mhat[i] ^ W[j]`, rows
    indexed by `M^`, columns by `W`.  Asserts `x` really is in `M^ ^ W` and
    that the reconstruction is exact."""
    basis = [wedge2(rd['Mhat'][i], rd['W'][j]) for i in range(2)
             for j in range(2)]
    sol = nullspace([[basis[k][r] for k in range(4)] + [x[r]]
                     for r in range(6)])
    assert len(sol) == 1, "x is not in M^ ^ W (or the basis is degenerate)"
    v = sol[0]
    assert v[4] != 0, "the reconstruction is degenerate"
    co = [-v[k] / v[4] for k in range(4)]
    for r in range(6):
        assert sum(co[k] * basis[k][r] for k in range(4)) == x[r], \
            "the M^ (x) W reconstruction is not exact"
    return [[co[0], co[1]], [co[2], co[3]]]


def det2(X):
    return X[0][0] * X[1][1] - X[0][1] * X[1][0]


def check_det_is_pitch(rd):
    """(OC-29)(iv): `Q` restricted to `M^ ^ W` is the DETERMINANT of the
    2 x 2 picture, up to one nonzero scalar -- asserted on a basis and on
    two off-basis vectors."""
    basis = [wedge2(rd['Mhat'][i], rd['W'][j]) for i in range(2)
             for j in range(2)]
    lam = None
    tests = [(basis[0], [[F(1), F(0)], [F(0), F(0)]]),
             (basis[1], [[F(0), F(1)], [F(0), F(0)]]),
             (basis[2], [[F(0), F(0)], [F(1), F(0)]]),
             (basis[3], [[F(0), F(0)], [F(0), F(1)]])]
    for i in range(4):
        for j in range(i + 1, 4):
            s = [basis[i][r] + basis[j][r] for r in range(6)]
            Xi, Xj = tests[i][1], tests[j][1]
            X = [[Xi[r][cc] + Xj[r][cc] for cc in range(2)] for r in range(2)]
            tests.append((s, X))
    for x, X in tests:
        d, q = det2(X), Q(x)
        if d == 0:
            assert q == 0, "(OC-29)(iv) FAILED: det = 0 but Q != 0"
            continue
        r = q / d
        if lam is None:
            lam = r
            assert lam != 0, "(OC-29)(iv) FAILED: Q vanishes on M^ ^ W"
        assert r == lam, "(OC-29)(iv) FAILED: Q|_{M^ ^ W} is not prop. to det"
    return lam


# ---------------- (OC-30): the exact bad set on M ---------------------------

def bad_set(D, rd):
    """(OC-30): the bad set on `M`, EXACTLY, from `K = D cap (M^ ^ W)`.

    Returns `(kind, data, dimK, Kmats)` with `kind` one of
      'none'  -- no point of `M` is bad; `data = []`
      'finite'-- `data` = the bad parameters, as `t` values with `None`
                 standing for the point at infinity `q = Mhat[1]`
      'all'   -- every point of `M` is bad.
    `Kmats` are the 2 x 2 pictures of a basis of `K`.

    Method: `q_t = Mhat[0] + t Mhat[1]` is bad iff `K cap (q_t (x) W) != 0`,
    and `q_t (x) W` consists ENTIRELY of decomposables, so this is exactly
    "`D` contains a line joining `q_t` to a point of the hub line"."""
    K = ocon.meet(D, rd['MW']) if D else []
    dimK = len(K)
    Kmats = [mw_coords(x, rd) for x in K]
    if dimK == 0:
        return 'none', [], dimK, Kmats
    if dimK >= 3:
        return 'all', [], dimK, Kmats
    if dimK == 1:
        X = Kmats[0]
        if det2(X) != 0:
            return 'none', [], dimK, Kmats
        # rank 1: the column space is a single point of P(M^)
        col = ([X[0][0], X[1][0]] if (X[0][0], X[1][0]) != (F(0), F(0))
               else [X[0][1], X[1][1]])
        assert (col[0], col[1]) != (F(0), F(0)), "a nonzero matrix with no column"
        return 'finite', [None if col[0] == 0 else col[1] / col[0]], dimK, Kmats
    # dimK == 2: badness at t is a single quadratic in t.  q_t (x) W is
    # spanned by (q_t, 0) and (0, q_t) in the 2 x 2 picture, so the 4 x 4
    # determinant of [K basis; q_t (x) W] is a polynomial of degree <= 2.
    def flat(X):
        return [X[0][0], X[0][1], X[1][0], X[1][1]]

    def dett(t):
        q = [F(1), t]
        rows = [flat(Kmats[0]), flat(Kmats[1]),
                flat([[q[0], F(0)], [q[1], F(0)]]),
                flat([[F(0), q[0]], [F(0), q[1]]])]
        return det4x4(rows)
    vals = [dett(F(k)) for k in (0, 1, 2, 3)]
    # interpolate a degree-<=2 polynomial through t = 0, 1, 2 and CHECK t = 3
    c0 = vals[0]
    c2 = (vals[2] - 2 * vals[1] + vals[0]) / 2
    c1 = vals[1] - c0 - c2
    assert c0 + 3 * c1 + 9 * c2 == vals[3], \
        "the badness determinant is not quadratic in t"
    if (c0, c1, c2) == (F(0), F(0), F(0)):
        return 'all', [], dimK, Kmats
    roots = []
    if c2 == 0:
        if c1 != 0:
            roots.append(-c0 / c1)
        # the point at infinity is bad iff the leading coefficient vanishes
        roots.append(None)
    else:
        disc = c1 * c1 - 4 * c2 * c0
        s = isqrt_exact(disc)
        if s is not None:
            roots.append((-c1 + s) / (2 * c2))
            if s != 0:
                roots.append((-c1 - s) / (2 * c2))
    return 'finite', roots, dimK, Kmats


def det4x4(rows):
    """Exact 4 x 4 determinant by cofactor expansion (four rows of length 4)."""
    def det3(m):
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
                - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
    tot = F(0)
    for j in range(4):
        minor = [[rows[i][k] for k in range(4) if k != j] for i in (1, 2, 3)]
        tot += (-1) ** j * rows[0][j] * det3(minor)
    return tot


def isqrt_exact(x):
    """The exact rational square root of `x >= 0`, or None when it is not a
    rational square (then the two bad points are irrational -- they exist in
    an extension but not on the Q-chart, which is stated where used)."""
    if x < 0:
        return None
    n, d = x.numerator, x.denominator
    rn, rd = int(round(n ** 0.5)), int(round(d ** 0.5))
    for cn in (rn - 2, rn - 1, rn, rn + 1, rn + 2):
        for cd in (rd - 2, rd - 1, rd, rd + 1, rd + 2):
            if cn >= 0 and cd > 0 and F(cn, cd) ** 2 == x:
                return F(cn, cd)
    return None


def pitch_rank(D):
    """`rank(Q|_D)` -- the rank of the Gram matrix of the Klein form on `D`.
    `rank = dim D` iff `D cap D^{perp_B} = 0`."""
    G = [[klein(u, w) for w in D] for u in D]
    r = rank(G)
    rad = ocon.meet(D, ocon.perp_B(D)) if D else []
    assert r == len(D) - len(rad), \
        "the Gram rank disagrees with dim(D cap D^{perp_B})"
    return r


def has_ruling(Kmats):
    """Does `K` contain a ruling `M^ ^ w` (a 2-space of FIXED W-direction,
    i.e. of fixed matrix ROW space)?  Decided exactly: `K` contains
    `{u w^T : u}` iff both `w`-columns of ... -- concretely, iff `K`
    contains two independent matrices `u_1 w^T`, `u_2 w^T` with the same
    `w`, which for `dim K = 2` means every element of `K` is rank <= 1 with
    a common row space, and for `dim K >= 3` is tested by the same span
    computation."""
    if len(Kmats) < 2:
        return False
    # a ruling M^ ^ w = {u w^T} is spanned by e_1 w^T, e_2 w^T; so K
    # contains it iff there is a nonzero w with both e_i w^T in K.
    # Solve for w in K^2: e_1 w^T in span(K) and e_2 w^T in span(K).
    def flat(X):
        return [X[0][0], X[0][1], X[1][0], X[1][1]]
    Kf = [flat(X) for X in Kmats]
    # complement functionals: rows f with f . Kf = 0
    perp = nullspace(Kf)          # basis of {f : sum f_k X_k = 0 for X in K}
    # e_1 w^T has flat (w0, w1, 0, 0); e_2 w^T has (0, 0, w0, w1).
    rows = []
    for f in perp:
        rows.append([f[0], f[1]])
        rows.append([f[2], f[3]])
    if not rows:
        return True               # K is everything
    return len(nullspace(rows)) > 0


# ---------------- --restate: (OC-29)/(OC-30), POOL-OS + POOL-OQ ------------

def restate():
    print("== (OC-29)/(OC-30): the ruling dictionary and the exact bad set, "
          "POOL-OS ==")
    print(f"   POOL-OS: the 4 lambda.habitat_specs habitats x every eligible "
          f"split x placement\n            seeds {RESTATE_SEEDS.start}-"
          f"{RESTATE_SEEDS.stop - 1} of `G'`, UNFILTERED (no target-rank / "
          f"stratum filter) but\n            guard-accepted through "
          f"outer.chart_point (repin.star_generic +\n            "
          f"verify_pencil_witness).  A derivation pool: NO figure is a rate.")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    hist, nfr, nrej, nsplit = {}, 0, 0, 0
    lam_vals = set()
    t0 = time.time()
    for name, E, _v0, _cmp in LAM.HABITATS4:
        for v in outer.eligible_splits(E):
            a, b, c, Gp, Hed = outer.split_data(E, v)
            Vp = sorted(verts_of(Gp), key=str)
            VH = sorted(verts_of(Hed), key=str)
            dfp = deficiency(Gp)
            nsplit += 1
            for seed in RESTATE_SEEDS:
                cp = outer.chart_point(Gp, random.Random(seed))
                if cp is None:
                    nrej += 1
                    continue
                placed, _pt, nrm = cp
                d = zneq.ledger(E, v, a, b, c, Gp, Hed, placed, Vp, VH, dfp)
                nfr += 1
                rd = ruling_data(placed, nrm, b, c)
                lam_vals.add(check_det_is_pitch(rd) != 0)
                if d['sigma'] != 0:
                    hist[('sigma != 0', d['sigma'])] = \
                        hist.get(('sigma != 0', d['sigma']), 0) + 1
                    continue
                D = span_basis(nullspace(d['U']))
                assert len(D) == 3, "dim D != 3 at a sigma = 0 frame"
                # (OC-29)(v): dimK = 1 + dim(D^{perp_B} cap <C(M), C(bc)>)
                T = ocon.perp_B(D)
                assert len(T) == 3, "the transmitted-wrench space is not 3-dim"
                sd = zneq.schubert_data(d['U'], rd['Mhat'], rd['W'])
                inter = ocon.meet(T, rd['Pi'])
                assert sd['dimK'] == 1 + len(inter), \
                    "(OC-29)(v) FAILED: dimK != 1 + dim(T cap Pi)"
                # (OC-30): the bad set, MY route
                kind, roots, dimK, Kmats = bad_set(D, rd)
                assert dimK == sd['dimK'], "two dimK routes disagree"
                assert has_ruling(Kmats) == sd['pencil'], \
                    "the ruling test disagrees with zneq.schubert_data"
                # ... against ZNEQ's INDEPENDENT Q[t]-GCD route
                polys = zneq.bad_t_polys(d['U'], rd['M0'], rd['Md'],
                                         placed[b], placed[c])
                g = zneq.poly_gcd(polys)
                if not g:
                    assert kind == 'all', \
                        "(OC-30) FAILED: GCD identically zero but bad set " \
                        "is not all of M"
                else:
                    assert kind != 'all', \
                        "(OC-30) FAILED: bad set called all of M but the " \
                        "GCD is nonzero"
                    gr = [r for r in roots if r is not None]
                    for r in gr:
                        assert sum(g[k] * r ** k
                                   for k in range(len(g))) == 0, \
                            "(OC-30) FAILED: a predicted bad t is not a " \
                            "root of the minors' GCD"
                    assert len(g) - 1 == len(gr) or len(g) - 1 > len(gr), \
                        "more predicted bad points than the GCD has roots"
                # (OC-29)(v), literally: <C(ab), C(ac)> IS the ruling
                # `pt(a)^ ^ W` of the OTHER kind, and Z-membership is exactly
                # "C(ab), C(ac) independent mod D".
                Cab = wedge2(hat(placed[a]), hat(placed[b]))
                Cac = wedge2(hat(placed[a]), hat(placed[c]))
                other = span_basis([wedge2(hat(placed[a]), w)
                                    for w in rd['W']])
                assert len(other) == 2 and \
                    rank([Cab, Cac] + other) == 2, \
                    "(OC-29)(v) FAILED: <C(ab), C(ac)> != pt(a)^ ^ W"
                assert (rank(list(D) + [Cab, Cac]) == 5) == d['inZ'], \
                    "(OC-29)(v) FAILED: Z-membership is not 'C(ab), C(ac) " \
                    "independent mod D'"
                # the sampled pt(a) agrees with Z-membership
                ta = zneq.meet_param_of(placed, rd['M0'], rd['Md'], a)
                assert ta is not None, "pt(a) is OFF the meet line"
                pred_bad = (kind == 'all' or
                            (kind == 'finite' and ta in
                             [r for r in roots if r is not None]))
                assert pred_bad == (not d['inZ']), \
                    "(OC-30) FAILED: the predicted goodness of the sampled " \
                    "t disagrees with Z-membership"
                pr = pitch_rank(D)
                # (OC-33): rank(Q|_D) = 3 ==> no ruling in D
                if pr == 3:
                    assert not has_ruling(Kmats), \
                        "(OC-33) FAILED: rank(Q|_D) = 3 with a ruling in D"
                key = (dimK, kind, len(roots), pr, sd['pencil'],
                       (len(g) - 1) if g else 'all-zero')
                hist[key] = hist.get(key, 0) + 1
    print(f"   splits probed: {nsplit};  chart points accepted: {nfr};  "
          f"draws rejected by the guards: {nrej}"
          f"   [{time.time() - t0:.0f} s]")
    print("   (dimK, bad set, #bad points, rank(Q|_D), ruling in D?, "
          "deg GCD) -> count:")
    for k in sorted(hist, key=str):
        print(f"       {k} : {hist[k]}")
    print("   asserted per frame: (OC-29)(i) M^ ^ W = L_b (+) L_c, "
          "elementwise; (ii) its Klein perp\n     = <C(M), C(bc)>; (iii) "
          "beta_b = <C(M)> (+) L_b, beta_b + beta_c 5-dimensional with\n"
          "     Klein perp <C(M)> -- (K-tight) *Step 2* item 5's own object; "
          "(iv) Q|_{M^ ^ W} prop.\n     to det; (v) dimK = 1 + "
          "dim(D^{perp_B} cap <C(M), C(bc)>); and (OC-30)'s bad set\n"
          "     against ZNEQ's INDEPENDENT Q[t]-GCD route and against the "
          "sampled point's\n     Z-membership; and (v) in its literal form "
          "-- <C(ab), C(ac)> = pt(a)^ ^ W, and\n     Z-membership == "
          "'C(ab), C(ac) independent mod D'.")
    assert lam_vals == {True}, "Q|_{M^ ^ W} degenerated somewhere"
    synthetic()
    print("\nRESTATE OK.")


def synthetic():
    """POOL-OQ: (OC-30)'s classification CONSTRUCTED across every value of
    `dim K`, plus the (OC-33) sufficiency-is-not-necessity witness, plus 60
    negative controls (README section 4 convention 6)."""
    print("\n   POOL-OQ: (OC-30)'s classification CONSTRUCTED, at every "
          "attainable dimK (>= 1\n     always, since dim D + dim(M^ ^ W) = "
          "3 + 4 > 6).")
    print(f"     rng: random.Random({SYNTH_SEED}); no graph, no placement.")
    rng = random.Random(SYNTH_SEED)
    e = [[F(1) if k == i else F(0) for k in range(4)] for i in range(4)]
    P0, Pd, pb, pc = e[0], e[1], e[2], e[3]
    rd = {'Mhat': [P0, Pd], 'W': [pb, pc],
          'MW': span_basis([wedge2(q, w) for q in (P0, Pd)
                            for w in (pb, pc)]),
          'M0': None, 'Md': None,
          'CM': wedge2(P0, Pd), 'Cbc': wedge2(pb, pc)}
    rd['Pi'] = ocon.perp_B(rd['MW'])
    assert len(rd['MW']) == 4 and len(rd['Pi']) == 2, "synthetic frame broken"
    lam = check_det_is_pitch(rd)
    print(f"     Q|_{{M^ ^ W}} = {lam} * det on the constructed frame "
          f"(OC-29)(iv)")

    def mat(X):
        """The element of M^ ^ W with 2 x 2 picture X."""
        bs = [wedge2(P0, pb), wedge2(P0, pc), wedge2(Pd, pb), wedge2(Pd, pc)]
        co = [X[0][0], X[0][1], X[1][0], X[1][1]]
        return [sum(co[k] * bs[k][r] for k in range(4)) for r in range(6)]

    def rand_out(n=1):
        """`n` vectors of `Lambda^2 K^4` OFF `M^ ^ W`, independent of it.
        `n <= 2`: `dim(M^ ^ W) = 4`, so at most 2 further directions fit --
        which is the reason `dim K >= 1` ALWAYS (3 + 4 - 6 = 1) and `dim K =
        0` is not a case at all."""
        assert n <= 2, "dim K >= 1 always: no room for a third direction"
        out = []
        while len(out) < n:
            x = [F(rng.randint(-6, 6)) for _ in range(6)]
            if rank(rd['MW'] + out + [x]) == 4 + len(out) + 1:
                out.append(x)
        return out

    cases = []
    # CASE 2: dimK = 1, generator NONSINGULAR.  Bad set EMPTY -- the
    # measured generic behaviour, and the reason the whole line is good.
    X = [[F(1), F(0)], [F(0), F(1)]]
    D = span_basis([mat(X)] + rand_out(2))
    cases.append(('dimK=1 nonsingular', D, 'none', False))
    # CASE 3: dimK = 1, generator RANK 1.  Exactly ONE bad point.
    X = [[F(1), F(2)], [F(0), F(0)]]
    D = span_basis([mat(X)] + rand_out(2))
    cases.append(('dimK=1 rank 1', D, 'finite1', False))
    # CASE 4: dimK = 2 = a RULING M^ ^ w.  The whole line M is bad.
    w = [pc[k] - 2 * pb[k] for k in range(4)]
    penc = [wedge2(P0, w), wedge2(Pd, w)]
    D = span_basis(penc + rand_out(1))
    cases.append(('dimK=2 ruling', D, 'all', True))
    # CASE 5: dimK = 2 but ANISOTROPIC over Q -- no decomposable at all, so
    # the bad set is EMPTY even though dimK = 2.  This is the witness that
    # (OC-33)'s `rank(Q|_D) = 3` is SUFFICIENT and NOT NECESSARY: here
    # rank(Q|_D) may be full, but the point is that dimK = 2 alone does not
    # make the line bad.
    X1 = [[F(1), F(0)], [F(0), F(1)]]
    X2 = [[F(0), F(-1)], [F(1), F(0)]]
    D = span_basis([mat(X1), mat(X2)] + rand_out(1))
    cases.append(('dimK=2 anisotropic/Q', D, 'finite0', False))
    # CASE 6: dimK = 3, a NONSINGULAR hyperplane of M^ ^ W -- no ruling
    # inside, and yet EVERY point of M is bad.  (ZNEQ's Case C, recovered
    # from the classification rather than assumed.)
    Ks = [mat([[F(1), F(0)], [F(0), F(-1)]]), mat([[F(0), F(1)], [F(0), F(0)]]),
          mat([[F(0), F(0)], [F(1), F(0)]])]
    D = span_basis(Ks)
    cases.append(('dimK=3 no ruling', D, 'all', False))
    # CASE 7: the (OC-33) separation, CONSTRUCTED -- rank(Q|_D) <= 2 WITHOUT
    # a ruling in D, so the sufficient condition of (OC-33) fails while the
    # bad set is still FINITE.  Built by putting the decomposable generator
    # of `K` into the RADICAL: `D` inside `x^{perp_B}` forces `x` in
    # `D cap D^{perp_B}`, hence `rank(Q|_D) <= 2`.
    x = mat([[F(1), F(2)], [F(0), F(0)]])
    assert Q(x) == 0, "the constructed K-generator is not decomposable"
    xp = ocon.perp_B([x])
    assert len(xp) == 5 and rank(xp + [x]) == 5, "x is not in x^{perp_B}"
    D = None
    for _ in range(3000):
        co = [[F(rng.randint(-6, 6)) for _ in range(5)] for _ in range(2)]
        cand = span_basis([x] + [[sum(co[i][k] * xp[k][r] for k in range(5))
                                 for r in range(6)] for i in range(2)])
        if len(cand) != 3:
            continue
        if rank(list(cand) + list(rd['MW'])) != 6:
            continue          # dim K must stay 1
        if pitch_rank(cand) <= 2:
            k2, r2, d2, Km2 = bad_set(cand, rd)
            if k2 == 'finite' and not has_ruling(Km2):
                D = cand
                break
    assert D is not None, "the (OC-33) separating witness was not constructed"
    cases.append(('rank(Q|_D)<=2, no ruling', D, 'finite1', False))
    for label, D, want, want_ruling in cases:
        assert len(D) == 3, f"{label}: D is not 3-dimensional"
        kind, roots, dimK, Kmats = bad_set(D, rd)
        nfin = len([r for r in roots if r is not None])
        got = ('finite%d' % nfin) if kind == 'finite' else kind
        assert got == want, \
            f"{label}: bad set is {got}, expected {want}"
        assert has_ruling(Kmats) == want_ruling, \
            f"{label}: ruling test = {has_ruling(Kmats)}, expected " \
            f"{want_ruling}"
        pr = pitch_rank(D)
        if want_ruling:
            assert pr <= 2, \
                f"{label}: a ruling inside D with rank(Q|_D) = 3 -- " \
                "(OC-33) is FALSE"
        print(f"     {label:26s} dimK={dimK}  bad={kind}"
              f"{'' if kind != 'finite' else ' (%d pts)' % len(roots)}"
              f"  ruling={has_ruling(Kmats)}  rank(Q|_D)={pr}")
    # 60 negative controls: random 3-spaces, the generic behaviour these
    # seven constructions must be read against.
    ctrl = {}
    for _ in range(60):
        while True:
            D = span_basis([[F(rng.randint(-9, 9)) for _ in range(6)]
                            for _ in range(3)])
            if len(D) == 3:
                break
        kind, roots, dimK, Kmats = bad_set(D, rd)
        pr = pitch_rank(D)
        key = (dimK, kind, has_ruling(Kmats), pr)
        ctrl[key] = ctrl.get(key, 0) + 1
    print("     60 negative controls (dimK, bad set, ruling?, rank(Q|_D)):")
    for k in sorted(ctrl, key=str):
        print(f"       {k} : {ctrl[k]}")
    assert all(k[0] == 1 and k[1] == 'none' and not k[2] and k[3] == 3
               for k in ctrl), \
        "a random 3-space was not generic -- the controls are contaminated"


# ---------------- --gtarget: (OC-31)/(OC-32), POOL-OG ----------------------

def gtarget():
    print("== (OC-31)/(OC-32): dimK <= 2 at every target-rank G-chart point, "
          "POOL-OG ==")
    print(f"   POOL-OG: the 4 lambda.habitat_specs habitats x every eligible "
          f"split x placement\n            seeds {GTARGET_SEEDS.start}-"
          f"{GTARGET_SEEDS.stop - 1} of the WHOLE graph `G` (not of `G'`), "
          f"guard-accepted for `G` by\n            repin.star_generic + "
          f"verify_pencil_witness.  Plus, per (shape, split), the\n"
          f"            two CONSTRUCTED (OC-32) placements.")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    hist, ntgt, noff, ncon = {}, 0, 0, 0
    nskip = [0]
    t0 = time.time()
    for name, E, _v0, _cmp in LAM.HABITATS4:
        VG = sorted(verts_of(E), key=str)
        tgtG = 6 * (len(VG) - 1) - deficiency(E)
        for v in outer.eligible_splits(E):
            a, b, c, Gp, Hed = outer.split_data(E, v)
            VH = sorted(verts_of(Hed), key=str)
            done_con = False
            for seed in GTARGET_SEEDS:
                pl = place_pencil_general(E, random.Random(seed))
                if pl is None:
                    continue
                placed, _pt, nrm, _hubs, _nb = pl
                if not star_generic(E, placed):
                    continue
                okG, _i = verify_pencil_witness(E, placed)
                if not okG:
                    continue
                if outer.panel_frame(placed, nrm, b, c) is None or \
                        not outer.lam0d(placed, nrm, b, c):
                    nskip[0] += 1
                    continue
                ckG, rkG = zneq.corank_at(E, placed, VG)
                sigma, _r = zneq.corank_at(Hed, placed, VH)
                rd = ruling_data(placed, nrm, b, c)
                # (OC-31)'s STRUCTURAL input: each chain interior has exactly
                # one hub neighbour, so pt(v) in Pi(b) and pt(a) in Pi(c).
                assert dot(nrm[b], [placed[v][k] - placed[b][k]
                                    for k in range(3)]) == 0, \
                    "(OC-31) FAILED: pt(v) is NOT in the panel Pi(b)"
                assert dot(nrm[c], [placed[a][k] - placed[c][k]
                                    for k in range(3)]) == 0, \
                    "(OC-31) FAILED: pt(a) is NOT in the panel Pi(c)"
                Cvb = wedge2(hat(placed[v]), hat(placed[b]))
                Cac = wedge2(hat(placed[a]), hat(placed[c]))
                Cva = wedge2(hat(placed[v]), hat(placed[a]))
                # ... hence C(vb) in L_b and C(ac) in L_c, AUTOMATICALLY
                assert in_span(Cvb, rd['Lb']), \
                    "(OC-31) FAILED: C(vb) is not in the hub pencil L_b"
                assert in_span(Cac, rd['Lc']), \
                    "(OC-31) FAILED: C(ac) is not in the hub pencil L_c"
                if rkG != tgtG:
                    noff += 1
                    continue
                ntgt += 1
                assert ckG == 0, "G at the Tay target but corank(G) != 0"
                assert sigma == 0, \
                    "(OC-24)(ii)/(OC-28)(ii) FAILED: corank(G) = 0 yet " \
                    "corank(H) > 0"
                mot, idx = OL.weld_motions(Hed, VH, placed, [])
                D = OL.rel_span(mot, idx, b, c)
                assert len(D) == 3, \
                    "dim D != 3 at a target-rank G-point with sigma = 0"
                # (K-tight) *Step 2* item 1 at (G, v, a, b): corank R(G) = 0
                # forces D (+) <C(ac), C(va), C(vb)> = K^6.
                assert rank(list(D) + [Cac, Cva, Cvb]) == 6, \
                    "(OC-31) FAILED: corank R(G) = 0 but D + the three " \
                    "hinge lines is not all of K^6"
                assert rank(list(D) + [Cac, Cvb]) == 5, \
                    "(OC-31) FAILED: C(ac), C(vb) are not independent mod D"
                kind, roots, dimK, Kmats = bad_set(D, rd)
                assert dimK <= 2, \
                    "(OC-31) FAILED: dimK >= 3 at a target-rank G-point"
                assert not in_span(Cvb, D) and not in_span(Cac, D), \
                    "(OC-31) FAILED: a distinguished ruling generator is in D"
                assert rank(list(D) + list(rd['Lb'])) == 5 and \
                    rank(list(D) + list(rd['Lc'])) == 5, \
                    "(OC-31) FAILED: a ruling L_b / L_c meets D"
                pr = pitch_rank(D)
                hist[(dimK, kind, pr, has_ruling(Kmats))] = \
                    hist.get((dimK, kind, pr, has_ruling(Kmats)), 0) + 1
                # (OC-32) CONSTRUCTED, once per (shape, split): forcing
                # C(va) to be a transversal of M and bc collapses it onto
                # C(vb) (resp. C(ac)), so target rank cannot survive.
                if not done_con:
                    M0, Md = rd['M0'], rd['Md']
                    q = [M0[k] + 2 * Md[k] for k in range(3)]
                    # END b (w = pt(b)^):  pt(a) = q on M (legal: M is inside
                    # Pi(c)), pt(v) on the line q--pt(b) (legal: that line is
                    # inside Pi(b)).  Then C(va) IS C(vb).
                    pa1 = q
                    pv1 = [q[k] + 3 * (placed[b][k] - q[k]) for k in range(3)]
                    # END c (w = pt(c)^):  pt(v) = q on M (legal: M is inside
                    # Pi(b)), pt(a) on the line q--pt(c) (legal: inside Pi(c)).
                    # Then C(va) IS C(ac).
                    pv2 = q
                    pa2 = [q[k] + 3 * (placed[c][k] - q[k]) for k in range(3)]
                    for tag, pv2_, pa2_ in (('b-end', pv1, pa1),
                                            ('c-end', pv2, pa2)):
                        Cva2 = wedge2(hat(pv2_), hat(pa2_))
                        Cvb2 = wedge2(hat(pv2_), hat(placed[b]))
                        Cac2 = wedge2(hat(pa2_), hat(placed[c]))
                        # the forced transversal IS one of the other two
                        other = Cvb2 if tag == 'b-end' else Cac2
                        assert rank([Cva2, other]) == 1, \
                            f"(OC-32) FAILED at {tag}: the forced " \
                            "transversal did not collapse onto C(vb)/C(ac)"
                        # C(va) IS a transversal of M and bc, by construction
                        assert in_span(Cva2, rd['MW']), \
                            f"(OC-32) at {tag}: C(va) is not a transversal"
                        assert rank(list(D) + [Cac2, Cva2, Cvb2]) <= 5, \
                            f"(OC-32) FAILED at {tag}: the collapsed triple " \
                            "still spans K^6 mod D -- target rank reachable"
                        # ... and the placement IS panel-legal
                        assert dot(nrm[c], [pa2_[k] - placed[c][k]
                                            for k in range(3)]) == 0, \
                            f"({tag}) the constructed pt(a) left Pi(c)"
                        assert dot(nrm[b], [pv2_[k] - placed[b][k]
                                            for k in range(3)]) == 0, \
                            f"({tag}) the constructed pt(v) left Pi(b)"
                        ncon += 1
                    done_con = True
    print(f"   G-chart points at the Tay target: {ntgt};  off-target "
          f"guard-accepted G-points: {noff};\n   (Lambda-0d)/meet-line "
          f"rejections: {nskip[0]};  (OC-32) constructions: {ncon}"
          f"   [{time.time() - t0:.0f} s]")
    print("   (dimK, bad set on M, rank(Q|_D), ruling in D?) -> count:")
    for k in sorted(hist, key=str):
        print(f"       {k} : {hist[k]}")
    assert ntgt, "no target-rank G-chart point drawn -- (OC-31) untested"
    print("   asserted per target-rank G-point: pt(v) in Pi(b) and "
          "pt(a) in Pi(c); C(vb) in L_b and\n     C(ac) in L_c; "
          "D (+) <C(ac), C(va), C(vb)> = K^6; C(ac), C(vb) independent "
          "mod D;\n     dimK <= 2; L_b cap D = L_c cap D = 0.  Per "
          "(shape, split): the (OC-32) collapse,\n     CONSTRUCTED at both "
          "ends, with the constructed placement's panel legality\n"
          "     asserted -- so the third generator is unavailable, not "
          "merely unfound.")
    print("\nGTARGET OK.")


# ---------------- --rekey: (OC-34), the (a_2) cross-pool re-keying ----------

def shape_key(edges):
    """The isomorphism class of a class shape, as the canonical form of its
    LENGTH-LABELLED HUB MULTIGRAPH: a subdivision whose hubs are exactly the
    vertices of degree >= 3 is determined up to isomorphism by (G-degree,
    branch lengths), so the key is the lexicographically least labelled
    multiset of (hub, hub, length) triples over all relabellings of the hub
    set.  |V(G-degree)| <= 6 throughout, so the |hubs|! loop is cheap."""
    import itertools
    hubs, branches = branch_decomposition(edges)
    assert branches is not None, "a bare cycle is not a class shape"
    hs = sorted(hubs, key=str)
    n = len(hs)
    pos = {h: i for i, h in enumerate(hs)}
    trips = [(pos[h1], pos[h2], len(inter) + 1) for (h1, h2, inter) in branches]
    best = None
    for perm in itertools.permutations(range(n)):
        key = tuple(sorted((min(perm[x], perm[y]), max(perm[x], perm[y]), L)
                           for (x, y, L) in trips))
        if best is None or key < best:
            best = key
    return (n, best)


def certify_shape(label, edges, cap_probe=48, col_cap=1 << 16):
    """gridwit's own (GR-9)/(GR-10) certificate hunt at ONE shape: does some
    filter-passing admissible colouring carry both-block tree-triple
    certificates?  Returns (certified, probed, capped)."""
    import closure
    from grid import (block_data, colourings, combinatorial_filter,
                      cycle_rank, rank_at_params, TRIES_SEED)
    from gridwit import tree_triple
    from dominance import branch_pmap
    from kslide import no_rigid_branch_union
    allverts = sorted(verts_of(edges), key=str)
    target = 6 * (len(allverts) - 1)
    # the CLASS PREDICATE, asserted rather than assumed: tight, def = 0,
    # hnoRigid.  (K-grid)'s certificate theorem (GR-9) is stated over tight
    # class shapes, so a shape certified here must be one.
    assert 5 * len(edges) == 6 * (len(allverts) - 1), \
        f"{label}: not tight (5|E| != 6(|V|-1))"
    assert deficiency(edges) == 0, f"{label}: def != 0"
    assert no_rigid_branch_union(edges, branch_pmap(edges)), \
        f"{label}: hnoRigid FAILS -- not a class shape"
    cols, odd = colourings(edges, cap=col_cap)
    assert not odd and cols is not None, f"{label}: odd-cycle obstruction"
    probed, any_cap = 0, False
    for col in cols:
        if combinatorial_filter(edges, allverts, col):
            continue
        if probed >= cap_probe:
            break
        probed += 1
        if closure.build_fixed_config(edges, allverts, col) is None:
            continue
        certs = []
        for mine in ('A', 'B'):
            bd = block_data(edges, allverts, col, mine)
            tt, capped = tree_triple(bd)
            any_cap = any_cap or capped
            if tt is None:
                break
            n_c = bd['n_c']
            for i in range(3):
                pair = tt[i] + tt[(i + 1) % 3]
                assert len(pair) == n_c - 1 and \
                    cycle_rank(bd['nodes'], pair) == 0, \
                    f"{label}: pair-union is not a spanning tree"
            certs.append(tt)
        if len(certs) == 2:
            rng = random.Random(TRIES_SEED * 17 + len(allverts))
            for _ in range(3):
                if rank_at_params(edges, allverts, col, rng) == target:
                    return True, probed, any_cap
            assert False, f"{label}: certified colouring missed the target"
    return False, probed, any_cap


def rekey():
    from grid import census_shapes
    from kslidecomb import shape_ok
    print("== (OC-34): the (a_2) cross-pool RE-KEYING, POOL-OR ==")
    print("   section (K-grid)'s 907 certified shapes and section (K-out)'s "
          "class-shape\n   population are labelled-instance pools with "
          "different keys ((OC-28)(a)).  Both\n   are re-keyed here by the "
          "isomorphism class of the length-labelled hub\n   multigraph "
          "(`shape_key`), and the containment reported.")
    print("   CAPS DISCLOSED (README section 4 convention 8): section "
          "(K-out)'s population is\n   `outer.named_inventory()` (19 named "
          "shapes) plus EVERY shape of\n   `outer.sweep_shapes()`, whose own "
          "bounds are exhaustive over lengths 1..9 for\n   theta3/theta4, "
          "1..5 for K4, 1..6 for K4+par and CAPPED at 25 per |V*| = 5\n"
          "   family; section (K-grid)'s is `grid.census_shapes()` (877 "
          "exhaustive K4-stratum\n   + 6 + 21 seeded sweep + 3 tight "
          "thetas).  Neither pool is re-sampled.\n")
    t0 = time.time()
    gridkeys = {}
    ngrid = 0
    for label, edges in census_shapes():
        ngrid += 1
        k = shape_key(edges)
        gridkeys.setdefault(k, label)
    print(f"   section (K-grid) census: {ngrid} labelled shapes -> "
          f"{len(gridkeys)} isomorphism classes"
          f"   [{time.time() - t0:.0f} s]")
    outpool = []
    for label, E in outer.named_inventory():
        outpool.append((f'named:{label}', E))
    for fname, fam in outer.sweep_shapes():
        for label, E in fam:
            outpool.append((f'sweep:{label}', E))
    print(f"   section (K-out) population: {len(outpool)} labelled shapes")
    seen, withl4, classes4 = {}, 0, {}
    nnoclass = 0
    for label, E in outpool:
        # only shapes carrying a length-4 companion at some eligible split
        # matter for (a_2) as the hand-off states it
        hit = False
        for v in outer.eligible_splits(E):
            sd = outer.split_data(E, v)
            if sd is None:
                continue
            a, b, c, Gp, Hed = sd
            if outer.companions4(Hed, b, c):
                hit = True
                break
        if not hit:
            continue
        withl4 += 1
        k = shape_key(E)
        classes4.setdefault(k, (label, E))
    print(f"   ... of which {withl4} labelled shapes carry a length-4 "
          f"companion at some eligible\n       split, in "
          f"{len(classes4)} isomorphism classes"
          f"   [{time.time() - t0:.0f} s]")
    inside = [k for k in classes4 if k in gridkeys]
    outside = [k for k in classes4 if k not in gridkeys]
    print(f"   IN section (K-grid)'s certified set: {len(inside)} classes;"
          f"  NOT in it: {len(outside)} classes")
    print("\n   the misses, certified DIRECTLY by gridwit's own "
          "(GR-9)/(GR-10) hunt:")
    ok, bad, capped = 0, [], 0
    for k in sorted(outside, key=str):
        label, E = classes4[k]
        # only a genuine class shape can be certified; report the rest
        cert, probed, was_capped = certify_shape(label, E)
        if was_capped:
            capped += 1
        if cert:
            ok += 1
        else:
            bad.append((label, k, probed))
        print(f"       {label:34s} hubs={k[0]:2d} certified={cert} "
              f"probed={probed}{' CAPPED' if was_capped else ''}")
    print(f"\n   directly certified: {ok} of {len(outside)};  "
          f"MISSES: {len(bad)};  node-cap hit at {capped}")
    for r in bad:
        print(f"       MISS {r}")
    print(f"   total: {len(inside)} + {ok} of {len(classes4)} isomorphism "
          f"classes of section (K-out)'s\n   length-4-companion population "
          f"carry a both-block tree-triple certificate.")
    print("   CONDITIONAL, and this is the whole point: the transfer is "
          "(OC-28)(iii), whose\n   antecedent (GR-10) is OPEN -- its min-max "
          "form REFUTED as posed, the statement\n   standing.  A certificate "
          "at a shape gives the `s_0` half AT THAT SHAPE by\n   (GR-9) + "
          "(GR-5) + section (K-clos) (AC-7); it does not prove (GR-10).")
    print(f"\n   [{time.time() - t0:.0f} s]")
    print("\nREKEY OK.")


# ---------------- --census{1,2}: the re-keyed per-class witness census -----

CENSUS_SEEDS = range(800, 803)


def out_classes():
    """One representative per isomorphism class of section (K-out)'s
    length-4-companion population, with the first eligible split carrying a
    length-4 companion.  Deterministic: the first representative met in
    `named_inventory()` then `sweep_shapes()` order."""
    pool = [(f'named:{lab}', E) for lab, E in outer.named_inventory()]
    for _fname, fam in outer.sweep_shapes():
        for lab, E in fam:
            pool.append((f'sweep:{lab}', E))
    seen, out = set(), []
    for lab, E in pool:
        v0 = None
        for v in outer.eligible_splits(E):
            sd = outer.split_data(E, v)
            if sd is None:
                continue
            a, b, c, Gp, Hed = sd
            if outer.companions4(Hed, b, c):
                v0 = v
                break
        if v0 is None:
            continue
        k = shape_key(E)
        if k in seen:
            continue
        seen.add(k)
        out.append((lab, E, v0, k))
    return out


def census(part):
    """(OC-31)/(OC-33) at ONE eligible split of EVERY isomorphism class of
    section (K-out)'s length-4-companion population -- the re-keyed
    successor to (OC-27)'s 138 labelled (shape, split) pairs.  Each hit is
    an individual WITNESS (one point certifies input (a) at that shape and
    split), never a rate."""
    cls = out_classes()
    cls.sort(key=lambda r: (len(verts_of(r[1])), str(r[0])))
    mine = [r for i, r in enumerate(cls) if i % 2 == (part - 1)]
    print(f"== (OC-31)/(OC-33) at every isomorphism class, POOL-OC2 part "
          f"{part} of 2 ==")
    print(f"   POOL-OC2: one representative per isomorphism class of section "
          f"(K-out)'s length-4-\n             companion population "
          f"({len(cls)} classes; caps as in --rekey), at the FIRST\n"
          f"             eligible split carrying a length-4 companion, "
          f"placement seeds\n             {CENSUS_SEEDS.start}-"
          f"{CENSUS_SEEDS.stop - 1} of the WHOLE graph `G`, first "
          f"guard-accepted target-rank point\n             per class.  "
          f"Part {part} takes every 2nd class by (|V|, label) order: "
          f"{len(mine)} classes.")
    print("   Each hit is a WITNESS, never a rate; caps disclosed.\n")
    t0, hist, hit, miss = time.time(), {}, 0, []
    for lab, E, v, k in mine:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        VG = sorted(verts_of(E), key=str)
        VH = sorted(verts_of(Hed), key=str)
        tgtG = 6 * (len(VG) - 1) - deficiency(E)
        got = None
        for seed in CENSUS_SEEDS:
            pl = place_pencil_general(E, random.Random(seed))
            if pl is None:
                continue
            placed, _pt, nrm, _hubs, _nb = pl
            if not star_generic(E, placed):
                continue
            okG, _i = verify_pencil_witness(E, placed)
            if not okG:
                continue
            if outer.panel_frame(placed, nrm, b, c) is None or \
                    not outer.lam0d(placed, nrm, b, c):
                continue
            ckG, rkG = zneq.corank_at(E, placed, VG)
            if rkG != tgtG:
                continue
            assert ckG == 0, f"{lab}: at the Tay target but corank(G) != 0"
            sigma, _r = zneq.corank_at(Hed, placed, VH)
            assert sigma == 0, \
                f"{lab}: corank(G) = 0 yet corank(H) > 0 -- (OC-28)(ii) FAILS"
            rd = ruling_data(placed, nrm, b, c)
            Cvb = wedge2(hat(placed[v]), hat(placed[b]))
            Cac = wedge2(hat(placed[a]), hat(placed[c]))
            Cva = wedge2(hat(placed[v]), hat(placed[a]))
            assert in_span(Cvb, rd['Lb']) and in_span(Cac, rd['Lc']), \
                f"{lab}: C(vb) / C(ac) left the hub pencils"
            mot, idx = OL.weld_motions(Hed, VH, placed, [])
            D = OL.rel_span(mot, idx, b, c)
            assert len(D) == 3, f"{lab}: dim D != 3"
            assert rank(list(D) + [Cac, Cva, Cvb]) == 6, \
                f"{lab}: (OC-31)'s (K-tight) item-1 consequence FAILS"
            kind, roots, dimK, Kmats = bad_set(D, rd)
            assert dimK <= 2, f"{lab}: (OC-31) FAILS, dimK >= 3"
            pr = pitch_rank(D)
            if pr == 3:
                assert not has_ruling(Kmats), \
                    f"{lab}: (OC-33) FAILS -- rank(Q|_D) = 3 with a ruling"
            got = (dimK, kind, pr, has_ruling(Kmats), seed)
            break
        if got is None:
            miss.append((lab, len(VG)))
            continue
        hit += 1
        hist[got[:4]] = hist.get(got[:4], 0) + 1
    print(f"   classes probed: {len(mine)};  target-rank witnesses: {hit};  "
          f"no witness in the seed window: {len(miss)}"
          f"   [{time.time() - t0:.0f} s]")
    print("   (dimK, bad set on M, rank(Q|_D), ruling in D?) -> count:")
    for kk in sorted(hist, key=str):
        print(f"       {kk} : {hist[kk]}")
    for r in miss:
        print(f"       NO WITNESS {r}")
    print("   asserted per witness: corank(G) = 0 ==> corank(H) = 0; "
          "C(vb) in L_b, C(ac) in L_c;\n     the (K-tight) item-1 "
          "consequence; dimK <= 2 ((OC-31)); and rank(Q|_D) = 3 ==> no "
          "ruling\n     ((OC-33)).  A `bad set = none` row is an individual "
          "PROOF that input (a) holds at\n     that (shape, split): the "
          "WHOLE pt(a)-fibre over that H-part lies in Z.")
    print(f"\nCENSUS{part} OK.")


def main():
    modes = {'--restate': restate, '--gtarget': gtarget, '--rekey': rekey,
             '--census1': lambda: census(1), '--census2': lambda: census(2)}
    args = [a for a in sys.argv[1:] if a in modes]
    if not args:
        print(__doc__)
        print("modes:", " ".join(sorted(modes)))
        return
    for a in args:
        t0 = time.time()
        modes[a]()
        print(f"[{a}: {time.time() - t0:.1f} s]")


if __name__ == '__main__':
    main()
