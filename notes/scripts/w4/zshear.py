"""Phase 39 direction ZSHEAR -- is the Witt shear a uniformity device?

The question (`notes/Pencil-strategy.md` §9.2 candidate **(ZH-1)**, the first
direction the external-technique shelf has produced): the orthogonal group of
the split form `q(w, m) = w . m` on `k^3 (+) k^3` contains unipotent shears
`Phi_S(w, m) = (w, m + S w)` for `S` skew, which fix each generator of a
maximal isotropic individually because `w^T S w = 0`.  Proposed use: replace
"exhibit a good seed" by "avoid finitely many proper affine subspaces of
`so_3(k)`", which over an infinite field is free -- exactly `hK`'s hypothesis.

PROVENANCE BAR, and it is the hard one.  The idea source is an unrefereed
preprint whose own acknowledgment credits an AI assistant with the proof
details and the Lean verification, and which this project has NOT independently
checked.  It is an IDEA SOURCE, never a citation: no theorem of it is imported,
assumed, or leaned on anywhere below.  Everything here stands on (a) classical
facts already in `notes/Pencil-strategy.md` §7's in-use list -- the Klein
quadric, its alpha/beta maximal isotropics, Witt's theorem -- and (b) this
project's own harness.  In particular the shear is NOT taken on trust as a new
object: `--iso` PROVES, as an identity in `Q[s0, s1, s2]`, that it is the
`Lambda^2` image of an affine TRANSLATION of `P^3`, i.e. an element of the
carrier's own projective gauge group, already implicitly available.

MODES (F11: each headline claim names the mode that tests THAT sentence).

  --iso    (SH-1)/(SH-2).  SYMBOLIC, no sampling anywhere.  Over `Q[s]` with
           `s` the free axial vector of a general skew `S`:
             * the project's pitch quadric `Q(x) = <x, star x>` equals
               `2 * dir(x) . mom(x)`, so §(K-pitch) *Step 0*'s form and the
               split form are the SAME form in the harness's own Plucker
               convention (an identity in `Q[6 vars]`);
             * `Phi_S = Lambda^2(T_{-s})`, `T_t` the translation `x -> x + t`
               of affine 3-space -- so `{Phi_S : S skew}` IS the 3-dimensional
               translation subgroup of `PGL(4)`, not merely isomorphic to it;
             * `Phi_S^T star Phi_S = star` identically, so `Q` is the shear
               group's own invariant.
  --bed    (SH-3).  The adversarial bed, GUARDED: §(K-flank) *Step F5(d)*'s
           five legal nondegenerate target-rank `G'` seeds at `P21` with
           `s0 = 1`, `dim R_a = 0`, `dim U = 1`, re-derived and asserted
           against that step's RECORDED values (30 / 5 / 5 over seeds
           101..140) before anything is concluded from them.  The
           `localtest.plane_basis` precedent is exactly this bed, so the
           composite genericity gate `repin.star_generic` is reported per
           seed rather than assumed.
  --inv    (SH-4).  The INVARIANCE claim, tested as an invariance and not by
           sampling a few `S`: at every bed seed, of BOTH strata, the whole
           §(K-tight) criterion is carried by the shear -- `U' = Phi^-T U` and
           `R_a' = Phi^-T R_a` as SUBSPACES, `Lambda^2 Pihat(b)' = Phi L2b`,
           the 2 x dim U criterion matrix EQUAL entry-by-entry in the pushed
           basis, and the exact rank at every corresponding placement equal.
  --prod   (SH-5)/(SH-6).  The coordinator's offered repair -- one shear per
           body instead of one global `S`.  Symbolic: the generator-wise
           defect is exactly `2 (t_u - t_v) . (dir X_u x dir X_v)`, so the
           product action does NOT preserve the form off the diagonal.  Then
           the carrier-side version: the maximal group of per-body
           translations preserving the pencil conditions at fixed panel
           normals is computed exactly, and it is the chart's own fixed-normal
           affine slice.
  --validate   all four, in that order.

CAPS, disclosed.  `--bed`/`--inv` use `P21` seeds 101..140 (the range *Step
F5(d)* itself used) and no others -- all 35 valid seeds, both strata, none
skipped; `--inv` gives the 5 forced-failure seeds 3 shears x (6 route-A + 3
route-B) placements each and the 30 escaping seeds 1 shear x (2 route-A + 1
route-B), all seeded; `--prod` samples 6 translation fields.  Nothing here is
a genericity claim: the symbolic modes
are identities, and the numeric modes are equalities asserted at every probed
point, so a single counterexample would fail an assert.

All exact `Q`.  Read-only w.r.t. the harness: every geometric primitive is
imported.  The one NEW local layer is `Poly` -- a minimal exact multivariate
polynomial type over `Q` -- which exists so that the invariance claims are
IDENTITIES rather than samples; the harness has no Python symbolic layer to
reuse (its symbolic layer is Macaulay2, and this direction opens no M2 leaf).
The `crit_from_placement` assembly is NOT a reimplementation of a harness
primitive: it is `repin.seed_probe`'s own computation re-keyed from a SEED to
a PLACEMENT (which is what a shear produces -- a placement that no seed
generates), built only from imported primitives, and `--inv` ASSERTS that it
reproduces `seed_probe` field-for-field at `t = 0` before any shear is applied.

Reproduce:
  python3 notes/scripts/w4/zshear.py --iso | --bed | --inv | --prod | --validate
"""

import random
import sys
import time
from fractions import Fraction as F

import os, sys                                                    # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (PL, cross3, hat, left_nullspace, nullspace,  # noqa: E402
                       rank as rank_exact, wedge2)
from pencil_escape import rquat, rvec3                             # noqa: E402
from kbare_common import verts_of                                  # noqa: E402
from nogood_subdiv import deficiency, hub_set                      # noqa: E402
from widened import orient, removeV, splitOff, split_report        # noqa: E402
from repin import (dot, hodge_star, in_span, lambda2_plane,        # noqa: E402
                   lambda2_through, rank_at_V, rob_in_plane,
                   seed_probe, span_basis, star_generic)
from kslidecomb import shape_data                                  # noqa: E402
from flanks import P21_SPECS                                       # noqa: E402


# ===================== a minimal exact symbolic layer ======================
#
# Monomials are tuples of (name, exponent) pairs, sorted by name; a Poly is a
# dict monomial -> Fraction with zero coefficients stripped.  Only +, -, * and
# equality are needed.

class Poly:
    __slots__ = ('c',)

    def __init__(self, c=None):
        self.c = {m: k for m, k in (c or {}).items() if k != 0}

    @staticmethod
    def num(x):
        return Poly({(): F(x)})

    @staticmethod
    def var(name):
        return Poly({((name, 1),): F(1)})

    def __add__(self, o):
        o = o if isinstance(o, Poly) else Poly.num(o)
        d = dict(self.c)
        for m, k in o.c.items():
            d[m] = d.get(m, F(0)) + k
        return Poly(d)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -k for m, k in self.c.items()})

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Poly) else Poly.num(o)))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        o = o if isinstance(o, Poly) else Poly.num(o)
        d = {}
        for m1, k1 in self.c.items():
            for m2, k2 in o.c.items():
                e = dict(m1)
                for nm, ex in m2:
                    e[nm] = e.get(nm, 0) + ex
                m = tuple(sorted(e.items()))
                d[m] = d.get(m, F(0)) + k1 * k2
        return Poly(d)

    __rmul__ = __mul__

    def is_zero(self):
        return not self.c

    def __eq__(self, o):
        return (self - (o if isinstance(o, Poly) else Poly.num(o))).is_zero()

    def __repr__(self):
        if not self.c:
            return '0'
        out = []
        for m, k in sorted(self.c.items()):
            s = '*'.join(nm if ex == 1 else f'{nm}^{ex}' for nm, ex in m)
            out.append(f'{k}' if not s else (s if k == 1 else f'{k}*{s}'))
        return ' + '.join(out)


def pmatmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum((A[i][k] * B[k][j] for k in range(m)), Poly())
             for j in range(p)] for i in range(n)]


def ptranspose(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def pmat_eq(A, B):
    return all(A[i][j] == B[i][j]
               for i in range(len(A)) for j in range(len(A[0])))


# ============ the two constructions of the shear, kept independent =========
#
# Convention, read off `exactcore`: `PL = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]`
# and `hat(c) = (c0, c1, c2, 1)`, so index 3 is the homogenizing coordinate and
# the plane at infinity is `x3 = 0`.  For `w` in `Lambda^2 K^4`,
#     dir(w) = (p03, p13, p23) = (w[2], w[4], w[5])
#     mom(w) = (p12, -p02, p01) = (w[3], -w[1], w[0])
# and for a line through affine points `x`, `y`: dir = x - y, mom = x cross y.

DIR_IX = (2, 4, 5)
MOM_IX = ((3, 1), (1, -1), (0, 1))          # (index, sign)


def dir_of(w):
    return [w[i] for i in DIR_IX]


def mom_of(w):
    return [w[i] * s if s == 1 else -w[i] for (i, s) in MOM_IX]


def lam2_of_translation(t):
    """Lambda^2 of the 4x4 translation `x -> x + t`, as the second compound
    matrix.  Entries live in whatever ring `t` does."""
    one, zero = (Poly.num(1), Poly()) if isinstance(t[0], Poly) else (F(1), F(0))
    T = [[one if i == j else zero for j in range(4)] for i in range(4)]
    for i in range(3):
        T[i][3] = t[i]
    M = [[None] * 6 for _ in range(6)]
    for I, (i, j) in enumerate(PL):
        for J, (k, l) in enumerate(PL):
            M[I][J] = T[i][k] * T[j][l] - T[j][k] * T[i][l]
    return M


def shear_matrix(s):
    """`Phi_S(w) = (dir w, mom w + S dir w)` with `S` the skew matrix of axial
    vector `s` (i.e. `S x = s cross x`), written in the harness's Plucker
    coordinates.  Built from the (dir, mom) description ONLY -- deliberately
    independent of `lam2_of_translation`, so that `--iso`'s comparison of the
    two is a real identity check and not a tautology."""
    one, zero = (Poly.num(1), Poly()) if isinstance(s[0], Poly) else (F(1), F(0))
    M = [[zero] * 6 for _ in range(6)]
    # dir coordinates are fixed
    for i in DIR_IX:
        M[i][i] = one
    # mom' = mom + s x dir ; unpack back into Plucker slots
    #   (s x d)_0 = s1 d2 - s2 d1, etc., with d = (w[2], w[4], w[5])
    sx = [(s[1], DIR_IX[2], s[2], DIR_IX[1]),
          (s[2], DIR_IX[0], s[0], DIR_IX[2]),
          (s[0], DIR_IX[1], s[1], DIR_IX[0])]
    for comp, ((ix, sign)) in enumerate(MOM_IX):
        a, ia, b, ib = sx[comp]
        # mom_comp = sign * w[ix]  =>  contribution to row ix is sign * (...)
        M[ix][ix] = one
        M[ix][ia] = M[ix][ia] + (a if sign == 1 else -a)
        M[ix][ib] = M[ix][ib] - (b if sign == 1 else -b)
    return M


def phi_num(t):
    """The exact-Q 6x6 shear matrix of the translation by `t` (so, the shear
    of axial vector `-t`).  Uses `lam2_of_translation`, whose agreement with
    `shear_matrix` is proved in `--iso`."""
    return lam2_of_translation(list(t))


def mat_apply(M, x):
    return [sum((M[i][j] * x[j] for j in range(len(x))), F(0))
            for i in range(len(M))]


def mat_applyT(M, x):
    return [sum((M[j][i] * x[j] for j in range(len(x))), F(0))
            for i in range(len(M))]


STAR = [[F(1) if j == k else F(0) for j in range(6)] for k in range(6)]
for _i in range(6):
    _e = [F(1) if _k == _i else F(0) for _k in range(6)]
    _s = hodge_star(_e)
    for _j in range(6):
        STAR[_j][_i] = _s[_j]


# =============================== mode --iso ================================

def driver_iso():
    print("== (SH-1)/(SH-2): what the Witt shear IS, proved symbolically ==")
    t0 = time.time()

    # (i) the two quadratic forms are the SAME form, in the harness's own
    #     Plucker convention.
    w = [Poly.var(f'w{k}') for k in range(6)]
    Qw = sum((w[i] * Poly({(): F(1)}) * hodge_star(w)[i] for i in range(6)),
             Poly())
    split = Poly()
    for a, b in zip(dir_of(w), mom_of(w)):
        split = split + a * b
    assert Qw == Poly.num(2) * split, (Qw, split)
    print("   (i) Q(x) = <x, star x> = 2 * dir(x) . mom(x) IDENTICALLY in")
    print("       Q[w0..w5]: §(K-pitch) *Step 0*'s pitch quadric and the split")
    print("       form on (dir, mom) are the same form -- not an analogy.")

    # (ii) a general skew shear IS Lambda^2 of a translation.
    s = [Poly.var('s0'), Poly.var('s1'), Poly.var('s2')]
    Phi = shear_matrix(s)
    Lam = lam2_of_translation([-s[0], -s[1], -s[2]])
    assert pmat_eq(Phi, Lam), 'shear != Lambda^2(translation)'
    print("   (ii) Phi_S = Lambda^2(T_{-s}) IDENTICALLY in Q[s0,s1,s2], where")
    print("        `s` is the axial vector of the skew `S` and `T_t` is the")
    print("        affine translation x -> x + t of 3-space.  The map")
    print("        s -> S is a linear ISOMORPHISM onto so_3 (dim 3 = dim of")
    print("        the translation group -- the d = 3 coincidence")
    print("        d(d-1)/2 = d), so the shear group is EXACTLY the")
    print("        translation subgroup of PGL(4) acting on line coordinates.")

    # (iii) the shear preserves the Klein form identically, so Q is ITS
    #       invariant.
    lhs = pmatmul(ptranspose(Phi), pmatmul([[Poly.num(x) for x in row]
                                            for row in STAR], Phi))
    assert pmat_eq(lhs, [[Poly.num(x) for x in row] for row in STAR])
    print("   (iii) Phi_S^T star Phi_S = star IDENTICALLY, so Q(Phi_S x) =")
    print("         Q(x) for EVERY skew S and every x: the pitch quadric is")
    print("         the shear group's own defining invariant.")

    # (iv) which maximal isotropic it fixes pointwise, and why that is a
    #      classical beta-plane and not new machinery.
    beta = []                      # lines in the plane at infinity: dir = 0
    for I, (i, j) in enumerate(PL):
        if 3 not in (i, j):
            e = [Poly() for _ in range(6)]
            e[I] = Poly.num(1)
            beta.append(e)
    assert len(beta) == 3
    for e in beta:
        assert all(x == y for x, y in zip(pmatmul(Phi, [[y] for y in e]),
                                          [[y] for y in e]))
    print("   (iv) the 3-space it fixes POINTWISE is span(e01, e02, e12) = the")
    print("        lines lying in the plane at infinity -- a beta-plane of the")
    print("        Klein quadric, i.e. one of the classical maximal isotropics")
    print("        already in this project's in-use list.  Conversely the")
    print("        pointwise stabilizer of a beta-plane inside O(Q) is exactly")
    print("        3-dimensional (a homothety x -> lambda x fixes that plane")
    print("        pointwise only projectively, and lands in O(Q) only at")
    print("        lambda = 1), so nothing larger is on offer.")
    print(f"\n   => the shear is ALREADY implicitly available to the arc: it is")
    print("      a translation of the ambient space, and every carrier")
    print("      condition (`HasPencilPanelRealization`'s extensor-through-")
    print("      both-points, `IsNondegPencilRealization`'s projective")
    print("      distinctness and non-collinearity) is a projective incidence")
    print("      condition, hence translation-invariant.  It is a GAUGE")
    print("      transformation, not new machinery.")
    print(f"   [{time.time() - t0:.1f}s]")


# ================= the criterion, re-keyed from seed to placement ===========

def crit_from_placement(edges, v, placed, nrm, rngseed):
    """`repin.seed_probe`'s §(K-tight) criterion computation, driven by a
    PLACEMENT instead of a seed.  Assembled from imported primitives only;
    `--inv` asserts it reproduces `seed_probe` field-for-field at `t = 0`."""
    a, b, c = orient(edges, v)
    Gv, Gp = removeV(edges, v), splitOff(edges, v, a, b)
    nG = len(verts_of(edges))
    tgtG = 6 * (nG - 1) - deficiency(edges)
    tgtGp = 6 * (nG - 2) - deficiency(Gp)
    hubsG = hub_set(edges)
    Vp = sorted(verts_of(Gp), key=str)
    rkp, rows, er, idx = rank_at_V(Gp, placed, Vp)
    out = {'a': a, 'b': b, 'c': c, 'rank Gp': rkp, 'target Gp': tgtGp,
           'target G': tgtG, 'target-rank': rkp == tgtGp}

    shared = [e for e in Gp if set(e) != {a, b}]
    rk_sh, rows_sh, er_sh, idx_sh = rank_at_V(shared, placed, Vp)
    out['s0'] = 5 * len(shared) - rk_sh

    e_ab = next(e for e in er if set(e) == {a, b})
    base_a = 6 * idx[a]
    Ra = []
    for lam in left_nullspace(rows):
        r = [F(0)] * 6
        for ri in er[e_ab]:
            for k in range(6):
                r[k] += lam[ri] * rows[ri][base_a + k]
        Ra.append(r)
    Ra_basis = span_basis(Ra)
    out['dim R_a'] = len(Ra_basis)
    out['Ra'] = Ra_basis
    out['corank Gp'] = 5 * len(Gp) - rkp

    motions = nullspace(rows_sh)
    ia, ib = 6 * idx_sh[a], 6 * idx_sh[b]
    D = [[m[ia + k] - m[ib + k] for k in range(6)] for m in motions]
    Db = span_basis(D)
    U = nullspace(Db) if Db else [[F(1) if k == i else F(0) for k in range(6)]
                                  for i in range(6)]
    out['dim U'] = len(U)
    out['U'] = U
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    out['Cab'] = wedge2(ah, bh)

    rng = random.Random(rngseed)
    if b in hubsG and b in nrm:
        L2b = lambda2_plane(placed[b], nrm[b], rng)
    else:
        L2b = span_basis(lambda2_through(ah) + lambda2_through(bh))
    rng2 = random.Random(rngseed + 1)
    if c in hubsG and c in nrm:
        L2c = lambda2_plane(placed[c], nrm[c], rng2)
    else:
        L2c = span_basis(lambda2_through(ah) + lambda2_through(ch))
    out['L2b'], out['L2c'] = L2b, L2c
    out['critA'] = any(any(dot(r, w) != 0 for w in L2b) for r in Ra_basis)
    out['critB'] = any(any(dot(r, w) != 0 for w in L2c) for r in Ra_basis)
    # the 2 x dim U criterion matrix of *Step 2.1*, in the returned U basis
    out['critmat'] = None
    return out


def critmat(placed, v, a, b, x, U):
    """The two placement functionals of §(K-tight) *Step 2.1* evaluated on the
    basis `U`, at placement `pt(v) = x`: rank 2 <=> the target is attained."""
    xh = hat(x)
    Cva, Cvb = wedge2(xh, hat(placed[a])), wedge2(xh, hat(placed[b]))
    return [[dot(u, Cva) for u in U], [dot(u, Cvb) for u in U]]


# =============================== mode --bed ================================

_BED = []


def _bed_report(bed, invalid):
    edges, v, jump, fine = bed
    a, b, c = orient(edges, v)
    print(f"   P21: |V| = {len(verts_of(edges))}, |E| = {len(edges)}, "
          f"split v = {v}, a = {a}, b = {b}, c = {c}")
    print(f"   count-theoretic prediction (widened.split_report): "
          f"dim R_a = {split_report(edges, v)['dim R_a (identity)']}")
    print(f"   seeds 101..140: {len(fine)} with dim R_a = 1, "
          f"{len(jump)} with s0 = 1, dim R_a = 0, dim U = 1, "
          f"{invalid} invalid")
    print(f"   ASSERTED against §(K-flank) *Step F5(d)*'s recorded "
          f"(30, 5, 5) -- MATCH")


def p21_bed(verbose=True):
    """§(K-flank) *Step F5(d)*'s bed, re-derived and GUARDED against that
    step's recorded values before use.  Cached within a process so that
    `--validate` pays for it once (each rebuild is ~44 s of exact-Q rank)."""
    if _BED:
        if verbose:
            _bed_report(*_BED)
        return _BED[0]
    edges, pmap = shape_data(P21_SPECS)
    v = pmap[0][1]
    a, b, c = orient(edges, v)
    jump, fine, invalid = [], [], 0
    for s in range(101, 141):
        p = seed_probe(edges, v, s, nplace=0)
        if p is None:
            invalid += 1
            continue
        assert p['dim U = dim R_a + 1'] and p['U cap Cab-perp == R_a'] \
            and p['R_a subset U'], (s, p)
        if p['dim R_a'] == 0:
            assert p['s0'] == 1 and p['dim U'] == 1, (s, p['s0'], p['dim U'])
            jump.append((s, p))
        else:
            assert p['dim R_a'] == 1 and p['s0'] == 0, (s, p['s0'])
            fine.append((s, p))
    # the recorded figures of *Step F5(d)*: 30 escaping, 5 forced-failure, 5
    # invalid, over seeds 101..140.
    assert (len(fine), len(jump), invalid) == (30, 5, 5), \
        (len(fine), len(jump), invalid)
    _BED.append((edges, v, jump, fine))
    _BED.append(invalid)
    if verbose:
        _bed_report((edges, v, jump, fine), invalid)
    return edges, v, jump, fine


def driver_bed():
    print("== (SH-3): the adversarial bed, guarded before use ==")
    t0 = time.time()
    edges, v, jump, fine = p21_bed()
    a, b, c = orient(edges, v)
    Gp = splitOff(edges, v, a, b)
    print(f"   forced-failure seeds: {[s for s, _ in jump]}")
    print(f"   the `plane_basis` precedent is EXACTLY this bed "
          f"(§(K-out) (OC-38)(iii)), so the composite gate is reported on "
          f"G' (the seed's own graph), not assumed:")
    bad = [s for s, p in jump if not star_generic(Gp, p['_ctx'][0])]
    okg = [s for s, p in fine if star_generic(Gp, p['_ctx'][0])]
    print(f"      forced-failure seeds rejected by the composite gate: "
          f"{len(bad)}/{len(jump)} ({bad})")
    print(f"      escaping seeds ACCEPTED by the composite gate: "
          f"{len(okg)}/{len(fine)} -- so gate rejection is NECESSARY but not")
    print(f"      sufficient for the dim R_a jump in this range "
          f"({len(fine) - len(okg)} escaping seeds are also rejected)")
    print("   => the five are legal chart points (every §(K-tight) structure")
    print("      identity holds at each) but NOT generic: they sit on the")
    print("      located coincidence locus.  Every figure below is stated")
    print("      about them as EXHIBITED points, never as a rate.")
    print(f"   [{time.time() - t0:.1f}s]")


# =============================== mode --inv ================================

def shear_placement(placed, t):
    return {u: [placed[u][k] + t[k] for k in range(3)] for u in placed}


def subspace_eq(A, B):
    if len(A) != len(B):
        return False
    return (all(in_span(x, B) for x in A) and all(in_span(x, A) for x in B))


def driver_inv():
    print("== (SH-4): the failure locus is SHEAR-INVARIANT -- tested as an ==")
    print("   invariance, not by sampling a few S ==")
    t0 = time.time()
    edges, v, jump, fine = p21_bed(verbose=False)
    a, b, c = orient(edges, v)
    VG = sorted(verts_of(edges), key=str)
    hubsG = hub_set(edges)
    print(f"   bed: {len(jump)} forced-failure + {len(fine)} escaping P21 "
          f"seeds (guard: --bed).  Caps, disclosed: the forced-failure pool")
    print(f"   gets 3 shears x (6 route-A + 3 route-B) placements per seed;")
    print(f"   the escaping pool gets 1 shear x (2 route-A + 1 route-B).")

    agree0 = shears = subeq = rankeq = pitcheq = matq = 0
    att_agree = 0
    for tag, pool, nsh, nA, nB in (('R_a=0', jump, 3, 6, 3),
                                   ('R_a=1', fine, 1, 2, 1)):
        for s, p in pool:
            placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
            rngseed = 700000 + 13 * s
            q0 = crit_from_placement(edges, v, placed, nrm, rngseed)
            for k in ('s0', 'dim R_a', 'dim U', 'corank Gp', 'critA', 'critB'):
                assert q0[k] == p[k], (s, k, q0[k], p[k])
            agree0 += 1
            rg = random.Random(910000 + 37 * s)
            for trial in range(nsh):
                t = rvec3(rg)
                while all(x == 0 for x in t):
                    t = rvec3(rg)
                PHI = phi_num(t)
                PHIinv = phi_num([-x for x in t])
                pl_t = shear_placement(placed, t)
                q1 = crit_from_placement(edges, v, pl_t, nrm, rngseed)
                shears += 1
                for k in ('s0', 'dim R_a', 'dim U', 'corank Gp', 'rank Gp',
                          'target-rank', 'critA', 'critB'):
                    assert q1[k] == q0[k], (s, t, k, q1[k], q0[k])
                pushU = [mat_applyT(PHIinv, u) for u in q0['U']]
                pushR = [mat_applyT(PHIinv, r) for r in q0['Ra']]
                pushL = [mat_apply(PHI, w) for w in q0['L2b']]
                assert subspace_eq(pushU, q1['U']), (s, t, 'U')
                assert subspace_eq(pushR, q1['Ra']), (s, t, 'Ra')
                assert subspace_eq(pushL, q1['L2b']), (s, t, 'L2b')
                assert q1['Cab'] == mat_apply(PHI, q0['Cab']), (s, t, 'Cab')
                subeq += 1
                # route A: the criterion matrix and the honest rank, at
                # corresponding placements pt(v) = x and pt(v) = x + t
                rgp = random.Random(660000 + 7 * s)
                a0 = a1 = False
                for _ in range(nA):
                    x = (rob_in_plane(pt[b], nrm[b], rgp)
                         if b in hubsG and b in nrm else rvec3(rgp))
                    if x in (placed[a], placed[b]):
                        continue
                    xt = [x[k] + t[k] for k in range(3)]
                    M0 = critmat(placed, v, a, b, x, q0['U'])
                    M1 = critmat(pl_t, v, a, b, xt, pushU)
                    assert M0 == M1, (s, t, x, M0, M1)
                    matq += 1
                    w0 = dict(placed); w0[v] = x
                    w1 = dict(pl_t); w1[v] = xt
                    r0 = rank_at_V(edges, w0, VG)[0]
                    r1 = rank_at_V(edges, w1, VG)[0]
                    assert r0 == r1, (s, t, x, r0, r1)
                    assert (r0 == q0['target G']) == (rank_exact(M0) == 2), \
                        (s, x, r0, M0)
                    a0 = a0 or (r0 == q0['target G'])
                    a1 = a1 or (r1 == q1['target G'])
                    rankeq += 1
                assert a0 == a1, (s, t, a0, a1)
                att_agree += 1
                # route B: sweep pt(a) in Pihat(c), pt(v) := old pt(a)
                rgb = random.Random(770000 + 11 * s)
                for _ in range(nB):
                    pa = (rob_in_plane(pt[c], nrm[c], rgb)
                          if c in hubsG and c in nrm else rvec3(rgb))
                    if pa in (placed[a], placed[c]):
                        continue
                    pl2 = dict(placed)
                    pl2[v], pl2[a] = placed[a], pa
                    pl2t = shear_placement(pl2, t)
                    r0 = rank_at_V(edges, pl2, VG)[0]
                    r1 = rank_at_V(edges, pl2t, VG)[0]
                    assert r0 == r1, (s, t, 'B', r0, r1)
                    rankeq += 1
                # the pitch of the transmitted wrench
                if q0['dim R_a'] == 1:
                    r0v, r1v = q0['Ra'][0], q1['Ra'][0]
                    Q0 = dot(hodge_star(r0v), r0v)
                    Q1 = dot(hodge_star(r1v), r1v)
                    assert (Q0 == 0) == (Q1 == 0), (s, t, Q0, Q1)
                    assert in_span(mat_applyT(PHIinv, r0v), [r1v]), (s, t)
                    pitcheq += 1
    print(f"   re-keying guard: crit_from_placement == seed_probe at t = 0 "
          f"on {agree0}/{agree0} bed seeds (s0, dim R_a, dim U, corank, "
          f"critA, critB)")
    print(f"   shears applied: {shears}, exact Q, seeded")
    print(f"   subspace transport U' = Phi^-T U, R_a' = Phi^-T R_a, "
          f"L2b' = Phi L2b, C(ab)' = Phi C(ab): {subeq}/{subeq}")
    print(f"   criterion matrix EQUAL entry-for-entry in the pushed basis: "
          f"{matq}/{matq}")
    print(f"   exact rank equal at corresponding placements (A and B): "
          f"{rankeq}/{rankeq}; attainment verdict per (seed, shear) equal: "
          f"{att_agree}/{att_agree}")
    print(f"   pitch Q(r~) vanishing preserved and r~' in <Phi r~>: "
          f"{pitcheq}/{pitcheq}")
    print("\n   => at EVERY bed seed of BOTH strata, the shear carries the")
    print("      criterion exactly: the 2 x dim U matrix is not merely of the")
    print("      same rank, it is the SAME MATRIX in the pushed basis, because")
    print("      <Phi^-T u, Phi C> = <u, C>.  So for a fixed seed the set of")
    print("      `bad S` is all of so_3 (if the seed fails) or empty (if it")
    print("      escapes) -- NEVER a proper nonempty affine subspace.  The")
    print("      (ZH-1) mechanism `finitely many proper affine subspaces")
    print("      cannot cover an affine space over an infinite field` has")
    print("      nothing to act on.")
    print(f"   [{time.time() - t0:.1f}s]")


# =============================== mode --prod ===============================

def driver_prod():
    print("== (SH-5)/(SH-6): the graph-indexed repair -- one shear per body ==")
    t0 = time.time()

    # (i) the generator-wise defect, symbolically.
    du = [Poly.var(f'du{k}') for k in range(3)]
    mu = [Poly.var(f'mu{k}') for k in range(3)]
    dv = [Poly.var(f'dv{k}') for k in range(3)]
    mv = [Poly.var(f'mv{k}') for k in range(3)]
    tu = [Poly.var(f'tu{k}') for k in range(3)]
    tv = [Poly.var(f'tv{k}') for k in range(3)]

    def q_of(d, m):
        return Poly.num(2) * sum((x * y for x, y in zip(d, m)), Poly())

    def push(d, m, t):
        # translation by t: dir fixed, mom -> mom - t x dir
        c = cross3(t, d)
        return d, [m[k] - c[k] for k in range(3)]

    Du, Mu = push(du, mu, tu)
    Dv, Mv = push(dv, mv, tv)
    lhs = q_of([Du[k] - Dv[k] for k in range(3)],
               [Mu[k] - Mv[k] for k in range(3)])
    rhs0 = q_of([du[k] - dv[k] for k in range(3)],
                [mu[k] - mv[k] for k in range(3)])
    delta = [tu[k] - tv[k] for k in range(3)]
    corr = Poly.num(2) * sum((delta[k] * cross3(du, dv)[k] for k in range(3)),
                             Poly())
    assert lhs == rhs0 + corr, (lhs - rhs0 - corr)
    print("   (i) IDENTITY in Q[du, mu, dv, mv, tu, tv]:")
    print("       Q(Phi_{tu} X_u - Phi_{tv} X_v)")
    print("           = Q(X_u - X_v) + 2 (tu - tv) . (dir X_u x dir X_v).")
    print("       So a per-body product action preserves the form")
    print("       GENERATOR-WISE iff `tu - tv` is perpendicular to")
    print("       `dir X_u x dir X_v` at every edge -- one linear condition")
    print("       per edge, and the conditions depend on the POINT.  Off the")
    print("       diagonal the defect is nonzero: with du = e0, dv = e1,")
    print("       tu - tv = e2 it is 2.  The product action is therefore NOT")
    print("       an action on the variety; only the diagonal (the global")
    print("       shear of --iso) is.")
    d1 = [F(1), F(0), F(0)]
    d2 = [F(0), F(1), F(0)]
    dd = [F(0), F(0), F(1)]
    assert 2 * sum(dd[k] * cross3(d1, d2)[k] for k in range(3)) == 2

    # (ii) the carrier-side maximal per-body translation family.
    edges, v, jump, fine = p21_bed(verbose=False)
    placed0, pt0, nrm0 = jump[0][1]['_ctx'][0], jump[0][1]['_ctx'][1], \
        jump[0][1]['_ctx'][2]
    V = sorted(verts_of(edges), key=str)
    ix = {u: i for i, u in enumerate(V)}
    hubsG = hub_set(edges)
    from exactcore import neighbors
    nb = neighbors(edges)
    cons = []
    for h in sorted(hubsG, key=str):
        if h not in nrm0:
            continue
        for u in sorted(nb[h], key=str):
            row = [F(0)] * (3 * len(V))
            for k in range(3):
                row[3 * ix[u] + k] += nrm0[h][k]
                row[3 * ix[h] + k] -= nrm0[h][k]
            cons.append(row)
    fld = nullspace(cons)
    print(f"\n   (ii) the carrier-side family, computed exactly at P21 seed "
          f"{jump[0][0]}:")
    print(f"        a per-body translation field (t_u) keeps every hub star")
    print(f"        coplanar at FIXED panel normals iff nrm_h . (t_u - t_h) = 0")
    print(f"        for every hub h and every u in N(h) -- one linear")
    print(f"        condition per hub-neighbour incidence.")
    print(f"        |V| = {len(V)}, hub incidences = {len(cons)}, "
          f"constraint rank = {rank_exact(cons)}, "
          f"dim of the family = {len(fld)} (of 3|V| = {3 * len(V)})")
    print(f"        It contains the 3-dimensional diagonal (the global shear)")
    print(f"        and it GROWS with the graph -- so it passes §4.6's")
    print(f"        growing-ground-set filter, unlike so_3 itself.")
    diag = []
    for k in range(3):
        d = [F(0)] * (3 * len(V))
        for u in V:
            d[3 * ix[u] + k] = F(1)
        diag.append(d)
    assert all(in_span(d, span_basis(fld)) for d in diag)
    print(f"        (diagonal-in-family: asserted)")

    # does it MOVE the failure?
    rg = random.Random(424242)
    moved = kept = illegal = 0
    for trial in range(6):
        co = [rquat(rg) for _ in fld]
        tf = [sum((k * bb[i] for k, bb in zip(co, fld)), F(0))
              for i in range(3 * len(V))]
        pl = {u: [placed0[u][k] + tf[3 * ix[u] + k] for k in range(3)]
              for u in V if u != v}
        q = crit_from_placement(edges, v, pl, nrm0, 800000 + trial)
        if not q['target-rank']:
            illegal += 1
        elif q['dim R_a'] == 0:
            kept += 1
        else:
            moved += 1
    print(f"        6 seeded fields applied to the forced-failure seed: "
          f"{moved} moved OFF dim R_a = 0 (the forced failure is GONE), "
          f"{kept} stayed at dim R_a = 0, {illegal} lost target rank")
    print(f"        (contrast --inv: the GLOBAL shear moved dim R_a at 0 of "
          f"45 (seed, shear) pairs.  Same 3 coordinates per body; the")
    print(f"        difference is entirely whether they are SHARED.)")
    print("\n   => among per-body TRANSLATIONS, the maximal carrier-preserving")
    print("      family acts SIMPLY TRANSITIVELY on the fixed-normal slice of")
    print("      the pencil chart (§(K-slide) *Step 1(e)*'s linear-fiber tower")
    print("      with the normals frozen), so it IS that slice re-labelled.")
    print("      It is NOT a symmetry of the criterion -- it moves dim R_a --")
    print("      so it gives DEFORMATION, which the arc already has, and no")
    print("      propagation.")
    print("      The dichotomy: a group that preserves the criterion cannot")
    print("      move a failure; a family that moves a failure cannot")
    print("      propagate a witness.")
    print(f"   [{time.time() - t0:.1f}s]")


def main():
    if '--iso' in sys.argv:
        driver_iso()
    elif '--bed' in sys.argv:
        driver_bed()
    elif '--inv' in sys.argv:
        driver_inv()
    elif '--prod' in sys.argv:
        driver_prod()
    elif '--validate' in sys.argv:
        driver_iso(); print()
        driver_bed(); print()
        driver_inv(); print()
        driver_prod()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
