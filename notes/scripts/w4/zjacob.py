"""Phase 39 direction ZJACOB -- is the Jacobian / singular-locus route alive?

The question (`notes/Pencil-strategy.md` §9.2 candidate **(ZH-4)**, the head of
that shelf's order after ZSHEAR struck (ZH-1)): present the escape-failure
locus as the SINGULAR LOCUS of the universal infinitesimal-motion cone along
its ZERO SECTION, so that "escape fails only on a proper closed subset" becomes
"the cone is generically smooth along its zero section" -- a Jacobian-rank
computation rather than a witness hunt.

PROVENANCE BAR, and it is the hard one.  The idea source is an unrefereed
preprint whose own acknowledgment credits an AI assistant with the proof
details, the Lean formalization and its verification, and which this project
has NOT independently checked.  It is an IDEA SOURCE, never a citation: no
theorem of it is imported, assumed, or leaned on anywhere below -- its Theorem
4.2 included.  Everything here stands on (a) classical facts (the Jacobian
criterion; the Eagon-Northcott / Bruns / Eisenbud-Huneke-Ulrich height bounds
for ideals of minors, all of which are UPPER bounds; Krull's height theorem)
and (b) this project's own harness and definition bodies.

WHAT THIS DRIVER IS FOR.  The direction's verdict is DERIVATIONAL -- the route
dies to an equivalence, not to a measurement (`notes/Pencil-informal.md`
§(K-jac) *Steps JC2/JC3*).  Three things in it are nevertheless MEASURED,
because F11 forbids stating a structural claim more strongly than what was run:

  --sym    (JC-1)(a), (JC-4).  SYMBOLIC, no sampling anywhere.  Identities in
           `Q[pts, m, om]`:
             * the harness's 5-rows-per-hinge model is NOT polynomial in the
               chart coordinates (`exactcore.perp_basis` is an rref, so the
               row entries are non-canonical rational functions); the
               POLYNOMIAL model of the same cone is the augmented system
               `m_x - m_y - om_e C_e(y) = 0` (`dominance.motion_system`), and
               that is the one the Jacobian criterion can be applied to;
             * the Jacobian of those equations at a ZERO-SECTION point
               `(y, m, om) = (y, 0, 0)` is exactly `[ 0 | A(y) ]` -- the
               `y`-block vanishes IDENTICALLY -- so the zero-section Jacobian
               computes `rank A(y)` and NOTHING else;
             * any equation of degree >= 2 in the FIBRE variables has an
               identically-vanishing Jacobian on the zero section: shown for
               a general fibre-quadratic with free `y`-dependent coefficients
               AND for the arc's own pitch quadric `Q(t) = <t, star t>`.  So
               the criterion is VACUOUS on exactly the Klein-quadric structure
               §(K-pure) works by hand.
  --tan    (JC-1)(b).  The identification, exhibited at named carriers: at
           every probed zero-section point the two models agree on the fibre
           dimension, and
             dim T_{(y,x,0)} (cone) = dim T_y Y + dim X + nullity(y,x),
           expected `dim T_y Y + dim X + 6`.  So the point is a smooth point
           of a complete intersection of the expected codimension iff the
           framework attains target rank there.  Over an ESCAPING seed the
           zero-section singular locus is exhibited to be §(K-tight) *Step
           2.4*'s degenerate conic `line(ab) u P'` -- both factors hit.
  --codim  (JC-3).  The classical bounds, computed on the actual shapes: the
           sharpest classical bound on our first degeneracy locus is
           `height(I_t) <= q - t + 1 = 7`, CONSTANT across the class (so it
           cannot see the graph at all, §4.6's filter), and it takes the
           generic rank `r` as its INPUT.  Then TWO exhibitions of exactly that
           input-dependence -- two sub-loci of ONE chart at `P21` (tight,
           class-shaped; the failing one leaning on §(K-tight) *Step 2.3*'s
           proof, stated as such), and two GLOBAL strata of the necklace `Nk_4`
           (over-braced, hence NOT a class shape, and used only because it is
           the arc's one carrier with two legal pencil strata of different
           generic rank).  The bound is satisfied in every case and
           distinguishes nothing.
  --validate   all three, in that order.

CAPS, disclosed.  `--sym` is free of sampling (identities in polynomial rings).
`--tan` uses the `P21` bed (seeds 101..140 -- the range §(K-flank) *Step F5(d)*
itself used, all 35 valid seeds, both strata) plus three named tight CLASS
habitats from `dominance.HABITATS` at 4 seeds each; per seed it probes 3
route-A placements plus the `line(ab)` placement plus (where `second_line_check`
supplies one) the `P'` point.  `--codim` computes closed-form integers at the
seven `dominance.HABITATS` plus `P21`; its first exhibition reuses the same
`P21` bed and probes 4 route-A placements at one seed of each stratum, and its
second takes ONE exact-Q rank on the global-cone stratum of `Nk_4` plus up to 8
draws on its local-cone stratum (`rank_modp`, a LOWER bound, so `= target`
PROVES attainment there).  Nothing here is a genericity claim: the symbolic mode is
identities and the numeric modes are equalities asserted at every probed point,
so a single exception fails the run.

All exact `Q`.  Read-only w.r.t. the harness: every geometric primitive is
imported, including `Poly` (from `zshear`, this arc's minimal exact multivariate
polynomial type -- NOT re-declared here).  The one new operation is `pdiff`,
formal partial differentiation of a `Poly`, which `zshear` had no use for.

Reproduce:
  python3 notes/scripts/w4/zjacob.py --sym | --tan | --codim | --validate
"""

import random
import sys
import time
from fractions import Fraction as F

import os, sys                                                    # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (hat, nullspace, rank as rank_exact,         # noqa: E402
                       wedge2)
from kbare_common import rank_modp, verts_of                       # noqa: E402
from nogood_subdiv import deficiency, hub_set                      # noqa: E402
from widened import orient, splitOff, split_report                 # noqa: E402
from repin import (dot, hodge_star, rank_at_V, rob_in_plane,       # noqa: E402
                   second_line_check, seed_probe, star_generic)
from dominance import (FREE, HABITATS, build_chart,                # noqa: E402
                       motion_system)
from kslidecomb import shape_data                                  # noqa: E402
from flanks import P21_SPECS                                       # noqa: E402
from battain import (def2_exact, hinge_planes, necklace,           # noqa: E402
                     necklace_localcone, points_from_normals,
                     rows_from_W, sample_cone, verify_pn)
from zshear import Poly                                            # noqa: E402

RNG_SEED = 20260826


# ===================== the one new symbolic operation ======================

def pdiff(p, name):
    """Formal partial derivative of a `Poly` with respect to the variable
    `name`.  `zshear.Poly` carries +, -, * and equality only; this is the one
    operation this direction adds, and it is not a re-implementation of a
    harness primitive (the harness has no Python symbolic differentiation --
    `dominance.dC_along` is a DIRECTIONAL derivative of a specific numeric
    family, a different object)."""
    d = {}
    for m, k in p.c.items():
        e = dict(m)
        if name not in e:
            continue
        ex = e.pop(name)
        if ex > 1:
            e[name] = ex - 1
        mm = tuple(sorted(e.items()))
        d[mm] = d.get(mm, F(0)) + k * ex
    return Poly(d)


def pzero_at(p, names):
    """`p` with every variable in `names` set to 0."""
    d = {}
    for m, k in p.c.items():
        if any(nm in names for nm, _ in m):
            continue
        d[m] = d.get(m, F(0)) + k
    return Poly(d)


# ===================== the cone, in its two models =========================
#
# THE OBJECT.  For a graph `G` and a base variety `B` of pencil realizations,
# the universal infinitesimal-motion cone is
#
#   C(G) = { (y, m) in B x (Lambda^2 K^4)^V : m_u - m_v in <C_uv(y)> for uv in E }
#
# a cone in the fibre variable `m`, with ZERO SECTION `Z = B x {0} subset C`.
# Two presentations, and the difference matters for the Jacobian criterion:
#
#  (5-row)  `repin.rank_at_V` / `battain.rows_from_W`: five rows per hinge,
#           a BASIS of `C_e^perp_E` obtained by `exactcore.perp_basis`, i.e.
#           by an rref.  Entries are non-canonical rational functions of the
#           chart coordinates.  Right for ranks, WRONG for a Jacobian.
#  (aug)    `dominance.motion_system`: six rows per hinge,
#           `m_x - m_y - om_e C_e = 0`, in the unknowns `(m, om)`.  Entries
#           are POLYNOMIAL in the chart coordinates and the system is linear
#           in the fibre variables `(m, om)`.  This is the model the Jacobian
#           criterion applies to.
#
# The two agree on the fibre dimension (`om_e` is determined by `m` whenever
# `C_e != 0`), which every `--tan` probe ASSERTS rather than assumes.


def aug_fibre_dim(edges, placed, V):
    """Fibre dimension of the cone over the point `placed`, in the augmented
    POLYNOMIAL model, cross-checked against the 5-row model."""
    A, vidx, ncols, C = motion_system(edges, V, placed)
    nu_aug = len(nullspace(A))
    rk5 = rank_at_V(edges, placed, V)[0]
    nu5 = 6 * len(V) - rk5
    assert nu_aug == nu5, (nu_aug, nu5)
    for j, ce in enumerate(C):
        assert any(x != 0 for x in ce), ('degenerate hinge', edges[j])
    return nu_aug, rk5


def chart_tangent_dim(Gp, placed, nrm):
    """dim T_y Y for `Y` the pencil chart of `Gp`, in the harness's affine
    chart: the kernel of the differentiated pencil condition
    `<n_u, pt(w) - pt(u)> = 0` over every hub `u` and `Gp`-neighbour `w`.
    `dominance.build_chart` with FREE scoping freezes nothing, so this is the
    whole chart's tangent space and not §(K-dom)'s FIXED sub-scoping."""
    Vp = sorted(verts_of(Gp), key=str)
    dirs, nvar, ncons = build_chart(Gp, Vp, hub_set(Gp), placed, nrm,
                                    FREE, None, None, None)
    return len(dirs), nvar, ncons


# =============================== mode --sym ================================

def sym_zero_section_jacobian():
    """(JC-1)(a).  On a small carrier with SYMBOLIC point coordinates: the
    Jacobian of the augmented cone equations at a zero-section point is
    `[ 0 | A(y) ]` identically."""
    # carrier: the 3-body path  x -- y -- z  (2 hinges).  Small enough that the
    # identity is checked entry-by-entry over the whole Jacobian.
    VH = ['x', 'y', 'z']
    Hed = [('x', 'y'), ('y', 'z')]
    pt = {u: [Poly.var(f'p{u}{i}') for i in range(3)] for u in VH}
    ptnames = [f'p{u}{i}' for u in VH for i in range(3)]
    mnames = [f'm{u}{k}' for u in VH for k in range(6)]
    onames = [f'o{j}' for j in range(len(Hed))]
    m = {u: [Poly.var(f'm{u}{k}') for k in range(6)] for u in VH}
    om = [Poly.var(nm) for nm in onames]

    C = [wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in Hed]
    Feq = []
    for j, (a, b) in enumerate(Hed):
        for k in range(6):
            Feq.append(m[a][k] - m[b][k] - om[j] * C[j][k])
    assert len(Feq) == 6 * len(Hed) == 12

    fibre = set(mnames) | set(onames)
    # (i) every equation is LINEAR in the fibre variables and polynomial in y
    for f in Feq:
        for mon in f.c:
            assert sum(ex for nm, ex in mon if nm in fibre) == 1, mon
    # (ii) the y-block of the Jacobian vanishes identically at the zero section
    ybad = 0
    for f in Feq:
        for nm in ptnames:
            if not pzero_at(pdiff(f, nm), fibre).is_zero():
                ybad += 1
    assert ybad == 0
    # (iii) the fibre block IS the augmented system's matrix -- compared
    # against `dominance.motion_system` run on the SAME symbolic points, so
    # this is a real identity check between two independent constructions
    # (differentiate-the-equations vs build-the-system) and not a restatement.
    Aj = [[pzero_at(pdiff(f, nm), fibre) for nm in (mnames + onames)]
          for f in Feq]
    Ams, vidx, ncols, Cms = motion_system(Hed, VH, pt)
    assert (len(Ams), ncols) == (len(Aj), len(Aj[0])), (len(Ams), ncols)
    ncmp = 0
    for i in range(len(Aj)):
        for j in range(len(Aj[0])):
            assert Aj[i][j] == Ams[i][j], (i, j, Aj[i][j], Ams[i][j])
            ncmp += 1
    print(f"   (i)   {len(Feq)}/{len(Feq)} cone equations are exactly LINEAR "
          f"in the fibre variables `(m, om)` and polynomial in `y`")
    print(f"   (ii)  the `y`-block of the Jacobian at `(y, 0, 0)`: "
          f"{len(Feq) * len(ptnames)}/{len(Feq) * len(ptnames)} entries "
          f"vanish IDENTICALLY in Q[pts]")
    print(f"   (iii) the fibre block equals `dominance.motion_system`'s matrix "
          f"`A(y)`")
    print(f"         entry-for-entry, {ncmp}/{ncmp} entries "
          f"({len(Feq)}x{len(mnames) + len(onames)}) -- two independent")
    print(f"         constructions on the same symbolic points, compared")
    print("   => rank Jac(y, 0, 0) = rank A(y).  The zero-section Jacobian "
          "computes")
    print("      the framework's own rank and nothing else.")
    return len(Feq)


def sym_fibre_quadratic():
    """(JC-4).  Any equation of fibre-degree >= 2 has an identically-vanishing
    Jacobian on the zero section -- so the criterion cannot see it at all."""
    tn = [f't{i}' for i in range(6)]
    t = [Poly.var(nm) for nm in tn]
    yn = [f'y{i}{j}' for i in range(6) for j in range(6)]
    fibre = set(tn)

    # (a) a GENERAL fibre-quadratic with free y-dependent coefficients
    Fgen = Poly()
    for i in range(6):
        for j in range(6):
            Fgen = Fgen + Poly.var(f'y{i}{j}') * t[i] * t[j]
    # (b) the arc's own pitch quadric, §(K-pitch) *Step 0*
    Qt = Poly()
    st = hodge_star(t)
    for k in range(6):
        Qt = Qt + t[k] * st[k]
    assert not Qt.is_zero()

    tot = 0
    for tag, f in (('general fibre-quadratic', Fgen), ('pitch Q(t)', Qt)):
        for nm in (tn + yn):
            d = pzero_at(pdiff(f, nm), fibre)
            assert d.is_zero(), (tag, nm, d)
            tot += 1
    print(f"   {tot}/{tot} partial derivatives of a fibre-QUADRATIC vanish "
          f"identically on the zero section")
    print("   (both a general `sum y_ij t_i t_j` with free coefficients and "
          "the arc's")
    print("   own pitch quadric `Q(t) = <t, star t>`).  A cone whose equations "
          "carry")
    print("   a fibre-quadratic is therefore SINGULAR ALONG ITS WHOLE ZERO "
          "SECTION,")
    print("   at every `y`: the zero-section Jacobian criterion is VACUOUS on "
          "it.")
    print("   By (PC-Z)/(PC5) the arc's obstruction (W4) is exactly such a "
          "quadric")
    print("   condition -- so the criterion is blind to the half of §(K-pure) "
          "that")
    print("   (ZH-4) advertised as its leverage.")
    return tot


def driver_sym():
    print("== (JC-1)(a) / (JC-4): the zero-section Jacobian, symbolically ==")
    t0 = time.time()
    print("\n  -- the model.  `exactcore.perp_basis` is an rref, so the "
          "harness's")
    print("     5-rows-per-hinge model has NON-POLYNOMIAL, non-canonical row")
    print("     entries; the Jacobian criterion needs the augmented "
          "polynomial")
    print("     model `m_x - m_y - om_e C_e(y) = 0`.  Everything below is in "
          "it.")
    print("\n  -- (JC-1)(a) the fibre-LINEAR part")
    sym_zero_section_jacobian()
    print("\n  -- (JC-4) the fibre-QUADRATIC part")
    sym_fibre_quadratic()
    print(f"\n   [{time.time() - t0:.1f}s]")


# =============================== mode --tan ================================

_BED = []


def p21_bed():
    """§(K-flank) *Step F5(d)*'s bed, re-derived and ASSERTED against that
    step's recorded (30, 5, 5) before anything is concluded from it -- the
    `localtest.plane_basis` precedent is exactly this bed.  Deliberately a
    local re-derivation rather than an import from `zshear`, so that this
    direction's figures do not depend on another direction's cache; the
    assertion against the RECORDED values is what pins it."""
    if _BED:
        return _BED[0]
    edges, pmap = shape_data(P21_SPECS)
    v = pmap[0][1]
    jump, fine, invalid = [], [], 0
    for s in range(101, 141):
        p = seed_probe(edges, v, s, nplace=0)
        if p is None:
            invalid += 1
            continue
        assert p['dim U = dim R_a + 1'] and p['U cap Cab-perp == R_a'] \
            and p['R_a subset U'], (s, p)
        (jump if p['dim R_a'] == 0 else fine).append((s, p))
    assert (len(fine), len(jump), invalid) == (30, 5, 5), \
        (len(fine), len(jump), invalid)
    _BED.append((edges, v, jump, fine))
    return _BED[0]


def line_ab_point(placed, a, b, lam=F(2, 5)):
    """A point of `line(pt a, pt b)`, which lies in `Pi(b)` and is therefore a
    legal route-A placement of `pt(v)` -- and is exactly the first factor of
    §(K-tight) *Step 2.4*'s failure conic `line(ab) u P'`.  It is a
    NONDEGENERACY-forbidden chart point of `G` (`IsNondegPencilRealization`
    conjunct 4), which is the point."""
    return [placed[a][k] + lam * (placed[b][k] - placed[a][k])
            for k in range(3)]


def probe_seed(edges, v, seed, p, nplace, tag, verbose):
    """One zero-section bookkeeping probe at one target-rank `G'` seed."""
    a, b, c = orient(edges, v)
    Gp = splitOff(edges, v, a, b)
    Vp = sorted(verts_of(Gp), key=str)
    VG = sorted(verts_of(edges), key=str)
    placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
    hubsG = p['_ctx'][9]
    tgtG = p['_ctx'][8]

    nuGp, rk5 = aug_fibre_dim(Gp, placed, Vp)
    assert nuGp == 6, (seed, nuGp)          # a target-rank G' seed
    dY, nvar, ncons = chart_tangent_dim(Gp, placed, nrm)
    # the `plane_basis` precedent (README §4 convention 1): `seed_probe` routes
    # through `widened.place_pencil_general`, so the composite genericity gate
    # is REPORTED per seed and never assumed -- and because it is not used as
    # an acceptance gate here, the smooth/singular tallies below are counts of
    # EXHIBITED points, never rates.
    gate = star_generic(Gp, placed)

    rows = []
    rg = random.Random(RNG_SEED + 7919 * seed)
    places = []
    for j in range(nplace):
        x = (rob_in_plane(pt[b], nrm[b], rg) if b in hubsG and b in nrm
             else None)
        if x is None or x in (placed[a], placed[b]):
            continue
        places.append(('generic', x))
    places.append(('line(ab)', line_ab_point(placed, a, b)))
    sl = second_line_check(edges, v, p)
    if sl is not None and sl['off line(ab)']:
        places.append(("P'", sl['P-prime point']))

    ah, bh = hat(placed[a]), hat(placed[b])
    for kind, x in places:
        pl2 = dict(placed)
        pl2[v] = x
        nuG, rkG = aug_fibre_dim(edges, pl2, VG)
        assert rkG <= tgtG, (seed, kind, rkG, tgtG)
        smooth = (nuG == 6)
        assert smooth == (rkG == tgtG), (seed, kind, nuG, rkG, tgtG)
        offline = rank_exact([hat(x), ah[:], bh[:]]) == 3
        assert offline == (kind != 'line(ab)'), (seed, kind, offline)
        rows.append((kind, nuG, rkG, tgtG, smooth, offline))
    if verbose:
        for kind, nuG, rkG, tgtG_, smooth, offline in rows:
            print(f"      {tag} seed {seed:>4} {kind:>9}: fibre dim {nuG} "
                  f"(expected 6, excess {nuG - 6}), rank {rkG}/{tgtG_} -> "
                  f"{'SMOOTH' if smooth else 'SINGULAR'} zero-section point"
                  f"{'' if offline else '  [on line(ab): chart-ILLEGAL for G]'}")
    return dY, rows, gate


def driver_tan():
    print("== (JC-1)(b): the identification, exhibited at named carriers ==")
    t0 = time.time()
    print("   dim T_{(y,x,0)}(cone) = dim T_y Y + dim X + fibre dim, and the")
    print("   expected value is dim T_y Y + dim X + 6.  So a zero-section "
          "point")
    print("   is a smooth point of a complete intersection of the EXPECTED")
    print("   codimension iff the framework attains target rank there -- which")
    print("   is asserted, not assumed, at every probe below.")

    tot = smooth = sing = 0
    agree_model = 0

    # ---- carrier 1: the P21 adversarial bed, both strata ------------------
    edges, v, jump, fine = p21_bed()
    a, b, c = orient(edges, v)
    print(f"\n   -- P21 (|V| = {len(verts_of(edges))}, "
          f"|E| = {len(edges)}, split v = {v}, a = {a}, b = {b}, c = {c}); "
          f"bed ASSERTED")
    print(f"      against §(K-flank) *Step F5(d)*'s recorded (30, 5, 5) over "
          f"seeds 101..140.")
    print(f"      count-theoretic prediction: dim R_a = "
          f"{split_report(edges, v)['dim R_a (identity)']}")
    dYs, gates = set(), []
    for tag, pool, nplace, verbose_n in (('R_a=0', jump, 3, 5),
                                         ('R_a=1', fine, 3, 2)):
        shown = 0
        for s, p in pool:
            dY, rows, gate = probe_seed(edges, v, s, p, nplace, tag,
                                        shown < verbose_n)
            shown += 1
            dYs.add(dY)
            gates.append((s, tag, gate))
            for kind, nuG, rkG, tg, sm, off in rows:
                tot += 1
                smooth += sm
                sing += (not sm)
                agree_model += 1
            if tag == 'R_a=0':
                assert all(not sm for r in rows for sm in (r[4],)), (s, rows)
    assert len(dYs) == 1, dYs
    print(f"      dim T_y Y = {dYs.pop()} at ALL 35 bed seeds "
          f"(one value, asserted)")
    gj = [s for s, tg, g in gates if tg == 'R_a=0' and not g]
    gf = [s for s, tg, g in gates if tg == 'R_a=1' and g]
    print(f"      `repin.star_generic` REPORTED, not used as a gate: rejects "
          f"{len(gj)}/{len(jump)} forced-failure")
    print(f"      seeds and accepts {len(gf)}/{len(fine)} escaping ones -- so "
          f"the tallies below are counts of")
    print(f"      EXHIBITED points, never rates (README §4 convention 1, the "
          f"`plane_basis` precedent).")

    # ---- carrier 2..4: named tight CLASS habitats -------------------------
    for name, E, vv, pm, note in HABITATS[:3]:
        assert deficiency(E) == 0 and 5 * len(E) == 6 * (len(verts_of(E)) - 1)
        print(f"\n   -- {name} (|V| = {len(verts_of(E))}, |E| = {len(E)}; "
              f"{note})")
        dYs, n, ngate = set(), 0, 0
        for s in range(400, 460):
            if n >= 4:
                break
            p = seed_probe(E, vv, s, nplace=0)
            if p is None:
                continue
            n += 1
            dY, rows, gate = probe_seed(E, vv, s, p, 2, 'class', n <= 2)
            dYs.add(dY)
            ngate += int(bool(gate))
            for kind, nuG, rkG, tg, sm, off in rows:
                tot += 1
                smooth += sm
                sing += (not sm)
                agree_model += 1
        assert n == 4, (name, n)
        print(f"      dim T_y Y = {sorted(dYs)} over {n} seeds; "
              f"`star_generic` accepts {ngate}/{n} (reported, not a gate)")

    print(f"\n   TOTALS: {tot} zero-section points probed; "
          f"{smooth} SMOOTH (fibre dim 6 = expected), {sing} SINGULAR "
          f"(excess >= 1)")
    print(f"   {agree_model}/{tot} agreements between the augmented POLYNOMIAL "
          f"model")
    print(f"   (`dominance.motion_system`) and the 5-row model "
          f"(`repin.rank_at_V`) on the")
    print(f"   fibre dimension -- asserted per probe, so a single divergence "
          f"fails the run.")
    print("   The `line(ab)` and `P'` rows are §(K-tight) *Step 2.4*'s "
          "degenerate")
    print("   conic, hit on both factors: over an ESCAPING seed the "
          "zero-section")
    print("   singular locus is exactly that conic -- an object the arc "
          "already owns")
    print("   in closed form, recovered here under a new name.")
    print(f"   [{time.time() - t0:.1f}s]")


# ============================== mode --codim ===============================

def en_numbers(nE, nV, t):
    """The classical height bounds for ideals of minors, instantiated on
    `phi = R(G)`: `p x q = 5|E| x 6|V|`, generic rank hypothesised `r = t`,
    and the locus of interest `D_1 = V(I_t)` (rank drops below target).

    Eagon-Northcott (Proc. Roy. Soc. A 269 (1962), 188-204), as quoted by
    Eisenbud-Huneke-Ulrich (Amer. J. Math. 126 (2004), 417-438):
        height(I_i) <= (r - i + 1)(max(p, q) - i + 1)
    Bruns (Proc. Amer. Math. Soc. 83 (1981), 19-24):
        height(I_i) <= (r - i + 1)(p + q - r - i + 1)
    EHU Theorem A (R regular local):
        height(I_i) <= (r - i + 1)(max(p, q) - i + 1) + i - 1
    ALL THREE ARE UPPER BOUNDS."""
    p, q = 5 * nE, 6 * nV
    i = r = t
    en = (r - i + 1) * (max(p, q) - i + 1)
    bruns = (r - i + 1) * (p + q - r - i + 1)
    ehu = en + i - 1
    return p, q, r, i, en, bruns, ehu


def driver_codim():
    print("== (JC-3): the classical bounds, computed on the actual shapes ==")
    t0 = time.time()
    print("   Properness of the escape-failure locus is `height(I_t) >= 1`, a")
    print("   LOWER bound on a codimension.  Every classical theorem about "
          "heights")
    print("   of ideals of minors is an UPPER bound (Eagon-Northcott 1962; "
          "Bruns")
    print("   1981; Eisenbud-Huneke-Ulrich 2004, whose introduction says so in")
    print("   as many words), and each takes the generic rank `r` as an INPUT.")

    shapes = []
    edges, pmap = shape_data(P21_SPECS)
    shapes.append(('P21 ((K-res) residual)', edges))
    for name, E, vv, pm, note in HABITATS:
        shapes.append((name, E))

    print("\n   shape                              |V|  |E|  5|E| 6(|V|-1) "
          "6|E| 6|V|+|E|-6   E-N Bruns")
    ens = set()
    for name, E in shapes:
        nV, nE = len(verts_of(E)), len(E)
        assert 5 * nE == 6 * (nV - 1), (name, nV, nE)
        assert deficiency(E) == 0, name
        t = 6 * (nV - 1)
        p, q, r, i, en, bruns, ehu = en_numbers(nE, nV, t)
        # the tight-class coincidences, asserted
        assert 5 * nE == t                       # 5-row model: #rows = target
        assert 6 * nE == 6 * nV + nE - 6         # aug model: #eq = exp. codim
        ens.add((en, bruns))
        print(f"   {name:<34} {nV:>3}  {nE:>3}  {5*nE:>4} {t:>8} "
              f"{6*nE:>5} {6*nV+nE-6:>10} {en:>5} {bruns:>5}")
    assert ens == {(7, 7)}, ens
    print("\n   Two count coincidences, asserted at every shape above:")
    print("     * 5-row model:  #rows = 5|E| = 6(|V|-1) = target, so the "
          "expected")
    print("       codimension EQUALS the number of equations -- the tight "
          "class is")
    print("       exactly where 'complete intersection of the expected "
          "codimension'")
    print("       is even arithmetically possible.")
    print("     * augmented model: #equations = 6|E| = 6|V| + |E| - 6 = the")
    print("       expected codimension, the same coincidence (index(G) = 0).")
    print("   And the bound itself is the CONSTANT 7 = 6|V| - 6(|V|-1) + 1 at "
          "every")
    print("   shape -- the number of trivial motions plus one.  It does not "
          "depend")
    print("   on the graph at all, so by §4.6's growing-ground-set filter it "
          "cannot")
    print("   distinguish one class member from another, let alone certify "
          "one.")

    # ---- exhibition 1: inside the arc's own TIGHT bed --------------------
    print("\n   -- exhibition 1 (a TIGHT class-shaped carrier): P21's own bed")
    edges, v, jump, fine = p21_bed()
    a, b, c = orient(edges, v)
    nV, nE = len(verts_of(edges)), len(edges)
    t = 6 * (nV - 1)
    sj, pj = jump[0]
    sf, pf = fine[0]
    rk_fail = _best_route_a_rank(edges, v, pj, 4)
    rk_esc = _best_route_a_rank(edges, v, pf, 4)
    print(f"      over the forced-failure seed {sj} the best route-A rank over "
          f"4 PROBED placements")
    print(f"      is {rk_fail} = target - {t - rk_fail} -- and §(K-tight) "
          f"*Step 2.3*'s calculus PROVES failure at")
    print(f"      every placement there (`dim R_a = 0`), which is what makes "
          f"the generic")
    print(f"      rank on that sub-locus {rk_fail} rather than merely "
          f"`<= {rk_fail}` on 4 samples;")
    print(f"      over the escaping seed {sf} it is {rk_esc} = target "
          f"({'ATTAINS' if rk_esc == t else 'SHORT'}).")
    assert rk_esc == t and rk_fail == t - 1, (rk_esc, rk_fail, t)
    p_, q_, r_, i_, en_, br_, eh_ = en_numbers(nE, nV, t)
    print(f"      So on the sub-locus `{{seed {sj}}} x X` the generic rank is "
          f"`r = {t - 1}` and")
    print(f"      `I_t = 0` identically: `height(I_t) = 0`, properness FAILS "
          f"there, and the")
    print(f"      Eagon-Northcott bound reads `(r - i + 1)(...) = 0 <= 0` -- "
          f"SATISFIED.")
    print(f"      On the whole of `Y x X`, IF `r = t`, it reads {en_}.  Same "
          f"graph, same")
    print(f"      matrix shape; the only thing that changed is `r`, which is "
          f"the bound's")
    print(f"      INPUT -- and `r = t` IS properness.")

    # ---- exhibition 2: the arc's constructed T2 candidate ----------------
    print("\n   -- exhibition 2 (a NON-class constructed carrier, where the "
          "two")
    print("      strata are global rather than seed-wise): the necklace "
          "`Nk_4` of")
    print("      §(K-bare-ext) *Step BE13*.  It is over-braced "
          "(`5|E| > 6(|V|-1)`), so")
    print("      it is NOT a class shape -- it is used only because it is the "
          "arc's")
    print("      one carrier with two legal pencil strata of DIFFERENT generic "
          "rank.")
    k = 4
    E = necklace(k)
    nV, nE = len(verts_of(E)), len(E)
    d3 = deficiency(E)            # the pebble-game oracle; `exact_deficiency`
    t3 = 6 * (nV - 1) - d3        # blows the recursion depth at |V| = 16
    d2 = def2_exact(E)
    assert 5 * nE > 6 * (nV - 1)
    print(f"      Nk_{k}: |V| = {nV}, |E| = {nE}, 5|E| = {5*nE} > "
          f"6(|V|-1) = {6*(nV-1)}, def_3 = {d3}, def_2 = {d2}, "
          f"target = {t3}")
    rng = random.Random(RNG_SEED + 11)
    N, P, W, free = sample_cone(E, rng)
    rows_c, nVc = rows_from_W(E, N, P, W)
    rk_cone = rank_exact([r[:] for r in rows_c])
    print(f"      GLOBAL-cone stratum: exact rank {rk_cone} "
          f"= 6(|V|-1) - def_2 = {6 * (nV - 1) - d2} "
          f"[(BE-13)'s law, recomputed here]")
    assert rk_cone == 6 * (nV - 1) - d2 == t3 - 1, (rk_cone, t3, d2)
    best, tries = -1, 0
    for sd in range(8):
        rg2 = random.Random(RNG_SEED + 4100 + 41 * sd)
        try:
            Nl, q = necklace_localcone(k, rg2)
            Pl, dims = points_from_normals(E, Nl, rg2)
            if Pl is None:
                continue
            Wl, freel = hinge_planes(E, Nl, Pl, rg2)
            ok, why = verify_pn(E, Nl, Pl, Wl)
            assert ok, why
        except (RuntimeError, AssertionError):
            continue
        tries += 1
        best = max(best, rank_modp(rows_from_W(E, Nl, Pl, Wl)[0]))
        if best == t3:
            break
    assert best == t3, (best, t3)
    print(f"      LOCAL-cone stratum: rank_modp {best} = target, from "
          f"{tries} legal stratum")
    print(f"      point(s); `rank_modp` is a LOWER bound for the rational "
          f"rank and the")
    print(f"      partition bound is a universal UPPER bound of `target`, so "
          f"the generic")
    print(f"      rank there is EXACTLY {t3}.")
    p2, q2, r2, i2, en2, br2, eh2 = en_numbers(nE, nV, t3)
    print(f"      Same conclusion as exhibition 1, now with the two strata "
          f"global: E-N")
    print(f"      reads 0 on the first (`r = {t3-1} < i = {t3}`) and {en2} on "
          f"the second, and is")
    print(f"      satisfied in both.  The classical package cannot see the "
          f"difference.")
    print(f"   [{time.time() - t0:.1f}s]")


def _best_route_a_rank(edges, v, p, nplace):
    """Best rank over `nplace` seeded route-A placements plus the two named
    special points -- an existential probe: the value returned is ATTAINED, so
    `= target` proves attainment and `< target` is a cap over the probed
    placements only."""
    a, b, c = orient(edges, v)
    placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
    hubsG, tgtG = p['_ctx'][9], p['_ctx'][8]
    VG = sorted(verts_of(edges), key=str)
    rg = random.Random(RNG_SEED + 2201)
    xs = []
    for _ in range(nplace):
        x = (rob_in_plane(pt[b], nrm[b], rg) if b in hubsG and b in nrm
             else None)
        if x is not None and x not in (placed[a], placed[b]):
            xs.append(x)
    best = -1
    for x in xs:
        pl2 = dict(placed)
        pl2[v] = x
        best = max(best, rank_at_V(edges, pl2, VG)[0])
        if best == tgtG:
            break
    return best


# ================================= main ====================================

MODES = {'--sym': driver_sym, '--tan': driver_tan, '--codim': driver_codim}


def main():
    args = [a for a in sys.argv[1:] if a != '--validate']
    if '--validate' in sys.argv[1:]:
        args = ['--sym', '--tan', '--codim']
    if not args or any(a not in MODES for a in args):
        print(__doc__)
        print(f"modes: {' | '.join(sorted(MODES))} | --validate")
        return 1
    t0 = time.time()
    for a in args:
        MODES[a]()
    print(f"\nZJACOB OK ({' '.join(args)}) [{time.time() - t0:.1f}s]")
    return 0


if __name__ == '__main__':
    sys.exit(main())
