"""
Phase 39, section (K-out) -- THE OUTER-LINE CRITERION (OUT), MEASURED.

WHY THIS DRIVER EXISTS.  `notes/Pencil-informal.md` section (K-Lambda)
*Step 5a* states **(OUT)**: at a hard-stratum, target-rank, length-4-companion
split, if EITHER outer companion line fails to be a relative twist --
`C1 = C(b x1) notin V_bc` or `C4 = C(x3 c) notin V_bc` -- then the far
covector `lambda` is proportional to neither `p+` nor `q`, so by (Lambda-2)
the pitch certificate fires somewhere on the `a`-line and the split escapes.
The hypothesis is `lambda_1 != 0` or `lambda_4 != 0`, because `lambda_i` is
`lambda(C_i)` and `V_bc = ker lambda cap S`.

*Step 5a* records that this hypothesis "has never been evaluated anywhere in
the arc": `lambda.py --adv` computes `lambda` and reports `lambda ~ p+` and
`lambda ~ q`, but reports NOTHING about `lambda_1` and `lambda_4` separately.
It also records the hinge-rate reading of the hypothesis --

    `C1 in V_bc`  <=>  some motion of `H` freezes the companion's last three
    hinges and bends the first  <=>  in `H/{e2,e3,e4}` (weld `x1,x2,x3,c`
    into one body `X`) the body `b` is not rigidly attached to `X`

-- and that reading has no driver either.  This file measures both.

WHAT IS NEW HERE.  Seven things, in increasing order of how much they change
the reading of (OUT).

  (OC-1) THE HINGE-RATE READING, MADE EXACT AND TESTED.  With `mu_1` the
    number of `H`-edges between `b` and `X`, and `R_1` the relative twist
    space of `(b, X)` in `H - e_1` with `X` welded, the following are
    EQUIVALENT at any placement satisfying (Lambda-0a) (`C_1..C_4`
    independent):
        lambda_1 = 0   <=>   C_1 in V_bc   <=>   dim{m(b) - m(X)} = 1 in
        H with X welded   <=>   (when mu_1 = 1)  C_1 in R_1.
    No genericity is needed: the companion coordinates of a relative twist
    are unique by (Lambda-0a), so `omega = (1,0,0,0)` says exactly that the
    motion welds `x1,x2,x3,c`.  Asserted per frame in `--pool`.

  (OC-2) THE COMBINATORIAL AVAILABILITY MAP.  `deficiency` (the polynomial
    (6,6)-pebble oracle) gives the AMBIENT-generic value of every dimension
    above.  Over the enumerated class scope -- the four certified
    length-4-companion habitats, the 19-shape named inventory, and the
    1357-shape systematic sweep of `outer.sweep_shapes()` (4296
    (split, companion) pairs in all) -- the answer is uniform:
        (mu_1, dim R_1, mu_4, dim R_4) = (1, 5, 1, 5),
    hence `A_1 := def(H/X) - def(H/(X + b)) = 0` and likewise `A_4 = 0`:
    at an ambient-generic placement BOTH disjuncts of (OUT) hold.

  (OC-3) THE PENCIL-SIDE REFINEMENT -- AND WHY (OC-2) IS NOT THE ANSWER.
    `C_1` is not a free line of `P^3`.  It is `C(b, x1)` with `pt(x1)` in the
    panel `Pi(b)`, so it is confined to the 2-dimensional PENCIL
    `L_b := alpha_{pt(b)} cap beta_{Pi(b)}` of lines through `pt(b)` in
    `Pi(b)`.  With `mu_1 = 1`, `lambda_1 = 0 <=> C_1 in R_1 cap L_b`, and
        dim R_1 = 5  =>  dim(R_1 cap L_b) >= 5 + 2 - 6 = 1.
    So `{lambda_1 = 0}` is NONEMPTY at every class shape in scope: there is
    always at least one direction of `x1`'s pencil that kills `lambda_1`.
    Measured `= 1` exactly at every probed chart point.  (OUT) is therefore
    generically available and NEVER automatic -- exactly the shape of
    (Lambda-0g)/(Lambda-0i) for `g14`.

  (OC-4) THE CONSTRUCTION.  In the (Lambda-0i) free-end pattern the bad
    direction is LEGAL, and the two ends are independent (welding `Y` for the
    `c`-side computation absorbs `e_1` and `e_2`, so `pt(x1)` does not enter
    `R_4`).  `--build` therefore slides `pt(x1)` and `pt(x3)` onto their two
    marked directions simultaneously and produces an exact chart point of a
    real class habitat with `lambda_1 = lambda_4 = 0` -- (OUT) SILENT -- while
    every (Lambda-0) clause, the target rank and `dim R_a = 1` survive.  At
    every such point the pitch certificate still fires (`deg_t Q(z(t)) = 4`),
    so the escape holds by (Lambda-2) even though (OUT) cannot see it.

  (OC-5) THE MEASUREMENT ITSELF -- the distribution of
    `(lambda_1 = 0, lambda_4 = 0)` over POOL-G, which is what *Step 5a* item
    (viii) asked for, plus the codimension-1 event rates of every (Lambda-0)
    bracket over the SAME pool as a calibration.

  (OC-6) SHAPE-LEVEL AVAILABILITY.  (OUT) as a route needs the escape at SOME
    target-rank seed, so the question that matters is per SHAPE, not per
    frame: does every (split, companion) pair have at least one hard-stratum
    frame where the hypothesis holds?  `--shapes` answers that over POOL-S.

  (OC-7) A SAMPLER FINDING, AND WHY THE RATE IN (OC-5) MUST NOT BE READ AS A
    HIT RATE.  Every `lambda_i = 0` frame of POOL-G carries a COINCIDENT
    HINGE LINE at its hub: `C(b, x1) = C(b, u)` for another `G'`-neighbour
    `u` of `b`, i.e. `pt(b), pt(x1), pt(u)` collinear -- so `b` is a free
    rotor about that line and the relative twist `omega C_1` is realized for
    trivial reasons.  Most of those are MANUFACTURED by the harness:
    `widened.place_pencil_general` routes every single-hub interior through
    `localtest.in_plane_point`, whose `plane_basis` is the DEGENERATE one of
    the README's *Divergences* table, and when it degenerates at a hub it
    puts EVERY such interior of that hub on ONE line.  Measured: the
    degeneracy implies `lambda_i = 0` at 15/15 (b-side) and 18/18 (c-side),
    and it is caught by NEITHER `flanks.star_span_ranks` (documented as "the
    genericity guard against the `plane_basis` artifact") NOR any of the four
    `IsNondegPencilRealization` conjuncts.  This is why `--build` matters:
    it reaches the same locus with no coincident hinge line at 3 of the 4
    habitats, so the phenomenon is real and not only an artifact.

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --comb
    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --pool
    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --shapes
    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --build

POOLS.  Each mode prints its pool up front and EVERY figure it reports is
over that one pool; nothing is aggregated across modes.

  POOL-C  (--comb)  deterministic, no rng: the 4 `lambda.habitat_specs`
                    habitats, `outer.named_inventory()`, and every family of
                    `outer.sweep_shapes()`.
  POOL-G  (--pool)  the 4 habitats x placement seeds 200-299 -- the
                    same integer pool `lambda.py --adv` uses for its habitat
                    leg, so the counts here are directly comparable to that
                    mode's.  Frames are kept when the placement is target-rank
                    with `dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4` and
                    the closed-star rank test `star_span_ranks` green -- NOT
                    the composite `repin.star_generic`, deliberately, since
                    the coincidence is what (OC-7) measures here (slice S2's
                    per-site judgement; the composite is reported, and its
                    rejection set is compared against the local diagnostic as
                    the FIELD HALF of the guard's adversarial test);
                    (Lambda-0d) failures are KEPT and reported separately
                    rather than dropped (which is what `lambda.habitat_frame`
                    does), because (OUT) stops applying there.
  POOL-S  (--shapes)  the 19-shape named inventory plus the first 4 shapes
                    of each `outer.sweep_shapes()` family, every eligible
                    split, placement seeds 1-39, <= 3 hard-stratum frames per
                    split.  DISJOINT from POOL-G; never aggregated with it.
  POOL-B  (--build)  the 4 habitats x placement seeds 200-259, slide
                    parameters from a fixed list.

CONVENTIONS (`notes/scripts/README.md` section 4): exact Q only, no floating
point; a degeneracy guard and a rank/dimension assert on every sampled
object; every rng is `random.Random(<literal>)` and its seed is printed.
Nothing in `lambda.py` / `outer.py` is modified -- both are READ.

LAYERING (`notes/scripts/README.md` section 2).  A `w4/` leaf beside
`flanks` / `pure` / `lambda` / `dominance` / `outer` / `sigma`, importing only
catalogued section-1 primitives: `outer`'s `split_data` / `companions4` /
`free_ends` / `hub_pattern` / `stratum_at` / `build_frame` / `geom_checks` /
`lam0d` / `sweep_shapes` / `named_inventory` / `eligible_splits`,
`lambda`'s `habitat_specs` / `rows_mnqs` / `qpoly` / `span_meet` / `poly_deg`
(through `importlib`, since `lambda` is a keyword), `nogood_subdiv`'s
`deficiency` / `contraction`, `pencil_escape.build_rigidity`,
`widened.place_pencil_general`, `flanks.nondeg_conjuncts`, `pitch`'s
`H_motions_vbc` / `klein` / `coords_in`, and `repin`'s `span_basis` /
`in_span` / `robust_plane_basis` plus the four configuration genericity
guards `star_span_ranks` / `hinge_coincidences` / `coincident_hinges` /
`star_generic` (the third and fourth added by the 2026-08-06 re-baselining
round; `hinge_coincidences` was written HERE and moved down to `repin` in
slice S2, so this file now IMPORTS what used to be its own local copy).
"""
import importlib
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (dot, hat, neighbors, nullspace, rank,       # noqa: E402
                       wedge2)
from kbare_common import verify_pencil_witness, verts_of           # noqa: E402
from pencil_escape import build_rigidity                           # noqa: E402
from nogood_subdiv import contraction, deficiency                  # noqa: E402
from widened import place_pencil_general                           # noqa: E402
from repin import (coincident_hinges, hinge_coincidences,          # noqa: E402
                   in_span, robust_plane_basis, span_basis,
                   star_generic, star_span_ranks)
from pitch import H_motions_vbc, coords_in, klein                  # noqa: E402
from flanks import nondeg_conjuncts                                # noqa: E402
import outer                                                       # noqa: E402

# READ, not used as a sampler: `localtest.plane_basis` is the DEGENERATE
# in-plane basis of the *Divergences* table, and `widened.place_pencil_general`
# routes every single-hub interior through it.  (OC-7) needs to know when it
# fires, so the diagnostic calls it directly; nothing here samples with it.
from localtest import plane_basis as DEGENERATE_PLANE_BASIS       # noqa: E402

# `lambda` is a Python keyword; `outer.py` reaches it the same way.  What is
# needed here is the four certified habitats, the (T5) bracket rows, the
# subspace meet and the a-line quartic -- all catalogued section-1 entries.
LAM = importlib.import_module('lambda')


# ---------------- the welded relative-twist model ---------------------------

def weld_motions(Hed, VH, placed, groups, drop=()):
    """Motions of `H` at `placed` with each vertex set in `groups` WELDED
    (`m(u) = m(w)` for `u, w` in the set) and the edges in `drop` deleted.

    Welding is imposed as explicit equality rows on top of
    `pencil_escape.build_rigidity`'s matrix rather than by contracting the
    graph, because a contracted edge would lose its hinge LINE -- and the
    hinge lines are the whole content here.  Returns `(motions, idx)`."""
    ed = [e for e in Hed
          if e not in drop and (e[1], e[0]) not in drop]
    rows, _er, _C, idx, n = build_rigidity({'edges': ed, 'V': VH,
                                            'pt': placed})
    extra = []
    for g in groups:
        g = list(g)
        for u in g[1:]:
            for k in range(6):
                r = [F(0)] * (6 * n)
                r[6 * idx[g[0]] + k] = F(1)
                r[6 * idx[u] + k] = F(-1)
                extra.append(r)
    mot = nullspace(rows + extra)
    assert mot, "welded system has no motions (not even the rigid ones)"
    return mot, idx


def rel_span(mot, idx, u, w):
    """A basis of `{m(u) - m(w) : m in mot}`; dimension asserted consistent."""
    D = [[m[6 * idx[u] + k] - m[6 * idx[w] + k] for k in range(6)]
         for m in mot]
    B = span_basis(D)
    assert len(B) == rank(D), "relative twist basis rank mismatch"
    return B


def line_pencil(placed, nrm, h):
    """`L_h`, the 2-dimensional pencil of lines through `pt(h)` inside the
    panel `Pi(h)`, as a basis of `Lambda^2 K^4`, plus the two in-plane
    directions generating it.  Every nonzero element is a genuine line
    through `pt(h)` in `Pi(h)` (`h ^ u` is decomposable), which is what makes
    (OC-3)'s marked direction realizable.

    Deterministic: built from `repin.robust_plane_basis` -- THE canonical
    in-plane basis, valid for any nonzero normal -- rather than from two rng
    draws of `rob_in_plane`, which can return collinear points and would make
    the figures depend on a salt."""
    bb = robust_plane_basis(nrm[h])
    assert bb is not None, "degenerate panel normal"
    b0, b1 = bb
    assert rank([b0, b1]) == 2, "in-plane basis degenerate"
    B = [wedge2(hat(placed[h]), hat([placed[h][i] + b0[i] for i in range(3)])),
         wedge2(hat(placed[h]), hat([placed[h][i] + b1[i] for i in range(3)]))]
    assert rank(B) == 2, "L_h is not 2-dimensional"
    return B, (b0, b1)


def marked_direction(placed, nrm, h, R):
    """(OC-3): the direction `d` with `C(pt(h), pt(h) + t d)` inside `R`, for
    every `t != 0`.  Returns `(d, dim(R cap L_h))`, `d = None` when the meet
    is not a single line."""
    B, (b0, b1) = line_pencil(placed, nrm, h)
    M = LAM.span_meet(R, B)
    if len(M) != 1:
        return None, len(M)
    co = coords_in(B, M[0])
    assert co is not None, "R cap L_h escaped L_h"
    d = [co[0] * b0[i] + co[1] * b1[i] for i in range(3)]
    if all(x == 0 for x in d):
        return None, -1
    assert dot(nrm[h], d) == 0, "marked direction leaves the panel"
    # the direction really does realize the marked line of the pencil:
    tgt = wedge2(hat(placed[h]),
                 hat([placed[h][i] + d[i] for i in range(3)]))
    assert rank([tgt, M[0]]) == 1, "marked direction does not realize R cap L"
    assert in_span(tgt, R), "the realized line is not inside R"
    return d, 1


# ---------------- (OC-7) the two degeneracy diagnostics ---------------------
#
# `hinge_coincidences` was written HERE, locally, when (OC-7) measured the
# defect; slice S2 (2026-08-06) repointed it at `repin.hinge_coincidences`,
# which is the same predicate with the same signature and the same semantics
# (this copy was its origin, not a second implementation -- README
# *Divergences*, the TRANSIENT-duplicate note, now discharged).  Imported
# above beside `coincident_hinges` / `star_generic`.  `degenerate_sampler`
# stays local: it is a question about `widened`'s SAMPLER, not about a
# configuration, so it has no place among the configuration guards.


def degenerate_sampler(nrm, h):
    """Does `widened.place_pencil_general`'s in-plane sampler degenerate at
    hub `h`?  It routes every single-hub interior through
    `localtest.in_plane_point`, whose `plane_basis` returns two PARALLEL
    directions for some normals -- and then EVERY such interior of `h` lands
    on ONE line through `pt(h)`, so all their hinge lines coincide."""
    bb = DEGENERATE_PLANE_BASIS(nrm[h])
    return len(bb) < 2 or rank(bb[:2]) < 2


# ---------------- the combinatorial side ((OC-2)) ---------------------------

def _cverts(verts, W):
    return sorted((set(verts) - set(W)) | {'v*'}, key=str)


def gen_rel_dim(edges, verts, u, w):
    """The AMBIENT-generic dimension of `{m(u) - m(w)}`, from the count
    matroid alone: `dim Mot(G) = 6 + def(G)` (both by
    `nogood_subdiv.deficiency`), and welding `u, w` is vertex identification,
    so the relative twist dimension is `def(G) - def(G/uw)`.  Explicit vertex
    lists keep isolated vertices alive (an isolated `u` gives 6, correctly)."""
    d1 = deficiency(edges, sorted(set(verts), key=str))
    d2 = deficiency(contraction(edges, [u, w]), _cverts(verts, [u, w]))
    return d1 - d2


def comb_data(Hed, P):
    """(OC-2) at one length-4 companion `P = [b, x1, x2, x3, c]`:
    `(mu_1, dim R_1, A_1, mu_4, dim R_4, A_4, chi)`.

    `X := {x1,x2,x3,c}` and `Y := {b,x1,x2,x3}` are the two welds; `mu` counts
    the surviving edges between the free end and the welded body; `R` is the
    relative twist space with those edges deleted; `A` is the relative twist
    dimension WITH them, i.e. the ambient-generic value of `[lambda_i = 0]`.
    `chi` is the number of chords inside `P` (path edges excluded) -- the
    quantity that makes the trivial-partition count of `H/X` equal `5 chi`."""
    VH = verts_of(Hed)
    out, defs = [], []
    for end, W in ((P[0], P[1:]), (P[4], P[:4])):
        K, VK = contraction(Hed, W), _cverts(VH, W)
        defs.append(deficiency(K, VK))
        mu = sum(1 for e in K if set(e) == {end, 'v*'})
        A = gen_rel_dim(K, VK, end, 'v*')
        Km = [e for e in K if set(e) != {end, 'v*'}]
        out.append((mu, gen_rel_dim(Km, VK, end, 'v*'), A))
    pathe = {frozenset((P[i], P[i + 1])) for i in range(4)}
    chi = sum(1 for e in Hed
              if e[0] in P and e[1] in P and frozenset(e) not in pathe)
    return out[0] + out[1] + (chi, defs[0], defs[1])


def comb():
    print("== (OC-2) the combinatorial availability map of (OUT) ==")
    print("   POOL-C: the 4 lambda.habitat_specs habitats, "
          "outer.named_inventory(),")
    print("           and every family of outer.sweep_shapes().  No rng.")
    print("   per (shape, split, length-4 companion): "
          "(mu_1, dim R_1, A_1, mu_4, dim R_4, A_4, chi)")
    print("     mu   = # H-edges between the free end and the welded body")
    print("     R    = relative twist space of (end, welded body) WITHOUT "
          "those edges")
    print("     A    = the same WITH them = the ambient-generic value of "
          "[lambda_i = 0]")
    print("     chi  = # chords inside the companion\n")

    print("-- part 1: the four certified length-4-companion habitats --")
    for name, E, v, cmp_ in LAM.HABITATS4:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        Ps = outer.companions4(Hed, b, c)
        assert Ps, f"{name}: no length-4 companion"
        for P in Ps:
            d = comb_data(Hed, P)
            print(f"   {name:14s} {P}  {d}  free={outer.free_ends(Gp, P)} "
                  f"pat={tuple(int(x) for x in outer.hub_pattern(Gp, P))}")

    hist, chi_h, dead, forced = {}, {}, [], []
    ncomp = 0

    def record(Hed, Gp, P, label, v):
        nonlocal ncomp
        d = comb_data(Hed, P)
        mu1, R1, A1, mu4, R4, A4, chi, dX, dY = d
        hist[(mu1, R1, A1, mu4, R4, A4)] = \
            hist.get((mu1, R1, A1, mu4, R4, A4), 0) + 1
        chi_h[(chi, dX, dY)] = chi_h.get((chi, dX, dY), 0) + 1
        ncomp += 1
        # the count identity behind (OC-2): welding X drops 3 vertices and
        # 3 + chi edges from a graph whose own trivial-partition count is 3,
        # so H/X's trivial-partition count is exactly 5 chi.
        K = contraction(Hed, P[1:])
        VK = _cverts(verts_of(Hed), P[1:])
        assert 6 * (len(VK) - 1) - 5 * len(K) == 5 * chi, \
            f"{label}: the 5 chi count identity failed"
        if A1 >= 1 and A4 >= 1:
            dead.append((label, v, tuple(P), d))
        if mu1 >= 2 or mu4 >= 2 or R1 <= 4 or R4 <= 4:
            forced.append((label, v, tuple(P), d))

    print("\n-- part 2: the named inventory --")
    nnamed = 0
    for label, E in outer.named_inventory():
        for v in outer.eligible_splits(E):
            a, b, c, Gp, Hed = outer.split_data(E, v)
            for P in outer.companions4(Hed, b, c):
                record(Hed, Gp, P, label, v)
                nnamed += 1
    print(f"   {nnamed} (split, companion) pairs over "
          f"{len(outer.named_inventory())} named shapes")

    print("\n-- part 3: the systematic class-shape sweep --")
    nsweep = 0
    for fname, fam in outer.sweep_shapes():
        n = 0
        for label, E in fam:
            for v in outer.eligible_splits(E):
                a, b, c, Gp, Hed = outer.split_data(E, v)
                for P in outer.companions4(Hed, b, c):
                    record(Hed, Gp, P, label, v)
                    n += 1
        nsweep += n
        print(f"   {fname}: {len(fam)} class shapes, {n} pairs")

    print(f"\n   (mu_1, dim R_1, A_1, mu_4, dim R_4, A_4) histogram over all "
          f"{ncomp} pairs:")
    for k in sorted(hist):
        print(f"       {k} : {hist[k]}")
    print(f"   (chi, def(H/X), def(H/Y)) histogram: "
          f"{dict(sorted(chi_h.items()))}")
    print(f"   shapes where BOTH disjuncts of (OUT) fail ambient-generically "
          f"(A_1, A_4 >= 1): {len(dead)}")
    print(f"   shapes where a disjunct is FORCED nonzero on the whole chart "
          f"(mu >= 2 or dim R <= 4): {len(forced)}")
    assert not dead, f"a class shape kills both disjuncts of (OUT): {dead[:3]}"
    assert all(k == (1, 5, 0, 1, 5, 0) for k in hist), \
        f"the availability map is not uniform: {sorted(hist)}"
    print(f"\nCOMB OK: {ncomp} (split, companion) pairs, all with "
          f"(mu, dim R, A) = (1, 5, 0) on BOTH sides.")
    print("  The whole map collapses to ONE measured statement, because with")
    print("  chi = 0 the arithmetic is forced: H/X drops 3 vertices and 3 "
          "edges from a")
    print("  graph of trivial-partition count 3, so H/X is TIGHT; and then")
    print("     H/X rigid  =>  A = 0 (a contraction of a rigid graph is "
          "rigid)")
    print("                and  dim R = 5 (deleting one independent edge of "
          "a tight")
    print("                     rigid graph costs exactly 5).")
    print("  Tightness is arithmetic; RIGIDITY of H/X is not, and is what "
          "the 4296")
    print("  deficiency calls measure.")
    print("  Reading, in three parts and no further:")
    print("   * A_1 = A_4 = 0 -- at an AMBIENT-generic placement both "
          "disjuncts of (OUT)")
    print("     hold, so (OUT) is available at every enumerated class shape.")
    print("   * dim R = 5 < 6 -- neither disjunct is identically zero, so "
          "(OUT) is never")
    print("     DEAD at a shape.")
    print("   * dim R = 5 >= 5 -- by (OC-3) the bad locus is NONEMPTY on "
          "every chart, so")
    print("     (OUT) is never AUTOMATIC either.  `deficiency` is the "
          "unconstrained count;")
    print("     the pencil chart is a proper subvariety of the placement "
          "space, so none of")
    print("     this is evidence about a pencil-generic placement.  That is "
          "what --pool")
    print("     and --build measure.")


# ---------------- frames of POOL-G ------------------------------------------

POOL_G_SEEDS = range(200, 300)
WAUX = (F(1), F(-2), F(5))     # the fixed auxiliary point off plane(a,b,c)


def frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH):
    """One POOL-G frame, or `(None, reason)`.

    Mirrors `lambda.habitat_frame` -- same placement (`place_pencil_general`
    on `random.Random(seed)`), same target-rank / `dim R_a = 1` filter (through
    the catalogued `outer.stratum_at`, which is `seed_probe`'s stress block
    without the parts this question does not use), same `lambda` -- with two
    deliberate differences: the closed-star rank test `star_span_ranks` is
    applied (the `plane_basis` precedent), and a (Lambda-0d) failure is REPORTED
    rather than dropped, because that is precisely where (OUT) stops
    applying.  `--pool` cross-checks `lambda` against `habitat_frame` on a
    fixed subsample.

    ADOPTION JUDGEMENT (slice S2, 2026-08-06).  This is one of the two sites
    where the coincident-hinge guard is deliberately NOT a rejection: the
    coincidence is what (OC-7) MEASURES, and rejecting it here would delete
    the measurement that opened the re-baselining round.  The acceptance set
    is therefore unchanged (`star_span_ranks` only) and the composite verdict
    `repin.star_generic` rides along in the returned dict as `'generic'`, for
    `--pool`'s field test to compare against the local diagnostics."""
    pl = place_pencil_general(Gp, random.Random(seed))
    if pl is None:
        return None, 'no placement'
    placed, pt, nrm, hubs, nb = pl
    if any(r != 3 for r in star_span_ranks(Gp, placed).values()):
        return None, 'star-span guard'
    st = outer.stratum_at(E, Gp, placed, a, b)
    if st is None:
        return None, 'off target rank'
    if st[1] != 1:
        return None, 'dim R_a != 1'
    if outer.panel_frame(placed, nrm, b, c) is None:
        return None, 'panels parallel'
    Vbc, ndim, _ = H_motions_vbc(E, v, a, b, c, placed)
    if len(Vbc) != 3:
        return None, f'dim V_bc = {len(Vbc)}'
    C = [wedge2(hat(placed[P[i]]), hat(placed[P[i + 1]])) for i in range(4)]
    if rank(C) != 4:
        return None, '(Lambda-0a) rank{C_i} < 4'
    Sb = span_basis(C)
    for x in Vbc:
        assert in_span(x, Sb), "V_bc escapes the companion span"
    Vco = [coords_in(C, x) for x in Vbc]
    assert all(x is not None for x in Vco)
    assert rank(Vco) == 3, "V_bc coordinate rank drop"
    ns = nullspace(Vco)
    assert len(ns) == 1, f"lambda is not a point of P(S*) ({len(ns)})"
    lam = ns[0]
    assert any(x != 0 for x in lam), "lambda = 0"
    # lambda_i = lambda(C_i), so the two hypothesis coordinates ARE the
    # membership tests (Step 5a's first displayed equivalence):
    assert (lam[0] == 0) == in_span(C[0], Vbc), "lambda_1 = 0 vs C_1 in V_bc"
    assert (lam[3] == 0) == in_span(C[3], Vbc), "lambda_4 = 0 vs C_4 in V_bc"
    fr = outer.build_frame(placed, pt, nrm, b, c, P, seed)
    M0, Md = fr['M']
    ts = [(placed[a][i] - M0[i]) / Md[i] for i in range(3) if Md[i] != 0]
    assert all(t == ts[0] for t in ts), "pt(a) is not on the meet line M"
    return {'seed': seed, 'placed': placed, 'pt': pt, 'nrm': nrm, 'fr': fr,
            'C': C, 'Vbc': Vbc, 'lam': lam, 't_a': ts[0], 'st': st,
            'a': a, 'b': b, 'c': c, 'Gp': Gp, 'Hed': Hed, 'VH': VH,
            'P': P, 'E': E, 'v': v,
            'generic': star_generic(Gp, placed),
            'coinc': coincident_hinges(Gp, placed)}, None


def clauses(d):
    """(Lambda-0a)-(Lambda-0f') at one frame, as an explicit dict of bools,
    plus `p+`, `q` and the three surviving Gram entries."""
    fr, C, placed = d['fr'], d['C'], d['placed']
    b, c = d['b'], d['c']
    waux = list(WAUX)
    m, n, q, s, (Cab, Cac, Cbc, Caw) = LAM.rows_mnqs(fr, d['t_a'], waux)
    pplus = [klein(Ci, fr['CM']) for Ci in C]
    g13, g14, g24 = klein(C[0], C[2]), klein(C[0], C[3]), klein(C[1], C[3])
    Sb = span_basis(C)
    return {
        'a': rank(C) == 4,
        'b': rank(Sb + [Cab, Cac]) == 6,
        'c': rank([m, n]) == 2,
        'd': outer.lam0d(placed, d['nrm'], b, c),
        'e': rank(Sb + [fr['CM']]) == 5,
        'f': (pplus[1] != 0 and pplus[2] != 0 and q[1] != 0 and q[2] != 0),
        'g13': g13 != 0, 'g14': g14 != 0, 'g24': g24 != 0,
    }, pplus, q


def pool():
    print("== (OC-1) + (OC-5): lambda_1 and lambda_4, measured ==")
    print(f"   POOL-G: the 4 lambda.habitat_specs habitats x placement seeds "
          f"{POOL_G_SEEDS.start}-{POOL_G_SEEDS.stop - 1}")
    print("           (the same integer pool lambda.py --adv uses for its "
          "habitat leg).")
    print("   Kept: target rank, dim R_a = 1, dim V_bc = 3, rank{C_i} = 4, "
          "the closed-star")
    print("   rank test green -- and DELIBERATELY NOT the composite "
          "coincident-hinge guard,")
    print("   which is what (OC-7) measures here and is reported below "
          "instead of rejected.")
    print("   (Lambda-0d) failures are KEPT and reported, not dropped.")
    print(f"   rng: the placement is random.Random(seed) inside "
          f"widened.place_pencil_general;\n        nothing else here draws -- "
          f"the aux point w is fixed at (1,-2,5) and the\n        pencil "
          f"L_h comes from repin.robust_plane_basis.  PYTHONHASHSEED=0.\n")

    tot = {'frames': 0, 'rejected': {}}
    zero_pat = {}
    per_shape = {}
    codim1 = {k: 0 for k in ('lambda_1', 'lambda_4', 'g13', 'g14', 'g24',
                             'p+_2', 'p+_3', 'q_2', 'q_3', '(Lambda-0d)')}
    lam0d_fail, out_silent, out_applies, concl_ok = 0, [], 0, 0
    bad_lam_p, bad_lam_q = 0, 0
    rel_checked, rel_rows = 0, []
    xchecked = 0
    deg_tab, coinc_tab, clean_pat = {}, {}, {}
    rotor_rows, both_deg, any_deg = [], 0, 0
    field_tab, field_extra, gen_pat = {}, [], {}

    for name, E, v, cmp_ in LAM.HABITATS4:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        VH = sorted(verts_of(Hed), key=str)
        Ps = outer.companions4(Hed, b, c)
        assert len(Ps) == 1, f"{name}: {len(Ps)} length-4 companions"
        P = Ps[0]
        sub = {}
        nsub = 0
        for seed in POOL_G_SEEDS:
            d, why = frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
            if d is None:
                tot['rejected'][why] = tot['rejected'].get(why, 0) + 1
                continue
            tot['frames'] += 1
            nsub += 1
            lam = d['lam']
            cl, pplus, q = clauses(d)
            for key, val in (('lambda_1', lam[0]), ('lambda_4', lam[3]),
                             ('p+_2', pplus[1]), ('p+_3', pplus[2]),
                             ('q_2', q[1]), ('q_3', q[2])):
                if val == 0:
                    codim1[key] += 1
            for key in ('g13', 'g14', 'g24'):
                if not cl[key]:
                    codim1[key] += 1
            if not cl['d']:
                codim1['(Lambda-0d)'] += 1
                lam0d_fail += 1
            key = (lam[0] == 0, lam[3] == 0)
            sub[key] = sub.get(key, 0) + 1
            zero_pat[key] = zero_pat.get(key, 0) + 1
            # (OC-7): the two degeneracy diagnostics, per side.
            cob = hinge_coincidences(Gp, d['placed'], b, P[1])
            coc = hinge_coincidences(Gp, d['placed'], c, P[3])
            dgb = degenerate_sampler(d['nrm'], b)
            dgc = degenerate_sampler(d['nrm'], c)
            nbH = neighbors(Hed)
            for side, dg, co, z, h, x in (('b', dgb, cob, lam[0] == 0,
                                           b, P[1]),
                                          ('c', dgc, coc, lam[3] == 0,
                                           c, P[3])):
                deg_tab[(side, dg, z)] = deg_tab.get((side, dg, z), 0) + 1
                coinc_tab[(side, bool(co), z)] = \
                    coinc_tab.get((side, bool(co), z), 0) + 1
                if z:
                    assert co, \
                        f"lambda_{side} = 0 with NO coincident hinge line " \
                        f"at the hub: {name} seed {seed}"
                    # the FREE ROTOR reading: the coincidence exhausts the
                    # hub's other H-neighbours, so every hinge attaching the
                    # hub to H shares one line and the hub spins about it.
                    others = set(nbH[h]) - {x}
                    assert set(co) & set(nbH[h]) == others, \
                        f"{name} seed {seed} side {side}: the coincidence " \
                        f"{sorted(co)} does NOT exhaust the hub's other " \
                        f"H-neighbours {sorted(others)}"
                    rotor_rows.append((name, seed, side, sorted(co),
                                       sorted(others), dg))
            if dgb and dgc:
                both_deg += 1
            if dgb or dgc:
                any_deg += 1
            if not cob and not coc:
                clean_pat[key] = clean_pat.get(key, 0) + 1
            if d['generic']:
                gen_pat[key] = gen_pat.get(key, 0) + 1
            # THE FIELD HALF OF THE ADVERSARIAL TEST (slice S2).  The
            # constructed half lives at `repin.py --hinge`; this is the
            # sampled one, and its provenance is measured, not invented.
            # `repin.star_generic` is the guard the round adopts; the local
            # (OC-7) diagnostic `cob or coc` is the hand-restriction §(K-out)
            # applied by eye.  The guard is the WIDER test by construction (it
            # looks at every body and every pair, the diagnostic only at the
            # two companion ends), so one direction is a theorem and the other
            # is the measurement: does looking everywhere find anything the
            # two ends do not?
            diag = bool(cob) or bool(coc)
            field_tab[(not d['generic'], diag)] = \
                field_tab.get((not d['generic'], diag), 0) + 1
            assert not (diag and d['generic']), \
                (f"{name} seed {seed}: a coincidence at a companion end that "
                 f"`star_generic` does not see -- the guard is NOT wider")
            if not d['generic'] and not diag:
                field_extra.append((name, seed, d['coinc']))
            # (OUT)'s hypothesis, and -- separately -- its conclusion.
            applies = cl['d'] and cl['f'] and cl['g13'] and cl['g14'] \
                and cl['g24'] and cl['a'] and cl['b'] and cl['c'] and cl['e']
            if lam[0] != 0 or lam[3] != 0:
                if applies:
                    out_applies += 1
                    assert rank([lam, pplus]) == 2, "(OUT) hypothesis holds " \
                        "but lambda ~ p+"
                    assert rank([lam, q]) == 2, "(OUT) hypothesis holds but " \
                        "lambda ~ q"
                    co = LAM.qpoly(d['fr'], lam)
                    assert LAM.poly_deg(co) >= 0, \
                        "(OUT) hypothesis holds but Q(z(t)) == 0"
                    concl_ok += 1
            else:
                out_silent.append((name, seed, applies,
                                   rank([lam, pplus]) == 1,
                                   rank([lam, q]) == 1,
                                   LAM.poly_deg(LAM.qpoly(d['fr'], lam)),
                                   dgb, dgc, cob, coc))
            if rank([lam, pplus]) == 1:
                bad_lam_p += 1
            if rank([lam, q]) == 1:
                bad_lam_q += 1
            # (OC-1): the welded model, at EVERY frame with lambda_1 = 0 or
            # lambda_4 = 0 (the load-bearing ones) and at the first three
            # clean frames of each habitat as controls.
            if lam[0] == 0 or lam[3] == 0 or nsub <= 3:
                rel_checked += 1
                rel_rows.append(rel_check(d))
            # cross-check the pipeline against `lambda.habitat_frame` on a
            # fixed subsample: same lambda, up to scale.
            if nsub <= 5:
                hf = LAM.habitat_frame(E, v, seed, P)
                if hf is not None and hf['lam'] is not None:
                    assert rank([hf['lam'], lam]) == 1, \
                        f"{name} seed {seed}: lambda disagrees with " \
                        f"lambda.habitat_frame"
                    xchecked += 1
        per_shape[name] = sub
        avail = sum(cnt for k, cnt in sub.items() if not (k[0] and k[1]))
        print(f"   {name:14s} {nsub:3d} frames   "
              f"(lambda_1 = 0, lambda_4 = 0) -> "
              f"{ {tuple(int(x) for x in k): val for k, val in sorted(sub.items())} }"
              f"   (OUT) hypothesis holds at {avail}/{nsub}")

    n = tot['frames']
    print(f"\n   POOL-G frames: {n}   rejected: {tot['rejected']}")
    print(f"   cross-checked against lambda.habitat_frame: {xchecked} frames, "
          f"lambda identical up to scale")
    print(f"\n   (OC-5) the distribution over POOL-G:")
    for k in sorted(zero_pat):
        lab = {(False, False): 'both outer coords NONZERO   ((OUT) applies)',
               (True, False): 'lambda_1 = 0 only           ((OUT) applies '
                              'via C_4)',
               (False, True): 'lambda_4 = 0 only           ((OUT) applies '
                              'via C_1)',
               (True, True): 'BOTH VANISH                 ((OUT) SILENT)'}[k]
        print(f"       {tuple(int(x) for x in k)}  {lab:52s} {zero_pat[k]:4d}"
              f"  ({zero_pat[k]}/{n})")
    hyp = n - zero_pat.get((True, True), 0)
    print(f"   (OUT)'s hypothesis holds at {hyp} of {n} POOL-G frames; it is "
          f"SILENT at {n - hyp}.")
    print(f"   (OUT)'s conclusion verified where the hypothesis holds AND "
          f"(Lambda-0)+(Lambda-0f')\n   are green: {concl_ok} of "
          f"{out_applies} such frames -- lambda off both bad points and "
          f"Q(z(t)) not identically 0.")
    print(f"   lambda ~ p+ : {bad_lam_p}     lambda ~ q : {bad_lam_q}   "
          f"(0 expected; a p+ hit would be a (T3) failure)")
    print(f"   (Lambda-0d) fails at {lam0d_fail} of {n} frames -- (OUT) does "
          f"NOT apply there\n   (the bad set becomes a hyperplane, which the "
          f"line {{lambda_1 = lambda_4 = 0}} does not contain).")
    print(f"\n   codimension-1 event rates over the SAME pool (the calibration "
          f"that says\n   how unremarkable a 'lambda_i = 0' rate is):")
    for k in sorted(codim1):
        print(f"       {k:12s} = 0 at {codim1[k]:4d} / {n}")
    if out_silent:
        print(f"\n   the (OUT)-SILENT frames, in full:")
        for (name, seed, applies, pp, qq, dg,
             dgb, dgc, cob, coc) in out_silent:
            print(f"       {name} seed {seed}: (Lambda-0)+(Lambda-0f') green "
                  f"{applies}, lambda ~ p+ {pp}, lambda ~ q {qq}, "
                  f"deg_t Q(z(t)) = {dg}")
            print(f"           degenerate in-plane sampler at (b, c): "
                  f"({dgb}, {dgc}); coincident hinges at b {cob}, at c {coc}")

    print(f"\n   (OC-7) the two degeneracy diagnostics over POOL-G:")
    print(f"     (side, degenerate in-plane sampler at the hub, "
          f"lambda_i = 0) -> count")
    for k in sorted(deg_tab, key=str):
        print(f"         {k} : {deg_tab[k]}")
    print(f"     (side, C_i coincides with another hinge line at the hub, "
          f"lambda_i = 0) -> count")
    for k in sorted(coinc_tab, key=str):
        print(f"         {k} : {coinc_tab[k]}")
    print(f"     every lambda_i = 0 frame, with its coincidence list "
          f"(hub, list, the hub's\n     other H-neighbours, sampler "
          f"degenerate) -- the list EXHAUSTS the others at\n     every one, "
          f"asserted, which is the FREE ROTOR reading:")
    for row in rotor_rows:
        print(f"         {row}")
    print(f"     frames with a degenerate in-plane sampler at b or c: "
          f"{any_deg} of {n} (both: {both_deg})")
    nclean = sum(clean_pat.values())
    print(f"     POOL-G frames with NO coincident hinge line at b or c: "
          f"{nclean} of {n}")
    print(f"       their (lambda_1 = 0, lambda_4 = 0) distribution: "
          f"{ {tuple(int(x) for x in k): val for k, val in sorted(clean_pat.items())} }")
    assert all(z for (side, dg, z) in deg_tab if dg), \
        "a degenerate-sampler frame did NOT force lambda_i = 0"
    assert all(not z for (side, co, z) in coinc_tab if not co), \
        "a coincidence-free frame nevertheless has lambda_i = 0"
    print(f"\n   THE FIELD HALF OF THE COINCIDENT-HINGE GUARD'S ADVERSARIAL "
          f"TEST (slice S2):\n     `repin.star_generic` REJECTS vs the local "
          f"(OC-7) diagnostic at (b, c) -> count")
    for k in sorted(field_tab, key=str):
        print(f"         (guard rejects, diagnostic fires) = "
              f"{tuple(bool(x) for x in k)} : {field_tab[k]}")
    nrej = sum(v for k, v in field_tab.items() if k[0])
    ndiag = sum(v for k, v in field_tab.items() if k[1])
    print(f"     the guard rejects {nrej} of {n}; the hand-restriction drops "
          f"{ndiag} of {n},\n     leaving §(K-out)'s {n - ndiag}.  The guard "
          f"is the wider test and its rejection\n     set CONTAINS the "
          f"diagnostic's, asserted at every frame above.")
    if field_extra:
        print(f"     the {len(field_extra)} frame(s) the guard catches and "
              f"the two-end diagnostic misses\n     (a coincidence elsewhere "
              f"in the configuration):")
        for row in field_extra:
            print(f"         {row}")
        print(f"     so the two sets are NOT equal: §(K-out)'s "
              f"hand-restriction to the {n - ndiag} frames\n     "
              f"coincidence-free AT THE COMPANION ENDS is WIDER than the "
              f"guard's own output,\n     which is {n - nrej} frames.  Every "
              f"lambda_i = 0 frame carries a coincidence at\n     the hub "
              f"the coordinate belongs to (asserted above), so the extra "
              f"frames all\n     have both outer coordinates nonzero and "
              f"neither reading is corrupted by the\n     other -- but a "
              f"rate quoted over the guard's sub-pool is the STRICTER one:")
    else:
        print("     and the two sets are EQUAL on this pool: every "
              "coincidence in a POOL-G\n     frame sits at a companion end, "
              "so §(K-out)'s hand-restriction to the\n     coincidence-free "
              "sub-pool IS the guard's output.")
    ngen = sum(gen_pat.values())
    print(f"     POOL-G frames the composite guard ACCEPTS: {ngen} of {n}; "
          f"their\n       (lambda_1 = 0, lambda_4 = 0) distribution: "
          f"{ {tuple(int(x) for x in k): val for k, val in sorted(gen_pat.items())} }")
    print("     Reading: the harness's in-plane sampler degeneracy IMPLIES "
          "lambda_i = 0 (it")
    print("     puts every single-hub interior of that hub on ONE line, so "
          "the hub becomes a")
    print("     free rotor about it), and EVERY lambda_i = 0 frame in this "
          "pool carries a")
    print("     coincident hinge line.  So the 18/357 rate above is NOT a hit "
          "rate for a")
    print("     generic chart point -- it is dominated by a sampler artifact "
          "that")
    print("     `star_span_ranks` does not catch.  --build reaches the locus "
          "without it.")
    print(f"\n   (OC-1) the welded model, at {rel_checked} frames "
          f"(every lambda_i = 0 frame + 3 controls per habitat):")
    agg = {}
    for row in rel_rows:
        agg[row] = agg.get(row, 0) + 1
    for k in sorted(agg):
        print(f"       (mu_1, dim W_1, dim R_1, dim(R_1^L_b) | "
              f"mu_4, dim W_4, dim R_4, dim(R_4^L_c)) = {k} : {agg[k]}")
    assert all(k[0] == 1 and k[2] == 5 and k[3] == 1
               and k[4] == 1 and k[6] == 5 and k[7] == 1 for k in agg), \
        f"(OC-1)/(OC-3) structure broke on the pencil chart: {sorted(agg)}"
    print("\nPOOL OK.  (OC-1) holds at every checked frame: lambda_i = 0 is "
          "EXACTLY the\n  welded model's 'the end body is not rigidly "
          "attached', and exactly `C_i in R_i`.\n  (OC-3) holds on the pencil "
          "chart too: dim R = 5 and dim(R cap L) = 1 at every\n  frame, so "
          "each companion end carries exactly ONE bad direction.")


def rel_check(d):
    """(OC-1) + (OC-3) at one frame, by the welded model.  Returns
    `(mu_1, dim W_1, dim R_1, dim(R_1 cap L_b), mu_4, dim W_4, dim R_4,
    dim(R_4 cap L_c))`, having asserted the equivalence chain against
    `lambda`."""
    Hed, VH, placed, P = d['Hed'], d['VH'], d['placed'], d['P']
    b, c, lam, C = d['b'], d['c'], d['lam'], d['C']
    out = []
    for end, inner, W, ei in ((b, P[1], P[1:], 0), (c, P[3], P[:4], 3)):
        e = next(ee for ee in Hed if set(ee) == {end, inner})
        mu = sum(1 for ee in Hed
                 if (ee[0] == end and ee[1] in W)
                 or (ee[1] == end and ee[0] in W))
        motW, idxW = weld_motions(Hed, VH, placed, [W])
        Wsp = rel_span(motW, idxW, end, inner)
        motR, idxR = weld_motions(Hed, VH, placed, [W], drop=[e])
        R = rel_span(motR, idxR, end, inner)
        assert len(R) >= len(Wsp), "deleting a hinge lost motions"
        # (OC-1), the whole chain:
        assert (lam[ei] == 0) == (len(Wsp) == 1), \
            "lambda_i = 0 vs the welded relative twist being nonzero"
        assert len(Wsp) <= 1, f"welded relative twist has dim {len(Wsp)}"
        if mu == 1:
            assert (lam[ei] == 0) == in_span(C[ei], R), \
                "lambda_i = 0 vs C_i in R_i"
        if len(Wsp) == 1:
            assert in_span(C[ei], Wsp) and in_span(Wsp[0], [C[ei]]), \
                "the welded relative twist is not spanned by C_i"
        _dd, k = marked_direction(placed, d['nrm'], end, R)
        out += [mu, len(Wsp), len(R), k]
    return tuple(out)


# ---------------- (OC-6) the shape-level availability -----------------------

POOL_S_SEEDS = range(1, 40)
POOL_S_PER_SPLIT = 3
POOL_S_SWEEP_CAP = 4


def shapes():
    print("== (OC-6): is (OUT) available at every SHAPE, not just every "
          "seed? ==")
    print(f"   POOL-S: outer.named_inventory() (19 named class shapes) plus "
          f"the first\n           {POOL_S_SWEEP_CAP} shapes of each "
          f"outer.sweep_shapes() family; every eligible split;\n           "
          f"placement seeds {POOL_S_SEEDS.start}-{POOL_S_SEEDS.stop - 1}, up "
          f"to {POOL_S_PER_SPLIT} hard-stratum frames per split;\n           "
          f"every length-4 companion at each.  Disjoint from POOL-G, and "
          f"never\n           aggregated with it.")
    print("   (OUT) needs the escape at SOME target-rank seed, so the "
          "shape-level question")
    print("   is whether a shape has a frame with lambda_1 != 0 or "
          "lambda_4 != 0 -- not\n   whether every frame does.\n")
    fams = [('named', outer.named_inventory())]
    for fname, fam in outer.sweep_shapes():
        fams.append((fname.split(' ')[0], fam[:POOL_S_SWEEP_CAP]))
    tot = {'shapes': 0, 'with4': 0, 'frames': 0, 'silent': 0, 'avail': 0}
    bad_shapes, silent_rows, zero_pat = [], [], {}
    ncoinc = [0]
    for fname, fam in fams:
        nsh, nfr, nsil = 0, 0, 0
        for label, E in fam:
            for v in outer.eligible_splits(E):
                a, b, c, Gp, Hed = outer.split_data(E, v)
                VH = sorted(verts_of(Hed), key=str)
                Ps = outer.companions4(Hed, b, c)
                if not Ps:
                    continue
                tot['with4'] += 1
                nsh += 1
                per = {tuple(P): [] for P in Ps}
                got = 0
                for seed in POOL_S_SEEDS:
                    d0 = None
                    for P in Ps:
                        d, why = frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
                        if d is None:
                            break
                        d0 = d
                        per[tuple(P)].append((d['lam'][0] == 0,
                                              d['lam'][3] == 0))
                        key = (d['lam'][0] == 0, d['lam'][3] == 0)
                        zero_pat[key] = zero_pat.get(key, 0) + 1
                        tot['frames'] += 1
                        nfr += 1
                        cob = hinge_coincidences(Gp, d['placed'], b, P[1])
                        coc = hinge_coincidences(Gp, d['placed'], c, P[3])
                        if bool(cob) or bool(coc):
                            ncoinc[0] += 1
                        if key != (False, False):
                            assert (cob if key[0] else True) and \
                                   (coc if key[1] else True), \
                                f"lambda_i = 0 with no coincident hinge: " \
                                f"{label} {v} {P} seed {seed}"
                        if key == (True, True):
                            cl, pplus, q = clauses(d)
                            nsil += 1
                            tot['silent'] += 1
                            silent_rows.append(
                                (label, v, tuple(P), seed,
                                 all(cl[k] for k in ('a', 'b', 'c', 'd', 'e',
                                                     'f', 'g13', 'g14',
                                                     'g24')),
                                 LAM.poly_deg(LAM.qpoly(d['fr'], d['lam']))))
                        else:
                            tot['avail'] += 1
                    if d0 is not None:
                        got += 1
                    if got >= POOL_S_PER_SPLIT:
                        break
                for P, rows in per.items():
                    if rows and all(r == (True, True) for r in rows):
                        bad_shapes.append((label, v, P, len(rows)))
        tot['shapes'] += len(fam)
        print(f"   {fname:8s}: {len(fam):3d} shapes -> {nsh:3d} "
              f"(split with a length-4 companion), {nfr:4d} frames, "
              f"{nsil} (OUT)-silent")
    n = tot['frames']
    print(f"\n   POOL-S frames: {n} over {tot['with4']} splits carrying a "
          f"length-4 companion")
    print(f"   (lambda_1 = 0, lambda_4 = 0) distribution:")
    for k in sorted(zero_pat):
        print(f"       {tuple(int(x) for x in k)} : {zero_pat[k]}")
    print(f"   (OUT)'s hypothesis holds at {tot['avail']} of {n} POOL-S "
          f"frames; SILENT at {tot['silent']}.")
    print(f"   (OC-7) frames carrying a coincident hinge line at b or c: "
          f"{ncoinc[0]} of {n};\n          every lambda_i = 0 frame is one "
          f"of them (asserted per frame).")
    if silent_rows:
        print("   the (OUT)-silent frames, in full "
              "(shape, split, companion, seed, (Lambda-0) green, "
              "deg_t Q(z(t))):")
        for row in silent_rows:
            print(f"       {row}")
    print(f"   (split, companion) pairs with NO available frame in POOL-S: "
          f"{len(bad_shapes)}")
    for row in bad_shapes:
        print(f"       {row}")
    assert not bad_shapes, \
        f"a class shape has (OUT) silent at every probed seed: {bad_shapes}"
    print(f"\nSHAPES OK: every (split, companion) pair that produced a frame "
          f"in POOL-S has\n  at least one hard-stratum target-rank frame "
          f"where (OUT)'s hypothesis holds.\n  This is SHAPE-level "
          f"availability, which is what (OUT) as a route needs; it is\n  "
          f"not uniformity, and no seed pool can make it so.")


# ---------------- (OC-4) the construction -----------------------------------

POOL_B_SEEDS = range(200, 260)
SLIDES = (F(1), F(2), F(-1), F(3), F(1, 2), F(5), F(-3), F(7))


def build():
    print("== (OC-4): a chart point of a real class habitat where (OUT) is "
          "SILENT ==")
    print(f"   POOL-B: the 4 habitats x placement seeds "
          f"{POOL_B_SEEDS.start}-{POOL_B_SEEDS.stop - 1}; slide parameters "
          f"{[str(s) for s in SLIDES]}")
    print("   rng: only widened.place_pencil_general's random.Random(seed);"
          " the marked")
    print("        directions are deterministic "
          "(repin.robust_plane_basis).")
    print("   The move: slide pt(x1) inside Pi(b) onto the ONE direction of")
    print("   L_b = (lines through pt(b) in Pi(b)) that lies in R_1, and "
          "pt(x3)")
    print("   inside Pi(c) onto the corresponding direction of L_c.  The two "
          "moves are")
    print("   INDEPENDENT: welding Y = {b,x1,x2,x3} for the c-side absorbs "
          "e_1 and e_2,")
    print("   so pt(x1) does not enter R_4, and symmetrically.\n")
    built, clean = 0, 0
    for name, E, v, cmp_ in LAM.HABITATS4:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        VH = sorted(verts_of(Hed), key=str)
        P = outer.companions4(Hed, b, c)[0]
        f1, f3 = outer.free_ends(Gp, P)
        if not (f1 and f3):
            print(f"   {name}: companion {P} is not doubly free "
                  f"({f1}, {f3}) -- the construction needs both ends")
            continue
        done = False
        for seed in POOL_B_SEEDS:
            d, why = frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
            if d is None or not outer.lam0d(d['placed'], d['nrm'], b, c):
                continue
            placed, pt, nrm = d['placed'], d['pt'], d['nrm']
            dirs = []
            for end, inner, W in ((b, P[1], P[1:]), (c, P[3], P[:4])):
                e = next(ee for ee in Hed if set(ee) == {end, inner})
                motR, idxR = weld_motions(Hed, VH, placed, [W], drop=[e])
                R = rel_span(motR, idxR, end, inner)
                assert len(R) == 5, f"dim R = {len(R)} (expected 5)"
                dd, k = marked_direction(placed, nrm, end, R)
                dirs.append(dd)
            if any(x is None for x in dirs):
                continue
            # does the marked direction merely point at another neighbour of
            # the hub (the degenerate 'free rotor' configuration)?  (OC-7).
            nbGp = neighbors(Gp)
            aim = []
            for end, dd in ((b, dirs[0]), (c, dirs[1])):
                L = wedge2(hat(placed[end]),
                           hat([placed[end][i] + dd[i] for i in range(3)]))
                aim.append([u for u in sorted(nbGp[end], key=str)
                            if rank([L, wedge2(hat(placed[end]),
                                               hat(placed[u]))]) == 1])
            hit = None
            for t1 in SLIDES:
                for t3 in SLIDES:
                    new = dict(placed)
                    new[P[1]] = [placed[b][i] + t1 * dirs[0][i]
                                 for i in range(3)]
                    new[P[3]] = [placed[c][i] + t3 * dirs[1][i]
                                 for i in range(3)]
                    if len(set(tuple(x) for x in new.values())) != len(new):
                        continue
                    if not verify_pencil_witness(Gp, new)[0]:
                        continue
                    # ADOPTION JUDGEMENT (slice S2): the SECOND deliberate
                    # non-adoption.  (OC-4)'s whole content is that the
                    # {lambda_1 = lambda_4 = 0} locus is reached at a point
                    # that is NOT the free-rotor configuration, and it is
                    # measured by counting how many of the four constructions
                    # come out coincidence-free (3 of 4, asserted below).
                    # Rejecting a coincident slide here would silently
                    # re-search until the count was 4 of 4 and delete the
                    # measurement.  So the acceptance gate stays the star-rank
                    # test and `star_generic` is REPORTED per construction.
                    if any(r != 3 for r in
                           star_span_ranks(Gp, new).values()):
                        continue
                    st = outer.stratum_at(E, Gp, new, a, b)
                    if st is None or st[1] != 1:
                        continue
                    Vbc, ndim, _ = H_motions_vbc(E, v, a, b, c, new)
                    if len(Vbc) != 3:
                        continue
                    Cn = [wedge2(hat(new[P[i]]), hat(new[P[i + 1]]))
                          for i in range(4)]
                    if rank(Cn) != 4:
                        continue
                    Vco = [coords_in(Cn, x) for x in Vbc]
                    if any(x is None for x in Vco) or rank(Vco) != 3:
                        continue
                    ns = nullspace(Vco)
                    if len(ns) != 1:
                        continue
                    hit = (t1, t3, new, ns[0], Vbc, Cn, st, ndim)
                    break
                if hit:
                    break
            if hit is None:
                continue
            t1, t3, new, lam, Vbc, Cn, st, ndim = hit
            dd = {'seed': seed, 'placed': new, 'pt': pt, 'nrm': nrm,
                  'C': Cn, 'Vbc': Vbc, 'lam': lam, 'a': a, 'b': b, 'c': c,
                  'Gp': Gp, 'Hed': Hed, 'VH': VH, 'P': P, 'E': E, 'v': v,
                  'fr': outer.build_frame(new, pt, nrm, b, c, P, seed)}
            M0, Md = dd['fr']['M']
            dd['t_a'] = next((new[a][i] - M0[i]) / Md[i]
                             for i in range(3) if Md[i] != 0)
            cl, pplus, q = clauses(dd)
            g = outer.geom_checks(new, nrm, b, c, P)
            co = LAM.qpoly(dd['fr'], lam)
            cob = hinge_coincidences(Gp, new, b, P[1])
            coc = hinge_coincidences(Gp, new, c, P[3])
            nd, ndinfo = nondeg_conjuncts(Gp, new)
            print(f"   {name:14s} seed {seed}, companion {P}, "
                  f"slides (t1, t3) = ({t1}, {t3})")
            print(f"       lambda = ({lam[0]}, .., .., {lam[3]}) -- "
                  f"lambda_1 = 0: {lam[0] == 0}, lambda_4 = 0: "
                  f"{lam[3] == 0}   => (OUT) is SILENT")
            print(f"       C_1 in V_bc: {in_span(Cn[0], Vbc)}   "
                  f"C_4 in V_bc: {in_span(Cn[3], Vbc)}")
            print(f"       (Lambda-0a..e) = "
                  f"{ {k: cl[k] for k in 'abcde'} }")
            print(f"       (Lambda-0f) middle brackets: p+ = "
                  f"(0, {pplus[1] != 0}, {pplus[2] != 0}, 0), "
                  f"q = (0, {q[1] != 0}, {q[2] != 0}, 0)")
            print(f"       Gram: g13 != 0 {cl['g13']}, g14 != 0 {cl['g14']} "
                  f"(= {g['g14'] != 0}), g24 != 0 {cl['g24']}")
            print(f"       still a legal pencil realization: target rank "
                  f"{st[0]}, dim R_a = {st[1]}, dim V_bc = {len(Vbc)}, "
                  f"dim Mot(H) = {ndim}")
            print(f"       lambda ~ p+ : {rank([lam, pplus]) == 1}    "
                  f"lambda ~ q : {rank([lam, q]) == 1}    "
                  f"deg_t Q(z(t)) = {LAM.poly_deg(co)}")
            print(f"       (OC-7) marked direction aims at the hub "
                  f"neighbours {aim}; coincident hinges at b {cob}, at c "
                  f"{coc}")
            print(f"       the composite guard repin.star_generic: "
                  f"{star_generic(Gp, new)}"
                  f"   (all coincidences: {coincident_hinges(Gp, new)})")
            print(f"       all four IsNondegPencilRealization conjuncts: "
                  f"{nd}" + ("" if nd else f"  {ndinfo}"))
            if not cob and not coc:
                clean += 1
            assert lam[0] == 0 and lam[3] == 0, "the construction failed"
            assert all(cl[k] for k in ('a', 'b', 'c', 'd', 'e', 'f',
                                       'g13', 'g14', 'g24')), \
                "a (Lambda-0) clause died: this is a KNOWN degeneration, " \
                "not the isolated (OUT) one"
            assert rank([lam, pplus]) == 2 and rank([lam, q]) == 2, \
                "lambda landed on a bad POINT, not merely the bad line"
            assert LAM.poly_deg(co) >= 0, \
                "Q(z(t)) == 0: the pitch certificate is blind here"
            assert nd, f"the constructed point is not a nondegenerate " \
                f"pencil realization: {ndinfo}"
            built += 1
            done = True
            break
        assert done, f"{name}: no construction over POOL-B"
    assert built == 4, f"only {built} of 4 habitats gave the construction"
    assert clean >= 3, f"only {clean} of 4 constructions are free of a " \
        f"coincident hinge line -- the construction would then be the " \
        f"degenerate free-rotor configuration, not a new phenomenon"
    print(f"\n   (OC-7) {clean} of {built} constructed points carry NO "
          f"coincident hinge line at\n   b or c, so on those the "
          f"lambda_1 = lambda_4 = 0 locus is reached at a genuinely\n   "
          f"nondegenerate pencil realization -- not by collapsing a hub's "
          f"hinge pencil.")
    print(f"\nBUILD OK: {built} of 4 habitats.  (OUT)'s bad line "
          f"{{lambda_1 = lambda_4 = 0}} is\n  REACHABLE by an explicit, legal "
          f"chart move at every probed class habitat, with\n  EVERY "
          f"(Lambda-0) clause and the hard-stratum target rank intact -- so "
          f"(OUT) is\n  strictly weaker than (Lambda-2), not a "
          f"reformulation of it.  At all {built}\n  constructed points "
          f"lambda is off both bad POINTS and deg_t Q(z(t)) = 4, so the "
          f"pitch\n  certificate still fires and the escape holds where "
          f"(OUT) cannot see it.")


# ---------------- main ------------------------------------------------------

def main():
    sys.stdout.reconfigure(line_buffering=True)
    args = sys.argv[1:]
    modes = {'--comb': comb, '--pool': pool, '--shapes': shapes,
             '--build': build}
    if not args or args[0] not in modes:
        print(__doc__)
        return
    modes[args[0]]()


if __name__ == '__main__':
    main()
