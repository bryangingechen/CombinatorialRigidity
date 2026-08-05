"""
Phase 39, section (K-Lambda) follow-up -- THE OUTER COMPANION BRACKET
`g14 = [b, x1, x3, c]`.

WHY THIS DRIVER EXISTS.  `m2/lambda0.m2` proved the exact span criterion
(Lambda-0f') at the generic point of the local frame,

    span_t w+(t) = 3  <=>  p+_2 p+_3 g13 g14 g24 != 0,
    span_t w-(t) = 3  <=>  q_2  q_3  g13 g14 g24 != 0,

and found the RECORDED criterion (Lambda-0f) incomplete: it carries the two
middle brackets but not the three Gram factors.  Two of the three are
`rank Q|_S = 4` in new clothing; the third,

    g14 = B(C1, C4) = [b, x1, x3, c],

is asserted NOWHERE in the harness.  Its failure is not vacuous: the M2
driver's block (P5) degenerates `C4`'s direction onto `C1`'s and drops both
spans while (Lambda-0a,b,c,e) and all four middle brackets survive.
`notes/Pencil-informal.md` section (K-Lambda) *What would change this* item
(vi) therefore asks the one question the 164 sampled frames could not answer,
BECAUSE the clause is generically satisfied:

    does any CLASS habitat, at a length-4-companion split, force `g14 = 0`
    on its WHOLE pencil chart -- i.e. are the two outer companion lines
    `C1 = C(b x1)` and `C4 = C(x3 c)` necessarily meeting there?

A hit would put a THIRD branch into (Lambda-2)'s two-point dichotomy and
force the Lambda-completeness theorem to be restated.  Sampling cannot
confirm a generically-true clause -- but it settles this question exactly,
because the question is whether `g14` VANISHES IDENTICALLY: one exact chart
point with `g14 != 0` refutes forcing at that habitat outright.

WHAT IS NEW HERE, BEYOND THE SWEEP.  Two structural facts, both elementary
and both driver-checked, that turn item (vi) from an open risk into a
located one:

  (Lambda-0g) THE GEOMETRIC FORM.  `x1` is a `G'`-neighbour of the hub `b`,
    so `C1 = C(b x1)` lies in the panel `Pi(b)`; likewise `C4 = C(x3 c)`
    lies in `Pi(c)`.  Both panels contain the meet line `M`, and two lines
    of a projective plane always meet, so EACH OUTER LINE ALWAYS MEETS `M`
    (this is the structural vanishing `p+_1 = p+_4 = 0` that (Lambda-0f)
    already records, read backwards).  Hence, whenever `Pi(b) != Pi(c)`,

        g14 = 0   <=>   C1 cap M  =  C4 cap M                as points of M.

    So the clause is not "two lines in space happen to meet" (codimension 1
    in a 4-parameter family) but "two marked points of the LINE `M`
    coincide" -- one equation on the chart, and the same `M` on which
    `pt(a)` slides.

  (Lambda-0i) THE MOBILITY CRITERION.  If `x1`'s only hub `G'`-neighbour is
    `b` and `x1` is not itself a hub -- equivalently, `x1` has degree 2 and
    `x2` is not a hub -- then `pt(x1)` is constrained by NOTHING but
    `pt(x1) in Pi(b)`, so it ranges over a dense subset of that plane with
    the whole rest of the placement held fixed.  `g14` is affine in
    `pt(x1)`, so `g14 == 0` on the chart would force
    `Pi(b) = plane(b, x3, c)`, hence `pt(c) in Pi(b)` -- a failure of
    (Lambda-0d), which the arc already names.  SO: IN THAT PATTERN THE
    `g14` CLAUSE IS IMPLIED BY (Lambda-0d) AND IS NOT A NEW HYPOTHESIS.
    Symmetrically with `x3` free in `Pi(c)` and the other half of
    (Lambda-0d).  The criterion is combinatorial, so `--sweep` can report
    exactly which class shapes it covers and which it does not.

WHAT THE DRIVER DOES.

  --geom      (Lambda-0g) at real class-habitat seeds, then the DECISIVE
              construction: at theta(3,4,5)/NT21/NT24/NT30, slide `pt(x1)`
              inside `Pi(b)` onto the line `b -- (C4 cap M)`, which forces
              `g14 = 0` while keeping every other (Lambda-0) clause.  The
              result is an exact pencil chart point OF A REAL CLASS HABITAT
              with `g14 = 0`; both `a`-line spans are then measured.  This
              reproduces `m2/lambda0.m2` block (P5) on a real habitat rather
              than on the abstract slice, and it makes `lambda.omega_curves`'
              own coded (Lambda-0f) equivalence FIRE -- caught and reported,
              never repaired (`notes/scripts/README.md` section 4
              convention 5 forbids touching `lambda.py`).
  --habitat   the named-inventory sweep: every class habitat of the arc's
              inventory that carries a length-4 `b`-`c` companion, at every
              eligible split and several target-rank hard-stratum seeds,
              with `g14` evaluated on every such companion.
  --sweep     the systematic class-shape sweep: exhaustive over the theta
              family, over `G* = K4` (the 877-shape stratum), and over
              `K4` + a parallel `bc` edge (the NT21/NT24/NT30 hub
              multigraph); plus a capped pass over the `|V*| = 5` hub
              graphs.  Per shape: the hub pattern of the companion, the
              (Lambda-0i) coverage verdict, and `g14` at a sampled pencil
              placement.
  --tangent   the chart-level certificate: at each sampled point the
              differential of `g14` along `dominance.build_chart`'s pencil
              tangent space is nonzero, so `{g14 = 0}` is a proper
              hypersurface of the chart -- the pattern-free form of
              (Lambda-0i).  Part 2 runs it on every companion the
              (Lambda-0i) free-end criterion does NOT reach.
  --patterns  the coverage boundary itself: which of the 8 hub patterns
              `(x1, x2, x3)` a class companion can even have, over the same
              families at a WIDENED length bound.  An unrealized pattern is
              a boundary, not a theorem, and is printed as such.

Exact rational arithmetic throughout; no floating point.  Every sampled
placement carries the `star_span_ranks` genericity guard (the `plane_basis`
precedent) and a rank assert; every rng is seeded and its seed printed.

    python3 notes/scripts/w4/outer.py --geom
    python3 notes/scripts/w4/outer.py --habitat
    python3 notes/scripts/w4/outer.py --sweep
    python3 notes/scripts/w4/outer.py --tangent
    python3 notes/scripts/w4/outer.py --patterns
"""
import importlib
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (cross3, dot, hat, left_nullspace, neighbors,  # noqa: E402
                       nullspace, rank, wedge2)
from kbare_common import verify_pencil_witness, verts_of            # noqa: E402
from localtest import meet_line                                     # noqa: E402
from nogood_subdiv import deficiency, hcard_ok, triangles           # noqa: E402
from widened import orient, place_pencil_general, removeV           # noqa: E402
from repin import rank_at_V, seed_probe, span_basis                 # noqa: E402
from pitch import (bracket, coords_in, det4, H_motions_vbc,        # noqa: E402
                   klein, paths_graph)
from kslidecomb import relabel, shape_ok                            # noqa: E402
from flanks import named_shapes, star_span_ranks                    # noqa: E402
from dominance import (build_chart, h_edges, simple_paths,         # noqa: E402
                       FIXED, HABITATS)

# `lambda` is a Python keyword, so `w4/lambda.py`'s primitives are reachable
# only through `importlib` (`notes/scripts/README.md` section 1, the caveat on
# the `lambda` rows).  What is needed here is SHAPE and FRAME data --
# `habitat_specs` (the four certified length-4-companion habitats) and
# `omega_curves` (the (Lambda-0f) span measurement whose criterion this
# driver is testing) -- not a linear-algebra primitive, so the README's
# "move it one layer down" remedy does not apply: moving `omega_curves` would
# edit `lambda.py` and trip the full figure gate on `--adv` (536 s) for no
# gain.  `lambda.py` is READ, never modified.
LAM = importlib.import_module('lambda')


# ---------------- the outer bracket, and its two marked points --------------

def companions4(Hed, b, c):
    """Every length-4 `b`-`c` path of `H`, as a vertex list `[b,x1,x2,x3,c]`.
    `dominance.simple_paths` is the canonical enumerator."""
    return [P for P in simple_paths(Hed, b, c, maxlen=4) if len(P) - 1 == 4]


def outer_bracket(placed, P):
    """`g14 = [b, x1, x3, c]` = `B(C(b x1), C(x3 c))` on a length-4 companion
    `P = [b, x1, x2, x3, c]`.  Zero iff the two outer companion lines meet."""
    assert len(P) == 5, "not a length-4 companion"
    return bracket(placed, P[0], P[1], P[3], P[4])


def meet_param(p, q, M0, Md):
    """The parameter `t` with `M0 + t*Md` on the line through the two affine
    `Q^3` points `p != q`, or `None` when that line is parallel to `M` (the
    meet is at infinity).  Coplanarity of the two lines is a PRECONDITION --
    asserted by the consistency check across the three components.

    NOT `lambda.span_meet`: that primitive meets two subspaces of `Q^6` and
    is hard-coded to that ambient (see the *Divergences* row).  This is the
    one-parameter solve of two COPLANAR lines in `Q^3`."""
    w = [q[i] - p[i] for i in range(3)]
    assert any(x != 0 for x in w), "degenerate line (coincident points)"
    num = cross3([M0[i] - p[i] for i in range(3)], w)
    den = cross3(Md, w)
    if all(x == 0 for x in den):
        # the line is affinely PARALLEL to `M`: coplanar with it (the caller
        # asserts that projectively, as `B(C, C(M)) = 0`), so in `P^3` the two
        # meet at `M`'s point at infinity.  `None` is that marked point.
        return None
    t = None
    for i in range(3):
        if den[i] != 0:
            ti = -num[i] / den[i]
            if t is None:
                t = ti
            else:
                assert ti == t, "inconsistent meet parameter (not coplanar)"
        else:
            assert num[i] == 0, "inconsistent meet parameter (not coplanar)"
    return t


def hub_pattern(Gp, P):
    """`(x1 hub, x2 hub, x3 hub)` in `G'` for a length-4 companion."""
    nb = neighbors(Gp)
    return tuple(len(nb[P[i]]) >= 3 for i in (1, 2, 3))


def free_ends(Gp, P):
    """(Lambda-0i)'s combinatorial criterion, both ends.

    `x1` is FREE when its only chart constraint is `pt(x1) in Pi(b)`: it is
    not a hub (so it carries no panel of its own) and `b` is its only hub
    `G'`-neighbour.  Then `pt(x1)` sweeps a dense subset of `Pi(b)` with the
    rest of the placement fixed, and `g14 == 0` on the chart would force
    `pt(c) in Pi(b)`, i.e. a failure of (Lambda-0d).  Symmetrically for
    `x3` in `Pi(c)`."""
    nb = neighbors(Gp)
    b, x1, _x2, x3, c = P

    def free(x, h):
        if len(nb[x]) >= 3:
            return False
        return all(len(nb[u]) < 3 for u in nb[x] if u != h)

    return free(x1, b), free(x3, c)


# ---------------- placements ------------------------------------------------

def split_data(edges, v):
    """`(a, b, c, G', H)` at the split `v`, or None when `v` is not usable /
    the two chain ends are not both hubs (the (K-Lambda) standing frame)."""
    o = orient(edges, v)
    if o is None:
        return None
    a, b, c = o
    nb = neighbors(edges)
    if len(nb[b]) < 3 or len(nb[c]) < 3:
        return None
    Gp = removeV(edges, v) + [(a, b)]
    return a, b, c, Gp, h_edges(edges, v, a)


def chart_point(Gp, rng):
    """A pencil-chart placement of `G'`, with the mandatory guards: every
    hub's closed star spans exactly its panel (`star_span_ranks`, the
    `plane_basis` genericity guard) and `verify_pencil_witness` green."""
    try:
        pl = place_pencil_general(Gp, rng)
    except UnboundLocalError:
        # LATENT DEFECT IN A FROZEN MODULE, guarded here rather than fixed.
        # `localtest.meet_line` is documented to signal "no meet line" by
        # returning a zero direction -- and `place_pencil_general` tests for
        # exactly that -- but when the two panel normals are PARALLEL its
        # every 2x2 minor vanishes, the base-point loop never binds `p0`, and
        # it raises `UnboundLocalError` instead of returning.  So the caller's
        # guard is unreachable in the one case it was written for.  Fixing it
        # means editing an `escape/`-layer module that the entire `w4/` stack
        # imports, i.e. re-baselining every recorded figure in the harness
        # (`notes/scripts/README.md` *figures do not move*, second bullet);
        # that is not this commit's business.  A parallel-normal draw is a
        # degenerate sample, so the correct local handling is to reject it.
        return None
    if pl is None:
        return None
    placed, pt, nrm, hubs, nb = pl
    if any(r != 3 for r in star_span_ranks(Gp, placed).values()):
        return None
    ok, _info = verify_pencil_witness(Gp, placed)
    if not ok:
        return None
    return placed, pt, nrm


def panel_frame(placed, nrm, b, c):
    """`(M0, Md, CM)` for the meet line `M = Pi(b) cap Pi(c)`, or None when
    the two panels are parallel/equal.  Asserts `M` is a genuine line."""
    M0, Md = meet_line(placed[b], nrm[b], placed[c], nrm[c])
    if all(x == 0 for x in Md):
        return None
    CM = wedge2(hat(M0), hat([M0[i] + Md[i] for i in range(3)]))
    assert any(x != 0 for x in CM), "degenerate C(M)"
    return M0, Md, CM


def lam0d(placed, nrm, b, c):
    """(Lambda-0d): `pt(c) not in Pi(b)` AND `pt(b) not in Pi(c)`."""
    return (dot(nrm[b], [placed[c][i] - placed[b][i] for i in range(3)]) != 0
            and dot(nrm[c], [placed[b][i] - placed[c][i]
                             for i in range(3)]) != 0)


def geom_checks(placed, nrm, b, c, P):
    """(Lambda-0g) at one chart point and one length-4 companion.  Returns a
    dict; every claim is asserted, not reported."""
    fr = panel_frame(placed, nrm, b, c)
    assert fr is not None, "panels parallel"
    M0, Md, CM = fr
    C1 = wedge2(hat(placed[P[0]]), hat(placed[P[1]]))
    C4 = wedge2(hat(placed[P[3]]), hat(placed[P[4]]))
    assert rank([C1, C4]) == 2, "outer companion lines dependent"
    g14 = outer_bracket(placed, P)
    assert klein(C1, C4) == g14, "g14 != B(C1, C4)"
    # both outer lines lie in their panel, hence meet M: the structural
    # zeros p+_1 = p+_4 = 0 of (Lambda-0f), read as geometry.
    for (x, h) in ((P[1], b), (P[3], c)):
        assert dot(nrm[h], [placed[x][i] - placed[h][i]
                            for i in range(3)]) == 0, "outer point off panel"
    assert klein(C1, CM) == 0 and klein(C4, CM) == 0, "outer line misses M"
    t1 = meet_param(placed[P[0]], placed[P[1]], M0, Md)
    t4 = meet_param(placed[P[3]], placed[P[4]], M0, Md)
    same = (t1 == t4)
    assert (g14 == 0) == same, \
        f"(Lambda-0g) FAILED: g14 == 0 is {g14 == 0}, meets coincide {same}"
    return {'g14': g14, 't1': t1, 't4': t4, 'C1': C1, 'C4': C4,
            'M': (M0, Md), 'CM': CM}


# ---------------- mode: the geometry, and the constructed g14 = 0 point -----

def build_frame(placed, pt, nrm, b, c, P, seed):
    """A `lambda.omega_curves`-shaped frame dict at an arbitrary chart point
    (`lambda.habitat_frame` re-samples internally, so it cannot be handed a
    MODIFIED placement -- which is exactly what the construction needs)."""
    fr = panel_frame(placed, nrm, b, c)
    assert fr is not None
    M0, Md, CM = fr
    C = [wedge2(hat(placed[P[i]]), hat(placed[P[i + 1]])) for i in range(4)]
    assert rank(C) == 4, "companion span not 4-dimensional"
    return {'seed': seed, 'complen': 4, 'hubpat': None, 'farhub': None,
            'bl': b, 'cl': c, 'path': list(P), 'placed': placed, 'pt': pt,
            'nrm': nrm, 'C': C, 'M': (M0, Md), 'CM': CM,
            'rng': random.Random(90210 + seed)}


def spans_at(fr, waux, strict=False):
    """`lambda.omega_curves` at a frame, catching the coded (Lambda-0f)
    equivalence when it fires.  Returns `(dict | None, message)`."""
    try:
        return LAM.omega_curves(fr, waux, strict=strict), None
    except AssertionError as e:
        return None, str(e)


def slide_x1_onto(placed, nrm, b, c, P, lamb):
    """Move `pt(x1)` inside `Pi(b)` onto the line joining `pt(b)` to
    `D = C4 cap M`, at parameter `lamb`.  Legal because `pt(b)` and `D` both
    lie in `Pi(b)` (`D in M = Pi(b) cap Pi(c)`), so the whole line does; and
    -- in the (Lambda-0i) free pattern -- `pt(x1) in Pi(b)` is `x1`'s only
    chart constraint.  Forces `C1 cap M = D = C4 cap M`, hence `g14 = 0`."""
    M0, Md, _CM = panel_frame(placed, nrm, b, c)
    t4 = meet_param(placed[P[3]], placed[P[4]], M0, Md)
    assert t4 is not None, "C4 meets M at infinity; construction needs t4"
    D = [M0[i] + t4 * Md[i] for i in range(3)]
    assert dot(nrm[b], [D[i] - placed[b][i] for i in range(3)]) == 0, \
        "D off Pi(b)"
    new = dict(placed)
    new[P[1]] = [placed[b][i] + lamb * (D[i] - placed[b][i]) for i in range(3)]
    return new, D


def stratum_at(edges, Gp, placed, a, b):
    """`(rank, dim R_a)` at an ARBITRARY placement of `G'`, or None when the
    placement is off target rank.

    Mirrors `repin.seed_probe`'s stress block for the same reason
    `build_frame` mirrors `lambda.habitat_frame`: `seed_probe` samples its own
    placement from an integer seed and so cannot be handed the MODIFIED one
    the construction produces.  The primitives are the catalogued ones
    (`repin.rank_at_V`, `exactcore.left_nullspace`, `repin.span_basis`)."""
    nG = len(verts_of(edges))
    tgtGp = 6 * (nG - 2) - deficiency(Gp)
    Vp = sorted(verts_of(Gp), key=str)
    rkp, rows, er, idx = rank_at_V(Gp, placed, Vp)
    if rkp != tgtGp:
        return None
    e_ab = next(e for e in er if set(e) == {a, b})
    base_a = 6 * idx[a]
    Ra = []
    for lam in left_nullspace(rows):
        r = [F(0)] * 6
        for ri in er[e_ab]:
            for k in range(6):
                r[k] += lam[ri] * rows[ri][base_a + k]
        Ra.append(r)
    return rkp, len(span_basis(Ra))


def geom():
    print("== (Lambda-0g): the outer bracket as a coincidence on M ==")
    print("   claim: C1 and C4 ALWAYS meet M (they lie in Pi(b), Pi(c), both")
    print("          of which contain M); so g14 = 0 <=> C1 cap M = C4 cap M.")
    waux = [F(1), F(-2), F(5)]
    nfr = 0
    for name, E, v, comp in LAM.HABITATS4:
        sd = split_data(E, v)
        assert sd is not None, f"{name}: split unusable"
        a, b, c, Gp, Hed = sd
        seen = 0
        for s in range(1, 60):
            p = seed_probe(E, v, s, nplace=0)
            if p is None or p['dim R_a'] != 1:
                continue
            placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
            if any(r != 3 for r in star_span_ranks(Gp, placed).values()):
                continue
            if not lam0d(placed, nrm, b, c):
                continue
            Ps = companions4(Hed, b, c)
            assert Ps, f"{name}: no length-4 companion"
            for P in Ps:
                g = geom_checks(placed, nrm, b, c, P)
                assert g['g14'] != 0, f"{name} seed {s}: g14 = 0 at a seed!"
                nfr += 1
            seen += 1
            if seen >= 3:
                break
        assert seen >= 3, f"{name}: too few hard-stratum seeds"
        print(f"   {name:14s} 3 seeds x {len(Ps)} companion(s): "
              f"g14 != 0, and t1 != t4 at every one")
    print(f"   (Lambda-0g) asserted at {nfr} (seed, companion) pairs\n")

    print("== the constructed g14 = 0 chart point (block (P5) on a REAL "
          "class habitat) ==")
    print("   move pt(x1) inside Pi(b) onto the line b--(C4 cap M).  Every")
    print("   other (Lambda-0) clause is kept; only g14 dies.")
    built, nblind = 0, [0]
    for name, E, v, comp in LAM.HABITATS4:
        a, b, c, Gp, Hed = split_data(E, v)
        for s in range(1, 60):
            p = seed_probe(E, v, s, nplace=0)
            if p is None or p['dim R_a'] != 1:
                continue
            placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
            if not lam0d(placed, nrm, b, c):
                continue
            Ps = companions4(Hed, b, c)
            P = Ps[0]
            fr1, fr3 = free_ends(Gp, P)
            if not fr1:
                continue
            base = build_frame(placed, pt, nrm, b, c, P, s)
            b0 = spans_at(base, waux)[0]
            if b0 is None or b0.get('off-pattern'):
                continue
            hit = None
            for lamb in (F(2), F(3), F(-1), F(5), F(1, 2), F(7), F(-3)):
                new, D = slide_x1_onto(placed, nrm, b, c, P, lamb)
                if not verify_pencil_witness(Gp, new)[0]:
                    continue
                if any(r != 3 for r in star_span_ranks(Gp, new).values()):
                    continue
                g = geom_checks(new, nrm, b, c, P)
                if g['g14'] != 0:
                    raise AssertionError("construction did not kill g14")
                nf = build_frame(new, pt, nrm, b, c, P, s)
                sp, msg = spans_at(nf, waux)
                pplus = [klein(Ci, nf['CM']) for Ci in nf['C']]
                qrow = [bracket(new, P[i], P[i + 1], b, c) for i in range(4)]
                if not (pplus[1] and pplus[2] and qrow[1] and qrow[2]):
                    # a middle bracket died too: that is the ALREADY-KNOWN
                    # (Lambda-0f) failure, not the isolated g14 degeneration
                    continue
                hit = (lamb, g, sp, msg, pplus, qrow, nf, new)
                break
            if hit is None:
                continue
            lamb, g, sp, msg, pplus, qrow, nf, new = hit
            # every other (Lambda-0) clause survives, explicitly:
            assert rank(nf['C']) == 4, "(Lambda-0a) died"
            Cab = wedge2(hat(new[a]), hat(new[b]))
            Cac = wedge2(hat(new[a]), hat(new[c]))
            Sb = span_basis(nf['C'])
            assert rank(Sb + [Cab, Cac]) == 6, "(Lambda-0b) S cap T != 0"
            mrow = [bracket(new, P[i], P[i + 1], a, b) for i in range(4)]
            nrow = [bracket(new, P[i], P[i + 1], a, c) for i in range(4)]
            assert rank([mrow, nrow]) == 2, "(Lambda-0c) died"
            assert lam0d(new, nrm, b, c), "(Lambda-0d) died"
            assert rank(Sb + [nf['CM']]) == 5, "(Lambda-0e) C(M) in S"
            assert pplus[1] != 0 and pplus[2] != 0, "(Lambda-0f) p+ middle"
            assert qrow[1] != 0 and qrow[2] != 0, "(Lambda-0f) q middle"
            g13 = klein(nf['C'][0], nf['C'][2])
            g24 = klein(nf['C'][1], nf['C'][3])
            assert g13 != 0 and g24 != 0, "rank Q|_S dropped too"
            print(f"   {name:14s} seed {s}, companion {P}, lambda = {lamb}")
            print(f"       g14 = 0; g13 = {g13}, g24 = {g24} (rank Q|_S = 4 "
                  f"survives)")
            print(f"       p+ = ({', '.join(str(x) for x in pplus)})")
            print(f"       q  = ({', '.join(str(x) for x in qrow)})")
            print(f"       (Lambda-0a,b,c,d,e) and all four middle brackets "
                  f"SURVIVE")
            if sp is None:
                print(f"       lambda.omega_curves' coded (Lambda-0f) "
                      f"equivalence FIRES: {msg}")
            else:
                print(f"       spans (w+, w-) = ({sp['span w+']}, "
                      f"{sp['span w-']})")
            # the spans, measured directly (omega_curves asserts (Lambda-0f)
            # before returning them, so recompute the two ranks here).
            rp, rm = raw_spans(nf, waux)
            print(f"       measured spans: span w+ = {rp}, span w- = {rm} "
                  f"(both drop from 3 -- (Lambda-0f') predicts exactly this)")
            assert rp < 3 and rm < 3, \
                "g14 = 0 did NOT drop the spans -- (Lambda-0f') is wrong"
            # ... and the placement really is a chart point of the habitat:
            ok, _ = verify_pencil_witness(Gp, new)
            assert ok and all(r == 3 for r in
                              star_span_ranks(Gp, new).values())
            Vbc, ndim, _ = H_motions_vbc(E, v, a, b, c, new)
            st = stratum_at(E, Gp, new, a, b)
            print(f"       still a legal pencil realization of {name}: "
                  f"dim V_bc = {len(Vbc)}, dim Mot(H) = {ndim}, "
                  f"{'TARGET-RANK' if st else 'off target rank'}"
                  + (f", dim R_a = {st[1]}" if st else ""))
            # ... so the third (Lambda-2) branch is LIVE at a good seed there.
            # Does it BITE?  The habitat's own far covector `lambda` is the
            # annihilator of `V_bc` in the `C`-basis; the pitch certificate is
            # blind along the whole `a`-line exactly when `lambda` annihilates
            # one of the two (now 2-dimensional) span containers.
            if len(Vbc) == 3:
                Vco = [coords_in(nf['C'], x) for x in Vbc]
                assert all(x is not None for x in Vco), "V_bc escapes S"
                ann = nullspace(Vco)
                assert len(ann) == 1, f"lambda not a point ({len(ann)})"
                lam_far = ann[0]
                WP, WM = raw_span_bases(nf, waux)
                blindP = all(dot(lam_far, w) == 0 for w in WP)
                blindM = all(dot(lam_far, w) == 0 for w in WM)
                qc = LAM.qpoly(nf, lam_far)
                print(f"       the habitat's own lambda: blind on span w+ "
                      f"{blindP}, on span w- {blindM}; "
                      f"Q(z(t)) {'== 0' if all(x == 0 for x in qc) else '!= 0'}"
                      f" (deg {LAM.poly_deg(qc)})")
                nblind[0] += int(blindP or blindM)
            built += 1
            break
    assert built == 4, f"only {built} of 4 habitats gave the construction"
    print(f"\n   the third (Lambda-2) branch BITES (the habitat's own lambda "
          f"annihilates a\n   collapsed span, so the pitch certificate goes "
          f"blind along the whole a-line)\n   at {nblind[0]} of {built} "
          f"constructed points.")
    print("\nGEOM OK: (Lambda-0g) holds at every probed (seed, companion); "
          "the g14 = 0\n  degeneration is REACHABLE on the pencil chart of "
          "all four class habitats\n  by an explicit chart move, and it drops "
          "both a-line spans -- so (Lambda-0f')\n  is confirmed on real "
          "habitats, and the recorded (Lambda-0f) is refuted there.")


def raw_span_bases(fr, waux):
    """The two sampled curve families `{w+(t)}`, `{w-(t)}` with NO
    (Lambda-0f) assertion -- the measurement `lambda.omega_curves` makes but
    guards behind the coded (and, since `m2/lambda0.m2`, incomplete) bracket
    equivalence, which is exactly what fires at a `g14 = 0` frame."""
    WP, WM = [], []
    for t in LAM.TS:
        m, n, q, s, _ = LAM.rows_mnqs(fr, t, waux)
        if rank([m, n]) != 2:
            continue
        wp, wm = LAM.cross4(m, n, s), LAM.cross4(m, n, q)
        if all(x == 0 for x in wp) or all(x == 0 for x in wm):
            continue
        WP.append(wp)
        WM.append(wm)
    assert len(WP) >= 6, "too few valid t"
    return WP, WM


def raw_spans(fr, waux):
    """`(rank span w+, rank span w-)`, un-guarded."""
    WP, WM = raw_span_bases(fr, waux)
    return rank(WP), rank(WM)


# ---------------- the shape inventory ---------------------------------------

def bounded_comps(m, total, lo, hi, fix):
    """Every length-`m` tuple of integers in `[lo, hi]` summing to `total`,
    with `fix` = {index: value} pinned.  Lexicographic, hence deterministic
    and reproducible without an rng."""
    cur = [0] * m

    def rec(i, rem):
        if i == m:
            if rem == 0:
                yield tuple(cur)
            return
        if rem < (m - i) * lo or rem > (m - i) * hi:
            return
        if i in fix:
            cur[i] = fix[i]
            if lo <= fix[i] <= hi:
                yield from rec(i + 1, rem - fix[i])
            return
        for x in range(lo, hi + 1):
            cur[i] = x
            yield from rec(i + 1, rem - x)

    return rec(0, total)


def has_l4(E0, lens, k):
    """Does the hub multigraph `E0` with branch lengths `lens`, split at
    branch `k` = (b, c), carry a length-4 `b`-`c` companion?  A companion is
    a simple `b`-`c` path of `H`, i.e. a simple hub path avoiding branch `k`
    whose branch lengths sum to 4.  Purely arithmetic, so it pre-filters the
    length enumeration before the (expensive) class certification."""
    b, c = E0[k]
    inc = {}
    for i, (u, w) in enumerate(E0):
        if i == k:
            continue
        inc.setdefault(u, []).append((i, w))
        inc.setdefault(w, []).append((i, u))

    def walk(cur, tot, seen):
        if tot > 4:
            return False
        if cur == c:
            return tot == 4
        for i, nxt in inc.get(cur, ()):
            if nxt in seen:
                continue
            if walk(nxt, tot + lens[i], seen | {nxt}):
                return True
        return False

    return walk(b, 0, {b})


K4E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
K4PARE = K4E + [(0, 1)]
THETA3 = [(0, 1), (0, 1), (0, 1)]
THETA4 = [(0, 1), (0, 1), (0, 1), (0, 1)]


def shapes_from(tag, n, E0, lmax, cap=None):
    """Every class shape over the hub multigraph `E0` (on `n` hubs) with a
    length-3 split branch and a length-4 `b`-`c` companion.

    Tightness pins `Sum l = 6(|E0| - n + 1)`; lengths run over `[1, lmax]`;
    the split branch runs over every branch index.  `shape_ok` is the
    established class predicate (tight + `def = 0` + `hnoRigid` at branch
    granularity).  Returns `(shapes, #tuples tried, capped?)`."""
    m = len(E0)
    tot = 6 * (m - n + 1)
    out, tried, seen = [], 0, set()
    for k in range(m):
        for lens in bounded_comps(m, tot, 1, lmax, {k: 3}):
            tried += 1
            if not has_l4(E0, lens, k):
                continue
            specs = tuple(relabel(n, E0, lens, k))
            if specs in seen:
                continue
            seen.add(specs)
            if shape_ok(list(specs)) is None:
                continue
            E = paths_graph([3], list(specs)[1:])[0]
            # `shape_ok` is tight + `def = 0` + `hnoRigid`; the class also
            # needs `hcard` and triangle-freeness (`lambda.habitat_specs`'
            # load-time predicate), which short branch lengths can break.
            if triangles(E) or not hcard_ok(E):
                continue
            out.append((f'{tag} {lens} split {k}', E))
            if cap is not None and len(out) >= cap:
                return out, tried, True
    return out, tried, False


def named_inventory():
    """The arc's named class habitats, from their canonical homes:
    `lambda.habitat_specs` (4), `dominance.habitats` (7) and
    `flanks.named_shapes` (the 8 uncovered-flank shapes)."""
    out = []
    for name, E, v, comp in LAM.HABITATS4:
        out.append((f'lambda:{name}', E))
    for name, E, v, pm, note in HABITATS:
        out.append((f'dom:{name}', E))
    for name, specs, note in named_shapes():
        out.append((f'flank:{name}', paths_graph([3], specs[1:])[0]))
    return out


def eligible_splits(E):
    """Every degree-2 vertex `v` whose split has both chain ends hubs."""
    return [v for v in sorted(verts_of(E), key=str)
            if split_data(E, v) is not None]


# ---------------- mode: the named-inventory sweep ---------------------------

def habitat():
    print("== every named class habitat with a length-4 companion, at every "
          "eligible split ==")
    print("   at target-rank hard-stratum seeds (dim R_a = 1): g14 != 0 on "
          "every companion.")
    tot_pairs, tot_shapes, patcount = 0, 0, {}
    for label, E in named_inventory():
        splits = eligible_splits(E)
        rows = []
        for v in splits:
            a, b, c, Gp, Hed = split_data(E, v)
            Ps = companions4(Hed, b, c)
            if not Ps:
                continue
            seen, vals = 0, []
            for s in range(1, 90):
                p = seed_probe(E, v, s, nplace=0)
                if p is None or p['dim R_a'] != 1:
                    continue
                placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
                if any(r != 3 for r in star_span_ranks(Gp, placed).values()):
                    continue
                if not lam0d(placed, nrm, b, c):
                    continue
                for P in Ps:
                    g = geom_checks(placed, nrm, b, c, P)
                    vals.append(g['g14'])
                    pat = hub_pattern(Gp, P)
                    patcount[pat] = patcount.get(pat, 0) + 1
                    assert g['g14'] != 0, \
                        f"{label} split {v} seed {s}: g14 = 0 -- A HIT"
                seen += 1
                if seen >= 3:
                    break
            if seen:
                rows.append((v, len(Ps), seen, len(vals)))
                tot_pairs += len(vals)
        if rows:
            tot_shapes += 1
            print(f"   {label}")
            for v, npath, seen, nval in rows:
                print(f"       split {v}: {npath} companion(s) x {seen} "
                      f"hard-stratum seeds -> {nval} nonzero g14")
    print(f"\n   hub patterns (x1,x2,x3) seen: "
          f"{sorted((k, v) for k, v in patcount.items())}")
    print(f"HABITAT OK: {tot_shapes} named shapes carry a length-4 companion; "
          f"{tot_pairs}\n  (split, seed, companion) triples, every one with "
          f"g14 != 0 and (Lambda-0g) asserted.")


# ---------------- mode: the systematic class-shape sweep --------------------

def sweep_shapes(cap5=25):
    """The families swept, deepest coverage first.  Each row is
    `(description, shapes)`; the description states the coverage boundary."""
    from kslidecomb import candidate_graphs
    out = []
    for tag, n, E0, lmax in (('theta3', 2, THETA3, 9),
                             ('theta4', 2, THETA4, 9),
                             ('K4', 4, K4E, 5),
                             ('K4+par', 4, K4PARE, 6)):
        sh, tried, capped = shapes_from(tag, n, E0, lmax)
        out.append((f'{tag} (EXHAUSTIVE over lengths 1..{lmax}; '
                    f'{tried} tuples)', sh))
    g5 = [(n, E) for (n, E) in candidate_graphs(5) if n == 5]
    for n, E0 in g5:
        sh, tried, capped = shapes_from(f'V5e{len(E0)}', n, E0, 5, cap=cap5)
        out.append((f'|V*| = 5, |E*| = {len(E0)} '
                    f'({"CAPPED at " + str(cap5) if capped else "EXHAUSTIVE"}'
                    f"; {tried} tuples)", sh))
    return out


SWEEP_SEED = 20260805


def sweep():
    print("== the systematic class-shape sweep ==")
    print("   per shape: every eligible split, every length-4 companion, the")
    print("   companion's hub pattern, the (Lambda-0i) coverage verdict, and")
    print("   g14 at a seeded pencil-chart placement.")
    print(f"   rng: random.Random({SWEEP_SEED} + shape index), one per "
          f"(shape, split)")
    grand = {'shapes': 0, 'with4': 0, 'comps': 0, 'zero': 0, 'placed': 0}
    patcount, covered, uncovered, nshape = {}, 0, [], 0
    for fname, fam in sweep_shapes():
        n4, ncomp, nz, npl = 0, 0, 0, 0
        for label, E in fam:
            grand['shapes'] += 1
            hit = False
            for v in eligible_splits(E):
                sd = split_data(E, v)
                a, b, c, Gp, Hed = sd
                Ps = companions4(Hed, b, c)
                if not Ps:
                    continue
                hit = True
                nshape += 1
                rng = random.Random(SWEEP_SEED + nshape)
                cp = None
                for _ in range(12):
                    cp = chart_point(Gp, rng)
                    if cp is None:
                        continue
                    placed, pt, nrm = cp
                    if panel_frame(placed, nrm, b, c) is None:
                        cp = None
                        continue
                    if not lam0d(placed, nrm, b, c):
                        cp = None
                        continue
                    break
                for P in Ps:
                    ncomp += 1
                    pat = hub_pattern(Gp, P)
                    patcount[pat] = patcount.get(pat, 0) + 1
                    f1, f3 = free_ends(Gp, P)
                    if f1 or f3:
                        covered += 1
                    else:
                        uncovered.append((label, v, tuple(P), pat))
                    if cp is None:
                        continue
                    placed, pt, nrm = cp
                    npl += 1
                    g = geom_checks(placed, nrm, b, c, P)
                    if g['g14'] == 0:
                        nz += 1
                        print(f"   !! {label} split {v} companion {P}: "
                              f"g14 = 0 AT THE SAMPLE")
            if hit:
                n4 += 1
        grand['with4'] += n4
        grand['comps'] += ncomp
        grand['zero'] += nz
        grand['placed'] += npl
        print(f"   {fname}: {len(fam)} class shapes, {n4} with a length-4 "
              f"companion,\n       {ncomp} (split, companion) pairs, "
              f"{npl} placed, {nz} with g14 = 0")
    print(f"\n   hub patterns (x1,x2,x3) over all families: "
          f"{sorted((k, v) for k, v in patcount.items())}")
    print(f"   (Lambda-0i) covers {covered} of {grand['comps']} companions "
          f"by the free-end criterion alone")
    if uncovered:
        print(f"   NOT covered by (Lambda-0i) ({len(uncovered)}); first few:")
        for row in uncovered[:8]:
            print(f"       {row}")
    else:
        print("   every companion in the sweep is (Lambda-0i)-covered")
    assert grand['zero'] == 0, "a sampled class chart point has g14 = 0"
    print(f"\nSWEEP OK: {grand['shapes']} class shapes examined, "
          f"{grand['with4']} carrying a\n  length-4 companion, "
          f"{grand['comps']} (split, companion) pairs, "
          f"{grand['placed']} placed exactly --\n  g14 != 0 at every one.")


# ---------------- mode: the chart-tangent certificate -----------------------

def dg14(placed, P, d):
    """The directional derivative of `g14 = [b,x1,x3,c]` along a point-velocity
    dict `d` (the multilinear expansion of the 4x4 bracket)."""
    keys = [P[0], P[1], P[3], P[4]]
    tot = F(0)
    for j, kj in enumerate(keys):
        if kj not in d:
            continue
        rows = [hat(placed[k]) for k in keys]
        rows[j] = list(d[kj]) + [F(0)]
        tot += det4(rows)
    return tot


def chart_dirs(Gp, placed, nrm, a, b, c):
    """`dominance.build_chart` in the FIXED scoping at a chart point."""
    VHa = sorted(verts_of(Gp), key=str)
    hubsGp = [u for u in sorted(neighbors(Gp), key=str)
              if len(neighbors(Gp)[u]) >= 3]
    dirs, nvar, ncons = build_chart(Gp, VHa, hubsGp, placed, nrm,
                                    FIXED, b, c, a)
    assert dirs, "empty chart tangent space"
    return dirs


def tangent():
    print("== the chart-tangent certificate: d g14 != 0 on the pencil chart ==")
    print("   scoping FIXED (dominance.build_chart): pt(a), pt(b), pt(c) and")
    print("   the two panels frozen, so the (Lambda-0) frame stands still and")
    print("   only the companion's own freedom is measured.  A nonzero")
    print("   differential makes {g14 = 0} a proper hypersurface of the chart.")
    tot, bad = 0, []
    print("\n-- part 1: the named inventory, at hard-stratum target-rank "
          "seeds --")
    for label, E in named_inventory():
        for v in eligible_splits(E):
            a, b, c, Gp, Hed = split_data(E, v)
            Ps = companions4(Hed, b, c)
            if not Ps:
                continue
            done = 0
            for s in range(1, 60):
                p = seed_probe(E, v, s, nplace=0)
                if p is None or p['dim R_a'] != 1:
                    continue
                placed, pt, nrm = p['_ctx'][0], p['_ctx'][1], p['_ctx'][2]
                if any(r != 3 for r in star_span_ranks(Gp, placed).values()):
                    continue
                if not lam0d(placed, nrm, b, c):
                    continue
                dirs = chart_dirs(Gp, placed, nrm, a, b, c)
                for P in Ps:
                    vals = [dg14(placed, P, d) for d in dirs]
                    tot += 1
                    if all(x == 0 for x in vals):
                        bad.append((label, v, tuple(P)))
                done += 1
                if done >= 2:
                    break
            if done:
                print(f"   {label:46s} split {v}: {len(Ps)} companion(s), "
                      f"d g14 != 0")

    print("\n-- part 2: every (Lambda-0i)-UNCOVERED companion of the "
          "--sweep families --")
    print("   (the pattern where BOTH ends are pinned: x2 is a hub, so "
          "pt(x1) and\n    pt(x3) each lie on a panel-meet LINE rather than "
          "sweeping a plane)")
    nunc, seenpat = 0, {}
    for fname, fam in sweep_shapes():
        for i, (label, E) in enumerate(fam):
            for v in eligible_splits(E):
                a, b, c, Gp, Hed = split_data(E, v)
                Ps = [P for P in companions4(Hed, b, c)
                      if not any(free_ends(Gp, P))]
                if not Ps:
                    continue
                rng = random.Random(TANGENT_SEED + nunc)
                cp = None
                for _ in range(12):
                    cp = chart_point(Gp, rng)
                    if cp is None:
                        continue
                    placed, pt, nrm = cp
                    if (panel_frame(placed, nrm, b, c) is None
                            or not lam0d(placed, nrm, b, c)):
                        cp = None
                        continue
                    break
                if cp is None:
                    continue
                placed, pt, nrm = cp
                dirs = chart_dirs(Gp, placed, nrm, a, b, c)
                for P in Ps:
                    pat = hub_pattern(Gp, P)
                    seenpat[pat] = seenpat.get(pat, 0) + 1
                    vals = [dg14(placed, P, d) for d in dirs]
                    tot += 1
                    nunc += 1
                    if all(x == 0 for x in vals):
                        bad.append((label, v, tuple(P)))
    print(f"   {nunc} uncovered companions certified; patterns "
          f"{sorted((k, v) for k, v in seenpat.items())}")
    print(f"\n   {tot} (chart point, companion) pairs; d g14 = 0 on the whole "
          f"tangent space at {len(bad)}")
    assert not bad, f"d g14 vanishes on the chart tangent space at {bad[:4]}"
    print("TANGENT OK: at every probed class chart point the differential of "
          "g14 along\n  the pencil chart is nonzero, so {g14 = 0} is a proper "
          "hypersurface of the\n  chart -- no class habitat in scope can force "
          "g14 = 0 identically, INCLUDING\n  the companions the (Lambda-0i) "
          "free-end criterion does not reach.")


TANGENT_SEED = 771100


# ---------------- mode: which companion hub patterns are reachable ----------

def patterns(lmax=8, cap=400):
    print("== which hub patterns (x1, x2, x3) can a class companion have? ==")
    print("   The (Lambda-0i) free-end criterion fails only when BOTH ends are")
    print("   pinned, i.e. only for patterns with x2 a hub, or with x1 and x3")
    print("   both hubs.  This mode asks whether such shapes exist at all.")
    print(f"   Widened length bound: lengths run to {lmax} (the --sweep "
          f"families stop\n   at 5/6), cap {cap} shapes per hub multigraph.")
    from kslidecomb import candidate_graphs
    fams = [('theta3', 2, THETA3), ('theta4', 2, THETA4),
            ('K4', 4, K4E), ('K4+par', 4, K4PARE)]
    fams += [(f'V5e{len(E0)}', n, E0)
             for (n, E0) in candidate_graphs(5) if n == 5]
    census, examples = {}, {}
    for tag, n, E0 in fams:
        sh, tried, capped = shapes_from(tag, n, E0, lmax, cap=cap)
        for label, E in sh:
            for v in eligible_splits(E):
                a, b, c, Gp, Hed = split_data(E, v)
                for P in companions4(Hed, b, c):
                    pat = hub_pattern(Gp, P)
                    census[pat] = census.get(pat, 0) + 1
                    examples.setdefault(pat, (label, v, tuple(P)))
        print(f"   {tag:8s}: {len(sh)} class shapes "
              f"({'CAPPED' if capped else 'exhaustive'}; {tried} tuples)")
    print("\n   pattern      count   free-end covered?   first example")
    allpat = [(x1, x2, x3) for x1 in (False, True) for x2 in (False, True)
              for x3 in (False, True)]
    for pat in allpat:
        cnt = census.get(pat, 0)
        cov = 'yes' if (not pat[0] and not pat[1]) or \
                       (not pat[2] and not pat[1]) else 'NO'
        ex = examples.get(pat, '--')
        print(f"   {str(tuple(int(x) for x in pat)):12s} {cnt:6d}   "
              f"{cov:16s}  {ex}")
    missing = [p for p in allpat if p not in census]
    print(f"\nPATTERNS OK: {sum(census.values())} companions; "
          f"{len(census)} of 8 patterns realized.")
    print(f"  unrealized in scope: {[tuple(int(x) for x in p) for p in missing]}"
          f"\n  (an unrealized pattern is a COVERAGE BOUNDARY, not a theorem: "
          f"it says the\n   swept families and length bound produce none, "
          f"not that none exists.)")


# ---------------- main ------------------------------------------------------

def main():
    args = sys.argv[1:]
    modes = {'--geom': geom, '--habitat': habitat, '--sweep': sweep,
             '--tangent': tangent, '--patterns': patterns}
    if not args or args[0] not in modes:
        print(__doc__)
        return
    modes[args[0]]()


if __name__ == '__main__':
    main()
