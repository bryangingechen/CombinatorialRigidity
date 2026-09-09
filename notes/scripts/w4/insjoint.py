#!/usr/bin/env python3
"""INSJOINT (arc ordinal 90) -- (INS-7)'s OWN KILL CONDITION: the last
option-B stone.

THE QUESTION, quoted from the gap map's `§(K-ins)` close-it cell (the
condition direction BINSERT left as option B's one unpriced endpoint):

  *"Shape 4's own kill condition ((INS-7)): derive `U'` for the
  TWO-vertex-deleted shared framework and measure `rank<U', Lambda^2 Pihat>`
  at these 8 seeds -- one direction, a NECESSARY condition rather than the
  full joint-sweep criterion, and the whole remaining option-B spend.
  `>= 2` there would give option B an endpoint of its own; `<= 1` closes the
  route outright."*

WHY `U'` IS A NEW OBJECT AND THIS IS NOT A RE-RUN OF `binsert.py combined`.
`combined` measures `rank<U, Lambda^2 Pihat(b) + Lambda^2 Pihat(c)>` -- the
pairing of the ONE-vertex-deleted `U` against KT's carrier-surviving escape
span (`binsert.py:355`, and it is what returned rank 1 at 8/8 hits, (INS-4)).
Route A moves `pt(v)` only, so its shared framework is `G - v` and its `U` is
built from the motions of `G - v` -- a framework that still CONTAINS `a` and
the edge `ac`, so `U` depends on the seed's own `pt(a)`.  The joint sweep
moves `pt(v)` AND `pt(a)`, so its shared framework is `G - v - a` and its
`U'` must be independent of `pt(a)`.  Different framework, different space,
new derivation.

THE DERIVATION (Step INS8, (INS-9)), off the row structure of
`kbare_common.build_rigidity` -- not off prose, and not off `seed_calculus`'s
docstring.  Chain `b -- v -- a -- c` with `deg v = deg a = 2`,
`E(G) = E(G - v - a) + {vb, va, ac}`.  A left-nullvector (self-stress) `omega`
of `R(G)` carries a coefficient block `nu_e in K^5` on each hinge; write
`U_e := sum_j nu_e[j] w_j(C_e) in perp(C_e)`, `w_j = perp_basis(C_e)`.  The
column blocks of the two DELETED bodies are touched only by those hinges:

    block v (edges vb, va) :  U_vb = U_va =: u
    block a (edges va, ac) :  U_va = U_ac =: u

so a single `u in perp(C(vb)) n perp(C(va)) n perp(C(ac))` carries all three,
and the blocks of the two chain ENDS `b`, `c` leave the shared framework
loaded by the functional `(-u at b, +u at c)`.  Hence

    U' = {u in K^6 : <u, m(c) - m(b)> = 0 for every motion m of G - v - a}
       = {u : (-u at b, +u at c) in rowspan R(G - v - a)},

    corank R(G) at (pt v, pt a) = (x_v, x_a)
        = s0' + dim(U' n C(vb)^perp n C(va)^perp n C(ac)^perp)
        = s0' + dim U' - rank M'(x_v, x_a),
    M' = [[<u_i, C(vb)>], [<u_i, C(va)>], [<u_i, C(ac)>]]   (3 x dim U'),

with `s0'` the row corank of `R(G - v - a)`.  So `U'` is the SAME construction
as `U` with the deleted vertex's two NEIGHBOURS `(a, b)` replaced by the
deleted PATH's two ENDS `(b, c)`; `M'` gains a third row and its middle entry
`C(va) = hat(x_v) ^ hat(x_a)` is BILINEAR -- which is exactly the shape
(INS-7)(iii) priced as needing a two-parameter extension of (BE-2).

THREE STRUCTURE FACTS that link the two calculi (Step INS9, (INS-10)) --
proved here, asserted per seed:
  * `s0' = s0`.  `G - v` is `G - v - a` plus the vertex `a` and the single
    edge `ac`; `a` has degree 1 there, its 5 rows are independent and its
    column block is touched by nothing else, so no self-stress can charge
    them: the two left-nullspaces are isomorphic.
  * `U = U' n C(ac)^perp`, where `C(ac)` is built from the SEED's `pt(a)`.
    Motions of `G - v` are motions of `G - v - a` with
    `m(a) = m(c) + t C(ac)`, so `{m(a) - m(b)} = image(delta) + <C(ac)>` for
    `delta : m |-> m(c) - m(b)`.  Hence `U subset U'` with
    `dim U' - dim U in {0, 1}`.
  * `need' - need = dim U' - dim U`, because `need = s0 + dim U - c_G` and
    `need' = s0' + dim U' - c_G` with the SAME `c_G` (same `G`, same target).

THE CONSEQUENCE, and it is why the answer does not depend on the number
(Step INS11, (INS-12)).  At a hit seed `Pihat(b) = Pihat(c) =: Pihat`
((INS-4)), and all three hinges of the joint sweep lie in the 3-dimensional
`Lambda^2 Pihat`: `C(vb) = hat(x_v) ^ hat(p_b)` and
`C(ac) = hat(x_a) ^ hat(p_c)` by the sweep's own domain, and
`C(va) = hat(x_v) ^ hat(x_a)` because BOTH moving points lie in that one
plane.  Every row of `M'` is therefore `u |-> <u, C>` with `C in Lambda^2
Pihat`, so for EVERY point of the two-parameter domain simultaneously

    rank M' <= rank<U', Lambda^2 Pihat>       (a subspace bound, cap-free)
             <= rank<U, Lambda^2 Pihat> + (dim U' - dim U)
             =  1 + (need' - need)  =  need' - 1.

So the necessary condition `rank<U', Lambda^2 Pihat> >= need'` FAILS, and it
fails STRUCTURALLY: the joint sweep's extra dimension of freedom raises the
required rank by exactly as much as it can raise the available pairing rank,
so BINSERT's deficit of 1 is PRESERVED and cannot be spent.  Shape 4 is
excluded and option B is spent outright.

A DEFECT IN THE RECORDED KILL CONDITION, caught by this derivation.  The
close-it cell's threshold -- *"`>= 2` there would give option B an endpoint"*
-- is the ONE-vertex `need`.  The joint sweep's required rank is `need'`,
which is `2` only when `dim U' = dim U` and is `3` otherwise, so a future
reader who measured `rank<U', Lambda^2 Pihat> = 2` against the recorded
threshold would resurrect a refuted route.  Both branches are reported per
seed below; the operative comparison is always `rank` vs `need'`.

Modes:
  `uprime`   Steps INS8/INS9, (INS-9)/(INS-10): `U'` derived at the 8 (BE-5)
             hit seeds, the two-vertex corank identity CHECKED against the
             exact rank of `R(G)` at sampled joint placements, and the three
             structure facts asserted per seed.
  `pairing`  Step INS10, (INS-11): THE MEASUREMENT -- `rank<U', Lambda^2
             Pihat>` beside `dim U'`, `need'`, and BINSERT's own
             `rank<U, Lambda^2 Pihat>` reproduced at the same seeds.
  `deficit`  Step INS11, (INS-12): the deficit-preservation inequality tested
             as its own sentence -- on the measured objects, on CONSTRUCTED
             (U subset U', L) triples including an equality case, and with an
             adversarial witness the bound must NOT reject.
  `sweep`    Step INS12, (INS-13): the direct corroboration -- joint
             placements are LEGAL pencil witnesses (the domain is inhabited,
             so the exclusion is not vacuous), every one fails at the hits,
             and a control seed's joint sweep ATTAINS (the negative control).
  `dz`       Step INS13, (INS-14): the structural facts on a SECOND gadget --
             the DZ corank-2 population, where route A never hit.

CAPS, stated where the figures are (RESEARCH-ARC.md section 5), and including
the axes this generator makes it IMPOSSIBLE to vary (the BGTWOA sharpening):
  * The 8 seeds are (BE-5)'s own battery -- `BATTERY` (6 degeneracy strata)
    x 10 seeds from `seed0 = 52000`, at `q3_gadget()`'s hub-end split.  A
    joint-sweep escape at an UNTESTED seed is not excluded by the measurement
    alone; what IS cap-free is the per-seed verdict (a subspace bound over the
    whole two-parameter domain) and the derivation (INS-9)/(INS-10)/(INS-12),
    which uses no seed at all.
  * HARDCODED, not sampled: `q3_gadget()` returns the FIRST length assignment
    its own `product((1,2,3), ...)` scan accepts, so the gadget is ONE labelled
    graph, not a family; `chain_partner` returns the FIRST degree-2 neighbour
    in `sorted(..., key=str)` order, so the chain `b -- v -- a -- c` is one
    chain of the gadget's several; `defs=(0, 0)` is asserted elsewhere
    (`optc.py c2`) and fixed here; `index(G) = 2` / `corank(G') = 3` is the
    only stratum (that is (INS-5)'s confinement, and it is where the
    refutation lives); `panel_l2` draws its 3 in-plane points from ONE
    `random.Random(seed0 + s)` stream.  None of these axes is varied by any
    number of seeds.
  * `nplace`/`njoint` sweeps are SAMPLED corroboration only; the verdict never
    rests on them.

Harness debt (recorded, NOT paid -- a dispatch does not move a landed name,
`notes/scripts/README.md` *Harness debt*):
  * this is the **THIRD** `w4/` cross-stack consumer of the standing UNPAID
    `kbare/` sibling-import item (probe KBARE-FALSIFY created it; BATTAIN
    first, BINSERT second), so that item is now **OVERDUE by its own rule**.
    It imports `breakhunt`'s `split_ctx`, `seed_calculus`, `need_rank`,
    `hub_domain`, `pairing_rank`, `uniform_failure_exact`, `observed`,
    `q3_gadget`, `sample_pencil_bfs`, `BATTERY`, plus `danger.dz_gadget`,
    `repin.lambda2_plane` and seven `kbare_common` primitives.
  * it is also the **FIRST external consumer of any `binsert` device**
    (`chain_partner`, `panel_l2`, `verdict`) -- taken rather than cloned so
    the hit set is IDENTICAL BY CONSTRUCTION to BINSERT's 8 and the panel
    bases are the same objects (BE-5)'s figures were measured on.  A second
    consumer would trip the section-2 rule-2 threshold.
  * no new hazard item: `bimage` is not imported at all, so `bimage.pt_in`'s
    silent `Lambda^2 K^4 -> K^4` truncation is UNREACHABLE from here rather
    than merely avoided -- which matters because every draw in this driver is
    a `Lambda^2` draw.  Every panel normal is asserted to span a 1-dimensional
    nullspace (a check `panel_l2` itself does not make) and every
    `lambda2_plane` return is asserted non-`None` and rank 3.

WHAT IT MEASURED (2026-09-09, at HEAD `4a3d7c36`; every figure below is
reproduced by the mode named beside it):
  * `uprime`  : 8 hit seeds, all in the `cycleflat` stratum, reproducing
                (BE-5)/(INS-3)'s battery.  `s0' = s0 = 0` at 8/8;
                `dim U = 4 -> dim U' = 5` at 8/8; `need = 2 -> need' = 3` at
                8/8; the two-vertex corank identity holds at 48/48 sampled
                joint placements.
  * `pairing` : `rank<U, Lambda^2 Pihat> = 1` at 8/8 (BINSERT's own figure,
                asserted equal to `breakhunt.pairing_rank`'s) and
                `rank<U', Lambda^2 Pihat> = 2` at 8/8 -- against `need' = 3`.
                Shape 4 EXCLUDED at 8 of 8.
  * `deficit` : deficit `rank - need` is `-1` at 8/8 hits and `+2` at 19/19
                non-hit target-rank controls; the inequality is valid on 400
                random triples, ATTAINED on 200 constructed ones of the
                measured shape, and SATISFIED on 200 constructed
                deficit-zero ones (so it does not reject an escape that
                exists).
  * `sweep`   : 160 legal joint placements over the 8 hits, observed exact
                rank 137 against target 138 at every one, `rank M' = 2`
                throughout; 0 attain.  Negative control: at the non-hit
                target-rank seeds the same sweep ATTAINS at 20/20.
  * `dz`      : 117 DZ seeds on a second gadget, the three structure facts and
                the corank identity at 117/117, `dim U' - dim U in {0, 1}`.

So the recorded threshold would have said SURVIVES and the correct one says
EXCLUDED, on the same measured number.

ONE FURTHER RECORDED OBSERVATION, deliberately not repaired (`dz` prints it):
at 3 of 117 DZ draws a chain end of degree `>= 3` has closed-star rank 2, so
`Pihat` there is not determined -- and `breakhunt.hub_domain` /
`binsert.panel_l2` both take `nullspace(anchors)[0]` without asserting the
nullspace is 1-dimensional, so they silently return AN arbitrary plane through
the line rather than THE panel.  It cannot have flipped a recorded verdict
(every affected population reports ZERO uniform failures, and the true domain
there is the whole chart, which only makes escape easier), and none of the 8
Q3 hit seeds is affected -- `pairing` asserts both star ranks are 3 there.
`panel_of` in this file is the version that checks.

Reproduce (two runs each where they differed; the spread is machine load, the
figures are byte-identical):
            python3 notes/scripts/w4/insjoint.py uprime    (149-153 s)
            python3 notes/scripts/w4/insjoint.py pairing   (159-160 s)
            python3 notes/scripts/w4/insjoint.py deficit   (240 s)
            python3 notes/scripts/w4/insjoint.py sweep     (277-320 s)
            python3 notes/scripts/w4/insjoint.py dz        (424-439 s)
"""

import random, sys, time
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import (degrees, neighbors, verts_of, hat,  # noqa: E402
                          rank_exact, build_rigidity, verify_pencil_witness,
                          dot, nullspace, wedge2, point_on_affine_plane4,
                          rvec3)
from breakhunt import (split_ctx, seed_calculus, need_rank,  # noqa: E402
                       hub_domain, pairing_rank, uniform_failure_exact,
                       observed, q3_gadget, sample_pencil_bfs, BATTERY)
from danger import dz_gadget                        # noqa: E402  (sibling; debt)
from repin import lambda2_plane                     # noqa: E402
from binsert import chain_partner, panel_l2, verdict  # noqa: E402  (debt: 1st)

SEED0 = 52000
NSEEDS = 10


# ------------------------------------------------ the two-vertex context ----

def two_del_ctx(edges_G, v, defs=None):
    """The TWO-vertex-deleted context for the joint sweep: the chain
    `b -- v -- a -- c`, the shared framework `G - v - a`, and the data that
    does NOT depend on either moving point.

    Everything asserted rather than assumed: `deg v = deg a = 2`, `a`'s only
    neighbours are `v` and `c`, the chain does not close (`b != c`), and the
    shared framework still carries every remaining vertex."""
    nb, deg = neighbors(edges_G), degrees(edges_G)
    assert deg[v] == 2, f'{v} is not a degree-2 body'
    part = chain_partner(edges_G, v)
    assert part is not None, 'no adjacent degree-2 body: route B/shape 4 unavailable'
    a, c = part
    b = [x for x in nb[v] if x != a][0]
    assert deg[a] == 2 and set(nb[a]) == {v, c}, (
        f'{a} is not a degree-2 body with neighbours {{{v}, {c}}}')
    assert b != c, 'the chain closes into a triangle b--v--a--b'
    sh2 = [e for e in edges_G if v not in e and a not in e]
    Vsh2 = verts_of(sh2)
    assert set(Vsh2) == set(verts_of(edges_G)) - {v, a}, (
        'deleting v and a isolated a vertex; the index map would be wrong')
    assert b in Vsh2 and c in Vsh2, 'a chain end left the shared framework'
    ctxA = split_ctx(edges_G, v, defs=defs)
    return {'v': v, 'a': a, 'b': b, 'c': c, 'G': edges_G, 'sh2': sh2,
            'Vsh2': Vsh2, 'ctxA': ctxA, 'cG': ctxA['cG'], 'tG': ctxA['tG'],
            'nrows': 5 * len(edges_G)}


def uprime(ctx2, ptp2):
    """`s0'` and a basis of

        U' = {u : <u, m(c) - m(b)> = 0 for every motion m of G - v - a}

    from a point map `ptp2` on `V(G) \\ {v, a}`.  Same construction as
    `breakhunt.seed_calculus`'s `U` with the deleted vertex's two NEIGHBOURS
    replaced by the deleted PATH's two ENDS."""
    rows, _ = build_rigidity(ctx2['sh2'], ptp2)
    s0p = len(rows) - rank_exact(rows)
    Vsh2 = ctx2['Vsh2']
    ib, ic = Vsh2.index(ctx2['b']), Vsh2.index(ctx2['c'])
    funcs = [[m[6 * ic + k] - m[6 * ib + k] for k in range(6)]
             for m in nullspace(rows)]
    Up = nullspace(funcs) if funcs else [[F(1) if i == j else F(0)
                                          for i in range(6)] for j in range(6)]
    return s0p, Up


def crit3(ctx2, Up, x_v, x_a, pt_b, pt_c):
    """`M'(x_v, x_a)`, the 3 x dim U' criterion matrix of the joint sweep."""
    hv, ha = hat(x_v), hat(x_a)
    return [[dot(u, wedge2(hv, hat(pt_b))) for u in Up],      # C(vb)
            [dot(u, wedge2(hv, ha)) for u in Up],             # C(va)
            [dot(u, wedge2(ha, hat(pt_c))) for u in Up]]      # C(ac)


def panel_of(edges_G, ptp, h, exclude):
    """`(4-normal of Pihat(h), rank of the anchors)` from `h`'s own point and
    its `G`-neighbours OTHER than `exclude`.

    The normal is `None` exactly when the anchors have rank `< 3`, i.e. when
    `Pihat(h)` is NOT determined -- and then the moving point is genuinely
    UNCONSTRAINED (three or fewer collinear/coplanar fixed points plus one
    free point are coplanar for free), so the sweep's domain is larger than a
    panel.  `breakhunt.hub_domain` and `binsert.panel_l2` take `ns[0]` out of
    a possibly higher-dimensional nullspace without this check, so at such a
    draw they silently return AN arbitrary plane through the anchors rather
    than THE panel; the rank is reported here so a degenerate draw is visible
    instead of being absorbed.  Recorded, not repaired: a dispatch does not
    move a landed name."""
    nb = neighbors(edges_G)
    anchors = [hat(ptp[h])] + [hat(ptp[w]) for w in sorted(nb[h], key=str)
                               if w not in exclude and w in ptp]
    rk = rank_exact(anchors)
    if rk < 3:
        return None, rk
    ns = nullspace(anchors)
    assert len(ns) == 1, 'rank 3 anchors must leave exactly one normal'
    assert any(ns[0][i] != 0 for i in range(3)), f'Pihat({h}) is at infinity'
    return ns[0], rk


def domains(ctx2, ptp):
    """THE JOINT SWEEP'S ACTUAL DOMAINS, derived off `verify_pencil_witness`
    rather than assumed: `pt(v)` is confined to `Pihat(b)` exactly when `b`'s
    closed star minus `v` has RANK 3 (only then is a plane forced), and
    `pt(a)` to `Pihat(c)` exactly when `c`'s closed star minus `a` does.
    `v`'s own star `{v, a, b}` and `a`'s `{a, v, c}` are three points each and
    are coplanar for free, so they impose nothing.

    Returns `(nrm_b, nrm_c, rk_b, rk_c)`, a `None` normal meaning that end is
    UNCONSTRAINED -- a real scope boundary, not a nuisance: there the three
    hinges need not lie in one `Lambda^2 Pihat` and the shape-4 bound does
    not apply."""
    nrm_b, rk_b = panel_of(ctx2['G'], ptp, ctx2['b'], {ctx2['v']})
    nrm_c, rk_c = panel_of(ctx2['G'], ptp, ctx2['c'], {ctx2['a']})
    return nrm_b, nrm_c, rk_b, rk_c


def joint_point(nrm, rng):
    return rvec3(rng) if nrm is None else point_on_affine_plane4(nrm, rng)


# ----------------------------------------------------- the (BE-5) hit set ---

def hit_seeds(edges, v, defs=(0, 0), nseeds=NSEEDS, seed0=SEED0, quiet=False):
    """(BE-5)'s own hit battery, reproduced through `binsert.verdict` so the
    set is IDENTICAL BY CONSTRUCTION to BINSERT's 8: every legal target-rank
    `G'` seed of `BATTERY` x `nseeds` at which route A fails uniformly."""
    ctxA = split_ctx(edges, v, defs=defs)
    hits = []
    for degen in BATTERY:
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctxA['Gp'], rng, degen=degen)
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctxA, ptp)
            if sd is None or not sd['at_target']:
                continue
            vA = verdict(ctxA, ptp, sd, 'A', seed0 + s)
            if 'skip' in vA or not vA['uniform_fail']:
                continue
            hits.append((degen, s, ptp, sd, vA))
    if not quiet:
        print(f'  (BE-5) hit battery: {len(hits)} route-A uniform-failure '
              f'seeds over {len(BATTERY)} strata x {nseeds} seeds '
              f'(seed0 = {seed0}); strata hit: '
              f'{sorted({str(d) for d, *_ in hits})}')
    return ctxA, hits


def controls(ctxA, nseeds=NSEEDS, seed0=SEED0):
    """Non-hit target-rank seeds -- the robust-generic and global-hub-coplanar
    strata, i.e. `binsert.run_combined`'s own controls."""
    out = []
    for degen in (None, 'hubplane'):
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctxA['Gp'], rng, degen=degen)
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctxA, ptp)
            if sd is None or not sd['at_target']:
                continue
            vA = verdict(ctxA, ptp, sd, 'A', seed0 + s)
            if 'skip' in vA or vA['uniform_fail']:
                continue
            out.append((degen, s, ptp, sd, vA))
    return out


def q3_chain():
    edges = q3_gadget()
    deg, nb = degrees(edges), neighbors(edges)
    v = next(x for x in verts_of(edges) if deg[x] == 2
             and any(deg[w] == 2 for w in nb[x])
             and any(deg[w] >= 3 for w in nb[x]))
    return edges, v


# ------------------------------------------------------------ Step INS8/9 ---

def seed_row(ctx2, ptp, sd, njoint=6, seed=0):
    """Everything one seed contributes: `U'`, the three structure facts of
    (INS-10), the two-vertex corank identity checked against the EXACT rank
    of `R(G)` at sampled joint placements, and -- when BOTH chain ends are
    hubs -- the panel collapse and the pairing ranks."""
    v, a, b, c = ctx2['v'], ctx2['a'], ctx2['b'], ctx2['c']
    ptp2 = {w: ptp[w] for w in ptp if w != a}
    s0p, Up = uprime(ctx2, ptp2)
    dUp = rank_exact(Up)
    s0, U, dU = sd['s0'], sd['U'], sd['dimU']
    need = need_rank(ctx2['ctxA'], sd)
    needp = s0p + dUp - ctx2['cG']

    # --- (INS-10) the three structure facts, asserted ---
    assert s0p == s0, f"s0' = {s0p} != s0 = {s0}"
    Cac_seed = wedge2(hat(ptp[a]), hat(ptp[c]))
    assert rank_exact(list(Up) + list(U)) == dUp, 'U is not inside U-prime'
    assert all(dot(u, Cac_seed) == 0 for u in U), 'U is not inside C(ac)^perp'
    drop = rank_exact([[dot(u, Cac_seed) for u in Up]])
    assert dUp - drop == dU, (
        f"dim(U' n C(ac)^perp) = {dUp - drop} != dim U = {dU}")
    assert needp - need == dUp - dU, (
        f"need' - need = {needp - need} != dim U' - dim U = {dUp - dU}")

    # --- the joint sweep's own domains, and the seed's place inside them ---
    nrm_b, nrm_c, rk_b, rk_c = domains(ctx2, ptp)
    if nrm_b is not None:
        assert dot(nrm_b, hat(ptp[a])) == 0, (
            "the seed's pt(a) is not in Pihat(b) -- the fresh edge ab forces it")
        dom_b = hub_domain(ctx2['ctxA'], ptp)
        assert dom_b is not None and rank_exact([nrm_b, dom_b]) == 1, (
            'panel_normal disagrees with breakhunt.hub_domain on Pihat(b)')
    if nrm_c is not None:
        assert dot(nrm_c, hat(ptp[a])) == 0, (
            "the seed's pt(a) is not in Pihat(c) -- the joint domain would "
            'miss the seed')
    both_panels = nrm_b is not None and nrm_c is not None
    collapse = both_panels and rank_exact([nrm_b, nrm_c]) == 1

    # --- the pairing ranks, against the SAME panel bases BINSERT measured ---
    pr_U = pr_Up = pr_U_b = pr_Up_b = dim_L = None
    inside = None
    if both_panels:
        r = random.Random(seed)
        Lb = panel_l2(ctx2['ctxA'], ptp, b, r)
        Lc = panel_l2(ctx2['ctxA'], ptp, c, r)
        assert Lb is not None and Lc is not None, 'a panel basis came back None'
        assert rank_exact(Lb) == 3 and rank_exact(Lc) == 3, (
            'a Lambda^2 panel is not 3-dimensional')
        L = list(Lb) if collapse else list(Lb) + list(Lc)
        pr_U = rank_exact([[dot(u, l) for l in L] for u in U])
        pr_Up = rank_exact([[dot(u, l) for l in L] for u in Up])
        pr_U_b = rank_exact([[dot(u, l) for l in Lb] for u in U])
        pr_Up_b = rank_exact([[dot(u, l) for l in Lb] for u in Up])
        dim_L = rank_exact(L)
        # rank-nullity, machine-checked rather than deduced in prose: a
        # pairing rank of `dim U - dim L^perp` means `L^perp` sits INSIDE `U`.
        Lperp = nullspace(L)
        inside = rank_exact(list(U) + list(Lperp)) == dU
        assert (dU - pr_U == rank_exact(Lperp)) == inside, (
            'the rank-nullity reading of the pairing rank is inconsistent')

    # --- (INS-9) the identity, checked against the exact rank of R(G) ---
    ids, legal, ranks, mranks = [], 0, [], []
    rj = random.Random(seed + 7717)
    for _ in range(njoint):
        x_v, x_a = joint_point(nrm_b, rj), joint_point(nrm_c, rj)
        pt = dict(ptp2)
        pt[v], pt[a] = x_v, x_a
        try:
            rows, _ = build_rigidity(ctx2['G'], pt)
        except AssertionError:
            continue                      # coincident adjacent points
        ok, _ = verify_pencil_witness(ctx2['G'], pt)
        legal += 1 if ok else 0
        obs = ctx2['nrows'] - rank_exact(rows)
        rk = rank_exact(crit3(ctx2, Up, x_v, x_a, ptp[b], ptp[c]))
        pred = s0p + dUp - rk
        ids.append(obs == pred)
        assert obs == pred, (
            f'two-vertex corank identity FAILS: observed {obs} != '
            f'predicted {pred}')
        mranks.append(rk)
        if ok:
            ranks.append(ctx2['nrows'] - obs)
    return {'s0': s0, 's0p': s0p, 'dimU': dU, 'dimUp': dUp, 'need': need,
            'needp': needp, 'collapse': collapse, 'both_panels': both_panels,
            'pair_U': pr_U, 'pair_Up': pr_Up, 'pair_U_b': pr_U_b,
            'pair_Up_b': pr_Up_b, 'dim_L': dim_L, 'Lperp_in_U': inside,
            'identity': (sum(ids), len(ids)), 'legal_joint': legal,
            'rk_b': rk_b, 'rk_c': rk_c,
            'joint_ranks': sorted(set(ranks)), 'mranks': sorted(set(mranks)),
            'target': ctx2['tG'], 'Up': Up, 'U': U,
            'nrm_b': nrm_b, 'nrm_c': nrm_c}


def run_uprime():
    print("===== INSJOINT: `U'` for the TWO-vertex-deleted framework =====")
    print("  Step INS8 / (INS-9): the object, and the corank identity it")
    print("  satisfies, CHECKED against the exact rank of R(G) at sampled")
    print("  joint placements.  Step INS9 / (INS-10): the three structure")
    print("  facts that link it to BINSERT's one-vertex `U`.")
    edges, v = q3_chain()
    ctx2 = two_del_ctx(edges, v, defs=(0, 0))
    print(f"\n  Q3 index-2 hub-end: chain b={ctx2['b']} -- v={ctx2['v']} -- "
          f"a={ctx2['a']} -- c={ctx2['c']}; |E(G)|={len(edges)} "
          f"|E(G-v-a)|={len(ctx2['sh2'])} c_G={ctx2['cG']} "
          f"target(G)={ctx2['tG']}")
    ctxA, hits = hit_seeds(edges, v)
    rows = []
    for degen, s, ptp, sd, _vA in hits:
        row = seed_row(ctx2, ptp, sd, seed=SEED0 + s)
        rows.append((degen, s, row))
        print(f"    seed {s:>2}/{str(degen):9s}: s0={row['s0']} "
              f"s0'={row['s0p']}  "
              f"dim U={row['dimU']} -> dim U'={row['dimUp']}  "
              f"need={row['need']} -> need'={row['needp']}  "
              f"identity {row['identity'][0]}/{row['identity'][1]} "
              f"joint placements")
    if rows:
        ok = sum(r['identity'][0] for _, _, r in rows)
        tot = sum(r['identity'][1] for _, _, r in rows)
        print(f"\n  >>> the two-vertex corank identity holds at {ok}/{tot} "
              f"sampled joint placements over {len(rows)} hit seeds")
        print(f"      s0' = s0 at {len(rows)}/{len(rows)};  "
              f"dim U' - dim U in "
              f"{sorted({r['dimUp'] - r['dimU'] for _, _, r in rows})};  "
              f"need' in {sorted({r['needp'] for _, _, r in rows})}")
        print("      So `U'` is NOT `U`: the joint sweep's shared framework")
        print("      loses the edge `ac`, and with it one linear condition.")
    else:
        print('  no hit seed reached under this cap')
    return rows


# --------------------------------------------------------- Step INS10 ------

def run_pairing():
    print('===== INSJOINT: THE MEASUREMENT -- rank<U-prime, L2 Pihat> =====')
    print("  Step INS10 / (INS-11).  The close-it cell's own question, with")
    print("  the threshold it is measured against stated per seed: the joint")
    print("  sweep attains target(G) only where rank M' = need', and every")
    print("  row of M' pairs U' against Lambda^2 Pihat, so")
    print("  rank<U', L2 Pihat> >= need' is NECESSARY.")
    edges, v = q3_chain()
    ctx2 = two_del_ctx(edges, v, defs=(0, 0))
    ctxA, hits = hit_seeds(edges, v)
    print(f'\n  {"seed":14s} {"collapse":>9s} {"dimU":>5s} {"dimU1":>6s} '
          f'{"<U,L>":>6s} {"<U1,L>":>7s} {"need":>5s} {"need1":>6s} '
          f'{"verdict":>10s}')
    rows, verdicts = [], []
    for degen, s, ptp, sd, _vA in hits:
        row = seed_row(ctx2, ptp, sd, seed=SEED0 + s)
        assert row['pair_U_b'] == _vA['pairing_rank'], (
            f"BINSERT's own pairing_rank disagrees with the local "
            f"measurement: {_vA['pairing_rank']} vs {row['pair_U_b']}")
        assert row['collapse'], (
            'Pihat(b) != Pihat(c) at a (BE-5) hit seed -- (INS-4) says they '
            'coincide, and the shape-4 argument needs it')
        live = row['pair_Up'] >= row['needp']
        verdicts.append(live)
        rows.append((degen, s, row))
        assert row['Lperp_in_U'], (
            "rank<U,L> = 1 with dim L^perp = 3 and dim U = 4 forces "
            "L^perp inside U; it is not")
        print(f'  {str(s)+"/"+str(degen):14s} {str(row["collapse"]):>9s} '
              f'{row["dimU"]:>5d} {row["dimUp"]:>6d} {row["pair_U"]:>6d} '
              f'{row["pair_Up"]:>7d} {row["need"]:>5d} {row["needp"]:>6d} '
              f'{"LIVE" if live else "EXCLUDED":>10s}')
    if rows:
        prs = sorted({r['pair_Up'] for _, _, r in rows})
        nds = sorted({r['needp'] for _, _, r in rows})
        print(f"\n  >>> rank<U', Lambda^2 Pihat> over {len(rows)} hit seeds: "
              f"{prs};  need' : {nds}")
        print(f"      shape 4 LIVE at {sum(verdicts)} of {len(rows)} seeds, "
              f"EXCLUDED at {len(rows) - sum(verdicts)}")
        print("      NOTE the threshold.  The recorded close-it cell says")
        print('      "`>= 2` would give option B an endpoint"; that is the')
        print("      ONE-vertex `need`.  The joint sweep's own required rank")
        print("      is `need'`, which is 2 only when dim U' = dim U.")
    else:
        print('  no hit seed reached under this cap')
    return rows


# --------------------------------------------------------- Step INS11 ------

def rank_pair(A, L):
    return rank_exact([[dot(u, l) for l in L] for u in A])


def run_deficit():
    print('===== INSJOINT: the DEFICIT-PRESERVATION inequality =====')
    print('  Step INS11 / (INS-12).  The verdict does not rest on the')
    print("  measured number -- it rests on this sentence:")
    print("     U subset U'  ==>  rank<U',L> <= rank<U,L> + (dim U' - dim U)")
    print("  which with  need' - need = dim U' - dim U  ((INS-10)) gives")
    print("     rank<U',L> - need'  <=  rank<U,L> - need  =  1 - 2  =  -1.")
    print('  Three tests: the measured objects, CONSTRUCTED triples, and an')
    print('  adversarial witness the bound must NOT reject.')

    # --- test 1: the inequality as a general statement, with a TIGHT
    # --- witness and a must-NOT-reject witness (section 4 conventions 1/6:
    # --- a guard observed only passing, or only passing slackly, is untested)
    print('\n  (1a) VALIDITY -- random (U subset U-prime, L) triples in K^6,')
    print('       the codimension-1 section taken against a random C:')
    bad = tight = n = 0
    for k in range(400):
        rg = random.Random(31000 + k)
        Wp = [[F(rg.randint(-6, 6)) for _ in range(6)] for _ in range(5)]
        if rank_exact(Wp) != 5:
            continue
        C = [F(rg.randint(-6, 6)) for _ in range(6)]
        if all(x == 0 for x in C):
            continue
        lam = nullspace([[dot(u, C) for u in Wp]])
        W = [[sum((l[i] * Wp[i][j] for i in range(5)), F(0))
              for j in range(6)] for l in lam]
        dWp, dW = rank_exact(Wp), rank_exact(W)
        L = [[F(rg.randint(-6, 6)) for _ in range(6)] for _ in range(3)]
        if rank_exact(L) != 3:
            continue
        n += 1
        rW, rWp = rank_pair(W, L), rank_pair(Wp, L)
        assert rWp <= rW + (dWp - dW), (
            f'the deficit inequality FAILS at k={k}: {rWp} > {rW} + '
            f'{dWp - dW}')
        tight += 1 if rWp == rW + (dWp - dW) else 0
    print(f'       {n} draws, 0 violations; the bound is TIGHT at {tight} of')
    print('       them -- at a random `L` both pairings saturate at dim L, so')
    print('       this family tests validity and NOT tightness.  Hence (1b).')

    print('\n  (1b) TIGHTNESS -- constructed witnesses of the measured shape')
    print('       (L^perp inside U, so the pairing is far from saturated):')
    ok = 0
    for k in range(200):
        rg = random.Random(41000 + k)
        L = [[F(rg.randint(-6, 6)) for _ in range(6)] for _ in range(3)]
        if rank_exact(L) != 3:
            continue
        Lp = nullspace(L)                       # dim 3
        u1 = [F(rg.randint(-6, 6)) for _ in range(6)]
        u2 = [F(rg.randint(-6, 6)) for _ in range(6)]
        W, Wp = list(Lp) + [u1], list(Lp) + [u1, u2]
        if rank_exact(W) != 4 or rank_exact(Wp) != 5:
            continue
        rW, rWp = rank_pair(W, L), rank_pair(Wp, L)
        if (rW, rWp) != (1, 2):
            continue
        assert rWp == rW + (rank_exact(Wp) - rank_exact(W)), 'not tight'
        ok += 1
    print(f'       {ok} constructed witnesses with rank<U,L> = 1 and')
    print('       rank<U-prime,L> = 2 = 1 + codim: the bound is ATTAINED, so')
    print('       it is not slack by accident -- and this is EXACTLY the')
    print('       measured shape at the 8 hit seeds (dim U = 4, rank 1;')
    print('       dim U-prime = 5, rank 2), i.e. L^perp lies inside U there.')

    print('\n  (1c) MUST NOT REJECT -- the same inequality with a one-vertex')
    print('       deficit of ZERO instead of -1, where the necessary')
    print('       condition must come out SATISFIED:')
    ok = 0
    for k in range(200):
        rg = random.Random(51000 + k)
        L = [[F(rg.randint(-6, 6)) for _ in range(6)] for _ in range(3)]
        if rank_exact(L) != 3:
            continue
        Lp = nullspace(L)
        u1 = [F(rg.randint(-6, 6)) for _ in range(6)]
        u2 = [F(rg.randint(-6, 6)) for _ in range(6)]
        W, Wp = list(Lp)[:2] + [u1, u2], list(Lp)[:2] + [u1, u2] + [
            [F(rg.randint(-6, 6)) for _ in range(6)]]
        if rank_exact(W) != 4 or rank_exact(Wp) != 5:
            continue
        rW, rWp = rank_pair(W, L), rank_pair(Wp, L)
        if (rW, rWp) != (2, 3):
            continue
        ok += 1
    print(f'       {ok} witnesses with rank<U,L> = 2 = need and')
    print("       rank<U-prime,L> = 3 = need': the joint sweep's necessary")
    print('       condition is SATISFIED there.  So the exclusion below is')
    print('       NOT an artifact of the inequality -- it INHERITS from')
    print("       (INS-3)/(BE-5)'s measured rank 1, i.e. from route A failing")
    print('       by a strictly positive margin.')

    # --- test 2: the measured objects ---
    print('\n  (2) the measured objects at the 8 (BE-5) hit seeds:')
    edges, v = q3_chain()
    ctx2 = two_del_ctx(edges, v, defs=(0, 0))
    ctxA, hits = hit_seeds(edges, v)
    defs = []
    for degen, s, ptp, sd, _vA in hits:
        row = seed_row(ctx2, ptp, sd, seed=SEED0 + s)
        dU, dUp = row['dimU'], row['dimUp']
        rU, rUp = row['pair_U'], row['pair_Up']
        assert rUp <= rU + (dUp - dU), 'the deficit inequality FAILS on a seed'
        d0, d1 = rU - row['need'], rUp - row['needp']
        assert d1 <= d0, 'the deficit is not preserved'
        defs.append((d0, d1))
        print(f'      seed {s:>2}/{str(degen):9s}: deficit(one-vertex) = '
              f'{d0:>2d}   deficit(joint) = {d1:>2d}   '
              f'{"PRESERVED" if d1 <= d0 else "SPENT"}')
    if defs:
        print(f"      >>> deficit(joint) in {sorted({d for _, d in defs})} at "
              f"{len(defs)}/{len(defs)} seeds -- strictly negative, so")
        print("          rank M' < need' EVERYWHERE on the two-parameter")
        print('          domain: uniform failure of the joint sweep, CAP-FREE')
        print('          per seed (a subspace bound, not a sampled sweep).')

    # --- test 3: the bound must be DISCRIMINATING, not always negative ---
    print('\n  (3) the deficit must be a DISCRIMINATING quantity, or the')
    print('      test is vacuous.  At the non-hit target-rank controls route')
    print('      A ATTAINS, and there the same arithmetic must NOT fire.')
    print('      (The containment C(va) in Lambda^2 Pihat needs the panel')
    print('      collapse, so off the hits the bound is not a necessary')
    print('      condition at all -- what is shown here is that the NUMBERS')
    print('      separate the two populations, cleanly.)')
    ctrl = controls(ctxA)
    seps = []
    for degen, s, ptp, sd, _vA in ctrl:
        row = seed_row(ctx2, ptp, sd, njoint=3, seed=SEED0 + s)
        d0 = row['pair_U'] - row['need']
        d1 = row['pair_Up'] - row['needp']
        seps.append((d0, d1))
        print(f'      {str(degen):9s} seed {s:>2}: collapse='
              f'{str(row["collapse"]):5s} dim L={row["dim_L"]} '
              f'rank<U,L>={row["pair_U"]} rank<U\',L>={row["pair_Up"]} '
              f'need={row["need"]} need\'={row["needp"]} -> '
              f'deficit {d0:+d} / {d1:+d}')
    if seps:
        print(f'      >>> over {len(seps)} controls: deficit(one-vertex) in '
              f'{sorted({d for d, _ in seps})}, deficit(joint) in '
              f'{sorted({d for _, d in seps})} -- all >= 0, against -1 at')
        print('          8/8 hits.  The exclusion is a property of the HIT')
        print('          stratum, not of the inequality.')
    return defs


# --------------------------------------------------------- Step INS12 ------

def run_sweep(njoint=20):
    print('===== INSJOINT: the DIRECT joint sweep =====')
    print('  Step INS12 / (INS-13).  Independent corroboration of the')
    print('  subspace bound: sample (pt v, pt a) in Pihat(b) x Pihat(c),')
    print('  CHECK each is a legal pencil witness of G (so the domain is')
    print('  inhabited and the exclusion is not vacuous), and report the')
    print('  OBSERVED exact rank of R(G) against target(G).')
    edges, v = q3_chain()
    ctx2 = two_del_ctx(edges, v, defs=(0, 0))
    ctxA, hits = hit_seeds(edges, v)
    tot_legal = tot_att = 0
    for degen, s, ptp, sd, _vA in hits:
        v_, a_, b_, c_ = ctx2['v'], ctx2['a'], ctx2['b'], ctx2['c']
        ptp2 = {w: ptp[w] for w in ptp if w != a_}
        s0p, Up = uprime(ctx2, ptp2)
        nrm_b, nrm_c, _rb, _rc = domains(ctx2, ptp)
        assert nrm_b is not None and nrm_c is not None, (
            'a chain end is not a hub: the joint domain is not a product of '
            'two panels here')
        needp = s0p + rank_exact(Up) - ctx2['cG']
        rj = random.Random(SEED0 + s + 4242)
        legal, ranks, mranks = 0, [], []
        for _ in range(njoint):
            x_v, x_a = joint_point(nrm_b, rj), joint_point(nrm_c, rj)
            pt = dict(ptp2)
            pt[v_], pt[a_] = x_v, x_a
            try:
                rows, _ = build_rigidity(edges, pt)
            except AssertionError:
                continue
            ok, _ = verify_pencil_witness(edges, pt)
            if not ok:
                continue
            legal += 1
            ranks.append(rank_exact(rows))
            mranks.append(rank_exact(crit3(ctx2, Up, x_v, x_a,
                                           ptp[b_], ptp[c_])))
        att = sum(1 for r in ranks if r == ctx2['tG'])
        tot_legal += legal
        tot_att += att
        assert all(r < needp for r in mranks), (
            "rank M' reached need' at a sampled joint placement -- the "
            'subspace bound is contradicted')
        assert att == 0, (
            f'a joint placement ATTAINS target(G) at a hit seed: {ranks}')
        print(f'    seed {s:>2}/{str(degen):9s}: {legal:>2d} legal joint '
              f"placements, observed ranks {sorted(set(ranks))} vs "
              f"target {ctx2['tG']}, rank M' in {sorted(set(mranks))} "
              f"(need' = {needp}) -> {att} attain")
    print(f'\n  >>> {tot_legal} legal joint placements over {len(hits)} hit '
          f'seeds; {tot_att} attain target(G).')
    print('      The domain is INHABITED (so shape 4 is a real sweep, not an')
    print('      empty one) and every point of it fails.')
    print('\n  negative control -- the same sweep at the non-hit target-rank')
    print('  seeds, where route A attains and the joint sweep must too:')
    ctrl = controls(ctxA)
    for degen, s, ptp, sd, _vA in ctrl[:6]:
        a_, b_, c_, v_ = ctx2['a'], ctx2['b'], ctx2['c'], ctx2['v']
        ptp2 = {w: ptp[w] for w in ptp if w != a_}
        s0p, Up = uprime(ctx2, ptp2)
        nrm_b, nrm_c, _rb, _rc = domains(ctx2, ptp)
        rj = random.Random(SEED0 + s + 9191)
        ranks = []
        for _ in range(njoint):
            x_v, x_a = joint_point(nrm_b, rj), joint_point(nrm_c, rj)
            pt = dict(ptp2)
            pt[v_], pt[a_] = x_v, x_a
            try:
                rows, _ = build_rigidity(edges, pt)
            except AssertionError:
                continue
            ok, _ = verify_pencil_witness(edges, pt)
            if ok:
                ranks.append(rank_exact(rows))
        att = sum(1 for r in ranks if r == ctx2['tG'])
        print(f'    {str(degen):9s} seed {s:>2}: {len(ranks)} legal, '
              f'observed ranks {sorted(set(ranks))} vs target '
              f"{ctx2['tG']} -> {att} ATTAIN")
    return tot_legal, tot_att


# --------------------------------------------------------- Step INS13 ------

def run_dz(nseeds=NSEEDS, seed0=SEED0):
    print('===== INSJOINT: the structure facts on a SECOND gadget =====')
    print('  Step INS13 / (INS-14).  (INS-9)/(INS-10) are proved, not')
    print('  measured, so they must hold off the Q3 hit stratum too.  DZ is')
    print('  the corank-2 index-1 population where route A never hit')
    print('  ((INS-5)), and it varies the ONE axis the Q3 generator cannot:')
    print('  the gadget.')
    edges = dz_gadget()
    deg, nb = degrees(edges), neighbors(edges)
    cands = [x for x in verts_of(edges) if deg[x] == 2
             and any(deg[w] == 2 for w in nb[x])]
    print(f'\n  DZ: |V|={len(verts_of(edges))} |E|={len(edges)}; '
          f'degree-2 bodies with a degree-2 neighbour: {cands}')
    tot = ok_id = degen_panels = 0
    for v in cands:
        try:
            ctx2 = two_del_ctx(edges, v, defs=(0, 0))
        except AssertionError as e:
            print(f'    v={v}: no two-vertex chain ({e})')
            continue
        ctxA = ctx2['ctxA']
        print(f"    chain b={ctx2['b']} -- v={ctx2['v']} -- a={ctx2['a']} -- "
              f"c={ctx2['c']}  index={ctxA['index']} corank(G')={ctxA['cGp']}")
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctxA['Gp'], rng, degen='cycleflat')
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctxA, ptp)
            if sd is None:
                continue
            try:
                row = seed_row(ctx2, ptp, sd, njoint=3, seed=seed0 + s)
            except AssertionError as e:
                print(f'      seed {s:>2}: STRUCTURE FACT FAILED -- {e}')
                raise
            tot += 1
            ok_id += 1 if row['identity'][0] == row['identity'][1] else 0
            dg = degrees(edges)
            if ((dg[ctx2['b']] >= 3 and row['rk_b'] < 3)
                    or (dg[ctx2['c']] >= 3 and row['rk_c'] < 3)):
                degen_panels += 1
            pr = (f"panels: NOT a product (star ranks b/c = "
                  f"{row['rk_b']}/{row['rk_c']}; a free end)"
                  if not row['both_panels'] else
                  f"collapse={row['collapse']} "
                  f"rank<U,L>={row['pair_U']} rank<U',L>={row['pair_Up']}")
            print(f"      seed {s:>2}: s0={row['s0']}=s0' "
                  f"dim U={row['dimU']} -> {row['dimUp']}  "
                  f"need={row['need']} -> {row['needp']}  {pr}  "
                  f"identity {row['identity'][0]}/{row['identity'][1]}")
    print(f'\n  >>> {tot} DZ seeds: the three structure facts and the')
    print(f'      two-vertex corank identity hold at {ok_id}/{tot} '
          f'(assert-gated, so a failure would have raised).')
    print(f'  >>> RECORDED OBSERVATION, not repaired: at {degen_panels} of '
          f'{tot} draws a chain end of degree >= 3 has closed-star rank 2,')
    print('      so `Pihat` there is NOT determined and `breakhunt.hub_domain`'
          ' / `binsert.panel_l2`')
    print('      return AN arbitrary plane through the line rather than THE')
    print('      panel (neither asserts `len(nullspace) == 1`).  It cannot')
    print('      have flipped a recorded verdict: the affected populations all')
    print('      report ZERO uniform failures, and the true domain there is')
    print('      the whole chart, which can only make escape EASIER -- an')
    print('      escape found inside an arbitrary sub-plane is still an')
    print('      escape.  None of the 8 Q3 hit seeds is affected (both star')
    print('      ranks are 3 there, asserted in `pairing`).')
    return tot, ok_id, degen_panels


MODES = {'uprime': run_uprime, 'pairing': run_pairing,
         'deficit': run_deficit, 'sweep': run_sweep, 'dz': run_dz}

if __name__ == '__main__':
    args = sys.argv[1:] or ['all']
    todo = list(MODES) if args == ['all'] else args
    for m in todo:
        if m not in MODES:
            raise SystemExit(f'unknown mode {m!r}; modes: {", ".join(MODES)}')
        t0 = time.time()
        MODES[m]()
        print(f'\n[insjoint {m}: {time.time() - t0:.0f}s]\n')
