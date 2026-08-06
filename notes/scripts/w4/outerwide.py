"""
Phase 39, section (K-out) CONTINUATION -- the widened combinatorial sweep, and
the hyperplane form of (OC-8).

WHY THIS DRIVER EXISTS.  `notes/Pencil-informal.md` section (K-out) *What would
change this* items 1-2 ask for a class shape with `dim R = 6` (which would kill
(OUT) there) or with `dim R <= 4` / `mu >= 2` (which would close (OUT)
unconditionally there), and say the first thing to do is to widen `--comb` past
the `|V*| <= 5` cap and the `lmax` bounds of `outer.sweep_shapes()`.  Item 6
asks for a symbolic treatment of `R_1 cap L_b`, `R_1` being a FAR object that
`m2/lambda0.m2`'s gauge slice does not reach.  This file answers both, and the
answer to the first is stronger than a widened no-hit:

  (OC-10) THE COMBINATORIAL AVAILABILITY MAP IS FORCED, NOT MEASURED.  At
    every class shape (tight, `def = 0`, `b` and `c` hubs, and `hnoRigid` --
    ALL FOUR are needed, see below), every eligible split and every length-4
    companion:
        chi = 0,  mu_1 = mu_4 = 1,  H/X and H/Y isostatic,
        A_1 = A_4 = 0,  dim R_1 = dim R_4 = 5.
    Proof (workbook Step O9): `def(G) = 0` with `5|E| = 6(|V|-1)` makes `5G`
    independent in the (6,6)-count matroid, so EVERY subgraph obeys
    `5|E'| <= 6|V'| - 6`; a cycle of length `L` has count `L - 6`, so the girth
    is `>= 6`, which kills all six possible chords of the companion and every
    second `b`-`X` edge; and a violating subgraph of `H/X` lifts, together with
    the three welded path edges, `b x_1` and the three split-path edges, to a
    `G`-subgraph `U` of count `< 0` -- EXCEPT in the one boundary case
    `5|K| = 6s + 1`, where `U` is TIGHT and independent, hence rigid, hence (a
    tight independent graph has min degree `>= 2`, so in a subdivision it is a
    union of COMPLETE branches) a rigid branch-union, PROPER because `b` is a
    hub whose third edge must leave `U`.  `hnoRigid` forbids that.  Hence items
    1-2 are UNREALIZABLE in the class: no widening can ever hit them.

    THE FIRST DRAFT OF THIS PROOF WAS WRONG, and `--adv` is what caught it: it
    discharged the boundary case by a pigeonhole on `W`-to-`X` edges, which is
    valid only when the violating subgraph has no `W`-`W` edge.  `--adv` rows 7
    and 8 are the counterexamples -- row 8 satisfies EVERY other hypothesis
    (count, girth, chi, no 2-into-weld, `b` and `c` hubs, `G` tight and
    isostatic) and still has `dim R_1 = 6`, its ONLY broken hypothesis being
    `hnoRigid`.  So `--wide` is corroboration of the CONCLUSION over a widened
    pool (5226 pairs) and `--adv` is the minimality test of the HYPOTHESES,
    each of which is shown load-bearing by a witness.

  (OC-11) THE HYPERPLANE FORM.  (OC-10) makes `dim R_1 = 5` a THEOREM, so
    `R_1` is a HYPERPLANE of `K^6` and the whole of (OUT)'s first disjunct is
    ONE linear functional.  Inside the panel: `beta_b` := the 3-dimensional
    space of lines of `Pi(b)` is totally `B`-isotropic, `dim(R_1 cap beta_b)
    >= 2` ALWAYS, and when it is exactly 2 that meet is the PENCIL of some
    single point `p` of `Pi(b)`.  Then
        lambda_1 = 0   <=>   p, pt(b), pt(x_1) collinear,
    so (OC-3)'s "exactly one marked direction of `x_1`'s pencil" acquires a
    FORMULA for the direction: it is `pt(b) -> p`.  And
        L_b subseteq R_1   <=>   p = pt(b),
    a single POINT coincidence in the panel plane -- (OC-8) restated as a
    codimension-2 non-coincidence rather than a rank lower bound.

  (OC-12) AT A DEGREE-3 HUB THE MARKED DIRECTION IS THE OTHER HINGE.  If
    `deg_G(b) = 3` (so `deg_H(b) = 2`, `b`'s H-neighbours being `x_1` and one
    other `u`), then `C(b,u) in R_1` unconditionally (rotate `b` about that
    hinge, its only one in `K`), so `p in C(b,u)` and the marked direction IS
    `C(b,u)`:
        lambda_1 = 0   <=>   C(b,x_1) = C(b,u)   (a COINCIDENT HINGE at `b`),
        unless `p = pt(b)`, i.e. unless `L_b subseteq R_1`.
    So (OC-7)'s measured implication *every `lambda_i = 0` frame carries a
    coincident hinge line at its hub, exhausting the hub's other H-neighbours*
    is a THEOREM at a degree-3 hub, with the free-rotor reading as its
    mechanism -- and `repin.star_generic` IMPLIES `lambda_1 != 0` there.

  (OC-13) THE BAD CASE, AND THE HUB SLIDE THAT DECIDES IT.  With `T_u` the
    relative twist space of `(u, v*)` in `(H/X) - b` (4-dimensional, and
    INDEPENDENT of `pt(b)`, `pt(x_1)` and `pt(a)`), `R_1 = <C(b,u)> (+) T_u`
    and `R_1 cap beta_b = <C(b,u)> (+) (T_u cap beta_b)`, so
        L_b subseteq R_1   <=>   dim(T_u cap beta_b) = 2,  or  pt(b) in C_0,
    where `C_0` is the line of `Pi(b)` spanning `T_u cap beta_b`.  Since `T_u`
    and `beta_b` do not see `pt(b)`, sliding `pt(b)` INSIDE its own panel is a
    legal chart move whenever `b` has no hub `G'`-neighbour, and `C_0` is then
    FIXED.  `--slide` runs both slides exactly: ONTO `C_0` (which would exhibit
    `L_b subseteq R_1` at a real class habitat, and a `lambda_1 = 0` point with
    NO coincident hinge) and OFF it.

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wide
    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --adv
    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wrench
    PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --slide

POOLS.  Each mode prints its pool and every figure is over that one pool;
nothing is aggregated across modes, and nothing here is aggregated with
`outerline.py`'s POOL-C / POOL-G / POOL-S / POOL-B.

  POOL-CW (--wide)   deterministic, no rng: `outer.named_inventory()` plus the
                     WIDENED family list `wide_shapes()` -- every family of
                     `outer.sweep_shapes()` at a raised `lmax` (theta3/theta4
                     and K4 now exhaustive over ALL admissible lengths), plus
                     theta5, two 3-hub multigraphs, K4 + two parallel edges,
                     the `|V*| = 5` families uncapped at a raised `lmax`, and
                     the `|V*| = 6` families capped.  Every family prints its
                     own coverage boundary.
  POOL-A  (--adv)    eight hand-built NON-class graphs, no rng: each breaks at
                     least one hypothesis of (OC-10) and exhibits a hit that
                     the class hypotheses forbid; the broken list is computed
                     per graph and asserted non-empty at every hit.
  POOL-W  (--wrench) the 4 `lambda.habitat_specs` habitats x placement seeds
                     200-219, accepted exactly as `outerline.frame_at` accepts
                     them (target rank, `dim R_a = 1`, `dim V_bc = 3`,
                     `rank{C_i} = 4`, closed-star ranks green); the composite
                     guard `repin.star_generic` is REPORTED per frame, since
                     (OC-12) is a statement ABOUT it.
  POOL-SL (--slide)  the same 4 habitats x seeds 200-219, restricted to frames
                     where `b` (resp. `c`) has no hub `G'`-neighbour, so the
                     slide is legal; deterministic slide targets.

CONVENTIONS (`notes/scripts/README.md` section 4): exact Q only; a degeneracy
guard and a rank/dimension assert on every sampled object; every rng is
`random.Random(<literal>)` and its seed is printed.  Nothing existing is
modified: `outerline.py`, `outer.py`, `lambda.py`, `repin.py` are all READ.

LAYERING (`notes/scripts/README.md` section 2).  A `w4/` leaf ABOVE
`outerline`, which it imports read-only for the welded relative-twist model
(`weld_motions`, `rel_span`, `line_pencil`, `marked_direction`, `comb_data`,
`frame_at`, `clauses`) -- the whole point being not to re-derive any of it (the
*Divergences* discipline).  Everything else comes from the catalogued section-1
primitives: `outer`, `repin`, `pitch`, `nogood_subdiv`, `exactcore`, `widened`,
`kslidecomb`, `flanks` and `lambda` (through `importlib`).
"""
import importlib
import itertools
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, hat, neighbors, nullspace, rank, wedge2  # noqa: E402
from kbare_common import verts_of                                   # noqa: E402
from nogood_subdiv import contraction, deficiency                    # noqa: E402
from pitch import coords_in, det4, klein                            # noqa: E402
from repin import (coincident_hinges, hinge_coincidences,            # noqa: E402
                   in_span, robust_plane_basis, span_basis,
                   star_generic, star_span_ranks)
from widened import place_pencil_general                             # noqa: E402
from flanks import nondeg_conjuncts                                  # noqa: E402
from kslidecomb import candidate_graphs                              # noqa: E402
import outer                                                         # noqa: E402
import outerline as OL                                               # noqa: E402

LAM = importlib.import_module('lambda')


# =================== part 1: (OC-10), the forced map ========================

def companion_sets(P):
    """The two welds `X = {x1,x2,x3,c}` and `Y = {b,x1,x2,x3}`."""
    return set(P[1:]), set(P[:4])


def two_into_weld(Hed, W):
    """Every vertex outside the weld `W` with TWO OR MORE `H`-neighbours in
    `W`.  Step O9's pigeonhole step: each such vertex closes a cycle of length
    `<= 5` through the welded path, which the girth-6 consequence of
    isostaticity forbids -- and it is exactly the configuration that would
    make `H/W` DEPENDENT (a 2-cycle at `v*`)."""
    nb = neighbors(Hed)
    out = []
    for u in sorted(nb, key=str):
        if u in W:
            continue
        if len(set(nb[u]) & W) >= 2:
            out.append((u, sorted(set(nb[u]) & W, key=str)))
    return out


def girth(edges, cap=7):
    """The length of a shortest cycle, or `> cap` reported as `cap + 1`.
    BFS from every vertex; exact and cheap at these sizes."""
    nb = neighbors(edges)
    best = cap + 1
    for s in sorted(nb, key=str):
        dist = {s: 0}
        par = {s: None}
        q = [s]
        while q:
            nq = []
            for v in q:
                for w in nb[v]:
                    if w == par[v]:
                        continue
                    if w in dist:
                        cyc = dist[v] + dist[w] + 1
                        best = min(best, cyc)
                    else:
                        dist[w] = dist[v] + 1
                        par[w] = v
                        nq.append(w)
            if min(dist.values(), default=0) >= best:
                break
            q = nq
        if best <= 3:
            break
    return best


def contracted_edges(Hed, W):
    """`E(H/W)` as an ordered list, `W` welded to `'v*'`, with multiplicity
    kept and the edges INTERNAL to `W` dropped -- `nogood_subdiv.contraction`
    is the canonical primitive, used exactly as `outerline.comb_data` uses
    it."""
    return contraction(Hed, sorted(W, key=str))


def chain_to_weld(Hed, W, b, x1):
    """`(ell_min, path)` -- the shortest `b`-to-`v*` path of `K = (H/X) - e_1`,
    as a vertex list in `H` (so its last vertex is the first `X`-vertex it
    reaches).  `dim R_1 = 5` forces `ell_min >= 5` (a cycle of `H/X` through
    `e_1` has length `ell_min + 1 >= 6`), and when `ell_min = 5` the relative
    twist space is exactly that chain's hinge-line span."""
    nb = neighbors(Hed)
    start = {b}
    prev = {b: None}
    frontier = [b]
    hit = None
    while frontier and hit is None:
        nxt = []
        for v in frontier:
            for w in sorted(nb[v], key=str):
                if w in prev:
                    continue
                if v == b and w == x1:
                    continue                     # e_1 is deleted from K
                if w in W:
                    prev[w] = v
                    hit = w
                    break
                prev[w] = v
                nxt.append(w)
            if hit is not None:
                break
        frontier = nxt
    if hit is None:
        return None, None
    path = [hit]
    while prev[path[-1]] is not None:
        path.append(prev[path[-1]])
    path.reverse()
    return len(path) - 1, path


def weld_paths(Hed, W, h, inner, maxlen=9):
    """Every simple `h`-to-`W` path of `H` of length `<= maxlen` whose first
    edge is NOT `h-inner` and whose interior avoids `W` -- i.e. every
    `h`-to-`v*` path of `K = (H/W) - e_1`.  `R_1` is contained in each one's
    hinge-line span."""
    nb = neighbors(Hed)
    out = []

    def walk(cur, seen, acc):
        if len(acc) - 1 >= maxlen:
            return
        for w in sorted(nb[cur], key=str):
            if w in seen:
                continue
            if cur == h and w == inner:
                continue
            if w in W:
                out.append(acc + [w])
                continue
            walk(w, seen | {w}, acc + [w])

    walk(h, {h}, [h])
    return out


def hub_free_end(Gp, h):
    """Does `h` have NO hub `G'`-neighbour?  (OC-13)'s legality criterion for
    the hub slide: then `pt(h)` may be moved anywhere inside its own panel
    with the panel and every other point held fixed."""
    nb = neighbors(Gp)
    return all(len(nb[u]) < 3 for u in nb[h])


def oc10_certificate(E, v, P):
    """(OC-10) at one (shape, split, length-4 companion): every step of Step
    O9's proof, asserted, plus the census row part 2 needs.  Returns a dict."""
    a, b, c, Gp, Hed = outer.split_data(E, v)
    VH = sorted(verts_of(Hed), key=str)
    X, Y = companion_sets(P)
    d = OL.comb_data(Hed, P)
    mu1, R1, A1, mu4, R4, A4, chi, dX, dY = d
    nV, nE = len(verts_of(E)), len(E)
    # (A) tight + isostatic, hence 5/6-sparse (the hypothesis of Step O9)
    assert 5 * nE == 6 * (nV - 1), "G is not tight"
    assert deficiency(E) == 0, "G is not rigid, so 5G is not independent"
    # (B) girth >= 6 kills every chord and every second b-X edge
    assert chi == 0, f"a chord survived: chi = {chi}"
    assert mu1 == 1 and mu4 == 1, f"mu != 1: {(mu1, mu4)}"
    # (C) the pigeonhole step: no outside vertex has two neighbours in a weld
    for W, tag in ((X, 'X'), (Y, 'Y')):
        bad = two_into_weld(Hed, W)
        assert not bad, f"a vertex has two {tag}-neighbours: {bad}"
    # the conclusion
    assert dX == 0 and dY == 0, f"H/X or H/Y is not rigid: {(dX, dY)}"
    assert (R1, A1, R4, A4) == (5, 0, 5, 0), f"the map moved: {d}"
    KX = contracted_edges(Hed, X)
    VKX = sorted((set(VH) - X) | {'v*'}, key=str)
    assert 6 * (len(VKX) - 1) - 5 * len(KX) == 0, "H/X is not tight"
    nb, nbH = neighbors(Gp), neighbors(Hed)
    lb, pb = chain_to_weld(Hed, X, b, P[1])
    lc, pc = chain_to_weld(Hed, Y, c, P[3])
    assert lb is not None and lb >= 5, f"ell_min(b) = {lb} < 5"
    assert lc is not None and lc >= 5, f"ell_min(c) = {lc} < 5"
    return {'degG': (len(nb[b]), len(nb[c])),
            'degH': (len(nbH[b]), len(nbH[c])),
            'hubfree': (hub_free_end(Gp, b), hub_free_end(Gp, c)),
            'ell': (lb, lc), 'free': outer.free_ends(Gp, P),
            'pat': tuple(int(x) for x in outer.hub_pattern(Gp, P)),
            'nV': nV}


THETA5 = [(0, 1)] * 5
M3A = [(0, 1), (0, 1), (0, 2), (0, 2), (1, 2)]
M3B = [(0, 1), (0, 1), (0, 2), (0, 2), (1, 2), (1, 2)]
K4_2PAR = outer.K4E + [(0, 1), (2, 3)]


def wide_shapes(cap5=60, cap6=12, lmax5=6, lmax6=6, e6max=10):
    """THE WIDENING.  Every family of `outer.sweep_shapes()` at a raised
    `lmax`, plus four families it does not reach at all.  Each row is
    `(description, shapes)` and the description states the coverage boundary
    exactly; `EXHAUSTIVE` means the `lmax` cannot bind, because tightness
    (`Sum l = 6(m - n + 1)`, with the split branch pinned at 3 and every other
    branch `>= 1`) caps every single length below it.

    `outer.shapes_from` is the canonical enumerator and is used unmodified; the
    only change is the bound it is called with."""
    out = []
    # `lmax` is EXHAUSTIVE for a family when it cannot bind: the split branch
    # is pinned at 3 and the other `m - 1` branches are `>= 1`, so no single
    # length can exceed `Sum l - 3 - (m - 2)` = `6(m - n + 1) - m - 1`.
    fams = [('theta3', 2, outer.THETA3, 9, None),
            ('theta4', 2, outer.THETA4, 13, None),
            ('theta5', 2, THETA5, 18, None),
            ('M3a (3 hubs, 5 branches)', 3, M3A, 13, None),
            ('M3b (3 hubs, 6 branches)', 3, M3B, 19, None),
            ('K4', 4, outer.K4E, 10, None),
            ('K4+par', 4, outer.K4PARE, 12, None),
            ('K4+2par (8 branches)', 4, K4_2PAR, 8, 60)]
    for tag, n, E0, lmax, cap in fams:
        m = len(E0)
        bound = 6 * (m - n + 1) - m - 1
        sh, tried, capped = outer.shapes_from(tag, n, E0, lmax, cap=cap)
        exh = ('CAPPED at %d, lmax = %d' % (cap, lmax) if capped else
               ('EXHAUSTIVE: lmax = %d >= the arithmetic bound %d'
                % (lmax, bound) if lmax >= bound else
                'BOUNDED at lmax = %d (arithmetic bound %d)' % (lmax, bound)))
        out.append((f'{tag} ({exh}; {tried} tuples)', sh))
    for nn, lm, cap in ((5, lmax5, cap5), (6, lmax6, cap6)):
        for n, E0 in [(n, E) for (n, E) in candidate_graphs(nn) if n == nn]:
            if nn == 6 and len(E0) > e6max:
                continue                        # a measured cost boundary
            sh, tried, capped = outer.shapes_from(f'V{nn}e{len(E0)}', n, E0,
                                                 lm, cap=cap)
            out.append((f'|V*| = {nn}, |E*| = {len(E0)} '
                        f'({"CAPPED at " + str(cap) if capped else "EXHAUSTIVE"}'
                        f' at lmax = {lm}; {tried} tuples)', sh))
    return out


def wide():
    print("== (OC-10): the widened combinatorial sweep, and the proof it "
          "corroborates ==")
    print("   POOL-CW: outer.named_inventory() plus wide_shapes().  No rng.")
    print("   Step O9 proves the map is FORCED for every tight isostatic G, "
          "so a hit is")
    print("   impossible and this sweep can only widen the measured base.  "
          "Every pair")
    print("   carries the proof's own steps as asserts (girth-6 consequences, "
          "the")
    print("   pigeonhole step, the tightness identity) and the census part 2 "
          "needs.\n")
    hist, chi_h, cens = {}, {}, {}
    ell_h, deg_h, hubfree_h, pat_h = {}, {}, {}, {}
    npairs, nshapes, ngirth = 0, 0, 0
    fams = [('named', outer.named_inventory())] + \
           [(desc, sh) for desc, sh in wide_shapes()]
    for fname, fam in fams:
        n = 0
        for label, E in fam:
            for v in outer.eligible_splits(E):
                sd = outer.split_data(E, v)
                if sd is None:
                    continue
                a, b, c, Gp, Hed = sd
                for P in outer.companions4(Hed, b, c):
                    cert = oc10_certificate(E, v, P)
                    d = OL.comb_data(Hed, P)
                    k = d[:6]
                    hist[k] = hist.get(k, 0) + 1
                    chi_h[d[6:]] = chi_h.get(d[6:], 0) + 1
                    ell_h[cert['ell']] = ell_h.get(cert['ell'], 0) + 1
                    deg_h[cert['degG']] = deg_h.get(cert['degG'], 0) + 1
                    hubfree_h[cert['hubfree']] = \
                        hubfree_h.get(cert['hubfree'], 0) + 1
                    pat_h[cert['pat']] = pat_h.get(cert['pat'], 0) + 1
                    cens[(cert['degG'][0] == 3, cert['hubfree'][0])] = \
                        cens.get((cert['degG'][0] == 3,
                                  cert['hubfree'][0]), 0) + 1
                    n += 1
                    npairs += 1
                    if npairs <= 250:            # girth on a subsample
                        g = girth(E)
                        assert g >= 6, f"{label}: girth {g} < 6"
                        ngirth += 1
        nshapes += len(fam)
        print(f"   {fname:56s}: {len(fam):4d} class shapes, {n:5d} pairs")
    print(f"\n   POOL-CW: {npairs} (split, companion) pairs over {nshapes} "
          f"class shapes")
    print(f"   (mu_1, dim R_1, A_1, mu_4, dim R_4, A_4) histogram:")
    for k in sorted(hist):
        print(f"       {k} : {hist[k]}")
    print(f"   (chi, def(H/X), def(H/Y)) histogram: {dict(sorted(chi_h.items()))}")
    assert all(k == (1, 5, 0, 1, 5, 0) for k in hist), \
        f"the availability map is not uniform: {sorted(hist)}"
    assert all(k == (0, 0, 0) for k in chi_h), f"chi or def moved: {chi_h}"
    print(f"   girth >= 6 asserted on the first {ngirth} pairs' shapes "
          f"(the rest carry the\n     two LOCAL consequences instead -- "
          f"chi = 0 and the pigeonhole step -- which\n     is what the proof "
          f"actually uses)")
    print(f"\n   HITS for *What would change this* item 1 (dim R = 6): 0 of "
          f"{npairs}")
    print(f"   HITS for item 2 (dim R <= 4 or mu >= 2):          0 of "
          f"{npairs}")
    print(f"   -- and by (OC-10) that rate is not a measurement but a "
          f"THEOREM: both are\n      unrealizable at any tight isostatic "
          f"shape, so no further widening can hit.")
    print(f"\n   THE CENSUS part 2 needs (this is what the widening actually "
          f"buys):")
    print(f"     (deg_G(b), deg_G(c)) histogram: "
          f"{dict(sorted(deg_h.items()))}")
    print(f"     (ell_min at b, at c) histogram: "
          f"{dict(sorted(ell_h.items()))}")
    print(f"     (b has no hub G'-neighbour, c has none) histogram: "
          f"{dict(sorted(hubfree_h.items()))}")
    print(f"     companion hub pattern (x1,x2,x3) histogram: "
          f"{dict(sorted(pat_h.items()))}")
    n3 = sum(cnt for (d3, hf), cnt in cens.items() if d3)
    n3f = sum(cnt for (d3, hf), cnt in cens.items() if d3 and hf)
    print(f"     (OC-12) applies at the b-end (deg_G(b) = 3) at {n3} of "
          f"{npairs} pairs;")
    print(f"     (OC-13)'s hub slide is legal there too at {n3f} of "
          f"{npairs}.")
    print(f"\n   COVERAGE BOUNDARY, stated as a boundary and not a theorem: "
          f"theta_m for m >= 4\n     yields ZERO class shapes at ANY lengths "
          f"(exhaustive above, and the reason is\n     arithmetic -- see the "
          f"workbook Step O9 remark), the |V*| = 5 families are\n     capped, "
          f"and |V*| = 6 is reached only at |E*| <= 10: one |E*| = 11 hub "
          f"graph\n     costs 137 s at cap 8, a measured cost, not a claim "
          f"about those shapes.")
    print(f"\nWIDE OK: {npairs} pairs, all (1, 5, 0) on both sides, "
          f"chi = 0 throughout.")


# =================== (OC-10)'s minimality ((OC-10-min)) =====================

def rigid_proper_closed(edges):
    """Every PROPER vertex subset whose induced subgraph has minimum degree
    `>= 2`, at least 3 vertices, and `def = 0` -- i.e. a rigid proper subgraph
    that is its own 2-core.  Step O9's case `b notin W` produces exactly such a
    subgraph, and in a subdivision every one of them is a union of COMPLETE
    hub-to-hub branches (a `G`-degree-2 vertex inside it has both its edges
    inside it, so the branch propagates to its hub ends), which is what
    `kslide.no_rigid_branch_union` -- the class predicate's `hnoRigid` -- rules
    out.  Enumerated by brute force; these graphs are tiny."""
    V = sorted(verts_of(edges), key=str)
    out = []
    for r in range(3, len(V)):
        for S in itertools.combinations(V, r):
            Ss = set(S)
            sub = [e for e in edges if e[0] in Ss and e[1] in Ss]
            if len(sub) < 3:
                continue
            dg = {}
            for u, w in sub:
                dg[u] = dg.get(u, 0) + 1
                dg[w] = dg.get(w, 0) + 1
            if len(dg) != r or min(dg.values()) < 2:
                continue
            if deficiency(sub, sorted(Ss, key=str)) == 0:
                out.append(tuple(sorted(Ss, key=str)))
    return out


def oc10_hypotheses(Hed, P, chi, pig, g):
    """Which of (OC-10)'s hypotheses does this hand-built `H` break?  The
    split path `b - v - a - c` is added back, since three of the hypotheses are
    about `G`, not `H`."""
    b, c = P[0], P[4]
    G = list(Hed) + [(b, '_v'), ('_v', '_a'), ('_a', c)]
    nb = neighbors(G)
    nV, nE = len(verts_of(G)), len(G)
    tight = (5 * nE == 6 * (nV - 1))
    return [t for t, ok in (
        ('count(H) = 3',
         6 * (len(verts_of(Hed)) - 1) - 5 * len(Hed) == 3),
        ('G tight', tight),
        ('def(G) = 0', deficiency(G) == 0),
        ('b, c hubs', len(nb[b]) >= 3 and len(nb[c]) >= 3),
        ('hnoRigid (no rigid proper branch-union)',
         not rigid_proper_closed(G)),
        ('girth(H) >= 6', g >= 6),
        ('chi = 0', chi == 0),
        ('no 2-into-weld vertex', not pig)) if not ok]


def adv_case(name, Hed, P, why):
    """One adversarial NON-class graph: `comb_data` on a hand-built `H` whose
    companion violates one hypothesis of (OC-10).  Reports the hit."""
    d = OL.comb_data(Hed, P)
    mu1, R1, A1, mu4, R4, A4, chi, dX, dY = d
    X, Y = companion_sets(P)
    g = girth(Hed)
    cnt = 6 * (len(verts_of(Hed)) - 1) - 5 * len(Hed)
    pig = bool(two_into_weld(Hed, X)) or bool(two_into_weld(Hed, Y))
    hit = (R1 >= 6 or R4 >= 6, R1 <= 4 or R4 <= 4 or mu1 >= 2 or mu4 >= 2)
    # which of (OC-10)'s hypotheses does this graph break?
    broken = oc10_hypotheses(Hed, P, chi, pig, g)
    print(f"   {name:26s} count(H) = {cnt:3d}  girth(H) = {g}  chi = {chi}  "
          f"(mu, dim R, A) = ({mu1}, {R1}, {A1} | {mu4}, {R4}, {A4})  "
          f"def(H/X) = {dX}")
    print(f"       {why}")
    print(f"       broken hypotheses of (OC-10): {broken}")
    print(f"       -> item-1 hit (dim R = 6): {hit[0]}   "
          f"item-2 hit (dim R <= 4 or mu >= 2): {hit[1]}")
    return d, g, hit, broken


def adv():
    print("== (OC-10) MINIMALITY: drop the class hypothesis and the hit "
          "appears ==")
    print("   POOL-A: six hand-built graphs, no rng.  Each violates ONE step "
          "of Step O9")
    print("   and exhibits exactly the hit that (OC-10) forbids inside the "
          "class, so the")
    print("   0-rate of --wide is attributable to the hypothesis and not to "
          "the search")
    print("   being too narrow.  These are NOT class shapes and no figure "
          "here is a")
    print("   class figure.\n")
    P = ['b', 'x1', 'x2', 'x3', 'c']
    path = [('b', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'c')]
    rows = []
    # 1. the chord `b x3` (a 4-cycle: girth 4 < 6)
    rows.append(adv_case(
        'chord b-x3', path + [('b', 'x3'), ('c', 'q'), ('q', 'b')], P,
        "chord b-x3 closes a 4-cycle; girth >= 6 forbids it in the class"))
    # 2. the chord `b c` (a 5-cycle)
    rows.append(adv_case(
        'chord b-c', path + [('b', 'c')], P,
        "chord b-c closes a 5-cycle; girth >= 6 forbids it in the class"))
    # 3. a vertex with two X-neighbours (the pigeonhole configuration)
    rows.append(adv_case(
        'u adj x1 and c', path + [('u', 'x1'), ('u', 'c')], P,
        "u has two X-neighbours: H/X gets a 2-cycle at v*, so H/X is "
        "DEPENDENT"))
    # 4. the 6-cycle through the whole X-path, disjoint from b
    rows.append(adv_case(
        '6-cycle thru X-path', path + [('c', 'u'), ('u', 'w'), ('w', 'x1')], P,
        "a 6-cycle containing x1-x2-x3-c contracts to a TRIANGLE on "
        "{u, w, v*}"))
    # 5. b free: no second b-X route at all (H not 2-connected at b)
    rows.append(adv_case(
        'b a pendant', path, P,
        "b attached only by e_1: deleting it frees b completely, dim R = 6"))
    # 6. two b-X edges through a long detour (mu = 2 without a short cycle
    #    inside the companion, which the girth bound still forbids in class)
    rows.append(adv_case(
        'mu = 2 via b-c edge', path + [('b', 'c'), ('b', 'u'), ('u', 'w'),
                                       ('w', 'z'), ('z', 'c')], P,
        "the b-c edge is a second b-X edge, so mu_1 = 2 and the first "
        "disjunct is FORCED"))
    # 7. THE CASE THAT CAUGHT A GAP IN STEP O9's FIRST DRAFT.  An 8-cycle
    #    through the whole X-path: count(H) = 3, girth 8, chi = 0, and NO
    #    vertex with two X-neighbours -- so it satisfies every LOCAL hypothesis
    #    the first draft of the proof used -- yet H/X contracts to a 5-cycle
    #    (count -1) and dim R_1 = 6.  What it breaks is the GLOBAL hypothesis:
    #    the subgraph it produces is a rigid proper branch-union, which
    #    `hnoRigid` forbids (and here `b` is not even a hub).  This row is the
    #    F11 test that the repaired hypothesis list is the right one.
    rows.append(adv_case(
        '8-cycle thru X-path', path + [('x1', 'w1'), ('w1', 'w2'),
                                       ('w2', 'w3'), ('w3', 'w4'),
                                       ('w4', 'c')], P,
        "count(H) = 3, girth 8, chi = 0, no 2-into-weld vertex -- every LOCAL "
        "hypothesis holds; H/X is a 5-cycle plus a pendant, count -1"))
    # 8. the same 8-cycle, but with `b` made a genuine HUB by a length-6
    #    detour that keeps count(H) = 3.  Now the ONLY broken hypothesis is
    #    `hnoRigid`: the 8-cycle together with `b x_1` and the split path is a
    #    rigid PROPER branch-union.  This is the row that makes `hnoRigid`
    #    demonstrably load-bearing rather than merely invoked.
    rows.append(adv_case(
        '8-cycle, b a real hub', path + [('x1', 'w1'), ('w1', 'w2'),
                                         ('w2', 'w3'), ('w3', 'w4'),
                                         ('w4', 'c'), ('b', 'z1'),
                                         ('z1', 'z2'), ('z2', 'z3'),
                                         ('z3', 'z4'), ('z4', 'z5'),
                                         ('z5', 'w2')], P,
        "b and c are hubs, G tight and isostatic, girth >= 6, chi = 0, no "
        "2-into-weld -- and STILL dim R_1 = 6"))
    n1 = sum(1 for _d, _g, h, _b in rows if h[0])
    n2 = sum(1 for _d, _g, h, _b in rows if h[1])
    print(f"\n   item-1 hits (dim R = 6): {n1} of {len(rows)}; "
          f"item-2 hits: {n2} of {len(rows)}")
    assert n1 >= 1 and n2 >= 1, \
        "the adversarial pool exhibits NEITHER hit -- the minimality test is " \
        "vacuous, so (OC-10)'s hypothesis has not been shown load-bearing"
    for d, g, h, broken in rows:
        assert not (h[0] or h[1]) or broken, \
            "an adversarial graph satisfies EVERY (OC-10) hypothesis and " \
            "still hits -- THE PROOF IS WRONG"
    print(f"\nADV OK: every hit sits at a graph that breaks a NAMED "
          f"hypothesis of (OC-10)\n  (the broken list is printed per row and "
          f"asserted non-empty at every hit);\n  none satisfies them all.  "
          f"The hypotheses are therefore load-bearing and the\n  0-rate of "
          f"--wide is not vacuous.")


# =================== part 2: the hyperplane form ============================

def panel_line_space(placed, nrm, h):
    """`beta_h`, the 3-dimensional space of LINES of the panel `Pi(h)`, plus
    the three panel points it is built from.  Every nonzero element is
    decomposable (`Lambda^2` of a 3-space), so every element IS a line of
    `Pi(h)`, and the whole space is totally `B`-isotropic (four vectors in a
    3-space have determinant 0) -- both asserted."""
    bb = robust_plane_basis(nrm[h])
    assert bb is not None, "degenerate panel normal"
    b0, b1 = bb
    p0 = hat(placed[h])
    p1 = hat([placed[h][i] + b0[i] for i in range(3)])
    p2 = hat([placed[h][i] + b1[i] for i in range(3)])
    B = [wedge2(p0, p1), wedge2(p0, p2), wedge2(p1, p2)]
    assert rank(B) == 3, "beta_h is not 3-dimensional"
    for x in B:
        for y in B:
            assert klein(x, y) == 0, "beta_h is not totally B-isotropic"
    return B, (p0, p1, p2)


def line_of(B, pts, w):
    """The line of `Pi(h)` represented by `w in beta_h`, as the functional
    `f` with `{x : f . x = 0}` in the `(p0, p1, p2)` coordinates of the panel.
    `w = a p0^p1 + b p0^p2 + c p1^p2` is the kernel of `x -> det[x, u, v]`,
    which in those coordinates is `(c, -b, a)`."""
    co = coords_in(B, w)
    assert co is not None, "w escaped beta_h"
    return [co[2], -co[1], co[0]]


def pencil_centre(B, pts, W2):
    """The point of `Pi(h)` whose pencil is the 2-dimensional `W2 subseteq
    beta_h`: two distinct lines of a projective plane meet in one point.
    Returned in `K^4`; asserted to lie on both lines and in the panel."""
    assert len(W2) == 2 and rank(W2) == 2, "not a 2-dimensional meet"
    f1, f2 = line_of(B, pts, W2[0]), line_of(B, pts, W2[1])
    ker = nullspace([f1, f2])
    assert len(ker) == 1, f"two lines of a plane met in dim {len(ker)}"
    co = ker[0]
    p = [sum((co[j] * pts[j][i] for j in range(3)), F(0)) for i in range(4)]
    assert any(x != 0 for x in p), "degenerate pencil centre"
    for w in W2:
        assert klein_point_on(p, w), "the centre is not on the line"
    return p


def klein_point_on(p, w):
    """Is the point `p in K^4` on the line `w in Lambda^2 K^4`?  `p ^ w = 0`
    in `Lambda^3 K^4`, whose four components are the four `3x3` minors; with
    `w` decomposable this is exactly incidence."""
    # p ^ w, in the PL order of exactcore (indices (i,j) with i<j)
    from exactcore import PL
    tri = {}
    for (i, j), wij in zip(PL, w):
        for k in range(4):
            if k == i or k == j:
                continue
            key = tuple(sorted((i, j, k)))
            sgn = 1
            perm = [i, j, k]
            # sign of the permutation sorting (i,j,k)
            for x in range(3):
                for y in range(x + 1, 3):
                    if perm[x] > perm[y]:
                        sgn = -sgn
            tri[key] = tri.get(key, F(0)) + sgn * wij * p[k]
    return all(x == 0 for x in tri.values())


def collinear(p, q, r):
    return rank([p, q, r]) <= 2


def far_twist_space(Hed, placed, X, b, u, rep):
    """`T_u` = `{m(u) - m(v*)}` in `(H/X) - b`: delete the body `b` from `H`,
    weld `X`, and read the relative twist space of `(u, rep)` for any `rep in
    X`.  Independent of `pt(b)`, `pt(x_1)` and `pt(a)` BY CONSTRUCTION -- `b`
    is not a vertex of the system and `a` is not a vertex of `H` -- which is
    what makes (OC-13)'s hub slide legal."""
    ed = [e for e in Hed if b not in e]
    VH = sorted(verts_of(ed), key=str)
    assert u in VH and rep in VH, "the far system lost an endpoint"
    mot, idx = OL.weld_motions(ed, VH, placed, [sorted(X, key=str)])
    return OL.rel_span(mot, idx, u, rep)


def wrench_row(d, side):
    """(OC-11)/(OC-12)/(OC-13) at one frame and one companion end.  Returns a
    dict of the measured integers plus every assertion's verdict."""
    Hed, VH, placed, nrm, P = d['Hed'], d['VH'], d['placed'], d['nrm'], d['P']
    Gp, lam = d['Gp'], d['lam']
    if side == 'b':
        h, inner, W, ei = d['b'], P[1], set(P[1:]), 0
    else:
        h, inner, W, ei = d['c'], P[3], set(P[:4]), 3
    nbH, nbP = neighbors(Hed), neighbors(Gp)
    e = next(ee for ee in Hed if set(ee) == {h, inner})
    mot, idx = OL.weld_motions(Hed, VH, placed, [sorted(W, key=str)], drop=[e])
    R = OL.rel_span(mot, idx, h, inner)
    # (OC-10) makes this a theorem, not a measurement:
    assert len(R) == 5, f"dim R != 5 on the pencil chart: {len(R)}"
    B, pts = panel_line_space(placed, nrm, h)
    meet = LAM.span_meet(R, B)
    # dim(R cap beta) >= 5 + 3 - 6 = 2 ALWAYS:
    assert len(meet) >= 2, f"dim(R cap beta) = {len(meet)} < 2"
    Ci = wedge2(hat(placed[h]), hat(placed[inner]))
    lam_i0 = (lam[ei] == 0)
    row = {'dimR': len(R), 'dimMeet': len(meet), 'lam0': lam_i0,
           'degH': len(nbH[h]), 'degGp': len(nbP[h]),
           'hubfree': hub_free_end(Gp, h),
           'coinc': bool(hinge_coincidences(Gp, placed, h, inner))}
    if len(meet) == 2:
        p = pencil_centre(B, pts, meet)
        # (OC-11): lambda_i = 0 <=> the marked point is on C(h, inner)
        assert lam_i0 == collinear(p, hat(placed[h]), hat(placed[inner])), \
            "(OC-11) FAILED: lambda_i = 0 is not `p on C(h, x_i)`"
        row['p_is_h'] = (rank([p, hat(placed[h])]) == 1)
        # L_h subseteq R  <=>  p = pt(h)
        Lh, _dirs = OL.line_pencil(placed, nrm, h)
        sub = all(in_span(x, R) for x in Lh)
        assert sub == row['p_is_h'], \
            "(OC-11) FAILED: `L_h subseteq R` is not `p = pt(h)`"
        row['Lsub'] = sub
        others = sorted(set(nbH[h]) - {inner}, key=str)
        if len(others) == 1:
            u = others[0]
            Cu = wedge2(hat(placed[h]), hat(placed[u]))
            # (OC-12): at a degree-3 hub the other hinge IS a relative twist
            assert in_span(Cu, R), \
                "(OC-12) FAILED: C(h,u) is not a relative twist at a " \
                "degree-2 (in H) hub"
            assert klein_point_on(p, Cu), \
                "(OC-12) FAILED: the marked point is off C(h,u)"
            marked_is_other = (rank([Ci, Cu]) == 1)
            if not row['p_is_h']:
                assert lam_i0 == marked_is_other, \
                    "(OC-12) FAILED: lambda_i = 0 is not the coincident-hinge " \
                    "condition at a degree-3 hub"
            row['deg3'] = True
            row['marked_is_other'] = marked_is_other
            # (OC-13): the far 4-plane and its panel trace
            T = far_twist_space(Hed, placed, W, h, u, inner)
            assert len(T) == 4, f"dim T_u = {len(T)} != 4"
            assert not in_span(Cu, T), "C(h,u) in T_u: R would collapse"
            assert len(span_basis(T + [Cu])) == 5, "R != <C(h,u)> + T_u"
            for x in R:
                assert in_span(x, span_basis(T + [Cu])), "R exceeds the sum"
            C0 = LAM.span_meet(T, B)
            assert len(C0) == len(meet) - 1, \
                "dim(R cap beta) != 1 + dim(T_u cap beta)"
            row['dimT_beta'] = len(C0)
            if len(C0) == 1:
                row['ptb_on_C0'] = klein_point_on(hat(placed[h]), C0[0])
                assert row['ptb_on_C0'] == row['p_is_h'], \
                    "(OC-13) FAILED: `pt(h) in C_0` is not `p = pt(h)`"
        else:
            row['deg3'] = False
    else:
        row['p_is_h'] = True
        row['Lsub'] = True
        row['deg3'] = (len(set(nbH[h]) - {inner}) == 1)
    # (OC-11a): R is contained in the hinge-line span of EVERY `h`-to-`v*`
    # path of `K`, since each edge of a path contributes `m(u) - m(w) in
    # <C(u,w)>`.  Is it their INTERSECTION?  That would make R a bracket
    # object at every end, not only at the `ell_min = 5` ones -- which is what
    # the M2 leaf needs in order to generalize.
    ell, pathv = chain_to_weld(Hed, W, h, inner)
    paths = weld_paths(Hed, W, h, inner, maxlen=(ell or 0) + 3)
    row['npaths'] = len(paths)
    if paths:
        inter = None
        for pv in paths:
            Cs = [wedge2(hat(placed[pv[i]]), hat(placed[pv[i + 1]]))
                  for i in range(len(pv) - 1)]
            sp = span_basis(Cs)
            for x in R:
                assert in_span(x, sp), \
                    "(OC-11a) FAILED: R escapes a path's hinge-line span"
            inter = sp if inter is None else LAM.span_meet(inter, sp)
        row['dimPathMeet'] = len(inter)
        row['pathmeet_is_R'] = (len(inter) == len(R)
                                and all(in_span(x, R) for x in inter))
    # the chain form, when a length-5 route exists
    row['ell'] = ell
    if ell == 5:
        Cs = [wedge2(hat(placed[pathv[i]]), hat(placed[pathv[i + 1]]))
              for i in range(5)]
        assert rank(Cs) == 5, "the length-5 chain's hinge lines are dependent"
        assert len(span_basis(Cs + list(R))) == 5, \
            "R_1 is not the length-5 chain's hinge-line span"
        row['chain'] = True
    else:
        row['chain'] = False
    return row


POOL_W_SEEDS = range(200, 220)


def wrench():
    print("== (OC-11)/(OC-12)/(OC-13): the hyperplane form of (OC-8), "
          "measured ==")
    print(f"   POOL-W: the 4 lambda.habitat_specs habitats x placement seeds "
          f"{POOL_W_SEEDS.start}-{POOL_W_SEEDS.stop - 1},")
    print("   accepted exactly as outerline.frame_at accepts them.  The "
          "composite guard")
    print("   repin.star_generic is REPORTED, not applied: (OC-12) is a "
          "statement about it.")
    print("   rng: random.Random(seed) inside widened.place_pencil_general "
          "only.\n")
    tot, rej = 0, {}
    agg, deg3rows, chainrows = {}, 0, 0
    guard_rows, viol = {}, []
    dimT, ellh, pathrows = {}, {}, {}
    for name, E, v, cmp_ in LAM.HABITATS4:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        VH = sorted(verts_of(Hed), key=str)
        Ps = outer.companions4(Hed, b, c)
        P = Ps[0]
        nsub = 0
        for seed in POOL_W_SEEDS:
            d, why = OL.frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
            if d is None:
                rej[why] = rej.get(why, 0) + 1
                continue
            tot += 1
            nsub += 1
            for side in ('b', 'c'):
                r = wrench_row(d, side)
                key = (side, r['dimMeet'], r['lam0'], r['Lsub'],
                       r.get('deg3'), r.get('marked_is_other'), r['coinc'])
                agg[key] = agg.get(key, 0) + 1
                if r.get('deg3'):
                    deg3rows += 1
                    dimT[r.get('dimT_beta')] = dimT.get(r.get('dimT_beta'),
                                                        0) + 1
                if r['chain']:
                    chainrows += 1
                ellh[r['ell']] = ellh.get(r['ell'], 0) + 1
                pk = (r['npaths'], r.get('dimPathMeet'),
                      r.get('pathmeet_is_R'))
                pathrows[pk] = pathrows.get(pk, 0) + 1
                # THE HEADLINE SENTENCE, tested as itself: at a degree-3 hub,
                # the composite guard IMPLIES the outer coordinate is nonzero.
                if r.get('deg3') and d['generic']:
                    guard_rows[('accepted', r['lam0'])] = \
                        guard_rows.get(('accepted', r['lam0']), 0) + 1
                    if r['lam0']:
                        viol.append((name, seed, side))
                elif r.get('deg3'):
                    guard_rows[('rejected', r['lam0'])] = \
                        guard_rows.get(('rejected', r['lam0']), 0) + 1
        print(f"   {name:14s} {nsub:3d} frames")
    print(f"\n   POOL-W frames: {tot}   rejected: {rej}")
    print(f"   per (side, dim(R cap beta), lambda_i = 0, L subseteq R, "
          f"deg-3 hub, marked = other\n     hinge, coincident hinge) -> count:")
    for k in sorted(agg, key=str):
        print(f"       {k} : {agg[k]}")
    print(f"\n   deg-3-hub ends: {deg3rows} of {2 * tot}; "
          f"dim(T_u cap beta_h) histogram: {dict(sorted(dimT.items()))}")
    print(f"   ell_min histogram: {dict(sorted(ellh.items()))}; ends where "
          f"R IS the length-5\n     chain's hinge-line span: {chainrows}")
    print(f"\n   (OC-11a) R vs the INTERSECTION of every path's hinge-line "
          f"span (the form the\n     M2 leaf needs in order to reach "
          f"ell_min > 5).  (#paths, dim of the meet,\n     the meet EQUALS R) "
          f"-> count:")
    for k in sorted(pathrows, key=str):
        print(f"       {k} : {pathrows[k]}")
    print(f"     (containment R subseteq every path span is asserted per "
          f"path, not reported.)")
    print(f"\n   (OC-12) AS A SENTENCE ABOUT THE GUARD: at a degree-3 hub, "
          f"star_generic\n     accepting the frame implies lambda_i != 0.  "
          f"(guard, lambda_i = 0) -> count:")
    for k in sorted(guard_rows, key=str):
        print(f"       {k} : {guard_rows[k]}")
    assert not viol, \
        f"(OC-12) REFUTED: a guard-accepted degree-3-hub end with " \
        f"lambda_i = 0: {viol[:3]}"
    print(f"     violations: {len(viol)} -- the implication is asserted per "
          f"end, not merely\n     observed as a rate.")
    print(f"\nWRENCH OK.  dim R = 5 (a theorem by (OC-10)), "
          f"dim(R cap beta) >= 2 always,\n  and where it is 2 the meet is the "
          f"pencil of a single panel point p with\n  lambda_i = 0 <=> p on "
          f"C(h, x_i) and L_h subseteq R <=> p = pt(h).  At a degree-3\n  hub "
          f"the other hinge line is always a relative twist, p sits on it, "
          f"and\n  lambda_i = 0 is EXACTLY the coincident-hinge condition.")


# =================== (OC-13): the hub slide =================================

def slide_placement(placed, h, newpt):
    out = dict(placed)
    out[h] = list(newpt)
    return out


def panel_point(pts, co):
    """An AFFINE `Q^3` point of the panel from `K^4` coordinates in the
    `(p0,p1,p2)` basis; `None` when the combination is at infinity."""
    p = [sum((co[j] * pts[j][i] for j in range(3)), F(0)) for i in range(4)]
    if p[3] == 0:
        return None
    return [p[i] / p[3] for i in range(3)]


def slide_targets(B, pts, C0, placed, nrm, h, avoid):
    """Rational points of `Pi(h)`: several ON the line `C_0` and several OFF
    it, all distinct from the points in `avoid`.  Deterministic (a fixed
    coefficient ladder), no rng."""
    f = line_of(B, pts, C0)
    ker = nullspace([f])
    assert len(ker) == 2, f"C_0 is not a line of the panel ({len(ker)})"
    on, off = [], []
    for s, t in ((F(1), F(0)), (F(0), F(1)), (F(1), F(1)), (F(1), F(-1)),
                 (F(2), F(1)), (F(1), F(2)), (F(3), F(-2)), (F(1), F(3))):
        co = [s * ker[0][j] + t * ker[1][j] for j in range(3)]
        q = panel_point(pts, co)
        if q is not None and all(q != x for x in avoid):
            on.append(q)
    for s, t, r in ((F(1), F(0), F(1)), (F(0), F(1), F(1)), (F(1), F(1), F(1)),
                    (F(1), F(-1), F(2)), (F(2), F(1), F(1)),
                    (F(1), F(2), F(3))):
        co = [s * ker[0][j] + t * ker[1][j] for j in range(3)]
        # push off the line: add r times a vector with f . w != 0
        w = None
        for e in ([F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), F(0), F(1)]):
            if sum(f[j] * e[j] for j in range(3)) != 0:
                w = e
                break
        assert w is not None, "the line functional is zero"
        co = [co[j] + r * w[j] for j in range(3)]
        q = panel_point(pts, co)
        if q is not None and all(q != x for x in avoid):
            off.append(q)
    return on, off


def check_slid(E, v, P, a, b, c, Gp, Hed, VH, placed, nrm, side):
    """Everything a chart point must satisfy, re-checked at a MODIFIED
    placement: a valid pencil realization, target rank, `dim R_a = 1`,
    `dim V_bc = 3`, `rank{C_i} = 4`, the (Lambda-0) clause battery, all four
    `IsNondegPencilRealization` conjuncts, and `lambda`."""
    from pitch import H_motions_vbc
    for hh in sorted(neighbors(Gp), key=str):
        if len(neighbors(Gp)[hh]) < 3:
            continue
        for u in neighbors(Gp)[hh]:
            if dot(nrm[hh], [placed[u][i] - placed[hh][i]
                             for i in range(3)]) != 0:
                return None, 'panel broken'
    for (u, w) in Gp:
        if placed[u] == placed[w]:
            return None, 'coincident adjacent points'
    if any(r != 3 for r in star_span_ranks(Gp, placed).values()):
        return None, 'star-span guard'
    st = outer.stratum_at(E, Gp, placed, a, b)
    if st is None:
        return None, 'off target rank'
    if st[1] != 1:
        return None, f'dim R_a = {st[1]}'
    if outer.panel_frame(placed, nrm, b, c) is None:
        return None, 'panels parallel'
    Vbc, _n, _s = H_motions_vbc(E, v, a, b, c, placed)
    if len(Vbc) != 3:
        return None, f'dim V_bc = {len(Vbc)}'
    C = [wedge2(hat(placed[P[i]]), hat(placed[P[i + 1]])) for i in range(4)]
    if rank(C) != 4:
        return None, 'rank{C_i} < 4'
    Vco = [coords_in(C, x) for x in Vbc]
    if any(x is None for x in Vco) or rank(Vco) != 3:
        return None, 'V_bc coordinate rank'
    ns = nullspace(Vco)
    if len(ns) != 1:
        return None, 'lambda not a point'
    lam = ns[0]
    nbG = neighbors(Gp)
    pt = {h: placed[h] for h in nbG if len(nbG[h]) >= 3}
    fr = outer.build_frame(placed, pt, nrm, b, c, P, 0)
    M0, Md = fr['M']
    ts = [(placed[a][i] - M0[i]) / Md[i] for i in range(3) if Md[i] != 0]
    if any(t != ts[0] for t in ts):
        return None, 'pt(a) left the meet line'
    ok, info = nondeg_conjuncts(Gp, placed)
    d = {'seed': 0, 'placed': placed, 'nrm': nrm, 'fr': fr, 'C': C,
         'Vbc': Vbc, 'lam': lam, 'st': st, 'a': a, 'b': b, 'c': c,
         'Gp': Gp, 'Hed': Hed, 'VH': VH, 'P': P, 'E': E, 'v': v,
         'generic': star_generic(Gp, placed),
         'coinc': coincident_hinges(Gp, placed), 'nondeg': ok,
         'nondeg_why': (None if ok else info),
         't_a': ts[0]}
    cl, pplus, q = OL.clauses(d)
    d['clauses'] = cl
    d['lam0d'] = cl['d']
    d['allclauses'] = all(cl[k] for k in ('a', 'b', 'c', 'd', 'e', 'f',
                                          'g13', 'g14', 'g24'))
    return d, None


def escape_cert(d):
    """(Lambda-2)'s certificate at a constructed chart point: the whole
    (Lambda-0)+(Lambda-0f') battery, whether `lambda` is proportional to
    either bad point, `deg_t Q(z(t))` along the `a`-line, and which outer
    coordinates vanish.  This is the sentence that matters at a point where
    (OUT) goes silent: the ESCAPE may still hold there, and (OC-4) is the
    precedent."""
    cl, pplus, q = OL.clauses(d)
    lam = d['lam']
    return (all(cl[k] for k in ('a', 'b', 'c', 'd', 'e', 'f', 'g13', 'g14',
                                'g24')),
            rank([lam, pplus]) == 1, rank([lam, q]) == 1,
            LAM.poly_deg(LAM.qpoly(d['fr'], lam)),
            tuple(int(x == 0) for x in lam))


def slide():
    print("== (OC-13): the hub slide -- is `L_b subseteq R_1` REACHABLE at a "
          "class habitat? ==")
    print(f"   POOL-SL: the 4 habitats x seeds {POOL_W_SEEDS.start}-"
          f"{POOL_W_SEEDS.stop - 1}, restricted to ends where the")
    print("   hub has no hub G'-neighbour (so pt(h) may be moved anywhere "
          "inside its own")
    print("   panel with the panel and every other point held fixed).  Slide "
          "targets are a")
    print("   fixed deterministic coefficient ladder; no rng beyond the "
          "placement seed.\n")
    print("   THE EXPERIMENT.  T_u and beta_h do not see pt(h), so C_0 = "
          "T_u cap beta_h is")
    print("   FIXED under the slide.  Sliding pt(h) ONTO C_0 would produce an "
          "exact chart")
    print("   point with L_h subseteq R (hence lambda_i = 0 for EVERY "
          "placement of x_i) and")
    print("   NO coincident hinge at h; sliding it OFF must give "
          "lambda_i != 0.\n")
    landed_on, landed_off, rej_on = [], [], {}
    tried = 0
    for name, E, v, cmp_ in LAM.HABITATS4:
        a, b, c, Gp, Hed = outer.split_data(E, v)
        VH = sorted(verts_of(Hed), key=str)
        P = outer.companions4(Hed, b, c)[0]
        nb = neighbors(Gp)
        for seed in POOL_W_SEEDS:
            d, why = OL.frame_at(E, v, P, seed, a, b, c, Gp, Hed, VH)
            if d is None:
                continue
            placed, nrm = d['placed'], d['nrm']
            for side, h, inner, W, ei in (('b', b, P[1], set(P[1:]), 0),
                                          ('c', c, P[3], set(P[:4]), 3)):
                if not hub_free_end(Gp, h):
                    continue
                others = sorted(set(neighbors(Hed)[h]) - {inner}, key=str)
                if len(others) != 1:
                    continue
                u = others[0]
                T = far_twist_space(Hed, placed, W, h, u, inner)
                if len(T) != 4:
                    continue
                B, pts = panel_line_space(placed, nrm, h)
                C0 = LAM.span_meet(T, B)
                if len(C0) != 1:
                    print(f"   {name} seed {seed} side {side}: "
                          f"dim(T_u cap beta) = {len(C0)} -- L_h subseteq R "
                          f"ALREADY")
                    continue
                avoid = [placed[x] for x in nb[h]] + [placed[h]]
                on, off = slide_targets(B, pts, C0[0], placed, nrm, h, avoid)
                tried += 1
                for q in on:
                    pl2 = slide_placement(placed, h, q)
                    d2, why2 = check_slid(E, v, P, a, b, c, Gp, Hed, VH,
                                          pl2, nrm, side)
                    if d2 is None:
                        rej_on[why2] = rej_on.get(why2, 0) + 1
                        continue
                    r = wrench_row(d2, side)
                    landed_on.append((name, seed, side, r['lam0'], r['Lsub'],
                                      r['coinc'], d2['generic'], d2['nondeg'],
                                      r['dimMeet']) + escape_cert(d2))
                    break
                for q in off:
                    pl2 = slide_placement(placed, h, q)
                    d2, why2 = check_slid(E, v, P, a, b, c, Gp, Hed, VH,
                                          pl2, nrm, side)
                    if d2 is None:
                        continue
                    r = wrench_row(d2, side)
                    landed_off.append((name, seed, side, r['lam0'],
                                       r['Lsub'], r['coinc'],
                                       d2['generic'], r['dimMeet']))
                    break
    print(f"\n   (side-ends where the slide was attempted: {tried})")
    print(f"   SLID ONTO C_0 -- landed at {len(landed_on)} chart points; "
          f"rejections: {rej_on}")
    print(f"     row = (habitat, seed, side, lambda_i = 0, L_h subseteq R, "
          f"coincident hinge at h,\n            star_generic, all four "
          f"nondeg conjuncts, dim(R cap beta) | (Lambda-0)+(0f')\n            "
          f"green, lambda ~ p+, lambda ~ q, deg_t Q(z(t)), "
          f"(lambda_i = 0 mask))")
    for row in landed_on[:12]:
        print(f"       {row}")
    gtab = {}
    for row in landed_on:
        gtab[(row[5], row[6], row[7])] = gtab.get((row[5], row[6], row[7]),
                                                  0) + 1
    print(f"     (coincident hinge at h, star_generic, all four nondeg "
          f"conjuncts) -> count:")
    for k in sorted(gtab, key=str):
        print(f"       {k} : {gtab[k]}")
    escrows = {}
    for row in landed_on:
        escrows[row[9:]] = escrows.get(row[9:], 0) + 1
    print(f"     the escape certificate at the slid points, aggregated:")
    for k in sorted(escrows, key=str):
        print(f"       {k} : {escrows[k]}")
    if landed_on:
        assert not any(row[10] or row[11] for row in landed_on), \
            "lambda is proportional to p+ or q at a slid point -- that is a " \
            "genuine (T3) escape failure at a nondegenerate hard-stratum " \
            "point and must be reported as the headline"
        assert all(row[12] >= 0 for row in landed_on), \
            "Q(z(t)) == 0 at a slid point"
    print(f"   SLID OFF C_0 -- landed at {len(landed_off)} chart points")
    for row in landed_off[:6]:
        print(f"       {row}")
    if landed_on:
        assert all(r[3] and r[4] for r in landed_on), \
            "a point slid ONTO C_0 does not have lambda_i = 0 with " \
            "L_h subseteq R -- (OC-13) is WRONG"
        clean = [r for r in landed_on if not r[5]]
        print(f"\n   VERDICT: `L_h subseteq R` IS REACHABLE at a class "
              f"habitat -- {len(landed_on)} exact\n     chart points, of "
              f"which {len(clean)} carry NO coincident hinge at the hub.  "
              f"So (OC-8)'s\n     bad case is not vacuous, and (OC-7)'s "
              f"coincidence implication is a fact\n     about POOL-G, not a "
              f"theorem beyond degree-3 hubs off C_0.")
    else:
        print(f"\n   VERDICT: no slide onto C_0 survives the chart "
              f"conditions ({rej_on}), so at\n     these habitats "
              f"`L_h subseteq R` is NOT reachable by the hub slide -- "
              f"evidence\n     FOR (OC-8), with the obstruction named by the "
              f"rejection reasons above.")
    assert all(not r[3] and not r[4] for r in landed_off), \
        "a point slid OFF C_0 still has lambda_i = 0 -- (OC-13) is WRONG"
    print(f"\nSLIDE OK: every point slid OFF C_0 has lambda_i != 0 "
          f"(asserted), which is\n  (OC-13)'s positive half: the bad locus of "
          f"pt(h) inside the panel is exactly\n  the line C_0.")


def main():
    if '--wide' in sys.argv:
        wide()
    elif '--adv' in sys.argv:
        adv()
    elif '--wrench' in sys.argv:
        wrench()
    elif '--slide' in sys.argv:
        slide()
    else:
        print(__doc__)
        sys.exit(2)


if __name__ == '__main__':
    main()
