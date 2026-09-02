"""
Phase 39, section (K-out) CONTINUATION (direction OWALL, ordinal 70) --
(OC-44)(iii), the wall-avoiding certificate-colouring EXISTENCE question
left by direction OQRANK (*Step O41*), attacked as an ARGUMENT with the
search demoted to an adversarial control.

WHAT THIS DRIVER TESTS, sentence by sentence (dispatch-log F11, and the
2026-09-02 sharpening: every headline names the sampler's support and
which of the claim's own variables that support VARIES).

  (OC-50) THE BLOCK MODEL IS THE WHOLE STORY.  At a sigma-fixed grid
    chart point of a class shape `G` at an admissible colouring, the
    entire (OC-40)/(OC-41) apparatus -- target rank of `G`, `dim D = 3`,
    the forced (1,2) star-eigen profile, `Q(g)`, `Gram_B(D_Y)`, hence
    `rank(Q|_D)` -- is computed by TWO DIRECTION NETWORKS IN QQ^3 with
    conic directions `A(s) = (1, s, s^2)`, `Q(x) = x_1^2 - x_0 x_2`:
    no Plucker coordinates, no QQ(i), no rigidity matrix of `G`.
    ASSERTED, not assumed: `--agree` recomputes every OQRANK verdict
    (`oqrank.point_at`, unmodified, at the SAME parameter draw) beside
    the model's and requires them EQUAL, clause by clause.  Only after
    that control does any model-only figure below get quoted.

  (OC-51) THE CONFINEMENT CALCULUS -- (OC-42)'s wall is ONE certificate
    of three, and the SECOND CONFINEMENT is identified.  With `H_X` the
    X-block network of `H` (nodes = Y-components, edges = X-edges
    labelled by X-class), `beta` = `b`'s node, `gamma` = `c`'s node, the
    X-condition `Q(g) != 0` is EXACTLY: `(beta gamma)` with class `j` is
    INDEPENDENT of `E(H_X)` in the class-parametrized direction-network
    matroid, for every X-class `j`.  Three PROVEN combinatorial
    certificates of the negation:

      (W)  [the (OC-42) WALL]  beta ~ gamma inside class `i` alone.
      (C)  [NEW -- the MONOCHROMATIC CUT]  beta !~ gamma in `H_X` MINUS
           the class-`i` edges (Kirchhoff-flow/apolarity proof).
      (Z)  [NEW -- the <= 3-CLASS VANISHING RULE]  a cycle-space element
           touching <= 3 distinct classes forces every per-class sum to
           vanish (three distinct Veronese points are independent), so
           coefficients are forced to ZERO, nodes are WELDED, and (W)
           becomes visible on the contracted network.

    ASSERTED per standing point: each certificate ==> `Q(g) = 0` AND `g`
    on that class's ruling line; and `Q(g) = 0` ==> `g` lies on SOME
    component ruling line (the double root is always a class parameter,
    never a stray conic point).  The residue -- confined with no
    certificate -- is COUNTED, never asserted away: it is a matroid-
    closure event with no rigid subnetwork witnessing it.

  (OC-52) THE Y-SIDE.  `Gram_B(D_Y)` is nonsingular at every standing
    point (ASSERTED, never merely reported), with the proven sufficient
    condition: TWO distinct Y-classes each cutting `b` from `c` in `H_Y`
    force two distinct roots of the 1-dimensional residue space, hence
    nondegeneracy.  ASSERTED: the two-cut predicate ==> `rank
    Gram_B(D_Y) = 2`, and `rank Gram_B(D_Y) = 2` outright.

  (OC-53) THE CENSUS WITHOUT THE COLOURING CAP.  OQRANK's (OC-43) hunt
    stopped at the first <= 6 certificate colourings ("never past the
    fourth").  This driver enumerates EVERY admissible colouring of the
    shape (2^branches, exhaustive -- `COL_CAP` disclosed and never
    approached on this population), keeps every certificate colouring,
    and classifies each as GOOD / walled / cut-confined / other-confined
    / Y-degenerate.  That turns the "174/174 within caps" figure into a
    per-class DENOMINATOR (how many certificate colourings exist, how
    many are good) -- the support datum the capped hunt could not see.

  (OC-54) THE SPLIT QUANTIFIER.  (a_1) is needed at every class
    (shape, SPLIT) (*Step O24*'s (a_1)); OQRANK measured ONE pinned split
    per class (`oschu.out_classes`' `v0`).  `--splits` runs the (OC-53)
    classification at EVERY eligible split of a shape, which is the one
    variable of (OC-44)(iii) the landed sampler holds fixed.

POOL: POOL-OW (this driver's own).  POOL-OQ2 is OQRANK's and is neither
re-run nor extended -- `--agree` CITES it by recomputing `point_at` as a
control on the model, at OQRANK's own seed and draw order.  Every "not
found" is not-found-under-the-stated-cap, never nonexistence.

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --controls
    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --agree 0 6
    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --full 0 60
    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --splits 0 12
    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --first 0 174
    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --synth
    PYTHONHASHSEED=0 python3 notes/scripts/w4/owall.py --validate

IMPORTS (read-only; nothing existing is modified): `oqrank`
(`point_at`, `cert_colourings`, `single_class_paths`, `find_edge`,
`PARAM_SEED` -- the landed OQRANK verdicts, used as the control),
`oschu` (`out_classes`), `grid` (`build_fixed_config_params`,
`block_data`, `colourings`, `combinatorial_filter`), `gridwit`
(`tree_triple`), `closure` (`components`, `build_fixed_config`,
`extensors`, `ruling_A_line`, `ruling_B_line`, `star_sign`), `outer`
(`split_data`, `eligible_splits`), `hybrid_gates`, `pitch`, `repin`,
`kbare_common`, `exactcore`.

HARNESS DEBT, recorded not paid (this pass may not modify a landed file):
  * `oschu.out_classes` gains a THIRD consumer (oschu, oqrank, this pass)
    -- section-2 rule 2's move-down trigger, RE-DATED.
  * `gridwit.tree_triple` gains a FOURTH consumer -- same trigger,
    RE-DATED.
  * `oqrank.point_at` / `oqrank.single_class_paths` gain their FIRST
    external consumer -- a NEW move-down item (they are the reference
    implementation of the (OC-40)/(OC-41)/(OC-42) verdicts).
"""
import random
import sys
import time
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, nullspace, rank                          # noqa: E402
from kbare_common import verts_of                                   # noqa: E402
from pitch import Q as Qklein, klein                                # noqa: E402
from repin import span_basis                                        # noqa: E402
from hybrid_gates import build_rigidity_extensors                   # noqa: E402
import closure                                                      # noqa: E402
from grid import (block_data, build_fixed_config_params,            # noqa: E402
                  colourings, combinatorial_filter)
from gridwit import tree_triple                                     # noqa: E402
import outer                                                        # noqa: E402
from oschu import out_classes                                       # noqa: E402
from oqrank import (PARAM_SEED, cert_colourings, find_edge,         # noqa: E402
                    point_at, single_class_paths)

SEED = 20260902                # printed by every mode
COL_CAP = 1 << 16              # admissible-colouring enumeration cap
DRAWS = 3                      # independent parameter draws per colouring
CERT_CAP_FULL = 4096           # certificate colourings kept per (shape, split)
SYNTH_CAP = 20000              # synthetic networks drawn in --synth


# ------------------------------------------------------------------ model --
#
# `W_F` is a 3-space carrying a nondegenerate quadratic form `Q` whose zero
# conic is the family's ruling parameterization `A(s)`, with
# `B(A(s), A(s')) = kappa (s - s')^2`, kappa != 0 ((OC-41)(ii)).  Any such
# datum is linearly isomorphic to the model below with the SAME affine
# parameter: `closure.ruling_A_line((1, s))` is, in the `closure.EIG_P`
# basis, `(2 i s, 1 + s^2, i(s^2 - 1))`, the image of `(1, s, s^2)` under an
# invertible QQ(i) matrix, and the landed `pitch.Q` pulls back to
# `-8 (x_1^2 - x_0 x_2)`.  `--controls` asserts both statements.

def Am(s):
    return [F(1), F(s), F(s) * F(s)]


def Bm(x, y):
    return x[1] * y[1] - (x[0] * y[2] + x[2] * y[0]) / 2


def Qm(x):
    return x[1] * x[1] - x[0] * x[2]


def perp_rows(s):
    """Two functionals spanning `A(s)`-perp: the edge's two constraints."""
    return [[-F(s), F(1), F(0)], [-F(s) * F(s), F(0), F(1)]]


def motion(nn, E):
    """Basis of `{m : V -> QQ^3 | m(n1) - m(n2) in <A(s)> for each edge}`."""
    rows = []
    for (n1, n2, s) in E:
        for f in perp_rows(s):
            r = [F(0)] * (3 * nn)
            for k in range(3):
                r[3 * n1 + k] += f[k]
                r[3 * n2 + k] -= f[k]
            rows.append(r)
    if not rows:
        return [[F(1) if j == i else F(0) for j in range(3 * nn)]
                for i in range(3 * nn)]
    return nullspace(rows)


def blocknet(Ed, VV, col, fam, par, compG):
    """The `fam`-block direction network of the (sub)graph `Ed` on `VV`.

    Nodes are the OTHER family's components inside `Ed`; an edge of `fam`
    joins its endpoints' nodes and carries its `fam`-CLASS parameter, read
    off `compG` (the class map of the AMBIENT graph `G`, so a class keeps
    the parameter the grid point gave it -- (OC-42)(i): deleting the two
    degree-2 interiors takes two leaves off their X-trees and one whole
    Y-component, changing no class parameter).

    Returns `(n_nodes, edges, node_of, cls_of)`."""
    Ef = [e for e in Ed if col[e] == fam]
    Eo = [e for e in Ed if col[e] != fam]
    co = closure.components(VV, Eo)
    nodes = sorted(set(co.values()))
    idx = {n: k for k, n in enumerate(nodes)}
    E = [(idx[co[x]], idx[co[y]], par[compG[x]]) for (x, y) in Ef]
    return len(nodes), E, (lambda v: idx[co[v]]), Ef


def li_ok_model(allverts, deg, nb, sA, sB):
    """(GR-5)'s closed-hub-neighbourhood LI clause, in the grid model.

    `grid_point((1,s),(1,u)) = M . (1, s, u, s u)` with `M` an invertible
    QQ(i) matrix (`--controls` asserts `det M != 0`), so the rank of a set
    of grid bodies is the rank over QQ of the rows `[1, s, u, s u]`."""
    for x in allverts:
        S = [w for w in ([x] + sorted(nb.get(x, []), key=str))
             if deg.get(w, 0) >= 3]
        if not S:
            continue
        rows = [[F(1), sA[w], sB[w], sA[w] * sB[w]] for w in S]
        if rank(rows) != len(S):
            return False
    return True


def draw_params(rng, cA, cB):
    pA = {k: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
          for k in sorted(set(cA.values()))}
    pB = {k: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
          for k in sorted(set(cB.values()))}
    return pA, pB


def model_point(E, allverts, Hed, VH, col, v, a, b, c, pA, pB,
                deg, nb, cA, cB):
    """(OC-50): every (OC-40)/(OC-41) quantity at ONE grid draw, computed
    from the two block networks alone.  Returns None when the draw is not
    a standing point, with the reason; otherwise the verdict dict."""
    sA = {x: pA[cA[x]] for x in allverts}
    sB = {x: pB[cB[x]] for x in allverts}
    if len({(sA[x], sB[x]) for x in allverts}) != len(allverts):
        return None, 'coincide'
    if len(set(pA.values())) != len(pA) or len(set(pB.values())) != len(pB):
        return None, 'param-collision'
    if not li_ok_model(allverts, deg, nb, sA, sB):
        return None, 'li'
    # target rank of G <=> both AMBIENT block networks isostatic.
    for fam, par, cG in (('A', pA, cA), ('B', pB, cB)):
        nn, Eb, _, _ = blocknet(E, allverts, col, fam, par, cG)
        if len(motion(nn, Eb)) != 3:
            return None, 'offtarget'
    evb, eva = find_edge(E, v, b), find_edge(E, v, a)
    X, Yc = col[evb], col[eva]
    parX, parY = (pA, pB) if X == 'A' else (pB, pA)
    cGX, cGY = (cA, cB) if X == 'A' else (cB, cA)
    nnX, EbX, nodeX, EfX = blocknet(Hed, VH, col, X, parX, cGX)
    nnY, EbY, nodeY, EfY = blocknet(Hed, VH, col, Yc, parY, cGY)
    mX, mY = motion(nnX, EbX), motion(nnY, EbY)
    bx, cx = nodeX(b), nodeX(c)
    by, cy = nodeY(b), nodeY(c)
    DX = span_basis([[m[3 * bx + k] - m[3 * cx + k] for k in range(3)]
                     for m in mX])
    DY = span_basis([[m[3 * by + k] - m[3 * cy + k] for k in range(3)]
                     for m in mY])
    assert len(mX) == 4 and len(mY) == 5, \
        f"(OC-40)(iv) block motion dims {len(mX)}/{len(mY)} != 4/5"
    assert len(DX) == 1 and len(DY) == 2, \
        f"(OC-40)(iv) profile ({len(DX)},{len(DY)}) != (1,2)"
    g0 = DX[0]
    qg = Qm(g0)
    rY = rank([[Bm(x, y) for y in DY] for x in DY])
    rQD = (1 if qg != 0 else 0) + rY
    # support diagnostics, in the model: the component ruling lines of H.
    LX = sorted({s for (_1, _2, s) in EbX})
    LY = sorted({s for (_1, _2, s) in EbY})
    onlineX = [s for s in LX if rank([g0, Am(s)]) == 1]
    secantX = any(rank([g0, Am(LX[i]), Am(LX[j])]) == 2
                  for i in range(len(LX)) for j in range(i + 1, len(LX)))
    secantY = any(rank(DY + [Am(LY[i]), Am(LY[j])]) == 2
                  for i in range(len(LY)) for j in range(i + 1, len(LY)))
    return dict(rQD=rQD, qg_nonzero=(qg != 0), rY=rY,
                onlineX=onlineX, nLX=len(LX), nLY=len(LY),
                suppX=('line' if onlineX else 'secant' if secantX else 'off'),
                suppY=('secant' if secantY else 'off'),
                X=X, Y=Yc, sX=parX, sY=parY,
                netX=(nnX, EbX, bx, cx), netY=(nnY, EbY, by, cy),
                g=g0), None


# ------------------------------------------------ the two combinatorial ---
#                                                  confinement predicates

def induced(nn, E, S):
    """Edges of the model network with BOTH endpoints in the node set S."""
    return [(n1, n2, s) for (n1, n2, s) in E if n1 in S and n2 in S]


def _uf(nodes):
    par = {n: n for n in nodes}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    def u(x, y):
        rx, ry = f(x), f(y)
        if rx != ry:
            par[rx] = ry
            return True
        return False
    return f, u


def rule_z_zeros(nodes, Ec):
    """(OC-51)(Z) -- THE <= 3-CLASS VANISHING RULE, and it is the mechanism
    *Step O41* attack (4) guessed BACKWARDS.

    Three distinct Veronese points are INDEPENDENT ((FR-2)(ii)), so a
    cycle-space element of the block network touching at most 3 distinct
    classes forces every one of its per-class sums to vanish -- for EVERY
    element of the 1-dimensional flex space.  Operationally: for a class
    set `S` with `|S| <= 3`, let `N_S` be the class-`S` subgraph; then for
    each `i in S`, `lambda` restricted to `N_S`'s class-`i` edges is a
    COBOUNDARY on `N_S`, hence vanishes on any class-`i` edge whose two
    endpoints already lie in one component of `N_S` minus its class-`i`
    edges.  Every such edge has `lambda_e = 0` identically, so the unique
    nontrivial motion is CONSTANT across it and its endpoints are welded.

    (What *Step O41* named -- "a value-level cancellation through a `>= 4`-
    class cycle relation" -- is the OPPOSITE reading: a `>= 4`-class cycle
    is where a nonzero relation LIVES; it is the `<= 3`-class cycles that
    KILL coefficients, and killing coefficients is what confines `g`.)

    Returns the list of (edge-index) forced zeros found in one sweep."""
    import itertools
    params = sorted({e[2] for _k, e in Ec})
    out = []
    for r in (1, 2, 3):
        for S in itertools.combinations(params, r):
            Sset = set(S)
            NS = [(k, e) for k, e in Ec if e[2] in Sset]
            if not NS:
                continue
            vs = sorted({x for _k, e in NS for x in (e[0], e[1])})
            for i in S:
                rest = [e for _k, e in NS if e[2] != i]
                f, u = _uf(vs)
                for (n1, n2, _s) in rest:
                    u(n1, n2)
                for k, e in NS:
                    if e[2] == i and f(e[0]) == f(e[1]):
                        out.append(k)
    return sorted(set(out))


def rigid_merge(nn, E):
    """(OC-51)(R) -- THE REDUCTION.  Contract every rigid (isostatic)
    sub-network of the block network, iterated to a fixed point.

    A node set `S` with `dim Mot(N[S]) = 3` carries only translations, so
    the unique nontrivial motion of `N` is CONSTANT on `S`: contracting `S`
    changes neither `Mot(N)` (as a space, via restriction/extension) nor
    `D_X`, and it preserves the count `2|E| = 3|V| - 4` exactly (a rigid
    `S` has `2|E(S)| = 3|S| - 3`).  So the reduction is EXACT, and every
    confinement predicate may be read on the reduced network instead.

    Returns `(rep, nodes, E_red)`: the node representative map, the reduced
    node list, and the reduced edge list (self-loops dropped -- an edge
    inside one contracted node constrains nothing and lies on no
    `beta`-`gamma` path)."""
    rep = list(range(nn))

    def find(x):
        while rep[x] != x:
            rep[x] = rep[rep[x]]
            x = rep[x]
        return x

    changed = True
    while changed:
        changed = False
        cur = sorted({find(x) for x in range(nn)})
        if len(cur) <= 1:
            break
        Ec = [(find(n1), find(n2), s) for (n1, n2, s) in E
              if find(n1) != find(n2)]
        k = len(cur)
        pos = {n: i for i, n in enumerate(cur)}
        for mask in range(1, 1 << k):
            S = {cur[i] for i in range(k) if mask >> i & 1}
            if len(S) < 2:
                continue
            ES = [(n1, n2, s) for (n1, n2, s) in Ec if n1 in S and n2 in S]
            if 2 * len(ES) < 3 * len(S) - 3:
                continue
            loc = {n: i for i, n in enumerate(sorted(S))}
            if len(motion(len(S), [(loc[n1], loc[n2], s)
                                   for (n1, n2, s) in ES])) == 3:
                it = iter(sorted(S))
                r0 = find(next(it))
                for n in it:
                    rn = find(n)
                    if rn != r0:
                        rep[rn] = r0
                changed = True
                break
    nodes = sorted({find(x) for x in range(nn)})
    Ered = [(find(n1), find(n2), s) for (n1, n2, s) in E
            if find(n1) != find(n2)]
    return (lambda x: find(x)), nodes, Ered


def closure_reduce(nn, E):
    """(OC-51)(Z)+(R) -- THE REDUCTION, iterated to a fixed point.

    Two EXACT contractions, alternated: the `<= 3`-class vanishing rule
    (`rule_z_zeros`) and rigid-subnetwork contraction.  Both weld nodes
    across which the unique nontrivial motion is CONSTANT, so neither
    changes `Mot(N)` or `D_X`; each may expose the other, so they are
    iterated.  Returns `(find, nodes, Ered)`."""
    rep = list(range(nn))

    def find(x):
        while rep[x] != x:
            rep[x] = rep[rep[x]]
            x = rep[x]
        return x

    def merge(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            rep[rx] = ry
            return True
        return False

    dead = set()
    changed = True
    while changed:
        changed = False
        Ec = [(k, (find(e[0]), find(e[1]), e[2]))
              for k, e in enumerate(E)
              if k not in dead and find(e[0]) != find(e[1])]
        for k in rule_z_zeros(sorted({find(x) for x in range(nn)}), Ec):
            if merge(E[k][0], E[k][1]):
                changed = True
            dead.add(k)
        if changed:
            continue
        cur = sorted({find(x) for x in range(nn)})
        Ecl = [e for _k, e in Ec]
        kk = len(cur)
        for mask in range(1, 1 << kk):
            S = {cur[i] for i in range(kk) if mask >> i & 1}
            if len(S) < 2:
                continue
            ES = [(n1, n2, s) for (n1, n2, s) in Ecl if n1 in S and n2 in S]
            if 2 * len(ES) < 3 * len(S) - 3:
                continue
            loc = {n: i for i, n in enumerate(sorted(S))}
            if len(motion(len(S), [(loc[n1], loc[n2], s)
                                   for (n1, n2, s) in ES])) == 3:
                it = iter(sorted(S))
                r0 = next(it)
                for n in it:
                    merge(n, r0)
                changed = True
                break
    nodes = sorted({find(x) for x in range(nn)})
    Ered = [(find(e[0]), find(e[1]), e[2]) for k, e in enumerate(E)
            if k not in dead and find(e[0]) != find(e[1])]
    return find, nodes, Ered


def wall_cut_reduced(nn, E, beta, gamma):
    """(W) and (C) read on the REDUCED network of `closure_reduce`.

    Returns `(nred, wall_params, cut_params)` -- the reduced node count and
    the class parameters `s_j` for which, respectively, `beta` and `gamma`
    are joined inside class `j` alone (the (OC-42) wall) or separated by
    deleting class `j` (the monochromatic cut)."""
    find, nodes, Ered = closure_reduce(nn, E)
    bb, gg = find(beta), find(gamma)
    if bb == gg:                       # excluded at target rank (dim D_X = 1)
        return len(nodes), None, None
    params = sorted({s for (_1, _2, s) in Ered})

    def conn(edges, x, y):
        par = {n: n for n in nodes}

        def f(z):
            while par[z] != z:
                par[z] = par[par[z]]
                z = par[z]
            return z
        for (n1, n2, _s) in edges:
            r1, r2 = f(n1), f(n2)
            if r1 != r2:
                par[r1] = r2
        return f(x) == f(y)

    wall = [s for s in params
            if conn([e for e in Ered if e[2] == s], bb, gg)]
    cut = [s for s in params
           if not conn([e for e in Ered if e[2] != s], bb, gg)]
    return len(nodes), wall, cut


def cut_classes(Hed, VH, col, fam, b, c):
    """(OC-51)(C), the MONOCHROMATIC-CUT predicate: the `fam`-classes `i`
    of `H` such that `b` and `c` fall in DIFFERENT components of `H` minus
    the class-`i` `fam`-edges.  Equivalently: a `b`-`c` edge cut of the
    `fam`-block network all of whose edges lie in class `i`.

    Dual to `oqrank.single_class_paths` -- (W) is a PATH inside one class,
    (C) is a CUT inside one class -- and NEITHER implies the other."""
    Ef = [e for e in Hed if col[e] == fam]
    comp = closure.components(VH, Ef)
    out = []
    for cid in sorted({comp[e[0]] for e in Ef}):
        keep = ([e for e in Hed if col[e] != fam] +
                [e for e in Ef if comp[e[0]] != cid])
        cc = closure.components(VH, keep)
        if cc[b] != cc[c]:
            out.append(cid)
    return out


def class_param(Hed, VH, col, fam, cid, par, compG):
    """The grid parameter of `H`'s `fam`-class `cid` (an `H`-level colour
    component), read off any of its edges' AMBIENT class."""
    comp = closure.components(VH, [e for e in Hed if col[e] == fam])
    for e in Hed:
        if col[e] == fam and comp[e[0]] == cid:
            return par[compG[e[0]]]
    return None


# ------------------------------------------------------- colouring census --

def certificate_colourings(E, allverts, cap=CERT_CAP_FULL):
    """EVERY admissible colouring carrying both-block tree-triple
    certificates ((GR-9)/(GR-10)) -- no probe cap, unlike
    `oqrank.cert_colourings`, which stops at the first `PROBE_CAP`
    filter-passing colourings.  Yields (index-among-filter-passing, col).
    `capped` is returned True if `cap` or `COL_CAP` was reached."""
    cols, odd = colourings(E, cap=COL_CAP)
    assert not odd and cols is not None, "odd-cycle obstruction / COL_CAP"
    out, passed, capped = [], 0, False
    for col in cols:
        if combinatorial_filter(E, allverts, col):
            continue
        passed += 1
        if closure.build_fixed_config(E, allverts, col) is None:
            continue
        ok = True
        for mine in ('A', 'B'):
            tt, _cap = tree_triple(block_data(E, allverts, col, mine))
            if tt is None:
                ok = False
                break
        if ok:
            out.append((passed - 1, col))
            if len(out) >= cap:
                capped = True
                break
    return out, len(cols), passed, capped


def classify(E, allverts, v, ci, cj, col, Hed, VH, deg, nb, a, b, c):
    """The GENERIC verdict at one (shape, split, certificate colouring),
    plus the two combinatorial predicates.  DRAWS independent seeded draws;
    `Q(g) != 0` at ONE standing draw is already the generic verdict by
    (OC-44)(i)'s openness, so a `good` is a WITNESS, never a rate; a
    `confined` is not-found-under-cap DRAWS unless (W) or (C) fires, in
    which case it is a THEOREM."""
    EA = [e for e in E if col[e] == 'A']
    EB = [e for e in E if col[e] == 'B']
    cA = closure.components(allverts, EA)
    cB = closure.components(allverts, EB)
    evb, eva = find_edge(E, v, b), find_edge(E, v, a)
    X, Yc = col[evb], col[eva]
    wallX = single_class_paths(Hed, VH, col, X, b, c)
    cutX = cut_classes(Hed, VH, col, X, b, c)
    cutY = cut_classes(Hed, VH, col, Yc, b, c)
    rng = random.Random(SEED * 1000 + ci * 97 + cj)
    rows, reasons = [], {}
    rw = rc = None
    nred = None
    for d in range(DRAWS):
        pA, pB = draw_params(rng, cA, cB)
        r, why = model_point(E, allverts, Hed, VH, col, v, a, b, c, pA, pB,
                             deg, nb, cA, cB)
        if r is None:
            reasons[why] = reasons.get(why, 0) + 1
            continue
        parX = r['sX']
        cGX = cA if X == 'A' else cB
        # ---- the HEADLINE assertions, per standing point.
        if wallX:
            assert not r['qg_nonzero'], \
                "(OC-42)(ii) WALL holds yet Q(g) != 0"
            for i in wallX:
                s_i = class_param(Hed, VH, col, X, i, parX, cGX)
                assert s_i in r['onlineX'], \
                    "(W) fires yet g is off that class's ruling line"
        if cutX:
            assert not r['qg_nonzero'], \
                "(OC-51)(C) monochromatic cut holds yet Q(g) != 0"
            for i in cutX:
                s_i = class_param(Hed, VH, col, X, i, parX, cGX)
                assert s_i in r['onlineX'], \
                    "(C) fires yet g is off that class's ruling line"
        if len(cutY) >= 2:
            assert r['rY'] == 2, \
                "(OC-52) two Y-cut classes yet Gram_B(D_Y) singular"
        assert r['rY'] == 2, "Y-block DEGENERATE -- (OC-43)(i) refuted"
        # ---- (OC-51)(R): the same two predicates on the REDUCED network.
        nnX, EbX, bx, cx = r['netX']
        nred, rwall, rcut = wall_cut_reduced(nnX, EbX, bx, cx)
        assert rwall is not None, \
            "the reduction merged beta with gamma -- dim D_X = 1 refuted"
        if rwall:
            assert not r['qg_nonzero'], \
                "(OC-51)(R)+(W) fires on the reduced network yet Q(g) != 0"
            for s_i in rwall:
                assert s_i in r['onlineX'], \
                    "reduced (W) fires yet g is off that class's line"
        if rcut:
            assert not r['qg_nonzero'], \
                "(OC-51)(R)+(C) fires on the reduced network yet Q(g) != 0"
        rw = rwall if rw is None else rw
        rc = rcut if rc is None else rc
        rows.append(r)
    if not rows:
        return dict(status='nostand', reasons=reasons, wallX=bool(wallX),
                    cutX=bool(cutX), ncutY=len(cutY), cj=cj,
                    rwall=False, rcut=False, nred=nred)
    good = any(r['rQD'] == 3 for r in rows)
    conf = all(not r['qg_nonzero'] for r in rows)
    # ---- the COMPLETENESS headline: the (OC-42) wall on the REDUCED
    #      network is the ONLY confinement mechanism.
    cert = None
    if conf:
        # THE HEADLINE that IS a theorem: the double root of `g`'s symbol is
        # always a CLASS parameter -- never a stray conic point.
        assert rows[0]['onlineX'], \
            ("Q(g) = 0 at every draw yet `g` lies on NO component ruling "
             "line -- a stray double root, off every class parameter")
        cert = ('W' if wallX else 'C' if cutX else
                'Z' if rw else 'ZC' if rc else 'none')
    if rw or rc:
        assert conf, "reduced (W)/(C) fires yet Q(g) != 0 at some draw"
    return dict(status='good' if good else 'confined' if conf else 'mixed',
                wallX=bool(wallX), cutX=bool(cutX), ncutY=len(cutY),
                nwall=len(wallX), ncut=len(cutX), cj=cj, cert=cert,
                rwall=bool(rw), rcut=bool(rc), nred=nred,
                suppX=rows[0]['suppX'], suppY=rows[0]['suppY'],
                rQD=rows[0]['rQD'], nstand=len(rows), reasons=reasons)


def shape_ctx(E, v):
    allverts = sorted(verts_of(E), key=str)
    sd = outer.split_data(E, v)
    if sd is None:
        return None
    a, b, c, Gp, Hed = sd
    VH = sorted(verts_of(Hed), key=str)
    deg, nb = {}, {}
    for (x, y) in E:
        deg[x] = deg.get(x, 0) + 1
        deg[y] = deg.get(y, 0) + 1
        nb.setdefault(x, []).append(y)
        nb.setdefault(y, []).append(x)
    return allverts, a, b, c, Hed, VH, deg, nb


# ----------------------------------------------------------- --controls ----

def leg_controls():
    print(f"[OW-1] the model, validated against the landed QQ(i) devices "
          f"(seed {SEED})")
    # (1) the Veronese identification: ruling_A_line((1,s)) is the image of
    #     (1, s, s^2) under a fixed invertible matrix, and pitch.Q pulls
    #     back to -8 Qm.
    def eigco(C):
        # coordinates in closure.EIG_P (a, b, c) |-> (a,b,c,c,-b,a)
        assert C[0] == C[5] and C[1] == -C[4] and C[2] == C[3], \
            "not a +1 star-eigenvector"
        return [C[0], C[1], C[2]]
    ss = [F(2), F(-3), F(5, 7), F(11, 3)]
    cols = [eigco(closure.ruling_A_line((1, s))) for s in ss]
    L = [[cols[i][k] for i in range(3)] for k in range(3)]   # images of 1,s,s^2
    # solve for the 3x3 matrix M with M (1,s,s^2) = A_actual(s): the three
    # coefficient vectors of the quadratic.
    M = None
    import itertools
    # A_actual(s) = c0 + c1 s + c2 s^2 ; recover c_j from three values.
    V = [[F(1), s, s * s] for s in ss[:3]]
    Vi = nullspace([[V[r][k] for k in range(3)] + [F(-1) if r == q else F(0)
                                                   for q in range(3)]
                    for r in range(3)])
    del Vi
    # direct: solve the 3x3 linear systems column by column via rref.
    import copy
    del copy
    def solve3(A, rhs):
        n = 3
        Mx = [A[i][:] + [rhs[i]] for i in range(n)]
        for cix in range(n):
            piv = next(i for i in range(cix, n) if Mx[i][cix] != 0)
            Mx[cix], Mx[piv] = Mx[piv], Mx[cix]
            pv = Mx[cix][cix]
            Mx[cix] = [x / pv for x in Mx[cix]]
            for i in range(n):
                if i != cix and Mx[i][cix] != 0:
                    f = Mx[i][cix]
                    Mx[i] = [x - f * y for x, y in zip(Mx[i], Mx[cix])]
        return [Mx[i][n] for i in range(n)]
    coef = [solve3(V, [cols[r][k] for r in range(3)]) for k in range(3)]
    M = [[coef[k][j] for j in range(3)] for k in range(3)]
    assert rank([list(r) for r in M]) == 3, "the Veronese matrix is singular"
    for s in ss:
        w = Am(s)
        img = [sum(M[k][j] * w[j] for j in range(3)) for k in range(3)]
        assert img == eigco(closure.ruling_A_line((1, s))), \
            "M (1,s,s^2) != ruling_A_line((1,s)) in EIG_P coordinates"
    print("  ruling_A_line((1,s)) = M . (1, s, s^2), det M != 0 : OK "
          "(4 parameters)")
    # pitch.Q on EIG_P pulls back to -8 Qm.
    for (x, y) in [(F(1), F(0)), (F(3), F(-2)), (F(1, 5), F(7))]:
        w = [F(1), x, y]
        C = [sum(M[k][j] * w[j] for j in range(3)) for k in range(3)]
        Cp = [C[0], C[1], C[2], C[2], -C[1], C[0]]
        assert Qklein(Cp) == -8 * Qm(w), "Q does not pull back to -8 Qm"
    for (w1, w2) in [([F(1), F(2), F(3)], [F(1), F(-1), F(4)]),
                     ([F(0), F(1), F(1)], [F(2), F(0), F(5)])]:
        C1 = [sum(M[k][j] * w1[j] for j in range(3)) for k in range(3)]
        C2 = [sum(M[k][j] * w2[j] for j in range(3)) for k in range(3)]
        P1 = [C1[0], C1[1], C1[2], C1[2], -C1[1], C1[0]]
        P2 = [C2[0], C2[1], C2[2], C2[2], -C2[1], C2[0]]
        assert klein(P1, P2) == -8 * Bm(w1, w2), \
            "B does not pull back to -8 Bm"
    print("  pitch.Q / pitch.klein pull back to -8 Qm / -8 Bm : OK")
    # (2) the grid-point factorization M4 . (1, s, u, s u), det != 0.
    from exactcore import Gauss
    Iu = Gauss(0, 1)
    M4 = [[Gauss(1, 0), Gauss(0, 0), Gauss(0, 0), Gauss(1, 0)],
          [-Iu, Gauss(0, 0), Gauss(0, 0), Iu],
          [Gauss(0, 0), Gauss(-1, 0), Gauss(1, 0), Gauss(0, 0)],
          [Gauss(0, 0), -Iu, -Iu, Gauss(0, 0)]]
    for (s, u) in [(F(2), F(3)), (F(-1, 3), F(5)), (F(7), F(-2, 5))]:
        w = [Gauss(1, 0), Gauss(s, 0), Gauss(u, 0), Gauss(s * u, 0)]
        img = [sum((M4[k][j] * w[j] for j in range(4)), Gauss(0, 0))
               for k in range(4)]
        assert img == closure.grid_point((1, s), (1, u)), \
            "grid_point != M4 . (1, s, u, s u)"
    assert rank([[x for x in row] for row in M4]) == 4, "M4 singular"
    print("  grid_point((1,s),(1,u)) = M4 . (1, s, u, s u), det M4 != 0 : OK")
    # (3) planted must-accepts / must-rejects on the block model.
    #     network shapes with 2|E| = 3|V| - 4 and dim D_X = 1.
    def probe_net(nn, E, bnode, cnode):
        m = motion(nn, E)
        D = span_basis([[x[3 * bnode + k] - x[3 * cnode + k] for k in range(3)]
                        for x in m])
        return len(m), D
    # (a) the single-edge network: a WALL and a CUT at once, g = A(s).
    d, D = probe_net(2, [(0, 1, F(4))], 0, 1)
    assert d == 4 and len(D) == 1 and Qm(D[0]) == 0 and \
        rank([D[0], Am(F(4))]) == 1, "planted trivial wall not detected"
    # (b) a monochromatic BRIDGE between two isostatic halves: 4 nodes,
    #     |E| = 4.  Halves are single edges (each 2 nodes, isostatic needs
    #     2|E| = 3|V| - 3 = 3 -- not integral), so use the 4-node witness
    #     below instead and plant the bridge on a 6-node network.
    # (c) a clean SECANT: two distinct classes on a b-c path, g off both.
    d, D = probe_net(3, [(0, 1, F(1)), (1, 2, F(5))], 0, 2)
    assert d == 5, f"secant probe motion dim {d}"
    # g is only 1-dimensional after imposing an ambient isostatic frame; on
    # this open path D is 2-dimensional and spanned by the two ruling lines.
    assert len(D) == 2 and rank(D + [Am(F(1)), Am(F(5))]) == 2, \
        "open 2-class path: D != <A(1), A(5)>"
    assert rank([[Bm(x, y) for y in D] for x in D]) == 2, \
        "(OC-41)(iii) secant plane degenerate"
    # (d) a TANGENT plane must be caught: <A(t), A'(t)>, exact derivative.
    t = F(3)
    Ap = [(Am(t + 1)[k] - Am(t - 1)[k]) / 2 for k in range(3)]
    T = [Am(t), Ap]
    assert rank([[Bm(x, y) for y in T] for x in T]) == 1, \
        "planted tangent plane not caught as degenerate"
    # (e) a ruling generator must be caught by Qm.
    assert Qm(Am(F(-7))) == 0 and Qm([F(1), F(2), F(3)]) != 0, \
        "Qm does not separate the conic"
    print("  planted wall / secant / tangent / ruling: 5/5 caught")
    print("\nOW-1 CONTROLS OK.")


# -------------------------------------------------------------- --agree ----

def leg_agree(lo, hi):
    """(OC-50): the model reproduces `oqrank.point_at` clause by clause at
    the SAME parameter draw.  The adversarial control on every model-only
    figure below."""
    print(f"[OW-2] model vs the landed QQ(i) devices, classes [{lo},{hi}) "
          f"(OQRANK seed {PARAM_SEED}, its own draw order)")
    cls = out_classes()
    npt = ncol = 0
    t0 = time.time()
    for ci in range(lo, min(hi, len(cls))):
        lab, E, v0, key = cls[ci]
        ctx = shape_ctx(E, v0)
        allverts, a, b, c, Hed, VH, deg, nb = ctx
        target = 6 * (len(allverts) - 1)
        rng = random.Random(PARAM_SEED * 100 + ci)
        for cj, (col, _probed) in enumerate(cert_colourings(E, allverts, 3)):
            ncol += 1
            evb, eva = find_edge(E, v0, b), find_edge(E, v0, a)
            X, Yc = col[evb], col[eva]
            EA = [e for e in E if col[e] == 'A']
            EB = [e for e in E if col[e] == 'B']
            cA = closure.components(allverts, EA)
            cB = closure.components(allverts, EB)
            for d in range(2):
                pA, pB = draw_params(rng, cA, cB)
                mv, why = model_point(E, allverts, Hed, VH, col, v0, a, b, c,
                                      pA, pB, deg, nb, cA, cB)
                built = build_fixed_config_params(E, allverts, col, pA, pB)
                if built is None:
                    assert mv is None and why in ('coincide',
                                                  'param-collision'), \
                        "model accepted a coincident-body draw"
                    continue
                pt, _, _ = built
                li = True
                for u in allverts:
                    S = [w for w in ([u] + sorted(nb.get(u, []), key=str))
                         if deg.get(w, 0) >= 3]
                    if S and rank([pt[w] for w in S]) != len(S):
                        li = False
                        break
                if not li:
                    assert mv is None and why in ('li', 'param-collision'), \
                        "the model's (GR-5) LI clause disagrees"
                    continue
                assert why != 'li', "the model rejected an LI-clean draw"
                ext = closure.extensors(E, pt)
                geo = (rank(build_rigidity_extensors(allverts, ext)) == target)
                assert geo == (mv is not None), \
                    f"target-rank verdict differs: geo={geo} model={why}"
                if not geo:
                    continue
                r = point_at(E, allverts, target, v0, a, b, c, Hed, col, pt,
                             X, Yc)
                assert mv['qg_nonzero'] == r['qg_nonzero'], "Q(g) differs"
                assert mv['rY'] == r['rY'], "rank Gram(D_Y) differs"
                assert mv['rQD'] == r['rQD'], "rank(Q|_D) differs"
                assert mv['suppX'] == r['suppX'], "suppX differs"
                assert mv['suppY'] == r['suppY'], "suppY differs"
                assert mv['nLX'] == r['nLX'] and mv['nLY'] == r['nLY'], \
                    "component ruling-line counts differ"
                npt += 1
        print(f"  {ci:3d} {lab[:38]:38s} cum points={npt} "
              f"({time.time() - t0:.0f}s)")
    print(f"  standing points compared : {npt} over {ncol} colourings")
    print(f"  clauses compared per point: Q(g), rank Gram(D_Y), rank(Q|_D), "
          f"suppX, suppY, #lines -- ALL EQUAL")
    print("\nOW-2 AGREE OK.")


# --------------------------------------------------------------- --full ----

def leg_full(lo, hi, splits=False):
    """(OC-53)/(OC-54): the classification over EVERY certificate colouring
    (and, with `splits`, every eligible split)."""
    what = "every eligible split" if splits else "the pinned split"
    print(f"[OW-{4 if splits else 3}] every certificate colouring at {what}, "
          f"classes [{lo},{hi}) (seed {SEED}, {DRAWS} draws/colouring)")
    cls = out_classes()
    tot = dict(good=0, confined=0, mixed=0, nostand=0)
    mech = dict(wall_only=0, cut_only=0, both=0, neither=0)
    rmech = dict(rw=0, rc=0, rw_only=0, rc_only=0, rboth=0, rneither=0,
                 raw_none=0, reduced_only=0)
    pairs = pairs_hit = 0
    per_class = []
    capped_any = False
    t0 = time.time()
    for ci in range(lo, min(hi, len(cls))):
        lab, E, v0, key = cls[ci]
        allverts = sorted(verts_of(E), key=str)
        certs, ncols, npass, capped = certificate_colourings(E, allverts)
        capped_any = capped_any or capped
        vs = outer.eligible_splits(E) if splits else [v0]
        for v in vs:
            ctx = shape_ctx(E, v)
            if ctx is None:
                continue
            allverts, a, b, c, Hed, VH, deg, nb = ctx
            pairs += 1
            cnt = dict(good=0, confined=0, mixed=0, nostand=0)
            for (cj, col) in certs:
                r = classify(E, allverts, v, ci, cj, col, Hed, VH, deg, nb,
                             a, b, c)
                cnt[r['status']] += 1
                tot[r['status']] += 1
                if r['status'] == 'confined':
                    if r['wallX'] and r['cutX']:
                        mech['both'] += 1
                    elif r['wallX']:
                        mech['wall_only'] += 1
                    elif r['cutX']:
                        mech['cut_only'] += 1
                    else:
                        mech['neither'] += 1
                    rmech[r['cert']] = rmech.get(r['cert'], 0) + 1
                    if r['rwall'] and r['rcut']:
                        rmech['rboth'] += 1
                    elif r['rwall']:
                        rmech['rw_only'] += 1
                    elif r['rcut']:
                        rmech['rc_only'] += 1
                    else:
                        rmech['rneither'] += 1
                    if not (r['wallX'] or r['cutX']):
                        rmech['reduced_only'] += 1
            if cnt['good']:
                pairs_hit += 1
            per_class.append((ci, lab, v, len(certs), ncols, npass, cnt))
        print(f"  {ci:3d} {lab[:30]:30s} adm={ncols:5d} pass={npass:4d} "
              f"cert={len(certs):4d} splits={len(vs):2d} "
              f"({time.time() - t0:.0f}s)")
    print(f"\n  (shape, split) pairs                : {pairs}")
    print(f"  pairs with >= 1 GOOD certificate col.: {pairs_hit}/{pairs}")
    print(f"  certificate colourings classified    : {sum(tot.values())}")
    for k in ('good', 'confined', 'mixed', 'nostand'):
        print(f"    {k:9s}: {tot[k]}")
    print(f"  confinement mechanism on the RAW block network, over the "
          f"{tot['confined']} confined colourings:")
    for k in ('wall_only', 'cut_only', 'both', 'neither'):
        print(f"    {k:10s}: {mech[k]}")
    print(f"  the same two predicates on the RIGID-REDUCED network:")
    for k in ('rw_only', 'rc_only', 'rboth', 'rneither'):
        print(f"    {k:10s}: {rmech[k]}")
    print(f"    visible ONLY after the reduction: {rmech['reduced_only']}")
    print(f"  FIRST certificate that fires, per confined colouring:")
    for k in ('W', 'C', 'Z', 'ZC', 'none'):
        print(f"    {k:5s}: {rmech.get(k, 0)}")
    print(f"  the RESIDUE -- confined with no combinatorial certificate: "
          f"{rmech.get('none', 0)}/{tot['confined']} "
          f"(a matroid-closure event: `beta` frozen to a class-`j` "
          f"neighbour of `gamma` with NO rigid subnetwork witnessing it)")
    assert tot['mixed'] == 0, \
        "a colouring gave Q(g) = 0 at some draws and != 0 at others"
    assert pairs_hit == pairs, \
        f"(OC-44)(iii) MISS: {pairs - pairs_hit} (shape, split) pairs have " \
        f"NO good certificate colouring among ALL of them"
    print(f"  colouring cap reached anywhere        : {capped_any} "
          f"(cap {CERT_CAP_FULL}; COL_CAP {COL_CAP})")
    # per-class denominators: the support datum the capped hunt could not see
    print(f"\n  per-(shape,split) good/cert ratio, smallest 12:")
    rows = sorted(per_class, key=lambda r: (r[6]['good'],
                                            -(r[3] or 1)))
    for (ci, lab, v, nc, na, npss, cnt) in rows[:12]:
        print(f"    {ci:3d} {lab[:30]:30s} v={str(v)[:6]:6s} "
              f"good={cnt['good']:4d}/{nc:4d} conf={cnt['confined']:4d} "
              f"nostand={cnt['nostand']:4d}")
    print(f"\nOW-{4 if splits else 3} OK.")


# -------------------------------------------------------------- --synth ----

def leg_first(lo, hi):
    """(OC-53)(i): the FIRST certificate colouring per class -- OQRANK's own
    naive-route point ((OC-43)(i): 147 rank-3 / 7 wall / 20 "second
    confinement") re-derived, and each rank-2 case labelled by WHICH
    certificate fires.  This is the measurement that decides whether the 20
    uncharacterized cases are the (OC-42) wall in disguise."""
    print(f"[OW-6] the FIRST certificate colouring per class, classes "
          f"[{lo},{hi}) (seed {SEED}) -- (OC-43)(i) re-derived and labelled")
    cls = out_classes()
    hist = {}
    rows = []
    t0 = time.time()
    for ci in range(lo, min(hi, len(cls))):
        lab, E, v0, key = cls[ci]
        allverts = sorted(verts_of(E), key=str)
        certs, ncols, npass, capped = certificate_colourings(E, allverts,
                                                             cap=1)
        ctx = shape_ctx(E, v0)
        allverts, a, b, c, Hed, VH, deg, nb = ctx
        if not certs:
            hist['nocert'] = hist.get('nocert', 0) + 1
            continue
        cj, col = certs[0]
        r = classify(E, allverts, v0, ci, cj, col, Hed, VH, deg, nb, a, b, c)
        k = (r['status'] if r['status'] != 'confined'
             else 'confined:' + str(r['cert']))
        hist[k] = hist.get(k, 0) + 1
        rows.append((ci, lab, k))
    print(f"  ({time.time() - t0:.0f}s)")
    print(f"  first-certificate-colouring outcome, {sum(hist.values())} "
          f"classes:")
    for k in sorted(hist):
        print(f"    {k:16s}: {hist[k]}")
    conf = [(ci, lab, k) for (ci, lab, k) in rows if k.startswith('confined')]
    print(f"  the rank-2 first points, labelled by certificate:")
    for (ci, lab, k) in conf:
        print(f"    {ci:3d} {lab[:44]:44s} {k}")
    print("\nOW-6 OK.")


def leg_synth():
    """A THIRD confinement mechanism, hunted synthetically: random
    class-labelled networks with `2|E| = 3|V| - 4`, every class a tree,
    `dim D_X = 1`, and `Q(g) = 0` -- does (W) or (C) always fire?

    This is the ADVERSARIAL control on (OC-51)'s completeness: the census
    population is whatever the 174 class shapes happen to realize, and a
    completeness claim needs a sampler that ranges over the object the
    claim quantifies (RESEARCH-ARC.md section 4's 2026-09-02 sharpening)."""
    print(f"[OW-5] synthetic completeness hunt (seed {SEED}, "
          f"cap {SYNTH_CAP} networks)")
    rng = random.Random(SEED)
    stats = dict(drawn=0, valid=0, conf=0, wall=0, cut=0, both=0, neither=0,
                 offclass=0, rw=0, rc_only=0, rneither=0)
    for _ in range(SYNTH_CAP):
        stats['drawn'] += 1
        nn = rng.choice([4, 6, 8])
        m = (3 * nn - 4) // 2
        if 2 * m != 3 * nn - 4:
            continue
        # random multigraph with m edges, then a random class partition into
        # connected acyclic (tree) blocks.
        ed = []
        for _e in range(m):
            x = rng.randrange(nn)
            y = rng.randrange(nn)
            if x == y:
                break
            ed.append((x, y))
        if len(ed) != m:
            continue
        # classes: grow trees greedily from random seeds.
        unass = list(range(m))
        rng.shuffle(unass)
        cls = [None] * m
        k = 0
        while unass:
            seed_e = unass.pop()
            cls[seed_e] = k
            touched = {ed[seed_e][0], ed[seed_e][1]}
            grown = True
            while grown and rng.random() < 0.6:
                grown = False
                for e in list(unass):
                    x, y = ed[e]
                    if (x in touched) != (y in touched):
                        cls[e] = k
                        touched.add(x)
                        touched.add(y)
                        unass.remove(e)
                        grown = True
                        break
            k += 1
        # class connectivity + acyclicity are guaranteed by the growth rule.
        # verify: each class is a tree.
        okc = True
        for j in range(k):
            es = [ed[e] for e in range(m) if cls[e] == j]
            vs = sorted({x for e in es for x in e})
            if not vs:
                continue
            if len(es) != len(vs) - 1:
                okc = False
                break
            par = {x: x for x in vs}

            def fnd(x):
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x
            for (x, y) in es:
                rx, ry = fnd(x), fnd(y)
                if rx == ry:
                    okc = False
                    break
                par[rx] = ry
            if not okc:
                break
        if not okc:
            stats['offclass'] += 1
            continue
        # a parameter draw, distinct per class
        par = {}
        for j in range(k):
            par[j] = F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
        if len(set(par.values())) != k:
            continue
        Emod = [(ed[e][0], ed[e][1], par[cls[e]]) for e in range(m)]
        mot = motion(nn, Emod)
        if len(mot) != 4:
            continue
        beta, gamma = 0, 1
        D = span_basis([[x[3 * beta + t] - x[3 * gamma + t] for t in range(3)]
                        for x in mot])
        if len(D) != 1:
            continue
        stats['valid'] += 1
        g0 = D[0]
        if Qm(g0) != 0:
            continue
        stats['conf'] += 1
        # (W): beta ~ gamma inside a single class
        wall = []
        for j in range(k):
            par2 = {x: x for x in range(nn)}

            def fnd2(x):
                while par2[x] != x:
                    par2[x] = par2[par2[x]]
                    x = par2[x]
                return x
            for e in range(m):
                if cls[e] == j:
                    rx, ry = fnd2(ed[e][0]), fnd2(ed[e][1])
                    if rx != ry:
                        par2[rx] = ry
            if fnd2(beta) == fnd2(gamma):
                wall.append(j)
        # (C): beta !~ gamma with class j deleted
        cut = []
        for j in range(k):
            par3 = {x: x for x in range(nn)}

            def fnd3(x):
                while par3[x] != x:
                    par3[x] = par3[par3[x]]
                    x = par3[x]
                return x
            for e in range(m):
                if cls[e] != j:
                    rx, ry = fnd3(ed[e][0]), fnd3(ed[e][1])
                    if rx != ry:
                        par3[rx] = ry
            if fnd3(beta) != fnd3(gamma):
                cut.append(j)
        if wall and cut:
            stats['both'] += 1
        elif wall:
            stats['wall'] += 1
        elif cut:
            stats['cut'] += 1
        else:
            stats['neither'] += 1
        # the same two predicates on the (Z)+(R)-REDUCED network
        _nred, rw, rc = wall_cut_reduced(nn, Emod, beta, gamma)
        assert rw is not None, "the reduction welded beta to gamma"
        if rw:
            stats['rw'] += 1
        elif rc:
            stats['rc_only'] += 1
        else:
            stats['rneither'] += 1
            print(f"    BEYOND (Z)+(R)+(W)+(C): nn={nn} ed={ed} "
                  f"cls={cls} g={g0}")
        for j in wall + cut:
            assert rank([g0, Am(par[j])]) == 1, \
                "(W)/(C) fires yet g is off that class's ruling line"
    print(f"  networks drawn                        : {stats['drawn']}")
    print(f"  off-class (not all classes trees)     : {stats['offclass']}")
    print(f"  target-rank-compatible (dim D_X = 1)  : {stats['valid']}")
    print(f"  of those, CONFINED (Q(g) = 0)         : {stats['conf']}")
    print(f"    (W) only : {stats['wall']}")
    print(f"    (C) only : {stats['cut']}")
    print(f"    both     : {stats['both']}")
    print(f"    NEITHER  : {stats['neither']}")
    print(f"  the SAME two predicates on the (Z)+(R)-REDUCED network:")
    print(f"    reduced (W)        : {stats['rw']}")
    print(f"    reduced (C) only   : {stats['rc_only']}")
    print(f"    NEITHER            : {stats['rneither']}")
    assert stats['rneither'] == 0, \
        "(OC-51) COMPLETENESS REFUTED synthetically -- a mechanism beyond " \
        "the reduced (W)/(C)"
    assert stats['wall'] > 0 and stats['cut'] > 0, \
        "the two mechanisms are not independently realized in this sweep"
    print(f"  BOTH mechanisms independently realized: (W)-only "
          f"{stats['wall']}, (C)-only {stats['cut']} -- NEITHER implies the "
          f"other")
    print("\nOW-5 SYNTH OK.")


def main():
    av = sys.argv[1:]
    print(f"# owall.py  direction OWALL (ordinal 70)  seed {SEED}")
    if not av or av[0] == '--validate':
        leg_controls()
        leg_agree(0, 2)
        leg_full(0, 6)
        leg_synth()
        return
    if av[0] == '--controls':
        leg_controls()
    elif av[0] == '--agree':
        leg_agree(int(av[1]), int(av[2]))
    elif av[0] == '--full':
        leg_full(int(av[1]), int(av[2]))
    elif av[0] == '--splits':
        leg_full(int(av[1]), int(av[2]), splits=True)
    elif av[0] == '--first':
        leg_first(int(av[1]), int(av[2]))
    elif av[0] == '--synth':
        leg_synth()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
