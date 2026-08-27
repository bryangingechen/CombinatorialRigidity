"""
Direction BTWOCUT (ordinal 44) -- the STRENGTHENED 2-CUT COMPOSITION LEMMA,
which by BINDUC's exhaustive decomposition IS (BE-14):

  across a 2-cut {u,v} with pieces G1, G2 both attaining,
      G attains  <=>  dim(rho_bar_1 + rho_bar_2) = min(delta_1 + delta_2, 6).

Succeeds `notes/scripts/w4/binduc.py` (Steps BE19-BE23).  BINDUC's, BZAVOID's
and BATTAIN's figures are CITED, never re-run here; this driver imports
`binduc` READ-ONLY and reuses its gluing machinery (`split_at_pair`,
`combinatorial_deltas`, `rel_screw_space`, `class_plane_config`,
`hub_classes`, `def_by_partitions`, `flat_config`, `ear`) rather than
reimplementing it.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-25)  THE STRENGTHENED STATEMENT, and the SIMULTANEITY worry is VACUOUS.
             `wcheck` : the welding clause (W) `rho_uv = delta_uv for EVERY
                        pair` at the induction's base classes.  At a
                        3-connected G the clause is FREE (delta_uv = 0 for
                        every pair, and attainment forces rho_uv = 0):
                        EXHAUSTIVE over 3-connected graphs n = 4..6, both the
                        combinatorial half and the flat-configuration half.
                        At max-degree <= 2 it is measured at generic points.
             `spqr`   : the ALTERNATIVE marked (rooted-3-block) frame, whose
                        base class is a 3-connected block MINUS its parent
                        virtual edge.  (BE-25)(iii): such a block still has
                        def_2 = def_3 = 0, by a one-line extension of
                        (BE-20)(i) -- so the marked frame's base is FREE too.
                        EXHAUSTIVE combinatorial sweep n = 4..6, plus the
                        configuration half on a subsample.

  (BE-26)  BINDUC's 56 EAR MISSES ARE A CONSTRUCTOR ARTIFACT, and the fix is
           the piece's OWN moduli -- the coordinator's Job-2 reading, tested.
             `earfix` : BINDUC's 296 ear additions re-run with extra rungs on
                        its own ladder, the decisive one being
                        `class_plane_config` with ALL hubs in ONE class, which
                        flattens the hub part but leaves every
                        pencil-UNCONSTRAINED vertex generic (the ear's
                        interior).  `flat_config` flattens those too, capping
                        rho at 3 = dim Lambda^2(plane).

  (BE-27)  THE GENERAL-POSITION HALF: what the pieces' own moduli supply.
             `moduli` : per split, the EXACT parameter count of the
                        construction's moduli ON EACH SIDE with the shared
                        flags HELD FIXED (the quantity (BE-22)(v) left
                        UNCOUNTED), against the residual gauge group's 7 / 5;
                        plus the multi-seeded measured maximum of
                        dim(rho_bar_1 + rho_bar_2).

  (BE-28)  THE CROSS-PAIR CLOSURE GAP.
             `crosspair`: (W) at EVERY pair of a composed graph, including the
                        pairs that STRADDLE the 2-cut -- the pairs whose
                        welding destroys the cut, so that no composition law
                        reaches them.

  (BE-29)  THE OBSTRUCTION HUNT (HIT shape 3 / F27), and the CONCURRENT-PLANE
           rung that BINDUC's cap 7 named as missing.
             `hunt`   : sweep (graph, 2-cut) instances with BOTH deltas
                        positive -- EXHAUSTIVE at n = 5, 6, plus a sampled
                        tier demanding a PRIVATE HUB ON EACH SIDE -- for an
                        instance whose target the extended constructor cannot
                        reach.  F27 escalation: one cheap draw per instance,
                        then the residuals ONLY multi-seeded.
             `probe`  : the ONE instance the pre-`bundle` ladder missed,
                        dissected under 40 independent ladder runs.

Modes: wcheck | spqr | earfix | moduli | crosspair | hunt | probe |
       validate
Reproduce: python3 notes/scripts/w4/btwocut.py <mode>
All figures exact Q (fractions.Fraction); every rng seeded and printed;
degeneracy guards and a rank/dimension assert on every sampled object
(`notes/scripts/README.md` s4 -- inherited by using binduc's
`assert_generic_star` + `kbare_common.verify_pencil_witness` acceptance gate
inside `class_plane_config` / `flat_config`).
"""
import itertools
import os
import random
import sys
import time

sys.setrecursionlimit(20000)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'kbare'))
sys.path.insert(0, HERE)

from exactcore import rank as rank_exact, neighbors, hat               # noqa: E402
from kbare_common import verts_of, build_rigidity                        # noqa: E402
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (README *Harness debt*, 2026-08-20).  BATTAIN was its first
# --- `w4/` consumer, `bzavoid` the second, `binduc` the third; this driver is
# --- the FOURTH, and the chain is now four deep
# --- (battain -> bzavoid -> binduc -> btwocut).  NO MOVE MADE.
from battain import def2_exact                                           # noqa: E402
from bzavoid import adj_of, connected_spanning, def3_of, edges_of_mask    # noqa: E402
from kbare_common import exact_deficiency                                # noqa: E402
from binduc import (assert_generic_star, class_plane_config,             # noqa: E402
                    combinatorial_deltas, cycle, def_by_partitions,
                    def_pair, deg_of, ear, flat_config, hub_classes,
                    hub_load, hubs_of, motion_space, part_value, path,
                    rel_screw_space, set_partitions, split_at_pair, theta,
                    vertex_connectivity_at_least)


# ============================================================ the extra rung

def hubflat_classes(edges):
    """ONE class holding every hub.  Through `class_plane_config` this flattens
    the hub part of the graph onto a single plane -- exactly what
    `flat_config` does to the HUBS -- while leaving every vertex whose closed
    neighbourhood contains NO hub at a fully generic point of P^3.  That is the
    rung BINDUC's ladder ('singleton' / 'pairwise' / 'closure' then
    `flat_config`) does not have: its three class modes all return SINGLETON
    classes on e.g. the cube, which is infeasible at hub load 4, so it falls
    back to `flat_config`, which flattens the FREE vertices too."""
    H = hubs_of(edges)
    return [frozenset(H)] if H else []


def ladder_moduli(G_edges, side_verts, u, v, classes):
    """EXACT parameter count of the construction's own moduli ON ONE SIDE with
    the shared flags (p_u, pi_u, p_v, pi_v) HELD FIXED:

      + 3 for every hub class whose hubs are all PRIVATE to this side
        (a plane in P^3 is a 3-parameter choice),
      + 3 - min(k(w), 3) for every vertex w PRIVATE to this side, where k(w)
        is the number of classes meeting closedNbhd_G(w) (each imposes one
        linear condition on p_w).

    Classes containing u or v contribute 0: their plane IS the shared flag.
    This is a COUNT -- a lower bound on the side's moduli inside its pencil
    stratum, since the constructor is one family and the stratum may be
    larger.  It is NOT an obstruction proof in either direction."""
    nb = neighbors(G_edges)
    priv = set(side_verts) - {u, v}
    tot = 0
    for C in classes:
        if u in C or v in C:
            continue
        if C <= priv:
            tot += 3
    for w in priv:
        star = {w} | set(nb.get(w, ()))
        k = sum(1 for C in classes if star & C)
        tot += 3 - min(k, 3)
    return tot


def free_vertices(edges):
    """The vertices on which the pencil condition imposes NOTHING once the hub
    planes are fixed: those whose closed neighbourhood contains no hub.  These
    are the piece's OWN moduli in the sense of (BE-22)(v)'s uncounted term."""
    nb = neighbors(edges)
    H = set(hubs_of(edges))
    out = []
    for w in verts_of(edges):
        star = {w} | set(nb.get(w, ()))
        if not (star & H):
            out.append(w)
    return sorted(out, key=str)


def extended_construction(edges, nseeds=3, seed0=0, extra_merge=2,
                          target=None):
    """BINDUC's ladder PLUS the `hubflat` rung PLUS randomized feasible
    coarsenings.  Returns (best_rank, tag, pt).  Every returned `pt` has
    already passed `assert_generic_star` and `verify_pencil_witness` inside
    `class_plane_config` / `flat_config`.

    With `target` given, the ladder STOPS at the first rung reaching it (which
    settles that graph outright, `rank <= target` being universal), so the
    full multi-seeded effort is spent only on the instances that might be
    candidates -- exactly the F27 shape."""
    out = (-1, None, None)

    def offer(tag, pt):
        nonlocal out
        if pt is None:
            return
        r = rank_exact(build_rigidity(edges, pt)[0])
        if r > out[0]:
            out = (r, tag, pt)
        return target is not None and r >= target

    # --- BINDUC's three class modes (read-only reuse)
    for mode in ('singleton', 'pairwise', 'closure'):
        cls = hub_classes(edges, mode)
        for s in range(nseeds):
            if offer(f'{mode}({len(cls)})',
                     class_plane_config(edges,
                                        random.Random(seed0 + 613 * s + 7),
                                        classes=cls)):
                return out
    # --- the NEW rung: all hubs in one class, free vertices generic
    hf = hubflat_classes(edges)
    for s in range(nseeds):
        if offer(f'hubflat({len(hf)})',
                 class_plane_config(edges,
                                    random.Random(seed0 + 977 * s + 11),
                                    classes=hf)):
            return out
    # --- randomized feasible coarsenings between the two extremes
    for s in range(extra_merge * nseeds):
        cls = random_feasible_classes(edges, random.Random(seed0 + 401 * s + 3))
        if cls is None:
            continue
        if offer(f'merge({len(cls)})',
                 class_plane_config(edges,
                                    random.Random(seed0 + 401 * s + 5),
                                    classes=cls)):
            return out
    # --- NEW rungs: class planes in SPECIAL position (BINDUC cap 7)
    for mode in ('bundle', 'halfbundle', 'line'):
        for cls in (hub_classes(edges, 'singleton'),
                    hub_classes(edges, 'pairwise')):
            for s in range(nseeds):
                rng = random.Random(seed0 + 1553 * s + 23)
                pl = structured_planes(len(cls), rng, mode)
                if pl is None:
                    continue
                if offer(f'{mode}({len(cls)})',
                         plane_config(edges, cls, pl, rng)):
                    return out
    # --- BINDUC's flat fallback
    offer('flat', flat_config(edges, random.Random(seed0 + 3)))
    return out


def plane_config(edges, classes, planes, rng, span=25, tries=40):
    """`class_plane_config` with the class planes SUPPLIED rather than drawn
    generically -- the rung BINDUC's cap 7 names as missing ("a graph whose
    attainment needs NON-GENERIC planes reports INFEASIBLE rather than a
    shortfall").  Same acceptance gate: `assert_generic_star` (adjacent points
    distinct AND no two hinge lines coincident at a body) plus
    `kbare_common.verify_pencil_witness`, and a rank/dimension assert on every
    solved system."""
    from fractions import Fraction as F
    from exactcore import nullspace
    from kbare_common import verify_pencil_witness
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    for _ in range(tries):
        pt = {}
        bad = False
        for w in V:
            star = {w} | set(nb.get(w, ()))
            rows = [planes[i] for i, C in enumerate(classes) if star & C]
            if not rows:
                pt[w] = (rq(rng, span), rq(rng, span), rq(rng, span))
                continue
            rk = rank_exact(rows)
            if rk > 3:
                return None
            sol = nullspace(rows)
            assert len(sol) == 4 - rk, 'nullspace dimension mismatch'
            for _ in range(30):
                c = [rq(rng, span) for _ in sol]
                x = [sum(c[i] * sol[i][k] for i in range(len(sol)))
                     for k in range(4)]
                if x[3] != 0:
                    break
            else:
                bad = True
                break
            pt[w] = tuple(x[k] / x[3] for k in range(3))
        if bad or len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        ok, why = verify_pencil_witness(edges, pt)
        if not ok:
            continue
        return pt
    return None


def structured_planes(nclasses, rng, mode, span=25):
    """Class planes in SPECIAL position:
      'bundle'   : all through one generic point q of P^3 (a 3-dim bundle);
      'line'     : all through one generic line (a pencil of planes);
      'halfbundle': half through a common point, half generic.
    `None` if the draw degenerates."""
    from fractions import Fraction as F
    from exactcore import nullspace
    if nclasses == 0:
        return []
    if mode == 'bundle':
        q = [rq(rng, span) for _ in range(3)] + [F(1)]
        out = []
        for _ in range(nclasses):
            sol = nullspace([q])
            assert len(sol) == 3, 'bundle: wrong nullspace dimension'
            c = [rq(rng, span) for _ in sol]
            a = [sum(c[i] * sol[i][k] for i in range(3)) for k in range(4)]
            if not any(x != 0 for x in a):
                return None
            out.append(a)
        return out
    if mode == 'line':
        P = [[rq(rng, span) for _ in range(4)] for _ in range(2)]
        if rank_exact(P) != 2:
            return None
        out = []
        for _ in range(nclasses):
            c = [rq(rng, span), rq(rng, span)]
            a = [c[0] * P[0][k] + c[1] * P[1][k] for k in range(4)]
            if not any(x != 0 for x in a):
                return None
            out.append(a)
        return out
    if mode == 'halfbundle':
        b = structured_planes((nclasses + 1) // 2, rng, 'bundle', span)
        if b is None:
            return None
        g = [[rq(rng, span) for _ in range(4)]
             for _ in range(nclasses - len(b))]
        for a in g:
            if not any(x != 0 for x in a):
                return None
        return b + g
    raise ValueError(mode)


def random_feasible_classes(edges, rng, tries=200):
    """Start from singleton hub classes; while some closed neighbourhood meets
    > 3 classes, merge two classes inside an offending neighbourhood.  Returns
    a feasible class partition (every closed nbhd meets <= 3 classes) or None.
    Strictly between 'singleton' and `hubflat` -- the rungs BINDUC's three
    fixed modes skip."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    if not H:
        return []
    cls = [{h} for h in H]
    for _ in range(tries):
        bad = None
        for w in verts_of(edges):
            star = {w} | set(nb.get(w, ()))
            hit = [i for i, C in enumerate(cls) if star & C]
            if len(hit) > 3:
                bad = hit
                break
        if bad is None:
            return [frozenset(C) for C in cls]
        i, j = rng.sample(bad, 2)
        i, j = min(i, j), max(i, j)
        cls[i] |= cls[j]
        cls.pop(j)
    return None


# ============ a THIRD deficiency oracle: def_3 of a MULTIGRAPH, so that the
# ============ welded quantity g_uv = def_3(G/uv) is computable past the
# ============ set-partition oracle's Bell-number wall

def def3_multi(verts, medges):
    """def_3 = max_P [6(|P|-1) - 5 d(P)] for a MULTIGRAPH given as a list of
    (a, b) pairs WITH repetition (loops must already be dropped), by
    `kbare_common.exact_deficiency`'s part-sum identity extended to
    multiplicities: def_3 = [6(n-1) - 5m] + max-weight packing of pairwise
    disjoint subsets S with f(S) = 5*E_in(S) - 6(|S|-1) > 0."""
    V = sorted(verts, key=str)
    n = len(V)
    idx = {v: i for i, v in enumerate(V)}
    m = len(medges)
    if n == 1:
        return 0
    N = 1 << n
    ein = [0] * N
    bits = [(1 << idx[a]) | (1 << idx[b]) for (a, b) in medges]
    for S in range(N):
        c = 0
        for bm in bits:
            if bm & S == bm:
                c += 1
        ein[S] = c
    pos = []
    for S in range(1, N):
        k = bin(S).count('1')
        if k < 2:
            continue
        f = 5 * ein[S] - 6 * (k - 1)
        if f > 0:
            pos.append((S, f))
    best = 0
    if pos:
        pos.sort(key=lambda t: -t[1])
        suff = [0] * (len(pos) + 1)
        for i in range(len(pos) - 1, -1, -1):
            suff[i] = suff[i + 1] + pos[i][1]

        def bnb(i, used, acc):
            nonlocal best
            if acc > best:
                best = acc
            if i == len(pos) or acc + suff[i] <= best:
                return
            S, f = pos[i]
            if not (S & used):
                bnb(i + 1, used | S, acc + f)
            bnb(i + 1, used, acc)
        bnb(0, 0, 0)
    return max(0, 6 * (n - 1) - 5 * m + best)


def contract_pair(edges, u, v):
    """G/uv as a MULTIGRAPH: parallel edges kept, the uv loop dropped -- the
    contraction (BE-22)(ii)'s welded framework runs on."""
    z = ('@', str(u), str(v))
    out = []
    for (a, b) in edges:
        aa = z if a in (u, v) else a
        bb = z if b in (u, v) else b
        if aa == bb:
            continue
        out.append((aa, bb))
    vs = set()
    for (a, b) in out:
        vs.add(a)
        vs.add(b)
    for w in verts_of(edges):
        if w not in (u, v):
            vs.add(w)
    vs.add(z)
    return sorted(vs, key=str), out


def g_exact(edges, u, v):
    """g_uv(G) = def_3(G / uv) with the contraction taken as a MULTIGRAPH --
    binduc's (BE-21) `g` by its second description.  Cross-checked against the
    set-partition oracle wherever that is affordable."""
    vs, me = contract_pair(edges, u, v)
    return def3_multi(vs, me)


def deltas_at(edges, u, v, check=True):
    """(V1, E1, f1, g1, V2, E2, f2, g2) for a split at the 2-cut {u,v}, with
    `g` by the contraction oracle rather than binduc's set-partition one, so
    the |V| <= 9 wall of `binduc.combinatorial_deltas` is gone.  Returns None
    if {u,v} is not a cut."""
    sp = split_at_pair(edges, u, v)
    if sp is None:
        return None
    V1, E1, V2, E2 = sp
    out = [V1, E1]
    for (Vi, Ei) in ((V1, E1), (V2, E2)):
        f = exact_deficiency(Ei)[0]
        g = g_exact(Ei, u, v)
        assert 0 <= f - g <= 6, ('delta out of [0,6]', Ei, f, g)
        if check and len(Vi) <= 8:
            fo = def_by_partitions(Ei, Vi, D=3)
            go = def_by_partitions(Ei, Vi, D=3, together=(u, v))
            assert (f, g) == (fo, go), ('oracle disagreement', Ei, u, v,
                                        (f, g), (fo, go))
        if Vi is V1:
            out += [f, g, V2, E2]
        else:
            out += [f, g]
    return tuple(out)


# ================================================= pair-level (W) machinery

def rho_at(edges, pt, u, v):
    """rho_uv = dim of the relative-screw image (binduc.rel_screw_space)."""
    return rel_screw_space(edges, pt, u, v)[0]


def delta_all_pairs(edges, verts=None, D=3, check=True):
    """{(u,v): (f, g_uv, delta_uv)} over all unordered pairs, in ONE pass over
    set partitions: a partition with value `val` witnesses g_uv >= val for
    every pair {u,v} sitting inside one of its parts.  Equivalent to calling
    binduc's `def_by_partitions(..., together=(a,b))` per pair (asserted
    against it on the small tier by `check`), but O(Bell(n)) rather than
    O(n^2 Bell(n))."""
    V = sorted(verts_of(edges), key=str) if verts is None else list(verts)
    f = 0
    g = {p: 0 for p in itertools.combinations(V, 2)}
    for P in set_partitions(V):
        val = part_value(edges, P, D)
        if val > f:
            f = val
        for part in P:
            if len(part) < 2:
                continue
            for pr in itertools.combinations(sorted(part, key=str), 2):
                if val > g[pr]:
                    g[pr] = val
    out = {}
    for pr in g:
        assert 0 <= f - g[pr] <= 6, ('delta out of [0,6]', edges, pr, f, g[pr])
        out[pr] = (f, g[pr], f - g[pr])
    if check and len(V) <= 7:
        assert f == exact_deficiency(edges)[0], ('oracle disagreement', edges)
        for pr in list(g)[:4]:
            gg = def_by_partitions(edges, V, D=D, together=pr)
            assert gg == g[pr], ('one-pass oracle disagrees', edges, pr,
                                 gg, g[pr])
    return out


def delta_all_pairs_fast(edges, check=True):
    """The same map as `delta_all_pairs`, but with `f` by
    `kbare_common.exact_deficiency` and each `g_uv` by the CONTRACTION oracle
    `g_exact` -- O(n^2 2^n) instead of O(Bell(n)), so |V| up to ~14 is
    affordable.  Cross-checked against the set-partition version whenever that
    is affordable (|V| <= 8)."""
    V = sorted(verts_of(edges), key=str)
    f = exact_deficiency(edges)[0]
    out = {}
    for pr in itertools.combinations(V, 2):
        g = g_exact(edges, *pr)
        assert 0 <= f - g <= 6, ('delta out of [0,6]', edges, pr, f, g)
        out[pr] = (f, g, f - g)
    if check and len(V) <= 8:
        ref = delta_all_pairs(edges, check=False)
        assert ref == out, ('two all-pairs oracles disagree', edges)
    return out


def w_clause(edges, pt, dmap=None):
    """The welding clause (W): rho_uv = delta_uv at EVERY pair.  Returns
    (ok, [(pair, rho, delta) violations], nchecked)."""
    if dmap is None:
        dmap = delta_all_pairs(edges)
    bad = []
    ker, r, nV = motion_space(edges, pt)
    V = sorted(verts_of(edges), key=str)
    idx = {w: i for i, w in enumerate(V)}
    for (a, b), (f, g, d) in dmap.items():
        ba, bb = 6 * idx[a], 6 * idx[b]
        img = [[m[bb + k] - m[ba + k] for k in range(6)] for m in ker]
        rho = rank_exact(img) if img else 0
        # the UNIVERSAL half of (BE-22)(ii): rho <= dim M - 6 - g always
        assert rho <= len(ker) - 6 - g, ('welded cap broken', a, b, rho, g)
        if rho != d:
            bad.append(((a, b), rho, d))
    return (not bad), bad, len(dmap)


# ======================================= (BE-25): the base classes carry (W)

def run_wcheck(nmax=6, seed=20260826):
    print('===== Step BE24 / (BE-25): the STRENGTHENED statement -- the '
          'welding clause (W) at the induction BASE =====')
    print('  (W)  at a single configuration, for EVERY pair {u,v} of V(G):')
    print('           rho_uv = delta_uv  (equivalently: G/uv attains too).')
    print('  Base 1, 3-CONNECTED: (W) is FREE and it is free for a reason that')
    print('  needs no genericity -- def_3 = 0 by (BE-20)(i) forces g_uv = 0 for')
    print('  every pair (0 <= g_uv <= f = 0), so delta_uv = 0; and attainment')
    print('  means dim M = 6 = the constants, so rho_uv = 0 at every pair.')
    t0 = time.time()
    tot = 0
    tot3 = 0
    cfg = 0
    for n in range(4, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        cnt = 0
        for mask in range(1 << len(pairs)):
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            tot += 1
            if not vertex_connectivity_at_least(n, edges, 3):
                continue
            cnt += 1
            tot3 += 1
            dm = delta_all_pairs(edges)
            for (a, b), (f, g, d) in dm.items():
                assert f == 0, ('def_3 != 0 at a 3-connected graph', edges)
                assert d == 0, ('delta != 0 at a 3-connected graph', edges,
                                a, b, g)
            # the configuration half, on a subsample (exact Q, flat witness)
            if cnt % 7 == 1:
                pt = flat_config(edges, random.Random(seed + mask))
                ok, bad, nch = w_clause(edges, pt, dm)
                assert ok, ('(W) failed at a 3-connected graph', edges, bad)
                r = rank_exact(build_rigidity(edges, pt)[0])
                assert r == 6 * (n - 1), ('flat witness misses target', edges)
                cfg += 1
        print(f'    n = {n}: {cnt} 3-connected labelled graphs, delta_uv = 0 '
              f'at EVERY pair')
    print(f'  EXHAUSTIVE n = 4..{nmax}: {tot3} 3-connected graphs of {tot} '
          f'connected, every pair delta_uv = 0; {cfg} of them additionally '
          f'checked at the flat witness with (W) holding at every pair and '
          f'rank = 6(|V|-1)')
    print('  Base 2, MAX DEGREE <= 2 (paths and cycles): the pencil condition')
    print('  is VACUOUS (three points are always coplanar), so Y = all')
    print('  configurations, irreducible; measured at generic points.')
    rows = []
    for k in range(2, 10):
        E = path(k)
        rows.append((f'P{k}', E))
    for k in range(3, 10):
        rows.append((f'C{k}', cycle(k)))
    okall = True
    for (name, E) in rows:
        V = sorted(verts_of(E), key=str)
        n = len(V)
        dm = delta_all_pairs(E)
        best = None
        for s in range(4):
            pt = generic_config(E, random.Random(seed + 31 * s))
            ok, bad, nch = w_clause(E, pt, dm)
            r = rank_exact(build_rigidity(E, pt)[0])
            tgt = 6 * (n - 1) - def3_of(E, n)
            if best is None or (ok, r) > best[0]:
                best = ((ok, r), bad, nch, tgt)
            if ok and r == tgt:
                break
        (ok, r), bad, nch, tgt = best
        okall = okall and ok and r == tgt
        print(f'    {name:5s}: rank {r}/{tgt} '
              f'{"ATTAINS" if r == tgt else "MISSES"}, (W) at all {nch} pairs: '
              f'{ok}' + ('' if ok else f'  violations {bad[:3]}'))
    print(f'  Base 2 verdict: (W) + attainment at every shape: {okall}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tot3, okall


def generic_config(edges, rng, span=60, tries=60):
    """A fully generic exact-Q point configuration.  LEGAL as a pencil
    configuration only when every closed star has <= 3 points, i.e. max degree
    <= 2 -- asserted."""
    nb = neighbors(edges)
    for v in verts_of(edges):
        assert len(nb.get(v, ())) <= 2, ('generic_config on a graph with a '
                                        'hub', v)
    V = sorted(verts_of(edges), key=str)
    from kbare_common import verify_pencil_witness
    for _ in range(tries):
        pt = {v: (rq(rng, span), rq(rng, span), rq(rng, span)) for v in V}
        if len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        ok, why = verify_pencil_witness(edges, pt)
        if not ok:
            continue
        return pt
    raise RuntimeError('generic_config: no generic draw')


def rq(rng, s=40):
    from fractions import Fraction as F
    return F(rng.randint(-s, s))


# =============== (BE-26): BINDUC's 56 ear misses under the extra ladder rung

def run_earfix(nseeds=3, seed=20260826):
    print('===== Step BE25 / (BE-26): BINDUC\'s 56 EAR MISSES are a '
          'CONSTRUCTOR artifact -- the piece\'s OWN moduli fix them =====')
    print('  BINDUC (BE-22)(vi) measured 296 ear additions to five 3-connected')
    print('  bases; 240 attained, and ALL 56 misses were `cube` with m in')
    print('  {3,4}, cause localized to rho_2 = 3 < delta_2 in {4,5}.  3 is')
    print('  dim Lambda^2(plane): at `flat_config` EVERY point, including the')
    print('  ear\'s INTERIOR, is in one plane, so every hinge line is, so')
    print('  rho <= 3 no matter what.  But an ear-interior vertex whose closed')
    print('  neighbourhood holds no hub is pencil-UNCONSTRAINED -- its point is')
    print('  FREE in P^3.  The rung that uses that freedom while keeping the')
    print('  hub part flat is `class_plane_config` with ALL hubs in ONE class.')
    t0 = time.time()
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    K5 = [(i, j) for i in range(5) for j in range(i + 1, 5)]
    cube = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
            (0, 4), (1, 5), (2, 6), (3, 7)]
    prism = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    bases = [('K4', K4, 4), ('K5', K5, 5), ('prism', prism, 6),
             ('K33', K33, 6), ('cube', cube, 8)]
    tot = att = 0
    misses = []
    bytag = {}
    for (bname, B, nb_) in bases:
        for (a, b) in itertools.combinations(range(nb_), 2):
            for m in (1, 2, 3, 4):
                E = ear(B, a, b, m)
                V = sorted(verts_of(E), key=str)
                n = len(V)
                d3 = def3_of(E, n)
                tgt = 6 * (n - 1) - d3
                r, tag, pt = extended_construction(E, nseeds=nseeds,
                                                   seed0=seed, target=tgt)
                tot += 1
                cd = combinatorial_deltas(E, a, b)
                diag = None
                if cd is not None and pt is not None:
                    V1, E1, f1, g1, V2, E2, f2, g2 = cd
                    d1, d2 = f1 - g1, f2 - g2
                    r1, i1, k1, rk1 = rel_screw_space(E1, pt, a, b)
                    r2, i2, k2, rk2 = rel_screw_space(E2, pt, a, b)
                    rsum = rank_exact(i1 + i2)
                    dimM = 6 * n - r
                    # (BE-22)(i), asserted at every case
                    assert dimM == k1 + k2 - 6 - rsum, (bname, a, b, m, dimM)
                    diag = (r1, d1, r2, d2, rsum, min(d1 + d2, 6))
                if r == tgt:
                    att += 1
                    bytag[tag] = bytag.get(tag, 0) + 1
                    if diag is not None:
                        assert diag[4] == diag[5], (bname, a, b, m, diag)
                else:
                    misses.append((bname, a, b, m, r, tgt, tag, diag))
        print(f'    base {bname:6s}: running total {att}/{tot} attaining')
    print(f'  TOTAL {att} of {tot} ear additions ATTAIN under the extended '
          f'ladder (BINDUC: 240 of 296)')
    # --- the exemplar: one of BINDUC's own 56, flat vs hubflat, side by side
    E = ear(cube, 0, 1, 4)
    V = sorted(verts_of(E), key=str)
    n = len(V)
    tgt = 6 * (n - 1) - def3_of(E, n)
    cd = deltas_at(E, 0, 1)
    V1, E1, f1, g1, V2, E2, f2, g2 = cd
    print(f'  EXEMPLAR cube + ear(m=4) at {{0,1}} (one of BINDUC\'s 56): '
          f'delta_1 = {f1 - g1}, delta_2 = {f2 - g2}, target {tgt}')
    for (tag, pt) in (('flat (BINDUC)',
                       flat_config(E, random.Random(seed + 3))),
                      ('hubflat (new rung)',
                       class_plane_config(E, random.Random(seed + 11),
                                          classes=hubflat_classes(E)))):
        r = rank_exact(build_rigidity(E, pt)[0])
        r1 = rho_at(E1, pt, 0, 1)
        r2 = rho_at(E2, pt, 0, 1)
        offp = sum(1 for w in free_vertices(E)
                   if rank_exact([hat(pt[x]) for x in V if x not in
                                  free_vertices(E)] + [hat(pt[w])]) > 3)
        print(f'    {tag:20s}: rank {r}/{tgt}, rho_1 = {r1}, rho_2 = {r2} '
              f'(delta_2 = {f2 - g2}); ear-interior points off the hub plane: '
              f'{offp} of {len(free_vertices(E))}')
    print(f'  winning rung histogram: '
          f'{sorted(bytag.items(), key=lambda kv: -kv[1])}')
    if misses:
        print(f'  {len(misses)} MISSES remain:')
        for r in misses[:8]:
            print(f'    base={r[0]} pair={(r[1], r[2])} m={r[3]} '
                  f'rank={r[4]}/{r[5]} best-by={r[6]} '
                  f'(rho1,d1,rho2,d2,sum,max)={r[7]}')
        print('    NOT an attainment refutation: `rank <= target` is')
        print('    universal, so a measured rank is a LOWER bound on the')
        print('    stratum maximum -- "not found under this constructor".')
    else:
        print('  ZERO misses.  BINDUC\'s 56 were entirely the `flat_config`')
        print('  artifact, and the fix is the ear\'s OWN moduli: nothing about')
        print('  the general-position half was involved (delta_1 = 0 on every')
        print('  3-connected base, so (BE-22)(vi) applies and the criterion is')
        print('  the single condition rho_2 = delta_2).')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return att, tot, misses


# ============ (BE-27): the pieces' own moduli -- the (BE-22)(v) uncounted term

def split_battery():
    """(name, edges, u, v) with {u,v} a 2-cut, chosen to reach BOTH-SIDES
    non-rigid, which is the genuinely open zone."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    out = [
        ('theta(3,3,3) @ hubs', theta(3, 3, 3), 'u', 'v'),
        ('theta(4,4,4) @ hubs', theta(4, 4, 4), 'u', 'v'),
        ('theta(4,5,6) @ hubs', theta(4, 5, 6), 'u', 'v'),
        ('theta(5,5,5) @ hubs', theta(5, 5, 5), 'u', 'v'),
        ('C10 @ antipodes', cycle(10), 'v0', 'v5'),
        ('C12 @ antipodes', cycle(12), 'v0', 'v6'),
        ('C8 @ antipodes', cycle(8), 'v0', 'v4'),
        ('K4+ear(3) @ 0,1', ear(K4, 0, 1, 3), 0, 1),
        ('K4+2 ears(3,3) @ 0,1', ear(ear(K4, 0, 1, 3), 0, 1, 3, tag='g'),
         0, 1),
        ('two ears(3,4) @ u,v', ear(ear([], 'u', 'v', 3), 'u', 'v', 4,
                                    tag='g'), 'u', 'v'),
        ('two ears(4,4) @ u,v', ear(ear([], 'u', 'v', 4), 'u', 'v', 4,
                                    tag='g'), 'u', 'v'),
        ('theta(4,4,4)+ear(3)', ear(theta(4, 4, 4), 'u', 'v', 3, tag='g'),
         'u', 'v'),
        ('theta(6,6,6) @ hubs', gen_theta([6, 6, 6]), 'u', 'v'),
        # BOTH sides carrying TWO PRIVATE hubs -- the genuinely open zone at
        # its hardest: neither side is a path, neither side is rigid.
        ('both sides hubbed (3,3)', two_hubbed(3, 3), 'u', 'v'),
        ('both sides hubbed (3,4)', two_hubbed(3, 4), 'u', 'v'),
        ('both sides hubbed (4,4)', two_hubbed(4, 4), 'u', 'v'),
    ]
    return out


def gen_theta(lengths):
    """u, v joined by len(lengths) internally-disjoint paths of the given
    EDGE lengths.  Splitting at {u,v} puts the first path on side 1 and the
    rest on side 2 -- or, with `split_at_pair`, the first COMPONENT."""
    E = []
    k = 0
    for L in lengths:
        prev = 'u'
        for _ in range(L - 1):
            k += 1
            cur = f'y{k}'
            E.append((prev, cur))
            prev = cur
        E.append((prev, 'v'))
    return E


def two_hubbed(m1, m2):
    """Two sides glued at {u,v}; side s is  u - c_s,  c_s joined to d_s by TWO
    internally-disjoint paths of m_s edges,  d_s - v.  Both c_s and d_s are
    degree-3 hubs PRIVATE to that side, and for m_s >= 3 the side is
    non-rigid, so this is the both-sides-non-rigid-with-hubs zone."""
    E = []
    for s, m in enumerate((m1, m2)):
        c, d = f'c{s}', f'd{s}'
        E += [('u', c), (d, 'v')]
        k = 0
        for _ in range(2):
            prev = c
            for _ in range(m - 1):
                k += 1
                cur = f'z{s}_{k}'
                E.append((prev, cur))
                prev = cur
            E.append((prev, d))
    return E


def run_moduli(nseeds=6, seed=20260826):
    print('===== Step BE26 / (BE-27): the GENERAL-POSITION half -- the '
          'pieces\' OWN moduli, which (BE-22)(v) left UNCOUNTED =====')
    print('  (BE-22)(v) prices the residual gauge group at dim 7 (adjacent cut')
    print('  pair) / 5 (non-adjacent) against Gr(3,6)\'s 9 and concludes it')
    print('  "cannot supply" general position.  Its own cap says that is a')
    print('  COUNT, not an obstruction proof, and that the pieces\' own moduli')
    print('  are uncounted.  Counted here, EXACTLY and combinatorially: with')
    print('  the shared flags (p_u, pi_u, p_v, pi_v) FIXED, side i still has 3')
    print('  free parameters for every vertex whose closed neighbourhood holds')
    print('  no hub, plus 2 for every non-hub in exactly one hub\'s star, etc.')
    print('  This is a COUNT of a lower bound on the moduli -- it is NOT a')
    print('  proof that transversality is attained.  The measured column is')
    print('  what carries that, per instance.')
    t0 = time.time()
    print()
    print('  | split | d1,d2 | side moduli w/ flags FIXED (1/2) | gauge | '
          'dim(rho1+rho2) best | max | reached |')
    reached = 0
    tot = 0
    rowsout = []
    for (name, E, u, v) in split_battery():
        cd = deltas_at(E, u, v)
        if cd is None:
            print(f'  {name}: NOT a 2-cut -- skipped')
            continue
        V1, E1, f1, g1, V2, E2, f2, g2 = cd
        d1, d2 = f1 - g1, f2 - g2
        n, dd2, dd3 = def_pair(E)
        tgt = 6 * (n - 1) - dd3
        adjacent = any(set(e) == {u, v} for e in E)
        gauge = 7 if adjacent else 5
        fv1 = [w for w in free_vertices(E1) if w not in (u, v)]
        fv2 = [w for w in free_vertices(E2) if w not in (u, v)]
        # free_vertices is computed on the piece; a vertex free in the piece
        # may be constrained in G (it can sit in a hub's star through the other
        # side).  Recompute against G to stay honest.
        fvG = set(free_vertices(E))
        fv1 = [w for w in fv1 if w in fvG]
        fv2 = [w for w in fv2 if w in fvG]
        cls_hf = hubflat_classes(E)
        cls_sg = hub_classes(E, 'singleton')
        mod1 = max(ladder_moduli(E, V1, u, v, cls_hf),
                   ladder_moduli(E, V1, u, v, cls_sg))
        mod2 = max(ladder_moduli(E, V2, u, v, cls_hf),
                   ladder_moduli(E, V2, u, v, cls_sg))
        best = (-1, None, None)
        for s in range(nseeds):
            r, tag, pt = extended_construction(E, nseeds=2,
                                               seed0=seed + 1009 * s,
                                               target=tgt)
            if pt is None:
                continue
            r1, i1, k1, rk1 = rel_screw_space(E1, pt, u, v)
            r2, i2, k2, rk2 = rel_screw_space(E2, pt, u, v)
            rsum = rank_exact(i1 + i2)
            dimM = 6 * n - r
            assert dimM == k1 + k2 - 6 - rsum, (name, s)
            if (rsum, r) > (best[0], -1 if best[2] is None else best[2]):
                best = (rsum, tag, r)
        mx = min(d1 + d2, 6)
        tot += 1
        ok = (best[0] == mx)
        reached += 1 if ok else 0
        print(f'  | {name:24s} | {d1},{d2} | {mod1}/{mod2} '
              f'(free verts {len(fv1)}/{len(fv2)}) | {gauge} | {best[0]} '
              f'({best[1]}) | {mx} | {"YES" if ok else "NO"} '
              f'| rank {best[2]}/{tgt}')
        rowsout.append((name, d1, d2, mod1, mod2, gauge, best[0], mx,
                        best[2], tgt))
    print()
    print(f'  {reached} of {tot} splits reach dim(rho1+rho2) = '
          f'min(d1+d2,6) under the extended, multi-seeded constructor.')
    print('  DISCLOSURE (mandatory): the "free verts" column is a COUNT of')
    print('  parameters, i.e. a LOWER bound on the piece\'s own moduli, and a')
    print('  count can never be an obstruction proof in either direction.  The')
    print('  "reached" column is the only load-bearing evidence, and each YES')
    print('  is a per-instance THEOREM (rank <= target is universal, so an')
    print('  attaining exact-Q draw settles that graph); each NO is')
    print('  "not found under this constructor", never "does not exist".')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return reached, tot, rowsout


# ================================ (BE-28): the CROSS-PAIR closure obligation

def run_crosspair(nseeds=4, ncensus=1200, seed=20260826):
    print('===== Step BE27 / (BE-28): the CROSS-PAIR closure gap -- (W) at '
          'the pairs that STRADDLE the 2-cut =====')
    print('  The strengthened statement must be usable as an INDUCTION')
    print('  HYPOTHESIS at whichever pair the next 2-cut turns out to be, so')
    print('  the natural shape is (W) at EVERY pair.  But its CONCLUSION for G')
    print('  then also has to cover pairs {x,y} with x, y private to OPPOSITE')
    print('  sides -- and G/xy is NOT decomposable at {u,v} (the merged vertex')
    print('  reconnects the two sides), so no composition law reaches it.')
    print('  Measured: does (W) hold at cross pairs anyway?')
    t0 = time.time()
    tot = ok_all = 0
    crossbad = []
    for (name, E, u, v) in split_battery():
        V = sorted(verts_of(E), key=str)
        if len(V) > 14:
            print(f'  {name}: |V| = {len(V)} > 14, the all-pairs oracle is too '
                  f'expensive -- skipped')
            continue
        sp = split_at_pair(E, u, v)
        if sp is None:
            continue
        V1, E1, V2, E2 = sp
        S1 = set(V1) - {u, v}
        S2 = set(V2) - {u, v}
        dm = delta_all_pairs_fast(E)
        best = None
        for s in range(nseeds):
            r, tag, pt = extended_construction(E, nseeds=2,
                                               seed0=seed + 733 * s,
                                               target=6 * (len(V) - 1)
                                               - def3_of(E, len(V)))
            if pt is None:
                continue
            good, bad, nch = w_clause(E, pt, dm)
            if best is None or len(bad) < len(best[1]):
                best = (good, bad, nch, r, tag)
            if good:
                break
        if best is None:
            print(f'  {name}: no configuration -- skipped')
            continue
        good, bad, nch, r, tag = best
        n = len(V)
        tgt = 6 * (n - 1) - def3_of(E, n)
        cross = [b for b in bad if (b[0][0] in S1 and b[0][1] in S2)
                 or (b[0][0] in S2 and b[0][1] in S1)]
        same = [b for b in bad if b not in cross]
        tot += 1
        ok_all += 1 if good else 0
        print(f'  {name:26s}: rank {r}/{tgt} by {tag}; (W) at all {nch} '
              f'pairs: {good}; violations {len(bad)} '
              f'(cross {len(cross)}, non-cross {len(same)})')
        if bad:
            for b in bad[:4]:
                print(f'      pair {b[0]}: rho = {b[1]}, delta = {b[2]}'
                      f'{"  [CROSS]" if b in cross else ""}')
            crossbad.append((name, len(cross), len(same)))
    print(f'  {ok_all} of {tot} battery graphs satisfy (W) at EVERY pair at a '
          f'single configuration.')
    # ---- the exhaustive tier: every small graph with a 2-cut, both deltas > 0
    cens = two_cut_census(nexh=6, nsamp=(), seed=seed)
    cens = [c for c in cens if c[0] <= 6]
    rng = random.Random(seed)
    if len(cens) > ncensus:
        cens = rng.sample(cens, ncensus)
    print(f'  CENSUS tier -- (graph, 2-cut) instances with d1, d2 > 0 drawn '
          f'from the EXHAUSTIVE n = 5, 6 census (seeded subsample of '
          f'{len(cens)}):')
    ctot = cok = 0
    cbadrows = []
    for (n, E, u, v, d1, d2) in cens:
        sp = split_at_pair(E, u, v)
        if sp is None:
            continue
        V1, E1, V2, E2 = sp
        S1, S2 = set(V1) - {u, v}, set(V2) - {u, v}
        dm = delta_all_pairs_fast(E)
        best = None
        for s in range(nseeds):
            r, tag, pt = extended_construction(E, nseeds=2,
                                               seed0=seed + 733 * s,
                                               target=6 * (len(V) - 1)
                                               - def3_of(E, len(V)))
            if pt is None:
                continue
            good, bad, nch = w_clause(E, pt, dm)
            if best is None or len(bad) < len(best[1]):
                best = (good, bad, nch, r, tag)
            if good:
                break
        if best is None:
            continue
        good, bad, nch, r, tag = best
        ctot += 1
        cok += 1 if good else 0
        if not good:
            cross = [b for b in bad if (b[0][0] in S1 and b[0][1] in S2)
                     or (b[0][0] in S2 and b[0][1] in S1)]
            cbadrows.append((n, E, u, v, d1, d2, len(bad), len(cross),
                             bad[:3], r, tag))
    print(f'    {cok} of {ctot} instances satisfy (W) at EVERY pair')
    if cbadrows:
        ncross = sum(1 for row in cbadrows if row[7] > 0)
        print(f'    {len(cbadrows)} with a violation, {ncross} of them '
              f'involving a CROSS pair.  First rows:')
        for row in cbadrows[:8]:
            print(f'      n={row[0]} cut=({row[2]},{row[3]}) '
                  f'd=({row[4]},{row[5]}) rank={row[9]} by {row[10]}; '
                  f'{row[6]} violations ({row[7]} cross): {row[8]}')
        print('    CLASSIFICATION: a (W) violation at a FOUND configuration is')
        print('    a constructor cap, not a proof that no configuration')
        print('    satisfies (W) -- `rho <= delta` is the universal direction,')
        print('    so a measured rho is a LOWER bound on the stratum maximum.')
    if crossbad:
        print('  So the all-pairs shape is NOT satisfied by the constructor at')
        print('  every instance; the violations localize the closure question.')
    else:
        print('  So the simultaneity worry BINDUC disclosed as cap 9 is not')
        print('  merely satisfiable at seven splits: it holds at every pair of')
        print('  every measured composed graph.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return ok_all, tot, crossbad


# ============================================ (BE-29): the obstruction hunt

def two_cut_census(nexh=6, nsamp=(7, 8), nmask=4000, seed=20260826,
                   need_both_delta=True, need_both_hub=False):
    """(graph, 2-cut) instances with BOTH sides' delta positive: EXHAUSTIVE
    over all connected labelled graphs on n = 5..nexh with max degree <= 4,
    plus `nmask` seeded random masks at each n in `nsamp`.  One instance per
    graph (the first qualifying 2-cut).  `need_both_hub` additionally demands a
    PRIVATE hub on each side -- the hardest zone, where neither side is a path.
    Deltas by the FAST oracles (`exact_deficiency` + the contraction oracle
    `g_exact`), cross-checked against binduc's set-partition oracle inside
    `deltas_at`."""
    rng = random.Random(seed)
    out = []
    tiers = [(n, None) for n in range(5, nexh + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        if samp is None:
            masks = range(1 << len(pairs))
        else:
            masks = [rng.getrandbits(len(pairs)) for _ in range(samp)]
        nb_local = None
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            if max(deg_of(n, edges)) > 4:
                continue
            nb_local = neighbors(edges)
            for (u, v) in pairs:
                cd = deltas_at(edges, u, v, check=False)
                if cd is None:
                    continue
                V1, E1, f1, g1, V2, E2, f2, g2 = cd
                d1, d2 = f1 - g1, f2 - g2
                if need_both_delta and not (d1 > 0 and d2 > 0):
                    continue
                if len(V1) < 3 or len(V2) < 3:
                    continue
                if need_both_hub:
                    h1 = any(len(nb_local[w]) >= 3 for w in V1
                             if w not in (u, v))
                    h2 = any(len(nb_local[w]) >= 3 for w in V2
                             if w not in (u, v))
                    if not (h1 and h2):
                        continue
                out.append((n, edges, u, v, d1, d2))
                break
    return out


def hunt_tier(cens, label, nseeds_escalate=4, seed=20260826):
    """Pass 1: one cheap ladder draw per instance, stopping at the target
    (which SETTLES that graph -- `rank <= target` is universal).  Pass 2: the
    residuals only, multi-seeded, per F27 (rank is lower semicontinuous, so a
    one-draw shortfall is worthless as evidence)."""
    hist = {}
    resid = []
    attain = 0
    for (n, E, u, v, d1, d2) in cens:
        tgt = 6 * (n - 1) - def3_of(E, n)
        hist[(d1, d2)] = hist.get((d1, d2), 0) + 1
        r, tag, pt = extended_construction(E, nseeds=1, seed0=seed,
                                           extra_merge=1, target=tgt)
        if r == tgt:
            attain += 1
        else:
            resid.append((n, E, u, v, d1, d2, tgt))
    print(f'    {label}: pass 1 (one ladder draw) settles {attain} of '
          f'{len(cens)}; {len(resid)} residuals escalate')
    short = []
    for (n, E, u, v, d1, d2, tgt) in resid:
        best = (-1, None, None)
        for s in range(nseeds_escalate):
            r, tag, pt = extended_construction(
                E, nseeds=3, seed0=seed + 1223 * s, extra_merge=3, target=tgt)
            if pt is None:
                continue
            cd = deltas_at(E, u, v, check=False)
            V1, E1, f1, g1, V2, E2, f2, g2 = cd
            r1, i1, k1, rk1 = rel_screw_space(E1, pt, u, v)
            r2, i2, k2, rk2 = rel_screw_space(E2, pt, u, v)
            rsum = rank_exact(i1 + i2)
            # (BE-22)(i) asserted on every escalated instance
            assert 6 * n - r == k1 + k2 - 6 - rsum, (E, u, v, s)
            if r > best[0]:
                best = (r, tag, rsum)
            if r == tgt:
                break
        if best[0] == tgt:
            attain += 1
        else:
            short.append((n, E, u, v, d1, d2, best[0], tgt, best[2],
                          min(d1 + d2, 6), best[1]))
    print(f'    {label}: {attain} of {len(cens)} ATTAIN after escalation; '
          f'{len(short)} shortfalls')
    print(f'    {label}: (d1,d2) histogram, top 8: '
          f'{sorted(hist.items(), key=lambda kv: -kv[1])[:8]}')
    return attain, len(cens), short


def run_hunt(nexh=6, nmask=15000, seed=20260826):
    print('===== Step BE28 / (BE-29): the OBSTRUCTION HUNT -- a 2-cut with '
          'BOTH deltas positive where the criterion\'s maximum is not '
          'reached =====')
    print('  The genuinely open zone of the strengthened 2-cut lemma is BOTH')
    print('  sides non-rigid with positive deltas ((BE-22)(iv) closes')
    print('  delta1 = delta2 = 0, (BE-22)(vi) closes one rigid side).  Swept')
    print('  here under the EXTENDED constructor with F27 escalation: one')
    print('  cheap draw per instance, then the residuals ONLY multi-seeded.')
    t0 = time.time()
    print('  TIER A -- every (graph, 2-cut) with d1, d2 > 0, EXHAUSTIVE over '
          f'connected labelled graphs on n = 5..{nexh}, max degree <= 4:')
    cA = two_cut_census(nexh=nexh, nsamp=(), seed=seed)
    aA, tA, sA = hunt_tier(cA, 'tier A', seed=seed)
    print(f'  TIER B -- the same with a PRIVATE HUB ON EACH SIDE (neither side '
          f'a path), {nmask} seeded masks at each of n = 7, 8, 9:')
    cB = two_cut_census(nexh=4, nsamp=(7, 8, 9), nmask=nmask, seed=seed,
                        need_both_hub=True)
    aB, tB, sB = hunt_tier(cB, 'tier B', seed=seed)
    short = sA + sB
    print(f'  TOTAL {aA + aB} of {tA + tB} instances ATTAIN')
    if short:
        print(f'  {len(short)} shortfalls -- CANDIDATES, never refutations:')
        for x in short[:10]:
            print(f'    n={x[0]} cut=({x[2]},{x[3]}) d=({x[4]},{x[5]}) '
                  f'rank {x[6]}/{x[7]} dim(rho1+rho2) {x[8]}/{x[9]} '
                  f'best-by={x[10]} E={x[1]}')
        print('    CLASSIFICATION (mandatory): each row is "not found under')
        print('    this constructor".  `rank <= target` is universal, so a')
        print('    measured rank is a LOWER bound on the stratum maximum; only')
        print('    a cap-free argument could turn one into a refutation.')
    else:
        print('  ZERO shortfalls: the criterion\'s maximum is reached at every')
        print('  swept instance with both deltas positive, INCLUDING every')
        print('  instance with a private hub on each side.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return aA + aB, tA + tB, short


# ========= (BE-25) check (c) for the MARKED frame: the SPQR leaf base classes

def run_spqr(nmax=6, seed=20260826):
    print('===== Step BE24 / (BE-25): the MARKED (rooted-SPQR) frame -- its '
          'BASE is FREE, by an argument =====')
    print('  The all-pairs shape (W) is what makes the induction HYPOTHESIS')
    print('  usable at whichever pair the next 2-cut turns out to be, but its')
    print('  CONCLUSION then has to cover CROSS pairs, for which no')
    print('  composition law exists (Step BE27).  The alternative that avoids')
    print('  cross pairs entirely is to recurse down a ROOTED 3-block (SPQR)')
    print('  tree: each subtree-union H attaches to the rest at exactly ONE')
    print('  separation pair {u,v}, so ONE marked pair suffices.  The price is')
    print('  a NEW base class -- an SPQR LEAF is a 3-connected block MINUS its')
    print('  parent virtual edge, a path, or a single edge.  Paths and single')
    print('  edges are free (Step BE24); the leaf 3-block is settled here.')
    print()
    print('  (BE-25)(iii): a 3-CONNECTED graph MINUS ONE EDGE still has')
    print('  def_2 = def_3 = 0.  Proof, extending (BE-20)(i) by one line: for')
    print('  a q >= 2 partition of a 3-connected B, 2 d_B(P) = sum |bdry V_i|')
    print('  >= 3q, so d_B(P) >= ceil(3q/2); deleting one edge gives')
    print('  d_H(P) >= ceil(3q/2) - 1, whence')
    print('    3(q-1) - 2 d_H(P) <= 3q - 3 - 2(ceil(3q/2) - 1) <= -1 < 0  and')
    print('    6(q-1) - 5 d_H(P) <= 6q - 1 - 5 ceil(3q/2) <= -1.5q - 1 < 0,')
    print('  so the q = 1 partition (value 0) is the maximum in both.  Hence')
    print('  every SPQR leaf 3-block is RIGID, delta_uv = 0 at EVERY pair, and')
    print('  S1 holds for the same reason base 1 does -- FREE, no genericity.')
    t0 = time.time()
    # --- combinatorial half, EXHAUSTIVE
    tot = 0
    fpos = 0
    worst2 = worst3 = None
    graphs = []
    for n in range(4, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        cnt = 0
        for mask in range(1 << len(pairs)):
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            if not vertex_connectivity_at_least(n, edges, 3):
                continue
            cnt += 1
            graphs.append((n, edges, cnt))
            for (u, v) in edges:
                H = [e for e in edges if set(e) != {u, v}]
                if not connected_spanning(n, adj_of(n, H)):
                    continue
                f = exact_deficiency(H)[0]
                f2 = def2_exact(H)
                tot += 1
                if f > 0 or f2 > 0:
                    fpos += 1
                # the proof's OWN inequality, swept separately: the worst
                # q >= 2 partition value of H, by the set-partition oracle
                if n <= 6 and cnt % 40 == 1:
                    V = sorted(verts_of(H), key=str)
                    w2 = max(part_value(H, P, 2) for P in set_partitions(V)
                             if len(P) >= 2)
                    w3 = max(part_value(H, P, 3) for P in set_partitions(V)
                             if len(P) >= 2)
                    worst2 = w2 if worst2 is None else max(worst2, w2)
                    worst3 = w3 if worst3 is None else max(worst3, w3)
        print(f'    n = {n}: {cnt} 3-connected labelled graphs')
    print(f'  EXHAUSTIVE n = 4..{nmax}: {tot} (3-connected B, edge uv) leaf '
          f'blocks B - uv, of which {fpos} have def_2 > 0 or def_3 > 0')
    print(f'  worst q >= 2 partition value over the swept subsample: '
          f'def_2-form {worst2}, def_3-form {worst3} (the proof bounds both '
          f'by -1; a value of exactly -1 means the bound is TIGHT)')
    # --- configuration half, on a subsample
    tot2 = att = wok = 0
    bad = []
    for (n, edges, cnt) in graphs:
        if n == 6 and cnt % 3 != 1:
            continue
        for (u, v) in edges:
            H = [e for e in edges if set(e) != {u, v}]
            if not connected_spanning(n, adj_of(n, H)):
                continue
            f = exact_deficiency(H)[0]
            g = g_exact(H, u, v)
            d = f - g
            tgt = 6 * (n - 1) - f
            r, tag, pt = extended_construction(H, nseeds=2, seed0=seed,
                                               extra_merge=2, target=tgt)
            tot2 += 1
            if pt is None:
                bad.append((n, H, u, v, None, tgt, f, g, d, 'no config'))
                continue
            if r == tgt:
                att += 1
            rho = rho_at(H, pt, u, v)
            if r == tgt and rho == d:
                wok += 1
            else:
                bad.append((n, H, u, v, r, tgt, f, g, d, rho))
    print(f'  CONFIGURATION half (every leaf at n = 4, 5; every third '
          f'3-connected graph at n = 6): {att} of {tot2} ATTAIN and {wok} of '
          f'{tot2} additionally have rho_uv = delta_uv, i.e. CARRY S1')
    if bad:
        print(f'  {len(bad)} leaves do NOT carry S1 -- CANDIDATES, never '
              f'refutations:')
        for x in bad[:8]:
            print(f'    n={x[0]} marked=({x[2]},{x[3]}) rank {x[4]}/{x[5]} '
                  f'f={x[6]} g={x[7]} delta={x[8]} rho={x[9]} H={x[1]}')
    else:
        print('  ZERO failures.  DISCLOSURE: S1 holds at the leaf 3-block for')
        print('  the SAME reason base 1 does -- the block minus its virtual')
        print('  edge is RIGID -- so this is not independent evidence about')
        print('  the flexible case; it is the argument above, confirmed.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return wok, tot2, bad


# ============================== the shortfall, dissected under heavy seeding

SHORTFALL = [(0, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 4), (3, 6),
             (5, 7), (6, 7)]


def dissect(E, u, v, nseeds=40, seed=20260826, label=''):
    """Full dissection of one (graph, 2-cut): both pieces' own attainment,
    the fibre-product law, the criterion, and the best rank over `nseeds`
    independent ladder runs (F27: a shortfall claim needs many seeds)."""
    V = sorted(verts_of(E), key=str)
    n = len(V)
    f = exact_deficiency(E)[0]
    tgt = 6 * (n - 1) - f
    cd = deltas_at(E, u, v)
    V1, E1, f1, g1, V2, E2, f2, g2 = cd
    d1, d2 = f1 - g1, f2 - g2
    law = max(g1 + g2, f1 + f2 - 6)
    print(f'  {label} cut {{{u},{v}}}: |V| = {n}, def_3(G) = {f}, '
          f'target = {tgt}')
    print(f'    side 1 {sorted(map(str, V1))}: f1 = {f1}, g1 = {g1}, '
          f'delta1 = {d1}')
    print(f'    side 2 {sorted(map(str, V2))}: f2 = {f2}, g2 = {g2}, '
          f'delta2 = {d2}')
    print(f'    (BE-21) law max(g1+g2, f1+f2-6) = {law}; def_3(G) = {f}: '
          f'{law == f}')
    assert law == f, ('(BE-21) law broken', E, u, v, law, f)
    best = (-1, None, None)
    stats = {}
    for s in range(nseeds):
        r, tag, pt = extended_construction(E, nseeds=3, seed0=seed + 7919 * s,
                                           extra_merge=3, target=tgt)
        if pt is None:
            continue
        r1, i1, k1, rk1 = rel_screw_space(E1, pt, u, v)
        r2, i2, k2, rk2 = rel_screw_space(E2, pt, u, v)
        rsum = rank_exact(i1 + i2)
        assert 6 * n - r == k1 + k2 - 6 - rsum, (E, u, v, s)
        at1 = (rk1 == 6 * (len(V1) - 1) - f1)
        at2 = (rk2 == 6 * (len(V2) - 1) - f2)
        key = (r, at1, at2, r1, r2, rsum)
        stats[key] = stats.get(key, 0) + 1
        if r > best[0]:
            best = (r, tag, key)
        if r == tgt:
            break
    print(f'    best rank over {nseeds} independent ladder runs: {best[0]} / '
          f'{tgt} (by {best[1]})')
    print('    (rank, side1 attains, side2 attains, rho1, rho2, '
          'dim(rho1+rho2)) -> count:')
    for k, c in sorted(stats.items(), key=lambda kv: -kv[0][0])[:6]:
        print(f'      {k} -> {c}')
    print(f'    criterion max min(d1+d2,6) = {min(d1 + d2, 6)}')
    return best[0], tgt, (d1, d2), stats


def run_probe(nseeds=40, seed=20260826):
    print('===== Step BE28 / (BE-29): the ONE shortfall of the hunt, '
          'DISSECTED =====')
    print('  The `hunt` tier-B sweep returned exactly one instance whose')
    print('  target the extended constructor did not reach.  Dissected here')
    print('  under 40 independent ladder runs, with both pieces\' own')
    print('  attainment reported separately -- because (BE-22)(iii) is')
    print('  conditional on BOTH PIECES ATTAINING, so a G-level shortfall at a')
    print('  SATISFIED criterion can only mean a piece is short.')
    t0 = time.time()
    dissect(SHORTFALL, 2, 3, nseeds=nseeds, seed=seed, label='shortfall')
    print()
    print('  Control: the same graph at its OTHER 2-cuts and 1-cuts, to')
    print('  localize the failure.')
    V = sorted(verts_of(SHORTFALL), key=str)
    for (a, b) in itertools.combinations(V, 2):
        if deltas_at(SHORTFALL, a, b, check=False) is None:
            continue
        cd = deltas_at(SHORTFALL, a, b, check=False)
        V1, E1, f1, g1, V2, E2, f2, g2 = cd
        print(f'    cut {{{a},{b}}}: sides {len(V1)}/{len(V2)} vertices, '
              f'delta = ({f1 - g1}, {f2 - g2})')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')


# ==================================================================== validate

def run_validate():
    print('##### btwocut validate -- reduced tiers of all seven modes #####')
    run_wcheck(nmax=5)
    print()
    run_spqr(nmax=5)
    print()
    run_earfix(nseeds=2)
    print()
    run_moduli(nseeds=3)
    print()
    run_crosspair(nseeds=2, ncensus=120)
    print()
    run_hunt(nexh=5, nmask=1500)


MODES = {
    'wcheck': run_wcheck,
    'earfix': run_earfix,
    'moduli': run_moduli,
    'crosspair': run_crosspair,
    'hunt': run_hunt,
    'spqr': run_spqr,
    'probe': run_probe,
    'validate': run_validate,
}

if __name__ == '__main__':
    if len(sys.argv) < 2 or sys.argv[1] not in MODES:
        print(f'usage: {sys.argv[0]} [{" | ".join(MODES)}]')
        sys.exit(1)
    MODES[sys.argv[1]]()
