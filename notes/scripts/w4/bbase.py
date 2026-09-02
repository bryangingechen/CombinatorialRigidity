"""
Direction BBASE (ordinal 62) -- THE FLAG BASE off the no-adjacent-hubs class,
(BE-65)(i) / (BE-68)(ii) item 1, the smaller of half (B)'s two residue items.

  TARGET  (BE-65)(i) says the legal flag assignments on the hub set `W` are
          the pencil configurations of `B_real` -- the graph whose edges are
          the LENGTH-1 branches -- a point `p_z` and a plane `pi_z ni p_z`
          per hub with `p_{z'} in pi_z` and `p_z in pi_{z'}` on every
          `B_real`-edge; a product of irreducible rational bundles iff
          `E(B_real) = {}`, and "the phase's own problem one level down"
          otherwise.  Is that base nonempty / irreducible / rational with
          dense Q-points off the free class?

  THE ANSWER, said at the top.  YES, and the object is NOT (CH-1)'s.  The
  base is the FLAG variety of `B_real` -- a flag at EVERY vertex -- whereas
  `A(B_real)` in Sec.(K-chart)'s sense carries normals only at vertices of
  degree >= 3, of which `B_real` has few or none.  Read as
  Sec.(K-chart)'s tower with the hub set taken to be ALL of `W`, the base is
  its STAGES 1-2 ONLY: stages 3 and 4, which are where min degree 2 and
  girth >= 4 are spent, DO NOT EXIST, because `B_real` has no non-hub
  vertices.  What replaces them:

    (BE-89)  the base FACTORS over `B_real`'s connected components, and is
             cut in `Fl^W` by `2|E|` equations, so its expected dimension is
             `5|W| - 2|E|` -- verified by an exact-Q Jacobian rank.
    (BE-90)  `B_real` a FOREST  ==>  the base is nonempty, IRREDUCIBLE,
             Q-rational with dense Q-points, of that dimension --
             UNCONDITIONALLY: no genericity, no degree bound.  The flag
             tower over `Fl` has fibre `F_Pi`, irreducible of CONSTANT
             dimension 3 at EVERY `Pi`.
    (BE-91)  max degree <= 2  ==>  the same on the constant-rank locus
             `Base^o`, by the point-first bundle.
    (BE-92)  the FULL base is REDUCIBLE at a triangle (flag dims 10 > 9) and
             at a 4-cycle (12 = 12).  Both extra components sit inside
             `U^c`, which the arc's own gate `G` already excludes; and on
             the class girth >= 6 forbids both shapes outright.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  census   THE `B_real` CENSUS, and job 2's `hcard` transport.  Exhaustive
           over the K4-skeleton class tier (`gridcol.class_shape`, sum of
           branch lengths 18) peeled at every 2-cut, plus sampled prism /
           K33 tiers, plus the OFF-CLASS `bpeel.constructed_tier` as the
           contrast.  Asserts the transport identity
           `d_z(B_real) - d_z(Lambda(H)) = |N_H(z) cap ({u,v} \\ hubs(H))|`
           at every piece, which is why `Delta(B_real) <= 2` FAILS while
           `hcard` holds: `W` is the marked-pair-augmented hub set.

  dim      (BE-89) THE COMPLETE-INTERSECTION DIMENSION.  Exact-Q Jacobian
           rank `= |W| + 2|E|` at drawn base points over a menu of shapes,
           hence `dim = 5|W| - 2|E|`, matching the flag tower's own count.

  forest   (BE-90) THE FOREST THEOREM, and the coordinator's reading (3).
           The fibre `F_Pi` has constant dimension 3 at every `Pi`
           (singular only at `Pi' = Pi`); path bases built BY the tower;
           and the feared jump at `p_i = p_{i+1}` exhibited as a legal,
           full-rank point of the SAME component -- the jump is an artifact
           of splitting the flag into point-then-plane.

  tri      (BE-92) THE REDUCIBILITY CERTIFICATES.  On the triangle's good
           component the three planes COINCIDE identically; a constructed
           collinear witness is legal with three PAIRWISE DISTINCT planes,
           so it is not in that component's closure.  With the F13
           adversarial pair: the `U` gate REJECTS the witness, the bare
           legality test ACCEPTS it, and the generic control passes both.

  cross    CROSS-SAMPLER AGREEMENT with the landed `bdecor.flag_assignment`
           (the arc's own flag-base sampler, imported, not reimplemented) on
           the (BE-64)/(BE-66) battery pieces.

  validate reduced tiers of all five.

Every figure is exact Q (`fractions.Fraction`); no floating point.
"""

import collections
import itertools
import random
import sys
import time
from fractions import Fraction as F

import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank as rank_exact, nullspace, neighbors          # noqa: E402
from kbare_common import verts_of                                       # noqa: E402
from bimage import v4, pt_in                                            # noqa: E402
from gridcol import class_shape                                         # noqa: E402
from bdecor import (hubs_and_branches, hub_adjacency, girth,            # noqa: E402
                    flag_assignment, R_BATTERY, nested_piece)
from bpeel import SKELETONS, split_at_pair, constructed_tier            # noqa: E402
from cflank import length_tuples                                        # noqa: E402

SEED = 20260902


# ============================================================ the flag base
#
# The projective carrier is the arc's own (`bdecor`/`bimage`): a point is a
# nonzero 4-vector, a plane is a nonzero 4-covector `n`, and `p in pi` is
# `n . p = 0`.  This is `kbare_common.verify_pencil_witness`'s own reading of
# the pencil condition -- a nonzero common normal for `{p_z} u {p_w : w ~ z}`
# -- restricted to the hub set, which is exactly (BE-65)(i)'s base.

def dot4(a, b):
    return sum(a[k] * b[k] for k in range(4))


def base_legal(W, E, P, N):
    """(BE-65)(i)'s conditions verbatim: `p_z in pi_z`, and `p_{z'} in pi_z`
    AND `p_z in pi_{z'}` on every `B_real`-edge.  Nonzero normals asserted."""
    for z in W:
        assert any(t != 0 for t in N[z]), ('zero normal at', z)
        assert any(t != 0 for t in P[z]), ('zero point at', z)
        if dot4(N[z], P[z]) != 0:
            return False
    for (a, b) in E:
        if dot4(N[a], P[b]) != 0 or dot4(N[b], P[a]) != 0:
            return False
    return True


def star_rank(W, E, P, z, nb):
    """`r_z` = rank of `{p_z} u {p_w : w a B_real-neighbour of z}`.  The plane
    fibre at `z` is `P^{3 - r_z}`, nonempty iff `r_z <= 3`."""
    return rank_exact([P[z]] + [P[w] for w in sorted(nb[z], key=str)])


def in_Uo(W, E, P, nb):
    """The constant-fibre-dimension locus `U`: `r_z = min(1 + d_z, 3)` at every
    `z`, so the plane fibre at `z` is `P^{3 - r_z}` of the SMALLEST dimension
    it can have.  At `d_z = 2` this says `p_z, p_{z'}, p_{z''}` are NOT
    collinear -- exactly the hinge-coincidence half of the arc's genericity
    proviso `G` (`binduc.assert_generic_star`), and Sec.(K-chart)'s `U_H` at a
    hub; at `d_z >= 3` it says the `1 + d_z` points span a plane EXACTLY, so
    `pi_z` is unique."""
    return all(star_rank(W, E, P, z, nb) == min(1 + len(nb[z]), 3) for z in W)


def jac_rank(W, E, P, N):
    """Rank of the Jacobian of the `|W| + 2|E|` bilinear equations cutting the
    AFFINE CONE over the base out of `(K^4)^W x (K^4)^W`.  Full rank
    `|W| + 2|E|` certifies a smooth point of a component of the expected
    dimension `7|W| - 2|E|` (cone) = `5|W| - 2|E|` (flags)."""
    idx = {z: i for i, z in enumerate(W)}
    n = len(W)
    rows = []

    def row(pblocks, nblocks):
        r = [F(0)] * (8 * n)
        for z, vec in pblocks:
            b = 4 * idx[z]
            for k in range(4):
                r[b + k] += vec[k]
        for z, vec in nblocks:
            b = 4 * n + 4 * idx[z]
            for k in range(4):
                r[b + k] += vec[k]
        return r

    for z in W:
        rows.append(row([(z, N[z])], [(z, P[z])]))
    for (a, b) in E:
        for (z, w) in ((a, b), (b, a)):
            rows.append(row([(w, N[z])], [(z, P[w])]))
    return rank_exact(rows)


def flag_dim(W, E, jr):
    """Cone tangent dimension minus the two scalings per vertex."""
    return 8 * len(W) - jr - 2 * len(W)


def expected_flag_dim(W, E):
    return 5 * len(W) - 2 * len(E)


def nb_of(W, E):
    nb = {z: set() for z in W}
    for (a, b) in E:
        nb[a].add(b)
        nb[b].add(a)
    return nb


# ------------------------------------------------- the two towers, as drawn

def draw_point_first(W, E, rng, s=20, tries=40):
    """(BE-91)'s tower: points FREE, then one normal per vertex in the plane
    space of its own closed `B_real`-star.  Valid when every `d_z <= 2` (then
    the point stage is unconstrained); asserts the fibre dimension it uses."""
    nb = nb_of(W, E)
    assert all(len(nb[z]) <= 2 for z in W), 'point-first tower needs Delta <= 2'
    for _ in range(tries):
        P = {z: v4(rng, s) for z in W}
        if not in_Uo(W, E, P, nb):
            continue
        N = {}
        for z in W:
            sp = nullspace([P[z]] + [P[w] for w in sorted(nb[z], key=str)])
            assert len(sp) == 3 - len(nb[z]), ('stage-2 fibre dimension', z)
            N[z] = pt_in(sp, rng, s)
        assert base_legal(W, E, P, N)
        return P, N
    return None, None


def fibre_F(Pi, rng, s=20, tries=40):
    """A point of `F_Pi = {(p, pi) in Fl : p in pi_0, p_0 in pi}` -- the flag
    tower's fibre.  Drawn as: `p` in the plane `pi_0` (2 params), then `pi`
    through `p_0` and `p` (a pencil, 1 param).  Total 3, at EVERY `Pi`."""
    p0, n0 = Pi
    sp = nullspace([n0])
    assert len(sp) == 3, 'the plane pi_0 is not a plane'
    for _ in range(tries):
        p = pt_in(sp, rng, s)
        pen = nullspace([p0, p])
        assert len(pen) == 4 - rank_exact([p0, p]), 'pencil dimension'
        n = pt_in(pen, rng, s)
        if any(t != 0 for t in n):
            return p, n
    return None, None


def draw_flag_tower(W, E, rng, s=20, order=None):
    """(BE-90)'s tower: a BFS order on a FOREST, each new vertex's WHOLE FLAG
    drawn in one stage from `F_Pi` of its (unique) placed neighbour."""
    nb = nb_of(W, E)
    P, N = {}, {}
    todo = list(order or sorted(W, key=str))
    placed = []
    while todo:
        # a vertex with at most one placed neighbour
        pick = None
        for z in todo:
            if len([w for w in nb[z] if w in P]) <= 1:
                pick = z
                break
        assert pick is not None, 'no forest order: some vertex has 2 placed nbrs'
        todo.remove(pick)
        anc = [w for w in nb[pick] if w in P]
        if not anc:
            p = v4(rng, s)
            n = pt_in(nullspace([p]), rng, s)
            P[pick], N[pick] = p, n
        else:
            p, n = fibre_F((P[anc[0]], N[anc[0]]), rng, s)
            P[pick], N[pick] = p, n
        placed.append(pick)
    assert base_legal(W, E, P, N)
    return P, N


def draw_coplanar(W, E, rng, s=20, tries=40):
    """All points generic in ONE plane, every plane THAT plane.  Legal for any
    `B`, and in `U` whenever no two `B`-neighbours of a vertex are collinear
    with it.  At a component of cyclomatic number `>= 2` this is not a special
    choice: `U`'s conditions at two degree-`>=3` vertices already force every
    point into a common plane (worked at the theta, `bbase.py dim`)."""
    for _ in range(tries):
        n = v4(rng, s)
        pl = nullspace([n])
        if len(pl) != 3:
            continue
        P = {z: pt_in(pl, rng, s) for z in W}
        N = {z: n for z in W}
        if base_legal(W, E, P, N) and in_Uo(W, E, P, nb_of(W, E)):
            return P, N
    return None, None


def flags_from_bdecor(W, E, rng, tries=40):
    """A base point drawn by the LANDED `bdecor.flag_assignment`, fed the graph
    `B` as a branch list of length-1 branches.  Imported, not reimplemented."""
    br = [(a, b, []) for (a, b) in E]
    for _ in range(tries):
        P, Bs = flag_assignment(list(W), br, rng)
        if P is None:
            continue
        N = {}
        ok = True
        for z in W:
            ann = nullspace(Bs[z])
            if len(ann) != 1:
                ok = False
                break
            N[z] = ann[0]
        if ok and base_legal(W, E, P, N):
            return P, N
    return None, None


# ============================================== `B_real` and its components

def components(W, ha):
    """Connected components of `B_real`, as `(vertices, edge count, max deg)`."""
    seen, out = set(), []
    for z in sorted(W, key=str):
        if z in seen:
            continue
        stack, C = [z], set()
        while stack:
            x = stack.pop()
            if x in C:
                continue
            C.add(x)
            stack.extend(ha[x] - C)
        seen |= C
        e = sum(len(ha[x] & C) for x in C) // 2
        out.append((sorted(C, key=str), e, max(len(ha[x] & C) for x in C)))
    return out


def piece_report(Ei, u, v):
    """`(W, B_real edges, hub adjacency, chart-hcard, transport residue)` for
    one piece.  The transport residue is the per-vertex excess of `B_real`'s
    degree over `Lambda(H)`'s -- job 2's quantity."""
    W, br = hubs_and_branches(Ei, u, v)
    ha = hub_adjacency(W, br)
    nbH = neighbors(Ei)
    real = {z for z in W if len(nbH[z]) >= 3}
    hcard = all(len([w for w in ha[z] if w in real]) <= 2 for z in real)
    resid = {}
    for z in W:
        lam = len([w for w in ha[z] if w in real])
        marked = len([w for w in ha[z] if w in ({u, v} - real)])
        resid[z] = (len(ha[z]), lam, marked, z in real)
    E = sorted({tuple(sorted((z, w), key=str)) for z in W for w in ha[z]})
    return W, E, ha, hcard, resid


# ==================================================== mode: census  (job 2)

def class_tier_K4():
    """EXHAUSTIVE: every K4-skeleton branch-length profile in `[1,6]^6` with
    sum 18 (the tightness equation for the K4 skeleton), certified by
    `gridcol.class_shape`."""
    sk = SKELETONS['K4']
    for prof in itertools.product(range(1, 7), repeat=len(sk)):
        if sum(prof) != 18:
            continue
        specs = [(a, b, L) for (a, b), L in zip(sk, prof)]
        E = class_shape(specs)
        if E is not None:
            yield ('K4' + str(prof), E)


def class_tier_sampled(name, nsamp, rng):
    """SAMPLED (cap disclosed): `nsamp` of the `Lambda != empty` length tuples
    of the prism / K33 skeleton at sum 24, certified by `class_shape`."""
    sk = SKELETONS[name]
    tup = [t for t in length_tuples(len(sk), 24, lo=1, hi=5) if any(L == 1 for L in t)]
    for prof in rng.sample(tup, min(nsamp, len(tup))):
        specs = [(a, b, L) for (a, b), L in zip(sk, prof)]
        E = class_shape(specs)
        if E is not None:
            yield (name + str(tuple(prof)), E, len(tup))


def _census_over(members, tag, out):
    for (label, E) in members:
        V = sorted(verts_of(E), key=str)
        out['members'] += 1
        out['girth'][girth(E)] += 1
        for (u, v) in itertools.combinations(V, 2):
            sp = split_at_pair(E, u, v)
            if sp is None:
                continue
            for Ei in (sp[1], sp[3]):
                W, BE, ha, hcard, resid = piece_report(Ei, u, v)
                out['pieces'] += 1
                if not hcard:
                    out['hcard_fail'] += 1
                # job 2's transport identity, asserted per vertex:
                #   d_z(B_real) = d_z(Lambda(H)) + |N_H(z) cap ({u,v} \ hubs)|
                # with `hcard` capping ONLY the first term at a hub, and the
                # marked pair's own degree capped by `deg_H <= 2`.
                for z in W:
                    tot, lam, marked, ishub = resid[z]
                    assert tot == lam + marked, (tag, 'transport residue', z, resid[z])
                    if ishub:
                        assert lam <= 2 or not hcard, (tag, 'hcard caps Lambda', z)
                    else:
                        assert tot <= 2, (tag, 'a non-hub of W has degree <= 2', z)
                out['maxdeg'][max((len(ha[z]) for z in W), default=0)] += 1
                forest = True
                for (C, e, md) in components(W, ha):
                    cyc = e - len(C) + 1
                    if cyc == 0:
                        out['comp']['tree(maxdeg %d)' % md] += 1
                    elif cyc == 1 and md == 2:
                        out['comp']['cycle %d' % len(C)] += 1
                        forest = False
                    elif cyc == 1:
                        out['comp']['unicyclic+trees'] += 1
                        forest = False
                    else:
                        out['comp']['cyclomatic %d' % cyc] += 1
                        forest = False
                out['forest' if forest else 'nonforest'] += 1


def run_census(seed=SEED, nsamp=400, quick=False):
    t0 = time.time()
    print('===== bbase census: `B_real` at the pieces, and job 2 =====')
    print(f'  seed {seed} (`random.Random`); counters printed sorted, '
          f'no PYTHONHASHSEED pin needed')
    rng = random.Random(seed)
    ok = True

    def fresh():
        return {'members': 0, 'pieces': 0, 'hcard_fail': 0, 'forest': 0,
                'nonforest': 0, 'maxdeg': collections.Counter(),
                'comp': collections.Counter(), 'girth': collections.Counter()}

    def show(name, out, denom):
        print(f'  {name}: {out["members"]} class members, {out["pieces"]} peel '
              f'pieces  [{denom}]')
        print(f'      girth of the member: {dict(sorted(out["girth"].items()))}')
        print(f'      chart-`hcard` failures at the piece: {out["hcard_fail"]}'
              f' / {out["pieces"]}')
        print(f'      max degree of `B_real`: {dict(sorted(out["maxdeg"].items()))}')
        print(f'      components: {dict(sorted(out["comp"].items()))}')
        print(f'      `B_real` a FOREST: {out["forest"]} / {out["pieces"]}'
              f'   (with a cycle: {out["nonforest"]})')

    tot_pieces = tot_forest = tot_hcf = tot_deg3 = 0

    o = fresh()
    mem = list(class_tier_K4())
    if quick:
        mem = mem[:120]
    _census_over(mem, 'K4', o)
    show('CLASS TIER, K4 skeleton',
         o, 'EXHAUSTIVE over [1,6]^6 at sum 18' + (' (first 120, quick)' if quick else ''))
    tot_pieces += o['pieces']; tot_forest += o['forest']; tot_hcf += o['hcard_fail']
    tot_deg3 += sum(c for d, c in o['maxdeg'].items() if d >= 3)

    for nm in ('prism', 'K33'):
        o2 = fresh()
        gen = list(class_tier_sampled(nm, 60 if quick else nsamp, rng))
        pool = gen[0][2] if gen else 0
        _census_over([(a, b) for (a, b, _c) in gen], nm, o2)
        show(f'CLASS TIER, {nm} skeleton', o2,
             f'SAMPLED {60 if quick else nsamp} of {pool} `Lambda != empty` '
             f'length tuples at sum 24 -- CAP, evidence about the sample only')
        tot_pieces += o2['pieces']; tot_forest += o2['forest']
        tot_hcf += o2['hcard_fail']
        tot_deg3 += sum(c for d, c in o2['maxdeg'].items() if d >= 3)

    print(f'  CLASS TOTAL: {tot_forest} / {tot_pieces} pieces have `B_real` a '
          f'FOREST; `hcard` failures {tot_hcf}; `Delta(B_real) >= 3` at '
          f'{tot_deg3} pieces; components of cyclomatic number >= 2: 0')
    ok &= (tot_hcf == 0) and (tot_forest == tot_pieces)

    # ---- the OFF-CLASS contrast: bpeel's own constructed tier
    o3 = fresh()
    o3['members'] = '(n/a)'
    for (tag, E, u, v, _d1, _d2, _f, _rn) in constructed_tier(
            maxlen=3, nsamp=40 if quick else 200):
        sp = split_at_pair(E, u, v)
        if sp is None:
            continue
        for Ei in (sp[1], sp[3]):
            W, BE, ha, hcard, resid = piece_report(Ei, u, v)
            o3['pieces'] += 1
            if not hcard:
                o3['hcard_fail'] += 1
            o3['maxdeg'][max((len(ha[z]) for z in W), default=0)] += 1
            forest = True
            for (C, e, md) in components(W, ha):
                cyc = e - len(C) + 1
                if cyc == 0:
                    o3['comp']['tree(maxdeg %d)' % md] += 1
                elif cyc == 1 and md == 2:
                    o3['comp']['cycle %d' % len(C)] += 1
                    forest = False
                elif cyc == 1:
                    o3['comp']['unicyclic+trees'] += 1
                    forest = False
                else:
                    o3['comp']['cyclomatic %d' % cyc] += 1
                    forest = False
            o3['forest' if forest else 'nonforest'] += 1
    print(f'  OFF-CLASS CONTRAST (`bpeel.constructed_tier`, NOT class-filtered):')
    print(f'      pieces {o3["pieces"]}, chart-`hcard` failures {o3["hcard_fail"]}')
    print(f'      max degree of `B_real`: {dict(sorted(o3["maxdeg"].items()))}')
    print(f'      components: {dict(sorted(o3["comp"].items()))}')
    print(f'      `B_real` a FOREST: {o3["forest"]} / {o3["pieces"]}')
    tri = o3['comp'].get('cycle 3', 0)
    resid = sum(c for k, c in o3['comp'].items() if k.startswith('cyclomatic'))
    print(f'      -- so the reducible shapes are REACHABLE off the class '
          f'({tri} triangle components) and UNREACHED on it;')
    print(f'      and the UNCOVERED shape -- a component of cyclomatic number '
          f'>= 2 --')
    print(f'      occurs {resid} times off the class and 0 times on it.')
    ok &= tri > 0

    print(f'  census {"GREEN" if ok else "RED"}, {time.time() - t0:.1f}s')
    return ok


# ======================================================= mode: dim  (BE-89)

def shape_menu():
    def path(m):
        return 'path%d' % m, list(range(1, m + 1)), [(i, i + 1) for i in range(1, m)]

    def cycle(m):
        return 'cycle%d' % m, list(range(1, m + 1)), [(i, i % m + 1) for i in range(1, m + 1)]

    out = [path(m) for m in range(1, 8)] + [cycle(m) for m in range(3, 9)]
    out.append(('star K1,3', [0, 1, 2, 3], [(0, 1), (0, 2), (0, 3)]))
    out.append(('star K1,4', [0, 1, 2, 3, 4], [(0, i) for i in (1, 2, 3, 4)]))
    out.append(('caterpillar', [0, 1, 2, 3, 4, 5],
                [(0, 1), (1, 2), (2, 3), (1, 4), (2, 5)]))
    out.append(('two paths (disjoint)', [1, 2, 3, 4, 5],
                [(1, 2), (2, 3), (4, 5)]))
    out.append(('tadpole (C4 + pendant)', [1, 2, 3, 4, 5],
                [(1, 2), (2, 3), (3, 4), (4, 1), (1, 5)]))
    out.append(('theta (cyclomatic 2)', [1, 2, 3, 4, 5],
                [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1), (2, 5)]))
    return out


def run_dim(seed=SEED):
    t0 = time.time()
    print('===== bbase dim: (BE-89), the complete-intersection dimension =====')
    print(f'  seed {seed}; exact Q throughout')
    rng = random.Random(seed)
    ok = True
    print('  shape                 |W| |E|  r_z          jac/eqs   flag dim  '
          'expected')
    for (name, W, E) in shape_menu():
        nb = nb_of(W, E)
        tree = len(E) == len(W) - len(components(W, {z: set(nb[z]) for z in W}))
        if all(len(nb[z]) <= 2 for z in W):
            P, N = draw_point_first(W, E, rng)
        elif tree:
            P, N = draw_flag_tower(W, E, rng)
        else:
            # cyclomatic number >= 2: neither tower reaches it, and the landed
            # `bdecor.flag_assignment` MISSES `U` here at 30/30 (see (BE-93)),
            # so the `U`-point is CONSTRUCTED -- at a theta, `U` forces every
            # point into one plane, and then every plane is that plane.
            P, N = draw_coplanar(W, E, rng)
        assert base_legal(W, E, P, N), name
        rz = [star_rank(W, E, P, z, nb) for z in W]
        jr = jac_rank(W, E, P, N)
        fd, exp = flag_dim(W, E, jr), expected_flag_dim(W, E)
        good = (jr == len(W) + 2 * len(E)) and fd == exp
        ok &= good
        print(f'  {name:<21} {len(W):>3} {len(E):>3}  {str(rz):<12} '
              f'{jr:>3}/{len(W) + 2 * len(E):<3}   {fd:>6}   {exp:>6}'
              f'   {"ok" if good else "MISMATCH"}')
    # a harness datum, reported not asserted: at the one cyclomatic->=2 shape,
    # the LANDED flag sampler never lands on the constant-rank locus.
    Wt = [1, 2, 3, 4, 5]
    Et = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1), (2, 5)]
    hit = miss = 0
    for _ in range(30):
        Pt, Nt = flags_from_bdecor(Wt, Et, rng)
        if Pt is None:
            continue
        assert base_legal(Wt, Et, Pt, Nt)
        if in_Uo(Wt, Et, Pt, nb_of(Wt, Et)):
            hit += 1
        else:
            miss += 1
    print(f'  harness datum (reported, not a claim): at the theta, '
          f'`bdecor.flag_assignment`')
    print(f'  lands OFF the constant-rank locus `U` at {miss} / {hit + miss} '
          f'draws -- every one legal, every')
    print(f'  one of tangent dimension {expected_flag_dim(Wt, Et) + 1} > '
          f'{expected_flag_dim(Wt, Et)}.  The `U`-point above is CONSTRUCTED.')
    print('  -- full Jacobian rank at a drawn point certifies a SMOOTH point of a')
    print('     component of dimension `5|W| - 2|E|`; the flag tower gives the')
    print('     same count as `5 + 3(m-1)` on a path and `3m` on a cycle.')
    print(f'  dim {"GREEN" if ok else "RED"}, {time.time() - t0:.1f}s')
    return ok


# ==================================================== mode: forest  (BE-90)

def run_forest(seed=SEED, ndraw=25):
    t0 = time.time()
    print('===== bbase forest: (BE-90), the flag tower and reading (3) =====')
    print(f'  seed {seed}; exact Q throughout')
    rng = random.Random(seed + 1)
    ok = True

    # (a) the fibre `F_Pi` has CONSTANT dimension 3 -- at generic AND at
    #     degenerate `Pi`, and its only singular point is `Pi' = Pi`.
    print('  (a) the fibre `F_Pi` = {(p,pi) in Fl : p in pi_0, p_0 in pi}:')
    W2, E2 = [1, 2], [(1, 2)]
    bad = 0
    for i in range(ndraw):
        p0 = v4(rng)
        n0 = pt_in(nullspace([p0]), rng)
        p, n = fibre_F((p0, n0), rng)
        P, N = {1: p0, 2: p}, {1: n0, 2: n}
        assert base_legal(W2, E2, P, N)
        jr = jac_rank(W2, E2, P, N)
        if flag_dim(W2, E2, jr) != expected_flag_dim(W2, E2):
            bad += 1
    print(f'      {ndraw - bad} / {ndraw} drawn fibre points are SMOOTH of flag '
          f'dimension {expected_flag_dim(W2, E2)} (= 5 + 3)')
    ok &= bad == 0
    # the one singular point, constructed: Pi' = Pi
    p0 = v4(rng)
    n0 = pt_in(nullspace([p0]), rng)
    Ps, Ns = {1: p0, 2: p0}, {1: n0, 2: n0}
    assert base_legal(W2, E2, Ps, Ns), 'Pi = Pi is a legal base point'
    jrs = jac_rank(W2, E2, Ps, Ns)
    print(f'      constructed `Pi_2 = Pi_1`: LEGAL, tangent flag dimension '
          f'{flag_dim(W2, E2, jrs)} > {expected_flag_dim(W2, E2)} -- the fibre\'s '
          f'only singular point, and it is IN the same irreducible `F_Pi`')
    ok &= flag_dim(W2, E2, jrs) > expected_flag_dim(W2, E2)

    # (b) path bases BUILT by the tower
    print('  (b) path bases built by the flag tower (one whole flag per stage):')
    for m in range(2, 8):
        W = list(range(1, m + 1))
        E = [(i, i + 1) for i in range(1, m)]
        P, N = draw_flag_tower(W, E, rng, order=W)
        assert base_legal(W, E, P, N)
        assert in_Uo(W, E, P, nb_of(W, E)), \
            'a generic tower draw must land in the constant-rank locus `U`'
        jr = jac_rank(W, E, P, N)
        fd, exp = flag_dim(W, E, jr), expected_flag_dim(W, E)
        good = fd == exp == 5 + 3 * (m - 1)
        ok &= good
        print(f'      path{m}: flag dim {fd} = 5 + 3*{m - 1} = {exp}  '
              f'{"ok" if good else "MISMATCH"}')

    # (c) READING (3): the feared jump at `p_i = p_{i+1}`
    print('  (c) reading (3): the coordinator\'s feared jump at `p_i = p_{i+1}`:')
    W3, E3 = [1, 2, 3], [(1, 2), (2, 3)]
    hits = 0
    for _ in range(ndraw):
        p1 = v4(rng)
        n1 = pt_in(nullspace([p1]), rng)
        p2 = p1[:]                       # the COINCIDENCE, constructed
        n2 = pt_in(nullspace([p1]), rng)  # any plane through p1 = p2
        if rank_exact([n1, n2]) != 2:
            continue
        p3 = pt_in(nullspace([n2]), rng)
        n3 = pt_in(nullspace([p2, p3]), rng)
        P, N = {1: p1, 2: p2, 3: p3}, {1: n1, 2: n2, 3: n3}
        if not base_legal(W3, E3, P, N):
            continue
        hits += 1
        jr = jac_rank(W3, E3, P, N)
        assert flag_dim(W3, E3, jr) == expected_flag_dim(W3, E3), \
            'a coincident-point base flag is a SMOOTH point of the same component'
    print(f'      {hits} constructed `p_1 = p_2` base flags: every one LEGAL and a')
    print(f'      SMOOTH point of the SAME `5|W| - 2|E| = '
          f'{expected_flag_dim(W3, E3)}` component -- NO fibre-dimension jump.')
    print('      The jump reading (3) feared is an artifact of splitting the flag')
    print('      into `p_{i+1}` (2 params) then `pi_{i+1}` (1); as ONE stage,')
    print('      `F_Pi` is irreducible of dimension 3 at every `Pi`.')
    ok &= hits > 0

    print(f'  forest {"GREEN" if ok else "RED"}, {time.time() - t0:.1f}s')
    return ok


# ======================================================= mode: tri  (BE-92)

def collinear_witness(m, rng, s=9):
    """A base point of `Base(C_m)` with all `m` points on ONE line and the
    planes free in that line's pencil -- the degenerate stratum, of cone
    dimension `4 + 2m` against the good component's `4m`."""
    x, y = v4(rng, s), v4(rng, s)
    while rank_exact([x, y]) != 2:
        y = v4(rng, s)
    W = list(range(1, m + 1))
    E = [(i, i % m + 1) for i in range(1, m + 1)]
    P = {}
    for z in W:
        a, b = F(rng.randint(-s, s)), F(rng.randint(-s, s))
        while a == 0 and b == 0:
            a, b = F(rng.randint(-s, s)), F(rng.randint(-s, s))
        P[z] = [a * x[k] + b * y[k] for k in range(4)]
    pen = nullspace([x, y])            # the pencil of planes through the line
    assert len(pen) == 2
    N = {z: pt_in(pen, rng, s) for z in W}
    return W, E, P, N


def run_tri(seed=SEED, ndraw=200):
    t0 = time.time()
    print('===== bbase tri: (BE-92), the short-cycle reducibility =====')
    print(f'  seed {seed}; exact Q throughout')
    rng = random.Random(seed + 2)
    ok = True

    # (a) the IDENTITY on the triangle's good component
    W, E = [1, 2, 3], [(1, 2), (2, 3), (1, 3)]
    nb = nb_of(W, E)
    same = drawn = 0
    for _ in range(ndraw):
        P = {z: v4(rng) for z in W}
        if not in_Uo(W, E, P, nb):
            continue
        drawn += 1
        sp = [nullspace([P[z]] + [P[w] for w in sorted(nb[z])]) for z in W]
        assert all(len(t) == 1 for t in sp), 'the plane at a triangle vertex is unique'
        if rank_exact([sp[0][0], sp[1][0], sp[2][0]]) == 1:
            same += 1
    print(f'  (a) on `U`, {same} / {drawn} triangle draws have all THREE planes')
    print(f'      EQUAL -- and it is an identity, not a coincidence: at a triangle')
    print(f'      `p_2 - p_1, p_3 - p_1` and `p_1 - p_2, p_3 - p_2` span the SAME')
    print(f'      plane, so `pi_1 = pi_2 = pi_3` wherever the fibre is a point.')
    ok &= (same == drawn and drawn > 0)

    # (b) the collinear witness -- OFF that component
    W, E, P, N = collinear_witness(3, rng)
    assert base_legal(W, E, P, N), 'the collinear witness must be a legal flag'
    distinct = all(rank_exact([N[a], N[b]]) == 2
                   for a, b in itertools.combinations(W, 2))
    jr = jac_rank(W, E, P, N)
    print(f'  (b) constructed COLLINEAR triangle witness: LEGAL, planes pairwise')
    print(f'      distinct = {distinct}, tangent flag dimension '
          f'{flag_dim(W, E, jr)} > {expected_flag_dim(W, E)}.')
    print(f'      Its three planes are DISTINCT, so by (a) it is not in the good')
    print(f'      component\'s closure: `Base(C_3)` is REDUCIBLE.')
    ok &= distinct and flag_dim(W, E, jr) > expected_flag_dim(W, E)

    # the stratum, as a family: every draw legal, dimension counted
    fam = 0
    for _ in range(40):
        Wc, Ec, Pc, Nc = collinear_witness(3, rng)
        if base_legal(Wc, Ec, Pc, Nc):
            fam += 1
    print(f'      the stratum as a FAMILY: {fam} / 40 draws legal.  Its cone')
    print(f'      dimension is 4 (the line `L` in Gr(2,4)) + 2m (points in `L`)')
    print(f'      + 2m (normals in `L^perp`) = 4 + 4m, i.e. FLAG dimension '
          f'4 + 2m = {4 + 2 * 3} at m = 3, against the good component\'s 3m = 9.')
    ok &= fam == 40

    # (c) F13 -- the adversarial pair the `U` gate must separate
    print('  (c) F13, the adversarial pair:')
    nbW = nb_of(W, E)
    print(f'      the collinear witness: bare legality ACCEPTS '
          f'({base_legal(W, E, P, N)}), the `U` gate REJECTS ({in_Uo(W, E, P, nbW)})')
    Wg, Eg = [1, 2, 3], [(1, 2), (2, 3), (1, 3)]
    Pg, Ng = draw_point_first(Wg, Eg, rng)
    print(f'      the generic control:   bare legality ACCEPTS '
          f'({base_legal(Wg, Eg, Pg, Ng)}), the `U` gate ACCEPTS '
          f'({in_Uo(Wg, Eg, Pg, nb_of(Wg, Eg))})')
    ok &= (not in_Uo(W, E, P, nbW)) and in_Uo(Wg, Eg, Pg, nb_of(Wg, Eg))

    # (d) the dimension table over cycle lengths
    print('  (d) cycle length m: good flag dim `3m` vs the collinear stratum\'s')
    print('      counted `4 + 2m`, each checked against the MEASURED tangent')
    print('      dimension at a constructed witness:')
    for m in range(3, 9):
        Wm = list(range(1, m + 1))
        Em = [(i, i % m + 1) for i in range(1, m + 1)]
        good = expected_flag_dim(Wm, Em)
        strat = 4 + 2 * m            # = (4 + 4m) cone params - 2m scalings
        Wc, Ec, Pc, Nc = collinear_witness(m, rng)
        assert base_legal(Wc, Ec, Pc, Nc), m
        tan = flag_dim(Wc, Ec, jac_rank(Wc, Ec, Pc, Nc))
        verdict = ('REDUCIBLE, the extra component is BIGGER' if strat > good else
                   'REDUCIBLE, two components of EQUAL dimension' if strat == good
                   else 'stratum strictly SMALLER than the good component')
        print(f'      m = {m}: good {good}, collinear stratum {strat} '
              f'(tangent {tan})   {verdict}')
        ok &= tan >= strat
    print('      girth >= 6 on the class forbids m = 3 and m = 4 outright, and a')
    print('      `B_real`-cycle IS a cycle of `H`, hence of `G`.')

    print(f'  tri {"GREEN" if ok else "RED"}, {time.time() - t0:.1f}s')
    return ok


# ============================================================ mode: cross

def run_cross(seed=SEED, ndraw=3):
    t0 = time.time()
    print('===== bbase cross: agreement with the landed `bdecor.flag_assignment` '
          '=====')
    print(f'  seed {seed}; exact Q throughout')
    rng = random.Random(seed + 3)
    ok = True
    pieces = [(nm, d['H'], d['u'], d['v']) for nm, d in R_BATTERY()]
    nd = nested_piece()
    pieces.append(('nested K4-in-K4', nd['H'], nd['u'], nd['v']))
    tot = good = 0
    for (nm, Ei, u, v) in pieces:
        W, E, ha, hcard, _res = piece_report(Ei, u, v)
        agree = 0
        for _ in range(ndraw):
            P, B = flag_assignment(W, [b for b in hubs_and_branches(Ei, u, v)[1]],
                                   rng)
            if P is None:
                continue
            # `B[z]` is the plane as a 3-dim SPAN; its normal is its annihilator
            N = {}
            for z in W:
                ann = nullspace(B[z])
                assert len(ann) == 1, ('the hub plane is not a plane', z)
                N[z] = ann[0]
            tot += 1
            if not base_legal(W, E, P, N):
                continue
            if not in_Uo(W, E, P, nb_of(W, E)):
                continue
            jr = jac_rank(W, E, P, N)
            if flag_dim(W, E, jr) != expected_flag_dim(W, E):
                continue
            agree += 1
            good += 1
        shape = ','.join(f'({len(C)}v,{e}e,D{md})' for C, e, md in
                         components(W, ha))
        print(f'  {nm[:44]:<44} |W|={len(W)} |E|={len(E)} {shape:<20} '
              f'{agree}/{ndraw}  dim {expected_flag_dim(W, E)}')
    print(f'  {good} / {tot} drawn flag assignments satisfy (BE-65)(i) verbatim, lie')
    print(f'  in `Base^o` and are SMOOTH points of the `5|W| - 2|E|` component.')
    ok &= good == tot and tot > 0
    print(f'  cross {"GREEN" if ok else "RED"}, {time.time() - t0:.1f}s')
    return ok


# ========================================================== mode: validate

def run_validate():
    t0 = time.time()
    print('===== bbase validate: reduced tiers of all five modes =====')
    ok = True
    ok &= run_census(quick=True)
    print()
    ok &= run_dim()
    print()
    ok &= run_forest(ndraw=12)
    print()
    ok &= run_tri(ndraw=60)
    print()
    ok &= run_cross(ndraw=2)
    print()
    print(f'===== validate {"GREEN" if ok else "RED"}, {time.time() - t0:.1f}s '
          f'=====')
    return ok


MODES = {'census': run_census, 'dim': run_dim, 'forest': run_forest,
         'tri': run_tri, 'cross': run_cross, 'validate': run_validate}

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if not args:
        print(__doc__)
        print('modes: ' + ' | '.join(MODES))
        sys.exit(0)
    for a in args:
        if a not in MODES:
            print(f'unknown mode {a!r}; modes: ' + ' | '.join(MODES))
            sys.exit(2)
        MODES[a]()
