"""
Phase 39 PENCIL, kernel (K), direction SIGZ (29th, eighth fan-out) -- the
`sigma > 0`-everywhere hunt at class shapes, and the degeneracy budget that
prices it.

Section: workbook `notes/Pencil-informal.md` section (K-out), labels
(OC-35)-(OC-40), Steps O31-O36.

WHAT IS NEW HERE (everything else is cited, not re-derived):

  (OC-35) the BRANCH-FLOW form of the pencil self-stress space, at an
          arbitrary (unslid) pencil placement.  A self-stress of a subgraph
          `F` with min degree >= 2 is exactly an assignment of one covector
          `psi_Q` per TOPOLOGICAL branch `Q` of `F`, lying in the perp of that
          branch's chain span `S_Q`, with Kirchhoff's law at every node of
          `F`'s topological reduction `F*`.  This is the unslid analogue of
          section (K-pure)'s limit-carrier stress form (`R_P := S_P^{perp_B}`,
          available bars); the difference is that there `S_P` is the SLIDE
          LIMIT chain span and here it is the actual one, so the statement
          applies on the pencil chart itself.
          Convention note: this harness's `pencil_escape.build_rigidity` uses
          the EUCLIDEAN perp of the hinge extensor, section (K-pure) the KLEIN
          perp.  They differ by one Hodge star, which is an isomorphism
          commuting with Kirchhoff, so every rank/dimension below is the same
          in either convention.  We use the Euclidean one throughout.

  (OC-36) the DEGENERACY-BUDGET identity.  With
          `delta^geo_Q := min(ell_Q, 6) - dim S_Q >= 0` the chain-span
          deficiency, `rho_F := 6(#nodes - 1) - rank(Kirchhoff) >= 0` the
          Kirchhoff-rank deficiency and
              slack(F) := sum_Q min(ell_Q, 6) - 6 c(F)
                        = 6(#nodes - 1) - sum_Q (6 - ell_Q)^+ ,
              corank R(F) = sum_Q delta^geo_Q + rho_F - slack(F) ,
          an identity at EVERY pencil placement.  (Equivalently, with
          `f(V(F)) = 6c(F) - |E(F)|` and the un-normalized
          `delta_Q := ell_Q - dim S_Q`,
          `corank R(F) = f(V(F)) + sum delta_Q + rho_F`.)

  (OC-37) the CLASS-SHAPE STRESS FLOOR.  At a class shape (tight, def = 0,
          `hnoRigid`), `slack(F) >= 0` for every min-degree->=2 subgraph
          `F` of `H`, with equality IFF `F`'s topological reduction has ONE
          node -- i.e. iff `F` is a cycle, or a bouquet of cycles through a
          single body.  Consequently a self-stress of `F` needs
              sum_Q delta^geo_Q + rho_F >= slack(F) + 1 ,
          which is `>= 1` for a cycle/bouquet and `>= 2` for EVERY other
          topology, thetas included.  So NO `H`-supported self-stress at a
          class shape is combinatorially forced: `{sigma = 0} = empty`
          cannot be certified by a count, and the counting route to a
          disproof of `hK` is DEAD.  Proof input: section (K-Lambda)
          (Lambda-4)(iii) (cited) applied to the short-path sub-multigraph.

  (OC-38) `P21`'s recorded mechanism, ledgered and LOCATED.  `P21` FAILS
          `hnoRigid` (a (K-res) residual, section (K-pure) P4/P7) -- every
          figure about it here carries that qualifier.  Its theta support has
          `slack = 0` at TWO nodes, which (OC-37) forbids at a class shape,
          and its `sigma = 1` decomposes as
          `(slack, sum delta^geo, rho) = (0, 1, 0)`: ONE unit of chain-span
          drop on the length-6 topological path.  A class-shape theta needs
          2.  The mechanism is quantitatively ONE UNIT SHORT of crossing
          into `hK`'s habitat.
          AND: on the landed window (`G''`-chart seeds 101..140, target rank
          required) the five sigma-jump seeds are EXACTLY the five where
          `localtest.plane_basis` degenerates at hub `c` -- SET EQUALITY, so
          the exhibited drop is the coincident-hinge-pair
          `C(c, x) = C(c, y)` that README section 4 convention 1 /
          *Harness debt* item 4 / (OC-7) name.  Under `repin.star_generic`,
          360 gate-accepted seeds give `sigma = 0` at every one.  The five
          jump points are still LEGAL chart points
          (`flanks.nondeg_conjuncts` green at all five), so
          `{sigma = 0}` IS a proper open at `P21` -- but the "5 of 35, so
          the complement is not thin" READING is refuted: the complement
          there is the sampler's coincidence locus.

  (OC-39) the hunt's verdict: `{sigma = 0} != empty` carries an exact-Q
          full-row-rank certificate at 3368 of 3368 class (shape, split)
          pairs over the EXHAUSTIVE `G* = K4` stratum plus the named
          habitats -- and by (OC-24)(i) + section (K-chart) (CH-1)(a) ONE
          such point is a complete certificate, so these are per-pair
          PROOFS that `hK` is not disproved there, not a tally.  NO HIT.

  (OC-40) what a hit would now have to look like, and the one named
          geometric input that is measured rather than proved.

Drivers:
    python3 notes/scripts/w4/sigz.py --reduce    # (OC-35)/(OC-36) identity
    python3 notes/scripts/w4/sigz.py --spans     # chain-span genericity
    python3 notes/scripts/w4/sigz.py --budget    # (Lambda-4)(iii) on the pool
    python3 notes/scripts/w4/sigz.py --slack     # (OC-37), the forced-stress
                                                 #   search -- ENUMERATES
    python3 notes/scripts/w4/sigz.py --theta     # (OC-37) at c(F*) <= 2
    python3 notes/scripts/w4/sigz.py --p21       # (OC-38) the P21 ledger
    python3 notes/scripts/w4/sigz.py --hunt      # the sigma > 0 hunt itself
    python3 notes/scripts/w4/sigz.py --validate  # all seven

`--validate` does NOT fit a 600 s foreground budget (measured ~700-750 s
over two runs), so it
is run as the TWO-invocation split below (`notes/scripts/README.md`'s
`flanks --limit` / `yloc --coll` precedent; recorded so a successor plans
around it rather than rediscovering it):

    python3 notes/scripts/w4/sigz.py --reduce --spans --budget --slack \
        --theta --p21                          # measured 239 s / 292 s
    python3 notes/scripts/w4/sigz.py --hunt    # measured 454 s / 455 s

Discipline (`notes/scripts/README.md` section 4): exact Fraction arithmetic
only; every sampled placement gated by `repin.star_generic` (the composite
guard -- NOT `star_span_ranks` alone); every sampled span asserts its
dimension; every rng seeded from a printed literal.
"""
import itertools
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, wedge2, hat, neighbors
from kbare_common import verts_of
from pencil_escape import build_rigidity
from nogood_subdiv import deficiency, branch_decomposition
from dominance import branch_pmap
from widened import place_pencil_general, orient, removeV, splitOff
from repin import star_generic, span_basis, coincident_hinges
from pitch import paths_graph
from kslide import no_rigid_branch_union
from kslidecomb import shape_data, shape_ok
from flanks import P21_SPECS
from ltwo import branch_subsets
from outer import split_data, eligible_splits, sweep_shapes

SEED = 20260819


# ---------------- topological reduction ------------------------------------

def topo_reduce(edges):
    """Topological reduction of a min-degree->=2 graph.

    Returns `(nodes, paths)` with `nodes` the sorted list of degree->=3
    vertices and `paths` a list of `(start, end, [edge, ...])` -- the maximal
    paths between nodes, each edge listed in walk order.  A component with no
    degree->=3 vertex is a cycle and comes back as one closed path
    `(v, v, edges)` with `v` its smallest vertex; `nodes` then contains `v`.

    Deliberately NOT `nogood_subdiv.branch_decomposition`: that one reduces
    `G` at its hubs (degree >= 3 in `G`), which is a different reduction for a
    SUBGRAPH `F` -- a `G`-hub can have `F`-degree 2, and then it must be
    absorbed into a longer topological path.  Divergences row candidate.
    """
    nb = neighbors(edges)
    V = sorted(nb, key=str)
    deg = {v: len(nb[v]) for v in V}
    assert all(deg[v] >= 2 for v in V), "topo_reduce wants min degree >= 2"
    nodes = [v for v in V if deg[v] >= 3]
    paths, used = [], set()

    def ekey(a, b):
        return (a, b) if str(a) <= str(b) else (b, a)

    for h in nodes:
        for first in sorted(nb[h], key=str):
            if ekey(h, first) in used:
                continue
            walk, prev, cur = [], h, first
            used.add(ekey(prev, cur))
            walk.append((prev, cur))
            while deg[cur] == 2:
                nxt = [y for y in nb[cur] if y != prev]
                assert len(nxt) == 1
                prev, cur = cur, nxt[0]
                used.add(ekey(prev, cur))
                walk.append((prev, cur))
            paths.append((h, cur, walk))
    # leftover components: pure cycles
    rest = [e for e in edges if ekey(*e) not in used]
    while rest:
        nb2 = neighbors(rest)
        start = min(nb2, key=str)
        walk, prev, cur = [], start, sorted(nb2[start], key=str)[0]
        used.add(ekey(prev, cur))
        walk.append((prev, cur))
        while cur != start:
            nxt = [y for y in nb2[cur] if y != prev]
            assert len(nxt) == 1
            prev, cur = cur, nxt[0]
            used.add(ekey(prev, cur))
            walk.append((prev, cur))
        nodes.append(start)
        paths.append((start, start, walk))
        rest = [e for e in rest if ekey(*e) not in used]
    return sorted(nodes, key=str), paths


def f_of(edges):
    """`f(V(F)) = 5|E| - 6(|V| - 1)` (Shared dictionary)."""
    return 5 * len(edges) - 6 * (len(verts_of(edges)) - 1)


# ---------------- the branch-flow stress system ----------------------------

def ekey(a, b):
    return (a, b) if str(a) <= str(b) else (b, a)


def hinge_lines(edges, placed):
    """`C_e = pt(u) ^ pt(w)` per edge, keyed orientation-free and asserted
    nonzero (README section 4 convention 1: a rank/dimension assert on every
    sampled object)."""
    C = {}
    for e in edges:
        Ce = wedge2(hat(placed[e[0]]), hat(placed[e[1]]))
        assert any(x != 0 for x in Ce), "degenerate hinge extensor"
        C[ekey(*e)] = Ce
    return C


def chain_span(walk, C):
    """`(dim S_Q, basis of S_Q^perp)` for one topological path."""
    lines = [C[ekey(a, b)] for (a, b) in walk]
    B = span_basis(lines)
    d = len(B)
    assert d == rank(lines), "chain-span basis disagrees with rank"
    per = nullspace(lines)          # Euclidean perp of the whole span
    assert len(per) == 6 - d, "perp dimension ledger broke"
    return d, per


def flow_system(edges, placed):
    """(OC-35): the Kirchhoff system on the branch perp spaces.

    Returns a dict with the corank, the per-path ledger, `rho`, and the
    (OC-36) decomposition, all exact.
    """
    C = hinge_lines(edges, placed)
    nodes, paths = topo_reduce(edges)
    cols, per_path = [], []
    for (h1, h2, walk) in paths:
        d, per = chain_span(walk, C)
        per_path.append((h1, h2, len(walk), d, len(per)))
        cols.append((h1, h2, per))
    nidx = {h: k for k, h in enumerate(nodes)}
    nvar = sum(len(per) for (_a, _b, per) in cols)
    rows = [[F(0)] * nvar for _ in range(6 * len(nodes))]
    col = 0
    for (h1, h2, per) in cols:
        for vec in per:
            for k in range(6):
                rows[6 * nidx[h1] + k][col] += vec[k]
                rows[6 * nidx[h2] + k][col] -= vec[k]
            col += 1
    rk = rank(rows) if nvar else 0
    corank = nvar - rk
    # (OC-36) ledger
    fF = f_of(edges)
    delta = sum(L - d for (_a, _b, L, d, _p) in per_path)
    rho = 6 * (len(nodes) - 1) - rk if nodes else -rk
    return {'corank': corank, 'paths': per_path, 'nodes': nodes,
            'nvar': nvar, 'rank': rk, 'f': fF, 'delta': delta, 'rho': rho}


def direct_corank(edges, placed):
    """corank of the full 5|E| x 6|V| rigidity matrix -- the ground truth."""
    V = sorted(verts_of(edges), key=str)
    rows, er, C, idx, n = build_rigidity(
        {'edges': list(edges), 'V': V, 'pt': placed})
    rk = rank(rows)
    return 5 * len(edges) - rk, rk, 6 * (n - 1)


# ---------------- shape pool ----------------------------------------------

def _specs_graph(specs):
    return paths_graph([specs[0][2]], specs[1:])


def hub_specs(edges):
    """`(n, E0, lens)` -- the hub multigraph of a subdivision, read off
    `nogood_subdiv.branch_decomposition` rather than from a spec literal, so
    the pool can carry graphs whose canonical home hands over an edge list."""
    hubs, branches = branch_decomposition(edges)
    if branches is None:
        return None
    hl = sorted(hubs, key=str)
    ren = {h: k for k, h in enumerate(hl)}
    E0 = [(ren[h1], ren[h2]) for (h1, h2, _i) in branches]
    lens = [len(i) + 1 for (_a, _b, i) in branches]
    return len(hl), E0, lens


def named_pool():
    """The arc's named class habitats, from their canonical homes.  Each is
    re-certified here as tight ^ def = 0 ^ hnoRigid before it enters the pool
    (the class predicate, `kslidecomb.shape_ok`'s three clauses)."""
    from pitch import theta_edges, nt21
    from dominance import nt16k5, branch_pmap
    from pencil_escape import double_subdivide, K4, K5_minus_matching
    out = [('theta(3,4,5)', theta_edges([3, 4, 5])),
           ('NT21', nt21()[0]),
           ('NT16k5', nt16k5()[0]),
           ('K4dbl', double_subdivide(K4())[0]),
           ('K5-M dbl', double_subdivide(K5_minus_matching())[0])]
    keep = []
    for name, E in out:
        if 5 * len(E) != 6 * (len(verts_of(E)) - 1):
            continue
        if deficiency(E) != 0:
            continue
        if hub_specs(E) is None:
            continue
        if not no_rigid_branch_union(E, branch_pmap(E)):
            continue
        keep.append((name, E))
    return keep


def k4_stratum(cap=None):
    """The exhaustive `G* = K4` class stratum: lengths in {1..5}^6 with
    `sum = 18` and a length-3 branch to be the split, filtered by
    `kslidecomb.shape_ok` (tight ^ def = 0 ^ hnoRigid at branch granularity).
    Enumeration order is `itertools.product`, hence deterministic."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    out = []
    for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
        if sum(lens) != 18 or 3 not in lens:
            continue
        k = lens.index(3)
        order = [k] + [i for i in range(6) if i != k]
        specs = [(K4[i][0], K4[i][1], lens[i]) for i in order]
        # relabel so the split branch is (0, 1, 3)
        b, c = K4[k]
        ren = {b: 0, c: 1}
        nxt = 2
        for v in range(4):
            if v not in ren:
                ren[v] = nxt
                nxt += 1
        specs = [(ren[u], ren[w], L) for (u, w, L) in specs]
        if shape_ok(specs) is None:
            continue
        out.append((f'K4{lens}', specs))
        if cap is not None and len(out) >= cap:
            break
    return out


def shape_pool(cap_k4=None, named=True):
    """`(name, edges)` for every class shape in the pool: the arc's named
    habitats plus the exhaustive `G* = K4` stratum (capped only where a mode
    says so, and the cap is always printed)."""
    pool = list(named_pool()) if named else []
    for name, specs in k4_stratum(cap_k4):
        pool.append((name, _specs_graph(specs)[0]))
    return pool


def sample_chart(edges, seed, tries=40):
    """A `star_generic`-gated exact-Q pencil placement, or None."""
    for t in range(tries):
        out = place_pencil_general(edges, random.Random(seed + 7919 * t))
        if out is None:
            continue
        placed = out[0]
        if not star_generic(edges, placed):
            continue
        return placed, seed + 7919 * t
    return None


# ---------------- mode: --reduce ------------------------------------------

def sub_supports(edges, hubs, branches, maxmask=1 << 14):
    """Every branch-subset subgraph of min degree >= 2, as an edge list."""
    out = []
    n = len(branches)
    assert (1 << n) <= maxmask, f'{n} branches: too many subsets'
    for mask in range(1, 1 << n):
        sel = [branches[i] for i in range(n) if mask >> i & 1]
        E = []
        for (h1, h2, interior) in sel:
            chain = [h1] + interior + [h2]
            E += [(chain[i], chain[i + 1]) for i in range(len(chain) - 1)]
        nb = neighbors(E)
        if any(len(nb[v]) < 2 for v in nb):
            continue
        out.append(E)
    return out


def mode_reduce():
    print("== (OC-35)/(OC-36): the branch-flow reduction, against the direct "
          "rigidity-matrix corank ==")
    print(f"   rng: random.Random({SEED} + 7919*t), gate repin.star_generic")
    print("   per (shape, seed, support F): corank R(F) direct == flow, and "
          "== f(V(F)) + sum delta + rho")
    pool = shape_pool(cap_k4=6)
    tot, bad, wit = 0, 0, 0
    for (name, edges) in pool:
        hubs, branches = branch_decomposition(edges)
        for si, seed in enumerate((SEED, SEED + 101)):
            got = sample_chart(edges, seed + 13 * len(name))
            if got is None:
                continue
            placed, used = got
            for E in sub_supports(edges, hubs, branches):
                tot += 1
                d, rk, tgt = direct_corank(E, placed)
                fl = flow_system(E, placed)
                if d != fl['corank']:
                    bad += 1
                    print(f"   MISMATCH {name} seed {used}: direct {d} "
                          f"flow {fl['corank']} on {len(E)} edges")
                    continue
                led = fl['f'] + fl['delta'] + fl['rho']
                if led != d:
                    bad += 1
                    print(f"   LEDGER BREAK {name} seed {used}: {d} vs "
                          f"f={fl['f']} delta={fl['delta']} rho={fl['rho']}")
                    continue
                if d > 0:
                    wit += 1
    # the corank > 0 direction: P21 at a plane_basis-degenerate seed, the
    # arc's one exhibited sigma-jump.  `hnoRigid` FAILS at P21 -- it is a
    # (K-res) residual, not a class member -- and that is exactly why it can
    # carry an f = 0 support at all.
    edges, pmap, v, a, b, c, Gp, Hed, theta = p21_setup()
    nz = 0
    for sd in (101, 111, 128, 136, 138):
        out = place_pencil_general(Gp, random.Random(sd))
        placed = out[0]
        for E in (theta, Hed):
            tot += 1
            d, rk, _t = direct_corank(E, placed)
            fl = flow_system(E, placed)
            if d != fl['corank'] or d != fl['f'] + fl['delta'] + fl['rho']:
                bad += 1
                print(f"   P21 LEDGER BREAK seed {sd}: {d} vs {fl}")
            if d > 0:
                wit += 1
                nz += 1
    print(f"   plus the P21 corank > 0 leg (hnoRigid FALSE there): "
          f"{nz} of 10 (support, seed) pairs carry a stress, and the "
          f"ledger holds at every one")
    print(f"   supports tested: {tot}; mismatches: {bad}; "
          f"supports with a stress: {wit}")
    assert bad == 0, "the branch-flow reduction or the ledger FAILED"
    print("   (OC-35) and (OC-36)'s identity: OK at every support tested")
    return tot


# ---------------- mode: --spans ------------------------------------------

def mode_spans():
    print("== chain-span genericity: dim S_Q for every topological path ==")
    print("   claim under test: at a star_generic chart point of a class "
          "shape, every topological path of length L has dim S = min(L, 6)")
    pool = shape_pool(cap_k4=12)
    seen, drops, byL = 0, [], {}
    for (name, edges) in pool:
        hubs, branches = branch_decomposition(edges)
        got = sample_chart(edges, SEED + 31 * len(edges))
        if got is None:
            print(f"   {name}: no gated placement")
            continue
        placed, used = got
        C = hinge_lines(edges, placed)
        # every topological path arising in ANY branch-subset support,
        # deduplicated by its edge set (a path is measured once per shape)
        done = set()
        for E in sub_supports(edges, hubs, branches):
            nodes, paths = topo_reduce(E)
            for (h1, h2, walk) in paths:
                tag = frozenset(ekey(*e) for e in walk)
                if tag in done:
                    continue
                done.add(tag)
                d, per = chain_span(walk, C)
                L = len(walk)
                seen += 1
                byL.setdefault(L, {}).setdefault(d, 0)
                byL[L][d] += 1
                if d != min(L, 6):
                    drops.append((name, used, L, d))
    print(f"   topological paths measured: {seen}")
    for L in sorted(byL):
        print(f"     L = {L}: " + ", ".join(
            f"dim {d} x{byL[L][d]}" for d in sorted(byL[L])))
    print(f"   paths with dim S < min(L, 6): {len(drops)}")
    for row in drops[:12]:
        print(f"     DROP {row}")
    return len(drops), seen


# ---------------- mode: --budget -----------------------------------------

def mode_budget():
    print("== (OC-36) combinatorial half: f(V(F)) <= -1 at every proper "
          "branch subset of a class shape ==")
    print("   source of the inequality: section (K-Lambda) (Lambda-4)(iii), "
          "cited, not re-derived; this mode ASSERTS it on the pool and reads "
          "off the budget it forces")
    pool = shape_pool(cap_k4=None)
    worst, tot, shapes = -10 ** 9, 0, 0
    fsplit = set()
    for (name, edges) in pool:
        shapes += 1
        n, E0, lens = hub_specs(edges)
        subs = branch_subsets(n, E0)
        for (Fidx, thr) in subs:
            if len(Fidx) == len(E0):
                continue
            s = sum(lens[i] for i in Fidx)
            fF = thr - s          # f(V(F)) = 6 c(F) - sum_F ell
            tot += 1
            assert fF <= -1, f'{name}: f = {fF} at {Fidx} -- (Lambda-4)(iii)!'
            worst = max(worst, fF)
        # the split complement H = G - int(beta): f = -3
        for v in eligible_splits(edges):
            sd = split_data(edges, v)
            if sd is None:
                continue
            a, b, c, Gp, Hed = sd
            fsplit.add(f_of(Hed))
    print(f"   class shapes: {shapes}; proper cyclic branch subsets: {tot}")
    print(f"   max f(V(F)) over all of them: {worst}  (must be <= -1)")
    print(f"   f(V(H)) over every eligible split of every shape: "
          f"{sorted(fsplit)}  (must be [-3])")
    assert worst <= -1
    assert fsplit == {-3}, fsplit
    print("   => every H-supported stress at a class shape needs "
          "sum delta + rho >= 1 - f(V(F)) >= 2")
    return shapes, tot


# ---------------- mode: --theta ------------------------------------------

def cycle_rank(E):
    return len(E) - len(verts_of(E)) + 1


def mode_theta():
    print("== (OC-37): the c(F*) <= 2 support census inside H, per class "
          "shape and per eligible split ==")
    print("   for each support: topology, path lengths, f, the budget "
          "1 - f it needs, and the measured corank at a gated chart point")
    pool = shape_pool(cap_k4=40)
    tab, tot, hits = {}, 0, []
    rho_ok, minlam = True, 10 ** 9
    for (name, edges) in pool:
        got = sample_chart(edges, SEED + 17 * len(edges))
        if got is None:
            continue
        placed, used = got
        hubs, branches = branch_decomposition(edges)
        for v in eligible_splits(edges):
            sd = split_data(edges, v)
            if sd is None:
                continue
            a, b, c, Gp, Hed = sd
            hubsH, brH = branch_decomposition(Hed)
            if brH is None:
                continue
            for E in sub_supports(Hed, hubsH, brH):
                cr = cycle_rank(E)
                if cr < 1 or cr > 2:
                    continue
                nodes, paths = topo_reduce(E)
                loops = sum(1 for (h1, h2, _w) in paths if h1 == h2)
                if cr == 1:
                    shape = 'cycle'
                elif loops == 0 and len(nodes) == 2 and len(paths) == 3:
                    shape = 'theta'
                elif loops == 2 and len(nodes) == 1:
                    shape = 'fig8'
                elif loops == 2:
                    shape = 'dumbbell'
                else:
                    shape = f'other(n={len(nodes)},p={len(paths)})'
                fl = flow_system(E, placed)
                tot += 1
                lens = tuple(sorted(L for (_a, _b, L, _d, _p) in fl['paths']))
                key = (shape, cr, fl['f'], lens if shape == 'theta' else None)
                tab[key] = tab.get(key, 0) + 1
                if shape == 'theta':
                    lam = sum(min(L, 6) for L in lens)
                    minlam = min(minlam, lam)
                    if fl['rho'] != lam - 12:
                        rho_ok = False
                if fl['corank'] > 0:
                    hits.append((name, used, shape, fl))
    print(f"   c <= 2 supports measured: {tot}")
    for key in sorted(tab, key=lambda k: (k[1], k[0], k[2], k[3] or ())):
        shape, cr, fF, lens = key
        tag = f'  lengths {lens}' if lens else ''
        print(f"     {shape:9s} c={cr}  f={fF:3d}  needs sum delta + rho >= "
              f"{1 - fF}   count {tab[key]}{tag}")
    print(f"   theta rho check: rho == sum min(ell_i, 6) - 12 at every "
          f"theta support?  {'YES' if rho_ok else 'NO'}  "
          f"(that equality IS the generic triple-intersection dimension "
          f"dim(S_1 ^ S_2 ^ S_3), so corank 0 follows from it)")
    print(f"   min over theta supports of sum min(ell_i, 6): {minlam} "
          f"(the (OC-37) bound proves >= 13 class-wide)")
    print(f"   supports with corank > 0: {len(hits)}")
    for (name, used, shape, fl) in hits[:10]:
        print(f"     STRESS {name} seed {used} {shape}: corank "
              f"{fl['corank']} = f {fl['f']} + delta {fl['delta']} + rho "
              f"{fl['rho']}")
    return tot, len(hits)


# ---------------- mode: --slack ------------------------------------------

def slack_of(E):
    """`(slack, n, lengths)` for a min-degree->=2 subgraph `E`.

    `slack(F) := sum_Q min(ell_Q, 6) - 6 c(F) = 6(n - 1) - sum_Q (6-ell_Q)^+`,
    over the TOPOLOGICAL paths of `F`.  `corank R(F) >= -slack(F)` at EVERY
    pencil placement, unconditionally -- so `slack < 0` anywhere inside `H`
    would be a combinatorially FORCED self-stress, hence `{sigma = 0} =
    empty`, hence `hK` FALSE at that shape ((OC-24)(ii)).  (OC-37) proves
    `slack >= 0` at every class shape, with equality iff `n = 1`.
    """
    nodes, paths = topo_reduce(E)
    lens = [len(w) for (_a, _b, w) in paths]
    c = len(E) - len(verts_of(E)) + 1
    return sum(min(L, 6) for L in lens) - 6 * c, len(nodes), tuple(
        sorted(lens))


def mode_slack(cap5=150):
    print("== (OC-37): the class-shape stress FLOOR, enumerated ==")
    print("   headline sentence under test: at every class shape, every "
          "min-degree->=2 subgraph `F` of `H` has "
          "`slack(F) >= 0`, with equality IFF `F`'s topological reduction "
          "has ONE node (a cycle, or a bouquet of cycles through one body).")
    print("   `slack < 0` anywhere would be a combinatorially FORCED "
          "self-stress at every pencil placement -- a PENCIL event.  This "
          "mode is the search for one, and it ENUMERATES rather than "
          "samples: no rng, no placement, no cap on the supports.")
    rows = list(sweep_shapes(cap5=cap5))
    rows.append(('the exhaustive `G* = K4` class stratum '
                 '(kslidecomb.shape_ok, no length-4-companion filter)',
                 [(nm, _specs_graph(sp)[0]) for nm, sp in k4_stratum()]))
    rows.append(('the arc''s named class habitats', named_pool()))
    tot, shapes, neg, zero_bad = 0, 0, [], []
    dist, zn = {}, {}
    for (desc, sh) in rows:
        print(f"   pool row: {desc}  ({len(sh)} shapes)")
        for (label, edges) in sh:
            shapes += 1
            for v in eligible_splits(edges):
                sd = split_data(edges, v)
                if sd is None:
                    continue
                a, b, c, Gp, Hed = sd
                hubsH, brH = branch_decomposition(Hed)
                if brH is None:
                    continue
                for E in sub_supports(Hed, hubsH, brH):
                    sl, nn, lens = slack_of(E)
                    tot += 1
                    dist[sl] = dist.get(sl, 0) + 1
                    if sl < 0:
                        neg.append((label, v, lens, sl))
                    if sl == 0:
                        zn[nn] = zn.get(nn, 0) + 1
                        if nn != 1:
                            zero_bad.append((label, v, lens, nn))
    print(f"   class shapes: {shapes}; (support, split) instances "
          f"enumerated: {tot}")
    print("   slack distribution: " + ", ".join(
        f"{k}:{dist[k]}" for k in sorted(dist)))
    print(f"   supports with slack < 0 (a FORCED stress, i.e. a PENCIL "
          f"event): {len(neg)}")
    for row in neg[:10]:
        print(f"     FORCED {row}")
    print(f"   supports with slack == 0, by node count of `F*`: {zn}  "
          f"(the theorem says node count 1 only)")
    print(f"   slack == 0 with more than one node: {len(zero_bad)}")
    for row in zero_bad[:10]:
        print(f"     COUNTEREXAMPLE {row}")
    assert not neg, "a FORCED stress exists -- PENCIL event, stop and report"
    assert not zero_bad, "(OC-37)'s equality clause is FALSE"
    return shapes, tot, len(neg)


# ---------------- mode: --p21 --------------------------------------------

def p21_setup():
    edges, pmap = shape_data(P21_SPECS)
    v = pmap[0][1]
    a, b, c = orient(edges, v)
    Gp = splitOff(edges, v, a, b)
    Hed = removeV(removeV(edges, v), a)
    theta_pairs = {tuple(sorted(map(str, e)))
                   for k in (1, 2, 5, 6)
                   for e in zip(pmap[k], pmap[k][1:])}
    theta = [e for e in Hed
             if tuple(sorted(map(str, e))) in theta_pairs]
    return edges, pmap, v, a, b, c, Gp, Hed, theta


def mode_p21(window=range(101, 141), gcap=500, tr_sub=60):
    print("== (OC-38): `P21`'s sigma-jump stratum, ledgered and located ==")
    print("   `P21` FAILS `hnoRigid`: it is a (K-res) residual, NOT a tight "
          "class member (section (K-pure) P4/P7, section (K-out) "
          "(OC-28)(iv)).  EVERY figure in this mode carries that qualifier, "
          "because the whole question is whether the mechanism crosses into "
          "`hK`'s habitat.")
    edges, pmap, v, a, b, c, Gp, Hed, theta = p21_setup()
    nV = len(verts_of(edges))
    tight = (5 * len(edges) == 6 * (nV - 1))
    nr = no_rigid_branch_union(edges, branch_pmap(edges))
    print(f"   |V| = {nV}, |E| = {len(edges)}, tight = {tight}, "
          f"def = {deficiency(edges)}, hnoRigid = {nr}")
    assert tight and deficiency(edges) == 0 and not nr, "P21 spec changed"
    print(f"   split v = {v}, a = {a}, b = {b}, c = {c}; "
          f"|E(H)| = {len(Hed)}, f(V(H)) = {f_of(Hed)}")
    print(f"   the recorded theta support (branches 12, 13, 23a, 23b): "
          f"{len(theta)} edges, f(V(F)) = {f_of(theta)}   <-- f = 0 is "
          f"EXACTLY what (Lambda-4)(iii) forbids in the class")
    nGp = len(verts_of(Gp))
    tgt = 6 * (nGp - 1) - deficiency(Gp)
    print()
    print(f"   (a) the landed window, seeds {window.start}..{window.stop - 1} "
          f"of `G''`'s chart (`widened.place_pencil_general`, the sampler "
          f"section (K-flank) F5(d) used), target rank of `G''` required:")
    rows, jump, degen = [], [], []
    for sd in window:
        out = place_pencil_general(Gp, random.Random(sd))
        if out is None:
            continue
        placed, pt, nrm, hubs, nb = out
        V = sorted(verts_of(Gp), key=str)
        R, _er, _C, _i, _n = build_rigidity(
            {'edges': Gp, 'V': V, 'pt': placed})
        if rank(R) != tgt:
            continue
        sig, rk, _t = direct_corank(Hed, placed)
        assert rk == 5 * len(Hed) - sig
        coinc = coincident_hinges(Gp, placed)
        zn = sorted(h for h in hubs if nrm[h][2] == 0)
        rows.append((sd, sig, zn, len(coinc)))
        if sig > 0:
            jump.append(sd)
            fl = flow_system(theta, placed)
            flH = flow_system(Hed, placed)
            assert fl['corank'] == direct_corank(theta, placed)[0]
            print(f"      seed {sd}: sigma = {sig}; theta ledger corank "
                  f"{fl['corank']} = f {fl['f']} + delta {fl['delta']} + rho "
                  f"{fl['rho']}, paths (L, dim S) = "
                  f"{[(L, d) for (_a, _b, L, d, _p) in fl['paths']]}")
            print(f"                 H ledger corank {flH['corank']} = f "
                  f"{flH['f']} + delta {flH['delta']} + rho {flH['rho']}, "
                  f"paths {[(L, d) for (_a, _b, L, d, _p) in flH['paths']]}")
            print(f"                 coincident hinge pairs: {coinc}; "
                  f"hubs with nrm[h][2] == 0: {zn}")
        if c in zn:
            degen.append(sd)
    print(f"      valid (target-rank) seeds in the window: {len(rows)}; "
          f"sigma > 0 at {len(jump)} of them: {jump}")
    print(f"      seeds where `localtest.plane_basis` DEGENERATES at hub c "
          f"(nrm[c][2] == 0): {degen}")
    same = (sorted(jump) == sorted(degen))
    print(f"      SET EQUALITY jump == plane_basis-degenerate-at-c: {same}")
    print()
    print(f"   (b) the same shape under the composite genericity gate "
          f"`repin.star_generic` (cap {gcap} seeds, CAP DISCLOSED; a witness "
          f"count, never a rate).  Target rank of `G''` is NOT imposed here "
          f"-- `sigma = corank R(H)` is defined at every legal chart point "
          f"((OC-23)) -- but it IS reported for the first {tr_sub}:")
    ok, jump2, tried, tr = 0, [], 0, 0
    for sd in range(gcap):
        out = place_pencil_general(Gp, random.Random(SEED + sd))
        if out is None:
            continue
        placed = out[0]
        if not star_generic(Gp, placed):
            continue
        tried += 1
        sig, rk, _t = direct_corank(Hed, placed)
        assert rk == 5 * len(Hed) - sig
        if sig > 0:
            jump2.append(SEED + sd)
        if tried <= tr_sub:
            V = sorted(verts_of(Gp), key=str)
            R, _er, _C, _i, _n = build_rigidity(
                {'edges': Gp, 'V': V, 'pt': placed})
            if rank(R) == tgt:
                tr += 1
                ok += 1
    print(f"      gate-accepted seeds: {tried}; with sigma > 0: "
          f"{len(jump2)} {jump2}")
    print(f"      of the first {tr_sub} gate-accepted seeds, "
          f"{tr} are at target rank of `G''`")
    return len(jump), same, ok, len(jump2)


# ---------------- mode: --hunt -------------------------------------------

def mode_hunt(nseed=4, cap_k4=None, gp_sub=40):
    print("== the hunt: is there a class (shape, split) with `sigma > 0` at "
          "EVERY chart point? ==")
    print("   BOUNDARY, stated before any number.  `{sigma = 0}` is a proper "
          "OPEN (section (K-out) (OC-24)(i), (OC-28)(iv)), so "
          "`{sigma = 0} = empty` is a CLOSED condition.  A tally of samples "
          "can only ever REFUTE it -- ONE corank-0 point suffices, and by "
          "(OC-24)(i) + section (K-chart) (CH-1)(a) that single point is a "
          "complete certificate.  A shape where every SAMPLED seed has "
          "sigma > 0 is 'not found under the cap', NEVER a hit: a hit needs "
          "an argument or an exhaustive uncapped chart-level certificate.")
    print(f"   method: per shape, up to {nseed} `repin.star_generic`-gated "
          f"exact-Q placements of `G`'s OWN chart; each one's `H`-part is a "
          f"point of every eligible split's `G''`-chart by (OC-28)(i), and "
          f"`sigma = corank R(H)` by (OC-23).  Cross-checked on the first "
          f"{gp_sub} (shape, split) pairs against a gated placement of "
          f"`G''`'s chart itself.")
    pool = shape_pool(cap_k4=cap_k4)
    print(f"   pool: {len(pool)} class shapes "
          f"({'K4 stratum EXHAUSTIVE (877) + 5 named' if cap_k4 is None else 'K4 stratum CAPPED at ' + str(cap_k4)})")
    pairs, certified, unresolved, xchecked = 0, 0, [], 0
    for (name, edges) in pool:
        placed = None
        for t in range(nseed):
            got = sample_chart(edges, SEED + 977 * t + 3 * len(edges),
                               tries=6)
            if got is not None:
                placed = got[0]
                break
        splits = eligible_splits(edges)
        for v in splits:
            sd = split_data(edges, v)
            if sd is None:
                continue
            a, b, c, Gp, Hed = sd
            pairs += 1
            ok = False
            if placed is not None:
                d, rk, _t = direct_corank(Hed, placed)
                assert rk == 5 * len(Hed) - d, "rank ledger broke"
                if d == 0:
                    assert rk == 5 * len(Hed), "corank-0 rank certificate"
                    ok = True
            if not ok:
                for t in range(nseed):
                    g2 = sample_chart(Gp, SEED + 613 * t + 5 * len(Hed),
                                      tries=6)
                    if g2 is None:
                        continue
                    d, rk, _t = direct_corank(Hed, g2[0])
                    if d == 0:
                        assert rk == 5 * len(Hed)
                        ok = True
                        break
            elif xchecked < gp_sub:
                g2 = sample_chart(Gp, SEED + 17 * len(Hed), tries=6)
                if g2 is not None:
                    d2, rk2, _t = direct_corank(Hed, g2[0])
                    assert d2 == 0, (name, v, d2)
                    xchecked += 1
            if ok:
                certified += 1
            else:
                unresolved.append((name, v))
    print(f"   class (shape, split) pairs: {pairs}")
    print(f"   pairs carrying an exact-Q FULL-ROW-RANK certificate for "
          f"`R(H)` (so `sigma = 0` there, so `{{sigma = 0}} != empty`, so NO "
          f"hit at that pair): {certified}")
    print(f"   `G''`-chart cross-checks agreeing: {xchecked}")
    print(f"   pairs not resolved under the cap: {len(unresolved)}")
    for row in unresolved[:12]:
        print(f"     UNRESOLVED {row}")
    return pairs, certified, len(unresolved)


# ---------------- main ---------------------------------------------------

def main():
    args = sys.argv[1:] or ['--validate']
    todo = (['--reduce', '--spans', '--budget', '--slack', '--theta',
             '--p21', '--hunt']
            if '--validate' in args else args)
    for m in todo:
        print()
        if m == '--reduce':
            mode_reduce()
        elif m == '--spans':
            mode_spans()
        elif m == '--budget':
            mode_budget()
        elif m == '--slack':
            mode_slack()
        elif m == '--theta':
            mode_theta()
        elif m == '--p21':
            mode_p21()
        elif m == '--hunt':
            mode_hunt()
        else:
            print(f"unknown mode {m}")
            return 2
    print()
    print("PASSED")
    return 0


if __name__ == '__main__':
    sys.exit(main())
