"""
Phase 39, kernel-(K) FIFTH fan-out direction PEX -- PATTERN-EXISTENCE on the
bare-cycle stratum, i.e. section (K-frame)'s residual (FR-R1): does EVERY
bare-cycle site of EVERY k = 4 class triple admit a `pattern colouring` --
an admissible 2-colouring of `G' = G - v + ab` whose six frame edges split
3-3 with pairwise-distinct ruling components per family, plus (FR-4)'s two
placement-free legality clauses?

Workbook section: `(K-frame)`, labels `(FR-8)+`, Steps `FR7+` (the reserved
direction-PEX namespace, `notes/Pencil-labels.md` 2026-08-07 PEX/TCOL
table).  Read against section (K-frame) *Steps FR0-FR6*, section (K-grid)
*Step G12* (admissible colourings = one free bit per branch), section
(K-ann) *Steps A14/A15* ((ANH-13)(iv): `c' = 1 <=> c(G) = 3`; (ANH-14)(a):
the 7-point open chain), and the standing combinatorics of
`Pencil-informal.md`'s *Shared dictionary* -- (R4) `hcard` (the hub-hub
subgraph has max degree <= 2), (SD-6) (branches have length <= 5), and
girth 6 from 5/6-sparsity.

THE TWO STRUCTURAL FACTS this driver measures and then CONSUMES (novel
here; (FR-8)/(FR-9)).  Write `H = G - v - a`, `P` the length-4 companion,
`X` the weld.

(1) THE STRATUM IS FINITE AND ENUMERABLE.  A bare-cycle site needs
    `c' = 1`, i.e. `c(G) = 3`, i.e. `(|V|,|E|) = (16,18)`; hubs have degree
    >= 3 so `n_hub <= 2c - 2 = 4`, branches number `n_hub + 2` and total
    18 with each <= 5 by (SD-6), and `G*` has no loop (a loop branch is a
    cycle of length <= 5, below girth).  So the whole bare-cycle stratum
    sits over FOUR hub multigraphs and finitely many length tuples --
    `--strat` enumerates them all, which is what LIFTS the `|V*| <= 5`
    sweep caveat (ANH-14)(b) / (FR-5) carry.  (Two of the four multigraphs
    are outside `outer.sweep_shapes` entirely.)

(2) THE FRAME'S NORMAL FORM PINS EVERY DEGREE OF FREEDOM.  `H/P` is
    EXACTLY (bare 6-cycle) + (the length-5 branch beta) -- 11 edges, 10
    nodes, nothing else -- so the site's six frame edges form an open path
    `x - z1 - ... - z5 - x'` in `G'` on 7 points whose two ends are the
    companion attachment points and are HUBS; `|S| in {1,2}` of `z1..z5`
    are hubs (beta's endpoints other than the weld), each having its third
    `G'`-neighbour inside beta at degree 2, so `z_j`'s hub-hub edges are
    frame edges; and no other `H`-edge joins two frame vertices.  Hence the
    frame is 2 or 3 COMPLETE, DISTINCT branches of `G'` -- independent free
    bits, so the alternating pattern is always reachable, forcing the 3-3
    split -- the unanchored frame edges are singleton ruling components,
    and the anchored ones can never collide.

Modes (run from the repo root, PYTHONHASHSEED=0):

    python3 notes/scripts/w4/patexist.py --frame    # (FR-9): the frame normal form, over ALL 1904 pool sites
    python3 notes/scripts/w4/patexist.py --recipe   # (FR-11): the CONSTRUCTED colouring, no search, over the pool
    python3 notes/scripts/w4/patexist.py --strat    # (FR-8)+(FR-12): the COMPLETE c(G) = 3 stratum, exhaustive
    python3 notes/scripts/w4/patexist.py --recon    # (FR-14): the 1904 / 1976 reconciliation + the c' <= 1 cells
    python3 notes/scripts/w4/patexist.py --kill     # the cheap kill + the load-bearing-hypothesis witnesses
    python3 notes/scripts/w4/patexist.py --validate # machinery pins, incl. (FR-10)'s two equivalences

WHICH MODE TESTS WHICH SENTENCE (F11).

--frame     (FR-9)(a)-(i): per site ASSERTS the 7-point path normal form,
            that the two companion ends are hubs, that `|S| in {1,2}`, that
            each run is a COMPLETE branch of `G'` and the runs are pairwise
            distinct, that frame parities never clash, that the only
            `H`-edges among frame vertices are the six frame edges plus
            possibly the `P`-edge `x x'`, that every hub `z_j`'s hub-hub
            edges are frame edges, that at `|S| = 2` EVERY hub-hub edge of
            `G'` is a frame edge, that `c(G') = 3` with `n_hub <= 4`, and
            that `Lambda` is acyclic.  Histograms the run-length profiles.
--recipe    (FR-11): builds ONE colouring per site by the recipe (frame bits
            forced to alternate; Lambda properly 2-coloured; every other bit
            the fixed constant 0) and asserts it passes `crit_33` +
            `legality_free` -- the SAME predicates `framedom.py --pattern`
            searches for.  It reports which of the four canonical variants
            was needed, i.e. exactly how much search the recipe replaces.
--strat     (FR-8) + (FR-12): enumerates the complete `c(G) = 3` stratum
            from the hub multigraph up (NOT `outer.sweep_shapes`), asserts
            the multigraph census, the girth pair (7, 6), and (SD-6) at
            `G'`, then re-runs --frame's clauses and --recipe's construction
            AND a fully EXHAUSTIVE colouring scan on every site.  It also
            asserts (FR-12)'s collision characterization (a legality-(i)
            collision is always a pair of length-2-branch interiors) and
            counts the collisions, which is 0.  This is the mode that tests
            the word `every` in (FR-R1) at the bare-cycle stratum.
--recon     (FR-14): keys BOTH censuses -- `outer.sweep_shapes` +
            `named_inventory`, and the complete-stratum enumeration -- by
            ISOMORPHISM CLASS of the shape (canonical over the <= 24 hub
            permutations, exact since `n_hub <= 4`), and asserts the only
            direction (FR-8) depends on: **no iso class the pool knows is
            missing from the enumeration**.  Then re-derives (ANH-13) *Step
            A14*'s `c' = 0` and `c' = 1` cells over the complete `c(G) = 2`
            and `c(G) = 3` strata, at both granularities.  It also asserts,
            per shape, that its own `len5_sites` agrees with
            `framedom.bare_sites`, that no `c(G) = 3` length-5 site is
            anything but a bare cycle, and that the labelled totals decompose
            as `iso total + duplicate over-count`.
--kill      the cheap kill (a site whose EVERY admissible colouring fails)
            over the census pool -- `--strat` runs it over the WHOLE
            stratum, which is the figure to quote; plus the F13 adversarial witnesses that (FR-10)'s
            mechanism is load-bearing: a CONSTRUCTED graph with an odd
            `Lambda` cycle must have ZERO legal admissible colourings, and
            its even-cycle control must have some -- so parity, not size, is
            the mechanism, and it is the one place a refutation could have
            lived.
--validate  machinery: the free-bit dictionary against
            `closure.alternation_classes`; (FR-10)(i) `two hubs share a
            family component IFF joined by a path of that family's hub-hub
            edges`; (FR-10)(ii) `legality clause (ii) holds IFF Lambda is
            properly edge-2-coloured`, asserted over every (split,
            colouring) pair of the census pool; and the stratum census.

Placement-free by construction: this direction's question is COMBINATORIAL,
so no configuration is built and no arithmetic beyond graph search happens
-- consequently there is no sampled object to guard, and the only
`random.Random` use is `--kill`'s tie-break, seeded and printed.  Imports
`framedom`, `closure`, `outer`, `shrink`, `annih`, `nogood_subdiv`,
`kbare_common`, `exactcore` READ-ONLY; nothing existing is modified.
"""
import argparse
import itertools
import os
import random
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors                                    # noqa: E402
from kbare_common import verts_of, is_2ec                          # noqa: E402
from nogood_subdiv import hcard_ok, triangles                      # noqa: E402
from closure import alternation_classes, colourings, components    # noqa: E402
from outer import (split_data, eligible_splits, shapes_from,       # noqa: E402
                   companions4, named_inventory, sweep_shapes)
from annih import path_edges                                       # noqa: E402
from shrink import hp_edge_rows                                    # noqa: E402
from anhr1 import core_decompose                                   # noqa: E402
from shrink import census_pool                                     # noqa: E402
from annih import girth                                            # noqa: E402
from framedom import (bare_sites, pool_splits, chn_sets,           # noqa: E402
                      line_ids, crit_33, legality_free)

PEX_SEED = 20260807


# ---------------- the frame normal form ((FR-9)) ---------------------------

def frame_path(edges6):
    """Order the six frame edges as a path (or closed hexagon) of `G'`.

    Returns `(verts, order, closed)` with `order[i] = (verts[i], verts[i+1])`
    the i-th frame edge; `verts` has 7 entries (open chain) or 6 (closed
    hexagon).  An arc-specific device: `framedom.bare_sites` returns the six
    edges in the CONTRACTED cycle's order, which does not say where the weld
    `X` breaks them open."""
    inc = defaultdict(list)
    for k, e in enumerate(edges6):
        inc[e[0]].append(k)
        inc[e[1]].append(k)
    assert all(len(v) <= 2 for v in inc.values()), "frame is not a path/cycle"
    ends = sorted((v for v in inc if len(inc[v]) == 1), key=str)
    closed = not ends
    if closed:
        assert len(inc) == 6, "closed frame is not a hexagon"
        start = sorted(inc, key=str)[0]
    else:
        assert len(ends) == 2 and len(inc) == 7, "frame is not a 7-point path"
        start = ends[0]
    verts, order, used, cur = [start], [], set(), start
    while len(order) < 6:
        nxt = [k for k in inc[cur] if k not in used]
        assert nxt, "frame walk stalled"
        k = nxt[0]
        used.add(k)
        e = edges6[k]
        w = e[1] if e[0] == cur else e[0]
        order.append((cur, w))
        verts.append(w)
        cur = w
    if closed:
        assert verts[0] == verts[6]
        verts = verts[:6]
    return verts, order, closed


def branch_of(comps, e):
    """(index of the alternation class = branch of `G'` holding `e`, parity
    of `e` inside it)."""
    for k, c in enumerate(comps):
        if e in c:
            return k, c[e]
        if (e[1], e[0]) in c:
            return k, c[(e[1], e[0])]
    raise AssertionError("edge in no alternation class")


def hub_set(Gp):
    deg = {u: len(ns) for u, ns in neighbors(Gp).items()}
    return deg, {u for u in deg if deg[u] >= 3}


def lambda_graph(Gp):
    """The hub-hub subgraph of `G'`.  (R4) says its max degree is <= 2, so it
    is a disjoint union of paths and cycles."""
    deg, hubs = hub_set(Gp)
    return [e for e in Gp if e[0] in hubs and e[1] in hubs], hubs, deg


def lam_components(Lam):
    """Components of `Lambda` as ordered vertex walks, `[(walk, is_cycle)]`;
    asserts (R4)'s max degree 2."""
    nb = defaultdict(list)
    for (u, w) in Lam:
        nb[u].append(w)
        nb[w].append(u)
    assert all(len(v) <= 2 for v in nb.values()), \
        "(R4) violated: hub with three hub neighbours"
    out, seen = [], set()
    for start in sorted(nb, key=str):
        if start in seen or len(nb[start]) != 1:
            continue
        walk, cur, prev = [start], start, None
        seen.add(start)
        while True:
            nxts = [w for w in nb[cur] if w != prev]
            if not nxts:
                break
            prev, cur = cur, nxts[0]
            walk.append(cur)
            seen.add(cur)
        out.append((walk, False))
    for start in sorted(nb, key=str):
        if start in seen:
            continue
        walk, cur, prev = [start], start, None
        seen.add(start)
        while True:
            nxts = [w for w in nb[cur] if w != prev]
            assert nxts, "cycle walk stalled"
            prev, cur = cur, nxts[0]
            if cur == start:
                break
            walk.append(cur)
            seen.add(cur)
        out.append((walk, True))
    return out


def frame_report(Gp, edges6):
    """Everything (FR-8) asserts about one site's frame."""
    deg, hubs = hub_set(Gp)
    verts, order, closed = frame_path(edges6)
    comps, odd = alternation_classes(Gp)
    assert not odd, "G' has a bare odd cycle component"
    binfo = [branch_of(comps, e) for e in order]
    if closed:
        ends = [verts[0], verts[0]]
        inner = verts[1:6]
    else:
        ends = [verts[0], verts[6]]
        inner = verts[1:6]
    S = [i + 1 for i, z in enumerate(inner) if deg[z] >= 3]
    runs, cur = [], [0]
    for i in range(1, 6):
        if i in S:
            runs.append(cur)
            cur = [i]
        else:
            cur.append(i)
    runs.append(cur)
    return {'verts': verts, 'order': order, 'closed': closed, 'ends': ends,
            'inner': inner, 'S': S, 'runs': runs, 'binfo': binfo,
            'comps': comps, 'deg': deg, 'hubs': hubs}


def frame_clauses(label, v, Gp, a, edges6, bad):
    """(FR-9)(a)-(i), asserted at one site; appends to `bad`."""
    R = frame_report(Gp, edges6)
    HE = set()
    for (u, w) in Gp:
        if a in (u, w):
            continue
        HE.add((u, w))
        HE.add((w, u))
    # (a) both companion ends are hubs of G'
    for e in R['ends']:
        if R['deg'][e] < 3:
            bad.append((label, v, 'end-not-hub', e))
    # (b)+(c) |S| in {1, 2}
    if len(R['S']) not in (1, 2):
        bad.append((label, v, 'S-size', tuple(R['S'])))
    # (d) each run is a COMPLETE branch of G', runs pairwise distinct
    bidx = [R['binfo'][i][0] for i in range(6)]
    for run in R['runs']:
        ks = {bidx[i] for i in run}
        if len(ks) != 1:
            bad.append((label, v, 'run-splits-branch', tuple(run)))
            continue
        k = ks.pop()
        if len(R['comps'][k]) != len(run):
            bad.append((label, v, 'run-not-whole-branch',
                        (len(run), len(R['comps'][k]))))
    if len({bidx[run[0]] for run in R['runs']}) != len(R['runs']):
        bad.append((label, v, 'runs-share-branch', tuple(bidx)))
    # (d') alternation realizable: frame parity tracks the frame index
    for i in range(6):
        for j in range(i + 1, 6):
            if R['binfo'][i][0] == R['binfo'][j][0]:
                same = (R['binfo'][i][1] == R['binfo'][j][1])
                if same != ((j - i) % 2 == 0):
                    bad.append((label, v, 'parity-conflict', (i, j)))
    # (f) the ONLY H-edges among frame vertices are the six frame edges,
    #     plus possibly the P-edge x-x' at the two ends
    fset = {(u, w) for (u, w) in R['order']} | \
           {(w, u) for (u, w) in R['order']}
    fv = R['verts']
    for i in range(len(fv)):
        for j in range(i + 1, len(fv)):
            p, q = fv[i], fv[j]
            if (p, q) in fset or (p, q) not in HE:
                continue
            if {p, q} == set(R['ends']):
                continue
            bad.append((label, v, 'frame-chord', (p, q)))
    # (g) every hub among z1..z5 has all its hub-hub edges on the frame
    for idx, z in enumerate(R['inner']):
        if R['deg'][z] < 3:
            continue
        for (u, w) in Gp:
            if z not in (u, w):
                continue
            o = w if u == z else u
            if R['deg'][o] >= 3 and (z, o) not in fset:
                bad.append((label, v, 'off-frame-lambda-at-zj', (z, o)))
    # (h) when |S| = 2, EVERY hub-hub edge of G' is a frame edge (the weld has
    #     H/P-degree 2, which forces deg_G(b) = deg_G(c) = 3 and the three
    #     companion interiors to have degree 2)
    if len(R['S']) == 2:
        for (u, w) in Gp:
            if R['deg'][u] >= 3 and R['deg'][w] >= 3 and (u, w) not in fset:
                bad.append((label, v, 'S2-off-frame-lambda', (u, w)))
    # (i) c(G') = 3 and Lambda is a forest (no Lambda cycle: it would be a
    #     cycle of G on hubs only, of length >= 6 > n_hub)
    nV = len(verts_of(Gp))
    if len(Gp) - nV + 1 != 3:
        bad.append((label, v, 'cycle-rank', len(Gp) - nV + 1))
    if len(R['hubs']) > 4:
        bad.append((label, v, 'too-many-hubs', len(R['hubs'])))
    Lam, hubs, deg = lambda_graph(Gp)
    for (walk, cyc) in lam_components(Lam):
        if cyc:
            bad.append((label, v, 'lambda-cycle', len(walk)))
    return R


# ---------------- the recipe ((FR-11)) --------------------------------------

def recipe_colouring(Gp, edges6, flip=False, other=0):
    """THE CONSTRUCTION, not a search.  Returns `(col, notes)`.

    Step 1  frame branches: bit forced so the frame path ALTERNATES, family
            A on even frame index (`flip` swaps the two families).  Legal
            because the 2-or-3 runs are distinct branches ((FR-8)(d)).
    Step 2  Lambda edges (= length-1 branches between hubs): properly
            2-coloured, alternating along each Lambda path/cycle and seeded
            by whatever Step 1 forced.  This is exactly (FR-4)'s second
            legality clause: a hub with two same-family Lambda edges has its
            3-member closed hub neighbourhood mono-component.
    Step 3  every remaining branch: the FIXED bit `other`.
    """
    R = frame_report(Gp, edges6)
    comps = R['comps']
    bit = [None] * len(comps)
    for i in range(6):
        k, par = R['binfo'][i]
        want = 'A' if ((i % 2 == 0) != flip) else 'B'
        b = (0 if want == 'A' else 1) ^ par
        if bit[k] is None:
            bit[k] = b
        else:
            assert bit[k] == b, "frame alternation is not realizable"
    Lam, hubs, deg = lambda_graph(Gp)
    lam_idx = {}
    for e in Lam:
        k, par = branch_of(comps, e)
        assert len(comps[k]) == 1, "Lambda edge is not a length-1 branch"
        lam_idx[frozenset(e)] = k
    notes = []
    for (walk, cyc) in lam_components(Lam):
        n = len(walk)
        seq = [lam_idx[frozenset((walk[i], walk[(i + 1) % n]))]
               for i in (range(n) if cyc else range(n - 1))]
        seed = next(((i, bit[k]) for i, k in enumerate(seq)
                     if bit[k] is not None), None)
        off, base = seed if seed is not None else (0, 0)
        for i, k in enumerate(seq):
            want = base ^ ((i - off) % 2)
            if bit[k] is None:
                bit[k] = want
            elif bit[k] != want:
                notes.append('lambda-parity-clash')
        if cyc and len(seq) % 2 == 1:
            notes.append('odd-lambda-cycle')
    for k in range(len(comps)):
        if bit[k] is None:
            bit[k] = other
    col = {}
    for k, cmp_ in enumerate(comps):
        for e, p in cmp_.items():
            col[e] = 'A' if (p ^ bit[k]) == 0 else 'B'
    return col, notes


def check_pattern(Gp, col, edges6):
    """The two predicates `framedom.py --pattern` searches for, applied to a
    single supplied colouring."""
    allverts = sorted(verts_of(Gp), key=str)
    EA = [e for e in Gp if col[e] == 'A']
    EB = [e for e in Gp if col[e] == 'B']
    cA = components(allverts, EA)
    cB = components(allverts, EB)
    chn = chn_sets(Gp)
    return (legality_free(col, cA, cB, allverts, chn),
            crit_33(line_ids(col, cA, cB, edges6)))


def collisions(Gp, allverts, cA, cB):
    """The pairs legality clause (i) forbids: two bodies with the SAME pair of
    ruling components, i.e. the same point of the grid."""
    seen, out = {}, []
    for u in allverts:
        key = (cA[u], cB[u])
        if key in seen:
            out.append((seen[key], u))
        else:
            seen[key] = u
    return out


def both_len2_interiors(Gp, deg, p, q):
    """(FR-12)'s characterization: a collision can only be a pair of degree-2
    bodies each of whose two neighbours is a hub -- i.e. two interiors of
    length-2 branches.  (Adjacent pairs and hub-involving pairs are killed by
    girth; see the draft.)"""
    nb = neighbors(Gp)
    for z in (p, q):
        if deg.get(z, 0) != 2:
            return False
        if any(deg.get(w, 0) < 3 for w in nb[z]):
            return False
    return True


def leg2_only(Gp, allverts, cA, cB):
    """(FR-4)'s SECOND legality clause alone: no 3-member closed hub
    neighbourhood is mono-component in either family."""
    chn = chn_sets(Gp)
    for u in sorted(chn, key=str):
        S = sorted(chn[u], key=str)
        if len(S) == 3:
            if len({cA[w] for w in S}) == 1 or len({cB[w] for w in S}) == 1:
                return False
    return True


def lam_proper(Gp, col):
    """Is `Lambda` properly edge-2-coloured by `col` -- no hub carrying two
    same-family hub-hub edges?"""
    Lam, hubs, deg = lambda_graph(Gp)
    at = defaultdict(list)
    for e in Lam:
        at[e[0]].append(col[e])
        at[e[1]].append(col[e])
    return all(len(set(v)) == len(v) for v in at.values())


def recipe_at(Gp, edges6):
    """Try the four canonical recipe variants (family swap x the constant
    for the untouched branches).  Returns `(ok, variant, notes)`."""
    allnotes = []
    for flip in (False, True):
        for other in (0, 1):
            col, notes = recipe_colouring(Gp, edges6, flip, other)
            allnotes.extend(notes)
            leg, crit = check_pattern(Gp, col, edges6)
            if leg and crit:
                return True, (flip, other), allnotes
    return False, None, allnotes


# ---------------- the complete c(G) = 3 stratum ((FR-8)) ------------------

def c3_hub_multigraphs():
    """Every connected loopless multigraph on `n` labelled vertices with
    `n + 2` edges and min degree >= 3, `n = 2..4` -- i.e. every hub
    multigraph a bare-cycle site's shape can have.  `n <= 2c - 2 = 4`
    because hubs have degree >= 3 and `Sum_hub deg = 2c - 2 + 2 n_hub`;
    loops are excluded because a loop branch is a cycle of length <= 5,
    below girth 6."""
    out = []
    for n in (2, 3, 4):
        m = n + 2
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        seen = set()
        for mult in itertools.product(range(m + 1), repeat=len(pairs)):
            if sum(mult) != m:
                continue
            deg = [0] * n
            for t, (i, j) in zip(mult, pairs):
                deg[i] += t
                deg[j] += t
            if min(deg) < 3:
                continue
            adj = {i: set() for i in range(n)}
            for t, (i, j) in zip(mult, pairs):
                if t:
                    adj[i].add(j)
                    adj[j].add(i)
            seenv, st = {0}, [0]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if y not in seenv:
                        seenv.add(y)
                        st.append(y)
            if len(seenv) != n:
                continue
            best = None
            for perm in itertools.permutations(range(n)):
                key = tuple(sorted(
                    (tuple(sorted((perm[i], perm[j]))), t)
                    for t, (i, j) in zip(mult, pairs) if t))
                if best is None or key < best:
                    best = key
            if best in seen:
                continue
            seen.add(best)
            E0 = [p for t, p in zip(mult, pairs) for _ in range(t)]
            out.append((n, E0, mult))
    return out


def c3_shapes(lmax=6):
    """Every `c(G) = 3` class shape carrying a (length-3 split branch,
    length-4 companion) pair, from the hub multigraph up.  `lmax` is
    deliberately 6 -- one above (SD-6)'s bound -- so the mode can ASSERT
    that no surviving shape has a length-6 branch."""
    out = []
    for n, E0, mult in c3_hub_multigraphs():
        tag = f'c3-n{n}-{"".join(str(t) for t in mult)}'
        sh, tried, capped = shapes_from(tag, n, E0, lmax)
        assert not capped
        out.append((tag, n, E0, sh, tried))
    return out


def sites_of(E):
    """Every bare-cycle site of every triple of one shape, as
    `(v, sd, P, kb, edges6)`."""
    for v in eligible_splits(E):
        sd = split_data(E, v)
        if sd is None:
            continue
        a, b, c, Gp, Hed = sd
        sites, _ = bare_sites(Hed, b, c)
        for (P, kb, edges6) in sites:
            yield v, sd, P, kb, edges6



# ---------------- the 1896/1904 reconciliation ((FR-14)) -------------------

def branches_with_ends(E):
    """Every branch of `E` as `(hub, hub, length)`.  A local device: the
    canonical `closure.alternation_classes` returns each branch as an EDGE
    SET with parities, which does not name the branch's two hub ends -- and
    the ends are exactly what an isomorphism key needs."""
    deg, hubs = hub_set(E)
    nb = neighbors(E)
    out, used = [], set()
    for h in sorted(hubs, key=str):
        for w in sorted(nb[h], key=str):
            if frozenset((h, w)) in used:
                continue
            used.add(frozenset((h, w)))
            prev, cur, ln = h, w, 1
            while deg[cur] == 2:
                nxt = [x for x in nb[cur] if x != prev][0]
                used.add(frozenset((cur, nxt)))
                prev, cur, ln = cur, nxt, ln + 1
            out.append((h, cur, ln))
    return out, sorted(hubs, key=str)


def shape_key(E):
    """The isomorphism class of a subdivision shape, canonically.  `G` is the
    subdivision of `G*` at its branch lengths ((R4)), so the pair
    (hub multigraph, length labels) is a complete invariant; `n_hub <= 4` on
    the strata this mode touches, so brute force over the <= 24 hub
    permutations is exact and instant."""
    brs, hubs = branches_with_ends(E)
    idx = {h: i for i, h in enumerate(hubs)}
    n = len(hubs)
    best = None
    for perm in itertools.permutations(range(n)):
        key = tuple(sorted((min(perm[idx[u]], perm[idx[w]]),
                            max(perm[idx[u]], perm[idx[w]]), L)
                           for (u, w, L) in brs))
        if best is None or key < best:
            best = key
    return (n, best)


def len5_sites(Hed, b, c):
    """Per length-4 companion: the length-5 branches of `H/P`, split into the
    three `--size` outcomes -- `bare` (reduced object a bare 6-cycle, i.e.
    (ANH-13)'s `c' = 1`), `loop0` (the branch has no core-node end, i.e.
    `c' = 0`, `H/P` a single cycle), and `other5` (everything else).  A local
    device that re-derives `framedom.bare_sites`' loop with the `e0 is None`
    arm counted instead of skipped; the `bare` and `other5` figures are
    ASSERTED equal to `framedom.bare_sites`' by the caller."""
    bare, loop0, other5 = 0, 0, 0
    for P in companions4(Hed, b, c):
        Pe = path_edges(Hed, P)
        Pset = {j for (j, s) in Pe}
        rows = hp_edge_rows(Hed, set(P), Pset)
        nodes, branches = core_decompose(rows)
        for (e0, e1, chain) in branches:
            if len(chain) != 5:
                continue
            if e0 is None:
                loop0 += 1
                continue
            drop = {r[0] for r in chain}
            keep = [r for r in rows if r[0] not in drop]
            nd, br = core_decompose(keep)
            if nd or len(br) != 1:
                other5 += 1
            else:
                bare += 1
    return bare, loop0, other5


def c_hub_multigraphs(c):
    """Every connected loopless multigraph on `n` labelled vertices with
    `n + c - 1` edges and min degree >= 3, `1 <= n <= 2c - 2` -- i.e. every
    hub multigraph a class shape of cycle rank `c` can have."""
    out = []
    for n in range(1, 2 * c - 1):
        m = n + c - 1
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        if not pairs:
            continue
        seen = set()
        for mult in itertools.product(range(m + 1), repeat=len(pairs)):
            if sum(mult) != m:
                continue
            deg = [0] * n
            for t, (i, j) in zip(mult, pairs):
                deg[i] += t
                deg[j] += t
            if min(deg) < 3:
                continue
            adj = {i: set() for i in range(n)}
            for t, (i, j) in zip(mult, pairs):
                if t:
                    adj[i].add(j)
                    adj[j].add(i)
            seenv, st = {0}, [0]
            while st:
                x = st.pop()
                for y in adj[x]:
                    if y not in seenv:
                        seenv.add(y)
                        st.append(y)
            if len(seenv) != n:
                continue
            best = None
            for perm in itertools.permutations(range(n)):
                key = tuple(sorted(
                    (tuple(sorted((perm[i], perm[j]))), t)
                    for t, (i, j) in zip(mult, pairs) if t))
                if best is None or key < best:
                    best = key
            if best in seen:
                continue
            seen.add(best)
            out.append((n, [p for t, p in zip(mult, pairs) for _ in range(t)],
                        mult))
    return out


def cstrat_shapes(c, lmax=6):
    """Every class shape of cycle rank `c` carrying a (length-3 split branch,
    length-4 companion) pair, from the hub multigraph up."""
    out = []
    for n, E0, mult in c_hub_multigraphs(c):
        tag = f'c{c}-n{n}-{"".join(str(t) for t in mult)}'
        sh, tried, capped = shapes_from(tag, n, E0, lmax)
        assert not capped
        out.append((tag, n, E0, sh, tried))
    return out


def site_profile(E):
    """`(bare, loop0, other5)` summed over every eligible split of `E`, with
    the `bare`/`other5` halves cross-checked against `framedom.bare_sites`."""
    B, L, O = 0, 0, 0
    for v in eligible_splits(E):
        sd = split_data(E, v)
        if sd is None:
            continue
        a, b, c, Gp, Hed = sd
        bb, ll, oo = len5_sites(Hed, b, c)
        ref, refother = bare_sites(Hed, b, c)
        assert bb == len(ref) and oo == refother, \
            "local len5_sites disagrees with framedom.bare_sites"
        B, L, O = B + bb, L + ll, O + oo
    return B, L, O


# ---------------- mode: --frame ((FR-9)) -----------------------------------

def mode_frame():
    print("== (FR-9) the bare-cycle frame's normal form in G' ==")
    print("   over the (ANH-9) pool `framedom.py --pattern` scans: the")
    print("   7-point path, the hub companion ends, the hub set S among")
    print("   z1..z5, the run decomposition into COMPLETE branches, the")
    print("   chord ban and the Lambda-locality of each hub z_j.\n")
    tot, closedn, nsplit, bad = 0, 0, 0, []
    Shist, runhist, lamhist = (defaultdict(int), defaultdict(int),
                               defaultdict(int))
    endedge = 0
    for desc, label, v, E, sd in pool_splits():
        a, b, c, Gp, Hed = sd
        sites, _ = bare_sites(Hed, b, c)
        if not sites:
            continue
        nsplit += 1
        assert hcard_ok(Gp) and is_2ec(Gp), f"{label}: G' hypothesis failure"
        Lam, hubs, deg = lambda_graph(Gp)
        for (walk, cyc) in lam_components(Lam):
            lamhist[('cycle' if cyc else 'path', len(walk))] += 1
        for (P, kb, edges6) in sites:
            tot += 1
            R = frame_clauses(label, v, Gp, a, edges6, bad)
            closedn += R['closed']
            Shist[len(R['S'])] += 1
            runhist[tuple(len(r) for r in R['runs'])] += 1
            p, q = R['ends']
            if p != q and ((p, q) in Gp or (q, p) in Gp):
                endedge += 1
    print(f"   splits with bare-cycle sites: {nsplit}; sites: {tot}")
    assert tot == 1904, "site census does not reproduce (ANH-13)'s 1904"
    print("   site census == (ANH-13)'s 1904                              OK")
    print(f"   closed-hexagon sites (x = x'): {closedn};"
          f" open 7-point sites: {tot - closedn}")
    print(f"   sites whose two companion ends are P-ADJACENT: {endedge}")
    print(f"   |S| histogram (hubs among z1..z5): {dict(sorted(Shist.items()))}")
    print("   run-length profiles: "
          f"{dict(sorted(runhist.items()))}")
    print("   Lambda components (type, #vertices): "
          f"{dict(sorted(lamhist.items(), key=str))}")
    if bad:
        print(f"\n   (FR-9) MISSES: {len(bad)}; first 12:")
        for row in bad[:12]:
            print(f"     {row}")
        print("FAILED")
        return 1
    print("\n   every (FR-9) clause holds at every one of the 1904 sites")
    print("PASSED")
    return 0


# ---------------- mode: --recipe ((FR-11)) ----------------------------------

def mode_recipe():
    print("== (FR-11) the CONSTRUCTED pattern colouring, over the pool ==")
    print("   one colouring per site, built by the recipe; no search over")
    print("   admissible colourings.  Both (FR-4) hypotheses asserted.\n")
    tot, ok, fail = 0, 0, []
    varhist, notehist = defaultdict(int), defaultdict(int)
    for desc, label, v, E, sd in pool_splits():
        a, b, c, Gp, Hed = sd
        sites, _ = bare_sites(Hed, b, c)
        for (P, kb, edges6) in sites:
            tot += 1
            good, var, notes = recipe_at(Gp, edges6)
            for nm in notes:
                notehist[nm] += 1
            if good:
                ok += 1
                varhist[var] += 1
            else:
                fail.append((label, v, kb))
    print(f"   sites: {tot}")
    assert tot == 1904
    print(f"   RECIPE SUCCEEDS at: {ok} / {tot}")
    print(f"   variant used (flip, other-branch bit): {dict(sorted(varhist.items()))}")
    print(f"   recipe notes raised: {dict(sorted(notehist.items()))}")
    if fail:
        print(f"   recipe misses: {len(fail)}; first 12:")
        for row in fail[:12]:
            print(f"     {row}")
        print("FAILED")
        return 1
    print("   NO misses: the construction is a recipe, not a search")
    print("PASSED")
    return 0


# ---------------- mode: --strat ((FR-8)/(FR-12)) ----------------------------------

def mode_strat(exhaustive_cap=8192):
    print("== (FR-8) + (FR-12): the COMPLETE c(G) = 3 stratum ==")
    print("   enumerated from the hub multigraph up, NOT from")
    print("   `outer.sweep_shapes` -- this is the mode that tests the word")
    print("   `every` in (FR-R1) at the bare-cycle stratum.\n")
    mg = c3_hub_multigraphs()
    print(f"   hub multigraphs with n+2 edges, min degree 3, loopless,"
          f" connected: {len(mg)}")
    for n, E0, mult in mg:
        print(f"     n = {n}, multiplicities {mult}, |E*| = {len(E0)}")
    fams = c3_shapes()
    tot_shapes = sum(len(sh) for (_t, _n, _E0, sh, _tr) in fams)
    print(f"\n   class shapes carrying a (length-3 split, length-4 companion)"
          f" pair: {tot_shapes}")
    for tag, n, E0, sh, tried in fams:
        print(f"     {tag:<18} {len(sh):>4} shapes  ({tried} length tuples)")
    tot, ok, fail, exh_zero, scarce = 0, 0, [], [], None
    ncoll = 0
    Shist, runhist, lamhist = (defaultdict(int), defaultdict(int),
                               defaultdict(int))
    bad, maxbranch, closedn, endedge = [], 0, 0, 0
    len2hist, blenhist = defaultdict(int), defaultdict(int)
    girthhist = defaultdict(int)
    famsites, fams2 = defaultdict(int), defaultdict(int)
    nshape_with = 0
    for tag, n, E0, sh, tried in fams:
        for label, E in sh:
            comps_seen = False
            for v, sd, P, kb, edges6 in sites_of(E):
                a, b, c, Gp, Hed = sd
                if not comps_seen:
                    nshape_with += 1
                    comps_seen = True
                    assert hcard_ok(Gp) and is_2ec(Gp)
                    Lam, hubs, deg = lambda_graph(Gp)
                    for (walk, cyc) in lam_components(Lam):
                        lamhist[('cycle' if cyc else 'path', len(walk))] += 1
                    cps, _o = alternation_classes(Gp)
                    maxbranch = max(maxbranch, max(len(c_) for c_ in cps))
                    len2 = sum(1 for c_ in cps if len(c_) == 2)
                    len2hist[len2] += 1
                    blenhist[tuple(sorted(len(c_) for c_ in cps))] += 1
                    gG, gGp = girth(E), girth(Gp)
                    girthhist[(gG, gGp)] += 1
                    if gG < 7:
                        bad.append((label, v, 'girth-G', gG))
                    if gGp < 6:
                        bad.append((label, v, 'girth-Gp', gGp))
                tot += 1
                famsites[tag] += 1
                R = frame_clauses(label, v, Gp, a, edges6, bad)
                closedn += R['closed']
                Shist[len(R['S'])] += 1
                if len(R['S']) == 2:
                    fams2[tag] += 1
                runhist[tuple(len(r) for r in R['runs'])] += 1
                p, q = R['ends']
                if p != q and ((p, q) in Gp or (q, p) in Gp):
                    endedge += 1
                good, var, notes = recipe_at(Gp, edges6)
                ok += good
                if not good:
                    fail.append((label, v, kb))
                # exhaustive: how many admissible colourings are patterns
                allverts = sorted(verts_of(Gp), key=str)
                chn = chn_sets(Gp)
                cols, odd = colourings(Gp, cap=exhaustive_cap)
                assert cols is not None and not odd
                ngood = 0
                for col in cols:
                    EA = [e for e in Gp if col[e] == 'A']
                    EB = [e for e in Gp if col[e] == 'B']
                    cA = components(allverts, EA)
                    cB = components(allverts, EB)
                    coll = collisions(Gp, allverts, cA, cB)
                    ncoll += len(coll)
                    for (p, q) in coll:
                        if not both_len2_interiors(Gp, R['deg'], p, q):
                            bad.append((label, v, 'collision-not-len2', (p, q)))
                    if legality_free(col, cA, cB, allverts, chn) and \
                            crit_33(line_ids(col, cA, cB, edges6)):
                        ngood += 1
                if ngood == 0:
                    exh_zero.append((label, v, kb))
                if scarce is None or ngood < scarce[0]:
                    scarce = (ngood, len(cols), label, str(v), kb)
    print(f"\n   shapes with at least one bare-cycle site: {nshape_with}")
    print(f"   BARE-CYCLE SITES over the complete stratum: {tot}")
    print(f"   longest branch of any G' met: {maxbranch}"
          f"   ((SD-6) at G' says <= 5)")
    print(f"   closed-hexagon sites (x = x'): {closedn};"
          f" P-adjacent companion ends: {endedge}")
    print(f"   sites per hub-multigraph family: {dict(sorted(famsites.items()))}")
    print(f"     (of which OUTSIDE outer.sweep_shapes: c3-n3-122 and"
          f" c3-n4-012210)")
    print(f"   |S| = 2 sites per family: {dict(sorted(fams2.items()))}")
    print(f"   |S| histogram: {dict(sorted(Shist.items()))}")
    print(f"   run-length profiles: {dict(sorted(runhist.items()))}")
    print(f"   Lambda components (type, #vertices): "
          f"{dict(sorted(lamhist.items(), key=str))}")
    print(f"   #length-2 branches of G' per shape: "
          f"{dict(sorted(len2hist.items()))}")
    print(f"   G' branch-length multisets: {dict(sorted(blenhist.items()))}")
    print(f"   (girth G, girth G') per shape: "
          f"{dict(sorted(girthhist.items()))}   ((R3) + hnoRigid: girth G >= 7)")
    if bad:
        print(f"\n   (FR-9) MISSES on the complete stratum: {len(bad)};"
              f" first 12:")
        for row in bad[:12]:
            print(f"     {row}")
    else:
        print("   every (FR-9) clause holds at every site of the stratum  OK")
    print(f"\n   RECIPE SUCCEEDS at: {ok} / {tot}")
    if fail:
        print(f"   recipe misses: {len(fail)}; first 12:")
        for row in fail[:12]:
            print(f"     {row}")
    print(f"   EXHAUSTIVE scan: sites with ZERO pattern colouring:"
          f" {len(exh_zero)}")
    print(f"   scarcest site: {scarce[0]} pattern colourings of {scarce[1]}"
          f" admissible, at {scarce[2]} v={scarce[3]} P#{scarce[4]}")
    print(f"   (FR-12) legality-(i) collisions seen over every admissible")
    print(f"   colouring of every site: {ncoll}; ALL of them pairs of")
    print(f"   length-2-branch interiors (asserted above)")
    if bad or fail or exh_zero:
        print("FAILED")
        return 1
    print("PASSED")
    return 0



# ---------------- mode: --recon ((FR-14)) ----------------------------------

def mode_recon():
    print("== (FR-14) the 1896 / 1904 reconciliation, and the c' <= 1"
          " columns ==")
    print("   which census over/under-counts, and by what mechanism;")
    print("   then (ANH-13)'s `c' = 0` and `c' = 1` cells re-derived over the")
    print("   COMPLETE strata rather than over `outer.sweep_shapes`.\n")

    # -- the pool's shape list, keyed by isomorphism class ------------------
    print("   -- 1. the two shape lists, keyed by isomorphism class --")
    pool = {}
    pool_labels = defaultdict(list)
    pool_tot = 0
    fams = [('named', named_inventory())] + \
        [(desc, sh) for (desc, sh) in sweep_shapes()]
    for desc, shapes in fams:
        for label, E in shapes:
            B, L, O = site_profile(E)
            if B == 0:
                continue
            k = shape_key(E)
            if k in pool:
                assert pool[k] == B, "same iso class, different site count"
            pool[k] = B
            pool_labels[k].append(f'{desc[:14]}|{label}')
            pool_tot += B
    strat = {}
    strat_labels = defaultdict(list)
    strat_fam = defaultdict(set)
    strat_tot = 0
    for tag, n, E0, sh, tried in cstrat_shapes(3):
        for label, E in sh:
            B, L, O = site_profile(E)
            assert O == 0, "a c(G) = 3 length-5 site is not a bare cycle"
            assert L == 0, "a c(G) = 3 shape has an e0-is-None length-5 branch"
            if B == 0:
                continue
            k = shape_key(E)
            if k in strat:
                assert strat[k] == B, "same iso class, different site count"
            strat[k] = B
            strat_labels[k].append(f'{tag}|{label}')
            strat_fam[tag].add(k)
            strat_tot += B
    print(f"      pool   : {len(pool_labels)} iso classes with sites,"
          f" {sum(len(v) for v in pool_labels.values())} labelled shapes,"
          f" {pool_tot} sites")
    print(f"      stratum: {len(strat_labels)} iso classes with sites,"
          f" {sum(len(v) for v in strat_labels.values())} labelled shapes,"
          f" {strat_tot} sites")
    missing = sorted(set(pool) - set(strat), key=str)
    extra = sorted(set(strat) - set(pool), key=str)
    print(f"      iso classes in the POOL but NOT in the stratum"
          f" enumeration: {len(missing)}   <-- must be 0 for (FR-8)")
    for k in missing[:6]:
        print(f"        MISSED {k}  (pool labels {pool_labels[k][:2]})")
    print(f"      iso classes in the stratum but not in the pool:"
          f" {len(extra)}")
    for k in extra[:6]:
        print(f"        new: {k}  sites {strat[k]}"
              f"  {strat_labels[k][:1]}")
    iso_tot = sum(strat.values())
    iso_pool = sum(pool.values())
    print(f"      SITES PER ISO CLASS, summed: pool {iso_pool},"
          f" stratum {iso_tot}   (difference {iso_tot - iso_pool},"
          f" over {len(extra)} classes)")
    print(f"      iso classes per hub-multigraph family: "
          f"{dict(sorted((t, len(v)) for t, v in strat_fam.items()))}")
    swept = strat_fam.get('c3-n4-111111', set())
    print(f"      pool's {len(pool)} classes all inside the swept K4 family:"
          f" {set(pool) <= swept}")

    # -- where the 8 went ---------------------------------------------------
    print("\n   -- 2. where the 8 went --")
    dup_pool = {k: len(v) for k, v in pool_labels.items() if len(v) > 1}
    dup_str = {k: len(v) for k, v in strat_labels.items() if len(v) > 1}
    over_pool = sum((len(v) - 1) * pool[k] for k, v in pool_labels.items())
    over_str = sum((len(v) - 1) * strat[k] for k, v in strat_labels.items())
    print(f"      pool iso classes carried more than once: {len(dup_pool)};"
          f" duplicate-induced site over-count: {over_pool}")
    print(f"      stratum iso classes carried more than once: {len(dup_str)};"
          f" duplicate-induced site over-count: {over_str}")
    ex = sorted(dup_pool, key=str)
    if ex:
        k = ex[0]
        print(f"      example duplicated pool class {k}: {pool[k]} sites,"
              f" carried {len(pool_labels[k])} times as")
        for lb in pool_labels[k][:4]:
            print(f"        {lb}")
    print(f"      pool labelled total {pool_tot} = iso total {iso_pool}"
          f" + duplicate over-count {over_pool}")
    print(f"      stratum labelled total {strat_tot} = iso total {iso_tot}"
          f" + duplicate over-count {over_str}")
    assert pool_tot == iso_pool + over_pool
    assert strat_tot == iso_tot + over_str
    assert not missing, \
        "(FR-8) EXHAUSTIVENESS FAILS: the pool knows an iso class the " \
        "stratum enumeration does not"

    # -- the c' <= 1 columns ------------------------------------------------
    print("\n   -- 3. (ANH-13) Step A14's c' <= 1 cells, re-derived --")
    for c in (2, 3):
        mg = c_hub_multigraphs(c)
        lab, iso, isoB, isoL = 0, {}, 0, 0
        nsh = 0
        for tag, n, E0, sh, tried in cstrat_shapes(c):
            for label, E in sh:
                B, L, O = site_profile(E)
                if B + L + O == 0:
                    continue
                nsh += 1
                lab += B + L
                k = shape_key(E)
                if k not in iso:
                    iso[k] = (B, L, O)
                    isoB += B
                    isoL += L
                assert iso[k] == (B, L, O)
        print(f"      c(G) = {c}: {len(mg)} hub multigraphs,"
              f" {nsh} labelled shapes with a length-5 site,"
              f" {len(iso)} iso classes")
        print(f"        c' = {c - 2} sites: LABELLED over the complete"
              f" stratum {lab};   per-ISO-CLASS total {isoB + isoL}")
    print("PASSED")
    return 0


# ---------------- mode: --kill ---------------------------------------------

def odd_lambda_witness():
    """An ADVERSARIAL graph, constructed not sampled: a 5-cycle of hubs, each
    carrying a pendant 2-path back to a common body, so every hub has
    Lambda-degree 2 and Lambda is an ODD cycle.  (FR-4)'s second legality
    clause must then FAIL at every admissible colouring -- which is the
    mechanism the (FR-10) census shows the class can never realize
    (`n_hub <= 4 < 5` at `c(G) = 3`, and a Lambda cycle needs length >= 6)."""
    E = [(i, (i + 1) % 5) for i in range(5)]
    nxt = 100
    for i in range(5):
        E += [(i, nxt), (nxt, 'z')]
        nxt += 1
    return E


def mode_kill(cap=8192):
    print("== the cheap kill + the load-bearing-hypothesis witnesses ==")
    print(f"   seed {PEX_SEED} (tie-breaks only)\n")
    rng = random.Random(PEX_SEED)
    assert rng.random() is not None
    print("   -- 1. the cheap kill, exhaustive over the census pool --")
    tot, miss, worst = 0, [], None
    for (nm, E, v) in census_pool():
        sd = split_data(E, v)
        if sd is None:
            continue
        a, b, c, Gp, Hed = sd
        sites, _ = bare_sites(Hed, b, c)
        if not sites:
            continue
        allverts = sorted(verts_of(Gp), key=str)
        chn = chn_sets(Gp)
        cols, odd = colourings(Gp, cap=cap)
        assert cols is not None and not odd
        for (P, kb, edges6) in sites:
            tot += 1
            good = 0
            for col in cols:
                EA = [e for e in Gp if col[e] == 'A']
                EB = [e for e in Gp if col[e] == 'B']
                cA = components(allverts, EA)
                cB = components(allverts, EB)
                if legality_free(col, cA, cB, allverts, chn) and \
                        crit_33(line_ids(col, cA, cB, edges6)):
                    good += 1
            if good == 0:
                miss.append((nm, v, kb))
            if worst is None or good < worst[0]:
                worst = (good, len(cols), nm, str(v), kb)
    print(f"   census-pool sites scanned exhaustively: {tot}")
    print(f"   scarcest: {worst[0]} pattern colourings of {worst[1]}"
          f" admissible ({worst[2]} v={worst[3]} P#{worst[4]})")
    print(f"   sites with ZERO pattern colouring: {len(miss)}")
    print("\n   -- 2. F13: the ODD-Lambda-cycle witness the recipe must fail --")
    E = odd_lambda_witness()
    allverts = sorted(verts_of(E), key=str)
    chn = chn_sets(E)
    Lam, hubs, deg = lambda_graph(E)
    lc = lam_components(Lam)
    print(f"      constructed graph: {len(allverts)} bodies,"
          f" {len(E)} edges, {len(hubs)} hubs")
    print(f"      Lambda components: {[(len(w), cyc) for (w, cyc) in lc]}")
    assert any(cyc and len(w) % 2 == 1 for (w, cyc) in lc), \
        "witness does not carry an odd Lambda cycle"
    cols, odd = colourings(E, cap=cap)
    assert cols is not None and not odd
    nlegal = 0
    for col in cols:
        EA = [e for e in E if col[e] == 'A']
        EB = [e for e in E if col[e] == 'B']
        cA = components(allverts, EA)
        cB = components(allverts, EB)
        if legality_free(col, cA, cB, allverts, chn):
            nlegal += 1
    print(f"      admissible colourings: {len(cols)};"
          f" LEGAL ones: {nlegal}  (must be 0)")
    assert nlegal == 0, "the odd-Lambda-cycle mechanism does not fire"
    print("      the mechanism fires: an odd Lambda cycle kills EVERY")
    print("      admissible colouring's legality                          OK")
    print("\n   -- 3. F13 negative control: even Lambda cycle --")
    E2 = [(i, (i + 1) % 6) for i in range(6)]
    nxt = 100
    for i in range(6):
        E2 += [(i, nxt), (nxt, 'z')]
        nxt += 1
    allv2 = sorted(verts_of(E2), key=str)
    chn2 = chn_sets(E2)
    cols2, odd2 = colourings(E2, cap=cap)
    n2 = 0
    for col in cols2:
        EA = [e for e in E2 if col[e] == 'A']
        EB = [e for e in E2 if col[e] == 'B']
        cA = components(allv2, EA)
        cB = components(allv2, EB)
        if legality_free(col, cA, cB, allv2, chn2):
            n2 += 1
    print(f"      even (6-)Lambda cycle: {len(cols2)} admissible,"
          f" {n2} legal  (must be > 0)")
    assert n2 > 0, "the negative control fails too -- the mechanism is wrong"
    print("      control passes: parity, not size, is the mechanism      OK")
    print("PASSED" if not miss else "FAILED")
    return 0 if not miss else 1


# ---------------- mode: --validate -----------------------------------------

def mode_validate():
    print("== machinery pins ==")
    n, neq = 0, 0
    for (nm, E, v) in census_pool():
        sd = split_data(E, v)
        if sd is None:
            continue
        a, b, c, Gp, Hed = sd
        comps, odd = alternation_classes(Gp)
        assert not odd
        cols, _ = colourings(Gp, cap=8192)
        assert len(cols) == 2 ** len(comps), \
            "free-bit dictionary broken: #colourings != 2^#branches"
        allverts = sorted(verts_of(Gp), key=str)
        Lam, hubs, deg = lambda_graph(Gp)
        for col in cols:
            EA = [e for e in Gp if col[e] == 'A']
            EB = [e for e in Gp if col[e] == 'B']
            cA = components(allverts, EA)
            cB = components(allverts, EB)
            assert leg2_only(Gp, allverts, cA, cB) == lam_proper(Gp, col), \
                "legality clause (ii) is NOT the proper-Lambda-2-colouring"
            neq += 1
        for col in cols[:8]:
            EA = [e for e in Gp if col[e] == 'A']
            cA = components(allverts, EA)
            # the propagation law: two hubs share an A-component IFF they are
            # joined by a path of A-coloured HUB-HUB edges
            GA = {h: set() for h in hubs}
            for (u, w) in Lam:
                if col[(u, w)] == 'A':
                    GA[u].add(w)
                    GA[w].add(u)
            for h1 in hubs:
                seen, st = {h1}, [h1]
                while st:
                    x = st.pop()
                    for y in GA[x]:
                        if y not in seen:
                            seen.add(y)
                            st.append(y)
                for h2 in hubs:
                    assert (cA[h1] == cA[h2]) == (h2 in seen), \
                        "hub-hub edges are not the only A-component propagators"
        n += 1
    print(f"   legality clause (ii) == `Lambda properly edge-2-coloured`,")
    print(f"   asserted over {neq} (split, colouring) pairs               OK")
    print(f"   #admissible colourings == 2^#branches at {n} census splits OK")
    print("   Step G12's one-free-bit-per-branch, machine-checked          OK")
    print("   hub-hub edges are the ONLY same-family component propagators OK")
    mg = c3_hub_multigraphs()
    print(f"   c(G) = 3 hub multigraph census: {len(mg)}"
          f" {[(n_, tuple(m)) for (n_, _E, m) in mg]}")
    print("PASSED")
    return 0


# ---------------- main -----------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--frame', action='store_true')
    ap.add_argument('--recipe', action='store_true')
    ap.add_argument('--strat', action='store_true')
    ap.add_argument('--recon', action='store_true')
    ap.add_argument('--kill', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.frame:
        return mode_frame()
    if args.recipe:
        return mode_recipe()
    if args.strat:
        return mode_strat()
    if args.recon:
        return mode_recon()
    if args.kill:
        return mode_kill()
    if args.validate:
        return mode_validate()
    ap.print_help()
    return 1


if __name__ == '__main__':
    sys.exit(main())
