"""§(K-grid) research direction GFORCE (2026-09-10) driver — (GR-177)-(GR-184):
do the (GR-16)(a)/(b) FORCING HANDLES of *Step G19* close into a propagation
scheme whose termination hypothesis is combinatorial and sufficient for
`dim Z = 0`, with no (GR-4'), no min-max and no certificate?

A `w4/` leaf beside `gridcol.py` / `gcoind.py`, importing `gridcol.py` /
`gridwit.py` / `grid.py` / `packmm.py` / `gcoind.py` / `closure.py` READ-ONLY
(README §2; same precedent as gcoind -> gridcol -> packmm -> gridwit -> grid).
Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --sound   # (GR-177) the reduction and the closure are SOUND
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --sep     # (GR-178) the first slice: the fixpoint at the 18 separators
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --sat     # (GR-179) no support case-split strengthens the fixpoint
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --pool    # (GR-180) coverage over the census pool, and against (GR-9)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --tt      # (GR-181) the kill branch: is success the tree-triple restated?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --kappa   # (GR-182) the sibling question: is the UNCONSTRAINED triple sufficient?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --rank3   # (GR-183) the THIRD handle (c) and its four determinant patterns
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --strat   # (GR-184) where the scheme still stops
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gforce.py --validate

Argument state: session draft `notes/Pencil-draft-GFORCE.md` (to be merged into
`notes/pencil/workbook/grid.md` §(K-grid) as *Steps G197-G204*; labels
(GR-177)-(GR-184) per the 2026-09-10 GFORCE reservation in
`notes/pencil/labels.md`).

WHAT IS NEW HERE, in one paragraph.  *Step G19* closes with "Neither is used
below; both are the natural handles for a future uniform argument", so the two
handles have never been RUN.  This driver runs them.  Handle (a) —
`|K_A(beta)| = 3` forces `Q_beta = 0` — is an INITIALISATION; handle (b) —
evaluating the hub relation at `t_{star_A(v)}` kills every A-end branch at `v`
and so forces an extra root on the last surviving B-end branch — is a
PROPAGATION STEP.  Together they define a monotone closure operator on the
table `S[beta] subset {classes}` of KNOWN ROOTS of `Q_beta`, run to a fixpoint;
the termination hypothesis is *the surviving branches carry no cycle*, and it
mentions no parameter.  FOUR strengths are implemented, because the
differences between them turn out to carry the whole verdict:

  * `leaf` — the LITERAL (b) of *Step G19*: at a hub of the support with
    exactly one surviving incident branch, that branch gains the root.
    Iterated to a fixpoint inside one round (which is iterated leaf-stripping).
  * `cut`  — `leaf` plus its own cut-space completion: a branch that is a
    COLOOP of the support carries no cycle flow, so it gains the root.  This is
    the same hub relation summed over one side of the cut, not a new input.
  * `full` — `cut` plus SERIES MERGING: at a node of the surviving subgraph
    with exactly two surviving branches, the hub relation reads
    `eps_b Q_b + eps_g Q_g = 0`, so the two share a root set.  This is
    (GR-16)(ii)'s "constant along a branch" re-applied to the SHRINKING
    surviving subgraph, and it is what makes handle (a) fire more than once.
  * `gen`  — `full` plus a THIRD handle (c), which is NOT in *Step G19*: at a
    node whose surviving incident branches are exactly three and all three
    already carry two roots, the hub identity is three equations in three
    unknowns and the three monic quadratics are independent whenever their
    root-PAIRS are pairwise distinct with empty common intersection, so all
    three branches die.  `--rank3` proves the independence by exhausting the
    four possible intersection patterns.  This mode is reported separately
    everywhere, because the (a)/(b) question is answered by `full` and the
    ROUTE question is answered by `gen`.

WHAT EACH MODE TESTS, one sentence each (README §4 / F11: the driver tests the
exact headline sentence).

--sound   (GR-177): the degree-2-suppressed hub model this driver builds from
          `bd` alone has cycle rank `bd['h']` and computes exactly the landed
          `gridwit.dim_W` at seeded exact-ℚ draws, and every closure the
          propagation reaches is SOUND — `residual = 0` implies the landed
          generic `dim Z` is 0, with 0 counterexamples over the swept
          population, for BOTH `full` and `gen`.

--sep     (GR-178): the first slice — the fixpoint at all 18 habitat
          separators of `gridcol.SEP_SHAPES`, per separator and per strength
          (`leaf` / `cut` / `full` / `gen`), against the exact `dim_W`.

--sat     (GR-179): no case split over candidate SUPPORTS strengthens the
          fixpoint — the surviving set at the `cut`/`full` fixpoint is itself
          a feasible support, so `exists a feasible Sigma` and `residual > 0`
          are the same statement; asserted at every separator and over the
          `--pool` population.

--pool    (GR-180): coverage — over the balanced filter-passing blocks of the
          census pool (capped), how often each strength certifies, split by
          whether the block carries a CLASS-RESPECTING tree-triple, so that
          "stronger than (GR-9)" is a signed count in both directions and not
          an adjective.

--tt      (GR-181): the direction's own kill branch — every certifying block
          carries an UNCONSTRAINED tree-triple (`gcoind.
          unconstrained_tree_triple`, as (GR-165) forces), and the mode counts
          the blocks that carry one WITHOUT the scheme certifying, which is
          what refutes "the scheme is the triple condition restated".

--kappa   (GR-182): §8's rank-3 twin, which this direction answers as a
          by-product — is the unconstrained tree-triple SUFFICIENT for
          `kappa < infinity`?  The mode counts blocks with a PROVEN (GR-8)
          lower bound `g(P) >= 1` (hence generic `dim Z > 0`, hence
          `kappa = infinity` by (GR-19)(iv)) that nevertheless carry an
          unconstrained tree-triple, and pins one witness.

--rank3   (GR-183): the third handle (c) is a THEOREM — three monic quadratics
          `R_j = prod_{X in S_j}(t - t_X)` with `|S_j| = 2` are linearly
          independent in `K[t]_{<=2}` whenever the pairs are pairwise distinct
          with empty common intersection; the mode exhausts the four possible
          pairwise-intersection patterns and evaluates the determinant in
          exact ℚ at seeded draws, and reports what (c) buys at the separators
          and on the pool.

--strat   (GR-184): where the scheme still stops — the residual blocks'
          combinatorial signature, reported as the count of surviving hubs at
          which every surviving branch carries the hub's own star class, which
          is exactly the configuration at which handle (b) is vacuous.

Exact throughout (`fractions.Fraction`; no floating point).  Ranks are exact ℚ
via the landed `gridwit.dim_W` / `gridcol.dim_W_branch`; this driver adds no
linear algebra of its own — the propagation is pure graph combinatorics on the
class incidence table, which is the whole point of the question.  Every rng is
seeded from `GF_SEED` and the seed is printed; no `set` is printed.

CAPS, disclosed here and re-printed by each mode that runs under one:
  * `--sep` runs the 18 separators, which live on exactly TWO carrier shapes
    (`gridcol.SEP_SHAPES`): `V6m10(3^10)` and `V6m11(3^8, 4^3)`.  "18/18" is
    therefore a statement about two graphs, and is reported that way.
  * `--pool` walks `gridcol.pool_shapes(shape_cap)` with `closure.colourings`
    under `col_cap`, and takes at most `per_shape` filter-passing colourings
    per shape; all three caps are printed with the figure.
  * `--tt`'s cobase / Edmonds enumerations are the landed `gcoind` ones and are
    EXHAUSTIVE over `C(m, h)` resp. `2^m`; `--tt`'s converse hunt is capped by
    the same `--pool` caps and reports "not found under cap C", never
    "does not exist".
  * `--kappa`'s (GR-8) bound is maximised over WHOLE-BRANCH sub-multigraphs
    only (`2^{#branches}`, exhaustive under `sub_cap`), which is a SUBFAMILY
    of `H_+`'s sub-multigraphs: `g(P) >= 1` is therefore a proof, and
    `g(P) = 0` is "no (GR-8) witness in this subfamily", never "dim W = 0".
  * `dim_Z_generic(b, rng, draws=k)` is a MINIMUM over `k` seeded draws, so
    `= 0` proves generic `dim Z = 0` and `> 0` reports only "not attained
    under `k` draws"; wherever this driver states generic `dim Z > 0` as a
    fact it carries a (GR-8) `g(P) >= 1` beside it.
  * no value sampling decides anything combinatorial here: the propagation is
    parameter-free by construction, and every parameter draw is used only to
    CHECK a landed exact-ℚ dimension.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import closure                                                        # noqa: E402
from closure import colourings, combinatorial_filter                  # noqa: E402
from kbare_common import verts_of                                     # noqa: E402
from grid import block_data, dim_Z_generic                            # noqa: E402
from gridwit import dim_W                                             # noqa: E402
from packmm import comp_count_nodes, fast_triple                      # noqa: E402
from gridcol import (SEP_SHAPES, branch_classes,                      # noqa: E402
                     dim_W_branch, pool_shapes)
from gcoind import separator_blocks, unconstrained_tree_triple        # noqa: E402

GF_SEED = 20260910


# ------------------------------------------------------------- primitives ---

def _comp(nodes, ends, live):
    """Component count of the sub-multigraph of (nodes, ends) on edge index
    set `live`.  Thin wrapper on the landed `packmm.comp_count_nodes` so the
    propagation never re-implements union-find."""
    return comp_count_nodes(nodes, [ends[k] for k in sorted(live)])


def cycle_rank(nodes, ends, live):
    """|live| - |nodes| + comp -- the cycle rank of the surviving subgraph.
    This is the driver's TERMINATION STATISTIC: 0 means the survivors carry no
    cycle, hence every `Q in W` supported on them is 0."""
    return len(live) - len(nodes) + _comp(nodes, ends, live)


def coloops(nodes, ends, live):
    """The coloops (bridges) of the sub-multigraph on `live`: edges lying on no
    cycle of it.  A loop is never a coloop."""
    base = _comp(nodes, ends, live)
    out = set()
    for k in live:
        u, w = ends[k]
        if u == w:
            continue
        if _comp(nodes, ends, live - {k}) > base:
            out.add(k)
    return out


def leaves(nodes, ends, live):
    """Iterated leaf-stripping: the edges removed when repeatedly deleting an
    edge that is the ONLY surviving edge at some node.  This is the LITERAL
    (GR-16)(b) — one hub, one surviving incident branch — run to its own
    fixpoint."""
    cur, removed = set(live), set()
    while True:
        deg = {v: 0 for v in nodes}
        for k in cur:
            u, w = ends[k]
            deg[u] += 1
            deg[w] += 1          # a loop contributes 2 at its node
        hit = None
        for v in nodes:
            if deg[v] != 1:
                continue
            inc = [k for k in cur if v in ends[k]]
            assert len(inc) == 1
            hit = inc[0]
            break
        if hit is None:
            return removed
        cur.discard(hit)
        removed.add(hit)


def forced_zero(nodes, ends, live, mode):
    """Which edges of `live` are forced to zero by the hub relations alone.

    `leaf` = the literal (GR-16)(b) fixpoint; `cut`/`full` = its cut-space
    completion (a coloop carries no cycle flow).  Both are consequences of
    `Q in C(G-degree)`; neither uses a parameter value."""
    if mode == 'leaf':
        return leaves(nodes, ends, live)
    return coloops(nodes, ends, live) | leaves(nodes, ends, live)


# --------------------------------------------- the degree-2-suppressed model -

def hub_model(bd):
    """The branch model of one block, derived from `bd` ALONE.

    `H_+` is `(bd['nodes'], bd['ced'])` with class `bd['cls'][k]` on edge `k`.
    Cycle vectors of `H_+` are constant (up to sign) along any maximal path of
    degree-2 nodes, so suppressing those nodes loses nothing and is exactly
    (GR-16)(ii) read backwards: at `Lambda = empty` the suppressed graph IS the
    hub multigraph `G-degree` and a super-edge IS a branch, carrying the union
    of the classes met along it.

    Returns (hnodes, ends, cls_sets, paths) with `paths[j]` the `bd` edge
    indices along super-edge `j` (so `cls_sets[j] = K_A(beta_j)`).
    Local device (README rule 3): `gridcol.branch_decomp` needs the UNCONTRACTED
    `edges` of `G` plus its hub set, which `separator_blocks()` does not return;
    this one works inside `H_+`.  `--sound` asserts the two agree wherever both
    are available."""
    nodes, ced, cls = bd['nodes'], bd['ced'], bd['cls']
    deg = {v: 0 for v in nodes}
    inc = {v: [] for v in nodes}
    for k, (u, w) in enumerate(ced):
        deg[u] += 1
        deg[w] += 1
        inc[u].append(k)
        inc[w].append(k)
    hset = {v for v in nodes if deg[v] != 2}
    # a component that is a bare cycle has no node of degree != 2: pin one
    seen = set()
    for v in nodes:
        if v in seen or v in hset:
            continue
        comp, stack = set(), [v]
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x)
            for k in inc[x]:
                a, b = ced[k]
                stack.append(b if a == x else a)
        seen |= comp
        if not (comp & hset):
            hset.add(min(comp, key=str))
    hnodes = sorted(hset, key=str)
    used, ends, paths = set(), [], []
    for h in hnodes:
        for k0 in inc[h]:
            if k0 in used:
                continue
            used.add(k0)
            path = [k0]
            a, b = ced[k0]
            cur = b if a == h else a
            if a == b:                      # a loop at h
                ends.append((h, h))
                paths.append(path)
                continue
            while cur not in hset:
                nxt = [k for k in inc[cur] if k not in used]
                assert len(nxt) == 1, "degree-2 node with != 2 edges"
                k = nxt[0]
                used.add(k)
                path.append(k)
                a, b = ced[k]
                cur = b if a == cur else a
            ends.append((h, cur))
            paths.append(path)
    assert len(used) == len(ced), "suppression lost an edge"
    cls_sets = [frozenset(cls[k] for k in p) for p in paths]
    return hnodes, ends, cls_sets, paths


# ------------------------------------------------------------ the closure ---

def propagate(hnodes, ends, cls_sets, mode='full', trace=False):
    """The (GR-16)(a)/(b) closure, run to a fixpoint.

    State: `S[j]` = the known roots of `Q_j` (a set of class ids), `dead` = the
    branches known to be identically zero.  Rules, all parameter-free:

      (a)  |S[j]| >= 3  ==>  j is dead        (deg Q <= 2, distinct classes
                                               carry distinct parameters)
      (b)  j forced to zero in the SUPPORT of class X  ==>  X enters S[j]
      (z)  j forced to zero in the SURVIVING subgraph  ==>  j is dead
      (s)  `full` only: two survivors meeting at a node of surviving degree 2
           share a root set

    Returns a dict with the fixpoint, the residual cycle rank of the survivors
    (the TERMINATION STATISTIC — 0 certifies `dim W = 0`), and the round count.
    """
    n = len(ends)
    S = [set(c) for c in cls_sets]
    dead = {j for j in range(n) if len(S[j]) >= 3}
    classes = sorted({c for cs in cls_sets for c in cs})
    rounds = 0
    log = []
    while True:
        rounds += 1
        before = (frozenset(dead), tuple(frozenset(s) for s in S))
        alive = set(range(n)) - dead
        # (z) survivors that carry no cycle flow at all
        dead |= forced_zero(hnodes, ends, alive, mode)
        alive = set(range(n)) - dead
        # (s) series merging on the surviving subgraph
        if mode in ('full', 'gen'):
            while True:
                deg = {v: [] for v in hnodes}
                for k in alive:
                    u, w = ends[k]
                    deg[u].append(k)
                    deg[w].append(k)
                merged = False
                for v in hnodes:
                    ks = deg[v]
                    if len(ks) == 2 and ks[0] != ks[1]:
                        a, b = ks
                        u = S[a] | S[b]
                        if u != S[a] or u != S[b]:
                            S[a] = set(u)
                            S[b] = set(u)
                            merged = True
                if not merged:
                    break
                nd = {j for j in alive if len(S[j]) >= 3}
                if nd:
                    dead |= nd
                    alive = set(range(n)) - dead
        # (g) `gen` only: the LOCAL RANK rule -- a THIRD handle, not (a)/(b).
        #     At a node whose surviving incident branches are exactly three
        #     and all three already carry two roots, the hub identity reads
        #     `sum_i eps_i c_i R_i(t) = 0` with `R_i` monic quadratic, i.e.
        #     three equations in three unknowns; `R_1, R_2, R_3` are linearly
        #     independent in `K[t]_{<=2}` whenever the three root-PAIRS are
        #     pairwise distinct and have empty common intersection (the four
        #     intersection patterns are checked exactly by `--rank3`), so all
        #     three `c_i` vanish and all three branches die.
        if mode == 'gen':
            deg = {v: [] for v in hnodes}
            for k in alive:
                u, w = ends[k]
                deg[u].append(k)
                deg[w].append(k)
            for v in hnodes:
                ks = [k for k in deg[v] if k in alive]
                if len(ks) != 3 or len(set(ks)) != 3:
                    continue
                if any(len(S[k]) != 2 for k in ks):
                    continue
                ps = [frozenset(S[k]) for k in ks]
                if len(set(ps)) != 3:
                    continue
                if ps[0] & ps[1] & ps[2]:
                    continue
                dead |= set(ks)
                alive = set(range(n)) - dead
        # (b) one support per class
        for X in classes:
            supp = {j for j in alive if X not in S[j]}
            for j in forced_zero(hnodes, ends, supp, mode):
                S[j].add(X)
        # (a) three roots kill a quadratic
        dead |= {j for j in range(n) if len(S[j]) >= 3}
        after = (frozenset(dead), tuple(frozenset(s) for s in S))
        if trace:
            log.append((rounds, len(dead),
                        cycle_rank(hnodes, ends, set(range(n)) - dead)))
        if after == before:
            break
    alive = set(range(n)) - dead
    return dict(dead=sorted(dead), alive=sorted(alive), S=[sorted(s) for s in S],
                residual=cycle_rank(hnodes, ends, alive), rounds=rounds - 1,
                log=log)


def certifies(bd, mode='full'):
    """True iff the fixpoint's surviving subgraph carries no cycle."""
    hnodes, ends, cs, _ = hub_model(bd)
    return propagate(hnodes, ends, cs, mode)['residual'] == 0


def feasible_support(hnodes, ends, cls_sets, sigma, mode='full'):
    """Is `sigma` a self-consistent candidate for `supp(Q)` of a nonzero
    `Q in W`?  Runs the same closure with everything OUTSIDE `sigma` declared
    dead; `sigma` is infeasible as soon as the closure kills one of its own
    members.  (GR-179) says this test never certifies more than `propagate`
    does; `--sat` asserts it."""
    n = len(ends)
    dead = set(range(n)) - set(sigma)
    S = [set(c) for c in cls_sets]
    classes = sorted({c for cs in cls_sets for c in cs})
    while True:
        if any(len(S[j]) >= 3 for j in sigma):
            return False
        alive = set(range(n)) - dead
        if not alive:
            return False
        if forced_zero(hnodes, ends, alive, mode) & set(sigma):
            return False
        before = tuple(frozenset(x) for x in S)
        while True:                                   # series merging
            deg = {v: [] for v in hnodes}
            for k in alive:
                u, w = ends[k]
                deg[u].append(k)
                deg[w].append(k)
            merged = False
            for v in hnodes:
                ks = deg[v]
                if len(ks) == 2 and ks[0] != ks[1]:
                    a, b = ks
                    u = S[a] | S[b]
                    if u != S[a] or u != S[b]:
                        S[a], S[b] = set(u), set(u)
                        merged = True
            if not merged:
                break
        if any(len(S[j]) >= 3 for j in sigma):
            return False
        for X in classes:
            supp = {j for j in alive if X not in S[j]}
            for j in forced_zero(hnodes, ends, supp, mode):
                S[j].add(X)
        if any(len(S[j]) >= 3 for j in sigma):
            return False
        if tuple(frozenset(x) for x in S) == before:
            return True


def g8_branch(hnodes, ends, cls_sets, sub_cap=1 << 14):
    """(GR-8) (§(K-grid) *Step G9*, PROVED): `dim W >= g(P) := 3 dim C(P) -
    sum_X r_X(P)` for every sub-multigraph `P` of `H_+`.  Maximised here over
    WHOLE-BRANCH `P` only — a subfamily, so `g >= 1` is a PROOF that generic
    `dim Z > 0` while `g = 0` is only "no witness in this subfamily".
    Returns (best g, the argmax branch set) or (None, None) above `sub_cap`."""
    n = len(ends)
    if (1 << n) > sub_cap:
        return None, None
    classes = sorted({c for cs in cls_sets for c in cs})
    best, arg = 0, None
    for bits in range(1, 1 << n):
        P = {j for j in range(n) if bits >> j & 1}
        cP = cycle_rank(hnodes, ends, P)
        if cP == 0:
            continue
        tot = 0
        for X in classes:
            tot += cP - cycle_rank(hnodes, ends,
                                   {j for j in P if X not in cls_sets[j]})
        if 3 * cP - tot > best:
            best, arg = 3 * cP - tot, sorted(P)
    return best, arg


def local_slack_ok(hnodes, ends, res):
    """Is there a surviving node whose LOCAL unknown count `sum_i (3 -
    |S[beta_i]|)` is at most the 3 equations the hub identity supplies?  If
    not, no local rule of any strength can fire there — (GR-183)'s counting
    half."""
    alive, S = set(res['alive']), res['S']
    deg = {v: [] for v in hnodes}
    for k in alive:
        u, w = ends[k]
        deg[u].append(k)
        deg[w].append(k)
    for v in hnodes:
        ks = deg[v]
        if ks and sum(3 - len(S[k]) for k in ks) <= 3:
            return True
    return False


def star_blocked_hubs(hnodes, ends, cls_sets, res):
    """(GR-184)'s signature: surviving hubs at which EVERY surviving incident
    branch carries one common class — exactly the configuration at which
    handle (b) evaluates to `0 = 0` and handle (c)'s determinant vanishes."""
    alive, S = set(res['alive']), res['S']
    deg = {v: [] for v in hnodes}
    for k in alive:
        u, w = ends[k]
        deg[u].append(k)
        deg[w].append(k)
    out = 0
    for v in hnodes:
        ks = deg[v]
        if len(ks) < 3:
            continue
        common = set(S[ks[0]])
        for k in ks[1:]:
            common &= set(S[k])
        if common:
            out += 1
    return out


# --------------------------------------------------------- the population --

def sweep(shape_cap=None, col_cap=1 << 12, per_shape=6):
    """Yield (label, mine, edges, allverts, bd) for every BALANCED
    filter-passing colouring-block of the census pool under the caps.  The
    gates are `gridcol.leg_hier`'s own, imported: `closure.colourings`,
    `closure.combinatorial_filter`, `closure.build_fixed_config`,
    `grid.block_data`."""
    for label, edges in pool_shapes(shape_cap):
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=col_cap)
        if cols is None or odd:
            continue
        done = 0
        for col in cols:
            if per_shape is not None and done >= per_shape:
                break
            if combinatorial_filter(edges, allverts, col):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            done += 1
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                if 2 * len(bd['E']) != 3 * (bd['n_c'] - 1):
                    continue                       # balance
                yield label, mine, edges, allverts, bd


# ------------------------------------------------------------------ modes --

def leg_sound(shape_cap=None, per_shape=4, draws=2):
    """[GF-1] (GR-177): the reduction and the closure are sound."""
    print(f"[GF-1] (GR-177) reduction + closure soundness (seed "
          f"{GF_SEED + 1}); caps: shapes {shape_cap or 'all 907'}, "
          f"col_cap 4096, per_shape {per_shape}, {draws} exact-ℚ draws")
    rng = random.Random(GF_SEED + 1)
    n = ident = bad_model = bad_full = bad_gen = 0
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        hn, ends, cs, paths = hub_model(bd)
        n += 1
        assert cycle_rank(hn, ends, set(range(len(ends)))) == bd['h'], \
            f"{label}/{mine}: suppressed model has the wrong cycle rank"
        supers = [(u, w, [bd['E'][k] for k in p])
                  for (u, w), p in zip(ends, paths)]
        assert [frozenset(x) for x in branch_classes(bd, supers)] == \
            list(cs), f"{label}/{mine}: super-edge class sets disagree"
        for _ in range(draws):
            sv = {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                  for c in set(bd['cls'])}
            if dim_W_branch(bd, hn, supers, sval=sv) != dim_W(bd, sval=sv):
                bad_model += 1
            ident += 1
        gz = dim_Z_generic(bd, rng, draws=4)
        if propagate(hn, ends, cs, 'full')['residual'] == 0 and gz != 0:
            bad_full += 1
        if propagate(hn, ends, cs, 'gen')['residual'] == 0 and gz != 0:
            bad_gen += 1
    print(f"  balanced filter-passing blocks: {n}")
    print(f"  suppressed model == landed gridwit.dim_W at exact ℚ draws: "
          f"{ident - bad_model}/{ident}")
    print(f"  UNSOUND certificates (residual 0 but generic dim Z > 0): "
          f"full {bad_full}, gen {bad_gen}")
    assert bad_model == 0 and bad_full == 0 and bad_gen == 0
    print()


def leg_sep():
    """[GF-2] (GR-178): the first slice — the fixpoint at the 18 separators."""
    print(f"[GF-2] (GR-178) the (GR-16)(a)/(b) fixpoint at the 18 habitat "
          f"separators")
    print(f"  CAP: the 18 live on exactly TWO carrier shapes "
          f"({' and '.join(SEP_SHAPES)}) -- 18/18 is a statement about two "
          f"graphs")
    tot = {m: 0 for m in ('leaf', 'cut', 'full', 'gen')}
    rows = []
    for i, (label, b) in enumerate(separator_blocks()):
        hn, ends, cs, _ = hub_model(b)
        r = {m: propagate(hn, ends, cs, m) for m in tot}
        assert dim_W(b) == 0, f"separator {i} is not a dim Z = 0 block"
        for m in tot:
            tot[m] += (r[m]['residual'] == 0)
        rows.append((i, label, len(ends), {m: r[m]['residual'] for m in tot}))
        print(f"    {i:2d} {label[:26]:26s} branches {len(ends):2d}  "
              f"residual leaf {r['leaf']['residual']} cut "
              f"{r['cut']['residual']} full {r['full']['residual']} gen "
              f"{r['gen']['residual']}   (exact dim_W = 0)")
    print(f"  certifies: leaf {tot['leaf']}/18, cut {tot['cut']}/18, full "
          f"{tot['full']}/18, gen {tot['gen']}/18")
    assert tot['leaf'] == tot['cut'] == tot['full'] == 4, \
        "the (a)/(b) fixpoint no longer certifies exactly 4 of the 18"
    assert tot['gen'] == 14, "handle (c) no longer lifts 4/18 to 14/18"
    print("  => the two handles of *Step G19* certify 4 of 18; the falsifiable")
    print("     tell of the dispatch (a nonzero residual at at least one")
    print("     separator) FIRED at 14 of them.")
    print()


def leg_sat(shape_cap=60, per_shape=4, branch_cap=14):
    """[GF-3] (GR-179): no support case-split strengthens the fixpoint."""
    print(f"[GF-3] (GR-179) support case-splits buy nothing; caps: "
          f"separators + shapes {shape_cap}, per_shape {per_shape}, "
          f"<= {branch_cap} branches (2^b enumeration)")
    checked = dis = 0
    pop = [(f'sep{i}', b) for i, (_, b) in enumerate(separator_blocks())]
    pop += [(lab, bd) for lab, mine, e, av, bd
            in sweep(shape_cap, per_shape=per_shape)]
    for lab, b in pop:
        hn, ends, cs, _ = hub_model(b)
        nb = len(ends)
        if nb > branch_cap:
            continue
        res = propagate(hn, ends, cs, 'full')
        any_feas = any(feasible_support(hn, ends, cs,
                                        [j for j in range(nb) if bits >> j & 1])
                       for bits in range(1, 1 << nb))
        checked += 1
        if any_feas != (res['residual'] > 0):
            dis += 1
            print(f"    DISAGREEMENT at {lab}: feasible {any_feas}, "
                  f"residual {res['residual']}")
    print(f"  blocks with BOTH the fixpoint and the 2^b support enumeration: "
          f"{checked}; disagreements {dis}")
    assert dis == 0
    print("  => `exists a feasible support` and `residual > 0` coincide: the")
    print("     surviving set at the fixpoint is itself feasible, so the")
    print("     closure is already maximal in this family.")
    print()


def leg_pool(shape_cap=None, per_shape=6):
    """[GF-4] (GR-180): coverage, and the signed comparison with (GR-9)."""
    print(f"[GF-4] (GR-180) coverage on the census pool (seed {GF_SEED + 4}); "
          f"caps: shapes {shape_cap or 'all 907'}, col_cap 4096, per_shape "
          f"{per_shape}, balanced blocks only")
    rng = random.Random(GF_SEED + 4)
    n = 0
    cnt = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        n += 1
        hn, ends, cs, _ = hub_model(bd)
        cf = propagate(hn, ends, cs, 'full')['residual'] == 0
        cg = propagate(hn, ends, cs, 'gen')['residual'] == 0
        tt, capped = fast_triple(bd)
        has_tt = tt is not None and not capped
        gz = dim_Z_generic(bd, rng, draws=4) == 0
        key = (cf, cg, has_tt, gz)
        cnt[key] = cnt.get(key, 0) + 1
    ntt = sum(v for k, v in cnt.items() if k[2])
    nf = sum(v for k, v in cnt.items() if k[0])
    ng = sum(v for k, v in cnt.items() if k[1])
    miss_f = sum(v for k, v in cnt.items() if k[2] and not k[0])
    miss_g = sum(v for k, v in cnt.items() if k[2] and not k[1])
    beyond_f = sum(v for k, v in cnt.items() if k[0] and not k[2])
    beyond_g = sum(v for k, v in cnt.items() if k[1] and not k[2])
    print(f"  balanced filter-passing blocks: {n}")
    print(f"    (GR-9) class-respecting tree-triple : {ntt}")
    print(f"    (a)/(b) fixpoint `full` certifies   : {nf}")
    print(f"    + handle (c), `gen` certifies       : {ng}")
    print(f"    (GR-9) certifies where `full` fails : {miss_f}")
    print(f"    (GR-9) certifies where `gen`  fails : {miss_g}")
    print(f"    `full` certifies where (GR-9) fails : {beyond_f} "
          f"(pool sample; the separators live outside this per_shape cut)")
    print(f"    `gen`  certifies where (GR-9) fails : {beyond_g}")
    for k in sorted(cnt):
        print(f"      full={int(k[0])} gen={int(k[1])} triple={int(k[2])} "
              f"genericZ0={int(k[3])} : {cnt[k]}")
    assert not any(v for k, v in cnt.items() if (k[0] or k[1]) and not k[3]), \
        "a certificate at a block whose generic dim Z was not 0"
    print("  => the (a)/(b) scheme and (GR-9) are INCOMPARABLE: neither")
    print("     condition contains the other.")
    print()


def leg_tt(shape_cap=None, per_shape=6, m_cap=18):
    """[GF-5] (GR-181): the kill branch — success is not the triple restated."""
    print(f"[GF-5] (GR-181) is the scheme the tree-triple restated?  caps: "
          f"shapes {shape_cap or 'all 907'}, per_shape {per_shape}, "
          f"m <= {m_cap} for the EXHAUSTIVE cobase enumeration")
    rng = random.Random(GF_SEED + 5)
    cert = cert_utt = utt_no_cert = skipped = n = 0
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        n += 1
        if len(bd['E']) > m_cap:
            skipped += 1
            continue
        hn, ends, cs, _ = hub_model(bd)
        cg = propagate(hn, ends, cs, 'gen')['residual'] == 0
        utt = unconstrained_tree_triple(bd) is not None
        if cg:
            cert += 1
            cert_utt += utt
        elif utt:
            utt_no_cert += 1
    print(f"  blocks {n} ({skipped} above the m-cap, not enumerated)")
    print(f"  certifying blocks that carry an unconstrained tree-triple: "
          f"{cert_utt}/{cert} -- (GR-165) forces this, and it holds")
    print(f"  blocks carrying an unconstrained tree-triple where the scheme "
          f"does NOT certify: {utt_no_cert}")
    assert cert_utt == cert
    assert utt_no_cert > 0, \
        "no witness separating the scheme from the unconstrained triple"
    print("  => the scheme's success is STRICTLY STRONGER than the")
    print("     unconstrained-triple condition, so it is not that condition")
    print("     restated; with [GF-4] it is INCOMPARABLE with (GR-9).")
    print()


def leg_kappa(shape_cap=None, per_shape=6, m_cap=18):
    """[GF-6] (GR-182): §8's rank-3 twin — is the UNCONSTRAINED tree-triple
    sufficient for `kappa < infinity`?"""
    print(f"[GF-6] (GR-182) is the unconstrained tree-triple SUFFICIENT for "
          f"kappa < infinity?  caps: shapes {shape_cap or 'all 907'}, "
          f"per_shape {per_shape}, m <= {m_cap}, (GR-8) over whole-branch P")
    rng = random.Random(GF_SEED + 6)
    pos = proven = with_utt = 0
    wit = None
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        if dim_Z_generic(bd, rng, draws=4) == 0:
            continue
        pos += 1
        hn, ends, cs, _ = hub_model(bd)
        g, arg = g8_branch(hn, ends, cs)
        if not g:
            continue
        proven += 1
        if len(bd['E']) <= m_cap and unconstrained_tree_triple(bd) is not None:
            with_utt += 1
            if wit is None:
                wit = (label, mine, len(bd['E']), bd['h'], g, arg)
    print(f"  blocks whose generic dim Z was not attained at 0: {pos}")
    print(f"    ... with a PROVEN (GR-8) bound g(P) >= 1 (so kappa = infinity "
          f"by (GR-19)(iv)): {proven}")
    print(f"    ... of those, carrying an UNCONSTRAINED tree-triple: "
          f"{with_utt}")
    print(f"  pinned witness (label, block, m, h, g(P), P): {wit}")
    assert wit is not None and with_utt > 0
    print("  => NO.  The unconstrained tree-triple is NECESSARY ((GR-165))")
    print("     and very far from sufficient.  This answers §8's rank-3")
    print("     entry, which was deliberately not dispatched this round.")
    print()


PATTERNS = (('disjoint pairs', ((1, 2), (3, 4), (5, 6))),
            ('one shared class', ((1, 2), (1, 3), (4, 5))),
            ('two shared, no common', ((1, 2), (1, 3), (2, 3))),
            ('a common class -- rule must NOT fire', ((1, 2), (1, 3), (1, 4))))


def leg_rank3(draws=6):
    """[GF-7] (GR-183): handle (c) is a theorem, and what it buys."""
    print(f"[GF-7] (GR-183) the third handle (c): three quadratics at one hub "
          f"(seed {GF_SEED + 7})")
    rng = random.Random(GF_SEED + 7)

    def det3(rows):
        (a, b, c), (d, e, f), (g, h, i) = rows
        return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    for name, pat in PATTERNS:
        common = set(pat[0]) & set(pat[1]) & set(pat[2])
        zero = 0
        for _ in range(draws):
            t = {x: F(rng.randint(1, 10 ** 4)) for x in range(1, 7)}
            rows = [[t[p[0]] * t[p[1]], -(t[p[0]] + t[p[1]]), F(1)]
                    for p in pat]
            zero += (det3(rows) == 0)
        fires = not common and len({frozenset(p) for p in pat}) == 3
        cs_txt = str(sorted(common))
        print(f"    {name:38s} common {cs_txt:10s} "
              f"det = 0 at {zero}/{draws} exact draws; rule fires: {fires}")
        assert (zero == 0) == fires, \
            f"pattern '{name}' disagrees with the combinatorial hypothesis"
    print("  => the four pairwise-intersection patterns are exhaustive for")
    print("     three DISTINCT 2-element root sets, and the determinant is")
    print("     identically zero exactly on the excluded one, so handle (c)")
    print("     is a theorem about generic parameters, not a measurement.")
    print()


def leg_strat(shape_cap=None, per_shape=6):
    """[GF-8] (GR-184): where the scheme stops."""
    print(f"[GF-8] (GR-184) the residual signature; caps: shapes "
          f"{shape_cap or 'all 907'}, per_shape {per_shape}")
    rng = random.Random(GF_SEED + 8)
    resid_tt = blocked = uncovered = slackless = 0
    hist = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        hn, ends, cs, _ = hub_model(bd)
        r = propagate(hn, ends, cs, 'gen')
        if r['residual'] == 0:
            continue
        if dim_Z_generic(bd, rng, draws=4) != 0:
            continue                        # correctly not certified
        resid_tt += 1
        sb = star_blocked_hubs(hn, ends, cs, r)
        blocked += (sb > 0)
        if not (sb > 0 or not local_slack_ok(hn, ends, r)):
            uncovered += 1
        if sb == 0:
            slackless += 1
        hist[r['residual']] = hist.get(r['residual'], 0) + 1
    seps = 0
    sep_blocked = 0
    for i, (label, b) in enumerate(separator_blocks()):
        hn, ends, cs, _ = hub_model(b)
        r = propagate(hn, ends, cs, 'gen')
        if r['residual'] == 0:
            continue
        seps += 1
        sep_blocked += (star_blocked_hubs(hn, ends, cs, r) > 0)
    print(f"  pool blocks with generic dim Z = 0 that `gen` does NOT certify: "
          f"{resid_tt}; residual cycle-rank histogram {sorted(hist.items())}")
    print(f"    ... (A) carrying at least one hub where every survivor "
          f"shares a class: {blocked}")
    print(f"    ... (B) the rest, {slackless}: no such hub, but no surviving "
          f"node has local unknown count <= 3 either")
    print(f"    residual blocks covered by NEITHER (A) nor (B): {uncovered}")
    assert uncovered == 0, \
        "a residual block outside (GR-183)'s two local-failure modes"
    print(f"  separators `gen` does not certify: {seps}; star-blocked "
          f"{sep_blocked}")
    print("  => EVERY residual block fails for one of the two reasons")
    print("     (GR-183)'s local exhaustion predicts: (A) a hub whose every")
    print("     survivor carries that hub's own star class, where (b) reads")
    print("     0 = 0 and (c)'s determinant vanishes identically; or (B) no")
    print("     surviving node with local unknown count <= 3 at all.")
    print()


MODES = ('sound', 'sep', 'sat', 'pool', 'tt', 'kappa', 'rank3', 'strat')
VALIDATE_KW = dict(sound=dict(shape_cap=40, per_shape=2, draws=1),
                   sep={}, sat=dict(shape_cap=20, per_shape=2),
                   pool=dict(shape_cap=60, per_shape=3),
                   tt=dict(shape_cap=60, per_shape=3),
                   kappa=dict(shape_cap=60, per_shape=3),
                   rank3=dict(draws=3), strat=dict(shape_cap=60, per_shape=3))


def main():
    ap = argparse.ArgumentParser()
    for f in MODES + ('validate',):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    chosen = [m for m in MODES if getattr(a, m)]
    if a.validate or not chosen:
        for m in MODES:
            globals()['leg_' + m](**VALIDATE_KW[m])
    else:
        for m in chosen:
            globals()['leg_' + m]()
    print("OK")


if __name__ == '__main__':
    main()
