"""
Phase 39 (K-grid) -- direction GLEAF: (GR-144)'s successor 4, leaf-covering on
the BRANCHES, and whether the landed Phase-12/13/14 matroid machinery reaches
it.

The `(K-grid)` close-it cell u7 names this successor as *"untouched by
(GR-142), still the one place the landed Phase-12/13/14 machinery might
reach"*.  (GR-138)'s own phrasing of it: *does every 6-tree-partition-carrying
cubic multigraph admit one in which a prescribed set of `<= n` vertices are
each a leaf of some part?*

RESULT (2026-09-03), and the deliverable is an ARGUMENT with the search
demoted to an adversarial control.  The reach question SPLITS.

  * (GR-145) the demand, stated precisely, in three equivalent forms -- and at
    `Lambda = 0` the prescribed set is NOT a parameter: a hub with NO leaf must
    have `deg_Ghat(u) >= 12`, which at `ell >= 2` forces it PURE.  So every
    non-pure hub is a leaf of some tree in EVERY 6-tree partition, and the
    demand is exactly (GR-136)(ii)'s pure-hub one.
  * (GR-146) the LOGICAL POSITION, and it is the verdict.  Leaf-covering is
    IMPLIED by (GR-18)(iii)'s residual (it is its hub-local relaxation,
    (GR-143)'s tier 1) and is VACUOUS inside (GR-140)'s own synthesis normal
    form: `D_beta = {alpha(head beta), gamma(tail beta)}` makes two of a pure
    hub's three absence-pairs share a coordinate, so a synthesized packing is
    leaf-covered by construction.  A THEOREM here therefore cannot advance
    (GR-10); only a REFUTATION could, and a refutation is strictly stronger
    than a g-flank.
  * (GR-147) NOT (GR-141)/(GR-142)'s object, and the reason is the ENCODING.
    The leaf (degree-cap) encoding is NOT a matroid -- exhibited at a genuine
    `D = 0`, `Lambda = 0` class shape, two maximal independent sets of
    different sizes.  The star-containment encoding of the SAME demand
    ((GR-135)(iii)'s `deg = 3` form) is a CONTRACTION, which is
    matroid-preserving.  This answers (GR-144)'s own *"what would change
    this"* clause (c) affirmatively on the branch side.
  * (GR-148) THE REDUCTION THEOREM.  At a FIXED leaf assignment the demand is
    exactly an Edmonds matroid-partition problem over the six contracted
    graphic matroids `M(G^o) / K_j`, and its criterion collapses to
    `sum_j [c(F u K_j) - c(F)] <= sigma(F)` at every branch set `F` -- the
    same `sigma` (GR-129) owns, used a THIRD time.  Equivalently
    `sum_j (comp(F u K_j) - 1) <= sum_{beta not in F} (6 - ell_beta - k_beta)`.
  * (GR-149) the SLACK LAW.  At a `D = 0` class shape `sigma(F) >= 1` for every
    `F` with `0 != F != E` -- a reading of (GR-25)'s cut criterion
    (`2 d(W') + exc >= 7`), so (GR-130)(b)'s tight lattice is TRIVIAL on this
    stratum -- and the per-branch inequality `ell_beta + k_beta <= 6` closes
    the criterion whenever every `F u K_j` is spanning-connected.
  * (GR-150) leaf-covering DECIDED, positively, on a stratum strictly WIDER
    than the residual's: all 312 `n_hub = 4` and all 4 598 `n_hub = 6` `D = 0`
    class shapes (2 623 of them pure-hub, where `gpack.all_packings` decides
    none and `gglob.synth_first` decided 150), plus the constructed families.
  * (GR-151) the reduction a PROOF would use: the COVER GRAPH on the pure hubs
    -- `u ~ w` iff `star(u) u star(w)` carries a cycle -- has maximum degree
    `<= 2`, by a six-slot count plus (GR-149) killing the degree-3
    configuration as a PROPER TIGHT SET, against SIX available colours.
  * (GR-152) where the machinery STOPS: the `exists`-assignment disjunction,
    the measured never-binding-nonempty-`F` CONJECTURE, and the g-flank hunt
    as the adversarial control -- including the two natural refuting
    configurations, both killed by `sigma >= 0` itself rather than by a
    search.

Oracles, and there are THREE for the reduction theorem.  (a) the exhaustive
`2^M` criterion sweep of (GR-148); (b) `union_rank_hetero`, this file's
augmenting-path rank in the union of six DIFFERENT graphic matroids -- the
computational shadow of `Matroid.Union` over an indexed family, cross-oracled
against `saferes.union_rank` on the constant family; (c) `first_pack_with` /
`first_leafcover`, direct depth-first enumerations of the constrained 6-tree
partitions (per assignment, and over all assignments).  Shapes
and habitat membership come from `glist.d0_shapes` / `cflank.cubic_habitat`
(the (GR-25) cut criterion) with `gridcol.class_shape` as the canonical
certificate; the residual's own population is `gpack.shape_rows`.

Caps, with denominators (README section 4 conventions 5 and 8).  `--state`,
`--encode` and `--value` run on (GR-132)'s own 12-shape population
(`m <= 6`, `Lambda = 0`, `n_hub in {2, 4}`) and say NOTHING about
`n_hub >= 6`.  `--edmonds` cross-oracles all three oracles exhaustively at
every `n_hub = 4` `D = 0` class shape (312) and oracles (a)/(b) at every
PURE-HUB `n_hub = 6` one (2 623 of 4 598), with the constrained-DFS oracle on
a 60-shape prefix and the nonempty-`F` leg on the constructed `n_hub = 10`
family.  `--slack` is exhaustive over all `2^M` branch subsets at
`n_hub in {4, 6}`.  `--decide` is exhaustive at `n_hub in {4, 6}` and a
CONSTRUCTED family at `n_hub in {10, ..., 20}` (circular and Moebius ladders
with the excess on two or three adjacent branches), which is a named family
and not a stratum; the exhaustive `D = 0` shape generator `glist.d0_shapes` is out of
reach at `n_hub >= 8` (measured: no shape produced in 400 s), which is a
harness limit and disclosed as one.  `--flank` reports a WITNESS-shaped
negative and two ARGUMENTS; its census leg is a capped sweep and its
`not found` is reported as *not found under cap*.

Workbook home: `notes/Pencil-informal-grid.md` section (K-grid) *Steps
G165--G172*, labels (GR-145)--(GR-152).  The reservation opens at the tail
GGLOB declared ((GR-145) / *Step G165*), one step BELOW the dispatch spec's
range, which skipped it; (GR-153) / *Step G173* are returned unused.

Run (each mode is a foreground-sized leg; `--validate` is all seven, 298 s,
inside ONE 600 s foreground invocation):
    python3 notes/scripts/w4/gleaf.py --state     # (GR-145)/(GR-146)
    python3 notes/scripts/w4/gleaf.py --encode    # (GR-147)
    python3 notes/scripts/w4/gleaf.py --edmonds   # (GR-148), (GR-152)(i)
    python3 notes/scripts/w4/gleaf.py --slack     # (GR-149)
    python3 notes/scripts/w4/gleaf.py --decide    # (GR-150)
    python3 notes/scripts/w4/gleaf.py --value     # (GR-146)(iii)
    python3 notes/scripts/w4/gleaf.py --flank     # (GR-151)/(GR-152)
    python3 notes/scripts/w4/gleaf.py --validate
"""
import sys
from itertools import combinations

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from closure import cycle_rank                                        # noqa: E402
from saferes import union_rank                                        # noqa: E402
from cflank import cubic_habitat                                      # noqa: E402
from gridcol import class_shape                                       # noqa: E402
from gpack import (all_packings, csets, legal_splits, shape_rows)      # noqa: E402
from glist import (csp_orient, d0_shapes, incidence, pure_hubs,        # noqa: E402
                   split_data, tree_deg)
from gglob import synth_first                                          # noqa: E402

LEAF_SEED = 20260903
RESID_SHAPES = 12          # (GR-132)'s own population, as `gpack.py --resid`
D0_N = (4, 6)              # the exhaustive `D = 0` strata this file reaches
BIG_N = (10, 12, 14, 16, 18, 20)   # the constructed families
PART_CAP = 200000          # assignment-enumeration cap in `decide_leafcover`
FLANK_SHAPES = 400         # `--flank`'s capped `n_hub = 6` census leg
DFS_SHAPES = 60            # `--edmonds`'s constrained-DFS cross-oracle prefix
INV_SHAPES = 400           # `--edmonds`'s relabelling-invariance prefix
CERT_SHAPES = 40           # `--flank`'s `class_shape` agreement prefix


# ------------------------------------------------------ local devices -------

def rank_tables(n, ends):
    """`(cr, cp)` by branch-subset bitmask: the cycle rank `c(F)` and the
    number of components `comp(F)` of the SPANNING subgraph `F` on all `n`
    hubs (isolated hubs counted).  Local device: `gpack.sigma_table` computes
    the matroid rank per mask with `closure.cycle_rank`; this one needs the
    component count as well (the (GR-148) component form) and is a plain DSU
    sweep, so it is kept separate rather than re-deriving one from the
    other."""
    m = len(ends)
    cr = [0] * (1 << m)
    cp = [n] * (1 << m)
    for mask in range(1, 1 << m):
        par = list(range(n))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        c = n
        for k in range(m):
            if mask >> k & 1:
                a, b = find(ends[k][0]), find(ends[k][1])
                if a != b:
                    par[a] = b
                    c -= 1
        cp[mask] = c
        cr[mask] = bin(mask).count('1') - (n - c)
    return cr, cp


def sigma_masks(lens, cr):
    """`sigma(F) = sum_F ell_beta - 6 c(F)` by mask -- (GR-129)'s slack, in the
    length form.  `sigma >= 0` IS 5/6-sparsity and `sigma(E) = 0` IS
    count-tightness."""
    m = len(lens)
    return [sum(lens[i] for i in range(m) if mask >> i & 1) - 6 * cr[mask]
            for mask in range(len(cr))]


def star_masks(n, ends):
    """Per hub, the bitmask of the branch indices incident to it."""
    m = len(ends)
    return {u: sum(1 << i for i in range(m) if u in ends[i]) for u in range(n)}


def hat_degree(inc, lens, u):
    """`deg_Ghat(u) = sum_{beta at u} (6 - ell_beta)`."""
    return sum(6 - lens[i] for i in inc[u])


def bad_pure(inc, C, S):
    """The hubs of `S` that are a leaf of NO tree of the packing `C` -- i.e.
    with all six tree-degrees equal to 2 ((GR-135)(iii))."""
    return [u for u in S if min(tree_deg(inc, C, u)) >= 2]


def leaf_assignment(inc, C, S):
    """For a leaf-covered packing, one tree per hub of `S` whose part contains
    that hub's WHOLE star -- the `deg = 3` half of (GR-135)(iii)'s
    equivalence, which is what the contraction encoding consumes.  `None` if
    some hub of `S` is a leaf of no tree."""
    out = {}
    for u in S:
        td = tree_deg(inc, C, u)
        if min(td) >= 2:
            return None
        j = td.index(max(td))
        assert td[j] == len(inc[u]), (u, td)
        out[u] = j
    return out


def partitions_into_blocks(items, maxb, cap=PART_CAP):
    """Set partitions of `items` into at most `maxb` blocks.  A leaf
    assignment `a : S -> {1..6}` matters only up to permuting the six trees
    (they are unlabelled, (GR-140)(iii)), so the canonical object is a
    partition of `S` -- `Bell(6) = 203` rather than `6^6 = 46 656`."""
    n = [0]

    def rec(rest):
        if not rest:
            yield []
            return
        first, tail = rest[0], rest[1:]
        for p in rec(tail):
            for i in range(len(p)):
                n[0] += 1
                assert n[0] < cap, "assignment enumeration hit its cap"
                yield p[:i] + [[first] + p[i]] + p[i + 1:]
            if len(p) < maxb:
                n[0] += 1
                assert n[0] < cap, "assignment enumeration hit its cap"
                yield [[first]] + p

    return rec(list(items))


def Ks_of(part, star):
    """The six reserved branch sets `K_j = star(S_j)` of a leaf assignment,
    as bitmasks, `K_j = 0` for an unused tree."""
    Ks = [0] * 6
    for j, blk in enumerate(part):
        msk = 0
        for u in blk:
            msk |= star[u]
        Ks[j] = msk
    return Ks


def crit_cycle(cr, sg, Ks, m):
    """(GR-148) cycle form: `sum_j [c(F u K_j) - c(F)] <= sigma(F)` at EVERY
    branch set.  Exhaustive over all `2^m` masks (the sweep is the claim)."""
    for mask in range(1 << m):
        base = cr[mask]
        tot = 0
        for k in Ks:
            tot += cr[mask | k] - base
            if tot > sg[mask]:
                return False
    return True


def crit_comp(cp, Ks, kb, lens, m):
    """(GR-148) component form:
    `sum_j (comp(F u K_j) - 1) <= sum_{beta not in F} (6 - ell_beta - k_beta)`.
    Algebraically equivalent to `crit_cycle`; carried as an independent
    computation so the equivalence is asserted rather than believed."""
    for mask in range(1 << m):
        lhs = sum(cp[mask | k] - 1 for k in Ks)
        rhs = sum(6 - lens[i] - kb[i] for i in range(m) if not mask >> i & 1)
        if lhs > rhs:
            return False
    return True


def crit_sigma(sg, Ks, kb, m):
    """(GR-148) SIGMA form: `2 sum_{beta not in F} k_beta <= sum_j sigma(F u
    K_j)` at every branch set.  Derived from the cycle form by the identity
    `sigma(F u K_j) = sigma(F) + 2|K_j \\ F| - 6 nu_j(F)`, which needs every
    reserved branch to have `ell = 2` -- true because a pure hub's whole star
    sits in `H` ((GR-149)(ii)).  This is the form in which the `F = 0`
    instance is an EQUALITY, so it is the form a proof of the measured
    equivalence would work in."""
    for mask in range(1 << m):
        lhs = 2 * sum(kb[i] for i in range(m) if not mask >> i & 1)
        rhs = sum(sg[mask | k] for k in Ks)
        if lhs > rhs:
            return False
    return True


def kb_of(Ks, m):
    """`k_beta = #{j : beta in K_j}` -- how many trees reserve a copy of the
    branch.  At `S` = pure hubs every `K_j` sits inside the length-2 subgraph
    `H`, so `k_beta <= 2 <= 4 = m_beta` and the reservation is always
    copy-feasible."""
    return [sum(1 for k in Ks if k >> i & 1) for i in range(m)]


# ------------------------------- the heterogeneous matroid-union oracle -----

def union_rank_hetero(elts, vmaps, nverts):  # noqa: C901
    """Rank of the edge multiset `elts` (a list of `(u, w)` pairs) in the union
    `Union_j M(G^o / K_j)` of the six CONTRACTED graphic matroids, by
    matroid-union augmenting paths.

    `vmaps[j]` is the vertex map of the `j`-th contraction (hubs to
    `K_j`-component ids), so `M_j`-independence of a set is acyclicity of its
    image under `vmaps[j]` and an element whose two images coincide is a LOOP
    of `M_j` -- it can never enter part `j`.

    This is the computational shadow of `Matroid.Union` over an INDEXED FAMILY
    (`CombinatorialRigidity/Matroid/Constructions/Union.lean`,
    `Matroid.Union` / `Matroid.union_indep_iff` / `Matroid.Union_rank_eq`),
    which is landed for a family of DIFFERENT matroids and not only for the
    `k`-fold power.  Local device, deliberately not `saferes.union_rank`: that
    one takes `k` copies of ONE graphic matroid on ONE vertex set, which is
    exactly the case (GR-130) needed and exactly the case this demand is
    not.  `--edmonds` asserts the two AGREE whenever every `vmap` is the
    identity."""
    k = len(vmaps)
    assert all(len(v) == nverts for v in vmaps), "vertex-map width mismatch"
    forests = [dict() for _ in range(k)]     # part -> {elt idx: (a, b) image}
    owner = {}
    rank = 0

    def img(j, idx):
        u, w = elts[idx]
        return vmaps[j][u], vmaps[j][w]

    def circuit(j, idx):
        """The circuit of `forests[j] + idx` in `M_j`, as a list of element
        indices of `forests[j]`, or `None` if `idx` is `M_j`-addable.  An
        empty list means `idx` is a LOOP: dependent, with nothing to
        exchange."""
        a, b = img(j, idx)
        if a == b:
            return []                        # loop of M_j
        adj = {}
        for y, (p, q) in forests[j].items():
            adj.setdefault(p, []).append((q, y))
            adj.setdefault(q, []).append((p, y))
        prev = {a: (None, None)}
        stack = [a]
        while stack:
            x = stack.pop()
            if x == b:
                path = []
                cur = b
                while prev[cur][0] is not None:
                    p, y = prev[cur]
                    path.append(y)
                    cur = p
                return path
            for (z, y) in adj.get(x, ()):
                if z not in prev:
                    prev[z] = (x, y)
                    stack.append(z)
        return None

    for idx in range(len(elts)):
        placed = False
        for j in range(k):
            if circuit(j, idx) is None:
                forests[j][idx] = img(j, idx)
                owner[idx] = j
                placed = True
                break
        if placed:
            rank += 1
            continue
        # exchange BFS: label[y] = (x, j) means "y sits on the circuit of x in
        # part j", so moving y out of j lets x in.
        label = {idx: None}
        queue = [idx]
        qi = 0
        aug = None
        while qi < len(queue) and aug is None:
            x = queue[qi]
            qi += 1
            for j in range(k):
                if owner.get(x) == j:
                    continue
                cyc = circuit(j, x)
                if cyc is None:
                    aug = (x, j)
                    break
                for y in cyc:
                    if y not in label:
                        label[y] = (x, j)
                        queue.append(y)
        if aug is None:
            continue                          # spanned; rank unchanged
        x, j = aug
        while True:
            forests[j][x] = img(j, x)
            owner[x] = j
            if label[x] is None:
                break
            nxt, nj = label[x]
            del forests[nj][x]
            x, j = nxt, nj
        rank += 1
    return rank


def hetero_feasible(n, ends, lens, Ks):
    """Does the reserved multiset partition into the six trees?  `E'` is the
    free copies (`m_beta - k_beta` of branch `beta`) and the answer is
    `rank_{Union_j M/K_j}(E') = |E'|` -- Edmonds' partition theorem, decided by
    `union_rank_hetero` rather than by the `2^m` criterion.

    The `K_j`-forest guard is NOT cosmetic and is the `F = 0` instance of the
    criterion: `rank(M / K_j) = (n - 1) - |K_j|` only when `K_j` is
    independent, so without it the rank count `|E'| = sum_j rank(M / K_j)`
    that turns *independent in the union* into *partitions into bases* is
    wrong, and this oracle silently accepts a reservation no spanning tree can
    contain.  Caught 2026-09-03 by the `--edmonds` cross-oracle, at
    `[[1, 4]]` on a `n_hub = 6` shape whose `K_0` carries a 4-cycle."""
    m = len(ends)
    for k in Ks:
        sel = [i for i in range(m) if k >> i & 1]
        if cycle_rank(list(range(n)), [ends[i] for i in sel]):
            return False
    kb = kb_of(Ks, m)
    vmaps = []
    for k in Ks:
        par = list(range(n))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for i in range(m):
            if k >> i & 1:
                a, b = find(ends[i][0]), find(ends[i][1])
                if a != b:
                    par[a] = b
        vmaps.append([find(u) for u in range(n)])
    elts = []
    for i in range(m):
        elts += [ends[i]] * (6 - lens[i] - kb[i])
    if any(6 - lens[i] - kb[i] < 0 for i in range(m)):
        return False
    return union_rank_hetero(elts, vmaps, n) == len(elts)


# ---------------------------------------- the direct constrained enumerator -

def first_leafcover(n, ends, lens, S, nodes=400000):
    """The first 6-tree partition of `Ghat` in which every hub of `S` is a leaf
    of some tree, by a deterministic depth-first enumeration with EARLY EXIT.

    Local device, and deliberately not `gpack.all_packings` (exhaustive by
    design, materializes ~10^4 partitions per `n_hub = 4` shape) nor
    `glist.first_feasible` (whose acceptance test is the (GR-134) CSP, a
    strictly stronger condition -- that difference is (GR-146))."""
    m = len(ends)
    inc = {u: [i for i in range(m) if u in ends[i]] for u in range(n)}
    found = []
    budget = [nodes]

    def rec(i, trees):
        if found or budget[0] <= 0:
            return
        budget[0] -= 1
        if i == m:
            if not all(len(t) == n - 1 for t in trees):
                return
            C = [set(j for j in range(6) if b in trees[j]) for b in range(m)]
            if all(min(sum(1 for b in inc[u] if j in C[b])
                       for j in range(6)) == 1 for u in S):
                found.append([tuple(sorted(t)) for t in trees])
            return
        rem = sum(6 - lens[t] for t in range(i + 1, m))
        for Cb in combinations(range(6), 6 - lens[i]):
            nt = [list(t) for t in trees]
            ok = True
            for j in Cb:
                if len(nt[j]) >= n - 1:
                    ok = False
                    break
                nt[j].append(i)
                if cycle_rank(list(range(n)), [ends[t] for t in nt[j]]):
                    ok = False
                    break
            if not ok:
                continue
            if sum((n - 1) - len(nt[j]) for j in range(6)) > rem:
                continue
            rec(i + 1, nt)
            if found or budget[0] <= 0:
                return

    rec(0, [[] for _ in range(6)])
    return (found[0] if found else None), nodes - budget[0]


def first_pack_with(n, ends, lens, Ks, nodes=2000000):
    """The first 6-tree partition of `Ghat` with `T_j` containing the reserved
    branch set `K_j` for every `j`, by depth-first enumeration with early
    exit -- the FIXED-assignment question the (GR-148) criterion decides,
    settled here without any matroid theory.  Returns `(packing or None,
    nodes)`; `nodes` exhausted is reported by the caller, never read as a
    negative."""
    m = len(ends)
    req = [[j for j in range(6) if Ks[j] >> i & 1] for i in range(m)]
    # RESERVED BRANCHES FIRST.  Without this ordering an infeasible
    # reservation whose cycle closes on the last branch costs the whole
    # `prod_beta C(6, m_beta)` search; with it the prune fires at once.
    order = sorted(range(m), key=lambda i: (-len(req[i]), i))
    suffix = [0] * (m + 1)
    for p in range(m - 1, -1, -1):
        suffix[p] = suffix[p + 1] + (6 - lens[order[p]])
    found = []
    budget = [nodes]

    def rec(p, trees):
        if found or budget[0] <= 0:
            return
        budget[0] -= 1
        if p == m:
            if all(len(t) == n - 1 for t in trees):
                found.append([tuple(sorted(t)) for t in trees])
            return
        i = order[p]
        need = req[i]
        free = [j for j in range(6) if j not in need]
        extra = (6 - lens[i]) - len(need)
        if extra < 0:
            return
        for add in combinations(free, extra):
            Cb = tuple(sorted(need + list(add)))
            nt = [list(t) for t in trees]
            ok = True
            for j in Cb:
                if len(nt[j]) >= n - 1:
                    ok = False
                    break
                nt[j].append(i)
                if cycle_rank(list(range(n)), [ends[t] for t in nt[j]]):
                    ok = False
                    break
            if not ok:
                continue
            if sum((n - 1) - len(nt[j]) for j in range(6)) > suffix[p + 1]:
                continue
            rec(p + 1, nt)
            if found or budget[0] <= 0:
                return

    rec(0, [[] for _ in range(6)])
    return (found[0] if found else None), nodes - budget[0]


def decide_leafcover(n, ends, lens, S, oracle='crit', count=False):
    """Decide the branch-side leaf-covering demand at a shape, through the
    (GR-148) reduction: is there a leaf assignment whose Edmonds criterion
    holds?  `oracle` is `'crit'` (the exhaustive `2^m` sweep) or `'union'`
    (`union_rank_hetero`).  Returns `(feasible, witness partition, #passing
    assignments)`; with `count=False` it stops at the first witness."""
    m = len(ends)
    star = star_masks(n, ends)
    if oracle == 'crit':
        cr, cp = rank_tables(n, ends)
        sg = sigma_masks(lens, cr)
    npass = 0
    wit = None
    for part in partitions_into_blocks(sorted(S), 6):
        Ks = Ks_of(part, star)
        kb = kb_of(Ks, m)
        if any(kb[i] > 6 - lens[i] for i in range(m)):
            continue
        if oracle == 'crit':
            if any(cr[k] for k in Ks):        # the `F = 0` instance
                continue
            ok = crit_cycle(cr, sg, Ks, m)
        else:
            ok = hetero_feasible(n, ends, lens, Ks)
        if ok:
            npass += 1
            if wit is None:
                wit = part
            if not count:
                break
    return (wit is not None), wit, npass


# ----------------------------------------- the cover graph of the demand ----

def cover_graph(n, ends, S):
    """`(max degree, bipartite?)` of the COVER GRAPH on the prescribed hubs:
    `u ~ w` iff `star(u) u star(w)` carries a cycle, i.e. iff `{u, w}` cannot
    be one block of a leaf assignment.  This is the pairwise part of the
    hypergraph a colouring proof of the demand would have to 6-colour; its
    hyperedges of rank `>= 3` are the alternating vertex covers of the longer
    cycles."""
    m = len(ends)
    star = star_masks(n, ends)
    adj = {u: set() for u in S}
    for u, w in combinations(S, 2):
        k = star[u] | star[w]
        sel = [i for i in range(m) if k >> i & 1]
        if cycle_rank(list(range(n)), [ends[i] for i in sel]):
            adj[u].add(w)
            adj[w].add(u)
    deg = max((len(adj[u]) for u in S), default=0)
    col = {}
    bip = True
    for s in S:
        if s in col:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in col:
                    col[y] = 1 - col[x]
                    stack.append(y)
                elif col[y] == col[x]:
                    bip = False
    return deg, bip


def two_colour_passes(n, ends, lens, S):
    """Does SOME 2-block leaf assignment pass the criterion?  Two blocks means
    two of the six trees own every prescribed star and the other four are
    untouched -- the measured shape of the witness at every constructed
    family member, and the quantitative form of (GR-136)(ii)'s slack."""
    if not S:
        return True
    S = sorted(S)
    for bits in range(1 << (len(S) - 1)):
        part = [[], []]
        for t, u in enumerate(S):
            part[0 if (t == 0 or bits >> (t - 1) & 1) else 1].append(u)
        part = [b for b in part if b]
        Ks = Ks_of(part, star_masks(n, ends))
        kb = kb_of(Ks, len(ends))
        if any(kb[i] > 6 - lens[i] for i in range(len(ends))):
            continue
        if hetero_feasible(n, ends, lens, Ks):
            return True
    return False


# ------------------------------------------------ constructed big families --

def prism(h):
    """The circular ladder `C_h x K_2` on `2h` hubs -- cubic, simple."""
    ed = []
    for i in range(h):
        ed.append((i, (i + 1) % h))
        ed.append((h + i, h + (i + 1) % h))
        ed.append((i, h + i))
    return ed


def moebius(h):
    """The Moebius ladder `M_h` on `2h` hubs: a `2h`-cycle plus the `h` long
    diagonals -- cubic, simple, and NOT bipartite, so it presents odd cycles
    the prism does not."""
    ed = [(i, (i + 1) % (2 * h)) for i in range(2 * h)]
    ed += [(i, i + h) for i in range(h)]
    return ed


def big_shapes(n):
    """Constructed `D = 0` class shapes at `n_hub = n` with as MANY pure hubs
    as the excess law allows: a cubic base graph (prism or Moebius ladder) with
    the whole excess budget `sum(ell - 2) = 6` on two `ell = 5` branches
    (`L = 2`, the (GR-140)(iv) minimum) or on three `ell = 4` branches, each
    candidate certified by `cflank.cubic_habitat` -- the (GR-25) cut criterion.
    A NAMED FAMILY, never a stratum: `glist.d0_shapes` is out of reach here."""
    assert n % 2 == 0
    out = []
    for name, base in (('prism', prism(n // 2)), ('moebius', moebius(n // 2))):
        m = len(base)
        assert m == 3 * n // 2, (name, n, m)
        for spec, exc in (('5+5', (3, 3)), ('4+4+4', (2, 2, 2)),
                          ('5+4+3', (3, 2, 1))):
            for combo in combinations(range(m), len(exc)):
                lens = [2] * m
                for t, i in enumerate(combo):
                    lens[i] = 2 + exc[t]
                if cubic_habitat(n, base, lens):
                    out.append(('%s-%s' % (name, spec), base, lens))
                    break
    return out


# -------------------------------------- [GLF-1] --state: (GR-145)/(GR-146) --

def resid_population():
    """(GR-132)'s own population: the first `RESID_SHAPES` census shapes with
    `m <= 6` and `Lambda = 0`, exactly as `gpack.py --resid` picks them."""
    return list(shape_rows(cap=RESID_SHAPES, mmax=6, lambda_free=True))


def leg_state():
    """[GLF-1] (GR-145)/(GR-146): the statement, the three equivalent forms,
    the non-pure-is-automatic theorem, and the two facts that fix the demand's
    logical position -- necessity, and vacuity inside (GR-140)."""
    print("[GLF-1] (GR-145)/(GR-146): the demand, and its logical position")

    print("  (i) at D = 0 every hub is CUBIC, and a hub with NO leaf must be "
          "PURE -- asserted over both exhaustive D = 0 strata")
    for n in D0_N:
        nsh = npu = 0
        hmin = 99
        for hedges, lens in d0_shapes(n):
            nsh += 1
            hubs = list(range(n))
            inc = incidence(hubs, hedges)
            assert all(len(inc[u]) == 3 for u in hubs), (hedges, lens)
            S = set(pure_hubs(hubs, hedges, lens))
            if S:
                npu += 1
            for u in hubs:
                d = hat_degree(inc, lens, u)
                assert (d >= 12) == (u in S), (hedges, lens, u, d)
                if u not in S:
                    hmin = min(hmin, 12 - d)
        print("      n_hub = %d: %d class shapes, %d with a pure hub; every "
              "non-pure hub has deg_Ghat <= 11 (slack >= %d)"
              % (n, nsh, npu, hmin))

    print("  (ii) the three forms agree at EVERY hub of EVERY packing of "
          "(GR-132)'s population -- no leaf <=> all six tree-degrees 2 <=> "
          "the D_beta a perfect matching; and a non-pure hub is a leaf of "
          "some tree in EVERY packing")
    npk = nhub = nbad = 0
    for label, edges, hubs, br, ends, lens in resid_population():
        n = len(hubs)
        inc = incidence(hubs, ends)
        S = set(pure_hubs(hubs, ends, lens))
        for trees in all_packings(hubs, ends, lens):
            npk += 1
            C = csets(lens, trees)
            for u in hubs:
                nhub += 1
                td = tree_deg(inc, C, u)
                Ds = [frozenset(set(range(6)) - C[i]) for i in inc[u]]
                pm = len(set().union(*Ds)) == sum(len(D) for D in Ds)
                assert (min(td) >= 2) == pm, (label, u, td, Ds)
                if min(td) >= 2:
                    assert u in S, (label, u, td)
                    nbad += 1
                if u not in S:
                    assert min(td) == 1, (label, u, td)
    print("      %d packings, %d (packing, hub) instances, %d of them a hub "
          "with no leaf -- every one at a PURE hub, 0 at a non-pure one"
          % (npk, nhub, nbad))

    print("  (iii) NECESSITY: every CSP-feasible legal pair's packing is "
          "leaf-covered ((GR-135)(iii)); so the residual IMPLIES the demand")
    nfeas = 0
    for label, edges, hubs, br, ends, lens in resid_population():
        inc = incidence(hubs, ends)
        S = pure_hubs(hubs, ends, lens)
        if not S:
            continue
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                if split_data(lens, C, J) is None:
                    continue
                if csp_orient(hubs, ends, lens, C, J) is not None:
                    nfeas += 1
                    assert not bad_pure(inc, C, S), (label, trees, J)
                    assert leaf_assignment(inc, C, S) is not None
    print("      %d CSP-feasible legal pairs, 0 with a leafless pure hub"
          % nfeas)

    print("  (iv) VACUITY inside (GR-140): a SYNTHESIZED packing is "
          "leaf-covered by construction -- asserted at every shape "
          "`synth_first` decides on the n_hub = 4 D = 0 stratum")
    nsyn = 0
    for hedges, lens in d0_shapes(4):
        hubs = list(range(4))
        S = pure_hubs(hubs, hedges, lens)
        if not S:
            continue
        sol, spent = synth_first(hubs, hedges, lens)
        assert sol is not None, ("synth_first found nothing", hedges, lens)
        alpha, gamma, trees = sol
        C = csets(lens, trees)
        inc = incidence(hubs, hedges)
        assert not bad_pure(inc, C, S), (hedges, lens, trees)
        # and the MECHANISM, asserted rather than the conclusion alone: at a
        # pure hub two of the three branches share a head or share a tail, so
        # two of its three `D_beta` share a coordinate of the grid.
        for u in S:
            Ds = [frozenset(set(range(6)) - C[i]) for i in inc[u]]
            assert len(set().union(*Ds)) < 6, (hedges, lens, u, Ds)
            assert any(Ds[a] & Ds[b] for a, b in combinations(range(3), 2)), \
                (hedges, lens, u, Ds)
        nsyn += 1
    print("      %d synthesized packings at pure-hub shapes, 0 leafless pure "
          "hubs, and at every pure hub two of the three D_beta SHARE a "
          "coordinate -- the demand is a TAUTOLOGY in (GR-140)'s normal form"
          % nsyn)
    print("  VERDICT (GR-146): the demand is the residual's hub-local "
          "relaxation ((GR-143) tier 1); a theorem here cannot advance "
          "(GR-10), and only a refutation -- strictly stronger than a "
          "g-flank -- could.")


# ----------------------------------------------- [GLF-2] --encode: (GR-147) -

def degcap_indep(n, ends, X):
    """The LEAF encoding's family: branch sets that are forests of `G^o` with
    `deg <= 1` at every hub of `X`.  Returned as the list of masks."""
    m = len(ends)
    out = []
    for mask in range(1 << m):
        sel = [i for i in range(m) if mask >> i & 1]
        if cycle_rank(list(range(n)), [ends[i] for i in sel]):
            continue
        if any(sum(1 for i in sel if u in ends[i]) > 1 for u in X):
            continue
        out.append(mask)
    return out


def contract_indep(n, ends, K):
    """The STAR-CONTAINMENT encoding's family: branch sets independent in the
    contraction `M(G^o) / K` (`K` a forest, given as a mask)."""
    m = len(ends)
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for i in range(m):
        if K >> i & 1:
            a, b = find(ends[i][0]), find(ends[i][1])
            if a != b:
                par[a] = b
    vm = [find(u) for u in range(n)]
    out = []
    for mask in range(1 << m):
        if mask & K:
            continue
        sel = [i for i in range(m) if mask >> i & 1]
        im = [(vm[ends[i][0]], vm[ends[i][1]]) for i in sel]
        if any(a == b for a, b in im):
            continue
        if cycle_rank(list(range(n)), im):
            continue
        out.append(mask)
    return out


def matroid_defect(masks):
    """`None` if `masks` is the independent-set family of a matroid; otherwise
    a witnessed defect: either two maximal members of different sizes, or an
    exchange-axiom failure `(X, Y)` with `|X| < |Y|` and no `y in Y \\ X`
    extending `X`."""
    ms = set(masks)
    assert 0 in ms, "the family is not down-closed at the empty set"
    for mask in ms:                            # down-closedness, asserted
        i = mask
        while i:
            low = i & -i
            assert mask ^ low in ms, "family is not down-closed"
            i ^= low
    maximal = [x for x in ms if all((x | (1 << b)) not in ms
                                    for b in range(20) if not x >> b & 1)]
    sizes = {bin(x).count('1') for x in maximal}
    if len(sizes) > 1:
        big = max(maximal, key=lambda x: bin(x).count('1'))
        small = min(maximal, key=lambda x: bin(x).count('1'))
        return ('unequal maximal sizes', small, big)
    for X in ms:
        for Y in ms:
            if bin(X).count('1') >= bin(Y).count('1'):
                continue
            if all((X | (1 << b)) not in ms
                   for b in range(20) if (Y >> b & 1) and not X >> b & 1):
                return ('exchange failure', X, Y)
    return None


def leg_encode():
    """[GLF-2] (GR-147): the two encodings of the SAME demand -- the leaf
    (degree-cap) one is not a matroid, the star-containment (contraction) one
    is, and that is why (GR-142) does not reach the branch side."""
    print("[GLF-2] (GR-147): the encoding decides the reach")
    pop = resid_population()

    print("  (i) the LEAF encoding is NOT a matroid -- exhibited at a genuine "
          "class shape with D = 0 and Lambda = 0, at |X| = 2")
    hit = None
    for label, edges, hubs, br, ends, lens in pop:
        n = len(hubs)
        for X in combinations(sorted(hubs), 2):
            d = matroid_defect(degcap_indep(n, ends, X))
            if d is not None:
                hit = (label, ends, lens, X, d)
                break
        if hit:
            break
    assert hit is not None, "no degree-cap defect found in the population"
    label, ends, lens, X, d = hit
    print("      shape %s, ends %s, lens %s, X = %s"
          % (label, ends, lens, list(X)))
    print("      defect: %s -- %s vs %s (sizes %d and %d)"
          % (d[0], bin(d[1]), bin(d[2]),
             bin(d[1]).count('1'), bin(d[2]).count('1')))

    print("  (ii) NEGATIVE CONTROL (README convention 6): at |X| = 1 the same "
          "family IS a matroid at every shape of the population -- so the "
          "defect is the SECOND constrained hub, not the degree cap as such")
    n1 = 0
    for lbl, edges, hubs, br, e2, l2 in pop:
        for u in hubs:
            assert matroid_defect(degcap_indep(len(hubs), e2, (u,))) is None, \
                (lbl, u)
            n1 += 1
    print("      %d (shape, single hub) families, all matroids" % n1)

    print("  (iii) PINNED COUNTER-FACT: the star-containment encoding of the "
          "SAME demand is a contraction, and IS a matroid at every reserved "
          "star of the population")
    n2 = 0
    for lbl, edges, hubs, br, e2, l2 in pop:
        n = len(hubs)
        star = star_masks(n, e2)
        for u in hubs:
            K = star[u]
            if cycle_rank(list(range(n)),
                          [e2[i] for i in range(len(e2)) if K >> i & 1]):
                continue                        # not a forest: no contraction
            assert matroid_defect(contract_indep(n, e2, K)) is None, (lbl, u)
            n2 += 1
    print("      %d (shape, reserved star) contractions, all matroids" % n2)
    print("  VERDICT (GR-147): (GR-142) kills a HUB-side family; the branch "
          "side is a CONTRACTION, matroid-preserving -- so the landed "
          "subsystem does reach the fixed-assignment demand.")


# ---------------------------------------------- [GLF-3] --edmonds: (GR-148) -

def leg_edmonds():
    """[GLF-3] (GR-148): the reduction theorem, cross-oracled three ways."""
    print("[GLF-3] (GR-148): the reduction theorem, three oracles")

    print("  (i) `union_rank_hetero` agrees with `saferes.union_rank` "
          "whenever every contraction is trivial (the constant family)")
    nid = 0
    for hedges, lens in d0_shapes(4):
        n = 4
        elts = []
        for i, (u, w) in enumerate(hedges):
            elts += [(u, w)] * (6 - lens[i])
        vm = [list(range(n)) for _ in range(6)]
        a = union_rank_hetero(elts, vm, n)
        b = union_rank(elts, list(range(n)), k=6)
        assert a == b == 6 * (n - 1), (hedges, lens, a, b)
        nid += 1
    print("      %d n_hub = 4 shapes, 0 disagreements, all at 6(n-1) = %d"
          % (nid, 6 * 3))

    print("  (ii) criterion (2^m sweep) vs `union_rank_hetero` vs the direct "
          "constrained DFS, at EVERY leaf assignment of EVERY n_hub = 4 "
          "D = 0 class shape")
    nsh = nass = 0
    for hedges, lens in d0_shapes(4):
        n = 4
        hubs = list(range(n))
        m = len(hedges)
        S = sorted(pure_hubs(hubs, hedges, lens))
        star = star_masks(n, hedges)
        cr, cp = rank_tables(n, hedges)
        sg = sigma_masks(lens, cr)
        nsh += 1
        for part in partitions_into_blocks(S, 6):
            Ks = Ks_of(part, star)
            kb = kb_of(Ks, m)
            if any(kb[i] > 6 - lens[i] for i in range(m)):
                continue
            forest = not any(cr[k] for k in Ks)
            c1 = forest and crit_cycle(cr, sg, Ks, m)
            c2 = forest and crit_comp(cp, Ks, kb, lens, m)
            c3 = hetero_feasible(n, hedges, lens, Ks)
            assert c1 == c2, ("the two criterion forms disagree",
                              hedges, lens, part)
            assert c1 == c3, ("criterion vs matroid union",
                              hedges, lens, part, c1, c3)
            nass += 1
    print("      %d shapes, %d (shape, assignment) instances, 0 disagreements "
          "between the cycle form, the component form and matroid union"
          % (nsh, nass))

    print("  (iii) the EXISTENCE questions agree: the (GR-148) reduction vs "
          "the direct DFS over constrained packings, at every n_hub = 4 shape")
    ndis = 0
    for hedges, lens in d0_shapes(4):
        n = 4
        hubs = list(range(n))
        S = sorted(pure_hubs(hubs, hedges, lens))
        ok, wit, _ = decide_leafcover(n, hedges, lens, S)
        pk, nodes = first_leafcover(n, hedges, lens, S)
        assert ok == (pk is not None), (hedges, lens, ok, pk is not None)
        if ok:
            # the DFS witness must itself carry a leaf assignment
            inc = incidence(hubs, hedges)
            C = csets(lens, pk)
            assert leaf_assignment(inc, C, S) is not None
        ndis += 1
    print("      %d shapes, 0 disagreements between the reduction and the "
          "direct enumeration" % ndis)

    print("  (iv) the same cross-oracle at n_hub = 6, where |S| reaches 2 and "
          "the assignment is a genuine variable: criterion vs matroid union "
          "at EVERY pure-hub shape, and vs the direct constrained DFS on a "
          "capped prefix")
    n6 = n6a = ndfs = npos = nneg = nfor = ncrt = 0
    for hedges, lens in d0_shapes(6):
        n = 6
        hubs = list(range(n))
        m = len(hedges)
        S = sorted(pure_hubs(hubs, hedges, lens))
        if not S:
            continue
        star = star_masks(n, hedges)
        cr, cp = rank_tables(n, hedges)
        sg = sigma_masks(lens, cr)
        n6 += 1
        for part in partitions_into_blocks(S, 6):
            Ks = Ks_of(part, star)
            kb = kb_of(Ks, m)
            if any(kb[i] > 6 - lens[i] for i in range(m)):
                continue
            forest = not any(cr[k] for k in Ks)
            c1 = forest and crit_cycle(cr, sg, Ks, m)
            c2 = forest and crit_comp(cp, Ks, kb, lens, m)
            cs = forest and crit_sigma(sg, Ks, kb, m)
            c3 = hetero_feasible(n, hedges, lens, Ks)
            assert c1 == c2 == cs, (hedges, lens, part, c1, c2, cs)
            assert c1 == c3, (hedges, lens, part, c1, c3)
            n6a += 1
            nfor += 0 if forest else 1
            ncrt += 1 if (forest and not c1) else 0
            if n6 <= DFS_SHAPES:
                pk, nodes = first_pack_with(n, hedges, lens, Ks)
                assert nodes < 2000000, "the DFS oracle exhausted its budget"
                assert c1 == (pk is not None), \
                    ("criterion vs constrained DFS", hedges, lens, part, c1)
                ndfs += 1
                npos += 1 if c1 else 0
                nneg += 0 if c1 else 1
    print("      %d pure-hub n_hub = 6 shapes, %d (shape, assignment) "
          "instances, 0 disagreements between the three criterion forms "
          "and matroid union" % (n6, n6a))
    print("      DFS cross-oracle on the first %d of them: %d instances, "
          "%d feasible and %d infeasible, 0 disagreements -- so BOTH verdicts "
          "are exercised" % (min(n6, DFS_SHAPES), ndfs, npos, nneg))
    print("      SUPPORT (RESEARCH-ARC section 4): of the %d instances, %d "
          "fail already at the `F = 0` instance (a `K_j` with a cycle) and "
          "%d have every `K_j` a forest and STILL fail the criterion -- so "
          "this stratum exercises the nonempty-`F` content %s"
          % (n6a, nfor, ncrt, "TOO" if ncrt else "NOT AT ALL"))

    print("  (v) the canonical reduction is sound: the criterion is invariant "
          "under permuting the six tree labels ((GR-140)(iii)), which is why "
          "an assignment matters only as a PARTITION of `S`")
    ninv = 0
    for hedges, lens in list(d0_shapes(6))[:INV_SHAPES]:
        n = 6
        m = len(hedges)
        hubs = list(range(n))
        S = sorted(pure_hubs(hubs, hedges, lens))
        if not S:
            continue
        star = star_masks(n, hedges)
        cr, cp = rank_tables(n, hedges)
        sg = sigma_masks(lens, cr)
        for part in partitions_into_blocks(S, 6):
            Ks = Ks_of(part, star)
            base = crit_cycle(cr, sg, Ks, m)
            for perm in (list(range(6))[::-1], [2, 0, 1, 5, 3, 4],
                         [5, 4, 3, 2, 1, 0]):
                Kp = [Ks[perm[j]] for j in range(6)]
                assert crit_cycle(cr, sg, Kp, m) == base, (hedges, lens, part)
                ninv += 1
    print("      %d permuted instances, 0 disagreements" % ninv)

    print("  (vi) the nonempty-`F` content, on the CONSTRUCTED n_hub = 10 "
          "family where |S| = 6 -- all three criterion forms, matroid union, "
          "and the measured equivalence with the `F = 0` instance")
    for name, base, lens in big_shapes(10):
        n, m = 10, len(base)
        S = sorted(pure_hubs(list(range(n)), base, lens))
        star = star_masks(n, base)
        cr, cp = rank_tables(n, base)
        sg = sigma_masks(lens, cr)
        ntot = ncyc = nfail = npass = 0
        minblk = 99
        for part in partitions_into_blocks(S, 6):
            Ks = Ks_of(part, star)
            kb = kb_of(Ks, m)
            if any(kb[i] > 6 - lens[i] for i in range(m)):
                continue
            ntot += 1
            forest = not any(cr[k] for k in Ks)
            c1 = forest and crit_cycle(cr, sg, Ks, m)
            c2 = forest and crit_comp(cp, Ks, kb, lens, m)
            c3 = forest and crit_sigma(sg, Ks, kb, m)
            c4 = hetero_feasible(n, base, lens, Ks)
            assert c1 == c2 == c3 == c4, (name, part, c1, c2, c3, c4)
            if not forest:
                ncyc += 1
            elif not c1:
                nfail += 1
            if c1:
                npass += 1
                minblk = min(minblk, len(part))
        print("      %-14s %3d assignments: %3d with a cyclic K_j, %d "
              "forest-but-criterion-FAIL, %3d pass (fewest blocks used: %d)"
              % (name, ntot, ncyc, nfail, npass, minblk))
    print("      MEASURED EQUIVALENCE: across every instance above and every "
          "one of (iv)'s, the criterion holds iff its `F = 0` instance does "
          "-- i.e. iff every `K_j` is a forest.  Stated as a CONJECTURE "
          "((GR-152)), not a theorem: the nonempty-`F` content is never the "
          "binding constraint anywhere it has been evaluated.")
    print("  VERDICT (GR-148): at a fixed leaf assignment the demand IS an "
          "Edmonds matroid-partition problem over the six contractions, and "
          "its criterion is sigma-shaped.")


# ------------------------------------------------ [GLF-4] --slack: (GR-149) -

def leg_slack():
    """[GLF-4] (GR-149): the slack law -- no PROPER tight branch set at a
    D = 0 class shape, so (GR-130)(b)'s tight lattice is trivial here."""
    print("[GLF-4] (GR-149): the slack law, exhaustive over all 2^m")
    for n in D0_N:
        nsh = 0
        worst = 99
        nz = 0
        for hedges, lens in d0_shapes(n):
            m = len(hedges)
            cr, cp = rank_tables(n, hedges)
            sg = sigma_masks(lens, cr)
            assert sg[(1 << m) - 1] == 0, (hedges, lens, sg[-1])
            assert sg[0] == 0
            for mask in range(1, (1 << m) - 1):
                assert sg[mask] >= 1, ("PROPER TIGHT SET", hedges, lens, mask)
                worst = min(worst, sg[mask])
                if sg[mask] == 1:
                    nz += 1
            nsh += 1
        print("      n_hub = %d: %d shapes, min sigma over proper nonempty F "
              "= %d, %d masks attaining 1; sigma(0) = sigma(E) = 0"
              % (n, nsh, worst, nz))

    print("  (ii) the per-branch inequality `ell_beta + k_beta <= 6` holds at "
          "every reserved star, so the criterion is closed at every F whose "
          "six `F u K_j` are spanning-connected")
    ncheck = 0
    for n in D0_N:
        for hedges, lens in d0_shapes(n):
            m = len(hedges)
            hubs = list(range(n))
            S = sorted(pure_hubs(hubs, hedges, lens))
            if not S:
                continue
            star = star_masks(n, hedges)
            for part in partitions_into_blocks(S, 6):
                Ks = Ks_of(part, star)
                kb = kb_of(Ks, m)
                for i in range(m):
                    assert lens[i] + kb[i] <= 6, (hedges, lens, part, i)
                    if kb[i]:
                        assert lens[i] == 2, "a long branch was reserved"
                ncheck += 1
    print("      %d (shape, assignment) instances, 0 violations; every "
          "reserved branch has ell = 2, so every K_j sits inside H" % ncheck)


# ----------------------------------------------- [GLF-5] --decide: (GR-150) -

def leg_decide():
    """[GLF-5] (GR-150): leaf-covering DECIDED, on a stratum strictly wider
    than the residual's."""
    print("[GLF-5] (GR-150): the demand decided")
    for n in D0_N:
        nsh = npu = nfail = 0
        maxS = 0
        for hedges, lens in d0_shapes(n):
            hubs = list(range(n))
            S = sorted(pure_hubs(hubs, hedges, lens))
            maxS = max(maxS, len(S))
            if S:
                npu += 1
            ok, wit, _ = decide_leafcover(n, hedges, lens, S)
            if not ok:
                nfail += 1
                print("      FAIL", hedges, lens, S)
            nsh += 1
        print("      n_hub = %d: %d class shapes (%d pure-hub, max |S| = %d) "
              "-- leaf-covering HOLDS at %d, FAILS at %d"
              % (n, nsh, npu, maxS, nsh - nfail, nfail))

    print("  (ii) how many leaf assignments pass -- the price of the "
          "`exists`-assignment disjunction, over the pure-hub shapes")
    for n in D0_N:
        tot = npass = 0
        for hedges, lens in d0_shapes(n):
            hubs = list(range(n))
            S = sorted(pure_hubs(hubs, hedges, lens))
            if not S:
                continue
            m = len(hedges)
            star = star_masks(n, hedges)
            cand = 0
            for part in partitions_into_blocks(S, 6):
                Ks = Ks_of(part, star)
                if any(kb > 6 - lens[i]
                       for i, kb in enumerate(kb_of(Ks, m))):
                    continue
                cand += 1
            _, _, np_ = decide_leafcover(n, hedges, lens, S, count=True)
            tot += cand
            npass += np_
        print("      n_hub = %d: %d passing of %d copy-feasible assignments "
              "(%.1f%%)" % (n, npass, tot, 100.0 * npass / max(tot, 1)))

    print("  (iii) the CONSTRUCTED families at n_hub = 10..20 -- where |S| is "
          "large and the demand is not near-vacuous (a NAMED family, never a "
          "stratum)")
    for n in BIG_N:
        rows = big_shapes(n)
        for name, base, lens in rows:
            hubs = list(range(n))
            S = sorted(pure_hubs(hubs, base, lens))
            ok, wit, _ = decide_leafcover(n, base, lens, S, oracle='union')
            print("      n_hub = %2d %-14s |S| = %2d  leaf-covering %s"
                  % (n, name, len(S), "HOLDS" if ok else "FAILS"))
            assert ok, (name, n, lens)
        if not rows:
            print("      n_hub = %2d: no habitat member in the family" % n)


# --------------------------------------------- [GLF-6] --value: (GR-146)(iii)

def leg_value():
    """[GLF-6] (GR-146)(iii): the demand's discriminating power, measured
    against the residual on (GR-132)'s own population."""
    print("[GLF-6] (GR-146)(iii): the relaxation's discriminating power")
    nleg = nlc = nfe = nbadpair = 0
    for label, edges, hubs, br, ends, lens in resid_population():
        inc = incidence(hubs, ends)
        S = pure_hubs(hubs, ends, lens)
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            lc = not bad_pure(inc, C, S)
            for J in legal_splits(lens, C):
                if split_data(lens, C, J) is None:
                    continue
                nleg += 1
                if lc:
                    nlc += 1
                else:
                    nbadpair += 1
                if csp_orient(hubs, ends, lens, C, J) is not None:
                    nfe += 1
                    assert lc, (label, trees, J)
    print("      %d legal (packing, split) pairs: %d leaf-covered (%.1f%%), "
          "%d CSP-feasible (%.1f%%), %d carrying the pure-hub conflict"
          % (nleg, nlc, 100.0 * nlc / nleg, nfe, 100.0 * nfe / nleg,
             nbadpair))
    print("      the relaxation admits %.2fx as many pairs as the target, so "
          "%d pairs pass the demand and FAIL the residual"
          % (nlc / float(nfe), nlc - nfe))
    print("  VERDICT: leaf-covering is (GR-143)'s tier 1 read as an existence "
          "statement; it is satisfied by most of the residual's own failures.")


# ------------------------------------- [GLF-7] --flank: (GR-151)/(GR-152) ---

def leg_flank():
    """[GLF-7] (GR-151)/(GR-152): the cover-graph degree bound, the g-flank
    hunt demoted to an adversarial control, and the two further ARGUMENTS that
    kill the natural refuting configurations."""
    print("[GLF-7] (GR-151)/(GR-152): the cover graph, and the refutation "
          "side")

    print("  (i) ARGUMENT 1 -- a hub carrying two PARALLEL branches can never "
          "be leafless: sigma({beta1, beta2}) >= 0 forces "
          "m_1 + m_2 <= 6, hence deg_Ghat(u) <= 11 < 12")
    npar = 0
    for n in D0_N:
        for hedges, lens in d0_shapes(n):
            hubs = list(range(n))
            inc = incidence(hubs, hedges)
            for u in hubs:
                pairs = [(i, j) for i, j in combinations(inc[u], 2)
                         if set(hedges[i]) == set(hedges[j])]
                for i, j in pairs:
                    assert (6 - lens[i]) + (6 - lens[j]) <= 6, \
                        (hedges, lens, u, i, j)
                    assert hat_degree(inc, lens, u) <= 11, (hedges, lens, u)
                    npar += 1
    print("      %d (shape, hub, parallel pair) instances, 0 violations"
          % npar)

    print("  (ii) ARGUMENT 2 -- the CONSTRUCTED refuting configuration "
          "(a K_{2,3} of length-2 branches, plus a hub with two neighbours "
          "inside it) is killed by sparsity itself, not by a search")
    # K_{2,3} on hubs 0,1 (degree 3) and 2,3,4 (degree 2), plus hub 5 joined
    # to 2 and 3 -- the configuration whose tight K_{2,3} would force every
    # nu_j = 0 while hub 5's own star closes a cycle.
    k23 = [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]
    plus = k23 + [(5, 2), (5, 3)]
    n = 6
    cr, cp = rank_tables(n, k23)
    sg = sigma_masks([2] * 6, cr)
    print("      the K_{2,3} alone: sigma = %d (TIGHT), so the criterion "
          "there admits no nu_j > 0" % sg[(1 << 6) - 1])
    assert sg[(1 << 6) - 1] == 0
    cr2, cp2 = rank_tables(n, plus)
    sg2 = sigma_masks([2] * 8, cr2)
    print("      adding hub 5's two branches: sigma = %d < 0, so the "
          "configuration is NOT 5/6-sparse and NOT a class shape"
          % sg2[(1 << 8) - 1])
    assert sg2[(1 << 8) - 1] < 0
    assert not cubic_habitat(6, plus, [2] * 8), "the configuration certified"
    print("      `cflank.cubic_habitat` REJECTS it, and (GR-149) explains "
          "why: a proper tight set cannot exist at all")

    print("  (iii) the SECOND oracle on a capped prefix -- a hunt for a shape "
          "whose every 6-tree partition has a leafless pure hub, decided by "
          "matroid union rather than by the criterion sweep")
    nsh = 0
    for hedges, lens in d0_shapes(6):
        hubs = list(range(6))
        S = sorted(pure_hubs(hubs, hedges, lens))
        if not S:
            continue
        ok, wit, _ = decide_leafcover(6, hedges, lens, S, oracle='union')
        assert ok, ("A G-FLANK CANDIDATE", hedges, lens, S)
        nsh += 1
        if nsh >= FLANK_SHAPES:
            break
    print("      NOT FOUND UNDER CAP: %d pure-hub n_hub = 6 shapes swept "
          "(cap %d of 2 623; `--decide` runs the criterion oracle over all "
          "2 623); a refutation would be a g-flank and would fire E1"
          % (nsh, FLANK_SHAPES))

    print("  (iv) (GR-151) ARGUMENT 3 -- the COVER GRAPH has max degree <= 2 "
          "at a pure hub, and the degree-3 configuration is a PROPER TIGHT "
          "SET, excluded by (GR-149)")
    # u = 0 with N(u) = {1, 2, 3}; w1 = 4 on {1, 2}, w2 = 5 on {2, 3},
    # w3 = 6 on {1, 3} -- the only way three cover-neighbours can fit the six
    # outside slots of u's neighbours (each w must take two of them, and two
    # w's on the same pair would give a neighbour degree 4).
    trip = [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (2, 5), (3, 5),
            (1, 6), (3, 6)]
    crt, cpt = rank_tables(7, trip)
    sgt = sigma_masks([2] * 9, crt)
    print("      the three-cover-neighbour configuration: 9 branches on 7 "
          "hubs, cycle rank %d, sigma = %d -- TIGHT, and PROPER at every "
          "class shape (a cubic graph has no 7 hubs), so (GR-149) excludes it"
          % (crt[(1 << 9) - 1], sgt[(1 << 9) - 1]))
    assert sgt[(1 << 9) - 1] == 0
    assert all(sum(1 for e in trip if v in e) == 3 for v in (0, 1, 2, 3))
    assert all(sum(1 for e in trip if v in e) == 2 for v in (4, 5, 6))

    print("  (v) (GR-151) the COVER GRAPH measured -- what a colouring proof "
          "would have to 6-colour, and how far from tight it is")
    for n in D0_N:
        worst = nbip = ntot = 0
        for hedges, lens in d0_shapes(n):
            S = sorted(pure_hubs(list(range(n)), hedges, lens))
            if not S:
                continue
            deg, bip = cover_graph(n, hedges, S)
            worst = max(worst, deg)
            ntot += 1
            nbip += 1 if bip else 0
        assert worst <= 2, ("cover-graph degree above the bound", n, worst)
        print("      n_hub = %d: %d pure-hub shapes, max cover-graph degree "
              "%d against 6 available colours, %d of them bipartite"
              % (n, ntot, worst, nbip))
    for n in BIG_N:
        for name, base, lens in big_shapes(n):
            S = sorted(pure_hubs(list(range(n)), base, lens))
            deg, bip = cover_graph(n, base, S)
            assert deg <= 2, ("cover-graph degree above the bound", name, deg)
            two = two_colour_passes(n, base, lens, S)
            assert two, ("no 2-colour assignment passes", name)
            print("      n_hub = %2d %-14s |S| = %2d, max cover degree %d, "
                  "bipartite %-5s, a 2-colour assignment passes: %s"
                  % (n, name, len(S), deg, bip, two))
    print("      so the colouring the (GR-152) conjecture reduces the demand "
          "to has SIX colours against a measured max degree far below that -- "
          "(GR-136)(ii)'s `3n` supply against `<= n` demand, seen here as "
          "TWO of the six trees sufficing")

    print("  (vi) the cut criterion and `gridcol.class_shape` agree where "
          "both are in reach (the canonical certificate, at n_hub = 4)")
    nagree = 0
    for hedges, lens in d0_shapes(4):
        specs = [(hedges[i][0], hedges[i][1], lens[i])
                 for i in range(len(hedges))]
        assert class_shape(specs) is not None, (hedges, lens)
        assert cubic_habitat(4, hedges, lens)
        nagree += 1
        if nagree >= CERT_SHAPES:
            break
    print("      %d n_hub = 4 shapes certified by BOTH "
          "`cflank.cubic_habitat` and `gridcol.class_shape` (cap %d; "
          "`cflank.py --law` is the exhaustive agreement check)"
          % (nagree, CERT_SHAPES))


# ---------------------------------------------------------------- main ------

MODES = [('--state', leg_state), ('--encode', leg_encode),
         ('--edmonds', leg_edmonds), ('--slack', leg_slack),
         ('--decide', leg_decide), ('--value', leg_value),
         ('--flank', leg_flank)]


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return
    print("gleaf.py -- direction GLEAF, (GR-144) successor 4 "
          "(seed %d, exact combinatorics, no sampling)" % LEAF_SEED)
    ran = False
    for flag, leg in MODES:
        if flag in args or '--validate' in args:
            leg()
            print()
            ran = True
    if not ran:
        print("no mode selected; see --help / the module docstring")


if __name__ == '__main__':
    main()
