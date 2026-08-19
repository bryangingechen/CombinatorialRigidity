"""§(K-grid) direction GCAP (2026-08-12) driver -- the general-sub-multigraph
instance of (GR-20)'s certificate 3: cap the (GR-8) family `max_P g(P)` over
admissible colourings at `D = 0`, characterize the binding non-circuit
family, and measure the colouring-existence target
`a = 0 AND max_P g(P) <= 0 in both blocks` at every `D = 0` class shape.

A `w4/` leaf beside `cflank.py`, importing `cflank.py` / `gridcol.py` /
`grid.py` / `gridwit.py` / `closure.py` READ-ONLY (README §2; `gridwit` is
the canonical home of `subgraph_g` / `structured_beta` / `a_and_M`, the same
route `packmm.py` takes).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --probe  # Step G23's scoping probe RE-ESTABLISHED as committed evidence + the full-census hit census
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --law    # the exact-g law on the Lambda = empty D = 0 stratum: max g <= 1 under NC1 (the cap)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --cap    # THE TARGET: a = 0 and max_P g(P) <= 0 in both blocks at some admissible colouring, at every D = 0 shape
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --flip   # the repair distance: <= 2 balance-preserving flips at binding blocks; the odd-pair flip at the no-even-branch circuits
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --adv    # the falsification control: binding-rich constructions + the F13 witness theta(2,4,4) the g-detector MUST reject
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --validate  # all five in one process -- OVER the 600 s foreground budget (~700 s); run the modes separately

Argument state: session draft `fanout-GCAP.md` (to be merged into
`notes/Pencil-informal-grid.md` §(K-grid) as Steps G29+; labels (GR-27)+ per the
2026-08-12 GCAP reservation in `notes/Pencil-labels.md`).

THE TWO STRUCTURE THEOREMS THE MODES REST ON (proofs in the draft; both are
asserted here rather than trusted).

(GR-27)  g is BLOCK-ADDITIVE and exactly computable.  For any sub-multigraph
         P of the contracted multigraph H+, with r_X(P) = dim C(P) -
         dim C(P minus X),

             g(P) = 3 dim C(P) - Sum_X r_X(P)
                  = Sum over 2-edge-connected blocks B of P of g(B),

         a bridge contributes 0, and every 2-edge-connected P is a union of
         FULL branch A-paths.  Hence  max(0, max_P g(P))  is computed
         exactly by enumerating branch subsets -- the "structured" proxy
         `gridwit.structured_beta` (class unions + node-induced subgraphs)
         is superseded on these pools by an exact figure.

(GR-28)  At `Lambda = empty`, `D = 0`, for an admissible colouring and a
         connected 2-edge-connected branch union S with q3 degree-3-in-S
         hubs (all in-S) and the rest degree-2-in-S:

             g_A(S) = 3 - defect_A(S),
             defect_A(S) = Sum_{beta in S} (A(beta) - 1)
                           + #(degree-2-in-S hubs whose two S-darts
                               are NOT both A),

         a = 0 automatically, and NC1 (the circuit instance) forces
         defect >= 2 on every 2ec S, i.e. `max_P g(P) <= 1`.  The k = 2
         (theta) case of that cap is proven; k >= 3 is asserted
         exhaustively here.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--probe  *Step G23*'s scoping figure, re-established as committed evidence
         (the original is recorded "measured, script not retained"): over
         the first 45 census shapes, the 572 balanced no-monochromatic-hub
         NC1-satisfying colourings give 1144 blocks of which exactly 16
         have generic dim Z > 0, each with a = 0 and structured (GR-8)
         maximum 1 -- and, exactly as recorded, all 16 on Lambda != empty
         shapes; then the SAME probe over the full 907-shape census, where
         the classification of every hit's minimal witness answers the
         decisive sub-question (every hit has exact max g = 1; minimal
         witnesses have cycle rank 2 <= k <= 6 and a finite path-profile
         list); and the CORRECTION: the "all on Lambda != empty shapes"
         clause is a sample-bias artifact of the 45-shape prefix -- the
         census carries Lambda = empty hits further in, exhibited.

--law    (GR-28) on the whole Lambda = empty D = 0 stratum (the 4920
         shapes, every admissible colouring, both blocks): the defect
         formula agrees with the exact `gridwit.subgraph_g` at every
         seeded-sampled pair, a = 0 at every sampled block, NC1-passing
         blocks have exact max g <= 1 (the cap; 0 blocks at g >= 2), and
         every binding block's minimal witnesses have k in {2, 3} with the
         realized path-profile list printed (the (GR-17)(d) analogue).

--cap    the colouring-existence target at every D = 0 class shape of the
         three pools (Lambda = empty 4920, census D = 0, the Lambda != 0
         n <= 4 pool): some admissible colouring has a = 0 and exact
         max_P g(P) <= 0 in BOTH blocks -- with the first-hit histogram,
         and the certificate cross-checked against an exact rational
         dim Z = 0 point at seeded sample shapes.

--flip   the repair mechanics: every Lambda = empty binding admissible
         colouring reaches a FULLY-good one (a = 0, max g <= 0 both
         blocks) by at most TWO balance-preserving even-branch flips; and
         at the no-even-branch binding circuits (profiles (1,3,3)/(1,1,5),
         CFLANK item (v), live only from n = 6 -- constructed here), the
         balance-preserving ODD-PAIR flip repairs every violated
         (colouring, circuit) instance.

--adv    the falsification control: constructed shapes stacking binding
         thetas (the analysis' worst case) are swept exhaustively over
         bits; and the F13 witness -- theta(2,4,4), found by a
         deterministic lexicographic search, out of habitat, all of whose
         admissible colourings have max g > 0 while NC1 is satisfiable,
         i.e. a shape only the g-detector rejects -- is asserted rejected,
         with the pinned counter-fact (the NC1 detector PASSES it) and an
         in-habitat negative control.

Exact throughout (integers and `fractions.Fraction`; no floats except in
printed rate summaries).  Wall-clock elapsed-time annotations (`[NNNs]`)
are printed by --law/--cap/--flip/--adv and are inherently
non-deterministic; every other byte of every mode is identical across
`PYTHONHASHSEED` values (the cflank precedent's corrected claim shape).  `subgraph_g` is pure cycle-rank arithmetic; rank
enters only through `gridcol.block_generic_zero` (GF(p) certified lower
bound) whose attaining draw is re-checked in exact Q here at every use,
through both the branch system and the landed `grid.dim_Z` (README §4
convention 2).  Rngs are seeded per mode and the seeds printed; no `set`
is printed.  Nothing samples a placement, so no figure is a rate over
sampled placements and `repin.star_generic` gates nothing below (§(K-clos)
(AC-9)'s discipline, as for `gridcol.py` / `cflank.py`).
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from closure import colourings                                         # noqa: E402
from grid import block_data, census_shapes, dim_Z                      # noqa: E402
from gridwit import a_and_M, structured_beta, subgraph_g               # noqa: E402
from gridcol import (block_generic_zero, class_shape, dim_W_branch,    # noqa: E402
                     multigraphs, subdivide)
from cflank import (CUBIC_N, admissible, cubic_habitat,                # noqa: E402
                    excess_profiles, flip_branch, hub_model,
                    length_tuples, nc1_violations)

G_SEED = 20260812


# ----------------------------------------------------- local devices --------

def two_ec_masks(pairs, kmin=2):
    """Connected bridgeless subsets of a branch list with cycle rank
    >= kmin, as (branch index tuple, k).  `pairs` = [(branch index,
    (end, end))] -- hub ends at `Lambda = empty` (precomputed once per
    shape), CONTRACTED ends at `Lambda != empty` (per block).

    Local device: by (GR-27) the (GR-8) maximum over ALL sub-multigraphs
    of H+ is a max over 2-edge-connected unions of full branch paths, and
    on an NC1-passing block (no binding circuit, classes exact) every
    binding subset contains a binding 2ec block with k >= 2 -- so this
    family is COMPLETE for the max-g <= 0 test there."""
    idxs = [k for (k, _e) in pairs]
    emap = dict(pairs)
    M = len(idxs)
    out = []
    for mask in range(1, 1 << M):
        ks = [idxs[j] for j in range(M) if mask >> j & 1]
        ends = emap
        vs = sorted({v for k in ks for v in ends[k]}, key=str)
        deg = {v: 0 for v in vs}
        for k in ks:
            deg[ends[k][0]] += 1
            deg[ends[k][1]] += 1
        if any(d < 2 for d in deg.values()):
            continue
        kk = len(ks) - len(vs) + 1
        if kk < kmin:
            continue
        adj = {v: [] for v in vs}
        for k in ks:
            adj[ends[k][0]].append((ends[k][1], k))
            adj[ends[k][1]].append((ends[k][0], k))
        seen, st = {vs[0]}, [vs[0]]
        while st:
            v = st.pop()
            for (u, _k) in adj[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        if len(seen) != len(vs):
            continue
        bridge = False
        for kd in ks:
            root = ends[kd][0]
            seen2, st2 = {root}, [root]
            while st2:
                v = st2.pop()
                for (u, k) in adj[v]:
                    if k != kd and u not in seen2:
                        seen2.add(u)
                        st2.append(u)
            if len(seen2) != len(vs):
                bridge = True
                break
        if not bridge:
            out.append((tuple(ks), kk))
    return out


def two_ec_subsets(hm, kmin=2):
    """`two_ec_masks` at the shape's own hub ends -- the `Lambda = empty`
    form, precomputed once per shape."""
    return two_ec_masks(list(enumerate(hm['ends'])), kmin)


def tec_candidates(hm, tec):
    """The colouring-independent pre-filter for BINDING subsets at
    `Lambda = empty`: a branch of length 4 or 5 has A(beta) >= 2 at every
    colouring, so defect(S) >= #{beta in S : l_beta >= 4}, and a binding S
    (defect <= 2) carries at most two such branches.  Exact -- discarded
    subsets are provably never binding -- and it is what makes the
    long-branch census shapes affordable."""
    lens = hm['lens']
    return [(ks, kk) for (ks, kk) in tec
            if sum(1 for k in ks if lens[k] >= 4) <= 2]


def branch_stats(hm, col, mine):
    """Per branch: (own-colour edge count A(beta), end-dart-is-own at the u
    side, at the w side) -- the whole colouring data the (GR-28) formula
    needs."""
    acnt, du, dw = [], [], []
    for (_u, _w, path) in hm['branches']:
        acnt.append(sum(1 for e in path if col[e] == mine))
        du.append(col[path[0]] == mine)
        dw.append(col[path[-1]] == mine)
    return acnt, du, dw


def g_formula(hm, stats, ks, kk):
    """(GR-28): g(S) = 3k - Sum_S A(beta) + aa2(S) at `Lambda = empty`.
    Valid ONLY when the shape has no length-1 branch (classes are then
    hub-local stars and interior singletons); `--law` cross-validates it
    against the exact `subgraph_g` at seeded pairs."""
    acnt, du, dw = stats
    ends = hm['ends']
    sA = sum(acnt[k] for k in ks)
    darts = {}
    for k in ks:
        u, w = ends[k]
        darts.setdefault(u, []).append(du[k])
        darts.setdefault(w, []).append(dw[k])
    aa2 = sum(1 for ds in darts.values() if len(ds) == 2 and all(ds))
    return 3 * kk - sA + aa2


def subset_eidx(bd, hm, ks):
    """The `bd['E']` indices of the own-colour edges on the branches `ks`."""
    esets = [set(hm['branches'][k][2]) for k in ks]
    return [i for i, e in enumerate(bd['E']) if any(e in s for s in esets)]


def gmax_exact_block(bd, hm, col, mine):
    """max(0, max_P g(P)) over the k >= 2 family EXACTLY, by (GR-27): the
    2ec-after-contraction branch subsets, exact `subgraph_g` on each.
    COMPLETE for an NC1-passing block (its k = 1 members never bind, and
    any binding subset contains a binding 2ec block).  Returns
    (gmax, witness branch tuple or None, contracted ends)."""
    cends, active = contracted_view(hm, col, mine)
    pairs = [(k, cends[k]) for k in active]
    best, wit = 0, None
    for (ks, _kk) in two_ec_masks(pairs):
        g = subgraph_g(bd, subset_eidx(bd, hm, ks))
        if g > best:
            best, wit = g, ks
    return best, wit, cends


def minimal_witnesses(bd, hm, tec, stats=None):
    """The minimal (by branch count) binding subsets of a block, with their
    g.  Uses the (GR-28) formula when `stats` is given (Lambda = empty),
    else the exact `subgraph_g`."""
    bysize = {}
    for (ks, kk) in tec:
        if stats is not None:
            g = g_formula(hm, stats, ks, kk)
        else:
            g = subgraph_g(bd, subset_eidx(bd, hm, ks))
        if g > 0:
            bysize.setdefault(len(ks), []).append((ks, kk, g))
    if not bysize:
        return []
    return bysize[min(bysize)]


def contracted_view(hm, col, mine):
    """The block's hub-level view: hubs merged along other-colour length-1
    branches (the Gamma_B contraction of (GR-16)(ii) for mine = 'A'), and
    the branches still carrying own-colour edges, with mapped ends.
    Returns (cends, active): per-branch mapped ends (None when the branch
    has no own-colour edge), and the active branch index list."""
    ends, lens, branches = hm['ends'], hm['lens'], hm['branches']
    parent = {v: v for v in hm['hubs']}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for k, (_u, _w, path) in enumerate(branches):
        if lens[k] == 1 and col[path[0]] != mine:
            u, w = ends[k]
            ru, rw = find(u), find(w)
            if ru != rw:
                parent[ru] = rw
    cends, active = [], []
    for k, (_u, _w, path) in enumerate(branches):
        if not any(col[e] == mine for e in path):
            cends.append(None)
            continue
        u, w = ends[k]
        cends.append((find(u), find(w)))
        active.append(k)
    return cends, active


def witness_profile(hm, ks, cends=None):
    """The (k, path-profile) classification of a witness subset: pendant
    branches pruned (a bridge leaves g unchanged, (GR-27)), then per core
    path (between contracted-degree >= 3 nodes) the branch-length tuple,
    canonicalized; pure-cycle components profiled directly.  The
    (GR-17)(d)-analogue datum.  `cends` (from `contracted_view`) supplies
    the block's contracted ends; default the G-degree hub ends
    (Lambda = empty)."""
    lens = hm['lens']
    ends = {k: (cends[k] if cends is not None else hm['ends'][k])
            for k in ks}
    live = [k for k in ks if ends[k] is not None]
    # prune pendants iteratively (they carry no cycle, g is unchanged)
    while True:
        deg = {}
        for k in live:
            for v in ends[k]:
                deg[v] = deg.get(v, 0) + 1
        drop = [k for k in live
                if deg[ends[k][0]] == 1 or deg[ends[k][1]] == 1]
        if not drop:
            break
        live = [k for k in live if k not in drop]
    if not live:
        return 0, ()
    deg = {}
    for k in live:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    kk = len(live) - len(deg) + \
        _ncomp({v for v in deg}, [ends[k] for k in live])
    core = {v for v, d in deg.items() if d >= 3}
    adj = {}
    for k in live:
        u, w = ends[k]
        adj.setdefault(u, []).append((w, k))
        adj.setdefault(w, []).append((u, k))
    used, profs = set(), []
    for v in sorted(core, key=str):
        for (u, k0) in list(adj[v]):
            if k0 in used:
                continue
            path, cur, k = [lens[k0]], u, k0
            used.add(k0)
            while cur not in core:
                nxt = [(x, kx) for (x, kx) in adj[cur]
                       if kx != k and kx not in used]
                if not nxt:
                    break
                cur, k = nxt[0]
                used.add(k)
                path.append(lens[k])
            profs.append(tuple(min(path, path[::-1])))
    # remaining branches form core-free cycles; profile each
    rest = [k for k in live if k not in used]
    while rest:
        k0 = rest[0]
        comp, front = {k0}, {ends[k0][0], ends[k0][1]}
        changed = True
        while changed:
            changed = False
            for k in rest:
                if k not in comp and (ends[k][0] in front or
                                      ends[k][1] in front):
                    comp.add(k)
                    front |= {ends[k][0], ends[k][1]}
                    changed = True
        profs.append(tuple(sorted(lens[k] for k in comp)))
        rest = [k for k in rest if k not in comp]
    return kk, tuple(sorted(profs))


def _ncomp(vs, es):
    parent = {v: v for v in vs}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for (u, w) in es:
        ru, rw = find(u), find(w)
        if ru != rw:
            parent[ru] = rw
    return len({find(v) for v in vs})


def minimal_wits_general(bd, hm, col, mine):
    """The minimal (by branch count) binding subsets of a block at ANY
    Lambda content: the 2ec-after-contraction subsets in size order, exact
    `subgraph_g`, stop at the first binding size.  Complete on NC1-passing
    blocks for the same reason as `gmax_exact_block`.  Used only on (rare)
    hit blocks.  Returns (witness list, contracted ends)."""
    cends, active = contracted_view(hm, col, mine)
    pairs = [(k, cends[k]) for k in active]
    tec = sorted(two_ec_masks(pairs), key=lambda x: len(x[0]))
    out, size = [], None
    for (ks, _kk) in tec:
        if size is not None and len(ks) > size:
            break
        g = subgraph_g(bd, subset_eidx(bd, hm, ks))
        if g > 0:
            out.append((ks, g))
            size = len(ks)
    return out, cends


def probe_block(bd, edges, allverts, hm, col, mine, rng):
    """One block of the *Step G23* probe.  Returns
    ('zero', sval)                        -- proven generic dim Z = 0, or
    ('hit', a, beta, gmax, wit)           -- proven dim Z >= gmax > 0, or
    ('anomaly', a, None)                  -- neither (a (GR-4') alarm).
    A candidate anomaly is retried at 6 more draws before being reported
    (*Step G4* item 1: a rank miss at one parameter point is not a miss of
    the recipe)."""
    sv = block_generic_zero(bd, hm['hubs'], hm['branches'], rng)
    if sv is not None:
        assert dim_W_branch(bd, hm['hubs'], hm['branches'], sval=sv) == 0
        assert dim_Z(bd, sval=sv) == 0, "branch model vs grid.dim_Z"
        return ('zero', sv)
    a, _M = a_and_M(bd, edges, allverts)
    gmax, wit, _cends = gmax_exact_block(bd, hm, col, mine)
    if a > 0 or gmax > 0:
        beta, _part = structured_beta(bd)
        return ('hit', a, beta, gmax, wit)
    sv = block_generic_zero(bd, hm['hubs'], hm['branches'], rng, draws=6)
    if sv is not None:
        assert dim_W_branch(bd, hm['hubs'], hm['branches'], sval=sv) == 0
        assert dim_Z(bd, sval=sv) == 0, "branch model vs grid.dim_Z"
        return ('zero', sv)
    return ('anomaly', a, None)


def nc1_from_bd(hm, col, bd, mine):
    """Per-block NC1: >= 3 distinct own-colour classes on every binding
    circuit, classes read off `grid.block_data` (exact at any Lambda,
    exactly as `cflank.nc1_violations` does for the two-block form)."""
    if not hm['binding']:
        return True
    cls_of = {e: c for e, c in zip(bd['E'], bd['cls'])}
    for (_cyc, walk) in hm['binding']:
        eseq = [e for (k, _, _) in walk for e in hm['branches'][k][2]]
        d = len({cls_of[e] for e in eseq if col[e] == mine})
        if d < 3:
            return False
    return True


def pool_specs():
    """The Lambda = empty D = 0 stratum, exactly CFLANK's `--cubic` pool."""
    for n in CUBIC_N:
        M = 3 * n // 2
        for hedges in multigraphs(n, M):
            for exc in excess_profiles(M, 6):
                yield n, [(u, w, 2 + e) for (u, w), e in zip(hedges, exc)]


def hub_degree_excess(hm):
    deg = {}
    for (u, w) in hm['ends']:
        deg[u] = deg.get(u, 0) + 1
        deg[w] = deg.get(w, 0) + 1
    return sum(d - 3 for d in deg.values())


# --------------------------------------------- [GCP-1] --probe: Step G23 ----

def leg_probe():
    """[GCP-1] Step G23's scoping probe as committed evidence + the census
    hit classification + the sample-bias correction."""
    import random
    print(f"[GCP-1] Step G23's scoping probe, re-established (seed "
          f"{G_SEED + 1}); then the full census")
    rng = random.Random(G_SEED + 1)
    # ---- part 1: the 45-shape reproduction ----
    shapes = cols_n = blocks = 0
    hits = []
    for label, edges in census_shapes():
        shapes += 1
        if shapes > 45:
            break
        hm = hub_model(edges)
        if hm is None:
            continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 16)
        assert not odd and cols is not None
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            if nc1_violations(hm, col, edges, allverts):
                continue
            cols_n += 1
            for mine in ('A', 'B'):
                blocks += 1
                bd = block_data(edges, allverts, col, mine)
                r = probe_block(bd, edges, allverts, hm, col, mine, rng)
                if r[0] == 'zero':
                    continue
                assert r[0] == 'hit', \
                    f"probe anomaly at {label}: neither zero nor explained"
                _tag, a, beta, gmax, _wit = r
                lam_shape = any(L == 1 for L in hm['lens'])
                wits, cends = minimal_wits_general(bd, hm, col, mine)
                assert wits, f"hit at {label} with no minimal witness"
                hits.append((label, mine, a, beta, gmax, lam_shape,
                             witness_profile(hm, wits[0][0], cends)))
    print(f"  45 census shapes: {cols_n} balanced, no-mono-hub, "
          f"NC1-satisfying colourings = {blocks} blocks")
    print(f"  {len(hits)} blocks with generic dim Z > 0 -- each PROVEN "
          f"positive by an explicit (GR-8) witness, not sampled")
    assert cols_n == 572 and len(hits) == 16, \
        "Step G23's 16-of-572 figure does not reproduce"
    assert all(h[2] == 0 for h in hits), "a hit with a > 0"
    assert all(h[3] == 1 for h in hits), "structured (GR-8) max != 1"
    assert all(h[4] == 1 for h in hits), "exact (GR-8) max != 1"
    assert all(h[5] for h in hits), "a 45-prefix hit off Lambda != empty"
    kk = sorted({h[6][0] for h in hits})
    print(f"  all 16: a = 0, structured max = exact max = 1, on "
          f"Lambda != empty shapes; witness cycle ranks {kk}")
    assert kk == [2], "a minimal witness that is not a theta"
    # ---- part 2: the full census ----
    shapes = cols_n = blocks = zero = clean_unc = 0
    hits = []
    for label, edges in census_shapes():
        hm = hub_model(edges)
        if hm is None:
            continue
        shapes += 1
        lam_shape = any(L == 1 for L in hm['lens'])
        # at Lambda = empty the (GR-28) formula computes every g exactly
        # over a per-shape 2ec list (cross-validated in --law), so the
        # rank probe is spent only on formula-clean blocks; at the two
        # shapes with > 4096 colourings the clean blocks are rank-
        # certified at a seeded 5 % sample (disclosed below) -- their
        # binding status stays exact, only the (GR-4')-anomaly watch is
        # sampled there
        tec = (None if lam_shape
               else tec_candidates(hm, two_ec_subsets(hm)))
        tec_sz = (sorted(tec, key=lambda x: len(x[0]))
                  if tec is not None else None)
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 16)
        assert not odd and cols is not None
        heavy = len(cols) > 4096 and not lam_shape
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            if nc1_violations(hm, col, edges, allverts):
                continue
            cols_n += 1
            for mine in ('A', 'B'):
                blocks += 1
                if not lam_shape:
                    stats = branch_stats(hm, col, mine)
                    gm = 0
                    for (ks, kk) in tec:
                        gm = max(gm, g_formula(hm, stats, ks, kk))
                    if gm > 0:
                        bd = block_data(edges, allverts, col, mine)
                        a, _M = a_and_M(bd, edges, allverts)
                        assert a == 0, f"{label}: a > 0 at Lambda = empty"
                        beta, _p = structured_beta(bd)
                        best = min(len(ks) for (ks, kk) in tec_sz
                                   if g_formula(hm, stats, ks, kk) > 0)
                        w0 = next(ks for (ks, kk) in tec_sz
                                  if len(ks) == best and
                                  g_formula(hm, stats, ks, kk) > 0)
                        # the witness is a PROOF of dim Z >= 1 by (GR-8);
                        # re-check it through the exact subgraph_g
                        assert subgraph_g(bd, subset_eidx(bd, hm, w0)) > 0
                        hits.append((label, mine, 0, beta, gm, lam_shape,
                                     witness_profile(hm, w0)))
                        continue
                    if heavy and rng.random() >= 0.05:
                        clean_unc += 1
                        continue
                bd = block_data(edges, allverts, col, mine)
                r = probe_block(bd, edges, allverts, hm, col, mine, rng)
                if r[0] == 'zero':
                    zero += 1
                    continue
                assert r[0] == 'hit', f"probe anomaly at {label}"
                _tag, a, beta, gmax, _wit = r
                wits, cends = minimal_wits_general(bd, hm, col, mine)
                assert wits, f"hit at {label} with no minimal witness"
                hits.append((label, mine, a, beta, gmax, lam_shape,
                             witness_profile(hm, wits[0][0], cends)))
    print(f"  full census: {shapes} shapes, {cols_n} NC1-passing admissible "
          f"colourings, {blocks} blocks: {zero} certified generic "
          f"dim Z = 0 (exact-Q point), {len(hits)} proven dim Z > 0, "
          f"{clean_unc} formula-clean blocks at the two > 4096-colouring "
          f"shapes carried by the sampled certification, 0 unexplained")
    assert zero + clean_unc + len(hits) == blocks
    assert all(h[2] == 0 for h in hits), "a census hit with a > 0"
    gdist = {}
    kdist = {}
    lam_hits = 0
    profs = {}
    for h in hits:
        gdist[h[4]] = gdist.get(h[4], 0) + 1
        kdist[h[6][0]] = kdist.get(h[6][0], 0) + 1
        if h[5]:
            lam_hits += 1
        profs[h[6][1]] = profs.get(h[6][1], 0) + 1
    print(f"  hit exact-gmax distribution: " +
          ", ".join(f"g={g}:{gdist[g]}" for g in sorted(gdist)))
    print(f"  hit witness cycle ranks: " +
          ", ".join(f"k={k}:{kdist[k]}" for k in sorted(kdist)))
    print(f"  hits on Lambda != empty shapes: {lam_hits}/{len(hits)}")
    lam0 = len(hits) - lam_hits
    print(f"  => THE CORRECTION: {lam0} census hits live on Lambda = EMPTY "
          f"shapes -- Step G23's 'all on Lambda != empty' clause was an "
          f"artifact of the 45-shape prefix (the census generator requires "
          f"a length-3 branch and orders the K4 stratum lexicographically, "
          f"so the prefix is all K4(1,...))" if lam0 else
          "  (no Lambda = empty census hit; the census's Lambda = empty "
          "slice is thin -- the pool sweep in --law carries that half)")
    print(f"  witness path-profile list (the (GR-17)(d) analogue; every "
          f"witness a union of core paths):")
    for p in sorted(profs, key=str):
        print(f"    {p}: {profs[p]}")
    assert all(h[4] == 1 for h in hits), \
        "a census hit with exact gmax >= 2 -- the cap is broken"
    print(f"  every hit has exact gmax = 1 and a k = 2 (theta) minimal "
          f"witness family" if kdist == {2: len(hits)} else
          f"  NOTE: non-theta minimal witnesses occur: {kdist}")
    print()


# ------------------------------------------------- [GCP-2] --law: (GR-28) ---

def leg_law():
    """[GCP-2] the exact-g law on the Lambda = empty D = 0 stratum."""
    import random
    import time
    print(f"[GCP-2] (GR-27)/(GR-28) on the Lambda = empty D = 0 stratum "
          f"(seed {G_SEED + 2})")
    rng = random.Random(G_SEED + 2)
    t0 = time.time()
    shapes = blocks = binding = xval = azero = 0
    gdist = {}
    profs = {}
    percshape = {}
    for n, specs in pool_specs():
        edges = class_shape(specs)
        if edges is None:
            continue
        hm = hub_model(edges)
        if hm is None:
            continue
        assert all(L >= 2 for L in hm['lens'])
        shapes += 1
        tec = tec_candidates(hm, two_ec_subsets(hm))
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 16)
        assert not odd and cols is not None
        nbind = 0
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            if nc1_violations(hm, col, edges, allverts):
                continue
            for mine in ('A', 'B'):
                blocks += 1
                stats = branch_stats(hm, col, mine)
                gm = 0
                for (ks, kk) in tec:
                    gm = max(gm, g_formula(hm, stats, ks, kk))
                gdist[gm] = gdist.get(gm, 0) + 1
                # seeded cross-validation: formula == exact subgraph_g,
                # and a == 0, on ~0.1 % of (block, subset) pairs
                if rng.random() < 0.001:
                    bd = block_data(edges, allverts, col, mine)
                    a, _ = a_and_M(bd, edges, allverts)
                    assert a == 0, f"a = {a} > 0 at Lambda = empty {specs}"
                    azero += 1
                    for (ks, kk) in tec:
                        ge = subgraph_g(bd, subset_eidx(bd, hm, ks))
                        gf = g_formula(hm, stats, ks, kk)
                        assert ge == gf, \
                            f"(GR-28) formula {gf} != exact {ge} at {specs}"
                        xval += 1
                if gm > 0:
                    binding += 1
                    nbind += 1
                    bd = block_data(edges, allverts, col, mine)
                    for (ks, kk, g) in minimal_witnesses(bd, hm, tec, stats):
                        k2, prof = witness_profile(hm, ks)
                        profs[(k2, prof)] = profs.get((k2, prof), 0) + 1
        if nbind:
            percshape[nbind] = percshape.get(nbind, 0) + 1
    print(f"  {shapes} shapes (the whole stratum), every admissible "
          f"colouring, both blocks: {blocks} NC1-passing blocks  "
          f"[{time.time() - t0:.0f}s]")
    print(f"  exact max_P g(P) distribution over them: " +
          ", ".join(f"g={g}:{gdist[g]}" for g in sorted(gdist)))
    assert max(gdist) <= 1, \
        "THE CAP IS BROKEN: an NC1-passing block with max g >= 2"
    print(f"  => THE CAP: max_P g(P) <= 1 at every NC1-passing admissible "
          f"block of the stratum (the k = 2 case is proven; this asserts "
          f"all k)")
    print(f"  binding blocks (g = 1): {binding} "
          f"({100.0 * binding / blocks:.2f}% of NC1-passing); shapes "
          f"carrying any: {sum(percshape.values())}/{shapes}")
    print(f"  cross-validated: formula vs subgraph_g at {xval} "
          f"(block, subset) pairs, a = 0 at {azero} sampled blocks")
    kdist = {}
    for (k2, _prof), c in profs.items():
        kdist[k2] = kdist.get(k2, 0) + c
    print(f"  minimal witness cycle ranks: " +
          ", ".join(f"k={k}:{kdist[k]}" for k in sorted(kdist)))
    print(f"  realized core-path profiles (top 12 by count):")
    tot = sum(profs.values())
    for (k2, prof), c in sorted(profs.items(), key=lambda x: -x[1])[:12]:
        print(f"    k={k2} {prof}: {c}")
    if len(profs) > 12:
        print(f"    ... {len(profs)} distinct profiles in total, "
              f"{tot} witness instances")
    print()


# --------------------------------------------- [GCP-3] --cap: the target ----

def good_colouring(edges, allverts, hm, cols, lam):
    """The first admissible colouring with a = 0 and exact max g <= 0 in
    both blocks; returns (index-among-good-candidates, colouring) or None.
    At `lam` (Lambda != empty) everything is exact `subgraph_g` +
    `a_and_M`; at Lambda = empty the (GR-28) formula carries the g half
    and a = 0 is (GR-28)'s (asserted separately in --law)."""
    tec = (None if lam
           else tec_candidates(hm, two_ec_subsets(hm)))
    tried = 0
    for col in cols:
        if not admissible(edges, allverts, hm, col):
            continue
        tried += 1
        ok = True
        for mine in ('A', 'B'):
            if lam:
                bd = block_data(edges, allverts, col, mine)
                if not nc1_from_bd(hm, col, bd, mine):
                    ok = False
                    break
                a, _ = a_and_M(bd, edges, allverts)
                if a > 0:
                    ok = False
                    break
                gm, _wit, _ce = gmax_exact_block(bd, hm, col, mine)
                if gm > 0:
                    ok = False
                    break
            else:
                stats = branch_stats(hm, col, mine)
                if any(g_formula(hm, stats, ks, kk) > 0
                       for (ks, kk) in tec):
                    ok = False
                    break
        if ok and not lam and nc1_violations(hm, col, edges, allverts):
            ok = False
        if ok:
            return tried, col
    return None


def leg_cap():
    """[GCP-3] the colouring-existence target at every D = 0 shape."""
    import random
    import time
    print(f"[GCP-3] THE TARGET: a = 0 and max_P g(P) <= 0 in both blocks "
          f"at some admissible colouring, every D = 0 shape "
          f"(seed {G_SEED + 3})")
    rng = random.Random(G_SEED + 3)
    t0 = time.time()

    def sweep(name, pool, lam):
        shapes = miss = 0
        hist = {}
        checked = 0
        for edges in pool:
            hm = hub_model(edges)
            if hm is None:
                continue
            shapes += 1
            allverts = sorted(verts_of(edges), key=str)
            cols, odd = colourings(edges, cap=1 << 13)
            assert not odd and cols is not None
            r = good_colouring(edges, allverts, hm, cols, lam)
            if r is None:
                miss += 1
                print(f"  *** TARGET MISS in {name}")
                continue
            tried, col = r
            hist[tried] = hist.get(tried, 0) + 1
            # seeded cross-check: the g-certificate against an exact
            # rational dim Z = 0 point, through both matrices
            if rng.random() < (0.02 if lam else 0.005):
                for mine in ('A', 'B'):
                    bd = block_data(edges, allverts, col, mine)
                    sv = block_generic_zero(bd, hm['hubs'], hm['branches'],
                                            rng, draws=4)
                    assert sv is not None, \
                        f"{name}: g-certificate without a dim Z = 0 point"
                    assert dim_W_branch(bd, hm['hubs'], hm['branches'],
                                        sval=sv) == 0
                    assert dim_Z(bd, sval=sv) == 0
                checked += 1
        top = sorted(hist)[:6]
        print(f"  {name}: {shapes} shapes, target satisfied at "
              f"{shapes - miss}/{shapes}; first-good-colouring histogram " +
              ", ".join(f"{k}:{hist[k]}" for k in top) +
              (" ..." if len(hist) > 6 else "") +
              f"; dim Z = 0 cross-checked at {checked} shapes "
              f"[{time.time() - t0:.0f}s]")
        return miss

    m1 = sweep("Lambda = empty D = 0 pool",
               (e for e in (class_shape(s) for _n, s in pool_specs())
                if e is not None), lam=False)
    cen = []
    for _label, edges in census_shapes():
        hm = hub_model(edges)
        if hm is not None and hub_degree_excess(hm) == 0:
            cen.append(edges)
    m2 = sweep("census D = 0 (Lambda mixed)", iter(cen), lam=True)
    lamp = []
    for (n, M, cap) in ((2, 3, 99), (4, 6, 99)):
        tgt = 6 * (M - n + 1)
        for hedges in multigraphs(n, M):
            for lens in length_tuples(M, tgt, lamcap=cap):
                if any(L == 1 for L in lens) and \
                        cubic_habitat(n, hedges, list(lens)):
                    specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
                    e = class_shape(specs)
                    if e is not None:
                        lamp.append(e)
    m3 = sweep("Lambda != empty n <= 4 pool", iter(lamp), lam=True)
    assert m1 == m2 == m3 == 0, "the colouring-existence target misses"
    print(f"  => the target statement holds at EVERY swept D = 0 shape.")
    print()


# ------------------------------------------------ [GCP-4] --flip: repair ----

def leg_flip():
    """[GCP-4] the repair mechanics, both halves."""
    import random
    import time
    print(f"[GCP-4] the repair: single-flips at Lambda = empty binding "
          f"blocks; the odd-pair flip at no-even-branch circuits "
          f"(seed {G_SEED + 4})")
    rng = random.Random(G_SEED + 4)
    t0 = time.time()
    # ---- half 1: Lambda = empty binding blocks: repair DISTANCE ----

    def fully_good(edges, allverts, hm, tec, col):
        if not admissible(edges, allverts, hm, col):
            return False
        if nc1_violations(hm, col, edges, allverts):
            return False
        sA = branch_stats(hm, col, 'A')
        sB = branch_stats(hm, col, 'B')
        return all(g_formula(hm, sA, ks, kk) <= 0 and
                   g_formula(hm, sB, ks, kk) <= 0 for (ks, kk) in tec)

    checked = 0
    dist = {}
    unrep = {}
    for n, specs in pool_specs():
        edges = class_shape(specs)
        if edges is None:
            continue
        hm = hub_model(edges)
        if hm is None:
            continue
        tec = tec_candidates(hm, two_ec_subsets(hm))
        if not tec:
            continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 16)
        assert not odd and cols is not None
        M = len(hm['lens'])
        evens = [k for k in range(M) if hm['lens'][k] % 2 == 0]
        odds = [k for k in range(M) if hm['lens'][k] % 2]
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            if nc1_violations(hm, col, edges, allverts):
                continue
            sA = branch_stats(hm, col, 'A')
            sB = branch_stats(hm, col, 'B')
            if all(g_formula(hm, sA, ks, kk) <= 0 and
                   g_formula(hm, sB, ks, kk) <= 0 for (ks, kk) in tec):
                continue
            checked += 1
            # balance-preserving moves in increasing size: one even flip;
            # an opposite-parity odd pair; two even flips
            moves = [[k] for k in evens]
            moves += [[k1, k2] for i, k1 in enumerate(odds)
                      for k2 in odds[i + 1:]]
            moves += [[k1, k2] for i, k1 in enumerate(evens)
                      for k2 in evens[i + 1:]]
            done = None
            for mv in moves:
                c2 = col
                for k in mv:
                    c2 = flip_branch(edges, c2, hm['branches'][k][2])
                if fully_good(edges, allverts, hm, tec, c2):
                    done = ('1-even' if len(mv) == 1 else
                            ('odd-pair' if hm['lens'][mv[0]] % 2
                             else '2-even'))
                    break
            if done is None:
                key = tuple(sorted(hm['lens']))
                unrep[key] = unrep.get(key, 0) + 1
            else:
                dist[done] = dist.get(done, 0) + 1
    nun = sum(unrep.values())
    print(f"  Lambda = empty binding blocks: {checked}; repaired to a "
          f"FULLY-good colouring (a = 0, max g <= 0 in both blocks) by a "
          f"balance-preserving move: " +
          ", ".join(f"{k}:{dist[k]}" for k in sorted(dist)) +
          f"; unrepaired within two flips: {nun}  "
          f"[{time.time() - t0:.0f}s]")
    if unrep:
        print(f"  unrepaired-block shapes by length multiset: " +
              ", ".join(f"{k}:{unrep[k]}" for k in sorted(unrep)))
    print(f"  (existence at every shape is [GCP-3]'s figure; this measures "
          f"the LOCALITY of the repair, and two flips do{'' if nun == 0 else ' NOT'} "
          f"suffice on the swept stratum)")
    # ---- half 2: the odd-pair flip at no-even-branch binding circuits ----
    # The n <= 4 pool carries NO violated no-even-branch circuit (asserted
    # below), so the habitat for CFLANK item (v) is CONSTRUCTED here: n = 6
    # cubic multigraphs with a triangle carrying the all-odd binding
    # profiles (1,3,3) (needs |Lambda| = 1) and (1,1,5) (|Lambda| = 2), the
    # remaining excess enumerated, capped at the first 150 shapes per
    # profile (disclosed -- a targeted construction, not a pool sweep).
    tested = fixed = 0
    fails = {}
    n4_noeven = n4_tested = 0
    for (n, M, cap) in ((2, 3, 99), (4, 6, 99)):
        tgt = 6 * (M - n + 1)
        for hedges in multigraphs(n, M):
            for lens in length_tuples(M, tgt, lamcap=cap):
                if not cubic_habitat(n, hedges, list(lens)):
                    continue
                specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
                edges = class_shape(specs)
                if edges is None:
                    continue
                hm = hub_model(edges)
                if hm is None:
                    continue
                noeven = [cyc for (cyc, _w) in hm['binding']
                          if not any(hm['lens'][k] % 2 == 0 for k in cyc)]
                if not noeven:
                    continue
                n4_noeven += 1
                allverts = sorted(verts_of(edges), key=str)
                cols, odd = colourings(edges, cap=1 << 13)
                assert not odd and cols is not None
                for col in cols:
                    if not admissible(edges, allverts, hm, col):
                        continue
                    if any(c in noeven for c in
                           nc1_violations(hm, col, edges, allverts)):
                        n4_tested += 1
    print(f"  n <= 4 pool: {n4_noeven} shapes carry a no-even-branch "
          f"binding circuit, but {n4_tested} admissible colourings "
          f"violate one -- item (v)'s live instances start at n = 6 "
          f"(constructed below)")
    assert n4_tested == 0

    def item_v_shapes():
        M = 9
        for prof in ((1, 3, 3), (1, 1, 5)):
            got = 0
            for hedges in multigraphs(6, M):
                tris = [(i, j, k)
                        for i in range(M) for j in range(i + 1, M)
                        for k in range(j + 1, M)
                        if len({v for e in (hedges[i], hedges[j],
                                            hedges[k]) for v in e}) == 3]
                for tri in tris:
                    rest = [k for k in range(M) if k not in tri]
                    exc_tri = sum(L - 2 for L in prof)
                    for exc in excess_profiles(len(rest), 6 - exc_tri):
                        lens = [0] * M
                        for t, L in zip(tri, prof):
                            lens[t] = L
                        for r, e in zip(rest, exc):
                            lens[r] = 2 + e
                        if not cubic_habitat(6, hedges, lens):
                            continue
                        if got >= 150:
                            return
                        got += 1
                        yield [(u, w, L)
                               for (u, w), L in zip(hedges, lens)]

    for specs in item_v_shapes():
        edges = class_shape(specs)
        if edges is None:
            continue
        hm = hub_model(edges)
        if hm is None:
            continue
        noeven = [cyc for (cyc, w) in hm['binding']
                  if not any(hm['lens'][k] % 2 == 0 for k in cyc)]
        if not noeven:
            continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 13)
        assert not odd and cols is not None
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            bad = [c for c in
                   nc1_violations(hm, col, edges, allverts)
                   if c in noeven]
            if not bad:
                continue
            tested += 1
            cyc = bad[0]
            ok = False
            allodd = [k for k in range(len(hm['lens']))
                      if hm['lens'][k] % 2]
            for k in cyc:
                if hm['lens'][k] % 2 == 0:
                    continue
                for k2 in allodd:
                    if k2 == k:
                        continue
                    c2 = flip_branch(edges, col,
                                     hm['branches'][k][2])
                    c2 = flip_branch(edges, c2,
                                     hm['branches'][k2][2])
                    if not admissible(edges, allverts, hm, c2):
                        continue
                    if cyc in nc1_violations(hm, c2, edges,
                                             allverts):
                        continue
                    ok = True
                    break
                if ok:
                    break
            if ok:
                fixed += 1
            else:
                key = tuple(sorted(hm['lens'][k] for k in cyc))
                fails[key] = fails.get(key, 0) + 1
    print(f"  no-even-branch binding circuits (profiles (1,3,3)/(1,1,5)), "
          f"constructed n = 6 shapes: {tested} violated (colouring, "
          f"circuit) instances; the balance-preserving odd-pair flip "
          f"repairs {fixed}/{tested}")
    if fails:
        print(f"  failures by circuit profile: " +
              ", ".join(f"{k}:{fails[k]}" for k in sorted(fails)))
    print()


# ---------------------------------------------- [GCP-5] --adv: the control --

# The F13 witness for the g-DETECTOR is CONSTRUCTED inside leg_adv by a
# deterministic lexicographic search (thetas first, then K4s) that is
# re-run on every invocation, so nothing depends on an unrecorded probe;
# the expected first hit theta(2,4,4) also has a two-line hand proof
# recorded in the draft (both length-4 path costs are bit-independent, so
# (GR-28) pins g(theta) = 1 at every admissible colouring, while NC1 needs
# only corner darts the bits can arrange).
def leg_adv():
    """[GCP-5] the falsification control + the F13 witness."""
    import random
    import time
    import itertools
    print(f"[GCP-5] the adversarial leg (seed {G_SEED + 5})")
    rng = random.Random(G_SEED + 5)
    t0 = time.time()
    # ---- (i) binding-theta-rich constructions ----
    # The --law characterization says a binding theta needs defect 2 and its
    # cost-0 paths are short; stack as many witness-shaped thetas as the
    # budget allows: the K4-minus-a-branch pattern embeds once per excess-
    # carrying pair of branches, so the densest cases are the n = 4 shapes
    # (whole budget on one K4) and prisms/K33 with paired long branches.
    K4H = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    PRISM = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    K33 = [(i, 3 + j) for i in range(3) for j in range(3)]
    targets = []
    for lens in itertools.product((2, 3, 4, 5), repeat=6):
        if sum(L - 2 for L in lens) == 6:
            targets.append(('K4', K4H, lens))
    for base, hedges in (('prism', PRISM), ('K33', K33)):
        for pat in itertools.combinations(range(len(hedges)), 2):
            lens = [2] * len(hedges)
            for k in pat:
                lens[k] = 5
            targets.append((base, hedges, tuple(lens)))
    worst = (0, None)
    swept = 0
    for (base, hedges, lens) in targets:
        n = 1 + max(max(u, w) for (u, w) in hedges)
        if not cubic_habitat(n, hedges, list(lens)):
            continue
        specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
        edges = class_shape(specs) if len(hedges) <= 6 else subdivide(specs)
        if edges is None:
            continue
        hm = hub_model(edges)
        tec = tec_candidates(hm, two_ec_subsets(hm))
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 16)
        assert not odd and cols is not None
        adm = good = bind = 0
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            adm += 1
            if nc1_violations(hm, col, edges, allverts):
                continue
            gA = max((g_formula(hm, branch_stats(hm, col, 'A'), ks, kk)
                      for (ks, kk) in tec), default=0)
            gB = max((g_formula(hm, branch_stats(hm, col, 'B'), ks, kk)
                      for (ks, kk) in tec), default=0)
            if gA > 0 or gB > 0:
                bind += 1
            else:
                good += 1
        swept += 1
        assert adm > 0 and good > 0, \
            f"adversarial target {base}{lens} defeats the target statement"
        rate = bind / adm
        if rate > worst[0]:
            worst = (rate, (base, lens, adm, bind, good))
    print(f"  (i) {swept} binding-theta-rich constructions swept "
          f"exhaustively over bits; every one keeps a fully-good "
          f"colouring; worst binding-block rate "
          f"{worst[0]:.3f} at {worst[1][0]}{worst[1][1]} "
          f"(adm {worst[1][2]}, binding {worst[1][3]}, good {worst[1][4]}) "
          f"[{time.time() - t0:.0f}s]")
    # ---- (ii) the F13 witness for the g-detector ----
    # deterministic search, thetas first then K4s in lexicographic order:
    # a Lambda = empty shape OUT of habitat, admissible colourings exist,
    # NC1 satisfiable at one of them, and EVERY admissible colouring has
    # max g > 0 in a block.  Expected first hit: theta(2,4,4) -- its two
    # length-4 path costs are bit-independent, so g(theta) = 1 at every
    # admissible colouring by (GR-28), while NC1 is satisfied by any
    # colouring with the right corner darts (a hand proof the assert
    # re-checks).
    THETA = [(0, 1)] * 3
    cands = [(THETA, lens) for lens in
             itertools.product((2, 3, 4, 5), repeat=3)]
    cands += [(K4H, lens) for lens in
              itertools.product((2, 3, 4, 5), repeat=6)]
    found = None
    for hedges, lens in cands:
        specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
        if class_shape(specs) is not None:
            continue                       # in habitat: not a witness
        edges = subdivide(specs)
        hm = hub_model(edges)
        if hm is None:
            continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=1 << 10)
        if odd or cols is None:
            continue
        tec = tec_candidates(hm, two_ec_subsets(hm))
        adm = nc1ok = good = 0
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            adm += 1
            n1 = not nc1_violations(hm, col, edges, allverts)
            if n1:
                nc1ok += 1
            gA = max((g_formula(hm, branch_stats(hm, col, 'A'), ks, kk)
                      for (ks, kk) in tec), default=0)
            gB = max((g_formula(hm, branch_stats(hm, col, 'B'), ks, kk)
                      for (ks, kk) in tec), default=0)
            if n1 and gA <= 0 and gB <= 0:
                good += 1
        if adm > 0 and nc1ok > 0 and good == 0:
            found = (hedges, lens, adm, nc1ok)
            break
    assert found is not None, "no F13 witness for the g-detector"
    hedges, lens, adm, nc1ok = found
    name = 'theta' if len(hedges) == 3 else 'K4'
    specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
    edges = subdivide(specs)
    V = len(verts_of(edges))
    why = []
    if 5 * len(edges) != 6 * (V - 1):
        why.append(f"not tight (5|E| = {5 * len(edges)} != "
                   f"{6 * (V - 1)} = 6(|V|-1))")
    hm0 = hub_model(edges)
    short = [sum(hm0['lens'][k] for k in cyc)
             for (cyc, _w) in hm0['binding']]
    if any(s < 7 for s in short):
        why.append(f"girth {min(short)} < 7")
    print(f"  (ii) F13 witness {name}{lens}: OUT of habitat "
          f"({'; '.join(why)}; class_shape rejects it); {adm} admissible "
          f"colourings, {nc1ok} of them NC1-passing, 0 with max g <= 0 in "
          f"both blocks -> the g-detector reports a MISS and must")
    print(f"    pinned counter-fact: the NC1 detector -- (GR-26)(i)'s "
          f"criterion -- PASSES this shape ({nc1ok} NC1-satisfying "
          f"colourings), so the (GR-8)-general detector is strictly "
          f"stronger than NC1 exactly as *Step G28* item (vi) required")
    # exact rank confirmation at one NC1-passing colouring: dim Z >= 1
    # proven by the witness, and measured >= 1 at seeded draws
    edges = subdivide(specs)
    hm = hub_model(edges)
    allverts = sorted(verts_of(edges), key=str)
    cols, odd = colourings(edges, cap=1 << 10)
    conf = False
    for col in cols:
        if not admissible(edges, allverts, hm, col):
            continue
        if nc1_violations(hm, col, edges, allverts):
            continue
        for mine in ('A', 'B'):
            stats = branch_stats(hm, col, mine)
            tec = tec_candidates(hm, two_ec_subsets(hm))
            wits = [(ks, kk) for (ks, kk) in tec
                    if g_formula(hm, stats, ks, kk) > 0]
            if not wits:
                continue
            bd = block_data(edges, allverts, col, mine)
            ge = subgraph_g(bd, subset_eidx(bd, hm, wits[0][0]))
            assert ge > 0
            sv = block_generic_zero(bd, hm['hubs'], hm['branches'], rng)
            assert sv is None, "witness block reached dim Z = 0"
            conf = True
            break
        if conf:
            break
    assert conf, "no NC1-passing binding block re-confirmed at the witness"
    print(f"    the witness's binding block re-confirmed: exact subgraph_g "
          f"> 0 (a PROOF of generic dim Z > 0 via (GR-8)), and no "
          f"dim Z = 0 draw found")
    # negative control: an in-habitat K4 accepted end to end
    ctl = [(0, 1, 3), (0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3),
           (2, 3, 3)]
    edges = class_shape(ctl)
    assert edges is not None
    hm = hub_model(edges)
    allverts = sorted(verts_of(edges), key=str)
    cols, odd = colourings(edges, cap=1 << 10)
    r = good_colouring(edges, allverts, hm, cols, lam=False)
    assert r is not None, "the negative control failed"
    print(f"    negative control K4(3,3,3,3,3,3) (IN habitat): fully-good "
          f"colouring at admissible index {r[0]}")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('probe', 'law', 'cap', 'flip', 'adv', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.probe, a.law, a.cap, a.flip, a.adv])
    if run or a.probe:
        leg_probe()
    if run or a.law:
        leg_law()
    if run or a.cap:
        leg_cap()
    if run or a.flip:
        leg_flip()
    if run or a.adv:
        leg_adv()
    print("OK")


if __name__ == '__main__':
    main()
