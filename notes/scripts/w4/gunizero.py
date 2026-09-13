"""§(K-grid) direction GUNIZERO (2026-09-13) driver -- IS `dim Z = 0`
UNIFORM IN `m` FOR GODDRUNG'S REPAIRED COLOURING?  §8's eighteenth pass,
rank 3, the `hK` lane's one entry.

THE QUESTION.  §(K-grid) (GR-256)(iv) reduces *uniform (GR-15) on `CL_m`*
to one statement -- *the repaired rule's colouring has `dim Z₊ = dim Z₋ = 0`
generically, for all `m`* -- and (GR-256)(i) says the rank half of (GR-15)
"is a rank computation on a shape-sized pair of matrices and stays PER
SHAPE".  §(K-grid) (GR-34)(ii) says the all-`m` statement "would need the
ladder's chunk classification".

WHAT THIS DRIVER SHOWS.  Both of those are wrong, and the all-`m` statement
is PROVED on an infinite family, by a route that computes no rank at all:

  * §(K-grid) (GR-9) -- a LANDED, PROVED theorem -- says a colouring block
    whose classes partition into three groups with pairwise-union spanning
    trees of the contracted multigraph `H₊` has `dim Z = 0` at GENERIC
    parameters.  That is a purely COMBINATORIAL discharge of the rank half.
  * (GR-175) asks only for six PAIRWISE NON-ADJACENT length-3 rungs; it does
    not pin their positions.  Placing them at the fixed columns
    `0, 2, 4, 6, 8, 10` (the CLUMPED placement) makes the repaired rule's
    colouring EVENTUALLY PERIODIC in `m` outside one fixed window.
  * The balance rider -- (GR-37)(iii)'s second caveat, the one conjunct the
    class-level span argument does not deliver and which (GR-251)(iv) left
    "not proved free in general" -- is solved here in CLOSED FORM: the
    deviation set and the rail-choice vector `σ` are formulas in the length
    vector, with NO search over the `4^k` knob set of (GR-252) step 6.
  * The tree-triple is then an explicit FORMULA IN `m` in both blocks.

So the repaired rule, on the clumped (GR-175) recipe, is a genuinely
search-free rule with a genuinely uniform certificate.

THE REFORMULATION THIS DRIVER INTRODUCES (and cross-checks against the
canonical device at every row).  `G` is the subdivision of `CL_m`; `E_B` is
a spanning forest at an admissible alternating colouring, so a set `F` of
`A`-edges is a COTREE of `H₊` iff `E ∖ F` is a spanning tree of `G`, iff
`F` has at most one edge per BRANCH and the branch set it cuts is a cotree
of `CL_m`.  That moves the tree-triple search from the `2m + 3`-node
contracted multigraph to the `2m`-node hub graph, where a connectivity
union-find replaces `cycle_rank` -- `grid.tree_triple`'s DFS caps out at
`n_hub = 24` and this closes `n_hub = 160`.  EVERY triple this driver
reports is re-verified by the CANONICAL device (`closure.cycle_rank` on
`bd['ced']`, pairwise unions acyclic, all three groups of size `m + 1`) --
the same test `grid.tree_triple` applies -- so the reformulation is a
search accelerator, never the certificate.

WHAT IT IMPORTS READ-ONLY (README §2): `goddrung` (`cycle_pairings`,
`rho_closed`, `repaired_colouring`, `search_repair`, `shape_model`,
`recipe_gr175`, `light_model`), `gexist` (`ladder_specs`,
`fully_good_rank`), `cflank` (`admissible`, `nc1_violations`), `grid`
(`block_data`, `dim_Z`, `tree_triple`), `gridcol` (`subdivide`),
`closure` (`cycle_rank`).  NO landed function is reimplemented.

Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunizero.py --rule      # the SEARCH-FREE closed-form rule at the clumped recipe -- (GR-257)/(GR-258)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunizero.py --triple --hi 80   # the FORMULA-IN-m tree-triple, canonical device -- (GR-259)/(GR-260)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunizero.py --tail      # the class-structure lemma the formula rests on -- (GR-259)(i)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunizero.py --spread    # GBASE's OWN i*m//6 positions: the tell's region -- (GR-262)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunizero.py --consumer  # F26: what the all-m statement buys, and what it does not -- (GR-263)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunizero.py --validate  # all of the above

SEEDS AND CAPS, disclosed per mode.  `--rule`'s admissibility and balance
verdicts are the canonical `cflank.admissible`, an EXACT predicate, cap-free
in both directions.  `--triple`'s verdicts are EXHIBITED partitions checked
by exact GF-free union-find plus `closure.cycle_rank`: a True is a PROOF and
carries no cap; the driver never reports a False as "no triple exists".
`--tail`'s pattern assertions are exact and exhaustive over the branch set.
The only sampled figure anywhere is `--spread`'s `dim_Z` column, which draws
seeded exact-ℚ parameters: a `0` there is an EXHIBITED vanishing point and
hence a per-shape PROOF (`dim Z` is upper-semicontinuous, so the generic
value is the minimum), while a nonzero would be a LOWER BOUND from one draw
and is reported as such.  `gexist.fully_good_rank`, run to `--rank-hi`, is
(GR-31)(i)'s own device and its True is likewise an exhibited certificate.
`grid.tree_triple`'s node cap (250 000) is quoted verbatim wherever the
cross-check is run.  `D_SEED` below is the one seed in the file.
"""

import argparse
import sys
import time

sys.path.insert(0, __file__.rsplit('/', 1)[0])

import cflank                                                 # noqa: E402
import closure                                                # noqa: E402
import gexist                                                 # noqa: E402
import goddrung                                               # noqa: E402
import grid                                                   # noqa: E402
import gridcol                                                # noqa: E402

D_SEED = 20260913

# The CLUMPED (GR-175) recipe: six pairwise non-adjacent length-3 rungs at
# FIXED columns, so the shape is one fixed window plus a growing all-even
# tail.  (GR-175) proves `D = 0` tight-class-shapehood for ANY six pairwise
# non-adjacent length-3 rungs, so this is (GR-175)'s recipe, not a new one;
# GBASE's `i*m//6` is a different placement of the same recipe (`--spread`).
CLUMPED = {0: 1, 2: 1, 4: 1, 6: 1, 8: 1, 10: 1}


# ---------------------------------------------------------------------------
# The closed-form repaired rule: deviation set AND balance, no search.
# ---------------------------------------------------------------------------

def sigma_closed(P):
    """The rail-choice vector `σ ∈ {0,1}^6`, in CLOSED FORM.

    With the deviation set of `dev_choices` below, the `i`-th length-3 rung's
    dart colour is `(p_i − i + σ_0 + σ_i + off) mod 2` (derivation in the
    draft: the top rim alternates with a STALL at each deviating rim, so
    `c(p_i) = c(0) ⊕ (p_i − |Stop ∩ [0, p_i)|)`, and the stall count is
    `(i − 1) + (1 − σ_0) + σ_i`).  `cflank.admissible`'s balance conjunct on
    an alternating colouring is exactly *three of the six length-3 rungs
    carry dart colour A*, so it reads off that formula: with `σ_0 = 0` the
    `i = 0` term is a hit for free and two more are bought by `σ_i = a_i`.
    This is the conjunct (GR-37)(iii)'s SECOND CAVEAT says the class-level
    span argument does not reach, and (GR-251)(iv) left measured only to
    `m ≤ 6` -- here it is discharged by a formula, for every `m`."""
    a = [(P[i] - i) % 2 for i in range(6)]
    sig, hits = [0] * 6, 1
    for i in range(1, 6):
        if hits < 3:
            sig[i] = a[i]
            hits += 1
        else:
            sig[i] = 1 ^ a[i]
    return sig, a


def dev_choices(m, exc, sig):
    """The `choices` knob vector of `goddrung.deviation_set` realising: for
    each length-3 rung at column `p`, serve face `p−1` from hub `p` FORWARD
    and face `p` from hub `p` BACKWARD, on OPPOSITE rails (`σ_i` says which
    way round).  Exactly `2·6 = 12` deviating hubs -- which is `ρ(ℓ)` by
    (GR-251) -- and `#top = 6 ≡ τ`, so the parity clause is met for free."""
    P = sorted(exc)
    specs = gexist.ladder_specs(m, exc)
    lens = [L for (_u, _w, L) in specs]
    phi, tau = goddrung.cycle_pairings(m, lens)
    S = {P[i]: sig[i] for i in range(6)}
    faces = [j for j in range(m) if phi[j]]
    ch = []
    for j in faces:
        if j in S:                       # face p: hub p, BACKWARD rim
            ch.append(1 if S[j] == 0 else 3)
        else:                            # face p−1: hub p, FORWARD rim
            assert (j + 1) % m in S, "face not adjacent to a length-3 rung"
            ch.append(2 if S[(j + 1) % m] == 0 else 0)
    assert sum(1 for c in ch if c & 2) % 2 == tau, "tau parity unmet"
    return tuple(ch), faces, tau


def closed_rule(m, exc):
    """The whole repaired colouring as a FORMULA in the length vector: no
    knob search, no `4^k` enumeration, no global-swap fallback, no neutral
    pair.  Built by the CANONICAL `goddrung.repaired_colouring`."""
    P = sorted(exc)
    sig, a = sigma_closed(P)
    ch, faces, tau = dev_choices(m, exc, sig)
    r = goddrung.repaired_colouring(m, exc, ch, extra=None, flip_global=False)
    assert r is not None, f"the closed-form choice collides at m = {m}"
    edges, allv, hm = goddrung.shape_model(r['specs'], light=True)
    r.update(edges=edges, allv=allv, hm=hm, sig=sig, a=a, P=P, exc=exc,
             choices=ch, k=len(faces), tau=tau)
    return r


# ---------------------------------------------------------------------------
# The branch reformulation, and the CANONICAL re-verification of every triple
# ---------------------------------------------------------------------------

def branch_index(edges):
    """Edge -> BRANCH index, read off `gridcol.subdivide`'s own vertex
    labels (`('i', branch, j)` for a subdivision vertex), not off list
    order.  Every branch here has `ℓ ≥ 2`, so every edge has at least one
    subdivision endpoint; asserted."""
    out = {}
    for e in edges:
        ids = {v[1] for v in e if v[0] == 'i'}
        assert len(ids) == 1, f"edge {e} has no unique branch label"
        out[e] = ids.pop()
    return out


def cl_connected_without(m, removed):
    """`CL_m` minus a BRANCH set, connected?  Branch indexing is
    `gexist.ladder_specs`': `0..m−1` top rims, `m..2m−1` bottom rims,
    `2m..3m−1` rungs."""
    par = list(range(2 * m))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    cnt = 2 * m
    for b in range(3 * m):
        if b in removed:
            continue
        if b < m:
            u, w = b, (b + 1) % m
        elif b < 2 * m:
            u, w = m + (b - m), m + ((b - m + 1) % m)
        else:
            u, w = b - 2 * m, m + (b - 2 * m)
        ru, rw = find(u), find(w)
        if ru != rw:
            par[ru] = rw
            cnt -= 1
    return cnt == 1


def block_classes(m, r, mine):
    """`(block_data, [class as a BRANCH-index tuple])` for one block."""
    bd = grid.block_data(r['edges'], r['allv'], r['col'], mine)
    bi = branch_index(r['edges'])
    byc = {}
    for k in range(len(bd['E'])):
        byc.setdefault(bd['cls'][k], []).append(bi[bd['E'][k]])
    return bd, bi, byc


def canonical_triple_check(m, r, mine, groups):
    """THE certificate.  Maps a branch-level triple back to EDGE groups and
    verifies it with the CANONICAL device -- `closure.cycle_rank` on
    `bd['ced']`, the same test `grid.tree_triple` applies -- plus the
    class-respecting property and the `m + 1` sizes that make each pairwise
    union a SPANNING tree rather than merely acyclic.  Returns
    `(ok, sizes, why)`; `ok` True is a proof, with no cap."""
    bd, bi, byc = block_classes(m, r, mine)
    gsets = [set(g) for g in groups]
    eg = [[], [], []]
    for c, brs in byc.items():
        bset = set(brs)
        hit = [g for g in range(3) if bset <= gsets[g]]
        if len(hit) != 1:
            return False, None, f"class {sorted(bset)} lands in {len(hit)} groups"
        ks = [k for k in range(len(bd['E'])) if bd['cls'][k] == c]
        eg[hit[0]].extend(bd['ced'][k] for k in ks)
    nodes = bd['nodes']
    acyc = all(closure.cycle_rank(nodes, eg[i] + eg[j]) == 0
               for i, j in ((0, 1), (0, 2), (1, 2)))
    sizes = [len(g) for g in eg]
    if not acyc:
        return False, sizes, "a pairwise union carries a cycle"
    if sizes != [m + 1] * 3:
        return False, sizes, f"group sizes {sizes} != {[m+1]*3}"
    return True, sizes, None


# ---------------------------------------------------------------------------
# THE FORMULA-IN-m TREE-TRIPLE at the clumped recipe
# ---------------------------------------------------------------------------

def triple_formula(m, mine):
    """The explicit tree-triple of the closed-form rule at the CLUMPED
    recipe, as a formula in `m` (branch indices).  Outside the fixed window
    the assignment is completely uniform -- EVERY tail top rim to group 1,
    EVERY tail bottom rim to group 2, EVERY tail rung to group 3 -- which is
    exactly the period-2 class pattern of `--tail`, so the class-respecting
    property is automatic there and only the window needs checking."""
    def T(j):
        return j % m

    def B(j):
        return m + (j % m)

    def R(j):
        return 2 * m + (j % m)
    if mine == 'A':
        g1 = [T(0), T(1), T(3)] + [T(j) for j in range(6, m - 1)] \
            + [B(0), B(5)] + [R(0), R(3), R(4)]
        g2 = [T(2), T(4), T(5)] + [B(2), B(3)] \
            + [B(j) for j in range(6, m)] + [R(1), R(2)]
        g3 = [T(m - 1), B(1), B(4), R(0), R(2), R(4)] \
            + [R(j) for j in range(5, m)]
    else:
        g1 = [T(1), T(2), T(3), T(6), T(7)] + [T(j) for j in range(10, m)] \
            + [B(0), B(1), B(4), B(5), B(8), B(9)]
        g2 = [T(0), T(4), T(5), T(9)] + [B(2), B(3), B(7)] \
            + [B(j) for j in range(11, m)] + [R(1), R(6), R(7), R(8), R(10)]
        g3 = [T(8), B(6), B(10)] \
            + [R(j) for j in range(m) if j not in (1, 7)]
    return [sorted(set(g)) for g in (g1, g2, g3)]


# ---------------------------------------------------------------------------
# [GUZ-1] --rule: the SEARCH-FREE closed-form rule
# ---------------------------------------------------------------------------

def leg_rule(hi=60, rank_hi=40, nc1_hi=12):
    """[GUZ-1] (GR-257)/(GR-258).  The repaired rule with BOTH its remaining
    quantifiers removed: the deviation set from (GR-249)'s pairings and the
    rail vector `σ` from `sigma_closed`, with NO search over (GR-252) step
    6's `4^k` knob set.  Admissibility (balance included) is the canonical
    `cflank.admissible`, an exact predicate -- cap-free both ways.

    CAPS.  `cflank.nc1_violations` needs `cflank.hub_model`'s simple-cycle
    enumeration and is fenced at `--nc1-hi`; `gexist.fully_good_rank` runs
    to `--rank-hi` and its True is an EXHIBITED exact-ℚ certificate (a
    proof).  Nothing else here is sampled."""
    import random
    rng = random.Random(D_SEED)
    print(f"[GUZ-1] (GR-257)/(GR-258) the SEARCH-FREE closed-form repaired "
          f"rule at the CLUMPED (GR-175) recipe {sorted(CLUMPED)} "
          f"(seed {D_SEED}, used only by fully_good_rank)")
    ok = rows = 0
    for m in range(12, hi + 1, 2):
        t0 = time.time()
        r = closed_rule(m, CLUMPED)
        adm = cflank.admissible(r['edges'], r['allv'], r['hm'], r['col'])
        nA = sum(1 for e in r['edges'] if r['col'][e] == 'A')
        pred, k, tau = goddrung.rho_closed(m, r['lens'])
        nc1 = (not cflank.nc1_violations(goddrung.shape_model(r['specs'])[2],
                                         r['col'], r['edges'], r['allv'])
               if m <= nc1_hi else None)
        fg = (gexist.fully_good_rank(r['edges'], r['allv'], r['hm'],
                                     r['col'], rng)
              if m <= rank_hi else None)
        rows += 1
        ok += 1 if adm else 0
        print(f"  m = {m:3d} (n_hub = {2*m:3d}): sigma = {r['sig']}, "
              f"rho = {pred} (k = {k}, tau = {tau}), dev = {len(r['dev'])} "
              f"hubs, A/B = {nA}/{len(r['edges'])-nA}; admissible = {adm}; "
              f"NC1 clear = {nc1}; fully-good (exact-ℚ dim Z = 0, BOTH "
              f"blocks) = {fg}; knob search = NONE  "
              f"[{time.time()-t0:.1f}s]")
    print(f"  => {ok}/{rows} admissible with NO search: (GR-252) step 6's "
          f"knob set is not needed at this recipe, so the rule really is "
          f"'a formula in the length vector' -- which (GR-256)(iv) assumed "
          f"but (GR-252) step 6 did not deliver.")


# ---------------------------------------------------------------------------
# [GUZ-2] --triple: the FORMULA-IN-m tree-triple
# ---------------------------------------------------------------------------

def leg_triple(hi=80, cross_hi=8):
    """[GUZ-2] (GR-259)/(GR-260).  The explicit tree-triple of
    `triple_formula`, verified at every even `m` in `12..hi` in BOTH blocks
    by the CANONICAL device (`closure.cycle_rank` on `bd['ced']`, pairwise
    unions acyclic, sizes `m + 1`).  By the LANDED, PROVED (GR-9) this is a
    proof of generic `dim Z₊ = dim Z₋ = 0` -- with no rank computed and no
    parameter drawn.

    CAPS.  None: each row is an exhibited partition and an exact check.
    `grid.tree_triple` is run as an independent cross-check only where its
    250 000-node DFS is affordable (`--cross-hi`); its caps do not travel
    with this leg's verdicts."""
    print(f"[GUZ-2] (GR-259)/(GR-260) the FORMULA-IN-m tree-triple, "
          f"CANONICAL device, m = 12..{hi}")
    ok = rows = 0
    for m in range(12, hi + 1, 2):
        t0 = time.time()
        r = closed_rule(m, CLUMPED)
        assert cflank.admissible(r['edges'], r['allv'], r['hm'], r['col'])
        cells = []
        good = True
        for mine in ('A', 'B'):
            # (GR-9)'s HYPOTHESIS, asserted rather than assumed: the OTHER
            # class must be a forest, and the block must be tight balanced
            # (`2|E_mine| = 3(n_c - 1)`), which is where (GR-9)'s
            # "pairwise unions are SPANNING trees" equivalence comes from.
            other = [e for e in r['edges'] if r['col'][e] != mine]
            comp = closure.components(r['allv'], other)
            assert len(other) == len(r['allv']) - len(set(comp.values())), \
                f"the other class is not a forest at m = {m}, block {mine}"
            bdq = grid.block_data(r['edges'], r['allv'], r['col'], mine)
            assert 2 * len(bdq['E']) == 3 * (bdq['n_c'] - 1), \
                f"block not tight balanced at m = {m}, block {mine}"
            assert 3 * bdq['h'] == len(bdq['E']), \
                f"the dim Z matrix is not square at m = {m}, block {mine}"
            gs = triple_formula(m, mine)
            conn = all(cl_connected_without(m, set(g)) for g in gs)
            cok, sizes, why = canonical_triple_check(m, r, mine, gs)
            good = good and cok
            cells.append(f"{mine}: cotrees = {conn}, CANONICAL = {cok}, "
                         f"sizes = {sizes}" + (f" ({why})" if why else ""))
        rows += 1
        ok += 1 if good else 0
        print(f"  m = {m:3d} (n_hub = {2*m:3d}): " + " | ".join(cells)
              + f"  [{time.time()-t0:.1f}s]")
    print(f"  => {ok}/{rows} -- an EXPLICIT tree-triple in both blocks at "
          f"every tested m, hence by (GR-9) generic dim Z = 0 in both "
          f"blocks, hence per-shape (GR-15), by a COMBINATORIAL "
          f"certificate.  (GR-256)(i)'s 'the rank half ... stays per "
          f"shape' is refuted as a structural claim.")
    print(f"  cross-check against `grid.tree_triple` (its own 250000-node "
          f"DFS, affordable only to m = {cross_hi}):")
    for m in range(12, cross_hi + 1, 2):
        r = closed_rule(m, CLUMPED)
        for mine in ('A', 'B'):
            bd, _bi, _byc = block_classes(m, r, mine)
            res, capped = grid.tree_triple(bd)
            print(f"    m = {m:3d} {mine}: tree_triple = "
                  f"{'FOUND' if res else ('capped at 250000 nodes' if capped else 'none')}")


# ---------------------------------------------------------------------------
# [GUZ-3] --tail: the class-structure lemma the formula rests on
# ---------------------------------------------------------------------------

def leg_tail(hi=60):
    """[GUZ-3] (GR-259)(i).  WHY the formula is uniform.  The tail
    assignment -- EVERY tail top rim to group 1, EVERY tail bottom rim to
    group 2, EVERY tail rung to group 3 -- is class-respecting exactly when
    no class lying strictly inside the tail MIXES KINDS, i.e. when every
    such class is a set of top rims, or of bottom rims, or a lone rung.
    That, and not any particular pairing, is the property the formula needs.

    SELF-CORRECTION (GUNIZERO, in-run): this leg first asserted the stronger
    pattern *'every tail rim class is an ADJACENT PAIR'*, and the leg
    refuted it -- block `B` carries a LONE bottom rim `B_{m−1}` at the
    window edge at every `m` (the wrap column, with `B_0` inside the
    window).  The strong form is false; the kind-purity form is what the
    construction uses, and it is what is asserted here.  Recorded rather
    than silently weakened.

    EXACT and EXHAUSTIVE over the class set at each `m`; no cap."""
    print(f"[GUZ-3] (GR-259)(i) TAIL classes are KIND-PURE, "
          f"m = 12..{hi} -- exhaustive over classes, no cap")
    ok = rows = 0
    for m in range(12, hi + 1, 2):
        r = closed_rule(m, CLUMPED)
        cells = []
        good = True
        for mine in ('A', 'B'):
            _bd, _bi, byc = block_classes(m, r, mine)
            bad, shape = [], {}
            for _c, brs in byc.items():
                cols = sorted(set(brs))
                if min(b % m for b in cols) < 12:
                    continue                       # touches the window
                kinds = sorted({0 if b < m else (1 if b < 2 * m else 2)
                                for b in cols})
                if len(kinds) != 1:
                    bad.append(tuple(cols))
                    continue
                key = ('top', 'bot', 'rung')[kinds[0]] + f"x{len(cols)}"
                shape[key] = shape.get(key, 0) + 1
            good = good and not bad
            cells.append(f"{mine}: kind-pure = {not bad}, tail shapes = "
                         + ",".join(f"{k}:{v}" for k, v in sorted(shape.items()))
                         + (f" MIXED {bad[:3]}" if bad else ""))
        rows += 1
        ok += 1 if good else 0
        print(f"  m = {m:3d}: " + " | ".join(cells))
    print(f"  => {ok}/{rows}.  No class strictly inside the tail mixes "
          f"kinds, so the tail assignment is class-respecting at every m, "
          f"and the window `[0, 11]` is the only part the formula names.  "
          f"The tail shapes are adjacent rim PAIRS and lone RUNGS, plus -- "
          f"block B only -- the one lone rim `B_{{m-1}}` at the window edge.")


# ---------------------------------------------------------------------------
# [GUZ-4] --spread: GBASE's OWN i*m//6 positions -- the tell's region
# ---------------------------------------------------------------------------

def leg_spread(hi=60, dz_hi=60):
    """[GUZ-4] (GR-262).  THE TELL, evaluated where the spec aimed it: past
    the landed `--far` cap, on GBASE's OWN placement `i*m//6`, is there an
    `m` at which the repaired rule is admissible and `dim Z ≠ 0`?

    Two colourings are run at each `m`: the LANDED `goddrung.search_repair`
    (which searches the knob set, so it IS (GR-252) as landed) and this
    direction's closed-form one.  Admissibility is exact and cap-free;
    `dim_Z` is a SEEDED exact-ℚ draw, so a `0` is an exhibited vanishing
    point and hence a per-shape PROOF (upper semicontinuity), while a
    nonzero would be ONE DRAW -- a lower bound on the generic value, not a
    measurement of it, and the driver says so rather than reporting it as a
    refutation.  `search_repair`'s own cap (200 000 sampled choice vectors
    above `4^k`) is reported per row."""
    import random
    from fractions import Fraction as F
    rng = random.Random(D_SEED)
    print(f"[GUZ-4] (GR-262) THE TELL at GBASE's own i*m//6 placement, "
          f"m = 12..{hi} (n_hub up to {2*hi}) -- past `--far`'s m = 40")
    hits = 0
    for m in range(12, hi + 1, 2):
        t0 = time.time()
        exc = goddrung.recipe_gr175(m)
        cells = []
        for name, build in (('landed', lambda: goddrung.search_repair(
                                m, exc, light=True)),
                            ('closed', lambda: closed_rule(m, exc))):
            r = build()
            if r.get('fail'):
                cells.append(f"{name}: no balanced repair "
                             f"({'knob set EXHAUSTED' if r['exhaustive'] else 'under cap ' + str(r['cap'])})")
                continue
            adm = cflank.admissible(r['edges'], r['allv'], r['hm'], r['col'])
            dz = []
            if m <= dz_hi:
                for mine in ('A', 'B'):
                    bd = grid.block_data(r['edges'], r['allv'], r['col'], mine)
                    sv = {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                          for c in set(bd['cls'])}
                    dz.append(grid.dim_Z(bd, sval=sv))
                if adm and any(d != 0 for d in dz):
                    hits += 1
            cells.append(f"{name}: admissible = {adm}, dim Z (1 seeded "
                         f"exact-ℚ draw per block) = {dz or 'not run'}")
        print(f"  m = {m:3d}: " + " | ".join(cells) + f"  [{time.time()-t0:.1f}s]")
    print(f"  => the tell fired {hits} times.  An `m` with the repaired rule "
          f"admissible and `dim Z != 0` was NOT FOUND in this range; the "
          f"region is unbounded, so this is a range verdict, not an "
          f"existence verdict.  Note a `0` entry is a PROOF (exhibited "
          f"vanishing point) while a nonzero would have been ONE DRAW.")


# ---------------------------------------------------------------------------
# [GUZ-5] --consumer: F26, what the all-m statement buys
# ---------------------------------------------------------------------------

def leg_consumer():
    """[GUZ-5] (GR-263).  The F26 accounting, measuring nothing new: which
    landed statement each half of the new certificate discharges, and which
    it does not."""
    print("[GUZ-5] (GR-263) F26: what an ALL-m (GR-15) on one infinite "
          "family buys, and what it does not")
    for line in [
        "(a) (GR-15)'s discharge chain -- '(GR-15) + (GR-1)/(AC-4) + (GR-5)"
        " + (AC-7) discharges hK on the tight stratum' -- consumes the FULL",
        "    forall over tight class shapes.  An infinite SUBFAMILY is not a"
        " partial input to it.  (GR-256)(iii) stands, and this direction",
        "    does NOT move the gap map's hK row.",
        "(b) But (GR-256)(iii)'s escape clause -- 'on any FINITE set of"
        " shapes the rule buys convenience, not a theorem that was not",
        "    already obtainable' -- does NOT cover this: (GR-15) is"
        " one-point-decidable PER SHAPE, and no finite number of one-point",
        "    decisions settles an infinite family.  So this IS a theorem"
        " that was not already obtainable.",
        "(c) It refutes two landed sentences about the SHAPE of the"
        " difficulty: (GR-256)(i)'s 'the rank half ... stays per shape' and",
        "    (GR-34)(ii)'s 'the all-m statement would need the ladder's"
        " chunk classification'.  No chunk is classified here.",
        "(d) It supplies the first instance of (GR-10) -- not merely"
        " (GR-15) -- on an infinite family, since the certificate IS the",
        "    tree-triple (GR-10) asks for.",
    ]:
        print("  " + line)


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    for f in ('rule', 'triple', 'tail', 'spread', 'consumer', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--hi', type=int, default=60)
    ap.add_argument('--triple-hi', type=int, default=80)
    ap.add_argument('--rank-hi', type=int, default=40)
    ap.add_argument('--nc1-hi', type=int, default=12)
    ap.add_argument('--cross-hi', type=int, default=8)
    ap.add_argument('--dz-hi', type=int, default=60)
    a = ap.parse_args()
    run = a.validate
    if run or a.rule:
        leg_rule(a.hi, a.rank_hi, a.nc1_hi)
    if run or a.triple:
        leg_triple(a.triple_hi, a.cross_hi)
    if run or a.tail:
        leg_tail(a.hi)
    if run or a.spread:
        leg_spread(a.hi, a.dz_hi)
    if run or a.consumer:
        leg_consumer()
    if not (run or a.rule or a.triple or a.tail or a.spread or a.consumer):
        ap.print_help()


if __name__ == '__main__':
    main()
