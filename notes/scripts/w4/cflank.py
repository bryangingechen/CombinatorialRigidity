"""§(K-grid) direction CFLANK (2026-08-07) driver -- the TARGETED ADVERSARIAL
FLANK against (GR-15): a tight class shape whose EVERY admissible colouring
leaves generic `dim Z > 0` in a block, or the obstruction to there being one.

A `w4/` leaf beside `gridcol.py`, importing `gridcol.py` / `packmm.py` /
`grid.py` / `gridwit.py` / `closure.py` READ-ONLY (README §2; same precedent
as packmm -> gridwit -> grid -> closure).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --law    # (GR-21) the excess law, (GR-22) the caps, (GR-25) the cut criterion
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --adv    # (GR-23) the flip injection, and the F13 witness the detector MUST reject
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --cubic  # THE FLANK HUNT, Lambda = empty: exhaustive over profiles AND over bits
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam    # the same hunt with Lambda != empty, n_hub <= 4 (all length tuples)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam6   # ... and n_hub = 6 at |Lambda| <= 1  (OVER the 600 s ceiling, ~1340 s: F15)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --dens   # the kill density, and (GR-23)'s bound asserted per binding circuit
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --tight  # the named large targets, up to 18 hubs / 51 vertices
    PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --validate  # all but --lam6

Argument state: session draft `fanout-CFLANK.md` (to be merged into
`notes/Pencil-informal.md` §(K-grid) as Steps G24+; labels (GR-21)+ per the
2026-08-07 CFLANK reservation in `notes/Pencil-labels.md`).

WHY THIS POOL, in one paragraph.  TCOL's *What would change this* item (v)
named two places to look for a flank: shapes whose `G°` is rich in `(2,2,3)`
and `(2,2,2,2)` circuits with conflicting `h_≠ ≥ 2` requirements, and hub
multigraphs with many parallel branch pairs.  (GR-21) below turns "rich in
binding circuits" into an exact budget: a tight class shape satisfies
`Σ_β (ℓ_β − 2) = 2·Σ_v (deg(v) − 3) + 6`, so EVERY unit of hub degree above
cubic costs two units of branch length above 2, and a binding circuit needs
`Σ_γ (ℓ_β − 2) ≤ 4 − r ≤ 1`.  The binding-circuit-rich stratum is therefore
exactly `D := Σ_v(deg(v) − 3) = 0`, i.e. the CUBIC hub multigraphs, which
carry a total length excess of exactly 6 -- a stratum the census reaches at
only 885 of 907 shapes (all at n_hub ∈ {2,4}) and `gridcol --wide` never
sweeps at all (its WIDE_PLAN has no (6,9) entry).  `--cubic` sweeps it
EXHAUSTIVELY: every hub multigraph up to isomorphism, every length profile
(enumerated, never sampled), every one of the `2^M` branch-bit patterns.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--law    (GR-21)/(GR-22)/(GR-25): the excess law is asserted at all 907
         census shapes and at every constructed pool shape, together with the
         caps it implies -- the length-2 sub-multigraph `H` is simple, no two
         hubs have three common `H`-neighbours, two binding triangles share
         at most a LENGTH-1 branch, and the `(2,2,2,2)` circuits are exactly
         the 4-cycles of `H`, counted -- and the (GR-25) cut criterion is
         asserted equivalent to `gridcol.class_shape` over every (multigraph,
         excess profile) of the stratum.

--adv    (GR-23): the flip injection (flipping an independent set of a
         binding circuit's branches carries an NC1-violating admissible
         colouring to an NC1-passing one) is asserted colouring by
         colouring; and the F13 adversarial witness -- the CONSTRUCTED
         all-length-2 `K4`, whose 24 admissible colourings ALL violate NC1 --
         is asserted to be reported as a miss by the same detector `--cubic`
         runs, with the named habitat conjunct it fails and an in-habitat
         negative control that the detector passes.

--cubic  THE FLANK HUNT at `Λ = ∅`: over the whole `D = 0` stratum at
         n_hub ∈ {2,4,6}, every length profile and every branch-bit pattern,
         no shape has ALL its admissible colourings NC1-violating, every
         shape satisfies (GR-23) or (GR-24) so that NC1-satisfiability is
         PROVEN there, and every shape carries an admissible colouring at
         generic `dim Z₊ = dim Z₋ = 0` -- exhibited by an exact-ℚ parameter
         point, which by (GR-7) remark (i) is a per-shape PROOF of the
         generic statement, i.e. of (GR-15) at that shape.

--lam    the same hunt with `Λ ≠ ∅`, where (GR-17)(d)'s binding list is only
--lam6   MEASURED, an off-circuit merge can push `D_A` below the run count
         (so the classes are read off `grid.block_data`, never off the run
         count), and a binding circuit can carry NO even branch -- so
         (GR-23)/(GR-24)'s balance-preserving flip does not exist and only
         the exhaustive scan carries the shape.

--tight  the named large targets -- the cube, the Wagner graph, the circular
         ladders CL5..CL8 and the truncations of `K4` and the prism -- which
         are the shapes the (GR-21)/(GR-22) analysis singles out as the only
         ways to defeat (GR-23) or (GR-24), and at which the (GR-24) repair
         is run constructively and its output rank-certified.

--dens   the quantitative obstruction: per binding circuit, the fraction of
         admissible colourings it kills, measured over the exhaustive pool
         and compared with the proven `≤ 1/4` of (GR-23) -- the number that
         says how many binding circuits a flank would need, against the
         (GR-22) cap on how many the habitat allows.

Exact throughout (integers and `fractions.Fraction`; no floats).  Rank comes
from `exactcore.rank` through `gridcol.dim_W_branch` / `grid.dim_Z`, and from
`kbare_common.rank_modp` as a CERTIFIED LOWER BOUND inside
`gridcol.block_generic_zero`, whose attaining draw is re-checked in exact ℚ
here at every reported hit (README §4 convention 2).  The rngs are seeded per
mode and the seeds printed; no `set` is printed.  Nothing here samples a
placement: every object is a colouring of a pinned finite graph, so no figure
is a rate over sampled placements and `repin.star_generic` gates nothing
below (§(K-clos) (AC-9)'s discipline, as for `gridcol.py` / `gridwit.py`).
"""
import argparse
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                     # noqa: E402
from closure import (alternation_classes, colourings,                 # noqa: E402
                     cycle_rank)
from grid import block_data, census_shapes, dim_Z                     # noqa: E402
from packmm import simple_cycles                                      # noqa: E402
from gridcol import (block_generic_zero, branch_decomp, class_shape,  # noqa: E402
                     cycle_walk, dim_W_branch, filter_pass,
                     multigraphs, subdivide)

C_SEED = 20260807
CUBIC_N = (2, 4, 6)


# ----------------------------------------------------- local devices --------

def excess_profiles(M, excess, maxexc=3):
    """Every distribution of `excess` units of branch length above 2 over M
    branches, per branch at most `maxexc` (so `ℓ ≤ 5`, (SD-6)).

    Local device (README rule 3, different name and different semantics from
    `gridcol.length_profiles`): that one enumerates LENGTH tuples summing to a
    target and falls back to seeded rejection sampling above a cap, which is
    the right tool for a wide sweep and the wrong one here -- (GR-21) pins the
    total excess at `2D + 6`, so the solution set is small enough to
    ENUMERATE, and an exhaustive claim is the whole point of this pass.
    Returns tuples of per-branch excesses, so `ℓ_β = 2 + e_β`."""
    out = []

    def rec(i, rem, acc):
        if rem == 0:
            out.append(tuple(acc) + (0,) * (M - i))
            return
        if i == M:
            return
        for e in range(min(maxexc, rem), -1, -1):
            acc.append(e)
            rec(i + 1, rem - e, acc)
            acc.pop()
    rec(0, excess, [])
    return out


def hub_model(edges):
    """The hub-level model of a class shape: (hubs, branches, ends, lens,
    circuits, binding walks).  `binding` are the circuits with
    `Σ_γ(ℓ_β − 1) ≤ 4`, i.e. exactly the ones (GR-17)(c) can obstruct.

    Local device: assembles `gridcol.branch_decomp` + `packmm.simple_cycles` +
    `gridcol.cycle_walk` into the one object every mode below consumes; no
    §1 primitive computes it."""
    hubs, branches = branch_decomp(edges)
    if branches is None:
        return None
    ends = [(u, w) for (u, w, _) in branches]
    lens = [len(p) for (_, _, p) in branches]
    idx = {v: i for i, v in enumerate(hubs)}
    cycs = simple_cycles(list(range(len(hubs))),
                         [(idx[u], idx[w]) for u, w in ends])
    binding = []
    for cyc in cycs:
        if sum(lens[k] for k in cyc) - len(cyc) <= 4:
            walk = cycle_walk(branches, ends, cyc)
            binding.append((tuple(sorted(cyc)), walk))
    return dict(hubs=hubs, branches=branches, ends=ends, lens=lens,
                cycs=cycs, binding=binding)


def h_neq(hm, col, walk):
    """`h_≠(γ)`: the hubs of the circuit walk at which the two cycle edges
    carry different colours.  Reads the colouring on the SUBDIVISION, so it
    needs no bit model and cannot drift from `closure.colourings`."""
    branches, ends = hm['branches'], hm['ends']
    r = len(walk)
    out = 0
    for i in range(r):
        (k, _u, w) = walk[i]
        (k2, u2, _w2) = walk[(i + 1) % r]
        e1 = next(e for e in branches[k][2] if w in e)
        e2 = next(e for e in branches[k2][2] if u2 in e)
        if col[e1] != col[e2]:
            out += 1
    return out


def nc1_violations(hm, col, edges=None, allverts=None):
    """The binding circuits at which (GR-17)(c)'s `D_A, D_B ≥ 3` fails.  Each
    one is a PROOF -- via (GR-8) at `P = γ` plus (GR-16)(iv) at balance --
    that generic `dim Z > 0` in the offending block.

    When `Λ = ∅` this is the run count `((L − r) + h_≠)/2`, exactly by
    (GR-17)(b).  When `Λ ≠ ∅` an off-circuit `Γ`-path can MERGE two runs into
    one class, so the run count is only an upper bound for `D`; there the
    classes are read off `grid.block_data` directly, which is exact in every
    case.  (GR-17)(d)'s two-profile list is proven only in the first regime,
    which is why the second is never taken on trust here."""
    lam = any(L == 1 for L in hm['lens'])
    bad = []
    if not lam:
        for (cyc, walk) in hm['binding']:
            L = sum(hm['lens'][k] for (k, _, _) in walk)
            if (L - len(walk)) + h_neq(hm, col, walk) < 6:
                bad.append(cyc)
        return bad
    bdA = block_data(edges, allverts, col, 'A')
    bdB = block_data(edges, allverts, col, 'B')
    clsA = {e: c for e, c in zip(bdA['E'], bdA['cls'])}
    clsB = {e: c for e, c in zip(bdB['E'], bdB['cls'])}
    for (cyc, walk) in hm['binding']:
        eseq = [e for (k, _, _) in walk for e in hm['branches'][k][2]]
        dA = len({clsA[e] for e in eseq if col[e] == 'A'})
        dB = len({clsB[e] for e in eseq if col[e] == 'B'})
        if min(dA, dB) < 3:
            bad.append(cyc)
    return bad


def admissible(edges, allverts, hm, col):
    """Admissible = alternating (guaranteed by `closure.colourings`) + both
    ruling classes forests + balanced + no monochromatic hub.  This is
    `gridcol.filter_pass` minus its `build_fixed_config` conjunct, which is a
    property of the CONSTRUCTED grid point and not of the colouring; the
    detector below applies `filter_pass` itself before measuring rank."""
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    if len(EA) != len(EB):
        return False
    if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
        return False
    for v in hm['hubs']:
        if len({col[e] for e in edges if v in e}) == 1:
            return False
    return True


def cubic_habitat(n, hedges, lens):
    """(GR-25) the CUT CRITERION for habitat membership at `D = 0`.

    At a cubic hub multigraph a branch-closed set with hub set `W'` and
    induced branch set `F` has `f = Σ_F(6 − ℓ) − 6(|W'| − 1)`, and
    `|F| = (3|W'| − ∂(W'))/2`, so `f = 6 − 2∂(W') − exc(E(W'))` with
    `exc = Σ(ℓ − 2)`.  Hence, given the excess law (GR-21), the shape is
    tight with `def = 0` and `hnoRigid` iff every proper `W'` with
    `|W'| ≥ 2` inducing a connected subgraph has

        2·∂(W') + exc(E(W')) ≥ 7,

    and girth 7 iff every circuit has `Σ_γ ℓ ≥ 7`; `hcard` and the two-hub
    triangle ban are then automatic because `Λ = ∅` leaves no hub-hub edge.
    Local device: `gridcol.class_shape` is the canonical certificate and stays
    the oracle -- but it runs `kslide.no_rigid_branch_union`, a `2^M` scan
    with a matroid rank inside, which is out of reach past `M ≈ 12`, while
    this is a `2^n` scan of O(M) work.  `--law` asserts the two AGREE on the
    entire `n_hub ≤ 6` pool before any target relies on this one."""
    exc = [L - 2 for L in lens]
    if any(L < 1 or L > 5 for L in lens):
        return False
    if sum(exc) != 6:
        return False
    idx = {}
    adj = {v: [] for v in range(n)}
    for k, (u, w) in enumerate(hedges):
        if u == w:
            return False
        adj[u].append((w, k))
        adj[w].append((u, k))
        idx.setdefault((min(u, w), max(u, w)), []).append(k)
    if any(len(a) != 3 for a in adj.values()):
        return False
    # `hcard` (R4) and the two-hub triangle ban -- automatic when `Λ = ∅`,
    # NOT automatic once hub-hub edges appear
    lamdeg = {v: 0 for v in range(n)}
    for k, (u, w) in enumerate(hedges):
        if lens[k] == 1:
            lamdeg[u] += 1
            lamdeg[w] += 1
    if any(d > 2 for d in lamdeg.values()):
        return False
    for (a, b) in [(i, j) for i in range(n) for j in range(i + 1, n)]:
        par = [k for k, (u, w) in enumerate(hedges)
               if {u, w} == {a, b}]
        if len(par) >= 2 and any(lens[k] == 1 for k in par) \
                and any(lens[k] == 2 for k in par):
            return False                   # a two-hub triangle (1 + 2 = C3)
    for mask in range(1, (1 << n) - 1):
        W = [v for v in range(n) if mask >> v & 1]
        if len(W) < 2:
            continue
        inside = [k for k, (u, w) in enumerate(hedges)
                  if (mask >> u & 1) and (mask >> w & 1)]
        if not inside:
            continue
        seen, st = {W[0]}, [W[0]]
        while st:
            v = st.pop()
            for (u, k) in adj[v]:
                if k in inside and u not in seen:
                    seen.add(u)
                    st.append(u)
        if len(seen) != len(W):
            continue                       # disconnected: its components are
                                           # themselves enumerated
        bd = 3 * len(W) - 2 * len(inside)
        if 2 * bd + sum(exc[k] for k in inside) < 7:
            return False
    return True


def private_even(hm):
    """(GR-24)'s hypothesis: a map sending each binding circuit to an EVEN
    branch of it that lies in no OTHER binding circuit, or None.

    Flipping such a branch repairs its own circuit and disturbs no other, so
    when it exists the violated circuits can all be repaired at once and NC1
    is satisfiable outright -- no union bound, no bound on how many binding
    circuits there are."""
    lens = hm['lens']
    inc = {}
    for (cyc, _w) in hm['binding']:
        for k in cyc:
            inc.setdefault(k, []).append(cyc)
    out = {}
    for (cyc, _w) in hm['binding']:
        pick = [k for k in cyc if lens[k] % 2 == 0 and len(inc[k]) == 1]
        if not pick:
            return None
        out[cyc] = pick[0]
    return out


def repair(edges, allverts, hm, col, priv):
    """Turn an admissible colouring into an NC1-passing one by (GR-24): flip
    the private even branch of every violated binding circuit, all at once."""
    bad = nc1_violations(hm, col, edges, allverts)
    out = col
    for cyc in bad:
        out = flip_branch(edges, out, hm['branches'][priv[cyc]][2])
    return out


def sub_multigraph_2(hm):
    """`H`: the sub-multigraph of the hub multigraph carried by the LENGTH-2
    branches -- the object every binding circuit lives in."""
    return [k for k in range(len(hm['lens'])) if hm['lens'][k] == 2]


# ------------------------------------------------- [CFL-1] --law: (GR-21) ---

def law_checks(label, hm, strict=True):
    """(GR-21) and the five (GR-22) caps, asserted at one shape."""
    hubs, ends, lens = hm['hubs'], hm['ends'], hm['lens']
    n, M = len(hubs), len(ends)
    deg = {h: 0 for h in hubs}
    for (u, w) in ends:
        deg[u] += 1
        deg[w] += 1
    D = sum(d - 3 for d in deg.values())
    assert min(deg.values()) >= 3, f"{label}: a hub of degree < 3"
    # (GR-21) the excess law
    assert sum(L - 2 for L in lens) == 2 * D + 6, \
        f"{label}: excess law fails ({sum(L - 2 for L in lens)} != {2 * D + 6})"
    E2 = sub_multigraph_2(hm)
    # (GR-22)(i) H is simple
    seen = set()
    for k in E2:
        key = tuple(sorted(ends[k], key=str))
        assert key not in seen, f"{label}: two parallel length-2 branches"
        seen.add(key)
    # (GR-22)(ii) no two hubs with three common H-neighbours
    nb2 = {h: set() for h in hubs}
    for k in E2:
        u, w = ends[k]
        nb2[u].add(w)
        nb2[w].add(u)
    q2 = 0
    for i, u in enumerate(hubs):
        for w in hubs[i + 1:]:
            j = len(nb2[u] & nb2[w])
            assert j <= 2, f"{label}: hubs with 3 common H-neighbours"
            q2 += j * (j - 1) // 2
    # (GR-22)(iii) two binding triangles share at most a LENGTH-1 branch
    tri = [cyc for (cyc, w) in hm['binding'] if len(cyc) == 3]
    quad = [cyc for (cyc, w) in hm['binding'] if len(cyc) == 4]
    for a in range(len(tri)):
        for b in range(a + 1, len(tri)):
            for k in set(tri[a]) & set(tri[b]):
                assert lens[k] == 1, \
                    f"{label}: binding triangles share a length-{lens[k]} branch"
    # (GR-22)(iv) the all-length-2 4-circuits ARE the 4-cycles of H, counted
    q4 = [cyc for cyc in quad if all(lens[k] == 2 for k in cyc)]
    assert len(q4) == q2 // 2, \
        f"{label}: #(2,2,2,2)-circuits {len(q4)} != q2/2 {q2 // 2}"
    nlam = sum(1 for L in lens if L == 1)
    # (GR-22)(v) at Lambda = empty the binding list is (2,2,3) + (2,2,2,2)
    if nlam == 0:
        assert len(quad) == len(q4), f"{label}: a binding 4-circuit off H"
        assert len(tri) <= sum(1 for L in lens if L == 3) <= 2 * D + 6, \
            f"{label}: T exceeds the length-3 branch count"
    return n, M, D, nlam, len(tri), len(quad), len(q4)


def leg_law():
    """[CFL-1] (GR-21) the excess law and (GR-22) the binding-circuit caps."""
    print(f"[CFL-1] (GR-21)/(GR-22) the excess law and the binding caps; "
          f"907 census shapes + the constructed D = 0 pool")
    tot = 0
    cmax = (0, None)
    byD = {}
    for label, edges in census_shapes():
        hm = hub_model(edges)
        if hm is None:
            continue
        n, M, D, nlam, T, Q, q4 = law_checks(label, hm)
        tot += 1
        if 4 * T + 3 * Q > cmax[0]:
            cmax = (4 * T + 3 * Q, (label, T, Q))
        byD[D] = byD.get(D, 0) + 1
    print(f"  census: excess law + all five caps asserted at {tot}/{tot} "
          f"shapes; the (GR-23) load 4T + 3Q peaks at {cmax[0]} "
          f"(T = {cmax[1][1]}, Q = {cmax[1][2]}) at {cmax[1][0]}")
    print(f"  census hub-degree excess D = sum_v (deg - 3), by value: " +
          ", ".join(f"D={k}:{byD[k]}" for k in sorted(byD)))
    # the constructed D = 0 pool -- the stratum the census barely reaches
    pool = 0
    best = (0, None)
    load = {}
    for n in CUBIC_N:
        M = 3 * n // 2
        for hedges in multigraphs(n, M):
            for exc in excess_profiles(M, 6):
                specs = [(u, w, 2 + e) for (u, w), e in zip(hedges, exc)]
                edges = class_shape(specs)
                if edges is None:
                    continue
                hm = hub_model(edges)
                if hm is None:
                    continue
                _, _, D, _, T, Q, _ = law_checks(f"D0n{n}{specs}", hm)
                assert D == 0
                pool += 1
                load[4 * T + 3 * Q] = load.get(4 * T + 3 * Q, 0) + 1
                if 4 * T + 3 * Q > best[0]:
                    best = (4 * T + 3 * Q, (specs, T, Q))
    # (GR-25): the cut criterion agrees with the canonical oracle, everywhere
    agree = disagree = 0
    for n in CUBIC_N:
        M = 3 * n // 2
        for hedges in multigraphs(n, M):
            for exc in excess_profiles(M, 6):
                lens = [2 + e for e in exc]
                specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
                a = class_shape(specs) is not None
                b = cubic_habitat(n, hedges, lens)
                if a == b:
                    agree += 1
                else:
                    disagree += 1
                    if disagree < 4:
                        print(f"    (GR-25) DISAGREES at {specs}: "
                              f"oracle {a}, cut criterion {b}")
    print(f"  (GR-25) the cut criterion vs `gridcol.class_shape`: "
          f"{agree}/{agree + disagree} agree over every (multigraph, excess "
          f"profile) of the D = 0 stratum at n_hub <= 6")
    assert disagree == 0, "(GR-25) is not equivalent to the habitat oracle"
    print(f"  constructed D = 0 pool: {pool} class shapes, all with total "
          f"length excess exactly 6 ((GR-21) at D = 0)")
    print(f"  (GR-23) load 4T + 3Q over the pool: " +
          ", ".join(f"{k}:{load[k]}" for k in sorted(load)))
    print(f"  richest binding-circuit shape: 4T + 3Q = {best[0]} at "
          f"T = {best[1][1]}, Q = {best[1][2]}")
    print(f"    specs = {best[1][0]}")
    assert best[0] < 12 and cmax[0] < 12, \
        "a shape reaches the (GR-23) union-bound threshold 4T + 3Q >= 12"
    print(f"  => 4T + 3Q < 12 EVERYWHERE, on the census and on the whole "
          f"D = 0 stratum: by (GR-23) every one of these shapes PROVABLY "
          f"carries an NC1-passing admissible colouring.")
    print()


# ------------------------------------------------- [CFL-2] --adv: (GR-23) ---

# The F13 adversarial witness, CONSTRUCTED: `K4` with every branch of length
# 2.  Every one of its 24 admissible colourings violates NC1, so the detector
# `--cubic` runs MUST report it as a miss.  It is OUT OF HABITAT and the miss
# is therefore correct behaviour, exactly as at the θ(1,2,9) precedent under
# §(K-clos) (AC-6): `Σℓ = 12` while tightness needs `6c = 18`, each of its
# four triangles is a `(2,2,2)` circuit of total length 6 < 7 (so girth
# fails) and is a proper rigid subgraph `Σ(6−ℓ) = 12 = 6(3−1)` (so `hnoRigid`
# fails).  `K4(2,2,2,2,3,3)` -- the same hub graph inside the habitat -- is
# the negative control.
ADV_SPECS = [(0, 1, 2), (0, 2, 2), (0, 3, 2), (1, 2, 2), (1, 3, 2), (2, 3, 2)]
CTL_SPECS = [(0, 1, 3), (0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3), (2, 3, 3)]


def independent_sets(r):
    """The subsets of `Z_r` with no two cyclically adjacent elements (r >= 3),
    as bitmasks -- the flips (GR-23) is allowed to make on a circuit."""
    out = []
    for s in range(1 << r):
        if all(not (s >> i & 1 and s >> ((i + 1) % r) & 1) for i in range(r)):
            out.append(s)
    return out


def flip_branch(edges, col, path):
    """The colouring with one branch's bit flipped (every edge of the branch
    swaps colour) -- this is the free bit of *Step G12*(i)."""
    out = dict(col)
    for e in path:
        out[e] = 'B' if col[e] == 'A' else 'A'
    return out


def leg_adv():
    """[CFL-2] (GR-23) the flip injection, and the F13 witness."""
    print(f"[CFL-2] (GR-23) the flip injection and the F13 adversarial "
          f"witness (seed {C_SEED + 2})")
    # (GR-23): on the constructed D = 0 pool, every NC1-violating admissible
    # colouring is carried to an NC1-passing admissible one by flipping an
    # independent set of the violated circuit's branches.
    checked = repaired = 0
    for n in (4, 6):
        M = 3 * n // 2
        for hedges in multigraphs(n, M):
            for exc in excess_profiles(M, 6):
                specs = [(u, w, 2 + e) for (u, w), e in zip(hedges, exc)]
                edges = class_shape(specs)
                if edges is None:
                    continue
                hm = hub_model(edges)
                if hm is None or not hm['binding']:
                    continue
                allverts = sorted(verts_of(edges), key=str)
                cols, odd = colourings(edges, cap=1 << 13)
                assert not odd and cols is not None
                for col in cols:
                    if not admissible(edges, allverts, hm, col):
                        continue
                    bad = nc1_violations(hm, col, edges, allverts)
                    if not bad:
                        continue
                    checked += 1
                    walk = next(w for (c, w) in hm['binding']
                                if c == bad[0])
                    r = len(walk)
                    got = False
                    for s in independent_sets(r):
                        if s == 0:
                            continue
                        c2 = col
                        for i in range(r):
                            if s >> i & 1:
                                c2 = flip_branch(edges, c2,
                                                 hm['branches'][walk[i][0]][2])
                        if not admissible(edges, allverts, hm, c2):
                            continue
                        if bad[0] not in nc1_violations(hm, c2, edges,
                                                        allverts):
                            got = True
                            break
                    assert got, f"(GR-23) fails at {specs}"
                    repaired += 1
            if n == 6:
                break            # one multigraph at n = 6 is enough evidence
    print(f"  (GR-23) the flip injection: {repaired}/{checked} NC1-violating "
          f"admissible colourings repaired at the violated circuit by an "
          f"independent-set flip (asserted)")
    # F13: the constructed all-length-2 K4
    edges = subdivide(ADV_SPECS)
    allverts = sorted(verts_of(edges), key=str)
    hm = hub_model(edges)
    n, M = len(hm['hubs']), len(hm['ends'])
    cG = len(edges) - len(allverts) + 1
    assert class_shape(ADV_SPECS) is None, \
        "the F13 witness is unexpectedly IN the habitat"
    assert 5 * len(edges) != 6 * (len(allverts) - 1), \
        "the F13 witness is unexpectedly tight"
    tri = [cyc for (cyc, w) in hm['binding'] if len(cyc) == 3]
    cols, odd = colourings(edges)
    assert not odd
    adm = good = 0
    for col in cols:
        if not admissible(edges, allverts, hm, col):
            continue
        adm += 1
        if not nc1_violations(hm, col, edges, allverts):
            good += 1
    print(f"  F13 witness K4(2,2,2,2,2,2): {adm} admissible colourings, "
          f"{good} of them NC1-passing -> the detector reports a MISS")
    assert adm > 0 and good == 0, "the F13 witness is not NC1-unsatisfiable"
    print(f"    the miss is CORRECT: the witness is out of habitat -- "
          f"5|E| = {5 * len(edges)} != 6(|V| - 1) = "
          f"{6 * (len(allverts) - 1)} (not tight), and each of its "
          f"{len(tri)} triangles is a length-6 circuit (girth < 7) and a "
          f"proper rigid subgraph sum(6 - l) = 12 = 6(3 - 1) (hnoRigid)")
    # the pinned counter-fact: what (GR-17)(d)'s binding LIST says here
    print(f"    pinned counter-fact: (GR-17)(d)'s two-profile list is proven "
          f"only under girth 7; at this witness the binding profiles are "
          f"(2,2,2) and (2,2,2,2), and it is the (2,2,2) triangles -- which "
          f"the habitat forbids -- that carry the kill")
    # the negative control: the same hub graph, inside the habitat
    cedges = class_shape(CTL_SPECS)
    assert cedges is not None, "the negative control is not a class shape"
    chm = hub_model(cedges)
    callv = sorted(verts_of(cedges), key=str)
    ccols, codd = colourings(cedges)
    assert not codd
    cadm = cgood = 0
    for col in ccols:
        if not admissible(cedges, callv, chm, col):
            continue
        cadm += 1
        if not nc1_violations(chm, col, cedges, callv):
            cgood += 1
    print(f"  negative control K4(3,3,3,3,3,3) (IN habitat): {cadm} "
          f"admissible colourings, {cgood} NC1-passing -> no miss")
    assert cgood > 0, "the negative control failed"
    print()


# ----------------------------------------------- [CFL-3] --cubic: the hunt --

def hunt_shape(specs, rng, want_rank=True, col_cap=1 << 16):
    """The detector, at one hub-multigraph spec.

    Returns None if the spec is not a class shape, else a dict with the
    exhaustive counts: how many admissible colourings, how many pass NC1, and
    -- when `want_rank` -- the first one at which BOTH blocks are certified
    generic `dim Z = 0` by an exact rational parameter point, which by (GR-7)
    remark (i) PROVES the generic statement, i.e. (GR-15) at this shape."""
    edges = class_shape(specs)
    if edges is None:
        return None
    hm = hub_model(edges)
    if hm is None:
        return None
    allverts = sorted(verts_of(edges), key=str)
    cols, odd = colourings(edges, cap=col_cap)
    if odd or cols is None:
        return None
    out = dict(adm=0, nc1=0, hit=None, tried=0, edges=edges, hm=hm,
               priv=private_even(hm) is not None,
               T=sum(1 for (c, w) in hm['binding'] if len(c) == 3),
               Q=sum(1 for (c, w) in hm['binding'] if len(c) == 4))
    for col in cols:
        if not admissible(edges, allverts, hm, col):
            continue
        out['adm'] += 1
        if nc1_violations(hm, col, edges, allverts):
            continue
        out['nc1'] += 1
        if not want_rank or out['hit'] is not None:
            continue
        if not filter_pass(edges, allverts, col, hm['hubs']):
            continue
        out['tried'] += 1
        bdA = block_data(edges, allverts, col, 'A')
        bdB = block_data(edges, allverts, col, 'B')
        svA = block_generic_zero(bdA, hm['hubs'], hm['branches'], rng)
        if svA is None:
            continue
        svB = block_generic_zero(bdB, hm['hubs'], hm['branches'], rng)
        if svB is None:
            continue
        # exact-ℚ recheck of the attaining draw (README §4 convention 2),
        # through BOTH the branch system and the landed contracted one
        assert dim_W_branch(bdA, hm['hubs'], hm['branches'], sval=svA) == 0
        assert dim_W_branch(bdB, hm['hubs'], hm['branches'], sval=svB) == 0
        assert dim_Z(bdA, sval=svA) == 0 and dim_Z(bdB, sval=svB) == 0, \
            f"branch model and grid.dim_Z disagree at the hit for {specs}"
        out['hit'] = out['tried']
    return out


def leg_cubic(rank_from=0):
    """[CFL-3] THE FLANK HUNT over the whole `D = 0` stratum."""
    import random
    import time
    print(f"[CFL-3] the flank hunt: the D = 0 (cubic hub multigraph) "
          f"stratum, EXHAUSTIVE over profiles and over bits "
          f"(seed {C_SEED + 3})")
    rng = random.Random(C_SEED + 3)
    t0 = time.time()
    grand = dict(shapes=0, nc1miss=0, rankmiss=0, adm=0, nc1=0, priv=0,
                 lam=0)
    hist = {}
    for n in CUBIC_N:
        M = 3 * n // 2
        gs = multigraphs(n, M)
        shapes = nc1miss = rankmiss = 0
        profs = 0
        for hedges in gs:
            for exc in excess_profiles(M, 6):
                profs += 1
                specs = [(u, w, 2 + e) for (u, w), e in zip(hedges, exc)]
                r = hunt_shape(specs, rng, want_rank=(n >= rank_from))
                if r is None:
                    continue
                shapes += 1
                grand['adm'] += r['adm']
                grand['nc1'] += r['nc1']
                if r['priv']:
                    grand['priv'] += 1
                if any(L == 1 for L in r['hm']['lens']):
                    grand['lam'] += 1
                assert r['priv'] or 4 * r['T'] + 3 * r['Q'] < 12, \
                    f"both proven NC1 criteria fail at {specs}"
                if r['adm'] and not r['nc1']:
                    nc1miss += 1
                    print(f"  *** NC1 MISS n={n} {specs} "
                          f"(admissible {r['adm']}, T={r['T']}, Q={r['Q']})")
                if n >= rank_from:
                    if r['hit'] is None:
                        rankmiss += 1
                        print(f"  *** (GR-15) MISS n={n} {specs} "
                              f"(admissible {r['adm']}, NC1-passing "
                              f"{r['nc1']}, filter-passing tried {r['tried']})")
                    else:
                        hist[r['hit']] = hist.get(r['hit'], 0) + 1
        print(f"  n_hub={n}, M={M}: {len(gs)} hub multigraphs up to iso x "
              f"{len(excess_profiles(M, 6))} excess profiles = {profs} specs; "
              f"{shapes} are class shapes")
        print(f"    NC1-unsatisfiable shapes: {nc1miss}; (GR-15) misses: "
              f"{rankmiss}  [{time.time() - t0:.0f}s]")
        grand['shapes'] += shapes
        grand['nc1miss'] += nc1miss
        grand['rankmiss'] += rankmiss
    print(f"  TOTAL: {grand['shapes']} class shapes of the D = 0 stratum, "
          f"{grand['adm']} admissible colourings enumerated "
          f"({grand['nc1']} NC1-passing)")
    top = sorted(hist)[:6]
    print(f"  first-hit histogram (filter-passing NC1-colourings tried): " +
          ", ".join(f"{k}:{hist[k]}" for k in top) +
          (" ..." if len(hist) > 6 else ""))
    print(f"  (GR-24)'s hypothesis (every binding circuit has a private even "
          f"branch) holds at {grand['priv']}/{grand['shapes']} shapes; every "
          f"shape satisfies (GR-24) or (GR-23), so NC1-satisfiability is "
          f"PROVEN, not merely measured, at all {grand['shapes']} "
          f"({grand['lam']} of them with Lambda != empty)")
    if grand['nc1miss'] == 0 and grand['rankmiss'] == 0:
        print(f"  NO FLANK: every shape of the stratum carries an admissible "
              f"colouring at generic dim Z_+ = dim Z_- = 0, certified by an "
              f"exact rational point.")
    print()


# ------------------------------------------------ [CFL-4] --dens: the rate --

def leg_dens():
    """[CFL-4] the kill density per binding circuit, over the exhaustive
    D = 0 pool -- the number the union-bound verdict rests on."""
    print(f"[CFL-4] the kill density per binding circuit over the D = 0 pool")
    worst = None
    tot_adm = tot_bad = 0
    nb_tot = 0
    shapes = 0
    perc = []
    for n in CUBIC_N:
        M = 3 * n // 2
        for hedges in multigraphs(n, M):
            for exc in excess_profiles(M, 6):
                specs = [(u, w, 2 + e) for (u, w), e in zip(hedges, exc)]
                edges = class_shape(specs)
                if edges is None:
                    continue
                hm = hub_model(edges)
                if hm is None or not hm['binding']:
                    continue
                allverts = sorted(verts_of(edges), key=str)
                cols, odd = colourings(edges, cap=1 << 13)
                if odd or cols is None:
                    continue
                adm = bad = 0
                percirc = {}
                for col in cols:
                    if not admissible(edges, allverts, hm, col):
                        continue
                    adm += 1
                    v = nc1_violations(hm, col, edges, allverts)
                    if v:
                        bad += 1
                    for cyc in v:
                        percirc[cyc] = percirc.get(cyc, 0) + 1
                if not adm:
                    continue
                # (GR-23)'s own sentence, asserted per binding circuit: the
                # flip injection bounds the fraction of admissible colourings
                # bad at ONE circuit by `1/(|S| + 1)` with `S` the nonempty
                # independent sets of EVEN branches of the circuit (1/3 at a
                # `(2,2,3)` triangle, 1/4 at a `(2,2,2,2)` 4-circuit).  Only
                # asserted at `Λ = ∅`: with a hub-hub edge an off-circuit
                # merge can keep `D_A < runs` after the flip, so the image is
                # not certified good there.
                if all(L != 1 for L in hm['lens']):
                    for (cyc, walk) in hm['binding']:
                        order = [k for (k, _u, _w) in walk]
                        r = len(order)
                        S = [s for s in independent_sets(r) if s
                             and all(hm['lens'][order[i]] % 2 == 0
                                     for i in range(r) if s >> i & 1)]
                        if not S:
                            continue
                        mult = 2 if any((~s) & ((1 << r) - 1) in S
                                        for s in S) else 1
                        den = len(S) // mult + 1
                        assert percirc.get(cyc, 0) * den <= adm, \
                            f"(GR-23) 1/{den} bound broken at {specs}: " \
                            f"{percirc.get(cyc, 0)}/{adm} at a {r}-circuit"
                shapes += 1
                nb = len(hm['binding'])
                nb_tot += nb
                tot_adm += adm
                tot_bad += bad
                rate = F(bad, adm * nb)
                perc.append(rate)
                if worst is None or rate > worst[0]:
                    worst = (rate, specs, nb, adm, bad)
    perc.sort()
    print(f"  shapes carrying a binding circuit: {shapes}; binding circuits "
          f"in total {nb_tot}")
    print(f"  admissible colourings {tot_adm}, NC1-violating {tot_bad} "
          f"(pooled {float(F(tot_bad, tot_adm)):.4f} of admissible)")
    print(f"  kill fraction per binding circuit: median "
          f"{float(perc[len(perc) // 2]):.4f}, max "
          f"{float(worst[0]):.4f} (proven cap 1/4 by (GR-23))")
    print(f"    max at {worst[1]}: {worst[2]} binding circuits, "
          f"{worst[4]}/{worst[3]} admissible colourings killed")
    assert worst[0] <= F(1, 4), "(GR-23)'s 1/4 cap is violated"
    thresh = 1 / float(worst[0])
    print(f"  => a flank driven by (NC1) alone needs more than "
          f"{thresh:.0f} binding circuits at ONE shape; (GR-22) caps that "
          f"count by 1/4 * sum_v C(deg_H v, 2) <= 3 n_hub / 4 at D = 0.")
    print()


# ------------------------------------------------ [CFL-6] --lam: Lambda != 0 -

def length_tuples(M, tgt, lamcap=99, lo=1, hi=5):
    """Every length tuple in `[lo, hi]^M` summing to `tgt` with at most
    `lamcap` entries equal to 1 -- the `Λ ≠ ∅` companion of
    `excess_profiles`, which only reaches `ℓ ≥ 2`."""
    out = []

    def rec(i, rem, acc, lam):
        if i == M:
            if rem == 0:
                out.append(tuple(acc))
            return
        for L in range(lo, hi + 1):
            nl = lam + (1 if L == 1 else 0)
            if nl > lamcap:
                continue
            if L + hi * (M - i - 1) < rem or L + lo * (M - i - 1) > rem:
                continue
            acc.append(L)
            rec(i + 1, rem - L, acc, nl)
            acc.pop()
    rec(0, tgt, [], 0)
    return out


LAM_PLAN = ((2, 3, 99), (4, 6, 99))
LAM6_PLAN = ((6, 9, 1),)


def leg_lam(plan=None):
    """[CFL-6] the `Λ ≠ ∅` half of the D = 0 stratum -- the regime where
    (GR-17)(d)'s binding list is only MEASURED, where an off-circuit merge can
    push `D_A` below the run count, and where a binding circuit can have NO
    even branch, so that (GR-23)/(GR-24)'s balance-preserving flip does not
    exist and only the exhaustive scan carries the shape."""
    import random
    import time
    print(f"[CFL-6] the Lambda != empty half of the D = 0 stratum "
          f"(seed {C_SEED + 6})")
    rng = random.Random(C_SEED + 6)
    t0 = time.time()
    tot = nc1miss = rankmiss = xval = noeven = lamshapes = 0
    for (n, M, cap) in (plan or LAM_PLAN):
        tgt = 6 * (M - n + 1)
        tup = length_tuples(M, tgt, lamcap=cap)
        shapes = 0
        for hedges in multigraphs(n, M):
            for lens in tup:
                if not cubic_habitat(n, hedges, list(lens)):
                    continue
                specs = [(u, w, L) for (u, w), L in zip(hedges, lens)]
                if M <= 6:
                    assert class_shape(specs) is not None, \
                        f"(GR-25) accepts a non-class shape: {specs}"
                    xval += 1
                shapes += 1
                if any(L == 1 for L in lens):
                    lamshapes += 1
                r = hunt_shape(specs, rng)
                if r is None:
                    continue
                tot += 1
                hm = r['hm']
                if any(not any(hm['lens'][k] % 2 == 0 for k in cyc)
                       for (cyc, w) in hm['binding']):
                    noeven += 1
                if r['adm'] and not r['nc1']:
                    nc1miss += 1
                    print(f"  *** NC1 MISS n={n} {specs}")
                if r['hit'] is None:
                    rankmiss += 1
                    print(f"  *** (GR-15) MISS n={n} {specs} "
                          f"(admissible {r['adm']}, NC1-passing {r['nc1']})")
        print(f"  n_hub={n}, M={M}, |Lambda| <= {cap}: {len(tup)} length "
              f"tuples x {len(multigraphs(n, M))} hub multigraphs; "
              f"{shapes} class shapes  [{time.time() - t0:.0f}s]")
    print(f"  (GR-25) cross-validated against `gridcol.class_shape` at "
          f"{xval} shapes (every M <= 6 one, Lambda included)")
    print(f"  {tot} shapes tested exhaustively over bits, {lamshapes} of them "
          f"with Lambda != empty; {noeven} carry a binding circuit with NO "
          f"even branch (where the (GR-23)/(GR-24) flip does not exist)")
    print(f"  NC1-unsatisfiable shapes: {nc1miss}; (GR-15) misses: "
          f"{rankmiss}")
    assert nc1miss == 0 and rankmiss == 0
    print()


# --------------------------------------------- [CFL-5] --tight: the targets -

def ring(vs):
    return [(vs[i], vs[(i + 1) % len(vs)]) for i in range(len(vs))]


def ladder(n):
    """The circular ladder `C_n x K_2` -- cubic, girth 4, `n` squares, and
    (for n >= 4) no non-trivial 3-edge-cut, so the excess is free to place."""
    top, bot = list(range(n)), list(range(n, 2 * n))
    return ring(top) + ring(bot) + [(i, i + n) for i in range(n)]


def truncate(hedges, n):
    """Replace every vertex of a cubic multigraph by a triangle (the classical
    truncation): the unique cubic family whose binding triangles can reach the
    (GR-21) cap `T = 2D + 6 = 6`, and therefore the family at which (GR-23)'s
    union bound provably RUNS OUT."""
    inc = {v: [] for v in range(n)}
    for k, (u, w) in enumerate(hedges):
        inc[u].append(k)
        inc[w].append(k)
    node = {}
    out = []
    for v in range(n):
        for j, k in enumerate(inc[v]):
            node[(v, k)] = len(node)
        t = [node[(v, k)] for k in inc[v]]
        assert len(t) == 3, "truncation needs a cubic graph"
        out += ring(t)
    legs = [(node[(u, k)], node[(w, k)]) for k, (u, w) in enumerate(hedges)]
    return out + legs, len(node)


CUBE = ring([0, 1, 2, 3]) + ring([4, 5, 6, 7]) + [(i, i + 4) for i in range(4)]
WAGNER = ring(list(range(8))) + [(i, i + 4) for i in range(4)]
K4H = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PRISM = ring([0, 1, 2]) + ring([3, 4, 5]) + [(0, 3), (1, 4), (2, 5)]


def targets():
    """The named large candidates the (GR-21)/(GR-22) analysis singles out --
    every one is a CONSTRUCTION aimed at a specific way of defeating the two
    proven criteria, not a member of any sampled pool."""
    tri4, n4 = truncate(K4H, 4)
    tri6, n6 = truncate(PRISM, 6)
    out = []
    # (a) the cube: the UNIQUE local shape in which all four branches of a
    #     binding 4-circuit can be shared with other binding 4-circuits
    #     (each edge of Q3 lies in exactly two of its six squares)
    out.append(('cube Q3, excess on two opposite top edges', 8, CUBE,
                {0: 3, 2: 3}))
    out.append(('cube Q3, excess on two adjacent top edges', 8, CUBE,
                {0: 3, 1: 3}))
    out.append(('cube Q3, excess spread 2+2+2 on the top square', 8, CUBE,
                {0: 2, 1: 2, 2: 2}))
    # (b) the Wagner graph V8: the other cubic graph on 8 hubs with girth 4
    out.append(('Wagner V8, excess on two rim edges', 8, WAGNER, {0: 3, 4: 3}))
    out.append(('Wagner V8, excess on two spokes', 8, WAGNER, {8: 3, 10: 3}))
    # (c) circular ladders: `n` squares, all sharing rungs -- the densest
    #     branch-SHARING family of binding 4-circuits the habitat allows
    for k in (5, 6, 7, 8):
        L = ladder(k)
        out.append((f'ladder CL{k}, excess on two far rungs', 2 * k, L,
                    {2 * k: 3, 2 * k + k // 2: 3}))
        out.append((f'ladder CL{k}, excess 2+2+2 on three rungs', 2 * k, L,
                    {2 * k: 2, 2 * k + 1: 2, 2 * k + 2: 2}))
    # (d) the truncations: the family that reaches the (GR-21) cap on binding
    #     TRIANGLES, where (GR-23)'s union bound provably runs out (4T >= 12)
    out.append(('truncated K4 (4 binding triangles)', n4, tri4,
                {0: 1, 3: 1, 6: 1, 9: 1, 12: 2}))
    out.append(('truncated prism (6 binding triangles, T = the (GR-21) cap)',
                n6, tri6, {0: 1, 3: 1, 6: 1, 9: 1, 12: 1, 15: 1}))
    return out


def one_admissible(edges, allverts, hm, rng, tries=40000):
    """A single admissible colouring, drawn from the CANONICAL alternation
    components (`closure.alternation_classes`, the same object
    `closure.colourings` enumerates) -- needed because at n_hub >= 10 the
    `2^M` enumeration is out of reach and the point here is to EXHIBIT a good
    colouring, not to search for one."""
    comps, odd = alternation_classes(edges)
    if odd:
        return None
    for _ in range(tries):
        bits = [rng.randint(0, 1) for _ in comps]
        col = {}
        for c, b in zip(comps, bits):
            for e, p in c.items():
                col[e] = 'A' if (p ^ b) == 0 else 'B'
        if admissible(edges, allverts, hm, col):
            return col
    return None


def leg_tight():
    """[CFL-5] the named large targets: the shapes at which the two proven
    criteria are contested, carried by (GR-24)'s constructive repair."""
    import random
    print(f"[CFL-5] the named large targets (seed {C_SEED + 5}); every one a "
          f"construction aimed at defeating (GR-23) or (GR-24)")
    rng = random.Random(C_SEED + 5)
    done = skip = 0
    for (name, n, hedges, exc) in targets():
        specs = [(u, w, 2 + exc.get(k, 0)) for k, (u, w) in enumerate(hedges)]
        tot = sum(L - 2 for (_, _, L) in specs)
        if tot != 6:
            print(f"  {name}: SKIPPED, excess {tot} != 6 ((GR-21) at D = 0)")
            skip += 1
            continue
        if not cubic_habitat(n, hedges, [L for (_, _, L) in specs]):
            print(f"  {name}: NOT a class shape ((GR-25) rejects it)")
            skip += 1
            continue
        edges = (class_shape(specs) if len(hedges) <= 12
                 else subdivide(specs))
        assert edges is not None, f"{name}: the two habitat routes disagree"
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        T = sum(1 for (c, w) in hm['binding'] if len(c) == 3)
        Q = sum(1 for (c, w) in hm['binding'] if len(c) == 4)
        priv = private_even(hm)
        load = 4 * T + 3 * Q
        tag = []
        if load < 12:
            tag.append("(GR-23)")
        if priv is not None:
            tag.append("(GR-24)")
        assert tag, f"{name}: BOTH proven criteria fail -- inspect by hand"
        assert priv is not None, f"{name}: (GR-24) has no private even branch"
        hit, seeds = 'no NC1-clear colouring reached rank 0', 0
        for _ in range(24):
            col = one_admissible(edges, allverts, hm, rng)
            assert col is not None, f"{name}: no admissible colouring found"
            col = repair(edges, allverts, hm, col, priv)
            assert not nc1_violations(hm, col, edges, allverts), \
                f"{name}: (GR-24)'s repair did not clear NC1"
            assert admissible(edges, allverts, hm, col), \
                f"{name}: (GR-24)'s repair broke admissibility"
            seeds += 1
            if not filter_pass(edges, allverts, col, hm['hubs']):
                continue
            bdA = block_data(edges, allverts, col, 'A')
            bdB = block_data(edges, allverts, col, 'B')
            svA = block_generic_zero(bdA, hm['hubs'], hm['branches'], rng,
                                     draws=4)
            if svA is None:
                continue
            svB = block_generic_zero(bdB, hm['hubs'], hm['branches'], rng,
                                     draws=4)
            if svB is None:
                continue
            assert dim_W_branch(bdA, hm['hubs'], hm['branches'],
                                sval=svA) == 0
            assert dim_W_branch(bdB, hm['hubs'], hm['branches'],
                                sval=svB) == 0
            assert dim_Z(bdA, sval=svA) == 0 and dim_Z(bdB, sval=svB) == 0
            hit = (f'dim Z_+ = dim Z_- = 0 (exact Q certificate, repaired '
                   f'colouring {seeds})')
            break
        print(f"  {name}: n_hub={n} M={len(hedges)} T={T} Q={Q} "
              f"4T+3Q={load} [{'+'.join(tag)}] -> {hit}")
        done += 1
    print(f"  {done} targets carried, {skip} skipped; NO target defeats both "
          f"proven criteria, and each one's repaired colouring is exhibited.")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('law', 'adv', 'cubic', 'lam', 'lam6', 'dens', 'tight',
              'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.law, a.adv, a.cubic, a.lam, a.lam6,
                                 a.dens, a.tight])
    if run or a.law:
        leg_law()
    if run or a.adv:
        leg_adv()
    if run or a.cubic:
        leg_cubic()
    if run or a.lam:
        leg_lam()
    if a.lam6:
        leg_lam(LAM6_PLAN)
    if run or a.dens:
        leg_dens()
    if run or a.tight:
        leg_tight()
    print("OK")


if __name__ == '__main__':
    main()
