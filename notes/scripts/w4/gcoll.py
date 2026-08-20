#!/usr/bin/env python3
"""GCOLL -- direction GCOLL (Phase 39, eighth fan-out, 2026-08-19): is
(GR-64)(R2) a THEOREM?  Does every habitat shape carry an anchor matching
`M` with `B(M) = 0` -- i.e. can the (GR-64) collision mechanism ever
obstruct (a')?

Answers `notes/Pencil-fanout.md` §"GCOLL -- twenty-seventh direction
(eighth fan-out)"; the mathematics is `notes/Pencil-informal-grid.md`
§(K-grid) *Steps G110-G115*, labels (GR-91)-(GR-96).

Everything here is at `Lambda = empty`, `D = 0`, modulo (GR-4').  Nothing
here closes (GR-15).  (R2) is a sub-target of input (Y), NOT (a') itself,
so nothing here can fire E3 (ARMED by GBAL's entry-5 HIT) -- see
*Step G115*.

The whole pass is COLOURING-FREE: no admissible cube is ever enumerated
(that is why it reaches shapes YLOC's `--coll` could not).  `d_adm`,
`d_fg` and full goodness are never recomputed here -- (GR-58)/(GR-64) own
those figures and this driver consumes them.

Modes
-----
--slack   (GR-91): the SLACK reformulation of the (GR-64) statistic --
          `coll_M(S) = |W_S| - 2|M cap S| = z(S) - s_M(S)` with
          `s_M(S)` the number of interiors matched INSIDE `S`; `s_M(S)`
          is always EVEN, hence `term(S) > 0` iff `s_M(S) = 0` iff
          `term(S) = r(S) := 6 - z(S) - exc(S)`, and the collision set
          of a positive-term chunk is its WHOLE interior set.  Asserted
          at every (inventory shape, matching, proper chunk) triple
          against the landed `yloc.collide` / `coll_terms` /
          `pack_bound`.
--dem     (GR-92): the DEMAND classification -- a chunk can demand
          anything at all only at six `(z, exc)` profiles, `r <= 2`
          always, `r = 2` only at `(3,1)` and `(4,0)`; the chord
          refinement of (GR-32)(ii); the `partial = 2` two-cut normal
          form.  Exhaustive census over the inventory.
--tf      (GR-93): the 2-FACTOR criterion -- a violated chunk's hub set
          is a union of cycles of the 2-factor `F = E \\ M`, with every
          chord in `M`; so violation detection at a fixed `M` is a
          `2^{c(F)}` search and needs NO chunk scan.  Asserted EQUAL to
          the landed `2^M` ground truth at every (inventory shape,
          matching) pair.
--suff    (GR-94): the two PROVEN sufficient conditions for
          `B(M) = 0` -- the cyclic-edge-connectivity one and the
          Hamiltonian one -- and their measured coverage, which is the
          whole 4924-shape inventory.
--big8    (GR-96)(a) = (GR-64)(R1): exact, uncapped `min_M B(M)` at the
          COMPLETE `n_hub = 8` habitat stratum (39 689 shapes).
--bigp    (GR-95) + (GR-96)(b): the same at the Petersen graph's whole
          habitat family (`n_hub = 10`, non-Hamiltonian, off-inventory)
          -- where (R2) is **REFUTED**, 180 of 36 860 length assignments
          carrying `min_M B(M) = 1` -- and at W5 (`E = 24`, disclosed out
          of reach for the chunk scan) and the eight odd-rich necklaces
          (`n_hub = 30, 40`).
--wit     (GR-95) verification: the 180 refuting witnesses re-verified
          through the LANDED `2^M` chunk scan and certified habitat by
          the canonical oracle `gridcol.class_shape` (not merely by
          (GR-25)), plus the two-mechanism census.
--dfg     (GR-95)(iv): `d_adm` and `d_fg` computed EXACTLY at all 180
          witnesses -- the E1(iv)/E2 detector (`min_M B > d_adm` would
          prove `d_adm < d_fg`) and the (a')-corroboration by-product.
--adv     F13 falsification controls, each with a must-fire witness.
--validate  all nine in one process (over the 600 s foreground budget --
          run the modes separately).

Discipline (`notes/scripts/README.md` §§1-4): exact integers only, no
floating point outside the self-timing prints; every rng seeded from
C_SEED and printed; no bare `set` printed; imports read-only from the
canonical layer.  No geometry is sampled anywhere in this driver -- every
object is a hub multigraph, a branch subset or a perfect matching -- so
the `plane_basis` degeneracy precedent has no sampled placement to
guard; the standing guard is discharged instead by routing every
structural verdict through a LANDED oracle and asserting agreement:
`yloc.collide` / `yloc.coll_terms` / `yloc.pack_bound` for the (GR-64)
statistic, `yloc.shape_ctx` (hence `gorient.prep_shape`, hence
`gcap.two_ec_subsets` at `kmin = 1`) for the chunk family,
`cflank.cubic_habitat` for habitat membership, `gorient.perfect_matchings`
for the matchings, `aglu.cubic_iso_classes` + `cflank.excess_profiles`
for the `n_hub = 8` stratum.  No rank and no colouring is touched.
"""

import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import yloc                                                            # noqa: E402
from cflank import admissible, cubic_habitat, excess_profiles          # noqa: E402
from gbal import z_to_map                                              # noqa: E402
from gridcol import class_shape                                        # noqa: E402
from gcap import branch_stats                                          # noqa: E402
from gorient import (cm_colouring, fully_good_scan,                     # noqa: E402
                     perfect_matchings)
from aglu import cubic_iso_classes                                     # noqa: E402
from gpsa import branches_at                                           # noqa: E402

C_SEED = 20260819

# The Petersen graph on 10 hubs, as a hub multigraph: outer 5-cycle,
# inner pentagram, five spokes.  Cubic, bridgeless, girth 5, cyclically
# 5-edge-connected, and NOT Hamiltonian -- the standard witness that the
# Hamiltonian sufficient condition (GR-94)(ii) is not vacuous, and the
# first non-Hamiltonian shape the collision statistic has been measured
# at.  Branch lengths are supplied per length assignment, not here.
PETERSEN = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
            (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
            (0, 5), (1, 6), (2, 7), (3, 8), (4, 9))

# `gorient.perfect_matchings`' own cap; raised explicitly wherever a
# shape's matching count could approach it, and DISCLOSED at every use.
PM_CAP = 100000


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a §1 primitive (checked against the README index
# and the Divergences table).  `is_chunk` is the only one that duplicates
# a canonical decision -- it is the membership predicate of
# `gcap.two_ec_masks(kmin = 1)`, needed because (GR-93)'s whole point is
# to decide chunk-hood for a CONSTRUCTED branch set without running the
# `2^M` scan that builds the family; `--tf` asserts every set it accepts
# is in the canonical family and that the two agree on every violated
# chunk of every (inventory shape, matching) pair.


def chunk_prof(specs, cd):
    """The colouring-free demand profile of a chunk, from `yloc.
    chunk_static`'s record: (z, exc, cap, r, ch, partial, nW) with
    `ch` the chords, `partial = |boundary(W_S)|` the exits and
    `r = 6 - z - exc` the DEMAND -- the least `s_M(S)` a matching must
    supply to keep the chunk's (GR-64) term non-positive."""
    frees = {}
    for (_v, _b1, _b2, b3) in cd['ints']:
        frees[b3] = frees.get(b3, 0) + 1
    ch = sum(1 for k in frees.values() if k == 2)
    part = sum(1 for k in frees.values() if k == 1)
    assert all(k in (1, 2) for k in frees.values()), \
        "a free branch with three interior ends: not a cubic host"
    assert part + 2 * ch == cd['z'], "exits + 2 chords != z"
    return (cd['z'], cd['exc'], cd['cap'], 6 - cd['z'] - cd['exc'],
            ch, part, cd['nW'])


def slack_of(cd, mb):
    """`s_M(S)` -- the number of interiors of `S` whose MATCHING branch
    lies inside `S` (equivalently: the free-branch weight `M` avoids,
    exits counting 1 and chords 2)."""
    return sum(1 for (v, _b1, _b2, b3) in cd['ints'] if mb[v] != b3)


def f_cycles(specs, n, mat):
    """The cycles of the 2-factor `F = E(G) \\ M`, as
    (hub frozenset, branch frozenset).  `F` is a 2-factor because the
    host is cubic and `M` is perfect, so every component is a circuit."""
    ms = set(mat)
    adj = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        if i in ms:
            continue
        adj[u].append((w, i))
        adj[w].append((u, i))
    for v in range(n):
        assert len(adj[v]) == 2, "F is not a 2-factor: cubic host + PM?"
    seen = set()
    out = []
    for v0 in range(n):
        if v0 in seen:
            continue
        comp, bs, st = {v0}, set(), [v0]
        seen.add(v0)
        while st:
            v = st.pop()
            for (u, i) in adj[v]:
                bs.add(i)
                if u not in comp:
                    comp.add(u)
                    seen.add(u)
                    st.append(u)
        assert len(bs) == len(comp), "an F-component that is not a circuit"
        out.append((frozenset(comp), frozenset(bs)))
    return out


def is_chunk(specs, S):
    """`gcap.two_ec_masks(kmin = 1)` membership for a branch set `S`:
    every touched hub of degree >= 2, connected, bridgeless, cycle rank
    >= 1.  (`kmin = 1` is `gorient.prep_shape`'s own setting -- the
    (GR-64) chunk family INCLUDES circuits, which is load-bearing here:
    an F-cycle of the 2-factor is itself a chunk.)"""
    if not S:
        return False
    deg = {}
    adj = {}
    for i in S:
        (u, w, _L) = specs[i]
        deg[u] = deg.get(u, 0) + 1
        deg[w] = deg.get(w, 0) + 1
        adj.setdefault(u, []).append((w, i))
        adj.setdefault(w, []).append((u, i))
    if any(d < 2 for d in deg.values()):
        return False
    vs = sorted(deg)
    if len(S) - len(vs) + 1 < 1:
        return False
    seen, st = {vs[0]}, [vs[0]]
    while st:
        v = st.pop()
        for (u, _i) in adj[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    if len(seen) != len(vs):
        return False
    for kd in S:
        root = specs[kd][0]
        s2, st = {root}, [root]
        while st:
            v = st.pop()
            for (u, i) in adj[v]:
                if i != kd and u not in s2:
                    s2.add(u)
                    st.append(u)
        if len(s2) != len(vs):
            return False
    return True


def stat_of(specs, S):
    """(z, exc, r, interiors) of a branch set, colouring-free."""
    deg = {}
    for i in S:
        (u, w, _L) = specs[i]
        deg[u] = deg.get(u, 0) + 1
        deg[w] = deg.get(w, 0) + 1
    ints = frozenset(v for v, d in deg.items() if d == 2)
    exc = sum(specs[i][2] - 2 for i in S)
    z = len(ints)
    return z, exc, 6 - z - exc, ints


def violated_2f(specs, n, mat, cycs=None):
    """(GR-93): ALL positive-(GR-64)-term chunks at the matching `M`,
    found without any chunk scan.

    A chunk has a positive term iff `s_M(S) = 0` iff every interior's
    free branch is in `M`; then every hub of `W_S` has both its
    `F`-branches inside `W_S`, so `W_S` is a union of `F`-cycles and
    `S = E(W_S) \\ C` for a vertex-disjoint `C` of `M`-branches inside
    `W_S` with `|boundary| + 2|C| = z(S) <= 5`.  Returns
    {(branch tuple, term)}."""
    ms = set(mat)
    if cycs is None:
        cycs = f_cycles(specs, n, mat)
    out = set()
    for msk in range(1, 1 << len(cycs)):
        W = set()
        for j in range(len(cycs)):
            if msk >> j & 1:
                W |= cycs[j][0]
        EW = [i for i, (u, w, _L) in enumerate(specs) if u in W and w in W]
        part = sum(1 for (u, w, _L) in specs if (u in W) != (w in W))
        if part > 5:
            continue
        intM = [i for i in EW if i in ms]
        for nc in range(0, (5 - part) // 2 + 1):
            for C in itertools.combinations(intM, nc):
                ends = [v for i in C for v in specs[i][:2]]
                if len(set(ends)) != len(ends):
                    continue
                S = tuple(i for i in EW if i not in C)
                if len(S) == len(specs):
                    continue                      # S = E(G): improper chunk
                z, _exc, r, _ints = stat_of(specs, S)
                if r < 1 or z != part + 2 * nc:
                    continue
                if not is_chunk(specs, S):
                    continue
                out.add((S, r))
    return out


def pack_of(specs, viol):
    """`B(M)` from (GR-93)'s violated-chunk list: the (GR-64)(iii)
    packing bound, whose collision sets are (by (GR-91)) the whole
    interior sets.  Routed through the landed `yloc.pack_bound`."""
    return yloc.pack_bound([(r, stat_of(specs, S)[3]) for (S, r) in viol])


def min_B(specs, n, mats):
    """`min_M B(M)`, exact, by (GR-93) -- no chunk scan, no cap on the
    chunk side.  Returns (value, witness matching)."""
    best, wit = None, None
    for mat in mats:
        b = pack_of(specs, violated_2f(specs, n, mat))
        if best is None or b < best:
            best, wit = b, mat
        if best == 0:
            break
    return best, wit


def cyclic_edge_conn(specs, n):
    """The cyclic edge connectivity of a hub multigraph, exactly, by a
    `2^n` hub-subset scan: the least `|boundary(W)|` over `W` with a
    circuit on BOTH sides.  `None` when no cyclic edge cut exists.
    (`2^n` is why this is only ever called at `n <= 16`.)"""
    best = None
    for msk in range(1, (1 << n) - 1):
        W = {v for v in range(n) if msk >> v & 1}
        Ein = [i for i, (u, w, _L) in enumerate(specs)
               if (u in W) and (w in W)]
        Eout = [i for i, (u, w, _L) in enumerate(specs)
                if (u not in W) and (w not in W)]
        if not _has_circuit(specs, Ein) or not _has_circuit(specs, Eout):
            continue
        bd = len(specs) - len(Ein) - len(Eout)
        if best is None or bd < best:
            best = bd
    return best


def _has_circuit(specs, E):
    """Does the branch set `E` contain a circuit?  (Some component is
    not a tree.)"""
    if not E:
        return False
    par = {}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for i in E:
        for v in specs[i][:2]:
            par.setdefault(v, v)
    for i in E:
        a, b = find(specs[i][0]), find(specs[i][1])
        if a == b:
            return True
        par[a] = b
    return False


def long5(specs):
    """The length-5 branches -- at most two, since (GR-21) pins the total
    excess at 6 and (SD-6) caps a branch at 5."""
    out = [i for i, (_u, _w, L) in enumerate(specs) if L == 5]
    assert len(out) <= 2, "three length-5 branches: excess > 6"
    return out


def ham_witness(specs, n, mats):
    """(GR-94)(ii): a matching `M` whose 2-factor `E \\ M` is a single
    Hamiltonian circuit and which contains NO length-5 branch, or
    `None`."""
    bad = set(long5(specs))
    for mat in mats:
        if bad & set(mat):
            continue
        cy = f_cycles(specs, n, mat)
        if len(cy) == 1:
            return mat
    return None


def avoid5_witness(specs, n, mats):
    """A matching containing no length-5 branch, or `None` -- the
    hypothesis Plesnik 1972 supplies for a 2-edge-connected cubic host
    (at most two branches to avoid)."""
    bad = set(long5(specs))
    for mat in mats:
        if not (bad & set(mat)):
            return mat
    return None


# --------------------------------------------------- shape inventories ------

def inventory():
    """YLOC's own 4924-shape inventory, read-only: the exhaustive
    `n_hub <= 6` habitat stratum plus W3M / W3 / W4 / NKo2v."""
    return yloc.all_shapes()


def petersen_family():
    """Every habitat length assignment of the Petersen graph: all
    `excess_profiles(15, 6)` distributions gated through
    `cflank.cubic_habitat`.  EXHAUSTIVE for that graph -- no cap.

    Also returns the REJECTED profiles, because which ones they are is a
    checkable sentence: the Petersen graph's only 3-edge-cuts are its
    vertex stars, so the only proper connected `W` with `|W| >= 2` and
    `partial(W) = 3` is a single vertex's complement, and (GR-25) then
    demands `exc(E(W)) >= 1` -- i.e. the gate rejects exactly the
    profiles that pile all 6 excess units onto one hub's three
    branches."""
    out, bad = [], []
    stars = [tuple(i for i, (u, w) in enumerate(PETERSEN) if v in (u, w))
             for v in range(10)]
    for exc in excess_profiles(15, 6):
        lens = [2 + e for e in exc]
        specs = tuple((u, w, L) for (u, w), L in zip(PETERSEN, lens))
        if cubic_habitat(10, [tuple(e) for e in PETERSEN], lens):
            out.append(specs)
        else:
            bad.append(specs)
    for specs in bad:
        assert any(sum(specs[i][2] - 2 for i in st) == 6 for st in stars), \
            "a Petersen profile rejected for some other reason"
    for specs in out:
        assert not any(sum(specs[i][2] - 2 for i in st) == 6
                       for st in stars), \
            "a star-concentrated Petersen profile passed the gate"
    return out


_WITS = [None]


def petersen_witnesses():
    """(GR-95): the habitat length assignments of the Petersen graph at
    which EVERY anchor matching has `B(M) >= 1` -- the (GR-64)(R2)
    counterexamples.  Memoized; deterministic (`excess_profiles`' own
    order, no rng)."""
    if _WITS[0] is not None:
        return _WITS[0]
    out = []
    for specs in petersen_family():
        mats = perfect_matchings(list(specs), cap=PM_CAP)
        b, _w = min_B(list(specs), 10, mats)
        if b > 0:
            out.append((specs, b))
    _WITS[0] = out
    return out


def stratum8():
    """The COMPLETE `n_hub = 8` habitat stratum, rebuilt from the
    canonical layer (`aglu.cubic_iso_classes(8)` +
    `cflank.excess_profiles(12, 6)` + `cflank.cubic_habitat`): 39 689
    shapes over 20 hub-multigraph classes, AGLU's landed count.
    Returned grouped by class, because every structure this pass needs
    (matchings, 2-factors, unions, boundaries) is length-INDEPENDENT and
    is therefore computed once per class."""
    reps = cubic_iso_classes(8)
    ep = excess_profiles(12, 6)
    out = []
    for hedges in reps:
        lens_ok = [tuple(2 + e for e in exc) for exc in ep
                   if cubic_habitat(8, list(hedges), [2 + e for e in exc])]
        if lens_ok:
            out.append((tuple(hedges), lens_ok))
    return out, len(ep)


def big_named():
    """The named large shapes, read-only from the canonical layer: W5
    (`E = 24`, out of reach for the `2^M` chunk scan) and the eight
    odd-rich necklaces at `m = 6, 8` (`n_hub = 30, 40`)."""
    keep = ('W5', 'NKp(6)', 'NK55(6)', 'NK(6)', 'NKo(6)',
            'NKp(8)', 'NK55(8)', 'NK(8)', 'NKo(8)')
    return [(t, n, s) for (t, n, s) in yloc.named_shapes() if t in keep]


# ---------------------------------------------- [GC-1] --slack: (GR-91) -----

def leg_slack():
    """[GC-1] (GR-91): the slack reformulation and the parity collapse."""
    t0 = time.time()
    print("[GC-1] (GR-91) the SLACK reformulation of the (GR-64) statistic")
    inv = inventory()
    trip = 0
    tight = 0
    sdist = {}
    tdist = {}
    Bdist = {}
    minB = {}
    for (_tag, n, specs) in inv:
        ctx = yloc.shape_ctx(specs, n)
        cds = ctx['cds']
        mats = perfect_matchings(specs, cap=PM_CAP)
        assert mats, "habitat shape with no perfect matching"
        best = None
        for mat in mats:
            mb = yloc.matb(specs, mat)
            mset = set(mat)
            terms = []
            for cd in cds:
                if cd['improper']:
                    continue
                (z, exc, cap, r, _ch, _pt, nW) = chunk_prof(specs, cd)
                coll = len(yloc.collide(cd, mb))
                s = slack_of(cd, mb)
                # (i) the three forms of the collision count
                assert coll == z - s, "(GR-91)(i) FAILS: coll != z - s"
                assert coll == nW - 2 * len(set(cd['S']) & mset), \
                    "(GR-91)(i) FAILS: coll != |W_S| - 2|M cap S|"
                # (ii) the slack is EVEN
                assert s % 2 == 0, "(GR-91)(ii) FAILS: odd slack"
                # (iii) term = r - s, so term > 0 iff s = 0 iff term = r
                term = coll - cap + 6
                assert term == r - s, "(GR-91)(iii) FAILS: term != r - s"
                assert (term > 0) == (s == 0 and r >= 1), \
                    "(GR-91)(iii) FAILS: a positive term off `s = 0, r >= 1`"
                if term > 0:
                    assert term == r and r in (1, 2), \
                        "(GR-91)(iii) FAILS: a positive term other than r"
                    # (iv) the collision set is the WHOLE interior set
                    assert yloc.collide(cd, mb) == \
                        frozenset(v for (v, _a, _b, _c) in cd['ints']), \
                        "(GR-91)(iv) FAILS: collision set != interiors"
                    terms.append((term, yloc.collide(cd, mb)))
                    tdist[term] = tdist.get(term, 0) + 1
                if coll == cap - 6:
                    tight += 1
                sdist[s] = sdist.get(s, 0) + 1
                trip += 1
            # the packing bound is unchanged by the reformulation
            b = yloc.pack_bound(terms)
            assert b == yloc.pack_bound(yloc.coll_terms(specs, cds, mb)), \
                "(GR-91) FAILS: the reformulated packing bound moved"
            Bdist[b] = Bdist.get(b, 0) + 1
            best = b if best is None else min(best, b)
        minB[best] = minB.get(best, 0) + 1
    print(f"  (i)-(iv) asserted at {trip} (inventory shape, matching, "
          f"proper chunk) triples, colouring-free: 0 failures, "
          f"{tight} at equality `coll = cap - 6`")
    print(f"      slack `s_M(S)` distribution (every value EVEN): "
          f"{dict(sorted(sdist.items()))}")
    print(f"      positive terms, by value: {dict(sorted(tdist.items()))} "
          f"-- each equal to its chunk's demand r(S)")
    print(f"  B(M) over all (shape, M): {dict(sorted(Bdist.items()))}")
    print(f"  min_M B(M) per shape:     {dict(sorted(minB.items()))}")
    assert all(s % 2 == 0 for s in sdist), \
        "an odd slack survived the census"
    assert list(minB) == [0], \
        "(GR-64)(R2) FAILS on the inventory -- HEADLINE, a REFUTATION"
    print(f"  [GC-1] {round(time.time() - t0, 1)} s")


# ------------------------------------------------ [GC-2] --dem: (GR-92) -----

def leg_dem():
    """[GC-2] (GR-92): the demand classification and its census."""
    t0 = time.time()
    print("[GC-2] (GR-92) which chunks can demand anything at all")
    inv = inventory()
    prof = {}
    allprof = {}
    nchunk = 0
    ndem = 0
    per_shape = {}
    twocut = 0
    twocut_ok = 0
    for (_tag, n, specs) in inv:
        ctx = yloc.shape_ctx(specs, n)
        d = 0
        for cd in ctx['cds']:
            if cd['improper']:
                continue
            (z, exc, cap, r, ch, part, nW) = chunk_prof(specs, cd)
            nchunk += 1
            allprof[(z, exc)] = allprof.get((z, exc), 0) + 1
            # (i) the capacity floor, with (GR-32)(ii)'s chord refinement
            chords = {}
            for (_v, _b1, _b2, b3) in cd['ints']:
                chords[b3] = chords.get(b3, 0) + 1
            chex = [specs[b][2] - 2 for b, k in chords.items() if k == 2]
            if part == 0:
                assert nW == n, "no exits but W_S proper"
                assert cap == 6 + sum(4 - e for e in chex), \
                    "(GR-92)(i) FAILS: the improper capacity identity"
            else:
                assert nW < n, "an exit with W_S spanning"
                assert cap >= 7 + sum(4 - e for e in chex), \
                    "(GR-92)(i) FAILS: (GR-32)(ii)'s chord-refined floor"
            assert z >= 2, "(GR-92)(i) FAILS: a proper chunk with z < 2"
            if r >= 1:
                ndem += 1
                d += 1
                # (ii) the six profiles, and r <= 2
                assert r <= 2, "(GR-92)(ii) FAILS: a demand above 2"
                assert (z, exc) in ((2, 3), (3, 1), (3, 2),
                                   (4, 0), (4, 1), (5, 0)), \
                    "(GR-92)(ii) FAILS: an unclassified demanding profile"
                assert (r == 2) == ((z, exc) in ((3, 1), (4, 0))), \
                    "(GR-92)(ii) FAILS: the r = 2 profile list"
                prof[(z, exc, ch, part, r)] = \
                    prof.get((z, exc, ch, part, r), 0) + 1
                # (iii) the two-cut normal form
                if part == 2 and ch == 0:
                    twocut += 1
                    WS = {v for i in cd['S'] for v in specs[i][:2]}
                    cutb = [i for i, (u, w, _L) in enumerate(specs)
                            if (u in WS) != (w in WS)]
                    assert (z, exc) == (2, 3), \
                        "(GR-92)(iii) FAILS: a 2-exit demand off (2, 3)"
                    assert len(cutb) == 2 and \
                        all(specs[i][2] == 2 for i in cutb), \
                        "(GR-92)(iii) FAILS: a 2-cut branch of length > 2"
                    assert sum(specs[i][2] - 2 for i in range(len(specs))
                               if i not in cd['S'] and i not in cutb) == 3, \
                        "(GR-92)(iii) FAILS: complement excess != 3"
                    twocut_ok += 1
                # (iv) a chord can only appear in a demand when it is long
                if ch >= 1:
                    assert sum(chex) >= (2 * ch + 1 if part == 0
                                        else 2 * ch + 2 - part), \
                        "(GR-92)(iv) FAILS: a short-chord demand"
        per_shape[d] = per_shape.get(d, 0) + 1
    print(f"  (i)-(iv) asserted at all {nchunk} proper chunks of the "
          f"4924-shape inventory: 0 failures")
    print(f"  proper-chunk (z, exc) profiles, all: "
          f"{dict(sorted(allprof.items()))}")
    print(f"  DEMANDING chunks (r >= 1): {ndem} of {nchunk}; profiles "
          f"(z, exc, chords, exits, r): {dict(sorted(prof.items()))}")
    print(f"  demanding chunks per shape: {dict(sorted(per_shape.items()))}")
    print(f"  (iii) 2-exit chordless demands: {twocut} of them, all "
          f"{twocut_ok} in the `(z, exc) = (2, 3)` two-cut normal form "
          f"with complement excess exactly 3")
    assert ndem > 0 and twocut > 0, "the census is vacuous"
    print(f"  [GC-2] {round(time.time() - t0, 1)} s")


# ------------------------------------------------- [GC-3] --tf: (GR-93) -----

def leg_tf():
    """[GC-3] (GR-93): the 2-factor criterion, exact against the landed
    `2^M` ground truth."""
    t0 = time.time()
    print("[GC-3] (GR-93) violation detection WITHOUT a chunk scan")
    inv = inventory()
    pairs = 0
    viol = 0
    cyc_hist = {}
    union_max = 0
    for (_tag, n, specs) in inv:
        ctx = yloc.shape_ctx(specs, n)
        cds = ctx['cds']
        canon = {cd['S'] for cd in cds}
        for mat in perfect_matchings(specs, cap=PM_CAP):
            mb = yloc.matb(specs, mat)
            gt = set()
            for cd in cds:
                if cd['improper']:
                    continue
                t = len(yloc.collide(cd, mb)) - cd['cap'] + 6
                if t > 0:
                    gt.add((cd['S'], t))
            cy = f_cycles(specs, n, mat)
            cyc_hist[len(cy)] = cyc_hist.get(len(cy), 0) + 1
            union_max = max(union_max, (1 << len(cy)) - 1)
            got = violated_2f(specs, n, mat, cy)
            assert got == gt, \
                "(GR-93) FAILS: the 2-factor criterion is not exact"
            for (S, _r) in got:
                assert S in canon, \
                    "(GR-93) FAILS: a constructed set outside the canonical " \
                    "chunk family"
            viol += len(gt)
            pairs += 1
    print(f"  the violated-chunk set found from the 2-factor `F = E \\ M` "
          f"alone EQUALS the `2^M` ground truth at all {pairs} "
          f"(inventory shape, matching) pairs: 0 disagreements, "
          f"{viol} violated (shape, M, chunk) triples")
    print(f"  every constructed branch set was in `gcap.two_ec_subsets`' "
          f"own family (so `is_chunk` agrees with the canonical predicate "
          f"wherever it matters)")
    print(f"  F-cycle counts c(F) over all (shape, M) pairs: "
          f"{dict(sorted(cyc_hist.items()))}; largest union search "
          f"{union_max} subsets (against `2^M` chunk masks, M up to "
          f"{max(len(s) for (_t, _n, s) in inv)})")
    print(f"  [GC-3] {round(time.time() - t0, 1)} s")


# ----------------------------------------------- [GC-4] --suff: (GR-94) -----

def leg_suff():
    """[GC-4] (GR-94): the two proven sufficient conditions, measured."""
    t0 = time.time()
    print("[GC-4] (GR-94) two PROVEN sufficient conditions for B(M) = 0")
    inv = inventory()
    n_ham = n_cyc = n_either = 0
    n_tot = 0
    cyc_hist = {}
    l5_hist = {}
    avoid_fail = 0
    ham_but_pos = 0
    cyc_but_pos = 0
    residual = []
    for (tag, n, specs) in inv:
        n_tot += 1
        mats = perfect_matchings(specs, cap=PM_CAP)
        l5_hist[len(long5(specs))] = l5_hist.get(len(long5(specs)), 0) + 1
        if avoid5_witness(specs, n, mats) is None:
            avoid_fail += 1
        cec = cyclic_edge_conn(specs, n)
        cyc_hist[cec] = cyc_hist.get(cec, 0) + 1
        hm = ham_witness(specs, n, mats)
        ok_c = (cec is None or cec >= 6) and \
            avoid5_witness(specs, n, mats) is not None
        if hm is not None:
            n_ham += 1
            # the theorem: this matching's bound must actually be 0
            if pack_of(specs, violated_2f(specs, n, hm)) != 0:
                ham_but_pos += 1
        if ok_c:
            n_cyc += 1
            w = avoid5_witness(specs, n, mats)
            if pack_of(specs, violated_2f(specs, n, w)) != 0:
                cyc_but_pos += 1
        if hm is not None or ok_c:
            n_either += 1
        else:
            residual.append((tag, n, specs))
    print(f"  (i) cyclic-edge-connectivity condition: {n_cyc} of {n_tot} "
          f"shapes have no cyclic edge cut below 6 AND a matching avoiding "
          f"every length-5 branch -- the theorem's witness verified "
          f"B(M) = 0 at every one ({cyc_but_pos} failures)")
    print(f"  (ii) Hamiltonian condition: {n_ham} of {n_tot} shapes carry a "
          f"Hamiltonian 2-factor whose complement avoids every length-5 "
          f"branch -- verified B(M) = 0 at every one ({ham_but_pos} "
          f"failures)")
    print(f"  (i) or (ii): {n_either} of {n_tot}; residual "
          f"{len(residual)} shapes rest on the general (GR-93) test")
    assert ham_but_pos == 0 and cyc_but_pos == 0, \
        "(GR-94) FAILS: a shape satisfying the hypothesis has B(M) > 0 -- " \
        "HEADLINE, the theorem is false"
    print(f"  cyclic edge connectivity over the inventory (None = no cyclic "
          f"edge cut): {dict(sorted(cyc_hist.items(), key=str))}")
    print(f"  length-5 branch count per shape: {dict(sorted(l5_hist.items()))}"
          f"; shapes with NO matching avoiding them: {avoid_fail} "
          f"(Plesnik 1972 predicts 0 for a 2-edge-connected cubic host)")
    assert avoid_fail == 0, \
        "a habitat shape whose every matching hits a length-5 branch -- " \
        "the Plesnik input needs its multigraph reading checked"
    # the residual is where the excess refinement is load-bearing
    rmin = {}
    for (_tag, n, specs) in residual:
        b, _w = min_B(specs, n, perfect_matchings(specs, cap=PM_CAP))
        rmin[b] = rmin.get(b, 0) + 1
    print(f"  residual shapes' min_M B(M) (by the general test): "
          f"{dict(sorted(rmin.items()))}")
    assert not rmin or list(rmin) == [0], \
        "(GR-64)(R2) FAILS on the residual -- HEADLINE"
    print(f"  [GC-4] {round(time.time() - t0, 1)} s")


# ------------------------------------------------ [GC-5] --big: (GR-95) -----

def leg_big8():
    """[GC-5a] (GR-95)(a) = (GR-64)(R1) at the complete `n_hub = 8`
    habitat stratum.  Split from [GC-5b] for the 600 s foreground
    budget (README's *Two invocations do not fit* row)."""
    t0 = time.time()
    print("[GC-5a] (GR-95)(a) = (GR-64)(R1) at n_hub = 8, by (GR-93)")

    # (a) the COMPLETE n_hub = 8 habitat stratum
    t1 = time.time()
    pool, nep = stratum8()
    tot = sum(len(ls) for (_h, ls) in pool)
    print(f"  (a) n_hub = 8: {len(pool)} of `cubic_iso_classes(8)`'s 20 "
          f"hub-multigraph classes carry a habitat length assignment, x "
          f"{nep} excess profiles -> {tot} habitat shapes (AGLU's landed "
          f"count 39689)  [{round(time.time() - t1, 1)} s to build]")
    assert tot == 39689, "the n_hub = 8 habitat count moved"
    dist8 = {}
    worst8 = []
    ham8 = 0
    for (hedges, lens_ok) in pool:
        # every structure below is length-INDEPENDENT: computed once
        base = [(u, w, 2) for (u, w) in hedges]
        mats = perfect_matchings(base, cap=PM_CAP)
        cyc = [f_cycles(base, 8, mat) for mat in mats]
        for lens in lens_ok:
            specs = tuple((u, w, L) for (u, w), L in zip(hedges, lens))
            best = None
            for mat, cy in zip(mats, cyc):
                b = pack_of(specs, violated_2f(specs, 8, mat, cy))
                best = b if best is None else min(best, b)
                if best == 0:
                    break
            dist8[best] = dist8.get(best, 0) + 1
            if best > 0:
                worst8.append((hedges, lens, best))
            if ham_witness(list(specs), 8, mats) is not None:
                ham8 += 1
    print(f"      min_M B(M) over all {tot} shapes: "
          f"{dict(sorted(dist8.items()))}")
    print(f"      shapes with min_M B(M) >= 1 (a (GR-64)(R2) refutation at "
          f"n_hub = 8): {len(worst8)}")
    assert list(dist8) == [0], \
        f"the n_hub = 8 verdict MOVED: {worst8[:2]} -- HEADLINE"
    print(f"      shapes covered by the PROVEN Hamiltonian condition "
          f"(GR-94)(ii): {ham8} of {tot} -- so (R2) is not merely measured "
          f"but PROVEN at every one of them")
    print(f"      so the smallest refuting witness is NOT at n_hub <= 8: "
          f"(R2) holds at every shape of the exhaustive n_hub <= 6 "
          f"inventory and of the exhaustive n_hub = 8 stratum")
    print(f"  [GC-5a] {round(time.time() - t0, 1)} s")


def leg_bigp():
    """[GC-5b] (GR-95)(b)-(c) = (GR-64)(R1) at the Petersen family and at
    the named large shapes."""
    t0 = time.time()
    print("[GC-5b] (GR-95)(b)-(c) = (GR-64)(R1) at n_hub = 10 .. 40, "
          "by (GR-93)")

    # (b) the Petersen graph's whole habitat family
    t1 = time.time()
    fam = petersen_family()
    nep = len(excess_profiles(15, 6))
    print(f"  (b) Petersen (n_hub = 10, girth 5, cyclically 5-edge-connected, "
          f"NOT Hamiltonian): {len(fam)} habitat length assignments of "
          f"{nep} excess profiles -- the {nep - len(fam)} rejected are "
          f"EXACTLY those piling all 6 excess units onto one hub's star "
          f"(asserted both ways), since Petersen's only 3-edge-cuts are "
          f"its vertex stars and (GR-25) then wants exc >= 1 outside "
          f"[{round(time.time() - t1, 1)} s]")
    distP = {}
    hamP = 0
    wits = petersen_witnesses()
    crit = 0
    for specs in fam:
        mats = perfect_matchings(list(specs), cap=PM_CAP)
        assert len(mats) == 6, "the Petersen matching count moved"
        if ham_witness(list(specs), 10, mats) is not None:
            hamP += 1
        best = None
        for mat in mats:
            cy = f_cycles(list(specs), 10, mat)
            # the classical structure: every 2-factor of Petersen is two
            # disjoint pentagons, so `M` is the 5 branches between them
            assert len(cy) == 2 and all(len(h) == 5 for (h, _b) in cy), \
                "a Petersen 2-factor that is not two pentagons"
            b = pack_of(specs, violated_2f(list(specs), 10, mat, cy))
            # (GR-95)(ii): the LOCAL criterion at Petersen
            ok = (not (set(long5(list(specs))) & set(mat))) and \
                all(sum(specs[i][2] - 2 for i in bs) >= 1 for (_h, bs) in cy)
            assert (b == 0) == ok, \
                "(GR-95)(ii) FAILS: the Petersen local criterion"
            crit += 1
            best = b if best is None else min(best, b)
        distP[best] = distP.get(best, 0) + 1
    print(f"      min_M B(M): {dict(sorted(distP.items()))}; shapes covered "
          f"by the Hamiltonian condition (GR-94)(ii): {hamP} "
          f"(Petersen has no Hamiltonian cycle, so 0 is the prediction)")
    print(f"  (GR-95) **(GR-64)(R2) is REFUTED**: {len(wits)} of {len(fam)} "
          f"habitat length assignments of the Petersen graph carry "
          f"`min_M B(M) >= 1` -- at EVERY one of their 6 matchings the "
          f"packing bound is positive, so no anchor matching is "
          f"collision-slack")
    assert hamP == 0, "a Hamiltonian 2-factor of the Petersen graph"
    assert len(wits) == 180 and distP == {0: 36680, 1: 180}, \
        "the (GR-95) refutation count MOVED -- HEADLINE"
    lm = {}
    for (specs, _b) in wits:
        key = tuple(sorted((L for (_u, _w, L) in specs), reverse=True))
        key = tuple(L for L in key if L > 2)
        lm[key] = lm.get(key, 0) + 1
    print(f"  (GR-95)(ii) the LOCAL criterion at Petersen -- `B(M) = 0` iff "
          f"the length-5 branch (if any) is in the 2-factor AND both "
          f"pentagons of the 2-factor carry excess -- asserted at all "
          f"{crit} (Petersen habitat shape, matching) pairs: 0 failures")
    print(f"      the witnesses' long-branch length multisets: "
          f"{dict(sorted(lm.items(), key=str))} -- every witness spreads its "
          f"6 units of excess over 3 or 4 branches, exactly one of them "
          f"length 5")

    # (c) W5 and the eight necklaces
    print(f"  (c) the named large shapes, out of reach for the `2^M` chunk "
          f"scan:")
    for (tag, n, specs) in big_named():
        t1 = time.time()
        mats = perfect_matchings(specs, cap=PM_CAP)
        assert len(mats) < PM_CAP, f"{tag}: matching cap {PM_CAP} BOUND"
        b, wit = min_B(specs, n, mats)
        cy = f_cycles(specs, n, wit)
        print(f"      {tag:9s} n_hub = {n:2d}, branches = {len(specs):2d}, "
              f"{len(mats):4d} matchings (cap {PM_CAP} NOT bound): "
              f"min_M B(M) = {b}, witness 2-factor has {len(cy)} cycles "
              f"[{round(time.time() - t1, 1)} s]")
        assert b == 0, f"(GR-64)(R2) REFUTED at {tag} -- HEADLINE"
    print(f"  CAP DISCLOSED: the chunk side is EXHAUSTIVE and uncapped "
          f"everywhere above -- (GR-93) replaces `gcap.two_ec_subsets`' "
          f"`2^M` scan by a `2^c(F)` union search, so W5 (`E = 24`) and the "
          f"necklaces (`E >= 45`), disclosed out of reach by (GR-64), are "
          f"now measured. What remains capped: `n_hub = 10` beyond the "
          f"Petersen graph and `n_hub >= 12` beyond the four necklace "
          f"families have NO search run (no enumerator), and "
          f"`gorient.perfect_matchings`' cap is disclosed as NOT bound "
          f"at every shape above.")
    print(f"  [GC-5b] {round(time.time() - t0, 1)} s")


# ------------------------------------------------ [GC-6] --wit: (GR-95) -----

def leg_wit():
    """[GC-6] (GR-95): the refutation re-verified two independent ways."""
    t0 = time.time()
    print("[GC-6] (GR-95) the (GR-64)(R2) counterexamples, re-verified")
    wits = petersen_witnesses()
    print(f"  {len(wits)} witnesses (deterministic, no rng)")
    mech = {}
    disagree = 0
    nothab = 0
    bvals = {}
    for (specs, b) in wits:
        ctx = yloc.shape_ctx(specs, 10)          # the LANDED 2^15 chunk scan
        cds = ctx['cds']
        mats = perfect_matchings(list(specs), cap=PM_CAP)
        per = []
        for mat in mats:
            mb = yloc.matb(specs, mat)
            per.append(yloc.pack_bound(yloc.coll_terms(specs, cds, mb)))
            for cd in cds:
                if cd['improper']:
                    continue
                if len(yloc.collide(cd, mb)) - cd['cap'] + 6 > 0:
                    key = (cd['z'], cd['exc'], chunk_prof(specs, cd)[4])
                    mech[key] = mech.get(key, 0) + 1
        if min(per) != b:
            disagree += 1
        bvals[min(per)] = bvals.get(min(per), 0) + 1
        # the CANONICAL habitat certificate, not merely (GR-25)
        if class_shape(list(specs)) is None:
            nothab += 1
    print(f"  (i) the landed `2^M` chunk scan (`gcap.two_ec_subsets` via "
          f"`gorient.prep_shape`) reproduces `min_M B(M)` at every witness: "
          f"{disagree} disagreements with the (GR-93) route; values "
          f"{dict(sorted(bvals.items()))}")
    assert disagree == 0, "(GR-95) FAILS: the two routes disagree"
    print(f"  (ii) `gridcol.class_shape` -- the CANONICAL habitat "
          f"certificate, `kslide.no_rigid_branch_union` with an exact "
          f"matroid rank inside -- certifies all {len(wits)} witnesses: "
          f"{nothab} rejections")
    assert nothab == 0, \
        "(GR-95) FAILS: a witness is not a habitat shape by the canonical " \
        "oracle -- HEADLINE"
    print(f"  (iii) the violated chunks, by (z, exc, chords): "
          f"{dict(sorted(mech.items()))} -- exactly TWO mechanisms, both "
          f"with demand r = 1: a zero-excess PENTAGON of the 2-factor "
          f"(z = 5, exc = 0, chordless) and `E(G) minus the length-5 "
          f"branch` when that branch is in `M` (z = 2, exc = 3, one chord)")
    assert set(mech) == {(5, 0, 0), (2, 3, 1)}, \
        "(GR-95)(iii) FAILS: a third mechanism"
    print(f"  [GC-6] {round(time.time() - t0, 1)} s")


# ------------------------------------------------ [GC-7] --dfg: (GR-95) -----

def leg_dfg():
    """[GC-7] (GR-95)(iv): `d_adm` and `d_fg` at the witnesses -- the
    E1(iv)/E2 detector, and the (a') by-product."""
    t0 = time.time()
    print("[GC-7] (GR-95)(iv) the witnesses' d_adm and d_fg, exactly")
    wits = petersen_witnesses()
    dadm = {}
    dfg = {}
    pairs = {}
    fired = 0
    inf = 0
    for (specs, b) in wits:
        ctx = yloc.shape_ctx(specs, 10)
        cds = ctx['cds']
        mats = perfect_matchings(list(specs), cap=PM_CAP)
        zs = yloc.adm_zs(specs, 10, ctx['binc'])
        da = yloc.d_adm_exact(specs, 10, ctx['binc'], ctx['oidx'],
                              ctx['edges'], ctx['allverts'], ctx['hm'],
                              zs, mats)
        if da is None:
            inf += 1
            continue
        best = None
        for z in zs:
            if not yloc.is_balanced_z(specs, ctx['oidx'], z):
                continue
            m, c = z_to_map(specs, 10, ctx['binc'], z)
            col = cm_colouring(specs, m, c)
            if not admissible(ctx['edges'], ctx['allverts'], ctx['hm'], col):
                continue
            if not yloc.good_z(specs, cds, z):
                continue
            for mat in mats:
                d = yloc.dist_of(specs, 10, m, mat)
                if best is None or d < best:
                    best = d
        dadm[da] = dadm.get(da, 0) + 1
        dfg[best] = dfg.get(best, 0) + 1
        pairs[(da, best)] = pairs.get((da, best), 0) + 1
        if b > da:
            fired += 1
    print(f"  d_adm (exhaustive z-cube, NO deviation cap): "
          f"{dict(sorted(dadm.items()))}; d_fg: "
          f"{dict(sorted(dfg.items(), key=str))}")
    assert inf == 0, "d_adm = infinity at a witness -- E1 clause (v) FIRES"
    print(f"  E1(iv)/E2 detector -- witnesses with `min_M B(M) > d_adm` "
          f"(which would prove `d_adm < d_fg`): {fired}")
    assert fired == 0, \
        "(a') REFUTED at a (GR-95) witness -- HEADLINE, E2's refutation " \
        "branch"
    print(f"  by-product, reported not developed: (d_adm, d_fg) pairs "
          f"{dict(sorted(pairs.items(), key=str))} -- `d_fg = d_adm` at "
          f"every witness, so (a') HOLDS at all {len(wits)} of them; this "
          f"is NEW territory for (a') ((GR-58)'s census is n_hub <= 6 plus "
          f"NKp(6)/NK55(6)), and it is a corroboration, not a proof")
    assert all(a == f for (a, f) in pairs), \
        "(a') FAILS at a witness -- HEADLINE"
    print(f"  [GC-7] {round(time.time() - t0, 1)} s")


# ------------------------------------------------------- [GC-8] --adv ------

def leg_adv():
    """[GC-6] F13 falsification controls."""
    t0 = time.time()
    print(f"[GC-8] F13 controls  (seed {C_SEED + 8})")
    rng = random.Random(C_SEED + 8)
    inv = inventory()
    samp = [s for s in inv if s[0] != 'pool'] + \
        rng.sample([s for s in inv if s[0] == 'pool'], 400)

    # (1) MUST-FIRE: the parity collapse is a THEOREM about matchings, not
    #     an artefact of the term being positive -- a NON-matching
    #     selection (one branch per hub, from a seeded perturbation of a
    #     matching) must produce an ODD slack somewhere.
    odd = 0
    for (_tag, n, specs) in samp[:80]:
        ctx = yloc.shape_ctx(specs, n)
        binc = branches_at(specs, n)
        for mat in perfect_matchings(specs, cap=PM_CAP)[:3]:
            mb = yloc.matb(specs, mat)
            v = rng.randrange(n)
            bad = dict(mb)
            bad[v] = rng.choice([i for i in binc[v] if i != mb[v]])
            for cd in ctx['cds']:
                if cd['improper']:
                    continue
                if slack_of(cd, bad) % 2 == 1:
                    odd += 1
    print(f"  (1) slack parity off a matching: {odd} odd slacks under a "
          f"seeded one-hub perturbation (must be > 0 -- otherwise "
          f"(GR-91)(ii) is vacuous)")
    assert odd > 0, "control (1) did not fire"

    # (2) MUST-FIRE: (GR-93) restricted to PROPER unions -- dropping the
    #     spanning case `W = V(G)` -- must MISS a violation.  This is the
    #     mechanism behind one of the two (GR-95) witness families
    #     (`E(G) minus the length-5 branch`), so it must not be optional.
    missed = 0
    for (_tag, n, specs) in samp:
        for mat in perfect_matchings(specs, cap=PM_CAP):
            full = violated_2f(specs, n, mat)
            if not full:
                continue
            cy = f_cycles(specs, n, mat)
            proper = set()
            for msk in range(1, (1 << len(cy)) - 1):
                W = set()
                for j in range(len(cy)):
                    if msk >> j & 1:
                        W |= cy[j][0]
                EW = [i for i, (u, w, _L) in enumerate(specs)
                      if u in W and w in W]
                intM = [i for i in EW if i in set(mat)]
                for nc in (0, 1, 2):
                    for C in itertools.combinations(intM, nc):
                        ends = [v for i in C for v in specs[i][:2]]
                        if len(set(ends)) != len(ends):
                            continue
                        S = tuple(i for i in EW if i not in C)
                        if len(S) == len(specs) or not is_chunk(specs, S):
                            continue
                        if stat_of(specs, S)[2] >= 1:
                            proper.add((S, stat_of(specs, S)[2]))
            if full - proper:
                missed += 1
    print(f"  (2) proper-union search only (the spanning case `W = V` "
          f"dropped): misses a violation at {missed} (shape, M) pairs "
          f"(must be > 0 -- the spanning case is load-bearing)")
    assert missed > 0, "control (2) did not fire"

    # (3) MUST-FIRE: dropping the chord option from (GR-93) must MISS a
    #     violation somewhere (the `C != empty` branch is load-bearing).
    chmiss = 0
    for (_tag, n, specs) in samp:
        for mat in perfect_matchings(specs, cap=PM_CAP):
            full = violated_2f(specs, n, mat)
            # chord-free variant: the same search with `C` forced empty
            cy = f_cycles(specs, n, mat)
            got = set()
            for msk in range(1, 1 << len(cy)):
                W = set()
                for j in range(len(cy)):
                    if msk >> j & 1:
                        W |= cy[j][0]
                EW = tuple(i for i, (u, w, _L) in enumerate(specs)
                           if u in W and w in W)
                if len(EW) == len(specs) or not is_chunk(specs, EW):
                    continue
                z, _e, r, _i = stat_of(specs, EW)
                if r >= 1:
                    got.add((EW, r))
            if full - got:
                chmiss += 1
    print(f"  (3) chord-free search only: misses a violation at {chmiss} "
          f"(shape, M) pairs (must be > 0)")
    assert chmiss > 0, "control (3) did not fire"

    # (4) NEGATIVE CONTROL: the demand `r` must be a NON-trivial predicate
    #     -- there must be proper chunks with r <= 0 and proper chunks
    #     with r >= 1 in the same shape, or (GR-92) is empty.
    both = 0
    for (_tag, n, specs) in samp:
        ctx = yloc.shape_ctx(specs, n)
        rs = {chunk_prof(specs, cd)[3] >= 1 for cd in ctx['cds']
              if not cd['improper']}
        if rs == {True, False}:
            both += 1
    print(f"  (4) the demand predicate is non-trivial at {both} of "
          f"{len(samp)} sampled shapes (must be > 0)")
    assert both > 0, "control (4) did not fire"

    # (5) MUST-FIRE: the Hamiltonian hypothesis needs the length-5
    #     proviso -- a Hamiltonian 2-factor whose complement DOES contain
    #     a length-5 branch must, somewhere, have B(M) > 0.
    fired = 0
    for (_tag, n, specs) in samp:
        if not long5(specs):
            continue
        bad = set(long5(specs))
        for mat in perfect_matchings(specs, cap=PM_CAP):
            if not (bad & set(mat)):
                continue
            if len(f_cycles(specs, n, mat)) != 1:
                continue
            if pack_of(specs, violated_2f(specs, n, mat)) > 0:
                fired += 1
    print(f"  (5) Hamiltonian 2-factor WITH a length-5 branch in the "
          f"matching: B(M) > 0 at {fired} (shape, M) pairs (must be > 0 -- "
          f"otherwise (GR-94)(ii)'s proviso is decoration)")
    assert fired > 0, "control (5) did not fire"

    # (6) NEGATIVE CONTROL on the (GR-95) refutation: the counterexample is
    #     a property of the LENGTH ASSIGNMENT, not of the Petersen graph --
    #     the same graph must carry habitat assignments with min_M B = 0.
    wits = {sp for (sp, _b) in petersen_witnesses()}
    zero = pos = 0
    for specs in petersen_family():
        b, _w = min_B(list(specs), 10, perfect_matchings(list(specs),
                                                        cap=PM_CAP))
        if b == 0:
            zero += 1
        else:
            pos += 1
            assert specs in wits, "a witness outside the memoized family"
    print(f"  (6) the refutation is a property of the LENGTH ASSIGNMENT, "
          f"not of the graph: the Petersen graph carries {zero} habitat "
          f"assignments with min_M B = 0 and {pos} with min_M B >= 1 "
          f"(both must be > 0)")
    assert zero > 0 and pos > 0, "control (6) did not fire"

    # (7) MUST-AGREE: `yloc.good_z` -- the (GR-56)(iii) criterion this pass
    #     uses for the (a') by-product -- against the landed combinatorial
    #     evaluator `gorient.fully_good_scan`, at a seeded sample of
    #     witnesses, over their WHOLE admissible cube.  (yloc asserts this
    #     on the inventory; the by-product needs it at n_hub = 10.)
    checked = 0
    for (specs, _b) in rng.sample(petersen_witnesses(), 3):
        ctx = yloc.shape_ctx(specs, 10)
        for z in yloc.adm_zs(specs, 10, ctx['binc']):
            m, c = z_to_map(specs, 10, ctx['binc'], z)
            col = cm_colouring(specs, m, c)
            gz = yloc.good_z(specs, ctx['cds'], z)
            gl = fully_good_scan(ctx['hm'], None, ctx['tec_cf'], ctx['lens'],
                                 branch_stats(ctx['hm'], col, 'A'))
            assert gz == gl, \
                "(GR-56)(iii)-in-z disagrees with fully_good_scan at " \
                "n_hub = 10 -- the (a') by-product's evaluator is unsound"
            checked += 1
    print(f"  (7) `good_z` == `gorient.fully_good_scan` at all {checked} "
          f"admissible colourings of 3 seeded witnesses (the (a') "
          f"by-product's evaluator, cross-checked at n_hub = 10)")
    assert checked > 0, "control (7) is vacuous"
    print(f"  [GC-8] {round(time.time() - t0, 1)} s")


# --------------------------------------------------------------- main -------

def main():
    args = sys.argv[1:]
    legs = {'--slack': leg_slack, '--dem': leg_dem, '--tf': leg_tf,
            '--suff': leg_suff, '--big8': leg_big8, '--bigp': leg_bigp,
            '--wit': leg_wit, '--dfg': leg_dfg, '--adv': leg_adv}
    if not args or args[0] == '--validate':
        order = ['--slack', '--dem', '--tf', '--suff', '--big8', '--bigp',
                 '--wit', '--dfg', '--adv']
    else:
        order = args
    print(f"GCOLL -- (GR-91)-(GR-96), Steps G110-G115   (C_SEED = {C_SEED})")
    for a in order:
        assert a in legs, f"unknown mode {a}"
        legs[a]()
        print()


if __name__ == '__main__':
    main()
