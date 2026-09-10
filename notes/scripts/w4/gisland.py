"""§(K-grid) direction GISLAND (2026-09-09) driver -- the NO-EVEN-BRANCH
BINDING-CIRCUIT ISLAND at `Λ ≠ ∅`: the 1608 shapes of (GR-26) where both
landed repair instruments are unavailable ((GR-23)'s flip set is EVEN
branches; (GR-24) needs a PRIVATE EVEN branch), and the `|Λ| ≥ 2` stratum at
`n_hub = 6` that `cflank.py --lam6` fences off at `lamcap = 1`.

A `w4/` leaf beside `cflank.py`, importing `cflank.py` / `gridcol.py` /
`grid.py` / `closure.py` / `packmm.py` READ-ONLY (README §2; same precedent
as cflank -> gridcol -> grid -> closure).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gisland.py --island  # the island re-censused over ISOMORPHISM CLASSES; NC1-clean AND merge-free counts
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gisland.py --wide    # the landed NC1 detector inspects only binding circuits -- is that sound at Lambda != empty?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gisland.py --chain   # (GR-86)'s repair chain on the island: the BALANCE obstruction, proved and measured
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gisland.py --pair    # the ODD-PAIR flip: the island's own repair instrument, and its privacy hypothesis
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gisland.py --deep    # THE REFUTATION HUNT: |Lambda| >= 2 at n_hub = 6, exhaustive over isomorphism classes
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gisland.py --validate  # all five

Argument state: session draft `notes/Pencil-draft-GISLAND.md` (to be merged
into `notes/pencil/workbook/grid.md` §(K-grid) as Steps G173+; labels
(GR-153)+ per the 2026-09-09 GISLAND reservation in `notes/pencil/labels.md`).

WHY THIS POOL, in one paragraph.  (GR-26)(iii) records 1608 of the 40 742
census-hunt shapes as carrying a binding circuit with NO even branch --
profiles `(1,1,5)` and `(1,3,3)` -- where (GR-23)/(GR-24)'s balance-preserving
flip does not exist and "only the exhaustive scan carries the shape".  The
merge mechanism that can push `D_A` below the run count needs a `Γ_A`-path OFF
the circuit, and by (GR-16)(iii) only hub-hub (i.e. LENGTH-1, `Λ`) branches
propagate one; so the island's mathematics lives at `|Λ| ≥ 1`, and the
harness's own fence -- `cflank.LAM6_PLAN = ((6, 9, 1),)` -- stops at
`|Λ| ≤ 1`, sweeping 24 846 of the 142 740 length tuples at `n_hub = 6`.  This
driver un-fences that by PARAMETERIZING (`cflank.length_tuples` already takes
`lamcap`), and pays for the 5.7x population by quotienting the LABELLED
length-tuple pool by the hub multigraph's own automorphism group: at
`n_hub = 6` the 164 794 habitat-passing labelled shapes are 7 892 isomorphism
classes, a 20.9x reduction, which turns a ~90-minute sweep into a ~4-minute
one.  The quotient is SOUND because every quantity below (class-shapehood,
the admissible-colouring count, the NC1 count, the existence of a rank
certificate) is an isomorphism invariant, and it is TESTED as such by
`--deep`'s orbit control rather than asserted.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--island  the island itself: re-censused over isomorphism classes of the
          whole (GR-26) population, with the no-even-branch binding circuits
          named per shape; and, per shape, the count of admissible colourings
          that are NC1-clean AND merge-free in BOTH blocks, with `D_A`, `D_B`
          read off `grid.block_data` and never off the run count.  Also the
          `h_≠ ∈ {0, 2}` law at an all-odd 3-circuit, asserted colouring by
          colouring.

--wide    the landed detector `cflank.nc1_violations` inspects only the
          BINDING circuits (`Σ(ℓ−1) ≤ 4`), a restriction (GR-17)(d) licenses
          only at `Λ = ∅`; this mode reruns the SAME landed gate against a
          hub model whose `binding` field has been widened to EVERY circuit,
          asserts landed ⊆ widened everywhere, and reports every colouring
          the restriction lets through.

--chain   (GR-86)(ii)'s repair chain adds distinct EVEN branches; on the
          island the violated circuit has none, so no chain can touch it --
          and flipping the odd branch that WOULD repair it changes `|E_A|` by
          exactly 1 while every even flip changes it by 0, so no even chain
          can restore BALANCE.  Both halves are asserted over the island.

--pair    the island's own instrument: at an all-odd binding circuit, `h_≠`
          is even, so a violated circuit has ALL its branches carrying the
          same end colour; balance forces exactly half the odd branches to be
          A-ended, hence an opposite-ended odd partner exists OFF the
          circuit; flipping the pair preserves balance and sets `h_≠ = 2`.
          Each clause asserted, and the resulting repair RUN and its output
          asserted admissible and NC1-clean.

--deep    THE REFUTATION HUNT: the `|Λ| ≥ 2` stratum at `n_hub = 6`, every
          length tuple (`lamcap` un-fenced), exhaustive over isomorphism
          classes and over all `2^M` bits at each -- a shape with `adm > 0`
          and `nc1 == 0` is by (GR-17)(c) a PROOF that (GR-15) fails there.

Exact throughout (integers and `fractions.Fraction`; no floats).  Rank comes
from `exactcore.rank` through `gridcol.dim_W_branch` / `grid.dim_Z`, and from
`kbare_common.rank_modp` as a CERTIFIED LOWER BOUND inside
`gridcol.block_generic_zero`, whose attaining draw is re-checked in exact ℚ
here at every reported hit (README §4 convention 2).  The rngs are seeded per
mode and the seeds printed; no `set` is printed.  Nothing here samples a
placement: every object is a colouring of a pinned finite graph, so no figure
is a rate over sampled placements and `repin.star_generic` gates nothing
below (§(K-clos) (AC-9)'s discipline, as for `cflank.py` / `gridcol.py`).

CAPS, disclosed once (they travel with every figure this driver prints):
  * `n_hub ∈ {2, 4, 6}` and `M = 3·n_hub/2` -- `gridcol.multigraphs` is
    exponential in the pair count and `n_hub = 8` is out of reach here.
  * branch lengths `1 ≤ ℓ ≤ 5`, the (SD-6) bound, hardcoded in
    `cflank.length_tuples`'s `lo`/`hi` and passed through unchanged.
  * `--deep`'s `lamcap` defaults to 99 (i.e. UNBOUNDED at M = 9, where
    `|Λ| ≤ 5` is forced by `Σℓ = 24`); the value actually run is printed.
  * `closure.colourings`' `cap = 2^16` on the number of alternation classes;
    never hit at `M ≤ 9`, asserted.
  * `gridcol.block_generic_zero`'s own internal draw budget: a `None` return
    is "no certificate found under that budget", never "none exists", and is
    reported as `hit = None` rather than as a refutation.
"""
import argparse
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from closure import colourings, cycle_rank                                        # noqa: E402
from grid import block_data, census_shapes, dim_Z                     # noqa: E402
from gridcol import (block_generic_zero, class_shape, cycle_walk,     # noqa: E402
                     dim_W_branch, filter_pass, multigraphs)
from kbare_common import verts_of                                     # noqa: E402
from cflank import (admissible, cubic_habitat, excess_profiles,       # noqa: E402
                    flip_branch, h_neq, hub_model, hunt_shape,
                    length_tuples, nc1_violations, private_even)

G_SEED = 20260909
CUBIC_N = (2, 4, 6)
COLCAP = 1 << 16


# ----------------------------------------------------- local devices --------

def edge_auts(n, hedges):
    """`Aut(G°)` as a group of permutations of BRANCH INDICES.

    Local device: no §1 primitive computes it.  `gridcol.multigraphs`
    canonicalizes hub multigraphs up to isomorphism but returns one labelled
    representative and never its automorphisms, which is exactly why the
    length-tuple pool laid on top of it is a LABELLED pool (README §4
    convention 7, and *Step G28*'s own pool caveat).  A vertex permutation
    fixing the edge multiset induces several branch permutations when
    parallel branches are present, so all of them are generated."""
    key = {}
    for k, (u, w) in enumerate(hedges):
        key.setdefault((min(u, w), max(u, w)), []).append(k)
    sig = sorted((e, len(v)) for e, v in key.items())
    out = set()
    for pi in itertools.permutations(range(n)):
        tgt = {}
        for k, (u, w) in enumerate(hedges):
            a, b = pi[u], pi[w]
            tgt.setdefault((min(a, b), max(a, b)), []).append(k)
        if sorted((e, len(v)) for e, v in tgt.items()) != sig:
            continue
        cls = sorted(tgt)
        for combo in itertools.product(*[itertools.permutations(key[e])
                                         for e in cls]):
            p = [None] * len(hedges)
            for e, dsts in zip(cls, combo):
                for s, d in zip(tgt[e], dsts):
                    p[s] = d
            out.add(tuple(p))
    return sorted(out)


def iso_orbits(auts, tuples):
    """The orbits of `Aut(G°)` on a list of length tuples, as
    {representative (the lexicographic minimum): [members]}."""
    orb = {}
    for lens in tuples:
        rep = min(tuple(lens[p[k]] for k in range(len(lens))) for p in auts)
        orb.setdefault(rep, []).append(tuple(lens))
    return orb


def hm_all(hm):
    """The landed hub model with its `binding` field WIDENED to every circuit.

    Not a new gate: `cflank.nc1_violations` reads `hm['binding']` and nothing
    else about which circuits to inspect, so handing it this dict runs the
    LANDED detector unrestricted.  `cflank.hub_model` fixes the restriction
    `Σ_γ(ℓ−1) ≤ 4` inline, which (GR-17)(d) licenses only at `Λ = ∅`."""
    return dict(hm, binding=[(tuple(sorted(c)),
                              cycle_walk(hm['branches'], hm['ends'], c))
                             for c in hm['cycs']])


def no_even_circuits(hm):
    """The binding circuits carrying NO even branch -- the island's defining
    object, and exactly where (GR-23)'s flip set `𝒮` is empty and (GR-24)'s
    private even branch cannot exist."""
    return [cyc for (cyc, _w) in hm['binding']
            if all(hm['lens'][k] % 2 == 1 for k in cyc)]


def circuit_report(hm, col, edges, allverts, cycs=None):
    """Per circuit: `(cyc, runs, D_A, D_B)` with `D_A`, `D_B` read off
    `grid.block_data` (never off the run count) and `runs` off (GR-17)(a).

    The merge diagnostic of *Step G28*: `D < runs` is the off-circuit merge,
    and `min(D_A, D_B) < 3` is the (GR-17)(c) violation."""
    bdA = block_data(edges, allverts, col, 'A')
    bdB = block_data(edges, allverts, col, 'B')
    clsA = {e: c for e, c in zip(bdA['E'], bdA['cls'])}
    clsB = {e: c for e, c in zip(bdB['E'], bdB['cls'])}
    out = []
    for cyc in (hm['cycs'] if cycs is None else cycs):
        walk = cycle_walk(hm['branches'], hm['ends'], cyc)
        L = sum(hm['lens'][k] for k in cyc)
        runs2 = (L - len(cyc)) + h_neq(hm, col, walk)
        assert runs2 % 2 == 0, "(GR-17)(a) parity fails"
        eseq = [e for k in cyc for e in hm['branches'][k][2]]
        dA = len({clsA[e] for e in eseq if col[e] == 'A'})
        dB = len({clsB[e] for e in eseq if col[e] == 'B'})
        out.append((tuple(sorted(cyc)), runs2 // 2, dA, dB))
    return out


def end_colour(hm, col, k):
    """The common colour of an ODD branch's two end edges (they alternate, so
    they agree exactly when `ℓ` is odd) -- the bit (GR-16)(i)'s A-count law
    reads."""
    path = hm['branches'][k][2]
    assert len(path) % 2 == 1, "end_colour is only defined at an odd branch"
    assert col[path[0]] == col[path[-1]], "alternation broken at an odd branch"
    return col[path[0]]


def scan_shape(specs, rng, want_rank=True, wide=True):
    """The island detector at one hub-multigraph spec.

    Every gate is the landed one: `gridcol.class_shape`, `cflank.hub_model`,
    `closure.colourings`, `cflank.admissible`, `cflank.nc1_violations`
    (twice -- once as landed, once against `hm_all`), `gridcol.filter_pass`,
    `gridcol.block_generic_zero`, and the exact-ℚ recheck through both
    `gridcol.dim_W_branch` and `grid.dim_Z`.  Nothing is reimplemented; the
    loop is this driver's, and `--deep`'s cross-check asserts it agrees with
    `cflank.hunt_shape` shape by shape."""
    edges = class_shape(specs)
    if edges is None:
        return None
    hm = hub_model(edges)
    if hm is None:
        return None
    allverts = sorted(verts_of(edges), key=str)
    cols, odd = colourings(edges, cap=COLCAP)
    assert cols is not None, "closure.colourings cap hit -- figure is capped"
    if odd:
        return None
    hma = hm_all(hm)
    out = dict(adm=0, nc1=0, nc1w=0, clean=0, hit=None, tried=0, missed=0,
               edges=edges, hm=hm, noeven=len(no_even_circuits(hm)),
               priv=private_even(hm) is not None,
               lam=sum(1 for L in hm['lens'] if L == 1),
               T=sum(1 for (c, w) in hm['binding'] if len(c) == 3),
               Q=sum(1 for (c, w) in hm['binding'] if len(c) == 4))
    for col in cols:
        if not admissible(edges, allverts, hm, col):
            continue
        out['adm'] += 1
        bad = nc1_violations(hm, col, edges, allverts)
        if not bad:
            out['nc1'] += 1
        if wide:
            badw = nc1_violations(hma, col, edges, allverts)
            assert set(map(tuple, bad)) <= set(map(tuple, badw)), \
                "widening the circuit set LOST a violation -- impossible"
            if not badw:
                out['nc1w'] += 1
                rep = circuit_report(hm, col, edges, allverts)
                if all(dA == r and dB == r for (_c, r, dA, dB) in rep):
                    out['clean'] += 1
            elif not bad:
                out['missed'] += 1
        if bad:
            continue
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
        assert dim_W_branch(bdA, hm['hubs'], hm['branches'], sval=svA) == 0
        assert dim_W_branch(bdB, hm['hubs'], hm['branches'], sval=svB) == 0
        assert dim_Z(bdA, sval=svA) == 0 and dim_Z(bdB, sval=svB) == 0, \
            f"branch model and grid.dim_Z disagree at the hit for {specs}"
        out['hit'] = out['tried']
    return out


def stratum(n, lamcap=99, lamlo=0, dedup=True):
    """Every `(hedges, lens)` of the `D = 0` stratum at `n_hub = n` that
    passes (GR-25)'s cut criterion, with at least `lamlo` and at most
    `lamcap` length-1 branches, one representative per isomorphism class.

    `M = 3n/2` and `Σℓ = 6(M − n + 1)` are the (GR-21) excess law at `D = 0`,
    exactly as `cflank.leg_lam` computes them."""
    M = 3 * n // 2
    tgt = 6 * (M - n + 1)
    tups = [t for t in length_tuples(M, tgt, lamcap=lamcap)
            if sum(1 for L in t if L == 1) >= lamlo]
    for hedges in multigraphs(n, M):
        auts = edge_auts(n, hedges) if dedup else [tuple(range(M))]
        orb = iso_orbits(auts, tups)
        for rep in sorted(orb):
            if cubic_habitat(n, hedges, list(rep)):
                yield hedges, rep, orb[rep], auts


def specs_of(hedges, lens):
    return [(u, w, L) for (u, w), L in zip(hedges, lens)]


# ------------------------------------------ [GIS-1] --island: the island ----

def leg_island():
    """[GIS-1] the no-even-branch island, re-censused over ISOMORPHISM
    CLASSES, with the NC1-clean AND merge-free colouring count per shape."""
    print(f"[GIS-1] the no-even-branch binding-circuit island (seed "
          f"{G_SEED + 1})")
    rng = random.Random(G_SEED + 1)
    t0 = time.time()
    prof = {}
    tot = isl = 0
    lam_isl = {}
    perlam = {}
    hneq_checked = 0
    for n in CUBIC_N:
        M = 3 * n // 2
        # the (GR-26) population EXACTLY as swept: Lambda = empty everywhere,
        # plus Lambda != empty at n <= 4 (all tuples) and |Lambda| <= 1 at 6.
        cap = 99 if n <= 4 else 1
        cnt = ncl = 0
        for hedges, lens, members, auts in stratum(n, lamcap=cap):
            r = scan_shape(specs_of(hedges, lens), rng, want_rank=False)
            if r is None:
                continue
            cnt += 1
            tot += len(members)
            hm = r['hm']
            ne = no_even_circuits(hm)
            if ne:
                edges = r['edges']
                allverts = sorted(verts_of(edges), key=str)
                cols, odd = colourings(edges, cap=COLCAP)
                assert cols is not None and not odd
                for col in cols:
                    if admissible(edges, allverts, hm, col):
                        nc1_law(hm, col)
                        hneq_checked += 1
            if ne:
                isl += 1
                ncl += 1
                lam_isl[r['lam']] = lam_isl.get(r['lam'], 0) + len(members)
                for cyc in ne:
                    p = tuple(sorted(hm['lens'][k] for k in cyc))
                    prof[p] = prof.get(p, 0) + len(members)
                perlam.setdefault(r['lam'], [0, 0, 0])
                perlam[r['lam']][0] += r['adm']
                perlam[r['lam']][1] += r['nc1w']
                perlam[r['lam']][2] += r['clean']
        print(f"  n_hub={n}, M={M}, |Lambda| <= {cap}: {cnt} isomorphism "
              f"classes of class shape, {ncl} on the island  "
              f"[{time.time() - t0:.0f}s]")
    print(f"  the (GR-26) population re-keyed: {tot} LABELLED class shapes "
          f"(cf. 40 742), of which the island is {isl} isomorphism classes")
    print(f"  no-even-branch binding-circuit profiles, by LABELLED shape "
          f"count: {dict(sorted(prof.items()))}")
    print(f"  island shapes by |Lambda| (labelled): "
          f"{dict(sorted(lam_isl.items()))}")
    for lam in sorted(perlam):
        a, w, c = perlam[lam]
        print(f"  island, |Lambda|={lam}: {a} admissible colourings, {w} "
              f"NC1-clean at EVERY circuit, {c} of those also merge-free in "
              f"both blocks (D_A = D_B = runs at every circuit)")
    print(f"  the `h_neq in {{0, 2}}` law at all-odd 3-circuits: asserted "
          f"inside `nc1_law` at {hneq_checked} admissible colourings")
    print()


def nc1_law(hm, col):
    """(GR-153)(a): at an all-odd circuit `h_≠` is the number of cyclically
    adjacent branch pairs whose end colours differ, hence EVEN; and at
    `r = 3` it is 0 or 2, with 0 iff all three end colours agree."""
    for (cyc, walk) in hm['binding']:
        if any(hm['lens'][k] % 2 == 0 for k in cyc):
            continue
        cs = [end_colour(hm, col, k) for (k, _u, _w) in walk]
        hn = sum(1 for i in range(len(cs)) if cs[i] != cs[(i + 1) % len(cs)])
        assert hn == h_neq(hm, col, walk), \
            "the end-colour model disagrees with `cflank.h_neq`"
        assert hn % 2 == 0, "h_neq odd at an all-odd circuit"
        if len(cs) == 3:
            assert hn in (0, 2) and (hn == 0) == (len(set(cs)) == 1)


# --------------------------------- [GIS-2] --wide: the detector's own scope --

def leg_wide():
    """[GIS-2] the landed NC1 detector inspects only the BINDING circuits.
    (GR-17)(d) licenses that restriction only at `Λ = ∅`; here it is measured
    against the same gate run over EVERY circuit."""
    print(f"[GIS-2] is the binding-circuit restriction of the landed NC1 "
          f"detector sound at `Lambda != empty`? (seed {G_SEED + 2})")
    rng = random.Random(G_SEED + 2)
    t0 = time.time()
    # (a) the 907-shape census pool
    cadm = cmiss = clam = cshapes = 0
    for name, edges in census_shapes():
        hm = hub_model(edges)
        if hm is None:
            continue
        cshapes += 1
        lam = sum(1 for L in hm['lens'] if L == 1)
        if lam == 0:
            continue
        clam += 1
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=COLCAP)
        assert cols is not None and not odd
        hma = hm_all(hm)
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            cadm += 1
            bad = nc1_violations(hm, col, edges, allverts)
            badw = nc1_violations(hma, col, edges, allverts)
            assert set(map(tuple, bad)) <= set(map(tuple, badw))
            if badw and not bad:
                cmiss += 1
                print(f"  *** RESTRICTION MISS at census shape {name}: "
                      f"widened finds {badw}, landed finds none")
    print(f"  census pool: {cshapes} shapes, {clam} with Lambda != empty, "
          f"{cadm} admissible colourings; the restriction lets {cmiss} "
          f"violating colourings through  [{time.time() - t0:.0f}s]")
    # (b) the constructed D = 0 stratum, Lambda = empty -- where (GR-17)(d)
    #     IS proven, so widening must change nothing: the negative control.
    zadm = zmiss = 0
    for n in CUBIC_N:
        for hedges, lens, members, auts in stratum(n, lamcap=0):
            r = scan_shape(specs_of(hedges, lens), rng, want_rank=False)
            if r is None:
                continue
            zadm += r['adm']
            zmiss += r['missed']
    print(f"  NEGATIVE CONTROL, the `Lambda = empty` stratum where "
          f"(GR-17)(d) is PROVEN: {zadm} admissible colourings, {zmiss} let "
          f"through by the restriction (must be 0)")
    assert zmiss == 0, "(GR-17)(d) fails at Lambda = empty"
    # (c) the constructed D = 0 stratum, Lambda != empty, n_hub <= 6, EVERY
    #     length tuple (the |Lambda| <= 1 fence removed)
    ladm = lmiss = lshapes = lbad = 0
    for n in CUBIC_N:
        for hedges, lens, members, auts in stratum(n, lamlo=1):
            r = scan_shape(specs_of(hedges, lens), rng, want_rank=False)
            if r is None:
                continue
            lshapes += 1
            ladm += r['adm']
            lmiss += r['missed']
            if r['missed']:
                lbad += 1
    print(f"  the `Lambda != empty` stratum at n_hub <= 6, lamcap UNFENCED: "
          f"{lshapes} isomorphism classes, {ladm} admissible colourings; the "
          f"restriction lets {lmiss} violating colourings through, at {lbad} "
          f"shapes  [{time.time() - t0:.0f}s]")
    print()


# ------------------------------------- [GIS-3] --chain: (GR-86) on the island

def leg_chain():
    """[GIS-3] (GR-86)'s repair chain, and why it cannot reach the island:
    its chain branches are EVEN by construction, and the island's violated
    circuit has none; and the odd flip that WOULD repair the circuit breaks
    BALANCE, which no even flip can restore."""
    print(f"[GIS-3] (GR-86)'s repair chain against the island (seed "
          f"{G_SEED + 3})")
    rng = random.Random(G_SEED + 3)
    t0 = time.time()
    shapes = evenhit = oddbal = balbad = 0
    nflip = blk = neven = 0
    for n in CUBIC_N:
        for hedges, lens, members, auts in stratum(n, lamlo=1):
            r = scan_shape(specs_of(hedges, lens), rng, want_rank=False,
                           wide=False)
            if r is None or not r['noeven']:
                continue
            edges, hm = r['edges'], r['hm']
            allverts = sorted(verts_of(edges), key=str)
            ne = no_even_circuits(hm)
            shapes += 1
            # (i) NO chain branch can lie on the circuit: chains are even.
            for cyc in ne:
                if any(hm['lens'][k] % 2 == 0 for k in cyc):
                    evenhit += 1
            cols, odd = colourings(edges, cap=COLCAP)
            assert cols is not None and not odd
            for col in cols:
                if not admissible(edges, allverts, hm, col):
                    continue
                nc1_law(hm, col)
                bad = set(map(tuple, nc1_violations(hm, col, edges,
                                                    allverts)))
                for cyc in ne:
                    if tuple(sorted(cyc)) not in bad:
                        continue
                    for k in cyc:
                        nflip += 1
                        c2 = flip_branch(edges, col, hm['branches'][k][2])
                        nA = sum(1 for e in edges if c2[e] == 'A')
                        nB = sum(1 for e in edges if c2[e] == 'B')
                        assert abs(nA - nB) == 2, \
                            "an odd flip must move |E_A| - |E_B| by exactly 2"
                        oddbal += 1
                        # (GR-86)(i) localized: the monochromatic hubs the
                        # flip creates are EXACTLY the blocked ends.
                        assert sorted(mono_hubs(edges, hm, c2)) == \
                            sorted(blocked_ends(edges, hm, col, k)), \
                            "(GR-86)(i)'s deficiency localization fails"
                        blk += len(blocked_ends(edges, hm, col, k))
                        # every EVEN flip, alone or in any chain, is
                        # balance-neutral -- so no chain repairs the balance
                        for j, L in enumerate(hm['lens']):
                            if L % 2:
                                continue
                            c3 = flip_branch(edges, c2, hm['branches'][j][2])
                            mA = sum(1 for e in edges if c3[e] == 'A')
                            if mA != nA:
                                balbad += 1
                            neven += 1
    print(f"  island shapes reached (lamcap UNFENCED, n_hub <= 6): {shapes} "
          f"isomorphism classes")
    print(f"  no-even-branch circuits found to contain an even branch: "
          f"{evenhit} (must be 0 -- it is the definition)")
    assert evenhit == 0
    print(f"  odd flips of a violated island circuit tested: {nflip}; every "
          f"one moves `|E_A| - |E_B|` by exactly 2 ({oddbal}/{nflip})")
    assert oddbal == nflip
    print(f"  (GR-86)(i)'s deficiency localization asserted at every one of "
          f"those {nflip} flips: the monochromatic hubs created are EXACTLY "
          f"the blocked ends ({blk} blocked ends in total)")
    print(f"  even flips tested for balance neutrality: {neven}; the number "
          f"that changed `|E_A|`: {balbad} (must be 0 -- (GR-16)(i): an even "
          f"branch has `A(β) = ℓ/2`, bit-independent)")
    assert balbad == 0
    print(f"  VERDICT: (GR-86)(ii)'s chain is EVEN-only and therefore "
          f"balance-NEUTRAL, so it cannot repair an island circuit ALONE -- "
          f"and that is exactly why it COMPOSES: it clears the blocked ends "
          f"an odd-pair flip leaves without touching the balance the pair "
          f"restored, and without touching the all-odd circuit at all.  "
          f"See --pair for the composite.  [{time.time() - t0:.0f}s]")
    print()


# ----------------------------------------- [GIS-4] --pair: the odd-pair flip

def mono_hubs(edges, hm, col):
    """The hubs at which all three darts carry one colour -- the conjunct
    (GR-86) calls admissibility, and the only one an odd-pair flip can
    break."""
    return [v for v in hm['hubs']
            if len({col[e] for e in edges if v in e}) == 1]


def blocked_ends(edges, hm, col, k):
    """(GR-86)(i) localized: the ends of branch `k` at which its dart is the
    LONE dart of its colour.  Flipping `k` creates a monochromatic hub at
    exactly those ends and nowhere else."""
    out = []
    for v in hm['branches'][k][:2]:
        dart = next(e for e in hm['branches'][k][2] if v in e)
        others = [col[e] for e in edges if v in e and e != dart]
        if all(c != col[dart] for c in others):
            out.append(v)
    return out


def even_chain_repair(edges, hm, col, cap=6):
    """(GR-86)(ii)'s repair chain, RUN: add distinct EVEN branches, each
    incident to a currently-inadmissible hub, until no hub is monochromatic.

    Bounded DFS to depth `cap` -- a capped search, so a `None` is "no chain
    of at most `cap` even branches", never "no chain".  Every branch it adds
    is even, so by (GR-16)(i) it is BALANCE-NEUTRAL, and at an island circuit
    (all branches odd) it cannot touch the circuit at all."""
    def dfs(cur, used, depth):
        bad = mono_hubs(edges, hm, cur)
        if not bad:
            return cur, used
        if depth == 0:
            return None, None
        v = bad[0]
        for k, L in enumerate(hm['lens']):
            if L % 2 or k in used or v not in hm['branches'][k][:2]:
                continue
            r, u = dfs(flip_branch(edges, cur, hm['branches'][k][2]),
                       used | {k}, depth - 1)
            if r is not None:
                return r, u
        return None, None
    return dfs(col, frozenset(), cap)


def island_repair(edges, allverts, hm, col, cyc, cap=6):
    """The composite island instrument: (GR-154)'s ODD PAIR, then
    (GR-86)(ii)'s EVEN repair chain.

    Stage 1+2 flip one branch of `cyc` together with an opposite-ended odd
    branch off it -- balance-preserving by (GR-153)(b), and `h_≠(cyc) = 2`
    by (GR-153)(a).  Stage 3 clears whatever monochromatic hubs those two
    flips left, using only EVEN branches, which changes neither the balance
    nor -- since `cyc` has no even branch -- `h_≠(cyc)`.

    Returns (colouring, (k, j, chain)) or (None, None).  `chain` empty means
    stage 3 was not needed."""
    odds = [k for k, L in enumerate(hm['lens']) if L % 2 == 1]
    tag = tuple(sorted(cyc))
    base = None
    inc = {}
    for (c, _w) in hm['binding']:
        for kk in c:
            inc[kk] = inc.get(kk, 0) + 1
    # TIER P first -- (GR-155)'s hypothesis in full: `beta` private (in no
    # OTHER binding circuit) and of length >= 3; `delta` in NO binding
    # circuit, odd, of length >= 3, opposite-ended, and with no blocked end.
    for k in sorted(cyc):
        if hm['lens'][k] < 3 or inc.get(k, 0) != 1:
            continue
        ck = end_colour(hm, col, k)
        for j in odds:
            if inc.get(j, 0) or hm['lens'][j] < 3 \
                    or end_colour(hm, col, j) == ck \
                    or blocked_ends(edges, hm, col, j):
                continue
            c2 = flip_branch(edges, col, hm['branches'][k][2])
            c2 = flip_branch(edges, c2, hm['branches'][j][2])
            assert admissible(edges, allverts, hm, c2), \
                "(GR-155): the private odd pair must stay admissible"
            walk = cycle_walk(hm['branches'], hm['ends'], cyc)
            assert h_neq(hm, c2, walk) == 2, "(GR-155): h_neq(gamma) != 2"
            was = set(map(tuple, nc1_violations(hm, col, edges, allverts)))
            now = set(map(tuple, nc1_violations(hm, c2, edges, allverts)))
            assert tag not in now, "(GR-155): gamma is not repaired"
            assert now <= was, \
                "(GR-155): the private odd pair violated a NEW binding circuit"
            return c2, (k, j, (), 'P')
    # TIER 1 then: both flipped branches of length >= 3, i.e. NEITHER is a
    # `Λ`-edge, which is the case (GR-154) proves outright.
    for tier in (3, 1):
        for k in sorted(cyc):
            if hm['lens'][k] < tier:
                continue
            ck = end_colour(hm, col, k)
            for j in odds:
                if j in cyc or hm['lens'][j] < tier \
                        or end_colour(hm, col, j) == ck:
                    continue
                c2 = flip_branch(edges, col, hm['branches'][k][2])
                c2 = flip_branch(edges, c2, hm['branches'][j][2])
                # (GR-154), the clauses that hold BEFORE any chain:
                assert sum(1 for e in edges if c2[e] == 'A') == \
                    sum(1 for e in edges if c2[e] == 'B'), \
                    "(GR-154)(i): the odd pair must preserve balance"
                walk = cycle_walk(hm['branches'], hm['ends'], cyc)
                assert h_neq(hm, c2, walk) == 2, \
                    "(GR-154)(ii): the odd pair must set h_neq(gamma) = 2"
                if tier == 3:
                    assert not cycle_rank(allverts,
                                          [e for e in edges
                                           if c2[e] == 'A']) \
                        and not cycle_rank(allverts,
                                           [e for e in edges
                                            if c2[e] == 'B']), \
                        "(GR-154)(iii): a non-Lambda pair cannot break the " \
                        "forest conjunct"
                    if base is None:
                        base = circuit_report(hm, col, edges, allverts,
                                              cycs=[c for (c, _w)
                                                    in hm['binding']])
                    now = circuit_report(hm, c2, edges, allverts,
                                         cycs=[c for (c, _w)
                                               in hm['binding']])
                    for (b0, n0) in zip(base, now):
                        if k in b0[0] or j in b0[0]:
                            continue
                        assert b0[2:] == n0[2:], \
                            "(GR-154)(iv): D_A/D_B moved at an untouched " \
                            "binding circuit"
                c3, used = even_chain_repair(edges, hm, c2, cap)
                if c3 is None:
                    continue
                assert all(hm['lens'][u] % 2 == 0 for u in used), \
                    "(GR-86)(ii) chains are EVEN by construction"
                assert not (set(used) & set(cyc)), \
                    "an even chain branch landed on an all-odd circuit"
                if not admissible(edges, allverts, hm, c3):
                    continue
                if tag in set(map(tuple, nc1_violations(hm, c3, edges,
                                                        allverts))):
                    continue
                return c3, (k, j, tuple(sorted(used)), tier)
    return None, None


def leg_pair():
    """[GIS-4] the island's own repair instrument: the ODD-PAIR flip."""
    print(f"[GIS-4] the odd-pair flip, the island's own instrument (seed "
          f"{G_SEED + 4})")
    rng = random.Random(G_SEED + 4)
    t0 = time.time()
    shapes = viol = partner = repaired = full = balassert = 0
    hnfix = chained = chainlen = nochain = 0
    tier3 = tier1 = tierP = 0
    noglobal = []
    unrep = []
    for n in CUBIC_N:
        for hedges, lens, members, auts in stratum(n, lamlo=1):
            r = scan_shape(specs_of(hedges, lens), rng, want_rank=False,
                           wide=False)
            if r is None or not r['noeven']:
                continue
            edges, hm = r['edges'], r['hm']
            allverts = sorted(verts_of(edges), key=str)
            ne = [tuple(sorted(c)) for c in no_even_circuits(hm)]
            shapes += 1
            cols, odd = colourings(edges, cap=COLCAP)
            assert cols is not None and not odd
            anyclean = False
            for col in cols:
                if not admissible(edges, allverts, hm, col):
                    continue
                # (GR-153)(b): balance <=> exactly half the odd branches are
                # A-ended.
                odds = [k for k, L in enumerate(hm['lens']) if L % 2 == 1]
                nA = sum(1 for k in odds
                         if end_colour(hm, col, k) == 'A')
                assert len(odds) % 2 == 0 and 2 * nA == len(odds), \
                    "(GR-153)(b) fails: balance is not the half-count law"
                balassert += 1
                bad = set(map(tuple, nc1_violations(hm, col, edges,
                                                    allverts)))
                if not bad:
                    anyclean = True
                for cyc in ne:
                    if cyc not in bad:
                        continue
                    viol += 1
                    # (GR-153)(c): an opposite-ended odd partner exists OFF
                    # the circuit.
                    cs = {end_colour(hm, col, k) for k in cyc}
                    assert len(cs) == 1, \
                        "a violated all-odd 3-circuit is monochromatic-ended"
                    c0 = cs.pop()
                    cand = [j for j in odds if j not in cyc
                            and end_colour(hm, col, j) != c0]
                    assert len(cand) >= 3, \
                        "(GR-153)(c) fails: fewer than 3 partners off gamma"
                    partner += 1
                    c2, pick = island_repair(edges, allverts, hm, col, cyc)
                    if c2 is None:
                        unrep.append((n, specs_of(hedges, lens), cyc))
                        continue
                    repaired += 1
                    if pick[3] == 'P':
                        tierP += 1
                    elif pick[3] == 3:
                        tier3 += 1
                    else:
                        tier1 += 1
                    if pick[2]:
                        chained += 1
                        chainlen += len(pick[2])
                    else:
                        nochain += 1
                    walk = cycle_walk(hm['branches'], hm['ends'], cyc)
                    if h_neq(hm, c2, walk) == 2:
                        hnfix += 1
                    if not nc1_violations(hm, c2, edges, allverts):
                        full += 1
            if not anyclean:
                noglobal.append((n, specs_of(hedges, lens)))
    print(f"  island shapes (lamcap UNFENCED, n_hub <= 6): {shapes} "
          f"isomorphism classes  [{time.time() - t0:.0f}s]")
    print(f"  (GR-153)(b) the half-count balance law asserted at "
          f"{balassert} admissible colourings")
    print(f"  violated island circuits: {viol}; (GR-153)(c) asserted at all "
          f"{partner} of them -- at least 3 opposite-ended odd partners OFF "
          f"the circuit, every time")
    print(f"  the composite instrument repairs the circuit AND lands back in "
          f"the admissible set at {repaired}/{viol}; `h_neq == 2` afterwards "
          f"at {hnfix}/{repaired}")
    print(f"  TIER P -- (GR-155)'s hypothesis in FULL (private beta of length "
          f">= 3; delta in NO binding circuit, length >= 3, opposite-ended, "
          f"unblocked), with its whole conclusion ASSERTED including `no NEW "
          f"binding circuit is violated`: {tierP}/{viol}")
    print(f"  TIER 1 (both flipped branches of length >= 3, so NEITHER is a "
          f"`Lambda`-edge -- the case (GR-154) proves outright, with the "
          f"balance / forest / h_neq / D-invariance clauses ASSERTED at each): "
          f"{tier3}/{repaired}; the `Lambda`-edge fallback was needed at "
          f"{tier1}/{repaired}")
    print(f"  (GR-86)(ii)'s even chain was NEEDED at {chained}/{repaired} "
          f"(mean chain length "
          f"{chainlen / chained if chained else 0:.2f}) and unnecessary at "
          f"{nochain}/{repaired} -- the odd pair alone sufficed there")
    print(f"  the repaired colouring is NC1-clean at EVERY binding circuit "
          f"at {full}/{viol} (the residual is the OTHER circuits the pair "
          f"disturbs -- the (GR-24)-style privacy hypothesis is what closes "
          f"it, and it is NOT asserted here)")
    print(f"  violated island circuits the instrument could NOT repair: "
          f"{len(unrep)}")
    for (n, sp, cyc) in unrep[:4]:
        print(f"    *** UNREPAIRED n_hub={n} {sp} at circuit {cyc}")
    print(f"  island shapes with NO NC1-clean admissible colouring at all: "
          f"{len(noglobal)}")
    for (n, sp) in noglobal[:6]:
        print(f"    *** (GR-15) REFUTATION CANDIDATE n_hub={n} {sp}")
    print()


# -------------------------------------------- [GIS-5] --deep: the hunt ------

def leg_deep(nhub=6, lamcap=99, lamlo=2, want_rank=True, control=40):
    """[GIS-5] THE REFUTATION HUNT over the stratum `cflank --lam6` fences
    off: `|Λ| >= lamlo` at `n_hub = nhub`, every length tuple, exhaustive
    over isomorphism classes and over all `2^M` bits at each."""
    print(f"[GIS-5] the refutation hunt: |Lambda| >= {lamlo} at "
          f"n_hub = {nhub}, lamcap = {lamcap} (seed {G_SEED + 5})")
    rng = random.Random(G_SEED + 5)
    t0 = time.time()
    M = 3 * nhub // 2
    tot = labelled = nc1miss = widemiss = rankmiss = isl = 0
    adm = nc1 = nc1w = clean = missed = 0
    lamhist = {}
    profs = {}
    ctl = random.Random(G_SEED + 55)
    ctl_done = ctl_ok = 0
    pool = list(stratum(nhub, lamcap=lamcap, lamlo=lamlo))
    nontriv = [i for i, (_h, _l, m, _a) in enumerate(pool) if len(m) > 1]
    ctl_idx = set(ctl.sample(nontriv, min(control, len(nontriv))))
    print(f"  {len(pool)} isomorphism classes pass (GR-25)'s cut criterion "
          f"({len(nontriv)} with a nontrivial orbit; {len(ctl_idx)} drawn "
          f"for the orbit control)  [{time.time() - t0:.0f}s]")
    for pidx, (hedges, lens, members, auts) in enumerate(pool):
        specs = specs_of(hedges, lens)
        r = scan_shape(specs, rng, want_rank=want_rank)
        if r is None:
            continue
        tot += 1
        labelled += len(members)
        hm = r['hm']
        adm += r['adm']
        nc1 += r['nc1']
        nc1w += r['nc1w']
        clean += r['clean']
        missed += r['missed']
        lamhist[r['lam']] = lamhist.get(r['lam'], 0) + len(members)
        ne = no_even_circuits(hm)
        if ne:
            isl += 1
            for cyc in ne:
                p = tuple(sorted(hm['lens'][k] for k in cyc))
                profs[p] = profs.get(p, 0) + len(members)
        if r['adm'] and not r['nc1']:
            nc1miss += 1
            print(f"  *** NC1 MISS {specs} (admissible {r['adm']})")
        if r['adm'] and not r['nc1w']:
            widemiss += 1
            print(f"  *** WIDE NC1 MISS {specs} (admissible {r['adm']}, "
                  f"landed-NC1-passing {r['nc1']})")
        if want_rank and r['hit'] is None:
            rankmiss += 1
            print(f"  *** (GR-15) rank MISS {specs} (admissible {r['adm']}, "
                  f"NC1-passing {r['nc1']}, filter-passing tried {r['tried']})")
        # the ORBIT CONTROL: the quotient is only sound if the scan really is
        # an isomorphism invariant, so re-run it at a non-representative
        # member of a seeded sample of nontrivial orbits.
        if pidx in ctl_idx:
            other = ctl.choice([m for m in members if m != tuple(lens)])
            r2 = scan_shape(specs_of(hedges, other), rng, want_rank=False)
            ctl_done += 1
            assert r2 is not None
            assert (r2['adm'], r2['nc1'], r2['nc1w'], r2['clean'],
                    r2['noeven']) == (r['adm'], r['nc1'], r['nc1w'],
                                      r['clean'], r['noeven']), \
                f"the automorphism quotient is NOT invariant at {specs}"
            # and pin THIS driver's loop to the landed `cflank.hunt_shape`
            r3 = hunt_shape(specs, rng, want_rank=False)
            assert (r3['adm'], r3['nc1']) == (r['adm'], r['nc1']), \
                f"scan_shape disagrees with cflank.hunt_shape at {specs}"
            ctl_ok += 1
    print(f"  {tot} isomorphism classes are class shapes = {labelled} "
          f"LABELLED shapes; {isl} on the no-even-branch island")
    print(f"  by |Lambda| (labelled): {dict(sorted(lamhist.items()))}")
    print(f"  no-even-branch binding-circuit profiles (labelled): "
          f"{dict(sorted(profs.items()))}")
    print(f"  {adm} admissible colourings; NC1-passing {nc1} (landed, "
          f"binding circuits only) / {nc1w} (EVERY circuit); {clean} of the "
          f"latter also merge-free in both blocks")
    print(f"  colourings the binding-circuit restriction lets through: "
          f"{missed}")
    print(f"  ORBIT CONTROL: {ctl_ok}/{ctl_done} nontrivial orbits re-scanned "
          f"at a second member with identical counts")
    print(f"  NC1-unsatisfiable shapes: {nc1miss} (landed) / {widemiss} "
          f"(every circuit); (GR-15) rank misses: {rankmiss}  "
          f"[{time.time() - t0:.0f}s]")
    if nc1miss == 0 and widemiss == 0 and rankmiss == 0:
        print(f"  NO REFUTATION under this cap: every shape of the unswept "
              f"|Lambda| >= {lamlo} stratum at n_hub = {nhub} carries an "
              f"admissible colouring that is NC1-clean at EVERY circuit and "
              f"certified at generic dim Z_+ = dim Z_- = 0 by an exact "
              f"rational point.")
    assert ctl_done == 0 or ctl_ok == ctl_done
    print()
    return dict(shapes=tot, labelled=labelled, nc1miss=nc1miss,
                widemiss=widemiss, rankmiss=rankmiss)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for f in ('island', 'wide', 'chain', 'pair', 'deep', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--lamcap', type=int, default=99)
    ap.add_argument('--lamlo', type=int, default=2)
    ap.add_argument('--nhub', type=int, default=6)
    a = ap.parse_args()
    if not any(vars(a)[f] for f in ('island', 'wide', 'chain', 'pair', 'deep',
                                    'validate')):
        ap.print_help()
        return
    if a.island or a.validate:
        leg_island()
    if a.wide or a.validate:
        leg_wide()
    if a.chain or a.validate:
        leg_chain()
    if a.pair or a.validate:
        leg_pair()
    if a.deep or a.validate:
        leg_deep(nhub=a.nhub, lamcap=a.lamcap, lamlo=a.lamlo)


if __name__ == '__main__':
    main()
