"""§(K-grid) direction GEXIST (2026-08-13) driver -- the arc's second PROOF
direction: the uniform fully-good existence target at `Lambda = empty`,
`D = 0` ("every tight class shape admits an admissible colouring with
a = 0 AND max_P g(P) <= 0 in both blocks"), attacked through the (GR-29)
ledger, modulo (GR-4').  NO new sweep: every pool below is an existing one
(GCAP's 4920-shape `Lambda = empty` `D = 0` stratum, the GUNIF witnesses)
or a targeted construction in CFLANK's idiom (circular ladders, the
crossing-tight-chunk family).

A `w4/` leaf beside `gunif.py`, importing `gunif.py` / `gcap.py` /
`cflank.py` / `gridcol.py` / `grid.py` / `gridwit.py` / `closure.py`
READ-ONLY (README §2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --exh     # (GR-32) the capacity theorem: case list certified on the whole existing pool
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --charge  # (GR-33)/(GR-34): the weakness frame, the first-moment refutation, the ladder rule
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --repair  # (GR-35): the weakness-GUIDED repair at the GUNIF witnesses + the pool law
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --adv     # W5 priced first (thinness measured); the hot-dart census (the sticking configuration)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --validate # all four in one process

Argument state: session draft `fanout-GEXIST.md` (to be merged into
`notes/Pencil-informal.md` §(K-grid) as Steps G38+; labels (GR-32)+ per the
2026-08-13 GEXIST reservation in `notes/Pencil-labels.md`).

THE DERIVED STRUCTURE THE MODES REST ON (proofs in the draft; asserted
here rather than trusted).  Throughout: `Lambda = empty`, `D = 0`, so G°
is a cubic multigraph, branch lengths in [2, 5] ((SD-6)), total excess
`exc = Sum(l - 2) = 6` ((GR-21)); a CHUNK is a connected 2-edge-connected
branch subset S; z(S) = #degree-2-in-S hubs; per (GR-28)(i)
defect_A(S) = Sum_{beta in S}(A(beta) - 1) + #(non-AA degree-2-in-S hubs)
and S is BINDING in A iff defect_A(S) <= 2 (g = 3 - defect >= 1).

(GR-32)  THE CAPACITY THEOREM.  Per item, dA + dB is deterministic:
         a branch contributes exc(beta) = l - 2 to defect_A + defect_B,
         a degree-2-in-S hub contributes 2 minus [its S-dart pair is
         monochromatic].  Hence

             defect_A(S) + defect_B(S) = 2 z(S) + exc(S) - z_mono(S),

         and habitat forces the CAPACITY cap(S) := 2 z(S) + exc(S) to be
         >= 7 at every chunk except S = E(G°), where it is exactly 6 and
         balance forces defect_A = defect_B = 3 identically (tightness:
         Sum(A(beta) - 1) = 3c - M = 3 at D = 0).  Proof of >= 7: (GR-25)
         at W_S plus dart bookkeeping (boundary = z - 2 ch, chord excess
         <= 3 by (SD-6)); improper W_S: z even, z = 0 forces S = E(G°),
         z = 2 leaves >= 3 excess inside, z >= 4 is free.  COROLLARY: a
         chunk with cap <= 5 is binding in some block at EVERY colouring
         -- theta(2,4,4), GCAP's F13 witness, has cap = 4, which is WHY
         it is a g-flank out of habitat; in habitat the mechanism is
         impossible.  Also N(S) := z + w3 + w4 + 2 w5 satisfies
         2N = cap + w_odd, so N >= 4 at every proper chunk.

(GR-33)  THE WEAKNESS LEMMA.  At an admissible colouring every hub has a
         dart pattern 2-1 (mono-hub ban): a MAJORITY colour and a unique
         MINORITY dart.  A degree-2-in-S hub's S-pair is monochromatic
         iff its exit dart IS the minority dart, and then the pair colour
         is the majority colour.  Hence

             defect_A(S) = N(S) - save_A(S),
             save_A(S)   = #(weak-A interiors: exit = minority, maj = A)
                         + #(B-majority odd branches in S),

         binding in A iff save_A >= N - 2 >= 2: every binding chunk
         needs >= 2 aligned weak items.  All-even sub-case = orientation
         form: dart colours of l2/l4 branches are an ORIENTATION of the
         hub multigraph (A-end = head), admissibility = in-degree in
         {1, 2} at every hub, weak-A hubs = in-degree-2 hubs whose
         out-dart exits S.

(GR-34)  ROUTE ADJUDICATION.  The first-moment / union-bound route is
         REFUTED as a route: on circular ladders CL_m (existing CFLANK
         targets, extended along the same recipe) the interval-chunk
         family alone has E[#binding chunks] growing with m past 1, while
         every instance keeps rank-certified fully-good colourings; and
         the interval events have size-independent probability, so no
         per-event-decay (LLL-shaped) argument closes either.  What
         survives is the CORRELATED route: the rung-minority rule (every
         hub's minority dart on its rung) yields an explicit fully-good
         colouring at every even-m ladder tested, PROVEN per shape by an
         exact rational dim Z = 0 point in both blocks through both
         matrices.

(GR-35)  THE UNCROSSING LEMMA AND THE GUIDED REPAIR.  The defect formula
         is SUBMODULAR: defect_A(S) + defect_A(S') >= defect_A(S u S') +
         defect_A(S n S') for any two branch sets with all degrees in
         {2, 3} (per-hub case analysis; the intersection needs no
         structure), so crossing binding chunks either merge into a
         binding union or intersect in a defect <= 1 set -- exactly the
         object the (GR-29) ledger classifies.  At every GUNIF witness
         the recorded flip
         distance (2/2/2/3) is realized inside the weakness frame: flips
         of majority-side even branches at the weak interiors of the
         named binding subset suffice.  On the swept stratum the same
         guided move set realizes Step G32's distance <= 2 law at every
         sampled binding colouring.  The named sticking configuration for
         a future theorem: a hub all three of whose darts are exits of
         capacity-tight chunks (the Hall obstruction to the minority
         orientation); the hot-dart census measures how close the
         habitat comes to one.

WHAT EACH MODE TESTS, one sentence each (F11 -- doubly binding: the
direction's claims are exhaustiveness claims; the per-sentence table is
in the draft's Verification section).

--exh    (GR-32)'s case list on the whole existing 4920-shape pool: EVERY
         2ec chunk of every shape satisfies the capacity trichotomy
         (proper => cap >= 7; improper z >= 2 => cap >= 7; z = 0 => S =
         E(G°) and cap = 6), N >= 4 off the whole graph, the whole-graph
         criticality defect == (3, 3) at every admissible colouring
         sampled, the defect = N - save identity against BOTH independent
         computations (gcap.g_formula and exact gridwit.subgraph_g), the
         2-1 hub-pattern lemma exhaustively, and the theta(2,4,4) /
         K4(3^6) adversarial pair.

--charge the weakness-frame consequences on a seeded pool subsample
         (binding <=> save >= N - 2, >= 2 weak items, the uncrossing
         lemma asserted on every hub-sharing chunk pair), then the ladder
         family: habitat-gated CL_m, the measured E[#binding] growth (the
         first-moment refutation), and the rung-minority rule colouring
         rank-certified fully-good.

--repair the weakness-guided flip search: witness distances 2/2/2/3
         reproduced with candidates RESTRICTED to weak sites of the named
         subset; the pool law (distance <= 2) at every sampled binding
         colouring with the same guided move set.

--adv    W5 priced first: capacity/tightness asserts (cap(S_W5) = 8 at a
         cut-tight W_S, cap(S_W3M) = 7), the measured binding and
         fully-good fractions (binding probability CONSTANT in |S| --
         the LLL killer; fully-good abundant, Step G36); then the
         hot-dart census over the pool subsample (hubs with all three
         darts hot = the sticking configuration; none found =>
         reported).

Exact throughout (integers; rank only through gridcol.block_generic_zero's
GF(p) lower bound with exact-Q recheck through BOTH matrices, README §4
convention 2).  Rngs seeded per mode, seeds printed; no `set` printed;
nothing samples a placement, so `repin.star_generic` gates nothing here
(§(K-clos) (AC-9)).  Wall-clock `[Ns]` annotations are inherently
non-deterministic; every other byte is seed-stable.
"""
import argparse
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from closure import colourings                                         # noqa: E402
from grid import block_data, dim_Z                                     # noqa: E402
from gridwit import subgraph_g                                         # noqa: E402
from gridcol import block_generic_zero, dim_W_branch, subdivide        # noqa: E402
from cflank import (admissible, cubic_habitat, flip_branch,            # noqa: E402
                    hub_model, nc1_violations)
from gcap import (branch_stats, g_formula, pool_specs, subset_eidx,    # noqa: E402
                  two_ec_masks, two_ec_subsets)
from gunif import WITNESSES, spec_to_hm_index, wit_colouring           # noqa: E402

X_SEED = 20260813


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a §1 primitive (checked against the README index and
# the Divergences table).  `chunk_shape` / `weak_frame` / `hub_minority` are
# the (GR-32)/(GR-33) bookkeeping; their canonical Python cross-checks are
# `gcap.g_formula` (the (GR-28) formula) and `gridwit.subgraph_g` (exact).


def incidence(hm):
    """hub -> list of incident branch indices (parallel branches kept)."""
    inc = {v: [] for v in hm['hubs']}
    for k, (u, w) in enumerate(hm['ends']):
        inc[u].append(k)
        inc[w].append(k)
    return inc


def chunk_shape(hm, inc, ks):
    """The colouring-INDEPENDENT data of a chunk (connected 2ec branch
    subset): (z2 hubs, exits, chords, exc, cap, N, improper).  Local
    device for (GR-32); every figure it feeds is cross-checked against
    `gcap.g_formula` / `gridwit.subgraph_g` in --exh."""
    ends, lens = hm['ends'], hm['lens']
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    assert all(d in (2, 3) for d in deg.values()), \
        "chunk with a hub of S-degree outside {2,3}: not cubic / not 2ec"
    z2 = sorted((v for v, d in deg.items() if d == 2), key=str)
    W = set(deg)
    sk = set(ks)
    chords, exits = set(), []
    for v in z2:
        free = [k for k in inc[v] if k not in sk]
        assert len(free) == 1, "degree-2-in-S hub without exactly one free dart"
        k = free[0]
        u, w = ends[k]
        other = w if v == u else u
        if other in W:
            chords.add(k)
        else:
            exits.append((v, k))
    assert 2 * len(chords) + len(exits) == len(z2), "dart bookkeeping broken"
    exc = sum(lens[k] - 2 for k in ks)
    w3 = sum(1 for k in ks if lens[k] == 3)
    w4 = sum(1 for k in ks if lens[k] == 4)
    w5 = sum(1 for k in ks if lens[k] == 5)
    return dict(z2=z2, W=W, exits=exits, chords=sorted(chords),
                exc=exc, cap=2 * len(z2) + exc,
                N=len(z2) + w3 + w4 + 2 * w5, wodd=w3 + w5,
                improper=(len(W) == len(hm['hubs'])))


def hub_minority(hm, stats):
    """Per hub: (majority colour own?, minority branch index) from the
    2-1 dart pattern -- the (GR-33) object.  `stats` = gcap.branch_stats
    for block A; asserts the pattern is 2-1 (mono-hub ban), so call it
    only on admissible colourings."""
    _acnt, du, dw = stats
    darts = {v: [] for v in hm['hubs']}
    for k, (u, w) in enumerate(hm['ends']):
        darts[u].append((k, du[k]))
        darts[w].append((k, dw[k]))
    out = {}
    for v, ds in darts.items():
        na = sum(1 for (_k, a) in ds if a)
        assert 0 < na < len(ds), "monochromatic hub on an admissible colouring"
        if len(ds) == 3:
            maj_a = (na == 2)
            mink = next(k for (k, a) in ds if a != maj_a)
            out[v] = (maj_a, mink)
        else:                              # only at D > 0, never reached here
            out[v] = (None, None)
    return out


def weak_frame(hm, inc, stats, cs, ks):
    """(GR-33): (defect_A, save_A, weakA_hubs, defect_B, save_B, weakB_hubs)
    of the chunk `ks`, from the weakness bookkeeping; --exh asserts it
    against the direct (GR-28) sum, gcap.g_formula and subgraph_g."""
    acnt, du, dw = stats
    ends, lens = hm['ends'], hm['lens']
    sk = set(ks)
    saveA = saveB = 0
    weakA, weakB = [], []
    for v in cs['z2']:
        pair = [(du[k] if v == ends[k][0] else dw[k])
                for k in inc[v] if k in sk]
        assert len(pair) == 2
        if pair[0] == pair[1]:
            if pair[0]:
                saveA += 1
                weakA.append(v)
            else:
                saveB += 1
                weakB.append(v)
    for k in ks:
        if lens[k] % 2:
            if 2 * acnt[k] < lens[k]:      # B-majority odd branch
                saveA += 1
            else:
                saveB += 1
    dA = cs['N'] - saveA
    dB = cs['N'] - saveB
    return dA, saveA, weakA, dB, saveB, weakB


def defect_direct(hm, inc, stats, ks, mine_a=True):
    """(GR-28)(i) literally: Sum(A(beta) - 1) + #(non-AA degree-2-in-S
    hubs) -- the independent recomputation --exh pits against
    N - save."""
    acnt, du, dw = stats
    ends, lens = hm['ends'], hm['lens']
    sk = set(ks)
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    tot = 0
    for k in ks:
        a = acnt[k] if mine_a else lens[k] - acnt[k]
        tot += a - 1
    for v, d in deg.items():
        if d != 2:
            continue
        pr = []
        for k in inc[v]:
            if k in sk:
                own = du[k] if v == ends[k][0] else dw[k]
                pr.append(own if mine_a else not own)
        if not (len(pr) == 2 and all(pr)):
            tot += 1
    return tot


def fully_good_rank(edges, allverts, hm, col, rng):
    """Rank-grade fully-good certificate: an exact rational dim Z = 0
    point in BOTH blocks through BOTH matrices ((GR-31)(i)'s device: by
    (GR-8)'s proven >= direction this proves a = 0 and max_P g(P) <= 0
    with no subset scan)."""
    for mine in ('A', 'B'):
        bd = block_data(edges, allverts, col, mine)
        sv = block_generic_zero(bd, hm['hubs'], hm['branches'], rng, draws=6)
        if sv is None:
            return False
        sval = {c: F(x) for c, x in sv.items()}
        dW = dim_W_branch(bd, hm['hubs'], hm['branches'], sval=sval)
        dZ = dim_Z(bd, sval=sval)
        assert dW == 0 and dZ == 0, \
            "GF(p) zero draw fails the exact-Q recheck (README §4 conv. 2)"
    return True


def sample_admissible(specs, edges, allverts, hm, rng, want, cap=400000):
    """Seeded rejection sampler for admissible colourings: random branch
    bits, kept iff `cflank.admissible`.  Degeneracy guard: asserts it
    produced the requested number inside the draw cap (a shape whose
    admissible set is too thin to sample is reported, not silently
    under-sampled)."""
    out, draws = [], 0
    while len(out) < want and draws < cap:
        draws += 1
        first = ['A' if rng.random() < 0.5 else 'B' for _ in specs]
        col = wit_colouring(specs, first)
        if admissible(edges, allverts, hm, col):
            out.append(col)
    assert len(out) == want, \
        f"admissible sampler starved: {len(out)}/{want} in {cap} draws"
    return out, draws


# ------------------------------------------------- ladder constructions -----
#
# CFLANK's `--tight` targets already carry CL5..CL8 with excess 2+2+2 on
# three rungs; the family below is the SAME recipe (cflank.ladder's hub
# graph, excess on rungs), extended to even m for the rung-minority rule.
# Targeted constructions in the CFLANK/GUNIF idiom -- not a pool widening.


def ladder_specs(m, exc_rungs):
    """CL_m as branch specs [(u, w, len)]: top rim 0..m-1 (branch i =
    (i, i+1)), bottom rim m..2m-1, rungs 2m..3m-1 (branch 2m+i =
    (i, m+i)); `exc_rungs` maps rung offset i -> extra length."""
    specs = []
    for i in range(m):
        specs.append((i, (i + 1) % m, 2))
    for i in range(m):
        specs.append((m + i, m + (i + 1) % m, 2))
    for i in range(m):
        specs.append((i, m + i, 2 + exc_rungs.get(i, 0)))
    return specs


def ladder_rule_first(m, specs):
    """The rung-minority rule colouring for EVEN m (draft Step G40): top
    hub i carries rim darts c_i = A iff i even and rung dart ~c_i; bottom
    hub m+i carries rim darts ~c_i and rung dart c_i.  Every hub's
    minority dart is its RUNG -- which no interval or square chunk ever
    uses as an exit -- so save == 0 on that whole family."""
    assert m % 2 == 0, "the pure rule needs even m (rim alternation parity)"
    first = []
    for i in range(m):                     # top rim (i, i+1): dart at i = c_i
        first.append('A' if i % 2 == 0 else 'B')
    for i in range(m):                     # bottom rim: dart at m+i = ~c_i
        first.append('B' if i % 2 == 0 else 'A')
    for i in range(m):                     # rung (i, m+i): dart at i = ~c_i
        first.append('B' if i % 2 == 0 else 'A')
    return first


def interval_chunks(m):
    """The interval-chunk family of CL_m: for start i, hub-length t in
    [2, m-1], the branch set {rungs i..i+t-1, top rims i..i+t-2, bottom
    rims i..i+t-2} (indices mod m) -- z = 4 (the corner hubs), exits =
    the four boundary rims.  Theta(m(m-2)) members: the first-moment
    refutation family."""
    out = []
    for i in range(m):
        for t in range(2, m):
            ks = []
            for j in range(t):
                ks.append(2 * m + (i + j) % m)          # rungs
            for j in range(t - 1):
                ks.append((i + j) % m)                  # top rims
                ks.append(m + (i + j) % m)              # bottom rims
            out.append(tuple(sorted(ks)))
    return out


# --------------------------------------------- [GEX-1] --exh: (GR-32) -------

def leg_exh():
    """[GEX-1] the capacity theorem's case list, certified on the whole
    existing pool; the identity chain; the hub-pattern lemma; the
    adversarial pair."""
    t0 = time.time()
    print(f"[GEX-1] (GR-32) capacity theorem -- case list on the existing "
          f"Lambda = empty D = 0 pool (seed {X_SEED + 1})")
    rng = random.Random(X_SEED + 1)

    # ---- (a) the 2-1 hub-pattern lemma, exhaustively (8 patterns x 3
    #      exits): unique minority; S-pair monochromatic iff exit = minority
    pats = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
    for p in pats:
        if sum(p) in (0, 3):
            continue                       # mono: excluded by admissibility
        maj = 1 if sum(p) == 2 else 0
        mins = [i for i in range(3) if p[i] != maj]
        assert len(mins) == 1
        for ex in range(3):
            pair = [p[i] for i in range(3) if i != ex]
            assert (pair[0] == pair[1]) == (ex == mins[0])
            if pair[0] == pair[1]:
                assert pair[0] == maj
    print("  hub-pattern lemma: 6 non-mono patterns x 3 exits certified "
          "(unique minority; S-pair mono <=> exit = minority, colour = maj)")

    # ---- (b) the capacity trichotomy over EVERY chunk of EVERY pool shape
    shapes = chunks = tight7 = 0
    tight_by_n = {}
    id_checks = 0
    for n, specs in pool_specs():
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        shapes += 1
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        assert hm is not None
        inc = incidence(hm)
        tec = two_ec_subsets(hm, kmin=1)
        allks = tuple(range(len(hm['ends'])))
        for (ks, _kk) in tec:
            chunks += 1
            cs = chunk_shape(hm, inc, ks)
            if len(cs['z2']) == 0:
                assert ks == allks, "z = 0 chunk that is not the whole graph"
                assert cs['cap'] == 6, "whole-graph capacity != 6"
                assert cs['N'] == 3 + cs['wodd'] // 2
            elif cs['improper']:
                assert len(cs['z2']) >= 2 and len(cs['z2']) % 2 == 0, \
                    "improper chunk with odd/small z"
                assert cs['cap'] >= 7, "improper z >= 2 chunk under capacity 7"
                assert cs['N'] >= 4
            else:
                assert cs['cap'] >= 7, "proper chunk under capacity 7"
                assert cs['N'] >= 4, "proper chunk with N <= 3"
            if cs['cap'] == 7 and ks != allks:
                tight7 += 1
                tight_by_n[n] = tight_by_n.get(n, 0) + 1
        # ---- (c) + (d) on a seeded subsample: whole-graph criticality and
        #      the identity chain defect = N - save = (GR-28) direct
        #      = 3 - g_formula (= 3 - subgraph_g at a deeper subsample)
        if rng.random() < 0.03:
            cols, odd = colourings(edges, cap=1 << 14)
            assert not odd and cols is not None
            adm = [c for c in cols if admissible(edges, allverts, hm, c)]
            for col in adm[:12]:
                stats = branch_stats(hm, col, 'A')
                hub_minority(hm, stats)    # asserts 2-1 patterns
                csall = chunk_shape(hm, inc, allks)
                dA, sA, _wA, dB, sB, _wB = weak_frame(hm, inc, stats, csall, allks)
                assert dA == 3 and dB == 3, \
                    "whole-graph criticality defect != (3, 3)"
                for (ks, kk) in tec[:60]:
                    cs = chunk_shape(hm, inc, ks)
                    dA, sA, _wA, dB, sB, _wB = weak_frame(hm, inc, stats, cs, ks)
                    assert dA == defect_direct(hm, inc, stats, ks, True)
                    assert dB == defect_direct(hm, inc, stats, ks, False)
                    assert dA == 3 - g_formula(hm, stats, ks, kk)
                    id_checks += 1
                    if rng.random() < 0.02:
                        bd = block_data(edges, allverts, col, 'A')
                        gS = subgraph_g(bd, subset_eidx(bd, hm, ks))
                        assert dA == 3 - gS, "formula vs exact subgraph_g"
    assert shapes == 4920, \
        f"pool regeneration drifted: {shapes} != 4920 recorded shapes"
    print(f"  {shapes} shapes (== the recorded 4920), {chunks} chunks: "
          f"capacity trichotomy holds at EVERY chunk "
          f"(proper/improper >= 7; whole graph == 6), N >= 4 off E(G°)")
    print(f"  capacity-TIGHT chunks (cap = 7, proper): {tight7}, by n_hub: "
          f"{sorted(tight_by_n.items())}")
    print(f"  identity chain defect = N - save = (GR-28) direct = "
          f"3 - g_formula asserted at {id_checks} (colouring, chunk) pairs "
          f"(subgraph_g cross-check at a ~2% subsample); whole-graph "
          f"criticality (3, 3) at every sampled admissible colouring")

    # ---- (e) the adversarial pair (README §4 convention 6)
    th = [(0, 1, 2), (0, 1, 4), (0, 1, 4)]
    hedges = [(u, w) for (u, w, _L) in th]
    lens = [L for (_u, _w, L) in th]
    assert not cubic_habitat(2, hedges, lens), \
        "theta(2,4,4) accepted by the habitat gate"
    edges = subdivide(th)
    hm = hub_model(edges)
    inc = incidence(hm)
    cs = chunk_shape(hm, inc, (0, 1, 2))
    assert cs['cap'] == 4, "theta(2,4,4) capacity != 4"
    print("  F13 pair: theta(2,4,4) REJECTED by the habitat gate with "
          "cap = 4 < 6 -- the capacity corollary explains GCAP's F13 "
          "witness (binding in some block at EVERY colouring; pinned "
          "counter-fact: NC1 is satisfiable there, Step G33)")
    k4 = [(0, 1, 3), (0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3), (2, 3, 3)]
    hedges = [(u, w) for (u, w, _L) in k4]
    lens = [L for (_u, _w, L) in k4]
    assert cubic_habitat(4, hedges, lens)
    edges = subdivide(k4)
    hm = hub_model(edges)
    inc = incidence(hm)
    for (ks, _kk) in two_ec_subsets(hm, kmin=1):
        cs = chunk_shape(hm, inc, ks)
        assert cs['cap'] >= 6
    print("  negative control: K4(3,3,3,3,3,3) in habitat, every chunk at "
          "capacity >= 6 (whole graph) / >= 7 (proper)")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------ [GEX-2] --charge: (GR-33/34) ----

def leg_charge():
    """[GEX-2] the weakness frame on the pool; the first-moment refutation
    on the ladder family; the rung-minority rule, rank-certified."""
    t0 = time.time()
    print(f"[GEX-2] (GR-33)/(GR-34) weakness frame + route adjudication "
          f"(seed {X_SEED + 2})")
    rng = random.Random(X_SEED + 2)

    # ---- (a) binding <=> save >= N - 2, >= 2 weak items, and the
    #      submodularity measurement, on a seeded pool subsample
    picked = binding_n = pairs_n = sub_viol = 0
    viol_wit = None
    for n, specs in pool_specs():
        if rng.random() >= 0.03:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        picked += 1
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        inc = incidence(hm)
        tec = two_ec_subsets(hm, kmin=1)
        cols, odd = colourings(edges, cap=1 << 14)
        assert not odd and cols is not None
        adm = [c for c in cols if admissible(edges, allverts, hm, c)]
        rng.shuffle(adm)
        for col in adm[:20]:
            stats = branch_stats(hm, col, 'A')
            dmap = {}
            for (ks, kk) in tec:
                cs = chunk_shape(hm, inc, ks)
                dA, sA, wA, dB, sB, wB = weak_frame(hm, inc, stats, cs, ks)
                dmap[ks] = dA
                for d, s, wk in ((dA, sA, wA), (dB, sB, wB)):
                    if d <= 2 and ks != tuple(range(len(hm['ends']))):
                        binding_n += 1
                        assert s >= cs['N'] - 2 and s >= 2, \
                            "binding chunk with < 2 weak items"
            # the UNCROSSING LEMMA (draft Step G41, proof-backed): the
            # defect FORMULA is submodular over pairs of min-degree-2
            # branch sets in a cubic host -- union and intersection taken
            # as formulas (defect_direct), no chunk-ness needed on either
            keys = [ks for ks in dmap if dmap[ks] <= 3]
            hubs_of = {ks: {v for k in ks for v in hm['ends'][k]}
                       for ks in keys}
            for i in range(len(keys)):
                for j in range(i + 1, len(keys)):
                    a, b = set(keys[i]), set(keys[j])
                    if not (hubs_of[keys[i]] & hubs_of[keys[j]]):
                        continue
                    if a <= b or b <= a:
                        continue
                    tun = tuple(sorted(a | b))
                    tit = tuple(sorted(a & b))
                    pairs_n += 1
                    du = defect_direct(hm, inc, stats, tun, True)
                    di = defect_direct(hm, inc, stats, tit, True) \
                        if tit else 0
                    if du + di > dmap[keys[i]] + dmap[keys[j]]:
                        sub_viol += 1
                        if viol_wit is None:
                            viol_wit = (n, specs, keys[i], keys[j],
                                        dmap[keys[i]], dmap[keys[j]], du, di)
    print(f"  pool subsample: {picked} shapes; {binding_n} binding "
          f"(chunk, block) instances, EVERY one with save >= N - 2 and "
          f">= 2 weak items")
    assert sub_viol == 0, \
        (f"UNCROSSING LEMMA refuted: n={viol_wit[0]}, S={viol_wit[2]}, "
         f"S'={viol_wit[3]}, defects {viol_wit[4]}+{viol_wit[5]} < "
         f"{viol_wit[6]}+{viol_wit[7]} -- fix the draft Step G41 proof")
    print(f"  UNCROSSING LEMMA asserted over {pairs_n} hub-sharing "
          f"low-defect chunk pairs (formula-level union/intersection, no "
          f"chunk-ness required): defect_A(S) + defect_A(S') >= "
          f"defect_A(S u S') + defect_A(S n S') at every pair")

    # ---- (b) the ladder family: E[#binding] growth + the rule colouring
    print("  ladder family CL_m, excess 2+2+2 on rungs 0, 1, 2 (the CFLANK "
          "--tight recipe):")
    for m in (6, 8, 10):
        specs = ladder_specs(m, {0: 2, 1: 2, 2: 2})
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        n = 2 * m
        assert cubic_habitat(n, hedges, lens), f"CL{m} out of habitat"
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        inc = incidence(hm)
        s2h = spec_to_hm_index(specs, hm)
        ivs = [tuple(sorted(s2h[i] for i in ks)) for ks in interval_chunks(m)]
        rungs_hm = {s2h[i] for i in range(2 * m, 3 * m)}
        # E[#binding (chunk, block) events] over seeded admissible
        # colourings, counted over the interval family alone (t >= 2, so
        # it CONTAINS every binding circuit of CL_m: the squares are the
        # t = 2 intervals and no other circuit is binding here) -- a
        # LOWER bound on the full binding count, each event once
        cols, draws = sample_admissible(specs, edges, allverts, hm, rng, 60)
        tot = 0
        for col in cols:
            stats = branch_stats(hm, col, 'A')
            cnt = 0
            for ks in ivs:
                cs = chunk_shape(hm, inc, ks)
                dA, _sA, _wA, dB, _sB, _wB = weak_frame(hm, inc, stats, cs, ks)
                cnt += (dA <= 2) + (dB <= 2)
            tot += cnt
        mean = tot / len(cols)
        # the rung-minority rule colouring: admissible, zero weak items on
        # the interval family, rank-certified fully good
        first = ladder_rule_first(m, specs)
        rcol = wit_colouring(specs, first)
        assert admissible(edges, allverts, hm, rcol)
        stats = branch_stats(hm, rcol, 'A')
        mino = hub_minority(hm, stats)
        assert all(mink in rungs_hm for (_maj, mink) in mino.values()), \
            "rule colouring: some hub's minority dart is NOT its rung"
        for ks in ivs:
            cs = chunk_shape(hm, inc, ks)
            dA, sA, _wA, dB, sB, _wB = weak_frame(hm, inc, stats, cs, ks)
            assert sA == 0 and sB == 0, "interval chunk with a weak item"
            assert dA >= 3 and dB >= 3
        assert not nc1_violations(hm, rcol, edges, allverts)
        ok = fully_good_rank(edges, allverts, hm, rcol, rng)
        assert ok, f"CL{m}: rule colouring NOT rank-certified fully good"
        print(f"    CL{m} (n={n}): habitat OK; E[#binding intervals x "
              f"blocks] = {mean:.2f} over 60 seeded admissible colourings "
              f"({draws} draws); rule colouring: admissible, minority = "
              f"rung at ALL {n} hubs, save = 0 on all {len(ivs)} intervals, "
              f"NC1 clear, dim Z = 0 BOTH blocks at an exact point (proof)")
        if m == 6:
            mean6 = mean
        if m == 10:
            assert mean > 1.0, \
                "first-moment refutation sentence needs E[#binding] > 1"
            assert mean > mean6, "E[#binding] did not grow with m"
    print("  => the union-bound/first-moment route is REFUTED as a route "
          "(E[#binding] > 1 and growing while fully-good colourings are "
          "PROVEN to exist at every member); the correlated rung-minority "
          "rule closes the whole family")
    print(f"  [{time.time() - t0:.0f}s]")


# --------------------------------------------- [GEX-3] --repair: (GR-35) ----

def leg_repair():
    """[GEX-3] the weakness-GUIDED repair: witness distances reproduced
    from weak sites only; the pool distance <= 2 law with guided moves."""
    t0 = time.time()
    print(f"[GEX-3] (GR-35) weakness-guided repair (seed {X_SEED + 3})")
    rng = random.Random(X_SEED + 3)

    # ---- (a) the four GUNIF witnesses: guided flips at the weak interiors
    #      of the NAMED subset realize the recorded distance
    recorded = {'W3M': 2, 'W3': 2, 'W4': 2, 'W5': 3}
    for (name, n, specs, first, S_idx, expect) in WITNESSES:
        tag = name.split()[0]
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        inc = incidence(hm)
        col = wit_colouring(specs, first)
        assert admissible(edges, allverts, hm, col)
        s2h = spec_to_hm_index(specs, hm)
        S_hm = tuple(sorted(s2h[i] for i in S_idx))
        stats = branch_stats(hm, col, 'A')
        cs = chunk_shape(hm, inc, S_hm)
        dA, sA, wA, dB, sB, wB = weak_frame(hm, inc, stats, cs, S_hm)
        assert dA == 3 - expect, f"{tag}: witness subset defect_A mismatch"
        # guided candidates: EVEN branches at the weak interiors of S
        # carrying the majority colour there (the (GR-33) local rotation)
        cand = []
        mino = hub_minority(hm, stats)
        weak = wA if sA >= sB else wB
        for v in weak:
            for k in inc[v]:
                if hm['lens'][k] % 2 == 0 and k != mino[v][1] \
                        and k not in cand:
                    cand.append(k)
        cand.sort()
        found = None
        from itertools import combinations
        for size in range(1, recorded[tag] + 1):
            for sub in combinations(cand, size):
                c2 = col
                for k in sub:
                    c2 = flip_branch(edges, c2, hm['branches'][k][2])
                if not admissible(edges, allverts, hm, c2):
                    continue
                if fully_good_rank(edges, allverts, hm, c2, rng):
                    found = (size, sub)
                    break
            if found:
                break
        assert found is not None, \
            f"{tag}: weak-site flips do not realize distance {recorded[tag]}"
        assert found[0] <= recorded[tag] and found[0] <= expect
        print(f"  {tag}: weak interiors (block "
              f"{'A' if sA >= sB else 'B'}): {len(weak)}, guided candidate "
              f"branches: {len(cand)}; fully-good (rank-certified, both "
              f"blocks, both matrices) at {found[0]} guided flip(s) -- "
              f"recorded distance {recorded[tag]}, g = {expect}")

    # ---- (b) the pool law with guided moves, on a seeded subsample
    tried = fixed1 = fixed2 = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.02 or tried >= 120:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        inc = incidence(hm)
        tec = two_ec_subsets(hm, kmin=1)
        cols, odd = colourings(edges, cap=1 << 14)
        assert not odd and cols is not None
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            if nc1_violations(hm, col, edges, allverts):
                continue
            stats = branch_stats(hm, col, 'A')
            worst, weak_sites = 0, []
            for (ks, _kk) in tec:
                cs = chunk_shape(hm, inc, ks)
                dA, sA, wA, dB, sB, wB = weak_frame(hm, inc, stats, cs, ks)
                if dA <= 2 and ks != tuple(range(len(hm['ends']))):
                    worst = max(worst, 3 - dA)
                    weak_sites += wA
                if dB <= 2 and ks != tuple(range(len(hm['ends']))):
                    worst = max(worst, 3 - dB)
                    weak_sites += wB
            if worst == 0:
                continue
            tried += 1
            mino = hub_minority(hm, stats)
            cand = sorted({k for v in weak_sites for k in inc[v]
                           if hm['lens'][k] % 2 == 0 and k != mino[v][1]})
            from itertools import combinations
            done = 0
            for size in (1, 2):
                for sub in combinations(cand, size):
                    c2 = col
                    for k in sub:
                        c2 = flip_branch(edges, c2, hm['branches'][k][2])
                    if not admissible(edges, allverts, hm, c2):
                        continue
                    s2 = branch_stats(hm, c2, 'A')
                    good = True
                    for (ks, _kk2) in tec:
                        cs = chunk_shape(hm, inc, ks)
                        dA, _a, _b, dB, _c, _d = weak_frame(hm, inc, s2, cs, ks)
                        if min(dA, dB) < 3:
                            good = False
                            break
                    if good:
                        done = size
                        break
                if done:
                    break
            assert done in (1, 2), \
                "pool binding colouring NOT repaired by <= 2 guided flips"
            fixed1 += done == 1
            fixed2 += done == 2
            if tried >= 120:
                break
    print(f"  pool law (guided moves only): {tried} binding NC1-passing "
          f"colourings sampled, all repaired -- distance 1: {fixed1}, "
          f"distance 2: {fixed2}, unrepaired: 0 (Step G32's law realized "
          f"inside the weakness frame)")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------ [GEX-4] --adv: pricing ----

def leg_adv():
    """[GEX-4] W5 priced first; the thinness measurements; the hot-dart
    census (the sticking configuration)."""
    t0 = time.time()
    print(f"[GEX-4] W5 first + the hot-dart census (seed {X_SEED + 4})")
    rng = random.Random(X_SEED + 4)

    # ---- (a) W5 and W3M priced in the (GR-32) frame
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    for tag, capw, tightcut in (('W5', 8, 7), ('W3M', 7, 7)):
        (name, n, specs, first, S_idx, expect) = by_tag[tag]
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        inc = incidence(hm)
        s2h = spec_to_hm_index(specs, hm)
        S_hm = tuple(sorted(s2h[i] for i in S_idx))
        cs = chunk_shape(hm, inc, S_hm)
        assert cs['cap'] == capw, f"{tag}: capacity != {capw}"
        cut = 2 * len(cs['exits']) + cs['exc'] \
            + sum(hm['lens'][k] - 2 for k in cs['chords'])
        assert cut == tightcut, f"{tag}: 2 d(W_S) + exc(E(W_S)) != {tightcut}"
        col = wit_colouring(specs, first)
        stats = branch_stats(hm, col, 'A')
        dA, sA, _wA, dB, sB, _wB = weak_frame(hm, inc, stats, cs, S_hm)
        assert sA == cs['N'] - dA
        print(f"  {tag}: cap(S) = {capw}, cut value 2d+exc(E(W_S)) = "
              f"{tightcut} (TIGHT at 7 => the witness stratum is the "
              f"capacity-tight one); witness colouring aligns save_A = "
              f"{sA} of N = {cs['N']}")

    # ---- (b) thinness at W5: binding fraction of the named subset and
    #      the fully-good fraction, over seeded admissible colourings
    (name, n, specs, first, S_idx, expect) = by_tag['W5']
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    hm = hub_model(edges)
    inc = incidence(hm)
    s2h = spec_to_hm_index(specs, hm)
    S_hm = tuple(sorted(s2h[i] for i in S_idx))
    cs = chunk_shape(hm, inc, S_hm)
    cols, draws = sample_admissible(specs, edges, allverts, hm, rng, 200)
    bindS = 0
    for col in cols:
        stats = branch_stats(hm, col, 'A')
        dA, _sA, _wA, dB, _sB, _wB = weak_frame(hm, inc, stats, cs, S_hm)
        if min(dA, dB) <= 2:
            bindS += 1
    fg = sum(fully_good_rank(edges, allverts, hm, c, rng)
             for c in cols[:60])
    print(f"  W5 measured: S binding at {bindS}/200 seeded admissible "
          f"colourings ({draws} draws) -- binding-at-g >= 1 needs only 2 "
          f"of 4 aligned interiors, so its probability is a CONSTANT, not "
          f"a decaying function of |S| (the LLL-shaped route's killer); "
          f"fully-good (rank-certified) at {fg}/60 -- abundant, exactly "
          f"Step G36's observation")
    assert bindS < 100, "W5 binding slice above 1/2 -- reprice the argument"
    assert fg > 20, "W5 fully-good slice NOT abundant -- Step G36 challenged"

    # ---- (c) the hot-dart census on a pool subsample: a dart is HOT when
    #      it is an exit of a capacity-tight (cap = 7) proper chunk; the
    #      sticking configuration is a hub with ALL THREE darts hot
    shapes3 = shapes_scanned = hot_hubs = full_hot = 0
    worst = None
    for n, specs in pool_specs():
        if rng.random() >= 0.04:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        shapes_scanned += 1
        edges = subdivide(specs)
        hm = hub_model(edges)
        inc = incidence(hm)
        hot = {v: set() for v in hm['hubs']}
        for (ks, _kk) in two_ec_subsets(hm, kmin=1):
            cs = chunk_shape(hm, inc, ks)
            if cs['improper'] or cs['cap'] > 7:
                continue
            for (v, k) in cs['exits']:
                hot[v].add(k)
        for v, s in hot.items():
            if len(s) >= 2:
                hot_hubs += 1
            if len(s) == 3:
                full_hot += 1
                if worst is None:
                    worst = (n, specs, str(v))
        shapes3 += 1
    print(f"  hot-dart census ({shapes_scanned} pool shapes): hubs with "
          f">= 2 hot darts: {hot_hubs}; hubs with ALL THREE darts hot "
          f"(the sticking configuration's seed): {full_hot}"
          + (f"; first: n={worst[0]}, hub {worst[2]}" if worst else
             " -- none on this subsample"))
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------- validate -------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', action='store_true')
    ap.add_argument('--charge', action='store_true')
    ap.add_argument('--repair', action='store_true')
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    ran = False
    if args.exh or args.validate:
        leg_exh()
        ran = True
    if args.charge or args.validate:
        leg_charge()
        ran = True
    if args.repair or args.validate:
        leg_repair()
        ran = True
    if args.adv or args.validate:
        leg_adv()
        ran = True
    if not ran:
        print(__doc__)
    else:
        print("gexist: ALL ASSERTS PASSED")


if __name__ == '__main__':
    main()
