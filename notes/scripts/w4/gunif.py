"""§(K-grid) direction GUNIF (2026-08-13) driver -- the arc's first PROOF
direction: adjudicate (GR-28)(iv)'s `k >= 3` dart-menu gap and the g-family
repair theorem (Step G33's What-would-change-this items (i)-(ii)) on the
`Lambda = empty`, `D = 0` stratum, modulo (GR-4').

A `w4/` leaf beside `gcap.py`, importing `gcap.py` / `cflank.py` /
`gridcol.py` / `grid.py` / `gridwit.py` / `closure.py` READ-ONLY (README
§2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --menu     # the (GR-29) dart menu, machine-certified complete
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --ledger   # the budget ledger: every n_hub <= 6 tuple killed by a named clause; survivors from n = 8
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --wit      # THE ADJUDICATION: four constructed witnesses (n = 8, 10, 12, 16; k = 3, 3, 4, 5) through the canonical gates -- (GR-28)(iv) REFUTED
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --repair   # what survives: per-shape (GR-15) at every witness; the flip distance (3 at W5)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --validate # all four in one process (~2 s -- inside the 600 s budget)

Argument state: session draft `fanout-GUNIF.md` (to be merged into
`notes/Pencil-informal.md` §(K-grid) as Steps G34+; labels (GR-29)+ per the
2026-08-13 GUNIF prep in `notes/Pencil-fanout.md`).

THE DERIVED STRUCTURE THE MODES REST ON (proofs in the draft; asserted here
rather than trusted).

Alternation (closure.alternation_classes): colours alternate along every
branch, one free bit per branch.  Hence at `Lambda = empty` (lengths >= 2,
and <= 5 by the PROVEN (SD-6)):

  l = 2: A(beta) = 1, darts (A, B)      -- one A end, one B end, always
  l = 3: A = 2 darts (A, A)  or  A = 1 darts (B, B)   -- the branch bit
  l = 4: A = 2, darts (A, B)                          -- cost 1 always
  l = 5: A = 3 darts (A, A)  or  A = 2 darts (B, B)   -- cost 2 or 1

COST-0 MENU (the (GR-28) core-path menu; --menu certifies completeness):
a cost-0 core path (every branch A(beta) = 1, every interior hub AA) is
  [l2]  a single length-2 branch          darts (A, B)
  [l3]  a single length-3 B-majority      darts (B, B)
  [l22] two length-2 branches, AA interior hub, darts (B, B),
        and the interior hub's THIRD dart is forced B by the mono-hub ban.
No cost-0 path has 3+ branches (a middle branch would need A darts at both
ends).  COST-1 MENU: --menu enumerates it; every member has <= 4 branches.

THE LEDGER (draft Steps G34+; --ledger certifies the case list): for a 2ec
branch subset S with defect_A(S) <= 1 and cycle rank k >= 3, W_S its hub
set, z = #[l22], w3 = #[l3], ch = #chords (branches of G° - S joining two
AA interiors: forced B at both ends, hence ODD by alternation, B-majority),
the kill clauses are
  (K-bal)  every forced-B-majority odd branch (each [l3], every chord, a
           B-majority cost-1 path) needs a distinct A-majority odd partner
           somewhere in G° (balance), each costing >= 1 excess;
  (K-sd6)  (SD-6): l <= 5, so chord excess <= 3, loops of G° are dead;
  (K-cut)  (GR-25): proper W_S needs 2 d(W_S) + exc(E(W_S)) >= 7, the
           complement side the same, total excess exactly 6 (GR-21);
  (K-mono) every corner needs an A dart: only [l2] heads and A-ended
           cost-1 paths supply them;
  (K-nc1)  binding circuits (branch-level Sum(l-1) <= 4) need >= 3 runs --
           in BOTH blocks; a 2-circuit of cost-0 paths is dead outright;
  (K-cut-inner) the cut criterion applied INSIDE W_S, at corners +
           [l22] interiors (drop a multi-branch P*'s interiors; removing
           one edge of the 2ec core keeps it connected) -- the clause the
           first ledger draft missed, caught when its would-be n = 8
           candidate FAILED the habitat gate (kept as a control).
--ledger enumerates the parameter tuples and names each case's killer;
the SURVIVING cases are the candidate menu --wit realizes.  RESULT:
every n_hub <= 6 tuple dies (so the exhaustive n <= 6 sweeps could
never see a counterexample -- a theorem, not luck), the first survivors
sit at n_hub = 8, and --wit realizes one: THE CAP IS FALSE from
n_hub = 8 on, and (GR-28)(iv) holds exactly on the swept stratum.

Exact throughout (integers; rank only through gridcol.block_generic_zero's
GF(p) lower bound with exact-Q recheck through BOTH matrices, README §4
convention 2).  Rngs seeded per mode, seeds printed; no `set` printed;
nothing samples a placement (§(K-clos) (AC-9)).
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from grid import block_data, dim_Z                                     # noqa: E402
from gridwit import subgraph_g                                         # noqa: E402
from gridcol import block_generic_zero, dim_W_branch, subdivide        # noqa: E402
from cflank import (admissible, cubic_habitat, flip_branch,            # noqa: E402
                    hub_model, nc1_violations)
from gcap import branch_stats, g_formula, subset_eidx                  # noqa: E402

U_SEED = 20260813


# ----------------------------------------------- the constructed witnesses --
#
# Three candidates, one per cycle rank k in {3, 4, 5} -- each realizing a
# surviving case of the ledger; every ledger constraint is tight somewhere,
# so these are the analysis' own worst cases in CFLANK's --adv idiom.
#
# W5 (n_hub = 16, k = 5, defect 0, g = 3):
#   corners c0..c7 on an all-[l2] 8-cycle, cyclically A-oriented; an [l22]
#   perfect matching c_{i-1} -- m_i -- c_{i+3} (interiors m1..m4 all AA);
#   S = cycle + matching: 16 branches, 12 hubs, defect_A(S) = 0, g = 3;
#   chord m1--m2 length 5 B-majority (B-forced at both AA ends => odd);
#   boundary l2s m3--o3, m4--o4 (d(W_S) = 2, outside ends deliver A);
#   outside K4-minus-edge on o1..o4, lengths (3,2,2,2,4) -- exc 3 exactly
#   ((GR-25) forces the 3/3 split), o1o2 = l3 A-majority balancing the
#   chord.
#
# W3 (n_hub = 10, k = 3, defect 1, g = 2):
#   core K4 on v1..v4 with P* = v1v2 an [l2,l2] cost-1 path whose interior
#   mNA has darts (B, B) -- both outer darts A -- so its third dart is
#   FREE, not B-forced; two [l22] paths (v1v4 via m1, v2v3 via m2), two
#   plain l2s (v1v3 head at v3, v2v4 head at v4), one l3B (v3v4);
#   d(W_S) = 3 boundary l2s from m1, m2 (A at the outside end) and mNA
#   (played A at mNA, so B at the outside end -- the free dart is what
#   defuses the mono-hub crash at the outside); outside = a triangle
#   o1o2o3 with lengths (5, 4, 2), the l5 A-majority balancing the
#   l3B.  S = the 9 core branches: defect_A(S) = 1 (mNA's non-AA
#   indicator), g = 2.  The shape has NO binding circuit at all, so NC1
#   is VACUOUS here -- the cap fails with room to spare.
#
# W4 (n_hub = 12, k = 4, defect 1, g = 2): core = prism on v1..v6
#   (triangles 123, 456, matching 14, 25, 36) with P* = v1v2 a single l3
#   A-majority (both darts A), l3Bs at v2v3 and v1v4, [l22]s at v4v5 (m1)
#   and v3v6 (m2), l2 heads serving v3, v4, v5, v6; boundary + outside
#   exactly as W5's.  S = the 11 core branches: defect_A(S) = 1 (P*'s
#   cost), g = 2.

# W5 hubs: c0..c7 = 0..7, m1..m4 = 8..11, o1..o4 = 12..15
W5_SPECS = (
    [(i, (i + 1) % 8, 2) for i in range(8)]
    + [(0, 8, 2), (8, 4, 2), (1, 9, 2), (9, 5, 2),
       (2, 10, 2), (10, 6, 2), (3, 11, 2), (11, 7, 2)]
    + [(8, 9, 5)]
    + [(10, 14, 2), (11, 15, 2)]
    + [(12, 13, 3), (12, 14, 2), (13, 14, 2), (12, 15, 2), (13, 15, 4)]
)
W5_FIRST = (['B'] * 8
            + ['B', 'A', 'B', 'A', 'B', 'A', 'B', 'A']
            + ['B']
            + ['B', 'B']
            + ['A', 'B', 'A', 'A', 'B'])
W5_S = list(range(16))

# W3 hubs: v1..v4 = 0..3, m1 = 4, m2 = 5, mNA = 6, o1..o3 = 7..9
W3_SPECS = [
    (0, 6, 2), (6, 1, 2),            # P* halves: A at v1, A at v2
    (0, 2, 2), (1, 3, 2),            # l2 heads at v3, v4
    (2, 3, 3),                       # l3B v3v4
    (0, 4, 2), (4, 3, 2),            # [l22] v1v4 via m1
    (1, 5, 2), (5, 2, 2),            # [l22] v2v3 via m2
    (4, 7, 2), (5, 8, 2), (6, 9, 2),  # boundary m1-o1, m2-o2, mNA-o3
    (7, 8, 5), (7, 9, 4), (8, 9, 2),  # outside triangle (5, 4, 2)
]
W3_FIRST = ['A', 'B',
            'B', 'B',
            'B',
            'B', 'A',
            'B', 'A',
            'B', 'B', 'A',
            'A', 'B', 'B']
W3_S = list(range(9))

# W3b hubs: v1..v4 = 0..3, mA1 = 4, mA2 = 5 (P* interiors), m = 6, o = 7
W3B_SPECS = [
    (0, 4, 2), (4, 5, 3), (5, 1, 2),  # P* = (2, 3A, 2), both interiors AA
    (0, 2, 2),                        # l2 head at v3
    (0, 3, 2),                        # l2 head at v1
    (1, 2, 2),                        # l2 head at v2
    (1, 3, 2),                        # l2 head at v4
    (2, 6, 2), (6, 3, 2),             # [l22] v3v4 via m
    (4, 7, 5),                        # boundary mA1-o, l5 B-majority
    (5, 7, 4),                        # boundary mA2-o, l4
    (6, 7, 2),                        # boundary m-o, l2
]
W3B_FIRST = ['B', 'A', 'A',
             'B',
             'A',
             'A',
             'B',
             'B', 'A',
             'B',
             'B',
             'B']
W3B_S = list(range(9))

# W4 hubs: v1..v6 = 0..5, m1 = 6, m2 = 7, o1..o4 = 8..11
W4_SPECS = [
    (0, 1, 3),                       # P* = l3 A-majority
    (0, 2, 2),                       # l2 head at v3
    (1, 2, 3),                       # l3B v2v3
    (3, 6, 2), (6, 4, 2),            # [l22] v4v5 via m1
    (3, 5, 2),                       # l2 head at v4
    (4, 5, 2),                       # l2 head at v6
    (0, 3, 3),                       # l3B v1v4
    (1, 4, 2),                       # l2 head at v5
    (2, 7, 2), (7, 5, 2),            # [l22] v3v6 via m2
    (6, 10, 2), (7, 11, 2),          # boundary m1-o3, m2-o4
    (8, 9, 3), (8, 10, 2), (9, 10, 2), (8, 11, 2), (9, 11, 4),
]
W4_FIRST = ['A',
            'B',
            'B',
            'B', 'A',
            'A',
            'B',
            'B',
            'B',
            'B', 'A',
            'B', 'B',
            'A', 'B', 'A', 'A', 'B']
W4_S = list(range(11))

# W3M -- the MINIMAL witness, n_hub = 8: hubs v1..v4 = 0..3, then the
# three [l22] interiors m14 = 4, m23 = 5, m34 = 6, singleton outside
# o = 7.  Core K4: P* = v1v2 a SINGLE l3 A-majority (n_int = 0, so the
# (K-cut-inner) clause cannot fire -- P* stays inside the inner cut),
# l2 heads at v3 and v4, [l22]s on 14, 23, 34; all three boundary
# branches leave AA interiors (B-forced), lengths (5, 4, 2): the l5
# B-majority balances P*, and o's darts are (B, A, A).  The shape has
# NO binding circuit (NC1 vacuous); S = the 9 core branches, k = 3,
# defect_A(S) = 1 (P*'s cost), g = 2.
W3M_SPECS = [
    (0, 1, 3),                        # P* = l3 A-majority
    (0, 2, 2), (1, 3, 2),             # l2 heads at v3, v4
    (0, 4, 2), (4, 3, 2),             # [l22] v1v4 via m14
    (1, 5, 2), (5, 2, 2),             # [l22] v2v3 via m23
    (2, 6, 2), (6, 3, 2),             # [l22] v3v4 via m34
    (4, 7, 5), (5, 7, 4), (6, 7, 2),  # boundary to o: (5, 4, 2)
]
W3M_FIRST = ['A',
             'B', 'B',
             'B', 'A',
             'B', 'A',
             'B', 'A',
             'B', 'B', 'B']
W3M_S = list(range(9))

WITNESSES = [
    ('W3M (n=8, k=3, defect 1) MINIMAL', 8, W3M_SPECS, W3M_FIRST,
     W3M_S, 2),
    ('W3 (n=10, k=3, defect 1)', 10, W3_SPECS, W3_FIRST, W3_S, 2),
    ('W4 (n=12, k=4, defect 1)', 12, W4_SPECS, W4_FIRST, W4_S, 2),
    ('W5 (n=16, k=5, defect 0)', 16, W5_SPECS, W5_FIRST, W5_S, 3),
]


def wit_colouring(specs, first):
    """The explicit alternating colouring: spec i's path edges get
    first[i], flip(first[i]), ... in u-to-w order (subdivide's own edge
    order)."""
    col = {}
    for i, (u, w, L) in enumerate(specs):
        prev = ('h', u)
        c = first[i]
        for j in range(L - 1):
            cur = ('i', i, j)
            col[(prev, cur)] = c
            c = 'A' if c == 'B' else 'B'
            prev = cur
        col[(prev, ('h', w))] = c
    return col


def spec_to_hm_index(specs, hm):
    """Map spec index -> hub_model branch index, by hub-end pair (all pairs
    distinct in WIT_SPECS; asserted)."""
    pairs = {}
    for k, (u, w) in enumerate(hm['ends']):
        key = frozenset((u, w))
        assert key not in pairs, "parallel branches: mapping by ends unsafe"
        pairs[key] = k
    out = []
    for (u, w, _L) in specs:
        out.append(pairs[frozenset((('h', u), ('h', w)))])
    return out


def check_candidate(name, n, specs, first, S_idx, expect, rng):
    """One candidate through the canonical gates.  Returns the verified
    exact g of its subset S (asserted == `expect`), or raises at the gate
    that kills it."""
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    assert len(specs) == 3 * n // 2, "not cubic"
    assert sum(L - 2 for L in lens) == 6, "excess is not 6"
    # gate 1: habitat, by the proven (GR-25) cut criterion (class_shape's
    # 2^M kslide scan is out of reach at these M; (GR-25) is proven and
    # asserted equivalent to it on the whole n <= 6 pool by cflank --law)
    assert cubic_habitat(n, hedges, lens), \
        f"{name}: OUT of habitat -- the ledger missed a clause"
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    V = len(allverts)
    assert 5 * len(edges) == 6 * (V - 1), "not tight"
    hm = hub_model(edges)
    assert hm is not None
    assert all(L >= 2 for L in hm['lens']), "Lambda != empty"
    # gate 2: the colouring is admissible
    col = wit_colouring(specs, first)
    assert set(col) == set(edges), "colouring/edge mismatch"
    assert admissible(edges, allverts, hm, col), \
        f"{name}: the witness colouring is NOT admissible"
    # gate 3: NC1 passes (run counts, exact at Lambda = empty)
    bad = nc1_violations(hm, col, edges, allverts)
    assert not bad, f"{name}: NC1 fails at circuits {bad}"
    nbind = len(hm['binding'])
    print(f"  {name}: habitat OK (cut criterion, 2^{n} subsets); tight, "
          f"|V| = {V}, M = {len(specs)}; admissible OK; NC1 OK "
          f"({nbind} binding circuit{'s' if nbind != 1 else ''}"
          f"{', i.e. NC1 VACUOUS here' if nbind == 0 else ''})")
    # gate 4: the exact g of S, through subgraph_g (the (GR-8) functional,
    # a PROOF of generic dim Z >= g at balance) and the (GR-28) formula
    s2h = spec_to_hm_index(specs, hm)
    S_hm = [s2h[i] for i in S_idx]
    bdA = block_data(edges, allverts, col, 'A')
    gS = subgraph_g(bdA, subset_eidx(bdA, hm, S_hm))
    stats = branch_stats(hm, col, 'A')
    b, q = len(S_hm), len({v for i in S_hm for v in hm['ends'][i]})
    kk = b - q + 1
    gF = g_formula(hm, stats, tuple(S_hm), kk)
    assert gS == gF, f"{name}: formula vs subgraph_g disagree"
    # gate 5: rank corroboration -- no dim Z = 0 draw should exist, and
    # the measured dim Z at exact seeded draws, through BOTH matrices
    sv = block_generic_zero(bdA, hm['hubs'], hm['branches'], rng, draws=6)
    assert sv is None or gS <= 0, \
        f"{name}: dim Z = 0 draw at a g >= 1 block: (GR-8) itself broken"
    from fractions import Fraction as F
    dims = []
    for _ in range(3):
        sval = {c: F(rng.randint(1, 10 ** 4)) for c in set(bdA['cls'])}
        dW = dim_W_branch(bdA, hm['hubs'], hm['branches'], sval=sval)
        dZ = dim_Z(bdA, sval=sval)
        assert dW == dZ, f"{name}: branch model vs grid.dim_Z disagree"
        dims.append(dW)
    print(f"    S: {b} branches, {q} hubs, k = {kk}; exact subgraph_g(S) "
          f"= {gS} = formula; no dim Z = 0 draw in 6; dim Z at 3 exact "
          f"draws (both matrices): {dims}")
    assert gS == expect, f"{name}: g = {gS}, expected {expect}"
    return gS


def leg_wit():
    """[GUN-3] the adjudication: three constructed candidates (k = 3, 4,
    5 at n_hub = 10, 12, 16) through the canonical gates.  (GR-28)(iv) is
    REFUTED iff a gate-clean NC1-passing admissible block has exact
    subgraph_g >= 2."""
    import random
    print(f"[GUN-3] the constructed witnesses (seed {U_SEED + 3})")
    rng = random.Random(U_SEED + 3)
    # (SD-6) control: W5 with its chord at length 7 must be REJECTED (the
    # ledger's k = 3 improper candidate dies exactly on this clause)
    lens7 = [L for (_u, _w, L) in W5_SPECS]
    lens7[16] = 7   # chord excess 5
    lens7[19] = 3   # keep total excess at 6: 5 + 1
    lens7[23] = 2
    assert sum(L - 2 for L in lens7) == 6
    assert not cubic_habitat(16, [(u, w) for (u, w, _L) in W5_SPECS],
                             lens7), \
        "(SD-6) control failed: a length-7 chord was accepted"
    print("  (SD-6) control: the length-7-chord variant is REJECTED by "
          "the habitat gate, as it must be")
    # (K-cut-inner) control: the ledger's would-be n_hub = 8 candidate
    # (P* = (2, 3A, 2), K4 core, singleton outside) is OUT of habitat --
    # the cut at corners + [l22] interiors (i.e. minus P*'s interiors)
    # has 2d + exc = 6 < 7.  This is the clause the first ledger draft
    # missed, caught because the realization attempt FAILED the gate.
    assert not cubic_habitat(8, [(u, w) for (u, w, _L) in W3B_SPECS],
                             [L for (_u, _w, L) in W3B_SPECS]), \
        "(K-cut-inner) control failed: the n = 8 candidate was accepted"
    print("  (K-cut-inner) control: the n_hub = 8 candidate (P* = "
          "(2,3A,2), K4 core, singleton outside) is REJECTED by the "
          "habitat gate -- the inner cut at corners + [l22] interiors "
          "is what kills it, the clause the ledger now carries")
    got = []
    for (name, n, specs, first, S_idx, expect) in WITNESSES:
        got.append(check_candidate(name, n, specs, first, S_idx, expect,
                                   rng))
    print(f"  => (GR-28)(iv) IS REFUTED at every k in {{3, 4, 5}}: "
          f"NC1-passing admissible blocks of Lambda = empty D = 0 "
          f"habitat shapes with exact max_P g(P) = {got} at n_hub = "
          f"8, 10, 12, 16 -- all outside the swept n_hub <= 6 stratum, "
          f"which the ledger proves cannot contain one; n_hub = 8 is "
          f"MINIMAL (the ledger kills every tuple below it)")
    print()


# --------------------------------------------- [GUN-1] --menu: the dart menu

def path_menu(max_m=5):
    """Enumerate every core path of <= max_m branches (lengths 2..5, one
    alternation bit each) with cost <= 1, canonicalized up to reversal.
    cost(P) = Sum(A(beta) - 1) + #(non-AA interior hubs); attributes per
    entry: (lens, outer darts, exc, h = #A outer darts, n_int, i_free =
    #non-AA interiors, nA/nB = #A-/B-majority odd branches).

    F11: this IS the exhaustiveness computation for the (GR-29) menu --
    the caller asserts the cost-0 menu is exactly {[l2], [l3], [l22]} and
    that no cost <= 1 path exceeds 4 branches (an l2 middle branch must
    be adjacent to the one non-AA interior, so <= 2 middles), max_m = 5
    giving margin."""
    import itertools
    out = {0: {}, 1: {}}
    for m in range(1, max_m + 1):
        for lens in itertools.product((2, 3, 4, 5), repeat=m):
            for bits in itertools.product((0, 1), repeat=m):
                acnt, du, dw = [], [], []
                for L, b in zip(lens, bits):
                    acnt.append((L + b) // 2 if b else L // 2)
                    du.append('A' if b else 'B')
                    dw.append('A' if (b ^ ((L - 1) % 2)) else 'B')
                cost = sum(a - 1 for a in acnt)
                if cost > 1:
                    continue
                aa = [dw[t] == 'A' and du[t + 1] == 'A'
                      for t in range(m - 1)]
                cost += sum(1 for f in aa if not f)
                if cost > 1:
                    continue
                desc = (lens, (du[0], dw[-1]), tuple(aa))
                rev = (lens[::-1], (dw[-1], du[0]), tuple(aa[::-1]))
                key = min(desc, rev)
                h = (du[0] == 'A') + (dw[-1] == 'A')
                nA = sum(1 for L, b in zip(lens, bits) if L % 2 and b)
                nB = sum(1 for L, b in zip(lens, bits) if L % 2 and not b)
                out[cost][key] = dict(
                    lens=lens, outer=(du[0], dw[-1]),
                    exc=sum(L - 2 for L in lens), h=h, n_int=m - 1,
                    i_free=sum(1 for f in aa if not f), nA=nA, nB=nB)
    return out


def leg_menu():
    """[GUN-1] the (GR-29) menu, machine-certified complete."""
    print("[GUN-1] the dart menu (exhaustive over paths of <= 5 branches, "
          "lengths 2..5, all bits)")
    menu = path_menu()
    m0 = menu[0]
    # the cost-0 menu is EXACTLY {[l2], [l3], [l22]}
    expect0 = {
        ((2,), ('A', 'B'), ()),
        ((2,), ('B', 'A'), ()),          # [l2] read from the other end
        ((3,), ('B', 'B'), ()),          # [l3] B-majority
        ((2, 2), ('B', 'B'), (True,)),   # [l22], AA interior
    }
    got0 = set(m0)
    canon = {min(d, (d[0][::-1], d[1][::-1], d[2][::-1])) for d in expect0}
    assert got0 == canon, f"cost-0 menu differs: {got0} vs {canon}"
    assert all(v['n_int'] <= 1 for v in m0.values())
    print(f"  cost-0 menu: EXACTLY {{[l2] (darts A,B), [l3] B-maj (B,B), "
          f"[l22] AA-interior (B,B)}} -- {len(m0)} canonical entries, "
          f"none with >= 3 branches; only [l2] presents an A dart")
    m1 = menu[1]
    assert all(len(v['lens']) <= 4 for v in m1.values()), \
        "a cost-1 path with 5 branches exists -- the ledger's menu is short"
    assert all(v['exc'] <= 3 for v in m1.values())
    print(f"  cost-1 menu: {len(m1)} canonical entries, all <= 4 branches "
          f"(an l2 middle must touch the non-AA interior), excess <= 3:")
    for key in sorted(m1, key=str):
        v = m1[key]
        print(f"    lens {v['lens']} outer {v['outer']} exc {v['exc']} "
              f"h {v['h']} interiors {v['n_int']} (free {v['i_free']}) "
              f"odd A-maj/B-maj {v['nA']}/{v['nB']}")
    # the 2-circuit kill: two cost-0 paths as a digon always violate NC1
    worst = 0
    for p in m0.values():
        for q in m0.values():
            for pd in (p['outer'], p['outer'][::-1]):
                for qd in (q['outer'], q['outer'][::-1]):
                    dA = sum(1 for t in (0, 1)
                             if not (pd[t] == 'A' and qd[t] == 'A'))
                    worst = max(worst, dA)
    assert worst <= 2
    print(f"  the 2-circuit kill: a digon of two cost-0 paths has "
          f"defect_A <= {worst} < 3 at every dart orientation -- NC1 "
          f"violated outright, so the core is SIMPLE at defect 0")
    print()


# ------------------------------------------ [GUN-2] --ledger: the case list

def leg_ledger():
    """[GUN-2] the budget ledger: enumerate every parameter tuple a
    defect <= 1 configuration can have, and certify that each one with
    n_hub <= 8 dies at a NAMED clause -- so the exhaustively swept
    n_hub <= 6 stratum (and n_hub = 8 with it) provably cannot contain a
    counter-configuration, and the witnesses' n_hub = 10 is MINIMAL.

    The kill clauses are all NECESSARY conditions, so every kill is a
    proof; a surviving tuple is a CANDIDATE (realization is --wit's job,
    done at n = 10, 12, 16)."""
    import itertools
    print("[GUN-2] the budget ledger (k <= 6 suffices: k >= 7 forces "
          "|W_S| >= 12, n_hub >= 13)")
    menu1 = list(path_menu()[1].values())
    # Every cost-1 path has at most ONE non-AA interior (each costs 1)
    assert all(v['i_free'] <= 1 for v in menu1)
    kills = {}
    survivors = []

    def kill(tag):
        kills[tag] = kills.get(tag, 0) + 1

    # A chord joins two W_S interiors.  AA--AA chords are B-forced at
    # both ends, hence ODD (alternation) with excess in {1, 3} ((SD-6))
    # and B-majority.  A chord using THE free dart (<= 1 exists, at a
    # non-AA cost-1 interior) may instead be even (exc {0, 2}, no
    # balance debt) or odd (B at the free end too).  `fd` records the
    # free dart's disposition.
    for pstar in [None] + menu1:
        h = pstar['h'] if pstar else 0
        n_int = pstar['n_int'] if pstar else 0
        excP = pstar['exc'] if pstar else 0
        nA_in = pstar['nA'] if pstar else 0
        nB_p = pstar['nB'] if pstar else 0
        i_free = pstar['i_free'] if pstar else 0
        for k in range(3, 7):
            npaths = 3 * (k - 1)
            for a in range(0, 2 * (k - 1) + 1):
                x = 2 * (k - 1) + a - h
                rem = npaths - x - (1 if pstar else 0)
                if x < 0 or rem < 0:
                    continue
                for w3 in range(rem + 1):
                    z = rem - w3
                    F = z + n_int             # free darts of W_S
                    WS = 2 * (k - 1) + z + n_int
                    for ch in range(F // 2 + 1):
                        bdry = F - 2 * ch
                        for fd in (('bdry', 'chord') if i_free else
                                   ('none',)):
                            if fd == 'chord' and ch == 0:
                                continue
                            nfree_b = 1 if fd == 'bdry' else 0
                            ch_aa = ch - (1 if fd == 'chord' else 0)
                            ch0 = ((0, 1, 2, 3),) * (ch - ch_aa) + \
                                  ((1, 3),) * ch_aa
                            for chexc in itertools.product(*ch0):
                                excW = w3 + excP + sum(chexc)
                                nB_in = w3 + nB_p + \
                                    sum(1 for e in chexc if e % 2)
                                if excW > 6:
                                    kill('budget: exc(E(W_S)) > 6')
                                    continue
                                if bdry == 0:
                                    if excW != 6:
                                        kill('improper: excess != 6')
                                    elif nA_in != nB_in:
                                        kill('improper: unbalanced')
                                    else:
                                        survivors.append(
                                            ('improper', k, WS))
                                    continue
                                if bdry == 1:
                                    kill('bridge: d(W_S) = 1')
                                    continue
                                if 2 * bdry + excW < 7:
                                    kill('cut at W_S: 2d + exc < 7')
                                    continue
                                # (K-cut-inner) the cut at corners +
                                # [l22] interiors, i.e. W_S minus a
                                # multi-branch P*'s interiors (removing
                                # ONE edge of the 2ec core keeps it
                                # connected, so this W' is always legal
                                # and proper).  Its boundary: the z
                                # [l22] darts not chorded AMONG
                                # THEMSELVES, plus P*'s two end darts,
                                # plus chords half-attached to P*
                                # interiors; its excess: w3 plus the
                                # chords fully inside.  Sound kill:
                                # even the MAXIMAL f over chord
                                # attachments stays < 7.
                                if n_int >= 1:
                                    fmax = -1
                                    exs = sorted(chexc, reverse=True)
                                    for zz in range(ch + 1):
                                        for zp in range(ch - zz + 1):
                                            pp = ch - zz - zp
                                            if 2 * zz + zp > z:
                                                continue
                                            if zp + 2 * pp > n_int:
                                                continue
                                            fI = 2 * ((z - 2 * zz - zp)
                                                      + 2 + zp) \
                                                + w3 + sum(exs[:zz])
                                            fmax = max(fmax, fI)
                                    if fmax < 7:
                                        kill('cut inside W_S: corners +'
                                             ' [l22] interiors')
                                        continue
                                # (o1) singleton outside: bdry = 3
                                if bdry == 3:
                                    if WS + 1 > 8:
                                        survivors.append(
                                            ('singleton', k, WS + 1))
                                    elif singleton_outside_lives(
                                            nfree_b, nA_in, nB_in,
                                            excW):
                                        survivors.append(
                                            ('singleton', k, WS + 1))
                                    else:
                                        kill('singleton outside: '
                                             'mono/balance enumeration')
                                # (o2) one outside component >= 2 hubs
                                pool = 6 - excW
                                if 2 * bdry + pool < 7:
                                    kill('cut at the outside: '
                                         '2d + exc < 7')
                                elif abs(nB_in - nA_in) > pool:
                                    kill('balance: majority surplus '
                                         'exceeds the excess pool')
                                else:
                                    survivors.append(
                                        ('outside>=2', k, WS + 2))
                                # (o3) >= 2 outside components needs
                                # d >= 4, i.e. bdry >= 4, WS >= 2(k-1)+4
                                # >= 8, n >= 10: never at n <= 8; folded
                                # into (o2)'s survivor n lower bound.
    small = [s for s in survivors if s[2] <= 6]
    assert not small, f"a tuple with n_hub <= 6 survives: {small[:3]}"
    nmin = min(s[2] for s in survivors)
    print(f"  every parameter tuple with n_hub <= 6 is KILLED; kill "
          f"histogram over all tuples:")
    for tag in sorted(kills):
        print(f"    {kills[tag]:6d}  {tag}")
    n8 = sorted({(s[0], s[1]) for s in survivors if s[2] <= 8})
    print(f"  surviving candidate tuples first appear at n_hub = {nmin} "
          f"(as ('kind', k) pairs at n <= 8): {n8}")
    assert nmin == 8 and all(s[0] == 'singleton' and s[1] == 3
                             for s in survivors if s[2] <= 8), \
        "the n = 8 survivors are not the k = 3 singleton family"
    print(f"  => the swept n_hub <= 6 stratum provably contains NO "
          f"defect <= 1 configuration at k >= 3: the 549 172-block "
          f"evidence for (GR-28)(iv) was exhaustive over EXACTLY the "
          f"stratum that cannot exhibit the failure; the first "
          f"surviving tuples are at n_hub = 8 -- and --wit REALIZES "
          f"one (W3M), so the boundary is EXACT: the cap is a theorem "
          f"at n_hub <= 6 and false from n_hub = 8 on")
    print()


def singleton_outside_lives(nfree, nA_in, nB_in, excW):
    """The one ledger case needing a dart-level enumeration: a singleton
    outside hub `o` receiving 3 boundary branches.  Sources: AA interiors
    (B-forced source dart) and at most `nfree` (<= 1) free cost-1
    interiors.  `o` lives iff some choice of boundary lengths (2..5,
    total excess 6 - excW, (SD-6)) and free-dart colours leaves `o`
    non-monochromatic AND the whole shape balanced (odd boundary from an
    AA interior is forced B-majority; odd boundary from the free interior
    chooses its majority)."""
    import itertools
    excB = 6 - excW
    for lens in itertools.product((2, 3, 4, 5), repeat=3):
        if sum(L - 2 for L in lens) != excB:
            continue
        for freeslots in itertools.combinations(range(3), nfree):
            for freedarts in itertools.product('AB', repeat=nfree):
                src = ['B'] * 3
                for s, d in zip(freeslots, freedarts):
                    src[s] = d
                odart, dA, dB = [], 0, 0
                for t in range(3):
                    if lens[t] % 2 == 0:
                        odart.append('A' if src[t] == 'B' else 'B')
                    else:
                        odart.append(src[t])
                        if src[t] == 'A':
                            dA += 1
                        else:
                            dB += 1
                if len(set(odart)) == 1:
                    continue                    # mono hub at o
                if nA_in + dA != nB_in + dB:
                    continue                    # unbalanced
                return True
    return False
#
# Two questions at each witness shape, both answered with rank-grade
# certificates (an exact rational dim Z = 0 point in BOTH blocks, through
# BOTH matrices -- by (GR-8)'s proven >= direction that is a PROOF of
# a = 0 and max g <= 0, i.e. of fully-good, with no subset scan):
#   (i)  does SOME admissible colouring certify dim Z = 0 in both blocks?
#        (per-shape (GR-15) -- i.e. does the refutation of the cap leave
#        (GR-15) itself standing at the witness shapes?)
#   (ii) the balance-preserving flip distance from the witness colouring
#        to such a certificate (the fate of Step G32's measured <= 2 law).

def rank_good(edges, allverts, hm, col, rng):
    """A PROOF of fully-good at `col`, or False: admissible + NC1 + an
    exact rational dim Z = 0 point in both blocks through both matrices."""
    if not admissible(edges, allverts, hm, col):
        return False
    if nc1_violations(hm, col, edges, allverts):
        return False
    for mine in ('A', 'B'):
        bd = block_data(edges, allverts, col, mine)
        sv = block_generic_zero(bd, hm['hubs'], hm['branches'], rng,
                                draws=4)
        if sv is None:
            return False
        assert dim_W_branch(bd, hm['hubs'], hm['branches'], sval=sv) == 0
        assert dim_Z(bd, sval=sv) == 0, "branch model vs grid.dim_Z"
    return True


def bit_colouring(specs, bits):
    return wit_colouring(specs, ['A' if b else 'B' for b in bits])


def leg_repair():
    """[GUN-4] per-shape (GR-15) and the flip distance at the witnesses."""
    import random
    import itertools
    import time
    print(f"[GUN-4] what survives at the witnesses (seed {U_SEED + 4})")
    rng = random.Random(U_SEED + 4)
    t0 = time.time()
    for (name, n, specs, first, S_idx, expect) in WITNESSES:
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = hub_model(edges)
        M = len(specs)
        # ---- (i) per-shape (GR-15): seeded random colouring search ----
        found = None
        for t in range(1, 2001):
            bits = [rng.randint(0, 1) for _ in range(M)]
            col = bit_colouring(specs, bits)
            if rank_good(edges, allverts, hm, col, rng):
                found = t
                break
        assert found is not None, \
            f"{name}: no fully-good colouring in 2000 draws"
        print(f"  {name}: per-shape (GR-15) HOLDS -- a fully-good "
              f"colouring (exact dim Z = 0 point, both blocks, both "
              f"matrices) at random draw {found}  "
              f"[{time.time() - t0:.0f}s]")
        # ---- (ii) flip distance from the witness colouring ----
        col0 = wit_colouring(specs, first)
        lens = [L for (_u, _w, L) in specs]
        s2h = spec_to_hm_index(specs, hm)
        evens = [k for k in range(M) if lens[k] % 2 == 0]
        odds = [k for k in range(M) if lens[k] % 2]
        oddpairs = [[k1, k2] for i, k1 in enumerate(odds)
                    for k2 in odds[i + 1:]]

        def moves_of_size(s):
            # balance-preserving move = a set of even flips plus any
            # number of odd PAIRS; size = number of flipped branches
            out = [list(evs) for evs in itertools.combinations(evens, s)]
            if s >= 2:
                for op in oddpairs:
                    for evs in itertools.combinations(evens, s - 2):
                        out.append(op + list(evs))
            return out

        dist = None
        for s in (1, 2, 3):
            for mv in moves_of_size(s):
                c2 = col0
                for k in mv:
                    c2 = flip_branch(edges, c2, hm['branches'][s2h[k]][2])
                if rank_good(edges, allverts, hm, c2, rng):
                    dist = s
                    break
            if dist is not None:
                break
        print(f"    flip distance from the witness colouring to a "
              f"rank-certified fully-good one: "
              f"{dist if dist is not None else '> 3'} "
              f"(balance-preserving flips; Step G32's measured law said "
              f"<= 2 on the n <= 6 stratum)  [{time.time() - t0:.0f}s]")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('menu', 'ledger', 'wit', 'repair', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.menu, a.ledger, a.wit, a.repair])
    if run or a.menu:
        leg_menu()
    if run or a.ledger:
        leg_ledger()
    if run or a.wit:
        leg_wit()
    if run or a.repair:
        leg_repair()
    print("OK")


if __name__ == '__main__':
    main()
