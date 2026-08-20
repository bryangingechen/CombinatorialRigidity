"""§(K-grid) direction GTMPL (2026-08-19) driver -- ledger attack (c) at the
next stratum: is the AA-GLUE configuration realizable at `n_hub >= 10`, where
AGLU left it?  (GR-76)(iv) narrows `n_hub = 10` to exactly THREE
counting-satisfiable templates
`(|F1|, |F2|, |W|) in {(4,0,1), (2,1,2), (0,2,3)}` with
`(n_2, n_3, |X|) = (4,4,2)`, `|T| = 10`, `q_T <= 1`; the counting side is
satisfiable there, so what must be added is the COLOURING side -- the 2-1
dart pattern at each hub off `T`, the mono-hub ban, and the (GR-25) cut
criterion.  This driver adds exactly that, and the answer comes in two
halves that meet at an EXACT BOUNDARY.

A `w4/` leaf beside `aglu.py`, importing `aglu.py` / `cflank.py` / `gcap.py` /
`gexist.py` / `gorient.py` / `grid.py` / `gridcol.py` / `gridwit.py` /
`gunif.py` READ-ONLY (README §2: the (K-grid) sub-arc is a genuine chain and
`aglu.py` is the direction immediately below this one -- its `chunks_of`,
`crossing_pairs`, `admissible_bits`, `dartmask`, `degmap`, `jfree` and
`cubic_iso_classes` are the LANDED devices for this exact question, each
cross-certified against the canonical layer in `aglu --val`, so reusing them
is rule 3 and reimplementing them would be a divergence).
Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --charge  # (GR-79)/(GR-80) ingredients: the universal dart identity + the 2-1 ledger, EXHAUSTIVE on the complete n_hub <= 6 stratum
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --frame   # (GR-79): the T-frame ledger, colouring-free, at EVERY slack-0 J-free crossing pair at n_hub = 4, 6, 8
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --tpl     # (GR-82): the three (GR-76)(iv) templates KILLED by enumeration; n_hub = 12/14 too; n_hub = 16 SURVIVES (the control)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --min     # (GR-82): the exhaustive integer search for the least feasible n_hub -- 16, with its full solution list
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --wit     # (GR-83): the n_hub = 16 WITNESS -- habitat-gated, admissible, rank-certified, the (GR-38) kill FAILING
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --e1      # (GR-83): the E1 control at the witness shape, plus the witness family (the phenomenon is not a knife edge)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --lam     # (GR-84): the residual and laminarity census AT THE WITNESS COLOURING -- what else breaks at n_hub = 16
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --val     # every local device cross-certified against the canonical layer

Argument state: session draft `notes/Pencil-draft-GTMPL.md` (to be merged into
`notes/Pencil-informal-grid.md` §(K-grid) as Steps G98-G103; labels
(GR-79)-(GR-84) per the 2026-08-19 GTMPL reservation in
`notes/Pencil-labels.md`).

THE DERIVED STRUCTURE THE MODES REST ON (proofs in the draft; ASSERTED here,
never trusted).  Throughout `Lambda = empty`, `D = 0`: `G°` cubic loopless,
lengths in [2, 5] ((SD-6)), total excess 6 ((GR-21)); chunk / interior /
corner / defect exactly as in `gexist.py`'s header; binding in A iff
`defect_A(S) <= 2`.  `T := S n S'`, `R := S - S'`, `R' := S' - S`; `n_2`,
`n_3` = the numbers of `T`-hubs of `T`-degree 2 ("interiors") and 3
("corners"); `X` = the hubs off `T`; `q_T = #(l = 3 branches of T)`.

(GR-79)  THE B-FLOODED FRAME (colouring-free consequences of
         `defect_A(T) = 0`, read straight off `gexist.defect_direct`).
         `defect_A(P) = Sum_P (A(beta) - 1) + #(non-AA degree-2-in-P hubs)`
         with every term >= 0 at `Lambda = empty`, so `defect_A(T) = 0`
         forces `A(beta) = 1` on every `T`-branch -- i.e. `l in {2, 3}` with
         the `l = 3` ones B-majority (pattern B A B) -- and every interior
         AA.  Hence (a) NO interior-interior `T`-branch (its two end darts
         would both be A, impossible at `l = 2` and A-majority at `l = 3`)
         -- which is (GR-74)(i) re-derived with no extra input; (b) every
         interior-incident `T`-branch has `l = 2` and delivers a **B** dart
         at its corner end; (c) so `q_T` counts corner-corner branches only,
         `|T| = 2 n_2 + p + q_T` with `p = #(l = 2 corner-corner branches)`,
         and `2|T| = 2 n_2 + 3 n_3` gives the CORNER LEDGER
             2p = 3 n_3 - 2 n_2 - 2 q_T;
         (d) the A-darts at corners are EXACTLY the `p` A-ends of the `l = 2`
         corner-corner branches, one apiece.

(GR-80)  THE CORNER CHARGE.  Every hub of an admissible colouring carries a
         2-1 dart pattern ((GR-33)); a corner's three darts are all
         `T`-darts, so it needs >= 1 A-dart, and by (GR-79)(d) those come
         one per `l = 2` corner-corner branch.  So `p >= n_3`, i.e.
             n_3 >= 2 n_2 + 2 q_T.
         (Against (GR-74)(iii)'s `2 n_2 <= 3 n_3` this is a factor 3
         stronger, and it is what kills the `n_hub = 8` template a THIRD
         independent way: `n_2 = n_3 = 4` violates it outright.)

(GR-81)  THE X CHARGE.  For EVERY branch, `bend(beta) = e - 2c + 1` where
         `bend` = the number of B end darts, `c = A(beta) - 1`, `e = l - 2`
         (three lines: even `l` -> `bend = 1`, odd A-majority -> 0, odd
         B-majority -> 2).  Summing over the branches off `T` with
         `Sum c = 3` ((GR-32)(iii) plus `c = 0` on `T`) and
         `Sum e = 6 - q_T` ((GR-21)) puts the B-dart count off `T` at
         `M - |T| + q_T - 6 + ... ` -- concretely, subtracting the `n_2`
         B-darts at interior free darts and the `2 n_2 + p + 2 q_T` B-darts
         at corners leaves
             #(B-darts at X hubs) = (3|X| - n_2 - 2 q_T) / 2
         EXACTLY.  The 2-1 pattern needs >= 1 B-dart at each X hub, so
             |X| >= n_2 + 2 q_T.
         (GR-76)(i) is the `>= 0` instance of the same count; this is the
         per-hub instance.

(GR-82)  THE BOUND, AND ITS TIGHTNESS.  With `n_2 >= 4` ((GR-38)(ii) via
         (GR-73)(iii)), (GR-80) and (GR-81) give
             n_hub = n_2 + n_3 + |X| >= 4 (n_2 + q_T) >= 16,
         so the AA-glue configuration is impossible at EVERY `n_hub <= 14`
         -- in particular all three (GR-76)(iv) templates are dead, each
         killed independently by either charge alone.  The bound is `n`-free
         and it is TIGHT: (GR-83).

(GR-83)  THE WITNESS.  An explicit habitat shape at `n_hub = 16` with an
         explicit admissible colouring and two crossing same-block binding
         chunks whose intersection is defect-free at slack 0 -- an AA-glue
         configuration, so the (GR-38) intersection kill FAILS there (proper
         union of defect 4).  All three charges hold with EQUALITY.

WHAT EACH MODE TESTS, one sentence each (F11; "exhaustive" / "the only" /
"forced" are their own claim class and get their own modes -- the
per-sentence table is in the draft's Verification section).

--charge  the (GR-81) dart identity and the (GR-33) 2-1 pattern asserted at
          EVERY branch of EVERY admissible colouring of the COMPLETE
          `n_hub <= 6` stratum (the landed 4920-shape pool), together with
          the two global corollaries the X charge rides on.
--frame   (GR-79)'s corner ledger asserted at EVERY slack-0 crossing chunk
          pair with a J-free intersection of EVERY hub-multigraph class at
          `n_hub = 4, 6, 8` -- colouring-free and length-free, so NO cap.
--tpl     the three (GR-76)(iv) templates ENUMERATED down to per-X-hub dart
          colours and per-corner A-dart assignments and found EMPTY, with
          each charge's kill reported separately and the number of
          (c, e)-consistent type multisets printed so the 0 survivors are
          visibly NON-vacuous (and `q_T = 2`, which (GR-76)(iv) excludes on
          counting grounds alone, shown to have none at all);
          `n_hub = 12, 14` likewise empty; `n_hub = 16` reported NON-empty,
          so the enumerator is not vacuously rejecting.
--min     the least `n_hub` admitting ANY solution of the whole aggregate
          system, by exhaustive integer search over `n_hub <= 40`.
--wit     the `n_hub = 16` witness re-verified through the CANONICAL layer
          only: `cflank.cubic_habitat`, `cflank.admissible`,
          `gexist.defect_direct`, `gorient.pair_slack`,
          `gorient.attachment_check`, and -- independently of the (GR-28)
          formula -- `gridwit.subgraph_g` plus an exact `grid.dim_Z_generic`.
--e1      the witness shape carries a fully-good admissible colouring (so no
          g-flank, E1 does not fire), and the witness generalizes across a
          parametrized family (not a single knife-edge coincidence).
--lam     at the witness COLOURING (one colouring, disclosed -- not a
          stratum scan): every binding chunk of both blocks, the crossing
          binding pairs, the inhabited kill residual, the kill failures, and
          whether two MAXIMAL binding chunks cross -- i.e. whether
          (GR-75)(iii)'s laminarity corollary extends past n_hub = 8.
--val     the two local devices asserted equal to their canonical
          counterparts: the complement chunk enumerator vs `aglu.chunks_of`,
          and the (c, e, bend) type table vs `gexist.defect_direct` /
          `gcap.branch_stats` on constructed instances.

Exact throughout (integers only; nothing here samples a placement, so
`repin.star_generic` gates nothing -- §(K-clos) (AC-9)'s discipline, as for
`aglu.py` / `gorient.py` / `cflank.py`; the one rank computation is
`grid.dim_Z_generic`, which takes the MINIMUM over seeded random label draws
precisely so no sigma-fixed special value is read as generic).  Rngs seeded
per mode, seeds printed; every printed collection is sorted.  Wall-clock
`[Ns]` annotations are inherently non-deterministic; every other byte is
seed-stable.
"""
import argparse
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from gridcol import subdivide                                          # noqa: E402
from cflank import (admissible, cubic_habitat, excess_profiles,         # noqa: E402
                    hub_model)
from gcap import branch_stats, subset_eidx                              # noqa: E402
from gexist import defect_direct, incidence                             # noqa: E402
from gorient import attachment_check, pair_slack                        # noqa: E402
from gridwit import subgraph_g                                          # noqa: E402
from grid import block_data, dim_Z, dim_Z_generic                       # noqa: E402
from gunif import wit_colouring                                         # noqa: E402
from nogood_subdiv import (deficiency, hcard_ok, hub_set,               # noqa: E402
                           triangles)
from aglu import (admissible_bits, chunks_of, crossing_pairs,           # noqa: E402
                  cubic_iso_classes, dartmask, degmap, jfree)

G_SEED = 20260819


# ----------------------------------------------------- local devices --------
#
# Two of them.  `chunks_via_complement` replaces `aglu.chunks_of` for
# PERFORMANCE only at `M = 24` and is asserted SET-EQUAL to it in --val;
# `TYPES` is the (l, majority) -> (c, e, bend) table, which has no canonical
# counterpart as a table and is asserted against `gexist.defect_direct` /
# `gcap.branch_stats` on constructed single-branch instances in --val.

# (l, ends-are-A) -> (c = A(beta) - 1, e = l - 2, bend = #B end darts).
# `ends-are-A` is None for even l (the two end darts necessarily differ).
TYPES = {
    (2, None): (0, 0, 1),
    (3, True): (1, 1, 0),
    (3, False): (0, 1, 2),
    (4, None): (1, 2, 1),
    (5, True): (2, 3, 0),
    (5, False): (1, 3, 2),
}
# the same table keyed by role, per (GR-79)/(GR-81):
#   F2 = both ends at interior free darts, which carry B  -> bend = 2
#   F1 = one end at an interior free dart                 -> bend >= 1
#   W  = neither end at T                                 -> unconstrained
ROLE_TYPES = {
    'F2': [t for t, (c, e, b) in TYPES.items() if b == 2],
    'F1': [t for t, (c, e, b) in TYPES.items() if b >= 1],
    'W': sorted(TYPES, key=str),
}


def chunks_via_complement(n, ends):
    """`aglu.chunks_of`'s family -- connected bridgeless branch subsets with
    every touched hub degree in {2, 3} -- enumerated through the COMPLEMENT.

    PERFORMANCE device.  `aglu.chunks_of` is a `2^M` scan with a `2^M`-long
    prefix table, which at `M = 24` is 16.7 M masks and ~130 MB; at a cubic
    hub `deg_S(v) in {0, 2, 3}` means the complement has degree in {3, 1, 0},
    so a chunk is exactly (a set `U` of hubs with all three darts outside `S`,
    a matching of the rest covering only its degree-3 vertices) -- a `2^n`
    scan over a handful of matchings.  Returns (branch tuple, degree map).
    --val asserts SET EQUALITY with `aglu.chunks_of` at every hub-multigraph
    class at `n_hub = 4, 6` and at seeded classes at `n_hub = 8`."""
    M = len(ends)
    out = []
    for umask in range(1 << n):
        Us = {v for v in range(n) if umask >> v & 1}
        H = [k for k in range(M)
             if ends[k][0] not in Us and ends[k][1] not in Us]
        if not H:
            continue
        degH = {}
        for k in H:
            for v in ends[k]:
                degH[v] = degH.get(v, 0) + 1
        if len(degH) != n - len(Us) or any(d < 2 for d in degH.values()):
            continue
        three = {v for v, d in degH.items() if d == 3}
        cand = [k for k in H
                if ends[k][0] in three and ends[k][1] in three]
        mats = []

        def rec(i, used, chosen):
            mats.append(frozenset(chosen))
            for j in range(i, len(cand)):
                k = cand[j]
                u, w = ends[k]
                if u in used or w in used:
                    continue
                chosen.append(k)
                used.add(u)
                used.add(w)
                rec(j + 1, used, chosen)
                chosen.pop()
                used.discard(u)
                used.discard(w)
        rec(0, set(), [])
        for mm in mats:
            ks = tuple(k for k in H if k not in mm)
            if not ks:
                continue
            deg = degmap(ends, ks)
            if any(d not in (2, 3) for d in deg.values()):
                continue
            if not _conn_bridgeless(ends, ks, deg):
                continue
            out.append((ks, deg))
    return out


def _conn_bridgeless(ends, ks, deg):
    vs = list(deg)
    adj = {v: [] for v in vs}
    for k in ks:
        u, w = ends[k]
        adj[u].append((w, k))
        adj[w].append((u, k))
    seen, st = {vs[0]}, [vs[0]]
    while st:
        v = st.pop()
        for (u, _k) in adj[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    if len(seen) != len(vs):
        return False
    for kd in ks:
        r = ends[kd][0]
        s2, st2 = {r}, [r]
        while st2:
            v = st2.pop()
            for (u, k) in adj[v]:
                if k != kd and u not in s2:
                    s2.add(u)
                    st2.append(u)
        if len(s2) != len(vs):
            return False
    return True


def hub_adarts(ends, lens, b):
    """hub -> the number of A end darts at it, from the branch bit vector `b`
    (`aglu.dartmask`'s convention: dart `2k` = the u-end of branch `k`)."""
    ad = dartmask(lens, b)
    out = {}
    for k, (u, w) in enumerate(ends):
        out[u] = out.get(u, 0) + (1 if ad >> (2 * k) & 1 else 0)
        out[w] = out.get(w, 0) + (1 if ad >> (2 * k + 1) & 1 else 0)
    return out, ad


def _pool(n):
    """(class, habitat length assignment) pairs at `n_hub = n`: every
    connected loopless cubic multigraph class times every excess profile,
    gated by the landed (GR-25) criterion `cflank.cubic_habitat`."""
    out = []
    ep = excess_profiles(3 * n // 2, 6)
    for hedges in cubic_iso_classes(n):
        for exc in ep:
            lens = [2 + e for e in exc]
            if cubic_habitat(n, list(hedges), lens):
                out.append((list(hedges), lens))
    return out


# ------------------------------- [GTM-1] --charge: (GR-81)'s ingredients ----

def leg_charge():
    """[GTM-1] the universal dart identity and the 2-1 ledger, asserted at
    every branch of every admissible colouring of the COMPLETE `n_hub <= 6`
    stratum -- the two facts (GR-80)/(GR-81) are pure bookkeeping on top of."""
    t0 = time.time()
    print("[GTM-1] (GR-81) the dart identity `bend = e - 2c + 1` and the "
          "(GR-33) 2-1 pattern, EXHAUSTIVE on the complete n_hub <= 6 "
          "stratum (no rng, no cap)")
    # (a) the table itself, over every (l, majority) case at Lambda = empty
    for (L, amaj), (c, e, bend) in sorted(TYPES.items(), key=str):
        assert bend == e - 2 * c + 1, (L, amaj)
        assert e == L - 2 and 0 <= bend <= 2
    print(f"  the six-row table: bend == e - 2c + 1 at all "
          f"{len(TYPES)} (l, majority) cases, l in [2, 5]")
    shapes = ncol = nbr = 0
    per_n = {}
    for n in (2, 4, 6):
        pool = _pool(n)
        M = 3 * n // 2
        cnt = 0
        for (ends, lens) in pool:
            shapes += 1
            for (b, _adm) in admissible_bits(n, ends, lens):
                ncol += 1
                cnt += 1
                nA, ad = hub_adarts(ends, lens, b)
                # (GR-33): every hub carries a 2-1 pattern
                assert set(nA) == set(range(n)) and \
                    all(a in (1, 2) for a in nA.values()), \
                    "(GR-33) mono-hub ban refuted: a hub is not 2-1"
                # the per-branch identity, against the type table
                tot_bend = 0
                sc = se = 0
                for k in range(M):
                    L = lens[k]
                    du = bool(ad >> (2 * k) & 1)
                    dw = bool(ad >> (2 * k + 1) & 1)
                    key = (L, du) if L % 2 else (L, None)
                    c, e, bend = TYPES[key]
                    assert (du == dw) == (L % 2 == 1), \
                        "alternation refuted: end darts agree iff l is odd"
                    assert bend == (0 if du else 1) + (0 if dw else 1), \
                        "the type table's bend disagrees with the darts"
                    assert bend == e - 2 * c + 1
                    tot_bend += bend
                    sc += c
                    se += e
                    nbr += 1
                # the two global corollaries the X charge rides on
                assert se == 6, "(GR-21) excess law refuted"
                assert sc == 3, "(GR-32)(iii) balance identity refuted"
                assert tot_bend == M, \
                    "#B-darts != M -- the summed dart identity refuted"
                assert sum(1 for a in nA.values() if a == 2) == n // 2, \
                    "#A-majority hubs != n_hub / 2"
        per_n[n] = (len(pool), cnt)
    print(f"  per-branch identity + 2-1 pattern asserted at {nbr} "
          f"(colouring, branch) instances over {ncol} admissible colourings "
          f"of {shapes} habitat shapes")
    print(f"  per n_hub (shapes, colourings): "
          f"{sorted((k, v) for k, v in per_n.items())}")
    assert shapes == 4920 and ncol == 284512, \
        "the landed n_hub <= 6 pool figures moved (4920 / 284 512)"
    print("  => the pool reproduces (GR-38)'s own stratum figures exactly: "
          "4920 shapes / 284 512 admissible colourings")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------- [GTM-2] --frame: (GR-79) ledger ------

def leg_frame():
    """[GTM-2] the (GR-79) corner ledger, colouring-free, at every slack-0
    crossing chunk pair with a J-free intersection of every class at
    `n_hub = 4, 6, 8`.  The premise's length-free surrogate is AGLU's:
    `#X-hubs = 0` and `jfree(T) = 0`, both IMPLIED by
    `slack = 0 and defect_A(T) = 0`, so the ledger is asserted on a SUPERSET
    of the pairs it claims, never a subset."""
    t0 = time.time()
    print("[GTM-2] (GR-79) the T-frame corner ledger, colouring-free and "
          "length-free, EXHAUSTIVE over every crossing chunk pair of every "
          "class at n_hub = 4, 6, 8 (no rng, no cap)")
    for n in (4, 6, 8):
        npair = nzero = nfree = 0
        prof = {}
        for hedges in cubic_iso_classes(n):
            ends = list(hedges)
            chs = chunks_of(n, ends)
            for (i, j, xs, T, jT, dT) in crossing_pairs(n, ends, chs):
                npair += 1
                if xs:
                    continue
                nzero += 1
                # (GR-73)(ii): at slack 0 every T-hub has deg_T in {2, 3}
                assert all(d in (2, 3) for d in dT.values()), \
                    "(GR-73)(ii) refuted: a slack-0 T-hub has deg_T not in " \
                    "{2, 3}"
                if jT:
                    continue
                nfree += 1
                ints = {v for v, d in dT.items() if d == 2}
                cors = {v for v, d in dT.items() if d == 3}
                n2, n3 = len(ints), len(cors)
                ii = [k for k in T
                      if ends[k][0] in ints and ends[k][1] in ints]
                ic = [k for k in T
                      if (ends[k][0] in ints) != (ends[k][1] in ints)]
                cc = [k for k in T
                      if ends[k][0] in cors and ends[k][1] in cors]
                # (GR-79)(a): jfree(T) = 0 IS "no interior-interior branch"
                assert not ii, \
                    "(GR-79)(a)/(GR-74)(i) refuted: an interior-interior " \
                    "T-branch survives a J-free intersection"
                # (GR-79)(c): the ledger, before any length is chosen
                assert len(ic) == 2 * n2, \
                    "(GR-79)(b) refuted: an interior's T-darts do not all " \
                    "land at corners"
                assert len(T) == 2 * n2 + len(cc)
                assert 2 * len(T) == 2 * n2 + 3 * n3
                assert 2 * len(cc) == 3 * n3 - 2 * n2, \
                    "(GR-79)(c) the corner ledger 2(p + q_T) = 3n_3 - 2n_2 " \
                    "refuted"
                prof[(n2, n3, len(T), len(cc))] = \
                    prof.get((n2, n3, len(T), len(cc)), 0) + 1
        print(f"  n_hub = {n}: {npair} crossing pairs, {nzero} at slack 0, "
              f"{nfree} of those with a J-free intersection")
        print(f"    (n_2, n_3, |T|, #corner-corner) profiles: "
              f"{sorted(prof.items())}")
        if n == 8:
            assert nfree == 44 and prof == {(4, 4, 10, 2): 44}, \
                "AGLU's (GR-74) n_hub = 8 pinning does not reproduce"
            # the (GR-80) kill of the n_hub = 8 template, third independent
            # proof of (GR-75)(i): p <= p + q_T = 2 < 4 = n_3
            for (n2, n3, _t, pq) in prof:
                assert pq < n3, \
                    "the (GR-80) corner charge does NOT kill n_hub = 8 -- " \
                    "(GR-75)(i) would need its other two proofs"
            print("    => (GR-80) alone kills every one of the 44: "
                  "p <= p + q_T = 2 < 4 = n_3, so some corner has three "
                  "B-darts -- a THIRD independent proof of (GR-75)(i)")
    print(f"  [{time.time() - t0:.0f}s]")


# ---------------------------------------- the aggregate frame enumeration ---

def _corner_ok(n2, n3, p, qT):
    """Is there an assignment of the `p` corner A-darts to the `n_3` corners
    giving every corner the 1-or-2 A-darts the 2-1 pattern demands?  Each
    `l = 2` corner-corner branch supplies EXACTLY one A-dart, at one of its
    two ends ((GR-79)(d)), so this is `n_3 <= p <= 2 n_3` -- and the ENUMERATED
    form (over per-corner A-counts) is what is checked, so a reader does not
    have to take the inequality on trust."""
    if n3 == 0:
        return p == 0
    # enumerate the per-corner A-count multiset: n3 corners, each 1 or 2, so
    # `twos` of them carry 2 and the rest 1
    return any(twos + n3 == p for twos in range(n3 + 1))


def _frames(n_hub, qmax=6):
    """Every aggregate AA-glue frame profile at `n_hub`, as
    (n_2, n_3, |X|, q_T, p, |F1|, |F2|, |W|), satisfying the (GR-79) ledger,
    the dart-count identities (GR-76)(ii), the branch total, and the two
    mono-hub charges.  Exhaustive: the parameter box is finite and fully
    walked."""
    M = 3 * n_hub // 2
    out = []
    for n2 in range(4, n_hub + 1):
        for n3 in range(0, n_hub - n2 + 1, 2):
            nx = n_hub - n2 - n3
            for qT in range(0, qmax + 1):
                num = 3 * n3 - 2 * n2 - 2 * qT
                if num < 0 or num % 2:
                    continue
                p = num // 2
                Tn = 2 * n2 + p + qT
                if not _corner_ok(n2, n3, p, qT):      # (GR-80)
                    continue
                for f2 in range(0, n2 // 2 + 1):
                    f1 = n2 - 2 * f2
                    if f1 < 0:
                        continue
                    if (3 * nx - f1) < 0 or (3 * nx - f1) % 2:
                        continue
                    w = (3 * nx - f1) // 2
                    if Tn + f1 + f2 + w != M:
                        continue
                    if w and nx < 2:                   # W joins distinct hubs
                        continue
                    nb = 3 * nx - n2 - 2 * qT
                    if nb < 0 or nb % 2:
                        continue
                    nb //= 2                           # #B-darts at X hubs
                    if nx == 0:
                        if nb:
                            continue
                    elif not (nx <= nb <= 2 * nx):     # (GR-81)
                        continue
                    out.append((n2, n3, nx, qT, p, f1, f2, w))
    return out


def _type_multisets(role, cnt, sc, se):
    """Every multiset of `cnt` branch types of the given role with
    `Sum c = sc` and `Sum e = se`, as sorted tuples of type keys."""
    keys = ROLE_TYPES[role]
    out = []

    def rec(i, left, c, e, acc):
        if left == 0:
            if c == sc and e == se:
                out.append(tuple(acc))
            return
        if c > sc or e > se:
            return
        for j in range(i, len(keys)):
            kc, ke, _kb = TYPES[keys[j]]
            acc.append(keys[j])
            rec(j, left - 1, c + kc, e + ke, acc)
            acc.pop()
    rec(0, cnt, 0, 0, [])
    return out


def _xdart_ok(nx, f1types, wtypes):
    """Enumerate the per-X-hub dart patterns and ask whether ANY assignment
    gives every X hub a 2-1 pattern.  Exact at `|X| = 2` (every `W` branch
    then joins the two X hubs, so only the `F1` split is free); above that it
    falls back to the aggregate count, which is the (GR-81) inequality."""
    nb = sum(TYPES[t][2] for t in wtypes) \
        + sum(1 for t in f1types if TYPES[t][2] == 2)
    if nx != 2:
        return nx <= nb <= 2 * nx
    # |X| = 2: each W branch contributes one dart to each hub; an F1 branch
    # contributes its X-end to one hub.  Each hub takes 3 - |W| F1 darts.
    per = 3 - len(wtypes)
    if per < 0 or 2 * per != len(f1types):
        return False
    f1b = [1 if TYPES[t][2] == 2 else 0 for t in f1types]   # 1 = B at X end
    # W dart colours at (x, y): odd branch -> equal, even -> opposite
    wx, wy = [], []
    for t in wtypes:
        L, amaj = t
        bend = TYPES[t][2]
        if L % 2:
            wx.append(1 - (1 if amaj else 0))
            wy.append(1 - (1 if amaj else 0))
        else:
            wx.append(1)                     # one end B, one end A
            wy.append(0)
        assert bend == wx[-1] + wy[-1]
    # an even W branch may be oriented either way: enumerate the 2^(#even)
    evens = [i for i, t in enumerate(wtypes) if t[0] % 2 == 0]
    for orient in range(1 << len(evens)):
        ax = [wx[i] for i in range(len(wtypes))]
        ay = [wy[i] for i in range(len(wtypes))]
        for bit, i in enumerate(evens):
            if orient >> bit & 1:
                ax[i], ay[i] = ay[i], ax[i]
        bwx, bwy = sum(ax), sum(ay)
        # split the F1 X-ends into two groups of `per`
        for sub in range(1 << len(f1b)):
            if bin(sub).count('1') != per:
                continue
            bfx = sum(f1b[i] for i in range(len(f1b)) if sub >> i & 1)
            bfy = sum(f1b) - bfx
            for (bb, tot) in ((bwx + bfx, 3), (bwy + bfy, 3)):
                if not (1 <= bb <= tot - 1):
                    break
            else:
                return True
    return False


def _solutions(n_hub, verbose=False):
    """Every (frame, off-T type multiset, X-hub dart pattern) triple at
    `n_hub` surviving the whole system."""
    out = []
    for fr in _frames(n_hub):
        (n2, n3, nx, qT, p, f1, f2, w) = fr
        # Sum c = 3 and Sum e = 6 - q_T over ALL off-T branches: split the
        # budget across the three roles exhaustively.
        for c2 in range(0, 4):
            for c1 in range(0, 4 - c2):
                cw = 3 - c2 - c1
                for e2 in range(0, 7 - qT):
                    for e1 in range(0, 7 - qT - e2):
                        ew = 6 - qT - e2 - e1
                        if ew < 0:
                            continue
                        L2 = _type_multisets('F2', f2, c2, e2)
                        if not L2:
                            continue
                        L1 = _type_multisets('F1', f1, c1, e1)
                        if not L1:
                            continue
                        LW = _type_multisets('W', w, cw, ew)
                        if not LW:
                            continue
                        for a in L2:
                            for b in L1:
                                for c in LW:
                                    if _xdart_ok(nx, b, c):
                                        out.append((fr, a, b, c))
    return out


# ------------------------------------------ [GTM-3] --tpl: the kill ---------

def leg_tpl():
    """[GTM-3] the three (GR-76)(iv) templates, enumerated and EMPTY -- and
    the same enumeration at n_hub = 12, 14 (empty) and 16 (NOT empty, so the
    enumerator is not vacuously rejecting)."""
    t0 = time.time()
    print("[GTM-3] (GR-82) the (GR-76)(iv) three-template question at "
          "n_hub = 10, ENUMERATED (no rng, no cap: the parameter box is "
          "finite and fully walked)")
    TPL = [(4, 0, 1), (2, 1, 2), (0, 2, 3)]
    n_hub = 10
    print("  the dispatched templates, each on (n_2, n_3, |X|) = (4, 4, 2), "
          "|T| = 10:")
    for (f1, f2, w) in TPL:
        rows = []
        for qT in range(0, 3):
            num = 3 * 4 - 2 * 4 - 2 * qT
            p = num // 2 if num >= 0 and num % 2 == 0 else None
            corner = (p is not None and _corner_ok(4, 4, p, qT))
            nbnum = 3 * 2 - 4 - 2 * qT
            xok = (nbnum >= 0 and nbnum % 2 == 0
                   and 2 <= nbnum // 2 <= 4)
            # the raw colouring enumeration, both charges switched off
            found = seen = 0
            for c2 in range(0, 4):
                for c1 in range(0, 4 - c2):
                    cw = 3 - c2 - c1
                    for e2 in range(0, 7 - qT):
                        for e1 in range(0, 7 - qT - e2):
                            ew = 6 - qT - e2 - e1
                            if ew < 0:
                                continue
                            for a in _type_multisets('F2', f2, c2, e2):
                                for b in _type_multisets('F1', f1, c1, e1):
                                    for c in _type_multisets('W', w, cw, ew):
                                        seen += 1
                                        if _xdart_ok(2, b, c):
                                            found += 1
            rows.append((qT, p, corner, xok, found, seen))
        print(f"    ({f1}, {f2}, {w}): "
              + "; ".join(f"q_T = {q}: p = {p}, corner-charge "
                          f"{'OK' if co else 'FAILS'}, X-charge "
                          f"{'OK' if xo else 'FAILS'}, "
                          f"{sn} (c, e)-consistent type multisets, "
                          f"X-hub-enumerated survivors {fo}"
                          for (q, p, co, xo, fo, sn) in rows))
        for (q, _p, co, xo, fo, sn) in rows:
            assert not co, "the (GR-80) corner charge admits a template"
            assert not xo, "the (GR-81) X charge admits a template"
            assert fo == 0, \
                "a (GR-76)(iv) template SURVIVES the X-hub dart " \
                "enumeration -- (GR-82) is overturned"
            if q > 1:
                assert sn == 0, \
                    "(GR-76)(iv)'s q_T <= 1 is refuted: a (c, e)-consistent " \
                    "type multiset exists at q_T = 2"
        assert sum(sn for (q, _p, _co, _xo, _fo, sn) in rows if q <= 1) > 0, \
            "no (c, e)-consistent type multiset exists at q_T <= 1 either, " \
            "so the 0 survivors are VACUOUS -- the COUNTING side would " \
            "already have closed this template and (GR-76)(iv)'s " \
            "'satisfiable' would be wrong"
    print("  => all three templates dead, and each of the two charges kills "
          "each of them INDEPENDENTLY (both columns FAIL at every q_T); the "
          "X-hub dart enumeration, run with both charges switched off, "
          "returns 0 survivors as well")
    for n in (10, 12, 14, 16, 18, 20):
        fr = _frames(n)
        sol = _solutions(n)
        print(f"  n_hub = {n:2d}: {len(fr)} aggregate frames, {len(sol)} full "
              f"solutions")
        if n <= 14:
            assert not fr and not sol, \
                f"the AA-glue system is FEASIBLE at n_hub = {n} -- (GR-82) " \
                f"is overturned"
        if n == 16:
            assert fr and sol, \
                "the enumerator finds nothing at n_hub = 16 either -- it is " \
                "vacuously rejecting, and (GR-83)'s witness contradicts it"
            print(f"    the n_hub = 16 frames: {sorted(fr)}")
            print(f"    first solution: {sol[0]}")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------ [GTM-4] --min: the boundary -----

def leg_min():
    """[GTM-4] the least `n_hub` at which the aggregate system has ANY
    solution, by exhaustive integer search."""
    t0 = time.time()
    print("[GTM-4] (GR-82) the least feasible n_hub, exhaustive over "
          "n_hub <= 40 (no rng; the search box is the whole parameter range "
          "the identities allow)")
    hits = []
    for n in range(2, 41, 2):
        fr = _frames(n)
        if fr:
            hits.append((n, len(fr)))
    print(f"  feasible n_hub (aggregate frames): {hits[:8]}"
          f"{' ...' if len(hits) > 8 else ''}")
    assert hits and hits[0][0] == 16, \
        "the least feasible n_hub is not 16 -- (GR-82)'s bound moved"
    print(f"  => the least feasible n_hub is {hits[0][0]}; every "
          f"n_hub <= 14 is INFEASIBLE, and the bound n_hub >= 4(n_2 + q_T) "
          f">= 16 is attained")
    for (n2, n3, nx, qT, p, f1, f2, w) in sorted(_frames(16)):
        assert (n2, n3, nx, qT, p) == (4, 8, 4, 0, 8), \
            "an n_hub = 16 frame off the tight profile"
        print(f"    frame: n_2 = {n2}, n_3 = {n3}, |X| = {nx}, q_T = {qT}, "
              f"p = {p}, (|F1|, |F2|, |W|) = ({f1}, {f2}, {w}) -- all three "
              f"charges tight")
    print(f"  [{time.time() - t0:.0f}s]")


# ---------------------------------------------- the n_hub = 16 witness ------

def witness_specs(ic=None, wlen=None):
    """(GR-83)'s witness family.  Hub labels: corners 0..7 (an 8-cycle),
    interiors 8..11, X hubs 12..15 (a 4-cycle of W branches).  `ic` maps each
    interior to its two corners (a perfect assignment: each corner is hit
    once); `wlen` gives the four W branches' (length, ends-are-A) types in
    cycle order.  Returns (specs, first, role, names)."""
    if ic is None:
        ic = {8: (0, 2), 9: (1, 3), 10: (4, 6), 11: (5, 7)}
    if wlen is None:
        wlen = [(3, False), (5, True), (4, None), (2, None)]
    C = list(range(8))
    U = [8, 9, 10, 11]
    X = [12, 13, 14, 15]
    specs, first, role, names = [], [], [], []

    def add(u, w, L, f, r, nm):
        specs.append((u, w, L))
        first.append(f)
        role.append(r)
        names.append(nm)
    # the corner 8-cycle: l = 2, consistently oriented, A at the w end
    for i in range(8):
        add(C[i], C[(i + 1) % 8], 2, 'B', 'cyc', f"cc{i}")
    # interior -> corner: l = 2, A at the interior end (the interior is AA)
    for j in sorted(ic):
        for a in ic[j]:
            add(j, a, 2, 'A', 'ic', f"ic{j}_{a}")
    # F1: interior -> X, l = 2, B at the interior end (its free dart)
    for t in range(4):
        add(U[t], X[t], 2, 'B', 'f1', f"f1_{t}")
    # W: the 4-cycle on the X hubs
    for t in range(4):
        (L, amaj) = wlen[t]
        if L % 2:
            f = 'A' if amaj else 'B'
        else:
            f = 'B'                          # B at the u end, A at the w end
        add(X[t], X[(t + 1) % 4], L, f, 'w', f"w{t}")
    return specs, first, role, names


def build_witness(ic=None, wlen=None):
    """Everything the canonical layer needs, plus the two chunks."""
    specs, first, role, names = witness_specs(ic, wlen)
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    n = 16
    if not cubic_habitat(n, hedges, lens):
        return None
    edges = subdivide(specs)
    allverts = verts_of(edges)
    col = wit_colouring(specs, first)
    hm = hub_model(edges)
    if hm is None:
        return None
    inc = incidence(hm)
    pairs = {}
    for k, (u, w) in enumerate(hm['ends']):
        key = frozenset((u, w))
        assert key not in pairs, "parallel branches: end-pair map unsafe"
        pairs[key] = k
    s2h = [pairs[frozenset((('h', u), ('h', w)))] for (u, w, _L) in specs]
    assert sorted(s2h) == list(range(len(specs)))
    assert all(hm['lens'][s2h[i]] == lens[i] for i in range(len(specs)))
    idx = {names[i]: s2h[i] for i in range(len(specs))}
    T = sorted(s2h[i] for i in range(len(specs)) if role[i] in ('cyc', 'ic'))
    R = sorted([idx['f1_0'], idx['f1_1'], idx['w0']])
    Rp = sorted([idx['f1_2'], idx['f1_3'], idx['w2']])
    S = sorted(T + R)
    Sp = sorted(T + Rp)
    return dict(specs=specs, first=first, role=role, names=names, idx=idx,
                hedges=hedges, lens=lens, edges=edges, allverts=allverts,
                col=col, hm=hm, inc=inc, T=T, R=R, Rp=Rp, S=S, Sp=Sp)


def _verdict(W):
    """The AA-glue verdict of a built witness, through the canonical
    evaluators only."""
    hm, inc, col = W['hm'], W['inc'], W['col']
    if not admissible(W['edges'], W['allverts'], hm, col):
        return None
    st = branch_stats(hm, col, 'A')
    dT = defect_direct(hm, inc, st, W['T'], True)
    dS = defect_direct(hm, inc, st, W['S'], True)
    dSp = defect_direct(hm, inc, st, W['Sp'], True)
    un = sorted(set(W['S']) | set(W['Sp']))
    dU = defect_direct(hm, inc, st, un, True)
    slack, ndiff = pair_slack(hm, inc, st, W['S'], W['Sp'])
    return dict(dT=dT, dS=dS, dSp=dSp, dU=dU, un=un, slack=slack,
                ndiff=ndiff, stats=st)


# --------------------------------------------- [GTM-5] --wit: (GR-83) -------

def leg_wit():
    """[GTM-5] the n_hub = 16 witness, verified through the CANONICAL layer
    and rank-certified."""
    t0 = time.time()
    print(f"[GTM-5] (GR-83) the n_hub = 16 AA-GLUE WITNESS "
          f"(seed {G_SEED + 5})")
    rng = random.Random(G_SEED + 5)
    W = build_witness()
    assert W is not None, \
        "the witness shape FAILS the landed (GR-25) habitat gate"
    n, lens = 16, W['lens']
    print(f"  shape: n_hub = 16, M = {len(lens)} branches, total excess "
          f"{sum(L - 2 for L in lens)}, lengths "
          f"{sorted(set(lens))}; |V(subdivision)| = {len(W['allverts'])}")
    print(f"  HABITAT: cflank.cubic_habitat(16, ...) = True   "
          f"(the landed (GR-25) cut criterion, the same oracle AGLU's "
          f"exhaustive n_hub = 8 scan is gated by)")
    assert 5 * len(W['edges']) == 6 * (len(W['allverts']) - 1), \
        "the witness shape is not tight"
    print(f"  tightness cross-check: 5|E| = {5 * len(W['edges'])} = "
          f"6(|V| - 1) = {6 * (len(W['allverts']) - 1)}")
    # the CANONICAL certificate `gridcol.class_shape`'s conjuncts, all but
    # `kslide.no_rigid_branch_union` (a 2^M scan with a matroid rank inside,
    # out of reach at M = 24 -- which is exactly why (GR-25) / cubic_habitat
    # is the arc's oracle past n_hub = 6, as AGLU's n_hub = 8 scan already
    # relied on).  Recorded as an INDEPENDENT cross-check of the gate.
    dfc = deficiency(W['edges'])
    hcd = hcard_ok(W['edges'])
    hbs = hub_set(W['edges'])
    tri = [t for t in triangles(W['edges']) if len(t & hbs) >= 2]
    print(f"  gridcol.class_shape's other conjuncts, independently: "
          f"nogood_subdiv.deficiency = {dfc} (the polynomial Lee--Streinu "
          f"pebble game), hcard_ok = {hcd}, two-hub triangles = {len(tri)}")
    assert dfc == 0 and hcd and not tri, \
        "the witness shape fails a class_shape conjunct: the (GR-25) gate " \
        "and the canonical certificate DISAGREE at n_hub = 16"
    print("  (the one conjunct not re-run is kslide.no_rigid_branch_union, "
          "a 2^M scan with a matroid rank inside -- out of reach at "
          "M = 24, and precisely what (GR-25) replaces)")
    v = _verdict(W)
    assert v is not None, "cflank.admissible REJECTS the witness colouring"
    print("  ADMISSIBLE: cflank.admissible(...) = True   (the canonical "
          "predicate: alternating + both classes forests + balanced + no "
          "mono hub)")
    nA, _ad = hub_adarts(W['hedges'], lens, _bits_of(W))
    print(f"  hub A-dart counts (the 2-1 pattern): "
          f"{sorted(set(nA.values()))} at all 16 hubs")
    hm, inc, st = W['hm'], W['inc'], v['stats']
    for (nm, ks) in (('T = S n S\'', W['T']), ('S', W['S']),
                     ("S'", W['Sp']), ("S u S'", v['un'])):
        d = defect_direct(hm, inc, st, ks, True)
        chunk = _conn_bridgeless(hm['ends'], tuple(ks),
                                 degmap(hm['ends'], ks)) and \
            all(x in (2, 3) for x in degmap(hm['ends'], ks).values())
        print(f"    {nm:12s} {len(ks):3d} branches   defect_A = {d}   "
              f"g = {3 - d}   chunk: {chunk}   "
              f"{'BINDING' if d <= 2 else 'not binding'}")
    assert v['dT'] == 0, "defect_A(T) != 0: not the AA-glue configuration"
    assert v['dS'] <= 2 and v['dSp'] <= 2, "a chunk is not binding"
    assert v['slack'] == 0 and v['ndiff'] == 0, "slack != 0"
    assert v['dS'] + v['dSp'] == v['dU'] + v['dT'] + v['slack'], \
        "(GR-38)(i) the exact slack identity refuted at the witness"
    assert len(v['un']) < len(lens), "the union is not proper"
    assert v['dU'] > 2, "the union IS binding: this is not a kill failure"
    print(f"  (GR-38)(i) slack identity: {v['dS']} + {v['dSp']} = "
          f"{v['dU']} + {v['dT']} + {v['slack']}  OK;   #X-hubs = "
          f"{v['ndiff']} (so slack = 0 by (GR-73)(i))")
    print(f"  (GR-38)(ii) attachment lemma, through the LANDED checker "
          f"gorient.attachment_check:")
    for (nm, a, b) in (("R'", W['S'], W['Sp']), ("R", W['Sp'], W['S'])):
        cls = attachment_check(hm, inc, a, b)
        print(f"    components of {nm}: {cls}")
        assert len(cls) == 1 and len(cls[0]) == 2 and \
            all(t == '23' for (_v, t) in cls[0]), \
            "the attachment families are not the AA-glue's two disjoint " \
            "2-member (2,3)-type families"
    print("  => the configuration IS the AA-glue configuration: crossing, "
          "same-block (A) binding, slack 0, defect_A(T) = 0, every "
          "attachment an AA (2,3)-hub -- and the (GR-38) KILL FAILS "
          "(union proper, defect 4 > 2, NOT binding)")
    # the three charges, all tight
    ends = hm['ends']
    dT = degmap(ends, W['T'])
    ints = {x for x, d in dT.items() if d == 2}
    cors = {x for x, d in dT.items() if d == 3}
    allh = set(hm['hubs'])
    xh = allh - ints - cors
    cc = [k for k in W['T'] if ends[k][0] in cors and ends[k][1] in cors]
    qT = sum(1 for k in cc if hm['lens'][k] == 3)
    p = len(cc) - qT
    n2, n3, nx = len(ints), len(cors), len(xh)
    print(f"  the (GR-79) ledger at the witness: n_2 = {n2}, n_3 = {n3}, "
          f"|X| = {nx}, q_T = {qT}, p = {p}, |T| = {len(W['T'])}")
    assert 2 * p == 3 * n3 - 2 * n2 - 2 * qT, "(GR-79)(c) refuted"
    nAd, _adw = hub_adarts(W['hedges'], lens, _bits_of(W))
    bx = sum(3 - nAd[x[1]] for x in xh)
    bc = sum(3 - nAd[x[1]] for x in cors)
    assert 2 * bx == 3 * nx - n2 - 2 * qT, \
        "(GR-81)'s B-dart count at the X hubs refuted at the witness"
    assert bc == 2 * n2 + p + 2 * qT, \
        "(GR-79)'s B-dart count at the corners refuted at the witness"
    print(f"  (GR-81) B-darts at the X hubs: {bx} = "
          f"(3|X| - n_2 - 2q_T)/2 = {(3 * nx - n2 - 2 * qT) // 2}; B-darts "
          f"at the corners: {bc} = 2n_2 + p + 2q_T = "
          f"{2 * n2 + p + 2 * qT}; A-darts at the corners: "
          f"{3 * n3 - bc} = p = {p}")
    assert n3 == 2 * n2 + 2 * qT, "(GR-80) is not TIGHT at the witness"
    assert nx == n2 + 2 * qT, "(GR-81) is not TIGHT at the witness"
    assert n2 + n3 + nx == 4 * (n2 + qT) == 16
    print(f"  (GR-80) n_3 >= 2n_2 + 2q_T : {n3} >= {2 * n2 + 2 * qT}  TIGHT")
    print(f"  (GR-81) |X| >= n_2 + 2q_T  : {nx} >= {n2 + 2 * qT}  TIGHT")
    print(f"  (GR-82) n_hub >= 4(n_2+q_T): 16 >= {4 * (n2 + qT)}  TIGHT "
          f"-- the bound is attained, so it is EXACT")
    # RANK CERTIFICATION: the exact g, independent of the (GR-28) formula
    bdA = block_data(W['edges'], W['allverts'], W['col'], 'A')
    print(f"  block A: |E_A| = {len(bdA['E'])}, cycle rank h = {bdA['h']}, "
          f"contracted nodes n_c = {bdA['n_c']}")
    for (nm, ks, want) in (('T', W['T'], 3 - v['dT']),
                           ('S', W['S'], 3 - v['dS']),
                           ("S'", W['Sp'], 3 - v['dSp']),
                           ("S u S'", v['un'], 3 - v['dU'])):
        g = subgraph_g(bdA, subset_eidx(bdA, hm, ks))
        print(f"    exact g({nm}) via gridwit.subgraph_g = {g}   "
              f"((GR-28) formula predicts {want})")
        assert g == want, \
            "the EXACT g disagrees with the (GR-28)(i) formula at the " \
            "witness -- the binding verdict is not rank-certified"
    dz = dim_Z(bdA)
    dzg = dim_Z_generic(bdA, rng)
    print(f"  exact rational dim Z in block A: {dz} at the component-index "
          f"labels, {dzg} at generic labels (the min over seeded draws, "
          f"§(K-clos) (AC-9))")
    assert dzg > 0, \
        "dim Z = 0 in block A at generic labels: the binding chunks are " \
        "not a REAL obstruction and the witness is a formula artifact"
    print("  => the obstruction is RANK-CERTIFIED: an exact rational "
          "dim Z > 0 in block A at generic labels, matching max g > 0")
    print(f"  [{time.time() - t0:.0f}s]")


def _bits_of(W):
    """The witness colouring as a branch bit vector in `aglu`'s convention
    (bit k = the u-end dart of branch k is A), on the SPEC branch order --
    which is `W['hedges']`'s order."""
    b = 0
    for i, (u, w, _L) in enumerate(W['specs']):
        if W['first'][i] == 'A':
            b |= 1 << i
    return b


# --------------------------------------------- [GTM-6] --e1: the controls ---

def leg_e1():
    """[GTM-6] the E1 control at the witness shape, and the witness family."""
    t0 = time.time()
    print(f"[GTM-6] (GR-83) the E1 control and the witness family "
          f"(seed {G_SEED + 6})")
    W = build_witness()
    ends, lens = W['hedges'], W['lens']
    ch = chunks_via_complement(16, ends)
    cap = []
    for (ks, deg) in ch:
        w45 = sum(1 for k in ks if lens[k] >= 4)
        if w45 + jfree(ends, ks, deg) <= 2:
            cap.append((ks, deg, w45))
    print(f"  the witness graph carries {len(ch)} chunks, {len(cap)} of them "
          f"in the (GR-36)/(F-b) BINDING-CAPABLE family (an EXACT family: a "
          f"chunk outside it is never binding at any colouring)")
    cols = admissible_bits(16, ends, lens)
    print(f"  the witness shape carries {len(cols)} admissible colourings")
    caches = []
    for (ks, deg, w45) in cap:
        oddm = 0
        for k in ks:
            if lens[k] % 2:
                oddm |= 1 << k
        prs = []
        for x, d in sorted(deg.items()):
            m = 0
            for k in ks:
                u, w = ends[k]
                if u == x:
                    m |= 1 << (2 * k)
                if w == x:
                    m |= 1 << (2 * k + 1)
            prs.append(m)
        caches.append((w45, oddm, bin(oddm).count('1'), tuple(prs), ks))
    fg = None
    tried = 0
    for (b, ad) in cols:
        tried += 1
        bad = False
        for (w45, oddm, nodd, prs, ks) in caches:
            pa = bin(b & oddm).count('1')
            if w45 + pa <= 2:
                naa = sum(1 for m in prs if (m & ad) != m)
                if w45 + pa + naa <= 2:
                    bad = True
                    break
            if w45 + (nodd - pa) <= 2:
                nbb = sum(1 for m in prs if (m & ad) != 0)
                if w45 + (nodd - pa) + nbb <= 2:
                    bad = True
                    break
        if not bad:
            fg = b
            break
    print(f"  E1: a FULLY-GOOD admissible colouring of the witness shape "
          f"(no binding chunk in either block over the binding-capable "
          f"family) was found at colouring #{tried} of {len(cols)}: "
          f"b = {fg}")
    assert fg is not None, \
        "NO fully-good colouring found: the witness shape may be a g-FLANK " \
        "and E1 may FIRE -- this needs the exhaustive scan, not this probe"
    print("  => the witness shape is NOT a g-flank: E1 does NOT fire.  "
          "(A single fully-good colouring settles E1 for a shape; no cap "
          "disclosure is needed for a POSITIVE.)")
    # the witness colouring itself CANNOT be fully good: a binding chunk IS
    # a g >= 1 obstruction.  Recorded because the dispatch asked.
    v = _verdict(W)
    print(f"  the witness COLOURING is necessarily not fully good: "
          f"g(S) = {3 - v['dS']} >= 1, and 'fully good' is "
          f"max_P g(P) <= 0 -- 'a realized AA-glue that is still fully "
          f"good' is an EMPTY case, not a weaker one")
    # the family: the phenomenon is not a knife edge
    ok = bad_hab = bad_adm = bad_cfg = 0
    fam = []
    ics = [{8: (0, 2), 9: (1, 3), 10: (4, 6), 11: (5, 7)},
           {8: (0, 2), 9: (4, 6), 10: (1, 3), 11: (5, 7)},
           {8: (0, 3), 9: (1, 4), 10: (2, 5), 11: (6, 7)},
           {8: (0, 2), 9: (1, 5), 10: (3, 6), 11: (4, 7)},
           {8: (0, 4), 9: (1, 5), 10: (2, 6), 11: (3, 7)}]
    wls = [[(3, False), (5, True), (4, None), (2, None)],
           [(5, True), (3, False), (4, None), (2, None)],
           [(3, False), (5, True), (2, None), (4, None)],
           [(4, None), (5, True), (3, False), (2, None)],
           [(2, None), (5, True), (4, None), (3, False)],
           [(3, False), (4, None), (5, True), (2, None)]]
    for i, ic in enumerate(ics):
        for j, wl in enumerate(wls):
            X = build_witness(ic, wl)
            if X is None:
                bad_hab += 1
                continue
            vv = _verdict(X)
            if vv is None:
                bad_adm += 1
                continue
            if not (vv['dT'] == 0 and vv['dS'] <= 2 and vv['dSp'] <= 2
                    and vv['slack'] == 0 and vv['dU'] > 2
                    and len(vv['un']) < len(X['lens'])):
                bad_cfg += 1
                continue
            ok += 1
            fam.append((i, j, vv['dS'], vv['dSp'], vv['dT'], vv['dU']))
    print(f"  the witness FAMILY over {len(ics)} interior-corner assignments "
          f"x {len(wls)} W-length rotations: {ok} give a habitat-gated, "
          f"admissible AA-glue configuration with the kill failing; "
          f"{bad_hab} fail the habitat gate, {bad_adm} fail admissibility, "
          f"{bad_cfg} are admissible but not AA-glue")
    print(f"  first five members (ic index, W index, dS, dS', dT, dU): "
          f"{fam[:5]}")
    assert ok >= 2, \
        "the AA-glue realization is a single isolated coincidence, not a " \
        "family -- report it as such"
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------- [GTM-7] --lam: (GR-84) ---------

def _s2h(W):
    """spec branch index -> hub_model branch index (no parallel branches)."""
    pairs = {}
    for k, (u, w) in enumerate(W['hm']['ends']):
        pairs[frozenset((u, w))] = k
    return [pairs[frozenset((('h', u), ('h', w)))] for (u, w, _L) in W['specs']]


def leg_lam():
    """[GTM-7] the residual / laminarity census AT THE WITNESS COLOURING --
    exhaustive over the whole chunk family of the witness graph, in BOTH
    blocks, at ONE colouring (disclosed: this is not a stratum scan and makes
    no claim about the shape's other 123 739 admissible colourings)."""
    t0 = time.time()
    print("[GTM-7] (GR-84) the residual and laminarity census at the witness "
          "COLOURING (exhaustive over all chunks of the witness graph in "
          "both blocks; ONE colouring -- see the cap disclosure)")
    W = build_witness()
    hm, inc, ends = W['hm'], W['inc'], W['hm']['ends']
    s2h = _s2h(W)
    ch = chunks_via_complement(16, W['hedges'])
    print(f"  the witness graph carries {len(ch)} chunks "
          f"(aglu.chunks_of's family, --val-certified)")
    for mine in (True, False):
        st = branch_stats(hm, W['col'], 'A' if mine else 'B')
        sets = []
        for (ks, _deg) in ch:
            hks = frozenset(s2h[k] for k in ks)
            if defect_direct(hm, inc, st, sorted(hks), mine) <= 2:
                sets.append(hks)
        maximal = [x for x in sets if not any(x < y for y in sets)]
        aaglue = resid = killfail = crossn = crossmax = 0
        dist = {}
        for i in range(len(sets)):
            for j in range(i + 1, len(sets)):
                a, b = sets[i], sets[j]
                if a <= b or b <= a:
                    continue
                ha = {x for k in a for x in ends[k]}
                hb = {x for k in b for x in ends[k]}
                if not (ha & hb):
                    continue
                crossn += 1
                T, un = sorted(a & b), sorted(a | b)
                dT = defect_direct(hm, inc, st, T, mine)
                dU = defect_direct(hm, inc, st, un, mine)
                sl = defect_direct(hm, inc, st, sorted(a), mine) \
                    + defect_direct(hm, inc, st, sorted(b), mine) - dU - dT
                if sl == 0 and dT == 0:
                    aaglue += 1
                if sl + dT <= 1:
                    resid += 1
                if len(un) < len(ends) and dU > 2:
                    killfail += 1
                if a in maximal and b in maximal:
                    crossmax += 1
                    dist[(sl, dT, dU)] = dist.get((sl, dT, dU), 0) + 1
        blk = 'A' if mine else 'B'
        print(f"  block {blk}: {len(sets)} binding chunks, {len(maximal)} of "
              f"them MAXIMAL; {crossn} crossing binding pairs, of which "
              f"{resid} lie in the kill residual (slack + defect(T) <= 1), "
              f"{aaglue} are AA-GLUE (slack = 0 AND defect(T) = 0), and "
              f"{killfail} are KILL FAILURES (proper union, not binding)")
        print(f"    crossing pairs of MAXIMAL binding chunks: {crossmax}"
              f"   (slack, defect(T), defect(union)) histogram "
              f"{sorted(dist.items())}")
        assert aaglue >= 1 and killfail >= 1, \
            "the census finds no AA-glue / no kill failure, contradicting " \
            "--wit's own witness"
        assert crossmax >= 1, \
            "no two MAXIMAL binding chunks cross, so (GR-75)(iii)'s " \
            "laminarity corollary SURVIVES here -- weaken the claim"
    print("  => at n_hub = 16 the WHOLE kill residual is inhabited (not just "
          "its AA-glue case), the (GR-38) kill fails repeatedly, and "
          "(GR-75)(iii)'s corollary -- laminarity of the MAXIMAL binding "
          "family per block -- FAILS as well")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------------ [GTM-8] --val -------

def leg_val():
    """[GTM-8] every local device asserted equal to its canonical
    counterpart."""
    t0 = time.time()
    print(f"[GTM-8] device cross-certification (seed {G_SEED + 8})")
    rng = random.Random(G_SEED + 8)
    # (1) the chunk enumerator vs aglu.chunks_of
    for n in (4, 6):
        ncls = 0
        for hedges in cubic_iso_classes(n):
            ends = list(hedges)
            a = {ks for (_m, ks, _d) in chunks_of(n, ends)}
            b = {ks for (ks, _d) in chunks_via_complement(n, ends)}
            assert a == b, \
                f"chunks_via_complement != aglu.chunks_of at n = {n}"
            ncls += 1
        print(f"  (1) chunk enumerator SET-EQUAL to aglu.chunks_of at all "
              f"{ncls} classes at n_hub = {n}")
    reps8 = cubic_iso_classes(8)
    pick = sorted(rng.sample(range(len(reps8)), 6))
    for i in pick:
        ends = list(reps8[i])
        a = {ks for (_m, ks, _d) in chunks_of(8, ends)}
        b = {ks for (ks, _d) in chunks_via_complement(8, ends)}
        assert a == b, "chunks_via_complement != aglu.chunks_of at n_hub = 8"
    print(f"  (1) ... and at seeded classes {pick} of the {len(reps8)} at "
          f"n_hub = 8 (|chunks| = "
          f"{len(chunks_of(8, list(reps8[pick[0]])))} at the first)")
    # (2) the TYPES table vs gexist.defect_direct / gcap.branch_stats
    #     one theta(l, 2, 2) per row: the branch under test plus two l = 2
    #     branches closing it, so the shape has hubs and a branch model.
    checked = 0
    for (L, amaj) in sorted(TYPES, key=str):
        c, e, bend = TYPES[(L, amaj)]
        specs = [(0, 1, L), (0, 1, 2), (0, 1, 2)]
        edges = subdivide(specs)
        allverts = verts_of(edges)
        hm = hub_model(edges)
        inc = incidence(hm)
        for firstc in ('A', 'B'):
            col = wit_colouring(specs, [firstc, 'A', 'B'])
            st = branch_stats(hm, col, 'A')
            k = next(k for k in range(3) if hm['lens'][k] == L)
            if L % 2:
                if (firstc == 'A') != bool(amaj):
                    continue
            acnt, du, dw = st
            assert acnt[k] - 1 == c, "TYPES' c != A(beta) - 1"
            assert hm['lens'][k] - 2 == e
            assert (0 if du[k] else 1) + (0 if dw[k] else 1) == bend, \
                "TYPES' bend != the end-dart count"
            d1 = defect_direct(hm, inc, st, [k], True)
            assert d1 == c, \
                "defect_direct on a single branch != c (no interior there)"
            checked += 1
    print(f"  (2) the (c, e, bend) table asserted against "
          f"gexist.defect_direct + gcap.branch_stats at {checked} "
          f"constructed single-branch instances covering all "
          f"{len(TYPES)} rows")
    # (3) the aggregate enumerator agrees with the closed-form charges
    bad = 0
    for n in range(2, 33, 2):
        for (n2, n3, nx, qT, p, _f1, _f2, _w) in _frames(n):
            if not (n3 >= 2 * n2 + 2 * qT and nx >= n2 + 2 * qT
                    and n >= 4 * (n2 + qT) and n2 >= 4):
                bad += 1
    assert bad == 0, \
        "an enumerated frame violates the closed-form (GR-80)/(GR-81)/" \
        "(GR-82) charges -- the derivation and the enumeration disagree"
    print("  (3) every enumerated aggregate frame at n_hub <= 32 satisfies "
          "the closed-form (GR-80)/(GR-81)/(GR-82) charges (the derivation "
          "and the enumeration agree, in the direction that matters: the "
          "enumeration never admits what the closed form forbids)")
    # (4) the witness's own arithmetic, independent of --wit's asserts
    W = build_witness()
    assert W is not None
    v = _verdict(W)
    assert v is not None
    assert (v['dT'], v['dS'], v['dSp'], v['dU'], v['slack']) == \
        (0, 2, 2, 4, 0), \
        "the witness figures moved: --wit's headline numbers are stale"
    print("  (4) the witness's headline 5-tuple "
          "(defect_A of T, S, S', union; slack) = (0, 2, 2, 4, 0), "
          "recomputed from scratch through the canonical evaluators")
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------------- main -----

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--charge', action='store_true')
    ap.add_argument('--frame', action='store_true')
    ap.add_argument('--tpl', action='store_true')
    ap.add_argument('--min', action='store_true')
    ap.add_argument('--wit', action='store_true')
    ap.add_argument('--e1', action='store_true')
    ap.add_argument('--lam', action='store_true')
    ap.add_argument('--val', action='store_true')
    a = ap.parse_args()
    any_ = False
    for flag, fn in (('charge', leg_charge), ('frame', leg_frame),
                     ('tpl', leg_tpl), ('min', leg_min), ('wit', leg_wit),
                     ('e1', leg_e1), ('lam', leg_lam),
                     ('val', leg_val)):
        if getattr(a, flag):
            fn()
            any_ = True
    if not any_:
        ap.print_help()


if __name__ == '__main__':
    main()
