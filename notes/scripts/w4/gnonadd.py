"""§(K-grid) direction GNONADD (2026-09-10) driver -- DOES A **NON-ADDITIVE**
MOVE (one that DELETES at least one parent hub) RELATE TWO `D = 0` CLASS
SHAPES?  §8's thirteenth-pass rank 1.  GEXPAND ((GR-171)) proved no ADDITIVE
zero-net-excess expansion move exists; its own Step G189 excludes
`Y -> Delta` as blind axis 1, and `gexpand.py`'s docstring dismisses it
"at girth: its new triangle is a circuit of total length 6 < 7".

THE ANSWER IS **YES**, AND THE GIRTH DISMISSAL IS THE ERROR.  A hub-deleting
move re-lengths the branches AT THE DELETED HUB -- they are inside the
changed region, not outside it (blind axis 2 is about branches away from the
changed region) -- so the new triangle need NOT absorb the whole `+6` of
`Delta Sigma-l`.  It may take `7, 8, 9` and give the rest back by SHORTENING
the boundary.  Witness, both ends certified by `gridcol.class_shape`:

    theta(4,4,4)  --Y->Delta-->  K4 with all six branches of length 3.

A `w4/` leaf beside `gexpand.py`, importing `cflank` / `gridcol` / `gisland`
/ `aglu` READ-ONLY (README §2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --law      # the (GR-169) accounting REDONE without the surviving-hubs assumption; sentence 1 survives, sentence 2 does NOT
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --wit      # THE WITNESS, both ends through the CANONICAL oracle `gridcol.class_shape`
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --cut      # THE MECHANISM ELIMINATED: (GR-170) at the new triangle IS (GR-173) at the contracted hub, hence AUTOMATICALLY satisfied
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --contract # the REDUCTION census: every hub set with cut 3 contracted, over the landed n_hub = 4 / 6 / 8 pools
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --chain    # SIX consecutive non-additive moves, K4(3^6) -> n_hub = 16, every member a class shape at `Lambda = empty`
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --ladder   # the LIMIT of the positive: (GR-175)'s infinite CL_m family is triangle-free, so no Y-reduction reaches it
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --blind    # gexpand's `reduction_frames` PROVABLY cannot express a Y-reduction -- the architectural blind axis, exhibited
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gnonadd.py --validate # all seven

WHAT A NON-ADDITIVE MOVE IS, stated once so every mode tests the same object.
A **Y-reduction** takes a `D = 0` class shape (the CHILD) to another (the
PARENT) by: choosing a hub set `A` that induces a connected subgraph, has
branch cut `partial(A) = 3` and odd `|A| >= 3`; DELETING `A` and every
branch inside it; and replacing it by ONE new hub carrying the three
boundary branches, whose lengths are re-chosen.  `Delta n = |A| - 1` (even,
as (GR-169) sentence 1 forces) and cubicity+tightness then FORCE

    Sigma_boundary l' = Sigma_boundary l + Sigma_{E(A)} l - 3(|A| - 1).

`|A| = 3` with `E(A)` a triangle is `Delta -> Y`; the inverse is `Y -> Delta`.
Nothing outside `A` and its three boundary branches changes.  This is
DISJOINT from GEXPAND's additive class: there every parent hub survives.

WHAT EACH MODE TESTS, one sentence each (F11).

--law      that (GR-169) SENTENCE 1 (`Dn` even, `DM = 3Dn/2`, `DSl = 3Dn`,
           `D(excess) = 0`) holds for a Y-reduction too -- it uses only
           cubicity and tightness -- while (GR-169) SENTENCE 2 ("the move
           adds `3k - s` genuinely-new branches of total length `6k`") is
           FALSE for one, by explicit counterexample.
--wit      that `theta(4,4,4)` and `K4(3^6)` are BOTH `D = 0` class shapes
           under the canonical `gridcol.class_shape`, and that the second is
           obtained from the first by a Y->Delta move.
--cut      that (GR-170) at `B` = the new triangle reads exactly
           `Sigma_{beta ∋ v} l_beta <= 11` at the contracted hub `v` of the
           parent -- i.e. it is (GR-173), which the parent already satisfies
           -- so the complement cut CANNOT kill deletions; measured as a
           slack over every move the census finds.
--contract the census: over the landed `n_hub = 4, 6, 8` populations, how
           many shapes admit a Y-reduction to a smaller class shape, and how
           many (shape, hub set, boundary re-length) triples survive.
--ladder   that (GR-175)'s `CL_m` carries NO connected hub set with cut 3 at
           `|A| in {3, 5}`, MEASURED at `m = 6..11`, so the positive does NOT
           reach the infinite family -- the limitation is measured, not
           assumed.  (`CL_m` is triangle-free for every `m >= 4` by a proof
           in the draft; the `|A| = 5` half is capped at `m <= 11`.)
--chain    that the move is not a small-`n` artefact: an unbroken chain of
           Y->Delta moves from `K4(3^6)` to `n_hub = 16` inside the
           `Lambda = empty` stratum, every member certified.
--blind    that `gexpand.reduction_frames` returns NOTHING at the witness's
           own child, by the two structural fences (`|W'| = 2k` even; every
           hub of `W'` at 0 or 2 outward darts) -- the blind axis exhibited
           rather than asserted.

CAPS, disclosed here and re-disclosed at each figure.
 * The census gates `n_hub <= 6` with `gridcol.class_shape` (CANONICAL: the
   `2^M` `no_rigid_branch_union` scan) and `n_hub = 8` with
   `cflank.cubic_habitat` (the `2^n` (GR-25) cut criterion), exactly as
   `gexpand.py` does; the two are asserted equivalent only at `n_hub <= 6`.
 * `--contract` at `n_hub = 8` runs over `aglu._pool8()`, which is the
   **`Lambda = empty`** stratum (39 689 shapes), NOT a general `n_hub = 8`
   pool.  `Lambda != empty` at `n_hub = 8` is NOT swept.
 * `|A| = 3` only, at `n_hub = 8`, for runtime; `|A| in {3, 5}` at
   `n_hub <= 6`.  A Y-reduction at `|A| >= 7` is NOT searched.
 * The move family searched is HUB-CONTRACTION (cut 3).  A non-additive move
   at `Delta n = 0`, and one deleting a hub set of cut `!= 3`, are NOT
   searched -- a positive needs only a witness, so this cap bounds the
   census, not the verdict.
 * Everything is at `D = 0` (cubic `G°`).
"""

import argparse
import itertools
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from cflank import cubic_habitat                                     # noqa: E402
from gridcol import class_shape, cubic_iso_classes                   # noqa: E402
from gisland import stratum                                          # noqa: E402
from aglu import _pool8                                              # noqa: E402
import gexpand                                                       # noqa: E402

X_SEED = 20260910          # no rng is used; pinned for the README convention

THETA444 = [(0, 1, 4), (0, 1, 4), (0, 1, 4)]
K4_3 = [(0, 1, 3), (0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3), (2, 3, 3)]


# --------------------------------------------------------------- primitives --

def specs(hedges, lens):
    return [(u, w, L) for (u, w), L in zip(hedges, lens)]


def canon_gate(n, hedges, lens):
    """The CANONICAL oracle where it is affordable, the (GR-25) cut criterion
    where it is not -- the same split `gexpand.py` uses, restated so the
    figure carries it."""
    if n <= 6:
        return class_shape(specs(hedges, lens)) is not None
    return cubic_habitat(n, hedges, list(lens))


def induced(n, hedges, A):
    """(inside branch indices, boundary branch indices, outside indices)."""
    ins, bd, out = [], [], []
    for i, (u, w) in enumerate(hedges):
        a, b = (u in A), (w in A)
        if a and b:
            ins.append(i)
        elif a or b:
            bd.append(i)
        else:
            out.append(i)
    return ins, bd, out


def connected_inside(hedges, A, ins):
    if len(A) <= 1:
        return True
    adj = {v: [] for v in A}
    for i in ins:
        (u, w) = hedges[i]
        adj[u].append(w)
        adj[w].append(u)
    st = [next(iter(A))]
    seen = {st[0]}
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    return len(seen) == len(A)


_GATE_MEMO = {}


def memo_gate(n, hedges, lens):
    """`canon_gate` memoized on a canonical key -- the census hits the same
    parent thousands of times."""
    key = (n, tuple(sorted((min(u, w), max(u, w), L)
                           for (u, w), L in zip(hedges, lens))))
    r = _GATE_MEMO.get(key)
    if r is None:
        r = canon_gate(n, hedges, lens)
        _GATE_MEMO[key] = r
    return r


_CUT3 = {}


def cut3_sets(n, hedges, sizes=(3,)):
    """Every connected hub set `A` with `partial(A) = 3` and odd
    `|A| >= 3` -- the LENGTH-INDEPENDENT half of the Y-reduction search,
    so it is computed once per hub multigraph.

    SCOPE, added 2026-09-12 after direction GTRIFREE and a user ruling.
    The guard below admits `|A|` up to `n - 1`, and that is NOT what the
    arc's induction means by a move.  Because `partial(A) = partial(V-A)`
    in a cubic hub multigraph, EVERY hub's complement is a frame at
    `|A| = n-1` with forced budget 12, so at that size every `D = 0`
    class shape reduces -- in one step, to `n_hub = 2`, transporting
    nothing.  RULED 2026-09-12: the intended move class is LOCAL, i.e.
    `|A|` bounded independently of `n`.  The unbounded frames are real
    and are recorded at §(K-grid) (GR-220) as a statement about this
    definition; they are out of scope for the `G°` induction.  The guard
    is deliberately NOT changed -- narrowing it would invalidate
    (GR-217)-(GR-223)'s landed measurements, which are measurements OF
    the unbounded family."""
    ck = (n, tuple(hedges), tuple(sizes))
    if ck in _CUT3:
        return _CUT3[ck]
    out = []
    for sz in sizes:
        if sz % 2 == 0 or sz < 3 or n - sz + 1 < 2:
            continue
        for A in itertools.combinations(range(n), sz):
            As = set(A)
            ins, bd, _o = induced(n, hedges, A)
            if 3 * sz - 2 * len(ins) != 3 or len(bd) != 3:
                continue
            if not connected_inside(hedges, As, ins):
                continue
            out.append((A, tuple(ins), tuple(bd)))
    _CUT3[ck] = out
    return out


def y_reductions(n, hedges, lens, sizes=(3,), gate=None, hi=5,
                 frames=None):
    """Every Y-reduction of this shape: contract a connected hub set `A` with
    `partial(A) = 3` and odd `|A| >= 3` to ONE hub, re-lengthing the three
    boundary branches over every distribution the budget allows.

    Yields `(A, budget, parent_hedges, parent_lens, newlens)`.  `budget` is
    `Sigma_boundary l'`, FORCED by cubicity + tightness (see the module
    docstring) -- it is not a free parameter, and the three-way split of it
    is the ONLY freedom the move has."""
    gate = gate or memo_gate
    for (A, ins, bd) in (frames if frames is not None
                         else cut3_sets(n, hedges, sizes)):
        As = set(A)
        sz = len(A)
        out = [i for i in range(len(hedges)) if i not in ins and i not in bd]
        budget = (sum(lens[i] for i in bd) + sum(lens[i] for i in ins)
                  - 3 * (sz - 1))
        if budget < 3 or budget > 3 * hi:
            continue
        keep = sorted(set(range(n)) - As)
        rel = {v: i + 1 for i, v in enumerate(keep)}
        phe = [(rel[hedges[i][0]], rel[hedges[i][1]]) for i in out]
        ple = [lens[i] for i in out]
        ends = []
        for i in bd:
            (u, w) = hedges[i]
            ends.append(rel[w] if u in As else rel[u])
        che0 = phe + [(0, e) for e in ends]
        if any(u == w for (u, w) in che0):
            continue
        for a in range(1, hi + 1):
            for b in range(1, hi + 1):
                c = budget - a - b
                if c < 1 or c > hi:
                    continue
                cle = ple + [a, b, c]
                if gate(n - sz + 1, che0, cle):
                    yield (A, budget, tuple(che0), tuple(cle), (a, b, c))


def ydelta(n, hedges, lens, v, tri, outer):
    """The EXPANSION direction: DELETE hub `v` and replace it by a triangle
    on three new hubs, the three former darts of `v` becoming the triangle's
    boundary with lengths `outer`.  The surviving hubs are relabelled, so
    `v` really is gone -- the positive control for `y_reductions`."""
    di = [i for i, (u, w) in enumerate(hedges) if u == v or w == v]
    if len(di) != 3:
        return None
    others = [(hedges[i][0] if hedges[i][1] == v else hedges[i][1])
              for i in di]
    keep = [x for x in range(n) if x != v]
    rel = {x: j for j, x in enumerate(keep)}
    nh = [(rel[hedges[i][0]], rel[hedges[i][1]])
          for i in range(len(hedges)) if i not in di]
    nl = [lens[i] for i in range(len(hedges)) if i not in di]
    b = n - 1
    for j, o in enumerate(others):
        nh.append((b + j, rel[o]))
        nl.append(outer[j])
    nh += [(b, b + 1), (b, b + 2), (b + 1, b + 2)]
    nl += list(tri)
    return n + 2, nh, nl


# ------------------------------------------------ [GNA-1] --law -------------

def leg_law():
    """[GNA-1] (GR-169) redone WITHOUT the surviving-hubs assumption."""
    print("[GNA-1] the (GR-169) accounting at a HUB-DELETING move (no rng)")
    t0 = time.time()
    # sentence 1: pure cubicity + tightness, so it survives verbatim.
    bad = 0
    for nP in range(2, 40, 2):
        for dn in range(2, 12, 2):
            nC = nP + dn
            MP, MC = 3 * nP // 2, 3 * nC // 2
            cP, cB = MP - nP + 1, MC - nC + 1
            SP, SC = 6 * cP, 6 * cB
            if MC - MP != 3 * dn // 2 or SC - SP != 3 * dn:
                bad += 1
            if (SC - 2 * MC) != (SP - 2 * MP):
                bad += 1
    assert bad == 0, "(GR-169) sentence 1 failed -- it is pure arithmetic"
    print("  (GR-169) sentence 1 -- `Dn` even, `DM = 3Dn/2`, `DSl = 3Dn`, "
          "`D(excess) = 0` -- HOLDS for any move between two `D = 0` shapes,")
    print("  hub-deleting included: the derivation uses ONLY `2M = 3n` and "
          "`Sl = 6(M - n + 1)`, never how the hubs correspond.  0 misses over")
    print("  n_P = 2..38, Dn = 2..10.")
    # sentence 2: the counterexample.
    tri = 9                       # the witness's triangle, total length 9
    k = 1
    print()
    print("  (GR-169) sentence 2 -- 'the move adds `3k - s` genuinely-new "
          "branches of total length `6k`' -- is FALSE for a Y->Delta move:")
    print(f"    at the witness `theta(4,4,4) -> K4(3^6)`, k = {k}, so it "
          f"predicts total new length 6k = {6 * k};")
    print(f"    the ACTUAL new branches are the triangle, total length "
          f"{tri}, and the three boundary branches are SHORTENED 4 -> 3,")
    print(f"    so DSl = {tri} - 3 = {tri - 3} = 6k.  The IDENTITY of "
          f"sentence 1 holds; the LOCALIZATION of sentence 2 does not.")
    print("    Sentence 2 presupposes every parent hub survives, so that no "
          "parent-derived branch changes length.  A hub-deleting move")
    print("    re-lengths the branches AT the deleted hub, and those are "
          "inside the changed region.")
    assert tri >= 7, "a triangle in a class shape needs total length >= 7"
    assert tri - 3 == 6 * k
    print(f"  [{time.time() - t0:.1f}s]")
    return 0


# ------------------------------------------------ [GNA-2] --wit -------------

def leg_wit():
    """[GNA-2] THE WITNESS, through the canonical oracle."""
    print("[GNA-2] the non-additive witness (no rng)")
    t0 = time.time()
    ep = class_shape(THETA444)
    ec = class_shape(K4_3)
    assert ep is not None, "theta(4,4,4) is not a class shape"
    assert ec is not None, "K4(3^6) is not a class shape"
    print("  parent  theta(4,4,4)  n_hub = 2, M = 3, Sl = 12, exc = 6   -- "
          "`gridcol.class_shape`: PASS")
    print("  child   K4(3,3,3,3,3,3) n_hub = 4, M = 6, Sl = 18, exc = 6 -- "
          "`gridcol.class_shape`: PASS")
    # the move, checked structurally rather than asserted
    n, he, ls = 4, [e for e, _ in [((u, w), L) for u, w, L in K4_3]], \
        [L for _, _, L in K4_3]
    he = [(u, w) for u, w, _ in K4_3]
    got = list(y_reductions(n, he, ls, sizes=(3,)))
    hits = [g for g in got if sorted(g[3]) == [4, 4, 4]]
    assert hits, "the witness's own Y-reduction was not found by the search"
    A, budget, phe, ple, nl = hits[0]
    print(f"  the Y-reduction found by `y_reductions`: A = {A} (a triangle, "
          f"cut 3), forced boundary budget = {budget},")
    print(f"    parent = {sorted(ple)} on hedges {sorted(phe)} -- i.e. "
          f"theta(4,4,4).  {len(got)} (A, re-length) pairs survive in all.")
    assert sum(nl) == budget == 12
    # a SECOND witness, where the untouched part is not a single hub
    prism_he = [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
                (0, 3), (1, 4), (2, 5)]
    prism_ls = [3, 3, 3, 3, 3, 3, 2, 2, 2]
    assert class_shape(specs(prism_he, prism_ls)) is not None
    pr = list(y_reductions(6, prism_he, prism_ls, sizes=(3,)))
    assert pr, "the prism admits no Y-reduction"
    print(f"  SECOND witness, n_hub = 6 -> 4: the PRISM `C3 x K2` with both "
          f"triangles at (3,3,3) and all three rungs at 2 --")
    print(f"    `gridcol.class_shape`: PASS; {len(pr)} Y-reductions to "
          f"n_hub = 4 class shapes, e.g. contract {pr[0][0]} -> lens "
          f"{list(pr[0][3])}.")
    print("    Here the untouched part is FOUR hubs and three branches, so "
          "the move is local in the induction's sense, not a")
    print("    degenerate whole-graph coincidence at n_hub = 2.")
    # both directions of the identity, computed from the two shapes rather
    # than written out as literals (the literal form asserted nothing)
    lp = [L for _, _, L in THETA444]
    lc = [L for _, _, L in K4_3]
    dn, dM, dS = 4 - 2, len(lc) - len(lp), sum(lc) - sum(lp)
    assert dn == 2 and dM == 3 * dn // 2 and dS == 3 * dn
    assert sum(L - 2 for L in lp) == sum(L - 2 for L in lc) == 6
    print("  Dn = +2, DM = +3 = 3Dn/2, DSl = +6 = 3Dn, D(excess) = 0.  ONE "
          "parent hub is deleted and THREE are added: NON-ADDITIVE.")
    print("  (GR-172) says `Dn = 2` is impossible.  Its PROOF is (GR-169) "
          "sentence 2 plus (GR-170), both additive-scoped; this witness")
    print("  is at Dn = 2 and refutes the sentence READ STANDALONE.")
    print(f"  [{time.time() - t0:.1f}s]")
    return 0


# ------------------------------------------------ [GNA-3] --cut -------------

def leg_cut():
    """[GNA-3] the coordinator's proposed mechanism, ELIMINATED."""
    print("[GNA-3] (GR-170) at the new region of a Y->Delta move (no rng)")
    t0 = time.time()
    print("  Claim: for a Y->Delta move with new triangle "
          "`B = {w1,w2,w3}`, (GR-170) at `B` reads")
    print("    exc_B <= 2*partial(B) - 1 = 2*3 - 1 = 5,")
    print("  and exc_B = (Sigma_t - 6) + Sigma_i(l'_i - 2) = "
          "Sigma_t + Sigma_i l'_i - 12 = (Sigma_i l_i + 6) - 12")
    print("       = Sigma_{beta ∋ v} l_beta - 6   at the PARENT hub `v`.")
    print("  So (GR-170) at `B` <=> Sigma_{beta ∋ v} l_beta <= 11, which is "
          "(GR-173) -- a property the PARENT already has.")
    print("  The complement cut is therefore AUTOMATICALLY SATISFIED at "
          "every Y->Delta move.  It does NOT extend to deletions.")
    # measured over every move the census finds at n_hub = 4 and 6
    checked = viol = outside = 0
    mins = None
    for n in (4, 6):
        for hedges, lens, _mem, _auts in stratum(n, lamcap=99):
            for (A, budget, phe, ple, nl) in y_reductions(
                    n, list(hedges), list(lens), sizes=(3,)):
                ins, bd, _o = induced(n, list(hedges), set(A))
                excB = sum(lens[i] - 2 for i in ins + bd)
                slack = 2 * 3 - 1 - excB
                if n - len(A) < 2:
                    outside += 1          # (GR-170)'s `|V - B| >= 2` fails
                    continue
                checked += 1
                if slack < 0:
                    viol += 1
                mins = slack if mins is None else min(mins, slack)
    print(f"  MEASURED over the exhaustive n_hub = 4 and 6 strata "
          f"(`gisland.stratum`, lamcap = 99, i.e. `Lambda` unrestricted),")
    print(f"    at every (child, contracted triangle, re-length) triple the "
          f"search certifies:")
    print(f"      {checked} instances WHERE (GR-170) APPLIES "
          f"(`|V - B| >= 2`): {viol} violations, min slack {mins}.")
    print(f"      {outside} instances at n_hub = 4, where `V - B` is a "
          f"SINGLE hub and (GR-170)'s hypothesis fails outright --")
    print(f"        these have exc_B = 6, slack -1, and are legal: they are "
          f"(GR-173)'s own n_hub = 2 exception seen from the child.")
    assert viol == 0, "a surviving move violates (GR-170) where it applies"
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------- [GNA-4] --contract -------------

def leg_contract():
    """[GNA-4] the Y-reduction census over the landed populations."""
    print("[GNA-4] the Y-reduction census (no rng)")
    t0 = time.time()
    for n, sizes in ((4, (3,)), (6, (3, 5))):
        tot = red = trip = 0
        for hedges, lens, _mem, _auts in stratum(n, lamcap=99):
            tot += 1
            got = list(y_reductions(n, list(hedges), list(lens), sizes=sizes))
            if got:
                red += 1
                trip += len(got)
        print(f"  n_hub = {n}: {red} of {tot} class shapes admit a "
              f"Y-reduction to a smaller class shape ({trip} "
              f"(hub set, re-length) triples).")
        print(f"    population `gisland.stratum({n}, lamcap=99)`: EXHAUSTIVE, "
              f"`Lambda` unrestricted.  |A| in {sizes}.  Parent gate "
              f"`gridcol.class_shape` (CANONICAL).")
    # n_hub = 8, Lambda = empty only; frames precomputed per hub class
    pool, _nep = _pool8()
    tot = red = trip = withtri = 0
    ncls = ntricls = 0
    for hedges, lens_ok in pool:
        fr = cut3_sets(8, list(hedges), sizes=(3,))
        ncls += 1 if lens_ok else 0
        if fr and lens_ok:
            ntricls += 1
        for lens in lens_ok:
            tot += 1
            if not fr:
                continue
            withtri += 1
            got = list(y_reductions(8, list(hedges), list(lens),
                                    frames=fr, gate=fast_gate6))
            if got:
                red += 1
                trip += len(got)
    print(f"  n_hub = 8: {red} of {tot} class shapes admit a Y-reduction "
          f"({trip} (hub set, re-length) triples).")
    print(f"    of those, {withtri} shapes ({ntricls} of {ncls} inhabited hub "
          f"classes) carry a connected cut-3 hub set at all, and "
          f"{red} of {withtri} of THOSE reduce.")
    print("    population `aglu._pool8()`: the **`Lambda = empty`** stratum, "
          "39 689 shapes -- NOT a general n_hub = 8 pool.")
    print("    |A| = 3 only.  Parent gate `cflank.cubic_habitat` (the "
          "(GR-25) cut criterion at n_hub = 6), not `class_shape`:")
    print("    the two are asserted equivalent over the whole n_hub <= 6 "
          "pool ((GR-25)'s own `--law`), and the n_hub <= 6 rows above")
    print("    re-run the same search under the canonical oracle.")
    assert tot == 39689, "the n_hub = 8 habitat count moved"
    print("  COMPARE (GR-174)(i): '0 of 39 689 admit ANY reduction', "
          "measured with `gexpand.reductions`, which is ADDITIVE-ONLY.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def fast_gate6(n, hedges, lens):
    return cubic_habitat(n, hedges, list(lens))


# ---------------------------------------------- [GNA-7] --chain -------------

def leg_chain(top=16, lo=2):
    """[GNA-7] an UNBROKEN chain of Y->Delta moves, so the positive is not a
    small-`n` artefact."""
    print(f"[GNA-7] the Y->Delta chain from K4(3^6), `Lambda = empty` "
          f"(lo = {lo}), to n_hub = {top} (no rng)")
    t0 = time.time()
    n, he, ls = 4, [(u, w) for u, w, _ in K4_3], [L for _, _, L in K4_3]
    assert class_shape(specs(he, ls)) is not None
    print(f"  n_hub =  4  K4(3^6)                        "
          f"class_shape: PASS")
    steps = 0
    while n < top:
        found = None
        for v in range(n):
            sv = sum(L for (u, w), L in zip(he, ls) if u == v or w == v)
            for tri in itertools.product(range(lo, 6), repeat=3):
                if sum(tri) < 7:
                    continue
                for outer in itertools.product(range(lo, 6), repeat=3):
                    if sum(tri) + sum(outer) != sv + 6:
                        continue
                    r = ydelta(n, he, ls, v, tri, outer)
                    if r and cubic_habitat(r[0], r[1], list(r[2])):
                        found = (v, tri, outer, r)
                        break
                if found:
                    break
            if found:
                break
        assert found, f"the chain broke at n_hub = {n}"
        v, tri, outer, (n, he, ls) = found
        steps += 1
        assert sum(L - 2 for L in ls) == 6, "the excess law broke"
        assert min(ls) >= lo
        canon = ("PASS" if (n <= 8 and class_shape(specs(he, ls)) is not None)
                 else (f"n/a (M = {len(he)})" if n > 8 else "FAIL"))
        print(f"  n_hub = {n:2d}  delete hub {v}, triangle {tri}, boundary "
              f"{outer}   habitat: PASS   class_shape: {canon}")
    print(f"  {steps} consecutive NON-ADDITIVE moves; every member a "
          f"`D = 0` class shape with excess exactly 6 and `Lambda = empty`.")
    print("  The n_hub = 6 and n_hub = 8 members are certified by the "
          "CANONICAL `gridcol.class_shape`; above that by `cubic_habitat`")
    print("  (the (GR-25) cut criterion), whose equivalence to "
          "`class_shape` is asserted only at n_hub <= 6.  Disclosed.")
    print(f"  CAP: greedy, first hit at each level; top = {top}.  This is a "
          f"CONSTRUCTION, so one witness per level is a proof at that")
    print("  level; it is NOT a proof that the chain continues forever.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# --------------------------------------------- [GNA-5] --ladder -------------

def ladder(m):
    """(GR-175)'s `CL_m`: `C_m x K2`, six rungs of length 3 pairwise
    non-adjacent, every other branch of length 2."""
    he, ls = [], []
    # SIX length-3 rungs.  (GR-175) says "for every `m >= 4`", but six
    # PAIRWISE NON-ADJACENT branches need `>= 12` hubs, so the construction
    # is EMPTY at m = 4 and m = 5 -- `gexpand --irred` measured m = 6..11,
    # which is exactly its realizable range.  Reported as a scope correction.
    assert m >= 6, "the six-rung construction needs m >= 6"
    rung_at = set(range(6))
    for i in range(m):
        he.append((i, (i + 1) % m))
        ls.append(2)
        he.append((m + i, m + (i + 1) % m))
        ls.append(2)
    for i in range(m):
        he.append((i, m + i))
        ls.append(3 if i in rung_at else 2)
    return 2 * m, he, ls


def leg_ladder():
    """[GNA-5] the LIMIT of the positive."""
    print("[GNA-5] does the Y-reduction reach (GR-175)'s infinite family? "
          "(no rng)")
    t0 = time.time()
    for m in range(6, 12):
        n, he, ls = ladder(m)
        assert cubic_habitat(n, he, ls), f"CL_{m} is not a class shape"
        cuts3 = 0
        for sz in (3, 5):
            for A in itertools.combinations(range(n), sz):
                ins, bd, out = induced(n, he, set(A))
                if 3 * sz - 2 * len(ins) == 3 and connected_inside(
                        he, set(A), ins):
                    cuts3 += 1
        got = list(y_reductions(n, he, ls, sizes=(3, 5),
                                gate=lambda a, b, c: cubic_habitat(a, b, list(c))))
        print(f"  CL_{m} (n_hub = {2 * m}): class shape PASS; "
              f"connected hub sets with cut 3 at |A| in (3,5): {cuts3}; "
              f"Y-reductions found: {len(got)}")
        assert cuts3 == 0 and not got
    print("  CL_m has girth 4 in the hub multigraph and no cut-3 hub set at "
          "|A| = 3 or 5, so NO Y-reduction applies at any m in 6..11.")
    print("  CAP: |A| in {3, 5} and m in 6..11 -- 'not found under cap', "
          "never 'does not exist'.  The POSITIVE therefore does NOT")
    print("  revive an induction over the whole stratum: (GR-175)'s family "
          "stays irreducible under this move family too.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ---------------------------------------------- [GNA-6] --blind -------------

def leg_blind():
    """[GNA-6] the architectural blind axis, exhibited not asserted."""
    print("[GNA-6] `gexpand.reduction_frames` at the witness's own child "
          "(no rng)")
    t0 = time.time()
    he = [(u, w) for u, w, _ in K4_3]
    ls = [L for _, _, L in K4_3]
    fr = gexpand.reduction_frames(4, tuple(he), kmax=3, kmin=1)
    got = list(gexpand.reductions(4, he, ls, kmax=3, kmin=1))
    print(f"  frames at K4(3^6), kmin = 1, kmax = 3: {len(fr)}; "
          f"reductions found: {len(got)}")
    assert not got, "gexpand found the Y-reduction after all"
    print("  WHY, from the source: `reduction_frames` iterates "
          "`itertools.combinations(range(n), 2*k)` -- |W'| is EVEN, while a")
    print("  contracted triangle has |A| = 3; and it rejects any hub of W' "
          "whose outward-dart count is not 0 or 2, while each triangle hub")
    print("  has exactly 1.  Two independent fences, both structural.  The "
          "blind axis is in the MOVE MODEL, not in a parameter:")
    print("  `apply_move` never removes a parent hub, and "
          "`move_complement_slack` is (GR-25)(i) at the complement of the")
    print("  BRAND-NEW hubs -- a set that only exists in an additive move.")
    # and the (GR-174) figure it therefore cannot have covered
    print("  CONSEQUENCE for (GR-174): its '0 of 39 689 reducible' is "
          "'0 ADDITIVELY reducible'.  [GNA-4] re-measures with deletions.")
    print(f"  [{time.time() - t0:.1f}s]")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--law', action='store_true')
    ap.add_argument('--wit', action='store_true')
    ap.add_argument('--cut', action='store_true')
    ap.add_argument('--contract', action='store_true')
    ap.add_argument('--ladder', action='store_true')
    ap.add_argument('--blind', action='store_true')
    ap.add_argument('--chain', action='store_true')
    ap.add_argument('--validate', action='store_true')
    a = ap.parse_args()
    rc = 0
    if a.law or a.validate:
        rc |= leg_law()
        print()
    if a.wit or a.validate:
        rc |= leg_wit()
        print()
    if a.cut or a.validate:
        rc |= leg_cut()
        print()
    if a.blind or a.validate:
        rc |= leg_blind()
        print()
    if a.ladder or a.validate:
        rc |= leg_ladder()
        print()
    if a.chain or a.validate:
        rc |= leg_chain()
        print()
    if a.contract or a.validate:
        rc |= leg_contract()
        print()
    if not any(vars(a).values()):
        ap.print_help()
    return rc


if __name__ == '__main__':
    sys.exit(main())
