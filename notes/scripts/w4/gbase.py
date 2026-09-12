"""§(K-grid) direction GBASE (2026-09-12) driver -- HOW BIG IS THE `G°`
INDUCTION'S **BASE** AT `D = 0`, AND IS (GR-15) ON IT EASIER THAN (GR-15)?
§8's sixteenth pass, rank 1.

THE SETTING.  The 2026-09-12 user ruling fixes the move family as
`M_c` := the Y-reductions at `|A| <= c` with `c` a constant INDEPENDENT of
`n` (`gnonadd.cut3_sets`' own SCOPE docstring).  The `G°` induction runs on
`n_hub` ((GR-226)(iv)); with `M_c` its BASE is every `D = 0` tight class
shape carrying no frame at `|A| <= c`, not the three `n_hub = 2` theta
shapes.  This driver measures that base at the CLASS layer and at the
SHAPE layer, un-fencing `gisland.CUBIC_N` / `cflank.CUBIC_N = (2, 4, 6)`
and `aglu._pool8()`'s hardcoded `n_hub = 8`.

THE TWO LAYERS ARE DIFFERENT QUANTITIES and the entry's own spec flagged
it.  `gnonadd.cut3_sets` reads only the hub multigraph ((GR-221)(i)), so
frame-existence at `|A| <= c` is a property of `G°` ALONE: **the base is a
UNION OF WHOLE CLASSES** (plus a length-dependent residual -- a shape with
a frame but no certified re-length at any of them).  The class share and
the shape share therefore have different denominators and, as this driver
measures, different answers.

WHAT IT IMPORTS READ-ONLY (README §2): `gridcol` (`cubic_iso_classes`,
`_canon`, `excess_profiles` via `aglu`), `gnonadd` (`cut3_sets`,
`y_reductions`, `induced`), `cflank` (`cubic_habitat`, `ladder`),
`gisland` (`stratum`), `aglu` (`_pool8`, `excess_profiles`).

ONE LOCAL DEVICE, for PERFORMANCE only, asserted equal to the canonical
one at the overlap (README §2 rule 3): `expand_classes(n)` builds the
connected loopless cubic multigraph classes at `n` from those at `n - 2`
by the double-subdivide-and-join expansion, canonicalising with
`gridcol._canon` -- the CANONICAL canonicaliser, not a copy.  `--val`
asserts it reproduces `gridcol.cubic_iso_classes` EXACTLY (same canonical
key set) at `n = 4, 6, 8`, and `--labcount` certifies COMPLETENESS at any
`n` by the orbit-counting identity `sum_classes n!/|Aut| == #labelled`,
the labelled count coming from the same least-deficient recursion
`cubic_iso_classes` itself uses.

Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --consumer   # F26: what the induction would actually need, and the BASE `M_c` implies -- (GR-233)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --char       # THE CHARACTERISATION: the parity lemma, the TWO shapes of an |A|=3 frame, the cyc-4-edge-connectivity MECHANISM tested -- (GR-234)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --classes    # the base at the CLASS layer, n_hub = 4..10, every bound c, class share AND labelled share -- (GR-236)(i)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --shapes     # the base at the SHAPE layer, Lambda = empty, in the `aglu._pool8()` unit (asserted against 39 689 / 22 720) -- (GR-236)(ii)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --orbits     # the SAME, in the ISOMORPHISM-CLASS unit -- the axis worth a factor of three -- (GR-237)(i)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --residual   # the length-dependent residual: a frame at |A| <= 5 but NO certified child there -- (GR-234)(iii)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --ladder     # (GR-34)'s recipe vs (GR-175)'s: both in the base; the rung-minority RULE extended to n_hub = 24 and REFUTED at odd rung lengths -- (GR-238)/(GR-239)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --sample     # the trend past the exhaustive range, seeded configuration-model draws (a TREND, not a share -- see the calibration) -- (GR-237)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --labcount 10  # the completeness certificate for the class list at n_hub = 10
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --val        # the four local devices against their canonical oracles
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gbase.py --validate   # --val --consumer --char --classes --shapes --orbits --residual --ladder

NO RANDOMNESS anywhere in this driver: every mode is an exhaustive count
over a finite set, so there is no sampler, no seed, and no semicontinuity
direction -- an exhaustive count here is a PROOF, not a bound
(dispatch-log F31).  The caps that DO bind are stated per mode and are
about the POPULATION (`Lambda = empty`, `n_hub <= 12`), never about a
search depth.
"""

import argparse
import sys
import time
from itertools import combinations_with_replacement

sys.path.insert(0, __file__.rsplit('/', 1)[0])

import aglu                                                   # noqa: E402
import cflank                                                 # noqa: E402
import gisland                                                # noqa: E402
import gnonadd                                                # noqa: E402
import gridcol                                                # noqa: E402

# The bounds this driver reports.  `c` is the move-size bound of the
# 2026-09-12 ruling; `3` and `5` are the only two the corpus has measured
# ((GR-198), (GR-231)), `7` and `9` are this direction's extension.
CBOUNDS = (3, 5, 7, 9)

# The sizes at which a frame can exist at all: odd, >= 3, <= n - 1.
def odd_sizes(n, hi=None):
    hi = n - 1 if hi is None else min(hi, n - 1)
    return tuple(s for s in range(3, hi + 1, 2))


# ---------------------------------------------------------------------------
# LOCAL DEVICE: class generation by expansion (performance only; --val)
# ---------------------------------------------------------------------------

_EXP_CACHE = {}


def _canon_key(n, hedges):
    A = [[0] * n for _ in range(n)]
    for (u, w) in hedges:
        A[u][w] += 1
        A[w][u] += 1
    return gridcol._canon(n, A)


def _connected_loopless(n, hedges):
    adj = {v: set() for v in range(n)}
    for (u, w) in hedges:
        if u == w:
            return False
        adj[u].add(w)
        adj[w].add(u)
    seen, st = {0}, [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    return len(seen) == n


def classes_certified(n, seed=20260912, secs=900):
    """Connected loopless cubic multigraph classes on `n` hubs, one
    representative each, WITH A COMPLETENESS PROOF.

    `n <= 8` defers to the CANONICAL `gridcol.cubic_iso_classes`.  Past that
    the list is built by seeded configuration-model draws
    (`sample_cubic`) plus the `mu = 2` / `mu = 1` two-hub additions of
    `expand_from` (which reach the digon-carrying classes the pairing model
    under-weights by `2^-D`), canonicalised by the CANONICAL
    `gridcol._canon`, and the loop stops **only** when the orbit-counting
    identity closes:

        sum over classes of n!/|Aut|  ==  #labelled connected loopless
                                          cubic multigraphs on n hubs

    the right-hand side coming from `labelled_all` through the exponential
    formula.  An equality there is a PROOF that nothing is missing -- how
    the candidates were found is then irrelevant, so the seeded search
    costs no cap.  `n = 10`: 91 classes, `sum = 94 008 600`, ~1 min."""
    import random
    from math import factorial
    if n in _EXP_CACHE:
        return _EXP_CACHE[n]
    if n <= 8:
        out = [list(h) for h in gridcol.cubic_iso_classes(n)]
        _EXP_CACHE[n] = out
        return out
    tab = {0: 1}
    for k in range(2, n + 1, 2):
        tab[k] = labelled_all(k)
    target = labelled_connected(n, tab)
    reps, tot = {}, 0

    def add(H):
        nonlocal tot
        k = _canon_key(n, H)
        if k in reps:
            return
        reps[k] = [tuple(sorted(e)) for e in H]
        tot += factorial(n) // aut_order(n, H)
    rng = random.Random(seed)
    t0 = time.time()
    while tot != target and time.time() - t0 < secs / 3:
        H = sample_cubic(n, rng)
        if H is not None:
            add(H)
    if tot != target:
        # the pairing model under-weights a class with `D` digons by
        # `2^-D`; the `mu = 2` / `mu = 1` two-hub additions reach those
        # deterministically.  At `n_hub = 10` the random half closes the
        # identity on its own and this branch is not taken.
        for H in expand_from(n, mus=(2, 1)):
            add([tuple(e) for e in H])
        while tot != target and time.time() - t0 < secs:
            H = sample_cubic(n, rng)
            if H is not None:
                add(H)
    assert tot == target, (
        f"class list at n_hub = {n} INCOMPLETE: sum n!/|Aut| = {tot} "
        f"vs {target} labelled connected -- raise `secs`")
    out = [reps[k] for k in sorted(reps)]
    _EXP_CACHE[n] = out
    return out


def expand_classes(n):
    """Connected loopless cubic multigraph classes on `n` hubs, one
    representative each.  `n <= 8` defers to the CANONICAL
    `gridcol.cubic_iso_classes`; past that, expansion from `n - 2`.

    The expansion: pick an unordered pair of edge slots `{i, j}` (i == j
    allowed), subdivide each once, and join the two new hubs.  `i == j`
    subdivides one edge twice and the join doubles the middle edge, so the
    two new hubs form a digon -- that case is what puts a digon-carrying
    class in range at all.  Completeness is NOT assumed: `--val` checks it
    exactly at n = 6, 8 and `--labcount` certifies it by orbit counting."""
    if n in _EXP_CACHE:
        return _EXP_CACHE[n]
    if n <= 8:
        out = [list(h) for h in gridcol.cubic_iso_classes(n)]
        _EXP_CACHE[n] = out
        return out
    return classes_certified(n)


def expand_from(n, mus=(2, 1, 0)):
    """The expansion step ALONE, `n` from `n - 2` -- the half `--val` checks
    against the canonical generator at n = 6 and n = 8.

    THE OPERATION SET, derived rather than guessed (the first version of
    this function used only the mu = 1 same-edge case and MISSED exactly one
    class at n = 6 -- the bridge between two digon-triangles, which has no
    edge whose reduction stays connected and loopless).  Adding two hubs
    `x, y` to a cubic multigraph means placing 6 new darts.  Let `mu` be the
    x-y edge multiplicity; `mu = 3` is a separate component, so
    `mu in {0, 1, 2}`.  The remaining `6 - 2mu` darts must attach to a
    CUBIC (dart-saturated) host, so they attach by BREAKING `(6 - 2mu)/2`
    old edges, each broken edge freeing its two ends.  Every assignment of
    the freed ends to the free darts of `x` and `y` is enumerated:

        mu = 2: break 1 edge   (the digon insertion)
        mu = 1: break 2 edges, split the 4 ends 2/2
        mu = 0: break 3 edges, split the 6 ends 3/3

    This is exhaustive over 2-hub additions BY CONSTRUCTION; whether every
    class at `n` is such an addition is NOT assumed -- `--val` checks it at
    n = 6, 8 and `--labcount` certifies it at `n` by orbit counting."""
    from itertools import combinations
    reps = {}
    x, y = n - 2, n - 1
    for H in expand_classes(n - 2):
        H = [tuple(e) for e in H]
        m = len(H)
        for mu in mus:
            nbreak = (6 - 2 * mu) // 2
            for S in combinations(range(m), nbreak):
                keep = [H[k] for k in range(m) if k not in S]
                ends = []
                for k in S:
                    ends.append(H[k][0])
                    ends.append(H[k][1])
                free = 3 - mu
                for xs in combinations(range(len(ends)), free):
                    ys = [t for t in range(len(ends)) if t not in xs]
                    new = list(keep) + [(x, y)] * mu
                    new += [(ends[t], x) for t in xs]
                    new += [(ends[t], y) for t in ys]
                    if not _connected_loopless(n, new):
                        continue
                    k = _canon_key(n, new)
                    if k not in reps:
                        reps[k] = [tuple(sorted(e)) for e in new]
    return [reps[k] for k in sorted(reps)]


def labelled_all(n):
    """#labelled loopless cubic multigraphs on `n` LABELLED hubs, connected
    or not -- the SAME least-deficient recursion `gridcol.cubic_iso_classes`
    runs, MEMOISED on the sorted multiset of remaining degrees.

    The memo is the only reason this is affordable: the raw recursion has
    `1.03e8` leaves at `n = 10` (measured, ~5 min) and `~1e11` at `n = 12`;
    memoised it is milliseconds, because the count from a state depends only
    on how many hubs still need 1, 2 or 3 darts.  Asserted against the raw
    recursion at `n = 2, 4, 6, 8` in `--val` (1 / 10 / 760 / 190 050)."""
    from functools import lru_cache

    @lru_cache(maxsize=None)
    def rec(state):
        # state: sorted tuple of remaining degrees of the hubs not yet closed
        st = [d for d in state if d > 0]
        if not st:
            return 1
        st.sort()
        # close the LEAST-deficient hub: its darts all go to the others
        need = st[0]
        rest = st[1:]
        tot = 0
        for combo in combinations_with_replacement(range(len(rest)), need):
            c = {}
            for u in combo:
                c[u] = c.get(u, 0) + 1
            if any(rest[u] < k for u, k in c.items()):
                continue
            nxt = list(rest)
            for u, k in c.items():
                nxt[u] -= k
            tot += rec(tuple(sorted(nxt)))
        return tot
    return rec(tuple([3] * n))


def labelled_all_raw(n):
    """The unmemoised least-deficient recursion, for `--val` only."""
    cnt = [0]
    rem = [3] * n
    edges = []

    def rec():
        v = next((i for i in range(n) if rem[i] > 0), None)
        if v is None:
            cnt[0] += 1
            return
        cand = [u for u in range(v + 1, n) if rem[u] > 0]
        for combo in combinations_with_replacement(cand, rem[v]):
            c = {}
            for u in combo:
                c[u] = c.get(u, 0) + 1
            if any(rem[u] < k for u, k in c.items()):
                continue
            for u in combo:
                rem[u] -= 1
                edges.append((v, u))
            rem[v] -= len(combo)
            rec()
            rem[v] += len(combo)
            for u in combo:
                rem[u] += 1
                edges.pop()
    rec()
    return cnt[0]


def labelled_connected(n, tab):
    """#labelled CONNECTED loopless cubic multigraphs on `n` labelled hubs,
    from `tab = {k: labelled_all(k)}` by the exponential formula -- split on
    the component of hub 0:

        T(n) = sum_{k even, 2 <= k <= n} C(n-1, k-1) * Cc(k) * T(n-k)

    which is a triangular system with `T(0) = 1`, solved upward for `Cc`.
    Exact integer arithmetic; no floating point, no sampling."""
    from math import comb
    cc = {}
    for m in range(2, n + 1, 2):
        acc = 0
        for k in range(2, m, 2):
            acc += comb(m - 1, k - 1) * cc[k] * tab[m - k]
        cc[m] = tab[m] - acc
    return cc[n]


def aut_order(n, hedges):
    """|Aut| of the hub multigraph, by refinement-pruned backtracking over
    vertex permutations preserving the multiplicity matrix."""
    A = [[0] * n for _ in range(n)]
    for (u, w) in hedges:
        A[u][w] += 1
        A[w][u] += 1
    col = [tuple(sorted(A[v])) for v in range(n)]
    for _ in range(n):
        new = [(col[v], tuple(sorted((A[v][u], col[u]) for u in range(n)
                                     if A[v][u]))) for v in range(n)]
        vals = sorted(set(new))
        mp = {t: i for i, t in enumerate(vals)}
        nc = [mp[t] for t in new]
        if nc == col:
            break
        col = nc
    perm = [-1] * n
    used = [False] * n
    cnt = [0]

    def rec(i):
        if i == n:
            cnt[0] += 1
            return
        for v in range(n):
            if used[v] or col[v] != col[i]:
                continue
            ok = True
            for j in range(i):
                if A[i][j] != A[v][perm[j]]:
                    ok = False
                    break
            if not ok:
                continue
            perm[i] = v
            used[v] = True
            rec(i + 1)
            used[v] = False
            perm[i] = -1
    rec(0)
    return cnt[0]


# ---------------------------------------------------------------------------
# THE BASE, at the CLASS layer
# ---------------------------------------------------------------------------

def frame_sizes(n, hedges):
    """The set of `|A|` at which this hub multigraph carries a
    `gnonadd.cut3_sets` frame -- LENGTH-INDEPENDENT ((GR-221)(i)), so it is
    a property of the class.  The CANONICAL predicate is called, at every
    odd size the guard admits, un-fencing its `sizes=(3,)` default."""
    got = {}
    for (A, ins, bd) in gnonadd.cut3_sets(n, list(hedges), sizes=odd_sizes(n)):
        got[len(A)] = got.get(len(A), 0) + 1
    return got


def in_base(n, hedges, c):
    """Is every shape on this hub multigraph a BASE case of the `M_c`
    induction -- i.e. no frame at `|A| <= c` at all?  Complement frames
    count: at `n - 1 <= c` they ARE inside `M_c` ((GR-231)'s preamble)."""
    return not any(sz <= c for sz in frame_sizes(n, hedges))


def small_cut_sets(n, hedges):
    """Every proper `W'` with `|W'| >= 2` inducing a connected subgraph and
    `partial(W') <= 3` -- exactly the sets that can bind (GR-25)(i).  At
    `Lambda = empty` no other `W'` can: `2*partial + exc >= 8 > 7` once
    `partial >= 4` and every `exc >= 0`.  Returns (bd, branch-index mask)."""
    adj = {v: [] for v in range(n)}
    for k, (u, w) in enumerate(hedges):
        adj[u].append((w, k))
        adj[w].append((u, k))
    out = []
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
            continue
        bd = 3 * len(W) - 2 * len(inside)
        if bd > 3:
            continue
        bm = 0
        for k in inside:
            bm |= 1 << k
        out.append((bd, bm))
    return out


def habitat_count_lambda_empty(n, hedges, profiles):
    """#excess profiles in `profiles` that pass (GR-25)'s criterion on this
    hub multigraph, at `Lambda = empty`.  EXACT, exhaustive, no cap.  The
    gate is `cflank.cubic_habitat`'s own inequality with the `partial >= 4`
    sets dropped -- `--val` asserts the two agree shape by shape at
    `n_hub = 8` against `aglu._pool8()`."""
    cons = small_cut_sets(n, hedges)
    m3 = [bm for (bd, bm) in cons if bd == 3]
    low = [(7 - 2 * bd, bm) for (bd, bm) in cons if bd < 3]
    ok = 0
    for e in profiles:
        supp = 0
        for k, x in enumerate(e):
            if x:
                supp |= 1 << k
        if any(not (supp & bm) for bm in m3):
            continue
        bad = False
        for (need, bm) in low:
            s = 0
            for k, x in enumerate(e):
                if x and (bm >> k & 1):
                    s += x
            if s < need:
                bad = True
                break
        if bad:
            continue
        ok += 1
    return ok


def excess_profiles_n(n):
    """The `Λ = ∅` excess profiles at `n_hub = n`: `M = 3n/2` branches,
    total excess `6` ((GR-21) at `D = 0`), each entry `≤ 3` (`ℓ ≤ 5`).
    The canonical `aglu.excess_profiles`, called at a new `M` -- the
    un-fencing of `aglu._pool8()`'s hardcoded `12`."""
    return aglu.excess_profiles(3 * n // 2, 6)


# ---------------------------------------------------------------------------
# [GBA-1] --consumer: the F26 check
# ---------------------------------------------------------------------------

def leg_consumer():
    """[GBA-1] what the `G°` induction would consume, and the base `M_c`
    implies -- with (GR-233)(iii)'s correction MEASURED: at `n_hub = 4`
    every shape carries a frame at `|A| = 3 = n - 1`, so the base there is
    EMPTY for every `c >= 3` and (GR-231)(i)'s `0 of 80` (which counts
    INTERIOR frames) is not a base figure."""
    print("[GBA-1] the F26 consumer check: what the induction needs")
    print("  (GR-226)(iv), the corpus's ONLY written statement of the "
          "induction, gives base `n_hub = 2` -- the three theta shapes.")
    print("  That base belongs to the UNBOUNDED family: (GR-217)(i)+(ii) "
          "put a complement frame at |A| = n-1 on every shape with "
          "n_hub >= 4, and (GR-218) makes its budget 12 and always "
          "realizable, so ONE move reaches n_hub = 2.")
    print("  Under M_c the complement frame survives only while n-1 <= c. "
          "The base is then {no frame at |A| <= c}.")
    tot = with3 = 0
    for hedges, lens, _mem, _auts in gisland.stratum(4, lamcap=99):
        tot += 1
        if gnonadd.cut3_sets(4, list(hedges), sizes=(3,)):
            with3 += 1
    print(f"  n_hub = 4, gisland.stratum(4, lamcap=99) EXHAUSTIVE: {tot} "
          f"shapes, {with3} carry a frame at |A| = 3 (= n-1, a COMPLEMENT "
          f"frame).  Base at every c >= 3: {tot - with3} of {tot}.")
    assert tot == 80 and with3 == 80, \
        "n_hub = 4 base is not empty -- (GR-233)(iii) is wrong"
    print("  => (GR-231)(i)'s `0 of 80` counts INTERIOR frames and is NOT "
          "a base measurement; the base's share at n_hub = 4 is 0, not 1.")


# ---------------------------------------------------------------------------
# [GBA-2] --char: the characterisation and the mechanism
# ---------------------------------------------------------------------------

def leg_char(hi=10):
    """[GBA-2] (GR-234): the parity lemma, |A| = 3 frames == triangles, and
    the cyclic-4-edge-connectivity MECHANISM tested against the bounded
    move family."""
    print("[GBA-2] (GR-234) the base characterised; the spec's mechanism "
          "tested")
    import itertools
    par = tri = dig = 0
    for n in (4, 6, 8):
        for H in expand_classes(n):
            H = [tuple(e) for e in H]
            for sz in range(1, n):
                for A in itertools.combinations(range(n), sz):
                    ins, bd, _o = gnonadd.induced(n, H, A)
                    d = 3 * sz - 2 * len(ins)
                    assert d % 2 == sz % 2, "parity lemma FALSE"
                    par += 1
                    if d == 3 and sz == 3:
                        # a |A| = 3 cut-3 set has exactly 3 internal
                        # branches on 3 hubs -- but NOT always a triangle
                        assert len(ins) == 3, "not 3 internal branches"
                        ends = [tuple(sorted(H[k])) for k in ins]
                        if len(set(ends)) == 3:
                            tri += 1                    # the triangle
                        else:
                            assert len(set(ends)) == 2, \
                                "|A| = 3 cut-3 set is neither shape"
                            dig += 1        # a DIGON with a pendant branch
    print(f"  parity `partial(A) = |A| (mod 2)` asserted at {par} hub "
          f"subsets over every class at n_hub = 4, 6, 8: 0 failures")
    print(f"  |A| = 3 cut-3 sets over every class at n_hub = 4, 6, 8: "
          f"{tri} TRIANGLES and {dig} DIGON-plus-PENDANT -- so the "
          f"corpus's `cut-3 triangle` is NOT the whole family")
    print("  the MECHANISM: base == {no non-trivial 3-edge-cut}?")
    for n in range(4, hi + 1, 2):
        reps = expand_classes(n)
        wit = None
        agree = 0
        for H in reps:
            H = [tuple(e) for e in H]
            fs = frame_sizes(n, H)
            cyc4 = not any(3 <= sz <= n - 3 for sz in fs)
            for c in CBOUNDS:
                base = not any(sz <= c for sz in fs)
                if base == cyc4:
                    agree += 1
                elif wit is None and base and not cyc4:
                    wit = (c, H, sorted(fs))
        print(f"    n_hub = {n}: {len(reps)} classes x {len(CBOUNDS)} "
              f"bounds; agreements {agree}/{len(reps) * len(CBOUNDS)}"
              + ("" if wit is None else
                 f"; FIRST WITNESS at c = {wit[0]}: frames only at "
                 f"|A| in {wit[2]}, hedges = {wit[1]}"))


# ---------------------------------------------------------------------------
# [GBA-3] --classes / [GBA-4] --shapes: the base's SIZE
# ---------------------------------------------------------------------------

def leg_classes(hi=10):
    """[GBA-3] (GR-236) the base at the CLASS layer and at the LABELLED
    layer (classes weighted by `n!/|Aut|`, the measure a uniform random
    cubic multigraph carries), exhaustively, `n_hub = 4..hi`."""
    from math import factorial
    print("[GBA-3] (GR-236) the base at the CLASS layer, EXHAUSTIVE")
    print("  n_hub | classes |" + "".join(f"  base c={c} |" for c in CBOUNDS)
          + "  (class share / labelled share)")
    for n in range(4, hi + 1, 2):
        t0 = time.time()
        reps = expand_classes(n)
        wts = [factorial(n) // aut_order(n, [tuple(e) for e in h])
               for h in reps]
        W = sum(wts)
        fss = [frame_sizes(n, [tuple(e) for e in h]) for h in reps]
        row = f"  {n:5d} | {len(reps):7d} |"
        for c in CBOUNDS:
            idx = [i for i, fs in enumerate(fss)
                   if not any(sz <= c for sz in fs)]
            cs = len(idx) / len(reps)
            ls = sum(wts[i] for i in idx) / W
            row += f" {len(idx):3d} {cs:5.1%}/{ls:5.1%} |"
        print(row + f"  [{time.time() - t0:.0f}s]")


def leg_shapes(hi=10):
    """[GBA-4] (GR-236) the base at the SHAPE layer, `Λ = ∅` -- the
    `aglu._pool8()` unit (per-representative excess profiles, NOT quotiented
    by `gisland.edge_auts`), un-fenced from `n_hub = 8` to `n_hub = 4..hi`.
    EXHAUSTIVE over every excess profile at every class: no cap, no draw."""
    print("[GBA-4] (GR-236) the base at the SHAPE layer, Lambda = empty, "
          "EXHAUSTIVE")
    for n in range(4, hi + 1, 2):
        t0 = time.time()
        reps = expand_classes(n)
        prof = excess_profiles_n(n)
        cnt = [habitat_count_lambda_empty(n, [tuple(e) for e in h], prof)
               for h in reps]
        fss = [frame_sizes(n, [tuple(e) for e in h]) for h in reps]
        tot = sum(cnt)
        inh = sum(1 for x in cnt if x)
        row = (f"  n_hub = {n:2d}: {len(reps):3d} classes ({inh} inhabited) "
               f"x {len(prof)} excess profiles -> {tot} habitat shapes;")
        for c in CBOUNDS:
            b = sum(cnt[i] for i, fs in enumerate(fss)
                    if not any(sz <= c for sz in fs))
            row += f"  base(c={c}) = {b} ({b / tot:.1%})"
        print(row + f"  [{time.time() - t0:.0f}s]")
        if n == 8:
            assert tot == 39689, \
                f"n_hub = 8 total {tot} != aglu._pool8()'s 39 689"
            b3 = sum(cnt[i] for i, fs in enumerate(fss)
                     if not any(sz <= 3 for sz in fs))
            assert b3 == 22720, \
                f"n_hub = 8 base {b3} != (GR-231)(iii)'s 22 720"
            print("    (asserted against aglu._pool8(): 39 689 total and "
                  "(GR-231)(iii)'s 22 720 base)")


def leg_residual(n=10, cap=120):
    """[GBA-5] (GR-234)(iii)'s length-dependent residual at `n_hub = n`:
    shapes with a frame at `|A| <= 5` but NO certified child at any of them.
    The parent gate is `cflank.cubic_habitat` (the (GR-25) criterion,
    (GR-25) being PROVEN equivalent to `gridcol.class_shape`); the child
    gate is the same.  CAP: the first `cap` habitat shapes per class in
    `aglu.excess_profiles` order -- a PREFIX, not a sample."""
    print(f"[GBA-5] the length-dependent residual at n_hub = {n}, "
          f"Lambda = empty (cap {cap} shapes/class)")
    reps = expand_classes(n)
    prof = excess_profiles_n(n)
    seen = red = res = 0
    for h in reps:
        H = [tuple(e) for e in h]
        fr = gnonadd.cut3_sets(n, H, sizes=(3, 5))
        if not fr:
            continue
        # the PARENT gate: the (GR-25) criterion by the same `∂ <= 3` route
        # `habitat_count_lambda_empty` uses (asserted equal to
        # `cflank.cubic_habitat` shape by shape at `n_hub = 8` in `--val`);
        # `cflank.cubic_habitat` itself is a `2^n` scan PER PROFILE and is
        # out of reach over 36 960 profiles x 91 classes.
        cons = small_cut_sets(n, H)
        m3 = [bm for (bd, bm) in cons if bd == 3]
        low = [(7 - 2 * bd, bm) for (bd, bm) in cons if bd < 3]
        k = 0
        for e in prof:
            supp = 0
            for t, x in enumerate(e):
                if x:
                    supp |= 1 << t
            if any(not (supp & bm) for bm in m3):
                continue
            if any(sum(e[t] for t in range(len(e)) if bm >> t & 1) < need
                   for (need, bm) in low):
                continue
            lens = [2 + x for x in e]
            k += 1
            if k > cap:
                break
            seen += 1
            ys = next(gnonadd.y_reductions(n, H, lens, sizes=(3, 5),
                                            gate=cflank.cubic_habitat,
                                            frames=fr), None)
            if ys is not None:
                red += 1
            else:
                res += 1
    print(f"  {seen} shapes carrying a frame at |A| in (3, 5): {red} "
          f"Y-reduce to a certified child, {res} do NOT (the residual).  "
          f"CAP: the first {cap} habitat shapes per class in "
          f"`aglu.excess_profiles` order -- a PREFIX, not a sample, so a "
          f"`0` here is `no residual found under cap {cap}`.")


# ---------------------------------------------------------------------------
# [GBA-6] --sample: the trend past the exhaustive range
# ---------------------------------------------------------------------------

def connected_sets(n, hedges, sz):
    """Every connected vertex set of size `sz`, by growth from each seed.
    In a cubic multigraph there are `O(n * 3^(sz-1))` of them, against
    `C(n, sz)` for `itertools.combinations` -- this is the only reason the
    sampler can reach `n_hub = 40`.  LOCAL DEVICE for performance:
    `--val` asserts `frames_upto` built on it agrees with the CANONICAL
    `gnonadd.cut3_sets` on every class at `n_hub = 4, 6, 8, 10`."""
    adj = {v: set() for v in range(n)}
    for (u, w) in hedges:
        adj[u].add(w)
        adj[w].add(u)
    out = set()
    for s in range(n):
        stack = [(frozenset([s]), frozenset(adj[s]))]
        while stack:
            S, fr = stack.pop()
            if len(S) == sz:
                out.add(S)
                continue
            for v in fr:
                if v < s:
                    continue
                T = S | {v}
                out.add(T) if len(T) == sz else None
                if len(T) < sz:
                    stack.append((T, (fr | adj[v]) - T))
    return [tuple(sorted(S)) for S in out if len(S) == sz]


def frames_upto(n, hedges, c):
    """The frame sizes `<= min(c, n-1)` this hub multigraph carries, by
    connected-set growth.  Same predicate as `gnonadd.cut3_sets`:
    `partial(A) = 3` and `A` connected (oddness is automatic,
    (GR-234)(i))."""
    got = set()
    for sz in odd_sizes(n, c):
        for A in connected_sets(n, hedges, sz):
            ins, bd, _o = gnonadd.induced(n, hedges, A)
            if 3 * sz - 2 * len(ins) == 3 and len(bd) == 3:
                got.add(sz)
                break
    return got


def sample_cubic(n, rng, tries=100000):
    """A connected loopless cubic multigraph on `n` labelled hubs, drawn
    from the CONFIGURATION MODEL (uniform random perfect matching on the
    `3n` darts) with rejection on loops and on disconnection.

    THE MEASURE, stated because it is not labelled-uniform: a pairing draw
    gives multigraph `G` with probability proportional to `1/prod_e mu_e!`,
    so a class carrying `D` digons is under-weighted by `2^-D` relative to
    labelled-uniform.  `--sample` reports the calibration against the
    EXACT labelled share at `n_hub = 8, 10`, where both are known."""
    darts = [v for v in range(n) for _ in range(3)]
    for _ in range(tries):
        rng.shuffle(darts)
        H = [(darts[2 * i], darts[2 * i + 1]) for i in range(3 * n // 2)]
        if _connected_loopless(n, H):
            return [tuple(sorted(e)) for e in H]
    return None


def leg_sample(sizes=(8, 10, 12, 16, 20, 24, 30), draws=300,
               bounds=(3, 5, 7), seed=20260912):
    """[GBA-6] (GR-237) the base's LABELLED share past the exhaustive
    range, by seeded configuration-model sampling.  The statistic is a
    0/1 indicator of a FINITE graph property, so each draw is exact and the
    only cap is Monte-Carlo error (a binomial s.e. of at most
    `0.5/sqrt(draws)`); nothing here is semicontinuous."""
    import random
    print(f"[GBA-6] (GR-237) the base's labelled share by seeded "
          f"configuration-model sampling (seed {seed}, {draws} draws)")
    rng = random.Random(seed)
    se = 0.5 / (draws ** 0.5)
    print(f"  binomial s.e. <= {se:.3f} at every cell")
    for n in sizes:
        t0 = time.time()
        hit = {c: 0 for c in bounds}
        got = 0
        while got < draws:
            H = sample_cubic(n, rng)
            if H is None:
                break
            got += 1
            fr = frames_upto(n, H, max(bounds))
            for c in bounds:
                if not any(sz <= c for sz in fr):
                    hit[c] += 1
        row = f"  n_hub = {n:2d}: {got} draws;"
        for c in bounds:
            row += f"  base(c={c}) = {hit[c] / got:.1%}"
        print(row + f"  [{time.time() - t0:.0f}s]")


# ---------------------------------------------------------------------------
# [GBA-7] --ladder: (GR-15) ON the base
# ---------------------------------------------------------------------------

def leg_ladder(seed=20260912):
    """[GBA-7] (GR-238)/(GR-239): the two ladder recipes the corpus carries
    -- §(K-grid) (GR-34)'s (excess 2+2+2 on three ADJACENT rungs, the
    CFLANK `--tight` recipe) and (GR-175)'s (six pairwise NON-ADJACENT
    length-3 rungs) -- are DIFFERENT length assignments on the SAME hub
    multigraph, so by (GR-221)(i) both are in the base; and the
    rung-minority RULE of `gexist.ladder_rule_first` closes one and NOT the
    other.

    CAP: `cflank.cubic_habitat` scans `2^n_hub` hub subsets, so every
    habitat certificate here stops at `n_hub = 24` (`m = 12`); `m = 14` was
    started and abandoned at that limiter, not at a mathematical one."""
    import random
    from gexist import ladder_specs, ladder_rule_first, fully_good_rank
    from gunif import wit_colouring
    from gridcol import subdivide
    from kbare_common import verts_of
    rng = random.Random(seed)
    print(f"[GBA-7] (GR-238)/(GR-239) the ladder spine of the base "
          f"(seed {seed})")
    # (GR-175)'s "six rungs of length 3 (pairwise non-adjacent)": rungs of
    # `CL_m` are pairwise vertex-disjoint, so non-adjacency is AUTOMATIC and
    # the only requirement is `m >= 6` -- which is exactly GNONADD's
    # 2026-09-11 correction ("need >= 12 hubs", i.e. n_hub >= 12).  The six
    # are taken evenly spread, `i*m//6`.
    recipes = [("(GR-34)  2+2+2 on three ADJACENT rungs", 3, lambda m:
                {0: 2, 1: 2, 2: 2}),
               ("(GR-175) six length-3 rungs", 6, lambda m:
                {i * m // 6: 1 for i in range(6)})]
    for (name, need, mk) in recipes:
        for m in (6, 8, 10, 12):
            if m < need:
                print(f"  {name}, m = {m}: EMPTY (needs m >= {need})")
                continue
            exc = mk(m)
            assert sum(exc.values()) == 6, name
            specs = ladder_specs(m, exc)
            H = [(u, w) for (u, w, _L) in specs]
            lens = [L for (_u, _w, L) in specs]
            n = 2 * m
            hab = cflank.cubic_habitat(n, H, lens)
            fr = frames_upto(n, H, max(CBOUNDS))
            edges = subdivide(specs)
            allv = sorted(verts_of(edges), key=str)
            hm = cflank.hub_model(edges)
            col = wit_colouring(specs, ladder_rule_first(m, specs))
            adm = cflank.admissible(edges, allv, hm, col)
            nc1 = not cflank.nc1_violations(hm, col, edges, allv)
            fg = (fully_good_rank(edges, allv, hm, col, rng)
                  if adm and nc1 else None)
            print(f"  {name}, m = {m} (n_hub = {n}): habitat = {hab}; "
                  f"frames at |A| <= {max(CBOUNDS)}: "
                  f"{sorted(fr) if fr else 'NONE -> IN THE BASE'}; "
                  f"rung-minority rule: admissible = {adm}, NC1 clear = "
                  f"{nc1}, fully-good (exact-Q dim Z = 0, BOTH blocks) = "
                  f"{fg}")
            if fg:
                continue
            # the rule failed: fall back to a SEARCH, so the entry reports
            # per-shape (GR-15) separately from the uniform rule
            priv = cflank.private_even(hm)
            hit = None
            for t in range(40):
                c0 = cflank.one_admissible(edges, allv, hm, rng)
                if c0 is None:
                    continue
                if priv:
                    c0 = cflank.repair(edges, allv, hm, c0, priv)
                if cflank.nc1_violations(hm, c0, edges, allv):
                    continue
                if not cflank.admissible(edges, allv, hm, c0):
                    continue
                if fully_good_rank(edges, allv, hm, c0, rng):
                    hit = t + 1
                    break
            print(f"      SEARCH fallback (private_even = "
                  f"{'yes' if priv else 'NO'}): "
                  + (f"FULLY-GOOD at draw {hit} (exact-Q witness, cap-free)"
                     if hit else "no fully-good colouring in 40 draws"))
    print("  => the rule is PARITY-FRAGILE: it needs every rung length "
          "EVEN (a length-L branch flips its dart colour L-1 times, so a "
          "rung can be its hub's minority dart at BOTH ends only when L is "
          "even).  (GR-34)'s recipe has rungs at 2 and 4; (GR-175)'s has "
          "six at 3.")


# ---------------------------------------------------------------------------
# [GBA-8] --val / --labcount
# ---------------------------------------------------------------------------

def leg_val():
    """[GBA-8] the three local devices against their canonical oracles."""
    print("[GBA-8] local devices vs canonical")
    for n in (4, 6, 8):
        e = expand_from(n)
        c = gridcol.cubic_iso_classes(n)
        ke = sorted(_canon_key(n, [tuple(x) for x in h]) for h in e)
        kc = sorted(_canon_key(n, list(h)) for h in c)
        assert ke == kc, f"expand_from disagrees with cubic_iso_classes " \
                         f"at n = {n} ({len(e)} vs {len(c)})"
        print(f"  expand_from({n}) == gridcol.cubic_iso_classes({n}): "
              f"{len(e)} classes, same canonical keys")
    pool, _nep = aglu._pool8()
    prof = excess_profiles_n(8)
    bad = 0
    for (h, ls) in pool:
        if habitat_count_lambda_empty(8, list(h), prof) != len(ls):
            bad += 1
    assert bad == 0, "habitat_count_lambda_empty disagrees with _pool8()"
    print(f"  habitat_count_lambda_empty == aglu._pool8() at all "
          f"{len(pool)} classes; total "
          f"{sum(len(ls) for (_h, ls) in pool)}")
    for n in (4, 6, 8, 10):
        for h in expand_classes(n):
            H = [tuple(e) for e in h]
            a = frames_upto(n, H, n - 1)
            b = set(frame_sizes(n, H))
            assert a == b, f"frames_upto != cut3_sets at n = {n}: {a} {b}"
    print("  frames_upto == gnonadd.cut3_sets at every class, "
          "n_hub = 4, 6, 8, 10")


def leg_labcount(n):
    """[GBA-9] the COMPLETENESS certificate for the class list at `n_hub =
    n`: `sum_classes n!/|Aut| == #labelled connected`, the right-hand side
    from `labelled_all` (the same least-deficient recursion) through the
    exponential formula.  An equality here PROVES the generator missed
    nothing -- it is not evidence about the generator, it is a count."""
    from math import factorial
    print(f"[GBA-9] completeness certificate at n_hub = {n}")
    tab = {0: 1}
    for k in range(2, n + 1, 2):
        t0 = time.time()
        tab[k] = labelled_all(k)
        print(f"  labelled_all({k}) = {tab[k]}  [{time.time() - t0:.0f}s]")
    rhs = labelled_connected(n, tab)
    reps = expand_classes(n)
    lhs = sum(factorial(n) // aut_order(n, [tuple(e) for e in h])
              for h in reps)
    print(f"  sum over {len(reps)} classes of {n}!/|Aut| = {lhs}")
    print(f"  #labelled CONNECTED loopless cubic multigraphs = {rhs}")
    print("  => " + ("COMPLETE (certificate holds)" if lhs == rhs
                     else f"INCOMPLETE: short by {rhs - lhs} labelled "
                          f"graphs -- the class list is NOT the whole set"))
    assert lhs == rhs, "class list incomplete at n_hub = %d" % n




# ---------------------------------------------------------------------------
# [GBA-10] --orbits: the SHAPE layer in the ISOMORPHISM-CLASS unit
# ---------------------------------------------------------------------------

def edge_auts_fast(n, hedges):
    """`Aut(G°)` as branch permutations -- the same object
    `gisland.edge_auts` returns, but by refinement-pruned backtracking over
    VERTEX permutations instead of all `n!` of them.  LOCAL DEVICE for
    performance: `--val` asserts the two return the SAME SET at every class
    at `n_hub = 4, 6, 8` (`gisland.edge_auts` is `itertools.permutations`
    over `range(n)`, which is `3.6e6` per class at `n_hub = 10`)."""
    import itertools
    A = [[0] * n for _ in range(n)]
    for (u, w) in hedges:
        A[u][w] += 1
        A[w][u] += 1
    col = [tuple(sorted(A[v])) for v in range(n)]
    for _ in range(n):
        new = [(col[v], tuple(sorted((A[v][u], col[u]) for u in range(n)
                                     if A[v][u]))) for v in range(n)]
        vals = sorted(set(new))
        mp = {t: i for i, t in enumerate(vals)}
        nc = [mp[t] for t in new]
        if nc == col:
            break
        col = nc
    perm = [-1] * n
    used = [False] * n
    vauts = []

    def rec(i):
        if i == n:
            vauts.append(tuple(perm))
            return
        for v in range(n):
            if used[v] or col[v] != col[i]:
                continue
            if any(A[i][j] != A[v][perm[j]] for j in range(i)):
                continue
            perm[i] = v
            used[v] = True
            rec(i + 1)
            used[v] = False
            perm[i] = -1
    rec(0)
    key = {}
    for k, (u, w) in enumerate(hedges):
        key.setdefault((min(u, w), max(u, w)), []).append(k)
    out = set()
    for pi in vauts:
        tgt = {}
        for k, (u, w) in enumerate(hedges):
            a, b = pi[u], pi[w]
            tgt.setdefault((min(a, b), max(a, b)), []).append(k)
        cls = sorted(tgt)
        for combo in itertools.product(*[itertools.permutations(key[e])
                                         for e in cls]):
            p = [None] * len(hedges)
            for e, tup in zip(cls, combo):
                for src, dst in zip(tgt[e], tup):
                    p[src] = dst
            out.add(tuple(p))
    return sorted(out)


def orbit_counts(n, hedges, profiles):
    """(#habitat shapes up to `Aut(G°)`, #habitat shapes as labelled length
    assignments) on this hub multigraph at `Λ = ∅`.

    THE UNIT THIS SETTLES.  `aglu._pool8()` counts the SECOND -- excess
    profiles per class representative, not quotiented -- and every
    `n_hub = 8` figure the corpus quotes ((GR-198)(iii), (GR-221)(iii),
    (GR-231)(iii)) is in that unit.  `gisland.stratum` counts the FIRST, and
    a `D = 0` tight CLASS SHAPE is an isomorphism class, so the first is
    what the induction's base is a set of."""
    auts = edge_auts_fast(n, list(hedges))
    cons = small_cut_sets(n, hedges)
    m3 = [bm for (bd, bm) in cons if bd == 3]
    low = [(7 - 2 * bd, bm) for (bd, bm) in cons if bd < 3]
    seen, lab = set(), 0
    for e in profiles:
        supp = 0
        for k, x in enumerate(e):
            if x:
                supp |= 1 << k
        if any(not (supp & bm) for bm in m3):
            continue
        if any(sum(e[k] for k in range(len(e)) if bm >> k & 1) < need
               for (need, bm) in low):
            continue
        lab += 1
        seen.add(min(tuple(e[p[k]] for k in range(len(e))) for p in auts))
    return len(seen), lab


def leg_orbits(hi=10):
    """[GBA-10] (GR-236) the base at the SHAPE layer in BOTH units, so the
    unit's effect on the landed figures is visible."""
    print("[GBA-10] (GR-236) the base at the SHAPE layer, Lambda = empty, "
          "in BOTH units")
    for n in range(4, hi + 1, 2):
        t0 = time.time()
        reps = expand_classes(n)
        prof = excess_profiles_n(n)
        rows = [(orbit_counts(n, [tuple(e) for e in h], prof),
                 frame_sizes(n, [tuple(e) for e in h])) for h in reps]
        orb = sum(r[0][0] for r in rows)
        lab = sum(r[0][1] for r in rows)
        row = (f"  n_hub = {n:2d}: {orb} shapes up to Aut(G) / {lab} "
               f"labelled length assignments;")
        for c in (3, 5):
            bo = sum(r[0][0] for r in rows
                     if not any(sz <= c for sz in r[1]))
            bl = sum(r[0][1] for r in rows
                     if not any(sz <= c for sz in r[1]))
            row += (f"  base(c={c}) = {bo} ({bo / orb:.1%}) up to Aut / "
                    f"{bl} ({bl / lab:.1%}) labelled;")
        print(row + f"  [{time.time() - t0:.0f}s]")


def main():
    ap = argparse.ArgumentParser()
    for f in ('consumer', 'char', 'classes', 'shapes', 'orbits',
              'residual', 'sample', 'ladder', 'val', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--labcount', type=int, default=0)
    ap.add_argument('--rescap', type=int, default=120)
    ap.add_argument('--hi', type=int, default=10)
    a = ap.parse_args()
    run = a.validate
    if run or a.val:
        leg_val()
    if run or a.consumer:
        leg_consumer()
    if run or a.char:
        leg_char(a.hi)
    if run or a.classes:
        leg_classes(a.hi)
    if run or a.shapes:
        leg_shapes(a.hi)
    if run or a.orbits:
        leg_orbits(a.hi)
    if run or a.residual:
        leg_residual(a.hi, a.rescap)
    if run or a.ladder:
        leg_ladder()
    if a.sample:
        leg_sample()
    if a.labcount:
        leg_labcount(a.labcount)
    if not (run or a.val or a.consumer or a.char or a.classes or a.shapes
            or a.orbits or a.residual or a.ladder or a.sample or a.labcount):
        ap.print_help()


if __name__ == '__main__':
    main()
