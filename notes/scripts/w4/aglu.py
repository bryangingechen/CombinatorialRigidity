"""§(K-grid) direction AGLU (2026-08-19) driver -- ledger attack (c): is the
AA-GLUE configuration REALIZABLE at n_hub >= 8?  It is the only surviving case
of the (GR-38) intersection kill: (GR-38)(iii) says two same-block binding
chunks that cross have a binding union UNLESS
`slack + defect(S n S') <= 1`, which forces the AA-glue configuration -- and
over the complete n_hub <= 6 stratum that configuration has 0 instances
(0 / 53 740 binding instances over 4920 shapes: binding is provably LAMINAR
there, so the kill is vacuously strong exactly where it is checked).

A `w4/` leaf beside `gorient.py`, importing `cflank.py` / `gcap.py` /
`gexist.py` / `gorient.py` / `gunif.py` / `gridcol.py` / `closure.py`
READ-ONLY (README §2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --pool    # the n_hub = 8 stratum, counted exactly
    PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --pin     # (GR-73)/(GR-74): the colouring-free structure + the n_hub = 8 PINNING, exhaustive
    PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --kill8   # (GR-75)/(GR-76): the exhaustive n_hub = 8 scan (every shape, every admissible colouring, every crossing pair)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --kill8 --slice i/k   # the same scan, graph-sliced (F15 budget)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --adv     # (GR-77): the falsification controls -- the detector must FIRE somewhere
    PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --val      # every fast device cross-certified against the canonical layer

Argument state: session draft `notes/Pencil-draft-AGLU.md` (to be merged into
`notes/Pencil-informal.md` §(K-grid) as Steps G92+; labels (GR-73)-(GR-78) per
the 2026-08-19 AGLU reservation in `notes/Pencil-labels.md`).

THE DERIVED STRUCTURE THE MODES REST ON (proofs in the draft; ASSERTED here,
never trusted).  Throughout `Lambda = empty`, `D = 0`: `G°` cubic loopless,
lengths in [2, 5] ((SD-6)), total excess 6 ((GR-21)); chunk / interior /
corner / exit / defect exactly as in `gexist.py`'s header; binding in A iff
`defect_A(S) <= 2`.  `T := S n S'`, `R := S - S'`, `R' := S' - S`.

(GR-73)  THE SLACK-0 DEGREE LEMMA (colouring-free).  `slack(S, S') = 0` iff
         `S, S'` share no X-hub (a hub of S-degree 2 = S'-degree 2 with
         DIFFERENT pairs) -- immediate from (GR-38)(i), whose slack is
         `>= #X-hubs`.  And then EVERY hub of `T` has `deg_T in {2, 3}`:
         `deg_T(v) = 1` puts one dart in `T`, one in `R` and one in `R'`,
         making `v` an X-hub; `deg_T(v) = 0` needs 4 darts at a cubic hub.
         So at slack 0 the intersection is itself a {2,3}-degree subgraph.

(GR-74)  THE n_hub = 8 PINNING.  Add `defect_A(T) = 0`.  Then (a) the
         deg-2 hubs of `T` are pairwise NON-ADJACENT in `T` (a T-branch
         joining two of them has an A-dart at both ends, hence is odd and
         A-majority, hence charges `defect_A(T) >= 1` by (GR-36)(i)/(ii));
         (b) the attachment lemma (GR-38)(ii) gives `>= 2` attachment hubs
         per component of `R'` (all interiors of `S`, all corners of `S'`
         at slack 0) and dually for `R`, and the two families are disjoint
         (S-degree 2 vs 3), so `n_2(T) >= 4`; (c) counting the
         deg-2-to-deg-3 T-edges, `2 n_2 <= 3 n_3`, and `2 n_2 + 3 n_3`
         even forces `n_3` even, so `n_2 = 4, n_3 = 4` at `n_hub = 8` --
         `T` covers ALL 8 hubs with exactly 10 branches, `R` and `R'` are
         SINGLE branches joining the two deg-2 pairs, and
         `S u S' = E(G°)`.

(GR-75)  THE KILL AT n_hub = 8 (the headline).  The (GR-74) template is
         COLOURING-INCONSISTENT.  At `defect_A(T) = 0` every T-branch has
         `l in {2, 3}` with the odd ones B-majority, and each of the four
         deg-2 T-hubs is AA, so its free dart is its minority dart and
         carries B; hence `R` and `R'` have B at BOTH ends, i.e. are odd
         B-majority.  So
             defect_A(E(G°)) = w45 + #(A-maj odd) = [l_R = 5] + [l_R' = 5]
                             <= 2,
         while balance forces `defect_A(E(G°)) = 3` identically
         ((GR-32)(iii)).  Contradiction: the AA-glue configuration is NOT
         realizable at `n_hub = 8`.  This is a PROOF, not a capped search,
         and `--kill8` re-derives it by exhaustion.

(GR-76)  THE W-CHARGE (the general-n residual, stated because the (GR-75)
         argument does NOT generalize by itself).  In ANY AA-glue
         configuration, split the non-T branches into `F2` (both ends at
         free darts of deg-2 T-hubs), `F1` (one such end) and `W` (neither).
         Global balance gives `Sum_{beta not in T} c(beta) = 3` with
         `c = [l >= 4] + [odd and A-maj]`, and the excess law gives
         `Sum e = 6 - q_T`, `e = l - 2`, `q_T = #(l = 3 in T)`.  Per branch
         `e - c >= c'` with `c' = c + 1` on F2, `c` on F1, `c - 1` on W
         (the six length/majority cases, tabulated in `--val`), whence
             |W| >= |F2| + q_T.
         At `n_hub = 8` the pinning gives `W = empty` and `|F2| = 2`, which
         is (GR-75) again; at larger `n` the charge is what a successor must
         beat, and it says an AA-glue witness needs branches entirely off
         the T-frame.

WHAT EACH MODE TESTS, one sentence each (F11 -- and here doubly binding: the
direction's claims are EXHAUSTIVENESS claims, which are their own claim class;
the per-sentence table is in the draft's Verification section).

--pool   the n_hub = 8 pool is counted exactly: the hub-multigraph iso
         classes from the local complete generator (cross-certified against
         `gridcol.multigraphs` at n = 2, 4, 6 in --val) times every excess
         profile, gated by `cflank.cubic_habitat` -- the landed (GR-25) cut
         criterion, used as the D = 0 membership oracle and not replaced.

--pin    (GR-73) and (GR-74) asserted at EVERY crossing chunk pair of EVERY
         n_hub = 8 hub-multigraph class (and at n <= 6 as a control): the
         attachment lemma (GR-38)(ii) re-asserted through
         `gorient.attachment_check`, the X-hub count, the slack-0 degree
         lemma, and -- at every pair with 0 X-hubs and J-free intersection
         -- the four pinning clauses.  Colouring-free and length-free, so
         NO cap: the claim is about a 20-graph finite object.

--kill8  the exhaustive n_hub = 8 scan: every habitat shape, every
         admissible colouring, every same-block binding chunk pair that
         crosses -- the slack identity (GR-38)(i) asserted exactly, the
         AA-glue count (slack = 0 and defect(T) = 0), the full kill residual
         (slack + defect(T) <= 1), the kill failures (union proper and not
         binding), and the laminarity verdict.  NO CAP is taken anywhere:
         the pool IS the complete stratum and every colouring of every shape
         is visited.

--adv    the falsification controls, because "0 instances" is worthless
         without a detector that fires: the K4 crossing pair with slack 0
         and its J-charged intersection (the combinatorial detector fires at
         n_hub = 4), a slack-0 crossing pair at n_hub = 8 (it fires there
         too), and (GR-30)'s W3M -- the landed MINIMAL n_hub = 8 witness --
         re-measured through this driver's own devices, binding chunk and
         all (the binding detector fires at n_hub = 8).

--val    every fast device asserted equal to the canonical one it replaces:
         the graph generator vs `gridcol.multigraphs`, the chunk enumerator
         vs `gcap.two_ec_subsets(kmin=1)`, the defect vs
         `gexist.defect_direct`, the admissibility vs `cflank.admissible`,
         the slack vs `gorient.pair_slack`, the (GR-36) bound vs
         `gorient.jdata`; plus the (GR-76) case table and a reproduction of
         (GR-38)'s own n <= 6 headline through this driver's devices.

Exact throughout (integers only; nothing here samples a placement, so
`repin.star_generic` gates nothing -- §(K-clos) (AC-9)'s discipline, as for
`gorient.py` / `cflank.py`).  Rngs seeded per mode, seeds printed; every
printed collection is sorted.  Wall-clock `[Ns]` annotations are inherently
non-deterministic; every other byte is seed-stable.
"""
import argparse
import os
import random
import sys
import time
from itertools import combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from closure import colourings                                         # noqa: E402
from gridcol import multigraphs, subdivide                             # noqa: E402
from cflank import (admissible, cubic_habitat, excess_profiles,         # noqa: E402
                    hub_model)
from gcap import branch_stats, two_ec_subsets                          # noqa: E402
from gexist import defect_direct, incidence                            # noqa: E402
from gorient import attachment_check, jdata, pair_slack                 # noqa: E402
from gunif import WITNESSES, wit_colouring                             # noqa: E402

A_SEED = 20260819

_ISO_CACHE = {}
_POOL8 = [None]


# ----------------------------------------------------- local devices --------
#
# All new.  Three of them replace a canonical function for PERFORMANCE only
# and are asserted equal to it in --val (README §2 rule 3 + §4 convention 4);
# the two that have no canonical counterpart are the graph generator (whose
# rationale is in its docstring) and the (GR-76) charge table.


def cubic_iso_classes(n):
    """Every connected loopless cubic multigraph on `n` hubs, ONE
    representative per isomorphism class.

    Local device, and the rationale is arithmetic: `gridcol.multigraphs(n, m)`
    walks multiplicity vectors over all `C(n, 2)` pairs by composition, which
    at `n = 8` is `C(39, 27) ~ 8e9` recursion branches -- out of reach.  This
    one recurses on the LEAST-deficient hub (all of whose remaining darts must
    go to higher-indexed hubs), so it enumerates each labelled graph exactly
    once, and canonicalizes by a pruned minimum-adjacency-matrix search
    refined by a Weisfeiler--Leman colouring.  `--val` asserts it returns the
    same CLASS COUNT as `gridcol.multigraphs` at `n = 2, 4, 6` (1 / 2 / 6) and
    that every class it emits is habitat-gate-consistent with that layer."""
    labelled = []
    rem = [3] * n
    edges = []

    def rec():
        v = next((i for i in range(n) if rem[i] > 0), None)
        if v is None:
            labelled.append(tuple(edges))
            return
        cand = [u for u in range(v + 1, n) if rem[u] > 0]
        for combo in combinations_with_replacement(cand, rem[v]):
            cnt = {}
            for u in combo:
                cnt[u] = cnt.get(u, 0) + 1
            if any(rem[u] < c for u, c in cnt.items()):
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
    reps = {}
    for es in labelled:
        A = [[0] * n for _ in range(n)]
        for (u, w) in es:
            A[u][w] += 1
            A[w][u] += 1
        seen, st = {0}, [0]
        while st:
            x = st.pop()
            for y in range(n):
                if A[x][y] and y not in seen:
                    seen.add(y)
                    st.append(y)
        if len(seen) != n:
            continue
        key = _canon(n, A)
        if key not in reps:
            reps[key] = es
    out = [reps[k] for k in sorted(reps)]
    _ISO_CACHE[n] = out
    return out


def _canon(n, A):
    """Lexicographically minimal flattened adjacency matrix over all vertex
    permutations, by DFS with prefix pruning."""
    col = [tuple(sorted(A[v])) for v in range(n)]
    for _ in range(n):
        new = [(col[v], tuple(sorted((A[v][u], col[u]) for u in range(n)
                                     if A[v][u]))) for v in range(n)]
        vals = sorted(set(new))
        m = {x: i for i, x in enumerate(vals)}
        nc = [m[x] for x in new]
        if nc == col:
            break
        col = nc
    best = [None]
    perm = [-1] * n
    used = [False] * n
    order = sorted(range(n), key=lambda v: (col[v], v))

    def rec(i, part):
        if i == n:
            if best[0] is None or part < best[0]:
                best[0] = part
            return
        for v in order:
            if used[v]:
                continue
            nxt = part + tuple(A[v][perm[j]] for j in range(i))
            if best[0] is not None and nxt > best[0][:len(nxt)]:
                continue
            used[v] = True
            perm[i] = v
            rec(i + 1, nxt)
            used[v] = False
            perm[i] = -1
    rec(0, ())
    return best[0]


def chunks_of(n, ends):
    """Every chunk of the hub multigraph `ends` as (branch-mask, branch
    tuple, S-degree map): connected, bridgeless, all S-degrees in {2, 3}.
    Includes `k = 1` circuits and the whole graph, exactly as
    `gorient.prep_shape`'s `two_ec_subsets(hm, kmin=1)` does.

    PERFORMANCE device: the canonical `gcap.two_ec_subsets` needs the
    subdivision-level `hub_model`, so calling it per shape re-derives an
    object that depends only on the hub multigraph.  This one is keyed on the
    multigraph, so it is computed ONCE per graph class and shared by all
    11 440 length assignments.  `--val` asserts the two agree, branch tuple
    for branch tuple, at every n <= 6 pool shape and at seeded n = 8 shapes."""
    M = len(ends)
    low = sum(1 << (3 * i) for i in range(n))
    inc = [(1 << (3 * ends[k][0])) + (1 << (3 * ends[k][1])) for k in range(M)]
    ds = [0] * (1 << M)
    for mask in range(1, 1 << M):
        lb = mask & -mask
        ds[mask] = ds[mask ^ lb] + inc[lb.bit_length() - 1]
    out = []
    for mask in range(1, 1 << M):
        x = ds[mask]
        if x & ~(x >> 1) & ~(x >> 2) & low:      # some hub has S-degree 1
            continue
        ks = tuple(k for k in range(M) if mask >> k & 1)
        deg = {}
        for k in ks:
            for v in ends[k]:
                deg[v] = deg.get(v, 0) + 1
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
            continue
        bridge = False
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
                bridge = True
                break
        if bridge:
            continue
        out.append((mask, ks, deg))
    return out


def degmap(ends, ks):
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    return deg


def jfree(ends, ks, deg=None):
    """The length-free half of the (GR-36)(iii) charge:
    `Sum over J-components ceil(m_i / 2)`, `J` = the interior-interior
    branches of the set (interior = degree 2 in the set).  Valid on ANY
    branch set of a cubic host, not only chunks: J has max degree <= 2, a
    J-cycle is a whole component of the set, and the run count on a cycle of
    `m` edges is also `>= ceil(m/2)` (draft Step G92).  Adding `w45` gives
    `gorient.jdata`'s `bound`, asserted equal in --val."""
    if deg is None:
        deg = degmap(ends, ks)
    ints = {v for v, d in deg.items() if d == 2}
    jed = [k for k in ks if ends[k][0] in ints and ends[k][1] in ints]
    if not jed:
        return 0
    adj = {v: [] for v in ints}
    for k in jed:
        u, w = ends[k]
        adj[u].append((w, k))
        adj[w].append((u, k))
    seen, tot = set(), 0
    for v0 in sorted(ints):
        if v0 in seen or not adj[v0]:
            continue
        cv, ce, st = {v0}, set(), [v0]
        while st:
            v = st.pop()
            for (u, k) in adj[v]:
                ce.add(k)
                if u not in cv:
                    cv.add(u)
                    st.append(u)
        seen |= cv
        tot += (len(ce) + 1) // 2
    return tot


def xhubs(ends, ksa, dega, ksb, degb):
    """The X-hubs of a chunk pair: shared hubs of S-degree 2 in BOTH with
    different pairs.  `slack >= #X-hubs` and `slack = 0` iff there are none
    ((GR-38)(i) -- both pairs AA at one hub would be a monochromatic hub)."""
    out = []
    for v in sorted(set(dega) & set(degb)):
        if dega[v] == 2 and degb[v] == 2:
            pa = frozenset(k for k in ksa if v in ends[k])
            pb = frozenset(k for k in ksb if v in ends[k])
            if pa != pb:
                out.append(v)
    return out


def chunk_cache(ends, lens, mask, ks, deg):
    """Per-(shape, chunk) colouring-independent data for the fast defect:
    `w45`, the branch mask of the ODD branches, and the 24-bit dart-pair mask
    of every interior.  Dart id of branch `k` = `2k` at its u-end, `2k+1` at
    its w-end."""
    w45 = sum(1 for k in ks if lens[k] >= 4)
    oddm = 0
    for k in ks:
        if lens[k] % 2:
            oddm |= 1 << k
    prs = []
    for v, d in deg.items():
        if d != 2:
            continue
        m = 0
        for k in ks:
            u, w = ends[k]
            if u == v:
                m |= 1 << (2 * k)
            if w == v:
                m |= 1 << (2 * k + 1)
        prs.append(m)
    return (mask, ks, w45, oddm, tuple(prs), len(prs))


def dartmask(lens, b):
    """The 24-bit A-dart mask of the colouring bit vector `b` (bit `k` of `b`
    = the u-end dart of branch `k` is A).  A branch's two end darts are equal
    iff its length is odd (alternation)."""
    ad = 0
    for k, L in enumerate(lens):
        if b >> k & 1:
            ad |= 1 << (2 * k)
            if L % 2:
                ad |= 1 << (2 * k + 1)
        elif L % 2 == 0:
            ad |= 1 << (2 * k + 1)
    return ad


def fast_defects(cache, b, ad):
    """(defect_A, defect_B) of a cached chunk at colouring `b` -- the
    (GR-36)(i) charge form of (GR-28)(i):
    `defect_A = w45 + #(A-majority odd branches) + #(non-AA interiors)`.
    Asserted equal to `gexist.defect_direct` in --val."""
    _mask, _ks, w45, oddm, prs, z = cache
    pa = bin(b & oddm).count('1')
    nodd = bin(oddm).count('1')
    dA = dB = None
    if w45 + pa <= 2:
        naa = 0
        for m in prs:
            if (m & ad) != m:
                naa += 1
        dA = w45 + pa + naa
    if w45 + (nodd - pa) <= 2:
        nbb = 0
        for m in prs:
            if (m & ad) != 0:
                nbb += 1
        dB = w45 + (nodd - pa) + nbb
    return dA, dB


def set_defects(ends, lens, ks, b, ad):
    """(defect_A, defect_B) of an ARBITRARY branch set by the same charge
    form -- no chunk-ness, no early exit (used for `T`, `S u S'`)."""
    deg = degmap(ends, ks)
    dA = dB = 0
    for k in ks:
        L = lens[k]
        if L % 2:
            amaj = bool(b >> k & 1)
            dA += (L - 1) // 2 + (1 if amaj else 0) - 1
            dB += (L - 1) // 2 + (0 if amaj else 1) - 1
        else:
            dA += L // 2 - 1
            dB += L // 2 - 1
    for v, d in deg.items():
        if d != 2:
            continue
        m = 0
        for k in ks:
            u, w = ends[k]
            if u == v:
                m |= 1 << (2 * k)
            if w == v:
                m |= 1 << (2 * k + 1)
        if (m & ad) != m:
            dA += 1
        if (m & ad) != 0:
            dB += 1
    return dA, dB


def admissible_bits(n, ends, lens):
    """Every admissible colouring of the shape as a branch bit vector `b`
    (bit `k` = the u-end dart of branch `k` is A), with its 24-bit A-dart
    mask.

    At `Lambda = empty` admissibility is exactly *balanced + no
    monochromatic hub*: the two ruling-class forest conjuncts of
    `cflank.admissible` are AUTOMATIC there, because every branch has an
    interior subdivision vertex whose two edges alternate (so it has
    own-colour degree <= 1) and there are no hub-hub edges, so no
    own-colour cycle can exist.  And balance is exactly `#(A-majority odd
    branches) = n_odd / 2`, since an even branch splits its length evenly.
    PERFORMANCE device; `--val` asserts SET EQUALITY with
    `cflank.admissible` on the subdivision at every one of the 4920
    n <= 6 pool shapes and at seeded n = 8 shapes.

    Enumerated by DFS over the branches in a hub-closing order, pruning at
    each hub as soon as its three darts are assigned (the mono-hub ban) and
    on the running A-majority-odd count (balance)."""
    M = len(ends)
    oddk = [k for k in range(M) if lens[k] % 2]
    if len(oddk) % 2:
        return []
    need = len(oddk) // 2
    isodd = [lens[k] % 2 == 1 for k in range(M)]
    darts = {}
    for k, (u, w) in enumerate(ends):
        darts.setdefault(u, []).append((k, 0))
        darts.setdefault(w, []).append((k, 1))
    hubs = sorted(darts)
    # hub-closing branch order: greedily take the branch that completes the
    # most hubs next
    order, left, cnt = [], set(range(M)), {v: 0 for v in hubs}
    while left:
        best, bv = None, None
        for k in sorted(left):
            c = 0
            for v in ends[k]:
                if cnt[v] == 2:
                    c += 1
            if best is None or c > best:
                best, bv = c, k
        order.append(bv)
        left.discard(bv)
        for v in ends[bv]:
            cnt[v] += 1
    pos = {k: i for i, k in enumerate(order)}
    close = [[] for _ in range(M)]
    for v in hubs:
        last = max(darts[v], key=lambda kd: pos[kd[0]])[0]
        close[last].append(tuple(darts[v]))
    out = []
    dc = [0] * (2 * M)

    def rec(i, nA, ad):
        if i == M:
            if nA == need:
                out.append((_bits(order[:M], dc, ends), ad))
            return
        k = order[i]
        rem_odd = sum(1 for kk in order[i:] if isodd[kk])
        if nA > need or nA + rem_odd < need:
            return
        for bit in (1, 0):
            du = bit
            dw = bit if isodd[k] else 1 - bit
            dc[2 * k] = du
            dc[2 * k + 1] = dw
            nad = ad
            if du:
                nad |= 1 << (2 * k)
            if dw:
                nad |= 1 << (2 * k + 1)
            ok = True
            for tri in close[k]:
                t = sum(dc[2 * kk + e] for (kk, e) in tri)
                if t == 0 or t == 3:
                    ok = False
                    break
            if ok:
                rec(i + 1, nA + (1 if (isodd[k] and bit) else 0), nad)
            dc[2 * k] = dc[2 * k + 1] = 0
    rec(0, 0, 0)
    return out


def _bits(_order, dc, ends):
    b = 0
    for k in range(len(ends)):
        if dc[2 * k]:
            b |= 1 << k
    return b


def crossing_pairs(n, ends, chs):
    """Every crossing chunk pair of the multigraph: share a hub, neither
    contained in the other (exactly `gorient.leg_kill`'s pair predicate).
    Returns (i, j, X-hub list, T branch tuple, jfree(T), deg_T map)."""
    out = []
    for i in range(len(chs)):
        mi, ksi, di = chs[i]
        for j in range(i + 1, len(chs)):
            mj, ksj, dj = chs[j]
            if not (set(di) & set(dj)):
                continue
            inter = mi & mj
            if inter == mi or inter == mj:
                continue
            xs = xhubs(ends, ksi, di, ksj, dj)
            T = tuple(k for k in ksi if mj >> k & 1)
            dT = degmap(ends, T)
            out.append((i, j, xs, T, jfree(ends, T, dT), dT))
    return out


def _pool8():
    """(graph classes, per-class habitat length assignments) at n_hub = 8,
    the (GR-25) gate through `cflank.cubic_habitat`.  Memoized."""
    if _POOL8[0] is not None:
        return _POOL8[0]
    reps = cubic_iso_classes(8)
    ep = excess_profiles(12, 6)
    pool = []
    for hedges in reps:
        lens_ok = []
        for exc in ep:
            lens = [2 + e for e in exc]
            if cubic_habitat(8, list(hedges), lens):
                lens_ok.append(tuple(lens))
        pool.append((hedges, lens_ok))
    _POOL8[0] = (pool, len(ep))
    return _POOL8[0]


# ------------------------------------------------- [AGL-1] --pool -----------

def leg_pool():
    """[AGL-1] the n_hub = 8 stratum, counted exactly."""
    t0 = time.time()
    print("[AGL-1] the n_hub = 8 Lambda = empty D = 0 habitat stratum, "
          "counted exactly (no rng)")
    for n in (2, 4, 6):
        reps = cubic_iso_classes(n)
        can = multigraphs(n, 3 * n // 2)
        assert len(reps) == len(can), \
            f"generator disagrees with gridcol.multigraphs at n = {n}"
        print(f"  n_hub = {n}: {len(reps)} hub-multigraph classes "
              f"(== gridcol.multigraphs: {len(can)})")
    pool, nep = _pool8()
    tot = sum(len(ls) for (_h, ls) in pool)
    per = [len(ls) for (_h, ls) in pool]
    print(f"  n_hub = 8: {len(pool)} hub-multigraph classes x {nep} excess "
          f"profiles; habitat (GR-25)-gated shapes: {tot}")
    print(f"  per class: {per} -- {sum(1 for c in per if c)} of "
          f"{len(pool)} classes carry ANY habitat length assignment")
    assert tot == 39689, "the n_hub = 8 habitat count moved"
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------- [AGL-2] --pin: (GR-73)/(GR-74) -------

def leg_pin():
    """[AGL-2] the colouring-free structure: the slack-0 degree lemma and
    the n_hub = 8 pinning, exhaustive over every crossing chunk pair of
    every hub-multigraph class."""
    t0 = time.time()
    print(f"[AGL-2] (GR-73)/(GR-74) colouring-free, exhaustive over every "
          f"crossing chunk pair of every class (seed {A_SEED + 2})")
    rng = random.Random(A_SEED + 2)
    for n in (4, 6, 8):
        reps = cubic_iso_classes(n)
        npair = nx0 = nx1 = npin = 0
        xh = {}
        att_x = att_23 = 0
        deg1_at_x0 = 0
        tmpl = {}
        xcnt = {}
        prof = {}
        for hedges in reps:
            ends = list(hedges)
            chs = chunks_of(n, ends)
            allm = (1 << len(ends)) - 1
            cps = crossing_pairs(n, ends, chs)
            for (i, j, xs, T, jT, dT) in cps:
                npair += 1
                xh[len(xs)] = xh.get(len(xs), 0) + 1
                mi, ksi, di = chs[i]
                mj, ksj, dj = chs[j]
                assert T, "(GR-38)(ii): hub-sharing chunks with no shared " \
                    "branch in a cubic host"
                if not xs:
                    nx0 += 1
                    # (GR-73): every hub of T has deg_T in {2, 3}
                    assert all(d in (2, 3) for d in dT.values()), \
                        "(GR-73) slack-0 degree lemma REFUTED"
                    if any(d == 1 for d in dT.values()):
                        deg1_at_x0 += 1
                    # (GR-76)(iii): the F2 / F1 / W partition of the off-T
                    # branches and its three dart-count identities
                    n2 = sum(1 for d in dT.values() if d == 2)
                    ints = {v for v, d in dT.items() if d == 2}
                    X = [v for v in range(n) if v not in dT]
                    nF1 = nF2 = nW = 0
                    for k in range(len(ends)):
                        if k in T:
                            continue
                        h = sum(1 for v in ends[k] if v in ints)
                        if h == 2:
                            nF2 += 1
                        elif h == 1:
                            nF1 += 1
                        else:
                            nW += 1
                            assert all(v not in dT for v in ends[k]), \
                                "(GR-76): a W branch touches a T-hub"
                    assert nF1 + 2 * nF2 == n2, \
                        "(GR-76): n_2 != |F1| + 2|F2|"
                    assert nF1 + 2 * nW == 3 * len(X), \
                        "(GR-76): 3|X| != |F1| + 2|W|"
                    assert len(T) + nF1 + nF2 + nW == len(ends), \
                        "(GR-76): branch count identity broken"
                    if len(X) <= 1:
                        assert nW == 0, "(GR-76): W nonempty at |X| <= 1"
                        xcnt[len(X)] = xcnt.get(len(X), 0) + 1
                    prof[(len(X), n2, nF1, nF2, nW)] = \
                        prof.get((len(X), n2, nF1, nF2, nW), 0) + 1
                    if jT == 0:
                        npin += 1
                        n2 = sum(1 for d in dT.values() if d == 2)
                        n3 = sum(1 for d in dT.values() if d == 3)
                        key = (len(dT), n2, n3, len(T), len(ksi) - len(T),
                               len(ksj) - len(T), (mi | mj) == allm)
                        tmpl[key] = tmpl.get(key, 0) + 1
                        if n == 8:
                            # (GR-74) all four clauses
                            assert (len(dT), n2, n3, len(T)) == (8, 4, 4, 10), \
                                f"(GR-74) pinning REFUTED: T profile {key}"
                            assert len(ksi) - len(T) == 1 \
                                and len(ksj) - len(T) == 1, \
                                "(GR-74) R / R' not single branches"
                            assert (mi | mj) == allm, \
                                "(GR-74) S u S' is not the whole graph"
                elif len(xs) == 1:
                    nx1 += 1
                # the attachment lemma, through the LANDED checker, on a
                # seeded subsample (it needs the subdivision-level model)
                if rng.random() < (0.004 if n == 8 else 0.05):
                    lens = _some_habitat_lens(n, ends, rng)
                    if lens is None:
                        continue
                    specs = [(u, w, L) for (u, w), L in zip(ends, lens)]
                    hm = hub_model(subdivide(specs))
                    inc = incidence(hm)
                    for cls in attachment_check(hm, inc, list(ksi),
                                                list(ksj)):
                        for (_v, tt) in cls:
                            if tt == 'X':
                                att_x += 1
                            else:
                                att_23 += 1
                    for cls in attachment_check(hm, inc, list(ksj),
                                                list(ksi)):
                        for (_v, tt) in cls:
                            if tt == 'X':
                                att_x += 1
                            else:
                                att_23 += 1
        print(f"  n_hub = {n}: {len(reps)} classes, {npair} crossing chunk "
              f"pairs; X-hub histogram {sorted(xh.items())}")
        print(f"    slack-0 (no X-hub) pairs: {nx0} -- (GR-73) asserted at "
              f"every one, deg_T = 1 hubs found: {deg1_at_x0} (the lemma "
              f"says 0); slack-<=-1 candidates: {nx0 + nx1}")
        print(f"    of the slack-0 pairs, J-free intersection "
              f"(jfree(T) = 0, forced by defect(T) = 0): {npin}; "
              f"(|T-hubs|, n2, n3, |T|, |R|, |R'|, union = E) profiles "
              f"{sorted(tmpl.items())}")
        print(f"    (GR-76)(iii) dart-count identities asserted at every "
              f"slack-0 pair; (|X|, n2, |F1|, |F2|, |W|) profiles "
              f"{sorted(prof.items())[:8]}{' ...' if len(prof) > 8 else ''}; "
              f"pairs with |X| <= 1, each asserted to have W = 0 (a W branch "
              f"needs two DISTINCT off-T hubs) -- the step (GR-76)(iii) then "
              f"closes for an AA-glue, where |W| >= |F2| forces |F2| = 0 and "
              f"so n_2 = |F1| = 3|X| <= 3 < 4: {sorted(xcnt.items())}")
        print(f"    attachment lemma (GR-38)(ii) re-asserted through "
              f"gorient.attachment_check on a seeded subsample: "
              f"{att_x} X-type, {att_23} (2,3)-type attachment hubs")
    print(f"  => (GR-74): at n_hub = 8 EVERY slack-0 J-free-intersection "
          f"crossing pair has T on all 8 hubs with 10 branches "
          f"(n2 = n3 = 4), R and R' single branches, and union = E(G°)")
    print(f"  [{time.time() - t0:.0f}s]")


def _some_habitat_lens(n, ends, rng):
    """A habitat length assignment for this multigraph, or None -- used only
    to build a subdivision for the LANDED attachment checker."""
    ep = excess_profiles(3 * n // 2, 6)
    order = list(range(len(ep)))
    rng.shuffle(order)
    for idx in order[:400]:
        lens = [2 + e for e in ep[idx]]
        if cubic_habitat(n, list(ends), lens):
            return lens
    return None


# ------------------------------- [AGL-3] --kill8: (GR-75)/(GR-76) -----------
#
# The scan is COMPLETE, not capped, and the completeness rests on three
# necessary conditions, each length-free or per-shape and each asserted
# against the canonical evaluator in --val:
#   (F-a) a residual instance is a CROSSING pair of chunks, both binding in
#         ONE block, with `slack + defect(T) <= 1`  ((GR-38)(iii));
#   (F-b) binding implies `w45(S) + jfree(S) <= 2`  (the (GR-36)(iii) bound,
#         which is <= defect in BOTH blocks);
#   (F-c) `slack >= #X-hubs` ((GR-38)(i)) and `defect(T) >= w45(T) +
#         jfree(T)` (the same charge, valid on an arbitrary branch set),
#         so `#X + w45(T) + jfree(T) <= 1`.
# A (shape, pair) dropped by (F-b)/(F-c) is PROVEN residual-free; it is not
# skipped by a budget.


def _graph_data(n, ends):
    """Colouring- and length-free per-graph data: chunks, per-chunk jfree and
    interior dart-pair masks, crossing pairs, and the residual candidates."""
    chs = chunks_of(n, ends)
    jf = [jfree(ends, ks, dg) for (_m, ks, dg) in chs]
    prs, prsd = [], []
    for (_m, ks, dg) in chs:
        pl, pd = [], {}
        for v, d in sorted(dg.items()):
            if d != 2:
                continue
            m = 0
            for k in ks:
                u, w = ends[k]
                if u == v:
                    m |= 1 << (2 * k)
                if w == v:
                    m |= 1 << (2 * k + 1)
            pl.append(m)
            pd[v] = m
        prs.append(tuple(pl))
        prsd.append(pd)
    cps = crossing_pairs(n, ends, chs)
    cand = [(i, j, tuple(xs), T, jT) for (i, j, xs, T, jT, _d) in cps
            if len(xs) + jT <= 1 and jf[i] <= 2 and jf[j] <= 2]
    return chs, jf, prs, cps, cand, prsd


def slack_direct(prsd_i, prsd_j, xs, ad, blk):
    """(GR-38)(i)'s slack computed DIRECTLY from its definition -- over the
    X-hubs, `psi_S + psi_S'` with `psi_T(v) = [the T-pair at v is not
    own-colour-monochromatic]`.  --kill8 asserts it equal to the value the
    slack IDENTITY gives at every realized pair, so the identity is TESTED
    there and not merely used as a definition (F11)."""
    tot = 0
    for v in xs:
        for pd in (prsd_i, prsd_j):
            m = pd[v]
            if blk == 0:
                if (m & ad) != m:
                    tot += 1
            else:
                if (m & ad) != 0:
                    tot += 1
    return tot


def _cache(ends, lens, ks, prs_i):
    w45 = sum(1 for k in ks if lens[k] >= 4)
    oddm = 0
    for k in ks:
        if lens[k] % 2:
            oddm |= 1 << k
    return (w45, oddm, bin(oddm).count('1'), prs_i)


def _dfast(c, b, ad):
    w45, oddm, nodd, prs = c
    pa = bin(b & oddm).count('1')
    dA = dB = None
    if w45 + pa <= 2:
        naa = 0
        for m in prs:
            if (m & ad) != m:
                naa += 1
        dA = w45 + pa + naa
    if w45 + nodd - pa <= 2:
        nbb = 0
        for m in prs:
            if (m & ad) != 0:
                nbb += 1
        dB = w45 + nodd - pa + nbb
    return dA, dB


def leg_kill8(sl=None):
    """[AGL-3] the exhaustive n_hub = 8 residual scan -- every habitat shape,
    every admissible colouring, every crossing pair that could carry
    `slack + defect(T) <= 1`."""
    t0 = time.time()
    n = 8
    print(f"[AGL-3] (GR-75) the EXHAUSTIVE n_hub = 8 kill-residual scan "
          f"(slice {sl or 'all'}; no rng, no cap)")
    pool, _nep = _pool8()
    idxs = [i for i in range(len(pool)) if pool[i][1]]
    if sl is not None:
        a, k = sl
        idxs = [i for t, i in enumerate(idxs) if t % k == a]
    shapes = live_shapes = ncol = 0
    cand_tot = live_pairs = 0
    bind_inst = pairs_n = 0
    aa_glue = resid = kill_ok = kill_whole = kill_fail = 0
    slack_hist = {}
    dt_hist = {}
    witnesses = []
    for gi in idxs:
        hedges, lens_list = pool[gi]
        ends = list(hedges)
        chs, jf, prs, cps, cand, prsd = _graph_data(n, ends)
        cand_tot += len(cand)
        allm = (1 << len(ends)) - 1
        for lens in lens_list:
            shapes += 1
            lens = list(lens)
            w45 = [sum(1 for k in ks if lens[k] >= 4) for (_m, ks, _d) in chs]
            liv = []
            for (i, j, xs, T, jT) in cand:
                if w45[i] + jf[i] > 2 or w45[j] + jf[j] > 2:
                    continue
                if len(xs) + jT + sum(1 for k in T if lens[k] >= 4) > 1:
                    continue
                liv.append((i, j, xs, T, jT))
            if not liv:
                continue
            live_shapes += 1
            live_pairs += len(liv)
            cset = sorted({i for (i, _j, _x, _T, _t) in liv}
                          | {j for (_i, j, _x, _T, _t) in liv})
            cc = {ci: _cache(ends, lens, chs[ci][1], prs[ci]) for ci in cset}
            for (b, ad) in admissible_bits(n, ends, lens):
                ncol += 1
                bd = {}
                for ci in cset:
                    dA, dB = _dfast(cc[ci], b, ad)
                    if dA is not None and dA <= 2:
                        bd[(ci, 0)] = dA
                    if dB is not None and dB <= 2:
                        bd[(ci, 1)] = dB
                bind_inst += len(bd)
                if len(bd) < 2:
                    continue
                for (i, j, xs, T, jT) in liv:
                    for blk in (0, 1):
                        if (i, blk) not in bd or (j, blk) not in bd:
                            continue
                        pairs_n += 1
                        mi, ksi, _di = chs[i]
                        mj, ksj, _dj = chs[j]
                        un = tuple(k for k in range(len(ends))
                                   if (mi | mj) >> k & 1)
                        dTp = set_defects(ends, lens, T, b, ad)[blk]
                        dUp = set_defects(ends, lens, un, b, ad)[blk]
                        dS, dSp = bd[(i, blk)], bd[(j, blk)]
                        slack = dS + dSp - dUp - dTp
                        slack_hist[slack] = slack_hist.get(slack, 0) + 1
                        dt_hist[dTp] = dt_hist.get(dTp, 0) + 1
                        assert slack == slack_direct(prsd[i], prsd[j], xs,
                                                     ad, blk), \
                            "(GR-38)(i) SLACK IDENTITY refuted: the identity " \
                            "and the direct X-hub sum disagree"
                        assert slack >= len(xs), \
                            "(GR-38)(i): slack below the X-hub count"
                        assert (slack == 0) == (len(xs) == 0), \
                            "(GR-73): slack 0 iff no X-hub refuted"
                        assert dTp >= jT + sum(1 for k in T
                                               if lens[k] >= 4), \
                            "the (GR-36) charge exceeds defect(T)"
                        if slack + dTp <= 1:
                            resid += 1
                            witnesses.append(('RESIDUAL', gi, lens, ksi,
                                              ksj, blk, slack, dTp, dUp))
                        if slack == 0 and dTp == 0:
                            aa_glue += 1
                        if (mi | mj) == allm:
                            kill_whole += 1
                        elif dUp <= 2:
                            kill_ok += 1
                        else:
                            kill_fail += 1
                            witnesses.append(('KILLFAIL', gi, lens, ksi,
                                              ksj, blk, slack, dTp, dUp))
    print(f"  {len(idxs)} habitat-carrying classes, {cand_tot} length-free "
          f"residual-candidate crossing pairs ((F-a)+(F-b)+(F-c))")
    print(f"  {shapes} habitat shapes; {live_shapes} keep a candidate after "
          f"the per-shape length filter ({live_pairs} (shape, pair) "
          f"instances); the other {shapes - live_shapes} are PROVEN "
          f"residual-free by (F-b)/(F-c), not skipped by a budget")
    print(f"  {ncol} admissible colourings visited (every colouring of every "
          f"live shape), {bind_inst} binding (candidate chunk, block) "
          f"instances")
    print(f"  crossing same-block binding CANDIDATE pairs realized: "
          f"{pairs_n}; slack histogram {sorted(slack_hist.items())}, "
          f"defect(T) histogram {sorted(dt_hist.items())}")
    print(f"  => kill residual (slack + defect(T) <= 1): {resid}; "
          f"AA-GLUE (slack = 0 AND defect(T) = 0): {aa_glue}")
    print(f"  union binding: {kill_ok}; union = E(G°) (defect 3 "
          f"identically): {kill_whole}; union proper and NOT binding "
          f"(a kill FAILURE): {kill_fail}")
    if witnesses:
        print(f"  FIRST WITNESS: {witnesses[0]}")
    assert aa_glue == 0, \
        "an AA-GLUE instance EXISTS at n_hub = 8 -- (GR-75) is overturned; " \
        "read the FIRST WITNESS line above"
    assert resid == 0, \
        "the (GR-38) kill RESIDUAL is inhabited at n_hub = 8 -- read the " \
        "FIRST WITNESS line above"
    assert kill_fail == 0, "the (GR-38) kill FAILS at n_hub = 8"
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------- [AGL-6] --lam8: the laminarity census ------

def leg_lam8(sl=None):
    """[AGL-6] the laminarity census at n_hub = 8: do crossing same-block
    binding chunk pairs EXIST there at all?  (GR-38)(iii)'s n <= 6 answer is
    0 of 53 740 binding instances.  This is NOT needed for the (GR-75)
    verdict -- an empty kill residual gives laminarity of the MAXIMAL
    binding family as a corollary -- it measures whether the kill is
    non-vacuous at n_hub = 8."""
    t0 = time.time()
    n = 8
    print(f"[AGL-6] the n_hub = 8 laminarity census (slice {sl or 'all'}; "
          f"no rng, no cap within the slice)")
    pool, _nep = _pool8()
    idxs = [i for i in range(len(pool)) if pool[i][1]]
    if sl is not None:
        a, k = sl
        idxs = [i for t, i in enumerate(idxs) if t % k == a]
    shapes = ncol = bind_inst = pairs_n = 0
    nest = 0
    first = None
    fg_shapes = flank = 0
    fg_cols = 0
    flank_wit = None
    fg_hist = {}
    for gi in idxs:
        hedges, lens_list = pool[gi]
        ends = list(hedges)
        chs, jf, prs, cps, _cand, _pd = _graph_data(n, ends)
        cross = {}
        for (i, j, xs, T, jT, _d) in cps:
            cross[(i, j)] = (len(xs), T, jT)
        hubs_of = [frozenset(dg) for (_m, _ks, dg) in chs]
        for lens in lens_list:
            shapes += 1
            lens = list(lens)
            cap = [ci for ci in range(len(chs))
                   if sum(1 for k in chs[ci][1] if lens[k] >= 4) + jf[ci] <= 2]
            cc = {ci: _cache(ends, lens, chs[ci][1], prs[ci]) for ci in cap}
            nfg = 0
            for (b, ad) in admissible_bits(n, ends, lens):
                ncol += 1
                bind = {0: [], 1: []}
                for ci in cap:
                    dA, dB = _dfast(cc[ci], b, ad)
                    if dA is not None and dA <= 2:
                        bind[0].append(ci)
                    if dB is not None and dB <= 2:
                        bind[1].append(ci)
                bind_inst += len(bind[0]) + len(bind[1])
                if not bind[0] and not bind[1]:
                    nfg += 1
                for blk in (0, 1):
                    lst = bind[blk]
                    for a1 in range(len(lst)):
                        for a2 in range(a1 + 1, len(lst)):
                            i, j = lst[a1], lst[a2]
                            if not (hubs_of[i] & hubs_of[j]):
                                continue
                            mi, mj = chs[i][0], chs[j][0]
                            if (mi & mj) == mi or (mi & mj) == mj:
                                nest += 1
                                continue
                            pairs_n += 1
                            if first is None:
                                first = (gi, lens, chs[i][1], chs[j][1], blk)
            fg_cols += nfg
            fg_hist[min(nfg, 10)] = fg_hist.get(min(nfg, 10), 0) + 1
            if nfg:
                fg_shapes += 1
            else:
                flank += 1
                if flank_wit is None:
                    flank_wit = (gi, lens)
    print(f"  {len(idxs)} classes, {shapes} habitat shapes, {ncol} "
          f"admissible colourings, {bind_inst} binding (chunk, block) "
          f"instances over the binding-capable family")
    print(f"  same-block binding pairs sharing a hub: nested {nest}, "
          f"CROSSING {pairs_n}")
    if first is not None:
        print(f"  first crossing pair: {first}")
    print(f"  THE E1 CONTROL (free by-product of this scan, exact and "
          f"exhaustive over the slice): {fg_shapes} of {shapes} shapes carry "
          f"a FULLY-GOOD admissible colouring (no binding chunk in either "
          f"block); {flank} do NOT -- a shape with 0 is a g-FLANK and fires "
          f"E1.  Fully-good colourings: {fg_cols} of {ncol}; per-shape count "
          f"histogram (capped at 10) {sorted(fg_hist.items())}")
    if flank_wit is not None:
        print(f"  E1 WITNESS (g-flank): class {flank_wit[0]}, "
              f"lengths {flank_wit[1]}")
    assert flank == 0, \
        "a g-FLANK exists at n_hub = 8: some habitat shape has a binding " \
        "chunk at EVERY admissible colouring -- E1 FIRES, read the E1 " \
        "WITNESS line"
    print(f"  [{time.time() - t0:.0f}s]")


def _col_of(hm, lens, b):
    """The subdivision-level colouring of the bit vector `b`."""
    col = {}
    for k, (_u, _w, path) in enumerate(hm['branches']):
        c = 'A' if (b >> k & 1) else 'B'
        for e in path:
            col[e] = c
            c = 'B' if c == 'A' else 'A'
    return col


# --------------------------------------------- [AGL-4] --adv ---------------

def leg_adv():
    """[AGL-4] the falsification controls: the detector must FIRE."""
    t0 = time.time()
    print(f"[AGL-4] falsification controls (seed {A_SEED + 4})")
    rng = random.Random(A_SEED + 4)
    # (a) K4: the combinatorial detector fires at n_hub = 4
    k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    chs = chunks_of(4, k4)
    cps = crossing_pairs(4, k4, chs)
    zero = [(i, j, T, jT) for (i, j, xs, T, jT, _d) in cps if not xs]
    print(f"  (a) K4 (n_hub = 4): {len(chs)} chunks, {len(cps)} crossing "
          f"pairs, {len(zero)} with NO X-hub (slack 0) -- the "
          f"combinatorial detector FIRES")
    assert zero, "the slack-0 detector finds nothing even at K4"
    i, j, T, jT = zero[0]
    print(f"      first: S = {chs[i][1]}, S' = {chs[j][1]}, T = {T}, "
          f"jfree(T) = {jT} (so defect(T) >= {jT} > 0: K4's intersection is "
          f"a 4-circuit, every hub an interior -- the J-charge is why this "
          f"slack-0 pair is NOT an AA-glue)")
    assert jT > 0, "K4's slack-0 intersection is J-free"
    # (b) slack 0 at n_hub = 8
    pool, _ = _pool8()
    tot0 = totpin = 0
    for (hedges, lens_list) in pool:
        ends = list(hedges)
        cps = crossing_pairs(8, ends, chunks_of(8, ends))
        z = [(i, j, T, jT) for (i, j, xs, T, jT, _d) in cps if not xs]
        tot0 += len(z)
        totpin += sum(1 for (_i, _j, _T, jT) in z if jT == 0)
    print(f"  (b) n_hub = 8, all 20 classes: {tot0} slack-0 crossing pairs, "
          f"{totpin} of them J-free -- both detectors FIRE, so the 0 in "
          f"--kill8 is a colouring fact, not an empty search")
    assert tot0 and totpin, "the n_hub = 8 slack-0 detector finds nothing"
    # (c) (GR-30)'s W3M: the landed MINIMAL n_hub = 8 witness, re-measured
    name, nn, specs, first, S_idx, _exp = WITNESSES[0]
    assert nn == 8, "WITNESSES[0] is not the n_hub = 8 witness"
    ends = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    assert cubic_habitat(8, ends, lens), \
        "(GR-30)'s W3M fails cubic_habitat -- pin drift"
    edges = subdivide(specs)
    hm = hub_model(edges)
    allverts = sorted(verts_of(edges), key=str)
    col = wit_colouring(specs, first)
    assert admissible(edges, allverts, hm, col), "W3M colouring not admissible"
    b = 0
    for k, (_u, _w, path) in enumerate(hm['branches']):
        if col[path[0]] == 'A':
            b |= 1 << k
    hidx = {v: i for i, v in enumerate(hm['hubs'])}
    hends = [(hidx[u], hidx[w]) for (u, w) in hm['ends']]
    hlens = hm['lens']
    ad = dartmask(hlens, b)
    chs8 = chunks_of(8, hends)
    nb = 0
    for (m, ks, dg) in chs8:
        c = chunk_cache(hends, hlens, m, ks, dg)
        dA, dB = fast_defects(c, b, ad)
        if (dA is not None and dA <= 2) or (dB is not None and dB <= 2):
            nb += 1
    print(f"  (c) {name}: habitat-gated, colouring admissible, and this "
          f"driver's own devices find {nb} binding (chunk, block) instances "
          f"at it -- the BINDING detector fires at n_hub = 8")
    assert nb > 0, "no binding chunk found at (GR-30)'s W3M"
    print(f"  [{time.time() - t0:.0f}s]")


# --------------------------------------------- [AGL-5] --val ---------------

def leg_val():
    """[AGL-5] every fast device asserted equal to the canonical one."""
    t0 = time.time()
    print(f"[AGL-5] device cross-certification (seed {A_SEED + 5})")
    rng = random.Random(A_SEED + 5)
    # 1. the generator
    for n in (2, 4, 6):
        assert len(cubic_iso_classes(n)) == len(multigraphs(n, 3 * n // 2))
    print("  1. cubic_iso_classes == gridcol.multigraphs class count at "
          "n = 2, 4, 6")
    # 2/3/4/5. chunks, admissibility, defect, slack, (GR-36) bound on the
    #          COMPLETE n <= 6 pool, plus seeded n = 8 shapes
    nsh = ncol = nch = ndef = nsl = nbd = 0
    todo = []
    for n in (2, 4, 6):
        for hedges in cubic_iso_classes(n):
            for exc in excess_profiles(3 * n // 2, 6):
                lens = [2 + e for e in exc]
                if cubic_habitat(n, list(hedges), lens):
                    todo.append((n, list(hedges), lens))
    n6 = len(todo)
    pool8, _ = _pool8()
    eight = [(8, list(h), list(L)) for (h, ls) in pool8 for L in ls]
    rng.shuffle(eight)
    todo += eight[:60]
    for (n, ends, lens) in todo:
        nsh += 1
        specs = [(u, w, L) for (u, w), L in zip(ends, lens)]
        edges = subdivide(specs)
        hm = hub_model(edges)
        allverts = sorted(verts_of(edges), key=str)
        inc = incidence(hm)
        hidx = {v: i for i, v in enumerate(hm['hubs'])}
        hends = [(hidx[u], hidx[w]) for (u, w) in hm['ends']]
        hlens = hm['lens']
        assert list(hlens) == list(lens), "branch order drift vs hub_model"
        assert [frozenset(e) for e in hends] == \
            [frozenset(e) for e in ends], "branch END order drift vs hub_model"
        mine = chunks_of(n, hends)
        can = two_ec_subsets(hm, kmin=1)
        assert sorted(ks for (_m, ks, _d) in mine) == \
            sorted(tuple(ks) for (ks, _kk) in can), \
            "chunks_of disagrees with gcap.two_ec_subsets(kmin=1)"
        nch += len(mine)
        # the (GR-36) bound vs gorient.jdata
        for (_m, ks, dg) in mine:
            jd = jdata(hm, inc, list(ks))
            w45 = sum(1 for k in ks if hlens[k] >= 4)
            assert jd['bound'] == w45 + jfree(hends, ks, dg), \
                "jfree + w45 != gorient.jdata bound"
            nbd += 1
        # admissibility
        cols, odd = colourings(edges, cap=1 << 14)
        assert not odd and cols is not None
        canon_adm = set()
        for ci, col in enumerate(cols):
            if admissible(edges, allverts, hm, col):
                b = 0
                for k, (_u, _w, path) in enumerate(hm['branches']):
                    if col[path[0]] == 'A':
                        b |= 1 << k
                canon_adm.add(b)
        mine_adm = {b for (b, _ad) in admissible_bits(n, hends, hlens)}
        assert mine_adm == canon_adm, \
            "admissible_bits != cflank.admissible on the subdivision"
        ncol += len(mine_adm)
        # defects and slack at every admissible colouring of a subsample
        for (b, ad) in admissible_bits(n, hends, hlens):
            if rng.random() > (0.006 if n < 8 else 0.02):
                continue
            col = _col_of(hm, hlens, b)
            stats = branch_stats(hm, col, 'A')
            statsB = (
                [hlens[k] - stats[0][k] for k in range(len(hlens))],
                [not x for x in stats[1]], [not x for x in stats[2]])
            for (m, ks, dg) in mine:
                c = chunk_cache(hends, hlens, m, ks, dg)
                dA, dB = fast_defects(c, b, ad)
                gA = defect_direct(hm, inc, stats, list(ks), True)
                gB = defect_direct(hm, inc, stats, list(ks), False)
                assert dA is None or dA == gA, "fast defect_A drift"
                assert dB is None or dB == gB, "fast defect_B drift"
                sA, sB = set_defects(hends, hlens, ks, b, ad)
                assert (sA, sB) == (gA, gB), "set_defects drift"
                ndef += 1
            cps = crossing_pairs(n, hends, mine)
            rng.shuffle(cps)
            for (i, j, xs, T, _jT, _dT) in cps[:25]:
                ksi, ksj = mine[i][1], mine[j][1]
                sk, nd = pair_slack(hm, inc, stats, list(ksi), list(ksj))
                assert nd == len(xs), \
                    "X-hub count != gorient.pair_slack's different-pair count"
                assert sk >= len(xs) and (sk == 0) == (not xs), \
                    "slack / X-hub relation broken"
                dS, _ = set_defects(hends, hlens, ksi, b, ad)
                dSp, _ = set_defects(hends, hlens, ksj, b, ad)
                un = tuple(sorted(set(ksi) | set(ksj)))
                dU, _ = set_defects(hends, hlens, un, b, ad)
                dT, _ = set_defects(hends, hlens, T, b, ad)
                assert dS + dSp == dU + dT + sk, \
                    "(GR-38)(i) slack identity refuted"
                skB, ndB = pair_slack(hm, inc, statsB, list(ksi), list(ksj))
                _, dSb = set_defects(hends, hlens, ksi, b, ad)
                _, dSpb = set_defects(hends, hlens, ksj, b, ad)
                _, dUb = set_defects(hends, hlens, un, b, ad)
                _, dTb = set_defects(hends, hlens, T, b, ad)
                assert dSb + dSpb == dUb + dTb + skB, \
                    "(GR-38)(i) slack identity refuted in block B"
                assert jfree(hends, T) <= min(dT, dTb), \
                    "the (GR-36) charge exceeds the intersection defect"
                nsl += 1
    print(f"  2-6. over the COMPLETE n <= 6 habitat pool ({n6} shapes) plus "
          f"60 seeded n = 8 shapes: {nch} chunk sets, {nbd} (GR-36) bounds, "
          f"{ncol} admissible colourings, {ndef} defect pairs, {nsl} slack "
          f"identities (both blocks) -- every one equal to the canonical "
          f"evaluator")
    assert n6 == 4920, "the n <= 6 habitat pool is not the recorded 4920"
    # 7. the (GR-76) charge table, by enumeration of the six cases
    rows = []
    for L in (2, 3, 4, 5):
        for amaj in (True, False):
            if L % 2 == 0 and not amaj:
                continue
            c = (1 if L >= 4 else 0) + (1 if (L % 2 and amaj) else 0)
            e = L - 2
            rows.append((L, 'A' if (L % 2 and amaj) else '-', c, e, e - c))
    for (L, mj, c, e, d) in rows:
        assert d == e - c
    assert all(d >= c - 1 for (_L, _m, c, _e, d) in rows), \
        "(GR-76) W-row bound e - c >= c - 1 refuted"
    f2 = [(L, c, e, e - c) for (L, mj, c, e, _d) in rows
          if not (L % 2 and mj == 'A') for e in [L - 2] if L % 2]
    # 8. the (GR-38) n <= 6 headline, reproduced through THIS driver's
    #    census pipeline (item 7; the strongest single check: the landed figures are
    #    4920 shapes / 284 512 admissible colourings / 53 740 binding
    #    (chunk, block) instances / 0 crossing same-block binding pairs)
    sh6 = col6 = bind6 = cross6 = nest6 = 0
    for n in (2, 4, 6):
        for hedges in cubic_iso_classes(n):
            ends = list(hedges)
            chs, jf, prs, _cps, _cd, _pd = _graph_data(n, ends)
            allm = (1 << len(ends)) - 1
            hubs_of = [frozenset(dg) for (_m, _ks, dg) in chs]
            for exc in excess_profiles(3 * n // 2, 6):
                lens = [2 + e for e in exc]
                if not cubic_habitat(n, list(ends), lens):
                    continue
                sh6 += 1
                cap = [ci for ci in range(len(chs))
                       if chs[ci][0] != allm
                       and sum(1 for k in chs[ci][1] if lens[k] >= 4)
                       + jf[ci] <= 2]
                cc = {ci: _cache(ends, lens, chs[ci][1], prs[ci])
                      for ci in cap}
                for (b, ad) in admissible_bits(n, ends, lens):
                    col6 += 1
                    bind = {0: [], 1: []}
                    for ci in cap:
                        dA, dB = _dfast(cc[ci], b, ad)
                        if dA is not None and dA <= 2:
                            bind[0].append(ci)
                        if dB is not None and dB <= 2:
                            bind[1].append(ci)
                    bind6 += len(bind[0]) + len(bind[1])
                    for blk in (0, 1):
                        lst = bind[blk]
                        for a1 in range(len(lst)):
                            for a2 in range(a1 + 1, len(lst)):
                                i, j = lst[a1], lst[a2]
                                if not (hubs_of[i] & hubs_of[j]):
                                    continue
                                mi, mj = chs[i][0], chs[j][0]
                                if (mi & mj) in (mi, mj):
                                    nest6 += 1
                                else:
                                    cross6 += 1
    print(f"  7. (GR-38)'s n <= 6 headline reproduced through this driver's "
          f"OWN census pipeline: {sh6} shapes, {col6} admissible colourings, "
          f"{bind6} binding (chunk, block) instances, {nest6} nested and "
          f"{cross6} CROSSING same-block binding pairs")
    assert (sh6, col6, bind6, cross6) == (4920, 284512, 53740, 0), \
        "the (GR-38) n <= 6 figures are not reproduced -- device drift"
    print(f"  8. (GR-76) charge table (l, odd-majority, c, e, e-c): "
          f"{sorted(rows)}; W-rows satisfy e - c >= c - 1, F1-rows "
          f"(B at one end, so no A-majority odd) e - c >= c, F2-rows "
          f"(B at both ends, so odd B-majority) e - c >= c + 1")
    print(f"  [{time.time() - t0:.0f}s]")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', action='store_true')
    ap.add_argument('--pin', action='store_true')
    ap.add_argument('--kill8', action='store_true')
    ap.add_argument('--lam8', action='store_true')
    ap.add_argument('--slice', default=None)
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--val', action='store_true')
    a = ap.parse_args()
    sl = None
    if a.slice:
        i, k = a.slice.split('/')
        sl = (int(i), int(k))
    any_ = False
    if a.pool:
        leg_pool()
        any_ = True
    if a.pin:
        leg_pin()
        any_ = True
    if a.kill8:
        leg_kill8(sl)
        any_ = True
    if a.lam8:
        leg_lam8(sl)
        any_ = True
    if a.adv:
        leg_adv()
        any_ = True
    if a.val:
        leg_val()
        any_ = True
    if not any_:
        ap.print_help()


if __name__ == '__main__':
    main()
