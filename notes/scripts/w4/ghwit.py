"""GHWIT -- the thirty-sixth kernel-(K) ordinal: the HALF-WITNESS CLAUSE
(GR-117)(iii) (spec: notes/Pencil-fanout.md S"GHWIT").

TARGET: *every pos-carrying O <= M pair has a maximum that is
balance-valid or half-resident* -- equivalently (contrapositive) no
O <= M, 2k = 2 pair has EVERY maximum forcing with both odd branches
fully resident (residency (2, 2), |h| = 4).

OUTCOME: a REFUTATION BY WITNESS -- the clause, the gap-2 law and
(GR-104)(i) at 2k = 2 all FALL -- plus a proven numerical gate that
makes the boundary sharp.

  (GR-120) THE (2,2) BUDGET (proven; --census).  At any O <= M pair
  (every 2k, any number of F-cycles), a FORCING maximum with residency
  (2, 2) forces the exact chord budget

      e_f + 2 h_s + f_0  =  n/2 - 6,      dist = 2 h_s + 4 + 2 f_0,

  where e_f = #full even chords, h_s = #half even chords whose RESIDENT
  end is a source, f_0 = #free even chords (both ends through).  Hence
  n >= 12 and d_par(M) >= 4, with n = 12 forcing e_f = h_s = f_0 = 0.
  COROLLARY: the half-witness clause -- hence the gap-2 law (GR-117)(i),
  hence (GR-104)(i) at 2k = 2, O <= M -- holds UNCONDITIONALLY at every
  pair with n <= 10, and at every pair with d_par(M) <= 2.

  (GR-121) THE SLIDE GATE (proven, and REFUTED as a complete route;
  --census).  At a (2,2) pos maximum with sink set K, sliding the source
  at an odd end e to any other position p of e's (GR-110) arc yields a
  maximum with that branch HALF-resident, and is valid iff p's M-partner
  is not a source other than e.  So a clause failure needs all four
  odd-end arcs FULLY BLOCKED; at d_par = 4 that means all four odd ends
  TIGHT.  Measured: only 20 of 40 (2,2) maxima on the landed pools, and
  half of those at each (GR-116) witness, are rescued by ONE slide -- the
  gate is a real necessary condition, not a proof.

  (GR-122) THE REFUTATION (--verify).  `refut20`: an explicit
  habitat-GATED single-F-cycle O <= M, 2k = 2 pair at n = 20 whose
  maximum family is 64 members, ALL forcing with residency (2, 2), no
  balance-valid and no half-resident member, and whose gap is
      d_adm(M) - d_par(M) = 8 - 4 = 4.
  So the half-witness clause (GR-117)(iii) is FALSE, the gap-2 law
  (GR-117)(i) is FALSE, and (GR-104)(i) at 2k = 2 -- i.e. per-matching
  (b') at the constant 2 -- is FALSE.  (GR-86)'s gap-4 cap is TIGHT.
  Every figure asserted through FOUR independent exact models.
  `clause20` is the weaker companion (all-(2,2), gap 2).

  (GR-123) THE CORRECTED (GR-108) BOUNDARY (--verify, --exh).  Three
  explicit habitat-GATED n = 12 pairs have pure pos + neg maximum
  families (gap 2): the balance law is FALSE from n = 12, NOT from
  n = 16 -- (GR-116)(iv)'s boundary sentence is refuted (its n <= 14
  legs were correctly hedged as "not found under cap").  And n = 12 is
  EXACT: EXHAUSTIVELY over every F-cycle type and every chord diagram at
  n <= 10, the 12 gap-2 instances that exist are none of them
  habitat-realizable under any ell-placement.

  Also measured (--exh, --build): 0 all-(2,2) and 0 gap-4 instances
  EXHAUSTIVELY over ALL chord diagrams, UNGATED, at n <= 12 (every
  F-cycle type) and n = 14 (single-cycle); the climb reaches (2,2)
  fraction 0.82 at n = 18 and 1.0 only at n = 20.

  REFUTED as a route (--census): the reduction *"the clause reduces to
  `some maximum has |h| = 2`"* -- the landed (GR-116) witness rand20b is
  pos-carrying with min |h| = 3 over its whole maximum family.

Modes:
  --census   (GR-120)/(GR-121)/(GR-122) asserted over the landed pools
             + the min-|h| refutation of the |h| = 2 reduction.
  --exh      the EXHAUSTIVE ungated diagram sweep (see above).
  --build    the budget-targeted construction hunt at n = 12..20.
  --validate all three.

Sibling imports (S2 rule-2 trips, DISCLOSED -- extending the recorded
GBLAW/GXESC *Harness debt* item's consumer lists; the move is the
coordinator's, not this dispatch's): `cell_data`, `cell_shapes`,
`pairs_of`, `rmodel_f` from `w4/gprice.py` (FOURTH consumer) and
`refut_specs`, `specs_of_diagram`, `word_census`, `word_stats`,
`word_valid` from `w4/gxesc.py` (SECOND consumer), all
read-only.  Balance-layer devices come DIRECTLY from gridbal_common,
never via the sibling re-exports.

Rank-free throughout: gexist.fully_good_rank is never imported or
called and no d_fg claim is made anywhere.  Exact integers / GF(2); no
floating point; every rng seeded, seed printed.
"""
import argparse
import collections
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from gridbal_common import odd_idx, stratum_cases, v8_specs           # noqa: E402
from gprice import cell_data, cell_shapes, pairs_of, rmodel_f        # noqa: E402
from gxesc import (refut_specs, specs_of_diagram,                     # noqa: E402
                   word_census, word_stats, word_valid)
from cflank import cubic_habitat                                      # noqa: E402

R_SEED = 20260826


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  `hub_edges` gives the
# (prev, next) F-edge index pair of every hub for ANY 2-factor cycle
# system (the gxesc word model's multi-cycle generalization, and it
# reduces to it verbatim on one cycle); `state_tables` the per-word hub
# states; `word_bitsets` the bitset layer the exhaustive sweep runs on;
# `pair_scan` the whole (M*, gap, all22) verdict of one diagram in
# bitset ops; `budget_of` the (GR-120) chord census of one labeled
# configuration; `slide_test` the (GR-121) criterion; `naive_family` the
# self-contained FOURTH model (no project device); `n12_specs` /
# `n20_specs` the pinned witnesses; `gate_general` the all-ell-placement
# habitat gate.


def hub_edges(cycles):
    """(prev, next) F-edge index of every hub, edges numbered along the
    cycles in order.  Hub v is a REVERSAL hub iff bits prev, next
    differ, and a SINK iff bit prev = 1 (gxesc's single-cycle
    convention verbatim when cycles = [[0, 1, ..., n-1]])."""
    pe, ne = {}, {}
    eid = 0
    for cyc in cycles:
        L = len(cyc)
        first = eid
        for t in range(L):
            v, w = cyc[t], cyc[(t + 1) % L]
            ne[v] = eid
            pe[w] = eid
            eid += 1
        assert eid - first == L
    return pe, ne


def state_tables(n, cycles):
    """For every word w in [0, 2^n): the hub-state arrays.  Returns
    (size, sink, src) with sink/src hub bitmasks and size = |R|."""
    pe, ne = hub_edges(cycles)
    W = 1 << n
    size = [0] * W
    sink = [0] * W
    src = [0] * W
    for w in range(W):
        sk = 0
        sr = 0
        c = 0
        for v in range(n):
            a = (w >> pe[v]) & 1
            b = (w >> ne[v]) & 1
            if a == b:
                continue
            c += 1
            if a:
                sk |= 1 << v
            else:
                sr |= 1 << v
        size[w] = c
        sink[w] = sk
        src[w] = sr
    return size, sink, src


def word_bitsets(n, cycles):
    """The bitset layer: SINK[v] / SRC[v] / RES[v] = the set of words (as
    a big-int bitset over word ids) at which hub v is a sink / source /
    reversal hub, and SZ[s] = the words with |R| = s.  Bits are packed
    into bytearrays first -- setting a bit on a 2^n-bit int is O(2^n),
    so the naive accumulation is quadratic."""
    size, sink, src = state_tables(n, cycles)
    W = 1 << n
    nb = (W + 7) // 8
    bsink = [bytearray(nb) for _ in range(n)]
    bsrc = [bytearray(nb) for _ in range(n)]
    bsz = [bytearray(nb) for _ in range(n + 1)]
    for w in range(W):
        q, r = w >> 3, w & 7
        m = 1 << r
        sk, sr = sink[w], src[w]
        while sk:
            v = (sk & -sk).bit_length() - 1
            bsink[v][q] |= m
            sk &= sk - 1
        while sr:
            v = (sr & -sr).bit_length() - 1
            bsrc[v][q] |= m
            sr &= sr - 1
        bsz[size[w]][q] |= m
    conv = lambda ba: int.from_bytes(bytes(ba), 'little')
    SINK = [conv(b) for b in bsink]
    SRC = [conv(b) for b in bsrc]
    SZ = [conv(b) for b in bsz]
    RES = [SINK[v] | SRC[v] for v in range(n)]
    ALL = (1 << W) - 1
    return SINK, SRC, RES, SZ, ALL


def maxsize(bs, SZ, n):
    """The largest |R| attained on a nonempty word bitset."""
    for s in range(n, -1, -1):
        if bs & SZ[s]:
            return s
    return -1


def pair_scan(n, chords, oj, SINK, SRC, RES, SZ, ALL):
    """One (diagram, odd-pair) instance in bitset ops.  `chords` is the
    chord list, `oj` the index pair of the two odd chords.  Returns
    (mstar, gap, all22, dpar): gap = d_adm - d_par ((GR-117)(i)), and
    all22 = the (GR-117)(iii) open case at this pair -- every maximum
    forcing with both odd branches fully resident."""
    ev = ALL
    for j, (a, b) in enumerate(chords):
        if j in oj:
            continue
        ev &= ~((SINK[a] & SINK[b]) | (SRC[a] & SRC[b]))
    (a1, b1) = chords[oj[0]]
    (a2, b2) = chords[oj[1]]
    ends = (a1, b1, a2, b2)
    aa = ev
    for v in ends:
        aa &= ~SINK[v]
    ab = ev & ~SINK[a1] & ~SINK[b1] & ~SRC[a2] & ~SRC[b2]
    m_aa = maxsize(aa, SZ, n)
    m_ab = maxsize(ab, SZ, n)
    mstar = max(m_aa, m_ab)
    gap = m_aa - m_ab if m_aa > m_ab else 0
    all22 = False
    if gap > 0:
        fam = aa & SZ[mstar]
        full = RES[a1] & RES[b1] & RES[a2] & RES[b2]
        all22 = (fam & ~full) == 0
    return mstar, gap, all22, n - mstar


def budget_of(n, sigma, mpairs, oddends):
    """(GR-120): the chord census of one labeled configuration.  sigma[v]
    in {0 = through, 1 = source, 2 = sink}.  Returns
    (e_f, h_s, h_k, f_0, resid, cls) with resid the sorted per-odd-branch
    resident-end count and cls the (GR-112)(i) class word at 2k = 2."""
    e_f = h_s = h_k = f_0 = 0
    for (a, b) in mpairs:
        ra, rb = sigma[a], sigma[b]
        if ra and rb:
            e_f += 1
        elif not ra and not rb:
            f_0 += 1
        else:
            s = ra if ra else rb
            if s == 1:
                h_s += 1
            else:
                h_k += 1
    resid = []
    labs = []
    for (u, w) in oddends:
        ls = {sigma[v] for v in (u, w) if sigma[v]}
        resid.append(sum(1 for v in (u, w) if sigma[v]))
        labs.append(None if not ls else (ls.pop() if len(ls) == 1 else -1))
    if labs and all(x == 1 for x in labs):
        cls = 'pos'
    elif labs and all(x == 2 for x in labs):
        cls = 'neg'
    else:
        cls = 'bal'
    return e_f, h_s, h_k, f_0, tuple(sorted(resid)), cls


def budget_assert(n, sigma, mpairs, oddends, dist):
    """The (GR-120) clauses at one valid configuration."""
    e_f, h_s, h_k, f_0, resid, cls = budget_of(n, sigma, mpairs, oddends)
    nres = sum(1 for v in range(n) if sigma[v])
    assert 2 * (e_f + h_s + h_k + f_0) + 2 * len(oddends) == n, \
        '(GR-120) chord count != n/2'
    assert n - nres == dist, '(GR-120) dist identity broken'
    if cls in ('pos', 'neg') and resid == (2, 2):
        assert h_k - h_s == 4 if cls == 'pos' else h_s - h_k == 4, \
            '(GR-120) the (2,2) ledger is not +-4'
        assert e_f + 2 * min(h_s, h_k) + f_0 == n // 2 - 6, \
            '(GR-120) the (2,2) chord budget fails'
        assert n >= 12, '(GR-120) a (2,2) forcing maximum below n = 12'
        assert dist >= 4, '(GR-120) a (2,2) forcing maximum with dist < 4'
        if n == 12:
            assert e_f == 0 and min(h_s, h_k) == 0 and f_0 == 0, \
                '(GR-120) the n = 12 rigidity fails'
    return e_f, h_s, h_k, f_0, resid, cls


def sigma_of_word(n, w, pe, ne):
    """The labeled configuration of one orientation word."""
    sig = [0] * n
    for v in range(n):
        a = (w >> pe[v]) & 1
        b = (w >> ne[v]) & 1
        if a != b:
            sig[v] = 2 if a else 1
    return sig


def naive_family(n, ech, gch):
    """A DELIBERATELY INDEPENDENT FOURTH MODEL of one single-F-cycle
    O <= M, 2k = 2 pair.  Self-contained brute force over all 2^n
    orientation words using NO project device: it recomputes hub states,
    validity, sizes, per-pattern optima and classes from the raw chord
    lists, so it shares no code path with the landed gxesc word census,
    the landed gprice rmodel_f, or this file's own bitset layer (its
    only contact with them is the ANSWER, which is what is asserted).
    Deliberately unoptimized -- ~2 s at n = 20.

    Returns (best, mstar, nfam, prof): `best` the max |R| at each of the
    four PATTERNS (so `n - best[p]` is (GR-106)(iv)'s f(p)), `mstar` the
    max over patterns, `nfam` the number of valid words of size mstar
    (the labeled maximum family), `prof` its (class, residency) profile.
    """
    THROUGH, SOURCE, SINK = 0, 1, 2
    pats = (('AA', SOURCE, SOURCE), ('AB', SOURCE, SINK),
            ('BA', SINK, SOURCE), ('BB', SINK, SINK))
    (u1, v1), (u2, v2) = gch[0], gch[1]
    best = {name: -1 for (name, _c1, _c2) in pats}
    for w in range(1 << n):
        st = [THROUGH] * n
        size = 0
        for v in range(n):
            a = (w >> ((v - 1) % n)) & 1
            b = (w >> v) & 1
            if a != b:
                st[v] = SINK if a else SOURCE
                size += 1
        ok = True
        for (a, b) in ech:
            if st[a] != THROUGH and st[a] == st[b]:
                ok = False
                break
        if not ok:
            continue
        for (name, c1, c2) in pats:
            if size <= best[name]:
                continue
            if st[u1] != THROUGH and st[u1] != c1:
                continue
            if st[v1] != THROUGH and st[v1] != c1:
                continue
            if st[u2] != THROUGH and st[u2] != c2:
                continue
            if st[v2] != THROUGH and st[v2] != c2:
                continue
            best[name] = size
    mstar = max(best.values())
    nfam = 0
    prof = collections.Counter()
    for w in range(1 << n):
        st = [THROUGH] * n
        size = 0
        for v in range(n):
            a = (w >> ((v - 1) % n)) & 1
            b = (w >> v) & 1
            if a != b:
                st[v] = SINK if a else SOURCE
                size += 1
        if size != mstar:
            continue
        ok = True
        for (a, b) in ech:
            if st[a] != THROUGH and st[a] == st[b]:
                ok = False
                break
        if ok:
            for (a, b) in gch:
                if st[a] != THROUGH and st[b] != THROUGH and st[a] != st[b]:
                    ok = False
                    break
        if not ok:
            continue
        nfam += 1
        labs = set()
        resid = []
        for (a, b) in gch:
            r = 0
            for e in (a, b):
                if st[e] != THROUGH:
                    labs.add(st[e])
                    r += 1
            resid.append(r)
        if len(labs) != 1:
            cls = 'bal'
        else:
            cls = 'pos' if SOURCE in labs else 'neg'
        prof[(cls, tuple(sorted(resid)))] += 1
    return best, mstar, nfam, prof


def n12_specs():
    """The THREE pinned n = 12 (GR-108) refutation witnesses found by the
    --exh sweep (lex-first three F-parallel-free single-F-cycle gap-2
    diagrams that pass the landed specs_of_diagram habitat recipe).
    Positional diagrams on the cycle 0..11; pinned figures
    (M*, family, #pos, #neg, #bal, gap, min |h|)."""
    return [
        ('n12a', 12, [(0, 2), (1, 4), (6, 8), (7, 10)],
         [(3, 11), (5, 9)], (8, 72, 36, 36, 0, 2, 2)),
        ('n12b', 12, [(0, 2), (1, 10), (4, 7), (6, 8)],
         [(3, 11), (5, 9)], (8, 72, 36, 36, 0, 2, 2)),
        ('n12c', 12, [(0, 3), (2, 4), (6, 9), (8, 10)],
         [(1, 5), (7, 11)], (8, 72, 36, 36, 0, 2, 2)),
    ]


def n20_specs():
    """The pinned n = 20 witnesses found by the --build climb (seed
    20260826).  `refut20` REFUTES (GR-104)(i) at 2k = 2 (gap 4);
    `clause20` refutes only the half-witness clause (gap 2, all-(2,2)).
    Both are habitat-GATED single-F-cycle O <= M pairs.  Pinned figures
    (M*, family, #pos, #neg, #bal, gap, min |h|)."""
    return [
        ('refut20', 20,
         [(15, 6), (13, 1), (17, 11), (18, 16), (7, 2), (5, 3), (9, 4),
          (0, 8)], [(10, 14), (12, 19)], (16, 64, 32, 32, 0, 4, 4)),
        ('clause20', 20,
         [(12, 16), (15, 5), (9, 7), (10, 19), (11, 1), (8, 3), (0, 13),
          (14, 18)], [(17, 4), (2, 6)], (16, 32, 16, 16, 0, 2, 4)),
    ]


def gate_general(n, cycles, chords, oj):
    """The habitat gate at ANY F-cycle type: every ell-placement with the
    two odd branches at ell in {3, 5}, every other branch at 2 or 4, and
    total excess 6 (Lambda = empty, so ell = 1 is excluded by
    convention), through the canonical cflank.cubic_habitat.  Returns
    (specs, mat) or None."""
    fed = []
    for cyc in cycles:
        L = len(cyc)
        for t in range(L):
            fed.append((cyc[t], cyc[(t + 1) % L]))
    med = list(chords)
    nb = len(fed) + len(med)
    oddpos = [len(fed) + j for j in oj]
    hedges = fed + med
    for (l1, l2) in ((3, 3), (3, 5), (5, 3), (5, 5)):
        need = 6 - ((l1 - 2) + (l2 - 2))
        if need < 0 or need % 2:
            continue
        others = [i for i in range(nb) if i not in oddpos]
        for combo in itertools.combinations(others, need // 2):
            lens = [2] * nb
            lens[oddpos[0]] = l1
            lens[oddpos[1]] = l2
            for c in combo:
                lens[c] = 4
            if cubic_habitat(n, hedges, lens):
                return ([(u, w, lens[i]) for i, (u, w) in enumerate(hedges)],
                        frozenset(range(len(fed), nb)))
    return None


def slide_test(n, cycles, mpairs, oddends, fam_sigmas):
    """(GR-121) tested at one pair: for every FORCING maximum with
    residency (2, 2), is there another maximum with the SAME SINK SET
    and an odd end freed?  By (GR-110)(ii) every configuration with a
    given sink set has |R| = 2|K|, so such a neighbour is exactly one
    (GR-110)(iii) source slide away and is automatically a maximum.
    Returns (n22, n_rescued)."""
    bysink = collections.defaultdict(list)
    for sig in fam_sigmas:
        K = frozenset(v for v in range(n) if sig[v] == 2)
        bysink[K].append(sig)
    n22 = nres = 0
    for sig in fam_sigmas:
        _e, _hs, _hk, _f0, resid, cls = budget_of(n, sig, mpairs, oddends)
        if cls == 'bal' or resid != (2, 2):
            continue
        n22 += 1
        K = frozenset(v for v in range(n) if sig[v] == 2)
        for other in bysink[K]:
            if budget_of(n, other, mpairs, oddends)[4] != (2, 2):
                nres += 1
                break
    return n22, nres


def cyc_types(n):
    """Every F-cycle type at n hubs (partitions of n into parts >= 2),
    realized as consecutive position blocks."""
    out = []

    def rec(rem, lo, acc):
        if rem == 0:
            cyc, t = [], 0
            for L in acc:
                cyc.append(list(range(t, t + L)))
                t += L
            out.append((tuple(acc), cyc))
            return
        for L in range(lo, rem + 1):
            if rem - L == 1:
                continue
            rec(rem - L, L, acc + [L])
    rec(n, 2, [])
    return out


def all_matchings(n):
    """Every perfect matching of 0..n-1 as a chord list (lowest
    unmatched point first -- each matching produced exactly once)."""
    pts = list(range(n))

    def rec(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for i in range(1, len(rest)):
            b = rest[i]
            sub = rest[1:i] + rest[i + 1:]
            for tail in rec(sub):
                yield [(a, b)] + tail
    return rec(pts)


def scan_matching(n, chords, SINK, SRC, RES, SZ, ALL, stats, cyctag,
                  hits):
    """Every odd-chord choice of one matching, with prefix/suffix AND
    sharing of the even-chord constraint sets."""
    m = len(chords)
    good = []
    for (a, b) in chords:
        good.append(ALL & ~((SINK[a] & SINK[b]) | (SRC[a] & SRC[b])))
    pre = [ALL] * (m + 1)
    for j in range(m):
        pre[j + 1] = pre[j] & good[j]
    suf = [ALL] * (m + 1)
    for j in range(m - 1, -1, -1):
        suf[j] = suf[j + 1] & good[j]
    for j in range(m - 1):
        for k in range(j + 1, m):
            mid = ALL
            for t in range(j + 1, k):
                mid &= good[t]
            ev = pre[j] & mid & suf[k + 1]
            (a1, b1) = chords[j]
            (a2, b2) = chords[k]
            aa = ev & ~SINK[a1] & ~SINK[b1] & ~SINK[a2] & ~SINK[b2]
            ab = ev & ~SINK[a1] & ~SINK[b1] & ~SRC[a2] & ~SRC[b2]
            m_aa = maxsize(aa, SZ, n)
            m_ab = maxsize(ab, SZ, n)
            mstar = m_aa if m_aa > m_ab else m_ab
            gap = m_aa - m_ab if m_aa > m_ab else 0
            stats['pairs'] += 1
            stats[f'gap_{gap}'] += 1
            if gap == 0:
                continue
            stats[f'dpar_{n - mstar}'] += 1
            full = RES[a1] & RES[b1] & RES[a2] & RES[b2]
            if (aa & SZ[mstar] & ~full) == 0:
                stats['ALL22'] += 1
                hits.append((cyctag, n, list(chords), (j, k), mstar, gap))
                print(f'    ** ALL-(2,2) HIT: n = {n}, cycles {cyctag}, '
                      f'chords = {chords}, odd = {(chords[j], chords[k])}, '
                      f'M* = {mstar}, GAP = {gap}')
            if gap >= 4:
                stats['GAP4'] += 1
                hits.append((cyctag, n, list(chords), (j, k), mstar, gap))
                print(f'    ** GAP-{gap} HIT ((GR-104)(i) REFUTATION): '
                      f'n = {n}, cycles {cyctag}, chords = {chords}, '
                      f'odd = {(chords[j], chords[k])}, M* = {mstar}')


# ------------------------------------------------- [GHW-1] --census ---------

def leg_census(args):
    """(GR-120)/(GR-121) asserted over the landed pools, and the min-|h|
    record that REFUTES the '|h| = 2' reduction."""
    t0 = time.time()
    print('  [GHW-1] --census: (GR-120) the (2,2) budget, (GR-121) the '
          'slide gate, and the min-|h| record')
    pools = []
    for (tag, n, specs) in stratum_cases():
        oidx, mats, _c = pairs_of(specs, n)
        for mat in mats:
            pools.append((f'stratum/{tag}', specs, n, mat, oidx))
    specs = v8_specs()
    oidx, mats, _c = pairs_of(specs, 8)
    for mat in mats:
        pools.append(('V8', specs, 8, mat, oidx))
    rng = random.Random(R_SEED)
    print(f'    pool seed {R_SEED}')
    for n in (12, 14):
        for (sp, mt) in cell_shapes(n, 2, 60, rng):
            pools.append((f'cell{n}', sp, n, mt, odd_idx(sp)))
    nconf = ncell = tot22 = totres = 0
    resid_hist = collections.Counter()
    budget_hist = collections.Counter()
    for (tag, sp, n, mat, oidx) in pools:
        if len(oidx) != 2:
            continue
        cycles, mpairs, oddends = cell_data(sp, n, mat, oidx)
        pe, ne = hub_edges(cycles)
        f = rmodel_f(n, cycles, mpairs, oddends)
        dpar = min(f.values())
        ncell += 1
        fam = []
        for w in range(1 << n):
            sig = sigma_of_word(n, w, pe, ne)
            ok = True
            for (a, b) in mpairs:
                if sig[a] and sig[b] and sig[a] == sig[b]:
                    ok = False
                    break
            if ok:
                for (a, b) in oddends:
                    if sig[a] and sig[b] and sig[a] != sig[b]:
                        ok = False
                        break
            if not ok:
                continue
            dist = n - sum(1 for v in range(n) if sig[v])
            if dist != dpar:
                continue
            e_f, h_s, h_k, f_0, resid, cls = budget_assert(
                n, sig, mpairs, oddends, dist)
            nconf += 1
            fam.append(sig)
            resid_hist[(cls, resid)] += 1
            if cls in ('pos', 'neg') and resid == (2, 2):
                budget_hist[(n, e_f, min(h_s, h_k), f_0, dist)] += 1
        s22, sres = slide_test(n, cycles, mpairs, oddends, fam)
        tot22 += s22
        totres += sres
    print(f'    (GR-120) asserted at {nconf} MAXIMA over {ncell} O<=M pairs '
          f'(2k = 2); residency x class {dict(sorted(resid_hist.items(), key=str))}')
    print(f'    (2,2) forcing maxima seen (n, e_f, h_s, f_0, dist): '
          f'{dict(sorted(budget_hist.items()))}')
    print(f'    (GR-121) slide gate: {totres} of {tot22} (2,2) forcing '
          f'maxima have a SAME-SINK-SET maximum with an odd end freed '
          f'(one (GR-110)(iii) source slide)')

    # --- the |h| = 2 reduction, REFUTED at the landed rand20b witness ----
    print('    the "some maximum has |h| = 2" reduction, at the four '
          '(GR-116) witnesses:')
    for (tag, n, ech, gch, pinned) in refut_specs():
        mstar, N, cnt, nclosed, minh, gap, all22 = word_census(n, ech, gch)
        assert (mstar, N, cnt['pos'], cnt['neg'], cnt['bal'], gap, minh) == \
            pinned, 'landed (GR-116) figure not reproduced'
        rh = collections.Counter()
        for w in range(1 << n):
            rot = (w >> 1) | ((w & 1) << (n - 1))
            if bin(w ^ rot).count('1') != mstar:
                continue
            if not word_valid(w, n, ech, gch):
                continue
            cls, h, closed, gres = word_stats(w, n, ech, gch)
            rh[(cls, gres, h)] += 1
        pe = {v: (v - 1) % n for v in range(n)}
        ne = {v: v for v in range(n)}
        fam = []
        for w in range(1 << n):
            rot = (w >> 1) | ((w & 1) << (n - 1))
            if bin(w ^ rot).count('1') != mstar:
                continue
            if word_valid(w, n, ech, gch):
                fam.append(sigma_of_word(n, w, pe, ne))
        s22, sres = slide_test(n, [list(range(n))], list(ech), list(gch),
                               fam)
        flag = 'REDUCTION FAILS HERE' if minh > 2 else 'has an |h| = 2 maximum'
        print(f'      {tag}: min |h| = {minh}  ({flag}); slide gate '
              f'{sres}/{s22} (2,2) maxima rescued; '
              f'(class, residency, h) profile '
              f'{dict(sorted(rh.items(), key=str))}')
    print(f'  leg census OK  [{time.time() - t0:.0f}s]')


# ---------------------------------------------------- [GHW-2] --exh ---------

def leg_exh(args):
    """The EXHAUSTIVE ungated diagram sweep."""
    t0 = time.time()
    print('  [GHW-2] --exh: EXHAUSTIVE over ALL chord diagrams, UNGATED '
          '(a superset of the habitat-gated pairs)')
    hits = []
    for n in (4, 6, 8, 10, 12):
        stats = collections.Counter()
        types = cyc_types(n)
        for (tag, cycles) in types:
            SINK, SRC, RES, SZ, ALL = word_bitsets(n, cycles)
            for chords in all_matchings(n):
                scan_matching(n, chords, SINK, SRC, RES, SZ, ALL, stats,
                              tag, hits)
        gaps = {int(k[4:]): v for k, v in stats.items()
                if k.startswith('gap_')}
        dps = {int(k[5:]): v for k, v in stats.items()
               if k.startswith('dpar_')}
        print(f'    n = {n}: {len(types)} F-cycle types, {stats["pairs"]} '
              f'(diagram, odd-pair) instances; gap histogram '
              f'{dict(sorted(gaps.items()))}; d_par at the gap > 0 '
              f'instances {dict(sorted(dps.items()))}; all-(2,2) '
              f'{stats["ALL22"]}; gap >= 4 {stats["GAP4"]}  '
              f'[{time.time() - t0:.0f}s]')
    for n in (14,):
        stats = collections.Counter()
        cycles = [list(range(n))]
        SINK, SRC, RES, SZ, ALL = word_bitsets(n, cycles)
        for chords in all_matchings(n):
            scan_matching(n, chords, SINK, SRC, RES, SZ, ALL, stats,
                          (n,), hits)
        gaps = {int(k[4:]): v for k, v in stats.items()
                if k.startswith('gap_')}
        dps = {int(k[5:]): v for k, v in stats.items()
               if k.startswith('dpar_')}
        print(f'    n = {n} SINGLE F-CYCLE only: {stats["pairs"]} instances; '
              f'gap histogram {dict(sorted(gaps.items()))}; d_par at the '
              f'gap > 0 instances {dict(sorted(dps.items()))}; all-(2,2) '
              f'{stats["ALL22"]}; gap >= 4 {stats["GAP4"]}  '
              f'[{time.time() - t0:.0f}s]')
    print(f'    total all-(2,2) hits {len([h for h in hits])}')

    # ---- CAPPED legs (caps disclosed; an exhausted cap is not emptiness) --
    rng = random.Random(R_SEED)
    print(f'    capped legs (seed {R_SEED}; an exhausted cap is NOT '
          f'nonexistence):')
    for (n, only_single, tries) in ((14, False, args.cap),
                                    (16, True, args.cap)):
        stats = collections.Counter()
        types = ([([list(range(n))], (n,))] if only_single
                 else [(c, t) for (t, c) in cyc_types(n)])
        for (cycles, tag) in types:
            SINK, SRC, RES, SZ, ALL = word_bitsets(n, cycles)
            for _t in range(tries):
                pl = list(range(n))
                rng.shuffle(pl)
                chords = [(pl[2 * i], pl[2 * i + 1]) for i in range(n // 2)]
                scan_matching(n, chords, SINK, SRC, RES, SZ, ALL, stats,
                              tag, hits)
        gaps = {int(k[4:]): v for k, v in stats.items()
                if k.startswith('gap_')}
        dps = {int(k[5:]): v for k, v in stats.items()
               if k.startswith('dpar_')}
        lab = 'SINGLE F-cycle' if only_single else f'{len(types)} F-cycle types'
        print(f'      n = {n} ({lab}), {tries} random matchings per type: '
              f'{stats["pairs"]} instances; gap histogram '
              f'{dict(sorted(gaps.items()))}; d_par at gap > 0 '
              f'{dict(sorted(dps.items()))}; all-(2,2) {stats["ALL22"]}; '
              f'gap >= 4 {stats["GAP4"]}  [{time.time() - t0:.0f}s]')

    # ---- the UNGATED disclosure: how many gap-2 instances are habitats? ---
    print('    UNGATED disclosure -- the sweep runs the raw (GR-106) model, '
          'a SUPERSET of the habitat-gated pairs (so the emptiness claims '
          'are stronger, but the gap histograms are NOT the landed gated '
          'population).  Sample of single-F-cycle gap-2 instances through '
          "the landed specs_of_diagram recipe:")
    for n in (10, 12, 14):
        cycles = [list(range(n))]
        SINK, SRC, RES, SZ, ALL = word_bitsets(n, cycles)
        seen = ngate = 0
        for chords in all_matchings(n):
            if seen >= args.gatecap:
                break
            m = len(chords)
            for j in range(m - 1):
                for k in range(j + 1, m):
                    if seen >= args.gatecap:
                        break
                    r = scan_one(n, chords, (j, k), SINK, SRC, RES, SZ, ALL)
                    if r[1] == 0:
                        continue
                    seen += 1
                    ech = [c for t, c in enumerate(chords) if t not in (j, k)]
                    gch = [chords[j], chords[k]]
                    if any((a - b) % n in (1, n - 1) for (a, b) in chords):
                        continue
                    if specs_of_diagram(n, ech, gch) is not None:
                        ngate += 1
        print(f'      n = {n}: {ngate} of the first {seen} single-cycle '
              f'gap-2 instances pass the gate')
    print(f'  leg exh OK  [{time.time() - t0:.0f}s]')


# -------------------------------------------------- [GHW-3] --build ---------

def scan_one(n, chords, oj, SINK, SRC, RES, SZ, ALL):
    """(M*, gap, n22, nmax) of one instance -- n22 = the number of maxima
    with residency (2, 2), so n22 = nmax is the (GR-117)(iii) open case."""
    ev = ALL
    for j, (a, b) in enumerate(chords):
        if j in oj:
            continue
        ev &= ~((SINK[a] & SINK[b]) | (SRC[a] & SRC[b]))
    (a1, b1) = chords[oj[0]]
    (a2, b2) = chords[oj[1]]
    aa = ev & ~SINK[a1] & ~SINK[b1] & ~SINK[a2] & ~SINK[b2]
    ab = ev & ~SINK[a1] & ~SINK[b1] & ~SRC[a2] & ~SRC[b2]
    m_aa = maxsize(aa, SZ, n)
    m_ab = maxsize(ab, SZ, n)
    mstar = m_aa if m_aa > m_ab else m_ab
    gap = m_aa - m_ab if m_aa > m_ab else 0
    if gap == 0:
        return mstar, 0, 0, 0
    fam = aa & SZ[mstar]
    full = RES[a1] & RES[b1] & RES[a2] & RES[b2]
    return mstar, gap, bin(fam & full).count('1'), bin(fam).count('1')


def transpositions(n, chords):
    """Every 2-chord endpoint transposition of a diagram (both swap
    variants per chord pair), F-parallels excluded."""
    m = len(chords)
    for i in range(m - 1):
        for j in range(i + 1, m):
            (a, b), (c, d) = chords[i], chords[j]
            for (p1, p2) in (((a, c), (b, d)), ((a, d), (b, c))):
                if (p1[0] - p1[1]) % n in (1, n - 1):
                    continue
                if (p2[0] - p2[1]) % n in (1, n - 1):
                    continue
                cc = list(chords)
                cc[i], cc[j] = p1, p2
                yield (i, j), cc


def leg_build(args):
    """The budget-targeted hunt: the FULL transposition neighbourhood of
    each landed (GR-116) witness, then a guided climb on the (2,2)
    fraction from seeded single-cycle starts."""
    t0 = time.time()
    print('  [GHW-3] --build: the (2,2)-fraction hunt (a NEW objective -- '
          'the landed hunt counted all22, this one CLIMBS toward it)')
    tabs = {}

    def tab(n):
        if n not in tabs:
            tabs[n] = word_bitsets(n, [list(range(n))])
        return tabs[n]

    print('    (i) the full 2-chord transposition neighbourhood of each '
          '(GR-116) witness (NEW pairs -- the landed leg mutated the '
          '(GR-113) diagram, not these):')
    for (tag, n, ech, gch, _p) in refut_specs():
        SINK, SRC, RES, SZ, ALL = tab(n)
        chords = list(ech) + list(gch)
        oj = (len(chords) - 2, len(chords) - 1)
        base = scan_one(n, chords, oj, SINK, SRC, RES, SZ, ALL)
        st = collections.Counter()
        best = 0.0
        ngate = 0
        for (_ij, cc) in transpositions(n, chords):
            r = scan_one(n, cc, oj, SINK, SRC, RES, SZ, ALL)
            st[f'gap_{r[1]}'] += 1
            if r[1] > 0:
                frac = r[2] / r[3]
                best = max(best, frac)
                if r[2] == r[3]:
                    st['ALL22'] += 1
                    got = specs_of_diagram(n, cc[:len(ech)], cc[len(ech):])
                    ngate += 1 if got is not None else 0
                    print(f'      ** ALL-(2,2) HIT off {tag}: chords {cc}, '
                          f'M* = {r[0]}, GAP = {r[1]}, '
                          f'habitat-gated: {got is not None}')
            if r[1] >= 4:
                print(f'      ** GAP-{r[1]} HIT off {tag}: chords {cc}')
        gaps = {int(k[4:]): v for k, v in st.items() if k.startswith('gap_')}
        print(f'      {tag} (n = {n}, base M* = {base[0]}, gap {base[1]}, '
              f'(2,2)-fraction {base[2]}/{base[3]}): '
              f'{sum(gaps.values())} transpositions, gap histogram '
              f'{dict(sorted(gaps.items()))}, best (2,2)-fraction '
              f'{best}, all-(2,2) {st["ALL22"]}  [{time.time() - t0:.0f}s]')

    print(f'    (ii) the guided climb (seed {R_SEED}); score = the (2,2) '
          'fraction of the maximum family at a gap > 0 pair, -1 otherwise:')
    rng = random.Random(R_SEED)
    for n in (12, 14, 16, 18, 20):
        SINK, SRC, RES, SZ, ALL = tab(n)
        m = n // 2
        bestall = 0.0
        nstart = 0
        nhit = 0
        ngated = 0
        for _s in range(args.starts):
            pl = list(range(n))
            rng.shuffle(pl)
            chords = []
            ok = True
            while pl:
                x = pl.pop()
                cands = [y for y in pl if (x - y) % n not in (1, n - 1)]
                if not cands:
                    ok = False
                    break
                y = rng.choice(cands)
                pl.remove(y)
                chords.append((x, y))
            if not ok:
                continue
            if nhit >= args.hitcap:
                break
            nstart += 1
            oj = (m - 2, m - 1)
            cur = scan_one(n, chords, oj, SINK, SRC, RES, SZ, ALL)
            score = cur[2] / cur[3] if cur[1] > 0 else -1.0
            for _step in range(args.steps):
                cands = []
                for (_ij, cc) in transpositions(n, chords):
                    r = scan_one(n, cc, oj, SINK, SRC, RES, SZ, ALL)
                    sc = r[2] / r[3] if r[1] > 0 else -1.0
                    if sc >= score:
                        cands.append((sc, cc, r))
                up = [c for c in cands if c[0] > score]
                pick = rng.choice(up) if up else (rng.choice(cands)
                                                  if cands else None)
                if pick is None:
                    break
                score, chords, cur = pick[0], pick[1], pick[2]
                bestall = max(bestall, score)
                if score >= 1.0 or cur[1] >= 4:
                    nhit += 1
                    ech = [c for t, c in enumerate(chords) if t not in oj]
                    gch = [chords[oj[0]], chords[oj[1]]]
                    g = specs_of_diagram(n, ech, gch)
                    if g is not None:
                        ngated += 1
                    kind = ('ALL-(2,2) + GAP-4 ((GR-104)(i) REFUTATION)'
                            if cur[1] >= 4 else 'ALL-(2,2)')
                    print(f'      ** {kind} HIT at n = {n}: chords '
                          f'{chords}, odd {(chords[oj[0]], chords[oj[1]])}, '
                          f'M* = {cur[0]}, GAP = {cur[1]}, habitat-gated '
                          f'{g is not None}')
                    break
            bestall = max(bestall, score)
        print(f'      n = {n}: {nstart} starts x <= {args.steps} steps; '
              f'best (2,2) fraction reached {bestall}; all-(2,2)/gap-4 '
              f'hits {nhit} ({ngated} habitat-gated)  '
              f'[{time.time() - t0:.0f}s]')
    print(f'  leg build OK  [{time.time() - t0:.0f}s]')


# ------------------------------------------------- [GHW-4] --verify ---------

def leg_verify(args):
    """The pinned n = 12 (GR-108) and n = 20 (GR-104)(i) refutation
    witnesses through FOUR independent exact models, and the n <= 10
    habitat-gate exhaustion that makes the (GR-108) boundary EXACT."""
    t0 = time.time()
    print('  [GHW-4] --verify: the pinned witnesses through FOUR '
          'independent exact models, and the exact (GR-108) boundary')
    for (tag, n, ech, gch, pinned) in n12_specs() + n20_specs():
        # model 1 -- the landed gxesc single-cycle orientation-word census
        cen = word_census(n, ech, gch)
        mstar, N, cnt, nclosed, minh, gap, all22 = cen
        assert (mstar, N, cnt['pos'], cnt['neg'], cnt['bal'], gap, minh) == \
            pinned, f'{tag}: word-model figures moved'
        assert cnt['bal'] == 0, f'{tag}: not a (GR-108) refutation'
        # model 2 -- this pass's bitset model
        chords = list(ech) + list(gch)
        oj = (len(chords) - 2, len(chords) - 1)
        B = word_bitsets(n, [list(range(n))])
        r = scan_one(n, chords, oj, *B)
        assert (r[0], r[1]) == (mstar, gap), f'{tag}: bitset model disagrees'
        # model 3 -- the LANDED gprice (GR-106) reversal-set model, on the
        # habitat-gated shape rebuilt by the landed specs_of_diagram recipe
        got = specs_of_diagram(n, ech, gch)
        assert got is not None, f'{tag}: the landed habitat recipe rejects it'
        specs, mat = got
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        assert cubic_habitat(n, hedges, lens), f'{tag}: not a habitat'
        oidx = odd_idx(specs)
        assert len(oidx) == 2 and set(oidx) <= set(mat), \
            f'{tag}: not an O <= M, 2k = 2 pair'
        cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
        assert len(cycles) == 1, f'{tag}: 2-factor is not a single cycle'
        f = rmodel_f(n, cycles, mpairs, oddends)
        assert f[0] == f[3] and f[1] == f[2], f'{tag}: (GR-105) broken'
        assert min(f.values()) == n - mstar and \
            f[1] - min(f.values()) == gap, f'{tag}: rmodel f disagrees'
        if n == 12:
            assert r[2] < r[3], f'{tag}: all-(2,2) after all'
            assert gap == 2, f'{tag}: gap moved'
        else:
            assert r[2] == r[3], f'{tag}: NOT all-(2,2)'
            assert cen[6], f'{tag}: word census disagrees on all22'
            assert minh == 4, f'{tag}: min |h| moved'
        # model 4 -- the self-contained brute force (no project device)
        nb, nms, nfam, nprof = naive_family(n, ech, gch)
        assert nms == mstar, f'{tag}: model 4 disagrees on M*'
        assert nfam == N, f'{tag}: model 4 disagrees on the family size'
        assert (n - nb['AA'], n - nb['AB'], n - nb['BA'], n - nb['BB']) == \
            (f[0], f[1], f[2], f[3]), f'{tag}: model 4 f-table disagrees'
        assert nb['AA'] - nb['AB'] == gap if gap else nb['AA'] == nb['AB'], \
            f'{tag}: model 4 gap disagrees'
        n22naive = sum(c for (k, c) in nprof.items() if k[1] == (2, 2)
                       and k[0] != 'bal')
        assert (n22naive == nfam) == (r[2] == r[3]), \
            f'{tag}: model 4 disagrees on all-(2,2)'
        verdict = ('(GR-117)(iii) HOLDS' if r[2] < r[3] else
                   ('(GR-117)(iii) REFUTED + (GR-117)(i) and (GR-104)(i) '
                    'REFUTED' if gap >= 4 else '(GR-117)(iii) REFUTED'))
        print(f'    {tag}: n = {n}, single F-cycle, habitat-GATED; '
              f'even chords {ech}, odd chords {gch}; M* = {mstar}, family '
              f'{N} = {cnt["pos"]} pos + {cnt["neg"]} neg + 0 bal, '
              f'GAP = {gap}, min |h| = {minh}; rmodel f = {f}; '
              f'(2,2) maxima {r[2]}/{r[3]} -- {verdict}')
        print(f'      model 4 (self-contained, no project device): '
              f'max |R| per pattern (AA, AB, BA, BB) = '
              f'({nb["AA"]}, {nb["AB"]}, {nb["BA"]}, {nb["BB"]}), '
              f'family {nfam}, profile '
              f'{dict(sorted(nprof.items(), key=str))}')
        print(f'      specs = {specs}, mat = {sorted(mat)}, oidx = {oidx}')
    print('    => (GR-108) is FALSE at n = 12, NOT first at n = 16: '
          '(GR-116)(iv) BOUNDARY REFUTED (gap 2 there, so (GR-104)(i) '
          'survives at the n = 12 witnesses).')
    print('    => at n = 20, refut20 has GAP 4 with an ALL-(2,2) maximum '
          'family: the half-witness clause (GR-117)(iii), the gap-2 law '
          '(GR-117)(i) and (GR-104)(i) at 2k = 2 are ALL REFUTED.')
    for n in (8, 10):
        ninst = ngap = ngate = 0
        for (tag, cycles) in cyc_types(n):
            B = word_bitsets(n, cycles)
            for chords in all_matchings(n):
                m = len(chords)
                for j in range(m - 1):
                    for k in range(j + 1, m):
                        ninst += 1
                        r = scan_one(n, chords, (j, k), *B)
                        if r[1] == 0:
                            continue
                        ngap += 1
                        if gate_general(n, cycles, chords, (j, k)) is not None:
                            ngate += 1
                            print(f'      ** GATED gap-{r[1]} pair at n = {n}: '
                                  f'cycles {tag}, chords {chords}, '
                                  f'odd {(chords[j], chords[k])}')
        print(f'    n = {n}: EXHAUSTIVE over every F-cycle type and every '
              f'chord diagram -- {ninst} instances, {ngap} with gap > 0, '
              f'{ngate} of those habitat-realizable (every ell-placement '
              f'tried, Lambda = empty)')
    print(f'  leg verify OK  [{time.time() - t0:.0f}s]')


# ------------------------------------------------------------ main ----------

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--census', action='store_true')
    ap.add_argument('--exh', action='store_true')
    ap.add_argument('--build', action='store_true')
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--validate', action='store_true')
    ap.add_argument('--starts', type=int, default=80)
    ap.add_argument('--steps', type=int, default=40)
    ap.add_argument('--cap', type=int, default=3000)
    ap.add_argument('--gatecap', type=int, default=120)
    ap.add_argument('--hitcap', type=int, default=12)
    args = ap.parse_args()
    if args.validate:
        args.census = args.exh = args.build = args.verify = True
    if not (args.census or args.exh or args.build or args.verify):
        ap.error('pick a mode')
    t0 = time.time()
    print('GHWIT -- the half-witness clause (GR-117)(iii)')
    if args.verify:
        leg_verify(args)
    if args.census:
        leg_census(args)
    if args.exh:
        leg_exh(args)
    if args.build:
        leg_build(args)
    print(f'ALL LEGS OK  [{time.time() - t0:.0f}s]')


if __name__ == '__main__':
    main()
