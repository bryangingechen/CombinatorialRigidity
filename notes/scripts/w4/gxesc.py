"""GXESC -- the thirty-fifth kernel-(K) ordinal: existential escape /
(GR-108) by global construction (spec: notes/Pencil-fanout.md S"GXESC").

TARGET: (GR-112)(v)'s hypothesis -- existential escape -- or an
unconditional proof of (GR-108), or a refutation by witness (S(K-grid)
Steps G132-G134).  OUTCOME: a REFUTATION BY WITNESS, plus a proven
ledger and a reshaped two-line residual:

  (GR-115) THE REVERSAL-LABEL LEDGER (proven).  Score every reversal
  hub +1 (source) / -1 (sink).  Per-cycle alternation makes every
  F-cycle's score 0; a fully-resident even matching pair scores 0
  (its labels differ); a fully-resident odd branch scores +-2 (its
  labels agree).  Hence, for EVERY valid configuration at EVERY
  O <= M pair:
      sum_j c_j  +  h  =  0,
  where c_j is odd branch j's resident-end score (in {-2..2}) and h is
  the EVEN-HALF LEDGER -- the score of the resident hubs whose even
  matching partner is through.  Corollaries, all proven:
    (i)   M-CLOSED (no half branch at all) => equally many forced-A
          and forced-B branches, an even free count, and the
          configuration is BALANCE-VALID -- at EVERY 2k;
    (ii)  at 2k = 2: |h| <= 1  =>  balance-valid;
    (iii) at 2k = 2: pos-forcing  =>  h <= -2, with h = -2 forcing
          BOTH odd branches half-resident.
  (--ledger asserts the clauses EXHAUSTIVELY over all 3^n labeled
  states on the n <= 6 stratum, over every valid orientation word of
  the (GR-113) witness, and over the labeled maximum families of V8 +
  the (GR-103) control.)

  (GR-116) THE BALANCE LAW (GR-108) IS REFUTED -- and existential
  escape with it.  Four explicit single-F-cycle O <= M, 2k = 2
  habitat pairs (two at n = 16, two at n = 20; refut_specs) have
  maximum families that are pure pos + neg with NO balance-valid
  member (gap d_adm - d_par = 2), so no fine-move walk can leave the
  pos class ((GR-112)(iv)).  The first, mut16, is ONE 2-chord
  endpoint transposition away from the (GR-113) witness diagram.
  (--hunt finds them; --verify re-derives every pinned figure through
  THREE independent models -- the word census, the landed
  gprice.rmodel_f, and (n = 16) the landed gblaw.enum_family.)

  (GR-117) THE GAP-2 LAW (the reshaped residual).  At 2k = 2, O <= M,
  the price form (GR-104)(i) is EXACTLY the statement
      d_adm(M) <= d_par(M) + 2,
  and it SURVIVES at all four witnesses (both one-flip prices +2).
  PROVEN whenever some maximum is balance-valid or has a
  half-resident odd branch (remove the (GR-107)(v) adjacent pair at
  the lone resident end: a balance-valid configuration at M* - 2).
  The one open case -- EVERY maximum forcing with both branches fully
  resident -- is measured EMPTY at all 248 hunted single-cycle pairs
  (--hunt's all22 counter), and a gap >= 4 pair (a price-form
  refutation) would have to live there; none found.

  Also measured: the M-closure coverage (--closure: how often the
  maximum family contains an M-closed => balance-valid member; the
  closed gap M* - M*_cl in {0, 2, 4} everywhere swept), and the
  (GR-113) witness anatomy (--strand: escaper vs stranded features,
  and the DIP CENSUS -- under interval flips through configurations
  of size >= M* - 2 the witness's 32 stranded maxima ALL reach
  balance-valid company, so the strandedness is an artifact of the
  L1-L3 move set, not of the dip depth).

Modes:
  --ledger   (GR-115) asserted (see above).
  --closure  the coverage sweep + the closed-gap histogram.
  --hunt     the single-cycle hunt at n = 12/14/16/18/20 + the witness
             2-chord transposition neighborhood: gap histograms,
             (GR-108) refutations, price-form refutations (gap >= 4),
             all-(2,2) pairs.
  --verify   the four pinned refutation witnesses, every figure
             asserted through the three models.
  --strand   the (GR-113) witness anatomy + the dip census.
  --validate all five.

Sibling imports (S2 rule-2 trips, DISCLOSED -- extending the recorded
GBLAW *Harness debt* item's consumer lists; the move is the
coordinator's, not this dispatch's): `cell_data`, `cell_shapes`,
`gr103_specs`, `pairs_of` from `w4/gprice.py` (third consumer) and
`cls_of`, `enum_family`, `safeflips`, `slides`, `strand_witness`,
`teleports`, `valid_pats` from `w4/gblaw.py` (second consumer), all
read-only.  Balance-layer devices
come DIRECTLY from gridbal_common, never via the sibling re-exports.

Rank-free throughout: gexist.fully_good_rank is never imported or
called and no d_fg claim is made anywhere ((a') / input (Y) untouched).
Exact integers / GF(2); no floating point; every rng seeded, seed
printed; every sampler draws a GRAPH, never a placement (S(K-clos)
(AC-9)).  Wall-clock [Ns] annotations are non-deterministic; every
other byte is seed-stable.
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
from gprice import (cell_data, cell_shapes, gr103_specs, pairs_of,    # noqa: E402
                    rmodel_f)
from gblaw import (cls_of, enum_family, safeflips, slides,            # noqa: E402
                   strand_witness, teleports, valid_pats)
from cflank import cubic_habitat                                      # noqa: E402

R_SEED = 20260826


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  `ledger_of` computes the
# (GR-115) ledger of one labeled configuration; `ledger_assert` asserts
# the theorem's clauses at one configuration; `closed_mstar` the maximum
# over M-CLOSED configurations by chord-subset enumeration; the
# `word_*` devices are a fast SINGLE-CYCLE census in the orientation-
# word model (word bit t = the edge position t -> t+1 directed forward;
# hub t is a reversal hub iff bits t-1 and t differ, a SINK iff they
# are (1, 0)); `cyc_sample` the single-cycle pair sampler;
# `witness_mutations` the 2-chord endpoint transpositions of the
# (GR-113) witness diagram; `dip_census` the interval-flip graph
# through valid words of size >= M* - d.


def lab_val(s):
    """+1 for a source (state 1), -1 for a sink (state 2)."""
    return 1 if s == 1 else -1


def ledger_of(sigma, mpairs, oddends):
    """(GR-115) at one labeled configuration: (gparts, h, mclosed)
    with gparts[j] = odd branch j's resident-end score, h = the
    even-half ledger, mclosed = no branch (even or odd) half-resident."""
    gparts = []
    ghalf = 0
    for (u, w) in oddends:
        gparts.append(sum(lab_val(sigma[v]) for v in (u, w) if sigma[v]))
        if bool(sigma[u]) != bool(sigma[w]):
            ghalf += 1
    h = 0
    ehalf = 0
    for (a, b) in mpairs:
        ra, rb = bool(sigma[a]), bool(sigma[b])
        if ra != rb:
            ehalf += 1
            h += lab_val(sigma[a] if ra else sigma[b])
    return gparts, h, (ehalf == 0 and ghalf == 0)


def ledger_assert(sigma, pats, k2, cycles, mpairs, oddends):
    """The (GR-115) clauses at one valid configuration (pats = its
    valid patterns).  Returns (gparts, h, mclosed)."""
    for cyc in cycles:
        assert sum(lab_val(sigma[v]) for v in cyc if sigma[v]) == 0, \
            '(GR-115) per-cycle score != 0'
    gparts, h, mclosed = ledger_of(sigma, mpairs, oddends)
    assert sum(gparts) + h == 0, '(GR-115) ledger identity violated'
    cls = cls_of(pats, k2)
    if mclosed:
        assert all(c in (-2, 0, 2) for c in gparts), \
            '(GR-115)(i) a half odd branch in an M-closed configuration'
        assert sum(1 for c in gparts if c == 2) == \
            sum(1 for c in gparts if c == -2), \
            '(GR-115)(i) forced-A/forced-B counts differ when M-closed'
        assert cls == 'bal', '(GR-115)(i) M-closed configuration not bal'
    if k2 == 2:
        if abs(h) <= 1:
            assert cls == 'bal', '(GR-115)(ii) |h| <= 1 but not bal'
        if cls == 'pos':
            assert all(c > 0 for c in gparts) and h <= -2, \
                '(GR-115)(iii) pos-forcing without sink surplus'
            if h == -2:
                assert gparts == [1, 1], \
                    '(GR-115)(iii) h = -2 without two half branches'
        if cls == 'neg':
            assert all(c < 0 for c in gparts) and h >= 2, \
                '(GR-115)(iii) neg-forcing without source surplus'
    return gparts, h, mclosed


def closed_mstar(n, cycles, mpairs, oddends):
    """max |R| over M-CLOSED valid configurations: enumerate matching-
    branch subsets (2^{n/2}); each induces R = its hub union, checked
    by per-cycle parity + a typed 2-colouring (cyclic adjacency and
    full even pairs DIFFER, full odd pairs AGREE)."""
    chords = [(a, b, 1) for (a, b) in mpairs] + \
        [(u, w, 0) for (u, w) in oddends]
    m = len(chords)
    best = 0
    for bits in range(1, 1 << m):
        hubs = set()
        edges = []
        for j in range(m):
            if (bits >> j) & 1:
                (a, b, rel) = chords[j]
                hubs.add(a)
                hubs.add(b)
                edges.append((a, b, rel))
        if len(hubs) <= best:
            continue
        ok = True
        for cyc in cycles:
            mem = [v for v in cyc if v in hubs]
            L = len(mem)
            if L % 2:
                ok = False
                break
            for t in range(L):
                if L == 2 and t == 1:
                    break
                if L >= 2:
                    edges.append((mem[t], mem[(t + 1) % L], 1))
        if not ok:
            continue
        adj = collections.defaultdict(list)
        for (a, b, rel) in edges:
            adj[a].append((b, rel))
            adj[b].append((a, rel))
        klass = {}
        for s in hubs:
            if s in klass:
                continue
            klass[s] = 0
            stack = [s]
            while stack and ok:
                a = stack.pop()
                for (b, rel) in adj[a]:
                    want = klass[a] ^ rel
                    if b not in klass:
                        klass[b] = want
                        stack.append(b)
                    elif klass[b] != want:
                        ok = False
                        break
            if not ok:
                break
        if ok:
            best = max(best, len(hubs))
    return best


# ----------------------------------------------- the single-cycle word model


def word_valid(w, n, ech, gch):
    """Validity of one orientation word on the positional n-cycle:
    resident(p) iff bits p-1, p differ; a resident hub is a sink iff
    bit p-1 = 1; full even chords must mix, full odd chords agree."""
    for (a, b) in ech:
        xa = (w >> ((a - 1) % n)) & 1
        if xa == ((w >> a) & 1):
            continue
        xb = (w >> ((b - 1) % n)) & 1
        if xb == ((w >> b) & 1):
            continue
        if xa == xb:
            return False
    for (a, b) in gch:
        xa = (w >> ((a - 1) % n)) & 1
        if xa == ((w >> a) & 1):
            continue
        xb = (w >> ((b - 1) % n)) & 1
        if xb == ((w >> b) & 1):
            continue
        if xa != xb:
            return False
    return True


def word_stats(w, n, ech, gch):
    """(class at 2k = 2, even-half ledger h, M-closed, residency) of
    one valid word, residency = the sorted per-odd-branch resident-end
    counts.  Label convention: bit p-1 = 1 at a resident hub means
    SINK (score -1); = 0 means SOURCE (score +1)."""
    gstate = []
    gres = []
    closed = True
    for (a, b) in gch:
        labs = set()
        res = 0
        for p in (a, b):
            xp = (w >> ((p - 1) % n)) & 1
            if xp != ((w >> p) & 1):
                labs.add(xp)
                res += 1
        if res == 1:
            closed = False
        gres.append(res)
        gstate.append(None if not labs else labs.pop())
    if gstate and all(s == 0 for s in gstate):
        cls = 'pos'
    elif gstate and all(s == 1 for s in gstate):
        cls = 'neg'
    else:
        cls = 'bal'
    h = 0
    for (a, b) in ech:
        ra = ((w >> ((a - 1) % n)) & 1) != ((w >> a) & 1)
        rb = ((w >> ((b - 1) % n)) & 1) != ((w >> b) & 1)
        if ra != rb:
            closed = False
            p = a if ra else b
            h += 1 if ((w >> ((p - 1) % n)) & 1) == 0 else -1
    return cls, h, closed, tuple(sorted(gres))


def word_census(n, ech, gch):
    """The labeled maximum family of one single-cycle pair by word
    enumeration: (mstar, N, class counter, #M-closed maxima, min |h|
    over maxima, gap, all22) -- gap = M* - max size over BAL-class
    words = d_adm - d_par ((GR-106)'s dist identity), and all22 = every
    maximum is forcing with both odd branches fully resident (the
    (GR-116) hard case; a gap >= 4 requires it)."""
    mstar = -1
    mbal = 0           # R = empty is valid and bal at every pair
    fam = []
    for w in range(1 << n):
        rot = (w >> 1) | ((w & 1) << (n - 1))
        size = bin(w ^ rot).count('1')
        if size < mstar and size <= mbal:
            continue
        if not word_valid(w, n, ech, gch):
            continue
        cls = word_stats(w, n, ech, gch)[0]
        if cls == 'bal' and size > mbal:
            mbal = size
        if size < mstar:
            continue
        if size > mstar:
            mstar, fam = size, []
        fam.append(w)
    if mstar == 0:
        fam = [0]          # the two constant words are ONE empty config
    cnt = collections.Counter()
    nclosed = 0
    minh = None
    all22 = True
    for w in fam:
        cls, h, closed, gres = word_stats(w, n, ech, gch)
        cnt[cls] += 1
        nclosed += 1 if closed else 0
        minh = abs(h) if minh is None else min(minh, abs(h))
        if cls == 'bal' or gres != (2, 2):
            all22 = False
    assert cnt['pos'] == cnt['neg'], 'colour-swap symmetry lost (GR-105)'
    gap = mstar - mbal
    assert gap >= 0 and gap % 2 == 0, 'gap parity broken'
    assert (gap == 0) == (cnt['bal'] > 0), 'gap vs bal-count inconsistency'
    return mstar, len(fam), cnt, nclosed, minh, gap, all22


def specs_of_diagram(n, ech, gch):
    """Rebuild a habitat-shaped spec list from a positional single-
    cycle diagram (cycle edges ell = 2, odd chords ell = 3, and the
    excess topped to 6 by two ell = 4 branches, tried at a few
    deterministic placements); returns (specs, mat) or None if no
    placement passes cubic_habitat."""
    fed = [(t, (t + 1) % n) for t in range(n)]
    med = list(ech) + list(gch)
    oddm = {len(med) - 2, len(med) - 1}
    base = [(u, w, 2) for (u, w) in fed] + \
        [(u, w, 3 if j in oddm else 2) for j, (u, w) in enumerate(med)]
    cands = ([n + i for i in range(len(ech))] + list(range(n)))
    for i in range(len(cands) - 1):
        for j in range(i + 1, min(i + 3, len(cands))):
            specs = list(base)
            for t in (cands[i], cands[j]):
                (u, w, L) = specs[t]
                if L != 2:
                    break
                specs[t] = (u, w, 4)
            else:
                hedges = [(u, w) for (u, w, _L) in specs]
                lens = [L for (_u, _w, L) in specs]
                if cubic_habitat(n, hedges, lens):
                    return specs, frozenset(range(n, n + len(med)))
    return None


def cyc_sample(n, tries, rng):
    """Seeded strand_witness-like pairs: ONE positional F-cycle, a
    random chord perfect matching avoiding F-parallels, both odd
    branches matching chords (2k = 2), gated by cubic_habitat.  A
    GRAPH sampler; no placement is drawn.  Returns (specs, ech, gch)
    triples."""
    out = []
    for _t in range(tries):
        pl = list(range(n))
        rng.shuffle(pl)
        med = []
        ok = True
        while pl:
            x = pl.pop()
            cands = [y for y in pl if (x - y) % n not in (1, n - 1)]
            if not cands:
                ok = False
                break
            y = rng.choice(cands)
            pl.remove(y)
            med.append((x, y))
        if not ok:
            continue
        mi = list(range(len(med)))
        rng.shuffle(mi)
        gch = [med[j] for j in mi[:2]]
        ech = [med[j] for j in mi[2:]]
        got = specs_of_diagram(n, ech, gch)
        if got is None:
            continue
        out.append((got[0], ech, gch))
    return out


def witness_positional():
    """The (GR-113) witness re-read as a positional diagram: hub ->
    position along its single F-cycle; returns (n, ech, gch) plus the
    hub-space cell data for the cross-asserts."""
    specs, mat = strand_witness()
    n = 16
    oidx = odd_idx(specs)
    cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
    assert len(cycles) == 1, 'witness 2-factor is not a single cycle'
    pos = {v: t for t, v in enumerate(cycles[0])}
    ech = [(pos[a], pos[b]) for (a, b) in mpairs]
    gch = [(pos[u], pos[w]) for (u, w) in oddends]
    return n, ech, gch, cycles, mpairs, oddends


def witness_mutations(n, ech, gch):
    """Every 2-chord endpoint transposition of the witness diagram
    (both swap variants per chord pair), re-gated by cubic_habitat via
    specs_of_diagram; yields (tag, specs, ech2, gch2)."""
    chords = list(ech) + list(gch)
    ne = len(ech)
    for i in range(len(chords) - 1):
        for j in range(i + 1, len(chords)):
            (a, b), (c, d) = chords[i], chords[j]
            for (p1, p2) in (((a, c), (b, d)), ((a, d), (b, c))):
                if (p1[0] - p1[1]) % n in (1, n - 1):
                    continue
                if (p2[0] - p2[1]) % n in (1, n - 1):
                    continue
                cc = list(chords)
                cc[i], cc[j] = p1, p2
                ech2, gch2 = cc[:ne], cc[ne:]
                got = specs_of_diagram(n, ech2, gch2)
                if got is None:
                    continue
                yield (f'mut({i},{j})', got[0], ech2, gch2)


def refut_specs():
    """The four (GR-116) refutation witnesses, pinned verbatim as found
    (the --hunt legs at seed 20260827: mut16 is the gated 2-chord
    transposition mut(1,2) of the (GR-113) witness diagram -- ONE
    endpoint swap between two even chords; the others are seeded
    single-cycle pool draws).  Positional diagrams on the cycle
    0..n-1; the shape is rebuilt deterministically by
    specs_of_diagram.  Pinned figures: (M*, family, #pos, #neg, #bal,
    gap, min |h|)."""
    return [
        ('mut16', 16,
         [(8, 5), (1, 9), (13, 15), (12, 3), (2, 7), (14, 10)],
         [(6, 11), (0, 4)], (12, 64, 32, 32, 0, 2, 2)),
        ('rand16', 16,
         [(2, 0), (15, 7), (1, 10), (13, 6), (8, 4), (12, 3)],
         [(5, 9), (11, 14)], (12, 48, 24, 24, 0, 2, 2)),
        ('rand20a', 20,
         [(8, 16), (7, 9), (3, 14), (6, 17), (1, 15), (11, 0), (13, 2),
          (18, 5)], [(10, 4), (12, 19)], (16, 32, 16, 16, 0, 2, 2)),
        ('rand20b', 20,
         [(1, 7), (18, 4), (8, 11), (3, 13), (12, 6), (9, 0), (17, 19),
          (15, 2)], [(14, 10), (5, 16)], (16, 48, 24, 24, 0, 2, 3)),
    ]


def dsu_find(parent, a):
    while parent[a] != a:
        parent[a] = parent[parent[a]]
        a = parent[a]
    return a


def dip_census(n, ech, gch, mstar, dmax):
    """The interval-flip graph through valid words of size >= M* - d,
    for even d <= dmax: nodes = valid words, edges = single interval
    flips (both ends valid, both sizes >= the threshold; the full flip
    -- the colour swap -- is excluded).  Returns (words -> size,
    {d: parent map}) for component queries by the caller."""
    words = {}
    for w in range(1 << n):
        if word_valid(w, n, ech, gch):
            rot = (w >> 1) | ((w & 1) << (n - 1))
            words[w] = bin(w ^ rot).count('1')
    masks = []
    for i in range(n):
        for L in range(1, n):
            m = 0
            for t in range(L):
                m |= 1 << ((i + t) % n)
            masks.append(m)
    edges = []
    for w in words:
        for m in masks:
            w2 = w ^ m
            if w2 > w and w2 in words:
                edges.append((min(words[w], words[w2]), w, w2))
    out = {}
    for d in range(2, dmax + 1, 2):
        thr = mstar - d
        parent = {w: w for w, s in words.items() if s >= thr}
        for (ms, a, b) in edges:
            if ms >= thr:
                ra, rb = dsu_find(parent, a), dsu_find(parent, b)
                if ra != rb:
                    parent[ra] = rb
        out[d] = parent
    return words, out


# ------------------------------------------------------------ sweeps --------


def stratum_pool():
    out = []
    for (_tag, n, specs) in stratum_cases():
        oidx, mats, _c = pairs_of(specs, n)
        for mat in mats:
            out.append((specs, n, mat, oidx))
    return out


def v8_pool():
    specs, n = v8_specs(), 8
    oidx, mats, _c = pairs_of(specs, n)
    return [(specs, n, mat, oidx) for mat in mats]


def control_pool():
    specs, n = gr103_specs(), 12
    return [(specs, n, frozenset({12, 13, 14, 15, 16, 17}),
             odd_idx(specs))]


def witness_pool():
    specs, mat = strand_witness()
    return [(specs, 16, mat, odd_idx(specs))]


def cell_pool(rng, n, k2, tries, cap=None):
    got = cell_shapes(n, k2, tries, rng)
    if cap is not None and len(got) > cap:
        got = got[:cap]
    return [(sp, n, mat, odd_idx(sp)) for (sp, mat) in got]


def closure_pair(specs, n, mat, oidx, stats):
    """--closure at one pair: (GR-115) asserted on the labeled maximum
    family; the coverage + closed-gap records."""
    cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
    mstar, fam, _bp = enum_family(n, cycles, mpairs, oddends)
    k2 = len(oidx)
    haspos = False
    nbal = nclosed = 0
    minh = None
    for (sigma, pats) in fam:
        _g, h, mclosed = ledger_assert(sigma, tuple(pats), k2, cycles,
                                       mpairs, oddends)
        c = cls_of(pats, k2)
        haspos |= (c == 'pos')
        nbal += 1 if c == 'bal' else 0
        nclosed += 1 if mclosed else 0
        minh = abs(h) if minh is None else min(minh, abs(h))
    if nbal == 0:
        stats['REFUTATION'] += 1
        print(f'    ** REFUTATION (no balance-valid maximum): n = {n}, '
              f'specs = {specs}, mat = {sorted(mat)}')
    mcl = closed_mstar(n, cycles, mpairs, oddends)
    assert mcl <= mstar
    assert (mcl == mstar) == (nclosed > 0), \
        'closed-gap vs closed-maximum-count inconsistency'
    stats['pairs'] += 1
    stats['forcing_pairs'] += 1 if haspos else 0
    stats['closedmax_pairs'] += 1 if nclosed else 0
    stats[f'clgap_{mstar - mcl}'] += 1
    if haspos:
        stats['forcing_closedmax'] += 1 if nclosed else 0
        stats[f'forcing_clgap_{mstar - mcl}'] += 1
    if k2 == 2:
        stats['h1_pairs'] += 1 if minh <= 1 else 0
        if haspos:
            stats['forcing_h1'] += 1 if minh <= 1 else 0
    return


def report_closure(tag, stats, t0):
    gaps = {int(k[6:]): v for k, v in stats.items()
            if k.startswith('clgap_')}
    fgaps = {int(k[14:]): v for k, v in stats.items()
             if k.startswith('forcing_clgap_')}
    print(f'  leg {tag}: {stats["pairs"]} O<=M pairs '
          f'({stats["forcing_pairs"]} with pos-forcing maxima); '
          f'M-closed maximum exists at {stats["closedmax_pairs"]} '
          f'(at {stats["forcing_closedmax"]} of the forcing ones); '
          f'|h|<=1 maximum exists at {stats["h1_pairs"]} '
          f'(at {stats["forcing_h1"]} of the forcing ones, 2k = 2 legs); '
          f'closed gap M* - M*_cl histogram {dict(sorted(gaps.items()))} '
          f'(forcing pairs only: {dict(sorted(fgaps.items()))})  '
          f'[{time.time() - t0:.0f}s]')


# --------------------------------------------- [GXE-1] --ledger --------------


def leg_ledger(args):
    t0 = time.time()
    print('[--ledger] (GR-115) asserted: exhaustively over all labeled '
          'states on the n <= 6 stratum; over every valid word of the '
          '(GR-113) witness; over the labeled maximum families of V8 + '
          'the (GR-103) control')
    nconf = 0
    npairs = 0
    for (specs, n, mat, oidx) in stratum_pool():
        cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
        k2 = len(oidx)
        for sigma in itertools.product((0, 1, 2), repeat=n):
            pats = valid_pats(sigma, cycles, mpairs, oddends)
            if pats is None:
                continue
            ledger_assert(sigma, tuple(pats), k2, cycles, mpairs, oddends)
            nconf += 1
        npairs += 1
    print(f'  stratum: EXHAUSTIVE over 3^n labeled states -- '
          f'{nconf} valid configurations across {npairs} pairs, '
          f'0 violations')
    # the witness: every valid word (all sizes), via the word model
    n, ech, gch, cycles, mpairs, oddends = witness_positional()
    pos2hub = {t: v for t, v in enumerate(cycles[0])}
    nw = 0
    for w in range(1 << n):
        if not word_valid(w, n, ech, gch):
            continue
        sigma = [0] * n
        for t in range(n):
            xa, xb = (w >> ((t - 1) % n)) & 1, (w >> t) & 1
            if xa != xb:
                sigma[pos2hub[t]] = 2 if xa else 1
        sigma = tuple(sigma)
        pats = valid_pats(sigma, cycles, mpairs, oddends)
        assert pats is not None, 'word model vs valid_pats disagree'
        ledger_assert(sigma, tuple(pats), 2, cycles, mpairs, oddends)
        cls, h, closed, _gres = word_stats(w, n, ech, gch)
        assert cls == cls_of(tuple(pats), 2), 'word class != cls_of'
        g2, h2, cl2 = ledger_of(sigma, mpairs, oddends)
        assert (h, closed) == (h2, cl2), 'word ledger != sigma ledger'
        nw += 1
    print(f'  witness: {nw} valid words (ALL sizes), ledger + class '
          f'cross-asserted against the sigma model, 0 violations')
    # V8 (2k = 4) + control (2k = 2): the labeled maximum families
    for tag, pool in (('V8 (2k = 4)', v8_pool()),
                      ('(GR-103) control', control_pool())):
        nf = 0
        for (specs, n, mat, oidx) in pool:
            cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
            _m, fam, _bp = enum_family(n, cycles, mpairs, oddends)
            for (sigma, pats) in fam:
                ledger_assert(sigma, tuple(pats), len(oidx), cycles,
                              mpairs, oddends)
                nf += 1
        print(f'  {tag}: {nf} labeled maxima asserted, 0 violations')
    print(f'[--ledger] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GXE-2] --closure -------------


def leg_closure(args):
    t0 = time.time()
    print(f'[--closure] the coverage sentence: does the maximum family '
          f'contain an M-closed member (=> balance-valid, (GR-115)(i))? '
          f'plus the closed-gap histogram; seed {R_SEED}')
    rng = random.Random(R_SEED)
    for tag, pool in (('stratum (EXHAUSTIVE)', stratum_pool()),
                      ('V8 (2k = 4)', v8_pool()),
                      ('(GR-103) control', control_pool()),
                      ('(GR-113) witness', witness_pool()),
                      ('n = 12, 2k = 2 cell pool (tries 120 -- CAP, '
                       'disclosed)', cell_pool(rng, 12, 2, 120)),
                      ('n = 12, 2k = 4 cell pool (tries 120 -- CAP, '
                       'disclosed)', cell_pool(rng, 12, 4, 120)),
                      ('n = 14, 2k = 2 cell pool (tries 60 -- CAP, '
                       'disclosed)', cell_pool(rng, 14, 2, 60)),
                      ('n = 16, 2k = 2 cell pool (tries 40, cap 12 -- '
                       'CAPS, disclosed)', cell_pool(rng, 16, 2, 40, 12))):
        t1 = time.time()
        stats = collections.Counter()
        for (specs, n, mat, oidx) in pool:
            closure_pair(specs, n, mat, oidx, stats)
        report_closure(tag, stats, t1)
    print(f'[--closure] OK  [{time.time() - t0:.0f}s]  (seed {R_SEED})')


# --------------------------------------------- [GXE-3] --hunt ----------------


def hunt_pair(nn, e2, g2, specs, tag, stats, gap_hist):
    mstar, N, cnt, nclosed, minh, gap, all22 = word_census(nn, e2, g2)
    stats['pairs'] += 1
    stats['forcing'] += 1 if cnt['pos'] else 0
    stats['closedmax'] += 1 if nclosed else 0
    stats['all22'] += 1 if all22 else 0
    gap_hist[gap] += 1
    if cnt['pos'] and not cnt['bal']:
        stats['refut'] += 1
        print(f'    ** (GR-108) REFUTATION (gap {gap}): {tag}, '
              f'ech = {e2}, gch = {g2}, specs = {specs}')
    if gap >= 4:
        stats['price_refut'] += 1
        print(f'    ** PRICE-FORM REFUTATION (gap {gap} >= 4): {tag}, '
              f'ech = {e2}, gch = {g2}, specs = {specs}')
    if cnt['pos'] and not nclosed:
        stats['forcing_no_closed'] += 1


def report_hunt(tag, stats, gap_hist, t1):
    print(f'  {tag}: {stats["pairs"]} gated pairs; {stats["forcing"]} '
          f'with pos-forcing maxima, of which '
          f'{stats["forcing_no_closed"]} lack an M-closed maximum; '
          f'all-maxima-(2,2)-forcing pairs {stats["all22"]}; gap '
          f'histogram {dict(sorted(gap_hist.items()))}; (GR-108) '
          f'refutations {stats["refut"]}; price-form refutations '
          f'(gap >= 4) {stats["price_refut"]}  [{time.time() - t1:.0f}s]')


def leg_hunt(args):
    t0 = time.time()
    print(f'[--hunt] the refutation hunt on the named single-cycle cell '
          f'(Step G134): pos-forcing maxima with bal = 0 (gap > 0) '
          f'refute (GR-108); gap >= 4 refutes the price form '
          f'(GR-104)(i); word-model census; seed {R_SEED + 1}')
    # control: the witness itself through the word model
    n, ech, gch, _cy, _mp, _oe = witness_positional()
    mstar, N, cnt, nclosed, minh, gap, all22 = word_census(n, ech, gch)
    assert (mstar, N) == (12, 152) and \
        (cnt['pos'], cnt['neg'], cnt['bal']) == (48, 48, 56) and \
        gap == 0, 'witness census drifted from the (GR-113) pinned figures'
    print(f'  control: the witness re-derived by the word model -- '
          f'M* = {mstar}, family {N} = 48/48/56, gap 0, M-closed maxima '
          f'{nclosed}, min |h| over maxima {minh}')
    # leg A: every 2-chord endpoint transposition of the witness diagram
    t1 = time.time()
    stats = collections.Counter()
    gap_hist = collections.Counter()
    for (tag, specs, e2, g2) in witness_mutations(n, ech, gch):
        hunt_pair(n, e2, g2, specs, tag, stats, gap_hist)
    report_hunt('witness mutations (EXHAUSTIVE over gated 2-chord '
                'transpositions)', stats, gap_hist, t1)
    total_refut = stats['refut'] + stats['price_refut']
    # leg B: seeded single-cycle pools at n = 16 / 18 / 20 (the original
    # discovery stream, seed R_SEED + 1) and the boundary-bracketing
    # pools at n = 12 / 14 (their own stream, seed R_SEED + 3, so the
    # discovery legs reproduce byte-identically)
    rng = random.Random(R_SEED + 1)
    rngb = random.Random(R_SEED + 3)
    print(f'  (boundary legs n = 12/14 use seed {R_SEED + 3})')
    for nn, tries, rr in ((12, 100, rngb), (14, 60, rngb),
                          (16, 60, rng), (18, 40, rng), (20, 12, rng)):
        t1 = time.time()
        stats = collections.Counter()
        gap_hist = collections.Counter()
        for (specs, e2, g2) in cyc_sample(nn, tries, rr):
            hunt_pair(nn, e2, g2, specs, f'n = {nn}', stats, gap_hist)
        report_hunt(f'n = {nn} single-cycle pool (tries {tries} -- CAP, '
                    f'disclosed)', stats, gap_hist, t1)
        total_refut += stats['refut'] + stats['price_refut']
    print(f'  refutation candidates TOTAL: {total_refut} (an exhausted '
          f'cap is not nonexistence; pinned re-verification in --verify)')
    print(f'[--hunt] OK  [{time.time() - t0:.0f}s]  (seed {R_SEED + 1})')


# --------------------------------------------- [GXE-4] --verify --------------


def leg_verify(args):
    t0 = time.time()
    print('[--verify] the four pinned (GR-116) refutation witnesses '
          're-derived through THREE independent models: the word '
          'census, the landed gprice.rmodel_f (cube-asserted at 1 054 '
          'pairs in its own sweeps), and -- at n = 16 -- the landed '
          'gblaw.enum_family; every figure asserted')
    f_pin = {0: 4, 1: 6, 2: 6, 3: 4}
    for (tag, n, ech, gch, fig) in refut_specs():
        t1 = time.time()
        got = specs_of_diagram(n, ech, gch)
        assert got is not None, f'{tag}: shape fails the habitat gate'
        specs, mat = got
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        assert cubic_habitat(n, hedges, lens), f'{tag}: gate lost'
        oidx = odd_idx(specs)
        assert len(oidx) == 2 and set(oidx) <= mat, \
            f'{tag}: not an O <= M, 2k = 2 pair'
        cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
        assert len(cycles) == 1, f'{tag}: not a single F-cycle'
        pos = {v: t for t, v in enumerate(cycles[0])}
        e2 = [(pos[a], pos[b]) for (a, b) in mpairs]
        g2 = [(pos[u], pos[w]) for (u, w) in oddends]
        mstar, N, cnt, nclosed, minh, gap, all22 = word_census(n, e2, g2)
        assert (mstar, N, cnt['pos'], cnt['neg'], cnt['bal'], gap,
                minh) == fig, f'{tag}: word census drifted from the pin'
        assert nclosed == 0 and not all22, f'{tag}: census flags drifted'
        f = rmodel_f(n, cycles, mpairs, oddends)
        assert f == f_pin, f'{tag}: rmodel_f f-table != pinned'
        assert min(f.values()) == n - mstar, f'{tag}: d_par != n - M*'
        line = (f'  {tag}: habitat OK, single 16-cycle' if n == 16 else
                f'  {tag}: habitat OK, single 20-cycle')
        line += (f'; word census (M*, N, pos, neg, bal, gap, min|h|) = '
                 f'{fig}; rmodel_f f = {f} (gap 2, both one-flip '
                 f'prices +2: the price form HOLDS)')
        if n == 16:
            ms2, fam, _bp = enum_family(n, cycles, mpairs, oddends)
            cc = collections.Counter(cls_of(p, 2) for (_s, p) in fam)
            assert (ms2, len(fam), cc['pos'], cc['neg'], cc['bal']) == \
                (fig[0], fig[1], fig[2], fig[3], 0), \
                f'{tag}: enum_family disagrees with the word census'
            some_half = False
            for (sigma, pats) in fam:
                _g, h, mclosed = ledger_assert(sigma, tuple(pats), 2,
                                               cycles, mpairs, oddends)
                assert abs(h) >= 2 and not mclosed, \
                    f'{tag}: (GR-115) contrapositive violated'
                res = sorted(sum(1 for v in (u, w) if sigma[v])
                             for (u, w) in oddends)
                if res != [2, 2]:
                    some_half = True
            assert some_half, f'{tag}: every maximum (2,2)-forcing'
            line += '; enum_family agrees (third model)'
        print(line + f'  [{time.time() - t1:.0f}s]')
    # provenance: mut16 is ONE 2-chord endpoint transposition of the
    # (GR-113) witness diagram (odd chords untouched)
    n, ech_w, gch_w, _cy, _mp, _oe = witness_positional()
    (tag, _n, ech_m, gch_m, _fig) = refut_specs()[0]
    assert {frozenset(c) for c in gch_m} == {frozenset(c) for c in gch_w}
    old = {frozenset(c) for c in ech_w} - {frozenset(c) for c in ech_m}
    new = {frozenset(c) for c in ech_m} - {frozenset(c) for c in ech_w}
    assert len(old) == 2 and len(new) == 2 and \
        set().union(*old) == set().union(*new), \
        'mut16 is not a single 2-chord transposition of the witness'
    print('  provenance: mut16 differs from the (GR-113) witness '
          'diagram by ONE endpoint transposition between two even '
          'chords (odd chords identical) -- asserted')
    print(f'[--verify] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GXE-5] --strand --------------


def leg_strand(args):
    t0 = time.time()
    print('[--strand] the witness anatomy: fine components re-derived, '
          'escaper vs stranded features, and the DIP CENSUS (interval '
          'flips through valid words of size >= M* - d)')
    specs, mat = strand_witness()
    n = 16
    oidx = odd_idx(specs)
    cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
    mstar, fam, _bp = enum_family(n, cycles, mpairs, oddends)
    k2 = 2
    cls = [cls_of(p, k2) for (_s, p) in fam]
    index = {s: i for i, (s, _p) in enumerate(fam)}
    parent = list(range(len(fam)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for i, (sigma, _p) in enumerate(fam):
        for s2 in itertools.chain(slides(sigma, cycles, 1),
                                  slides(sigma, cycles, 2),
                                  teleports(sigma, cycles),
                                  safeflips(sigma, cycles, mpairs,
                                            oddends)):
            p2 = valid_pats(s2, cycles, mpairs, oddends)
            if p2 is None:
                continue
            ri, rj = find(i), find(index[s2])
            if ri != rj:
                parent[ri] = rj
    comps = collections.defaultdict(list)
    for i in range(len(fam)):
        comps[find(i)].append(i)
    balroots = {r for r, mem in comps.items()
                if any(cls[i] == 'bal' for i in mem)}
    stranded = [i for i in range(len(fam))
                if cls[i] == 'pos' and find(i) not in balroots]
    escapers = [i for i in range(len(fam))
                if cls[i] == 'pos' and find(i) in balroots]
    assert (len(stranded), len(escapers)) == (32, 16), \
        'witness fine-component structure drifted'
    # features: ledger, residency, sink-set sharing with the bal family
    balsinks = {tuple(v for v in range(n) if fam[i][0][v] == 2)
                for i in range(len(fam)) if cls[i] == 'bal'}
    for tag, pool in (('escapers (16)', escapers),
                      ('stranded (32)', stranded)):
        hh = collections.Counter()
        rr = collections.Counter()
        share = 0
        for i in pool:
            sigma = fam[i][0]
            gparts, h, _cl = ledger_of(sigma, mpairs, oddends)
            hh[h] += 1
            res = tuple(sorted(sum(1 for v in (u, w) if sigma[v])
                               for (u, w) in oddends))
            rr[res] += 1
            key = tuple(v for v in range(n) if sigma[v] == 2)
            share += 1 if key in balsinks else 0
        print(f'  {tag}: h histogram {dict(sorted(hh.items()))}; '
              f'gamma-residency histogram '
              f'{dict((str(k), v) for k, v in sorted(rr.items()))}; '
              f'sink set shared with a bal maximum: {share}')
    # the bal family's own closure figures
    nclosed = sum(1 for i in range(len(fam)) if cls[i] == 'bal'
                  and ledger_of(fam[i][0], mpairs, oddends)[2])
    mcl = closed_mstar(n, cycles, mpairs, oddends)
    print(f'  bal family (56): M-closed members {nclosed}; '
          f'M*_cl = {mcl} vs M* = {mstar}')
    # the dip census, in the word model
    nn, ech, gch, cycles2, _mp2, _oe2 = witness_positional()
    pos2hub = {t: v for t, v in enumerate(cycles2[0])}
    hub2pos = {v: t for t, v in pos2hub.items()}

    def word_of(sigma):
        # single cycle, R != 0: labels determine every edge bit
        w = 0
        for t in range(nn):
            # bit t = edge (t, t+1): equals 1 iff the next reversal
            # hub strictly ahead (positions t+1, t+2, ...) is a sink
            s = (t + 1) % nn
            while not sigma[pos2hub[s]]:
                s = (s + 1) % nn
            if sigma[pos2hub[s]] == 2:
                w |= 1 << t
        return w

    words, dips = dip_census(nn, ech, gch, mstar, 8)
    balwords = {word_of(fam[i][0]) for i in range(len(fam))
                if cls[i] == 'bal'}
    for d in sorted(dips):
        parent = dips[d]
        balroots2 = {dsu_find(parent, w) for w in balwords}
        esc_s = sum(1 for i in stranded
                    if dsu_find(parent, word_of(fam[i][0])) in balroots2)
        esc_e = sum(1 for i in escapers
                    if dsu_find(parent, word_of(fam[i][0])) in balroots2)
        print(f'  dip d = {d} (configs of size >= {mstar - d}: '
              f'{len(parent)} valid words): stranded pos maxima reaching '
              f'bal company {esc_s}/32; big-component pos {esc_e}/16')
    print(f'[--strand] OK  [{time.time() - t0:.0f}s]')


# ----------------------------------------------------------- main -----------


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--ledger', action='store_true')
    ap.add_argument('--closure', action='store_true')
    ap.add_argument('--hunt', action='store_true')
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--strand', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.validate:
        args.ledger = args.closure = args.hunt = True
        args.verify = args.strand = True
    if not (args.ledger or args.closure or args.hunt or args.verify
            or args.strand):
        ap.error('pick a mode: --ledger / --closure / --hunt / --verify '
                 '/ --strand / --validate')
    if args.ledger:
        leg_ledger(args)
    if args.closure:
        leg_closure(args)
    if args.hunt:
        leg_hunt(args)
    if args.verify:
        leg_verify(args)
    if args.strand:
        leg_strand(args)


if __name__ == '__main__':
    main()
