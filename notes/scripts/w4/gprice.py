"""GPRICE -- the thirty-third kernel-(K) ordinal: (GR-104)(i), the PRICE
form of the selection clause (spec: notes/Pencil-fanout.md S"GPRICE --
thirty-third ordinal").

TARGET: (GR-104)(i) -- at some parity-optimal configuration with
|delta| <= 2 (balanced ones qualifying vacuously), some majority-side flip
has f(p + chi_gamma) <= f(p) + 2 (S(K-grid) Step G124).  Theorem at
n <= 10 by (GR-101)(ii) + (GR-86); measured intact at the three audited
n = 12 stall pairs; OPEN from n = 12.  This pass reduces the open cell to
an exact combinatorial normal form and sweeps it far past the cube limit:

  (GR-106) THE REVERSAL-SET NORMAL FORM.  Fix a perfect matching M with
  ALL odd branches inside M (the only live cell: a feasible majority
  branch outside M is cheap by definition, so (GR-104)(i) holds at any
  pattern carrying one, by (GR-86)).  Then the 2-factor F = G minus M is
  all-even, an admissible configuration at any odd pattern p is exactly
  (i) a set R of "reversal hubs" meeting every F-cycle evenly, (ii) an
  alternating sink/source labelling of R around each F-cycle, subject to
  (iii) no even matching pair labelled (sink, sink) or (source, source),
  and (iv) each end of an A-odd matching branch in R labelled SOURCE,
  each end of a B-odd one labelled SINK; and
      dist(z, M) = n - |R|   EXACTLY.
  Hence f(p) = n - max |R| over p-valid reversal sets -- computable in
  2^n instead of 2^{3n/2}, which reaches n = 14/16 where the cube stops
  at 12.  (asserted against the full-cube f at every cube-reachable
  pair; --cell, --seed)

  (GR-105) THE COMPLEMENT IDENTITY.  Reversing every even-branch
  orientation is a dist-preserving bijection between the admissible
  configurations at p and at the ALL-FLIPPED pattern pbar: at O <= M,
      f(p) = f(pbar)  for EVERY pattern p.
  In particular at 2k = 2: f(AA) = f(BB) and f(AB) = f(BA) -- the two
  majority one-flip prices at a stalled all-A optimum are EQUAL, which
  is (GR-103)(iii)'s measured [0, 0] symmetry explained.  (asserted at
  every O <= M pair of every leg; --cell, --seed, --hunt)

  THE HUNT SENTENCE.  At an O <= M pair the price form fails iff no
  balanced pattern attains d_par(M), some |delta| = 2 pattern does, and
  every majority flip from every such optimal pattern prices >= +4.
  --hunt sweeps seeded habitat shapes at n = 12/14/16 for exactly that
  configuration of f-values (R-model exact, no cap on the pattern side;
  shape/matching caps disclosed).

Modes:
  --cell     stratum (EXHAUSTIVE shapes, all O <= M matchings) + V8 +
             the (GR-103) constructed control pair: R-model f asserted
             == full-cube f at every pattern; (GR-105) asserted; the
             price verdict and gap histogrammed per 2k.
  --seed     seeded n = 8/10 (cube-asserted) and n = 12 (R-model, first
             pairs cube-asserted): same sentences at scale.
  --hunt     seeded n = 12/14/16, R-model only: the hunt sentence, worst
             flip prices printed, any refutation candidate printed in
             full (shape, matching, f-table) for independent audit.
  --validate all three.

Rank-free throughout: gexist.fully_good_rank is never imported or called
and no d_fg claim is made anywhere ((a') / input (Y) untouched).  Exact
integers / GF(2); no floating point; every rng seeded, seed printed;
every sampler draws a GRAPH, never a placement (S(K-clos) (AC-9)).
Wall-clock [Ns] annotations are non-deterministic; every other byte is
seed-stable.
"""
import argparse
import collections
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

# balance layer: DIRECTLY from gridbal_common (the 2026-08-25 move-down;
# never via the sibling re-exports)
from gridbal_common import (branches_at, imb_of, odd_idx, seeded_shapes,    # noqa: E402
                            stratum_cases, v8_specs)
from gbal import z_admissible                                               # noqa: E402
from gflow import adm_cube, f_layers                                        # noqa: E402
from gorient import perfect_matchings                                       # noqa: E402
from cflank import cubic_habitat                                            # noqa: E402

R_SEED = 20260825


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  `f_cycles` extracts the
# 2-factor's cycles; `cell_data` the (F-cycles, even matching pairs, odd
# ends) triple of one O <= M pair; `rmodel_f` the (GR-106) reversal-set
# computation of f at EVERY pattern; `cube_f` the landed full-cube f
# (gflow.f_layers) for the cross-assert; `price_verdict` the (GR-104)(i)
# sentence at one f-table.


def f_cycles(specs, n, mat):
    """The cycles of the 2-factor F = specs minus mat, as hub sequences
    (branch-id-aware, so parallel branches give the length-2 cycle)."""
    inc = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        if i in mat:
            continue
        inc[u].append((i, w))
        inc[w].append((i, u))
    for v in range(n):
        assert len(inc[v]) == 2, 'F is not a 2-factor'
    seen = set()
    cycles = []
    for v0 in range(n):
        if v0 in seen:
            continue
        cyc = [v0]
        seen.add(v0)
        br, cur = inc[v0][0]
        used = {br}
        cur = inc[v0][0][1]
        while cur != v0:
            cyc.append(cur)
            seen.add(cur)
            nb = [(i, x) for (i, x) in inc[cur] if i not in used]
            assert len(nb) == 1, 'walk error'
            used.add(nb[0][0])
            cur = nb[0][1]
        cycles.append(cyc)
    assert sum(len(c) for c in cycles) == n
    return cycles


def cell_data(specs, n, mat, oidx):
    """(F-cycles, even matching hub pairs, odd-branch end pairs) of one
    O <= M pair."""
    oset = set(oidx)
    assert oset <= set(mat), 'not an O <= M pair'
    cycles = f_cycles(specs, n, mat)
    mpairs = [(specs[i][0], specs[i][1]) for i in mat if i not in oset]
    oddends = [(specs[i][0], specs[i][1]) for i in oidx]
    return cycles, mpairs, oddends


def rmodel_diag(n, cycles, mpairs, oddends):
    """Mechanism diagnostic: (M*, #structurally-max R, #of them valid at
    some balanced pattern).  The balance law at the pair says the third
    count is >= 1; its ratio to the second measures how close the pair
    is to a law violation."""
    k2 = len(oddends)
    balpats = [p for p in range(1 << k2) if imb_of(k2, p) == 0]
    endhubs = sorted({v for (u, w) in oddends for v in (u, w)})
    cmasks = [sum(1 << v for v in cyc) for cyc in cycles]
    mstar, nmax, nbal = 0, 0, 0
    for mask in range(1 << n):
        ok = True
        for cm in cmasks:
            if bin(mask & cm).count('1') % 2:
                ok = False
                break
        if not ok:
            continue
        size = bin(mask).count('1')
        if size < mstar:
            continue
        cmembers = [[v for v in cyc if (mask >> v) & 1] for cyc in cycles]
        adj = collections.defaultdict(list)
        for mem in cmembers:
            L = len(mem)
            if L >= 2:
                for t in range(L):
                    a, b = mem[t], mem[(t + 1) % L]
                    if L == 2 and t == 1:
                        break
                    adj[a].append(b)
                    adj[b].append(a)
        for (x, y) in mpairs:
            if (mask >> x) & 1 and (mask >> y) & 1:
                adj[x].append(y)
                adj[y].append(x)
        klass, comp = {}, {}
        ok = True
        cid = 0
        members = [v for v in range(n) if (mask >> v) & 1]
        for s in members:
            if s in klass:
                continue
            cid += 1
            klass[s] = 0
            comp[s] = cid
            stack = [s]
            while stack and ok:
                a = stack.pop()
                for b in adj[a]:
                    if b not in klass:
                        klass[b] = klass[a] ^ 1
                        comp[b] = cid
                        stack.append(b)
                    elif klass[b] == klass[a]:
                        ok = False
                        break
            if not ok:
                break
        if not ok:
            continue
        anyvalid = anybal = False
        for p in range(1 << k2):
            need = {}
            good = True
            for j, (u, w) in enumerate(oddends):
                lab = (p >> j) & 1
                for v in (u, w):
                    if (mask >> v) & 1:
                        o = klass[v] ^ lab
                        cv = comp[v]
                        if need.setdefault(cv, o) != o:
                            good = False
                            break
                if not good:
                    break
            if good:
                anyvalid = True
                if p in balpats:
                    anybal = True
                    break
        if not anyvalid:
            continue
        if size > mstar:
            mstar, nmax, nbal = size, 0, 0
        nmax += 1
        nbal += 1 if anybal else 0
    return mstar, nmax, nbal


def rmodel_f(n, cycles, mpairs, oddends):
    """(GR-106): f(pattern) = n - max |R| over pattern-valid reversal
    sets, at EVERY pattern in one 2^n enumeration.  A set R is
    structurally valid iff it meets every F-cycle evenly and its aux
    graph (cyclic adjacency along each F-cycle + an edge per even
    matching pair inside R) is bipartite; it is p-valid iff the forced
    end labels (A-end SOURCE, B-end SINK) extend to a proper 2-colouring
    -- checked per component through the ends' parity classes."""
    k2 = len(oddends)
    endhubs = sorted({v for (u, w) in oddends for v in (u, w)})
    cmasks = [sum(1 << v for v in cyc) for cyc in cycles]
    best = {p: 0 for p in range(1 << k2)}       # R = empty is always valid
    for mask in range(1, 1 << n):
        # per-cycle parity (bitmask pre-check, then member extraction)
        ok = True
        for cm in cmasks:
            if bin(mask & cm).count('1') % 2:
                ok = False
                break
        if not ok:
            continue
        cmembers = [[v for v in cyc if (mask >> v) & 1] for cyc in cycles]
        # aux graph: cyclic adjacency + even-M edges inside R
        adj = collections.defaultdict(list)
        for mem in cmembers:
            L = len(mem)
            if L >= 2:
                for t in range(L):
                    a, b = mem[t], mem[(t + 1) % L]
                    if L == 2 and t == 1:
                        break                     # dedupe the wrap pair
                    adj[a].append(b)
                    adj[b].append(a)
        for (x, y) in mpairs:
            if (mask >> x) & 1 and (mask >> y) & 1:
                adj[x].append(y)
                adj[y].append(x)
        # 2-colour (bipartiteness = the alternation + pair exclusions)
        klass = {}
        ok = True
        members = [v for v in range(n) if (mask >> v) & 1]
        for s in members:
            if s in klass:
                continue
            klass[s] = 0
            stack = [s]
            comp = s
            while stack and ok:
                a = stack.pop()
                for b in adj[a]:
                    if b not in klass:
                        klass[b] = klass[a] ^ 1
                        stack.append(b)
                    elif klass[b] == klass[a]:
                        ok = False
                        break
            if not ok:
                break
        if not ok:
            continue
        size = len(members)
        # component ids for the ends only (forcing involves only ends)
        comp = {}
        cid = 0
        seenc = set()
        for s in members:
            if s in seenc:
                continue
            cid += 1
            stack = [s]
            seenc.add(s)
            comp[s] = cid
            while stack:
                a = stack.pop()
                for b in adj[a]:
                    if b not in seenc:
                        seenc.add(b)
                        comp[b] = cid
                        stack.append(b)
        ein = [v for v in endhubs if (mask >> v) & 1]
        for p in range(1 << k2):
            if best[p] >= size:
                continue
            # forced label of end v under p: 0 = source (A), 1 = sink (B)
            need = {}
            good = True
            for j, (u, w) in enumerate(oddends):
                lab = (p >> j) & 1
                for v in (u, w):
                    if (mask >> v) & 1:
                        o = klass[v] ^ lab       # component orientation
                        cv = comp[v]
                        if need.setdefault(cv, o) != o:
                            good = False
                            break
                if not good:
                    break
            if good:
                best[p] = size
    return {p: n - best[p] for p in range(1 << k2)}


def cube_f(specs, n, mat, oidx):
    """The landed full-cube f (gflow.adm_cube + f_layers) at one pair."""
    binc = branches_at(specs, n)
    base = {}
    for i in mat:
        (u, w, _L) = specs[i]
        base[u] = (i, 0)
        base[w] = (i, 1)
    cube = adm_cube(specs, n, binc, oidx)
    f, _dpar = f_layers(cube, n, base)
    return f


def price_verdict(f, k2):
    """The (GR-104)(i) sentence at one f-table.  Returns (kind, gap,
    minprice): kind 'vacuous' (a balanced pattern attains d_par),
    'strict' (an |delta| = 2 pattern does and no balanced one; minprice
    = the best majority one-flip price over all such optima -- the
    price form holds iff minprice <= 2), or 'no-d2-optimum' (every
    optimum has |delta| >= 4: (GR-C1)-adjacent, outside the target's
    quantifier)."""
    dpar = min(f.values())
    bal = [p for p in f if imb_of(k2, p) == 0]
    dadm = min(f[p] for p in bal)
    gap = dadm - dpar
    if any(f[p] == dpar for p in bal):
        return 'vacuous', gap, None
    d2 = [p for p in f if abs(imb_of(k2, p)) == 2 and f[p] == dpar]
    if not d2:
        return 'no-d2-optimum', gap, None
    minprice = None
    for p in d2:
        delta = imb_of(k2, p)
        wantbit = 0 if delta > 0 else 1
        for j in range(k2):
            if (p >> j) & 1 != wantbit:
                continue
            pr = f[p ^ (1 << j)] - f[p]
            minprice = pr if minprice is None else min(minprice, pr)
    return 'strict', gap, minprice


def gr103_specs():
    """(GR-103)(i)'s printed witness shape (consumed for independent
    reconstruction, exactly as the workbook publishes it; the audit
    figures asserted here are ITS landed ones -- a control, not a
    re-derivation)."""
    return [(0, 4, 2), (4, 1, 2), (1, 5, 2), (5, 2, 2), (2, 6, 2),
            (6, 3, 2), (3, 7, 2), (7, 8, 2), (8, 9, 4), (9, 10, 2),
            (10, 11, 4), (11, 0, 2), (0, 1, 3), (2, 3, 3), (4, 8, 2),
            (5, 9, 2), (6, 10, 2), (7, 11, 2)]


def sweep_pair(specs, n, mat, oidx, with_cube, stats):
    """One O <= M pair: R-model f, the (GR-105) assert, the optional
    (GR-106) cube cross-assert, and the price verdict into `stats`."""
    k2 = len(oidx)
    cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
    f = rmodel_f(n, cycles, mpairs, oddends)
    full = (1 << k2) - 1
    for p in f:
        assert f[p] == f[p ^ full], '(GR-105) complement identity violated'
    if with_cube:
        fc = cube_f(specs, n, mat, oidx)
        assert set(fc) == set(f), 'cube missed a pattern (O <= M => all ' \
            'patterns feasible)'
        for p in f:
            assert f[p] == fc[p], '(GR-106) R-model f != cube f'
        stats['cube_pairs'] += 1
    kind, gap, minprice = price_verdict(f, k2)
    stats['pairs'] += 1
    stats[f'kind_{kind}'] += 1
    stats[f'gap_{gap}'] += 1
    stats[f'spread_{max(f.values()) - min(f.values())}'] += 1
    if kind == 'strict':
        stats[f'minprice_{minprice}'] += 1
        if minprice >= 4:
            stats['REFUTATION'] += 1
            print(f'    ** REFUTATION CANDIDATE (price {minprice}): '
                  f'n = {n}, specs = {specs}, mat = {sorted(mat)}, '
                  f'f = {f}')
    return f


def cell_shapes(n, k2, tries, rng):
    """A NEW cell-targeted sampler (disclosed): draws the pair (F, M)
    DIRECTLY -- F a random 2-factor (random cycle partition, cycles of
    length >= 2), M a random perfect matching on the hubs avoiding
    F-parallels, the k2 odd branches placed INSIDE M by length (ell = 3;
    excess topped up to 6 with ell = 4 branches, Lambda = empty
    respected) -- and gates each candidate by the canonical
    cflank.cubic_habitat.  Every O <= M pair is reachable this way; the
    seeded_shapes pool only rarely produces one.  Returns a list of
    (specs, mat) with mat the matching branch-index frozenset."""
    out = []
    for _t in range(tries):
        perm = list(range(n))
        rng.shuffle(perm)
        # random cycle partition: cut the permutation into cycles >= 2
        cycles = []
        i = 0
        while i < n:
            rem = n - i
            if rem < 4:
                L = rem
            else:
                L = rng.randrange(2, rem - 1) if rng.random() < 0.7 else rem
                if rem - L == 1:
                    L += 1
            cycles.append(perm[i:i + L])
            i += L
        fedges = []
        for cyc in cycles:
            L = len(cyc)
            fedges += [(cyc[t], cyc[(t + 1) % L]) for t in range(L)]
            if L == 2:
                fedges.pop()
                fedges += [(cyc[0], cyc[1]), (cyc[0], cyc[1])]
        # random perfect matching avoiding F-parallels
        fset = {frozenset(e) for e in fedges}
        hubs = list(range(n))
        rng.shuffle(hubs)
        medges = []
        pool = list(hubs)
        ok = True
        while pool:
            x = pool.pop()
            cands = [y for y in pool if frozenset((x, y)) not in fset]
            if not cands:
                ok = False
                break
            y = rng.choice(cands)
            pool.remove(y)
            medges.append((x, y))
        if not ok:
            continue
        # lengths: k2 odd matching branches at ell = 3, excess topped to 6
        n4 = (6 - k2) // 2
        assert k2 + 2 * n4 == 6, 'excess arithmetic (2k in {2, 4, 6})'
        mi = list(range(len(medges)))
        rng.shuffle(mi)
        oddm = mi[:k2]
        specs = [(u, w, 2) for (u, w) in fedges] + \
            [(u, w, 3 if j in oddm else 2) for j, (u, w) in enumerate(medges)]
        allb = list(range(len(specs)))
        rng.shuffle(allb)
        placed = 0
        specs2 = list(specs)
        for i in allb:
            if placed == n4:
                break
            (u, w, L) = specs2[i]
            if L == 2:
                specs2[i] = (u, w, 4)
                placed += 1
        specs = specs2
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        mat = frozenset(range(len(fedges), len(specs)))
        oidx = odd_idx(specs)
        if len(oidx) != k2 or not set(oidx) <= mat:
            continue
        out.append((specs, mat))
    return out


def pairs_of(specs, n, mat_cap=None):
    """The O <= M pairs of one shape (matchings capped when mat_cap
    binds; the caller discloses)."""
    oidx = odd_idx(specs)
    oset = set(oidx)
    mats = [m for m in perfect_matchings(specs) if oset <= m]
    capped = False
    if mat_cap is not None and len(mats) > mat_cap:
        mats = mats[:mat_cap]
        capped = True
    return oidx, mats, capped


def report(tag, stats, t0):
    kinds = {k[5:]: v for k, v in stats.items() if k.startswith('kind_')}
    gaps = {int(k[4:]): v for k, v in stats.items() if k.startswith('gap_')}
    mps = {int(k[9:]): v for k, v in stats.items()
           if k.startswith('minprice_')}
    spr = {int(k[7:]): v for k, v in stats.items()
           if k.startswith('spread_')}
    print(f'  leg {tag}: {stats["pairs"]} O<=M pairs '
          f'({stats["cube_pairs"]} cube-asserted); kinds {dict(sorted(kinds.items()))}; '
          f'gap histogram {dict(sorted(gaps.items()))}; '
          f'f-spread (max f - min f over patterns) {dict(sorted(spr.items()))}; '
          f'strict-pair min one-flip prices {dict(sorted(mps.items()))}; '
          f'refutation candidates {stats["REFUTATION"]}  '
          f'[{time.time() - t0:.0f}s]')


# --------------------------------------------- [GPR-1] --cell ---------------

def leg_cell(args):
    t0 = time.time()
    print('[--cell] (GR-105)/(GR-106) asserted on the exhaustive stratum '
          '+ V8 + the (GR-103) control; price verdicts histogrammed')
    stats = collections.Counter()
    for (_tag, n, specs) in stratum_cases():
        oidx, mats, _c = pairs_of(specs, n)
        for mat in mats:
            sweep_pair(specs, n, mat, oidx, True, stats)
    report('stratum (EXHAUSTIVE)', stats, t0)
    t1 = time.time()
    stats = collections.Counter()
    n, specs = 8, v8_specs()
    oidx, mats, _c = pairs_of(specs, n)
    for mat in mats:
        sweep_pair(specs, n, mat, oidx, True, stats)
    report('V8 (2k = 4)', stats, t1)
    # the (GR-103) control: its landed audit figures re-found in the
    # R-model (d_par = 4, gap 0, both flip prices 0 -- Step G123(iii))
    t1 = time.time()
    stats = collections.Counter()
    specs, n = gr103_specs(), 12
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    assert cubic_habitat(n, hedges, lens), '(GR-103) shape fails the gate'
    oidx = odd_idx(specs)
    mat = frozenset({12, 13, 14, 15, 16, 17})
    f = sweep_pair(specs, n, mat, oidx, True, stats)
    assert min(f.values()) == 4 and f[0] == 4, '(GR-103) d_par = 4 lost'
    assert f[1] == f[2] == 4, '(GR-103) stalled flip prices [0, 0] lost'
    print(f'    (GR-103) control: f = {f} -- d_par = 4, gap 0, the '
          f'stalled majority flips price [0, 0], all re-found by the '
          f'R-model on top of the cube assert')
    report('(GR-103) control', stats, t1)
    print(f'[--cell] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GPR-2] --seed ---------------

def leg_seed(args):
    t0 = time.time()
    print(f'[--seed] seeded n = 8/10 (cube-asserted) and n = 12 (R-model, '
          f'first 6 pairs cube-asserted); seed {R_SEED}')
    rng = random.Random(R_SEED)
    for n, tries, mat_cap in ((8, 200, 6), (10, 90, 6), (12, 400, 4)):
        t1 = time.time()
        stats = collections.Counter()
        ncap = 0
        cube_left = 10 ** 9 if n <= 10 else 6
        for sp in seeded_shapes(n, tries, rng):
            oidx, mats, capped = pairs_of(sp, n, mat_cap)
            ncap += 1 if capped else 0
            for mat in mats:
                sweep_pair(sp, n, mat, oidx, cube_left > 0, stats)
                cube_left -= 1
        print(f'    (n = {n}: tries {tries}, matchings capped at {mat_cap} '
              f'on {ncap} shapes -- CAP, disclosed)')
        report(f'n = {n} seeded', stats, t1)
    print(f'[--seed] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GPR-3] --hunt ---------------

def leg_hunt(args):
    t0 = time.time()
    print(f'[--hunt] the hunt sentence, R-model exact; two pools per n: '
          f'seeded habitat shapes (all O <= M matchings) and the NEW '
          f'cell-targeted (F, M) sampler; caps disclosed; '
          f'seed {R_SEED + 1}')
    rng = random.Random(R_SEED + 1)
    # pool 1: seeded habitat shapes, every O <= M matching
    for n, tries in ((14, 300),):
        t1 = time.time()
        stats = collections.Counter()
        for sp in seeded_shapes(n, tries, rng):
            oidx, mats, _c = pairs_of(sp, n)
            for mat in mats:
                sweep_pair(sp, n, mat, oidx, False, stats)
        print(f'    (n = {n}: seeded habitat pool, tries {tries} -- CAP, '
              f'disclosed)')
        report(f'n = {n} seeded-pool hunt', stats, t1)
    # pool 2: the cell-targeted sampler, both 2k strata
    for n, k2, tries, pair_cap in ((12, 2, 400, None), (12, 4, 400, None),
                                   (14, 2, 300, None), (14, 4, 300, None),
                                   (16, 2, 200, 30), (16, 4, 150, 20),
                                   (18, 2, 60, 4)):
        t1 = time.time()
        stats = collections.Counter()
        got = cell_shapes(n, k2, tries, rng)
        if pair_cap is not None and len(got) > pair_cap:
            got = got[:pair_cap]
        for (sp, mat) in got:
            sweep_pair(sp, n, mat, odd_idx(sp), False, stats)
        print(f'    (n = {n}, 2k = {k2}: cell sampler, tries {tries} -> '
              f'{len(got)} gated pairs'
              f'{f" (pair cap {pair_cap})" if pair_cap else ""} -- CAPS, '
              f'disclosed; an exhausted cap is not nonexistence)')
        report(f'n = {n}, 2k = {k2} cell hunt', stats, t1)
    print(f'[--hunt] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GPR-4] --mech ---------------

def leg_mech(args):
    t0 = time.time()
    print(f'[--mech] balance-law mechanism: among the structurally-maximum '
          f'reversal sets of a pair, how many reach a balanced pattern '
          f'(the law needs >= 1; the min ratio measures near-misses); '
          f'seed {R_SEED + 2}')
    rng = random.Random(R_SEED + 2)
    worst = None      # (nbal/nmax) minimum, as an exact pair of ints
    nz = 0
    npairs = 0
    ratio_hist = collections.Counter()
    for (_tag, n, specs) in stratum_cases():
        oidx, mats, _c = pairs_of(specs, n)
        for mat in mats:
            cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
            mstar, nmax, nbal = rmodel_diag(n, cycles, mpairs, oddends)
            npairs += 1
            assert nbal >= 1, 'balance law violated on the stratum'
            nz += 1 if nbal == nmax else 0
            key = (nbal, nmax)
            if worst is None or nbal * worst[1] < worst[0] * nmax:
                worst = key
            ratio_hist['all' if nbal == nmax else 'some'] += 1
    print(f'  stratum: {npairs} O<=M pairs; balance law asserted at every '
          f'one; max-R families reaching balance: {dict(ratio_hist)}; '
          f'worst (reaching / maximum) = {worst[0]}/{worst[1]}')
    # the (GR-103) control pair
    specs, n = gr103_specs(), 12
    oidx = odd_idx(specs)
    mat = frozenset({12, 13, 14, 15, 16, 17})
    cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
    mstar, nmax, nbal = rmodel_diag(n, cycles, mpairs, oddends)
    assert nbal >= 1
    print(f'  (GR-103) control: M* = {mstar}, structurally-max R sets '
          f'{nmax}, of which {nbal} reach a balanced pattern')
    # a seeded n = 12 cell pool
    got = cell_shapes(12, 2, 120, rng)
    w2 = None
    for (sp, mat) in got:
        oidx = odd_idx(sp)
        cycles, mpairs, oddends = cell_data(sp, 12, mat, oidx)
        _m, nmax, nbal = rmodel_diag(12, cycles, mpairs, oddends)
        assert nbal >= 1, 'balance law violated at n = 12'
        if w2 is None or nbal * w2[1] < w2[0] * nmax:
            w2 = (nbal, nmax)
    print(f'  n = 12 cell pool: {len(got)} pairs (tries 120 -- CAP, '
          f'disclosed); balance law asserted at every one; worst '
          f'(reaching / maximum) = {w2[0]}/{w2[1]}')
    print(f'[--mech] OK  [{time.time() - t0:.0f}s]')


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--cell', action='store_true')
    ap.add_argument('--seed', action='store_true')
    ap.add_argument('--hunt', action='store_true')
    ap.add_argument('--mech', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.validate:
        args.cell = args.seed = args.hunt = args.mech = True
    if not (args.cell or args.seed or args.hunt or args.mech):
        ap.error('pick a mode: --cell / --seed / --hunt / --mech / '
                 '--validate')
    if args.cell:
        leg_cell(args)
    if args.seed:
        leg_seed(args)
    if args.hunt:
        leg_hunt(args)
    if args.mech:
        leg_mech(args)


if __name__ == '__main__':
    main()
