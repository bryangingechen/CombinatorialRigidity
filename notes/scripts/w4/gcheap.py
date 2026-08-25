"""GCHEAP -- the thirty-first kernel-(K) ordinal: (GR-C2), the selection
clause of GFLOW's descent (spec: notes/Pencil-fanout.md S"GCHEAP --
thirty-first ordinal").

TARGET: (GR-C2) -- at some parity-optimal configuration with |delta| <= 2,
some majority-side odd branch is CHEAP: its flip is (GR-50)-feasible and it
is not a doubly-blocked matching branch (S(K-grid) Step G108(iv)).  Measured
0/96930 + 0/2114 + 0/371 by gflow --desc and unproven.  This pass proves it
UNDER A RESTRICTED QUANTIFIER with the exact boundary named, in the STRONGER
every-step form, via one identity and one capacity count:

  (GR-100) THE LONE-DART IDENTITY AND THE BLOCKED-END CAPACITY.  At any
  admissible z of a cubic loop-free hub multigraph (colour 0 = A,
  delta = a - b signed):

    (i)  every hub has 1 or 2 A-darts, and counting A-darts branchwise
         (|H| + 2a of them) against 2n - #{v : one A-dart} gives the EXACT
         identity   #{v : exactly one A-dart} = n/2 - delta;
    (ii) a BLOCKED END of a majority-side branch (the end at which the
         branch carries the minority dart, (GR-86)(i)) is a lone-
         majority-dart hub, and each hub hosts AT MOST ONE blocked end
         (its minority dart is unique); hence
    (iii) sum over majority-side branches of #blocked ends <= n/2 - |delta|,
         and in particular
             #doubly-blocked majority branches <= floor((n - 2|delta|)/4).
  (--cap)

  (GR-101) THE SELECTION COROLLARY.  (GR-99)(ii) gives >= |delta| feasible
  majority flips at every unbalanced admissible configuration; a cheap
  branch is a feasible one that is not doubly-blocked-in-M, so at every
  unbalanced admissible configuration and EVERY perfect matching M

      #cheap majority branches >= |delta| - floor((n - 2|delta|)/4),

  which is >= 1 whenever n < 6|delta|.  At |delta| = 2 that is all of
  n <= 10: the every-step form of (GR-C2) is a THEOREM there (no
  parity-optimality needed), the landed 96930/2114/371 censuses become
  theorems, and the first possible failure moves from n_hub = 8 (Step
  G108(v)'s cell, now PROVABLY empty) to n_hub = 12.  (--sel)

  (GR-102) THE BOUNDARY IS TIGHT.  An explicit constructed habitat shape at
  n_hub = 12, 2k = 2 (gated by cflank.cubic_habitat) carries an admissible
  unbalanced configuration at which BOTH majority branches are feasible
  doubly-blocked matching branches -- the every-step form FAILS at exactly
  n = 6|delta|.  The same mode audits the full 2^18 z-cube at that
  (shape, M): whether the witness is parity-optimal, and whether (GR-C2)
  AS POSED (the parity-optimal quantifier) survives there.  (--bnd)

Modes:
  --cap      (GR-100): the identity and the capacity, per admissible
             configuration (matching-free sentences) -- stratum
             (EXHAUSTIVE, full 2^|E| cube per shape) + V8 + seeded
             n = 8/10; the per-hub injection asserted hubwise; the
             doctored capacity (bound - 1) reported as the F13 control.
  --sel      (GR-101): the cheap-count lower bound at EVERY unbalanced
             admissible configuration x perfect matching (a NEW
             quantifier: the landed (GR-89)(iv) census is parity-optimal-
             only) -- stratum (EXHAUSTIVE) + V8 + seeded n = 8/10;
             (GR-99)'s >= |delta| feasible majority flips re-asserted as
             the consumed input.
  --bnd      (GR-102): the constructed n_hub = 12 witness (habitat-gated),
             its every-step failure asserts, the full-cube parity
             audit at its (shape, M), and a seeded n = 12 hunt for
             further witnesses (tries capped, disclosed).
  --validate all three, in the order above.

The (GR-100)/(GR-101) sentences are configuration-level and are asserted at
the configuration level; nothing here re-runs gflow --desc's landed
parity-optimal censuses (the sentences here quantify over ALL unbalanced
admissible configurations, a strictly larger set, and the parity-optimal
figures are cited, not re-measured).

Rank-free throughout: gexist.fully_good_rank is never imported or called
and no d_fg claim is made anywhere ((a') / input (Y) untouched).  Exact
integers / GF(2) throughout; no floating point; every rng seeded with the
seed printed; nothing samples a placement (S(K-clos) (AC-9)) -- every
sampler draws a GRAPH.  Wall-clock [Ns] annotations are non-deterministic;
every other byte is seed-stable.
"""
import argparse
import collections
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

# the eleven moved balance-layer devices: imported from gridbal_common
# DIRECTLY (the 2026-08-25 move-down; not via the sibling re-exports)
from gridbal_common import (branches_at, feas_flip, feasible_at, imb_of,   # noqa: E402
                            odd_idx, seeded_shapes, stratum_cases, v8_specs)
from gbal import (assign_feasible, z_admissible, z_of_orientation,         # noqa: E402
                  z_pattern, z_to_map)
from gdesc import majority_of                                              # noqa: E402
from gflow import adm_cube, block_ends_at, f_layers                        # noqa: E402
from gorient import perfect_matchings                                      # noqa: E402
from cflank import cubic_habitat                                           # noqa: E402

R_SEED = 20260825


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  `lone_hubs` counts the
# lone-majority-dart hubs off the cube's own majority map c (c[v] = 1 iff
# hub v has exactly one A-dart, since three darts split 2-1); `maj_data`
# the per-configuration majority-side blocked-end census; `cheap_of` the
# Step G108(iv) cheap-branch list at one (configuration, matching);
# `tight_specs` the constructed n = 12 boundary candidate; `tight_z` its
# tight orientation as an explicit z.


def lone_hubs(c, n, side):
    """#{v : exactly one `side`-dart}: side 0 (A) counts c[v] = 1 (majority
    B means the A-dart is the lone one), side 1 the complement."""
    k = sum(1 for v in range(n) if c[v] == 1)
    return k if side == 0 else n - k


def maj_data(specs, oidx, mm, c, pat, k2):
    """Per configuration: (delta, majority spec-indices, per-branch blocked-
    end counts, the blocked-end hub count).  None at a balanced pattern."""
    delta = imb_of(k2, pat)
    if delta == 0:
        return None
    maj = majority_of(oidx, pat, delta)
    majset = set(maj)
    be = {i: len(block_ends_at(specs, mm, i)) for i in maj}
    hubs = [v for v in mm if mm[v][0] in majset]
    return delta, maj, be, hubs


def cheap_of(specs, n, oidx, pat, maj, be, mat, fcache):
    """Step G108(iv): the cheap majority branches at one (z, M) -- flip
    (GR-50)-feasible AND not a doubly-blocked matching branch.  Returns
    (cheap list, feasible count, doubly-blocked-matching list)."""
    pos = {i: j for j, i in enumerate(oidx)}
    cheap, nf, dbm = [], 0, []
    for i in maj:
        key = (pat, pos[i])
        if key not in fcache:
            fcache[key] = feas_flip(specs, n, oidx, pat, pos[i])
        feas = fcache[key]
        nf += 1 if feas else 0
        double_m = (i in mat and be[i] == 2)
        if double_m:
            dbm.append(i)
        if feas and not double_m:
            cheap.append(i)
    return cheap, nf, dbm


def tight_specs():
    """The constructed n_hub = 12 boundary candidate: F = the 12-cycle
    0,4,1,5,2,6,3,7,8,9,10,11 (branches length 2, except (8,9) and (10,11)
    at length 4), the two ODD branches gamma1 = (0,1), gamma2 = (2,3) at
    length 3, and the four even matching branches (4,8),(5,9),(6,10),
    (7,11) at length 2.  Excess 1+1+2+2 = 6.  M = {gamma1, gamma2, the
    four}; U = {0,1,2,3} spans no branch outside {gamma1, gamma2}."""
    cyc = [0, 4, 1, 5, 2, 6, 3, 7, 8, 9, 10, 11]
    fedges = [(cyc[t], cyc[(t + 1) % 12]) for t in range(12)]
    specs = [(u, w, 4 if (u, w) in ((8, 9), (10, 11)) else 2)
             for (u, w) in fedges]
    specs += [(0, 1, 3), (2, 3, 3)]                       # gamma1, gamma2
    specs += [(4, 8, 2), (5, 9, 2), (6, 10, 2), (7, 11, 2)]
    return specs


def tight_z(specs, n, oidx):
    """The tight configuration of `tight_specs`: pattern all-A, every even
    branch's A-end forced off U = {0,1,2,3} with in-load exactly 2 on
    every other hub (the (GR-100)-extremal profile).  Built directly:
    z[i] = 0 iff the A-end is the u-end of branch i."""
    aend = {(0, 4): 4, (4, 1): 4, (1, 5): 5, (5, 2): 5, (2, 6): 6,
            (6, 3): 6, (3, 7): 7, (7, 8): 8, (8, 9): 9, (9, 10): 10,
            (10, 11): 11, (11, 0): 11,
            (4, 8): 8, (5, 9): 9, (6, 10): 10, (7, 11): 7}
    z = []
    oset = set(oidx)
    for i, (u, w, _L) in enumerate(specs):
        if i in oset:
            z.append(0)                                    # all-A pattern
        else:
            z.append(0 if aend[(u, w)] == u else 1)
    return z


def hist(d):
    return dict(sorted(d.items(), key=lambda t: (t[0] is None, t[0])))


def legs(rng, with_n12=False):
    """The sweep legs: the stratum (EXHAUSTIVE), V8, seeded n = 8/10
    (gflow.seeded_shapes = balb.rand_habitat behind the (GR-25) cut
    criterion; tries as in gflip, seeds printed by the caller)."""
    out = [('stratum', list(stratum_cases()))]
    out.append(('V8', [('V8', 8, v8_specs())]))
    for n, tries in ((8, 200), (10, 90)):
        shapes = seeded_shapes(n, tries, rng)
        out.append((f'n={n} seeded', [(f'n{n}#{j + 1}', n, sp)
                                      for j, sp in enumerate(shapes)]))
    return out


# --------------------------------------------- [GCH-1] --cap  (GR-100) ------

def leg_cap(args):
    t0 = time.time()
    rng = random.Random(R_SEED)
    print(f'[--cap] (GR-100) identity + blocked-end capacity; seed {R_SEED}')
    worst = {}     # per leg: max blocked-end count minus capacity (<= 0)
    attain = {}    # per leg: #configs attaining the capacity exactly
    for (leg, cases) in legs(rng):
        ncfg = nunb = 0
        att = 0
        wgap = None
        dbl_hist = collections.Counter()
        for (_tag, n, specs) in cases:
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            k2 = len(oidx)
            for (z, mm, c, pat) in adm_cube(specs, n, binc, oidx):
                ncfg += 1
                delta = imb_of(k2, pat)
                # (GR-100)(i): the lone-dart identity, signed, both sides
                assert lone_hubs(c, n, 0) == n // 2 - delta, 'identity (A)'
                assert lone_hubs(c, n, 1) == n // 2 + delta, 'identity (B)'
                md = maj_data(specs, oidx, mm, c, pat, k2)
                if md is None:
                    continue
                nunb += 1
                delta, maj, be, hubs = md
                # (GR-100)(ii): each blocked end is a lone-majority hub --
                # for A-majority (delta > 0) the majority colour at that
                # hub is B, i.e. c[v] = 1; symmetric at delta < 0.  The
                # injection is per-hub: v carries ONE minority dart, so
                # the hub list has no repeats by construction; assert both.
                want = 1 if delta > 0 else 0
                for v in hubs:
                    assert c[v] == want, 'blocked end not a lone-dart hub'
                assert len(hubs) == len(set(hubs)), 'hub hosting two ends'
                cap_ = n // 2 - abs(delta)
                total = sum(be.values())
                assert total == len(hubs), 'blocked-end recount'
                # (GR-100)(iii): the capacity, and the double-block bound
                assert total <= cap_, 'blocked-end capacity violated'
                ndbl = sum(1 for i in maj if be[i] == 2)
                assert ndbl <= (n - 2 * abs(delta)) // 4, 'double capacity'
                dbl_hist[ndbl] += 1
                g = total - cap_
                wgap = g if wgap is None else max(wgap, g)
                if g == 0:
                    att += 1
        worst[leg] = wgap
        attain[leg] = att
        print(f'  leg {leg:12s}: {ncfg} admissible configurations, '
              f'{nunb} unbalanced; capacity gap max {wgap} '
              f'(attained at {att}); #doubly-blocked majority {hist(dbl_hist)}')
    # F13 control: the doctored capacity (bound - 1) must FAIL somewhere
    assert any(g == 0 for g in worst.values() if g is not None), \
        'doctored capacity (cap - 1) never separated: no attainment found'
    print(f'  F13: capacity attained on legs '
          f'{[k for k, g in worst.items() if g == 0]} -- the doctored bound '
          f'(cap - 1) FAILS there, so the constant is exact')
    print(f'[--cap] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GCH-2] --sel  (GR-101) ------

def leg_sel(args):
    t0 = time.time()
    rng = random.Random(R_SEED + 1)
    print(f'[--sel] (GR-101) cheap-count bound at EVERY unbalanced '
          f'admissible configuration x matching; seed {R_SEED + 1}')
    for (leg, cases) in legs(rng):
        pairs = ninst = 0
        mincheap = None
        minslack = None
        dbm_hist = collections.Counter()
        capped = 0
        mat_cap = None if leg == 'stratum' else 6
        for (_tag, n, specs) in cases:
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            k2 = len(oidx)
            cube = [t for t in adm_cube(specs, n, binc, oidx)
                    if imb_of(k2, t[3]) != 0]
            mats = perfect_matchings(specs)
            if mat_cap is not None and len(mats) > mat_cap:
                mats = mats[:mat_cap]
                capped += 1
            pairs += len(mats)
            fcache = {}
            oset = set(oidx)
            for mat in mats:
                base = {}
                for i in mat:
                    (u, w, _L) = specs[i]
                    base[u] = (i, 0)
                    base[w] = (i, 1)
                matodd = [oidx.index(i) for i in mat if i in oset]
                taxof = {}
                for (z, mm, c, pat) in cube:
                    ninst += 1
                    delta, maj, be, _hubs = \
                        maj_data(specs, oidx, mm, c, pat, k2)
                    # (GR-102)(i): the stall tax at every configuration
                    if pat not in taxof:
                        am = sum(1 for j in matodd if not (pat >> j) & 1)
                        taxof[pat] = 2 * am - len(matodd)
                    d = sum(1 for v in range(n) if mm[v] != base[v])
                    assert d >= abs(taxof[pat] + delta), 'stall tax'
                    cheap, nf, dbm = cheap_of(
                        specs, n, oidx, pat, maj, be, mat, fcache)
                    # the consumed input, re-asserted: (GR-99)(ii)
                    assert nf >= abs(delta), '(GR-99) violated'
                    bound = abs(delta) - (n - 2 * abs(delta)) // 4
                    # (GR-101): the cheap-count lower bound
                    assert len(cheap) >= bound, 'cheap bound violated'
                    if n < 6 * abs(delta):
                        assert len(cheap) >= 1, 'every-step (GR-C2) fails'
                    dbm_hist[len(dbm)] += 1
                    mc = len(cheap)
                    mincheap = mc if mincheap is None else min(mincheap, mc)
                    sl = mc - bound
                    minslack = sl if minslack is None else min(minslack, sl)
        print(f'  leg {leg:12s}: {pairs} (shape, matching) pairs '
              f'({capped} matching-capped at {mat_cap}), {ninst} unbalanced '
              f'(configuration, matching) instances; min #cheap {mincheap}; '
              f'min slack over the bound {minslack}; '
              f'#feasible-doubly-blocked-matching {hist(dbm_hist)}')
    print('  the landed (GR-89)(iv) censuses (96930 + 2114 + 371, '
          'parity-optimal) are implied by the sentence asserted here '
          '(all unbalanced configurations) and are cited, not re-run')
    print(f'[--sel] OK  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GCH-3] --bnd  (GR-102) ------

def audit_pair(specs, n, mat, tag):
    """Full 2^|E| audit at one (shape, matching): d_par(M), d_adm(M), the
    parity-optimal |delta| = 2 configurations and their cheap counts."""
    binc = branches_at(specs, n)
    oidx = odd_idx(specs)
    k2 = len(oidx)
    base = {}
    for i in mat:
        (u, w, _L) = specs[i]
        base[u] = (i, 0)
        base[w] = (i, 1)
    cube = adm_cube(specs, n, binc, oidx)
    f, dpar = f_layers(cube, n, base)
    bal = [p for p in f if imb_of(k2, p) == 0]
    dadm = min(f[p] for p in bal) if bal else None
    fcache = {}
    popt = pbal = 0
    stall = 0
    worst_bad = None
    amof = {}
    for (z, mm, c, pat) in cube:
        d = sum(1 for v in range(n) if mm[v] != base[v])
        delta = imb_of(k2, pat)
        # (GR-102)(i): the stall tax dist >= |a_M - b_M + delta|, at EVERY
        # admissible configuration of this (shape, M)
        if pat not in amof:
            am = sum(1 for i in mat if i in set(oidx)
                     and not (pat >> oidx.index(i)) & 1)
            bm = sum(1 for i in mat if i in set(oidx)
                     and (pat >> oidx.index(i)) & 1)
            amof[pat] = am - bm
        assert d >= abs(amof[pat] + delta), 'stall tax violated'
        if d != dpar:
            continue
        if delta == 0:
            pbal += 1
            continue
        if abs(delta) != 2:
            continue
        popt += 1
        _delta, maj, be, _hubs = maj_data(specs, oidx, mm, c, pat, k2)
        cheap, _nf, dbm = cheap_of(specs, n, oidx, pat, maj, be, mat, fcache)
        if not cheap:
            stall += 1
            prices = sorted(
                f[pat ^ (1 << oidx.index(i))] - dpar for i in maj
                if pat ^ (1 << oidx.index(i)) in f)
            worst_bad = (pat, prices)
    print(f'    audit {tag}: d_par(M) = {dpar}, d_adm(M) = {dadm}, '
          f'per-matching gap {None if dadm is None else dadm - dpar}; '
          f'parity-optimal configurations: {pbal} balanced, {popt} at '
          f'|delta| = 2 of which {stall} STALLED (no cheap majority branch)'
          + (f'; a stalled pattern {worst_bad[0]} has exact majority one-'
             f'flip prices {worst_bad[1]} -- the DESCENT STEP survives the '
             f'stall' if worst_bad else ''))
    return dpar, dadm, popt, pbal, stall


def leg_bnd(args):
    t0 = time.time()
    print(f'[--bnd] (GR-102) the n_hub = 12 boundary; seed {R_SEED + 2}')
    # ---- the constructed candidate ---------------------------------------
    specs = tight_specs()
    n = 12
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    ok = cubic_habitat(n, hedges, lens)
    print(f'  constructed shape: cubic_habitat gate -> {ok}')
    assert ok, 'constructed candidate fails the (GR-25) habitat gate'
    binc = branches_at(specs, n)
    oidx = odd_idx(specs)
    k2 = len(oidx)
    assert k2 == 2 and set(oidx) == {12, 13}, 'odd branches misplaced'
    mat = frozenset({12, 13, 14, 15, 16, 17})
    ends = set()
    for i in mat:
        (u, w, _L) = specs[i]
        assert u not in ends and w not in ends, 'matching not a matching'
        ends |= {u, w}
    assert ends == set(range(12)), 'matching not perfect'
    z = tight_z(specs, n, oidx)
    assert z_admissible(specs, n, binc, z), 'tight z inadmissible'
    mm, c = z_to_map(specs, n, binc, z)
    pat = z_pattern(z, oidx)
    delta = imb_of(k2, pat)
    assert pat == 0 and delta == 2, 'tight z not the all-A pattern'
    # (GR-100) at the witness: the identity is TIGHT
    assert lone_hubs(c, n, 0) == n // 2 - delta == 4
    _d, maj, be, _h = maj_data(specs, oidx, mm, c, pat, k2)
    assert sorted(maj) == [12, 13]
    for i in maj:
        assert i in mat and be[i] == 2, 'majority branch not DBM'
    fcache = {}
    cheap, nf, dbm = cheap_of(specs, n, oidx, pat, maj, be, mat, fcache)
    assert nf == 2, 'a majority flip is infeasible (b = 0 corner broken?)'
    assert len(dbm) == 2 and not cheap, 'witness is not a total failure'
    print('  WITNESS: unbalanced admissible configuration (all-A, '
          'delta = 2) at which BOTH majority branches are feasible '
          'doubly-blocked matching branches -- 0 cheap branches: the '
          'every-step form of (GR-C2) FAILS at n_hub = 12 = 6|delta|; '
          'the (GR-101) boundary is TIGHT')
    base = {}
    for i in mat:
        (u, w, _L) = specs[i]
        base[u] = (i, 0)
        base[w] = (i, 1)
    dist_z = sum(1 for v in range(n) if mm[v] != base[v])
    print(f'    dist(z_tight, M) = {dist_z} '
          f'(predicted = #even matching branches = 4; the (GR-102) tax '
          f'floor a_M - b_M + delta = 4 is met with equality)')
    assert dist_z == 4
    dpar, dadm, popt, pbal, stall = audit_pair(
        specs, n, mat, 'constructed (M)')
    assert dist_z == dpar and stall > 0, 'witness not parity-optimal'
    print(f'    so z_tight IS parity-optimal: the PER-CONFIGURATION form '
          f'of (GR-C2) is REFUTED at n_hub = 12.  The AS-POSED form '
          f'(existential over parity-optimal configurations) '
          f'{"still HOLDS" if popt - stall > 0 or pbal > 0 else "FAILS"} '
          f'at this (shape, M): {popt - stall} cheap-carrying parity-'
          f'optimal |delta| = 2 configurations, {pbal} balanced parity-'
          f'optimal ones (gap {dadm - dpar})')
    # ---- seeded hunt for further witnesses -------------------------------
    rng = random.Random(R_SEED + 2)
    tries = 400
    shapes = [sp for sp in seeded_shapes(12, tries, rng)
              if len(odd_idx(sp)) == 2]
    print(f'  seeded n = 12 hunt: {len(shapes)} habitat shapes with '
          f'2k = 2 from {tries} tries (CAP, disclosed)')
    found = 0
    audited = 0
    for si, sp in enumerate(shapes):
        binc = branches_at(sp, n)
        oidx = odd_idx(sp)
        (u1, w1, _L1) = sp[oidx[0]]
        (u2, w2, _L2) = sp[oidx[1]]
        U = {u1, w1, u2, w2}
        if len(U) < 4:
            continue                       # odd branches share a hub
        uu = [i for i, (u, w, _L) in enumerate(sp)
              if u in U and w in U and i not in oidx]
        if uu:
            continue                       # an even U-U branch: unfillable
        for mat in perfect_matchings(sp):
            if not (oidx[0] in mat and oidx[1] in mat):
                continue
            lo = [0 if v in U else 2 for v in range(n)]
            hi = list(lo)
            oset = set(oidx)
            even = [i for i in range(len(sp)) if i not in oset]
            edges = [(sp[i][0], sp[i][1]) for i in even]
            asg, _R = assign_feasible(n, edges, lo, hi)
            if asg is None:
                continue
            z = z_of_orientation(sp, oidx, [0, 0], even, asg)
            assert z_admissible(sp, n, binc, z)
            mm, c = z_to_map(sp, n, binc, z)
            pat = z_pattern(z, oidx)
            _d, maj, be, _h = maj_data(sp, oidx, mm, c, pat, 2)
            fc = {}
            cheap, nf, dbm = cheap_of(sp, n, oidx, pat, maj, be, mat, fc)
            assert nf == 2 and len(dbm) == 2 and not cheap
            found += 1
            if audited < 2:
                audited += 1
                audit_pair(sp, n, mat, f'seeded #{si + 1}')
            break
    print('  every seeded witness above is an every-step failure; the '
          'audited pairs report whether the as-posed existential also '
          'fails there (a stall count equal to the |delta| = 2 optimum '
          'count WITH no balanced optimum would be required)')
    print(f'  seeded hunt: {found} further every-step witnesses '
          f'(first {audited} audited in full)')
    print(f'[--bnd] OK  [{time.time() - t0:.0f}s]')


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--cap', action='store_true')
    ap.add_argument('--sel', action='store_true')
    ap.add_argument('--bnd', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.validate:
        args.cap = args.sel = args.bnd = True
    if not (args.cap or args.sel or args.bnd):
        ap.error('pick a mode: --cap / --sel / --bnd / --validate')
    if args.cap:
        leg_cap(args)
    if args.sel:
        leg_sel(args)
    if args.bnd:
        leg_bnd(args)


if __name__ == '__main__':
    main()
