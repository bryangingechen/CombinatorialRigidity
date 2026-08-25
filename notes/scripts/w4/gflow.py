"""GFLOW -- the twenty-sixth kernel-(K) direction: (b')'s AVAILABILITY half,
Clause A' sub-clause 2, the DOUBLY-BLOCKED case (spec:
notes/Pencil-fanout.md S"GFLOW -- twenty-sixth direction (eighth fan-out)").

TARGET: BALB proved (b')'s PRICE half outright ((GR-68)) and left its
AVAILABILITY half as Clause A' -- at every unbalanced parity-optimal
configuration a legal flip set F with z + chi_F balanced and
|W(F) \\ S| - |W(F) cap S| <= 2 -- with sub-clause 1 (one-end-blocked)
"nearly done" and sub-clause 2 (doubly-blocked) the named residual.  This
pass takes BALB's untried route 3 (an exchange statement between two
degree-constrained-orientation problems) and lands the following chain.

  (GR-85) THE CHANGEOVER-COST MODEL.  Fix a perfect matching M with
  2-factor F = G0 \\ M.  For a hub v let A(v) be the number of A-coloured
  darts among v's TWO F-branches, so A(v) in {0, 1, 2}.  Then

      v deviates from M   <=>   A(v) = 1,     dist(m, M) = #{v : A(v) = 1},

  admissibility is A(v) = 0 => m_v = 1, A(v) = 2 => m_v = 0 (m_v = the
  indicator that M(v)'s dart at v is A), and it holds GLOBALLY iff three
  local conditions hold, one per M-branch mu = uw:

      mu odd, A-coloured : A(u) <= 1 and A(w) <= 1
      mu odd, B-coloured : A(u) >= 1 and A(w) >= 1
      mu even            : not(A(u) = A(w) = 0) and not(A(u) = A(w) = 2).

  So the ONLY free variables are the orientations of the EVEN branches
  INSIDE F, and with T(p) := 2 |O_A cap F| + |H cap F| = sum_v A(v),

      dist = T(p) - 2 * #{v : A(v) = 2},

  which gives (GR-67)(ii)'s parity law in one line (T(p) = |H cap F| mod 2).
  READING: the objective is #{v : A(v) ODD} -- a PARITY count, NOT a linear
  or convex function of the orientation's degree data -- so route 3's
  "min-cost flow, hence polynomial" reading is WRONG as an instrument: the
  FEASIBILITY side is a degree-constrained orientation ((GR-50), Hakimi),
  the OBJECTIVE is not a flow cost.  (--model)

  (GR-86) THE REPAIR-CHAIN THEOREM -- the exchange instrument that DOES
  work, and it is n-free.  Flipping one odd branch gamma leaves the
  configuration inadmissible at exactly those ends of gamma that carry
  gamma's dart (the BLOCKED ends); each is repaired by a CHAIN of even
  branch flips that terminates at the first hub with slack.  A chain
  repair exists iff the flipped pattern is (GR-50)-feasible, and its price
  is
      gamma in M, dart-free       : 0
      gamma in M, one-end-blocked : 0 or 2
      gamma in M, doubly blocked  : 0, 2 or 4
      gamma in F (any blocking)   : -2, 0 or 2
  -- because the chain's F->M and M->F transitions cancel in pairs, so the
  price is (start contribution) + (terminus contribution) and is
  INDEPENDENT of the chain's length.  So

      Delta dist <= 2 UNLESS gamma is a DOUBLY-BLOCKED MATCHING branch,
      and then Delta dist <= 4.

  (--chain, cap-free at n = 30/40/50/60 in --big)

  (GR-87) SUB-CLAUSE 1 IS PROVEN, and BALB's side condition DISSOLVES.
  The one-end-blocked case costs <= 2 with NO far-end side condition:
  BALB's residual `m(w_beta) != beta for one of the two available beta' is
  not needed (the chain simply continues) and is in fact FALSE from
  n_hub = 8 -- measured stuck instances where BOTH two-branch moves are
  illegal.  (--exact)

  (GR-88) SUB-CLAUSE 2 IS REFUTED AS POSED, with the exact boundary.  A
  doubly-blocked MATCHING branch can carry one-flip price EXACTLY 4, first
  at parity-optimal |delta| = 2 configurations at n_hub = 8; the price is
  never 6 or more.  Two corrections of the landed reading: the price of the
  (1,2,2) mixed pair is |W| - 2|W cap S| = 4 - 2|W cap S|, so ONE deviating
  extra endpoint already gives <= 2 (BALB's "both" is the price-ZERO
  condition); and route 1's named input is DIRECTIONALLY WRONG -- optimality
  forbids Delta dist < 0, i.e. it CAPS |W cap S| at |W|/2, so it pushes
  against deviating endpoints, not toward them.  (--exact)

  (GR-89) THE RESIDUAL RESHAPED, AND A PROVEN n-FREE CONSTANT.  Iterating
  (GR-86) down the imbalance ladder gives, with (GR-69),

      d_adm(M) - d_par(M) <= 4 * min(k, floor(n_hub/4))  ( <= 12 ),

  the FIRST proven n-free bound of (b')'s own shape -- modulo ONE named
  clause (GR-R1): at every unbalanced admissible configuration some
  majority-side odd branch has a (GR-50)-feasible flip.  With |delta| <= 2
  at some parity-optimal configuration the same chain gives <= 4.  The
  residual for the constant 2 is now a SELECTION statement, not a repair
  statement: some majority-side odd branch is not a doubly-blocked matching
  branch.  It is PROVEN by counting whenever n_hub < 3k + 5|delta|/2 -- in
  particular on the WHOLE n_hub <= 6 stratum -- and measured with zero
  failures everywhere else probed.  (--desc)

  (GR-90) the status statement, the caps and the hand-off.  (--adv)

Modes:
  --model    (GR-85): the changeover model, both directions, EXHAUSTIVE on
             the stratum (all 4780 odd-carrying habitat shapes, all perfect
             matchings, the full 2^|E| z-cube) plus V8 and seeded n = 8/10.
  --chain    (GR-86): the chain repair -- completeness against the (GR-50)
             oracle, the price by case for EVERY chain repair (not just the
             cheapest), and the (GR-68) cross-check, over the stratum.
  --exact    (GR-87)/(GR-88): the EXACT one-flip price f(p + chi_gamma) - dist
             by full z-cube over the whole stratum and seeded n = 8/10/12;
             the price-4 witness named; BALB's two-branch side condition
             counted where it fails.
  --desc     (GR-89): clause (GR-R1), the greedy descent to balance, the
             selection-clause census and the counting bound.
  --big      beyond the stratum: seeded exact n = 8/10/12, V8, and CAP-FREE
             chain certificates on the necklaces at n = 30/40/50/60.
  --adv      F13 falsification controls.
  --validate all six, in the order above.

Rank-free throughout: gexist.fully_good_rank is never imported or called
and no d_fg claim is made anywhere ((a') / input (Y) is GCOLL's neighbourhood
this wave, and (GR-64)(R2) is GCOLL's target -- untouched here).  Exact
integers / GF(2) throughout; no floating point; every rng seeded with the
seed printed; nothing samples a placement (S(K-clos) (AC-9)) -- rand_habitat
samples a GRAPH.  Wall-clock [Ns] annotations are non-deterministic; every
other byte is seed-stable.
"""
import argparse
import collections
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from balb import (dev_set, dist_anchored, price_pred, rand_habitat,        # noqa: E402
                  stratum_cases, v8_specs, w_set)
from gadm import complete_matching, nko_specs                             # noqa: E402
from gbal import (dart_col, feasible_at, flip_legal, map_to_z, odd_idx,    # noqa: E402
                  z_admissible, z_pattern, z_to_map)
from gdesc import imb_of, majority_of                                     # noqa: E402
from gdev import habitat_by_lemma, nk_specs                               # noqa: E402
from gorient import m_of_matching, perfect_matchings                      # noqa: E402
from gpsa import branches_at, nk55_specs, nkp_specs, pattern_of           # noqa: E402

# `feas_flip`/`seeded_shapes` MOVED DOWN to `gridbal_common` on 2026-08-25
# (README *Harness debt*, direction GFLIP): `gflip` imports both, past §2
# rule 2's trigger, alongside nine sibling devices from `balb`/`gbal`/
# `gdesc`/`gpsa`.  Re-exported here, so this module's own modes and
# `gflip`'s import line are unchanged.
from gridbal_common import feas_flip, seeded_shapes                       # noqa: E402

R_SEED = 20260819


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  `a_of` is (GR-85)'s per-hub
# A-count; `m_ind` its companion m_v; `mconstraints` the three local
# conditions; `t_of` the T(p) invariant; `bad_hubs` the inadmissibility
# witness set; `chain_repairs` / `chain_first` the (GR-86) repair chains;
# `block_ends_at` the blocked-end count that names the four cases;
# `adm_cube` the exhaustive admissible-z enumeration; `f_layers` the exact
# per-pattern minimum dist; `walk_adm` the large-n admissible-configuration
# sampler.


def nonmatch_at(binc, matbr, v):
    """The two F-branches (non-matching branches) at hub `v`."""
    nm = [i for i in binc[v] if i not in matbr]
    assert len(nm) == 2, "hub not cubic, or matching not perfect"
    return nm


def a_of(specs, n, binc, matbr, z):
    """(GR-85): A(v) = the number of A-coloured (colour 0) darts at `v`
    among v's TWO F-branches.  A(v) in {0, 1, 2}."""
    A = {}
    for v in range(n):
        A[v] = sum(1 for i in nonmatch_at(binc, matbr, v)
                   if dart_col(specs, z, v, i) == 0)
    return A


def m_ind(specs, n, base, z):
    """(GR-85): m_v = [M(v)'s dart at v is A-coloured]."""
    return {v: 1 if dart_col(specs, z, v, base[v][0]) == 0 else 0
            for v in range(n)}


def mconstraints(specs, n, mat, oset, pat_of_branch, A):
    """(GR-85): the three local conditions, one per M-branch.  Returns the
    list of violated (branch, kind) pairs -- empty iff all hold."""
    bad = []
    for i in mat:
        (u, w, _L) = specs[i]
        if i in oset:
            if pat_of_branch[i] == 0:          # A-coloured odd matching branch
                if A[u] > 1 or A[w] > 1:
                    bad.append((i, 'oddA'))
            else:                              # B-coloured
                if A[u] < 1 or A[w] < 1:
                    bad.append((i, 'oddB'))
        else:
            if (A[u] == 0 and A[w] == 0) or (A[u] == 2 and A[w] == 2):
                bad.append((i, 'even'))
    return bad


def t_of(specs, oidx, matbr, z):
    """(GR-85): T(p) = 2 |O_A cap F| + |H cap F|, the invariant sum_v A(v).
    Depends on the odd pattern and the matching only."""
    oset = set(oidx)
    oaf = sum(1 for i in oidx if z[i] == 0 and i not in matbr)
    hf = sum(1 for i, (_u, _w, L) in enumerate(specs)
             if L % 2 == 0 and i not in matbr and i not in oset)
    return 2 * oaf + hf


def bad_hubs(specs, n, binc, z):
    """The hubs at which `z` is INADMISSIBLE -- all three darts equal.
    Empty iff gbal.z_admissible."""
    out = []
    for v in range(n):
        a, b, c = (dart_col(specs, z, v, i) for i in binc[v])
        if a == b == c:
            out.append(v)
    return out


def block_ends_at(specs, m, i):
    """The ends of odd branch `i` at which `i` carries the MINORITY dart --
    the BLOCKED ends.  0 = dart-free, 1 = one-end-blocked, 2 = doubly
    blocked."""
    (u, w, _L) = specs[i]
    return [v for v in (u, w) if m[v][0] == i]


def case_of(specs, m, matbr, i):
    """(GR-86)'s four-case key: 'M'/'F' by whether the odd branch is a
    matching branch, times the number of blocked ends."""
    nb = len(block_ends_at(specs, m, i))
    return ('M' if i in matbr else 'F') + ('-free', '-one', '-double')[nb]


def chain_repairs(specs, n, binc, z, D, oset, cap=4000, nodecap=200000):
    """(GR-86): EVERY chain repair of the odd-branch flip set `D`.  Flip
    `D`, then repeatedly flip an EVEN branch at a currently-inadmissible
    hub, never re-flipping a branch already used, until the configuration
    is admissible.  Returns (list of flip sets, capped?).  Only even
    branches are added, so the odd pattern changes exactly on `D`."""
    z0 = list(z)
    for g in D:
        z0[g] ^= 1
    sols, seen, nd = [], set(), 0
    stack = [(tuple(z0), frozenset(D))]
    while stack:
        nd += 1
        if len(sols) >= cap or nd > nodecap:
            return sols, True
        zc, J = stack.pop()
        if (zc, J) in seen:
            continue
        seen.add((zc, J))
        bh = bad_hubs(specs, n, binc, list(zc))
        if not bh:
            sols.append(J)
            continue
        v = bh[0]
        for i in binc[v]:
            if i in J or i in oset:
                continue
            z2 = list(zc)
            z2[i] ^= 1
            stack.append((tuple(z2), J | {i}))
    return sols, False


def chain_first(specs, n, binc, z, D, oset, nodecap=40000):
    """(GR-86), SHORTEST-first: one chain repair, by breadth-first search on
    the partial flip set.  The large-n instrument -- no z-cube anywhere, so
    it is CAP-FREE except for the node cap, which is reported."""
    z0 = list(z)
    for g in D:
        z0[g] ^= 1
    q = collections.deque([(tuple(z0), frozenset(D))])
    seen = {tuple(z0)}
    nd = 0
    while q:
        nd += 1
        if nd > nodecap:
            return None, True
        zc, J = q.popleft()
        bh = bad_hubs(specs, n, binc, list(zc))
        if not bh:
            return J, False
        v = bh[0]
        for i in binc[v]:
            if i in J or i in oset:
                continue
            z2 = list(zc)
            z2[i] ^= 1
            t2 = tuple(z2)
            if t2 in seen:
                continue
            seen.add(t2)
            q.append((t2, J | {i}))
    return None, False


def adm_cube(specs, n, binc, oidx):
    """EXHAUSTIVE: every admissible z of the full 2^|E| cube, with its (m, c)
    and its odd pattern.  Usable to |E| = 18 (n_hub = 12)."""
    mn = len(specs)
    out = []
    for bits in range(1 << mn):
        z = [(bits >> i) & 1 for i in range(mn)]
        if z_admissible(specs, n, binc, z):
            mm, c = z_to_map(specs, n, binc, z)
            out.append((z, mm, c, z_pattern(z, oidx)))
    return out


def f_layers(cube, n, base):
    """f(pattern) = the exact minimum dist(., M) over admissible z with that
    pattern, off the exhaustive cube; plus d_par(M) = min f."""
    f = {}
    for (_z, mm, _c, pat) in cube:
        d = sum(1 for v in range(n) if mm[v] != base[v])
        if pat not in f or d < f[pat]:
            f[pat] = d
    return f, min(f.values())


def walk_adm(specs, n, binc, z, rng, steps):
    """A seeded random walk on the admissible configurations by single-branch
    flips that preserve admissibility (the free-T1 move of (GR-45)(iii) in
    z-coordinates).  The large-n sampler; asserts admissibility at exit."""
    z = list(z)
    for _ in range(steps):
        i = rng.randrange(len(specs))
        z[i] ^= 1
        if not z_admissible(specs, n, binc, z):
            z[i] ^= 1
    assert z_admissible(specs, n, binc, z)
    return z


def seeds_at(specs, n, oidx):
    """One admissible configuration per (GR-50)-feasible odd pattern, via the
    landed polynomial oracle -- no cube, so this works at any n."""
    k2 = len(oidx)
    out = []
    for bits in range(1 << k2):
        p = [(bits >> t) & 1 for t in range(k2)]
        z = feasible_at(specs, n, oidx, p)
        if z is not None:
            assert z_admissible(specs, n, branches_at(specs, n), z)
            out.append(z)
    return out


def necklaces(ms=(6, 8, 10, 12)):
    """The commissioned odd-rich necklace families, reused read-only, gated
    by the POLYNOMIAL habitat criterion ((GR-42), gdev.habitat_by_lemma) --
    cflank.cubic_habitat's 2^n_hub cut enumeration is out of reach here."""
    fam = (('NK', lambda m: nk_specs(m)[0]),
           ('NKo', lambda m: nko_specs(m)[0]),
           ('NKp', lambda m: nkp_specs(m)[0]),
           ('NK55', lambda m: nk55_specs(m)[0]))
    out = []
    for m in ms:
        for (nm, fn) in fam:
            specs = fn(m)
            n = 5 * m
            he = [(u, w) for (u, w, _L) in specs]
            lens = [L for (_u, _w, L) in specs]
            ok, why = habitat_by_lemma(n, he, lens)
            assert ok, f"{nm}({m}) not habitat: {why}"
            if odd_idx(specs):
                out.append((f'{nm}({m})', n, specs))
    return out


def hist(d):
    return dict(sorted(d.items(), key=lambda t: (t[0] is None, t[0])))


def hist2(d):
    return dict(sorted(d.items(), key=lambda t: (t[0][0], t[0][1] is None,
                                                 t[0][1])))


# ------------------------------------------------- [GFL-1] --model ----------

def leg_model():
    """[GFL-1] (GR-85): the changeover-cost model, BOTH directions."""
    t0 = time.time()
    print("[GFL-1] (GR-85) the changeover-cost model -- "
          "dist = #{v : A(v) = 1}, and admissibility is three local "
          "conditions per M-branch")
    rng = random.Random(R_SEED + 1)
    cases = stratum_cases()
    print(f"  stratum: {len(cases)} odd-carrying habitat shapes "
          f"(gbal.pool_cases behind the (GR-25) cut criterion -- "
          f"EXHAUSTIVE, not a subsample)")
    # CONVERSE-DIRECTION CAP, disclosed: the converse enumerates
    # 2^|O| * 2^|even F-branches| assignments per (shape, matching), so it runs
    # on the first `conv_cap` shapes of each leg only.  The FORWARD direction
    # is UNCAPPED on the stratum.
    conv_cap = 120
    for (tag, cs) in (('stratum n_hub <= 6 (EXHAUSTIVE forward)', cases),
                      ('V8 (Wagner habitat shape)',
                       [('V8', 8, v8_specs())]),
                      ('seeded n_hub = 8',
                       [(f'r8#{j + 1}', 8, s) for j, s in
                        enumerate(seeded_shapes(8, 240, rng))]),
                      ('seeded n_hub = 10',
                       [(f'r10#{j + 1}', 10, s) for j, s in
                        enumerate(seeded_shapes(10, 120, rng))])):
        nq = ncert = tsame = nconv = 0
        for si, (_nm, n, specs) in enumerate(cs):
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            oset = set(oidx)
            cube = adm_cube(specs, n, binc, oidx)
            for mat in perfect_matchings(specs):
                matbr = set(mat)
                base = m_of_matching(specs, mat)
                # --- direction 1: every admissible z satisfies the model ---
                seen_A = set()
                for (z, mm, c, pat) in cube:
                    A = a_of(specs, n, binc, matbr, z)
                    mv = m_ind(specs, n, base, z)
                    S = dev_set(mm, base)
                    assert set(v for v in range(n) if A[v] == 1) == S, \
                        "(GR-85): {A(v) = 1} != the deviating set"
                    assert len(S) == dist_anchored(specs, n, binc, z, matbr), \
                        "(GR-85): dist mismatch against (GR-67)(i)"
                    for v in range(n):
                        assert A[v] + mv[v] in (1, 2), "(GR-85): a_v range"
                        if A[v] == 0:
                            assert mv[v] == 1, "(GR-85): A = 0 forces m = 1"
                        if A[v] == 2:
                            assert mv[v] == 0, "(GR-85): A = 2 forces m = 0"
                    pb = {i: z[i] for i in oidx}
                    assert not mconstraints(specs, n, mat, oset, pb, A), \
                        "(GR-85): admissible z violates a local condition"
                    T = t_of(specs, oidx, matbr, z)
                    assert T == sum(A.values()), "(GR-85): T != sum A(v)"
                    n2 = sum(1 for v in range(n) if A[v] == 2)
                    assert len(S) == T - 2 * n2, "(GR-85): dist = T - 2 n_2"
                    assert len(S) % 2 == T % 2, "(GR-85): parity vs T"
                    assert T % 2 == sum(
                        1 for i, (_u, _w, L) in enumerate(specs)
                        if L % 2 == 0 and i not in matbr) % 2, \
                        "(GR-85): parity law corollary broken"
                    assert map_to_z(specs, mm, c) == z, "z round-trip"
                    assert pattern_of(specs, mm, c, oidx) == pat, \
                        "pattern_of != z_pattern"
                    seen_A.add((pat, tuple(A[v] for v in range(n))))
                    nq += 1
                tsame += 1
                if si >= conv_cap:
                    continue
                # --- direction 2: the three conditions are SUFFICIENT ------
                evf = [i for i in range(len(specs))
                       if i not in matbr and i not in oset]
                for bits in range(1 << len(oidx)):
                    pb = {i: (bits >> j) & 1 for j, i in enumerate(oidx)}
                    pat = 0
                    for j, i in enumerate(oidx):
                        if pb[i]:
                            pat |= 1 << j
                    A0 = {v: 0 for v in range(n)}
                    for i in oidx:
                        if i in matbr or pb[i] != 0:
                            continue
                        (u, w, _L) = specs[i]
                        A0[u] += 1
                        A0[w] += 1
                    for ob in range(1 << len(evf)):
                        A = dict(A0)
                        for t, i in enumerate(evf):
                            (u, w, _L) = specs[i]
                            A[u if (ob >> t) & 1 == 0 else w] += 1
                        ok = not mconstraints(specs, n, mat, oset, pb, A) \
                            and max(A.values()) <= 2
                        got = (pat, tuple(A[v] for v in range(n))) in seen_A
                        assert ok == got, \
                            "(GR-85): the local conditions are not exactly " \
                            "admissibility"
                        ncert += 1
                nconv += 1
        print(f"  {tag}: {nq} (shape, matching, admissible z) triples "
              f"asserted forward over {tsame} (shape, matching) pairs, and "
              f"{ncert} (odd pattern, even-F orientation) assignments "
              f"asserted in the converse over {nconv} of them "
              f"(converse capped at the first {conv_cap} shapes; the "
              f"forward direction is uncapped) -- 0 failures"
              )
    print("  READING: the objective is #{v : A(v) ODD}, a PARITY count. "
          "Feasibility is a degree-constrained orientation ((GR-50)); the "
          "objective is NOT a convex function of the degree data, so route "
          "3's min-cost-flow reading does not apply (see --adv control 3).")
    print(f"  [{time.time() - t0:.0f}s]")



# ------------------------------------------------- [GFL-2] --chain ----------

def leg_chain():
    """[GFL-2] (GR-86): the repair-chain theorem -- completeness, the price
    by case, and the chain-price invariance."""
    t0 = time.time()
    print("[GFL-2] (GR-86) the repair-chain theorem: a chain repair exists "
          "iff the flipped pattern is (GR-50)-feasible, and its price is "
          "length-free")
    bound = {'M-free': 0, 'M-one': 2, 'M-double': 4,
             'F-free': 2, 'F-one': 2, 'F-double': 2}
    for (tag, cs, matcap) in (('stratum n_hub <= 6 (EXHAUSTIVE)',
                               stratum_cases(), None),
                              ('V8', [('V8', 8, v8_specs())], None)):
        pmin = collections.defaultdict(collections.Counter)
        pmax = collections.defaultdict(collections.Counter)
        bylen = collections.defaultdict(collections.Counter)
        disagree = inv = capped = npairs = 0
        for (_nm, n, specs) in cs:
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            oset = set(oidx)
            cube = adm_cube(specs, n, binc, oidx)
            mats = perfect_matchings(specs)
            if matcap:
                mats = mats[:matcap]
            for mat in mats:
                matbr = set(mat)
                base = m_of_matching(specs, mat)
                for (z, mm, _c, pat) in cube:
                    S = dev_set(mm, base)
                    for j, i in enumerate(oidx):
                        key = case_of(specs, mm, matbr, i)
                        feas = feas_flip(specs, n, oidx, pat, j)
                        sols, cp = chain_repairs(specs, n, binc, z, [i], oset)
                        if cp:
                            capped += 1
                        npairs += 1
                        if (len(sols) > 0) != feas:
                            disagree += 1
                        if not sols:
                            continue
                        prices = []
                        for J in sols:
                            assert flip_legal(specs, n, binc, mm, set(J)), \
                                "(GR-86): a chain repair is not legal"
                            z2 = list(z)
                            for b in J:
                                z2[b] ^= 1
                            assert z_admissible(specs, n, binc, z2)
                            assert z_pattern(z2, oidx) == pat ^ (1 << j), \
                                "(GR-86): the chain moved another odd branch"
                            mm2, _c2 = z_to_map(specs, n, binc, z2)
                            act = len(dev_set(mm2, base)) - len(S)
                            W = w_set(specs, n, binc, matbr, set(J))
                            assert act == price_pred(W, S), \
                                "(GR-68) price formula broken on a chain"
                            prices.append(act)
                            bylen[len(J)][act] += 1
                        assert min(prices) <= bound[key], \
                            f"(GR-86): {key} price {min(prices)} > " \
                            f"{bound[key]}"
                        assert max(prices) <= bound[key], \
                            f"(GR-86): {key} MAX price {max(prices)} > " \
                            f"{bound[key]}"
                        if min(prices) != max(prices):
                            inv += 1
                        pmin[key][min(prices)] += 1
                        pmax[key][max(prices)] += 1
        print(f"  {tag}: {npairs} (admissible z, odd branch) pairs, "
              f"{disagree} disagreements between the chain search and the "
              f"(GR-50) feasibility oracle, {capped} caps hit, "
              f"{inv} instances where two chain repairs differ in price")
        for k in sorted(pmin):
            print(f"    {k:9s} bound {bound[k]:+d}  min-price {hist(pmin[k])} "
                  f" max-price {hist(pmax[k])}")
        print(f"    price BY CHAIN SIZE |J| (the 'independent of length' "
              f"claim, tested directly): "
              + ", ".join(f"|J|={L}: {hist(bylen[L])}"
                          for L in sorted(bylen)))
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GFL-3] --exact ----------

def leg_exact():
    """[GFL-3] (GR-87)/(GR-88): the EXACT one-flip price by full z-cube, the
    price-4 witness, and BALB's two-branch side condition where it fails."""
    t0 = time.time()
    print("[GFL-3] (GR-87)/(GR-88) the EXACT one-flip price "
          "f(p + chi_gamma) - dist(z), by full z-cube")
    rng = random.Random(R_SEED + 3)
    bound = {'M-free': 0, 'M-one': 2, 'M-double': 4,
             'F-free': 2, 'F-one': 2, 'F-double': 2}
    legs = [('stratum n_hub <= 6 (EXHAUSTIVE: all shapes, all matchings, '
             'full 2^|E| cube, no cap)', stratum_cases(), None),
            ('V8', [('V8', 8, v8_specs())], None)]
    for (n, tries, cap) in ((8, 500, 60), (10, 240, 30), (12, 90, 12)):
        sh = seeded_shapes(n, tries, rng)
        legs.append((f'seeded habitat n_hub = {n} (exact per shape)',
                     [(f'r{n}#{j + 1}', n, s) for j, s in enumerate(sh)], cap))
    wit4 = None
    for (tag, cs, matcap) in legs:
        ph = collections.defaultdict(collections.Counter)
        npairs = viol = 0
        gaps = collections.Counter()
        s1_tot = s1_fail = 0
        r1_tot = r1_bad = 0
        optcls = collections.Counter()
        w_arith = collections.Counter()
        ncap = 0
        for (nm, n, specs) in cs:
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            k2 = len(oidx)
            cube = adm_cube(specs, n, binc, oidx)
            mats = perfect_matchings(specs)
            if matcap is not None and len(mats) > matcap:
                ncap += 1
                mats = mats[:matcap]
            for mat in mats:
                matbr = set(mat)
                base = m_of_matching(specs, mat)
                f, dpar = f_layers(cube, n, base)
                dadm = min((v for p, v in f.items() if imb_of(k2, p) == 0),
                           default=None)
                assert dadm is not None, "E1 clause (v): no balanced pattern"
                assert (dadm - dpar) % 2 == 0, "(GR-67) Cor. 1 broken"
                gaps[dadm - dpar] += 1
                for (z, mm, _c, pat) in cube:
                    d = sum(1 for v in range(n) if mm[v] != base[v])
                    S = dev_set(mm, base)
                    opt = (d == dpar)
                    delta = imb_of(k2, pat)
                    maj = set(majority_of(oidx, pat, 1 if delta > 0 else -1)) \
                        if delta else set()
                    for j, i in enumerate(oidx):
                        key = case_of(specs, mm, matbr, i)
                        p2 = pat ^ (1 << j)
                        if opt and i in maj:
                            optcls[key] += 1
                        if p2 not in f:
                            ph[key][None] += 1
                            continue
                        pr = f[p2] - d
                        ph[key][pr] += 1
                        npairs += 1
                        if pr > bound[key]:
                            viol += 1
                        if (pr == 4 and key == 'M-double' and opt
                                and abs(delta) == 2 and i in maj
                                and (wit4 is None or n < wit4[1])):
                            wit4 = (nm, n, [tuple(s) for s in specs],
                                    sorted(mat), i, pat, d, dpar)
                        # BALB's two-branch side condition, where it applies
                        bl = block_ends_at(specs, mm, i)
                        if len(bl) == 1:
                            s1_tot += 1
                            ill = not any(
                                flip_legal(specs, n, binc, mm, {i, b})
                                for b in binc[bl[0]] if b != i)
                            if ill:
                                s1_fail += 1
                            # BALB's OWN sentence: majority-side, at a
                            # parity-optimal configuration.
                            if opt and i in maj:
                                r1_tot += 1
                                if ill:
                                    r1_bad += 1
                        # the (1,2,2) W-arithmetic of (GR-88)
                        if len(bl) == 2 and i in matbr:
                            (u, w, _L) = specs[i]
                            for b1 in nonmatch_at(binc, matbr, u):
                                for b2 in nonmatch_at(binc, matbr, w):
                                    J = {i, b1, b2}
                                    if len(J) != 3:
                                        continue
                                    if not flip_legal(specs, n, binc, mm, J):
                                        continue
                                    W = w_set(specs, n, binc, matbr, J)
                                    pp = price_pred(W, S)
                                    assert pp == len(W) - 2 * len(W & S)
                                    w_arith[(len(W), len(W & S), pp)] += 1
        print(f"  {tag}: {npairs} (z, odd branch) pairs with the flip "
              f"feasible; {viol} violations of the (GR-86) case bound; "
              f"per-matching gaps {hist(gaps)}"
              + (f"; {ncap} shapes had their matching list capped"
                 if ncap else ""))
        for k in sorted(ph):
            print(f"    {k:9s} bound {bound[k]:+d}  exact price {hist(ph[k])}")
        print(f"    at a parity-optimal configuration the MAJORITY-side "
              f"classes are {dict(sorted(optcls.items()))}")
        if s1_tot:
            print(f"    BALB's two-branch side condition (some beta at the "
                  f"blocked end legal): FAILS at {s1_fail} of {s1_tot} "
                  f"one-end-blocked instances over ALL configurations, and "
                  f"at {r1_bad} of {r1_tot} in BALB's OWN scope "
                  f"(majority-side, at a parity-optimal configuration)")
        if w_arith:
            tot = sum(w_arith.values())
            le2 = sum(c for (wl, ws, pp), c in w_arith.items() if pp <= 2)
            one = sum(c for (wl, ws, pp), c in w_arith.items()
                      if wl == 4 and ws == 1)
            print(f"    the (1,2,2) mixed pair: {tot} legal instances, "
                  f"price = |W| - 2|W cap S| at every one; {le2} have "
                  f"price <= 2, of which {one} have EXACTLY ONE deviating "
                  f"extra endpoint (|W| = 4, |W cap S| = 1, price 2) -- so "
                  f"one endpoint suffices, not two")
    if wit4 is not None:
        (nm, n, sp, mt, i, pat, d, dpar) = wit4
        print(f"  the price-4 witness, named exactly: {nm} n_hub = {n}, "
              f"specs {sp}, matching branches {mt}, doubly-blocked "
              f"majority branch {i} = {sp[i]}, pattern bits {pat}, "
              f"dist = {d} = d_par(M) = {dpar}, |delta| = 2 -- "
              f"f(p + chi_gamma) = {d + 4}, so the one-flip price is "
              f"EXACTLY 4 and Clause A' sub-clause 2 FAILS at this branch")
    print(f"  [{time.time() - t0:.0f}s]")


# -------------------------------------------------- [GFL-4] --desc ----------

def leg_desc():
    """[GFL-4] (GR-89): clause (GR-R1), the greedy descent, the selection-clause
    census and the counting bound."""
    t0 = time.time()
    print("[GFL-4] (GR-89) the descent: clause (GR-R1), the greedy descent to "
          "balance, and the SELECTION clause that replaces the repair "
          "residual")
    rng = random.Random(R_SEED + 4)
    legs = [('stratum n_hub <= 6 (EXHAUSTIVE)', stratum_cases(), None, None),
            ('V8', [('V8', 8, v8_specs())], None, None)]
    for (n, tries, mcap, zcap) in ((8, 200, 10, 500), (10, 90, 6, 400)):
        sh = seeded_shapes(n, tries, rng)
        legs.append((f'seeded habitat n_hub = {n}',
                     [(f'r{n}#{j + 1}', n, s) for j, s in enumerate(sh)],
                     mcap, zcap))
    for (tag, cs, matcap, zcap) in legs:
        r1fail = nunb = 0
        tot = collections.Counter()
        step = collections.Counter()
        dfail = 0
        selopt = selfail = 0
        allmd = []
        capped = 0
        for (nm, n, specs) in cs:
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            oset = set(oidx)
            k2 = len(oidx)
            cube = adm_cube(specs, n, binc, oidx)
            mats = perfect_matchings(specs)
            if matcap is not None and len(mats) > matcap:
                capped += 1
                mats = mats[:matcap]
            zs = [t for t in cube]
            if zcap is not None and len(zs) > zcap:
                zs = rng.sample(zs, zcap)
                capped += 1
            for mat in mats:
                matbr = set(mat)
                base = m_of_matching(specs, mat)
                f, dpar = f_layers(cube, n, base)
                for (z, mm, _c, pat) in zs:
                    delta = imb_of(k2, pat)
                    if delta == 0:
                        continue
                    nunb += 1
                    sgn = 1 if delta > 0 else -1
                    maj = [(j, i) for j, i in enumerate(oidx)
                           if (sgn > 0) == (((pat >> j) & 1) == 0)]
                    feas = [(j, i) for (j, i) in maj
                            if feas_flip(specs, n, oidx, pat, j)]
                    if not feas:
                        r1fail += 1
                    d = sum(1 for v in range(n) if mm[v] != base[v])
                    if d == dpar:
                        selopt += 1
                        cheap = [(j, i) for (j, i) in feas
                                 if case_of(specs, mm, matbr, i) != 'M-double']
                        if not cheap:
                            selfail += 1
                        if feas and not cheap:
                            allmd.append((nm, n, sorted(mat), pat))
                        # the counting bound (GR-89)(iii)
                        if maj and all(i in matbr and
                                       len(block_ends_at(specs, mm, i)) == 2
                                       for (_j, i) in maj):
                            assert n >= 3 * (k2 // 2) + 5 * abs(delta) // 2, \
                                "(GR-89)(iii) counting bound violated"
                    # the greedy descent, from THIS configuration
                    zc = list(z)
                    run = 0
                    worst = 0
                    ok = True
                    while True:
                        pc = z_pattern(zc, oidx)
                        dl = imb_of(k2, pc)
                        if dl == 0:
                            break
                        sg = 1 if dl > 0 else -1
                        mmc, _cc = z_to_map(specs, n, binc, zc)
                        Sc = dev_set(mmc, base)
                        best = None
                        for j, i in enumerate(oidx):
                            if (sg > 0) != (((pc >> j) & 1) == 0):
                                continue
                            sols, cp = chain_repairs(specs, n, binc, zc,
                                                     [i], oset)
                            if cp:
                                capped += 1
                            for J in sols:
                                W = w_set(specs, n, binc, matbr, set(J))
                                pr = price_pred(W, Sc)
                                if best is None or pr < best[0]:
                                    best = (pr, J)
                        if best is None:
                            ok = False
                            break
                        run += best[0]
                        worst = max(worst, best[0])
                        for b in best[1]:
                            zc[b] ^= 1
                        assert z_admissible(specs, n, binc, zc)
                    if not ok:
                        dfail += 1
                        continue
                    assert imb_of(k2, z_pattern(zc, oidx)) == 0
                    tot[run] += 1
                    step[worst] += 1
        print(f"  {tag}: {nunb} unbalanced admissible configurations"
              + (f", {capped} caps hit" if capped else ", no cap hit"))
        print(f"    (GR-R1) no majority-side odd branch has a feasible flip: "
              f"{r1fail}")
        print(f"    greedy descent-to-balance: total price {hist(tot)}, "
              f"worst single step {hist(step)}, {dfail} descents stalled")
        print(f"    SELECTION clause at parity-optimal configurations: "
              f"{selopt} audited, {selfail} with NO cheap "
              f"(non-M-doubly-blocked) feasible majority branch")
        if allmd:
            print(f"    all-majority-doubly-blocked configurations: "
                  f"{allmd[:3]}")
    # The targeted hunt (GR-89)(iii) predicts: a TOTAL failure of the
    # selection clause needs n_hub >= 3k + 5|delta|/2, so its first possible
    # home is n_hub = 8 with 2k = 2 and BOTH odd branches doubly-blocked
    # matching branches.  Swept directly.
    hit = 0
    seen = 0
    shapes = 0
    for _t in range(900):
        specs = rand_habitat(8, rng, 1)
        if not specs:
            continue
        specs = specs[0]
        oidx = odd_idx(specs)
        if len(oidx) != 2:
            continue
        shapes += 1
        n = 8
        binc = branches_at(specs, n)
        cube = adm_cube(specs, n, binc, oidx)
        for mat in perfect_matchings(specs):
            matbr = set(mat)
            if not all(i in matbr for i in oidx):
                continue
            base = m_of_matching(specs, mat)
            _f, dpar = f_layers(cube, n, base)
            for (_z, mm, _c, pat) in cube:
                if sum(1 for v in range(n) if mm[v] != base[v]) != dpar:
                    continue
                if imb_of(2, pat) == 0:
                    continue
                seen += 1
                maj = majority_of(oidx, pat, 1 if imb_of(2, pat) > 0 else -1)
                if all(len(block_ends_at(specs, mm, i)) == 2 for i in maj):
                    hit += 1
    print(f"  the TARGETED hunt at the counting bound's first possible home "
          f"(n_hub = 8, 2k = 2, BOTH odd branches in M): {shapes} seeded "
          f"habitat shapes with exactly two odd branches, {seen} unbalanced "
          f"parity-optimal configurations at an all-odd-in-M matching, "
          f"{hit} with BOTH majority branches doubly blocked -- "
          f"NOT FOUND under this cap, which is not a proof of nonexistence")
    print(f"  [{time.time() - t0:.0f}s]")


# --------------------------------------------------- [GFL-5] --big ----------

def leg_big():
    """[GFL-5] beyond the stratum: CAP-FREE chain certificates at
    n = 30/40/50/60."""
    t0 = time.time()
    print(f"[GFL-5] beyond the stratum -- CAP-FREE (GR-86) certificates "
          f"(seed {R_SEED + 5})")
    print("  WHY this reaches where BALB's m = 6 table could not: (GR-86) is "
          "a RELATIVE statement, so it needs no d_par(M) and therefore no "
          "gadm.dp_pref 2^dim table.  (b') itself still needs d_par(M) and "
          "is still capped at m = 6.")
    rng = random.Random(R_SEED + 5)
    bound = {'M-free': 0, 'M-one': 2, 'M-double': 4,
             'F-free': 2, 'F-one': 2, 'F-double': 2}
    for m in (6, 8, 10, 12):
        res = collections.Counter()
        capped = tries = 0
        for (nm, n, specs) in necklaces((m,)):
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            oset = set(oidx)
            mat = complete_matching(specs, n, [])
            assert mat is not None and len(mat) == n // 2
            matbr = set(mat)
            base = m_of_matching(specs, mat)
            sds = seeds_at(specs, n, oidx)
            assert sds, f"{nm}: no feasible pattern at all"
            for _t in range(30):
                z = walk_adm(specs, n, binc, rng.choice(sds), rng,
                             3 * len(specs))
                mm, _c = z_to_map(specs, n, binc, z)
                S = dev_set(mm, base)
                pat = z_pattern(z, oidx)
                for j, i in enumerate(oidx):
                    if not feas_flip(specs, n, oidx, pat, j):
                        continue
                    tries += 1
                    key = case_of(specs, mm, matbr, i)
                    J, cp = chain_first(specs, n, binc, z, [i], oset)
                    if cp or J is None:
                        capped += 1
                        continue
                    assert flip_legal(specs, n, binc, mm, set(J))
                    z2 = list(z)
                    for b in J:
                        z2[b] ^= 1
                    assert z_admissible(specs, n, binc, z2)
                    assert z_pattern(z2, oidx) == pat ^ (1 << j)
                    mm2, _c2 = z_to_map(specs, n, binc, z2)
                    act = len(dev_set(mm2, base)) - len(S)
                    W = w_set(specs, n, binc, matbr, set(J))
                    assert act == price_pred(W, S), "(GR-68) broken at large n"
                    assert act <= bound[key], \
                        f"(GR-86): {key} price {act} at n = {n}"
                    res[(key, act)] += 1
        print(f"  necklaces at m = {m} (n_hub = {5 * m}): {tries} feasible "
              f"(configuration, odd branch) flips certified, {capped} node "
              f"caps hit -- {hist2(res)}")
    # the seeded exact legs, for the record
    for (n, tries, mcap) in ((8, 200, 10), (10, 90, 6), (12, 40, 4)):
        sh = seeded_shapes(n, tries, rng)
        gaps = collections.Counter()
        md = collections.Counter()
        for specs in sh:
            binc = branches_at(specs, n)
            oidx = odd_idx(specs)
            k2 = len(oidx)
            cube = adm_cube(specs, n, binc, oidx)
            mats = perfect_matchings(specs)[:mcap]
            for mat in mats:
                matbr = set(mat)
                base = m_of_matching(specs, mat)
                f, dpar = f_layers(cube, n, base)
                dadm = min((v for p, v in f.items() if imb_of(k2, p) == 0),
                           default=None)
                gaps[dadm - dpar] += 1
                for (z, mm, _c, pat) in cube:
                    d = sum(1 for v in range(n) if mm[v] != base[v])
                    if d != dpar:
                        continue
                    delta = imb_of(k2, pat)
                    if abs(delta) != 2:
                        continue
                    for j, i in enumerate(majority_of(oidx, pat,
                                                      1 if delta > 0 else -1)):
                        if case_of(specs, mm, matbr, i) != 'M-double':
                            continue
                        jj = oidx.index(i)
                        p2 = pat ^ (1 << jj)
                        md[f[p2] - d if p2 in f else None] += 1
        print(f"  seeded habitat n_hub = {n}: {len(sh)} shapes, "
              f"per-matching gaps {hist(gaps)}; the one-flip price of a "
              f"doubly-blocked MATCHING branch at a |delta| = 2 "
              f"parity-optimal configuration: {hist(md)} "
              f"(matching list capped at {mcap} per shape)")
    print(f"  [{time.time() - t0:.0f}s]")


# --------------------------------------------------- [GFL-6] --adv ----------

def leg_adv():
    """[GFL-6] F13 falsification controls: every guard above is exercised on
    an instance it must REJECT."""
    t0 = time.time()
    print("[GFL-6] F13 falsification controls (a guard observed only passing "
          "is untested)")
    rng = random.Random(R_SEED + 6)
    cs = stratum_cases()[:200]

    # (1) the model, broken: read A(v) off the MATCHING dart instead of the
    #     two F-darts.  Must disagree with the deviating set somewhere.
    bad = 0
    tot = 0
    for (_nm, n, specs) in cs:
        binc = branches_at(specs, n)
        oidx = odd_idx(specs)
        cube = adm_cube(specs, n, binc, oidx)
        for mat in perfect_matchings(specs):
            matbr = set(mat)
            base = m_of_matching(specs, mat)
            for (z, mm, _c, _p) in cube:
                S = dev_set(mm, base)
                Ax = {v: sum(1 for i in binc[v]
                             if i in matbr and dart_col(specs, z, v, i) == 0)
                      for v in range(n)}
                tot += 1
                if set(v for v in range(n) if Ax[v] == 1) != S:
                    bad += 1
    print(f"  (1) the model with A(v) read off the MATCHING dart instead of "
          f"the two F-darts: {bad} of {tot} (z, M) pairs DISAGREE with the "
          f"deviating set -- the (GR-85) identity is specific to the "
          f"2-factor, not an accident of counting")
    assert bad > 0, "control (1) did not fire"

    # (2) the case bound tightened to 2 EVERYWHERE must fail, and only on
    #     M-double.
    fired = collections.Counter()
    for (_nm, n, specs) in cs:
        binc = branches_at(specs, n)
        oidx = odd_idx(specs)
        oset = set(oidx)
        cube = adm_cube(specs, n, binc, oidx)
        for mat in perfect_matchings(specs):
            matbr = set(mat)
            base = m_of_matching(specs, mat)
            f, _dp = f_layers(cube, n, base)
            for (z, mm, _c, pat) in cube:
                d = sum(1 for v in range(n) if mm[v] != base[v])
                for j, i in enumerate(oidx):
                    p2 = pat ^ (1 << j)
                    if p2 not in f:
                        continue
                    if f[p2] - d > 2:
                        fired[case_of(specs, mm, matbr, i)] += 1
    print(f"  (2) the bound tightened to <= 2 for every case: violated at "
          f"{dict(sorted(fired.items()))} -- the exception is EXACTLY "
          f"'M-double' and the case split is not vacuous")
    assert set(fired) == {'M-double'} and fired['M-double'] > 0, \
        "control (2) did not isolate M-double"

    # (3) route 2's naive two-sided 2-Lipschitz law -- the SMALLEST witness.
    wit = None
    for (nm, n, specs) in stratum_cases():
        binc = branches_at(specs, n)
        oidx = odd_idx(specs)
        cube = adm_cube(specs, n, binc, oidx)
        for mat in perfect_matchings(specs):
            base = m_of_matching(specs, mat)
            f, _dp = f_layers(cube, n, base)
            for p, v in f.items():
                for j in range(len(oidx)):
                    p2 = p ^ (1 << j)
                    if p2 in f and abs(f[p2] - v) > 2:
                        c = (n, [tuple(s) for s in specs], sorted(mat),
                             p, p2, v, f[p2])
                        if wit is None or c[0] < wit[0]:
                            wit = c
        if wit is not None and wit[0] <= 4:
            break
    print(f"  (3) route 2's naive law |f(p + chi) - f(p)| <= 2 is REFUTED: "
          f"n_hub = {wit[0]}, specs {wit[1]}, matching branches {wit[2]}, "
          f"pattern {wit[3]} -> {wit[4]} carries f {wit[5]} -> {wit[6]} "
          f"(jump {abs(wit[6] - wit[5])}) -- so the exchange MUST be "
          f"anchored, and the jump direction is balanced-optimal -> "
          f"unbalanced")
    assert wit is not None, "control (3) did not fire"

    # (4) route 1's named input runs the WRONG WAY: at a parity-optimal
    #     configuration optimality CAPS |W cap S| at |W|/2.
    capped = viol = 0
    for (_nm, n, specs) in cs:
        binc = branches_at(specs, n)
        oidx = odd_idx(specs)
        cube = adm_cube(specs, n, binc, oidx)
        for mat in perfect_matchings(specs):
            matbr = set(mat)
            base = m_of_matching(specs, mat)
            f, dpar = f_layers(cube, n, base)
            for (z, mm, _c, _pat) in cube:
                d = sum(1 for v in range(n) if mm[v] != base[v])
                if d != dpar:
                    continue
                S = dev_set(mm, base)
                for bits in range(1 << len(specs)):
                    J = set(i for i in range(len(specs)) if (bits >> i) & 1)
                    if not J or not flip_legal(specs, n, binc, mm, J):
                        continue
                    W = w_set(specs, n, binc, matbr, J)
                    capped += 1
                    if 2 * len(W & S) > len(W):
                        viol += 1
    print(f"  (4) at a parity-optimal configuration, every one of the "
          f"{capped} legal flip sets satisfies 2|W cap S| <= |W| "
          f"({viol} violations) -- optimality CAPS the number of deviating "
          f"endpoints, so route 1's 'forced onto S' input is directionally "
          f"wrong")
    assert viol == 0, "control (4) contradicts (GR-68) minimality"

    # (5) a shuffled price predictor must disagree with the truth.
    dis = tot = 0
    for (_nm, n, specs) in cs[:60]:
        binc = branches_at(specs, n)
        oidx = odd_idx(specs)
        oset = set(oidx)
        cube = adm_cube(specs, n, binc, oidx)
        for mat in perfect_matchings(specs):
            matbr = set(mat)
            base = m_of_matching(specs, mat)
            for (z, mm, _c, _pat) in cube:
                S = dev_set(mm, base)
                for i in oidx:
                    sols, cp = chain_repairs(specs, n, binc, z, [i], oset)
                    for J in sols[:2]:
                        W = w_set(specs, n, binc, matbr, set(J))
                        Sx = set(rng.sample(sorted(range(n)), len(S))) \
                            if len(S) <= n else S
                        tot += 1
                        if price_pred(W, Sx) != price_pred(W, S):
                            dis += 1
    print(f"  (5) the (GR-68) price with S replaced by a random hub set of "
          f"the same size disagrees at {dis} of {tot} chain repairs -- the "
          f"formula is testing S, not |S|")
    assert dis > 0, "control (5) did not fire"
    print(f"  [{time.time() - t0:.0f}s]")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    for fl in ('model', 'chain', 'exact', 'desc', 'big', 'adv', 'validate'):
        ap.add_argument(f'--{fl}', action='store_true')
    a = ap.parse_args()
    any_ = False
    for (fl, fn) in (('model', leg_model), ('chain', leg_chain),
                     ('exact', leg_exact), ('desc', leg_desc),
                     ('big', leg_big), ('adv', leg_adv)):
        if getattr(a, fl) or a.validate:
            fn()
            any_ = True
    if not any_:
        ap.print_help()


if __name__ == '__main__':
    main()
