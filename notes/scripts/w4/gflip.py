"""GFLIP -- the thirtieth kernel-(K) ordinal: (GR-R1), the flip-availability
clause of GFLOW's descent (spec: notes/Pencil-fanout.md S"GFLIP -- thirtieth
ordinal").

TARGET: (GR-R1) -- at every unbalanced admissible configuration, some
majority-side odd branch has a (GR-50)-feasible flip (S(K-grid) Step
G108(ii)).  Measured 0/771530 by gflow --desc and unproven; proving it makes
(GR-89)(ii)'s n-free bound d_adm(M) - d_par(M) <= 4*min(k, floor(n_hub/4))
<= 12 a THEOREM.  This pass PROVES it, via three steps:

  (GR-97) THE DEMAND FORM of the (GR-51) weight criterion.  The (GR-50)
  bounds have the closed forms

      l_v = [o_v = 0]          u_v = d_v - [o_v = q_v]

  (o_v = A-odd darts at v, q_v = odd darts, d_v = 3 - q_v), so with
  inc_H(S) := e_H(S) + bd_H(S) (even branches MEETING S),
  N_A(S) := #{v in S : o_v = q_v} and N_B(S) := #{v in S : o_v = 0}
  (q = 0 hubs count in BOTH), (GR-51)'s two weight inequalities are exactly

      inc_H(S) >= N_A(S)   and   inc_H(S) >= N_B(S)   for every S,

  i.e. W_A(S) = 2(inc_H(S) - N_A(S)) and W_B(S) = 2(inc_H(S) - N_B(S)) --
  in particular both are always EVEN.  Flipping an A-branch gamma to B
  never enlarges N_A and enlarges N_B(S) by exactly
  e_gamma(S) := #{ends v of gamma in S with o_v = 1}, so the flipped
  pattern is feasible iff inc_H(S) >= N_B(S) + e_gamma(S) for every S.
  (--form)

  (GR-98) THE COUNTING LEMMA.  For ANY pattern with o_v <= 2 everywhere
  (feasibility not needed) and any hub set S, with n_j(S) := #{v in S :
  o_v = j} and slack s(S) := inc_H(S) - N_B(S), cubicity gives the exact
  identity

      sum_{v in S} b_v = 2 n_0(S) + 2 n_1(S) + n_2(S) - s(S) - e_H(S),

  and e_H(S) <= inc_H(S) = n_0(S) + s(S) plus sum_S b_v <= 2b yield

      b >= n_1(S) - s(S)

  (b = #B-branches).  Symmetrically a >= #{v in S : b_v = 1} - s_A(S).
  (--lemma)

  (GR-99) THE SELECTION THEOREM, whose corollary is (GR-R1).  At any
  feasible pattern of a cubic loop-free hub multigraph (NO habitat gate,
  NO bound on 2k, no connectivity or bridgelessness), the number of
  A-branches whose flip is infeasible is AT MOST b, and symmetrically at
  most a for the B side.  Proof: a blocked gamma has a witness S_gamma
  with slack s(S_gamma) <= e_gamma(S_gamma) - 1 ((GR-97), since the p-side
  inequalities hold); s is submodular and >= 0 at a feasible p, so the
  union U of the witnesses has s(U) <= sum (e_gamma - 1); a hub with
  o_v = 1 is the lone-A end of exactly ONE A-branch and gamma's two ends
  are distinct (loop-free), so n_1(U) >= sum e_gamma; (GR-98) gives
  b >= n_1(U) - s(U) >= #blocked.  Hence at an unbalanced pattern with
  majority side A, at least a - b = |delta| >= 2 majority flips are
  feasible -- (GR-R1), with room to spare.  (--thm; witness anatomy and
  falsification controls in --wit)

Modes:
  --form     (GR-97): the closed l/u forms and the demand-form equivalence
             against the (GR-50) oracle, over ALL 2^{2k} patterns per shape
             and ALL 2^n hub sets -- stratum (EXHAUSTIVE) + V8 + seeded
             n = 8/10; plus the doctored-demand (q = 0 dropped) control.
  --lemma    (GR-98): the exact identity and the two counting inequalities
             at every (pattern, hub set) pair -- feasible AND infeasible
             patterns -- over the stratum + V8.
  --thm      (GR-99): #blocked <= opposite count per side, and >= |delta|
             feasible majority flips at every unbalanced feasible pattern
             (the (GR-R1) sentence, pattern form) -- stratum (EXHAUSTIVE)
             + V8 + seeded n = 8/10 + the named large shapes (sampled
             patterns, seeded) + beyond-habitat random cubic shapes at
             2k = 8/10 (outside the arc's excess-6 scope: the theorem has
             no 2k cap).
  --wit      witness anatomy at every blocked stratum instance (the exact
             shape (GR-99)'s proof predicts), plus the tightness report
             (#blocked = opposite count attained?) and the naive
             "never blocked" control.
  --validate all four, in the order above.

The (GR-R1) quantifier factors through the pattern: a configuration IS an
admissible z ((GR-49)), its pattern is feasible by witness, and both
"majority side" and "the flip is (GR-50)-feasible" depend on the pattern
alone -- so the pattern-level sentence tested here is EQUIVALENT to
(GR-R1)'s configuration-level sentence, and nothing here re-measures
gflow --desc's landed 701382-configuration census (a different, weaker
sentence at a different quantifier level).

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

from balb import stratum_cases, v8_specs                                   # noqa: E402
from gbal import (bounds_of, feasible_at, named_cases, odd_idx,            # noqa: E402
                  random_cases)
from gdesc import imb_of                                                   # noqa: E402
from gflow import feas_flip, seeded_shapes                                 # noqa: E402
from gpsa import branches_at                                               # noqa: E402

R_SEED = 20260825


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive (checked against the README index and
# the Divergences table).  `odd_profile` reads (o, q) off a bitmask pattern;
# `even_masks` the even-branch endpoint bitmasks; `demand_data` /
# `demand_ok` the (GR-97) demand form; `blocked_of` the per-side blocked
# lists; `wit_anatomy` extracts a blocked branch's violating hub sets and
# checks the (GR-99) witness shape.  Patterns are bitmasks in
# gpsa.pattern_of's bit order (bit j = colour of oidx[j], 1 = B), as in
# gflow/gdesc.


def odd_profile(specs, n, oidx, pat):
    """(o, q) per hub for the bitmask pattern `pat` (colour 0 = A)."""
    o = [0] * n
    q = [0] * n
    for j, i in enumerate(oidx):
        (u, w, _L) = specs[i]
        for v in (u, w):
            q[v] += 1
            if not (pat >> j) & 1:
                o[v] += 1
    return o, q


def even_masks(specs, n, oidx):
    """Endpoint bitmasks of the even branches (multiplicity kept)."""
    oset = set(oidx)
    return [(1 << u) | (1 << w)
            for i, (u, w, _L) in enumerate(specs) if i not in oset]


def demand_data(n, o, q, doctor=False):
    """(GR-97): the two demand bitmasks -- N_A counts hubs with o = q,
    N_B hubs with o = 0, q = 0 hubs in BOTH.  `doctor` drops the q = 0
    hubs from both (the F13 control: a relaxation, never stricter)."""
    na = nb = 0
    for v in range(n):
        if doctor and q[v] == 0:
            continue
        if o[v] == q[v]:
            na |= 1 << v
        if o[v] == 0:
            nb |= 1 << v
    return na, nb


def demand_ok(n, emasks, na, nb):
    """(GR-97): inc_H(S) >= N_A(S) and inc_H(S) >= N_B(S) at ALL 2^n hub
    sets (n <= 12 guard)."""
    assert n <= 12, "subset enumeration guard"
    for mask in range(1 << n):
        inc = sum(1 for em in emasks if em & mask)
        if inc < bin(na & mask).count('1'):
            return False
        if inc < bin(nb & mask).count('1'):
            return False
    return True


def blocked_of(specs, n, oidx, pat):
    """([blocked A positions], [blocked B positions]) at the pattern."""
    bA, bB = [], []
    for j in range(len(oidx)):
        if not feas_flip(specs, n, oidx, pat, j):
            (bB if (pat >> j) & 1 else bA).append(j)
    return bA, bB


def wit_anatomy(specs, n, oidx, pat, j):
    """For a BLOCKED branch oidx[j] at the feasible pattern `pat`: check
    (GR-97)'s account of the block and return the anatomy histogram keys.
    Works on the flipped-to side's demands (B-demands for an A-branch,
    A-demands for a B-branch -- the latter via the colour swap pat ^ full,
    under which o <-> b and N_A <-> N_B).

    Asserts: (i) the kept side's inequalities survive the flip at every S
    (monotonicity); (ii) at least one violating S exists; (iii) every
    violating S has slack s(S) <= e_gamma(S) - 1 with e_gamma(S) >= 1 and
    s(S) >= 0.  Returns (s, e_gamma, |S|) of a minimal violator."""
    k2 = len(oidx)
    full = (1 << k2) - 1
    p = pat if not (pat >> j) & 1 else pat ^ full  # blocked branch now A
    o, q = odd_profile(specs, n, oidx, p)
    na, nb = demand_data(n, o, q)
    emasks = even_masks(specs, n, oidx)
    (eu, ew, _L) = specs[oidx[j]]
    # ends of gamma that join N_B on the flip: lone-A ends (o = 1)
    gain = 0
    for v in (eu, ew):
        assert o[v] >= 1, "gamma not A at its own end"
        if o[v] == 1:
            gain |= 1 << v
    # N_A after the flip: ends with o = q leave
    drop = 0
    for v in (eu, ew):
        if o[v] == q[v]:
            drop |= 1 << v
    best = None
    for mask in range(1 << n):
        inc = sum(1 for em in emasks if em & mask)
        nbs = bin(nb & mask).count('1')
        s = inc - nbs
        assert s >= 0, "pattern not feasible on the flipped-to side"
        assert inc >= bin(na & mask).count('1'), "pattern not feasible (kept side)"
        assert inc >= bin((na & ~drop) & mask).count('1'), \
            "kept-side inequality broken by the flip: monotonicity FALSE"
        eg = bin(gain & mask).count('1')
        if inc < nbs + eg:
            assert eg >= 1 and s <= eg - 1, "witness outside the proof's shape"
            sz = bin(mask).count('1')
            key = (sz, s, eg)
            if best is None or key < best:
                best = key
    assert best is not None, \
        "oracle says blocked but no demand-form violator exists"
    (sz, s, eg) = best
    return (s, eg, sz)


def hist(d):
    return dict(sorted(d.items(),
                       key=lambda t: ((t[0] is None, t[0])
                                      if not isinstance(t[0], tuple)
                                      else (False, t[0]))))


def seeded_legs(rng):
    """The gflow-shaped seeded legs: habitat shapes at n = 8 and 10."""
    legs = []
    for (n, tries) in ((8, 200), (10, 90)):
        sh = seeded_shapes(n, tries, rng)
        legs.append((f'seeded habitat n_hub = {n}',
                     [(f'r{n}#{t + 1}', n, s) for t, s in enumerate(sh)]))
    return legs


# ------------------------------------------------- [GFP-1] --form -----------

def leg_form():
    """[GFP-1] (GR-97): the closed l/u forms and the demand-form
    equivalence, over ALL patterns and ALL hub sets."""
    t0 = time.time()
    print("[GFP-1] (GR-97) the demand form: l_v = [o_v = 0], "
          "u_v = d_v - [o_v = q_v], and feasibility <=> "
          "inc_H(S) >= N_A(S), N_B(S) at every S")
    rng = random.Random(R_SEED + 1)
    print(f"  seed {R_SEED + 1}")
    legs = [('stratum n_hub <= 6 (EXHAUSTIVE)', stratum_cases()),
            ('V8', [('V8', 8, v8_specs())])] + seeded_legs(rng)
    for (tag, cs) in legs:
        pairs = feas = 0
        dis = 0        # doctored control: strictly more permissive
        for (_nm, n, specs) in cs:
            oidx = odd_idx(specs)
            emasks = even_masks(specs, n, oidx)
            for pat in range(1 << len(oidx)):
                pairs += 1
                o, q, d, lo, hi = bounds_of(
                    specs, n, oidx,
                    [(pat >> t) & 1 for t in range(len(oidx))])
                for v in range(n):
                    assert lo[v] == (1 if o[v] == 0 else 0), "l closed form"
                    assert hi[v] == d[v] - (1 if o[v] == q[v] else 0), \
                        "u closed form"
                na, nb = demand_data(n, o, q)
                ok = demand_ok(n, emasks, na, nb)
                zc = feasible_at(specs, n, oidx,
                                 [(pat >> t) & 1 for t in range(len(oidx))])
                assert ok == (zc is not None), \
                    "(GR-97) demand form disagrees with the (GR-50) oracle"
                if ok:
                    feas += 1
                nad, nbd = demand_data(n, o, q, doctor=True)
                okd = demand_ok(n, emasks, nad, nbd)
                assert (not ok) or okd, "doctored form not a relaxation"
                if okd and not ok:
                    dis += 1
        print(f"  {tag}: {pairs} (shape, pattern) pairs, {feas} feasible, "
              f"0 disagreements with the oracle")
        print(f"    doctored control (q = 0 hubs dropped from N_A/N_B): "
              f"{dis} patterns wrongly declared feasible"
              + ("" if dis else " -- the q = 0 clause never binds here"))
    print(f"  [{time.time() - t0:.1f}s]")


# ------------------------------------------------- [GFP-2] --lemma ----------

def leg_lemma():
    """[GFP-2] (GR-98): the exact identity and the counting inequalities,
    at feasible AND infeasible patterns."""
    t0 = time.time()
    print("[GFP-2] (GR-98) the counting lemma: "
          "sum_S b_v = 2n_0 + 2n_1 + n_2 - s - e_H, and b >= n_1(S) - s(S)")
    legs = [('stratum n_hub <= 6 (EXHAUSTIVE)', stratum_cases()),
            ('V8', [('V8', 8, v8_specs())])]
    for (tag, cs) in legs:
        trip = 0
        skipA = skipB = 0
        for (_nm, n, specs) in cs:
            oidx = odd_idx(specs)
            k2 = len(oidx)
            oset = set(oidx)
            epairs = [(u, w) for i, (u, w, _L) in enumerate(specs)
                      if i not in oset]
            for pat in range(1 << k2):
                o, q = odd_profile(specs, n, oidx, pat)
                b = [q[v] - o[v] for v in range(n)]
                acnt = k2 - bin(pat).count('1')
                bcnt = bin(pat).count('1')
                doA = max(o) <= 2 if n else True
                doB = max(b) <= 2 if n else True
                if not doA:
                    skipA += 1
                if not doB:
                    skipB += 1
                for mask in range(1 << n):
                    S = [v for v in range(n) if (mask >> v) & 1]
                    eH = sum(1 for (u, w) in epairs
                             if (mask >> u) & 1 and (mask >> w) & 1)
                    inc = sum(1 for (u, w) in epairs
                              if (mask >> u) & 1 or (mask >> w) & 1)
                    # handshake sanity: sum_S d_v = inc + e_H
                    assert sum(3 - q[v] for v in S) == inc + eH, "handshake"
                    trip += 1
                    if doA:
                        n0 = sum(1 for v in S if o[v] == 0)
                        n1 = sum(1 for v in S if o[v] == 1)
                        n2 = sum(1 for v in S if o[v] == 2)
                        s = inc - n0
                        assert sum(b[v] for v in S) == \
                            2 * n0 + 2 * n1 + n2 - s - eH, "(GR-98) identity"
                        assert bcnt >= n1 - s, "(GR-98) b >= n_1(S) - s(S)"
                    if doB:
                        m0 = sum(1 for v in S if b[v] == 0)
                        m1 = sum(1 for v in S if b[v] == 1)
                        m2 = sum(1 for v in S if b[v] == 2)
                        sA = inc - m0
                        assert sum(o[v] for v in S) == \
                            2 * m0 + 2 * m1 + m2 - sA - eH, \
                            "(GR-98) identity, colour-swapped"
                        assert acnt >= m1 - sA, "(GR-98) a >= m_1(S) - s_A(S)"
        print(f"  {tag}: {trip} (shape, pattern, hub set) triples asserted; "
              f"{skipA} patterns skipped on the A side (an o = 3 hub), "
              f"{skipB} on the B side -- all infeasible by (GR-97)")
    print(f"  [{time.time() - t0:.1f}s]")


# ------------------------------------------------- [GFP-3] --thm ------------

def leg_thm():
    """[GFP-3] (GR-99): #blocked <= opposite count per side; >= |delta|
    feasible majority flips at every unbalanced feasible pattern."""
    t0 = time.time()
    print("[GFP-3] (GR-99) the selection theorem: at every feasible pattern "
          "#blocked A-branches <= b and #blocked B-branches <= a; at every "
          "unbalanced feasible pattern >= |delta| majority flips are "
          "feasible -- hence (GR-R1)")
    rng = random.Random(R_SEED + 3)
    print(f"  seed {R_SEED + 3}")
    legs = [('stratum n_hub <= 6 (EXHAUSTIVE)', stratum_cases(), None),
            ('V8', [('V8', 8, v8_specs())], None)]
    legs += [(t, cs, None) for (t, cs) in seeded_legs(rng)]
    named = [(tag, n, sp) for (tag, n, sp) in named_cases()
             if odd_idx(sp)]
    legs.append(('named large shapes (SAMPLED patterns)', named, 300))
    beyond, _conc = random_cases(rng, (12, 16), 6, (8, 10), 0.5)
    legs.append(('beyond-habitat random cubic 2k = 8/10 '
                 '(NOT excess-6 -- the theorem has no 2k cap)', beyond, None))
    for (tag, cs, patcap) in legs:
        nfeas = nunb = 0
        blkA = collections.Counter()
        blkB = collections.Counter()
        tightA = tightB = 0
        r1min = None
        capped = 0
        for (_nm, n, specs) in cs:
            oidx = odd_idx(specs)
            k2 = len(oidx)
            if patcap is not None and k2 > 8:
                pats = {rng.randrange(1 << k2) for _ in range(patcap)}
                capped += 1
            else:
                pats = range(1 << k2)
            for pat in pats:
                p = [(pat >> t) & 1 for t in range(k2)]
                if feasible_at(specs, n, oidx, p) is None:
                    continue
                nfeas += 1
                acnt = k2 - sum(p)
                bcnt = sum(p)
                bA, bB = blocked_of(specs, n, oidx, pat)
                assert len(bA) <= bcnt, "(GR-99) FAILS on the A side"
                assert len(bB) <= acnt, "(GR-99) FAILS on the B side"
                blkA[len(bA)] += 1
                blkB[len(bB)] += 1
                if len(bA) == bcnt and bA:
                    tightA += 1
                if len(bB) == acnt and bB:
                    tightB += 1
                delta = imb_of(k2, pat)
                if delta:
                    nunb += 1
                    if delta > 0:
                        nf = acnt - len(bA)
                    else:
                        nf = bcnt - len(bB)
                    assert nf >= abs(delta), \
                        "(GR-99) corollary FAILS: < |delta| feasible " \
                        "majority flips"
                    assert nf >= 1, "(GR-R1) FAILS at this pattern"
                    if r1min is None or nf < r1min:
                        r1min = nf
        print(f"  {tag}: {nfeas} feasible patterns ({nunb} unbalanced), "
              f"0 violations"
              + (f", {capped} shapes pattern-SAMPLED" if capped else ""))
        print(f"    #blocked-A histogram {hist(blkA)}, #blocked-B "
              f"histogram {hist(blkB)}; bound tight "
              f"(#blocked = opposite count > 0): A side {tightA}, "
              f"B side {tightB}")
        if nunb:
            print(f"    minimum #feasible majority flips at an unbalanced "
                  f"pattern: {r1min} (the corollary needs >= |delta| >= 2; "
                  f"(GR-R1) needs >= 1)")
    print(f"  [{time.time() - t0:.1f}s]")


# ------------------------------------------------- [GFP-4] --wit ------------

def leg_wit():
    """[GFP-4] witness anatomy at every blocked stratum instance, plus the
    controls."""
    t0 = time.time()
    print("[GFP-4] witness anatomy: every blocked (shape, feasible pattern, "
          "branch) instance on the stratum has a demand-form violator of "
          "the exact (GR-99) proof shape (s <= e_gamma - 1, e_gamma >= 1, "
          "kept side monotone)")
    anat = collections.Counter()
    nblk = nfeas = 0
    ex = None
    for (nm, n, specs) in stratum_cases():
        oidx = odd_idx(specs)
        k2 = len(oidx)
        for pat in range(1 << k2):
            p = [(pat >> t) & 1 for t in range(k2)]
            if feasible_at(specs, n, oidx, p) is None:
                continue
            nfeas += 1
            bA, bB = blocked_of(specs, n, oidx, pat)
            for j in bA + bB:
                nblk += 1
                key = wit_anatomy(specs, n, oidx, pat, j)
                anat[key] += 1
                if ex is None:
                    ex = (nm, n, pat, oidx[j], key)
    print(f"  stratum (EXHAUSTIVE): {nfeas} feasible patterns, "
          f"{nblk} blocked (pattern, branch) instances, all with a "
          f"proof-shaped witness")
    print(f"    (s, e_gamma, |S|) of the minimal violator: {hist(anat)}")
    if ex:
        print(f"    first blocked instance: shape {ex[0]} (n_hub = {ex[1]}), "
              f"pattern bits {ex[2]}, branch {ex[3]}, anatomy {ex[4]}")
    print("    control (F13): the naive stronger sentence 'no branch is "
          "ever blocked' is "
          + ("REFUTED by the instances above" if nblk else
             "NOT separated on this leg (0 blocked instances)"))
    print(f"  [{time.time() - t0:.1f}s]")


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--form', action='store_true')
    ap.add_argument('--lemma', action='store_true')
    ap.add_argument('--thm', action='store_true')
    ap.add_argument('--wit', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.validate:
        args.form = args.lemma = args.thm = args.wit = True
    if not (args.form or args.lemma or args.thm or args.wit):
        ap.error('pick a mode (--form --lemma --thm --wit or --validate)')
    if args.form:
        leg_form()
    if args.lemma:
        leg_lemma()
    if args.thm:
        leg_thm()
    if args.wit:
        leg_wit()
    print("gflip: all requested legs PASSED")


if __name__ == '__main__':
    main()
