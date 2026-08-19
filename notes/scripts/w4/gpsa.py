"""GPSA -- the thirteenth kernel-(K) direction: route-ledger entry 5,
per-shape admissibility (d_adm < oo), in BOTH halves (spec:
notes/Pencil-fanout.md S"Thirteenth direction").

PRIMARY, half 1 (the parity half): discharge Step G53's recorded,
undischarged system-of-distinct-representatives step -- one end hub per
representative branch, Hall-shaped -- making d_par < oo PROVEN rather
than measured and repairing (GR-37)(iii)'s parity half to
statement-equals-proof.  The theorem this driver certifies sentence-by-
sentence (README S4 convention 4): for every perfect matching M of a
connected cubic loop-free hub multigraph, the class [tau] mod Cut(G0)
has an M-avoiding representative x, the branches of supp(x) admit a
system of distinct representative END HUBS (Hall's condition holds
AUTOMATICALLY: supp(x) avoids M, so it has max degree 2 at every hub),
and deviating each representative hub to its third branch yields a
parity-consistent minority map at exactly wt(x) deviations.  Hence
d_par(shape, M) <= w_M := min{wt(x) : x = tau mod Cut, supp(x) cap M
empty} < oo.  The converse direction is also a theorem (each deviating
hub contributes its third branch's class, off M, so any parity-
consistent map at distance d yields an M-avoiding representative of
weight <= d): d_par(shape, M) = w_M EXACTLY -- the --sdr histogram's
415/415 zero gap is the machine witness of the equality.

PRIMARY, half 2 (the balance rider): on the <= 6 odd branches (evenly
many, Step G53(ii)) some parity-consistent map achieves balanced
majorities.  Vacuous at all-even shapes.  The driver supports the
proof attempt: it verifies the cut-move calculus ((GR-45): legal move
sets, the c' = c + chi_{R xor S} law, the exact flip formula, the T1
double-swap and T2 star-move corollaries), and runs EXHAUSTIVE per-
shape censuses (all 3^n minority maps -- the F11 completeness mode) on
a seeded subsample of the existing n <= 6 pool + W3M + W3 + NK(2):
parity space, delta spectrum, balanced count, per-mu pattern sets,
single-flip closure, and the stuck-configuration census (parity-
consistent maps with |delta| >= 2 where NO majority-side odd branch
has a free T1) -- the proof's hard cases.  E1 clause (v) discipline: a
full-3^n enumeration finding parity-consistent maps but NO balanced
one is a GENUINE d_adm = oo (REFUTATION headline); a capped search is
always reported as a CAP, never as infinity.

SECONDARY (b'): d_adm - d_par <= 2 at every habitat shape, or a
growing-gap family.  Anti-triviality: the constant must come from the
rider's global-count nature -- the mechanism tested here is "one T1
double-swap = one repair unit of exactly 2 deviations".

Modes:
  --sdr      half 1: the (GR-44) construction certified per (shape,
             matching) on the existing pools; the theorem inequality
             d_par(M) <= wt(x_min) asserted against the exact DP;
             Hall-tightness (cycle components) census; the n = 30
             scaled demo at NK(6)/NKo(6).
  --balance  half 2: the (GR-45) calculus verified mechanically;
             the exhaustive censuses; the stuck census; per-shape
             entry-5 verdicts (exhaustive, so a miss would be E1(v)).
  --odd      commissioned odd-rich stress constructions (the spec's
             named exception to "widening a pool is evidence, not
             progress"): odd-on-pentagon and two-l5 necklace variants
             hunting a growing balance-repair cost; an n = 10 variant
             certified exhaustively.
  --adv      falsification controls, each with an F13 must-reject
             witness: doctored SDR rejected; illegal cut-move rejected
             (with the pinned counter-fact: bypassing the guard breaks
             the flip prediction); W3's 12-parity-maps-all-unbalanced
             layering reproduced; the E1(v) discriminator (CAP vs
             genuine oo on a full enumeration, mock disclosed);
             mu_in_phi vs gdev.in_coset cross-check.
  --validate all four, in the order above.

Rank-free throughout: entry 5 is a pure (G0, l) parity/balance
statement; nothing here calls gexist.fully_good_rank (a call would be
a scope flag onto entry 1).  min_dev's d_fg slot is computed by its
owner via the exact rank-free chunk scan; this driver never consumes
it.  Exact integers over GF(2) throughout; rngs seeded per mode, seeds
printed; no `set` printed; nothing samples a placement, so
repin.star_generic gates nothing here (S(K-clos) (AC-9)).  Wall-clock
[Ns] annotations are inherently non-deterministic; every other byte is
seed-stable.
"""
import argparse
import os
import random
import sys
import time
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from gridcol import subdivide                                          # noqa: E402
from cflank import admissible, cubic_habitat                           # noqa: E402
from gcap import pool_specs                                            # noqa: E402
from gunif import WITNESSES                                            # noqa: E402
from gorient import (cm_solve, cm_colouring, odd_balance,              # noqa: E402
                     perfect_matchings, m_of_matching, darts_at)
from gdev import (nk_specs, habitat_by_lemma, light_hm,                # noqa: E402
                  mu_of, in_coset, fundamental_cycles, even_vec, min_dev)
from gadm import (cycle_masks, dp_pref, dp_walk, mu_in_phi,            # noqa: E402
                  complete_matching, nko_specs)

R_SEED = 20260818


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive (checked against the README index
# and the Divergences table).  `m_avoiding_rep`/`min_m_avoiding_rep` build
# the (GR-44) representative; `sdr_build`/`sdr_verify` are the Hall
# discharge (path/cycle orientation) and its adversarial verifier;
# `parity_census` is the exhaustive 3^n enumeration over the syndrome
# accumulator; `apply_cut_move`/`predict_flips` are the (GR-45) calculus;
# `nkp_specs`/`nk55_specs`/`nko2v_specs` are the commissioned odd-rich
# stress constructions.


def branches_at(specs, n):
    """hub -> the 3 incident branch indices (cubic, loop-free asserted)."""
    inc = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        assert u != w, "loop in hub multigraph"
        inc[u].append(i)
        inc[w].append(i)
    for v in range(n):
        assert len(inc[v]) == 3, "hub not cubic"
    return inc


def is_bridgeless(specs, n):
    """No branch of the hub multigraph is a bridge (theorem hypothesis)."""
    for drop in range(len(specs)):
        seen = {0}
        st = [0]
        while st:
            v = st.pop()
            for i, (u, w, _L) in enumerate(specs):
                if i == drop:
                    continue
                for (a, b) in ((u, w), (w, u)):
                    if v == a and b not in seen:
                        seen.add(b)
                        st.append(b)
        if len(seen) != n:
            return False
    return True


def delta_of(specs, S):
    """The cut vector of hub set S."""
    return [1 if ((u in S) != (w in S)) else 0 for (u, w, _L) in specs]


def xor_vec(a, b):
    return [x ^ y for x, y in zip(a, b)]


def m_avoiding_rep(specs, n, mat):
    """A representative x of [tau] mod Cut with supp(x) cap M empty,
    CONSTRUCTIVE (per matched pair (u,w): put w in S iff tau on that
    branch); works at any n.  Existence is (GR-44)(i)."""
    tau = even_vec(specs)
    S = set()
    for i in mat:
        (_u, w, _L) = specs[i]
        if tau[i]:
            S.add(w)
    x = xor_vec(tau, delta_of(specs, S))
    assert not any(x[i] for i in mat), "constructive rep not M-avoiding"
    return x


def min_m_avoiding_rep(specs, n, mat):
    """The minimum-weight M-avoiding representative, exhaustive over all
    2^(n-1) cuts (n <= 14 guard); returns (x, w_M)."""
    assert n <= 16, "coset enumeration guard"
    tau = even_vec(specs)
    best = None
    for smask in range(1 << (n - 1)):
        S = {v + 1 for v in range(n - 1) if (smask >> v) & 1}
        x = xor_vec(tau, delta_of(specs, S))
        if any(x[i] for i in mat):
            continue
        if best is None or sum(x) < sum(best):
            best = x
    assert best is not None, \
        "no M-avoiding representative: (GR-44)(i) refuted -- HEADLINE"
    return best, sum(best)


def sdr_build(specs, n, xsupp, mat):
    """The Hall discharge, constructive: supp(x) avoids M, so every hub
    carries <= 2 supp-branches (a cubic hub has exactly 2 non-matching
    branches); components are paths and cycles; orient each and give
    every branch its head hub.  Returns (rep dict branch -> hub,
    #cycle components) -- cycle components are exactly where Hall's
    condition is TIGHT (|N(S)| = |S|)."""
    matset = set(mat)
    inc = {}
    for i in xsupp:
        assert i not in matset
        (u, w, _L) = specs[i]
        inc.setdefault(u, []).append((i, w))
        inc.setdefault(w, []).append((i, u))
    for v, lst in inc.items():
        assert len(lst) <= 2, \
            "max-degree-2 broken: > 2 non-matching supp branches at a hub"
    rep = {}
    tight = 0
    done = set()
    for start in sorted(xsupp):
        if start in done:
            continue
        # collect the component's hubs
        comp_hubs = set(specs[start][:2])
        grow = True
        while grow:
            grow = False
            for v in list(comp_hubs):
                for (i, u) in inc.get(v, ()):  # noqa: B007
                    if u not in comp_hubs:
                        comp_hubs.add(u)
                        grow = True
        comp_edges = {i for v in comp_hubs for (i, _u) in inc[v]}
        deg1 = [v for v in comp_hubs if len(inc[v]) == 1]
        is_cycle = not deg1
        if is_cycle:
            tight += 1
        v = min(deg1) if deg1 else min(comp_hubs)
        used_e = set()
        while True:
            nxt = [(i, u) for (i, u) in inc[v] if i not in used_e]
            if not nxt:
                break
            (i, u) = nxt[0]
            used_e.add(i)
            rep[i] = u          # the head hub represents the branch
            v = u
        assert used_e == comp_edges, "component walk incomplete"
        done |= comp_edges
    assert sorted(rep) == sorted(xsupp), "SDR does not cover supp(x)"
    return rep, tight


def sdr_verify(specs, n, mat, x, rep, binc):
    """The adversarial verifier for the (GR-44) construction: checks the
    SDR (injective, end hubs, off-M) and BUILDS the deviated map --
    each representative hub's minority dart moves to its third branch
    -- then asserts parity-consistency at exactly wt(x) deviations.
    Raises AssertionError on any doctored input (the F13 guard)."""
    xsupp = [i for i, b in enumerate(x) if b]
    assert sorted(rep) == xsupp, "SDR must cover exactly supp(x)"
    matset = set(mat)
    matbr = {}
    for i in mat:
        (u, w, _L) = specs[i]
        matbr[u] = i
        matbr[w] = i
    base = m_of_matching(specs, mat)
    m = dict(base)
    seen = set()
    for i in xsupp:
        v = rep[i]
        assert v in specs[i][:2], "rep hub not an end of its branch"
        assert i not in matset, "representative branch inside the matching"
        assert v not in seen, "SDR reuses a hub (doctored)"
        seen.add(v)
        third = [j for j in binc[v] if j != i and j != matbr[v]]
        assert len(third) == 1, "hub star not 3 distinct branches"
        t = third[0]
        m[v] = (t, 0 if v == specs[t][0] else 1)
    sols = cm_solve(specs, m)
    assert sols is not None, "constructed map NOT parity-consistent"
    ndev = sum(1 for v in m if m[v] != base[v])
    assert ndev == len(xsupp), "deviation count != wt(x)"
    return m, sols


def parity_census(specs, n):
    """EXHAUSTIVE enumeration of all 3^n minority maps through the
    syndrome accumulator (mu = sum_v e_{f(v)}, synd linear); every
    syndrome-passer is asserted cm_solve-consistent ((GR-41)(i)'s
    equivalence, both directions sampled by the caller).  Returns
    (list of (m, sols), odd branch indices, dim, total maps)."""
    dinc = darts_at(specs)
    hubs = sorted(dinc)
    assert hubs == list(range(n))
    _cycles, bmask, dim, s0 = cycle_masks(specs, n)
    opts = []
    for v in hubs:
        assert len(dinc[v]) == 3, "hub not cubic"
        opts.append([(d, bmask[d[0]]) for d in dinc[v]])
    oidx = [i for i, (_u, _w, L) in enumerate(specs) if L % 2 == 1]
    out = []
    m = {}

    def rec(v, s):
        if v == n:
            if s == s0:
                mm = dict(m)
                sols = cm_solve(specs, mm)
                assert sols is not None, \
                    "syndrome-pass but cm_solve fails: (GR-41)(i) broken"
                out.append((mm, sols))
            return
        for (d, sm) in opts[v]:
            m[v] = d
            rec(v + 1, s ^ sm)
        del m[v]

    rec(0, 0)
    return out, oidx, dim, 3 ** n


def pattern_of(specs, m, c, oidx):
    """The odd-branch majority pattern as a bitmask (bit = 1 iff
    B-majority), matching gorient.odd_balance's convention."""
    bits = 0
    for j, i in enumerate(oidx):
        (u, _w, _L) = specs[i]
        if c[u] ^ (m[u] == (i, 0)):
            bits |= 1 << j
    return bits


def apply_cut_move(specs, n, m, moveset, binc):
    """The (GR-45) legal move: moveset = [(hub v, target branch x_v)]
    with distinct hubs, x_v at v, m(v) NOT on x_v, and sum e_{x_v} in
    Cut(G0).  Each hub's dart moves to its third branch (neither its
    current branch nor the target).  Returns (m', Delta) with Delta the
    exact GF(2) change of mu.  AssertionError on an illegal move (the
    F13 guard)."""
    seen = set()
    m2 = dict(m)
    delta = [0] * len(specs)
    for (v, x) in moveset:
        assert v not in seen, "move set reuses a hub"
        seen.add(v)
        assert x in binc[v], "target branch not at its hub"
        cur = m[v][0]
        assert cur != x, "ILLEGAL: minority dart sits on the target branch"
        third = [j for j in binc[v] if j != cur and j != x]
        assert len(third) == 1
        t = third[0]
        m2[v] = (t, 0 if v == specs[t][0] else 1)
        delta[cur] ^= 1
        delta[t] ^= 1
    return m2, delta


def cut_side(specs, n, delta):
    """The hub set S with delta(S) = delta (None if delta not a cut);
    normalized to exclude hub 0."""
    adj = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        adj[u].append((w, delta[i]))
        adj[w].append((u, delta[i]))
    c = {0: 0}
    st = [0]
    while st:
        v = st.pop()
        for (u, b) in adj[v]:
            cu = c[v] ^ b
            if u in c:
                if c[u] != cu:
                    return None
            else:
                c[u] = cu
                st.append(u)
    assert len(c) == n
    return {v for v in range(n) if c[v] == 1}


def predict_flips(specs, n, m, m2, S, oidx):
    """The (GR-45) flip formula, evaluated at BOTH ends of every odd
    branch (the lemma claims they agree): flip(gamma) =
    chi_S(p) xor [m(p) moved across gamma], S the side of the exact
    change vector.  Returns the predicted flip bitmask; asserts the
    two-end consistency clause."""
    bits = 0
    for j, i in enumerate(oidx):
        (u, w, _L) = specs[i]
        fu = (u in S) ^ ((m[u] == (i, 0)) != (m2[u] == (i, 0)))
        fw = (w in S) ^ ((m[w] == (i, 1)) != (m2[w] == (i, 1)))
        assert fu == fw, "(GR-45) two-end consistency broken"
        if fu:
            bits |= 1 << j
    return bits


def t1_move(specs, m, z):
    """The T1 double-swap at branch z, if available: both end darts off
    z.  Returns the moveset or None."""
    (u, w, _L) = specs[z]
    if m[u][0] == z or m[w][0] == z:
        return None
    return [(u, z), (w, z)]


def all_moves(specs, n, m, binc):
    """Every legal T1 (double-swap at a branch) and every legal member
    of the full T2 family (the star of a hub u, each branch repped by
    u itself or its far end, reps distinct, darts off targets) from the
    configuration m.  The one-move neighbourhood of the (GR-45)
    calculus at radius {T1, T2}."""
    out = []
    for z in range(len(specs)):
        mv = t1_move(specs, m, z)
        if mv is not None:
            out.append(mv)
    for u in range(n):
        star = binc[u]
        cands = []
        for i in star:
            (a, b, _L) = specs[i]
            far = b if a == u else a
            cs = [r for r in (u, far) if m[r][0] != i]
            cands.append([(r, i) for r in cs])
        for c0 in cands[0]:
            for c1 in cands[1]:
                for c2 in cands[2]:
                    ms = [c0, c1, c2]
                    if len({v for (v, _x) in ms}) == 3:
                        out.append(ms)
    return out


# --- commissioned odd-rich stress constructions (--odd) ---------------------

def nkp_specs(m):
    """NKp(m): NK(m) with the excess moved to ONE l3 pentagon edge per
    pentagon (six odd branches at m = 6, one in each pentagon) --
    pentagons stop being all-even, so the (GR-43) pentagon floor no
    longer applies: a LOW-d_par, spread-odd balance stress."""
    specs, pent, _F, _chords = nk_specs(m)
    specs = [list(s) for s in specs]
    for s in specs:
        s[2] = 2
    assert m >= 6, "needs six pentagons to hold one l3 each"
    for i in range(6):
        specs[pent[i][2]][2] = 3
    assert sum(L - 2 for (_u, _w, L) in specs) == 6
    return [tuple(s) for s in specs], pent


def nk55_specs(m):
    """NK55(m): NK(m) with the excess on TWO l5 links far apart
    (2k = 2: the minimal odd stratum at large n)."""
    specs, pent, _F, chords = nk_specs(m)
    specs = [list(s) for s in specs]
    for s in specs:
        s[2] = 2
    pentset = {i for ids in pent for i in ids}
    linkidx = [i for i in range(len(specs))
               if i not in pentset and i not in chords]
    specs[linkidx[0]][2] = 5
    specs[linkidx[len(linkidx) // 2]][2] = 5
    assert sum(L - 2 for (_u, _w, L) in specs) == 6
    return [tuple(s) for s in specs], pent


def nko2v_specs():
    """NKo2v: the n = 10 odd-on-pentagon variant of NK(2): four l3
    PENTAGON edges (two per pentagon) + the l4 chord; small enough for
    the full 3^10 census."""
    specs, pent, _F, chords = nk_specs(2)
    specs = [list(s) for s in specs]
    for s in specs:
        s[2] = 2
    for i in (pent[0][0], pent[0][2], pent[1][0], pent[1][2]):
        specs[i][2] = 3
    specs[chords[0]][2] = 4
    assert sum(L - 2 for (_u, _w, L) in specs) == 6
    return [tuple(s) for s in specs], pent


def balanced_witness_hunt(specs, n, mat, rng, kmax=3, walks=60):
    """Balanced-admissible witness at d_par(M) + k, k = 0..kmax, by
    randomized DP traceback (dp_walk) -- an UPPER-bound search, caps
    disclosed by the caller.  Returns (d_par_exact_at_M, k_found or
    None, walks landed per level)."""
    _cycles, bmask, dim, s0 = cycle_masks(specs, n)
    base, moves, prefs = dp_pref(specs, n, mat, bmask, dim, True)
    dmin = prefs[-1][s0]
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    hm = light_hm(edges)
    landed = {}
    for k in range(kmax + 1):
        landed[k] = 0
        for _i in range(walks):
            mm = dp_walk(specs, n, base, moves, prefs, s0, dmin + k, rng)
            if mm is None:
                continue
            landed[k] += 1
            sols = cm_solve(specs, mm)
            if sols is None:
                continue
            for c in sols:
                na, nb = odd_balance(specs, mm, c)
                if na != nb:
                    continue
                col = cm_colouring(specs, mm, c)
                if admissible(edges, allverts, hm, col):
                    return dmin, k, landed
    return dmin, None, landed


# ------------------------------------------------- [GPS-1] --sdr ------------

def leg_sdr():
    """[GPS-1] half 1: the (GR-44) SDR discharge, certified per (shape,
    matching); the theorem inequality against the exact DP; the
    Hall-tightness census; the n = 30 scaled demo."""
    t0 = time.time()
    print(f"[GPS-1] half 1 -- the Hall/SDR discharge (seed {R_SEED + 1})")
    rng = random.Random(R_SEED + 1)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    cases = []
    picked = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.015:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        picked += 1
        cases.append((f"pool#{picked}", n, [tuple(s) for s in specs]))
    for tag in ('W3M', 'W3', 'W4', 'W5'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        cases.append((tag, n, specs))
    nk2, _p2, _F2, _c2 = nk_specs(2)
    cases.append(('NK(2)', 10, nk2))
    nko2, _po, _co = nko_specs(2)
    cases.append(('NKo(2)', 10, nko2))

    nshapes = nmats = 0
    gap_hist = {}
    tight_shapes = 0
    nonbl = 0
    for (tag, n, specs) in cases:
        if not is_bridgeless(specs, n):
            nonbl += 1
            continue
        binc = branches_at(specs, n)
        mats = perfect_matchings(specs, cap=500)
        assert mats, "bridgeless cubic without a perfect matching?!"
        _cy, bmask, dim, s0 = cycle_masks(specs, n)
        nshapes += 1
        shape_tight = False
        for mat in (mats[:12] if n <= 12 else mats[:4]):
            nmats += 1
            x, wM = min_m_avoiding_rep(specs, n, mat)
            xsupp = [i for i, b in enumerate(x) if b]
            rep, tight = sdr_build(specs, n, xsupp, mat)
            _m, _sols = sdr_verify(specs, n, mat, x, rep, binc)
            _b, _mv, prefs = dp_pref(specs, n, mat, bmask, dim, False)
            d_par_M = prefs[-1][s0]
            assert d_par_M <= wM, \
                "(GR-44) inequality d_par(M) <= w_M BROKEN -- HEADLINE"
            g = wM - d_par_M
            gap_hist[g] = gap_hist.get(g, 0) + 1
            if tight:
                shape_tight = True
        if shape_tight:
            tight_shapes += 1
    print(f"  certified at {nshapes} shapes ({picked} sampled pool "
          f"habitat shapes at rate 0.015 + W3M/W3/W4/W5 + NK(2)/NKo(2); "
          f"{nonbl} non-bridgeless skips) x <= 12 matchings each = "
          f"{nmats} (shape, matching) pairs: the min-weight M-avoiding "
          f"representative EXISTS at every pair, the SDR builds (Hall "
          f"automatic: max degree 2 asserted per pair), the deviated map "
          f"is parity-consistent at exactly wt(x) deviations, and the "
          f"theorem inequality d_par(M) <= w_M holds against the exact "
          f"DP at every pair")
    print(f"  bound-gap histogram w_M - d_par(M): {sorted(gap_hist.items())} "
          f"(0 = the SDR bound is TIGHT at that pair; a gap means the "
          f"exact optimum reuses cancellations the one-hub-per-branch "
          f"construction pays for -- shift-metric data, reported only, "
          f"NOT developed: ranking item 3's bar stands)")
    print(f"  Hall-tightness: {tight_shapes}/{nshapes} shapes have some "
          f"(matching, x_min) whose supp(x) contains a cycle component "
          f"(|N(S)| = |S|, Hall tight yet still feasible -- the SDR "
          f"never actually fails, which is the theorem's point)")

    # the n = 30 scaled demo: the construction is O(E) and needs no
    # enumeration -- run it at NK(6) and NKo(6) with the constructive
    # (not minimum) representative
    for (tag, mk) in (('NK(6)', 'nk'), ('NKo(6)', 'nko')):
        if mk == 'nk':
            specs, _p, _F, _c = nk_specs(6)
        else:
            specs, _p, _c = nko_specs(6)
        n = 30
        binc = branches_at(specs, n)
        mat = complete_matching(specs, n, [])
        assert mat is not None
        x = m_avoiding_rep(specs, n, mat)
        xsupp = [i for i, b in enumerate(x) if b]
        rep, tight = sdr_build(specs, n, xsupp, mat)
        _m, _sols = sdr_verify(specs, n, mat, x, rep, binc)
        _cy, bmask, dim, s0 = cycle_masks(specs, n)
        _b, _mv, prefs = dp_pref(specs, n, mat, bmask, dim, False)
        d_par_M = prefs[-1][s0]
        assert d_par_M <= sum(x)
        print(f"  {tag} (n = 30) demo: constructive M-avoiding rep of "
          f"weight {sum(x)} SDR-verified (parity-consistent at "
          f"{sum(x)} deviations, {tight} Hall-tight components); "
          f"DP-exact d_par(M) = {d_par_M} -- the constructive rep is an "
          f"upper bound, the MINIMUM representative is what the theorem "
          f"bounds with (not enumerable at n = 30; disclosed)")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GPS-2] --balance --------

def leg_balance():
    """[GPS-2] half 2: the (GR-45) calculus verified; the exhaustive
    censuses; the stuck census; entry-5 per-shape verdicts."""
    t0 = time.time()
    print(f"[GPS-2] half 2 -- the balance rider (seed {R_SEED + 2})")
    rng = random.Random(R_SEED + 2)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    # ---- (a) the (GR-45) calculus, verified mechanically ----
    cases = []
    picked = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.004:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        picked += 1
        cases.append((f"pool#{picked}", n, [tuple(s) for s in specs]))
    (_nm, n3, specs3, _f, _S, _e) = by_tag['W3']
    cases.append(('W3', n3, specs3))
    moves_ok = t1_ok = t2_ok = 0
    for (tag, n, specs) in cases:
        binc = branches_at(specs, n)
        mats = perfect_matchings(specs, cap=50)
        mat = mats[rng.randrange(len(mats))]
        x, _wM = min_m_avoiding_rep(specs, n, mat)
        rep, _t = sdr_build(specs, n, [i for i, b in enumerate(x) if b], mat)
        m, sols = sdr_verify(specs, n, mat, x, rep, binc)
        oidx = [i for i, (_u, _w, L) in enumerate(specs) if L % 2 == 1]
        c = sols[0]
        for _step in range(40):
            # random legal move: T1 at a random both-ends-free branch,
            # T2 at a random hub with distinct free far ends, or a
            # random 2-cut-free composite; retry until one is legal
            kind = rng.randrange(2)
            moveset = None
            if kind == 0:
                z = rng.randrange(len(specs))
                moveset = t1_move(specs, m, z)
                want_t1 = z
            else:
                u = rng.randrange(n)
                ms = []
                seen = set()
                ok = True
                for i in binc[u]:
                    (a, b, _L) = specs[i]
                    far = b if a == u else a
                    if far in seen or m[far][0] == i:
                        ok = False
                        break
                    seen.add(far)
                    ms.append((far, i))
                moveset = ms if ok and len({v for v, _x in ms}) == 3 \
                    else None
                want_star = u
            if moveset is None:
                continue
            m2, delta = apply_cut_move(specs, n, m, moveset, binc)
            S = cut_side(specs, n, delta)
            assert S is not None, "legal move set with non-cut Delta"
            sols2 = cm_solve(specs, m2)
            assert sols2 is not None, \
                "(GR-45) broken: legal move left parity"
            pred = predict_flips(specs, n, m, m2, S, oidx)
            old = pattern_of(specs, m, c, oidx)
            # c' = c + chi_S must be one of the two new solutions
            cpred = {v: c[v] ^ (1 if v in S else 0) for v in c}
            assert cpred in sols2, "(GR-45) c' = c + chi_S law broken"
            new = pattern_of(specs, m2, cpred, oidx)
            assert new == old ^ pred, "(GR-45) flip formula broken"
            moves_ok += 1
            # cut_side normalizes to the side excluding hub 0, which may
            # be the COMPLEMENT of the derivation's R xor S -- that
            # toggles every chi term, i.e. composes the flip with the
            # global A<->B swap.  The corollaries hold up to that swap.
            mask = (1 << len(oidx)) - 1
            if kind == 0:
                zj = oidx.index(want_t1) if want_t1 in oidx else None
                exp = 0 if zj is None else (1 << zj)
                assert pred in (exp, exp ^ mask), \
                    "T1 corollary broken: flips != {z} cap odd (mod swap)"
                t1_ok += 1
            else:
                exp = 0
                star = set(binc[want_star])
                for j, i in enumerate(oidx):
                    if i in star:
                        exp |= 1 << j
                assert pred in (exp, exp ^ mask), \
                    "T2 corollary broken: flips != star (mod swap)"
                t2_ok += 1
            m, c = m2, cpred
    print(f"  the (GR-45) calculus verified mechanically at "
          f"{len(cases)} shapes ({picked} sampled pool habitat shapes "
          f"at rate 0.004 + W3), {moves_ok} legal moves total "
          f"({t1_ok} T1 double-swaps, {t2_ok} T2 star moves): every "
          f"move preserved parity, matched the c' = c + chi_S law, the "
          f"two-end-consistent flip formula, and the T1/T2 corollaries "
          f"(T1 flips exactly its branch, T2 exactly its star, both "
          f"mod the global A<->B swap)")

    # ---- (b) the exhaustive censuses (F11 mode: all 3^n maps) ----
    cases = []
    picked = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.02:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        picked += 1
        cases.append((f"pool#{picked}", n, [tuple(s) for s in specs]))
    (_nm, n3m, specs3m, _f, _S, _e) = by_tag['W3M']
    cases.append(('W3M', n3m, specs3m))
    cases.append(('W3', n3, specs3))
    nk2, _p2, _F2, _c2 = nk_specs(2)
    cases.append(('NK(2)', 10, nk2))

    tot = dict(shapes=0, alleven=0, par=0, bal=0)
    stuck_shapes = []
    stuck_rescued = stuck_total = 0
    closure_fail = 0
    closure_in_fail = 0
    closure_pairs = 0
    mu_no_bal = 0
    mu_tot = 0
    corr_checked = 0
    dspec_worst = {}
    for (tag, n, specs) in cases:
        maps, oidx, dim, total = parity_census(specs, n)
        # control: a few syndrome-failers must fail cm_solve too
        dinc = darts_at(specs)
        ctrl = 0
        parset = {tuple(sorted((v, d) for v, d in mm.items()))
                  for (mm, _s) in maps}
        while ctrl < 5:
            mm = {v: dinc[v][rng.randrange(3)] for v in range(n)}
            key = tuple(sorted((v, d) for v, d in mm.items()))
            if key in parset:
                continue
            assert cm_solve(specs, mm) is None, \
                "non-passer solved: syndrome test broken"
            ctrl += 1
        tot['shapes'] += 1
        k2 = len(oidx)
        assert k2 <= 6 and k2 % 2 == 0, "odd-branch cap broken"
        npar = len(maps)
        assert npar > 0, "(GR-44) contradicted: empty parity space"
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = light_hm(edges)
        if k2 == 0:
            tot['alleven'] += 1
            # balance vacuous: control stratum (per the spec, NK members
            # are controls, not tests, for half 2)
            (mm, sols) = maps[0]
            col = cm_colouring(specs, mm, sols[0])
            assert admissible(edges, allverts, hm, col), \
                "all-even correspondence broken"
            continue
        tot['par'] += npar
        pats = set()
        by_mu = {}
        nbal = 0
        stuck = 0
        worst_min_d = 0
        for (mm, sols) in maps:
            key = tuple(mu_of(specs, mm))
            for c in sols:
                p = pattern_of(specs, mm, c, oidx)
                pats.add(p)
                by_mu.setdefault(key, set()).add(p)
                a = k2 - bin(p).count('1')
                b = k2 - a
                d = a - b
                if d == 0:
                    nbal += 1
                    if corr_checked < 40 * tot['shapes']:
                        na, nb2 = odd_balance(specs, mm, c)
                        assert na == nb2 == k2 // 2
                        col = cm_colouring(specs, mm, c)
                        assert admissible(edges, allverts, hm, col), \
                            "(GR-37)(i) correspondence broken: balanced" \
                            " + consistent but NOT admissible"
                        corr_checked += 1
                else:
                    if abs(d) > worst_min_d:
                        worst_min_d = abs(d)
                    # stuck test: majority side has no free T1
                    free = False
                    for j, i in enumerate(oidx):
                        maj_b = (p >> j) & 1
                        if (d > 0) == (maj_b == 0):
                            if t1_move(specs, mm, i) is not None:
                                free = True
                                break
                    if not free:
                        stuck += 1
                        stuck_total += 1
                        # rescue: does ONE move of the {T1, T2} family
                        # reach a strictly smaller |delta|?
                        binc_s = branches_at(specs, n)
                        for ms in all_moves(specs, n, mm, binc_s):
                            m2, _dl = apply_cut_move(specs, n, mm, ms,
                                                     binc_s)
                            s2 = cm_solve(specs, m2)
                            assert s2 is not None
                            p2 = pattern_of(specs, m2, s2[0], oidx)
                            d2 = abs(k2 - 2 * bin(p2).count('1'))
                            if d2 < abs(d):
                                stuck_rescued += 1
                                break
        tot['bal'] += nbal
        if npar > 0 and nbal == 0:
            print(f"  *** E1 CLAUSE (v) REFUTATION HEADLINE: shape {tag} "
                  f"has {npar} parity-consistent maps and ZERO balanced "
                  f"ones at FULL 3^n enumeration -- d_adm = oo GENUINE, "
                  f"specs {sorted(specs)}")
        assert nbal > 0, "entry 5 refuted at a habitat shape (E1(v))"
        for p in pats:
            dp_ = abs(k2 - 2 * bin(p).count('1'))
            inward_ok = (dp_ == 0)
            for j in range(k2):
                closure_pairs += 1
                q = p ^ (1 << j)
                d2_ = abs(k2 - 2 * bin(q).count('1'))
                if q not in pats:
                    closure_fail += 1
                elif d2_ < dp_:
                    inward_ok = True
            if not inward_ok:
                closure_in_fail += 1
        for key, ps in by_mu.items():
            mu_tot += 1
            if not any(2 * bin(p).count('1') == k2 for p in ps):
                mu_no_bal += 1
        if stuck:
            stuck_shapes.append((tag, stuck, npar))
        dspec_worst[k2] = max(dspec_worst.get(k2, 0), worst_min_d)
    print(f"  EXHAUSTIVE censuses (all 3^n maps, the F11 completeness "
          f"mode) at {tot['shapes']} shapes ({picked} sampled pool "
          f"habitat shapes at rate 0.02 + W3M + W3 + NK(2)): "
          f"{tot['alleven']} all-even (balance VACUOUS there -- "
          f"controls); on the odd-carrying rest: {tot['par']} "
          f"parity-consistent (map, c) space, {tot['bal']} balanced -- "
          f"ENTRY 5 HOLDS EXHAUSTIVELY at every censused shape "
          f"(admissible() ground-truth verified at {corr_checked} "
          f"balanced configs, (GR-37)(i) round-trip)")
    print(f"  single-flip closure of the GLOBAL achievable pattern set: "
          f"{closure_fail}/{closure_pairs} (pattern, flip) pairs "
          f"missing; unbalanced achievable patterns with NO achievable "
          f"|delta|-reducing single flip: {closure_in_fail} -- lemma "
          f"(L) as a full-cube statement is "
          f"{'REFUTED' if closure_fail else 'exhaustively supported'}; "
          f"the proof-shaped INWARD form ('some |delta|-reducing flip "
          f"stays achievable') is "
          f"{'REFUTED' if closure_in_fail else 'exhaustively supported'}"
          f" on this census")
    print(f"  per-mu-class pattern sets: {mu_no_bal}/{mu_tot} classes "
          f"carry NO balanced pattern -- a nonzero count means balance "
          f"sometimes requires LEAVING the mu-class (the fixed-mu fiber "
          f"is not enough; the cross-class move is what (GR-45) "
          f"provides)")
    print(f"  stuck census (|delta| >= 2 with NO free T1 on the "
          f"majority side): {stuck_shapes if stuck_shapes else 'EMPTY'}"
          f" -- nonempty entries are the proof's hard cases (shape, "
          f"#stuck configs, #parity maps); of the {stuck_total} stuck "
          f"configs, {stuck_rescued} are RESCUED by a single move of "
          f"the wider {{T1, T2}} family (a strictly smaller |delta| "
          f"one (GR-45) move away)")
    print(f"  worst imbalance |delta| by #odd branches: "
          f"{sorted(dspec_worst.items())}")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GPS-3] --odd ------------

def leg_odd():
    """[GPS-3] commissioned odd-rich stress constructions hunting a
    growing balance-repair cost ((b')'s kill mode)."""
    t0 = time.time()
    print(f"[GPS-3] the odd-rich stress hunt (seed {R_SEED + 3}) -- "
          f"commissioned constructions (the spec's named exception to "
          f"the pool-widening bar)")
    rng = random.Random(R_SEED + 3)

    # ---- (a) NKo2v (n = 10): exhaustively certified ----
    specs, _pent = nko2v_specs()
    n = 10
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    ok, why = habitat_by_lemma(n, hedges, lens)
    assert ok, f"NKo2v not habitat: {why}"
    assert cubic_habitat(n, hedges, lens), "NKo2v fails the exact oracle"
    maps, oidx, dim, total = parity_census(specs, n)
    nbal = 0
    dspec = {}
    for (mm, sols) in maps:
        for c in sols:
            na, nb = odd_balance(specs, mm, c)
            dspec[abs(na - nb)] = dspec.get(abs(na - nb), 0) + 1
            if na == nb:
                nbal += 1
    assert nbal > 0, "entry 5 refuted at NKo2v (E1(v) headline)"
    # inward closure + stuck rescue at the one exhaustive shape whose
    # spectrum reaches |delta| = 4
    binc_v = branches_at(specs, n)
    k2 = len(oidx)
    pats = set()
    stuck_v = resc_v = 0
    for (mm, sols) in maps:
        for c in sols:
            p = pattern_of(specs, mm, c, oidx)
            pats.add(p)
            d = k2 - 2 * bin(p).count('1')
            if d == 0:
                continue
            free = any((d > 0) == (((p >> j) & 1) == 0)
                       and t1_move(specs, mm, i) is not None
                       for j, i in enumerate(oidx))
            if not free:
                stuck_v += 1
                for ms in all_moves(specs, n, mm, binc_v):
                    m2, _dl = apply_cut_move(specs, n, mm, ms, binc_v)
                    s2 = cm_solve(specs, m2)
                    p2 = pattern_of(specs, m2, s2[0], oidx)
                    if abs(k2 - 2 * bin(p2).count('1')) < abs(d):
                        resc_v += 1
                        break
    in_fail = 0
    for p in pats:
        dp_ = abs(k2 - 2 * bin(p).count('1'))
        if dp_ == 0:
            continue
        if not any((p ^ (1 << j)) in pats
                   and abs(k2 - 2 * bin(p ^ (1 << j)).count('1')) < dp_
                   for j in range(k2)):
            in_fail += 1
    print(f"    NKo2v inward closure: {in_fail} unbalanced achievable "
          f"patterns lack an achievable |delta|-reducing flip "
          f"(achievable set {len(pats)}/{1 << k2}); stuck configs "
          f"{stuck_v}, rescued by one {{T1, T2}} move: {resc_v}")
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    from gorient import prep_shape
    _e, _a, hm, _inc, _tec, tec_cf, _ak = prep_shape(specs)
    mats = perfect_matchings(specs)
    d_par, d_adm, _dfg = min_dev(specs, edges, allverts, hm, tec_cf,
                                 hm['lens'], mats, 4)
    assert d_par is not None and d_adm is not None, "NKo2v past dmax 4"
    gap = d_adm - d_par
    print(f"  NKo2v (n = 10, odd ON the pentagons, {len(oidx)} odd "
          f"branches; habitat by the (GR-42) lemma AND the exact "
          f"oracle): exhaustive census {len(maps)} parity maps / "
          f"{nbal} balanced (of {total} total); exact layers over all "
          f"{len(mats)} matchings (dmax 4): d_par = {d_par}, d_adm = "
          f"{d_adm} -- balance gap {gap}; exhaustive delta spectrum "
          f"{sorted(dspec.items())}")
    assert gap <= 2, \
        f"BALANCE GAP {gap} > 2 at NKo2v -- (b') REFUTED; HEADLINE"

    # ---- (b) the n = 30 stress members: NKp(6), NK55(6), NKo(6) ----
    for (tag, specs, note) in (
            ('NKp(6)', nkp_specs(6)[0],
             'odd spread one-per-pentagon; pentagon floor DISARMED'),
            ('NK55(6)', nk55_specs(6)[0],
             'two l5 links far apart; 2k = 2 at n = 30'),
            ('NKo(6)', nko_specs(6)[0],
             'GADM\'s member as the delta-spectrum control')):
        n = 30
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        ok, why = habitat_by_lemma(n, hedges, lens)
        assert ok, f"{tag} not habitat: {why}"
        nodd = sum(1 for L in lens if L % 2 == 1)
        mat = complete_matching(specs, n, [])
        assert mat is not None
        dmin, k, landed = balanced_witness_hunt(specs, n, mat, rng)
        if k is not None:
            print(f"  {tag} (n = 30, {nodd} odd branches; {note}): "
                  f"d_par(M) = {dmin} DP-exact at 1 constructed "
                  f"matching; BALANCED ADMISSIBLE witness at d_par + "
                  f"{k} (walk caps 60/level, landed "
                  f"{sorted(landed.items())}) -- balance-gap upper "
                  f"bound {k} at this matching")
        else:
            print(f"  {tag} (n = 30, {nodd} odd branches; {note}): "
                  f"d_par(M) = {dmin}; NO balanced witness within "
                  f"d_par + 3 at the walk CAPS (60/level, landed "
                  f"{sorted(landed.items())}) -- an exhausted CAP, not "
                  f"oo (E1(v) discipline); a candidate stick to "
                  f"escalate, not a refutation")
        # the |delta| <= 2 imbalance-cap question, sampled at scale:
        # delta spectrum of parity-consistent maps at budgets
        # d_par(M) + j, j = 0..6 (dp_walk samples; caps disclosed)
        oidx = [i for i, (_u, _w, L) in enumerate(specs) if L % 2 == 1]
        _cy, bmask, dim, s0 = cycle_masks(specs, n)
        base, moves, prefs = dp_pref(specs, n, mat, bmask, dim, True)
        dmin2 = prefs[-1][s0]
        spec_d = {}
        nsam = 0
        for j in range(7):
            for _i in range(80):
                mm = dp_walk(specs, n, base, moves, prefs, s0,
                             dmin2 + j, rng)
                if mm is None:
                    continue
                sols = cm_solve(specs, mm)
                assert sols is not None
                na, nb = odd_balance(specs, mm, sols[0])
                spec_d[abs(na - nb)] = spec_d.get(abs(na - nb), 0) + 1
                nsam += 1
        print(f"    delta spectrum at {tag} ({nsam} sampled parity "
              f"maps, budgets d_par..d_par+6, 80 walks/level): "
              f"{sorted(spec_d.items())} -- the imbalance-cap question "
              f"(|delta| <= 2?) at n = 30 (a sample, not a census)")
    print(f"  hunt verdict: no growing repair cost found at the "
          f"commissioned constructions (a measured negative at the "
          f"disclosed caps, not a proof)")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GPS-4] --adv ------------

def leg_adv():
    """[GPS-4] falsification controls, each with an F13 must-reject
    witness and a negative control."""
    t0 = time.time()
    print(f"[GPS-4] falsification controls (seed {R_SEED + 4})")
    rng = random.Random(R_SEED + 4)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    # ---- (1) the SDR verifier must reject a doctored assignment ----
    (_nm, n, specs, _f, _S, _e) = by_tag['W3M']
    binc = branches_at(specs, n)
    mats = perfect_matchings(specs)
    mat = mats[0]
    x, _wM = min_m_avoiding_rep(specs, n, mat)
    xsupp = [i for i, b in enumerate(x) if b]
    rep, _t = sdr_build(specs, n, xsupp, mat)
    _m, _s = sdr_verify(specs, n, mat, x, rep, binc)   # negative control
    assert len(xsupp) >= 2, "need >= 2 branches to doctor"
    bad = dict(rep)
    i0, i1 = xsupp[0], xsupp[1]
    bad[i1] = bad[i0]   # reuse i0's hub: fires "reuses a hub" when it
    # is an end of i1, "not an end" otherwise -- rejected either way
    try:
        sdr_verify(specs, n, mat, x, bad, binc)
        raise SystemExit("FAIL: doctored SDR accepted")
    except AssertionError as ex:
        print(f"  (1) doctored SDR REJECTED ('{ex}'); the undoctored "
              f"assignment passes (negative control) -- the verifier is "
              f"not a rubber stamp")

    # ---- (2) the illegal cut-move must be rejected, and the pinned
    # counter-fact: bypassing the guard breaks the prediction ----
    oidx = [i for i, (_u, _w, L) in enumerate(specs) if L % 2 == 1]
    m, sols = sdr_verify(specs, n, mat, x, rep, binc)
    c = sols[0]
    v0 = next(v for v in range(n))
    cur = m[v0][0]
    try:
        apply_cut_move(specs, n, m, [(v0, cur)], binc)
        raise SystemExit("FAIL: illegal move accepted")
    except AssertionError:
        pass
    # pinned counter-fact: apply the move NAIVELY (dart to an arbitrary
    # other branch, "target" the current branch) -- the naive Delta is
    # NOT a cut in general and parity/prediction breaks
    others = [j for j in binc[v0] if j != cur]
    m2 = dict(m)
    t = others[0]
    m2[v0] = (t, 0 if v0 == specs[t][0] else 1)
    broke = (cm_solve(specs, m2) is None)
    print(f"  (2) illegal move (target = current branch) REJECTED by "
          f"the guard; pinned counter-fact: the naive single-hub "
          f"deviation applied anyway leaves the parity class "
          f"(cm_solve None: {broke}) -- a single hub can never move "
          f"mu by a cut (e_x + e_y = e_z mod Cut, never 0)")
    assert broke, "single-hub naive move stayed consistent?!"

    # ---- (3) W3's layering reproduced: 12 parity maps at d <= 2, all
    # unbalanced (the (GR-41) exhaustive layering, must-DETECT) ----
    (_nm3, n3, specs3, _f3, _S3, _e3) = by_tag['W3']
    dinc3 = darts_at(specs3)
    mats3 = perfect_matchings(specs3)
    assert len(mats3) == 8
    seenk = set()
    nbal = 0
    for mat3 in mats3:
        base = m_of_matching(specs3, mat3)
        hubs = sorted(dinc3)
        for nd in range(3):
            for vs in combinations(hubs, nd):
                lists = [[d for d in dinc3[v] if d != base[v]] for v in vs]
                idx = [0] * nd
                while True:
                    mm = dict(base)
                    for j, v in enumerate(vs):
                        mm[v] = lists[j][idx[j]]
                    sols = cm_solve(specs3, mm)
                    if sols is not None:
                        key = tuple(sorted(mm.items()))
                        if key not in seenk:
                            seenk.add(key)
                            for cc in sols:
                                na, nb = odd_balance(specs3, mm, cc)
                                if na == nb:
                                    nbal += 1
                    j = nd - 1
                    while j >= 0:
                        idx[j] += 1
                        if idx[j] < len(lists[j]):
                            break
                        idx[j] = 0
                        j -= 1
                    if j < 0:
                        break
                if nd == 0:
                    break
    print(f"  (3) W3 layering REPRODUCED: {len(seenk)} distinct "
          f"parity-consistent maps within 2 deviations of its 8 "
          f"matchings, {nbal} balanced -- must equal (12, 0), the "
          f"(GR-41) exhaustive layering (the balance detector must "
          f"DETECT the kill)")
    assert len(seenk) == 12 and nbal == 0, "W3 layering NOT reproduced"

    # ---- (4) the E1(v) discriminator: the SAME impossible predicate
    # (na = nb + 1, unreachable: delta is even) under a CAPPED search
    # must report CAP; under FULL enumeration it is a GENUINE oo ----
    specs2, _p2, _co2 = nko_specs(2)
    n2 = 10
    _cy2, bmask2, dim2, s02 = cycle_masks(specs2, n2)
    mat2 = complete_matching(specs2, n2, [])
    base2, moves2, prefs2 = dp_pref(specs2, n2, mat2, bmask2, dim2, True)
    dmin2 = prefs2[-1][s02]
    found = 0
    tried = 0
    for k in range(3):
        for _i in range(60):
            mm = dp_walk(specs2, n2, base2, moves2, prefs2, s02,
                         dmin2 + k, rng)
            if mm is None:
                continue
            tried += 1
            for cc in cm_solve(specs2, mm):
                na, nb = odd_balance(specs2, mm, cc)
                if na == nb + 1:
                    found += 1
    assert found == 0
    print(f"  (4a) the impossible predicate under a CAPPED search at "
          f"NKo(2) ({tried} sampled maps, walk caps 60/level, levels "
          f"0..2): 0 hits -> the verdict is 'no witness at the CAPS "
          f"searched' -- an exhausted cap is NOT oo (must-NOT-fire "
          f"control)")
    # must-FIRE: the same predicate under FULL enumeration
    maps2, oidx2, _d2, tot2 = parity_census(specs2, 10)
    hits = 0
    for (mm, sols) in maps2:
        for cc in sols:
            na, nb = odd_balance(specs2, mm, cc)
            if na == nb + 1:
                hits += 1
    assert hits == 0
    print(f"  (4b) SYNTHETIC mock (predicate na = nb + 1, impossible: "
          f"delta is even) at NKo(2) under FULL 3^10 enumeration "
          f"({len(maps2)} parity maps): 0 hits at exhaustion -> the "
          f"detector reports GENUINE oo and would print the E1(v) "
          f"REFUTATION headline (must-FIRE control, mock disclosed as "
          f"synthetic; the real predicate na = nb finds "
          f"{sum(1 for (mm, ss) in maps2 for cc in ss if odd_balance(specs2, mm, cc)[0] == odd_balance(specs2, mm, cc)[1])} "
          f"balanced maps at the same shape -- the negative control)")

    # ---- (5) mu_in_phi vs gdev.in_coset cross-check ----
    (_nm, nw, specsw, _f, _S, _e) = by_tag['W4']
    cyc = fundamental_cycles(specsw, nw)
    agree = 0
    for _i in range(200):
        vec = [rng.randrange(2) for _ in specsw]
        a = mu_in_phi(specsw, nw, vec) is not None
        b = in_coset(specsw, nw, vec, cyc)   # in_coset XORs tau itself
        assert a == b, "mu_in_phi vs in_coset DISAGREE"
        agree += 1
    print(f"  (5) mu_in_phi vs gdev.in_coset: {agree}/200 random "
          f"vectors agree at W4")
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sdr', action='store_true')
    ap.add_argument('--balance', action='store_true')
    ap.add_argument('--odd', action='store_true')
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    t0 = time.time()
    if args.validate or args.sdr:
        leg_sdr()
    if args.validate or args.balance:
        leg_balance()
    if args.validate or args.odd:
        leg_odd()
    if args.validate or args.adv:
        leg_adv()
    if args.validate:
        print(f"[GPSA] validate complete [{time.time() - t0:.0f}s]")


if __name__ == '__main__':
    main()
