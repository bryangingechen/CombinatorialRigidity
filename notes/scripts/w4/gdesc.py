"""GDESC -- the fourteenth kernel-(K) direction: the entry-5 descent
lemma's STUCK CASE (spec: notes/Pencil-fanout-archive.md S"Fourteenth
direction").

PRIMARY: close the descent lemma's stuck case -- from every
parity-consistent (m, c) in which every majority-side odd branch is
dart-blocked, some legal (GR-45) move strictly reduces the imbalance
|imb| (written |delta| in the workbook; this driver writes `imb` for
the imbalance THROUGHOUT and reserves `cut`/`delta_of` for cut vectors,
per the prep's notation warning).  The driver supports the proof
attempt (theorem-first); its two structural theorems are certified
sentence-by-sentence (README S4 convention 4):

  (GR-46) ONE-MOVE TRANSITIVITY of the (GR-45) calculus: for ANY two
  parity-consistent minority maps m, m', the move set
  R = {v : m(v) != m'(v)} with targets x_v = the third branch at v
  (!= branch(m(v)), != branch(m'(v))) is LEGAL -- by the star relation
  e_{x_v} = cut({v}) + e_{cur} + e_{new}, so
  sum e_{x_v} = cut(R) + (mu(m) + mu(m')) which is a cut since both mu
  lie in tau + Cut -- and applying it carries m to m'.  Consequence:
  the descent lemma over the FULL legal family is EQUIVALENT to
  entry 5's balance half (a reducing move exists iff a smaller-|imb|
  parity-consistent map exists), and a configuration defeating EVERY
  legal move exists iff d_adm = oo at the shape (E1 clause (v)); the
  Step-G62(ii) demotion event is meaningful only for a RESTRICTED
  catalogue ({T1, T2}-local).

  (GR-47) NORMAL FORM: parity-consistent maps m correspond exactly to
  triples (X, phi, T) -- X = supp(mu(m)) a coset representative
  (chi_X in Phi = tau + Cut), phi an injective end-selection of X (the
  dart-holding end per X-branch), T = {branches holding BOTH end
  darts} a perfect matching of V minus phi(X) avoiding X -- with the
  exact pattern formula: for odd gamma, pattern(gamma) =
  c(u) xor [gamma in T, or gamma in X selected at u].

The stuck-case escape catalogue this pass states and asserts per
configuration (F11: each case names the mode that certifies it):
  (K1) T2 at a dart-on end v of a majority branch (m(v) ON gamma);
  (K2) T2 at a dart-off end v of a majority branch;
  (K3) the PAIR-STAR extension at a DOUBLY-blocked majority branch
       gamma (both end darts on gamma, so T2 at both its ends is
       provably illegal): S = ends(gamma), targets = the cut
       cut(S) branches, each repped by one of its own ends with dart
       off it, reps distinct -- legal since the target sum IS cut(S),
       and it flips {gamma} plus the odd non-hub-repped side branches.
Reduction criterion (exact, from (GR-45)(ii) mod the global swap):
a move with net majority flip t reduces |imb| iff 1 <= t <= |imb| - 1
(t = |imb| lands at -|imb|: NOT a reduction).

SECONDARY (b'): d_adm - d_par <= 2; its named unmeasured half --
|imb| at parity-OPTIMAL maps -- is measured exactly per censused
shape (--opt), together with exact per-shape d_par / d_adm / gap from
the full-3^n census (a fresh subsample at this driver's own seeds,
disclosed; W3/NKo2v pinned against the landed record).

Modes:
  --stuck    (GR-46) transitivity certified at random parity-map pairs
             per censused shape + an n = 30 scaled demo; (GR-47)
             normal-form round-trip at EVERY censused parity map; the
             stuck census rebuilt with blocking profiles ((1,)/(1,1)/
             (2,)/... = per-majority-branch end-dart counts) and the
             all-doubly-blocked discriminator; the large-shape stuck
             hunt at NKp(6)/NK55(6) (dp_walk samples, caps disclosed).
  --cases    the case analysis's own asserts: per stuck config, which
             of K1/K2/K3 fires, each constructed move applied and its
             |imb| reduction asserted; the {T1,T2}-family full scan
             (rescue coverage, must re-derive GPSA's 148/148); any
             config where {T1,T2} AND the K3 extension all fail is a
             LOCAL-DEMOTION candidate (expected 0; a find is reported,
             not a refutation of entry 5 -- (GR-46) Corollary 2).
  --opt      |imb| at parity-optimal maps ((b')'s named unmeasured
             half) + exact d_par/d_adm/gap per censused shape; the
             mechanism comparison gap <= min-|imb|-at-optimum reported
             (a reading, not asserted); NKo2v cross-checked against
             min_dev and the landed (2, 2); W3 against (2, 3).
  --adv      falsification controls (F13, each with a must-reject or
             must-fire witness): a doctored non-reducing "escape" is
             REJECTED by verify_escape; the local-demotion
             discriminator FIRES on a T1-only-restricted scan of a
             real stuck config (synthetic restriction, disclosed) and
             does NOT fire on the full scan (negative control); a
             doctored transitivity move set with a non-cut target sum
             is REJECTED; the E1(v) discriminator (CAP vs genuine-oo
             at full enumeration, mock disclosed) carried forward.
  --validate all four, in the order above.

Rank-free throughout: the target is entry 5's balance half, a pure
(G0, l) statement; gexist.fully_good_rank is never imported or called
(a call would be a scope flag onto entry 1).  Exact integers over
GF(2) throughout; rngs seeded per mode, seeds printed; no `set`
printed; nothing samples a placement (S(K-clos) (AC-9)).  Wall-clock
[Ns] annotations are inherently non-deterministic; every other byte is
seed-stable.  No pool is new: the census legs subsample gcap.pool_specs
behind the cflank.cubic_habitat gate at this driver's own seeds (fresh
subsamples, disclosed); NKp(6)/NK55(6)/NKo2v are GPSA's commissioned
constructions, reused read-only.
"""
import argparse
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from gridcol import subdivide                                          # noqa: E402
from cflank import cubic_habitat                                       # noqa: E402
from gcap import pool_specs                                            # noqa: E402
from gunif import WITNESSES                                            # noqa: E402
from gorient import (cm_solve, odd_balance, perfect_matchings,         # noqa: E402
                     m_of_matching, prep_shape)
from gdev import (min_dev, habitat_by_lemma)                           # noqa: E402
from gadm import (cycle_masks, dp_pref, dp_walk, mu_in_phi,            # noqa: E402
                  complete_matching)
from gpsa import (branches_at, is_bridgeless, delta_of,                # noqa: E402
                  parity_census, pattern_of, apply_cut_move, cut_side,
                  t1_move, all_moves, nkp_specs, nk55_specs,
                  nko2v_specs)

# `imb_of` MOVED DOWN to `gridbal_common` on 2026-08-25 (README *Harness
# debt*, direction GFLIP): `gflip` imports it, past §2 rule 2's trigger,
# alongside ten sibling devices from `balb`/`gbal`/`gflow`/`gpsa`.
# Re-exported here, so this module's own modes and `balb`'s/`gflow`'s
# import lines are unchanged.  `majority_of` joined it 2026-08-25 (README
# *Harness debt*, directions GCHEAP/GPRICE): `gcheap`/`gflow` both already
# pull it, past the trigger again; re-exported here for the same reason.
from gridbal_common import imb_of, majority_of                         # noqa: E402

R_SEED = 20260818


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive (checked against the README index
# and the Divergences table).  `imb_of`/`majority_of` read the imbalance
# off a pattern (both moved to `gridbal_common` 2026-08-25, used here via
# the re-export above); `transit_move` is the (GR-46) construction;
# `normal_form`/`rebuild_nf` the (GR-47) bijection; `t2_at`/
# `ts_pair_moves` the per-hub T2 family and its K3 pair-star extension;
# `rescue_scan`/`verify_escape` the escape search and its adversarial
# verifier; `census_layers` the exact per-shape d_par/d_adm/|imb|-at-
# optimum computation off the full census.


def block_ends(specs, m, i):
    """The ends of branch i whose dart sits ON i (the blocking darts)."""
    (u, w, _L) = specs[i]
    return [v for v in (u, w) if m[v][0] == i]


def targets_cut(specs, n, moveset):
    """The GF(2) sum of the move set's TARGET branches; returns the cut
    side (None iff not a cut -- the (GR-45) legality test this driver
    must run itself, since apply_cut_move checks only the per-hub
    guards)."""
    vec = [0] * len(specs)
    for (_v, x) in moveset:
        vec[x] ^= 1
    return cut_side(specs, n, vec)


def move_imb(specs, n, m, moveset, binc, oidx, k2):
    """Apply a legal move set and return (|imb'| , m').  Asserts the
    target sum is a cut (legality) and the result parity-consistent."""
    assert targets_cut(specs, n, moveset) is not None, \
        "ILLEGAL move set: target sum not a cut"
    m2, _dl = apply_cut_move(specs, n, m, moveset, binc)
    s2 = cm_solve(specs, m2)
    assert s2 is not None, "(GR-45) broken: legal move left parity"
    p2 = pattern_of(specs, m2, s2[0], oidx)
    return abs(imb_of(k2, p2)), m2


def transit_move(specs, m, m2, binc):
    """The (GR-46) construction: the one legal move set carrying m to
    m2 (both parity-consistent): hubs R = {v : m(v) != m2(v)}, target
    at v = the third branch (!= cur, != new)."""
    ms = []
    for v in sorted(m):
        if m[v] == m2[v]:
            continue
        cur, new = m[v][0], m2[v][0]
        assert cur != new
        x = [j for j in binc[v] if j != cur and j != new]
        assert len(x) == 1, "hub star not 3 distinct branches"
        ms.append((v, x[0]))
    return ms


def normal_form(specs, n, m):
    """The (GR-47) decomposition of a parity-consistent map:
    X = {branches with exactly one end dart} (a coset representative of
    [tau]), phi = its injective end-selection, T = {branches with both
    end darts} (a perfect matching of V minus phi(X), avoiding X).
    Every clause asserted."""
    cnt = [0] * len(specs)
    for v in sorted(m):
        cnt[m[v][0]] += 1
    X = [i for i, c in enumerate(cnt) if c == 1]
    T = [i for i, c in enumerate(cnt) if c == 2]
    assert all(c <= 2 for c in cnt)
    phi = {}
    for i in X:
        (u, w, _L) = specs[i]
        ends = [v for v in (u, w) if m[v][0] == i]
        assert len(ends) == 1
        phi[i] = ends[0]
    sel = sorted(phi.values())
    assert len(sel) == len(set(sel)), "phi not injective"
    tends = sorted(v for i in T for v in specs[i][:2])
    assert len(tends) == len(set(tends)), "T not a matching"
    assert sorted(sel + tends) == list(range(n)), \
        "V != phi(X) disjoint-union V(T)"
    assert not (set(X) & set(T))
    chi = [1 if i in set(X) else 0 for i in range(len(specs))]
    assert mu_in_phi(specs, n, chi) is not None, \
        "(GR-47) broken: X not a coset representative of [tau]"
    return X, phi, T


def rebuild_nf(specs, n, X, phi, T):
    """Inverse of normal_form."""
    m = {}
    for i in X:
        v = phi[i]
        m[v] = (i, 0 if v == specs[i][0] else 1)
    for i in T:
        (u, w, _L) = specs[i]
        m[u] = (i, 0)
        m[w] = (i, 1)
    assert sorted(m) == list(range(n))
    return m


def t2_at(specs, m, binc, u):
    """Every legal T2 move set at hub u (targets = star(u); each branch
    repped by u or its far end, dart off target, reps distinct)."""
    star = binc[u]
    cands = []
    for i in star:
        (a, b, _L) = specs[i]
        far = b if a == u else a
        cs = [r for r in (u, far) if m[r][0] != i]
        cands.append([(r, i) for r in cs])
    out = []
    for c0 in cands[0]:
        for c1 in cands[1]:
            for c2 in cands[2]:
                ms = [c0, c1, c2]
                if len({v for (v, _x) in ms}) == 3:
                    out.append(ms)
    return out


def ts_pair_moves(specs, n, m, binc, u, w):
    """The K3 pair-star extension at S = {u, w}: targets = the branches
    of the cut cut(S), each repped by one of its OWN ends with dart off
    it, reps distinct.  Target sum = cut(S) by construction (legal);
    NOT a member of the {T1, T2} family in general."""
    S = {u, w}
    targets = [i for i, b in enumerate(delta_of(specs, S)) if b]
    if not targets:
        return []
    cands = []
    for i in targets:
        (a, b2, _L) = specs[i]
        cs = [r for r in (a, b2) if m[r][0] != i]
        if not cs:
            return []
        cands.append([(r, i) for r in cs])
    out = []

    def rec(j, used, acc):
        if j == len(cands):
            out.append(list(acc))
            return
        for (r, i) in cands[j]:
            if r not in used:
                used.add(r)
                acc.append((r, i))
                rec(j + 1, used, acc)
                acc.pop()
                used.discard(r)

    rec(0, set(), [])
    return out


def rescue_scan(specs, n, m, binc, oidx, k2, d0, family):
    """All |imb|-reducing move sets from `family` (a list of move
    sets); returns [(new |imb|, moveset)] sorted by new |imb|."""
    out = []
    for ms in family:
        d2, _m2 = move_imb(specs, n, m, ms, binc, oidx, k2)
        if d2 < d0:
            out.append((d2, ms))
    return sorted(out, key=lambda t: (t[0], t[1]))


def verify_escape(specs, n, m, binc, oidx, k2, d0, moveset):
    """The adversarial escape verifier: accepts a move set ONLY if it
    is legal AND strictly reduces |imb| (F13 guard; raises on a
    doctored escape)."""
    d2, m2 = move_imb(specs, n, m, moveset, binc, oidx, k2)
    assert d2 < d0, \
        f"DOCTORED escape: |imb| {d0} -> {d2} is not a strict reduction"
    return d2, m2


def stuck_configs(specs, n, maps, oidx, k2):
    """(m, sols, p, imb) for every stuck configuration in the census:
    imb != 0 and NO majority-side odd branch has a free T1.  One entry
    per (map, c-solution); the global swap pairs them off, so profiles
    are counted per (map, c)."""
    out = []
    for (mm, sols) in maps:
        for c in sols:
            p = pattern_of(specs, mm, c, oidx)
            d = imb_of(k2, p)
            if d == 0:
                continue
            maj = majority_of(oidx, p, d)
            if any(t1_move(specs, mm, i) is not None for i in maj):
                continue
            out.append((mm, c, p, d))
    return out


def census_layers(specs, n, maps, oidx, k2, mats):
    """Exact per-shape layers off the full census: d_par(shape),
    d_adm(shape), the balance gap, and min |imb| over the
    parity-OPTIMAL maps ((b')'s named unmeasured half)."""
    bases = [m_of_matching(specs, mat) for mat in mats]
    d_par = d_adm = None
    opt_imbs = []
    for (mm, sols) in maps:
        dist = min(sum(1 for v in mm if mm[v] != b[v]) for b in bases)
        imbs = [abs(imb_of(k2, pattern_of(specs, mm, c, oidx)))
                for c in sols]
        bal = (0 in imbs)
        if d_par is None or dist < d_par:
            d_par = dist
            opt_imbs = []
        if dist == d_par:
            opt_imbs.append(min(imbs))
        if bal and (d_adm is None or dist < d_adm):
            d_adm = dist
    return d_par, d_adm, (None if d_adm is None else d_adm - d_par), \
        (min(opt_imbs) if opt_imbs else None)


def census_cases(rng, rate, with_nko2v=True):
    """The censused shape list: a fresh pool subsample at this driver's
    own seed (disclosed) + W3M + W3 + NKo2v (the stuck-census bed)."""
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    cases = []
    picked = 0
    for n, specs in pool_specs():
        if rng.random() >= rate:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        picked += 1
        cases.append((f"pool#{picked}", n, [tuple(s) for s in specs]))
    for tag in ('W3M', 'W3'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        cases.append((tag, n, specs))
    if with_nko2v:
        specs, _pent = nko2v_specs()
        cases.append(('NKo2v', 10, specs))
    return cases, picked


# ------------------------------------------------- [GDS-1] --stuck ----------

def leg_stuck():
    """[GDS-1] (GR-46) transitivity + (GR-47) normal form certified;
    the stuck census with blocking profiles; the large-shape hunt."""
    t0 = time.time()
    print(f"[GDS-1] transitivity, normal form, the stuck census "
          f"(seed {R_SEED + 11})")
    rng = random.Random(R_SEED + 11)
    cases, picked = census_cases(rng, 0.02)

    # ---- (a) (GR-46) + (GR-47), certified per shape ----
    tr_ok = nf_ok = 0
    shapes = 0
    for (tag, n, specs) in cases:
        binc = branches_at(specs, n)
        assert is_bridgeless(specs, n)
        maps, oidx, dim, total = parity_census(specs, n)
        k2 = len(oidx)
        shapes += 1
        # (GR-47): round-trip EVERY censused parity map + pattern law
        for (mm, sols) in maps:
            X, phi, T = normal_form(specs, n, mm)
            assert rebuild_nf(specs, n, X, phi, T) == mm
            c = sols[0]
            Xs, Ts = set(X), set(T)
            for j, i in enumerate(oidx):
                u = specs[i][0]
                pred = c[u] ^ (1 if (i in Ts or (i in Xs and phi[i] == u))
                               else 0)
                assert pred == ((pattern_of(specs, mm, c, oidx) >> j) & 1), \
                    "(GR-47) pattern formula broken"
            nf_ok += 1
        # (GR-46): random parity-map pairs, the transit move certified
        for _i in range(min(8, len(maps))):
            (m1, s1) = maps[rng.randrange(len(maps))]
            (m2, _s2) = maps[rng.randrange(len(maps))]
            ms = transit_move(specs, m1, m2, binc)
            if not ms:
                continue
            S = targets_cut(specs, n, ms)
            assert S is not None, \
                "(GR-46) BROKEN: transit target sum not a cut"
            m3, dl = apply_cut_move(specs, n, m1, ms, binc)
            assert m3 == m2, "(GR-46) BROKEN: transit move misses m2"
            Sd = cut_side(specs, n, dl)
            assert Sd is not None
            c1 = s1[0]
            cpred = {v: c1[v] ^ (1 if v in Sd else 0) for v in c1}
            assert cpred in cm_solve(specs, m2), \
                "(GR-46) c' = c + chi law broken"
            tr_ok += 1
    print(f"  (GR-47) normal form round-tripped at {nf_ok} parity maps "
          f"over {shapes} shapes ({picked} sampled pool habitat shapes "
          f"at rate 0.02 + W3M + W3 + NKo2v): X a coset rep of [tau], "
          f"phi injective, T a perfect matching of the complement "
          f"avoiding X, and the pattern formula exact at every odd "
          f"branch")
    print(f"  (GR-46) one-move transitivity certified at {tr_ok} random "
          f"parity-map pairs: the transit move set is LEGAL (distinct "
          f"hubs, darts off targets, target sum a cut) and carries m to "
          f"m' with the c' = c + chi law -- EVERY parity-consistent map "
          f"is ONE legal (GR-45) move from every other")

    # ---- (b) the n = 30 scaled transitivity demo ----
    specs, _p = nkp_specs(6)
    n = 30
    binc = branches_at(specs, n)
    ok, why = habitat_by_lemma(n, [(u, w) for (u, w, _L) in specs],
                               [L for (_u, _w, L) in specs])
    assert ok, f"NKp(6) not habitat: {why}"
    _cy, bmask, dim, s0 = cycle_masks(specs, n)
    mat = complete_matching(specs, n, [])
    base, moves, prefs = dp_pref(specs, n, mat, bmask, dim, True)
    dmin = prefs[-1][s0]
    got = []
    while len(got) < 2:
        mm = dp_walk(specs, n, base, moves, prefs, s0, dmin + 2, rng)
        if mm is not None and cm_solve(specs, mm) is not None:
            got.append(mm)
    ms = transit_move(specs, got[0], got[1], binc)
    assert targets_cut(specs, n, ms) is not None
    m3, _dl = apply_cut_move(specs, n, got[0], ms, binc)
    assert m3 == got[1]
    print(f"  n = 30 demo (NKp(6)): two dp_walk parity maps differing "
          f"at {len(ms)} hubs joined by ONE legal move (target sum a "
          f"cut, guards live) -- transitivity is not a small-n artifact")

    # ---- (c) the stuck census with blocking profiles ----
    prof_hist = {}
    all_double = 0
    stuck_tot = 0
    per_shape = []
    for (tag, n, specs) in cases:
        binc = branches_at(specs, n)
        maps, oidx, dim, total = parity_census(specs, n)
        k2 = len(oidx)
        if k2 == 0:
            continue
        sc = stuck_configs(specs, n, maps, oidx, k2)
        if not sc:
            continue
        per_shape.append((tag, len(sc), len(maps)))
        for (mm, c, p, d) in sc:
            stuck_tot += 1
            maj = majority_of(oidx, p, d)
            prof = tuple(sorted(len(block_ends(specs, mm, i))
                                for i in maj))
            key = (abs(d), prof)
            prof_hist[key] = prof_hist.get(key, 0) + 1
            if all(len(block_ends(specs, mm, i)) == 2 for i in maj):
                all_double += 1
    print(f"  stuck census ({stuck_tot} stuck (map, c) configs; "
          f"per shape: {per_shape}): blocking profiles "
          f"(|imb|, per-majority-branch end-dart counts) -> count: "
          f"{sorted(prof_hist.items())}")
    print(f"  ALL-DOUBLY-BLOCKED configs (every majority branch holds "
          f"BOTH end darts -- the profile that provably kills T2 at "
          f"every majority end AND every majority T1): {all_double} "
          f"-- the K3 pair-star extension is the named escape there")

    # ---- (d) the large-shape stuck hunt (caps disclosed) ----
    for (tag, sp) in (('NKp(6)', nkp_specs(6)[0]),
                      ('NK55(6)', nk55_specs(6)[0])):
        n = 30
        binc = branches_at(sp, n)
        oidx = [i for i, (_u, _w, L) in enumerate(sp) if L % 2 == 1]
        k2 = len(oidx)
        _cy, bmask, dim, s0 = cycle_masks(sp, n)
        mat = complete_matching(sp, n, [])
        base, moves, prefs = dp_pref(sp, n, mat, bmask, dim, True)
        dmin = prefs[-1][s0]
        found = 0
        checked = 0
        resc = 0
        hard = []
        prof_h = {}
        for j in range(5):
            for _i in range(120):
                mm = dp_walk(sp, n, base, moves, prefs, s0, dmin + j, rng)
                if mm is None:
                    continue
                sols = cm_solve(sp, mm)
                assert sols is not None
                checked += 1
                for c in sols:
                    p = pattern_of(sp, mm, c, oidx)
                    d = imb_of(k2, p)
                    if d == 0:
                        continue
                    maj = majority_of(oidx, p, d)
                    if any(t1_move(sp, mm, i) is not None for i in maj):
                        continue
                    found += 1
                    prof = tuple(sorted(len(block_ends(sp, mm, i))
                                        for i in maj))
                    prof_h[(abs(d), prof)] = \
                        prof_h.get((abs(d), prof), 0) + 1
                    fam = all_moves(sp, n, mm, binc)
                    if rescue_scan(sp, n, mm, binc, oidx, k2,
                                   abs(d), fam):
                        resc += 1
                    else:
                        hard.append((dict(mm), dict(c), p, d))
        print(f"  {tag} (n = 30) stuck hunt: {found} stuck (map, c) "
              f"configs among {checked} dp_walk samples (budgets "
              f"d_par..d_par+4, 120 walks/level -- a CAPPED sample, "
              f"not a census); profiles {sorted(prof_h.items())}; "
              f"{resc} rescued by a single {{T1, T2}} move"
              + ("" if found == 0 else f"; unrescued: {found - resc}"))
        # -- analyze any {T1, T2}-unrescued config: the K3 pair-star at
        # majority ends, then the FULL 2-hub pair-star family --
        for (mm, c, p, d) in hard:
            d0 = abs(d)
            maj = majority_of(oidx, p, d)
            prof = tuple(sorted(len(block_ends(sp, mm, i)) for i in maj))
            star_o = {i: sorted(set(sp[i][:2])
                                & {v for x in maj for v in sp[x][:2]})
                      for i in maj}
            k3 = []
            for i in maj:
                (u, w, _L) = sp[i]
                for msx in ts_pair_moves(sp, n, mm, binc, u, w):
                    d2, _m2 = move_imb(sp, n, mm, msx, binc, oidx, k2)
                    if d2 < d0:
                        k3.append((d2, i))
                        break
            wide = 0
            if not k3:
                for va in range(n):
                    for vb in range(va + 1, n):
                        for msx in ts_pair_moves(sp, n, mm, binc,
                                                 va, vb):
                            d2, _m2 = move_imb(sp, n, mm, msx, binc,
                                               oidx, k2)
                            if d2 < d0:
                                wide += 1
                                break
                        if wide:
                            break
                    if wide:
                        break
            print(f"    {{T1, T2}}-UNRESCUED stuck config at {tag} "
                  f"(|imb| = {d0}, blocking profile {prof}, majority "
                  f"branches {sorted(maj)}, shared majority end hubs "
                  f"{sorted((i, star_o[i]) for i in maj)}): K3 "
                  f"pair-star at majority ends rescues: "
                  f"{sorted(k3) if k3 else 'NO'}"
                  + ("" if k3 else f"; SOME 2-hub pair-star rescues: "
                                   f"{'YES' if wide else 'NO'} -- a "
                                   f"LOCAL-demotion witness for the "
                                   f"{{T1, T2}} catalogue either way "
                                   f"((GR-46) Cor. 2: entry 5 itself "
                                   f"is untouched)"))
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GDS-2] --cases ----------

def leg_cases():
    """[GDS-2] the case analysis's asserts: K1/K2/K3 per stuck config;
    the {T1,T2} rescue coverage re-derived; local-demotion candidates."""
    t0 = time.time()
    print(f"[GDS-2] the stuck-case catalogue (seed {R_SEED + 12})")
    rng = random.Random(R_SEED + 12)
    cases, picked = census_cases(rng, 0.02)

    tag_hist = {}
    resc_tt = 0
    resc_k3only = 0
    unresc = 0
    stuck_tot = 0
    red_hist = {}
    for (tag, n, specs) in cases:
        binc = branches_at(specs, n)
        maps, oidx, dim, total = parity_census(specs, n)
        k2 = len(oidx)
        if k2 == 0:
            continue
        for (mm, c, p, d) in stuck_configs(specs, n, maps, oidx, k2):
            stuck_tot += 1
            d0 = abs(d)
            maj = majority_of(oidx, p, d)
            # -- the {T1, T2} family scan (GPSA's rescue re-derived) --
            fam = all_moves(specs, n, mm, binc)
            tt = rescue_scan(specs, n, mm, binc, oidx, k2, d0, fam)
            # -- the catalogue: K1 / K2 at majority ends, K3 pair-star --
            fired = []
            for i in maj:
                (u, w, _L) = specs[i]
                blocked = block_ends(specs, mm, i)
                for v in (u, w):
                    for ms in t2_at(specs, mm, binc, v):
                        d2, _m2 = move_imb(specs, n, mm, ms, binc,
                                           oidx, k2)
                        if d2 < d0:
                            fired.append('K1' if v in blocked else 'K2')
                if len(blocked) == 2:
                    # THEOREM check: a doubly-blocked branch has an
                    # empty rep set, so NO legal T2 exists at either
                    # of its ends (K3's raison d'etre).
                    assert t2_illegal_at_double(specs, mm, binc, i)
                    for ms in ts_pair_moves(specs, n, mm, binc, u, w):
                        d2, _m2 = move_imb(specs, n, mm, ms, binc,
                                           oidx, k2)
                        if d2 < d0:
                            fired.append('K3')
            fired = sorted(set(fired))
            key = (abs(d), tuple(fired) if fired else ('NONE',))
            tag_hist[key] = tag_hist.get(key, 0) + 1
            if tt:
                resc_tt += 1
                red_hist[(d0, tt[0][0])] = \
                    red_hist.get((d0, tt[0][0]), 0) + 1
            elif 'K3' in fired:
                resc_k3only += 1
            else:
                unresc += 1
                print(f"  *** LOCAL-DEMOTION candidate at {tag}: a "
                      f"stuck config (|imb| = {d0}) with NO reducing "
                      f"{{T1, T2}} move and NO reducing K3 pair-star "
                      f"-- by (GR-46) Corollary 1 a wider reducing "
                      f"move still exists iff a smaller-|imb| map "
                      f"exists at this shape (it does: the census is "
                      f"balanced); the LOCAL catalogue is what failed")
    print(f"  case coverage over {stuck_tot} stuck configs: "
          f"(|imb|, fired cases) -> count: {sorted(tag_hist.items())}")
    print(f"  rescue coverage: {resc_tt}/{stuck_tot} rescued by a "
          f"single {{T1, T2}} move (GPSA's census re-derived), "
          f"{resc_k3only} rescued ONLY by the K3 pair-star extension, "
          f"{unresc} by neither (local-demotion candidates)")
    print(f"  best single-move reduction (|imb| before, after) -> "
          f"count: {sorted(red_hist.items())}")
    assert unresc == 0, \
        "local catalogue INCOMPLETE at a censused shape (reported above)"
    print(f"  [{time.time() - t0:.0f}s]")


def t2_illegal_at_double(specs, m, binc, i):
    """THEOREM check (K3's hypothesis): if branch i holds BOTH end
    darts, i's rep set is empty (neither end's dart is off i), so no
    legal T2 exists at either end of i."""
    (u, w, _L) = specs[i]
    assert m[u][0] == i and m[w][0] == i
    return (t2_at(specs, m, binc, u) == []
            and t2_at(specs, m, binc, w) == [])


# ------------------------------------------------- [GDS-3] --opt ------------

def leg_opt():
    """[GDS-3] (b')'s named unmeasured half: |imb| at parity-OPTIMAL
    maps, exact per censused shape, + exact d_par/d_adm/gap."""
    t0 = time.time()
    print(f"[GDS-3] |imb| at parity-optimal maps -- (b')'s unmeasured "
          f"half (seed {R_SEED + 13})")
    rng = random.Random(R_SEED + 13)
    cases, picked = census_cases(rng, 0.02)

    gap_hist = {}
    opt_hist = {}
    mech_viol = 0
    nshapes = 0
    pinned = {}
    for (tag, n, specs) in cases:
        maps, oidx, dim, total = parity_census(specs, n)
        k2 = len(oidx)
        if k2 == 0:
            continue
        mats = perfect_matchings(specs, cap=500)
        d_par, d_adm, gap, opt_imb = census_layers(specs, n, maps, oidx,
                                                   k2, mats)
        assert d_adm is not None, \
            "entry 5 refuted at a censused shape (E1(v) HEADLINE)"
        nshapes += 1
        gap_hist[gap] = gap_hist.get(gap, 0) + 1
        opt_hist[opt_imb] = opt_hist.get(opt_imb, 0) + 1
        if gap > opt_imb:
            mech_viol += 1
        if gap > 2:
            print(f"  *** BALANCE GAP {gap} > 2 at {tag} -- (b') "
                  f"REFUTED; HEADLINE")
        assert gap <= 2
        if tag in ('W3', 'W3M', 'NKo2v'):
            pinned[tag] = (d_par, d_adm, gap, opt_imb)
    print(f"  exact layers at {nshapes} odd-carrying censused shapes "
          f"({picked} sampled pool habitat shapes at rate 0.02 + W3M + "
          f"W3 + NKo2v), all matchings (cap 500), full census "
          f"distances:")
    print(f"    balance gap d_adm - d_par -> count: "
          f"{sorted(gap_hist.items())}")
    print(f"    min |imb| over parity-OPTIMAL maps -> count: "
          f"{sorted(opt_hist.items())} -- (b')'s named unmeasured "
          f"half, now measured: the decomposition needs <= 2 at every "
          f"shape")
    print(f"    mechanism reading (gap <= min-|imb|-at-optimum, one T1 "
          f"unit = 2 movements per 2 imbalance): violations "
          f"{mech_viol}/{nshapes} (reported, not asserted -- the "
          f"repair chain's availability at the optimum is exactly the "
          f"stuck-case question)")
    # pins against the landed record
    assert pinned['W3'][:3] == (2, 3, 1), \
        f"W3 layers moved: {pinned['W3']} != (2, 3, 1) -- landed record"
    assert pinned['NKo2v'][:3] == (2, 2, 0), \
        f"NKo2v layers moved: {pinned['NKo2v']}"
    print(f"    pins: W3 (d_par, d_adm, gap, opt-|imb|) = "
          f"{pinned['W3']} (landed: 2, 3, 1); W3M = {pinned['W3M']}; "
          f"NKo2v = {pinned['NKo2v']} (landed: 2, 2, 0)")
    # NKo2v cross-check against the owner's exact min_dev
    specs, _pent = nko2v_specs()
    n = 10
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    _e, _a, hm, _inc, _tec, tec_cf, _ak = prep_shape(specs)
    mats = perfect_matchings(specs)
    d_par_md, d_adm_md, _dfg = min_dev(specs, edges, allverts, hm,
                                       tec_cf, hm['lens'], mats, 4)
    assert (d_par_md, d_adm_md) == pinned['NKo2v'][:2], \
        "census-derived layers DISAGREE with min_dev at NKo2v"
    print(f"    NKo2v cross-check: census-derived (d_par, d_adm) = "
          f"min_dev's ({d_par_md}, {d_adm_md}) -- the distance "
          f"computation is not a new oracle")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GDS-4] --adv ------------

def leg_adv():
    """[GDS-4] falsification controls (F13), each with a must-reject
    or must-fire witness and a negative control."""
    t0 = time.time()
    print(f"[GDS-4] falsification controls (seed {R_SEED + 14})")
    rng = random.Random(R_SEED + 14)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    # ---- (1) doctored escape must-reject ----
    (_nm, n, specs, _f, _S, _e) = by_tag['W3M']
    binc = branches_at(specs, n)
    maps, oidx, dim, total = parity_census(specs, n)
    k2 = len(oidx)
    sc = stuck_configs(specs, n, maps, oidx, k2)
    assert sc, "W3M lost its stuck configs?!"
    (mm, c, p, d) = sc[0]
    d0 = abs(d)
    fam = all_moves(specs, n, mm, binc)
    good = rescue_scan(specs, n, mm, binc, oidx, k2, d0, fam)
    assert good, "W3M stuck config not rescued?!"
    _d2, _m2 = verify_escape(specs, n, mm, binc, oidx, k2, d0,
                             good[0][1])   # negative control: passes
    bad = None
    for ms in fam:
        d2, _m2 = move_imb(specs, n, mm, ms, binc, oidx, k2)
        if d2 >= d0:
            bad = ms
            break
    assert bad is not None
    try:
        verify_escape(specs, n, mm, binc, oidx, k2, d0, bad)
        raise SystemExit("FAIL: doctored escape accepted")
    except AssertionError as ex:
        print(f"  (1) doctored escape (a legal move that does NOT "
              f"reduce |imb|) REJECTED ('{ex}'); the true rescue "
              f"passes (negative control)")

    # ---- (2) the local-demotion discriminator must-fire ----
    # synthetic restriction, disclosed: the T1-only family on a REAL
    # stuck config finds nothing (stuck = no majority free T1; minority
    # or even T1s never reduce), so the discriminator FIRES; the full
    # {T1, T2} scan on the same config does not (negative control).
    t1fam = [ms for z in range(len(specs))
             for ms in [t1_move(specs, mm, z)] if ms is not None]
    r1 = rescue_scan(specs, n, mm, binc, oidx, k2, d0, t1fam)
    assert not r1
    print(f"  (2) local-demotion discriminator: FIRES on the T1-only "
          f"restricted scan of a real W3M stuck config (0 reducers "
          f"among {len(t1fam)} legal T1s -- synthetic family "
          f"restriction, disclosed), and does NOT fire on the full "
          f"{{T1, T2}} scan ({len(good)} reducers -- negative "
          f"control); a genuine find would be a LOCAL demotion "
          f"witness, not an entry-5 refutation ((GR-46) Cor. 2)")

    # ---- (3) doctored transitivity move set must-reject ----
    (m1, _s1) = maps[rng.randrange(len(maps))]
    m2 = None
    for (mmx, _sx) in maps:
        if mmx != m1:
            m2 = mmx
            break
    ms = transit_move(specs, m1, m2, binc)
    assert targets_cut(specs, n, ms) is not None   # negative control
    doct = None
    for pos in range(len(ms)):
        (v0, x0) = ms[pos]
        for j in binc[v0]:
            if j == x0 or j == m1[v0][0]:
                continue
            cand = ms[:pos] + [(v0, j)] + ms[pos + 1:]
            if targets_cut(specs, n, cand) is None:
                doct = cand
                break
        if doct is not None:
            break
    assert doct is not None, \
        "no doctorable position: every single-target swap stayed a cut"
    print(f"  (3) doctored transitivity move set (one target swapped "
          f"to the hub's third branch) REJECTED: target sum is NOT a "
          f"cut (cut_side None); the undoctored set passes (negative "
          f"control) -- (GR-46)'s legality clause is load-bearing, "
          f"not decorative")

    # ---- (4) the E1(v) discriminator, carried forward ----
    # capped search at NKp(6) (impossible predicate na = nb + 1 -- the
    # imbalance is even): must report a CAP, never oo
    sp, _p = nkp_specs(6)
    n30 = 30
    _cy, bmask, dim30, s0 = cycle_masks(sp, n30)
    mat = complete_matching(sp, n30, [])
    base, moves, prefs = dp_pref(sp, n30, mat, bmask, dim30, True)
    dmin = prefs[-1][s0]
    tried = hits = 0
    for k in range(3):
        for _i in range(60):
            mx = dp_walk(sp, n30, base, moves, prefs, s0, dmin + k, rng)
            if mx is None:
                continue
            tried += 1
            for cc in cm_solve(sp, mx):
                na, nb = odd_balance(sp, mx, cc)
                if na == nb + 1:
                    hits += 1
    assert hits == 0
    print(f"  (4a) impossible predicate (na = nb + 1; the imbalance is "
          f"even) under a CAPPED search at NKp(6) ({tried} sampled "
          f"maps, 60 walks/level, levels 0..2): 0 hits -> 'no witness "
          f"at the CAPS searched' -- an exhausted cap is NOT oo")
    sp2, _pent = nko2v_specs()
    maps2, oidx2, _d2, _tot2 = parity_census(sp2, 10)
    hits2 = sum(1 for (mx, ss) in maps2 for cc in ss
                if odd_balance(sp2, mx, cc)[0]
                == odd_balance(sp2, mx, cc)[1] + 1)
    nbal2 = sum(1 for (mx, ss) in maps2 for cc in ss
                if odd_balance(sp2, mx, cc)[0]
                == odd_balance(sp2, mx, cc)[1])
    assert hits2 == 0 and nbal2 > 0
    print(f"  (4b) SYNTHETIC mock (same impossible predicate) at NKo2v "
          f"under FULL 3^10 enumeration ({len(maps2)} parity maps): 0 "
          f"hits at exhaustion -> genuine oo, the E1(v) headline path "
          f"(mock disclosed as synthetic; the real predicate na = nb "
          f"finds {nbal2} balanced -- negative control)")
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stuck', action='store_true')
    ap.add_argument('--cases', action='store_true')
    ap.add_argument('--opt', action='store_true')
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    t0 = time.time()
    if args.validate or args.stuck:
        leg_stuck()
    if args.validate or args.cases:
        leg_cases()
    if args.validate or args.opt:
        leg_opt()
    if args.validate or args.adv:
        leg_adv()
    if args.validate:
        print(f"[GDESC] validate complete [{time.time() - t0:.0f}s]")


if __name__ == '__main__':
    main()
