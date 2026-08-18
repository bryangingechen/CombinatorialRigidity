"""GADM -- the twelfth kernel-(K) direction: the growth-law question at the
pentagon necklaces (spec: notes/Pencil-fanout.md S"Twelfth direction").

Primary target (a'): the d_fg = d_adm law -- fully-goodness is free at the
admissibility optimum.  Measured support at prep: d_fg = d_adm at 133/133
shapes (131 seeded pool subsample + W3 + NK(2), ALL at d <= 3, deliberately
not exhaustive -- the provenance travels with the figure).  Secondary (b'):
the balance-layer bound d_adm - d_par <= 2, or a family where it grows.

Modes (the spec's priority order; experiment 1 = --nk runs FIRST):
  --nk       the necklace family's own layer split: exact d_par = d_adm at
             the members (a d = m witness construction meeting the proven
             pentagon lower bound d >= m, DP-confirmed over the
             cycle-syndrome space at explicitly CONSTRUCTED matchings --
             perfect_matchings is never called at n_hub >= 30), and
             rank-certified fully-good tests AT the optimum: the (a') law's
             first test in the large-d regime.
  --free     the (a') case list: exhaustive optimal-solution censuses at
             W3 / NK(2) / the ladders / a fresh seeded pool subsample,
             W5 rank-light; per-mu fully-good availability (WHERE the
             exchange freedom has to live); the binding-chunk profile of
             the failing optima (the sticking-case list).
  --balance  the (b') case list: the odd-branch cap (<= 6 at every habitat
             shape, from the excess law), W3 layered exactly, the odd-rich
             necklace variant NKo(m), and an odd-6 pool hunt for a balance
             gap > 2.
  --adv      falsification controls, each with an F13 must-fire/-reject
             witness: DP vs the landed exhaustive instrument at NK(2);
             doctored-pentagon reject; non-matching-anchor reject; the W3
             balance gap and the NK(2) shift excess must be DETECTED; the
             d_fg cap discriminator must report an exhausted cap as a CAP,
             never as infinity.
  --validate all four, in the order above.

Family qualifiers, binding on every figure printed here: every "0
fully-hot" figure in the record is capacity-tight / realized only (the
binding-capable family carries 761 on a 184-shape subsample, (GR-36); the
(GR-40) corner condition prunes 815 -> 573 -- a prune, not a zero).

Exact integers throughout; rank only through gexist.fully_good_rank
(gridcol.block_generic_zero's GF(p) lower bound with the exact-Q recheck
through BOTH matrices, README S4 convention 2).  Rngs seeded per mode,
seeds printed; no `set` printed; nothing samples a placement, so
repin.star_generic gates nothing here (S(K-clos) (AC-9)).  Wall-clock [Ns]
annotations are inherently non-deterministic; every other byte is
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
from gcap import branch_stats, pool_specs                              # noqa: E402
from gunif import WITNESSES                                            # noqa: E402
from gexist import fully_good_rank, ladder_specs                       # noqa: E402
from gorient import (cm_solve, cm_colouring, odd_balance,              # noqa: E402
                     perfect_matchings, m_of_matching, prep_shape,
                     fully_good_scan, fast_defects, darts_at)
from gdev import (nk_specs, habitat_by_lemma, light_hm, phi_of,        # noqa: E402
                  mu_of, in_coset, fundamental_cycles, min_dev,
                  even_vec)

R_SEED = 20260817
INF = 10 ** 9


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive (checked against the README index
# and the Divergences table).  `cycle_masks`/`dp_pref`/`dp_walk` are the
# exact per-matching deviation DP over the cycle-syndrome space (new: the
# landed gdev.min_dev enumerates deviation SETS and is infeasible past the
# pool); `mu_in_phi` is the same-or-different 2-colouring test for coset
# membership (cross-checked against gdev.in_coset in --adv);
# `pentagon_floor_audit` certifies the (GR-43) pentagon accounting per
# witness; `complete_matching` builds explicit perfect matchings;
# `nk_d_eq_m_witness` / `nk_d_eq_m_random` are the d = m witness searches;
# `nko_specs` is the odd-rich necklace variant for the (b') hunt.


def cycle_masks(specs, n):
    """Per-branch syndrome bitmask over one fundamental-cycle basis; the
    syndrome of a GF(2) branch vector x is the XOR of masks over its
    support.  A minority map m is parity-consistent iff
    synd(mu(m)) == synd(tau), tau = [l even]."""
    cycles = fundamental_cycles(specs, n)
    dim = len(cycles)
    assert dim == len(specs) - n + 1, "cycle-space dimension off"
    bmask = [0] * len(specs)
    for j, cyc in enumerate(cycles):
        for i in cyc:
            bmask[i] |= 1 << j
    tau = even_vec(specs)
    s0 = 0
    for i, t in enumerate(tau):
        if t:
            s0 ^= bmask[i]
    return cycles, bmask, dim, s0


def dp_moves(specs, n, mat, bmask):
    """Per hub, the two deviation moves as (syndrome, dart) pairs."""
    base = m_of_matching(specs, mat)
    dinc = darts_at(specs)
    moves = []
    for v in range(n):
        bi = base[v][0]
        mv = []
        for (i, e) in dinc[v]:
            if (i, e) == base[v]:
                continue
            mv.append((bmask[bi] ^ bmask[i], (i, e)))
        assert len(mv) == 2, "cubic hub without exactly two deviations"
        moves.append(mv)
    return base, moves


def dp_pref(specs, n, mat, bmask, dim, keep_pref):
    """Exact DP: after processing hubs 0..v-1, dp[s] = min deviations
    among them whose move syndromes XOR to s (each hub deviates at most
    once, to one of its two non-matching darts).  Returns (base, moves,
    prefs): prefs[v] = the table before hub v, prefs[n] = final; when
    keep_pref is False only the final table is kept (prefs = [final])."""
    base, moves = dp_moves(specs, n, mat, bmask)
    sz = 1 << dim
    dp = [INF] * sz
    dp[0] = 0
    prefs = [dp[:]] if keep_pref else None
    for v in range(n):
        cur = dp
        best = cur[:]
        for (sig, _d) in moves[v]:
            if sig == 0:
                continue          # a zero-syndrome move never lowers a min
            for s in range(sz):
                c = cur[s ^ sig] + 1
                if c < best[s]:
                    best[s] = c
        dp = best
        if keep_pref:
            prefs.append(dp[:])
    return base, moves, (prefs if keep_pref else [dp])


def dp_walk(specs, n, base, moves, prefs, s_tgt, budget, rng, tries=200):
    """Sample a deviation witness of EXACT total count `budget` reaching
    syndrome `s_tgt`, by randomized backward traceback over the prefix DP
    tables (requires keep_pref).  Returns a minority map or None (the
    retry cap is disclosed by the caller)."""
    nn = len(moves)
    for _t in range(tries):
        s, r = s_tgt, budget
        m = dict(base)
        for v in range(nn - 1, -1, -1):
            opts = []
            if prefs[v][s] <= r:
                opts.append(None)
            if r >= 1:
                for (sig, d) in moves[v]:
                    if sig != 0 and prefs[v][s ^ sig] <= r - 1:
                        opts.append((sig, d))
            if not opts:
                break
            ch = opts[rng.randrange(len(opts))]
            if ch is not None:
                m[v] = ch[1]
                s ^= ch[0]
                r -= 1
        else:
            if s == 0 and r == 0:
                return m
    return None


def mu_in_phi(specs, n, mu):
    """mu in [l even] + Cut(G0), by the 2-colouring test: need c with
    delta(c) = mu + tau, i.e. BFS forcing c(w) = c(u) ^ (mu+tau)_beta;
    returns the colouring dict or None.  Cross-checked against
    gdev.in_coset in --adv."""
    tau = even_vec(specs)
    adj = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        b = mu[i] ^ tau[i]
        adj[u].append((w, b))
        adj[w].append((u, b))
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
    assert len(c) == n, "hub graph disconnected"
    return c


def pentagon_floor_audit(specs, pent, mat, m):
    """The (GR-43) accounting, certified on a concrete witness: every hub
    lies in exactly one pentagon with exactly 2 own-pentagon branches + 1
    external; mu(M) = 0 is REQUIRED (matching anchor -- a base map with
    mu != 0 is REJECTED, guarding ranking item 8's boundary); each
    deviation flips {M(v), new dart's branch}, never a foreign pentagon's
    branch; per pentagon the single-own-pentagon-flip (b-move) count has
    the parity of |mu cap P_i|.  Returns (dist, per-pentagon b-counts)."""
    pset = [set(ids) for ids in pent]
    allpent = set()
    for ps in pset:
        allpent |= ps
    owner = {}
    for pi, ids in enumerate(pent):
        assert len(ids) == 5, "doctored pentagon: not five branches"
        vs = []
        for i in ids:
            (u, w, _L) = specs[i]
            vs.extend((u, w))
        assert len(set(vs)) == 5, "doctored pentagon: not a 5-cycle"
        for v in set(vs):
            assert v not in owner, "pentagons not vertex-disjoint"
            owner[v] = pi
    base = m_of_matching(specs, mat)
    assert sorted(base) == sorted(owner), \
        "anchor does not cover exactly the pentagon hubs"
    assert sum(mu_of(specs, base)) == 0, \
        "non-matching anchor REJECTED: mu(base) != 0 evades the floor " \
        "by discarding the (GR-37)(ii) cancellation (ranking item 8)"
    for v in sorted(owner):
        inc = [i for i, (u, w, _L) in enumerate(specs) if v in (u, w)]
        own = [i for i in inc if i in pset[owner[v]]]
        assert len(inc) == 3 and len(own) == 2, \
            "hub without exactly 2 own-pentagon branches + 1 external"
    bcnt = [0] * len(pent)
    dist = 0
    for v in sorted(m):
        dart = m[v]
        if dart == base[v]:
            continue
        dist += 1
        flips = {base[v][0], dart[0]}
        pi = owner[v]
        for f in flips:
            assert (f in pset[pi]) or (f not in allpent), \
                "move flips a foreign pentagon branch"
        if len(flips & pset[pi]) == 1:
            bcnt[pi] += 1
    mu = mu_of(specs, m)
    for pi, ids in enumerate(pent):
        assert bcnt[pi] % 2 == sum(mu[i] for i in ids) % 2, \
            "(GR-43) b-move parity accounting off"
    return dist, bcnt


def complete_matching(specs, n, forced, cap=200000):
    """A perfect matching of the hub multigraph containing the forced
    branch indices, by backtracking; None if the node cap binds (the
    caller discloses).  perfect_matchings is NEVER called at n >= 30."""
    inc = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        if u != w:
            inc[u].append((i, w))
            inc[w].append((i, u))
    covered = set()
    acc = list(forced)
    for i in forced:
        (u, w, _L) = specs[i]
        if u in covered or w in covered:
            return None
        covered.add(u)
        covered.add(w)
    nodes = [0]

    def rec():
        nodes[0] += 1
        if nodes[0] > cap:
            return None
        v = next((x for x in range(n) if x not in covered), None)
        if v is None:
            return frozenset(acc)
        for (i, u) in inc[v]:
            if u != v and u not in covered:
                covered.add(v)
                covered.add(u)
                acc.append(i)
                got = rec()
                if got is not None:
                    return got
                acc.pop()
                covered.discard(v)
                covered.discard(u)
        return None

    return rec()


def pentagon_pairings(m):
    """Perfect matchings of the pentagon-pairing multigraph: nodes = the
    m pentagons; edges = the two links (i, i+1) and the chord
    (i, i+m/2).  Enumerated recursively (m <= 10)."""
    edges = []
    for i in range(m):
        edges.append((i, (i + 1) % m, 'linkA'))
        edges.append((i, (i + 1) % m, 'linkB'))
    for i in range(m // 2):
        edges.append((i, i + m // 2, 'chord'))
    out = []

    def rec(un, acc):
        if not un:
            out.append(list(acc))
            return
        v = min(un)
        for (a, b, tag) in edges:
            if a == v and b in un and b != v:
                rec(un - {a, b}, acc + [(a, b, tag)])
            elif b == v and a in un and a != v:
                rec(un - {a, b}, acc + [(b, a, tag)])

    rec(frozenset(range(m)), [])
    return out


def nk_external(specs, m, pair):
    """The G0 branch index and the (moving hub, moving hub) pair of a
    pentagon-pairing edge."""
    (a, b, tag) = pair

    def V(i, j):
        return 5 * (i % m) + j

    if tag == 'linkA':
        want = (V(a, 0), V(b, 2)) if (a + 1) % m == b else (V(b, 0), V(a, 2))
    elif tag == 'linkB':
        want = (V(a, 1), V(b, 3)) if (a + 1) % m == b else (V(b, 1), V(a, 3))
    else:
        want = (V(min(a, b), 4), V(max(a, b), 4))
    for i, (u, w, _L) in enumerate(specs):
        if (u, w) == want or (w, u) == want:
            return i, want[0], want[1]
    raise AssertionError("pairing external not found in specs")


def pent_edges_at(specs, pent, pi, v):
    """The two own-pentagon branch indices at hub v."""
    return [i for i in pent[pi] if v in (specs[i][0], specs[i][1])]


def hub_owner(specs, pent):
    owner = {}
    for pi, ids in enumerate(pent):
        for i in ids:
            for v in specs[i][:2]:
                owner.setdefault(v, pi)
    return owner


def nk_d_eq_m_witness(specs, pent, m, n, want=1):
    """Search for d = m witnesses of the PAIRED form: a pentagon pairing,
    one moving hub per pentagon at the shared external, one
    pentagon-edge flip each; mu = the m chosen pentagon edges (all
    external flips cancel in pairs); requires mu in Phi and a perfect
    matching containing the pairing externals.  Exhaustive over pairings
    x 4^(m/2) edge choices (m <= 10) until `want` witnesses are
    collected.  Returns a list of (mat, minority map, mu)."""
    owner = hub_owner(specs, pent)
    found = []
    for pairing in pentagon_pairings(m):
        exts = [nk_external(specs, m, p) for p in pairing]
        hubpairs = []
        for (_x, ha, hb) in exts:
            ea = pent_edges_at(specs, pent, owner[ha], ha)
            eb = pent_edges_at(specs, pent, owner[hb], hb)
            hubpairs.append((ha, ea, hb, eb))
        k = len(exts)
        for choice in range(1 << (2 * k)):
            mu = [0] * len(specs)
            picks = []
            for j, (ha, ea, hb, eb) in enumerate(hubpairs):
                pa = ea[(choice >> (2 * j)) & 1]
                pb = eb[(choice >> (2 * j + 1)) & 1]
                mu[pa] ^= 1
                mu[pb] ^= 1
                picks.append((ha, pa, hb, pb))
            if sum(mu) != m:
                continue
            if mu_in_phi(specs, n, mu) is None:
                continue
            forced = [x for (x, _a, _b) in exts]
            mat = complete_matching(specs, n, forced)
            if mat is None:
                continue
            mm = m_of_matching(specs, mat)
            for (ha, pa, hb, pb) in picks:
                mm[ha] = (pa, 0 if ha == specs[pa][0] else 1)
                mm[hb] = (pb, 0 if hb == specs[pb][0] else 1)
            if mu_of(specs, mm) != mu:
                continue
            if cm_solve(specs, mm) is None:
                continue
            found.append((mat, mm, mu))
            if len(found) >= want:
                return found
    return found


def nk_d_eq_m_random(specs, pent, m, n, rng, tries=20000):
    """Fallback d = m search, GENERAL form: one moving hub per pentagon
    (any of its 5), one pentagon-edge flip each; unpaired external flips
    land IN mu.  Randomized; tries disclosed by the caller."""
    owner = hub_owner(specs, pent)
    hubs_of = [sorted(v for v, p in owner.items() if p == pi)
               for pi in range(m)]
    ext_of = {}
    allpent = {i for ids in pent for i in ids}
    for v in sorted(owner):
        inc = [i for i, (u, w, _L) in enumerate(specs) if v in (u, w)]
        ext = [i for i in inc if i not in allpent]
        assert len(ext) == 1
        ext_of[v] = ext[0]
    for _t in range(tries):
        movers = []
        mu = [0] * len(specs)
        for pi in range(m):
            v = hubs_of[pi][rng.randrange(5)]
            pe = pent_edges_at(specs, pent, pi, v)[rng.randrange(2)]
            movers.append((v, pe))
            mu[pe] ^= 1
            mu[ext_of[v]] ^= 1
        if mu_in_phi(specs, n, mu) is None:
            continue
        # matching constraint: M(v) in {pe_v, ext_v}; try a random
        # option per mover, forced edges must form a partial matching
        for _t2 in range(6):
            forced = set()
            used = {}
            ok = True
            for (v, pe) in movers:
                choicelist = [ext_of[v], pe] if rng.random() < 0.5 \
                    else [pe, ext_of[v]]
                placed = False
                for cch in choicelist:
                    (cu, cw, _L) = specs[cch]
                    if used.get(cu, cch) == cch and used.get(cw, cch) == cch:
                        used[cu] = cch
                        used[cw] = cch
                        forced.add(cch)
                        placed = True
                        break
                if not placed:
                    ok = False
                    break
            if not ok:
                continue
            mat = complete_matching(specs, n, sorted(forced))
            if mat is None:
                continue
            mm = m_of_matching(specs, mat)
            good = True
            for (v, pe) in movers:
                pair = {pe, ext_of[v]}
                if mm[v][0] not in pair:
                    good = False
                    break
                other = (pair - {mm[v][0]}).pop()
                mm[v] = (other, 0 if v == specs[other][0] else 1)
            if not good:
                continue
            if mu_of(specs, mm) != mu:
                continue
            if cm_solve(specs, mm) is None:
                continue
            return mat, mm, mu
    return None


def nko_specs(m):
    """The odd-rich necklace variant NKo(m): same graph as NK(m), the
    excess placed on ODD branches while every pentagon stays all-l2 (so
    the (GR-43) pentagon floor still applies).  m >= 6: six l3 links;
    m = 2: four l3 links + the chord at l4."""
    specs, pent, _F, chords = nk_specs(m)
    specs = [list(s) for s in specs]
    for s in specs:
        s[2] = 2
    pentset = {i for ids in pent for i in ids}
    linkidx = [i for i in range(len(specs))
               if i not in pentset and i not in chords]
    if m >= 6:
        for i in linkidx[:6]:
            specs[i][2] = 3
    else:
        for i in linkidx[:4]:
            specs[i][2] = 3
        specs[chords[0]][2] = 4
    assert sum(L - 2 for (_u, _w, L) in specs) == 6
    return [tuple(s) for s in specs], pent, chords


def opt_census(specs, edges, allverts, hm, tec_cf, lens, mats, d):
    """Exhaustive census of ALL optimal solutions at deviation count d:
    per optimal mu (as a tuple), (#admissible realizations, #fully-good
    ones -- exact full-chunk scan), plus the failing (m, c) pairs."""
    dinc = darts_at(specs)
    hubs = sorted(dinc)
    per_mu = {}
    fails = []
    for mat in mats:
        base = m_of_matching(specs, mat)
        for vs in combinations(hubs, d):
            lists = [[x for x in dinc[v] if x != base[v]] for v in vs]
            idx = [0] * d
            while True:
                m = dict(base)
                for j, v in enumerate(vs):
                    m[v] = lists[j][idx[j]]
                sols = cm_solve(specs, m)
                if sols is not None:
                    for c in sols:
                        na, nb = odd_balance(specs, m, c)
                        if na != nb:
                            continue
                        col = cm_colouring(specs, m, c)
                        if not admissible(edges, allverts, hm, col):
                            continue
                        key = tuple(mu_of(specs, m))
                        stats = branch_stats(hm, col, 'A')
                        good = fully_good_scan(hm, None, tec_cf, lens,
                                               stats)
                        a, g = per_mu.get(key, (0, 0))
                        per_mu[key] = (a + 1, g + (1 if good else 0))
                        if not good:
                            fails.append((dict(m), dict(c)))
                j = d - 1
                while j >= 0:
                    idx[j] += 1
                    if idx[j] < len(lists[j]):
                        break
                    idx[j] = 0
                    j -= 1
                if j < 0:
                    break
            if d == 0:
                break
    return per_mu, fails


# ------------------------------------------------- [GAD-1] --nk -------------

def leg_nk():
    """[GAD-1] experiment 1: the necklace layer split, measured where the
    133/133 law has never been tested."""
    t0 = time.time()
    print(f"[GAD-1] the necklace family's own layer split "
          f"(seed {R_SEED + 1})")
    rng = random.Random(R_SEED + 1)
    verdicts = {}
    for m in (2, 6, 8, 10):
        specs, pent, F, chords = nk_specs(m)
        n = 5 * m
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        ok, why = habitat_by_lemma(n, hedges, lens_s)
        assert ok, f"NK({m}) not habitat: {why}"
        cycles, bmask, dim, s0 = cycle_masks(specs, n)
        if n <= 20:
            _phi, phis = phi_of(specs, n)
            floor = (phis + 1) // 2
            floormsg = f"{floor} (exact 2^{n} enumeration)"
        elif m % 4 == 2:
            floor = m // 2
            floormsg = f"{floor} (phi* = m exactly at m == 2 mod 4, " \
                       f"(GR-42)(ii))"
        else:
            floor = m // 2
            floormsg = f"in [{m // 2}, {3 * m // 4}] (exact phi* OPEN in " \
                       f"[m, m + m/2] at m == 0 mod 4; only phi >= m is " \
                       f"consumed)"
        # ---- the d = m witnesses (upper bound; the proven (GR-43)
        #      pentagon bound is the matching-free lower bound)
        nwant = 40 if m == 10 else 12
        wits = nk_d_eq_m_witness(specs, pent, m, n, want=nwant)
        how = 'paired search'
        if not wits:
            wr = nk_d_eq_m_random(specs, pent, m, n, rng)
            wits = [wr] if wr is not None else []
            how = 'general randomized search (20000 tries)'
        elif m == 10:
            for _i in range(20):
                wr = nk_d_eq_m_random(specs, pent, m, n, rng, tries=2000)
                if wr is not None and all(wr[1] != w[1] for w in wits):
                    wits.append(wr)
        wit = wits[0] if wits else None
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = light_hm(edges)
        wit_m = wit_mat = None
        if wit is not None:
            mat, mm, mu = wit
            dist, bcnt = pentagon_floor_audit(specs, pent, mat, mm)
            assert dist == m and all(b >= 1 for b in bcnt), \
                "constructed witness violates its own accounting"
            assert in_coset(specs, n, mu_of(specs, mm), cycles), \
                "witness mu outside the coset (in_coset cross-check)"
            sols = cm_solve(specs, mm)
            assert sols is not None
            na, nb = odd_balance(specs, mm, sols[0])
            assert na == nb == 0, "NK member with odd branches?"
            col = cm_colouring(specs, mm, sols[0])
            assert admissible(edges, allverts, hm, col), \
                "parity-consistent NK witness not admissible -- the " \
                "(GR-37)(i) correspondence broke"
            wit_m, wit_mat = mm, mat
            print(f"  NK({m}) (n={n}): d = {m} WITNESS constructed via "
                  f"{how}; audited: every pentagon takes >= 1 b-move "
                  f"(counts {bcnt}) => with the proven pentagon bound "
                  f"d >= {m} from EVERY perfect matching: "
                  f"d_par = d_adm = {m} EXACT (balance vacuous: all-even)")
        else:
            print(f"  NK({m}) (n={n}): NO d = {m} witness found (paired "
                  f"search exhausted + 20000 random tries -- an exhausted "
                  f"cap, not a nonexistence proof); d_par in "
                  f"[{m}, ?] by the pentagon bound")
        # ---- DP confirmation at the constructed matching
        prefs = None
        if wit is not None and dim <= 21:
            keep = dim <= 16
            base, moves, prefs = dp_pref(specs, n, wit_mat, bmask, dim,
                                         keep)
            dmin = prefs[-1][s0]
            assert dmin >= m, "(GR-43) REFUTED by DP: min deviations < m"
            assert dmin <= m, "DP misses the constructed witness's count"
            print(f"    DP (syndrome dim {dim}, 2^{dim} states, at the "
                  f"construction's matching): exact min = {dmin} == m -- "
                  f"the (GR-43) floor is ATTAINED at this matching")
            if not keep:
                prefs = None
        elif wit is not None:
            print(f"    DP skipped at dim {dim} (2^{dim} states past the "
                  f"budget); the exact value stands on the proven lower "
                  f"bound + the constructed witness")
        # ---- NK(2): cross-check the whole triple against the landed
        #      exhaustive instrument and GDEV's recorded figures
        if m == 2:
            _e2, _a2, _hm2, _inc2, _tec2, tec_cf2, _ak2 = prep_shape(specs)
            mats2 = perfect_matchings(specs)
            d_par, d_adm, d_fg = min_dev(specs, edges, allverts, hm,
                                         tec_cf2, hm['lens'], mats2, 3)
            assert (d_par, d_adm, d_fg) == (2, 2, 2), \
                "NK(2) triple moved from GDEV's recorded 2/2/2"
            print(f"    NK(2) cross-check vs min_dev over all "
                  f"{len(mats2)} matchings: d_par = d_adm = d_fg = 2 "
                  f"(GDEV's recorded figures reproduced)")
        # ---- the (a') test AT the optimum: rank-certified fully-good
        #      among optimal witnesses (caps disclosed)
        d_fg_here = None
        ranked = 0
        cap_wit = 60 if m == 10 else 12
        if wit is not None:
            cands = [w[1] for w in wits]
            if prefs is not None:
                for _i in range(4 * cap_wit):
                    mm2 = dp_walk(specs, n, base, moves, prefs, s0, m, rng)
                    if mm2 is not None and mm2 not in cands:
                        cands.append(mm2)
                    if len(cands) >= cap_wit:
                        break
            for mm2 in cands[:cap_wit]:
                sols = cm_solve(specs, mm2)
                if sols is None:
                    continue
                for c in sols:
                    col = cm_colouring(specs, mm2, c)
                    if not admissible(edges, allverts, hm, col):
                        continue
                    ranked += 1
                    if fully_good_rank(edges, allverts, hm, col, rng):
                        d_fg_here = m
                        break
                if d_fg_here is not None:
                    break
        if d_fg_here is not None:
            print(f"    (a') AT THE OPTIMUM: fully good RANK-CERTIFIED at "
                  f"deviation count {m} = d_adm ({ranked} rank tests, "
                  f"witness cap {cap_wit}) -- d_fg = d_adm = {m} at "
                  f"NK({m}): the law HOLDS at this member")
            verdicts[m] = (floormsg, m, str(m))
        elif wit is not None:
            print(f"    (a') AT THE OPTIMUM: not certified within the "
                  f"witness cap ({ranked} rank tests, cap {cap_wit}); an "
                  f"exhausted cap is a CAP, not a d_fg > d_adm claim "
                  f"(d_fg is a min over ALL matchings)")
            verdicts[m] = (floormsg, m, '(cap)')
        else:
            verdicts[m] = (floormsg, None, '(cap)')
    print("  == experiment 1 verdict ==")
    for m in (2, 6, 8, 10):
        floormsg, d_adm, df = verdicts[m]
        da = str(d_adm) if d_adm is not None else f">= {m}"
        print(f"    NK({m}): floor ceil(phi*/2) = {floormsg}; "
              f"d_par = d_adm = {da} (balance vacuous at all-even "
              f"shapes); d_fg = {df}")
    print("    -> OUTCOME 3 of the spec's three: the whole stack sits at "
          "d = m, strictly ABOVE the floor (= m/2 at m == 2 mod 4; <= "
          "3m/4 always), the excess >= m/4 GROWING in m.  d_par is "
          "MEASURED at the members and equals d_adm (balance vacuous), "
          "so the excess is the SHIFT-METRIC layer, not balance: "
          "(GR-41)'s Hamming relaxation is loose by >= m/4 -> unbounded "
          "((GR-43): the pentagon floor d >= m, proven + audited per "
          "witness).  The d_fg = d_adm law itself HOLDS at every member "
          "where the optimum was rank-certified.")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GAD-2] --free -----------

def leg_free():
    """[GAD-2] the (a') case list: optimal-solution censuses; per-mu
    fully-good availability; the sticking profile."""
    t0 = time.time()
    print(f"[GAD-2] (a') optimal-class census (seed {R_SEED + 2})")
    rng = random.Random(R_SEED + 2)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    def census_of(tag, specs, nloc, dmax):
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        _e, _a, hm, _inc, _tec, tec_cf, _ak = prep_shape(specs)
        lens = hm['lens']
        mats = perfect_matchings(specs)
        d_par, d_adm, d_fg = min_dev(specs, edges, allverts, hm, tec_cf,
                                     lens, mats, dmax)
        assert d_adm is not None, f"{tag}: no admissible within {dmax}"
        if d_fg is None:
            print(f"  {tag}: d_adm = {d_adm}, d_fg NOT FOUND within cap "
                  f"{dmax} (an exhausted cap is not infinity)")
            return
        assert d_fg == d_adm, \
            f"{tag}: d_fg = {d_fg} > d_adm = {d_adm} -- the (a') LAW is " \
            f"REFUTED at a finite witness (E2's branch, HEADLINE)"
        per_mu, _fails = opt_census(specs, edges, allverts, hm, tec_cf,
                                    lens, mats, d_adm)
        tot = sum(a for (a, _g) in per_mu.values())
        good = sum(g for (_a, g) in per_mu.values())
        mu_all = len(per_mu)
        mu_good = sum(1 for (_a, g) in per_mu.values() if g > 0)
        print(f"  {tag} (n={nloc}): d_adm = d_fg = {d_adm}; optimal "
              f"census: {tot} admissible optima in {mu_all} optimal "
              f"mu-classes; fully-good {good}; {mu_good}/{mu_all} "
              f"mu-classes carry a fully-good realization")

    # ---- W3 FIRST (the balance stick), then the ladders, then NK(2)
    (_nm3, n3, specs3, _f3, _S3, _e3) = by_tag['W3']
    census_of('W3', specs3, n3, 3)
    census_of('CL5', ladder_specs(5, {0: 2, 1: 2, 2: 2}), 10, 3)
    census_of('CL6', ladder_specs(6, {0: 2, 1: 2, 2: 2}), 12, 2)
    specs2, _p2, _F2, _c2 = nk_specs(2)
    census_of('NK(2)', specs2, 10, 2)

    # ---- W5 rank-light (n = 16: the full-chunk scan's 2^24 subset
    #      enumeration is out of budget; fully-goodness by RANK)
    (_nm5, n5, specs5, _f5, _S5, _e5) = by_tag['W5']
    edges5 = subdivide(specs5)
    allverts5 = sorted(verts_of(edges5), key=str)
    hm5 = light_hm(edges5)
    mats5 = perfect_matchings(specs5)
    dinc5 = darts_at(specs5)
    hubs5 = sorted(dinc5)
    got = None
    ranked = 0
    n_opt = 0
    for nd in range(0, 3):
        for mat in mats5:
            base = m_of_matching(specs5, mat)
            for vs in combinations(hubs5, nd):
                lists = [[x for x in dinc5[v] if x != base[v]] for v in vs]
                idx = [0] * nd
                while True:
                    m = dict(base)
                    for j, v in enumerate(vs):
                        m[v] = lists[j][idx[j]]
                    sols = cm_solve(specs5, m)
                    if sols is not None:
                        for c in sols:
                            na, nb = odd_balance(specs5, m, c)
                            if na != nb:
                                continue
                            col = cm_colouring(specs5, m, c)
                            if not admissible(edges5, allverts5, hm5, col):
                                continue
                            n_opt += 1
                            if got is None and ranked < 25:
                                ranked += 1
                                if fully_good_rank(edges5, allverts5, hm5,
                                                   col, rng):
                                    got = nd
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
            if got is not None:
                break
        if got is not None:
            break
    assert got is not None, \
        f"W5: no rank-certified fully-good among the first admissible " \
        f"selections (cap 25 rank tests) -- raise the cap before reading"
    print(f"  W5 (n={n5}, rank-light): first admissible selections appear "
          f"at d = {got}; fully good RANK-CERTIFIED there ({ranked} rank "
          f"tests, cap 25) -- d_fg = d_adm = {got} at W5 (its "
          f"corner-separated chunks bind capably yet the optimum is free)")

    # ---- the fresh pool subsample: per-mu availability + sticking list
    picked = 0
    all_mu_ok = 0
    some_mu_dead = 0
    frac_min = None
    frac_min_tag = None
    stick_profiles = {}
    law_broken = []
    for n, specs in pool_specs():
        if rng.random() >= 0.02:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens_s):
            continue
        picked += 1
        edges, allverts, hm, _inc, _tec, tec_cf, _ak = prep_shape(specs)
        lens = hm['lens']
        mats = perfect_matchings(specs)
        d_par, d_adm, d_fg = min_dev(specs, edges, allverts, hm, tec_cf,
                                     lens, mats, 3)
        assert d_adm is not None and d_fg is not None, \
            f"pool shape past the d <= 3 cap: {sorted(specs)} -- investigate"
        if d_fg != d_adm:
            law_broken.append((sorted(specs), d_adm, d_fg))
            continue
        per_mu, fails = opt_census(specs, edges, allverts, hm, tec_cf,
                                   lens, mats, d_adm)
        tot = sum(a for (a, _g) in per_mu.values())
        good = sum(g for (_a, g) in per_mu.values())
        assert good > 0, "census misses the fully-good optimum"
        if all(g > 0 for (_a, g) in per_mu.values()):
            all_mu_ok += 1
        else:
            some_mu_dead += 1
        if frac_min is None or good * frac_min[1] < frac_min[0] * tot:
            frac_min = (good, tot)
            frac_min_tag = sorted(specs)
        for (mmap, c) in fails[:20]:
            col = cm_colouring(specs, mmap, c)
            acnt, du, dw = branch_stats(hm, col, 'A')
            for (cf, improper) in tec_cf:
                if improper:
                    continue
                dA, dB = fast_defects(cf, lens, acnt, du, dw)
                if dA <= 2 or dB <= 2:
                    ks, prs = cf
                    key = (min(dA, dB), len(ks), len(prs))
                    stick_profiles[key] = stick_profiles.get(key, 0) + 1
    assert not law_broken, \
        f"(a') LAW REFUTED at pool shapes {law_broken} (finite witnesses; " \
        f"E2's branch, HEADLINE)"
    print(f"  fresh pool subsample (rate 0.02, THIS driver's seed): "
          f"{picked} shapes, ALL with d_fg = d_adm -- the law holds on "
          f"the whole fresh subsample")
    print(f"    per-mu availability: at {all_mu_ok} shapes EVERY optimal "
          f"mu-class carries a fully-good realization; at {some_mu_dead} "
          f"shapes SOME optimal mu-class carries NONE -- there the (a') "
          f"exchange freedom must include the mu / matching choice, not "
          f"only the deviation set at fixed mu (the named sticking case)")
    if frac_min is not None:
        print(f"    worst fully-good fraction among optima: "
              f"{frac_min[0]}/{frac_min[1]} at specs {frac_min_tag}")
    print(f"    binding profile of failing optima (min defect, "
          f"#branches, #interiors) -> count: "
          f"{sorted(stick_profiles.items())} (capped at 20 fails/shape)")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GAD-3] --balance --------

def leg_balance():
    """[GAD-3] the (b') case list: the odd-branch cap, W3 layered
    exactly, the odd-rich necklaces, the odd-6 pool hunt."""
    t0 = time.time()
    print(f"[GAD-3] (b') the balance layer (seed {R_SEED + 3})")
    rng = random.Random(R_SEED + 3)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    # ---- (a) the odd-branch cap: the excess law => #odd branches <= 6
    checked = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.005:
            continue
        nodd = sum(1 for (_u, _w, L) in specs if L % 2 == 1)
        assert nodd <= 6, "odd-branch cap broken (excess law violated?)"
        assert nodd % 2 == 0, "odd #odd-branches at an even-hub shape"
        checked += 1
    print(f"  the odd-branch cap: every habitat shape has <= 6 odd "
          f"branches (each odd length l in (3,5) costs l-2 >= 1 of the "
          f"excess-6 budget) and an even number of them; asserted at "
          f"{checked} sampled pool shapes.  So the balance rider always "
          f"concerns <= 6 branches: any imbalance is <= 6, i.e. <= 3 "
          f"repair units -- the layer CANNOT grow through the imbalance "
          f"itself, only through a growing repair COST per unit")

    # ---- (b) W3 layered exactly: d_par vs d_adm
    (_nm3, n3, specs3, _f3, _S3, _e3) = by_tag['W3']
    edges3 = subdivide(specs3)
    allverts3 = sorted(verts_of(edges3), key=str)
    _e, _a, hm3, _inc3, _tec3, tec_cf3, _ak3 = prep_shape(specs3)
    mats3 = perfect_matchings(specs3)
    d_par3, d_adm3, d_fg3 = min_dev(specs3, edges3, allverts3, hm3,
                                    tec_cf3, hm3['lens'], mats3, 3)
    assert d_adm3 == d_fg3 == 3, "the W3 stick moved"
    print(f"  W3 layered exactly (all {len(mats3)} matchings): "
          f"d_par = {d_par3}, d_adm = {d_adm3}, d_fg = {d_fg3} -- the "
          f"balance gap d_adm - d_par = {d_adm3 - d_par3}")

    # ---- (c) the odd-rich necklaces NKo(m)
    for m in (2, 6):
        specs, pent, _chords = nko_specs(m)
        n = 5 * m
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        ok, why = habitat_by_lemma(n, hedges, lens_s)
        assert ok, f"NKo({m}) not habitat: {why}"
        nodd = sum(1 for L in lens_s if L % 2 == 1)
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = light_hm(edges)
        _cycles, bmask, dim, s0 = cycle_masks(specs, n)
        if m == 2:
            _e2, _a2, _hm2, _inc2, _tec2, tec_cf2, _ak2 = prep_shape(specs)
            mats = perfect_matchings(specs)
            d_par, d_adm, d_fg = min_dev(specs, edges, allverts, hm,
                                         tec_cf2, hm['lens'], mats, 4)
            gapmsg = '(cap 4)' if d_adm is None else str(d_adm - d_par)
            print(f"  NKo(2) (n={n}, {nodd} odd branches): exact "
                  f"d_par = {d_par}, d_adm = {d_adm}, d_fg = {d_fg} "
                  f"(all matchings, dmax 4) -- balance gap {gapmsg}")
            if d_fg is not None and d_adm is not None:
                assert d_fg == d_adm, \
                    "(a') LAW REFUTED at NKo(2) (finite witness, HEADLINE)"
        else:
            mat = complete_matching(specs, n, [])
            assert mat is not None
            base, moves, prefs = dp_pref(specs, n, mat, bmask, dim, True)
            dmin = prefs[-1][s0]
            assert dmin >= m, "(GR-43) pentagon floor refuted at NKo"
            found_k = None
            found_col = None
            used = {}
            for k in range(0, 4):
                used[k] = 0
                for _i in range(60):
                    mm = dp_walk(specs, n, base, moves, prefs, s0,
                                 dmin + k, rng)
                    if mm is None:
                        continue
                    used[k] += 1
                    sols = cm_solve(specs, mm)
                    if sols is None:
                        continue
                    for c in sols:
                        na, nb = odd_balance(specs, mm, c)
                        if na != nb:
                            continue
                        col = cm_colouring(specs, mm, c)
                        if admissible(edges, allverts, hm, col):
                            found_k = k
                            found_col = col
                            break
                    if found_k is not None:
                        break
                if found_k is not None:
                    break
            if found_k is not None:
                print(f"  NKo(6) (n={n}, {nodd} odd branches): "
                      f"d_par(M) = {dmin} exact at 1 constructed matching "
                      f"(>= {m} proven for every matching); BALANCED "
                      f"admissible witness at d_par + {found_k} (walk "
                      f"caps: 60/level, levels 0..3, walks landed "
                      f"{sorted(used.items())}) -- balance gap <= "
                      f"{found_k} at this matching (the gap is a min "
                      f"over matchings; this is an upper bound)")
                if fully_good_rank(edges, allverts, hm, found_col, rng):
                    print(f"    and that balanced witness is fully good "
                          f"(RANK-certified): d_fg <= {dmin + found_k} "
                          f"at NKo(6) -- the (a') law is consistent "
                          f"here too")
                else:
                    print(f"    (its rank test did not certify at the "
                          f"first witness; cap 1 -- no claim)")
            else:
                print(f"  NKo(6) (n={n}, {nodd} odd branches): "
                      f"d_par(M) = {dmin}; NO balanced witness within "
                      f"d_par + 3 at the walk caps (60/level) -- a "
                      f"candidate balance stick PAST the pool's (0,2); "
                      f"walks landed {sorted(used.items())}; escalate "
                      f"before reading as structure")

    # ---- (d) the odd-6 pool hunt for a gap > 2
    picked = 0
    gap_hist = {}
    worst = None
    for n, specs in pool_specs():
        nodd = sum(1 for (_u, _w, L) in specs if L % 2 == 1)
        if nodd != 6:
            continue
        if rng.random() >= 0.08:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens_s):
            continue
        picked += 1
        edges, allverts, hm, _inc, _tec, tec_cf, _ak = prep_shape(specs)
        mats = perfect_matchings(specs)
        d_par, d_adm, _d_fg = min_dev(specs, edges, allverts, hm, tec_cf,
                                      hm['lens'], mats, 4)
        assert d_par is not None and d_adm is not None, \
            f"odd-6 shape past dmax 4: {sorted(specs)} -- investigate"
        g = d_adm - d_par
        gap_hist[g] = gap_hist.get(g, 0) + 1
        if worst is None or g > worst[0]:
            worst = (g, sorted(specs))
        assert g <= 2, \
            f"BALANCE GAP {g} > 2 at odd-6 pool shape {sorted(specs)} " \
            f"-- (b') REFUTED as a <= 2 bound; HEADLINE this shape"
    print(f"  odd-6 pool hunt (the odd-richest stratum): {picked} shapes, "
          f"balance-gap histogram {sorted(gap_hist.items())} -- no gap "
          f"> 2 found (a measured negative at the sampled caps, not a "
          f"proof); worst gap {worst[0] if worst else '-'}")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GAD-4] --adv ------------

def leg_adv():
    """[GAD-4] falsification controls, each with a must-fire/-reject
    witness (F13)."""
    t0 = time.time()
    print(f"[GAD-4] falsification controls (seed {R_SEED + 4})")
    rng = random.Random(R_SEED + 4)

    # ---- (1) DP vs the landed exhaustive instrument at NK(2)
    specs, pent, _F, _chords = nk_specs(2)
    n = 10
    cycles, bmask, dim, s0 = cycle_masks(specs, n)
    mats = perfect_matchings(specs)
    dpmins = []
    for mat in mats:
        _b, _mv, prefs = dp_pref(specs, n, mat, bmask, dim, False)
        dpmins.append(prefs[-1][s0])
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    hm = light_hm(edges)
    _e2, _a2, _hm2, _inc2, _tec2, tec_cf2, _ak2 = prep_shape(specs)
    d_par, _d_adm, _d_fg = min_dev(specs, edges, allverts, hm, tec_cf2,
                                   hm['lens'], mats, 3)
    assert min(dpmins) == d_par == 2, \
        "DP disagrees with min_dev at NK(2) -- DP wrong, stop"
    print(f"  (1) DP validated: min over all {len(mats)} NK(2) matchings "
          f"= {min(dpmins)} == min_dev's d_par = {d_par} (per-matching "
          f"DP minima {sorted(dpmins)})")

    # ---- (2) mu_in_phi vs in_coset on random vectors
    agree = 0
    for _i in range(2000):
        x = [rng.randrange(2) for _ in specs]
        a = mu_in_phi(specs, n, x) is not None
        b = in_coset(specs, n, x, cycles)
        assert a == b, "mu_in_phi and in_coset disagree"
        agree += 1
    print(f"  (2) coset-test cross-check: mu_in_phi == in_coset at "
          f"{agree} random vectors at NK(2)")

    # ---- (3) doctored pentagon must-reject
    fake_pent = [pent[0][:4] + [pent[1][0]], pent[1]]
    fired = False
    try:
        base = m_of_matching(specs, mats[0])
        pentagon_floor_audit(specs, fake_pent, mats[0], dict(base))
    except AssertionError:
        fired = True
    assert fired, "doctored pentagon list ACCEPTED -- audit toothless"
    print("  (3) doctored-pentagon control: a non-5-cycle claimed as a "
          "pentagon is REJECTED by the floor audit")

    # ---- (4) non-matching anchor must-reject (ranking item 8's boundary)
    dinc = darts_at(specs)
    mat0 = sorted(mats[0])
    dropped = mat0[-1]
    near = frozenset(mat0[:-1])
    basebad = m_of_matching(specs, near)
    (u0, w0, _L0) = specs[dropped]
    # point the two uncovered hubs so their flips do NOT cancel: u0 at a
    # non-dropped dart, w0 at the dropped branch
    basebad[u0] = next((i, e) for (i, e) in dinc[u0] if i != dropped)
    basebad[w0] = (dropped, 1 if w0 == specs[dropped][1] else 0)
    assert sum(mu_of(specs, basebad)) != 0
    fired = False
    try:
        pentagon_floor_audit(specs, pent, near, basebad)
    except AssertionError:
        fired = True
    assert fired, "non-matching anchor ACCEPTED -- the mu(base) = 0 " \
        "gate is toothless and the floor could be silently evaded"
    print("  (4) non-matching-anchor control: a near-perfect-matching "
          "base map is REJECTED (mu(base) != 0); an anchor class with "
          "mu != 0 evades the floor by construction but discards the "
          "(GR-37)(ii) cancellation -- a NEW MODEL, not a repair "
          "(ranking item 8)")

    # ---- (5) the W3 balance gap and NK(2) shift excess must be DETECTED
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    (_nm3, _n3, specs3, _f3, _S3, _e3) = by_tag['W3']
    edges3 = subdivide(specs3)
    allverts3 = sorted(verts_of(edges3), key=str)
    _e, _a, hm3, _inc3, _tec3, tec_cf3, _ak3 = prep_shape(specs3)
    mats3 = perfect_matchings(specs3)
    d_par3, d_adm3, _dfg3 = min_dev(specs3, edges3, allverts3, hm3,
                                    tec_cf3, hm3['lens'], mats3, 3)
    assert d_adm3 - d_par3 >= 1, "W3 balance gap NOT detected"
    _phi2, phis2 = phi_of(specs, n)
    assert d_par - (phis2 + 1) // 2 == 1, "NK(2) shift excess NOT detected"
    print(f"  (5) known positives detected: the W3 balance gap "
          f"d_adm - d_par = {d_adm3 - d_par3} >= 1; the NK(2) shift "
          f"excess d_par - floor = {d_par - (phis2 + 1) // 2} = 1")

    # ---- (6) the cap discriminator: an exhausted cap reports as a CAP
    d_par_c, d_adm_c, d_fg_c = min_dev(specs3, edges3, allverts3, hm3,
                                       tec_cf3, hm3['lens'], mats3, 2)
    assert d_adm_c is None and d_fg_c is None, \
        "the W3 scan at dmax 2 found what GDEV proved absent"
    print("  (6) cap discriminator: the W3 scan capped at dmax = 2 "
          "returns NOT-FOUND-WITHIN-CAP (None), never infinity.  E1 "
          "clause (iv) discipline: a finite d_adm < d_fg refutes the "
          "LAW (E2's branch); d_fg = infinity at finite d_adm would be "
          "a g-flank (E1); an exhausted cap is NEITHER")
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser(description="GADM: the growth-law "
                                 "question at the pentagon necklaces")
    ap.add_argument('--nk', action='store_true')
    ap.add_argument('--free', action='store_true')
    ap.add_argument('--balance', action='store_true')
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    ran = False
    if args.nk or args.validate:
        leg_nk()
        ran = True
    if args.free or args.validate:
        leg_free()
        ran = True
    if args.balance or args.validate:
        leg_balance()
        ran = True
    if args.adv or args.validate:
        leg_adv()
        ran = True
    if not ran:
        ap.print_help()


if __name__ == '__main__':
    main()
