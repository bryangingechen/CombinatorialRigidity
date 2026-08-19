"""§(K-grid) direction GDEV (2026-08-14) driver -- the arc's fourth PROOF
direction: the BOUNDED-DEVIATION SELECTION THEOREM target ((GR-37)'s anchor
with a shape-free deviation bound), merged with the CORNER-SIDE CHARGE for
`m_J = 0` (W5-type) chunks as its first named sub-deliverable, and the
(b)-conditional realized-binding seed hunt as the falsification control.
NO new sweep and NO enumerator: every pool below is an existing one (GCAP's
4920-shape `Lambda = empty` `D = 0` stratum, the GUNIF witnesses, the
CFLANK/GEXIST ladders) or a targeted construction in the GUNIF idiom.

A `w4/` leaf beside `gorient.py`, importing `gorient.py` / `gexist.py` /
`gunif.py` / `gcap.py` / `cflank.py` / `gridcol.py` / `closure.py`
READ-ONLY (README §2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --charge  # (GR-40): the corner charge, case list certified; the family recount
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --bound   # (GR-41): the parity floor; W3 priced FIRST; the pool layer split
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --adv     # (GR-42): the necklace family -- the shape-free bound REFUTED
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --hunt    # the (b)-armed targeted realized-fully-hot construction hunt
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --validate # all four in one process

Argument state: session draft `fanout-GDEV.md` (to be merged into
`notes/Pencil-informal-grid.md` §(K-grid) as Steps G48+; labels (GR-40)+ per the
2026-08-14 GDEV reservation in `notes/Pencil-labels.md`).

THE DERIVED STRUCTURE THE MODES REST ON (proofs in the draft; asserted here
rather than trusted).  Throughout `Lambda = empty`, `D = 0`: G° cubic,
lengths in [2, 5] ((SD-6)), total excess 6 ((GR-21)); chunk / interior /
corner / exit / defect as in gexist.py's header; binding in X iff
defect_X <= 2; (GR-36)/(GR-37) as in gorient.py's header.

(GR-40)  THE CORNER CHARGE.  For a connected branch subset S with all
         S-degrees in {2, 3} of a habitat shape, write z = #interiors
         (S-degree 2), corners = the 2(k-1) S-degree-3 hubs
         (k = |S| - |W_S| + 1), m_J = #interior-interior S-branches
         ((GR-36)'s J edges), odd_cc = #ODD corner-corner S-branches.
         At every admissible colouring, in BOTH blocks,
             defect_X(S) >= w45(S)
                            + ceil((z + odd_cc - m_J - (k-1)) / 2).
         PROOF SHAPE (the case list --charge certifies): each corner
         needs >= 1 A-dart (mono-hub ban); A-darts at corners are
         supplied only by (i) even cc branches (exactly one A-end each),
         (ii) A-majority odd branches (charged by (GR-36)(i)), and
         (iii) even corner-interior branches whose interior end is B --
         i.e. by non-AA interiors (also charged).  Counting:
         #cc = 3(k-1) - z + m_J, so the demand 2(k-1) forces
         2*(defect_X - w45) >= z + odd_cc - m_J - (k-1).  Consequences:
         a chunk BINDING in some block satisfies the colouring-free
             z + odd_cc - m_J <= (k-1) + 4 - 2 w45     (corner condition)
         -- the m_J = 0 (corner-separated) analogue of (GR-36)(iii)'s
         m_J <= 4 - 2 w45.  TIGHT at W3M's S (bound 1 = defect_A, where
         the (GR-36) bound is 0); the W5 scaling family sits exactly at
         the zero of the bound (z = k-1, odd_cc = m_J = 0), so it stays
         (correctly) uncharged -- it binds.

(GR-41)  THE PARITY FLOOR.  Let tau = [l even] in GF(2)^branches and
         Phi = tau + Cut(G°).  (i) Every admissible colouring's minority
         map m has mu(m) := sum_v e_{m(v)} in Phi (that IS (GR-37)(i)'s
         solvability), and wt(mu(m)) == n_hub (mod 2).  (ii) For every
         perfect matching M, mu(M) = 0, so the deviation distance
         satisfies dist(m, M) >= wt(mu(m)) / 2 >= phi* / 2 where
         phi* = min weight of a parity-matched Phi element.  (iii) Hence
         NO admissible -- a fortiori no fully-good -- colouring exists
         within ceil(phi*/2) - 1 deviations of ANY perfect matching:
         the deviation count of (GR-37)'s selection is bounded BELOW by
         a colouring-free shape invariant.  Two lines from (GR-37).
         MEASURED LAYER SPLIT on top of it (--bound): the floor is one
         of THREE stacked layers -- parity/shift-metric (d_par), the
         odd-branch BALANCE rider (d_adm), fully-goodness (d_fg) -- and
         (i) d_fg = d_adm at EVERY shape measured (the deviation cost of
         the selection is entirely about reaching ADMISSIBILITY, never
         about avoiding binding chunks), while (ii) the W3 stick lives
         in the BALANCE layer, not the parity one (phi*(W3) = 2:
         parity-consistent maps exist at d <= 2 and every c-solution
         fails balance).

(GR-42)  THE REFUTATION FAMILY.  The pentagon necklace NK(m) (m even):
         m pentagons P_i on hubs 5i+j, links (i,0)-(i+1,2) and
         (i,1)-(i+1,3), chords (i,4)-(i+m/2,4); all lengths 2 except
         three length-4 branches (excess 6, all EVEN).  (i) HABITAT, by
         the lemma: a cubic 3-edge-connected cyclically-4-edge-connected
         multigraph with Sum(l-2) = 6, l in [2,5], and every hub star
         carrying excess <= 5 satisfies (GR-25)(i) -- every legal proper
         W' has boundary >= 4 or is the complement of a singleton, whose
         interior keeps >= 1 excess.  All four lemma hypotheses are
         polynomial-time per member; the lemma is cross-validated against
         the exhaustive 2^n `cflank.cubic_habitat` at NK(2), and its
         load-bearing clause (cyclic 4-edge-connectivity) carries an F13
         adversarial witness (the all-l2+matching-excess triangular
         prism, which passes every other clause and must be REJECTED).
         (ii) phi(NK(m)) >= m: all lengths even makes Phi the set of
         internal-edge indicators of bipartitions, and the m pentagons
         are edge-disjoint odd cycles, each needing an internal edge; at
         m == 2 (mod 4) the explicit F = {pentagon edges (3,4)} is a
         Phi element of weight m, so phi = phi* = m exactly.  (iii) A
         fully-good colouring EXISTS at every member checked
         (rank-certified, both blocks, both matrices) -- constructed
         through mu(m) = chi_F pointer/pairing realizations, so NOTHING
         here is a flank.  By (GR-41), d(NK(m)) >= m/2 -> infinity:
         THERE IS NO SHAPE-FREE DEVIATION BOUND.  This refutes the
         bounded-deviation FORM (E1 clause (iii): a form-refutation,
         never per-shape (GR-15)); the anchor (GR-37) and the honest
         successor -- bound d by the parity invariant, d <= phi*/2 + c,
         measured c = 0 everywhere probed -- are stated in the draft.

WHAT EACH MODE TESTS, one sentence each (F11 -- doubly binding: the
direction's claims are case-list / exhaustiveness claims; the per-sentence
table is in the draft's Verification section).

--charge (GR-40) asserted per (colouring, chunk) over every admissible
         colouring of a seeded pool subsample, in both blocks, on top of
         the (GR-36) bound; the dart-supply case list certified
         exhaustively (l in 2..5, both bits); the corner-count identity
         #corners = 2(k-1) and the cc-count identity asserted per chunk;
         W3M pinned as the tightness witness (corner bound 1 vs (GR-36)
         bound 0); the binding-capable family recounted under
         (GR-36) AND the corner condition (what (b) buys the hunt).

--bound  (GR-41) asserted per sampled admissible colouring (coset
         membership via fundamental cycles, weight parity, the distance
         bound against EVERY perfect matching); W3 priced FIRST: phi* is
         computed, the d <= 2 stick RE-DERIVED and LAYERED at the
         admissible level (exhaustive over all matchings x deviations,
         with per-layer counts), and a fully-good colouring exhibited at
         d = 3; the witnesses and ladders priced; the pool subsample
         measured as the LAYER TRIPLE (d_par, d_adm, d_fg) against the
         floor -- the growth-law data.

--adv    (GR-42): NK(2) cross-validated against the exhaustive habitat
         oracle and priced exactly; NK(6)/NK(8)/NK(10) certified habitat
         by the lemma (each clause machine-checked per member), their
         pentagon packing and F-upper certified, constructed admissible
         colourings asserted, fully-good colourings rank-certified (the
         E1 guard: every member keeps one), and the floor d >= m/2
         reported -- the d >= 4 and d >= 5 witnesses the MISS
         deliverables name.

--hunt   the (b)-ARMED control (the corner charge lands in --charge, so
         the re-arm condition holds): ONE targeted, capped, disclosed
         construction hunt for a realized-binding FULLY-HOT hub at
         n_hub in {8, 10} -- central-hub three-cycle frames whose three
         dart-pair cycles each pass BOTH charges, completed to habitat,
         then scanned exactly over all admissible colourings.

Exact throughout (integers; rank only through gridcol.block_generic_zero's
GF(p) lower bound with exact-Q recheck through BOTH matrices, README §4
convention 2).  Rngs seeded per mode, seeds printed; no `set` printed;
nothing samples a placement, so `repin.star_generic` gates nothing here
(§(K-clos) (AC-9)).  Wall-clock `[Ns]` annotations are inherently
non-deterministic; every other byte is seed-stable.
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
from closure import colourings                                         # noqa: E402
from gridcol import branch_decomp, subdivide                           # noqa: E402
from cflank import admissible, cubic_habitat, hub_model                # noqa: E402
from gcap import branch_stats, pool_specs                              # noqa: E402
from gunif import WITNESSES, spec_to_hm_index, wit_colouring           # noqa: E402
from gexist import (incidence, chunk_shape, fully_good_rank,           # noqa: E402
                    ladder_specs)
from gorient import (jdata, chunk_fast, fast_defects, darts_at,        # noqa: E402
                     cm_solve, cm_colouring, odd_balance,
                     perfect_matchings, m_of_matching, prep_shape,
                     fully_good_scan)

R_SEED = 20260814


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a §1 primitive (checked against the README index and
# the Divergences table).  `cdata` is the (GR-40) bookkeeping on top of
# gorient.jdata; `phi_of` / `mu_of` / `in_coset` are the (GR-41) parity
# objects; `nk_specs` / `realize_mu` / `habitat_by_lemma` are the (GR-42)
# construction and its polynomial habitat certificate.


def cdata(hm, inc, ks):
    """(GR-40) colouring-independent corner data of a connected branch
    subset with S-degrees in {2, 3}: interiors z, corners, k, m_J,
    odd_cc, w45, the (GR-36) bound and the corner bound; asserts the
    corner-count and cc-count identities of the proof."""
    ends, lens = hm['ends'], hm['lens']
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    assert all(d in (2, 3) for d in deg.values())
    ints = {v for v, d in deg.items() if d == 2}
    corners = {v for v, d in deg.items() if d == 3}
    kk = len(ks) - len(deg) + 1
    assert kk >= 1
    assert len(corners) == 2 * (kk - 1), \
        "(GR-40) corner-count identity refuted: #corners != 2(k-1)"
    m_j = odd_cc = n_cc = n_ci = 0
    for k in ks:
        u, w = ends[k]
        ci = (u in ints) + (w in ints)
        if ci == 2:
            m_j += 1
        elif ci == 1:
            n_ci += 1
        else:
            n_cc += 1
            if lens[k] % 2 == 1:
                odd_cc += 1
    assert n_cc == 3 * (kk - 1) - len(ints) + m_j, \
        "(GR-40) cc-count identity refuted"
    assert n_ci == 2 * len(ints) - 2 * m_j
    w45 = sum(1 for k in ks if lens[k] >= 4)
    term = len(ints) + odd_cc - m_j - (kk - 1)
    cbound = w45 + max(0, (term + 1) // 2)
    jd = jdata(hm, inc, ks)
    assert jd['w45'] == w45 and len(jd['jedges']) == m_j
    return dict(z=len(ints), k=kk, m_j=m_j, odd_cc=odd_cc, w45=w45,
                gr36=jd['bound'], corner=cbound,
                cond=(term <= 2 * (2 - w45)))


def dart_table():
    """The (GR-40) supply case list, certified exhaustively: for every
    length l in [2, 5] and both alternation bits, the two end darts of a
    branch satisfy (even => ends differ, exactly one A-end) and
    (odd => ends equal = the branch majority)."""
    for L in range(2, 6):
        for c0 in (0, 1):                    # first edge colour, 0 = A
            cend = c0 ^ ((L - 1) % 2)        # last edge colour
            a_edges = sum(1 for j in range(L) if (c0 ^ (j % 2)) == 0)
            if L % 2 == 0:
                assert c0 != cend and (c0 == 0) + (cend == 0) == 1, \
                    "even-branch dart case refuted"
                assert a_edges == L // 2
            else:
                assert c0 == cend, "odd-branch dart case refuted"
                maj_a = a_edges > L - a_edges
                assert (c0 == 0) == maj_a, \
                    "odd-branch majority-dart case refuted"
    return 8


def even_vec(specs):
    return [1 if L % 2 == 0 else 0 for (_u, _w, L) in specs]


def cut_of(specs, n, mask):
    """The cut vector of the hub subset `mask` (bit i = hub i in U)."""
    return [1 if ((mask >> u & 1) != (mask >> w & 1)) else 0
            for (u, w, _L) in specs]


def phi_of(specs, n):
    """(phi, phi*) of the shape: the min weight over the coset
    [l even] + Cut(G°), and its parity-matched (wt == n mod 2)
    refinement.  2^n enumeration -- callers keep n <= 20."""
    assert n <= 20
    tau = even_vec(specs)
    best = best_p = None
    for mask in range(1 << (n - 1)):         # cuts come in complement pairs
        cut = cut_of(specs, n, mask)
        w = sum(t ^ c for t, c in zip(tau, cut))
        if best is None or w < best:
            best = w
        if w % 2 == n % 2 and (best_p is None or w < best_p):
            best_p = w
    return best, best_p


def mu_of(specs, m):
    """mu(m): per-branch parity of pointing minority-dart ends."""
    mu = [0] * len(specs)
    for v, (i, _e) in m.items():
        mu[i] ^= 1
    return mu


def fundamental_cycles(specs, n):
    """One GF(2) cycle basis of the hub multigraph, as branch index
    lists (spanning tree + one fundamental cycle per non-tree branch)."""
    adj = {}
    for i, (u, w, _L) in enumerate(specs):
        adj.setdefault(u, []).append((w, i))
        adj.setdefault(w, []).append((u, i))
    parent = {0: None}
    order = [0]
    st = [0]
    while st:
        v = st.pop()
        for (u, i) in adj[v]:
            if u not in parent:
                parent[u] = (v, i)
                order.append(u)
                st.append(u)
    assert len(parent) == n, "hub graph disconnected"
    tree = {parent[v][1] for v in parent if parent[v] is not None}
    cycles = []
    depth = {0: 0}
    for v in order[1:]:
        depth[v] = depth[parent[v][0]] + 1
    for i, (u, w, _L) in enumerate(specs):
        if i in tree:
            continue
        cyc = {i}
        a, b = u, w
        while a != b:
            if depth[a] < depth[b]:
                a, b = b, a
            pa, pi = parent[a]
            cyc ^= {pi}
            a = pa
        cycles.append(sorted(cyc))
    return cycles


def in_coset(specs, n, x, cycles):
    """x in [l even] + Cut(G°), tested by orthogonality of x + [l even]
    to every fundamental cycle."""
    tau = even_vec(specs)
    y = [a ^ b for a, b in zip(x, tau)]
    return all(sum(y[i] for i in cyc) % 2 == 0 for cyc in cycles)


def min_dev(specs, edges, allverts, hm, tec_cf, lens, mats, dmax):
    """Exact minimum deviation distances over ALL the given matchings, as
    the LAYER TRIPLE (d_par, d_adm, d_fg): the least d at which some
    (M, d deviations) minority map is parity-consistent (cm_solve
    succeeds) / extends to an admissible colouring (+ balance) / to a
    fully-good one (exact full-chunk scan); each None past dmax."""
    dinc = darts_at(specs)
    hubs = sorted(dinc)
    d_par = d_adm = d_fg = None
    for nd in range(dmax + 1):
        for mat in mats:
            base = m_of_matching(specs, mat)
            for vs in combinations(hubs, nd):
                lists = [[d for d in dinc[v] if d != base[v]] for v in vs]
                idx = [0] * nd
                while True:
                    m = dict(base)
                    for j, v in enumerate(vs):
                        m[v] = lists[j][idx[j]]
                    sols = cm_solve(specs, m)
                    if sols is not None:
                        if d_par is None:
                            d_par = nd
                        for c in sols:
                            na, nb = odd_balance(specs, m, c)
                            if na != nb:
                                continue
                            col = cm_colouring(specs, m, c)
                            if not admissible(edges, allverts, hm, col):
                                continue
                            if d_adm is None:
                                d_adm = nd
                            if d_fg is None:
                                stats = branch_stats(hm, col, 'A')
                                if fully_good_scan(hm, None, tec_cf, lens,
                                                   stats):
                                    d_fg = nd
                        if d_fg is not None:
                            return d_par, d_adm, d_fg
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
    return d_par, d_adm, d_fg


# --------------------------------------------- the necklace family ----------

def nk_specs(m):
    """NK(m), m even: m pentagons + links + chords, three length-4
    branches on the first three chords (or the chord + first two links
    at m = 2).  Returns (specs, pentagon branch-index lists, F = the
    per-pentagon (3,4)-edge indices, chord indices)."""
    assert m % 2 == 0 and m >= 2

    def V(i, j):
        return 5 * (i % m) + j

    specs, pent = [], []
    for i in range(m):
        ids = []
        for j in range(5):
            ids.append(len(specs))
            specs.append([V(i, j), V(i, (j + 1) % 5), 2])
        pent.append(ids)
    links = []
    for i in range(m):
        links.append(len(specs))
        specs.append([V(i, 0), V((i + 1) % m, 2), 2])
        links.append(len(specs))
        specs.append([V(i, 1), V((i + 1) % m, 3), 2])
    chords = []
    for i in range(m // 2):
        chords.append(len(specs))
        specs.append([V(i, 4), V(i + m // 2, 4), 2])
    exc_on = chords[:3] if len(chords) >= 3 else chords + links[:2]
    for k in exc_on:
        specs[k][2] = 4
    F = [pent[i][3] for i in range(m)]
    return [tuple(s) for s in specs], pent, F, chords


def realize_mu(specs, n, F, rng, tries=400):
    """A minority map m with mu(m) = chi_F: one pointer end per F-branch,
    every other hub paired with a neighbour along a shared branch (two
    pointers cancel).  Randomized greedy with retries; asserts the
    realization exactly."""
    inc = darts_at(specs)
    for _t in range(tries):
        m = {}
        used = set()
        ok = True
        for i in sorted(F):
            (u, w, _L) = specs[i]
            free = [v for v in (u, w) if v not in used]
            if not free:
                ok = False
                break
            v = free[0] if len(free) == 1 or rng.random() < 0.5 else free[1]
            m[v] = (i, 0 if v == specs[i][0] else 1)
            used.add(v)
        if not ok:
            continue
        rest = [v for v in range(n) if v not in used]
        rng.shuffle(rest)
        restset = set(rest)
        for v in list(rest):
            if v not in restset:
                continue
            cands = [(i, e) for (i, e) in inc[v]
                     if (specs[i][1] if e == 0 else specs[i][0]) in restset
                     and (specs[i][1] if e == 0 else specs[i][0]) != v]
            if not cands:
                ok = False
                break
            (i, e) = cands[rng.randrange(len(cands))]
            u = specs[i][1] if e == 0 else specs[i][0]
            m[v] = (i, e)
            m[u] = (i, 1 - e)
            restset.discard(v)
            restset.discard(u)
        if not ok or restset:
            continue
        mu = mu_of(specs, m)
        assert mu == [1 if i in set(F) else 0 for i in range(len(specs))], \
            "realize_mu produced the wrong coset element"
        return m
    return None


def habitat_by_lemma(n, hedges, lens, verbose=False):
    """The (GR-42)(i) polynomial habitat certificate: cubic, loop-free,
    l in [2,5] with total excess 6, every hub star's excess <= 5,
    3-edge-connected, cyclically 4-edge-connected.  The LEMMA (proof in
    the draft) turns these into (GR-25)(i); cross-validated against the
    exhaustive `cflank.cubic_habitat` at NK(2) and n <= 6 pool shapes,
    with the prism as the F13 must-reject witness.  Returns (ok, why)."""
    M = len(hedges)
    exc = [L - 2 for L in lens]
    if any(L < 2 or L > 5 for L in lens):
        return False, 'length'
    if sum(exc) != 6:
        return False, 'excess'
    deg = {v: 0 for v in range(n)}
    star = {v: 0 for v in range(n)}
    for k, (u, w) in enumerate(hedges):
        if u == w:
            return False, 'loop'
        deg[u] += 1
        deg[w] += 1
        star[u] += exc[k]
        star[w] += exc[k]
    if any(d != 3 for d in deg.values()):
        return False, 'not-cubic'
    if any(s > 5 for s in star.values()):
        return False, 'star-excess'

    def comps_without(drop):
        adj = {v: [] for v in range(n)}
        for k, (u, w) in enumerate(hedges):
            if k in drop:
                continue
            adj[u].append((w, k))
            adj[w].append((u, k))
        seen = {}
        cid = 0
        for v0 in range(n):
            if v0 in seen:
                continue
            st = [v0]
            seen[v0] = cid
            while st:
                v = st.pop()
                for (u, _k) in adj[v]:
                    if u not in seen:
                        seen[u] = cid
                        st.append(u)
            cid += 1
        return seen, cid, adj

    for k1 in range(M):                       # 1- and 2-cuts: none
        for k2 in range(k1, M):
            _s, cid, _a = comps_without({k1, k2})
            if cid > 1:
                return False, '2-cut'
    for ks in combinations(range(M), 3):      # 3-cuts: never cycle/cycle
        seen, cid, adj = comps_without(set(ks))
        if cid <= 1:
            continue
        cyc_sides = 0
        for c in range(cid):
            vs = [v for v, cc in seen.items() if cc == c]
            ne = sum(1 for k, (u, w) in enumerate(hedges)
                     if k not in ks and seen[u] == c and seen[w] == c)
            if ne >= len(vs):                 # a component with a cycle
                cyc_sides += 1
        if cyc_sides >= 2:
            return False, 'cyclic-3-cut'
    return True, 'ok'


def light_hm(edges):
    """The (hubs, branches, ends, lens) sub-dict of `cflank.hub_model`,
    WITHOUT its simple-cycle enumeration (exponential in the cyclomatic
    number, prohibitive at NK(8)+): exactly what `cflank.admissible` and
    `gexist.fully_good_rank` consume.  Local device; not a §1 shadow."""
    hubs, branches = branch_decomp(edges)
    assert branches is not None
    return dict(hubs=hubs, branches=branches,
                ends=[(u, w) for (u, w, _p) in branches],
                lens=[len(p) for (_u, _w, p) in branches])


PRISM_SPECS = [(0, 1, 2), (1, 2, 2), (2, 0, 2),
               (3, 4, 2), (4, 5, 2), (5, 3, 2),
               (0, 3, 4), (1, 4, 4), (2, 5, 4)]


# ------------------------------------------- [GDV-1] --charge: (GR-40) ------

def leg_charge():
    """[GDV-1] the corner charge: case list, pool certification, the W3M
    tightness pin, the family recount."""
    t0 = time.time()
    print(f"[GDV-1] (GR-40) the corner charge (seed {R_SEED + 1})")
    rng = random.Random(R_SEED + 1)
    ncases = dart_table()
    print(f"  supply case list certified exhaustively: {ncases} (length, "
          f"bit) branch cases -- even: ends differ, one A-end; odd: ends "
          f"equal = majority")

    picked = pairs = beats = eq_corner = 0
    sum_viol = sum_pairs = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.025:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens_s):
            continue
        picked += 1
        edges, allverts, hm, inc, tec, tec_cf, allks = prep_shape(specs)
        lens = hm['lens']
        ccache = [cdata(hm, inc, ks) for (ks, _kk) in tec]
        cols, odd = colourings(edges, cap=1 << 14)
        assert not odd and cols is not None
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            stats = branch_stats(hm, col, 'A')
            acnt, du, dw = stats
            for ((cf, _imp), cd) in zip(tec_cf, ccache):
                dA, dB = fast_defects(cf, lens, acnt, du, dw)
                assert dA >= cd['corner'] and dB >= cd['corner'], \
                    "(GR-40) corner charge refuted at a pool chunk"
                pairs += 1
                if cd['corner'] > cd['gr36']:
                    beats += 1
                if dA == cd['corner'] or dB == cd['corner']:
                    eq_corner += 1
                # the SUM form (measured only, no claim): does
                # w45 + Sum ceil(m_i/2) + corner term ever exceed defect?
                s = cd['gr36'] + (cd['corner'] - cd['w45'])
                sum_pairs += 1
                if dA < s or dB < s:
                    sum_viol += 1
    print(f"  pool subsample: {picked} shapes; corner charge asserted in "
          f"BOTH blocks at {pairs} (colouring, chunk) pairs on top of the "
          f"(GR-36) bound; corner bound STRICTLY beats (GR-36) at {beats} "
          f"pairs; attained with equality at {eq_corner}")
    print(f"  the naive SUM of the two charges (measured, NOT claimed): "
          f"violated at {sum_viol} of {sum_pairs} pairs -- "
          + ("the sum form is FALSE; max is the theorem"
             if sum_viol else "no violation seen (still not claimed)"))

    # the W3M tightness pin + the W5 boundary
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    for tag, want_c, want_g in (('W3M', 1, 0), ('W5', 0, 0)):
        (name, n2, specs2, first2, S_idx2, _e) = by_tag[tag]
        edges2 = subdivide(specs2)
        allverts2 = sorted(verts_of(edges2), key=str)
        hm2 = hub_model(edges2)
        inc2 = incidence(hm2)
        s2h = spec_to_hm_index(specs2, hm2)
        S_hm = tuple(sorted(s2h[i] for i in S_idx2))
        cd = cdata(hm2, inc2, S_hm)
        assert cd['corner'] == want_c and cd['gr36'] == want_g, \
            f"{tag} charge data changed"
        col2 = wit_colouring(specs2, first2)
        stats2 = branch_stats(hm2, col2, 'A')
        cf2 = chunk_fast(hm2, inc2, S_hm)
        dA, dB = fast_defects(cf2, hm2['lens'], *stats2)
        print(f"  {tag}: S has z={cd['z']}, k={cd['k']}, m_J={cd['m_j']}, "
              f"odd_cc={cd['odd_cc']}, w45={cd['w45']}; corner bound "
              f"{cd['corner']}, (GR-36) bound {cd['gr36']}; witness "
              f"defects (A,B) = ({dA},{dB})")
        if tag == 'W3M':
            assert dA == cd['corner'] == 1, "W3M tightness pin broken"
            print("    -> TIGHT at the minimal witness: the corner charge "
                  "prices W3M's S exactly where (GR-36) prices it 0 "
                  "(the pinned counter-fact)")
        else:
            assert cd['z'] == cd['k'] - 1
            print("    -> the W5 scaling family sits at the exact zero of "
                  "the bound (z = k-1, m_J = odd_cc = 0): charged nothing, "
                  "correctly -- it binds; what the charge caps is how far "
                  "ABOVE z = k-1 a corner-separated binding chunk can go "
                  "(corner condition: z + odd_cc - m_J <= (k-1) + 4 - 2w45)")

    # the family recount: binding-capable under (GR-36) alone vs BOTH
    picked2 = d36 = dboth = 0
    hub36_2 = hub36_3 = hubb_2 = hubb_3 = 0
    for n2, specs2 in pool_specs():
        if rng.random() >= 0.04:
            continue
        hedges = [(u, w) for (u, w, _L) in specs2]
        lens_s = [L for (_u, _w, L) in specs2]
        if not cubic_habitat(n2, hedges, lens_s):
            continue
        picked2 += 1
        edges2, allverts2, hm2, inc2, tec2, _cf2, allks2 = prep_shape(specs2)
        h36 = {v: set() for v in hm2['hubs']}
        hb = {v: set() for v in hm2['hubs']}
        for (ks, _kk) in tec2:
            if ks == allks2:
                continue
            cs = chunk_shape(hm2, inc2, ks)
            if cs['improper']:
                continue
            cd = cdata(hm2, inc2, ks)
            if cd['gr36'] <= 2:
                for (v, k) in cs['exits']:
                    h36[v].add(k)
                if cd['corner'] <= 2:
                    for (v, k) in cs['exits']:
                        hb[v].add(k)
        d36 += sum(len(s) for s in h36.values())
        dboth += sum(len(s) for s in hb.values())
        for v in hm2['hubs']:
            if len(h36[v]) >= 2:
                hub36_2 += 1
            if len(h36[v]) == 3:
                hub36_3 += 1
            if len(hb[v]) >= 2:
                hubb_2 += 1
            if len(hb[v]) == 3:
                hubb_3 += 1
    print(f"  family recount ({picked2} pool shapes, fresh seeded "
          f"subsample): capable exit darts under (GR-36) alone: {d36}, "
          f"under BOTH charges: {dboth}; hubs >= 2 capable-hot: "
          f"{hub36_2} -> {hubb_2}; FULLY capable-hot: {hub36_3} -> "
          f"{hubb_3} -- the corner condition is what (b) buys the hunt")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------- [GDV-2] --bound: (GR-41) -------

def leg_bound():
    """[GDV-2] the parity floor; W3 priced FIRST; witnesses, ladders,
    and the pool layer-split measurement."""
    t0 = time.time()
    print(f"[GDV-2] (GR-41) the parity floor (seed {R_SEED + 2})")
    rng = random.Random(R_SEED + 2)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}

    # ---- (a) W3 FIRST
    (name, n3, specs3, first3, S3, _e) = by_tag['W3']
    phi, phis = phi_of(specs3, n3)
    print(f"  W3 (n={n3}): phi = {phi}, phi* = {phis} -> floor "
          f"ceil(phi*/2) = {(phis + 1) // 2}")
    edges3 = subdivide(specs3)
    allverts3 = sorted(verts_of(edges3), key=str)
    hm3 = hub_model(edges3)
    mats3 = perfect_matchings(specs3)
    dinc3 = darts_at(specs3)
    hubs3 = sorted(dinc3)
    n_cand = n_par = n_bal = n_adm = 0
    for mat in mats3:
        base = m_of_matching(specs3, mat)
        for nd in range(0, 3):
            for vs in combinations(hubs3, nd):
                lists = [[d for d in dinc3[v] if d != base[v]] for v in vs]
                idx = [0] * nd
                while True:
                    m = dict(base)
                    for j, v in enumerate(vs):
                        m[v] = lists[j][idx[j]]
                    n_cand += 1
                    sols = cm_solve(specs3, m)
                    if sols is not None:
                        n_par += 1
                        for c in sols:
                            na, nb = odd_balance(specs3, m, c)
                            if na != nb:
                                continue
                            n_bal += 1
                            col = cm_colouring(specs3, m, c)
                            if admissible(edges3, allverts3, hm3, col):
                                n_adm += 1
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
    print(f"  W3 stick RE-DERIVED and LAYERED: over all {len(mats3)} "
          f"matchings x <= 2 deviations ({n_cand} minority maps): "
          f"parity-consistent {n_par}, of their c-solutions "
          f"balance-passing {n_bal}, admissible {n_adm}")
    assert n_adm == 0, "admissible colouring within 2 deviations at W3 " \
        "-- GORIENT's stick is wrong"
    if n_par > 0 and n_bal == 0:
        print("    -> so the W3 stick is NOT the parity layer (floor "
              f"{(phis + 1) // 2} only): parity-consistent maps exist at "
              "d <= 2, and every one of their c-solutions fails the "
              "ODD-BRANCH BALANCE rider -- the stick lives in the "
              "balance layer")
    elif n_par == 0:
        print("    -> the stick is the parity/shift-metric layer: no "
              "parity-consistent map at d <= 2 at all")
    else:
        print("    -> the stick is the admissibility layer past balance "
              "-- investigate")
    # a fully-good colouring at d = 3 (rank-certified; caps disclosed)
    got = None
    ranked = 0
    for mat in mats3:
        base = m_of_matching(specs3, mat)
        for vs in combinations(hubs3, 3):
            lists = [[d for d in dinc3[v] if d != base[v]] for v in vs]
            idx = [0] * 3
            while True:
                m = dict(base)
                for j, v in enumerate(vs):
                    m[v] = lists[j][idx[j]]
                sols = cm_solve(specs3, m)
                if sols is not None:
                    for c in sols:
                        na, nb = odd_balance(specs3, m, c)
                        if na != nb:
                            continue
                        col = cm_colouring(specs3, m, c)
                        if not admissible(edges3, allverts3, hm3, col):
                            continue
                        if ranked >= 40:
                            continue
                        ranked += 1
                        if fully_good_rank(edges3, allverts3, hm3, col, rng):
                            got = sorted(mat)
                            break
                if got:
                    break
                j = 2
                while j >= 0:
                    idx[j] += 1
                    if idx[j] < len(lists[j]):
                        break
                    idx[j] = 0
                    j -= 1
                if j < 0:
                    break
            if got:
                break
        if got:
            break
    assert got is not None, "no fully-good colouring found at d = 3 at W3 " \
        f"(rank cap 40; {ranked} tested)"
    print(f"  W3: fully good (rank-certified, both blocks, both matrices) "
          f"AT d = 3, matching branches {got} ({ranked} rank tests, cap "
          f"40) -- so d_adm(W3) = d_fg(W3) = 3 against a parity floor of "
          f"{(phis + 1) // 2}: the W3 gap is the BALANCE layer's")

    # ---- (b) the other witnesses and the ladders
    for tag in ('W3M', 'W4', 'W5'):
        (nm, n2, specs2, _f, _S, _e) = by_tag[tag]
        phi2, phis2 = phi_of(specs2, n2)
        assert (phis2 + 1) // 2 <= 2, \
            f"{tag}: floor exceeds the measured d = 2"
        print(f"  {tag} (n={n2}): phi* = {phis2} -> floor "
              f"{(phis2 + 1) // 2} (consistent with the measured d = 2)")
    for ml in (5, 6, 7, 8):
        specs2 = ladder_specs(ml, {0: 2, 1: 2, 2: 2})
        phi2, phis2 = phi_of(specs2, 2 * ml)
        want = 0 if ml % 2 == 0 else 2
        assert phi2 == want, f"CL{ml}: phi != {want}"
        msg = ('bipartite, rung rule free' if ml % 2 == 0
               else 'odd ladder: non-bipartite, the parity floor is 1')
        print(f"  CL{ml}: phi = {phi2}, phi* = {phis2} -> floor "
              f"{(phis2 + 1) // 2} ({msg})")

    # ---- (c) the pool layer split: phi* vs exact d_par / d_adm / d_fg
    picked = 0
    floor_hist = {}
    gap_par = {}
    gap_adm = {}
    gap_fg = {}
    cert_cols = cert_pms = 0
    for n, specs in pool_specs():
        if rng.random() >= 0.025:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens_s):
            continue
        picked += 1
        edges, allverts, hm, inc, tec, tec_cf, allks = prep_shape(specs)
        lens = hm['lens']
        phi2, phis2 = phi_of(specs, n)
        fl = (phis2 + 1) // 2
        floor_hist[fl] = floor_hist.get(fl, 0) + 1
        mats = perfect_matchings(specs)
        d_par, d_adm, d_fg = min_dev(specs, edges, allverts, hm, tec_cf,
                                     lens, mats, 3)
        assert d_adm is not None and d_fg is not None, \
            "pool shape with no fully-good selection within 3 deviations " \
            "-- a NEW stick beyond W3's depth; investigate"
        assert d_par >= fl, "(GR-41) floor refuted: parity below phi*/2"
        gap_par[d_par - fl] = gap_par.get(d_par - fl, 0) + 1
        gap_adm[d_adm - d_par] = gap_adm.get(d_adm - d_par, 0) + 1
        gap_fg[d_fg - d_adm] = gap_fg.get(d_fg - d_adm, 0) + 1
        # per-colouring certification of the floor's two pieces, on a
        # seeded sub-subsample of admissible colourings
        if rng.random() < 0.25:
            cycles = fundamental_cycles(specs, n)
            s2h = None
            try:
                s2h = spec_to_hm_index(specs, hm)
            except AssertionError:
                pass
            if s2h is not None:
                cols, odd = colourings(edges, cap=1 << 14)
                assert not odd and cols is not None
                from gexist import hub_minority
                for col in cols:
                    if not admissible(edges, allverts, hm, col):
                        continue
                    if rng.random() >= 0.2:
                        continue
                    stats = branch_stats(hm, col, 'A')
                    mino = hub_minority(hm, stats)
                    m = {}
                    h2i = {}
                    for i, k in enumerate(s2h):
                        (u, w, _L) = specs[i]
                        h2i.setdefault(('h', u), {})[k] = (i, 0)
                        h2i.setdefault(('h', w), {})[k] = (i, 1)
                    for h, (_maj, mink) in mino.items():
                        m[h[1]] = h2i[h][mink]
                    mu = mu_of(specs, m)
                    wt = sum(mu)
                    assert in_coset(specs, n, mu, cycles), \
                        "(GR-41)(i) refuted: admissible mu outside coset"
                    assert wt % 2 == n % 2, "(GR-41) weight parity refuted"
                    assert wt >= phis2, "(GR-41) phi* minimality refuted"
                    cert_cols += 1
                    for mat in mats:
                        dist = sum(1 for v in m
                                   if m[v][0] not in mat)
                        assert 2 * dist >= wt, \
                            "(GR-41)(ii) refuted: dist < wt(mu)/2"
                        cert_pms += 1
    print(f"  pool subsample: {picked} shapes; floor histogram "
          f"{sorted(floor_hist.items())}; layer gaps -- d_par - floor: "
          f"{sorted(gap_par.items())}, d_adm - d_par (balance): "
          f"{sorted(gap_adm.items())}, d_fg - d_adm (fully-good): "
          f"{sorted(gap_fg.items())}")
    print(f"  (GR-41) certified per colouring: coset membership + weight "
          f"parity + phi* minimality at {cert_cols} admissible colourings; "
          f"dist >= wt/2 at {cert_pms} (colouring, matching) pairs")
    print(f"  [{time.time() - t0:.0f}s]")


# --------------------------------------------- [GDV-3] --adv: (GR-42) -------

def leg_adv():
    """[GDV-3] the necklace family: the habitat lemma with its F13
    witness, NK(2) exact, NK(6)/NK(8)/NK(10) certified, the refutation."""
    t0 = time.time()
    print(f"[GDV-3] (GR-42) the necklace family (seed {R_SEED + 3})")
    rng = random.Random(R_SEED + 3)

    # ---- (a) the F13 witness for the lemma checker
    n_p = 6
    hedges_p = [(u, w) for (u, w, _L) in PRISM_SPECS]
    lens_p = [L for (_u, _w, L) in PRISM_SPECS]
    ok, why = habitat_by_lemma(n_p, hedges_p, lens_p)
    assert not ok and why == 'cyclic-3-cut', \
        "lemma checker fails to reject the prism"
    assert not cubic_habitat(n_p, hedges_p, lens_p)
    print("  F13 witness: the all-l2 + matching-excess triangular prism is "
          "REJECTED by the lemma checker for exactly its cyclic 3-cut "
          "(each triangle), agreeing with the exhaustive (GR-25) oracle; "
          "pinned counter-fact: it passes cubic + 3ec + star-excess, so "
          "the cyclic-4-ec clause is the load-bearing one")

    # ---- (b) cross-validation of the lemma on the n <= 6 pool: the lemma
    #      is SUFFICIENT, so lemma-true must imply habitat-true (one
    #      direction; the pool is where the exhaustive oracle is cheap)
    rngx = random.Random(R_SEED + 33)
    nboth = nlem = 0
    for n, specs in pool_specs():
        if rngx.random() >= 0.01:
            continue
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        ok, _why = habitat_by_lemma(n, hedges, lens_s)
        if ok:
            nlem += 1
            assert cubic_habitat(n, hedges, lens_s), \
                "lemma-true but (GR-25)-false: the lemma is REFUTED"
            nboth += 1
    print(f"  lemma sufficiency control on a pool subsample: {nlem} "
          f"lemma-true shapes, {nboth} confirmed habitat by the "
          f"exhaustive oracle (0 disagreements)")

    # ---- (c) the members
    for m in (2, 6, 8, 10):
        specs, pent, F, chords = nk_specs(m)
        n = 5 * m
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        assert len(specs) == 3 * n // 2
        assert sum(L - 2 for L in lens_s) == 6
        assert all(L % 2 == 0 for L in lens_s), "NK must be all-even"
        ok, why = habitat_by_lemma(n, hedges, lens_s)
        assert ok, f"NK({m}) fails the lemma checker: {why}"
        if n <= 10:
            assert cubic_habitat(n, hedges, lens_s), \
                "NK(2): lemma-true but the exhaustive oracle disagrees"
        # the pentagon packing: m edge-disjoint odd cycles => phi >= m
        seenb = set()
        for ids in pent:
            assert len(ids) == 5 and all(i not in seenb for i in ids)
            seenb |= set(ids)
            vs = [specs[i][0] for i in ids]
            assert len(set(vs)) == 5, "pentagon is not a 5-cycle"
        # the F upper bound at m == 2 (mod 4): NK - F bipartite, F internal
        exact = (m % 4 == 2)
        if exact:
            colr = {}
            adj = {v: [] for v in range(n)}
            for k, (u, w) in enumerate(hedges):
                if k in set(F):
                    continue
                adj[u].append(w)
                adj[w].append(u)
            colr[0] = 0
            st = [0]
            while st:
                v = st.pop()
                for u in adj[v]:
                    if u in colr:
                        assert colr[u] == 1 - colr[v], \
                            "NK - F not bipartite: the F upper bound fails"
                    else:
                        colr[u] = 1 - colr[v]
                        st.append(u)
            assert len(colr) == n
            for i in F:
                (u, w, _L) = specs[i]
                assert colr[u] == colr[w], "an F-edge crosses the bipartition"
        if n <= 20:
            phi, phis = phi_of(specs, n)
            assert phi == m and phis == m, \
                f"NK({m}): exact phi != m (packing/upper broken)"
            phimsg = f"phi = phi* = {m} (EXACT, 2^{n} enumeration)"
        elif exact:
            phimsg = f"phi = phi* = {m} (packing lower + explicit-F upper)"
        else:
            phimsg = f"phi >= {m} (packing lower; upper {m + m // 2} " \
                     f"by F + chords)"
        # constructed admissible colouring, mu = chi_F (m == 2 mod 4) or
        # chi_{F + chords} (m == 0 mod 4)
        Fx = F if exact else F + chords
        mm = realize_mu(specs, n, Fx, rng)
        assert mm is not None, f"NK({m}): mu realization starved"
        sols = cm_solve(specs, mm)
        assert sols is not None, \
            f"NK({m}): constructed coset element not solvable"
        edges = subdivide(specs)
        allverts = sorted(verts_of(edges), key=str)
        hm = light_hm(edges)
        col0 = cm_colouring(specs, mm, sols[0])
        assert admissible(edges, allverts, hm, col0), \
            f"NK({m}): constructed colouring not admissible"
        # fully-good existence (the E1 guard), rank-certified over
        # constructed coset realizations (cap disclosed)
        goodcol = None
        tested = 0
        for _t in range(30):
            m2 = realize_mu(specs, n, Fx, rng)
            if m2 is None:
                continue
            sols2 = cm_solve(specs, m2)
            if sols2 is None:
                continue
            for c2 in sols2:
                col = cm_colouring(specs, m2, c2)
                if not admissible(edges, allverts, hm, col):
                    continue
                tested += 1
                if fully_good_rank(edges, allverts, hm, col, rng):
                    goodcol = col
                    break
            if goodcol is not None:
                break
        assert goodcol is not None, \
            f"NK({m}): no fully-good colouring found in {tested} " \
            f"rank tests (cap 30 realizations) -- RAISE THE CAP before " \
            f"reading this as structure"
        print(f"  NK({m}) (n={n}, |branches|={len(specs)}): HABITAT by the "
              f"lemma (3ec + cyclic-4ec + star excess <= 5, all "
              f"machine-checked); {phimsg}; constructed admissible "
              f"colouring OK; fully good RANK-CERTIFIED ({tested} rank "
              f"tests) -- NOT a flank; floor: d >= {m // 2}"
              + (f" [exact oracle agrees]" if n <= 10 else ""))
        if m == 2:
            # exact pricing at the smallest member
            mats = perfect_matchings(specs)
            for mat in mats:
                assert cm_solve(specs, m_of_matching(specs, mat)) is None, \
                    "NK(2): some all-M rule is consistent -- phi > 0 broken"
            _e2, _a2, _hm2, inc2, tec2, tec_cf2, _ak2 = prep_shape(specs)
            d_par, d_adm, d_fg = min_dev(specs, edges, allverts, hm,
                                         tec_cf2, hm['lens'], mats, 2)
            print(f"    NK(2) exact: {len(mats)} matchings, all-M "
                  f"inconsistent at EVERY one (d = 0 empty, as the floor "
                  f"demands); exact d_par = {d_par}, d_adm = {d_adm}, "
                  f"d_fg = {d_fg} (floor {m // 2}) -- the floor is "
                  + ("ATTAINED" if d_fg == m // 2 else "not attained"))
    print("  => (GR-42): NK(m) is habitat with fully-good colourings for "
          "every even m, and every admissible colouring sits >= m/2 "
          "deviations from EVERY perfect matching ((GR-41) with "
          "phi >= m): d(NK(6)) >= 3, d(NK(8)) >= 4, d(NK(10)) >= 5, "
          "unbounded along the family -- THE SHAPE-FREE BOUNDED-DEVIATION "
          "FORM IS REFUTED (a form-refutation, E1 clause (iii); per-shape "
          "(GR-15) holds at every member, certified above)")
    print(f"  [{time.time() - t0:.0f}s]")


# ---------------------------------------------------- [GDV-4] --hunt --------

def leg_hunt():
    """[GDV-4] the (b)-armed control: ONE targeted, capped construction
    hunt for a realized-binding fully-hot hub at n_hub in {8, 10},
    frames = central hub with three dart-pair cycles passing BOTH
    charges."""
    t0 = time.time()
    print(f"[GDV-4] the (b)-armed realized-fully-hot hunt (seed "
          f"{R_SEED + 4})")
    rng = random.Random(R_SEED + 4)
    FRAME_CAP = 40000
    SCAN_CAP = 600
    tried = gated = scanned = 0
    found = None
    # frame: hub 0 with darts to x1=1, x2=2, x3=3 (lengths la, lb, lc);
    # cycle paths x_i - x_j through 0 or 1 extra hubs; extras completed
    # to cubic by matching stubs among themselves / to a tail hub.
    for la in (2, 3):
        for lb in (2, 3):
            for lc in (2, 3):
                for ex in range(2, 6):        # extra hubs 4 .. 3+ex-1...
                    nh = 4 + ex
                    # random capped generation of completions: branches
                    # among {1,2,3} u extras, all lengths 2..3, until
                    # cubic; then excess fix-up is implicit in lengths
                    for _attempt in range(1500):
                        tried += 1
                        if tried > FRAME_CAP:
                            break
                        specs = [(0, 1, la), (0, 2, lb), (0, 3, lc)]
                        deg = {v: 0 for v in range(nh)}
                        deg[0] = 3
                        for (_u, w, _L) in specs:
                            deg[w] += 1
                        okb = True
                        guard = 0
                        while okb and any(d < 3 for v, d in deg.items()):
                            guard += 1
                            if guard > 60:
                                okb = False
                                break
                            opens = [v for v in range(nh) if deg[v] < 3]
                            if len(opens) < 2:
                                okb = False
                                break
                            u = opens[rng.randrange(len(opens))]
                            wl = [v for v in opens if v != u]
                            w = wl[rng.randrange(len(wl))]
                            L = 2 + rng.randrange(2)
                            specs.append((u, w, L))
                            deg[u] += 1
                            deg[w] += 1
                        if not okb:
                            continue
                        exc = sum(L - 2 for (_u, _w, L) in specs)
                        if exc > 6:
                            continue
                        # top up excess to 6 on random branches (<= 5)
                        specs = [list(s) for s in specs]
                        guard = 0
                        while exc < 6 and guard < 200:
                            guard += 1
                            i = rng.randrange(len(specs))
                            if specs[i][2] < 5:
                                specs[i][2] += 1
                                exc += 1
                        if exc != 6:
                            continue
                        specs = [tuple(s) for s in specs]
                        hedges = [(u, w) for (u, w, _L) in specs]
                        lens_s = [L for (_u, _w, L) in specs]
                        if not cubic_habitat(nh, hedges, lens_s):
                            continue
                        gated += 1
                        if scanned >= SCAN_CAP:
                            continue
                        # arm: hub 0 must have all three darts exits of
                        # chunks passing BOTH charges (colouring-free)
                        edges, allverts, hm, inc, tec, tec_cf, allks = \
                            prep_shape(specs)
                        capable = {}
                        for (ks, _kk) in tec:
                            if ks == allks:
                                continue
                            cs = chunk_shape(hm, inc, ks)
                            if cs['improper']:
                                continue
                            cd = cdata(hm, inc, ks)
                            if cd['gr36'] <= 2 and cd['corner'] <= 2:
                                for (v, k) in cs['exits']:
                                    capable.setdefault(v, set()).add(k)
                        h0 = ('h', 0)
                        if len(capable.get(h0, ())) < 3:
                            continue
                        scanned += 1
                        cols, odd = colourings(edges, cap=1 << 14)
                        if odd or cols is None:
                            continue
                        lens = hm['lens']
                        realized = set()
                        for col in cols:
                            if not admissible(edges, allverts, hm, col):
                                continue
                            stats = branch_stats(hm, col, 'A')
                            acnt, du, dw = stats
                            for ((cf, imp), (ks, _kk)) in zip(tec_cf, tec):
                                if imp:
                                    continue
                                dA, dB = fast_defects(cf, lens, acnt,
                                                      du, dw)
                                if dA <= 2 or dB <= 2:
                                    cs = chunk_shape(hm, inc, ks)
                                    for (v, k) in cs['exits']:
                                        if v == h0:
                                            realized.add(k)
                            if len(realized) == 3:
                                break
                        if len(realized) == 3:
                            found = specs
                            break
                    if found or tried > FRAME_CAP:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    print(f"  frames tried: {tried} (cap {FRAME_CAP}), habitat-gated: "
          f"{gated}, armed (all three central darts exits of chunks "
          f"passing BOTH charges) and colouring-scanned: {scanned} "
          f"(cap {SCAN_CAP})")
    if found:
        print(f"  REALIZED-BINDING FULLY-HOT HUB FOUND: specs {found} -- "
              f"a SEED, not a flank (E1 clause (i)); route to the CSP "
              f"test at this seed per the spec's otherwise-clause")
    else:
        print("  NOT FOUND: no realized-binding fully-hot hub among the "
              "armed completions -- consistent with the exhaustive n <= 6 "
              "zero ((GR-38)'s census) and the (GR-39) kills; the "
              "corner-armed family is where a successor hunts next")
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------- validate -------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--charge', action='store_true')
    ap.add_argument('--bound', action='store_true')
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--hunt', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    ran = False
    if args.charge or args.validate:
        leg_charge()
        ran = True
    if args.bound or args.validate:
        leg_bound()
        ran = True
    if args.adv or args.validate:
        leg_adv()
        ran = True
    if args.hunt or args.validate:
        leg_hunt()
        ran = True
    if not ran:
        print(__doc__)
    else:
        print("gdev: ALL ASSERTS PASSED")


if __name__ == '__main__':
    main()
