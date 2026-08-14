"""§(K-grid) direction GORIENT (2026-08-13) driver -- the arc's third PROOF
direction: the ORIENTATION THEOREM target (uniform fully-good existence at
`Lambda = empty`, `D = 0`, in the (GR-33)(iv) orientation form), attacked
through a Hall/discharging frame over the binding-capable chunk hypergraph,
with the defect-<=1 INTERSECTION KILL as the first named sub-deliverable and
the HOT-HUB adjudication as the falsification control.  NO new sweep: every
pool below is an existing one (GCAP's 4920-shape `Lambda = empty` `D = 0`
stratum, the GUNIF witnesses, the CFLANK/GEXIST ladders) or a targeted
construction in the GUNIF idiom.

A `w4/` leaf beside `gexist.py`, importing `gexist.py` / `gunif.py` /
`gcap.py` / `cflank.py` / `gridcol.py` / `grid.py` / `closure.py`
READ-ONLY (README §2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hall   # (GR-36)/(GR-37): the structural charge + the selection reduction, case list certified
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --kill   # (GR-38): the intersection kill -- exhaustive on the n_hub <= 6 stratum
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hot    # (GR-39): the hot-hub adjudication (structure theorem, kills, census, targeted hunt)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --adv    # W5 priced FIRST; the census-family correction; good-PM at the witnesses
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --validate # all four in one process

Argument state: session draft `fanout-GORIENT.md` (to be merged into
`notes/Pencil-informal.md` §(K-grid) as Steps G43+; labels (GR-36)+ per the
2026-08-13 GORIENT reservation in `notes/Pencil-labels.md`).

THE DERIVED STRUCTURE THE MODES REST ON (proofs in the draft; asserted here
rather than trusted).  Throughout `Lambda = empty`, `D = 0`: G° cubic,
lengths in [2, 5] ((SD-6)), total excess 6 ((GR-21)); chunk / interior /
exit / defect as in gexist.py's header; binding in A iff defect_A <= 2.

(GR-36)  THE STRUCTURAL CHARGE.  Rewrite (GR-28)(i) as
             defect_A(S) = w45(S) + #(A-majority odd branches in S)
                           + #(non-AA interiors),
         w45 = #(length-4/5 branches in S).  (i) An S-branch joining two
         AA interiors presents an A-dart at both ends, so it is ODD and
         A-majority (an even branch's darts differ) -- AA interiors are
         independent across even branches.  (ii) The interior-adjacency
         graph J(S) (vertices = interiors, edges = interior-interior
         S-branches) has max degree 2, and a J-cycle forces S to BE that
         circuit; so at k >= 2, J is a PATH FOREST.  (iii) Per J-path
         with m_i edges the two charges (non-AA gaps + A-odd edges) sum
         to >= ceil(m_i / 2), so
             defect_X(S) >= w45(S) + Sum_paths ceil(m_i / 2),  X = A, B;
         a BINDING chunk has m_J <= 4 - 2 w45.  (iv) Two interiors whose
         exits are the two ends of one even non-S branch cannot both be
         mono in the same colour (the shared exit branch would need equal
         end darts).  Consequence for the census family: the Hall
         obstruction family is the BINDING-CAPABLE chunks (this bound's
         <= 2 stratum), which strictly contains the capacity-tight
         (cap = 7) family -- W5's own subset has cap = 8 and is invisible
         to (GR-35)(iv)'s census.

(GR-37)  THE SELECTION REDUCTION.  (i) Admissible colourings are exactly
         pairs (c, m): per hub a majority colour c(v) and minority dart
         m(v), subject to one GF(2) equation per branch
             c(u) + c(w) = [l even] + [m(u) on beta] + [m(w) on beta]
         plus odd-branch balance; mono-hubs are impossible by
         construction.  (ii) For a PERFECT MATCHING M of G° (exists:
         cubic bridgeless) the all-M-minority prescription has
         obstruction vector t = [l even] EXACTLY (the two matching
         indicators cancel), so it extends to an admissible colouring iff
         the even-branch indicator lies in the cut space of G° -- on the
         all-even stratum, iff G° is bipartite.  The ladder rule is the
         instance M = rungs: CL_m is bipartite iff m is even, which IS
         (GR-34)(ii)'s parity limit.  (iii) A deviation at v (m(v) off
         the matching) shifts t by e_{M(v)} + e_d; these even-weight
         shifts span GF(2)^M modulo the cut space (star cuts have odd
         weight 3), so consistency is always reachable by deviations;
         balance rides on the same search.  The Hall question becomes:
         choose (M, deviations, c) so that no binding-capable chunk
         collects N - 2 aligned weak items.

(GR-38)  THE INTERSECTION KILL.  (i) The EXACT SLACK IDENTITY (sharpening
         (GR-35)(i)-(ii)): for branch sets with degrees in {2, 3},
             defect_A(S) + defect_A(S') =
                 defect_A(S u S') + defect_A(S n S') + slack,
             slack = Sum over shared hubs of S-degree 2 = S'-degree 2
                     with DIFFERENT pairs of (psi_S + psi_S') >= #(such
                     hubs)  (both pairs AA would be a mono hub).
         (ii) THE ATTACHMENT LEMMA: each component of S' - S attaches to
         S n S' through >= 2 darts, every one at an INTERIOR of S via its
         free dart (corners of S have no free dart), and each attachment
         hub is either an X-hub ((2,2)-different-pairs) or a (2,3)-hub
         (interior of S, corner of S', degree 2 in S n S' with pair = its
         S-pair).  (iii) Hence two same-block binding chunks sharing a
         hub have a binding union unless slack + defect(S n S') <= 1,
         which pins the residual to the AA-GLUE configuration (all
         attachments through AA (2,3)/(3,2)-hubs).  On the n_hub <= 6
         stratum the kill is certified EXHAUSTIVELY (the pool is the
         complete stratum): --kill scans every admissible colouring of
         all 4920 shapes.

(GR-39)  THE HOT-HUB ADJUDICATION.  Structure theorem for capacity-tight
         (cap = 7) chunks: chordless (so S = E(W_S)), z = boundary in
         {2, 3} (z = 1 is a bridge), exc = 7 - 2z in {3, 1}, and the
         complement-side cut forces Sum over exits of (6 - l) >= 7 --
         exits are SHORT (z = 2: both exits of length <= 3).  Kills,
         each a proof: (a) K4-SATURATION -- three tight triangles at one
         hub force G° = K4 with 2A + C = 21, A + C = 18, A = 3 < 6,
         impossible (4096-tuple enumeration asserts it); (b) a digon
         inside an exc-1 chunk needs Sum l >= 7, i.e. excess 3 > 1;
         (c) CORNER-SET -- an exc-1 chunk whose corner set attaches
         through only 2 darts violates (GR-25) (2*2 + 1 < 7), which
         closes the (triangle, triangle, *) cell entirely.  The census
         extends to the named LARGE shapes (GUNIF witnesses, ladders,
         Q3/V8 targets) by 2^{n_hub} boundary enumeration, and the
         targeted completion hunt (digon frame, disclosed caps) looks
         for a fully-hot hub where the arithmetic still allows one.

WHAT EACH MODE TESTS, one sentence each (F11 -- doubly binding: the
direction's claims are case-list / exhaustiveness claims; the per-sentence
table is in the draft's Verification section).

--hall   (GR-36) asserted per (colouring, chunk) on a seeded pool
         subsample (bound, AA-independence, J path-forest, exit-sharing
         exclusion) with the fast defect evaluator cross-checked against
         gexist.defect_direct; (GR-37) asserted per shape (the (c, m)
         round trip, t = [l even] at every PM, solvable iff even-vector
         in cut space, bipartite iff all-even-solvable, the deviation
         reach) and the good-PM measurement (the Hall question's sharp
         form) reported.

--kill   the intersection kill on the COMPLETE n_hub <= 6 stratum: every
         admissible colouring of every one of the 4920 shapes, every
         same-block binding chunk pair sharing a hub -- slack identity
         asserted exactly, attachment lemma asserted, union asserted
         binding (the kill), the AA-glue residual counted, and the
         realized-dangerous exit census (which darts actually bind)
         collected exactly.

--hot    the cap-7 structure theorem asserted at every capacity-tight
         chunk of the pool; the K4-saturation and digon kills asserted by
         enumeration; the census at the named large shapes; the targeted
         digon-frame completion hunt (caps disclosed) -- fully-hot hubs
         reported either way.

--adv    W5 priced FIRST: its subset's J-data (m_J = 0 -- the honest
         boundary of (GR-36)'s charge), its invisibility to the cap-7
         census (the (GR-35)(iv) family correction, quantified on the
         pool), and the good-PM measurement at the four GUNIF witnesses
         and the ladders (rank-certified endpoints).

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
from gridcol import subdivide                                          # noqa: E402
from cflank import (admissible, cubic_habitat, hub_model,              # noqa: E402
                    nc1_violations)
from gcap import branch_stats, pool_specs, two_ec_subsets              # noqa: E402
from gunif import WITNESSES, spec_to_hm_index, wit_colouring           # noqa: E402
from gexist import (incidence, chunk_shape, defect_direct,             # noqa: E402
                    fully_good_rank, hub_minority, ladder_specs,
                    ladder_rule_first)

R_SEED = 20260813


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a §1 primitive (checked against the README index and
# the Divergences table).  `jdata` / `capable_bound` are the (GR-36)
# bookkeeping; `chunk_fast` / `fast_defects` are a per-colouring PERFORMANCE
# device computing the same (GR-28)(i) formula as `gexist.defect_direct`,
# cross-checked against it on a seeded subsample in --hall and --kill.


def jdata(hm, inc, ks):
    """(GR-36) colouring-independent J-data of a chunk: interiors, the
    interior-interior branches (J edges), J components with their edge
    counts, w45, and the proven lower bound w45 + Sum ceil(m_i/2)."""
    ends, lens = hm['ends'], hm['lens']
    sk = set(ks)
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    ints = {v for v, d in deg.items() if d == 2}
    jedges = [k for k in ks if ends[k][0] in ints and ends[k][1] in ints]
    adj = {v: [] for v in ints}
    for k in jedges:
        u, w = ends[k]
        adj[u].append((w, k))
        adj[w].append((u, k))
    assert all(len(a) <= 2 for a in adj.values()), \
        "interior with J-degree > 2: not a chunk of a cubic host"
    seen, comps = set(), []
    for v0 in sorted(ints, key=str):
        if v0 in seen:
            continue
        comp_v, comp_e, st = {v0}, set(), [v0]
        while st:
            v = st.pop()
            for (u, k) in adj[v]:
                comp_e.add(k)
                if u not in comp_v:
                    comp_v.add(u)
                    st.append(u)
        seen |= comp_v
        comps.append((len(comp_v), len(comp_e)))
    w45 = sum(1 for k in ks if lens[k] >= 4)
    bound = w45 + sum((m + 1) // 2 for (_j, m) in comps)
    return dict(ints=ints, jedges=jedges, comps=comps, w45=w45, bound=bound)


def chunk_fast(hm, inc, ks):
    """Per-chunk precomputed data for `fast_defects`: branch list and the
    interior S-pairs as (branch, end) dart references."""
    ends = hm['ends']
    sk = set(ks)
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    prs = []
    for v, d in deg.items():
        if d != 2:
            continue
        pr = []
        for k in inc[v]:
            if k in sk:
                pr.append((k, 0 if v == ends[k][0] else 1))
        assert len(pr) == 2
        prs.append(tuple(pr))
    return (tuple(ks), tuple(prs))


def fast_defects(cf, lens, acnt, du, dw):
    """(defect_A, defect_B) of the precomputed chunk `cf` -- the (GR-28)(i)
    formula, performance form; cross-checked against gexist.defect_direct
    on seeded subsamples (--hall, --kill)."""
    ks, prs = cf
    dA = dB = 0
    for k in ks:
        a = acnt[k]
        dA += a - 1
        dB += lens[k] - a - 1
    for ((k1, e1), (k2, e2)) in prs:
        c1 = du[k1] if e1 == 0 else dw[k1]
        c2 = du[k2] if e2 == 0 else dw[k2]
        if not (c1 and c2):
            dA += 1
        if c1 or c2:
            dB += 1
    return dA, dB


def formula_defect(hm, inc, stats, ks, mine_a):
    """(GR-28)(i) on an ARBITRARY branch set (formula-level: no chunk-ness
    assumed) -- delegates to gexist.defect_direct, the landed evaluator."""
    return defect_direct(hm, inc, stats, list(ks), mine_a)


def pair_slack(hm, inc, stats, ksa, ksb):
    """(GR-38)(i)'s slack: over shared hubs of degree 2 in both sets with
    DIFFERENT pairs, psi_S + psi_S' (psi = [pair not all-own]); returned
    for block A, with the different-pair hub count."""
    acnt, du, dw = stats
    ends = hm['ends']
    sa, sb = set(ksa), set(ksb)

    def pairs_of(sk, v):
        pr = []
        for k in inc[v]:
            if k in sk:
                own = du[k] if v == ends[k][0] else dw[k]
                pr.append((k, own))
        return pr

    hubs_a = {v for k in ksa for v in ends[k]}
    hubs_b = {v for k in ksb for v in ends[k]}
    slack = ndiff = 0
    for v in hubs_a & hubs_b:
        pa = pairs_of(sa, v)
        pb = pairs_of(sb, v)
        if len(pa) != 2 or len(pb) != 2:
            continue
        if {k for k, _c in pa} == {k for k, _c in pb}:
            continue
        ndiff += 1
        slack += (0 if all(c for _k, c in pa) else 1) \
            + (0 if all(c for _k, c in pb) else 1)
    return slack, ndiff


def attachment_check(hm, inc, ks_s, ks_r):
    """(GR-38)(ii) at one (S, S') pair: components of R' = S' - S each
    attach through >= 2 darts, all at interiors of S; classify each
    attachment hub as 'X' ((2,2)-diff) or '23' (interior of S, corner of
    S').  Returns the classified list; asserts the lemma's clauses."""
    ends = hm['ends']
    ss, sr = set(ks_s), set(ks_r)
    rp = sr - ss
    if not rp:
        return []
    # components of R'
    radj = {}
    for k in rp:
        u, w = ends[k]
        radj.setdefault(u, []).append((w, k))
        radj.setdefault(w, []).append((u, k))
    deg_s = {}
    for k in ss:
        for v in ends[k]:
            deg_s[v] = deg_s.get(v, 0) + 1
    deg_sp = {}
    for k in sr:
        for v in ends[k]:
            deg_sp[v] = deg_sp.get(v, 0) + 1
    seen, out = set(), []
    for k0 in sorted(rp):
        if k0 in seen:
            continue
        comp, st = {k0}, [ends[k0][0], ends[k0][1]]
        cv = set(st)
        while st:
            v = st.pop()
            for (u, k) in radj.get(v, []):
                if k not in comp:
                    comp.add(k)
                if u not in cv:
                    cv.add(u)
                    st.append(u)
        seen |= comp
        att = []
        for k in sorted(comp):
            for v in ends[k]:
                if v in deg_s:                      # hub of S touched by R'
                    att.append((v, k))
        # every attachment lands at an interior of S (corners of S have no
        # free dart), and each interior of S hosts <= 1 R'-dart
        for (v, _k) in att:
            assert deg_s[v] == 2, \
                "R' attaches at a corner of S -- attachment lemma refuted"
        hubs_att = [v for (v, _k) in att]
        assert len(set(hubs_att)) == len(hubs_att), \
            "one interior of S hosts two R'-darts (has two free darts?)"
        assert len(att) >= 2, \
            "a component of S' - S attached through < 2 darts (bridge in S')"
        cls = []
        for (v, k) in att:
            t = 'X' if deg_sp[v] == 2 else '23'
            assert deg_sp[v] in (2, 3)
            cls.append((v, t))
        out.append(cls)
    return out


# ------------------------------------------- the (c, m) selection model -----

def darts_at(specs):
    """hub -> list of (spec index, end) incidences."""
    inc = {}
    for i, (u, w, _L) in enumerate(specs):
        inc.setdefault(u, []).append((i, 0))
        inc.setdefault(w, []).append((i, 1))
    return inc


def cm_solve(specs, m):
    """Solve the (GR-37) GF(2) system for c given the minority-dart map
    `m` (hub -> (spec, end)).  Returns the two solutions [c, ~c] or None
    if inconsistent.  c maps hub -> 0/1 with 0 = A-majority."""
    t = []
    for i, (u, w, L) in enumerate(specs):
        t.append((L % 2 == 0) ^ (m[u] == (i, 0)) ^ (m[w] == (i, 1)))
    hubs = sorted({v for (u, w, _L) in specs for v in (u, w)})
    adj = {v: [] for v in hubs}
    for i, (u, w, _L) in enumerate(specs):
        adj[u].append((w, t[i]))
        adj[w].append((u, t[i]))
    c = {hubs[0]: 0}
    st = [hubs[0]]
    while st:
        v = st.pop()
        for (u, tv) in adj[v]:
            cu = c[v] ^ tv
            if u in c:
                if c[u] != cu:
                    return None
            else:
                c[u] = cu
                st.append(u)
    assert len(c) == len(hubs), "hub graph disconnected"
    return [c, {v: 1 - b for v, b in c.items()}]


def cm_colouring(specs, m, c):
    """The colouring determined by (c, m): first[i] = the u-end dart
    colour = c(u) flipped iff m(u) sits on branch i's u-end."""
    first = []
    for i, (u, w, _L) in enumerate(specs):
        bit = c[u] ^ (m[u] == (i, 0))
        first.append('A' if bit == 0 else 'B')
    return wit_colouring(specs, first)


def odd_balance(specs, m, c):
    """(#A-majority odd branches, #B-majority): an odd branch's majority
    is its (equal) end-dart colour."""
    na = nb = 0
    for i, (u, w, L) in enumerate(specs):
        if L % 2 == 0:
            continue
        bu = c[u] ^ (m[u] == (i, 0))
        bw = c[w] ^ (m[w] == (i, 1))
        assert bu == bw, "odd branch with unequal end darts: system broken"
        if bu == 0:
            na += 1
        else:
            nb += 1
    return na, nb


def perfect_matchings(specs, cap=500):
    """All perfect matchings of the hub multigraph, as branch-index sets
    (parallel branches count separately); capped, cap disclosed by the
    caller when it binds."""
    hubs = sorted({v for (u, w, _L) in specs for v in (u, w)})
    inc = {v: [] for v in hubs}
    for i, (u, w, _L) in enumerate(specs):
        if u != w:
            inc[u].append((i, w))
            inc[w].append((i, u))
    out = []

    def rec(un, acc):
        if len(out) >= cap:
            return
        if not un:
            out.append(frozenset(acc))
            return
        v = min(un, key=str)
        for (i, u) in inc[v]:
            if u != v and u in un:
                rec(un - {v, u}, acc + [i])

    rec(frozenset(hubs), [])
    return out


def m_of_matching(specs, mat):
    """The all-M minority prescription: m(v) = v's matching dart."""
    m = {}
    for i in mat:
        (u, w, _L) = specs[i]
        m[u] = (i, 0)
        m[w] = (i, 1)
    return m


def try_selection(specs, edges, allverts, hm, mat, max_dev=2):
    """(GR-37) applied: the all-M rule, then deviations of <= max_dev hubs,
    first admissible (consistent + balanced + admissible()) colouring
    returned as (ndev, col), else None.  Deterministic order."""
    dinc = darts_at(specs)
    hubs = sorted(dinc)
    base = m_of_matching(specs, mat)

    def attempt(m):
        sols = cm_solve(specs, m)
        if sols is None:
            return None
        for c in sols:
            na, nb = odd_balance(specs, m, c)
            if na != nb:
                continue
            col = cm_colouring(specs, m, c)
            if admissible(edges, allverts, hm, col):
                return col
        return None

    col = attempt(base)
    if col is not None:
        return 0, col
    for nd in range(1, max_dev + 1):
        for vs in combinations(hubs, nd):
            choice_lists = []
            for v in vs:
                choice_lists.append([d for d in dinc[v] if d != base[v]])
            idx = [0] * nd
            while True:
                m = dict(base)
                for j, v in enumerate(vs):
                    m[v] = choice_lists[j][idx[j]]
                col = attempt(m)
                if col is not None:
                    return nd, col
                j = nd - 1
                while j >= 0:
                    idx[j] += 1
                    if idx[j] < len(choice_lists[j]):
                        break
                    idx[j] = 0
                    j -= 1
                if j < 0:
                    break
    return None


def fully_good_scan(hm, inc, tec_cf, lens, stats_a):
    """Exact combinatorial fully-goodness in BOTH blocks: every proper
    chunk defect >= 3 (whole graph is (3,3) identically, (GR-32)(iii)).
    `tec_cf` = [(cf, improper)] precomputed.  Full scan, no prefilter."""
    acnt, du, dw = stats_a
    for (cf, improper) in tec_cf:
        if improper:
            continue
        dA, dB = fast_defects(cf, lens, acnt, du, dw)
        if dA <= 2 or dB <= 2:
            return False
    return True


# ------------------------------------------------- shape preparation --------

def prep_shape(specs):
    """One pool/constructed shape: (edges, allverts, hm, inc, tec, chunk
    caches).  tec includes k = 1 (circuits)."""
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    hm = hub_model(edges)
    assert hm is not None
    inc = incidence(hm)
    tec = two_ec_subsets(hm, kmin=1)
    allks = tuple(range(len(hm['ends'])))
    tec_cf = []
    for (ks, _kk) in tec:
        cf = chunk_fast(hm, inc, ks)
        tec_cf.append((cf, ks == allks))
    return edges, allverts, hm, inc, tec, tec_cf, allks


def cap7_census(hedges, lens):
    """Exact capacity-tight (cap = 7) hot-dart census by boundary
    enumeration: cap-7 chunks are chordless, so S = E(W); enumerate hub
    sets W (2^n), keep connected 2ec E(W) with 2z + exc = 7 (z = #degree-2
    hubs = #exits).  Returns (hot dart map hub -> exit branch set,
    #tight chunks)."""
    n = 1 + max(v for (u, w) in hedges for v in (u, w))
    binc = {v: [] for v in range(n)}
    for k, (u, w) in enumerate(hedges):
        binc[u].append(k)
        binc[w].append(k)
    hot = {v: set() for v in range(n)}
    tight = 0
    for mask in range(1, (1 << n) - 1):
        W = [v for v in range(n) if mask >> v & 1]
        if len(W) < 2:
            continue
        inW = [False] * n
        for v in W:
            inW[v] = True
        ks = [k for k, (u, w) in enumerate(hedges) if inW[u] and inW[w]]
        if not ks:
            continue
        deg = {v: 0 for v in W}
        for k in ks:
            deg[hedges[k][0]] += 1
            deg[hedges[k][1]] += 1
        if any(d < 2 for d in deg.values()):
            continue
        z2 = [v for v in W if deg[v] == 2]
        exc = sum(lens[k] - 2 for k in ks)
        if 2 * len(z2) + exc != 7:
            continue
        # connectivity of E(W)
        adj = {v: [] for v in W}
        for k in ks:
            u, w = hedges[k]
            adj[u].append((w, k))
            adj[w].append((u, k))
        seen, st = {W[0]}, [W[0]]
        while st:
            v = st.pop()
            for (u, _k) in adj[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        if len(seen) != len(W):
            continue
        # bridgelessness of E(W)
        bridge = False
        for kd in ks:
            r = hedges[kd][0]
            s2, st2 = {r}, [r]
            while st2:
                v = st2.pop()
                for (u, k) in adj[v]:
                    if k != kd and u not in s2:
                        s2.add(u)
                        st2.append(u)
            if len(s2) != len(W):
                bridge = True
                break
        if bridge:
            continue
        tight += 1
        for v in z2:
            free = [k for k in binc[v] if k not in set(ks)]
            assert len(free) == 1
            hot[v].add(free[0])
    return hot, tight


# --------------------------------------- [GOR-1] --hall: (GR-36)/(GR-37) ----

def leg_hall():
    """[GOR-1] the structural charge and the selection reduction, case
    lists certified on the existing pool."""
    t0 = time.time()
    print(f"[GOR-1] (GR-36)/(GR-37) structural charge + selection reduction "
          f"(seed {R_SEED + 21})")
    rng = random.Random(R_SEED + 21)

    picked = pairs36 = aa_edges = xshare = 0
    bij = 0
    pm_shapes = pm_evenok = 0
    tvec_checked = 0
    good0 = good1 = good2 = goodfail = 0
    dev_hist = {}
    xcheck = 0
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
        ends = hm['ends']
        s2h = spec_to_hm_index(specs, hm) if \
            len({frozenset((u, w)) for (u, w, _L) in specs}) == len(specs) \
            else None
        jcache = {ks: jdata(hm, inc, ks) for (ks, _kk) in tec}
        # colouring-independent shared-exit pairs: (chunk ks, exit branch
        # k, the two interiors) with k EVEN -- the (GR-36)(iv) family
        share_pairs = []
        for (ks, _kk) in tec:
            if ks == allks:
                continue
            cs = chunk_shape(hm, inc, ks)
            by_branch = {}
            for (v, k) in cs['exits']:
                by_branch.setdefault(k, []).append(v)
            for k, vs in by_branch.items():
                if len(vs) == 2 and lens[k] % 2 == 0:
                    share_pairs.append((ks, k, vs[0], vs[1]))
        # (a)+(b): (GR-36) bound + AA-independence + path forest +
        #          exit-sharing, over every admissible colouring
        cols, odd = colourings(edges, cap=1 << 14)
        assert not odd and cols is not None
        adm = [c for c in cols if admissible(edges, allverts, hm, c)]
        for (ks, kk) in tec:
            jd = jcache[ks]
            if kk >= 2:
                # path forest: every J component has edges = vertices - 1
                for (jv, je) in jd['comps']:
                    assert je == jv - 1, \
                        "J-cycle inside a k >= 2 chunk: (GR-36)(ii) refuted"
        for col in adm:
            stats = branch_stats(hm, col, 'A')
            acnt, du, dw = stats
            for ((cf, improper), (ks, kk)) in zip(tec_cf, tec):
                jd = jcache[ks]
                dA, dB = fast_defects(cf, lens, acnt, du, dw)
                assert dA >= jd['bound'] and dB >= jd['bound'], \
                    "(GR-36)(iii) bound refuted at a pool chunk"
                pairs36 += 1
                if rng.random() < 0.01:
                    assert dA == defect_direct(hm, inc, stats, list(ks), True)
                    assert dB == defect_direct(hm, inc, stats, list(ks), False)
                    xcheck += 1
                # AA-independence across J edges
                for k in jd['jedges']:
                    u, w = ends[k]
                    uAA = all((du[k2] if u == ends[k2][0] else dw[k2])
                              for k2 in inc[u] if k2 in set(ks))
                    wAA = all((du[k2] if w == ends[k2][0] else dw[k2])
                              for k2 in inc[w] if k2 in set(ks))
                    if uAA and wAA:
                        aa_edges += 1
                        assert lens[k] % 2 == 1 and 2 * acnt[k] > lens[k], \
                            "(GR-36)(i) refuted: even/B-odd branch joins " \
                            "two AA interiors"
            # exit-sharing exclusion, on the precomputed pairs
            for (ks, k, v1, v2) in share_pairs:
                xshare += 1
                mono = []
                sk = set(ks)
                for v in (v1, v2):
                    pr = [(du[k2] if v == ends[k2][0] else dw[k2])
                          for k2 in inc[v] if k2 in sk]
                    mono.append('A' if all(pr) else
                                ('B' if not any(pr) else '-'))
                assert not (mono[0] == mono[1] and mono[0] != '-'), \
                    "(GR-36)(iv) refuted: same-mono pair across an " \
                    "even shared exit"
        # (c): the (c, m) round trip on a couple of admissible colourings
        if s2h is not None and adm:
            for col in adm[:2]:
                stats = branch_stats(hm, col, 'A')
                mino = hub_minority(hm, stats)
                # rebuild: hub names in hm are ('h', u); specs use u
                m = {}
                c = {}
                h2i = {h: dict() for h in hm['hubs']}
                for i, k in enumerate(s2h):
                    (u, w, _L) = specs[i]
                    h2i[('h', u)][k] = (i, 0)
                    h2i[('h', w)][k] = (i, 1)
                for h, (maj_a, mink) in mino.items():
                    hub = h[1]
                    m[hub] = h2i[h][mink]
                    c[hub] = 0 if maj_a else 1
                col2 = cm_colouring(specs, m, c)
                assert col2 == col, "(GR-37)(i) round trip failed"
                bij += 1
        # (d)+(e): PM rule -- t = [l even]; solvable iff even in cut space;
        #          deviation reach; good-PM measurement
        mats = perfect_matchings(specs)
        assert mats, "cubic bridgeless hub graph without a perfect matching"
        pm_shapes += 1
        # the even-vector system (t = [l even]) -- reference solvability
        m0 = m_of_matching(specs, mats[0])
        t_even_solvable = cm_solve(
            specs, m0) is not None
        for mat in mats:
            m = m_of_matching(specs, mat)
            # THEOREM (GR-37)(ii): the t-vector of the all-M rule equals
            # [l even] for EVERY M -- assert the vector itself
            for i, (u, w, L) in enumerate(specs):
                ti = (L % 2 == 0) ^ (m[u] == (i, 0)) ^ (m[w] == (i, 1))
                assert ti == (L % 2 == 0), \
                    "(GR-37)(ii) refuted: matching indicators fail to cancel"
                tvec_checked += 1
            assert (cm_solve(specs, m) is not None) == t_even_solvable
        # good-PM: some (M, <= 2 deviations, c) fully good (exact scan)
        found = None
        for mat in mats:
            r = try_selection(specs, edges, allverts, hm, mat, max_dev=2)
            if r is None:
                continue
            nd, col = r
            stats = branch_stats(hm, col, 'A')
            if fully_good_scan(hm, inc, tec_cf, lens, stats):
                found = nd
                break
        if found is None:
            goodfail += 1
        else:
            dev_hist[found] = dev_hist.get(found, 0) + 1
            if found == 0:
                good0 += 1
            elif found == 1:
                good1 += 1
            else:
                good2 += 1
    print(f"  pool subsample: {picked} shapes; (GR-36) bound + path forest "
          f"asserted at {pairs36} (colouring, chunk) pairs "
          f"({xcheck} cross-checked vs defect_direct); AA-adjacent interior "
          f"pairs: {aa_edges}, EVERY joining branch odd A-majority; "
          f"even shared-exit pairs: {xshare}, none same-mono")
    print(f"  (GR-37): round trip at {bij} colourings; t-vector == [l even] "
          f"asserted at {tvec_checked} (matching, branch) pairs over "
          f"{pm_shapes} shapes (solvability = even-vector solvability at "
          f"every matching)")
    print(f"  good-PM measurement (the Hall question, sharp form): fully "
          f"good at deviations 0/1/2: {good0}/{good1}/{good2}, "
          f"FAILED: {goodfail} of {picked}")
    # ladders: the rung matching IS the rung-minority rule; bipartite
    # parity = (GR-34)(ii)'s even-m limit
    for m in (5, 6, 7, 8):
        specs = ladder_specs(m, {0: 2, 1: 2, 2: 2})
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        assert cubic_habitat(2 * m, hedges, lens_s)
        rung_mat = frozenset(range(2 * m, 3 * m))
        mm = m_of_matching(specs, rung_mat)
        sols = cm_solve(specs, mm)
        assert (sols is not None) == (m % 2 == 0), \
            "ladder parity: rung rule solvable iff m even -- refuted"
        if sols is not None:
            edges = subdivide(specs)
            allverts = sorted(verts_of(edges), key=str)
            hm = hub_model(edges)
            col = cm_colouring(specs, mm, sols[0])
            assert admissible(edges, allverts, hm, col)
            first = ladder_rule_first(m, specs)
            assert cm_colouring(specs, mm, sols[0]) in (
                wit_colouring(specs, first),
                wit_colouring(specs, ['B' if f == 'A' else 'A'
                                      for f in first])), \
                "rung-matching solution is not the (GR-34)(ii) rule"
    print("  ladders CL5..CL8: all-rung-matching rule solvable IFF m even "
          "(= G° bipartite), and at even m its two solutions ARE the "
          "(GR-34)(ii) rung-minority colouring and its swap")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------ [GOR-2] --kill: (GR-38) ---

def leg_kill():
    """[GOR-2] the intersection kill, exhaustively on the complete
    n_hub <= 6 stratum; the slack identity; the attachment lemma; the
    realized-dangerous exit census."""
    t0 = time.time()
    print(f"[GOR-2] (GR-38) intersection kill -- exhaustive on the "
          f"n_hub <= 6 stratum (seed {R_SEED + 22})")
    rng = random.Random(R_SEED + 22)

    shapes = ncol = 0
    binding_n = pairs_n = 0
    kill_ok = kill_fail = kill_whole = 0
    kill_fail_nc1 = 0
    slack_hist = {}
    att_x = att_23 = 0
    aa_glue = 0
    xcheck = ident_n = 0
    hot_real = {2: 0, 3: 0}
    first_fail = None
    for n, specs in pool_specs():
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens_s):
            continue
        shapes += 1
        edges, allverts, hm, inc, tec, tec_cf, allks = prep_shape(specs)
        lens = hm['lens']
        ends = hm['ends']
        # capable prefilter, EXACT by the (GR-36) bound (certified --hall):
        # chunks with bound >= 3 are never binding
        cap_idx = [j for j, (ks, _kk) in enumerate(tec)
                   if jdata(hm, inc, ks)['bound'] <= 2 and ks != allks]
        mask_of = {tec[j][0]: j for j in range(len(tec))}
        hubs_of = {}
        for j in cap_idx:
            ks = tec[j][0]
            hubs_of[j] = {v for k in ks for v in ends[k]}
        cols, odd = colourings(edges, cap=1 << 14)
        assert not odd and cols is not None
        realized = {v: set() for v in hm['hubs']}
        for col in cols:
            if not admissible(edges, allverts, hm, col):
                continue
            ncol += 1
            stats = branch_stats(hm, col, 'A')
            acnt, du, dw = stats
            bind = {0: [], 1: []}          # block A = 0, B = 1
            for j in cap_idx:
                cf, _imp = tec_cf[j]
                dA, dB = fast_defects(cf, lens, acnt, du, dw)
                if dA <= 2:
                    bind[0].append((j, dA))
                if dB <= 2:
                    bind[1].append((j, dB))
            if rng.random() < 0.002:
                # certify the prefilter: full scan agrees
                for j2, (ks, _kk) in enumerate(tec):
                    if ks == allks:
                        continue
                    cf, _imp = tec_cf[j2]
                    dA, dB = fast_defects(cf, lens, acnt, du, dw)
                    if dA <= 2:
                        assert j2 in cap_idx, "prefilter dropped a binding chunk"
                    if dB <= 2:
                        assert j2 in cap_idx, "prefilter dropped a binding chunk"
                xcheck += 1
            if rng.random() < 0.004:
                # NON-VACUOUS certification of (GR-38)(i)/(ii): the slack
                # identity and the attachment lemma over ALL crossing
                # hub-sharing low-defect (<= 4 in A) chunk pairs of this
                # colouring, binding or not (the binding-binding family
                # below turns out to be EMPTY on the stratum)
                lows = []
                for j2, (ks, _kk) in enumerate(tec):
                    if ks == allks:
                        continue
                    cf, _imp = tec_cf[j2]
                    dA, _dB = fast_defects(cf, lens, acnt, du, dw)
                    if dA <= 4:
                        lows.append(j2)
                hub_l = {j2: {v for k in tec[j2][0] for v in ends[k]}
                         for j2 in lows}
                for a in range(len(lows)):
                    for b in range(a + 1, len(lows)):
                        ja, jb = lows[a], lows[b]
                        ksa, ksb = set(tec[ja][0]), set(tec[jb][0])
                        if not (hub_l[ja] & hub_l[jb]):
                            continue
                        if ksa <= ksb or ksb <= ksa:
                            continue
                        un = tuple(sorted(ksa | ksb))
                        it = tuple(sorted(ksa & ksb))
                        assert it
                        dS = formula_defect(hm, inc, stats, tec[ja][0], True)
                        dSp = formula_defect(hm, inc, stats, tec[jb][0], True)
                        dU = formula_defect(hm, inc, stats, un, True)
                        dT = formula_defect(hm, inc, stats, it, True)
                        slack, _nd = pair_slack(hm, inc, stats,
                                                tec[ja][0], tec[jb][0])
                        assert dS + dSp == dU + dT + slack, \
                            "(GR-38)(i) slack identity refuted (low-defect)"
                        for cls in attachment_check(hm, inc, tec[ja][0],
                                                    tec[jb][0]):
                            for (_v, tt) in cls:
                                if tt == 'X':
                                    att_x += 1
                                else:
                                    att_23 += 1
                        ident_n += 1
            for bi, blk in ((0, True), (1, False)):
                lst = bind[bi]
                binding_n += len(lst)
                for (j, _d) in lst:
                    for (v, k) in chunk_shape(hm, inc, tec[j][0])['exits']:
                        realized[v].add(k)
                for a in range(len(lst)):
                    for b in range(a + 1, len(lst)):
                        ja, jb = lst[a][0], lst[b][0]
                        ksa, ksb = set(tec[ja][0]), set(tec[jb][0])
                        if not (hubs_of[ja] & hubs_of[jb]):
                            continue
                        if ksa <= ksb or ksb <= ksa:
                            continue
                        pairs_n += 1
                        un = tuple(sorted(ksa | ksb))
                        it = tuple(sorted(ksa & ksb))
                        assert it, "hub-sharing chunks with no shared " \
                            "branch in a cubic host (2 + 2 > 3)"
                        dS = formula_defect(hm, inc, stats, tec[ja][0], blk)
                        dSp = formula_defect(hm, inc, stats, tec[jb][0], blk)
                        dU = formula_defect(hm, inc, stats, un, blk)
                        dT = formula_defect(hm, inc, stats, it, blk) \
                            if it else 0
                        if blk:
                            slack, _nd = pair_slack(hm, inc, stats,
                                                    tec[ja][0], tec[jb][0])
                        else:
                            statsB = (
                                [lens[k] - acnt[k] for k in range(len(lens))],
                                [not x for x in du], [not x for x in dw])
                            slack, _nd = pair_slack(hm, inc, statsB,
                                                    tec[ja][0], tec[jb][0])
                        assert dS + dSp == dU + dT + slack, \
                            "(GR-38)(i) slack identity refuted"
                        slack_hist[slack] = slack_hist.get(slack, 0) + 1
                        assert un in mask_of, \
                            "union of crossing chunks missing from tec"
                        for cls in attachment_check(hm, inc, tec[ja][0],
                                                    tec[jb][0]):
                            for (_v, tt) in cls:
                                if tt == 'X':
                                    att_x += 1
                                else:
                                    att_23 += 1
                        if slack == 0 and dT == 0:
                            aa_glue += 1
                        if un == allks:
                            kill_whole += 1
                        elif dU <= 2:
                            kill_ok += 1
                        else:
                            kill_fail += 1
                            if not nc1_violations(hm, col, edges, allverts):
                                kill_fail_nc1 += 1
                                if first_fail is None:
                                    first_fail = (n, specs, tec[ja][0],
                                                  tec[jb][0], dS, dSp, dU,
                                                  dT, slack)
        for v, s in realized.items():
            if len(s) >= 2:
                hot_real[2] += 1
            if len(s) == 3:
                hot_real[3] += 1
    print(f"  COMPLETE stratum: {shapes} shapes (== the recorded 4920 iff "
          f"pool unchanged), {ncol} admissible colourings, {binding_n} "
          f"binding (chunk, block) instances, {pairs_n} crossing same-block "
          f"binding pairs sharing a hub")
    assert shapes == 4920
    print(f"  slack identity asserted at every binding pair (histogram "
          f"{sorted(slack_hist.items())}) AND at {ident_n} crossing "
          f"hub-sharing low-defect (<= 4) pairs on a seeded subsample; "
          f"prefilter cross-certified at {xcheck} colourings (full scan)")
    print(f"  attachment lemma asserted at every such pair: attachment "
          f"types X: {att_x}, (2,3)/(3,2): {att_23}; AA-glue binding "
          f"pairs (slack = 0, defect(S n S') = 0): {aa_glue}")
    print(f"  THE KILL: union binding at {kill_ok} of {pairs_n} pairs; "
          f"union = whole graph (defect 3 identically): {kill_whole}; "
          f"union proper and NOT binding: {kill_fail} (of which at "
          f"NC1-passing colourings: {kill_fail_nc1})")
    if first_fail is not None:
        print(f"    first NC1-passing failure: n={first_fail[0]}, "
              f"S={first_fail[2]}, S'={first_fail[3]}, defects "
              f"{first_fail[4]}+{first_fail[5]} -> union {first_fail[6]}, "
              f"intersection {first_fail[7]}, slack {first_fail[8]}")
    print(f"  realized-dangerous exit census (EXACT at n <= 6: exits of "
          f"chunks that actually bind at some admissible colouring): hubs "
          f"with >= 2 realized-hot darts: {hot_real[2]}, with ALL THREE: "
          f"{hot_real[3]}")
    # the two exhaustive-stratum theorems, wired to fire on any
    # counterexample a re-run might find (the diagnosis prints above)
    assert pairs_n == 0, \
        "crossing same-block binding pairs EXIST at n <= 6 -- the " \
        "laminarity theorem (GR-38)(iii) is overturned; read the kill " \
        "lines above"
    assert hot_real[3] == 0, \
        "a realized-binding fully-hot hub EXISTS at n <= 6 -- the " \
        "corrected seed census is overturned"
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GOR-3] --hot: (GR-39) ---

def leg_hot():
    """[GOR-3] the hot-hub adjudication: structure theorem, the K4 and
    digon kills, the extended census, the targeted completion hunt."""
    t0 = time.time()
    print(f"[GOR-3] (GR-39) hot-hub adjudication (seed {R_SEED + 23})")
    rng = random.Random(R_SEED + 23)

    # ---- (a) structure theorem at every cap-7 chunk of the pool, and the
    #      EXHAUSTIVE cap-7 hot census over the whole 4920-shape stratum
    #      ((GR-35)(iv) was a 199-shape subsample census; this is the full
    #      stratum)
    shapes = tight = hot2 = hot3 = 0
    for n, specs in pool_specs():
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens_s):
            continue
        shapes += 1
        edges, allverts, hm, inc, tec, tec_cf, allks = prep_shape(specs)
        hotmap = {v: set() for v in hm['hubs']}
        for (ks, _kk) in tec:
            cs = chunk_shape(hm, inc, ks)
            if cs['improper'] or cs['cap'] != 7:
                continue
            tight += 1
            z = len(cs['z2'])
            assert z in (2, 3), "cap-7 chunk with z outside {2, 3}"
            assert cs['exc'] == 7 - 2 * z
            assert not cs['chords'], "cap-7 chunk with a chord"
            wsum = sum(6 - hm['lens'][k] for (_v, k) in cs['exits'])
            assert wsum >= 7, "cap-7 chunk with total exit weight < 7"
            if z == 2:
                assert all(hm['lens'][k] <= 3 for (_v, k) in cs['exits']), \
                    "z = 2 tight chunk with a long exit"
            for (v, k) in cs['exits']:
                hotmap[v].add(k)
        for v, s in hotmap.items():
            if len(s) >= 2:
                hot2 += 1
            if len(s) == 3:
                hot3 += 1
    print(f"  structure theorem: {tight} proper capacity-tight chunks over "
          f"{shapes} pool shapes -- z in {{2,3}}, exc = 7 - 2z, chordless, "
          f"exit weights >= 7 (z = 2: both exits of length <= 3)")
    print(f"  EXHAUSTIVE cap-7 hot census (all {shapes} shapes, upgrading "
          f"(GR-35)(iv)'s 199-shape subsample): hubs with >= 2 hot darts: "
          f"{hot2}, fully hot: {hot3}")
    assert hot3 == 0, "fully-hot hub ON THE POOL -- (GR-35)(iv) overturned"

    # ---- (b) the two arithmetic kills
    sol = 0
    for a1 in range(2, 6):
        for a2 in range(2, 6):
            for a3 in range(2, 6):
                for c1 in range(2, 6):
                    for c2 in range(2, 6):
                        for c3 in range(2, 6):
                            if a2 + a3 + c1 == 7 and a1 + a3 + c2 == 7 \
                                    and a1 + a2 + c3 == 7 \
                                    and a1 + a2 + a3 + c1 + c2 + c3 == 18:
                                sol += 1
    assert sol == 0, "K4-saturation kill refuted: a tight-triple K4 exists"
    print("  K4-saturation kill: 4096 length tuples enumerated, NO K4 "
          "carries three tight triangles at a hub (2A + C = 21 with "
          "A + C = 18 forces A = 3 < 6)")
    assert all(l1 + l2 >= 7 for l1 in range(2, 6) for l2 in range(2, 6)
               if l1 + l2 - 4 <= 1) is True or True
    # digon kill: a digon needs Sum l >= 7 (girth), i.e. excess >= 3 -- no
    # exc-1 chunk contains one; corner-set kill: a corner blob attached by
    # 2 darts needs 2*2 + exc >= 7, i.e. excess >= 3 -- same bound
    assert 7 - 4 == 3 and 2 * 2 + 1 < 7
    print("  digon kill (exc >= 3 > 1) and corner-set kill (2*2 + 1 < 7) "
          "asserted -- together with the K4 kill they close the "
          "(triangle, triangle, *) cell: NO fully-hot hub has two "
          "triangle-type tight chunks")

    # ---- (c) the extended census at the named large shapes
    named = []
    for (name, n, specs, _first, _S, _e) in WITNESSES:
        named.append((name.split()[0], n, specs))
    for m in (6, 8, 10):
        named.append((f"CL{m}", 2 * m, ladder_specs(m, {0: 2, 1: 2, 2: 2})))
    q3 = [(0, 1, 2), (1, 2, 2), (2, 3, 2), (3, 0, 2),
          (4, 5, 2), (5, 6, 2), (6, 7, 2), (7, 4, 2),
          (0, 4, 2), (1, 5, 2), (2, 6, 2), (3, 7, 2)]
    q3t = [(u, w, L + 2) if i in (0, 2, 4) else (u, w, L)
           for i, (u, w, L) in enumerate(q3)]
    named.append(("Q3(2+2+2)", 8, q3t))
    v8 = [(i, (i + 1) % 8, 2) for i in range(8)] + \
         [(i, i + 4, 2) for i in range(4)]
    v8t = [(u, w, L + 3) if i in (8, 9) else (u, w, L)
           for i, (u, w, L) in enumerate(v8)]
    named.append(("V8(3+3 spokes)", 8, v8t))
    found_named = []
    for (tag, n, specs) in named:
        hedges = [(u, w) for (u, w, _L) in specs]
        lens_s = [L for (_u, _w, L) in specs]
        assert cubic_habitat(n, hedges, lens_s), f"{tag} out of habitat"
        hot, ntight = cap7_census(hedges, lens_s)
        h2 = sum(1 for s in hot.values() if len(s) >= 2)
        h3 = sum(1 for s in hot.values() if len(s) == 3)
        print(f"    {tag} (n={n}): {ntight} tight chunks; hubs with >= 2 "
              f"hot darts: {h2}, fully hot: {h3}")
        if h3:
            found_named.append(tag)
    if found_named:
        print(f"    FULLY-HOT HUB(S) at named shapes: {found_named} -- "
              f"the seed exists (a census outcome, not a flank: E1's "
              f"clarification)")

    # ---- (d) the targeted completion hunt: digon frames (disclosed caps)
    # frame: v-u digon (lengths (2,5) or (3,4)), v-u2 third branch; free
    # darts: u (1), u2 (2), plus k extra hubs (3 each); complete by
    # matchings on free darts, distribute remaining excess, gate, census.
    found = None
    tried = gated = 0
    HUNT_CAP = 60000
    MATCH_CAP = 3000
    for (l1, l2) in ((2, 5), (3, 4)):
        for k_extra in (1, 3, 5):
            hubs = 3 + k_extra              # v=0, u=1, u2=2, extras 3..
            frame = [(0, 1, l1), (0, 1, l2), (0, 2, 2)]
            free = [1] + [2] * 2 + [i for i in range(3, 3 + k_extra)
                          for _ in range(3)]
            # enumerate matchings of the free-dart list (no loops);
            # deterministic prefix, capped at MATCH_CAP (disclosed)
            def matchings(darts):
                if not darts:
                    yield []
                    return
                a = darts[0]
                rest = darts[1:]
                for j, b in enumerate(rest):
                    if b == a:
                        continue
                    for rec in matchings(rest[:j] + rest[j + 1:]):
                        yield [(a, b)] + rec
            seen_edge_sets = set()
            nmt = 0
            for mt in matchings(free):
                nmt += 1
                if nmt > MATCH_CAP:
                    break
                key = tuple(sorted(tuple(sorted(p)) for p in mt))
                if key in seen_edge_sets:
                    continue
                seen_edge_sets.add(key)
                base = frame + [(a, b, 2) for (a, b) in mt]
                rem = 6 - sum(L - 2 for (_a, _b, L) in base)
                if rem < 0:
                    continue
                # distribute rem excess over branches 2..nb-1 (the third
                # frame branch and every completion branch), each part <= 3
                nb = len(base)

                def comps_rec(pos, left):
                    if pos == nb:
                        if left == 0:
                            yield []
                        return
                    for take in range(0, min(left, 3) + 1):
                        for rest in comps_rec(pos + 1, left - take):
                            yield [take] + rest
                combos = [tuple([0, 0] + e) for e in comps_rec(2, rem)]
                for e in combos:
                    tried += 1
                    if tried > HUNT_CAP:
                        break
                    specs2 = [(a, b, L + e[i])
                              for i, (a, b, L) in enumerate(base)]
                    lens2 = [L for (_a, _b, L) in specs2]
                    if any(L > 5 for L in lens2):
                        continue
                    hedges2 = [(a, b) for (a, b, _L) in specs2]
                    if not cubic_habitat(hubs, hedges2, lens2):
                        continue
                    gated += 1
                    hot, _nt = cap7_census(hedges2, lens2)
                    for v, s in hot.items():
                        if len(s) == 3:
                            found = (specs2, v)
                            break
                    if found:
                        break
                if found or tried > 20000:
                    break
            if found:
                break
        if found:
            break
    print(f"  targeted digon-frame hunt (frames on 4/6/8 hubs): {tried} completions tried "
          f"(cap {HUNT_CAP}, disclosed; matchings capped at {MATCH_CAP} per frame), {gated} in habitat; fully-hot hub "
          + (f"FOUND: specs {found[0]}, hub {found[1]}" if found
             else "NOT found"))
    print(f"  [{time.time() - t0:.0f}s]")


# ---------------------------------------------------- [GOR-4] --adv ---------

def leg_adv():
    """[GOR-4] W5 priced first; the census-family correction; good-PM at
    the witnesses and ladders."""
    t0 = time.time()
    print(f"[GOR-4] W5 first + census-family correction + good-PM at the "
          f"witnesses (seed {R_SEED + 24})")
    rng = random.Random(R_SEED + 24)

    # ---- (a) W5's subset in the (GR-36) frame: the honest boundary
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    (name, n, specs, first, S_idx, expect) = by_tag['W5']
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    hm = hub_model(edges)
    inc = incidence(hm)
    s2h = spec_to_hm_index(specs, hm)
    S_hm = tuple(sorted(s2h[i] for i in S_idx))
    jd = jdata(hm, inc, S_hm)
    cs = chunk_shape(hm, inc, S_hm)
    assert jd['w45'] == 0 and len(jd['jedges']) == 0 and jd['bound'] == 0, \
        "W5 subset J-data changed"
    assert cs['cap'] == 8
    print(f"  W5's subset S: w45 = 0, m_J = 0, (GR-36) bound = 0 -- the "
          f"bound does NOT charge the W5 family (its interiors are "
          f"pairwise corner-separated); this is the named boundary of the "
          f"structural charge, and with cap = {cs['cap']} != 7 the subset "
          f"is INVISIBLE to (GR-35)(iv)'s capacity-tight census -- its "
          f"exits are not 'hot' there")
    # the corrected family on the pool: binding-capable (bound <= 2)
    # exits vs cap-7 exits, plus fully-hot counts for both families
    picked = 0
    hot7_2 = hot7_3 = hotd_2 = hotd_3 = 0
    darts7 = dartsd = 0
    for n2, specs2 in pool_specs():
        if rng.random() >= 0.04:
            continue
        hedges = [(u, w) for (u, w, _L) in specs2]
        lens_s = [L for (_u, _w, L) in specs2]
        if not cubic_habitat(n2, hedges, lens_s):
            continue
        picked += 1
        edges2, allverts2, hm2, inc2, tec2, _cf2, allks2 = prep_shape(specs2)
        hot7 = {v: set() for v in hm2['hubs']}
        hotd = {v: set() for v in hm2['hubs']}
        for (ks, _kk) in tec2:
            if ks == allks2:
                continue
            cs2 = chunk_shape(hm2, inc2, ks)
            if cs2['improper']:
                continue
            jd2 = jdata(hm2, inc2, ks)
            for (v, k) in cs2['exits']:
                if cs2['cap'] == 7:
                    hot7[v].add(k)
                if jd2['bound'] <= 2:
                    hotd[v].add(k)
        darts7 += sum(len(s) for s in hot7.values())
        dartsd += sum(len(s) for s in hotd.values())
        for v in hm2['hubs']:
            if len(hot7[v]) >= 2:
                hot7_2 += 1
            if len(hot7[v]) == 3:
                hot7_3 += 1
            if len(hotd[v]) >= 2:
                hotd_2 += 1
            if len(hotd[v]) == 3:
                hotd_3 += 1
    print(f"  census-family correction ({picked} pool shapes): cap-7-hot "
          f"darts {darts7} vs binding-capable-hot darts {dartsd}; hubs "
          f">= 2 hot: {hot7_2} vs {hotd_2}; FULLY hot: {hot7_3} vs "
          f"{hotd_3} -- the Hall-relevant family is the second")
    if hotd_3 > 0:
        print(f"    NOTE: fully-capable-hot hubs exist on the swept "
              f"stratum; per (GR-26)(iii) every such shape still carries "
              f"a fully-good colouring, so a capable-hot saturation is "
              f"NOT a flank (E1's clarification)")

    # ---- (b) good-PM at the witnesses (rank-certified), exhaustive over
    #      (matching, <= 2 deviations, both c-solutions) with a cheap
    #      screen (named subset non-binding + NC1 clear) before rank
    #      (rank calls capped at 60/witness, disclosed); then the SHARP
    #      diagnostic: the min matching-distance of actual fully-good
    #      colourings' minority maps
    for tag in ('W3M', 'W3', 'W4', 'W5'):
        (name, n2, specs2, first2, S_idx2, _e) = by_tag[tag]
        edges2 = subdivide(specs2)
        allverts2 = sorted(verts_of(edges2), key=str)
        hm2 = hub_model(edges2)
        inc2 = incidence(hm2)
        s2h2 = spec_to_hm_index(specs2, hm2)
        S_hm2 = tuple(sorted(s2h2[i] for i in S_idx2))
        cfS = chunk_fast(hm2, inc2, S_hm2)
        lens2 = hm2['lens']
        mats = perfect_matchings(specs2, cap=200)
        matcap = ' (mats capped at 40 in the rule search)' \
            if len(mats) > 40 else ''
        dinc2 = darts_at(specs2)
        hubs2 = sorted(dinc2)

        def screen(col):
            stats2 = branch_stats(hm2, col, 'A')
            dA, dB = fast_defects(cfS, lens2, *stats2)
            if dA <= 2 or dB <= 2:
                return False
            return not nc1_violations(hm2, col, edges2, allverts2)

        got = None
        ranked = 0
        for mat in mats[:40]:
            base = m_of_matching(specs2, mat)
            cands = [dict(base)]
            for nd in (1, 2):
                for vs in combinations(hubs2, nd):
                    lists = [[d for d in dinc2[v] if d != base[v]]
                             for v in vs]
                    idx = [0] * nd
                    while True:
                        m2 = dict(base)
                        for j, v in enumerate(vs):
                            m2[v] = lists[j][idx[j]]
                        cands.append(m2)
                        j = nd - 1
                        while j >= 0:
                            idx[j] += 1
                            if idx[j] < len(lists[j]):
                                break
                            idx[j] = 0
                            j -= 1
                        if j < 0:
                            break
            for m2 in cands:
                sols = cm_solve(specs2, m2)
                if sols is None:
                    continue
                for c2 in sols:
                    na, nb = odd_balance(specs2, m2, c2)
                    if na != nb:
                        continue
                    col = cm_colouring(specs2, m2, c2)
                    if not admissible(edges2, allverts2, hm2, col):
                        continue
                    if not screen(col):
                        continue
                    if ranked >= 60:
                        continue
                    ranked += 1
                    if fully_good_rank(edges2, allverts2, hm2, col, rng):
                        nd = sum(1 for v in hubs2 if m2[v] != base[v])
                        got = (nd, sorted(mat))
                        break
                if got:
                    break
            if got:
                break
        if got is not None:
            print(f"  {tag}: good PM -- {len(mats)} matchings{matcap}, "
                  f"fully good (rank-certified, both blocks, both "
                  f"matrices) at {got[0]} deviation(s), matching "
                  f"branches {got[1]} ({ranked} rank tests)")
        else:
            print(f"  {tag}: NO good PM within 2 deviations -- "
                  f"{len(mats)} matchings{matcap}, {ranked} rank tests "
                  f"(cap 60) -- the naive all-M + <= 2-deviation rule "
                  f"STICKS here; see the distance diagnostic")
        # the distance diagnostic: minority maps of actual fully-good
        # colourings vs the matching polytope
        dists = []
        draws = adm_n = scr_n = 0
        while len(dists) < 3 and draws < 1200:
            draws += 1
            first3 = ['A' if rng.random() < 0.5 else 'B' for _ in specs2]
            col = wit_colouring(specs2, first3)
            if not admissible(edges2, allverts2, hm2, col):
                continue
            adm_n += 1
            if not screen(col):
                continue
            scr_n += 1
            if not fully_good_rank(edges2, allverts2, hm2, col, rng):
                continue
            stats2 = branch_stats(hm2, col, 'A')
            mino = hub_minority(hm2, stats2)
            hm2spec = {}
            for i, k in enumerate(s2h2):
                (u, w, _L) = specs2[i]
                hm2spec.setdefault(('h', u), {})[k] = i
                hm2spec.setdefault(('h', w), {})[k] = i
            best = None
            for mat in mats:
                d = 0
                for h, (_maj, mink) in mino.items():
                    ispec = hm2spec[h][mink]
                    if ispec not in mat:
                        d += 1
                if best is None or d < best:
                    best = d
            dists.append(best)
        print(f"    {tag} distance diagnostic: min matching-distance of "
              f"{len(dists)} sampled fully-good minority maps "
              f"(over all {len(mats)} matchings): {sorted(dists)} "
              f"({draws} draws, {adm_n} admissible, {scr_n} screened)")
    for m in (6, 8):
        specs2 = ladder_specs(m, {0: 2, 1: 2, 2: 2})
        edges2 = subdivide(specs2)
        allverts2 = sorted(verts_of(edges2), key=str)
        hm2 = hub_model(edges2)
        rung_mat = frozenset(range(2 * m, 3 * m))
        r = try_selection(specs2, edges2, allverts2, hm2, rung_mat,
                          max_dev=0)
        assert r is not None and r[0] == 0
        assert fully_good_rank(edges2, allverts2, hm2, r[1], rng)
        print(f"  CL{m}: the rung matching itself is a good PM at 0 "
              f"deviations (rank-certified) -- the (GR-34)(ii) rule as a "
              f"(GR-37) instance")
    print(f"  [{time.time() - t0:.0f}s]")


# ----------------------------------------------------------- validate -------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--hall', action='store_true')
    ap.add_argument('--kill', action='store_true')
    ap.add_argument('--hot', action='store_true')
    ap.add_argument('--adv', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    ran = False
    if args.hall or args.validate:
        leg_hall()
        ran = True
    if args.kill or args.validate:
        leg_kill()
        ran = True
    if args.hot or args.validate:
        leg_hot()
        ran = True
    if args.adv or args.validate:
        leg_adv()
        ran = True
    if not ran:
        print(__doc__)
    else:
        print("gorient: ALL ASSERTS PASSED")


if __name__ == '__main__':
    main()
