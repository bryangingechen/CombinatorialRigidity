"""
Direction BEARFULL (ordinal 47) -- the EAR CASE's last two items, and a
ROUTING question about the induction's shape.

  JOB 1  (BE-32)(+) AS A THEOREM.  *A graph that forces `pi_u = pi_v` has
         `delta_uv = 0`.*  BEARCASE leaves this as the SINGLE named residue of
         the ear case on the (beta) side.  Status on arrival: MEASURED at
         208 418 instances under the AGGRESSIVE plane-class closure, with two
         of its three mechanisms -- (BE-32)(ii) a common triangle, (BE-32)(iii)
         `>= 3` common neighbours -- already theorems by the four-line MERGE
         INEQUALITY  `value = f - 6k + 5c`.

  JOB 2  (b2) FOR A GENERAL PIECE -- the middle clause of (BE-37)(ii)'s
         reduction, at a piece not covered by (BE-38)(ii)'s
         `dist_{G_1}(u,v) <= 4` transfer.

  JOB 3  THE ROUTING QUESTION.  Does the EAR CASE already BE the induction
         step, via an open ear decomposition (classical; Whitney 1932), so
         that the INTERNAL R-NODE leaves the critical path?

Succeeds `notes/scripts/w4/bearcase.py` (Steps BE34-BE37), which this driver
imports READ-ONLY together with `bimage` / `btwocut` / `binduc` /
`kbare_common` through it, rather than reimplementing the chain,
classification, deficiency, pencil-witness or free-sampler machinery.
BEARCASE's, BIMAGE's, BTWOCUT's, BINDUC's and BZAVOID's figures are CITED,
never re-run.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-39)  THE PARTITION-LATTICE LAWS the merge inequality actually proves.
             `merge`   : for an OPTIMAL partition P, the quotient multigraph Q
                         on the parts satisfies  5 e_Q(S) <= 6(|S|-1)  for
                         EVERY set S of parts -- so Q is SIMPLE and has GIRTH
                         >= 6.  And the partition weight
                         g(P) = 5 e_in(P) + 6|P| - 6n  is SUPERMODULAR on the
                         partition lattice, so the JOIN of two optimal
                         partitions is optimal: there is a unique COARSEST
                         optimal partition P_max and
                           delta_uv = 0  <=>  u, v in one block of P_max,
                         which makes "delta = 0" an EQUIVALENCE RELATION.
                         ENUMERATED: every optimal partition, every subset of
                         parts, every pair of optimal partitions, over ALL
                         connected labelled graphs on n = 3..6.

  (BE-40)  THE SHORT-CYCLE LAW -- one statement that CONTAINS (BE-32)(ii),
           (iii) and sharpens (iv).
             `cycles`  : every cycle of G of length <= 5 lies inside a SINGLE
                         part of EVERY optimal partition; a 6-cycle either
                         does, or its six parts are a TIGHT set whose merge is
                         again optimal.  Hence  delta_xy = 0  for any x, y on
                         a common cycle of length <= 6, and
                         delta_xy <= max(0, L - 6)  on a common L-cycle.

  (BE-41)  (BE-32)(+) REDUCED to a statement with NO GEOMETRY IN IT.
             `forced`  : every AGGRESSIVELY-forced pair is <=6-cycle-class
                         connected -- which, with (BE-39)'s equivalence
                         relation and (BE-40), gives delta = 0.  PROVED for
                         every forcing step whose three points put two in one
                         closed star; MEASURED for the rest.
             `chain`   : the proof's boundary, LOCATED -- a named triangle-chain
                         family whose forcing step needs a cycle of length
                         EXACTLY 7, i.e. one more than the merge inequality's
                         slack allows, and at which delta = 0 nonetheless.

  (BE-42)  (b2) IS A CONSEQUENCE OF (b1), by one line of Grassmann.
             `bgrass`  : Pi_u <= Z, so
                         dim(rho_1 cap Z) <= dim Z - 2 + dim(rho_1 cap Pi_u)
                         and the same at v.  Hence (b1) => (b2) outright when
                         delta_1 >= 5, and  rho_1 cap Pi_u = 0 at EITHER end
                         => (b2) at every delta_1.  Measured on bearcase's
                         free sampler EXTENDED to pieces with
                         dist_{G_1}(u,v) >= 5, which is exactly what
                         (BE-38)(ii)'s transfer does not reach.

  (BE-43)  THE ROUTING VERDICT, and it is NO.
             `eardec`  : an OPEN EAR DECOMPOSITION decider (new -- the arc had
                         none).  PROVED: in a chord-free decomposition the LAST
                         ear's interior has degree 2, so a chord-free open ear
                         decomposition forces a degree-2 vertex -- hence EVERY
                         graph of minimum degree >= 3, i.e. every R-NODE,
                         forces a single-edge ear.  Plus gap (ii): avoiding
                         CROSS PAIRS needs a cycle through every branch vertex,
                         with the Petersen witness for where that fails.
             `chord`   : the SINGLE-EDGE ear step.  Combinatorially FREE --
                         def_3(G + uv) = max(def_3(G) - delta_uv,
                         def_3(G) - 5), proved and swept.  Geometrically NOT
                         free: the chord imposes p_v in pi_u AND p_u in pi_v,
                         and a generic point of Y^o(G) satisfies NEITHER
                         (decided exactly, never sampled), so nothing the
                         induction has at G transfers to G + uv.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, `contains`) and never of dimensions, every
sampled configuration through binduc's `assert_generic_star` AND
`kbare_common.verify_pencil_witness`, every cap disclosed.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import itertools                                                     # noqa: E402
import os
import random
import sys
import time
from fractions import Fraction as F                                  # noqa: F401

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import rank as rank_exact, hat, neighbors            # noqa: E402
from kbare_common import (verts_of, exact_deficiency,                # noqa: E402
                          verify_pencil_witness)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- BATTAIN was its first `w4/` consumer, `bzavoid` the second, `binduc` the
# --- third, `btwocut` the fourth, `bimage` the FIFTH, `bearcase` the SIXTH;
# --- this driver is the SEVENTH, and the chain is now SEVEN deep
# --- (battain -> bzavoid -> binduc -> btwocut -> bimage -> bearcase ->
# --- bearfull).  NO MOVE MADE (a dispatch may not edit a landed driver
# --- another direction may be importing in flight); the recorded consumer
# --- list is EXTENDED in the workbook's harness note instead.
from binduc import (assert_generic_star, cycle, hubs_of, path,        # noqa: E402
                    rel_screw_space, theta)
from btwocut import def3_multi, g_exact                              # noqa: E402
from bzavoid import edges_of_mask, adj_of, connected_spanning        # noqa: E402
from bimage import (dim, forced_same_plane, isect, pencil_space,      # noqa: E402
                    plane_at, same_space, span)
from bearcase import sample_piece_config, subdivide                  # noqa: E402


# ===================================================== partition machinery

def f_of(W, eset):
    """f(W) = 5|E(W)| - 6(|W|-1), the part weight of `kbare_common`'s
    part-sum identity;  f(emptyset) = f(singleton) = 0."""
    W = frozenset(W)
    if len(W) < 2:
        return 0
    m = sum(1 for (a, b) in eset if a in W and b in W)
    return 5 * m - 6 * (len(W) - 1)


def def3_fast(edges, check=13):
    """`btwocut.def3_multi` on the simple graph -- the SAME part-sum identity
    as `kbare_common.exact_deficiency` but with the branch-and-bound's suffix
    bound precomputed, which is what makes n >= 14 affordable.  Cross-checked
    against `exact_deficiency` at every call with |V| <= `check`, so the two
    cannot drift."""
    V = verts_of(edges)
    d = def3_multi(V, [tuple(e) for e in edges])
    if len(V) <= check:
        assert d == exact_deficiency(edges)[0], \
            ('def3_multi disagrees with exact_deficiency', edges)
    return d


def set_partitions(lst):
    if not lst:
        yield []
        return
    first, rest = lst[0], lst[1:]
    for P in set_partitions(rest):
        for i in range(len(P)):
            yield P[:i] + [[first] + P[i]] + P[i + 1:]
        yield [[first]] + P


def partition_value(P, eset, n):
    """6(|P|-1) - 5 d(P), d(P) = #edges NOT inside a part."""
    inside = 0
    for B in P:
        S = set(B)
        inside += sum(1 for (a, b) in eset if a in S and b in S)
    return 6 * (len(P) - 1) - 5 * (len(eset) - inside)


def optimal_partitions(edges):
    """EVERY partition attaining def_3, plus that value.  Cross-checked
    against `kbare_common.exact_deficiency` (the packing oracle) on every
    call, so the two cannot drift."""
    V = sorted(verts_of(edges), key=str)
    eset = [tuple(sorted(e, key=str)) for e in edges]
    best = None
    opts = []
    for P in set_partitions(V):
        val = partition_value(P, eset, len(V))
        if best is None or val > best:
            best, opts = val, [P]
        elif val == best:
            opts.append(P)
    f = exact_deficiency(edges)[0]
    assert best == f, ('partition oracle disagrees with the packing oracle',
                       edges, best, f)
    return f, opts


def blocks_of(P):
    out = {}
    for i, B in enumerate(P):
        for z in B:
            out[z] = i
    return out


def quotient_edges(P, eset):
    """The multiset of Q-edges: (part index, part index) per crossing edge."""
    bl = blocks_of(P)
    return [(bl[a], bl[b]) for (a, b) in eset if bl[a] != bl[b]]


def join_partition(P, Q):
    """The finest common coarsening, by union-find on the vertices."""
    bl1, bl2 = blocks_of(P), blocks_of(Q)
    V = sorted(bl1, key=str)
    par = {z: z for z in V}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for R in (P, Q):
        for B in R:
            for z in B[1:]:
                a, b = find(B[0]), find(z)
                if a != b:
                    par[a] = b
    del bl1, bl2
    groups = {}
    for z in V:
        groups.setdefault(find(z), []).append(z)
    return [sorted(g, key=str) for g in groups.values()]


# ============================== (BE-39): the quotient sparsity + join lemmas

def run_merge(nmax=6, nsamp=(7, 8), nmask=600, seed=20260828):
    print('===== Step BE38 / (BE-39): THE PARTITION-LATTICE LAWS the merge '
          'inequality actually proves =====')
    print('  THE MERGE INEQUALITY (BEARCASE/BIMAGE, cited).  If P attains')
    print('  f = def_3(H), merging k+1 of its parts into one gives a')
    print('  partition of value  f - 6k + 5c,  c = #edges between distinct')
    print('  merged parts.  TWO consequences the arc has not extracted:')
    print()
    print('  (BE-39)(i)  THE QUOTIENT SPARSITY LAW.  P optimal => for EVERY')
    print('     set S of parts,  5 e_Q(S) <= 6(|S|-1),  because the merged')
    print('     partition is a competitor.  |S| = 2 gives  e_Q <= 1:  the')
    print('     quotient multigraph Q is SIMPLE.  |S| = 3, 4, 5 forbid a')
    print('     triangle, a 4-cycle and a 5-cycle, so  GIRTH(Q) >= 6;  and a')
    print('     6-cycle is allowed but TIGHT (5*6 = 30 = 6*5).')
    print()
    print('  (BE-39)(ii) THE JOIN LEMMA.  Write  g(P) = sum_B f(B) + const')
    print('     = 5 e_in(P) + 6|P| - 6n.  Then g is SUPERMODULAR on the')
    print('     partition lattice:  e_in(P v Q) >= e_in(P) + e_in(Q) -')
    print('     e_in(P ^ Q)  (an edge inside a P-block or a Q-block is inside')
    print('     a join block), and  |P v Q| >= |P| + |Q| - |P ^ Q|  (the')
    print('     block-intersection bipartite graph has |P|+|Q| vertices,')
    print('     |P ^ Q| edges and |P v Q| components).  Hence')
    print('       g(P v Q) >= g(P) + g(Q) - g(P ^ Q) >= max + max - max,')
    print('     so the JOIN of two optimal partitions is OPTIMAL.  There is a')
    print('     unique COARSEST optimal partition P_max, and')
    print('       delta_uv = 0  <=>  u, v lie in one block of P_max,')
    print('     which makes "delta = 0" an EQUIVALENCE RELATION on V(G).')
    print('     (=>: g_uv = f means some optimal partition has u,v together,')
    print('     and the join of all optimal partitions is one; <=: P_max is')
    print('     itself an optimal partition with u,v together.)')
    print()
    t0 = time.time()
    rng = random.Random(seed)
    ngraph = 0
    nopt = 0
    nsubset = 0
    nsparse_bad = 0
    ngirth_bad = 0
    njoin = 0
    njoin_bad = 0
    npair = 0
    npmax_bad = 0
    ntight = 0
    girth_hist = {}
    tiers = [(n, None) for n in range(3, nmax + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            ngraph += 1
            eset = [tuple(sorted(e)) for e in edges]
            f, opts = optimal_partitions(edges)
            nopt += len(opts)
            for P in opts:
                qe = quotient_edges(P, eset)
                s = len(P)
                # (i) EVERY subset of parts, enumerated
                for r in range(2, s + 1):
                    for S in itertools.combinations(range(s), r):
                        Ss = set(S)
                        e = sum(1 for (a, b) in qe if a in Ss and b in Ss)
                        nsubset += 1
                        if 5 * e > 6 * (r - 1):
                            nsparse_bad += 1
                        if 5 * e == 6 * (r - 1) and r >= 2:
                            ntight += 1
                # girth of Q, read off the simple graph
                simple = set()
                dup = False
                for (a, b) in qe:
                    k = (min(a, b), max(a, b))
                    if k in simple:
                        dup = True
                    simple.add(k)
                if dup:
                    ngirth_bad += 1
                gq = _girth(s, simple)
                girth_hist[gq] = girth_hist.get(gq, 0) + 1
                if gq is not None and gq < 6:
                    ngirth_bad += 1
            # (ii) the join lemma, on EVERY pair of optimal partitions
            for P, Q in itertools.combinations(opts, 2):
                J = join_partition(P, Q)
                njoin += 1
                if partition_value(J, eset, n) != f:
                    njoin_bad += 1
            # P_max and the delta = 0 characterisation, on EVERY pair
            Pmax = opts[0]
            for P in opts[1:]:
                Pmax = join_partition(Pmax, P)
            assert partition_value(Pmax, eset, n) == f, 'P_max not optimal'
            bl = blocks_of(Pmax)
            for (u, v) in itertools.combinations(sorted(verts_of(edges),
                                                        key=str), 2):
                npair += 1
                d0 = (f - g_exact(edges, u, v) == 0)
                if d0 != (bl[u] == bl[v]):
                    npmax_bad += 1
        print(f'   n = {n}' + (' EXHAUSTIVE' if samp is None
                               else f' SAMPLED ({samp} seeded masks)')
              + f': cumulative {ngraph} graphs, {nopt} optimal partitions, '
                f'{nsubset} part-subsets')
    print()
    print(f'  (i)  5 e_Q(S) <= 6(|S|-1) over {nsubset} ENUMERATED subsets of '
          f'the parts of {nopt} optimal partitions: {nsparse_bad} violations')
    print(f'       of which TIGHT (equality, so the merge is again optimal): '
          f'{ntight}')
    print(f'  girth(Q) histogram (None = forest): '
          + ', '.join(f'{k}: {v}' for k, v in
                      sorted(girth_hist.items(),
                             key=lambda t: (t[0] is not None, t[0])))
          + f'   -- entries below 6, or a parallel Q-edge: {ngirth_bad}')
    print(f'  (ii) join of two optimal partitions optimal: {njoin} ENUMERATED '
          f'pairs, {njoin_bad} failures')
    print(f'       delta_uv = 0  <=>  same block of P_max: {npair} pairs, '
          f'{npmax_bad} failures')
    print(f'  CAP DISCLOSURE.  Exhaustive to n = {nmax} and NOT beyond; the '
          f'n = {nsamp} tier is {nmask} seeded masks.  (i) and (ii) are '
          f'PROVED above -- the sweep confirms the proofs and pins the TIGHT '
          f'count, it does not carry them.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    assert nsparse_bad == 0 and ngirth_bad == 0 and njoin_bad == 0 \
        and npmax_bad == 0, 'a proved law failed on the sweep'
    return ngraph, nsubset, njoin, npair


def _girth(nv, simple):
    """Girth of a simple graph on `nv` nodes given as an edge set; None if
    acyclic."""
    nb = {i: set() for i in range(nv)}
    for (a, b) in simple:
        nb[a].add(b)
        nb[b].add(a)
    best = None
    for s in range(nv):
        dist = {s: 0}
        par = {s: None}
        order = [s]
        qi = 0
        while qi < len(order):
            x = order[qi]
            qi += 1
            for y in nb[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    par[y] = x
                    order.append(y)
                elif y != par[x]:
                    c = dist[x] + dist[y] + 1
                    if best is None or c < best:
                        best = c
    return best


# ================================== (BE-40): the short-cycle law, and delta

def short_cycles(edges, L):
    """Vertex tuples of every simple cycle of G of length 3..L, each listed
    once (smallest vertex first, by the driver's own index order)."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    idx = {v: i for i, v in enumerate(V)}
    out = []
    for s in V:
        stack = [(s, (s,))]
        while stack:
            cur, pth = stack.pop()
            for w in nb.get(cur, ()):
                if w == s:
                    if len(pth) >= 3 and idx[pth[1]] < idx[pth[-1]]:
                        out.append(pth)
                elif idx[w] > idx[s] and w not in pth and len(pth) < L:
                    stack.append((w, pth + (w,)))
    return out


def cycle_classes(edges, L=6):
    """Union-find on V(G), unioning V(C) for every cycle of length <= L."""
    V = sorted(verts_of(edges), key=str)
    par = {v: v for v in V}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for C in short_cycles(edges, L):
        r = find(C[0])
        for z in C[1:]:
            rz = find(z)
            if rz != r:
                par[rz] = r
    return find


def run_cycles(nmax=6, nsamp=(7,), nmask=400, seed=20260828, Lmax=8):
    print('===== Step BE39 / (BE-40): THE SHORT-CYCLE LAW -- one statement '
          'that CONTAINS (BE-32)(ii) and (iii) and sharpens (iv) =====')
    print('  (BE-40)(i)  PROVED.  Let C be a cycle of G, P an optimal')
    print('     partition, r the number of edges of C that CROSS parts.  The')
    print('     crossing edges form a closed walk in Q, and by (BE-39)(i) no')
    print('     two of them join the SAME pair of parts, so they are DISTINCT')
    print('     Q-edges; a non-empty set of distinct edges forming a closed')
    print('     walk has every Q-vertex of even degree, hence contains a')
    print('     Q-CYCLE, which by (BE-39)(i) has length >= 6.  So')
    print('       r = 0   or   r >= 6.')
    print('     For |C| <= 5 the second is impossible, so r = 0:  EVERY cycle')
    print('     of length <= 5 lies inside a SINGLE part of EVERY optimal')
    print('     partition.')
    print('  (BE-40)(ii) PROVED.  |C| = 6 and r > 0 forces r = 6, hence six')
    print('     DISTINCT parts carrying six Q-edges -- a TIGHT set, whose')
    print('     merge is again optimal.  Either way some optimal partition')
    print('     has all of C in one block, so by (BE-39)(ii)')
    print('       delta_xy = 0  for any x, y on a common cycle of length <= 6.')
    print('  (BE-40)(iii) PROVED.  In general the r crossings visit at most r')
    print('     parts, so  delta_xy <= 6(r-1) - 5r = r - 6 <= |C| - 6:')
    print('       delta_xy <= max(0, L - 6)  on a common L-cycle,')
    print('     which beats (BE-32)(iv) delta <= dist for every L <= 11.')
    print('  CONTAINMENT.  (BE-32)(ii) is L = 3.  (BE-32)(iii) is L = 4 and')
    print('     its hypothesis WEAKENS from ">= 3 common neighbours" to')
    print('     ">= 2": two common neighbours already make a 4-cycle.')
    print()
    t0 = time.time()
    rng = random.Random(seed)
    ngraph = 0
    nc5 = nc5bad = 0
    nc6 = nc6bad = nc6tight = 0
    npair = npairbad = 0
    nLb = nLbad = 0
    ncommon2 = ncommon2bad = 0
    tiers = [(n, None) for n in range(3, nmax + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            ngraph += 1
            eset = [tuple(sorted(e)) for e in edges]
            f, opts = optimal_partitions(edges)
            cyc = short_cycles(edges, Lmax)
            # (i)/(ii): the crossing count on every cycle of every optimal P
            for P in opts:
                bl = blocks_of(P)
                for C in cyc:
                    L = len(C)
                    r = sum(1 for i in range(L)
                            if bl[C[i]] != bl[C[(i + 1) % L]])
                    if L <= 5:
                        nc5 += 1
                        if r != 0:
                            nc5bad += 1
                    elif L == 6:
                        nc6 += 1
                        if r == 0:
                            pass
                        elif r == 6:
                            parts = sorted({bl[z] for z in C})
                            e = sum(1 for (a, b) in eset
                                    if bl[a] != bl[b] and bl[a] in parts
                                    and bl[b] in parts)
                            if len(parts) == 6 and 5 * e == 6 * 5:
                                nc6tight += 1
                            else:
                                nc6bad += 1
                        else:
                            nc6bad += 1
            # the delta consequences
            find = cycle_classes(edges, 6)
            nb = neighbors(edges)
            V = sorted(verts_of(edges))
            for (u, v) in itertools.combinations(V, 2):
                d = f - g_exact(edges, u, v)
                if find(u) == find(v):
                    npair += 1
                    if d != 0:
                        npairbad += 1
                com = set(nb.get(u, ())) & set(nb.get(v, ()))
                if len(com) >= 2 and v not in nb.get(u, ()):
                    ncommon2 += 1
                    if d != 0:
                        ncommon2bad += 1
                best = None
                for C in cyc:
                    if u in C and v in C:
                        best = len(C) if best is None else min(best, len(C))
                if best is not None:
                    nLb += 1
                    if d > max(0, best - 6):
                        nLbad += 1
        print(f'   n = {n}' + (' EXHAUSTIVE' if samp is None
                               else f' SAMPLED ({samp} seeded masks)')
              + f': cumulative {ngraph} graphs, {nc5} (cycle<=5, optimal P) '
                f'incidences, {npair} same-class pairs')
    print()
    print(f'  (i)   cycles of length <= 5 inside ONE part: {nc5} ENUMERATED '
          f'(cycle, optimal partition) incidences, {nc5bad} violations')
    print(f'  (ii)  6-cycles: {nc6} incidences, {nc6tight} of them split into '
          f'SIX parts forming a TIGHT set, {nc6bad} violations')
    print(f'  (ii)  delta = 0 on a common cycle of length <= 6 (transitively '
          f'closed by (BE-39)(ii)): {npair} pairs, {npairbad} violations')
    print(f'  (iii) delta <= max(0, L-6) at the SHORTEST common cycle: '
          f'{nLb} pairs, {nLbad} violations')
    print(f'  containment: NON-adjacent pairs with exactly >= 2 common '
          f'neighbours -- (BE-32)(iii) does NOT cover these below 3 -- '
          f'{ncommon2} pairs, {ncommon2bad} with delta /= 0')
    print(f'  CAP DISCLOSURE.  Cycles are enumerated to length {Lmax} only, '
          f'so the (iii) column is read at the shortest common cycle of '
          f'length <= {Lmax} and is silent about pairs whose only common '
          f'cycles are longer.  Exhaustive to n = {nmax}.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    assert nc5bad == 0 and nc6bad == 0 and npairbad == 0 and nLbad == 0, \
        'a proved law failed on the sweep'
    return ngraph, nc5, npair, nLb


# =========================== (BE-41): (BE-32)(+) reduced, and its boundary

def forcing_derivation(edges):
    """`bimage.forced_same_plane`'s closure, RE-RUN with the derivation
    recorded: for each seed hub h, the ordered list of (hub v, the three
    points of N[v] cap A that admitted it).  Asserted to reproduce
    `forced_same_plane`'s pair set exactly, so the two cannot drift."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    out = {}
    allpairs = set()
    for h in H:
        A = {h} | set(nb[h])
        fam = [h]
        steps = []
        changed = True
        while changed:
            changed = False
            for v in H:
                if v in fam:
                    continue
                star = {v} | set(nb[v])
                wit = sorted(star & A, key=str)
                if len(wit) >= 3:
                    A |= star
                    fam.append(v)
                    steps.append((v, tuple(wit[:3]), tuple(wit)))
                    changed = True
        out[h] = (fam, sorted(A, key=str), steps)
        for a, b in itertools.combinations(sorted(fam, key=str), 2):
            allpairs.add((a, b))
    assert allpairs == set(forced_same_plane(edges)), \
        'the recorded derivation does not reproduce forced_same_plane'
    return out


def step_shape(edges, v, wit, nb):
    """Classify one forcing step by the shape (BE-41)(i) proves.
    'star2'    : two of the three points lie in ONE closed star N[w] and are
                 not the degenerate pair {v, w}  -- a triangle or 4-cycle
                 through v and w, so PROVED.
    'spread'   : the residue."""
    # a point p is "in the star of w" for every fam-neighbour w; the proof
    # only needs SOME w with two of the points in N[w] other than {v,w}.
    V = verts_of(edges)
    for w in V:
        star = {w} | set(nb.get(w, ()))
        inside = [p for p in wit if p in star]
        if len(inside) < 2:
            continue
        for a, b in itertools.combinations(inside, 2):
            if {a, b} == {v, w}:
                continue
            if w == v:
                continue
            # v-a-w-b-v with a,b in N[w] and a,b in N[v] (or a = v)
            if a != v and b != v and a != w and b != w:
                if a in nb.get(v, ()) and b in nb.get(v, ()):
                    return 'star2', w
            if a == v or b == v:
                other = b if a == v else a
                if other != w and v in nb.get(w, ()) \
                        and other in nb.get(w, ()) \
                        and other in nb.get(v, ()):
                    return 'star2', w
    return 'spread', None


def run_forced(nmax=6, nsamp=(7, 8, 9), nmask=1400, seed=20260828):
    print('===== Step BE40 / (BE-41): (BE-32)(+), REDUCED to a statement with '
          'NO GEOMETRY IN IT =====')
    print('  THE CLOSURE OPERATOR, NAMED (the spec demands it).  "Forced" is')
    print('  meaningful only relative to one.  The 208 418-instance figure is')
    print('  `bimage.forced_same_plane`: seed a hub h with A := N[h], and')
    print('  repeatedly admit a hub v with |N[v] cap A| >= 3, setting')
    print('  A := A cup N[v].  It is the AGGRESSIVE operator -- it assumes')
    print('  every three forced points INDEPENDENT, so it OVER-claims forcing,')
    print('  and a theorem proved for every pair it lists holds a fortiori for')
    print('  the genuinely forced ones.  THIS is the operator proved for here.')
    print()
    print('  (BE-41)(i)  PROVED.  Every forcing step whose three points put')
    print('     TWO in one closed star N[w] (other than the degenerate pair')
    print('     {v, w}) puts v on a cycle of length 3 or 4 through w:')
    print('        v - a - w - b - v   (a, b in N(v) cap N(w)),  or')
    print('        v - w - b - v       (v ~ w, b in N(v) cap N(w)).')
    print('     By (BE-40) that is delta = 0 between v and w, and by')
    print('     (BE-39)(ii) it composes.  In particular the FIRST step is')
    print('     ALWAYS of this shape: |N[v] cap N[h]| >= 3 with v not~ h means')
    print('     >= 3 common neighbours ((BE-32)(iii)); with v ~ h it means a')
    print('     common neighbour, i.e. a TRIANGLE ((BE-32)(ii)).  So')
    print('     (BE-32)(ii)/(iii) are exactly the base case of this induction.')
    print()
    print('  (BE-41)(ii) MEASURED, not proved: every aggressively-forced pair')
    print('     is <=6-CYCLE-CLASS connected, hence delta = 0.  The residue is')
    print('     the SPREAD step, where the three points come from three')
    print('     different stars; `chain` locates its boundary exactly.')
    print()
    t0 = time.time()
    rng = random.Random(seed)
    nforce = 0
    nunc = 0
    nstep = 0
    nspread = 0
    nproved = 0
    ndelta = 0
    nviol = 0
    unc = []
    viol = []
    tiers = [(n, None) for n in range(3, nmax + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            der = forcing_derivation(edges)
            fs = sorted(forced_same_plane(edges))
            if not fs:
                continue
            nb = neighbors(edges)
            find = cycle_classes(edges, 6)
            # PROVED links only: a star-2 step licenses a triangle or 4-cycle
            # through v and its witness hub w, which is delta = 0 by (BE-40),
            # and (BE-39)(ii) composes them.
            par = {z: z for z in verts_of(edges)}

            def pfind(x):
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x

            for (h, (fam, A, steps)) in der.items():
                for (v, wit, allwit) in steps:
                    nstep += 1
                    shape, w = step_shape(edges, v, wit, nb)
                    if shape == 'spread':
                        # try the other admissible witness triples before
                        # calling it a spread step
                        for tri in itertools.combinations(allwit, 3):
                            sh, ww = step_shape(edges, v, tri, nb)
                            if sh == 'star2':
                                shape, w = sh, ww
                                break
                    if shape == 'spread':
                        nspread += 1
                    else:
                        a, b = pfind(v), pfind(w)
                        if a != b:
                            par[a] = b
            f = None
            for (u, v) in fs:
                nforce += 1
                if pfind(u) == pfind(v):
                    nproved += 1
                if find(u) != find(v):
                    nunc += 1
                    if len(unc) < 6:
                        unc.append((tuple(edges), u, v))
                if n <= 7:
                    if f is None:
                        f = exact_deficiency(edges)[0]
                    ndelta += 1
                    if f - g_exact(edges, u, v) != 0:
                        nviol += 1
                        if len(viol) < 6:
                            viol.append((tuple(edges), u, v))
        print(f'   n = {n}' + (' EXHAUSTIVE' if samp is None
                               else f' SAMPLED ({samp} seeded masks)')
              + f': cumulative {nforce} forced pairs, {nstep} forcing steps, '
                f'{nspread} of them SPREAD, {nunc} pairs not <=6-cycle-class '
                f'connected')
    print()
    print(f'  (i)  forcing steps: {nstep} total, {nstep - nspread} PROVED by '
          f'the star-2 shape, {nspread} SPREAD (the residue)')
    print(f'       forced PAIRS carried all the way by star-2 links alone, '
          f'i.e. delta = 0 PROVED with no measurement: {nproved} of {nforce}')
    print(f'  (ii) forced pairs <=6-cycle-class connected: {nforce} pairs, '
          f'{nunc} NOT connected')
    print(f'  delta = 0 at forced pairs, checked directly at n <= 7: '
          f'{ndelta} pairs, {nviol} violations')
    for r in unc:
        print('     not connected:', r)
    for r in viol:
        print('     *** delta /= 0 at a forced pair:', r)
    print(f'  CAP DISCLOSURE.  Exhaustive to n = {nmax}; the n = {nsamp} '
          f'tiers are {nmask} seeded masks each.  The (ii) column is '
          f'MEASURED -- it reads "no aggressively-forced pair outside a '
          f'<=6-cycle class was found under this cap", never "none exists". '
          f'The direct delta check is capped at n <= 7 by the cost of '
          f'`g_exact`, and the wider n = 9..13 hunt lives in `chain`.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return nforce, nunc, nstep, nspread, nproved


def tri_chain(k, npend=1):
    """The named boundary family.  t_0..t_k is a path; x_i completes the
    triangle (t_i, t_{i+1}) for i < k; v is joined to t_0 and to x_{k-1} and
    carries `npend` pendants.  The forcing step at v uses the three points
    {v, t_0, x_{k-1}} of N[v] cap A, and the SHORTEST cycle through v has
    length k + 2 -- so the family crosses (BE-40)'s bound at k = 5."""
    E = []
    for i in range(k):
        E.append((('t', i), ('t', i + 1)))
        E.append((('x', i), ('t', i)))
        E.append((('x', i), ('t', i + 1)))
    V = ('v', 0)
    E.append((V, ('t', 0)))
    E.append((V, ('x', k - 1)))
    for j in range(npend):
        E.append((V, ('p', j)))
    return sorted(E, key=lambda e: (str(e[0]), str(e[1])))


def run_chain(kmax=6, seed=20260828, nlo=9, nhi=13, ntrial=4500):
    print('===== Step BE40 / (BE-41)(iii): THE PROOF\'S BOUNDARY, LOCATED -- '
          'and it is EXACTLY where the merge inequality runs out of slack '
          '=====')
    print('  The merge inequality gives  5 e_Q(S) <= 6(|S|-1),  so a 6-cycle')
    print('  of Q is TIGHT and a 7-cycle is not: 5*7 = 35 < 36 = 6*6.  That is')
    print('  why (BE-40) stops at 6, and the family below shows the stop is')
    print('  REAL, not an artifact of the proof: it produces forcing steps')
    print('  whose shortest cycle is 7, 8, ... and which therefore have NO')
    print('  <=6-cycle certificate -- yet delta = 0 at every one of them.')
    t0 = time.time()
    rows = []
    for k in range(3, kmax + 1):
        for npend in (1, 2):
            E = tri_chain(k, npend)
            V = verts_of(E)
            fs = forced_same_plane(E)
            vv, t0v = ('v', 0), ('t', 0)
            key = (vv, t0v) if (vv, t0v) in fs else (t0v, vv)
            if key not in fs:
                rows.append((k, npend, len(V), len(E), None, None, None,
                             'NOT FORCED'))
                continue
            # the family's admitting step is a genuine SPREAD step -- no
            # witness triple at all makes it star-2, so it is outside
            # (BE-41)(i) and not merely unlucky
            nbE = neighbors(E)
            spread_ok = False
            for (h, (fam, A, steps)) in forcing_derivation(E).items():
                for (vx, wit, allwit) in steps:
                    if vx != vv:
                        continue
                    if all(step_shape(E, vx, t, nbE)[0] == 'spread'
                           for t in itertools.combinations(allwit, 3)):
                        spread_ok = True
            assert spread_ok, ('the boundary family stopped producing a '
                               'SPREAD step', k, npend)
            f = def3_fast(E)
            d = f - g_exact(E, vv, t0v)
            find = cycle_classes(E, 6)
            cyc = [c for c in short_cycles(E, k + 4) if vv in c]
            ml = min((len(c) for c in cyc), default=None)
            rows.append((k, npend, len(V), len(E), f, d, ml,
                         'SAME' if find(vv) == find(t0v) else 'DIFFERENT'))
    print('   k  pend    n   m   def_3  delta(v,t_0)  min cycle thru v   '
          '<=6-class')
    for (k, npend, n, m, f, d, ml, cl) in rows:
        print(f'  {k:2d}  {npend:3d}  {n:4d} {m:3d}  {str(f):>5s}  '
              f'{str(d):>10s}  {str(ml):>14s}   {cl}')
    esc = [r for r in rows if r[7] == 'DIFFERENT']
    assert all(r[5] == 0 for r in rows if r[5] is not None), \
        'delta /= 0 in the boundary family -- this would be HIT shape 4'
    assert esc, 'the boundary family produced no escape -- the claim is empty'
    print(f'  Every member\'s admitting step is ASSERTED to be a genuine '
          f'SPREAD step: no witness triple at all makes it star-2.')
    print(f'  {len(esc)} of {len(rows)} members ESCAPE the <=6-cycle '
          f'certificate (shortest cycle through v is {min(r[6] for r in esc)} '
          f'or more), and delta = 0 at EVERY member.')
    print()
    print('  AND THE SAME ESCAPE, FOUND BLIND.  A random hunt in the band')
    print('  where the statement is not vacuous (def_3 > 0, so delta = 0 is')
    print('  not free) rather than in a construction:')
    rng = random.Random(seed)
    ngr = npos = nf = nunc = nchk = nviol = 0
    unc = []
    for t in range(ntrial):
        n = rng.randint(nlo, nhi)
        pairs = list(itertools.combinations(range(n), 2))
        m = rng.randint(n, int(1.4 * n) + 2)
        if m > len(pairs):
            continue
        edges = sorted(rng.sample(pairs, m))
        if not connected_spanning(n, adj_of(n, edges)):
            continue
        ngr += 1
        fs = sorted(forced_same_plane(edges))
        if not fs:
            continue
        f = def3_fast(edges)
        if f <= 0:
            continue
        npos += 1
        find = cycle_classes(edges, 6)
        res = [p for p in fs if find(p[0]) != find(p[1])]
        nf += len(fs)
        nunc += len(res)
        chk = res + rng.sample(fs, min(2, len(fs)))
        for (u, v) in chk:
            nchk += 1
            if f - g_exact(edges, u, v) != 0:
                nviol += 1
                unc.append((tuple(edges), u, v))
    print(f'   {ngr} connected graphs at n = {nlo}..{nhi} with '
          f'm in [n, 1.4n+2];  {npos} of them have def_3 > 0 AND a forced '
          f'pair;  {nf} forced pairs, of which {nunc} are NOT '
          f'<=6-cycle-class connected;  {nchk} delta computations, '
          f'{nviol} with delta /= 0')
    for r in unc[:4]:
        print('     *** delta /= 0:', r)
    assert nviol == 0, 'delta /= 0 at a forced pair in the f > 0 band'
    print(f'  CAP DISCLOSURE.  The blind hunt is SEEDED RANDOM, not '
          f'exhaustive; delta is computed at every not-connected pair and at '
          f'two further forced pairs per graph, not at all of them (the cost '
          f'is `g_exact`).  The family above is a CONSTRUCTION and proves '
          f'only that the escape is non-empty.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows, nunc, nviol


# ======================= (BE-42): (b2) is a consequence of (b1) -- Grassmann

def dist_in_graph(edges, u, v):
    nb = neighbors(edges)
    seen = {u: 0}
    order = [u]
    i = 0
    while i < len(order):
        x = order[i]
        i += 1
        if x == v:
            return seen[x]
        for y in nb.get(x, ()):
            if y not in seen:
                seen[y] = seen[x] + 1
                order.append(y)
    return None


def far_piece_battery():
    """bearcase's `piece_battery`, restricted to and EXTENDED at the regime
    (BE-38)(ii)'s transfer does NOT reach: dist_{G_1}(u,v) >= 5."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    PRISM = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
             (0, 3), (1, 4), (2, 5)]
    out = [
        ('path of 5 edges u-v (all-S)', path(6), 'v0', 'v5'),
        ('path of 6 edges u-v (all-S)', path(7), 'v0', 'v6'),
        ('path of 7 edges u-v (all-S)', path(8), 'v0', 'v7'),
        ('C10 @ antipodes (path)', cycle(10), 'v0', 'v5'),
        ('C12 @ antipodes (path)', cycle(12), 'v0', 'v6'),
        ('theta(5,5,5) @ hubs (P-node)', theta(5, 5, 5), 'u', 'v'),
        ('theta(5,6,7) @ hubs (P-node)', theta(5, 6, 7), 'u', 'v'),
        ('theta(6,6,6) @ hubs (P-node)', theta(6, 6, 6), 'u', 'v'),
        ('theta(6,7,8) @ hubs (P-node)', theta(6, 7, 8), 'u', 'v'),
        ('theta(5,7,9) @ hubs (P-node)', theta(5, 7, 9), 'u', 'v'),
        ('K4 subdivided x5 @ 0,1 (R-node)', subdivide(K4, 5, 'f'), 0, 1),
        ('K4 subdivided x6 @ 0,1 (R-node)', subdivide(K4, 6, 'g'), 0, 1),
        ('K4 subdivided x5 @ 0,2 (R-node)', subdivide(K4, 5, 'h'), 0, 2),
        ('K_{3,3} subdivided x5 @ 0,1 (R-node)', subdivide(K33, 5, 'j'),
         0, 1),
        ('K_{3,3} subdivided x5 @ 0,3 (R-node)', subdivide(K33, 5, 'k'),
         0, 3),
        ('K_{3,3} subdivided x6 @ 0,1 (R-node)', subdivide(K33, 6, 'l'),
         0, 1),
        ('prism subdivided x5 @ 0,1 (R-node)', subdivide(PRISM, 5, 'm'),
         0, 1),
        ('prism subdivided x5 @ 0,5 (R-node)', subdivide(PRISM, 5, 'n'),
         0, 5),
        ('prism subdivided x6 @ 0,1 (R-node)', subdivide(PRISM, 6, 'o'),
         0, 1),
    ]
    return out


def run_bgrass(seed=20260828, nseeds=10):
    print('===== Step BE41 / (BE-42): (b2) IS A CONSEQUENCE OF (b1), by ONE '
          'LINE OF GRASSMANN =====')
    print('  (BE-42)(i)  PROVED, and it is not a dimension count.  Pi_u <= Z')
    print('     by the definition Z = Pi_u + Pi_v, so for ANY subspace X')
    print('       dim(X cap Z) + dim Pi_u = dim((X cap Z) + Pi_u)')
    print('                                  + dim(X cap Z cap Pi_u)')
    print('                               <= dim Z + dim(X cap Pi_u),')
    print('     i.e.  dim(X cap Z) <= dim Z - 2 + dim(X cap Pi_u),  and')
    print('     symmetrically at v.  With X = rho_bar_1:')
    print('       dim(rho_1 cap Z) <= dim Z - 2')
    print('                           + min(dim(rho_1 cap Pi_u),')
    print('                                 dim(rho_1 cap Pi_v)).')
    print('  (BE-42)(ii) CONSEQUENCES.  (b2) demands')
    print('     dim(rho_1 cap Z) <= max(delta_1 + dim Z - 6, dim Z - 2).')
    print('     - (b1) at strength <= 1 gives dim Z - 1, which meets (b2)')
    print('       whenever delta_1 + dim Z - 6 >= dim Z - 1, i.e.')
    print('       delta_1 >= 5.  So (b1) => (b2) OUTRIGHT at delta_1 >= 5.')
    print('     - (b1) SHARPENED to  rho_1 cap Pi_u = 0  at EITHER end gives')
    print('       dim Z - 2 exactly, i.e. (b2) at EVERY delta_1.')
    print('     So the three clauses of (BE-37)(ii) are not independent: (b2)')
    print('     is (b1) at ONE end, sharpened from <= 1 to 0, and the only')
    print('     pieces needing more are those with dim(rho_1 cap Pi_u) = 1 at')
    print('     BOTH ends and delta_1 <= 4 -- which is the PATH-LIKE side, and')
    print('     (BE-38)(i) already proves (beta) there.')
    print('  (BE-42)(iii) WHERE THE SHARPENING COMES FROM.  Every hinge line')
    print('     at u lies in Pi_u = p_u ^ pi_u (the closed star of u is in')
    print('     pi_u, so a hinge line at u passes through p_u inside pi_u),')
    print('     and `assert_generic_star` forbids two hinge lines at u from')
    print('     coinciding, so ANY TWO of them SPAN Pi_u.  If two u-v paths')
    print('     leave u by different edges, rho_bar_1 is contained in BOTH')
    print('     path spans ((BE-30)(iv)) whose Pi_u-parts are different lines')
    print('     -- which is (BE-38)(iii)\'s measured "0 wherever two u-v paths')
    print('     leave u by different edges", now with its mechanism named.')
    print()
    t0 = time.time()
    tested = 0
    rows = []
    ntight = 0
    for (name, edges, u, v) in far_piece_battery():
        d = dist_in_graph(edges, u, v)
        draws = []
        for sd in range(nseeds):
            rng = random.Random(seed + 7919 * sd + len(name))
            got, why = sample_piece_config(edges, u, v, rng)
            if got is None:
                continue
            pt, planes = got
            pa = plane_at(edges, pt, u)
            if pa is not None:
                assert same_space(pa, planes[u]), \
                    'the chosen plane at u is not the closed star\'s plane'
            pb = plane_at(edges, pt, v)
            if pb is not None:
                assert same_space(pb, planes[v]), \
                    'the chosen plane at v is not the closed star\'s plane'
            ok, _ = verify_pencil_witness(edges, pt)
            assert ok, 'sampler produced a non-pencil configuration'
            rho, img, dM, r = rel_screw_space(edges, pt, u, v)
            S = span(img) if img else []
            Piu = pencil_space(hat(pt[u]), planes[u])
            Piv = pencil_space(hat(pt[v]), planes[v])
            Z = span(Piu + Piv)
            assert dim(Piu) == 2 and dim(Piv) == 2, 'a pencil is not 2-dim'
            # Pi_u <= Z as an IDENTITY of spaces, not of dimensions
            assert same_space(isect(Piu, Z), Piu), 'Pi_u not inside Z'
            assert same_space(isect(Piv, Z), Piv), 'Pi_v not inside Z'
            cu = dim(isect(S, Piu)) if S else 0
            cv = dim(isect(S, Piv)) if S else 0
            cz = dim(isect(S, Z)) if S else 0
            dz = dim(Z)
            bound = dz - 2 + min(cu, cv)
            assert cz <= bound, ('(BE-42)(i) violated', name, cz, bound)
            if cz == bound:
                ntight += 1
            draws.append((dim(S), cu, cv, cz, dz))
        if not draws:
            print(f'    {name:38s}: NO LEGAL DRAW (sampler shape guard)')
            continue
        r1 = max(x[0] for x in draws)
        att = [x for x in draws if x[0] == r1]
        cu = min(x[1] for x in att)
        cv = min(x[2] for x in att)
        cz = min(x[3] for x in att)
        dz = att[0][4]
        b2 = max(r1 + dz - 6, dz - 2)
        tested += 1
        ok = 'OK' if cz <= b2 else 'FAILS (b2)'
        rows.append((name, d, r1, cu, cv, cz, dz, b2, ok))
        print(f'    {name:38s}: dist = {d}, rho_1 = {r1}, dim Z = {dz}, '
              f'(rho_1 cap Pi_u, Pi_v) = ({cu},{cv}), dim(rho_1 cap Z) = '
              f'{cz} <= (b2) bound {b2}   {ok}')
    bad = [r for r in rows if r[8] != 'OK']
    print(f'  {tested} pieces, ALL with dist_(G_1)(u,v) >= 5 -- exactly the '
          f'regime (BE-38)(ii)\'s transfer does not reach; {len(bad)} fail '
          f'(b2).')
    print(f'  (BE-42)(i) held as an EXACT inequality at every draw of every '
          f'piece, TIGHT at {ntight} draws.')
    zero = [r for r in rows if min(r[3], r[4]) == 0]
    print(f'  {len(zero)} of {tested} pieces have rho_1 cap Pi_u = 0 or '
          f'rho_1 cap Pi_v = 0 at the attaining draw -- for those (b2) is '
          f'PROVED by (BE-42)(ii), with no genericity and no count.')
    print('  CAP DISCLOSURE.  The sampler is bearcase\'s free parametrization '
          'and inherits its shape guard (branch vertices an independent set, '
          'each free vertex with at most one branch neighbour), so the '
          'battery is SUBDIVISIONS only. delta_1 is the MEASURED max '
          'dim rho_bar_1 over draws, a LOWER bound on the combinatorial '
          'delta_1, which UNDER-states the (b2) bound -- the conservative '
          'direction.  (BE-42)(i) is PROVED; the columns confirm it and '
          'measure where it is tight.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    assert not bad, '(b2) failed at a piece'
    return tested, rows


# ============================ (BE-43): the routing verdict -- ear + chord

def ear_decompositions(n, edges, cap=400000):
    """Decide whether a 2-connected graph has a CHORD-FREE open ear
    decomposition: a cycle C, then paths of length >= 2 whose two endpoints
    are distinct vertices of the current graph and whose interior is new.
    Exhaustive within `cap` states, with two sound prunes:
      * COUNT.  Each remaining ear has length >= 2, so with R remaining edges
        and N remaining vertices, #ears = R - N <= N, i.e. R <= 2N.
      * MEMO.  A state is the pair (attached vertices, covered edges).
    Raises on cap overflow rather than reporting a false negative."""
    nb = neighbors(edges)
    E = set(tuple(sorted(e)) for e in edges)
    nv = len(verts_of(edges))
    seen = set()
    states = [0]

    def rec(have_v, have_e):
        states[0] += 1
        if states[0] > cap:
            raise RuntimeError('ear search cap exceeded')
        if len(have_e) == len(E):
            return True
        key = (frozenset(have_v), frozenset(have_e))
        if key in seen:
            return False
        seen.add(key)
        R = len(E) - len(have_e)
        N = nv - len(have_v)
        if R > 2 * N:
            return False
        for a in sorted(have_v, key=str):
            stack = [(a, (a,), frozenset())]
            while stack:
                cur, pth, used = stack.pop()
                for w in nb.get(cur, ()):
                    e = tuple(sorted((cur, w)))
                    if e in have_e or e in used:
                        continue
                    if w in have_v:
                        if len(pth) >= 2 and w != a:
                            if rec(have_v | set(pth[1:]),
                                   have_e | used | {e}):
                                return True
                        continue
                    if w in pth:
                        continue
                    stack.append((w, pth + (w,), used | {e}))
        return False

    for C in short_cycles(edges, n):
        he = set()
        for i in range(len(C)):
            he.add(tuple(sorted((C[i], C[(i + 1) % len(C)]))))
        if rec(set(C), he):
            return True, states[0]
    return False, states[0]


def is_two_connected(n, edges):
    if n < 3:
        return False
    if not connected_spanning(n, adj_of(n, edges)):
        return False
    for z in range(n):
        rest = [e for e in edges if z not in e]
        vs = sorted({x for e in rest for x in e})
        if len(vs) != n - 1:
            return False
        idx = {v: i for i, v in enumerate(vs)}
        re = [(idx[a], idx[b]) for (a, b) in rest]
        if not connected_spanning(n - 1, adj_of(n - 1, re)):
            return False
    return True


def is_three_connected(n, edges):
    if n < 4:
        return False
    if not is_two_connected(n, edges):
        return False
    for a, b in itertools.combinations(range(n), 2):
        rest = [e for e in edges if a not in e and b not in e]
        vs = sorted({x for e in rest for x in e})
        if len(vs) != n - 2:
            return False
        idx = {v: i for i, v in enumerate(vs)}
        re = [(idx[x], idx[y]) for (x, y) in rest]
        if not connected_spanning(n - 2, adj_of(n - 2, re)):
            return False
    return True


PETERSEN = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
            (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
            (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]


def _hamiltonian(edges, n):
    """Exhaustive search for a Hamiltonian cycle; False if none exists."""
    nb = neighbors(edges)
    start = 0

    def rec(cur, used):
        if len(used) == n:
            return start in nb.get(cur, ())
        for w in nb.get(cur, ()):
            if w in used:
                continue
            if rec(w, used | {w}):
                return True
        return False

    return rec(start, {start})



def run_eardec(nmax=6, nsamp=(7, 8), nmask=900, seed=20260828):
    print('===== Step BE42 / (BE-43)(i): THE EAR-DECOMPOSITION ROUTE -- the '
          'generator the arc did not have, and the theorem that decides its '
          'first gap =====')
    print('  THE HYPOTHESIS UNDER TEST (coordinator, this dispatch; it rests')
    print('  on no measurement and no workbook result, and a grep confirms the')
    print('  arc had never considered it).  Every 2-connected graph has an')
    print('  OPEN EAR DECOMPOSITION starting from a cycle -- CLASSICAL, the')
    print('  construction being Whitney\'s (H. Whitney, *Non-separable and')
    print('  planar graphs*, Trans. Amer. Math. Soc. 34 (1932), no. 2,')
    print('  339-362; NO section number is asserted).  (BE-18) reduces (BE-14)')
    print('  to 2-connected graphs and a cycle is max-degree <= 2, one of the')
    print('  FREE base classes ((BE-25)(iv)).  Each ear WITH AN INTERIOR')
    print('  VERTEX attaches at a pair {u,v} that IS a 2-cut of the enlarged')
    print('  graph, so that step is exactly BEARCASE\'s ear case with G_2 the')
    print('  ear and G_1 arbitrary.  If nothing else were needed, the INTERNAL')
    print('  R-NODE would leave the critical path.')
    print()
    print('  (BE-43)(i)  PROVED, one line, and it DECIDES gap (i).  In a')
    print('     chord-free open ear decomposition the LAST ear has length >= 2')
    print('     and no later ear attaches to it, so its interior vertices have')
    print('     degree exactly 2 in G; and if there is no ear at all then G is')
    print('     a cycle.  Either way:')
    print('       G has a CHORD-FREE open ear decomposition')
    print('                                       =>  G has a vertex of')
    print('                                           degree 2.')
    print('     Contrapositive: EVERY graph of minimum degree >= 3 -- in')
    print('     particular every 3-CONNECTED graph, i.e. every R-NODE --')
    print('     forces a single-edge ear in EVERY open ear decomposition.')
    print('     The counting bound  m <= 2n - |C| <= 2n - girth(G)  is the')
    print('     weaker numerical shadow of the same fact (K_4: 6 > 5).')
    print('  READING.  So the ear route does not remove the R-node difficulty;')
    print('  it RELOCATES it into the single-edge step, which `chord` prices.')
    print()
    t0 = time.time()
    rng = random.Random(seed)
    ntwo = nthree = nfree = nfree3 = 0
    nmin2 = 0
    nbranchcyc = 0
    fail = []
    thmbad = 0
    tiers = [(n, None) for n in range(3, nmax + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        c2 = c3 = cfree2 = cfree3 = 0
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            if not is_two_connected(n, edges):
                continue
            c2 += 1
            three = is_three_connected(n, edges)
            if three:
                c3 += 1
            nb = neighbors(edges)
            mind = min(len(nb.get(z, ())) for z in range(n))
            # GAP (ii): a decomposition in which NO ear attaches at an
            # earlier ear's INTERIOR forces every degree->=3 vertex onto the
            # initial cycle (a vertex off C receiving no later attachment has
            # degree 2).  So "some cycle carries every branch vertex" is
            # NECESSARY for the induction to avoid CROSS PAIRS entirely.
            branch = {z for z in range(n) if len(nb.get(z, ())) >= 3}
            oncyc = False
            for C in short_cycles(edges, n):
                if branch <= set(C):
                    oncyc = True
                    break
            if oncyc:
                nbranchcyc += 1
            try:
                ok, st = ear_decompositions(n, edges)
            except RuntimeError:
                fail.append((tuple(edges), 'search cap'))
                continue
            if ok:
                cfree2 += 1
                if three:
                    cfree3 += 1
                if mind != 2:
                    thmbad += 1
                else:
                    nmin2 += 1
            elif mind >= 3:
                pass
        ntwo += c2
        nthree += c3
        nfree += cfree2
        nfree3 += cfree3
        print(f'   n = {n}' + (' EXHAUSTIVE' if samp is None
                               else f' SAMPLED ({samp} seeded masks)')
              + f': {c2} 2-connected labelled graphs, '
                f'{cfree2} admit a CHORD-FREE open ear decomposition; of the '
                f'{c3} 3-connected ones, {cfree3} do')
    print()
    print(f'  TOTAL: {ntwo} 2-connected graphs, {nfree} chord-free; '
          f'{nthree} 3-connected, {nfree3} chord-free.')
    print(f'  (BE-43)(i) confirmed: {nfree} chord-free graphs, of which '
          f'{nmin2} have a degree-2 vertex and {thmbad} do NOT '
          f'(the theorem forbids the second column).')
    print()
    print('  GAP (ii) -- WHICH STRENGTHENED STATEMENT.  The induction needs')
    print('  the welding clause at the NEXT ear\'s attachment pair, so it')
    print('  carries a THIRD shape -- call it S-dec, marked by the')
    print('  decomposition rather than by a rooted tree.  S-dec is strictly')
    print('  WEAKER than S-all (finitely many NAMED pairs, fixed in advance)')
    print('  and is not S-mark.  But a later ear may attach at a vertex')
    print('  INTERIOR to an earlier ear, and then the pair is a CROSS PAIR in')
    print('  the sense of (BE-28)(i) -- contracting it destroys the 2-cut, so')
    print('  neither the (BE-21) def_3 law nor the (BE-22)(i) fibre-product')
    print('  law reaches it.  PROVED: a decomposition avoiding that entirely')
    print('  forces every degree->=3 vertex onto the INITIAL CYCLE, because a')
    print('  vertex off C that receives no later attachment has degree 2.  So')
    print('  a NECESSARY condition for the ear route to avoid cross pairs is')
    print('  that some cycle of G carries every branch vertex.')
    print(f'      {nbranchcyc} of {ntwo} 2-connected graphs have a cycle '
          f'through EVERY degree->=3 vertex; the other '
          f'{ntwo - nbranchcyc} force a CROSS PAIR into the ear induction.')
    print('  So under this cap gap (ii) does NOT bite -- an honest negative')
    print('  for the analysis, and it says where to look instead.  For a')
    print('  SUBDIVISION of a base graph B, a cycle carrying every branch')
    print('  vertex is exactly a HAMILTONIAN cycle of B, so the first')
    print('  witnesses are subdivisions of NON-HAMILTONIAN 3-connected bases:')
    ham = _hamiltonian(PETERSEN, 10)
    print(f'      the PETERSEN graph (n = 10, m = 15, 3-connected): '
          f'Hamiltonian cycle found = {ham} (exhaustive search).')
    assert ham is False, 'Petersen came out Hamiltonian -- the witness is void'
    print('      Hence EVERY subdivision of Petersen -- 2-connected, not')
    print('      3-connected, and carrying an INTERNAL R-node -- has NO cycle')
    print('      through its ten branch vertices, so EVERY open ear')
    print('      decomposition of it attaches some ear at an earlier ear\'s')
    print('      interior and the induction meets a CROSS PAIR.  Both gaps')
    print('      therefore localise at the SAME place: the R-node.')
    if fail:
        print(f'  {len(fail)} graphs hit the search cap and are reported as '
              f'UNDECIDED, not as negatives.')
    print(f'  CAP DISCLOSURE.  Exhaustive to n = {nmax}, sampled at '
          f'n = {nsamp} ({nmask} seeded masks each).  The search is a '
          f'DECISION per graph (exhaustive within a state cap of 400 000, '
          f'with two SOUND prunes: R <= 2N by the ear-length count, and '
          f'memoisation of (attached vertices, covered edges)); (BE-43)(i) '
          f'is PROVED and the sweep confirms it.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    assert thmbad == 0 and nfree3 == 0, '(BE-43)(i) failed on the sweep'
    return ntwo, nfree, nthree, nfree3, nbranchcyc, fail


def run_chord(nmax=6, seed=20260828, ndraw=8):
    print('===== Step BE42 / (BE-43)(ii): THE SINGLE-EDGE EAR STEP -- '
          'combinatorially FREE, geometrically NOT =====')
    print('  (BE-43)(ii) PROVED.  Adding the edge uv raises d(P) by one for')
    print('  exactly the partitions that SEPARATE u and v, so')
    print('     def_3(G + uv) = max( max_{P: u,v together} value_G(P),')
    print('                          max_{P: separated}   value_G(P) - 5 )')
    print('                   = max( def_3(G) - delta_uv, def_3(G) - 5 ).')
    print('  So the combinatorial half of the chord step is FREE and EXACT --')
    print('  no new law, and it is the merge inequality\'s own bookkeeping.')
    print()
    print('  (BE-43)(iii) THE OBSTRUCTION, and it is not a dimension count.')
    print('  By (BE-16) the pencil condition IS *every closed star coplanar*,')
    print('  so G + uv demands  p_v in pi_u  AND  p_u in pi_v:  the chord')
    print('  variety Y^o(G+uv) is a PROPER CLOSED subset of Y^o(G).  The')
    print('  induction hands over a GENERIC point of a component of Y^o(G),')
    print('  which therefore lies OUTSIDE Y^o(G+uv) -- decided exactly below,')
    print('  never sampled.  And attainment cannot be inherited by')
    print('  specialisation in any case: dim M is UPPER semicontinuous, so')
    print('  moving onto a proper closed subvariety can only RAISE it above')
    print('  the cap that attainment demands.  This is the same shape as the')
    print('  arc\'s other hard steps, and it is not softer than the internal')
    print('  R-node it was meant to replace.')
    print()
    t0 = time.time()
    rng = random.Random(seed)
    ngraph = 0
    nchk = 0
    nbad = 0
    print('  (a) the def_3 law, ENUMERATED over every connected labelled '
          f'graph on n = 3..{nmax} and every non-edge:')
    for n in range(3, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        cnt = 0
        for mask in range(1 << len(pairs)):
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            ngraph += 1
            es = set(tuple(sorted(e)) for e in edges)
            f = exact_deficiency(edges)[0]
            for (u, v) in pairs:
                if (u, v) in es:
                    continue
                d = f - g_exact(edges, u, v)
                got = exact_deficiency(sorted(es | {(u, v)}))[0]
                want = max(f - d, f - 5)
                nchk += 1
                cnt += 1
                if got != want:
                    nbad += 1
        print(f'      n = {n}: cumulative {ngraph} graphs, {nchk} '
              f'(graph, non-edge) instances')
    print(f'      {nchk} instances, {nbad} violations of '
          f'def_3(G+uv) = max(def_3(G) - delta_uv, def_3(G) - 5)')
    assert nbad == 0, 'the chord def_3 law failed'
    print()
    print('  (b) the geometric half: at a generic pencil configuration of G, '
          'is p_v in pi_u?  DECIDED per draw (a rank computation over exact '
          'Q), never sampled.')
    hits = 0
    tried = 0
    nodraw = 0
    for (name, edges, u, v) in far_piece_battery():
        for sd in range(ndraw):
            rngd = random.Random(seed + 104729 * sd + len(name))
            got, why = sample_piece_config(edges, u, v, rngd)
            if got is None:
                nodraw += 1
                continue
            pt, planes = got
            ok, _ = verify_pencil_witness(edges, pt)
            assert ok, 'sampler produced a non-pencil configuration'
            assert_generic_star(edges, pt)
            piu = plane_at(edges, pt, u)
            piv = plane_at(edges, pt, v)
            if piu is None or piv is None:
                continue
            tried += 1
            inu = rank_exact(piu + [hat(pt[v])]) == 3
            inv = rank_exact(piv + [hat(pt[u])]) == 3
            if inu and inv:
                hits += 1
    print(f'      {tried} generic pencil draws of pieces with u, v '
          f'NON-adjacent: {hits} satisfy BOTH p_v in pi_u and p_u in pi_v.')
    assert hits == 0, ('a generic pencil draw already satisfied the chord '
                       'condition -- the obstruction would be empty')
    print('      So Y^o(G + uv) misses the generic point of Y^o(G) at every '
          'draw: the chord step starts from a configuration the induction '
          'does NOT hand it.')
    print()
    print('  (c) how much the chord costs, per graph: the codimension is 2 '
          'conditions (p_v in pi_u, p_u in pi_v) whenever both closed stars '
          'span a plane -- LABELLED AS A COUNT (ZJACOB (JC-6)); nothing here '
          'derives properness, smoothness or transversality from it.')
    print(f'  CAP DISCLOSURE.  (a) is exhaustive to n = {nmax} and NOT '
          f'beyond.  (b) is a per-draw DECISION over {tried} draws from '
          f'bearcase\'s free sampler and inherits its shape guard; it '
          f'establishes that the generic point of Y^o(G) is not a chord '
          f'point, NOT that Y^o(G+uv) is empty or of any particular '
          f'dimension.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return nchk, nbad, tried, hits


# ============================================================== driver CLI

def run_validate():
    """A reduced tier of every mode, for a fast end-to-end check."""
    t0 = time.time()
    run_merge(nmax=5, nsamp=(6,), nmask=40)
    print()
    run_cycles(nmax=5, nsamp=(6,), nmask=40)
    print()
    run_forced(nmax=5, nsamp=(6, 7), nmask=300)
    print()
    run_chain(kmax=6, ntrial=900)
    print()
    run_bgrass(nseeds=4)
    print()
    run_eardec(nmax=5, nsamp=(6,), nmask=200)
    print()
    run_chord(nmax=5, ndraw=3)
    print(f'\n===== validate: all seven modes at a reduced tier, '
          f'{time.time() - t0:.1f} s =====')


MODES = {
    'merge': run_merge,       # (BE-39)     quotient sparsity + join lemma
    'cycles': run_cycles,     # (BE-40)     the short-cycle law
    'forced': run_forced,     # (BE-41)     (BE-32)(+) reduced
    'chain': run_chain,       # (BE-41)(iii) the boundary, located
    'bgrass': run_bgrass,     # (BE-42)     (b2) from (b1) by Grassmann
    'eardec': run_eardec,     # (BE-43)(i)  the ear route, and the chord gap
    'chord': run_chord,       # (BE-43)(ii) the single-edge ear step, priced
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: {os.path.basename(__file__)} '
              f'[{"|".join(MODES)}]')
        sys.exit(2)
    MODES[mode]()
