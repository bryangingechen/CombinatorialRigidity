"""GBLAW -- the thirty-fourth kernel-(K) ordinal: (GR-108), the balance
law (spec: notes/Pencil-fanout.md S"GBLAW -- thirty-fourth ordinal").

TARGET: (GR-108) -- at every perfect matching M of a cubic loop-free hub
multigraph with all odd branches inside M, the parity optimum is attained
at a BALANCED pattern: d_adm(M) = d_par(M) (S(K-grid) Step G128).  Minted
and measured by GPRICE (0 violations at 1 431 pairs); NOT a theorem; its
strong form (every structurally-maximum reversal set reaches balance)
fails from exactly n = 12, so a proof must EXCHANGE between maximum
reversal sets.  This pass delivers the exchange CALCULUS and reduces the
law to one named connectivity statement, measured here:

  (GR-110) THE ARC-TRANSVERSAL NORMAL FORM.  Fix the sink set K of a
  valid configuration.  The valid configurations with sink set exactly K
  are precisely the choices of ONE source in the interior of each K-arc
  (the segments between cyclically consecutive sinks on each F-cycle),
  subject to: no even matching pair with both ends chosen, and no odd
  branch with one end chosen and the other in K.  All have |R| = 2|K|.
  Hence a source slides freely inside its arc (dually for sinks) --
  the move calculus's first generator.  (--form asserts the family-by-
  sink-set equality, and the whole labeled-family enumeration against
  the landed rmodel_f per-pattern table.)

  (GR-111) THE RECOMBINATION THEOREM.  For two maximum orientations
  x, y, swap any union of GLUED components of supp(x XOR y) (glued =
  closed under the mixed-state conflicts at matching pairs and odd
  ends): both recombinants are again valid maxima.  Corollary: the
  maximum family is recombination-connected, and at 2k = 2 a law
  failure forces, at EVERY pair (x AA-max, y BB-max), a glued chain
  linking a y-sink end of gamma_1 to an x-source end of gamma_2 -- the
  sharpened refutation shape.  (--recomb asserts the theorem
  mechanically on sampled (x, y, T) triples and measures the
  separation criterion where pos-forcing maxima exist.)

  (GR-112) THE ESCAPE LEMMA.  Each valid configuration's valid patterns
  form a subcube whose imbalance values are an interval of even
  integers [mu, M].  A single source/sink slide, adjacent-pair
  teleport, or safe component flip (a component holding resident ends
  of at most ONE odd branch) shifts mu by at least -2 -- so no single
  move crosses from mu >= 2 (pos-forcing) to M <= -2 (neg-forcing),
  and the FIRST non-pos configuration on any fine-move walk out of a
  pos-forcing maximum is balance-valid.  Hence the balance law follows
  from the ESCAPE statement: from some pos-forcing maximum, some
  fine-move sequence through maxima leaves the pos-forcing class.
  (--conn asserts the no-crossing sentence on every edge it builds.)

  (GR-113) THE MEASURED ESCAPE VERDICT.  --conn builds the full labeled
  maximum family of each swept pair and its fine-move graph at three
  nested move levels (slides; + teleports; + safe flips), and reports
  whether EVERY component containing a pos- or neg-forcing maximum
  also contains a balance-valid one (universal escape -- strictly
  stronger than the law).

Modes:
  --form     (GR-110) + the enumeration cross-assert vs rmodel_f:
             stratum (EXHAUSTIVE) + V8 + the (GR-103) control + a
             seeded n = 12 cell pool.
  --conn     (GR-112)/(GR-113): the fine-move census at three move
             levels on the same pools; the no-crossing assert on every
             edge; escape verdicts histogrammed.
  --recomb   (GR-111) asserted on sampled (x, y, T) triples; the 2k = 2
             separation criterion hunted constructively at every
             pos-forcing maximum of every pos-forcing pair.
  --strand   the no-escape witness in full: the pinned component
             structure and the EXHAUSTIVE separation hunt over its
             stranded maxima (cap-free at this pair: one F-cycle, so
             orientations are config-determined).
  --validate all four.

Sibling imports (S2 rule-2 trips, DISCLOSED -- Harness debt, the move
is the coordinator's, not this dispatch's): `cell_data`, `cell_shapes`,
`gr103_specs`, `pairs_of`, `rmodel_f` from `w4/gprice.py` (all
read-only; every one a candidate for the gridbal_common layer at its
second consumer, which this driver is).  Balance-layer devices come
DIRECTLY from gridbal_common, never via the sibling re-exports.

Rank-free throughout: gexist.fully_good_rank is never imported or called
and no d_fg claim is made anywhere ((a') / input (Y) untouched).  Exact
integers / GF(2); no floating point; every rng seeded, seed printed;
every sampler draws a GRAPH, never a placement (S(K-clos) (AC-9)).
Wall-clock [Ns] annotations are non-deterministic; every other byte is
seed-stable.
"""
import argparse
import collections
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from gridbal_common import imb_of, odd_idx, stratum_cases, v8_specs   # noqa: E402
from gprice import (cell_data, cell_shapes, gr103_specs, pairs_of,    # noqa: E402
                    rmodel_f)
from cflank import cubic_habitat                                      # noqa: E402

R_SEED = 20260825


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  A labeled CONFIGURATION is a
# state tuple sigma in {0 (through/absent), 1 (SOURCE), 2 (SINK)}^n; its
# reversal set R is the support, and it refines GPRICE's reversal-set
# mask by the sink/source labelling, which is what the move calculus
# needs.  `valid_pats` is the first-principles validator every move goes
# through; `enum_family` the exhaustive labeled enumeration; `arcs_of`
# the (GR-110) sink-arc system; `slides`/`teleports`/`safeflips` the
# three move generators; `orient_of`/`states_of` the config <->
# orientation dictionary (GR-111 works at the edge level).


def valid_pats(sigma, cycles, mpairs, oddends):
    """None if sigma is not a valid configuration; else the sorted list
    of patterns it is valid at (alternation per F-cycle, no equal-label
    even matching pair, no mixed-label odd branch; patterns = the
    subcube fixing each forced branch colour)."""
    for cyc in cycles:
        ms = [v for v in cyc if sigma[v]]
        if len(ms) % 2:
            return None
        L = len(ms)
        for t in range(L):
            if L >= 2 and sigma[ms[t]] == sigma[ms[(t + 1) % L]]:
                return None
    for (a, b) in mpairs:
        if sigma[a] and sigma[a] == sigma[b]:
            return None
    forced = []
    for (u, w) in oddends:
        labs = {sigma[v] for v in (u, w) if sigma[v]}
        if len(labs) == 2:
            return None
        # label 1 (source) forces colour A = bit 0; label 2 (sink) -> B
        forced.append(None if not labs else (0 if labs == {1} else 1))
    k2 = len(oddends)
    pats = [p for p in range(1 << k2)
            if all(f is None or ((p >> j) & 1) == f
                   for j, f in enumerate(forced))]
    return pats


def imb_interval(pats, k2):
    """The (min, max) imbalance over a config's valid-pattern subcube
    ((GR-112): always an interval of even integers)."""
    vals = sorted({imb_of(k2, p) for p in pats})
    assert vals == list(range(vals[0], vals[-1] + 1, 2)), \
        '(GR-112) imbalance values not an even interval'
    return vals[0], vals[-1]


def cls_of(pats, k2):
    """'bal' (valid at a balanced pattern) / 'pos' (all valid patterns
    have imbalance > 0) / 'neg'."""
    lo, hi = imb_interval(pats, k2)
    if lo > 0:
        return 'pos'
    if hi < 0:
        return 'neg'
    return 'bal'


def enum_family(n, cycles, mpairs, oddends):
    """(mstar, family, bestp): the exhaustive labeled maximum family
    plus the per-pattern maximum |R| over ALL valid configurations
    (bestp[p] == n - f(p), the --form cross-assert).  Masks are pruned
    by per-cycle parity + aux-graph bipartiteness (as in
    gprice.rmodel_f), then each of the 2^{#components} labelings is
    kept iff end-consistent; every family sigma is re-checked through
    valid_pats (two independent validators)."""
    k2 = len(oddends)
    cmasks = [sum(1 << v for v in cyc) for cyc in cycles]
    out = []
    mstar = 0
    bestp = {p: 0 for p in range(1 << k2)}
    for mask in range(1 << n):
        ok = True
        for cm in cmasks:
            if bin(mask & cm).count('1') % 2:
                ok = False
                break
        if not ok:
            continue
        size = bin(mask).count('1')
        members = [v for v in range(n) if (mask >> v) & 1]
        adj = collections.defaultdict(list)
        for cyc in cycles:
            mem = [v for v in cyc if (mask >> v) & 1]
            L = len(mem)
            if L >= 2:
                for t in range(L):
                    if L == 2 and t == 1:
                        break
                    a, b = mem[t], mem[(t + 1) % L]
                    adj[a].append(b)
                    adj[b].append(a)
        for (x, y) in mpairs:
            if (mask >> x) & 1 and (mask >> y) & 1:
                adj[x].append(y)
                adj[y].append(x)
        klass, comp, comps = {}, {}, []
        ok = True
        for s in members:
            if s in klass:
                continue
            comps.append(s)
            klass[s] = 0
            comp[s] = s
            stack = [s]
            while stack and ok:
                a = stack.pop()
                for b in adj[a]:
                    if b not in klass:
                        klass[b] = klass[a] ^ 1
                        comp[b] = s
                        stack.append(b)
                    elif klass[b] == klass[a]:
                        ok = False
                        break
            if not ok:
                break
        if not ok:
            continue
        for bits in range(1 << len(comps)):
            ori = {c: (bits >> i) & 1 for i, c in enumerate(comps)}
            # end-consistency + forced colours, straight off the labels
            forced = []
            good = True
            for (u, w) in oddends:
                labs = {klass[v] ^ ori[comp[v]]
                        for v in (u, w) if (mask >> v) & 1}
                if len(labs) == 2:
                    good = False
                    break
                forced.append(None if not labs else labs.pop())
            if not good:
                continue
            for p in range(1 << k2):
                if all(f is None or ((p >> j) & 1) == f
                       for j, f in enumerate(forced)):
                    bestp[p] = max(bestp[p], size)
            if size < mstar:
                continue
            sigma = [0] * n
            for v in members:
                # label bit: 0 = source, 1 = sink
                sigma[v] = 1 + (klass[v] ^ ori[comp[v]])
            sigma = tuple(sigma)
            pats = valid_pats(sigma, cycles, mpairs, oddends)
            assert pats is not None, \
                'independent validators disagree (enum vs valid_pats)'
            if size > mstar:
                mstar, out = size, []
            out.append((sigma, tuple(pats)))
    return mstar, out, bestp


def arcs_of(sigma, cycles, lab):
    """The lab-delimited arc system of sigma ((GR-110) with lab = 2 the
    sink arcs): for each F-cycle meeting lab, the list of interior-hub
    lists between cyclically consecutive lab-hubs."""
    arcs = []
    for cyc in cycles:
        L = len(cyc)
        idxs = [t for t in range(L) if sigma[cyc[t]] == lab]
        if not idxs:
            continue
        for i, p in enumerate(idxs):
            q = idxs[(i + 1) % len(idxs)]
            run, t = [], (p + 1) % L
            while t != q:
                run.append(cyc[t])
                t = (t + 1) % L
            arcs.append(run)
            if len(idxs) == 1:
                break  # single delimiter: one arc all the way around
    return arcs


def transversal_family(n, sigma0, cycles, mpairs, oddends):
    """(GR-110): the configurations generated from sigma0's sink set by
    free choice of one source per sink-arc interior, filtered by the
    even-pair independence and the odd mixed-ends exclusion -- computed
    WITHOUT the validator, as the theorem states them."""
    sinks = [v for v in range(n) if sigma0[v] == 2]
    arcs = arcs_of(sigma0, cycles, 2)
    mpart = {}
    for (a, b) in mpairs:
        mpart[a], mpart[b] = b, a
    osib, oside = {}, {}
    for (u, w) in oddends:
        osib[u], osib[w] = w, u
    sinkset = set(sinks)
    out = set()
    for pick in itertools.product(*[range(len(a)) for a in arcs]):
        srcs = [arcs[i][j] for i, j in enumerate(pick)]
        ss = set(srcs)
        if len(ss) != len(srcs):
            continue  # cannot happen (arc interiors disjoint); guard
        if any(mpart.get(s) in ss for s in srcs):
            continue  # even pair with both ends chosen
        if any(osib.get(s) in sinkset for s in srcs):
            continue  # odd branch with a source end and a sink end
        sigma = [0] * n
        for v in sinks:
            sigma[v] = 2
        for v in srcs:
            sigma[v] = 1
        out.add(tuple(sigma))
    return out


# ------------------------------------------------------- move calculus ------

def slides(sigma, cycles, lab):
    """All single slides of a lab-labelled hub inside its arc (the
    (GR-110) generator): yields candidate sigma' tuples (validated by
    the caller)."""
    for cyc in cycles:
        L = len(cyc)
        idxs = [t for t in range(L) if sigma[cyc[t]]]
        for i, p in enumerate(idxs):
            v = cyc[p]
            if sigma[v] != lab:
                continue
            prv, nxt = idxs[i - 1], idxs[(i + 1) % len(idxs)]
            # double gap: positions strictly between prv and nxt through p
            run, t = [], (prv + 1) % L
            if len(idxs) == 1:
                run = [q for q in range(L) if q != p]
            else:
                while t != nxt:
                    if t != p:
                        run.append(t)
                    t = (t + 1) % L
            for t in run:
                s2 = list(sigma)
                s2[v] = 0
                s2[cyc[t]] = lab
                yield tuple(s2)


def gaps_of(sigma, cycles):
    """The insertion gaps of sigma: per cycle, maximal through-runs
    between consecutive reversal hubs, plus whole reversal-free
    cycles."""
    gaps = []
    for cyc in cycles:
        L = len(cyc)
        idxs = [t for t in range(L) if sigma[cyc[t]]]
        if not idxs:
            gaps.append([cyc[t] for t in range(L)])
            continue
        for i, p in enumerate(idxs):
            q = idxs[(i + 1) % len(idxs)]
            run, t = [], (p + 1) % L
            while t != q:
                run.append(cyc[t])
                t = (t + 1) % L
            if run:
                gaps.append(run)
            if len(idxs) == 1:
                break
    return gaps


def teleports(sigma, cycles):
    """All adjacent-pair removals followed by a same-gap pair insertion
    anywhere ((GR-107)(v)'s two moves composed): yields candidate
    sigma' tuples."""
    for cyc in cycles:
        L = len(cyc)
        idxs = [t for t in range(L) if sigma[cyc[t]]]
        if len(idxs) < 2:
            continue
        npairs = 1 if len(idxs) == 2 else len(idxs)
        for i in range(npairs):
            a, b = cyc[idxs[i]], cyc[idxs[(i + 1) % len(idxs)]]
            s0 = list(sigma)
            s0[a] = s0[b] = 0
            for run in gaps_of(tuple(s0), cycles):
                for j in range(len(run)):
                    for k in range(j + 1, len(run)):
                        for (la, lb) in ((1, 2), (2, 1)):
                            s2 = list(s0)
                            s2[run[j]], s2[run[k]] = la, lb
                            s2 = tuple(s2)
                            if s2 != sigma:
                                yield s2


def aux_comps(sigma, cycles, mpairs):
    """The aux components of sigma's reversal set (cycle adjacency +
    even matching pairs inside R), as a hub -> root map."""
    members = [v for v in range(len(sigma)) if sigma[v]]
    adj = collections.defaultdict(list)
    for cyc in cycles:
        mem = [v for v in cyc if sigma[v]]
        L = len(mem)
        if L >= 2:
            for t in range(L):
                if L == 2 and t == 1:
                    break
                adj[mem[t]].append(mem[(t + 1) % L])
                adj[mem[(t + 1) % L]].append(mem[t])
    for (a, b) in mpairs:
        if sigma[a] and sigma[b]:
            adj[a].append(b)
            adj[b].append(a)
    comp = {}
    for s in members:
        if s in comp:
            continue
        comp[s] = s
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w not in comp:
                    comp[w] = s
                    stack.append(w)
    return comp


def safeflips(sigma, cycles, mpairs, oddends):
    """All safe component flips (components holding resident ends of at
    most ONE odd branch): yields sigma' tuples."""
    comp = aux_comps(sigma, cycles, mpairs)
    ends_in = collections.defaultdict(set)
    for j, (u, w) in enumerate(oddends):
        for v in (u, w):
            if sigma[v]:
                ends_in[comp[v]].add(j)
    roots = sorted({c for c in comp.values()})
    for c in roots:
        if len(ends_in[c]) > 1:
            continue
        s2 = list(sigma)
        for v, cv in comp.items():
            if cv == c:
                s2[v] = 3 - s2[v]
        yield tuple(s2)


# ------------------------------------------------ orientation dictionary ----

def orient_of(sigma, cycles, rng):
    """One orientation realizing sigma: per cycle a bit tuple, bit[t] =
    1 iff the edge cyc[t] -> cyc[t+1] is directed forward.  Sink at
    position p <-> (bit[p-1], bit[p]) = (1, 0); source <-> (0, 1).
    Reversal-free cycles get a seeded coin."""
    bits = []
    for cyc in cycles:
        L = len(cyc)
        idxs = [t for t in range(L) if sigma[cyc[t]]]
        if not idxs:
            bits.append(tuple([rng.randrange(2)] * L))
            continue
        row = [0] * L
        for t in range(L):
            # first reversal hub strictly ahead of edge t
            s = (t + 1) % L
            while not sigma[cyc[s]]:
                s = (s + 1) % L
            row[t] = 1 if sigma[cyc[s]] == 2 else 0
        bits.append(tuple(row))
    return tuple(bits)


def states_of(bits, cycles, n):
    """The state tuple of an orientation."""
    sigma = [0] * n
    for ci, cyc in enumerate(cycles):
        L = len(cyc)
        for t in range(L):
            a, b = bits[ci][t - 1], bits[ci][t]
            if (a, b) == (1, 0):
                sigma[cyc[t]] = 2
            elif (a, b) == (0, 1):
                sigma[cyc[t]] = 1
    return tuple(sigma)


def glue_data(x, y, cycles, mpairs, oddends, n):
    """The glued super-components of supp(x XOR y): returns (zedges,
    find, hcomp, sx, sy) with find the union-find root map over
    z-edges, hcomp the hub -> root map for hubs on a z-edge."""
    # z-support edges and their F-components (edges adjacent via a hub)
    parent = {}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    zedges = []
    for ci, cyc in enumerate(cycles):
        for t in range(len(cyc)):
            if x[ci][t] != y[ci][t]:
                e = (ci, t)
                parent[e] = e
                zedges.append(e)
    byhub = collections.defaultdict(list)
    for (ci, t) in zedges:
        cyc = cycles[ci]
        byhub[cyc[t]].append((ci, t))
        byhub[cyc[(t + 1) % len(cyc)]].append((ci, t))
    for es in byhub.values():
        for e in es[1:]:
            union(es[0], e)
    sx, sy = states_of(x, cycles, n), states_of(y, cycles, n)
    hcomp = {}
    for v, es in byhub.items():
        hcomp[v] = find(es[0])
    for v in range(n):
        if v not in hcomp:
            assert sx[v] == sy[v], 'z-fixed hub with differing states'
    # gluing: mixed-state conflicts at even pairs and odd ends
    forb_even = lambda p, q: p and p == q            # noqa: E731
    forb_odd = lambda p, q: p and q and p != q       # noqa: E731
    for (pair, forb) in ([(mp, forb_even) for mp in mpairs] +
                         [(oe, forb_odd) for oe in oddends]):
        a, b = pair
        if a in hcomp and b in hcomp:
            if forb(sx[a], sy[b]) or forb(sy[a], sx[b]):
                union(hcomp[a], hcomp[b])
    return zedges, find, hcomp, sx, sy


def swap_T(x, y, zedges, find, T):
    """The recombinants (x_T, y_T) for a union-of-super-components T."""
    xt = [list(row) for row in x]
    yt = [list(row) for row in y]
    for (ci, t) in zedges:
        if find((ci, t)) in T:
            xt[ci][t], yt[ci][t] = y[ci][t], x[ci][t]
    return (tuple(tuple(r) for r in xt), tuple(tuple(r) for r in yt))


def recombine(x, y, cycles, mpairs, oddends, n, rng):
    """(GR-111) at one (x, y): one seeded recombination (x_T, y_T) for
    a random union-of-super-components T."""
    zedges, find, _hc, _sx, _sy = glue_data(x, y, cycles, mpairs,
                                            oddends, n)
    supers = sorted({find(e) for e in zedges})
    T = {s for s in supers if rng.randrange(2)}
    xt, yt = swap_T(x, y, zedges, find, T)
    return xt, yt, len(supers)


def separation(x, y, cycles, mpairs, oddends, n):
    """(GR-111)'s 2k = 2 corollary, constructively: for x pos-forcing
    and y neg-forcing orientations, decide whether the glued
    super-components separate {gamma_1 ends y-sink} from {gamma_2 ends
    x-source} (or the (BA) mirror), and if so return the balance-valid
    recombinant x_T; else None."""
    zedges, find, hcomp, sx, sy = glue_data(x, y, cycles, mpairs,
                                            oddends, n)
    for (g_out, g_in) in ((0, 1), (1, 0)):
        need_out = {find(hcomp[e]) for e in oddends[g_out]
                    if e in hcomp and sy[e] == 2}
        need_in = {find(hcomp[e]) for e in oddends[g_in]
                   if e in hcomp and sx[e] == 1}
        # a gamma end that is x-source but z-fixed can never move to the
        # y side: the criterion fails on this orientation pair
        if any(e not in hcomp and sx[e] == 1 for e in oddends[g_in]):
            continue
        if any(e not in hcomp and sy[e] == 2 for e in oddends[g_out]):
            continue
        if need_out & need_in:
            continue
        xt, _yt = swap_T(x, y, zedges, find, need_in)
        return xt
    return None


# ------------------------------------------------------------ sweeps --------

def family_of(specs, n, mat, oidx):
    cycles, mpairs, oddends = cell_data(specs, n, mat, oidx)
    mstar, fam, bestp = enum_family(n, cycles, mpairs, oddends)
    return cycles, mpairs, oddends, mstar, fam, bestp


def form_pair(specs, n, mat, oidx, stats):
    """--form at one pair: the enumeration cross-assert vs the landed
    rmodel_f (per pattern, every pattern), and (GR-110) asserted at
    every distinct sink set of the maximum family."""
    cycles, mpairs, oddends, mstar, fam, bestp = \
        family_of(specs, n, mat, oidx)
    k2 = len(oidx)
    f = rmodel_f(n, cycles, mpairs, oddends)
    assert mstar == n - min(f.values()), 'M* != n - d_par'
    for p in f:
        assert bestp[p] == n - f[p], \
            'labeled enumeration != rmodel_f at a pattern'
    # (GR-110): family grouped by sink set == the transversal family
    bysink = collections.defaultdict(set)
    for (sigma, _pats) in fam:
        key = tuple(v for v in range(n) if sigma[v] == 2)
        bysink[key].add(sigma)
    for key in sorted(bysink):
        sigma0 = sorted(bysink[key])[0]
        gen = transversal_family(n, sigma0, cycles, mpairs, oddends)
        assert bysink[key] == gen, \
            '(GR-110) transversal family != enumerated family at a sink set'
        assert all(sum(1 for v in s if v) == 2 * len(key) for s in gen), \
            '(GR-110) |R| != 2|sinks|'
        stats['sinksets'] += 1
    stats['pairs'] += 1
    stats['fam'] += len(fam)


def conn_pair(specs, n, mat, oidx, stats, detail=None):
    """--conn at one pair: the fine-move graph of the labeled maximum
    family at three nested move levels; the (GR-112) no-crossing assert
    on every edge; the escape verdicts."""
    cycles, mpairs, oddends, mstar, fam, _bp = \
        family_of(specs, n, mat, oidx)
    k2 = len(oidx)
    index = {sigma: i for i, (sigma, _p) in enumerate(fam)}
    cls = [cls_of(pats, k2) for (_s, pats) in fam]
    N = len(fam)
    # candidates generated ONCE per config, tagged by move level
    edges = {1: [], 2: [], 3: []}
    for i, (sigma, pats) in enumerate(fam):
        lo1, _ = imb_interval(pats, k2)
        for lvl, cand in ((1, itertools.chain(slides(sigma, cycles, 1),
                                              slides(sigma, cycles, 2))),
                          (2, teleports(sigma, cycles)),
                          (3, safeflips(sigma, cycles, mpairs, oddends))):
            for s2 in cand:
                p2 = valid_pats(s2, cycles, mpairs, oddends)
                if p2 is None:
                    continue
                assert sum(1 for v in s2 if v) == mstar, \
                    'move changed the reversal count'
                j = index.get(s2)
                assert j is not None, 'valid maximum missed by enum_family'
                # (GR-112): no single move crosses pos <-> neg, and the
                # interval minimum drops by at most 2
                lo2, _ = imb_interval(tuple(p2), k2)
                assert not (cls[i] == 'pos' and cls[j] == 'neg'), \
                    '(GR-112) pos -> neg crossing'
                assert not (cls[i] == 'neg' and cls[j] == 'pos'), \
                    '(GR-112) neg -> pos crossing'
                assert lo2 >= lo1 - 2, '(GR-112) interval minimum fell > 2'
                edges[lvl].append((i, j))
    levels = {}
    parent = list(range(N))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for level, lvl in (('L1-slides', 1), ('L2-teleports', 2),
                       ('L3-safeflips', 3)):
        for (i, j) in edges[lvl]:
            ri, rj = find(i), find(j)
            if ri != rj:
                parent[ri] = rj
        comps = collections.defaultdict(collections.Counter)
        for i in range(N):
            comps[find(i)][cls[i]] += 1
        bad = sum(1 for c in comps.values()
                  if (c['pos'] or c['neg']) and not c['bal'])
        # existential escape: where pos-forcing maxima exist at all, at
        # least one of them shares a component with a balance-valid one
        haspos = any(c == 'pos' for c in cls)
        exi = (not haspos) or any(c['pos'] and c['bal']
                                  for c in comps.values())
        levels[level] = (len(comps), bad, exi, len(edges[lvl]))
    stats['pairs'] += 1
    stats['fam'] += N
    stats['forcing'] += sum(1 for c in cls if c != 'bal')
    for level, (ncomp, bad, exi, _ne) in levels.items():
        stats[f'{level}_comps'] += ncomp
        stats[f'{level}_noescape'] += bad
        if not exi:
            stats[f'{level}_noexi_pairs'] += 1
        if bad:
            stats[f'{level}_noescape_pairs'] += 1
            # witnesses printed for the headline levels only (L1 alone is
            # expected to strand components; that is the measurement)
            if detail is not None and level != 'L1-slides':
                detail.append((level, n, specs, sorted(mat)))
    return levels


def recomb_pair(specs, n, mat, oidx, stats, rng, draws=6):
    """--recomb at one pair: (GR-111) asserted on seeded (x, y, T)
    triples; the 2k = 2 separation criterion measured when pos-forcing
    maxima exist."""
    cycles, mpairs, oddends, mstar, fam, _bp = \
        family_of(specs, n, mat, oidx)
    k2 = len(oidx)
    cls = [cls_of(pats, k2) for (_s, pats) in fam]
    stats['pairs'] += 1
    for _d in range(draws):
        i, j = rng.randrange(len(fam)), rng.randrange(len(fam))
        x = orient_of(fam[i][0], cycles, rng)
        y = orient_of(fam[j][0], cycles, rng)
        xt, yt, _ns = recombine(x, y, cycles, mpairs, oddends, n, rng)
        for bits in (xt, yt):
            s = states_of(bits, cycles, n)
            p = valid_pats(s, cycles, mpairs, oddends)
            assert p is not None, '(GR-111) recombinant invalid'
            assert sum(1 for v in s if v) == mstar, \
                '(GR-111) recombinant not maximum'
        stats['triples'] += 1
    # separation criterion, 2k = 2 only, where pos-forcing maxima exist:
    # for EACH pos-forcing x, hunt a neg-forcing y whose gluing
    # separates the pinned ends; the returned recombinant must be a
    # balance-valid maximum (asserted)
    if k2 == 2 and any(c == 'pos' for c in cls):
        stats['pos_pairs'] += 1
        posi = [i for i, c in enumerate(cls) if c == 'pos']
        negi = [i for i, c in enumerate(cls) if c == 'neg']
        bali = [i for i, c in enumerate(cls) if c == 'bal']
        # the law (measured 1 431/1 431 by GPRICE) says bali is nonempty
        assert bali, 'balance law violated (no balance-valid maximum)'
        nsep = 0
        if len(negi) > 40:
            stats['sep_capped_pairs'] += 1
        for i in posi:
            got = False
            ys = negi if len(negi) <= 40 else rng.sample(negi, 40)
            for j in ys:
                x = orient_of(fam[i][0], cycles, rng)
                y = orient_of(fam[j][0], cycles, rng)
                xt = separation(x, y, cycles, mpairs, oddends, n)
                if xt is not None:
                    s = states_of(xt, cycles, n)
                    p = valid_pats(s, cycles, mpairs, oddends)
                    assert p is not None and cls_of(p, k2) == 'bal', \
                        '(GR-111) separated recombinant not balance-valid'
                    assert sum(1 for v in s if v) == mstar, \
                        '(GR-111) separated recombinant not maximum'
                    got = True
                    break
            nsep += 1 if got else 0
        stats['sep_pos'] += len(posi)
        stats['sep_found'] += nsep
        stats['sep_all_pairs'] += 1 if nsep == len(posi) else 0
    return


def strand_witness():
    """GBLAW's no-escape witness (found and printed by --conn's n = 16
    leg; re-entered here for independent reconstruction): n = 16, one
    16-cycle 2-factor, 2k = 2 with both odd branches matching chords.
    Its maximum family splits under the FULL move calculus (slides +
    teleports + safe flips) into one 88-config component carrying every
    balance-valid maximum and two stranded pure components (32
    pos-forcing / 32 neg-forcing), and no stranded maximum admits a
    separating recombination partner ((GR-113), asserted by --strand)."""
    specs = [(8, 15, 2), (15, 7, 2), (7, 4, 2), (4, 1, 2), (1, 10, 2),
             (10, 5, 2), (5, 13, 2), (13, 2, 4), (2, 6, 2), (6, 12, 2),
             (12, 3, 2), (3, 0, 2), (0, 9, 2), (9, 14, 2), (14, 11, 2),
             (11, 8, 2), (1, 13, 2), (3, 11, 2), (9, 4, 2), (8, 6, 2),
             (5, 15, 3), (12, 10, 4), (0, 2, 3), (14, 7, 2)]
    return specs, frozenset(range(16, 24))


def sweep(pool, worker, **kw):
    stats = collections.Counter()
    for (specs, n, mat, oidx) in pool:
        worker(specs, n, mat, oidx, stats, **kw)
    return stats


def stratum_pool():
    out = []
    for (_tag, n, specs) in stratum_cases():
        oidx, mats, _c = pairs_of(specs, n)
        for mat in mats:
            out.append((specs, n, mat, oidx))
    return out


def control_pool():
    specs, n = gr103_specs(), 12
    return [(specs, n, frozenset({12, 13, 14, 15, 16, 17}),
             odd_idx(specs))]


def v8_pool():
    specs, n = v8_specs(), 8
    oidx, mats, _c = pairs_of(specs, n)
    return [(specs, n, mat, oidx) for mat in mats]


def cell_pool(rng, n, k2, tries, cap=None):
    got = cell_shapes(n, k2, tries, rng)
    if cap is not None and len(got) > cap:
        got = got[:cap]
    return [(sp, n, mat, odd_idx(sp)) for (sp, mat) in got]


def report_form(tag, stats, t0):
    print(f'  leg {tag}: {stats["pairs"]} O<=M pairs; labeled maximum '
          f'family total {stats["fam"]}; (GR-110) asserted at '
          f'{stats["sinksets"]} (pair, sink set) cells  '
          f'[{time.time() - t0:.0f}s]')


def report_conn(tag, stats, t0):
    lv = {}
    for level in ('L1-slides', 'L2-teleports', 'L3-safeflips'):
        lv[level] = (stats[f'{level}_comps'],
                     stats[f'{level}_noescape'],
                     stats[f'{level}_noescape_pairs'],
                     stats[f'{level}_noexi_pairs'])
    print(f'  leg {tag}: {stats["pairs"]} O<=M pairs; family total '
          f'{stats["fam"]} ({stats["forcing"]} pos/neg-forcing); '
          f'components (total / no-escape / pairs-with-no-escape / '
          f'pairs-with-no-EXISTENTIAL-escape): '
          + '; '.join(f'{k} {v[0]}/{v[1]}/{v[2]}/{v[3]}'
                      for k, v in lv.items())
          + f'  [{time.time() - t0:.0f}s]')


def report_recomb(tag, stats, t0):
    print(f'  leg {tag}: {stats["pairs"]} pairs; (GR-111) asserted at '
          f'{stats["triples"]} (x, y, T) triples; pos-forcing pairs '
          f'{stats["pos_pairs"]} (of which {stats["sep_all_pairs"]} '
          f'separate at EVERY pos-forcing maximum); separation found at '
          f'{stats["sep_found"]}/{stats["sep_pos"]} pos-forcing maxima '
          f'(neg-partner cap 40 bound at {stats["sep_capped_pairs"]} '
          f'pairs -- CAP, disclosed)  [{time.time() - t0:.0f}s]')


# --------------------------------------------- [GBL-1] --form ---------------

def leg_form(args):
    t0 = time.time()
    print('[--form] (GR-110) the arc-transversal normal form + the '
          'enumeration cross-assert vs the landed rmodel_f')
    rng = random.Random(R_SEED)
    for tag, pool in (('stratum (EXHAUSTIVE)', stratum_pool()),
                      ('V8 (2k = 4)', v8_pool()),
                      ('(GR-103) control', control_pool()),
                      ('n = 12, 2k = 2 cell pool (tries 120 -- CAP, '
                       'disclosed)', cell_pool(rng, 12, 2, 120)),
                      ('n = 14, 2k = 2 cell pool (tries 60 -- CAP, '
                       'disclosed)', cell_pool(rng, 14, 2, 60))):
        t1 = time.time()
        stats = sweep(pool, form_pair)
        report_form(tag, stats, t1)
    print(f'[--form] OK  [{time.time() - t0:.0f}s]  (seed {R_SEED})')


# --------------------------------------------- [GBL-2] --conn ---------------

def leg_conn(args):
    t0 = time.time()
    print('[--conn] (GR-112)/(GR-113): the fine-move census at three '
          'nested move levels; the no-crossing assert rides every edge')
    rng = random.Random(R_SEED + 1)
    detail = []
    for tag, pool in (('stratum (EXHAUSTIVE)', stratum_pool()),
                      ('V8 (2k = 4)', v8_pool()),
                      ('(GR-103) control', control_pool()),
                      ('n = 12, 2k = 2 cell pool (tries 120 -- CAP, '
                       'disclosed)', cell_pool(rng, 12, 2, 120)),
                      ('n = 12, 2k = 4 cell pool (tries 120 -- CAP, '
                       'disclosed)', cell_pool(rng, 12, 4, 120)),
                      ('n = 14, 2k = 2 cell pool (tries 60 -- CAP, '
                       'disclosed)', cell_pool(rng, 14, 2, 60)),
                      ('n = 16, 2k = 2 cell pool (tries 40, cap 12 -- '
                       'CAPS, disclosed)', cell_pool(rng, 16, 2, 40, 12))):
        t1 = time.time()
        stats = collections.Counter()
        for (specs, n, mat, oidx) in pool:
            conn_pair(specs, n, mat, oidx, stats, detail=detail)
        report_conn(tag, stats, t1)
    if detail:
        print(f'    no-escape witnesses ({len(detail)}):')
        for (level, n, specs, mat) in detail:
            print(f'      {level}: n = {n}, specs = {specs}, mat = {mat}')
    else:
        print('    universal escape at EVERY swept pair and every move '
              'level that reports 0 above')
    print(f'[--conn] OK  [{time.time() - t0:.0f}s]  (seed {R_SEED + 1})')


# --------------------------------------------- [GBL-3] --recomb -------------

def leg_recomb(args):
    t0 = time.time()
    print('[--recomb] (GR-111) asserted on seeded (x, y, T) triples; '
          'the 2k = 2 separation criterion measured at pos-forcing pairs')
    rng = random.Random(R_SEED + 2)
    # replay --conn's rng stream so its n = 16 pool (the leg holding the
    # no-escape witness) is swept HERE for separation, byte-identically
    rngc = random.Random(R_SEED + 1)
    for (nn, kk, tt) in ((12, 2, 120), (12, 4, 120), (14, 2, 60)):
        cell_pool(rngc, nn, kk, tt)
    for tag, pool in (('stratum (EXHAUSTIVE)', stratum_pool()),
                      ('(GR-103) control', control_pool()),
                      ('n = 12, 2k = 2 cell pool (tries 120 -- CAP, '
                       'disclosed)', cell_pool(rng, 12, 2, 120)),
                      ('n = 16, 2k = 2 cell pool (tries 40, cap 12 -- '
                       'CAPS, disclosed; identical to the --conn pool '
                       'holding the no-escape witness)',
                       cell_pool(rngc, 16, 2, 40, 12))):
        t1 = time.time()
        stats = collections.Counter()
        for (specs, n, mat, oidx) in pool:
            recomb_pair(specs, n, mat, oidx, stats, rng)
        report_recomb(tag, stats, t1)
    print(f'[--recomb] OK  [{time.time() - t0:.0f}s]  (seed {R_SEED + 2})')


# --------------------------------------------- [GBL-4] --strand -------------

def leg_strand(args):
    t0 = time.time()
    print('[--strand] the no-escape witness in full: fine components, '
          'stranded family, and the EXHAUSTIVE separation hunt (one '
          'F-cycle, so each config has a unique orientation -- no '
          'orientation cap exists at this pair)')
    specs, mat = strand_witness()
    n = 16
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    assert cubic_habitat(n, hedges, lens), 'witness fails the gate'
    oidx = odd_idx(specs)
    assert len(oidx) == 2 and set(oidx) <= mat, 'witness not O <= M, 2k = 2'
    cycles, mpairs, oddends, mstar, fam, _bp = \
        family_of(specs, n, mat, oidx)
    assert len(cycles) == 1, 'witness 2-factor is not a single cycle'
    k2 = len(oidx)
    cls = [cls_of(p, k2) for (_s, p) in fam]
    cc = collections.Counter(cls)
    assert (mstar, len(fam)) == (12, 152) and \
        (cc['pos'], cc['neg'], cc['bal']) == (48, 48, 56), \
        'witness family drifted'
    # L3 fine components
    index = {s: i for i, (s, _p) in enumerate(fam)}
    parent = list(range(len(fam)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for i, (sigma, _p) in enumerate(fam):
        for s2 in itertools.chain(slides(sigma, cycles, 1),
                                  slides(sigma, cycles, 2),
                                  teleports(sigma, cycles),
                                  safeflips(sigma, cycles, mpairs,
                                            oddends)):
            p2 = valid_pats(s2, cycles, mpairs, oddends)
            if p2 is None:
                continue
            ri, rj = find(i), find(index[s2])
            if ri != rj:
                parent[ri] = rj
    comps = collections.defaultdict(list)
    for i in range(len(fam)):
        comps[find(i)].append(i)
    profs = sorted((len(mem),
                    tuple(sorted(collections.Counter(
                        cls[i] for i in mem).items())))
                   for mem in comps.values())
    assert profs == [(32, (('neg', 32),)), (32, (('pos', 32),)),
                     (88, (('bal', 56), ('neg', 16), ('pos', 16)))], \
        'witness component structure drifted'
    print('  components: 88 (56 bal + 16 pos + 16 neg) + 32 pure pos + '
          '32 pure neg -- the stranded family')
    stranded = [i for mem in comps.values()
                if not any(cls[i] == 'bal' for i in mem)
                for i in mem if cls[i] == 'pos']
    bigpos = [i for mem in comps.values()
              if any(cls[i] == 'bal' for i in mem)
              for i in mem if cls[i] == 'pos']
    negi = [i for i, c in enumerate(cls) if c == 'neg']
    rng = random.Random(R_SEED + 3)  # never consumed here (one F-cycle)
    nsep = {'stranded': 0, 'big-component': 0}
    for tag, pool in (('stranded', stranded), ('big-component', bigpos)):
        for i in pool:
            x = orient_of(fam[i][0], cycles, rng)
            got = False
            for j in negi:
                y = orient_of(fam[j][0], cycles, rng)
                xt = separation(x, y, cycles, mpairs, oddends, n)
                if xt is not None:
                    s = states_of(xt, cycles, n)
                    p = valid_pats(s, cycles, mpairs, oddends)
                    assert p is not None and cls_of(p, k2) == 'bal' \
                        and sum(1 for v in s if v) == mstar
                    got = True
                    break
            nsep[tag] += 1 if got else 0
    assert nsep['stranded'] == 0, \
        'a stranded maximum separated after all -- update the workbook'
    print(f'  separation over ALL {len(negi)} neg-forcing partners '
          f'(EXHAUSTIVE at this pair): stranded {nsep["stranded"]}/'
          f'{len(stranded)}, big-component {nsep["big-component"]}/'
          f'{len(bigpos)}')
    print(f'[--strand] OK  [{time.time() - t0:.0f}s]')


# ----------------------------------------------------------- main -----------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--form', action='store_true')
    ap.add_argument('--conn', action='store_true')
    ap.add_argument('--recomb', action='store_true')
    ap.add_argument('--strand', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.validate:
        args.form = args.conn = args.recomb = args.strand = True
    if not (args.form or args.conn or args.recomb or args.strand):
        ap.error('pick a mode: --form / --conn / --recomb / --strand / '
                 '--validate')
    if args.form:
        leg_form(args)
    if args.conn:
        leg_conn(args)
    if args.recomb:
        leg_recomb(args)
    if args.strand:
        leg_strand(args)


if __name__ == '__main__':
    main()
