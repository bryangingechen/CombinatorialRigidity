#!/usr/bin/env python3
"""
orbitrule.py -- Track C driver (W4-reopen P1, certificate half).

Tests two claims of §(K-main) Step MC15 at targeted instances, exact Q:

  (MC-62)  dim U = min(delta2, 3) for a !~ b, and min(delta2, 1) for a ~ b, where
         U = {P_a - P_b : P in F(G', q)} and delta2 = def2(G') - def2(G'/ab).
         At a picture q certified by dim F(G', q) = 3 + def2(G') (the flex space itself;
         for G' satisfying (H) this is q in U(G')), the
         drawn dim U is a LOWER bound for the generic value and (elementary,
         (MC-4)(b) at G'+ab+x) an UPPER bound min(delta2, 3) holds at every
         certified q; so a drawn equality certifies the generic value.
  (MC-64)  the orbit rule: a !~ b and delta2 = 1 => p_b in pi_a on all of X0(G')
         iff b has a neighbour in R(a) (the maximal def2-rigid set containing
         a, or {a}); orbit (iii) iff a ~ b and delta2 >= 1; (iv) iff delta2 = 0;
         a !~ b and delta2 >= 2 => orbit (i).
         "p_b not in pi_a" is an open condition (one certified q certifies
         it); "p_b in pi_a" at every drawn q is draw-level only.

Modes (run from the repository root, PYTHONHASHSEED=0):
  --cells8     every open chain with k = 2 interior vertices of every simple
               2EC graph on <= 8 vertices (the population of (MC-57)'s
               k = 2 cells); G' = G - interior, (a, b) = the chain ends.
  --sparse N   every connected graph on n <= N vertices (n even) with
               2|E| = 3n - 4 and 2|E(Y)| <= 3|Y| - 4 for every |Y| >= 2
               (a 1-dof rod linkage with no def2-rigid subgraph), every
               non-adjacent pair: the (MC-65) lemma (the core of (MC-64)'s "only if").
Seeded (20260924, per-instance string seeds), pictures uniform integers in
[-30, 30]^2 (maincomp.sample_q), up to 3 certified pictures per instance.
"""
import argparse
import itertools
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402
from exactcore import rank as rank_exact, neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from maincomp import def_k, lifting_space, sample_q, two_ec_graphs, connected_graphs, decode  # noqa: E402
from splitext import flex_space, contract as merge_pair  # noqa: E402
from nogood_subdiv import branch_decomposition  # noqa: E402

SEED = 20260924
DRAWS = 3


def delta2(E, V, a, b):
    return def_k(E, 3, V) - def_k(merge_pair(E, a, b), 3, [v for v in V if v != b])


def rigid_class(E, V, a):
    """R(a): a together with every w with delta2(a, w) = 0 (a common def2-rigid
    subgraph, (MC-13)(b)'s argument)."""
    return {a} | {w for w in V if w != a and delta2(E, V, a, w) == 0}


def read_orbit(E, V, a, b, tag):
    """(dim U, p_a off pi_b, p_b off pi_a, #certified pictures) combined over up to
    DRAWS pictures certified in U(G')."""
    d2 = def_k(E, 3, V)
    best = None
    ncert = 0
    for t in range(DRAWS):
        rng = random.Random(f'{SEED}:orbitrule:{tag}:{t}')
        q = sample_q(rng, V, E, 30)
        Fb = flex_space(E, V, q)                  # certified: dim F(q) = 3 + def2 (the JJ value)
        assert len(Fb) >= 3 + d2, '(MC-4)(b)'
        if len(Fb) != 3 + d2:
            continue
        ncert += 1
        ia, ib = 3 * V.index(a), 3 * V.index(b)
        U = [[v[ia + j] - v[ib + j] for j in range(3)] for v in Fb]
        dU = rank_exact(U) if U else 0
        ha = (q[a][0], q[a][1], F(1))
        hb = (q[b][0], q[b][1], F(1))
        pb_off = any(sum(x * y for x, y in zip(u, hb)) for u in U)
        pa_off = any(sum(x * y for x, y in zip(u, ha)) for u in U)
        cur = (dU, pa_off, pb_off)
        best = cur if best is None else (max(best[0], dU), best[1] or pa_off, best[2] or pb_off)
    if best is None:
        return None
    return best + (ncert,)


def orbit_name(dU, pa_off, pb_off):
    return ('iv' if dU == 0 else 'i' if (pa_off and pb_off)
            else 'ii' if (pa_off or pb_off) else 'iii')


def predict(E, V, a, b):
    nb = neighbors(E)
    adj = b in nb[a]
    d2t = delta2(E, V, a, b)
    if adj:
        dU = min(d2t, 1)
        orb = 'iv' if d2t == 0 else 'iii'
        return dU, orb, d2t, adj, None
    dU = min(d2t, 3)
    if d2t == 0:
        return dU, 'iv', d2t, adj, None
    if d2t >= 2:
        return dU, 'i', d2t, adj, None
    Ra, Rb = rigid_class(E, V, a), rigid_class(E, V, b)
    pb_on = any(w in Ra for w in nb[b])       # b has a neighbour in R(a)
    pa_on = any(w in Rb for w in nb[a])       # a has a neighbour in R(b)
    assert not (pb_on and pa_on), 'both incidences predicted (two edges between R(a), R(b))'
    orb = 'ii' if (pb_on or pa_on) else 'i'
    return dU, orb, d2t, adj, (len(Ra), len(Rb), pa_on, pb_on)


def cells8():
    tally = Counter()
    mism = []
    for name, E in two_ec_graphs(8):
        hubs, br = branch_decomposition(E)
        if not br:
            continue
        for bi, (h1, h2, I) in enumerate(br):
            if len(I) != 2 or h1 == h2:
                continue
            Ws = set(I)
            Ep = [e for e in E if e[0] not in Ws and e[1] not in Ws]
            Vp = verts_of(Ep)
            nbp = neighbors(Ep)
            if len(Vp) != len(verts_of(E)) - 2 or min(len(s) for s in nbp.values()) < 2:
                continue
            obs = read_orbit(Ep, Vp, h1, h2, f'{name}:{bi}')
            if obs is None:
                tally['no certified picture'] += 1
                continue
            dU, pa_off, pb_off, nc = obs
            orb = orbit_name(dU, pa_off, pb_off)
            pdU, porb, d2t, adj, extra = predict(Ep, Vp, h1, h2)
            ok = (dU == pdU and orb == porb)
            tally[(orb, dU, porb, pdU, 'a~b' if adj else 'a!~b', d2t, ok)] += 1
            if not ok:
                mism.append((name, h1, h2, orb, dU, porb, pdU, adj, d2t, extra))
    print('k = 2 chains of simple 2EC graphs on <= 8 vertices, G\' = G - interior:')
    print('  (observed orbit, dim U | predicted orbit, dim U | adjacency, delta2 | match): count')
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  mismatches: {len(mism)}')
    for m in mism[:20]:
        print('   ', m)


def sparse_tight(E, n):
    nb = neighbors(E)
    if any(len(nb.get(v, ())) < 2 for v in range(n)):
        return False
    if 2 * len(E) != 3 * n - 4:
        return False
    for r in range(2, n):
        for Y in itertools.combinations(range(n), r):
            Ys = set(Y)
            e = sum(1 for (u, w) in E if u in Ys and w in Ys)
            if 2 * e > 3 * r - 4:
                return False
    return True


def sparse(N):
    lev = connected_graphs(N)
    tally = Counter()
    bad = []
    for n in range(4, N + 1, 2):
        graphs = [decode(n, c) for c in lev[n]]
        tight = [E for E in graphs if sparse_tight(E, n)]
        print(f'n={n}: {len(tight)} tight sparse graphs (2|E| = 3n - 4, min degree >= 2)')
        for gi, E in enumerate(tight):
            V = list(range(n))
            nb = neighbors(E)
            assert def_k(E, 3, V) == 1
            for a, b in itertools.permutations(V, 2):
                if b in nb[a]:
                    continue
                assert delta2(E, V, a, b) == 1
                obs = read_orbit(E, V, a, b, f'sp{n}:{gi}:{a}:{b}')
                if obs is None:
                    tally[(n, 'no certified picture')] += 1
                    continue
                dU, pa_off, pb_off, nc = obs
                tally[(n, 'dimU', dU)] += 1
                if not pb_off:
                    bad.append((n, gi, E, a, b, dU, nc))
                tally[(n, 'p_b off pi_a' if pb_off else 'p_b ON pi_a at every draw')] += 1
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  candidate counterexamples to (MC-65) (p_b on pi_a at every certified draw): {len(bad)}')
    for x in bad[:20]:
        print('   ', x)


def split7(cap):
    """Step MC11's instances (G, x): x of degree 2, neighbours a !~ b; G' = G - x.
    Simple 2EC graphs on 4..7 vertices in maincomp order, every eligible x, the
    first `cap` instances.  Tallies (delta2, dim U, c) against (MC-62)/(MC-64), c :=
    dim(U + K l_ab) - 1 read at the same certified picture."""
    tally = Counter()
    k = 0
    for name, E in two_ec_graphs(7, 4):
        nb = neighbors(E)
        for x in verts_of(E):
            if len(nb[x]) != 2:
                continue
            a, b = sorted(nb[x])
            if b in nb[a]:
                continue
            Ep = [e for e in E if x not in e]
            Vp = verts_of(Ep)
            obs = read_orbit(Ep, Vp, a, b, f'split:{name}:{x}')
            if obs is None:
                tally['no certified picture'] += 1
                continue
            dU, pa_off, pb_off, nc = obs
            orb = orbit_name(dU, pa_off, pb_off)
            pdU, porb, d2t, adj, extra = predict(Ep, Vp, a, b)
            tally[(f'delta2={d2t}', f'dimU={dU} (pred {pdU})', f'orbit {orb} (pred {porb})',
                   'match' if (dU == pdU and orb == porb) else 'MISMATCH')] += 1
            k += 1
            if k >= cap:
                break
        if k >= cap:
            break
    print(f'Step MC11 instances (first {k} of the simple 2EC graphs on 4..7 vertices):')
    for key, v in sorted(tally.items(), key=str):
        print(f'  {key}: {v}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--split7', type=int, default=0)
    ap.add_argument('--cells8', action='store_true')
    ap.add_argument('--sparse', type=int, default=0)
    a = ap.parse_args()
    if a.cells8:
        cells8()
    if a.split7:
        split7(a.split7)
    if a.sparse:
        sparse(a.sparse)


if __name__ == '__main__':
    main()
