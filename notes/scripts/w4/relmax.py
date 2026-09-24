#!/usr/bin/env python3
"""
relmax.py -- §(K-main) Step MC16, second reading (the third 2026-09-24 session's Track G): checks, at
witnesses, of the lemma (MC-119) of Step MC16 and of the core choice of (MC-120).  Pure
combinatorics (exact integer deficiencies, count-matroid ranks, no randomness) except
--cert, which calls coreshrink's own seeded sampler through contractcheck.run.

Run from the repository root:
  PYTHONHASHSEED=0 python3 <this file> --lemma 8        # (MC-119) on every simple 2EC graph, n <= 8
  PYTHONHASHSEED=0 python3 <this file> --families       # (MC-120) at Track A's stuck families
  PYTHONHASHSEED=0 python3 <this file> --cert           # coreshrink (i)/(ii) at (MC-120)'s cores
  PYTHONHASHSEED=0 python3 <this file> --witness 16 --smax 4 --cores K4,dC4   # Track A's witness set
  PYTHONHASHSEED=0 python3 <this file> --pairs88 400    # (MC-88) at family pairs and 400 seeded random graphs

(MC-119)  x a vertex of degree <= 2 (or x = None and G non-rigid); W a maximal def3-rigid
       subset of V - x (of V), |W| >= 2, with G/G[W] simple.  Then
       def2(G) = def2(G[W]) + def2(G/G[W])        (ADDITIVITY).
Maximal rigid sets are computed as the classes of "u, w lie in a common def3-rigid set"
<=> def3(G with u, w identified) = def3(G) (an optimal partition with u ~ w exists, and
parts of optimal partitions are rigid); cross-checked against brute force for n <= 8.
"""
import argparse
import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors  # noqa: E402
from maincomp import def_k, two_ec_graphs  # noqa: E402
from nogood_subdiv import branch_decomposition, contraction, count_matroid_rank  # noqa: E402
from splitext import contract as merge_pair  # noqa: E402


def d2(E, V):
    return def_k(E, 3, V)


def d3(E, V):
    return def_k(E, 6, V)


def induced(E, W):
    W = set(W)
    return [e for e in E if e[0] in W and e[1] in W]


def verts(E):
    return sorted({v for e in E for v in e}, key=str)


def simple_quotient(E, W):
    W = set(W)
    cnt = {}
    for u, w in E:
        if (u in W) != (w in W):
            o = w if u in W else u
            cnt[o] = cnt.get(o, 0) + 1
    return all(c <= 1 for c in cnt.values())


def heavy_outside(E, W):
    """outside vertices with >= 2 neighbours in W."""
    W = set(W)
    cnt = {}
    for u, w in E:
        if (u in W) != (w in W):
            o = w if u in W else u
            cnt[o] = cnt.get(o, 0) + 1
    return sorted((o for o, c in cnt.items() if c >= 2), key=str)


def counts(E, V, W):
    H = induced(E, W)
    Q = contraction(E, sorted(W, key=str))
    return d2(E, V), d2(H, sorted(W, key=str)), d2(Q, verts(Q))


def pstar(E, V):
    """The non-singleton maximal def3-rigid sets of (V, E) (isolated vertices allowed)."""
    base = d3(E, V)
    parent = {v: v for v in V}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for u, w in combinations(V, 2):
        if find(u) == find(w):
            continue
        mp = merge_pair(E, u, w)
        if d3(mp, [v for v in V if v != w]) == base:
            parent[find(w)] = find(u)
    cls = {}
    for v in V:
        cls.setdefault(find(v), set()).add(v)
    return [frozenset(c) for c in cls.values() if len(c) >= 2]


def rigid_brute(E, V):
    out = []
    for r in range(2, len(V) + 1):
        for W in combinations(V, r):
            if d3(induced(E, W), list(W)) == 0:
                out.append(frozenset(W))
    return [W for W in out if not any(W < X for X in out)]


def chains(E):
    hubs, br = branch_decomposition(E)
    return [(a, b, I) for (a, b, I) in (br or []) if I]


# ---------------------------------------------------------------- (MC-119) exhaustive

def run_lemma(nmax, brute_to):
    from collections import Counter
    tally = Counter()
    for name, E in two_ec_graphs(nmax):
        V = verts(E)
        nb = neighbors(E)
        n = len(V)
        if n <= brute_to:
            assert sorted(map(sorted, pstar(E, V))) == sorted(map(sorted, rigid_brute(E, V))), name
        # x = None: G non-rigid, W a maximal rigid set of G
        if d3(E, V) > 0:
            for W in pstar(E, V):
                assert simple_quotient(E, W), (name, sorted(W))
                dG, dH, dQ = counts(E, V, W)
                assert dG == dH + dQ, ('(MC-119), x = None', name, sorted(W), dG, dH, dQ)
                tally['x=None: additive'] += 1
        # x of degree 2
        for x in V:
            if len(nb[x]) != 2:
                continue
            Ex = [e for e in E if x not in e]
            Vx = [v for v in V if v != x]
            if n <= brute_to:
                assert sorted(map(sorted, pstar(Ex, Vx))) == \
                    sorted(map(sorted, rigid_brute(Ex, Vx))), (name, x)
            # is x on a chain with k >= 2?  (a degree-2 neighbour)
            k2 = any(len(nb[y]) == 2 for y in nb[x])
            for W in pstar(Ex, Vx):
                hv = heavy_outside(E, W)
                if hv:
                    # (MC-119)'s simplicity clause: only x itself can be heavy, and only when
                    # x's chain has k = 1 (both ends in W)
                    assert hv == [x] and not k2, (name, x, sorted(W), hv)
                    tally['deg-2 x: G/H not simple (x has both ends in W, k = 1)'] += 1
                    continue
                dG, dH, dQ = counts(E, V, W)
                assert dG == dH + dQ, ('(MC-119)', name, x, sorted(W), dG, dH, dQ)
                tally['deg-2 x: simple, additive'] += 1
    print(f'(MC-119) on every simple 2EC graph with n <= {nmax} (P* cross-checked by brute '
          f'force for n <= {brute_to}); every assert held:')
    for k, v in sorted(tally.items()):
        print(f'  {k}: {v}')


# ---------------------------------------------------------------- families

T_UNIT = {  # theta(2,3,4): hubs h, h'; paths h-y-h', h-t1-w-h', h-v-t2-v'-h'; in t1, out t2
    'verts': ['h', 'hp', 'y', 't1', 'w', 'v', 't2', 'vp'],
    'edges': [('h', 'y'), ('y', 'hp'), ('h', 't1'), ('t1', 'w'), ('w', 'hp'),
              ('h', 'v'), ('v', 't2'), ('t2', 'vp'), ('vp', 'hp')],
    'in': 't1', 'out': 't2'}
UNITS = {
    's': {'verts': ['o'], 'edges': [], 'in': 'o', 'out': 'o'},
    'Q': {'verts': ['a', 'p', 'c', 'r'], 'edges': [('a', 'p'), ('p', 'c'), ('c', 'r'), ('r', 'a')],
          'in': 'a', 'out': 'c'},
    'A': {'verts': ['a', 'p', 'q', 'b'], 'edges': [('a', 'p'), ('p', 'q'), ('q', 'b'), ('b', 'a')],
          'in': 'a', 'out': 'b'},
    'T': T_UNIT,
}


def necklace(word):
    E, ins, outs = [], [], []
    for i, u in enumerate(word):
        U = UNITS[u]
        lab = {v: f'{u}{i}.{v}' for v in U['verts']}
        E += [(lab[a], lab[b]) for a, b in U['edges']]
        ins.append(lab[U['in']])
        outs.append(lab[U['out']])
    L = len(word)
    for i in range(L):
        E.append((outs[i], ins[(i + 1) % L]))
    return E, verts(E)


def comps(E, V):
    nb = {v: set() for v in V}
    for u, w in E:
        nb[u].add(w)
        nb[w].add(u)
    seen, out = set(), []
    for s in V:
        if s in seen:
            continue
        c, st = {s}, [s]
        while st:
            u = st.pop()
            for y in nb[u]:
                if y not in c:
                    c.add(y)
                    st.append(y)
        seen |= c
        out.append(c)
    return out


def two_connected(E, V):
    if len(comps(E, V)) != 1:
        return False
    for v in V:
        if len(comps([e for e in E if v not in e], [u for u in V if u != v])) != 1:
            return False
    return True


def cond_S(E, V):
    big = [e for e in E for _ in range(2)]
    return count_matroid_rank(big, V, k=3, ell=4) == len(big)


def in_S(E, V):
    nb = neighbors(E)
    degs = sorted(len(nb[v]) for v in V)
    cyc = all(d == 2 for d in degs)
    theta = degs.count(3) == 2 and degs.count(2) == len(V) - 2
    return degs[0] >= 2 and two_connected(E, V) and not cyc and not theta and cond_S(E, V)


def chain_cell(E, V, a, b, I):
    nb = neighbors(E)
    Ws = set(I)
    Ep = [e for e in E if e[0] not in Ws and e[1] not in Ws]
    Vp = [v for v in V if v not in Ws]
    mp = merge_pair(Ep, a, b)
    Vm = [v for v in Vp if v != b]
    dl = d3(Ep, Vp) - d3(mp, Vm)
    dl2 = d2(Ep, Vp) - d2(mp, Vm)
    adj = b in nb[a]
    k = len(I)
    if k >= 3:
        use = True
    elif k == 2:
        use = dl == 0 or (not adj and dl2 >= 2)
    else:
        use = dl == 0 or dl >= 5
    return dict(k=k, adj=adj, delta=dl, delta2=dl2, usable=use, I=I, a=a, b=b)


def g2_core(E, V):
    """(MC-120)'s core: G non-rigid -> a non-singleton maximal rigid set of G;
    G rigid -> for the first blocked chain vertex x (chains in branch order) such that
    V - x has a non-singleton rigid subset, a maximal one."""
    if d3(E, V) > 0:
        P = pstar(E, V)
        return None, (sorted(P, key=lambda W: sorted(map(str, W)))[0] if P else None)
    for (a, b, I) in chains(E):
        c = chain_cell(E, V, a, b, I)
        if c['usable']:
            continue
        x = I[0]
        Ex = [e for e in E if x not in e]
        Vx = [v for v in V if v != x]
        P = pstar(Ex, Vx)
        if P:
            return x, sorted(P, key=lambda W: sorted(map(str, W)))[0]
    return None, None


FAMILIES = ['QsQsQ', 'QQQQs', 'QQQQQ', 'QsQsQs', 'QQQQQQ', 'QQQQQQQ', 'AsAsAs', 'AAAAAA',
            'AAAAAAA', 'TsTsTs', 'TTTTTT', 'TTTTTTT', 'QsAsTs', 'QAQAQA']


def run_families(cert):
    import random
    out = []
    for word in FAMILIES:
        E, V = necklace(word)
        cells = [chain_cell(E, V, a, b, I) for (a, b, I) in chains(E)]
        nuse = sum(c['usable'] for c in cells)
        rigid = d3(E, V) == 0
        print(f'{word}: n={len(V)} m={len(E)} classS={in_S(E, V)} def2={d2(E, V)} '
              f'def3={d3(E, V)} ({"rigid" if rigid else "non-rigid"}); usable chains '
              f'{nuse}/{len(cells)}; cells (k, a~b, delta, delta2) = '
              f'{sorted(set((c["k"], int(c["adj"]), c["delta"], c["delta2"]) for c in cells))}')
        # every blocked chain vertex x, every maximal rigid subset of V - x: (MC-119)
        nW = 0
        for c in cells:
            if c['usable']:
                continue
            for x in c['I']:
                Ex = [e for e in E if x not in e]
                Vx = [v for v in V if v != x]
                for W in pstar(Ex, Vx):
                    assert simple_quotient(E, W), (word, x, sorted(W))
                    dG, dH, dQ = counts(E, V, W)
                    assert d3(induced(E, W), sorted(W, key=str)) == 0
                    assert dG == dH + dQ, (word, x, sorted(W), dG, dH, dQ)
                    nW += 1
        x, W = g2_core(E, V)
        if W is not None:
            dG, dH, dQ = counts(E, V, W)
            assert simple_quotient(E, W) and len(W) < len(V) and dG == dH + dQ
            print(f'   (MC-119) at every blocked chain vertex x and every maximal rigid W of '
                  f'G - x: {nW} (x, W) pairs, all simple and additive')
            print(f'   (MC-120) core: x={x} W={sorted(map(str, W))} |W|={len(W)}: '
                  f'def2 G/H/(G/H) = {dG}/{dH}/{dQ}, additive, G/H simple')
            out.append((word, E, W))
    if cert:
        from contractcheck import run as cs_run
        for word, E, W in out:
            if len(E) > 40:
                print(f'   coreshrink skipped at {word} (m = {len(E)} > 40)')
                continue
            cf, nj, verdict, line = cs_run(word, E, W, f'trackG:{word}')
            print(f'   coreshrink at {word}, W={sorted(map(str, W))}: (i)={int(cf)} (ii)={int(nj)} '
                  f'{verdict}')
        del random


# ---------------------------------------------------------------- Track A's witness set

def run_witness(nmax, smax, cores):
    """(MC-119) at every degree-2 x (and x = None when G is non-rigid) of every class-S member of
    Step MC16's witness set (coverstruct.witness_set: subdivisions of the named cores), and (MC-120)'s
    core at every member with no usable chain."""
    from collections import Counter
    import coverstruct as SA
    tally = Counter()
    nS = nstuck = 0
    for name, E, V in SA.witness_set(nmax, smax, cores):
        nS += 1
        nb = neighbors(E)
        if d3(E, V) > 0:
            for W in pstar(E, V):
                assert simple_quotient(E, W)
                dG, dH, dQ = counts(E, V, W)
                assert dG == dH + dQ, (name, sorted(W))
                tally['x=None: additive'] += 1
        for x in V:
            if len(nb[x]) != 2:
                continue
            Ex = [e for e in E if x not in e]
            Vx = [v for v in V if v != x]
            for W in pstar(Ex, Vx):
                if heavy_outside(E, W):
                    assert heavy_outside(E, W) == [x]
                    tally['deg-2 x: not simple'] += 1
                    continue
                dG, dH, dQ = counts(E, V, W)
                assert dG == dH + dQ, (name, x, sorted(W))
                tally['deg-2 x: simple, additive'] += 1
        cells = [chain_cell(E, V, a, b, I) for (a, b, I) in chains(E)]
        if not any(c['usable'] for c in cells):
            nstuck += 1
            x, W = g2_core(E, V)
            assert W is not None and simple_quotient(E, W) and len(W) < len(V)
            dG, dH, dQ = counts(E, V, W)
            assert dG == dH + dQ and d3(induced(E, W), sorted(W, key=str)) == 0
            print(f'  no usable chain: {name} n={len(V)} def2={dG} def3={d3(E, V)}: (MC-120) core '
                  f'x={x} |W|={len(W)} def2(H)={dH} def2(G/H)={dQ}, additive')
    print(f'witness set (n <= {nmax}, smax {smax}, cores {cores or "all"}): {nS} class-S members, '
          f'{nstuck} with no usable chain; every assert held:')
    for k, v in sorted(tally.items()):
        print(f'  {k}: {v}')


# ---------------------------------------------------------------- (MC-88) at targeted pairs

def delta_pair(E, V, a, b):
    mp = merge_pair(E, a, b)
    Vm = [v for v in V if v != b]
    return d2(E, V) - d2(mp, Vm), d3(E, V) - d3(mp, Vm)


def run_pairs88(nrand, seed):
    """(MC-88): delta2 = 0 => delta = 0 and delta2 = 1 => delta <= 1, ASSERTED at
    (a) every pair of every family graph G and of every G - C (C a chain of G);
    (b) every pair of nrand seeded random graphs G(n, p), n = 9..12, p in {0.25, 0.35, 0.5}
        (random.Random(seed); support: all labelled graphs on n vertices, edges iid)."""
    import random
    from collections import Counter
    hist = Counter()
    ngraphs = 0

    def check(E, V, tag):
        nonlocal ngraphs
        ngraphs += 1
        for a, b in combinations(V, 2):
            dl2, dl = delta_pair(E, V, a, b)
            hist[(dl2, dl)] += 1
            assert dl2 != 0 or dl == 0, (tag, a, b, dl2, dl)
            assert dl2 != 1 or dl <= 1, (tag, a, b, dl2, dl)

    for word in FAMILIES:
        E, V = necklace(word)
        if len(V) > 28:
            continue
        check(E, V, word)
        for (a, b, I) in chains(E):
            Ws = set(I)
            check([e for e in E if e[0] not in Ws and e[1] not in Ws],
                  [v for v in V if v not in Ws], (word, a, b))
    nfam = ngraphs
    rng = random.Random(seed)
    for i in range(nrand):
        n = 9 + i % 4
        p = (0.25, 0.35, 0.5)[i % 3]
        E = [(u, w) for u, w in combinations(range(n), 2) if rng.random() < p]
        check(E, list(range(n)), ('rand', i))
    print(f'(MC-88) at every pair: {nfam} family graphs and chain deletions (n <= 28), '
          f'{ngraphs - nfam} random graphs (n = 9..12, seed {seed}); every assert held')
    print(f'  (delta2, delta) histogram: {dict(sorted(hist.items()))}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lemma', type=int, default=0)
    ap.add_argument('--brute', type=int, default=8)
    ap.add_argument('--families', action='store_true')
    ap.add_argument('--cert', action='store_true')
    ap.add_argument('--witness', type=int, default=0)
    ap.add_argument('--pairs88', type=int, default=0)
    ap.add_argument('--seed', type=int, default=20260924)
    ap.add_argument('--smax', type=int, default=2)
    ap.add_argument('--cores', default='')
    a = ap.parse_args()
    if a.lemma:
        run_lemma(a.lemma, a.brute)
    if a.families or a.cert:
        run_families(a.cert)
    if a.pairs88:
        run_pairs88(a.pairs88, a.seed)
    if a.witness:
        run_witness(a.witness, a.smax, a.cores.split(',') if a.cores else None)


if __name__ == '__main__':
    main()
