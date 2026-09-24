#!/usr/bin/env python3
"""
earcover.py -- Step MC21 (Track J) (W4-reopen P1): does the EAR step alone reach every graph of the class S?

Pure combinatorics (count-matroid deficiencies, exact integers); deterministic; writes nothing.
For every class-S member G (Step MC16's definition, coverstruct.in_class_S), every chain is put in
one of the cells
  USABLE   a landed step applies (coverstruct.chain_data's rule: k >= 3; k = 2 with delta = 0 or
           (a !~ b and delta2 >= 2); k = 1 with delta = 0 or delta >= 5);
  A'       k = 2, a ~ b, delta = 1                                   (closed by Step MC17's (MC-105));
  C'-I     k = 1, 1 <= delta <= 4, and (MC-142)'s witness exists: a set Y of def3-classes of G' = G - y
           through [a], [b] with c(Y) <= 4, c(Y) minimal among the subsets of Y through [a], [b],
           and union(Y) + y != V(G).  Then W = union(Y) + y is ASSERTED to be rigid in G, with G/G[W]
           simple and def2(G) = def2(G[W]) + def2(G/G[W])                (closed by (MC-143));
  C'-II    k = 1, 1 <= delta <= 4, no such Y; split into -tree / -cyclic by whether the class
           quotient of G' is a tree.
The claim under test ((MC-148)): EVERY class-S member has a chain in USABLE, A' or C'-I.  Also ASSERTED
at every C'-II chain: G is rigid, and V(Gamma3) is the unique minimiser (the (MC-145) dichotomy).
Classes of G' are computed as: u ~ v iff def3(G') = def3(G'/uv) ((MC-90): a common rigid subgraph).
Modes:  --necklaces | --hunt FILE|-  (graph6, e.g. geng -C -d2 -t -q n 0:floor((3n-4)/2)) |
        --witness N --smax S [--cores K4,dC4]   (coverstruct's subdivision witness set)
PYTHONHASHSEED=0, repository root.
"""
import argparse
import itertools
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
import coverstruct as cs  # noqa: E402
from exactcore import neighbors  # noqa: E402


def classes_of(E, V):
    f3 = cs.d3(E, V)
    parent = {v: v for v in V}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for u, w in itertools.combinations(V, 2):
        if find(u) == find(w):
            continue
        mp = cs.merge_pair(E, u, w)
        Vm = [v for v in V if v != w]
        if cs.d3(mp, Vm) == f3:
            parent[find(w)] = find(u)
    groups = {}
    for v in V:
        groups.setdefault(find(v), []).append(v)
    cls = [frozenset(g) for g in groups.values()]
    of = {v: i for i, C in enumerate(cls) for v in C}
    qe = Counter()
    for (u, w) in E:
        i, j = of[u], of[w]
        if i != j:
            qe[frozenset((i, j))] += 1
    assert all(m == 1 for m in qe.values()), 'class quotient not simple'
    return cls, of, [tuple(sorted(e)) for e in qe]


def cval(Y, QE):
    Y = set(Y)
    e = sum(1 for (i, j) in QE if i in Y and j in Y)
    return 6 * (len(Y) - 1) - 5 * e, e


def cprime_case(E, V, y, a, b, delta=None):
    """(MC-142) for the k = 1 chain a - y - b.  Returns ('I', W) or ('II-tree'|'II-cyclic', None).
    If delta (chain_data's) is given, ASSERT it equals min c(Y) over class sets through A, B ((MC-79)(i))."""
    Ep = [e for e in E if y not in e]
    Vp = [v for v in V if v != y]
    cls, of, QE = classes_of(Ep, Vp)
    A, B = of[a], of[b]
    assert A != B
    others = [i for i in range(len(cls)) if i not in (A, B)]
    cv = {}
    for k in range(len(others) + 1):
        for S in itertools.combinations(others, k):
            Y = frozenset((A, B) + S)
            cv[Y] = cval(Y, QE)[0]
    assert delta is None or min(cv.values()) == delta, ('(MC-79)(i)', delta, min(cv.values()))
    full = frozenset(range(len(cls)))
    for Y, c in sorted(cv.items(), key=lambda t: len(t[0])):
        if c > 4 or Y == full:
            continue
        if all(cv[Z] >= c for Z in cv if Z <= Y):
            W = set(y for _ in [0])
            for i in Y:
                W |= cls[i]
            W = sorted(W, key=str)
            H = cs.induced(E, W)
            assert cs.d3(H, W) == 0, ('MC-142 rigid', W)
            assert cs.simple_quotient(E, W), ('MC-142 simple', W)
            assert cs.d2(E, V) == cs.d2(H, W) + cs.quotient_def2(E, W), ('MC-142 additive', W)
            nbH = neighbors(H)
            assert min(len(nbH[v]) for v in W) >= 2
            return 'I', W
    # Case II: assert the dichotomy's content
    delta = min(cv.values())
    assert cv[full] == delta and [Y for Y, c in cv.items() if c == delta] == [full]
    assert cs.d3(E, V) == 0, 'Case II but G not rigid'
    tree = cval(full, QE)[1] == len(full) - 1
    return ('II-tree' if tree else 'II-cyclic'), None


def classify_graph(E, V, full=False):
    """Returns (list of cells per chain, closable?)."""
    cells = []
    closable = False
    for (a, b, I) in sorted(cs.chains(E), key=lambda t: -len(t[2])):
        c = cs.chain_data(E, V, a, b, I)
        if c['usable']:
            cells.append(('USABLE', c['k'], c['delta']))
            closable = True
        elif c['k'] == 2 and c['adj'] and c['delta'] == 1:
            cells.append(("A'", 2, 1))
            closable = True
        else:
            assert c['k'] == 1 and 1 <= c['delta'] <= 4, c
            kind, W = cprime_case(E, V, I[0], a, b, c['delta'])
            cells.append(("C'-" + kind, 1, c['delta']))
            if kind == 'I':
                closable = True
        if closable and not full:
            break
    return cells, closable


def run_pop(gen, label, full):
    tot = nS = nclos = 0
    hist = Counter()
    worst = []
    for name, E, V in gen:
        tot += 1
        if not cs.in_class_S(E, V):
            continue
        nS += 1
        cells, ok = classify_graph(E, V, full)
        nclos += ok
        for c in cells:
            hist[c] += 1
        if not ok:
            worst.append((name, cells))
        if not any(c[0] == 'USABLE' for c in cells) or full:
            if not any(c[0] == 'USABLE' for c in cells):
                print(f'  no usable chain: {name} n={len(V)} cells={cells} EAR-closable={ok}')
    print(f'{label}: {tot} graphs, {nS} in class S, {nclos} with an EAR-closable chain '
          f'(USABLE / A\' / C\'-I); chain-cell histogram {dict(sorted(hist.items()))}')
    assert not worst, worst
    return hist


def gen_necklaces():
    for u in ['QsQsQ', 'QQQQs', 'QQQQQ', 'QsQsQs', 'AsAsAs', 'AAAAAA', 'AAAAAAA', 'QQQQQQ',
              'QsQs', 'AAAAA', 'QQQQQQQ', 'QsQsQss', 'TsTsTs', 'TTTTTT', 'TTTTTTT']:
        E, V = cs.necklace(u)
        yield u, E, V


def gen_hunt(path):
    for line in (sys.stdin if path == '-' else open(path)):
        if line.strip():
            E, V = cs.g6decode(line)
            yield line.strip(), E, V


def gen_witness(nmax, smax, cores):
    for name, E, V in cs.witness_set(nmax, smax, cores):
        yield name, E, V


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--necklaces', action='store_true')
    ap.add_argument('--hunt', default='')
    ap.add_argument('--witness', type=int, default=0)
    ap.add_argument('--smax', type=int, default=2)
    ap.add_argument('--cores', default='')
    ap.add_argument('--full', action='store_true', help='classify every chain, not only until closable')
    a = ap.parse_args()
    if a.necklaces:
        run_pop(gen_necklaces(), 'necklaces', True)
    if a.hunt:
        run_pop(gen_hunt(a.hunt), f'hunt {a.hunt}', a.full)
    if a.witness:
        cores = a.cores.split(',') if a.cores else None
        run_pop(gen_witness(a.witness, a.smax, cores), f'witness n<={a.witness}', a.full)


if __name__ == '__main__':
    main()
