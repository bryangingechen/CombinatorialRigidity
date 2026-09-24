#!/usr/bin/env python3
"""
classes.py -- Track J (W4-reopen P1, cell (MC-51)(c) at delta2 = 3, delta in {3,4}).

Pure combinatorics (partition counts, maincomp.def_k); deterministic; writes nothing.
For every k = 1 chain a - y - b (y of degree 2, a, b of degree >= 3, a !~ b) of every
simple 2EC graph on <= N vertices, with G' = G - y:
  delta = def3(G') - def3(G'/ab), delta2 likewise with def2;
keep delta2 = 3 and delta in {3, 4}.  Then report:
  * the def3-classes of G' (maximal rigid sets, singletons otherwise) and the class
    quotient Gamma3 (asserted simple);
  * the minimisers X of c(X) = 6(|X|-1) - 5 e(X) over class sets X containing A, B
    (asserted min = delta, (F-1)/(MC-79)(i)); whether SOME minimiser is a tree
    (then a path A..B, (F-13)) or ALL are cyclic;
  * whether G is in the class S of (MC-76) (2-connected, not cycle/theta, (S)),
    whether G is rigid, and whether y lies in a maximal rigid set R of G (and R = V?).
    python3 classes.py --exh 8
"""
import argparse
import itertools
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts'))
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts', 'w4'))
import scriptpath  # noqa: F401,E402
from maincomp import def_k, two_ec_graphs  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from earstep import contract  # noqa: E402


def nbrs(E):
    nb = {}
    for (u, w) in E:
        nb.setdefault(u, set()).add(w)
        nb.setdefault(w, set()).add(u)
    return nb


def induced(E, S):
    S = set(S)
    return [(u, w) for (u, w) in E if u in S and w in S]


def rigid(E, S):
    S = sorted(S, key=str)
    if len(S) < 2:
        return False
    Ei = induced(E, S)
    return def_k(Ei, 6, S) == 0


def max_rigid_sets(E, V):
    rig = []
    for k in range(len(V), 1, -1):
        for S in itertools.combinations(V, k):
            if any(set(S) <= R for R in rig):
                continue
            if rigid(E, S):
                rig.append(set(S))
    return rig


def class_quotient(E, V):
    rig = max_rigid_sets(E, V)
    cls = [frozenset(R) for R in rig]
    covered = set().union(*rig) if rig else set()
    cls += [frozenset([v]) for v in V if v not in covered]
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


def is_S(E, V):
    for k in range(2, len(V) + 1):
        for S in itertools.combinations(V, k):
            if 2 * len(induced(E, S)) > 3 * k - 4:
                return False
    return True


def two_connected(E, V):
    for v in V:
        rest = [x for x in V if x != v]
        Ei = [(a, b) for (a, b) in E if v not in (a, b)]
        nb = nbrs(Ei)
        seen, st = {rest[0]}, [rest[0]]
        while st:
            x = st.pop()
            for y in nb.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        if len(seen) != len(rest):
            return False
    return True


def analyse(name, E):
    V = verts_of(E)
    nb = nbrs(E)
    out = []
    for y in sorted(nb, key=str):
        if len(nb[y]) != 2:
            continue
        a, b = sorted(nb[y], key=str)
        if b in nb[a] or len(nb[a]) < 3 or len(nb[b]) < 3:
            continue
        Ep = [e for e in E if y not in e]
        Vp = [v for v in V if v != y]
        cab = contract(Ep, a, b)
        vab = [v for v in Vp if v != b]
        d2 = def_k(Ep, 3, Vp) - def_k(cab, 3, vab)
        d3 = def_k(Ep, 6, Vp) - def_k(cab, 6, vab)
        if d2 != 3 or d3 not in (3, 4):
            continue
        cls, of, QE = class_quotient(Ep, Vp)
        A, B = of[a], of[b]
        idx = list(range(len(cls)))
        best, mins = None, []
        others = [i for i in idx if i not in (A, B)]
        for k in range(len(others) + 1):
            for S in itertools.combinations(others, k):
                Y = (A, B) + S
                c, e = cval(Y, QE)
                if best is None or c < best:
                    best, mins = c, [(Y, e)]
                elif c == best:
                    mins.append((Y, e))
        assert best == d3, (name, y, best, d3)
        tree = any(e == len(Y) - 1 for (Y, e) in mins)
        inS = two_connected(E, V) and is_S(E, V)
        Grig = def_k(E, 6, V) == 0
        RG = [R for R in max_rigid_sets(E, V) if y in R]
        sizes = sorted(len(C) for C in cls)
        out.append(dict(name=name, y=y, a=a, b=b, d3=d3, n=len(V), ncls=len(cls), sizes=sizes,
                        tree=tree, nmin=len(mins), inS=inS, Grig=Grig,
                        yR=(len(RG[0]) if RG else 0)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=8)
    ap.add_argument('--nmin', type=int, default=4)
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    pop = two_ec_graphs(a.exh, a.nmin)
    hist = Counter()
    ex = {}
    for name, E in pop:
        for r in analyse(name, E):
            key = (r['d3'], 'tree' if r['tree'] else 'cyclic', 'S' if r['inS'] else '-',
                   'rigid' if r['Grig'] else 'flex', r['yR'] == r['n'], r['ncls'])
            hist[key] += 1
            ex.setdefault(key, []).append((r['name'], r['y'], r['a'], r['b'], r['sizes']))
            if a.verbose:
                print(r)
    print('key = (delta, some minimiser a tree?, G in S?, G rigid?, y-rigid-set = V?, #classes of G\')')
    for k in sorted(hist, key=str):
        print(f'  {k}: {hist[k]}   e.g. {ex[k][:2]}')
    print('total', sum(hist.values()))


if __name__ == '__main__':
    main()
