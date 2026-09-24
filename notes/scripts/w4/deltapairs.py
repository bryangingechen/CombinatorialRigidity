#!/usr/bin/env python3
"""
deltapairs.py -- W4-reopen P1, §(K-main) Step MC17 (the third 2026-09-24 session's Track F): tests of (MC-90)/(MC-91), the relation
between delta = def3(G') - def3(G'/ab) and delta2 = def2(G') - def2(G'/ab).

Everything is exact integer arithmetic (deficiencies via maincomp.def_k, the
(D,D)-count matroid rank; cross-checked against brute-force partition
enumeration with --brute).  Nothing is random.  Writes nothing.

    python3 deltapairs.py --exh 7 [--minY] [--brute]
    python3 deltapairs.py --witness

--exh N: every connected simple graph with minimum degree >= 2 on 3..N
  vertices (hypothesis (H); NOT only 2EC), every unordered pair {a, b}.
  Asserts (MC-91): delta2 <= 2 implies delta <= delta2.  With --minY also
  asserts (MC-90): delta2 = min_{Y ∋ a,b} def2(G'[Y]) and
  delta = min_{Y ∋ a,b} def3(G'[Y]).  With --brute, recomputes f, g by
  enumerating set partitions (n <= 7).  Prints the (adjacent, delta2, delta)
  histogram.
--witness: the explicit graphs realising every pair (delta, delta2) that
  (MC-91) allows, with a !~ b and G' satisfying (H); asserts the claimed values.
"""
import argparse
import os
import sys
from collections import Counter
from itertools import combinations

W4 = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(W4))
sys.path.insert(0, W4)
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from maincomp import def_k, connected_graphs, decode  # noqa: E402


def contract(edges, a, b):
    """G'/ab as a multigraph: b renamed a, loops dropped, parallels KEPT (the
    maximum over partitions with a, b in one part counts them)."""
    out = []
    for (u, w) in edges:
        u2 = a if u == b else u
        w2 = a if w == b else w
        if u2 != w2:
            out.append((u2, w2))
    return out


def deltas(E, V, a, b):
    Vc = [v for v in V if v != b]
    Ec = contract(E, a, b)
    f2, f3 = def_k(E, 3, V), def_k(E, 6, V)
    g2, g3 = def_k(Ec, 3, Vc), def_k(Ec, 6, Vc)
    return f2 - g2, f3 - g3


def induced(E, Y):
    Ys = set(Y)
    return [(u, w) for (u, w) in E if u in Ys and w in Ys]


def minY(E, V, a, b):
    rest = [v for v in V if v not in (a, b)]
    m2 = m3 = None
    for r in range(len(rest) + 1):
        for S in combinations(rest, r):
            Y = [a, b] + list(S)
            EY = induced(E, Y)
            d2, d3 = def_k(EY, 3, Y), def_k(EY, 6, Y)
            m2 = d2 if m2 is None else min(m2, d2)
            m3 = d3 if m3 is None else min(m3, d3)
    return m2, m3


def brute(E, V, D, together=None):
    best = None
    idx = {v: i for i, v in enumerate(V)}

    def rec(i, lab, k):
        nonlocal best
        if i == len(V):
            if together and lab[idx[together[0]]] != lab[idx[together[1]]]:
                return
            d = sum(1 for (u, w) in E if lab[idx[u]] != lab[idx[w]])
            val = D * (k - 1) - (D - 1) * d
            best = val if best is None else max(best, val)
            return
        for c in range(k + 1):
            lab.append(c)
            rec(i + 1, lab, max(k, c + 1))
            lab.pop()
    rec(0, [], 0)
    return best


def exh(N, want_minY, want_brute):
    lev = connected_graphs(N)
    hist = Counter()
    ngr = npairs = 0
    for n in range(3, N + 1):
        for code in lev[n]:
            E = decode(n, code)
            V = list(range(n))
            deg = Counter()
            for (u, w) in E:
                deg[u] += 1
                deg[w] += 1
            if min(deg[v] for v in V) < 2:
                continue
            ngr += 1
            adj = set(E) | {(w, u) for (u, w) in E}
            for a, b in combinations(V, 2):
                npairs += 1
                d2, d3 = deltas(E, V, a, b)
                assert 0 <= d2 <= 3 and 0 <= d3 <= 6, (n, code, a, b, d2, d3)
                if d2 <= 2:
                    assert d3 <= d2, ('F-2 FAILS', n, code, a, b, d2, d3)
                if want_minY:
                    m2, m3 = minY(E, V, a, b)
                    assert (m2, m3) == (d2, d3), ('F-1 FAILS', n, code, a, b,
                                                  d2, d3, m2, m3)
                if want_brute:
                    f2, f3 = brute(E, V, 3), brute(E, V, 6)
                    g2 = brute(E, V, 3, (a, b))
                    g3 = brute(E, V, 6, (a, b))
                    assert (f2 - g2, f3 - g3) == (d2, d3), ('brute', n, code, a, b)
                hist[((a, b) in adj, d2, d3)] += 1
    print(f'(H) graphs on 3..{N} vertices: {ngr}; unordered pairs: {npairs}')
    print(f'asserted: F-2 (delta2 <= 2 => delta <= delta2)'
          + ('; F-1 (min over induced Y)' if want_minY else '')
          + ('; brute-force partitions agree' if want_brute else ''))
    print('histogram (adjacent, delta2, delta): count')
    for key in sorted(hist):
        print(f'  adj={int(key[0])} delta2={key[1]} delta={key[2]}: {hist[key]}')


def cyc(n, off=0):
    return [(off + i, off + (i + 1) % n) for i in range(n)]


def witness():
    rows = []
    # (0,0): K4 minus an edge, the two degree-3 vertices... use a, b in a
    # common triangle-free rigid set: K_{2,3} is def2-rigid, a, b = the 2-side.
    k23 = [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]
    rows.append(('K_{2,3}, a,b the two hubs', k23, 0, 1, (0, 0)))
    # (0,1): C4, a, b opposite.
    rows.append(('C4, a,b opposite', cyc(4), 0, 2, (1, 0)))
    # (1,1): two triangles joined by a bridge, a, b in different triangles,
    # neither a bridge end.
    tt = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]
    rows.append(('two triangles + bridge 2-3, a=0, b=5', tt, 0, 5, (1, 1)))
    # (0,2): C5, a, b at distance 2.
    rows.append(('C5, a,b at distance 2', cyc(5), 0, 2, (2, 0)))
    # (1,2): triangle - bridge - C4, a in triangle, b in C4.
    tc = [(0, 1), (1, 2), (2, 0), (2, 3)] + [(3, 4), (4, 5), (5, 6), (6, 3)]
    rows.append(('triangle 012 - bridge 2-3 - C4 3456, a=0, b=5', tc, 0, 5, (2, 1)))
    # (2,2): three triangles in a chain of two bridges, a, b in the end ones.
    ttt = [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3), (5, 6),
           (6, 7), (7, 8), (8, 6)]
    rows.append(('triangles 012-345-678, bridges 2-3, 5-6, a=0, b=8', ttt, 0, 8, (2, 2)))
    # (0,3): C6, a, b opposite.
    rows.append(('C6, a,b opposite', cyc(6), 0, 3, (3, 0)))
    # (j,3), j = 1..6: C_{6+j}, a, b at distance floor((6+j)/2).
    for j in range(1, 7):
        n = 6 + j
        rows.append((f'C{n}, a,b at distance {n // 2}', cyc(n), 0, n // 2, (3, j)))
    bad = 0
    for name, E, a, b, (w2, w3) in rows:
        V = sorted({v for e in E for v in e})
        deg = Counter()
        for (u, w) in E:
            deg[u] += 1
            deg[w] += 1
        assert min(deg[v] for v in V) >= 2
        assert (a, b) not in E and (b, a) not in E
        d2, d3 = deltas(E, V, a, b)
        ok = (d2, d3) == (w2, w3)
        bad += not ok
        print(f'{name:<52} delta2={d2} delta={d3}  {"OK" if ok else "FAIL"}')
    return bad


def akb():
    bad = 0
    for n, want in [(5, (1, 0)), (7, (1, 1))]:
        Ep = cyc(n)                     # G' = C_n, a = 0, b = 1 adjacent
        a, b = 0, 1
        V = list(range(n))
        d2, d3 = deltas(Ep, V, a, b)
        x1, x2 = n, n + 1
        E = Ep + [(a, x1), (x1, x2), (x2, b)]
        VG = V + [x1, x2]
        rigid = []
        for r in range(2, len(VG) + 1):
            for Y in combinations(VG, r):
                if def_k(induced(E, Y), 3, list(Y)) == 0:
                    rigid.append(Y)
        ok = (d2, d3) == want and not rigid
        bad += not ok
        print(f"G' = C{n}, a ~ b, ear k = 2 (G = theta(1,3,{n - 1})): delta2={d2} delta={d3}; "
              f"def2-rigid induced subgraphs of G: {len(rigid)}  {'OK' if ok else 'FAIL'}")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--minY', action='store_true')
    ap.add_argument('--brute', action='store_true')
    ap.add_argument('--witness', action='store_true')
    ap.add_argument('--akb', action='store_true')
    a = ap.parse_args()
    bad = 0
    if a.exh:
        exh(a.exh, a.minY, a.brute)
    if a.witness:
        bad += witness()
    if a.akb:
        bad += akb()
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
