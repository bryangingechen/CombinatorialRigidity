#!/usr/bin/env python3
"""iffwit.py (§(K-main) Steps MC17-MC18's second reading, 2026-09-25; ported from the reader's scratch).
readerE iffwit.py -- witness for the wording repair of (MC-111)(d)'s first
sentence: G' = K_{2,3}, a, b its hubs (a !~ b).  Brute-force partitions
(exact integers; deterministic).  Prints def2(G'), def2(G'/ab) (so delta2),
and def2 of G'' = G' + ab, which is 0: G'' is a def2-rigid subgraph of itself
containing the edge ab, although delta2 = 0."""
def partitions(s):
    if not s: yield []; return
    x, rest = s[0], s[1:]
    for p in partitions(rest):
        for i in range(len(p)): yield p[:i] + [[x] + p[i]] + p[i+1:]
        yield [[x]] + p
def val(P, E, D):
    part = {v: i for i, B in enumerate(P) for v in B}
    d = sum(1 for u, w in E if part[u] != part[w])
    return D*(len(P)-1) - (D-1)*d
def deff(V, E, D, together=None):
    return max(val(P, E, D) for P in partitions(V)
               if together is None or any(together[0] in B and together[1] in B for B in P))
V = [0, 1, 2, 3, 4]              # hubs a = 0, b = 1; paths 0-x-1 for x = 2, 3, 4
E = [(0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 1)]
f2 = deff(V, E, 3); g2 = deff(V, E, 3, (0, 1))
print('K_{2,3}: def2 =', f2, ' def2(G/ab) =', g2, ' delta2 =', f2 - g2)
print("G'' = K_{2,3} + ab: def2 =", deff(V, E + [(0, 1)], 3))
