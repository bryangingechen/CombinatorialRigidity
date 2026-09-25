#!/usr/bin/env python3
"""wsearch.py -- §(K-main) Step MC21, the second reading of 2026-09-25 ((MC-163); ported from the reader's scratch): does (MC-143) ALONE close the Case II-cyclic chains?

For each Case II-cyclic instance (the six 13-vertex chains findcyc.py prints, hard-coded as in
cycprobe.py, plus ringprobe.py's in-S C10 rings with n <= 17), enumerate EVERY vertex set W with
y in W, W != V(G), and test (MC-143)'s hypotheses exactly:
  G[W] of minimum degree >= 2 and connected, def3(G[W]) = 0 (rigid), G/G[W] simple, and
  def2(G) = def2(G[W]) + def2(G/G[W]) (additive).
Prints the number of W passing each filter.  Pure combinatorics (count-matroid deficiencies,
exact integers); exhaustive over the stated subsets; deterministic.  Run from the repository root:
    PYTHONHASHSEED=0 python3 notes/scripts/w4/wsearch.py
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coverstruct as cs  # noqa: E402
import ringprobe as rp  # noqa: E402
from exactcore import neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402

CASES13 = [('L???C@_F?sW_Go', 6), ('L???C@_F?sW_Go', 5), ('L???E?oBECDODO', 6),
           ('L??CAA_EAgDG@g', 5), ('L??CAA_EAgDG@g', 2), ('L??CB@Oa@GB_?s', 4)]


def connected(E, W):
    W = set(W)
    nb = {v: set() for v in W}
    for u, w in E:
        nb[u].add(w); nb[w].add(u)
    s = next(iter(W)); seen = {s}; st = [s]
    while st:
        v = st.pop()
        for x in nb[v]:
            if x not in seen:
                seen.add(x); st.append(x)
    return seen == W


def search(label, E, V, y):
    nb = neighbors(E)
    a, b = sorted(nb[y], key=str)
    assert cs.in_class_S(E, V), label
    D2 = cs.d2(E, V)
    rest = [v for v in V if v not in (y, a, b)]
    cnt = dict(tested=0, mindeg=0, simple=0, rigid=0, additive=0)
    found = []
    for r in range(len(rest)):          # r < len(rest): W != V
        for S in itertools.combinations(rest, r):
            W = [y, a, b] + list(S)
            cnt['tested'] += 1
            H = cs.induced(E, W)
            dg = {v: 0 for v in W}
            for u, w in H:
                dg[u] += 1; dg[w] += 1
            if min(dg.values()) < 2 or not connected(H, W):
                continue
            cnt['mindeg'] += 1
            if not cs.simple_quotient(E, W):
                continue
            cnt['simple'] += 1
            if cs.d3(H, W) != 0:
                continue
            cnt['rigid'] += 1
            if D2 != cs.d2(H, W) + cs.quotient_def2(E, W):
                continue
            cnt['additive'] += 1
            found.append(sorted(W, key=str))
    print(label, f'n={len(V)} y={y} a={a} b={b}', cnt,
          'first W:' if found else '', found[0] if found else '', flush=True)
    return cnt['additive']


def main():
    tot = 0
    for g6, y in CASES13:
        E, V = cs.g6decode(g6)
        tot += search(f'{g6}:y{y}', E, V, y) > 0
    for (label, Ep, a, b, blobs) in rp.instances():
        if not label.startswith('Y4'):
            continue
        E = Ep + [(a, 'y'), ('y', b)]
        V = verts_of(E)
        if not cs.in_class_S(E, V) or len(V) > 17:
            print(label, f'n={len(V)} skipped (not in S, or n > 17)')
            continue
        tot += search(label, E, V, 'y') > 0
    print('instances with some (MC-143) W:', tot)


if __name__ == '__main__':
    main()
