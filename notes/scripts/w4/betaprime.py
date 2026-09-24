#!/usr/bin/env python3
"""betaprime.py -- §(K-main) Step MC16, second reading (Track G): a witness that (MC-81)(beta')'s "at EVERY proper rigid W with
simple quotient and 1 <= def2(H) < def2(G), in S" cannot hold: a member of S with such a W that is
NOT additive (so (MC-39)(i) fails there, by (MC-68)).  Exact deficiencies only.
Run from the repository root:  PYTHONHASHSEED=0 python3 <this file> [--cert]"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import relmax as TG  # noqa: E402

C = [(f'c{i}', f'c{(i + 1) % 6}') for i in range(6)]          # W = C6
Z = [('z1', 'z2'), ('z2', 'z3'), ('z1', 'c0'), ('z2', 'c2'), ('z3', 'c4')]
EAR = [('c1', 'e1'), ('e1', 'e2'), ('e2', 'e3'), ('e3', 'e4'), ('e4', 'c3')]   # k = 4 ear
E = C + Z + EAR
V = TG.verts(E)
W = [f'c{i}' for i in range(6)]
dG, dH, dQ = TG.counts(E, V, W)
print(f'n={len(V)} m={len(E)} in S: {TG.in_S(E, V)}; def2(G)={dG} def3(G)={TG.d3(E, V)}')
print(f'W = C6: rigid {TG.d3(TG.induced(E, W), W) == 0}, proper, G/H simple {TG.simple_quotient(E, W)}; '
      f'def2(H)={dH} def2(G/H)={dQ}: 1 <= def2(H) < def2(G) is {1 <= dH < dG}; '
      f'additive {dG == dH + dQ}')
Wp = W + ['z1', 'z2', 'z3']
print(f'the maximal rigid set containing W: {sorted(max((P for P in TG.pstar(E, V) if set(W) <= P), key=len))}')

if '--cert' in sys.argv:
    from contractcheck import run as cs_run
    for tag in ('d0', 'd1'):
        cf, nj, verdict, line = cs_run('C6pend', E, W, f'trackG:C6pend:{tag}')
        print(f'coreshrink at W = C6 [{tag}]: (i)={int(cf)} (ii)={int(nj)} {verdict}')
    if not TG.in_S(E, V):
        raise SystemExit('not in S')
    # the Theorem-S core of the same graph, for contrast
    x, Wg = TG.g2_core(E, V)
    print(f'(MC-120) core of the same graph: x={x} W={sorted(Wg) if Wg else None}')
