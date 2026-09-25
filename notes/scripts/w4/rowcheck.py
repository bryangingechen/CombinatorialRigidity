#!/usr/bin/env python3
"""rowcheck.py (§(K-main) Step MC20's second reading, 2026-09-25; ported from the reader's scratch): the line-vector rows of Step MC20's (MC-134) table, transcribed from the PROSE (Pluecker
order 01,02,03,12,13,23), tested for the prose's stated property 'every listed vector brings in a
coordinate the earlier ones lack' (in the listed order), and for rank = row length.  Exact; no rng."""
from fractions import Fraction as F
C = ['01', '02', '03', '12', '13', '23']
def v(*terms):
    out = [0] * 6
    for s, c in terms:
        out[C.index(c)] += s
    return out
p = lambda c: (1, c)   # noqa: E731
m = lambda c: (-1, c)  # noqa: E731
ROWS = {
 '(a) n=3': [v(p('01')), v(p('12')), v(p('02'))],
 '(a) n=4': [v(p('01')), v(p('12')), v(p('23')), v(p('03'))],
 '(a) n=5': [v(p('01')), v(p('12')), v(p('23')), v(p('13')), v(p('01'), p('03'))],
 '(a) n=6': [v(p('01')), v(p('12')), v(p('23')), v(p('13')), v(m('01'), p('12'), m('03'), m('23')), v(p('02'))],
 '(b) k=2 ne': [v(p('01')), v(p('12')), v(p('23'))],
 '(b) k=3 ne': [v(p('01')), v(p('13')), v(p('12'), m('23')), v(p('23'))],
 '(b) k=4 ne': [v(p('01')), v(p('13')), v(p('03')), v(p('02')), v(p('23'))],
 '(b) k=5 ne': [v(p('01')), v(p('13')), v(p('03')), v(p('01'), p('02')), v(p('12')), v(p('23'))],
 '(b) k=2 eq': [v(p('01')), v(p('12')), v(p('02'), p('12'))],
 '(b) k=3 eq': [v(p('01')), v(p('13')), v(p('23')), v(p('02'), p('12'))],
 '(b) k=4 eq': [v(p('01')), v(p('13')), v(p('03')), v(p('02')), v(p('02'), p('12'))],
 '(b) k=5 eq': [v(p('01')), v(p('13')), v(p('23')), v(p('02'), p('03')), v(p('02')), v(p('02'), p('12'))],
 '(c) k=2': [v(p('01')), v(p('12')), v(p('02'))],
 '(c) k=3': [v(p('01')), v(p('13')), v(p('23')), v(p('02'))],
 '(c) k=4': [v(p('01')), v(p('13')), v(p('13'), p('23')), v(p('12')), v(p('02'))],
 '(c) k=5': [v(p('01')), v(p('12')), v(p('13'), p('23')), v(p('03')), v(p('02'), m('23')), v(p('02'))],
}
def rank(M):
    M = [[F(x) for x in r] for r in M]; rk = 0
    for col in range(6):
        piv = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col] / M[rk][col]; M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk
for name, R in ROWS.items():
    seen, bad = set(), []
    for j, r in enumerate(R):
        sup = {i for i in range(6) if r[i]}
        if not (sup - seen): bad.append(j + 1)
        seen |= sup
    print(f'{name:<12} rank {rank(R)}/{len(R)}; listed order fails the "new coordinate" property at vector(s) {bad or "none"}')
