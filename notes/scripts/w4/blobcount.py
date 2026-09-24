#!/usr/bin/env python3
"""blobcount.py -- Step MC21 (Track J), (MC-147) and (MC-146) checked: in a class-S member all of whose chains have k = 1, for
every chain y with delta >= 1, some degree-2 vertex w != y lies in a non-singleton def3-class of
G - y.  (graph6 on stdin, or --necklaces.)  Pure counts; deterministic; asserts; prints a tally."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
import coverstruct as cs
import earcover as ec
from exactcore import neighbors


def check(E, V, tally):
    ch = cs.chains(E)
    if not ch or any(len(I) != 1 for (_, _, I) in ch):
        return
    tally['allk1'] += 1
    nb = neighbors(E)
    deg2 = [v for v in V if len(nb[v]) == 2]
    for (a, b, I) in ch:
        y = I[0]
        Ep = [e for e in E if y not in e]
        Vp = [v for v in V if v != y]
        cls, of, QE = ec.classes_of(Ep, Vp)
        if of[a] == of[b]:
            tally['delta0'] += 1
            continue
        inblob = [w for w in deg2 if w != y and len(cls[of[w]]) > 1]
        assert inblob, ('MC-147 fails', E, y)
        tally['chains'] += 1
        # (MC-146): every non-singleton class X of G - y is rigid in G, with G/G[X] simple and additive
        D2 = cs.d2(E, V)
        for X in cls:
            if len(X) < 2:
                continue
            W = sorted(X, key=str)
            H = cs.induced(E, W)
            assert cs.d3(H, W) == 0 and cs.simple_quotient(E, W), ('MC-146', W)
            assert D2 == cs.d2(H, W) + cs.quotient_def2(E, W), ('MC-146 additivity', W)
            tally['blobs'] += 1


tally = {'allk1': 0, 'delta0': 0, 'chains': 0, 'blobs': 0}
if '--necklaces' in sys.argv:
    for u in ['QsQsQ', 'QQQQs', 'QQQQQ', 'QsQsQs', 'QQQQQQ', 'QQQQQQQ', 'TsTsTs', 'TTTTTT']:
        E, V = cs.necklace(u)
        if cs.in_class_S(E, V):
            check(E, V, tally)
else:
    for line in sys.stdin:
        if line.strip():
            E, V = cs.g6decode(line)
            if cs.in_class_S(E, V):
                check(E, V, tally)
print('class-S members with every chain k = 1:', tally['allk1'], '; chains with delta >= 1 checked:',
      tally['chains'], '(each has a degree-2 vertex inside a blob of G - y); delta = 0 chains:',
      tally['delta0'], '; blobs checked for (MC-146):', tally['blobs'])
