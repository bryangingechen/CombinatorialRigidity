#!/usr/bin/env python3
"""findcyc.py -- Step MC21 (Track J): print the class-S members (graph6 on stdin) that have a C'-II-cyclic chain
(earcover.py's cells), with the chain, its classes and the class quotient.  Deterministic."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
import coverstruct as cs
import earcover as ec
for line in sys.stdin:
    if not line.strip():
        continue
    E, V = cs.g6decode(line)
    if not cs.in_class_S(E, V):
        continue
    for (a, b, I) in cs.chains(E):
        c = cs.chain_data(E, V, a, b, I)
        if c['usable'] or c['k'] != 1:
            continue
        kind, W = ec.cprime_case(E, V, I[0], a, b)
        if kind != 'II-cyclic':
            continue
        y = I[0]
        Ep = [e for e in E if y not in e]
        Vp = [v for v in V if v != y]
        cls, of, QE = ec.classes_of(Ep, Vp)
        cells, ok = ec.classify_graph(E, V, True)
        print(line.strip(), 'y', y, 'a', a, 'b', b, 'delta', c['delta'], 'classes',
              [sorted(C) for C in cls], 'A', of[a], 'B', of[b], 'QE', QE, 'cells', cells)
