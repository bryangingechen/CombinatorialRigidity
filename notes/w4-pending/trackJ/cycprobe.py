#!/usr/bin/env python3
"""cycprobe.py -- Track J: ringprobe.probe (chord point, class level, rhobar, truth) at the
C'-II-cyclic chains found by findcyc.py on 13 vertices (graph6 + chain vertex y hard-coded below).
PYTHONHASHSEED=0, seed 20260924, repository root."""
import os, sys, random
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts'))
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts', 'w4'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
import coverstruct as cs
import earcover as ec
import ringprobe as rp
from exactcore import neighbors

CASES = [('L???C@_F?sW_Go', 6), ('L???C@_F?sW_Go', 5), ('L???E?oBECDODO', 6),
         ('L??CAA_EAgDG@g', 5), ('L??CAA_EAgDG@g', 2), ('L??CB@Oa@GB_?s', 4)]
for g6, y in CASES:
    E, V = cs.g6decode(g6)
    nb = neighbors(E)
    a, b = sorted(nb[y])
    Ep = [e for e in E if y not in e]
    Vp = [v for v in V if v != y]
    cls, of, QE = ec.classes_of(Ep, Vp)
    blobs = [sorted(C) for C in cls]
    rec = rp.probe(f'{g6}:y{y}', Ep, a, b, blobs, random.Random(f'{rp.SEED}:{g6}:{y}'))
    print(rec, flush=True)
