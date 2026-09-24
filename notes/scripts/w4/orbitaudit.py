#!/usr/bin/env python3
"""orbitaudit.py -- Track I audit of `earante.py --orbits`: re-run its certificate search
and print the COEFFICIENT of each certifying monomial minor (the driver prints only that one
exists).  A coefficient divisible by p means the certificate says nothing in characteristic p.
Deterministic; imports the landed driver unchanged.
    PYTHONHASHSEED=0 python3 orbitaudit.py     (< 5 s)
"""
import os, sys
REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
import scriptpath  # noqa
import earante as ea
from fractions import Fraction as F

e = ea.E4
cases = {
    'i': ({0: [0], 1: [1], 2: [2, 3], 3: [2, 3]}, e[0], [e[0][t] + e[2][t] for t in range(4)],
          [e[1][t] + e[3][t] for t in range(4)], e[1],
          {'l0 l1 != 0': (4, None, (0, 1)), 'l0 = 0, l1 l2 != 0': (4, 0, (1, 2)),
           'L1': (4, (0, 2), (1,)), 'l1 = 0, l0 l2 != 0': (3, 1, (0, 2)),
           'L0': (1, (1, 2), (0,)), 'L2': (1, (0, 1), (2,))}),
    'ii': ({0: [0], 1: [1], 2: [1, 2], 3: [1, 2, 3]}, e[0], [e[0][t] + e[2][t] for t in range(4)],
           e[3], e[1],
           {'l0 l1 l2 != 0': (5, None, (0, 1, 2)), 'l2 = 0, l0 l1 != 0': (4, 2, (0, 1)),
            'l0 = 0, l1 l2 != 0': (4, 0, (1, 2)), 'L1': (4, (0, 2), (1,)),
            'l1 = 0, l0 l2 != 0': (3, 1, (0, 2)), 'L0': (1, (1, 2), (0,)), 'L2': (1, (0, 1), (2,))}),
}
for orb, (allowed, pa, x1, x2, pb, table) in cases.items():
    gens = []
    for col, rows in allowed.items():
        for r_ in rows:
            X = [[F(0)] * 4 for _ in range(4)]
            X[r_][col] = F(1)
            gens.append(X)
    Ls = [ea.wedge2(pa, x1), ea.wedge2(x1, x2), ea.wedge2(x2, pb)]
    c = [ea.padd(ea.padd({(1, 0, 0): Ls[0][t]} if Ls[0][t] else {},
                         {(0, 1, 0): Ls[1][t]} if Ls[1][t] else {}),
                 {(0, 0, 1): Ls[2][t]} if Ls[2][t] else {}) for t in range(6)]
    Tm = [ea.lie_act(X, c) for X in gens]
    for stratum, (d, kill, need) in table.items():
        s = d + 1
        if kill is None:
            sub = Tm
        else:
            ks = (kill,) if isinstance(kill, int) else kill
            sub = [[{m: cc for m, cc in ent.items() if all(m[x] == 0 for x in ks)} for ent in row]
                   for row in Tm]
        mins = ea.minors(sub, s)
        coefs = sorted({abs(cf) for key, pol in mins.items() if len(pol) == 1
                        for (mono, cf) in pol.items()
                        if all(mono[x] == 0 for x in range(3) if x not in need)})
        # the driver takes the FIRST such minor in its iteration order:
        first = None
        for key, pol in mins.items():
            if len(pol) == 1:
                (mono, cf), = pol.items()
                if all(mono[x] == 0 for x in range(3) if x not in need):
                    first = cf
                    break
        print(f'orbit ({orb}) {stratum:<20}: driver\'s certifying coefficient {first}; '
              f'all certifying |coefficients| {coefs}')
