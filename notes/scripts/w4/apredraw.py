#!/usr/bin/env python3
"""apredraw.py -- §(K-main) Step MC18 (Track B): a'(z0) at a single chord-point draw is an UPPER
bound for its generic value (dim M_{G'} is upper semicontinuous).  Re-measures
a'(z0) at K independent certified chord points (q certified in U(G'), U(G'+ab);
z0 a random point of L_{G'+ab}(q) with G'+ab attaining, mod-p certificate) and
reports the minimum -- the generic value is <= the minimum, and equals it once
the minimum is 0.  Exact Q motion spaces.  PYTHONHASHSEED=0; repo root."""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
import chordprobe as cp
from maincomp import thetas, def_k, two_ec_graphs
from kbare_common import verts_of

def ap_draws(E, a, b, K, tag, S=30):
    out = []
    for k in range(K):
        rec = cp.chord_instance(tag, E, a, b, random.Random(f'{cp.SEED}:redraw:{tag}:{k}:{S}'),
                                nz1=0, want_truth=False)
        if rec['status'] == 'ok':
            out.append((rec['ap'], rec['r'], rec['rn']))
    return out

if __name__ == '__main__':
    K = 6
    cases = []
    th = dict(thetas(13))
    for lab in ['theta2.2.7:14-19', 'theta2.3.8:1-16', 'theta1.3.7:11-19', 'theta1.3.7:12-14',
                'theta2.3.3:0-1', 'theta2.2.3:0-1']:
        nm, pr = lab.split(':'); a, b = map(int, pr.split('-'))
        E = th[nm]
        if lab in ('theta2.3.3:0-1', 'theta2.2.3:0-1'):
            # G' = theta minus the length-2 chain between the hubs 0, 1
            nb = cp.nbrs(E)
            y = [v for v in nb if len(nb[v]) == 2 and nb[v] == {0, 1}][0]
            E = [e for e in E if y not in e]
        cases.append((lab, E, a, b))
    ex8 = dict(two_ec_graphs(8, 8))
    for lab in ['x8_174485505:5-7', 'x8_194069537:5-7', 'x8_218500544:4-6']:
        nm, pr = lab.split(':'); a, b = map(int, pr.split('-'))
        E = ex8[nm]
        nb = cp.nbrs(E)
        y = [v for v in nb if nb[v] == {a, b}][0]
        cases.append((lab, [e for e in E if y not in e], a, b))
    cases.append(('r10n11:3-4', [(0, 1), (0, 4), (1, 2), (1, 3), (2, 5), (2, 9), (3, 10), (4, 5),
                                 (6, 8), (6, 9), (7, 8), (7, 10)], 3, 4))
    for (lab, E, a, b) in cases:
        V = verts_of(E); vs = [v for v in V if v != b]
        from earstep import contract
        d = def_k(E, 6) - def_k(contract(E, a, b), 6, vs)
        d2 = def_k(E, 3) - def_k(contract(E, a, b), 3, vs)
        res = ap_draws(E, a, b, K, lab)
        print(f'{lab}: delta={d} delta2={d2}  (a\', r(z0), dim rho cap n^perp) per draw: {res}  '
              f'min a\' = {min(x[0] for x in res) if res else None}')
