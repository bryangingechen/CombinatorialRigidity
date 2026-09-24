#!/usr/bin/env python3
"""starcap.py -- §(K-main) Step MC18 (Track B): at the chord point z0 (case A, delta in {3, 4}),
dim(rho(z0) cap star(p_a)), dim(rho(z0) cap star(p_b)) and dim(rho(z0) cap
N0), N0 = Pen(p_a, pi_a) + Pen(p_b, pi_b).  The bad configuration of (MC-112)
at delta = 4, a' = 0 is rho(z0) = Pen(p_a, s_a) + Pen(p_b, s_b), i.e. both
star intersections 2-dimensional.  Exact Q; PYTHONHASHSEED=0; repo root."""
import os, sys, random, itertools
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
import chordprobe as cp
from exactcore import nullspace, wedge2
from kbare_common import build_rigidity, verts_of, rank_modp
from maincomp import sample_q, lifting_space, _interp, def_k, thetas, habitats
from earstep import contract

def prof(E, a, b, rng):
    V = verts_of(E); nV = len(V)
    f2 = def_k(E, 3); Ec = E + [(a, b)]
    tgt_c = 6 * (nV - 1) - def_k(Ec, 6); d2c = def_k(Ec, 3)
    for _ in range(8):
        try:
            q = sample_q(rng, V, Ec, 30); L = lifting_space(E, V, q); Lc = lifting_space(Ec, V, q)
        except (AssertionError, RuntimeError):
            continue
        if len(L) != 3 + f2 or len(Lc) != 3 + d2c: continue
        co = [rng.randint(-30, 30) for _ in Lc]
        z = [sum(c * bb[t] for c, bb in zip(co, Lc)) for t in range(nV)]
        pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
        if rank_modp(build_rigidity(Ec, pt)[0]) == tgt_c: break
    else:
        return None
    M = nullspace(build_rigidity(E, pt)[0])
    rho = cp.rel(M, V, a, b)
    ia, ib = V.index(a), V.index(b)
    pa, pb = cp.hom(q[a], z[ia]), cp.hom(q[b], z[ib])
    h0 = _interp(E, V, q, z)
    if tuple(h0[a]) == tuple(h0[b]): return 'B'
    sa = [wedge2(pa, e) for e in cp.E4]; sb = [wedge2(pb, e) for e in cp.E4]
    Pa = nullspace([cp.normal(h0[a])]); Pb = nullspace([cp.normal(h0[b])])
    N0 = [wedge2(pa, x) for x in Pa] + [wedge2(pb, x) for x in Pb]
    return (cp.dim(rho), cp.cap(rho, sa), cp.cap(rho, sb), cp.cap(rho, N0))

tally = {}
insts = cp.from_members(thetas(14)) + cp.from_members(habitats()[::24])
for (label, E, a, b) in insts:
    if not cp.satisfies_H(E): continue
    V = verts_of(E); vs = [v for v in V if v != b]
    d = def_k(E, 6) - def_k(contract(E, a, b), 6, vs)
    if d not in (3, 4): continue
    p = prof(E, a, b, random.Random(f'{cp.SEED}:star:{label}'))
    tally[(d, p)] = tally.get((d, p), 0) + 1
print('(delta, (r(z0), dim rho cap star(p_a), dim rho cap star(p_b), dim rho cap N0)): count')
for k in sorted(tally, key=str): print('  ', k, tally[k])
