#!/usr/bin/env python3
"""lamab.py -- §(K-main) Step MC18 (Track B): at the chord point z0 of (G', a, b) with delta = 4 and
a'(z0) = 0 (case A), the 1-dim space L_ab = n^perp cap rho(z0)^perp of
ab-components of the self-stresses of G'+ab, and its position relative to the
flag geometry at z0.  Exact Q (mod-p only as the G'+ab attainment
certificate).  Run from the repository root.  Seeded (PYTHONHASHSEED=0)."""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scriptpath  # noqa
from fractions import Fraction as F
from exactcore import nullspace, wedge2, dot
from kbare_common import build_rigidity, verts_of, rank_modp
from maincomp import sample_q, lifting_space, _interp, def_k
from earstep import contract
from repin import hodge_star
import chordprobe as cp

def K(x, y): return dot(x, hodge_star(y))

def geom(label, E, a, b, rng):
    V = verts_of(E); nV = len(V)
    f = def_k(E, 6); f2 = def_k(E, 3)
    vs = [v for v in V if v != b]
    delta = f - def_k(contract(E, a, b), 6, vs)
    Ec = E + [(a, b)]
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
    n = wedge2(pa, pb)
    h0 = _interp(E, V, q, z)
    if tuple(h0[a]) == tuple(h0[b]): return ('caseB',)
    Rp = cp.kperp(rho)                      # implied screws rho^perp
    Lab = [v for v in nullspace([hodge_star(x) for x in rho] + [hodge_star(n)])]
    na, nb_ = cp.normal(h0[a]), cp.normal(h0[b])
    Pa = nullspace([na]); Pb = nullspace([nb_])
    L2a = cp.lambda2_plane(na); L2b = cp.lambda2_plane(nb_)
    star = lambda p: [wedge2(p, e) for e in cp.E4]
    PenA = [x for x in L2a if cp.dim(star(pa) + [x]) == 3]  # crude; use cap instead
    def inside(v, S): return cp.dim(S + [v]) == cp.dim(S)
    penA = [wedge2(pa, x) for x in Pa]; penB = [wedge2(pb, x) for x in Pb]
    penAb = [wedge2(pa, x) for x in Pb]; penBa = [wedge2(pb, x) for x in Pa]
    out = dict(label=label, delta=delta, ap=len(M) - 6 - f, dimRp=len(Rp), dimLab=len(Lab))
    if len(Lab) == 1:
        lam = Lab[0]
        out.update(lam_line=(K(lam, lam) == 0), lam_is_n=inside(lam, [n]),
                   in_N0=inside(lam, penA + penB), in_Q=inside(lam, penAb + penBa),
                   in_L2a=inside(lam, L2a), in_L2b=inside(lam, L2b),
                   in_star_a=inside(lam, star(pa)), in_star_b=inside(lam, star(pb)))
    return out

if __name__ == '__main__':
    from maincomp import habitats, thetas
    SEED = 20260924
    pop = habitats()[::int(sys.argv[1]) if len(sys.argv) > 1 else 8]
    insts = cp.from_members(pop) + cp.from_members(thetas(14))
    tally = {}
    for (label, E, a, b) in insts:
        if not cp.satisfies_H(E): continue
        V = verts_of(E); vs = [v for v in V if v != b]
        if def_k(E, 6) - def_k(contract(E, a, b), 6, vs) != 4: continue
        g = geom(label, E, a, b, random.Random(f'{SEED}:lamab:{label}'))
        if g is None or g == ('caseB',): 
            tally[str(g)] = tally.get(str(g), 0) + 1; continue
        key = tuple((k, g[k]) for k in sorted(g) if k != 'label')
        tally[key] = tally.get(key, 0) + 1
    for k, v in tally.items(): print(v, k)
