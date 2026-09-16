#!/usr/bin/env python3
"""
adversarial.py -- the smark attack's adversarial control for the S10 m=2 core
(session 3).  "Where it breaks" (state.md): the profile bounds c'(Pi_w) <= 1,
c'(Pi_v) <= 1, c'(Pi_w + Pi_v) <= 2 are measured with NO excess on the 23-side
battery, but that battery has at most two interior hubs and NO 3-connected
chunk (no K4 minor).  A girth->=7 side, side-degree >= 2 at both hub terminals,
with c'(Pi_w) >= 2 or c'(Pi_w + Pi_v) >= 3 would REFUTE S10's clean m=2 form.

This driver samples the block profile (sideprof machinery) of hard girth->=7
sides that DO contain a K4 minor / three interior hubs, and reports excess at
every block -- flagging any c'(Pi_u), c'(Pi_v), c'(Pi_u+Pi_v) above the S10
bound.  Each draw is an exact witness, so a row with no excess is a theorem
for the component through the draw (S7(vi)); "no excess found" over the sample
is NOT a theorem about the class (the population is named and capped).

    python3 notes/attacks/smark/drivers/adversarial.py --seed S --draws N [--side NAME|all]
    (run from the repository root; workbook: attack-smark.md S12)

All arithmetic exact.  Reads READ-ONLY; writes nothing.
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sideprof as SP  # noqa: E402


def subdiv(edges, k):
    """subdivide every edge into k edges (k-1 new degree-2 vertices).
    New vertex tags: f'{a}_{b}_{i}' for edge (a,b), i in 1..k-1."""
    out = []
    for (a, b) in edges:
        chain = [a] + [f's_{a}_{b}_{i}' for i in range(1, k)] + [b]
        out += list(zip(chain[:-1], chain[1:]))
    return out


def prism_side(k=3):
    """triangular prism K3xK2 (3-connected, K4 minor), terminals u, v two
    vertices of one triangle, every edge subdivided into k (girth 3k)."""
    # triangles u-a-b-u and v-c-d-v (wait: prism = two triangles + a matching)
    P = [('u', 'a'), ('a', 'b'), ('b', 'u'),        # triangle 1: u,a,b
         ('v', 'c'), ('c', 'd'), ('d', 'v'),        # triangle 2: v,c,d
         ('u', 'v'), ('a', 'c'), ('b', 'd')]        # matching
    return subdiv(P, k)


def sk4_lengths(lengths):
    """topological K4 on {u,v,p,q}, edges (uv,up,uq,vp,vq,pq) subdivided into
    `lengths`; u, v the terminals (degree 3 hubs), p, q interior hubs.  A
    genuine K4 minor (not series-parallel), girth = min triangle sum."""
    names = [('u', 'v'), ('u', 'p'), ('u', 'q'), ('v', 'p'), ('v', 'q'), ('p', 'q')]
    out = []
    for (a, b), k in zip(names, lengths):
        chain = [a] + [f's_{a}_{b}_{i}' for i in range(1, k)] + [b]
        out += list(zip(chain[:-1], chain[1:]))
    return out


SIDES = {
    # flexible K4-minor sides (girth >= 7, both terminals side-degree 3):
    'sk4_d2': lambda: sk4_lengths((4, 3, 3, 3, 3, 4)),   # delta=2, |V|=18, girth 10
    'sk4_d3': lambda: sk4_lengths((3, 3, 3, 4, 4, 4)),   # delta=3, |V|=19, girth 10
    'sk4_d4': lambda: sk4_lengths((4, 3, 3, 4, 4, 4)),   # delta=4, |V|=20, girth 10
    'prism': lambda: prism_side(3),                      # subdivided triangular prism (delta varies)
}


def run(name, seed, ndraw):
    edges = SIDES[name]()
    u, v = 'u', 'v'
    from kbare_common import verts_of
    from bimage import dim, rho_bar_of
    from binduc import assert_generic_star
    from kbare_common import verify_pencil_witness
    from bunif import profile, generic_c
    import random
    import time
    V = sorted(verts_of(edges), key=str)
    nb = SP.neighbors(edges)
    gi = SP.girth(edges)
    f, g, delta, xc = SP.side_deltas(edges, u, v)
    target = 6 * (len(V) - 1) - f
    rng = random.Random(seed)
    t0 = time.time()
    print(f'== {name}: |V|={len(V)}, |E|={len(edges)}, girth={gi}, '
          f'side-deg=({len(nb[u])},{len(nb[v])}), f={f}, g={g}, delta={delta} [{xc}]')
    seen = {}
    for d in range(ndraw):
        got = None
        for _ in range(60):
            pu, Bu, pv, Bv = SP.draw_flags(rng)
            SP.assert_generic_flags(pu, Bu, pv, Bv)
            got = SP.sample_side(edges, u, v, rng, {u: (pu, Bu), v: (pv, Bv)})
            if got is not None:
                break
        if got is None:
            print(f'   draw {d}: SAMPLER FAILED')
            continue
        pt, _pl, _W, _br = got
        ok, _ = verify_pencil_witness(edges, pt)
        assert ok
        assert_generic_star(edges, pt)
        SP.assert_realizes_flags(edges, pt, u, v, pu, Bu, pv, Bv)
        S, rho, dM, rk = rho_bar_of(edges, pt, u, v)
        attains = (rk == target)
        welds = (dM - rho == 6 + g)
        L2T, basis, _T = SP.adapted_transform(pt, u, v, Bu, Bv)
        Sad = SP.to_adapted(L2T, S)
        assert dim(Sad) == rho
        cad = profile(Sad, SP.B_ADAPTED)
        c = {U: cad[SP.bunif_key(U)] for U in SP.U_LIST}
        exc = {SP.ulabel(U): c[U] - generic_c(rho, SP.udim(U))
               for U in SP.U_LIST if c[U] - generic_c(rho, SP.udim(U))}
        # the three S10 m=2 quantities (u<->w terminal)
        cPu = c[('Pu',)]
        cPv = c[('Pv',)]
        cPuPv = c[('Pu', 'Pv')]
        flag = []
        if cPu >= 2:
            flag.append(f'c(Pi_u)={cPu}>=2')
        if cPv >= 2:
            flag.append(f'c(Pi_v)={cPv}>=2')
        if cPuPv >= 3:
            flag.append(f'c(Pi_u+Pi_v)={cPuPv}>=3')
        alarm = '  ** REFUTES S10 m=2 clean form: ' + ', '.join(flag) if flag else ''
        key = (rho, cPu, cPv, cPuPv)
        seen[key] = seen.get(key, 0) + 1
        print(f'   draw {d}: rho={rho}, attains={attains}, welded={welds}; '
              f'c(Pi_u)={cPu}, c(Pi_v)={cPv}, c(Pi_u+Pi_v)={cPuPv}; '
              f'excess={exc if exc else "none"}{alarm}')
    print(f'   -- {name}: (rho, cPu, cPv, cPuPv) seen: {seen}  [{time.time()-t0:.1f}s]')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, required=True)
    ap.add_argument('--side', default='all')
    a = ap.parse_args()
    names = list(SIDES) if a.side == 'all' else [a.side]
    print(f'adversarial: seed={a.seed}, draws={a.draws}, sides={names}')
    for nm in names:
        run(nm, a.seed, a.draws)


if __name__ == '__main__':
    main()
