#!/usr/bin/env python3
"""
pencilline.py -- WHICH line of the terminal pencil lies in rho_bar, and by which
motion (smark attack, session 4; workbook S13(i)).

On the K4-minor / prism sides of `adversarial.py` the block profile has
c'(Pi_u) = 1 at delta >= 3 (S12(iii)).  This driver computes the line
rho_bar cap Pi_u exactly, compares it with the hinge lines L_{u x} at u, and
exhibits the motion m with m(u) = 0, m(v) = that line: the active hinges and
the vertices co-moving with v.  Finding (6/6 draws over sk4_d3, sk4_d4, prism):
the line is the hinge L_{u x} toward v along the direct u-v branch, and the
motion welds that whole branch to v -- the side is an EAR composed in
parallel with a fully flexible remainder (delta = 6 once the branch is
removed), so the tight c'(Pi_u) = 1 is S8's ear profile, not a hub effect.

    python3 notes/attacks/smark/drivers/pencilline.py --seed 20260916 --draws 2 [--side sk4_d3,sk4_d4,prism]
    (run from the repository root)

Exact arithmetic (fractions.Fraction); seeded; reads READ-ONLY, writes nothing.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sideprof as SP           # noqa: E402  (bootstraps the corpus path)
import adversarial as ADV       # noqa: E402
from exactcore import hat, wedge2, nullspace  # noqa: E402
from kbare_common import verts_of              # noqa: E402
from binduc import motion_space                # noqa: E402
from bimage import span, dim                   # noqa: E402
from bdecor import d3, weld_d3                 # noqa: E402
from bunif import mat_inv                      # noqa: E402


def intersect_with_coords(S, keep):
    """basis of {x in span(S) : x_k = 0 for k not in keep}."""
    if not S:
        return []
    comp = [k for k in range(6) if k not in keep]
    A = [[S[i][k] for i in range(len(S))] for k in comp]
    ns = nullspace(A)
    out = []
    for a in ns:
        vec = [sum(a[i] * S[i][k] for i in range(len(S))) for k in range(6)]
        if any(vec):
            out.append(vec)
    return span(out) if out else []


def normalize(vec):
    for x in vec:
        if x != 0:
            return [y / x for y in vec]
    return vec


def direct_branch_edges(edges):
    return [e for e in edges if any(str(x).startswith('s_u_v_') for x in e)]


def run(name, seed, ndraw):
    edges = ADV.SIDES[name]()
    u, v = 'u', 'v'
    V = sorted(verts_of(edges), key=str)
    idx = {w: i for i, w in enumerate(V)}
    nb = SP.neighbors(edges)
    rng = random.Random(seed)
    f, g = d3(edges), weld_d3(edges, u, v)
    E2 = [e for e in edges if e not in set(direct_branch_edges(edges))]
    f2, g2 = d3(E2), weld_d3(E2, u, v)
    print(f'== {name}: side-deg=({len(nb[u])},{len(nb[v])}); (f,g,delta)=({f},{g},{f-g}); '
          f'minus direct u-v branch: ({f2},{g2},{f2-g2})')
    for d in range(ndraw):
        got = None
        for _ in range(60):
            pu, Bu, pv, Bv = SP.draw_flags(rng)
            SP.assert_generic_flags(pu, Bu, pv, Bv)
            got = SP.sample_side(edges, u, v, rng, {u: (pu, Bu), v: (pv, Bv)})
            if got is not None:
                break
        assert got is not None, 'sampler failed'
        pt = got[0]
        L2T, _basis, _T = SP.adapted_transform(pt, u, v, Bu, Bv)
        L2Tinv = mat_inv(L2T)
        ker, _r, nV = motion_space(edges, pt)
        bu, bv = 6 * idx[u], 6 * idx[v]
        img = [[m[bv + k] - m[bu + k] for k in range(6)] for m in ker]
        S = span(img)
        Sad = SP.to_adapted(L2T, S)
        rho = dim(Sad)
        for (term, other, keep, label) in [(u, v, [1, 2], 'Pi_u'), (v, u, [3, 4], 'Pi_v')]:
            I = intersect_with_coords(Sad, keep)
            print(f'  draw {d}: rho={rho}; dim(rho_bar cap {label}) = {len(I)}')
            for line in I:
                ln = normalize(line)
                hits = [f'L_{term}{x}' for x in sorted(nb[term])
                        if normalize(SP.apply6(L2T, wedge2(hat(pt[term]), hat(pt[x])))) == ln]
                lo = SP.apply6(L2Tinv, line)
                A = [[img[i][k] for i in range(len(img))] + [lo[k]] for k in range(6)]
                sol = None
                for a in nullspace(A):
                    if a[-1] != 0:
                        sol = [-x / a[-1] for x in a[:-1]]
                        break
                assert sol is not None
                m = [sum(sol[i] * ker[i][k] for i in range(len(ker))) for k in range(6 * nV)]
                mu = m[bu:bu + 6]
                m = [m[6 * i + k] - mu[k] for i in range(nV) for k in range(6)]
                assert [m[bv + k] for k in range(6)] == lo
                active = []
                for (x, y) in edges:
                    dxy = [m[6 * idx[x] + k] - m[6 * idx[y] + k] for k in range(6)]
                    if any(dxy):
                        Lxy = wedge2(hat(pt[x]), hat(pt[y]))
                        k0 = next(k for k in range(6) if Lxy[k] != 0)
                        c = dxy[k0] / Lxy[k0]
                        assert all(dxy[k] == c * Lxy[k] for k in range(6)), 'not a hinge motion'
                        active.append((x, y))
                comove = [z for z in V if [m[6 * idx[z] + k] for k in range(6)] == lo]
                inactive = sorted(set(edges) - set(active))
                print(f'     line = hinge {hits or "(none)"}; inactive hinges {inactive}; '
                      f'co-moving with {other}: {sorted(comove, key=str)}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, required=True)
    ap.add_argument('--side', default='sk4_d3,sk4_d4,prism')
    a = ap.parse_args()
    print(f'pencilline: seed={a.seed}, draws={a.draws}')
    for nm in a.side.split(','):
        run(nm, a.seed, a.draws)


if __name__ == '__main__':
    main()
