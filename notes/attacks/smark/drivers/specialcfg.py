#!/usr/bin/env python3
"""
specialcfg.py -- SPECIAL configurations of the minimal uncovered single piece
(smark attack, session 4; workbook S13(v)).

The break after session 4 is the single piece with dist(u, v) >= 6 and delta <= 3;
its minimal instance is K4-e subdivided with lengths (4,2,3,4,2) (|V| = 14,
girth 8, dist 6, delta 3).  This driver pins the interior hubs p, q to special
incidences with the terminal flags (point in pi_u, plane through p_u, on L, on M,
coplanar hubs, coincident hub planes, ...) and reports whether Pi_u ever lies in
rho_bar (c(Pi_u) = 2) while the welded framework still attains -- a test of the
POINTWISE form of the target (no component genericity used).  Finding: c(Pi_u) = 0
in every family except the triple-coincident planes pi_p = pi_q = pi_u, where the
side stops attaining (rho = 4 > delta) and c(Pi_u) = 1; Pi_u is never contained.

    python3 notes/attacks/smark/drivers/specialcfg.py --seed 20260916 --draws 3
    (run from the repository root)

Exact arithmetic; seeded; reads READ-ONLY, writes nothing.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sideprof as SP                                   # noqa: E402
import census as C                                      # noqa: E402
from exactcore import rank as rank_exact                # noqa: E402
from kbare_common import verts_of, verify_pencil_witness  # noqa: E402
from bimage import rho_bar_of, pt_in, plane_meet        # noqa: E402
from bdecor import d3, weld_d3                          # noqa: E402
from bunif import profile                               # noqa: E402


def v4(rng, s=20):
    return [F(rng.randint(-s, s)) for _ in range(4)]


def plane_through(pts, rng):
    B = list(pts)
    while len(B) < 3:
        B.append(v4(rng))
    return B if rank_exact(B) == 3 else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, default=3)
    ap.add_argument('--lengths', default='4,2,3,4,2')
    a = ap.parse_args()
    skel, u, v = C.SKEL['K4-e']
    edges = C.subdiv_lengths(skel, tuple(int(x) for x in a.lengths.split(',')))
    V = sorted(verts_of(edges), key=str)
    f, g = d3(edges), weld_d3(edges, u, v)
    print(f'specialcfg: seed={a.seed}; K4-e lengths={a.lengths}: |V|={len(V)} f={f} g={g} '
          f'delta={f-g} dist={C.dist(edges,u,v)} girth={C.girth(edges)}')
    rng = random.Random(a.seed)

    def run_special(label, make_fixed):
        print(f'   {label}:')
        for _d in range(a.draws):
            got = None
            for _ in range(200):
                pu, Bu, pv, Bv = SP.draw_flags(rng)
                SP.assert_generic_flags(pu, Bu, pv, Bv)
                extra = make_fixed(pu, Bu, pv, Bv, rng)
                if extra is None:
                    continue
                fx = {u: (pu, Bu), v: (pv, Bv)}
                fx.update(extra)
                try:
                    got = SP.sample_side(edges, u, v, rng, fx)
                except AssertionError:
                    got = None
                if got is not None:
                    break
            if got is None:
                print('       SAMPLER FAILED')
                continue
            pt = got[0]
            ok, _ = verify_pencil_witness(edges, pt)
            assert ok
            S, rho, dM, rk = rho_bar_of(edges, pt, u, v)
            att = (rk == 6 * (len(V) - 1) - f)
            weld = (dM - rho == 6 + g)
            L2T, _b, _T = SP.adapted_transform(pt, u, v, Bu, Bv)
            cad = profile(SP.to_adapted(L2T, S), SP.B_ADAPTED)
            c = {U: cad[SP.bunif_key(U)] for U in SP.U_LIST}
            flag = '  ** Pi_u CONTAINED' if c[('Pu',)] >= 2 else ''
            print(f'       rho={rho} attains={att} welded={weld} c(Pi_u)={c[("Pu",)]} '
                  f'c(Pi_v)={c[("Pv",)]} c(Pi_u+Pi_v)={c[("Pu","Pv")]}{flag}')

    def fa(pu, Bu, pv, Bv, rng):
        pp = pt_in(Bu, rng, 20)
        Bp = plane_through([pp, pu], rng)
        return None if Bp is None else {'p': (pp, Bp)}

    def fb(pu, Bu, pv, Bv, rng):
        pp, pq = pt_in(Bu, rng, 20), pt_in(Bu, rng, 20)
        Bp, Bq = plane_through([pp], rng), plane_through([pq], rng)
        return None if (Bp is None or Bq is None) else {'p': (pp, Bp), 'q': (pq, Bq)}

    def fc(pu, Bu, pv, Bv, rng):
        pp = v4(rng)
        Bp = plane_through([pp, pu], rng)
        return None if Bp is None else {'p': (pp, Bp)}

    def fd(pu, Bu, pv, Bv, rng):
        Bh = [pu, pv, v4(rng)]
        if rank_exact(Bh) != 3:
            return None
        pp, pq = pt_in(Bh, rng, 20), pt_in(Bh, rng, 20)
        Bp, Bq = plane_through([pp], rng), plane_through([pq], rng)
        return None if (Bp is None or Bq is None) else {'p': (pp, Bp), 'q': (pq, Bq)}

    def fe(pu, Bu, pv, Bv, rng):
        pp = pt_in(plane_meet(Bu, Bv), rng, 20)
        Bp = plane_through([pp], rng)
        return None if Bp is None else {'p': (pp, Bp)}

    def ff(pu, Bu, pv, Bv, rng):
        Bh = [v4(rng) for _ in range(3)]
        if rank_exact(Bh) != 3:
            return None
        return {'p': (pt_in(Bh, rng, 20), Bh), 'q': (pt_in(Bh, rng, 20), Bh)}

    def fg(pu, Bu, pv, Bv, rng):
        pp = pt_in([pu, pv], rng, 20)
        Bp = plane_through([pp], rng)
        return None if Bp is None else {'p': (pp, Bp)}

    def fh(pu, Bu, pv, Bv, rng):
        return {'p': (pt_in(Bu, rng, 20), Bu)}

    def fi(pu, Bu, pv, Bv, rng):
        return {'p': (pt_in(Bu, rng, 20), Bu), 'q': (pt_in(Bu, rng, 20), Bu)}

    run_special('(a) p_p in pi_u and p_u in pi_p (mutual incidence, hub at distance 4)', fa)
    run_special('(b) p_p, p_q both in pi_u', fb)
    run_special('(c) p_u in pi_p', fc)
    run_special('(d) the four hub points coplanar', fd)
    run_special('(e) p_p on L = pi_u cap pi_v', fe)
    run_special('(f) pi_p = pi_q', ff)
    run_special('(g) p_p on M = p_u p_v', fg)
    run_special('(h) pi_p = pi_u', fh)
    run_special('(i) pi_p = pi_q = pi_u', fi)


if __name__ == '__main__':
    main()
