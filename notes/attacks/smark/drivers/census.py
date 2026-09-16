#!/usr/bin/env python3
"""
census.py -- the single-piece census (smark attack, session 4; workbook S13(iv)).

By S13(ii) rho_bar of a side is the INTERSECTION of the rho_bar's of its pieces at
{u, v} (components of H - {u, v}), so the m = 2 profile bounds of S10 reduce to
single pieces.  This driver builds girth->=7 single pieces from small 3-connected
(or K4-minus-edge) skeletons by subdividing every skeleton edge (lengths drawn
seeded from --lens), keeps those with girth >= 7, dist(u, v) >= 4 and
delta in {2, 3, 4}, samples each at generic flags, and prints the block profile:
c(Pi_u), c(Pi_v), c(Pi_u + Pi_v), the four 3-dim blocks, c(<M>), c(<L>); a row is
FLAGGED if it exceeds S10's m = 2 bound.  Hubs are pairwise non-adjacent (all
lengths >= 2), so by S13(iii) each fibre is irreducible and each row is a
theorem for its side (S7(vi)).

    python3 notes/attacks/smark/drivers/census.py --seed 20260916 --draws 2 --per 3 --maxV 32 [--skel all|name,name]
    (run from the repository root)

Exact arithmetic; seeded; reads READ-ONLY, writes nothing.
"""
import argparse
import itertools
import os
import random
import sys
import time
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sideprof as SP                                   # noqa: E402
from exactcore import neighbors                         # noqa: E402
from kbare_common import verts_of, verify_pencil_witness  # noqa: E402
from bimage import rho_bar_of                           # noqa: E402
from bdecor import d3, weld_d3, girth                   # noqa: E402
from bunif import profile                               # noqa: E402


def subdiv_lengths(skel, lengths):
    out = []
    for (a, b), k in zip(skel, lengths):
        chain = [a] + [f's_{a}_{b}_{i}' for i in range(1, k)] + [b]
        out += list(zip(chain[:-1], chain[1:]))
    return out


def dist(edges, u, v):
    nb = neighbors(edges)
    D = {u: 0}
    q = deque([u])
    while q:
        x = q.popleft()
        for y in nb[x]:
            if y not in D:
                D[y] = D[x] + 1
                q.append(y)
    return D.get(v)


def pieces(edges, u, v):
    """number of components of H - {u, v}."""
    nb = neighbors(edges)
    rest = set(verts_of(edges)) - {u, v}
    comps, seen = 0, set()
    for s in sorted(rest, key=str):
        if s in seen:
            continue
        comps += 1
        stack = [s]
        seen.add(s)
        while stack:
            x = stack.pop()
            for y in nb[x]:
                if y in rest and y not in seen:
                    seen.add(y)
                    stack.append(y)
    return comps


# skeletons: (edge list, u, v); u, v non-adjacent in the skeleton
SKEL = {
    'K4-e': ([('u', 'p'), ('u', 'q'), ('v', 'p'), ('v', 'q'), ('p', 'q')], 'u', 'v'),
    'K33': ([(x, y) for x in ('u', 'v', 's') for y in ('a', 'b', 'c')], 'u', 'v'),
    'K33-e': ([(x, y) for x in ('u', 'v', 's') for y in ('a', 'b', 'c') if (x, y) != ('s', 'a')], 'u', 'v'),
    'prism-same-tri': ([('u', 'a'), ('v', 'a'), ('b', 'c'), ('c', 'd'), ('d', 'b'), ('u', 'b'), ('v', 'c'), ('a', 'd')], 'u', 'v'),
    'prism-diff-tri': ([('u', 'a'), ('a', 'b'), ('b', 'u'), ('c', 'v'), ('v', 'd'), ('d', 'c'), ('u', 'c'), ('a', 'v'), ('b', 'd')], 'u', 'v'),
    'cube-d2': ([('u', 'a'), ('u', 'b'), ('u', 'c'), ('a', 'v'), ('b', 'v'), ('a', 'd'), ('c', 'd'), ('b', 'e'), ('c', 'e'), ('v', 'f'), ('d', 'f'), ('e', 'f')], 'u', 'v'),
    'cube-d3': ([('u', 'a'), ('u', 'b'), ('u', 'c'), ('a', 'd'), ('b', 'd'), ('a', 'e'), ('c', 'e'), ('b', 'f'), ('c', 'f'), ('d', 'v'), ('e', 'v'), ('f', 'v')], 'u', 'v'),
    'V8': ([('u', 'a'), ('a', 'b'), ('b', 'c'), ('c', 'v'), ('v', 'd'), ('d', 'e'), ('e', 'f'), ('f', 'u'), ('a', 'd'), ('b', 'e'), ('c', 'f')], 'u', 'v'),
    'K5-e': ([('u', 'a'), ('u', 'b'), ('u', 'c'), ('v', 'a'), ('v', 'b'), ('v', 'c'), ('a', 'b'), ('b', 'c'), ('a', 'c')], 'u', 'v'),
    'W5': ([('h', 'u'), ('h', 'a'), ('h', 'v'), ('h', 'b'), ('h', 'c'), ('u', 'a'), ('a', 'v'), ('v', 'b'), ('b', 'c'), ('c', 'u')], 'u', 'v'),
    'Pet': ([('u', 'a'), ('a', 'v'), ('v', 'b'), ('b', 'c'), ('c', 'u'), ('u', 'A'), ('a', 'B'), ('v', 'C'), ('b', 'D'), ('c', 'E'), ('A', 'C'), ('C', 'E'), ('E', 'B'), ('B', 'D'), ('D', 'A')], 'u', 'v'),
    # side-degree 1 at u (a bridge u-x into a K4 / K4-e chunk): the S6 line L_{ux} is structural
    'K4-tail': ([('u', 'x'), ('x', 'v'), ('x', 'p'), ('x', 'q'), ('v', 'p'), ('v', 'q'), ('p', 'q')], 'u', 'v'),
    'K4-e-tail': ([('u', 'x'), ('x', 'p'), ('x', 'q'), ('v', 'p'), ('v', 'q'), ('p', 'q')], 'u', 'v'),
}
ORDER = ['K4-e', 'K4-tail', 'K4-e-tail', 'K33', 'K33-e', 'prism-same-tri', 'prism-diff-tri',
         'cube-d2', 'cube-d3', 'V8', 'K5-e', 'W5', 'Pet']


def analyse(edges, u, v):
    V = sorted(verts_of(edges), key=str)
    f, g = d3(edges), weld_d3(edges, u, v)
    return len(V), girth(edges), dist(edges, u, v), f, g, f - g, pieces(edges, u, v)


def profile_side(edges, u, v, rng, tries=60):
    got = None
    for _ in range(tries):
        pu, Bu, pv, Bv = SP.draw_flags(rng)
        SP.assert_generic_flags(pu, Bu, pv, Bv)
        got = SP.sample_side(edges, u, v, rng, {u: (pu, Bu), v: (pv, Bv)})
        if got is not None:
            break
    if got is None:
        return None
    pt = got[0]
    ok, _ = verify_pencil_witness(edges, pt)
    assert ok
    f, g = d3(edges), weld_d3(edges, u, v)
    V = sorted(verts_of(edges), key=str)
    S, rho, dM, rk = rho_bar_of(edges, pt, u, v)
    attains = (rk == 6 * (len(V) - 1) - f)
    welds = (dM - rho == 6 + g)
    L2T, _basis, _T = SP.adapted_transform(pt, u, v, Bu, Bv)
    Sad = SP.to_adapted(L2T, S)
    cad = profile(Sad, SP.B_ADAPTED)
    c = {U: cad[SP.bunif_key(U)] for U in SP.U_LIST}
    return dict(rho=rho, attains=attains, welds=welds,
                cPu=c[('Pu',)], cPv=c[('Pv',)], cPuPv=c[('Pu', 'Pv')],
                cMPu=c[('L', 'Pu')], cMPv=c[('L', 'Pv')], cPuL=c[('Pu', 'ell')], cPvL=c[('Pv', 'ell')],
                cM=c[('L',)], cL=c[('ell',)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, default=2)
    ap.add_argument('--maxV', type=int, default=32)
    ap.add_argument('--lens', default='2,3,4')
    ap.add_argument('--skel', default='all')
    ap.add_argument('--nvec', type=int, default=200, help='length vectors per skeleton (enumerated if fewer)')
    ap.add_argument('--per', type=int, default=3, help='sides kept per (skeleton, delta)')
    a = ap.parse_args()
    lens = [int(x) for x in a.lens.split(',')]
    names = ORDER if a.skel == 'all' else a.skel.split(',')
    rng = random.Random(a.seed)
    t0 = time.time()
    flagged, rows = [], 0
    print(f'census: seed={a.seed}, draws={a.draws}, lens={lens}, nvec={a.nvec}, per={a.per}, maxV={a.maxV}')
    for nm in names:
        skel, u, v = SKEL[nm]
        m = len(skel)
        if len(lens) ** m <= a.nvec:
            vecs = list(itertools.product(lens, repeat=m))
        else:
            vecs = [tuple(rng.choice(lens) for _ in range(m)) for _ in range(a.nvec)]
        kept = {}
        for L in vecs:
            edges = subdiv_lengths(skel, L)
            nV, gi, ds, f, g, de, pc = analyse(edges, u, v)
            if nV > a.maxV or gi < 7 or ds < 4 or de not in (2, 3, 4):
                continue
            kept.setdefault(de, [])
            if len(kept[de]) < a.per:
                kept[de].append((L, nV, gi, ds, f, g, pc))
        print(f'== {nm}: kept {{delta: n}} = { {d: len(x) for d, x in sorted(kept.items())} } '
              f'from {len(vecs)} length vectors')
        for de in sorted(kept):
            for (L, nV, gi, ds, f, g, pc) in kept[de]:
                edges = subdiv_lengths(skel, L)
                nb = neighbors(edges)
                for _d in range(a.draws):
                    r = profile_side(edges, u, v, rng)
                    if r is None:
                        print(f'   {nm} L={L}: SAMPLER FAILED')
                        continue
                    rows += 1
                    bad = []
                    if r['cPu'] >= 2:
                        bad.append('cPu>=2')
                    if r['cPv'] >= 2:
                        bad.append('cPv>=2')
                    if de <= 3 and r['cPuPv'] >= 3:
                        bad.append('cPuPv>=3')
                    if de == 4 and r['cPuPv'] >= 4:
                        bad.append('cPuPv>=4')
                    if de == 3 and max(r['cMPu'], r['cMPv'], r['cPuL'], r['cPvL']) >= 3:
                        bad.append('3dim>=3')
                    if bad:
                        flagged.append((nm, L, r))
                    tag = ('  ** ' + ','.join(bad)) if bad else ''
                    print(f'   {nm} L={L} |V|={nV} girth={gi} dist={ds} f={f} g={g} delta={de} pieces={pc} '
                          f'sdeg=({len(nb[u])},{len(nb[v])}) rho={r["rho"]} att={r["attains"]} weld={r["welds"]} '
                          f'cPu={r["cPu"]} cPv={r["cPv"]} cPuPv={r["cPuPv"]} '
                          f'3dim=({r["cMPu"]},{r["cMPv"]},{r["cPuL"]},{r["cPvL"]}) cM={r["cM"]} cL={r["cL"]}{tag}')
        sys.stdout.flush()
    print(f'ROWS: {rows}  FLAGGED: {len(flagged)}  [{time.time() - t0:.0f}s]')
    for x in flagged:
        print('  ', x)


if __name__ == '__main__':
    main()
