#!/usr/bin/env python3
"""
exactgain.py -- the exact-gain identity (MC-11) of workbook §(K-main).

Claim checked.  For a simple connected graph `G` of minimum degree >= 2, at
EVERY admissible planar picture `q` (adjacent `q_u != q_w`, every `q(N[v])`
non-collinear) and EVERY `z` in the lifting space `L(q)`:

    rank R(q, z)  ==  rank R(q, 0)  +  rank beta(Psi z, .)            (MC-11)

where `R` is the 5-rows-per-hinge rigidity matrix (`kbare_common.
build_rigidity`) and `beta(Psi z, .)` is (MC-6)'s form on `F(q) = Psi L(q)`
(`maincomp.beta_form`).  No genericity: the identity is asserted at jump
points `q` (`dim L(q) > 3 + def2`) and at special `z` as well.

Every rank here is EXACT over Q (`exactcore.rank`), so each instance is a
check of the identity at that point, not a bound.

Sampler support (HARNESS.md *Evidence*).  Per instance and per scale `S` in
`--scales` (default 2, 3, 30): `q` uniform on `[-S, S]^{2|V|}` integers,
rejected until admissible (`maincomp.sample_q`); scales 2 and 3 are there to
land on special positions (collinear triples outside closed neighbourhoods,
jump points of `L`).  For each `q`, the `z` tested are: every basis vector of
`L(q)` (the integer-scaled RREF basis), the sum of the first and last basis
vectors, and one uniform `[-S, S]` combination of the basis.  It varies `q`
and `z` over the admissible part of the X0 chart and its jump strata; it does
NOT touch non-admissible charts (vertical planes).

Populations: `--battery` (maincomp's nine), `--exh N` (every simple 2EC graph
on 3..N vertices, maincomp's enumeration), `--thetas SMAX`.

    python3 notes/scripts/w4/exactgain.py --battery
    python3 notes/scripts/w4/exactgain.py --exh 6
    python3 notes/scripts/w4/exactgain.py --thetas 10
    python3 notes/scripts/w4/exactgain.py --exh 6 --jump 200
    python3 notes/scripts/w4/exactgain.py --battery --exh 5 --thetas 8 --molecular --scales 1,2,30

`--molecular` checks (MC-11)(i) instead, at ARBITRARY heights `z in K^V` (a
molecular framework, not a pencil one) and pictures `q` required only to be
injective on edges (scale 1 forces degenerate positions): the rank equals
`6(|V|-1) - dim(H(l) & H(a(z)))`, and at `z = 0` it equals `6(|V|-1) - dim
H(l)`.  Per graph and per scale, two draws: `q` uniform on `[-S, S]^{2|V|}`
redrawn until edge-injective, `z` uniform on `[-S, S]^V`.  (Mode first run by
the 2026-09-24 second reader as a scratch check; committed here.)

`--jump N` adds, per graph, the first of up to N scale-2 admissible pictures
at which `dim L(q) > 3 + def2` (a jump point; none exists at some graphs, e.g.
where every admissible `q` has the minimal `dim L`), and checks it the same way.

Prints one summary line per population: instances, points checked, how many
were at a jump point, how many had positive gain; exits nonzero on any
failure (an AssertionError naming the graph).  Seeded; writes nothing.
"""
import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact  # noqa: E402
from kbare_common import build_rigidity, verts_of  # noqa: E402
from maincomp import (sample_q, lifting_space, _interp, _cycle_basis,  # noqa: E402
                      beta_form, def_k, battery, two_ec_graphs, thetas)


def _cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def dim_H(edges, cyc, pin_lists):
    """dim of the intersection over the pin assignments `r` in `pin_lists` of
    H(r) = {omega in K^E : sum_{e in C} sigma_C(e) omega_e r_e = 0 for every cycle C}."""
    rows = []
    for rs in pin_lists:
        for c in cyc:
            for i in range(3):
                row = [F(0)] * len(edges)
                for ei, sg in c.items():
                    row[ei] += sg * rs[ei][i]
                rows.append(row)
    return len(edges) - (rank_exact(rows) if rows else 0)


def check_molecular(edges, rng, S):
    """(MC-11)(i) at ARBITRARY heights z in K^V and any q with q_u != q_w on
    edges: rank R(q, z) = 6(|V|-1) - dim(H(l) & H(a(z))), and at z = 0
    rank R(q, 0) = 6(|V|-1) - dim H(l).  Exact Q."""
    V = verts_of(edges)
    while True:
        q = {v: (F(rng.randint(-S, S)), F(rng.randint(-S, S))) for v in V}
        if all(q[u] != q[w] for u, w in edges):
            break
    z = {v: F(rng.randint(-S, S)) for v in V}
    cyc = _cycle_basis(edges, V)
    ph = {v: (q[v][0], q[v][1], F(1)) for v in V}
    ell = [_cross(ph[u], ph[w]) for u, w in edges]
    a = [tuple(z[w] * ph[u][i] - z[u] * ph[w][i] for i in range(3)) for u, w in edges]
    pt = {v: (q[v][0], q[v][1], z[v]) for v in V}
    rk = rank_exact(build_rigidity(edges, pt)[0])
    assert rk == 6 * (len(V) - 1) - dim_H(edges, cyc, [ell, a]), ('(MC-11)(i) fails', edges, q, z)
    flat = {v: (q[v][0], q[v][1], F(0)) for v in V}
    rk0 = rank_exact(build_rigidity(edges, flat)[0])
    assert rk0 == 6 * (len(V) - 1) - dim_H(edges, cyc, [ell]), ('(MC-11)(i) flat fails', edges, q)


def check_point(edges, V, q, L, z, cyc):
    """Assert (MC-11) at (q, z); return (rank, flat, gain)."""
    pt = {v: (q[v][0], q[v][1], z[i]) for i, v in enumerate(V)}
    flat = {v: (q[v][0], q[v][1], F(0)) for v in V}
    rk = rank_exact(build_rigidity(edges, pt)[0])
    rk0 = rank_exact(build_rigidity(edges, flat)[0])
    k = _interp(edges, V, q, z)
    M = [beta_form(edges, cyc, k, _interp(edges, V, q, b)) for b in L]
    g = rank_exact(M) if M and M[0] else 0
    assert rk == rk0 + g, ('(MC-11) fails', edges, q, z, rk, rk0, g)
    return rk, rk0, g


def jump_q(rng, V, edges, d2, tries):
    """The first admissible `q` at scale 2 with `dim L(q) > 3 + def2`, or None."""
    for _ in range(tries):
        q = sample_q(rng, V, edges, 2, tries=2000)
        if len(lifting_space(edges, V, q)) > 3 + d2:
            return q
    return None


def run(name, edges, seed, scales, jtries):
    V = verts_of(edges)
    d2 = def_k(edges, 3)
    cyc = _cycle_basis(edges, V)
    pts = jumps = pos = 0
    qs = []
    for S in scales:
        rng = random.Random(f'{seed}:{name}:{S}')
        qs.append((rng, S, sample_q(rng, V, edges, S, tries=2000)))
    if jtries:
        rng = random.Random(f'{seed}:{name}:jump')
        qj = jump_q(rng, V, edges, d2, jtries)
        if qj is not None:
            qs.append((rng, 2, qj))
    for rng, S, q in qs:
        L = lifting_space(edges, V, q)
        jump = len(L) > 3 + d2
        zs = [list(b) for b in L]
        if len(L) >= 2:
            zs.append([a + b for a, b in zip(L[0], L[-1])])
        c = [rng.randint(-S, S) for _ in L]
        zs.append([sum(ci * b[i] for ci, b in zip(c, L)) for i in range(len(V))])
        for z in zs:
            _, _, g = check_point(edges, V, q, L, z, cyc)
            pts += 1
            jumps += jump
            pos += g > 0
    return pts, jumps, pos


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--battery', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--seed', type=int, default=20260924)
    ap.add_argument('--scales', default='2,3,30')
    ap.add_argument('--molecular', action='store_true',
                    help='check (MC-11)(i) at arbitrary z and any edge-injective q instead')
    ap.add_argument('--jump', type=int, default=0,
                    help='also search up to N scale-2 pictures per graph for a jump point')
    a = ap.parse_args()
    scales = [int(s) for s in a.scales.split(',')]
    pops = []
    if a.battery:
        pops.append(('battery', battery()))
    if a.exh:
        pops.append((f'exh{a.exh}', two_ec_graphs(a.exh)))
    if a.thetas:
        pops.append((f'thetas{a.thetas}', thetas(a.thetas)))
    if not pops:
        ap.error('name a population')
    if a.molecular:
        for pname, pop in pops:
            n = 0
            for name, edges in pop:
                rng = random.Random(f'{a.seed}:{name}:mol')
                for S in scales:
                    for _ in range(2):
                        check_molecular(edges, rng, S)
                        n += 1
            print(f'{pname}: {len(pop)} graphs, {n} points, (MC-11)(i) holds at all '
                  f'(arbitrary z; q only edge-injective)')
        return
    for pname, pop in pops:
        tot = [0, 0, 0]
        for name, edges in pop:
            r = run(name, edges, a.seed, scales, a.jump)
            tot = [x + y for x, y in zip(tot, r)]
        print(f'{pname}: {len(pop)} graphs, {tot[0]} points, (MC-11) holds at all; '
              f'{tot[1]} at a jump point q, {tot[2]} with positive gain')


if __name__ == '__main__':
    main()
