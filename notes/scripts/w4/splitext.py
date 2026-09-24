#!/usr/bin/env python3
"""
splitext.py -- the split-off step on the main component X0 (workbook §(K-main),
*the split-off step on X0*, claims (MC-28)-(MC-32), Step MC11).

Setting.  `G` simple and 2-edge-connected, `x` a vertex of degree 2 whose
neighbours `a`, `b` are NOT adjacent.  `G'' := G.splitOff x a b = G - x + ab`
(`kbare_common.split_off`) and `G' := G - x` (the graph of (MC-18) at `k = 1`),
so `G'' = G' + ab`.  The special point over a point `(q', z'')` of `B(G'')` puts
`p_x := p_a + s (p_b - p_a)` on the hinge line `p_a p_b`; there the hinges `xa`,
`xb` and the deleted `ab` are one line.

Per instance (a pair `(G, x)`) the driver does four things.
  (1) The IH point.  Up to 10 draws `(q', z'')` of `B(G'')` (`maincomp`
      sampler, scale 30).  It is CERTIFIED when `dim L_{G''}(q') = 3 +
      def2(G'')` (so `q'` lies in `U(G'')`, by (MC-4)(b)) and the mod-p rank
      equals `target(G'') = 6(|V''|-1) - def3(G'')` (a certificate: mod-p rank
      <= Q-rank <= target).  Uncertified instances are counted and skipped.
  (2) (MC-28).  The special point is asserted to be a pencil configuration of
      `G` (`verify_pencil_witness`), and `rank_p(special) == rank_p(IH) + 5` is
      ASSERTED.  The identity is field-free, so it holds in GF(p) exactly.
  (3) (MC-30), X0-membership, by the proved criterion, in exact Q.  With
      `F(G', q')` the flex space of `G'` (2 rows per edge), `U := {P_a - P_b}`,
      `l_ab := p^_a x p^_b` and `phi0(P) := (P_a - P_b) . p^_x0`: the special
      point lies on X0(G) for every `z''` in `L_{G''}(q')` when (1) is
      certified, one admissible `q_x1` has `dim L_G(q', q_x1) = 3 + def2(G)`,
      and `U = 0` or `phi0 != 0`.  Also ASSERTED at certified instances:
      `U != K l_ab` ((MC-30)(i)); `c := dim(U + K l_ab) - 1` equals 2 when
      `def2` rises, and `[U != 0]` when it does not and `q_x1` certifies
      ((MC-30)(iii)).
  (4) (MC-32), the first-order gain along an EXACT curve of B(G) through the
      special point: `q'` fixed, `q_x(t) = q_x0 + t eta`, `P(t)` in `F(G', q')`
      with `(P_a - P_b) . p^_x(t) = 0`, `z(t) = Phi(P(t))`.  Its 1-jet is
      `P1 = -psi(P0)/phi0(W0) W0 + (a random element of ker phi0)`, with
      `psi(P) = (P_a - P_b) . (eta, 0)`.  The gain is the mod-p rank of `S0^T
      A1 K0` (augmented matrix, `maincomp.aug_matrix`; `A1` by an exact
      central difference).  It is a lower bound for the Q-rank at the curve's
      generic point, since `rank_p(A0) = rank_Q(A0)` there (asserted through
      (MC-3)'s `rank A0 = |E| + rank R`).  Up to `--jets` draws of `(eta,
      kernel coefficients)` per instance; the best is reported.  Gain >= needed
      is a certificate that X0(G) attains; gain < needed is "not found under
      the cap".
Also asserted per instance ((MC-29)): `ddef3 := def3(G) - def3(G'')` and
`ddef2 := def2(G) - def2(G'')` lie in {0, 1}; `ddef3 == [delta >= 5]` with
`delta = def3(G') - def3(G'/ab)` ((MC-17)'s delta); `ddef2 == [delta_2 >= 2]`
with `delta_2 = def2(G') - def2(G'/ab)`; the needed gain `target(G) -
rank(special) == 1 - ddef3`.  Each population ends with a histogram of
`(dim U, c, delta)` over the certified instances and the list of graphs (with
`n`, `m`) carrying an instance with `delta >= 5`.

Modes (run from the repository root; seeded, seed 20260924; writes nothing):

    python3 notes/scripts/w4/splitext.py --exh 7 [--jets 3] [--list]
    python3 notes/scripts/w4/splitext.py --exh 8
    python3 notes/scripts/w4/splitext.py --thetas 10
    python3 notes/scripts/w4/splitext.py --thetas 13 --smin 11 [--perg 3]
    python3 notes/scripts/w4/splitext.py --control --exh 6

`--exh N`: every simple 2EC graph on 4..N vertices (`maincomp.two_ec_graphs`)
and every eligible `x`.  `--thetas SMAX`: `theta(p1, p2, p3)` with `smin <= p1 +
p2 + p3 <= SMAX` (`maincomp.thetas`), the first `--perg` (default 3) eligible
`x` in sorted order per graph -- a CAP, disclosed in the output.  `--control`:
also the along-the-line curve (`eta = q_b - q_a`, `P(t) = P0`), every point
of which is a special point, so its gain is ASSERTED to be 0 (a negative
control for (4)).  `--list` prints every instance.

Sampler support (HARNESS.md *Evidence*).  `q'` uniform on `[-30, 30]^{2|V''|}`
integers, rejected until admissible for `G''`; `z''` a uniform `[-30, 30]`
combination of the integer RREF basis of `L_{G''}(q')`; `s = i/j` with `i`
uniform in `[2, 40]` and `j` in `[41, 90]`; `q_x1` uniform on `[-30, 30]^2`
until `(q', q_x1)` is admissible for `G`; `eta` uniform on `[-30, 30]^2`
(a draw parallel to the line is skipped); kernel coefficients uniform in
`[-30, 30]`.  Fenced constants: scale 30, 10 IH draws, 200 `q_x1` tries.
Arithmetic: exact Q for (3) and for the curve data; ranks mod 2^61-1 for (1),
(2) and (4), each used only as a certificate or a lower bound as stated.  The
last line of each population (`-- ...: N s`) is wall-clock, exempt from
byte-identity.
"""
import argparse
import os
import random
import sys
import time
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact, nullspace, neighbors  # noqa: E402
from kbare_common import (build_rigidity, rank_modp, verts_of,  # noqa: E402
                          verify_pencil_witness, split_off)
from maincomp import (sample_q, lifting_space, _interp, aug_matrix, def_k,  # noqa: E402
                      def3_pebble, rref_p, nullspace_p, _modp, P,
                      two_ec_graphs, thetas)

SEED = 20260924
SCALE = 30


def contract(edges, a, b):
    """G/ab as a multigraph on V - b (b merged into a; loops dropped)."""
    out = []
    for (u, w) in edges:
        u2, w2 = (a if u == b else u), (a if w == b else w)
        if u2 != w2:
            out.append((u2, w2))
    return out


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def hat3(qv):
    return (qv[0], qv[1], F(1))


def flex_space(edges, V, q):
    """Exact basis of F(G, q) = {P : V -> K^3, P_u - P_w in K l_uw}: rows
    (P_u - P_w) . p^_u = 0 and (P_u - P_w) . p^_w = 0 per edge (Step MC4's
    2-condition block).  Defined at every edge-injective q, any min degree."""
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for (u, w) in edges:
        for qv in (q[u], q[w]):
            r = [F(0)] * (3 * len(V))
            for k, c in enumerate(hat3(qv)):
                r[3 * idx[u] + k] += c
                r[3 * idx[w] + k] -= c
            rows.append(r)
    return nullspace(rows)


def admissible(edges, V, q):
    nb = neighbors(edges)
    if any(q[u] == q[w] for (u, w) in edges):
        return False
    for v in V:
        N = [v] + list(nb.get(v, ()))
        if len(N) >= 3 and rank_exact([[F(1), q[w][0], q[w][1]] for w in N]) < 3:
            return False
    return True


def gain_modp(edges, V, X0, X1):
    """(mod-p rank of S0^T A1 K0, mod-p rank of A0) for the augmented matrix
    along the 1-jet X0 + t X1 (affine-chart points).  A is quadratic in the
    points, so the central difference is exactly dA/dt at 0."""
    A0 = aug_matrix(edges, V, X0)
    Ap = aug_matrix(edges, V, {v: tuple(a + b for a, b in zip(X0[v], X1[v])) for v in V})
    Am = aug_matrix(edges, V, {v: tuple(a - b for a, b in zip(X0[v], X1[v])) for v in V})
    A1 = [[_modp((a - b) / 2) for a, b in zip(r, s)] for r, s in zip(Ap, Am)]
    cols = len(A0[0])
    rk0 = len(rref_p(A0)[1])
    K0 = nullspace_p(A0, cols)
    S0 = nullspace_p([list(c) for c in zip(*A0)], len(A0))
    A1K = [[sum(r[j] * k[j] for j in range(cols) if r[j]) % P for k in K0] for r in A1]
    B = [[sum(s[i] * A1K[i][c] for i in range(len(A1)) if s[i]) % P
          for c in range(len(K0))] for s in S0]
    return (len(rref_p(B)[1]) if B and B[0] else 0), rk0


def ih_point(Epp, Vpp, rng, d2pp, tpp):
    for _ in range(10):
        qp = sample_q(rng, Vpp, Epp, SCALE)
        Lp = lifting_space(Epp, Vpp, qp)
        c = [rng.randint(-SCALE, SCALE) for _ in Lp]
        zp = {w: sum(ci * bb[j] for ci, bb in zip(c, Lp)) for j, w in enumerate(Vpp)}
        ptp = {w: (qp[w][0], qp[w][1], zp[w]) for w in Vpp}
        rk = rank_modp(build_rigidity(Epp, ptp)[0])
        if rk == tpp and len(Lp) == 3 + d2pp:
            return qp, zp, ptp, rk
    return None


def run_one(E, name, x, a, b, jets, control):
    V = verts_of(E)
    n = len(V)
    Epp = split_off(E, x, a, b)
    Ep = [e for e in E if x not in e]
    Vpp = verts_of(Epp)
    assert Vpp == [v for v in V if v != x]
    d3G, d3pp, d3p = def3_pebble(E), def3_pebble(Epp), def3_pebble(Ep)
    d2G, d2pp, d2p = def_k(E, 3), def_k(Epp, 3), def_k(Ep, 3)
    cab = contract(Ep, a, b)
    vab = [v for v in Vpp if v != b]
    dlt = d3p - def_k(cab, 6, vab)
    dlt2 = d2p - def_k(cab, 3, vab)
    dd3, dd2 = d3G - d3pp, d2G - d2pp
    assert dd3 in (0, 1) and dd2 in (0, 1), ('(MC-29) ddef3/ddef2 out of range', name, x)
    assert dd3 == int(dlt >= 5), ('(MC-29) ddef3 != [delta >= 5]', name, x, dlt)
    assert dd2 == int(dlt2 >= 2), ('(MC-29) ddef2 != [delta_2 >= 2]', name, x, dlt2)
    tG, tpp = 6 * (n - 1) - d3G, 6 * (n - 2) - d3pp
    rng = random.Random(f'{SEED}:{name}:{x}')
    ih = ih_point(Epp, Vpp, rng, d2pp, tpp)
    out = {'name': name, 'x': x, 'n': n, 'm': len(E), 'dd3': dd3, 'dd2': dd2, 'delta': dlt,
           'delta2': dlt2}
    if ih is None:
        out['ih'] = False
        return out
    out['ih'] = True
    qp, zp, ptp, rkp = ih
    # (2) the special point and (MC-28)
    s = F(rng.randint(2, 40), rng.randint(41, 90))
    pt = dict(ptp)
    pt[x] = tuple(pa + s * (pb - pa) for pa, pb in zip(ptp[a], ptp[b]))
    ok, info = verify_pencil_witness(E, pt)
    assert ok, ('special point is not a pencil configuration', name, x, info)
    rk_sp = rank_modp(build_rigidity(E, pt)[0])
    assert rk_sp == rkp + 5, ('(MC-28) rank(special) != rank(G\'\') + 5', name, x, rk_sp, rkp)
    need = tG - rk_sp
    assert need == 1 - dd3, ('(MC-29) needed gain != 1 - ddef3', name, x)
    out['need'] = need
    # (3) (MC-30): membership, exact Q
    Fb = flex_space(Ep, Vpp, qp)
    ia, ib = 3 * Vpp.index(a), 3 * Vpp.index(b)

    def diff(P_):
        return [P_[ia + k] - P_[ib + k] for k in range(3)]
    U = [diff(v) for v in Fb]
    dU = rank_exact(U)
    ha, hb = hat3(qp[a]), hat3(qp[b])
    lab = cross(ha, hb)
    c = rank_exact(U + [list(lab)]) - 1
    assert not (dU == 1 and c == 0), ('(MC-30)(i) U = K l_ab at a certified IH point', name, x)
    if dd2 == 1:
        assert c == 2, ('(MC-30)(iii) def2 rises but c != 2', name, x, c)
    hx0 = tuple((1 - s) * u + s * w for u, w in zip(ha, hb))
    phi0_nz = any(dot(u, hx0) != 0 for u in U)
    for _ in range(200):
        q1 = dict(qp)
        q1[x] = (F(rng.randint(-SCALE, SCALE)), F(rng.randint(-SCALE, SCALE)))
        if admissible(E, V, q1):
            break
    else:
        raise RuntimeError('no admissible q_x1')
    dLG_ok = len(lifting_space(E, V, q1)) == 3 + d2G
    if dLG_ok and dd2 == 0:
        assert c == int(dU > 0), ('(MC-30)(iii) def2 flat but c != [U != 0]', name, x, c, dU)
    out.update(dU=dU, c=c, phi0=phi0_nz, dLG=dLG_ok, mem=dLG_ok and (dU == 0 or phi0_nz))
    # the flex P0 = Psi_{G''}(z'') and its consistency with the heights
    P0d = _interp(Epp, Vpp, qp, [zp[w] for w in Vpp])
    P0 = [t for w in Vpp for t in P0d[w]]
    assert all(dot(P0d[w], hat3(qp[w])) == zp[w] for w in Vpp), 'Phi(P0) != z\'\''
    assert all(t == 0 for t in cross(diff(P0), lab)), 'P0_a - P0_b is not in K l_ab'
    assert dot(P0d[a], hx0) == pt[x][2], 'z_x0 != h_a(q_x0)'
    X0 = dict(pt)
    # (4) (MC-32): the exact curve, q' fixed
    best = -1
    if out['mem']:
        for j in range(jets):
            jr = random.Random(f'{SEED}:{name}:{x}:jet{j}')
            dl = (F(jr.randint(-SCALE, SCALE)), F(jr.randint(-SCALE, SCALE)), F(0))
            if dl[0] * (qp[b][1] - qp[a][1]) == dl[1] * (qp[b][0] - qp[a][0]):
                continue                        # eta parallel to the line: not transverse
            psi0 = dot(diff(P0), dl)
            if phi0_nz:
                W0 = next(v for v in Fb if dot(diff(v), hx0) != 0)
                f0 = dot(diff(W0), hx0)
                P1 = [-psi0 / f0 * t for t in W0]
                ker = [[t - dot(diff(v), hx0) / f0 * u for t, u in zip(v, W0)] for v in Fb if v is not W0]
            else:
                P1 = [F(0)] * len(P0)
                ker = list(Fb)
            cc = [jr.randint(-SCALE, SCALE) for _ in ker]
            P1 = [p + sum(ci * kv[i] for ci, kv in zip(cc, ker)) for i, p in enumerate(P1)]
            assert dot(diff(P1), hx0) + psi0 == 0, 'the 1-jet leaves the curve'
            X1 = {w: (F(0), F(0), dot(P1[3 * i:3 * i + 3], hat3(qp[w]))) for i, w in enumerate(Vpp)}
            X1[x] = (dl[0], dl[1], dot(P1[ia:ia + 3], hx0) + dot(P0[ia:ia + 3], dl))
            g, rk0 = gain_modp(E, V, X0, X1)
            assert rk0 == len(E) + rk_sp, '(MC-3) rank A0 != |E| + rank R mod p'
            best = max(best, g)
            if best >= need:
                break
    out['gain'] = best
    if control:
        dl = (qp[b][0] - qp[a][0], qp[b][1] - qp[a][1], F(0))
        X1 = {w: (F(0), F(0), F(0)) for w in Vpp}
        X1[x] = (dl[0], dl[1], dot(P0[ia:ia + 3], dl))
        g, _ = gain_modp(E, V, X0, X1)
        assert g == 0, ('control: the along-line curve has first-order gain', name, x, g)
        out['ctrl'] = g
    return out


def instances(pop, perg):
    for name, E in pop:
        nb = neighbors(E)
        k = 0
        for x in sorted(nb, key=str):
            if len(nb[x]) != 2:
                continue
            a, b = sorted(nb[x], key=str)
            if b in nb[a]:
                continue
            if k >= perg:
                break
            k += 1
            yield name, E, x, a, b


def run(pname, pop, a, perg):
    t0 = time.time()
    rows = [run_one(E, name, x, u, w, a.jets, a.control) for name, E, x, u, w in instances(pop, perg)]
    stats = Counter()
    for r in rows:
        if not r['ih']:
            stats['IH point not certified in 10 draws'] += 1
            continue
        stats[(f"ddef3=+{r['dd3']} ddef2=+{r['dd2']} needed={r['need']} "
               f"membership certified={r['mem']} first-order gain>=needed={r['gain'] >= r['need']}")] += 1
        if a.list:
            print(f"  {r['name']:<16} x={r['x']!s:<3} delta={r['delta']} delta_2={r['delta2']} "
                  f"dU={r['dU']} c={r['c']} phi0!=0={r['phi0']} dimL_G ok={r['dLG']} "
                  f"need={r['need']} gain={r['gain']}" + (f" control={r['ctrl']}" if a.control else ''))
    for k, v in sorted(stats.items()):
        print(f'{v:5d}  {k}')
    cert = [r for r in rows if r['ih']]
    short = [r for r in cert if r['gain'] < r['need']]
    for r in short:
        print(f"  gain < needed under the cap ({a.jets} jets): {r['name']} x={r['x']} gain={r['gain']}")
    unmem = [r for r in cert if not r['mem']]
    for r in unmem[:10]:
        print(f"  membership NOT certified: {r['name']} x={r['x']} dU={r['dU']} phi0!=0={r['phi0']} "
              f"dimL_G ok={r['dLG']}")
    hist = Counter((r['dU'], r['c'], r['delta']) for r in cert)
    print('  (dim U, c, delta): ' + ', '.join(f'{k}: {v}' for k, v in sorted(hist.items())))
    far = Counter((r['name'], r['n'], r['m']) for r in cert if r['delta'] >= 5)
    if far:
        print('  delta >= 5 at (graph, n, m) x instances: '
              + ', '.join(f'{k} x{v}' for k, v in sorted(far.items())))
    cap = '' if perg >= 10 ** 6 else f' (cap: first {perg} eligible x per graph)'
    print(f'{pname}{cap}: {len(rows)} instances, IH certified at {len(cert)}; (MC-28) rank(special) = '
          f'rank(G\'\') + 5 at all {len(cert)}; membership certified at {len(cert) - len(unmem)}; '
          f'close outright (ddef3 = +1) at {sum(1 for r in cert if r["dd3"] == 1)}; '
          f'first-order gain >= needed at {len(cert) - len(short)}'
          + (f'; control gain 0 at all {len(cert)}' if a.control else ''))
    print(f'-- {pname}: {time.time() - t0:.1f} s')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--smin', type=int, default=0)
    ap.add_argument('--perg', type=int, default=3, help='cap on eligible x per theta graph')
    ap.add_argument('--jets', type=int, default=3)
    ap.add_argument('--control', action='store_true')
    ap.add_argument('--list', action='store_true')
    a = ap.parse_args()
    if not (a.exh or a.thetas):
        ap.error('name a population')
    print(f'splitext: seed={SEED} scale={SCALE} jets={a.jets} control={a.control}')
    if a.exh:
        run(f'exh{a.exh}', two_ec_graphs(a.exh, nmin=4), a, 10 ** 6)
    if a.thetas:
        pop = [(nm, E) for nm, E in thetas(a.thetas)
               if sum(int(t) for t in nm[5:].split('.')) >= a.smin]
        run(f'thetas{a.thetas}' + (f' (sum >= {a.smin})' if a.smin else ''), pop, a, a.perg)


if __name__ == '__main__':
    main()
