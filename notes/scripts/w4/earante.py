#!/usr/bin/env python3
"""
earante.py -- the short open ear step on X0 WITH the antecedent (W4 reopened,
P3 Track 1; workbook §(K-main) Step MC13, claims (MC-43)-(MC-51): the 2026-09-24
second-reader continuation of Step MC10's (MC-27)).

Setting and notation are Step MC10's.  `G = G' + ear_k`, an open `a - b` ear
with `k` interior vertices; at a point `p` of X0(G') the relative screw space
is `rho = {X_b - X_a : X in M_{G'}}`, `r = dim rho`, `delta = def3(G') -
def3(G'/ab)`, `U = {P_a - P_b}`; the flag pair `(p_a, pi_a; p_b, pi_b)` lies
in orbit (i)-(iv); `Lambda_j` is the span of the `j + 1` hinge lines of an
`ear_j` placement (`j = 1`: the point on `m = pi_a cap pi_b`; `j >= 2`: first
point in `pi_a`, last in `pi_b`, middle points free).  `(P_j)` for a fixed
`rho` says: a generic `ear_j` placement has `dim(rho cap Lambda_j) =
max(0, r + j - 5)`, the least possible value.  The antecedent of the ear step
at `k` is `X0(G' + ear_{k-1})` attaining; by (MC-22) it gives `(P_{k-1})`.

What the driver asserts (each is a PROVED claim of the workbook; an assert
firing is a counterexample or a bug):
  (MC-16) pointwise, at every constructed `G' + ear_j` point: `dim M_G =
          dim M_{G'} - r + dim(rho cap Lambda) + (j + 1) - lambda`, with
          `dim M_G` from the exact rank of `G`'s own rigidity matrix;
  (MC-22) at every constructed point where `G'` attains and `lambda = j + 1`:
          `G` attains there iff `r >= min(delta, 5 - j)` and `dim(rho cap
          Lambda) = max(0, r + j - 5)`;
  (MC-45)  `(P_2) => (P_3)` for every `rho`, in every orbit, at every `r`;
  (MC-46)  `(P_1) => (P_2)` for every `rho` whose flag pair is in orbit (i)
          or (ii), at every `r`;
  (MC-48)  if every subgraph `K` of `G'` has `5 e(K) <= 6(|V(K)| - 1)` and
          `a !~ b`, then `delta_2 := def2(G') - def2(G'/ab) >= 2`;
  and the trivial consistency facts: an observed flag-genericity (the two
  incidence functionals `z -> z_b - h_a(q_b)`, `z -> z_a - h_b(q_a)`
  independent on `L(q)`) forces orbit (i) and `dim U >= 2`; orbit (iv) is
  `U = 0`; orbit (iii) has `dim U <= 1`.
"Observed (P_j)" = the least value `max(0, r + j - 5)` seen at one of up to
`T = 4` random placements (a CERTIFICATE that this `rho` is outside the bad
set `B_j(r)`: `dim(rho cap Lambda)` is upper semicontinuous on the
irreducible placement space); "(P_j) fails" = not seen in `T` tries (a
measurement).  (MC-45) and (MC-46) are statements about subspaces `rho` of
`Lambda^2 K^4` in a given flag orbit, so they are asserted at EVERY draw, not
only at draws certified generic.  A draw where `G'` attains and `r = delta`
certifies `r` at X0(G')'s generic point (`r_draw <= r_generic <= delta`,
`earstep.py --rdelta`); only certified draws are counted as `cert`.

Modes (run from the repository root; exact arithmetic over Q, except the
attainment screen of `G'` below; seeded; writes nothing):

    python3 notes/scripts/w4/earante.py --orbits
    python3 notes/scripts/w4/earante.py --frames
    python3 notes/scripts/w4/earante.py --exh 6 [--draws 3]
    python3 notes/scripts/w4/earante.py --thetas 14
    python3 notes/scripts/w4/earante.py --habitats [--stride S] [--limit N]
    python3 notes/scripts/w4/earante.py --chord 6
    python3 notes/scripts/w4/earante.py --chord-thetas 14
    python3 notes/scripts/w4/earante.py --chord-habitats [--stride S] [--limit N]

`--orbits` (a PROOF input, exact symbolic): for the flag-pair stabiliser `S`
of orbit (i) (`dim S = 5`) and of orbit (ii) (`dim S = 6`), and the standard
`ear_2` placement of each, the dimension of the `S`-orbit of every point
`[l0 L0 + l1 L1 + l2 L2]` of `P(Lambda_2)`, read off minors of the
infinitesimal-action matrix computed as exact polynomials in `(l0, l1, l2)`.
Asserted: the table used by (MC-46)'s count (orbit (i): orbit dimension 4
where `l1 != 0` (three pieces: `l0 l1 != 0`, `l0 = 0 != l1 l2`, the point
`L1`), 3 on `l1 = 0`, 1 at `L0`, `L2`; orbit (ii): 5 where `l0 l1 l2
!= 0`, 4 where `l0 l2 = 0 != l1`, 3 on `l1 = 0`, 1 at `L0`, `L2`), the
transitivity of `S` on generic `ear_2` placements, and the semi-invariance of
the two quadrics `Q1 = x_M x_L`, `Q2 = det[x_u | x_v]` of orbit (i).
`--frames` (constructed witnesses, exact): in a standard frame of each orbit
and for `k = 1, 2, 3`, `r = 1, 2, 3`, the named families of (MC-43)/(MC-46)/
(MC-47) (`rho` containing a terminal pencil, `rho` inside the sum of the two
terminal pencils, `rho` meeting the plane's lines in orbit (iv)) and a random
`rho` (uniform integers in `[-9, 9]`); asserted: each family is bad where the
workbook says so and a random `rho` is good in every cell outside orbit
(iii) at `k = 1`.
`--exh N` (MEASURED): every simple 2EC `G'` on 3..N vertices
(`maincomp.two_ec_graphs`) and every NON-adjacent pair `a < b`, `k = 2, 3`.
One X0(G') draw per graph (`maincomp.probe`: `q` uniform integers in
`[-30, 30]`, `z` a uniform `[-30, 30]` combination of an exact basis of
`L(q)`), the first of up to `--draws` at which `G'` attains (rank mod
2^61 - 1 equal to the target: a certificate).
`--thetas S` / `--habitats` (MEASURED): `G` is a member (every simple
theta graph with `p1 + p2 + p3 <= S`; `maincomp.habitats()`'s 888 class
shapes, every `--stride`-th of them, then the first `--limit`), decomposed at
every maximal degree-2 chain with `k = 2` or `3` interior vertices and
non-adjacent ends `a, b` of degree >= 3; `G' = G - chain`.  One X0(G') draw
per instance.  The full `--habitats` pool (2 811 instances) is over the 600 s
foreground ceiling.
`--chord N` / `--chord-thetas S` / `--chord-habitats` (MEASURED, with the
pointwise identities of (MC-44), (MC-49), (MC-50) asserted): `k = 1`, over every
simple 2EC `G'` on 3..N vertices and non-adjacent pair, or over the members
above decomposed at their `k = 1` chains; draws a
point `z0` of X0(G' + ab) over a `q` certified in U(G') (`dim L = 3 + def2`
for both `G'` and `G' + ab` at `q`), at which `G' + ab` attains; asserts
`dim M_{G'+ab} = dim M_{G'} - r + dim(rho cap <n>)` (`n = p_a p_b`), then
`r(z0) - dim(rho cap <n>) = min(delta, 5) + a'(z0)`, and for `delta <= 5`
that `n` is not in `rho(z0)` and `r(z0) = delta + a'(z0)`; at the degenerate
`ear_1` point `y0` on `n` (a point of X0(G) when `dim U >= 2`) asserts
`dim M_G = dim M_{G'+ab} + 1`, and that this is the target of `G` whenever
`delta >= 5` (and `dim U >= 2`).  Reports `dim(rho(z0) cap n^perp)` (Klein) and
`a'(z0)`.  Where `pi_a != pi_b` at `z0` it also builds, for two random
`z1 in L(q)`, the first-order limit of the ear_1 span along `z0 + s z1` (with
`q_y(s)` on the line `(h_a - h_b)(s) = 0` through `q_y0`), asserts it is a pencil
through `y0` containing `n` ((MC-50)), records whether the two limit planes
differ, and whether `K0 = dim M_{G'}(z0) - r + dim(rho cap limit)` equals the
target of `G' + ear_1` -- which, with `dim U >= 2` and `q` certified in U(G'),
certifies that X0(G' + ear_1) attains (upper semicontinuity along the curve).

Sampler support (HARNESS.md *Evidence*): X0(G') points as in
`maincomp.probe`; `ear_j` placements: each point a uniform `[-9, 9]` integer
combination of an exact basis of the required plane / line / `K^4`
(`earstep.pt_in`), redrawn until adjacent points are distinct (and, for the
rigidity-matrix check of `G`, every ear point affine); `T = 4` placements
per test.  `--chord*`: `q` uniform in `[-30, 30]^2` per vertex, redrawn until
admissible for `G' + ab` and certified in U(G') and U(G' + ab) (6 tries),
`z0` a uniform `[-30, 30]` combination of an exact basis of `L_{G'+ab}(q)`,
`y0 = p_a + t (p_b - p_a)` with `t` a rational in `(0, 1)` (numerator in
`[2, 9]`, denominator in `[12, 19]`), `z1` a uniform `[-30, 30]` combination of
an exact basis of `L_{G'}(q)`.  The flags are those of the
drawn point, not sampled separately; so orbits (ii)-(iv) are reached only
where X0(G') forces them.  Seed 20260924.  Exact Q for every motion space,
relative screw space, span and intersection; the attainment of `G'` at a
draw is screened mod 2^61 - 1 (`rank_p = target` is a certificate) and then
re-derived exactly from the exact motion space.  The trailing `; N s` of
each summary line is wall-clock, the one field exempt from byte-identity.
"""
import argparse
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact, nullspace, wedge2, dot  # noqa: E402
from kbare_common import build_rigidity, verts_of, rank_modp  # noqa: E402
from maincomp import (sample_q, lifting_space, _interp, def_k,  # noqa: E402
                      two_ec_graphs)
from earstep import weld_rows, contract, pt_in  # noqa: E402
from repin import hodge_star  # noqa: E402
from nogood_subdiv import is_simple, count_matroid_rank  # noqa: E402

SEED = 20260924
T = 4                      # placements tried per (P_j) test
E4 = [[F(int(i == j)) for j in range(4)] for i in range(4)]
PL = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def dim(vs):
    vs = [v for v in vs if any(x != 0 for x in v)]
    return rank_exact(vs) if vs else 0


def klein(x, y):
    return dot(x, hodge_star(y))


# ---------------------------------------------------------------- flags

def hom(q, z):
    return [q[0], q[1], z, F(1)]


def normal(h):
    """pi : z = h0 x + h1 y + h2  <->  normal (h0, h1, -1, h2) in K^4."""
    return [h[0], h[1], F(-1), h[2]]


def ev(h, qq):
    return h[0] * qq[0] + h[1] * qq[1] + h[2]


def orbit_of(ha, hb, qa, za, qb, zb):
    if tuple(ha) == tuple(hb):
        return 'iv'
    inc_b = ev(ha, qb) == zb          # p_b in pi_a
    inc_a = ev(hb, qa) == za          # p_a in pi_b
    return 'iii' if (inc_a and inc_b) else ('ii' if (inc_a or inc_b) else 'i')


def placement(rng, j, pa, na, pb, nb, affine=True):
    """Homogeneous points p_a, x_1..x_j, p_b of an ear_j placement."""
    for _ in range(200):
        if j == 1:
            mid = [pt_in(rng, [na, nb])]
        else:
            mid = ([pt_in(rng, [na])] + [[F(rng.randint(-9, 9)) for _ in range(4)]
                                          for _ in range(j - 2)] + [pt_in(rng, [nb])])
        pts = [pa] + mid + [pb]
        if affine and any(x[3] == 0 for x in mid):
            continue
        if all(dim([pts[i], pts[i + 1]]) == 2 for i in range(len(pts) - 1)):
            return pts
    raise RuntimeError('no admissible ear placement in 200 tries')


def chain_lines(pts):
    return [wedge2(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def cap_dim(rho, Lam):
    return dim(rho) + dim(Lam) - dim(rho + Lam)


def p_test(rng, rho, j, fl):
    """(observed, min dim(rho cap Lambda_j), lambda at the min) over T placements."""
    r = dim(rho)
    want = max(0, r + j - 5)
    best = None
    for _ in range(T):
        pts = placement(rng, j, *fl, affine=False)
        Lam = chain_lines(pts)
        c, lam = cap_dim(rho, Lam), dim(Lam)
        if best is None or (lam, -c) > (best[1], -best[0]):
            best = (c, lam)
        if lam == j + 1 and c == want:
            return True, c, lam
    return False, best[0], best[1]


# ---------------------------------------------------------------- X0(G') data

def motion_basis(edges, pt):
    rows, _ = build_rigidity(edges, pt)
    return nullspace(rows)


def rel_space(M, V, a, b):
    ia, ib = V.index(a), V.index(b)
    return [[X[6 * ib + t] - X[6 * ia + t] for t in range(6)] for X in M]


def count_c(edges, V):
    """Every subgraph K has 5 e(K) <= 6(|V(K)| - 1): the 5-fold edge multiset
    is independent in the (6,6)-count matroid."""
    big = [e for e in edges for _ in range(5)]
    return count_matroid_rank(big, V, k=6, ell=6) == len(big)


def draw_point(edges, rng, draws, S=30):
    """First X0(G') draw (maincomp.probe's sampler) at which G' attains."""
    V = verts_of(edges)
    n = len(V)
    tgt = 6 * (n - 1) - def_k(edges, 6)
    for _ in range(draws):
        q = sample_q(rng, V, edges, S)
        L = lifting_space(edges, V, q)
        coeff = [rng.randint(-S, S) for _ in L]
        z = [sum(c * bb[i] for c, bb in zip(coeff, L)) for i in range(n)]
        pt = {v: (q[v][0], q[v][1], z[i]) for i, v in enumerate(V)}
        if rank_modp(build_rigidity(edges, pt)[0]) == tgt:
            return dict(q=q, L=L, z=z, pt=pt, tgt=tgt, V=V,
                        jj=len(L) == 3 + def_k(edges, 3))
    return None


def instance(edges, a, b, P, rng, ks=(2, 3)):
    """All data at one (G', a, b) and one attaining X0(G') point P."""
    V = P['V']
    q, z, pt, L = P['q'], P['z'], P['pt'], P['L']
    f = def_k(edges, 6)
    vs = [v for v in V if v != b]
    g = def_k(contract(edges, a, b), 6, vs)
    delta = f - g
    d2 = def_k(edges, 3)
    delta2 = d2 - def_k(contract(edges, a, b), 3, vs)
    M = motion_basis(edges, pt)
    assert len(M) == 6 * len(V) - P['tgt'], 'exact rank of G\' != mod-p certificate'
    rho = rel_space(M, V, a, b)
    r = dim(rho)
    Mw = nullspace(build_rigidity(edges, pt)[0] + weld_rows(V, a, b))
    assert r == len(M) - len(Mw), 'r != dim M - dim M_weld'
    h = _interp(edges, V, q, z)
    ia, ib = V.index(a), V.index(b)
    orb = orbit_of(h[a], h[b], q[a], z[ia], q[b], z[ib])
    Hs = [_interp(edges, V, q, bb) for bb in L]
    dU = dim([[x - y for x, y in zip(hh[a], hh[b])] for hh in Hs])
    fg = dim([[bb[ib] - ev(hh[a], q[b]), bb[ia] - ev(hh[b], q[a])]
              for bb, hh in zip(L, Hs)])
    adj = any({a, b} == {u, w} for (u, w) in edges)
    cc = count_c(edges, V)
    if cc and not adj:
        assert delta2 >= 2, ('(MC-48) delta2 < 2 under the count', a, b, delta2)
    if fg == 2:
        assert orb == 'i' and dU >= 2, '(MC-48) FG without orbit (i), dim U >= 2'
    if orb == 'iv':
        assert dU == 0
    if orb == 'iii':
        assert dU <= 1
    fl = (hom(q[a], z[ia]), normal(h[a]), hom(q[b], z[ib]), normal(h[b]))
    rec = dict(r=r, delta=delta, delta2=delta2, orb=orb, dU=dU, fg=fg, adj=adj,
               cert=(r == delta), jj=P['jj'], count=cc, k={})
    for k in ks:
        obs_prev = p_test(rng, rho, k - 1, fl)
        obs_k = p_test(rng, rho, k, fl)
        if obs_prev[0] and k == 3:
            assert obs_k[0], ('(MC-45) (P2) holds but (P3) not found', r, orb)
        if obs_prev[0] and k == 2 and orb in ('i', 'ii'):
            assert obs_k[0], ('(MC-46) (P1) holds but (P2) not found', r, orb)
        att = ear_point_check(edges, V, pt, a, b, M, rho, r, delta, f, k, fl, rng)
        rec['k'][k] = dict(prev=obs_prev, cur=obs_k, att=att)
    return rec


def ear_point_check(edges, V, pt, a, b, M, rho, r, delta, f, k, fl, rng):
    """Build G = G' + ear_k at one affine placement, check (MC-16) exactly and
    (MC-22)'s pointwise form; return whether G attains there."""
    pts = placement(rng, k, *fl, affine=True)
    Lam = chain_lines(pts)
    lam, c = dim(Lam), cap_dim(rho, Lam)
    tags = [('ear', i) for i in range(k)]
    Ge = list(edges) + list(zip([a] + tags, tags + [b]))
    pt2 = dict(pt)
    for tg, x in zip(tags, pts[1:-1]):
        pt2[tg] = (x[0] / x[3], x[1] / x[3], x[2] / x[3])
    n2 = len(V) + k
    dimMG = 6 * n2 - rank_exact(build_rigidity(Ge, pt2)[0])
    pred = len(M) - r + c + (k + 1) - lam
    assert dimMG == pred, ('(MC-16) pointwise identity fails', dimMG, pred)
    defG = f - min(delta, 5 - k)                     # (MC-17), k <= 4
    assert defG == def_k(Ge, 6), '(MC-17) fails'
    attains = dimMG == 6 + defG
    if len(M) == 6 + f and lam == k + 1:
        crit = r >= min(delta, 5 - k) and c == max(0, r + k - 5)
        assert attains == crit, '(MC-22) pointwise iff fails'
    return attains


# ---------------------------------------------------------------- populations

def chains(E, ks=(2, 3)):
    """Maximal degree-2 chains with k in `ks` interior vertices between two
    distinct NON-adjacent vertices of degree >= 3: (a, b, interior)."""
    nb = {}
    for (u, w) in E:
        nb.setdefault(u, set()).add(w)
        nb.setdefault(w, set()).add(u)
    deg = {x: len(nb[x]) for x in nb}
    adj = {frozenset(e) for e in E}
    out, seen = [], set()
    for x in sorted(nb, key=str):
        if deg[x] != 2 or x in seen:
            continue
        ends = []
        for s in sorted(nb[x], key=str):
            prev, cur, part = x, s, []
            while deg[cur] == 2 and cur != x:
                part.append(cur)
                prev, cur = cur, [y for y in nb[cur] if y != prev][0]
            ends.append((cur, part))
        seen.add(x)
        for _, part in ends:
            seen |= set(part)
        (e1, p1), (e2, p2) = ends
        inter = list(reversed(p1)) + [x] + p2
        if e1 == e2 or frozenset((e1, e2)) in adj or len(inter) not in ks:
            continue
        out.append((e1, e2, inter))
    return out


def member_instances(name, E, ks=(2, 3)):
    out = []
    for (a, b, inter) in chains(E, ks):
        Gp = [(u, w) for (u, w) in E if u not in inter and w not in inter]
        out.append((f'{name}:{a}-{b}', Gp, a, b, len(inter)))
    return out


# ---------------------------------------------------------------- tables

def new_cell():
    return dict(n=0, cert=0, prev=0, cur=0, bad=0, att=0)


def tally(cells, rec, anomalies, label):
    for k, d in rec['k'].items():
        key = (k, rec['orb'], rec['r'])
        c = cells.setdefault(key, new_cell())
        c['n'] += 1
        c['cert'] += rec['cert']
        c['prev'] += d['prev'][0]
        c['cur'] += d['cur'][0]
        c['att'] += d['att']
        if d['prev'][0] and not d['cur'][0]:
            c['bad'] += 1
            anomalies.append((label, k, rec['orb'], rec['r'], rec['delta'], rec['dU']))


def print_cells(cells, title):
    print(f'-- {title}: per (k, orbit, r) cell: n | cert (r = delta) | '
          f'(P_(k-1)) seen | (P_k) seen | (P_(k-1)) but not (P_k) | G attains at the point')
    for key in sorted(cells):
        c = cells[key]
        print(f'   k={key[0]} orbit {key[1]:<3} r={key[2]}: {c["n"]:>5} | {c["cert"]:>5} | '
              f'{c["prev"]:>5} | {c["cur"]:>5} | {c["bad"]:>3} | {c["att"]:>5}')


def run_instances(insts, draws, title, t0):
    cells, anomalies, extra = {}, [], dict(noatt=0, fg=0, count=0, cfg=0, orbs={})
    for (label, Gp, a, b, ks, P, rng) in insts:
        if P is None:
            extra['noatt'] += 1
            continue
        rec = instance(Gp, a, b, P, rng, ks)
        extra['fg'] += rec['fg'] == 2
        extra['count'] += rec['count']
        extra['cfg'] += rec['count'] and rec['fg'] == 2
        extra['orbs'][rec['orb']] = extra['orbs'].get(rec['orb'], 0) + 1
        tally(cells, rec, anomalies, label)
    print_cells(cells, title)
    ninst = sum(extra['orbs'].values())
    print(f'   instances {ninst}; orbits {dict(sorted(extra["orbs"].items()))}; '
          f'flag-generic (FG) at {extra["fg"]}; count (5e <= 6(|K|-1)) holds at '
          f'{extra["count"]}, and FG is observed at {extra["cfg"]} of those ((MC-48)(ii) '
          f'predicts all, modulo Jackson-Jordan); G\' short at every draw: {extra["noatt"]}')
    for x in anomalies[:30]:
        print('   (P_(k-1)) holds, (P_k) not found:', x)
    tot_bad = sum(c['bad'] for c in cells.values())
    print(f'{title}: {ninst} instances, {sum(c["n"] for c in cells.values())} '
          f'(instance, k) cells-entries, {tot_bad} with (P_(k-1)) but not (P_k); '
          f'asserts (MC-16), (MC-22), (MC-45), (MC-46), (MC-48) passed; '
          f'{time.time() - t0:.1f} s')
    return 0


def exh(N, draws):
    t0 = time.time()
    insts = []
    for name, E in two_ec_graphs(N):
        rng = random.Random(f'{SEED}:ante:{name}')
        P = draw_point(E, rng, draws)
        V = verts_of(E)
        adj = {frozenset(e) for e in E}
        for i, a in enumerate(V):
            for b in V[i + 1:]:
                if frozenset((a, b)) in adj:
                    continue
                insts.append((f'{name}:{a}-{b}', E, a, b, (2, 3), P,
                              random.Random(f'{SEED}:ante:{name}:{a}-{b}')))
    return run_instances(insts, draws, f'exh n <= {N} (G\' 2EC, non-adjacent a, b)', t0)


def members(pop, title, draws):
    t0 = time.time()
    insts = []
    for name, E in pop:
        if not is_simple(E):
            continue
        for (label, Gp, a, b, k) in member_instances(name, E):
            rng = random.Random(f'{SEED}:ante:{label}')
            P = draw_point(Gp, rng, draws)
            insts.append((label, Gp, a, b, (k,), P, rng))
    return run_instances(insts, draws, title, t0)


# ---------------------------------------------------------------- --frames

def frame_of(orb):
    """(p_a, normal of pi_a, p_b, normal of pi_b), pi = {X : n.X = 0}, plus the
    two terminal pencils and, in orbit (iv), the plane."""
    e = E4
    fr = {'i': (e[0], [0, 1, 0, 0], e[1], [1, 0, 0, 0]),       # pi_a=<e0,e2,e3>, pi_b=<e1,e2,e3>
          'ii': (e[0], [0, 0, 0, 1], e[1], [1, 0, 0, 0]),      # pi_a=<e0,e1,e2>, pi_b=<e1,e2,e3>
          'iii': (e[0], [0, 0, 0, 1], e[1], [0, 0, 1, 0]),     # pi_a=<e0,e1,e2>, pi_b=<e0,e1,e3>
          'iv': (e[0], [0, 0, 0, 1], e[1], [0, 0, 0, 1])}[orb]
    pa, na, pb, nb = fr
    na, nb = [F(x) for x in na], [F(x) for x in nb]
    A = nullspace([na])
    B = nullspace([nb])
    pen_a = [wedge2(pa, x) for x in A]
    pen_b = [wedge2(pb, x) for x in B]
    lines_pi = [wedge2(A[i], A[j]) for i in range(3) for j in range(i + 1, 3)]
    return (pa, na, pb, nb), pen_a, pen_b, lines_pi


def rnd6(rng):
    return [F(rng.randint(-9, 9)) for _ in range(6)]


def comb(rng, vs):
    cs = [F(rng.randint(-9, 9)) for _ in vs]
    return [sum(c * v[t] for c, v in zip(cs, vs)) for t in range(6)]


def frames():
    rng = random.Random(f'{SEED}:frames')
    bad = 0
    for orb in ('i', 'ii', 'iii', 'iv'):
        fl, pen_a, pen_b, lines_pi = frame_of(orb)
        assert dim(pen_a) == 2 and dim(pen_b) == 2
        N = pen_a + pen_b
        dN = dim(N)
        for r in (1, 2, 3):
            fams = {'random': [rnd6(rng) for _ in range(r)]}
            if r >= 2:
                fams['>=Pen_a'] = pen_a + [rnd6(rng) for _ in range(r - 2)]
                fams['>=Pen_b'] = pen_b + [rnd6(rng) for _ in range(r - 2)]
            if r < dN:
                fams['<=Pen_a+Pen_b'] = [comb(rng, N) for _ in range(r)]
            if orb == 'iv':
                fams['meets Lambda^2 pi'] = [comb(rng, lines_pi)] + [rnd6(rng) for _ in range(r - 1)]
            for fam, rho in fams.items():
                if dim(rho) != r:
                    continue
                row = []
                for k in (1, 2, 3):
                    if orb == 'iii' and k == 1:
                        row.append('k=1 n/a')
                        continue
                    ok = p_test(rng, rho, k, fl)[0]
                    row.append(f'k={k}:{"good" if ok else "BAD"}')
                    want = expected(orb, fam, r, k, dN)
                    if want is not None and want != ok:
                        bad += 1
                        row[-1] += '(!)'
                print(f'   orbit {orb:<3} r={r} {fam:<18} ' + ' '.join(row))
    print(f'frames: {"all expected statuses" if not bad else f"{bad} UNEXPECTED"} '
          f'(random rho good outside orbit (iii) k=1; terminal pencils bad at r <= 5-k; '
          f'rho in Pen_a+Pen_b bad at k <= 2 in orbits (i)-(iii); orbit (iv) at k=2: '
          f'rho meeting Lambda^2 pi bad)')
    return bad


def expected(orb, fam, r, k, dN):
    if fam == 'random':
        return True
    if fam in ('>=Pen_a', '>=Pen_b'):
        return not (r <= 5 - k)
    if fam == '<=Pen_a+Pen_b':
        if orb in ('i', 'ii'):          # dim N = 4
            if r == 3:
                return k == 3
            return True if k >= 2 else None
        if orb == 'iii':                # dim N = 3: B_2(2) = B_3(2) = {rho in N}
            return False if (r == 2 and k >= 2) else None
        return None
    if fam == 'meets Lambda^2 pi':
        return False if k == 2 else None
    return None


# ---------------------------------------------------------------- --orbits

def padd(p, q_, s=1):
    out = dict(p)
    for m, c in q_.items():
        out[m] = out.get(m, 0) + s * c
        if out[m] == 0:
            del out[m]
    return out


def pmul(p, q_):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q_.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            out[m] = out.get(m, 0) + c1 * c2
            if out[m] == 0:
                del out[m]
    return out


def minors(Mat, s):
    """All s x s minors of a matrix of polynomials (rows x cols), exact, as
    {(rowset, colset): poly}; DP over column subsets."""
    nr, nc = len(Mat), len(Mat[0])
    out = {}
    for rows in itertools.combinations(range(nr), s):
        D = {(): {(0, 0, 0): F(1)}}
        for i in rows:
            D2 = {}
            for S, val in D.items():
                if not val:
                    continue
                for j in range(nc):
                    if j in S or not Mat[i][j]:
                        continue
                    sgn = -1 if sum(1 for x in S if x > j) % 2 else 1
                    T_ = tuple(sorted(S + (j,)))
                    D2[T_] = padd(D2.get(T_, {}), pmul(val, Mat[i][j]), sgn)
            D = D2
        for S, val in D.items():
            if val:
                out[(rows, S)] = val
    return out


def lie_act(X, c):
    out = [dict() for _ in range(6)]
    for kk, (i, j) in enumerate(PL):
        if not c[kk]:
            continue
        Xi = [X[r][i] for r in range(4)]
        Xj = [X[r][j] for r in range(4)]
        w1 = wedge2(Xi, E4[j])
        w2 = wedge2(E4[i], Xj)
        for t in range(6):
            s = w1[t] + w2[t]
            if s:
                out[t] = padd(out[t], {m: cc * s for m, cc in c[kk].items()})
    return out


def orbits():
    """The orbit-dimension table behind (MC-46)'s count, exact and symbolic."""
    e = E4
    cases = {
        'i': ({0: [0], 1: [1], 2: [2, 3], 3: [2, 3]},
              e[0], [e[0][t] + e[2][t] for t in range(4)],
              [e[1][t] + e[3][t] for t in range(4)], e[1], 5,
              {'l0 l1 != 0': (4, None, (0, 1)), 'l0 = 0, l1 l2 != 0': (4, 0, (1, 2)),
               'L1': (4, (0, 2), (1,)), 'l1 = 0, l0 l2 != 0': (3, 1, (0, 2)),
               'L0': (1, (1, 2), (0,)), 'L2': (1, (0, 1), (2,))}),
        'ii': ({0: [0], 1: [1], 2: [1, 2], 3: [1, 2, 3]},
               e[0], [e[0][t] + e[2][t] for t in range(4)], e[3], e[1], 6,
               {'l0 l1 l2 != 0': (5, None, (0, 1, 2)), 'l2 = 0, l0 l1 != 0': (4, 2, (0, 1)),
                'l0 = 0, l1 l2 != 0': (4, 0, (1, 2)), 'L1': (4, (0, 2), (1,)),
                'l1 = 0, l0 l2 != 0': (3, 1, (0, 2)), 'L0': (1, (1, 2), (0,)),
                'L2': (1, (0, 1), (2,))}),
    }
    bad = 0
    for orb, (allowed, pa, x1, x2, pb, gdim, table) in cases.items():
        gens = []
        for col, rows in allowed.items():
            for r_ in rows:
                X = [[F(0)] * 4 for _ in range(4)]
                X[r_][col] = F(1)
                gens.append(X)
        assert len(gens) == gdim + 1
        Ls = [wedge2(pa, x1), wedge2(x1, x2), wedge2(x2, pb)]
        assert dim(Ls) == 3
        c = [padd(padd({(1, 0, 0): Ls[0][t]} if Ls[0][t] else {},
                       {(0, 1, 0): Ls[1][t]} if Ls[1][t] else {}),
                  {(0, 0, 1): Ls[2][t]} if Ls[2][t] else {}) for t in range(6)]
        Tm = [lie_act(X, c) for X in gens]
        # transitivity on ear_2 placements: the stabiliser's orbit of (x1, x2)
        # in P(pi_a) x P(pi_b) has dimension 4
        tang = []
        for X in gens:
            v1 = [sum(X[i][j] * x1[j] for j in range(4)) for i in range(4)]
            v2 = [sum(X[i][j] * x2[j] for j in range(4)) for i in range(4)]
            tang.append(v1 + v2)
        odim_pl = dim(tang + [x1 + [F(0)] * 4, [F(0)] * 4 + x2]) - 2
        assert odim_pl == 4, ('stabiliser not transitive on ear_2 placements', orb, odim_pl)
        print(f'orbit ({orb}): stabiliser dim {gdim}; transitive on generic ear_2 placements '
              f'(orbit dim 4 in P(pi_a) x P(pi_b))')
        for stratum, (d, kill, need) in table.items():
            s = d + 1                            # tangent rank = proj orbit dim + 1
            if kill is None:
                sub = Tm
            else:
                ks = (kill,) if isinstance(kill, int) else kill
                sub = [[{m: cc for m, cc in ent.items() if all(m[x] == 0 for x in ks)}
                        for ent in row] for row in Tm]
            mins = minors(sub, s)
            wit = None
            for key, pol in mins.items():
                if len(pol) == 1:
                    (mono, cf), = pol.items()
                    if all(mono[x] == 0 for x in range(3) if x not in need):
                        wit = (key, mono, cf)
                        break
            upper = minors(sub, s + 1) if s + 1 <= min(len(sub), 6) else {}
            ok = wit is not None and not upper
            bad += not ok
            print(f'   {stratum:<20}: projective orbit dimension {d}'
                  f'{" (certified: a monomial minor of size %d, none of size %d)" % (s, s + 1) if ok else " FAILED"}')
        if orb == 'i':
            rng = random.Random(f'{SEED}:semiinv')
            for _ in range(5):
                x = [F(rng.randint(-9, 9)) for _ in range(6)]
                a_, b_ = F(rng.randint(1, 9)), F(rng.randint(1, 9))
                C = [[F(rng.randint(-9, 9)) for _ in range(2)] for _ in range(2)]
                g = [[a_, 0, 0, 0], [0, b_, 0, 0], [0, 0, C[0][0], C[0][1]],
                     [0, 0, C[1][0], C[1][1]]]
                gx = [F(0)] * 6
                for kk, (i, j) in enumerate(PL):
                    gi = [F(g[r_][i]) for r_ in range(4)]
                    gj = [F(g[r_][j]) for r_ in range(4)]
                    w = wedge2(gi, gj)
                    gx = [u + x[kk] * v for u, v in zip(gx, w)]
                q1 = lambda y: y[0] * y[5]                               # noqa: E731
                q2 = lambda y: y[1] * y[4] - y[2] * y[3]                 # noqa: E731
                chi = a_ * b_ * (C[0][0] * C[1][1] - C[0][1] * C[1][0])
                assert q1(gx) == chi * q1(x) and q2(gx) == chi * q2(x), 'semi-invariance'
            print('   Q1 = x_M x_L and Q2 = det[x_u | x_v] are semi-invariants of one '
                  'character (5 exact group elements)')
    print(f'orbits: {"table certified" if not bad else f"{bad} strata FAILED"}')
    return bad


# ---------------------------------------------------------------- --chord

def limit_plane(n, v):
    """The plane spanned by two meeting lines with Pluecker vectors n, v, as a
    1-element basis of its normal covectors."""
    N_ = nullspace(line_points(n) + line_points(v))
    assert len(N_) == 1, 'the two lines do not span a plane'
    return N_


def line_points(L_):
    """Two points spanning the line with Pluecker vector L_ (decomposable):
    for L_ = p ^ q the antisymmetric matrix p q^T - q p^T has row space <p, q>."""
    M = [[F(0)] * 4 for _ in range(4)]
    for kk, (i, j) in enumerate(PL):
        M[i][j] = L_[kk]
        M[j][i] = -L_[kk]
    out = []
    for i in range(4):
        rowi = M[i]
        if any(rowi):
            out.append(rowi)
    basis = []
    for x in out:
        if dim(basis + [x]) > len(basis):
            basis.append(x)
    assert len(basis) == 2, 'not a line'
    return basis


def chord_instance(E, a, b, rng):
    """k = 1 at (G', a, b), a !~ b: the chord gadget G' + ab.  None if no
    certified attaining X0(G'+ab) point over a certified q in 6 draws."""
    V = verts_of(E)
    nV = len(V)
    f = def_k(E, 6)
    d2 = def_k(E, 3)
    Ec = E + [(a, b)]
    tgt_c = 6 * (nV - 1) - def_k(Ec, 6)
    vs = [v for v in V if v != b]
    delta = f - def_k(contract(E, a, b), 6, vs)
    d2c = def_k(Ec, 3)
    got = None
    for _ in range(6):
        q = sample_q(rng, V, Ec, 30)
        try:
            L = lifting_space(E, V, q)
        except AssertionError:              # N_{G'}[v] collinear at this q
            continue
        Lc = lifting_space(Ec, V, q)
        if len(L) != 3 + d2 or len(Lc) != 3 + d2c:
            continue
        coeff = [rng.randint(-30, 30) for _ in Lc]
        z = [sum(c * bb[t] for c, bb in zip(coeff, Lc)) for t in range(nV)]
        pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
        if rank_modp(build_rigidity(Ec, pt)[0]) == tgt_c:
            got = (q, L, z, pt)
            break
    if got is None:
        return None
    q, L, z, pt = got
    M = motion_basis(E, pt)
    Mc = motion_basis(Ec, pt)
    assert len(Mc) == 6 * nV - tgt_c, 'exact rank of G\'+ab != mod-p certificate'
    rho = rel_space(M, V, a, b)
    r = dim(rho)
    ia, ib = V.index(a), V.index(b)
    pa, pb = hom(q[a], z[ia]), hom(q[b], z[ib])
    n = wedge2(pa, pb)
    cn = cap_dim(rho, [n])
    assert len(Mc) == len(M) - r + cn, '(MC-16) at the chord fails'
    ap = len(M) - 6 - f
    assert r - cn == min(delta, 5) + ap, '(MC-49) chord attainment identity'
    if delta <= 5:
        assert cn == 0 and r == delta + ap, '(MC-49) delta <= 5 consequences'
    nperp = cap_dim(rho, nullspace([hodge_star(n)]))       # rho cap n^perp (Klein)
    # the degenerate ear_1 point y0 on the line p_a p_b
    t = F(rng.randint(2, 9), rng.randint(2, 9) + 10)
    y0 = tuple(pt[a][s] + t * (pt[b][s] - pt[a][s]) for s in range(3))
    y0h = [y0[0], y0[1], y0[2], F(1)]
    Ge = E + [(a, ('ear', 0)), (('ear', 0), b)]
    pt2 = dict(pt)
    pt2[('ear', 0)] = y0
    dMG = 6 * (nV + 1) - rank_exact(build_rigidity(Ge, pt2)[0])
    assert dMG == len(Mc) + 1, '(MC-49) degenerate ear_1 point identity'
    defG = f - min(delta, 4)
    assert defG == def_k(Ge, 6), '(MC-17) fails'
    Hs = [_interp(E, V, q, bb) for bb in L]
    dU = dim([[x - y for x, y in zip(hh[a], hh[b])] for hh in Hs])
    if delta >= 5 and dU >= 2:
        assert dMG == 6 + defG, '(MC-49) delta >= 5 closure fails'
    # (MC-50): first-order limit of the ear_1 span along the line z0 + s z1 in
    # L(q), with q_y(s) on m(s) through q_y0; asserted: a pencil at y0 through n
    h0 = _interp(E, V, q, z)
    D0 = [x - y for x, y in zip(h0[a], h0[b])]
    planes, K0best = [], None
    if (D0[0], D0[1]) != (0, 0):
        nn = D0[0] * D0[0] + D0[1] * D0[1]
        for _ in range(2):
            c1 = [rng.randint(-30, 30) for _ in L]
            z1 = [sum(cc * bb[s] for cc, bb in zip(c1, L)) for s in range(nV)]
            h1 = _interp(E, V, q, z1)
            D1 = [x - y for x, y in zip(h1[a], h1[b])]
            lam_ = -ev(D1, y0) / nn
            w = (lam_ * D0[0], lam_ * D0[1])
            zy1 = ev(h1[a], y0) + h0[a][0] * w[0] + h0[a][1] * w[1]
            py1 = [w[0], w[1], zy1, F(0)]
            pa1 = [F(0), F(0), z1[ia], F(0)]
            pb1 = [F(0), F(0), z1[ib], F(0)]
            v1 = [x + y for x, y in zip(wedge2(pa1, y0h), wedge2(pa, py1))]
            v2 = [x + y for x, y in zip(wedge2(py1, pb), wedge2(y0h, pb1))]
            v = [(1 - t) * x - t * y for x, y in zip(v1, v2)]
            if dim([n, v]) != 2:
                continue
            assert dim([wedge2(y0h, E4[s]) for s in range(4)] + [v]) == 3, \
                '(MC-50) limit line not through y0'
            assert klein(v, v) == 0 and klein(n, v) == 0, '(MC-50) limit not a pencil'
            K0 = len(M) - r + cap_dim(rho, [n, v])
            K0best = K0 if K0best is None else min(K0best, K0)
            planes.append(limit_plane(n, v))
    distinct = len(planes) == 2 and dim(planes[0] + planes[1]) > 1
    closes = K0best is not None and K0best == 6 + defG and dU >= 2
    if (D0[0], D0[1]) == (0, 0):
        lim = 'n/a (pi_a || pi_b at z0)'
    elif not planes:
        lim = 'n/a (limit degenerate)'
    else:
        lim = ('K0 = target' if closes else 'K0 > target') + \
              (', planes differ' if distinct else ', one plane')
    return dict(delta=delta, ap=ap, r=r, nperp=nperp, dU=dU, distinct=distinct,
                closes=closes, lim=lim)


def chord_run(insts, title):
    t0 = time.time()
    hist, tot, none = {}, 0, 0
    red = close = low = 0
    for (label, E, a, b, rng) in insts:
        tot += 1
        rec = chord_instance(E, a, b, rng)
        if rec is None:
            none += 1
            continue
        key = (min(rec['delta'], 6), rec['ap'], rec['r'], rec['nperp'], rec['dU'] >= 2,
               rec['lim'])
        hist[key] = hist.get(key, 0) + 1
        if rec['delta'] <= 4:
            low += 1
            if rec['nperp'] <= 3 and rec['distinct']:
                red += 1
                close += rec['closes']
    print(f'-- {title}: (delta, a\'(z0), r(z0), dim(rho(z0) cap n^perp), dim U >= 2, '
          'the first-order limit pencils): count')
    for key in sorted(hist):
        print(f'   delta={key[0]} a\'={key[1]} r={key[2]} dim(rho cap n^perp)={key[3]} '
              f'dimU>=2={key[4]} limit: {key[5]}: {hist[key]}')
    print(f'{title}: {tot} pairs, {tot - none} with a certified attaining X0(G\'+ab) point over '
          f'a certified q (identities asserted at all); delta <= 4 at {low}, of which '
          f'dim(rho(z0) cap n^perp) <= 3 with two distinct limit planes at {red} and a limit '
          f'pencil reaching K0 = target at {close}; no certified draw at {none}; '
          f'{time.time() - t0:.1f} s')
    return 0


def chord_exh(N):
    insts = []
    for name, E in two_ec_graphs(N):
        V = verts_of(E)
        adj = {frozenset(e) for e in E}
        for i, a in enumerate(V):
            for b in V[i + 1:]:
                if frozenset((a, b)) not in adj:
                    insts.append((f'{name}:{a}-{b}', E, a, b,
                                  random.Random(f'{SEED}:chord:{name}:{a}-{b}')))
    return chord_run(insts, f'chord, exh n <= {N}')


def chord_members(pop, title):
    insts = []
    for name, E in pop:
        if not is_simple(E):
            continue
        for (label, Gp, a, b, k) in member_instances(name, E, ks=(1,)):
            insts.append((label, Gp, a, b, random.Random(f'{SEED}:chord:{label}')))
    return chord_run(insts, title)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--orbits', action='store_true')
    ap.add_argument('--frames', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--habitats', action='store_true')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--chord', type=int, default=0)
    ap.add_argument('--chord-thetas', type=int, default=0)
    ap.add_argument('--chord-habitats', action='store_true')
    ap.add_argument('--stride', type=int, default=1)
    ap.add_argument('--draws', type=int, default=3)
    a = ap.parse_args()
    print(f'# earante.py seed={SEED} T={T}')
    bad = 0
    if a.orbits:
        bad += orbits()
    if a.frames:
        bad += frames()
    if a.exh:
        bad += exh(a.exh, a.draws)
    if a.thetas:
        from maincomp import thetas
        bad += members(thetas(a.thetas), f'thetas p1+p2+p3 <= {a.thetas}', a.draws)
    if a.habitats or a.chord_habitats:
        from maincomp import habitats
        pop = habitats()[::a.stride]
        if a.limit:
            pop = pop[:a.limit]
        tag = f'habitats ({len(pop)} members, stride {a.stride})'
        if a.habitats:
            bad += members(pop, tag, a.draws)
        if a.chord_habitats:
            bad += chord_members(pop, 'chord, ' + tag)
    if a.chord:
        bad += chord_exh(a.chord)
    if a.chord_thetas:
        from maincomp import thetas
        bad += chord_members(thetas(a.chord_thetas), f'chord, thetas p1+p2+p3 <= {a.chord_thetas}')
    if not (a.orbits or a.frames or a.exh or a.thetas or a.habitats or a.chord
            or a.chord_thetas or a.chord_habitats):
        ap.error('name a mode')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
