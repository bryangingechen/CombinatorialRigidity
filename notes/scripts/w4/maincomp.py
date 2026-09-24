#!/usr/bin/env python3
"""
maincomp.py -- the main-component census (W4 reopened, P1; workbook §(K-main)).

The object (`notes/pencil/workbook/K-main.md`).  A pencil configuration of a
simple graph `G` is `p : V -> P^3`, adjacent points distinct, every closed
neighbourhood `N[v]` coplanar.  In the affine chart `p_v = (q_v, z_v)` (a planar
position and a height).  For a planar picture `q` in which every `q(N[v])` with
`|N[v]| >= 3` is non-collinear:

  (MC-1) the pencil condition is LINEAR in `z`: `z` must lie in the lifting
         space `L(q) = {z : z|N[v] is the restriction of an affine function of
         q, for every v}`;
  (MC-2) the main component `X0` is the closure of `{(q, z) : q generic,
         z in L(q)}` -- irreducible, containing the flat configurations `z = 0`;
  (MC-3) the hinge extensors `p_u ^ p_v` are affine in `z`, so the augmented
         motion matrix at `(q, z)` is `A0(q) + A1(z)`, `A1` linear;
  (MC-4) at connected `G` with min degree >= 2 the flat rank is
         `rank(q, 0) = 6|V| - 3 - dim L(q)` exactly, and `dim L(q) >= 3 + def2`.

Per instance this driver samples ONE point of X0 per draw -- `q` with integer
coordinates in `[-S, S]`, redrawn until `q` is injective on edges and every
closed neighbourhood of size >= 3 is non-collinear; an exact basis of `L(q)`;
`z` a random integer combination of it -- and reports:

  rank    the molecular rank at `(q, z)` (5 rows per hinge, `kbare_common.
          build_rigidity`, the landed `rigidityRows` model), computed mod the
          Mersenne prime 2^61-1.  rank mod p <= rank over Q <= target always
          (`kbare_common` docstring: the partition bound), so
          `rank_p == target` CERTIFIES `rank_Q == target`: an exhibited
          attaining point of X0, a proof for that graph.  A shortfall is
          re-checked in exact Q and redrawn (`--retry`); the best draw is a
          LOWER bound for X0's generic rank (semicontinuity), not a measurement
          of it.
  target  `6(|V|-1) - def3`, `def3` by the (6,6) pebble game
          (`nogood_subdiv.deficiency`).
  def2    `max_P 3(|P|-1) - 2 d(P)` (Lean `deficiency G 2`), by the (3,3)
          pebble game on `2G` (`nogood_subdiv.count_matroid_rank`, k = l = 3).
  dimL    `dim L(q)`, exact.
  flat    the rank at `(q, 0)`, mod p; ASSERTED equal to `6|V| - 3 - dimL`
          ((MC-4), elementary) and to be `<= 6(|V|-1) - def2`.
  JJ      `dimL == 3 + def2`, i.e. the flat rank equals Jackson--Jordan's
          `6(|V|-1) - def2` at this `q` (the smark brief §3(a) citation;
          published, unformalized, unverified beyond R).
  gain1   (with `--gain`) the first-order rank gain at the flat point in the
          direction `z`: rank of `S0^T A1(z) K0`, `K0`/`S0` the kernel / left
          kernel of the augmented flat matrix `A0`.  Needed gain: `def2 - def3`.
          Computed mod p; a lower bound for the Q-rank whenever the mod-p rank
          of `A0` equals its Q-rank, which is asserted from (MC-4).  The three
          trivial liftings (z = 1, x, y) are asserted to give `gain1 = 0`.
  nondeg  whether the sampled point satisfies all four conjuncts of
          `IsNondegPencilRealization` (`flanks.nondeg_conjuncts`), with the
          failing conjunct named.

Asserted per draw: (MC-1) forward -- every closed neighbourhood coplanar and
adjacent points distinct at `(q, z)` (`kbare_common.verify_pencil_witness`);
(MC-3) on the first draw of every instance -- the augmented matrix is affine
along `z` (A(z1+z2) = A(z1)+A(z2)-A(0), A(2z) = 2A(z)-A(0), exactly);
(MC-4) as above.

Modes (run from the repository root; exact arithmetic; seeded; writes nothing):

    python3 notes/scripts/w4/maincomp.py --selftest
    python3 notes/scripts/w4/maincomp.py --battery [--gain]
    python3 notes/scripts/w4/maincomp.py --exh 7 [--gain]
    python3 notes/scripts/w4/maincomp.py --pool NAME [--gain]   (NAME: --list)

`--exh N` is every isomorphism class of simple 2-edge-connected graphs on
3..N vertices, generated here by vertex augmentation of connected graphs with
a stdlib canonical form (individualization-refinement; no nauty); the counts
are asserted against OEIS A001349 (connected) and A007146 (connected
bridgeless) through n = 8 in `--selftest`.  `--pool exh8` is the same
population with per-n summaries.  Every mode's members are kept iff simple
and 2EC.

Sampler support (HARNESS.md *Evidence*): `q` uniform on `[-S, S]^{2|V|}`
integers, `S = --scale` (default 30), rejection on the two open conditions
above; `z` a uniform `[-S, S]` integer combination of the RREF basis of `L(q)`
(integer-scaled).  It varies every coordinate of the X0 fibre bundle; it does
NOT sample any other component of the configuration space (no vertical
planes, no special `q` where `L(q)` jumps), by design.
"""
import argparse
import os
import random
import sys
import time
from fractions import Fraction as F
from math import lcm

import os, sys  # noqa: F811
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank as rank_exact, nullspace, wedge2, hat, neighbors  # noqa: E402
from kbare_common import (rank_modp, build_rigidity, verts_of, is_2ec,       # noqa: E402
                          verify_pencil_witness, exact_deficiency, P61)
from nogood_subdiv import count_matroid_rank, deficiency as def3_pebble       # noqa: E402

P = P61


# ---------------------------------------------------------------- deficiencies

def def_k(edges, D, verts=None):
    """Lean `deficiency G n` with `D = bodyBarDim n`: `max_P D(|P|-1) -
    (D-1) d(P)`, as `D(|V|-1) - rank_{(D,D)}((D-1)G)` (Tay's count)."""
    if verts is None:
        verts = verts_of(edges)
    n = len(verts)
    if n <= 1:
        return 0
    big = [e for e in edges for _ in range(D - 1)]
    return D * (n - 1) - count_matroid_rank(big, verts, k=D, ell=D)


def def_brute(edges, D):
    """The same maximum by enumerating every set partition (small n only)."""
    V = verts_of(edges)
    best = 0

    def rec(i, lab, k):
        nonlocal best
        if i == len(V):
            d = sum(1 for (u, w) in edges if lab[u] != lab[w])
            best = max(best, D * (k - 1) - (D - 1) * d)
            return
        for c in range(k + 1):
            lab[V[i]] = c
            rec(i + 1, lab, max(k, c + 1))
        del lab[V[i]]
    rec(0, {}, 0)
    return best


# ---------------------------------------------------------------- mod-p algebra

def _modp(x):
    if isinstance(x, F):
        assert x.denominator % P, 'denominator divisible by p'
        return x.numerator % P * pow(x.denominator % P, P - 2, P) % P
    return x % P


def rref_p(M):
    A = [[_modp(x) for x in row] for row in M]
    if not A:
        return A, []
    rows, cols = len(A), len(A[0])
    piv, r = [], 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if A[i][c]), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        inv = pow(A[r][c], P - 2, P)
        A[r] = [x * inv % P for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * b) % P for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return A, piv


def nullspace_p(M, cols):
    if not M:
        return [[int(i == j) for j in range(cols)] for i in range(cols)]
    R, piv = rref_p(M)
    ps = set(piv)
    out = []
    for fc in range(cols):
        if fc in ps:
            continue
        v = [0] * cols
        v[fc] = 1
        for ri, pc in enumerate(piv):
            v[pc] = -R[ri][fc] % P
        out.append(v)
    return out


# ---------------------------------------------------------------- the lifting space

def lifting_constraints(edges, V, q):
    """Rows `c` (indexed by V) with `sum_w c_w z_w = 0`: for each `v`, the left
    kernel of the `|N[v]| x 3` matrix `[1, x_w, y_w]`.  Asserts every closed
    neighbourhood of size >= 3 is non-collinear."""
    idx = {v: i for i, v in enumerate(V)}
    nb = neighbors(edges)
    rows = []
    for v in V:
        N = [v] + sorted(nb.get(v, ()), key=str)
        A = [[F(1), q[w][0], q[w][1]] for w in N]
        assert rank_exact(A) == min(3, len(N)), ('collinear closed nbhd', v)
        At = [list(col) for col in zip(*A)]
        for c in nullspace(At):
            r = [F(0)] * len(V)
            for w, cw in zip(N, c):
                r[idx[w]] += cw
            rows.append(r)
    return rows


def lifting_space(edges, V, q):
    """Exact basis of L(q), each vector integer-scaled."""
    rows = lifting_constraints(edges, V, q)
    B = nullspace(rows) if rows else [[F(int(i == j)) for j in range(len(V))]
                                      for i in range(len(V))]
    out = []
    for b in B:
        m = lcm(*[x.denominator for x in b])
        out.append([x * m for x in b])
    return out


def sample_q(rng, V, edges, S, tries=200):
    nb = neighbors(edges)
    for _ in range(tries):
        q = {v: (F(rng.randint(-S, S)), F(rng.randint(-S, S))) for v in V}
        if any(q[u] == q[w] for (u, w) in edges):
            continue
        ok = True
        for v in V:
            N = [v] + list(nb.get(v, ()))
            if len(N) >= 3 and rank_exact([[F(1), q[w][0], q[w][1]] for w in N]) < 3:
                ok = False
                break
        if ok:
            return q
    raise RuntimeError('no admissible planar picture q in %d tries' % tries)


# ---------------------------------------------------------------- augmented matrix

def aug_matrix(edges, V, pt):
    """Rows (e, k): (m_u - m_w - omega_e C_e)_k, columns 6|V| + |E|.  Its
    kernel is the motion space when every C_e != 0."""
    idx = {v: i for i, v in enumerate(V)}
    n, m = len(V), len(edges)
    rows = []
    for ei, (u, w) in enumerate(edges):
        C = wedge2(hat(pt[u]), hat(pt[w]))
        for k in range(6):
            r = [F(0)] * (6 * n + m)
            r[6 * idx[u] + k] += 1
            r[6 * idx[w] + k] -= 1
            r[6 * n + ei] = -C[k]
            rows.append(r)
    return rows


def _mat_add(A, B, a=1, b=1):
    return [[a * x + b * y for x, y in zip(r, s)] for r, s in zip(A, B)]


def check_affine(edges, V, q, L):
    """(MC-3): the augmented matrix is affine along the fibre L(q), exactly."""
    def pt_of(z):
        return {v: (q[v][0], q[v][1], z[i]) for i, v in enumerate(V)}
    z0 = [F(0)] * len(V)
    z1 = L[0] if L else z0
    z2 = L[-1] if L else z0
    zs = [a + b for a, b in zip(z1, z2)]
    zd = [2 * a for a in z1]
    A0 = aug_matrix(edges, V, pt_of(z0))
    A1 = aug_matrix(edges, V, pt_of(z1))
    A2 = aug_matrix(edges, V, pt_of(z2))
    As = aug_matrix(edges, V, pt_of(zs))
    Ad = aug_matrix(edges, V, pt_of(zd))
    assert As == _mat_add(_mat_add(A1, A2), A0, 1, -1), '(MC-3) additivity fails'
    assert Ad == _mat_add(A1, A0, 2, -1), '(MC-3) homogeneity fails'


# ---------------------------------------------------------------- first-order gain

def gain1(edges, V, q, zvec, L, dimL):
    """rank_p(S0^T A1(z) K0), and the same for the three trivial liftings
    (asserted 0).  Returns the gain in direction `zvec`."""
    def pt_of(z):
        return {v: (q[v][0], q[v][1], z[i]) for i, v in enumerate(V)}
    n, m = len(V), len(edges)
    cols = 6 * n + m
    A0 = aug_matrix(edges, V, pt_of([F(0)] * n))
    # (MC-4) in augmented form: rank_Q(A0) = m + 6n - 3 - dimL ; check mod p
    _, piv = rref_p(A0)
    assert len(piv) == m + 6 * n - 3 - dimL, 'mod-p rank of A0 != Q-rank'
    K0 = nullspace_p(A0, cols)
    A0T = [list(c) for c in zip(*A0)]
    S0 = nullspace_p(A0T, len(A0))

    def g(z):
        A = aug_matrix(edges, V, pt_of(z))
        A1 = [[_modp(x - y) for x, y in zip(r, s)] for r, s in zip(A, A0)]
        # only the omega columns of A1 are nonzero
        A1K = [[sum(A1[i][j] * k[j] for j in range(6 * n, cols)) % P
                for k in K0] for i in range(len(A1))]
        B = [[sum(s[i] * A1K[i][c] for i in range(len(A1)) if s[i]) % P
              for c in range(len(K0))] for s in S0]
        return len(rref_p(B)[1]) if B and B[0] else 0
    for triv in ([F(1)] * n, [q[v][0] for v in V], [q[v][1] for v in V]):
        assert g(triv) == 0, 'trivial lifting has first-order gain'
    return g(zvec)


# ---------------------------------------------------------------- one instance

def probe(edges, rng, S, want_gain=False, want_affine=False):
    V = verts_of(edges)
    n = len(V)
    q = sample_q(rng, V, edges, S)
    L = lifting_space(edges, V, q)
    dimL = len(L)
    coeff = [rng.randint(-S, S) for _ in L]
    zvec = [sum(c * b[i] for c, b in zip(coeff, L)) for i in range(n)]
    pt = {v: (q[v][0], q[v][1], zvec[i]) for i, v in enumerate(V)}
    ok, info = verify_pencil_witness(edges, pt)
    assert ok, ('(MC-1) forward direction fails', info)
    if want_affine:
        check_affine(edges, V, q, L)
    rows, _ = build_rigidity(edges, pt)
    rk = rank_modp(rows)
    flat = {v: (q[v][0], q[v][1], F(0)) for v in V}
    rows0, _ = build_rigidity(edges, flat)
    rk0 = rank_modp(rows0)
    assert rk0 == 6 * n - 3 - dimL, ('(MC-4) flat identity fails', rk0, dimL)
    out = {'rank': rk, 'flat': rk0, 'dimL': dimL, 'pt': pt, 'q': q}
    if want_gain:
        out['gain1'] = gain1(edges, V, q, zvec, L, dimL)
    return out


def census(name, edges, seed, draws=1, retry=4, S=30, want_gain=False,
           want_nondeg=True):
    V = verts_of(edges)
    n = len(V)
    d3 = def3_pebble(edges)
    d2 = def_k(edges, 3)
    tgt = 6 * (n - 1) - d3
    assert d3 <= d2, ('def3 > def2 at a connected graph', name)
    best = None
    tries = 0
    first = True
    for dr in range(draws + retry):
        if dr >= draws and best is not None and best['rank'] == tgt:
            break
        rng = random.Random(f'{seed}:{name}:{dr}')
        r = probe(edges, rng, S, want_gain=want_gain, want_affine=first)
        first = False
        tries += 1
        assert r['dimL'] >= 3 + d2, ('(MC-4) dim L < 3 + def2', name)
        assert r['flat'] <= 6 * (n - 1) - d2
        if r['rank'] < tgt:
            rows, _ = build_rigidity(edges, r['pt'])
            r['rank'] = rank_exact(rows)          # exact Q at a shortfall
        if best is None or r['rank'] > best['rank']:
            best = r
    res = {'name': name, 'n': n, 'm': len(edges), 'def2': d2, 'def3': d3,
           'target': tgt, 'rank': best['rank'], 'flat': best['flat'],
           'dimL': best['dimL'], 'JJ': best['dimL'] == 3 + d2,
           'attains': best['rank'] == tgt, 'draws': tries}
    if want_gain:
        res['gain1'] = best['gain1']
    if want_nondeg:
        # nondegeneracy is an open condition too: a degenerate drawn point is
        # redrawn (up to `retry` more attaining draws) before it is reported
        from flanks import nondeg_conjuncts
        ok, info = nondeg_conjuncts(edges, best['pt'])
        extra = 0
        while not ok and res['attains'] and extra < retry:
            rng = random.Random(f'{seed}:{name}:nd{extra}')
            r = probe(edges, rng, S)
            extra += 1
            if r['rank'] == tgt:
                ok, info = nondeg_conjuncts(edges, r['pt'])
        res['nondeg'] = 'yes' if ok else info[0].split(' ')[1]
    return res


def fmt(r):
    s = (f"{r['name']:<22} n={r['n']:>2} m={r['m']:>2} def2={r['def2']:>2} "
         f"def3={r['def3']:>2} dimL={r['dimL']:>2} JJ={'Y' if r['JJ'] else 'N'} "
         f"flat={r['flat']:>3} rank={r['rank']:>3}/{r['target']:<3} "
         f"{'ATTAINS' if r['attains'] else 'SHORT  '} draws={r['draws']}")
    if 'gain1' in r:
        s += f" gain1={r['gain1']}/{r['def2'] - r['def3']}"
    if 'nondeg' in r:
        s += f" nondeg={r['nondeg']}"
    if 'feas' in r:
        s += f" {r['feas']},{r['rig']}"
    return s


# ---------------------------------------------------------------- graph enumeration

def _refine(adj, cells):
    """Equitable refinement of an ordered partition; label-independent."""
    while True:
        where = {}
        for ci, c in enumerate(cells):
            for v in c:
                where[v] = ci
        new = []
        for ci, c in enumerate(cells):
            if len(c) == 1:
                new.append(c)
                continue
            sig = {}
            for v in c:
                key = tuple(sorted(where[w] for w in adj[v]))
                sig.setdefault(key, []).append(v)
            for key in sorted(sig):
                new.append(sig[key])
        if len(new) == len(cells):
            return new
        cells = new


def canon(n, edges):
    """Canonical code of a simple graph on range(n): the minimum adjacency
    code over the leaves of the individualization-refinement tree."""
    adj = {v: set() for v in range(n)}
    for u, w in edges:
        adj[u].add(w)
        adj[w].add(u)
    best = None

    def leaf(order):
        pos = {v: i for i, v in enumerate(order)}
        code = 0
        for u, w in edges:
            a, b = sorted((pos[u], pos[w]))
            code |= 1 << (b * (b - 1) // 2 + a)
        return code

    def rec(cells):
        nonlocal best
        cells = _refine(adj, cells)
        k = next((i for i, c in enumerate(cells) if len(c) > 1), None)
        if k is None:
            c = leaf([c[0] for c in cells])
            if best is None or c < best:
                best = c
            return
        for v in cells[k]:
            rest = [w for w in cells[k] if w != v]
            rec(cells[:k] + [[v], rest] + cells[k + 1:])
    rec([list(range(n))])
    return best


def decode(n, code):
    out = []
    for b in range(1, n):
        for a in range(b):
            if code >> (b * (b - 1) // 2 + a) & 1:
                out.append((a, b))
    return out


def connected_graphs(nmax):
    """{n: sorted list of canonical codes} of connected simple graphs, n <= nmax."""
    level = {1: [canon(1, [])]}
    for n in range(2, nmax + 1):
        seen = set()
        for code in level[n - 1]:
            E = decode(n - 1, code)
            for mask in range(1, 1 << (n - 1)):
                E2 = E + [(i, n - 1) for i in range(n - 1) if mask >> i & 1]
                seen.add(canon(n, E2))
        level[n] = sorted(seen)
    return level


def two_ec_graphs(nmax, nmin=3):
    lev = connected_graphs(nmax)
    out = []
    for n in range(nmin, nmax + 1):
        for code in lev[n]:
            E = decode(n, code)
            if is_2ec(E):
                out.append((f'x{n}_{code}', E))
    return out


# ---------------------------------------------------------------- populations

def battery():
    from pitch import theta_edges
    from widened import W19
    from pencil_escape import K4
    C = lambda k: [(i, (i + 1) % k) for i in range(k)]          # noqa: E731
    K33 = [(a, b) for a in range(3) for b in range(3, 6)]
    return [('C4', C(4)), ('C5', C(5)), ('C7', C(7)), ('K4', K4()), ('K33', K33),
            ('theta222', theta_edges([2, 2, 2])), ('theta345', theta_edges([3, 4, 5])),
            ('theta534', theta_edges([5, 3, 4])), ('W19', W19())]


def thetas(smax=16):
    """theta(a, b, c), 1 <= a <= b <= c, b >= 2 (simple), a + b + c <= smax."""
    from pitch import theta_edges
    out = []
    for a in range(1, smax):
        for b in range(max(a, 2), smax):
            for c in range(b, smax - a - b + 1):
                out.append((f'theta{a}.{b}.{c}', theta_edges([a, b, c])))
    return out


def habitats():
    """The kernel-(K) class shapes: lambda.habitat_specs (theta(3,4,5), NT21,
    NT24, NT30), kslidecl.MEMBERS, and the exhaustive G* = K4 stratum of
    `kslidecomb.py --k4full` (every length assignment in {1..5}^6, sum 18,
    passing `shape_ok`)."""
    import importlib
    import itertools
    lam = importlib.import_module('lambda')
    from kslidecl import MEMBERS
    from kslide import member
    from kslidecomb import relabel, shape_ok, shape_data
    out = [(nm, E) for (nm, E, _v, _c) in lam.habitat_specs()]
    for key, (nm, specs) in sorted(MEMBERS.items()):
        out.append((f'member:{key}', member(specs)[0]))
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
        if sum(lens) != 18 or 3 not in lens:
            continue
        specs = relabel(4, K4, lens, lens.index(3))
        if shape_ok(specs) is None:
            continue
        out.append(('k4:' + ''.join(map(str, lens)), shape_data(specs)[0]))
    return out


def _smark_drivers():
    here = os.path.dirname(os.path.abspath(__file__))
    d = os.path.join(os.path.dirname(os.path.dirname(here)), 'attacks', 'smark', 'drivers')
    if d not in sys.path:
        sys.path.insert(0, d)


def smark():
    """G = side + ear_m, m in {2, 3, 4}, over the 27 sides of smark's
    `splitoff.py --sides all` (sideprof ORDER + ORDER2 + adversarial SIDES),
    imported READ-ONLY from `notes/attacks/smark/drivers/`; the ear is
    `earcompose.ear_edges` (m interior vertices).  Kept iff simple and 2EC."""
    _smark_drivers()
    import sideprof as SP
    import adversarial as ADV
    from earcompose import ear_edges
    names = SP.ORDER + SP.ORDER2 + list(ADV.SIDES)
    out = []
    for nm in names:
        side = SP.SIDES[nm]() if nm in SP.SIDES else ADV.SIDES[nm]()
        for m in (2, 3, 4):
            out.append((f'{nm}+ear{m}', side + ear_edges(m)))
    return out


def residuals():
    """The 255 recorded residual inhabitants (`wtri.recorded_pool()`, the
    (RS-12) pool) and the named witnesses W19, R20, S29, T32, NT21c3."""
    from wtri import recorded_pool
    from widened import W19
    from rpool import R20
    from saferes import w29
    from weloc import T32
    from dominance import nt21c3
    out = [(f'pool{i:03d}', E) for i, E in enumerate(recorded_pool())]
    out += [('W19', W19()), ('R20', R20()), ('S29', w29()), ('T32', T32),
            ('NT21c3', nt21c3()[0])]
    return out


def peels():
    """The 928 members `G = H1 + H2` of `bgenuine.family()` (K4 R-sides glued
    to free sides at {u, v}); a name ends in `:forced` iff
    `bgenuine.forced_seed(G)` is not None (392 expected, asserted)."""
    from bgenuine import family, forced_seed
    out = []
    nf = 0
    for i, (n1, n2, _L, H1, H2) in enumerate(family()):
        G = H1 + H2
        f = forced_seed(G) is not None
        nf += f
        out.append((f'peel{i:03d}.{n1}.{n2}' + (':forced' if f else ''), G))
    assert len(out) == 928 and nf == 392, (len(out), nf)
    return out


def exh8():
    return two_ec_graphs(8)


POOLS = {'battery': battery, 'thetas': thetas, 'habitats': habitats,
         'smark': smark, 'residuals': residuals, 'peels': peels, 'exh8': exh8}


def classify(E):
    """Feasibility certificate (landed-sufficient / landed-necessary proxies of
    `nogood_subdiv`) and whether a proper rigid subgraph exists."""
    from nogood_subdiv import provably_feasible, provably_infeasible, rigid_vertex_sets
    if provably_feasible(E):
        feas = 'feas'
    elif provably_infeasible(E):
        feas = 'infeas'
    else:
        feas = 'middle'
    try:
        rig = 'rigid' if rigid_vertex_sets(E) else 'norigid'
    except AssertionError:
        rig = 'rigid?'
    return feas, rig


def run(pop, a):
    from nogood_subdiv import is_simple
    t0 = time.time()
    rows = []
    dropped = 0
    for name, E in pop:
        if not (is_simple(E) and is_2ec(E)):
            dropped += 1
            continue
        r = census(name, E, a.seed, draws=a.draws, retry=a.retry, S=a.scale,
                   want_gain=a.gain, want_nondeg=not a.no_nondeg)
        r['feas'], r['rig'] = classify(E)
        rows.append(r)
        if a.verbose or not r['attains']:
            print(fmt(r), flush=True)
    if dropped:
        print(f'   ({dropped} members dropped: not simple or not 2EC)')
    return rows, time.time() - t0


def summary(rows, label):
    tot = len(rows)
    gap = [r for r in rows if r['def2'] > r['def3']]
    short = [r for r in rows if not r['attains']]
    jj = [r for r in rows if not r['JJ']]
    print(f'== {label}: {tot} graphs; def2 > def3 at {len(gap)}; '
          f'X0 ATTAINS at {tot - len(short)}/{tot}; SHORT at {len(short)}; '
          f'JJ fails at the drawn q at {len(jj)}')
    if rows and 'gain1' in rows[0]:
        full = sum(1 for r in gap if r['gain1'] == r['def2'] - r['def3'])
        print(f'   first-order gain reaches def2 - def3 at {full}/{len(gap)} of the gap graphs')
    from collections import Counter
    if rows and 'nondeg' in rows[0]:
        c = Counter(r['nondeg'] for r in rows)
        print('   nondeg at the drawn X0 point: ' +
              ', '.join(f'{k} {v}' for k, v in sorted(c.items())))
        ap = [r for r in rows if r['feas'] == 'feas' and r['attains'] and r['nondeg'] != 'yes']
        print(f'   A-prime watch (certified-feasible, attains, drawn point degenerate): {len(ap)}')
        for r in ap[:20]:
            print('     ' + fmt(r))
    if rows and 'feas' in rows[0]:
        c = Counter((r['feas'], r['rig']) for r in rows)
        cg = Counter((r['feas'], r['rig']) for r in gap)
        print('   classes (feas/infeas/middle x rigid/norigid): ' +
              ', '.join(f'{k[0]},{k[1]} {v} (gap {cg.get(k, 0)})' for k, v in sorted(c.items())))
        b2 = [r for r in gap if r['feas'] == 'infeas' and r['rig'] == 'rigid']
        print(f'   W4 branch 2 (certified infeasible, proper rigid subgraph) with def2 > def3: '
              f'{len(b2)}; X0 SHORT among them: {sum(not r["attains"] for r in b2)}')
        for r in b2[:a_list]:
            print('     ' + fmt(r))


a_list = 0


def selftest():
    # oracles: def3 pebble vs partition max; def2 pebble vs brute force
    pop = battery() + two_ec_graphs(6)
    for name, E in pop:
        if len(verts_of(E)) <= 8:
            assert def_k(E, 3) == def_brute(E, 3), ('def2 oracle', name)
            assert def_k(E, 6) == def_brute(E, 6) == def3_pebble(E), ('def3 oracle', name)
        if len(verts_of(E)) <= 12:
            assert exact_deficiency(E)[0] == def3_pebble(E), ('def3 exact', name)
    # enumeration counts: OEIS A001349 (connected graphs) and A007146
    # (connected bridgeless graphs), n = 1..8
    lev = connected_graphs(8)
    counts = [len(lev[n]) for n in range(1, 9)]
    assert counts == [1, 1, 2, 6, 21, 112, 853, 11117], counts
    c2 = [sum(1 for code in lev[n] if is_2ec(decode(n, code))) for n in range(3, 9)]
    assert c2 == [1, 3, 11, 60, 502, 7403], c2
    print(f'selftest: oracles agree on {len(pop)} graphs; connected-graph counts '
          f'{counts} = OEIS A001349; 2EC counts (n = 3..8) {c2} = OEIS A007146; PASS')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--battery', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--pool', default=None)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--seed', type=int, default=20260923)
    ap.add_argument('--draws', type=int, default=1)
    ap.add_argument('--retry', type=int, default=4)
    ap.add_argument('--scale', type=int, default=30)
    ap.add_argument('--gain', action='store_true')
    ap.add_argument('--no-nondeg', action='store_true')
    ap.add_argument('--verbose', '-v', action='store_true')
    ap.add_argument('--list-b2', type=int, default=0,
                    help='print up to N W4-branch-2 gap members in the summary')
    a = ap.parse_args()
    global a_list
    a_list = a.list_b2
    if a.list:
        print('pools:', ', '.join(sorted(POOLS)))
        return
    if a.selftest:
        selftest()
        return
    print(f'maincomp: seed={a.seed} draws={a.draws} retry={a.retry} scale={a.scale} '
          f'gain={a.gain}')
    if a.battery:
        a.verbose = True
        rows, dt = run(battery(), a)
        summary(rows, 'battery')
    if a.exh:
        pop = two_ec_graphs(a.exh)
        rows, dt = run(pop, a)
        for n in range(3, a.exh + 1):
            summary([r for r in rows if r['n'] == n], f'exhaustive 2EC n={n}')
        summary(rows, f'exhaustive 2EC n<={a.exh}')
    if a.pool:
        for nm in a.pool.split(','):
            t0 = time.time()
            pop = POOLS[nm]()
            print(f'-- pool {nm}: {len(pop)} members, built in {time.time() - t0:.0f} s')
            rows, dt = run(pop, a)
            if nm == 'exh8':
                for n in range(3, 9):
                    summary([r for r in rows if r['n'] == n], f'exhaustive 2EC n={n}')
            summary(rows, f'pool {nm}')


if __name__ == '__main__':
    main()
