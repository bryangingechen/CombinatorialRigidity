#!/usr/bin/env python3
"""
jjbuild.py -- (§(K-main) Jackson--Jordan over any infinite field, the 2026-09-25 write-up, staged in
notes/w4-pending/; ported from the writer's scratch) the constructions in the proof of Jackson--Jordan's Thm 6.1
(TR-2006-06, pp.14-20), run exactly over finite fields of characteristic 2, 3
and 10007, in the field-general form written up as (NEW-I1)-(NEW-I27).

Claim exercised.  Each construction of the proof takes a GENERIC
non-degenerate pin-collinear body-and-pin realization of a smaller graph (the
pin-lines drawn at random, then checked against the open conditions (a) no two
pin-lines parallel and (b) no three concurrent) and outputs a pin-collinear
body-and-pin realization of G.  At every instance and field the driver asserts:
  * every intermediate rank step the proof claims (0-extension +2,
    1-extension +2, vertex split >= +2, the single bar of Claim 6.8 +1, the
    cut-and-glue identity of Lemma 2.7, the rank of the moved configuration
    after the Zariski move replacing each epsilon-move);
  * the OUTPUT is a body-and-pin realization (pins of each body distinct and
    on its pin-line, body point off the line), NON-DEGENERATE (adjacent bodies
    have distinct pin-lines: the invariant of bypass R2), and has
    rank r(G*, q) = t(G) = 2(|V| + |E|) - 3 - def(G);
  * Lemma 5.1 in rank form at every realization: r(G*, q) = 2|E| - |V| +
    rank R_BP(G, q|_E).
Every free parameter of a Zariski move is drawn uniformly; a draw that hits an
excluded value is redrawn and COUNTED (the count is printed).  A rank failure
at a drawn parameter is counted separately and must be 0.

Deficiency: two oracles, asserted equal -- a subset DP over set partitions
(this file) and `maincomp.def_k(edges, 3)` (a count-matroid rank).

Fields: `--fields`, default `2^16,3^10,10007` (jjchar's constructors, which
assert primitivity and check their tables).

Modes (run from the repository root; seeded, seed 20260925; writes nothing):
    python3 jjbuild.py --selftest     the guards and their adversarial witnesses,
                                      and Lemmas 3.2/3.3 at a seeded battery
    python3 jjbuild.py --run          every construction at every instance
"""
import argparse
import itertools
import os
import random
import sys

# Path bootstrap: the canonical idiom of notes/scripts/README.md section 0.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from jjchar import make_field  # noqa: E402
from maincomp import def_k  # noqa: E402

SEED = 20260925


# ---------------------------------------------------------------- arithmetic

class Ar:
    """Field arithmetic over one of jjchar's field objects (0 and 1 are the
    zero and one in every encoding)."""

    def __init__(self, Fd):
        self.F = Fd
        self.name = Fd.name
        if hasattr(Fd, 'add'):                          # GF(p^k), p odd
            self.add, self.mul, self.inv, self.neg = Fd.add, Fd.mul, Fd.inv, Fd.neg
        elif Fd.char == 2:                              # GF(2^k)
            self.add = lambda a, b: a ^ b
            self.mul, self.inv = Fd.mul, Fd.inv
            self.neg = lambda a: a
        else:                                           # GF(p)
            p = Fd.p
            self.add = lambda a, b: (a + b) % p
            self.mul = lambda a, b: a * b % p
            self.inv = lambda a: pow(a, p - 2, p)
            self.neg = lambda a: (-a) % p

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def div(self, a, b):
        assert b != 0, 'division by zero'
        return self.mul(a, self.inv(b))

    def rand(self, rng):
        return self.F.rand(rng)

    def rank(self, rows):
        return self.F.rank(rows) if rows else 0


# ---------------------------------------------------------------- geometry
# Points (x, y).  Lines (a, b, c): the set a x + b y + c = 0, (a, b) != 0.

def cross3(A, u, v):
    return (A.sub(A.mul(u[1], v[2]), A.mul(u[2], v[1])),
            A.sub(A.mul(u[2], v[0]), A.mul(u[0], v[2])),
            A.sub(A.mul(u[0], v[1]), A.mul(u[1], v[0])))


def det2(A, u, v):
    return A.sub(A.mul(u[0], v[1]), A.mul(u[1], v[0]))


def det3(A, u, v, w):
    c = cross3(A, v, w)
    return A.add(A.add(A.mul(u[0], c[0]), A.mul(u[1], c[1])), A.mul(u[2], c[2]))


def line_through(A, P, Q):
    assert P != Q, 'line through two equal points'
    return cross3(A, (P[0], P[1], 1), (Q[0], Q[1], 1))


def meet(A, L, M):
    X, Y, W = cross3(A, L, M)
    if W == 0:
        return None                                    # parallel (or equal)
    return (A.div(X, W), A.div(Y, W))


def on(A, P, L):
    return A.add(A.add(A.mul(L[0], P[0]), A.mul(L[1], P[1])), L[2]) == 0


def same(A, L, M):
    return cross3(A, L, M) == (0, 0, 0)


def parallel(A, L, M):
    return det2(A, L, M) == 0


def direction(A, L):
    return (L[1], A.neg(L[0]))


def line_dir(A, P, d):
    """The line through P with direction d != 0."""
    a, b = d[1], A.neg(d[0])
    return (a, b, A.neg(A.add(A.mul(a, P[0]), A.mul(b, P[1]))))


def point_on(A, L, s):
    if L[1] != 0:
        base = (0, A.neg(A.div(L[2], L[1])))
    else:
        base = (A.neg(A.div(L[2], L[0])), 0)
    d = direction(A, L)
    return (A.add(base[0], A.mul(s, d[0])), A.add(base[1], A.mul(s, d[1])))


def rand_point(A, rng):
    return (A.rand(rng), A.rand(rng))


def rand_line(A, rng):
    while True:
        L = (A.rand(rng), A.rand(rng), A.rand(rng))
        if L[0] or L[1]:
            return L


# ---------------------------------------------------------------- graphs

def ed(a, b):
    return (a, b) if str(a) <= str(b) else (b, a)


def inc(E, v):
    return [e for e in E if v in e]


def other(e, v):
    return e[1] if e[0] == v else e[0]


def deficiency(V, E):
    """max over set partitions P of 3(|P| - 1) - 2 e(P), by a subset DP."""
    n = len(V)
    if n <= 1:
        return 0
    ix = {v: i for i, v in enumerate(V)}
    emask = [(1 << ix[a]) | (1 << ix[b]) for a, b in E]
    full = (1 << n) - 1
    f = [0] * (full + 1)
    for m in range(1, full + 1):
        f[m] = 3 + 2 * sum(1 for em in emask if em & m == em)
    best = [0] * (full + 1)
    for m in range(1, full + 1):
        low = m & -m
        rest = m ^ low
        b = None
        sub = rest
        while True:
            A_ = sub | low
            val = f[A_] + best[m ^ A_]
            if b is None or val > b:
                b = val
            if sub == 0:
                break
            sub = (sub - 1) & rest
        best[m] = b
    return best[full] - 3 - 2 * len(E)


def deficiency2(V, E):
    """Second oracle: maincomp.def_k(edges, 3) = max_P 3(|P|-1) - 2 d(P)."""
    return def_k(E, 3, verts=list(V)) if E else 3 * (len(V) - 1)


def dfc(V, E):
    d1 = deficiency(V, E)
    if len(V) >= 2 and all(any(v in e for e in E) for v in V):
        d2 = deficiency2(V, E)
        assert d1 == d2, ('deficiency oracles disagree', V, E, d1, d2)
    return d1


def target(V, E):
    return 2 * (len(V) + len(E)) - 3 - dfc(V, E)


def induced(V, E, S):
    S = set(S)
    return [v for v in V if v in S], [e for e in E if e[0] in S and e[1] in S]


def star_graph(V, E):
    """The body-and-pin graph G*: vertices ('v', v), ('p', e)."""
    SV = [('v', v) for v in V] + [('p', e) for e in E]
    SE = []
    for v in V:
        pins = inc(E, v)
        for e in pins:
            SE.append((('v', v), ('p', e)))
        for e, f in itertools.combinations(pins, 2):
            SE.append((('p', e), ('p', f)))
    return SV, SE


# ---------------------------------------------------------------- rigidity

def rig_rank(A, SV, SE, pos):
    ix = {x: i for i, x in enumerate(SV)}
    rows = []
    for a, b in SE:
        r = [0] * (2 * len(SV))
        dx, dy = A.sub(pos[a][0], pos[b][0]), A.sub(pos[a][1], pos[b][1])
        r[2 * ix[a]], r[2 * ix[a] + 1] = dx, dy
        r[2 * ix[b]], r[2 * ix[b] + 1] = A.neg(dx), A.neg(dy)
        rows.append(r)
    return A.rank(rows)


def bp_rank(A, V, E, pos):
    """rank R_BP(G, q|_E): rows Q(e) = (1, 0, -x_e), R(e) = (0, 1, y_e) (TR p.10)."""
    ix = {v: i for i, v in enumerate(V)}
    rows = []
    for e in E:
        x, y = pos[('p', e)]
        for vec in ((1, 0, A.neg(x)), (0, 1, y)):
            r = [0] * (3 * len(V))
            for k in range(3):
                r[3 * ix[e[0]] + k] = vec[k]
                r[3 * ix[e[1]] + k] = A.neg(vec[k])
            rows.append(r)
    return A.rank(rows)


def star_rank(A, V, E, pos):
    SV, SE = star_graph(V, E)
    return rig_rank(A, SV, SE, pos)


# ---------------------------------------------------------------- realizations

def is_bp(A, V, E, pos, L):
    """A pin-collinear body-and-pin realization (the R0 form: the pin-line of
    a degree-1 body is a datum through its pin)."""
    for v in V:
        pins = [pos[('p', e)] for e in inc(E, v)]
        if not pins or len(set(pins)) != len(pins):
            return False
        if any(not on(A, P, L[v]) for P in pins):
            return False
        if on(A, pos[('v', v)], L[v]):
            return False
    return True


def is_nondeg(A, E, L):
    return all(not same(A, L[a], L[b]) for a, b in E)


def lines_generic(A, V, L):
    """(a) no two pin-lines parallel (or equal); (b) no three concurrent."""
    for u, v in itertools.combinations(V, 2):
        if parallel(A, L[u], L[v]):
            return False
    for u, v, w in itertools.combinations(V, 3):
        if det3(A, L[u], L[v], L[w]) == 0:
            return False
    return True


def gen_real(A, V, E, rng, body_ok=None):
    """A realization built on random pin-lines satisfying (a), (b).  body_ok,
    if given, is an extra open condition on the body points."""
    while True:
        L = {v: rand_line(A, rng) for v in V}
        if lines_generic(A, V, L):
            break
    pos = {}
    for e in E:
        pos[('p', e)] = meet(A, L[e[0]], L[e[1]])
    while True:
        for v in V:
            while True:
                P = rand_point(A, rng)
                if not on(A, P, L[v]):
                    break
            pos[('v', v)] = P
        if body_ok is None or body_ok(pos, L):
            break
    assert is_bp(A, V, E, pos, L) and is_nondeg(A, E, L)
    return pos, L


class Log:
    def __init__(self):
        self.redraw = 0          # draws hitting an excluded value
        self.rankfail = 0        # draws failing the rank condition (must stay 0)
        self.steps = []

    def step(self, what, got, want, op='=='):
        ok = {'==': got == want, '>=': got >= want}[op]
        self.steps.append(f'{what} {got} {op} {want}')
        assert ok, ('rank step fails', what, got, op, want)


def finish(A, V, E, pos, L, log, name):
    SV, SE = star_graph(V, E)
    assert set(pos) >= set(SV), 'positions missing'
    assert is_bp(A, V, E, pos, L), f'{name}: output is not a pin-collinear body-and-pin realization'
    assert is_nondeg(A, E, L), f'{name}: output is DEGENERATE (R2 violated)'
    r = rig_rank(A, SV, SE, pos)
    t = target(V, E)
    assert r == 2 * len(E) - len(V) + bp_rank(A, V, E, pos), 'Lemma 5.1 in rank form fails'
    log.step('r(G*) vs t(G)', r, t)
    return r, t


def check_generic(A, V, E, rng):
    """Corollary: a realization built on generic pin-lines has rank t."""
    pos, L = gen_real(A, V, E, rng)
    r = star_rank(A, V, E, pos)
    assert r == 2 * len(E) - len(V) + bp_rank(A, V, E, pos), 'Lemma 5.1 in rank form fails'
    return pos, L, r


def draw_until(rng, draw, conds, log, cap=500):
    for _ in range(cap):
        x = draw()
        if all(c(x) for c in conds):
            return x
        log.redraw += 1
    raise AssertionError('no admissible draw within cap')


# ---------------------------------------------------------------- constructions

def c_base(A, V, E, rng, log):
    """K2 and K3 directly."""
    if len(V) == 2:
        (e,) = E
        u, v = e
        X = rand_point(A, rng)
        Lu = line_dir(A, X, (1, A.rand(rng)))
        Lv = draw_until(rng, lambda: line_dir(A, X, (1, A.rand(rng))), [lambda M: not same(A, M, Lu)], log)
        pu = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, Lu)], log)
        pv = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, Lv)], log)
        pos = {('p', e): X, ('v', u): pu, ('v', v): pv}
        return pos, {u: Lu, v: Lv}
    pos, L = gen_real(A, V, E, rng)                     # K3: three lines in general position
    return pos, L


def c62(A, V, E, parts, rng, log):
    """Disjoint union (Claim 6.2)."""
    pos, L = {}, {}
    for S in parts:
        Vi, Ei = induced(V, E, S)
        p, l, r = check_generic(A, Vi, Ei, rng)
        log.step(f'r(G_{len(Vi)}*)', r, target(Vi, Ei))
        pos.update(p)
        L.update(l)
    return pos, L


def c63(A, V, E, v1, rng, log):
    """Degree-1 vertex (Claim 6.3)."""
    (p1,) = inc(E, v1)
    u1 = other(p1, v1)
    V1 = [v for v in V if v != v1]
    E1 = [e for e in E if e != p1]
    pos, L, r1 = check_generic(A, V1, E1, rng)
    log.step('r(G1*) = t(G1)', r1, target(V1, E1))
    pins = [pos[('p', e)] for e in inc(E1, u1)]
    p2 = inc(E1, u1)[0]
    Q1 = draw_until(rng, lambda: point_on(A, L[u1], A.rand(rng)), [lambda P: P not in pins], log)
    Q2 = draw_until(rng, lambda: rand_point(A, rng), [lambda P: P != Q1], log)
    Lv1 = draw_until(rng, lambda: line_dir(A, Q1, (1, A.rand(rng))),
                     [lambda M: not same(A, M, L[u1]), lambda M: not on(A, Q2, M)], log)
    pos[('p', p1)] = Q1
    pos[('v', v1)] = Q2
    L[v1] = Lv1
    SV1, SE1 = star_graph(V1, E1)
    H = (SV1 + [('p', p1)], SE1 + [(('p', p1), ('v', u1)), (('p', p1), ('p', p2))])
    log.step('0-ext p1', rig_rank(A, H[0], H[1], pos), r1 + 2)
    H = (H[0] + [('v', v1)], H[1] + [(('v', v1), ('p', p1))])
    log.step('pendant v1', rig_rank(A, H[0], H[1], pos), r1 + 3)
    return pos, L


def c64(A, V, E, p0, rng, log):
    """Bridge (Claim 6.4)."""
    u1, u2 = p0
    E0 = [e for e in E if e != p0]
    pos, L, r0 = check_generic(A, V, E0, rng)
    log.step('r(G0*) = t(G0)', r0, target(V, E0))
    Q = meet(A, L[u1], L[u2])
    assert Q not in [pos[('p', e)] for e in inc(E0, u1) + inc(E0, u2)], '(b) should exclude this'
    pos[('p', p0)] = Q
    return pos, L


def c65_same(A, V, E, v1, rng, log):
    """Degree 2, both neighbours in one brick of G - v1 (Claim 6.5, first case)."""
    p1, p2 = inc(E, v1)
    u1, u2 = other(p1, v1), other(p2, v1)
    V1 = [v for v in V if v != v1]
    E1 = [e for e in E if v1 not in e]
    pos, L, r1 = check_generic(A, V1, E1, rng)
    log.step('r(G1*) = t(G1)', r1, target(V1, E1))
    X12 = meet(A, L[u1], L[u2])
    Qs = []
    for u in (u1, u2):
        pins = [pos[('p', e)] for e in inc(E1, u)]
        Qs.append(draw_until(rng, lambda: point_on(A, L[u], A.rand(rng)),
                             [lambda P: P not in pins, lambda P: P != X12], log))
    Q1, Q2 = Qs
    Lv1 = line_through(A, Q1, Q2)
    Q = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, Lv1)], log)
    pos[('p', p1)], pos[('p', p2)], pos[('v', v1)] = Q1, Q2, Q
    L[v1] = Lv1
    SV, SE = star_graph(V1, E1)
    SV = SV + [('p', p1)]
    SE = SE + [(('p', p1), ('v', u1)), (('p', p1), ('p', inc(E1, u1)[0]))]
    log.step('0-ext p1', rig_rank(A, SV, SE, pos), r1 + 2)
    SV = SV + [('p', p2)]
    SE = SE + [(('p', p2), ('v', u2)), (('p', p2), ('p', inc(E1, u2)[0]))]
    log.step('0-ext p2', rig_rank(A, SV, SE, pos), r1 + 4)
    SV = SV + [('v', v1)]
    SE = SE + [(('v', v1), ('p', p1)), (('v', v1), ('p', p2))]
    log.step('0-ext v1', rig_rank(A, SV, SE, pos), r1 + 6)
    return pos, L


def c65_case1(A, V, E, v1, rng, log):
    """Degree 2, u1u2 not an edge, distinct bricks (Claim 6.5 Case 1)."""
    pa, pb = inc(E, v1)
    u1, u2 = other(pa, v1), other(pb, v1)
    assert ed(u1, u2) not in E
    V1 = [v for v in V if v != v1]
    E1 = [e for e in E if v1 not in e]
    p0 = ed(u1, u2)
    E2 = E1 + [p0]
    t1, t2 = target(V1, E1), target(V1, E2)
    assert t2 >= t1 + 3, 'Case 1 deficiency inequality def(G2) <= def(G1) - 1 fails'

    def body_ok(pos, L):
        X = meet(A, L[u1], L[u2])
        a, b = pos[('v', u1)], pos[('v', u2)]
        return (not on(A, b, L[u1]) and not on(A, a, L[u2])
                and det2(A, (A.sub(a[0], X[0]), A.sub(a[1], X[1])), (A.sub(b[0], X[0]), A.sub(b[1], X[1]))) != 0)
    pos, L = gen_real(A, V1, E2, rng, body_ok)
    r1 = star_rank(A, V1, E1, pos)
    r2 = star_rank(A, V1, E2, pos)
    log.step('r(G1*) = t(G1) (restriction)', r1, t1)
    log.step('r(G2*) = t(G2)', r2, t2)
    SV1, SE1 = star_graph(V1, E1)
    P0 = ('p', p0)

    def H2(p4, at):
        ps = dict(pos)
        ps[P0] = at
        return rig_rank(A, SV1 + [P0], SE1 + [(P0, ('v', u1)), (P0, ('v', u2)), (P0, ('p', p4))], ps)
    X = pos[P0]
    cands = inc(E1, u1) + inc(E1, u2)
    p4 = next(p for p in cands if H2(p, X) == r1 + 3)
    if p4 not in inc(E1, u1):
        u1, u2 = u2, u1
        pa, pb = pb, pa
    log.step('H2 = G1* + p0u1 + p0u2 + p0p4', H2(p4, X), r1 + 3)
    qu2 = pos[('v', u2)]
    p3 = inc(E1, u2)[0]
    pins1 = [pos[('p', e)] for e in inc(E1, u1)]
    pins2 = [pos[('p', e)] for e in inc(E1, u2)]
    d1 = direction(A, L[u1])

    def draw():
        s = A.rand(rng)
        return (A.add(X[0], A.mul(s, d1[0])), A.add(X[1], A.mul(s, d1[1])))

    def Q2of(Q1):
        return meet(A, line_through(A, Q1, qu2), L[u2])
    conds = [lambda Q1: Q1 != X,
             lambda Q1: Q1 not in pins1,
             lambda Q1: not parallel(A, line_through(A, Q1, qu2), L[u2]),
             lambda Q1: not on(A, pos[('p', p3)], line_through(A, Q1, qu2)),
             lambda Q1: Q2of(Q1) not in pins2]
    while True:
        Q1 = draw_until(rng, draw, conds, log)
        if H2(p4, Q1) >= r1 + 3:
            break
        log.rankfail += 1
    log.step('H2 after the move of p0 along L(u1)', H2(p4, Q1), r1 + 3, '>=')
    L0 = line_through(A, Q1, qu2)
    Q2 = Q2of(Q1)
    Q0 = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, L0)], log)
    P1, P2 = ('p', pa), ('p', pb)
    pos.pop(P0)
    pos[P1], pos[P2], pos[('v', v1)] = Q1, Q2, Q0
    L[v1] = L0
    SV = SV1 + [P1]
    SE = SE1 + [(P1, ('v', u1)), (P1, ('p', p4))]
    SV2 = SV + [P2]
    SE2 = SE + [(P2, P1), (P2, ('v', u2)), (P2, ('p', p3))]
    log.step('1-ext p2', rig_rank(A, SV2, SE2, pos), r1 + 5, '>=')
    SV2 = SV2 + [('v', v1)]
    SE2 = SE2 + [(('v', v1), P1), (('v', v1), P2)]
    log.step('0-ext v1', rig_rank(A, SV2, SE2, pos), r1 + 7, '>=')
    return pos, L


def c65_case2(A, V, E, v1, rng, log):
    """Degree 2, u1u2 an edge, d(u1), d(u2) >= 3 (Claim 6.5 Case 2): the
    flagged step, with the pencil parameter theta and the auxiliary line M."""
    pa, pb = inc(E, v1)
    u1, u2 = other(pa, v1), other(pb, v1)
    p3 = ed(u1, u2)
    assert p3 in E
    V1 = [v for v in V if v != v1]
    E1 = [e for e in E if v1 not in e]
    Wa = [other(e, u1) for e in inc(E1, u1) if e != p3]     # w_4 .. w_j
    Wb = [other(e, u2) for e in inc(E1, u2) if e != p3]     # w_{j+1} .. w_k
    assert Wa and Wb and not set(Wa) & set(Wb), 'u1, u2 have a common neighbour: G3 not simple'
    z = 'z#'
    V3 = [v for v in V1 if v not in (u1, u2)] + [z]
    E3 = [e for e in E1 if u1 not in e and u2 not in e] + [ed(z, w) for w in Wa + Wb]
    assert dfc(V3, E3) <= dfc(V1, E1) - 1, 'def(G3) <= def(G1) - 1 fails'
    pos3, L3, r3 = check_generic(A, V3, E3, rng)
    log.step('r(G3*) = t(G3)', r3, target(V3, E3))
    Lz = L3[z]
    qz = pos3[('v', z)]
    zp = {w: ('p', ed(z, w)) for w in Wa + Wb}
    SV3, SE3 = star_graph(V3, E3)
    s4, sj1 = zp[Wa[0]], zp[Wb[0]]
    S = {frozenset((zp[a], zp[b])) for a in Wa for b in Wb} - {frozenset((s4, sj1))}
    SE0 = [e for e in SE3 if frozenset(e) not in S]
    log.step('H0 = G3* - S', rig_rank(A, SV3, SE0, pos3), r3)
    zpins = [pos3[zp[w]] for w in Wa + Wb]
    Q1 = draw_until(rng, lambda: point_on(A, Lz, A.rand(rng)), [lambda P: P not in zpins], log)
    Q3 = draw_until(rng, lambda: point_on(A, Lz, A.rand(rng)), [lambda P: P not in zpins, lambda P: P != Q1], log)
    P1, P3 = ('p', pa), ('p', p3)
    pos4 = dict(pos3)
    pos4[P1], pos4[P3] = Q1, Q3
    SV1_ = SV3 + [P1, P3]
    SE1_ = [e for e in SE0 if frozenset(e) != frozenset((s4, sj1))]
    SE1_ += [(P1, P3), (P1, s4), (P1, ('v', z)), (P3, sj1), (P3, ('v', z))]
    rH1 = rig_rank(A, SV1_, SE1_, pos4)
    log.step('H1 (two 1-extensions)', rH1, r3 + 4)
    # vertex split of z into u1 (P1, P3, Wa-pins) and u2 (P1, P3, Wb-pins); rename pins to G's names
    ren = {('v', z): None}
    for w in Wa:
        ren[zp[w]] = ('p', ed(u1, w))
    for w in Wb:
        ren[zp[w]] = ('p', ed(u2, w))

    def R(x):
        return ren.get(x, x)
    U1, U2 = ('v', u1), ('v', u2)
    SV2 = [R(x) for x in SV1_ if x != ('v', z)] + [U1, U2]
    SE2 = [(R(a), R(b)) for a, b in SE1_ if ('v', z) not in (a, b)]
    SE2 += [(U1, x) for x in [P1, P3] + [ren[zp[w]] for w in Wa]]
    SE2 += [(U2, x) for x in [P1, P3] + [ren[zp[w]] for w in Wb]]
    pos5 = {R(x): p for x, p in pos4.items() if x != ('v', z)}
    pos5[U1] = pos5[U2] = qz
    rH2 = rig_rank(A, SV2, SE2, pos5)
    log.step('H2 (vertex split)', rH2, rH1 + 2, '>=')
    # the auxiliary line M through Q1
    M = None
    while M is None:
        d = (A.rand(rng), A.rand(rng))
        if d == (0, 0):
            continue
        Mc = line_dir(A, Q1, d)
        if not same(A, Mc, Lz) and not on(A, qz, Mc):
            M = Mc
        else:
            log.redraw += 1
    d0 = direction(A, Lz)
    while True:
        d1 = (A.rand(rng), A.rand(rng))
        if det2(A, d0, d1) != 0:
            break
    Lw = {w: L3[w] for w in Wa + Wb}
    other_pins = {w: [pos3[('p', e)] for e in inc(E3, w) if z not in e] for w in Wa}
    pinsb = [pos3[zp[w]] for w in Wb]

    def config(th):
        dth = (A.add(d0[0], A.mul(th, d1[0])), A.add(d0[1], A.mul(th, d1[1])))
        Lp = line_dir(A, Q3, dth)
        return Lp

    def ok(th):
        if th == 0:
            return False
        Lp = config(th)
        if any(parallel(A, Lp, Lw[w]) for w in Wa) or parallel(A, Lp, M):
            return False
        if on(A, qz, Lp):
            return False
        new = [meet(A, Lp, Lw[w]) for w in Wa]
        p1n = meet(A, Lp, M)
        if len(set(new + [p1n, Q3])) != len(new) + 2:
            return False
        if any(meet(A, Lp, Lw[w]) in other_pins[w] for w in Wa):
            return False
        L1 = line_through(A, p1n, qz)
        if parallel(A, L1, Lz) or on(A, Q3, L1):
            return False
        Q2 = meet(A, L1, Lz)
        if Q2 in pinsb:
            return False
        return True

    def moved(th):
        Lp = config(th)
        ps = dict(pos5)
        for w in Wa:
            ps[ren[zp[w]]] = meet(A, Lp, Lw[w])
        ps[P1] = meet(A, Lp, M)
        return Lp, ps
    # the family at theta = 0 is the configuration q5
    Lp0, ps0 = moved(0)
    assert same(A, Lp0, Lz) and ps0 == pos5, 'the pencil family does not pass through q5 at theta = 0'
    while True:
        th = draw_until(rng, lambda: A.rand(rng), [ok], log)
        Lp, ps = moved(th)
        if rig_rank(A, SV2, SE2, ps) >= rH1 + 2:
            break
        log.rankfail += 1
    log.step('H2 after the pencil move (theta)', rig_rank(A, SV2, SE2, ps), rH1 + 2, '>=')
    p1n = ps[P1]
    L1 = line_through(A, p1n, qz)
    Q2 = meet(A, L1, Lz)
    Q0 = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, L1)], log)
    P2 = ('p', pb)
    ps[P2], ps[('v', v1)] = Q2, Q0
    SEf = [e for e in SE2 if frozenset(e) != frozenset((U2, P1))]
    SEf += [(P2, P1), (P2, U2), (P2, P3)]
    SVf = SV2 + [P2]
    log.step('1-ext p2', rig_rank(A, SVf, SEf, ps), rH1 + 4, '>=')
    SVf = SVf + [('v', v1)]
    SEf = SEf + [(('v', v1), P1), (('v', v1), P2)]
    log.step('0-ext v1', rig_rank(A, SVf, SEf, ps), rH1 + 6, '>=')
    SVg, SEg = star_graph(V, E)
    assert set(map(frozenset, SEf)) <= set(map(frozenset, SEg)), 'the built graph is not a subgraph of G*'
    L = {w: L3[w] for w in V3 if w != z}
    L[u1], L[u2], L[v1] = Lp, Lz, L1
    return ps, L


def c65_case3(A, V, E, v1, rng, log):
    """Degree 2, u1u2 an edge, d(u2) = 2 (Claim 6.5 Case 3)."""
    pa, pb = inc(E, v1)
    u1, u2 = other(pa, v1), other(pb, v1)
    if len(inc(E, u2)) != 2:
        u1, u2, pa, pb = u2, u1, pb, pa
    p3 = ed(u1, u2)
    assert p3 in E and len(inc(E, u2)) == 2
    V4 = [v for v in V if v not in (v1, u2)]
    E4 = [e for e in E if v1 not in e and u2 not in e]
    pos, L, r4 = check_generic(A, V4, E4, rng)
    log.step('r(G4*) = t(G4)', r4, target(V4, E4))
    pins = [pos[('p', e)] for e in inc(E4, u1)]
    Q1 = draw_until(rng, lambda: point_on(A, L[u1], A.rand(rng)), [lambda P: P not in pins], log)
    Q3 = draw_until(rng, lambda: point_on(A, L[u1], A.rand(rng)), [lambda P: P not in pins + [Q1]], log)
    Q2 = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, L[u1])], log)
    Lv1, Lu2 = line_through(A, Q1, Q2), line_through(A, Q3, Q2)
    Q5 = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, Lv1)], log)
    Q6 = draw_until(rng, lambda: rand_point(A, rng), [lambda P: not on(A, P, Lu2)], log)
    pos[('p', pa)], pos[('p', p3)], pos[('p', pb)] = Q1, Q3, Q2
    pos[('v', v1)], pos[('v', u2)] = Q5, Q6
    L[v1], L[u2] = Lv1, Lu2
    return pos, L


def c66(A, V, E, p1, rng, log):
    """def(G - p1) = def(G) (Claim 6.6)."""
    v1, v2 = p1
    E1 = [e for e in E if e != p1]
    assert dfc(V, E1) == dfc(V, E)
    pos, L, r1 = check_generic(A, V, E1, rng)
    log.step('r(G1*) = t(G1)', r1, target(V, E1))
    pos[('p', p1)] = meet(A, L[v1], L[v2])
    return pos, L


def c68(A, V, E, p1, p2, rng, log):
    """A 2-edge-cut {p1, p2} with def(G - p1) = def(G) + 1 (Claim 6.8)."""
    E1 = [e for e in E if e != p1]
    assert dfc(V, E1) == dfc(V, E) + 1
    # the side of p1's end u: the component of G1 - p2 containing u
    u, v = p1
    E12 = [e for e in E1 if e != p2]
    comp = {u}
    grew = True
    while grew:
        grew = False
        for a, b in E12:
            if (a in comp) != (b in comp):
                comp |= {a, b}
                grew = True
    assert v not in comp, 'p1 is not across the cut'

    def body_ok(pos, L):
        Q = meet(A, L[u], L[v])
        return not on(A, pos[('v', v)], line_through(A, Q, pos[('p', p2)]))
    pos, L = gen_real(A, V, E1, rng, body_ok)
    r1 = star_rank(A, V, E1, pos)
    log.step('r(G1*) = t(G1)', r1, target(V, E1))
    Q = meet(A, L[u], L[v])
    P1 = ('p', p1)
    pos[P1] = Q
    SV, SE = star_graph(V, E1)
    p3 = inc(E1, u)[0]
    SV1, SE1 = SV + [P1], SE + [(P1, ('v', u)), (P1, ('p', p3))]
    rH1 = rig_rank(A, SV1, SE1, pos)
    log.step('H1 (0-ext p1)', rH1, r1 + 2)
    # the explicit motion: rotate v's side about q(p2), fix the rest
    X2 = pos[('p', p2)]
    side_v = {('v', w) for w in V if w not in comp} | {('p', e) for e in E1 if e != p2 and e[0] not in comp}
    m = {}
    for x in SV1:
        if x in side_v:
            y = (A.sub(pos[x][0], X2[0]), A.sub(pos[x][1], X2[1]))
            m[x] = (y[1], A.neg(y[0]))                  # J'(x - q(p2)): rotation about q(p2)
        else:
            m[x] = (0, 0)

    def edge_val(a, b):
        d = (A.sub(pos[a][0], pos[b][0]), A.sub(pos[a][1], pos[b][1]))
        dm = (A.sub(m[a][0], m[b][0]), A.sub(m[a][1], m[b][1]))
        return A.add(A.mul(d[0], dm[0]), A.mul(d[1], dm[1]))
    assert all(edge_val(a, b) == 0 for a, b in SE1), 'the rotation is not a motion of H1'
    assert edge_val(P1, ('v', v)) != 0, 'the bar p1 v does not block the rotation'
    log.step('H2 = H1 + p1v', rig_rank(A, SV1, SE1 + [(P1, ('v', v))], pos), rH1 + 1)
    return pos, L


def affine_line(A, Mx, tv, Lf):
    P = point_on(A, Lf, 0)
    Q = point_on(A, Lf, 1)

    def img(X):
        return (A.add(A.add(A.mul(Mx[0][0], X[0]), A.mul(Mx[0][1], X[1])), tv[0]),
                A.add(A.add(A.mul(Mx[1][0], X[0]), A.mul(Mx[1][1], X[1])), tv[1]))
    return line_through(A, img(P), img(Q)), img


def c_final(A, V, E, B1, rng, log):
    """The final gluing along a superbrick B1 with d(B1) = 2, with R1's affine map."""
    B1 = set(B1)
    cut = [e for e in E if (e[0] in B1) != (e[1] in B1)]
    assert len(cut) == 2
    (pA, pB) = cut
    u1, v1 = (pA[0], pA[1]) if pA[0] in B1 else (pA[1], pA[0])
    u2, v2 = (pB[0], pB[1]) if pB[0] in B1 else (pB[1], pB[0])
    assert v1 != v2, 'v1 = v2: G2 would have a double edge'
    w0, w1, w2 = 'w0#', 'w1#', 'w2#'
    VH1, EH1 = induced(V, E, B1)
    VH2, EH2 = induced(V, E, set(V) - B1)
    p3, p4, p5 = ed(u1, w0), ed(w0, w1), ed(w1, u2)
    p6, p7 = ed(v1, w2), ed(v2, w2)
    V1, E1 = VH1 + [w0, w1], EH1 + [p3, p4, p5]
    V2, E2 = VH2 + [w2], EH2 + [p6, p7]
    assert dfc(V1, E1) == 0, 'Claim 6.10(a) fails: G1 is not strong'
    assert dfc(V2, E2) <= dfc(V, E), 'Claim 6.10(b) fails'
    pos1, L1, r1 = check_generic(A, V1, E1, rng)
    pos2, L2, r2 = check_generic(A, V2, E2, rng)
    log.step('r(G1*) = 2(n1+m1) - 3', r1, 2 * (len(V1) + len(E1)) - 3)
    log.step('r(G2*) = t(G2)', r2, target(V2, E2))
    a, b = pos2[('p', p6)], pos2[('p', p7)]
    a_, b_ = pos1[('p', p3)], pos1[('p', p5)]
    assert a != b and a_ != b_
    ba = (A.sub(b[0], a[0]), A.sub(b[1], a[1]))
    ba_ = (A.sub(b_[0], a_[0]), A.sub(b_[1], a_[1]))
    while True:
        c = (A.rand(rng), A.rand(rng))
        if det2(A, ba, c) != 0:
            break
    D = det2(A, ba, c)
    Ninv = ((A.div(c[1], D), A.neg(A.div(c[0], D))), (A.neg(A.div(ba[1], D)), A.div(ba[0], D)))

    def mk(c_):
        # Mx = [ba_ | c_] . [ba | c]^{-1}
        C = ((ba_[0], c_[0]), (ba_[1], c_[1]))
        Mx = tuple(tuple(A.add(A.mul(C[i][0], Ninv[0][j]), A.mul(C[i][1], Ninv[1][j])) for j in range(2)) for i in range(2))
        tv = (A.sub(a_[0], A.add(A.mul(Mx[0][0], a[0]), A.mul(Mx[0][1], a[1]))),
              A.sub(a_[1], A.add(A.mul(Mx[1][0], a[0]), A.mul(Mx[1][1], a[1]))))
        return Mx, tv

    def okc(c_):
        if det2(A, ba_, c_) == 0:
            return False
        Mx, tv = mk(c_)
        l1, _ = affine_line(A, Mx, tv, L2[v1])
        l2, _ = affine_line(A, Mx, tv, L2[v2])
        return not same(A, l1, L1[u1]) and not same(A, l2, L1[u2])
    c_ = draw_until(rng, lambda: (A.rand(rng), A.rand(rng)), [okc], log)
    Mx, tv = mk(c_)
    _, img = affine_line(A, Mx, tv, L2[v1])
    assert img(a) == a_ and img(b) == b_
    pos, L = {}, {}
    drop1 = {('v', w0), ('v', w1), ('p', p3), ('p', p4), ('p', p5)}
    drop2 = {('v', w2), ('p', p6), ('p', p7)}
    for x, P in pos1.items():
        if x not in drop1:
            pos[x] = P
    for x, P in pos2.items():
        if x not in drop2:
            pos[x] = img(P)
    pos[('p', pA)], pos[('p', pB)] = a_, b_
    for w in VH1:
        L[w] = L1[w]
    for w in VH2:
        L[w], _ = affine_line(A, Mx, tv, L2[w])
    # the rank bookkeeping of TR p.20
    SV1, SE1 = star_graph(V1, E1)
    F1V = [x for x in SV1 if x not in {('v', w0), ('v', w1), ('p', p4)}]
    F1E = [e for e in SE1 if e[0] in F1V and e[1] in F1V]
    rF1 = rig_rank(A, F1V, F1E, pos1)
    rF1p = rig_rank(A, F1V, F1E + [(('p', p3), ('p', p5))], pos1)
    log.step('r(F1) = r(G1*) - 6', rF1, r1 - 6)
    log.step('r(F1 + p3p5) = r(F1)', rF1p, rF1)
    SV2, SE2 = star_graph(V2, E2)
    F2V = [x for x in SV2 if x != ('v', w2)]
    F2E = [e for e in SE2 if ('v', w2) not in e]
    log.step('r(F2) = r(G2*) - 2', rig_rank(A, F2V, F2E, pos2), r2 - 2)
    SVg, SEg = star_graph(V, E)
    rG = rig_rank(A, SVg, SEg, pos)
    rGp = rig_rank(A, SVg, SEg + [(('p', pA), ('p', pB))], pos)
    log.step('r(G* + p1p2) = r(F1+p3p5) + r(F2) - 1', rGp, rF1p + (r2 - 2) - 1)
    log.step('r(G*) = r(G* + p1p2)', rG, rGp)
    log.step('r(G*) = 2(n+m) - 3 - def(G2)', rG, 2 * (len(V) + len(E)) - 3 - dfc(V2, E2))
    return pos, L


# ---------------------------------------------------------------- instances

def K(names):
    return [ed(a, b) for a, b in itertools.combinations(names, 2)]


def instances():
    I = []
    I.append(('K2', ['a', 'b'], [ed('a', 'b')], 'base', {}))
    I.append(('K3', ['a', 'b', 'c'], K('abc'), 'base', {}))
    I.append(('K3+K3 disjoint', list('abcdef'), K('abc') + K('def'), 'c62', {'parts': [set('abc'), set('def')]}))
    I.append(('P3', list('abc'), [ed('a', 'b'), ed('b', 'c')], 'c63', {'v1': 'a'}))
    I.append(('K4+pendant', list('abcde'), K('abcd') + [ed('d', 'e')], 'c63', {'v1': 'e'}))
    I.append(('K3-bridge-K3', list('abcdef'), K('abc') + K('def') + [ed('c', 'd')], 'c64', {'p0': ed('c', 'd')}))
    I.append(('K4+v1 same brick', list('abcdv'), K('abcd') + [ed('a', 'v'), ed('b', 'v')], 'c65_same', {'v1': 'v'}))
    # Case 1: triangles {u,a,b}, {x,c,d}, joined by a-c; v ~ u, x
    E1 = K(['u', 'a', 'b']) + K(['x', 'c', 'd']) + [ed('a', 'c'), ed('v', 'u'), ed('v', 'x')]
    I.append(('Case1 two triangles', ['u', 'a', 'b', 'x', 'c', 'd', 'v'], E1, 'c65_case1', {'v1': 'v'}))
    E1b = K(['u', 'a', 'b', 'c']) + K(['x', 'd', 'e', 'f']) + [ed('a', 'd'), ed('v', 'u'), ed('v', 'x')]
    I.append(('Case1 two K4', ['u', 'a', 'b', 'c', 'x', 'd', 'e', 'f', 'v'], E1b, 'c65_case1', {'v1': 'v'}))
    # Case 2: triangles {u,a,b}, {x,c,d}, joined by u-x; v ~ u, x
    E2 = K(['u', 'a', 'b']) + K(['x', 'c', 'd']) + [ed('u', 'x'), ed('v', 'u'), ed('v', 'x')]
    I.append(('Case2 two triangles', ['u', 'a', 'b', 'x', 'c', 'd', 'v'], E2, 'c65_case2', {'v1': 'v'}))
    E2b = K(['u', 'a', 'b', 'c']) + K(['x', 'd', 'e', 'f']) + [ed('u', 'x'), ed('v', 'u'), ed('v', 'x')]
    I.append(('Case2 two K4', ['u', 'a', 'b', 'c', 'x', 'd', 'e', 'f', 'v'], E2b, 'c65_case2', {'v1': 'v'}))
    E2c = K(['u', 'a', 'b', 'c']) + K(['x', 'd', 'e', 'f']) + [ed('u', 'x'), ed('v', 'u'), ed('v', 'x'),
                                                              ed('a', 'y'), ed('y', 'z'), ed('z', 'd')]
    I.append(('Case2 two K4 + path a-y-z-d', ['u', 'a', 'b', 'c', 'x', 'd', 'e', 'f', 'v', 'y', 'z'], E2c,
              'c65_case2', {'v1': 'v'}))
    C5 = [ed('c0', 'c1'), ed('c1', 'c2'), ed('c2', 'c3'), ed('c3', 'c4'), ed('c4', 'c0')]
    I.append(('C5 (Case 1, def 2)', ['c0', 'c1', 'c2', 'c3', 'c4'], C5, 'c65_case1', {'v1': 'c0'}))
    Eth = [ed('u', 'x'), ed('u', 'v'), ed('x', 'v'), ed('u', 'a'), ed('u', 'b'), ed('x', 'c'), ed('x', 'd'),
           ed('a', 'c'), ed('b', 'd')]
    I.append(('Case2 triangle + two 4-cycles', ['u', 'x', 'v', 'a', 'b', 'c', 'd'], Eth, 'c65_case2',
              {'v1': 'v'}))
    Eth2 = [ed('u', 'x'), ed('u', 'v'), ed('x', 'v'), ed('u', 'a'), ed('u', 'b'), ed('x', 'c'), ed('x', 'd'),
            ed('a', 'c'), ed('b', 'e'), ed('e', 'd')]
    I.append(('Case2 triangle + 4-cycle + 5-cycle (def > 0)', ['u', 'x', 'v', 'a', 'b', 'c', 'd', 'e'], Eth2,
              'c65_case2', {'v1': 'v'}))
    Eq = [ed('u', 'x'), ed('u', 'v'), ed('x', 'v'), ed('u', 'a'), ed('a', 'b'), ed('b', 'c'), ed('c', 'u')]
    I.append(('Case3 triangle on a 4-cycle (def > 0)', ['u', 'x', 'v', 'a', 'b', 'c'], Eq, 'c65_case3', {'v1': 'v'}))
    E8c = K('abcd') + K('efgh') + [ed('a', 'e'), ed('b', 'f'), ed('c', 'x'), ed('x', 'y'), ed('y', 'z'),
                                   ed('z', 'c')]
    I.append(('two K4, 2-matching, C4 at c (Claim 6.8, def > 0)', list('abcdefghxyz'), E8c, 'c68',
              {'p1': ed('a', 'e'), 'p2': ed('b', 'f')}))
    E3 = K(['u', 'a', 'b', 'c']) + [ed('u', 'x'), ed('v', 'u'), ed('v', 'x')]
    I.append(('Case3 K4 + triangle', ['u', 'a', 'b', 'c', 'x', 'v'], E3, 'c65_case3', {'v1': 'v'}))
    I.append(('K4 (Claim 6.6)', list('abcd'), K('abcd'), 'c66', {'p1': ed('a', 'b')}))
    E8 = K('abcd') + K('efgh') + [ed('a', 'e'), ed('b', 'f')]
    I.append(('two K4, 2-matching (Claim 6.8)', list('abcdefgh'), E8, 'c68',
              {'p1': ed('a', 'e'), 'p2': ed('b', 'f')}))
    I.append(('two K4, 2-matching (gluing)', list('abcdefgh'), E8, 'c_final', {'B1': set('abcd')}))
    E8d = K('abcd') + [ed('e', 'f'), ed('f', 'g'), ed('g', 'h'), ed('h', 'e'), ed('a', 'e'), ed('b', 'g')]
    I.append(('K4 + C4 via two edges (gluing)', list('abcdefgh'), E8d, 'c_final', {'B1': set('abcd')}))
    E7p = K('abcd') + [ed('e', 'f'), ed('f', 'g'), ed('a', 'e'), ed('b', 'g')]
    I.append(('K4 + path e-f-g via two edges (gluing, def > 0)', list('abcdefg'), E7p, 'c_final', {'B1': set('abcd')}))
    E9 = K('abcd') + K('efgh') + K('ijkl') + [ed('a', 'e'), ed('f', 'i'), ed('j', 'b')]
    I.append(('three K4 cycle (gluing)', list('abcdefghijkl'), E9, 'c_final', {'B1': set('abcd')}))
    E9b = K('abcd') + K('efgh') + K('ijkl') + [ed('a', 'e'), ed('f', 'i'), ed('j', 'a')]
    I.append(('three K4 cycle, u1 = u2 (gluing)', list('abcdefghijkl'), E9b, 'c_final', {'B1': set('abcd')}))
    return I


CONS = {'base': c_base, 'c62': c62, 'c63': c63, 'c64': c64, 'c65_same': c65_same,
        'c65_case1': c65_case1, 'c65_case2': c65_case2, 'c65_case3': c65_case3,
        'c66': c66, 'c68': c68, 'c_final': c_final}


def run(fields):
    print(f'jjbuild: seed={SEED} fields={",".join(A.name for A in fields)}')
    total = 0
    for A in fields:
        tot_redraw = tot_fail = 0
        for name, V, E, kind, kw in instances():
            rng = random.Random(f'{SEED}:{A.name}:{name}')
            log = Log()
            pos, L = CONS[kind](A, V, E, rng=rng, log=log, **kw)
            r, t = finish(A, V, E, pos, L, log, name)
            tot_redraw += log.redraw
            tot_fail += log.rankfail
            total += 1
            print(f'{A.name}: {name} [{kind}]: n={len(V)} m={len(E)} def={dfc(V, E)} '
                  f'r(G*)={r}=t(G) non-degenerate; steps: ' + '; '.join(log.steps)
                  + f'; redraws={log.redraw} rankfail={log.rankfail}', flush=True)
        print(f'{A.name}: all {len(instances())} constructions OK; excluded-value redraws {tot_redraw}; '
              f'rank failures at drawn parameters {tot_fail}')
    return 0


# ---------------------------------------------------------------- selftest

def strong(V, E):
    return dfc(V, E) == 0


def superstrong(V, E):
    """def = 0 and the only tight partition is {V}: every partition with >= 2
    parts has negative deficiency."""
    if len(V) == 1:
        return True
    if dfc(V, E) != 0:
        return False
    for P in set_partitions(V):
        if len(P) >= 2 and 3 * (len(P) - 1) - 2 * cross(P, E) >= 0:
            return False
    return True


def set_partitions(V):
    V = list(V)
    if not V:
        yield []
        return
    first, rest = V[0], V[1:]
    for P in set_partitions(rest):
        for i in range(len(P)):
            yield P[:i] + [P[i] | {first}] + P[i + 1:]
        yield P + [{first}]


def cross(P, E):
    lab = {v: i for i, S in enumerate(P) for v in S}
    return sum(1 for a, b in E if lab[a] != lab[b])


def maximal_sets(V, E, pred):
    """For each v, the union of all X containing v with pred(G[X]); returns the
    set of these unions, and asserts each union satisfies pred (the union lemma)."""
    out = []
    for v in V:
        others = [w for w in V if w != v]
        U = {v}
        for k in range(1, len(others) + 1):
            for T in itertools.combinations(others, k):
                X = {v, *T}
                if pred(*induced(V, E, X)):
                    U |= X
        assert pred(*induced(V, E, U)), 'union lemma fails'
        out.append(frozenset(U))
    return set(out)


def selftest():
    bad = 0
    A = Ar(make_field('2^16'))
    rng = random.Random(f'{SEED}:selftest')
    # guard 1: is_nondeg must reject the degenerate K3 (all three pin-lines equal)
    Lc = rand_line(A, rng)
    V, E = list('abc'), K('abc')
    pts = [point_on(A, Lc, s) for s in (1, 2, 3)]
    posd = {('p', ed('a', 'b')): pts[0], ('p', ed('b', 'c')): pts[1], ('p', ed('a', 'c')): pts[2]}
    for v in V:
        while True:
            P = rand_point(A, rng)
            if not on(A, P, Lc):
                break
        posd[('v', v)] = P
    Ld = {v: Lc for v in V}
    ok_bp, ok_nd = is_bp(A, V, E, posd, Ld), is_nondeg(A, E, Ld)
    print(f'witness K3 with one common pin-line: is_bp={ok_bp} (counter-fact: it IS a pin-collinear '
          f'body-and-pin realization), is_nondeg={ok_nd} (must be False)')
    bad += (not ok_bp) + ok_nd
    r_deg = star_rank(A, V, E, posd)
    print(f'   its rank r(K3*) = {r_deg} < t(K3) = {target(V, E)}; the TR Lemma 4.2 proof would move the pin ac '
          f'along L(c) = L(a) onto L0 through q(ab), i.e. onto q(ab) itself')
    bad += not (r_deg < target(V, E))
    posn, Ln = gen_real(A, V, E, rng)
    print(f'negative control (generic K3): is_bp={is_bp(A, V, E, posn, Ln)} is_nondeg={is_nondeg(A, E, Ln)} '
          f'rank={star_rank(A, V, E, posn)}')
    bad += not (is_bp(A, V, E, posn, Ln) and is_nondeg(A, E, Ln) and star_rank(A, V, E, posn) == target(V, E))
    # guard 2: is_bp must reject a body point on its pin-line
    posb = dict(posn)
    posb[('v', 'a')] = point_on(A, Ln['a'], 7)
    print(f'witness body point on its line: is_bp={is_bp(A, V, E, posb, Ln)} (must be False)')
    bad += is_bp(A, V, E, posb, Ln)
    # guard 3: lines_generic must reject three concurrent lines and two parallel ones
    X = rand_point(A, rng)
    Lcon = {v: line_dir(A, X, (1, i + 1)) for i, v in enumerate(V)}
    Lpar = dict(Ln)
    Lpar['b'] = (Ln['a'][0], Ln['a'][1], A.add(Ln['a'][2], 1))
    print(f'witness concurrent lines: lines_generic={lines_generic(A, V, Lcon)}; parallel pair: '
          f'{lines_generic(A, V, Lpar)} (both must be False); control: {lines_generic(A, V, Ln)}')
    bad += lines_generic(A, V, Lcon) + lines_generic(A, V, Lpar) + (not lines_generic(A, V, Ln))
    # R0 witness: in characteristic 2 the TR's degree-1 pin-line contains the body point
    qv, qp = (1, 0), (0, 1)
    dvec = (A.sub(qv[0], qp[0]), A.sub(qv[1], qp[1]))       # (1, 1) in char 2: isotropic
    Lorth = (dvec[0], dvec[1], A.neg(A.add(A.mul(dvec[0], qp[0]), A.mul(dvec[1], qp[1]))))
    print(f'R0 witness over {A.name}: the line through q(p) orthogonal to q(v)q(p) contains q(v): '
          f'{on(A, qv, Lorth)} (must be True)')
    bad += not on(A, qv, Lorth)
    # Lemmas 3.2, 3.3 and the one-edge property at a seeded battery
    brng = random.Random(f'{SEED}:bricks')
    nb = 0
    for trial in range(40):
        n = brng.randrange(3, 7)
        Vb = [f'v{i}' for i in range(n)]
        Eb = [ed(a, b) for a, b in itertools.combinations(Vb, 2) if brng.random() < 0.55]
        if not Eb or any(not inc(Eb, v) for v in Vb):
            continue
        nb += 1
        dG = dfc(Vb, Eb)
        tight = [P for P in set_partitions(Vb) if 3 * (len(P) - 1) - 2 * cross(P, Eb) == dG]
        bricks = maximal_sets(Vb, Eb, strong)
        sbricks = maximal_sets(Vb, Eb, superstrong)
        for fam in (bricks, sbricks):
            assert sum(len(S) for S in fam) == n and set().union(*fam) == set(Vb), 'Lemma 3.2 fails'
        mn = min(len(P) for P in tight)
        mx = max(len(P) for P in tight)
        assert all(set(map(frozenset, P)) == bricks for P in tight if len(P) == mn), 'Lemma 3.3(a) fails'
        assert all(set(map(frozenset, P)) == sbricks for P in tight if len(P) == mx), 'Lemma 3.3(b) fails'
        for P in tight:
            for S, T in itertools.combinations(P, 2):
                assert sum(1 for a, b in Eb if (a in S and b in T) or (a in T and b in S)) <= 1, \
                    'two parts of a tight partition joined by 2 edges'
            assert all(strong(*induced(Vb, Eb, S)) for S in P), 'a part of a tight partition is not strong'
    print(f'Lemma 3.2 = (NEW-I6)(iii), Lemma 3.3 = (NEW-I6)(v), parts of tight partitions strong = (NEW-I6)(iv), '
          f'one-edge property = (NEW-I5)(ii): verified at {nb} seeded graphs on 3..6 vertices')
    print(f'selftest: {"FAIL" if bad else "OK"}')
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--run', action='store_true')
    ap.add_argument('--fields', default='2^16,3^10,10007')
    a = ap.parse_args()
    bad = 0
    if a.selftest:
        bad += selftest()
    if a.run:
        bad += run([Ar(make_field(s)) for s in a.fields.split(',')])
    if not (a.selftest or a.run):
        ap.error('name a mode')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
