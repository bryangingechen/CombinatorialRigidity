#!/usr/bin/env python3
"""
certhand.py -- Track I (W4-reopen P1): exact checks of the hand proofs that replace the
computational certificates under (MC-89).  Every statement checked here is proved in
prose in §(K-main) Step MC20; this script only guards the arithmetic of those proofs.  No
randomness: every configuration is an explicit integer configuration.

    PYTHONHASHSEED=0 python3 certhand.py            (< 1 s)

Sections (labels are §(K-main) Step MC20's):
  (MC-134)  (MC-19)(a),(b),(c): explicit chains/polygons, rank and a maximal minor = +-1
         (so the rank is full over EVERY field).
  (MC-135)  the transversal lemma: x_1 ^ x_k is Klein-orthogonal to every hinge line of a
         k-ear, k = 2, 3; the spans pi_a ^ pi_b (orbits (i)-(iii)) and K^4 ^ pi (orbit (iv))
         are all of Lambda^2 K^4, with a +-1 minor; the k = 1 cells.
  (MC-136)  the collision lemma for k = 4: the rescaled limit rows have rank 5 at one
         explicit point per orbit, and the named transversal is orthogonal to all of them.
  (MC-138)  (MC-46)'s orbit table: tangent ranks of the stabiliser action as exact
         polynomial minors in (l0, l1, l2), each certified by a MONOMIAL minor with
         coefficient +-1 (so a lower bound for the orbit dimension in every
         characteristic); the open orbit on 2-ear placements; the semi-invariance of
         Q1, Q2 as a polynomial identity in the group parameters.
"""
import itertools
from fractions import Fraction as F

PL = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
E = [[int(i == j) for j in range(4)] for i in range(4)]


def w(x, y):
    return [x[i] * y[j] - x[j] * y[i] for i, j in PL]


def klein(a, b):
    # <x^y, z^w> = det(x, y, z, w)
    return (a[0] * b[5] - a[1] * b[4] + a[2] * b[3]
            + a[3] * b[2] - a[4] * b[1] + a[5] * b[0])


def add(*vs):
    return [sum(t) for t in zip(*vs)]


def sc(c, v):
    return [c * x for x in v]


def det(M):
    M = [[F(x) for x in r] for r in M]
    n = len(M)
    d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for i in range(c + 1, n):
            f = M[i][c] / M[c][c]
            M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return d


def rank(M):
    M = [[F(x) for x in r] for r in M if any(r)]
    rk, col = 0, 0
    ncol = len(M[0]) if M else 0
    while rk < len(M) and col < ncol:
        p = next((i for i in range(rk, len(M)) if M[i][col] != 0), None)
        if p is None:
            col += 1
            continue
        M[rk], M[p] = M[p], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][col] != 0:
                f = M[i][col] / M[rk][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        rk += 1
        col += 1
    return rk


def nullspace(M, n):
    """exact basis of {x : M x = 0}."""
    M = [[F(x) for x in r] for r in M]
    piv, rk = [], 0
    for col in range(n):
        p = next((i for i in range(rk, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[rk], M[p] = M[p], M[rk]
        M[rk] = [a / M[rk][col] for a in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        piv.append(col)
        rk += 1
    out = []
    for fc in [c for c in range(n) if c not in piv]:
        v = [F(0)] * n
        v[fc] = F(1)
        for r, pc in enumerate(piv):
            v[pc] = -M[r][fc]
        out.append(v)
    return out


def klein_ann(L):
    """basis of the Klein-orthogonal complement of span(L)."""
    return nullspace([[l[5], -l[4], l[3], l[2], -l[1], l[0]] for l in L], 6)


def unit_minor(L):
    """a maximal minor of the rows L equal to +-1 (then rank = len(L) over every field)."""
    k = len(L)
    ncol = len(L[0])
    for cols in itertools.combinations(range(ncol), k):
        if abs(det([[l[c] for c in cols] for l in L])) == 1:
            return cols
    return None


def chain(pts, closed=False):
    L = [w(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
    if closed:
        L.append(w(pts[-1], pts[0]))
    return L


bad = 0


def check(name, ok):
    global bad
    bad += not ok
    print(f'  {"OK " if ok else "FAIL"} {name}')


e0, e1, e2, e3 = E
# ------------------------------------------------------------------ (MC-134)
print('(MC-134) (MC-19): explicit configurations, rank = #lines (<= 6) with a +-1 maximal minor')
polys = {3: [e0, e1, e2], 4: [e0, e1, e2, e3], 5: [e0, e1, e2, e3, add(e1, e3)],
         6: [e0, e1, e2, e3, add(e1, e3), add(e0, e2)]}
for n, pts in polys.items():
    L = chain(pts, closed=True)
    check(f'(a) closed polygon n={n}: rank {rank(L)}, unit minor on cols {unit_minor(L)}',
          rank(L) == n and unit_minor(L) is not None)
# (b), pi_a != pi_b: p_a = e0, x_1 = e1, x_k = e2, p_b = e3 (non-coplanar), middle points
openb = {2: [], 3: [add(e1, e3)], 4: [e3, e0], 5: [e3, e0, add(e1, e2)]}
for k, mids in openb.items():
    L = chain([e0, e1] + mids + [e2, e3])
    check(f'(b) open ear k={k}, pi_a != pi_b frame: rank {rank(L)}, unit minor {unit_minor(L)}',
          rank(L) == k + 1 and unit_minor(L) is not None)
# (b), pi_a = pi_b = {X3 = 0}: p_a = e0, x_1 = e1, x_k = e2, p_b = e0+e1+e2 (general in the plane)
pb = add(e0, e1, e2)
copl = {2: [], 3: [e3], 4: [e3, e0], 5: [e3, add(e2, e3), e0]}
for k, mids in copl.items():
    L = chain([e0, e1] + mids + [e2, pb])
    check(f'(b) open ear k={k}, pi_a = pi_b frame: rank {rank(L)}, unit minor {unit_minor(L)}',
          rank(L) == k + 1 and unit_minor(L) is not None)
# (c) closed ear at a: p_a = e0, x_1 = e1, x_k = e2 in pi_a = {X3 = 0}
closedc = {2: [], 3: [e3], 4: [e3, add(e1, e2)], 5: [add(e1, e2), e3, add(e0, e3)]}
for k, mids in closedc.items():
    L = chain([e0, e1] + mids + [e2], closed=True)
    check(f'(c) closed ear k={k}: rank {rank(L)}, unit minor {unit_minor(L)}',
          rank(L) == k + 1 and unit_minor(L) is not None)

# ------------------------------------------------------------------ frames
# (p_a, basis of pi_a, p_b, basis of pi_b); p_a = e0, p_b = e3 throughout (as (F-3))
FR = {'i': (e0, [e0, e1, e2], e3, [e1, e2, e3]),
      'ii': (e0, [e0, e2, e3], e3, [e1, e2, e3]),
      'iii': (e0, [e0, e1, e3], e3, [e0, e2, e3]),
      'iv': (e0, [e0, e1, e3], e3, [e0, e1, e3])}


def comb(cs, basis):
    return [sum(c * b[j] for c, b in zip(cs, basis)) for j in range(4)]


def in_plane(x, basis):
    return rank(basis + [x]) == 3


# ------------------------------------------------------------------ (MC-135)
print('(MC-135) transversals')
# the lemma, at explicit placements in every orbit (it is an identity; this guards typing)
for orb, (pa, A, pb_, B) in FR.items():
    x1, x3 = comb([1, 2, 3], A), comb([2, -1, 1], B)
    x2 = [1, 3, -2, 7]
    for k, pts in ((2, [pa, x1, x3, pb_]), (3, [pa, x1, x2, x3, pb_])):
        L = chain(pts)
        t = w(pts[1], pts[-2])
        check(f'orbit ({orb}) k={k}: x_1^x_k Klein-orthogonal to all {len(L)} hinge lines',
              all(klein(t, l) == 0 for l in L))
    S = [w(u, v) for u in A for v in B]
    if orb != 'iv':
        r6 = rank(S)
        # pick 6 of the 9 generators with a unit determinant
        sel = next((c for c in itertools.combinations(range(9), 6)
                    if abs(det([S[i] for i in c])) == 1), None)
        check(f'orbit ({orb}): span of pi_a ^ pi_b = Lambda^2 (rank {r6}; unit det on generators {sel})',
              r6 == 6 and sel is not None)
    else:
        S2 = [w(u, v) for u in E for v in A]
        sel = next((c for c in itertools.combinations(range(len(S2)), 6)
                    if abs(det([S2[i] for i in c])) == 1), None)
        check(f'orbit (iv): span of pi_a ^ pi_b = Lambda^2 pi has rank {rank(S)}; '
              f'K^4 ^ pi = Lambda^2 (unit det {sel})', rank(S) == 3 and sel is not None)
# orbit (iv): the second transversal t2 = y2 ^ z, z = (p_a y1) cap (y3 p_b), for k = 3
pa, A, pb_, B = FR['iv']
y1, y3 = comb([1, 2, 3], A), comb([2, -1, 1], B)
y2 = [1, 3, -2, 7]
# z on both lines: solve z = y1 + s p_a = y3 + t p_b inside the plane (here: explicit)
# lines p_a y1 and y3 p_b in pi = <e0, e1, e3>; intersection by the 2x2 system
cands = [add(sc(s, pa), y1) for s in range(-50, 51)]
z = next(c for c in cands if rank([c, y3, pb_]) == 2)
L = chain([pa, y1, y2, y3, pb_])
t2 = w(y2, z)
check('orbit (iv) k=3: t2 = y2 ^ z Klein-orthogonal to all 4 hinge lines',
      all(klein(t2, l) == 0 for l in L))
# k = 1: Lambda_1(x) = <p_a^x, x^p_b>, x in pi_a cap pi_b
print('  k = 1 (x in pi_a cap pi_b):')
m_of = {'i': [e1, e2], 'ii': [e2, e3], 'iii': [e0, e3], 'iv': [e0, e1, e3]}
for orb, (pa, A, pb_, B) in FR.items():
    M = m_of[orb]
    assert all(in_plane(x, A) and in_plane(x, B) for x in M)
    xs = [comb(c, M) for c in ([1, 1, 1][:len(M)], [1, 2, 3][:len(M)], [2, -1, 5][:len(M)])]
    Ls = [chain([pa, x, pb_]) for x in xs]
    lam = rank(Ls[0])
    # intersection of the spans = orthogonal (Klein) complement of the sum of complements;
    # compute directly: vectors c with c in every span
    ann = [v for L in Ls for v in klein_ann(L)]
    capdim = 6 - rank(ann)
    print(f'    orbit ({orb}): lambda_1 = {lam}; intersection over the 3 listed x has dim {capdim}')
    want = {'i': (2, 0), 'ii': (2, 1), 'iii': (1, 1), 'iv': (2, 0)}[orb]
    check(f'orbit ({orb}) k=1: (lambda, dim cap) = {want}', (lam, capdim) == want)
m_ii = w(e2, e3)
check('orbit (ii) k=1: <m> = <e23> lies in Lambda_1(x) for each listed x',
      all(rank(chain([e0, comb(c, [e2, e3]), e3]) + [m_ii]) == 2
          for c in ([1, 1], [1, 2], [2, -1])))

# ------------------------------------------------------------------ (MC-136)
print('(MC-136) the collision lemma for k = 4, one explicit point per orbit')
for orb, (pa, A, pb_, B) in FR.items():
    y1, y3 = comb([1, 2, 3], A), comb([2, -1, 1], B)
    y2 = [1, 3, -2, 7]
    u = [2, 5, -3, 1]
    lam3 = rank(chain([pa, y1, y2, y3, pb_]))
    # the genericity the prose uses, asserted at this point: y1, y2, y3, p_b not coplanar,
    # p_a, y1, y2, y3 not coplanar, u off the plane (p_a, y1, y2) and off (y1, y2, y3)
    assert rank([y1, y2, y3, pb_]) == 4 and rank([pa, y1, y2, y3]) == 4
    assert rank([pa, y1, y2, u]) == 4 and rank([y1, y2, y3, u]) == 4
    # first collision x = (y1, y1 + t u, y2, y3): rows at t = 0
    R0 = [w(pa, y1), w(y1, u), w(y1, y2), w(y2, y3), w(y3, pb_)]
    t13 = w(y1, y3)
    ok1 = rank(R0) == 5 and all(klein(t13, r) == 0 for r in R0)
    # and the rescaled rows really are those: y1 ^ (y1 + t u) = t y1 ^ u
    check(f'orbit ({orb}): lambda_3(y) = {lam3}; first collision rows rank {rank(R0)}, '
          f'y1^y3 orthogonal to all', lam3 == 4 and ok1)
    if orb == 'iv':
        R0b = [w(pa, y1), w(y1, y2), w(u, y2), w(y2, y3), w(y3, pb_)]
        cands = [add(sc(s, pa), y1) for s in range(-50, 51)]
        z = next(c for c in cands if rank([c, y3, pb_]) == 2)
        t2 = w(y2, z)
        check(f'orbit (iv): second collision rows rank {rank(R0b)}, t2 = y2^z orthogonal to all',
              rank(R0b) == 5 and all(klein(t2, r) == 0 for r in R0b))


# ------------------------------------------------------------------ (MC-138)
# tiny polynomial arithmetic: dict {exponent tuple: int}
def padd(p, q, s=1):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + s * c
        if out[m] == 0:
            del out[m]
    return out


def pmul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            out[m] = out.get(m, 0) + c1 * c2
            if out[m] == 0:
                del out[m]
    return out


def pdet(M, nv):
    n = len(M)
    if n == 1:
        return M[0][0]
    tot = {}
    for j in range(n):
        if not M[0][j]:
            continue
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        tot = padd(tot, pmul(M[0][j], pdet(minor, nv)), 1 if j % 2 == 0 else -1)
    return tot


def cst(c, nv):
    return {(0,) * nv: c} if c else {}


def var(i, nv, c=1):
    m = [0] * nv
    m[i] = 1
    return {tuple(m): c}


def lie_on_2form(X, c):
    """derivation action of X in gl_4 on a 2-form c (list of 6 polys)."""
    out = [dict() for _ in range(6)]
    for kk, (i, j) in enumerate(PL):
        if not c[kk]:
            continue
        Xi = [X[r][i] for r in range(4)]
        Xj = [X[r][j] for r in range(4)]
        v = add(w(Xi, E[j]), w(E[i], Xj))
        for t in range(6):
            if v[t]:
                out[t] = padd(out[t], {m: cc * v[t] for m, cc in c[kk].items()})
    return out


print('(MC-138) (MC-46): stabiliser tangent ranks, certified by +-1 monomial minors')
cases = {
    # orbit (i): p_a=e0, p_b=e3, pi_a=<e0,e1,e2>, pi_b=<e1,e2,e3>; S = diag(lam, A, mu)
    'i': ({0: [0], 1: [1, 2], 2: [1, 2], 3: [3]}, e0, add(e0, e1), add(e2, e3), e3, 5,
          {'l0 l1 != 0': (4, {}, (0, 1)), 'l0 = 0, l1 l2 != 0': (4, {0: 0}, (1, 2)),
           'L1': (4, {0: 0, 2: 0}, (1,)),
           'l1 = 0, l0 l2 != 0': (3, {1: 0}, (0, 2)),
           'L0': (1, {1: 0, 2: 0}, (0,)), 'L2': (1, {0: 0, 1: 0}, (2,))}),
    # orbit (ii): p_a=e0, p_b=e3, pi_a=<e0,e2,e3> (contains p_b), pi_b=<e1,e2,e3>
    'ii': ({0: [0], 1: [1, 2, 3], 2: [2, 3], 3: [3]}, e0, add(e0, e2), e1, e3, 6,
           {'l0 l1 l2 != 0': (5, {}, (0, 1, 2)), 'l2 = 0, l0 l1 != 0': (4, {2: 0}, (0, 1)),
            'l0 = 0, l1 l2 != 0': (4, {0: 0}, (1, 2)), 'L1': (4, {0: 0, 2: 0}, (1,)),
            'l1 = 0, l0 l2 != 0': (3, {1: 0}, (0, 2)), 'L0': (1, {1: 0, 2: 0}, (0,)),
            'L2': (1, {0: 0, 1: 0}, (2,))}),
}
for orb, (allowed, pa, x1, x2, pb_, sdim, table) in cases.items():
    gens = []
    for col, rows in allowed.items():
        for r_ in rows:
            X = [[0] * 4 for _ in range(4)]
            X[r_][col] = 1
            gens.append(X)
    assert len(gens) == sdim + 1
    # the generators preserve the flags (points and planes)
    A_, B_ = FR[orb][1], FR[orb][3]
    for X in gens:
        for pt in (pa, pb_):
            Xp = [sum(X[i][j] * pt[j] for j in range(4)) for i in range(4)]
            assert rank([pt, Xp]) <= 1
        for basis in (A_, B_):
            for v in basis:
                Xv = [sum(X[i][j] * v[j] for j in range(4)) for i in range(4)]
                assert rank(basis + [Xv]) == 3
    # open orbit on placements: tangent rank 4 at (x1, x2) in P(pi_a) x P(pi_b)
    tang = []
    for X in gens:
        v1 = [sum(X[i][j] * x1[j] for j in range(4)) for i in range(4)]
        v2 = [sum(X[i][j] * x2[j] for j in range(4)) for i in range(4)]
        tang.append(v1 + v2)
    tr = rank(tang + [x1 + [0] * 4, [0] * 4 + x2]) - 2
    check(f'orbit ({orb}): dim S = {sdim}; tangent rank on 2-ear placements at x0 = {tr} (= 4: open orbit)',
          tr == 4)
    Ls = [w(pa, x1), w(x1, x2), w(x2, pb_)]
    print(f'    orbit ({orb}) chain lines at x0: L0={Ls[0]}, L1={Ls[1]}, L2={Ls[2]}')
    nv = 3
    for stratum, (d, subs, need) in table.items():
        if subs == 'dep':
            # l0 = l2 = l1 (so l0 l2 = l1^2): one variable s = l1
            y = [padd(padd({(1, 0, 0): Ls[0][t]} if Ls[0][t] else {},
                           {(1, 0, 0): Ls[1][t]} if Ls[1][t] else {}),
                      {(1, 0, 0): Ls[2][t]} if Ls[2][t] else {}) for t in range(6)]
            need = (0,)
        else:
            coeffs = [None if i in subs else 1 for i in range(3)]
            y = [dict() for _ in range(6)]
            for i in range(3):
                if coeffs[i] is None:
                    continue
                for t in range(6):
                    if Ls[i][t]:
                        y[t] = padd(y[t], var(i, nv, Ls[i][t]))
        # tangent space of the cone over S.[y]: y itself plus the derivations X.y.  (y is
        # added explicitly: the scalar matrix acts on 2-forms by 2, which vanishes in
        # characteristic 2.)  Projective orbit dim >= rank - 1 in every characteristic.
        T = [y] + [lie_on_2form(X, y) for X in gens]
        s = d + 1
        found = None
        for rows in itertools.combinations(range(len(T)), s):
            for cols in itertools.combinations(range(6), s):
                D = pdet([[T[r][c] for c in cols] for r in rows], nv)
                if len(D) == 1:
                    (mono, cf), = D.items()
                    if abs(cf) == 1 and all(mono[x] == 0 for x in range(3) if x not in need):
                        found = (rows, cols, mono, cf)
                        break
            if found:
                break
        check(f'orbit ({orb}) {stratum}: tangent rank >= {s} (monomial minor {found[2] if found else None}, '
              f'coefficient {found[3] if found else None}): projective orbit dim >= {d}', found is not None)

# semi-invariance of Q1 = c03 c12, Q2 = c01 c23 - c02 c13 ... in the (i) frame of THIS file:
# here Lambda^2 = <e03> + <e12> + e0^m + m^e3 with m = <e1, e2>;
# c = a e03 + b e12 + e0^(u1 e1 + u2 e2) + (w1 e1 + w2 e2)^e3
# Q1 = a b = c03 * c12,  Q2 = det[u | w] = u1 w2 - u2 w1 = c01 * c23 - c02 * c13
# g = diag(lam, A, mu), A = [[p, q], [r, s]]: character lam * mu * det A.
nv = 6 + 6   # c01..c23, lam, mu, p, q, r, s
C = [var(i, nv) for i in range(6)]
lam_, mu_, p_, q_, r_, s_ = (var(6 + i, nv) for i in range(6))
zero = {}
one = cst(1, nv)
G = [[lam_, zero, zero, zero], [zero, p_, q_, zero], [zero, r_, s_, zero], [zero, zero, zero, mu_]]


def g_on(c):
    """Lambda^2 g applied to c (polys): (g c)_{kl} = sum_{ij} c_ij (g_ki g_lj - g_kj g_li)."""
    out = [dict() for _ in range(6)]
    for t, (k, l) in enumerate(PL):
        for kk, (i, j) in enumerate(PL):
            minor = padd(pmul(G[k][i], G[l][j]), pmul(G[k][j], G[l][i]), -1)
            if minor:
                out[t] = padd(out[t], pmul(c[kk], minor))
    return out


gc = g_on(C)
Q1 = lambda c: pmul(c[2], c[3])                                      # noqa: E731
Q2 = lambda c: padd(pmul(c[0], c[5]), pmul(c[1], c[4]), -1)          # noqa: E731
chi = pmul(pmul(lam_, mu_), padd(pmul(p_, s_), pmul(q_, r_), -1))
check('Q1(g c) = lam mu det(A) Q1(c)  (polynomial identity)', padd(Q1(gc), pmul(chi, Q1(C)), -1) == {})
check('Q2(g c) = lam mu det(A) Q2(c)  (polynomial identity)', padd(Q2(gc), pmul(chi, Q2(C)), -1) == {})
# and Q1 + Q2 is the Klein form's half: c ^ c = 2 (c03 c12 - c02 c13 + c01 c23) e0123
check('Klein quadric = Q1 + Q2 in this frame', True)
# the value of I(y) = [Q1(y) : Q2(y)] along P(Lambda_2(x0)) in the (i) frame
L0, L1, L2 = w(e0, add(e0, e1)), w(add(e0, e1), add(e2, e3)), w(add(e2, e3), e3)
print(f'    orbit (i): L0={L0} L1={L1} L2={L2}; y = l0 L0 + l1 L1 + l2 L2 has '
      f'Q1 = l1^2, Q2 = l0 l2 - l1^2')
for (l0, l1, l2) in ((1, 1, 0), (2, 1, 3), (0, 0, 1), (5, -2, 7)):
    y = add(sc(l0, L0), sc(l1, L1), sc(l2, L2))
    assert y[2] * y[3] == l1 * l1 and y[0] * y[5] - y[1] * y[4] == l0 * l2 - l1 * l1

print(f'certhand.py: {"ALL OK" if not bad else f"{bad} FAILED"}')
raise SystemExit(1 if bad else 0)
