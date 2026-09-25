#!/usr/bin/env python3
"""
charcheck.py -- §(K-main) Step MC20, the second reading of 2026-09-25 ((MC-168); ported from the
reader's scratch): an independent, seeded, exact check
of the hand-proved statements (MC-134)-(MC-138) in POSITIVE characteristic, where the
landed drivers (exact over Q) say nothing.  Written from the prose, not from certhand.py.

    PYTHONHASHSEED=0 python3 notes/scripts/w4/charcheck.py [--quick]

Fields: GF(p) for p in {2, 3, 5, 7} and GF(2^8) (poly basis, x^8+x^4+x^3+x+1).
Frames: Step MC20's orbit table (p_a = e0, p_b = e3).

What a line of output means (HARNESS.md *Evidence*):
  * [A] chain spans (MC-134): exact rank of each explicit configuration over the field.
  * [B] intersections (MC-135)/(MC-136): the intersection of Lambda_k(x) over SPAN-GENERIC
    placements x defined over the field.  Each such x is a K-point of the open set where
    Lambda(x) is a morphism to the Grassmannian, so every c lying in Lambda(x) on a dense set
    lies in Lambda(x) there: the printed value is an UPPER BOUND for dim of the intersection
    over the algebraic closure (a certificate), and the hand-proved lower bound
    (<m>, <n>, Lambda^2 pi) is asserted to lie inside it.
  * [C] (MC-138) tangent ranks rank{y, X y : X in Lie S} at EVERY point of each stratum over
    the field (small p) -- a lower bound for the projective orbit dimension (+1).
  * [D] (MC-46) at field-rational rho: family members must be bad at every placement
    (asserted); a non-family rho with a good placement is CERTIFIED good ((P_2) is open);
    a non-family rho with no good placement over the small field is a SUSPECT and is
    re-tested over GF(2^8) (p = 2) with seeded random placements.
  * [E] (MC-45), r = 2, at field-rational rho: (P_2)-good but (P_3)-bad suspects, re-tested.
"""
import itertools
import random
import sys

QUICK = '--quick' in sys.argv


# ------------------------------------------------------------------ fields
class GFp:
    def __init__(self, p):
        self.p, self.q, self.name = p, p, f'GF({p})'

    def add(self, a, b): return (a + b) % self.p
    def sub(self, a, b): return (a - b) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def neg(self, a): return (-a) % self.p
    def inv(self, a): return pow(a, self.p - 2, self.p)
    def of(self, n): return n % self.p
    def elems(self): return range(self.p)


class GF2m:
    def __init__(self, m, poly):
        self.m, self.poly, self.q, self.name = m, poly, 2 ** m, f'GF(2^{m})'
        self._inv = {}

    def add(self, a, b): return a ^ b
    sub = add
    def neg(self, a): return a

    def mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a >> self.m:
                a ^= self.poly
        return r

    def inv(self, a):
        if a not in self._inv:
            r, e = 1, self.q - 2
            base = a
            while e:
                if e & 1:
                    r = self.mul(r, base)
                base = self.mul(base, base)
                e >>= 1
            self._inv[a] = r
        return self._inv[a]

    def of(self, n): return n & 1          # the prime field image of an integer
    def elems(self): return range(self.q)


class GFpm:
    """GF(p^m), elements encoded as integers in base p (coefficient of x^i = digit i)."""
    def __init__(self, p, m):
        self.p, self.m, self.q, self.name = p, m, p ** m, f'GF({p}^{m})'
        # find a monic irreducible of degree m by brute force (no root / no factor)
        for tail in itertools.product(range(p), repeat=m):
            poly = list(tail) + [1]          # coefficients low..high
            if self._irreducible(poly):
                self.poly = poly
                break
        self._mul = {}

    def _irreducible(self, poly):
        p, m = self.p, self.m
        # brute force: no monic factor of degree 1..m//2
        for d in range(1, m // 2 + 1):
            for tail in itertools.product(range(p), repeat=d):
                f = list(tail) + [1]
                r = list(poly)
                for i in range(len(r) - 1, d - 1, -1):
                    c = r[i]
                    if c:
                        for j in range(d + 1):
                            r[i - d + j] = (r[i - d + j] - c * f[j]) % p
                if not any(r[:d]):
                    return False
        return True

    def _dig(self, a):
        return [(a // self.p ** i) % self.p for i in range(self.m)]

    def _enc(self, d):
        return sum(c * self.p ** i for i, c in enumerate(d))

    def add(self, a, b): return self._enc([(x + y) % self.p for x, y in zip(self._dig(a), self._dig(b))])
    def sub(self, a, b): return self._enc([(x - y) % self.p for x, y in zip(self._dig(a), self._dig(b))])
    def neg(self, a): return self._enc([(-x) % self.p for x in self._dig(a)])

    def mul(self, a, b):
        key = (a, b)
        if key in self._mul:
            return self._mul[key]
        x, y = self._dig(a), self._dig(b)
        r = [0] * (2 * self.m)
        for i, u in enumerate(x):
            if u:
                for j, v in enumerate(y):
                    r[i + j] = (r[i + j] + u * v) % self.p
        for i in range(2 * self.m - 1, self.m - 1, -1):
            c = r[i]
            if c:
                for j in range(self.m + 1):
                    r[i - self.m + j] = (r[i - self.m + j] - c * self.poly[j]) % self.p
        out = self._enc(r[:self.m])
        self._mul[key] = out
        return out

    def inv(self, a):
        r, e, base = 1, self.q - 2, a
        while e:
            if e & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            e >>= 1
        return r

    def of(self, n): return n % self.p
    def elems(self): return range(self.q)


def rank(K, M):
    M = [list(r) for r in M]
    rk, ncol = 0, (len(M[0]) if M else 0)
    for col in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = K.inv(M[rk][col])
        M[rk] = [K.mul(iv, x) for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col]
                M[i] = [K.sub(x, K.mul(f, y)) for x, y in zip(M[i], M[rk])]
        rk += 1
        if rk == len(M):
            break
    return rk


def nullspace(K, M, n):
    M = [list(r) for r in M]
    piv, rk = [], 0
    for col in range(n):
        p_ = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if p_ is None:
            continue
        M[rk], M[p_] = M[p_], M[rk]
        iv = K.inv(M[rk][col])
        M[rk] = [K.mul(iv, x) for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col]
                M[i] = [K.sub(x, K.mul(f, y)) for x, y in zip(M[i], M[rk])]
        piv.append(col)
        rk += 1
    out = []
    for fc in [c for c in range(n) if c not in piv]:
        v = [0] * n
        v[fc] = 1
        for r, pc in enumerate(piv):
            v[pc] = K.neg(M[r][fc])
        out.append(v)
    return out


PL = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def wedge(K, x, y):
    return [K.sub(K.mul(x[i], y[j]), K.mul(x[j], y[i])) for i, j in PL]


def lincomb(K, cs, vs):
    out = [0] * len(vs[0])
    for c, v in zip(cs, vs):
        out = [K.add(o, K.mul(c, x)) for o, x in zip(out, v)]
    return out


def proj_points(K, basis):
    """all points of P(span basis) over K, one representative each."""
    d = len(basis)
    pts = []
    for cs in itertools.product(K.elems(), repeat=d):
        nz = next((c for c in cs if c), None)
        if nz is None or nz != 1:
            continue
        pts.append(lincomb(K, cs, basis))
    return pts


def rand_point(K, rng, basis):
    while True:
        cs = [rng.randrange(K.q) for _ in basis]
        if any(cs):
            return lincomb(K, cs, basis)


E = [[int(i == j) for j in range(4)] for i in range(4)]
e0, e1, e2, e3 = E
FR = {'i': ([e0, e1, e2], [e1, e2, e3]), 'ii': ([e0, e2, e3], [e1, e2, e3]),
      'iii': ([e0, e1, e3], [e0, e2, e3]), 'iv': ([e0, e1, e3], [e0, e1, e3])}
MLINE = {'i': [e1, e2], 'ii': [e2, e3], 'iii': [e0, e3], 'iv': [e0, e1, e3]}
GEN_LAM = {'i': [2, 3, 4, 5], 'ii': [2, 3, 4, 5], 'iii': [1, 3, 4, 5], 'iv': [2, 3, 4, 5]}
HAND = {'i': [0, 0, 0, 0], 'ii': [1, 0, 0, 0], 'iii': [1, 0, 0, 0], 'iv': [0, 3, 0, 0]}

bad = 0


def report(ok, msg):
    global bad
    bad += not ok
    print(f'  {"OK  " if ok else "FAIL"} {msg}')


def lines_of(K, pts):
    return [wedge(K, pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def span_lam(K, L):
    return rank(K, [l for l in L if any(l)]) if any(any(l) for l in L) else 0


# ------------------------------------------------------------------ [A] (MC-134)
def check_A(K):
    f = [1, 1, 1, 0]
    ad = lambda *v: [sum(t) for t in zip(*v)]  # noqa: E731
    ng = lambda v: [-x for x in v]              # noqa: E731
    rows = {
        '(a) n=3': ([e0, e1, e2], True, 3), '(a) n=4': ([e0, e1, e2, e3], True, 4),
        '(a) n=5': ([e0, e1, e2, e3, ad(e1, e3)], True, 5),
        '(a) n=6': ([e0, e1, e2, e3, ad(e1, e3), ad(e0, e2)], True, 6),
        '(b) k=2 ne': ([e0, e1, e2, e3], False, 3),
        '(b) k=3 ne': ([e0, e1, ad(e1, e3), e2, e3], False, 4),
        '(b) k=4 ne': ([e0, e1, e3, e0, e2, e3], False, 5),
        '(b) k=5 ne': ([e0, e1, e3, e0, ad(e1, e2), e2, e3], False, 6),
        '(b) k=2 eq': ([e0, e1, e2, f], False, 3),
        '(b) k=3 eq': ([e0, e1, e3, e2, f], False, 4),
        '(b) k=4 eq': ([e0, e1, e3, e0, e2, f], False, 5),
        '(b) k=5 eq': ([e0, e1, e3, ad(e2, e3), e0, e2, f], False, 6),
        '(c) k=2': ([e0, e1, e2], True, 3), '(c) k=3': ([e0, e1, e3, e2], True, 4),
        '(c) k=4': ([e0, e1, e3, ad(e1, e2), e2], True, 5),
        '(c) k=5': ([e0, e1, ad(e1, e2), e3, ad(e0, e3), e2], True, 6),
    }
    # the insertion step for k >= 6: points e0 + j e3 between x2 = e3 and x3 = e0 of the
    # (b) k = 5 frame; in characteristic p the point with p | j equals e0 (noted, harmless)
    allok = True
    for name, (pts, closed, want) in rows.items():
        P = [[K.of(x) for x in v] for v in pts]
        L = lines_of(K, P + ([P[0]] if closed else []))
        r = span_lam(K, L)
        allok &= (r == want)
        if r != want:
            print(f'    {K.name} {name}: rank {r} != {want}')
    report(allok, f'[A] {K.name}: all 16 (MC-134) configurations have the claimed rank')
    # (b) k = 6..9 by insertion on e3 e0
    ok6 = True
    for extra in range(1, 5):
        mids = [E[3]] + [[1, 0, 0, K.of(j)] for j in range(1, extra + 1)] + [E[0]]
        P = [e0, e1] + mids + [[0, 1, 1, 0], e2, e3]
        P = [[K.of(x) for x in v] for v in P]
        ok6 &= span_lam(K, lines_of(K, P)) == 6
    report(ok6, f'[A] {K.name}: insertion k = 6..9 keeps rank 6')


# ------------------------------------------------------------------ [B] intersections
def placements(K, orb, k, rng, cap):
    A, B = FR[orb]
    if k == 1:
        if K.q ** len(MLINE[orb]) <= 4000:
            for x in proj_points(K, MLINE[orb]):
                yield [e0, x, e3]
        else:
            for _ in range(cap):
                yield [e0, rand_point(K, rng, MLINE[orb]), e3]
        return
    tot = (K.q ** 3) ** 2 * (K.q ** 4) ** (k - 2)
    if tot <= cap:
        PA, PB, P3 = proj_points(K, A), proj_points(K, B), proj_points(K, E)
        for x1 in PA:
            for mids in itertools.product(P3, repeat=k - 2):
                for xk in PB:
                    yield [e0, x1] + list(mids) + [xk, e3]
    else:
        for _ in range(cap):
            yield ([e0, rand_point(K, rng, A)] + [rand_point(K, rng, E) for _ in range(k - 2)]
                   + [rand_point(K, rng, B), e3])


def check_B(K, cap):
    rng = random.Random(f'readerB:B:{K.name}')
    for orb in FR:
        row = []
        for k in range(1, 5):
            perps, acc, rej = [], 0, 0
            lower = None
            if orb == 'ii' and k == 1:
                lower = [wedge(K, e2, e3)]
            if orb == 'iii' and k == 1:
                lower = [wedge(K, e0, e3)]
            if orb == 'iv' and k == 2:
                A = FR['iv'][0]
                lower = [wedge(K, A[0], A[1]), wedge(K, A[0], A[2]), wedge(K, A[1], A[2])]
            for pts in placements(K, orb, k, rng, cap):
                L = [l for l in lines_of(K, pts) if any(l)]
                if span_lam(K, L) != GEN_LAM[orb][k - 1]:
                    rej += 1
                    continue
                acc += 1
                if lower is not None:
                    assert rank(K, L + lower) == rank(K, L), ('hand lower bound not in Lambda', orb, k)
                perps.extend(nullspace(K, L, 6))
                if len(perps) > 60:                      # compress to a row basis
                    perps = basis_rows(K, perps)
            cap_dim = 6 - rank(K, perps) if perps else 6
            ok = acc > 0 and cap_dim == HAND[orb][k - 1]
            row.append(f'k={k}: {cap_dim} (acc {acc}, rej {rej})')
            report(ok, f'[B] {K.name} orbit ({orb}) k={k}: guarded cap {cap_dim}, hand {HAND[orb][k-1]}'
                       f' (span-generic placements {acc}, deficient {rej})')


def basis_rows(K, M):
    """a row basis of M (reduced)."""
    M = [list(r) for r in M]
    out, rk = [], 0
    ncol = len(M[0])
    for col in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = K.inv(M[rk][col])
        M[rk] = [K.mul(iv, x) for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col]
                M[i] = [K.sub(x, K.mul(f, y)) for x, y in zip(M[i], M[rk])]
        rk += 1
    return M[:rk]


# ------------------------------------------------------------------ [C] (MC-138)
def lie_on(K, X, c):
    """derivation action of X (4x4, entries in K) on the 2-form c."""
    out = [0] * 6
    for kk, (i, j) in enumerate(PL):
        if not c[kk]:
            continue
        Xi = [X[r][i] for r in range(4)]
        Xj = [X[r][j] for r in range(4)]
        v = [K.add(a, b) for a, b in zip(wedge(K, Xi, E[j]), wedge(K, E[i], Xj))]
        out = [K.add(o, K.mul(c[kk], x)) for o, x in zip(out, v)]
    return out


def check_C(K):
    cases = {  # allowed[col] = rows r with E_{r,col} in Lie S; x0; strata {name: (pred, s)}
        'i': ({0: [0], 1: [1, 2], 2: [1, 2], 3: [3]}, [1, 1, 0, 0], [0, 0, 1, 1],
              {'l1 != 0': (lambda l: l[1] != 0, 5), 'l1 = 0, l0 l2 != 0': (lambda l: l[1] == 0 and l[0] and l[2], 4),
               'L0': (lambda l: l[1] == 0 and l[2] == 0 and l[0], 2),
               'L2': (lambda l: l[0] == 0 and l[1] == 0 and l[2], 2)}),
        'ii': ({0: [0], 1: [1, 2, 3], 2: [2, 3], 3: [3]}, [1, 0, 1, 0], [0, 1, 0, 0],
               {'l0 l1 l2 != 0': (lambda l: l[0] and l[1] and l[2], 6),
                'l0 l2 = 0 != l1': (lambda l: l[1] and not (l[0] and l[2]), 5),
                'l1 = 0, l0 l2 != 0': (lambda l: l[1] == 0 and l[0] and l[2], 4),
                'L0': (lambda l: l[1] == 0 and l[2] == 0 and l[0], 2),
                'L2': (lambda l: l[0] == 0 and l[1] == 0 and l[2], 2)}),
    }
    for orb, (allowed, x1, x2, strata) in cases.items():
        gens = []
        for col, rows in allowed.items():
            for r_ in rows:
                X = [[0] * 4 for _ in range(4)]
                X[r_][col] = 1
                gens.append(X)
        Ls = [wedge(K, e0, x1), wedge(K, x1, x2), wedge(K, x2, e3)]
        # open orbit: tangent rank on P(pi_a) x P(pi_b) at x0
        A, B = FR[orb]
        tang = []
        for X in gens:
            v1 = [sum(X[i][j] * x1[j] for j in range(4)) for i in range(4)]
            v2 = [sum(X[i][j] * x2[j] for j in range(4)) for i in range(4)]
            tang.append([K.of(t) for t in v1 + v2])
        tr = rank(K, tang + [[K.of(t) for t in x1] + [0] * 4, [0] * 4 + [K.of(t) for t in x2]]) - 2
        report(tr == 4, f'[C] {K.name} orbit ({orb}): tangent rank on 2-ear placements at x0 = {tr}')
        for name, (pred, s) in strata.items():
            worst, n = 99, 0
            for l in itertools.product(K.elems(), repeat=3):
                if not any(l) or not pred(l):
                    continue
                y = lincomb(K, list(l), Ls)
                T = [y] + [lie_on(K, X, y) for X in gens]
                worst = min(worst, rank(K, T))
                n += 1
            report(n > 0 and worst >= s, f'[C] {K.name} orbit ({orb}) {name}: min rank{{y, Xy}} over '
                                          f'{n} points = {worst} (need >= {s})')


# ------------------------------------------------------------------ [D], [E]
def subspaces(K, dim, rng, cap):
    """F_q-rational subspaces of K^6 of the given dim: all if few, else seeded sample."""
    seen = set()
    npts = (K.q ** 6 - 1) // (K.q - 1)
    ncomb = 1
    for i in range(dim):
        ncomb = ncomb * (npts - i) // (i + 1)
    if ncomb <= 200000:
        vecs = proj_points(K, [[int(i == j) for j in range(6)] for i in range(6)])
        for combo in itertools.combinations(vecs, dim):
            if rank(K, list(combo)) < dim:
                continue
            key = tuple(map(tuple, basis_rows(K, list(combo))))
            if key in seen:
                continue
            seen.add(key)
            yield [list(r) for r in key]
    else:
        for _ in range(cap):
            while True:
                M = [[rng.randrange(K.q) for _ in range(6)] for _ in range(dim)]
                if rank(K, M) == dim:
                    break
            yield basis_rows(K, M)


def meets(K, rho, L):
    return rank(K, rho + L) < len(rho) + rank(K, L)


def good_at(K, rho, pts_iter, k, lam):
    target = max(0, len(rho) + k - 5)
    for pts in pts_iter:
        L = [l for l in lines_of(K, pts) if any(l)]
        if span_lam(K, L) != lam:
            continue
        inter = len(rho) + lam - rank(K, rho + L)
        if inter == target:
            return True
    return False


def check_D(K, big, cap):
    rng = random.Random(f'readerB:D:{K.name}')
    for orb in ('i', 'ii'):
        A, B = FR[orb]
        PA, PB = proj_points(K, A), proj_points(K, B)
        pl2 = [[e0, x1, x2, e3] for x1 in PA for x2 in PB]
        pl2 = [p for p in pl2 if span_lam(K, lines_of(K, p)) == 3]
        PenA = [wedge(K, e0, v) for v in A if v != e0]
        PenB = [wedge(K, v, e3) for v in B if v != e3]
        N = PenA + PenB
        for r in (1, 2, 3):
            fam_bad, cert_good, suspects, n = 0, 0, [], 0
            for rho in subspaces(K, r, rng, cap):
                n += 1
                inA = rank(K, rho + PenA) == len(rho)
                inB = rank(K, rho + PenB) == len(rho)
                inN = rank(K, rho + N) == rank(K, N)
                fam = inA or inB or (r == 3 and inN)
                g = good_at(K, rho, pl2, 2, 3)
                if fam:
                    assert not g, ('family member good', orb, r, rho)
                    fam_bad += 1
                elif g:
                    cert_good += 1
                else:
                    suspects.append(rho)
            # re-test suspects over the big field
            still = 0
            for rho in suspects:
                rng2 = random.Random(f'readerB:D2:{orb}:{rho}')
                it = ([e0, rand_point(big, rng2, A), rand_point(big, rng2, B), e3] for _ in range(200))
                if not good_at(big, rho, it, 2, 3):
                    still += 1
            report(still == 0, f'[D] {K.name} orbit ({orb}) r={r}: {n} rational rho; families {fam_bad} '
                               f'(all bad); certified good {cert_good}; small-field suspects {len(suspects)}, '
                               f'good over {big.name}: {len(suspects) - still}; unresolved {still}')


def check_E(K, big, cap):
    rng = random.Random(f'readerB:E:{K.name}')
    for orb in FR:
        A, B = FR[orb]
        PA, PB, P3 = proj_points(K, A), proj_points(K, B), proj_points(K, E)
        pl2 = [[e0, x1, x2, e3] for x1 in PA for x2 in PB]
        pl3 = [[e0, x1, y, x3, e3] for x1 in PA for y in P3 for x3 in PB]
        n, p2good, sus, unres = 0, 0, 0, 0
        for rho in subspaces(K, 2, rng, cap):
            n += 1
            if not good_at(K, rho, pl2, 2, 3):
                continue
            p2good += 1
            if good_at(K, rho, pl3, 3, 4):
                continue
            sus += 1
            rng2 = random.Random(f'readerB:E2:{orb}:{rho}')
            it = ([e0, rand_point(big, rng2, A), rand_point(big, rng2, E), rand_point(big, rng2, B), e3]
                  for _ in range(200))
            if not good_at(big, rho, it, 3, 4):
                unres += 1
        report(unres == 0, f'[E] {K.name} orbit ({orb}) r=2: {n} rational rho, (P2)-good {p2good}; '
                           f'(P3) not seen good over {K.name}: {sus}; unresolved over {big.name}: {unres}')


def main():
    big = GF2m(8, 0x11B)
    fields = [GFp(2), GFp(3), GFp(5), GFp(7), big]
    for K in fields:
        check_A(K)
    for K in [GFp(2), GFp(3), GFp(5), big]:
        check_B(K, cap=(3000 if QUICK else 20000))
    for K in [GFp(2), GFp(3), GFp(5)]:
        check_C(K)
    check_D(GFp(2), big, cap=0)
    if not QUICK:
        check_D(GFp(3), GFpm(3, 4), cap=1500)
    check_E(GFp(2), big, cap=0)
    print(f'charcheck.py: {"ALL OK" if not bad else f"{bad} FAILED"}')
    raise SystemExit(1 if bad else 0)


if __name__ == '__main__':
    main()
