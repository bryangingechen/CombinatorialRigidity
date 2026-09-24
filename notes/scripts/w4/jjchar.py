#!/usr/bin/env python3
"""
jjchar.py -- Jackson--Jordan's equality in (MC-4) form, in POSITIVE
characteristic (workbook §(K-main), claim (MC-33)(ii); Literature section).

Claim exhibited.  Let `k` be a finite field and `G` a simple 2EC graph.  One
admissible planar picture `q : V -> k^2` (adjacent `q_u != q_w`, every closed
neighbourhood of size >= 3 non-collinear) with

    dim L(q) = 3 + def2(G)                                         (JJ at q)

proves `l0(G) = 3 + def2(G)` over EVERY infinite field of characteristic
`char k`.  Reason: `dim L(q) >= 3 + def2` at every admissible `q` over every
field ((MC-4)(b), a partition count); `L(q)` is the kernel of Step MC2's
`(z, h)` interpolation matrix `M(q)`, whose entries are polynomials over the
prime field; so a nonzero minor of the size exhibited at `q` is a nonzero
polynomial, and it does not vanish at generic points of any infinite field of
that characteristic.  By Step MC4's bijection `F(q) = L(q)` and the plane
duality of Step MC4, this is Jackson--Jordan's Thm 7.1 (rod-and-pin rank
`3|V| - 3 - def(G)`, TR-2006-06 p.21) in that characteristic, for that graph.

Asserted at EVERY drawn admissible `q`, in every field: (MC-4)(b)
`dim ker M(q) >= 3 + def2(G)`, and Step MC4's bijection in rank form,
`dim ker M(q) == dim F(q)`, `F(q)` the flex space (2 rows per edge:
`(P_u - P_w) . (x, y, 1) = 0` at both ends).  Both are field-free; a failure is
a bug.  A draw with `dim L(q) > 3 + def2` is only an upper bound for `l0`: it
is reported as "not exhibited", never as a counterexample.

Fields (`--fields`, default `2^16,3^10,101,10007`: characteristics 2, 3, 101,
10007).  All arithmetic is exact in the named field -- these ranks are the
object, NOT a proxy for a rational rank (`notes/scripts/README.md` §4
convention 2 concerns GF(p) used for Q; it does not apply here).
  `2^16`: GF(2)[X]/(X^16 + X^12 + X^3 + X + 1), log/exp tables of X.
  `3^10`: GF(3)[X]/(X^10 + X^3 + X + 2), log/exp tables of X and Zech's
          logarithms for addition.
  Both constructors ASSERT that X has multiplicative order exactly `q - 1`
  (so the polynomial is primitive, hence irreducible, and the quotient is a
  field with X a generator: the `q - 1` distinct powers of X are units); check
  the table multiplication (and, for `3^10`, the Zech addition) against the
  slow polynomial arithmetic at 2 000 seeded pairs; and check `a * a^-1 = 1`
  (and `a + (-a) = 0`) at every nonzero `a`.
  `P` (an integer): GF(P), P prime asserted by trial division.

Modes (run from the repository root; seeded, seed 20260924; writes nothing):

    python3 notes/scripts/w4/jjchar.py --selftest
    python3 notes/scripts/w4/jjchar.py --exh 7 [--fields 2^16,3^10,101,10007] [--tries 3]
    python3 notes/scripts/w4/jjchar.py --exh 8
    python3 notes/scripts/w4/jjchar.py --battery --thetas 12

`--selftest`: the field guards and their adversarial witnesses (§4 convention
6).  Must be REJECTED: over GF(2), X^4 + X^3 + X^2 + X + 1 (irreducible, X of
order 5, not primitive) and X^16 + 1 (reducible); over GF(3), X^2 + 1
(irreducible, X of order 4, not primitive) and X^2 + 2 (reducible); the
composite 10005.  Must be ACCEPTED (the negative controls): X^4 + X + 1 and
X^2 + X + 2, the two production polynomials, 101 and 10007.
`--exh N`: every simple 2EC graph on 3..N vertices (`maincomp.two_ec_graphs`).
`--battery`, `--thetas SMAX`: `maincomp`'s populations.

Sampler support (HARNESS.md *Evidence*): per graph and field, up to `--tries`
pictures `q`, each uniform on `k^{2|V|}` and rejected (at most 200 times) until
admissible; the least `dim L(q)` over the tries is reported, and the tries stop
at the first exhibition.  Seeded `random.Random('<seed>:<field>:<graph>')`.
The lines beginning `-- ` (one per field and population) are wall-clock,
exempt from byte-identity.
"""
import argparse
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from maincomp import def_k, two_ec_graphs, battery, thetas  # noqa: E402

SEED = 20260924


# ---------------------------------------------------------------- the fields

def clmul_mod(a, b, poly, k):
    """Carry-less product of a, b reduced mod the degree-k polynomial `poly`
    (the slow reference multiplication)."""
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> k:
            a ^= poly
    return r


class GF2k:
    """GF(2^k) = GF(2)[X]/(poly), elements as ints < 2^k, multiplication by
    log/exp tables of the generator X.  Refuses a non-primitive poly."""

    def __init__(self, k, poly):
        assert poly >> k == 1, 'poly must have degree k'
        self.k, self.q, self.poly = k, 1 << k, poly
        self.name = f'GF(2^{k})'
        self.char = 2
        exp = [0] * (2 * self.q)
        log = [0] * self.q
        x = 1
        for i in range(self.q - 1):
            if x == 1 and i > 0:
                raise ValueError(f'X has order {i} < 2^{k} - 1: poly {poly:#x} is not primitive')
            exp[i] = x
            log[x] = i
            x <<= 1
            if x >> k:
                x ^= poly
        if x != 1:
            raise ValueError(f'X^(2^{k}-1) != 1: poly {poly:#x} is reducible')
        for i in range(self.q - 1, 2 * self.q):
            exp[i] = exp[i - (self.q - 1)]
        self.exp, self.log = exp, log
        rng = random.Random(f'{SEED}:{self.name}:selfcheck')
        for _ in range(2000):
            a, b = rng.randrange(self.q), rng.randrange(self.q)
            assert self.mul(a, b) == clmul_mod(a, b, poly, k), 'log/exp multiplication wrong'
        for a in range(1, self.q):
            assert self.mul(a, self.inv(a)) == 1, 'inverse wrong'

    def mul(self, a, b):
        return self.exp[self.log[a] + self.log[b]] if a and b else 0

    def neg(self, a):
        return a

    def inv(self, a):
        return self.exp[(self.q - 1) - self.log[a]]

    def rand(self, rng):
        return rng.randrange(self.q)

    def rank(self, M):
        A = [r[:] for r in M]
        if not A:
            return 0
        rows, cols = len(A), len(A[0])
        exp, log, qm1 = self.exp, self.log, self.q - 1
        rk = 0
        for c in range(cols):
            pr = next((i for i in range(rk, rows) if A[i][c]), None)
            if pr is None:
                continue
            A[rk], A[pr] = A[pr], A[rk]
            li = qm1 - log[A[rk][c]]
            A[rk] = [exp[log[x] + li] if x else 0 for x in A[rk]]
            piv = A[rk]
            for i in range(rows):
                f = A[i][c]
                if i != rk and f:
                    lf = log[f]
                    A[i] = [x ^ (exp[log[y] + lf] if y else 0) for x, y in zip(A[i], piv)]
            rk += 1
            if rk == rows:
                break
        return rk


def is_prime(p):
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


class GFp:
    def __init__(self, p):
        if not is_prime(p):
            raise ValueError(f'{p} is not prime')
        self.p, self.name, self.char = p, f'GF({p})', p

    def neg(self, a):
        return (-a) % self.p

    def rand(self, rng):
        return rng.randrange(self.p)

    def rank(self, M):
        p = self.p
        A = [[x % p for x in r] for r in M]
        if not A:
            return 0
        rows, cols = len(A), len(A[0])
        rk = 0
        for c in range(cols):
            pr = next((i for i in range(rk, rows) if A[i][c]), None)
            if pr is None:
                continue
            A[rk], A[pr] = A[pr], A[rk]
            iv = pow(A[rk][c], p - 2, p)
            A[rk] = [x * iv % p for x in A[rk]]
            piv = A[rk]
            for i in range(rows):
                f = A[i][c]
                if i != rk and f:
                    A[i] = [(x - f * y) % p for x, y in zip(A[i], piv)]
            rk += 1
            if rk == rows:
                break
        return rk


class GFpk:
    """GF(p^k) = GF(p)[X]/(f), p odd, f = X^k + sum c_i X^i monic.  Elements
    are encoded as ints sum d_i p^i (digits d_i = coefficients of X^i), so 0
    and 1 are zero and one; `rank` works internally with discrete logs to the
    base X and Zech's table `zech[n] = log(1 + X^n)`.  Refuses a non-primitive f."""

    def __init__(self, p, k, coeffs):
        assert is_prime(p) and p > 2 and len(coeffs) == k
        self.p, self.k, self.q, self.c = p, k, p ** k, list(coeffs)
        self.name, self.char = f'GF({p}^{k})', p
        q = self.q
        exp = [0] * (q - 1)
        log = [-1] * q
        d = [1] + [0] * (k - 1)
        for i in range(q - 1):
            e = self._enc(d)
            if e == 1 and i > 0:
                raise ValueError(f'X has order {i} < {p}^{k} - 1: f is not primitive')
            exp[i] = e
            log[e] = i
            d = self._times_x(d)
        if self._enc(d) != 1:
            raise ValueError(f'X^({p}^{k}-1) != 1: f is reducible')
        self.exp, self.log, self.half = exp, log, (q - 1) // 2
        zech = [-1] * (q - 1)
        for n_ in range(q - 1):
            e = exp[n_]
            one_plus = e - e % p + (e % p + 1) % p
            zech[n_] = log[one_plus]
        self.zech = zech
        rng = random.Random(f'{SEED}:{self.name}:selfcheck')
        for _ in range(2000):
            a, b = rng.randrange(q), rng.randrange(q)
            assert self.mul(a, b) == self._mul_slow(a, b), 'log/exp multiplication wrong'
            assert self.add(a, b) == self._enc([(x + y) % p for x, y in zip(self._dec(a), self._dec(b))]), \
                'Zech addition wrong'
        for a in range(1, q):
            assert self.mul(a, self.inv(a)) == 1, 'inverse wrong'
            assert self.add(a, self.neg(a)) == 0, 'negation wrong'

    def _enc(self, d):
        return sum(x * self.p ** i for i, x in enumerate(d))

    def _dec(self, e):
        out = []
        for _ in range(self.k):
            out.append(e % self.p)
            e //= self.p
        return out

    def _times_x(self, d):
        t = d[-1]
        d = [0] + d[:-1]
        return [(x - t * ci) % self.p for x, ci in zip(d, self.c)] if t else d

    def _mul_slow(self, a, b):
        da, r = self._dec(a), [0] * self.k
        for coef in reversed(self._dec(b)):          # Horner in X over b's digits
            r = self._times_x(r)
            r = [(x + coef * y) % self.p for x, y in zip(r, da)]
        return self._enc(r)

    def mul(self, a, b):
        return self.exp[(self.log[a] + self.log[b]) % (self.q - 1)] if a and b else 0

    def inv(self, a):
        return self.exp[(-self.log[a]) % (self.q - 1)]

    def neg(self, a):
        return self.exp[(self.log[a] + self.half) % (self.q - 1)] if a else 0

    def add(self, a, b):
        if not a:
            return b
        if not b:
            return a
        la, lb = self.log[a], self.log[b]
        z = self.zech[(lb - la) % (self.q - 1)]
        return 0 if z < 0 else self.exp[(la + z) % (self.q - 1)]

    def rand(self, rng):
        return rng.randrange(self.q)

    def rank(self, M):
        log, zech, m, half = self.log, self.zech, self.q - 1, self.half
        A = [[log[x] for x in r] for r in M]        # -1 encodes zero
        if not A:
            return 0
        rows, cols = len(A), len(A[0])
        rk = 0
        for c in range(cols):
            pr = next((i for i in range(rk, rows) if A[i][c] >= 0), None)
            if pr is None:
                continue
            A[rk], A[pr] = A[pr], A[rk]
            lp = A[rk][c]
            A[rk] = [(x - lp) % m if x >= 0 else -1 for x in A[rk]]
            piv = A[rk]
            for i in range(rows):
                f = A[i][c]
                if i == rk or f < 0:
                    continue
                row = A[i]
                for j in range(cols):
                    y = piv[j]
                    if y < 0:
                        continue
                    t = (f + y + half) % m            # log of -f * piv[j]
                    x = row[j]
                    if x < 0:
                        row[j] = t
                    else:
                        z = zech[(t - x) % m]
                        row[j] = -1 if z < 0 else (x + z) % m
            rk += 1
            if rk == rows:
                break
        return rk


POLY16 = 0x1100B          # X^16 + X^12 + X^3 + X + 1
F3_10 = [2, 1, 0, 1, 0, 0, 0, 0, 0, 0]    # X^10 + X^3 + X + 2 over GF(3)


def make_field(spec):
    if spec == '2^16':
        return GF2k(16, POLY16)
    if spec == '3^10':
        return GFpk(3, 10, F3_10)
    return GFp(int(spec))


# ---------------------------------------------------------------- the matrices
# Entries are written with the field's own negation `Fd.neg` (the identity in
# characteristic 2), and `1` is every field's unit in its encoding.

def neg(Fd, a):
    return Fd.neg(a)


def interp_matrix(Fd, edges, V, q):
    """Step MC2's M(q): unknowns z (|V|) then h_v (3 per v); a row
    z_w - h_v . (x_w, y_w, 1) = 0 for every v and w in N[v]."""
    nb = neighbors(edges)
    idx = {v: i for i, v in enumerate(V)}
    n = len(V)
    rows = []
    for v in V:
        for w in [v] + sorted(nb.get(v, ()), key=str):
            r = [0] * (4 * n)
            r[idx[w]] = 1
            b = n + 3 * idx[v]
            r[b], r[b + 1], r[b + 2] = neg(Fd, q[w][0]), neg(Fd, q[w][1]), neg(Fd, 1)
            rows.append(r)
    return rows


def flex_matrix(Fd, edges, V, q):
    """F(q): rows (P_u - P_w) . (x, y, 1) = 0 at q_u and at q_w, per edge."""
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for (u, w) in edges:
        for pv in (q[u], q[w]):
            r = [0] * (3 * len(V))
            for kk, cf in enumerate((pv[0], pv[1], 1)):
                r[3 * idx[u] + kk] = cf
                r[3 * idx[w] + kk] = neg(Fd, cf)
            rows.append(r)
    return rows


def admissible(Fd, edges, V, q):
    nb = neighbors(edges)
    if any(q[u] == q[w] for (u, w) in edges):
        return False
    for v in V:
        N = [v] + list(nb.get(v, ()))
        if len(N) >= 3 and Fd.rank([[1, q[w][0], q[w][1]] for w in N]) < 3:
            return False
    return True


def exhibit(Fd, name, edges, d2, tries):
    """Least dim L(q) over up to `tries` admissible draws (stopping at 3 + d2),
    or None if no admissible q was found."""
    V = verts_of(edges)
    n = len(V)
    rng = random.Random(f'{SEED}:{Fd.name}:{name}')
    best = None
    for _ in range(tries):
        for _ in range(200):
            q = {v: (Fd.rand(rng), Fd.rand(rng)) for v in V}
            if admissible(Fd, edges, V, q):
                break
        else:
            continue
        dL = 4 * n - Fd.rank(interp_matrix(Fd, edges, V, q))
        dF = 3 * n - Fd.rank(flex_matrix(Fd, edges, V, q))
        assert dL >= 3 + d2, ('(MC-4)(b) fails', Fd.name, name, dL, d2)
        assert dL == dF, ('Step MC4 bijection F(q) = L(q) fails in rank form', Fd.name, name, dL, dF)
        best = dL if best is None else min(best, dL)
        if best == 3 + d2:
            break
    return best


# ---------------------------------------------------------------- modes

def selftest():
    bad = 0
    for label, ctor in (('X^4+X^3+X^2+X+1 (irreducible, not primitive)', lambda: GF2k(4, 0b11111)),
                        ('X^16+1 (reducible)', lambda: GF2k(16, 0x10001)),
                        ('X^2+1 over GF(3) (irreducible, not primitive)', lambda: GFpk(3, 2, [1, 0])),
                        ('X^2+2 over GF(3) (reducible)', lambda: GFpk(3, 2, [2, 0])),
                        ('10005 (composite)', lambda: GFp(10005))):
        try:
            ctor()
            print(f'NOT rejected: {label}  FAIL')
            bad += 1
        except ValueError as e:
            print(f'rejected: {label}: {e}')
    for label, ctor in (('X^4+X+1', lambda: GF2k(4, 0b10011)),
                        ('X^16+X^12+X^3+X+1', lambda: GF2k(16, POLY16)),
                        ('X^2+X+2 over GF(3)', lambda: GFpk(3, 2, [2, 1])),
                        ('X^10+X^3+X+2 over GF(3)', lambda: GFpk(3, 10, F3_10)),
                        ('101', lambda: GFp(101)), ('10007', lambda: GFp(10007))):
        Fd = ctor()
        print(f'accepted: {label} -> {Fd.name}')
    Fd = GF2k(4, 0b10011)
    assert [Fd.mul(Fd.exp[1], Fd.exp[i]) for i in range(3)] == [2, 4, 8]
    print(f'selftest: {"FAIL" if bad else "OK"}')
    return bad


def run(pname, pop, fields, tries):
    d2s = {name: def_k(edges, 3) for name, edges in pop}
    for Fd in fields:
        t0 = time.time()
        eq = 0
        bad = []
        for name, edges in pop:
            best = exhibit(Fd, name, edges, d2s[name], tries)
            if best == 3 + d2s[name]:
                eq += 1
            else:
                bad.append((name, best, 3 + d2s[name]))
        print(f'{Fd.name}: {pname}: {len(pop)} graphs: dim L(q) = 3 + def2 exhibited at {eq}; '
              f'not exhibited at {len(bad)} (an upper bound per draw, not a counterexample)', flush=True)
        for b in bad[:20]:
            print(f'    not exhibited: {b[0]} best dim L = {b[1]}, 3 + def2 = {b[2]}')
        print(f'-- {Fd.name} {pname}: {time.time() - t0:.1f} s', flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--battery', action='store_true')
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--fields', default='2^16,3^10,101,10007')
    ap.add_argument('--tries', type=int, default=3)
    a = ap.parse_args()
    bad = 0
    if a.selftest:
        bad += selftest()
    pops = []
    if a.battery:
        pops.append(('battery', battery()))
    if a.exh:
        pops.append((f'exh{a.exh}', two_ec_graphs(a.exh)))
    if a.thetas:
        pops.append((f'thetas{a.thetas}', thetas(a.thetas)))
    if not (a.selftest or pops):
        ap.error('name a mode')
    if pops:
        fields = [make_field(s) for s in a.fields.split(',')]
        print(f'jjchar: seed={SEED} tries={a.tries} fields={",".join(f.name for f in fields)}')
        for pname, pop in pops:
            run(pname, pop, fields, a.tries)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
