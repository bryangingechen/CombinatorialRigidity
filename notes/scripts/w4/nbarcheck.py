#!/usr/bin/env python3
"""nbarcheck.py (§(K-main) Steps MC17-MC18's second reading, 2026-09-25; ported from the reader's scratch).
readerE nbarcheck.py -- exact check of two linear-algebra facts used for
(MC-110)'s last bullet and for the proposed (NEW-X1):
 (1) along a curve of flag pairs (p_a, alpha(s); p_b, beta(s)) with
     alpha(s)(p_b) = s*phi1, beta(s)(p_a) = s*phi2 (the chord point at s = 0,
     case A: alpha(0), beta(0) independent), the limit of
     N(s) = Pen(p_a, pi_a(s)) + Pen(p_b, pi_b(s)) is
     Nbar = N0 + < phi1 * p_a ^ e_alpha + phi2 * p_b ^ e_beta >,
     N0 = Pen(p_a, pi_a(0)) + Pen(p_b, pi_b(0))   (e_alpha, e_beta: alpha(e_alpha)=1,
     beta(e_alpha)=0, alpha(e_beta)=0, beta(e_beta)=1);
 (2) every reachable limit pencil Pen(y0(t), sigma(t)) of (MC-108)(ii) for this
     direction lies in Nbar (so the conic of reachable pencils mod n spans
     P(Nbar/n)), and Nbar(theta) + Nbar(theta') = n^perp for theta != theta'.
The limit of a polynomial family of subspaces is computed exactly by
valuation Gaussian elimination over K[s]_(s).  Points p_a, p_b fixed (a
projective change of frame makes this general).  Exact Fractions; seeded
(random.Random('readerE:nbar')); 20 random instances."""
import random
from fractions import Fraction as F

PL = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def wedge(u, v): return [u[i]*v[j]-u[j]*v[i] for i, j in PL]
def rank(M):
    M = [r[:] for r in M if any(x != 0 for x in r)]; r = 0
    if not M: return 0
    for c in range(len(M[0])):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]/M[r][c]; M[i] = [a-f*b for a, b in zip(M[i], M[r])]
        r += 1
        if r == len(M): break
    return r
def kernel(M, n):
    # null space of rows M (vectors v with M v = 0)
    import copy
    A = [r[:] for r in M]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; inv = 1/A[r][c]; A[r] = [x*inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [a-f*b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
    out = []
    for fcol in [c for c in range(n) if c not in piv]:
        v = [F(0)]*n; v[fcol] = F(1)
        for i, c in enumerate(piv): v[c] = -A[i][fcol]
        out.append(v)
    return out
# polynomial vectors: list over coords of coefficient lists
def padd(a, b): L = max(len(a), len(b)); return [(a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0) for i in range(L)]
def pscale(a, c): return [c*x for x in a]
def pmul(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i+j] += x*y
    return out
def pwedge(u, v):  # u, v: 4 polynomials each
    return [padd(pmul(u[i], v[j]), pscale(pmul(u[j], v[i]), -1)) for i, j in PL]
def const(vec): return [c[0] if c else F(0) for c in vec]
def divs(vec): return [c[1:] if len(c) > 1 else [F(0)] for c in vec]
def limit_space(vecs, maxit=50):
    vecs = [v[:] for v in vecs]
    for _ in range(maxit):
        C = [const(v) for v in vecs]
        ker = kernel([list(col) for col in zip(*C)], len(C))  # combos of the vecs with zero const term
        if not ker: return C
        comb = ker[0]; k = next(i for i, x in enumerate(comb) if x != 0)
        new = [[F(0)] for _ in range(6)]
        for i, x in enumerate(comb):
            if x != 0: new = [padd(a, pscale(b, x)) for a, b in zip(new, vecs[i])]
        assert all(c[0] == 0 for c in new)
        vecs[k] = divs(new)
    raise RuntimeError
def main():
    rng = random.Random('readerE:nbar'); ok = 0
    R = lambda: F(rng.randint(-9, 9))
    for trial in range(20):
        pa = [F(1),F(0),F(0),F(0)]; pb = [F(0),F(1),F(0),F(0)]
        # alpha(0), beta(0) vanish on n^ = <e0,e1>, independent: alpha0 = (0,0,1,x), beta0 = (0,0,y,1)
        a0 = [F(0),F(0),F(1),R()]; b0 = [F(0),F(0),R(),F(1)]
        if rank([a0[2:], b0[2:]]) < 2: continue
        phi1, phi2 = R(), R()
        if phi1 == 0 and phi2 == 0: continue
        # alpha(s) = a0 + s a1 with a1(pa) = 0, a1(pb) = phi1; beta(s) = b0 + s b1, b1(pb) = 0, b1(pa) = phi2
        a1 = [F(0), phi1, R(), R()]; b1 = [phi2, F(0), R(), R()]
        def pen(p, al0, al1):   # basis of {p ^ u : alpha(s)(u) = 0} as polynomial vectors (via u = kernel of alpha(s) mod p)
            # kernel of the 1x4 polynomial row (al0 + s al1): use the three vectors u_ij = al_j e_i - al_i e_j
            al = [[al0[i], al1[i]] for i in range(4)]
            us = []
            for i in range(4):
                for j in range(i+1, 4):
                    u = [[F(0)] for _ in range(4)]; u[i] = al[j][:]; u[j] = pscale(al[i], -1); us.append(u)
            P = [[x] for x in p]
            return [pwedge(P, u) for u in us]
        vecs = pen(pa, a0, a1) + pen(pb, b0, b1)
        # generic rank 4 (orbit (i) for s != 0); reduce to 4 independent polynomial generators by checking a sample s
        Nbar = limit_space(select(vecs))
        # prediction
        ea = kernel([a0, b0, pa, pb][:0] + [ [b0[i] for i in range(4)] ], 4)  # placeholder, replaced below
        # e_alpha, e_beta in <e2,e3> with alpha0(e_alpha)=1, beta0(e_alpha)=0 etc.
        Mab = [[a0[2], a0[3]], [b0[2], b0[3]]]
        det = Mab[0][0]*Mab[1][1]-Mab[0][1]*Mab[1][0]
        inv = [[Mab[1][1]/det, -Mab[0][1]/det], [-Mab[1][0]/det, Mab[0][0]/det]]
        e_al = [F(0), F(0), inv[0][0], inv[1][0]]; e_be = [F(0), F(0), inv[0][1], inv[1][1]]
        N0 = [wedge(pa, u) for u in kernel([a0], 4)] + [wedge(pb, u) for u in kernel([b0], 4)]
        extra = [phi1*x + phi2*y for x, y in zip(wedge(pa, e_al), wedge(pb, e_be))]
        pred = N0 + [extra]
        good = rank(Nbar) == 4 and rank(pred) == 4 and rank(Nbar + pred) == 4
        # (2) reachable pencils for this direction lie in Nbar
        n = wedge(pa, pb)
        for t in [F(1,3), F(2), F(-5,7)]:
            y0 = [(1-t)*x + t*y for x, y in zip(pa, pb)]
            # v with alpha0(v) = -t phi1, beta0(v) = -(1-t) phi2, v in <e2,e3>
            rhs = [-t*phi1, -(1-t)*phi2]
            v = [F(0), F(0), inv[0][0]*rhs[0]+inv[0][1]*rhs[1], inv[1][0]*rhs[0]+inv[1][1]*rhs[1]]
            pen_t = [n, wedge(y0, v)]
            good &= rank(Nbar + pen_t) == 4
        # two directions span n^perp: Nbar(theta) + Nbar(theta') has rank 5 when theta != theta'
        extra2 = [phi2*x + (phi1+1)*y for x, y in zip(wedge(pa, e_al), wedge(pb, e_be))]
        if phi1*(phi1+1) - phi2*phi2 != 0:
            good &= rank(N0 + [extra] + [extra2]) == 5
        ok += good
        print(f'trial {trial}: phi=({phi1},{phi2}) limit dim {rank(Nbar)}; matches prediction and holds the pencils: {good}')
    print('all good:', ok)
def select(vecs):
    # pick a maximal subset independent at a sample s (generic rank)
    s = F(3, 11); chosen = []; cur = []
    for v in vecs:
        ev = [sum(c*s**i for i, c in enumerate(comp)) for comp in v]
        if rank(cur + [ev]) > rank(cur): chosen.append(v); cur.append(ev)
    return chosen
if __name__ == '__main__':
    main()
