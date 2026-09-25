#!/usr/bin/env python3
"""capcheck.py (§(K-main) Steps MC17-MC18's second reading, 2026-09-25; ported from the reader's scratch).
readerE capcheck.py -- an independent re-check (not importing earstep/lamguard)
of the ear-span intersections  cap_k = intersection of Lambda_k(y) over
placements y OF GENERIC SPAN, per flag orbit (i)-(iv) and k = 1..4, in the
frame of (MC-92) (p_a = e0, p_b = e3), plus (MC-92)'s hand placements and
(MC-97)'s orbit-(ii), k = 1 pencil identity.  Exact Fractions; seeded
(random.Random('readerE:capcheck')); run from anywhere.

A placement (k = 1): x in pi_a cap pi_b; (k >= 2): x1 in pi_a, x_k in pi_b,
middle points free in K^4.  Lambda_k(y) = span of the k+1 chain lines
p_a x1, x1 x2, ..., x_k p_b (Pluecker order 01,02,03,12,13,23).  A draw is
used only if dim Lambda_k(y) equals the generic value; rejected draws are
counted.  cap = 0 over used draws PROVES the generic intersection is 0; a
nonzero cap is an upper bound only (the hand arguments give equality)."""
import random
from fractions import Fraction as F
from itertools import combinations

def wedge(u, v):
    return [u[i]*v[j]-u[j]*v[i] for i, j in [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]]

def rref(M):
    M = [r[:] for r in M]; piv = []; r = 0
    ncol = len(M[0]) if M else 0
    for c in range(ncol):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]; M[r] = [x*inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f*b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == len(M): break
    return M[:r], piv

def rank(M): return len(rref(M)[0]) if M else 0

def kernel(M, n):
    if not M: return [[F(int(i == j)) for j in range(n)] for i in range(n)]
    R, piv = rref(M); free = [c for c in range(n) if c not in piv]; out = []
    for f in free:
        v = [F(0)]*n; v[f] = F(1)
        for i, c in enumerate(piv): v[c] = -R[i][f]
        out.append(v)
    return out

def meet(spaces):
    """intersection of subspaces of K^6 given by spanning lists"""
    perps = []
    for S in spaces: perps += kernel(S, 6)       # annihilators (dot pairing)
    return kernel(perps, 6)

e = [[F(int(i == j)) for j in range(4)] for i in range(4)]
pa, pb = e[0], e[3]
# planes as normals n (pi = {X : n.X = 0}); pi_a contains e0, pi_b contains e3
ORB = {
    'i':   ([0,0,0,1], [1,0,0,0]),        # pi_a=<e0,e1,e2>, pi_b=<e1,e2,e3>
    'ii':  ([0,1,0,0], [1,0,0,0]),        # pi_a=<e0,e2,e3> (has p_b), pi_b=<e1,e2,e3>
    'iii': ([0,0,1,0], [0,1,0,0]),        # pi_a=<e0,e1,e3>, pi_b=<e0,e2,e3>
    'iv':  ([0,1,0,0], [0,1,0,0]),        # pi_a=pi_b=<e0,e2,e3>
}
def pt_in(rng, normals):
    B = kernel([[F(x) for x in n] for n in normals], 4)
    c = [F(rng.randint(-7, 7)) for _ in B]
    return [sum(ci*b[j] for ci, b in zip(c, B)) for j in range(4)]

def lines(pts): return [wedge(pts[i], pts[i+1]) for i in range(len(pts)-1)]

def generic_lambda(orb, k): return 1 if (k == 1 and orb == 'iii') else min(k+1, 6)

def main():
    rng = random.Random('readerE:capcheck')
    for orb, (na, nb) in ORB.items():
        for k in range(1, 5):
            lam0 = generic_lambda(orb, k); used = []; rej = 0
            while len(used) < 30:
                if k == 1: pts = [pa, pt_in(rng, [na, nb]), pb]
                else: pts = [pa, pt_in(rng, [na])] + [[F(rng.randint(-7,7)) for _ in range(4)] for _ in range(k-2)] + [pt_in(rng, [nb]), pb]
                L = lines(pts)
                if rank(L) != lam0: rej += 1; continue
                used.append(L)
            c = meet(used)
            print(f'orbit ({orb:>3}) k={k}: lambda={lam0}  dim cap={len(c)}  basis={[[str(x) for x in v] for v in c]}  rejected={rej}')
    # (MC-97): orbit (ii), k = 1 -- Lambda_1(y) = Pen(y, pi_a) and contains m
    na, nb = ORB['ii']
    mb = kernel([[F(x) for x in na], [F(x) for x in nb]], 4)
    m = wedge(mb[0], mb[1])
    ok = True
    for (s, t) in [(1,2),(3,-1),(-2,5),(4,7),(1,0)]:
        y = [s*u + t*w for u, w in zip(mb[0], mb[1])]
        L = lines([pa, y, pb])
        if rank(L) == 2: ok &= rank(L + [m]) == 2
        else: print('  deficient placement (s,t)=', (s,t), 'rank', rank(L))
    print('orbit (ii), k=1: m in every generic-span Lambda_1(y):', ok)
    # (MC-92) hand placements, k = 2
    add = lambda u, v: [a+b for a, b in zip(u, v)]
    hand = {'i': [(e[1],e[2]), (e[2],e[1]), (add(e[0],e[1]), add(e[2],e[3]))],
            'ii': [(e[2],e[1]), (add(e[0],e[2]),e[1]), (e[2],add(e[1],e[2])), (add(e[2],e[3]),e[1])]}
    for orb, pls in hand.items():
        na, nb = ORB[orb]; spans = []
        for x1, x2 in pls:
            assert sum(F(a)*b for a,b in zip(na,x1)) == 0 and sum(F(a)*b for a,b in zip(nb,x2)) == 0
            L = lines([pa, x1, x2, pb]); assert rank(L) == 3; spans.append(L)
        run = []
        for j in range(1, len(spans)+1): run.append(len(meet(spans[:j])))
        print(f'(MC-92) orbit ({orb}) hand placements: running dim of the intersection = {run}')

if __name__ == '__main__':
    main()
