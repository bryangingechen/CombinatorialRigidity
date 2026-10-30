#!/usr/bin/env python3
"""Structured adversarial subspaces rho for SHORT-CORE (workbook S6-S8, S12), exact over Q.

    python3 notes/attacks/short-core/drivers/adversarial_rho.py 1 15

Written by the session-1 independent reader of S6-S8 and committed by the attack. Per trial and
kappa in {1, 2, 3}, it draws base data (tangent_check.planes), then per k in {3, 4, 5} draws 6
subspaces rho as sums of 1-3 structured blocks or random subspaces of them: the stars of p_a, p_b,
a random point and random points of Pi_a and Pi_b; Lambda^2 of Pi_a, Pi_b, L = Pi_a & Pi_b and
Pi_a + Pi_b; Pi_a^Pi_b, Pi_a^V, Pi_b^V, L^V and L^E; <p_a,p_b>^E; Lambda^2<p_a,p_b,e>. At a
random ear datum it counts a failure when W = rho + J is proper and holds both stars.
The draws are not guarded by S6-S8's independence conditions, so a failure outside
(kappa, k) = (3, 3) would need that check before it counts against S6-S8. One draw per rho, so this
is evidence about the sampler's support.
"""
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tangent_check as tc  # noqa: E402

N=5
E=[[F(int(i==j)) for j in range(N)] for i in range(N)]
def w2(u,v): return tc.tovec(tc.wedge(u,v),2)
def lin(vs,rng): return tc.comb(vs,rng)
def blk_star(p): return [w2(p,e) for e in E]
def blk_L2(B): return [w2(u,v) for u,v in itertools.combinations(B,2)]
def blk_AB(A,B): return [w2(u,v) for u in A for v in B]
def blk_AV(A): return [w2(u,e) for u in A for e in E]
def basis(vs):
    out=[]
    for v in vs:
        if tc.rank(out+[v])>len(out): out.append(v)
    return out
def lin10(vs,rng):
    c=[F(rng.randint(-9,9)) for _ in vs]
    if all(x==0 for x in c): c[0]=F(1)
    return [sum(ci*v[j] for ci,v in zip(c,vs)) for j in range(10)]
def randsub(blk,dim,rng):
    b=basis(blk); dim=min(dim,len(b))
    return [lin10(b,rng) for _ in range(dim)]
def run(seed,trials):
    rng=random.Random(seed); fails={}; cnt={}
    for _ in range(trials):
        for kappa in (1,2,3):
            Pa,Pb=tc.planes(rng,kappa)
            pa,pb=lin(Pa,rng),lin(Pb,rng)
            L=[]  # basis of intersection
            # crude: compute intersection via nullspace
            ns=tc.nullspace([[Pa[i][j] for i in range(3)]+[-Pb[i][j] for i in range(3)] for j in range(N)],6)
            L=[[sum(x[i]*Pa[i][j] for i in range(3)) for j in range(N)] for x in ns]
            e=tc.rvec(rng)
            blocks=[blk_star(pa),blk_star(pb),blk_L2(Pa),blk_L2(Pb),blk_AB(Pa,Pb),blk_AV(Pa),blk_AV(Pb),
                    blk_star(e),blk_AV(L),blk_L2(L) if len(L)>=2 else [],blk_L2(Pa+Pb),blk_AB(L,E),
                    blk_star(lin(Pa,rng)),blk_star(lin(Pb,rng)), blk_AB([pa,pb],E), blk_L2([pa,pb,e])]
            blocks=[b for b in blocks if b]
            for k in (3,4,5):
                for _r in range(6):
                    chosen=rng.sample(blocks,rng.randint(1,3))
                    rho=[]
                    for b in chosen:
                        rho+= b if rng.random()<0.5 else randsub(b,rng.randint(1,9),rng)
                    y=tc.ear(rng,k,Pa,Pb)
                    W=rho+tc.joins(k,pa,pb,y)
                    S=tc.star(y[1])+tc.star(y[3])
                    rW=tc.rank(W)
                    fail = rW<10 and tc.rank(W+S)==rW
                    cnt[(kappa,k)]=cnt.get((kappa,k),0)+1
                    if fail: fails[(kappa,k)]=fails.get((kappa,k),0)+1
    print("draws",sorted(cnt.items()))
    print("fails",sorted(fails.items()))
if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
