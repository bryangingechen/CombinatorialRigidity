"""Part C lifts against motions in 3-space, on cycles and one edge (PENCIL-SCENES recon (i)).

Run: PYTHONHASHSEED=0 python3 notes/scripts/scenes/lift_cycles.py
(no arguments; seed 7, fixed below; exact rationals)

Written by the 2026-11-11 simplification recon agent (question (i)); banked as written.
Report: notes/pencil-scenes/simplify-i.md, Step 1.

General points b_v in Q^4 on C_4..C_7 and K_2. The plane of a body is a 3-dimensional subspace
containing the points of its closed neighbourhood (their span on a cycle). Prints, per graph,
the dimension of the lift space (def:pencil-d-lift; trivial lifts have dimension 4) and of the
infinitesimal motions of the body-hinge structure with hinges b_u ^ b_v (trivial: 6).
"""
import random, itertools
from fractions import Fraction as Fr
random.seed(7)
def rank(rows):
    M=[list(map(Fr,r)) for r in rows]; rk=0
    ncol=len(M[0]) if M else 0
    for c in range(ncol):
        p=next((i for i in range(rk,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][c]!=0:
                f=M[i][c]/M[rk][c]; M[i]=[a-f*b for a,b in zip(M[i],M[rk])]
        rk+=1
    return rk
def rv(n): return [Fr(random.randint(-9,9)) for _ in range(n)]
def wedge(a,b): return [a[i]*b[j]-a[j]*b[i] for i,j in itertools.combinations(range(4),2)]
def run(name, n, edges):
    b=[rv(4) for _ in range(n)]
    nb={v:[v] for v in range(n)}
    for u,v in edges: nb[u].append(v); nb[v].append(u)
    # normal n_v of plane Pi_v (contains closed nbhd, padded by random points): Pi_v = n_v^perp
    # forms on Pi_v = K^4* / K n_v ; lift: zeta_w = psi_v(b_w); dim liftSpace = dim Ltilde - n
    rows=[]
    for v in range(n):
        pts=[b[w] for w in nb[v]]
        assert rank(pts)==min(3,len(pts)),(name,v)
        for w in nb[v]:
            r=[0]*(5*n); r[w]=1
            for i in range(4): r[n+4*v+i]-=b[w][i]
            rows.append(r)
    lt=5*n-rank(rows)
    # degree-1 bodies: closed nbhd rank 2 < 3, plane padded: kernel of restriction is n-dim only if Pi_v fixed
    liftdim=lt-sum(4-min(3,len(nb[v])) for v in range(n)) + sum(3-min(3,len(nb[v])) for v in range(n))
    spanrank=rank(b)
    rows=[]
    for k,(u,v) in enumerate(edges):
        L=wedge(b[u],b[v])
        for i in range(6):
            r=[0]*(6*n+len(edges)); r[6*u+i]=1; r[6*v+i]=-1; r[6*n+k]=-L[i]; rows.append(r)
    mot=6*n+len(edges)-rank(rows)
    print(f"{name}: |V|={n} dim liftSpace={liftdim} (trivial lifts {spanrank if spanrank==4 else 4}) ; dim motions={mot} (trivial 6)")
for n in (4,5,6,7):
    run(f"C{n}", n, [(i,(i+1)%n) for i in range(n)])
run("K2", 2, [(0,1)])
