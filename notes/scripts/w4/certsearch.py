# throwaway search for explicit chain placements with small integer points whose
# Pluecker vectors have a maximal minor equal to +-1 (characteristic-free)
import itertools
from fractions import Fraction as F
PL = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def w(x,y): return [x[i]*y[j]-x[j]*y[i] for i,j in PL]
def det(M):
    M=[[F(x) for x in r] for r in M]; n=len(M); d=F(1)
    for c in range(n):
        p=next((i for i in range(c,n) if M[i][c]!=0),None)
        if p is None: return F(0)
        if p!=c: M[c],M[p]=M[p],M[c]; d=-d
        d*=M[c][c]
        for i in range(c+1,n):
            f=M[i][c]/M[c][c]; M[i]=[a-f*b for a,b in zip(M[i],M[c])]
    return d
def maxminors(L):
    k=len(L); out=set()
    for cols in itertools.combinations(range(6),k):
        out.add(abs(det([[l[c] for c in cols] for l in L])))
    return out
e=[[int(i==j) for j in range(4)] for i in range(4)]
cand=[p for p in itertools.product([0,1],repeat=4) if any(p)]
cand1=[p for p in itertools.product([-1,0,1],repeat=4) if any(p)]
def nnz(L): return sum(1 for l in L for x in l if x)
# closed polygon n=6: e0,e1,e2,e3,u,v
best=None
for u in cand:
  for v in cand:
    pts=[e[0],e[1],e[2],e[3],list(u),list(v)]
    L=[w(pts[i],pts[(i+1)%6]) for i in range(6)]
    d=abs(det(L))
    if d==1:
      s=nnz(L)
      if best is None or s<best[0]: best=(s,u,v)
print('polygon6',best)
best=None
for u in cand:
    pts=[e[0],e[1],e[2],e[3],list(u)]
    L=[w(pts[i],pts[(i+1)%5]) for i in range(5)]
    if 1 in maxminors(L):
      s=nnz(L)
      if best is None or s<best[0]: best=(s,u)
print('polygon5',best)
# open chain frame p_a=e0,x1=e1,xk=e2,p_b=e3, mids
for k in (3,4,5):
  best=None
  for mids in itertools.product(cand,repeat=k-2):
    pts=[e[0],e[1]]+[list(m) for m in mids]+[e[2],e[3]]
    L=[w(pts[i],pts[i+1]) for i in range(len(pts)-1)]
    if 1 in maxminors(L):
      s=nnz(L)
      if best is None or s<best[0]: best=(s,mids)
  print('open',k,best)
# pi_a=pi_b: p_a=e0,x1=e1,xk=e2? need p_a,x1,xk,p_b general in plane X3=0: p_b=e0+e1+e2
pb=[1,1,1,0]
for k in (2,3,4,5):
  best=None
  for mids in itertools.product(cand,repeat=k-2):
    pts=[e[0],e[1]]+[list(m) for m in mids]+[e[2],pb]
    L=[w(pts[i],pts[i+1]) for i in range(len(pts)-1)]
    if 1 in maxminors(L):
      s=nnz(L)
      if best is None or s<best[0]: best=(s,mids)
  print('coplanar',k,best)
# closed ear: p_a=e0, x1=e1, xk=e2 in X3=0, closed
for k in (2,3,4,5):
  best=None
  for mids in itertools.product(cand,repeat=k-2):
    pts=[e[0],e[1]]+[list(m) for m in mids]+[e[2]]
    L=[w(pts[i],pts[(i+1)%len(pts)]) for i in range(len(pts))]
    if 1 in maxminors(L):
      s=nnz(L)
      if best is None or s<best[0]: best=(s,mids)
  print('closed',k,best)
