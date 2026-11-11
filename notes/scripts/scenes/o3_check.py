"""O3 (PENCIL-SCENES) at theta(2,2,3): the face gradients of a scene over S_G
are an infinitesimal motion of the bar framework (G, q), and not every motion.

S_G: points V, one face N[v] per body v.  A scene gives each face an affine
function h_v(xi) = g_v . xi + c_v, with h_v(q_w) the same for every face v
through the point w.  Exact arithmetic (fractions.Fraction).  Prints

  dim F(q)                  the space of scenes, face planes as unknowns
  rank of gradient image    the scenes modulo constants
  dim motions of (G,q)      the bar framework's infinitesimal motions
  gradients are motions     (g_u - g_v) . (q_u - q_v) = 0 on every edge
  rank(image+translations), rank(image+rotation)
                            the translations lie in the image, the rotation
                            does not

Source: the appendix of notes/pencil-scenes/refs-liftings.md (2026-11-11).
Run: PYTHONHASHSEED=0 python3 notes/scripts/scenes/o3_check.py
"""
from fractions import Fraction as F
V = ['a','b','1','2','3','4']
E = [('a','1'),('1','b'),('a','2'),('2','b'),('a','3'),('3','4'),('4','b')]
q = {'a':(-2,0),'b':(2,1),'1':(0,1),'2':(0,-1),'3':(-1,2),'4':(1,3)}
N = {v:{v} for v in V}
for u,v in E: N[u].add(v); N[v].add(u)
ix = {v:i for i,v in enumerate(V)}
def rref(rows, n):
    M=[list(map(F,r)) for r in rows]; piv=[]; r=0
    for c in range(n):
        p=next((i for i in range(r,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; M[r]=[x/M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0: f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
    return M, piv
rank = lambda rows: len(rref(rows, len(rows[0]))[1])
def null(rows, n):
    M,piv=rref(rows,n); out=[]
    for fc in [c for c in range(n) if c not in piv]:
        x=[F(0)]*n; x[fc]=F(1)
        for i,pc in enumerate(piv): x[pc]=-M[i][fc]
        out.append(x)
    return out
n=3*len(V); rows=[]          # unknowns per face v: (g_x, g_y, c); h_v(xi) = g.xi + c
for w in V:                  # point w: h_v(q_w) equal for all faces v containing w
    fs=[v for v in V if w in N[v]]
    for v in fs[1:]:
        r=[0]*n
        for s,f in ((1,fs[0]),(-1,v)):
            k=3*ix[f]; r[k]+=s*q[w][0]; r[k+1]+=s*q[w][1]; r[k+2]+=s
        rows.append(r)
S=null(rows,n); print('dim F(q) =',len(S))
G=[[s[3*ix[v]+j] for v in V for j in (0,1)] for s in S]
print('rank of gradient image =',rank(G))
R=[]
for u,v in E:
    r=[0]*(2*len(V)); d=(q[u][0]-q[v][0],q[u][1]-q[v][1])
    r[2*ix[u]],r[2*ix[u]+1]=d; r[2*ix[v]],r[2*ix[v]+1]=-d[0],-d[1]; R.append(r)
print('dim motions of (G,q) =',2*len(V)-rank(R))
print('gradients are motions:',all(sum(F(a)*b for a,b in zip(r,g))==0 for g in G for r in R))
rot=[c for v in V for c in (-q[v][1],q[v][0])]; tr=[[1,0]*len(V),[0,1]*len(V)]
print('rank(image+translations) =',rank(G+tr),' rank(image+rotation) =',rank(G+[rot]))
