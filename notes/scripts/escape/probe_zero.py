"""
Decisive probe for route (b): does the escape polynomial  E(config) = r . (bhat ^ chat)
have an in-stratum zero locus (=> escape is genuinely generic, not a structural
identity), or is it never zero (=> a pure algebraic certificate exists)?

Method: fix a generic pencil realization of G' = (dbl-subdiv K4)^{ab}_v, then move ONE
free parameter t (a's position along the meet line Pi(b) ^ Pi(c)) exactly over Q.
Sample E(t) at many rational t; E(t) is a rational function of t.  If E takes both
signs (=> a real rational zero exists inside the stratum), route (b)-as-identity is
dead.  Also do the same sweep for a hub-plane rotation parameter.
"""
from fractions import Fraction as F
import random
import pencil_escape as pe
from pencil_escape import (double_subdivide, build_rigidity, rank, left_nullspace,
                           wedge2, hat, dot)

def K4():
    vs=[0,1,2,3]; return [(i,j) for i in vs for j in vs if i<j]

def build_config_parametric(seed):
    """Return a function cfg(t) producing G' data with a's meet-line param = t,
    everything else fixed by `seed`."""
    base_edges = K4()
    edges, hubs, chains, allverts = double_subdivide(base_edges)
    (u,x,y,w) = chains[0]
    b,c,a,v = u,w,y,x
    edges2 = [(p,q) for (p,q) in edges if p!=v and q!=v]
    edges2.append((b,a))
    Vp = sorted(set(sum(([p,q] for p,q in edges2), [])))
    nb = {vv:set() for vv in Vp}
    for p,q in edges2:
        nb[p].add(q); nb[q].add(p)

    rng = random.Random(seed)
    pt0 = {h: pe.rvec3(rng) for h in hubs}
    normal = {h: pe.rvec3(rng) for h in hubs}

    def plane_basis(h):
        n = normal[h]; basis=[]
        for e in ([F(1),F(0),F(0)],[F(0),F(1),F(0)],[F(0),F(0),F(1)]):
            proj = dot(e,n)/dot(n,n)
            d = [e[i]-proj*n[i] for i in range(3)]
            if any(di!=0 for di in d): basis.append(d)
            if len(basis)==2: break
        return basis

    def in_plane(h):
        bss = plane_basis(h); s=pe.rquat(rng); t=pe.rquat(rng)
        return [pt0[h][i]+s*bss[0][i]+t*bss[1][i] for i in range(3)]

    # meet line of b,c planes: base point p0 + t*dir
    n1,n2 = normal[b], normal[c]
    d = [n1[1]*n2[2]-n1[2]*n2[1], n1[2]*n2[0]-n1[0]*n2[2], n1[0]*n2[1]-n1[1]*n2[0]]
    c1=dot(n1,pt0[b]); c2=dot(n2,pt0[c])
    for fc in range(3):
        cols=[k for k in range(3) if k!=fc]
        A=[[n1[cols[0]],n1[cols[1]]],[n2[cols[0]],n2[cols[1]]]]
        det=A[0][0]*A[1][1]-A[0][1]*A[1][0]
        if det!=0:
            p0=[F(0)]*3
            inv=[[A[1][1]/det,-A[0][1]/det],[-A[1][0]/det,A[0][0]/det]]
            p0[cols[0]]=inv[0][0]*c1+inv[0][1]*c2
            p0[cols[1]]=inv[1][0]*c1+inv[1][1]*c2
            break

    # fix placement of every non-hub except a
    fixed = {}
    for s in Vp:
        if s in hubs: fixed[s]=pt0[s]; continue
        if s==a: continue
        hub_nbrs=[t for t in nb[s] if t in hubs]
        fixed[s]=in_plane(hub_nbrs[0])

    def cfg(t):
        pt = dict(fixed)
        pt[a] = [p0[i]+t*d[i] for i in range(3)]
        return {'edges':edges2,'V':Vp,'pt':pt,'nb':nb,'a':a,'b':b,'c':c,'v':v,'hubs':hubs}
    return cfg, a, b, c

def escape_value(data):
    rows, edge_rows, C, idx, n = build_rigidity(data)
    rk = rank(rows); tgt = 6*(n-1)
    ln = left_nullspace(rows)
    if rk!=tgt or len(ln)!=1:
        return None, rk, len(ln)
    lam = ln[0]
    a,b,c = data['a'],data['b'],data['c']; pt=data['pt']
    def find_edge(p,q):
        for e in edge_rows:
            if set(e)=={p,q}: return e
    e_ab=find_edge(a,b)
    base_a=6*idx[a]
    r=[F(0)]*6
    (uu,ww)=e_ab
    for ri in edge_rows[e_ab]:
        coef=lam[ri]
        for k in range(6):
            r[k]+=coef*rows[ri][base_a+k]
    Cbc=wedge2(hat(pt[b]),hat(pt[c]))
    return dot(r,Cbc), rk, 1

if __name__=='__main__':
    for seed in [1000, 2000, 3000]:
        cfg,a,b,c = build_config_parametric(seed)
        print(f"\n=== seed {seed}: sweep a along meet line, E(t)=r.(bhat^chat) ===")
        vals=[]
        for tnum in range(-8, 9):
            t = F(tnum)
            E, rk, nul = escape_value(cfg(t))
            tag = "" if E is None else ("ZERO!" if E==0 else ("+" if E>0 else "-"))
            vals.append((t,E,rk,nul,tag))
            print(f"  t={str(t):>4}  E={'None(rk%d,nul%d)'%(rk,nul) if E is None else str(E)[:40]:>42}  {tag}")
        signs = set(v[4] for v in vals if v[1] is not None and v[1]!=0)
        haszero = any(v[1]==0 for v in vals if v[1] is not None)
        print(f"  -> signs seen: {signs}  explicit-zero-at-integer: {haszero}  "
              f"crosses-zero(both signs): {signs=={'+','-'}}")
