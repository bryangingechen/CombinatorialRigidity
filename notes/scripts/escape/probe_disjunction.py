"""
Optimism guard.  M1 (r . Lambda^2Pihat(a) != 0) has a genuine in-stratum failure locus.
Two questions:
 (Q1) at an M1-failure config, do M2 (r not-perp pencil(b)) or M3 work?  I.e. is the
      RIGHT target the disjunction r not-in S^perp (at least one candidate)?
 (Q2) is r in S^perp (ALL THREE fail) ever achievable in-stratum?  If yes, Case III
      itself breaks on that locus; if never, Case III survives via the disjunction.
"""
from fractions import Fraction as F
import random, functools
print = functools.partial(print, flush=True)
from probe_zero import build_config_parametric
import pencil_escape as pe
from pencil_escape import (build_rigidity, rank, left_nullspace, wedge2, hat, dot,
                           span_L2, pencil_space)

def full_escape(data):
    rows, edge_rows, C, idx, n = build_rigidity(data)
    rk=rank(rows); tgt=6*(n-1); ln=left_nullspace(rows)
    if rk!=tgt or len(ln)!=1: return None
    lam=ln[0]; a,b,c=data['a'],data['b'],data['c']; pt=data['pt']
    def fe(p,q):
        for e in edge_rows:
            if set(e)=={p,q}: return e
    e_ab=fe(a,b); base_a=6*idx[a]; r=[F(0)]*6
    for ri in edge_rows[e_ab]:
        for k in range(6): r[k]+=lam[ri]*rows[ri][base_a+k]
    ah,bh,ch=hat(pt[a]),hat(pt[b]),hat(pt[c])
    Cbc=wedge2(bh,ch)
    L2a=span_L2(ah,bh,ch); penb=pencil_space(bh,data,b); penc=pencil_space(ch,data,c)
    S=L2a+penb+penc
    return {
      'M1': dot(r,Cbc)!=0,
      'M2': any(dot(r,w)!=0 for w in penb),
      'M3': any(dot(r,w)!=0 for w in penc),
      'r_in_Sperp': all(dot(r,w)==0 for w in S),
      'dimS': rank(S), 'r':r,
      'S':S,
    }

# (Q1) evaluate near the M1 zero t* ~ -2.5311710127 for seed 1000
print("=== (Q1) behaviour of M1/M2/M3 across the M1 zero (seed 1000) ===")
cfg,a,b,c = build_config_parametric(1000)
for t in [F(-26,10), F(-253,100), F(-2531171,1000000), F(-2532,1000), F(-254,100)]:
    res = full_escape(cfg(t))
    if res is None:
        print(f"  t={float(t):+.7f}: rank/nullity invalid"); continue
    print(f"  t={float(t):+.9f}: M1={res['M1']} M2={res['M2']} M3={res['M3']} "
          f"r_in_Sperp={res['r_in_Sperp']} dimS={res['dimS']}")

# (Q2) try hard to drive r into S^perp: 2-parameter scan (meet param t AND a hub-plane
# tilt) looking for ALL-THREE-FAIL, plus many random samples checking r_in_Sperp.
print("\n=== (Q2) is r in S^perp (all three fail) ever achievable? ===")
found=0; tested=0
for seed in range(4000, 4008):
    cfg,a,b,c=build_config_parametric(seed)
    for tnum in range(-3,4):
        res=full_escape(cfg(F(tnum)))
        if res is None: continue
        tested+=1
        if res['r_in_Sperp']:
            found+=1
            print(f"  seed{seed} t={tnum}: r_in_Sperp=TRUE  (all candidates fail!)")
        # also flag whenever NONE of M1,M2,M3 works
        if not (res['M1'] or res['M2'] or res['M3']):
            print(f"  seed{seed} t={tnum}: NO candidate works (M1,M2,M3 all False)")
print(f"  tested {tested} valid in-stratum configs; r_in_Sperp found: {found}")

# Also: does M1 alone ever fail while the disjunction holds? count M1 failures.
print("\n=== M1-failure frequency vs disjunction over a t-sweep (seed 3000) ===")
cfg,a,b,c=build_config_parametric(3000)
m1fail=0; disjfail=0; valid=0
for tn in range(-12,13):
    for d in (F(0), F(1,3)):
        res=full_escape(cfg(F(tn)+d))
        if res is None: continue
        valid+=1
        if not res['M1']: m1fail+=1
        if not (res['M1'] or res['M2'] or res['M3']): disjfail+=1
print(f"  valid={valid}  M1-fails={m1fail}  disjunction-fails(all three)={disjfail}")
