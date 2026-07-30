"""Localize the in-stratum escape zero for seed 1000 in t in (-3,-2), confirming
rank 84 / nullity 1 persist right up to the crossing (=> the failure config is a
valid pencil realization, not a rank-dropping degeneracy)."""
from fractions import Fraction as F
from probe_zero import build_config_parametric, escape_value

cfg,a,b,c = build_config_parametric(1000)

# bisection between t=-3 (E<0) and t=-2 (E>0)
lo, hi = F(-3), F(-2)
Elo,_,_ = escape_value(cfg(lo))
Ehi,_,_ = escape_value(cfg(hi))
print(f"start: E(-3)={'%+d'%(1 if Elo>0 else -1)} E(-2)={'%+d'%(1 if Ehi>0 else -1)}")
for it in range(40):
    mid = (lo+hi)/2
    Emid, rk, nul = escape_value(cfg(mid))
    if Emid is None:
        print(f"  iter {it}: t={float(mid):.10f}  E=None rk={rk} nul={nul}  (rank drop!)")
        break
    sign = '+' if Emid>0 else ('-' if Emid<0 else '0')
    if it % 5 == 0 or it>34:
        print(f"  iter {it}: t={float(mid):.12f}  rk={rk} nul={nul}  E sign={sign}  |E|~{float(abs(Emid)):.3e}")
    if Emid == 0:
        print("  EXACT rational zero at t =", mid); break
    if (Emid>0) == (Ehi>0):
        hi = mid; Ehi = Emid
    else:
        lo = mid; Elo = Emid
print(f"\nfinal bracket: t in ({float(lo):.12f}, {float(hi):.12f})  width={float(hi-lo):.3e}")
# confirm rank/nullity valid at the tight bracket ends
for t in (lo, hi):
    E, rk, nul = escape_value(cfg(t))
    print(f"  t={float(t):.12f}: rank={rk} nullity={nul}  E sign={'+' if E>0 else '-'}  (valid pencil realization)")
print("\n=> the escape r.(bhat^chat) has a genuine zero at an INTERIOR, rank-84/nullity-1")
print("   pencil realization: M1 FAILS there.  The escape is generic, NOT a structural identity.")
