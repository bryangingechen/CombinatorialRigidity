#!/usr/bin/env python3
"""bkwit.py (§(K-main) Step MC10's second reading, 2026-09-25; ported from the reader's scratch): witness that (MC-27)'s literal bad set B_k(r) ("at EVERY placement") differs from
the set where (P_k) fails ("at the generic placement").  Orbit (iv), k = 2, r = 1: frame p_a = e0,
p_b = e3, pi_a = pi_b = pi = <e0, e1, e3>; rho = <l>, l = the line e1 e3 + e0... (a line in pi).
Generic 2-ear placements (x1, x2 in pi) have Lambda_2 = Lambda^2 pi, which contains l: (P_2) fails.
The valid placement x1 = e1, x2 = e0 + e1 (on the line p_a x1; all adjacent points distinct) has
lambda = 2 and l not in Lambda: so rho is NOT in the literal B_2(1).  Exact, deterministic, stdlib."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mc10indep import wedge, rank, dim_cap, e, vadd
pa, pb = e(0), e(3)
ell = [wedge(e(1), vadd(e(0), e(3)))]                    # a line of pi = <e0, e1, e3>
gen = [pa, vadd(e(0), e(1), e(1)), vadd(e(1), e(3), e(3), e(3)), pb]   # a generic-span placement
L = [wedge(gen[i], gen[i + 1]) for i in range(3)]
print('generic placement: lambda =', rank(L), ', dim(rho cap Lambda) =', dim_cap(ell, L), '(> 0: (P_2) fails)')
dege = [pa, e(1), vadd(e(0), e(1)), pb]                  # x2 on the line p_a x1
assert all(dege[i] != dege[i + 1] for i in range(3)) and rank([dege[1], dege[2]]) == 2
L2 = [wedge(dege[i], dege[i + 1]) for i in range(3)]
print('valid placement x2 on p_a x1: lambda =', rank(L2), ', dim(rho cap Lambda) =', dim_cap(ell, L2),
      '(= 0: so rho is not in the literal B_2(1))')
ok = rank(L) == 3 and dim_cap(ell, L) == 1 and rank(L2) == 2 and dim_cap(ell, L2) == 0
print('witness', 'CONFIRMED' if ok else 'FAILED')
sys.exit(0 if ok else 1)
