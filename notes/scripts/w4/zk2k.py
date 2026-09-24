"""zk2k.py -- §(K-main) Step MC19 (Track E): exhibited certificates for (MC-128)(a) at small k (the proof is general):
K_{2,k}, k = 3..10, one seeded hub-plane-chart draw each: all four conjuncts with explicit normals,
and rank mod 2^61-1 equal to 6(|V|-1) - def3 (a certificate).  PYTHONHASHSEED=0 python3 zk2k.py"""
import random
from zcore import zdraw, complete_normals, nondeg, rank_p, target, F1, F2
out = []
for k in range(3, 11):
    E = [(('a',), ('x', i)) for i in range(k)] + [(('b',), ('x', i)) for i in range(k)]
    assert F1(E) and F2(E)
    rng = random.Random(f'20260924:K2{k}')
    n, pt = zdraw(E, rng)
    ok, why = nondeg(E, complete_normals(E, n, pt), pt)
    rk, t = rank_p(E, pt), target(E)
    assert ok and rk == t, (k, ok, why, rk, t)
    out.append(f'K2,{k}: {rk}/{t}')
print('; '.join(out), '-- all nondegenerate and attaining')
