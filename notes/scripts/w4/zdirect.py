"""zdirect.py -- §(K-main) Step MC19 (Track E): direct certificates of the generic motive at A-prime graphs of the zstuck
shape (seed 1, --draws random graphs, |V| <= 13): one seeded hub-plane-chart draw per graph (up to 3),
all four conjuncts with explicit normals and rank mod 2^61-1 == 6(|V|-1) - def3.  A certificate per
graph (an exhibited nondegenerate attaining realization); a miss would be a lower bound only.
    PYTHONHASHSEED=0 python3 zdirect.py --draws 1500"""
import argparse, random
from zcore import F1, F2, zdraw, complete_normals, nondeg, rank_p, target, verts_of
from zsurvey import is_Aprime
from zstuck import build
from kbare_common import is_2ec
ap = argparse.ArgumentParser(); ap.add_argument('--draws', type=int, default=1500); a = ap.parse_args()
rng = random.Random(1)
n = ok = 0
for i in range(a.draws):
    E = build(rng, rng.randint(4, 7))
    if len(verts_of(E)) > 13 or not is_2ec(E) or not (F1(E) and F2(E)) or not is_Aprime(E):
        continue
    n += 1
    for d in range(3):
        r = zdraw(E, random.Random(f'20260924:zd:{i}:{d}'))
        nn, pt = r
        good, _ = nondeg(E, complete_normals(E, nn, pt), pt)
        if good and rank_p(E, pt) == target(E):
            ok += 1
            break
print(f'zstuck-shaped A-prime graphs (seed 1, {a.draws} draws, |V| <= 13, with repeats): {n}; '
      f'nondegenerate attaining draw exhibited at {ok}')
