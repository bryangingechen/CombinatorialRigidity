from fractions import Fraction as F
import random, itertools
from common import *
rng = random.Random(20260915)
IDX = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def wedge(p, q): return [p[i] * q[j] - p[j] * q[i] for (i, j) in IDX]
def star(p):
    vs = []
    for k in range(4):
        e = [F(0)] * 4; e[k] = F(1); vs.append(wedge(p, e))
    return vs
BLOCKS = {"L": [0], "Pu": [1, 2], "Pv": [3, 4], "ell": [5]}
BN = ["L", "Pu", "Pv", "ell"]
SUBSETS = [s for r in range(5) for s in itertools.combinations(BN, r)]
def E_basis(sub):
    vs = []
    for b in sub:
        for i in BLOCKS[b]:
            e = [F(0)] * 6; e[i] = F(1); vs.append(e)
    return vs
def defects(A, B):
    out = []
    for sub in SUBSETS:
        E = E_basis(sub)
        cA = intersection_dim(A, E) if E else 0
        cB = intersection_dim(B, E) if E else 0
        out.append(cA + cB - len(E))
    return out
# replay the same draws as task45_parity.py: 50 Klein pairs, one x in K^6, then the 20 pairs
for _ in range(50):
    rand_vec(rng, 4); rand_vec(rng, 4)
rand_vec(rng, 6)
generic = [0, -1, -2, -2, -1, -1, -1, -2, -2, -3, -3, -1, -2, -2, -1, 0]
labels = ["+".join(s) if s else "0" for s in SUBSETS]
print("generic vector (pair 0):", generic)
for t in range(20):
    p = rand_vec(rng, 4, nonzero=True); pp = rand_vec(rng, 4, nonzero=True)
    for _ in range(30):
        rand_group_element(rng)
    d = defects(star(p), star(pp))
    zp = [i + 1 for i, c in enumerate(p) if c == 0]
    zpp = [i + 1 for i, c in enumerate(pp) if c == 0]
    diff = [labels[k] for k in range(16) if d[k] != generic[k]]
    print(f"pair {t:>2}: zero coords p={zp} p'={zpp}  differs at E in {diff}  vector={d}")
