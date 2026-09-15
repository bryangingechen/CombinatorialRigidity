"""Tasks 4 and 5: Klein-form identification, star(p) ∩ g star(p'), the 16
coordinate-subspace defects, and star(p) ∩ g Λ²(π)."""
from fractions import Fraction as F
import random, itertools
from common import *

rng = random.Random(20260915)

# Λ²K⁴ -> K⁶: e12 -> x0, e13,e14 -> x_u, e23,e24 -> x_v, e34 -> x_inf
IDX = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def wedge(p, q):
    return [p[i] * q[j] - p[j] * q[i] for (i, j) in IDX]

def star(p):
    """basis (list of vectors, may be dependent) of {p ∧ y}."""
    vs = []
    for k in range(4):
        e = [F(0)] * 4; e[k] = F(1)
        vs.append(wedge(p, e))
    return vs

def lambda2(plane):
    """plane = list of 3 vectors spanning π ⊆ K⁴; Λ²(π) spanned by pairwise wedges."""
    return [wedge(plane[i], plane[j]) for i in range(3) for j in range(i + 1, 3)]

def apply(M, vs):
    return [matvec(M, v) for v in vs]

# --- Klein form check ---------------------------------------------------
klein_ok = True
for _ in range(50):
    p, q = rand_vec(rng, 4), rand_vec(rng, 4)
    if Q(wedge(p, q)) != 0:
        klein_ok = False
print("Q(p∧q) = 0 for 50 random p,q in K^4:", klein_ok)
# and non-decomposable check: a random x has Q(x) != 0 typically
x = rand_vec(rng, 6)
print("  (a random x in K^6 has Q(x) =", Q(x), ")")

# --- coordinate subspaces E (sums of the four summands) -------------------
BLOCKS = {"L": [0], "Pu": [1, 2], "Pv": [3, 4], "ell": [5]}
BLOCK_NAMES = ["L", "Pu", "Pv", "ell"]
def E_basis(subset):
    vs = []
    for bname in subset:
        for i in BLOCKS[bname]:
            e = [F(0)] * 6; e[i] = F(1)
            vs.append(e)
    return vs
SUBSETS = []
for r in range(5):
    for sub in itertools.combinations(BLOCK_NAMES, r):
        SUBSETS.append(sub)
assert len(SUBSETS) == 16

def defects(A, B):
    out = []
    for sub in SUBSETS:
        E = E_basis(sub)
        dE = len(E)
        cA = intersection_dim(A, E) if E else 0
        cB = intersection_dim(B, E) if E else 0
        out.append(cA + cB - dE)
    return out

# --- Task 4 --------------------------------------------------------------
print()
print("Task 4: A = star(p), B = star(p'), 20 pairs x 30 group elements")
print(f"{'pair':>4} {'min_g dim(A∩gB)':>16} {'max_g':>6}  {'p':<28} {'p_prime'}")
mins, maxdef = [], None
defect_vectors = []
for t in range(20):
    p = rand_vec(rng, 4, nonzero=True)
    pp = rand_vec(rng, 4, nonzero=True)
    A, B = star(p), star(pp)
    assert subspace_dim(A) == 3 and subspace_dim(B) == 3
    dims = []
    for _ in range(30):
        a, b, C = rand_group_element(rng)
        g = group_matrix(a, b, C)
        dims.append(intersection_dim(A, apply(g, B)))
    mins.append(min(dims))
    d = defects(A, B)
    defect_vectors.append(d)
    m = max(d)
    maxdef = m if maxdef is None else max(maxdef, m)
    print(f"{t:>4} {min(dims):>16} {max(dims):>6}  {fmt(p):<28} {fmt(pp)}")
print("min over all pairs of min_g dim(A∩gB):", min(mins), "; max over all pairs:", max(mins))
print()
print("16 subsets E (order):", ["+".join(s) if s else "0" for s in SUBSETS])
print("dim E             :", [len(E_basis(s)) for s in SUBSETS])
for t in range(3):
    print(f"defect vector pair {t}:", defect_vectors[t])
print("max over all 20 pairs and all 16 E of c_A(E)+c_B(E)-dim E:", maxdef)
# also report per-E max across the 20 pairs
perE = [max(dv[k] for dv in defect_vectors) for k in range(16)]
print("per-E max over the 20 pairs:", perE)

# --- Task 5 --------------------------------------------------------------
print()
print("Task 5: A = star(p), B = Λ²(π), 20 pairs x 30 group elements")
print(f"{'pair':>4} {'min_g dim(A∩gB)':>16} {'max_g':>6}")
mins5 = []
for t in range(20):
    p = rand_vec(rng, 4, nonzero=True)
    while True:
        plane = [rand_vec(rng, 4) for _ in range(3)]
        if rank(plane) == 3:
            break
    A, B = star(p), lambda2(plane)
    assert subspace_dim(A) == 3 and subspace_dim(B) == 3
    dims = []
    for _ in range(30):
        a, b, C = rand_group_element(rng)
        g = group_matrix(a, b, C)
        dims.append(intersection_dim(A, apply(g, B)))
    mins5.append(min(dims))
    print(f"{t:>4} {min(dims):>16} {max(dims):>6}")
print("min over all pairs of min_g dim(A∩gB):", min(mins5), "; max over all pairs:", max(mins5))
