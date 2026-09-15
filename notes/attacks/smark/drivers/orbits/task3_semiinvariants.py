"""Task 3: semi-invariant quadratic forms on K^6 under G.

A quadratic form q(x) = x^T S x (S symmetric 6x6, 21 unknowns).
For a Lie algebra generator X (acting on vectors), (X.q)(x) = x^T (X^T S + S X) x.
Semi-invariance for chi: X^T S + S X = dchi(X) S for all six generators.
"""
from fractions import Fraction as F
from common import *

GENS = lie_generators()
PAIRS = [(i, j) for i in range(6) for j in range(i, 6)]   # 21 monomials x_i x_j
NAMES = ["x0", "xu1", "xu2", "xv1", "xv2", "xinf"]
assert len(PAIRS) == 21

def S_from_vec(s):
    S = zeros(6, 6)
    for k, (i, j) in enumerate(PAIRS):
        S[i][j] = s[k]
        S[j][i] = s[k]
    return S

def vec_from_S(S):
    return [S[i][j] for (i, j) in PAIRS]

def act(X, S):
    XT = transpose(X)
    A = matmul(XT, S)
    B = matmul(S, X)
    return [[A[i][j] + B[i][j] for j in range(6)] for i in range(6)]

def operator_matrix(X, lam):
    """21x21 matrix of s -> vec(X^T S + S X - lam S)."""
    cols = []
    for k in range(21):
        e = [F(0)] * 21
        e[k] = F(1)
        S = S_from_vec(e)
        out = act(X, S)
        out = [[out[i][j] - lam * S[i][j] for j in range(6)] for i in range(6)]
        cols.append(vec_from_S(out))
    return transpose(cols)   # rows = output coords, cols = input coords

def form_str(s):
    terms = []
    for k, (i, j) in enumerate(PAIRS):
        c = s[k] if i == j else 2 * s[k]     # x^T S x has coefficient 2 S_ij on x_i x_j, i<j
        if c != 0:
            terms.append(f"{c}*{NAMES[i]}*{NAMES[j]}")
    return " + ".join(terms) if terms else "0"

# ---- (a) chi = a b det C -----------------------------------------------
big = []
for name, X, dchi in GENS:
    big += operator_matrix(X, dchi)
ker = nullspace(big, 21)
print("chi = a*b*det(C): dim of semi-invariant quadratic forms =", len(ker))
for v in ker:
    print("   basis form:", form_str(v))
# Q1 = x0*xinf  -> S_05 = 1/2 ; Q2 = xu1*xv2 - xu2*xv1 -> S_14 = 1/2, S_23 = -1/2
sQ1 = [F(0)] * 21; sQ1[PAIRS.index((0, 5))] = F(1, 2)
sQ2 = [F(0)] * 21; sQ2[PAIRS.index((1, 4))] = F(1, 2); sQ2[PAIRS.index((2, 3))] = F(-1, 2)
print("   Q1 in kernel:", rank(ker + [sQ1]) == len(ker), " Q2 in kernel:", rank(ker + [sQ2]) == len(ker))
print("   rank(span{Q1,Q2}) =", rank([sQ1, sQ2]), " => kernel == span{Q1,Q2}:", len(ker) == 2 and rank(ker + [sQ1, sQ2]) == 2)

# ---- (b) all characters: torus weights first ----------------------------
# torus T = (a, b, diag(c3, c4)); weights of coordinates in the basis (da, db, dc3, dc4):
W = {0: (1, 1, 0, 0), 1: (1, 0, 1, 0), 2: (1, 0, 0, 1), 3: (0, 1, 1, 0), 4: (0, 1, 0, 1), 5: (0, 0, 1, 1)}
weight_spaces = {}
for k, (i, j) in enumerate(PAIRS):
    w = tuple(W[i][t] + W[j][t] for t in range(4))
    weight_spaces.setdefault(w, []).append(k)

# sanity: the four torus generators act diagonally with these weights
torus = {n: X for (n, X, _) in GENS if n in ("da", "db", "dC11", "dC22")}
for w, ks in weight_spaces.items():
    for k in ks:
        e = [F(0)] * 21; e[k] = F(1)
        S = S_from_vec(e)
        for t, gname in enumerate(("da", "db", "dC11", "dC22")):
            out = vec_from_S(act(torus[gname], S))
            assert out == [w[t] * c for c in e], (w, k, gname)
print()
print("torus weight spaces (weights in (da, db, dc3, dc4)) and the sl2-kernel in each:")
offdiag = [X for (n, X, _) in GENS if n in ("dC12", "dC21")]
found = []
for w in sorted(weight_spaces):
    ks = weight_spaces[w]
    # restrict the two off-diagonal operators to this weight space; want q with X.q = 0
    rows = []
    for X in offdiag:
        Mfull = operator_matrix(X, F(0))
        for r in range(21):
            rows.append([Mfull[r][k] for k in ks])
    kerw = nullspace(rows, len(ks))
    monos = [f"{NAMES[PAIRS[k][0]]}*{NAMES[PAIRS[k][1]]}" for k in ks]
    line = f"  weight {w}: span{{{', '.join(monos)}}} (dim {len(ks)}), sl2-kernel dim {len(kerw)}"
    if kerw:
        forms = []
        for v in kerw:
            full = [F(0)] * 21
            for idx, k in enumerate(ks):
                full[k] = v[idx]
            forms.append(form_str(full))
        line += "  <-- semi-invariant: " + " ; ".join(forms)
        m, n, k3, k4 = w
        chi = f"a^{m} b^{n} c3^{k3} c4^{k4}" + ("" if k3 == k4 else "  (NOT a character of G: c3,c4 exponents differ)")
        line += f"   character {chi}"
        found.append((w, forms))
    print(line)
print()
print("summary: characters admitting a nonzero semi-invariant quadratic form:")
for w, forms in found:
    m, n, k3, k4 = w
    print(f"  chi = a^{m} b^{n} det(C)^{k3}  (k3={k3}, k4={k4}):  {' ; '.join(forms)}")
