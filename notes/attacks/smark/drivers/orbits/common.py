"""Exact rational linear algebra + the group G = K* x K* x GL2 acting on K^6.

Coordinates of x in K^6: index 0 = x_0, 1,2 = x_u, 3,4 = x_v, 5 = x_inf.
(a,b,C).x = (ab x_0 ; a C x_u ; b C x_v ; det(C) x_inf).
"""
from fractions import Fraction as F
import random

# ---------- exact linear algebra ----------
def rank(M):
    """Rank of a list-of-rows matrix over Q (exact)."""
    M = [list(row) for row in M]
    if not M:
        return 0
    nrows, ncols = len(M), len(M[0])
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [v / pv for v in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        r += 1
        if r == nrows:
            break
    return r

def rref(M):
    """Return (R, pivots) reduced row echelon form of M (list of rows)."""
    M = [list(row) for row in M]
    if not M:
        return M, []
    nrows, ncols = len(M), len(M[0])
    pivots = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [v / pv for v in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == nrows:
            break
    return M[:r], pivots

def nullspace(M, ncols=None):
    """Basis (list of vectors) of {v : M v = 0}."""
    if ncols is None:
        ncols = len(M[0])
    R, pivots = rref(M)
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fcol in free:
        v = [F(0)] * ncols
        v[fcol] = F(1)
        for i, pc in enumerate(pivots):
            v[pc] = -R[i][fcol]
        basis.append(v)
    return basis

def matvec(M, x):
    return [sum(M[i][j] * x[j] for j in range(len(x))) for i in range(len(M))]

def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)] for i in range(n)]

def transpose(M):
    return [list(col) for col in zip(*M)]

def zeros(n, m):
    return [[F(0)] * m for _ in range(n)]

def eye(n):
    M = zeros(n, n)
    for i in range(n):
        M[i][i] = F(1)
    return M

def det2(C):
    return C[0][0] * C[1][1] - C[0][1] * C[1][0]

# ---------- random small rationals ----------
def rand_rat(rng, nonzero=False, lo=-6, hi=6, dens=(1, 2, 3)):
    while True:
        v = F(rng.randint(lo, hi), rng.choice(dens))
        if not nonzero or v != 0:
            return v

def rand_vec(rng, n, nonzero=False):
    while True:
        v = [rand_rat(rng) for _ in range(n)]
        if not nonzero or any(c != 0 for c in v):
            return v

# ---------- the group and its Lie algebra ----------
def group_matrix(a, b, C):
    """6x6 matrix of (a,b,C) on K^6."""
    M = zeros(6, 6)
    M[0][0] = a * b
    for i in range(2):
        for j in range(2):
            M[1 + i][1 + j] = a * C[i][j]
            M[3 + i][3 + j] = b * C[i][j]
    M[5][5] = det2(C)
    return M

def rand_group_element(rng):
    a = rand_rat(rng, nonzero=True)
    b = rand_rat(rng, nonzero=True)
    while True:
        C = [[rand_rat(rng) for _ in range(2)] for _ in range(2)]
        if det2(C) != 0:
            break
    return a, b, C

def lie_generators():
    """The six Lie algebra generators as 6x6 matrices, with names and
    the value of d(chi) on each for chi(a,b,C) = a b det C."""
    gens = []
    Da = zeros(6, 6)
    for i in (0, 1, 2):
        Da[i][i] = F(1)
    gens.append(("da", Da, F(1)))
    Db = zeros(6, 6)
    for i in (0, 3, 4):
        Db[i][i] = F(1)
    gens.append(("db", Db, F(1)))
    for i in range(2):
        for j in range(2):
            X = zeros(6, 6)
            X[1 + i][1 + j] = F(1)   # E_ij on x_u
            X[3 + i][3 + j] = F(1)   # E_ij on x_v
            if i == j:
                X[5][5] = F(1)       # tr(E_ii) on x_inf
            gens.append((f"dC{i+1}{j+1}", X, F(1) if i == j else F(0)))
    return gens

# ---------- the quadratic forms ----------
def Q1(x):
    return x[0] * x[5]

def Q2(x):
    return x[1] * x[4] - x[2] * x[3]

def Q(x):
    return Q1(x) - Q2(x)

def rank_uv(x):
    return rank([[x[1], x[3]], [x[2], x[4]]])

# ---------- subspaces ----------
def subspace_dim(vectors):
    return rank(vectors) if vectors else 0

def intersection_dim(U, V):
    """dim(span U  cap  span V) for lists of vectors in the same K^n."""
    dU, dV = subspace_dim(U), subspace_dim(V)
    dSum = subspace_dim(list(U) + list(V))
    return dU + dV - dSum

def fmt(v):
    return "(" + ", ".join(str(c) for c in v) + ")"
