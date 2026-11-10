"""PENCIL-SCENES worked examples: the lifting space L(q) and the rank of configurations.

Stdlib-only and exact (fractions.Fraction), like the natural/ flatness drivers. Two modes, each
printing the figures that notes/PencilScenes.md section 4 quotes:

  theta   the theta graph with paths of lengths 2, 2, 3 (hubs a, b; a-1-b, a-2-b, a-3-4-b) at a
          fixed asymmetric picture: def_2, def_3, def_4; dim L(q); the ranks of the plane framework
          P_q (d = 2), of the flat, an affine and the fold configuration (d = 3) and of the fold in
          dimension 4; the face planes of the fold, the bar condition of their gradients on every
          edge and across the crease between the faces of the non-adjacent hubs a and b; the
          motions of the bar framework (G, q) against the scenes modulo constants.
  cycle7  the 7-cycle at a seeded random picture with seeded random heights: def_2, def_3, def_4;
          dim L(q); flat and one-height ranks at d = 3; flat, one-height and two-height ranks at
          d = 4.

The rank of a configuration with points b_v in K^{d+1} is that of the body-hinge framework whose
hinge at an edge uv is the join b_u v b_v in the exterior square (dimension D = C(d+1, 2)). By
lem:pencil-d-rank-collineation's proof this is the rank of the panel-hinge framework with normals
b_v, since the two hinges differ by one fixed linear isomorphism of the screw space.

Invocation (from the repository root):
  python3 notes/scripts/scenes/example.py theta
  python3 notes/scripts/scenes/example.py cycle7
"""
from fractions import Fraction as F
from itertools import combinations
import random
import sys


def rref_nullspace(rows, ncols):
    """A basis of the right nullspace of the matrix with the given rows."""
    M = [list(r) for r in rows]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    basis = []
    for fc in (c for c in range(ncols) if c not in piv):
        v = [F(0)] * ncols
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis


def rank(rows, ncols):
    return ncols - len(rref_nullspace(rows, ncols))


def closed_nbhd(E, v):
    return [v] + [b if a == v else a for (a, b) in E if v in (a, b)]


def admissible(V, E, q):
    """Adjacent picture points distinct, and no closed neighbourhood on one line."""
    if any(q[u] == q[v] for u, v in E):
        return False
    for v in V:
        pts = [[F(q[w][0]), F(q[w][1]), F(1)] for w in closed_nbhd(E, v)]
        if rank(pts, 3) < 3:
            return False
    return True


def lifting_space(V, E, q):
    """A basis of L(q): unknowns are the heights z_v and an affine function (a, b, c) per body."""
    assert admissible(V, E, q), "picture not admissible"
    n = len(V)
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for v in V:
        for w in closed_nbhd(E, v):
            r = [F(0)] * (4 * n)
            r[idx[w]] = F(1)
            b = n + 3 * idx[v]
            r[b], r[b + 1], r[b + 2] = -F(q[w][0]), -F(q[w][1]), F(-1)
            rows.append(r)
    full = rref_nullspace(rows, 4 * n)
    heights = [vec[:n] for vec in full]
    # guard: at an admissible picture the heights fix the affine functions, so projecting is injective
    assert rank(heights, n) == len(full), "projection to the heights is not injective"
    return heights


def wedge2(p, s):
    return [p[i] * s[j] - p[j] * s[i] for i, j in combinations(range(len(p)), 2)]


def hinge_rank(V, E, pts):
    """(rank, motions) of the body-hinge framework with hinge pts[u] v pts[v] at each edge."""
    idx = {v: i for i, v in enumerate(V)}
    k = len(pts[V[0]])
    D = k * (k - 1) // 2
    n, m = len(V), len(E)
    rows = []
    for ei, (u, v) in enumerate(E):
        L = wedge2(pts[u], pts[v])
        assert any(L), f"zero hinge at {u}{v}"
        for c in range(D):
            r = [F(0)] * (D * n + m)
            r[D * idx[u] + c], r[D * idx[v] + c], r[D * n + ei] = F(1), F(-1), -L[c]
            rows.append(r)
    motions = len(rref_nullspace(rows, D * n + m))  # hinges nonzero, so the multipliers are fixed
    return D * n - motions, motions


def deficiency(V, E, D):
    """max over partitions P of V of D(|P| - 1) - (D - 1) d(P), by brute force."""
    def partitions(s):
        if not s:
            yield []
            return
        for p in partitions(s[1:]):
            for i in range(len(p)):
                yield p[:i] + [[s[0]] + p[i]] + p[i + 1:]
            yield [[s[0]]] + p
    best = 0
    for P in partitions(list(V)):
        part = {v: i for i, B in enumerate(P) for v in B}
        d = sum(1 for a, b in E if part[a] != part[b])
        best = max(best, D * (len(P) - 1) - (D - 1) * d)
    return best


def points(V, q, heights):
    return {v: [F(q[v][0]), F(q[v][1])] + [F(z[v]) for z in heights] + [F(1)] for v in V}


def theta():
    V = ['a', 'b', '1', '2', '3', '4']
    E = [('a', '1'), ('1', 'b'), ('a', '2'), ('2', 'b'), ('a', '3'), ('3', '4'), ('4', 'b')]
    q = {'a': (-2, 0), 'b': (2, 1), '1': (0, 1), '2': (0, -1), '3': (-1, 2), '4': (1, 3)}
    # adversarial witness for the admissibility guard: N[a] = {a, 1, 2, 3} on the line x = 0
    bad = dict(q, a=(0, 3), **{'3': (0, 2)})
    assert not admissible(V, E, bad) and admissible(V, E, q)
    n = len(V)
    print("theta(2,2,3): def_2, def_3, def_4 =",
          deficiency(V, E, 3), deficiency(V, E, 6), deficiency(V, E, 10))
    L = lifting_space(V, E, q)
    print("dim L(q) =", len(L))
    flat = {v: 0 for v in V}
    aff = {v: 3 * q[v][0] - q[v][1] + 5 for v in V}
    # the fold: face of a is z = 0, face of b is z = x, creased along x = 0 through q_1 and q_2
    fold = {v: (q[v][0] if v in ('b', '4') else 0) for v in V}
    for z in (aff, fold):  # both lie in L(q)
        assert rank(L + [[F(z[v]) for v in V]], n) == len(L), "height not in L(q)"
    print("d = 2, P_q:              rank, motions =", hinge_rank(V, E, points(V, q, [])),
          " target", 3 * (n - 1) - deficiency(V, E, 3))
    for name, zs in (("flat", [flat]), ("affine", [aff]), ("fold", [fold])):
        print(f"d = 3, {name:6s}:          rank, motions =", hinge_rank(V, E, points(V, q, zs)),
              " target", 6 * (n - 1) - deficiency(V, E, 6))
    print("d = 4, heights (fold, 0): rank, motions =",
          hinge_rank(V, E, points(V, q, [fold, flat])), " target", 10 * (n - 1) - deficiency(V, E, 10))
    # face planes of the fold: the affine function through the lifted closed neighbourhood
    h = {}
    for v in V:
        rows = [[F(q[w][0]), F(q[w][1]), F(1), -F(fold[w])] for w in closed_nbhd(E, v)]
        ns = rref_nullspace(rows, 4)
        assert len(ns) == 1 and ns[0][3] != 0, f"face of {v} not a unique non-vertical plane"
        h[v] = tuple(x / ns[0][3] for x in ns[0][:3])
        print(f"  face of {v}: z = {h[v][0]} x + {h[v][1]} y + {h[v][2]}")

    def jump(u, v, s, t):  # (g_u - g_v) . (q_s - q_t)
        return ((h[u][0] - h[v][0]) * (q[s][0] - q[t][0]) + (h[u][1] - h[v][1]) * (q[s][1] - q[t][1]))
    print("gradient jumps across edges, (g_u - g_v).(q_u - q_v):", [str(jump(u, v, u, v)) for u, v in E])
    print("across the crease of a and b (not adjacent), (g_a - g_b).(q_1 - q_2):", jump('a', 'b', '1', '2'))
    idx = {v: i for i, v in enumerate(V)}
    bars = []
    for u, v in E:
        r = [F(0)] * (2 * n)
        dx, dy = F(q[u][0] - q[v][0]), F(q[u][1] - q[v][1])
        r[2 * idx[u]], r[2 * idx[u] + 1], r[2 * idx[v]], r[2 * idx[v] + 1] = dx, dy, -dx, -dy
        bars.append(r)
    print("motions of the bar framework (G, q):", len(rref_nullspace(bars, 2 * n)),
          "  scenes modulo constants, dim L(q) - 1:", len(L) - 1,
          "  cycle rank of G:", len(E) - n + 1)


def cycle7():
    seed = 2
    rng = random.Random(seed)
    n = 7
    V = [str(i) for i in range(n)]
    E = [(str(i), str((i + 1) % n)) for i in range(n)]
    print("C_7, seed", seed, ": def_2, def_3, def_4 =",
          deficiency(V, E, 3), deficiency(V, E, 6), deficiency(V, E, 10))
    q = {v: (rng.randint(-20, 20), rng.randint(-20, 20)) for v in V}
    print("picture:", q)
    L = lifting_space(V, E, q)
    print("dim L(q) =", len(L))
    zero = {v: 0 for v in V}
    z1 = {v: rng.randint(-20, 20) for v in V}
    z2 = {v: rng.randint(-20, 20) for v in V}
    # guard: z1, z2 independent modulo the affine heights, so W has dimension 2
    aff = [[F(q[v][0]) for v in V], [F(q[v][1]) for v in V], [F(1)] * n]
    assert rank(aff + [[F(z1[v]) for v in V], [F(z2[v]) for v in V]], n) == 5, "W not 2-dimensional"
    print("d = 3: flat", hinge_rank(V, E, points(V, q, [zero]))[0],
          " one height", hinge_rank(V, E, points(V, q, [z1]))[0],
          " target", 6 * (n - 1) - deficiency(V, E, 6))
    print("d = 4: flat", hinge_rank(V, E, points(V, q, [zero, zero]))[0],
          " W of dim 1", hinge_rank(V, E, points(V, q, [z1, zero]))[0],
          " W of dim 2", hinge_rank(V, E, points(V, q, [z1, z2]))[0],
          " target", 10 * (n - 1) - deficiency(V, E, 10))


if __name__ == "__main__":
    {"theta": theta, "cycle7": cycle7}[sys.argv[1]]()
