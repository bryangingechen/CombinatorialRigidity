"""Canonical exact-ℚ primitives for the Phase-39 PENCIL numerics harness.

The base layer.  Everything here is a **pure, deterministic, rng-free**
primitive that was previously reimplemented independently in
`escape/pencil_escape.py` and `kbare/kbare_common.py` (and, for `cross3`,
in three places).  The two model layers now import from here instead, so a
defect in one of these has one home and moves every figure that depends on
it — the failure mode the `plane_basis` degeneracy exhibited (a defect in
one copy left the other copies' figures untouched, so nothing flagged it;
see `notes/scripts/README.md` *Divergences*).

Only semantically identical reimplementations were merged here.  Same-named
functions that genuinely differ — `plane_basis`, `rvec3`/`rquat`/`rint`,
`build_rigidity`, `theta_edges`, `neighbors` (2-arg), `validate`, and the
`no_good_search`/`nogood_subdiv` predicate pair — are deliberately left
where they are and catalogued in `README.md` *Divergences*; merging any of
them would move recorded figures.

Exact ℚ throughout (`fractions.Fraction`); no floating point anywhere in the
harness.  The one enlargement is `Gauss`, exact ℚ(i), moved down here from
`w4/closure.py` on 2026-08-20 (which re-exports it) once a second arc needed
isotropic vectors.
"""
import scriptpath  # noqa: F401  -- present so this module is import-order-safe
from fractions import Fraction as F

# ---------------- exact-ℚ linear algebra ----------------


def rref(M):
    """Reduced row echelon form (list of list of Fraction). Returns (R, pivots)."""
    M = [row[:] for row in M]
    if not M:
        return M, []
    rows = len(M)
    cols = len(M[0])
    pivots = []
    r = 0
    for c in range(cols):
        # find pivot in column c at or below row r
        piv = None
        for i in range(r, rows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = F(1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    return M, pivots


def rank(M):
    """Exact rational rank.  (`kbare_common` exposes this as `rank_exact`.)"""
    if not M:
        return 0
    _, p = rref(M)
    return len(p)


def nullspace(M):
    """Basis of {x : M x = 0} (right null space), as list of column-vectors."""
    if not M:
        return []
    cols = len(M[0])
    R, piv = rref(M)
    pivset = set(piv)
    free = [c for c in range(cols) if c not in pivset]
    basis = []
    for fcol in free:
        vec = [F(0)] * cols
        vec[fcol] = F(1)
        for ri, pc in enumerate(piv):
            vec[pc] = -R[ri][fcol]
        basis.append(vec)
    return basis


def left_nullspace(M):
    """Basis of {y : y^T M = 0} = nullspace of M^T."""
    if not M:
        return []
    rows = len(M)
    cols = len(M[0])
    MT = [[M[i][j] for i in range(rows)] for j in range(cols)]
    return nullspace(MT)


def dot(u, v):
    """Coordinate (Euclidean) pairing.  On ℝ⁶ this is NOT the Klein form —
    for that use `pitch.klein` (= dot with `repin.hodge_star`)."""
    return sum((a * b for a, b in zip(u, v)), F(0))


def cross3(u, v):
    """Cross product on ℚ³.  (`repin` exposes this as `cross`.)"""
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0]]


# ---------------- exact ℚ(i) ----------------
#
# `Gauss` moved down here from `closure.py:79` on 2026-08-20 (the harness
# move-down round, slice 2).  `closure` was deliberately the only driver whose
# scalars are not ℚ and kept this class private, on the recorded ground that
# "nothing else needs isotropic vectors"; §(K-out)'s residual route
# (`rank(Q|_D) = 3` via ⋆-eigen splitting) now does, which is the condition
# that reasoning made the move conditional on, and the user adjudicated the
# move down (2026-08-19, `notes/scripts/README.md` *Harness debt*).  `closure`
# re-exports it, so every recorded figure of `closure` and `grid` is unchanged.
# It is the ONE non-ℚ scalar type in the base layer: nothing here returns a
# `Gauss` unless it was handed one.

class Gauss:
    """Exact Gaussian rationals ℚ(i).  Coerces int / Fraction on every op."""
    __slots__ = ('re', 'im')

    def __init__(self, re=0, im=0):
        self.re = F(re)
        self.im = F(im)

    @staticmethod
    def _c(z):
        return z if isinstance(z, Gauss) else Gauss(z, 0)

    def __add__(self, o):
        o = Gauss._c(o)
        return Gauss(self.re + o.re, self.im + o.im)
    __radd__ = __add__

    def __neg__(self):
        return Gauss(-self.re, -self.im)

    def __sub__(self, o):
        return self + (-Gauss._c(o))

    def __rsub__(self, o):
        return Gauss._c(o) + (-self)

    def __mul__(self, o):
        o = Gauss._c(o)
        return Gauss(self.re * o.re - self.im * o.im,
                     self.re * o.im + self.im * o.re)
    __rmul__ = __mul__

    def _inv(self):
        n = self.re * self.re + self.im * self.im
        assert n != 0, "division by zero in ℚ(i)"
        return Gauss(self.re / n, -self.im / n)

    def __truediv__(self, o):
        return self * Gauss._c(o)._inv()

    def __rtruediv__(self, o):
        return Gauss._c(o) * self._inv()

    def __eq__(self, o):
        if not isinstance(o, (int, F, Gauss)):
            return NotImplemented
        o = Gauss._c(o)
        return self.re == o.re and self.im == o.im

    def __ne__(self, o):
        r = self.__eq__(o)
        return r if r is NotImplemented else (not r)

    def __bool__(self):
        return self.re != 0 or self.im != 0

    def __hash__(self):
        return hash((self.re, self.im))

    def __repr__(self):
        if self.im == 0:
            return str(self.re)
        if self.re == 0:
            return f"{self.im}i"
        return f"({self.re}{'+' if self.im > 0 else '-'}{abs(self.im)}i)"


# ---------------- Plücker / exterior ----------------

# index order for Lambda^2 of R^4 (basis e0,e1,e2,e3):
PL = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def wedge2(P, Q):
    """P,Q in Q^4 -> P^Q in R^6 (Plucker coords, order PL)."""
    return [P[i] * Q[j] - P[j] * Q[i] for (i, j) in PL]


def hat(c):
    """homogenize a Q^3 point -> Q^4 as (x,y,z,1)."""
    return [c[0], c[1], c[2], F(1)]


def perp_basis(v):
    """basis of {w in R^6 : w . v = 0} (5-dim if v != 0)."""
    return nullspace([v])  # 1 x 6 matrix


# ---------------- graph adjacency ----------------


def neighbors(edges):
    """Adjacency map, keyed only by the vertices the edge list touches.

    NOT the same function as `pencil_escape.neighbors_seeded(edges, allverts)`,
    which pre-seeds a key for every vertex of an explicit list (so isolated
    vertices survive as empty sets).  See README *Divergences*.
    """
    nb = {}
    for u, w in edges:
        nb.setdefault(u, set()).add(w)
        nb.setdefault(w, set()).add(u)
    return nb
