#!/usr/bin/env python3
"""strata.py -- body-hinge rank on realization strata, P^3 and P^4 (2026-10-29).

The evidence behind `notes/Strata.md`.  For each graph G of a fixed
population and each stratum X of hinge configurations, it takes the exact
rank of the body-hinge rigidity matrix at a seeded rational point of X and
compares it with a count.  The rank at one point is a LOWER bound for the
generic rank on X (rank is lower semicontinuous).  Every count printed here
is an UPPER bound, proved in the note, so a match certifies that the generic
rank on X equals the count, on that graph.

Modes (run from the repo root; each prints its seed):

  python3 notes/scripts/strata/strata.py --linear [--seed N]
      The linear rungs: every hinge independently in one linear section of
      the Klein quadric whose lines span a D'-dimensional subspace L.  Cell:
      rank at a point / 6(n-1) - def_D'(G) [rank at a random vector of L per
      hinge, the per-edge linear envelope].
  python3 notes/scripts/strata/strata.py --mixed [--seed N]
      Blocks of edges confined to different sections, the other edges
      generic: rank at a point [rank at the per-edge linear envelope].
  python3 notes/scripts/strata/strata.py --perbody [--seed N]
      The per-body strata: molecular (hinge p_u v p_v), panel (hinge
      Pi_u ^ Pi_v; parallel edges share it), pencil (lifted from a planar
      picture through a random height in the lifting space L(q)) and the
      flat pencil configuration (height 0).  Counts def_6, and def_3 for the
      flat configuration.
  python3 notes/scripts/strata/strata.py --examples [--seed N]
      The note's two C6 sentences: (a) the stratum "all hinges through one
      point, the point free" spans all of (Lambda^2 Q^4)^E yet has rank 27 at
      every draw; (b) three hinges meeting a fixed line: rank 30; all six:
      rank 29.  Asserted.
  python3 notes/scripts/strata/strata.py --selftest [--seed N]
      Every degeneracy guard rejects a constructed witness and passes its
      negative control; def_D by subset DP agrees with brute-force partitions
      and, at D = 6, with `kbare_common.exact_deficiency`; the motion identity
      rank R = 6(n-1) - |E| + rank{g_e (x) C_e} holds at sampled strata.

Added in the second session (2026-10-29; the five modes above unchanged,
their output byte-identical):

  python3 notes/scripts/strata/strata.py --complexes [--seed N]
      Per-body special complexes (hinge uv meets lines ell_u and ell_v) and
      per-body linear complexes (hinge uv in complexes w_u and w_v) in P^3:
      rank at a point / 6(n-1)-def_6 [rank at the per-edge envelope
      {w_u, w_v}^perp | at |E| <= 9 the min-max min_F |E-F| + dim sum_F
      g_e (x) L_e by brute force over F].
  python3 notes/scripts/strata/strata.py --residual4 [--seed N]
      The P^4 flat base of the note's Result 9: hinge planes inside one
      hyperplane, the one at uv through points p_u, p_v.  Rank in P^4 /
      10(n-1)-def_4, and the D = 4 residual / 4(n-1)-def_4.
  python3 notes/scripts/strata/strata.py --d4 [--seed N]
      The six P^4 per-body flag strata on `GRAPHS4` (the samplers' docstrings
      give each one's model and its polar-dual form).  Asserted: generic and
      panel at 10(n-1)-def_10 (Tay-Whiteley; Katoh-Tanigawa, d >= 2), and
      three flat sub-cases at the counts of the theorems they reduce to
      (pencil0, line-o: def_6, the P^3 molecular theorem; l+h0: def_3, the
      planar theorem).  Reported, not asserted: point, pencil, line-x,
      line+hyp, each against the upper bound 10(n-1)-def_10.  Ranks by the
      motion identity at D = 10, cross-checked against `rig_rank_dot`.
  python3 notes/scripts/strata/strata.py --lifting [--seed N]
      Lifting-space dimensions at a seeded picture on `GRAPHS4`: planar
      (dim L(q) - 3 = def_3 asserted at simple graphs) and in K^3 (dim L(q)
      - 4 against def_4, reported); then the cubic diamond rings at
      n = 12, 16, 20, past the DP cap, where a rank of 10(n-1) certifies.

Added in the third session (2026-10-29; the nine modes above unchanged, their
output byte-identical):

  python3 notes/scripts/strata/strata.py --pd [--seed N]
      The pencil of P^d at d = 2..6, D = C(d+1,2), dual form: a planar picture
      q plus d-2 heights in L(q), hinge the line b_u b_v.  On the simple
      graphs of `GRAPHS4`: rank at a point / D(n-1) - def_D, asserted at
      d = 2, 3 (Katoh-Tanigawa at d = 2; Phase 40), reported at d >= 4.  Also
      asserted: dim L(q) = 3 + def_3; def at C(l,2), l = 3 + def_3, equals
      def_inf (def at n + 2, where only tree quotients count) on all 38
      graphs; the points span min(d+1, dim L(q)) dimensions; def_D = def_inf
      in the stable range d >= dim L(q) - 1.  Then `PD_PAST_CAP` (theta
      graphs, subdivisions, diamond rings; n <= 25) at d = 4..6 against
      D(n-1), where a match certifies.

Added in Phase 42a (2026-10-29; the ten modes above unchanged, their output
byte-identical; `notes/Phase42-design.md` sections 2.4-2.5):

  python3 notes/scripts/strata/strata.py --content [--seed N]
      T1 on `GRAPHS4` at d = 4, 5, 6: the flat configuration (every height
      0) against D(n-1) + 3 - dim L(q), asserted at every graph; R1's base
      (the last height 0, the P^(d-1) pencil in a hyperplane) against
      D(n-1) - def_(D_(d-1)), asserted at d = 4, reported at d = 5, 6.  T2
      at d = 3..6: closed m-gons of affine points, 3 <= m <= D, with joins
      independent over every field (Smith invariant factors all 1), and the
      long ear's D-gon `cert_top` with three consecutive points at height
      zero, asserted; seed-independent.  Then the content-range graphs
      (theta(2,2,k), theta(2,2,2,k), D's witness, diamond rings at m = 6, 7)
      at d = 4, 5, 6: rank at a point / D(n-1) - def_D under the DP cap,
      reported, and against D(n-1) past it, where a match certifies.

Added for Phase 42a's T4 (2026-10-29; the eleven modes above unchanged, their
output byte-identical; `notes/Phase42-design.md` sections 2.3-2.4):

  python3 notes/scripts/strata/strata.py --oneear [--seed N]
      T4's first half, ONE-EAR.  Theta graphs with a one-body ear a - x - b
      (`one_ear_graphs`: the ends share one, two or no neighbours in
      V1 = V - x) at d = 4, 5: a pencil configuration of G restricted to V1,
      the incidence locus the d = 3 step needs G1 = G - x to attain on, and
      G1's own configuration at the same picture, each against G1's target
      (reported); with dim(Pi_a cap Pi_b), the d = 3 step's two hypotheses,
      and at two shared neighbours the premises of a forced motion of G1
      on the locus (asserted).

Added for Phase 42a's T3 (2026-10-29; the twelve modes above unchanged, their
output byte-identical; `notes/Phase42-design.md` sections 2.3-2.4):

  python3 notes/scripts/strata/strata.py --short [--seed N]
      T3, SHORT.  An open ear a - x_1 - ... - x_k - b on V1 with
      3 <= k <= D-2 and def_D(G[V1]) > def_D(G), and G'' = G with x_2
      suppressed (sec:main-component-short).  The d = 3 step's two stages at
      d = 3, 4, 5: base data from a configuration of G'', a general ear
      datum y, W = rho + span(the ear joins of G''); then x_2 put back at a
      general affine point.  Only the danger cells: def_D(G'') = def_D(G)
      (so (*) needs one dimension more than W) and 2d-1 <= dim W <= D-1 (so
      W can contain both stars and still not be Lambda^2); off them the
      d-general insertion lemma settles the step.  Reported at d = 4, 5:
      whether W contains star(y_1), star(y_3), both (X3 fails), the images
      of rho, of the far joins and of W modulo the two stars, the step's (*)
      and (*) at a general ear datum of G; asserted at d = 3, where the
      chapter proves them, and everywhere: the ear rank formula, every
      deficiency by a partition matched by a generic-hinge rank.

Added for Phase 42a's T4, second half (2026-10-29; the thirteen modes above
unchanged, their output byte-identical; `notes/Phase42-design.md` sections
2.3-2.4):

  python3 notes/scripts/strata/strata.py --orbit [--seed N]
      The orbit ears, ONE-EAR (sec:main-component-orbit): an open ear with
      k = 1, 2 interior bodies at non-adjacent ends where def_D(G[V1]) >
      def_D(G), so row 12 does not cover the step, at d = 3..6 on the
      content range; --short's families, the cells from a box search seeded
      by (family, d, k) alone.  k = 1: G[V1] on the incidence locus and the
      step's (*).  k = 2: the d = 3 route, G_1 (x_2 suppressed) on the
      locus, W = rho + its two joins, then x_2 put back at a general point
      of the end planes A, B, against the ceiling dim(rho + Lambda^2(A+B));
      and (*) at G's own configuration.  The d = 3 steps' merged hypothesis
      is certified per cell.  Asserted: the ear rank formula, every
      deficiency certified, the merged hypothesis putting each end off the
      other's plane, and at d = 3 lem:pencil-insertion-two.

Added for Phase 42a's T5 (2026-10-29; the fourteen modes above unchanged,
their output byte-identical; `notes/Phase42-design.md` sections 2.3-2.4):

  python3 notes/scripts/strata/strata.py --coverage [--seed N]
      T5, the coverage.  The case analysis of sec:main-component-coverage
      read at D = C(d+1, 2), d = 3..6, on subdivisions of small cores
      (`COV_CORES`, paths of 1..COV_LMAX edges), sparse and in the content
      range: which rows of def:pencil-x0-reduces apply at D, and the
      obligation each row's P^d step carries (`cov_tag`: GEN, SHORT-CORE,
      ONE-EAR).  Exact combinatorics only (`core_def`, checked against the
      3^n DP under the cap), so seed-independent.  Asserted: the coverage at
      D at every graph (Theorem S read at D), the chain facts its proof uses,
      and at D >= 10 the reduction to a chain with k >= 3 or ONE-CLASS's
      shape (def_D = 0, every chain one-body); reported: the cells with no
      GEN row, the k = 1 orbit chains, a one-body box (paths of 1-2 edges),
      and Petersen subdivisions past the box (`COV_BEYOND`).

Verdict: the last line is `OK: every target met`, or `FAILED: ...` with exit
status 1; a mismatch in any mode counts.

Population (labelled graphs, capped; nothing here is a census): the 23 graphs
of `GRAPHS` below, n <= 12 bodies; `--d4` adds the 15 of `GRAPHS4` (seven
triangle-rich graphs, the cube, Petersen, and six sparse graphs, three of them
with def_10 > 0), 38 in all, 36 simple.  Supports: in
--linear and --mixed a section (the plane, the point, the complex, the lines)
is drawn ONCE per stratum per run and reused for every graph; the hinges vary
per graph.  The per-body modes draw their per-body data afresh per graph.
Coordinates are integers in [-COORD, COORD]; combination coefficients are
nonzero integers in that range.  Exact Q throughout (`fractions.Fraction`,
no GF(p)).  The deficiency DP is exponential (3^n), hence n <= 12; `--short`
and `--orbit` work past it, with each deficiency certified by a partition and
a rank; `--coverage` by `core_def`, exact on subdivisions of a core (its
docstring), a DP over the core's bodies.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F
from itertools import combinations, permutations, product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, left_nullspace, wedge2  # noqa: E402
from kbare_common import exact_deficiency  # noqa: E402
from pitch import klein, det4, theta_edges  # noqa: E402
from hybrid_gates import build_rigidity_extensors  # noqa: E402

COORD = 1000


class Degenerate(Exception):
    """A sampled object failed its degeneracy guard."""


def need(cond, msg):
    if not cond:
        raise Degenerate(msg)


# ---------------- counts ----------------

def deficiency(n, edges, D):
    """def_D(G) = max over partitions P of D(|P|-1) - (D-1) e(P), where e(P)
    counts the edges (with multiplicity, loops never) joining distinct parts.
    Subset DP: f(P) = -D - (D-1)|E| + sum_parts [D + (D-1)|E(part)|]."""
    full = (1 << n) - 1
    inside = [0] * (full + 1)
    for S in range(1, full + 1):
        inside[S] = sum(1 for u, v in edges if (S >> u) & 1 and (S >> v) & 1)
    best = [0] * (full + 1)
    for S in range(1, full + 1):
        low = S & -S
        rest = S ^ low
        b, T = None, rest
        while True:
            part = T | low
            val = D + (D - 1) * inside[part] + best[S ^ part]
            if b is None or val > b:
                b = val
            if T == 0:
                break
            T = (T - 1) & rest
        best[S] = b
    return -D - (D - 1) * len(edges) + best[full]


def deficiency_brute(n, edges, D):
    """The same maximum by enumerating set partitions (selftest oracle)."""
    best = 0

    def go(i, assign, k):
        nonlocal best
        if i == n:
            e = sum(1 for u, v in edges if assign[u] != assign[v])
            best = max(best, D * (k - 1) - (D - 1) * e)
            return
        for b in range(k + 1):
            assign.append(b)
            go(i + 1, assign, max(k, b + 1))
            assign.pop()
    go(0, [], 0)
    return best


def rig_rank(n, edges, hinges):
    rows = build_rigidity_extensors(list(range(n)), list(zip(edges, hinges)))
    return rank(rows)


def rig_rank_dot(n, edges, hinges):
    """The body-hinge rank in any screw dimension D = len(C_e): rows
    r (x) (e_u - e_v), r over a basis of the coordinate annihilator of C_e, so
    a motion is (S_v) with S_u - S_v in span C_e.  At D = 6 the Klein
    annihilator of `rig_rank` gives the same motions."""
    D = len(hinges[0])
    rows = []
    for (u, v), C in zip(edges, hinges):
        need(any(C), "zero hinge")
        for r in nullspace([C]):
            row = [F(0)] * (D * n)
            for k in range(D):
                row[D * u + k] += r[k]
                row[D * v + k] -= r[k]
            rows.append(row)
    return rank(rows)


def motion_rank(n, edges, hinges):
    """D(n-1) - |E| + rank{g_e (x) C_e}, g_e = e's column of a cycle basis,
    D = len(C_e) (6 in P^3, 10 in P^4)."""
    D = len(hinges[0])
    cyc = fund_cycles(n, edges)
    M = [[F(z.get(j, 0)) * hinges[j][i] for j in range(len(edges))]
         for z in cyc for i in range(D)]
    return D * (n - 1) - len(edges) + (rank(M) if M else 0)


def fund_cycles(n, edges):
    """Fundamental cycles of a spanning tree, each a signed edge dict; the
    column of edge j across them is g_j, the cographic vector."""
    parent, order = {0: None}, [0]
    while order:
        x = order.pop()
        for j, (u, v) in enumerate(edges):
            for a, b, s in ((u, v, 1), (v, u, -1)):
                if a == x and b not in parent:
                    parent[b] = (x, j, s)
                    order.append(b)
    need(len(parent) == n, "disconnected graph")
    tree = {p[1] for p in parent.values() if p is not None}

    def root_path(x):
        out = {}
        while parent[x] is not None:
            p, j, s = parent[x]
            out[j] = out.get(j, 0) + s
            x = p
        return out
    cyc = []
    for j, (u, v) in enumerate(edges):
        if j in tree:
            continue
        # u -> v along e_j, then v -> root -> u through the tree; the signed
        # root path of x has boundary x - root
        z = {j: 1}
        for k, s in root_path(v).items():
            z[k] = z.get(k, 0) - s
        for k, s in root_path(u).items():
            z[k] = z.get(k, 0) + s
        cyc.append(z)
    return cyc


def lovasz_rank(n, edges, spans):
    """min over F of |E - F| + dim sum_{e in F} g_e (x) L_e: the rank of
    {g_e (x) C_e} at C_e generic in L_e = span(spans[e]) (Lovasz 1977, as
    Tanigawa 2012 Thm 2.1 states it; Rado 1942), by brute force over F."""
    cyc = fund_cycles(n, edges)
    blocks = [[[F(z.get(j, 0)) * b[i] for z in cyc for i in range(len(b))]
               for b in spans[j]] for j in range(len(edges))]
    m = len(edges)
    return min(m - bin(S).count("1")
               + rank([v for j in range(m) if (S >> j) & 1 for v in blocks[j]])
               for S in range(1 << m))


# ---------------- sampling ----------------

class Sampler:
    def __init__(self, seed):
        self.R = random.Random(seed)

    def num(self):
        return F(self.R.randint(-COORD, COORD))

    def pt(self):
        return [self.num() for _ in range(4)]

    def vec(self, k):
        return [self.num() for _ in range(k)]

    def comb(self, basis):
        """A combination with every coefficient nonzero, so a nonzero vector
        whenever `basis` is independent."""
        cs = [F(self.R.choice((-1, 1)) * self.R.randint(1, COORD)) for _ in basis]
        return [sum((c * b[i] for c, b in zip(cs, basis)), F(0))
                for i in range(len(basis[0]))]


def unit(i):
    return [F(int(i == j)) for j in range(4)]


def subspace(pts, dim, what):
    need(rank(pts) == dim, f"{what}: rank {rank(pts)} != {dim}")
    return pts


class Section:
    """A family of lines, hinge by hinge: `draw()` returns one line.  Its
    linear span is measured from SPAN_SAMPLES draws and must have dimension
    D'; every later draw is checked nonzero, decomposable and inside it."""
    SPAN_SAMPLES = 12

    def __init__(self, name, D, draw):
        self.name, self.D, self._draw = name, D, draw
        S = [self._draw() for _ in range(self.SPAN_SAMPLES)]
        self.span = [S[i] for i in _pivots(S)]
        need(len(self.span) == D, f"{name}: span dim {len(self.span)} != {D}")

    def draw(self):
        C = self._draw()
        need(any(C), f"{self.name}: zero hinge")
        need(klein(C, C) == 0, f"{self.name}: not a line")
        need(rank(self.span + [C]) == self.D, f"{self.name}: hinge off span")
        return C


def _pivots(vecs):
    out, acc = [], []
    for i, v in enumerate(vecs):
        if rank(acc + [v]) > len(acc):
            acc.append(v)
            out.append(i)
    return out


def sec_generic(s):
    return Section("generic", 6, lambda: wedge2(s.pt(), s.pt()))


def sec_complex(s, w=None):
    """Lines L of the linear complex of w: klein(L, w) = 0; w nondegenerate."""
    w = w or [s.num() for _ in range(6)]
    need(klein(w, w) != 0, "complex: w is degenerate (a line)")

    def draw():
        a = s.pt()
        row = [klein(wedge2(a, unit(i)), w) for i in range(4)]
        null = nullspace([row])
        need(len(null) == 3, "complex: null plane of a has wrong dimension")
        return wedge2(a, s.comb(null))
    return Section("complex", 5, draw)


def sec_special_complex(s, ell=None):
    """Lines meeting a fixed line ell (the complex of a decomposable w)."""
    ell = subspace(ell or [s.pt(), s.pt()], 2, "special complex: ell")
    return Section("special-cx", 5, lambda: wedge2(s.comb(ell), s.pt()))


def sec_congruence(s, l1=None, l2=None):
    """Lines meeting two skew lines l1, l2."""
    l1, l2 = l1 or [s.pt(), s.pt()], l2 or [s.pt(), s.pt()]
    subspace(l1 + l2, 4, "congruence: l1, l2 not skew")
    return Section("congruence", 4, lambda: wedge2(s.comb(l1), s.comb(l2)))


def sec_regulus(s, lines=None):
    """Lines meeting three pairwise skew lines (one ruling of a quadric)."""
    lines = lines or [[s.pt(), s.pt()] for _ in range(3)]
    for a, b in combinations(lines, 2):
        subspace(a + b, 4, "regulus: two of the lines are not skew")
    l1, l2, l3 = lines

    def draw():
        a = s.comb(l1)   # the transversal through a: its plane with l2 cut by l3
        d1, d2 = det4([a, l2[0], l2[1], l3[0]]), det4([a, l2[0], l2[1], l3[1]])
        c = [d2 * x - d1 * y for x, y in zip(l3[0], l3[1])]
        C = wedge2(a, c)
        for m in lines:
            need(klein(C, wedge2(m[0], m[1])) == 0, "regulus: misses a line")
        return C
    return Section("regulus", 3, draw)


def sec_plane(s, H=None):
    H = subspace(H or [s.pt() for _ in range(3)], 3, "plane: H")
    return Section("plane", 3, lambda: wedge2(s.comb(H), s.comb(H)))


def sec_star(s, O=None):
    O = O or s.pt()
    need(any(O), "star: O = 0")
    return Section("star", 3, lambda: wedge2(O, s.pt()))


def sec_planar_pencil(s, H=None, O=None):
    """Lines of one plane H through one point O of it."""
    H = subspace(H or [s.pt() for _ in range(3)], 3, "planar pencil: H")
    O = O or s.comb(H)
    need(rank(H + [O]) == 3 and any(O), "planar pencil: O not a point of H")
    return Section("planar-pencil", 2, lambda: wedge2(O, s.comb(H)))


LINEAR = [sec_generic, sec_complex, sec_special_complex, sec_congruence,
          sec_regulus, sec_plane, sec_star, sec_planar_pencil]


def body_guard(n, edges, hinges):
    """No two hinges at a body coincide, except along parallel edges."""
    for v in range(n):
        at = [(frozenset(e), C) for e, C in zip(edges, hinges) if v in e]
        for (e, C), (f, Cp) in combinations(at, 2):
            if e != f:
                need(rank([C, Cp]) == 2, f"two hinges coincide at body {v}")


def envelope(s, sec, m):
    return [s.comb(sec.span) for _ in range(m)]


# ---------------- per-body strata ----------------

def molecular(s, n, edges):
    p = [s.pt() for _ in range(n)]
    return [wedge2(p[u], p[v]) for u, v in edges]


def panel(s, n, edges):
    N = [s.pt() for _ in range(n)]
    out = []
    for u, v in edges:
        ns = nullspace([N[u], N[v]])
        need(len(ns) == 2, "panel: normals of adjacent bodies proportional")
        out.append(wedge2(ns[0], ns[1]))
    return out


def lifting_space(n, edges, q):
    """L(q): heights z, affine in the picture on every closed neighbourhood.
    The picture q lies in K^k, k = len(q[0]) (k = 2 for P^3, 3 for P^4); a
    closed neighbourhood must be affinely independent or spanning."""
    k = len(q[0])
    nb = {v: sorted({w for e in edges if v in e for w in e} - {v})
          for v in range(n)}
    rows = []
    for v in range(n):
        N = [v] + nb[v]
        A = [list(q[w]) + [F(1)] for w in N]
        need(rank(A) == min(len(N), k + 1), f"picture not admissible at body {v}")
        for phi in left_nullspace(A):
            r = [F(0)] * n
            for w, c in zip(N, phi):
                r[w] += c
            rows.append(r)
    L = nullspace(rows) if rows else [[F(int(i == j)) for i in range(n)]
                                      for j in range(n)]
    affine = [[q[w][i] for w in range(n)] for i in range(k)] + [[F(1)] * n]
    need(rank(L) >= k + 1 and rank(L + affine) == rank(L),
         "L(q) misses the affine heights")
    return L


def pencil(s, n, edges, flat=False):
    q = [(s.num(), s.num()) for _ in range(n)]
    for u, v in edges:
        need(q[u] != q[v], "picture: adjacent bodies coincide")
    z = [F(0)] * n if flat else s.comb(lifting_space(n, edges, q))
    p = [[q[v][0], q[v][1], z[v], F(1)] for v in range(n)]
    return [wedge2(p[u], p[v]) for u, v in edges]


# ---------------- graphs ----------------

def relabel(edges):
    vs = sorted({w for e in edges for w in e})
    ix = {v: i for i, v in enumerate(vs)}
    return len(vs), [(ix[u], ix[v]) for u, v in edges]


def cyc(k):
    return k, [(i, (i + 1) % k) for i in range(k)]


def complete(k):
    return k, list(combinations(range(k), 2))


def kbip(a, b):
    return a + b, [(i, a + j) for i in range(a) for j in range(b)]


def wheel(k):
    return k + 1, [(i, (i + 1) % k) for i in range(k)] + [(i, k) for i in range(k)]


def double(g):
    return g[0], g[1] + g[1]


def ears_on_k23(k):
    n, E = kbip(2, 3)
    for i in range(k):
        a, b = (0, 1) if i % 2 == 0 else (2, 3)
        E += [(a, n), (n, n + 1), (n + 1, b)]
        n += 2
    return n, E


def ring_k4(m):
    n, E = 0, []
    for _ in range(m):
        E += [(n + i, n + j) for i, j in combinations(range(4), 2)]
        n += 4
    E += [(4 * i + 3, (4 * (i + 1)) % n) for i in range(m)]
    return n, E


def rand_graph(n, e, seed):
    """A Hamilton cycle plus random chords (a fixed, seeded shape)."""
    r = random.Random(seed)
    E = [(i, (i + 1) % n) for i in range(n)]
    while len(E) < e:
        u, v = r.sample(range(n), 2)
        if (u, v) not in E and (v, u) not in E:
            E.append((u, v))
    return n, E


GRAPHS = {
    "C6": cyc(6), "C7": cyc(7), "C8": cyc(8), "C9": cyc(9),
    "K4": complete(4), "K5": complete(5), "K2,3": kbip(2, 3),
    "K3,3": kbip(3, 3), "K2,5": kbip(2, 5), "W5": wheel(5),
    "prism": (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                  (0, 3), (1, 4), (2, 5)]),
    "bowtie": (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]),
    "2C4": double(cyc(4)), "2C5": double(cyc(5)),
    "theta333": relabel(theta_edges([3, 3, 3])),
    "theta2333": relabel(theta_edges([2, 3, 3, 3])),
    "K23+1ear": ears_on_k23(1), "K23+2ear": ears_on_k23(2),
    "ringK4x3": ring_k4(3),
    "rnd8-10": rand_graph(8, 10, 7), "rnd8-11": rand_graph(8, 11, 8),
    "rnd9-12": rand_graph(9, 12, 9), "rnd9-13": rand_graph(9, 13, 10),
}


def simple(edges):
    return len(set(map(frozenset, edges))) == len(edges)


# ---------------- modes ----------------

def mode_linear(s):
    secs = [mk(s) for mk in LINEAR]
    print("cell = rank at a point / 6(n-1)-def_D' [rank at the per-edge "
          "envelope]; * marks a mismatch")
    print(f"{'graph':10}{'n':>3}{'e':>3} "
          + " ".join(f"{x.name}({x.D})".rjust(17) for x in secs))
    bad = 0
    for g, (n, E) in GRAPHS.items():
        cells = []
        for x in secs:
            H = [x.draw() for _ in E]
            body_guard(n, E, H)
            got, pred = rig_rank(n, E, H), 6 * (n - 1) - deficiency(n, E, x.D)
            env = rig_rank(n, E, envelope(s, x, len(E)))
            ok = got == pred == env
            bad += not ok
            cells.append(f"{got}/{pred}[{env}]" + ("" if ok else "*"))
        print(f"{g:10}{n:>3}{len(E):>3} " + " ".join(c.rjust(17) for c in cells))
    print(f"mismatches: {bad} of {len(GRAPHS) * len(secs)}")
    return bad


MIXED = [("ringK4x3", sec_plane, [range(0, 6), range(6, 12)]),
         ("ringK4x3", sec_regulus, [range(0, 6), range(6, 12), range(12, 18)]),
         ("theta333", sec_plane, [range(0, 3), range(3, 6)]),
         ("theta333", sec_complex, [range(0, 6)]),
         ("K23+2ear", sec_star, [range(0, 6), range(6, 12)]),
         ("rnd9-13", sec_planar_pencil, [range(0, 5), range(5, 10)]),
         ("rnd9-13", sec_regulus, [range(0, 7), range(7, 13)])]


def mode_mixed(s):
    print("each block in its own section, the other edges generic: "
          "rank at a point [rank at the per-edge envelope]")
    bad = 0
    for g, mk, blocks in MIXED:
        n, E = GRAPHS[g]
        gen = sec_generic(s)
        H = [gen.draw() for _ in E]
        env = envelope(s, gen, len(E))
        for blk in blocks:
            x = mk(s)
            for i in blk:
                H[i], env[i] = x.draw(), s.comb(x.span)
        body_guard(n, E, H)
        a, b = rig_rank(n, E, H), rig_rank(n, E, env)
        bad += a != b
        print(f"  {g:10}{x.name:14}blocks {[len(b_) for b_ in blocks]}: "
              f"{a} [{b}]" + ("" if a == b else "  *"))
    print(f"mismatches: {bad} of {len(MIXED)}")
    return bad


def mode_perbody(s):
    print("rank at a point / 6(n-1)-def_6 (pencil-flat: / 6(n-1)-def_3); "
          "pencil only at simple graphs of minimum degree 2")
    bad = 0
    for g, (n, E) in GRAPHS.items():
        t6 = 6 * (n - 1) - deficiency(n, E, 6)
        t3 = 6 * (n - 1) - deficiency(n, E, 3)
        runs = [("molecular", molecular(s, n, E), t6),
                ("panel", panel(s, n, E), t6)]
        if simple(E) and min(sum(v in e for e in E) for v in range(n)) >= 2:
            runs += [("pencil", pencil(s, n, E), t6),
                     ("pencil-flat", pencil(s, n, E, flat=True), t3)]
        cells = []
        for name, H, t in runs:
            body_guard(n, E, H)
            r = rig_rank(n, E, H)
            bad += r != t
            cells.append(f"{name} {r}/{t}" + ("" if r == t else "*"))
        print(f"  {g:10}" + "   ".join(cells))
    print(f"mismatches: {bad}")
    return bad


def mode_examples(s):
    n, E = GRAPHS["C6"]
    draws, vecs, ranks = 40, [], set()
    for _ in range(draws):
        x = sec_star(s)          # a fresh common point per draw
        H = [x.draw() for _ in E]
        vecs.append([c for C in H for c in C])
        ranks.add(rig_rank(n, E, H))
    print(f"(a) C6, all hinges through one point, the point redrawn per draw: "
          f"span of {draws} draws has dimension {rank(vecs)} of {6 * len(E)}; "
          f"rigidity ranks {sorted(ranks)}; count at a fixed point "
          f"{6 * (n - 1) - deficiency(n, E, 3)}; generic "
          f"{6 * (n - 1) - deficiency(n, E, 6)}")
    x, gen = sec_special_complex(s), sec_generic(s)
    half = [x.draw() for _ in range(3)] + [gen.draw() for _ in range(3)]
    allm = [x.draw() for _ in range(6)]
    rh, ra = rig_rank(n, E, half), rig_rank(n, E, allm)
    print(f"(b) C6, hinges meeting one fixed line: three of them -> rank "
          f"{rh}; all six -> rank {ra}")
    bad = (rank(vecs) != 36) + (ranks != {27}) + (rh != 30) + (ra != 29)
    print(f"mismatches against the note's sentences: {bad}")
    return bad


def expect_reject(what, thunk):
    try:
        thunk()
    except Degenerate:
        return
    raise SystemExit(f"selftest FAILED: guard accepted {what}")


def mode_selftest(s):
    p = s.pt
    # (1) each guard rejects a constructed witness; its negative control passes
    a, b = p(), p()
    mid = [x + y for x, y in zip(a, b)]
    witnesses = [
        ("plane on three collinear points", lambda: sec_plane(s, [a, b, mid]),
         lambda: sec_plane(s)),
        ("congruence on two meeting lines",
         lambda: sec_congruence(s, [a, b], [a, p()]), lambda: sec_congruence(s)),
        ("regulus with two meeting lines",
         lambda: sec_regulus(s, [[a, b], [a, p()], [p(), p()]]),
         lambda: sec_regulus(s)),
        ("complex of a line (degenerate w)",
         lambda: sec_complex(s, wedge2(a, b)), lambda: sec_complex(s)),
        ("special complex on a doubled point", lambda: sec_special_complex(s, [a, a]),
         lambda: sec_special_complex(s)),
        ("planar pencil with O off H",
         lambda: sec_planar_pencil(s, [unit(0), unit(1), unit(2)], unit(3)),
         lambda: sec_planar_pencil(s)),
        ("a section declared at the wrong span dimension",
         lambda: Section("star-as-4", 4, sec_star(s)._draw), lambda: sec_star(s)),
        ("two equal hinges at a body",
         lambda: body_guard(3, [(0, 1), (0, 2)], [wedge2(a, b)] * 2),
         lambda: body_guard(3, [(0, 1), (0, 2)], [wedge2(a, b), wedge2(a, p())])),
        ("a picture with a collinear closed neighbourhood",
         lambda: lifting_space(3, [(0, 1), (1, 2), (2, 0)],
                               [(F(0), F(0)), (F(1), F(1)), (F(2), F(2))]),
         lambda: lifting_space(3, [(0, 1), (1, 2), (2, 0)],
                               [(F(0), F(0)), (F(1), F(0)), (F(0), F(1))])),
    ]
    for what, bad, good in witnesses:
        expect_reject(what, bad)
        good()
    x = sec_plane(s)
    off = wedge2(p(), p())
    expect_reject("a hinge off its section's span",
                  lambda: Section.draw(type("W", (), {
                      "_draw": lambda self: off, "name": "plane",
                      "span": x.span, "D": 3})()))
    print(f"guards: {len(witnesses) + 1} witnesses rejected, controls passed")
    # (2) the deficiency oracles agree
    checked = 0
    for g, (n, E) in GRAPHS.items():
        for D in (2, 3, 4, 5, 6):
            if n <= 9:
                assert deficiency(n, E, D) == deficiency_brute(n, E, D), (g, D)
                checked += 1
        if simple(E):
            assert deficiency(n, E, 6) == exact_deficiency(E)[0], g
            checked += 1
    print(f"deficiency: {checked} agreements (DP vs partitions at n <= 9, all "
          f"D in 2..6; DP vs kbare_common.exact_deficiency at D = 6, simple)")
    # (3) the motion identity at sampled strata
    cases = [("C6", sec_complex), ("theta333", sec_regulus),
             ("rnd8-10", sec_plane), ("K2,3", sec_generic),
             ("2C5", sec_congruence), ("ringK4x3", sec_star)]
    for g, mk in cases:
        n, E = GRAPHS[g]
        x = mk(s)
        H = [x.draw() for _ in E]
        assert rig_rank(n, E, H) == motion_rank(n, E, H), g
    print(f"motion identity: {len(cases)} cases agree")
    print("selftest passed")
    return 0


# ---------------- per-body complexes in P^3 (next test 4) ----------------

def unit6(i):
    return [F(int(i == j)) for j in range(6)]


def complex_span(ws):
    """{C : klein(C, w) = 0 for every w in ws}: the span of the lines of the
    linear congruence cut by the complexes ws (4-dim for two of them)."""
    return nullspace([[klein(unit6(i), w) for i in range(6)] for w in ws])


def perbody_special(s, n, edges):
    """Each body v has a line ell_v; hinge uv joins a point of ell_u to a
    point of ell_v (all lines meeting both, ell_u and ell_v skew)."""
    ell = [subspace([s.pt(), s.pt()], 2, "special: ell_v") for _ in range(n)]
    for u, v in edges:
        subspace(ell[u] + ell[v], 4, "special: adjacent axes not skew")
    W = [wedge2(*x) for x in ell]
    H = [wedge2(s.comb(ell[u]), s.comb(ell[v])) for u, v in edges]
    return H, [complex_span([W[u], W[v]]) for u, v in edges]


def perbody_complex(s, n, edges):
    """Each body v has a nondegenerate linear complex w_v; hinge uv is the
    line through a random point a lying in both complexes (the meet of a's
    two null planes)."""
    w = []
    for _ in range(n):
        x = [s.num() for _ in range(6)]
        need(klein(x, x) != 0, "complex: w_v degenerate")
        w.append(x)
    H = []
    for u, v in edges:
        a = s.pt()
        null = nullspace([[klein(wedge2(a, unit(i)), w[b]) for i in range(4)]
                          for b in (u, v)])
        need(len(null) == 2, "complex: the two null planes of a coincide")
        C = wedge2(*null)
        need(klein(C, w[u]) == 0 == klein(C, w[v]), "complex: hinge off a complex")
        H.append(C)
    return H, [complex_span([w[u], w[v]]) for u, v in edges]


LOVASZ_MAX_EDGES = 9


def mode_complexes(s):
    print("per-body complexes: rank at a point / 6(n-1)-def_6 [rank at the "
          "per-edge envelope L_uv = {w_u, w_v}^perp; at |E| <= "
          f"{LOVASZ_MAX_EDGES} also | the min-max 6(n-1)-|E|+min_F(...)]")
    bad, checked = 0, 0
    for g, (n, E) in GRAPHS.items():
        t6 = 6 * (n - 1) - deficiency(n, E, 6)
        cells = []
        for name, mk in (("special", perbody_special), ("complex", perbody_complex)):
            H, Ls = mk(s, n, E)
            for C, L in zip(H, Ls):
                need(len(L) == 4 and rank(L + [C]) == 4 and klein(C, C) == 0,
                     f"{name}: hinge off its congruence")
            body_guard(n, E, H)
            r = rig_rank(n, E, H)
            env = rig_rank(n, E, [s.comb(L) for L in Ls])
            ok = r == t6 == env
            lv = ""
            if len(E) <= LOVASZ_MAX_EDGES:
                lr = 6 * (n - 1) - len(E) + lovasz_rank(n, E, Ls)
                ok, checked, lv = ok and lr == env, checked + 1, f"|{lr}"
            bad += not ok
            cells.append(f"{name} {r}/{t6}[{env}{lv}]" + ("" if ok else "*"))
        print(f"  {g:10}" + "   ".join(cells))
    print(f"min-max agreements checked: {checked}; mismatches: {bad}")
    return bad


# ---------------- P^4 (next tests 2 and 3) ----------------
#
# A hinge of a body-hinge framework in P^4 is a plane (a 3-dim subspace of
# K^5), recorded by its Pluecker vector in Lambda^3 K^5 = K^10.  The rank is
# a function of the hinge vectors up to one common linear isomorphism of the
# screw space, so a configuration may equally be recorded through its polar
# dual (hinge planes W <-> lines W^perp, in Lambda^2 K^5): the containments
# reverse, "hinges at v contain the point p_v" <-> "the dual lines lie in the
# hyperplane p_v^perp", "... lie in the hyperplane B_v" <-> "... pass through
# the point B_v^perp", "... contain the line A_v" <-> "... lie in the plane
# A_v^perp".  Each sampler states which form it uses; one framework never
# mixes them.  Ranks come from the motion identity at D = 10, cross-checked
# against `rig_rank_dot` on the first graphs.

def det_exact(M):
    M = [r[:] for r in M]
    k, out = len(M), F(1)
    for c in range(k):
        p = next((i for i in range(c, k) if M[i][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            out = -out
        out *= M[c][c]
        for i in range(c + 1, k):
            f = M[i][c] / M[c][c]
            M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return out


def ext(vecs):
    """Pluecker vector of span(vecs): the maximal minors, columns in
    lexicographic order (at k = 2, m = 4 this is `wedge2`'s PL order)."""
    m = len(vecs[0])
    return [det_exact([[v[c] for c in cols] for v in vecs])
            for cols in combinations(range(m), len(vecs))]


def span_cap(U, W):
    """A basis of span(U) cap span(W)."""
    null = nullspace([[x[i] for x in U] + [-y[i] for y in W]
                      for i in range(len(U[0]))])
    pts = [[sum((c * x[i] for c, x in zip(z, U)), F(0)) for i in range(len(U[0]))]
           for z in null]
    return [pts[i] for i in _pivots(pts)]


def hinge_plane(vecs):
    """The Lambda^3 vector of the plane spanned by `vecs` (rank 3 required)."""
    idx = _pivots(vecs)
    need(len(idx) == 3, f"hinge spans dimension {len(idx)}, not a plane")
    return ext([vecs[i] for i in idx])


def d4_generic(s, n, edges):
    """Dual form: a random line per hinge."""
    return [ext([s.vec(5), s.vec(5)]) for _ in edges]


def d4_panel(s, n, edges, b=None):
    """Hinges at v in a hyperplane B_v.  Dual form: the line b_u b_v,
    b_v = B_v^perp (the P^4 molecular configuration)."""
    b = b or [s.vec(5) for _ in range(n)]
    for u, v in edges:
        need(rank([b[u], b[v]]) == 2, "panel: adjacent B coincide")
    return [ext([b[u], b[v]]) for u, v in edges]


def d4_point(s, n, edges):
    """Hinges at v through a point p_v.  Dual form: hinge uv a random line in
    the plane p_u^perp cap p_v^perp."""
    P = [s.vec(5) for _ in range(n)]
    out = []
    for u, v in edges:
        pl = subspace(nullspace([P[u], P[v]]), 3, "point: adjacent p coincide")
        out.append(ext(subspace([s.comb(pl), s.comb(pl)], 2, "point: hinge")))
    return out


def d4_pencil(s, n, edges, flat=False):
    """Hinges at v through p_v and inside B_v, with p_w in B_v for w in N[v].
    Dual form, lifted: b_v = (q_v, z_v, 1) with q a picture in K^3 and z in
    the lifting space (affine in q on every closed neighbourhood), so b_N[v]
    lies in a hyperplane; hinge b_u b_v.  flat: z = 0, every b_v in one
    hyperplane, so hinges in Lambda^2 K^4 (the P^3 molecular count def_6)."""
    q = [s.vec(3) for _ in range(n)]
    z = [F(0)] * n if flat else s.comb(lifting_space(n, edges, q))
    return d4_panel(s, n, edges, [q[v] + [z[v], F(1)] for v in range(n)])


def d4_lineplane(s, n, edges, flat=False):
    """Hinges at v contain a line A_v and lie in a hyperplane B_v.  Dual form:
    hinge lines through b_v inside the plane pi_v, so b_N[v] is coplanar;
    lifted from a planar picture q by two heights z, w in L(q).  flat:
    z = w = 0, every b_v in one plane (the planar count def_3)."""
    q = [s.vec(2) for _ in range(n)]
    L = lifting_space(n, edges, q)
    z, w = ([F(0)] * n, [F(0)] * n) if flat else (s.comb(L), s.comb(L))
    return d4_panel(s, n, edges, [q[v] + [z[v], w[v], F(1)] for v in range(n)])


def d4_line_concurrent(s, n, edges):
    """Hinges at v contain a line A_v, adjacent lines meet (primal form).
    Every A_v through one point o: hinge o ^ a_u ^ a_v, the P^3 molecular
    configuration in K^5/o (count def_6)."""
    o = s.vec(5)
    a = [s.vec(5) for _ in range(n)]
    return [hinge_plane([o, a[u], a[v]]) for u, v in edges]


def degeneracy_order(n, edges):
    """Remove a minimum-degree vertex repeatedly (ties: the least label);
    reversed, every vertex has at most the degeneracy many earlier
    neighbours."""
    adj = {v: {w for e in edges if v in e for w in e} - {v} for v in range(n)}
    left, out = set(range(n)), []
    while left:
        v = min(left, key=lambda x: (len(adj[x] & left), x))
        out.append(v)
        left.remove(v)
    return out[::-1], adj


def transversal(A1, A2, A3):
    """The line meeting three lines of P^4 that span it: through
    a = A1 cap span(A2, A3), meeting A3 inside span(a, A2)."""
    need(rank(A2 + A3) == 4, "transversal: A2, A3 not skew")
    a = span_cap(A1, A2 + A3)
    need(len(a) == 1, "transversal: A1 does not cut span(A2, A3) in a point")
    c = span_cap([a[0]] + A2, A3)
    need(len(c) == 1, "transversal: no point on A3")
    return [a[0], c[0]]


def d4_line_constructive(s, n, edges):
    """The same stratum, built line by line in degeneracy order.  A_v must
    meet each earlier neighbour's line; if two of those lines meet at m,
    A_v passes through m (else A_v lies in their plane and two hinges at v
    coincide).  Two forced points fix A_v; one forced point plus at most one
    further line; none: up to two lines (a point on each), or three (their
    transversal).  Anything else raises Degenerate."""
    order, adj = degeneracy_order(n, edges)
    A = {}
    for v in order:
        U = [u for u in sorted(adj[v]) if u in A]
        forced = []
        for u, w in combinations(U, 2):
            m = span_cap(A[u], A[w])
            need(len(m) <= 1, "constructive: two earlier lines coincide")
            if m and all(rank([m[0], f]) == 2 for f in forced):
                forced.append(m[0])
        if len(forced) >= 2:
            line = forced[:2]
            need(all(rank(line + [f]) == 2 for f in forced),
                 "constructive: forced points not collinear")
        elif forced:
            rest = [u for u in U if rank(A[u] + forced) == 3]
            need(len(rest) <= 1, "constructive: a forced point and two more lines")
            line = forced + [s.comb(A[rest[0]]) if rest else s.vec(5)]
        elif len(U) <= 2:
            line = [s.comb(A[u]) for u in U] + [s.vec(5) for _ in range(2 - len(U))]
        else:
            need(len(U) == 3, "constructive: four earlier lines, no forced point")
            line = transversal(*[A[u] for u in U])
        subspace(line, 2, "constructive: A_v")
        for u in U:
            need(rank(A[u] + line) == 3, "constructive: A_v misses a neighbour")
        A[v] = line
    return [hinge_plane(A[u] + A[v]) for u, v in edges]


def ear_cycle(k, every=1):
    """C_k with a triangle ear on every `every`-th edge."""
    n, E = cyc(k)
    for i in range(0, k, every):
        E += [(i, n), (n, (i + 1) % k)]
        n += 1
    return n, E


def triangle_ring(m):
    n, E = 0, []
    for _ in range(m):
        E += [(n, n + 1), (n + 1, n + 2), (n + 2, n)]
        n += 3
    E += [(3 * i + 2, (3 * (i + 1)) % n) for i in range(m)]
    return n, E


GRAPHS4 = dict(GRAPHS, **{
    "diamond": (4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]),
    "octa": (6, [e for e in combinations(range(6), 2)
                 if e not in ((0, 1), (2, 3), (4, 5))]),
    "strip8": (8, [(i, i + 1) for i in range(7)] + [(i, i + 2) for i in range(6)]),
    "friend3": (7, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0),
                    (0, 5), (5, 6), (6, 0)]),
    "W7": wheel(7), "C6ears": ear_cycle(6), "triring4": triangle_ring(4),
    "cube": (8, [(i, i ^ b) for i in range(8) for b in (1, 2, 4) if i < i ^ b]),
    "petersen": (10, [(i, (i + 1) % 5) for i in range(5)]
                 + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
                 + [(i, i + 5) for i in range(5)]),
    # sparse: def_6 > def_10 or def_4 > 0; C11, C12, C5-C5 have def_10 > 0
    "C11": cyc(11), "C12": cyc(12), "C11ear": ear_cycle(11, 11),
    "C9ears3": ear_cycle(9, 3), "theta444": relabel(theta_edges([4, 4, 4])),
    "C5-C5": (10, cyc(5)[1] + [(5 + i, 5 + (i + 1) % 5) for i in range(5)]
              + [(0, 5)]),
})


def mode_residual4(s):
    print("Result 9's flat base: hinge planes of P^4 inside one hyperplane H, "
          "the one at uv through p_u, p_v (a pencil each).  rank in P^4 / "
          "10(n-1)-def_4; the D = 4 residual / 4(n-1)-def_4")
    bad = 0
    for i, (g, (n, E)) in enumerate(GRAPHS.items()):
        p = [s.pt() for _ in range(n)]
        H4 = [ext(subspace([p[u], p[v], s.pt()], 3, "residual: hinge"))
              for u, v in E]
        H10 = [hinge_plane([p[u] + [F(0)], p[v] + [F(0)], s.pt() + [F(0)]])
               for u, v in E]
        body_guard(n, E, H4)
        body_guard(n, E, H10)
        d4 = deficiency(n, E, 4)
        r10, r4 = motion_rank(n, E, H10), motion_rank(n, E, H4)
        if i < 4:
            assert r10 == rig_rank_dot(n, E, H10) and r4 == rig_rank_dot(n, E, H4), g
        t10, t4 = 10 * (n - 1) - d4, 4 * (n - 1) - d4
        ok = r10 == t10 and r4 == t4
        bad += not ok
        print(f"  {g:10}P^4 {r10}/{t10}   D=4 {r4}/{t4}" + ("" if ok else "  *"))
    print(f"mismatches: {bad}")
    return bad


D4_TYPES = [
    # (column, sampler, count it is asserted against or None, simple only)
    ("generic", d4_generic, 10, False),
    ("panel", d4_panel, 10, True),
    ("point", d4_point, None, False),
    ("pencil", d4_pencil, None, True),
    ("pencil0", lambda s, n, E: d4_pencil(s, n, E, flat=True), 6, True),
    ("line-o", d4_line_concurrent, 6, True),
    ("line-x", d4_line_constructive, None, True),
    ("line+hyp", d4_lineplane, None, True),
    ("l+h0", lambda s, n, E: d4_lineplane(s, n, E, flat=True), 3, True),
]


def mode_d4(s):
    print("P^4 per-body flag strata (hinges at v contain no flat / a point / "
          "a line, and lie in a hyperplane or not).  Cell: the rank at a "
          "point, a LOWER bound for the stratum's generic rank; every cell is "
          "at most t = 10(n-1)-def_10.  Asserted cells (generic, panel: = t; "
          "pencil0, line-o: = 10(n-1)-def_6; l+h0: = 10(n-1)-def_3) carry * on "
          "a mismatch; the rest print '<' when below t, '-' when the sampler "
          "or the stratum is degenerate there, '.' when not applicable "
          "(coupled types at multigraphs).")
    print(f"{'graph':10}{'n':>3}{'e':>3}{'d10':>4}{'d6':>4}{'d4':>4}{'d3':>4}"
          f"{'t':>5} " + "".join(f"{c:>9}" for c, *_ in D4_TYPES))
    bad, below = 0, {}
    for i, (g, (n, E)) in enumerate(GRAPHS4.items()):
        d = {D: deficiency(n, E, D) for D in (10, 6, 4, 3)}
        t = 10 * (n - 1) - d[10]
        cells = []
        for col, mk, D, simple_only in D4_TYPES:
            if simple_only and not simple(E):
                cells.append(".")
                continue
            try:
                H = mk(s, n, E)
                body_guard(n, E, H)
            except Degenerate:
                cells.append("-")
                continue
            r = motion_rank(n, E, H)
            if i < 3:
                assert r == rig_rank_dot(n, E, H), (g, col)
            assert r <= t, (g, col)
            if D is not None:
                ok = r == 10 * (n - 1) - d[D]
                bad += not ok
                cells.append(f"{r}" + ("" if ok else "*"))
            else:
                below.setdefault(col, []).extend([g] if r < t else [])
                cells.append(f"{r}" + ("<" if r < t else ""))
        print(f"{g:10}{n:>3}{len(E):>3}{d[10]:>4}{d[6]:>4}{d[4]:>4}{d[3]:>4}"
              f"{t:>5} " + "".join(f"{c:>9}" for c in cells))
    for col, gs in below.items():
        print(f"  {col}: below t at {len(gs)} graph(s){': ' + ', '.join(gs) if gs else ''}")
    print(f"mismatches (asserted cells): {bad}")
    return bad


def diamond_ring(m):
    """m copies of K_4 - e joined in a ring through their degree-2 vertices:
    cubic, n = 4m, def_3 >= m - 3 (the ring partition)."""
    n, E = 0, []
    for _ in range(m):
        E += [(n, n + 1), (n, n + 2), (n + 1, n + 2), (n + 1, n + 3), (n + 2, n + 3)]
        n += 4
    E += [(4 * i + 3, (4 * (i + 1)) % n) for i in range(m)]
    return n, E


def mode_lifting(s):
    print("lifting spaces at a seeded picture: dim L(q) - (k+1) against "
          "def_(k+1), k = 2 (the planar picture of line+hyp; = is asserted at "
          "simple graphs, the blueprint's dim L(q) = 3 + def_3) and k = 3 (the "
          "picture of the P^4 pencil; reported)")
    bad, neq, lt = 0, [], []
    for g, (n, E) in GRAPHS4.items():
        cells = []
        for k in (2, 3):
            dl = len(lifting_space(n, E, [s.vec(k) for _ in range(n)])) - k - 1
            d = deficiency(n, E, k + 1)
            if k == 2 and simple(E):
                bad += dl != d
            if k == 3:
                neq += [g] if dl != d else []
                lt += [g] if dl < d else []
            cells.append(f"k={k}: {dl} vs {d}" + ("" if dl == d else " <>"))
        print(f"  {g:10}" + "   ".join(cells))
    print(f"  k = 3: unequal at {len(neq)} of {len(GRAPHS4)}, below def_4 at "
          f"{len(lt)}{': ' + ', '.join(lt) if lt else ''}")
    print("cubic rings of diamonds, past the DP cap (n = 4m): rank at a point "
          "against 10(n-1), the trivial ceiling, so a match certifies")
    for m in (3, 4, 5):
        n, E = diamond_ring(m)
        dl = len(lifting_space(n, E, [s.vec(2) for _ in range(n)])) - 3
        r = {}
        for col, mk, *_ in D4_TYPES:
            if col in ("generic", "pencil", "line+hyp", "l+h0"):
                H = mk(s, n, E)
                body_guard(n, E, H)
                r[col] = motion_rank(n, E, H)
        top = 10 * (n - 1)
        ok = r["generic"] == r["pencil"] == r["line+hyp"] == top \
            and r["l+h0"] == top - dl
        bad += not ok
        print(f"  m={m} n={n}: dim L(q)-3 = {dl}; generic {r['generic']}, pencil "
              f"{r['pencil']}, line+hyp {r['line+hyp']}, l+h0 {r['l+h0']} "
              f"(= 10(n-1) - (dim L(q)-3) = {top - dl})" + ("" if ok else "  *"))
    print(f"mismatches: {bad}")
    return bad


PD_DIMS = (2, 3, 4, 5, 6)


def pd_pencil(s, n, edges, d, q, L):
    """The pencil of P^d, dual form: b_v = (q_v, z^1_v, ..., z^(d-2)_v, 1),
    q a planar picture and every z^i in L(q), so every coordinate is affine in
    q on each closed neighbourhood and b_N[v] lies in a plane; hinge the line
    b_u b_v in Lambda^2 K^(d+1).  d = 3 is `pencil`, d = 4 `d4_lineplane`.
    Returns the points and the hinges."""
    hs = [s.comb(L) for _ in range(d - 2)]
    b = [list(q[v]) + [h[v] for h in hs] + [F(1)] for v in range(n)]
    for u, v in edges:
        need(rank([b[u], b[v]]) == 2, "pencil: adjacent points coincide")
    return b, [ext([b[u], b[v]]) for u, v in edges]


def mode_pd(s):
    print("the pencil of P^d, d = 2..6, D = C(d+1,2): a planar picture plus d-2 "
          "heights in L(q).  Cell: rank at a point / t = D(n-1) - def_D; '*' "
          "marks a mismatch at d = 2, 3 (Katoh-Tanigawa at d = 2; Phase 40), "
          "'<' a point below t at d >= 4 (reported), 's' the stable range "
          "d >= dim L(q) - 1.  Asserted at every graph: dim L(q) = 3 + def_3 "
          "(simple graphs), def_C(l,2) = def_inf with l = 3 + def_3 (every "
          "graph), the points spanning min(d+1, l) dimensions, and at stable d "
          "def_D = def_inf.")
    print(f"{'graph':10}{'n':>3}{'e':>3}{'d3':>4}{'dinf':>5}{'l':>4} "
          + "".join(f"{'d=' + str(d):>13}" for d in PD_DIMS))
    bad, below = 0, {}
    for i, (g, (n, E)) in enumerate(GRAPHS4.items()):
        dfc = {}

        def df(D):
            if D not in dfc:
                dfc[D] = deficiency(n, E, D)
            return dfc[D]
        d3, dinf = df(3), df(n + 2)  # D - 1 > n: only tree quotients count
        l3 = 3 + d3
        bad += df(l3 * (l3 - 1) // 2) != dinf
        if not simple(E):
            print(f"{g:10}{n:>3}{len(E):>3}{d3:>4}{dinf:>5}{'.':>4}  (multigraph: "
                  f"def lemma only)")
            continue
        q = [s.vec(2) for _ in range(n)]
        L = lifting_space(n, E, q)
        ell = len(L)
        bad += ell != l3
        cells = []
        for d in PD_DIMS:
            D = (d + 1) * d // 2
            try:
                b, H = pd_pencil(s, n, E, d, q, L)
                body_guard(n, E, H)
                need(rank(b) == min(d + 1, ell), "points span too little")
            except Degenerate:
                cells.append("-")
                continue
            r = motion_rank(n, E, H)
            if i < 2:
                assert r == rig_rank_dot(n, E, H), (g, d)
            t = D * (n - 1) - df(D)
            assert r <= t, (g, d)
            stable = d >= ell - 1
            if stable:
                bad += df(D) != dinf
            mark = ""
            if r != t:
                mark = "*" if d <= 3 else "<"
                if d <= 3:
                    bad += 1
                else:
                    below.setdefault(d, []).append(g)
            cells.append(f"{r}/{t}{mark}{'s' if stable else ''}")
        print(f"{g:10}{n:>3}{len(E):>3}{d3:>4}{dinf:>5}{ell:>4} "
              + "".join(f"{c:>13}" for c in cells))
    for d in PD_DIMS[2:]:
        gs = below.get(d, [])
        print(f"  d={d}: below t at {len(gs)} graph(s)" + (": " + ", ".join(gs) if gs else ""))
    print("past the DP cap, d = 4..6: rank at a point against D(n-1), the trivial "
          "ceiling, so '=' certifies the stratum's generic rank (and def_D = 0); "
          "'?' is inconclusive.  dim L(q) - 1 is where the stable range starts")
    n_eq, n_all = 0, 0
    for g, (n, E) in PD_PAST_CAP.items():
        q = [s.vec(2) for _ in range(n)]
        L = lifting_space(n, E, q)
        cells = []
        for d in (4, 5, 6):
            D = (d + 1) * d // 2
            b, H = pd_pencil(s, n, E, d, q, L)
            body_guard(n, E, H)
            r = motion_rank(n, E, H)
            ok = r == D * (n - 1)
            n_eq, n_all = n_eq + ok, n_all + 1
            cells.append(f"d={d}: {r}/{D * (n - 1)}" + ("=" if ok else "?"))
        print(f"  {g:10}n={n:>2} e={len(E):>2} dim L(q) = {len(L):>2}:  "
              + "   ".join(cells))
    print(f"  certified {n_eq} of {n_all} cells past the cap")
    print(f"mismatches (asserted): {bad}")
    return bad


def subdivide(g, k):
    """Every edge of g replaced by a path of k edges."""
    n, E = g
    out = []
    for u, v in E:
        path = [u] + list(range(n, n + k - 1)) + [v]
        n += k - 1
        out += list(zip(path, path[1:]))
    return n, out


PD_PAST_CAP = {
    "ring3": diamond_ring(3), "ring4": diamond_ring(4), "ring5": diamond_ring(5),
    "theta555": relabel(theta_edges([5, 5, 5])),
    "theta666": relabel(theta_edges([6, 6, 6])),
    "K4/3": subdivide(complete(4), 3), "K33/2": subdivide(kbip(3, 3), 2),
    "petersen/2": subdivide(GRAPHS4["petersen"], 2),
}


# ---------------- Phase 42a: T1, T2 and the content range ----------------

CERT_TRIES = 1000


def elementary_divisors(M):
    """The invariant factors of an integer matrix (its Smith normal form's
    diagonal, zeros dropped).  All are 1 iff the gcd of the maximal minors is
    1, iff the rows stay independent over every field."""
    A = [[int(x) for x in r] for r in M]
    out = []
    while A and A[0] and any(any(r) for r in A):
        _, i, j = min((abs(x), i, j) for i, r in enumerate(A)
                      for j, x in enumerate(r) if x)
        while True:
            A[0], A[i] = A[i], A[0]
            for r in A:
                r[0], r[j] = r[j], r[0]
            p = A[0][0]
            for i in range(1, len(A)):
                c = A[i][0] // p
                A[i] = [x - c * y for x, y in zip(A[i], A[0])]
            for j in range(1, len(A[0])):
                c = A[0][j] // p
                for r in A:
                    r[j] -= c * r[0]
            rest = [(abs(A[i][0]), i, 0) for i in range(1, len(A)) if A[i][0]] \
                + [(abs(A[0][j]), 0, j) for j in range(1, len(A[0])) if A[0][j]]
            if rest:
                _, i, j = min(rest)
                continue
            bad = next((i for i in range(1, len(A))
                        if any(x % p for x in A[i][1:])), None)
            if bad is None:
                break
            A[0] = [x + y for x, y in zip(A[0], A[bad])]
            i, j = 0, 0
        out.append(abs(A[0][0]))
        A = [r[1:] for r in A[1:]]
    return out


def unimodular(J):
    """The rows of the integer matrix J are independent over every field."""
    return rank(J) == len(J) and set(elementary_divisors(J)) == {1}


def closed_joins(Y):
    """The joins Y_0 Y_1, ..., Y_(m-2) Y_(m-1), Y_(m-1) Y_0 of a closed polygon."""
    return [ext([Y[i], Y[(i + 1) % len(Y)]]) for i in range(len(Y))]


def cert_search(d, m):
    """A closed m-gon of affine points of K^(d+1), coordinates in {-1, 0, 1},
    with joins independent over every field, by a search seeded by (d, m)
    alone, so the same at every --seed.  Returns it and the tries."""
    R = random.Random(1000 * d + m)
    for t in range(1, CERT_TRIES + 1):
        Y = [[F(R.randint(-1, 1)) for _ in range(d)] + [F(1)] for _ in range(m)]
        if all(Y[i] != Y[(i + 1) % m] for i in range(m)) \
                and unimodular(closed_joins(Y)):
            return Y, t
    raise Degenerate(f"cert: no closed {m}-gon in P^{d} in {CERT_TRIES} tries")


def cert_ear(d, k):
    """Row 12's open ear a, x_1, ..., x_k, b: k + 2 affine points with the k + 1
    consecutive joins independent over every field and heights zero at a,
    x_1, x_k, b, so that they lie in every lifting space (the chapter's
    lem:pencil-ear-fibre(1)).  Searched as `cert_search`."""
    R = random.Random(100000 + 1000 * d + k)
    for t in range(1, CERT_TRIES + 1):
        Y = [[F(R.randint(-1, 1)) for _ in range(d)] + [F(1)] for _ in range(k + 2)]
        for i in (0, 1, k, k + 1):
            Y[i][2:d] = [F(0)] * (d - 2)
        J = [ext([Y[i], Y[i + 1]]) for i in range(k + 1)]
        if all(any(j) for j in J) and unimodular(J):
            return Y, t
    raise Degenerate(f"cert: no open ear of {k} in P^{d} in {CERT_TRIES} tries")


def euler_trail(adj, a, b):
    """An Euler trail from a to b of the graph adj (vertex -> set of
    neighbours), smallest neighbour first (Hierholzer); adj is consumed."""
    stack, out = [a], []
    while stack:
        v = stack[-1]
        if adj[v]:
            w = min(adj[v])
            adj[v].discard(w)
            adj[w].discard(v)
            stack.append(w)
        else:
            out.append(stack.pop())
    out.reverse()
    need(out[0] == a and out[-1] == b and not any(adj.values()),
         "euler: not an Euler trail")
    return out


def cert_top(d):
    """A closed D-gon, D = C(d+1,2), of affine points with joins independent
    over every field and Y_(D-1), Y_0, Y_1 at height zero (the long ear's x_k,
    a = b, x_1).  On P_0 = (0,..,0,1) and P_i = e_(i-1) + e_d, a unimodular
    basis with P_1, P_2 at height zero, the joins P_i P_j are a unimodular
    basis of Lambda^2.  Even d: an Euler circuit of K_(d+1), whose joins are
    that basis.  Odd d: an Euler circuit of K_(d+1) minus the perfect
    matching M = {12, 03, 45, 67, ...}, and for each ij in M a detour
    i -> R -> k at a step i -> k, R = P_j + P_k - P_i, with joins
    P_i P_j + P_i P_k and P_j P_k - P_i P_k.  Both circuits run 1 -> 0 -> 2.
    Returns the points, the circuit and the detours {step: (i, j)}."""
    P = [[F(0)] * d + [F(1)]] + [[F(int(c == i)) for c in range(d)] + [F(1)]
                                  for i in range(d)]
    M = [] if d % 2 == 0 else [(1, 2), (0, 3)] + [(i, i + 1) for i in range(4, d, 2)]
    adj = {v: {w for w in range(d + 1) if w != v} for v in range(d + 1)}
    for i, j in M + [(0, 1), (0, 2)]:
        adj[i].discard(j)
        adj[j].discard(i)
    walk = [0] + euler_trail(adj, 2, 1)
    used, detours = {0, len(walk) - 1}, {}
    for i, j in M:
        s = next(s for s in range(len(walk)) if s not in used and walk[s] in (i, j))
        used.add(s)
        detours[s] = (walk[s], j if walk[s] == i else i)
    Y = []
    for s, v in enumerate(walk):
        Y.append(P[v])
        if s in detours:
            i, j = detours[s]
            k = walk[(s + 1) % len(walk)]
            Y.append([x + y - z for x, y, z in zip(P[j], P[k], P[i])])
    return Y, walk, detours


def placed(Y, m):
    """Phase 40's placement of a closed walk of m >= D bodies on a closed
    D-gon Y: bodies 0..D-3 at Y_0..Y_(D-3), bodies D-2..m-2 at Y_(D-2), the
    last at Y_(D-1).  A cycle on m bodies, or an open ear a, x_1, ..., x_k, b
    with m = k + 1, b at a's point."""
    D = len(Y)
    return [Y[min(i, D - 2)] for i in range(m - 1)] + [Y[D - 1]]


CERT_HEXAGON = [[F(x) for x in y] for y in ((1, 0, 0, 1), (0, -1, 0, 1), (0, 0, 1, 1),
                                            (-1, 0, 1, 1), (0, 0, 0, 1), (-1, -1, 0, 1))]


def content_graphs():
    """The content-range graphs of Phase42-design.md section 2.5, with the
    singleton bound on def_3 that the design states for each family."""
    th = lambda *ls: relabel(theta_edges(list(ls)))  # noqa: E731
    G = {f"th22-{k}": (th(2, 2, k), k - 2) for k in range(4, 11)}
    G.update({f"th222-{k}": (th(2, 2, 2, k), k - 3) for k in range(5, 11)})
    G["Dwit"] = ((7, [(i, (i + 1) % 6) for i in range(6)] + [(0, 3), (6, 1), (6, 4)]),
                 0)
    G.update({f"ring{m}": (diamond_ring(m), m - 3) for m in (6, 7)})
    return G


def mode_content(s):
    bad = 0
    print("T1 (Phase 42a, row 5), one seeded picture q per graph of GRAPHS4.  "
          "flat: every height 0, against D(n-1) + 3 - dim L(q) (asserted, every "
          "graph and d; the chapter's flat rank).  R1: the last of the d-2 "
          "heights 0, the rest fresh in L(q), so the P^(d-1) pencil in a "
          "hyperplane, against D(n-1) - def_(D_(d-1)) (asserted at d = 4: Phase "
          "40 and Result 15; reported at d = 5, 6, '<' below; '.' at "
          "multigraphs).  Also asserted: def_3 <= d-3 gives def_(D_(d-1)) = "
          "def_D (section 2.5, by Result 16)")
    print(f"{'graph':10}{'n':>3}{'e':>3}{'d3':>4}{'d6':>4}{'d10':>4}{'d15':>4}"
          f"{'l':>4} " + "".join(f"{'d=' + str(d) + ' flat':>12}{'R1':>9}"
                                 for d in (4, 5, 6)))
    reach = {d: [0, 0, 0] for d in (4, 5, 6)}  # simple graphs; flat, R1 at target
    for g, (n, E) in GRAPHS4.items():
        df = {D: deficiency(n, E, D) for D in (3, 6, 10, 15, 21)}
        q = [s.vec(2) for _ in range(n)]
        L = lifting_space(n, E, q)
        ell = len(L)
        cells = []
        for d in (4, 5, 6):
            D, Dm = (d + 1) * d // 2, d * (d - 1) // 2
            t = D * (n - 1) - df[D]
            b = [list(q[v]) + [F(0)] * (d - 2) + [F(1)] for v in range(n)]
            H = [ext([b[u], b[v]]) for u, v in E]
            body_guard(n, E, H)
            r, tf = motion_rank(n, E, H), D * (n - 1) + 3 - ell
            bad += r != tf
            cells.append(f"{r}/{tf}" + ("" if r == tf else "*"))
            if df[3] <= d - 3:
                bad += df[Dm] != df[D]
            if not simple(E):
                cells.append(".")
                continue
            hs = [s.comb(L) for _ in range(d - 3)]
            b = [list(q[v]) + [h[v] for h in hs] + [F(0), F(1)] for v in range(n)]
            H = [ext([b[u], b[v]]) for u, v in E]
            body_guard(n, E, H)
            r1, t1 = motion_rank(n, E, H), D * (n - 1) - df[Dm]
            mark = ""
            if r1 != t1:
                mark = "*" if d == 4 else "<"
                bad += d == 4
            cells.append(f"{r1}/{t1}{mark}")
            reach[d][0] += 1
            reach[d][1] += r == t
            reach[d][2] += r1 == t
        print(f"{g:10}{n:>3}{len(E):>3}{df[3]:>4}{df[6]:>4}{df[10]:>4}{df[15]:>4}"
              f"{ell:>4} " + "".join(f"{c:>12}" if i % 2 == 0 else f"{c:>9}"
                                     for i, c in enumerate(cells)))
    for d, (k, f, r1) in reach.items():
        print(f"  d={d}: at the P^d target D(n-1) - def_D, of {k} simple graphs: "
              f"flat {f} (def_3 = def_D), R1 {r1}")

    print("T2 (CERT, rows 10-12): affine points of K^(d+1) whose joins are "
          "independent over every field (invariant factors all 1), asserted.  "
          "By a search seeded by (d, m) or (d, k) alone, with its tries: closed "
          "m-gons, 3 <= m < D (the cycle), and open ears a, x_1, .., x_k, b, "
          "2 <= k <= D-2, at height zero at a, x_1, x_k, b (row 12).  m = D by "
          "`cert_top`, also the long ear's certificate (Y_(D-1), Y_0, Y_1 at "
          "height zero); its placements on cycles of m = D, D+1, D+3 bodies and "
          "ears of k = D-1, D, D+2 interior bodies span Lambda^2.  d = 3 is the "
          "control, with the chapter's hexagon (lem:pencil-chain-span-"
          "certificates) asserted too, and the negative control "
          "[[1, 1], [1, -1]] (invariant factors 1, 2) rejected.")
    for m in range(3, 7):
        bad += not unimodular(closed_joins(CERT_HEXAGON[:m]))
    neg = [[F(1), F(1)], [F(1), F(-1)]]
    bad += elementary_divisors(neg) != [1, 2] or unimodular(neg)
    for d in (3, 4, 5, 6):
        D = (d + 1) * d // 2
        tries, ears = [], []
        for out, find, ms in ((tries, cert_search, range(3, D)),
                              (ears, cert_ear, range(2, D - 1))):
            for m in ms:
                try:
                    out.append(find(d, m)[1])
                except Degenerate:
                    out.append("-")
                    bad += 1
        Y, walk, detours = cert_top(d)
        ok = len(Y) == D and unimodular(closed_joins(Y)) \
            and not any(Y[i][2:d] != [F(0)] * (d - 2) for i in (D - 1, 0, 1))
        for m in (D, D + 1, D + 3):
            ok = ok and rank(closed_joins(placed(Y, m))) == D
        bad += not ok
        print(f"  d={d} D={D:>2}: m = 3..{D - 1}, tries "
              + " ".join(map(str, tries)) + f"; k = 2..{D - 2}, tries "
              + " ".join(map(str, ears)) + f"; m = {D}: circuit "
              + "-".join(map(str, walk))
              + (", detours " + " ".join(f"{i}{j}@{walk[t]}{walk[(t + 1) % len(walk)]}"
                                         for t, (i, j) in detours.items())
                 if detours else "")
              + ("" if ok else "  *"))

    print("the content range (section 2.5): the pencil of P^d at one seeded "
          "point per graph, fresh heights per d, against t = D(n-1) - def_D "
          "under the DP cap (n <= 12; '<' below t, reported) and D(n-1) past it "
          "('=' certifies, '?' inconclusive).  'c' marks a content cell, "
          "d <= dim L(q) - 1 = 2 + def_3.  th22-k: theta(2,2,k), row 14's one-"
          "body ear whose ends share a neighbour; th222-k: theta(2,2,2,k), route "
          "B's two hubs with three common neighbours; Dwit: D's candidate "
          "witness (section 2.3), C6 + 03 + y on 1, 4; ringm: diamond rings, a "
          "condition at every body.  Asserted under the cap: def_3 at least the "
          "design's singleton bound, dim L(q) = 3 + def_3, rank <= t")
    print(f"{'graph':10}{'n':>3}{'e':>3}{'d3':>4}{'l':>4} "
          + "".join(f"{'d=' + str(d):>13}" for d in (4, 5, 6)))
    tally, short = [0, 0], []
    for g, ((n, E), lo) in content_graphs().items():
        capped = n <= 12
        df = {}
        if capped:
            df = {D: deficiency(n, E, D) for D in (3, 10, 15, 21)}
            bad += df[3] < lo
        q = [s.vec(2) for _ in range(n)]
        L = lifting_space(n, E, q)
        ell = len(L)
        if capped:
            bad += ell != 3 + df[3]
        cells = []
        for d in (4, 5, 6):
            D = (d + 1) * d // 2
            _, H = pd_pencil(s, n, E, d, q, L)
            body_guard(n, E, H)
            r = motion_rank(n, E, H)
            content = d <= ell - 1
            if capped:
                t = D * (n - 1) - df[D]
                assert r <= t, (g, d)
                ok, mark = r == t, ("" if r == t else "<")
            else:
                t = D * (n - 1)
                ok, mark = r == t, ("=" if r == t else "?")
            if content:
                tally[0] += 1
                tally[1] += ok
                short += [] if ok else [f"{g}@{d}"]
            cells.append(f"{r}/{t}{mark}{'c' if content else ''}")
        print(f"{g:10}{n:>3}{len(E):>3}{df.get(3, '.'):>4}{ell:>4} "
              + "".join(f"{c:>13}" for c in cells))
    print(f"  content cells at their target: {tally[1]} of {tally[0]}"
          + ("" if not short else "; not: " + ", ".join(short)))
    print(f"mismatches (asserted): {bad}")
    return bad



# ---------------- Phase 42a: T4's first half, the one-body ear ----------------

def one_ear_graphs():
    """T4's graphs (Phase42-design.md section 2.4).  Each is a theta graph
    with hubs a = 0, b = 1, not adjacent, and x = 2 the interior body of its
    first 2-path: a one-body ear a - x - b on V1 = V - x.  th22-k,
    theta(2,2,k), k = 4..10: a and b share one neighbour in V1 (row 14's
    configuration; Result 22's family).  th222-k, theta(2,2,2,k), k = 5..10:
    they share two (route B's hubs).  th23-k, theta(2,3,k), k = 4..9: none,
    the control."""
    th = lambda *ls: relabel(theta_edges(list(ls)))  # noqa: E731
    G = {f"th22-{k}": th(2, 2, k) for k in range(4, 11)}
    G.update({f"th222-{k}": th(2, 2, 2, k) for k in range(5, 11)})
    G.update({f"th23-{k}": th(2, 3, k) for k in range(4, 10)})
    return G


def plane_of(pts, edges, v):
    """A basis of Pi_v = span b_N[v]."""
    P = [pts[w] for w in sorted({v} | {w for e in edges if v in e for w in e})]
    return [P[i] for i in _pivots(P)]


def identify(n, edges, a, b):
    """G with b identified into a, relabelled; an edge ab becomes a loop,
    which def_D ignores.  So def_D of it is the maximum over the partitions
    with a and b in one part, the merged deficiency def:deficiency-merged."""
    ix = {v: i for i, v in enumerate(w for w in range(n) if w != b)}
    ix[b] = ix[a]
    return n - 1, [(ix[u], ix[v]) for u, v in edges]


def mode_oneear(s):
    print("T4's first half (Phase 42a; Phase42-design.md sections 2.3-2.4, "
          "ONE-EAR): a one-body ear a - x - b, G1 = G[V1] = G - x.  At d = 4, "
          "5, one seeded picture q per graph, fresh heights per d.  G1@G: a "
          "pencil configuration of G (heights in L_G(q)) restricted to V1, "
          "the locus the d = 3 step needs G1 to attain on "
          "(lem:pencil-one-ear-incidence); [G1]: G1's own configuration at "
          "q|V1 (heights in L_G1), the control.  Both against t1 = D(n1-1) - "
          "def_D(G1) under the DP cap (n1 <= 12; '<' below, reported) or "
          "D(n1-1) past it ('=' certifies, '?' inconclusive).  G: G's rank at "
          "its configuration, as in --content; 'c' a content cell of G, d <= "
          "dim L_G(q) - 1.  meet: dim(Pi_a cap Pi_b), Pi_v = span b_N[v] in "
          "G1, at G's configuration | at G1's.  sh: neighbours a, b share in "
          "V1.  M: the d = 3 step's hypothesis def_3(G1; a, b) + 2 <= "
          "def_3(G1) (sec:main-component-orbit).  le: def_D(G1) <= def_D(G), "
          "its other hypothesis at D ('.' past the cap).  Asserted: x has "
          "neighbours a, b only, a and b not adjacent, dim Pi_a = dim Pi_b = "
          "3, b_x in Pi_a cap Pi_b at G's configuration, every rank at most "
          "its count, and under the cap dim L(q) = 3 + def_3 for G and G1.")
    print(f"{'graph':9}{'n':>3}{'e':>3}{'d3':>4}{'sh':>3}{'M':>2} "
          + "".join(f"{'d=' + str(d) + ' G':>12}{'G1@G [G1]':>16}{'meet':>6}{'le':>3}"
                    for d in (4, 5)))
    bad, tally, forced = 0, {}, []
    for g, (n, E) in one_ear_graphs().items():
        a, b, x = 0, 1, 2
        nb = {v: {w for e in E if v in e for w in e} - {v} for v in range(n)}
        bad += nb[x] != {a, b} or b in nb[a]
        keep = [v for v in range(n) if v != x]
        ix = {v: i for i, v in enumerate(keep)}
        n1, E1 = n - 1, [(ix[u], ix[v]) for u, v in E if x not in (u, v)]
        a1, b1 = ix[a], ix[b]
        sh = len(nb[a] & nb[b] - {x})
        df = {D: deficiency(n, E, D) for D in (3, 10, 15)} if n <= 12 else {}
        df1 = {D: deficiency(n1, E1, D) for D in (3, 10, 15)} if n1 <= 12 else {}
        mh = "."
        if df1:
            mh = "y" if deficiency(*identify(n1, E1, a1, b1), 3) + 2 <= df1[3] else "n"
        q = [s.vec(2) for _ in range(n)]
        L = lifting_space(n, E, q)
        q1 = [q[v] for v in keep]
        L1 = lifting_space(n1, E1, q1)
        if df:
            bad += len(L) != 3 + df[3]
        if df1:
            bad += len(L1) != 3 + df1[3]
        cells = []
        for d in (4, 5):
            D = (d + 1) * d // 2
            bG, H = pd_pencil(s, n, E, d, q, L)
            body_guard(n, E, H)
            r = motion_rank(n, E, H)
            t = D * (n - 1) - df[D] if df else D * (n - 1)
            assert r <= t, (g, d)
            mark = ("" if r == t else "<") if df else ("=" if r == t else "?")
            cells.append(f"{r}/{t}{mark}{'c' if d <= len(L) - 1 else ''}")
            p1 = [bG[v] for v in keep]
            pg, Hg = pd_pencil(s, n1, E1, d, q1, L1)
            body_guard(n1, E1, Hg)
            t1 = D * (n1 - 1) - df1[D] if df1 else D * (n1 - 1)
            r1, meet = [], []
            for pts in (p1, pg):
                H1 = [ext([pts[u], pts[v]]) for u, v in E1]
                body_guard(n1, E1, H1)
                r1.append(motion_rank(n1, E1, H1))
                assert r1[-1] <= t1, (g, d)
                A, B = plane_of(pts, E1, a1), plane_of(pts, E1, b1)
                bad += len(A) != 3 or len(B) != 3
                if pts is p1:
                    bad += rank(A + [bG[x]]) != 3 or rank(B + [bG[x]]) != 3
                meet.append(len(span_cap(A, B)))
            # past the cap a rank of D(n1-1) certifies t1 for both cells
            sure = bool(df1) or max(r1) == t1
            mk = [("" if rr == t1 else "<" if sure else "?") + ("" if df1 or rr != t1 else "=")
                  for rr in r1]
            cells.append(f"{r1[0]}/{t1}{mk[0]} [{r1[1]}{mk[1]}]")
            if sh == 2:
                # the mechanism: b_x, b_y, b_w independent make the hubs'
                # planes coincide in G, so a, y, b, w lie in one 3-space and
                # the 4-cycle's hinges are dependent in Lambda^2; where the
                # k-path's hinges span Lambda^2 that dependency extends to a
                # motion assignment of G1, so G1 ranks below D(n1-1) there
                y, w = sorted(nb[a] & nb[b] - {x})
                bad += rank([bG[v] for v in (x, y, w)]) != 3
                bad += rank([bG[v] for v in (a, y, b, w)]) != 3
                path = [ext([p1[u], p1[v]]) for u, v in E1
                        if not {u, v} & {ix[y], ix[w]}]
                if rank(path) == D:
                    forced.append(f"{g}@{d}")
                    bad += r1[0] > D * (n1 - 1) - 1
            cells.append(f"{meet[0]}|{meet[1]}")
            cells.append("." if not (df and df1) else "y" if df1[D] <= df[D] else "n")
            fam = tally.setdefault((g.split("-")[0], d), [0, 0, 0, set(), []])
            fam[0] += 1
            fam[1] += r1[0] == t1
            fam[2] += r1[1] == t1
            fam[3].add(f"{meet[0]}|{meet[1]}")
            fam[4] += [] if r1[0] == t1 else [g]
        print(f"{g:9}{n:>3}{len(E):>3}{df.get(3, '.'):>4}{sh:>3}{mh:>2} "
              + "".join(f"{c:>12}" if i % 4 == 0 else f"{c:>16}" if i % 4 == 1
                        else f"{c:>6}" if i % 4 == 2 else f"{c:>3}"
                        for i, c in enumerate(cells)))
    for (fam, d), (k, at, atg, meets, short) in tally.items():
        print(f"  {fam}, d={d}: G1 at t1 at G's configuration on {at} of {k} "
              f"(its own: {atg} of {k}); meet " + ", ".join(sorted(meets))
              + ("" if not short else "; below: " + ", ".join(short)))
    print("  th222-k, two shared neighbours y, w: at G's configuration b_x, b_y, "
          "b_w and b_a, b_y, b_b, b_w each span 3 dimensions (asserted, every "
          "cell), so the 4-cycle a y b w has dependent hinges; where the k-path's "
          "hinges span Lambda^2 this extends to a motion assignment of G1, which "
          "then ranks at most D(n1-1) - 1 (asserted): "
          + (", ".join(forced) if forced else "no cell"))
    print(f"mismatches (asserted): {bad}")
    return bad


# ---------------- Phase 42a: T3, the short ears (SHORT) ----------------

SHORT_DIMS = (3, 4, 5)
SHORT_PER = 2       # danger cells drawn per (family, d, k)
SHORT_TRIES = 400   # box draws per (family, d, k)
SHORT_NMAX = 40     # bodies of G
SHORT_REDRAWS = 3   # fresh points per cell after a failed degeneracy guard


def core_subdivision(core_n, core_edges, lengths):
    """The core multigraph with edge i replaced by a path of lengths[i] edges:
    n, the edges, and each core edge's path (ends included)."""
    n, E, paths = core_n, [], []
    for (u, v), m in zip(core_edges, lengths):
        p = [u] + list(range(n, n + m - 1)) + [v]
        n += m - 1
        E += list(zip(p, p[1:]))
        paths.append(p)
    return n, E, paths


def partition_value(n, edges, parts, D):
    """D(|P|-1) - (D-1) e(P) for the given parts, singletons elsewhere."""
    lab = list(range(n))
    for i, part in enumerate(parts):
        for v in part:
            lab[v] = n + i
    e = sum(1 for u, v in edges if lab[u] != lab[v])
    return D * (len(set(lab)) - 1) - (D - 1) * e


def path_partitions_def(n, edges, paths, D, blocks=()):
    """The best of the trivial partition and the partitions whose parts are
    the components of a union of whole paths and every block, singletons
    elsewhere: a lower bound on def_D.  In a subdivision an optimal partition
    has this form (a part ending inside a path gains by shedding the tail, a
    part with no cycle by splitting into singletons); `def_certified` checks
    it at every use."""
    best = 0
    for S in range(1 << len(paths)):
        comps = []
        for p in [paths[i] for i in range(len(paths)) if (S >> i) & 1] + list(blocks):
            c = set(p)
            for o in [o for o in comps if o & c]:
                comps.remove(o)
                c |= o
            comps.append(c)
        best = max(best, partition_value(n, edges, comps, D))
    return best


def def_certified(s, n, edges, paths, D, blocks=()):
    """def_D past the DP cap: `path_partitions_def`, a lower bound, matched by
    the rank at a generic-hinge point, which is at most D(n-1) - def_D
    (Tay-Whiteley).  A match certifies; a gap raises Degenerate."""
    t = D * (n - 1) - path_partitions_def(n, edges, paths, D, blocks)
    r = motion_rank(n, edges, [s.vec(D) for _ in edges])
    assert r <= t, ("partition bound", r, t)
    need(r == t, f"def_{D}: generic rank {r} below the partition count {t}")
    return D * (n - 1) - t


def tree_path(n, edges, a, b):
    """A path a -> b as a signed edge dict with boundary b - a, the signs as
    in `fund_cycles`."""
    parent, order = {a: None}, [a]
    while order:
        x = order.pop()
        for j, (u, v) in enumerate(edges):
            for p, q, sg in ((u, v, 1), (v, u, -1)):
                if p == x and q not in parent:
                    parent[q] = (x, j, sg)
                    order.append(q)
    need(b in parent, "tree_path: b not reached")
    out = {}
    while parent[b] is not None:
        p, j, sg = parent[b]
        out[j] = out.get(j, 0) + sg
        b = p
    return out


def rel_screws(n, edges, H, a, b):
    """rho: a basis of the relative screws S_b - S_a over the motions, read as
    motion assignments (Result 1): lambda in K^E with sum +-lambda_e H_e = 0 on
    every cycle, and S_v - S_u = lambda_e H_e at an edge (u, v)."""
    D = len(H[0])
    M = [[F(z.get(j, 0)) * H[j][i] for j in range(len(edges))]
         for z in fund_cycles(n, edges) for i in range(D)]
    mot = nullspace(M) if M else [[F(int(i == j)) for i in range(len(edges))]
                                  for j in range(len(edges))]
    path = tree_path(n, edges, a, b)
    rho = [[sum((sg * lam[j] * H[j][i] for j, sg in path.items()), F(0))
            for i in range(D)] for lam in mot]
    return [rho[i] for i in _pivots(rho)]


def point_over(P, uv):
    """The affine point over the picture point uv of the 3-space span(P), as
    an ear datum puts x_1 on the plane of a (def:pencil-ear-data)."""
    d = len(P[0]) - 1
    A = [[P[i][c] for i in range(3)] for c in (0, 1, d)]
    det = det_exact(A)
    need(det != 0, "point_over: the plane is vertical")
    rhs = [uv[0], uv[1], F(1)]
    c = [det_exact([row[:i] + [rhs[r]] + row[i + 1:] for r, row in enumerate(A)]) / det
         for i in range(3)]
    return [sum((c[i] * P[i][j] for i in range(3)), F(0)) for j in range(d + 1)]


def star(y):
    """The joins y v e_i, which span star(y), the lines through y."""
    return [ext([y, [F(int(i == j)) for j in range(len(y))]]) for i in range(len(y))]


def affine_pt(s, d):
    return [s.num() for _ in range(d)] + [F(1)]


class CoreEar:
    """A subdivided core multigraph whose last core edge is the ear: V1 is
    labelled first, the ear's interior after it in order from a."""

    def __init__(self, core, lengths):
        (self.cn, self.ce), self.ls, self.k = core, list(lengths), lengths[-1] - 1
        self.key = tuple(lengths)

    def graph(self, k):
        n, E, paths = core_subdivision(self.cn, self.ce, self.ls[:-1] + [k + 1])
        return n, E, paths, (), paths[-1][0], paths[-1][-1]

    def base(self):
        return core_subdivision(self.cn, self.ce[:-1], self.ls[:-1]) + ((),)

    def label(self):
        return ",".join(map(str, self.ls[:-1]))


class NecklaceEar:
    """r diamonds K_4 - e (bodies t, u, v, w; edges tu tv uv uw vw) in a ring,
    w of each joined to t of the next by a path of ells[i] edges, so a pencil
    condition binds at every diamond body.  The ear runs from the body of
    role ra in diamond 0 to the body of role rb in diamond B.  Paths: the two
    ring arcs between diamonds 0 and B, and the ear; blocks: the diamonds."""

    def __init__(self, ells, B, ra, rb, k):
        self.k, self.key = k, (tuple(ells), B, ra, rb, k)
        E, dia, n = [], [], 0
        for _ in ells:
            E += [(n, n + 1), (n, n + 2), (n + 1, n + 2), (n + 1, n + 3), (n + 2, n + 3)]
            dia.append([n, n + 1, n + 2, n + 3])
            n += 4
        segs = []
        for i, m in enumerate(ells):
            p = [dia[i][3]] + list(range(n, n + m - 1)) + [dia[(i + 1) % len(ells)][0]]
            n += m - 1
            E += list(zip(p, p[1:]))
            segs.append(p)
        self.n1, self.E1, self.blocks = n, E, [set(x) for x in dia]
        self.a, self.b = dia[0]["tuvw".index(ra)], dia[B]["tuvw".index(rb)]
        ends = set(dia[0]) | set(dia[B])
        self.arcs = [sorted(ends.union(*(set(segs[i]) | set(dia[i]) for i in idx)))
                     for idx in (range(B), range(B, len(ells)))]

    def graph(self, k):
        ear = [self.a] + list(range(self.n1, self.n1 + k)) + [self.b]
        return (self.n1 + k, self.E1 + list(zip(ear, ear[1:])), self.arcs + [ear],
                self.blocks, self.a, self.b)

    def base(self):
        return self.n1, self.E1, self.arcs, self.blocks

    def label(self):
        ells, B, ra, rb, _ = self.key
        return ",".join(map(str, ells)) + f"/{B}{ra}{rb}"


SHORT_FAMS = {
    # name: (core or None, the box's top length, G[V1] and the ends a, b)
    "th3": ((2, [(0, 1)] * 3), 4, "a cycle; a, b at arc lengths l1, l2"),
    "th4": ((2, [(0, 1)] * 4), 4, "a theta; a, b its hubs"),
    "k4": ((4, [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]), 0,
           "a theta (K_4 - e subdivided); a, b inside two of its paths"),
    "same": ((4, [(0, 1), (0, 1), (0, 2), (2, 3), (3, 1), (2, 3)]), 0,
             "a theta; a, b inside one of its paths"),
    "hub": ((3, [(0, 1), (0, 1), (0, 2), (2, 1), (0, 2)]), 0,
            "a theta; a a hub, b inside a path"),
    "neck": (None, 0, "a necklace of 3-6 diamonds joined by paths of 1-7 edges; "
             "a, b diamond bodies"),
}


def short_draw(R, fam, D, k):
    """One spec from fam's box: core lengths in [1, D + top] (the theta
    families' sorted), or a necklace; None if G is not simple."""
    core, top, _ = SHORT_FAMS[fam]
    if core is None:
        r = R.randint(3, 6)
        return NecklaceEar([R.randint(1, 7) for _ in range(r)], R.randint(1, r - 1),
                           R.choice("tuvw"), R.choice("tuvw"), k)
    ls = [R.randint(1, D + top) for _ in core[1][1:]]
    if top:
        ls.sort()
    ls.append(k + 1)
    unit = [frozenset(e) for e, m in zip(core[1], ls) if m == 1]
    return CoreEar(core, ls) if len(unit) == len(set(unit)) else None


def short_danger(fam, d, k):
    """Up to SHORT_PER danger cells for (fam, d, k), by a search of fam's box
    seeded by (fam, d, k) alone, so the same at every --seed.  A danger cell:
    n <= SHORT_NMAX, def_3(G) >= d-2 (the content range), def_D(G[V1]) >
    def_D(G) (SHORT's hypothesis), def_D(G'') = def_D(G) (no slack: (*) needs
    dim W + 1), and 2d-1 <= k + def_D(G[V1]) - def_D(G'') <= D-1 (the count
    of dim W, at which W can hold both stars and be proper).  The deficiencies
    here are `path_partitions_def`'s; `short_cell` certifies them."""
    D = (d + 1) * d // 2
    R = random.Random(10000 * list(SHORT_FAMS).index(fam) + 100 * d + k)
    found, seen = [], set()
    for _ in range(SHORT_TRIES):
        spec = short_draw(R, fam, D, k)
        if spec is None or spec.key in seen:
            continue
        seen.add(spec.key)
        n, E, paths, blocks, _, _ = spec.graph(k)
        if n > SHORT_NMAX or path_partitions_def(n, E, paths, 3, blocks) < d - 2:
            continue
        dG = path_partitions_def(n, E, paths, D, blocks)
        n1, E1, paths1, blocks1 = spec.base()
        f = path_partitions_def(n1, E1, paths1, D, blocks1)
        n2, E2, paths2, blocks2, _, _ = spec.graph(k - 1)
        d2 = path_partitions_def(n2, E2, paths2, D, blocks2)
        if f > dG == d2 and 2 * d - 1 <= k + f - d2 <= D - 1:
            found.append(spec)
            if len(found) == SHORT_PER:
                break
    return found


def short_cell(s, spec, d):
    """The d = 3 step's two stages (thm:pencil-x0-open-ear-three, -four) in P^d,
    at one seeded point.  Stage 1: a picture and heights in L_G''(q), whose
    restriction to V1 is the base data; Pi_a, Pi_b the planes of a and b in
    G''.  Stage 2: a general ear datum of G'' (y_1 on Pi_a over a fresh
    picture point, y_k on Pi_b, the middle bodies free affine points), W =
    rho + span(its ear joins).  Then x_2 put back at a general affine point,
    and a fresh general ear datum of G over the same base."""
    D, k = (d + 1) * d // 2, spec.k
    n, E, paths, blocks, a, b = spec.graph(k)
    n2, E2, paths2, blocks2, _, _ = spec.graph(k - 1)
    n1, E1, paths1, blocks1 = spec.base()
    dG, d2 = def_certified(s, n, E, paths, D, blocks), def_certified(s, n2, E2, paths2, D, blocks2)
    f, d3 = def_certified(s, n1, E1, paths1, D, blocks1), def_certified(s, n, E, paths, 3, blocks)
    q2 = [s.vec(2) for _ in range(n2)]
    b2, H2 = pd_pencil(s, n2, E2, d, q2, lifting_space(n2, E2, q2))
    body_guard(n2, E2, H2)
    base = b2[:n1]
    H1 = [ext([base[u], base[v]]) for u, v in E1]
    r1 = motion_rank(n1, E1, H1)
    PA, PB = plane_of(b2, E2, a), plane_of(b2, E2, b)
    need(len(PA) == 3 and len(PB) == 3, "the planes of a, b in G''")
    rho = rel_screws(n1, E1, H1, a, b)
    y = {1: point_over(PA, s.vec(2)), k: point_over(PB, s.vec(2))}
    for i in range(3, k):
        y[i] = affine_pt(s, d)
    ear2 = [base[a], y[1]] + [y[i] for i in range(3, k + 1)] + [base[b]]
    J2 = [ext([p, p2]) for p, p2 in zip(ear2, ear2[1:])]
    W = rho + J2
    dW = rank(W)
    pts2 = base + ear2[1:-1]
    r2 = motion_rank(n2, E2, [ext([pts2[u], pts2[v]]) for u, v in E2])
    holds = lambda U, V: rank(U + V) == rank(U)  # noqa: E731
    in1, in3 = holds(W, star(y[1])), holds(W, star(y[3]))
    # R_i: rho and the joins of G'''s ear away from y_i
    caps = []
    for yi, R in ((y[1], rho + J2[2:]), (y[3], rho + J2[:1] + J2[3:])):
        caps.append((rank(R) + d - rank(R + star(yi)), max(0, rank(R) + d - D)))
    stars = star(y[1]) + star(y[3])
    ctrl = holds(stars, star(y[1])) and holds(stars, star(y[3])) and rank(stars) == 2 * d - 1
    # images in Lambda^2 / (star(y_1) + star(y_3)), of dimension C(d-1, 2): of
    # rho, of the joins y_4 y_5, .., y_k p_b (the others lie in the stars),
    # and of W; X3 holds at the cell iff W's image is everything or W misses
    # a star
    img = [rank(stars + U) - rank(stars) for U in (rho, J2[3:], W)]
    ear = [base[a], y[1], affine_pt(s, d)] + ear2[2:]
    dI = rank(rho + [ext([p, p2]) for p, p2 in zip(ear, ear[1:])])
    pts = base + ear[1:-1]
    rG = motion_rank(n, E, [ext([pts[u], pts[v]]) for u, v in E])
    gen = ([base[a], point_over(PA, s.vec(2))] + [affine_pt(s, d) for _ in range(k - 2)]
           + [point_over(PB, s.vec(2)), base[b]])
    dGen = rank(rho + [ext([p, p2]) for p, p2 in zip(gen, gen[1:])])
    return dict(D=D, k=k, n=n, d3=d3, dG=dG, d2=d2, f=f, r1=r1, t1=D * (n1 - 1) - f,
                r2=r2, t2=D * (n2 - 1) - d2, rG=rG, tG=D * (n - 1) - dG, dW=dW,
                rho=len(rho), in1=in1, in3=in3, caps=caps, ctrl=ctrl, img=img, dI=dI, dGen=dGen,
                need=k + 1 + f - dG)


def mode_short(s):
    print("T3 (Phase 42a; Phase42-design.md sections 2.3-2.4, SHORT): an open "
          "ear a - x_1 - .. - x_k - b on V1, 3 <= k <= D-2, and G'' = G with x_2 "
          "suppressed (sec:main-component-short).  Danger cells only (`short_"
          "danger`: def_D(G[V1]) > def_D(G) = def_D(G''), 2d-1 <= dim W <= D-1, "
          "def_3(G) >= d-2), drawn from each family's box by a search seeded by "
          "(family, d, k) alone.  Per cell: def_3, f = def_D(G[V1]), def_D(G), "
          "def_D(G''); sh1, sh2: G[V1] and G'' below target (0 = at it); W = dim "
          "W; rho = dim rho; st: W contains star(y_1), star(y_3); cap: dim(R_i "
          "cap star(y_i)) / the general-position value max(0, dim R_i + d - D), "
          "R_i = rho + the joins of G'''s ear away from y_i; img: the dimensions "
          "of the images of rho, of the joins y_4 y_5 .. y_k p_b and of W in "
          "Lambda^2 / (star(y_1) + star(y_3)), / its dimension C(d-1, 2) (X3 "
          "holds where W's image is everything); need = k+1+f-def_D(G), (*)'s "
          "bound; step: dim(rho + Lambda) with x_2 at a general affine point; "
          "gen: at a fresh general ear datum of G.  'X' marks W containing both "
          "stars and W != Lambda^2 (X3 fails), '*' the step's (*) failing, '~' "
          "a redraw after a failed degeneracy guard.  Asserted at every cell: "
          "every deficiency certified "
          "(`def_certified`), the ear rank formula (lem:block-rank-ear) at G'' and "
          "at G, every rank at most its count, dim W = k + f - def_D(G'') where "
          "G[V1] and G'' attain, and the containment test's control (star(y_1) + "
          "star(y_3) contains both, of dimension 2d-1).  At d = 3, where the "
          "chapter proves the step (thm:pencil-x0-open-ear-three, -four): G[V1] "
          "and G'' at target, no 'X', no '*'.")
    print("families (G[V1]; a, b): " + "; ".join(f"{g}: {v[2]}" for g, v in SHORT_FAMS.items()))
    print(f"{'fam':5}{'lengths':18}{'d':>2}{'n':>4}{'k':>3}{'d3':>4}{'f':>4}{'dG':>4}"
          f"{'dG2':>4}{'sh1':>4}{'sh2':>4}{'W':>4}{'rho':>4}{'st':>4}{'cap':>10}"
          f"{'img':>10}{'need':>5}{'step':>5}{'gen':>5}")
    cols = ("cells", "G[V1] at target", "G'' at target", "X3 fails",
            "W contains a star", "caps at the general-position value",
            "the step's (*)", "(*) at a general ear datum", "the step gains over W",
            "the joins y_4 .. p_b fill the quotient", "rho fills it")
    bad, tally = 0, {}
    for d in SHORT_DIMS:
        D, Q = (d + 1) * d // 2, (d - 1) * (d - 2) // 2
        for fam in SHORT_FAMS:
            for k in range(3, D - 1):
                for spec in short_danger(fam, d, k):
                    # a failed guard redraws the point, up to SHORT_REDRAWS
                    # times ('~' per redraw); a deficiency not certified fails
                    # at every draw
                    for draws in range(SHORT_REDRAWS + 1):
                        try:
                            c = short_cell(s, spec, d)
                            break
                        except Degenerate as e:
                            err = e
                    else:
                        bad += 1
                        print(f"{fam:5}{spec.label():18}{d:>2}  degenerate: {err}")
                        continue
                    sh1, sh2 = c["t1"] - c["r1"], c["t2"] - c["r2"]
                    bad += min(sh1, sh2, c["tG"] - c["rG"]) < 0
                    bad += c["r2"] != c["r1"] + (D - 1) * (k - 1) + c["dW"] - 1
                    bad += c["rG"] != c["r1"] + (D - 1) * k + c["dI"] - 1
                    bad += sh1 == sh2 == 0 and c["dW"] != k + c["f"] - c["d2"]
                    bad += not c["ctrl"]
                    x3 = c["in1"] and c["in3"] and c["dW"] < D
                    star_fail = c["dI"] < c["need"]
                    if d == 3:
                        bad += sh1 != 0 or sh2 != 0 or x3 or star_fail
                    t = tally.setdefault((fam, d), [0] * len(cols))
                    for i, v in enumerate((1, sh1 == 0, sh2 == 0, x3, c["in1"] or c["in3"],
                                           all(x == e for x, e in c["caps"]),
                                           not star_fail, c["dGen"] >= c["need"],
                                           c["dI"] > c["dW"], c["img"][1] == Q,
                                           c["img"][0] == Q)):
                        t[i] += v
                    cap = "|".join(f"{x}" for x, _ in c["caps"]) + "/" + \
                        "|".join(f"{e}" for _, e in c["caps"])
                    img = "|".join(map(str, c["img"])) + f"/{Q}"
                    print(f"{fam:5}{spec.label():18}{d:>2}{c['n']:>4}{k:>3}{c['d3']:>4}"
                          f"{c['f']:>4}{c['dG']:>4}{c['d2']:>4}{sh1:>4}{sh2:>4}{c['dW']:>4}"
                          f"{c['rho']:>4}{int(c['in1']):>3}{int(c['in3'])}{cap:>10}{img:>10}"
                          f"{c['need']:>5}{c['dI']:>5}{c['dGen']:>5} "
                          + ("X" if x3 else "") + ("*" if star_fail else "") + "~" * draws)
    print("per family and d, the columns: " + "; ".join(cols))
    for d in SHORT_DIMS:
        row = [0] * len(cols)
        for (fam, dd), t in tally.items():
            if dd == d:
                print(f"  d={d} {fam:5}" + " ".join(f"{v:>4}" for v in t))
                row = [x + v for x, v in zip(row, t)]
        print(f"  d={d} all  " + " ".join(f"{v:>4}" for v in row))
    print(f"mismatches (asserted): {bad}")
    return bad


# ---------------- Phase 42a: T4's second half, the orbit ears (ONE-EAR) ----------------

ORBIT_DIMS = (3, 4, 5, 6)
ORBIT_PER = 2       # cells drawn per (family, d, k, class)
ORBIT_TRIES = 400   # box draws per (family, d, k)
ORBIT_NMAX = 40     # bodies of G
ORBIT_REDRAWS = 3   # fresh points per cell after a failed degeneracy guard
# Result 23's two d = 4 cells where (*) at k = 1 asks for 3: theta(2,2,9)
# and theta(2,3,8), the ear a 2-path, G[V1] = C_11 (core lengths of "th3")
ORBIT_FIXED = {("th3", 4, 1): ((2, 9), (3, 8))}


def orbit_meet(s, spec, d):
    """dim(Pi_a cap Pi_b) on the incidence locus, at a configuration of G_1
    (the ear a - x_1 - b) drawn from the sampler s; Pi_v the plane of v in
    G_1.  Besides the point of x_1 the meet holds whatever the structure of
    G[V1] forces: shared neighbours, or an edge between the ends' blocks."""
    n2, E2, _, _, a, b = spec.graph(1)
    pts, _ = orbit_config(s, n2, E2, d)
    A, B = plane_of(pts, E2, a), plane_of(pts, E2, b)
    need(len(A) == 3 and len(B) == 3, "the planes of a, b")
    return len(span_cap(A, B))


def orbit_spec(fam, lengths, k):
    core = SHORT_FAMS[fam][0]
    return CoreEar(core, list(lengths) + [k + 1])


def orbit_counts(spec, d, k):
    """The deficiencies of the search (`path_partitions_def`; `orbit_cell`
    certifies them), or None if the spec is outside the population: n >
    ORBIT_NMAX, ends adjacent, def_3(G) < d - 2 (outside the content range),
    or def_D(G[V1]) <= def_D(G) (row 12 covers the step: k + 1 independent
    joins give (*))."""
    D = (d + 1) * d // 2
    n, E, paths, blocks, a, b = spec.graph(k)
    n1, E1, paths1, blocks1 = spec.base()
    if n > ORBIT_NMAX or a == b or {a, b} in map(set, E1):
        return None
    if path_partitions_def(n, E, paths, 3, blocks) < d - 2:
        return None
    dG = path_partitions_def(n, E, paths, D, blocks)
    f = path_partitions_def(n1, E1, paths1, D, blocks1)
    if f <= dG:
        return None
    nb = [{w for e in E1 if v in e for w in e} - {v} for v in (a, b)]
    out = dict(dG=dG, f=f, sh=len(nb[0] & nb[1]))
    if k == 2:
        n2, E2, paths2, blocks2, _, _ = spec.graph(1)
        out["dG1"] = path_partitions_def(n2, E2, paths2, D, blocks2)
    return out


def orbit_search(fam, d, k):
    """The cells for (fam, d, k): ORBIT_FIXED's, then a search of fam's box
    seeded by (fam, d, k) alone, so the same at every --seed.  Every cell has
    an open ear with k interior bodies at non-adjacent ends, def_3(G) >= d-2
    and def_D(G[V1]) > def_D(G) (`orbit_counts`).  At k = 2 also def_D(G_1) =
    def_D(G), G_1 = G with x_2 suppressed (no slack: (*) needs one dimension
    more than W), and the cells split in two classes: 'danger', where
    s = 2 + f - def_D(G_1), the predicted dim W, is at least C(6 - meet, 2),
    the dimension of Lambda^2(A+B) (so W can contain it), and at most D-1;
    'plain' otherwise.  The meet is `orbit_meet`'s, at a configuration drawn
    from a sampler seeded by (fam, d, k) too.  Up to ORBIT_PER cells per
    class."""
    D = (d + 1) * d // 2
    classes = ("plain", "danger") if k == 2 else ("plain",)
    found = {c: [] for c in classes}
    S = Sampler(2000000 + 10000 * list(SHORT_FAMS).index(fam) + 100 * d + k)

    def take(spec):
        c = orbit_counts(spec, d, k)
        if c is None or (k == 2 and c["dG1"] != c["dG"]):
            return
        cls = "plain"
        if k == 2:
            try:
                m = orbit_meet(S, spec, d)
            except Degenerate:
                return
            if (6 - m) * (5 - m) // 2 <= 2 + c["f"] - c["dG1"] <= D - 1:
                cls = "danger"
        if len(found[cls]) < ORBIT_PER:
            found[cls].append((cls, spec))

    for ls in ORBIT_FIXED.get((fam, d, k), ()):
        take(orbit_spec(fam, ls, k))
    R = random.Random(1000000 + 10000 * list(SHORT_FAMS).index(fam) + 100 * d + k)
    seen = set()
    for _ in range(ORBIT_TRIES):
        if all(len(v) == ORBIT_PER for v in found.values()):
            break
        spec = short_draw(R, fam, D, k)
        if spec is None or spec.key in seen:
            continue
        seen.add(spec.key)
        take(spec)
    return [x for c in classes for x in found[c]]


def orbit_config(s, n, E, d):
    """A pencil configuration of (n, E) in P^d: a seeded picture, d-2 heights
    in L(q); the points and the hinges."""
    q = [s.vec(2) for _ in range(n)]
    b, H = pd_pencil(s, n, E, d, q, lifting_space(n, E, q))
    body_guard(n, E, H)
    return b, H


def orbit_cell(s, spec, d, k):
    """One cell.  k = 1 (row 14, thm:pencil-x0-open-ear-one): G's configuration,
    on V1 a point of the incidence locus b_x in Pi_a cap Pi_b; G[V1]'s rank
    there, rho, and (*)'s dim(rho + Lambda), Lambda = span(p_a x, x p_b).
    k = 2 (row 15, thm:pencil-x0-open-ear-two-orbit): the d = 3 route, G_1's
    configuration (the locus, y the point of x_1), W = rho + span(p_a y,
    y p_b), A, B the planes of a, b there, Lambda^2(A+B) the span of every
    hinge an insertion x_1 in A, x_2 in B can reach; then a general such
    insertion; and, apart from the route, G's own configuration, where
    G[V1] is general."""
    D = (d + 1) * d // 2
    n, E, paths, blocks, a, b = spec.graph(k)
    n1, E1, paths1, blocks1 = spec.base()
    c = dict(D=D, n=n, dG=def_certified(s, n, E, paths, D, blocks),
             f=def_certified(s, n1, E1, paths1, D, blocks1),
             d3=def_certified(s, n, E, paths, 3, blocks))
    c["need"] = k + 1 + c["f"] - c["dG"]
    c["t1"], c["tG"] = D * (n1 - 1) - c["f"], D * (n - 1) - c["dG"]
    nb = [{w for e in E1 if v in e for w in e} - {v} for v in (a, b)]
    c["sh"] = len(nb[0] & nb[1])
    # the d = 3 steps' merged hypothesis def_3(G[V1]; a, b) + 2 <= def_3(G[V1]):
    # adding ab lowers def_3 by at most 2, and by 2 exactly when it holds
    # (the partitions keeping a, b together do not change)
    c["M"] = (def_certified(s, n1, E1, paths1, 3, blocks1)
              - def_certified(s, n1, E1 + [(a, b)], paths1 + [[a, b]], 3, blocks1)) == 2

    def at(pts, edges):
        """G[V1]'s rank, rho, the planes of a and b in the graph of pts and
        their meet, and whether each end's point is off the other's plane."""
        base = pts[:n1]
        H1 = [ext([base[u], base[v]]) for u, v in E1]
        A, B = plane_of(pts, edges, a), plane_of(pts, edges, b)
        need(len(A) == 3 and len(B) == 3, "the planes of a, b")
        off = rank(A + [pts[b]]) == 4 and rank(B + [pts[a]]) == 4
        return motion_rank(n1, E1, H1), rel_screws(n1, E1, H1, a, b), A, B, off

    def joins(ps):
        return [ext([p, p2]) for p, p2 in zip(ps, ps[1:])]

    if k == 1:
        bG, H = orbit_config(s, n, E, d)
        c["rG"] = motion_rank(n, E, H)
        c["r1"], rho, A, B, c["off"] = at(bG, E)
        c["meet"], c["rho"] = len(span_cap(A, B)), len(rho)
        c["s"] = rank(rho + joins([bG[a], bG[n1], bG[b]]))
        c["formula"] = c["rG"] == c["r1"] + (D - 1) + c["s"] - 1
        return c
    n2, E2, paths2, blocks2, _, _ = spec.graph(1)
    c["dG1"] = def_certified(s, n2, E2, paths2, D, blocks2)
    c["tG1"] = D * (n2 - 1) - c["dG1"]
    b1, H1p = orbit_config(s, n2, E2, d)
    c["rG1"] = motion_rank(n2, E2, H1p)
    c["r1"], rho, A, B, c["off"] = at(b1, E2)
    c["meet"], c["rho"] = len(span_cap(A, B)), len(rho)
    y = b1[n1]
    c["s"] = rank(rho + joins([b1[a], y, b1[b]]))
    AB = [(A + B)[i] for i in _pivots(A + B)]
    c["lam"] = rank([ext([u, v]) for u, v in combinations(AB, 2)])
    c["c"] = rank(rho + [ext([u, v]) for u, v in combinations(AB, 2)])
    x1, x2 = point_over(A, s.vec(2)), point_over(B, s.vec(2))
    c["ins"] = rank(rho + joins([b1[a], x1, x2, b1[b]]))
    pts = b1[:n1] + [x1, x2]
    body_guard(n, E, joins_of(pts, E))
    rR = motion_rank(n, E, joins_of(pts, E))
    c["formula"] = (c["rG1"] == c["r1"] + (D - 1) + c["s"] - 1
                    and rR == c["r1"] + 2 * (D - 1) + c["ins"] - 1)
    c["rR"] = rR
    bG, H = orbit_config(s, n, E, d)
    c["rG"] = motion_rank(n, E, H)
    r1g, rhog, Ag, Bg, _ = at(bG, E)
    c["gen"] = rank(rhog + joins([bG[a], bG[n1], bG[n1 + 1], bG[b]]))
    c["r1g"], c["meetg"] = r1g, len(span_cap(Ag, Bg))
    c["formula"] &= c["rG"] == r1g + 2 * (D - 1) + c["gen"] - 1
    return c


def joins_of(pts, E):
    return [ext([pts[u], pts[v]]) for u, v in E]


def mode_orbit(s):
    print("T4's second half (Phase 42a; Phase42-design.md sections 2.3-2.4, "
          "ONE-EAR): the orbit ears, an open ear a - x_1 (- x_2) - b on V1 with "
          "k = 1, 2 interior bodies at non-adjacent ends, where def_D(G[V1]) > "
          "def_D(G), so row 12 does not cover the step and (*) asks dim(rho + "
          "Lambda) >= need = k + 1 + f - def_D(G) >= k + 2 "
          "(sec:main-component-orbit; f = def_D(G[V1])).  Content range only "
          "(def_3(G) >= d - 2).  Cells from the families of --short (`orbit_"
          "search`, seeded by (family, d, k) alone), plus Result 23's two d = 4 "
          "cells.  k = 1: at G's configuration, whose restriction to V1 lies on "
          "the incidence locus: G[V1] (sh1 = t1 - its rank), s = dim(rho + "
          "Lambda) against need, G.  k = 2, the d = 3 route: G_1 = G with x_2 "
          "suppressed at its own configuration (the locus; y the point of x_1); "
          "sh1, shG1 = G[V1], G_1 below target; s = dim W, W = rho + span(p_a y, "
          "y p_b); lam = dim Lambda^2(A+B), A, B the planes of a, b; c = dim(rho "
          "+ Lambda^2(A+B)), the most any insertion x_1 in A, x_2 in B reaches; "
          "ins = dim(rho + Lambda) at a general one; then, apart from the route, "
          "gen = dim(rho + Lambda) at G's own configuration, where G[V1] is "
          "general.  meet = dim(Pi_a cap Pi_b) (k = 2: at G_1's configuration | "
          "at G's).  o: each end's point off the other end's plane.  Flags: 'I' "
          "ins < min(s+1, c) (a P^d form of lem:pencil-insertion-two fails), "
          "'X' c < need (every insertion falls short: the route is obstructed), "
          "'*' ins < need, '!' gen < need, '~' a redraw.  Asserted at every "
          "cell: every deficiency certified (`def_certified`), the ear rank "
          "formula (lem:block-rank-ear) at each configuration, every rank at most "
          "its count, s = 2 + f - def_D(G_1) where G[V1] and G_1 attain, and o "
          "wherever M (M puts each end off the other's plane at d = 3, and a "
          "P^d configuration projects to a P^3 one).  At d = 3 wherever o, "
          "where the chapter proves the step: lam = 6 and ins >= min(s+1, 6) "
          "(lem:pencil-insertion-two).  M: the d = 3 steps' merged hypothesis "
          "def_3(G[V1]; a, b) + 2 <= def_3(G[V1]), certified as def_3(G[V1]) - "
          "def_3(G[V1] + ab) = 2.")
    print("families (G[V1]; a, b): " + "; ".join(f"{g}: {v[2]}" for g, v in SHORT_FAMS.items()))
    bad, tally = 0, {}
    cols1 = ("cells", "G[V1] at target on the locus", "(*)", "G at target")
    cols2 = ("cells", "G_1 at target", "G[V1] at target on the locus",
             "W contains Lambda^2(A+B), W proper", "ins >= min(s+1, c)",
             "the route's (*): ins >= need", "c >= need", "gen >= need", "G at target")
    for k in (1, 2):
        print(f"k = {k}" + (" (row 14, one-body ear)" if k == 1 else
                            " (row 15, two-body ear at non-adjacent ends)"))
        if k == 1:
            print(f"{'fam':5}{'lengths':18}{'d':>2}{'n':>4}{'sh':>3}{'M':>2}{'d3':>4}"
                  f"{'f':>4}{'dG':>4}{'sh1':>4}{'meet':>5}{'o':>2}{'rho':>4}{'s':>4}"
                  f"{'need':>5}{'G':>12}")
        else:
            print(f"{'fam':5}{'cls':>7}{'lengths':>18}{'d':>2}{'n':>4}{'sh':>3}{'M':>2}{'d3':>4}"
                  f"{'f':>4}{'dG':>4}{'dG1':>4}{'sh1':>4}{'shG1':>5}{'meet':>6}{'o':>2}"
                  f"{'rho':>4}{'s':>4}{'lam':>4}{'c':>4}{'ins':>4}{'need':>5}{'gen':>4}"
                  f"{'G':>12}")
        for d in ORBIT_DIMS:
            D = (d + 1) * d // 2
            for fam in SHORT_FAMS:
                for cls, spec in orbit_search(fam, d, k):
                    for draws in range(ORBIT_REDRAWS + 1):
                        try:
                            c = orbit_cell(s, spec, d, k)
                            break
                        except Degenerate as e:
                            err = e
                    else:
                        bad += 1
                        print(f"{fam:5}{spec.label():18}{d:>2}  degenerate: {err}")
                        continue
                    sh1 = c["t1"] - c["r1"]
                    bad += not c["formula"]
                    bad += c["M"] and not c["off"]
                    bad += min(sh1, c["tG"] - c["rG"]) < 0
                    Gc = f"{c['rG']}/{c['tG']}" + ("" if c["rG"] == c["tG"] else "<")
                    t = tally.setdefault((k, fam, d), [0] * (len(cols1) if k == 1 else len(cols2)))
                    if k == 1:
                        star = c["s"] < c["need"]
                        flags = ("*" if star else "") + "~" * draws
                        for i, v in enumerate((1, sh1 == 0, not star, c["rG"] == c["tG"])):
                            t[i] += v
                        print(f"{fam:5}{spec.label():18}{d:>2}{c['n']:>4}{c['sh']:>3}"
                              f"{'y' if c['M'] else 'n':>2}{c['d3']:>4}{c['f']:>4}{c['dG']:>4}{sh1:>4}{c['meet']:>5}"
                              f"{'o' if c['off'] else '.':>2}{c['rho']:>4}{c['s']:>4}"
                              f"{c['need']:>5}{Gc:>12} {flags}")
                        continue
                    shG1 = c["tG1"] - c["rG1"]
                    bad += min(shG1, c["tG"] - c["rR"]) < 0
                    bad += sh1 == shG1 == 0 and c["s"] != 2 + c["f"] - c["dG1"]
                    ins_ok = c["ins"] >= min(c["s"] + 1, c["c"])
                    if d == 3 and c["off"]:
                        bad += c["lam"] != 6 or c["ins"] < min(c["s"] + 1, 6)
                    contain = c["c"] == c["s"] < D
                    flags = (("I" if not ins_ok else "") + ("X" if c["c"] < c["need"] else "")
                             + ("*" if c["ins"] < c["need"] else "")
                             + ("!" if c["gen"] < c["need"] else "") + "~" * draws)
                    for i, v in enumerate((1, shG1 == 0, sh1 == 0, contain, ins_ok,
                                           c["ins"] >= c["need"], c["c"] >= c["need"],
                                           c["gen"] >= c["need"], c["rG"] == c["tG"])):
                        t[i] += v
                    print(f"{fam:5}{cls:>7}{spec.label():>18}{d:>2}{c['n']:>4}{c['sh']:>3}"
                          f"{'y' if c['M'] else 'n':>2}{c['d3']:>4}{c['f']:>4}{c['dG']:>4}{c['dG1']:>4}{sh1:>4}{shG1:>5}"
                          f"{str(c['meet']) + '|' + str(c['meetg']):>6}"
                          f"{'o' if c['off'] else '.':>2}{c['rho']:>4}{c['s']:>4}{c['lam']:>4}"
                          f"{c['c']:>4}{c['ins']:>4}{c['need']:>5}{c['gen']:>4}{Gc:>12} {flags}")
        cols = cols1 if k == 1 else cols2
        print(f"per family and d (k = {k}), the columns: " + "; ".join(cols))
        for d in ORBIT_DIMS:
            row = [0] * len(cols)
            for (kk, fam, dd), t in tally.items():
                if kk == k and dd == d:
                    print(f"  d={d} {fam:5}" + " ".join(f"{v:>4}" for v in t))
                    row = [x + v for x, v in zip(row, t)]
            print(f"  d={d} all  " + " ".join(f"{v:>4}" for v in row))
    print(f"mismatches (asserted): {bad}")
    return bad


# ---------------- Phase 42a's T5: the coverage at D ----------------

COV_DIMS = (3, 4, 5, 6)
COV_LMAX = 4         # core paths of 1..COV_LMAX edges: chains of k <= 3 bodies
COV_EXHAUST = 4096   # a core with at most this many length vectors: all of them
COV_TRIES = 3000     # box draws per (core, d) otherwise
COV_PER = 60         # graphs kept per (core, d) from the draws
PETERSEN = (10, [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
             + [(5 + i, 5 + (i + 2) % 5) for i in range(5)])
COV_CORES = {
    # name: (core bodies, core edges); each 2-connected, of minimum degree 3
    "th3": (2, [(0, 1)] * 3),
    "th4": (2, [(0, 1)] * 4),
    "hub": (3, [(0, 1), (0, 1), (0, 2), (2, 1), (0, 2)]),
    "same": (4, [(0, 1), (0, 1), (0, 2), (2, 3), (3, 1), (2, 3)]),
    "k4": (4, [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]),
    "w4": (5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4), (4, 1)]),
    "prism": (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]),
    "k33": (6, [(i, j) for i in range(3) for j in range(3, 6)]),
    "cube": (8, [(i, i ^ (1 << t)) for i in range(8) for t in range(3) if i < i ^ (1 << t)]),
    "petersen": PETERSEN,
}


def core_def(nc, paths, D):
    """def_D of the subdivision of a core multigraph: nc core bodies, and each
    path (u, v, L) a path of L edges from u to v whose L - 1 interior bodies
    have degree two (u = v: a cycle through u; L = 1: an edge, a loop if
    u = v).  Exact.  Among the partitions attaining def_D take one with the
    most parts.  An interior body with at most one neighbour in its part, not
    alone, gains 1 or D by leaving it, so each interior body is alone or its
    part holds its whole path, ends included.  The parts are then the blocks
    of a partition of the core with paths absorbed, and a path inside a block
    is absorbed iff L <= D (left out, it adds D(L-1) - (D-1)L = L - D).  So
    def_D = c0 + max over the partitions of the core of sum_B w(B), with w(B)
    = D + the sum over the non-loop paths inside B of D-1 (L = 1) or
    max(0, D-L) (L >= 2), and c0 = -D - (D-1)(the non-loop edges) + sum of
    L - D over the non-loop paths with L >= 2 + sum of max(0, L - D) over the
    loops with L >= 2: a subset DP over the core, as `deficiency` is over the
    bodies; --coverage checks the two against each other under the DP cap."""
    c0, inner = -D, []
    for u, v, L in paths:
        if u == v:
            c0 += max(0, L - D) if L >= 2 else 0
        elif L == 1:
            c0 -= D - 1
            inner.append((u, v, D - 1))
        else:
            c0 += L - D
            inner.append((u, v, max(0, D - L)))
    full = (1 << nc) - 1
    w = [D + sum(om for u, v, om in inner if (S >> u) & 1 and (S >> v) & 1)
         for S in range(full + 1)]
    best = [0] * (full + 1)
    for S in range(1, full + 1):
        low = S & -S
        rest = S ^ low
        b, T = None, rest
        while True:
            part = T | low
            val = w[part] + best[S ^ part]
            if b is None or val > b:
                b = val
            if T == 0:
                break
            T = (T - 1) & rest
        best[S] = b
    return c0 + best[full]


def core_expand(nc, paths):
    """The subdivision itself: its body count and edges, core bodies first."""
    n, E = nc, []
    for u, v, L in paths:
        p = [u] + list(range(n, n + L - 1)) + [v]
        n += L - 1
        E += list(zip(p, p[1:]))
    return n, E


def core_identify(nc, paths, a, b):
    """The core with b identified into a (`identify`, on cores): its def_D is
    the merged deficiency def_D(G; a, b)."""
    ix = {v: i for i, v in enumerate(w for w in range(nc) if w != b)}
    ix[b] = ix[a]
    return nc - 1, [(ix[u], ix[v], L) for u, v, L in paths]


def core_induce(nc, paths, U, S):
    """G[W], W = the core bodies of the mask U plus the interiors of the
    paths S: U relabelled in order, the paths S and the edges inside U."""
    ix = {v: i for i, v in enumerate(u for u in range(nc) if (U >> u) & 1)}
    return len(ix), [(ix[u], ix[v], L) for j, (u, v, L) in enumerate(paths)
                     if j in S or (L == 1 and (U >> u) & 1 and (U >> v) & 1)]


def core_contract(nc, paths, U, S):
    """G/G[W] (def:rigid-contraction), W as in `core_induce`, collapsed to
    its least core body r: G[W]'s edges deleted, every other path kept with
    its ends in U moved to r (a path of U outside S becomes a cycle at r)."""
    r = min(u for u in range(nc) if (U >> u) & 1)
    keep = [v for v in range(nc) if not (U >> v) & 1 or v == r]
    ix = {v: i for i, v in enumerate(keep)}
    for v in range(nc):
        if (U >> v) & 1:
            ix[v] = ix[r]
    return len(keep), [(ix[u], ix[v], L) for j, (u, v, L) in enumerate(paths)
                       if not (j in S or (L == 1 and (U >> u) & 1 and (U >> v) & 1))]


def core_sparse(nc, paths):
    """G sparse: s_3(X) >= 1 for every X of two or more bodies.  A violating X
    contains a set of planar deficiency zero (lem:deficiency-sparse), whose
    bodies each have two neighbours in it, so a set U of core bodies (two or
    more, as the core has no loops) plus whole paths between them.  Over
    those 2e - 3|X| is largest with every 2-path of U taken (a path adds
    3 - L).  So G is sparse iff 2 (edges of U) + (2-paths of U) <= 3|U| - 4
    for every U of two or more core bodies."""
    for U in range(1, 1 << nc):
        size = bin(U).count("1")
        val = sum(3 - L for u, v, L in paths
                  if L <= 2 and u != v and (U >> u) & 1 and (U >> v) & 1)
        if size >= 2 and val > 3 * size - 4:
            return False
    return True


def core_sets(nc, paths, D, need_u=0, need_p=None, twos=False):
    """Every W = U + the interiors of the paths S (each of 2+ edges, both ends
    in U) with |W| >= 2, every body of W with two neighbours in W, and
    s_D(W) <= 0: the shape of every set of deficiency zero at D (alone, a body
    with one neighbour in its set has value D - (D-1) > 0, and an interior
    body's two neighbours bring its whole path), and a necessary condition
    for it.  Only U containing need_u and S containing need_p; with twos,
    every 2-path of U in S.  Yields (U, S, |W|)."""
    longp = [j for j, (u, v, L) in enumerate(paths) if L >= 2]
    for U in range(1, 1 << nc):
        if U & need_u != need_u:
            continue
        inside = [j for j in longp if (U >> paths[j][0]) & 1 and (U >> paths[j][1]) & 1]
        if need_p is not None and need_p not in inside:
            continue
        fixed = [j for j in inside if j == need_p or (twos and paths[j][2] == 2)]
        free = [j for j in inside if j not in fixed]
        dirU = [(u, v) for u, v, L in paths if L == 1 and (U >> u) & 1 and (U >> v) & 1]
        for mask in range(1 << len(free)):
            S = fixed + [free[i] for i in range(len(free)) if (mask >> i) & 1]
            size = bin(U).count("1") + sum(paths[j][2] - 1 for j in S)
            if size < 2:
                continue
            deg = dict.fromkeys((u for u in range(nc) if (U >> u) & 1), 0)
            for u, v in dirU + [paths[j][:2] for j in S]:
                deg[u] += 1
                deg[v] += 1
            e = len(dirU) + sum(paths[j][2] for j in S)
            if min(deg.values()) >= 2 and D * (size - 1) - (D - 1) * e <= 0:
                yield U, S, size


def cov_core(nc, paths, D, d3):
    """A core at D, clause (7) of def:pencil-x0-reduces read at D (row 9: the
    contracted set has def_D = 0, the additivity stays planar): W proper,
    def_D(G[W]) = 0, no body outside W adjacent to two bodies of W, and
    def_3(G[W]) + def_3(G/G[W]) <= def_3(G).  The first (U, S) found, or None,
    over every W of `core_sets`'s shape with every 2-path of U in S (else
    that path's interior body is adjacent to two bodies of W)."""
    nW = nc + sum(L - 1 for _, _, L in paths)
    for U, S, size in core_sets(nc, paths, D, twos=True):
        if size == nW:
            continue
        if any(sum(1 for u, v, L in paths if L == 1 and z in (u, v) and (U >> (u + v - z)) & 1) >= 2
               for z in range(nc) if not (U >> z) & 1):
            continue
        sub = core_induce(nc, paths, U, S)
        if (core_def(*sub, D) == 0
                and core_def(*sub, 3) + core_def(*core_contract(nc, paths, U, S), 3) <= d3):
            return U, S
    return None


def core_auts(nc, ce):
    """The core's automorphisms, as permutations of its bodies."""
    base = sorted(tuple(sorted(e)) for e in ce)
    return [p for p in permutations(range(nc))
            if sorted(tuple(sorted((p[u], p[v]))) for u, v in ce) == base]


def cov_population(name, d, auts, lmax=COV_LMAX):
    """The graphs of core `name` at d: every length vector in [1, lmax]^E if
    there are at most COV_EXHAUST, else COV_TRIES box draws seeded by (name,
    d, lmax) alone, keeping the first COV_PER; one per isomorphism class (the
    core's automorphisms), simple (no two 1-paths on one pair), sparse, and in
    the content range def_3 >= d - 2.  Each core body has degree >= 3, so G is
    2-connected and not a cycle, and its chains are its paths of 2+ edges."""
    nc, ce = COV_CORES[name]
    if lmax ** len(ce) <= COV_EXHAUST:
        vecs, cap = product(range(1, lmax + 1), repeat=len(ce)), None
    else:
        R = random.Random(3000000 + 10000 * lmax + 100 * list(COV_CORES).index(name) + d)
        vecs = (tuple(R.randint(1, lmax) for _ in ce) for _ in range(COV_TRIES))
        cap = COV_PER
    out, seen = [], set()
    for ls in vecs:
        key = min(tuple(sorted((min(p[u], p[v]), max(p[u], p[v]), L)
                               for (u, v), L in zip(ce, ls))) for p in auts)
        if key in seen:
            continue
        seen.add(key)
        paths = [(u, v, L) for (u, v), L in zip(ce, ls)]
        ones = [frozenset((u, v)) for u, v, L in paths if L == 1]
        if (len(ones) == len(set(ones)) and core_sparse(nc, paths)
                and core_def(nc, paths, 3) >= d - 2):
            out.append((ls, paths))
            if cap and len(out) == cap:
                break
    return out


def cov_cell(nc, paths, d):
    """The rows of def:pencil-x0-reduces read at D = C(d+1, 2) that apply to
    G, and the facts the coverage's proof needs at D.  Per chain a - x_1 ..
    x_k - b on V1 (f = def_D(G[V1]), m = def_D(G[V1]; a, b)): 'long' k >= D-1;
    'ear' 2 <= k <= D-1 and f <= def_D(G) (row 12); 'short' 3 <= k <= D-2 and
    f > def_D(G) (SHORT); 'orbit2' k = 2, ends apart, f > def_D(G) and M
    (row 15); 'one' k = 1, ends apart, f <= def_D(G) and M (row 14); 'split'
    k = 1, ends apart, m + D-1 <= f (row 16).  M is the d = 3 steps' merged
    hypothesis def_3(G[V1]; a, b) + 2 <= def_3(G[V1]).  Global: 'flat'
    def_3 = def_D (row 5), 'base' def_(D_(d-1)) = def_D (R1's base row), and
    'core' (`cov_core`).  'orbit1' marks a k = 1 chain with f > def_D(G) and
    no split-off: (*) there is ONE-EAR's third part, which no row uses."""
    D, Dm = (d + 1) * d // 2, d * (d - 1) // 2
    dG, d3 = core_def(nc, paths, D), core_def(nc, paths, 3)
    c = dict(D=D, dG=dG, d3=d3, rows=[], chains=[], orbit1=0)
    if d3 == dG:
        c["rows"].append(("flat", 0, False))
    c["base"] = d >= 4 and core_def(nc, paths, Dm) == dG
    for i, (a, b, L) in enumerate(paths):
        if L < 2:
            continue
        k, G1 = L - 1, paths[:i] + paths[i + 1:]
        f, f3 = core_def(nc, G1, D), core_def(nc, G1, 3)
        mg = core_identify(nc, G1, a, b)
        m, m3 = core_def(*mg, D), core_def(*mg, 3)
        adj = any(LL == 1 and {u, v} == {a, b} for u, v, LL in G1)
        nb = [{u + v - x for u, v, LL in G1 if LL == 1 and x in (u, v)} for x in (a, b)]
        sh = (any(LL == 2 and {u, v} == {a, b} for u, v, LL in G1)
              or bool(nb[0] & nb[1]))
        M, split = m3 + 2 <= f3, k == 1 and not adj and m + D - 1 <= f
        rows = [("long", k >= D - 1), ("ear", 2 <= k <= D - 1 and f <= dG),
                ("short", 3 <= k <= D - 2 and f > dG),
                ("orbit2", k == 2 and not adj and f > dG and M),
                ("one", k == 1 and not adj and f <= dG and M), ("split", split)]
        c["rows"] += [(r, k, sh) for r, ok in rows if ok]
        c["orbit1"] += k == 1 and f > dG and not split
        usable = (k >= 3 or (k == 2 and (m == f or (not adj and M)))
                  or (k == 1 and (m == f or split)))
        c["chains"].append(dict(i=i, k=k, f=f, m=m, f3=f3, m3=m3, adj=adj, M=M,
                                split=split, usable=usable, G1=G1, mg=mg))
    c["core"] = cov_core(nc, paths, D, d3)
    if c["core"] is not None:
        c["rows"].append(("core", 0, False))
    return c


def cov_tag(row, k, sh, d):
    """The obligation a row's P^d step carries (Phase42-design.md section
    2.1's verdicts): 'GEN', GEN given only formal work (CERT, CARRIER) or a
    proved part (SHORT's X3 range, k >= C(d-1, 2) + 3); 'SHORT-CORE';
    'ONE-EAR' (row 15 at d >= 4; row 14 at d >= 5, and at d = 4 when the
    ends share a neighbour in V1).  At d = 3 every row is Phase 40's."""
    if d == 3 or row in ("flat", "core", "long", "ear", "split"):
        return "GEN"
    if row == "short":
        return "GEN" if k >= (d - 1) * (d - 2) // 2 + 3 else "SHORT-CORE"
    if row == "one" and d == 4 and not sh:
        return "GEN"
    return "ONE-EAR"


def cov_label(name, ls):
    return f"{name} " + "".join(map(str, ls))


# Past the box: Petersen with every edge a path of L edges, at d.  By hand each
# is D-sparse but for V(G) (every proper subgraph has sum L > D c), so it has
# no core, and every chain has k = L - 1 >= 3 with f > def_D(G): its only rows
# are SHORT-CORE's (k <= C(d-1, 2) + 2).
COV_BEYOND = (("petersen", PETERSEN, 4, 4), ("petersen", PETERSEN, 6, 5))
COV_ROWS = ("flat", "core", "long", "ear", "short", "orbit2", "one", "split")


def cov_check(nc, paths, d, checked):
    """One cell: `cov_cell`, its class and its mismatches.  Asserted: the
    chain facts and the coverage at D (`mode_coverage`'s header), core_def
    against the DP where n <= 12, and at D >= 10 the reduction proved in
    Phase42-design.md section 2.4 (T5): a cell with no GEN row has a chain
    with k >= 3, or def_D(G) = 0 and every chain k = 1."""
    D, bad = (d + 1) * d // 2, 0
    c = cov_cell(nc, paths, d)
    if core_expand(nc, paths)[0] <= 12:
        for o in [(nc, paths)] + [o for ch in c["chains"] for o in ((nc, ch["G1"]), ch["mg"])]:
            for DD in (3, D):
                bad += core_def(*o, DD) != deficiency(*core_expand(*o), DD)
                checked[0] += 1
    for ch in c["chains"]:
        a, b, _ = paths[ch["i"]]
        bad += ch["m"] == ch["f"] and ch["f"] > c["dG"]
        bad += ch["k"] == 2 and not ch["adj"] and ch["m"] != ch["f"] and not ch["M"]
        if ch["k"] == 1:
            bad += ch["adj"] or not ch["M"]
            if ch["m"] != ch["f"] and not ch["split"]:
                bad += not any(core_def(*core_induce(nc, paths, U, S), D) == 0
                               for U, S, _ in core_sets(nc, paths, D, (1 << a) | (1 << b), ch["i"]))
                checked[1] += 1
    n, E = core_expand(nc, paths)
    if c["core"] is not None and n <= 12:
        # the core again on the bodies, by the 3^n DP: W proper, def_D(G[W]) =
        # 0, no body outside W with two neighbours in W, and the additivity
        U, S = c["core"]
        W, pos = {u for u in range(nc) if (U >> u) & 1}, nc
        for j, (u, v, L) in enumerate(paths):
            W |= set(range(pos, pos + L - 1)) if j in S else set()
            pos += L - 1
        iw = {v: i for i, v in enumerate(sorted(W))}
        EW = [(iw[u], iw[v]) for u, v in E if u in W and v in W]
        r = min(W)
        ic = {v: i for i, v in enumerate(v for v in range(n) if v not in W or v == r)}
        ic.update(dict.fromkeys(W, ic[r]))
        EC = [(ic[u], ic[v]) for u, v in E if not (u in W and v in W)]
        out = [len({w for e in E if x in e for w in e} & W) for x in range(n) if x not in W]
        dW3, dC3 = deficiency(len(W), EW, 3), deficiency(n - len(W) + 1, EC, 3)
        bad += not (2 <= len(W) < n and deficiency(len(W), EW, D) == 0 and max(out) <= 1
                    and dW3 + dC3 <= c["d3"]
                    and dW3 == core_def(*core_induce(nc, paths, U, S), 3)
                    and dC3 == core_def(*core_contract(nc, paths, U, S), 3))
        checked[0] += 1
    c["covered"] = any(ch["usable"] for ch in c["chains"]) or c["core"] is not None
    bad += not c["covered"]
    tags = {cov_tag(r, k, sh, d) for r, k, sh in c["rows"]}
    c["cls"] = ("GEN" if "GEN" in tags else "either" if len(tags) == 2
                else tags.pop() if tags else "none")
    bad += c["cls"] == "none"
    ks = [ch["k"] for ch in c["chains"]]
    if D >= 10 and c["cls"] != "GEN":
        bad += not (max(ks) >= 3 or (c["dG"] == 0 and set(ks) == {1}))
    return c, bad


def cov_rowtext(c):
    return " ".join(f"{r}@{k}" + ("+" if sh and r == "one" else "") for r, k, sh in c["rows"])


def mode_coverage(s):
    print("T5 (Phase 42a; Phase42-design.md section 2.4, coverage): the structural "
          "coverage (sec:main-component-coverage) read at D = C(d+1, 2), d = 3..6, "
          "on subdivisions of small cores (`COV_CORES`: every core body of degree "
          ">= 3, every core edge a path of 1..COV_LMAX edges), sparse, so past rows "
          "1-5 of the coverage's table (def_3 = def_D, a planar-rigid set, cut "
          "vertices, bridges, cycles), in the content range def_3 >= d - 2.  "
          "Deficiencies by `core_def`, exact, checked against the 3^n DP wherever "
          "n <= 12.  No point is drawn: the figures do not vary with the seed.  "
          "Rows, as `cov_cell` reads def:pencil-x0-reduces at D: flat, core, and "
          "per chain long, ear (row 12), short (SHORT), orbit2 (row 15), one "
          "(row 14), split (row 16); base, R1's base row, apart.  Each row's "
          "obligation as `cov_tag`: GEN, SHORT-CORE or ONE-EAR.  A cell is GEN if "
          "a GEN row applies; otherwise it needs SHORT-CORE, ONE-EAR, or either "
          "('either'), and 'R1' marks the open cells R1's base row settles.  "
          "Asserted at every cell, the coverage at D (some chain usable at D, or a "
          "core at D: Theorem S read at D), and per chain: m = f gives f <= "
          "def_D(G) (lem:deficiency-ear-merge); at k = 2, ends apart and m != f "
          "give M (lem:deficiency-two-body-chain, D >= 6); at k = 1 the ends are "
          "apart and M holds (lem:deficiency-one-body-chain (1)), and if neither "
          "m = f nor a split-off, x_1 lies in a set of def_D zero (its (2) read "
          "at D).  So no cell needs a k = 1 orbit cell (orbit1: f > def_D(G), no "
          "split-off), ONE-EAR's third part.  Also asserted at D >= 10: a cell "
          "with no GEN row has a chain with k >= 3, or def_D(G) = 0 and every "
          "chain k = 1 (so ONE-EAR alone can be needed only there, through row "
          "14).  Then `COV_BEYOND`, past the box, whose predicted class is "
          "asserted.")
    print("cores: " + "; ".join(f"{g}: {nc} bodies, {len(ce)} edges"
                                + (" (all)" if COV_LMAX ** len(ce) <= COV_EXHAUST else
                                   f" ({COV_PER} of {COV_TRIES} draws)")
                                for g, (nc, ce) in COV_CORES.items()))
    bad, auts, checked = 0, {}, [0, 0]
    classes = ("GEN", "SHORT-CORE", "ONE-EAR", "either")
    for d in COV_DIMS:
        D = (d + 1) * d // 2
        print(f"d = {d} (D = {D}); listed: the open cells (no GEN row), and the cells "
              f"whose every row is a k = 1, 2 ear: core lengths, n, def_3, def_D, R1, "
              f"class, rows (row@k, '+' ends sharing a neighbour in V1)")
        table, present, only_core = {}, dict.fromkeys(COV_ROWS, 0), 0
        for name, (nc, ce) in COV_CORES.items():
            if name not in auts:
                auts[name] = core_auts(nc, ce)
            t = table.setdefault(name, [0] * 7)
            for ls, paths in cov_population(name, d, auts[name]):
                c, b = cov_check(nc, paths, d, checked)
                bad += b
                if not c["covered"]:
                    print(f"  {cov_label(name, ls)}: NOT COVERED at D = {D}")
                kinds = {r for r, _, _ in c["rows"]}
                for r in kinds:
                    present[r] += 1
                only_core += {r for r, k, sh in c["rows"] if cov_tag(r, k, sh, d) == "GEN"} == {"core"}
                t[0] += 1
                if c["cls"] in classes:
                    t[1 + classes.index(c["cls"])] += 1
                t[5] += c["cls"] != "GEN" and c["base"]
                t[6] += c["orbit1"]
                if c["cls"] != "GEN" or (kinds and kinds <= {"one", "orbit2"}):
                    print(f"  {cov_label(name, ls):18}{core_expand(nc, paths)[0]:>4}{c['d3']:>4}"
                          f"{c['dG']:>4}{'R1' if c['base'] else '.':>4}  {c['cls']:11}{cov_rowtext(c)}")
                if name == "k4" and ls == (3,) * 6:
                    print(f"  C's hand count, {cov_label(name, ls)} (K_4, every edge "
                          f"subdivided twice): rows {cov_rowtext(c)}")
                    bad += d == 3 and kinds != {"orbit2"}
                    bad += d == 4 and "ear" not in kinds
        print(f"per core at d = {d}: graphs; GEN, SHORT-CORE, ONE-EAR, either; the "
              f"open ones R1 settles; the chains orbit1 (f > def_D(G), no split-off)")
        tot = [0] * 7
        for name, t in table.items():
            print(f"  {name:6}" + "".join(f"{v:>6}" for v in t))
            tot = [x + v for x, v in zip(tot, t)]
        print(f"  {'all':6}" + "".join(f"{v:>6}" for v in tot))
        print("  cells with each row: " + ", ".join(f"{r} {v}" for r, v in present.items())
              + f"; with core as their only GEN row: {only_core}")
        # the one-body box: paths of 1-2 edges, so every chain has k = 1; at
        # D >= 10 the cells with def_D(G) = 0 are the only ones where ONE-EAR
        # alone can be needed (cov_check's last assertion); listed: those with
        # no core, and any cell with no GEN row
        one = [0, 0, 0, 0, 0]
        for name, (nc, ce) in COV_CORES.items():
            for ls, paths in cov_population(name, d, auts[name], 2):
                c, b = cov_check(nc, paths, d, checked)
                bad += b
                cls_ = c["dG"] == 0
                gen = {r for r, k, sh in c["rows"] if cov_tag(r, k, sh, d) == "GEN"}
                one = [one[0] + 1, one[1] + cls_, one[2] + (cls_ and bool(gen)),
                       one[3] + (cls_ and "core" in gen), one[4] + (cls_ and gen == {"core"})]
                if not c["covered"] or c["cls"] != "GEN" or (cls_ and c["core"] is None):
                    print(f"  {cov_label(name, ls):18}{core_expand(nc, paths)[0]:>4}{c['d3']:>4}"
                          f"{c['dG']:>4}{'R1' if c['base'] else '.':>4}  {c['cls']:11}{cov_rowtext(c)}")
        print(f"  the one-body box (paths of 1-2 edges, every chain k = 1; {COV_PER} of "
              f"{COV_TRIES} draws past {COV_EXHAUST} vectors): {one[0]} graphs, {one[1]} "
              f"with def_D(G) = 0, {one[2]} of these with a GEN row, {one[3]} with a core, "
              f"{one[4]} with the core as their only GEN row")
    print("past the box (`COV_BEYOND`): core lengths, d, n, def_3, def_D, R1, class, rows")
    for name, (nc, ce), L, d in COV_BEYOND:
        paths = [(u, v, L) for u, v in ce]
        c, b = cov_check(nc, paths, d, checked)
        bad += b + (c["cls"] != "SHORT-CORE")
        print(f"  {name} {L}^{len(ce):<8}{d:>2}{core_expand(nc, paths)[0]:>4}{c['d3']:>4}"
              f"{c['dG']:>4}{'R1' if c['base'] else '.':>4}  {c['cls']:11}{cov_rowtext(c)}")
    print(f"core_def against the DP: {checked[0]} checks; x_1 in a set of def_D zero: "
          f"{checked[1]} chains")
    print(f"mismatches (asserted): {bad}")
    return bad


MODES = ("linear", "mixed", "perbody", "examples", "selftest",
         "complexes", "residual4", "d4", "lifting", "pd", "content", "oneear", "short",
         "orbit", "coverage")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    for m in MODES:
        ap.add_argument(f"--{m}", action="store_true")
    args = ap.parse_args()
    modes = [m for m in MODES if getattr(args, m)]
    if not modes:
        ap.error("choose a mode")
    print(f"seed {args.seed}")
    bad = sum(globals()[f"mode_{m}"](Sampler(args.seed)) for m in modes)
    if bad:
        print(f"FAILED: {bad} mismatch(es)")
        sys.exit(1)
    print("OK: every target met")


if __name__ == "__main__":
    main()
