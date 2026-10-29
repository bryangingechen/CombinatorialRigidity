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
no GF(p)).  The deficiency DP is exponential (3^n), hence n <= 12.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F
from itertools import combinations

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


MODES = ("linear", "mixed", "perbody", "examples", "selftest",
         "complexes", "residual4", "d4", "lifting", "pd", "content", "oneear")


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
