#!/usr/bin/env python3
"""strata.py -- body-hinge rank in P^3 on realization strata (2026-10-29).

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

Verdict: the last line is `OK: every target met`, or `FAILED: ...` with exit
status 1; a mismatch in any mode counts.

Population (labelled graphs, capped; nothing here is a census): the 23 graphs
of `GRAPHS` below, n <= 12 bodies.  Supports: a section (the plane, the point,
the complex, the lines) is drawn ONCE per stratum per run and reused for every
graph; the hinges vary per graph.  Coordinates are integers in
[-COORD, COORD]; combination coefficients are nonzero integers in that
range.  Exact Q throughout (`fractions.Fraction`, no GF(p)).
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


def motion_rank(n, edges, hinges):
    """6(n-1) - |E| + rank{g_e (x) C_e}, g_e = e's column of a cycle basis."""
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
    M = [[F(z.get(j, 0)) * hinges[j][i] for j in range(len(edges))]
         for z in cyc for i in range(6)]
    return 6 * (n - 1) - len(edges) + (rank(M) if M else 0)


# ---------------- sampling ----------------

class Sampler:
    def __init__(self, seed):
        self.R = random.Random(seed)

    def num(self):
        return F(self.R.randint(-COORD, COORD))

    def pt(self):
        return [self.num() for _ in range(4)]

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
    """L(q): heights z, affine in the picture on every closed neighbourhood."""
    nb = {v: sorted({w for e in edges if v in e for w in e} - {v})
          for v in range(n)}
    rows = []
    for v in range(n):
        N = [v] + nb[v]
        A = [[q[w][0], q[w][1], F(1)] for w in N]
        need(rank(A) == 3, f"picture not admissible at body {v}")
        for phi in left_nullspace(A):
            r = [F(0)] * n
            for w, c in zip(N, phi):
                r[w] += c
            rows.append(r)
    L = nullspace(rows) if rows else [[F(int(i == j)) for i in range(n)]
                                      for j in range(n)]
    affine = [[q[w][0] for w in range(n)], [q[w][1] for w in range(n)],
              [F(1)] * n]
    need(rank(L) >= 3 and rank(L + affine) == rank(L),
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    for m in ("linear", "mixed", "perbody", "examples", "selftest"):
        ap.add_argument(f"--{m}", action="store_true")
    args = ap.parse_args()
    modes = [m for m in ("linear", "mixed", "perbody", "examples", "selftest")
             if getattr(args, m)]
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
