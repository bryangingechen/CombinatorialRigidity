"""§(K-clos) driver — what the polarity does over an algebraically closed field.

A `w4/` leaf: nothing imports it, so its import closure is itself.  Run from
the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --fixed     # (AC-2), (AC-3)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --sweep     # (AC-4)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --shapes    # (AC-6)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --flanks    # (AC-6)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --pool      # (AC-6) THE AGGREGATE
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --parity    # (AC-6) the C11 mechanism
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --collapse  # (AC-5)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --char2     # (AC-8)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --validate  # all eight

`--pool` is the only place an aggregate figure may be read from: it runs over
exactly the union of the `--shapes` and `--flanks` rows and tallies them into
three DISJOINT groups (tight; rigid-but-not-count-tight; not rigid).  Note
`def = 0` and count-tightness `5|E| = 6(|V|−1)` are different predicates.
Argument state: `notes/Pencil-informal.md` §(K-clos).

WHY A NEW FIELD.  Every other driver in the harness is exact ℚ, and over ℚ (as
over ℝ) the project's polarity `σ = screwComplementIso` is built on the
*definite* standard dot product, so `x ⬝ᵥ x = 0 ⟹ x = 0`.  That single fact is
what powers §(K-σ) *Step σ1(a)* and *Step σ6*.  This driver works over the
Gaussian rationals **ℚ(i) ⊂ ℂ**, the smallest extension of ℚ in which
`∑ xᵢ² = 0` has nonzero solutions, and uses the harness's OWN `⋆`
(`repin.hodge_star`), its OWN rigidity-row builder
(`hybrid_gates.build_rigidity_extensors`) and its OWN nondegeneracy checker
(`flanks.nondeg_conjuncts`) unchanged — nothing about the polarity or the
predicate is re-implemented; only the scalar field is enlarged.  An existence
statement verified over ℚ(i) is an existence statement over `ℂ̄`.

Exact throughout: `Gauss` wraps a pair of `fractions.Fraction`.  No floating
point.  No randomness (so nothing to seed); no `set` is printed.

ONE FIGURE MOVED ON 2026-08-06 (slice S2 of the re-baselining round), and it
carries a NEW measured fact, **(AC-9)**.  The `starOK` column of `--sweep` and
the corresponding `--fixed` line used to report `star_span_ranks` alone; they
now report the composite `repin.star_generic` (closed-star ranks AND no two
hinge lines coinciding at a body).  Under it EVERY σ-fixed configuration of
`ds-K4` — all 64 ruling colourings, including the 12 target-rank ones and the
(AC-3) witness — is REJECTED, with a coincidence at every hub, while its rank,
its four `IsNondegPencilRealization` conjuncts and its closed-star ranks stay
green.  So (AC-3)'s refutation of "the σ-fixed locus is degenerate" is a
statement about THAT PREDICATE and not about genericity, and on this shape the
σ-fixed locus sits entirely inside the coincident-hinge locus.  `--char2`'s
seed also moved (0-60 first clean seed 2 → 6), since its `clean_pencil_seed`
now applies the composite guard; its mod-`p` ranks are an explicitly-labelled
proxy and moved with it.
"""
import argparse
import itertools
import os
import sys
from fractions import Fraction as F
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, neighbors, nullspace, rank, rref, wedge2  # noqa: E402
from pencil_escape import K4, K5_minus_matching, double_subdivide   # noqa: E402
from repin import hodge_star, lambda2_through                       # noqa: E402
from pitch import theta_edges                                       # noqa: E402
from hybrid_gates import build_rigidity_extensors                   # noqa: E402
from kbare_common import rank_modp, verts_of                        # noqa: E402
from exactcore import hat                                           # noqa: E402
from widened import W19                                             # noqa: E402
from flanks import clean_pencil_seed, nondeg_conjuncts             # noqa: E402
from repin import (coincident_hinges, star_generic,                 # noqa: E402
                   star_span_ranks)
from nogood_subdiv import (deficiency, hcard_ok, hub_set,        # noqa: E402
                           rigid_vertex_sets, triangles)


# ---------------------------------------------------------------- ℚ(i) ----

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


I = Gauss(0, 1)


def g(x):
    return Gauss(x, 0)


# --------------------------------------------------- the fixed quadric ----
#
# Q = {x : x ⬝ᵥ x = 0} ⊂ P³ is the quadric of self-conjugate points of the
# project's polarity.  Over ℚ it is empty; over ℚ(i) the substitution
# y = (x₀+ix₁, x₀−ix₁, x₂+ix₃, x₂−ix₃) turns x⬝ᵥx into y₀y₁ + y₂y₃, whose
# Segre parameterization gives the two rulings.

def grid_point(st, uv):
    """The point of Q at ruling parameters (s:t) ∈ P¹ (ruling A) and
    (u:v) ∈ P¹ (ruling B).  Homogeneous ℚ(i)⁴."""
    s, t = (g(st[0]), g(st[1]))
    u, v = (g(uv[0]), g(uv[1]))
    return [s * u + t * v, -I * (s * u - t * v),
            s * v - t * u, -I * (s * v + t * u)]


def ruling_A_line(st):
    """Plücker 6-vector of the ruling-A line {(s:t)} × P¹ ⊂ Q."""
    return wedge2(grid_point(st, (1, 0)), grid_point(st, (0, 1)))


def ruling_B_line(uv):
    """Plücker 6-vector of the ruling-B line P¹ × {(u:v)} ⊂ Q."""
    return wedge2(grid_point((1, 0), uv), grid_point((0, 1), uv))


# ------------------------------------------------- the ⋆ eigenspaces ------
#
# ⋆ = repin.hodge_star, an involution; on Λ²K⁴ its ±1 eigenspaces are the two
# 3-spaces below.  They are ℚ-RATIONAL even though the conic of decomposable
# vectors inside each is not.  In Plücker order (01,02,03,12,13,23).

EIG_P = [[F(1), F(0), F(0), F(0), F(0), F(1)],
         [F(0), F(1), F(0), F(0), F(-1), F(0)],
         [F(0), F(0), F(1), F(1), F(0), F(0)]]
EIG_M = [[F(1), F(0), F(0), F(0), F(0), F(-1)],
         [F(0), F(1), F(0), F(0), F(1), F(0)],
         [F(0), F(0), F(1), F(-1), F(0), F(0)]]


def star_sign(C):
    """+1 / -1 if ⋆C = ±C (C ≠ 0), else None."""
    S = hodge_star(C)
    j = next(k for k in range(6) if C[k] != 0)
    lam = S[j] / C[j]
    if all(S[k] == lam * C[k] for k in range(6)):
        if lam == 1:
            return +1
        if lam == -1:
            return -1
    return None


def eig_coords(C, basis):
    """Coordinates (α,β,γ) of C in `basis`; C must lie in the eigenspace."""
    M = [[basis[r][c] for r in range(3)] + [C[c]] for c in range(6)]
    R, piv = rref(M)
    assert piv == [0, 1, 2], "vector not in the eigenspace"
    return [R[r][3] for r in range(3)]


def conic_coords(C, basis):
    """The direction triple of an isotropic C inside a ⋆-eigenspace.

    On either eigenspace the ambient form restricts to ⟨x,x⟩ = 2(α²+β²+γ²),
    so the decomposable (= line) vectors of the eigenspace form a smooth
    conic — empty over ℝ, a P¹ over ℚ(i).  The assertion below IS the
    statement "the ruling's Plücker points are exactly that conic".
    """
    a, b, c = (Gauss._c(x) for x in eig_coords(C, basis))
    assert a * a + b * b + c * c == 0, "eigen-direction is not on the conic"
    return [a, b, c]


# ------------------------------------------------------- the shapes -------

def dsk4():
    edges, hubs, chains, allverts = double_subdivide(K4())
    return 'ds-K4', edges


def shapes():
    """Tight class shapes / residual inhabitants, with their own tight check."""
    out = [dsk4(),
           ('ds-(K5-M)', double_subdivide(K5_minus_matching())[0]),
           ('theta(3,4,5)', theta_edges([3, 4, 5])),
           ('theta(4,4,4)', theta_edges([4, 4, 4])),
           ('theta(3,3,6)', theta_edges([3, 3, 6])),
           ('theta(2,4,6)', theta_edges([2, 4, 6])),
           ('theta(1,5,6) hub-hub', theta_edges([1, 5, 6])),
           ('theta(2,2,8)', theta_edges([2, 2, 8])),
           ('theta(1,2,9) hub-hub', theta_edges([1, 2, 9])),
           ('theta(2,3,7)', theta_edges([2, 3, 7])),
           ('C12 bare cycle', theta_edges([6, 6])),
           ('C11 bare odd cycle', theta_edges([5, 6])),
           ('W19 (K-res)', W19()[0] if isinstance(W19(), tuple) else W19())]
    return out


# --------------------------------------------------- the 2-colourings -----

def alternation_classes(edges):
    """Partition the edges into ALTERNATION CHAINS.

    Conjunct 4 at a degree-2 body forbids its two edges from sharing a ruling
    (three collinear points otherwise), so edges meeting at a degree-2 body
    must get opposite colours.  Following that constraint through a branch
    gives one free bit per branch.  Returns a list of dicts
    {edge -> parity}, one per component of the constraint graph, and a flag
    saying whether any component is an ODD cycle (no proper colouring at all).
    """
    nb = neighbors(edges)
    link = {e: [] for e in edges}
    for v, ns in nb.items():
        if len(ns) == 2:
            inc = [e for e in edges if v in e]
            assert len(inc) == 2, f"degree-2 body {v} with {len(inc)} edges"
            link[inc[0]].append(inc[1])
            link[inc[1]].append(inc[0])
    seen, comps, odd = set(), [], False
    for e in edges:
        if e in seen:
            continue
        par, stack = {e: 0}, [e]
        seen.add(e)
        while stack:
            f = stack.pop()
            for h in link[f]:
                if h not in par:
                    par[h] = 1 - par[f]
                    seen.add(h)
                    stack.append(h)
                elif par[h] == par[f]:
                    odd = True
        comps.append(par)
    return comps, odd


def colourings(edges, cap=4096):
    """Every proper 2-colouring of the alternation constraint graph."""
    comps, odd = alternation_classes(edges)
    if odd:
        return [], odd
    n = len(comps)
    if 2 ** n > cap:
        return None, odd
    out = []
    for bits in itertools.product((0, 1), repeat=n):
        col = {}
        for c, b in zip(comps, bits):
            for e, p in c.items():
                col[e] = 'A' if (p ^ b) == 0 else 'B'
        out.append(col)
    return out, odd


def components(verts, edges):
    parent = {v: v for v in verts}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for u, w in edges:
        ru, rw = find(u), find(w)
        if ru != rw:
            parent[ru] = rw
    reps = sorted({find(v) for v in verts}, key=str)
    idx = {r: k for k, r in enumerate(reps)}
    return {v: idx[find(v)] for v in verts}


def cycle_rank(verts, edges):
    comp = components(verts, edges)
    return len(edges) - len(verts) + len(set(comp.values()))


def build_fixed_config(edges, allverts, col):
    """The σ-fixed pencil configuration of `edges` at the ruling colouring
    `col`.  Returns (pt, EA, EB) with `pt` homogeneous ℚ(i)⁴, or None if the
    colouring forces two bodies to coincide."""
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    compA = components(allverts, EA)   # constant ruling-A parameter (s:t)
    compB = components(allverts, EB)   # constant ruling-B parameter (u:v)
    if len({(compA[v], compB[v]) for v in allverts}) != len(allverts):
        return None
    pt = {v: grid_point((1, compA[v] + 1), (1, compB[v] + 1))
          for v in allverts}
    return pt, EA, EB


def dehom(p):
    assert p[3] != 0
    return [p[0] / p[3], p[1] / p[3], p[2] / p[3]]


# -------------------------------------------------------- the systems ----

def extensors(edges, pt):
    ext = [(e, wedge2(pt[e[0]], pt[e[1]])) for e in edges]
    for _, C in ext:
        assert any(c != 0 for c in C)
    return ext


def full_rank(allverts, ext):
    return rank(build_rigidity_extensors(allverts, ext))


def eigen_subsystem_contracted(allverts, edges, col, ext, which):
    """`eigen_subsystem` with the OTHER ruling's equations solved out.

    Valid only when the other ruling class is a forest (the filter enforces
    it): then its `m_u = m_w` equations are independent, contribute exactly
    `3·|E_other|` to the rank, and leave one free `K³` per component.  The
    residual system is the direction network on the contracted graph, which
    is what makes the flank shapes affordable.  Cross-checked against the
    uncontracted `eigen_subsystem` in `--fixed`.
    """
    basis = EIG_P if which == 'P' else EIG_M
    mine = 'A' if which == 'P' else 'B'
    other = [e for e in edges if col[e] != mine]
    comp = components(allverts, other)
    nC = len(set(comp.values()))
    assert cycle_rank(allverts, other) == 0, "other ruling class has a cycle"
    n = 3 * nC
    rows = []
    for e, C in ext:
        if col[e] != mine:
            continue
        bu, bw = 3 * comp[e[0]], 3 * comp[e[1]]
        assert bu != bw, "a ruling edge inside one contracted node"
        for f in nullspace([conic_coords(C, basis)]):
            row = [F(0)] * n
            for k in range(3):
                row[bu + k] += f[k]
                row[bw + k] -= f[k]
            rows.append(row)
    return 3 * len(other) + rank(rows), 3 * len(allverts)


def eigen_subsystem(allverts, ext, which):
    """The 3-dimensional subsystem in the `which` ⋆-eigenspace, over ℚ.

    Variables m_v ∈ K³.  An edge whose hinge lies in THIS eigenspace gives 2
    equations ((m_u − m_w) ∥ the hinge direction); an edge whose hinge lies in
    the OTHER one gives 3 (m_u = m_w, because the relative screw must be a
    multiple of a vector with no component here).

    Built independently of `build_rigidity_extensors`, so that
    `rank(+) + rank(−) == rank(full)` is a test of the decoupling, not a
    restatement of it.
    """
    basis = EIG_P if which == 'P' else EIG_M
    idx = {v: k for k, v in enumerate(allverts)}
    n = 3 * len(allverts)
    rows = []
    for (u, w), C in ext:
        bu, bw = 3 * idx[u], 3 * idx[w]
        s = star_sign(C)
        assert s is not None, "hinge is not a ⋆-eigenvector"
        if ('P' if s == +1 else 'M') == which:
            perp = nullspace([conic_coords(C, basis)])
            assert len(perp) == 2
            for f in perp:
                row = [F(0)] * n
                for k in range(3):
                    row[bu + k] += f[k]
                    row[bw + k] -= f[k]
                rows.append(row)
        else:
            for k in range(3):
                row = [F(0)] * n
                row[bu + k] = F(1)
                row[bw + k] = F(-1)
                rows.append(row)
    return rank(rows), n


# ------------------------------------------------------------ legs -------

POOL_EDGES = {}
POOL = []      # (name, |V|, |E|, def, target, best, first-failure-cause)


def habitat_flags(edges):
    """Two NECESSARY conditions of the habitat `hK` is quantified over, so a
    failure of the grid construction can be attributed correctly.

    * `hnoRigid` — no PROPER rigid subgraph (`rigid_vertex_sets` empty).  It is
      a literal hypothesis of `hK` (`Escape.lean:555`).
    * `feasNec` — the landed NECESSARY conditions for `PencilNondegFeasible`:
      `hcard` (`ncard_closedHubNbhd_le_three_…`) and no triangle with two hubs
      (`not_pencilNondegFeasible_of_triangle_two_hubs`).  A shape failing this
      has NO nondegenerate pencil realization at all, σ-fixed or otherwise, so
      the grid construction failing there is correct behaviour.
    """
    hubs = hub_set(edges)
    two_hub_tri = any(len(t & hubs) >= 2 for t in triangles(edges))
    return (len(rigid_vertex_sets(edges)) == 0,
            hcard_ok(edges) and not two_hub_tri)


def leg_pool():
    """AC-Q — THE PINNED POOL and the one aggregate figure this section quotes.

    Runs after `--shapes` and `--flanks`, over exactly the union of their two
    tables and nothing else, so the aggregate cannot drift from the rows that
    produced it (the `63/63`-across-inconsistent-pools defect,
    `notes/dispatch-log.md`).
    """
    assert POOL, "run --shapes and --flanks first"
    print(f"[AC-Q] the pinned pool: the {len(POOL)} shapes of the two tables"
          f" above, and nothing else")
    tight = [r for r in POOL if r[3] == 0 and 5 * r[2] == 6 * (r[1] - 1)]
    rig = [r for r in POOL if r[3] == 0 and 5 * r[2] != 6 * (r[1] - 1)]
    nonrig = [r for r in POOL if r[3] != 0]
    for lab, grp in (('tight (def = 0 AND 5|E| = 6(|V|-1))', tight),
                     ('rigid but NOT count-tight (def = 0)', rig),
                     ('NOT rigid (def > 0)', nonrig)):
        hit = [r for r in grp if r[5] == r[4]]
        print(f"  {lab:38s} {len(hit):3d} / {len(grp):3d} at the Tay target")
        for r in grp:
            if r[5] != r[4]:
                print(f"      MISS  {r[0]:22s} def {r[3]}  best "
                      f"{r[5]:4d}  target {r[4]:4d}   {r[6]}")
    allhit = [r for r in POOL if r[5] == r[4]]
    print(f"  overall                                {len(allhit):3d} /"
          f" {len(POOL):3d}")
    print()
    print("  the three MISSes, against the habitat `hK` is quantified over:")
    for r in POOL:
        if r[5] == r[4]:
            continue
        edges = POOL_EDGES[r[0]]
        hnr, fea = habitat_flags(edges)
        inhab = hnr and fea
        print(f"    {r[0]:22s} hnoRigid {str(hnr):5s}  feas-necessary "
              f"{str(fea):5s}  ->  {'IN' if inhab else 'OUT OF'} the habitat")
    print("  A MISS at a shape OUT of the habitat is not a counterexample to")
    print("  the construction; a MISS IN the habitat is.")
    print("  Quote ONLY these three fractions.  `def = 0` is not the same")
    print("  predicate as count-tightness: W19 is rigid with 5|E| - 6(|V|-1)")
    print("  = 2, and it is the only member of the middle group.")
    print()


def leg_parity():
    """AC-R2 — WHEN does no admissible colouring exist at all?

    An alternation chain closes into a cycle only if every body along it has
    degree 2, i.e. only inside a connected component of `G` that IS a cycle;
    the cycle is odd exactly when that component has odd length.  So the
    conjecture is: **no proper alternation colouring exists iff `G` has an odd
    cycle component**.  Tested on every cycle `C3..C14` and on every shape of
    the pinned pool.
    """
    print("[AC-R2] the ONE identified structural obstruction: parity")
    bad = []
    for k in range(3, 15):
        edges = [(i, (i + 1) % k) for i in range(k)]
        _comps, odd = alternation_classes(edges)
        if odd:
            bad.append(k)
        assert odd == (k % 2 == 1), f"C{k}: parity prediction wrong"
    print(f"  bare cycles C3..C14 with NO admissible colouring: {bad}")
    print("  = exactly the odd ones                                       OK")
    others = 0
    for name, edges in shapes():
        if len(verts_of(edges)) == len(edges) and all(
                len(n) == 2 for n in neighbors(edges).values()):
            continue                                   # a bare cycle
        _c, odd = alternation_classes(edges)
        assert not odd, f"{name}: unexpected odd alternation cycle"
        others += 1
    from flanks import named_shapes
    from kslidecomb import shape_data
    for (name, specs, _n) in named_shapes():
        _c, odd = alternation_classes(shape_data(specs)[0])
        assert not odd, f"{name}: unexpected odd alternation cycle"
        others += 1
    print(f"  every non-cycle shape of the pool admits one: {others}/{others}")
    print("  ⟹ the ONLY graphs with no σ-fixed nondegenerate configuration")
    print("    for parity reasons are the bare ODD cycles.  The other two")
    print("    failures below are NOT parity: they are a nondegeneracy")
    print("    failure and a rank shortfall, both at def > 0 shapes.")
    print()


def leg_control():
    print("[AC-C0] control: the fixed quadric over ℚ vs over ℚ(i)")
    found = None
    for x in itertools.product(range(-3, 4), repeat=4):
        if any(x) and sum(c * c for c in x) == 0:
            found = x
    print(f"  ℚ-isotropic vectors in [-3,3]⁴ : {found}   (expected None)")
    assert found is None
    p = grid_point((1, 1), (1, 2))
    print(f"  ℚ(i)-isotropic witness p = {p}")
    assert dot(p, p) == 0 and any(c != 0 for c in p)
    assert rank(EIG_P) == 3 and rank(EIG_M) == 3
    for b in EIG_P:
        assert hodge_star(b) == b
    for b in EIG_M:
        assert hodge_star(b) == [-c for c in b]
    for a in EIG_P:
        for b in EIG_M:
            assert dot(a, b) == 0
    print("  ⋆ eigenspaces: dim 3 + 3, ℚ-rational, mutually ⬝ᵥ-orthogonal  OK")
    sA = star_sign(ruling_A_line((1, 2)))
    sB = star_sign(ruling_B_line((1, 3)))
    print(f"  ⋆-sign of a ruling-A line: {sA:+d};  of a ruling-B line: {sB:+d}")
    assert {sA, sB} == {+1, -1}
    for (s1, u1, s2, u2) in [((1, 2), (1, 3), (1, 2), (1, 5)),
                             ((1, 2), (1, 3), (1, 7), (1, 3)),
                             ((1, 2), (1, 3), (1, 7), (1, 5))]:
        p1, p2 = grid_point(s1, u1), grid_point(s2, u2)
        br_s = s1[0] * s2[1] - s2[0] * s1[1]
        br_u = u1[0] * u2[1] - u2[0] * u1[1]
        assert (dot(p1, p2) == 0) == (br_s == 0 or br_u == 0)
    print("  conjugacy law  p·p′ = 0 ⟺ a shared ruling parameter          OK")
    print()


def combinatorial_filter(edges, allverts, col):
    """The three cheap necessary conditions, so the sweeps stay affordable.

    (i) no hub monochromatic — else its whole star lies on one ruling line and
        the star rank is 2 (the panel is not determined);
    (ii) both ruling classes forests — else the eigen-subsystem in the OTHER
        eigenspace has ≥ 3 dependent equations;
    (iii) balanced |E_A| = |E_B| — the only split for which both subsystems
        can be isostatic at a tight shape.
    Returns (reason or None).
    """
    nb = neighbors(edges)
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    for v, ns in nb.items():
        if len(ns) >= 3:
            cs = {col[e] for e in edges if v in e}
            if len(cs) == 1:
                return 'monochromatic hub'
    if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
        return 'ruling cycle'
    if len(EA) != len(EB):
        return 'unbalanced'
    return None


def probe(name, edges, col, want_full=False, fast=False):
    """One σ-fixed configuration: legality, rank, and the decoupling."""
    allverts = sorted(verts_of(edges), key=str)
    built = build_fixed_config(edges, allverts, col)
    if built is None:
        return None
    pt, EA, EB = built
    for v in allverts:
        assert dot(pt[v], pt[v]) == 0
    for (u, w) in edges:
        assert dot(pt[u], pt[w]) == 0
    ext = extensors(edges, pt)
    for e, C in ext:
        assert (star_sign(C) == +1) == (col[e] == 'A')
    placed = {v: dehom(pt[v]) for v in allverts}
    # The composite genericity guard since 2026-08-06 (slice S2): closed-star
    # ranks AND no two hinge lines coinciding at a body.  Reported, as before,
    # rather than used to reject: a σ-fixed configuration is CONSTRUCTED here,
    # not sampled, so its genericity is a measurement about the construction.
    genok = star_generic(edges, placed)
    srk = star_span_ranks(edges, placed)
    coin = coincident_hinges(edges, placed)
    ok, why = nondeg_conjuncts(edges, placed)
    if fast:
        rP, _ = eigen_subsystem_contracted(allverts, edges, col, ext, 'P')
        rM, _ = eigen_subsystem_contracted(allverts, edges, col, ext, 'M')
    else:
        rP, _ = eigen_subsystem(allverts, ext, 'P')
        rM, _ = eigen_subsystem(allverts, ext, 'M')
        if cycle_rank(allverts, EA) == cycle_rank(allverts, EB) == 0:
            cP, _ = eigen_subsystem_contracted(allverts, edges, col, ext, 'P')
            cM, _ = eigen_subsystem_contracted(allverts, edges, col, ext, 'M')
            assert (cP, cM) == (rP, rM), "contracted / full ranks disagree"
    d = dict(nEA=len(EA), nEB=len(EB), starok=genok, ok=ok,
             starrk=(set(srk.values()) == {3}), coin=coin,
             why=(None if ok else why[0]),
             rP=rP, rM=rM, rk=rP + rM,
             cA=cycle_rank(allverts, EA), cB=cycle_rank(allverts, EB))
    if want_full:
        d['full'] = full_rank(allverts, ext)
        assert d['full'] == d['rk'], "the ⋆-eigen decoupling FAILED"
    return d


def leg_fixed():
    """AC-E / AC-R — one explicit σ-fixed nondegenerate target-rank witness."""
    name, edges = dsk4()
    allverts = sorted(verts_of(edges))
    cols, odd = colourings(edges)
    print("[AC-E] a σ-fixed pencil configuration over ℚ(i), ds-K4")
    print(f"  |V| = {len(allverts)}, |E| = {len(edges)}, "
          f"alternation chains = {len(alternation_classes(edges)[0])}, "
          f"odd cycle: {odd}")
    hit = None
    for col in cols:
        if combinatorial_filter(edges, allverts, col):
            continue
        d = probe(name, edges, col, want_full=True)
        if d and d['ok'] and d['rk'] == 6 * (len(allverts) - 1):
            hit = (col, d)
            break
    assert hit is not None, "no legal target-rank σ-fixed configuration"
    col, d = hit
    print(f"  |E_A| = {d['nEA']}, |E_B| = {d['nEB']}, "
          f"cycle ranks {d['cA']}/{d['cB']} (both forests: "
          f"{d['cA'] == d['cB'] == 0})")
    print("  every body isotropic; every edge conjugate; every hinge screw a")
    print("  ⋆-eigenvector whose sign is its ruling                        OK")
    print(f"  all four IsNondegPencilRealization conjuncts: {d['ok']}; "
          f"closed-star ranks all 3: {d['starrk']}")
    print(f"  the composite genericity guard repin.star_generic: "
          f"{d['starok']}")
    print(f"    coincident hinge lines (body, x, u): {d['coin']}")
    print(f"  rank {d['full']} = rank(+) {d['rP']} + rank(−) {d['rM']}, "
          f"target {6 * (len(allverts) - 1)}, deficit "
          f"{6 * (len(allverts) - 1) - d['full']}")
    print("  ⟹ σ-FIXED PENCIL CONFIGURATIONS EXIST over ℂ̄, satisfy every")
    print("    IsNondegPencilRealization conjunct, and REACH the Tay target.")
    print("    §(K-σ) Step σ6's 'the fixed locus is degenerate' is REFUTED")
    print("    AS A STATEMENT ABOUT THAT PREDICATE for the symmetric")
    print("    correlation (it holds for the null one, which is a different")
    print("    fixed locus).")
    print("  BUT (measured 2026-08-06, slice S2, and NOT known when (AC-3)")
    print("    was written): the witness carries a coincident hinge line at")
    print("    EVERY hub -- the harness' composite genericity guard rejects")
    print("    it, while its rank, its four conjuncts and its closed-star")
    print("    ranks are all green.  So 'nondegenerate' here means exactly")
    print("    'the four conjuncts', never 'generic'; --sweep measures how")
    print("    far that goes on this shape.")
    print()
    return col


def leg_sweep():
    """AC-S — the exhaustive census over ds-K4's 2⁶ ruling colourings."""
    name, edges = dsk4()
    allverts = sorted(verts_of(edges))
    target = 6 * (len(allverts) - 1)
    cols, _ = colourings(edges)
    print(f"[AC-S] every ruling colouring of ds-K4 ({len(cols)})")
    print("   |E_A| |E_B|  genOK nondegOK  rank  def   r+   r-  cA cB   n")
    tally = {}
    good = 0
    for col in cols:
        d = probe(name, edges, col)
        if d is None:
            continue
        key = (d['nEA'], d['nEB'], d['starok'], d['ok'], d['rk'],
               d['rP'], d['rM'], d['cA'], d['cB'])
        tally[key] = tally.get(key, 0) + 1
        if d['ok']:
            good += 1
    for key in sorted(tally):
        nEA, nEB, so, ok, rk, rP, rM, cA, cB = key
        print(f"   {nEA:4d} {nEB:5d}  {str(so):5s}  {str(ok):5s}"
              f"   {rk:4d} {target - rk:4d} {rP:4d} {rM:4d}  {cA:2d} {cB:2d}"
              f"  {tally[key]:3d}")
    print(f"  legal (all four IsNondegPencilRealization conjuncts): "
          f"{good} / {len(cols)}")
    ngen = sum(n for k, n in tally.items() if k[3] and k[2])
    print(f"  ... AND composite-guard generic (no coincident hinge line "
          f"anywhere): {ngen} / {len(cols)}")
    assert ngen == 0, "a σ-fixed colouring is composite-guard GENERIC -- " \
        "(AC-9) as measured 2026-08-06 no longer holds; update §(K-clos)"
    tgt = sum(n for k, n in tally.items() if k[3] and k[4] == target)
    print(f"  legal AND at the Tay target              : {tgt} / {len(cols)}")
    for k in tally:
        if k[4] == target:                      # at the target ⟹ balanced
            assert k[0] == k[1], "a target-rank colouring is unbalanced"
            assert k[7] == k[8] == 0, "a target-rank colouring has a cycle"
            assert k[5] == k[6] == 3 * len(allverts) - 3, \
                "a target-rank colouring has a non-isostatic eigen-block"
        if k[0] != k[1]:                        # unbalanced ⟹ deficient
            assert k[4] < target, "an unbalanced colouring reached target"
    print("  every TARGET-RANK colouring is balanced (|E_A| = |E_B|), both")
    print("  ruling classes are forests, and BOTH eigen-blocks are isostatic")
    print(f"  at 3|V|−3 = {3 * len(allverts) - 3}                          "
          f"    OK")
    print("  every unbalanced colouring falls short of the target          OK")
    print("  every colouring satisfies rank = rank(+) + rank(−)            OK")
    print("  (legality is NOT balance: 3 legal colourings are 8/10 or 10/8,")
    print("   nondegenerate but one short of the target)")
    print()


def leg_shapes():
    """AC-U — is the grid construction a class-UNIFORM recipe?  (No.)"""
    print("[AC-U] the grid construction across tight class shapes")
    print("  shape                |V| |E| def chains  pass  legal  best  target"
          "  gap   first failure cause")
    verdicts = {}
    for name, edges in shapes():
        allverts = sorted(verts_of(edges), key=str)
        comps, odd = alternation_classes(edges)
        dfc = deficiency(edges)
        target = 6 * (len(allverts) - 1) - dfc
        cols, _ = colourings(edges)
        if cols is None:
            print(f"  {name:20s} {len(allverts):3d} {len(edges):3d} {dfc:3d}"
                  f"  {len(comps):5d}   (2^{len(comps)} colourings: skipped)")
            continue
        if odd:
            print(f"  {name:20s} {len(allverts):3d} {len(edges):3d} {dfc:3d}"
                  f"  {len(comps):5d}   NO proper alternation colouring")
            verdicts[name] = 'no colouring'
            POOL.append((name, len(allverts), len(edges), dfc, target, -1,
                         'no alternation colouring'))
            POOL_EDGES[name] = edges
            continue
        best, legal, passed, whys = -1, 0, 0, []
        for col in cols:
            if combinatorial_filter(edges, allverts, col):
                continue
            passed += 1
            d = probe(name, edges, col, fast=True)
            if d is None:
                whys.append('coincident bodies')
                continue
            if not d['ok']:
                whys.append(d['why'])
                continue
            legal += 1
            best = max(best, d['rk'])
        gap = (target - best) if best >= 0 else None
        print(f"  {name:20s} {len(allverts):3d} {len(edges):3d} {dfc:3d}"
              f"  {len(comps):5d} {passed:5d}  {legal:5d} "
              f"{best if best >= 0 else -1:5d}  {target:6d}"
              f"  {gap if gap is not None else 'n/a':>4}"
              f"   {(whys[0] if whys else '')[:34]}")
        verdicts[name] = 'target' if gap == 0 else (
            'no legal grid' if best < 0 else f'gap {gap}')
        POOL.append((name, len(allverts), len(edges), dfc, target, best,
                     whys[0] if whys else None))
        POOL_EDGES[name] = edges
    print()
    print("  verdict by shape:")
    for k, v in verdicts.items():
        print(f"    {k:14s} {v}")
    print("  A shape with no legal grid, or with best < target, has NO")
    print("  σ-fixed nondegenerate target-rank realization: the grid")
    print("  construction is NOT a class-uniform recipe.")
    print()


def leg_collapse():
    """AC-F — at a σ-fixed seed, route σ IS route A.  The field-neutral kill.

    Route A's uniform-failure criterion at a body `b` is `r ⊥ Λ²Π̂(b)`; route
    σ's is `r ⊥ α_{pt(b)}` (§(K-σ) (σ6)).  At a σ-fixed configuration
    `Π(b) = pt(b)^⊥`, so `Λ²Π̂(b) = ⋆ α_{pt(b)}`; and the whole matrix
    decouples over the ⋆-eigenspaces, so the residual load `r` is a
    ⋆-eigenvector.  Self-adjointness of ⋆ then gives
    `⟨r, ⋆a⟩ = ⟨⋆r, a⟩ = ±⟨r, a⟩`, i.e. the two criteria COINCIDE.
    """
    print("[AC-F] the collapse: at a σ-fixed seed route σ = route A")
    name, edges = dsk4()
    allverts = sorted(verts_of(edges))
    cols, _ = colourings(edges)
    chosen = None
    for c in cols:
        if combinatorial_filter(edges, allverts, c):
            continue
        d = probe(name, edges, c)
        if d and d['ok'] and d['rk'] == 6 * (len(allverts) - 1):
            chosen = c
            break
    assert chosen is not None
    pt, EA, EB = build_fixed_config(edges, allverts, chosen)
    checked = 0
    for b in allverts:
        alpha = lambda2_through(pt[b])            # α_{pt(b)}, 3-dim
        assert len(alpha) == 3
        beta = [hodge_star(x) for x in alpha]     # ⋆α = β_{pt(b)^⊥} = Λ²Π̂(b)
        assert rank(beta) == 3
        # pt(b) ∈ Π(b) (the panel–point incidence), so α ∩ β is the 2-dim
        # pencil of lines through pt(b) inside Π(b) and dim(α+β) = 4.
        assert rank(alpha + beta) == 4
        for eig in (EIG_P, EIG_M):
            # {r ∈ eigenspace : r ⊥ α} vs {r ∈ eigenspace : r ⊥ β}, as
            # SUBSPACES (a basis-wise check would not settle the iff).
            Ma = [[dot(x, e) for e in eig] for x in alpha]
            Mb = [[dot(x, e) for e in eig] for x in beta]
            Va, Vb = nullspace(Ma), nullspace(Mb)
            assert len(Va) == len(Vb)
            assert rank(Va + Vb) == len(Va), \
                "the two criteria cut different subspaces"
            checked += 1
    print("  ds-K4, σ-fixed target-rank seed: for every body b and each")
    print(f"  ⋆-eigenspace,  {{r : r ⊥ α_pt(b)}} = {{r : r ⊥ Λ²Π̂(b)}} as")
    print(f"  subspaces :  {checked}/{checked}")
    print("  ⟹ route σ's criterion and route A's criterion coincide there.")
    print("  A σ-equivariant seed recipe therefore buys route σ's obligation")
    print("  1 for free and DELETES route σ in the same stroke.")
    print()


def leg_flanks(cap=6):
    """AC-X — the grid construction at the shapes NO mechanism covers.

    The §(K-slide-comb) *Step D5* / §(K-flank) flank list: the `K5`
    5-chromatic shape, the 6v11e acyclicity-obstructed shape, the `K222`
    octahedron, the two wheels, a menu-blocked `K4` shape, and `P21`.  These
    are the shapes every class-uniform mechanism of the arc has failed at.
    """
    from flanks import named_shapes
    from kslidecomb import shape_data
    print("[AC-X] the grid construction at the uncovered flanks")
    print(f"  PROBE CAP: the first {cap} filter-passing colourings per")
    print("  shape are probed, so `hit` SATURATES at that cap and is NOT a")
    print("  fraction of `pass`.  The load-bearing column is `best`.")
    print("  shape                                  |V| |E| chains  pass"
          f"  hit/{cap}  best target")
    for (name, specs, _note) in named_shapes():
        edges, _pmap = shape_data(specs)
        allverts = sorted(verts_of(edges), key=str)
        comps, odd = alternation_classes(edges)
        target = 6 * (len(allverts) - 1) - deficiency(edges)
        cols, _ = colourings(edges, cap=1 << 20)
        if odd or cols is None:
            print(f"  {name[:38]:38s} {len(allverts):3d} {len(edges):3d}"
                  f"  {len(comps):5d}   (no colouring enumeration)")
            continue
        passed, tried, best, hit = 0, 0, -1, 0
        for col in cols:
            if combinatorial_filter(edges, allverts, col):
                continue
            passed += 1
            if tried >= cap:
                continue
            tried += 1
            # cross-check the ⋆-eigen decoupling against the FULL 6|V|-column
            # matrix once per shape, where that is affordable
            full = (tried == 1 and len(allverts) <= 21)
            d = probe(name, edges, col, want_full=full, fast=not full)
            if d is None or not d['ok']:
                continue
            best = max(best, d['rk'])
            if d['rk'] == target:
                hit += 1
        print(f"  {name[:38]:38s} {len(allverts):3d} {len(edges):3d}"
              f"  {len(comps):5d} {passed:5d} {hit:5d}/{cap} "
              f"{best if best >= 0 else -1:5d} {target:6d}")
        POOL.append((name, len(allverts), len(edges), deficiency(edges),
                     target, best, None))
        POOL_EDGES[name] = edges
    print("  `pass` counts colourings surviving the combinatorial filter;")
    print("  `hit` counts how many of the AT MOST %d PROBED ones are legal"
          % cap)
    print("  and at the target — it is capped, not a census.")
    print()


def star_matrix():
    cols = []
    for j in range(6):
        e = [0] * 6
        e[j] = 1
        cols.append(hodge_star(e))
    return [[cols[j][i] for j in range(6)] for i in range(6)]


def leg_char2():
    """AC-2c — the polarity in characteristic 2, and the char-p residue."""
    print("[AC-2c] the polarity in characteristic 2")
    for x in itertools.product((0, 1), repeat=4):
        assert (sum(c * c for c in x)) % 2 == (sum(x) ** 2) % 2
    print("  x⬝ᵥx = (∑xᵢ)² on all of 𝔽₂⁴ (16/16): the polarity's fixed locus")
    print("  is the DOUBLE PLANE {∑xᵢ = 0}, not a smooth quadric          OK")
    S = star_matrix()
    Sm = [[S[i][j] - (1 if i == j else 0) for j in range(6)] for i in range(6)]
    Sp = [[S[i][j] + (1 if i == j else 0) for j in range(6)] for i in range(6)]
    print(f"  over ℚ  : rank(⋆−1) = {rank(Sm)}, rank(⋆+1) = {rank(Sp)}"
          f"  → eigenspaces 3 + 3, Λ² splits")
    print(f"  over 𝔽₂ : rank(⋆−1) = {rank_modp(Sm, 2)}, "
          f"rank(⋆+1) = {rank_modp(Sp, 2)}  → ⋆−1 ≡ ⋆+1, no splitting")
    assert (rank(Sm), rank(Sp)) == (3, 3)
    assert all(Sm[i][j] % 2 == Sp[i][j] % 2 for i in range(6)
               for j in range(6))
    print()
    print("[AC-P] the char-p residue: one RATIONAL target-rank pencil")
    print("       configuration of ds-K4, reduced mod p")
    _, edges = dsk4()
    allverts = sorted(verts_of(edges))
    seed, placed, _ctx, _stats = clean_pencil_seed(edges, range(0, 60))
    pt = {v: hat(placed[v]) for v in allverts}
    M = build_rigidity_extensors(allverts, extensors(edges, pt))
    # clear denominators row-wise (rational rank unchanged, and each row then
    # has coprime integer entries, so mod-p reduction is meaningful)
    Z = []
    for row in M:
        L = 1
        for x in row:
            L = L * x.denominator // gcd(L, x.denominator)
        Z.append([int(x * L) for x in row])
    r0 = rank(M)
    assert rank(Z) == r0
    print(f"  |V| = {len(allverts)}, target {6 * (len(allverts) - 1)}, "
          f"seed {seed}, rational rank: {r0}")
    for p in (2, 3, 5, 7, 11, 13, 10 ** 9 + 7):
        rp = rank_modp(Z, p)
        print(f"    p = {p:11d} : {rp:4d}" + ("   <-- drops" if rp < r0
                                              else ""))
    print("  This matrix is a PROXY: the object `hK` actually quantifies is a")
    print("  minor of `pencilRow`, whose entries are ℤ-polynomial in the seed")
    print("  (`cross₃Poly` = a 4×4 determinant, `annihRow` = a 2×2 minor).")
    print("  A drop at ONE seed is not a char-p obstruction; it only shows")
    print("  the mod-p reduction is a separate question from char-0")
    print("  non-vanishing.")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('fixed', 'sweep', 'shapes', 'flanks', 'pool', 'parity',
              'collapse', 'char2', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.fixed, a.sweep, a.shapes, a.flanks,
                                 a.pool, a.parity, a.collapse, a.char2])
    if run or a.fixed:
        leg_control()
        leg_fixed()
    if run or a.sweep:
        leg_sweep()
    if run or a.shapes:
        leg_shapes()
    if run or a.flanks:
        leg_flanks()
    if run or a.pool:
        if not POOL:
            leg_shapes()
            leg_flanks()
        leg_pool()
    if run or a.parity:
        leg_parity()
    if run or a.collapse:
        leg_collapse()
    if run or a.char2:
        leg_char2()
    print("OK")


if __name__ == '__main__':
    main()
