"""
Phase 39 (K-bare) numerics gate — common infrastructure.

Model (verified against landed Lean source 2026-07-30, this recon):
  * `HasPencilRealization K 3 G` (Molecule/Pencil/Statement.lean:103):
      exists F, normal, point with HasPencilPanelRealization G F normal point
      and finrank span(F.rigidityRows) = 6(|V|-1) - deficiency(G,3).
  * HasPencilPanelRealization (Statement.lean:88): coplanar panel realization
      (normal v != 0 on V(G); supportExtensor e != 0 for ALL e; each link's
      extensor ExtensorInPanel both endpoint normals), point v != 0,
      point v . normal v = 0, each link's extensor ExtensorThroughPoint both
      endpoint points.
  * rigidityRows (RigidityMatrix/Basic.lean:654): per link e=uv, all r in
      dualAnnihilator(span{C_e}) acting as S |-> r(S u - S v).  In the
      standard dual basis this is: 5 rows per edge = basis of {w : w . C_e = 0}
      (coordinate dot on the 6 Plucker coords), +w in u-block, -w in v-block.
  * deficiency (Molecular/Deficiency.lean:262/273): max over partitions P of
      6(|P|-1) - 5 d(P), D = bodyBarDim 3 = 6, mult 5.

Witness class sampled here (exact-Q molecular pencil configurations):
  points p : V -> Q^3, point v := hat(p v) = (p,1), C_e := hat(p u) ^ hat(p v),
  normal v := any nonzero solution of n . hat(p w) = 0 for all w in the closed
  star of v.  Such (F, normal, point) satisfies every HasPencilPanelRealization
  conjunct provided (a) adjacent points are distinct (C_e != 0, and the wedge
  witness makes ExtensorInPanel/ThroughPoint verbatim), (b) each closed star
  is coplanar (the nullspace is nonzero).  Both are checked per sample.

Rank certification: for ANY framework and ANY partition P,
  rank <= 6(|V|-1) - partitionDef(P)   (within-part rows kill part-constants;
  crossing rows are <= 5 per edge), hence rank <= target.  Therefore
  rank mod p == target  ==>  exact rational rank == target (mod-p rank is a
  lower bound for rational rank).  Shortfalls are re-checked in exact Q.
"""
from fractions import Fraction as F
import random
from array import array

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

# Exact-Q linear algebra + Plucker primitives + 1-arg `neighbors`: canonical
# home is `notes/scripts/exactcore.py` (this file used to reimplement them
# alongside `escape/pencil_escape.py`).  Re-exported here under exactly the
# names this module used to define -- `rank_exact` is `exactcore.rank` -- so
# every `from kbare_common import *` consumer sees an unchanged namespace.
from exactcore import (rref, nullspace, dot, PL, wedge2, hat,   # noqa: E402,F401
                       perp_basis, neighbors, rank as rank_exact)

P61 = (1 << 61) - 1  # Mersenne prime

# ---------------- exact-Q linear algebra ----------------

def rank_modp(M, p=P61):
    """Rank over GF(p).  Lower bound for rational rank (equality generically)."""
    A = []
    for row in M:
        r = []
        for x in row:
            if isinstance(x, F):
                r.append(x.numerator % p * pow(x.denominator % p, p - 2, p) % p)
            else:
                r.append(x % p)
        A.append(r)
    if not A:
        return 0
    rows, cols = len(A), len(A[0])
    rk = 0
    for c in range(cols):
        pr = None
        for i in range(rk, rows):
            if A[i][c]:
                pr = i
                break
        if pr is None:
            continue
        A[rk], A[pr] = A[pr], A[rk]
        inv = pow(A[rk][c], p - 2, p)
        A[rk] = [x * inv % p for x in A[rk]]
        for i in range(rows):
            if i != rk and A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * b) % p for a, b in zip(A[i], A[rk])]
        rk += 1
        if rk == rows:
            break
    return rk

# ---------------- graph utilities ----------------

def verts_of(edges):
    vs = set()
    for u, w in edges:
        vs.add(u)
        vs.add(w)
    return sorted(vs, key=str)

def degrees(edges):
    d = {}
    for u, w in edges:
        d[u] = d.get(u, 0) + 1
        d[w] = d.get(w, 0) + 1
    return d

def is_connected(edges, verts=None):
    if verts is None:
        verts = verts_of(edges)
    if not verts:
        return True
    nb = neighbors(edges)
    seen = {verts[0]}
    stack = [verts[0]]
    while stack:
        x = stack.pop()
        for y in nb.get(x, ()):
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == len(verts)

def is_2ec(edges):
    """Connected and no bridge (min edge-cut >= 2), by edge-deletion probe."""
    verts = verts_of(edges)
    if not is_connected(edges, verts):
        return False
    for i in range(len(edges)):
        rest = edges[:i] + edges[i + 1:]
        if not is_connected(rest, verts):
            return False
    return True

def closed_hub_nbhds(edges):
    """closedHubNbhd v = {w : deg w >= 3 and (w = v or w ~ v)} (Motive.lean:82).
    Returns {v: ncard}."""
    deg = degrees(edges)
    nb = neighbors(edges)
    out = {}
    for v in verts_of(edges):
        s = set()
        if deg.get(v, 0) >= 3:
            s.add(v)
        for w in nb.get(v, ()):
            if deg.get(w, 0) >= 3:
                s.add(w)
        out[v] = len(s)
    return out

# ---------------- exact deficiency (D = 6, mult = 5) ----------------

def subset_f_table(edges):
    """f(W) = 5|E(W)| - 6(|W|-1) for every subset W (bitmask index).
    Identity: partitionDef(P) = def_finest + sum_parts f(part),
    def_finest = 6(|V|-1) - 5|E|.  Requires a SIMPLE graph (uses adjacency
    bitmasks; parallel edges would need multiplicity-aware counting)."""
    verts = verts_of(edges)
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    # simplicity check (no parallel, no loop):
    seen = set()
    for u, w in edges:
        assert u != w, "loop present"
        key = frozenset((u, w))
        assert key not in seen, "parallel edge present"
        seen.add(key)
    adj = [0] * n
    for u, w in edges:
        adj[idx[u]] |= 1 << idx[w]
        adj[idx[w]] |= 1 << idx[u]
    N = 1 << n
    E_in = array('i', [0]) * N
    low = [0] * N
    for S in range(1, N):
        v = (S & -S).bit_length() - 1
        S0 = S & (S - 1)
        E_in[S] = E_in[S0] + bin(adj[v] & S0).count('1')
    return verts, E_in

def exact_deficiency(edges, report=False):
    """Exact deficiency(G, 3) = max_P [6(|P|-1) - 5 d(P)] via the part-sum
    identity.  Returns (def, info)."""
    verts, E_in = subset_f_table(edges)
    n = len(verts)
    m = len(edges)
    N = 1 << n
    full = N - 1
    def_finest = 6 * (n - 1) - 5 * m
    pos = []          # subsets with f > 0 (candidates to merge into parts)
    maxf_proper = None
    zero_proper = 0
    for S in range(1, N):
        k = bin(S).count('1')
        if k < 2:
            continue
        f = 5 * E_in[S] - 6 * (k - 1)
        if S != full:
            if maxf_proper is None or f > maxf_proper:
                maxf_proper = f
            if f == 0:
                zero_proper += 1
        if f > 0:
            pos.append((S, f))
    f_full = 5 * E_in[full] - 6 * (n - 1)
    # max over partitions of sum f(parts): singletons contribute 0, so this is
    # the max-weight packing of DISJOINT positive-f subsets.
    if not pos:
        best = 0
    else:
        pos.sort(key=lambda t: -t[1])
        best = 0
        def bnb(i, used, acc):
            nonlocal best
            if acc + sum(f for S, f in pos[i:]) <= best:
                return
            if i == len(pos):
                best = max(best, acc)
                return
            S, f = pos[i]
            if not (S & used):
                bnb(i + 1, used | S, acc + f)
            bnb(i + 1, used, acc)
            best = max(best, acc)
        bnb(0, 0, 0)
    d = def_finest + best
    d = max(d, 0)  # trivial one-part partition witnesses 0
    info = {
        'def_finest': def_finest, 'f_full': f_full,
        'maxf_proper_ge2': maxf_proper, 'zero_f_proper_count': zero_proper,
        'n_positive_f_subsets': len(pos), 'packing_gain': best,
    }
    if report:
        print(f"    deficiency: |V|={n} |E|={m} def_finest={def_finest} "
              f"maxf(proper,|W|>=2)={maxf_proper} #f>0={len(pos)} "
              f"packing={best} => def={d}")
    return d, info

# ---------------- rigidity matrix ----------------

def build_rigidity(edges, pt):
    """5 rows/edge molecular body-hinge matrix; requires adjacent points
    distinct (asserts)."""
    V = verts_of(edges)
    idx = {v: k for k, v in enumerate(V)}
    ncol = 6 * len(V)
    rows = []
    for (u, w) in edges:
        assert pt[u] != pt[w], f"adjacent coincident points at edge {(u, w)}"
        Ce = wedge2(hat(pt[u]), hat(pt[w]))
        for wv in perp_basis(Ce):
            row = [F(0)] * ncol
            bu, bw = 6 * idx[u], 6 * idx[w]
            for k in range(6):
                row[bu + k] += wv[k]
                row[bw + k] -= wv[k]
            rows.append(row)
    return rows, len(V)

def pencil_rank(edges, pt, exact=False):
    rows, n = build_rigidity(edges, pt)
    rk = rank_exact(rows) if exact else rank_modp(rows)
    return rk, len(rows), n

# ---------------- pencil witness verification ----------------

def verify_pencil_witness(edges, pt):
    """Independently verify pt is a genuine molecular pencil configuration:
    per vertex, the closed-star hats admit a nonzero common normal.  Returns
    (ok, normals or violation)."""
    nb = neighbors(edges)
    normals = {}
    for v in verts_of(edges):
        star = [hat(pt[v])] + [hat(pt[u]) for u in nb.get(v, ())]
        ns = nullspace(star)
        if not ns:
            return False, ('no coplanar normal at', v)
        normals[v] = ns[0]
    for (u, w) in edges:
        if pt[u] == pt[w]:
            return False, ('coincident adjacent points', (u, w))
    return True, normals

# ---------------- gadget constructions ----------------

def spider(l1, l2, l3, center=True):
    """Hub triangle A,B,C joined by three subdivided arcs of lengths l1 (A-B),
    l2 (B-C), l3 (C-A); optional center Z with spokes to A, B, C.
    spider(6,6,6, center=True)  = the 19-vertex L6a theta counterexample.
    spider(5,5,5, center=True)  = G'_dang (the 17-vertex gadget's dangerous split).
    Returns (edges, meta) with meta naming hubs/arcs."""
    edges = []
    arcs = {}
    for (h1, h2, L, tag) in [('A', 'B', l1, 'ab'), ('B', 'C', l2, 'bc'),
                             ('C', 'A', l3, 'ca')]:
        prev = h1
        interior = []
        for i in range(1, L):
            v = f'{tag}{i}'
            edges.append((prev, v))
            interior.append(v)
            prev = v
        edges.append((prev, h2))
        arcs[tag] = interior
    if center:
        for h in ('A', 'B', 'C'):
            edges.append(('Z', h))
    return edges, {'hubs': ['A', 'B', 'C'], 'center': 'Z' if center else None,
                   'arcs': arcs}

def dangerous_gadget(L=5):
    """The 17-vertex feasible-but-dangerous gadget (design doc L6a block):
    path a-v-b, a joined to hubs x,y; x,y,b on a subdivided triangle of three
    length-L arcs.  L=5: |V|=17, |E|=19."""
    edges = []
    arcs = {}
    for (h1, h2, tag) in [('x', 'y', 'xy'), ('y', 'b', 'yb'), ('b', 'x', 'bx')]:
        prev = h1
        interior = []
        for i in range(1, L):
            w = f'{tag}{i}'
            edges.append((prev, w))
            interior.append(w)
            prev = w
        edges.append((prev, h2))
        arcs[tag] = interior
    edges += [('a', 'x'), ('a', 'y'), ('a', 'v'), ('v', 'b')]
    return edges, {'hubs': ['x', 'y', 'b', 'a'], 'arcs': arcs}

def split_off(edges, v, a, b):
    """G' = G.splitOff v a b: delete v (and its two edges va, vb), add fresh
    edge ab (Operations.lean:769 at a degree-2 v)."""
    out = [e for e in edges if v not in e]
    removed = len(edges) - len(out)
    assert removed == 2, f"v={v} does not have exactly two incident edges"
    out.append((a, b))
    return out

# ---------------- exact-Q random sampling helpers ----------------

def rint(rng, lo=-9, hi=9):
    return F(rng.randint(lo, hi))

def rvec3(rng):
    return [rint(rng) for _ in range(3)]

def rnonzero3(rng):
    while True:
        v = rvec3(rng)
        if any(x != 0 for x in v):
            return v

def plane_basis(nvec3):
    """Two independent directions orthogonal (Euclidean) to spatial normal.

    DEGENERATE, same defect as `localtest.plane_basis`: when a coordinate of
    `nvec3` is 0 the first two accepted directions are PARALLEL, so
    `point_in_plane3` samples a line.  This is that same construction cleared
    of denominators, hence a DIFFERENT scalar multiple — the two are NOT
    interchangeable, and merging them would move recorded figures.  Robust
    successor: `repin.robust_plane_basis`.  README *Divergences*."""
    basis = []
    for e in ([F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), F(0), F(1)]):
        d = [e[i] * dot(nvec3, nvec3) - dot(e, nvec3) * nvec3[i] for i in range(3)]
        if any(x != 0 for x in d):
            basis.append(d)
        if len(basis) == 2:
            return basis
    raise RuntimeError

def point_in_plane3(p0, nvec3, rng):
    b1, b2 = plane_basis(nvec3)
    s, t = rint(rng, -6, 6), rint(rng, -6, 6)
    den = rng.randint(1, 4)
    return [p0[i] + (s * b1[i] + t * b2[i]) / den for i in range(3)]

def normal4_through(hats, rng, tries=50):
    """Random nonzero 4-normal orthogonal to the given hat-points, with a
    nonzero spatial part (so the plane is affine).  hats: list of 4-vectors."""
    ns = nullspace(hats)
    assert ns, "no common plane through the given points"
    for _ in range(tries):
        coeffs = [rint(rng, -5, 5) for _ in ns]
        n = [sum(c * w[i] for c, w in zip(coeffs, ns)) for i in range(4)]
        if any(n[i] != 0 for i in range(3)):
            return n
    raise RuntimeError("could not find affine plane normal")

def point_on_affine_plane4(n4, rng):
    """Random affine point p in Q^3 with n4 . hat(p) = 0 (spatial part of n4
    nonzero)."""
    j = max(range(3), key=lambda i: abs(n4[i]))
    assert n4[j] != 0
    coords = [None] * 3
    free = [i for i in range(3) if i != j]
    for i in free:
        coords[i] = rint(rng, -8, 8)
    coords[j] = -(n4[3] + sum(n4[i] * coords[i] for i in free)) / n4[j]
    return coords
