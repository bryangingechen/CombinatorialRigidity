"""
Phase 39 W4 (hcontract) recon — the contraction-arm hybrid gates N8/N9/N10.

Exact-Q molecular pencil model, shared infrastructure imported from
../kbare/kbare_common.py (see its module docstring for the verified
model-to-Lean dictionary: 5 rows/edge = perp basis of the Plucker hinge
extensor, deficiency = max over partitions of 6(|P|-1) - 5 d(P)).

Three gates (design doc, section "W4 decomposition recon"):

N8 (K4 via triangle contraction; the bare-kernel (K-bare-c) shape).
  G = K4, H = triangle {1,2,3}.  G/E(H) = the 3-fold parallel class on
  {v*, 4}; its ONLY target-rank (= 6) bare pencil realizations are the
  coincident-cluster ones (pt(v*) = pt(4) = pt*, panels = the common plane
  Pi*, hinges = distinct lines through pt* in Pi*) -- checked here.  The
  W4 specialization glue then forces the hybrid onto: atoms 1,2,3 in Pi*
  (the cross-incidence pt1(i) . n2(4) = 0), atom 4 := pt*, all hinges the
  molecular joining lines.  Gate: contraction rank = 6, hybrid rank = 18
  = 6*3 - def(K4) (def = 0), pencil witness verified.

N9 (C4+x,y via vertex removal; the branch-(2b) 6.5-mirror, and a truth
  gate for the conjecture at the W4 discriminating instance).
  G = C4(1,2,3,4) + x~1, x~3, y~1, y~3 (the cluster-refutation instance;
  feasible, simple, EVERY rigid-subgraph contraction non-simple, so the
  (K-c) branch never fires -- G sits in the vertex-removal branch).
  G - x = C4 + y: its pencil stratum forces all five atoms coplanar
  (star(1) and star(3) share {2,4,y}); target 24 = 6*4 - 0.  Re-add x:
  pt(x) in Pi(1) meet Pi(3) = the common plane, hinges = joining lines;
  target 30 = 6*5 - 0.  Gate: IH rank 24, extended rank 30, both pencil
  witnesses verified.  NOTE: 30 here is ALSO the first direct sample of
  the conjecture's target on this instance's (forced all-coplanar) pencil
  stratum -- the R1/R2 record only bounded it (deficit non-positive).
  FINDING (first run, seed 3901 sample 3): with pt(x) on the LINE through
  pt(1), pt(3) the two fresh hinges coincide and the rank caps at 29 --
  a genuine in-stratum failure locus for the re-add, excluded exactly by
  the output motive's own fourth conjunct (closedNbhd(x) = {x,1,3}
  point-triple LI).  The gate now samples the nondegenerate branch
  (triple-LI enforced, as the eventual steering leaf must) and keeps the
  collinear control as a deliberate mechanism check.

N10 (C4+x+y+xy via C4 contraction; the (K-c) kernel shape and the
  general two-distinct-anchor boundary pattern, remainder (ii)).
  G = C4(1,2,3,4) + x~1, y~2, x~y.  H = C4; G/E(H) = triangle {v*,x,y}:
  SIMPLE and feasible (hub-free), so the IH's generic half fires there --
  this is a genuine (K-c) instance.  IH: generic triangle, rank 12 =
  6*2 - 0.  Hybrid: keep p2's atoms c_x, c_y (and the x~y hinge), sample
  the C4 block in-family: Pi(1) := plane(p1, p2, c_x), p4 in Pi(1);
  Pi(2) := plane(p1, p2, c_y), p3 in Pi(2).  Distinct anchors c_x != c_y
  give two genuinely distinct boundary panels -- the first sample beyond
  N3's single-cluster boundary pattern.  Gate: hybrid rank 30 =
  6*5 - def(G) (def = 0), pencil witness + nondegeneracy conjuncts
  verified (adjacent hubs 1,2: normals independent).

Run:  python3 notes/scripts/w4/hybrid_gates.py [nsamples]
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'kbare'))
from kbare_common import (F, hat, wedge2, perp_basis, nullspace, dot,
                          rank_exact, exact_deficiency, verts_of, neighbors,
                          degrees, build_rigidity, verify_pencil_witness,
                          rvec3, rint)


# ---------------- generic helpers ----------------

def rank_rows_exact(rows):
    return rank_exact(rows)


def build_rigidity_extensors(vertices, edge_ext):
    """Rigidity matrix from explicit hinge extensors: edge_ext is a list of
    ((u, w), C_e) with C_e a 6-vector Plucker extensor (need not come from
    two affine atoms -- used for the degenerate contraction realizations)."""
    idx = {v: k for k, v in enumerate(vertices)}
    ncol = 6 * len(vertices)
    rows = []
    for (u, w), Ce in edge_ext:
        assert any(c != 0 for c in Ce), f"zero extensor at {(u, w)}"
        for wv in perp_basis(Ce):
            row = [F(0)] * ncol
            bu, bw = 6 * idx[u], 6 * idx[w]
            for k in range(6):
                row[bu + k] += wv[k]
                row[bw + k] -= wv[k]
            rows.append(row)
    return rows


def plane_through(p0, p1, p2):
    """4-normal of the affine plane through three affine points (assumed in
    general position)."""
    ns = nullspace([hat(p0), hat(p1), hat(p2)])
    assert len(ns) == 1, "three points not in general position"
    return ns[0]


def point_in_plane(n4, rng, avoid=()):
    """Random affine point with n4 . hat(p) = 0, distinct from `avoid`."""
    j = next(i for i in range(3) if n4[i] != 0)
    for _ in range(200):
        coords = [None] * 3
        free = [i for i in range(3) if i != j]
        for i in free:
            coords[i] = rint(rng, -8, 8)
        coords[j] = -(n4[3] + sum(n4[i] * coords[i] for i in free)) / n4[j]
        if all(coords != a for a in avoid):
            return coords
    raise RuntimeError


def li_hats(points):
    """Rank of the hat-matrix of the given affine points."""
    return rank_exact([hat(p) for p in points])


# ---------------- N8: K4 via triangle contraction ----------------

def gate_n8(rng):
    # The contracted graph: 3-fold parallel class on {v*, 4}.  Its bare
    # target-rank realization is the coincident cluster: shared (pt*, Pi*),
    # hinges = distinct lines through pt* inside Pi*.
    A, B, C = rvec3(rng), rvec3(rng), rvec3(rng)
    if li_hats([A, B, C]) < 3:
        return None
    Pi = plane_through(A, B, C)           # the shared panel
    pstar = A                              # the shared concurrency point
    q1, q2, q3 = B, C, point_in_plane(Pi, rng, avoid=(A, B, C))
    ext = [(('v', 'w'), wedge2(hat(pstar), hat(q))) for q in (q1, q2, q3)]
    rows_c = build_rigidity_extensors(['v', 'w'], ext)
    rk_c = rank_rows_exact(rows_c)

    # The hybrid: atoms 1,2,3 in Pi* (cross-incidence into Pi(4) = Pi*),
    # atom 4 := pt*; all six hinges = molecular joining lines.
    p = {1: q1, 2: q2, 3: q3, 4: pstar}
    edges = [(1, 2), (2, 3), (1, 3), (4, 1), (4, 2), (4, 3)]
    ok, _ = verify_pencil_witness(edges, p)
    if not ok:
        return None
    rows, _ = build_rigidity(edges, p)
    rk = rank_rows_exact(rows)
    dfc, _ = exact_deficiency(edges)
    return rk_c, rk, 6 * 3 - dfc


# ---------------- N9: C4+x,y via vertex removal ----------------

C4XY = [(1, 2), (2, 3), (3, 4), (4, 1),
        ('x', 1), ('x', 3), ('y', 1), ('y', 3)]


def gate_n9(rng):
    # G - x = C4 + y.  Pencil stratum: star(1) = {1,2,4,y}, star(3) =
    # {3,2,4,y} both coplanar; generically {2,4,y} spans a plane so ALL
    # five atoms are coplanar.  Sample that branch directly.
    A, B, C = rvec3(rng), rvec3(rng), rvec3(rng)
    if li_hats([A, B, C]) < 3:
        return None
    Pi = plane_through(A, B, C)
    p = {2: A, 4: B, 'y': C,
         1: point_in_plane(Pi, rng, avoid=(A, B, C)),
         3: point_in_plane(Pi, rng, avoid=(A, B, C))}
    if p[1] == p[3]:
        return None
    edges_v = [(1, 2), (2, 3), (3, 4), (4, 1), ('y', 1), ('y', 3)]
    ok, _ = verify_pencil_witness(edges_v, p)
    if not ok:
        return None
    # nondegeneracy spot-checks on the IH witness (non-hub point triples):
    for (v, a, b) in [(2, 1, 3), (4, 1, 3), ('y', 1, 3)]:
        if li_hats([p[v], p[a], p[b]]) < 3:
            return None
    rows_v, _ = build_rigidity(edges_v, p)
    rk_v = rank_rows_exact(rows_v)
    dfc_v, _ = exact_deficiency(edges_v)

    # Re-add x: pt(x) in Pi(1) meet Pi(3) = Pi (the coincident-panel
    # branch); hinges = joining lines (forced: through pt(x) and
    # pt(1)/pt(3)).  Nondegenerate branch: {x,1,3} triple-LI (the output
    # motive's fourth conjunct at x; collinear pt(x) is the rank-29
    # failure locus, see the module docstring finding).
    p['x'] = point_in_plane(Pi, rng, avoid=tuple(p.values()))
    if li_hats([p['x'], p[1], p[3]]) < 3:
        return None
    ok, _ = verify_pencil_witness(C4XY, p)
    if not ok:
        return None
    rows, _ = build_rigidity(C4XY, p)
    rk = rank_rows_exact(rows)
    dfc, _ = exact_deficiency(C4XY)
    return rk_v, 6 * 4 - dfc_v, rk, 6 * 5 - dfc


def gate_n9_collinear_control(rng):
    """Deliberate control: pt(x) ON line(pt(1), pt(3)) -- expect rank 29."""
    while True:
        A, B, C = rvec3(rng), rvec3(rng), rvec3(rng)
        if li_hats([A, B, C]) < 3:
            continue
        Pi = plane_through(A, B, C)
        p = {2: A, 4: B, 'y': C,
             1: point_in_plane(Pi, rng, avoid=(A, B, C)),
             3: point_in_plane(Pi, rng, avoid=(A, B, C))}
        if p[1] == p[3]:
            continue
        # midpoint-style rational point on the line through p1, p3:
        t = F(rng.randint(1, 5), rng.randint(6, 9))
        p['x'] = [p[1][i] + t * (p[3][i] - p[1][i]) for i in range(3)]
        if p['x'] in (p[1], p[3]):
            continue
        ok, _ = verify_pencil_witness(C4XY, p)
        if not ok:
            continue
        rows, _ = build_rigidity(C4XY, p)
        return rank_rows_exact(rows)


# ---------------- N10: C4+x+y+xy via C4 contraction ----------------

N10E = [(1, 2), (2, 3), (3, 4), (4, 1), ('x', 1), ('y', 2), ('x', 'y')]


def gate_n10(rng):
    # p2: generic triangle {v*, x, y} (hub-free, no pencil constraint).
    cx, cy, cv = rvec3(rng), rvec3(rng), rvec3(rng)
    if li_hats([cx, cy, cv]) < 3 or cx == cy:
        return None
    tri_edges = [('x', 'v'), ('y', 'v'), ('x', 'y')]
    rows_t, _ = build_rigidity(tri_edges, {'x': cx, 'y': cy, 'v': cv})
    rk_t = rank_rows_exact(rows_t)

    # In-family C4 block: hubs 1 (nbrs 2,4,x) and 2 (nbrs 1,3,y).
    # Pi(1) = plane(p1, p2, c_x) must also contain p4;
    # Pi(2) = plane(p1, p2, c_y) must also contain p3.
    p1, p2v = rvec3(rng), rvec3(rng)
    if li_hats([p1, p2v, cx]) < 3 or li_hats([p1, p2v, cy]) < 3:
        return None
    Pi1 = plane_through(p1, p2v, cx)
    Pi2 = plane_through(p1, p2v, cy)
    p = {1: p1, 2: p2v, 'x': cx, 'y': cy,
         4: point_in_plane(Pi1, rng, avoid=(p1, p2v, cx)),
         3: point_in_plane(Pi2, rng, avoid=(p1, p2v, cy))}
    ok, normals = verify_pencil_witness(N10E, p)
    if not ok:
        return None
    # nondegeneracy: adjacent hubs 1,2 -> closedHubNbhd(1) = {1,2} needs
    # independent normals, i.e. Pi(1) != Pi(2):
    if rank_exact([normals[1], normals[2]]) < 2:
        return None
    # non-hub point triples:
    for (v, a, b) in [(3, 2, 4), (4, 1, 3), ('x', 1, 'y'), ('y', 2, 'x')]:
        if li_hats([p[v], p[a], p[b]]) < 3:
            return None
    rows, _ = build_rigidity(N10E, p)
    rk = rank_rows_exact(rows)
    dfc, _ = exact_deficiency(N10E)
    return rk_t, rk, 6 * 5 - dfc


# ---------------- N10b: forced-boundary-panel pattern ----------------

N10BE = [(1, 2), (2, 3), (3, 4), (4, 1), ('x', 1), ('y', 1), ('x', 'y')]


def gate_n10b(rng):
    """The sharpest remainder-(ii) pattern: boundary body 1 has TWO outside
    anchors x, y (G = C4 + x~1, y~1, x~y; contraction = the same simple
    triangle).  Pi(1) must contain p1, p2, p4, c_x, c_y, so it is FORCED =
    plane(p1, c_x, c_y): no boundary-panel genericity survives at 1.
    Gate: hybrid rank 30 = 6*5 - def (def = 0)."""
    cx, cy, cv = rvec3(rng), rvec3(rng), rvec3(rng)
    if li_hats([cx, cy, cv]) < 3 or cx == cy:
        return None
    rows_t, _ = build_rigidity([('x', 'v'), ('y', 'v'), ('x', 'y')],
                               {'x': cx, 'y': cy, 'v': cv})
    rk_t = rank_rows_exact(rows_t)

    p1 = rvec3(rng)
    if li_hats([p1, cx, cy]) < 3:
        return None
    Pi1 = plane_through(p1, cx, cy)      # the FORCED boundary panel at 1
    p = {1: p1, 'x': cx, 'y': cy,
         2: point_in_plane(Pi1, rng, avoid=(p1, cx, cy)),
         4: point_in_plane(Pi1, rng, avoid=(p1, cx, cy)),
         3: rvec3(rng)}
    if p[2] == p[4]:
        return None
    ok, _ = verify_pencil_witness(N10BE, p)
    if not ok:
        return None
    for (v, a, b) in [(2, 1, 3), (4, 1, 3), (3, 2, 4),
                      ('x', 1, 'y'), ('y', 1, 'x')]:
        if li_hats([p[v], p[a], p[b]]) < 3:
            return None
    rows, _ = build_rigidity(N10BE, p)
    rk = rank_rows_exact(rows)
    dfc, _ = exact_deficiency(N10BE)
    return rk_t, rk, 6 * 5 - dfc


# ---------------- driver ----------------

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    rng = random.Random(3901)

    print("== N8: K4 via triangle contraction (bare (K-bare-c) shape) ==")
    got = 0
    while got < n:
        r = gate_n8(rng)
        if r is None:
            continue
        got += 1
        rk_c, rk, tgt = r
        print(f"  sample {got}: contraction rank {rk_c} (target 6), "
              f"hybrid K4 rank {rk} / target {tgt}")
        assert rk_c == 6 and rk == tgt == 18, "N8 FAILED"

    print("== N9: C4+x,y via vertex removal (branch-(2b) 6.5-mirror) ==")
    got = 0
    while got < n:
        r = gate_n9(rng)
        if r is None:
            continue
        got += 1
        rk_v, tgt_v, rk, tgt = r
        print(f"  sample {got}: C4+y rank {rk_v} / target {tgt_v}; "
              f"extended C4+x,y rank {rk} / target {tgt}")
        assert rk_v == tgt_v == 24 and rk == tgt == 30, "N9 FAILED"
    rk29 = gate_n9_collinear_control(rng)
    print(f"  collinear control (pt(x) on line(pt1,pt3)): rank {rk29} "
          f"(mechanism check, expect 29)")
    assert rk29 == 29, "N9 collinear control unexpected"

    print("== N10: C4+x+y+xy via C4 contraction ((K-c) shape, general "
          "boundary pattern) ==")
    got = 0
    while got < n:
        r = gate_n10(rng)
        if r is None:
            continue
        got += 1
        rk_t, rk, tgt = r
        print(f"  sample {got}: triangle IH rank {rk_t} (target 12), "
              f"hybrid rank {rk} / target {tgt}")
        assert rk_t == 12 and rk == tgt == 30, "N10 FAILED"

    print("== N10b: C4+x~1,y~1,xy (forced boundary panel at body 1) ==")
    got = 0
    while got < n:
        r = gate_n10b(rng)
        if r is None:
            continue
        got += 1
        rk_t, rk, tgt = r
        print(f"  sample {got}: triangle IH rank {rk_t} (target 12), "
              f"hybrid rank {rk} / target {tgt}")
        assert rk_t == 12 and rk == tgt == 30, "N10b FAILED"

    print("ALL GATES PASSED")


if __name__ == '__main__':
    main()
