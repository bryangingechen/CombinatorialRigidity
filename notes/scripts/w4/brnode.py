"""
Direction BRNODE (ordinal 52) -- rho_bar at the INTERNAL R-NODE,
(BE-31)(ii)'s named residue: the step from *ear* to *general piece*.

  TARGET  Let H be a 2-connected piece with marked pair {u,v} whose SPQR
          tree carries an INTERNAL R-node -- a 3-connected skeleton B with
          at least one virtual edge replaced by a flexible child.  Describe
          rho_bar_{u,v}(H): a computation from B together with the
          children's own data, or a criterion at the peel of a child, that
          does NOT go through a per-shape witness.

  JOB 1's SHARP FORM (the spec: decide FIRST)  Is rho_bar at an R-node a
          function of the children's rho_bar at all?  ANSWER: YES, by the
          DECORATED-SKELETON LAW (BE-59), proved in the workbook and
          asserted here at every draw: the full boundary trace of a child
          C_e at its terminals {x,y} is Delta (+) ({0} (+) rho_bar_e)
          -- a function of rho_bar_e ALONE ((BE-59)(i), extracted from
          (BE-22)(i)'s own proof) -- so M(H) restricted to V(B) is EXACTLY
          the motion space of the DECORATED skeleton (each edge e of B
          constrained by m_x - m_y in rho_bar_e in place of a hinge line),
          and rho_bar_{u,v}(H) is its image at (u,v).  Exact at EVERY
          configuration, no genericity.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-59)  THE DECORATED-SKELETON LAW.
             `law`  : at every battery piece and draw, as identities of
                      SPACES: (i) the boundary-pair lemma
                      image(M(C_e) at (x,y)) = Delta (+) 0(+)rho_bar_e in
                      K^12, per child; (ii) rho_bar(H) = rho_bar of the
                      decorated skeleton (children entering ONLY through
                      their rho_bar, recomputed on the child subgraph
                      alone); (iii) the dim law dim M(H) = dim M(B; dec)
                      + sum_e (dim M(C_e) - 6 - d_e), the many-piece
                      fibre-product law containing (BE-22)(i).
                      Plus the SAME-rho_bar / DIFFERENT-geometry pair test
                      (job 1's decidable form): redraw a child's interior
                      keeping rho_bar_e the same subspace (full-span m=5
                      mechanism, and the flat Lambda^2 pi mechanism of
                      (BE-30)(iii)(b)) and assert rho_bar(H) unmoved.

  (BE-60)  THE RECURSION OVER THE SPQR TREE, COMPLETE.
             `rec`  : nested pieces (R-node top, P-node child, S-node
                      grandchildren): rho_bar computed bottom-up from the
                      hinge LINES alone -- S sums, P intersects, R takes
                      the decorated kernel -- asserted equal to the direct
                      computation, as spaces.

  (BE-61)  THE CARVE-OUT -- (BE-22)(vi)'s reach at the R-node.
             `carve`: combinatorial, no configuration.  The collapse peel
                      at child e exists iff delta_{xy} of a SIDE vanishes;
                      for the all-leaf remainder that is
                      delta_{xy}(B - uv - e), a checkable function of B.
                      Enumerated EXHAUSTIVELY over all labelled 3-connected
                      B at n = 4, 5 (and n = 6 exhaustively in full mode,
                      named shapes + a disclosed sample in validate);
                      witnesses both ways: K4 always collapses, the PRISM
                      at two rungs does NOT -- the both-flexible case is
                      nonempty already at ONE flexible child.

  (BE-62)  JOB 2 -- the routing verdict's measured half.
             `route`: at constructed both-flexible pieces, guarded draws:
                      the (BE-22)(i) fibre-product identity ASSERTED at
                      every peel; attainment, welded attainment (rho_i vs
                      delta_i) and the general-position shortfall
                      min(rho_1+rho_2,6) - dim(rho_bar_1+rho_bar_2)
                      REPORTED per draw (constructor-capped figures,
                      F27 one-directional: a shortfall is "not attained by
                      this constructor", never "does not attain").

Succeeds `notes/scripts/w4/bwin.py` (Steps BE53-BE57); imports `bwin` /
`bsharp` / `bimage` / `binduc` READ-ONLY, and through them the rest of the
chain -- the `kbare/` sibling-import set gains its THIRTEENTH consumer and
the chain is ELEVEN deep (recorded, NO MOVE MADE).  Landed figures are
CITED, never re-run.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, never dimensions), every sampled
configuration through binduc's `assert_generic_star` AND
`kbare_common.verify_pencil_witness`, every cap disclosed.

DISCLOSED DRIVER CAPS: (1) the sampler is bsharp's
`sample_piece_config_adj`, so batteries are confined to pieces whose branch
subgraph has max degree <= 2 -- the prism one-flex piece is therefore a
CARVE witness (combinatorial) and route draws use its two-ear variant;
(2) the pair test runs at the two mechanisms named above, not at every
mechanism producing equal rho_bar; (3) `carve` full mode is exhaustive at
n <= 6; validate's n = 6 tier is named shapes + a 300-graph sample,
disclosed in the output.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import itertools
import random
import sys
import time
from fractions import Fraction as F

import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import (rank as rank_exact, nullspace, hat, wedge2,   # noqa: E402
                       neighbors)
from kbare_common import verts_of, verify_pencil_witness             # noqa: E402
from binduc import (assert_generic_star, def_by_partitions,          # noqa: E402
                    motion_space, set_partitions, theta,
                    vertex_connectivity_at_least)
from bimage import (dim, isect, lam2, rho_bar_of,                    # noqa: E402
                    same_space, span, perp_std)
from bsharp import (_relabel, guarded_draw,                          # noqa: E402
                    sample_piece_config_adj)
from bwin import dehom                                               # noqa: E402

SEED = 20260901

I6 = [[F(1) if i == j else F(0) for j in range(6)] for i in range(6)]


# ============================================= width-agnostic space helpers
# bimage's `span` has a rank-6 shortcut that returns I6, which is WRONG for
# 12-wide rows; these never shortcut.

def dim_w(rows):
    return rank_exact(rows) if rows else 0


def span_w(rows):
    return nullspace(nullspace(rows)) if rows else []


def same_space_w(A, B):
    return dim_w(A) == dim_w(B) == dim_w(A + B)


# ===================================================== piece construction
#
# A piece is (H_edges, children, VB) built from a skeleton B, a parent edge
# (u, v) DELETED from H, and substitutions on other edges of B.  `children`
# covers EVERY edge of B - parent: a leaf child is the real edge itself.

def ear_child(x, y, m, tag):
    """Path x - t1 - ... - tm - y (m >= 1 interior vertices)."""
    vs = [x] + [f'{tag}{i}' for i in range(1, m + 1)] + [y]
    return [(vs[i], vs[i + 1]) for i in range(m + 1)]


def theta_child(x, y, abc, tag):
    """theta(a, b, c) between x and y, interiors tagged."""
    E = theta(*abc)
    ren = {'u': x, 'v': y}
    for (p, q) in E:
        for z in (p, q):
            if z not in ('u', 'v') and z not in ren:
                ren[z] = f'{tag}{z}'
    return _relabel(E, ren)


def build_piece(name, skel, parent, subs):
    """skel: edges of B.  parent: (u,v), deleted.  subs: {edge: spec} with
    spec = ('ear', m) or ('theta', (a,b,c)) or ('spec', edges).  Returns
    dict(name, H, children, VB, u, v)."""
    u, v = parent
    VB = sorted({z for e in skel for z in e}, key=str)
    H = []
    children = []          # (x, y, child_edges, kind)
    ktag = 0
    for (x, y) in skel:
        if {x, y} == {u, v}:
            continue       # the parent virtual edge is NOT an edge of H
        key = frozenset((x, y))
        spec = subs.get(key)
        if spec is None:
            ce = [(x, y)]
            kind = 'leaf'
        elif spec[0] == 'ear':
            ktag += 1
            ce = ear_child(x, y, spec[1], f'e{ktag}_')
            kind = f'ear({spec[1]})'
        elif spec[0] == 'theta':
            ktag += 1
            ce = theta_child(x, y, spec[1], f't{ktag}_')
            kind = 'theta' + str(spec[1])
        else:
            ce = spec[1]
            kind = 'spec'
        H += ce
        children.append((x, y, ce, kind))
    return dict(name=name, H=H, children=children, VB=VB, u=u, v=v)


def K5():
    return [(a, b) for a, b in itertools.combinations(range(5), 2)]


def K4_named():
    return [('u', 'v'), ('u', 'a'), ('u', 'b'), ('v', 'a'), ('v', 'b'),
            ('a', 'b')]


def PRISM_named():
    return [('a1', 'a2'), ('a2', 'a3'), ('a3', 'a1'),
            ('b1', 'b2'), ('b2', 'b3'), ('b3', 'b1'),
            ('a1', 'b1'), ('a2', 'b2'), ('a3', 'b3')]


def K33_named():
    return [(x, y) for x in ('x1', 'x2', 'x3') for y in ('y1', 'y2', 'y3')]


# ============================================= (BE-59): the decorated law

def decorated_motion(children, pt, VB):
    """Motion space of the DECORATED skeleton: m: V(B) -> K^6 with
    m_x - m_y in rho_bar_e for every child.  The decorations are computed
    on the CHILD SUBGRAPH ALONE -- nothing else about the child enters.
    Returns (kernel basis, {child index: (S_e, rho_e, dM_e)})."""
    idx = {z: i for i, z in enumerate(sorted(VB, key=str))}
    n6 = 6 * len(idx)
    rows = []
    decs = []
    for (x, y, ce, kind) in children:
        S_e, rho_e, dMe, _ = rho_bar_of(ce, pt, x, y)
        decs.append((S_e, rho_e, dMe))
        for wv in perp_std(S_e):
            row = [F(0)] * n6
            bx, by = 6 * idx[x], 6 * idx[y]
            for k in range(6):
                row[bx + k] += wv[k]
                row[by + k] -= wv[k]
            rows.append(row)
    if rows:
        ker = nullspace(rows)
    else:
        ker = [[F(1) if i == j else F(0) for j in range(n6)]
               for i in range(n6)]
    return ker, decs, idx


def decorated_rho(children, pt, VB, u, v):
    ker, decs, idx = decorated_motion(children, pt, VB)
    bu, bv = 6 * idx[u], 6 * idx[v]
    img = [[m[bv + k] - m[bu + k] for k in range(6)] for m in ker]
    return span(img), ker, decs


def boundary_pair_check(ce, pt, x, y):
    """(BE-59)(i): image(M(C_e) at (x,y)) = Delta (+) 0(+)rho_bar_e, as an
    identity of SUBSPACES of K^12.  Raises on failure."""
    Vc = sorted(verts_of(ce), key=str)
    idx = {w: i for i, w in enumerate(Vc)}
    ker, _, _ = motion_space(ce, pt)
    R = [[m[6 * idx[x] + k] for k in range(6)]
         + [m[6 * idx[y] + k] for k in range(6)] for m in ker]
    S_e, rho_e, dMe, _ = rho_bar_of(ce, pt, x, y)
    target = [d + d for d in I6] + [[F(0)] * 6 + list(b) for b in S_e]
    assert same_space_w(span_w(R), span_w(target)), \
        '(BE-59)(i): boundary trace is not Delta (+) 0(+)rho_bar'
    assert dim_w(R) == 6 + rho_e, '(BE-59)(i): boundary trace dimension'
    return rho_e, dMe


def full_law_measure(pc, pt):
    """Everything Step BE58 asserts at one configuration."""
    S_dir, rho_dir, dMH, _ = rho_bar_of(pc['H'], pt, pc['u'], pc['v'])
    S_dec, ker, decs = decorated_rho(pc['children'], pt, pc['VB'],
                                     pc['u'], pc['v'])
    # (BE-59)(ii): the law, as an identity of spaces
    assert same_space(S_dir, S_dec), \
        '(BE-59)(ii): decorated skeleton disagrees with the direct rho_bar'
    # (BE-59)(i): the boundary-pair lemma, per child
    internal = 0
    for (x, y, ce, kind), (S_e, rho_e, dMe) in zip(pc['children'], decs):
        rho_c, dMc = boundary_pair_check(ce, pt, x, y)
        assert rho_c == rho_e and dMc == dMe
        internal += dMe - 6 - rho_e
    # (BE-59)(iii): the dim law
    assert dMH == len(ker) + internal, \
        '(BE-59)(iii): dim M(H) != dim M(B; dec) + sum internal freedoms'
    return S_dir, rho_dir, dMH, decs


# ------------------------------------------------------------ law batteries

def law_battery():
    B = []
    B.append(build_piece('K4+ear1(ab)', K4_named(), ('u', 'v'),
                         {frozenset(('a', 'b')): ('ear', 1)}))
    B.append(build_piece('K4+ear4(ab)', K4_named(), ('u', 'v'),
                         {frozenset(('a', 'b')): ('ear', 4)}))
    B.append(build_piece('K4+ear5(ab)', K4_named(), ('u', 'v'),
                         {frozenset(('a', 'b')): ('ear', 5)}))
    B.append(build_piece('K4+theta222(ab)', K4_named(), ('u', 'v'),
                         {frozenset(('a', 'b')): ('theta', (2, 2, 2))}))
    B.append(build_piece('K4+ear2(ab)+ear1(ua)', K4_named(), ('u', 'v'),
                         {frozenset(('a', 'b')): ('ear', 2),
                          frozenset(('u', 'a')): ('ear', 1)}))
    B.append(build_piece('K4+ear2(ua)+ear2(vb)', K4_named(), ('u', 'v'),
                         {frozenset(('u', 'a')): ('ear', 2),
                          frozenset(('v', 'b')): ('ear', 2)}))
    B.append(build_piece('K4+3ears(2,2,3)', K4_named(), ('u', 'v'),
                         {frozenset(('a', 'b')): ('ear', 2),
                          frozenset(('u', 'a')): ('ear', 2),
                          frozenset(('v', 'b')): ('ear', 3)}))
    # FLEXIBLE at the marked pair: dim M = 7, rho_bar_{u,v} nonzero
    B.append(build_piece('K4+3ears(3,3,2)', K4_named(), ('u', 'v'),
                         {frozenset(('u', 'a')): ('ear', 3),
                          frozenset(('v', 'b')): ('ear', 3),
                          frozenset(('a', 'b')): ('ear', 2)}))
    B.append(build_piece('K33+ear2+ear3', K33_named(), ('x1', 'y1'),
                         {frozenset(('x2', 'y2')): ('ear', 2),
                          frozenset(('x3', 'y3')): ('ear', 3)}))
    return B


def draw_piece(pc, rng, tries=30):
    for _ in range(tries):
        got = guarded_draw(pc['H'], pc['u'], pc['v'], rng,
                           sampler=sample_piece_config_adj)
        if got is not None:
            return got
    return None


def plane_of_hub(H, pt, z):
    """Affine data (normal, offset, homogeneous basis) of the closed-star
    plane at z; requires the star to span a plane."""
    nb = neighbors(H)
    star = [hat(pt[z])] + [hat(pt[w]) for w in nb[z]]
    ns = nullspace(star)
    assert len(ns) == 1, 'closed star does not span a plane'
    n4 = ns[0]
    basis = nullspace([n4])
    return n4, basis


def affine_pt_in_plane(basis, rng, s=25):
    """Random affine point of a homogeneous plane basis (3 vectors in K^4)."""
    for _ in range(200):
        cs = [F(rng.randint(-s, s)) for _ in range(3)]
        x = [sum(cs[j] * basis[j][k] for j in range(3)) for k in range(4)]
        if x[3] != 0:
            return tuple(dehom(x))
    raise RuntimeError('no affine point in plane')


def run_pair_full(rng, npairs=3):
    """Job 1's decidable form at the FULL-SPAN mechanism: an ear(5) child
    generically has rho_bar_e = K^6; redraw its interior (different
    geometry, same rho_bar_e) and assert rho_bar(H) is unmoved."""
    pc = build_piece('K4+ear5(ab)', K4_named(), ('u', 'v'),
                     {frozenset(('a', 'b')): ('ear', 5)})
    ear = next(c for c in pc['children'] if c[3] == 'ear(5)')
    x, y, ce, _ = ear
    ints = sorted(verts_of(ce), key=str)
    ints = [w for w in ints if w not in (x, y)]
    done = 0
    attempts = 0
    while done < npairs and attempts < 60:
        attempts += 1
        got = draw_piece(pc, rng)
        if got is None:
            continue
        pt, planes = got
        S0, _, _, _ = rho_bar_of(pc['H'], pt, pc['u'], pc['v'])
        Se0, re0, _, _ = rho_bar_of(ce, pt, x, y)
        if re0 != 6:
            continue    # want the full-span mechanism; disclosed
        _, ba = plane_of_hub(pc['H'], pt, x)
        _, bb = plane_of_hub(pc['H'], pt, y)
        pt2 = dict(pt)
        # interior w adjacent to x lies in pi_x, to y in pi_y, else free
        nbc = neighbors(ce)
        for w in ints:
            if x in nbc[w]:
                pt2[w] = affine_pt_in_plane(ba, rng)
            elif y in nbc[w]:
                pt2[w] = affine_pt_in_plane(bb, rng)
            else:
                pt2[w] = tuple(F(rng.randint(-25, 25)) for _ in range(3))
        try:
            assert_generic_star(pc['H'], pt2)
        except AssertionError:
            continue
        ok, _ = verify_pencil_witness(pc['H'], pt2)
        if not ok:
            continue
        Se1, re1, _, _ = rho_bar_of(ce, pt2, x, y)
        if re1 != 6:
            continue
        assert same_space(Se0, Se1)
        assert any(pt2[w] != pt[w] for w in ints), 'interiors did not move'
        S1, _, _, _ = rho_bar_of(pc['H'], pt2, pc['u'], pc['v'])
        assert same_space(S0, S1), \
            'pair test (full-span): rho_bar(H) moved with the interior'
        # and the decorated law at BOTH configurations
        full_law_measure(pc, pt)
        full_law_measure(pc, pt2)
        done += 1
    assert done == npairs, f'pair test (full-span): only {done} pairs drawn'
    return done


def run_pair_flat(rng, npairs=3):
    """The NON-full-span pair mechanism ((BE-30)(iii)(b)): with
    pi_a = pi_b = pi, an ear(2) child has rho_bar_e = Lambda^2 pi at EVERY
    interior draw -- equal subspaces, different geometry."""
    pc = build_piece('K4+ear2(ab)', K4_named(), ('u', 'v'),
                     {frozenset(('a', 'b')): ('ear', 2)})
    ear = next(c for c in pc['children'] if c[3] == 'ear(2)')
    x, y, ce, _ = ear
    ints = [w for w in sorted(verts_of(ce), key=str) if w not in (x, y)]
    plane_h = [[F(1), F(0), F(0), F(0)],
               [F(0), F(1), F(0), F(0)],
               [F(0), F(0), F(0), F(1)]]     # z = 0, homogeneous basis
    L2 = lam2(plane_h)
    done = 0
    attempts = 0
    verts = sorted(verts_of(pc['H']), key=str)
    while done < npairs and attempts < 60:
        attempts += 1
        pt = {w: (F(rng.randint(-25, 25)), F(rng.randint(-25, 25)), F(0))
              for w in verts}
        try:
            assert_generic_star(pc['H'], pt)
        except AssertionError:
            continue
        ok, _ = verify_pencil_witness(pc['H'], pt)
        if not ok:
            continue
        Se0, re0, _, _ = rho_bar_of(ce, pt, x, y)
        assert same_space(Se0, L2), \
            '(BE-30)(iii)(b): flat ear(2) rho_bar is not Lambda^2 pi'
        S0, _, _, _ = rho_bar_of(pc['H'], pt, pc['u'], pc['v'])
        pt2 = dict(pt)
        for w in ints:
            pt2[w] = (F(rng.randint(-25, 25)), F(rng.randint(-25, 25)), F(0))
        try:
            assert_generic_star(pc['H'], pt2)
        except AssertionError:
            continue
        ok, _ = verify_pencil_witness(pc['H'], pt2)
        if not ok:
            continue
        Se1, _, _, _ = rho_bar_of(ce, pt2, x, y)
        assert same_space(Se1, L2)
        assert any(pt2[w] != pt[w] for w in ints), 'interiors did not move'
        S1, _, _, _ = rho_bar_of(pc['H'], pt2, pc['u'], pc['v'])
        assert same_space(S0, S1), \
            'pair test (flat): rho_bar(H) moved with the interior'
        full_law_measure(pc, pt)
        done += 1
    assert done == npairs, f'pair test (flat): only {done} pairs drawn'
    return done


def run_law(seed=SEED, nd=4):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== law: the decorated-skeleton law (BE-59), seed {seed}')
    total = 0
    for pc in law_battery():
        got = 0
        rows = []
        for _ in range(nd * 12):
            if got == nd:
                break
            g = draw_piece(pc, rng)
            if g is None:
                continue
            pt, planes = g
            S, rho, dMH, decs = full_law_measure(pc, pt)
            rows.append((rho, dMH, [d[1] for d in decs]))
            got += 1
        assert got == nd, f'{pc["name"]}: only {got}/{nd} draws'
        total += got
        rhos = sorted({r for r, _, _ in rows})
        dMs = sorted({m for _, m, _ in rows})
        print(f'  {pc["name"]:28s}  draws {got}  rho_bar dims {rhos}  '
              f'dim M(H) {dMs}  child rho dims {rows[0][2]}')
    pf = run_pair_full(rng)
    print(f'  pair test, full-span mechanism (ear(5), rho_bar_e = K^6): '
          f'{pf}/{pf} pairs, rho_bar(H) unmoved')
    pfl = run_pair_flat(rng)
    print(f'  pair test, flat mechanism (ear(2), rho_bar_e = Lambda^2 pi): '
          f'{pfl}/{pfl} pairs, rho_bar(H) unmoved')
    print(f'== law PASS: (BE-59)(i)/(ii)/(iii) asserted at every one of '
          f'{total} guarded draws + {pf + pfl} interior-redraw pairs '
          f'({time.time() - t0:.1f} s)')


# ============================================= (BE-60): the full recursion

def sp_eval(spec, pt):
    """Bottom-up SPQR evaluation from hinge LINES alone.
    spec = ('leaf', x, y) | ('series', [specs]) | ('parallel', [specs])."""
    if spec[0] == 'leaf':
        return span([wedge2(hat(pt[spec[1]]), hat(pt[spec[2]]))])
    parts = [sp_eval(s, pt) for s in spec[1]]
    if spec[0] == 'series':
        out = []
        for P in parts:
            out += P
        return span(out)
    out = parts[0]
    for P in parts[1:]:
        out = isect(out, P)
    return out


def series_leaves(ce):
    """The all-S spec of a path child, ordered from x to y."""
    return ('series', [('leaf', a, b) for (a, b) in ce])


def theta_spec(x, y, ce):
    """The P-of-S spec of a theta child built by theta_child."""
    nb = neighbors(ce)
    paths = []
    for w0 in sorted(nb[x], key=str):
        P = [(x, w0)]
        prev, cur = x, w0
        while cur != y:
            nxt = [z for z in nb[cur] if z != prev][0]
            P.append((cur, nxt))
            prev, cur = cur, nxt
        paths.append(series_leaves(P))
    return ('parallel', paths)


def run_rec(seed=SEED, nd=3):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== rec: the recursion over the SPQR tree (BE-60), seed {seed}')

    # R1: R-node top, P-node child of S-children
    r1 = build_piece('K4+theta233(ab)', K4_named(), ('u', 'v'),
                     {frozenset(('a', 'b')): ('theta', (2, 3, 3))})
    # R2: R-node top, theta child + ear child
    r2 = build_piece('K4+theta223(ab)+ear2(ua)', K4_named(), ('u', 'v'),
                     {frozenset(('a', 'b')): ('theta', (2, 2, 3)),
                      frozenset(('u', 'a')): ('ear', 2)})
    # R3: R-node top, one child itself a SERIES of a theta and a path
    th = theta_child('a', 'z3_', (2, 2, 2), 't3_')
    tail = [('z3_', 'w3_'), ('w3_', 'b')]
    r3 = build_piece('K4+series(theta222,path2)(ab)', K4_named(), ('u', 'v'),
                     {frozenset(('a', 'b')): ('spec', th + tail)})

    def spec_of(pc, x, y, ce, kind):
        if kind == 'leaf':
            return ('leaf', x, y)
        if kind.startswith('ear'):
            return series_leaves(ce)
        if kind.startswith('theta'):
            return theta_spec(x, y, ce)
        # r3's nested child: series of theta(a..z3_) then path z3_..b
        return ('series', [theta_spec('a', 'z3_', th), series_leaves(tail)])

    for pc in (r1, r2, r3):
        got = 0
        for _ in range(nd * 10):
            if got == nd:
                break
            g = draw_piece(pc, rng)
            if g is None:
                continue
            pt, _ = g
            # bottom-up: every child's rho_bar from LINES alone...
            idx = {z: i for i, z in enumerate(sorted(pc['VB'], key=str))}
            n6 = 6 * len(idx)
            rows = []
            for (x, y, ce, kind) in pc['children']:
                S_rec = sp_eval(spec_of(pc, x, y, ce, kind), pt)
                # the recursive value IS the child's rho_bar (S/P laws):
                S_e, _, _, _ = rho_bar_of(ce, pt, x, y)
                assert same_space(S_rec, S_e), \
                    f'(BE-60): S/P recursion wrong at child {kind}'
                for wv in perp_std(S_rec):
                    row = [F(0)] * n6
                    bx, by = 6 * idx[x], 6 * idx[y]
                    for k in range(6):
                        row[bx + k] += wv[k]
                        row[by + k] -= wv[k]
                    rows.append(row)
            ker = nullspace(rows)
            bu, bv = 6 * idx[pc['u']], 6 * idx[pc['v']]
            S_rec = span([[m[bv + k] - m[bu + k] for k in range(6)]
                          for m in ker])
            S_dir, _, _, _ = rho_bar_of(pc['H'], pt, pc['u'], pc['v'])
            assert same_space(S_rec, S_dir), \
                '(BE-60): full recursion disagrees with the direct rho_bar'
            got += 1
        assert got == nd, f'{pc["name"]}: only {got}/{nd} draws'
        print(f'  {pc["name"]:36s}  draws {got}: lines-only recursion '
              f'== direct rho_bar, as spaces')
    print(f'== rec PASS: the SPQR recursion (leaf lines -> S sums -> P '
          f'intersects -> R decorated kernel) asserted at every draw '
          f'({time.time() - t0:.1f} s)')


# ============================================= (BE-61): the carve-out

def edges_of_graph_mask(n, mask, pairs):
    return [pairs[i] for i in range(len(pairs)) if (mask >> i) & 1]


def gen_3conn(n):
    """All labelled 3-connected graphs on range(n) (exhaustive)."""
    pairs = list(itertools.combinations(range(n), 2))
    out = []
    for mask in range(1 << len(pairs)):
        if bin(mask).count('1') < 3 * n / 2:
            continue
        E = edges_of_graph_mask(n, mask, pairs)
        degs = {}
        for a, b in E:
            degs[a] = degs.get(a, 0) + 1
            degs[b] = degs.get(b, 0) + 1
        if len(degs) < n or min(degs.values()) < 3:
            continue
        if vertex_connectivity_at_least(n, E, 3):
            out.append(E)
    return out


def carve_enumerate(ns=(4, 5), n6mode='named', n6samp=300, seed=SEED):
    """delta_{xy}(B - uv - e) over (B, uv, e): the checkable collapse
    condition for the all-leaf remainder.  Exhaustive at each n in `ns`;
    n = 6 either 'named'+sampled or 'full' (exhaustive), disclosed."""
    rng = random.Random(seed)
    results = {}

    def scan_graph(n, E, tally):
        verts = list(range(n)) if isinstance(E[0][0], int) \
            else sorted({z for e in E for z in e}, key=str)
        parts = list(set_partitions(verts))
        where = []
        for P in parts:
            w = {}
            for i, part in enumerate(P):
                for z in part:
                    w[z] = i
            where.append((w, len(P)))
        cross = []      # per partition: list of crossing flags per edge
        for (w, q) in where:
            cross.append([1 if w[a] != w[b] else 0 for (a, b) in E])
        dtot = [sum(c) for c in cross]
        for iu in range(len(E)):
            for ie in range(len(E)):
                if ie == iu:
                    continue
                ex, ey = E[ie]
                f = 0
                g = 0
                for pi, (w, q) in enumerate(where):
                    d = dtot[pi] - cross[pi][iu] - cross[pi][ie]
                    val = 6 * (q - 1) - 5 * d
                    if val > f:
                        f = val
                    if w[ex] == w[ey] and val > g:
                        g = val
                delta = f - g
                tally[0] += 1
                if delta == 0:
                    tally[1] += 1
                elif tally[2] is None:
                    tally[2] = (E, E[iu], E[ie], delta)

    for n in ns:
        graphs = gen_3conn(n)
        tally = [0, 0, None]
        for E in graphs:
            scan_graph(n, E, tally)
        results[n] = (len(graphs), tally)
        print(f'  n={n} EXHAUSTIVE: {len(graphs)} labelled 3-connected '
              f'graphs, {tally[0]} (B,uv,e) triples, '
              f'delta_xy(B-uv-e)=0 at {tally[1]} '
              f'({100.0 * tally[1] / tally[0]:.1f}%)')
        if tally[2] is not None:
            E, euv, ee, dd = tally[2]
            print(f'      first positive witness: B={E}  uv={euv}  e={ee}  '
                  f'delta={dd}')
    if n6mode == 'full':
        graphs = gen_3conn(6)
        tally = [0, 0, None]
        for E in graphs:
            scan_graph(6, E, tally)
        print(f'  n=6 EXHAUSTIVE: {len(graphs)} labelled 3-connected '
              f'graphs, {tally[0]} triples, delta=0 at {tally[1]} '
              f'({100.0 * tally[1] / tally[0]:.1f}%)')
        results[6] = (len(graphs), tally)
    else:
        named = {'prism': PRISM_named(), 'K33': K33_named(),
                 'octahedron': [(a, b) for a, b in
                                itertools.combinations(range(6), 2)
                                if (a, b) not in ((0, 1), (2, 3), (4, 5))],
                 'wheel5': [(5, i) for i in range(5)]
                 + [(i, (i + 1) % 5) for i in range(5)]}
        for nm, E in named.items():
            tally = [0, 0, None]
            scan_graph(6, E, tally)
            print(f'  n=6 named {nm:10s}: {tally[0]} triples, delta=0 at '
                  f'{tally[1]} ({100.0 * tally[1] / tally[0]:.1f}%)')
        # a disclosed sample of labelled 3-connected graphs at n = 6
        pairs = list(itertools.combinations(range(6), 2))
        tally = [0, 0, None]
        got = 0
        tried = 0
        while got < n6samp and tried < 60 * n6samp:
            tried += 1
            mask = rng.getrandbits(len(pairs))
            E = edges_of_graph_mask(6, mask, pairs)
            if len(E) < 9:
                continue
            degs = {}
            for a, b in E:
                degs[a] = degs.get(a, 0) + 1
                degs[b] = degs.get(b, 0) + 1
            if len(degs) < 6 or min(degs.values()) < 3:
                continue
            if not vertex_connectivity_at_least(6, E, 3):
                continue
            scan_graph(6, E, tally)
            got += 1
        print(f'  n=6 SAMPLED (cap {n6samp} graphs, DISCLOSED -- not '
              f'exhaustive): {got} graphs, {tally[0]} triples, delta=0 at '
              f'{tally[1]} ({100.0 * tally[1] / tally[0]:.1f}%)')
    return results


def peel_table(pc):
    """Per child peel of a constructed piece: (f, g, delta) of BOTH sides,
    combinatorially (independent set-partition oracle)."""
    out = []
    for i, (x, y, ce, kind) in enumerate(pc['children']):
        if kind == 'leaf':
            continue
        side2 = ce
        side1 = []
        for j, (a, b, cf, k2) in enumerate(pc['children']):
            if j != i:
                side1 += cf
        v1 = sorted({z for e in side1 for z in e}, key=str)
        v2 = sorted({z for e in side2 for z in e}, key=str)
        f1 = def_by_partitions(side1, v1)
        g1 = def_by_partitions(side1, v1, together=(x, y))
        f2 = def_by_partitions(side2, v2)
        g2 = def_by_partitions(side2, v2, together=(x, y))
        out.append((kind, (x, y), (f1, g1, f1 - g1), (f2, g2, f2 - g2)))
    return out


def run_carve(seed=SEED, n6mode='named'):
    t0 = time.time()
    print(f'== carve: (BE-22)(vi)\'s reach at the R-node (BE-61), '
          f'seed {seed}, n6mode={n6mode}')
    print('  -- the collapse condition at the peel of child e, all-leaf '
          'remainder: delta_xy(B - uv - e) = 0 --')
    carve_enumerate(n6mode=n6mode, seed=seed)
    print('  -- peel tables at the constructed pieces (combinatorial; '
          'delta = f - g per side) --')
    pieces = [
        build_piece('K4+ear2(ab)  [ONE flexible child]', K4_named(),
                    ('u', 'v'), {frozenset(('a', 'b')): ('ear', 2)}),
        build_piece('prism+ear2(a2b2)  [ONE flexible child]', PRISM_named(),
                    ('a1', 'b1'), {frozenset(('a2', 'b2')): ('ear', 2)}),
        build_piece('prism+2ears(rungs)  [TWO flexible children]',
                    PRISM_named(), ('a1', 'b1'),
                    {frozenset(('a2', 'b2')): ('ear', 2),
                     frozenset(('a3', 'b3')): ('ear', 1)}),
        build_piece('K4+ear2(ab)+ear3(ua)  [TWO flexible children]',
                    K4_named(), ('u', 'v'),
                    {frozenset(('a', 'b')): ('ear', 2),
                     frozenset(('u', 'a')): ('ear', 3)}),
        build_piece('K4+ear2(ab)+ear1(ua)  [TWO, short-cycle remainder]',
                    K4_named(), ('u', 'v'),
                    {frozenset(('a', 'b')): ('ear', 2),
                     frozenset(('u', 'a')): ('ear', 1)}),
    ]
    witness_no_collapse = 0
    for pc in pieces:
        print(f'  {pc["name"]}')
        any_zero = False
        for (kind, cut, s1, s2) in peel_table(pc):
            print(f'      peel {kind:9s} at {cut}:  side1 (f,g,delta)={s1}'
                  f'  side2={s2}')
            if s1[2] == 0 or s2[2] == 0:
                any_zero = True
        print(f'      -> collapse peel available: {any_zero}')
        if not any_zero:
            witness_no_collapse += 1
    # the two headline asserts
    k4 = peel_table(pieces[0])
    assert k4[0][2][2] == 0, 'K4 one-flex: remainder delta should be 0'
    pr = peel_table(pieces[1])
    assert pr[0][2][2] > 0 and pr[0][3][2] > 0, \
        'prism one-flex: both sides should be flexible at the only peel'
    assert witness_no_collapse >= 1
    print(f'== carve PASS: K4 one-flex COLLAPSES (remainder delta 0); '
          f'prism one-flex does NOT ({witness_no_collapse} constructed '
          f'no-collapse pieces) ({time.time() - t0:.1f} s)')


# ============================================= (BE-62): the routing measure

def run_route(seed=SEED, nd=3):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== route: the (BE-22) quantities at R-node peels (BE-62), '
          f'seed {seed}')
    print('  figures are constructor-capped (adj sampler): a shortfall is '
          '"not attained by THIS constructor", never "does not attain" '
          '(F27).')
    pieces = [
        build_piece('K4+ear2(ab)  [collapse ctrl]', K4_named(), ('u', 'v'),
                    {frozenset(('a', 'b')): ('ear', 2)}),
        build_piece('K4+ear3(ua)+ear3(vb)', K4_named(), ('u', 'v'),
                    {frozenset(('u', 'a')): ('ear', 3),
                     frozenset(('v', 'b')): ('ear', 3)}),
        build_piece('K4+ear2(ab)+ear3(ua)', K4_named(), ('u', 'v'),
                    {frozenset(('a', 'b')): ('ear', 2),
                     frozenset(('u', 'a')): ('ear', 3)}),
        build_piece('K4+3ears(3,3,2)', K4_named(), ('u', 'v'),
                    {frozenset(('u', 'a')): ('ear', 3),
                     frozenset(('v', 'b')): ('ear', 3),
                     frozenset(('a', 'b')): ('ear', 2)}),
    ]
    gp_shortfalls = 0
    weld_shortfalls = 0
    npeels = 0
    for pc in pieces:
        VH = sorted(verts_of(pc['H']), key=str)
        fH = def_by_partitions(pc['H'], VH)
        got = 0
        for _ in range(nd * 10):
            if got == nd:
                break
            g = draw_piece(pc, rng)
            if g is None:
                continue
            pt, _ = g
            _, _, dMH, _ = rho_bar_of(pc['H'], pt, pc['u'], pc['v'])
            attH = (dMH == 6 + fH)
            lines = [f'  {pc["name"]:26s} draw {got}: dim M(H)={dMH} '
                     f'(target {6 + fH}, attains={attH})']
            for i, (x, y, ce, kind) in enumerate(pc['children']):
                if kind == 'leaf':
                    continue
                side2 = ce
                side1 = []
                for j, (a, b, cf, k2) in enumerate(pc['children']):
                    if j != i:
                        side1 += cf
                v1 = sorted({z for e in side1 for z in e}, key=str)
                v2 = sorted({z for e in side2 for z in e}, key=str)
                f1 = def_by_partitions(side1, v1)
                g1 = def_by_partitions(side1, v1, together=(x, y))
                f2 = def_by_partitions(side2, v2)
                g2 = def_by_partitions(side2, v2, together=(x, y))
                d1, d2 = f1 - g1, f2 - g2
                S1, r1, dM1, _ = rho_bar_of(side1, pt, x, y)
                S2, r2, dM2, _ = rho_bar_of(side2, pt, x, y)
                dsum = dim(span(S1 + S2))
                # (BE-22)(i), ASSERTED (exact at every configuration)
                assert dMH == dM1 + dM2 - 6 - dsum, \
                    '(BE-22)(i) fails at an R-node peel'
                att1 = (dM1 == 6 + f1)
                att2 = (dM2 == 6 + f2)
                weld = (r1 == d1, r2 == d2)
                gp = min(r1 + r2, 6) - dsum
                crit = (dsum == min(d1 + d2, 6))
                npeels += 1
                if gp > 0:
                    gp_shortfalls += 1
                if not all(weld):
                    weld_shortfalls += 1
                lines.append(
                    f'      peel {kind:8s} at ({x},{y}): '
                    f'delta=({d1},{d2}) rho=({r1},{r2}) '
                    f'attain=({att1},{att2}) weld(rho=delta)={weld} '
                    f'dim(sum)={dsum} vs min(d1+d2,6)={min(d1 + d2, 6)} '
                    f'criterion={crit} gp_shortfall={gp}')
            print('\n'.join(lines))
            got += 1
        assert got == nd, f'{pc["name"]}: only {got}/{nd} draws'
    print(f'== route: {npeels} measured peels; (BE-22)(i) ASSERTED at every '
          f'one; general-position shortfall min(rho1+rho2,6)-dim(sum) > 0 '
          f'at {gp_shortfalls}/{npeels}; welded-attainment shortfall at '
          f'{weld_shortfalls}/{npeels} (constructor-capped, disclosed) '
          f'({time.time() - t0:.1f} s)')


# ===================================================== validate

def run_validate():
    t0 = time.time()
    print('== validate: all four modes at a reduced tier ==')
    run_law(nd=2)
    run_rec(nd=2)
    run_carve(n6mode='named')
    run_route(nd=2)
    print(f'== validate PASS ({time.time() - t0:.1f} s total)')


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode == 'law':
        run_law()
    elif mode == 'rec':
        run_rec()
    elif mode == 'carve':
        run_carve(n6mode=(sys.argv[2] if len(sys.argv) > 2 else 'named'))
    elif mode == 'route':
        run_route()
    elif mode == 'validate':
        run_validate()
    else:
        raise SystemExit(f'unknown mode {mode!r}: '
                         'law | rec | carve [named|full] | route | validate')
