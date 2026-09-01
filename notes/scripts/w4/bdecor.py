"""
Direction BDECOR (ordinal 53) -- the ACHIEVABLE DECORATIONS of an internal
R-node piece, (BE-62)(iii)'s named residue: which decoration tuples
{rho_bar_e} are simultaneously achievable by pencil configurations of H.

  TARGET  BRNODE proved the FACTORIZATION -- children incident to a branch
          vertex z are coupled ONLY through the flag (p_z, pi_z), so the
          achievable tuples are a fibred product over flag assignments on
          V(B) of PER-CHILD achievable sets, known exactly for leaves and
          for EARS ((BE-30)(ii)/(iii)) and open beyond.  This direction
          asks for the per-child sets past ears (theta children first) and
          for attainment of the decorated skeleton over the coupled flags.

  THE ANSWER, said at the top (the spec demands it).  The per-child sets
  are NEVER NEEDED past ears.  Recursing the fibration down to the
  TOPOLOGICAL skeleton -- hubs (degree >= 3, plus u, v) joined by one edge
  per maximal degree-2 branch -- makes EVERY child an ear, and at a fixed
  legal flag assignment on the hub set the legal configurations are the
  LITERAL PRODUCT of legal ear chains, one per branch ((BE-64)).  The
  coordinator's job-2 hypothesis ("the P-node layer may be FREE") is
  therefore CONFIRMED and STRENGTHENED: every layer is free at fixed
  flags, and the only coupling left is the flag base itself, which is a
  PENCIL-REALIZATION problem for the hub subgraph -- free exactly when no
  two hubs are adjacent, and otherwise the arc's own §(K-chart) object
  ((BE-65)).

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-64)  THE BRANCH-PRODUCT THEOREM.
             `prod` : both directions, as identities of SPACES.
                      FORWARD -- at joint draws from TWO independent
                      samplers (`bsharp.sample_piece_config_adj` and
                      `widened.place_pencil_general`), every topological
                      branch's point chain is (BE-30)(ii)-legal at the
                      configuration's own closed-star flags.
                      CONVERSE (the MIX test, and the direct test of the
                      spec's weak link (b), the DEGREE-3 TERMINAL) --
                      chains drawn in INDEPENDENT runs at one fixed flag
                      assignment are glued into one configuration; both
                      gates asserted, and rho_bar asserted equal to the
                      branch-decorated value.
                      Plus the decorated-skeleton law (BE-59)(ii) on the
                      TOPOLOGICAL skeleton (coarser than SPQR: its
                      children are exactly the ears), and a NESTED piece
                      (an R-node child inside an R-node piece).

  (BE-66)  THE THETA CHILD, DONE EXPLICITLY.
             `theta`: the first case past ears.  rho_bar = the
                      intersection of the three chain spans (the P law),
                      the generic dimension law
                      max(0, sum_j min(a_j,6) - 12) at pi_x != pi_y, and
                      the welded-attainment obligation (BE-22)(iii)(a)
                      measured: rho = delta at every drawn triple.

  (BE-66)(iii)  THE SMALL-BRANCH CORRECTION -- the spec's weak link (a).
             `small`: (BE-30)(iii) does NOT stay inside its branch.  In
                      the pi_x = pi_y regime a length-3 branch has span
                      EXACTLY Lambda^2 pi, so two of them have EQUAL
                      spans and the P-node intersection does not drop:
                      rho_bar EXCEEDS general position, by up to 3.  The
                      exact law is max(ambient, confined) with the
                      confined term computed inside Lambda^2 pi.

  (BE-65)  THE FLAG BASE, AND WHERE THE RESIDUAL DIFFICULTY SITS.
             `chart`: the achievable-decoration space IS the pencil chart
                      of H, and its tower is §(K-chart) (CH-1)'s
                      (`widened.place_pencil_general`): hub points free,
                      hub normals in ker A_h, non-hub points in the meet
                      of their hub planes.  The three (CH-1) hypotheses
                      (`hcard`, min degree 2, girth >= 4) checked at every
                      battery piece; cross-sampler agreement on rho_bar
                      between the branch sampler and `place_pencil_general`.

  (BE-67)  HALF (B) -- attainment over the coupled flags.
             `attain`: (BE-22)'s quantities at R-node peels whose peeled
                      child is a THETA (BRNODE measured ear children
                      only).  The (BE-22)(i) fibre-product identity
                      ASSERTED at every peel; attainment, welded
                      attainment and the general-position shortfall
                      REPORTED.  A row that reaches the criterion is a
                      PER-PIECE THEOREM (`rank <= target` is universal and
                      the conclusion existential); a row that does not
                      would be "not attained by this constructor" (F27).

Succeeds `notes/scripts/w4/brnode.py` (Steps BE58-BE62); imports `brnode` /
`bsharp` / `bimage` / `binduc` / `bwin` / `bzavoid` / `widened` /
`nogood_subdiv` READ-ONLY, and through them the rest of the chain -- the
`kbare/` sibling-import set gains its FOURTEENTH consumer and the chain is
TWELVE deep (recorded in `notes/scripts/README.md` *Harness debt*, NO MOVE
MADE).  Landed figures are CITED, never re-run.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, never dimensions), every sampled
configuration through binduc's `assert_generic_star` AND
`kbare_common.verify_pencil_witness` -- the composite guard §3 requires of a
`place_pencil_general`-sampled battery before any rate is quoted.

DISCLOSED DRIVER CAPS.
  (1) The branch sampler `sample_by_branches` places hub points in order of
      hub-degree, each inside the intersection of the planes its complete
      constraints force, and VERIFIES every constraint before returning --
      so it draws a hub with THREE neighbours in the MARKED-PAIR-AUGMENTED
      hub set ({u, v} union {degree >= 3}, which is bsharp's own "branch
      vertex" set), which `bsharp.sample_piece_config_adj` REFUSES outright.
      That is a real (small) LIFT of the chain's standing sampler cap, and it
      is what lets the NESTED two-level R-node piece be drawn at all --
      `prod` records bsharp refusing exactly that row while the branch
      sampler and `widened.place_pencil_general` draw it (widened's own hub
      set is degree->=-3 only, so the nested piece is inside ITS cap).
      (CH-1)'s `hcard` is likewise read on degree->=-3 vertices only and
      holds at every battery piece.  The placement is still a greedy order,
      so a dense hub subgraph (e.g. an all-leaf K4 skeleton, whose only
      pencil configurations are flat) can still defeat it.
  (2) `theta`/`small` quote GENERIC members of the achievable set: the
      minimum over the seeded draws, since dim of an intersection is UPPER
      semicontinuous.  A larger value at a special configuration is not a
      counterexample to the generic law -- `small` exhibits exactly such
      configurations on purpose.
  (3) `attain`'s battery is K4-skeleton pieces with theta and ear children
      from ONE constructor; a shortfall elsewhere would be "not attained by
      this constructor", never "does not attain" (F27).  None was seen.
  (4) Deficiencies use `nogood_subdiv.deficiency` (the (6,6)-count-matroid
      oracle) so that the WELDED multigraph is computable at |V| > 8; it is
      cross-checked against binduc's exact `def_by_partitions(together=)`
      partition oracle at 15/15 small instances in `chart`.

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

from exactcore import (rank as rank_exact, nullspace, hat,               # noqa: E402
                       neighbors)
from kbare_common import verts_of, verify_pencil_witness                 # noqa: E402
from binduc import (assert_generic_star, def_by_partitions,              # noqa: E402
                    theta)
from bimage import (dim, isect, same_space, span, v4, pt_in,             # noqa: E402
                    sample_flags, legal_chain, chain_of, rho_bar_of)
from bsharp import guarded_draw, sample_piece_config_adj                 # noqa: E402
from bwin import dehom                                                   # noqa: E402
from brnode import build_piece, K4_named, PRISM_named                    # noqa: E402
from widened import place_pencil_general                                 # noqa: E402
from nogood_subdiv import deficiency as peb_def                          # noqa: E402

SEED = 20260901

I6 = [[F(1) if i == j else F(0) for j in range(6)] for i in range(6)]


# ================================================= deficiencies (cap (4))

def d3(edges):
    """def_3 of a (multi)graph, via the (6,6)-count-matroid oracle."""
    V = sorted(verts_of(edges), key=str)
    ren = {w: i for i, w in enumerate(V)}
    return peb_def([(ren[a], ren[b]) for (a, b) in edges],
                   list(range(len(V))))


def weld_d3(edges, x, y):
    """g_{xy} = def_3 of the WELDED multigraph (identify y with x; parallel
    edges KEPT -- the partition value counts edge multiplicity)."""
    V = sorted({w for e in edges for w in e} - {y}, key=str)
    ren = {w: i for i, w in enumerate(V)}
    ren[y] = ren[x]
    E2 = [(ren[a], ren[b]) for (a, b) in edges if ren[a] != ren[b]]
    return peb_def(E2, list(range(len(V))))


# ======================================== the TOPOLOGICAL skeleton (BE-64)

def hubs_and_branches(edges, u, v):
    """W = {u, v} union {degree >= 3}, and one branch per maximal path whose
    interior vertices all have degree 2.  Returns (sorted W, branches) with
    a branch given as (z, z', [interior vertices in order])."""
    nb = neighbors(edges)
    W = set([u, v]) | {z for z in verts_of(edges) if len(nb[z]) >= 3}
    branches, seen = [], set()
    for z in sorted(W, key=str):
        for w0 in sorted(nb[z], key=str):
            if frozenset((z, w0)) in seen:
                continue
            seen.add(frozenset((z, w0)))
            path, prev, cur = [z, w0], z, w0
            while cur not in W:
                nxt = [t for t in nb[cur] if t != prev][0]
                seen.add(frozenset((cur, nxt)))
                path.append(nxt)
                prev, cur = cur, nxt
            branches.append((path[0], path[-1], path[1:-1]))
    return sorted(W, key=str), branches


def hub_adjacency(W, branches):
    """The HUB SUBGRAPH: which hubs a LENGTH-1 branch (a real edge) joins."""
    ha = {z: set() for z in W}
    for (z, zp, ints) in branches:
        if not ints:
            ha[z].add(zp)
            ha[zp].add(z)
    return ha


def hcard_ok_piece(edges, u, v):
    """(CH-1)'s `hcard` -- every vertex of degree >= 3 has at most two
    neighbours of degree >= 3 -- read on the topological skeleton, PLUS the
    marked-pair-augmented version this driver's own sampler works with (the
    marked pair is in W whatever its degree, so that the branches ending at
    it are named).  Returns (chart-hcard, W, branches, hub adjacency)."""
    W, br = hubs_and_branches(edges, u, v)
    ha = hub_adjacency(W, br)
    nb = neighbors(edges)
    real = {z for z in W if len(nb[z]) >= 3}
    chart_hcard = all(len([w for w in ha[z] if w in real]) <= 2
                      for z in real)
    return chart_hcard, W, br, ha


def girth(edges):
    nb = neighbors(edges)
    best = None
    for s in sorted(nb, key=str):
        dist = {s: 0}
        par = {s: None}
        q = [s]
        while q:
            x = q.pop(0)
            for y in nb[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    par[y] = x
                    q.append(y)
                elif y != par[x]:
                    c = dist[x] + dist[y] + 1
                    best = c if best is None else min(best, c)
    return best


# ============================================ the branch sampler (BE-64/65)

def flag_assignment(W, branches, rng, s=20, tries=400, fixed=None):
    """A legal flag assignment on the hub set: p_z in P^3 and a plane pi_z
    through p_z with p_{z'} in pi_z for every LENGTH-1 branch zz'.

    The hub points are placed IN ORDER of hub-degree, each one inside the
    intersection of the planes its already-complete constraints force -- so
    a hub with THREE hub neighbours (which `bsharp.sample_piece_config_adj`
    and `widened.place_pencil_general` both bail on) is handled, and the
    result is VERIFIED against every constraint before it is returned.  The
    planes are then read off the closed HUB-star.  `fixed` pins flags (e.g.
    at u, v) to a `sample_flags` draw."""
    ha = hub_adjacency(W, branches)
    order = sorted(W, key=lambda z: (len(ha[z]), str(z)))
    # the constraint sets: one per hub, {z} u ha[z], required to have rank <= 3
    cons = {z: sorted({z} | ha[z], key=str) for z in W}
    for _ in range(tries):
        P, B = {}, {}
        if fixed:
            for z, (p, bb) in fixed.items():
                P[z], B[z] = p, bb
        ok = True
        for z in order:
            if z in P:
                continue
            basis = None                      # None = unconstrained
            for c in W:
                S = cons[c]
                if z not in S:
                    continue
                others = [w for w in S if w != z]
                if any(w not in P for w in others):
                    continue                  # constraint not yet complete
                sp = span([P[w] for w in others])
                if dim(sp) < 3:
                    continue                  # any point keeps rank <= 3
                basis = sp if basis is None else isect(basis, sp)
            if basis is None:
                P[z] = v4(rng, s)
            elif dim(basis) == 0:
                ok = False
                break
            else:
                P[z] = pt_in(basis, rng, s)
        if not ok:
            continue
        if any(rank_exact([P[a], P[b]]) != 2
               for a, b in itertools.combinations(sorted(W, key=str), 2)):
            continue
        for z in W:                            # VERIFY every constraint
            if rank_exact([P[w] for w in cons[z]]) > 3:
                ok = False
                break
        if not ok:
            continue
        for z in W:
            if z in B:
                if any(rank_exact(B[z] + [P[w]]) != 3 for w in ha[z]):
                    ok = False
                    break
                continue
            bas = [P[z]] + [P[w] for w in sorted(ha[z], key=str)]
            for _fill in range(6):
                if rank_exact(bas) >= 3:
                    break
                bas.append(v4(rng, s))
            if rank_exact(bas) != 3:
                ok = False
                break
            B[z] = nullspace([nullspace(bas)[0]])
            assert dim(B[z]) == 3 and rank_exact(B[z] + [P[z]]) == 3, \
                'the hub plane does not carry its own point'
        if not ok:
            continue
        return P, B
    return None, None


def draw_branch(P, B, z, zp, k, rng, s=20, tries=60):
    """ONE branch's interior, drawn from ITS OWN moduli alone ((BE-30)(ii)'s
    parametrization): first point in pi_z, last in pi_{z'}, the rest free;
    at k = 1 the single interior point lies in pi_z cap pi_{z'}."""
    if k == 0:
        return []
    for _ in range(tries):
        if k == 1:
            L = nullspace([nullspace(B[z])[0], nullspace(B[zp])[0]])
            if not L:
                return None
            out = [pt_in(L, rng, s)]
        else:
            out = [pt_in(B[z], rng, s)]
            for _ in range(k - 2):
                out.append(v4(rng, s))
            out.append(pt_in(B[zp], rng, s))
        if legal_chain([P[z]] + out + [P[zp]]):
            return out
    return None


def assemble(edges, pts, gate=True):
    """Homogeneous points -> affine, through BOTH gates."""
    if any(x[3] == 0 for x in pts.values()):
        return None
    aff = {w: tuple(dehom(x)) for w, x in pts.items()}
    if len(set(aff.values())) != len(aff):
        return None
    if gate:
        try:
            assert_generic_star(edges, aff)
        except AssertionError:
            return None
        ok, _ = verify_pencil_witness(edges, aff)
        if not ok:
            return None
    return aff


def sample_by_branches(edges, u, v, rng, s=20, tries=40, fixed=None):
    """(BE-64)'s parametrization: a hub flag assignment, then INDEPENDENT
    legal chains, one per topological branch.  Returns
    (affine pt, {z: plane basis}, W, branches) or None."""
    W, branches = hubs_and_branches(edges, u, v)
    for _ in range(tries):
        P, B = flag_assignment(W, branches, rng, s, fixed=fixed)
        if P is None:
            continue
        pts, ok = dict(P), True
        for (z, zp, ints) in branches:
            got = draw_branch(P, B, z, zp, len(ints), rng, s)
            if got is None:
                ok = False
                break
            for w, x in zip(ints, got):
                pts[w] = x
        if not ok:
            continue
        aff = assemble(edges, pts)
        if aff is None:
            continue
        return aff, {z: B[z] for z in W}, W, branches
    return None


# ============================== the branch-decorated form of (BE-59)(ii)

def branch_span(pt, path):
    """<C_b>, the span of the branch's hinge-line chain."""
    return span(chain_of([hat(pt[w]) for w in path]))


def branch_decorated_rho(edges, pt, u, v, W=None, branches=None):
    """rho_bar_{u,v} of the TOPOLOGICAL skeleton decorated by the chain
    spans -- (BE-59)(ii) at the coarsest decomposition whose children are
    all ears.  Returns (space, dim, per-branch spans)."""
    if W is None:
        W, branches = hubs_and_branches(edges, u, v)
    idx = {z: i for i, z in enumerate(W)}
    n6 = 6 * len(W)
    rows, spans = [], []
    for (z, zp, ints) in branches:
        S = branch_span(pt, [z] + ints + [zp])
        spans.append(S)
        for wv in nullspace(S) if S else I6:
            row = [F(0)] * n6
            bz, bzp = 6 * idx[z], 6 * idx[zp]
            for k in range(6):
                row[bz + k] += wv[k]
                row[bzp + k] -= wv[k]
            rows.append(row)
    ker = nullspace(rows) if rows else [[F(1) if i == j else F(0)
                                         for j in range(n6)]
                                        for i in range(n6)]
    bu, bv = 6 * idx[u], 6 * idx[v]
    img = [[m[bv + k] - m[bu + k] for k in range(6)] for m in ker]
    S = span(img) if img else []
    return S, dim(S), spans


def chain_is_legal(pt, planes, z, zp, ints):
    """The (BE-30)(ii) legality of ONE branch at the configuration's own
    flags: the point chain legal, the first hinge line in Pi_z, the last in
    Pi_{z'}.  `planes` carries a homogeneous basis per hub."""
    path = [z] + ints + [zp]
    P = [hat(pt[w]) for w in path]
    if not legal_chain(P):
        return False, 'chain not legal'
    if ints:
        if rank_exact(planes[z] + [hat(pt[ints[0]])]) != 3:
            return False, 'first interior point off pi_z'
        if rank_exact(planes[zp] + [hat(pt[ints[-1]])]) != 3:
            return False, 'last interior point off pi_zp'
    else:
        if rank_exact(planes[z] + [hat(pt[zp])]) != 3:
            return False, 'real-edge endpoint off pi_z'
        if rank_exact(planes[zp] + [hat(pt[z])]) != 3:
            return False, 'real-edge endpoint off pi_zp'
    return True, ''


def star_planes(edges, pt, W):
    """The closed-star plane at each hub, read off the CONFIGURATION."""
    nb = neighbors(edges)
    out = {}
    for z in W:
        star = [hat(pt[z])] + [hat(pt[w]) for w in sorted(nb[z], key=str)]
        ns = nullspace(star)
        if len(ns) != 1:
            return None
        out[z] = nullspace([ns[0]])
    return out


# ===================================================== batteries

def theta_piece(abc, tag='ab'):
    return theta(*abc)


def R_BATTERY():
    K4 = K4_named()
    return [
        ('K4 + th(3,3,3)/ab', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('a', 'b')): ('theta', (3, 3, 3))})),
        ('K4 + th(5,5,5)/ab', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('a', 'b')): ('theta', (5, 5, 5))})),
        ('K4 + th(5,5,5)/ab + ear3/ua', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('a', 'b')): ('theta', (5, 5, 5)),
                                  frozenset(('u', 'a')): ('ear', 3)})),
        ('K4 + th(4,4,5)/ab + ear3/ua + ear3/vb', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('a', 'b')): ('theta', (4, 4, 5)),
                                  frozenset(('u', 'a')): ('ear', 3),
                                  frozenset(('v', 'b')): ('ear', 3)})),
        ('K4 + th(5,5,5)/ua + th(5,5,5)/vb', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('u', 'a')): ('theta', (5, 5, 5)),
                                  frozenset(('v', 'b')): ('theta', (5, 5, 5))})),
        ('K4 + th(6,6,6)/ab + ear4/ua', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('a', 'b')): ('theta', (6, 6, 6)),
                                  frozenset(('u', 'a')): ('ear', 4)})),
        ('K4 + 3 ears(3,3,2) [brnode ctrl]', build_piece(
            'p', K4, ('u', 'v'), {frozenset(('u', 'a')): ('ear', 3),
                                  frozenset(('v', 'b')): ('ear', 3),
                                  frozenset(('a', 'b')): ('ear', 2)})),
    ]


def nested_piece():
    """An R-node child INSIDE an R-node piece: the child on ab is itself a
    K4 skeleton (minus its own parent edge) with two ears."""
    inner = build_piece('inner', K4_named(), ('u', 'v'),
                        {frozenset(('u', 'a')): ('ear', 3),
                         frozenset(('v', 'b')): ('ear', 3)})
    ren = {'u': 'a', 'v': 'b', 'a': 'n1', 'b': 'n2'}
    ce = [(ren.get(p, f'n_{p}'), ren.get(q, f'n_{q}'))
          for (p, q) in inner['H']]
    return build_piece('K4 + [K4-piece]/ab + ear3/ua', K4_named(), ('u', 'v'),
                       {frozenset(('a', 'b')): ('spec', ce),
                        frozenset(('u', 'a')): ('ear', 3)})


# ======================================================== mode: prod

def run_prod(seed=SEED, ndraw=3):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== prod: (BE-64) THE BRANCH-PRODUCT THEOREM, both directions, '
          f'seed {seed}')
    print('  FORWARD: at a joint draw, restriction to a topological branch is')
    print('  a (BE-30)(ii)-legal ear chain at the configuration\'s own flags.')
    print('  CONVERSE (the MIX test): chains drawn in INDEPENDENT runs at ONE')
    print('  fixed flag assignment glue to a legal configuration -- the direct')
    print('  test of the spec\'s weak link (b), a DEGREE-3 (and higher)')
    print('  TERMINAL, which the ear case never tested.')
    fwd_ok = fwd_bad = 0
    law_ok = 0
    pieces = R_BATTERY() + [('nested: ' + nested_piece()['name'],
                             nested_piece())]
    for nm, pc in pieces:
        H, u, v = pc['H'], pc['u'], pc['v']
        ok, W, br, ha = hcard_ok_piece(H, u, v)
        degmax = max(len(br_ints) for (_, _, br_ints) in
                     [(0, 0, [])] + [(0, 0, i) for (_, _, i) in br])
        hubdeg = {}
        for (z, zp, _i) in br:
            hubdeg[z] = hubdeg.get(z, 0) + 1
            hubdeg[zp] = hubdeg.get(zp, 0) + 1
        per = {}
        for tag in ('branch', 'bsharp-adj', 'widened'):
            drawn = 0
            for _ in range(ndraw * 10):
                if drawn == ndraw:
                    break
                pt = None
                if tag == 'branch':
                    got = sample_by_branches(H, u, v, rng)
                    pt = got[0] if got else None
                elif tag == 'bsharp-adj':
                    got = guarded_draw(H, u, v, rng,
                                       sampler=sample_piece_config_adj)
                    pt = got[0] if got else None
                else:
                    out = place_pencil_general(H, rng)
                    if out is not None:
                        cand = {k: tuple(x) for k, x in out[0].items()}
                        try:
                            assert_generic_star(H, cand)
                            okw, _w = verify_pencil_witness(H, cand)
                            pt = cand if okw else None
                        except AssertionError:
                            pt = None
                if pt is None:
                    continue
                planes = star_planes(H, pt, W)
                if planes is None:
                    continue
                for (z, zp, ints) in br:
                    good, why = chain_is_legal(pt, planes, z, zp, ints)
                    if good:
                        fwd_ok += 1
                    else:
                        fwd_bad += 1
                        print(f'     FORWARD FAILURE {nm} [{tag}] '
                              f'({z},{zp}): {why}')
                # (BE-59)(ii) on the TOPOLOGICAL skeleton, as spaces
                S, r, spans = branch_decorated_rho(H, pt, u, v, W, br)
                S0, r0, _dM, _rk = rho_bar_of(H, pt, u, v)
                assert same_space(S, S0) if (r or r0) else r == r0, \
                    f'(BE-64) branch-decorated law fails at {nm}'
                law_ok += 1
                drawn += 1
            per[tag] = drawn
        print(f'  {nm:42s} |V|={len(verts_of(H)):3d} hubs={len(W)} '
              f'branches={len(br)} maxhubdeg={max(hubdeg.values())} '
              f'hcard={ok} draws={per}')
    print(f'  FORWARD: {fwd_ok} branch restrictions legal, {fwd_bad} not.')
    print(f'  (BE-59)(ii) on the topological skeleton: {law_ok} draws, '
          f'asserted as spaces, 0 mismatches.')

    # --- the MIX test, the converse and weak link (b)
    print()
    print('  MIX (converse): chains from INDEPENDENT runs, glued.')
    mix_ok = mix_bad = 0
    mixed_shapes = 0
    for abc in [(3, 3, 3), (4, 4, 4), (5, 5, 5), (4, 5, 6), (2, 4, 5),
                (3, 5, 6), (2, 2, 3), (6, 6, 6)]:
        E = theta(*abc)
        W, br = hubs_and_branches(E, 'u', 'v')
        assert len(br) == 3, 'a theta has three branches'
        done = 0
        for _ in range(40):
            if done:
                break
            pu, Bu, pv, Bv = sample_flags(rng, 'nonadj')
            P, B = flag_assignment(W, br, rng,
                                   fixed={'u': (pu, Bu), 'v': (pv, Bv)})
            if P is None:
                continue
            runs = []
            for _k in range(len(br)):
                cand, ok = {}, True
                for (z, zp, ints) in br:
                    g = draw_branch(P, B, z, zp, len(ints), rng)
                    if g is None:
                        ok = False
                        break
                    for w, x in zip(ints, g):
                        cand[w] = x
                runs.append(cand if ok else None)
            if any(r is None for r in runs):
                continue
            mix = dict(P)
            for j, (z, zp, ints) in enumerate(br):
                for w in ints:
                    mix[w] = runs[j][w]
            aff = assemble(E, mix)
            if aff is None:
                continue
            # both gates passed inside `assemble`; now the law
            S, r, spans = branch_decorated_rho(E, aff, 'u', 'v', W, br)
            S0, r0, _d, _rk = rho_bar_of(E, aff, 'u', 'v')
            A = I6
            for sp in spans:
                A = isect(A, sp)
            assert same_space(S, S0) if (r or r0) else r == r0, 'mix: law'
            assert (same_space(A, S0) if (dim(A) or r0) else dim(A) == r0), \
                'mix: the P-node law fails'
            mix_ok += 1
            done = 1
            mixed_shapes += 1
            print(f'    theta{abc}: gates PASS, spans={[dim(s) for s in spans]}'
                  f' rho={r0} = dim(cap spans)={dim(A)}')
        if not done:
            mix_bad += 1
            print(f'    theta{abc}: NO MIXED DRAW under the try budget')
    print(f'  MIX: {mix_ok} glued configurations, {mix_bad} shapes without '
          f'a draw.  Every terminal here has degree 3 into the child.')
    print(f'  prod: {time.time() - t0:.1f}s')
    return fwd_bad == 0 and mix_bad == 0


# ======================================================== mode: theta

THETA_TRIPLES = [(3, 3, 3), (4, 4, 4), (5, 5, 5), (6, 6, 6), (4, 4, 5),
                 (4, 5, 5), (5, 5, 6), (5, 6, 6), (2, 2, 2), (2, 2, 3),
                 (2, 3, 3), (2, 4, 6), (2, 5, 6), (2, 6, 6), (3, 3, 4),
                 (3, 4, 4), (3, 6, 6), (4, 6, 6), (3, 3, 5), (3, 5, 6),
                 (7, 3, 3), (7, 4, 4), (7, 5, 5), (8, 3, 3), (7, 7, 7),
                 (8, 4, 4), (9, 3, 3), (7, 6, 6), (3, 4, 7), (3, 3, 10)]


def run_theta(seed=SEED, ndraw=3, triples=None):
    t0 = time.time()
    rng = random.Random(seed)
    triples = triples or THETA_TRIPLES
    print(f'== theta: (BE-66) the THETA CHILD -- the first per-child set past '
          f'ears, seed {seed}')
    print('  rho_bar = <C_1> cap <C_2> cap <C_3> (the P law, asserted as')
    print('  spaces); the generic dimension law max(0, sum min(a_j,6) - 12);')
    print('  and the welded-attainment obligation (BE-22)(iii)(a): rho = delta.')
    print(f"  {'(a,b,c)':>12} {'spans':>14} {'rho':>4} {'law':>4} "
          f"{'f':>3} {'g':>3} {'delta':>5} {'dimM':>5} {'att':>5}")
    law_bad = weld_bad = 0
    n = 0
    for abc in triples:
        E = theta(*abc)
        best = None
        for _ in range(ndraw):
            got = sample_by_branches(E, 'u', 'v', rng)
            if got is None:
                continue
            pt, B, W, br = got
            S0, r0, dM, _rk = rho_bar_of(E, pt, 'u', 'v')
            A = I6
            spans = []
            for (z, zp, ints) in br:
                sp = branch_span(pt, [z] + ints + [zp])
                spans.append(dim(sp))
                A = isect(A, sp)
            assert (same_space(A, S0) if (dim(A) or r0) else dim(A) == r0), \
                f'the P-node law fails at theta{abc}'
            if best is None or r0 < best[0]:
                best = (r0, sorted(spans), dM)
        if best is None:
            print(f'  {str(abc):>12}  NO DRAW')
            continue
        r0, spans, dM = best
        gp = max(0, sum(min(a, 6) for a in abc) - 12)
        f = d3(E)
        g = weld_d3(E, 'u', 'v')
        dl = f - g
        n += 1
        if r0 != gp:
            law_bad += 1
        if r0 != dl:
            weld_bad += 1
        print(f"  {str(abc):>12} {str(spans):>14} {r0:>4} {gp:>4} "
              f"{f:>3} {g:>3} {dl:>5} {dM:>5} {str(dM == 6 + f):>5}"
              f"{'' if r0 == gp else '  <-- LAW MISS'}"
              f"{'' if r0 == dl else '  <-- rho != delta'}")
    print(f'  the generic dimension law holds at {n - law_bad}/{n} triples;')
    print(f'  rho = delta (welded attainment, (BE-22)(iii)(a)) at '
          f'{n - weld_bad}/{n}.')
    print(f'  theta: {time.time() - t0:.1f}s')
    return law_bad == 0 and weld_bad == 0


# ======================================================== mode: small

def lam2_of(plane_basis):
    """Lambda^2 pi, the 3-space of lines inside the plane."""
    return span([[a[i] * b[j] - a[j] * b[i]
                  for (i, j) in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]]
                 for a, b in itertools.combinations(plane_basis, 2)])


def run_small(seed=SEED, ndraw=4, triples=None):
    t0 = time.time()
    rng = random.Random(seed)
    triples = triples or [(2, 2, 2), (2, 2, 3), (2, 3, 3), (3, 3, 3),
                          (3, 3, 4), (3, 4, 4), (4, 4, 4), (4, 4, 5),
                          (5, 5, 5), (3, 3, 6), (3, 6, 6), (2, 6, 6),
                          (3, 5, 5), (6, 6, 6), (3, 3, 5)]
    print(f'== small: (BE-66)(iii) the SMALL-BRANCH CORRECTION -- the spec\'s '
          f'weak link (a), seed {seed}')
    print('  (BE-30)(iii) does NOT stay inside its branch.  At pi_x = pi_y a')
    print('  length-3 branch has span EXACTLY Lambda^2 pi, so two of them have')
    print('  EQUAL spans and the P-node intersection does not drop.  Predicted')
    print('  law: max(ambient, confined), confined computed inside Lambda^2 pi')
    print('  with c(a) = dim(<C_a> cap Lambda^2 pi).')
    print(f"  {'(a,b,c)':>10} {'regime':>8} {'spans':>14} {'rho':>4} "
          f"{'ambient':>7} {'confined':>8} {'max':>4} {'att':>5}")
    miss = 0
    n = 0
    exceed = exceed_nonatt = 0
    for regime in ('nonadj', 'equal'):
        for abc in triples:
            E = theta(*abc)
            best = None
            for _ in range(ndraw):
                pu, Bu, pv, Bv = sample_flags(rng, regime)
                got = sample_by_branches(E, 'u', 'v', rng,
                                         fixed={'u': (pu, Bu),
                                                'v': (pv, Bv)})
                if got is None:
                    continue
                pt, B, W, br = got
                S0, r0, dM, _ = rho_bar_of(E, pt, 'u', 'v')
                spans = [branch_span(pt, [z] + i + [zp])
                         for (z, zp, i) in br]
                if regime == 'equal':
                    L2 = lam2_of(Bu)
                    assert dim(L2) == 3, 'Lambda^2 pi is not 3-dimensional'
                    cs = [dim(isect(sp, L2)) for sp in spans]
                    conf = max(0, sum(cs) - 2 * 3)
                else:
                    conf = 0
                amb = max(0, sum(dim(sp) for sp in spans) - 12)
                if best is None or r0 < best[0]:
                    best = (r0, [dim(sp) for sp in spans], amb, conf,
                            dM, dM == 6 + d3(E))
            if best is None:
                print(f'  {str(abc):>10} {regime:>8}  NO DRAW')
                continue
            r0, sp, amb, conf, dM, att = best
            pred = max(amb, conf)
            n += 1
            if r0 != pred:
                miss += 1
            if r0 > amb:
                exceed += 1
                if not att:
                    exceed_nonatt += 1
            print(f"  {str(abc):>10} {regime:>8} {str(sp):>14} {r0:>4} "
                  f"{amb:>7} {conf:>8} {pred:>4} {str(att):>5}"
                  f"{'' if r0 == pred else '  <-- PREDICTION MISS'}"
                  f"{'  <-- EXCEEDS general position' if r0 > amb else ''}")
    print(f'  the max(ambient, confined) law holds at {n - miss}/{n} rows.')
    print(f'  rows EXCEEDING general position: {exceed}; of those, '
          f'{exceed_nonatt} at a NON-ATTAINING configuration.')
    print('  Read the right way: an "EXCEEDS" row is an ACHIEVABLE decoration')
    print('  far from general position -- it is what (BE-62)(iii)\'s')
    print('  quantifier admits and (BE-22)(iii)\'s "both pieces attain"')
    print('  hypothesis excludes.  The att column is the measured proof of')
    print('  that exclusion, not an assertion.')
    print(f'  small: {time.time() - t0:.1f}s')
    return miss == 0


# ======================================================== mode: chart

def run_chart(seed=SEED, ndraw=2):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== chart: (BE-65) THE FLAG BASE -- the achievable-decoration space '
          f'IS the pencil chart, seed {seed}')
    print('  (CH-1) hypotheses per battery piece, and cross-sampler agreement')
    print('  between the branch sampler and widened.place_pencil_general (the')
    print('  code (CH-1) is written against).  Acceptance gate at BOTH:')
    print('  assert_generic_star AND verify_pencil_witness.')
    # (4) the deficiency-oracle cross-check
    print()
    print('  cap (4): the (6,6)-count-matroid weld oracle vs binduc\'s exact')
    print('  partition oracle def_by_partitions(together=):')
    tests = [(f'theta{abc}', theta(*abc), 'u', 'v')
             for abc in [(2, 2, 2), (2, 2, 3), (2, 3, 3), (3, 3, 3),
                         (2, 2, 4), (2, 3, 4), (3, 3, 4), (2, 4, 4)]]
    for m in range(1, 6):
        E = ([('u', 'w1')] + [(f'w{i - 1}', f'w{i}') for i in range(2, m + 1)]
             + [(f'w{m}', 'v')])
        tests.append((f'ear({m})', E, 'u', 'v'))
    tests.append(('C4 antipodes', [('a', 'u'), ('u', 'b'), ('b', 'v'),
                                   ('v', 'a')], 'a', 'b'))
    tests.append(('K4-uv', [('u', 'a'), ('u', 'b'), ('v', 'a'), ('v', 'b'),
                            ('a', 'b')], 'u', 'v'))
    bad = 0
    for nm, E, x, y in tests:
        V = sorted(verts_of(E), key=str)
        f1 = def_by_partitions(E, V)
        g1 = def_by_partitions(E, V, together=(x, y))
        f2, g2 = d3(E), weld_d3(E, x, y)
        if (f1, g1) != (f2, g2):
            bad += 1
            print(f'    {nm}: exact=({f1},{g1}) pebble=({f2},{g2})  MISMATCH')
    print(f'    {len(tests) - bad}/{len(tests)} agree, {bad} mismatches.')
    print()
    print(f"  {'piece':42s} {'hcard':>5} {'mindeg':>6} {'girth':>5} "
          f"{'branch rho':>11} {'widened rho':>12}")
    agree = disagree = 0
    for nm, pc in R_BATTERY():
        H, u, v = pc['H'], pc['u'], pc['v']
        ok, W, br, ha = hcard_ok_piece(H, u, v)
        nb = neighbors(H)
        mind = min(len(nb[z]) for z in verts_of(H))
        g = girth(H)
        ds = set()
        for _ in range(ndraw * 6):
            if len(ds) >= 1 and len(ds) * 6 <= ndraw * 6:
                pass
            got = sample_by_branches(H, u, v, rng)
            if got is not None:
                ds.add(rho_bar_of(H, got[0], u, v)[1])
            if len(ds) >= 2:
                break
        dw = set()
        for _ in range(60):
            out = place_pencil_general(H, rng)
            if out is None:
                continue
            pp = {k: tuple(x) for k, x in out[0].items()}
            try:
                assert_generic_star(H, pp)
            except AssertionError:
                continue
            okw, _ = verify_pencil_witness(H, pp)
            if not okw:
                continue
            dw.add(rho_bar_of(H, pp, u, v)[1])
            if len(dw) >= 2:
                break
        same = (min(ds) == min(dw)) if (ds and dw) else False
        if same:
            agree += 1
        else:
            disagree += 1
        print(f'  {nm:42s} {str(ok):>5} {mind:>6} {str(g):>5} '
              f'{str(sorted(ds)):>11} {str(sorted(dw)):>12}'
              f'{"" if same else "   <-- SAMPLERS DISAGREE"}')
    print(f'  cross-sampler agreement on the generic rho_bar: {agree} agree, '
          f'{disagree} disagree.')
    print('  Every piece above satisfies (CH-1)\'s three hypotheses, so')
    print('  (CH-1)(a)/(e) hand over irreducibility, rationality over Q and')
    print('  DENSE Q-POINTS for its configuration space -- ALREADY PROVED in')
    print('  §(K-chart); this direction re-uses it, it does not re-prove it.')
    print(f'  chart: {time.time() - t0:.1f}s')
    return disagree == 0 and bad == 0


# ======================================================== mode: attain

def run_attain(seed=SEED, ndraw=2):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== attain: (BE-67) HALF (B) -- (BE-22) at R-node peels whose child '
          f'is a THETA, seed {seed}')
    print('  BRNODE measured EAR children only (24/24).  Figures are')
    print('  constructor-capped (cap (3)); a shortfall would be "not attained')
    print('  by THIS constructor", never "does not attain" (F27).')
    npeel = gp_short = weld_short = 0
    for nm, pc in R_BATTERY():
        H, u, v = pc['H'], pc['u'], pc['v']
        fH = d3(H)
        drawn = 0
        for _ in range(ndraw * 8):
            if drawn == ndraw:
                break
            got = sample_by_branches(H, u, v, rng)
            if got is None:
                continue
            pt = got[0]
            _S, _r, dMH, _rk = rho_bar_of(H, pt, u, v)
            print(f'  {nm:42s} draw {drawn}: dim M(H)={dMH} '
                  f'(target {6 + fH}, attains={dMH == 6 + fH})')
            for i, (x, y, ce, kind) in enumerate(pc['children']):
                if kind == 'leaf':
                    continue
                side2 = ce
                side1 = []
                for j, (_a, _b, cf, _k) in enumerate(pc['children']):
                    if j != i:
                        side1 += cf
                f1, g1 = d3(side1), weld_d3(side1, x, y)
                f2, g2 = d3(side2), weld_d3(side2, x, y)
                d1, d2 = f1 - g1, f2 - g2
                S1, r1, dM1, _ = rho_bar_of(side1, pt, x, y)
                S2, r2, dM2, _ = rho_bar_of(side2, pt, x, y)
                dsum = dim(span(S1 + S2))
                assert dMH == dM1 + dM2 - 6 - dsum, \
                    '(BE-22)(i) fails at an R-node peel'
                npeel += 1
                weld = (r1 == d1, r2 == d2)
                if not all(weld):
                    weld_short += 1
                if dsum != min(d1 + d2, 6):
                    gp_short += 1
                print(f'      peel {kind:12s} at ({x},{y}): '
                      f'delta=({d1},{d2}) rho=({r1},{r2}) '
                      f'attain=({dM1 == 6 + f1},{dM2 == 6 + f2}) '
                      f'weld(rho=delta)={weld} dim(sum)={dsum} vs '
                      f'min(d1+d2,6)={min(d1 + d2, 6)} '
                      f'{"OK" if dsum == min(d1 + d2, 6) else "SHORT"}')
            drawn += 1
    print(f'  peels={npeel}  general-position shortfalls={gp_short}  '
          f'welded-attainment shortfalls={weld_short}')
    print('  A row that REACHES the criterion is a PER-PIECE THEOREM: rank <=')
    print('  target is universal and the conclusion existential, so one')
    print('  exact-Q configuration settles that piece ((BE-37)(i)(3)).  What')
    print('  is NOT settled is the CLASS statement over all pieces.')
    print(f'  attain: {time.time() - t0:.1f}s')
    return gp_short == 0 and weld_short == 0


# ======================================================== validate

def run_validate():
    t0 = time.time()
    print('===== bdecor validate: reduced tiers of all five modes =====')
    ok = True
    ok &= run_prod(ndraw=2)
    print()
    ok &= run_theta(ndraw=2, triples=THETA_TRIPLES[:14])
    print()
    ok &= run_small(ndraw=3, triples=[(2, 2, 3), (3, 3, 3), (3, 3, 4),
                                      (4, 4, 4), (4, 4, 5), (3, 3, 5)])
    print()
    ok &= run_chart(ndraw=1)
    print()
    ok &= run_attain(ndraw=1)
    print()
    print(f'===== validate {"GREEN" if ok else "RED"}, '
          f'{time.time() - t0:.1f}s =====')
    return ok


MODES = {'prod': run_prod, 'theta': run_theta, 'small': run_small,
         'chart': run_chart, 'attain': run_attain, 'validate': run_validate}

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if not args:
        print(__doc__)
        print('modes: ' + ' | '.join(MODES))
        sys.exit(0)
    for a in args:
        if a not in MODES:
            print(f'unknown mode {a!r}; modes: ' + ' | '.join(MODES))
            sys.exit(2)
        MODES[a]()
