"""
Phase 39 (K-pitch) -- the null-wrench test: motion-side transfer + the
pt(a)-sweep quartic.  Exact-Q validation of the derivations in
`notes/Pencil-informal.md` section (K-pitch).

Setting (as in `repin.py`): chain b - v - a - c (v, a degree 2; the
(K-tight)/(K-res) hard stratum has both ends b, c hubs), G' = G - v + ab,
target-rank pencil-generic G' seed, dim R_a = 1, stress load r = the a-block
of the ab-fiber part of the unique G'-stress.  Pairings: <.,.> Euclidean on
Plucker coordinates (the row model), B(x,y) = <x, star y> the Klein form,
Q(x) = B(x,x) (pitch quadric: Q(x) = 0 iff x is a line extensor).

Derived + validated here (per seed, all exact):

  (T1) two-port form: with H := G - v - a (terminals b, c),
       V_bc := span{m(b) - m(c) : m a motion of H} (generically 3-dim) and
       T := span{C_ab, C_ac} (the pencil of lines through pt(a) in
       plane(a,b,c); totally B-isotropic), the load r spans the EUCLIDEAN
       perp of W := V_bc + T (5-dim generically; V_bc cap T = 0 is forced
       by G' rigidity).  No stress appears on the right-hand side.
  (T2) sign law: let z span V_bc cap T^{perp B} (the "reciprocal twist":
       the unique H-relative-twist of b vs c doing no reciprocal work on
       either a-hinge).  In the hyperbolic plane T^{perp B}/T, star(r)-bar
       and z-bar are B-orthogonal, so  Q(r) = 0 iff Q(z) = 0, and when
       nonzero  Q(r) * Q(z) < 0  (opposite signs; the quotient form has
       discriminant -1 mod squares).
  (T3) motion form of the FULL escape criterion: route-A failure iff
       star(r) in Lambda^2 Pihat(b) (a line in panel b), route-B dually;
       combined failure iff star(r) = C(M), M = Pi(b) cap Pi(c) -- and,
       transferred by (T1),  escape iff  B(C(M), m) != 0 for SOME m in
       V_bc.  In particular Q(r) != 0 certifies BOTH routes at once.
  (T4) the pt(a)-sweep quartic: with everything but pt(a) fixed and
       pt(a) = p0 + t*d on M, q(t) := Q(z(t)) is a polynomial of degree
       <= 4 in t whose t^4 coefficient is Q(z_inf), z_inf computed from
       the lines (d,0)^ b-hat, (d,0)^ c-hat through M's direction point --
       an a-free leading term.  (K-pitch) at the split follows from
       q not identically 0 at one seed of the a-free chart data.

Drivers (foreground, one at a time):
    python3 notes/scripts/w4/pitch.py --control   # dbl-subdiv K4 + tight thetas
    python3 notes/scripts/w4/pitch.py --witness   # W19 / S29 residual splits
    python3 notes/scripts/w4/pitch.py --stratum   # (def 0, dim R_a 1) pool pairs
    python3 notes/scripts/w4/pitch.py --sweep     # the quartic q(t), 3 habitats
"""
import os
import random
import sys
from fractions import Fraction as F

_HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (_HERE, os.path.join(_HERE, '..', 'kbare'),
           os.path.join(_HERE, '..', 'escape')):
    sys.path.insert(0, _p)

from repin import (seed_probe, hodge_star, span_basis, in_span, rank_at_V,
                   lambda2_plane)
from widened import (orient, removeV, splitOff, place_pencil_general,
                     split_report, residuals, prime_pool, W19)
from nogood_subdiv import deficiency, hub_set
from saferes import w29, split_usable
from pencil_escape import (build_rigidity, rank, left_nullspace, nullspace,
                           wedge2, hat, dot, rquat, double_subdivide)
from localtest import meet_line
from kbare_common import verts_of


# ---------------- Klein form ------------------------------------------------

def klein(x, y):
    """B(x,y) = <x, star y>: the Klein (Pluecker) symmetric bilinear form."""
    return dot(x, hodge_star(y))


def Q(x):
    return klein(x, x)


def cross3(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0]]


# ---------------- theta graphs (tight members with a length-3 path) --------

def theta_edges(lengths):
    """Theta graph: two hubs 0, 1 joined by paths of the given edge-lengths.
    index(G) = 12 - sum(lengths), so sum = 12 is (K)-tight."""
    edges = []
    nxt = 10
    for L in lengths:
        prev = 0
        for k in range(L - 1):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
        edges.append((prev, 1))
        nxt += 1
    return edges


# ---------------- the motion-side objects ----------------------------------

def H_motions_vbc(edges, v, a, b, c, placed):
    """(V_bc basis, dim of H motion space, |V(H)| sanity) for H = G - v - a."""
    Hed = [e for e in edges if v not in e and a not in e]
    VH = sorted(verts_of(Hed), key=str)
    assert len(VH) == len(verts_of(edges)) - 2, "H lost a vertex"
    rows, er, C, idx, n = build_rigidity({'edges': Hed, 'V': VH, 'pt': placed})
    motions = nullspace(rows)
    ib, ic = 6 * idx[b], 6 * idx[c]
    D = [[m[ib + k] - m[ic + k] for k in range(6)] for m in motions]
    return span_basis(D), len(motions), len(VH)


def z_from(Vbc, Cab, Cac):
    """z spanning V_bc cap T^{perp B}, via the 3-dim cross product of the two
    linear conditions B(., C_ab) = B(., C_ac) = 0 on a 3-dim V_bc.  Returns
    (z, coeffs) or (None, None) when the conditions are dependent."""
    if len(Vbc) != 3:
        return None, None
    row_ab = [klein(m, Cab) for m in Vbc]
    row_ac = [klein(m, Cac) for m in Vbc]
    co = cross3(row_ab, row_ac)
    if all(x == 0 for x in co):
        return None, None
    z = [sum((co[i] * Vbc[i][k] for i in range(3)), F(0)) for k in range(6)]
    return z, co


# ---------------- the per-seed transfer check --------------------------------

def transfer_probe(edges, v, seed):
    """Validate (T1)-(T3) at one target-rank G' seed.  Returns a dict or
    None (invalid seed).  All checks are asserts; a violation raises."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if p['dim R_a'] != 1:
        return {'seed': seed, 'skip': f"dim R_a = {p['dim R_a']}"}
    r = Ra_basis[0]
    assert any(x != 0 for x in r)
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab2, Cac = wedge2(ah, bh), wedge2(ah, ch)
    assert Cab2 == Cab or Cab2 == [-x for x in Cab]
    # T is totally B-isotropic (shared point pt(a)):
    assert Q(Cab2) == 0 and Q(Cac) == 0 and klein(Cab2, Cac) == 0
    # r is reciprocal to both a-hinges (Euclidean = row model):
    assert dot(r, Cab2) == 0 and dot(r, Cac) == 0

    Vbc, dimMot, nVH = H_motions_vbc(edges, v, a, b, c, placed)
    out = {'seed': seed, 'dim Vbc': len(Vbc), 'dim mot(H)': dimMot}
    # (T1) r perp_E V_bc:
    assert all(dot(r, m) == 0 for m in Vbc), "r not perp V_bc"
    # V_bc cap T = 0 (forced by G' rigidity at a target-rank seed):
    W = span_basis(Vbc + [Cab2, Cac])
    assert len(W) == len(Vbc) + 2, "V_bc meets T"
    out['dim W'] = len(W)
    if len(W) == 5:
        Wperp = nullspace(W)
        assert len(Wperp) == 1 and in_span(r, Wperp), "W^perp != <r>"
        out['T1'] = True
    else:
        out['T1'] = f'dim W = {len(W)} (r in W^perp checked only)'
        assert all(dot(r, w) == 0 for w in [Cab2, Cac]), out

    # (T2) the sign law, via z:
    z, co = z_from(Vbc, Cab2, Cac)
    Qr = Q(r)
    out['Q(r)'] = Qr
    if z is None:
        out['T2'] = 'z degenerate (conditions dependent on V_bc)'
    else:
        Qz = Q(z)
        out['Q(z)'] = Qz
        sr = hodge_star(r)
        zbar_ok = not in_span(z, [Cab2, Cac])
        sbar_ok = not in_span(sr, [Cab2, Cac])
        out['side ok'] = zbar_ok and sbar_ok
        if zbar_ok and sbar_ok and len(W) == 5:
            # B-orthogonality of star(r)-bar and z-bar in T^perp/T:
            # B(star r, z) = <r, z> = 0 is (T1); assert it explicitly.
            assert dot(r, z) == 0
            assert (Qr == 0) == (Qz == 0), (Qr, Qz)
            if Qr != 0:
                assert Qr * Qz < 0, (Qr, Qz)
            out['T2'] = True
        else:
            out['T2'] = 'side conditions failed'

    # (T3) per-route decomposability + the motion form of the full criterion:
    critA, critB = p['critA'], p['critB']
    out['critA'], out['critB'] = critA, critB
    if Qr != 0:
        assert critA and critB, "pitch != 0 must certify both routes"
        out['pitch certifies'] = True
    if b in hubsG and b in nrm and c in hubsG and c in nrm:
        p0, d = meet_line(pt[b], nrm[b], pt[c], nrm[c])
        m0, m1 = p0, [p0[i] + d[i] for i in range(3)]
        CM = wedge2(hat(m0), hat(m1))
        # C(M) is auto-reciprocal to T (M passes through pt(a)):
        assert klein(CM, Cab2) == 0 and klein(CM, Cac) == 0
        esc_motion = any(klein(CM, m) != 0 for m in Vbc)
        assert esc_motion == (critA or critB), \
            "motion-form combined criterion mismatch"
        out['T3'] = True
        # per-route star(r)-in-panel form (route A):
        L2b = lambda2_plane(pt[b], nrm[b], random.Random(555 + seed))
        starr_in_panel_b = in_span(hodge_star(r), L2b)
        assert (not critA) == starr_in_panel_b, "route-A star-form mismatch"
    # Gram rank of the Klein form on V_bc (3 = nondegenerate 3-system):
    gram = [[klein(x, y) for y in Vbc] for x in Vbc]
    out['rank Q|Vbc'] = rank(gram)
    return out


def run_transfer(name, edges, v, seeds, need=5):
    print(f"== {name}: motion-side transfer (T1)-(T3) ==")
    n_ok = n_pitch = 0
    for seed in seeds:
        o = transfer_probe(edges, v, seed)
        if o is None:
            continue
        if 'skip' in o:
            print(f"  seed {seed}: skipped ({o['skip']})")
            continue
        n_ok += 1
        pz = o.get('Q(z)', None)
        print(f"  seed {seed}: dimVbc={o['dim Vbc']} dimW={o['dim W']} "
              f"T1={o['T1']} T2={o['T2']} T3={o.get('T3', '-')} "
              f"gramQ={o['rank Q|Vbc']} Q(r)={'0' if o['Q(r)'] == 0 else 'nz'}"
              f" Q(z)={'-' if pz is None else ('0' if pz == 0 else 'nz')} "
              f"critA={o['critA']} critB={o['critB']}")
        n_pitch += (o['Q(r)'] != 0)
        if n_ok >= need:
            break
    print(f"  -- {name}: {n_ok} seeds, pitch nonzero on {n_pitch}/{n_ok}")
    return n_ok, n_pitch


# ---------------- drivers ----------------------------------------------------

def control():
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    tot = pit = 0
    n, k = run_transfer('dbl-subdiv K4 (tight)', E, chains[0][1],
                        range(440, 480), need=6)
    tot += n; pit += k
    for lengths in ((3, 4, 5), (3, 3, 6)):
        E = theta_edges(lengths)
        assert deficiency(E) == 0, lengths
        n, k = run_transfer(f'theta{lengths} (tight)', E, 10,
                            range(200, 240), need=5)
        tot += n; pit += k
    print(f"CONTROL OK: transfer validated on {tot} seeds; "
          f"pitch nonzero on {pit}/{tot}")


def witness():
    tot = pit = 0
    for name, G, seeds, need in (('W19', W19(), range(3000, 3040), 3),
                                 ('S29', w29(), range(3000, 3030), 2)):
        v = split_usable(G)[0][0][0]
        n, k = run_transfer(f'{name} split v={v} (residual)', G, v,
                            seeds, need=need)
        tot += n; pit += k
    print(f"WITNESS OK: transfer validated on {tot} residual seeds; "
          f"pitch nonzero on {pit}/{tot}")


def stratum(pairs_n=4, maxv=22):
    print("== residual pool, (def 0, dim R_a 1) stratum ==")
    pairs = []
    for E, _ in residuals(prime_pool()):
        if len(verts_of(E)) > maxv or deficiency(E) != 0:
            continue
        for (v, _, _) in split_usable(E)[0]:
            d = split_report(E, v)
            if d is not None and d['dim R_a'] == 1:
                pairs.append((E, v))
    rng = random.Random(20260804)
    rng.shuffle(pairs)
    tot = pit = 0
    for (E, v) in pairs[:pairs_n]:
        n, k = run_transfer(f'|V|={len(verts_of(E))} v={v}', E, v,
                            range(5000, 5030), need=2)
        tot += n; pit += k
    print(f"STRATUM OK: transfer validated on {tot} pool seeds; "
          f"pitch nonzero on {pit}/{tot}")


# ---------------- (T5) longer companions: the Lambda-compression ------------

def coords_in(S, vec):
    """Coordinates of `vec` in the (independent) spanning list S, or None."""
    rows6 = [[Si[r] for Si in S] + [-vec[r]] for r in range(6)]
    for x in nullspace(rows6):
        if x[-1] != 0:
            return [xi / x[-1] for xi in x[:-1]]
    return None


def det3(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def cross4(l1, l2, l3):
    """omega with [l1; l2; l3] . omega = 0 (Laplace cofactors, 3x4)."""
    A = [l1, l2, l3]
    out = []
    for i in range(4):
        cols = [j for j in range(4) if j != i]
        minor = [[A[r][j] for j in cols] for r in range(3)]
        out.append((F(-1) ** (i + 1)) * det3(minor))
    return out


def paths_graph(bc_paths, labeled_paths):
    """Build a subdivision graph from hub-path specs.
    `bc_paths`: list of lengths of b(=0)-c(=1) paths; `labeled_paths`:
    list of (h1, h2, length) for other hub pairs. Returns (edges, paths)
    where paths maps an index to its full vertex list."""
    edges, paths, nxt = [], {}, 100
    specs = [(0, 1, L) for L in bc_paths] + list(labeled_paths)
    for k, (h1, h2, L) in enumerate(specs):
        vs = [h1]
        prev = h1
        for _ in range(L - 1):
            edges.append((prev, nxt))
            vs.append(nxt)
            prev = nxt
            nxt += 1
        edges.append((prev, h2))
        vs.append(h2)
        paths[k] = vs
    return edges, paths


def nt21():
    """A non-theta tight habitat: hubs b=0, c=1, u=2, w=3; b-c paths of
    length 3 (the split chain) and 4 (the companion); plus b-u:4, u-c:4,
    b-w:3, w-c:3, u-w:3.  Sum ell = 24 = 6 c(G-hub) (c = 4): tight."""
    return paths_graph([3, 4], [(0, 2, 4), (2, 1, 4), (0, 3, 3),
                                (3, 1, 3), (2, 3, 3)])


def companion4_probe(edges, v, seed, comp_path, far_arc=None):
    """(T5) at one seed: with a length-4 companion b-x1-x2-x3-c, the far
    data enters Q(z) only through the annihilator covector lambda of V_bc
    inside span(C1..C4), and Q(z) = 2(w0 w2 g1 + w1 w3 g2 + w0 w3 g3)."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None or p['dim R_a'] != 1:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab0, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    assert comp_path[0] == b and comp_path[-1] == c and len(comp_path) == 5
    C = [wedge2(hat(placed[comp_path[i]]), hat(placed[comp_path[i + 1]]))
         for i in range(4)]
    assert rank(C) == 4, "companion line span degenerate"
    # Gram zeros (consecutive lines meet):
    for i in range(3):
        assert klein(C[i], C[i + 1]) == 0
    g1, g2, g3 = klein(C[0], C[2]), klein(C[1], C[3]), klein(C[0], C[3])
    Vbc, _, _ = H_motions_vbc(edges, v, a, b, c, placed)
    if len(Vbc) != 3:
        return None
    # path-sum containment V_bc <= span(C), and the far covector lambda:
    Vco = []
    for m in Vbc:
        co = coords_in(C, m)
        assert co is not None, "V_bc escapes the companion span"
        Vco.append(co)
    lam_space = nullspace(Vco)
    assert len(lam_space) == 1, "far covector not unique"
    lam = lam_space[0]
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab, Cac = wedge2(ah, bh), wedge2(ah, ch)
    mrow = [klein(Ci, Cab) for Ci in C]
    nrow = [klein(Ci, Cac) for Ci in C]
    assert mrow[0] == 0 and nrow[3] == 0, "structural zeros"
    om = cross4(lam, mrow, nrow)
    for row in (lam, mrow, nrow):
        assert dot(row, om) == 0
    z4 = [sum((om[i] * C[i][k] for i in range(4)), F(0)) for k in range(6)]
    if all(x == 0 for x in z4):
        return None
    # z4 is THE reciprocal twist:
    z, _ = z_from(Vbc, Cab, Cac)
    assert z is not None and in_span(z4, span_basis([z])), \
        "Lambda-compressed z differs from computed z"
    Qz4 = 2 * (om[0] * om[2] * g1 + om[1] * om[3] * g2 + om[0] * om[3] * g3)
    assert Q(z4) == Qz4, "Lambda-quadratic formula"
    r = Ra_basis[0]
    Qr = Q(r)
    assert (Qr == 0) == (Qz4 == 0)
    if Qr != 0:
        assert Qr * Qz4 < 0
    out = {'seed': seed, 'Q!=0': Qz4 != 0}
    # theta bonus: lambda is the far arc's span normal, restricted:
    if far_arc is not None:
        D = [wedge2(hat(placed[far_arc[i]]), hat(placed[far_arc[i + 1]]))
             for i in range(len(far_arc) - 1)]
        nu = nullspace(span_basis(D))
        if len(nu) == 1:
            lam2 = [dot(Ci, nu[0]) for Ci in C]
            assert in_span(lam2, span_basis([lam])), \
                "theta far-covector cross-check"
            out['nu check'] = True
    return out


def companion4():
    print("== (T5) length-4 companion: the Lambda-compression ==")
    E = theta_edges((3, 4, 5))
    comp = [0, 13, 14, 15, 1]
    far = [0, 17, 18, 19, 20, 1]
    n_ok = 0
    for seed in range(200, 240):
        o = companion4_probe(E, 10, seed, comp, far_arc=far)
        if o is None:
            continue
        n_ok += 1
        print(f"  theta(3,4,5) seed {seed}: lambda unique, z4 == z, "
              f"Q = Lambda-quadratic OK, Q != 0: {o['Q!=0']}, "
              f"nu cross-check: {o.get('nu check', '-')}")
        if n_ok >= 3:
            break
    assert n_ok >= 3
    # the non-theta habitat:
    E, paths = nt21(), None
    E2, pmap = paths_graph([3, 4], [(0, 2, 4), (2, 1, 4), (0, 3, 3),
                                    (3, 1, 3), (2, 3, 3)])
    from nogood_subdiv import deficiency as defic
    assert defic(E2) == 0, "NT21 not tight-rigid"
    # hnoRigid at branch granularity (a rigid subgraph is a union of
    # whole branches -- its own 2-core):
    import itertools as it
    nbr = len(pmap)
    for rsub in range(1, 2 ** nbr - 1):
        sel = [pmap[k] for k in range(nbr) if rsub & (1 << k)]
        vs = set(v_ for p_ in sel for v_ in p_)
        sub = [e for e in E2 if e[0] in vs and e[1] in vs]
        if not sub or len(verts_of(sub)) < 3:
            continue
        if defic(sub) == 0 and len(verts_of(sub)) < len(verts_of(E2)):
            # a vertex-proper rigid branch union would break hnoRigid
            raise AssertionError(f"NT21 has a proper rigid subgraph {rsub}")
    print("  NT21: tight (def 0), no proper rigid branch-union "
          f"(2^{nbr} checked)")
    split_v = pmap[0][1]           # first interior of the length-3 b-c path
    comp2 = pmap[1]
    n_ok = 0
    for seed in range(300, 340):
        o = companion4_probe(E2, split_v, seed, comp2)
        if o is None:
            continue
        n_ok += 1
        print(f"  NT21 seed {seed}: lambda unique, z4 == z, "
              f"Q = Lambda-quadratic OK, Q != 0: {o['Q!=0']}")
        if n_ok >= 2:
            break
    assert n_ok >= 2
    print("COMPANION4 OK: Lambda-compression validated "
          "(theta(3,4,5) + NT21)")


# ---------------- the companion-chain closed form (theta(3,3,6)) ------------

def det4(rows):
    from pencil_escape import rref
    M = [r[:] for r in rows]
    det = F(1)
    for c in range(4):
        piv = next((i for i in range(c, 4) if M[i][c] != 0), None)
        if piv is None:
            return F(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det *= M[c][c]
        inv = F(1) / M[c][c]
        for i in range(c + 1, 4):
            f = M[i][c] * inv
            if f != 0:
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return det


def bracket(placed, p, q, r_, s):
    return det4([hat(placed[p]), hat(placed[q]), hat(placed[r_]),
                 hat(placed[s])])


def theta336(need=4):
    """The companion-chain closed form: at theta(3,3,6), the split chain
    b-v-a-c has a PARALLEL length-3 companion b-x-y-c, so the path-sum
    containment V_bc <= span(lines of any b-c path of H) pins
    V_bc = <C(bx), C(xy), C(yc)>, and the reciprocal twist's pitch is the
    bracket MONOMIAL
        Q(z) = 2 [x,y,a,b][b,x,a,c][y,c,a,b][x,y,a,c][b,x,y,c].
    Validated exactly per seed, plus the pairing-bracket dictionary
    B(C(uv), C(pq)) = det[u^,v^,p^,q^]."""
    E = theta_edges((3, 3, 6))
    v = 10                      # first interior of path 1; a = 11
    n_ok = 0
    for seed in range(200, 260):
        p = seed_probe(E, v, seed, nplace=0)
        if p is None or p['dim R_a'] != 1:
            continue
        placed, pt, nrm, hubs, nb, U, Ra_basis, Cab0, tgtG, hubsG = p['_ctx']
        a, b, c = p['a'], p['b'], p['c']
        assert (a, b, c) == (11, 0, 1)
        x, y = 13, 14           # companion path b=0 - 13 - 14 - c=1
        # pairing-bracket dictionary (spot check on this seed's points):
        for (u1, u2, w1, w2) in ((b, x, a, b), (x, y, a, c), (b, x, y, c)):
            lhs = klein(wedge2(hat(placed[u1]), hat(placed[u2])),
                        wedge2(hat(placed[w1]), hat(placed[w2])))
            rhs = det4([hat(placed[u1]), hat(placed[u2]),
                        hat(placed[w1]), hat(placed[w2])])
            assert lhs == rhs, "pairing-bracket dictionary"
        C1 = wedge2(hat(placed[b]), hat(placed[x]))
        C2 = wedge2(hat(placed[x]), hat(placed[y]))
        C3 = wedge2(hat(placed[y]), hat(placed[c]))
        Vbc, _, _ = H_motions_vbc(E, v, a, b, c, placed)
        if len(Vbc) != 3:
            continue
        # V_bc = <C1, C2, C3> (path-sum containment + dimension):
        assert all(in_span(Ci, Vbc) for Ci in (C1, C2, C3)), \
            "V_bc != companion-path line span"
        ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
        Cab, Cac = wedge2(ah, bh), wedge2(ah, ch)
        # closed-form z in the C-basis:
        u_ = bracket(placed, x, y, a, b)
        w_ = bracket(placed, y, c, a, b)
        s_ = bracket(placed, b, x, a, c)
        t_ = bracket(placed, x, y, a, c)
        zf = [(-w_ * t_) * C1[k] + (w_ * s_) * C2[k] + (-u_ * s_) * C3[k]
              for k in range(6)]
        assert any(q != 0 for q in zf)
        assert klein(zf, Cab) == 0 and klein(zf, Cac) == 0
        z, _ = z_from(Vbc, Cab, Cac)
        assert z is not None and in_span(zf, span_basis([z])), \
            "closed-form z differs from computed z"
        m_ = bracket(placed, b, x, y, c)
        Qzf = 2 * u_ * s_ * w_ * t_ * m_
        assert Q(zf) == Qzf, "bracket-monomial factorization"
        r = Ra_basis[0]
        Qr = Q(r)
        assert (Qr == 0) == (Qzf == 0)
        if Qr != 0:
            assert Qr * Qzf < 0
        n_ok += 1
        print(f"  seed {seed}: V_bc = <C1,C2,C3> OK; Q(z) = 2*u*s*w*t*m "
              f"with brackets nonzero: "
              f"{all(q != 0 for q in (u_, s_, w_, t_, m_))}; "
              f"sign law vs Q(r): OK")
        if n_ok >= need:
            break
    assert n_ok >= 3, "too few valid seeds"
    print(f"THETA336 OK: bracket-monomial closed form validated on "
          f"{n_ok} seeds")


# ---------------- the pt(a)-sweep quartic (T4) -------------------------------

def lagrange_coeffs(pts):
    """Exact interpolating polynomial coefficients (low->high) through
    5 points [(t, q)] -- degree <= 4."""
    ts = [t for t, _ in pts]
    n = len(ts)
    coeffs = [F(0)] * n
    for i, (ti, qi) in enumerate(pts):
        den = F(1)
        Li = [F(1)]
        for j, tj in enumerate(ts):
            if j == i:
                continue
            den *= (ti - tj)
            new = [F(0)] * (len(Li) + 1)
            for k, ck in enumerate(Li):
                new[k + 1] += ck
                new[k] += ck * (-tj)
            Li = new
        for k in range(len(Li)):
            coeffs[k] += qi * Li[k] / den
    return coeffs


def poly_eval(coeffs, t):
    acc = F(0)
    for ck in reversed(coeffs):
        acc = acc * t + ck
    return acc


def sweep_one(name, edges, v, seeds):
    """(T4) at the first valid seed: interpolate q(t) = Q(z(t)), check
    degree <= 4, leading coefficient = Q(z_inf), q not identically zero,
    and tie q's sign law to the recomputed stress at two valid t."""
    print(f"== {name}: pt(a)-sweep quartic ==")
    for seed in seeds:
        p = seed_probe(edges, v, seed, nplace=0)
        if p is None or p['dim R_a'] != 1:
            continue
        placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
        a, b, c = p['a'], p['b'], p['c']
        if not (b in hubsG and b in nrm and c in hubsG and c in nrm):
            continue
        Vbc, _, _ = H_motions_vbc(edges, v, a, b, c, placed)
        if len(Vbc) != 3:
            continue
        p0, d = meet_line(pt[b], nrm[b], pt[c], nrm[c])
        bh, ch = hat(placed[b]), hat(placed[c])

        def z_at(pa4):
            return z_from(Vbc, wedge2(pa4, bh), wedge2(pa4, ch))[0]

        def q_at(t):
            pa = [p0[i] + t * d[i] for i in range(3)]
            z = z_at(hat(pa))
            return F(0) if z is None else Q(z)

        ts = [F(0), F(1), F(-1), F(2), F(-2)]
        coeffs = lagrange_coeffs([(t, q_at(t)) for t in ts])
        # degree check at extra points:
        for t in (F(3), F(-3), F(1, 2), F(5)):
            assert poly_eval(coeffs, t) == q_at(t), "degree > 4?!"
        # leading coefficient = the a-free direction-point form:
        dhat4 = [d[0], d[1], d[2], F(0)]
        zinf = z_from(Vbc, wedge2(dhat4, bh), wedge2(dhat4, ch))[0]
        qinf = F(0) if zinf is None else Q(zinf)
        assert coeffs[4] == qinf, (coeffs[4], qinf)
        nz = any(x != 0 for x in coeffs)
        print(f"  seed {seed}: q(t) degree<=4 coeffs "
              f"{['nz' if x != 0 else '0' for x in coeffs]} "
              f"(low->high); q4 == Q(z_inf): True; q4 != 0: {qinf != 0}; "
              f"q not identically 0: {nz}")
        assert nz, "q(t) identically zero at this seed"
        # tie to the stress at two valid t (full G'-recompute):
        Gp = splitOff(edges, v, a, b)
        Vp = sorted(verts_of(Gp), key=str)
        tgtGp = 6 * (len(Vp) - 1) - deficiency(Gp)
        checked = 0
        for t in (F(3), F(-4), F(7), F(-6), F(9)):
            pl2 = dict(placed)
            pl2[a] = [p0[i] + t * d[i] for i in range(3)]
            rk, rows, er, idx = rank_at_V(Gp, pl2, Vp)
            if rk != tgtGp:
                continue
            e_ab = next(e for e in er if set(e) == {a, b})
            base_a = 6 * idx[a]
            Ra = []
            for lam in left_nullspace(rows):
                rr = [F(0)] * 6
                for ri in er[e_ab]:
                    for k in range(6):
                        rr[k] += lam[ri] * rows[ri][base_a + k]
                Ra.append(rr)
            Rb = span_basis(Ra)
            if len(Rb) != 1:
                continue
            rt = Rb[0]
            Qrt, qt = Q(rt), q_at(t)
            assert (Qrt == 0) == (qt == 0), (t, Qrt, qt)
            if Qrt != 0:
                assert Qrt * qt < 0, (t, Qrt, qt)
            checked += 1
            print(f"    t={t}: stress recomputed, sign law "
                  f"Q(r(t))*q(t) < 0 or both 0: True")
            if checked >= 2:
                break
        assert checked >= 1, "no valid t for the stress cross-check"
        return True
    print(f"  {name}: no usable seed found")
    return False


def sweep():
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    ok = sweep_one('dbl-subdiv K4 (tight)', E, chains[0][1], range(440, 470))
    ok &= sweep_one('theta(3,4,5) (tight)', theta_edges((3, 4, 5)), 10,
                    range(200, 230))
    # W19's splits all have a non-hub chain end (no meet line to sweep);
    # the both-ends-hubs residual-shaped habitats here are theta(3,3,6)
    # (contains a rigid C6) and S29's split o0_0.
    ok &= sweep_one('theta(3,3,6) (residual-shaped)', theta_edges((3, 3, 6)),
                    10, range(200, 230))
    ok &= sweep_one('S29 split o0_0 (residual)', w29(), 'o0_0',
                    range(3002, 3012))
    print("SWEEP OK" if ok else "SWEEP: some habitat unusable")


# ---------------- the slide-in degeneration (route-1 probe) -----------------

def rows_from_lines(edges, Cmap, V):
    """Rigidity rows from EXPLICIT line extensors per edge (the projective
    limit configuration; magnitudes normalized away)."""
    from pencil_escape import perp_basis
    idx = {v_: k for k, v_ in enumerate(V)}
    ncol = 6 * len(V)
    rows = []
    for e in edges:
        Ce = Cmap[e]
        assert any(x != 0 for x in Ce), f"zero limit line at {e}"
        for w_ in perp_basis(Ce):
            row = [F(0)] * ncol
            bu, bw = 6 * idx[e[0]], 6 * idx[e[1]]
            for k in range(6):
                row[bu + k] += w_[k]
                row[bw + k] -= w_[k]
            rows.append(row)
    return rows, idx


def vbc_from_lines(Hed, Cmap, b, c):
    VH = sorted(verts_of(Hed), key=str)
    rows, idx = rows_from_lines(Hed, Cmap, VH)
    motions = nullspace(rows)
    ib, ic = 6 * idx[b], 6 * idx[c]
    D = [[m[ib + k] - m[ic + k] for k in range(6)] for m in motions]
    return span_basis(D)


def slide_probe(edges, v, seed, slide_map,
                eps_list=(F(1), F(1, 4), F(1, 16), F(1, 64))):
    """The slide-in family: each slid interior x moves on
    pt(hub) + eps*(x0 - pt(hub)) (chart-legal: the segment stays in the
    hub's panel).  Track V_bc, z, Q(z) at eps in {1, 1/4, 1/16, 1/64} and
    at the projective LIMIT configuration (hub-incident hinges keep their
    original lines; slid-slid hinges become hub chords)."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None or p['dim R_a'] != 1:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab0, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab, Cac = wedge2(ah, bh), wedge2(ah, ch)
    Hed = [e for e in edges if v not in e and a not in e]
    report = {'seed': seed, 'eps': []}
    bases = {}
    for eps in eps_list:
        pl = dict(placed)
        for x, h in slide_map.items():
            pl[x] = [pt[h][i] + eps * (placed[x][i] - pt[h][i])
                     for i in range(3)]
        Vbc, dimMot, _ = H_motions_vbc(edges, v, a, b, c, pl)
        report['dim mot ' + str(eps)] = dimMot
        if len(Vbc) != 3:
            report['eps'].append((eps, f'dim V_bc = {len(Vbc)}'))
            continue
        z, _ = z_from(Vbc, Cab, Cac)
        qz = None if z is None else Q(z)
        report['eps'].append((eps, 'Q!=0' if qz not in (None, 0) else
                              ('Q=0' if qz == 0 else 'z degen')))
        bases[eps] = Vbc
    # the limit configuration.  Per-edge rule (derived in the workbook):
    #   * (hub u, slid x -> u): the hinge line is CONSTANT along the slide
    #     (u^ ^ (u^ + eps d) = eps * u^ ^ x0^) -- keep the original line;
    #   * (slid p -> h_p, slid q -> h_q), h_p != h_q: the chord h_p ^ h_q;
    #   * (slid p -> h_p, fixed q), q != h_p: the line h_p ^ q0;
    #   * (fixed, fixed): unchanged.
    Cmap = {}
    ok = True
    for e in Hed:
        p_, q_ = e
        tp = slide_map.get(p_)
        tq = slide_map.get(q_)
        if tp is not None and tq is not None:
            Ce = wedge2(hat(pt[tp]), hat(pt[tq]))
        elif tp is not None and q_ == tp or tq is not None and p_ == tq:
            Ce = wedge2(hat(placed[p_]), hat(placed[q_]))   # constant line
        elif tp is not None:
            Ce = wedge2(hat(pt[tp]), hat(placed[q_]))
        elif tq is not None:
            Ce = wedge2(hat(placed[p_]), hat(pt[tq]))
        else:
            Ce = wedge2(hat(placed[p_]), hat(placed[q_]))
        if all(x == 0 for x in Ce):
            ok = False
            break
        Cmap[e] = Ce
    if not ok:
        report['limit'] = 'coincident limit points'
        return report
    VH = sorted(verts_of(Hed), key=str)
    rows_lim, idx_lim = rows_from_lines(Hed, Cmap, VH)
    mot_lim = nullspace(rows_lim)
    report['dim mot limit'] = len(mot_lim)
    ibl, icl = 6 * idx_lim[b], 6 * idx_lim[c]
    Vlim = span_basis([[m[ibl + k] - m[icl + k] for k in range(6)]
                       for m in mot_lim])
    report['dim V_bc limit'] = len(Vlim)
    if len(Vlim) == 3:
        zlim, _ = z_from(Vlim, Cab, Cac)
        report['Q(z) limit'] = None if zlim is None else Q(zlim)
        report['z limit'] = ('degen' if zlim is None else
                             ('null' if Q(zlim) == 0 else 'pitched'))
        # convergence evidence, basis-invariantly: the normalized Pluecker
        # coordinates of the 3-plane V_bc(eps) approach the limit plane's:
        pl_lim = plucker3(Vlim)
        difs = []
        for eps in sorted(bases, reverse=True)[-3:]:
            d_ = max(abs(x - y) for x, y in zip(plucker3(bases[eps]), pl_lim))
            difs.append((eps, d_))
        report['convergence'] = difs
    return report


def plucker3(basis):
    """Normalized Pluecker coordinates of a 3-plane in K^6 (20 maximal
    minors of the 3x6 basis matrix; scaled so the largest |entry| is 1,
    with the first nonzero entry positive) -- basis-invariant."""
    import itertools as it
    assert len(basis) == 3
    ps = [det3([[basis[r][cix] for cix in cols] for r in range(3)])
          for cols in it.combinations(range(6), 3)]
    mx = max(abs(x) for x in ps)
    assert mx != 0
    ps = [x / mx for x in ps]
    lead = next(x for x in ps if x != 0)
    return [x if lead > 0 else -x for x in ps]


def slide_line(name, seed, rep):
    conv = rep.get('convergence')
    cs = ('; '.join(
        f"eps={e_}: {('%.3g' % float(d_)) if not isinstance(d_, str) else d_}"
        for e_, d_ in conv) if conv else '-')
    return (f"  {name} seed {seed}: eps track "
            f"{[(str(e_), s_) for e_, s_ in rep['eps']]}; "
            f"mot {rep.get('dim mot 1/64')}->"
            f"{rep.get('dim mot limit')} (limit); "
            f"dim V_bc(limit)={rep.get('dim V_bc limit')}; "
            f"z(limit): {rep.get('z limit', '-')}; convergence: {cs}")


def slide():
    print("== slide-in degeneration (route-1 probe) ==")
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    v = chains[0][1]
    aa = chains[0][2]
    # slide every intact chain's interiors into their adjacent hubs:
    smap = {}
    for (u, x, y, w) in chains[1:]:
        smap[x] = u
        smap[y] = w
    n_ok = 0
    for seed in range(440, 470):
        rep = slide_probe(E, v, seed, smap,
                          eps_list=(F(1), F(1, 4), F(1, 16), F(1, 64),
                                    F(1, 256), F(1, 1024)))
        if rep is None:
            continue
        n_ok += 1
        print(slide_line('dbl-K4', seed, rep))
        if n_ok >= 3:
            break
    assert n_ok >= 3
    # theta(3,4,5): partial slide (only panel-adjacent interiors move):
    E2 = theta_edges((3, 4, 5))
    smap2 = {13: 0, 15: 1, 17: 0, 20: 1}   # arc ends -> their hubs
    n_ok = 0
    for seed in range(200, 230):
        rep = slide_probe(E2, 10, seed, smap2)
        if rep is None:
            continue
        n_ok += 1
        print(slide_line('theta(3,4,5)', seed, rep))
        if n_ok >= 2:
            break
    assert n_ok >= 2
    print("SLIDE probe done (verdict recorded in the workbook)")


def main():
    if '--control' in sys.argv:
        control()
    elif '--witness' in sys.argv:
        witness()
    elif '--stratum' in sys.argv:
        stratum()
    elif '--sweep' in sys.argv:
        sweep()
    elif '--theta336' in sys.argv:
        theta336()
    elif '--companion4' in sys.argv:
        companion4()
    elif '--slide' in sys.argv:
        slide()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
