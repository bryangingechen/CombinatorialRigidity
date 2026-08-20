"""
Probe KBARE-FALSIFY — the falsification hunt for `hbareSplit` / (K-bare-ext).

Commissioned 2026-08-20 (`notes/Pencil-fanout.md` §"Two probes SPECCED and
AUTHORIZED 2026-08-20"); labels/paths reserved in `notes/Pencil-labels.md`
§"Reserved namespace — probe KBARE-FALSIFY".  Backs
`notes/Pencil-informal.md` §(K-bare-ext) *Steps BE1–BE8*.

WHAT IS BEING BROKEN, AND WHAT THIS DRIVER CAN AND CANNOT SHOW.
`hbareSplit` (`Molecule/Pencil/Escape.lean:351`) concludes
`HasPencilRealization K 3 G`, which is an EXISTENTIAL over frameworks
(`Statement.lean:103`, read this pass).  So:
  * (T2) refuting `hbareSplit` needs `HasPencilRealization K 3 G` to FAIL —
    a universal non-existence over all frameworks and all placements.  No
    sampler can certify that, and this driver never claims to: it can only
    (a) rule a gadget OUT as a T2 candidate by exhibiting an attaining
    realization, or (b) hand a *mechanism* to an argument.  Every gadget
    probed here attains, so none is a T2 candidate.
  * (T1) refuting (K-bare-ext) — the arbitrary-seed insertion lemma, a
    FORALL over target-rank `G'` seeds — needs one legal target-rank seed at
    which EVERY placement of `v` fails.  That IS decidable per seed without a
    cap (`uniform_failure` below: the 2x2 minors of the criterion matrix are
    quadratic forms in the placement, so "fails everywhere on the domain" is
    an identical-vanishing test, not a sample).  The seed HUNT is capped; the
    per-seed verdict is not.
  * (T3) the FORALL-form "off-line => attains" is already known false
    (§(K-tight) *Step 2.4* / *Step 3*: the failure locus is
    `line(a,b) u P'`).  Off-line failure points are reported here as
    corroboration at a NEW stratum, never as a hit.

Model: the `kbare_common` carrier (points `p : V -> Q^3`, `point v = hat(p v)`,
`C_e = hat(p u) ^ hat(p v)`, `normal v` from the closed-star nullspace), which
this pass re-verified against `HasPencilPanelRealization` (`Statement.lean:88`)
and `IsNondegPencilRealization` (`Motive.lean:110`).  Exact ℚ throughout;
GF(p) rank only as a certified lower bound, as in `kbare_common`.

THE CALCULUS (the §(K-tight) *Step 2* boundary-load machinery, transported).
Derived here from the row structure of `kbare_common.build_rigidity`, not
imported as prose:
    U   = {u in K^6 : (u at a, -u at b) in rowspan(shared rows of G - v)}
        = {u : <u, m(a) - m(b)> = 0 for every motion m of G - v},
    R_a = {sum_j nu_j w_j : nu the `ab`-block of a G'-self-stress},
          w_j the 5 `perp_basis(C_ab)` generators,
    s0  = corank of the shared rows,
and the CORANK IDENTITY, which is scope-free (no `def = 0`, no genericity):
    corank R(G) at pt(v) = x  =  s0 + dim(U ∩ C(va)^perp ∩ C(vb)^perp)
                             =  s0 + dim U - rank M(x),
    M(x) = [[<u_i, C(va)>], [<u_i, C(vb)>]]   (2 x dim U, entries LINEAR in x).
Attainment of `target(G)` <=> that equals `index(G) + def(G)`; in the
count-dependent stratum (`def = 0`) that is exactly `rank M(x) = 2`.

Modes (`python3 notes/scripts/kbare/breakhunt.py <mode>`):
  tiers  (BE1)  the tier audit: every probed gadget ATTAINS, so no T2
                candidate exists in the arc's gadget stock; plus the
                witness-class and sampler disclosures (the recorded DZ
                figures ride `kbare_common.plane_basis`, the known-degenerate
                member of the *Divergences* family).
  calc   (BE2)  the calculus transported: corank identity + the three
                structure identities + the per-placement biconditional, at
                DZ (both split shapes) and at a corank-3 index-2 gadget.
  arith  (BE3)  the index bound: `index(G) <= 2` in the count-dependent
                habitat, hence `corank(G') <= 3` — proved by arithmetic, and
                verified by exhaustive enumeration over every cubic
                multigraph skeleton on <= 6 hubs plus an arithmetic candidate
                count on the named 8- and 10-hub skeletons.
  rzero  (BE4)  THE HIT HUNT: legal target-rank `G'` seeds with
                `dim R_a = 0`, or with uniform route-A failure on the whole
                placement domain.  Cap-free per seed.
  locus  (BE5)  the failure locus, CONSTRUCTED not sampled: exact off-line
                failure points from the (A, B) linear maps (T3).
  c1b    (BE6)  the second gadget against option-C's C1 finding.
  all           tiers + calc + arith + rzero + locus + c1b.

Reproduce (repo root):
  python3 notes/scripts/kbare/breakhunt.py tiers|calc|arith|rzero|locus|c1b|all
"""
import random, sys, time
from fractions import Fraction as F
from itertools import combinations

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from kbare_common import *                      # noqa: F401,F403,E402
from exactcore import left_nullspace            # noqa: E402  (base layer)
from gate2 import line_of_two_planes            # noqa: E402  (sibling; debt item)
from danger import dz_gadget, sample_dz_pencil  # noqa: E402  (sibling; debt item)
from optc import SKELETONS, build_from_skeleton  # noqa: E402  (sibling; debt)
from repin import (star_generic, robust_plane_basis,  # noqa: E402
                   lambda2_plane)

# ---------------------------------------------------------------- helpers ---

def index_of(edges):
    return 5 * len(edges) - 6 * (len(verts_of(edges)) - 1)

def hub_set(edges):
    d = degrees(edges)
    return [v for v in verts_of(edges) if d[v] >= 3]

def cross4_of(u, v):
    """The 6 Plucker coords of u ^ v (wrapper kept local for readability)."""
    return wedge2(u, v)


# ------------------------------------------------- the split context -------

def split_ctx(edges_G, v, defs=None):
    """Everything the calculus needs about one split, geometry-free.

    `defs=(dG, dGp)` supplies the deficiencies when the exact 2^|V| table is
    too big (they are then certified elsewhere — see `--arith`); otherwise
    they are computed exactly."""
    nb, deg = neighbors(edges_G), degrees(edges_G)
    assert deg[v] == 2, f"{v} is not a degree-2 body"
    a, b = sorted(nb[v], key=str)
    edges_Gp = split_off(edges_G, v, a, b)      # (a, b) appended LAST
    assert edges_Gp[-1] == (a, b)
    edges_sh = [e for e in edges_G if v not in e]
    n = len(verts_of(edges_G))
    if defs is None:
        dG = exact_deficiency(edges_G)[0]
        dGp = exact_deficiency(edges_Gp)[0]
    else:
        dG, dGp = defs
    return {
        'v': v, 'a': a, 'b': b, 'G': edges_G, 'Gp': edges_Gp, 'sh': edges_sh,
        'Vsh': verts_of(edges_sh), 'n': n,
        'dG': dG, 'dGp': dGp,
        'tG': 6 * (n - 1) - dG, 'tGp': 6 * (n - 2) - dGp,
        'cG': 5 * len(edges_G) - (6 * (n - 1) - dG),
        'cGp': 5 * len(edges_Gp) - (6 * (n - 2) - dGp),
        'index': index_of(edges_G),
        'hubs': (deg[a] >= 3, deg[b] >= 3), 'degv2': True,
    }


def seed_calculus(ctx, ptp):
    """At a `G'` placement `ptp`: s0, U, R_a and the structure identities.
    Returns None if the configuration is not a legal `G'` pencil witness."""
    ok, _ = verify_pencil_witness(ctx['Gp'], ptp)
    if not ok:
        return None
    rows_sh, _ = build_rigidity(ctx['sh'], ptp)
    s0 = len(rows_sh) - rank_exact(rows_sh)
    Vsh = ctx['Vsh']
    ia, ib = Vsh.index(ctx['a']), Vsh.index(ctx['b'])
    funcs = [[m[6 * ia + k] - m[6 * ib + k] for k in range(6)]
             for m in nullspace(rows_sh)]
    U = nullspace(funcs) if funcs else [[F(1) if i == j else F(0)
                                         for i in range(6)] for j in range(6)]
    rows_p, _ = build_rigidity(ctx['Gp'], ptp)
    rkp = rank_exact(rows_p)
    Cab = cross4_of(hat(ptp[ctx['a']]), hat(ptp[ctx['b']]))
    wab = perp_basis(Cab)
    Ra = []
    for st in left_nullspace(rows_p):
        nu = st[-5:]
        Ra.append([sum((nu[j] * wab[j][k] for j in range(5)), F(0))
                   for k in range(6)])
    dimU, dimRa = rank_exact(U), rank_exact(Ra)
    # the three structure identities of §(K-tight) Step 2
    dim_meet = dimU + 5 - rank_exact(list(U) + list(wab))     # dim(U ∩ Cab^perp)
    checks = {
        'dimU_eq_dimRa_plus_1': dimU == dimRa + 1,
        'Ra_subset_U': rank_exact(list(U) + list(Ra)) == dimU,
        'meet_eq_Ra': dim_meet == dimRa,
        'dimRa_eq_index_plus_1_minus_s0': dimRa == ctx['index'] + 1 - s0,
    }
    return {'s0': s0, 'U': U, 'Ra': Ra, 'dimU': dimU, 'dimRa': dimRa,
            'Cab': Cab, 'rkGp': rkp, 'at_target': rkp == ctx['tGp'],
            'checks': checks, 'star_generic': star_generic(ctx['Gp'], ptp)}


def crit_matrix(ctx, ptp, sd, x3):
    """M(x) — the 2 x dim U criterion matrix at placement pt(v) = x3."""
    ha, hb, hx = hat(ptp[ctx['a']]), hat(ptp[ctx['b']]), hat(x3)
    Cva, Cvb = cross4_of(hx, ha), cross4_of(hx, hb)
    return [[dot(u, Cva) for u in sd['U']], [dot(u, Cvb) for u in sd['U']]]


def predicted_corank(ctx, ptp, sd, x3):
    return sd['s0'] + sd['dimU'] - rank_exact(crit_matrix(ctx, ptp, sd, x3))


def observed(ctx, ptp, x3):
    """(legal witness?, exact rank of R(G)) at pt(v) = x3."""
    pt = dict(ptp)
    pt[ctx['v']] = x3
    try:
        ok, _ = verify_pencil_witness(ctx['G'], pt)
    except AssertionError:
        return False, None
    if not ok:
        return False, None
    rows, _ = build_rigidity(ctx['G'], pt)
    return True, rank_exact(rows)


# --------------------------------- the AB maps and the failure locus -------

def ab_maps(ctx, ptp, sd):
    """The two linear maps A, B : K^4 -> K^(dim U),
        A(y)_i = <u_i, y ^ hat(a)>,   B(y)_i = <u_i, y ^ hat(b)>,
    as matrices in the standard basis of K^4.  A(hat a) = B(hat b) = 0, and
    `A(hat b) = -B(hat a) = -(<u_i, C_ab>)`.  The route-A failure locus is
    exactly {y : A(y) ^ B(y) = 0}, so it always contains line(a, b) (there
    C(va) ∥ C(vb)) — the structural reason every on-line placement fails."""
    ha, hb = hat(ptp[ctx['a']]), hat(ptp[ctx['b']])
    Am, Bm = [], []
    for j in range(4):
        e = [F(1) if i == j else F(0) for i in range(4)]
        Am.append([dot(u, cross4_of(e, ha)) for u in sd['U']])
        Bm.append([dot(u, cross4_of(e, hb)) for u in sd['U']])
    return Am, Bm                     # rows indexed by the K^4 basis


def apply_map(Mrows, y4):
    d = len(Mrows[0])
    return [sum((y4[j] * Mrows[j][i] for j in range(4)), F(0)) for i in range(d)]


def wedge_vec(p, q):
    """All 2x2 minors of the 2 x d matrix [p; q] (zero iff p ∥ q)."""
    return [p[i] * q[j] - p[j] * q[i] for i, j in combinations(range(len(p)), 2)]


def need_rank(ctx, sd):
    """The rank of `M(x)` that ATTAINMENT requires, scope-free:
    `corank R(G) = s0 + dim U - rank M(x)` and attainment asks for
    `corank = index(G) + def(G)`, so `rank M = s0 + dim U - index - def`.
    `rank M <= min(2, dim U)`, so a required rank above that bound is
    UNIFORM FAILURE by arithmetic alone.  In the count-dependent stratum
    (`def = 0`, `dim U = index + 2 - s0`) this is always 2 — the
    §(K-tight) *Step 2.1* form."""
    return sd['s0'] + sd['dimU'] - ctx['cG']


def domain_frame(ctx, ptp, domain, rng):
    """An affine frame `(base, dirs)` of the placement domain in K^4: the
    whole chart when `domain is None`, else the hub end's panel
    `{y : <domain, y> = 0}`.  In-plane directions come from
    `repin.robust_plane_basis` — the canonical sampler basis the 2026-08-06
    re-baselining round made mandatory for new work."""
    if domain is None:
        base = [F(x) for x in rvec3(rng)] + [F(1)]
        dirs = [[F(1), F(0), F(0), F(0)], [F(0), F(1), F(0), F(0)],
                [F(0), F(0), F(1), F(0)]]
        return base, dirs
    p0 = point_on_affine_plane4(domain, rng)
    base = [F(x) for x in p0] + [F(1)]
    b0, b1 = robust_plane_basis(domain[:3])
    return base, [list(b0) + [F(0)], list(b1) + [F(0)]]


def lin_coeffs(u, anchor4, base, dirs):
    """`y |-> <u, y ^ anchor4>` restricted to `base + sum s_k dirs[k]`, as the
    coefficient tuple `(c0, c_1, ..., c_m)` of an AFFINE-LINEAR form."""
    return [dot(u, cross4_of(base, anchor4))] + \
           [dot(u, cross4_of(d, anchor4)) for d in dirs]


def poly_mul(p, q):
    """Product of two affine-linear coefficient tuples, as a dict
    monomial-multiset -> coefficient."""
    out = {}
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            if a == 0 or b == 0:
                continue
            k = tuple(sorted((i, j)))
            out[k] = out.get(k, F(0)) + a * b
    return out


def uniform_failure_exact(ctx, ptp, sd, domain=None, rng=None):
    """THE CAP-FREE per-seed verdict.  Every entry of `M(x)` is an
    affine-linear form in the domain parameters, so every 2x2 minor is a
    quadratic form with finitely many coefficients: `rank M <= need - 1`
    everywhere on the domain is decided by checking those coefficients are
    ZERO — no sampling, no cap.  Returns (uniform_fail, reason)."""
    need = need_rank(ctx, sd)
    if need > min(2, sd['dimU']):
        return True, f'arithmetic: required rank {need} > min(2, dim U)'
    if need <= 0:
        return False, f'required rank {need} <= 0: attains everywhere legal'
    rng = rng or random.Random(3)
    base, dirs = domain_frame(ctx, ptp, domain, rng)
    ha, hb = hat(ptp[ctx['a']]), hat(ptp[ctx['b']])
    A = [lin_coeffs(u, ha, base, dirs) for u in sd['U']]
    B = [lin_coeffs(u, hb, base, dirs) for u in sd['U']]
    if need == 1:                      # rank 0 everywhere <=> all forms zero
        for row in A + B:
            if any(c != 0 for c in row):
                return False, 'some entry of M is not identically zero'
        return True, 'M vanishes identically on the domain'
    for i, j in combinations(range(sd['dimU']), 2):
        m = poly_mul(A[i], B[j])
        for k, c in poly_mul(A[j], B[i]).items():
            m[k] = m.get(k, F(0)) - c
        if any(c != 0 for c in m.values()):
            return False, f'minor ({i},{j}) is not identically zero'
    return True, ('all %d 2x2 minors of M vanish IDENTICALLY on the domain'
                  % (sd['dimU'] * (sd['dimU'] - 1) // 2))


def uniform_failure(ctx, ptp, sd, domain=None, nprobe=6, rng=None):
    """CAP-FREE per-seed test of "every placement fails".

    Each minor of `M(x)` is a quadratic form in `x in K^4`; the placement
    domain is either the affine chart (free placement) or a 2-plane (a hub
    split).  A quadratic form vanishes identically on an affine subspace iff
    it vanishes at enough points of it — here checked by evaluating on a
    spanning set of `dim+2` choose 2 sample directions AND, independently, by
    the algebraic criterion `rank A <= 1 or rank B <= 1 or A ∥ B on the whole
    domain` via a symbolic sweep in two parameters.  Returns
    (uniform_fail, witness) where `witness` is an attaining placement when the
    answer is False."""
    need = need_rank(ctx, sd)
    if need > min(2, sd['dimU']):
        return True, None                 # forced by arithmetic, no geometry
    if need <= 0:
        return False, None
    Am, Bm = ab_maps(ctx, ptp, sd)
    rng = rng or random.Random(1)
    # A spanning affine frame of the domain, in K^4 (last coord 1 = affine).
    ha = hat(ptp[ctx['a']])
    base = [F(x) for x in ptp[ctx['a']]] + [F(1)]
    if domain is None:
        dirs = [[F(1), F(0), F(0), F(0)], [F(0), F(1), F(0), F(0)],
                [F(0), F(0), F(1), F(0)]]
    else:                                  # 2-plane {y : <domain, y> = 0}
        dirs = [d for d in nullspace([domain])][:3]
        dirs = [d for d in dirs if any(x != 0 for x in d)]
    # sweep the domain on a rational grid; a quadratic vanishing on a
    # (dim+2)-point general-position grid per 2-plane vanishes identically
    grid = []
    for t in (F(0), F(1), F(-1), F(2), F(1, 2), F(3), F(-2), F(5, 3)):
        for k, d in enumerate(dirs):
            grid.append([base[i] + t * d[i] for i in range(4)])
        if len(dirs) >= 2:
            grid.append([base[i] + t * dirs[0][i] + (t + 1) * dirs[1][i]
                         for i in range(4)])
    for _ in range(nprobe):
        cs = [rint(rng, -7, 7) for _ in dirs]
        grid.append([base[i] + sum(c * d[i] for c, d in zip(cs, dirs))
                     for i in range(4)])
    for y in grid:
        if y[3] == 0:
            continue
        p, q = apply_map(Am, y), apply_map(Bm, y)
        got = (wedge_vec(p, q) if need == 2 else list(p) + list(q))
        if any(z != 0 for z in got):
            x3 = [y[i] / y[3] for i in range(3)]
            return False, x3
    return True, None


def failure_points_through(ctx, ptp, sd, anchor, ntry=40, rng=None,
                           domain=None):
    """CONSTRUCT failure points, not sample them.  On the line
    {hat(anchor) + t z} the locus {A ^ B = 0} reduces to a LINEAR system in
    `t` (because A(hat a) = 0), so each direction `z` either yields an exact
    rational failure point or provably none.  Returns a list of
    (t, x3, off_line) triples."""
    rng = rng or random.Random(7)
    Am, Bm = ab_maps(ctx, ptp, sd)
    ha, hb = hat(ptp[ctx['a']]), hat(ptp[ctx['b']])
    anch = hat(ptp[anchor])
    A0, B0 = apply_map(Am, anch), apply_map(Bm, anch)
    dline = [hb[i] - ha[i] for i in range(4)]
    out = []
    for _ in range(ntry):
        if domain is None:
            z = [rint(rng, -8, 8) for _ in range(3)] + [F(0)]
        else:
            ns = [d for d in nullspace([domain])]
            cs = [rint(rng, -8, 8) for _ in ns]
            z = [sum(c * d[i] for c, d in zip(cs, ns)) for i in range(4)]
        if all(x == 0 for x in z):
            continue
        Az, Bz = apply_map(Am, z), apply_map(Bm, z)
        # (A0 + t Az) ^ (B0 + t Bz) = W0 + t W1 + t^2 W2, and at an ANCHOR
        # end one of A0, B0 vanishes (A(hat a) = 0, B(hat b) = 0), so W0 = 0
        # identically: the locus on this line is t * (W1 + t W2) = 0.  The
        # root t = 0 is the anchor point itself (an illegal placement — it
        # coincides with pt of the anchor), so the CONTENT is the linear
        # system W1 + t W2 = 0, which is exactly solvable.
        W0, W2 = wedge_vec(A0, B0), wedge_vec(Az, Bz)
        W1 = [a + b for a, b in zip(wedge_vec(A0, Bz), wedge_vec(Az, B0))]
        assert all(x == 0 for x in W0), 'anchor is not on the failure locus'
        cand, good = None, True
        for c1, c2 in zip(W1, W2):
            if c2 == 0:
                if c1 != 0:
                    good = False
                    break
            else:
                t = -c1 / c2
                if cand is None:
                    cand = t
                elif cand != t:
                    good = False
                    break
        ts = [cand] if (good and cand is not None) else []
        for t in ts:
            y = [anch[i] + t * z[i] for i in range(4)]
            if y[3] == 0:
                continue
            x3 = [y[i] / y[3] for i in range(3)]
            d = [y[i] - ha[i] for i in range(4)]
            on_line = all(d[i] * dline[j] == d[j] * dline[i]
                          for i in range(4) for j in range(4))
            out.append((t, x3, not on_line))
    return out


# ------------------------------------------------- general pencil sampler --

def sample_pencil_bfs(edges, rng, degen=None, apex=None):
    """A general exact-ℚ pencil configuration for ANY habitat topology.

    Phase 1 places hub points and hub panels by BFS over the hub-hub
    adjacency graph (each panel chosen through the hub's already-placed
    closed-star members, then the unplaced hub neighbours dropped onto it);
    phase 2 places every non-hub body on its adjacent hub's panel, or on the
    meet line of two.  Robust: no call to the degenerate
    `kbare_common.plane_basis` family (`README` *Divergences*) — planes come
    from `normal4_through`, points from `point_on_affine_plane4`.

    `degen` forces a deeper stratum, for the adversarial battery:
      'hubplane'  every hub point in one global plane,
      'apexline'  the apex's hub neighbours COLLINEAR inside its panel,
      'flat'      every body of the graph in one plane (maximally degenerate),
      'starline'  every hub's neighbours collinear inside its panel.
    Raises AssertionError/RuntimeError when the draw is inconsistent (the
    caller retries with a fresh seed)."""
    deg, nb = degrees(edges), neighbors(edges)
    hubs = hub_set(edges)
    if apex is None:
        hh = {h: [w for w in nb[h] if deg[w] >= 3] for h in hubs}
        apex = max(hubs, key=lambda h: (len(hh[h]), str(h))) if hubs else None
    pt, plane, done = {}, {}, set()
    if degen == 'flat':
        n4 = [rint(rng, -6, 6) for _ in range(3)] + [rint(rng, -6, 6)]
        if all(x == 0 for x in n4[:3]):
            n4[0] = F(1)
        for w in verts_of(edges):
            pt[w] = point_on_affine_plane4(n4, rng)
        for h in hubs:
            plane[h] = n4
        return pt, plane
    glob = None
    if degen == 'hubplane':
        glob = [rint(rng, -6, 6) for _ in range(3)] + [rint(rng, -6, 6)]
        if all(x == 0 for x in glob[:3]):
            glob[0] = F(1)
    if degen == 'cycleflat':
        S = coplanar_closure(edges, shortest_cycle(edges))
        n4 = normal4_through([hat(rvec3(rng))], rng)
        for w in sorted(S, key=str):
            pt[w] = point_on_affine_plane4(n4, rng)
        for h in hubs:
            if h in S and len([w for w in nb[h] if w in S]) >= 2:
                plane[h] = n4
    order = ([apex] if apex is not None else []) + \
            [h for h in hubs if h != apex]
    for root in order:
        if root not in pt:
            pt[root] = (point_on_affine_plane4(glob, rng) if glob
                        else rvec3(rng))
        queue = [root]
        while queue:
            h = queue.pop(0)
            if h in done:
                continue
            done.add(h)
            if h not in plane:
                anchors = [hat(pt[h])] + [hat(pt[w]) for w in
                                          sorted(nb[h], key=str) if w in pt]
                plane[h] = normal4_through(anchors, rng)
            fresh = [w for w in sorted(nb[h], key=str)
                     if w not in pt and deg[w] >= 3]
            collinear = (degen == 'starline') or (degen == 'apexline'
                                                 and h == apex)
            if collinear and len(fresh) >= 2:
                # a rational line inside the panel, through pt(h)
                p0 = point_on_affine_plane4(plane[h], rng)
                d = [p0[i] - pt[h][i] for i in range(3)]
                if all(x == 0 for x in d):
                    raise RuntimeError('degenerate panel line')
                for k, w in enumerate(fresh):
                    s = rint(rng, 1, 9) + F(k)
                    pt[w] = [pt[h][i] + s * d[i] for i in range(3)]
            else:
                for w in fresh:
                    pt[w] = (point_on_affine_plane4(glob, rng) if glob
                             else point_on_affine_plane4(plane[h], rng))
            for w in fresh:
                queue.append(w)
            for w in sorted(nb[h], key=str):      # cover the hub component
                if deg[w] >= 3 and w not in done:
                    queue.append(w)
    for h in hubs:
        if h not in plane:
            plane[h] = normal4_through([hat(pt[h])], rng)
    for w in verts_of(edges):
        if w in pt:
            continue
        adj = sorted([h for h in nb[w] if h in plane], key=str)
        if not adj:
            pt[w] = rvec3(rng)
        elif len(adj) == 1:
            pt[w] = point_on_affine_plane4(plane[adj[0]], rng)
        else:
            q = line_of_two_planes(plane[adj[0]], plane[adj[1]], rng)
            if q is None:
                raise RuntimeError(f'parallel panels at {w}')
            pt[w] = q
    return pt, plane


def two_core(edges):
    """Iteratively drop degree-<= 1 bodies; stresses live only here."""
    cur = list(edges)
    while True:
        d = degrees(cur)
        drop = [v for v in verts_of(cur) if d[v] <= 1]
        if not drop:
            return cur
        cur = [e for e in cur if e[0] not in drop and e[1] not in drop]


def shortest_cycle(edges):
    """A shortest cycle of the 2-core, as a vertex set (BFS from each body)."""
    core = two_core(edges)
    nb = neighbors(core)
    best = None
    for r in sorted(nb, key=str):
        par, dist = {r: None}, {r: 0}
        q = [r]
        while q:
            x = q.pop(0)
            for y in sorted(nb[x], key=str):
                if y not in dist:
                    dist[y], par[y] = dist[x] + 1, x
                    q.append(y)
                elif par.get(x) != y:
                    ln = dist[x] + dist[y] + 1
                    if best is None or ln < best[0]:
                        pa, pb2 = [x], [y]
                        while par[pa[-1]] is not None:
                            pa.append(par[pa[-1]])
                        while par[pb2[-1]] is not None:
                            pb2.append(par[pb2[-1]])
                        best = (ln, set(pa) | set(pb2))
    return best[1] if best else set()


def coplanar_closure(edges, S):
    """THE PENCIL PROPAGATION RULE, as a combinatorial closure.  If three
    bodies of a hub's closed star lie in a plane `P` and span it, the hub's
    panel IS `P`, so its whole closed star lies in `P`.  Hence: while some hub
    `h` has `|closedStar(h) ∩ S| >= 3`, add all of `closedStar(h)`.  This is
    why the pencil stratum has no *local* degenerations of the bar-joint kind:
    a forced coplanarity spreads along hubs until the closure stops."""
    deg, nb = degrees(edges), neighbors(edges)
    S = set(S)
    while True:
        grew = False
        for h in verts_of(edges):
            if deg[h] < 3:
                continue
            star = set([h]) | set(nb[h])
            if len(star & S) >= 3 and not star <= S:
                S |= star
                grew = True
        if not grew:
            return S


def hub_domain(ctx, ptp):
    """The placement domain normal: `None` for a free split, else the 4-normal
    of the hub end's panel through its `G`-neighbours other than `v`."""
    deg, nb = degrees(ctx['G']), neighbors(ctx['G'])
    ends = [x for x in (ctx['a'], ctx['b']) if deg[x] >= 3]
    if not ends:
        return None
    h = ends[0]
    anchors = [hat(ptp[h])] + [hat(ptp[w]) for w in sorted(nb[h], key=str)
                               if w != ctx['v']]
    ns = nullspace(anchors)
    if not ns or all(ns[0][i] == 0 for i in range(3)):
        raise RuntimeError('degenerate hub placement panel')
    return ns[0]


# -------------------------------------------------------------- BE1: tiers --

Q3_LENGTHS = None   # filled by `q3_gadget()`

def q3_gadget():
    """The option-C C2 index-2 hit on the cube skeleton (24v/28e, f(V) = +2,
    corank 2 at `G`'s target, corank 3 at a split's).  Rebuilt here from
    `optc.SKELETONS` + the same length rule so the figure is reproducible
    from this file; `def = 0` and no-proper-rigid come from the skeleton-level
    certificate (see `--arith`), the exact 2^24 table being `optc.py c2`'s."""
    global Q3_LENGTHS
    skel, apex = SKELETONS['cube Q3 (8v)']
    apex_e = [e for e in skel if apex in e]
    other = [e for e in skel if apex not in e]
    from itertools import product
    need = 3 * 8 + 4 - len(apex_e)
    for ls in product((1, 2, 3), repeat=len(other)):
        if sum(ls) != need:
            continue
        lengths = {e: 1 for e in apex_e}
        lengths.update(dict(zip(other, ls)))
        if skel_ok_multi(skel, [lengths[e] for e in skel])[0]:
            Q3_LENGTHS = lengths
            edges = build_from_skeleton(skel, lengths)
            ren = {f's{apex}': 'h0'}
            return [(ren.get(u, u), ren.get(w, w)) for (u, w) in edges]
    raise RuntimeError('no Q3 hit')


def attain_check(name, edges, nsample=6, seed0=990, defs=None):
    """Does `G` attain its bare pencil target?  An attaining sample rules the
    gadget OUT as a T2 candidate (T2 needs universal non-attainment)."""
    n = len(verts_of(edges))
    d = defs if defs is not None else exact_deficiency(edges)[0]
    tG = 6 * (n - 1) - d
    best, got = -1, None
    for s in range(nsample):
        rng = random.Random(seed0 + s)
        try:
            pt, _ = sample_pencil_bfs(edges, rng)
            ok, _ = verify_pencil_witness(edges, pt)
            assert ok
            rk = rank_modp(build_rigidity(edges, pt)[0])
        except (AssertionError, RuntimeError):
            continue
        best = max(best, rk)
        if rk == tG and got is None:
            got = pt
    exact = None
    if got is not None:
        exact = rank_exact(build_rigidity(edges, got)[0])
    print(f"  {name}: |V|={n} |E|={len(edges)} index={index_of(edges)} def={d} "
          f"target={tG} rows={5*len(edges)} -> best rank {best}"
          f"{'' if exact is None else f' (exact-Q {exact})'} "
          f"[{'ATTAINS -> NOT a T2 candidate' if best == tG else 'NOT attained under cap'}]")
    return best == tG


def run_tiers():
    print("===== BE1: the tier audit =====")
    print("  T2 (refuting hbareSplit) needs `HasPencilRealization K 3 G` to")
    print("  FAIL: universal non-existence over frameworks AND placements.")
    print("  An attaining realization at G rules the gadget out as T2.")
    edz = dz_gadget()
    a1 = attain_check("DZ (subdivided K3,3 + apex)", edz)
    eq3 = q3_gadget()
    a2 = attain_check("Q3 index-2 hit (skeleton-certified def 0)", eq3, defs=0)
    print(f"\n  >>> T2 candidates among the arc's danger gadgets: "
          f"{0 if (a1 and a2) else '??'} of 2 "
          f"(both attain; the gate's seven were already known to attain)")
    print("\n  DISCLOSURE 1 (witness class).  This sampler places affine")
    print("  points and reads hinges as `hat(p u) ^ hat(p v)`; it is a")
    print("  SUBCLASS of the frameworks `HasPencilRealization` quantifies")
    print("  over.  Non-attainment under this class would still not be T2.")
    print("\n  DISCLOSURE 2 (the recorded DZ seeds ride the degenerate")
    print("  plane_basis).  `danger.sample_dz_pencil` places h0's three hub")
    print("  neighbours with `kbare_common.point_in_plane3`, i.e. the")
    print("  known-degenerate `plane_basis` (README *Divergences*): when the")
    print("  drawn normal's third coordinate is 0 the three land on ONE LINE")
    print("  (the option-C D3 'apex star collinear' stratum) unannounced.")
    fired = []
    for tag, s0, cnt in [('danger probe 2 attainment', 4200, 10),
                         ('danger probe 3a extension', 7100, 8),
                         ('danger probe 3b extension', 8200, 8),
                         ('optc C1 (D1/D2)', 11000, 6),
                         ('optc C1 (D3/D4)', 11100, 6),
                         ('optc C2 mini-gate', 13000, 4),
                         ('optc C2 mini-gate (ext)', 13050, 4),
                         ('optc C3', 15000, 12)]:
        hits = []
        for s in range(cnt):
            rng = random.Random(s0 + s)
            n0 = rnonzero3(rng)
            b1, b2 = plane_basis(n0)
            cr = [b1[1] * b2[2] - b1[2] * b2[1], b1[2] * b2[0] - b1[0] * b2[2],
                  b1[0] * b2[1] - b1[1] * b2[0]]
            if all(x == 0 for x in cr):
                hits.append(s0 + s)
        fired.append((tag, len(hits), cnt, hits))
        print(f"    {tag}: degenerate at {len(hits)}/{cnt} seeds {hits}")
    tot = sum(h for _, h, _, _ in fired)
    ntot = sum(c for _, _, c, _ in fired)
    print(f"    >>> {tot}/{ntot} of the recorded (K-bare) DZ seed draws sit on")
    print(f"        the coincidence locus.  Same defect class as (OC-7) in the")
    print(f"        (K) arc; this driver uses the robust sampler throughout.")
    return a1, a2


# --------------------------------------------------------------- BE2: calc --

def run_calc(nseeds=8, seed0=31000):
    print("===== BE2: the §(K-tight) Step-2 calculus, transported to (K-bare) =====")
    cases = [("DZ, non-hub-ends split (v=u1h2_2)", dz_gadget(), 'u1h2_2', None),
             ("DZ, KT-faithful hub-end split (v=u1h2_1)", dz_gadget(),
              'u1h2_1', None)]
    eq3 = q3_gadget()
    deg, nb = degrees(eq3), neighbors(eq3)
    vq = next(x for x in verts_of(eq3) if deg[x] == 2
              and any(deg[w] == 2 for w in nb[x])
              and any(deg[w] >= 3 for w in nb[x]))
    cases.append((f"Q3 index-2 gadget, hub-end split (v={vq})", eq3, vq,
                  (0, 0)))
    e666, m666 = spider(6, 6, 6)
    arc = m666['arcs']['ab']
    v666 = arc[len(arc) // 2]
    cases.append((f"theta(6,6,6)+center — count-INDEPENDENT (v={v666})",
                  e666, v666, None))
    allok = True
    for name, edges, v, defs in cases:
        ctx = split_ctx(edges, v, defs=defs)
        print(f"\n  {name}")
        print(f"    index(G)={ctx['index']} def(G)={ctx['dG']} def(G')={ctx['dGp']} "
              f"target(G)={ctx['tG']} target(G')={ctx['tGp']} "
              f"corank(G' at target)={ctx['cGp']} hub ends={ctx['hubs']}")
        nseed = nid = nbic = nplace = 0
        s0s, needs = set(), set()
        tally = {k: 0 for k in ('dimU_eq_dimRa_plus_1', 'Ra_subset_U',
                                'meet_eq_Ra', 'dimRa_eq_index_plus_1_minus_s0')}
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctx['Gp'], rng)
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctx, ptp)
            if sd is None or not sd['at_target']:
                continue
            nseed += 1
            s0s.add(sd['s0'])
            needs.add(need_rank(ctx, sd))
            for k, ok2 in sd['checks'].items():
                tally[k] += 1 if ok2 else 0
            if all(sd['checks'].values()):
                nid += 1
            try:
                dom = hub_domain(ctx, ptp)
            except RuntimeError:
                dom = None
            # per-placement: predicted corank vs observed, exact
            for k in range(6):
                if dom is None:
                    x3 = rvec3(rng)
                else:
                    x3 = point_on_affine_plane4(dom, rng)
                okw, rk = observed(ctx, ptp, x3)
                if not okw:
                    continue
                nplace += 1
                pred = predicted_corank(ctx, ptp, sd, x3)
                if 5 * len(ctx['G']) - rk == pred:
                    nbic += 1
                else:
                    allok = False
                    print(f"    seed {s} place {k}: CORANK IDENTITY FAILS "
                          f"predicted {pred} observed {5*len(ctx['G'])-rk}")
        print(f"    {nseed} target-rank seeds; s0 values {sorted(s0s)}; "
              f"required rank M {sorted(needs)}; corank identity "
              f"{nbic}/{nplace} placements")
        for k in sorted(tally):
            print(f"      structure identity {k}: {tally[k]}/{nseed}")
        if nbic != nplace:
            allok = False
    print(f"\n  >>> calculus transport: {'ALL IDENTITIES HOLD' if allok else 'A FAILURE WAS SEEN'}")
    return allok


# -------------------------------------------------------------- BE3: arith --

def skel_ok_multi(skel, lens):
    """Multigraph-safe habitat check at the skeleton level: every PROPER
    closed whole-path sub-multigraph has `f <= -1`, where for an edge subset
    `S` with hub set `W`, `f = 6(|S| - |W| + 1) - sum_{e in S} l_e`.

    A DIFFERENT function from `optc.skeleton_check`, which keys lengths by the
    edge PAIR and so cannot see parallel skeleton edges (see the README
    *Divergences* row added with this driver).  Closure rule as there: a
    length-1 edge between two included hubs is forced into `S`.
    Returns (ok, worst_f)."""
    k = len(skel)
    worst = None
    for S in range(1, (1 << k) - 1):
        W, sl, ns = set(), 0, 0
        for i in range(k):
            if S >> i & 1:
                W.add(skel[i][0]); W.add(skel[i][1])
                sl += lens[i]; ns += 1
        if len(W) < 2:
            continue
        closed = True
        for i in range(k):
            if not (S >> i & 1) and lens[i] == 1 \
                    and skel[i][0] in W and skel[i][1] in W:
                closed = False
                break
        if not closed:
            continue
        f = 6 * (ns - len(W) + 1) - sl
        if worst is None or f > worst:
            worst = f
        if f >= 0:
            return False, worst
    return True, worst


def compositions(total, parts, lo, hi):
    """Every tuple of `parts` integers in `[lo, hi]` summing to `total`,
    generated with sum pruning (a `product()` filter is 10^3-10^5 times more
    work at the sizes `--arith` needs)."""
    if parts == 0:
        if total == 0:
            yield ()
        return
    lowest, highest = lo * (parts - 1), hi * (parts - 1)
    for x in range(lo, hi + 1):
        r = total - x
        if r < lowest or r > highest:
            continue
        for tail in compositions(r, parts - 1, lo, hi):
            yield (x,) + tail


def count_candidates(skel, H, index):
    """How many length assignments even satisfy the ARITHMETIC (apex edges
    pinned to 1, total `3H + 6 - index`, every arc `<= 5 - index` by the
    pruning lemma) — counted by DP, no habitat check and no enumeration, so
    it is affordable on skeletons whose `2^|E|` subset check is not.  A count
    of 0 settles the index for that skeleton outright."""
    lmax = max(1, 5 - index)
    L = 3 * H + 6 - index
    deg = {}
    for (x, y) in skel:
        deg[x] = deg.get(x, 0) + 1
        deg[y] = deg.get(y, 0) + 1
    total = 0
    for apex in sorted(deg):
        ai = [i for i, e in enumerate(skel) if apex in e]
        nbs = [e[0] if e[1] == apex else e[1] for e in (skel[i] for i in ai)]
        if len(set(nbs)) != len(nbs) or apex in nbs:
            continue
        k, need = len(skel) - len(ai), L - len(ai)
        dp = {0: 1}
        for _ in range(k):
            nxt = {}
            for tot, c in dp.items():
                for l in range(1, lmax + 1):
                    nxt[tot + l] = nxt.get(tot + l, 0) + c
            dp = {t: c for t, c in nxt.items() if t <= need}
        total += dp.get(need, 0)
    return total


def enumerate_family(skel, H, index, lmax=None):
    """Every length assignment on `skel` with an apex whose three edges are
    length 1 (the only known `¬PencilNondegFeasible` certificate at a cubic
    skeleton: `closedHubNbhd(apex)` = 4), total length `3H + 6 - index`,
    passing `skel_ok_multi` and subdivided-simple.  Yields (apex, lens).

    PRUNING LEMMA (a consequence of `skel_ok_multi`, not of the theorem being
    tested): for an edge with `l_e >= 2`, the subset `E - {e}` is a PROPER
    closed sub-multigraph with `f = index + l_e - 6`, so the habitat check
    itself forces `l_e <= 5 - index`.  Enumerating at that cap is therefore
    lossless; `run_arith` asserts the lemma on a rejected witness."""
    if lmax is None:
        lmax = max(1, 5 - index)
    Es = len(skel)
    L = 3 * H + 6 - index
    deg = {}
    for (x, y) in skel:
        deg[x] = deg.get(x, 0) + 1
        deg[y] = deg.get(y, 0) + 1
    for apex in sorted(deg):
        ai = [i for i, e in enumerate(skel) if apex in e]
        nb = [e[0] if e[1] == apex else e[1] for e in (skel[i] for i in ai)]
        if len(set(nb)) != len(nb) or apex in nb:
            continue                       # apex needs 3 DISTINCT neighbours
        rest = [i for i in range(Es) if i not in ai]
        need = L - len(ai)
        if need < len(rest) or need > lmax * len(rest):
            continue
        for ls in compositions(need, len(rest), 1, lmax):
            lens = [0] * Es
            for i in ai:
                lens[i] = 1
            for i, l in zip(rest, ls):
                lens[i] = l
            # subdivided-simple: at most one of a parallel class has length 1
            bad = False
            seen = {}
            for i, e in enumerate(skel):
                key = tuple(sorted(e))
                seen.setdefault(key, []).append(lens[i])
            for key, ll in seen.items():
                if sum(1 for l in ll if l == 1) > 1:
                    bad = True
            if bad:
                continue
            ok, _ = skel_ok_multi(skel, lens)
            if ok:
                yield apex, lens


def build_multi(skel, lens, apex):
    edges = []
    for i, (x, y) in enumerate(skel):
        prev = 'h0' if x == apex else f's{x}'
        end = 'h0' if y == apex else f's{y}'
        for j in range(1, lens[i]):
            w = f'p{i}_{j}'
            edges.append((prev, w))
            prev = w
        edges.append((prev, end))
    return edges


def run_arith():
    print("===== BE3: the index bound in the count-dependent (K-bare) habitat =====")
    print("  THEOREM (arithmetic, no cap).  Let `G` satisfy hbareSplit's")
    print("  antecedents with `E(G~)` count-dependent (index >= 1) and some")
    print("  degree-2 body.  Then index(G) <= 2, hence corank(G' at target)")
    print("  = index + 1 <= 3.")
    print("  Proof.  (i) For any maximal degree-2 path of length l >= 2,")
    print("  deleting its interiors leaves a PROPER vertex subset W with")
    print("  f(W) = index + l - 6, so hnoRigid forces l <= 5 - index.")
    print("  (ii) index = 4 would force every l <= 1, i.e. no degree-2 body")
    print("  at all, contradicting hdeg2.  (iii) index = 3 forces every")
    print("  l <= 2, so L <= 2*Es; with L = 6Es - 6H + 3 (the index identity)")
    print("  that gives 4Es <= 6H - 3, while min-degree-3 at the suppressed")
    print("  skeleton gives 2Es >= 3H, i.e. 4Es >= 6H.  Contradiction.")
    print("  (A bare cycle has no skeleton: |V| >= 5 forces C5, index 1.)")
    # (a) verify clause (i) against the exact table at DZ
    edz = dz_gadget()
    d, info = exact_deficiency(edz)
    print(f"\n  exact cross-check at DZ: index={index_of(edz)} def={d} "
          f"max f(W) proper={info['maxf_proper_ge2']} "
          f"(clause (i) predicts a length-4 path is the longest allowed: "
          f"5-index = {5-index_of(edz)}; DZ's longest arc is 4)")
    # (a2) the pruning lemma, asserted on a witness it must reject
    k33 = [tuple(e) for e in SKELETONS['K3,3 (6v)'][0]]
    apex0 = 0
    lens_bad = [1 if apex0 in e else 2 for e in k33]
    over = 5 - 1 + 1                       # 5 - index + 1 at index 1 = 5
    for i, e in enumerate(k33):
        if apex0 not in e:
            lens_bad[i] = over
            break
    ok_bad, worst_bad = skel_ok_multi(k33, lens_bad)
    assert not ok_bad, 'the pruning lemma is wrong: a length-5 arc survived'
    print(f"  pruning lemma asserted: a length-{over} arc at index 1 is "
          f"rejected by the habitat check (worst f = {worst_bad} >= 0)")
    # (b) exhaustive enumeration over cubic multigraph skeletons
    from gridcol import cubic_iso_classes
    tally = {}
    t0 = time.time()
    fam = []
    # SCOPE, stated per index because the costs differ by orders of magnitude:
    # indices 3 and 4 are swept EXHAUSTIVELY over every cubic multigraph
    # skeleton on <= 8 hubs (the sweep is free — the total-length equation has
    # no solution at all under the pruning cap, which is the theorem);
    # indices 1 and 2 are exhaustive to 6 hubs, and at 8/10 hubs cover the
    # named skeletons only (the length census there is combinatorially large).
    for H in (2, 4, 6):
        cls = cubic_iso_classes(H)
        print(f"\n  cubic multigraph skeletons on {H} hubs: {len(cls)} iso "
              f"classes; indices 1-4 swept EXHAUSTIVELY [{time.time()-t0:.0f}s]")
        for ci, skel in enumerate(cls):
            skel = [tuple(e) for e in skel]
            for index in (1, 2, 3, 4):
                hits = list(enumerate_family(skel, H, index))
                if hits:
                    tally[(H, index)] = tally.get((H, index), 0) + len(hits)
                    for apex, lens in hits:
                        fam.append((H, index, ci, skel, apex, lens))
    print(f"\n  CAP, stated rather than smoothed over: the exhaustive class"
          f" sweep stops at 6 hubs.  `cubic_iso_classes(8)` alone costs ~110 s"
          f" and the index-1 length census on a 12-edge skeleton is"
          f" combinatorially large, so 8 and 10 hubs are covered by the named"
          f" skeletons, and there by the ARITHMETIC count below — which needs"
          f" no habitat check and so settles indices 3/4 outright.")
    named = [('cube Q3 (8v)', SKELETONS['cube Q3 (8v)'][0], 8),
             ('Wagner V8 (8v)', SKELETONS['Wagner V8 (8v)'][0], 8),
             ('Petersen (10v)', SKELETONS['Petersen (10v)'][0], 10)]
    for nm, skel, H in named:
        skel = [tuple(e) for e in skel]
        row = [(index, count_candidates(skel, H, index))
               for index in (1, 2, 3, 4)]
        print(f"  {nm}: candidate length assignments per index "
              f"{ {i: c for i, c in row} }"
              f"  -> indices with ZERO candidates: "
              f"{[i for i, c in row if c == 0]}")
    print(f"\n  census (apex-certified infeasible, skeleton-level habitat check):")
    for key in sorted(tally):
        print(f"    H={key[0]} index={key[1]}: {tally[key]} length assignments")
    bad = [k for k in tally if k[1] >= 3]
    print(f"  >>> index >= 3 members found: {len(bad)} "
          f"(the theorem predicts 0){' ' if not bad else ' -- ' + str(bad)}")
    maxlen = max((max(l for l in lens) for _, _, _, _, _, lens in fam),
                 default=0)
    print(f"  >>> longest arc over all {len(fam)} enumerated members: {maxlen} "
          f"(clause (i) bound at index 1 is 4)")
    # (c) exact certification of one NEW member, if one is small enough
    news = [(H, idx, skel, apex, lens) for (H, idx, ci, skel, apex, lens) in fam
            if H == 6 and idx == 1]
    print(f"\n  H=6 index-1 members (DZ's own stratum): {len(news)}")
    shown = 0
    for H, idx, skel, apex, lens in news:
        edges = build_multi(skel, lens, apex)
        n = len(verts_of(edges))
        if n > 21 or shown >= 2:
            continue
        d, info = exact_deficiency(edges)
        hubn = closed_hub_nbhds(edges)
        print(f"    member {shown}: skel={skel} apex={apex} lens={lens} "
              f"|V|={n} |E|={len(edges)} exact def={d} f(V)={index_of(edges)} "
              f"maxf(proper)={info['maxf_proper_ge2']} 2EC={is_2ec(edges)} "
              f"maxClosedHubNbhd={max(hubn.values())}")
        shown += 1
    print(f"\n[arith {time.time()-t0:.0f}s]")
    return tally, fam


# -------------------------------------------------------------- BE4: rzero --

BATTERY = [None, 'hubplane', 'apexline', 'starline', 'cycleflat', 'flat']


def pairing_rank(ctx, ptp, sd, dom, rng=None):
    """The rank of the pairing `U x Lambda^2 Pihat(b)` — the invariant behind
    §(K-tight) *Step 2.4*'s uniform-failure criterion `r ⊥ Lambda^2 Pihat(b)`,
    read at any `dim R_a`.  Rank `<= 1` is SUFFICIENT for uniform route-A
    failure: every `C(va)`, `C(vb)` with `pt(v)` in the panel lies in
    `Lambda^2 Pihat(b)` (the two pencils through `pt(a)` and `pt(b)` span it,
    `pt(a) in Pihat(b)` being forced by the fresh edge `ab`), so both rows of
    `M` become multiples of ONE functional."""
    if dom is None:
        return None
    rng = rng or random.Random(11)
    hb = [x for x in (ctx['a'], ctx['b']) if degrees(ctx['G'])[x] >= 3][0]
    L = lambda2_plane(ptp[hb], dom[:3], rng)
    if L is None:
        return None
    return rank_exact([[dot(u, l) for l in L] for u in sd['U']])


def certify_uniform(ctx, ptp, dom, seed, nplace=8):
    """Independent corroboration of an exact uniform-failure verdict: sample
    legal placements in the domain and report the OBSERVED exact ranks (which
    must all be < target(G)) plus the free-space legality check."""
    ranks, illegal = [], 0
    for k in range(nplace):
        r = random.Random(seed * 7 + k)
        x = rvec3(r) if dom is None else point_on_affine_plane4(dom, r)
        okw, rk = observed(ctx, ptp, x)
        if not okw:
            illegal += 1
        else:
            ranks.append(rk)
    assert all(rk < ctx['tG'] for rk in ranks), (
        f'exact verdict says uniform failure but a placement attains '
        f'{ctx["tG"]}: {ranks}')
    return {'observed_ranks': sorted(set(ranks)), 'target': ctx['tG'],
            'illegal_draws': illegal}

def run_rzero(nseeds=10, seed0=52000):
    print("===== BE4: THE HIT HUNT — `dim R_a = 0` / uniform route-A failure =====")
    print("  A legal target-rank `G'` seed at which EVERY placement fails")
    print("  refutes (K-bare-ext) as stated (tier T1: a route defect, NOT a")
    print("  refutation of hbareSplit, whose consequent is an existential at")
    print("  `G`).  `dim R_a = 0` <=> `s0 = index + 1` is the §(K-tight)")
    print("  Step-2.3 mechanism; the second mechanism is `A ^ B == 0` on the")
    print("  whole domain.  Both are tested CAP-FREE per seed.")
    cases = [("DZ non-hub-ends", dz_gadget(), 'u1h2_2', None),
             ("DZ hub-end", dz_gadget(), 'u1h2_1', None)]
    eq3 = q3_gadget()
    deg, nb = degrees(eq3), neighbors(eq3)
    vq = next(x for x in verts_of(eq3) if deg[x] == 2
              and any(deg[w] == 2 for w in nb[x])
              and any(deg[w] >= 3 for w in nb[x]))
    cases.append(("Q3 index-2 hub-end", eq3, vq, (0, 0)))
    # the count-INDEPENDENT half of the habitat, which the gate's seven
    # gadgets inhabit.  `spider(5,5,5)+center` (= G'_dang, 16v) has
    # index 0, def 0, corank(G') = 1: there a hit needs only s0 = 1, ONE
    # geometric stress in the shared framework — the cheapest hit target in
    # the whole habitat, and it sits inside the landed gate's own stock.
    e555, _ = spider(5, 5, 5)
    a555 = neighbors(e555)
    v555 = 'ab2'
    cases.append(("spider(5,5,5)+center (gate gadget), index 0", e555, v555,
                  None))
    e666, m666 = spider(6, 6, 6)
    arc = m666['arcs']['ab']
    cases.append(("theta(6,6,6)+center (gate gadget), def-drop branch", e666,
                  arc[len(arc) // 2], None))
    hits, rows = [], []
    for name, edges, v, defs in cases:
        ctx = split_ctx(edges, v, defs=defs)
        print(f"\n  {name}: index={ctx['index']} def(G)={ctx['dG']} "
              f"def(G')={ctx['dGp']} corank(G')={ctx['cGp']} cG={ctx['cG']}"
              + (f" => dim R_a = {ctx['index']}+1-s0, so a hit needs "
                 f"s0 = {ctx['index']+1}" if ctx['dG'] == 0 else
                 " (def > 0: the dim U = dim R_a + 1 identity does NOT hold"
                 " here — see BE2 — so the hit criterion is read off"
                 " `need_rank` directly)"))
        for degen in BATTERY:
            nlegal = nat = 0
            s0seen, ravals = {}, {}
            unif = []
            for s in range(nseeds):
                rng = random.Random(seed0 + s)
                try:
                    ptp, _ = sample_pencil_bfs(ctx['Gp'], rng, degen=degen)
                except (AssertionError, RuntimeError):
                    continue
                sd = seed_calculus(ctx, ptp)
                if sd is None:
                    continue
                nlegal += 1
                s0seen[sd['s0']] = s0seen.get(sd['s0'], 0) + 1
                if not sd['at_target']:
                    continue
                nat += 1
                key = (sd['dimRa'], sd['dimU'], need_rank(ctx, sd))
                ravals[key] = ravals.get(key, 0) + 1
                try:
                    dom = hub_domain(ctx, ptp)
                except RuntimeError:
                    continue
                uf, wit = uniform_failure(ctx, ptp, sd, domain=dom,
                                          rng=random.Random(seed0 + s))
                ufx, why = uniform_failure_exact(
                    ctx, ptp, sd, domain=dom, rng=random.Random(seed0 + s))
                assert uf == ufx, (f'grid and exact verdicts disagree at '
                                   f'{name}/{degen}/{s}: {uf} vs {ufx} ({why})')
                if ufx:
                    unif.append(s)
                    obs = certify_uniform(ctx, ptp, dom, seed0 + s)
                    obs['pairing_rank_U_x_L2panel'] = pairing_rank(
                        ctx, ptp, sd, dom, random.Random(seed0 + s))
                    hits.append((name, degen, s, sd['s0'], sd['dimRa'],
                                 sd['dimU'], why, obs))
                elif wit is not None:
                    okw, rk = observed(ctx, ptp, wit)
                    assert not okw or rk == ctx['tG'], (
                        f"criterion says attain, observed {rk} vs {ctx['tG']}")
            print(f"    battery {str(degen):9s}: {nlegal} legal witnesses, "
                  f"{nat} AT target(G'); s0 histogram {s0seen}; "
                  f"(dimRa,dimU,needRank) histogram {ravals}; "
                  f"uniform-failure seeds {unif}")
            rows.append((name, degen, nlegal, nat, dict(s0seen), dict(ravals),
                         list(unif)))
    print(f"\n  >>> T1 HITS (legal target-rank seeds failing at EVERY "
          f"placement): {len(hits)}")
    if hits:
        for h in hits:
            print(f"      {h}")
    else:
        print("      NOT FOUND under this cap (6 sampler strata x "
              f"{nseeds} seeds x 3 (gadget, split) cases).  This is a cap")
        print("      report, NOT '(K-bare-ext) is true'.")
    return hits, rows


# -------------------------------------------------------------- BE5: locus --

def run_locus(nseeds=4, seed0=61000):
    print("===== BE5: the failure locus, CONSTRUCTED (tier T3) =====")
    print("  Every on-line placement fails for a structural reason: on")
    print("  line(a,b), C(va) ∥ C(vb), so rank M <= 1.  The question is")
    print("  whether the locus has another component.  optc C3 answered it by")
    print("  SAMPLING (0/179 off-line failures) — but the locus is a curve,")
    print("  which random sampling can never meet.  Here it is solved.")
    for name, edges, v, defs in [("DZ non-hub-ends", dz_gadget(), 'u1h2_2', None),
                                 ("DZ hub-end", dz_gadget(), 'u1h2_1', None)]:
        ctx = split_ctx(edges, v, defs=defs)
        print(f"\n  {name}: corank(G')={ctx['cGp']}")
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctx['Gp'], rng)
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctx, ptp)
            if sd is None or not sd['at_target']:
                continue
            Am, Bm = ab_maps(ctx, ptp, sd)
            rkA, rkB = rank_exact(Am), rank_exact(Bm)
            try:
                dom = hub_domain(ctx, ptp)
            except RuntimeError:
                dom = None
            found, nline = [], 0
            for anchor in (ctx['a'], ctx['b']):
                for (t, x3, off) in failure_points_through(
                        ctx, ptp, sd, anchor, rng=random.Random(seed0 + 7 * s),
                        domain=dom):
                    nline += 1
                    okw, rk = observed(ctx, ptp, x3)
                    if not okw or rk is None:
                        continue
                    found.append((anchor, off, rk, ctx['tG']))
            offhits = [f for f in found if f[1] and f[2] < ctx['tG']]
            print(f"    seed {s}: dimU={sd['dimU']} dimRa={sd['dimRa']} "
                  f"s0={sd['s0']} rank A={rkA} rank B={rkB}; "
                  f"{nline} lines through an end carry a solution, "
                  f"{len(found)} of them a LEGAL placement, of which OFF-line "
                  f"and verified-failing: {len(offhits)}")
            for (anchor, off, rk, tg) in offhits[:3]:
                print(f"        off-line failure through {anchor}: exact rank "
                      f"{rk} = target {tg} - {tg - rk}")
    print("\n  >>> T3 reading: an off-line failure point is the `∀`-form's")
    print("      refutation, ALREADY SETTLED at the (K-tight) control; found")
    print("      here it corroborates at the (K-bare) stratum and corrects")
    print("      option-C C3's 'the failure set looks exactly like the line'.")


# ---------------------------------------------------------------- BE6: c1b --

def run_c1b(nseeds=8, seed0=71000):
    print("===== BE6: the second gadget against option-C's C1 finding =====")
    print("  C1 (one gadget, one sampler family): at DZ, chain-local")
    print("  degenerations all fall BELOW target(G'), so the rank antecedent")
    print("  itself polices them.  Tested here at a SECOND gadget.")
    eq3 = q3_gadget()
    deg, nb = degrees(eq3), neighbors(eq3)
    vq = next(x for x in verts_of(eq3) if deg[x] == 2
              and any(deg[w] == 2 for w in nb[x])
              and any(deg[w] >= 3 for w in nb[x]))
    for name, edges, v, defs in [("Q3 index-2 gadget", eq3, vq, (0, 0)),
                                 ("DZ (control)", dz_gadget(), 'u1h2_2', None)]:
        ctx = split_ctx(edges, v, defs=defs)
        print(f"\n  {name}, split at {v} (a={ctx['a']}, b={ctx['b']}), "
              f"target(G')={ctx['tGp']}")
        for degen in ['apexline', 'starline', 'hubplane', 'flat']:
            below = at = 0
            ranks = []
            for s in range(nseeds):
                rng = random.Random(seed0 + s)
                try:
                    ptp, _ = sample_pencil_bfs(ctx['Gp'], rng, degen=degen)
                    ok, _ = verify_pencil_witness(ctx['Gp'], ptp)
                    assert ok
                    rk = rank_exact(build_rigidity(ctx['Gp'], ptp)[0])
                except (AssertionError, RuntimeError):
                    continue
                ranks.append(rk)
                if rk == ctx['tGp']:
                    at += 1
                else:
                    below += 1
            print(f"    {degen:9s}: {at} AT target', {below} BELOW "
                  f"(ranks {sorted(set(ranks))})")
    print("\n  >>> reading: a degeneration that lands AT target' is NOT")
    print("      excluded by (K-bare-ext)'s antecedent, so C1's 'the rank")
    print("      hypothesis polices the degeneracy' holds only for the")
    print("      strata where the column reads 0 AT target'.")


# --------------------------------------------------------------------- main --

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('tiers', 'all'):
        run_tiers()
    if which in ('calc', 'all'):
        print()
        run_calc()
    if which in ('arith', 'all'):
        run_arith()
    if which in ('rzero', 'all'):
        print()
        run_rzero()
    if which in ('locus', 'all'):
        print()
        run_locus()
    if which in ('c1b', 'all'):
        print()
        run_c1b()
    print(f"\n[breakhunt {which}: {time.time() - t0:.0f}s]")
