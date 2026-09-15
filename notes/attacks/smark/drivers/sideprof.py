#!/usr/bin/env python3
"""
sideprof.py -- the smark attack's side-profile control: block profile of rho_bar at a
generic flag pair, in the ADAPTED basis (b1 = p_u, b2 = p_v, b3 b4 = pi_u cap pi_v).

    python3 notes/attacks/smark/drivers/sideprof.py --side NAME --seed S --draws N [--verbose]
    (run from the repository root; workbook: notes/pencil/workbook/attack-smark.md S5)
    NAME in: ear1..ear5 theta33 theta34 theta44 tail cycletail dumbbell all

Per draw:
  * exact pencil configuration of the side at a PRESCRIBED generic flag pair
    (corpus sampler `bdecor.sample_by_branches(..., fixed=...)`, or the same
    three corpus primitives driven by a pendant-aware skeleton for `tail`);
  * asserts: `kbare_common.verify_pencil_witness`, `binduc.assert_generic_star`,
    the four exact genericity conditions on the flag pair, the configuration
    realizes the flags (p_u, p_v as points; every neighbour of u in pi_u, of v
    in pi_v; when the closed star spans a plane, that plane IS the prescribed
    one), and the PENDANT TRICK identity: attaching two pendants at u placed in
    pi_u and two at v placed in pi_v leaves rho_bar unchanged as a space;
  * rho_bar via `bimage.rho_bar_of` (= `binduc.rel_screw_space` + span);
  * (f, g, delta) via `bdecor.d3` / `bdecor.weld_d3`, cross-checked against
    `binduc.def_by_partitions` (|V| <= 10) and `kbare_common.exact_deficiency`;
  * coordinate change Lambda^2(T), T = [b1 b2 b3 b4]^{-1}, via `bunif.mat_inv`
    and `bunif.lam2_mat`; block profile via `bunif.profile` (computed BOTH in
    adapted coordinates and in the original coordinates via `bunif.blocks_of`,
    asserted equal);
  * Gram ranks of Q1, Q2, Q = Q1 - Q2 on rho_bar in adapted coordinates
    (Q asserted to be half of `bimage.klein` transported, and its Gram rank
    asserted equal to the Klein Gram rank in original coordinates).

All arithmetic exact (fractions.Fraction).  Every rng seeded; seed printed.
Reads the repository READ-ONLY; writes nothing.
"""
import argparse
import itertools
import os
import random
import sys
import time
from fractions import Fraction as F

# repo root = four directories above this file (notes/attacks/smark/drivers/)
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))))
sys.path.insert(0, os.path.join(REPO, 'notes', 'scripts'))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (PL, hat, rank as rank_exact, nullspace,        # noqa: E402
                       wedge2, neighbors)
from kbare_common import (verts_of, verify_pencil_witness,             # noqa: E402
                          exact_deficiency)
from binduc import (assert_generic_star, def_by_partitions,            # noqa: E402
                    rel_screw_space)
from bimage import (dim, span, same_space, plane_meet, plane_at,       # noqa: E402
                    rho_bar_of, sample_flags, pt_in, klein)
from bwin import dehom                                                 # noqa: E402
from bdecor import (d3, weld_d3, flag_assignment, draw_branch,         # noqa: E402
                    assemble, sample_by_branches, hubs_and_branches,
                    girth)
from bunif import (SUBS, CAP, profile, blocks_of, mat_inv,             # noqa: E402
                   lam2_mat, generic_c)

# ------------------------------------------------------------------ sides


def path_side(m):
    """ear m: u - w0 - ... - w{m-1} - v."""
    E, prev = [], 'u'
    for i in range(m):
        E.append((prev, f'w{i}'))
        prev = f'w{i}'
    E.append((prev, 'v'))
    return E


def theta_side(a, b):
    """two internally disjoint u-v paths with a and b interior vertices."""
    E = []
    for tag, m in (('x', a), ('y', b)):
        prev = 'u'
        for i in range(m):
            E.append((prev, f'{tag}{i}'))
            prev = f'{tag}{i}'
        E.append((prev, 'v'))
    return E


def tail_side():
    """ear3 (u-w0-w1-w2-v) plus a pendant path w1-q0-q1 off the middle
    interior vertex w1 (deg w1 = 3)."""
    return path_side(3) + [('w1', 'q0'), ('q0', 'q1')]


def cycletail_side():
    """5-cycle u,c1,c2,c3,c4 through u; v joined to c2 (distance 2 from u;
    the 5-cycle has two such vertices, c2 chosen) by the path c2-t-v."""
    return [('u', 'c1'), ('c1', 'c2'), ('c2', 'c3'), ('c3', 'c4'),
            ('c4', 'u'), ('c2', 't'), ('t', 'v')]


def dumbbell_side():
    """5-cycle u,a1,a2,a3,a4 and 5-cycle v,b1,b2,b3,b4, joined by the edge
    a2-b2 (a2 at distance 2 from u, b2 at distance 2 from v)."""
    return [('u', 'a1'), ('a1', 'a2'), ('a2', 'a3'), ('a3', 'a4'), ('a4', 'u'),
            ('v', 'b1'), ('b1', 'b2'), ('b2', 'b3'), ('b3', 'b4'), ('b4', 'v'),
            ('a2', 'b2')]


SIDES = {
    'ear1': lambda: path_side(1), 'ear2': lambda: path_side(2),
    'ear3': lambda: path_side(3), 'ear4': lambda: path_side(4),
    'ear5': lambda: path_side(5),
    'theta33': lambda: theta_side(3, 3), 'theta34': lambda: theta_side(3, 4),
    'theta44': lambda: theta_side(4, 4),
    'tail': tail_side, 'cycletail': cycletail_side, 'dumbbell': dumbbell_side,
}
ORDER = ['ear1', 'ear2', 'ear3', 'ear4', 'ear5', 'theta33', 'theta34',
         'theta44', 'tail', 'cycletail', 'dumbbell']

# ------------------------------------------- block labels (task convention)
#
# Adapted basis b1 = p_u, b2 = p_v, b3, b4 span pi_u cap pi_v.  In
# `exactcore.PL` order (01,02,03,12,13,23) the adapted coordinates are
#   x0 <-> b1^b2      : task block  L   (bunif 'M',   the line p_u p_v)
#   x1,x2 <-> b1^b3, b1^b4 : task block Pu  (bunif 'Pix', pencil at u in pi_u)
#   x3,x4 <-> b2^b3, b2^b4 : task block Pv  (bunif 'Piy', pencil at v in pi_v)
#   x5 <-> b3^b4      : task block  ell (bunif 'L',   the line pi_u cap pi_v)
TASK_OF = {'M': 'L', 'Pix': 'Pu', 'Piy': 'Pv', 'L': 'ell'}
TASK_ORDER = ['L', 'Pu', 'Pv', 'ell']
TASK_IDX = {'L': [0], 'Pu': [1, 2], 'Pv': [3, 4], 'ell': [5]}
TASK_CAP = {'L': 1, 'Pu': 2, 'Pv': 2, 'ell': 1}
E6 = [[F(1) if i == j else F(0) for j in range(6)] for i in range(6)]
B_ADAPTED = {b: [E6[i] for i in TASK_IDX[TASK_OF[b]]] for b in TASK_OF}
# the 16 U's, in the task's order: by size, then (L, Pu, Pv, ell)
U_LIST = [tuple(s) for k in range(5)
          for s in itertools.combinations(TASK_ORDER, k)]


def bunif_key(U):
    """task-labelled subset -> bunif `SUBS` key."""
    inv = {v: k for k, v in TASK_OF.items()}
    return tuple(sorted(inv[b] for b in U))


def ulabel(U):
    return 'none' if not U else ('all' if len(U) == 4 else '+'.join(U))


def udim(U):
    return sum(TASK_CAP[b] for b in U)


# ------------------------------------------------ pendant-aware skeleton


def side_skeleton(edges, u, v):
    """`bdecor.hubs_and_branches` with degree-1 vertices ALSO in W, so a
    pendant path is a branch ending at a terminal (the corpus function
    IndexErrors on a pendant end).  Identical to the corpus function on a
    side without degree-1 vertices (asserted by the caller)."""
    nb = neighbors(edges)
    W = {u, v} | {z for z in verts_of(edges) if len(nb[z]) >= 3
                  or len(nb[z]) == 1}
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


def sample_side(edges, u, v, rng, fixed, s=20, tries=40):
    """Achieve(phi) sampler at the prescribed flags `fixed = {u: (p_u, basis
    of pi_u), v: (p_v, basis of pi_v)}`.  Corpus `sample_by_branches` when
    the side has no degree-1 vertex; otherwise the same three primitives
    (`flag_assignment`, `draw_branch`, `assemble`) on the pendant-aware
    skeleton.  Returns (affine pt, planes, W, branches) or None."""
    nb = neighbors(edges)
    if all(len(nb[z]) != 1 for z in verts_of(edges)):
        W0, br0 = hubs_and_branches(edges, u, v)
        W1, br1 = side_skeleton(edges, u, v)
        assert (W0, sorted(br0)) == (W1, sorted(br1)), 'skeleton mismatch'
        return sample_by_branches(edges, u, v, rng, s=s, tries=tries,
                                  fixed=fixed)
    W, branches = side_skeleton(edges, u, v)
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


# ------------------------------------------------------ flags & checks


def draw_flags(rng, s=20, tries=200):
    """`bimage.sample_flags(rng, 'nonadj')` with both points affine
    (last coordinate nonzero)."""
    for _ in range(tries):
        pu, Bu, pv, Bv = sample_flags(rng, 'nonadj', s)
        if pu[3] == 0 or pv[3] == 0:
            continue
        return pu, Bu, pv, Bv
    raise RuntimeError('draw_flags: no affine draw')


def normal_of(B):
    ns = nullspace(B)
    assert len(ns) == 1, 'plane basis must have rank 3'
    return ns[0]


def assert_generic_flags(pu, Bu, pv, Bv):
    """The four exact conditions: p_u != p_v, pi_u != pi_v, p_v notin pi_u,
    p_u notin pi_v."""
    assert rank_exact([pu, pv]) == 2, 'p_u = p_v'
    assert rank_exact([normal_of(Bu), normal_of(Bv)]) == 2, 'pi_u = pi_v'
    assert rank_exact(Bu + [pv]) == 4, 'p_v in pi_u'
    assert rank_exact(Bv + [pu]) == 4, 'p_u in pi_v'


def assert_realizes_flags(edges, pt, u, v, pu, Bu, pv, Bv):
    """The configuration carries the prescribed flag pair."""
    nb = neighbors(edges)
    for z, p, B in ((u, pu, Bu), (v, pv, Bv)):
        assert rank_exact([hat(pt[z]), p]) == 1, f'p_{z} not the flag point'
        for w in nb[z]:
            assert rank_exact(B + [hat(pt[w])]) == 3, \
                f'neighbour {w} of {z} off pi_{z}'
        Pz = plane_at(edges, pt, z)
        if Pz is not None:
            assert same_space(Pz, B), f'closed-star plane at {z} != pi_{z}'


def pendant_check(edges, pt, u, v, Bu, Bv, S, rng, s=20, tries=60):
    """PENDANT TRICK: attach pendants pu1, pu2 at u (points in pi_u) and pv1,
    pv2 at v (points in pi_v); the augmented graph is a pencil configuration
    whose closed-star plane at u (resp. v) IS pi_u (resp. pi_v), and its
    rho_bar equals the side's as a space.  Returns True when asserted."""
    for _ in range(tries):
        aug = list(edges) + [(u, 'pu1'), (u, 'pu2'), (v, 'pv1'), (v, 'pv2')]
        pts = dict(pt)
        ok = True
        for name, B in (('pu1', Bu), ('pu2', Bu), ('pv1', Bv), ('pv2', Bv)):
            x = pt_in(B, rng, s)
            if x[3] == 0:
                ok = False
                break
            pts[name] = tuple(dehom(x))
        if not ok or len(set(pts.values())) != len(pts):
            continue
        try:
            assert_generic_star(aug, pts)
        except AssertionError:
            continue
        okw, _ = verify_pencil_witness(aug, pts)
        if not okw:
            continue
        assert same_space(plane_at(aug, pts, u), Bu), 'pendant plane at u'
        assert same_space(plane_at(aug, pts, v), Bv), 'pendant plane at v'
        S2, r2, _dM, _rk = rho_bar_of(aug, pts, u, v)
        assert r2 == dim(S) and same_space(S, S2), \
            'pendant trick changed rho_bar'
        return True
    raise RuntimeError('pendant_check: no legal pendant placement')


# --------------------------------------------------- adapted coordinates


def adapted_transform(pt, u, v, Bu, Bv):
    """(Lambda^2 T, [b1, b2, b3, b4], T) with T = [b1 b2 b3 b4]^{-1}."""
    b1, b2 = hat(pt[u]), hat(pt[v])
    Lb = plane_meet(Bu, Bv)
    assert len(Lb) == 2, 'pi_u cap pi_v is not a line'
    b3, b4 = Lb
    basis = [b1, b2, b3, b4]
    assert rank_exact(basis) == 4, 'adapted basis degenerate'
    Bmat = [[basis[k][i] for k in range(4)] for i in range(4)]   # columns
    T = mat_inv(Bmat)
    assert T is not None
    L2T = lam2_mat(T)
    # sanity: b_k ^ b_l -> the unit vector at PL index of (k,l)
    for idx, (k, l) in enumerate(PL):
        img = apply6(L2T, wedge2(basis[k], basis[l]))
        assert img == E6[idx], ('Lambda^2 T does not send b_k^b_l to e_kl',
                                k, l, img)
    return L2T, basis, T


def apply6(M, x):
    return [sum(M[i][j] * x[j] for j in range(6)) for i in range(6)]


def det4(M):
    """Exact determinant by Laplace expansion (4 x 4)."""
    n = len(M)
    if n == 1:
        return M[0][0]
    tot = F(0)
    for j in range(n):
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        tot += (-1) ** j * M[0][j] * det4(minor)
    return tot


def to_adapted(L2T, S):
    return span([apply6(L2T, r) for r in S]) if S else []


# ------------------------------------------------------------ the forms


def Q1(x, y):
    return (x[0] * y[5] + y[0] * x[5]) / 2


def Q2(x, y):
    """(det[x_u | y_v] + det[y_u | x_v]) / 2, x_u = (x1, x2), y_v = (y3, y4)."""
    return ((x[1] * y[4] - x[2] * y[3]) + (y[1] * x[4] - y[2] * x[3])) / 2


def Qk(x, y):
    return Q1(x, y) - Q2(x, y)


def gram_rank(form, S):
    if not S:
        return 0
    G = [[form(a, b) for b in S] for a in S]
    return rank_exact(G)


# ---------------------------------------------------------- combinatorics


def side_deltas(edges, u, v):
    """(f, g, delta) with f = def_3(H), g = def_3(H/uv); primary oracle
    `bdecor.d3` / `bdecor.weld_d3`, cross-checked."""
    V = sorted(verts_of(edges), key=str)
    f, g = d3(edges), weld_d3(edges, u, v)
    f2, _info = exact_deficiency(edges)
    assert f2 == f, ('exact_deficiency disagrees with d3', f2, f)
    if len(V) <= 10:
        f3 = def_by_partitions(edges, V, D=3)
        g3 = def_by_partitions(edges, V, D=3, together=(u, v))
        assert (f3, g3) == (f, g), ('def_by_partitions disagrees', f3, g3, f, g)
        xc = 'd3/exact_deficiency/def_by_partitions agree'
    else:
        xc = 'd3/exact_deficiency agree (def_by_partitions skipped, |V| > 10)'
    return f, g, f - g, xc


# ----------------------------------------------------------------- driver


def run_side(name, seed, ndraw, verbose=False):
    edges = SIDES[name]()
    u, v = 'u', 'v'
    V = sorted(verts_of(edges), key=str)
    gi = girth(edges)
    assert gi is None or gi >= 5, ('girth < 5', gi)
    rng = random.Random(seed)
    t0 = time.time()
    f, g, delta, xc = side_deltas(edges, u, v)
    print(f'== side {name}: |V| = {len(V)}, |E| = {len(edges)}, '
          f'girth = {gi}, seed = {seed}, draws = {ndraw}')
    print(f'   edges: {edges}')
    print(f'   f = def3(H) = {f}, g = def3(H/uv) = {g}, delta = {delta}'
          f'   [{xc}]')
    target = 6 * (len(V) - 1) - f
    prof_counts, gram_counts, rows = {}, {}, []
    fails = 0
    for d in range(ndraw):
        got = None
        for attempt in range(40):
            pu, Bu, pv, Bv = draw_flags(rng)
            assert_generic_flags(pu, Bu, pv, Bv)
            got = sample_side(edges, u, v, rng, {u: (pu, Bu), v: (pv, Bv)})
            if got is not None:
                break
        if got is None:
            fails += 1
            print(f'   draw {d}: SAMPLER FAILED (40 flag pairs x 40 tries)')
            continue
        pt, _planes, _W, _br = got
        ok, _ = verify_pencil_witness(edges, pt)
        assert ok, 'verify_pencil_witness failed'
        assert_generic_star(edges, pt)
        assert_realizes_flags(edges, pt, u, v, pu, Bu, pv, Bv)
        # rho_bar
        S, rho, dM, rk = rho_bar_of(edges, pt, u, v)
        _r2, img, _k, _rk2 = rel_screw_space(edges, pt, u, v)
        assert same_space(span(img), S)
        attains = (rk == target)
        pend = pendant_check(edges, pt, u, v, Bu, Bv, S, rng)
        # adapted coordinates
        L2T, basis, T = adapted_transform(pt, u, v, Bu, Bv)
        Sad = to_adapted(L2T, S)
        assert dim(Sad) == rho
        # profile: adapted (coordinate blocks) and original (bunif.blocks_of)
        cad = profile(Sad, B_ADAPTED)
        fr = (hat(pt[u]), Bu, hat(pt[v]), Bv, basis[2], basis[3])
        Borig = blocks_of(fr)
        corig = profile(S, Borig)
        assert cad == corig, ('adapted vs original profile differ', cad, corig)
        for b, rows_b in Borig.items():      # blocks map to coordinate blocks
            assert same_space(to_adapted(L2T, rows_b), B_ADAPTED[b]), b
        # Gram ranks
        gq1, gq2, gq = (gram_rank(Q1, Sad), gram_rank(Q2, Sad),
                        gram_rank(Qk, Sad))
        gk = gram_rank(klein, S)
        # Q is half the Klein form transported by Lambda^2 T, which scales it
        # by det T: 2 Q(L2T a, L2T b) = det(T) klein(a, b) on every pair.
        dT = det4(T)
        assert dT != 0
        for a in S:
            for b in S:
                assert 2 * Qk(apply6(L2T, a), apply6(L2T, b)) == dT * klein(a, b), \
                    'Q is not the transported Klein form'
        assert gq == gk, ('Klein Gram rank differs across coordinates', gq, gk)
        prof = tuple(cad[bunif_key(U)] for U in U_LIST)
        exc = tuple(cad[bunif_key(U)] - generic_c(rho, udim(U)) for U in U_LIST)
        key = (rho, prof)
        prof_counts[key] = prof_counts.get(key, 0) + 1
        gram_counts[(gq1, gq2, gq)] = gram_counts.get((gq1, gq2, gq), 0) + 1
        rows.append((d, rho, delta, attains, prof, exc, (gq1, gq2, gq)))
        print(f'   draw {d}: rho = {rho}, delta = {delta}, rho==delta: '
              f'{rho == delta}; side attains (rank {rk} vs target {target}): '
              f'{attains}; pendant-trick rho_bar identity: {pend}')
        print(f'      c(U) over {len(U_LIST)} U (order: '
              f'{", ".join(ulabel(U) for U in U_LIST)}):')
        print(f'      c      = {prof}')
        print(f'      excess = {exc}')
        print(f'      Gram ranks on rho_bar: Q1 = {gq1}, Q2 = {gq2}, '
              f'Q = Q1 - Q2 = {gq}'
              f'{"  (totally isotropic)" if gq == 0 else ""}')
        if verbose:
            print('      rho_bar basis, adapted coords (x0 | xu1 xu2 | xv1 xv2 | xinf):')
            for r in Sad:
                print('        ', [str(x) for x in r])
    # summary
    print(f'   -- summary for {name}: {ndraw - fails}/{ndraw} draws sampled'
          f'{f", {fails} FAILED" if fails else ""}; '
          f'{len(prof_counts)} distinct (rho, profile); '
          f'{len(gram_counts)} distinct Gram-rank triple(s)')
    for (rho, prof), cnt in sorted(prof_counts.items()):
        print(f'      profile x{cnt}  (rho = {rho}, delta = {delta}):')
        print(f'        {"U":14s} {"dimU":>4s} {"c(U)":>4s} {"gen":>3s} {"exc":>3s}')
        for U, c in zip(U_LIST, prof):
            gen = generic_c(rho, udim(U))
            print(f'        {ulabel(U):14s} {udim(U):4d} {c:4d} {gen:3d} '
                  f'{c - gen:3d}')
    for tri, cnt in sorted(gram_counts.items()):
        print(f'      Gram ranks (Q1, Q2, Q) = {tri}  x{cnt}')
    print(f'   [{time.time() - t0:.1f} s]')
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--side', required=True,
                    help='one of ' + ' '.join(ORDER) + ' or all')
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, required=True)
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    names = ORDER if a.side == 'all' else [a.side]
    for nm in names:
        if nm not in SIDES:
            sys.exit(f'unknown side {nm}')
    print(f'strata_proto: seed = {a.seed}, draws = {a.draws}, '
          f'sides = {names}')
    print('adapted basis: b1 = p_u, b2 = p_v, (b3, b4) = pi_u cap pi_v; '
          'PL order (01,02,03,12,13,23) -> (L | Pu Pu | Pv Pv | ell)')
    for nm in names:
        run_side(nm, a.seed, a.draws, a.verbose)


if __name__ == '__main__':
    main()
