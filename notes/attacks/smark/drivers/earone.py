#!/usr/bin/env python3
"""
earone.py -- the smark attack's control for workbook S9 (the ear1 composition
criterion) and S7 (excess = attainment loss of a bar-augmented side).

    python3 notes/attacks/smark/drivers/earone.py --side NAME|all|all2|both --seed S --draws N [--px K]
    (run from the repository root; workbook: notes/pencil/workbook/attack-smark.md S7, S9)

Per side and per draw (exact Q, seeded; the sampling, genericity asserts and
adapted coordinates are `sideprof.py`'s):
  * rho_bar of the side at a prescribed generic flag pair; rho, delta, attains,
    welded-attains (dim M(H/uv) == 6 + g, computed as dim M(H) - rho);
  * A' = rho_bar cap (Pi_u + Pi_v) in adapted coordinates (x_M = x_L = 0):
    dim A', the Q2 = det[x_u|x_v] Gram rank on A', and -- when A' is a
    Q2-isotropic plane -- which ruling: R^y = y ^ W (projection to x_u or
    x_v has rank 2) or R_w = w ^ M (both projections rank <= 1);
  * dim(T cap <M,L>) for T = rho_bar^perp, and the S9 identity
    dim A' = rho - 2 + dim(T cap <M,L>)  (asserted);
  * S7 check: dim A' == dim M(H + bar M + bar L) - dim M(H/uv), the two bars
    imposed as two extra rows on the relative screw (asserted);
  * the S9 PREDICTED verdict (delta <= 4: dim A' <= 2 and A' not an R^y;
    delta = 5: dim A' <= 3; delta = 6: yes);
  * the ACTUAL verdict at --px random points p_x on the line L = pi_u cap pi_v:
    dim(rho_bar + p_x ^ M) == min(delta + 2, 6), AND the composed graph
    G = H + x (edges ux, xv, p_x on L) verified as a pencil configuration
    with rank R(G) == 6 |V(G)| - 6 - def3(G); def3(G) is asserted to equal
    f + 2 - min(delta + 2, 6) (the brief's composition formula).
Predicted and actual must agree at every generic p_x; a disagreement is the
"what would change this" of S9 and is printed as MISMATCH.

Reads the repository READ-ONLY; writes nothing.
"""
import argparse
import os
import random
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sideprof as SP  # noqa: E402  (bootstraps the harness path itself)

from exactcore import rank as rank_exact, nullspace, wedge2, hat  # noqa: E402
from kbare_common import verts_of, verify_pencil_witness  # noqa: E402
from binduc import assert_generic_star  # noqa: E402
from bimage import span, dim, rho_bar_of  # noqa: E402
from bwin import dehom  # noqa: E402
from bdecor import d3  # noqa: E402
from bunif import profile, generic_c  # noqa: E402


def combine(coeffs, rows):
    return [sum((c * r[j] for c, r in zip(coeffs, rows)), F(0))
            for j in range(len(rows[0]))]


def A_prime(Sad):
    """rho_bar cap (Pi_u + Pi_v): the elements with x_M = x_L = 0."""
    if not Sad:
        return []
    cons = [[r[0] for r in Sad], [r[5] for r in Sad]]
    return [combine(c, Sad) for c in nullspace(cons)]


def q2_gram_rank(A):
    return SP.gram_rank(SP.Q2, A) if A else 0


def ruling_family(A):
    """For a Q2-isotropic 2-plane A in Pi_u + Pi_v: 'R^y' (y ^ W, vertex on
    M) or 'R_w' (w ^ M, vertex on L)."""
    xu = [[r[1], r[2]] for r in A]
    xv = [[r[3], r[4]] for r in A]
    if max(rank_exact(xu), rank_exact(xv)) == 2:
        return 'R^y'
    return 'R_w'


def t_cap_ML(Sad):
    """dim(T cap <M,L>), T = Klein complement of rho_bar; t = (t_M, 0..0, t_L)
    is Q-orthogonal to s iff t_M s_L + t_L s_M = 0."""
    if not Sad:
        return 2
    return 2 - rank_exact([[s[5], s[0]] for s in Sad])


def motions_with_bars(Sad):
    """dim M(H + bar M + bar L) - dim M(H/uv) = dim{s in rho_bar : Q(s, M) =
    Q(s, L) = 0} = dim{s : s_L = 0 and s_M = 0} -- computed as a rank
    condition, independently of A_prime's route."""
    if not Sad:
        return 0
    return len(Sad) - rank_exact([[s[5], s[0]] for s in Sad])


def predicted(delta, dimA, fam):
    if delta >= 6:
        return True
    if delta == 5:
        return dimA <= 3
    return dimA <= 2 and not (dimA == 2 and fam == 'R^y')


def run(name, seed, ndraw, npx):
    edges = SP.SIDES[name]()
    u, v = 'u', 'v'
    V = sorted(verts_of(edges), key=str)
    gi = SP.girth(edges)
    assert gi is None or gi >= 5, ('girth < 5', gi)
    rng = random.Random(seed)
    t0 = time.time()
    f, g, delta, xc = SP.side_deltas(edges, u, v)
    nb = SP.neighbors(edges)
    print(f'== side {name}: |V| = {len(V)}, |E| = {len(edges)}, girth = {gi}, '
          f'side-degrees ({len(nb[u])}, {len(nb[v])}), seed = {seed}, '
          f'draws = {ndraw}, px = {npx}')
    print(f'   f = {f}, g = {g}, delta = {delta}   [{xc}]')
    target = 6 * (len(V) - 1) - f
    Gedges = edges + [(u, 'x'), ('x', v)]
    d3G = d3(Gedges)
    assert d3G == f + 2 - min(delta + 2, 6), ('composition formula', d3G, f, delta)
    targetG = 6 * len(V) - d3G          # |V(G)| = |V| + 1
    summary = {'draws': 0, 'fail': 0, 'agree': 0, 'mismatch': 0,
               'pred_yes': 0, 'attain': 0, 'weld': 0}
    exc_seen = {}
    for d in range(ndraw):
        got = None
        for _ in range(40):
            pu, Bu, pv, Bv = SP.draw_flags(rng)
            SP.assert_generic_flags(pu, Bu, pv, Bv)
            got = SP.sample_side(edges, u, v, rng, {u: (pu, Bu), v: (pv, Bv)})
            if got is not None:
                break
        if got is None:
            summary['fail'] += 1
            print(f'   draw {d}: SAMPLER FAILED')
            continue
        pt, _pl, _W, _br = got
        ok, _ = verify_pencil_witness(edges, pt)
        assert ok
        assert_generic_star(edges, pt)
        SP.assert_realizes_flags(edges, pt, u, v, pu, Bu, pv, Bv)
        S, rho, dM, rk = rho_bar_of(edges, pt, u, v)
        attains = (rk == target)
        welds = (dM - rho == 6 + g)          # dim M(H/uv) = dim M(H) - rho
        L2T, basis, _T = SP.adapted_transform(pt, u, v, Bu, Bv)
        Sad = SP.to_adapted(L2T, S)
        assert dim(Sad) == rho
        A = A_prime(Sad)
        dimA = dim(A)
        g2 = q2_gram_rank(A)
        fam = ruling_family(A) if (dimA == 2 and g2 == 0) else '-'
        tML = t_cap_ML(Sad)
        assert dimA == rho - 2 + tML, ('S9 dimension identity', dimA, rho, tML)
        assert dimA == motions_with_bars(Sad), 'S7: bars vs A_prime'
        pred = predicted(delta, dimA, fam)
        # actual, at npx points of L
        actual = []
        for k in range(npx):
            for _ in range(100):
                c3, c4 = (F(rng.randint(-20, 20)) for _ in range(2))
                if (c3, c4) == (0, 0):
                    continue
                px = [c3 * basis[2][j] + c4 * basis[3][j] for j in range(4)]
                if px[3] != 0:
                    break
            w1, w2 = wedge2(px, pu), wedge2(px, pv)
            dsum = dim(span(S + [w1, w2]))
            ok_sum = (dsum == min(delta + 2, 6))
            ptG = dict(pt)
            ptG['x'] = tuple(dehom(px))
            okG, _ = verify_pencil_witness(Gedges, ptG)
            assert okG, 'H + x is not a pencil configuration'
            _S, _r, _dm, rkG = rho_bar_of(Gedges, ptG, u, v)
            attG = (rkG == targetG)
            assert ok_sum == (attG or not (attains and welds)), \
                ('rank of G vs relative-screw sum disagree', dsum, rkG, targetG)
            actual.append(attG)
        act_all = all(actual)
        agree = (pred == act_all) if (attains and welds) else None
        cad = profile(Sad, SP.B_ADAPTED)
        exc = tuple(cad[SP.bunif_key(U)] - generic_c(rho, SP.udim(U))
                    for U in SP.U_LIST)
        exc_seen[exc] = exc_seen.get(exc, 0) + 1
        summary['draws'] += 1
        summary['attain'] += attains
        summary['weld'] += welds
        summary['pred_yes'] += bool(pred)
        if agree is True:
            summary['agree'] += 1
        elif agree is False:
            summary['mismatch'] += 1
        tag = ('agree' if agree else 'MISMATCH' if agree is False
               else 'n/a (side or weld not attaining)')
        print(f'   draw {d}: rho = {rho}, delta = {delta}, attains = {attains}, '
              f'welded = {welds}; dim A\' = {dimA}, Q2-Gram = {g2}, family = {fam}, '
              f'dim(T cap <M,L>) = {tML}; S9 predicts G attains: {pred}; '
              f'actual at {npx} p_x: {actual} -> {tag}')
    print(f'   -- summary {name}: {summary["draws"]}/{ndraw} sampled'
          f'{f", {summary["fail"]} FAILED" if summary["fail"] else ""}; '
          f'attains {summary["attain"]}, welded {summary["weld"]}, '
          f'S9 predicts yes at {summary["pred_yes"]}, '
          f'predicted==actual at {summary["agree"]}, MISMATCH at {summary["mismatch"]}')
    for exc, cnt in sorted(exc_seen.items()):
        nz = [(SP.ulabel(U), e) for U, e in zip(SP.U_LIST, exc) if e]
        print(f'      excess x{cnt}: {nz if nz else "none"}')
    print(f'   [{time.time() - t0:.1f} s]')
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--side', required=True)
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, required=True)
    ap.add_argument('--px', type=int, default=3)
    a = ap.parse_args()
    names = (SP.ORDER if a.side == 'all' else SP.ORDER2 if a.side == 'all2'
             else SP.ORDER + SP.ORDER2 if a.side == 'both' else [a.side])
    for nm in names:
        if nm not in SP.SIDES:
            sys.exit(f'unknown side {nm}')
    print(f'earone: seed = {a.seed}, draws = {a.draws}, px = {a.px}, sides = {names}')
    tot = {}
    for nm in names:
        s = run(nm, a.seed, a.draws, a.px)
        for k, val in s.items():
            tot[k] = tot.get(k, 0) + val
    print(f'== TOTAL: {tot}')


if __name__ == '__main__':
    main()
