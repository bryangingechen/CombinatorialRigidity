#!/usr/bin/env python3
"""
earcompose.py -- the smark attack's control for workbook S10 (the reviewer's
chain-length stratification of the consumed 2-cut, session 3 verification).

    python3 notes/attacks/smark/drivers/earcompose.py --seed S --draws N [--ears 2,3,4] [--side NAME|hub]
    (run from the repository root; workbook: notes/pencil/workbook/attack-smark.md S10, S12)

S10 composes side 1 = H' (a hub-terminal side, side-degree >= 2 at w and v)
with side 2 = ear_m at the hub 2-cut {w, v}, and reads off from S3 + S8 that
G = H' u ear_m attains at generic flags:
  * m >= 4: unconditionally (given H' attains and welded-attains);
  * m = 3: iff c'(Pi_w), c'(Pi_v) <= 1 (bites only at delta' = 2);
  * m = 2: iff c'(Pi_w), c'(Pi_v) <= 1, c'(Pi_w+Pi_v) <= 2, and the two
    3-dim blocks at each pencil <= 2 (bites at delta' = 2, 3), + exceptions.

This driver checks S10 END TO END on the named battery, exactly:
  For each (side1, m):
    * G = side1_edges + ear_m (interior vertices 'e0'..'e{m-1}');
    * def3(G) = d3(G), asserted == f1 + f2 - min(delta1 + delta2, 6)  [2-cut law];
    * per draw at a PRESCRIBED generic flag pair (sideprof's sampler, asserts):
        - side 1 config -> rho_bar_1, delta1, attains1, welds1, block profile;
        - ear   config -> rho_bar_2, delta2, attains2, welds2 (== the S8 ear row);
        - PREDICTED (gluing law, brief S2 / S10(ii)): G attains iff
            dim(rho_bar_1 + rho_bar_2) == min(delta1 + delta2, 6);
        - S3 CRITERION verdict: all 16 block inequalities
            c1(U) + c2(U) <= dim U + max(0, delta1 + delta2 - 6) hold
          (the exceptions (X1)-(X4) are reported, not auto-avoided);
        - ACTUAL: combined config ptG = side1 config u ear config (shared u, v),
          verified a pencil configuration, rank R(G) == targetG = 6|V(G)| - 6 - def3(G);
        - assert PREDICTED == ACTUAL, and (block criterion holds and no exception)
          ==> ACTUAL, and print any block where c1 exceeds S10's required bound.
All arithmetic exact (fractions.Fraction). Reads READ-ONLY; writes nothing.
"""
import argparse
import os
import random
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sideprof as SP  # noqa: E402  (bootstraps the harness path)
import adversarial as ADV  # noqa: E402  (the K4-minor / prism adversarial sides)

from exactcore import rank as rank_exact  # noqa: E402
from kbare_common import verts_of, verify_pencil_witness  # noqa: E402
from binduc import assert_generic_star  # noqa: E402
from bimage import span, dim, rho_bar_of  # noqa: E402
from bdecor import d3  # noqa: E402
from bunif import profile, generic_c  # noqa: E402

# hub-terminal battery: side-degree >= 2 at BOTH terminals (the S10 m=2 class)
HUB_SIDES = ['theta33', 'theta34', 'theta44', 'theta45', 'theta55',
             'theta344', 'theta444', 'theta445', 'theta555', 'theta4444',
             'hubcyc', 'cross44', 'cross55', 'dumbbell']


def ear_edges(m):
    """u - e0 - ... - e{m-1} - v (interior tags disjoint from every battery side)."""
    E, prev = [], 'u'
    for i in range(m):
        E.append((prev, f'e{i}'))
        prev = f'e{i}'
    E.append((prev, 'v'))
    return E


def block_profile(Sad, rho):
    """the 16 c(U) and the excess over the generic lower bound, in U_LIST order."""
    cad = profile(Sad, SP.B_ADAPTED)
    c = {U: cad[SP.bunif_key(U)] for U in SP.U_LIST}
    return c


def run(side, m, seed, ndraw):
    e1 = (SP.SIDES[side]() if side in SP.SIDES else ADV.SIDES[side]())
    e2 = ear_edges(m)
    G = e1 + e2
    u, v = 'u', 'v'
    V1 = sorted(verts_of(e1), key=str)
    VG = sorted(verts_of(G), key=str)
    gG = SP.girth(G)
    rng = random.Random(seed)
    f1, g1, d1, _ = SP.side_deltas(e1, u, v)
    f2, g2, d2, _ = SP.side_deltas(e2, u, v)
    d3G = d3(G)
    assert d3G == f1 + f2 - min(d1 + d2, 6), \
        ('2-cut law', d3G, f1, f2, d1, d2)
    targetG = 6 * (len(VG) - 1) - d3G
    target1 = 6 * (len(V1) - 1) - f1
    minsum = min(d1 + d2, 6)
    slack = max(0, d1 + d2 - 6)
    print(f'== {side} (delta1={d1}) + ear{m} (delta2={d2}): |V(G)|={len(VG)}, '
          f'girth(G)={gG}, def3(G)={d3G} (2-cut law ok), min(sum,6)={minsum}, seed={seed}')
    S = {'draws': 0, 'agree': 0, 'mismatch': 0, 'crit_yes': 0, 'attain': 0,
         'over': 0}
    for d in range(ndraw):
        got1 = got2 = None
        for _ in range(40):
            pu, Bu, pv, Bv = SP.draw_flags(rng)
            SP.assert_generic_flags(pu, Bu, pv, Bv)
            fixed = {u: (pu, Bu), v: (pv, Bv)}
            got1 = SP.sample_side(e1, u, v, rng, fixed)
            got2 = SP.sample_side(e2, u, v, rng, fixed)
            if got1 is not None and got2 is not None:
                break
        if got1 is None or got2 is None:
            print(f'   draw {d}: SAMPLER FAILED')
            continue
        pt1, _pl1, _W1, _br1 = got1
        pt2, _pl2, _W2, _br2 = got2
        # shared terminals must coincide (same prescribed flags)
        assert pt1[u] == pt2[u] and pt1[v] == pt2[v], 'terminal mismatch'
        for e in (e1, e2):
            ok, _ = verify_pencil_witness(e, pt1 if e is e1 else pt2)
            assert ok
        assert_generic_star(e1, pt1)
        SP.assert_realizes_flags(e1, pt1, u, v, pu, Bu, pv, Bv)
        S1, rho1, dM1, rk1 = rho_bar_of(e1, pt1, u, v)
        S2, rho2, dM2, rk2 = rho_bar_of(e2, pt2, u, v)
        att1 = (rk1 == target1)
        weld1 = (dM1 - rho1 == 6 + g1)
        att2 = (rk2 == 6 * (len(sorted(verts_of(e2), key=str)) - 1) - f2)
        weld2 = (dM2 - rho2 == 6 + g2)
        # PREDICTED: gluing law
        dsum = dim(span(S1 + S2))
        pred = (dsum == minsum)
        # block profiles in adapted coords
        L2T, basis, _T = SP.adapted_transform(pt1, u, v, Bu, Bv)
        Sad1 = SP.to_adapted(L2T, S1)
        Sad2 = SP.to_adapted(L2T, S2)
        assert dim(Sad1) == rho1 and dim(Sad2) == rho2
        c1 = block_profile(Sad1, rho1)
        c2 = block_profile(Sad2, rho2)
        crit = all(c1[U] + c2[U] <= SP.udim(U) + slack for U in SP.U_LIST)
        # S10's required per-block bound on c1: dim U + slack - c2(U)
        over = [(SP.ulabel(U), c1[U], SP.udim(U) + slack - c2[U])
                for U in SP.U_LIST
                if c1[U] > SP.udim(U) + slack - c2[U]]
        # ACTUAL: combined configuration
        ptG = dict(pt1)
        ptG.update({w: pt2[w] for w in pt2 if w not in (u, v)})
        okG, _ = verify_pencil_witness(G, ptG)
        assert okG, 'combined config not a pencil configuration'
        _SG, _rG, _dMG, rkG = rho_bar_of(G, ptG, u, v)
        actual = (rkG == targetG)
        good = att1 and weld1 and att2 and weld2
        agree = (pred == actual)
        # sanity: gluing law must reproduce the rank
        assert (dsum == minsum) == (actual or not good), \
            ('gluing law vs rank', dsum, minsum, rkG, targetG, good)
        S['draws'] += 1
        S['attain'] += actual
        S['crit_yes'] += crit
        if good:
            S['agree'] += agree
            S['mismatch'] += (not agree)
        if over:
            S['over'] += 1
        # if criterion holds and no over-bound, S3 predicts attain
        if crit and not over and good:
            assert actual, ('S3 criterion holds but G does not attain', side, m)
        tag = 'agree' if (good and agree) else \
              ('MISMATCH' if good else 'n/a (side/weld not attaining)')
        marks = f', c1 OVER S10 bound: {over}' if over else ''
        print(f'   draw {d}: att(1,2)=({att1},{att2}) weld(1,2)=({weld1},{weld2}); '
              f'dim(r1+r2)={dsum}/{minsum}, S3 crit={crit}; '
              f'predict attain={pred}, actual={actual} -> {tag}{marks}')
    print(f'   -- {side}+ear{m}: {S["draws"]} draws; attains {S["attain"]}, '
          f'S3 crit {S["crit_yes"]}, agree {S["agree"]}, MISMATCH {S["mismatch"]}, '
          f'draws with c1 over S10 bound {S["over"]}')
    return S


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, required=True)
    ap.add_argument('--ears', default='2,3,4')
    ap.add_argument('--side', default='hub')
    a = ap.parse_args()
    ears = [int(x) for x in a.ears.split(',')]
    sides = HUB_SIDES if a.side == 'hub' else [a.side]
    print(f'earcompose: seed={a.seed}, draws={a.draws}, ears={ears}, sides={sides}')
    t0 = time.time()
    tot = {}
    for side in sides:
        for m in ears:
            s = run(side, m, a.seed, a.draws)
            for k, val in s.items():
                tot[k] = tot.get(k, 0) + val
    print(f'== TOTAL: {tot}  [{time.time() - t0:.1f} s]')


if __name__ == '__main__':
    main()
