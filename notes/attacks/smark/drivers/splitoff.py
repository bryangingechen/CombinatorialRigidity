#!/usr/bin/env python3
"""
splitoff.py -- the smark attack's control for workbook S14 (session 5): the split-off
antecedent G_- = H' u ear_{m-1} attaining supplies the S10 block list for G = H' u ear_m,
and the ear alone avoids the isotropy exceptions (X1)-(X4).  Reuses sideprof.py,
earcompose.py, adversarial.py, census.py and the harness modules they import.

    timeout 1800 python3 notes/attacks/smark/drivers/splitoff.py --seed S --draws N [--sides hub|all|A,B] [--ears 2,3,4]
    timeout  900 python3 notes/attacks/smark/drivers/splitoff.py --seed S --draws N --special
    (run from the repository root; --repo PATH otherwise.  Workbook: notes/pencil/workbook/attack-smark.md S14)

Per side H' and per m in --ears, at N seeded draws of a PRESCRIBED generic flag pair
(the side, ear_{m-1} and ear_m each sampled once at the same flags):
  (1) side data: delta', rho' = dim rho_bar', attains1, welds1;
  (2) G_- = H' u ear_{m-1}: exact rank vs 6(|V|-1) - def3 -> att_minus; dim(rho' cap rho(ear_{m-1}));
  (3) G   = H' u ear_m:     att; dim(rho' cap rho(ear_m));
  (4) the S10 block list for m on the side's profile c1 -> list_ok;
  (5) the CLAIM: att_minus and delta'+m <= 6  ==>  welds1 and cap_{m-1} = 0 and list_ok;
                 att_minus and delta'+m  > 6  ==>  attains1 and dim(rho' + rho(ear_{m-1})) = 6;
  (6) exception-avoidance Gram data for B = rho_bar(ear_m) alone (m = 2, 3) and T_B = B^perp (Klein);
  (7) tallies per (side, m) and a TOTAL line.

Adapted coordinates (sideprof): x = (x0 | x1 x2 | x3 x4 | x5) = (x_M ; x_u ; x_v ; x_L) with
x0 <-> p_u ^ p_v (the line M; sideprof task block 'L'), x5 <-> the line L = pi_u cap pi_v
(sideprof task block 'ell'), (x1,x2) <-> Pi_u, (x3,x4) <-> Pi_v.  Q1 = x_M x_L,
Q2 = det[x_u | x_v], Q = Q1 - Q2 (sideprof.Q1/Q2/Qk, polarized).
The three E's of item (6) are defined by COORDINATES and labelled by them in the output:
  '<L>^perp={x_L=0}', '<M>^perp={x_M=0}', 'Pu+Pv={x_M=x_L=0}' = Pi_u + Pi_v.
NB: under the Klein form Q the two labels are swapped -- {x_L = 0} is the Klein-orthogonal
of the line M and {x_M = 0} that of the line L (S2's E = <M>^perp, <L>^perp respectively);
both coordinate hyperplanes are checked, so the (X3) verdict is unaffected.  Read the braces.

All arithmetic exact (fractions.Fraction); every rng seeded.  Reads the repo READ-ONLY.
"""
import argparse
import os
import random
import sys
import time
from fractions import Fraction as F


def bootstrap(repo):
    drv = os.path.join(repo, 'notes', 'attacks', 'smark', 'drivers')
    if not os.path.isdir(drv):
        sys.exit(f'drivers dir not found: {drv} (pass --repo)')
    sys.path.insert(0, drv)


def run_all(a):
    import sideprof as SP          # noqa: E402  (bootstraps the harness path)
    import earcompose as EC        # noqa: E402
    import adversarial as ADV      # noqa: E402
    import census as CS            # noqa: E402
    from exactcore import rank as rank_exact, nullspace   # noqa: E402
    from kbare_common import verts_of, verify_pencil_witness  # noqa: E402
    from binduc import assert_generic_star                # noqa: E402
    from bimage import span, dim, rho_bar_of, isect, pt_in  # noqa: E402
    from bdecor import d3                                 # noqa: E402
    from bunif import profile                             # noqa: E402

    E6 = [[F(1) if i == j else F(0) for j in range(6)] for i in range(6)]
    # the three E's, by coordinate definition
    E_SETS = [('<L>^perp={x_L=0}', span([E6[i] for i in (0, 1, 2, 3, 4)])),
              ('<M>^perp={x_M=0}', span([E6[i] for i in (1, 2, 3, 4, 5)])),
              ('Pu+Pv={x_M=x_L=0}', span([E6[i] for i in (1, 2, 3, 4)]))]

    def side_edges(name):
        if name in SP.SIDES:
            return SP.SIDES[name]()
        if name in ADV.SIDES:
            return ADV.SIDES[name]()
        sys.exit(f'unknown side {name}')

    def klein_perp_adapted(B):
        """B^perp under Q = Q1 - Q2 in adapted coordinates (exact nullspace)."""
        if not B:
            return [r[:] for r in E6]
        M = [[SP.Qk(b, e) for e in E6] for b in B]
        T = nullspace(M)
        T = span(T) if T else []
        assert dim(T) == 6 - dim(B), ('klein_perp dim', dim(T), dim(B))
        for b in B:
            for t in T:
                assert SP.Qk(b, t) == 0, 'klein_perp not orthogonal'
        return T

    def cap_dim(A, B):
        return dim(A) + dim(B) - dim(span(A + B))

    def compose(e1, pt1, ek, ptk, u, v):
        """H' u ear_k at shared flags: (att, rkG, targetG, d3G)."""
        G = e1 + ek
        ptG = dict(pt1)
        ptG.update({w: ptk[w] for w in ptk if w not in (u, v)})
        okG, why = verify_pencil_witness(G, ptG)
        assert okG, ('combined config not a pencil configuration', why)
        _S, _r, _dM, rkG = rho_bar_of(G, ptG, u, v)
        d3G = d3(G)
        targetG = 6 * (len(verts_of(G)) - 1) - d3G
        return rkG == targetG, rkG, targetG, d3G

    def s10_list(c1, rho1, m):
        """the S10 block list for m on the side's profile; returns (ok, details)."""
        Pu, Pv = c1[('Pu',)], c1[('Pv',)]
        PuPv = c1[('Pu', 'Pv')]
        MPu, MPv = c1[('L', 'Pu')], c1[('L', 'Pv')]        # sideprof 'L' = the line M
        PuL, PvL = c1[('Pu', 'ell')], c1[('Pv', 'ell')]    # sideprof 'ell' = the line L
        if m == 2:
            s = max(0, rho1 - 3)
            checks = [('c(Pu)', Pu, 1 + s), ('c(Pv)', Pv, 1 + s), ('c(Pu+Pv)', PuPv, 2 + s),
                      ('c(M+Pu)', MPu, 2 + s), ('c(M+Pv)', MPv, 2 + s),
                      ('c(Pu+L)', PuL, 2 + s), ('c(Pv+L)', PvL, 2 + s)]
        elif m == 3:
            s = max(0, rho1 - 2)
            checks = [('c(Pu)', Pu, 1 + s), ('c(Pv)', Pv, 1 + s)]
        else:
            checks = []
        bad = [(nm, val, bnd) for (nm, val, bnd) in checks if val > bnd]
        return (not bad), checks, bad

    # ---------------------------------------------------------------- item (6)
    def gram_block(B, label):
        """rows: (name, expected-predicate-string, got) for B and for T_B."""
        out = {}
        out['Q1'] = SP.gram_rank(SP.Q1, B)
        out['Q2'] = SP.gram_rank(SP.Q2, B)
        out['Q'] = SP.gram_rank(SP.Qk, B)
        for nm, E in E_SETS:
            I = isect(B, E) if (B and E) else []
            out[('c', nm)] = dim(I)
            out[('Q2on', nm)] = SP.gram_rank(SP.Q2, I)
        return out

    # expectations (team lead's hand computation); each is (key, text, predicate)
    def expectations(m):
        ge1 = lambda x: x >= 1  # noqa: E731
        if m == 2:
            B_exp = [('Q1', '1', lambda x: x == 1), ('Q2', '3', lambda x: x == 3),
                     ('Q', '2', lambda x: x == 2)]
            for nm, _ in E_SETS:
                B_exp += [(('c', nm), '2', lambda x: x == 2),
                          (('Q2on', nm), '2', lambda x: x == 2)]
            T_exp = [(('c', E_SETS[0][0]), '2', lambda x: x == 2),
                     (('Q2on', E_SETS[0][0]), '2', lambda x: x == 2),
                     (('c', E_SETS[1][0]), '2', lambda x: x == 2),
                     (('Q2on', E_SETS[1][0]), '>=1', ge1),
                     (('c', E_SETS[2][0]), '1', lambda x: x == 1)]
        elif m == 3:
            B_exp = [('Q2', '4', lambda x: x == 4),
                     (('c', E_SETS[0][0]), '3', lambda x: x == 3),
                     (('Q2on', E_SETS[0][0]), '>=1', ge1),
                     (('c', E_SETS[1][0]), '3', lambda x: x == 3),
                     (('Q2on', E_SETS[1][0]), '>=1', ge1),
                     (('c', E_SETS[2][0]), '2', lambda x: x == 2),
                     (('Q2on', E_SETS[2][0]), '2', lambda x: x == 2)]
            T_exp = [(('c', E_SETS[0][0]), '<=1', lambda x: x <= 1),
                     (('c', E_SETS[1][0]), '<=1', lambda x: x <= 1),
                     (('c', E_SETS[2][0]), '0', lambda x: x == 0)]
        else:
            B_exp, T_exp = [], []
        return B_exp, T_exp

    def kstr(k):
        return k if isinstance(k, str) else f'{k[0]}[{k[1]}]'

    def report_gram(m, Bad, indent='      '):
        """print item (6) for B = rho_bar(ear_m) in adapted coords; return #mismatches."""
        TB = klein_perp_adapted(Bad)
        gB, gT = gram_block(Bad, 'B'), gram_block(TB, 'T_B')
        B_exp, T_exp = expectations(m)
        mism = 0
        for tag, g, exps, sp in (('B=rho(ear_%d)' % m, gB, B_exp, Bad), ('T_B=B^perp', gT, T_exp, TB)):
            parts = []
            expd = {k: (txt, pred) for k, txt, pred in exps}
            for k in (['Q1', 'Q2', 'Q'] + [x for nm, _ in E_SETS for x in (('c', nm), ('Q2on', nm))]):
                got = g[k]
                if k in expd:
                    txt, pred = expd[k]
                    ok = pred(got)
                    mism += (not ok)
                    parts.append(f'{kstr(k)}={txt}/{got}{"" if ok else " **MISMATCH**"}')
                else:
                    parts.append(f'{kstr(k)}=-/{got}')
            print(f'{indent}(6) {tag} (dim {dim(sp)}): '
                  + '; '.join(parts))
        return mism

    # ----------------------------------------------------------------- driver
    def draw_triple(e1, eA, eB, u, v, rng, tries=60, extra=None):
        """side + ear_A + ear_B at ONE prescribed generic flag pair."""
        for _ in range(tries):
            pu, Bu, pv, Bv = SP.draw_flags(rng)
            SP.assert_generic_flags(pu, Bu, pv, Bv)
            fx_uv = {u: (pu, Bu), v: (pv, Bv)}
            fx1 = dict(fx_uv)
            if extra is not None:
                ex = extra(pu, Bu, pv, Bv, rng)
                if ex is None:
                    continue
                fx1.update(ex)
            try:
                got1 = SP.sample_side(e1, u, v, rng, fx1)
            except AssertionError:
                got1 = None
            if got1 is None:
                continue
            gotA = SP.sample_side(eA, u, v, rng, fx_uv) if eA is not None else 'none'
            gotB = SP.sample_side(eB, u, v, rng, fx_uv)
            if gotA is not None and gotB is not None:
                return (pu, Bu, pv, Bv), got1, gotA, gotB
        return None

    def run_side_m(side, m, seed, ndraw, tot):
        u, v = 'u', 'v'
        e1 = side_edges(side)
        eA, eB = EC.ear_edges(m - 1), EC.ear_edges(m)
        V1 = sorted(verts_of(e1), key=str)
        rng = random.Random(seed)
        t0 = time.time()
        f1, g1, d1, _ = SP.side_deltas(e1, u, v)
        fA, gA, dA, _ = SP.side_deltas(eA, u, v)
        fB, gB, dB, _ = SP.side_deltas(eB, u, v)
        target1 = 6 * (len(V1) - 1) - f1
        GA, GB = e1 + eA, e1 + eB
        d3A, d3B = d3(GA), d3(GB)
        assert d3A == f1 + fA - min(d1 + dA, 6), ('2-cut law G_-', d3A, f1, fA, d1, dA)
        assert d3B == f1 + fB - min(d1 + dB, 6), ('2-cut law G', d3B, f1, fB, d1, dB)
        nbs = SP.neighbors(e1)
        print(f'== side {side} (|V|={len(V1)}, side-deg=({len(nbs[u])},{len(nbs[v])}), '
              f'f={f1}, g={g1}, delta\'={d1}) ; m={m}: ear_{m-1} (delta={dA}), ear_{m} (delta={dB}); '
              f'def3(G_-)={d3A}, def3(G)={d3B} [2-cut law ok]; delta\'+m={d1 + m} '
              f'({"<= 6" if d1 + m <= 6 else "> 6"}); seed={seed}')
        if dA != m:
            print(f'   NOTE: delta(ear_{m-1}) = {dA} != m = {m}; the claim uses the literal m')
        S = dict(draws=0, att_minus=0, att=0, claim_viol=0, gram_mism=0, fails=0,
                 attains1=0, welds1=0, list_ok=0)
        for d in range(ndraw):
            got = draw_triple(e1, eA, eB, u, v, rng)
            if got is None:
                S['fails'] += 1
                print(f'   draw {d}: SAMPLER FAILED')
                continue
            (pu, Bu, pv, Bv), got1, gotA, gotB = got
            pt1, ptA, ptB = got1[0], gotA[0], gotB[0]
            assert pt1[u] == ptA[u] == ptB[u] and pt1[v] == ptA[v] == ptB[v], 'terminal mismatch'
            for e, p in ((e1, pt1), (eA, ptA), (eB, ptB)):
                ok, why = verify_pencil_witness(e, p)
                assert ok, why
            assert_generic_star(e1, pt1)
            SP.assert_realizes_flags(e1, pt1, u, v, pu, Bu, pv, Bv)
            # (1) side
            S1, rho1, dM1, rk1 = rho_bar_of(e1, pt1, u, v)
            att1 = (rk1 == target1)
            weld1 = (dM1 - rho1 == 6 + g1)
            # ears alone
            SA, rhoA, dMA, rkA = rho_bar_of(eA, ptA, u, v)
            SB, rhoB, dMB, rkB = rho_bar_of(eB, ptB, u, v)
            attA = (rkA == 6 * (len(verts_of(eA)) - 1) - fA)
            attB = (rkB == 6 * (len(verts_of(eB)) - 1) - fB)
            # (2) G_-
            att_minus, rkGA, tGA, _ = compose(e1, pt1, eA, ptA, u, v)
            capA, sumA = cap_dim(S1, SA), dim(span(S1 + SA))
            # (3) G
            att, rkGB, tGB, _ = compose(e1, pt1, eB, ptB, u, v)
            capB, sumB = cap_dim(S1, SB), dim(span(S1 + SB))
            # (4) block list
            L2T, basis, _T = SP.adapted_transform(pt1, u, v, Bu, Bv)
            Sad1 = SP.to_adapted(L2T, S1)
            assert dim(Sad1) == rho1
            cad = profile(Sad1, SP.B_ADAPTED)
            c1 = {U: cad[SP.bunif_key(U)] for U in SP.U_LIST}
            list_ok, checks, bad = s10_list(c1, rho1, m)
            # (5) the claim
            viol = []
            if att_minus and d1 + m <= 6:
                if not weld1:
                    viol.append('welds1 False')
                if capA != 0:
                    viol.append(f'dim(rho\' cap rho(ear_{m-1})) = {capA} != 0')
                if not list_ok:
                    viol.append(f'list_ok False: {bad}')
            if att_minus and d1 + m > 6:
                if not att1:
                    viol.append('attains1 False')
                if sumA != 6:
                    viol.append(f'dim(rho\' + rho(ear_{m-1})) = {sumA} != 6')
            S['draws'] += 1
            S['att_minus'] += att_minus
            S['att'] += att
            S['attains1'] += att1
            S['welds1'] += weld1
            S['list_ok'] += list_ok
            S['claim_viol'] += bool(viol)
            print(f'   draw {d}: (1) delta\'={d1} rho\'={rho1} attains1={att1} welds1={weld1} | '
                  f'ears alone: rho(ear_{m-1})={rhoA} att={attA}, rho(ear_{m})={rhoB} att={attB}')
            print(f'      (2) G_-=H\'+ear_{m-1}: rank {rkGA} vs target {tGA} -> att_minus={att_minus}; '
                  f'dim(rho\' cap rho(ear_{m-1}))={capA}, dim(sum)={sumA}')
            print(f'      (3) G  =H\'+ear_{m}: rank {rkGB} vs target {tGB} -> att={att}; '
                  f'dim(rho\' cap rho(ear_{m}))={capB}, dim(sum)={sumB}')
            print(f'      (4) S10 list m={m}: ' + (', '.join(f'{nm}={val}<={bnd}' for nm, val, bnd in checks)
                                                 if checks else 'nothing') + f' -> list_ok={list_ok}')
            branch = ('delta\'+m<=6' if d1 + m <= 6 else 'delta\'+m>6') if att_minus else 'vacuous (att_minus False)'
            print(f'      (5) CLAIM [{branch}]: ' + ('OK' if not viol else 'VIOLATION: ' + '; '.join(viol)))
            if viol:
                print(f'      **** CLAIM VIOLATION at side={side} m={m} draw={d} seed={seed}: {viol}')
            if m in (2, 3):
                SadB = SP.to_adapted(L2T, SB)
                assert dim(SadB) == rhoB
                S['gram_mism'] += report_gram(m, SadB)
            sys.stdout.flush()
        print(f'   -- {side}+m={m}: draws={S["draws"]} (fails {S["fails"]}), att_minus={S["att_minus"]}, '
              f'att={S["att"]}, attains1={S["attains1"]}, welds1={S["welds1"]}, list_ok={S["list_ok"]}, '
              f'claim_violations={S["claim_viol"]}, gram_mismatches={S["gram_mism"]}  [{time.time() - t0:.1f}s]')
        sys.stdout.flush()
        for k, val in S.items():
            tot[k] = tot.get(k, 0) + val
        return S

    # ------------------------------------------------------------ --special
    def run_special(seed, ndraw):
        skel, u, v = CS.SKEL['K4-e']
        lengths = (4, 2, 3, 4, 2)
        e1 = CS.subdiv_lengths(skel, lengths)
        V1 = sorted(verts_of(e1), key=str)
        f1, g1, d1, _ = SP.side_deltas(e1, u, v)
        target1 = 6 * (len(V1) - 1) - f1
        eA, eB = EC.ear_edges(1), EC.ear_edges(2)
        fA, gA, dA, _ = SP.side_deltas(eA, u, v)
        fB, gB, dB, _ = SP.side_deltas(eB, u, v)
        print(f'== SPECIAL: K4-e {lengths} |V|={len(V1)} f={f1} g={g1} delta\'={d1} '
              f'dist={CS.dist(e1, u, v)} girth={CS.girth(e1)}; family (i) pi_p = pi_q = pi_u; '
              f'ear_1 (delta={dA}), ear_2 (delta={dB}); seed={seed}, draws={ndraw}')
        print(f'   expected: attains1 False, welds1 True, rho\'=4, att(H\'+ear_1) True (cap 0), att(H\'+ear_2) False')
        rng = random.Random(seed)

        def fam_i(pu, Bu, pv, Bv, rng):
            return {'p': (pt_in(Bu, rng, 20), Bu), 'q': (pt_in(Bu, rng, 20), Bu)}

        print(f'   {"draw":>4s} {"delta\'":>6s} {"rho\'":>4s} {"attains1":>8s} {"welds1":>6s} '
              f'{"att(+ear1)":>10s} {"att(+ear2)":>10s} {"cap1":>4s} {"cap2":>4s} {"sum1":>4s} {"sum2":>4s} '
              f'{"c(Pu)":>5s} {"realizes":>8s}')
        rows = 0
        for d in range(ndraw):
            got = draw_triple(e1, eA, eB, u, v, rng, tries=200, extra=fam_i)
            if got is None:
                print(f'   draw {d}: SAMPLER FAILED')
                continue
            (pu, Bu, pv, Bv), got1, gotA, gotB = got
            pt1, ptA, ptB = got1[0], gotA[0], gotB[0]
            for e, p in ((e1, pt1), (eA, ptA), (eB, ptB)):
                ok, why = verify_pencil_witness(e, p)
                assert ok, why
            realizes = True
            try:
                SP.assert_realizes_flags(e1, pt1, u, v, pu, Bu, pv, Bv)
            except AssertionError as ex:
                realizes = f'NO ({ex})'
            S1, rho1, dM1, rk1 = rho_bar_of(e1, pt1, u, v)
            att1 = (rk1 == target1)
            weld1 = (dM1 - rho1 == 6 + g1)
            SA = rho_bar_of(eA, ptA, u, v)[0]
            SB = rho_bar_of(eB, ptB, u, v)[0]
            attA, rkA, tA, _ = compose(e1, pt1, eA, ptA, u, v)
            attB, rkB, tB, _ = compose(e1, pt1, eB, ptB, u, v)
            capA, sumA = cap_dim(S1, SA), dim(span(S1 + SA))
            capB, sumB = cap_dim(S1, SB), dim(span(S1 + SB))
            L2T, _b, _T = SP.adapted_transform(pt1, u, v, Bu, Bv)
            cad = profile(SP.to_adapted(L2T, S1), SP.B_ADAPTED)
            cPu = cad[SP.bunif_key(('Pu',))]
            print(f'   {d:4d} {d1:6d} {rho1:4d} {str(att1):>8s} {str(weld1):>6s} '
                  f'{str(attA):>10s} {str(attB):>10s} {capA:4d} {capB:4d} {sumA:4d} {sumB:4d} {cPu:5d} {str(realizes):>8s}'
                  f'   [ranks: side {rk1}/{target1}; +ear1 {rkA}/{tA}; +ear2 {rkB}/{tB}]')
            rows += 1
            sys.stdout.flush()
        print(f'TOTAL-SPECIAL: draws={rows}')

    # ------------------------------------------------------------------ main
    t0 = time.time()
    if a.special:
        run_special(a.seed, a.draws)
        print(f'[{time.time() - t0:.1f}s]')
        return
    ears = [int(x) for x in a.ears.split(',')]
    if a.sides == 'hub':
        sides = list(EC.HUB_SIDES) + ['sk4_d2', 'sk4_d3', 'sk4_d4', 'prism']
    elif a.sides == 'all':
        sides = list(SP.ORDER) + list(SP.ORDER2) + list(ADV.SIDES)
    else:
        sides = a.sides.split(',')
    print(f'splitoff: seed={a.seed}, draws={a.draws}, ears={ears}, sides={sides}')
    print('adapted coords: (x0 | x1 x2 | x3 x4 | x5) = (x_M ; x_u ; x_v ; x_L); Q1 = x_M x_L, '
          'Q2 = det[x_u|x_v], Q = Q1 - Q2')
    tot = {}
    table = []
    for side in sides:
        for m in ears:
            if m < 2:
                sys.exit('m must be >= 2 (ear_{m-1} needs m-1 >= 1)')
            S = run_side_m(side, m, a.seed, a.draws, tot)
            table.append((side, m, S))
    print('== per-(side, m) tallies: side m draws att_minus att attains1 welds1 list_ok claim_viol gram_mism')
    for side, m, S in table:
        print(f'   {side:10s} {m} {S["draws"]:2d} {S["att_minus"]:2d} {S["att"]:2d} {S["attains1"]:2d} '
              f'{S["welds1"]:2d} {S["list_ok"]:2d} {S["claim_viol"]:2d} {S["gram_mism"]:2d}')
    print(f'TOTAL: draws={tot.get("draws", 0)}, claim_violations={tot.get("claim_viol", 0)}, '
          f'gram_mismatches={tot.get("gram_mism", 0)}  '
          f'(att_minus={tot.get("att_minus", 0)}, att={tot.get("att", 0)}, sampler_fails={tot.get("fails", 0)})'
          f'  [{time.time() - t0:.1f}s]')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, required=True)
    ap.add_argument('--draws', type=int, required=True)
    ap.add_argument('--sides', default='hub')
    ap.add_argument('--ears', default='2,3,4')
    ap.add_argument('--special', action='store_true')
    ap.add_argument('--repo', default=os.getcwd())
    args = ap.parse_args()
    bootstrap(args.repo)
    run_all(args)
