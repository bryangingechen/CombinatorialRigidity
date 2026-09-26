#!/usr/bin/env python3
"""
orbitlink.py -- the refined 2-ear link and the `k = 2` open-ear cell without the orbit
count (workbook §(K-main) Step MC13, *The `k = 2` cell without the orbit count*,
(MC-173)-(MC-176); the Phase-40 ORBIT recon, 2026-09-26).

Setting and notation are Step MC10's and Step MC13's.  An open ear `a - x1 - x2 - b` on `G'`
gives `G = G' + ear_2`; `G1 := G' + (a - x - b)` is `G` with `x2` split off (the antecedent).
At a point of X0(G'), `rho = {X_b - X_a : X in M_{G'}}`; `y` is a point of `m = pi_a cap pi_b`;
`Lambda_1(y) = span(p_a ^ y, y ^ p_b)`; `s := dim(rho + Lambda_1(y))`; `Lambda_2(x)` is the span of
the three hinge lines of a 2-ear placement `x = (x1, x2)`, `x1 in pi_a`, `x2 in pi_b`.

What each mode asserts (an assert firing is a counterexample to a workbook claim, or a bug):

  --link [--trials N]   (MC-173), on random orbit-(i) and orbit-(ii) frames.
      Orbit (i): the four limit directions of the proof's four curves, together with
      Lambda_1(y), span Lambda^2 K^4 (rank 6, exact, at every frame); for an adversarial
      `rho` (random `r` in 1..4, drawn inside a random subspace `W` that contains
      Lambda_1(y) and is spanned half the time by limit directions), when `s <= 5` some one
      of the four limit directions lies outside `rho + Lambda_1(y)`, and the proof's curve
      reaches `dim(rho + Lambda_2(x(t))) >= min(s + 1, 6)` at an exhibited `t` in a fixed
      list, with `lambda_2 = 3` there.  That exhibited placement is a certificate (rank is
      lower semicontinuous, so the generic value is at least the exhibited one).  Also, at
      three random placements, the best is `>= min(s + 1, 6)` (a consistency check).
      Orbit (ii): the limit directions of BOTH curve families, over all `u in pi_a-hat`,
      `w in pi_b-hat`, `sigma`, span only a 5-space with Lambda_1(y) (asserted, exact):
      this is why the proof is orbit-(i)-only.  The random-draw figure is PRINTED, not
      asserted: (MC-173) claims nothing in orbit (ii), and a single draw is a lower bound
      for the generic value, never a measurement of it.
  --witness             (B)'s witness: `K4` with every edge subdivided twice is in the class
      S of Step MC16, has def2 = 9 > def3 = 0, is rigid, has no (MC-80) core, and every one
      of its six chains has `k = 2`, `a !~ b`, `delta = delta2 = 3`.  So in (MC-89)'s step
      list its only covering step is the `k = 2`, `a !~ b`, `delta2 >= 2` cell.
  --e2e [--limit N]     (MC-176) end to end, exact, at the witness's six chains and at the
      first N further qualifying chains (`k = 2`, `a !~ b`, `delta >= 1`, `delta2 >= 2`, one
      chain per graph) of the subdivisions of `K4` with lengths in {1,2,3}, in
      `itertools.product` order.  At each: an attaining point of X0(G') over a picture
      certified main (`dim L(q) = 3 + def2`); `y` on `m` (its picture on the zero line of
      `h_a - h_b`); G1 attains there over a certified-main picture; the flag pair is in orbit
      (i); `s = 2 + min(delta, 4)`; the rank identity of (MC-16) at G1; the eight chart
      limit directions span Lambda^2 with Lambda_1(y); the first one outside
      `rho + Lambda_1(y)` gives a curve point where G attains, with (MC-16)'s identity; and a
      random generic placement over a certified-main picture of G where
      `dim(rho + Lambda_2) >= min(s + 1, 6)` and G attains.

Sampler support.  --link: frames are random invertible integer matrices (entries in -9..9,
rank 4 asserted), `y`, `y'` random in m-hat (independence asserted); `rho` as above.  It varies
the frame, `y`, `r` and `rho`; `K` is Q.  --e2e: pictures from `maincomp.sample_q` (range 30),
heights uniform in L(q) (earante.draw_point), `y`'s picture uniform in -30..30 on the zero line,
placements uniform in -30..30; it varies the graph (subdivided K4 only), the chain, the
picture and the heights.  Population caps: --trials (default 1500 per orbit), --limit
(default 24).  Exact Q throughout; seeds are printed.

Commands (repository root):
  PYTHONHASHSEED=0 python3 notes/scripts/w4/orbitlink.py --link
  PYTHONHASHSEED=0 python3 notes/scripts/w4/orbitlink.py --witness
  PYTHONHASHSEED=0 python3 notes/scripts/w4/orbitlink.py --e2e
"""
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank as rank_exact, wedge2  # noqa: E402
from kbare_common import build_rigidity  # noqa: E402
from maincomp import lifting_space, _interp, def_k  # noqa: E402
import earante as E  # noqa: E402
import coverstruct as C  # noqa: E402

SEED = 20260926
SIGMA0 = F(1, 3)
TLIST = [F(1, 7), F(1, 11), F(2, 13), F(1, 3), F(3, 17), F(5, 19)]
K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def dim(vs):
    return E.dim(vs)


def comb(*terms):
    out = [F(0)] * len(terms[0][1])
    for c, v in terms:
        out = [a + c * b for a, b in zip(out, v)]
    return out


def rint(rng, S=9):
    return F(rng.randint(-S, S))


def rand_in(rng, span):
    return comb(*[(rint(rng), v) for v in span])


def lam2(pa, pb, x1, x2):
    return [wedge2(pa, x1), wedge2(x1, x2), wedge2(x2, pb)]


# ---------------------------------------------------------------- --link

def frame(rng, orbit):
    while True:
        e = [[rint(rng) for _ in range(4)] for _ in range(4)]
        if dim(e) == 4:
            break
    pa, pb = e[0], e[3]
    if orbit == 1:
        pia, pib, m = [e[0], e[1], e[2]], [e[1], e[2], e[3]], [e[1], e[2]]
    else:                                   # orbit (ii): p_b in pi_a
        pia, pib, m = [e[0], e[2], e[3]], [e[1], e[2], e[3]], [e[2], e[3]]
    return pa, pb, pia, pib, m


def four_curves(pa, pb, y, y2):
    """The proof's four curves: (family, u or w, sigma).  alpha: x1 = y + t u,
    x2 = (1 - sigma) y + sigma p_b; beta: x1 = (1 - sigma) y + sigma p_a, x2 = y + t w."""
    return [('alpha', y2, F(0)), ('alpha', pa, SIGMA0), ('alpha', y2, SIGMA0),
            ('beta', y2, SIGMA0)]


def curve_limit_dir(pa, pb, y, fam, v, sig):
    if fam == 'alpha':
        return wedge2(v, comb((1 - sig, y), (sig, pb)))
    return wedge2(comb((1 - sig, y), (sig, pa)), v)


def curve_point(pa, pb, y, fam, v, sig, t):
    if fam == 'alpha':
        return comb((F(1), y), (t, v)), comb((1 - sig, y), (sig, pb))
    return comb((1 - sig, y), (sig, pa)), comb((F(1), y), (t, v))


def all_family_dirs(pa, pb, pia, pib, y):
    out = []
    for sig in (F(0), SIGMA0):
        out += [curve_limit_dir(pa, pb, y, 'alpha', u, sig) for u in pia]
        out += [curve_limit_dir(pa, pb, y, 'beta', w, sig) for w in pib]
    return out


def run_link(trials):
    print(f'--link: seed {SEED}, {trials} trials per orbit, sigma0 = {SIGMA0}')
    for orbit in (1, 2):
        rng = random.Random(f'{SEED}:link:{orbit}')
        hist = {}
        shortfall_draws = 0
        n = 0
        while n < trials:
            pa, pb, pia, pib, m = frame(rng, orbit)
            y = rand_in(rng, m)
            y2 = rand_in(rng, m)
            if dim([y, y2]) < 2:
                continue
            if orbit == 2 and dim([y, pb]) < 2:
                continue
            L1 = [wedge2(pa, y), wedge2(y, pb)]
            assert dim(L1) == 2, 'lambda_1 = 2 at y in m (MC-169)'
            fam_span = dim(L1 + all_family_dirs(pa, pb, pia, pib, y))
            if orbit == 1:
                curves = four_curves(pa, pb, y, y2)
                dirs = [curve_limit_dir(pa, pb, y, *c) for c in curves]
                assert dim(L1 + dirs) == 6, '(MC-173): the four limit directions span'
                assert fam_span == 6
            else:
                assert fam_span == 5, 'orbit (ii): the two families span a 5-space'
            r = rng.choice([1, 2, 3, 4])
            wdim = rng.choice([3, 4, 5, 6])
            if rng.random() < 0.5:
                Wb = L1 + [[rint(rng) for _ in range(6)] for _ in range(wdim - 2)]
            else:
                Wb = L1 + [rand_in(rng, all_family_dirs(pa, pb, pia, pib, y))
                           for _ in range(wdim - 2)]
            rho = [rand_in(rng, Wb) for _ in range(r)]
            if dim(rho) == 0:
                continue
            s = dim(rho + L1)
            want = min(s + 1, 6)
            n += 1
            if orbit == 1:
                Wsp = rho + L1
                pick = None
                for c, d in zip(curves, dirs):
                    if s == 6 or dim(Wsp + [d]) > s:
                        pick = c
                        break
                assert pick is not None, '(MC-173): a limit direction outside rho + L1'
                ok = False
                for t in TLIST:
                    x1, x2 = curve_point(pa, pb, y, *pick, t)
                    L2 = lam2(pa, pb, x1, x2)
                    if dim(L2) == 3 and dim(rho + L2) >= want:
                        ok = True
                        break
                assert ok, ('(MC-173): the curve reaches the bound at no listed t', s)
            best = 0
            for _ in range(3):
                x1, x2 = rand_in(rng, pia), rand_in(rng, pib)
                L2 = lam2(pa, pb, x1, x2)
                if dim(L2) == 3:
                    best = max(best, dim(rho + L2))
            if orbit == 1:
                assert best >= want, ('orbit (i): no random placement reaches the bound', s)
            elif best < want:
                shortfall_draws += 1
            key = (s, best >= want)
            hist[key] = hist.get(key, 0) + 1
        name = '(i)' if orbit == 1 else '(ii)'
        print(f'  orbit {name}: {n} trials; (s, best-of-3 random draws >= min(s+1,6)) histogram:')
        for k in sorted(hist):
            print(f'     s={k[0]}  reached={k[1]}: {hist[k]}')
        if orbit == 1:
            print('  orbit (i): four-curve span 6 at every frame; the proof curve certifies '
                  'the bound at every trial; ALL OK')
        else:
            print(f'  orbit (ii): family span 5 at every frame (asserted); {shortfall_draws} '
                  'trials whose best of 3 random draws fell short (a lower bound, not a '
                  'measurement; not claimed)')


# ---------------------------------------------------------------- --witness

def witness_graph():
    return C.subdivide(K4, (2, 2, 2, 2, 2, 2))


def run_witness():
    Eg, Vg = witness_graph()
    assert C.in_class_S(Eg, Vg), 'witness in class S'
    D2, D3 = C.d2(Eg, Vg), C.d3(Eg, Vg)
    assert (D2, D3) == (9, 0), (D2, D3)
    kind, cores = C.theorem_s_cores(Eg, Vg)
    assert kind == 'rigid' and cores == [], (kind, cores)
    chs = C.chains(Eg)
    assert len(chs) == 6
    for (a, b, I) in chs:
        cd = C.chain_data(Eg, Vg, a, b, I)
        assert cd['k'] == 2 and not cd['adj'], cd
        assert cd['delta'] == 3 and cd['delta2'] == 3, cd
    print(f'--witness: K4 subdivided (2,2,2,2,2,2): n={len(Vg)} m={len(Eg)}, class S, '
          f'def2={D2} > def3={D3}, rigid, (MC-80) cores: none; 6 chains, each k=2, a !~ b, '
          'delta = delta2 = 3.  Only covering step in (MC-89): the k=2, a !~ b, delta2 >= 2 '
          'cell.  OK')


# ---------------------------------------------------------------- --e2e

def rankG(edges, pt):
    return rank_exact(build_rigidity(edges, pt)[0])


def target(edges):
    V = {v for e in edges for v in e}
    return 6 * (len(V) - 1) - def_k(edges, 6)


def main_cert(edges, q):
    V = E.verts_of(edges)
    return len(lifting_space(edges, V, q)) == 3 + def_k(edges, 3)


def e2e_instance(Eg, a, b, I, seed):
    rng = random.Random(seed)
    x1, x2 = I
    Ep = [e for e in Eg if x1 not in e and x2 not in e]
    for _attempt in range(20):
        P = E.draw_point(Ep, rng, 50)
        assert P is not None
        if P['jj']:
            break
    assert P['jj'], 'no draw over a certified-main picture of G\''
    q, z, pt, V = P['q'], P['z'], P['pt'], P['V']
    rG1p = rankG(Ep, pt)
    assert rG1p == target(Ep), 'G\' attains'
    h = _interp(Ep, V, q, z)
    ia, ib = V.index(a), V.index(b)
    orb = E.orbit_of(h[a], h[b], q[a], z[ia], q[b], z[ib])
    assert orb == 'i', ('flag pair not in orbit (i)', orb)
    D = [h[a][i] - h[b][i] for i in range(3)]
    xv = 1000
    for _ in range(200):
        if D[0] != 0:
            Y = rint(rng, 30)
            X = -(D[1] * Y + D[2]) / D[0]
        else:
            X = rint(rng, 30)
            Y = -(D[0] * X + D[2]) / D[1]
        q1 = dict(q)
        q1[xv] = (X, Y)
        E1 = Ep + [(a, xv), (xv, b)]
        if (X, Y) not in (q[a], q[b]) and main_cert(E1, q1):
            break
    else:
        raise AssertionError('no certified-main picture of G1 on the zero line')
    zx = E.ev(h[a], (X, Y))
    assert zx == E.ev(h[b], (X, Y))
    pt1 = dict(pt)
    pt1[xv] = (X, Y, zx)
    rG1 = rankG(E1, pt1)
    assert rG1 == target(E1), 'G1 attains at the incidence point'
    M = E.motion_basis(Ep, pt)
    rho = E.rel_space(M, V, a, b)
    pa, pb = E.hom(q[a], z[ia]), E.hom(q[b], z[ib])
    y = [X, Y, zx, F(1)]
    L1 = [wedge2(pa, y), wedge2(y, pb)]
    s = dim(rho + L1)
    f = def_k(Ep, 6)
    g = def_k(C.merge_pair(Ep, a, b), 6, [v for v in V if v != b])
    delta = f - g
    assert s == 2 + min(delta, 4), ('s', s, delta)
    assert rG1 == rG1p + 4 + s, '(MC-16) at G1, rank form'

    def pt_a(qq):
        return [qq[0], qq[1], E.ev(h[a], qq), F(1)]

    def pt_b(qq):
        return [qq[0], qq[1], E.ev(h[b], qq), F(1)]

    cands = []
    for dq in [(F(1), F(0)), (F(0), F(1))]:
        for sig in (F(0), SIGMA0):
            q2 = ((1 - sig) * X + sig * q[b][0], (1 - sig) * Y + sig * q[b][1])
            da = [dq[0], dq[1], E.ev(h[a], dq) - h[a][2], F(0)]
            cands.append(('alpha', dq, q2, wedge2(da, pt_b(q2))))
            q1_ = ((1 - sig) * X + sig * q[a][0], (1 - sig) * Y + sig * q[a][1])
            db = [dq[0], dq[1], E.ev(h[b], dq) - h[b][2], F(0)]
            cands.append(('beta', dq, q1_, wedge2(pt_a(q1_), db)))
    assert dim(L1 + [c[3] for c in cands]) == 6, 'chart limit directions span'
    W = rho + L1
    pick = next((c for c in cands if s == 6 or dim(W + [c[3]]) > s), None)
    assert pick is not None
    want = min(s + 1, 6)
    EG = Ep + [(a, x1), (x1, x2), (x2, b)]
    tgtG = target(EG)
    fam, dq, qfix, _c = pick
    curve_ok = False
    for t in TLIST:
        if fam == 'alpha':
            qx1, qx2 = (X + t * dq[0], Y + t * dq[1]), qfix
        else:
            qx1, qx2 = qfix, (X + t * dq[0], Y + t * dq[1])
        ptG = dict(pt)
        ptG[x1] = (qx1[0], qx1[1], E.ev(h[a], qx1))
        ptG[x2] = (qx2[0], qx2[1], E.ev(h[b], qx2))
        L2 = [wedge2(pa, pt_a(qx1)), wedge2(pt_a(qx1), pt_b(qx2)), wedge2(pt_b(qx2), pb)]
        s2 = dim(rho + L2)
        if s2 >= want:
            rG = rankG(EG, ptG)
            assert rG == rG1p + 9 + s2, '(MC-16) at G, curve point'
            assert rG == tgtG, 'G attains at the curve point'
            curve_ok = True
            break
    assert curve_ok, 'the curve reaches the bound at no listed t'
    gen_ok = False
    for _ in range(20):
        qx1 = (rint(rng, 30), rint(rng, 30))
        qx2 = (rint(rng, 30), rint(rng, 30))
        qG = dict(q)
        qG[x1], qG[x2] = qx1, qx2
        if len({qx1, qx2, q[a], q[b]}) < 4 or not main_cert(EG, qG):
            continue
        ptG = dict(pt)
        ptG[x1] = (qx1[0], qx1[1], E.ev(h[a], qx1))
        ptG[x2] = (qx2[0], qx2[1], E.ev(h[b], qx2))
        L2 = [wedge2(pa, pt_a(qx1)), wedge2(pt_a(qx1), pt_b(qx2)), wedge2(pt_b(qx2), pb)]
        s2 = dim(rho + L2)
        if s2 < want:
            continue
        rG = rankG(EG, ptG)
        assert rG == rG1p + 9 + s2, '(MC-16) at G, generic placement'
        assert rG == tgtG, 'G attains at a generic placement'
        gen_ok = True
        break
    assert gen_ok, 'no certified-main generic placement reached the bound in 20 draws'
    return dict(delta=delta, r=dim(rho), s=s, fam=fam)


def run_e2e(limit):
    print(f'--e2e: seed {SEED}; the witness\'s 6 chains, then up to {limit} further '
          'qualifying chains of subdivided K4 (lengths in {1,2,3}, itertools order)')
    Eg, Vg = witness_graph()
    rows = []
    for idx, (a, b, I) in enumerate(C.chains(Eg)):
        rows.append((('witness', idx), e2e_instance(Eg, a, b, I, f'{SEED}:e2e:w:{idx}')))
    extra = 0
    for s in itertools.product([1, 2, 3], repeat=6):
        if extra >= limit:
            break
        if 2 not in s or s == (2, 2, 2, 2, 2, 2):
            continue
        Eg, Vg = C.subdivide(K4, s)
        if not C.in_class_S(Eg, Vg):
            continue
        for idx, (a, b, I) in enumerate(C.chains(Eg)):
            cd = C.chain_data(Eg, Vg, a, b, I)
            if cd['k'] == 2 and not cd['adj'] and cd['delta'] >= 1 and cd['delta2'] >= 2:
                rows.append(((s, idx), e2e_instance(Eg, a, b, I, f'{SEED}:e2e:{s}:{idx}')))
                extra += 1
                break
    hist = {}
    for _name, rec in rows:
        key = (rec['delta'], rec['r'], rec['s'])
        hist[key] = hist.get(key, 0) + 1
    for k in sorted(hist):
        print(f'   (delta, r, s) = {k}: {hist[k]} instances')
    print(f'  {len(rows)} instances ({len(rows) - extra} witness chains, {extra} further): '
          'every assert held -- orbit (i), G\', G1 and G attain over certified-main pictures, '
          's = 2 + min(delta, 4), (MC-16) at G1 and G.  ALL OK')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--link', action='store_true')
    ap.add_argument('--trials', type=int, default=1500)
    ap.add_argument('--witness', action='store_true')
    ap.add_argument('--e2e', action='store_true')
    ap.add_argument('--limit', type=int, default=24)
    args = ap.parse_args()
    if not (args.link or args.witness or args.e2e):
        ap.error('choose --link, --witness and/or --e2e')
    if args.link:
        run_link(args.trials)
    if args.witness:
        run_witness()
    if args.e2e:
        run_e2e(args.limit)


if __name__ == '__main__':
    main()
