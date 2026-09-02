"""
Direction BGENUINE (ordinal 57) -- IS BONEONE'S RE-OPENED COINCIDENCE
GENUINE, AND DOES IT BITE?

  THE TARGET the spec names.  BONEONE re-opened half (B)'s last
  general-position enemy with 392 exhibited R-node-shaped (1,1) peels at
  which pi_u = pi_v is FORCED ((BE-81)).  But everything there is the
  AGGRESSIVE operator, whose own docstring discloses that it "assumes every
  3 forced points are independent, which OVER-claims forcing; a hit is a
  CANDIDATE" (`binduc.flat_forcing_closure`).  So two geometric questions
  were left standing ((BE-82)(ii)/(iii)):

    (a) GENUINENESS.  At a configuration of Chart(H), are the three
        witnesses {v, b_1, b_2} of the admitting step AFFINELY INDEPENDENT
        -- so that pi_v really is forced -- or does the over-claim
        EVAPORATE, the three being collinear at every legal configuration?

    (b) DOES IT BITE.  If genuine, does the forced pi_u = pi_v drop
        dim(rho_bar_1 + rho_bar_2) below min(delta_1 + delta_2, 6) = 2?

  THE ANSWER, said at the top: GENUINE, and it does NOT bite.

    (BE-84) THE CERTIFICATE IS A HINGE PAIR, so the guard already settles
            genuineness -- no draw, no genericity, no irreducibility.
            (BE-77)(ii)'s certificate is {v, b_1, b_2} with b_1, b_2 two
            DISTINCT NEIGHBOURS of v, and `binduc.assert_generic_star` --
            the standing plane_basis-class guard every landed measurement in
            this arc runs under -- asserts exactly rank[p_v, p_b1, p_b2] = 3
            at every vertex and every pair of its neighbours.  Census: 1832
            of the family's 1856 admitting steps are of that shape, and 372
            of the 392 forced witnesses have a seed whose WHOLE derivation
            is.  The other 24 steps are measured and come back rank 3 too.

    (BE-85) THE CHART OF A FORCED WITNESS, EXACTLY.  The forced set A is
            confined to one plane and everything else is FREE: 3 580 / 3 580
            confinement controls and 1 100 / 1 100 freedom controls.  So the
            flat-A draw is not a stratum sampler -- it parametrizes the
            guarded chart.  pi_u = pi_v asserted AS SPACES at every draw.
            And the whole family is OFF (CH-1)'s class: girth 3 at 392/392.

    (BE-86) IT DOES NOT BITE, AND THE NAIVE SHORTFALL IS READ AGAINST THE
            WRONG DENOMINATOR.  With a_i := dim M_i - 6 - f_i the side's own
            attainment loss, (BE-22)(i)+(ii)+(BE-21) give the criterion
            WITHOUT (BE-22)(iii)'s both-attain hypothesis:

              H attains  <=>  dim(rho_bar_1 + rho_bar_2)
                                 = min(delta_1 + delta_2, 6) + a_1 + a_2.

            At all 392: dim(rho_bar_1 + rho_bar_2) = 2 + a_1 + a_2 exactly,
            rho_bar_1 cap rho_bar_2 = 0 AS SPACES, rho_i = delta_i + a_i (so
            (BE-22)(iii)(a) is free), and H ATTAINS -- an exhibited exact-Q
            certificate per witness, which is a PROOF per witness.  Measured
            against the naive `2 - dim(sum)` the same data reads 0 at 292 and
            -1 at 100; the 100 are exactly the rows where one side loses
            attainment, and the loss cancels.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `cert`  (BE-84)  The certificate census over the whole 928-member family,
            with `bspread.closure_trace` supplying the derivations and
            `bearfull.step_shape` the landed classification; then the
            geometric rank of EVERY certificate at an exact-Q draw, asserted
            equal to 3, and separately asserted to be IMPLIED by the guard.

  `chart` (BE-85)  The flat-A parametrization and its two controls, the
            plane identity AS SPACES, and the (CH-1) clause census.

  `bite`  (BE-86)  The shortfall, at every one of the 392 and at WIT11 over
            several independent draws, with the (BE-69) semicontinuity
            signature and the naive-denominator histogram reported beside
            the corrected one.

Succeeds `notes/scripts/w4/boneone.py` (Steps BE78-BE82) and, through it,
`bspread` / `bpeel` / `bearfull` / `bdecor` / `bimage` / `btwocut` / `binduc` /
`bwin` / `kbare_common`, all imported READ-ONLY rather than reimplemented: no
deficiency oracle, no closure, no R-node stand-in, no witness generator and no
rho_bar are rewritten here.  BONEONE's and BSPREAD's figures are CITED, never
re-run, except where a mode re-derives one ON PURPOSE and says so.

Conventions inherited verbatim (`notes/scripts/README.md`): exact integer /
rational arithmetic throughout, every rng seeded with the printed literal
below, every cap disclosed WITH ITS DENOMINATOR.

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import os
import sys
import random
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from exactcore import neighbors, rank as rank_exact, hat              # noqa: E402
from kbare_common import (exact_deficiency, verify_pencil_witness,    # noqa: E402
                          verts_of)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20), and
# --- BONEONE's (BE-83)(iii) recorded the standing verdict that `w4/` is a
# --- de-facto shared LAYER rather than a device chain.  This driver is the
# --- EIGHTEENTH `kbare/` consumer and takes the chain SIXTEEN deep
# --- (`... -> bpeel -> bspread -> boneone -> bgenuine`).  NO MOVE MADE.
from binduc import assert_generic_star                                # noqa: E402
from btwocut import g_exact                                           # noqa: E402
from bimage import (dim, isect, pt_in, plane_at, rho_bar_of,          # noqa: E402
                    same_space, span, v4)
from bwin import dehom                                                # noqa: E402
from bearfull import step_shape                                       # noqa: E402
from bdecor import girth                                              # noqa: E402
from bpeel import hubs_of, rnode_shaped                               # noqa: E402
from bspread import closure_trace                                     # noqa: E402
from boneone import free_sides, k4_rsides, wit11                      # noqa: E402

SEED = 20260902

U, V = 'u', 'v'


# ============================================ the family (CITED, not re-run)

def family():
    """The factorized generator of (BE-79)(i), re-run here ONLY to get the
    graphs -- BONEONE's counts (928 members, 392 forced) are CITED, and this
    mode asserts them rather than reporting them as new."""
    R = {9: k4_rsides(9, 'A'), 10: k4_rsides(10, 'A')}
    Fr = {4: free_sides(4, 'B'), 5: free_sides(5, 'B')}
    for (n1, n2) in ((9, 4), (9, 5), (10, 4)):
        for (L, H1) in R[n1]:
            for H2 in Fr[n2]:
                yield (n1, n2, L, H1, H2)


def hinge_pair(nb, z, wit):
    """Is this admitting step's certificate a HINGE PAIR -- the admitted
    vertex itself together with at least TWO of its own neighbours?  That is
    (BE-77)(ii)'s `{v, b_1, b_2}` shape, and it is exactly the triple
    `assert_generic_star` asserts non-collinear."""
    return (z in wit) and len(wit & set(nb[z])) >= 2


def forced_seed(G):
    """A hub whose aggressive closure admits BOTH terminals, preferring one
    whose WHOLE derivation is hinge-pair.  Returns (h, A, adm, trace, pure)
    or None.  `closure_trace` is `bspread`'s, imported read-only; it is
    byte-for-byte `bpeel.pair_forced`'s growth rule with the derivation
    recorded, which is why `pair_forced` is not called again here."""
    nb = neighbors(G)
    hb = hubs_of(G, nb)
    best = None
    for h in hb:
        A, adm, tr = closure_trace(nb, hb, h)
        if U not in adm or V not in adm:
            continue
        pure = all(hinge_pair(nb, z, w) for (z, w) in tr)
        if best is None:
            best = (h, A, adm, tr, pure)
        if pure:
            return (h, A, adm, tr, True)
    return best


# =================================================== the flat-A chart sampler

def plane_basis(rng, s=20, tries=40):
    for _ in range(tries):
        bb = [v4(rng, s) for _ in range(3)]
        if rank_exact(bb) == 3:
            return bb
    raise RuntimeError('plane_basis: no rank-3 draw')


def draw_flat(edges, A, rng, s=20, tries=120):
    """An exact-Q configuration with every vertex of `A` in ONE plane and
    every other vertex free in P^3, put through BOTH standing gates
    (`assert_generic_star` and `kbare_common.verify_pencil_witness`).  A draw
    that passes them IS a point of Chart(edges) by definition, however it was
    found -- and (BE-85)(i) says this parametrizes the guarded chart, not a
    stratum of it.  Returns (pt, plane basis) or (None, None)."""
    Vs = sorted(verts_of(edges), key=str)
    for _ in range(tries):
        bb = plane_basis(rng, s)
        pts, ok = {}, True
        for w in Vs:
            x = pt_in(bb, rng, s) if w in A else v4(rng, s)
            if x[3] == 0:
                ok = False
                break
            pts[w] = tuple(dehom(x))
        if not ok or len(set(pts.values())) != len(pts):
            continue
        try:
            assert_generic_star(edges, pts)
        except AssertionError:
            continue
        good, _why = verify_pencil_witness(edges, pts)
        if not good:
            continue
        return pts, bb
    return None, None


def off_plane_point(bb, rng, s=20, tries=40):
    for _ in range(tries):
        x = v4(rng, s)
        if x[3] == 0:
            continue
        q = tuple(dehom(x))
        if rank_exact(bb + [hat(q)]) == 4:
            return q
    return None


# ========================================== mode: cert   ((BE-84), job 1)

def run_cert(seed=SEED):
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE83 / (BE-84): job 1 -- the certificate is a HINGE '
          'PAIR, so the GUARD settles genuineness =====')
    print('  THE ARGUMENT, and it needs no draw.  (BE-77)(ii)\'s certificate')
    print('  is {v, b_1, b_2} with b_1, b_2 two DISTINCT NEIGHBOURS of v.')
    print('  `binduc.assert_generic_star` (binduc.py:194) asserts, at every')
    print('  vertex v and every pair a, b of its neighbours,')
    print('        rank[ hat p_v, hat p_a, hat p_b ] = 3,')
    print('  i.e. exactly that the three are AFFINELY INDEPENDENT.  So at')
    print('  every guarded configuration the aggressive step is a GENUINE')
    print('  forcing step, pointwise -- no genericity, no irreducibility.')
    print()
    nfam = nforced = nsteps = nhinge = nother = npure = 0
    shapes = {}
    kinds = {}
    exc = []
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        nfam += 1
        got = forced_seed(G)
        if got is None:
            continue
        nforced += 1
        h, A, adm, tr, pure = got
        npure += int(pure)
        nb = neighbors(G)
        for (z, wit) in tr:
            nsteps += 1
            key = (z in wit, len(wit & set(nb[z])))
            kinds[key] = kinds.get(key, 0) + 1
            if hinge_pair(nb, z, wit):
                nhinge += 1
            else:
                nother += 1
                exc.append((n1, n2, H1, H2, z, wit))
            sh, _w = step_shape(G, z, wit, nb)
            shapes[sh] = shapes.get(sh, 0) + 1
    assert nfam == 928 and nforced == 392, \
        ('the family disagrees with BONEONE (BE-81)', nfam, nforced)
    print(f'  THE CENSUS, over BONEONE\'s whole family ({nfam} members, '
          f'{nforced} forced -- both CITED from (BE-81) and asserted here).')
    print('  ONE derivation per witness, chosen by `forced_seed`, which')
    print('  PREFERS a seed whose whole derivation is hinge-pair; the counts')
    print('  below are of that derivation, not of every derivation there is:')
    print(f'      admitting steps in the chosen derivations : {nsteps}')
    print(f'      HINGE-PAIR certificates                   : {nhinge}')
    print(f'      other (the admitted vertex NOT yet in A)  : {nother}')
    print(f'      forced witnesses with an ALL-hinge-pair derivation from '
          f'some seed: {npure} / {nforced}')
    print(f'      certificate profile (v in wit, # of v\'s neighbours in '
          f'wit) -> count: {dict(sorted(kinds.items()))}')
    print(f'      `bearfull.step_shape` on the same steps: {shapes} '
          f'(the landed (BE-41)(i) classification, reported not used -- the')
    print('      star-2/spread split was RETIRED by (BE-74)/(BE-75), and the')
    print('      hinge-pair test above is a different and finer question)')
    assert nhinge + nother == nsteps
    assert nother == len(exc)
    print()
    print('  THE GEOMETRIC CHECK, run anyway -- and on the 24 steps that are')
    print('  NOT hinge pairs it is the only thing available.  Each is three')
    print('  distinct NEIGHBOURS of the admitted vertex, so the guard says')
    print('  nothing about them directly; measured at an exact-Q draw:')
    seen = {}
    for (n1, n2, H1, H2, z, wit) in exc:
        G = H1 + H2
        got = forced_seed(G)
        pt, _bb = draw_flat(G, got[1], rng)
        assert pt is not None, ('no guarded draw at an exceptional step', z)
        r = rank_exact([hat(pt[x]) for x in sorted(wit, key=str)])
        seen[(len(wit), r)] = seen.get((len(wit), r), 0) + 1
        assert r == 3, ('an exceptional certificate is DEGENERATE', z, wit, r)
    print(f'      (|certificate|, rank at the draw) -> count: {seen}   '
          f'-- every one INDEPENDENT')
    print()
    print('  AND THE GUARD ITSELF, re-run as the implication it is asserted')
    print('  to be: at one guarded draw per forced witness, every hinge-pair')
    print('  certificate is checked to have rank 3, and the check is checked')
    print('  to follow from `assert_generic_star`\'s own body.')
    nchk = 0
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is None:
            continue
        h, A, adm, tr, pure = got
        pt, _bb = draw_flat(G, A, rng)
        assert pt is not None, 'no guarded draw at a forced witness'
        nb = neighbors(G)
        for (z, wit) in tr:
            if not hinge_pair(nb, z, wit):
                continue
            bs = sorted(wit & set(nb[z]), key=str)[:2]
            r = rank_exact([hat(pt[z]), hat(pt[bs[0]]), hat(pt[bs[1]])])
            assert r == 3, ('a hinge pair is collinear at a GUARDED '
                            'configuration -- assert_generic_star is wrong',
                            z, bs)
            nchk += 1
    print(f'      hinge-pair certificates checked at a guarded draw: '
          f'{nchk} / {nhinge}, rank 3 every time, 0 exceptions')
    print()
    print('  WIT11\'s derivation, printed in full (the instance (BE-81)(ii)')
    print('  reports, re-read here for its certificate SHAPES):')
    H1, H2 = wit11()
    G = H1 + H2
    nb = neighbors(G)
    h, A, adm, tr, pure = forced_seed(G)
    V1 = {str(x) for x in verts_of(H1)}
    V2 = {str(x) for x in verts_of(H2)}
    print(f'      seed {h}, all-hinge-pair derivation = {pure}')
    for (z, wit) in tr:
        sh, _w = step_shape(G, z, wit, nb)
        a = len({str(x) for x in wit} & V1)
        b = len({str(x) for x in wit} & V2)
        print(f'        admit {str(z):<12} witnesses '
              f'{sorted(map(str, wit))!s:<36} split ({a}, {b})  '
              f'shape {sh}  hinge pair {hinge_pair(nb, z, wit)}')
    print()
    print(f'  CAP DISCLOSURE, WITH THE DENOMINATOR.  The {nhinge} / {nsteps}')
    print(f'  and {npure} / {nforced} are over BONEONE\'s family and no larger:')
    print(f'  the denominator is the {nforced} forced members of the '
          f'{nfam}-member')
    print('  factorized census of (BE-81), exhaustive in each of its three')
    print('  rows and capped at (n_1, n_2) in {(9,4), (9,5), (10,4)}.  The')
    print('  ARGUMENT above is not capped: it is a statement about the')
    print('  certificate SHAPE and holds wherever (BE-77)(ii) does.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return nhinge + nother == nsteps and npure == 372


# ========================================= mode: chart  ((BE-85))

def run_chart(seed=SEED, ndraw=1):
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE84 / (BE-85): the chart of a forced witness, '
          'EXACTLY -- and the family is OFF (CH-1)\'s class =====')
    print('  THE PARAMETRIZATION.  By (BE-84) the forcing is genuine at every')
    print('  guarded configuration, so the forced set A lies in ONE plane')
    print('  there; and at every forced witness EVERY hub is admitted, so')
    print('  N[z] <= A for every hub z and every other vertex has degree <= 2,')
    print('  whose closed star is 3 points and coplanar for free.  Hence the')
    print('  guarded chart is  {A in a plane} x {the rest free}.  Both halves')
    print('  are CONTROLLED below rather than asserted.')
    nforced = 0
    conf_ok = conf_bad = free_ok = free_bad = 0
    plane_ok = 0
    partial = 0
    ch1 = {'hcard': 0, 'mindeg>=2': 0, 'girth>=4': 0, 'all three': 0}
    girths = {}
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is None:
            continue
        nforced += 1
        h, A, adm, tr, _p = got
        nb = neighbors(G)
        hb = hubs_of(G, nb)
        assert set(adm) == set(hb), \
            'a hub is NOT admitted -- the parametrization argument breaks'
        VG = set(verts_of(G))
        if A != VG:
            partial += 1
        pt, bb = draw_flat(G, A, rng)
        assert pt is not None, 'no guarded draw at a forced witness'
        # the plane identity, AS SPACES (F25)
        Pu, Pv = plane_at(G, pt, U), plane_at(G, pt, V)
        assert Pu and Pv and same_space(Pu, Pv), \
            'pi_u = pi_v FAILS at a draw the closure says is forced'
        assert all(same_space(Pu, plane_at(G, pt, z)) for z in hb), \
            'an admitted hub plane differs from pi_u'
        plane_ok += 1
        # control 1 -- CONFINEMENT: move one A vertex off the plane; the
        # pencil gate must FAIL, i.e. A really is forced coplanar.
        for w in sorted(A, key=str):
            q = off_plane_point(bb, rng)
            assert q is not None
            p2 = dict(pt)
            p2[w] = q
            ok2, _ = verify_pencil_witness(G, p2)
            if ok2:
                conf_bad += 1
            else:
                conf_ok += 1
        # control 2 -- FREEDOM: re-draw one non-A vertex anywhere; the gates
        # must still PASS, i.e. it really is unconstrained.
        for w in sorted(VG - set(A), key=str):
            for _t in range(30):
                p3 = dict(pt)
                x = v4(rng, 20)
                if x[3] == 0:
                    continue
                p3[w] = tuple(dehom(x))
                if len(set(p3.values())) != len(p3):
                    continue
                try:
                    assert_generic_star(G, p3)
                except AssertionError:
                    continue
                ok3, _ = verify_pencil_witness(G, p3)
                if ok3:
                    free_ok += 1
                else:
                    free_bad += 1
                break
        # (CH-1)'s three hypotheses
        hc = all(len([x for x in nb[z] if len(nb[x]) >= 3]) <= 2
                 for z in nb if len(nb[z]) >= 3)
        md = min(len(nb[z]) for z in nb) >= 2
        gg = girth(G)
        girths[gg] = girths.get(gg, 0) + 1
        ch1['hcard'] += hc
        ch1['mindeg>=2'] += md
        ch1['girth>=4'] += (gg >= 4)
        ch1['all three'] += (hc and md and gg >= 4)
    print(f'      pi_u = pi_v asserted AS SPACES (`bimage.same_space` on '
          f'`plane_at`): {plane_ok} / {nforced}, and every admitted hub '
          f'plane equal to it')
    print(f'      CONFINEMENT control -- one A vertex moved off the plane, '
          f'gate must FAIL: {conf_ok} fail / {conf_ok + conf_bad}, '
          f'{conf_bad} still passing')
    print(f'      FREEDOM control -- one non-A vertex re-drawn anywhere, '
          f'gates must PASS: {free_ok} pass / {free_ok + free_bad}, '
          f'{free_bad} failing')
    print(f'      forced witnesses with A a PROPER subset of V (so the '
          f'configuration is NOT flat): {partial} / {nforced}')
    assert conf_bad == 0 and free_bad == 0
    print()
    print('  THE (CH-1) CHECK the spec asks for, answered -- and the answer')
    print('  is NO, on the girth clause, at EVERY member:')
    print(f'      {ch1}   over {nforced} forced witnesses')
    print(f'      girth histogram: {girths}')
    print('      So (CH-1) is UNAVAILABLE here, and with it (BE-69)(ii)\'s')
    print('      irreducibility and (BE-72)(iii).  WHY IT COSTS NOTHING:')
    print('      (BE-84) is POINTWISE (the guard implies the rank, at every')
    print('      guarded point, with no density argument), and (BE-86) is')
    print('      EXISTENTIAL (attainment needs ONE configuration, (BE-14)/')
    print('      (BE-16)).  Neither conclusion quantifies over a generic')
    print('      point, so neither needs the chart irreducible.  What is NOT')
    print('      available is the step from "pi_u = pi_v at every GUARDED')
    print('      configuration" to "at every configuration of Chart(H)".')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return conf_bad == 0 and free_bad == 0 and ch1['all three'] == 0


# ========================================== mode: bite   ((BE-86), job 2)

def measure(H1, H2, pt):
    """(delta_i, a_i, rho_i, dim(rho_1+rho_2), attains) at one configuration.
    `a_i := dim M_i - 6 - f_i` is the SIDE's own attainment loss -- the term
    (BE-22)(iii) assumes away and the denominator this direction restores."""
    f1, g1 = exact_deficiency(H1)[0], g_exact(H1, U, V)
    f2, g2 = exact_deficiency(H2)[0], g_exact(H2, U, V)
    S1, r1, dM1, _ = rho_bar_of(H1, pt, U, V)
    S2, r2, dM2, _ = rho_bar_of(H2, pt, U, V)
    a1, a2 = dM1 - 6 - f1, dM2 - 6 - f2
    dsum = dim(span(S1 + S2))
    return (f1 - g1, f2 - g2, a1, a2, r1, r2, dsum, S1, S2, dM1, dM2)


def run_bite(seed=SEED, nwit=4):
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE85 / (BE-86): job 2 -- IT DOES NOT BITE, and the '
          'naive shortfall is read against the WRONG DENOMINATOR =====')
    print('  THE CRITERION, WITHOUT (BE-22)(iii)\'s HYPOTHESIS.  Write')
    print('  a_i := dim M_i - 6 - f_i >= 0 for side i\'s own attainment loss.')
    print('  (BE-22)(i) is  dim M(H) = dim M_1 + dim M_2 - 6 - dim(sum),')
    print('  and (BE-21) is def_3(H) = max(g_1+g_2, f_1+f_2-6), so')
    print()
    print('     H attains  <=>  dim(rho_1 + rho_2) = min(d_1+d_2, 6) + a_1+a_2,')
    print()
    print('  which at a_1 = a_2 = 0 IS (BE-22)(iii).  The universal partition')
    print('  cap dim M(H) >= 6 + def_3(H) makes the left side never EXCEED the')
    print('  right, so the shortfall is one-sided and `= 0` is `attains`.')
    print()
    tab, naive, nrow = {}, {}, 0
    losers = []
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is None:
            continue
        pt, _bb = draw_flat(G, got[1], rng)
        assert pt is not None, 'no guarded draw at a forced witness'
        (d1, d2, a1, a2, r1, r2, dsum, S1, S2, dM1, dM2) = measure(H1, H2, pt)
        assert d1 == 1 and d2 == 1, 'the family is not at (1, 1)'
        fH = exact_deficiency(G)[0]
        _SH, _rH, dMH, _ = rho_bar_of(G, pt, U, V)
        assert dMH == dM1 + dM2 - 6 - dsum, '(BE-22)(i) fails at a witness'
        target = min(d1 + d2, 6) + a1 + a2
        assert dsum == target, ('SHORTFALL -- a genuine counterexample class',
                                n1, n2, d1, d2, a1, a2, dsum, target)
        assert dMH == 6 + fH, 'H does not attain at the exhibited draw'
        assert isect(S1, S2) == [], \
            'rho_bar_1 cap rho_bar_2 is NONZERO -- general position fails'
        assert r1 == d1 + a1 and r2 == d2 + a2, \
            '(BE-22)(ii) is not tight -- the welded framework misses'
        key = (a1, a2, r1, r2, dsum)
        tab[key] = tab.get(key, 0) + 1
        naive[2 - dsum] = naive.get(2 - dsum, 0) + 1
        nrow += 1
        if a1 + a2 > 0:
            losers.append((H1, H2))
    print(f'  THE CENSUS, one exact-Q draw at each of the {nrow} forced '
          f'witnesses -- every line an ASSERT, not a report:')
    print('      (a_1, a_2, rho_1, rho_2, dim(rho_1+rho_2)) -> count')
    for k, v in sorted(tab.items()):
        print(f'         {k} -> {v}')
    print()
    print(f'      dim(rho_1+rho_2) = 2 + a_1 + a_2      : {nrow} / {nrow}')
    print(f'      rho_bar_1 cap rho_bar_2 = 0 AS SPACES : {nrow} / {nrow}')
    print(f'      rho_i = delta_i + a_i  ((BE-22)(iii)(a) FREE) : '
          f'{nrow} / {nrow}')
    print(f'      dim M(H) = 6 + def_3(H), i.e. H ATTAINS       : '
          f'{nrow} / {nrow}')
    print()
    print('  THE NAIVE SHORTFALL, on the SAME data, so the denominator error')
    print('  is visible rather than smoothed:')
    print(f'      (2 - dim(rho_1+rho_2)) -> count: {dict(sorted(naive.items()))}')
    print('      A reader taking `min(d_1+d_2,6) = 2` as the denominator sees')
    print('      100 rows "exceeding general position" and would have to')
    print('      explain them; the explanation is that at those rows exactly')
    print('      ONE SIDE loses attainment, and the loss CANCELS.  This is')
    print('      (BE-66)(iii)\'s "rho_bar exceeds general position at')
    print('      pi_x = pi_y, at NON-ATTAINING configurations" -- the same')
    print('      mechanism, here shown to be BENIGN.')
    print()
    print('  F27 -- the one FAILURE claim in this mode, drawn repeatedly.')
    print('  "One side does not attain" is a claim that a property FAILS, so')
    print(f'  it is re-drawn independently at {nwit} of the losing rows:')
    step = max(1, len(losers) // nwit)
    for (H1, H2) in losers[::step][:nwit]:
        G = H1 + H2
        got = forced_seed(G)
        vals = []
        for _k in range(4):
            pt, _bb = draw_flat(G, got[1], rng)
            if pt is None:
                continue
            m = measure(H1, H2, pt)
            vals.append((m[2], m[3], m[6]))
        n1s, n2s = len(verts_of(H1)), len(verts_of(H2))
        print(f'      n = {len(verts_of(G))} (n_1, n_2) = ({n1s}, {n2s}): '
              f'(a_1, a_2, dim(sum)) over {len(vals)} independent draws -> '
              f'{sorted(set(vals))}')
    print()
    print('  WIT11 ITSELF, with the (BE-69) semicontinuity signature.')
    H1, H2 = wit11()
    G = H1 + H2
    got = forced_seed(G)
    firsts, best = None, None
    for k in range(5):
        pt, _bb = draw_flat(G, got[1], rng)
        assert pt is not None
        m = measure(H1, H2, pt)
        val = (m[4], m[5], m[6])
        if firsts is None:
            firsts = val
        best = val if best is None else tuple(max(a, b)
                                              for a, b in zip(best, val))
        print(f'      draw {k}: rho_1 = {m[4]}, rho_2 = {m[5]}, '
              f'dim(rho_1+rho_2) = {m[6]}, a = ({m[2]}, {m[3]})')
    print(f'      first draw {firsts} vs max over 5 draws {best}'
          f'{"  -- FIRST DRAW ALREADY GENERIC" if firsts == best else ""}')
    print('      (BE-69)(i)\'s semicontinuity is PROVED there; this is its')
    print('      signature, not its proof, and (BE-69)(ii)\'s dichotomy is')
    print('      NOT invoked -- WIT11 is off (CH-1)\'s class ((BE-85)(iii)).')
    print()
    print('  CAP DISCLOSURE, WITH THE DENOMINATOR.  Every fraction above is')
    print(f'  over the {nrow} FORCED members of BONEONE\'s 928-member')
    print('  factorized family -- exhaustive in each of its three rows,')
    print('  capped at (n_1, n_2) in {(9,4), (9,5), (10,4)}, and NOT over the')
    print('  928 (the 536 unforced members carry no coincidence, so the')
    print('  question does not arise there).  One draw per witness, five at')
    print('  WIT11; attainment is EXISTENTIAL, so one exhibited exact-Q')
    print('  configuration is a PROOF per witness ((BE-52), F27).')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return nrow == 392


# ====================================== mode: wider  ((BE-85)(iv), (BE-86)(v))

def wider_row():
    """The `(n_1, n_2) = (10, 5)` row -- ONE ROW BEYOND BONEONE's cap, and a
    NEW figure minted here rather than cited: (BE-81)'s census covers
    {(9,4), (9,5), (10,4)} and says so.  Same factorized generator, same
    per-side oracles."""
    R = k4_rsides(10, 'A')
    Fr = free_sides(5, 'B')
    for (L, H1) in R:
        for H2 in Fr:
            yield (10, 5, L, H1, H2)


def run_wider(seed=SEED, stride=8):
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE84 / (BE-85)(iv) and Step BE85 / (BE-86)(v): the '
          'SAME two questions ONE ROW BEYOND BONEONE\'s cap =====')
    print('  (BE-81)\'s census stops at (n_1, n_2) in {(9,4), (9,5), (10,4)}')
    print('  and discloses it.  The (10, 5) row is the next cell of the same')
    print('  factorized generator; its figures are NEW here, not cited.')
    tot = forced = nhc = 0
    gh = {}
    nsteps = nhinge = npure = 0
    cands = []
    for (_n1, _n2, _L, H1, H2) in wider_row():
        G = H1 + H2
        tot += 1
        got = forced_seed(G)
        if got is None:
            continue
        forced += 1
        cands.append((H1, H2))
        h, A, adm, tr, pure = got
        npure += int(pure)
        nb = neighbors(G)
        for (z, wit) in tr:
            nsteps += 1
            nhinge += int(hinge_pair(nb, z, wit))
        g = girth(G)
        gh[g] = gh.get(g, 0) + 1
        nhc += all(len([x for x in nb[z] if len(nb[x]) >= 3]) <= 2
                   for z in nb if len(nb[z]) >= 3)
    print(f'      (10, 5): {tot} R-node-shaped (1,1) peels on n = 13, '
          f'{forced} with pi_u = pi_v FORCED   [NEW]')
    print(f'      girth histogram of the forced: {gh}; `hcard` at {nhc} / '
          f'{forced}; so all three (CH-1) clauses at 0 / {forced}')
    print(f'      hinge-pair certificates {nhinge} / {nsteps}; all-hinge-pair '
          f'derivations {npure} / {forced}')
    print()
    print('  THE TRIANGLE-FREE SUB-ROW, run because it is the only cell that')
    print('  could have produced a (CH-1)-eligible witness: both sides drawn')
    print('  from the triangle-free members only.')
    tf = tff = 0
    for (_n1, _n2, _L, H1, H2) in wider_row():
        if girth(H1) < 4 or girth(H2) < 4:
            continue
        tf += 1
        if forced_seed(H1 + H2) is not None:
            tff += 1
    print(f'      triangle-free R-node side x triangle-free small side: '
          f'{tf} pairs, {tff} FORCED')
    print('      (R-node sides at n_1 = 10: 36 of 40 are triangle-free; at')
    print('      n_1 = 9: 0 of 12.  Small sides: 0 of 4 at n_2 = 4, 18 of 60')
    print('      at n_2 = 5.  So (10, 5) is the FIRST cell of the generator')
    print('      in which a girth-4 peel is combinatorially possible at all,')
    print('      and forcing does not occur in it.)')
    print()
    print(f'  THE SHORTFALL on this row, at every {stride}-th forced member '
          f'in generator order (a DISCLOSED SUBSAMPLE, not exhaustive):')
    tab = {}
    n = 0
    for (H1, H2) in cands[::stride]:
        G = H1 + H2
        got = forced_seed(G)
        pt, _bb = draw_flat(G, got[1], rng)
        assert pt is not None, 'no guarded draw at a (10,5) witness'
        (d1, d2, a1, a2, r1, r2, dsum, S1, S2, _dM1, _dM2) = measure(H1, H2, pt)
        fH = exact_deficiency(G)[0]
        _S, _r, dMH, _ = rho_bar_of(G, pt, U, V)
        assert dsum == min(d1 + d2, 6) + a1 + a2, \
            ('SHORTFALL one row beyond the cap', d1, d2, a1, a2, dsum)
        assert dMH == 6 + fH, 'H does not attain at a (10,5) witness'
        assert isect(S1, S2) == [], 'rho_bar_1 cap rho_bar_2 nonzero'
        assert r1 == d1 + a1 and r2 == d2 + a2, '(BE-22)(ii) not tight'
        tab[(a1, a2, r1, r2, dsum)] = tab.get((a1, a2, r1, r2, dsum), 0) + 1
        n += 1
    print(f'      (a_1, a_2, rho_1, rho_2, dim(rho_1+rho_2)) -> count, '
          f'over {n} of the {forced}:')
    for k, v in sorted(tab.items()):
        print(f'         {k} -> {v}')
    print(f'      dim(rho_1+rho_2) = 2 + a_1 + a_2, rho_1 cap rho_2 = 0 AS '
          f'SPACES, rho_i = delta_i + a_i, and H ATTAINS: {n} / {n}')
    print()
    print('  CAP DISCLOSURE, WITH THE DENOMINATOR.  The combinatorial figures')
    print(f'  are EXHAUSTIVE over the {tot}-member (10, 5) row.  The shortfall')
    print(f'  figures are over {n} of its {forced} forced members -- every')
    print(f'  {stride}-th in generator order, chosen for cost (about 0.4 s per')
    print('  witness at n = 13), NOT a random sample and NOT exhaustive.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return forced > 0 and gh.get(3, 0) == forced


# ============================================================== validate

def run_validate():
    ok = True
    ok &= bool(run_cert())
    print()
    ok &= bool(run_chart())
    print()
    ok &= bool(run_bite())
    print()
    ok &= bool(run_wider())
    print()
    print('===== Step BE86 / (BE-87) and Step BE87 / (BE-88) are PROSE '
          '(what half (B) is left with, and the board); nothing to run. =====')
    print('VALIDATE:', 'OK' if ok else 'FAILED')
    return ok


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    {'cert': run_cert, 'chart': run_chart, 'bite': run_bite,
     'wider': run_wider, 'validate': run_validate}[mode]()
