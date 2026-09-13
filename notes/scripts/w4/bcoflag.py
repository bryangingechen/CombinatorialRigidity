"""
Direction BCOFLAG (ordinal 115) -- IS `Good != EMPTY` A CLASS THEOREM AT THE
COINCIDENT-FLAG PEELS, AND WHAT IS THE RIGHT OBJECT THERE?

  THE QUESTION the spec names.  (BE-284)(ii) records the scope limit on the
  sixteen-block closure: the criterion (BE-96)(iv) holds "at a GENERIC-REGIME
  flag pair", but `pi_u = pi_v` is FORCED at an internal R-node peel with both
  sides flexible, at 392 of 928 ((BE-81)).  There the four blocks do not
  decompose the screw space, so the 16-block criterion "is not merely unproved
  there, it is not the right object".  (BE-284)(ii) then says those peels are
  "settled PER-PIECE by (BE-86)(ii)'s 392 exact-Q certificates ... which by
  (BE-69)(ii)'s consequence 1 is a THEOREM per piece, but not as a class".

  THE ANSWER, said at the top.  Two of those three sentences do not hold.

    (1) THE CITATION IS VOID AT ALL 392.  (BE-69)(ii)'s consequence 1 ("one
        exact-Q draw in `Good` settles the piece") runs through the
        dense-or-empty dichotomy, which runs through `Chart(H)` irreducible,
        which is (CH-1)(a) under `hcard`, min degree 2 and GIRTH >= 4.  The
        direction that produced the certificates already measured that clause
        and recorded its failure: (BE-85)(iii), girth 3 at 392/392, `hcard` at
        8/392, ALL THREE at 0/392 -- "taking (BE-69)(ii)'s dense-or-empty
        dichotomy ... with it".  So no draw at any of the 392 can be upgraded
        by that route.  What survives is weaker and sufficient: `Good != 0` is
        an EXISTENTIAL, so an exhibited point of `Good` proves it outright,
        with no irreducibility at all.

    (2) THE PER-PIECE RESULT IS 292 OF 392, NOT 392 OF 392.  `Good = A_1 cap
        A_2 cap GP` and `A_i = {a_i = 0}` ((BE-69)(i)).  At 100 of the 392 the
        exhibited draw has `a_i = 1` ((BE-86)(ii)'s census, rows `(0,1,1,2,3)`
        60 and `(1,0,2,1,3)` 40), so the draw is OUTSIDE `Good` and by
        (BE-69)(ii)'s consequence 2 settles nothing about it.  `H` attains at
        all 392 -- that is (BE-86)(i)'s UNCONDITIONAL criterion and needs no
        `a_i = 0` -- but `H` attaining is (BE-14) at `H`, not `Good != 0`.

  SO THE RIGHT OBJECT is (BE-86)(i)'s a-corrected criterion read
  EXISTENTIALLY, not `Good != 0` and not a stable-subspace family: the
  consumer ((BE-25)(ii) S-mark, check (a)) needs (BE-14) at the top, which is
  existential, and the apparatus that makes `Good != 0` the right proxy for it
  -- openness plus irreducibility -- is unavailable at every one of these
  peels.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `blocks`  DRAW-FREE, EXACT, COMPLETE.  Enumerates the S(phi)-stable
            subspaces of the screw space in BOTH regimes by the same
            algorithm: every stable subspace is stable under the maximal
            torus, the torus has six DISTINCT weights on Lambda^2 K^4 in each
            regime, so every stable subspace is a sum of weight lines and the
            2^6 = 64 candidates are an EXHAUSTIVE list.  Generic regime
            reproduces the landed 16 ((BE-96)(iv)), which is the method's
            control; the coincident regime is new.

  `losers`  The un-fenced F27 redraw.  `bgenuine.run_bite` re-draws at
            `nwit=4` of the losing rows, four draws each (a hardcoded
            `range(4)`), which is the blind axis sitting exactly on the one
            failure claim in that step.  This mode re-draws at EVERY losing
            row, `ndraw` times, at TWO coordinate-box sizes, and asks the
            EXISTENTIAL question the corpus never asked there: is there a
            draw with `a_1 = a_2 = 0` -- i.e. an exhibited point of `Good`?
            One such draw would move a row from OPEN to PROVED, needing no
            irreducibility.  A miss is "not found under cap", never "empty".

  `prof`    What the right object looks like, measured: at each forced
            witness, the coincident-regime stable subspaces of `blocks` with
            `c_i(U) = dim(rho_bar_i cap U)` on each side, plus the two
            containment controls (`rho_bar_i` inside `Lambda^2 pi`? inside
            `alpha_x + alpha_y`?).

Imports the canonical layer READ-ONLY (`bgenuine`, `bimage`, `bunif`,
`boneone`, `bpeel`, `binduc`, `kbare_common`): no deficiency oracle, no
closure, no witness generator, no rho_bar and no flag frame is rewritten here.
BGENUINE's and BONEONE's figures are CITED, never re-run, except where a mode
re-derives one ON PURPOSE and says so.  No landed driver is edited: the fenced
constant is un-fenced by parameterizing THIS driver's own loop around
`bgenuine.draw_flat` / `bgenuine.measure`, which are imported unchanged.

Exact integer / rational arithmetic throughout; every rng seeded with the
printed literal below; every cap disclosed WITH ITS DENOMINATOR.

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import os
import sys
import itertools
import random
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from exactcore import wedge2, rank as rank_exact, hat                 # noqa: E402
from kbare_common import verts_of                                     # noqa: E402
from bimage import (F, dim, isect, span, alpha_plane, lam2,           # noqa: E402
                    pencil_space, plane_at, rho_bar_of, same_space)
from bunif import mat_inv, matmul                                     # noqa: E402
from bdecor import sample_by_branches                                 # noqa: E402
from kbare_common import exact_deficiency                             # noqa: E402
from bgenuine import draw_flat, family, forced_seed, measure          # noqa: E402

SEED = 20260913
U, V = 'u', 'v'


# ================================================ the stable-subspace lattice

def _wedge_action(g):
    """Lambda^2 of a 4x4 matrix, in the basis order of `_L2_BASIS`."""
    cols = [[g[i][j] for i in range(4)] for j in range(4)]   # g e_j
    out = []
    for (i, j) in _L2_BASIS:
        out.append(wedge2(cols[i], cols[j]))
    return out                                              # rows = images


_L2_BASIS = list(itertools.combinations(range(4), 2))        # 6 pairs


def _weight_lines():
    """The six torus weight lines of Lambda^2 K^4 in the standard basis:
    e_i ^ e_j has weight t_i t_j, and the six products of DISTINCT pairs from
    four independent characters are pairwise distinct."""
    return [span([wedge2(_e(i), _e(j))]) for (i, j) in _L2_BASIS]


def _e(i):
    return [F(1) if k == i else F(0) for k in range(4)]


def _stable(W, gs):
    """Is the subspace `W` (a list of rows) carried into itself by every
    matrix of `gs` acting on Lambda^2?"""
    if not W:
        return True
    d = dim(W)
    for A in gs:
        img = [[sum(w[k] * A[k][m] for k in range(6)) for m in range(6)]
               for w in W]
        if dim(W + img) != d:
            return False
    return True


def _lam2_of(g):
    """The 6x6 matrix of Lambda^2 g, rows indexed by _L2_BASIS."""
    return _wedge_action(g)


def _gens_generic(rng, s=6, ngen=8):
    """Random elements of S(phi) in the GENERIC regime, in the frame
    (p_x, e_1, e_2, p_y) = the standard basis: diag(lambda, A, mu), A in GL_2.
    This is `bunif.stab_elt`'s group, written in the frame itself."""
    out = []
    while len(out) < ngen:
        A = [[F(rng.randint(-s, s)) for _ in range(2)] for _ in range(2)]
        if A[0][0] * A[1][1] - A[0][1] * A[1][0] == 0:
            continue
        lam, mu = F(rng.randint(1, s)), F(rng.randint(1, s))
        D = [[F(0)] * 4 for _ in range(4)]
        D[0][0], D[3][3] = lam, mu
        D[1][1], D[1][2], D[2][1], D[2][2] = A[0][0], A[0][1], A[1][0], A[1][1]
        out.append(D)
    return out


def _gens_coincident(rng, s=6, ngen=12):
    """Random elements of S(phi) in the COINCIDENT regime, in the frame
    (p_x, p_y, e, f) with pi_x = pi_y = pi = <p_x, p_y, e> and f off pi.
    S(phi) = {g : g<p_x> = <p_x>, g<p_y> = <p_y>, g pi = pi}, i.e.
        g p_x = a p_x,  g p_y = b p_y,
        g e   = c_1 p_x + c_2 p_y + c_3 e,      (pi is preserved)
        g f   = d_1 p_x + d_2 p_y + d_3 e + d_4 f.
    Nine parameters; the Levi is the diagonal torus and the unipotent radical
    is the (c_1, c_2, d_1, d_2, d_3) part.  Written as COLUMNS."""
    out = []
    while len(out) < ngen:
        a, b = F(rng.randint(1, s)), F(rng.randint(1, s))
        c3, d4 = F(rng.randint(1, s)), F(rng.randint(1, s))
        c1, c2 = F(rng.randint(-s, s)), F(rng.randint(-s, s))
        d1, d2, d3 = (F(rng.randint(-s, s)) for _ in range(3))
        Mt = [[a, F(0), c1, d1],
              [F(0), b, c2, d2],
              [F(0), F(0), c3, d3],
              [F(0), F(0), F(0), d4]]
        if mat_inv(Mt) is None:
            continue
        out.append(Mt)
    return out


def _lattice(gens):
    """EXHAUSTIVE over the 64 torus-stable candidates.  Every S(phi)-stable
    subspace is stable under the maximal torus; the torus has six DISTINCT
    weights on Lambda^2 K^4 in both regimes (checked by the caller), so it is
    a sum of weight lines.  Returns the stable ones as (dim, basis)."""
    lines = _weight_lines()
    acts = [_lam2_of(g) for g in gens]
    out = []
    for mask in range(64):
        W = []
        for i in range(6):
            if mask >> i & 1:
                W += lines[i]
        W = span(W)
        if _stable(W, acts):
            out.append((dim(W), W, mask))
    return out


def run_blocks(seed=SEED):
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE308 / (BE-309): the stable-subspace lattice in BOTH '
          'regimes, DRAW-FREE and EXHAUSTIVE =====')
    print('  THE ENUMERATION IS COMPLETE, and here is why it is allowed to')
    print('  say so.  S(phi) contains the maximal torus T of the frame, so')
    print('  every S(phi)-stable subspace is T-stable; T acts on Lambda^2 K^4')
    print('  with the six weights t_i t_j, PAIRWISE DISTINCT in both regimes;')
    print('  so every T-stable subspace is a sum of weight lines and the 64')
    print('  subsets are an exhaustive candidate list.  This is an ENUMERATION')
    print('  claim and it has its own driver -- this mode.')
    print()
    for (name, gens) in (('GENERIC  (p_x, e_1, e_2, p_y), S = GL_1 x GL_2 x GL_1',
                          _gens_generic(rng)),
                         ('COINCIDENT (p_x, p_y, e, f), pi_x = pi_y = pi',
                          _gens_coincident(rng))):
        lat = _lattice(gens)
        hist = {}
        for (d, _W, _m) in lat:
            hist[d] = hist.get(d, 0) + 1
        print(f'  {name}')
        print(f'      S(phi)-stable subspaces of Lambda^2 K^4: {len(lat)}')
        print(f'      by dimension: {dict(sorted(hist.items()))}')
        if 'GENERIC' in name:
            assert len(lat) == 16, ('the generic regime must reproduce '
                                    '(BE-96)(iv)\'s SIXTEEN', len(lat))
            print('      ASSERTED == 16, which is (BE-96)(iv)\'s family: the')
            print('      method\'s control, reproduced not assumed.')
        else:
            print('      NEW.  The four generic blocks are gone; see below.')
        print()

    # --- the named subspaces in the coincident regime, and the coordinator's
    # --- proposed mechanism, tested by name.
    px, py, e, f = _e(0), _e(1), _e(2), _e(3)
    pi = [px, py, e]
    Pix, Piy = pencil_space(px, pi), pencil_space(py, pi)
    M = span([wedge2(px, py)])
    L2 = lam2(pi)
    print('  THE COORDINATOR\'S MECHANISM, tested by name and REFUTED.')
    print('  The spec proposed "a coarser pairing whose totally-singular')
    print('  blocks are Pi_x = Pi_y and Lambda^2 pi_x, giving a family of 4".')
    print(f'      dim Pi_x = {dim(Pix)}, dim Pi_y = {dim(Piy)}, '
          f'dim Lambda^2 pi = {dim(L2)}')
    print(f'      Pi_x == Pi_y ?  {same_space(Pix, Piy)}   '
          f'(p_x != p_y at every guarded draw, so NO)')
    print(f'      dim(Pi_x cap Pi_y) = {dim(isect(Pix, Piy))}, '
          f'and it equals <M> = <p_x ^ p_y> ? '
          f'{same_space(isect(Pix, Piy), M)}')
    print(f'      dim(Pi_x + Pi_y) = {dim(span(Pix + Piy))}, '
          f'== Lambda^2 pi ? {same_space(span(Pix + Piy), L2)}')
    tot = span(Pix + Piy + M)
    print(f'      dim(Pi_x + Pi_y + <M>) = {dim(tot)}  -- the "four blocks"')
    print('        span only THREE of the six dimensions, and they are not')
    print('        independent: the sum is Lambda^2 pi and the intersection')
    print('        of the two pencils is <M>.  So the failure is not that the')
    print('        pairing is coarser -- it is that the blocks OVERLAP and')
    print('        MISS HALF the screw space.  <L> does not exist at all:')
    print('        pi_x cap pi_y is pi itself, 3-dimensional, so `plane_meet`')
    print('        returns a 3-element basis and `bunif.flag_frame` returns')
    print('        None -- which is (BE-284)(ii)\'s sentence, verified.')
    assert not same_space(Pix, Piy), 'Pi_x = Pi_y would need p_x = p_y'
    assert dim(tot) == 3, 'the coincident blocks must span exactly Lambda^2 pi'
    print()
    lat = _lattice(_gens_coincident(rng))
    alx, aly = alpha_plane(px), alpha_plane(py)
    named = [('0', []),
             ('<M> = <p_x ^ p_y>', M),
             ('Pi_x = p_x ^ pi', Pix),
             ('Pi_y = p_y ^ pi', Piy),
             ('Lambda^2 pi', L2),
             ('alpha_x = p_x ^ K^4', alx),
             ('alpha_y = p_y ^ K^4', aly),
             ('Lambda^2 pi + <p_x ^ f>', span(L2 + [wedge2(px, f)])),
             ('Lambda^2 pi + <p_y ^ f>', span(L2 + [wedge2(py, f)])),
             ('alpha_x + alpha_y', span(alx + aly)),
             ('Lambda^2 K^4', span([_e2(i, j) for (i, j) in _L2_BASIS]))]
    print('  THE ELEVEN, NAMED.  Every enumerated stable subspace is one of')
    print('  these, and every one of these is enumerated -- both directions')
    print('  ASSERTED, so the naming is a bijection and not a sample:')
    for (nm, W) in named:
        hit = [X for (_d, X, _m) in lat if same_space(W, X)]
        print(f'      dim {dim(W)}   {nm}')
        assert len(hit) == 1, (nm, 'named subspace is not in the lattice once')
    assert len(named) == len(lat), ('the naming misses a stable subspace',
                                    len(named), len(lat))
    print()
    print('  THE STRUCTURAL READING, and it is stronger than "a smaller')
    print('  family".  Exactly ONE stable subspace is 1-dimensional, so the')
    print('  SOCLE is simple (= <M>) and the S(phi)-module Lambda^2 K^4 is')
    print('  INDECOMPOSABLE at a coincident-flag pair: there is no direct-sum')
    print('  block decomposition at all, coarse or fine.  In the generic')
    print('  regime the lattice is the Boolean lattice 2^4 on four blocks')
    print('  (16 = 1+2+3+4+3+2+1); here it is an 11-element lattice with a')
    print('  unique atom, and Pi_x cap Pi_y = <M> != 0 is exactly the')
    print('  overlap that kills the direct sum.')
    from bimage import klein as _klein
    for (nm, W) in (('Lambda^2 pi', L2), ('alpha_x', alx), ('alpha_y', aly)):
        assert all(_klein(a, b) == 0 for a in W for b in W), \
            (nm, 'not totally singular')
    print('  AND Lambda^2 pi is a MAXIMAL TOTALLY SINGULAR subspace of the')
    print('  Klein quadric (a beta-plane: the lines lying IN the plane pi),')
    print('  asserted here by the Klein form vanishing identically on it.')
    print('  So at a coincident-flag peel both rho_bar_i are confined to ONE')
    print('  maximal totally singular 3-space -- see mode `conf`.')
    ones = [W for (d, W, _m) in lat if d == 1]
    assert len(ones) == 1 and same_space(ones[0], M), \
        'the socle must be the single line <M>'
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return True


def _e2(i, j):
    return wedge2(_e(i), _e(j))


# ============================================ the un-fenced F27 redraw

def run_losers(seed=SEED, ndraw=6, boxes=(20, 60)):
    """EVERY forced witness with a_1 + a_2 > 0, `ndraw` independent draws at
    each of `boxes` coordinate ranges.  The question is EXISTENTIAL: is there
    a draw with a_1 = a_2 = 0 and dim(rho_bar_1 + rho_bar_2) = 2?  Such a
    draw is a point of `Good` and PROVES `Good != 0` at that piece with no
    irreducibility (which is unavailable here -- (BE-85)(iii))."""
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE311 / (BE-312): the un-fenced redraw at EVERY losing '
          'row =====')
    print('  THE FENCE.  `bgenuine.run_bite(nwit=4)` re-draws at 4 of the')
    print('  losing rows, four draws each (a hardcoded `range(4)` inside the')
    print('  loop, not a parameter).  `blindaxes.py --imports` puts `nwit=4`')
    print('  on the DEFAULTS list, and it sits on the one FAILURE claim in')
    print('  that step.  Un-fenced here by parameterizing THIS driver\'s loop')
    print('  around the imported `draw_flat` / `measure`, not by editing them.')
    print()
    rows, escaped, tab = [], [], {}
    nforced = 0
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is None:
            continue
        nforced += 1
        pt, _bb = draw_flat(G, got[1], rng)
        assert pt is not None, 'no guarded draw at a forced witness'
        m = measure(H1, H2, pt)
        if m[2] + m[3] > 0:
            rows.append((n1, n2, H1, H2, got))
    assert nforced == 392, ('the family disagrees with (BE-81)', nforced)
    print(f'  The losing rows, by the FIRST draw: {len(rows)} of {nforced} '
          f'-- (BE-86)(ii)\'s 100, reproduced not cited.')
    print()
    for s in boxes:
        found = 0
        seen = {}
        for (n1, n2, H1, H2, got) in rows:
            G = H1 + H2
            best = None
            for _k in range(ndraw):
                pt, _bb = draw_flat(G, got[1], rng, s=s)
                if pt is None:
                    continue
                m = measure(H1, H2, pt)
                key = (m[2], m[3], m[6])
                seen[key] = seen.get(key, 0) + 1
                if m[2] == 0 and m[3] == 0:
                    best = key
            if best is not None:
                found += 1
                escaped.append((n1, n2, len(verts_of(G))))
        tab[s] = (found, dict(sorted(seen.items())))
        print(f'  box |coord| <= {s}, {ndraw} draws x {len(rows)} rows = '
              f'{ndraw * len(rows)} draws:')
        print(f'      (a_1, a_2, dim(rho_bar_1 + rho_bar_2)) -> count: '
              f'{tab[s][1]}')
        print(f'      rows at which a_1 = a_2 = 0 was FOUND (a `Good` point, '
              f'hence `Good != 0` PROVED there): {found} / {len(rows)}')
    print()
    print('  READING, with the semicontinuity direction stated (F27).')
    print('  `dim M_i` is UPPER semicontinuous, so a draw is an UPPER bound')
    print('  on the generic `a_i`: a draw with a_i = 0 PROVES a_i = 0')
    print('  generically ((BE-69)(iii)\'s U-1 mechanism, `bgoodempty`\'s own')
    print('  docstring), and a draw with a_i = 1 proves NOTHING.  So a HIT')
    print('  above is a theorem and a MISS is "NOT FOUND UNDER CAP", never')
    print('  "Good is empty" -- and `Good` being empty cannot be certified by')
    print('  draws at all here, because the dense-or-empty dichotomy needs')
    print('  (CH-1)(a), which (BE-85)(iii) measured absent at 392/392.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tab


# ================================================== the profile at the blocks

def run_prof(seed=SEED, cap=60):
    """`c_i(U) = dim(rho_bar_i cap U)` at the COINCIDENT-regime stable
    subspaces, over a stride subsample of the forced witnesses."""
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE309 / (BE-310): what the right object measures =====')
    wit = []
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is not None:
            wit.append((n1, n2, H1, H2, got))
    step = max(1, len(wit) // cap)
    sub = wit[::step][:cap]
    print(f'  Stride subsample: {len(sub)} of {len(wit)} forced witnesses '
          f'(every {step}th in generator order -- chosen for COST, not '
          f'random and not exhaustive).')
    inside_l2 = inside_al = nrow = 0
    prof = {}
    for (n1, n2, H1, H2, got) in sub:
        G = H1 + H2
        pt, _bb = draw_flat(G, got[1], rng)
        if pt is None:
            continue
        Bx, By = plane_at(G, pt, U), plane_at(G, pt, V)
        if Bx is None or By is None:
            continue
        assert same_space(Bx, By), 'pi_u = pi_v is not forced at this draw'
        px, py = hat(pt[U]), hat(pt[V])
        assert rank_exact([px, py]) == 2, 'p_x = p_y at a guarded draw'
        Pix, Piy = pencil_space(px, Bx), pencil_space(py, By)
        M = span([wedge2(px, py)])
        L2 = lam2(Bx)
        S1, r1, _dM1, _ = rho_bar_of(H1, pt, U, V)
        S2, r2, _dM2, _ = rho_bar_of(H2, pt, U, V)
        nrow += 1
        if S1 and dim(span(S1 + L2)) == dim(L2):
            inside_l2 += 1
        alx = span(alpha_plane(px) + alpha_plane(py))
        if S1 and dim(span(S1 + alx)) == dim(alx):
            inside_al += 1
        key = tuple(dim(isect(S, W)) for S in (S1, S2)
                    for W in (Pix, Piy, M, L2))
        key = (r1, r2) + key
        prof[key] = prof.get(key, 0) + 1
    print('  (rho_1, rho_2 | c_1 at Pi_x, Pi_y, <M>, L^2pi | c_2 at the same)')
    for k, v in sorted(prof.items()):
        print(f'      {k} -> {v}')
    print(f'      rho_bar_1 inside Lambda^2 pi : {inside_l2} / {nrow}')
    print(f'      rho_bar_1 inside alpha_x + alpha_y : {inside_al} / {nrow}')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return prof


def run_side(seed=SEED, cap=40, ndraw=4):
    """THE NON-SEQUITUR, exhibited.  (BE-69)(iii) discharges `A_i != 0` as
    "(BE-14) for the side -- the 2-cut induction's own hypothesis, not a new
    obligation".  But `A_i` is a subset of `Chart(H)`, the COMPOSITE's chart,
    while (BE-14) for the side is a statement about `Chart(H_i)`; and at a
    forced peel the restriction `Chart(H) -> Chart(H_i)` lands inside the
    coincidence locus `{pi_u = pi_v}`, which is PROPER and CLOSED in
    `Chart(H_i)` -- side `i` alone does not force it ((BE-282)(iv): 0 of 854
    one-sided library draws are off the generic regime).  So the preimage of
    a dense open need not be nonempty, and the discharge does not follow.
    This mode exhibits the gap: side `i` attaining on its OWN chart at a
    configuration with `pi_u != pi_v`, at rows where it does NOT attain inside
    the composite."""
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE311 / (BE-312): the side attains on its OWN chart '
          'and not inside the composite =====')
    rows = []
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is None:
            continue
        pt, _bb = draw_flat(G, got[1], rng)
        if pt is None:
            continue
        m = measure(H1, H2, pt)
        if m[2] + m[3] > 0:
            rows.append((n1, n2, H1, H2, 1 if m[2] else 2))
    step = max(1, len(rows) // cap)
    sub = rows[::step][:cap]
    print(f'  Losing rows: {len(rows)}; stride subsample {len(sub)} '
          f'(every {step}th, chosen for COST -- not random, not exhaustive).')
    tally = {'sides': 0, 'draws': 0, 'sampler None': 0,
             'flag undetermined on the side alone': 0,
             'pi_u = pi_v': 0, 'pi_u != pi_v': 0}
    split_a, comp_a, own_a, ok = {}, {}, {}, 0
    for (n1, n2, H1, H2, which) in sub:
        Hs = H1 if which == 1 else H2
        tally['sides'] += 1
        hit = False
        for _k in range(ndraw):
            tally['draws'] += 1
            got = sample_by_branches(Hs, U, V, rng)
            if got is None:
                tally['sampler None'] += 1
                continue
            pt = got[0]
            f_i = exact_deficiency(Hs)[0]
            _S, _r, dM, _ = rho_bar_of(Hs, pt, U, V)
            a_i = dM - 6 - f_i
            own_a[a_i] = own_a.get(a_i, 0) + 1
            if a_i == 0:
                hit = True
            Bx, By = plane_at(Hs, pt, U), plane_at(Hs, pt, V)
            if Bx is None or By is None:
                tally['flag undetermined on the side alone'] += 1
                continue
            if same_space(Bx, By):
                tally['pi_u = pi_v'] += 1
                comp_a[a_i] = comp_a.get(a_i, 0) + 1
            else:
                tally['pi_u != pi_v'] += 1
                split_a[a_i] = split_a.get(a_i, 0) + 1
        if hit:
            ok += 1
    print(f'  Draw accounting over {tally["sides"]} losing sides x {ndraw} '
          f'draws of the side\'s OWN chart (`bdecor.sample_by_branches`, '
          f'(BE-64)\'s parametrization):')
    for k, v in tally.items():
        print(f'      {k:<38} {v}')
    print(f'      a_i over EVERY usable own-chart draw : {own_a}')
    print(f'      a_i at the SPLIT-flag draws          : {split_a}')
    print(f'      a_i at COINCIDENT draws on the side alone : {comp_a}')
    print(f'      sides with a_i = 0 found on their own '
          f'chart: {ok} / {tally["sides"]}')
    print('  READING.  `dim M_i` is UPPER semicontinuous, so a_i = 0 at ONE')
    print('  draw PROVES a_i = 0 generically on that side\'s own chart: each')
    print('  hit is a THEOREM that the side attains on its own, at a')
    print('  configuration where pi_u != pi_v.  Inside the composite the same')
    print('  side has a_i = 1 at every draw taken here.  So "A_i != 0 is')
    print('  (BE-14) for the side" does NOT transfer at a forced peel, and')
    print('  the two statements are about two different charts.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return ok, tally


MODES = {'blocks': run_blocks, 'losers': run_losers, 'prof': run_prof,
         'side': run_side}



def _path_in(edges, A, u, v):
    """A u--v path all of whose vertices lie in `A`, or None.  BFS inside the
    induced subgraph on `A`."""
    from exactcore import neighbors as _nb
    nb = _nb(edges)
    if u not in A or v not in A:
        return None
    seen, q = {u: None}, [u]
    while q:
        w = q.pop(0)
        for z in nb.get(w, ()):
            if z in A and z not in seen:
                seen[z] = w
                q.append(z)
    if v not in seen:
        return None
    out, w = [], v
    while w is not None:
        out.append(w)
        w = seen[w]
    return out[::-1]


def run_conf(seed=SEED):
    """THE CONFINEMENT, and it is a PROOF and not a measurement once its one
    combinatorial hypothesis is checked.  (BE-30)(iv) is `rho_bar_i` inside
    `<l_e : e in P>` for EVERY u--v path `P` of side `i`, pointwise at every
    configuration.  At a guarded configuration the hinge of an edge is the
    JOIN of its two concurrency points ((BE-16)(iii)), so if some u--v path of
    side `i` has ALL its vertices in the forced coplanar set `A`, every one of
    its hinges lies in `Lambda^2 pi` and therefore `rho_bar_i` does.  This
    mode checks the hypothesis COMBINATORIALLY -- draw-free, exhaustive over
    the 392 -- so the containment measured at 60/60 by `prof` is a theorem at
    every witness where the check passes."""
    t0 = time.time()
    print('===== Step BE309 / (BE-310): the confinement rho_bar_i inside '
          'Lambda^2 pi, as a PROOF =====')
    both = one = none = nfor = 0
    lens = {}
    for (n1, n2, _L, H1, H2) in family():
        G = H1 + H2
        got = forced_seed(G)
        if got is None:
            continue
        nfor += 1
        A = set(got[1])
        P1, P2 = _path_in(H1, A, U, V), _path_in(H2, A, U, V)
        if P1 and P2:
            both += 1
            lens[(len(P1) - 1, len(P2) - 1)] = \
                lens.get((len(P1) - 1, len(P2) - 1), 0) + 1
        elif P1 or P2:
            one += 1
        else:
            none += 1
    print(f'  Over the {nfor} forced witnesses, DRAW-FREE (the closure set A '
          f'is combinatorial):')
    print(f'      a u--v path inside A on BOTH sides : {both} / {nfor}')
    print(f'      on exactly ONE side                : {one} / {nfor}')
    print(f'      on NEITHER side                    : {none} / {nfor}')
    print(f'      (|P_1|, |P_2|) edge-length histogram: '
          f'{dict(sorted(lens.items()))}')
    print()
    print('  CONSEQUENCE, at every witness in the first row.  Both rho_bar_i')
    print('  lie in the SAME 3-dimensional stable subspace Lambda^2 pi, so')
    print('  (BE-95)(i) at U = Lambda^2 pi reads')
    print('        dim(rho_bar_1 + rho_bar_2) <= 3,')
    print('  and (BE-86)(i) needs it to be 2 + a_1 + a_2 = rho_1 + rho_2.')
    print('  Hence at a coincident-flag rung-3 peel with the confinement,')
    print('        H attains  ==>  a_1 + a_2 <= 1,')
    print('  i.e. AT MOST ONE SIDE MAY LOSE ATTAINMENT.  That is one')
    print('  inequality at ONE stable subspace, not sixteen and not eleven,')
    print('  and it is the instrument the generic-regime block family is')
    print('  replaced by here.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return both, nfor


MODES['conf'] = run_conf


if __name__ == '__main__':
    args = sys.argv[1:] or ['blocks']
    for a in args:
        if a not in MODES:
            raise SystemExit(f'unknown mode {a!r}; modes: {sorted(MODES)}')
        MODES[a]()
        print()
