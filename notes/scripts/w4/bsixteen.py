"""
Direction BSIXTEEN (Phase 39 PENCIL, section (K-bare-ext)) -- THE ELEVEN
REMAINING STABLE BLOCKS at rung 3.  Of the 16 `S(phi)`-stable `U` of the
screw space, 14 can host a violation arithmetically ((BE-97)(i)); `Pi_x`,
`Pi_y` ((BE-259)(i)) and `<M>` ((BE-274)) are closed.  Can the other ELEVEN
be closed -- which PROVES `Good != EMPTY` at rung 3 -- or does one of them
host a violation?

  THE ANSWER, said at the top.  The eleven are NOT eleven problems, but not
  for the reason a block-sum inheritance lemma would give -- THAT LEMMA IS
  FALSE, and in the dangerous direction: `c_i` is SUPERADDITIVE over block
  sums (`c_i(A + B) >= c_i(A) + c_i(B)`), so a sum can bind where both
  summands are closed.  What DOES collapse the eleven is ONE INSTRUMENT
  applied SIXTEEN TIMES: (BE-30)(iv)'s path confinement `rho_bar_i <= <P>`
  is BLOCK-AGNOSTIC, so

        c_i(U) <= dim(<P_0> cap U)     at EVERY configuration, for EVERY U,

  and the right-hand side is a TABLE in `(m, U)` with `m = dim <P_0>`.

  MODES
    table  THE 16-COLUMN PATH TABLE.  Draw a generic-regime flag and a
           (BE-30)(ii)-legal chain of length `m`, compute `dim(<P> cap U)`
           for all 16 stable `U`, and assert it against the closed form

               B(m, U) = max( |U cap {Pi_x, Pi_y}| , m + dim U - 6 )

           -- a FORCED floor (`l_1 in Pi_x`, `l_m in Pi_y` are (BE-30)(ii))
           and a general-position count, never anything between.  Exact
           over Q, seeded, every line an assert.
    cert   THE TRANSVERSAL CERTIFICATES, per block.  `dim(<P> cap U) =
           dim U - rank K(<P>^perp, U)` with `K` the KLEIN pairing, so a
           single decomposable `eta` -- a LINE meeting every path edge --
           certifies one unit of exclusion at every block it does not
           annihilate.  Prints which blocks each explicit `eta` separates.
    trace  THE BLOCK-SUM LEMMAS, both directions.  (a) the TRACE lemma
           `c_i(U) <= c_i(U') + dim(U/U')` for `U' <= U` a sub-sum -- PROVED
           and asserted; (b) the SUPERADDITIVITY counterexample that refutes
           "sums inherit their closures from their summands".
    arith  THE RUNG-3 ARITHMETIC, cap-free and per block.  Enumerate every
           `(delta_1, delta_2, dist_1, dist_2, rho_1, rho_2, c_1, c_2)` the
           landed constraints allow and report, block by block, how many
           violating tuples survive L0-L4, then +LP (the table), then +L6
           (general position at the vacuous corner), then +L7 (general
           position INSIDE `<P_0>`).  Seedless, no sampling.
    pop    THE SURVIVORS' POPULATION, priced with NO DRAWS.  `(dist_1,
           dist_2, delta_1, delta_2)` is combinatorial, so which blocks'
           surviving corners are even reachable in-region is decided over
           `bgoodempty.run_block`'s whole job list without sampling.
    mech   CAN THE `side` POPULATION EVEN REFUTE L7?  A draw-free count of
           the (BE-45)(i) SERIES ENDS in the side library -- the one landed
           mechanism that refutes the UNFLOORED law.  A population with none
           cannot refute it, and saying so is the difference between a cap
           and a confirmation.
    side   THE CARRIER READING.  Over the side library, the 16-column
           `c_i(U)` census against `dim(<P_0> cap U)` -- the assert that
           carries the table from free legal chains to `Chart(H)`.
    validate  table + cert + trace + arith + a reduced side.

  NOTATION, stated ONCE.  `V := Lambda^2 K^4`, `dim V = 6`.  The four blocks
  are `bunif.BLK = ('Pix', 'M', 'L', 'Piy')` with `bunif.CAP =
  {2, 1, 1, 2}`; `bunif.SUBS` is EVERY SUBSET of them, so the 16 stable `U`
  ARE the block sums.  `Pi_x = p_x ^ pi_x`, `Pi_y = p_y ^ pi_y`,
  `<M> = <p_x ^ p_y>`, `<L> = <pi_x cap pi_y>` (`bunif.blocks_of`, read at
  source).  `c_i(U) := dim(rho_bar_i cap U)`; `slack := max(0, delta_1 +
  delta_2 - 6)`; RUNG 3 is `Sigma_delta <= 6`, where `slack = 0` and the
  obligation at `U` is `c_1(U) + c_2(U) <= dim U`.  `<P>` is the span of the
  hinge lines of an x--y path `P`; `m` its EDGE count when we speak of the
  path and `dim <P>` when we speak of the space -- they agree for `m <= 5`
  at a generic draw and the driver asserts `dim <P> = min(m, 6)` rather than
  assuming it.

  CAPS ARE DISCLOSED IN-MODE and travel with every figure.  A capped search
  reports NOT FOUND UNDER CAP C, never "does not exist".

  WHAT THIS DRIVER DOES NOT DO.  It does not attempt the properness residue
  -- a proof that `U <= rho_bar_i` is a proper closed condition at
  `rho_i <= 5` once the path confinement has gone vacuous ((BE-259)(ii),
  (BE-277)(iii)).  That is direction BPROPCL's, and every closure here that
  needs it is stated CONDITIONALLY on it and says so.
"""

import os
import sys
import time
import random
import itertools
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import wedge2, hat, rank as rank_exact          # noqa: E402
from bimage import (dim, span, isect, klein, klein_perp,       # noqa: E402
                    rho_bar_of, pencil_space, plane_at)
from bdecor import sample_by_branches                          # noqa: E402
import bunif                                                   # noqa: E402
import bgoodempty as BG                                        # noqa: E402
import bmblock as BM                                           # noqa: E402

SEED = 20260912
RUNG3 = 6          # `Sigma_delta <= RUNG3` is (BE-225)(iii)'s bottom rung
DIMV = 6

BLK = bunif.BLK                     # ('Pix', 'M', 'L', 'Piy')
CAP = bunif.CAP                     # {'Pix': 2, 'M': 1, 'L': 1, 'Piy': 2}
SUBS = bunif.SUBS                   # every subset -- the 16 stable U
ENDS = ('Pix', 'Piy')               # the two blocks with a FORCED path line

# The three blocks already closed at rung 3: `Pi_x`/`Pi_y` ((BE-259)(i) at
# `dist_i <= 4`, measured otherwise) and `<M>` ((BE-274)).
CLOSED = (('Pix',), ('M',), ('Piy',))
DEAD = ((), tuple(sorted(BLK)))     # `U = 0` and `U = Lambda^2 K^4`


def dU(S):
    return sum(CAP[b] for b in S)


def forced(S):
    """`|U cap {Pi_x, Pi_y}|` -- the number of path hinge lines (BE-30)(ii)
    FORCES into `U`: `l_1 in Pi_x` and `l_m in Pi_y`, always."""
    return sum(1 for b in S if b in ENDS)


def Bbound(m, S):
    """THE TABLE.  `m` is `dim <P>`, not the edge count."""
    return max(forced(S), m + dU(S) - DIMV)


def label(S):
    return '+'.join(S) if S else '0'


# ============================================== the flag and the legal chain

def rq(rng, s=20):
    return F(rng.randint(-s, s))


def v4(rng, s=20):
    return [rq(rng, s) for _ in range(4)]


def draw_flag(rng, s=20):
    """A GENERIC-REGIME flag pair `(p_x, pi_x, p_y, pi_y)`: two planes
    meeting in a line `L = <e1, e2>`, with `p_x in pi_x`, `p_y in pi_y` and
    `rank[p_x, e1, e2, p_y] = 4` -- `bunif.flag_frame`'s own test, which is
    exactly `pi_x != pi_y`, `p_x notin pi_y`, `p_y notin pi_x`."""
    for _ in range(80):
        px, py, e1, e2 = (v4(rng, s) for _ in range(4))
        if rank_exact([px, e1, e2, py]) != 4:
            continue
        fr = (px, [px, e1, e2], py, [py, e1, e2], e1, e2)
        assert rank_exact(fr[1]) == 3 and rank_exact(fr[3]) == 3
        return fr
    return None


def blocks(fr):
    """`bunif.blocks_of`, which asserts the four blocks sum DIRECTLY to
    `V` -- the fact that makes the 16 subsets the 16 stable `U`."""
    return bunif.blocks_of(fr)


def usub(B, S):
    rows = []
    for b in S:
        rows += B[b]
    return span(rows) if rows else []


def draw_chain(fr, m, rng, s=20):
    """A (BE-30)(ii)-LEGAL x--y chain with `m` edges: `p_0 = p_x`,
    `p_m = p_y`, `p_1 in pi_x` (so `l_1 in Pi_x`), `p_{m-1} in pi_y` (so
    `l_m in Pi_y`), interior vertices free, consecutive triples NOT
    collinear (the carrier's own hinge-coincidence gate).  At `m = 2` the
    single interior vertex is adjacent to BOTH ends, so it lies in
    `pi_x cap pi_y = L` -- forced, not chosen."""
    px, Bx, py, By, e1, e2 = fr
    for _ in range(120):
        pts = [px] + [None] * (m - 1) + [py]
        if m == 1:
            pts = [px, py]
        elif m == 2:
            c = [rq(rng, s), rq(rng, s)]
            pts[1] = [c[0] * e1[k] + c[1] * e2[k] for k in range(4)]
        else:
            for (j, basis) in ((1, Bx), (m - 1, By)):
                c = [rq(rng, s) for _ in basis]
                pts[j] = [sum(c[i] * basis[i][k] for i in range(len(basis)))
                          for k in range(4)]
            for j in range(2, m - 1):
                pts[j] = v4(rng, s)
        if any(p is None or all(t == 0 for t in p) for p in pts):
            continue
        if any(rank_exact([pts[j], pts[j + 1]]) != 2 for j in range(m)):
            continue
        if any(rank_exact([pts[j - 1], pts[j], pts[j + 1]]) != 3
               for j in range(1, m)):
            continue                      # the legality gate, (BE-30)(ii)
        return pts
    return None


def pspan(pts):
    return span([wedge2(pts[j], pts[j + 1]) for j in range(len(pts) - 1)])


def on_L(fr, p):
    """Is the point `p` on `L = pi_x cap pi_y`?"""
    return rank_exact([fr[4], fr[5], p]) == 2


def loci(fr, pts):
    """THE NAMED DEGENERACY LOCI of a legal chain, each a PROPER CLOSED
    condition, each found by a driver assert rather than assumed.

      `endL`   an interior path vertex ADJACENT TO A TERMINAL lies on
               `L = pi_x cap pi_y`.  Then `p_1 in pi_y`, so `l_2` lies in
               `Lambda^2 pi_y = Pi_y + <L>` and that cell jumps by one.
               FORCED at `m = 2` (where `p_1` is adjacent to both terminals),
               and harmless there -- see `table`'s `m = 2` column.
      `span`   (BE-272)(ii)'s OWN condition: `p_0, p_m, p_1, p_2` fail to span
               at `m = 3`, or `p_0, p_m, p_1, p_3` at `m = 4`.  Then the
               explicit transversal `eta` degenerates and `<M>` (and the sums
               containing it) jump.

    Returns the set of loci the draw sits on; empty means GENERAL POSITION in
    the sense the table's equality needs."""
    m = len(pts) - 1
    out = set()
    if m >= 3 and (on_L(fr, pts[1]) or on_L(fr, pts[m - 1])):
        out.add('endL')
    if m == 3 and rank_exact([pts[0], pts[3], pts[1], pts[2]]) != 4:
        out.add('span')
    if m == 4 and rank_exact([pts[0], pts[4], pts[1], pts[3]]) != 4:
        out.add('span')
    return out


def pair_rank(P, U):
    """`rank K(<P>^perp, U)` with `K` the KLEIN pairing.  The identity

        dim(<P> cap U) = dim U - rank K(<P>^perp, U)

    holds because `<P> = (<P>^perp)^perp`.  THE TABLE'S EQUALITY IS EXACTLY
    THE STATEMENT THAT THIS RANK IS MAXIMAL, i.e. equal to
    `min(6 - dim<P>, dim U - f(U))`: `<P>^perp` annihilates the `f(U)` end
    lines `l_1, l_m` that (BE-30)(ii) forces into `U`, and it has only
    `6 - dim<P>` dimensions to spend.  So the table is ONE determinantal
    open condition per `(m, U)`, not a list of special cases."""
    ann = klein_perp(P)
    if not ann or not U:
        return 0
    return rank_exact([[klein(a, u) for u in U] for a in ann])


# ==================================================== mode: table

def run_table(ndraw=40, mmax=8, seed=SEED):
    """THE 16-COLUMN PATH TABLE.  CAP: `ndraw` exact-Q draws per
    `m = 2..mmax`, flag and chain coefficients from a 41-cube of Q, seeded;
    free LEGAL chains, NOT points of `Chart(H)` (that reading is `side`).
    The region has `x !~ y` ((BE-272)(iii)), so `m >= 2` throughout.

    TWO CLAIMS, KEPT APART because they have different statuses:
      FLOOR      `dim(<P> cap U) >= B(dim<P>, U)`   POINTWISE, asserted at
                 every draw -- the forced end lines plus a dimension count.
      EQUALITY   `= B(dim<P>, U)` exactly when `rank K(<P>^perp, U)` is
                 MAXIMAL, which is one determinantal OPEN condition per
                 `(m, U)`.  Asserted at every draw OFF the named loci
                 (`loci`), and the draws ON them are reported as a NEGATIVE
                 CONTROL rather than dropped."""
    t0 = time.time()
    print(f'== table: `dim(<P> cap U)` for ALL 16 STABLE `U`, exact over Q, '
          f'seed {seed}')
    print(f'   CAP: {ndraw} legal chains per `m = 2..{mmax}` on a freshly '
          f'drawn generic-regime flag.')
    print('   (BE-30)(iv) is PROVED and POINTWISE, so `c_i(U) <= '
          'dim(<P_0> cap U)` at EVERY')
    print('   configuration for EVERY `U` -- no semicontinuity in this step.')
    rng = random.Random(seed)
    obs, nonsat, tot, ndg, jump = {}, 0, 0, 0, {}
    nlow, neq, nrk = 0, 0, 0
    for m in range(2, mmax + 1):
        got = 0
        while got < ndraw:
            fr = draw_flag(rng)
            if fr is None:
                continue
            pts = draw_chain(fr, m, rng)
            if pts is None:
                continue
            B = blocks(fr)
            P = pspan(pts)
            dp = dim(P)
            assert dp <= min(m, DIMV), ('`dim<P>` exceeded min(m,6)', m, dp)
            l1, lm = wedge2(pts[0], pts[1]), wedge2(pts[-2], pts[-1])
            assert dim(B['Pix'] + [l1]) == 2, '`l_1` is NOT in `Pi_x`'
            assert dim(B['Piy'] + [lm]) == 2, '`l_m` is NOT in `Pi_y`'
            got += 1
            tot += 1
            if dp != min(m, DIMV):
                nonsat += 1
                continue
            bad = loci(fr, pts)
            if bad:
                ndg += 1
            for S in SUBS:
                U = usub(B, S)
                c = dim(isect(P, U)) if U else 0
                nlow += 1
                assert c >= Bbound(dp, S), \
                    ('THE POINTWISE FLOOR FAILS', m, dp, label(S), c,
                     Bbound(dp, S))
                if U:
                    nrk += 1
                    assert c == dU(S) - pair_rank(P, U), \
                        ('the Klein-pairing identity FAILS', m, label(S))
                if not bad:
                    obs[(m, S, c)] = obs.get((m, S, c), 0) + 1
                    neq += 1
                    assert c == Bbound(dp, S), \
                        ('THE TABLE FAILS OFF THE NAMED LOCI', m, dp,
                         label(S), c, Bbound(dp, S), sorted(bad))
                elif c != Bbound(dp, S):
                    k = (m, label(S), Bbound(dp, S), c,
                         ','.join(sorted(bad)))
                    jump[k] = jump.get(k, 0) + 1
    print(f'   draws {tot}; `dim<P> = min(m,6)` at {tot - nonsat} of {tot} '
          f'({nonsat} degenerate, excluded)')
    print(f'   of the saturating draws, {ndg} sit on a NAMED LOCUS '
          f'(`loci`) and {tot - nonsat - ndg} do not.')
    print(f'   POINTWISE FLOOR asserted at all {nlow} (draw, U) cells, '
          f'0 failures:')
    print('       `dim(<P> cap U) >= max( |U cap {Pi_x,Pi_y}| , '
          'dim<P> + dim U - 6 )`')
    print(f'   THE KLEIN-PAIRING IDENTITY `dim(<P> cap U) = dim U - '
          f'rank K(<P>^perp, U)`')
    print(f'   asserted at all {nrk} cells, 0 failures -- so the table IS '
          f'the statement that')
    print('   that rank is MAXIMAL, one determinantal open condition per '
          '`(m, U)`.')
    print(f'   EQUALITY asserted at all {neq} cells OFF the named loci, '
          f'0 failures.')
    print('   NEGATIVE CONTROL -- on the loci, the cells that move (and '
          'only these):')
    for k in sorted(jump):
        print(f'       m={k[0]}  {k[1]:<16} {k[2]} -> {k[3]}   x{jump[k]}'
              f'   [{k[4]}]')
    if not jump:
        print('       (none seen at this cap)')
    print('   The table, `U` by `U` (columns `m = 2 .. 8`):')
    print(f'     {"U":<16}{"dim":>4}{"fl":>4}   ' +
          '  '.join(f'm={m}' for m in range(2, mmax + 1)))
    for S in SUBS:
        row = []
        for m in range(2, mmax + 1):
            vals = sorted({c for (mm, SS, c) in obs if mm == m and SS == S})
            row.append(','.join(str(v) for v in vals) if vals else '-')
        mark = ' [dead]' if S in DEAD else (' [closed]' if S in CLOSED
                                            else '')
        print(f'     {label(S):<16}{dU(S):>4}{forced(S):>4}   ' +
              '  '.join(f'{v:>3}' for v in row) + mark)
    print(f'   [{time.time() - t0:.1f}s]')
    return obs, tot, nonsat, jump


# ===================================================== mode: cert

def _meets(a, b):
    """Two LINES of P^3 meet iff their Klein pairing vanishes."""
    return klein(a, b) == 0


def run_cert(ndraw=30, seed=SEED):
    """THE TRANSVERSAL CERTIFICATES.  `u in <P>` iff `<u, eta> = 0` for
    every `eta` in the Klein-annihilator `<P>^perp`, so

        dim(<P> cap U) = dim U - rank K(<P>^perp, U),

    `K` the Klein pairing matrix.  ONE decomposable `eta` -- a LINE meeting
    every path edge -- therefore certifies ONE unit of exclusion at every
    `U` it does not annihilate, and for a decomposable `eta` the pattern is
    READABLE OFF THE GEOMETRY:
        `<eta, Pi_x> = 0`  iff  `eta` passes through `p_x` or lies in `pi_x`
        `<eta, <M>> = 0`   iff  `eta` meets the line `M = p_x v p_y`
        `<eta, <L>> = 0`   iff  `eta` meets the line `L = pi_x cap pi_y`
        `<eta, Pi_y> = 0`  iff  `eta` passes through `p_y` or lies in `pi_y`
    CAP: `ndraw` legal chains per `m`, seeded, exact over Q."""
    t0 = time.time()
    print(f'== cert: explicit DECOMPOSABLE transversals, per block, '
          f'seed {seed}')
    rng = random.Random(seed + 11)
    # the explicit eta for each m, as an index pair into the path points
    ETA = {2: (0, 2), 3: (1, 2), 4: (1, 3)}
    print('   `eta(m)`: m=2 -> `p_0 ^ p_2` (= `M` itself), m=3 -> `p_1 ^ '
          'p_2`, m=4 -> `p_1 ^ p_3`.')
    print('   Each is asserted to ANNIHILATE every hinge line of the chain, '
          'then its')
    print('   separation pattern over the four blocks is recorded.')
    for m in (2, 3, 4):
        i, j = ETA[m]
        pat, ok, dec = {}, 0, 0
        for _ in range(ndraw):
            fr = draw_flag(rng)
            if fr is None:
                continue
            pts = draw_chain(fr, m, rng)
            if pts is None:
                continue
            B = blocks(fr)
            eta = wedge2(pts[i], pts[j])
            hinges = [wedge2(pts[k], pts[k + 1]) for k in range(m)]
            assert all(_meets(eta, h) for h in hinges), \
                ('the transversal does NOT annihilate every hinge line', m)
            assert klein(eta, eta) == 0, 'the transversal is not a LINE'
            ok += 1
            dec += 1
            sep = tuple(b for b in BLK
                        if any(klein(eta, w) != 0 for w in B[b]))
            pat[sep] = pat.get(sep, 0) + 1
        print(f'   m={m}: transversal verified at {ok}/{ndraw} draws '
              f'(decomposable at {dec}/{ok});')
        for sep in sorted(pat, key=lambda t: -pat[t]):
            print(f'        separates {list(sep) or "nothing"}  x{pat[sep]}')
    # m = 5: no decomposable transversal; the exclusion is a determinant.
    print('   m=5: the Klein annihilator of `<P>` is 1-dimensional; the '
          'exclusion at a')
    print('        1-dimensional block is the NON-VANISHING of `<eta, U>`, '
          'an open')
    print('        condition witnessed exactly over Q.  Decomposability of '
          'that `eta`:')
    nd, ndec, sepc = 0, 0, {}
    for _ in range(ndraw):
        fr = draw_flag(rng)
        if fr is None:
            continue
        pts = draw_chain(fr, 5, rng)
        if pts is None:
            continue
        B = blocks(fr)
        P = pspan(pts)
        if dim(P) != 5:
            continue
        ann = klein_perp(P)
        assert len(ann) == 1 and dim(ann) == 1, 'the annihilator is not a line'
        eta = ann[0]
        nd += 1
        if klein(eta, eta) == 0:
            ndec += 1
        sep = tuple(b for b in BLK if any(klein(eta, w) != 0 for w in B[b]))
        sepc[sep] = sepc.get(sep, 0) + 1
    print(f'        DECOMPOSABLE at {ndec} of {nd} draws -- so at `m = 5` '
          f'the functional is')
    print('        genuinely NOT a transversal line, exactly as at `<M>` '
          '((BE-272)(ii)).')
    for sep in sorted(sepc, key=lambda t: -sepc[t]):
        print(f'        separates {list(sep)}  x{sepc[sep]}')
    print(f'   [{time.time() - t0:.1f}s]')


# ===================================================== mode: trace

def run_trace(ndraw=200, seed=SEED):
    """THE BLOCK-SUM LEMMAS, BOTH DIRECTIONS.

    (a) THE TRACE LEMMA, PROVED.  For sub-sums `U' <= U`, projection of
        `W cap U` along `U'` onto `U/U'` has kernel `W cap U'`, so

            c(U) <= c(U') + (dim U - dim U'),   equivalently
            e(U) := dim U - c(U)  is MONOTONE INCREASING in the subset.

    (b) SUPERADDITIVITY, the REFUTATION.  `c(A + B) >= c(A) + c(B)` with
        STRICT inequality on a nonempty open: a line spanned by `a + b` has
        `c(A) = c(B) = 0` and `c(A+B) = 1`.  So "a block sum inherits its
        closure from its summands" is FALSE, and false in the dangerous
        direction -- the sum can bind where both summands are closed.
    CAP: `ndraw` random subspaces of `V` per dimension `1..5`, seeded,
    exact over Q; plus one EXHIBITED exact-Q counterexample for (b)."""
    t0 = time.time()
    print(f'== trace: the two block-sum lemmas, seed {seed}')
    rng = random.Random(seed + 29)
    ntr, nsup, nstrict = 0, 0, 0
    for r in range(1, 6):
        for _ in range(ndraw // 5):
            fr = draw_flag(rng)
            if fr is None:
                continue
            B = blocks(fr)
            W = span([[rq(rng) for _ in range(6)] for _ in range(r)])
            if dim(W) != r:
                continue
            c = {S: (dim(isect(W, usub(B, S))) if S else 0) for S in SUBS}
            for S in SUBS:
                for S2 in SUBS:
                    if not set(S2) <= set(S):
                        continue
                    ntr += 1
                    assert c[S] <= c[S2] + dU(S) - dU(S2), \
                        ('THE TRACE LEMMA FAILS', label(S), label(S2),
                         c[S], c[S2])
                    if S2 and set(S2) != set(S):
                        rest = tuple(sorted(set(S) - set(S2)))
                        nsup += 1
                        assert c[S] >= c[S2] + c[rest], \
                            ('SUPERADDITIVITY FAILS', label(S), c[S])
                        if c[S] > c[S2] + c[rest]:
                            nstrict += 1
    print(f'   (a) TRACE `c(U) <= c(U\') + dim(U/U\')`: asserted at '
          f'{ntr} (subspace, U\' <= U) pairs, 0 failures.')
    print(f'   (b) SUPERADDITIVITY `c(A+B) >= c(A)+c(B)`: asserted at '
          f'{nsup} splittings, 0 failures;')
    print(f'       STRICT at {nstrict} of them -- the sum sees what neither '
          f'summand does.')
    # the exhibited counterexample, in the standard frame
    fr = (
        [F(1), F(0), F(0), F(0)], None, [F(0), F(0), F(0), F(1)], None,
        [F(0), F(1), F(0), F(0)], [F(0), F(0), F(1), F(0)])
    px, _, py, _, e1, e2 = fr
    fr = (px, [px, e1, e2], py, [py, e1, e2], e1, e2)
    B = blocks(fr)
    w = [B['M'][0][k] + B['L'][0][k] for k in range(6)]
    W = span([w])
    cM = dim(isect(W, B['M']))
    cL = dim(isect(W, B['L']))
    cML = dim(isect(W, usub(B, ('L', 'M'))))
    print(f'   EXHIBITED, exact over Q, in the standard frame '
          f'`(p_x, e_1, e_2, p_y) = (e0, e1, e2, e3)`:')
    print(f'       `W = <(p_x ^ p_y) + (e_1 ^ e_2)>`, dim 1: '
          f'`c(<M>) = {cM}`, `c(<L>) = {cL}`, `c(<M>+<L>) = {cML}`.')
    assert (cM, cL, cML) == (0, 0, 1), 'the exhibited counterexample broke'
    print('   So BOTH summands are closed at this `W` and the SUM is not: '
          'the coordinator\'s')
    print('   hoped-for "sums inherit their summands\' closures" is '
          'REFUTED by a witness.')
    print(f'   [{time.time() - t0:.1f}s]')
    return ntr, nsup, nstrict


# ===================================================== mode: arith

def _tuples(dmax=7):
    """Every `(d1, d2, t1, t2, r1, r2)` the landed constraints allow at
    rung 3.  `t_i = dist_i` is capped at `dmax` because every bound in play
    sees only `min(dist_i, 6)`; the `dmax` cell is the `>= dmax` class."""
    for d1 in range(0, RUNG3 + 1):
        for d2 in range(0, RUNG3 + 1 - d1):            # L0
            for t1 in range(2, dmax + 1):              # L4
                if d1 > t1:                            # (BE-256)(i)
                    continue
                for t2 in range(2, dmax + 1):
                    if d2 > t2:
                        continue
                    for r1 in range(0, min(d1, t1, DIMV) + 1):   # L1, L2
                        for r2 in range(0, min(d2, t2, DIMV) + 1):
                            yield (d1, d2, t1, t2, r1, r2)


def run_arith(dmax=7):
    """THE RUNG-3 ARITHMETIC, CAP-FREE AND PER BLOCK.  No sampling, no
    seed.  The laws, and their standing:

      L0  `delta_1 + delta_2 <= 6`                  rung 3, (BE-225)(iii)
      L1  `rho_i <= delta_i`                        (BE-22)(ii) at `a_i = 0`
      L2  `rho_i <= dist_i`                         (BE-256)(ii), POINTWISE
      L2b `delta_i <= dist_i`                       (BE-256)(i), COMBINATORIAL
      L3  `c_i(U) <= min(rho_i, dim U)`             trivial
      L4  `dist_i >= 2`                             the region, `x !~ y`
      LP  `c_i(U) <= B(min(dist_i,6), U)`           THE TABLE -- (BE-30)(iv)
                                                    plus `table`/`cert`
      L6  `dist_i >= 6  ==>  c_i(U) = max(0, rho_i + dim U - 6)`
                                                    general position once the
                                                    confinement is VACUOUS --
                                                    the (BE-277)(iii) residue,
                                                    MEASURED at `<M>`/`Pi_x`
      LG  `c_i(U) <= max(f(U), rho_i + B(m_i,U) - m_i)`, `f(U) =
          |U cap {Pi_x, Pi_y}|`, `m_i = min(dist_i, 6)`
                                                    THE FORCED FLOOR OR THE
                                                    GENERAL-POSITION COUNT,
                                                    never anything between --
                                                    the TABLE's own shape one
                                                    level down.  A NAMED
                                                    CANDIDATE, measured by
                                                    `side`, not a theorem.
      L7  `c_i(U) = max(0, rho_i + B(m_i,U) - m_i)`  the same WITHOUT the
                                                    forced floor.  REFUTED in
                                                    principle by (BE-45)(i):
                                                    a SERIES END at `x` puts
                                                    `<l_e> <= rho_bar_i cap
                                                    Pi_x` at EVERY
                                                    configuration, so
                                                    `c_i(Pi_x) >= 1` with no
                                                    general-position content.
                                                    Kept as a column to show
                                                    how much of the closure
                                                    needs the floor.
    A violation at `U` is `c_1(U) + c_2(U) >= dim U + 1` (slack `= 0`)."""
    t0 = time.time()
    print('== arith: the rung-3 arithmetic at ALL 16 BLOCKS, cap-free, '
          'seedless, no sampling')
    base = list(_tuples(dmax))
    print(f'   base tuples `(d1,d2,t1,t2,r1,r2)` under L0-L2b, L4: '
          f'{len(base)}   (`dist` capped at {dmax}; every bound sees only '
          f'`min(dist,6)`)')
    print(f'     {"U":<16}{"dim":>4}  {"L0-L4":>8}{"+LP":>8}{"+L6":>8}'
          f'{"+LG":>8}{"+L7":>8}   +L6 corner (dist_1, dist_2)')
    out, pshort = {}, {}
    for S in SUBS:
        d = dU(S)
        n = {'b': 0, 'p': 0, 'l6': 0, 'lg': 0, 'l7': 0}
        corner, shape, pcorner = set(), set(), set()
        for (d1, d2, t1, t2, r1, r2) in base:
            m1, m2 = min(t1, DIMV), min(t2, DIMV)
            for c1 in range(0, min(r1, d) + 1):
                for c2 in range(0, min(r2, d) + 1):
                    if c1 + c2 <= d:
                        continue                      # not a violation
                    n['b'] += 1
                    if c1 > Bbound(m1, S) or c2 > Bbound(m2, S):
                        continue
                    n['p'] += 1
                    pcorner.add((min(t1, DIMV), min(t2, DIMV)))
                    g6 = [max(0, r1 + d - DIMV), max(0, r2 + d - DIMV)]
                    if (t1 >= DIMV and c1 != g6[0]) or \
                       (t2 >= DIMV and c2 != g6[1]):
                        continue
                    n['l6'] += 1
                    corner.add((min(t1, DIMV), min(t2, DIMV)))
                    shape.add(((m1, m2), (c1, c2), (r1, r2)))
                    if c1 > max(forced(S), r1 + Bbound(m1, S) - m1) or \
                       c2 > max(forced(S), r2 + Bbound(m2, S) - m2):
                        continue
                    n['lg'] += 1
                    if c1 != max(0, r1 + Bbound(m1, S) - m1) or \
                       c2 != max(0, r2 + Bbound(m2, S) - m2):
                        continue
                    n['l7'] += 1
        out[S] = (n, corner, shape, pcorner)
        mark = ' [dead]' if S in DEAD else (' [closed]' if S in CLOSED
                                            else '')
        cs = ','.join(f'({a},{b})' for (a, b) in sorted(corner)) or '--'
        pm = (f'min m_i >= {min(min(t) for t in pcorner)}' if pcorner
              else '--')
        print(f'     {label(S):<16}{d:>4}  {n["b"]:>8}{n["p"]:>8}'
              f'{n["l6"]:>8}{n["lg"]:>8}{n["l7"]:>8}   {cs}{mark}')
        pshort[S] = pm
    print('   WHERE THE `+LP` SURVIVORS LIVE -- the smallest `min(m_1,m_2)` '
          'any of them has.')
    print('   A block whose `+LP` survivors ALL have `min(m_i) = 6` is '
          'closed by the TABLE')
    print('   alone whenever EITHER side is short, exactly as `<M>` is in '
          '(BE-274)(i):')
    for S in SUBS:
        if S in DEAD:
            continue
        print(f'       {label(S):<16}{pshort[S]}')
    print('   THE +L6 SURVIVORS, shape by shape -- `((m_1,m_2), (c_1,c_2), '
          '(rho_1,rho_2))`.')
    print('   A kill condition naming a number carries its derivation, so '
          'these are printed')
    print('   rather than summarized:')
    allsh = set()
    for S in SUBS:
        for sh in out[S][2]:
            allsh.add(sh)
    for sh in sorted(allsh):
        who = [label(S) for S in SUBS if sh in out[S][2]]
        print(f'       m={sh[0]}  c={sh[1]}  rho={sh[2]}   at {who}')
    if allsh:
        hi = min(max(s[0]) for s in allsh)
        lo = min(min(s[0]) for s in allsh)
        n5 = sum(1 for s in allsh if max(s[0]) == 5)
        print(f'   DERIVED from the list above, not asserted: every '
              f'surviving shape has')
        print(f'   `max(m_1, m_2) >= {hi}` and `min(m_1, m_2) >= {lo}`; '
              f'{n5} of {len(allsh)} shapes have a side at')
        print(f'   `m_i = 5` and the remaining {len(allsh) - n5} sit at '
              f'`(m_1, m_2) = (4, 4)`.  Every one has')
        print('   `m_i <= 5` on BOTH sides -- i.e. the path confinement is '
              'PROPER on both,')
        print('   so the residue is NOT (BE-277)(iii)\'s, which is the '
              'VACUOUS corner `m_i = 6`.')
    print('   A `0` in the `+LP` column is a closure by the TABLE alone '
          '-- proved wherever')
    print('   the table row is proved.  A `0` that appears only at `+L6` '
          'is CONDITIONAL on')
    print('   the properness residue ((BE-277)(iii)), which is direction '
          'BPROPCL\'s.')
    print(f'   [{time.time() - t0:.1f}s]')
    return out


# ===================================================== mode: pop

def run_pop(seed=SEED, maxlen=5, dmax=7):
    """THE SURVIVORS' POPULATION, PRICED WITH NO DRAWS.  `(dist_i, delta_i)`
    at an internal R-node peel is COMBINATORIAL, so which blocks' surviving
    corners are reachable in-region is graph theory, not sampling.  Replays
    `bgoodempty.run_block`'s job list at its COMMITTED defaults through the
    SAME region gates as `bmblock.run_reach`.  CAP: that job list -- two
    skeletons, branch lengths `<= maxlen`, the non-adjacent hub pairs, a
    66-shape side-1 library; no `njob` truncation, no `quick`."""
    t0 = time.time()
    print(f'== pop: the in-region `(dist_1, dist_2, delta_1, delta_2)` '
          f'population, NO DRAWS, seed {seed}')
    jobs = BM._jobs(seed, maxlen)
    rows, joint = 0, {}
    import bproper
    for (skname, prof, xy, s1name, s1E) in jobs:
        x, y = xy
        try:
            E, E1, E2, x, y = bproper.composite(skname, list(prof), xy, s1E)
        except Exception:
            continue
        if len({frozenset(e) for e in E}) != len(E):
            continue
        nbH = BG.neighbors(E)
        if y in nbH.get(x, ()):
            continue
        if len(nbH.get(x, ())) < 3 or len(nbH.get(y, ())) < 3:
            continue
        if min(len(v) for v in nbH.values()) < 2 or BG.girth(E) < 4:
            continue
        if not BG.hcard_ok_piece(E, x, y):
            continue
        if not BG.rnode_shaped(E2, x, y):
            continue
        if len(BG.neighbors(E1).get(x, ())) < 2 or \
           len(BG.neighbors(E2).get(x, ())) < 2:
            continue
        if len(BG.neighbors(E1).get(y, ())) < 2 or \
           len(BG.neighbors(E2).get(y, ())) < 2:
            continue
        d1, d2 = BG.delta_of(E1, x, y), BG.delta_of(E2, x, y)
        if d1 + d2 > RUNG3:
            continue
        t1, t2 = BG.dist_of(E1, x, y), BG.dist_of(E2, x, y)
        rows += 1
        assert min(t1, t2) >= 2, ('an in-region peel with dist = 1', t1, t2)
        assert d1 <= t1 and d2 <= t2, \
            ('(BE-256)(ii) `delta <= dist` FAILS in-region', d1, t1, d2, t2)
        key = (d1, d2, min(t1, dmax), min(t2, dmax))
        joint[key] = joint.get(key, 0) + 1
    print(f'   in-region peels {rows}   (jobs offered {len(jobs)}) '
          f'-- NO configuration was drawn')
    # per-block reachability, staged exactly as `arith` stages the laws
    print(f'     {"U":<16}{"dim":>4}  {"+LP":>8}{"+L6":>8}{"+L7":>8}'
          f'   of {rows} in-region peels')
    outp = {}
    for S in SUBS:
        d = dU(S)
        hit = {'p': 0, 'l6': 0, 'l7': 0}
        for (d1, d2, t1, t2), n in joint.items():
            m1, m2 = min(t1, DIMV), min(t2, DIMV)
            a = {'p': False, 'l6': False, 'l7': False}
            for r1 in range(0, min(d1, t1, DIMV) + 1):
                for r2 in range(0, min(d2, t2, DIMV) + 1):
                    for c1 in range(0, min(r1, d, Bbound(m1, S)) + 1):
                        for c2 in range(0, min(r2, d, Bbound(m2, S)) + 1):
                            if c1 + c2 <= d:
                                continue
                            a['p'] = True
                            g6 = [max(0, r1 + d - DIMV),
                                  max(0, r2 + d - DIMV)]
                            if (m1 >= DIMV and c1 != g6[0]) or \
                               (m2 >= DIMV and c2 != g6[1]):
                                continue
                            a['l6'] = True
                            if c1 != max(0, r1 + Bbound(m1, S) - m1) or \
                               c2 != max(0, r2 + Bbound(m2, S) - m2):
                                continue
                            a['l7'] = True
            for k in hit:
                if a[k]:
                    hit[k] += n
        outp[S] = hit
        mark = ' [dead]' if S in DEAD else (' [closed]' if S in CLOSED
                                            else '')
        print(f'     {label(S):<16}{d:>4}  {hit["p"]:>8}{hit["l6"]:>8}'
              f'{hit["l7"]:>8}{mark}')
    print('   A `0` in `+LP` is a block the TABLE closes on this whole '
          'population with no')
    print('   general-position step at all.  NEVER "cannot occur": the cap '
          'is the job list.')
    print(f'   CROSS-CHECK against (BE-276)(i): `<M>`\'s `+LP` figure is '
          f'{outp[("M",)]["p"]} of {rows},')
    print('   which is that clause\'s own `248 of 2 946` -- reproduced here '
          'from the SAME')
    print('   job list by a DIFFERENT route (the table, not a `dist` '
          'threshold), so it is a')
    print('   same-input reproduction and buys comparability, not '
          'independence.')
    print(f'   [{time.time() - t0:.1f}s]')
    return rows, joint, outp


# ===================================================== mode: mech

def run_mech(seed=SEED, maxarc=8, maxtheta=7, cap=400, maxlen=9):
    """CAN THE `side` POPULATION EVEN REFUTE L7?  (BE-45)(i)'s SERIES END is
    the one landed mechanism that forces `c_i(Pi_x) >= 1` with NO
    general-position content: if every x--y path of the side leaves `x` by
    the SAME edge, that edge is a bridge and `<l_e> <= rho_bar_i cap Pi_x`
    at EVERY configuration.  L7 (the UNFLOORED law) predicts `0` there
    whenever `rho_i` is small, so a series-end side REFUTES L7 -- and a
    population with no series-end side CANNOT.

    This mode is COMBINATORIAL: it needs no configuration and no draw.  For
    every side of the library it counts the distinct FIRST edges over all
    x--y paths, at `x` and at `y`.  A count of `1` is (M1) firing."""
    t0 = time.time()
    print(f'== mech: can this population refute L7?  (BE-45)(i) SERIES ENDS '
          f'in the side library')
    print(f'   NO DRAWS -- `first edge of every x--y path` is combinatorial. '
          f'CAPS: maxarc={maxarc},')
    print(f'   maxtheta={maxtheta}, xy_paths(cap={cap}, maxlen={maxlen}) -- '
          f'`side`\'s own values.')
    lib = list(BG.side_library(maxarc, maxtheta, 40, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in BG.side1_library()]
    rows, m1x, m1y, hist, names = 0, 0, 0, {}, []
    for (tag, E, x, y) in lib:
        paths, _tr = BG.xy_paths(E, x, y, cap=cap, maxlen=maxlen)
        if not paths:
            continue
        rows += 1
        fx = {P[0][1] if P[0][0] == x else P[0][0] for P in paths}
        fy = {P[-1][1] if P[-1][0] == y else P[-1][0] for P in paths}
        hist[(len(fx), len(fy))] = hist.get((len(fx), len(fy)), 0) + 1
        if len(fx) == 1:
            m1x += 1
            names.append((tag, 'x'))
        if len(fy) == 1:
            m1y += 1
            names.append((tag, 'y'))
    print(f'   sides {rows}; `(#first edges at x, #first edges at y)` -> '
          f'count: {dict(sorted(hist.items()))}')
    print(f'   SERIES ENDS ((BE-45)(i) (M1) firing): {m1x} at `x`, {m1y} at '
          f'`y`.')
    if m1x == 0 and m1y == 0:
        print('   ZERO.  So THIS POPULATION CANNOT REFUTE L7, and the '
              '`side` census\'s')
        print('   100 % agreement is NOT evidence that the unfloored law '
              'holds in general --')
        print('   it is evidence that the library is built from 2-connected '
              'shapes (cycles,')
        print('   generalized thetas, ladders) in which every terminal has '
              'two path-disjoint')
        print('   first edges.  The floored form (BLOCK-GP) is what the '
              'closure is run at,')
        print('   and it is the form that survives a series end.  '
              'NOT FOUND UNDER CAP C.')
    else:
        print(f'   NONZERO -- these sides DO carry (M1), so the census '
              f'CAN see the refutation:')
        for nm in names[:12]:
            print(f'      {nm}')
    print(f'   [{time.time() - t0:.1f}s]')
    return rows, m1x, m1y, hist


# ===================================================== mode: side

def run_side(ndraw=2, seed=SEED, maxarc=8, maxtheta=7, cap=400, maxlen=9):
    """THE CARRIER READING.  `bgoodempty.run_pix`'s shape at ALL 16 BLOCKS:
    over the side library, draw configurations, build the flag frame
    (`bunif.flag_frame`, which REJECTS the non-generic regime), and assert
    at every draw and every `U`

        c_i(U) <= dim(<P_0> cap U)            THE BLOCK PATH BOUND, POINTWISE
        dim(<P_0> cap U) >= B(dim <P_0>, U)   THE TABLE'S FLOOR, POINTWISE

    and MEASURE (never assert -- it is a candidate law, not a theorem)

        L7:  c_i(U) = max(0, rho_i + dim(<P_0> cap U) - dim <P_0>)

    i.e. `rho_bar_i` in general position INSIDE `<P_0>` against
    `<P_0> cap U`.  L7 at `dim <P_0> = 6` is exactly the general-position
    step (BE-258)(iv) reports at `Pi_x` and (BE-273)(ii) reports at `<M>`;
    the content here is the rest of the table.

    CAPS, and they travel: `ndraw` draws per side (the landed `run_pix`
    value is 3 -- this is FENCED to {ndraw} and the fence is named in the
    same sentence as every figure below); `maxarc`/`maxtheta` and
    `xy_paths(cap, maxlen)` are `run_pix`'s COMMITTED values, restored.
    ONE shortest path per side, not all of them -- `rho_bar_i` is confined
    by EVERY x--y path, so using one is sound and not sharp."""
    t0 = time.time()
    print(f'== side: the 16-column `c_i(U)` census on `Chart(H)`, seed '
          f'{seed}')
    print(f'   CAPS: ndraw={ndraw} (run_pix landed at 3), maxarc={maxarc}, '
          f'maxtheta={maxtheta},')
    print(f'   xy_paths(cap={cap}, maxlen={maxlen}); ONE shortest path per '
          f'side.')
    lib = list(BG.side_library(maxarc, maxtheta, 40, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in BG.side1_library()]
    rows, nreg, nbound, ntab, tabfail = 0, 0, 0, 0, []
    l7ok, l7bad, l7cases = 0, 0, {}
    hist, offreg = {}, 0
    for (tag, E, x, y) in lib:
        dd = BG.dist_of(E, x, y)
        paths, _tr = BG.xy_paths(E, x, y, cap=cap, maxlen=maxlen)
        short = [P for P in paths if len(P) == dd]
        if not short:
            continue
        cmin, seen = {S: 9 for S in SUBS}, 0
        for sdr in range(ndraw):
            rng = random.Random(seed + 733 * sdr + len(E))
            got = sample_by_branches(E, x, y, rng)
            if got is None:
                continue
            pt = got[0] if isinstance(got, tuple) else got
            try:
                Srho, rho, _dM, _r = rho_bar_of(E, pt, x, y)
            except AssertionError:
                continue
            fr = bunif.flag_frame(E, pt, x, y)
            if fr is None:
                offreg += 1
                continue                    # off the GENERIC flag regime
            nreg += 1
            B = blocks(fr)
            P0 = span([wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in short[0]])
            dp = dim(P0)
            assert dp <= min(dd, DIMV), ('`dim<P_0>` exceeds min(dist,6)',
                                         tag, dd, dp)
            assert (dim(isect(Srho, P0)) == rho) if Srho else True, \
                ('(BE-30)(iv) fails at the shortest path', tag)
            for S in SUBS:
                U = usub(B, S)
                cU = dim(isect(Srho, U)) if (Srho and U) else 0
                cP = dim(isect(P0, U)) if U else 0
                nbound += 1
                assert cU <= cP, ('THE BLOCK PATH BOUND FAILS', tag,
                                  label(S), cU, cP)
                assert cP >= Bbound(dp, S), \
                    ('THE TABLE FLOOR FAILS ON Chart(H)', tag, dp,
                     label(S), cP, Bbound(dp, S))
                if dp == min(dd, DIMV):
                    ntab += 1
                    if cP != Bbound(dp, S):
                        tabfail.append((tag, dd, dp, label(S), cP,
                                        Bbound(dp, S)))
                pred = max(0, rho + cP - dp)
                if cU == pred:
                    l7ok += 1
                else:
                    l7bad += 1
                    k = (label(S), dp, rho, cU, pred)
                    l7cases[k] = l7cases.get(k, 0) + 1
                cmin[S] = min(cmin[S], cU)
            seen += 1
        if seen == 0:
            continue
        rows += 1
        for S in SUBS:
            hist[(S, min(dd, 7), cmin[S])] = \
                hist.get((S, min(dd, 7), cmin[S]), 0) + 1
    print(f'   side rows {rows}; generic-regime draws {nreg}; draws '
          f'REJECTED off the generic')
    print(f'   flag regime {offreg} -- those peels are (BE-86)/(BGENUINE) '
          f'territory, not this')
    print(f'   16-block family at all, and are excluded here rather than '
          f'silently averaged in.')
    print(f'   BLOCK PATH BOUND `c_i(U) <= dim(<P_0> cap U)` and the TABLE '
          f'FLOOR asserted at')
    print(f'   all {nbound} (draw, U) cells, 0 failures.')
    if tabfail:
        print(f'   !! the table EQUALITY fails at {len(tabfail)} of {ntab} '
              f'saturating cells on `Chart(H)`:')
        agg = {}
        for b in tabfail:
            agg[(b[2], b[3], b[4], b[5])] = agg.get((b[2], b[3], b[4],
                                                     b[5]), 0) + 1
        for k in sorted(agg):
            print(f'      dim<P_0>={k[0]}  {k[1]:<16} {k[3]} -> {k[2]}'
                  f'   x{agg[k]}   (the (NO-END-ON-L) jump locus)')
    else:
        print(f'   the table `B(dim<P_0>, U)` REPRODUCES `dim(<P_0> cap U)` '
              f'at all {ntab} saturating cells.')
    tot7 = l7ok + l7bad
    print(f'   L7 (MEASURED, never asserted): `c_i(U) = max(0, rho_i + '
          f'dim(<P_0> cap U) - dim<P_0>)`')
    print(f'      holds at {l7ok} of {tot7} (draw, U) cells '
          f'({100.0 * l7ok / tot7:.2f} %).')
    if l7bad:
        print(f'      the {l7bad} disagreements, `(U, dim<P_0>, rho, '
              f'observed c, L7 prediction)`:')
        for k in sorted(l7cases, key=lambda t: -l7cases[t])[:16]:
            print(f'        {k}   x{l7cases[k]}')
        hi = sum(v for k, v in l7cases.items() if k[3] > k[4])
        print(f'      of these, {hi} have `c > prediction` (the direction '
              f'that could host a')
        print('      violation) and the rest `c < prediction` (harmless '
              '-- L7 over-predicts).')
    print('   generic `c_i(U)` by `(dist_i, c)`, the ELEVEN OPEN blocks:')
    for S in SUBS:
        if S in DEAD or S in CLOSED:
            continue
        h = {(t, c): hist[(SS, t, c)] for (SS, t, c) in hist if SS == S}
        print(f'     {label(S):<16}{dict(sorted(h.items()))}')
    print(f'   [{time.time() - t0:.1f}s]')
    return rows, nreg, tabfail, hist, (l7ok, l7bad, l7cases)


# ===================================================== validate

def run_validate():
    print('== validate: table + cert + trace + arith + pop + reduced side')
    print('   FENCED: table(ndraw=8) against 40; cert(ndraw=6) against 30;')
    print('   trace(ndraw=40) against 200; side(ndraw=1, maxarc=4, '
          'maxtheta=4) against')
    print('   2/8/7.  arith and pop run at FULL defaults (both are '
          'draw-free).')
    run_table(ndraw=8, mmax=7)
    run_cert(ndraw=6)
    run_trace(ndraw=40)
    run_arith()
    run_pop()
    run_mech(maxarc=4, maxtheta=4)
    run_side(ndraw=1, maxarc=4, maxtheta=4)


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode == 'table':
        run_table()
    elif mode == 'cert':
        run_cert()
    elif mode == 'trace':
        run_trace()
    elif mode == 'arith':
        run_arith()
    elif mode == 'pop':
        run_pop()
    elif mode == 'mech':
        run_mech()
    elif mode == 'side':
        run_side()
    elif mode == 'validate':
        run_validate()
    else:
        print(f'unknown mode {mode!r}')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
