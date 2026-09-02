"""
Direction BUNIF (ordinal 63) -- IS `reach` UNIFORM OVER THE CLASS?

  THE TARGET the spec names.  BPEEL reduced half (B)'s last residue
  ((BE-67)(iii)) to ONE NUMBER per (piece, peel) ((BE-69)(iii)):

    reach(H; x, y) := max_{A_1 cap A_2} dim(rho_bar_1 + rho_bar_2),

  attained on a dense open, hence GENERIC; and (BE-67)(iii) at H is
  `A_1 cap A_2 != {}` (already free) together with

    reach(H; x, y) = min(delta_1 + delta_2, 6).

  The class statement is that ONE sentence, quantified over every internal
  R-node piece and every peel.

  THE ANSWER, said at the top: `reach` IS COMPUTED FROM PER-SIDE DATA, by a
  law with BOTH DIRECTIONS PROVED -- so the class statement is REDUCED
  (HIT shape 2), not proved and not refuted.

    (BE-94) THE FLAG PAIR HAS A 5-DIMENSIONAL STABILIZER, AND IT ACTS ON
            EACH SIDE SEPARATELY.  S(phi) = Stab_{PGL_4}(p_x, pi_x, p_y,
            pi_y) is 5-dimensional, contains the maximal torus, and by
            (BE-70)(ii) acts on EACH side's achievable family on its own.
            In the generic flag regime Lambda^2 K^4 splits S(phi)-canonically
            as  Pi_x (+) <M> (+) <L> (+) Pi_y  of dims (2, 1, 1, 2), and the
            S(phi)-STABLE subspaces are EXACTLY the 16 sums of those blocks.

    (BE-95) THE BLOCK CAP -- an upper bound on reach, PROVED (modular law),
            one inequality per stable subspace.  It CONTAINS both of
            (BE-71)'s located mechanisms: two-sided (P) is its
            `U = core_1 cap core_2` instance and two-sided (Z) at
            E = Pi_x + Pi_y is its `U = {Pi_x, Pi_y}` instance.

    (BE-96) THE BLOCK LAW -- the cap is ATTAINED, so reach is a function of
            the two PER-SIDE profiles alone.  The matching lower bound is
            proved by degenerating each side independently along a 1-PS of
            S(phi) (lower semicontinuity of dim(V_1 + V_2) makes a limit a
            valid lower bound, and the GL_2 factor separates the two graded
            pieces inside a 2-dimensional block).

    (BE-97) WHICH BLOCK CAN BITE.  The arithmetic kills only the two
            trivial members, so the triage is MEASURED: the violation margin
            is 0 at every row, Pi_x is the ONLY block at which BOTH sides
            exceed the generic profile at once, and the class statement is
            TIGHT there -- it survives by exactly zero margin.  The residue
            is a PER-SIDE question of the (BE-45) kind.

    (BE-98) Jobs 2 and 3, and the board.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `equiv` (BE-94)  S(phi)-equivariance ASSERTED: a constructed stabilizer
            element fixes the flag pair AS SPACES at both terminals, carries
            rho_bar_i to Lambda^2 g . rho_bar_i AS SPACES, and -- moved on
            ONE SIDE ONLY, which is (BE-70)(ii) in group form -- reglues
            through both gates with the other side's rho_bar UNCHANGED.
            The four-block direct sum is asserted at every peel.

  `law`   (BE-95)/(BE-96)  Over the R-battery, the nested piece and a
            subdivided-skeleton tier: blockdeg <= measured <= blockcap
            ASSERTED at every row, `blockdeg == blockcap` counted (that is
            the law PROVED at the row), and the shortfall against
            min(delta_1+delta_2, 6) + a_1 + a_2 reported.

  `bind`  (BE-97)  The triage: the exhaustive arithmetic enumeration of
            conceivable violations per stable U, then the MEASURED violation
            margin (asserted <= 0 at every row), which U comes closest, where
            the margin is exactly 0 at a proper nonempty U, and the per-side
            census of one-side vs BOTH-sides non-generic profiles.

  `abst` (BE-96)  The law's abstract half, off the graphs: for random
            subspace pairs in the standard flag frame, the cap is ATTAINED by
            a group move, and the two bounds bracket it (ASSERTED).

  `coin`  the COINCIDENT flag regime pi_x = pi_y, where the four-block sum
            DEGENERATES (Pi_x + Pi_y = Lambda^2 pi, Pi_x cap Pi_y = <M>, both
            ASSERTED) so (BE-96) is stated for the generic regime ONLY.  The
            CAP survives, and (BE-71)(i)'s two-sided (Z) at Z = Lambda^2 pi is
            EXHIBITED there on (BE-30)(iii)(b)-confined ear pairs.

Succeeds `notes/scripts/w4/bbase.py` (Steps BE88-BE92) and, through the
chain, `bgenuine` / `boneone` / `bspread` / `bpeel` / `bdecor` / `bimage` /
`btwocut` / `binduc` / `bwin` / `kbare_common`, all imported READ-ONLY rather
than reimplemented: no deficiency oracle, no rho_bar, no peel scan, no
sampler and no R-node stand-in is rewritten here.

Conventions inherited verbatim (`notes/scripts/README.md`): exact integer /
rational arithmetic throughout (`fractions.Fraction`, no floating point), the
single rng seed printed below, every cap disclosed WITH ITS DENOMINATOR.

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

from fractions import Fraction as F                                   # noqa: E402
from exactcore import (PL, hat, rank as rank_exact, rref,             # noqa: E402
                       wedge2)
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20) and
# --- BONEONE's (BE-83)(iii) recorded the standing verdict that `w4/` is a
# --- de-facto shared LAYER, not a device chain.  This driver is the
# --- TWENTIETH `kbare/` consumer and takes the chain EIGHTEEN deep
# --- (`... -> boneone -> bgenuine -> bbase -> bunif`).  NO MOVE MADE.
from binduc import split_at_pair                                      # noqa: E402
from bimage import (contains, dim, isect, lam2, pencil_space,         # noqa: E402
                    plane_at, plane_meet, rho_bar_of, same_space,
                    sample_ear_span, sample_flags, span)
from bwin import dehom                                                # noqa: E402
from bdecor import (R_BATTERY, assemble, d3, nested_piece,            # noqa: E402
                    sample_by_branches, weld_d3)
from bpeel import constructed_tier, peel_sides                        # noqa: E402

SEED = 20260902

# ======================================================= the four blocks
# The S(phi)-canonical decomposition of the screw space at a GENERIC-REGIME
# flag pair.  `Pix` = p_x ^ pi_x (the hinge lines at x), `Piy` = p_y ^ pi_y,
# `M` = the Pluecker point of the line p_x v p_y, `L` = that of pi_x cap pi_y.
BLK = ('Pix', 'M', 'L', 'Piy')
CAP = {'Pix': 2, 'M': 1, 'L': 1, 'Piy': 2}
SUBS = [tuple(sorted(s)) for k in range(5)
        for s in itertools.combinations(BLK, k)]

# The block ORDERINGS a one-parameter subgroup of S(phi) can realize.  A
# 1-PS acts with weight w_x on Pi_x, w_y on Pi_y, w_L on <L> and
# w_x + w_y - 2 w_L on <M> -- so only 8 of the 24 orderings occur, and the
# lower bound of (BE-96) quantifies over exactly those.
ACHIEVABLE = sorted({
    tuple(sorted(BLK, key=lambda z: {'Pix': a, 'M': a + b, 'L': 0,
                                     'Piy': b}[z]))
    for a in range(-6, 7) for b in range(-6, 7)
    if len({a, a + b, 0, b}) == 4})


def mat_inv(A):
    n = len(A)
    aug = [list(A[i]) + [F(1) if i == j else F(0) for j in range(n)]
           for i in range(n)]
    R, piv = rref(aug)
    if piv != list(range(n)):
        return None
    return [r[n:] for r in R]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def apply4(g, x):
    return [sum(g[i][j] * x[j] for j in range(4)) for i in range(4)]


def lam2_mat(g):
    """Lambda^2 g on the screw space, in `exactcore.PL` order."""
    cols = []
    for (a, b) in PL:
        cols.append(wedge2([g[i][a] for i in range(4)],
                           [g[i][b] for i in range(4)]))
    return [[cols[k][i] for k in range(6)] for i in range(6)]


def act2(Lg, S):
    return span([[sum(Lg[a][b] * row[b] for b in range(6)) for a in range(6)]
                 for row in S])


def flag_frame(H, pt, x, y):
    """(p_x, pi_x, p_y, pi_y, e_1, e_2) with <e_1, e_2> = pi_x cap pi_y, or
    None off the GENERIC flag regime (pi_x = pi_y, p_x in pi_y, p_y in pi_x
    are all excluded by the rank-4 test)."""
    px, py = hat(pt[x]), hat(pt[y])
    Bx, By = plane_at(H, pt, x), plane_at(H, pt, y)
    if Bx is None or By is None:
        return None
    Lb = plane_meet(Bx, By)
    if Lb is None or len(Lb) != 2:
        return None
    if rank_exact([px, Lb[0], Lb[1], py]) != 4:
        return None
    return px, Bx, py, By, Lb[0], Lb[1]


def blocks_of(fr):
    px, Bx, py, By, e1, e2 = fr
    B = {'Pix': pencil_space(px, Bx), 'Piy': pencil_space(py, By),
         'M': [wedge2(px, py)], 'L': [wedge2(e1, e2)]}
    assert dim(B['Pix'] + B['Piy'] + B['M'] + B['L']) == 6, \
        'the four blocks do not sum DIRECTLY to the screw space'
    return B


def stab_elt(fr, rng, s=5):
    """A random element of S(phi): diag(lambda, A, mu) in the frame
    (p_x, e_1, e_2, p_y), A in GL_2.  Five parameters modulo scalars."""
    px, _Bx, py, _By, e1, e2 = fr
    T = [[c[i] for c in (px, e1, e2, py)] for i in range(4)]   # columns
    Ti = mat_inv(T)
    if Ti is None:
        return None
    A = [[F(rng.randint(-s, s)) for _ in range(2)] for _ in range(2)]
    if A[0][0] * A[1][1] - A[0][1] * A[1][0] == 0:
        return None
    D = [[F(0)] * 4 for _ in range(4)]
    D[0][0] = F(rng.randint(1, s))
    D[3][3] = F(rng.randint(1, s))
    D[1][1], D[1][2], D[2][1], D[2][2] = A[0][0], A[0][1], A[1][0], A[1][1]
    return matmul(matmul(T, D), Ti)


def profile(S, B):
    """c(U) = dim(rho_bar cap U) for each of the 16 S(phi)-stable U."""
    c = {}
    for sub in SUBS:
        rows = []
        for b in sub:
            rows += B[b]
        U = span(rows)
        c[sub] = dim(isect(S, U)) if (S and U) else 0
    return c


def blockcap(c1, c2, r1, r2):
    """(BE-95): the PROVED upper bound on dim(rho_bar_1 + rho_bar_2), with
    the stable subspace that binds it."""
    best, arg = 99, None
    for sub in SUBS:
        du = sum(CAP[b] for b in sub)
        val = r1 + r2 - max(0, c1[sub] + c2[sub] - du)
        if val < best:
            best, arg = val, sub
    return best, arg


def graded(c, r, order):
    """Block dimensions of the associated graded of a subspace with profile
    `c` under the 1-PS whose weight order is `order` (increasing)."""
    out, prev = {}, 0
    for j in range(3, -1, -1):
        cj = c[tuple(sorted(order[j:]))]
        out[order[j]] = cj - prev
        prev = cj
    assert sum(out.values()) == r, ('graded does not exhaust', out, r)
    return out


def blockdeg(c1, c2, r1, r2):
    """(BE-96): the PROVED lower bound on reach -- degenerate each side
    independently along a 1-PS of S(phi) and add block by block."""
    best, arg = -1, None
    for s in ACHIEVABLE:
        b1 = graded(c1, r1, s)
        for t in ACHIEVABLE:
            b2 = graded(c2, r2, t)
            val = sum(min(b1[b] + b2[b], CAP[b]) for b in BLK)
            if val > best:
                best, arg = val, (s, t)
    return best, arg


def generic_c(r, du):
    """dim(V cap U) for a GENERIC r-dimensional V and a du-dimensional U."""
    return max(0, r + du - 6)


# ================================================= the peel population

def battery_peels():
    """Population A: BDECOR's seven constructed R-node pieces plus BPEEL's
    nested two-level piece -- the population (BE-67)(i)'s 28/28 and
    (BE-69)(iii)'s 16/16 were measured on."""
    return R_BATTERY() + [('nested [K4-piece in a K4 piece]', nested_piece())]


def battery_rows(rng, ndraw):
    for nm, pc in battery_peels():
        H, u, v = pc['H'], pc['u'], pc['v']
        drawn = 0
        for _ in range(ndraw * 10):
            if drawn == ndraw:
                break
            got = sample_by_branches(H, u, v, rng)
            if got is None:
                continue
            drawn += 1
            pt = got[0]
            for i, (_x0, _y0, _ce, kind0) in enumerate(pc['children']):
                if kind0 == 'leaf':
                    continue
                x, y, side1, side2, kind = peel_sides(pc, i)
                yield (nm, H, pt, x, y, side1, side2, kind)


def tier_rows(rng, njobs, maxlen=3):
    """Population B: subdivided 3-connected skeletons (BPEEL's constructed
    tier), restricted to peels its own R-node stand-in accepts."""
    seen, n = set(), 0
    for (tag, E, x, y, d1, d2, forced, rn) in constructed_tier(
            maxlen=maxlen, nsamp=60, seed=SEED):
        if n >= njobs:
            return
        if not rn or min(d1, d2) == 0:
            continue
        key = (tag, x, y)
        if key in seen:
            continue
        seen.add(key)
        got = sample_by_branches(E, x, y, rng)
        if got is None:
            continue
        pt = got[0]
        sp = split_at_pair(E, x, y)
        if sp is None:
            continue
        _V1, E1, _V2, E2 = sp
        n += 1
        yield (tag, E, pt, x, y, E1, E2, 'tier')


def measure_row(H, pt, x, y, side1, side2):
    """(profile_1, profile_2, r_1, r_2, delta_1, delta_2, a_1, a_2, measured
    dim(rho_bar_1 + rho_bar_2)), or None off the generic flag regime."""
    fr = flag_frame(H, pt, x, y)
    if fr is None:
        return None
    B = blocks_of(fr)
    S1, r1, dM1, _ = rho_bar_of(side1, pt, x, y)
    S2, r2, dM2, _ = rho_bar_of(side2, pt, x, y)
    f1, g1 = d3(side1), weld_d3(side1, x, y)
    f2, g2 = d3(side2), weld_d3(side2, x, y)
    return (profile(S1, B), profile(S2, B), r1, r2, f1 - g1, f2 - g2,
            dM1 - 6 - f1, dM2 - 6 - f2, dim(S1 + S2), B, S1, S2, fr)


# ============================================== mode: equiv  ((BE-94))

def run_equiv(seed=SEED, ndraw=2):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== equiv: (BE-94) THE FLAG PAIR\'S STABILIZER ACTS ON EACH SIDE '
          f'SEPARATELY, seed {seed}')
    print('  S(phi) = Stab_{PGL_4}(p_x, pi_x, p_y, pi_y) = diag(lambda, A, mu)')
    print('  in the frame (p_x, e_1, e_2, p_y), A in GL_2 on L = pi_x cap pi_y')
    print('  -- FIVE parameters modulo scalars, and it contains the maximal')
    print('  torus.  Asserted at every row: the four blocks sum DIRECTLY to')
    print('  the screw space; g fixes BOTH flags AS SPACES; rho_bar_i goes to')
    print('  Lambda^2 g . rho_bar_i AS SPACES; and -- the (BE-70)(ii) claim in')
    print('  group form -- g applied to ONE SIDE ONLY reglues through both')
    print('  gates, moving that side\'s rho_bar and leaving the other\'s fixed.')
    nrow = nboth = nside = ndeg = 0
    for (nm, H, pt, x, y, side1, side2, kind) in battery_rows(rng, ndraw):
        fr = flag_frame(H, pt, x, y)
        if fr is None:
            ndeg += 1
            continue
        blocks_of(fr)                       # asserts the direct sum
        g = stab_elt(fr, rng)
        if g is None:
            continue
        Lg = lam2_mat(g)
        newpt, ok = {}, True
        for w, cxy in pt.items():
            z = apply4(g, hat(cxy))
            if z[3] == 0:
                ok = False
                break
            newpt[w] = tuple(dehom(z))
        if not ok:
            continue
        nrow += 1
        px, Bx, py, By, _e1, _e2 = fr
        assert same_space([hat(newpt[x])], [px]), 'g moved p_x'
        assert same_space([hat(newpt[y])], [py]), 'g moved p_y'
        assert same_space(plane_at(H, newpt, x), Bx), 'g moved pi_x'
        assert same_space(plane_at(H, newpt, y), By), 'g moved pi_y'
        for side in (side1, side2):
            S, _r, _dM, _ = rho_bar_of(side, pt, x, y)
            Sn, _rn, _dMn, _ = rho_bar_of(side, newpt, x, y)
            assert same_space(Sn, act2(Lg, S)), \
                'rho_bar is not Lambda^2 g-equivariant'
        nboth += 1
        # --- the ONE-SIDED move: g on side 1's interior only.
        V1 = {w for e in side1 for w in e} - {x, y}
        mixed = {w: (newpt[w] if w in V1 else pt[w]) for w in pt}
        aff = assemble(H, {w: hat(c) for w, c in mixed.items()})
        if aff is None:
            continue
        S1, r1, _d, _ = rho_bar_of(side1, pt, x, y)
        S2, r2, _d, _ = rho_bar_of(side2, pt, x, y)
        M1, _r, _d, _ = rho_bar_of(side1, aff, x, y)
        M2, _r, _d, _ = rho_bar_of(side2, aff, x, y)
        assert same_space(M1, act2(Lg, S1)), 'the moved side did not transport'
        assert same_space(M2, S2), 'the UNMOVED side moved'
        nside += 1
    print(f'  rows {nrow}: flag FIXED and rho_bar EQUIVARIANT on both sides '
          f'at {nboth}/{nrow}')
    print(f'  the ONE-SIDED regluing (both gates) succeeded at {nside}/{nrow}'
          f'  -- (BE-70)(ii) in group form')
    print(f'  rows OFF the generic flag regime (pi_x = pi_y or a terminal on '
          f'the other plane): {ndeg}')
    print(f'  equiv: {time.time() - t0:.1f}s')
    return nboth == nrow


# ========================================= modes: law  ((BE-95)/(BE-96))

def run_law(seed=SEED, ndraw=2, njobs=90):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== law: (BE-95) THE BLOCK CAP and (BE-96) THE BLOCK LAW, '
          f'seed {seed}')
    print('  cap  (PROVED, modular law):   dim(rho_1+rho_2) <= min over the 16')
    print('        S(phi)-stable U of  r_1 + r_2 - max(0, c_1(U)+c_2(U)-dim U)')
    print('  deg  (PROVED, degeneration):  reach >= max over the 8 realizable')
    print('        1-PS orderings of  sum_b min(beta_b^1 + beta_b^2, cap_b)')
    print('  Where cap == deg the row\'s reach is PINNED BY TWO PROOFS, and')
    print('  (BE-71)(ii)\'s open completeness question is CLOSED at that row.')
    tot = pinned = short = nbind = 0
    per = {}
    for label, gen in (('A [R-battery + nested]', battery_rows(rng, ndraw)),
                       ('B [subdivided skeletons]', tier_rows(rng, njobs))):
        n = p = s = b = 0
        for (nm, H, pt, x, y, side1, side2, kind) in gen:
            got = measure_row(H, pt, x, y, side1, side2)
            if got is None:
                continue
            (c1, c2, r1, r2, d1, d2, a1, a2, meas, B, S1, S2, fr) = got
            cap, carg = blockcap(c1, c2, r1, r2)
            deg, _darg = blockdeg(c1, c2, r1, r2)
            assert deg <= meas <= cap, \
                ('the block bounds bracket nothing', nm, (x, y), deg, meas,
                 cap)
            n += 1
            if cap == deg:
                p += 1
            else:
                print(f'  cap > deg  {nm} peel {(x, y)}  d=({d1},{d2}) '
                      f'r=({r1},{r2}) meas {meas} in [deg {deg}, cap {cap}] '
                      f'-- the DEGENERATION bound is not sharp here; the row '
                      f'is settled by the measured value, not by the law')
            if len(carg) < 4:
                b += 1
            if meas != min(d1 + d2, 6) + a1 + a2:
                s += 1
                print(f'  SHORTFALL  {nm} peel {(x, y)}  d=({d1},{d2}) '
                      f'r=({r1},{r2}) a=({a1},{a2}) meas {meas} '
                      f'target {min(d1 + d2, 6) + a1 + a2}  binding U {carg}')
        per[label] = (n, p, s, b)
        tot += n
        pinned += p
        short += s
        nbind += b
        print(f'  {label:26s} rows {n:4d}   cap == deg (law PROVED at the '
              f'row) {p:4d}   binding U PROPER {b:4d}   shortfall {s}')
    print(f'  TOTAL rows {tot}, cap == deg at {pinned}, shortfall at {short}.')
    print('  A PROPER binding U means the cap is doing work no dimension')
    print('  count does: the row is NOT in general position, and reach is')
    print('  still exactly what the two per-side profiles say.')
    print(f'  law: {time.time() - t0:.1f}s')
    return short == 0


# ============================================== mode: bind  ((BE-97))

def never_bites(sub):
    """Can `sub` host an arithmetically-conceivable violation at all?
    Enumerates every (delta_1, delta_2, c_1, c_2) the caps allow."""
    du = sum(CAP[b] for b in sub)
    hits = []
    for d1 in range(7):
        for d2 in range(7):
            slack = max(0, d1 + d2 - 6)
            for c1 in range(min(du, d1) + 1):
                for c2 in range(min(du, d2) + 1):
                    if c1 + c2 > du + slack:
                        hits.append((d1, d2, c1, c2))
    return hits


def run_bind(seed=SEED, ndraw=2, njobs=60):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== bind: (BE-97) WHICH BLOCK CAN BITE, seed {seed}')
    print('  A VIOLATION at U is  c_1(U) + c_2(U) > dim U + max(0, d_1+d_2-6),')
    print('  and by the CAP a violation IS a shortfall -- a theorem, not')
    print('  evidence.  So the class statement is exactly: no peel has one.')
    print('  Pass 1, the ARITHMETIC alone, over every (d_1,d_2,c_1,c_2) the')
    print('  block caps and rho_i <= delta_i allow:')
    live = {}
    for sub in SUBS:
        hits = never_bites(sub)
        live[sub] = hits
        du = sum(CAP[b] for b in sub)
        tag = 'NEVER BITES' if not hits else f'{len(hits):3d} conceivable'
        print(f'    U = {str(sub):30s} dim {du}   {tag}')
    dead = [s for s in SUBS if not live[s]]
    print(f'  Only {len(dead)} of the 16 die on arithmetic alone '
          f'({[s for s in dead]}) -- the empty subspace and the whole screw')
    print('  space.  So the arithmetic does NOT triage the list, and the')
    print('  earlier reading that Pi_x could not bite was WRONG: it rested on')
    print('  (BE-38)(iii)\'s MEASURED "never 2 below rho = 6", which is not a')
    print('  theorem.  What (BE-44)(ii) DOES prove is a per-side structural')
    print('  price: c_i(Pi_x) = 2 forces EVERY x-y path of side i to span 6.')
    print('  Pass 2, MEASURED: the violation MARGIN')
    print('    margin(row) := max over the 16 U of')
    print('                   c_1(U) + c_2(U) - dim U - max(0, d_1+d_2-6),')
    print('  which is > 0 exactly at a shortfall.  Reported as a histogram,')
    print('  with the U that comes closest named.')
    hist, closest, tight, nrow = {}, {}, {}, 0
    cmax = {'Pix': 0, 'Piy': 0}
    cl2 = [0, 0]
    exc_both = {sub: 0 for sub in SUBS}
    exc_one = {sub: 0 for sub in SUBS}
    for label, gen in (('A', battery_rows(rng, ndraw)),
                       ('B', tier_rows(rng, njobs))):
        for (nm, H, pt, x, y, side1, side2, kind) in gen:
            got = measure_row(H, pt, x, y, side1, side2)
            if got is None:
                continue
            (c1, c2, r1, r2, d1, d2, a1, a2, meas, B, S1, S2, fr) = got
            nrow += 1
            slack = max(0, d1 + d2 - 6)
            best, barg = -99, None
            for sub in SUBS:
                du = sum(CAP[b] for b in sub)
                m = c1[sub] + c2[sub] - du - slack
                if m > best:
                    best, barg = m, sub
                n1 = c1[sub] > generic_c(r1, du)
                n2 = c2[sub] > generic_c(r2, du)
                if n1 and n2:
                    exc_both[sub] += 1
                elif n1 or n2:
                    exc_one[sub] += 1
            hist[best] = hist.get(best, 0) + 1
            closest[barg] = closest.get(barg, 0) + 1
            for sub in SUBS:
                if 0 < len(sub) < 4 and \
                        c1[sub] + c2[sub] - sum(CAP[b] for b in sub) \
                        - slack == 0:
                    tight[sub] = tight.get(sub, 0) + 1
            cmax['Pix'] = max(cmax['Pix'], c1[('Pix',)], c2[('Pix',)])
            cmax['Piy'] = max(cmax['Piy'], c1[('Piy',)], c2[('Piy',)])
            for (c, r) in ((c1, r1), (c2, r2)):
                for blk in (('Pix',), ('Piy',)):
                    if c[blk] == 2:
                        cl2[0] += 1
                        if r < 6:
                            cl2[1] += 1
            assert best <= 0, ('A VIOLATION -- this is a SHORTFALL', nm,
                               (x, y), barg, best)
    print(f'  rows {nrow}; margin histogram '
          f'{sorted(hist.items(), reverse=True)}')
    print('  margin <= 0 ASSERTED at every row, so 0 shortfalls.  The U that')
    print('  comes closest, per row:')
    for sub, k in sorted(closest.items(), key=lambda t: -t[1]):
        print(f'    U = {str(sub):30s} closest at {k:4d} rows')
    print('  the rows where the margin is exactly 0 at a PROPER NONEMPTY U --')
    print('  i.e. the class statement survives there by ZERO margin:')
    for sub, k in sorted(tight.items(), key=lambda t: -t[1]):
        print(f'    U = {str(sub):30s} TIGHT at {k:4d} rows')
    print(f'  largest per-side c_i(Pi_x) seen: {cmax["Pix"]}; '
          f'c_i(Pi_y): {cmax["Piy"]}  (the cap is 2, and c_i = 2 is what')
    print('  (BE-44)(ii) prices at "every x-y path of side i spans 6")')
    print('  and the per-side census -- how often ONE side, and how often')
    print('  BOTH sides at once, exceed the generic profile at the same U:')
    for sub in SUBS:
        if exc_one[sub] or exc_both[sub]:
            print(f'    U = {str(sub):30s} one side {exc_one[sub]:4d}   '
                  f'BOTH sides {exc_both[sub]:4d}')
    print(f'  JOB 2, the standing inventory verdict, run on this section\'s')
    print(f'  OWN citation: (BE-38)(iii)\'s third clause -- "never 2 below')
    print(f'  rho_1 = 6" -- is a MEASUREMENT over 37 pieces that (BE-45)(iii)')
    print(f'  records as STANDING, and the c_i(Pi) = 2 rows are where it')
    print(f'  could break.  Sides with c_i(Pi) = 2: {cl2[0]}; of those with')
    print(f'  rho_i < 6 (which would REFUTE the clause): {cl2[1]}.')
    print('  THE RESIDUE, as a per-side question -- the shape (BE-22)(vi)')
    print('  asked its successor for: for each of the 14 live U, exhibit a')
    print('  peel whose TWO sides are simultaneously non-generic at that U by')
    print('  enough to break the block cap, or prove none exists.  That is a')
    print('  question about ONE side and its profile at a time, and (BE-45)')
    print('  is the answered instance of it at U = Pi_x.')
    print(f'  bind: {time.time() - t0:.1f}s')
    return True


# ================================================ mode: abst  ((BE-96))

E4 = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]
BSTD = {'Pix': [wedge2(E4[0], E4[1]), wedge2(E4[0], E4[2])],
        'Piy': [wedge2(E4[1], E4[3]), wedge2(E4[2], E4[3])],
        'M': [wedge2(E4[0], E4[3])], 'L': [wedge2(E4[1], E4[2])]}
IDX = {'Pix': [0, 1], 'M': [2], 'L': [3], 'Piy': [4, 5]}


def rand_sub(rng, d, mode, s=6):
    """A random d-dimensional subspace of the screw space: `generic`, or
    `adapted` to the four blocks, or `confined` to one stable subspace."""
    for _ in range(200):
        if mode == 'generic':
            rows = [[F(rng.randint(-s, s)) for _ in range(6)]
                    for _ in range(d)]
        elif mode == 'adapted':
            rows, need, pick = [], d, []
            for k, b in enumerate(BLK):
                rest = sum(CAP[z] for z in BLK[k + 1:])
                t = rng.randint(max(0, need - rest), min(CAP[b], need))
                pick.append(t)
                need -= t
            for k, b in enumerate(BLK):
                for _ in range(pick[k]):
                    r = [F(0)] * 6
                    for i in IDX[b]:
                        r[i] = F(rng.randint(-s, s))
                    rows.append(r)
        else:
            sub = SUBS[rng.randrange(len(SUBS))]
            idx = [i for b in sub for i in IDX[b]]
            if len(idx) < d:
                continue
            rows = []
            for _ in range(d):
                r = [F(0)] * 6
                for i in idx:
                    r[i] = F(rng.randint(-s, s))
                rows.append(r)
        S = span(rows)
        if dim(S) == d:
            return S
    return None


def run_abst(seed=SEED, ntrial=400, ngrp=60):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== abst: (BE-96) IS THE CAP ATTAINED IN GENERAL, seed {seed}')
    print('  The peel measurement can only report the pairs the pieces')
    print('  happen to realize.  This mode drops the graphs entirely and')
    print('  asks the ABSTRACT question the law rests on: for two subspaces')
    print('  of the screw space in the standard flag frame, is')
    print('     max over g in S(phi) of dim(V_1 + g V_2)  =  the block CAP?')
    print('  (S(phi)-stability makes both profiles g-invariant, so both')
    print('  bounds are constants of the orbit -- ASSERTED per group draw.)')
    n = nul = nmax = 0
    for _ in range(ntrial):
        d1, d2 = rng.randint(1, 5), rng.randint(1, 5)
        V1 = rand_sub(rng, d1, rng.choice(['generic', 'adapted', 'confined']))
        V2 = rand_sub(rng, d2, rng.choice(['generic', 'adapted', 'confined']))
        if V1 is None or V2 is None:
            continue
        c1, c2 = profile(V1, BSTD), profile(V2, BSTD)
        cap, _ca = blockcap(c1, c2, d1, d2)
        deg, _da = blockdeg(c1, c2, d1, d2)
        best = dim(V1 + V2)
        for _ in range(ngrp):
            g = stab_elt((E4[0], [E4[0], E4[1], E4[2]], E4[3],
                          [E4[1], E4[2], E4[3]], E4[1], E4[2]), rng)
            if g is None:
                continue
            gV2 = act2(lam2_mat(g), V2)
            assert profile(gV2, BSTD) == c2, \
                'the profile is not S(phi)-invariant'
            best = max(best, dim(V1 + gV2))
        n += 1
        assert deg <= best <= cap, ('the block bounds bracket nothing',
                                    d1, d2, deg, best, cap)
        if cap == deg:
            nul += 1
        if best == cap:
            nmax += 1
    print(f'  {n} random pairs: cap ATTAINED by a group move at {nmax}/{n};')
    print(f'  the degeneration bound already equals the cap at {nul}/{n}.')
    print('  CAP DISCLOSED: the group sweep is 60 draws per pair, so')
    print(f'  "attained" is a WITNESS ({nmax} of them) and "not attained"')
    print('  would be a none-found, not a proof.  The bracket deg <= best <=')
    print('  cap is ASSERTED, and it is the half that carries a proof.')
    print(f'  abst: {time.time() - t0:.1f}s')
    return nmax == n


# ================================================= mode: coin (the regime)

def run_coin(seed=SEED, nflag=12):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== coin: THE COINCIDENT REGIME pi_x = pi_y, seed {seed}')
    print('  (BE-94)-(BE-96) are stated for the GENERIC flag regime, and this')
    print('  mode is the disclosure of what happens outside it.  At')
    print('  pi_x = pi_y = pi the four-block sum DEGENERATES: <L> is no longer')
    print('  a line of the screw space, Pi_x and Pi_y both sit INSIDE')
    print('  Lambda^2 pi, and they MEET in <M>.  ASSERTED at every flag draw:')
    print('    Pi_x + Pi_y = Lambda^2 pi (dim 3)   and   Pi_x cap Pi_y = <M>.')
    print('  So the four blocks span 3, not 6, and no direct sum survives --')
    print('  which is why the ATTAINMENT half of the law is stated for the')
    print('  generic regime only (S(phi) is 8-dimensional there and its')
    print('  stable subspaces do not form a direct sum).')
    print('  The CAP survives, because it is the modular law and needs no')
    print('  decomposition.  Exhibited here at Z = Lambda^2 pi, which is')
    print('  exactly (BE-71)(i)\'s TWO-SIDED (Z) at dim 3, using (BE-30)(iii)')
    print('  (b)\'s own confinement: two ears of length <= 3 at coincident')
    print('  flags are BOTH confined to Lambda^2 pi.')
    ndeg = ncap = nbite = 0
    for _ in range(nflag):
        flags = sample_flags(rng, 'equal')
        px, Bx, py, By = flags
        assert same_space(Bx, By), 'the equal regime did not produce pi_x = pi_y'
        Pix, Piy, Mv, Lp = (pencil_space(px, Bx), pencil_space(py, By),
                            [wedge2(px, py)], lam2(Bx))
        assert same_space(Pix + Piy, Lp), \
            'Pi_x + Pi_y is not Lambda^2 pi in the coincident regime'
        assert same_space(isect(Pix, Piy), Mv), \
            'Pi_x cap Pi_y is not <M> in the coincident regime'
        ndeg += 1
        for (m1, m2) in ((2, 2), (2, 3), (3, 3), (3, 5), (5, 5)):
            _p1, _l1, V1 = sample_ear_span(flags, m1, rng)
            _p2, _l2, V2 = sample_ear_span(flags, m2, rng)
            if not V1 or not V2:
                continue
            r1, r2 = dim(V1), dim(V2)
            meas = dim(V1 + V2)
            worst, warg = 6, ('(none)', 6, 0, 0)
            for k, U in (('Pi_x', Pix), ('Pi_y', Piy), ('<M>', Mv),
                         ('Lam2 pi', Lp)):
                du = dim(U)
                c1 = dim(isect(V1, U)) if V1 else 0
                c2 = dim(isect(V2, U)) if V2 else 0
                val = min(6, r1 + r2 - max(0, c1 + c2 - du))
                if val < worst:
                    worst, warg = val, (k, du, c1, c2)
            assert meas <= worst, \
                ('the cap FAILS in the coincident regime', m1, m2, meas,
                 worst, warg)
            ncap += 1
            if meas < min(r1 + r2, 6):
                nbite += 1
                if nbite <= 5:
                    print(f'    ears (m1,m2) = ({m1},{m2}): r = ({r1},{r2}), '
                          f'dim(V_1+V_2) = {meas} < min(r_1+r_2, 6) = '
                          f'{min(r1 + r2, 6)}   binding {warg}')
    print(f'  {ndeg} coincident flag draws, degeneration ASSERTED at every '
          f'one;')
    print(f'  {ncap} ear pairs with the CAP asserted, 0 failures, of which '
          f'{nbite} lose')
    print('  dimension outright -- the two-sided (Z) mechanism, EXHIBITED.')
    print('  What this does NOT do: it does not reach a FORCED coincidence.')
    print('  CAP DISCLOSED -- the coincidence here is CONSTRUCTED (a')
    print('  `bimage.sample_flags(.., "equal")` draw), and BGENUINE (BE-85)(i)')
    print('  records that the branch sampler cannot draw a forced witness\'s')
    print('  chart at all.  The forced family is BGENUINE\'s 392/392 with')
    print('  shortfall 0 ((BE-86)(ii)), CITED here and not re-run.')
    print(f'  coin: {time.time() - t0:.1f}s')
    return True


def run_validate():
    ok = True
    ok &= run_equiv(ndraw=1)
    ok &= run_law(ndraw=1, njobs=40)
    ok &= run_bind(ndraw=1, njobs=30)
    ok &= run_coin(nflag=6)
    ok &= run_abst(ntrial=120, ngrp=25)
    print(f'\nVALIDATE: {"ALL MODES PASS" if ok else "FAILURE"}')
    return ok


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    fn = {'equiv': run_equiv, 'law': run_law, 'bind': run_bind,
          'coin': run_coin, 'abst': run_abst,
          'validate': run_validate}[mode]
    fn()
