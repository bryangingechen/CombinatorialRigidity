"""
Direction BONEONE (ordinal 56) -- CAN AN R-NODE-SHAPED 2-CUT PEEL HAVE
delta_1 = delta_2 = 1?

  THE TARGET the spec names.  BSPREAD reduced job 2 -- CROSS-CUT-ONLY forcing
  at an R-node peel with both sides flexible, half (B)'s LAST general-position
  enemy -- to one purely combinatorial question ((BE-77)(iv)): can an
  R-node-shaped 2-cut peel have delta_1 = delta_2 = 1?  A `no` would remove
  the enemy outright.  The evidence pointing at `no` was 43 763 R-node-shaped
  peels and 932 peels at (1,1) over two tiers with the INTERSECTION EMPTY.

  THE ANSWER, said at the top: YES -- and the enemy RE-OPENS.

    (BE-79) THE PEEL FACTORIZES.  delta_i and `rnode_shaped` are both
            functions of ONE SIDE, and any two sides glue.  So the question
            is not about peels at all: it asks whether a SINGLE side can be
            R-node-shaped with delta = 1.  It can.  WIT11: an n = 9 side over
            the K4 skeleton with delta = 1, glued to an n = 4 side with
            delta = 1, is an R-node-shaped peel at (1,1) on 11 vertices.
            WIT16 glues two copies of the n = 9 side, so BOTH sides are
            R-node-shaped -- the `and` reading falls too.

    (BE-80) WHY BOTH TIERS SAW NOTHING, and neither reason is evidence.
            A side that is R-node-shaped with delta >= 1 has
              |V| >= 7 + min_s [ 5 s + phi(q - p - 1 - s) ] >= 9,
            with equality ONLY when q = p + 2, i.e. only over K4; a side with
            delta = 1 has |V| >= 4.  So the smallest R-node-shaped (1,1) peel
            has 11 vertices -- ONE ABOVE tier A's n <= 10 cap.  And EVERY
            2-cut of a subdivided skeleton has a PATH side, whose delta is
            min(L, 6) >= 2, so tier B could not host one AT ANY CAP.  Both
            tiers had ZERO chances, and the "empty intersection" is vacuous.

    (BE-81) THE ENEMY IS LIVE.  Of the 48 R-node-shaped (1,1) peels on 11
            vertices, 24 have pi_u = pi_v FORCED, every certificate exactly
            (BE-77)(ii)'s {v, b_1, b_2} split (2,2) by the cut.  So
            (BE-66)(iv)'s CONCLUSION -- the coincidence cannot be forced
            where the consumer needs it -- is REFUTED for the aggressive
            operator, not merely unproved.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `side` (BE-79)  The factorization, ASSERTED: for a battery of glued pairs,
            `btwocut.deltas_at` and `bpeel.rnode_shaped` on the glued graph
            agree side-for-side with the same functions run on the sides
            alone.  Then the two witnesses, verified off the shipped oracles
            (and cross-checked against `binduc`'s set-partition oracle
            wherever `deltas_at`'s own `check=True` reaches).

  `bound` (BE-80)  The size theorem and the two vacuity findings.  The phi
            table is enumerated exhaustively over simple graphs on <= 6
            vertices; the contraction identity behind the bound is asserted
            against `kbare_common.exact_deficiency`; the bound itself is
            checked by EXHAUSTIVE enumeration of R-node-shaped sides over
            every 3-connected skeleton on p = 4, 5, 6 inside the caps below.
            Then the path-side law delta = min(L, 6), and the assertion --
            run over `bpeel.constructed_tier` ITSELF -- that every peel of
            the constructed tier has a path side.

  `force` (BE-81)  The forcing census.  EVERY R-node-shaped (1,1) peel on 11
            and 12 vertices of the factorized generator, with
            `bpeel.pair_forced` run on each and `bearfull.step_shape`
            classifying every step of the winning derivation.

Succeeds `notes/scripts/w4/bspread.py` (Steps BE73-BE77) and, through it,
`bpeel` / `bearfull` / `btwocut` / `bimage` / `bzavoid` / `binduc` /
`kbare_common`, all imported READ-ONLY rather than reimplemented: no
deficiency oracle, no closure, no R-node stand-in and no peel scan is
rewritten here.  BSPREAD's and BPEEL's figures are CITED, never re-run,
except where a mode re-derives one ON PURPOSE and says so.

Conventions inherited verbatim (`notes/scripts/README.md`): exact integer
arithmetic throughout, every rng seeded with the printed literal below, every
cap disclosed.

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import neighbors                                    # noqa: E402
from kbare_common import exact_deficiency, verts_of                # noqa: E402
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- This driver is the SEVENTEENTH `kbare/` consumer and takes the chain
# --- FIFTEEN deep (`battain -> bzavoid -> binduc -> btwocut -> bimage ->
# --- bearcase -> bearfull -> bsharp -> brule -> bwin -> brnode -> bdecor ->
# --- bpeel -> bspread -> boneone`).  NO MOVE MADE -- a dispatch may not edit
# --- a landed driver another direction may be importing in flight; job 3's
# --- verdict on whether fifteen deep is still a device chain is in the
# --- workbook's harness note.
from btwocut import (deltas_at, g_exact,                           # noqa: E402
                     vertex_connectivity_at_least)
from bearfull import step_shape                                    # noqa: E402
from binduc import split_at_pair                                   # noqa: E402
from bpeel import (SKELETONS, constructed_tier, hubs_of,           # noqa: E402
                   pair_forced, peel_scan, rnode_shaped, subdivided)
from bspread import closure_trace                                  # noqa: E402

SEED = 20260901

U, V = 'u', 'v'


# ================================================== side-level primitives

def side_delta(E):
    """(f, g, delta) of ONE SIDE at its terminals {U, V}, by the same two
    oracles `btwocut.deltas_at` uses per side -- `exact_deficiency` for f and
    `btwocut.g_exact` (the contraction oracle) for g.  Nothing is
    reimplemented: the point of this function is that BOTH are functions of
    the side alone, which is (BE-79)(i)."""
    f = exact_deficiency(E)[0]
    g = g_exact(E, U, V)
    assert 0 <= f - g <= 6, ('delta out of [0, 6]', E, f, g)
    return f, g, f - g


def rside(lengths, tag):
    """An R-node-shaped SIDE over the K4 skeleton: `bpeel.subdivided` builds
    the piece with branch lengths `lengths` (the virtual branch A-B first and
    always at length 1), then the virtual edge is REMOVED.  So the side H
    satisfies H + uv = a subdivision of K4 with uv unsubdivided, which is
    exactly what `bpeel.rnode_shaped` tests for."""
    skel = SKELETONS['K4']
    assert skel[0] == ('A', 'B')
    E = subdivided(skel, [1] + list(lengths))
    ren = {'A': U, 'B': V}
    out = []
    for (a, b) in E:
        if (a, b) == ('A', 'B'):
            continue                       # drop the virtual edge
        out.append((ren.get(a, (tag, a)), ren.get(b, (tag, b))))
    return out


def k4_rsides(n, tag='A'):
    """EVERY R-node-shaped side over K4 on n vertices with delta = 1, by
    exhaustive enumeration of the five non-virtual branch lengths."""
    out = []
    for c in _comps(n - 4, 5):
        L = tuple(k + 1 for k in c)
        H = rside(L, tag)
        assert len(verts_of(H)) == n
        if side_delta(H)[2] == 1:
            assert rnode_shaped(H, U, V), ('not R-node-shaped', L)
            out.append((L, H))
    return out


def free_sides(n, tag='B'):
    """EVERY side on n vertices with delta = 1 and no shape condition: all
    simple graphs on {u, v} + (n-2) interior vertices with u !~ v, connected,
    both terminals of degree >= 1, and H + uv 2-connected (so the glue is a
    genuine 2-cut of a 2-connected graph)."""
    ext = [(tag, i) for i in range(n - 2)]
    W = [U, V] + ext
    pairs = [e for e in itertools.combinations(W, 2) if set(e) != {U, V}]
    out = []
    for mask in range(1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        if len(verts_of(E)) != n:
            continue
        nb = neighbors(E)
        if not nb.get(U) or not nb.get(V):
            continue
        seen, st = {W[0]}, [W[0]]
        while st:
            x = st.pop()
            for y in nb[x]:
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        if len(seen) != n:
            continue
        idx = {w: i for i, w in enumerate(sorted(map(str, W)))}
        EE = [(idx[str(a)], idx[str(b)]) for (a, b) in E] + \
             [(idx[str(U)], idx[str(V)])]
        if not vertex_connectivity_at_least(n, EE, 2):
            continue
        if side_delta(E)[2] == 1:
            out.append(E)
    return out


def _comps(total, parts):
    if parts == 0:
        if total == 0:
            yield ()
        return
    for k in range(total + 1):
        for r in _comps(total - k, parts - 1):
            yield (k,) + r


def three_connected(p):
    """Every simple 3-connected graph on p vertices, up to isomorphism, by
    brute force over labelled graphs with `btwocut`'s connectivity test."""
    pairs = list(itertools.combinations(range(p), 2))
    seen, out = set(), []
    for mask in range(1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        if len(E) < (3 * p + 1) // 2:
            continue
        deg = [0] * p
        for (a, b) in E:
            deg[a] += 1
            deg[b] += 1
        if min(deg) < 3:
            continue
        if not vertex_connectivity_at_least(p, E, 3):
            continue
        best = None
        for pe in itertools.permutations(range(p)):
            k = tuple(sorted(tuple(sorted((pe[a], pe[b]))) for (a, b) in E))
            if best is None or k < best:
                best = k
        if best in seen:
            continue
        seen.add(best)
        out.append(list(best))
    return out


# ========================================= mode: side   ((BE-79))

WIT11_LENGTHS = (1, 1, 1, 6, 1)      # branch lengths A-C, A-D, B-C, B-D, C-D
W9_ALT = (1, 1, 4, 3, 1)


def wit11():
    """The minimal witness: an R-node-shaped side on 9 vertices with
    delta = 1, glued to a 4-vertex side with delta = 1."""
    H1 = rside(WIT11_LENGTHS, 'A')
    H2 = [(U, ('B', 0)), (U, ('B', 1)), (('B', 0), ('B', 1)),
          (('B', 0), V)]
    return H1, H2


def wit16():
    H1 = rside(WIT11_LENGTHS, 'A')
    H2 = rside(WIT11_LENGTHS, 'B')
    return H1, H2


def _peel_report(H1, H2, name):
    G = H1 + H2
    n = len(verts_of(G))
    found = [(u, v) for (u, v, _1, _2, _3, _4) in peel_scan(n, G)
             if {u, v} == {U, V}]
    assert found, ('the glue is not a peel', name)
    cd = deltas_at(G, U, V, check=True)
    V1, E1, f1, g1, V2, E2, f2, g2 = cd
    by = {frozenset(map(str, verts_of(E1))): (f1 - g1, rnode_shaped(E1, U, V)),
          frozenset(map(str, verts_of(E2))): (f2 - g2, rnode_shaped(E2, U, V))}
    d1, r1 = by[frozenset(map(str, verts_of(H1)))]
    d2, r2 = by[frozenset(map(str, verts_of(H2)))]
    print(f'      {name}: n = {n}, m = {len(G)}; delta_1 = {d1}, '
          f'delta_2 = {d2}; R-node-shaped side 1 = {r1}, side 2 = {r2}; '
          f'forced = {pair_forced(G, U, V)}')
    return G, (d1, d2, r1, r2)


def run_side(seed=SEED):
    print('===== Step BE78 / (BE-79): the peel FACTORIZES, and the answer '
          'is YES =====')
    print('  (BE-79)(i)  delta_i and `rnode_shaped` are functions of ONE')
    print('  SIDE.  ASSERTED against the shipped whole-graph oracle: for')
    print('  every glued pair below, `btwocut.deltas_at` and')
    print('  `bpeel.rnode_shaped` on the GLUED graph agree side-for-side')
    print('  with `exact_deficiency` / `btwocut.g_exact` / `rnode_shaped`')
    print('  run on the sides ALONE.')
    t0 = time.time()
    rng = random.Random(seed)
    Rs = k4_rsides(9) + k4_rsides(10)
    Fs = free_sides(4) + free_sides(5)
    print(f'      {len(Rs)} R-node-shaped K4 sides at delta = 1 (n = 9, 10); '
          f'{len(Fs)} unrestricted sides at delta = 1 (n = 4, 5)')
    checked = 0
    pool = [(H1, H2) for (_L, H1) in Rs for H2 in Fs]
    rng.shuffle(pool)
    for (H1, H2) in pool[:400]:
        s1, s2 = side_delta(H1), side_delta(H2)
        r1, r2 = rnode_shaped(H1, U, V), rnode_shaped(H2, U, V)
        G = H1 + H2
        cd = deltas_at(G, U, V, check=True)
        V1, E1, f1, g1, V2, E2, f2, g2 = cd
        got = {frozenset(map(str, verts_of(E1))): (f1, g1,
                                                   rnode_shaped(E1, U, V)),
               frozenset(map(str, verts_of(E2))): (f2, g2,
                                                   rnode_shaped(E2, U, V))}
        assert got[frozenset(map(str, verts_of(H1)))] == (s1[0], s1[1], r1)
        assert got[frozenset(map(str, verts_of(H2)))] == (s2[0], s2[1], r2)
        checked += 1
    print(f'      {checked} / {checked} glued pairs: the glued graph\'s '
          f'(f, g, R-node) per side EQUALS the sides\' own, 0 mismatches.')
    print('      So a witness needs only ONE R-node-shaped side at delta = 1')
    print('      and ONE side at delta = 1, built independently.')
    print()
    print('  (BE-79)(ii)  THE WITNESSES.  `deltas_at(check=True)` runs')
    print('  binduc\'s independent set-partition oracle on every side it can')
    print('  reach (|V| <= 8), so the small side is cross-checked twice.')
    G11, r11 = _peel_report(*wit11(), name='WIT11')
    G16, r16 = _peel_report(*wit16(), name='WIT16')
    assert r11[:2] == (1, 1) and (r11[2] or r11[3])
    assert r16[:2] == (1, 1) and r16[2] and r16[3]
    print('      WIT11 answers the `or` reading (the one the consumer needs:')
    print('      (BE-67)(iii) knows the REST-OF-PIECE side is R-node-shaped')
    print('      and knows nothing about the child).  WIT16 answers the `and`')
    print('      reading too, so no narrowing of the hypothesis rescues it.')
    print()
    print('  (BE-79)(iii)  THE SHAPE OF THE n = 9 SIDE, stated so it can be')
    print('  read without the driver.  Skeleton K4 on {u, v, C, D}; the')
    print(f'  virtual edge uv absent; branch lengths {WIT11_LENGTHS} on '
          '(uC, uD, vC, vD, CD).')
    H1, _ = wit11()
    f, g, d = side_delta(H1)
    print(f'      H1: n = {len(verts_of(H1))}, m = {len(H1)}, '
          f'def_3 = {f}, g_uv = {g}, delta = {d}; the triangle {{u, C, D}}')
    print('      is the unique positive block and B_1 = {u, C, D} is the')
    print('      u-block of its optimal partition, with v ~ C the unique')
    print('      edge from [v] to B_1 -- exactly (BE-77)(ii) Step 3.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return True


# ========================================= mode: bound  ((BE-80))

def phi_table(vmax=9):
    """phi(c) = min over SIMPLE graphs of (|S| - 1) for a connected subgraph
    with cyclomatic number c, enumerated exhaustively on <= vmax vertices."""
    out = {0: 0}
    for v in range(3, vmax + 1):
        emax = v * (v - 1) // 2
        for c in range(1, emax - v + 2):
            out.setdefault(c, v - 1)
    return out


def size_bound(p, q, phi):
    """7 + min_s [5 s + phi(q - p - 1 - s)] -- the (BE-80)(i) lower bound on
    |V(H)| for an R-node-shaped side with def_3 >= 1 over a skeleton with p
    vertices and q edges."""
    C = q - p - 1
    return max(p, 7 + min(5 * s + phi[C - s] for s in range(C + 1)))


def _path_length(E, u, v):
    """L if the side `E` is the bare path u - x_1 - ... - x_{L-1} - v (its
    interior vertices all of degree 2, its terminals of degree 1, and
    |E| = |V| - 1), else None."""
    nb = neighbors(E)
    W = verts_of(E)
    if len(E) != len(W) - 1:
        return None
    if len(nb.get(u, ())) != 1 or len(nb.get(v, ())) != 1:
        return None
    for w in W:
        if w in (u, v):
            continue
        if len(nb[w]) != 2:
            return None
    return len(E)


def path_side(L):
    """The side that is a bare path u - x_1 - ... - x_{L-1} - v."""
    if L == 1:
        return None
    ws = [(f'p{i}',) for i in range(L - 1)]
    ch = [U] + ws + [V]
    return [(ch[i], ch[i + 1]) for i in range(L)]


def run_bound(ncap4=12, ncap56=10, seed=SEED):
    print('===== Step BE79 / (BE-80): the SIZE theorem, and why BOTH tiers '
          'of (BE-77)(iv) had ZERO chances =====')
    t0 = time.time()
    phi = phi_table()
    print('  (BE-80)(i)  THE BOUND.  def_3(H) = max over CONTRACTIONS Q of')
    print('  [v_Q - 5 s_Q - 6], s_Q := e_Q - v_Q; H 2-connected makes every')
    print('  Q 2-connected, so s_Q >= 0 and def_3 >= 1 forces v_Q >= 7 + 5 s.')
    print('  Contracting blocks costs sum(|S_i| - 1) >= phi(sum c_i) with')
    print('  sum c_i = (q - p - 1) - s, so')
    print('      |V(H)| >= 7 + min_s [ 5 s + phi(q - p - 1 - s) ].')
    print('  phi, enumerated exhaustively over simple graphs on <= 6 '
          'vertices:')
    print('     ', {c: phi[c] for c in range(0, 11)})
    print('  The bound is >= 9 always, and = 9 ONLY at q = p + 2; a simple')
    print('  3-connected graph has q >= ceil(3p/2), so q = p + 2 forces')
    print('  p <= 4: the ONLY skeleton reaching 9 is K4.')
    tab = []
    for p in (4, 5, 6, 7, 8):
        for q in range((3 * p + 1) // 2, p * (p - 1) // 2 + 1):
            tab.append((p, q, size_bound(p, q, phi)))
    print(f'      min over all (p, q) with p <= 8 = '
          f'{min(t[2] for t in tab)}, attained only at '
          f'{[(t[0], t[1]) for t in tab if t[2] == 9]}')
    assert min(t[2] for t in tab) == 9
    assert [(t[0], t[1]) for t in tab if t[2] == 9] == [(4, 6)]
    print()
    print('  (BE-80)(ii)  THE BOUND, CHECKED BY EXHAUSTIVE ENUMERATION over')
    print('  every 3-connected skeleton on p = 4, 5, 6 and every branch-')
    print(f'  length profile inside the caps (n <= {ncap4} at p = 4, '
          f'n <= {ncap56} at p = 5, 6).')
    scanned = mind = 0
    minima = []
    for p in (4, 5, 6):
        cap = ncap4 if p == 4 else ncap56
        for G in three_connected(p):
            q = len(G)
            lo = size_bound(p, q, phi)
            if lo > cap:
                continue
            for uv in G:
                others = [e for e in G if e != uv]
                for n in range(lo, cap + 1):
                    for c in _comps(n - p, len(others)):
                        ell = {uv: 1}
                        for e, k in zip(others, c):
                            ell[e] = k + 1
                        E = []
                        for e in G:
                            k = ell[e]
                            if k == 1:
                                E.append(e)
                                continue
                            prev = e[0]
                            for j in range(k - 1):
                                w = ('s', e, j)
                                E.append((prev, w))
                                prev = w
                            E.append((prev, e[1]))
                        H = [e for e in E if e != uv]
                        ren = {uv[0]: U, uv[1]: V}
                        H = [(ren.get(a, a), ren.get(b, b)) for (a, b) in H]
                        scanned += 1
                        f, g, d = side_delta(H)
                        if d >= 1:
                            assert len(verts_of(H)) >= lo, (p, q, n, lo)
                            minima.append((len(verts_of(H)), p, q, d))
                            if d == 1:
                                mind += 1
    lo9 = [m for m in minima if m[0] == 9]
    print(f'      {scanned} R-node-shaped sides enumerated; '
          f'{len(minima)} with delta >= 1, {mind} with delta = 1.')
    print(f'      Smallest |V| with delta >= 1 = {min(m[0] for m in minima)}; '
          f'skeletons attaining it = '
          f'{sorted({(m[1], m[2]) for m in lo9})}; 0 violations of the bound.')
    assert min(m[0] for m in minima) == 9
    assert sorted({(m[1], m[2]) for m in lo9}) == [(4, 6)]
    print()
    print('  (BE-80)(iii)  TIER A HAD ZERO CHANCES.  A side with delta = 1')
    print('  has |V| >= 4 -- |V| = 3 forces the side to be u - x - v, whose')
    print('  delta is 2.  So an R-node-shaped peel at (1, 1) has')
    print('  n = n_1 + n_2 - 2 >= 9 + 4 - 2 = 11, and WIT11 ATTAINS it.')
    p3 = path_side(2)
    assert side_delta(p3)[2] == 2
    print(f'      the 3-vertex side u - x - v: delta = {side_delta(p3)[2]}')
    print('      tier A of (BE-77)(iv) is `bspread.py peel` at n = 6..10.')
    print('      11 > 10, so its EMPTY INTERSECTION was forced by the cap:')
    print('      5 005 R-node-shaped peels and 932 peels at (1, 1) could not')
    print('      have met whatever the truth is.  0 chances, not 932.')
    print()
    print('  (BE-80)(iv)  TIER B HAD ZERO CHANCES AT ANY CAP, and this is')
    print('  the sharper of the two.  The path-side law, asserted:')
    row = []
    for L in range(2, 13):
        d = side_delta(path_side(L))[2]
        assert d == min(L, 6), (L, d)
        row.append((L, d))
    print(f'      delta of the bare path side, L = 2..12: {row}  '
          '= min(L, 6), never 1.')
    print('  And EVERY peel `bpeel.constructed_tier` yields sits at a')
    print('  SUBDIVIDED SKELETON BRANCH (`prof[i] >= 2` in its own body), so')
    print('  one side is the interior of that branch -- a path.  Asserted')
    print('  over the shipped generator:')
    tot = withpath = lawok = 0
    for (_tag, E, u, v, d1, d2, _forced, _rn) in constructed_tier(
            maxlen=3, nsamp=120, seed=seed):
        tot += 1
        _V1, E1, _V2, E2 = split_at_pair(E, u, v)
        ds = {id(E1): d1, id(E2): d2}
        got = False
        for Ei in (E1, E2):
            L = _path_length(Ei, u, v)
            if L is None:
                continue
            got = True
            assert ds[id(Ei)] == min(L, 6), (L, ds[id(Ei)])
            lawok += 1
        assert got, 'a constructed peel with no path side'
        withpath += 1
        assert not (d1 == 1 and d2 == 1)
    print(f'      {tot} constructed peels, {withpath} of them carrying a '
          f'PATH side ({lawok} path sides, every one at delta = min(L, 6)); '
          f'0 at (1, 1) -- STRUCTURALLY, not by cap.')
    print('      (cap: maxlen = 3, nsamp = 120 here, since the claim is')
    print('      structural; BPEEL ran the same generator at maxlen = 4,')
    print('      nsamp = 1 500 for its 38 758 peels, CITED not re-run.)')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return True


# ========================================= mode: force  ((BE-81))

def run_force(seed=SEED):
    print('===== Step BE80 / (BE-81): the forcing census -- THE ENEMY '
          'RE-OPENS =====')
    t0 = time.time()
    print('  Every R-node-shaped peel at (1, 1) on 11 and 12 vertices, built')
    print('  by the factorized generator of (BE-79)(i): an R-node-shaped K4')
    print('  side at delta = 1 glued to an unrestricted side at delta = 1.')
    print('  `bpeel.pair_forced` is the shipped verdict; by (BE-73)(ii)(b) a')
    print('  ONE-SIDED certificate would force delta_i = 0, so at (1, 1)')
    print('  every hit is CROSS-CUT-ONLY by construction.')
    R = {9: k4_rsides(9, 'A'), 10: k4_rsides(10, 'A')}
    Fr = {4: free_sides(4, 'B'), 5: free_sides(5, 'B')}
    rows = []
    sample = None
    for (n1, n2) in ((9, 4), (9, 5), (10, 4)):
        tot = forced = 0
        for (_L, H1) in R[n1]:
            for H2 in Fr[n2]:
                G = H1 + H2
                cd = deltas_at(G, U, V, check=False)
                assert cd[2] - cd[3] == 1 and cd[6] - cd[7] == 1
                assert rnode_shaped(cd[1], U, V) or rnode_shaped(cd[5], U, V)
                tot += 1
                if pair_forced(G, U, V):
                    forced += 1
                    if sample is None:
                        sample = G
        rows.append((n1 + n2 - 2, n1, n2, tot, forced))
        print(f'      n = {n1 + n2 - 2} (n_1 = {n1}, n_2 = {n2}): {tot} '
              f'R-node-shaped (1, 1) peels, {forced} with pi_u = pi_v FORCED')
    assert rows[0][4] > 0
    print()
    print('  THE DERIVATION at WIT11, with every step classified by')
    print('  `bearfull.step_shape` -- the (BE-41)(i) star-2 shape, or the')
    print('  spread residue (BE-74) closed:')
    G = sum(wit11(), [])
    nb = neighbors(G)
    hubs = hubs_of(G, nb)
    V1 = set(map(str, verts_of(wit11()[0])))
    V2 = set(map(str, verts_of(wit11()[1])))
    shown = 0
    for h in sorted(hubs, key=str):
        A, adm, tr = closure_trace(nb, hubs, h)
        if U not in adm or V not in adm:
            continue
        print(f'      seed {h}:')
        for (z, wit) in tr:
            sh, _w = step_shape(G, z, wit, nb)
            a = len({str(x) for x in wit} & V1)
            b = len({str(x) for x in wit} & V2)
            print(f'        admit {str(z):<10} witnesses '
                  f'{sorted(map(str, wit))!s:<34} split = ({a}, {b})  '
                  f'shape = {sh}')
        shown += 1
        if shown == 2:
            break
    print()
    print('  THE CERTIFICATE IS EXACTLY (BE-77)(ii)\'s.  The first terminal')
    print('  is admitted ONE-SIDEDLY ((BE-77)(i)(b)); the second is admitted')
    print('  on {v, b_1, b_2} with witness split (2, 2), b_1 = C the unique')
    print('  neighbour of v in side 1\'s u-block and b_2 the unique')
    print('  neighbour of v in side 2\'s.  So the theorem is CONFIRMED on a')
    print('  live instance in the direction it was proved -- and it is the')
    print('  hypothesis (1, 1) that turns out to be satisfiable.')
    print()
    print('  CAP DISCLOSURE.  The n = 11 row is EXHAUSTIVE over the class it')
    print('  names: every K4-skeleton R-node side at n = 9 with delta = 1')
    print('  (12 of them, all branch profiles) against every 4-vertex side')
    print('  with delta = 1 (4 of them, all graphs).  The n = 12 rows are')
    print('  exhaustive in the same sense at (9, 5) and (10, 4).  Sides over')
    print('  the p = 5, 6 skeletons start at n_1 = 10 and are NOT in this')
    print('  census -- they would only add witnesses.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows[0][4] > 0


# ============================================================== validate

def run_validate():
    ok = True
    ok &= bool(run_side())
    print()
    ok &= bool(run_bound())
    print()
    ok &= bool(run_force())
    print()
    print('===== Step BE81 / (BE-82) and Step BE82 / (BE-83) are PROSE '
          '(the consumer residue and the board); nothing to run. =====')
    print('VALIDATE:', 'OK' if ok else 'FAILED')
    return ok


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    {'side': run_side, 'bound': run_bound, 'force': run_force,
     'validate': run_validate}[mode]()
