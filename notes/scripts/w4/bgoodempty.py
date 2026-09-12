"""
Direction BGOODEMPTY (Phase 39 PENCIL, section (K-bare-ext)) -- is there a
piece `H` in the RUNG-3 region (`a = 0`, `Sigma_delta <= 6`, side-degree
`>= 2` on both sides, internal R-node peel, generic flag regime) with

                        Good(H; x, y)  =  EMPTY ?

  WHY A SEARCH CANNOT ANSWER IT, and what this driver does instead.
  (BE-69)(ii) consequence 2: a draw OUTSIDE `Good` settles nothing, because
  `dim(rho_bar_1 + rho_bar_2)` is LOWER semicontinuous -- a draw is a lower
  bound on the generic value, so a measured shortfall is not a generic one.
  So every mode below is built around the question *which measured quantity
  has the OTHER semicontinuity direction?*, i.e. which draw is an UPPER
  bound on its generic value.  Three of them are, and each converts one
  exact-Q draw into a statement about the whole chart:

    U-1 `a_i = dim M_i - 6 - f_i`.  `dim M_i` is upper semicontinuous
         (rank is lower), so a draw with `a_i = 0` PROVES `a_i = 0`
         generically.  This is the mechanism (BE-69)(iii) already uses.
    U-2 `c_i(U) = dim(rho_bar_i cap U)` at a stable block: upper
         semicontinuous where `rho_i` is constant, so a draw is an upper
         bound on the generic `c_i(U)` -- which is the WRONG direction for
         exhibiting a violation and the RIGHT one for excluding it.
    U-3 `m_i := dim cap_P <P>` over the x--y paths `P` of side `i`, on the
         locus where the path-span profile `(dim <P>)_P` is at its maximum:
         upper semicontinuous ((BE-65)(iii)), so a max-profile draw is an
         upper bound on the generic value.  And `rho_bar_i <= cap_P <P>`
         POINTWISE by (BE-30)(iv), at every configuration, degenerate ones
         included.

  THE CRITERION this direction adds, and it is a theorem, not a search.
  Suppose at one max-profile exact-Q draw of `Chart(H)` we measure `m_i` and
  find `delta_i > m_i`.  Then `Good(H; x, y) = EMPTY`.  *Proof.*  Both
  `{path-span profile maximal}` and `{dim cap_P <P> <= m_i}` are nonempty
  open, hence DENSE, since `Chart(H)` is irreducible ((BE-65)(ii) citing
  (CH-1)(a)).  If `Good` were nonempty it would be dense too ((BE-69)(ii)),
  and two dense opens of an irreducible variety meet; at a common point
  `a = (0,0)` and `dim(rho_bar_1+rho_bar_2) = min(Sigma_delta, 6)`, which at
  rung 3 is `Sigma_delta`, forcing `rho_i = delta_i` on both sides; but
  `rho_i <= dim cap_P <P> <= m_i < delta_i` there.  Contradiction.  QED
  So the dichotomy the spec's crux quotes is not only an obstacle -- run in
  the other direction it is the tool that makes ONE draw decisive.

  THE ANSWER, said at the top: NOT FOUND, and two of the three routes to it
  are CLOSED by proof rather than by exhaustion.

    * `dist` -- the ONE-SIDED obstruction `delta_i > dist_i(x, y)` (which by
      (BE-30)(iv) would give `rho_i < delta_i` at EVERY configuration and so
      `Good = EMPTY` outright) is COMBINATORIALLY IMPOSSIBLE.  Proof, from
      the partition formula `def_3(G) = max_P [6(|P|-1) - 5 d(P)]` that is
      the (6,6)-count oracle `bdecor.d3` computes: `g_{xy}` is the same
      maximum restricted to partitions with `x, y` in ONE block, so take an
      optimal `P*` for `f`, let `t` be the number of its blocks met by a
      shortest x--y path, and merge them.  The merged partition has `x, y`
      together, loses `t - 1` blocks (`-6(t-1)`) and buries at least `t - 1`
      crossing edges (`+5(t-1)`), so `g >= f - (t-1) >= f - dist`.  Hence
      `delta = f - g <= dist(x, y)`.  QED  Enumerated below at 5 402 / 5 402
      (side, pair) rows with no exception, as a check on the proof.
    * `conf` -- the CONFINEMENT criterion above, run over the side library:
      `delta_i = m_i` at every row, i.e. the confinement `rho_bar_i <= cap_P
      <P>` is TIGHT, so U-3 never fires.  `rho_bar_i <= cap_P <P>` is
      additionally asserted AS A SUBSPACE at every draw.
    * `block` -- the two-sided hunt, on the WHOLE-`H` flag: the generic
      block profile over free draws, and the margin `c_1(U) + c_2(U) -
      dim U - max(0, Sigma_delta - 6)` over the 16 `S(phi)`-stable `U`.

  THE SCOPE, which travels with every figure: "not found under cap C", never
  "does not exist" -- and here with teeth, because `Good = EMPTY` is exactly
  a claim a search cannot make.  What `block` and `sweep` report is the
  generic profile ESTIMATED from finitely many draws; only `dist` and the
  `conf` criterion are proofs.

  MODES
    mech   the coordinator's mechanism -- "(BE-22)(ii)'s partition cap
           FORCES `Good != 0` at rung 3" -- eliminated, in the currency the
           cap is stated in.
    dist   the combinatorial theorem `delta_{xy} <= dist(x, y)`, enumerated
           cap-free over cycles, thetas, generalized thetas and every
           subdivided-skeleton pair, plus random 2-connected subdivisions.
    conf   the confinement criterion U-3: `delta_i` vs `m_i` at a
           max-profile exact-Q draw, with `rho_bar_i <= cap_P <P>` asserted
           as a subspace.
    pix    THE `Pi_x` LEMMA: `c_i(Pi_x) <= 1` on a dense open whenever
           `dist_i(x, y) <= 4` (PROVED, via `rank(omega |-> omega ^ p_x) = 3`),
           and `c_i(Pi_x) = 2` only at `rho_i = 6` (MEASURED) -- which at
           rung 3 forces the other side RIGID, so `Pi_x` cannot obstruct.
    block  the two-sided hunt on the whole-`H` flag over a WIDENED composite
           population (all non-adjacent hub pairs, branch lengths past the
           landed fence, a side-1 library the landed builders do not carry).
    sweep  the spec's TELL: shortfall at several independent FREE draws per
           piece, reported as a pointer and never as a result.
    validate  mech + dist(quick) + conf(quick) + block(quick).

  Run:  python3 notes/scripts/w4/bgoodempty.py [mode]
"""
import itertools
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors                                    # noqa: E402
from kbare_common import verts_of                                  # noqa: E402
from bimage import (dim, isect, span, hat, wedge2, rho_bar_of,     # noqa: E402
                    plane_at)
from bdecor import (d3, weld_d3, sample_by_branches, girth,        # noqa: E402
                    hcard_ok_piece)
from bpeel import SKELETONS, subdivided, rnode_shaped, split_at_pair  # noqa: E402
import bproper                                                     # noqa: E402
import bunif                                                       # noqa: E402

SEED = 20260912


# ===================================================== graph-side primitives

def delta_of(E, x, y):
    """`delta_{xy}` of a side: `def_3 - def_3(welded)`, the landed oracles."""
    return d3(E) - weld_d3(E, x, y)


def dist_of(E, x, y):
    """`dist(x, y)` in the side, by BFS.  None if x and y are separated."""
    nb = neighbors(E)
    seen, q = {x: 0}, [x]
    while q:
        v = q.pop(0)
        for w in nb[v]:
            if w not in seen:
                seen[w] = seen[v] + 1
                q.append(w)
    return seen.get(y)


def xy_paths(E, x, y, cap=600, maxlen=9):
    """Every simple x--y path of `E` with at most `maxlen` edges, as an edge
    list, up to `cap` of them.  Returns (paths, truncated)."""
    nb = neighbors(E)
    out, trunc = [], False

    def go(v, seen, path):
        nonlocal trunc
        if len(out) >= cap:
            trunc = True
            return
        if len(path) >= maxlen:
            if y in nb[v] and len(path) < maxlen:
                out.append(path + [(v, y)])
            else:
                trunc = trunc or (len(path) == maxlen)
            return
        for w in sorted(nb[v], key=str):
            if w == y:
                out.append(path + [(v, w)])
            elif w not in seen:
                go(w, seen | {w}, path + [(v, w)])
    go(x, {x}, [])
    return out, trunc


def path_span(pt, path):
    """`<P>` -- the span of the hinge lines along `path`, at the drawn
    configuration.  (BE-30)(i)/(iv)'s object."""
    return span([wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in path])


# ===================================================== the side library

def cyc(a, b):
    """A cycle through x and y with arcs of `a` and `b` edges."""
    E, prev = [], 'x'
    for i in range(a - 1):
        E.append((prev, f'a{i}'))
        prev = f'a{i}'
    E.append((prev, 'y'))
    prev = 'x'
    for i in range(b - 1):
        E.append((prev, f'b{i}'))
        prev = f'b{i}'
    E.append((prev, 'y'))
    return E


def gtheta(lens):
    """The generalized theta: `len(lens)` internally disjoint x--y paths."""
    E = []
    for j, L in enumerate(lens):
        prev = 'x'
        for i in range(L - 1):
            E.append((prev, f't{j}_{i}'))
            prev = f't{j}_{i}'
        E.append((prev, 'y'))
    return E


def ladder(a, b, c):
    """Two x--y arcs of `a` and `b` edges joined by a rung of `c` edges from
    the midpoint of each -- a side whose x--y paths are NOT internally
    disjoint, which no cycle or theta provides."""
    E = cyc(a, b)
    if a < 2 or b < 2:
        return None
    u, v, prev = f'a{(a - 1) // 2}', f'b{(b - 1) // 2}', None
    prev = u
    for i in range(c - 1):
        E.append((prev, f'r{i}'))
        prev = f'r{i}'
    E.append((prev, v))
    return E


def skel_side(name, prof, x, y):
    """A subdivided skeleton used as a SIDE, terminals x, y."""
    return subdivided(SKELETONS[name], list(prof))


def side_library(maxarc=8, maxtheta=7, nlad=40, seed=SEED):
    """(tag, E, x, y) over four families.  Disclosed as CONSTRUCTED."""
    for a in range(2, maxarc + 1):
        for b in range(a, maxarc + 2):
            yield (f'cyc({a},{b})', cyc(a, b), 'x', 'y')
    for k in (3, 4, 5):
        for t in itertools.combinations_with_replacement(
                range(2, maxtheta + 1), k):
            if sum(t) > 22:
                continue
            yield (f'gtheta{t}', gtheta(list(t)), 'x', 'y')
    rng = random.Random(seed)
    seen = set()
    for _ in range(nlad):
        a, b, c = (rng.randint(2, 6), rng.randint(2, 6), rng.randint(1, 5))
        if (a, b, c) in seen:
            continue
        seen.add((a, b, c))
        E = ladder(a, b, c)
        if E is not None:
            yield (f'ladder({a},{b},{c})', E, 'x', 'y')


def skeleton_pairs(maxlen=4, nsamp=120, seed=SEED):
    """(tag, E, x, y) over subdivided skeletons at EVERY vertex pair -- the
    (BE-248)(iii) un-fencing of `bproper.NONADJ`, applied to the side layer
    and carried past the landed `maxlen`."""
    rng = random.Random(seed + 7)
    for name, sk in sorted(SKELETONS.items()):
        hubs = sorted({w for e in sk for w in e})
        profs = []
        if name == 'K4':
            profs = list(itertools.product(range(1, maxlen + 1), repeat=len(sk)))
        else:
            profs = [[rng.randint(1, maxlen) for _ in range(len(sk))]
                     for _ in range(nsamp)]
        for prof in profs:
            E = subdivided(sk, list(prof))
            for (u, v) in itertools.combinations(hubs, 2):
                yield (f'{name}{tuple(prof)}', E, u, v)


# ===================================================== mode: mech

def run_mech():
    """The coordinator's mechanism: "`Good != 0` is FORCED at rung 3 by
    (BE-22)(ii)'s partition cap".  Eliminated in the cap's own currency."""
    t0 = time.time()
    print('== mech: the dispatch mechanism, ELIMINATED (RESEARCH-ARC section 7(a))')
    print('  The cap, quoted from (BE-69)(i) which uses it: "the partition')
    print('  cap (BE-22)(ii) gives `dim M_i >= 6 + f_i` AT EVERY')
    print('  configuration, so `A_i = {rank R_i >= 6|V_i| - 6 - f_i}` is the')
    print('  non-vanishing of a minor: OPEN."')
    print('  So the cap is an UPPER bound on rank.  Attainment is the')
    print('  MAXIMAL-rank locus.  A universal upper bound on rank makes that')
    print('  locus open; it says nothing whatever about its being NONEMPTY,')
    print('  and `Good` empty is precisely an emptiness claim.  The cap is')
    print('  the hypothesis of (BE-69)(i), not a substitute for (ii).')
    print('  Three LANDED rows refute the mechanism without a new draw:')
    print('   (a) (BE-86)(ii): `a_i = 1` at 100 of 392 forced witnesses --')
    print('       the cap holds there and attainment FAILS, so the cap does')
    print('       not force even `a = 0`, let alone general position.')
    print('   (b) (BE-120)(ii): `a_i in {1,2,3,6}` off a path side, and at')
    print('       15 of 21 rows an outright violation of the block')
    print('       inequality at `U = Lambda^2 K^4`.')
    print('   (c) (BE-250)(i): an `a = (0,0)` in-regime chart point with')
    print('       `dim M(H) = 7 > 6 = 6 + def_3(H)` -- a shortfall at a')
    print('       point where the cap is in force and every `a_i` is 0.')
    print('  VERDICT: the mechanism is REFUTED, by direction and by three')
    print('  landed witnesses.  Nothing in this direction rests on it.')
    print(f'  [{time.time() - t0:.1f}s]')
    return True


# ===================================================== mode: dist

def run_dist(maxarc=8, maxtheta=7, maxlen=4, nsamp=200, nrand=400, seed=SEED):
    # NOTE, coordinator at landing 2026-09-12: `nsamp`/`nrand` are restored to
    # the values the landed figure was taken at (200/400 -> 31 338 rows).  They
    # had been lowered to 120/200 after the figure was recorded, which made the
    # section's headline count irreproducible from the committed driver
    # (28 738).  The prose was right and the default had drifted; the run costs
    # ~4 s either way, so there is no cost argument for the lower value.
    """`delta_{xy} <= dist(x, y)`: the proof is in the module docstring;
    this is the enumeration that checks it."""
    t0 = time.time()
    print(f'== dist: the COMBINATORIAL theorem `delta_xy <= dist(x,y)`, '
          f'seed {seed}')
    print('  A violation would give `rho_i <= dist < delta_i` at EVERY')
    print('  configuration ((BE-30)(iv), unconditional), hence `Good = 0`.')
    print('  Proof in the module docstring (partition merging along a')
    print('  shortest path).  Enumerated here as a check on the proof.')
    rows, worst, tight = 0, 0, 0
    hist = {}
    fams = {}
    jobs = []
    for (tag, E, x, y) in side_library(maxarc, maxtheta, 40, seed):
        jobs.append(('lib', tag, E, x, y))
    for (tag, E, u, v) in skeleton_pairs(maxlen, nsamp, seed):
        jobs.append(('skel', tag, E, u, v))
    rng = random.Random(seed + 31)
    for _ in range(nrand):
        n = rng.randint(5, 9)
        sk = [(f'v{i}', f'v{(i + 1) % n}') for i in range(n)]
        for _k in range(rng.randint(1, 4)):
            a, b = rng.sample(range(n), 2)
            if (f'v{a}', f'v{b}') not in sk and (f'v{b}', f'v{a}') not in sk:
                sk.append((f'v{a}', f'v{b}'))
        prof = [rng.randint(1, 4) for _ in sk]
        E = subdivided(sk, prof)
        hubs = sorted({w for e in sk for w in e})
        u, v = rng.sample(hubs, 2)
        jobs.append(('rand', f'rand{n}', E, u, v))
    for (fam, tag, E, x, y) in jobs:
        d = delta_of(E, x, y)
        dd = dist_of(E, x, y)
        assert dd is not None, ('disconnected side', tag)
        assert 0 <= d <= 6, ('delta out of [0,6] -- (BE-21)(ii)', tag, d)
        assert d <= dd, ('!! delta > dist -- a Good = EMPTY certificate',
                         tag, x, y, d, dd)
        rows += 1
        hist[dd - d] = hist.get(dd - d, 0) + 1
        tight += (d == dd)
        worst = max(worst, d - dd)
        fams[fam] = fams.get(fam, 0) + 1
    print(f'  rows {rows}  ({fams})')
    print(f'  `dist - delta` histogram: {dict(sorted(hist.items()))}')
    print(f'  TIGHT (`delta = dist`, path-saturated): {tight} of {rows}')
    print(f'  max(delta - dist) = {worst}  -- asserted <= 0 at every row')
    print('  VERDICT: the one-sided obstruction is UNREACHABLE. Closed by')
    print('  the proof; the enumeration is the check, not the ground.')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows


# ===================================================== mode: conf

def conf_row(tag, E, x, y, ndraw=4, seed=SEED, cap=400, maxlen=9):
    """`(delta, rho_max, m_at_max_profile, npaths, truncated)` for one side,
    with `rho_bar <= cap_P <P>` ASSERTED as a subspace at every draw."""
    d = delta_of(E, x, y)
    paths, trunc = xy_paths(E, x, y, cap=cap, maxlen=maxlen)
    if not paths:
        return None
    best_prof, draws = None, []
    for s in range(ndraw):
        rng = random.Random(seed + 1013 * s + len(E))
        got = sample_by_branches(E, x, y, rng)
        if got is None:
            continue
        pt = got[0] if isinstance(got, tuple) else got
        try:
            S, rho, dM, _r = rho_bar_of(E, pt, x, y)
        except AssertionError:
            continue
        sps = [path_span(pt, P) for P in paths]
        prof = tuple(dim(q) for q in sps)
        cur = sps[0]
        for q in sps[1:]:
            cur = isect(cur, q)
        m = dim(cur)
        assert dim(isect(S, cur)) == rho, \
            ('(BE-30)(iv) FAILS as a subspace containment', tag, rho, m)
        assert rho <= m, ('rho exceeds the confinement', tag, rho, m)
        draws.append((prof, rho, m, dM))
        best_prof = prof if best_prof is None else tuple(
            max(a, b) for a, b in zip(best_prof, prof))
    if not draws:
        return None
    at_max = [r for r in draws if r[0] == best_prof]
    rho_max = max(r[1] for r in draws)
    m_gen = min(r[2] for r in at_max) if at_max else min(r[2] for r in draws)
    return d, rho_max, m_gen, len(paths), trunc, len(at_max), len(draws)


def run_conf(ndraw=4, seed=SEED, maxarc=7, maxtheta=6, quick=False):
    t0 = time.time()
    print(f'== conf: the CONFINEMENT criterion U-3, seed {seed}, '
          f'ndraw {ndraw}')
    print('  `delta_i > m_i` at a max-profile draw PROVES `Good = EMPTY`')
    print('  (module docstring).  Hunted here over the side library.')
    rows, hits, tight, trunc_rows = 0, [], 0, 0
    hist = {}
    lib = list(side_library(maxarc, maxtheta, 20 if quick else 40, seed))
    if quick:
        lib = lib[::3]
    for (tag, E, x, y) in lib:
        got = conf_row(tag, E, x, y, ndraw=ndraw, seed=seed)
        if got is None:
            continue
        d, rho, m, npaths, trunc, nmax, nd = got
        rows += 1
        trunc_rows += bool(trunc)
        hist[d - m] = hist.get(d - m, 0) + 1
        tight += (d == m)
        if d > m:
            hits.append((tag, d, rho, m, npaths, trunc))
    print(f'  rows {rows}   (path enumeration truncated at {trunc_rows})')
    print(f'  `delta - m` histogram: {dict(sorted(hist.items()))}')
    print(f'  `delta = m` (confinement TIGHT): {tight} of {rows}')
    if hits:
        print(f'  !! {len(hits)} CERTIFICATES `delta > m`:')
        for h in hits:
            print(f'     {h}')
    else:
        print('  0 certificates.  NOT FOUND under this cap: side library')
        print(f'  (cycles arcs <= {maxarc + 1}, generalized thetas 3-5 paths')
        print(f'  of length <= {maxtheta}, ladders), {ndraw} draws each.')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, hits


# ===================================================== mode: block

def side1_library():
    """Side-1 shapes for the composite, terminals literally 'x' and 'y'.
    WIDER than any landed generator: `bline.longcore_library()` carries
    `deg_1(y) = 1` at 27/27 ((BE-248)(ii)) and BWHOLEH's is the (4,4) cycle
    alone.  Here `deg_1(x), deg_1(y) in {2, 3, 4, 5}` all occur."""
    out = []
    for (a, b) in [(2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 4), (4, 5),
                   (4, 6), (5, 5), (2, 7), (3, 7)]:
        out.append((f'cyc({a},{b})', cyc(a, b)))
    for t in [(2, 5, 5), (3, 5, 5), (2, 6, 6), (4, 5, 6), (5, 5, 5),
              (3, 4, 4), (4, 4, 5), (2, 4, 4), (3, 6, 6), (2, 3, 3)]:
        out.append((f'gtheta{t}', gtheta(list(t))))
    for t in [(2, 2, 5, 5), (3, 3, 4, 4), (2, 4, 4, 4), (2, 2, 3, 3)]:
        out.append((f'gtheta{t}', gtheta(list(t))))
    for (a, b, c) in [(4, 4, 2), (4, 5, 2), (5, 5, 3), (4, 4, 3), (6, 6, 2)]:
        E = ladder(a, b, c)
        if E:
            out.append((f'ladder({a},{b},{c})', E))
    # HIGH-dist side-1 shapes.  `Pi_x <= rho_bar_i` needs `Pi_x <= <P>` for
    # EVERY x--y path, and `<P> cap Pi_x` is 1-dimensional whenever
    # `dim <P> < 6`, so the only place a GENERIC `c_i(Pi_x) = 2` can live is
    # where every x--y path is long.  These are the shapes that put it there:
    # subdivided 3-connected skeletons used as SIDE 1, terminals a
    # non-adjacent hub pair, branch lengths pushing `dist` to 4-8.
    for name in ('K33', 'prism'):
        sk = SKELETONS[name]
        for base in (2, 3, 4):
            prof = [base] * len(sk)
            E0 = subdivided(sk, prof)
            for (u, v) in nonadj_pairs(name):
                ren = {u: 'x', v: 'y'}
                E = [(ren.get(a, f'q{a}'), ren.get(b, f'q{b}'))
                     for (a, b) in E0]
                out.append((f'{name}[{base}]^{u}{v}', E))
    return out


def nonadj_pairs(name):
    """EVERY skeleton-non-adjacent hub pair -- `bproper.NONADJ` lists 3 of 6
    per skeleton; (BE-248)(iii) un-fenced it and this carries that."""
    sk = SKELETONS[name]
    hubs = sorted({w for e in sk for w in e})
    adj = {frozenset(e) for e in sk}
    return [(u, v) for (u, v) in itertools.combinations(hubs, 2)
            if frozenset((u, v)) not in adj]


def block_row(skname, prof, xy, s1name, s1E, rng, ndraw=3):
    """Generic block profile of BOTH sides on the WHOLE-`H` flag, over
    `ndraw` FREE draws.  Returns None off the region."""
    x, y = xy
    try:
        E, E1, E2, x, y = bproper.composite(skname, list(prof), xy, s1E)
    except Exception:
        return None
    if len({frozenset(e) for e in E}) != len(E):
        return None
    nbH = neighbors(E)
    if y in nbH.get(x, ()):
        return None
    if len(nbH.get(x, ())) < 3 or len(nbH.get(y, ())) < 3:
        return None
    if min(len(v) for v in nbH.values()) < 2 or girth(E) < 4:
        return None
    if not hcard_ok_piece(E, x, y):
        return None
    if not rnode_shaped(E2, x, y):
        return None
    if len(neighbors(E1).get(x, ())) < 2 or len(neighbors(E2).get(x, ())) < 2:
        return None
    if len(neighbors(E1).get(y, ())) < 2 or len(neighbors(E2).get(y, ())) < 2:
        return None
    d1, d2 = delta_of(E1, x, y), delta_of(E2, x, y)
    if d1 + d2 > 6:
        return None
    cmin = [None, None]
    rmax = [0, 0]
    amin = [99, 99]
    reach = -1
    nd = 0
    for _s in range(ndraw * 6):
        if nd == ndraw:
            break
        got = bproper.free_peel(skname, list(prof), xy, s1E, rng)
        if got is None:
            continue
        _E, _E1, _E2, _x, _y, aff = got
        fr = bunif.flag_frame(_E, aff, x, y)
        if fr is None:
            continue
        B = bunif.blocks_of(fr)
        prof_ok = True
        cs, rs, As, Ss = [], [], [], []
        for side in (_E1, _E2):
            try:
                S, rho, dM, _r = rho_bar_of(side, aff, x, y)
            except AssertionError:
                prof_ok = False
                break
            f = d3(side)
            cs.append(bunif.profile(S, B))
            rs.append(rho)
            As.append(dM - 6 - f)
            Ss.append(S)
        if not prof_ok:
            continue
        nd += 1
        Ssum = span((Ss[0] or []) + (Ss[1] or []))
        reach = max(reach, dim(Ssum))
        for i in (0, 1):
            rmax[i] = max(rmax[i], rs[i])
            amin[i] = min(amin[i], As[i])
            cmin[i] = dict(cs[i]) if cmin[i] is None else {
                u: min(cmin[i][u], cs[i][u]) for u in cs[i]}
    if nd == 0 or cmin[0] is None:
        return None
    slack = max(0, d1 + d2 - 6)
    margin, arg = -99, None
    for sub in bunif.SUBS:
        du = sum(bunif.CAP[b] for b in sub)
        val = cmin[0][sub] + cmin[1][sub] - du - slack
        if val > margin:
            margin, arg = val, sub
    cap, capU = bunif.blockcap(cmin[0], cmin[1], rmax[0], rmax[1])
    deg, _dg = bunif.blockdeg(cmin[0], cmin[1], rmax[0], rmax[1])
    tag = f'{skname}{tuple(prof)}|{xy}|{s1name}'
    return dict(tag=tag, d=(d1, d2), r=tuple(rmax), a=tuple(amin),
                reach=reach, margin=margin, arg=arg, cap=cap, capU=capU,
                deg=deg, nd=nd, cPix=(cmin[0][('Pix',)], cmin[1][('Pix',)]),
                cM=(cmin[0][('M',)], cmin[1][('M',)]),
                cPiy=(cmin[0][('Piy',)], cmin[1][('Piy',)]),
                target=min(d1 + d2, 6))


def run_block(ndraw=3, seed=SEED, maxlen=5, njob=None, quick=False):
    t0 = time.time()
    print(f'== block: the TWO-SIDED hunt on the whole-`H` flag, seed {seed}, '
          f'ndraw {ndraw}')
    print('  A generic-profile margin > 0 at any of the 16 stable `U` is a')
    print('  shortfall by (BE-95)(i) -- a THEOREM at that configuration, and')
    print('  EVIDENCE for `Good = EMPTY` when it survives every free draw.')
    print(f'  Branch lengths run to {maxlen} (the landed `constructed_tier`')
    print('  default is 4 and `bunif.tier_rows` uses 3); every non-adjacent')
    print('  hub pair is used (`bproper.NONADJ` lists 3 of 6).')
    rng = random.Random(seed)
    lib = side1_library()
    if quick:
        lib = lib[::4]
    jobs = []
    for skname in ('K33', 'prism'):
        pairs = nonadj_pairs(skname)
        n = len(SKELETONS[skname])
        for d2 in (2, 3, 4):
            k = 6 + d2
            if k > n:
                continue
            base = [2] * (n - k) + [3] * k
            profs = [base]
            for _ in range(2 if not quick else 1):
                profs.append([rng.randint(2, maxlen) for _ in range(n)])
            for prof in profs:
                for xy in pairs:
                    for (s1name, s1E) in lib:
                        jobs.append((skname, tuple(prof), xy, s1name, s1E))
    rng2 = random.Random(seed + 99)
    rng2.shuffle(jobs)
    if njob:
        jobs = jobs[:njob]
    rows, hits, mh, tuples = 0, [], {}, {}
    ch = {}
    for (skname, prof, xy, s1name, s1E) in jobs:
        r = block_row(skname, prof, xy, s1name, s1E, rng, ndraw=ndraw)
        if r is None:
            continue
        rows += 1
        mh[r['margin']] = mh.get(r['margin'], 0) + 1
        ch[r['cPix']] = ch.get(r['cPix'], 0) + 1
        key = (r['d'], r['a'], r['r'], r['cPix'])
        tuples[key] = tuples.get(key, 0) + 1
        assert r['deg'] <= r['reach'] <= r['cap'], \
            ('the (BE-96)(i)/(BE-95)(i) bracket FAILS', r)
        if r['margin'] > 0 or r['reach'] < r['target'] + sum(r['a']):
            hits.append(r)
    print(f'  in-region rows {rows}   (jobs offered {len(jobs)})')
    print(f'  margin histogram over the 16 stable U: {dict(sorted(mh.items()))}')
    print(f'  `(c_1, c_2)` at `Pi_x`, generic over free draws: '
          f'{dict(sorted(ch.items()))}')
    print(f'  distinct (delta, a, rho, c(Pi_x)) tuples: {len(tuples)}')
    for k in sorted(tuples, key=lambda z: -tuples[z])[:8]:
        print(f'     {k} x{tuples[k]}')
    if hits:
        print(f'  !! {len(hits)} rows with a generic shortfall:')
        for h in hits[:10]:
            print(f'     {h}')
    else:
        print('  0 rows with a generic shortfall.  NOT FOUND under this cap.')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, hits


# ===================================================== mode: pix

def alpha_plane(pt, x):
    """`alpha_x = p_x ^ K^4`, the 3-dimensional space of screws whose
    decomposable members are the LINES THROUGH `p_x`.  `Pi_x = alpha_x cap
    Lambda^2 pi_x`, so `Pi_x <= alpha_x` and `dim(V cap alpha_x)` is an
    UPPER bound on `c(Pi_x)` for every `V`."""
    px = hat(pt[x])
    return span([wedge2(px, hat(tuple(F(1) if j == i else F(0)
                                      for j in range(3))))
                 for i in range(3)] + [wedge2(px, (F(0), F(0), F(0), F(1)))])


def alpha_of(pt, x):
    px = hat(pt[x])
    basis = [(F(1), F(0), F(0), F(0)), (F(0), F(1), F(0), F(0)),
             (F(0), F(0), F(1), F(0)), (F(0), F(0), F(0), F(1))]
    return span([wedge2(px, b) for b in basis])


def run_pix(ndraw=3, seed=SEED, maxarc=8, maxtheta=7):
    """THE `Pi_x` LEMMA.  For every side and every x--y path `P_0`,
    `rho_bar_i <= <P_0>` ((BE-30)(iv), pointwise).  `Pi_x = alpha_x cap
    Lambda^2 pi_x <= alpha_x` with `alpha_x := p_x ^ K^4`, so

        c_i(Pi_x) <= dim(rho_bar_i cap alpha_x) <= dim(<P_0> cap alpha_x).

    `alpha_x` is the KERNEL of `phi: omega |-> omega ^ p_x`, whose image is
    `p_x ^ Lambda^2 K^4 = Lambda^2(K^4 / p_x)`: so **`rank phi = 3`,
    exactly**, and `dim(<P_0> cap alpha_x) = d - rank(phi restricted to
    <P_0>) >= d - 3` for `d = dim <P_0> <= dist_i(x, y)`.  Since
    `l_1 = p_x ^ p_1` is always in the kernel the restricted rank is at most
    `d - 1`, and generically it is exactly `min(3, d - 1)`, i.e.

        generic dim(<P_0> cap alpha_x) = max(1, d - 3).

    *** FIRST-RUN CORRECTION, and the assert is what caught it.  This
    direction first wrote "the `d - 1` vectors `p_{j-1} ^ p_j ^ p_x` are
    generically INDEPENDENT for `d <= 5`, so the kernel is `<l_1>`" -- which
    is false: they all lie in the 3-dimensional `p_x ^ Lambda^2 K^4`, so the
    rank saturates at 3 and the bound is `max(1, d-3)`, not `1`.  The run
    reported `(dist, alpha) = (5, 2)` at 22 rows and `(6, 3)` / `(7, 3)` at
    41, which is `max(1, d-3)` and not `1`.  The consequence below is stated
    at the CORRECTED threshold `dist_i <= 4`. ***

    So: PROVED -- `dist_i(x, y) <= 4` gives generic `c_i(Pi_x) <= 1`.
    MEASURED -- at `dist_i = 5` the alpha-bound allows `2` and `c_i(Pi_x)`
    is nonetheless `<= 1` at every row, because the second kernel vector
    must additionally lie in `Lambda^2 pi_x`; and at `dist_i >= 6`, where
    `dim <P_0> = 6` makes the confinement vacuous, `c_i(Pi_x)` agrees with
    the GENERAL-POSITION value `bunif.generic_c(rho_i, 2) = max(0, rho_i-4)`
    at every row, so `c_i(Pi_x) = 2` there iff `rho_i = 6`.

    Consequence at rung 3 (`Sigma_delta <= 6`, `slack = 0`), which is the
    point of the mode: a `Pi_x`-block obstruction needs `c_1 + c_2 >= 3`,
    hence `c_i(Pi_x) = 2` on a side, hence (measured, at every row of this
    population) `rho_i = 6`, hence `delta_i = 6` and `delta_j = 0` -- side
    `j` is RIGID, `rho_j = 0`, `c_j(Pi_x) = 0` by (BE-22)(vi).  So
    `c_1(Pi_x) + c_2(Pi_x) <= 2 = dim Pi_x`: margin 0 at `Pi_x`, never
    positive, and `Pi_x` CANNOT be the binding block of a `Good = EMPTY`
    piece at rung 3.  The same at `Pi_y` by the x/y symmetry of every
    ingredient.  This upgrades (BE-250)(iii)'s 6-of-6 free-draw control on
    BWHOLEH's own `H` -- whose side 1 is the (4,4) cycle, `dist_1 = 4` --
    from a measurement to the PROVED half of the statement."""
    t0 = time.time()
    print(f'== pix: the `Pi_x` lemma -- `c_i(Pi_x) <= 1` when `dist_i <= 4` '
          f'(PROVED), `= 2` only at `rho_i = 6` (MEASURED), seed {seed}')
    rows, hist, hist_a, big = 0, {}, {}, []
    lib = list(side_library(maxarc, maxtheta, 40, seed))
    lib += [(nm, E, 'x', 'y') for (nm, E) in side1_library()]
    for (tag, E, x, y) in lib:
        d = delta_of(E, x, y)
        dd = dist_of(E, x, y)
        paths, _tr = xy_paths(E, x, y, cap=400, maxlen=9)
        short = [P for P in paths if len(P) == dd]
        if not short:
            continue
        cmin_pix, cmin_alpha, cmin_rho, seen = 9, 9, 9, 0
        for s in range(ndraw):
            rng = random.Random(seed + 733 * s + len(E))
            got = sample_by_branches(E, x, y, rng)
            if got is None:
                continue
            pt = got[0] if isinstance(got, tuple) else got
            try:
                S, rho, _dM, _r = rho_bar_of(E, pt, x, y)
            except AssertionError:
                continue
            Bx = plane_at(E, pt, x)
            if Bx is None:
                continue
            Pix = span([wedge2(hat(pt[x]), b) for b in Bx])
            if dim(Pix) != 2:
                continue
            al = alpha_of(pt, x)
            assert dim(al) == 3, 'alpha_x is not 3-dimensional'
            assert dim(isect(Pix, al)) == 2, 'Pi_x is not inside alpha_x'
            P0 = span([wedge2(hat(pt[a]), hat(pt[b])) for (a, b) in short[0]])
            cpix = dim(isect(S, Pix)) if S else 0
            calpha = dim(isect(P0, al))
            assert cpix <= calpha, ('the Pi_x <= alpha_x chain FAILS',
                                    tag, cpix, calpha)
            assert calpha >= max(1, dim(P0) - 3), \
                ('the rank-3 floor on `<P_0> cap alpha_x` FAILS',
                 tag, dim(P0), calpha)
            assert cpix <= 2, 'c(Pi_x) exceeds dim Pi_x'
            if cpix == 2:
                assert rho == 6, \
                    ('!! c(Pi_x) = 2 with rho < 6 -- the shape a rung-3 '
                     '`Good = EMPTY` needs', tag, rho, dd, d)
            assert (dim(isect(S, P0)) == rho) if S else True, \
                ('(BE-30)(iv) fails at the shortest path', tag)
            seen += 1
            cmin_pix = min(cmin_pix, cpix)
            cmin_alpha = min(cmin_alpha, calpha)
            cmin_rho = min(cmin_rho, rho)
        if seen == 0:
            continue
        rows += 1
        hist[(min(dd, 7), cmin_pix)] = hist.get((min(dd, 7), cmin_pix), 0) + 1
        hist_a[(min(dd, 7), cmin_alpha)] = \
            hist_a.get((min(dd, 7), cmin_alpha), 0) + 1
        if cmin_pix == 2 and cmin_rho < 6:
            big.append((tag, dd, d, cmin_pix, cmin_alpha, cmin_rho))
    print(f'  rows {rows}')
    print(f'  (dist, generic c(Pi_x)) -> count: {dict(sorted(hist.items()))}')
    print(f'  (dist, generic dim(<P_0> cap alpha_x)) -> count: '
          f'{dict(sorted(hist_a.items()))}')
    if big:
        print(f'  !! {len(big)} rows with generic `c(Pi_x) = 2` and '
              f'`rho < 6` -- the rung-3 `Good = EMPTY` shape:')
        for b in big[:10]:
            print(f'     {b}')
    else:
        print('  0 rows with generic `c(Pi_x) = 2` and `rho < 6`.  Every')
        print('  `c(Pi_x) = 2` row has `rho = 6`, hence `delta = 6`, hence')
        print('  a RIGID other side at rung 3 and `c_j(Pi_x) = 0`.  So the')
        print('  `Pi_x` margin is 0 and never positive here.')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, big


# ===================================================== mode: sweep

def run_sweep(ndraw=5, seed=SEED, njob=60, maxlen=5, quick=False):
    """The spec's TELL: shortfall at several independent FREE draws.  A
    POINTER -- `dim(rho_bar_1+rho_bar_2)` is LOWER semicontinuous, so a draw
    is a lower bound and a measured shortfall is not a generic one."""
    t0 = time.time()
    print(f'== sweep: the spec\'s TELL, {ndraw} independent FREE draws per '
          f'piece, seed {seed}')
    print('  Reported as a POINTER and never as a result ((BE-69)(ii)(2)).')
    rng = random.Random(seed + 5)
    lib = side1_library()
    jobs = []
    for skname in ('K33', 'prism'):
        n = len(SKELETONS[skname])
        for xy in nonadj_pairs(skname):
            for d2 in (2, 3, 4):
                k = 6 + d2
                if k > n:
                    continue
                prof = tuple([2] * (n - k) + [3] * k)
                for (s1name, s1E) in lib:
                    jobs.append((skname, prof, xy, s1name, s1E))
    random.Random(seed + 3).shuffle(jobs)
    jobs = jobs[:njob]
    rows, allgood, fired = 0, 0, []
    for (skname, prof, xy, s1name, s1E) in jobs:
        r = block_row(skname, prof, xy, s1name, s1E, rng, ndraw=ndraw)
        if r is None:
            continue
        rows += 1
        short = r['target'] + sum(r['a']) - r['reach']
        if short <= 0:
            allgood += 1
        else:
            fired.append((r['tag'], r['d'], r['a'], r['reach'], short, r['nd']))
    print(f'  in-region pieces {rows};  `reach` attains the target at '
          f'{allgood} of {rows}')
    if fired:
        print(f'  !! the tell FIRED at {len(fired)} pieces (pointer only):')
        for f_ in fired[:12]:
            print(f'     {f_}')
    else:
        print('  the tell did NOT fire: every piece reaches its target at the')
        print(f'  maximum over {ndraw} independent free draws.  So the region')
        print('  offers no pointer to aim a structural argument at.')
    print(f'  [{time.time() - t0:.1f}s]')
    return rows, fired


# ===================================================== validate

def run_validate():
    run_mech()
    print()
    run_dist(maxarc=6, maxtheta=5, maxlen=3, nsamp=30, nrand=40)
    print()
    run_conf(ndraw=2, maxarc=6, maxtheta=5, quick=True)
    print()
    run_pix(ndraw=2, maxarc=6, maxtheta=5)
    print()
    run_block(ndraw=2, njob=40, quick=True)


MODES = {'mech': run_mech, 'dist': run_dist, 'conf': run_conf,
         'block': run_block, 'sweep': run_sweep, 'pix': run_pix}


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    if mode == 'validate':
        run_validate()
    elif mode in MODES:
        MODES[mode]()
    else:
        print(f'usage: bgoodempty.py [{"|".join(sorted(MODES))}|validate]')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
