"""BSIGFOUR (ordinal 118) -- is a FORCED coincident-flag peel at Sigma-delta
>= 4 INHABITED, and if so does the confinement of (BE-310)(i) survive there?

THE QUESTION, and why it is the only POSITIVE route to (BE-14) on the
forced lane.  (BE-310)(i) (owning section BCOFLAG) proves that at a forced
coincident-flag peel with a u--v path of each side inside the forced set A,
both rho_bar_i lie in Lambda^2 pi, a maximal totally singular 3-space, so
dim(rho_bar_1 + rho_bar_2) <= 3.  (BE-86)(i) (owning section BGENUINE) is
the unconditional criterion: H attains IFF that dimension equals
min(delta_1+delta_2, 6) + a_1 + a_2, and the left side never exceeds the
right.  So at Sigma-delta >= 4 the peel CANNOT attain -- a shortfall, which
by (BE-69)(ii) (owning section BPEEL) holds identically on Chart(H).
(BE-311)(ii) is that kill condition, and it is OPEN because BONEONE's
generator is (1,1)-only: `k4_rsides` and `free_sides` both carry a fenced
`side_delta(...)[2] == 1` filter, so the whole 392-member corpus sits at
Sigma-delta = 2 and the region has never been SAMPLED, let alone measured
empty.  (BE-311)(ii) names the instrument in terms: "a (delta_1, delta_2)-
widened generator is the cheapest next instrument".  This driver is it.

WHAT IS UN-FENCED HERE, and how.  `boneone.k4_rsides(n)` and
`boneone.free_sides(n)` each end in `if side_delta(E)[2] == 1`.  This driver
does NOT copy their bodies: it imports `boneone.rside`, `boneone.side_delta`,
`boneone._comps` and re-runs the SAME enumeration with the delta filter as a
PARAMETER (`rsides_at`, `free_sides_at`), and mode `fence` asserts that at
delta = 1 the widened pools reproduce `k4_rsides` / `free_sides` element for
element.  The landed functions are the oracle for their own special case.
The recommended permanent fix is a `delta=1` keyword on both landed
functions; until that lands, `fence` is the figure-invariance test.

CAPS, and they travel with every figure this driver prints.
  * R-node pool: EVERY branch profile of the K4 skeleton at n_1 <= RCAP
    (default 12), exhaustive per n.  A K4 R-node side first reaches
    delta = 4 at n_1 = 12 (6 profiles), delta = 5 at 13, delta = 6 at 14.
  * free pool: EVERY side at n_2 <= FCAP (default 5), exhaustive per n
    (the 2^(C(n,2)-1) mask enumeration of `boneone.free_sides`).  n_2 = 6
    is 7 032 sides and is available with --fcap 6 at ~20x the glue cost.
  * The R-node shape is required on SIDE 1 only -- the `or` reading
    (BE-79)(ii) settles as the one the consumer can supply.
  * tier B (mode `rand`) is a SEEDED random tier over 2-connected graphs,
    not exhaustive; its seed is SEED and its size is NRAND.
A zero from any mode reads "not found under cap C", never "does not exist".

MODES
  fence  -- the un-fencing is faithful: widened pools at delta = 1 equal the
            landed `k4_rsides` / `free_sides`, element for element.
  theory -- the SECOND-TERMINAL DICHOTOMY, enumerated on the live closure:
            at every forced peel of the widened generator, classify v's
            witness split (c_1, c_2) and check the sharpened reading of
            (BE-77)(ii) that this direction derives (see (BE-324)).
  widen  -- THE HUNT.  Every glued pair of the widened generator, with the
            (delta_1, delta_2) profile of the forced ones and the (BE-310)(i)
            confinement test on both sides.
  rand   -- an independent tier: seeded random 2-connected graphs, every
            2-cut, same three tests.  Guards against the factorized
            generator being itself the fence.
  cover  -- a NECESSARY per-side condition for the confinement (`A` is a
            union of closed stars of HUBS), swept over three tiers.
  reach  -- the TIGHT per-side necessary condition `side_reach`, which
            bounds `A ∩ V(H_i)` from above at EVERY glue.  This is the mode
            that makes the none-found glue-independent, and its zero at
            `delta >= 4` is (BE-333)(ii)'s bound, measured.
  w9alt  -- the UNREAD blind axis `boneone.W9_ALT`, re-derived with the axis
            opened: what it is, and whether consuming it would move
            (BE-85)(iii)'s girth finding.

RUN ORDER for a re-verification: `fence` (1 s, the un-fencing and the
(BE-79)(i) re-assertion), `widen` (15 s, the hunt), `blame` (4 s, the
(BE-77)(ii) refutation), `theory` (18 s, the witness-split census), `reach`
(minutes, the glue-independent sweep), `cover`, `w9alt`, `rand` (the only
mode that has not been run to completion -- see (BE-331)(i)).
"""

import os
import sys
import time
import random
import itertools

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import neighbors                                    # noqa: E402
from kbare_common import verts_of, exact_deficiency                # noqa: E402
from binduc import vertex_connectivity_at_least, split_at_pair     # noqa: E402
from btwocut import deltas_at                                      # noqa: E402
from bpeel import rnode_shaped, hubs_of                            # noqa: E402
from bspread import closure_trace                                  # noqa: E402
from bcoflag import _path_in                                       # noqa: E402
from boneone import U, V, rside, side_delta, _comps                # noqa: E402
import boneone as _bone                                            # noqa: E402

SEED = 20260913
RCAP = 12                # exhaustive K4 branch profiles up to n_1 = RCAP
FCAP = 5                 # exhaustive free sides up to n_2 = FCAP
NRAND = 400              # seeded random graphs in tier B
MODES = {}


# ===================================================== the widened pools

def rsides_at(n, deltas=None, tag='A'):
    """`boneone.k4_rsides(n)` with the `delta == 1` fence REMOVED.  Same
    enumeration, same two oracles; `deltas` is a set of admitted delta
    values, or None for all.  Returns [(L, H, delta)]."""
    out = []
    for c in _comps(n - 4, 5):
        L = tuple(k + 1 for k in c)
        H = rside(L, tag)
        assert len(verts_of(H)) == n, ('size', n, L)
        d = side_delta(H)[2]
        if deltas is not None and d not in deltas:
            continue
        assert rnode_shaped(H, U, V), ('not R-node-shaped', L)
        out.append((L, H, d))
    return out


def free_sides_at(n, deltas=None, tag='B'):
    """`boneone.free_sides(n)` with the `delta == 1` fence REMOVED.  Every
    simple graph on {u, v} + (n-2) interior vertices with u !~ v, connected,
    both terminals of degree >= 1, H + uv 2-connected.  Returns [(H, delta)]."""
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
        d = side_delta(E)[2]
        if deltas is not None and d not in deltas:
            continue
        out.append((E, d))
    return out


def run_fence(rcap=RCAP, fcap=FCAP):
    """The un-fencing is FAITHFUL: at delta = 1 the widened pools reproduce
    the landed generators element for element.  This is the figure-invariance
    test the core discipline asks for when a hardcoded constant is opened."""
    t0 = time.time()
    print('===== mode `fence`: the widened pools agree with the landed '
          'generators at delta = 1 =====')
    ok = 0
    for n in (9, 10):
        mine = [(L, H) for (L, H, d) in rsides_at(n, {1})]
        land = _bone.k4_rsides(n, 'A')
        assert mine == land, ('k4_rsides mismatch', n)
        print(f'      k4_rsides({n})   : {len(land):4d} sides, identical')
        ok += 1
    for n in (4, 5):
        mine = [E for (E, d) in free_sides_at(n, {1})]
        land = _bone.free_sides(n, 'B')
        assert mine == land, ('free_sides mismatch', n)
        print(f'      free_sides({n})  : {len(land):4d} sides, identical')
        ok += 1
    print(f'  {ok} / 4 pools identical to the landed function at delta = 1.')
    print('  So every figure below differs from BONEONE\'s ONLY by the '
          'delta filter.')
    print()
    print('  The delta profile of each widened pool (the region BONEONE\'s')
    print('  fence hid).  CAP: R-node exhaustive to n_1 = '
          f'{rcap}, free exhaustive to n_2 = {fcap}.')
    for n in range(4, rcap + 1):
        prof = {}
        for (_L, _H, d) in rsides_at(n):
            prof[d] = prof.get(d, 0) + 1
        print(f'      K4 R-node side n = {n:2d}: {dict(sorted(prof.items()))}')
    for n in range(4, fcap + 1):
        prof = {}
        for (_E, d) in free_sides_at(n):
            prof[d] = prof.get(d, 0) + 1
        print(f'      free side     n = {n:2d}: {dict(sorted(prof.items()))}')
    print()
    print('  (BE-79)(i) RE-ASSERTED OUTSIDE ITS OWN delta.  BONEONE asserts')
    print('  the factorization at 400 / 400 glued pairs, every one at')
    print('  delta = 1.  The widened generator relies on it at every delta,')
    print('  so it is re-run here across the widened range: for a seeded')
    print('  sample of glues, `btwocut.deltas_at(G, u, v, check=True)` must')
    print('  agree side-for-side with each side\'s own `side_delta`.')
    rng = random.Random(SEED)
    pool_r = [(H, d) for n in range(4, rcap + 1) for (_L, H, d)
              in rsides_at(n)]
    pool_f = [(E, d) for n in range(4, fcap + 1) for (E, d)
              in free_sides_at(n)]
    seen = {}
    for _ in range(600):
        (H1, d1) = rng.choice(pool_r)
        (H2, d2) = rng.choice(pool_f)
        cd = deltas_at(H1 + H2, U, V, check=True)
        f1, g1, f2, g2 = cd[2], cd[3], cd[6], cd[7]
        assert (f1, g1) == side_delta(H1)[:2], ('side 1 disagrees', f1, g1)
        assert (f2, g2) == side_delta(H2)[:2], ('side 2 disagrees', f2, g2)
        seen[(d1, d2)] = seen.get((d1, d2), 0) + 1
    print(f'      600 / 600 seeded glues agree side-for-side; the '
          f'(delta_1, delta_2) cells hit: {dict(sorted(seen.items()))}')
    print(f'  [{time.time() - t0:.1f} s]')


MODES['fence'] = run_fence


# ====================================================== the glue + the tests

def glue(H1, H2):
    return list(H1) + list(H2)


def forced_seeds(G):
    """EVERY hub whose aggressive closure admits BOTH terminals, with its
    trace.  `bgenuine.forced_seed` returns one (preferring a hinge-pure
    derivation); the confinement question is about the SET A, and different
    seeds give different A, so a hunt for the confinement must try them all.
    Growth rule is `bspread.closure_trace`, byte-for-byte
    `bpeel.pair_forced`'s."""
    nb = neighbors(G)
    hb = hubs_of(G, nb)
    if U not in hb or V not in hb:
        return []
    out = []
    for h in hb:
        A, adm, tr = closure_trace(nb, hb, h)
        if U in adm and V in adm:
            out.append((h, set(A), set(adm), tr))
    return out


def confined(H1, H2, A):
    """(BE-310)(i)'s combinatorial hypothesis, per side: a u--v path of the
    side all of whose vertices lie in A.  `bcoflag._path_in` verbatim."""
    return (_path_in(H1, A, U, V), _path_in(H2, A, U, V))


def witness_split(G, H1, H2, tr):
    """The SECOND terminal's witness split (c_1, c_2) of (BE-77)(ii)'s proof,
    read off the live trace: c_i = |N_{H_i}[second] ∩ (A_i at its admission)|.
    Returns (second, c1, c2) or None if the trace does not admit both."""
    nb = neighbors(G)
    V1, V2 = set(verts_of(H1)), set(verts_of(H2))
    nb1, nb2 = neighbors(H1), neighbors(H2)
    seen = []
    for (z, wit) in tr:
        if z in (U, V):
            seen.append((z, set(wit)))
    if len(seen) < 2:
        return None
    second, wit = seen[1]
    star1 = ({second} | set(nb1.get(second, ()))) & V1
    star2 = ({second} | set(nb2.get(second, ()))) & V2
    assert len(wit) >= 3, ('admission under threshold', wit)
    del nb
    return (second, len(wit & star1), len(wit & star2))


def _dist(E):
    """dist_{H_i}(u, v) inside the side.  The combinatorial companion of
    (BE-30)(iv)'s bound: this direction proves delta_i <= dist_i outright
    (see (BE-327)), with no attainment proviso, and the confinement needs a
    u--v path INSIDE A, so its length is >= dist."""
    nb = neighbors(E)
    seen, q = {U: 0}, [U]
    while q:
        w = q.pop(0)
        for z in nb.get(w, ()):
            if z not in seen:
                seen[z] = seen[w] + 1
                q.append(z)
    return seen.get(V)


def _peel_row(H1, H2, d1=None, d2=None, r1=None, r2=None,
              want_rnode_side1=True):
    """One glued pair, fully tested.  Returns a dict or None if the glue is
    not a legal peel.  `d_i` / `r_i` are the side's OWN delta and R-node
    verdict; they are per-side by (BE-79)(i) and so are passed in from the
    pool rather than recomputed per glue (the oracles are the expensive
    part).  Passing None recomputes them, which is what `rand` does."""
    G = glue(H1, H2)
    n = len(verts_of(G))
    d1 = side_delta(H1)[2] if d1 is None else d1
    d2 = side_delta(H2)[2] if d2 is None else d2
    r1 = rnode_shaped(H1, U, V) if r1 is None else r1
    r2 = rnode_shaped(H2, U, V) if r2 is None else r2
    if want_rnode_side1 and not (r1 or r2):
        return None
    seeds = forced_seeds(G)
    row = {'n': n, 'd1': d1, 'd2': d2, 'r1': r1, 'r2': r2,
           'forced': bool(seeds), 'conf': False, 'confseeds': 0,
           'nseeds': len(seeds), 'splits': [], 'G': G,
           'p1': None, 'p2': None, 'dist1': _dist(H1), 'dist2': _dist(H2)}
    for (_h, A, _adm, tr) in seeds:
        P1, P2 = confined(H1, H2, A)
        if P1 is not None:
            row['p1'] = max(row['p1'] or 0, len(P1) - 1)
        if P2 is not None:
            row['p2'] = max(row['p2'] or 0, len(P2) - 1)
        if P1 and P2:
            row['conf'] = True
            row['confseeds'] += 1
        sp = witness_split(G, H1, H2, tr)
        if sp is not None:
            row['splits'].append(sp[1:])
    return row


def run_widen(rcap=RCAP, fcap=FCAP, verbose=True):
    """THE HUNT.  Every glued pair of the (delta_1, delta_2)-widened
    factorized generator; the (delta_1, delta_2) profile of the FORCED ones;
    and (BE-310)(i)'s confinement on both sides wherever forced."""
    t0 = time.time()
    print('===== mode `widen`: the (delta_1, delta_2)-WIDENED factorized '
          'generator =====')
    print(f'  CAPS: K4 R-node sides exhaustive at n_1 = 4..{rcap}; free '
          f'sides exhaustive at n_2 = 4..{fcap};')
    print('        R-node shape required on at least one side (the `or` '
          'reading of (BE-79)(ii)).')
    R = {}
    for n in range(4, rcap + 1):
        R[n] = rsides_at(n)
    Fr = {}
    for n in range(4, fcap + 1):
        Fr[n] = free_sides_at(n)
    rfree = {}
    for n in Fr:
        for (H2, _d) in Fr[n]:
            rfree[id(H2)] = rnode_shaped(H2, U, V)
    nR = sum(len(v) for v in R.values())
    nF = sum(len(v) for v in Fr.values())
    print(f'      pools: {nR} R-node sides, {nF} free sides  '
          f'[{time.time() - t0:.1f} s]')

    tot = forced = sig4 = f_sig4 = conf_sig4 = 0
    prof_all = {}
    prof_forced = {}
    prof_conf = {}
    hits = []
    viol77 = []
    why = {}
    dp = {}
    pd = {}
    for n1 in sorted(R):
        for (_L, H1, d1) in R[n1]:
            for n2 in sorted(Fr):
                for (H2, d2) in Fr[n2]:
                    row = _peel_row(H1, H2, d1, d2, True,
                                    rfree.get(id(H2)))
                    if row is None:
                        continue
                    tot += 1
                    key = (d1, d2)
                    prof_all[key] = prof_all.get(key, 0) + 1
                    if d1 + d2 >= 4:
                        sig4 += 1
                    if not row['forced']:
                        continue
                    forced += 1
                    prof_forced[key] = prof_forced.get(key, 0) + 1
                    if d1 >= 1 and d2 >= 1 and key != (1, 1):
                        viol77.append((n1, n2, key))
                    if d1 + d2 >= 4:
                        f_sig4 += 1
                        why[(key, row['p1'] is not None,
                             row['p2'] is not None)] = \
                            why.get((key, row['p1'] is not None,
                                     row['p2'] is not None), 0) + 1
                        if row['conf']:
                            conf_sig4 += 1
                            hits.append((n1, n2, key, row))
                    if row['conf']:
                        dp[(d1, row['p1'])] = dp.get((d1, row['p1']), 0) + 1
                        dp[(d2, row['p2'])] = dp.get((d2, row['p2']), 0) + 1
                    pd[(d1, row['dist1'], row['p1'])] = \
                        pd.get((d1, row['dist1'], row['p1']), 0) + 1
                    pd[(d2, row['dist2'], row['p2'])] = \
                        pd.get((d2, row['dist2'], row['p2']), 0) + 1
                    if row['conf']:
                        prof_conf[key] = prof_conf.get(key, 0) + 1

    print(f'  legal R-node-shaped peels tested : {tot}')
    print(f'      of them at Sigma-delta >= 4  : {sig4}')
    print(f'      FORCED (pi_u = pi_v)         : {forced}')
    print(f'      FORCED at Sigma-delta >= 4   : {f_sig4}')
    print(f'      FORCED + CONFINED at Sd >= 4 : {conf_sig4}   <-- '
          '(BE-311)(ii)\'s kill condition')
    print()
    print('  (delta_1, delta_2) profile of ALL tested peels:')
    print(f'      {dict(sorted(prof_all.items()))}')
    print('  (delta_1, delta_2) profile of the FORCED ones:')
    print(f'      {dict(sorted(prof_forced.items()))}')
    print('  (delta_1, delta_2) profile of FORCED + confined on BOTH sides:')
    print(f'      {dict(sorted(prof_conf.items()))}')
    print()
    print('  CONTROL -- (BE-77)(ii) says forced with BOTH sides flexible '
          'implies (1,1).')
    print(f'      forced rows with min(d1,d2) >= 1 and (d1,d2) != (1,1): '
          f'{len(viol77)}')
    if viol77:
        print(f'      VIOLATIONS: {viol77[:10]}')
    print()
    print('  WHY the kill condition misses: at Sigma-delta >= 4, which SIDE')
    print('  carries a u--v path inside A.  key = ((d1,d2), side1 ok, '
          'side2 ok):')
    for k in sorted(why, key=str):
        print(f'      {k} : {why[k]}')
    print()
    print('  (delta_i, confining path length) over CONFINED forced rows, '
          'per side:')
    print(f'      {dict(sorted(dp.items(), key=str))}')
    print()
    print('  (delta_i, dist_i(u,v), confining path length or None) over all '
          'FORCED rows, per side:')
    for k in sorted(pd, key=str):
        print(f'      {k} : {pd[k]}')
    print(f'  [{time.time() - t0:.1f} s]  rcap {rcap} fcap {fcap}')
    if verbose and hits:
        print()
        print('  HITS (the kill condition), first 5:')
        for (n1, n2, key, row) in hits[:5]:
            print(f'      n=({n1},{n2}) (d1,d2)={key} n={row["n"]}')
            print(f'      G = {sorted(map(tuple, row["G"]))}')
    return {'tot': tot, 'forced': forced, 'sig4': sig4, 'f_sig4': f_sig4,
            'conf_sig4': conf_sig4, 'prof_forced': prof_forced,
            'prof_conf': prof_conf, 'viol77': viol77, 'hits': hits}


MODES['widen'] = run_widen


# ====================================================== the theory mode

def run_theory(rcap=RCAP, fcap=FCAP):
    """THE SECOND-TERMINAL DICHOTOMY, enumerated on the live closure.
    (BE-77)(ii) proves: forced + both sides flexible ==> delta_1 = delta_2 = 1,
    via the witness split (c_1, c_2) of the SECOND terminal admitted, where
    c_i <= 2 on any side with delta_i >= 1 ((BE-74)(i) under (BE-74)(ii)'s
    block induction).  This direction's sharpening (see (BE-324)) reads the
    same three steps ONE SIDE AT A TIME, which the landed clause does not:
    if delta_i >= 1 then either c_i = 2 in the shape {v, b_i} -- and Step 3's
    merge gives delta_i <= 1 -- or c_i <= 1, which needs c_{3-i} >= 3 and by
    (BE-74)(i) forces delta_{3-i} = 0.  So at ANY forced peel,
    delta_i >= 2 for some i implies delta_{3-i} = 0 AND c_i <= 1.  This mode
    checks the (c_1, c_2) census against that claim over the widened
    generator, which is the first population that can even test it."""
    t0 = time.time()
    print('===== mode `theory`: the second terminal\'s witness split, '
          'enumerated =====')
    R, Fr = {}, {}
    for n in range(4, rcap + 1):
        R[n] = rsides_at(n)
    for n in range(4, fcap + 1):
        Fr[n] = free_sides_at(n)
    rfree = {}
    for n in Fr:
        for (H2, _d) in Fr[n]:
            rfree[id(H2)] = rnode_shaped(H2, U, V)
    census = {}
    bad_c = []
    bad_pair = []
    nforced = 0
    for n1 in sorted(R):
        for (_L, H1, d1) in R[n1]:
            for n2 in sorted(Fr):
                for (H2, d2) in Fr[n2]:
                    row = _peel_row(H1, H2, d1, d2, True,
                                    rfree.get(id(H2)))
                    if row is None or not row['forced']:
                        continue
                    nforced += 1
                    for (c1, c2) in row['splits']:
                        census[(d1, d2, c1, c2)] = \
                            census.get((d1, d2, c1, c2), 0) + 1
                        if d1 >= 1 and c1 >= 3:
                            bad_c.append((d1, d2, c1, c2))
                        if d2 >= 1 and c2 >= 3:
                            bad_c.append((d1, d2, c1, c2))
                        if d1 >= 2 and d2 >= 1:
                            bad_pair.append((d1, d2, c1, c2))
                        if d2 >= 2 and d1 >= 1:
                            bad_pair.append((d1, d2, c1, c2))
    print(f'  forced peels with a readable second-terminal trace: {nforced}')
    print('  (d1, d2, c1, c2) census over every forced seed:')
    for k in sorted(census):
        print(f'      {k} : {census[k]}')
    print()
    print('  CLAIM A  (BE-74)(i) per side: delta_i >= 1 ==> c_i <= 2.')
    print(f'      counterexamples: {len(bad_c)}')
    print('  CLAIM B  this direction\'s sharpening: delta_i >= 2 ==> '
          'delta_{3-i} = 0.')
    print(f'      counterexamples: {len(bad_pair)}')
    print(f'  [{time.time() - t0:.1f} s]')
    return census, bad_c, bad_pair


MODES['theory'] = run_theory


# ====================================================== the random tier

def _rand_2conn(rng, n, p):
    pairs = list(itertools.combinations(range(n), 2))
    for _ in range(60):
        E = [e for e in pairs if rng.random() < p]
        if len(verts_of(E)) != n:
            continue
        if not vertex_connectivity_at_least(n, E, 2):
            continue
        return E
    return None


def run_rand(nrand=NRAND, seed=SEED, nlo=9, nhi=12):
    """TIER B -- an independent, SEEDED random tier over 2-connected graphs,
    every 2-cut {u,v} with u !~ v and both sides carrying an interior vertex.
    NOT exhaustive and NOT the factorized generator, so it guards against the
    generator itself being the fence.  Caps: nrand graphs, n in [nlo, nhi],
    edge probability swept over three values, no max-degree filter (BPEEL's
    census 1 carried one, which (BE-77)(iv) records as why its R-node peels
    were rigid on one side)."""
    t0 = time.time()
    rng = random.Random(seed)
    print('===== mode `rand`: an independent SEEDED random tier =====')
    print(f'  CAPS: {nrand} graphs, n in [{nlo}, {nhi}], p in '
          '(0.22, 0.3, 0.4), no max-degree filter, seed '
          f'{seed}.  NOT exhaustive.')
    tot = forced = sig4 = f_sig4 = conf_sig4 = 0
    prof_forced, prof_conf, prof_all = {}, {}, {}
    viol77, hits = [], []
    for i in range(nrand):
        n = rng.randint(nlo, nhi)
        p = rng.choice((0.22, 0.3, 0.4))
        E = _rand_2conn(rng, n, p)
        if E is None:
            continue
        nb = neighbors(E)
        for (u, v) in itertools.combinations(sorted(nb), 2):
            if v in nb[u]:
                continue
            sp = split_at_pair(E, u, v)
            if sp is None:
                continue
            _V1, H1, _V2, H2 = sp
            V1 = set(verts_of(H1)) - {u, v}
            V2 = set(verts_of(H2)) - {u, v}
            if not V1 or not V2:
                continue
            ren = {u: U, v: V}
            A1 = [(ren.get(a, ('A', a)), ren.get(b, ('A', b))) for (a, b) in H1]
            A2 = [(ren.get(a, ('B', a)), ren.get(b, ('B', b))) for (a, b) in H2]
            r1, r2 = rnode_shaped(A1, U, V), rnode_shaped(A2, U, V)
            if not (r1 or r2):
                continue
            d1, d2 = side_delta(A1)[2], side_delta(A2)[2]
            row = _peel_row(A1, A2, d1, d2, r1, r2)
            if row is None:
                continue
            tot += 1
            key = (d1, d2)
            prof_all[key] = prof_all.get(key, 0) + 1
            if d1 + d2 >= 4:
                sig4 += 1
            if not row['forced']:
                continue
            forced += 1
            prof_forced[key] = prof_forced.get(key, 0) + 1
            if d1 >= 1 and d2 >= 1 and key != (1, 1):
                viol77.append((key, len(V1), len(V2)))
            if row['conf']:
                prof_conf[key] = prof_conf.get(key, 0) + 1
            if d1 + d2 >= 4:
                f_sig4 += 1
                if row['conf']:
                    conf_sig4 += 1
                    hits.append((key, row))
    print(f'  R-node-shaped peels tested       : {tot}')
    print(f'      at Sigma-delta >= 4          : {sig4}')
    print(f'      FORCED                       : {forced}')
    print(f'      FORCED at Sigma-delta >= 4   : {f_sig4}')
    print(f'      FORCED + CONFINED at Sd >= 4 : {conf_sig4}')
    print(f'  (d1,d2) profile, all tested : {dict(sorted(prof_all.items()))}')
    print(f'  (d1,d2) profile, forced     : {dict(sorted(prof_forced.items()))}')
    print(f'  (d1,d2) profile, confined   : {dict(sorted(prof_conf.items()))}')
    print(f'  (BE-77)(ii) control, violations: {len(viol77)}  {viol77[:8]}')
    if hits:
        print(f'  HITS: {[h[0] for h in hits[:8]]}')
    print(f'  [{time.time() - t0:.1f} s]')
    return {'tot': tot, 'forced': forced, 'sig4': sig4, 'f_sig4': f_sig4,
            'conf_sig4': conf_sig4, 'viol77': viol77, 'hits': hits,
            'prof_forced': prof_forced}


MODES['rand'] = run_rand


# ====================================================== the unread blind axis

def run_w9alt():
    """`boneone.W9_ALT = (1, 1, 4, 3, 1)` is declared and read NOWHERE
    (`blindaxes.py --imports notes/scripts/w4/boneone.py`: "read at UNREAD").
    Opened here rather than trusted."""
    t0 = time.time()
    print('===== mode `w9alt`: the UNREAD blind axis boneone.W9_ALT =====')
    for (name, L) in (('WIT11_LENGTHS', _bone.WIT11_LENGTHS),
                      ('W9_ALT', _bone.W9_ALT)):
        H = rside(L, 'A')
        f, g, d = side_delta(H)
        n = len(verts_of(H))
        nb = neighbors(H)
        tri = sorted({frozenset((a, b, c))
                      for a in nb for b in nb[a] for c in nb[b]
                      if c in nb[a] and len({a, b, c}) == 3})
        print(f'      {name:14s} = {L}: n = {n}, def_3 = {f}, g = {g}, '
              f'delta = {d}, R-node = {rnode_shaped(H, U, V)}')
        print(f'      {"":14s}   triangles: {len(tri)}  '
              f'{[tuple(sorted(map(str, t))) for t in tri]}')
    print()
    print('  READING.  Both n = 9 K4 R-node sides at delta = 1 carry a')
    print('  triangle, and it is the SAME one -- lengths uC = uD = CD = 1 in')
    print('  both profiles.  So consuming W9_ALT in place of WIT11_LENGTHS')
    print('  would NOT have moved (BE-85)(iii)\'s girth histogram {3: 392}')
    print('  nor its "0 / 392 satisfy (CH-1)" row: (BE-85)(iii) already')
    print('  proves the n_1 = 9 column is triangle-free at 0 / 12 by an')
    print('  arithmetic argument over ALL twelve profiles, and W9_ALT is')
    print('  one of the twelve.  The axis is unread because it is')
    print('  REDUNDANT, not because it was suppressed.')
    print(f'  [{time.time() - t0:.1f} s]')


MODES['w9alt'] = run_w9alt


# ============================ WHERE (BE-77)(ii) BREAKS, localized mechanically

def _partitions(xs):
    if not xs:
        yield []
        return
    x, rest = xs[0], xs[1:]
    for P in _partitions(rest):
        for i in range(len(P)):
            yield P[:i] + [[x] + P[i]] + P[i + 1:]
        yield [[x]] + P


def _pvalue(E, P):
    idx = {}
    for i, B in enumerate(P):
        for w in B:
            idx[w] = i
    d = sum(1 for (a, b) in E if idx[a] != idx[b])
    return 6 * (len(P) - 1) - 5 * d


def optimal_partitions(E):
    """EVERY optimal partition of a side, by brute force over all set
    partitions, scored with the SAME functional `kbare_common.exact_deficiency`
    maximizes: value(P) = 6(|P|-1) - 5 d(P).  Asserted against
    `exact_deficiency` so the brute force is checked, not trusted.  Bell(n),
    so n <= 9 only."""
    Vs = sorted(verts_of(E), key=str)
    assert len(Vs) <= 9, ('too big for brute force', len(Vs))
    best = None
    out = []
    for P in _partitions(Vs):
        val = _pvalue(E, P)
        if best is None or val > best:
            best, out = val, [P]
        elif val == best:
            out.append(P)
    assert best == exact_deficiency(E)[0], ('brute force disagrees with the '
                                            'landed oracle', best)
    return best, out


def _A_at_second_terminal(G, seed):
    """The closure set A AT THE MOMENT the SECOND terminal is admitted --
    which is the state (BE-77)(ii)'s Steps 1-2 reason about, not the final
    fixed point.  Replays `bspread.closure_trace`'s own trace: A starts at
    the seed's closed star and each recorded step unions in that vertex's
    closed star.  Returns None if the trace does not admit both terminals."""
    (h, _A, _adm, tr) = seed
    nb = neighbors(G)
    A = {h} | set(nb[h])
    order = [h] if h in (U, V) else []
    for (z, _wit) in tr:
        if z in (U, V):
            order.append(z)
            if len(order) == 2:
                return (A, order[0], order[1])
        A |= {z} | set(nb[z])
    return None


def run_blame(seed=SEED):
    """(BE-77)(ii) is REFUTED, and the defect is LOCALIZED to its Step 2.

    Step 1 concludes `A_i = U_{w in F_i} N_{H_i}[w]` with `F_i` inside `B_i`,
    the block of the FIRST terminal in an optimal partition of side `i`; Step
    2 then reads (BE-74)(i)'s bound on `A = B_i u N(B_i)` as a bound on
    `c_i := |N_{H_i}[t2] ∩ A_i|` and concludes `c_i = 2 ==> t2 has a
    neighbour b_i IN B_i`; Step 3 merges `[t2]` with `B_i` along that edge
    and gets `delta_i <= 1`.  But `A_i := A ∩ V(H_i)` also contains `t2`
    itself as soon as ANY admitted hub of the OTHER side is adjacent to it,
    and `t2` need not lie in `B_i u N(B_i)`.  Then `c_i = 2` in the shape
    `{t2, b_i}` with `b_i` in `N(B_i)` minus `B_i`, there is no edge
    and `delta_i <= 1` does not follow.

    What SURVIVES is the certificate shape, in the OPEN-neighbourhood form:
    with `c_i' := |N_{H_i}(t2) ∩ A_i|` (t2 itself excluded), (BE-74)(i) gives
    `c_i' <= 1` on every side with `delta_i >= 1`, so a 3-witness admission
    forces `t2 ∈ A` and `c_1' = c_2' = 1` -- the `{v, b_1, b_2}` shape, with
    NO claim that `b_i ∈ B_i`.  Both are checked below.

    CAPS: exhaustive over the cell `n_1 = 9`, `n_2 ∈ {4, 5}` of the widened
    generator (brute-force partitions need `n <= 9`: Bell(9) = 21 147), one
    forced seed per peel (`forced_seeds(...)[0]`, the same preference order
    `bgenuine.forced_seed` uses).  Not the whole generator."""
    t0 = time.time()
    print('===== mode `blame`: where (BE-77)(ii) breaks, mechanically =====')
    R9 = rsides_at(9)
    F = [(E, d) for n in (4, 5) for (E, d) in free_sides_at(n)]
    cache, tally = {}, {}
    shown = 0
    bad_open, bad_cert, ok_cert = 0, 0, 0
    for (_L, H1, d1) in R9:
        for (H2, d2) in F:
            row = _peel_row(H1, H2, d1, d2, True, rnode_shaped(H2, U, V))
            if row is None or not row['forced']:
                continue
            G = row['G']
            got = _A_at_second_terminal(G, forced_seeds(G)[0])
            if got is None:
                continue
            A, t1, t2 = got
            cert = []
            for (i, (Hi, di)) in enumerate(((H1, d1), (H2, d2)), start=1):
                Ai = set(A) & set(verts_of(Hi))
                nb = neighbors(Hi)
                ci = len(({t2} | set(nb.get(t2, ()))) & Ai)
                ci_open = len(set(nb.get(t2, ())) & Ai)
                cert.append((ci, ci_open))
                if di < 1:
                    continue
                if ci_open > 1:
                    bad_open += 1
                key = (id(Hi), t1)
                if key not in cache:
                    best, opts = optimal_partitions(Hi)
                    rec = []
                    for P in opts:
                        B = set(next(b for b in P if t1 in b))
                        rec.append((P, B | {y for x in B for y in nb[x]}, B))
                    cache[key] = rec
                rec = cache[key]
                cont = any(Ai <= NB for (_P, NB, _B) in rec)
                only_t2 = any(Ai - NB == {t2} for (_P, NB, _B) in rec)
                nbr_in_B = any(set(nb.get(t2, ())) & B for (_P, _NB, B) in rec)
                tally[(di, cont, only_t2, ci, ci_open, nbr_in_B)] = \
                    tally.get((di, cont, only_t2, ci, ci_open, nbr_in_B), 0) + 1
                if di >= 2 and ci == 2 and not nbr_in_B and shown < 2:
                    shown += 1
                    print(f'      THE BREAK, side {i}, delta_i = {di}, '
                          f'(t1, t2) = ({t1}, {t2})')
                    print(f'        H_i = '
                          f'{sorted(tuple(sorted(map(str, e))) for e in Hi)}')
                    print(f'        A_i = {sorted(map(str, Ai))}   '
                          f'c_i = {ci}, c_i\' = {ci_open}')
                    for (P, NB, B) in rec:
                        print('        optimal P = '
                              f'{[sorted(map(str, b)) for b in P]}; '
                              f'B_i = {sorted(map(str, B))}; '
                              f'B_i u N(B_i) = {sorted(map(str, NB))}; '
                              f'A_i minus that = {sorted(map(str, Ai - NB))}')
                    print(f'        t2 has a neighbour in B_i? {nbr_in_B}  '
                          '<-- Step 3 needs this and it is FALSE')
            tot = cert[0][1] + cert[1][1] + (1 if t2 in A else 0)
            if d1 >= 1 and d2 >= 1:
                if cert[0][1] == 1 and cert[1][1] == 1 and t2 in A:
                    ok_cert += 1
                else:
                    bad_cert += 1
            assert tot >= 3 or d1 < 1 or d2 < 1, ('witness count', tot)
    print()
    print('  CLAIM (repaired, (BE-325)): on a side with delta_i >= 1 the OPEN')
    print("  count c_i' = |N_{H_i}(t2) ∩ A_i| is <= 1.")
    print(f'      counterexamples: {bad_open}')
    print('  CLAIM (repaired, (BE-325)): with BOTH sides flexible the second')
    print("  terminal's certificate is exactly {t2, b_1, b_2}, c_1' = c_2' = 1.")
    print(f'      holds: {ok_cert}   fails: {bad_cert}')
    print()
    print('  (delta_i, Step-1 containment for SOME optimal partition, the')
    print('   only excess is t2, c_i, c_i\', t2 has a neighbour IN B_i):')
    for k in sorted(tally, key=str):
        print(f'      {k} : {tally[k]}')
    print()
    print('  READ: every row with `nbr_in_B = False` and `c_i = 2` is a row')
    print('  where (BE-77)(ii) Step 3 has no edge to merge along.  Those are')
    print('  exactly the rows where its conclusion delta_i <= 1 fails.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return tally


MODES['blame'] = run_blame


# ============== the per-side NECESSARY condition for (BE-310)(i)'s confinement

def coverable(E):
    """A NECESSARY condition, on the SIDE alone, for (BE-310)(i)'s
    confinement hypothesis to be satisfiable at any glue.

    `A` is a union of CLOSED STARS of ADMITTED vertices, and only HUBS
    (degree >= 3 in the glued graph) are ever admitted.  An interior vertex
    of a side has the same degree in the side and in the glue; the two
    terminals gain degree from the other side, so they are hubs whenever the
    partner supplies an edge -- which every legal side does.  So
        A ∩ V(H_i)  ⊆  U_{w ∈ K_i} N_{H_i}[w],   K_i := {u, v} ∪ {w interior :
                                                          deg_{H_i}(w) >= 3},
    and a u--v path inside A forces a u--v path inside that union.  This
    function tests exactly that, and it is a function of the SIDE -- which is
    what makes the sweep possible without gluing, by the same per-side
    argument as (BE-79)(i).  It over-accepts (the union is the largest `A`
    any glue could produce), so `False` is SOUND and `True` is a CANDIDATE.
    """
    nb = neighbors(E)
    K = {U, V} | {w for w in nb if w not in (U, V) and len(nb[w]) >= 3}
    cov = set()
    for w in K:
        cov |= {w} | set(nb[w])
    return _path_in(E, cov, U, V) is not None


def _rand_side(rng, n, p, tag='B'):
    """A seeded random side on n vertices: u !~ v, connected, both terminals
    of degree >= 1, H + uv 2-connected -- `boneone.free_sides`' own four
    conditions, sampled instead of enumerated."""
    ext = [(tag, i) for i in range(n - 2)]
    W = [U, V] + ext
    pairs = [e for e in itertools.combinations(W, 2) if set(e) != {U, V}]
    E = [e for e in pairs if rng.random() < p]
    if len(verts_of(E)) != n:
        return None
    nb = neighbors(E)
    if not nb.get(U) or not nb.get(V):
        return None
    seen, st = {W[0]}, [W[0]]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    if len(seen) != n:
        return None
    idx = {w: i for i, w in enumerate(sorted(map(str, W)))}
    EE = [(idx[str(a)], idx[str(b)]) for (a, b) in E] + \
         [(idx[str(U)], idx[str(V)])]
    if not vertex_connectivity_at_least(n, EE, 2):
        return None
    return E


def run_cover(seed=SEED, nsamp=6000, nlo=7, nhi=10, rcap=RCAP, fcap=6):
    """THE DECISIVE PER-SIDE SWEEP.  `coverable` is necessary for the
    confinement, so a side with `delta >= 4` and `coverable` is the ONLY
    place (BE-311)(ii)'s kill condition can live.  Three tiers:
      * every free side at n <= fcap, EXHAUSTIVE (the 2^(C(n,2)-1) mask
        enumeration of `boneone.free_sides`, un-fenced in delta);
      * every K4 R-node side at n <= rcap, EXHAUSTIVE in branch profiles;
      * `nsamp` SEEDED random sides at n in [nlo, nhi], with the edge
        probability swept -- not exhaustive, and its zero reads
        "not found under cap".
    """
    t0 = time.time()
    rng = random.Random(seed)
    print('===== mode `cover`: is ANY side both flexible (delta >= 4) and '
          'star-coverable? =====')
    print('  `coverable` is NECESSARY for (BE-310)(i)\'s confinement and is a '
          'function of the side alone.')
    for (name, gen) in (
            ('free, exhaustive n <= %d' % fcap,
             ((E, d) for n in range(4, fcap + 1) for (E, d)
              in free_sides_at(n))),
            ('K4 R-node, exhaustive n <= %d' % rcap,
             ((H, d) for n in range(4, rcap + 1) for (_L, H, d)
              in rsides_at(n)))):
        tab = {}
        hits = []
        for (E, d) in gen:
            c = coverable(E)
            tab[(d, c)] = tab.get((d, c), 0) + 1
            if d >= 4 and c:
                hits.append((d, E))
        print(f'  tier "{name}": (delta, coverable) -> '
              f'{dict(sorted(tab.items(), key=str))}')
        print(f'      sides with delta >= 4 AND coverable: {len(hits)}')
        if hits:
            d, E = hits[0]
            print(f'      FIRST HIT delta = {d}: '
                  f'{sorted(tuple(sorted(map(str, e))) for e in E)}')
    tab = {}
    hits = []
    got = 0
    for _ in range(nsamp):
        n = rng.randint(nlo, nhi)
        p = rng.choice((0.25, 0.32, 0.4, 0.5))
        E = _rand_side(rng, n, p)
        if E is None:
            continue
        got += 1
        d = side_delta(E)[2]
        c = coverable(E)
        tab[(d, c)] = tab.get((d, c), 0) + 1
        if d >= 4 and c:
            hits.append((n, d, E))
    print(f'  tier "seeded random, n in [{nlo}, {nhi}]": {got} sides drawn '
          f'from {nsamp} attempts, seed {seed}')
    print(f'      (delta, coverable) -> {dict(sorted(tab.items(), key=str))}')
    print(f'      sides with delta >= 4 AND coverable: {len(hits)}')
    for (n, d, E) in hits[:3]:
        print(f'      HIT n = {n}, delta = {d}, dist = {_dist(E)}: '
              f'{sorted(tuple(sorted(map(str, e))) for e in E)}')
    print(f'  [{time.time() - t0:.1f} s]')
    return tab, hits


MODES['cover'] = run_cover


def side_reach(E):
    """The TIGHT per-side necessary condition for (BE-310)(i)'s confinement.

    At a forced peel BOTH terminals are admitted, so `u, v ∈ A`.  An interior
    vertex `w` of side `i` has `N_H[w] = N_{H_i}[w]`, so it is admitted iff
    `|N_{H_i}[w] ∩ A_i| >= 3`; and `A_i := A ∩ V(H_i)` grows only by the
    closed stars of admitted side-`i` vertices, together with `u` and `v`
    themselves (which the other side may import, and which are admitted here
    anyway).  Hence

        A_i  ⊆  R(H_i) := the closure of  N_{H_i}[u] ∪ N_{H_i}[v]  under
                "admit an interior w on 3 of its closed star", inside H_i,

    for EVERY glue and every seed -- `R(H_i)` is the largest `A_i` any
    partner could produce.  So a `u--v` path inside `A` forces one inside
    `R(H_i)`, and `side_reach` is NECESSARY for the confinement, sound in
    the `False` direction, and a function of the SIDE ALONE.

    It is strictly sharper than `coverable`, which allows every degree->=3
    interior vertex to be admitted; `side_reach` makes them earn it."""
    nb = neighbors(E)
    A = {U, V} | set(nb.get(U, ())) | set(nb.get(V, ()))
    interior = [w for w in nb if w not in (U, V)]
    changed = True
    while changed:
        changed = False
        for w in interior:
            star = {w} | set(nb[w])
            if len(star & A) >= 3 and not star <= A:
                A |= star
                changed = True
    return _path_in(E, A, U, V) is not None


def run_reach(seed=SEED, nsamp=6000, nlo=7, nhi=11, rcap=RCAP, fcap=6):
    """THE GLUE-INDEPENDENT SWEEP.  `side_reach` is necessary for the
    confinement at ANY glue, so a side with `delta >= 4` and `side_reach` is
    the only place (BE-311)(ii)'s kill condition can live -- and a zero here
    is a much stronger none-found than a zero over a list of glues.

    CAPS: free sides exhaustive at n <= fcap; K4 R-node sides exhaustive in
    branch profiles at n <= rcap; plus `nsamp` SEEDED random sides at
    n in [nlo, nhi] with the edge probability swept.  Not exhaustive above
    fcap; its zero reads "not found under cap"."""
    t0 = time.time()
    rng = random.Random(seed)
    print('===== mode `reach`: is ANY side both flexible (delta >= 4) and '
          'REACHABLE? =====')
    print('  `side_reach` bounds A_i from ABOVE at every glue, so a False '
          'here closes the side for good.')
    for (name, gen) in (
            (f'free, exhaustive n <= {fcap}',
             ((E, d) for n in range(4, fcap + 1)
              for (E, d) in free_sides_at(n))),
            (f'K4 R-node, exhaustive n <= {rcap}',
             ((H, d) for n in range(4, rcap + 1)
              for (_L, H, d) in rsides_at(n)))):
        tab, hits = {}, []
        for (E, d) in gen:
            r = side_reach(E)
            tab[(d, r)] = tab.get((d, r), 0) + 1
            if d >= 4 and r:
                hits.append((d, E))
        print(f'  tier "{name}": (delta, reachable) -> '
              f'{dict(sorted(tab.items(), key=str))}')
        print(f'      delta >= 4 AND reachable: {len(hits)}')
        if hits:
            print(f'      FIRST: delta = {hits[0][0]}, '
                  f'{sorted(tuple(sorted(map(str, e))) for e in hits[0][1])}')
    tab, hits, got = {}, [], 0
    for _ in range(nsamp):
        n = rng.randint(nlo, nhi)
        p = rng.choice((0.25, 0.32, 0.4, 0.5))
        E = _rand_side(rng, n, p)
        if E is None:
            continue
        got += 1
        d = side_delta(E)[2]
        r = side_reach(E)
        tab[(d, r)] = tab.get((d, r), 0) + 1
        if d >= 4 and r:
            hits.append((n, d, E))
    print(f'  tier "seeded random, n in [{nlo}, {nhi}]": {got} sides from '
          f'{nsamp} attempts, seed {seed}')
    print(f'      (delta, reachable) -> {dict(sorted(tab.items(), key=str))}')
    print(f'      delta >= 4 AND reachable: {len(hits)}')
    for (n, d, E) in hits[:3]:
        print(f'      HIT n = {n}, delta = {d}, dist = {_dist(E)}: '
              f'{sorted(tuple(sorted(map(str, e))) for e in E)}')
    print(f'  [{time.time() - t0:.1f} s]')
    return tab, hits


MODES['reach'] = run_reach


if __name__ == '__main__':
    args = sys.argv[1:] or ['fence']
    for a in args:
        if a not in MODES:
            raise SystemExit(f'unknown mode {a!r}; modes: {sorted(MODES)}')
        MODES[a]()
        print()
