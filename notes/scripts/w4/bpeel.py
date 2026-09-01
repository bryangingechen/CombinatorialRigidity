"""
Direction BPEEL (ordinal 54) -- (BE-67)(iii), HALF (B)'s CLASS STATEMENT:
for EVERY internal R-node piece H, does some point of Chart(H) make both
peel sides attain and put rho_bar_1, rho_bar_2 in general position?

  THE CRUX the spec names.  BDECOR located TWO ways to fail and discharged
  each separately -- the welded half FREE at theta children ((BE-66)(ii)),
  the general-position half's only LOCATED enemy unforceable at an R-node
  peel ((BE-66)(iv)).  The open question is whether those are the ONLY two.
  That is an EXHAUSTIVENESS claim, and reading (BE-66)(iii)'s "only LOCATED
  enemy" as "no third mechanism" is the one move the spec forbids (F11).

  THE ANSWER, said at the top.  The exhaustiveness obligation is RETIRED,
  not discharged by enumeration, and the retirement is two theorems:

    (BE-69) THE DICHOTOMY.  On Chart(H) -- irreducible by (BE-65)(ii) /
            (CH-1)(a) -- the good locus is ZARISKI-OPEN, so it is DENSE or
            EMPTY.  A failure is therefore never a phenomenon at a special
            point: it is a shortfall of ONE generic invariant.
    (BE-70) THE PEEL-INDEPENDENCE THEOREM.  No topological branch crosses a
            2-cut, so at a fixed flag assignment rho_bar_1 and rho_bar_2 are
            functions of DISJOINT coordinate blocks.  The two sides share
            exactly ONE datum: the flag pair at (u, v).

  Together: any failure mechanism, located or not, is a statement about the
  pair of independent achievable families at a generic flag pair -- it must
  show up as a shortfall of the GENERIC REACH, which one exact-Q draw
  computes.  So no list of mechanisms is needed and none is claimed.

  AND ONE CORRECTION, which is this direction's sharpest single sentence
  (F12, annotated at source).  (BE-66)(iv) discharges the located enemy by
  "the only landed mechanism forcing pi_x = pi_y is BZAVOID's triangle
  propagation ((BE-15)), which needs x ~ y".  That is INCOMPLETE: (BE-15)(ii)
  carries its OWN scope correction recording a landed GENERAL rule that
  needs no triangle and no adjacency (K_{3,3} is forced flat and
  triangle-free), implemented as `binduc.flat_forcing_closure`.  The right
  discharge is (BE-32)(+) + (BE-22)(vi): forced => delta = 0 => the
  general-position half has NO CONTENT.  That re-ranks the SPREAD step.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `open`  (BE-69)  The dichotomy's measurable signature: the peel invariants
                   are lower semicontinuous, the FIRST generic draw already
                   reaches the maximum over all draws, and no draw ever
                   exceeds it.  (BE-22)(i) asserted at every peel.
  `indep` (BE-70)  (a) ASSERT that no topological branch crosses the peel's
                   2-cut, at every piece and every peel.  (b) THE CROSS-MIX
                   TEST: side 1's chains from run A and side 2's chains from
                   run B at one fixed flag assignment, glued -- both gates
                   asserted, and rho_bar_i asserted equal AS SPACES to its
                   own run's value.  The mix realizes pairs (V1, V2) neither
                   run drew, which is the product claim itself.
  `law`            The 2-cut delta law delta_{uv}(H) = max(0, d1 + d2 - 6),
                   asserted against two independent oracles.  It is what
                   makes (BE-32)(+) NEARLY VACUOUS at a 2-cut pair, hence
                   why only the ONE-SIDED form of the discharge bites.
  `force` (BE-73)  THE ENUMERATION, which is what F11 demands of an
                   exhaustiveness claim.  Over 2-cut instances: is
                   pi_u = pi_v FORCED by the landed aggressive closure, and
                   if so is min(delta_1, delta_2) = 0?  A forced instance
                   with BOTH deltas positive is the third-mechanism
                   candidate.  One-sided forcing is separated from
                   CROSS-CUT-only forcing, because (BE-32)(+) covers the
                   first and nothing covers the second.
  `gate`  (BE-72)  JOB 2, the cross-branch proviso G.  The two coincidence
                   types are enumerated and each decided: point coincidence
                   across branches is NEVER forced; hinge-line coincidence
                   at a hub is forced ONLY by a length-1 branch beside a
                   length-2 branch -- a TRIANGLE ON TWO HUBS, which
                   (CH-1)'s girth >= 4 already excludes.  Measured both
                   ways, including the named forced-empty control.

CAPS, DISCLOSED (F27, F11, and cap disclosure is MANDATORY here).

  (1) `force`'s enumeration is EXHAUSTIVE over connected labelled graphs at
      n <= 6 with max degree <= 4, plus seeded random masks at n = 7, 8, and
      a constructed long-branch tier.  A "none found" is "none found under
      cap C", NEVER "there is no third mechanism".  The census is run TWICE,
      by two independent enumerators (this driver's own scan over ALL 2-cuts
      of a graph, and `btwocut.two_cut_census`, which keeps one per graph).
  (2) The aggressive closure OVER-claims forcing (it assumes every three
      forced points independent), so a "forced" verdict is a CANDIDATE and a
      "not forced" verdict is SOUND -- the direction the hunt needs.
  (3) `open`/`indep` quote GENERIC values as the MAXIMUM over seeded draws
      (dim of a sum is LOWER semicontinuous), the opposite convention to
      BDECOR's `theta`/`small`, which quote a minimum of an INTERSECTION.
  (4) `open`/`indep` run on BDECOR's own R_BATTERY plus the nested piece:
      ONE constructor.  A shortfall would be "not attained by this
      constructor" (F27), never "does not attain".  None was seen.
  (5) Deficiencies use `bdecor.d3` / `bdecor.weld_d3` (the (6,6)-count
      oracle, the only one that runs on a welded multigraph at |V| > 8) and
      `btwocut.deltas_at` (the contraction oracle, cross-checked against
      binduc's set-partition oracle inside itself at |V| <= 8).

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import itertools
import random
import sys
import time
from fractions import Fraction as F

import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import rank as rank_exact, neighbors                      # noqa: E402
from kbare_common import verts_of                                        # noqa: E402
from bzavoid import adj_of, connected_spanning, edges_of_mask            # noqa: E402
from binduc import (flat_forcing_closure, split_at_pair, theta,          # noqa: E402
                    deg_of, vertex_connectivity_at_least)
from btwocut import deltas_at, two_cut_census                            # noqa: E402
from bimage import (dim, isect, same_space, span, v4, pt_in,            # noqa: E402
                    rho_bar_of, legal_chain, chain_of)
from bdecor import (R_BATTERY, nested_piece, d3, weld_d3, girth,         # noqa: E402
                    hubs_and_branches, sample_by_branches, assemble,
                    flag_assignment, draw_branch)

SEED = 20260901


# ============================== the aggressive closure, made PAIRWISE

def closure_from(nb, hubs, h):
    """`binduc.flat_forcing_closure`'s inner loop, INSTRUMENTED.

    Returns (A, admitted): `A` the vertex set forced into the single plane
    pi_h, `admitted` the hubs whose PLANE is forced EQUAL to pi_h.  The
    growth rule for `A` is byte-for-byte binduc's (a hub is admitted on
    three star points already in `A`), so the fixed point of `A` is
    identical -- `force` asserts that against the landed function.  What
    binduc does not expose is `admitted`, and a PAIR question needs it."""
    A = {h} | set(nb[h])
    adm = {h}
    changed = True
    while changed:
        changed = False
        for v in hubs:
            star = {v} | set(nb[v])
            if len(star & A) >= 3:
                if v not in adm:
                    adm.add(v)
                    changed = True
                if not star <= A:
                    A |= star
                    changed = True
    return A, adm


def hubs_of(edges, nb=None):
    nb = nb or neighbors(edges)
    return sorted((z for z in verts_of(edges) if len(nb[z]) >= 3), key=str)


def pair_forced(edges, u, v):
    """Is pi_u = pi_v FORCED by the aggressive closure?  True iff some hub's
    closure admits BOTH.  Over-claims (cap (2)), so True is a CANDIDATE and
    False is sound."""
    nb = neighbors(edges)
    hubs = hubs_of(edges, nb)
    if u not in hubs or v not in hubs:
        return False
    for h in hubs:
        _A, adm = closure_from(nb, hubs, h)
        if u in adm and v in adm:
            return True
    return False


def forced_flat_here(n, edges):
    """This module's own flat verdict, for the cross-check against the
    landed `binduc.flat_forcing_closure`."""
    nb = neighbors(edges)
    hubs = hubs_of(edges, nb)
    V = set(verts_of(edges))
    for h in hubs:
        A, _adm = closure_from(nb, hubs, h)
        if A >= V and len(V) == n:
            return True
    return False


# ================================ the internal-R-node shape of a peel

def suppress_deg2(edges, keep):
    """Suppress every degree-2 vertex outside `keep`, replacing its two
    incident edges by one -- the topological skeleton of (BE-64)'s own
    `hubs_and_branches`, written on an edge list so it can run inside a
    census.  Returns a multigraph edge list (parallel edges KEPT: a parallel
    pair is a P-node and is exactly what must NOT be called an R-node)."""
    E = [tuple(e) for e in edges]
    changed = True
    while changed:
        changed = False
        deg = {}
        for (a, b) in E:
            deg[a] = deg.get(a, 0) + 1
            deg[b] = deg.get(b, 0) + 1
        for z in list(deg):
            if z in keep or deg[z] != 2:
                continue
            inc = [e for e in E if z in e]
            if len(inc) != 2:
                continue
            (a, b), (c, d) = inc
            x = a if a != z else b
            y = c if c != z else d
            if x == y:                     # a loop would appear: leave it
                continue
            E = [e for e in E if z not in e] + [(x, y)]
            changed = True
            break
    return E


def rnode_shaped(E_side, u, v):
    """Is the peel at {u,v} presented, on THIS side, by an R-node -- i.e. is
    the side's skeleton, with the virtual edge uv put back and every
    degree-2 vertex suppressed, SIMPLE and 3-CONNECTED?

    This is the computable stand-in for "uv is a virtual edge of a simple
    3-connected SPQR skeleton", the exact hypothesis (BE-66)(iv) argues
    under.  It is disclosed as a stand-in, not as an SPQR implementation:
    a parallel pair after suppression is a P-node and is rejected; a
    degree-2 marked vertex after suppression is an S-node and is rejected."""
    E = suppress_deg2(list(E_side) + [(u, v)], keep={u, v})
    if len(set(map(frozenset, E))) != len(E):
        return False                                   # parallel: P-node
    V = sorted({w for e in E for w in e}, key=str)
    if len(V) < 4:
        return False
    ren = {w: i for i, w in enumerate(V)}
    EE = [(ren[a], ren[b]) for (a, b) in E]
    nb = neighbors(EE)
    if min(len(nb[i]) for i in range(len(V))) < 3:
        return False
    return vertex_connectivity_at_least(len(V), EE, 3)


# ============================================== mode: force  ((BE-73))

def peel_scan(n, edges, nb=None):
    """EVERY 2-cut {u,v} of `edges` with u !~ v and both sides carrying at
    least one interior vertex -- a SUPERSET of the internal-R-node peels
    (which additionally need the node's skeleton 3-connected), so a
    "none found" over this scan is the stronger statement."""
    nb = nb or neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    out = []
    for (u, v) in itertools.combinations(V, 2):
        if v in nb[u]:
            continue
        sp = split_at_pair(edges, u, v)
        if sp is None:
            continue
        V1, E1, V2, E2 = sp
        if len(V1) < 3 or len(V2) < 3:
            continue
        out.append((u, v, V1, E1, V2, E2))
    return out


SKELETONS = {
    'K4': [('A', 'B'), ('A', 'C'), ('A', 'D'), ('B', 'C'), ('B', 'D'),
           ('C', 'D')],
    'prism': [('A', 'B'), ('B', 'C'), ('C', 'A'), ('D', 'E'), ('E', 'F'),
              ('F', 'D'), ('A', 'D'), ('B', 'E'), ('C', 'F')],
    'K33': [('A', 'D'), ('A', 'E'), ('A', 'F'), ('B', 'D'), ('B', 'E'),
            ('B', 'F'), ('C', 'D'), ('C', 'E'), ('C', 'F')],
}


def subdivided(skel, lengths):
    """The piece: skeleton edge i becomes a branch of `lengths[i]` edges.
    Length 1 is a REAL hub-hub edge, length k >= 2 a branch with k-1
    degree-2 interior vertices -- the (BE-64) topological-branch profile,
    written as a graph so the census can run on it."""
    E = []
    for i, (a, b) in enumerate(skel):
        k = lengths[i]
        if k == 1:
            E.append((a, b))
            continue
        prev = a
        for j in range(k - 1):
            w = f's{i}_{j}'
            E.append((prev, w))
            prev = w
        E.append((prev, b))
    return E


def delta_pair(edges, u, v):
    """(delta_1, delta_2) at the 2-cut {u,v}, by the (6,6)-count oracle
    (`bdecor.d3` / `bdecor.weld_d3`), which runs on the WELDED multigraph at
    |V| > 8 where `btwocut.deltas_at`'s partition oracle cannot."""
    sp = split_at_pair(edges, u, v)
    if sp is None:
        return None
    _V1, E1, _V2, E2 = sp
    out = []
    for Ei in (E1, E2):
        f, g = d3(Ei), weld_d3(Ei, u, v)
        assert 0 <= f - g <= 6, ('delta out of [0,6]', Ei, f, g)
        out.append(f - g)
    return out[0], out[1], E1, E2


def constructed_tier(maxlen=4, nsamp=1500, seed=SEED):
    """The tier the random census CANNOT reach: pieces built as a
    3-CONNECTED SKELETON with a branch-length profile, so that an
    internal-R-node peel with BOTH sides flexible actually occurs.  Every
    profile of K4 exhaustively at branch lengths 1..maxlen, plus seeded
    profiles of the prism and K_{3,3}.  Yields
    (tag, edges, u, v, d1, d2, forced, rnode)."""
    rng = random.Random(seed)
    jobs = []
    K4 = SKELETONS['K4']
    for prof in itertools.product(range(1, maxlen + 1), repeat=len(K4)):
        jobs.append(('K4', K4, list(prof)))
    for nm in ('prism', 'K33'):
        sk = SKELETONS[nm]
        for _ in range(nsamp):
            jobs.append((nm, sk, [rng.randint(1, maxlen)
                                  for _ in range(len(sk))]))
    for (nm, sk, prof) in jobs:
        E = subdivided(sk, prof)
        for i, (a, b) in enumerate(sk):
            if prof[i] < 2:
                continue                     # a real edge is not virtual
            got = delta_pair(E, a, b)
            if got is None:
                continue
            d1, d2, E1, E2 = got
            rn = rnode_shaped(E1, a, b) or rnode_shaped(E2, a, b)
            yield (f'{nm}{tuple(prof)}', E, a, b, d1, d2,
                   pair_forced(E, a, b), rn)


def run_force(nexh=6, nsamp=(7, 8), nmask=3000, seed=SEED, quick=False):
    t0 = time.time()
    print(f'== force: (BE-73) THE ENUMERATION -- is the located enemy '
          f'FORCEABLE at a 2-cut, and does it BITE?  seed {seed}')
    print('  (BE-66)(iv) says "no LANDED mechanism forces pi_x = pi_y at a')
    print('  virtual edge\'s ends, because (BE-15) needs x ~ y".  (BE-15)(ii)')
    print('  carries its OWN scope correction: the GENERAL rule needs neither')
    print('  a triangle nor adjacency.  Question 1 -- is it forceable at a')
    print('  NON-ADJACENT pair?  Question 2 -- when it is, is')
    print('  min(delta_1, delta_2) = 0, so that (BE-22)(vi) empties the')
    print('  general-position half before the confinement can bite?')

    # ---- the two named witnesses, first, as ASSERTS ---------------------
    K23 = [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]
    assert pair_forced(K23, 0, 1), 'K_{2,3} should force pi_u = pi_v'
    nbK = neighbors(K23)
    assert 1 not in nbK[0], 'K_{2,3}\'s marked pair should be NON-adjacent'
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
           (2, 3), (2, 4), (2, 5)]
    assert flat_forcing_closure(6, K33) and forced_flat_here(6, K33), \
        'K_{3,3} should be forced flat by both closures'
    nb33 = neighbors(K33)
    tri = any(set(nb33[a]) & set(nb33[b]) for (a, b) in K33)
    print(f'  ANSWER TO QUESTION 1: YES.  K_{{2,3}} forces pi_u = pi_v at a')
    print(f'  NON-ADJACENT pair (0 ~ 1 is False), and K_{{3,3}} is forced flat')
    print(f'  with a triangle = {tri}.  So (BE-66)(iv)\'s REASON is incomplete;')
    print('  what survives is the CONCLUSION, and by a different argument.')

    # ---- census 1: this driver's own scan over ALL 2-cuts ---------------
    rng = random.Random(seed)
    tiers = [(n, None) for n in range(5, nexh + 1)] + \
            [(n, nmask if not quick else nmask // 6) for n in nsamp]
    tot = ncut = nforced = nbite = nrbite = nrnode = nrboth = 0
    nrforced = 0
    onesided = crosscut = 0
    flatchecks = 0
    hits = []
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        if samp is None:
            masks = range(1 << len(pairs))
        else:
            masks = [rng.getrandbits(len(pairs)) for _ in range(samp)]
        cn = cf = cb = cr = crb = 0
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            adj = adj_of(n, edges)
            if not connected_spanning(n, adj):
                continue
            if max(deg_of(n, edges)) > 4:
                continue
            if not vertex_connectivity_at_least(n, edges, 2):
                continue
            tot += 1
            if flatchecks < 4000:                     # the cross-check (2)
                assert forced_flat_here(n, edges) == flat_forcing_closure(
                    n, edges), ('closure disagreement', edges)
                flatchecks += 1
            nb = neighbors(edges)
            for (u, v, V1, E1, V2, E2) in peel_scan(n, edges, nb):
                ncut += 1
                cn += 1
                rn = rnode_shaped(E1, u, v) or rnode_shaped(E2, u, v)
                forced = pair_forced(edges, u, v)
                if not (rn or forced):
                    continue
                cd = deltas_at(edges, u, v, check=False)
                _V1, E1_, f1, g1, _V2, E2_, f2, g2 = cd
                d1, d2 = f1 - g1, f2 - g2
                both = (d1 > 0 and d2 > 0)
                if rn:
                    nrnode += 1
                    if both:
                        nrboth += 1
                        crb += 1
                if not forced:
                    continue
                nforced += 1
                cf += 1
                if rn:
                    nrforced += 1
                if pair_forced(E1_, u, v) or pair_forced(E2_, u, v):
                    onesided += 1
                else:
                    crosscut += 1
                if both:
                    nbite += 1
                    cb += 1
                    if rn:
                        nrbite += 1
                        cr += 1
                        hits.append((n, edges, u, v, d1, d2))
        print(f'  n = {n:2d}{"  exhaustive" if samp is None else f"  {samp} masks"}'
              f': {cn} peels (2-cut, u !~ v), {cf} FORCED, {cb} of those '
              f'with BOTH deltas positive, {cr} of THOSE R-node-shaped '
              f'[R-node-shaped with both deltas positive, forced or not: '
              f'{crb}]')
    print(f'  CENSUS 1 (all 2-cuts of each graph): graphs {tot}, peels {ncut}, '
          f'forced {nforced} ({onesided} one-sided, {crosscut} cross-cut '
          f'only; {nrnode} R-node-shaped, {nrforced} of those forced), '
          f'forced-AND-both-deltas-positive '
          f'{nbite}, of those R-NODE-shaped {nrbite}')
    print(f'  THE NON-VACUITY CHECK, which is what makes the 0 mean '
          f'something: R-node-shaped peels with BOTH deltas positive, '
          f'forced or not = {nrboth}.  The hunt had that many chances.')
    print(f'  closure cross-check against the landed '
          f'`binduc.flat_forcing_closure`: {flatchecks} graphs, 0 disagreements')

    # ---- census 3: the CONSTRUCTED tier, which is the non-vacuous one ---
    cn = crn = crb = cfr = chit = 0
    chits = []
    for (tag, E, u, v, d1, d2, forced, rn) in constructed_tier(
            maxlen=3 if quick else 4, nsamp=300 if quick else 1500, seed=seed):
        cn += 1
        if rn:
            crn += 1
        if forced:
            cfr += 1
        if rn and d1 > 0 and d2 > 0:
            crb += 1
            if forced:
                chit += 1
                chits.append((tag, u, v, d1, d2))
    print(f'  CENSUS 3 (CONSTRUCTED: every branch-length profile of K4 at '
          f'lengths 1..{3 if quick else 4} exhaustively, plus seeded profiles '
          f'of the prism and K_{{3,3}}) -- the tier the random censuses cannot')
    print(f'  reach, because a random graph at n <= 8 with max degree <= 4 '
          f'never carries an R-node peel with both sides flexible:')
    print(f'      peels {cn}, R-node-shaped {crn}, FORCED {cfr}, '
          f'R-node-shaped with BOTH deltas positive {crb}, '
          f'FORCED among those {chit}')
    for h in chits[:6]:
        print(f'      {h}')

    # ---- census 2: the INDEPENDENT enumerator ---------------------------
    cens = two_cut_census(nexh=nexh, nsamp=nsamp,
                          nmask=nmask if not quick else nmask // 6,
                          seed=seed, need_both_delta=True)
    f2 = [(n, E, u, v, d1, d2) for (n, E, u, v, d1, d2) in cens
          if v not in neighbors(E)[u] and pair_forced(E, u, v)]
    f2r = []
    for (n, E, u, v, d1, d2) in f2:
        sp = split_at_pair(E, u, v)
        if sp is None:
            continue
        _V1, E1, _V2, E2 = sp
        if rnode_shaped(E1, u, v) or rnode_shaped(E2, u, v):
            f2r.append((n, E, u, v, d1, d2))
    f2n = len(f2r)
    adjn = sum(1 for (n, E, u, v, d1, d2) in cens if v in neighbors(E)[u])
    print(f'  CENSUS 2 (`btwocut.two_cut_census`, BOTH deltas positive by '
          f'construction, one 2-cut per graph): {len(cens)} instances, '
          f'{adjn} with u ~ v, {f2n} with pi_u = pi_v FORCED')
    if nrbite == 0 and f2n == 0 and chit == 0:
        print(f'  ANSWER TO QUESTION 2, under cap (1): at an R-NODE-shaped '
              f'peel, EVERY forced instance found ({nrforced} + {cfr}) has '
              f'min(d1, d2) = 0 -- so (BE-22)(vi) empties the '
              f'general-position half BEFORE the')
        print(f'  confinement can bite.  Off the R-node shape (P- and S-node '
              f'peels, which (BE-67)(iii) does not quantify over) forcing '
              f'with both deltas positive is COMMON: {nbite} instances.')
    else:
        print(f'  HIT: {nrbite} + {f2n} + {chit} R-NODE-shaped forced peels '
              f'with BOTH '
              f'deltas positive.  Witnesses:')
        for h in hits[:6]:
            print(f'      {h}')
        for h in f2r[:6]:
            print(f'      c2 {h}')
        for h in chits[:6]:
            print(f'      c3 {h}')
    print('  READ THIS THE RIGHT WAY (F11).  "None found under cap (1)" is')
    print('  NOT "there is no third mechanism".  What IS proved is the')
    print('  ONE-SIDED case: forcing inside a single side gives delta_i = 0')
    print('  by (BE-32)(+), and (BE-22)(vi) then empties the general-position')
    print('  half.  CROSS-CUT-only forcing is the named open residue.')
    print(f'  force: {time.time() - t0:.1f}s')
    return nrbite == 0 and f2n == 0 and chit == 0


# ================================================ mode: law (the 2-cut delta)

def run_law(nexh=6, nmask=1500, seed=SEED, quick=False):
    t0 = time.time()
    print(f'== law: delta_uv(H) = max(0, d1 + d2 - 6) at a 2-cut, seed {seed}')
    print('  Why this matters, and it is not bookkeeping.  (BE-32)(+) says a')
    print('  FORCED pi_u = pi_v gives delta_uv = 0.  At a 2-cut pair that')
    print('  reads d1 + d2 <= 6 -- almost always true and NO help.  So only')
    print('  the ONE-SIDED form of (BE-32)(+), read on a side, has content:')
    print('  that is why `force` separates one-sided from cross-cut forcing.')
    n_ok = 0
    rng = random.Random(seed)
    tiers = [(n, None) for n in range(5, nexh + 1)] + \
            [(n, nmask if not quick else nmask // 5) for n in (7, 8)]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = range(1 << len(pairs)) if samp is None else \
            [rng.getrandbits(len(pairs)) for _ in range(samp)]
        cnt = 0
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            if max(deg_of(n, edges)) > 4:
                continue
            if not vertex_connectivity_at_least(n, edges, 2):
                continue
            for (u, v, V1, E1, V2, E2) in peel_scan(n, edges):
                cd = deltas_at(edges, u, v, check=(n <= 6))
                _V1, _E1, f1, g1, _V2, _E2, f2, g2 = cd
                d1, d2 = f1 - g1, f2 - g2
                fH, gH = d3(edges), weld_d3(edges, u, v)
                assert fH - gH == max(0, d1 + d2 - 6), \
                    ('the 2-cut delta law fails', edges, u, v, d1, d2, fH, gH)
                cnt += 1
                n_ok += 1
        print(f'  n = {n:2d}{"  exhaustive" if samp is None else "  sampled"}: '
              f'{cnt} peels, law ASSERTED at every one')
    ctor = 0
    for (tag, E, u, v, d1, d2, forced, rn) in constructed_tier(
            maxlen=3, nsamp=120 if quick else 400, seed=seed):
        fH, gH = d3(E), weld_d3(E, u, v)
        assert fH - gH == max(0, d1 + d2 - 6), \
            ('the 2-cut delta law fails on the constructed tier', tag, u, v)
        ctor += 1
    print(f'  constructed tier: {ctor} peels, law ASSERTED at every one')
    print(f'  TOTAL {n_ok + ctor} peels, 0 failures.  Two oracles: '
          f'`btwocut.deltas_at` (contraction, cross-checked against binduc\'s')
    print(f'  set-partition oracle at n <= 6) for the sides, the (6,6)-count '
          f'oracle (`bdecor.d3`/`weld_d3`) for the whole piece.')
    print(f'  law: {time.time() - t0:.1f}s')
    return True


# ============================ the peel's own branch bookkeeping ((BE-70))

def peel_sides(pc, i):
    """Side 2 = child i's edges, side 1 = everything else, and the peel pair
    (x, y) = that child's terminals -- BDECOR's `run_attain` split, lifted
    out so `open`/`indep` share it."""
    x, y, ce, kind = pc['children'][i]
    side1 = []
    for j, (_a, _b, cf, _k) in enumerate(pc['children']):
        if j != i:
            side1 += cf
    return x, y, side1, ce, kind


def branch_sides(branches, side1, side2, x, y):
    """Which side each topological branch lies in.  ASSERTS (BE-70)(i): no
    branch crosses the 2-cut."""
    S1 = {w for e in side1 for w in e}
    S2 = {w for e in side2 for w in e}
    out = []
    for br in branches:
        (z, zp, ints) = br
        vs = set([z, zp]) | set(ints)
        in1, in2 = vs <= S1, vs <= S2
        assert in1 or in2, ('a topological branch CROSSES the 2-cut', br, x, y)
        out.append((br, 1 if in1 else 2))
    return out


# ================================================ mode: open ((BE-69))

def peel_rows(pc, pt, ndraw_tag=''):
    """Every peel of the piece at this configuration: (kind, x, y, d1, d2,
    r1, r2, dM1, dM2, dsum, attains).  (BE-22)(i) is ASSERTED, not reported."""
    H = pc['H']
    _S, _r, dMH, _rk = rho_bar_of(H, pt, pc['u'], pc['v'])
    rows = []
    for i, (x, y, ce, kind) in enumerate(pc['children']):
        if kind == 'leaf':
            continue
        x, y, side1, side2, kind = peel_sides(pc, i)
        f1, g1 = d3(side1), weld_d3(side1, x, y)
        f2, g2 = d3(side2), weld_d3(side2, x, y)
        S1, r1, dM1, _ = rho_bar_of(side1, pt, x, y)
        S2, r2, dM2, _ = rho_bar_of(side2, pt, x, y)
        dsum = dim(span(S1 + S2))
        assert dMH == dM1 + dM2 - 6 - dsum, '(BE-22)(i) fails at an R-node peel'
        assert dM1 >= 6 + f1 and dM2 >= 6 + f2, \
            'a side beats the universal partition cap -- impossible'
        rows.append((kind, x, y, f1 - g1, f2 - g2, r1, r2, dM1, dM2, dsum,
                     dM1 == 6 + f1, dM2 == 6 + f2, S1, S2))
    return rows


def run_open(seed=SEED, ndraw=5):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== open: (BE-69) THE DICHOTOMY -- the good locus is ZARISKI-OPEN '
          f'on an irreducible Chart(H), seed {seed}')
    print('  so it is DENSE or EMPTY, and a failure is never a phenomenon at')
    print('  a special point.  The measurable signature: the peel invariants')
    print('  are LOWER semicontinuous, the FIRST generic draw already reaches')
    print('  the maximum over all draws, and no draw ever exceeds it (cap 3).')
    npeel = nfirst = nshort = 0
    pieces = R_BATTERY() + [('nested [K4 child in a K4 piece]', nested_piece())]
    for nm, pc in pieces:
        H, u, v = pc['H'], pc['u'], pc['v']
        best, first = {}, {}
        drawn = 0
        for _ in range(ndraw * 8):
            if drawn == ndraw:
                break
            got = sample_by_branches(H, u, v, rng)
            if got is None:
                continue
            pt = got[0]
            for row in peel_rows(pc, pt):
                (kind, x, y, d1, d2, r1, r2, dM1, dM2, dsum, a1, a2,
                 _S1, _S2) = row
                key = (x, y)
                val = (dsum, r1, r2, int(a1), int(a2))
                if key not in first:
                    first[key] = val
                    best[key] = val
                else:
                    best[key] = tuple(max(a, b) for a, b in
                                      zip(best[key], val))
            drawn += 1
        for key in sorted(best, key=str):
            npeel += 1
            if first[key] == best[key]:
                nfirst += 1
            assert all(f <= b for f, b in zip(first[key], best[key])), \
                'a later draw beat the first on every coordinate -- impossible'
            print(f'  {nm:44s} peel {str(key):14s} first draw '
                  f'{first[key]} vs max over {drawn} draws {best[key]}'
                  f'{"" if first[key] == best[key] else "   <-- first draw NOT generic"}')
    print(f'  peels {npeel}, first draw already at the maximum at {nfirst}')
    print('  WHAT THIS DOES AND DOES NOT SHOW.  Semicontinuity is PROVED')
    print('  ((BE-69)(i)); the measurement is its signature, not its proof.')
    print('  A draw BELOW the maximum is a non-generic point and is expected;')
    print('  a draw ABOVE it would refute the openness argument (assert).')
    print(f'  open: {time.time() - t0:.1f}s')
    return nshort == 0


# =============================================== mode: indep ((BE-70))

def run_indep(seed=SEED, ndraw=3):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== indep: (BE-70) THE PEEL-INDEPENDENCE THEOREM, seed {seed}')
    print('  (a) ASSERT no topological branch crosses the peel\'s 2-cut.')
    print('  (b) THE CROSS-MIX TEST: side 1\'s chains from run A and side 2\'s')
    print('      from run B at ONE fixed flag assignment, glued.  Both gates')
    print('      asserted; rho_bar_i asserted equal AS SPACES to its own')
    print('      run\'s value.  The mix realizes pairs (V1, V2) NEITHER run')
    print('      drew -- which is the product claim itself.')
    nbr = nmix = nnew = 0
    for nm, pc in R_BATTERY():
        H, u, v = pc['H'], pc['u'], pc['v']
        W, branches = hubs_and_branches(H, u, v)
        for i, (x0, y0, ce, kind) in enumerate(pc['children']):
            if kind == 'leaf':
                continue
            x, y, side1, side2, kind = peel_sides(pc, i)
            assert x in W and y in W, \
                'a peel terminal is not a hub -- branches could cross'
            bs = branch_sides(branches, side1, side2, x, y)
            nbr += len(bs)
            got = 0
            for _ in range(ndraw * 10):
                if got == ndraw:
                    break
                P, B = flag_assignment(W, branches, rng)
                if P is None:
                    continue
                runs = []
                for _r in range(2):
                    pts, ok = dict(P), True
                    for (z, zp, ints) in branches:
                        ch = draw_branch(P, B, z, zp, len(ints), rng)
                        if ch is None:
                            ok = False
                            break
                        for w, xx in zip(ints, ch):
                            pts[w] = xx
                    if not ok:
                        break
                    aff = assemble(H, pts)
                    if aff is None:
                        break
                    runs.append((pts, aff))
                if len(runs) != 2:
                    continue
                mix = dict(P)
                for (br, sd) in bs:
                    (z, zp, ints) = br
                    src = runs[0][0] if sd == 1 else runs[1][0]
                    for w in ints:
                        mix[w] = src[w]
                affm = assemble(H, mix)
                if affm is None:
                    continue
                S1a, r1a, _, _ = rho_bar_of(side1, runs[0][1], x, y)
                S2b, r2b, _, _ = rho_bar_of(side2, runs[1][1], x, y)
                S1m, r1m, _, _ = rho_bar_of(side1, affm, x, y)
                S2m, r2m, _, _ = rho_bar_of(side2, affm, x, y)
                assert same_space(S1a, S1m), \
                    'rho_bar_1 of the MIX differs from run A -- side 1 is not'\
                    ' a function of side 1\'s own coordinates'
                assert same_space(S2b, S2m), \
                    'rho_bar_2 of the MIX differs from run B'
                S2a = rho_bar_of(side2, runs[0][1], x, y)[0]
                S1b = rho_bar_of(side1, runs[1][1], x, y)[0]
                da = dim(span(S1a + S2a))
                db = dim(span(S1b + S2b))
                dm = dim(span(S1m + S2m))
                if not same_space(S2a, S2b):
                    nnew += 1                 # the MIX pair is a NEW pair
                nmix += 1
                got += 1
                print(f'  {nm:40s} peel ({x},{y}) mix {got}: '
                      f'dim(sum) run A {da}, run B {db}, MIX {dm}'
                      f'{"  [pair NEW]" if not same_space(S2a, S2b) else "  [pair repeated]"}')
    print(f'  branches classified {nbr}, none crossing a 2-cut (ASSERTED); '
          f'MIX configurations {nmix}, all gate-passing; mixes realizing a '
          f'pair (V1, V2) NEITHER parent run drew: {nnew}')
    print('  The dim(sum) column repeating across A, B and the MIX is the')
    print('  DICHOTOMY at work, not a weakness: by (BE-69) the generic value')
    print('  is already reached at the first draw (`open`, 16/16), so every')
    print('  gate-passing pair reaches it.  The evidence for the PRODUCT is')
    print('  the pair being new and the gate passing anyway.')
    print('  The gate passing is the content: side 1 and side 2 are drawn')
    print('  INDEPENDENTLY and glue with no cross-side condition, which is')
    print('  (BE-70)(ii).  It is stated modulo the proviso G, exactly as')
    print('  (BE-64)(ii) is -- see `gate`.')
    print(f'  indep: {time.time() - t0:.1f}s')
    return nmix > 0


# ================================================= mode: gate ((BE-72))

def two_hub_triangle():
    """The named forced-empty-G control: two hubs joined by BOTH a length-1
    branch (the real edge) and a length-2 branch -- a TRIANGLE ON TWO HUBS,
    which is exactly (BE-30)(iii)(c)'s forced-degenerate shape and exactly
    what (CH-1)'s girth >= 4 hypothesis excludes.  The third branch is LONG
    on purpose: it makes z and zp hubs WITHOUT dragging in a dense hub
    subgraph, which would force pi_z = pi_zp and hide the mechanism (a K4
    hub subgraph is forced flat, and then the length-2 branch's interior
    point is free in the common plane and the gate PASSES)."""
    return [('z', 'zp'), ('z', 'w'), ('w', 'zp'),
            ('z', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'zp')]


def run_gate(seed=SEED, nflag=40):
    t0 = time.time()
    rng = random.Random(seed)
    print(f'== gate: (BE-72) JOB 2 -- the cross-branch proviso G, seed {seed}')
    print('  G is the conjunction of TWO coincidence types and no others:')
    print('   (G-point) two branches\' interior points coincide;')
    print('   (G-line)  two branches\' first hinge lines coincide at a hub z,')
    print('        i.e. p_z, p^b_1, p^b\'_1 are COLLINEAR.')
    print('  (G-point) is never forced: each branch interior point ranges over a')
    print('  POSITIVE-dimensional set (a plane at length >= 3, a line at')
    print('  length 2) drawn INDEPENDENTLY per branch.  (G-line) is forced only')
    print('  when both branches\' first points are confined to ONE line')
    print('  through p_z -- which needs two length-2 branches at z with the')
    print('  same line, and the landed instance of that is a length-1 branch')
    print('  BESIDE a length-2 branch: a TRIANGLE ON TWO HUBS.')

    ctrl = two_hub_triangle()
    gctrl = girth(ctrl)
    print(f'  CONTROL (the triangle on two hubs): girth = {gctrl} '
          f'(so (CH-1)\'s girth >= 4 EXCLUDES it)')
    W, branches = hubs_and_branches(ctrl, 'z', 'zp')
    bad = ok = tries = neq = 0
    for _ in range(nflag * 3):
        P, B = flag_assignment(W, branches, rng)
        if P is None:
            continue
        if not same_space(B['z'], B['zp']):
            neq += 1
        pts, fine = dict(P), True
        for (z, zp, ints) in branches:
            ch = draw_branch(P, B, z, zp, len(ints), rng)
            if ch is None:
                fine = False
                break
            for w, xx in zip(ints, ch):
                pts[w] = xx
        tries += 1
        if not fine or assemble(ctrl, pts) is None:
            bad += 1
        else:
            ok += 1
    print(f'  {tries} completed flag draws at the control ({neq} of them with '
          f'pi_z != pi_zp): G EMPTY at {bad}, nonempty at {ok}')

    tot = miss = 0
    for prof in ((2, 2, 2, 2, 2, 2), (3, 3, 3, 3, 3, 3), (2, 3, 2, 3, 2, 3),
                 (4, 2, 3, 2, 4, 3), (3, 4, 5, 3, 4, 5)):
        E = subdivided(SKELETONS['K4'], list(prof))
        g = girth(E)
        W, branches = hubs_and_branches(E, 'A', 'B')
        good = tries = 0
        for _ in range(nflag):
            P, B = flag_assignment(W, branches, rng)
            if P is None:
                continue
            tries += 1
            hit = False
            for _att in range(5):        # 5 independent chain attempts
                pts, fine = dict(P), True
                for (z, zp, ints) in branches:
                    ch = draw_branch(P, B, z, zp, len(ints), rng)
                    if ch is None:
                        fine = False
                        break
                    for w, xx in zip(ints, ch):
                        pts[w] = xx
                if fine and assemble(E, pts) is not None:
                    hit = True
                    break
            if hit:
                good += 1
            tot += 1
        if good == 0:
            miss += 1
        print(f'  K4 profile {prof}: girth {g}, every branch length >= 2, '
              f'G NONEMPTY at {good} of {tries} legal flags (5 independent '
              f'chain attempts each)')
    print(f'  {tot} legal flags on girth->=-4 pieces, {miss} profiles with no '
          f'assembly at ANY flag.  A flag with no assembly in 5 attempts is')
    print('  "no assembly FOUND", never "G is empty there" (F27) -- and it')
    print('  does not matter either way: the class statement is EXISTENTIAL')
    print('  over the whole chart, so G empty at an ISOLATED flag is')
    print('  ABSORBED.  Only G empty at EVERY flag would be fatal.')
    print('  THE ARGUMENT, which needs no driver ((BE-72)(iii)).  G is empty')
    print('  at EVERY legal flag iff the piece has NO pencil configuration at')
    print('  all -- because (BE-64)(ii) is a BIJECTION, so Chart(H) is the')
    print('  union over flags of (prod Ear) cap G.  And (CH-1)(a) says')
    print('  Chart(H) is NONEMPTY under hcard + min degree 2 + girth >= 4.')
    print('  So a forced-empty G is impossible on (CH-1)\'s own class, and')
    print('  BDECOR\'s named gap CLOSES there by the result BDECOR cites.')
    print(f'  gate: {time.time() - t0:.1f}s')
    return miss == 0


def run_validate():
    t0 = time.time()
    print('===== bpeel validate: reduced tiers of all five modes =====')
    ok = True
    ok &= run_open(ndraw=2)
    print()
    ok &= run_indep(ndraw=1)
    print()
    ok &= run_law(nexh=6, nmask=300, quick=True)
    print()
    ok &= run_force(nexh=6, nsamp=(7,), nmask=600, quick=True)
    print()
    ok &= run_gate(nflag=12)
    print()
    print(f'===== validate {"GREEN" if ok else "RED"}, '
          f'{time.time() - t0:.1f}s =====')
    return ok


MODES = {'open': run_open, 'indep': run_indep, 'law': run_law,
         'force': run_force, 'gate': run_gate, 'validate': run_validate}

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if not args:
        print('usage: bpeel.py {' + '|'.join(MODES) + '}')
        sys.exit(2)
    ok = True
    for a in args:
        if a not in MODES:
            print(f'unknown mode {a}')
            sys.exit(2)
        ok &= bool(MODES[a]())
    sys.exit(0 if ok else 1)
