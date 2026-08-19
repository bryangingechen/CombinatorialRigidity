"""GBAL -- the fifteenth kernel-(K) direction: INPUT (X), balance
existence in the (GR-47) normal form (spec: notes/Pencil-fanout.md
S"Fifteenth direction -- GBAL (sixth fan-out)").

TARGET: route-ledger entry 5's balance half -- per odd-carrying habitat
shape, exhibit a parity-consistent configuration whose odd-branch
majority pattern is BALANCED (exactly half the odd branches on each
side).  GDESC's (GR-46) Cor. 1 closed the move-availability route
(descent over the FULL (GR-45) family IS the balance half), so this
pass attacks EXISTENCE directly, by an instrument outside the move
calculus.

The chain this pass lands (each clause has the mode that certifies it):

  (GR-49) THE Z-FORM.  Parity-consistent minority maps together with a
  chosen potential are EXACTLY the "admissible dart colourings": one bit
  z_i per branch, the dart at the u-end of branch i coloured z_i and the
  dart at the w-end coloured z_i xor tau_i (tau_i = [l_i even]), such
  that NO hub sees three equal dart colours.  Under the bijection the
  odd-branch majority pattern is literally z restricted to the odd
  branches.  (--zform)

  (GR-50) THE ORIENTATION CRITERION.  Fix the odd branches' colours by a
  balanced pattern p.  Every EVEN branch carries exactly one A-dart and
  one B-dart, so choosing z on the even branches is exactly ORIENTING
  them (head = the A-end), and the hub condition becomes
  l_v <= indeg(v) <= u_v with l_v = max(0, 1 - o_v),
  u_v = min(d_v, 2 - o_v), where o_v = the number of A-coloured odd
  darts at v and d_v = the number of even branches at v.  Balance is
  therefore decided EXACTLY, in polynomial time, over the <= C(6,3) = 20
  balanced patterns.  (--oracle)

  (GR-51) THE WEIGHT CRITERION.  That orientation is feasible iff the
  two-sided Hall condition holds, and after the cubic identity
  2 e_H(S) + dH(S) = sum_S d_v it collapses to a LOCAL inequality: for
  every hub set S,  sum_{v in S} w_A(v) + dH(S) >= 0  (and the same for
  B), with w_A(v) = 2 u_v - d_v.  w_A(v) = -1 EXACTLY at hubs carrying
  two odd branches both coloured A, and w_A(v) >= 0 everywhere else.
  (--oracle)

  (GR-52) THE PARITY THEOREM.  If the balanced pattern has at most ONE
  monochromatic-pair hub on each side, both inequalities hold -- because
  a violating set would have to consist of the single -1 hub (even
  degree 1), q = 3 hubs (even degree 0) and q = 1 same-colour hubs (even
  degree 2), whose internal even degree sums to an ODD number, and that
  sum is 2 e_H(S).  (--split)

  (GR-53) THE SPLITTING LEMMA.  The constraint structure a shape imposes
  on its <= 6 odd branches is a multiset of PAIRS (one per hub carrying
  exactly two odd branches) and TRIPLES (one per hub carrying three), in
  which every odd branch lies in at most 2 constraints -- because it has
  two ends.  Every such structure admits a balanced split with NO
  monochromatic triple and at most ONE monochromatic pair per side.
  Proved by exhaustion over the MAXIMAL structures (adding constraints
  only makes the requirement harder, so maximal suffices).  (--split)

  (GR-54) THE BALANCE THEOREM = INPUT (X), DISCHARGED.  At every
  connected cubic loop-free hub multigraph whose odd branches number
  2k <= 6, a balanced admissible configuration EXISTS.  Chain:
  (GR-53) supplies a balanced pattern with <= 1 monochromatic-pair hub
  per side and no monochromatic triple; (GR-52) turns that into the
  (GR-51) inequalities; (GR-50) turns those into a feasible orientation;
  (GR-49) turns the orientation into a parity-consistent balanced
  (m, c).  Bridgelessness is NOT used, and the parity layer comes out
  free (an admissible z IS a parity-consistent map).  (--thm)

Modes:
  --zform    (GR-49) certified: the full 2^M admissible-z cube and the
             full 3^n parity census in bijection, pattern = z|_O, and
             the (GR-45) legality test re-derived as a per-hub
             condition on a flip SET (exhaustive over all 2^M subsets
             at small shapes).
  --oracle   (GR-50)/(GR-51): the oracle vs the exhaustive z-cube at
             EVERY habitat shape of the Lambda = empty D = 0 pool; the
             weight criterion vs the oracle over all 2^n hub sets.
  --two      the minimal odd stratum 2k = 2 (the spec's opening case),
             and the route-note-(b) dichotomy CORRECTION.
  --split    (GR-52)'s hypothesis and (GR-53)'s exhaustion.
  --thm      (GR-54) end to end: the good split found, the orientation
             built, the certificate re-verified through cm_solve /
             odd_balance / cflank.admissible -- over the whole pool, the
             n = 30..60 necklaces, and seeded random cubic stress.
  --adv      F13 falsification controls, each with a must-reject or
             must-fire witness and a negative control.
  --validate all six, in the order above.

Rank-free throughout: gexist.fully_good_rank is never imported or
called and no d_fg claim is made anywhere.  Exact integers / GF(2)
throughout; no floating point; rngs seeded per mode with the seed
printed; no `set` printed; nothing samples a placement (S(K-clos)
(AC-9)) -- `rand_cubic` samples a GRAPH.  Wall-clock [Ns] annotations
are inherently non-deterministic; every other byte is seed-stable.
"""
import argparse
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from cflank import admissible, cubic_habitat                           # noqa: E402
from gcap import pool_specs                                            # noqa: E402
from gunif import WITNESSES                                            # noqa: E402
from gorient import cm_colouring, cm_solve, odd_balance, prep_shape    # noqa: E402
from gdev import nk_specs, habitat_by_lemma                            # noqa: E402
from gadm import nko_specs                                             # noqa: E402
from gpsa import (branches_at, is_bridgeless, delta_of, parity_census,  # noqa: E402
                  pattern_of, nkp_specs, nk55_specs, nko2v_specs)

R_SEED = 20260819


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive (checked against the README index and
# the Divergences table).  `dart_col`/`z_admissible`/`z_to_map`/`map_to_z`
# are the (GR-49) bijection; `assign_feasible` the (GR-50) degree-constrained
# assignment WITH its infeasibility certificate (the violating hub set);
# `balance_oracle` the exact per-shape decision; `weight_of`/
# `weight_criterion` the (GR-51) local form; `constraints_of`/`good_split`/
# `maximal_structures` the (GR-53) combinatorics; `rand_cubic` a seeded
# random connected bridgeless cubic multigraph sampler (a GRAPH sampler --
# no placement is drawn, so S(K-clos) (AC-9) does not apply).


def odd_idx(specs):
    """The odd-branch indices, in gpsa.parity_census's own order."""
    return [i for i, (_u, _w, L) in enumerate(specs) if L % 2 == 1]


def dart_col(specs, z, v, i):
    """(GR-49): the colour of the dart at hub `v` on branch `i`.  The
    u-end dart is z[i]; the w-end dart is z[i] xor tau_i."""
    (u, w, L) = specs[i]
    if v == u:
        return z[i]
    assert v == w, "hub not an end of the branch"
    return z[i] ^ (1 if L % 2 == 0 else 0)


def z_admissible(specs, n, binc, z):
    """(GR-49): no hub sees three equal dart colours."""
    for v in range(n):
        a, b, c = (dart_col(specs, z, v, i) for i in binc[v])
        if a == b == c:
            return False
    return True


def z_to_map(specs, n, binc, z):
    """(GR-49) forward: the (m, c) of an admissible z -- c(v) = the
    majority dart colour at v, m(v) = the minority dart."""
    m, c = {}, {}
    for v in range(n):
        cs = [dart_col(specs, z, v, i) for i in binc[v]]
        maj = 0 if cs.count(0) >= 2 else 1
        c[v] = maj
        lone = [t for t in range(3) if cs[t] != maj]
        assert len(lone) == 1, "hub not 2-1 split: z was not admissible"
        i = binc[v][lone[0]]
        m[v] = (i, 0 if v == specs[i][0] else 1)
    return m, c


def map_to_z(specs, m, c):
    """(GR-49) backward: the z of a parity-consistent (m, c)."""
    return [c[specs[i][0]] ^ (1 if m[specs[i][0]] == (i, 0) else 0)
            for i in range(len(specs))]


def z_pattern(z, oidx):
    """The odd-branch majority pattern of z, in pattern_of's bit order."""
    bits = 0
    for j, i in enumerate(oidx):
        if z[i]:
            bits |= 1 << j
    return bits


def flip_legal(specs, n, binc, m, F):
    """(GR-49) corollary: the (GR-45) legality test in z-coordinates --
    `F` carries an admissible z to an admissible z + chi_F iff at every
    hub `[m(v) in F] == [|F cap star(v)| >= 2]`.  T1 is |F| = 1 at a
    dart-free branch, T2 a star, K3 a pair-star."""
    for v in range(n):
        deg = sum(1 for i in binc[v] if i in F)
        if (m[v][0] in F) != (deg >= 2):
            return False
    return True


def bounds_of(specs, n, oidx, p):
    """(GR-50): (o, q, d, lo, hi) for the pattern `p` (p[j] = the colour
    of oidx[j]; colour 0 = A).  lo/hi bound the number of even branches
    at v whose A-end is v."""
    o = [0] * n
    q = [0] * n
    for j, i in enumerate(oidx):
        (u, w, _L) = specs[i]
        for v in (u, w):
            q[v] += 1
            if p[j] == 0:
                o[v] += 1
    d = [3 - q[v] for v in range(n)]
    assert all(x >= 0 for x in d), "hub with more than three odd branches"
    lo = [max(0, 1 - o[v]) for v in range(n)]
    hi = [min(d[v], 2 - o[v]) for v in range(n)]
    return o, q, d, lo, hi


def assign_feasible(nv, edges, lo, hi):
    """(GR-50)/(GR-51): assign every edge to ONE endpoint with
    lo[v] <= load[v] <= hi[v].  Returns (assignment, None) on success or
    (None, R) with R a hub set violating the two-sided Hall condition --
    the infeasibility CERTIFICATE.  Augmenting-path algorithm, exact
    integers; this is the constructive half of (GR-51)'s proof."""
    bad = {v for v in range(nv) if lo[v] > hi[v]}
    if bad:
        return None, bad
    asg = [e[0] for e in edges]
    load = [0] * nv
    for a in asg:
        load[a] += 1
    inc = {v: [] for v in range(nv)}
    for j, (a, b) in enumerate(edges):
        inc[a].append(j)
        inc[b].append(j)

    def other(j, v):
        a, b = edges[j]
        return b if a == v else a

    for phase in (0, 1):
        moved = True
        while moved:
            moved = False
            for v in range(nv):
                while (load[v] > hi[v]) if phase == 0 else (load[v] < lo[v]):
                    par = {v: None}
                    stack = [v]
                    tgt = None
                    while stack and tgt is None:
                        x = stack.pop()
                        for j in inc[x]:
                            y = other(j, x)
                            if phase == 0 and asg[j] != x:
                                continue
                            if phase == 1 and asg[j] != y:
                                continue
                            if y in par:
                                continue
                            par[y] = (x, j)
                            ok = (load[y] < hi[y]) if phase == 0 \
                                else (load[y] > lo[y])
                            if ok:
                                tgt = y
                                break
                            stack.append(y)
                    if tgt is None:
                        return None, set(par)
                    y = tgt
                    while par[y] is not None:
                        x, j = par[y]
                        if phase == 0:
                            asg[j] = y
                            load[y] += 1
                            load[x] -= 1
                        else:
                            asg[j] = x
                            load[x] += 1
                            load[y] -= 1
                        y = x
                    moved = True
    for v in range(nv):
        assert lo[v] <= load[v] <= hi[v], "assignment out of bounds"
    return asg, None


def z_of_orientation(specs, oidx, p, even, asg):
    """(GR-49)+(GR-50): rebuild the branch colouring z from a balanced
    pattern and an even-branch orientation."""
    z = [0] * len(specs)
    for j, i in enumerate(oidx):
        z[i] = p[j]
    for t, i in enumerate(even):
        (u, _w, _L) = specs[i]
        z[i] = 0 if asg[t] == u else 1
    return z


def feasible_at(specs, n, oidx, p):
    """The (GR-50) decision at ONE pattern: returns z or None."""
    _o, _q, _d, lo, hi = bounds_of(specs, n, oidx, p)
    if any(hi[v] < lo[v] for v in range(n)):
        return None
    oset = set(oidx)
    even = [i for i in range(len(specs)) if i not in oset]
    edges = [(specs[i][0], specs[i][1]) for i in even]
    asg, _R = assign_feasible(n, edges, lo, hi)
    if asg is None:
        return None
    return z_of_orientation(specs, oidx, p, even, asg)


def balanced_patterns(k2):
    """Every balanced colouring of the 2k odd branches (colour 0 = A)."""
    if k2 == 0:
        return [()]
    return [c for c in itertools.product((0, 1), repeat=k2)
            if 2 * sum(c) == k2]


def balance_oracle(specs, n, oidx, want_all=False):
    """(GR-50): the EXACT balance decision.  Returns (z, p) for the first
    feasible balanced pattern, or (None, None) if NO balanced pattern is
    feasible -- which would be d_adm = infinity, E1 clause (v)."""
    feas = []
    for p in balanced_patterns(len(oidx)):
        z = feasible_at(specs, n, oidx, p)
        if z is None:
            continue
        if want_all:
            feas.append((tuple(p), z))
            continue
        return z, tuple(p)
    if want_all:
        return feas, None
    return None, None


def verify_balanced(specs, n, binc, oidx, z, ground=None):
    """Re-verify a certificate through the LANDED primitives: admissible
    z, round-trip to a cm_solve-consistent (m, c), odd_balance exactly
    half-and-half, pattern = z|_O.  With `ground` = prep_shape's
    (edges, allverts, hm), also assert cflank.admissible on the induced
    colouring -- the (GR-37)(i) ground truth."""
    assert z_admissible(specs, n, binc, z), "certificate not admissible"
    m, c = z_to_map(specs, n, binc, z)
    sols = cm_solve(specs, m)
    assert sols is not None, "certificate not parity-consistent"
    assert c in sols, "certificate potential not a cm_solve solution"
    na, nb = odd_balance(specs, m, c)
    assert na == nb, f"certificate not balanced: ({na}, {nb})"
    assert z_pattern(z, oidx) == pattern_of(specs, m, c, oidx), \
        "pattern != z|_O"
    if ground is not None:
        edges, allverts, hm = ground
        col = cm_colouring(specs, m, c)
        assert admissible(edges, allverts, hm, col), \
            "certificate REJECTED by cflank.admissible -- ground truth"
    return na, nb


def weight_of(o_v, q_v, colour):
    """(GR-51): w(v) = 2 u_v - d_v for the A-side (colour 0) or
    d_v - 2 l_v for the B-side (colour 1).  Equals -1 EXACTLY at a hub
    carrying two odd branches both of that colour."""
    a = o_v if colour == 0 else q_v - o_v
    b = q_v - a
    assert a <= 2, "monochromatic triple hub: the bounds are infeasible"
    return (3 - q_v) if b >= 1 else (1 - a)


def weight_criterion(specs, n, oidx, p):
    """(GR-51) checked over ALL 2^n hub sets (n <= 20 guard).  Returns
    (okA, okB, worstA, worstB)."""
    assert n <= 20, "subset enumeration guard"
    o, q, _d, lo, hi = bounds_of(specs, n, oidx, p)
    if any(hi[v] < lo[v] for v in range(n)):
        return False, False, None, None
    wA = [weight_of(o[v], q[v], 0) for v in range(n)]
    wB = [weight_of(o[v], q[v], 1) for v in range(n)]
    oset = set(oidx)
    even = [(u, w) for i, (u, w, _L) in enumerate(specs) if i not in oset]
    okA = okB = True
    worstA = worstB = None
    for mask in range(1 << n):
        S = [v for v in range(n) if (mask >> v) & 1]
        dH = sum(1 for (u, w) in even
                 if ((mask >> u) & 1) != ((mask >> w) & 1))
        sA = sum(wA[v] for v in S) + dH
        sB = sum(wB[v] for v in S) + dH
        if worstA is None or sA < worstA:
            worstA = sA
        if worstB is None or sB < worstB:
            worstB = sB
        okA = okA and sA >= 0
        okB = okB and sB >= 0
    return okA, okB, worstA, worstB


def brute_balance(specs, n, binc, oidx):
    """Exhaustive 2^M search for a balanced admissible z -- the ground
    truth the oracle is checked against (M <= 20 guard)."""
    M = len(specs)
    assert M <= 20, "z-cube enumeration guard"
    k2 = len(oidx)
    for zz in itertools.product((0, 1), repeat=M):
        if 2 * sum(zz[i] for i in oidx) != k2:
            continue
        if z_admissible(specs, n, binc, list(zz)):
            return list(zz)
    return None


def constraints_of(specs, n, oidx):
    """(GR-53): the shape's constraint structure on its odd branches --
    one PAIR per hub carrying exactly two odd branches, one TRIPLE per
    hub carrying three, as tuples of positions in `oidx`.  Every odd
    branch lies in at most 2 constraints (it has two ends)."""
    pos = {i: j for j, i in enumerate(oidx)}
    pairs, triples = [], []
    at = {v: [] for v in range(n)}
    for i in oidx:
        (u, w, _L) = specs[i]
        at[u].append(pos[i])
        at[w].append(pos[i])
    for v in range(n):
        if len(at[v]) == 2:
            pairs.append(tuple(sorted(at[v])))
        elif len(at[v]) == 3:
            triples.append(tuple(sorted(at[v])))
        else:
            assert len(at[v]) <= 3, "hub with four odd branches"
    return pairs, triples


def split_cost(p, pairs, triples):
    """(tA, tB, bad_triples) for the colouring p."""
    tA = sum(1 for (a, b) in pairs if p[a] == 0 and p[b] == 0)
    tB = sum(1 for (a, b) in pairs if p[a] == 1 and p[b] == 1)
    bad = sum(1 for t in triples if p[t[0]] == p[t[1]] == p[t[2]])
    return tA, tB, bad


def good_split(k2, pairs, triples):
    """(GR-53): a balanced pattern with NO monochromatic triple and at
    most one monochromatic pair per side, or None."""
    best = None
    for p in balanced_patterns(k2):
        tA, tB, bad = split_cost(p, pairs, triples)
        if bad == 0 and tA <= 1 and tB <= 1:
            key = (tA + tB, p)
            if best is None or key < best[0]:
                best = (key, p)
    return None if best is None else best[1]


def maximal_structures(k2):
    """Every MAXIMAL constraint structure on k2 labelled odd branches:
    a multiset of 2- and 3-subsets with every element in <= 2
    constraints and at most ONE element left with spare degree (so no
    further constraint can be added).  Adding constraints only makes the
    (GR-53) requirement harder, so maximal structures suffice."""
    types = [tuple(c) for r in (2, 3)
             for c in itertools.combinations(range(k2), r)]
    out = []
    deg = [0] * k2
    cur = []

    def rec(t):
        if t == len(types):
            spare = sum(1 for v in range(k2) if deg[v] < 2)
            if spare <= 1:
                out.append((tuple(c for c in cur if len(c) == 2),
                            tuple(c for c in cur if len(c) == 3)))
            return
        c = types[t]
        for mult in range(3):
            if mult and any(deg[v] + mult > 2 for v in c):
                break
            for _ in range(mult):
                cur.append(c)
            for v in c:
                deg[v] += mult
            rec(t + 1)
            for v in c:
                deg[v] -= mult
            for _ in range(mult):
                cur.pop()

    rec(0)
    return out


def rand_cubic(n, rng, tries=600):
    """A seeded random CONNECTED, LOOP-FREE, BRIDGELESS cubic multigraph
    on n hubs, as (u, w) pairs.  A GRAPH sampler; no placement is drawn,
    so S(K-clos) (AC-9) does not apply.  None if the tries run out."""
    for _ in range(tries):
        stubs = [v for v in range(n) for _ in range(3)]
        rng.shuffle(stubs)
        es = [(stubs[2 * i], stubs[2 * i + 1]) for i in range(3 * n // 2)]
        if any(u == w for (u, w) in es):
            continue
        specs = [(u, w, 2) for (u, w) in es]
        adj = {v: [] for v in range(n)}
        for (u, w) in es:
            adj[u].append(w)
            adj[w].append(u)
        seen, st = {0}, [0]
        while st:
            v = st.pop()
            for u in adj[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        if len(seen) != n:
            continue
        if not is_bridgeless(specs, n):
            continue
        return es
    return None


def pool_cases():
    """Every habitat shape of the Lambda = empty, D = 0 pool (cflank's
    `--cubic` pool behind the (GR-25) cut criterion) -- EXHAUSTIVE, not
    a subsample."""
    out = []
    for n, specs in pool_specs():
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        out.append((n, [tuple(s) for s in specs]))
    return out


def named_cases():
    """The named large shapes: GUNIF's W-witnesses and GPSA/GADM's
    commissioned odd-rich necklace constructions (reused read-only)."""
    out = []
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    for tag in ('W3M', 'W3', 'W4', 'W5'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        out.append((tag, n, [tuple(s) for s in specs]))
    specs, _pent = nko2v_specs()
    out.append(('NKo2v', 10, specs))
    for m in (6, 8, 10, 12):
        sp, _pent = nkp_specs(m)
        out.append((f'NKp({m})', 5 * m, sp))
        sp, _pent = nk55_specs(m)
        out.append((f'NK55({m})', 5 * m, sp))
        sp, _pent, _F, _ch = nk_specs(m)
        out.append((f'NK({m})', 5 * m, sp))
        out.append((f'NKo({m})', 5 * m, nko_specs(m)[0]))
    return out


def random_cases(rng, sizes, per, k2s, conc_rate):
    """Seeded random cubic bridgeless shapes with prescribed odd counts;
    `conc_rate` of the placements are deliberately CONCENTRATED on one
    hub's neighbourhood (the adversarial side of the sweep)."""
    out = []
    conc = 0
    for n in sizes:
        for _t in range(per):
            es = rand_cubic(n, rng)
            if es is None:
                continue
            M = len(es)
            for k2 in k2s:
                if M < k2:
                    continue
                sp = [[u, w, 2] for (u, w) in es]
                if rng.random() < conc_rate:
                    v0 = rng.randrange(n)
                    pref = sorted(
                        range(M),
                        key=lambda i: (v0 not in es[i], rng.random()))
                    idxs = pref[:k2]
                    conc += 1
                else:
                    idxs = rng.sample(range(M), k2)
                for i in idxs:
                    sp[i][2] = 3
                sp = [tuple(s) for s in sp]
                if len(odd_idx(sp)) != k2:
                    continue
                out.append((f'rand(n={n},2k={k2})', n, sp))
    return out, conc


# ------------------------------------------------- [GBL-1] --zform ----------

def leg_zform():
    """[GBL-1] (GR-49) certified."""
    t0 = time.time()
    print("[GBL-1] (GR-49) the z-form: admissible dart colourings = "
          "parity-consistent (m, c), with pattern = z|_O")
    cases = [(f'pool#{j + 1}', n, sp)
             for j, (n, sp) in enumerate(pool_cases())]
    print(f"  pool habitat shapes (EXHAUSTIVE; the (GR-25) cut criterion "
          f"as gate): {len(cases)}")
    cases += [(t, n, sp) for (t, n, sp) in named_cases() if n <= 10]
    step = 37
    tot_cfg = tot_shape = cube_shapes = 0
    for idx, (tag, n, specs) in enumerate(cases):
        binc = branches_at(specs, n)
        assert is_bridgeless(specs, n), f"{tag}: hub multigraph has a bridge"
        maps, oidx, _dim, _total = parity_census(specs, n)
        tot_shape += 1
        seen = set()
        for (mm, sols) in maps:
            for c in sols:
                z = map_to_z(specs, mm, c)
                assert z_admissible(specs, n, binc, z), \
                    f"{tag}: a parity-consistent (m, c) has inadmissible z"
                m2, c2 = z_to_map(specs, n, binc, z)
                assert m2 == mm and c2 == c, f"{tag}: z round-trip failed"
                assert z_pattern(z, oidx) == pattern_of(specs, mm, c, oidx), \
                    f"{tag}: pattern != z|_O"
                seen.add(tuple(z))
                tot_cfg += 1
        assert len(seen) == 2 * len(maps), f"{tag}: z / map count mismatch"
        if idx % step == 0 or tag in ('W3M', 'W3', 'NKo2v'):
            cnt = 0
            for zz in itertools.product((0, 1), repeat=len(specs)):
                if z_admissible(specs, n, binc, list(zz)):
                    cnt += 1
                    assert tuple(zz) in seen, \
                        f"{tag}: admissible z missing from the census"
            assert cnt == len(seen), f"{tag}: cube / census counts differ"
            cube_shapes += 1
    print(f"  bijection asserted at {tot_shape} shapes / {tot_cfg} "
          f"configurations (every (m, c) of the FULL 3^n census, both "
          f"potentials); the FULL 2^M admissible-z cube enumerated and "
          f"matched exactly at {cube_shapes} of them")
    # (GR-49)'s corollary: the (GR-45) legality test in z-coordinates,
    # checked EXHAUSTIVELY over (admissible z, flip set F) at small shapes
    fl_shapes = fl_pairs = t1s = 0
    for (tag, n, specs) in cases[::811]:
        M = len(specs)
        if M > 9:
            continue
        binc = branches_at(specs, n)
        fl_shapes += 1
        for zz in itertools.product((0, 1), repeat=M):
            zl = list(zz)
            if not z_admissible(specs, n, binc, zl):
                continue
            mm, _cc = z_to_map(specs, n, binc, zl)
            darted = {mm[v][0] for v in range(n)}
            for fm in range(1 << M):
                F = {i for i in range(M) if (fm >> i) & 1}
                z2 = [zl[i] ^ (1 if i in F else 0) for i in range(M)]
                assert flip_legal(specs, n, binc, mm, F) == \
                    z_admissible(specs, n, binc, z2), \
                    f"{tag}: the (GR-45) flip-set characterization fails"
                fl_pairs += 1
                if len(F) == 1:
                    i = next(iter(F))
                    assert flip_legal(specs, n, binc, mm, F) == \
                        (i not in darted), \
                        f"{tag}: single-branch flip != free-T1 condition"
                    t1s += 1
    print(f"  the (GR-45) legality test in z-coordinates -- F is legal "
          f"iff [m(v) in F] == [|F cap star(v)| >= 2] at every hub -- "
          f"asserted EXHAUSTIVELY over {fl_pairs} (admissible z, flip "
          f"set) pairs at {fl_shapes} shapes (all 2^M subsets each), "
          f"with the |F| = 1 case asserted equal to (GR-45)(iii)'s "
          f"free-T1 condition at {t1s} of them")
    print("  => (GR-49): the (c, m) model, the coset Phi, the (GR-47) "
          "(X, phi, T) normal form and its pattern formula are all "
          "ABSORBED into one bit per branch, and the (GR-45) move "
          "calculus becomes a per-hub condition on a flip SET")
    print(f"  [{time.time() - t0:.1f}s]")
    print()


# ------------------------------------------------ [GBL-2] --oracle ----------

def leg_oracle():
    """[GBL-2] (GR-50)/(GR-51)."""
    t0 = time.time()
    print("[GBL-2] (GR-50) the orientation oracle; (GR-51) the weight "
          "criterion")
    pool = pool_cases()
    bal = 0
    for (n, specs) in pool:
        binc = branches_at(specs, n)
        oidx = odd_idx(specs)
        z, _p = balance_oracle(specs, n, oidx)
        b = brute_balance(specs, n, binc, oidx)
        assert (z is None) == (b is None), \
            f"ORACLE DISAGREES WITH THE EXHAUSTIVE CUBE at n={n} {specs}"
        assert z is not None, \
            f"UNBALANCED HABITAT SHAPE -- d_adm = oo, E1(v): n={n} {specs}"
        verify_balanced(specs, n, binc, oidx, z)
        bal += 1
    print(f"  pool: {len(pool)} habitat shapes; oracle == exhaustive 2^M "
          f"decision at EVERY one (0 disagreements); balanced at "
          f"{bal}/{len(pool)}")
    print("  => entry 5's balance half holds at EVERY shape of the "
          "Lambda = empty D = 0 pool, by EXHAUSTIVE decision (not a "
          "sample, not a cap)")
    checked = disagree = 0
    for (n, specs) in pool[::3]:
        oidx = odd_idx(specs)
        for p in balanced_patterns(len(oidx)):
            feas = feasible_at(specs, n, oidx, p) is not None
            okA, okB, _wa, _wb = weight_criterion(specs, n, oidx, p)
            checked += 1
            if (okA and okB) != feas:
                disagree += 1
                print(f"  CRITERION/ORACLE DISAGREE n={n} p={p} {specs}")
    print(f"  (GR-51) weight criterion vs orientation feasibility: "
          f"{checked} (shape, balanced pattern) pairs, {disagree} "
          f"disagreements (all 2^n hub sets scanned per pair)")
    assert disagree == 0, "(GR-51) refuted -- HEADLINE"
    print(f"  [{time.time() - t0:.1f}s]")
    print()


# --------------------------------------------------- [GBL-3] --two ----------

def leg_two():
    """[GBL-3] the minimal odd stratum, and the route-note-(b)
    dichotomy CORRECTION."""
    t0 = time.time()
    print("[GBL-3] the minimal odd stratum 2k = 2, and the route-note-(b) "
          "correction")
    rng = random.Random(R_SEED + 3)
    print(f"  seed {R_SEED + 3}")
    cases = [(f'pool#{j + 1}', n, sp)
             for j, (n, sp) in enumerate(pool_cases())]
    cases += [(t, n, sp) for (t, n, sp) in named_cases()]
    rand, _c = random_cases(rng, (4, 6, 8, 10, 12, 14, 20, 30), 40, (2,), 0.0)
    two = [(t, n, sp) for (t, n, sp) in cases + rand
           if len(odd_idx(sp)) == 2]
    nz = okc = 0
    for (tag, n, specs) in two:
        oidx = odd_idx(specs)
        binc = branches_at(specs, n)
        pairs, triples = constraints_of(specs, n, oidx)
        assert not triples, f"{tag}: a triple at 2k = 2 is impossible"
        for p in balanced_patterns(2):
            tA, tB, bad = split_cost(p, pairs, triples)
            assert tA == 0 and tB == 0 and bad == 0, \
                f"{tag}: a monochromatic-pair hub at 2k = 2 -- refutes " \
                f"the (GR-54) minimal-stratum corollary"
            nz += 1
            if n <= 14:
                okA, okB, wa, wb = weight_criterion(specs, n, oidx, p)
                assert okA and okB and wa >= 0 and wb >= 0, \
                    f"{tag}: the weight criterion goes negative at 2k = 2"
                okc += 1
        z, _p = balance_oracle(specs, n, oidx)
        assert z is not None, f"{tag}: NO balanced z at 2k = 2"
        verify_balanced(specs, n, binc, oidx, z)
    print(f"  2k = 2 shapes: {len(two)} ({len(two) - len(rand)} habitat / "
          f"named, {len(rand)} seeded random cubic bridgeless with NO "
          f"habitat gate, n up to 30)")
    print(f"  monochromatic-pair hubs at a balanced pattern: 0 / {nz} "
          f"(shape, pattern) pairs -- so (GR-52)'s hypothesis holds "
          f"VACUOUSLY on the whole stratum; the weight criterion is "
          f"non-negative at {okc} of them (all 2^n hub sets each); a "
          f"balanced certificate is produced and re-verified through "
          f"cm_solve / odd_balance at every shape")
    par = onto = cut2 = 0
    for (tag, n, specs) in two:
        g1, g2 = odd_idx(specs)
        e1, e2 = set(specs[g1][:2]), set(specs[g2][:2])
        is_par = e1 == e2
        img = {(0, 0)}
        for v in range(n):
            cut = delta_of(specs, {v})
            g = (cut[g1], cut[g2])
            img |= {(a ^ g[0], b ^ g[1]) for (a, b) in img}
        is_onto = len(img) == 4
        assert is_onto == (not is_par), \
            f"{tag}: the corrected dichotomy fails -- onto {is_onto}, " \
            f"parallel {is_par}"
        par += is_par
        onto += is_onto
        adj = {v: [] for v in range(n)}
        for i, (u, w, _L) in enumerate(specs):
            if i in (g1, g2):
                continue
            adj[u].append(w)
            adj[w].append(u)
        seen, st = {0}, [0]
        while st:
            v = st.pop()
            for u in adj[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        cut2 += (len(seen) != n)
    print(f"  CORRECTION: the projection Phi -> GF(2)^O is ONTO at "
          f"{onto} / {len(two)} shapes and NOT onto at {len(two) - onto}; "
          f"the non-onto side is EXACTLY the PARALLEL-pair side "
          f"({par} parallel), asserted shape by shape -- a CYCLE-space "
          f"condition")
    print(f"  CORRECTION: {{gamma1, gamma2}} is a 2-EDGE CUT at {cut2} / "
          f"{len(two)} shapes -- a different (matching-side) condition, "
          f"and the two sets do not coincide, so route note (b)'s "
          f"'2-edge cut' reading names the wrong obstruction")
    hab2 = [(t, n, sp) for (t, n, sp) in two if not t.startswith('rand')]
    hpar4 = sum(1 for (_t, n, sp) in hab2 if n >= 4
                and set(sp[odd_idx(sp)[0]][:2]) == set(sp[odd_idx(sp)[1]][:2]))
    hcut = 0
    for (_t, n, sp) in hab2:
        g1, g2 = odd_idx(sp)
        adj = {v: [] for v in range(n)}
        for i, (u, w, _L) in enumerate(sp):
            if i in (g1, g2):
                continue
            adj[u].append(w)
            adj[w].append(u)
        seen, st = {0}, [0]
        while st:
            v = st.pop()
            for u in adj[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        hcut += (len(seen) != n)
    print(f"  habitat VACUITY: of {len(hab2)} habitat / named 2k = 2 "
          f"shapes, {hpar4} have a parallel odd pair at n >= 4 and "
          f"{hcut} have {{gamma1, gamma2}} as a 2-edge cut -- BOTH "
          f"readings of the dichotomy are vacuous here, and the n = 2 "
          f"theta shapes are the whole parallel exception")
    assert hpar4 == 0 and hcut == 0, "the habitat vacuity claim is refuted"
    print(f"  [{time.time() - t0:.1f}s]")
    print()


# ------------------------------------------------- [GBL-4] --split ----------

def leg_split():
    """[GBL-4] (GR-52)'s hypothesis and (GR-53)'s exhaustion."""
    t0 = time.time()
    print("[GBL-4] (GR-52) the parity theorem's hypothesis; (GR-53) the "
          "splitting lemma, by exhaustion")
    for k2 in (2, 4, 6):
        structs = maximal_structures(k2)
        worst = 0
        for (pairs, triples) in structs:
            p = good_split(k2, list(pairs), list(triples))
            assert p is not None, \
                f"(GR-53) REFUTED at 2k = {k2}: pairs={pairs} " \
                f"triples={triples} has NO good balanced split"
            tA, tB, bad = split_cost(p, list(pairs), list(triples))
            assert bad == 0 and tA <= 1 and tB <= 1
            worst = max(worst, tA + tB)
        print(f"  2k = {k2}: {len(structs)} MAXIMAL constraint structures "
              f"(every odd branch in <= 2 constraints, no further "
              f"constraint addable); a good balanced split exists at "
              f"EVERY one; worst total monochromatic-pair count = {worst}")
    print("  => (GR-53) holds; by monotonicity (a sub-structure's split "
          "cost is no larger) it holds for every constraint structure, "
          "maximal or not")
    # the structures really do arise: read them off the shapes and re-check
    seen_p = {}
    for (n, specs) in pool_cases():
        oidx = odd_idx(specs)
        if not oidx:
            continue
        pairs, triples = constraints_of(specs, n, oidx)
        for j in range(len(oidx)):
            deg = sum(1 for c in list(pairs) + list(triples) if j in c)
            assert deg <= 2, "an odd branch in three constraints"
        key = (len(oidx), len(pairs), len(triples))
        seen_p[key] = seen_p.get(key, 0) + 1
        p = good_split(len(oidx), pairs, triples)
        assert p is not None, f"no good split at n={n} {specs}"
        z = feasible_at(specs, n, oidx, p)
        assert z is not None, \
            f"(GR-52) REFUTED: good split infeasible at n={n} {specs}"
    print(f"  realized (2k, #pairs, #triples) profiles over the pool: "
          f"{dict(sorted(seen_p.items()))}")
    print(f"  [{time.time() - t0:.1f}s]")
    print()


# --------------------------------------------------- [GBL-5] --thm ----------

def leg_thm():
    """[GBL-5] (GR-54) end to end."""
    t0 = time.time()
    print("[GBL-5] (GR-54) the balance theorem, end to end: good split -> "
          "orientation -> certificate -> ground truth")
    rng = random.Random(R_SEED + 5)
    print(f"  seed {R_SEED + 5}")
    by_k = {}
    for (n, specs) in pool_cases():
        oidx = odd_idx(specs)
        binc = branches_at(specs, n)
        pairs, triples = constraints_of(specs, n, oidx)
        p = good_split(len(oidx), pairs, triples)
        assert p is not None, f"(GR-53) failed at n={n} {specs}"
        z = feasible_at(specs, n, oidx, p)
        assert z is not None, f"(GR-52) failed at n={n} {specs}"
        edges, allverts, hm, _i, _t, _tc, _a = prep_shape(specs)
        verify_balanced(specs, n, binc, oidx, z, (edges, allverts, hm))
        rec = by_k.setdefault(len(oidx), 0)
        by_k[len(oidx)] = rec + 1
    print(f"  pool, by odd count: {dict(sorted(by_k.items()))} -- the "
          f"theorem's own construction (NOT the search) produces a "
          f"balanced certificate at every one, and EVERY certificate is "
          f"accepted by cflank.admissible (the (GR-37)(i) ground truth)")
    print("  named / commissioned shapes -- the theorem's construction, "
          "with an EXACT verdict (not a capped sample) at n = 30..60:")
    for (tag, n, specs) in named_cases():
        oidx = odd_idx(specs)
        binc = branches_at(specs, n)
        pairs, triples = constraints_of(specs, n, oidx)
        p = good_split(len(oidx), pairs, triples)
        assert p is not None, f"{tag}: (GR-53) failed"
        z = feasible_at(specs, n, oidx, p)
        assert z is not None, f"{tag}: (GR-52) failed"
        na, nb = verify_balanced(specs, n, binc, oidx, z)
        _ok, why = habitat_by_lemma(n, [(u, w) for (u, w, _L) in specs],
                                    [L for (_u, _w, L) in specs])
        print(f"    {tag:<10} n={n:<3} 2k={len(oidx)}  BALANCED "
              f"({na},{nb}) at pattern {p}; habitat_by_lemma: {why}")
    rand, conc = random_cases(rng, (4, 6, 8, 10, 12, 16, 20, 30), 70,
                              (2, 4, 6), 0.5)
    for (tag, n, specs) in rand:
        oidx = odd_idx(specs)
        binc = branches_at(specs, n)
        pairs, triples = constraints_of(specs, n, oidx)
        p = good_split(len(oidx), pairs, triples)
        assert p is not None, f"{tag}: (GR-53) failed on {specs}"
        z = feasible_at(specs, n, oidx, p)
        assert z is not None, f"{tag}: (GR-52) failed on {specs}"
        verify_balanced(specs, n, binc, oidx, z)
    print(f"  seeded random cubic bridgeless stress (NO habitat gate, "
          f"2k in {{2, 4, 6}}): {len(rand)}/{len(rand)} balanced by the "
          f"theorem's construction ({conc} placements deliberately "
          f"CONCENTRATED on one hub's neighbourhood)")
    print("  => (GR-54): input (X) is DISCHARGED -- entry 5's balance "
          "half is PROVEN, and (GR-49) makes the parity half fall out "
          "with it (an admissible z IS a parity-consistent map)")
    print(f"  [{time.time() - t0:.1f}s]")
    print()


# --------------------------------------------------- [GBL-6] --adv ----------

def leg_adv():
    """[GBL-6] F13 falsification controls."""
    t0 = time.time()
    print("[GBL-6] falsification controls (F13): each must reject or fire, "
          "each with a negative control")
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    (_nm, n, specs, _f, _S, _e) = by_tag['W3']
    specs = [tuple(s) for s in specs]
    binc = branches_at(specs, n)
    oidx = odd_idx(specs)
    edges, allverts, hm, _i, _t, _tc, _a = prep_shape(specs)
    ground = (edges, allverts, hm)

    z, _p = balance_oracle(specs, n, oidx)
    assert z is not None
    verify_balanced(specs, n, binc, oidx, z, ground)
    rejected = tried = accepted = 0
    by_kind = {'inadmissible': 0, 'unbalanced': 0}
    for i in range(len(specs)):
        zz = list(z)
        zz[i] ^= 1
        tried += 1
        adm = z_admissible(specs, n, binc, zz)
        bal = 2 * sum(zz[j] for j in oidx) == len(oidx)
        truth = adm and bal
        try:
            verify_balanced(specs, n, binc, oidx, zz, ground)
            got = True
        except AssertionError:
            got = False
        assert got == truth, \
            f"verify_balanced disagrees with ground truth on flip {i}"
        if got:
            accepted += 1
        else:
            rejected += 1
            by_kind['inadmissible' if not adm else 'unbalanced'] += 1
    print(f"  (1) single-bit flips of a VERIFIED balanced z at W3: "
          f"{tried} tried, {rejected} REJECTED by verify_balanced "
          f"({by_kind['inadmissible']} because the flip breaks the hub "
          f"guard, {by_kind['unbalanced']} because it unbalances the odd "
          f"pattern) and {accepted} ACCEPTED -- and verify_balanced's "
          f"verdict is asserted EQUAL to the independent ground truth "
          f"(admissible AND half-and-half) at every one of the {tried}. "
          f"Negative control: the undoctored z passes.  Pinned "
          f"counter-fact: a flip on an even branch off every blocked hub "
          f"is a GENUINE second certificate, so a verifier that rejected "
          f"all 15 would be wrong -- rejection must be earned"
          )
    assert rejected > 0 and accepted > 0 and by_kind['inadmissible'] > 0 \
        and by_kind['unbalanced'] > 0, \
        "control (1) degenerate: not all three outcomes realized"

    sp3 = [(0, 1, 3), (0, 1, 3), (0, 1, 3)]
    o3 = odd_idx(sp3)
    _o, _q, _d, lo, hi = bounds_of(sp3, 2, o3, (0, 0, 0))
    assert any(hi[v] < lo[v] for v in range(2)), \
        "control (2) broken: the all-A pattern should be bound-infeasible"
    neg2 = balance_oracle([(0, 1, 3), (0, 1, 3), (0, 1, 2)], 2, [0, 1])
    print(f"  (2) the all-A pattern at an all-odd theta hub is "
          f"BOUND-INFEASIBLE (l_v > u_v), exactly as (GR-50) requires; "
          f"the pattern is not balanced anyway, and the balanced decision "
          f"at theta(3,3,2) succeeds (negative control): "
          f"{neg2[0] is not None}")

    ed = [(0, 1), (0, 1), (0, 1)]
    asg, R = assign_feasible(2, ed, [0, 0], [1, 1])
    assert asg is None and R is not None, "control (3): no certificate"
    eS = sum(1 for (u, w) in ed if u in R and w in R)
    assert eS > len(R), "control (3): the returned set does not violate Hall"
    print(f"  (3) an infeasible degree-constrained instance (3 parallel "
          f"edges, hi = 1 each): assign_feasible returns the VIOLATING "
          f"hub set (|R| = {len(R)}, e(R) = {eS} > sum hi = {len(R)}) -- "
          f"an infeasibility CERTIFICATE, not a silent failure; the same "
          f"instance at hi = 2 succeeds (negative control): "
          f"{assign_feasible(2, ed, [0, 0], [2, 2])[0] is not None}")

    fired = not z_admissible(specs, n, binc, [0] * len(specs))
    assert fired, "control (4): the all-zero z should be inadmissible at W3"
    print(f"  (4) the all-zero z at W3 is INADMISSIBLE ({fired}); "
          f"z_to_map's 2-1-split assert is the guard, and the verified "
          f"certificate is admissible (negative control): "
          f"{z_admissible(specs, n, binc, z)}")

    # (5) the (GR-53) exhaustion must FAIL on a deliberately weakened bar
    bad = None
    for k2 in (4, 6):
        for (pairs, triples) in maximal_structures(k2):
            if all(max(split_cost(p, list(pairs), list(triples))[:2]) > 0
                   for p in balanced_patterns(k2)):
                bad = (k2, pairs, triples)
                break
        if bad:
            break
    print(f"  (5) the (GR-53) bar is TIGHT, not slack: a structure at "
          f"which NO balanced split reaches ZERO monochromatic pairs on "
          f"both sides exists ({bad is not None}) -- "
          f"{('2k=%d pairs=%s triples=%s' % bad) if bad else 'none'}; so "
          f"'<= 1 per side' cannot be strengthened to '0', and (GR-52)'s "
          f"parity argument is doing real work")
    assert bad is not None, "control (5) did not fire: the bar looks slack"

    # (6) E1 clause (v) discriminator: the decision is EXACT, so an
    #     infinity would be reported as an infinity, never as a cap
    sp6 = [(0, 1, 3), (0, 1, 3), (0, 1, 2)]
    o6 = odd_idx(sp6)
    z6, _p6 = balance_oracle(sp6, 2, o6)
    b6 = brute_balance(sp6, 2, branches_at(sp6, 2), o6)
    assert (z6 is not None) == (b6 is not None)
    print(f"  (6) E1(v) discriminator on theta(3,3,2): oracle balanced = "
          f"{z6 is not None}, exhaustive 2^M cube balanced = "
          f"{b6 is not None} -- the two AGREE, so a 'no balanced "
          f"configuration' verdict from this oracle is a GENUINE d_adm = "
          f"oo at full decision, never a cap")
    print(f"  [{time.time() - t0:.1f}s]")
    print()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for f in ('zform', 'oracle', 'two', 'split', 'thm', 'adv'):
        ap.add_argument(f'--{f}', action='store_true')
    ap.add_argument('--validate', action='store_true')
    a = ap.parse_args()
    if a.validate:
        a.zform = a.oracle = a.two = a.split = a.thm = a.adv = True
    if not any((a.zform, a.oracle, a.two, a.split, a.thm, a.adv)):
        ap.print_help()
        return
    print(f"gbal.py -- GBAL, input (X): balance existence "
          f"(base seed {R_SEED})")
    print()
    if a.zform:
        leg_zform()
    if a.oracle:
        leg_oracle()
    if a.two:
        leg_two()
    if a.split:
        leg_split()
    if a.thm:
        leg_thm()
    if a.adv:
        leg_adv()


if __name__ == '__main__':
    main()
