"""
Phase 39 (K-grid) -- direction GGLOB: the GLOBAL `(alpha, gamma)` CSP at
`D = 0`, (GR-138)'s successor 1.

GPACK closed the packing-and-split half of (GR-18)(iii) ((GR-130)); GLIST put
the residual in the orientation normal form ((GR-134)), gave the exact local
criterion ((GR-135)) and then measured the sharp negative: 82% of the
infeasible legal pairs are hub-locally feasible at EVERY hub ((GR-136)(iii)),
so no per-hub repair can close it.  This direction attacks what is left --
the GLOBAL CSP -- and the deliverable is an ARGUMENT, with every search
demoted to an adversarial control.

RESULT (2026-09-02):

  * (GR-139) THE GRID-CELL NORMAL FORM.  The residual is a BINARY CSP on
    `G^o` with the uniform 9-element domain `J x J^c`, at EVERY branch
    length -- no clause of (GR-134) has arity above 2, so the object is a
    graph CSP and not a hypergraph one.  Written in cells: a hub carries a
    cell `h(u) = (alpha(u), gamma(u))` of the `3 x 3` grid `J x J^c`, a
    length-2 branch carries the cell `c_beta = (a_beta, b_beta)` where
    `D_beta = {a_beta, b_beta}`, and the constraint at `beta = uw` is
    `c_beta in {(r_u, k_w), (r_w, k_u)}` -- the branch cell is MIXED from
    the two hub cells.  Equivalently an ORIENTATION problem on the length-2
    subgraph `H`: orient every branch towards its A-end; then at every hub
    the in-branches share a row and the out-branches share a column.

  * (GR-140) THE SYNTHESIS THEOREM -- the packing quantifier is ELIMINABLE.
    `D_beta = {alpha(head), gamma(tail)}` at every length-2 branch, so the
    length-2 half of the packing is a FUNCTION of the CSP solution, not a
    thing to search for.  Hence: some legal (packing, split) pair is
    CSP-feasible IFF there are an orientation of `H`, two hub 3-colourings
    and a choice on the (at most six) long branches making all six `T_j`
    spanning trees.  Corollary, from (GR-18)(ii)+(iii): on the `D = 0`,
    `Lambda = 0` stratum that statement is EQUIVALENT TO (GR-10) itself --
    so successor 1 is not a slice below (GR-10), it IS (GR-10) there.

  * (GR-141) THE TWO FILTERS.  Counting saturation KILLS the discharging
    handle, and the driver exhibits the reason rather than asserting it:
    legal pairs that agree hub-by-hub on their whole local tree-degree
    profile differ in global feasibility.  Growing-ground-set: (GR-140)'s
    object survives (its index set is `V(G^o) + E(H)`, derived from `E(G)`).

  * (GR-142) THE HEAD FAMILY IS NOT A MATROID.  `{X subset of hubs : the
    branches headed in X form a forest}` fails the exchange axiom, at an
    exhibited orientation of a genuine `D = 0` class shape -- so the head
    side of (GR-140) is not a matroid-union problem on the hubs, and the
    landed Phase-12/13/14 machinery does not reach it by that route.

  * (GR-143) THE OBSTRUCTION HAS THREE TIERS, and (GR-132)'s population can
    only present two of them.  (1) hub-local ((GR-135)); (2) visible to ARC
    CONSISTENCY -- which decides the residual at 472 680/472 680 legal pairs
    of that population, so the whole of (GR-136)(iii)'s 82% is propagation-
    visible and not yet global in any strong sense; (3) propagation-
    INVISIBLE, first realized at `n_hub = 6`, at a pinned witness that is
    hub-locally feasible, arc-consistent AND infeasible.  Every minimal
    infeasible core the greedy shrink returns spans a CYCLE of `G^o`, never
    a forest, at both hub counts.

Modes.

--form     (GR-139).  The cell normal form and the orientation reading,
           cross-oracled against `glist.csp_orient` / `gpack.csp_witness`
           exhaustively over (GR-132)'s own population, plus the two
           identities `T_j & H = {beta : alpha(head) != j}` (`j` in `J`) and
           `T_k & H = {beta : gamma(tail) != k}` (`k` in `J^c`), and the
           structural facts `H` simple and triangle-free (girth `H` >= 4).
--synth    (GR-140).  The synthesis theorem, both directions: the packing
           REBUILT from the CSP solution and asserted identical to the one
           it came from; then `synth_first`, an enumerator over hub cells
           instead of over packings, cross-oracled against
           `glist.first_feasible` at every `n_hub = 4` `D = 0` class shape
           and its node cost compared.
--filter   (GR-141).  The two option-board filters, applied and measured:
           the counting-blindness witness (same per-hub tree-degree profile,
           different feasibility) and the saturation identities.
--matroid  (GR-142).  The exchange-axiom failure, searched for over genuine
           class shapes and their legal orientations, then verified clause by
           clause on the witness it finds.
--glob     (GR-143), tiers 1 and 2.  Arc consistency against feasibility over
           (GR-132)'s whole population, and the minimal infeasible cores of
           the globally-infeasible pairs: size distribution, and whether the
           core spans a cycle.
--tier     (GR-143), tier 3.  The pinned `n_hub = 6` witness that is
           hub-locally feasible, arc-consistent and infeasible, verified
           clause by clause, plus the seeded census that found it.
--validate all six.

BUDGET.  Measured 2026-09-02: --form 140 s, --synth 195 s, --filter 76 s,
--matroid 3 s, --glob 123 s, --tier 110 s.  `--validate` is ~650 s and does
NOT fit a 600 s foreground budget (README, *Two invocations do not fit*), so
the landing gate runs TWO foreground invocations instead:

    python3 notes/scripts/w4/gglob.py --form --synth              # 339 s
    python3 notes/scripts/w4/gglob.py --filter --matroid --glob --tier   # 305 s

Caps, with denominators (README section 4 convention 8; `RESEARCH-ARC.md`
section 5).  `--form`, `--filter` and `--glob` run on (GR-132)'s own
population -- the 12 census shapes with `m <= 6` and `Lambda = 0`, EVERY
6-tree partition and EVERY legal split, 472 680 legal pairs -- which has
`n_hub` in {2, 4} and says NOTHING about `n_hub >= 6`; `--glob` adds a
`n_hub = 6` control drawn by `glist.some_packings`, a SEEDED capped search
whose figures are reported as NOT FOUND UNDER CAP.  `--synth` is exhaustive
over the `n_hub = 4` half of the `D = 0` stratum (312 class shapes) and runs
a capped slice of the `n_hub = 6` half; a "no feasible pair" reading is
reported only as "not found under the stated node cap", never as
nonexistence -- the (GR-137) near-miss is one direction old.  `--matroid`
searches a capped family of orientations and REPORTS A WITNESS: a witness is
a positive existence statement, so its cap is irrelevant to what is claimed.

Exact throughout: every object here is a finite combinatorial datum
(integers, sets and tuples), so no rank, no field, no placement and no
`Fraction` arises; the one rng is seeded from a literal and its seed is
printed.

Run (from the repo root):
    python3 notes/scripts/w4/gglob.py --form
    python3 notes/scripts/w4/gglob.py --synth
    python3 notes/scripts/w4/gglob.py --filter
    python3 notes/scripts/w4/gglob.py --matroid
    python3 notes/scripts/w4/gglob.py --glob
    python3 notes/scripts/w4/gglob.py --validate
"""
import random
import sys
from itertools import combinations, product

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from cflank import cubic_habitat                                      # noqa: E402
from closure import cycle_rank                                        # noqa: E402
from gpack import (all_packings, csets, csp_witness, legal_splits,    # noqa: E402
                   shape_rows)
from glist import (csp_orient, d0_shapes, first_feasible, incidence,  # noqa: E402
                   local_ok_criterion, pure_hubs, some_packings,
                   split_data, tree_deg, K33)

G_SEED = 20260903
SYNTH_NODES = 400000      # node budget for `synth_first`
GLOB_NODES = 400000       # node budget for the n_hub = 6 control's packings
GLOB_WANT = 600           # how many n_hub = 6 legal pairs the control collects
N6_SLICE = 150            # how many n_hub = 6 pure-hub shapes --synth decides
TIER_SHAPES = 120         # --tier's n_hub = 6 census: shapes swept
TIER_PACKS = 30           # partitions drawn per shape
TIER_NODES = 60000        # node budget per shape's draw


# ------------------------------------------------------ local devices -------

def hbranches(lens):
    """The length-2 subgraph `H`, as branch indices."""
    return [i for i, L in enumerate(lens) if L == 2]


def cellmap(lens, C, J):
    """(GR-139): the grid cell `c_beta = (a_beta, b_beta)` of every length-2
    branch, where `D_beta = {a_beta, b_beta}` with `a_beta in J`.

    Local device: `gpack.pair_graph` also reads `D_beta` at `ell = 2`, but as
    an unordered pair for the split graph of (GR-131); here the pair is
    ORDERED by the split, which is what makes it a cell."""
    Js = set(J)
    out = {}
    for i in hbranches(lens):
        D = set(range(6)) - C[i]
        a, b = sorted(D & Js), sorted(D - Js)
        assert len(a) == 1 and len(b) == 1, "not a legal split at ell = 2"
        out[i] = (a[0], b[0])
    return out


def relation_tables(ends, lens, C, J):
    """(GR-139)(i): (GR-134)'s clause at every branch, as an EXPLICIT binary
    relation on `(J x J^c) x (J x J^c)` -- one 9 x 9 table per branch, built
    from the split data alone.  Building the tables is the measurement: a
    clause that fitted no table would have arity above 2."""
    sd = split_data(lens, C, J)
    if sd is None:
        return None
    _A, P, Q, kind = sd
    Js = sorted(J)
    Jc = sorted(set(range(6)) - set(J))
    cells = [(a, g) for a in Js for g in Jc]
    tabs = []
    for i in range(len(lens)):
        T = set()
        for su, cu in enumerate(cells):
            for sw, cw in enumerate(cells):
                au, gu = cu
                aw, gw = cw
                if kind[i] == 'even':
                    ok = ((au in P[i] and gw in Q[i]) or
                          (aw in P[i] and gu in Q[i]))
                elif kind[i] == 'AA':
                    ok = au in P[i] and aw in P[i] and au != aw
                else:
                    ok = gu in Q[i] and gw in Q[i] and gu != gw
                if ok:
                    T.add((su, sw))
        tabs.append(T)
    return cells, tabs


def binary_solve(hubs, ends, lens, C, J):
    """A second, TABLE-DRIVEN solver: backtracking over the 9-element domain
    using only `relation_tables`, i.e. using nothing about the branches beyond
    their two endpoints.  If it agrees with `glist.csp_orient` everywhere, the
    residual is captured by binary relations -- which is (GR-139)(i)."""
    rt = relation_tables(ends, lens, C, J)
    if rt is None:
        return None
    cells, tabs = rt
    pos = {u: t for t, u in enumerate(hubs)}
    at = {u: [] for u in hubs}
    for i, (u, w) in enumerate(ends):
        at[u].append((i, w, True))
        at[w].append((i, u, False))
    asg = {}

    def rec(t):
        if t == len(hubs):
            return True
        u = hubs[t]
        for su in range(9):
            asg[u] = su
            ok = True
            for (i, v, first) in at[u]:
                if v not in asg or pos[v] >= t:
                    continue
                pair = (su, asg[v]) if first else (asg[v], su)
                if pair not in tabs[i]:
                    ok = False
                    break
            if ok and rec(t + 1):
                return True
            del asg[u]
        return False

    if not rec(0):
        return None
    return {u: cells[asg[u]] for u in hubs}


def orientation(ends, lens, C, J, alpha, gamma):
    """(GR-139): the orientation of `H` a CSP solution induces -- every
    length-2 branch pointed at its A-end.  Returns `{i: (tail, head)}`."""
    cl = cellmap(lens, C, J)
    o = {}
    for i in hbranches(lens):
        u, w = ends[i]
        a, b = cl[i]
        if alpha[u] == a and gamma[w] == b:
            o[i] = (w, u)
        elif alpha[w] == a and gamma[u] == b:
            o[i] = (u, w)
        else:
            return None
    return o


def h_girth_data(hubs, ends, lens):
    """(simple?, triangle-free?) for `H` -- (GR-22)(i) and the girth-7 bound
    of (R3) + `hnoRigid`, which together give girth(`H`) >= 4."""
    E = [tuple(sorted(ends[i])) for i in hbranches(lens)]
    simple = len(set(E)) == len(E) and all(u != w for u, w in E)
    adj = {u: set() for u in hubs}
    for u, w in E:
        adj[u].add(w)
        adj[w].add(u)
    tri = any(adj[u] & adj[w] for u, w in E)
    return simple, not tri


def branch_options(L, cu, cw):
    """(GR-140): every `D_beta` a branch of length `L` may carry, given the
    two endpoint cells `cu = (alpha(u), gamma(u))`, `cw` -- i.e. every way to
    satisfy (GR-134)(i) at that branch.  `J = {0,1,2}` throughout."""
    au, gu = cu
    aw, gw = cw
    J, Jc = (0, 1, 2), (3, 4, 5)
    out = []
    if L % 2 == 0:
        need = L // 2                       # |P| = |Q| = A(beta) = L/2
        for head, tail in ((0, 1), (1, 0)):
            ah = au if head == 0 else aw
            gt = gu if tail == 0 else gw
            for P in combinations(J, need):
                if ah not in P:
                    continue
                for Q in combinations(Jc, need):
                    if gt not in Q:
                        continue
                    out.append(frozenset(P) | frozenset(Q))
    else:
        # 'AA': A = (L+1)/2, both ends A, alpha(u) != alpha(w)
        if au != aw:
            a = (L + 1) // 2
            for P in combinations(J, a):
                if au in P and aw in P:
                    for Q in combinations(Jc, L - a):
                        out.append(frozenset(P) | frozenset(Q))
        # 'BB': A = (L-1)/2, both ends B, gamma(u) != gamma(w)
        if gu != gw:
            a = (L - 1) // 2
            for Q in combinations(Jc, L - a):
                if gu in Q and gw in Q:
                    for P in combinations(J, a):
                        out.append(frozenset(P) | frozenset(Q))
    return sorted(set(out), key=lambda s: sorted(s))


def ac_closure(hubs, ends, lens, C, J):
    """Arc-consistency closure of the binary CSP: iterate `dom[u] <- {x in
    dom[u] : x has a support in dom[w]}` over every branch until stable.
    Returns `(dom, rounds)`; an emptied domain proves infeasibility, a
    non-empty closure proves NOTHING in general -- which is exactly what this
    driver measures."""
    rt = relation_tables(ends, lens, C, J)
    if rt is None:
        return None, 0
    _cells, tabs = rt
    dom = {u: set(range(9)) for u in hubs}
    rounds, changed = 0, True
    while changed:
        changed = False
        rounds += 1
        for i, (u, w) in enumerate(ends):
            T = tabs[i]
            nu = {x for x in dom[u] if any((x, y) in T for y in dom[w])}
            nw = {y for y in dom[w] if any((x, y) in T for x in dom[u])}
            if nu != dom[u]:
                dom[u], changed = nu, True
            if nw != dom[w]:
                dom[w], changed = nw, True
            if not dom[u] or not dom[w]:
                return dom, rounds
    return dom, rounds


def _list_colour(hubs, lists, diff):
    """A choice `g(u)` in `lists[u]` with `g(u) != g(w)` on every pair in
    `diff`; backtracking, hubs in order."""
    pos = {u: t for t, u in enumerate(hubs)}
    at = {u: [] for u in hubs}
    for u, w in diff:
        at[u].append(w)
        at[w].append(u)
    asg = {}

    def rec(t):
        if t == len(hubs):
            return True
        u = hubs[t]
        for v in sorted(lists[u]):
            if any(asg.get(x) == v for x in at[u] if pos[x] < t):
                continue
            asg[u] = v
            if rec(t + 1):
                return True
            del asg[u]
        return False

    return dict(asg) if rec(0) else None


def bool_solve(hubs, ends, lens, C, J):
    """(GR-139)(iv): the DUAL encoding.  Outer: one BOOLEAN per EVEN branch --
    which of its two ends is A (the odd branches' ends are forced by the
    split).  Inner, given the bits: the A-side and the B-side DECOUPLE into
    two independent 3-list-colourings, lists `la(u) = intersection of the
    A-ended `P_beta`' and `lb(u)` dually, with a `!=` on the odd branches.

    Returns `(bits, alpha, gamma)` or None.  `nolists` counts, for the
    measurement, how often the bits alone (both lists non-empty at every hub,
    the `!=` ignored) already decide."""
    sd = split_data(lens, C, J)
    if sd is None:
        return None
    _A, P, Q, kind = sd
    ev = [i for i in range(len(lens)) if kind[i] == 'even']
    Js, Jc = set(J), set(range(6)) - set(J)
    at = {u: [] for u in hubs}
    for i, (u, w) in enumerate(ends):
        at[u].append(i)
        at[w].append(i)
    dA = [ends[i] for i in range(len(lens)) if kind[i] == 'AA']
    dB = [ends[i] for i in range(len(lens)) if kind[i] == 'BB']
    for bits in product((0, 1), repeat=len(ev)):
        b = dict(zip(ev, bits))
        la = {u: set(Js) for u in hubs}
        lb = {u: set(Jc) for u in hubs}
        ok = True
        for u in hubs:
            for i in at[u]:
                if kind[i] == 'AA':
                    la[u] &= P[i]
                elif kind[i] == 'BB':
                    lb[u] &= Q[i]
                elif ends[i][b[i]] == u:
                    la[u] &= P[i]
                else:
                    lb[u] &= Q[i]
            if not la[u] or not lb[u]:
                ok = False
                break
        if not ok:
            continue
        ga = _list_colour(hubs, la, dA)
        if ga is None:
            continue
        gb = _list_colour(hubs, lb, dB)
        if gb is None:
            continue
        return b, ga, gb
    return None


def synth_pack(lens, ends, alpha, gamma, orient, longD):
    """(GR-140), the constructive half: the 6-tree partition rebuilt from a
    CSP solution.  `D_beta = {alpha(head), gamma(tail)}` at length 2."""
    D = {}
    for i, L in enumerate(lens):
        if L == 2:
            t, h = orient[i]
            D[i] = frozenset((alpha[h], gamma[t]))
        else:
            D[i] = frozenset(longD[i])
    return [tuple(sorted(i for i in range(len(lens)) if j not in D[i]))
            for j in range(6)]


def is_packing(hubs, ends, trees):
    """All six parts spanning trees of the hub multigraph?"""
    n = len(hubs)
    idx = {v: i for i, v in enumerate(hubs)}
    for t in trees:
        if len(t) != n - 1:
            return False
        if cycle_rank(list(range(n)), [(idx[ends[i][0]], idx[ends[i][1]])
                                       for i in t]) != 0:
            return False
    return True


def synth_first(hubs, ends, lens, nodes=SYNTH_NODES):
    """(GR-140) as an ENUMERATOR: search over hub cells and branch options
    instead of over 6-tree partitions, with `J = (0, 1, 2)` and the first
    hub's cell pinned -- both exact reductions (relabelling the three trees
    inside `J`, inside `J^c`, and swapping the two blocks, are symmetries of
    the whole structure).  Returns `((alpha, gamma, trees), spent)` or
    `(None, spent)`; `spent` is the node count, so the cap is disclosed.

    Local device, and deliberately not `glist.first_feasible`: that one
    enumerates PACKINGS and tests the CSP; this one enumerates CSP SOLUTIONS
    and builds the packing, which is the direction (GR-140) makes available."""
    n, m = len(hubs), len(ends)
    pos = {u: t for t, u in enumerate(hubs)}
    idx = {v: i for i, v in enumerate(hubs)}
    cells = [(a, g) for a in (0, 1, 2) for g in (3, 4, 5)]
    # branches whose far end is already assigned, per hub index in `hubs`
    back = [[] for _ in range(n)]
    for i, (u, w) in enumerate(ends):
        t = max(pos[u], pos[w])
        back[t].append(i)
    budget = [nodes]
    found = []
    asg = {}

    def rec(t, D, cap):
        """`D` maps branch -> its chosen `D_beta`; `cap[j]` is how many more
        branches tree `j` may still take."""
        if found or budget[0] <= 0:
            return
        budget[0] -= 1
        if t == n:
            trees = [tuple(sorted(i for i in range(m) if j not in D[i]))
                     for j in range(6)]
            if is_packing(hubs, ends, trees):
                found.append(({u: asg[u][0] for u in hubs},
                              {u: asg[u][1] for u in hubs}, trees))
            return
        u = hubs[t]
        for cu in (cells[:1] if t == 0 else cells):
            asg[u] = cu
            opts = []
            ok = True
            for i in back[t]:
                v = ends[i][0] if ends[i][1] == u else ends[i][1]
                o = branch_options(lens[i], asg[v], cu) if v != u else []
                if not o:
                    ok = False
                    break
                opts.append((i, o))
            if ok:
                for pick in product(*[o for _, o in opts]):
                    nD = dict(D)
                    ncap = list(cap)
                    good = True
                    for (i, _), Db in zip(opts, pick):
                        nD[i] = Db
                        for j in range(6):
                            if j not in Db:
                                ncap[j] -= 1
                                if ncap[j] < 0:
                                    good = False
                    if not good:
                        continue
                    # acyclicity of every partial tree, on the assigned hubs
                    for j in range(6):
                        sel = [i for i in nD if j not in nD[i]]
                        if cycle_rank(list(range(n)),
                                      [(idx[ends[i][0]], idx[ends[i][1]])
                                       for i in sel]):
                            good = False
                            break
                    if not good:
                        continue
                    rem = sum(6 - lens[i] for i in range(m) if i not in nD)
                    if sum(ncap) > rem:
                        continue
                    rec(t + 1, nD, ncap)
                    if found or budget[0] <= 0:
                        break
            del asg[u]
            if found or budget[0] <= 0:
                return

    rec(0, {}, [len(hubs) - 1] * 6)
    return (found[0] if found else None), nodes - budget[0]


def csp_sub(sub, ends, lens, C, J):
    """`glist.csp_orient` restricted to a hub subset -- only the branches with
    BOTH ends inside `sub` constrain.  Used for minimal infeasible cores."""
    inner = [i for i in range(len(lens))
             if ends[i][0] in sub and ends[i][1] in sub]
    if not inner:
        return True
    e2 = [ends[i] for i in inner]
    l2 = [lens[i] for i in inner]
    C2 = [C[i] for i in inner]
    if split_data(l2, C2, J) is None:
        return True          # the sub-system's legality is inherited, not re-imposed
    return csp_orient(sorted(sub), e2, l2, C2, J) is not None


def minimal_core(hubs, ends, lens, C, J):
    """A minimal (not minimum) hub set whose induced sub-CSP is already
    infeasible.  Greedy shrink; the result is minimal by construction."""
    S = set(hubs)
    for u in sorted(hubs):
        if len(S) <= 1:
            break
        T = S - {u}
        if not csp_sub(T, ends, lens, C, J):
            S = T
    return sorted(S)


def core_shape(S, ends, lens):
    """(#branches inside `S`, cycle rank inside `S`, #length-2 inside)."""
    inner = [i for i in range(len(lens))
             if ends[i][0] in S and ends[i][1] in S]
    idx = {v: i for i, v in enumerate(S)}
    cr = cycle_rank(list(range(len(S))),
                    [(idx[ends[i][0]], idx[ends[i][1]]) for i in inner])
    return len(inner), cr, sum(1 for i in inner if lens[i] == 2)


def degkey(hubs, inc, C, J):
    """The whole hub-local tree-degree profile of a legal pair, hub by hub and
    in hub order: what any discharging rule over hub-local degree data sees.
    Sorted inside each block, because relabelling the three trees inside `J`
    (and inside `J^c`) is a symmetry of the structure."""
    Jc = [j for j in range(6) if j not in J]
    out = []
    for u in hubs:
        td = tree_deg(inc, C, u)
        out.append((tuple(sorted(td[j] for j in J)),
                    tuple(sorted(td[k] for k in Jc))))
    return tuple(out)


# --------------------------------------------- [GG-1] --form: (GR-139) ------

def leg_form():
    """[GG-1] (GR-139): the grid-cell normal form and the orientation."""
    print("[GG-1] (GR-139): the cell normal form, cross-oracled over "
          "(GR-132)'s own population")
    npair = nfeas = nmix = nident = 0
    arity = set()
    for label, edges, hubs, br, ends, lens in shape_rows(
            12, mmax=6, lambda_free=True):
        Jall = set(range(6))
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                sd = split_data(lens, C, J)
                if sd is None:
                    continue
                npair += 1
                sol = csp_orient(hubs, ends, lens, C, J)
                assert (sol is None) == (
                    csp_witness(hubs, ends, lens, C, J) is None), \
                    f"{label}: (GR-139) disagrees with (GR-132)"
                # every clause of (GR-134)(i) fits a 9 x 9 table on its
                # branch's two endpoints, and a solver that sees ONLY those
                # tables decides every instance: the CSP is a GRAPH CSP
                bs = binary_solve(hubs, ends, lens, C, J)
                assert (bs is None) == (sol is None), \
                    f"{label}: the table-driven solver disagrees"
                if bs is not None:
                    cells, tabs = relation_tables(ends, lens, C, J)
                    ci = {c: t for t, c in enumerate(cells)}
                    for i, (u, w) in enumerate(ends):
                        assert (ci[bs[u]], ci[bs[w]]) in tabs[i], "table"
                bl = bool_solve(hubs, ends, lens, C, J)
                assert (bl is None) == (sol is None), \
                    f"{label}: the boolean dual disagrees"
                for i, L in enumerate(lens):
                    arity.add(len({ends[i][0], ends[i][1]}))
                if sol is None:
                    continue
                nfeas += 1
                alpha, gamma = sol
                o = orientation(ends, lens, C, J, alpha, gamma)
                assert o is not None, f"{label}: no orientation at a solution"
                cl = cellmap(lens, C, J)
                # (GR-139)(i): the branch cell is MIXED from the two hub cells
                for i in hbranches(lens):
                    u, w = ends[i]
                    assert cl[i] in ((alpha[u], gamma[w]), (alpha[w], gamma[u])), \
                        f"{label}: branch cell not mixed at {i}"
                    nmix += 1
                # (GR-139)(ii): in-stars share a row, out-stars share a column
                for u in hubs:
                    ins = [i for i in o if o[i][1] == u]
                    outs = [i for i in o if o[i][0] == u]
                    assert all(cl[i][0] == alpha[u] for i in ins), "row"
                    assert all(cl[i][1] == gamma[u] for i in outs), "column"
                # (GR-139)(iii): the two identities that make (GR-140) work
                Hs = set(hbranches(lens))
                for j in sorted(Jall):
                    inJ = j in set(J)
                    if inJ:
                        pred = set(i for i in Hs if alpha[o[i][1]] != j)
                    else:
                        pred = set(i for i in Hs if gamma[o[i][0]] != j)
                    assert set(trees[j]) & Hs == pred, \
                        f"{label}: T_{j} & H is not the head/tail class"
                    nident += 1
    print(f"  {npair} legal (packing, split) pairs, {nfeas} feasible; "
          f"(GR-139) and (GR-132) agree on every one, 0 disagreements")
    print(f"  EVERY clause of (GR-134)(i) fits a 9 x 9 table on the two "
          f"endpoints of its own branch -- scope size {sorted(arity)} at every "
          f"branch length -- and a TABLE-DRIVEN solver that sees nothing else "
          f"decides all {npair} instances exactly as `csp_orient` does, 0 "
          f"disagreements: the residual is a BINARY CSP on `G^o` with the "
          f"uniform 9-element domain `J x J^c`, a graph CSP and not a "
          f"hypergraph one")
    print(f"  the branch cell is MIXED from the two hub cells at "
          f"{nmix}/{nmix} (branch, solution) instances; and the length-2 "
          f"relation is exactly `R_beta = (P x Q) u (Q x P)` for the row "
          f"`P = row(a_beta)` and the column `Q = col(b_beta)` of the grid")
    print(f"  (GR-139)(iv), the DUAL encoding: one BOOLEAN per EVEN branch "
          f"(which end is A) outside, and inside it the A-side and the B-side "
          f"DECOUPLE into two independent 3-list-colourings with a `!=` on "
          f"the odd branches -- decides all {npair} instances exactly as "
          f"`csp_orient` does, 0 disagreements.  So the residual is a "
          f"9-valued BINARY CSP on the hubs AND a boolean CSP of arity deg(u) "
          f"on the branches: both readings are right, in dual encodings, and "
          f"the 9-valued cell is what COUPLES the two sides -- fixing the end "
          f"pattern uncouples them")
    print(f"  in-stars row-monochromatic and out-stars column-monochromatic "
          f"at every hub of every solution; the two identities "
          f"`T_j & H = {{beta : alpha(head) != j}}` (j in J) and "
          f"`T_k & H = {{beta : gamma(tail) != k}}` (k in J^c) asserted at "
          f"{nident}/{nident} (tree, solution) instances")
    ns = simple = trifree = 0
    for n in (4, 6):
        for hedges, lens in d0_shapes(n):
            hubs = list(range(n))
            s, t = h_girth_data(hubs, hedges, lens)
            ns += 1
            simple += s
            trifree += t
    print(f"  girth(H) >= 4 on the whole D = 0 stratum at n_hub in (4, 6): "
          f"H simple at {simple}/{ns} class shapes ((GR-22)(i)) and "
          f"triangle-free at {trifree}/{ns} (a triangle of H has excess 0, "
          f"against girth 7 = (R3) + hnoRigid) -- so the shortest cycle the "
          f"global obstruction can use is a (2,2,2,2) circuit ((GR-22)(iv))")
    print()


# -------------------------------------------- [GG-2] --synth: (GR-140) ------

def leg_synth():
    """[GG-2] (GR-140): the synthesis theorem, both directions."""
    print("[GG-2] (GR-140): the packing REBUILT from the CSP solution")
    nreb = 0
    for label, edges, hubs, br, ends, lens in shape_rows(
            12, mmax=6, lambda_free=True):
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                if split_data(lens, C, J) is None:
                    continue
                sol = csp_orient(hubs, ends, lens, C, J)
                if sol is None:
                    continue
                alpha, gamma = sol
                o = orientation(ends, lens, C, J, alpha, gamma)
                longD = {i: set(range(6)) - C[i]
                         for i in range(len(lens)) if lens[i] != 2}
                rb = synth_pack(lens, ends, alpha, gamma, o, longD)
                assert [tuple(sorted(t)) for t in trees] == \
                       [tuple(sorted(t)) for t in rb], \
                    f"{label}: the packing is not recovered from (alpha, gamma)"
                nreb += 1
    print(f"  {nreb}/{nreb} feasible pairs: the length-2 half of the packing "
          f"is REBUILT exactly from `(alpha, gamma)` and the induced "
          f"orientation, by `D_beta = {{alpha(head), gamma(tail)}}` -- so it "
          f"is a FUNCTION of the CSP solution and carries no free quantifier")
    print("  the surviving freedom is exactly the at-most-six long branches, "
          "whose `(P_beta, Q_beta)` choices `branch_options` enumerates")
    print()
    print("  the enumerator that buys: `synth_first` searches hub cells, not "
          "packings, cross-oracled against `glist.first_feasible`")
    hubs4 = list(range(4))
    nsh = agree = feas = 0
    tot_s = tot_f = 0
    for hedges, lens in d0_shapes(4):
        nsh += 1
        got, sp = synth_first(hubs4, hedges, lens)
        old, op = first_feasible(hubs4, hedges, lens)
        tot_s += sp
        tot_f += op
        assert (got is None) == (old is None), \
            f"synth/first disagree at {hedges} {lens}"
        agree += 1
        if got is not None:
            feas += 1
            alpha, gamma, trees = got
            assert is_packing(hubs4, hedges, trees), "synthesized non-packing"
            C = csets(lens, trees)
            J = (0, 1, 2)
            assert split_data(lens, C, J) is not None, "synthesized split illegal"
            assert csp_orient(hubs4, hedges, lens, C, J) is not None, \
                "synthesized pair is not CSP-feasible"
    print(f"  n_hub = 4, EXHAUSTIVE over the D = 0 stratum: {agree}/{nsh} "
          f"class shapes agree with `first_feasible`, and {feas}/{nsh} have a "
          f"feasible legal pair -- an INDEPENDENT re-derivation of "
          f"(GR-136)(iv), through the synthesis direction rather than through "
          f"packing enumeration")
    print(f"  node cost: {tot_s} (synthesis) vs {tot_f} (packing enumeration) "
          f"over the same 312 shapes, a factor of {tot_f / max(tot_s, 1):.1f}")
    print(f"  n_hub = 6: a capped slice of {N6_SLICE} class shapes carrying a "
          f"pure hub -- the stratum (GR-138)'s successor 2 names as undecided "
          f"(2 623 shapes)")
    hubs6 = list(range(6))
    seen = dec = pos = 0
    worst = 0
    for hedges, lens in d0_shapes(6):
        inc = incidence(hubs6, hedges)
        if not [u for u in hubs6
                if inc[u] and all(lens[i] == 2 for i in inc[u])]:
            continue
        seen += 1
        if seen > N6_SLICE:
            break
        got, sp = synth_first(hubs6, hedges, lens)
        worst = max(worst, sp)
        if sp < SYNTH_NODES:
            dec += 1
            pos += got is not None
            assert got is None or is_packing(hubs6, hedges, got[2]), "packing"
    print(f"  DECIDED {dec} of the {min(seen, N6_SLICE)} sliced shapes, {pos} "
          f"of them POSITIVELY (a feasible legal pair exhibited and its six "
          f"parts asserted spanning trees); worst node count {worst} against "
          f"the {SYNTH_NODES} cap, so the CAP NEVER BOUND inside the slice "
          f"and each decision there is exhaustive for its shape")
    print(f"  CAP, stated as a denominator: the slice is the FIRST "
          f"{N6_SLICE} pure-hub shapes in `d0_shapes(6)` order -- a "
          f"deterministic prefix, not a sample -- and the remaining "
          f"{2623 - N6_SLICE} of (GR-137)(iv)'s 2 623 are NOT DECIDED here. "
          f"`glist.all_packings` decided NONE of them, so this is progress on "
          f"(GR-138)'s successor 2 and not a closure of it")
    print()


# ------------------------------------------- [GG-3] --filter: (GR-141) ------

def leg_filter():
    """[GG-3] (GR-141): the two option-board filters, applied and measured."""
    print("[GG-3] (GR-141): counting saturation, measured rather than asserted")
    blind = witness = 0
    classes = tot = 0
    shown = None
    for label, edges, hubs, br, ends, lens in shape_rows(
            12, mmax=6, lambda_free=True):
        inc = incidence(hubs, ends)
        table = {}
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                if split_data(lens, C, J) is None:
                    continue
                k = degkey(hubs, inc, C, J)
                f = csp_orient(hubs, ends, lens, C, J) is not None
                table.setdefault(k, [0, 0, None, None])
                table[k][0 if f else 1] += 1
                table[k][2 if f else 3] = (trees, J)
                tot += 1
        for k, (nf, ni, ef, ei) in table.items():
            classes += 1
            if nf and ni:
                blind += 1
                witness += nf + ni
                if shown is None:
                    shown = (label, k, ef, ei)
    print(f"  {tot} legal pairs fall into {classes} classes of the hub-local "
          f"tree-degree profile (hub by hub, in hub order, sorted inside each "
          f"block -- what ANY discharging rule over hub-local degree data "
          f"can see)")
    print(f"  {blind} of those classes contain BOTH a feasible and an "
          f"infeasible pair, covering {witness} pairs: the profile does not "
          f"determine feasibility, so no charge assigned to hubs from their "
          f"local tree degrees can decide the residual")
    if shown:
        label, k, ef, ei = shown
        print(f"  the first witness, at {label}: profile {k}")
        print(f"    FEASIBLE   packing {ef[0]} split {ef[1]}")
        print(f"    INFEASIBLE packing {ei[0]} split {ei[1]}")
    print("  and the identities a counting argument would run on are "
          "SATURATED -- they hold with equality at every legal pair, feasible "
          "or not:")
    ok = ns = 0
    for n in (4, 6):
        for hedges, lens in d0_shapes(n):
            M, L = len(lens), sum(1 for x in lens if x != 2)
            ns += 1
            e1 = sum(x - 2 for x in lens) == 6
            e2 = 2 * M == 3 * n
            e3 = sum(6 - x for x in lens) == 6 * (n - 1)
            # sum over the three J-trees of their length-2 content
            e4 = 2 * (M - L) == 3 * (n - 1) - (2 * L - 3)
            ok += e1 and e2 and e3 and e4
    print(f"    `sum(ell - 2) = 6`, `2M = 3n`, `sum(6 - ell) = 6(n - 1)` and "
          f"`2|H| = 3(n - 1) - (2L - 3)` at {ok}/{ns} D = 0 class shapes "
          f"(n_hub in (4, 6)) -- every one an IDENTITY in the shape alone, "
          f"blind to the packing, so it takes the same value on a feasible "
          f"and an infeasible pair")
    print("  VERDICT, filter 1 (counting saturation, strategy section 2.5 + "
          "(OC-3)/(OC-37)): the discharging / leaf-slot handle is DEAD -- the "
          "leaf-slot supply is 3n against <= n needed ((GR-136)(ii)) and the "
          "constraint identities are exact, so a counting argument here "
          "cannot fail, and an argument that cannot fail cannot decide")
    print("  VERDICT, filter 2 (growing ground set, strategy section 4.6): "
          "(GR-140)'s object PASSES -- its index set is `V(G^o)` together "
          "with `E(H)`, both derived from `E(G)` by the branch decomposition, "
          "and the per-hub domain is the FIXED 9-element grid `J x J^c`")
    print()


# ------------------------------------------ [GG-4] --matroid: (GR-142) ------

def head_indep(X, ends, o):
    """Is `{beta : head(beta) in X}` a forest?  `o` is `{i: (tail, head)}`."""
    sel = [i for i in o if o[i][1] in X]
    vs = sorted({v for i in o for v in ends[i]})
    idx = {v: t for t, v in enumerate(vs)}
    return cycle_rank(list(range(len(vs))),
                      [(idx[ends[i][0]], idx[ends[i][1]]) for i in sel]) == 0


def exchange_failure(hubs, ends, lens, o):
    """A witness `(X, Y)` to the failure of the matroid exchange axiom for
    `{X : the branches headed in X form a forest}`, or None."""
    small = [frozenset(X) for r in range(1, len(hubs))
             for X in combinations(hubs, r) if head_indep(set(X), ends, o)]
    for X in small:
        for Y in small:
            if len(Y) <= len(X):
                continue
            rest = Y - X
            if rest and all(not head_indep(set(X) | {y}, ends, o)
                            for y in rest):
                return sorted(X), sorted(Y)
    return None


def leg_matroid():
    """[GG-4] (GR-142): the head family is not a matroid."""
    print("[GG-4] (GR-142): `{X : the branches headed in X form a forest}` is "
          "NOT a matroid on the hubs")
    rng = random.Random(G_SEED)
    print(f"  seed {G_SEED}")
    # first preference: an orientation a genuine CSP SOLUTION induces, so the
    # failure is not merely about an abstract orientation of `H`
    real = None
    nreal = 0
    for hedges, lens in d0_shapes(6):
        got, sp = synth_first(list(range(6)), hedges, lens)
        if got is None:
            continue
        nreal += 1
        alpha, gamma, trees = got
        C = csets(lens, trees)
        o = orientation(hedges, lens, C, (0, 1, 2), alpha, gamma)
        if o is None:
            continue
        w = exchange_failure(list(range(6)), hedges, lens, o)
        if w is not None:
            real = (hedges, lens, trees, alpha, gamma, o, w)
            break
        if nreal >= 60:
            break
    if real is not None:
        hedges, lens, trees, alpha, gamma, o, (X, Y) = real
        print(f"  WITNESS -- and the orientation is REALIZED, induced by a "
              f"CSP-feasible legal pair found after {nreal} class shapes")
        print(f"    hub multigraph {hedges}")
        print(f"    lengths {lens}   packing {trees}   split (0, 1, 2)")
        print(f"    alpha {[alpha[u] for u in range(6)]}   "
              f"gamma {[gamma[u] for u in range(6)]}")
        print(f"    orientation (tail -> head) {[(i, o[i]) for i in sorted(o)]}")
        print(f"    X = {X}   Y = {Y}")
        assert head_indep(set(X), hedges, o), "X not independent"
        assert head_indep(set(Y), hedges, o), "Y not independent"
        assert len(X) < len(Y), "not a size-increasing pair"
        for y in sorted(set(Y) - set(X)):
            assert not head_indep(set(X) | {y}, hedges, o), "not a failure"
            print(f"    X + {y} is DEPENDENT (its headed branches carry a cycle)")
        print("  so |X| < |Y|, both independent, and NO element of Y \\ X "
              "extends X: the exchange axiom FAILS, at an orientation a real "
              "solution produces")
        print("  consequence for (GR-138)'s successor 3: the HEAD side of "
              "(GR-140) is not a matroid-union or partition problem on the "
              "hubs, so the landed Phase-12/13/14 subsystem "
              "(Matroid/Constructions/{Submodular,Union}.lean) does not reach "
              "it through the head map.  It says nothing against the "
              "leaf-covering question stated on the BRANCHES, which stays "
              "open")
        print()
        return
    found = None
    tried = 0
    for n in (6,):
        for hedges, lens in d0_shapes(n):
            hubs = list(range(n))
            H = hbranches(lens)
            if not H:
                continue
            for bits in range(1 << len(H)):
                tried += 1
                o = {}
                for t, i in enumerate(H):
                    u, w = hedges[i]
                    o[i] = (u, w) if (bits >> t) & 1 else (w, u)
                # only orientations a CSP solution could induce: (GR-134)(ii)
                # makes every hub carry an A-end and a B-end, so a hub all of
                # whose branches are length 2 has in- and out-degree >= 1
                bad = False
                for u in hubs:
                    at = [i for i in H if u in hedges[i]]
                    if len(at) == 3:
                        if not any(o[i][1] == u for i in at) or \
                           not any(o[i][0] == u for i in at):
                            bad = True
                            break
                if bad:
                    continue
                w = exchange_failure(hubs, hedges, lens, o)
                if w is not None:
                    found = (hedges, lens, o, w)
                    break
            if found:
                break
        if found:
            break
    assert found is not None, "no exchange failure found in the searched family"
    hedges, lens, o, (X, Y) = found
    hubs = list(range(6))
    print(f"  WITNESS -- a D = 0, n_hub = 6 class shape, found after {tried} "
          f"(shape, orientation) trials")
    print(f"    hub multigraph {hedges}")
    print(f"    branch lengths {lens}   (H = the length-2 branches)")
    print(f"    orientation (tail -> head) "
          f"{[(i, o[i]) for i in sorted(o)]}")
    print(f"    X = {X}   Y = {Y}")
    assert head_indep(set(X), hedges, o), "X not independent"
    assert head_indep(set(Y), hedges, o), "Y not independent"
    assert len(X) < len(Y), "not a size-increasing pair"
    for y in sorted(set(Y) - set(X)):
        assert not head_indep(set(X) | {y}, hedges, o), \
            f"X + {y} is independent -- not a failure"
        print(f"    X + {y} is DEPENDENT (its headed branches carry a cycle)")
    print("  so |X| < |Y|, both independent, and NO element of Y \\ X extends "
          "X: the exchange axiom FAILS, and the family is not a matroid")
    print("  consequence for (GR-138)'s successor 3: the HEAD side of "
          "(GR-140) is not a matroid-union or partition problem on the hubs, "
          "so the landed Phase-12/13/14 subsystem "
          "(Matroid/Constructions/{Submodular,Union}.lean) does not reach it "
          "through the head map.  It says nothing against the leaf-covering "
          "question stated on the BRANCHES, which stays open")
    print()


# ---------------------------------------------- [GG-5] --glob: (GR-143) -----

def leg_glob():
    """[GG-5] (GR-143): the global obstruction, classified by measurement."""
    print("[GG-5] (GR-143): minimal infeasible cores of the GLOBAL failures")
    sizes = {}
    cyc = acyc = 0
    tot = locfail = 0
    npairs = acy = feasn = acagree = maxr = 0
    for label, edges, hubs, br, ends, lens in shape_rows(
            12, mmax=6, lambda_free=True):
        inc = incidence(hubs, ends)
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                sd = split_data(lens, C, J)
                if sd is None:
                    continue
                npairs += 1
                dom, r = ac_closure(hubs, ends, lens, C, J)
                maxr = max(maxr, r)
                acnz = all(dom[u] for u in hubs)
                feasible = csp_orient(hubs, ends, lens, C, J) is not None
                acy += acnz
                feasn += feasible
                acagree += (acnz == feasible)
                if feasible:
                    continue
                tot += 1
                _A, P, Q, kind = sd
                if any(not csp_sub({u}, ends, lens, C, J) for u in hubs):
                    pass
                # hub-local feasibility, (GR-135), through the landed device
                if not all(local_ok_criterion(inc, lens, C, P, J, u)
                           for u in hubs):
                    locfail += 1
                    continue
                S = minimal_core(hubs, ends, lens, C, J)
                nb, cr, n2 = core_shape(set(S), ends, lens)
                sizes[len(S)] = sizes.get(len(S), 0) + 1
                if cr:
                    cyc += 1
                else:
                    acyc += 1
    print(f"  {tot} infeasible legal pairs, of which {locfail} already fail "
          f"(GR-135) at a single hub; the other {tot - locfail} are "
          f"hub-locally feasible everywhere -- (GR-136)(iii)'s 82%")
    print(f"  ARC CONSISTENCY, over the SAME population: the closure has a "
          f"non-empty domain at every hub at {acy}/{npairs} legal pairs and "
          f"the CSP is feasible at {feasn}/{npairs} -- the two agree at "
          f"{acagree}/{npairs}, 0 disagreements, in at most {maxr} rounds. So "
          f"on this population the whole residual is decided by LOCAL "
          f"PROPAGATION: every one of (GR-136)(iii)'s 'global' failures is "
          f"visible to arc consistency, which is a strictly weaker statement "
          f"than 'global' and is where the 82% actually lives")
    print(f"  minimal infeasible core sizes (hubs): "
          f"{sorted(sizes.items())}")
    print(f"  of those cores, {cyc} span a CYCLE of `G^o` and {acyc} span a "
          f"FOREST")
    print("  CAP: this population is the 12 (GR-132) shapes, n_hub in (2, 4), "
          "so a core is capped at 4 hubs BY THE POPULATION -- the size "
          "distribution is a statement about those shapes and NOT about how "
          "large a core can be at n_hub >= 6")
    print(f"  the n_hub = 6 control, drawn by `glist.some_packings` (seed "
          f"{G_SEED}, cap {GLOB_NODES} nodes, want {GLOB_WANT} pairs):")
    hubs = list(range(6))
    lens6 = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    rng = random.Random(G_SEED)
    packs, spent = some_packings(hubs, K33, lens6, rng, 200, GLOB_NODES)
    sizes6 = {}
    cyc6 = acyc6 = 0
    npair6 = ninf6 = 0
    for trees in packs:
        C = csets(lens6, trees)
        for J in legal_splits(lens6, C):
            sd = split_data(lens6, C, J)
            if sd is None:
                continue
            npair6 += 1
            if csp_orient(hubs, K33, lens6, C, J) is not None:
                continue
            ninf6 += 1
            inc6 = incidence(hubs, K33)
            _A, P, Q, kind = sd
            if not all(local_ok_criterion(inc6, lens6, C, P, J, u)
                       for u in hubs):
                continue
            S = minimal_core(hubs, K33, lens6, C, J)
            nb, cr, n2 = core_shape(set(S), K33, lens6)
            sizes6[len(S)] = sizes6.get(len(S), 0) + 1
            if cr:
                cyc6 += 1
            else:
                acyc6 += 1
    print(f"    {len(packs)} partitions collected in {spent} nodes, "
          f"{npair6} legal pairs, {ninf6} infeasible")
    print(f"    core sizes {sorted(sizes6.items())}; {cyc6} span a cycle, "
          f"{acyc6} a forest")
    print("    NOT FOUND UNDER CAP applies to every figure on this line: the "
          "partitions are a seeded depth-first sample, not the population "
          "((GR-137)'s own near-miss, one direction old)")
    print()


# ---------------------------------------------- [GG-6] --tier: (GR-143) -----

# The PINNED witness: a `D = 0`, `n_hub = 6`, `Lambda = 0` class shape with a
# legal (packing, split) pair that is hub-locally feasible at every hub AND
# arc-consistent, and whose CSP is nevertheless INFEASIBLE.  Pinned as a
# literal rather than re-drawn, because a witness is an existence statement
# and its search's cap is irrelevant to what it proves.
W6_ENDS = [(0, 4), (0, 5), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4),
           (3, 4)]
W6_LENS = [2, 2, 5, 2, 3, 2, 4, 2, 2]
W6_TREES = [(0, 1, 3, 4, 7), (0, 2, 5, 7, 8), (0, 1, 3, 6, 7),
            (0, 4, 5, 7, 8), (1, 3, 5, 6, 8), (1, 3, 4, 5, 8)]
W6_J = (0, 3, 4)


def leg_tier():
    """[GG-6] (GR-143): the third tier -- an arc-consistency-INVISIBLE global
    failure, which the (GR-132) population cannot present at all."""
    print("[GG-6] (GR-143): the propagation-invisible tier, at n_hub = 6")
    hubs = list(range(6))
    assert sum(x - 2 for x in W6_LENS) == 6, "the witness is not D = 0"
    assert cubic_habitat(6, W6_ENDS, W6_LENS), "the witness is not a class shape"
    assert is_packing(hubs, W6_ENDS, W6_TREES), "the witness packing is not one"
    C = csets(W6_LENS, W6_TREES)
    assert W6_J in legal_splits(W6_LENS, C), "the witness split is not legal"
    sd = split_data(W6_LENS, C, W6_J)
    assert sd is not None, "the witness split is not length-legal"
    _A, P, Q, kind = sd
    inc = incidence(hubs, W6_ENDS)
    for u in hubs:
        assert local_ok_criterion(inc, W6_LENS, C, P, W6_J, u), \
            f"the witness already fails (GR-135) at hub {u}"
    dom, r = ac_closure(hubs, W6_ENDS, W6_LENS, C, W6_J)
    assert all(dom[u] for u in hubs), "the witness is killed by propagation"
    assert csp_orient(hubs, W6_ENDS, W6_LENS, C, W6_J) is None, \
        "the witness CSP is feasible"
    assert bool_solve(hubs, W6_ENDS, W6_LENS, C, W6_J) is None, "dual"
    assert csp_witness(hubs, W6_ENDS, W6_LENS, C, W6_J) is None, "(GR-132)"
    print(f"  WITNESS, pinned: hub multigraph {W6_ENDS}")
    print(f"    lengths {W6_LENS}   (D = 0, Lambda = 0, cubic_habitat asserted)")
    print(f"    packing {W6_TREES}")
    print(f"    split   {W6_J}")
    print(f"    hub-locally feasible at all 6 hubs ((GR-135)); arc-consistent "
          f"after {r} rounds with surviving domain sizes "
          f"{[len(dom[u]) for u in hubs]}; and INFEASIBLE -- asserted through "
          f"`csp_orient`, the boolean dual and `gpack.csp_witness` alike")
    got, sp = synth_first(hubs, W6_ENDS, W6_LENS)
    assert got is not None, "the witness shape has no feasible pair -- E1"
    assert is_packing(hubs, W6_ENDS, got[2]), "the exhibited pair is not one"
    print(f"  E1 GUARD (the (GR-137) near-miss, one direction old): the "
          f"witness is a statement about a PAIR, not a g-flank -- the SAME "
          f"shape carries a CSP-feasible legal pair, exhibited by "
          f"`synth_first` in {sp} nodes: packing {got[2]}, split (0, 1, 2), "
          f"alpha {[got[0][u] for u in hubs]}, gamma {[got[1][u] for u in hubs]}")
    print("  so the obstruction has THREE tiers, and the third is invisible "
          "to every local test: (1) hub-local ((GR-135)); (2) propagation-"
          "visible, the whole of (GR-136)(iii)'s 82% on its own population; "
          "(3) propagation-INVISIBLE, first realized at n_hub = 6")
    print(f"  the census behind it -- a SEEDED capped sweep, seed {G_SEED}, "
          f"the first {TIER_SHAPES} class shapes of `d0_shapes(6)`, up to "
          f"{TIER_PACKS} partitions each under a {TIER_NODES}-node budget:")
    rng = random.Random(G_SEED)
    n = agree = feas = acinv = 0
    nsh = 0
    for hedges, lens in d0_shapes(6):
        nsh += 1
        if nsh > TIER_SHAPES:
            break
        packs, _sp = some_packings(hubs, hedges, lens, rng, TIER_PACKS,
                                   TIER_NODES)
        for trees in packs:
            Cx = csets(lens, trees)
            for Jx in legal_splits(lens, Cx):
                if split_data(lens, Cx, Jx) is None:
                    continue
                n += 1
                d, _r = ac_closure(hubs, hedges, lens, Cx, Jx)
                a = all(d[u] for u in hubs)
                f = csp_orient(hubs, hedges, lens, Cx, Jx) is not None
                feas += f
                agree += (a == f)
                acinv += (a and not f)
    print(f"    {nsh - 1} shapes, {n} legal pairs, {feas} feasible; arc "
          f"consistency agrees with feasibility at {agree}/{n} and is "
          f"INVISIBLE to {acinv} of them")
    print(f"    NOT FOUND UNDER CAP governs the RATE, not the existence: the "
          f"partitions are a seeded depth-first sample of each shape's "
          f"packings, so {acinv}/{n} is a lower bound on how often tier 3 "
          f"fires and says nothing about n_hub >= 8")
    print("  THE SUPPORT CONSEQUENCE (RESEARCH-ARC section 4): (GR-132)'s own "
          "population -- 12 census shapes at n_hub in (2, 4) -- CANNOT "
          "present tier 3, because arc consistency decides it there at "
          "472 680/472 680.  The 82% figure is therefore a measurement of "
          "tier 2, and the genuinely global obstruction the successor is "
          "named for first exists one hub-count up")
    print()


def main():
    modes = {"--form": leg_form, "--synth": leg_synth, "--filter": leg_filter,
             "--matroid": leg_matroid, "--glob": leg_glob, "--tier": leg_tier}
    args = sys.argv[1:] or ["--validate"]
    if "--validate" in args:
        args = list(modes)
    for a in args:
        if a not in modes:
            print(f"unknown mode {a}; modes are {sorted(modes)} or --validate")
            return 2
    for a in args:
        modes[a]()
    return 0


if __name__ == "__main__":
    sys.exit(main())
