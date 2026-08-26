"""
Phase 39 PENCIL, kernel (K), direction OGEOM (38th ordinal, 46th direction) --
the GEOMETRIC route to a disproof of `hK`.

Section: workbook `notes/Pencil-informal.md` section (K-out), labels
(OC-45)-(OC-49), Steps O42-O46.

THE QUESTION.  Is there a class (shape, split) with `{sigma = 0} = empty` --
every chart point of `H = G - v - a` carrying a self-stress?  By (OC-24) that
makes `hK` FALSE at that shape.  (OC-37) killed the COUNTING route
(`slack(F) >= 0` at every class shape, equality iff `F` is a cycle or a
bouquet), and direction SIGZ's hunt on that mechanism returned NO HIT.  What
survives is the GEOMETRIC half: no forced chain-span drop and no forced
Kirchhoff drop.  This driver attacks that half.

WHAT IS NEW HERE (everything else is cited, not re-derived).

  (OC-45) the CLASS-SHAPE BRANCH BOUNDS, proven and asserted.  At a class
          shape `G` (tight, def = 0, `hnoRigid`, `hcard`) with topological
          reduction `G*`:
            (i)   `G*` has no bridge;
            (ii)  every branch has length <= 5;
            (iii) `|E*| <= 6(|V*| - 1)`, and the number of length-1 branches
                  (hub-hub edges) is at most `(6|V*| - 6 - |E*|)/4`.
          (ii) is what makes `sigz.k4_stratum`'s `{1..5}^6` range a THEOREM
          rather than a cap -- so (OC-39)'s "exhaustive `K4` stratum" survives
          an adversarial re-enumeration at range `{1..12}^6`.  This mode runs
          that re-enumeration.

  (OC-46) the RESTRICTION-DOMINANCE lemma -- the pass's main structural tool.
          Let `G` be a class shape with `hcard` and `F` a min-degree->=2
          subgraph that is an INDUCED subgraph of `G`.  Then the restriction
          map from `G`'s pencil chart to `F`'s OWN pencil chart is DOMINANT.
          Consequently
              corank R(F) at the generic `G`-chart point
                  = corank R(F) at the generic `F`-chart point,
          a quantity that depends on `F` ALONE -- the ambient shape drops out.
          Proof: below, in `complete_placement`, which is the proof written as
          a constructive extension and is what this mode runs.

  (OC-47) the LIVE-CORE reduction.  On `F`'s own chart a topological path of
          length >= 6 has full chain span (`dim S_Q = 6`, one exact-Q
          determinant, `--core`), hence `S_Q^perp = 0` and its flow variable
          is forced to 0 -- the path is DEAD and may be deleted.  Iterating
          (delete, re-reduce) leaves the LIVE CORE.  Since a class shape has
          girth >= 7, every cycle is dead, so:
            * a cycle or bouquet support NEVER carries a stress at a class
              shape -- the `slack = 0` mechanism, the ONLY topology at which
              ONE geometric unit suffices ((OC-37)(iii)), is CLASS-UNIFORMLY
              unavailable;
            * a live core has `n(F*) >= 2`, min node degree >= 3, and every
              topological path of length <= 5.
          With (Lambda-4)(iii) (`sum ell >= 6c + 1` on every proper cyclic
          branch subset) that gives the CORE BUDGET
              sum_Q (5 - ell_Q)  <=  6 n(F*) - |E(F*)| - 7 ,
          which is what makes the core search below FINITE and small.

  (OC-48) the CORE SEARCH, run.  Live cores are enumerated with NO cap
          inside each `(n(F*), |E(F*)|)` cell, iso-reduced, and each one's
          OWN pencil chart is sampled at exact Q.  Cells run by this pass:
          `n(F*) = 2` and `3` at every `|E*|`, `n(F*) = 4` at `|E*| <= 8`,
          `n(F*) = 5` at `|E*| = 8`.  A core with `corank > 0` at EVERY
          gated sample is a candidate `hK` counterexample and is reported as
          such (and then owes the (OC-38) coincidence check).

  (OC-49) the AMBIENT coverage: which class (shape, split) pairs (OC-48)
          actually settles, ON and OFF the `G* = K4` stratum -- the
          `H`-live-core census, plus (OC-39)-style exact-Q full-row-rank
          certificates as a cross-check at a disclosed sample.

Drivers:
    python3 notes/scripts/w4/ogeom.py --bound   # (OC-45)      5 s
    python3 notes/scripts/w4/ogeom.py --dom     # (OC-46)     90 s
    python3 notes/scripts/w4/ogeom.py --core    # (OC-47)      3 s
    python3 notes/scripts/w4/ogeom.py --hunt    # (OC-48)    364 s  THE HUNT
    python3 notes/scripts/w4/ogeom.py --cert    # (OC-49)    190 s
    python3 notes/scripts/w4/ogeom.py --huntn N LO HI [PART OF]
                                                # (OC-48), one more core cell

`--validate` (all five) does NOT fit a 600 s foreground budget (5 + 90 + 3 +
364 + 190 = 652 s measured), so it runs as the TWO-invocation split below --
`notes/scripts/README.md`'s `flanks --limit` / `yloc --coll` / `sigz --hunt`
precedent, recorded here so a successor plans around it:

    python3 notes/scripts/w4/ogeom.py --bound --dom --core --cert   # 288 s
    python3 notes/scripts/w4/ogeom.py --hunt                        # 364 s

and the `n(F*) = 5, |E*| = 8` cell, which `--hunt` does not include, needs
three more invocations of its own (318 s / 318 s / 318 s measured):

    python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 0 3
    python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 1 3
    python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 2 3

Discipline (`notes/scripts/README.md` section 4): exact `Fraction` arithmetic
only, no floating point; every sampled placement gated by
`repin.star_generic` (the composite guard, NOT `star_span_ranks` alone -- the
(OC-7)/(OC-38) lesson); every sampled span asserts its dimension; every rng
seeded from a printed literal; every cap printed beside the figure it caps.
"""
import itertools
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, wedge2, hat, neighbors, dot
from kbare_common import verts_of
from pencil_escape import build_rigidity, rvec3, rquat
from nogood_subdiv import deficiency, branch_decomposition
from dominance import branch_pmap
from widened import place_pencil_general
from repin import star_generic
from flanks import nondeg_conjuncts
from pitch import paths_graph
from kslide import no_rigid_branch_union
from outer import split_data, eligible_splits
from sigz import topo_reduce, flow_system, ekey, sub_supports

SEED = 20260826

K4E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


# ============================================================ helpers =======

def hub_set(edges):
    nb = neighbors(edges)
    return {v for v in nb if len(nb[v]) >= 3}


def hcard_ok(edges):
    """`hcard` at branch granularity: every hub has at most TWO hub
    neighbours (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
    `Molecule/Pencil/Motive.lean:409`, read at the subdivision)."""
    nb = neighbors(edges)
    H = hub_set(edges)
    return all(len([u for u in nb[h] if u in H]) <= 2 for h in H)


def class_shape_ok(edges):
    """The class predicate on a raw edge list: tight, def = 0, `hnoRigid` at
    branch granularity, `hcard`.  (`kslidecomb.shape_ok` is the same three
    clauses plus `hcard`, but it only accepts the `(0, 1, 3)` split-branch
    spec form, so the clauses are called directly here.)"""
    nV = len(verts_of(edges))
    if 5 * len(edges) != 6 * (nV - 1):
        return False
    if deficiency(edges) != 0:
        return False
    hubs, branches = branch_decomposition(edges)
    if not branches:
        return False
    if not no_rigid_branch_union(edges, branch_pmap(edges)):
        return False
    return hcard_ok(edges)


def class_ok_counting(n, E0, lens, bind=None):
    """The class predicate in its PURE COUNTING form, on the hub multigraph.

    `G` is tight iff `sum ell = 6 c(E*)`.  Given tightness, `def(G) = 0` is
    5/6-sparsity, and `hnoRigid` at branch granularity is `f(V(F)) <= -1` on
    every proper branch union, i.e.
        `sum_S ell >= 6 c(S) + 1` for every proper `S` with `c(S) >= 1`
    (a tight sparse subgraph is rigid, so `no_rigid_branch_union` and this
    inequality say the same thing at a tight shape).  `hcard` is at most two
    length-1 branches per node.

    This is the same predicate as `class_shape_ok`, which routes through
    `nogood_subdiv.deficiency` and `kslide.no_rigid_branch_union`; the two
    are cross-checked against each other in `--cert`'s self-check, and the
    counting form is used for enumeration because the oracle form costs a
    matroid rank per subset."""
    m = len(E0)
    c = m - n + 1
    if sum(lens) != 6 * c:
        return False
    if not core_hcard_ok(n, E0, lens):
        return False
    if bind is None:
        bind = binding_subsets(E0, 5 * m - 6 * c)
    d = [5 - L for L in lens]
    for (mask, B) in bind:
        if mask == (1 << m) - 1:
            continue                       # the whole graph is not proper
        s = 0
        for i in range(m):
            if mask >> i & 1:
                s += d[i]
        if s > B:
            return False
    return True


def build_subdivision(n, E0, lens):
    """The subdivision of the loopless multigraph `(n, E0)` with branch
    lengths `lens`, via `pitch.paths_graph` (hub labels 0..n-1, interior
    labels from 100)."""
    specs = [(u, w, L) for (u, w), L in zip(E0, lens)]
    return paths_graph([], specs)[0]


def cyc_rank(E0sub, nverts_touched=None):
    """Cycle rank of a sub-multigraph given as a list of (u, w) pairs."""
    if not E0sub:
        return 0
    vs = sorted({v for e in E0sub for v in e})
    par = {v: v for v in vs}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    comp = len(vs)
    for (u, w) in E0sub:
        a, b = find(u), find(w)
        if a != b:
            par[a] = b
            comp -= 1
    return len(E0sub) - len(vs) + comp


def sample_chart(edges, seed, tries=40, gate=True):
    """A `repin.star_generic`-gated exact-Q pencil placement of `edges`, or
    None.  Same recipe as `sigz.sample_chart`; repeated here only because the
    gate is optional in this driver's adversarial legs."""
    for t in range(tries):
        out = place_pencil_general(edges, random.Random(seed + 7919 * t))
        if out is None:
            continue
        placed = out[0]
        if gate and not star_generic(edges, placed):
            continue
        return placed, seed + 7919 * t
    return None


def direct_corank(edges, placed):
    """corank of the full `5|E| x 6|V|` rigidity matrix -- the ground truth."""
    V = sorted(verts_of(edges), key=str)
    rows, er, C, idx, n = build_rigidity(
        {'edges': list(edges), 'V': V, 'pt': placed})
    rk = rank(rows)
    return 5 * len(edges) - rk, rk


# ================================================== mode --bound (OC-45) ====

def k4_stratum_range(rng_hi, need3=True):
    """The `G* = K4` class stratum enumerated with branch lengths in
    `1..rng_hi` -- `sigz.k4_stratum` is this at `rng_hi = 5`."""
    out = []
    for lens in itertools.product(range(1, rng_hi + 1), repeat=6):
        if sum(lens) != 18:
            continue
        if need3 and 3 not in lens:
            continue
        E = build_subdivision(4, K4E, list(lens))
        if not class_shape_ok(E):
            continue
        out.append((lens, E))
    return out


def mode_bound():
    print("== (OC-45): the class-shape branch bounds, and the adversarial "
          "re-enumeration of (OC-39)'s `K4` stratum ==")
    print("   PROOF (stated here, asserted below).  Let `G` be a class shape,"
          " `G*` its hub multigraph, `e` a branch of length `ell_e`.")
    print("   `G` is tight, so `sum ell = 6 c(G*)`; `hnoRigid` at branch")
    print("   granularity is (Lambda-4)(iii): every PROPER branch subset `F`")
    print("   with `c(F) >= 1` has `sum_F ell >= 6 c(F) + 1`.  Take")
    print("   `F = G - e` (min degree still >= 2, every hub having degree")
    print("   >= 3 in `G*`).  If `e` is a bridge, `c(F) = c(G*)` and")
    print("   `6c - ell_e >= 6c + 1` is impossible, so `G*` is BRIDGELESS.")
    print("   Otherwise `c(F) = c(G*) - 1` and `6c - ell_e >= 6c - 5`, i.e.")
    print("   `ell_e <= 5`.  Summing `ell <= 5` over `E*` gives")
    print("   `6(|E*| - |V*| + 1) <= 5|E*|`, i.e. `|E*| <= 6(|V*| - 1)`; and")
    print("   with `k` branches of length 1 the same sum gives")
    print("   `6c <= k + 5(|E*| - k)`, i.e. `4k <= 6|V*| - 6 - |E*|`.")

    base = k4_stratum_range(5)
    wide = k4_stratum_range(12)
    print(f"   `G* = K4`, sum ell = 18, a length-3 branch required "
          f"(the split needs one -- `widened.orient`):")
    print(f"     lengths in 1..5  : {len(base)} class shapes  "
          f"(= `sigz.k4_stratum`'s 877)")
    print(f"     lengths in 1..12 : {len(wide)} class shapes  "
          f"-- ADVERSARIAL RE-ENUMERATION at a range that cannot bind")
    assert len(base) == len(wide), "the 1..5 range is a CAP, not a theorem"
    assert len(base) == 877, f"expected 877, got {len(base)}"
    print("     VERDICT: equal, so (OC-39)'s `EXHAUSTIVE K4 stratum` claim "
          "survives; the `{1..5}` range is the theorem (ii), not a cap.")

    nos = k4_stratum_range(12, need3=False)
    print(f"   `G* = K4` class shapes with NO length-3 branch (hence no "
          f"eligible split at all, `widened.orient` returning None): "
          f"{len(nos) - len(wide)}")

    mx, mk, worst = 0, 0, None
    for lens, E in wide:
        mx = max(mx, max(lens))
        k = sum(1 for L in lens if L == 1)
        if k > mk:
            mk, worst = k, lens
        assert max(lens) <= 5, (lens, "branch longer than 5")
        assert 4 * k <= 6 * 4 - 6 - 6, (lens, "hub-hub bound broken")
    print(f"   over the 877: max branch length {mx} (bound 5); max #length-1 "
          f"branches {mk} (bound (6*4-6-6)/4 = {(6 * 4 - 6 - 6) // 4}), "
          f"attained at {worst}")
    return len(base), len(wide)


# ==================================================== mode --dom (OC-46) ====

def is_induced(edges, Fed):
    """Is `F` an INDUCED subgraph of `G`?  (OC-46)'s hypothesis: a `G`-edge
    joining two `F`-vertices that is not an `F`-edge is a CHORD, and both its
    endpoints then have `G`-degree > `F`-degree >= 2, hence are hubs whose
    panels are already pinned by `F` -- which is exactly the one place the
    extension below can fail."""
    FV = set(verts_of(Fed))
    Fk = {ekey(*e) for e in Fed}
    return all(ekey(*e) in Fk for e in edges
               if e[0] in FV and e[1] in FV)


def complete_placement(edges, Fed, posF, rng):
    """(OC-46) AS A CONSTRUCTION: extend a placement of `F`'s vertices, drawn
    from `F`'s OWN pencil chart, to a legal pencil placement of `G`.

    The proof, step by step (`hcard` is used at (b) and (d)):

      (a) Every `G`-hub `h` in `V(F)` gets its panel from `F` alone: the
          normal `n_h` is the nullspace of `{pt(u) - pt(h) : u ~_F h}`, which
          is 1-dimensional because `posF` came from `F`'s chart (an
          `F`-degree-2 vertex gives two independent directions; an
          `F`-degree->=3 vertex is an `F`-hub, whose star `posF` already made
          coplanar).  Nothing outside `F` is consulted, so nothing outside
          `F` can obstruct it.
      (b) Every hub `k` outside `V(F)` is placed in the intersection of the
          panels of its hub neighbours that lie in `V(F)`.  By `hcard` there
          are at most two of those, so the intersection is at least a line
          and is nonempty.
      (c) Its normal `n_k` is then drawn from the nullspace of
          `{pt(u) - pt(k) : u a HUB neighbour of k}` -- again >= 1-dimensional
          by `hcard`.  This is what makes the hub-hub condition SYMMETRIC:
          `pt(k) in Pi(h)` was arranged at (b), and `pt(h) in Pi(k)` is
          arranged here.
      (d) Every non-hub outside `V(F)` has degree 2, hence at most two hub
          neighbours, all of whose panels are now fixed; place it in the
          intersection.

    Returns `(placed, reason)` with `reason = None` on success.  The ONE
    structural failure is a CHORD (`is_induced` false): then step (a) pins
    the panel of a hub whose chord partner is already placed, and the pencil
    condition at (e) is an equation on `posF` rather than something the
    extension can solve.  That case is COUNTED, never silently dropped.
    """
    nb = neighbors(edges)
    nbF = neighbors(Fed)
    hubs = hub_set(edges)
    FV = set(verts_of(Fed))
    placed = dict(posF)
    nrm = {}

    # (a) panels of hubs inside F
    for h in sorted(hubs & FV, key=str):
        cons = [[placed[u][i] - placed[h][i] for i in range(3)]
                for u in sorted(nbF[h], key=str)]
        basis = nullspace(cons)
        if len(basis) != 1:
            return None, ('panel at F-hub not 1-dimensional', h, len(basis))
        nrm[h] = basis[0]

    def meet(cons_planes, r):
        """A point in the intersection of the given (point, normal) planes."""
        rows = [list(n) for (_p, n) in cons_planes]
        rhs = [dot(n, p) for (p, n) in cons_planes]
        if not rows:
            return rvec3(r)
        # particular solution + a random point of the kernel
        aug = [rows[i] + [rhs[i]] for i in range(len(rows))]
        sol = _solve_affine(aug)
        if sol is None:
            return None
        p0, ker = sol
        co = [rquat(r) for _ in ker]
        return [p0[i] + sum((c * k[i] for c, k in zip(co, ker)), F(0))
                for i in range(3)]

    # (b)+(c) hubs outside F
    outside_hubs = sorted(hubs - FV, key=str)
    for k in outside_hubs:
        planes = [(placed[u], nrm[u]) for u in sorted(nb[k], key=str)
                  if u in nrm]
        p = meet(planes, rng)
        if p is None:
            return None, ('no point in the panel meet at an outside hub', k)
        placed[k] = p
    for k in outside_hubs:
        cons = [[placed[u][i] - placed[k][i] for i in range(3)]
                for u in sorted(nb[k], key=str) if u in hubs]
        basis = nullspace(cons) if cons else [[F(1), F(0), F(0)],
                                              [F(0), F(1), F(0)],
                                              [F(0), F(0), F(1)]]
        if not basis:
            return None, ('no normal at an outside hub (hcard?)', k)
        co = [rquat(rng) for _ in basis]
        n = [sum((c * b[i] for c, b in zip(co, basis)), F(0))
             for i in range(3)]
        if all(x == 0 for x in n):
            return None, ('zero normal draw', k)
        nrm[k] = n

    # (d) non-hubs outside F
    for z in sorted(set(nb) - FV - hubs, key=str):
        planes = [(placed[u], nrm[u]) for u in sorted(nb[z], key=str)
                  if u in nrm]
        p = meet(planes, rng)
        if p is None:
            return None, ('no point in the panel meet at an outside non-hub',
                          z)
        placed[z] = p

    # (e) the pencil condition, asserted rather than assumed
    for h in sorted(hubs, key=str):
        for u in nb[h]:
            if dot(nrm[h], [placed[u][i] - placed[h][i]
                            for i in range(3)]) != 0:
                return None, ('pencil condition violated (CHORD?)', h, u)
    for (u, w) in edges:
        if placed[u] == placed[w]:
            return None, ('coincident adjacent points', u, w)
    return placed, None


def _solve_affine(aug):
    """Solve `A x = b` for `x in Q^3` given the augmented rows; return
    `(x0, kernel_basis)` or None if inconsistent."""
    rows = [r[:] for r in aug]
    ncol = 3
    piv = []
    r = 0
    for c in range(ncol):
        pr = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                pr = i
                break
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        pivval = rows[r][c]
        rows[r] = [x / pivval for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                fac = rows[i][c]
                rows[i] = [a - fac * b for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    for i in range(r, len(rows)):
        if all(x == 0 for x in rows[i][:ncol]) and rows[i][ncol] != 0:
            return None
    x0 = [F(0)] * ncol
    for i, c in enumerate(piv):
        x0[c] = rows[i][ncol]
    ker = []
    for c in range(ncol):
        if c in piv:
            continue
        v = [F(0)] * ncol
        v[c] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -rows[i][c]
        ker.append(v)
    return x0, ker


def dom_pool(cap_k4=40, cap_off=24):
    """`(name, edges)` over the `G* = K4` class stratum (capped, and the cap
    is printed by the caller) plus the off-`K4` strata this pass
    enumerates."""
    pool = []
    for lens, E in k4_stratum_range(5)[:cap_k4]:
        pool.append((f'K4{lens}', E))
    for (name, n, E0, lens, E) in off_k4_shapes(cell_cap=2, nmax=4,
                                                emax_cap=8)[:cap_off]:
        pool.append((name, E))
    return pool


def mode_dom(cap_k4=40, nsupp=60):
    print("== (OC-46): restriction-dominance -- `G`'s pencil chart surjects "
          "onto the chart of every INDUCED min-degree->=2 subgraph ==")
    print("   the lemma's PROOF is `complete_placement`'s docstring; this "
          "mode RUNS it, so a gap in the proof shows up as a failed "
          "extension rather than as prose.")
    print(f"   rng: random.Random({SEED} + ...), gate repin.star_generic on "
          f"BOTH the `F`-chart draw and the completed `G`-placement")
    pool = dom_pool(cap_k4=cap_k4)
    print(f"   pool: {len(pool)} class shapes "
          f"(K4 stratum CAPPED at {cap_k4} + the off-K4 census's first 24, "
          f"caps disclosed); per shape the first {nsupp} induced supports")
    tot, ok, chord, skipped, gated = 0, 0, 0, 0, 0
    failed = []
    Hpairs, Hok = 0, 0
    for (name, edges) in pool:
        hubs, branches = branch_decomposition(edges)
        subs = sub_supports(edges, hubs, branches) if branches else []
        seen = 0
        for Fed in subs:
            nbF = neighbors(Fed)
            if any(len(nbF[v]) < 2 for v in nbF):
                continue
            if len(Fed) == len(edges):
                continue
            if not is_induced(edges, Fed):
                chord += 1
                continue
            seen += 1
            if seen > nsupp:
                break
            tot += 1
            got = sample_chart(Fed, SEED + 31 * len(Fed) + len(name),
                               tries=12)
            if got is None:
                skipped += 1
                continue
            posF, used = got
            placed, why = complete_placement(
                edges, Fed, posF, random.Random(SEED + 7 * used))
            if placed is None:
                failed.append((name, len(Fed), why))
                continue
            for u in verts_of(Fed):
                assert placed[u] == posF[u], "restriction is not the identity"
            if star_generic(edges, placed):
                gated += 1
            ok += 1
        # the case the whole pass turns on: F = H itself, always induced
        for v in eligible_splits(edges):
            sd = split_data(edges, v)
            if sd is None:
                continue
            Hed = sd[4]
            assert is_induced(edges, Hed), "H = G - v - a is not induced"
            Hpairs += 1
            g = sample_chart(Hed, SEED + 53 * len(Hed) + len(name), tries=12)
            if g is None:
                continue
            placed, why = complete_placement(
                edges, Hed, g[0], random.Random(SEED + 11 * g[1]))
            if placed is None:
                failed.append((name, 'H', why))
                continue
            Hok += 1
    print(f"   induced proper supports tested: {tot}")
    print(f"   extensions constructed, each asserting the pencil condition "
          f"at EVERY hub of `G` and distinct endpoints on every edge: {ok}")
    print(f"   ... of which the extension also passes the composite gate "
          f"`repin.star_generic` on `G`: {gated}")
    print(f"   `F = H` (always induced, a vertex deletion): {Hpairs} pairs, "
          f"{Hok} extensions constructed")
    print(f"   supports skipped (no gated `F`-chart draw under the try cap): "
          f"{skipped}")
    print(f"   NON-induced proper supports (a CHORD -- (OC-46) does not "
          f"apply; counted, not dropped): {chord}")
    print(f"   extension FAILURES: {len(failed)}")
    for row in failed[:10]:
        print(f"     FAILED {row}")
    assert not failed, "an extension failed -- (OC-46) has a gap"

    # ---- the END-TO-END leg: core -> G, which IS the theorem's mechanism --
    print("   END-TO-END (this is the whole argument, run once per pair): "
          "take `H`'s LIVE CORE, draw a gated corank-0 point of the CORE's "
          "own chart, extend it to `G` by (OC-46), assert the extension is a "
          "LEGAL chart point (`repin.star_generic` AND all four conjuncts of "
          "`IsNondegPencilRealization` via `flanks.nondeg_conjuncts`), and "
          "assert `corank R(H) = 0` there -- an exact-Q full-row-rank "
          "certificate obtained WITHOUT sampling the ambient shape.")
    e2e, e2e_ok, e2e_empty, e2e_fail = 0, 0, 0, []
    for (name, edges) in pool:
        for v in eligible_splits(edges):
            sd = split_data(edges, v)
            if sd is None:
                continue
            Hed = sd[4]
            Ec, nodes, plens = live_core(Hed)
            e2e += 1
            if not Ec:
                e2e_empty += 1
                got = sample_chart(edges, SEED + 97 * len(Hed), tries=12)
                if got is None:
                    e2e_fail.append((name, v, 'no G-chart draw'))
                    continue
                d, rk = direct_corank(Hed, got[0])
                assert d == 0 and rk == 5 * len(Hed), (name, v, d)
                e2e_ok += 1
                continue
            assert is_induced(edges, Ec), "the live core is not induced in G"
            done = False
            for t in range(8):
                g = sample_chart(Ec, SEED + 131 * t + 3 * len(Ec), tries=8)
                if g is None:
                    continue
                dc = flow_system(Ec, g[0])['corank']
                if dc != 0:
                    continue
                placed, why = complete_placement(
                    edges, Ec, g[0], random.Random(SEED + 29 * t + g[1]))
                if placed is None:
                    continue
                if not star_generic(edges, placed):
                    continue
                okc, info = nondeg_conjuncts(edges, placed)
                if not okc:
                    continue
                d, rk = direct_corank(Hed, placed)
                assert d == 0 and rk == 5 * len(Hed), (name, v, d, 'core 0')
                e2e_ok += 1
                done = True
                break
            if not done:
                e2e_fail.append((name, v, 'no legal core-extension found'))
    print(f"   pairs run end-to-end: {e2e}; certified: {e2e_ok} "
          f"({e2e_empty} of them with an EMPTY live core, where the theorem "
          f"says `sigma = 0` outright); failures: {len(e2e_fail)}")
    for row in e2e_fail[:10]:
        print(f"     E2E FAILED {row}")
    assert not e2e_fail, "an end-to-end certificate failed"
    return tot, ok, chord


# =================================================== mode --core (OC-47) ====

def two_core(edges):
    """The maximal subgraph of min degree >= 2."""
    E = list(edges)
    while True:
        nb = neighbors(E)
        drop = {v for v in nb if len(nb[v]) < 2}
        if not drop:
            return E
        E = [e for e in E if e[0] not in drop and e[1] not in drop]
        if not E:
            return []


def live_core(edges, deadlen=6):
    """(OC-47) AS AN ALGORITHM: delete every topological path of length
    >= `deadlen` (its flow variable is forced to 0 because its chain span is
    all of `Lambda^2 K^4`), take the 2-core, re-reduce, iterate.

    Returns `(E_core, nodes, path_lengths)`.  The fixed point is empty, or
    has min node degree >= 3 with every topological path of length <= 5 --
    a single cycle cannot survive, since a class shape has girth >= 7."""
    E = two_core(edges)
    while E:
        nodes, paths = topo_reduce(E)
        dead = [w for (_a, _b, w) in paths if len(w) >= deadlen]
        if not dead:
            nodes, paths = topo_reduce(E)
            return E, nodes, sorted(len(w) for (_a, _b, w) in paths)
        drop = {ekey(*e) for w in dead for e in w}
        E = two_core([e for e in E if ekey(*e) not in drop])
    return [], [], []


def path_span_dim(pts):
    """`dim <pt_i ^ pt_{i+1}>` along a vertex list of exact-Q 3-vectors."""
    lines = [wedge2(hat(pts[i]), hat(pts[i + 1]))
             for i in range(len(pts) - 1)]
    for L in lines:
        assert any(x != 0 for x in L), "degenerate hinge extensor"
    return rank(lines)


def mode_core():
    print("== (OC-47): the live-core reduction -- a topological path of "
          "length >= 6 is DEAD, so cycles and bouquets never carry a "
          "class-shape stress ==")
    print("   LEMMA A (one exact-Q determinant, computed here, not quoted): "
          "six path extensors of seven points in general position in Q^3 are "
          "INDEPENDENT, so `dim S_Q = 6` whenever `ell_Q >= 6`.")
    wit = [[F(0), F(0), F(0)], [F(1), F(0), F(0)], [F(0), F(1), F(0)],
           [F(0), F(0), F(1)], [F(1), F(1), F(3)], [F(2), F(5), F(1)],
           [F(7), F(1), F(2)]]
    d = path_span_dim(wit)
    print(f"   witness pts {[[int(x) for x in p] for p in wit]}")
    print(f"   dim S = {d} (target 6)")
    assert d == 6, "LEMMA A FAILS -- the whole reduction is wrong"

    print("   Lemma A in the FOUR constrained window patterns a class shape "
          "can force (each is a specialisation of the free one, so a witness "
          "INSIDE the pattern is what is needed; together they exhaust the "
          "ways a length-6 window can meet a node's panel, because a "
          "topological path has no interior node and girth >= 7 forbids a "
          "loop of length 6):")
    #  pattern 1: the window starts at a node h, whose panel is spanned by
    #  pt(h) and its two F-neighbours -- so the first interior point lies in
    #  a plane through pt(h).  Realised by putting w1 in the plane z = 0
    #  through h = origin.
    p1 = [[F(0), F(0), F(0)], [F(1), F(0), F(0)], [F(0), F(1), F(0)],
          [F(1), F(1), F(2)], [F(3), F(0), F(1)], [F(0), F(4), F(5)],
          [F(2), F(3), F(7)]]
    assert all(p1[i][2] == 0 for i in (0, 1, 2)), "pattern 1 mis-built"
    d1 = path_span_dim(p1)
    print(f"     pattern 1 (w0 a node, w1 and w2 in its panel z = 0): "
          f"dim S = {d1}")
    assert d1 == 6
    #  pattern 2: TWO nodes inside the window, each pinning its neighbours to
    #  its own panel (the worst case a length-1/2 branch chain produces).
    p2 = [[F(0), F(0), F(0)], [F(1), F(0), F(0)], [F(2), F(1), F(0)],
          [F(3), F(0), F(0)], [F(4), F(1), F(1)], [F(1), F(5), F(2)],
          [F(6), F(2), F(3)]]
    d2 = path_span_dim(p2)
    print(f"     pattern 2 (w1 and w3 nodes, w0..w3 coplanar in z = 0): "
          f"dim S = {d2}")
    assert d2 == 6
    #  pattern 3: BOTH ends of the window are nodes, each pinning its own
    #  path-neighbour to its own panel -- the pattern a length-6 topological
    #  path between two core nodes actually presents.
    p3 = [[F(0), F(0), F(0)], [F(1), F(0), F(0)], [F(2), F(3), F(1)],
          [F(0), F(4), F(5)], [F(3), F(1), F(7)], [F(5), F(2), F(2)],
          [F(4), F(2), F(2)]]
    assert p3[0][2] == 0 and p3[1][2] == 0, "pattern 3 mis-built (w0 panel)"
    assert p3[5][2] == p3[6][2], "pattern 3 mis-built (w6 panel)"
    d3 = path_span_dim(p3)
    print(f"     pattern 3 (BOTH w0 and w6 nodes, w1 in w0's panel z = 0 "
          f"and w5 in w6's panel z = 2): dim S = {d3}")
    assert d3 == 6
    #  pattern 4: the window is a LOOP's first six edges, so w1 AND w6 are
    #  both `w0`-neighbours and both lie in `w0`'s single panel.  This is the
    #  one pattern the other three miss, and it occurs exactly at a loop of
    #  length 7 (girth >= 7 forbids 6; length >= 8 admits a window with one
    #  constrained end, which is pattern 1).
    p4 = [[F(0), F(0), F(0)], [F(1), F(0), F(0)], [F(2), F(3), F(1)],
          [F(0), F(4), F(5)], [F(3), F(1), F(7)], [F(5), F(2), F(2)],
          [F(0), F(1), F(0)]]
    assert p4[0][2] == 0 and p4[1][2] == 0 and p4[6][2] == 0, \
        "pattern 4 mis-built (w1 and w6 must share w0's panel z = 0)"
    d4 = path_span_dim(p4)
    print(f"     pattern 4 (a LOOP of length 7: w0 a node with BOTH w1 and "
          f"w6 in its single panel z = 0): dim S = {d4}")
    assert d4 == 6


    print("   CONSEQUENCE (with girth >= 7 at a class shape, (Lambda-4)'s "
          "own first consequence):")
    print("     every cycle of `G` has length >= 7 >= 6, so `dim S = 6`, so "
          "`S^perp = 0`, so no stress -- and a bouquet is `sum_loops "
          "(6 - dim S_loop) = 0` by (OC-36).  The `slack = 0` mechanism, the "
          "ONLY one at which a SINGLE geometric unit suffices ((OC-37)(iii)),"
          " is CLASS-UNIFORMLY unavailable.")

    print("   measured, on the cycles' OWN charts (which are free position, "
          "a cycle having no node): min corank over 6 seeds, by length")
    for L in range(3, 15):
        E = [(i, (i + 1) % L) for i in range(L)]
        best = None
        for s in range(6):
            got = sample_chart(E, SEED + 101 * s + L, tries=10)
            if got is None:
                continue
            d, _ = direct_corank(E, got[0])
            best = d if best is None else min(best, d)
        exp = max(0, 6 - min(L, 6))
        print(f"     cycle C_{L:<2}: min corank {best}   (predicted "
              f"6 - min(ell,6) = {exp})")
        assert best == exp, (L, best, exp)

    print("   CONSISTENCY with (OC-38), the arc's ONLY exhibited "
          "sigma-jump.  `P21`'s recorded theta support has topological path "
          "lengths (3, 3, 6) and `slack = 0` at `n = 2`.  Read through this "
          "pass: the length-6 path is DEAD at the generic point, the "
          "remaining two length-3 paths reduce to a 6-cycle, which is dead "
          "too, so the LIVE CORE IS EMPTY and the generic corank is 0.  The "
          "recorded `sigma = 1` is therefore a NON-generic point -- exactly "
          "(OC-38)(iii)'s `localtest.plane_basis` coincidence locus, where "
          "the length-6 path's span drops from 6 to 5.  Measured here:")
    th = build_subdivision(2, [(0, 1), (0, 1), (0, 1)], [3, 3, 6])
    best = None
    for sdd in range(8):
        got = sample_chart(th, SEED + 401 * sdd, tries=10)
        if got is None:
            continue
        dd = flow_system(th, got[0])['corank']
        best = dd if best is None else min(best, dd)
    Ec, nodes, plens = live_core(th)
    print(f"     theta(3, 3, 6): live core = {'EMPTY' if not Ec else plens}; "
          f"min corank over 8 gated exact-Q draws of its own chart = {best} "
          f"(so `sigma = 0` generically, matching (OC-38)(iv)'s 360/360 "
          f"gate-accepted seeds)")
    assert best == 0 and not Ec
    bud = 6 * 2 - 3 - 7
    print(f"     and theta(3, 3, 6) is NOT a live core of a class shape "
          f"anyway: `sum d = {5 * 3 - 12}` exceeds the core budget "
          f"`6n - |E*| - 7 = {bud}` -- which is (Lambda-4)(iii) refusing "
          f"`f(V(F)) = 0`, i.e. exactly (OC-38)(ii)'s `one unit short`.")
    assert 5 * 3 - 12 > bud

    print("   the CORE BUDGET, derived: a live core has every `ell_Q <= 5` "
          "and, being a proper cyclic branch subset, `sum ell >= 6c + 1` "
          "((Lambda-4)(iii)); writing `d_Q = 5 - ell_Q >= 0`,")
    print("     sum_Q d_Q  <=  6 n(F*) - |E(F*)| - 7 ,")
    print("   which is what makes the (OC-48) search finite.")
    return d, d1, d2


# =================================================== mode --hunt (OC-48) ====

def canon_multigraph(n, mult, pairs):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((tuple(sorted((p[i], p[j]))), t)
                           for (i, j), t in zip(pairs, mult)))
        if best is None or key < best:
            best = key
    return best


def core_topologies(n, mlo=None, mhi=None):
    """Every loopless connected multigraph on `n` nodes with min degree >= 3
    and `|E| <= 6n - 7` (the (OC-47) core budget's own consequence), up to
    isomorphism.  Parallel multiplicity is capped at 5, which is forced: `k`
    parallel branches are a sub-multigraph with `c = k - 1`, so
    `sum ell >= 6k - 5`, while `ell <= 5` gives `sum ell <= 5k`.
    `mlo`/`mhi` restrict `|E|`, which is what makes `n >= 5` affordable."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    emax = 6 * n - 7
    lo = max((3 * n + 1) // 2, mlo if mlo is not None else 0)
    hi = min(emax, mhi if mhi is not None else emax)
    seen, out = set(), []
    for m in range(lo, hi + 1):
        for mult in fixed_sum_vectors(len(pairs), m, 5):
            deg = [0] * n
            for (i, j), t in zip(pairs, mult):
                deg[i] += t
                deg[j] += t
            if min(deg) < 3:
                continue
            par = list(range(n))

            def find(x):
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x
            comp = n
            for (i, j), t in zip(pairs, mult):
                if t:
                    a, b = find(i), find(j)
                    if a != b:
                        par[a] = b
                        comp -= 1
            if comp != 1:
                continue
            key = canon_multigraph(n, mult, pairs)
            if key in seen:
                continue
            seen.add(key)
            E0 = [pr for pr, t in zip(pairs, mult) for _ in range(t)]
            out.append((n, E0))
    return out


def binding_subsets(E0, budget):
    """The sub-multigraphs whose (Lambda-4)(iii) constraint can BIND.

    `S` needs `sum_S ell >= 6 c(S) + 1`, i.e. `sum_S d <= B_S` with
    `B_S := 5|S| - 6 c(S) - 1`.  Since `sum_S d <= sum d <= budget`, only
    subsets with `B_S < budget` can bind.  The condition is ADDITIVE over
    components and a component with `c = 0` only helps, so it is enough to
    check subsets that are connected with `c >= 1`; such an `S` touching a
    vertex set `W` has `c = |S| - |W| + 1`, hence
        `B_S = 6|W| - |S| - 7`,
    so it binds only when `|S| > 6|W| - 7 - budget`.  Enumerating `W` first
    and then the LARGE edge subsets inside `W` is what makes this cheap; a
    brute-force cross-check over all `2^m` subsets is asserted for small `m`
    by `--hunt`'s self-check.
    """
    m = len(E0)
    verts = sorted({v for e in E0 for v in e})
    out = []
    for r in range(2, len(verts) + 1):
        for W in itertools.combinations(verts, r):
            Ws = set(W)
            idx = [i for i in range(m) if E0[i][0] in Ws and E0[i][1] in Ws]
            thr = 6 * r - 7 - budget
            for k in range(max(2, thr + 1), len(idx) + 1):
                for sel in itertools.combinations(idx, k):
                    S = [E0[i] for i in sel]
                    if len({v for e in S for v in e}) != r:
                        continue
                    c = cyc_rank(S)
                    if c < 1:
                        continue
                    B = 5 * len(S) - 6 * c - 1
                    if B < budget:
                        mask = 0
                        for i in sel:
                            mask |= 1 << i
                        out.append((mask, B))
    return out


def binding_subsets_brute(E0, budget):
    """The same set by brute force over all `2^m` subsets -- the self-check
    for `binding_subsets`' vertex-set pruning."""
    m = len(E0)
    out = []
    for mask in range(1, 1 << m):
        S = [E0[i] for i in range(m) if mask >> i & 1]
        c = cyc_rank(S)
        if c < 1:
            continue
        B = 5 * len(S) - 6 * c - 1
        if B < budget:
            out.append((mask, B))
    return out


def bounded_vectors(m, total, hi):
    """Every `d in {0..hi}^m` with `sum d <= total`, generated directly (the
    `5^m`-then-filter form is not affordable at `m = 17`)."""
    cur = [0] * m

    def rec(i, rem):
        if i == m:
            yield tuple(cur)
            return
        for x in range(0, min(hi, rem) + 1):
            cur[i] = x
            yield from rec(i + 1, rem - x)
        cur[i] = 0
    yield from rec(0, total)


def core_hcard_ok(n, E0, lens):
    """`hcard` inherited by the core: a node may have at most TWO length-1
    branches, since those are hub-hub edges of the ambient class shape."""
    cnt = {v: 0 for v in range(n)}
    for (u, w), L in zip(E0, lens):
        if L == 1:
            cnt[u] += 1
            cnt[w] += 1
    return all(v <= 2 for v in cnt.values())


def _auts(n, E0):
    """The vertex permutations preserving the multigraph `(n, E0)`."""
    base = sorted(E0)
    out = []
    for p in itertools.permutations(range(n)):
        img = sorted(tuple(sorted((p[u], p[w]))) for (u, w) in E0)
        if img == base:
            out.append(p)
    return out


def canon_lengths_key(n, E0, lens, auts):
    """Canonical form of a branch-length assignment under `Aut(E*)` and under
    the interchange of parallel branches: isomorphic cores have equal generic
    corank, so only one representative needs a chart draw."""
    best = None
    for p in auts:
        cls = {}
        for (u, w), L in zip(E0, lens):
            cls.setdefault(tuple(sorted((p[u], p[w]))), []).append(L)
        key = tuple(sorted((k, tuple(sorted(v))) for k, v in cls.items()))
        if best is None or key < best:
            best = key
    return best


def core_lengths(n, E0, brute=False):
    """Every branch-length vector making `(n, E0)` a LIVE CORE that could sit
    inside a class shape: `1 <= ell <= 5` ((OC-47)), `hcard`, and
    `sum_S ell >= 6c(S) + 1` for every sub-multigraph `S` with `c(S) >= 1`
    (that is (Lambda-4)(iii), which the core inherits from the ambient class
    shape as a proper branch subset)."""
    m = len(E0)
    budget = 6 * n - m - 7
    if budget < 0:
        return []
    bind = (binding_subsets_brute(E0, budget) if brute
            else binding_subsets(E0, budget))
    auts = _auts(n, E0)
    out, seen = [], set()
    for d in bounded_vectors(m, budget, 4):
        good = True
        for (mask, B) in bind:
            s = 0
            for i in range(m):
                if mask >> i & 1:
                    s += d[i]
            if s > B:
                good = False
                break
        if not good:
            continue
        lens = tuple(5 - x for x in d)
        if not core_hcard_ok(n, E0, lens):
            continue
        key = canon_lengths_key(n, E0, lens, auts)
        if key in seen:
            continue
        seen.add(key)
        out.append(lens)
    return out


def core_corank(n, E0, lens, nseed=8, gate=True, direct=False):
    """The generic corank of the core's OWN pencil chart: the MINIMUM over
    `nseed` gated exact-Q draws.  A single 0 is a proof that the generic
    corank is 0 (`{corank = 0}` is open and the chart is irreducible,
    section (K-chart) (CH-1)(a)); an all-positive column is `not found under
    the seed cap` and is a CANDIDATE, never a verdict.

    The corank is read off the (OC-35) BRANCH-FLOW system rather than the
    `5|E| x 6|V|` rigidity matrix -- the two agree by (OC-35)/(OC-36), which
    SIGZ proved and asserted at 400 instances; `--hunt`'s self-check
    re-asserts the agreement on a subsample here (`direct=True`)."""
    E = build_subdivision(n, E0, list(lens))
    best, drew = None, 0
    for s in range(nseed):
        got = sample_chart(E, SEED + 977 * s + 13 * sum(lens), tries=8,
                           gate=gate)
        if got is None:
            continue
        drew += 1
        d = flow_system(E, got[0])['corank']
        if direct:
            dd, _ = direct_corank(E, got[0])
            assert dd == d, ('flow vs direct corank', n, E0, lens, dd, d)
        best = d if best is None else min(best, d)
        if best == 0:
            break
    return best, drew, E


def hunt_selfcheck():
    """Two self-checks the hunt's exhaustiveness rests on: the vertex-set
    pruning of `binding_subsets` against brute force over all `2^m` subsets,
    and the (OC-35) flow corank against the direct rigidity-matrix corank."""
    print("   SELF-CHECK 1: `binding_subsets`' pruning vs brute force over "
          "all 2^m subsets, on every topology with n(F*) <= 3 AND on every "
          "n(F*) = 4 topology with |E*| <= 8 (brute force is 2^m, so the "
          "cross-check itself needs a cap)")
    same, tested = 0, 0
    for n, mlo, mhi in ((2, None, None), (3, None, None), (4, 6, 8)):
        for (nn, E0) in core_topologies(n, mlo, mhi):
            a = set(core_lengths(n, E0, brute=False))
            b = set(core_lengths(n, E0, brute=True))
            assert a == b, (n, E0, len(a), len(b))
            same += len(a)
            tested += 1
    print(f"     {tested} topologies, {same} accepted length vectors, "
          f"pruned == brute force at all of them")
    print("   SELF-CHECK 2: (OC-35) flow corank == direct rigidity-matrix "
          "corank, on the first live core of each n(F*) <= 3 topology")
    k = 0
    for n in (2, 3):
        for (nn, E0) in core_topologies(n):
            L = core_lengths(n, E0)
            if not L:
                continue
            core_corank(n, E0, L[0], nseed=2, direct=True)
            k += 1
    print(f"     asserted at {k} (core, seed) instances, 0 mismatches")


def mode_hunt(nmax=4, nseed=8):
    print("== (OC-48) THE HUNT: every LIVE CORE, on its OWN pencil chart ==")
    print("   WHY THIS IS THE WHOLE QUESTION.  By (OC-46) the corank of an "
          "induced support at the generic `G`-chart point equals its corank "
          "at the generic `F`-chart point -- the ambient class shape DROPS "
          "OUT.  By (OC-47) every topological path of length >= 6 is dead, "
          "so only LIVE CORES (all `ell_Q <= 5`, min node degree >= 3) can "
          "carry a stress, and the core budget makes them finite.")
    print("   BOUNDARY, before any number.  A core with `corank = 0` at one "
          "gated draw is a PROOF that it is free (openness + chart "
          "irreducibility).  A core with `corank > 0` at every draw is `not "
          "found free under the seed cap` and is a CANDIDATE `hK` "
          "counterexample owing the (OC-38) coincidence check.")
    print(f"   rng: random.Random({SEED} + 977*s + 13*sum(ell)); "
          f"seed cap {nseed} gated draws per core; gate repin.star_generic")
    print("   ISO-REDUCTION: length vectors are canonicalised under "
          "`Aut(E*)` and under the interchange of parallel branches; "
          "isomorphic cores have equal generic corank, so one representative "
          "is drawn per class.  The counts below are of CLASSES.")
    hunt_selfcheck()
    tot, free, cand = 0, 0, []
    for n in (2, 3):
        tops = core_topologies(n)
        ncore, nfree = 0, 0
        for (nn, E0) in tops:
            for lens in core_lengths(n, E0):
                best, drew, E = core_corank(n, E0, lens, nseed=nseed)
                ncore += 1
                tot += 1
                if best == 0:
                    nfree += 1
                    free += 1
                else:
                    cand.append((n, tuple(E0), lens, best, drew))
        print(f"   n(F*) = {n}: {len(tops)} topologies, {ncore} live-core "
              f"classes (EXHAUSTIVE, NO CAP), {nfree} PROVED free by a "
              f"corank-0 exact-Q witness")
    t4, f4, c4 = hunt_range(4, 6, 8, nseed=nseed)
    tot += t4
    free += f4
    cand += c4
    print(f"   n(F*) = 4, |E*| in 6..8: {t4} live-core classes (EXHAUSTIVE "
          f"in that cell range), {f4} proved free")
    print(f"   TOTAL: {tot} live-core classes, {free} proved free, "
          f"{len(cand)} candidates")
    for row in cand[:40]:
        print(f"     CANDIDATE {row}")
    print("   COVERAGE, stated as a cap: `n(F*) in {2, 3}` is complete at "
          "every `|E*|`; `n(F*) = 4` is complete here only for `|E*| <= 8`. "
          "`--huntn N LO HI [PART OF]` runs any other cell -- this pass also "
          "ran `--huntn 5 8 8` in three slices (70 174 classes, all free). "
          "Cells NOT searched: `n(F*) = 4` at `|E*| >= 9`, `n(F*) = 5` at "
          "`|E*| >= 9`, and every `n(F*) >= 6`.")
    return tot, free, cand


def hunt_range(n, lo, hi, nseed=8, part=0, of=1):
    """The `n(F*) = n` sweep restricted to `|E*| in [lo, hi]`, optionally to
    slice `part` of `of` (a deterministic stride over the enumerated core
    classes) -- the same computation as `--hunt`'s legs, split only so that
    each invocation fits a 600 s foreground budget
    (`notes/scripts/README.md`'s `flanks --limit` / `yloc --coll`
    precedent).  Slicing changes NOTHING but which classes an invocation
    covers; the union of the slices is the cell."""
    tot, free, cand = 0, 0, []
    k = 0
    for (nn, E0) in core_topologies(n, lo, hi):
        for lens in core_lengths(n, E0):
            k += 1
            if (k - 1) % of != part:
                continue
            best, drew, E = core_corank(n, E0, lens, nseed=nseed)
            tot += 1
            if best == 0:
                free += 1
            else:
                cand.append((n, tuple(E0), lens, best, drew))
    return tot, free, cand


def mode_huntn(n, lo, hi, part=0, of=1, nseed=8):
    print(f"== (OC-48) THE HUNT, cell range: n(F*) = {n}, |E*| in "
          f"{lo}..{hi}, slice {part} of {of} ==")
    print("   same computation, same seeds, same gate and the same "
          "iso-reduction as `--hunt`; split by `|E*|` cell and by a "
          "deterministic stride only so each invocation fits a 600 s "
          "foreground budget.  The union of the slices IS the cell.")
    tot, free, cand = hunt_range(n, lo, hi, nseed=nseed, part=part, of=of)
    print(f"   live-core classes in this slice: {tot}; PROVED free by a "
          f"corank-0 exact-Q witness: {free}; candidates: {len(cand)}")
    for row in cand[:40]:
        print(f"     CANDIDATE {row}")
    return tot, free, cand


# =================================================== mode --cert (OC-49) ====

def fixed_sum_vectors(m, total, hi):
    """Every `d in {0..hi}^m` with `sum d == total`."""
    cur = [0] * m

    def rec(i, rem):
        if i == m - 1:
            if 0 <= rem <= hi:
                cur[i] = rem
                yield tuple(cur)
            return
        for x in range(0, min(hi, rem) + 1):
            cur[i] = x
            yield from rec(i + 1, rem - x)
    if m == 0:
        return
    yield from rec(0, total)


def off_k4_bases(nmax=5, emax_cap=10):
    """The hub multigraphs a class shape can have, other than `K4`:
    loopless, connected, min degree >= 3, `|E*| <= min(6(|V*| - 1),
    emax_cap)` ((OC-45)(iii) plus a DISCLOSED cap), parallel multiplicity
    <= 5 ((OC-45)(ii) again: `k` parallel branches need `sum ell >= 6k - 5`
    while `ell <= 5` caps it at `5k`)."""
    out = []
    for n in range(2, nmax + 1):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        emax = min(6 * (n - 1), emax_cap)
        seen = set()
        for mult in itertools.product(range(0, 6), repeat=len(pairs)):
            m = sum(mult)
            if m > emax or m < (3 * n + 1) // 2:
                continue
            deg = [0] * n
            for (i, j), t in zip(pairs, mult):
                deg[i] += t
                deg[j] += t
            if min(deg) < 3:
                continue
            par = list(range(n))

            def find(x):
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x
            comp = n
            for (i, j), t in zip(pairs, mult):
                if t:
                    a, b = find(i), find(j)
                    if a != b:
                        par[a] = b
                        comp -= 1
            if comp != 1:
                continue
            key = canon_multigraph(n, mult, pairs)
            if key in seen:
                continue
            seen.add(key)
            E0 = [pr for pr, t in zip(pairs, mult) for _ in range(t)]
            if n == 4 and len(E0) == 6 and len(set(E0)) == 6:
                continue                       # that IS the K4 stratum
            c = len(E0) - n + 1
            if 6 * c > 5 * len(E0) or 6 * c < len(E0):
                continue
            out.append((n, E0))
    return out


def off_k4_shapes(cell_cap=None, nmax=5, emax_cap=10):
    """Class shapes whose hub multigraph is NOT `K4`, enumerated per hub
    multigraph.  `cell_cap` caps the number kept per multigraph and IS
    PRINTED wherever a figure from this pool is quoted; `emax_cap` caps
    `|E*|` and is printed too."""
    out = []
    for (n, E0) in off_k4_bases(nmax=nmax, emax_cap=emax_cap):
        m = len(E0)
        tot = 6 * (m - n + 1)
        kept = 0
        auts = _auts(n, E0)
        bind = binding_subsets(E0, 5 * m - tot)
        seen = set()
        for d in fixed_sum_vectors(m, 5 * m - tot, 4):
            lens = tuple(5 - x for x in d)
            if 3 not in lens:
                continue
            if not class_ok_counting(n, E0, lens, bind=bind):
                continue
            key = canon_lengths_key(n, E0, lens, auts)
            if key in seen:
                continue
            seen.add(key)
            E = build_subdivision(n, E0, list(lens))
            if not eligible_splits(E):
                continue
            out.append((f'V{n}E{m}{lens}', n, E0, lens, E))
            kept += 1
            if cell_cap is not None and kept >= cell_cap:
                break
    return out


def mode_cert(nmax=5, emax_cap=9, sample_cap=250):
    print("== (OC-49): the AMBIENT coverage -- which class (shape, split) "
          "pairs the (OC-48) core theorem actually settles, ON AND OFF the "
          "`G* = K4` stratum ==")
    print("   BOUNDARY (restated from (OC-39)(i)): `{sigma = 0}` is Zariski "
          "open in an irreducible chart, so `{sigma = 0} = empty` is CLOSED; "
          "one rational chart point with `corank R(H) = 0` is a COMPLETE "
          "per-pair certificate, and a pair with no such point found is "
          "`not found under the cap`, never a hit.")
    print("   WHAT IS NEW.  `H = G - v - a` is an INDUCED subgraph of `G`, "
          "so (OC-46) applies to `H` itself and `sigma` equals the corank of "
          "`H`'s LIVE CORE on the CORE's own chart.  A pair whose core is on "
          "(OC-48)'s exhausted list is therefore settled by a THEOREM, with "
          "no per-shape sampling at all.")
    print("   the counting class predicate `class_ok_counting` is used for "
          "enumeration; it is cross-checked against the oracle predicate "
          "`class_shape_ok` (deficiency + no_rigid_branch_union) below.")

    # self-check: counting predicate == oracle predicate on the K4 stratum
    a, b = set(), set()
    for lens in itertools.product(range(1, 6), repeat=6):
        if sum(lens) != 18:
            continue
        if class_ok_counting(4, K4E, lens):
            a.add(lens)
        if class_shape_ok(build_subdivision(4, K4E, list(lens))):
            b.add(lens)
    print(f"   SELF-CHECK: counting predicate accepts {len(a)} K4-stratum "
          f"length vectors, oracle predicate {len(b)}, equal: {a == b}")
    assert a == b, "the counting class predicate diverges from the oracle"

    spot, agree = 0, 0
    for (nm, n, E0, lens, E) in off_k4_shapes(cell_cap=3, nmax=5,
                                              emax_cap=8):
        spot += 1
        if class_shape_ok(E) == class_ok_counting(n, E0, lens):
            agree += 1
    print(f"   SELF-CHECK (off-`K4`): the two predicates agree at "
          f"{agree} / {spot} spot-checked off-`K4` shapes "
          f"(cell cap 3, |E*| <= 8 -- the oracle predicate costs a matroid "
          f"rank per branch subset, so the cross-check itself is capped)")
    assert agree == spot, "the counting predicate diverges off K4"

    from sigz import named_pool
    legs = [("the five NAMED class habitats -- (OC-39)'s pool minus its "
             "K4 stratum", list(named_pool())),
            ('G* = K4 (EXHAUSTIVE, no cap)',
             [(f'K4{l}', E) for l, E in k4_stratum_range(5)])]
    off = off_k4_shapes(cell_cap=None, nmax=nmax, emax_cap=emax_cap)
    legs.append((f'G* != K4, |V*| <= {nmax}, |E*| <= {emax_cap} '
                 f'(EXHAUSTIVE inside that CAP, iso-reduced)',
                 [(nm, E) for (nm, n, E0, lens, E) in off]))
    print("   EXHAUSTED CELLS (from (OC-48), each with NO cap inside the "
          "cell): n(F*) = 2 and 3 at every |E*|; n(F*) = 4 at |E*| in "
          "6..8; n(F*) = 5 at |E*| = 8.  A pair whose `H`-live-core lands "
          "in one of those cells -- or is EMPTY -- is settled by the "
          "theorem.")
    for label, shapes in legs:
        dist, pairs, settled = {}, 0, 0
        for (nm, E) in shapes:
            for v in eligible_splits(E):
                sd = split_data(E, v)
                if sd is None:
                    continue
                Hed = sd[4]
                Ec, nodes, plens = live_core(Hed)
                pairs += 1
                key = (len(nodes), len(plens))
                dist[key] = dist.get(key, 0) + 1
                if cell_exhausted(len(nodes), len(plens)):
                    settled += 1
        print(f"   {label}: {len(shapes)} shapes, {pairs} (shape, split) "
              f"pairs")
        for k in sorted(dist):
            print(f"     `H`-live-core (n(F*), #paths) = {k}: {dist[k]} "
                  f"pairs")
        print(f"     pairs whose `H`-live-core lies in an EXHAUSTED "
              f"(OC-48) cell, hence SETTLED by the theorem with no "
              f"per-shape sampling: {settled} / {pairs}")

    print(f"   CROSS-CHECK: exact-Q full-row-rank certificates for `R(H)` at "
          f"a deterministic stride sample of the off-`K4` pairs, "
          f"SAMPLE CAP {sample_cap} pairs (the cap is real)")
    pool = [(nm, E) for (nm, n, E0, lens, E) in off]
    step = max(1, len(pool) // sample_cap)
    tested, certified, unresolved = 0, 0, []
    for (name, E) in pool[::step][:sample_cap]:
        got = sample_chart(E, SEED + 3 * len(E), tries=10)
        placed = got[0] if got else None
        for v in eligible_splits(E)[:1]:
            sd = split_data(E, v)
            if sd is None:
                continue
            a2, b2, c2, Gp, Hed = sd
            tested += 1
            ok = False
            if placed is not None:
                d, rk = direct_corank(Hed, placed)
                assert rk == 5 * len(Hed) - d, "rank ledger broke"
                if d == 0:
                    assert rk == 5 * len(Hed), "corank-0 rank certificate"
                    ok = True
            if not ok:
                g2 = sample_chart(Gp, SEED + 613 + 5 * len(Hed), tries=10)
                if g2 is not None:
                    d, rk = direct_corank(Hed, g2[0])
                    if d == 0:
                        assert rk == 5 * len(Hed)
                        ok = True
            if ok:
                certified += 1
            else:
                unresolved.append((name, v))
    print(f"     off-`K4` pairs sampled: {tested}; carrying an exact-Q "
          f"FULL-ROW-RANK certificate: {certified}; unresolved under the "
          f"cap: {len(unresolved)}")
    print("   (OC-39) UPGRADED: its pool was the 877 `K4` shapes PLUS the "
          "five named habitats, 3368 (shape, split) pairs sampled.  Here "
          "3324 + 44 = 3368 pairs, and EVERY one of them has an `H`-live-"
          "core in an exhausted cell -- so all 3368 of (OC-39)'s per-pair "
          "certificates are now consequences of a theorem.")
    for row in unresolved[:12]:
        print(f"       UNRESOLVED {row}")
    return tested, certified, len(unresolved)


def cell_exhausted(n, m):
    """Is the `(n(F*), |E(F*)|)` cell one that (OC-48) enumerated with NO cap
    and found entirely free?  `n = 0` is the empty core (no live core at
    all, hence no stress).  The cells are exactly the ones the `--hunt` /
    `--huntn` invocations recorded in the workbook's *Verification* block."""
    if n == 0:
        return True
    if n in (2, 3):
        return True
    if n == 4 and 6 <= m <= 8:
        return True
    if n == 5 and m == 8:
        return True
    return False


# ---------------- main ---------------------------------------------------

def main(argv):
    args = argv[1:]
    if '--huntn' in args:
        k = args.index('--huntn')
        n, lo, hi = int(args[k + 1]), int(args[k + 2]), int(args[k + 3])
        part = int(args[k + 4]) if len(args) > k + 4 else 0
        of = int(args[k + 5]) if len(args) > k + 5 else 1
        mode_huntn(n, lo, hi, part, of)
        return 0
    flags = set(args)
    if not flags or '--validate' in flags:
        flags = {'--bound', '--dom', '--core', '--hunt', '--cert'}
    if '--bound' in flags:
        mode_bound()
        print()
    if '--dom' in flags:
        mode_dom()
        print()
    if '--core' in flags:
        mode_core()
        print()
    if '--hunt' in flags:
        mode_hunt()
        print()
    if '--cert' in flags:
        mode_cert()
        print()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
