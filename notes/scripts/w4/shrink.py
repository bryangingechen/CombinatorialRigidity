"""
Phase 39, kernel-(K) second fan-out direction R -- (ANH-R1): PENCIL-RIGIDITY
OF THE CONTRACTED FRAMEWORK, THE WEAK-MAP QUESTION, AND THE BAD LOCUS.

Workbook section: `(K-ann)`, continuation Steps A10-A13; labels `(ANH-9)` --
`(ANH-12)` (the reserved direction-R namespace, `notes/Pencil-labels.md`
2026-08-06 T/R/M table).  Read against section (K-ann) *Steps A4/A7/A8*
((ANH-4) the `k = 4` Tay circuit, (ANH-7) the one-bracket recipe, (ANH-R1)
its open input), section (K-out) *Steps O3/O6* ((OC-3)/(OC-4), whose shape
this driver's `--bad` mode mirrors on the tau side) and
`notes/Pencil-strategy.md` sections 2.3 / 4.6 (the rank-lower-bound
asymmetry and the weak-map lead).

THE OBJECT.  At a `k = 4` class (shape, split, companion) with a guarded
target-rank seed, `H/P` (the far graph with the companion welded) has generic
Tay stress dimension 1 and `E(H/P)` is a CIRCUIT ((ANH-4)): generically every
edge is stressed.  The realized stress `tau` at the PENCIL placement can only
specialize (`supp_pen <= supp_gen`).  Since `tau` is constant along each
branch of `H/P` ((ANH-6)), the support is a union of branches, and

    supp_pen  is strictly smaller than  supp_gen
        <=>  some branch beta has tau_beta = 0
        <=>  H/P - beta is DEPENDENT at the pencil placement,

which at a length-5 branch (count exactly 0) is the failure of (ANH-R1).

(ANH-9), framing (no driver leg of its own -- the census supplies its
per-shape witnesses).  The pencil chart is an irreducible parametrized
variety, so "the matroid at the generic pencil placement" `M_pen^gen` is
well-defined and is a weak-map image of the generic Tay matroid `M_gen`;
(ANH-R1) at a triple is `E(H/P) - beta` independent in `M_pen^gen`, and by
rank semicontinuity ONE rational chart point with `H/P - beta` independent
decides it for that triple.

(ANH-10), mode `--census`.  The pinned probe (`notes/Phase39.md` (g)): hunt a
class seed with `supp_pen` strictly inside `supp_gen` at `k = 4`.  Per
guarded seed (composite guard `repin.star_generic`, riding in through
`dominance.base_seed` -- so the aggregate may be quoted as a rate): the
stress dimension, the branch-by-branch support, and an independent
cross-check that rebuilds the stress space of `H/P - beta` on the reduced
edge list.  The off-class control (hnoRigid dropped) is the positive control:
there the hunt target EXISTS and the machinery must find it.

(ANH-11)/(ANH-12), mode `--bad`.  The common-transversal construction: if all
six hinge lines of a 6-cycle `Z` in `H/P - beta` meet one line `L`, they lie
in the special linear complex of axis `L`, so `C(L)` is a self-stress
supported on `Z` -- a Tay-ISOSTATIC 6-cycle gone dependent -- and
`H/P - beta` is dependent there.  Anchoring `L = line(pt(u0), pt(u3))` at two
opposite cycle bodies makes four of the six incidences automatic, and the two
others are LINEAR in one movable far vertex each, so the bad point is reached
EXACTLY (rational coordinates) by two legal single-vertex pencil-chart moves.
This is the tau-side analogue of section (K-out)'s (OC-4) silent point:
(ANH-R1)'s bad locus is inhabited on the honest chart, so no counting /
matroid / placement-blind argument can ever deliver (ANH-R1).

Mode `--comb`: the combinatorial availability of the construction over the
4296-triple census pool (no placements).

Drivers (foreground, one at a time; exact rational arithmetic, no floating
point anywhere; every sampled configuration carries rank/dimension asserts;
all sampling is through `dominance.base_seed`'s guarded integer seeds --
this file adds NO new rng):

    python3 notes/scripts/w4/shrink.py --census    # (ANH-10), the pinned probe
    python3 notes/scripts/w4/shrink.py --bad       # (ANH-11)/(ANH-12)
    python3 notes/scripts/w4/shrink.py --comb      # construction availability
    python3 notes/scripts/w4/shrink.py --validate  # the machinery
"""
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, wedge2, hat, dot, neighbors
from repin import span_basis, in_span, star_generic
from pitch import klein, det4
from kbare_common import verify_pencil_witness
from outer import (split_data, companions4, named_inventory, sweep_shapes,
                   eligible_splits, stratum_at)
from annih import (prepared, stress_space, contracted_edges, hp_branches,
                   branch_lengths, branch_screw, girth, gen_stress_dim,
                   habitats4, control_shapes, swept_probes, path_edges,
                   single_vertex_dirs)
from dominance import cycle_data


# ---------------- bookkeeping on the contracted multigraph ------------------

def hp_edge_rows(Hed, Pverts, Pset, tag='X*'):
    """`E(H/P)` as `(j, u, w, x, y)` rows: `j` the `H`-edge index, `(u, w)`
    the welded body names, `(x, y)` the real endpoint VERTICES of `H` (whose
    placed points define the hinge line -- a line at the welded body `X` still
    passes through its companion-vertex endpoint)."""
    out = []
    for j, (x, y) in enumerate(Hed):
        if j in Pset:
            continue
        u = tag if x in Pverts else x
        w = tag if y in Pverts else y
        assert u != w, "H/P has a loop"
        out.append((j, u, w, x, y))
    return out


def branch_edge_ix(Hed, path):
    """The `H`-edge indices along a branch vertex path."""
    return {j for (j, s) in path_edges(Hed, path)}


def stress_dim_without(Hed, VH, placed, Pset, drop):
    """dim of the realized stress space of `H/P - drop`, rebuilt from scratch
    on the reduced edge list (an independent matrix, not a slice of the full
    solve).  `drop` must avoid the companion."""
    assert not (set(drop) & set(Pset)), "dropping companion edges"
    red, redP = [], set()
    for t, e in enumerate(Hed):
        if t in drop:
            continue
        if t in Pset:
            redP.add(len(red))
        red.append(e)
    return len(stress_space(red, VH, placed, redP)[0])


def hp_cycles(rows, length=6, avoid=frozenset(), cap=200):
    """Simple `length`-cycles of the contracted multigraph, as `(edge rows in
    cyclic order, body sequence)` pairs.  Bodies pairwise distinct; `H`-edge
    indices in `avoid` excluded; deterministic; each cycle once."""
    adj = {}
    for r in rows:
        if r[0] in avoid:
            continue
        adj.setdefault(r[1], []).append((r, r[2]))
        adj.setdefault(r[2], []).append((r, r[1]))
    for u in adj:
        adj[u].sort(key=lambda t: t[0][0])
    out, seen = [], set()

    def dfs(start, cur, es, eset, bset):
        if len(out) >= cap:
            return
        for (r, w) in adj.get(cur, ()):
            if r[0] in eset:
                continue
            if len(es) == length - 1:
                if w == start:
                    key = frozenset(eset | {r[0]})
                    if key not in seen:
                        seen.add(key)
                        out.append(es + [r])
                continue
            if w == start or w in bset:
                continue
            dfs(start, w, es + [r], eset | {r[0]}, bset | {w})

    for start in sorted(adj, key=str):
        dfs(start, start, [], frozenset(), frozenset({start}))
    # reconstruct body sequences
    fixed = []
    for es in out:
        e0b = {es[0][1], es[0][2]}
        elb = {es[-1][1], es[-1][2]}
        start = sorted(e0b & elb, key=str)[0]
        bodies, cur = [start], start
        for r in es:
            cur = r[2] if r[1] == cur else r[1]
            bodies.append(cur)
        assert bodies[-1] == bodies[0] and len(set(bodies[:-1])) == length, \
            "cycle reconstruction failed"
        fixed.append((es, bodies[:-1]))
    return fixed


def hp_six_cycles(rows, avoid=frozenset(), cap=200):
    """The 6-cycle case (the availability census `--comb` measures exactly
    this form)."""
    return hp_cycles(rows, 6, avoid, cap)


# ---------------- the census pool --------------------------------------------

def census_pool(per_family=4, cap_swept=28):
    """The pinned pool: the four named `k = 4` class habitats at their pinned
    splits, plus the first `per_family` class shapes of each
    `outer.sweep_shapes` family that carry an eligible split with a length-4
    companion (nobody hand-picked those), capped at `cap_swept` swept rows.
    Deterministic."""
    out = [(n, E, v) for (n, E, v) in habitats4()]
    swept = 0
    for desc, shapes in sweep_shapes():
        taken = 0
        for label, E in shapes:
            if taken >= per_family or swept >= cap_swept:
                break
            for v in eligible_splits(E):
                sd = split_data(E, v)
                if sd is None:
                    continue
                a, b, c, Gp, Hed = sd
                if not companions4(Hed, b, c):
                    continue
                out.append((f'sw:{label}/v{v}', E, v))
                taken += 1
                swept += 1
                break
        if swept >= cap_swept:
            break
    return out


# ---------------- mode: the census (ANH-10) ----------------------------------

def branch_report(d):
    """(dimS, branches, zero_branches, taus): the stress space at the seed and
    the branch-by-branch support of its (unique, at k = 4) stress."""
    Hed, VH, placed = d['Hed'], d['VH'], d['placed']
    taus, C = stress_space(Hed, VH, placed, d['Pset'])
    branches = hp_branches(Hed, d['Pverts'], d['Pset'])
    zeros = []
    if len(taus) == 1:
        for path in branches:
            rho = branch_screw(Hed, taus[0], path)
            if all(x == 0 for x in rho):
                zeros.append(path)
    return len(taus), branches, zeros, taus


def mode_census():
    print("== (ANH-10) the support census: hunting supp_pen strictly inside"
          " supp_gen at k = 4 ==")
    print("   At k = 4, (ANH-4) makes E(H/P) a circuit: supp_gen = E(H/P).")
    print("   tau is one screw per BRANCH ((ANH-6)), so a strict drop at the")
    print("   pencil placement is exactly: some branch beta with tau_beta = 0,")
    print("   i.e. H/P - beta DEPENDENT there -- at a length-5 branch, the")
    print("   failure of (ANH-R1).  Every seed is `dominance.base_seed`-")
    print("   guarded (composite guard repin.star_generic), so the aggregate")
    print("   may be quoted as a rate.  The off-class control (hnoRigid")
    print("   dropped) is the positive control: the drop EXISTS there and the")
    print("   machinery must find it.\n")
    pool = census_pool()
    print(f"   pool: {len(pool)} (shape, split) pairs "
          f"(4 named k = 4 habitats + {len(pool) - 4} swept)")
    print(f"\n   {'shape/split':<34}{'seed':>5} {'dimRa':>6} {'|E(H/P)|':>9}"
          f" {'dimS':>5} {'#br':>4} {'#l5':>4} {'zero':>5} {'xchk':>5}")
    nseed = nfull = n5 = nsite5 = nhard = 0
    drops, anomalies, skipped = [], [], []
    for (name, E, v) in pool:
        ds = prepared(E, v, 1)
        if not ds:
            skipped.append((name, 'no guarded seed <= 400'))
            continue
        d = ds[0]
        if d['k'] != 4:
            skipped.append((name, f"k = {d['k']}"))
            continue
        Hed, VH, placed = d['Hed'], d['VH'], d['placed']
        # the GENERIC side of `supp_gen = E(H/P)` at this shape ((ANH-4)
        # proves it; the pebble game re-checks the stress dimension)
        HP = contracted_edges(Hed, d['Pverts'], d['Pset'])
        assert gen_stress_dim(HP) == 1, f"{name}: H/P generic count != 1"
        dimS, branches, zeros, taus = branch_report(d)
        if dimS != 1:
            anomalies.append((name, d['seed'], f'dim S_pen = {dimS} != 1'))
            print(f"   {name:<34}{d['seed']:>5} {d['dim R_a']:>6}"
                  f" {len(Hed) - 4:>9} {dimS:>5}   ** ANOMALY: H/P not"
                  " pencil-rigid **")
            continue
        b5 = [p for p in branches if len(p) - 1 == 5]
        # cross-check: rebuild the reduced stress space for every length-5
        # branch, plus the first shorter branch (the equivalence
        # `tau_beta = 0  <=>  H/P - beta dependent` needs dim S_pen = 1,
        # asserted above).
        xchk = 0
        zero_sets = [branch_edge_ix(Hed, p) for p in zeros]
        for path in b5 + branches[:1]:
            bset = branch_edge_ix(Hed, path)
            dred = stress_dim_without(Hed, VH, placed, d['Pset'], bset)
            iszero = bset in zero_sets
            assert (dred >= 1) == iszero, \
                f"{name}: tau_beta and the reduced rebuild disagree"
            xchk += 1
        if zeros:
            drops.append((name, d['seed'], [len(p) - 1 for p in zeros]))
        else:
            nfull += 1
        nseed += 1
        nsite5 += len(b5)
        n5 += 1 if b5 else 0
        nhard += 1 if d['dim R_a'] == 1 else 0
        print(f"   {name:<34}{d['seed']:>5} {d['dim R_a']:>6}"
              f" {len(Hed) - 4:>9} {dimS:>5} {len(branches):>4}"
              f" {len(b5):>4} {len(zeros):>5} {xchk:>5}")
    # the positive control: the machinery must FIND the drop off-class
    print("\n   -- off-class positive control (hnoRigid FAILS there) --")
    ctl_found = 0
    for (name, E, v) in control_shapes():
        d = prepared(E, v, 1)[0]
        Hed, VH = d['Hed'], d['VH']
        dimS, branches, zeros, taus = branch_report(d)
        assert dimS == 1 and zeros, \
            "the control was supposed to exhibit a zero branch"
        bset = branch_edge_ix(Hed, zeros[0])
        assert stress_dim_without(Hed, VH, d['placed'], d['Pset'],
                                  bset) >= 1
        ctl_found += 1
        print(f"   {name:<34}{d['seed']:>5} : dim S = {dimS},"
              f" zero branches {sorted(len(p) - 1 for p in zeros)}"
              " -- the hunt target exists and is FOUND here")
    for (name, why) in skipped:
        print(f"   [skipped {name}: {why}]")
    print(f"\nCENSUS {'HIT' if drops or anomalies else 'OK'}: {nseed} guarded"
          f" k = 4 class seeds over {nseed + len(skipped)} pooled pairs;"
          f" dim S_pen = 1 and supp_pen = E(H/P) (every branch stressed) at"
          f" {nfull}/{nseed}; {nsite5} length-5-branch sites, tau_beta != 0"
          f" at every one -- (ANH-R1) witnessed per shape; {nhard} seeds on"
          f" the hard stratum (dim R_a = 1); reduced-rebuild cross-checks"
          f" agree at every seed; the off-class control finds its drop"
          f" ({ctl_found}/1).")
    if drops:
        print("   STRICT SUPPORT DROPS FOUND (class!):", drops)
    if anomalies:
        print("   ANOMALIES:", anomalies)


# ---------------- the common-transversal construction (ANH-11/12) -----------

CAND_T = [F(0), F(1), F(-1), F(2), F(-2), F(3), F(1, 2), F(-1, 2), F(5),
          F(-3), F(7), F(2, 3)]


def plane_functional(A0h, A3h, ph):
    """`x -> det4([A0h, A3h, ph, hat(x)])` as `(n, c)`, value `n . x + c`
    (affine in `x`).  The zero set is the plane through the three points;
    a point `x` on it makes `line(p, x)` meet `line(A0, A3)`."""
    c = det4([A0h, A3h, ph, hat([F(0)] * 3)])
    n = []
    for i in range(3):
        e = [F(1) if t == i else F(0) for t in range(3)]
        n.append(det4([A0h, A3h, ph, hat(e)]) - c)
    return n, c


def solve_on_moves(n, c, x0, dirs, maxout=8):
    """Rational points `x = x0 + sum t_i d_i` with `n . x + c = 0`,
    deterministically enumerated (small parameters first).  Empty when the
    functional is constant nonzero on the affine move space."""
    a = [dot(n, dd) for dd in dirs]
    r = -(dot(n, x0) + c)
    if all(x == 0 for x in a):
        return [list(x0)] if r == 0 else []
    piv = next(i for i in range(len(a)) if a[i] != 0)
    free = [i for i in range(len(a)) if i != piv]
    outs = []
    if not free:
        combos = [()]
    elif len(free) == 1:
        combos = [(t,) for t in CAND_T]
    else:
        combos = [(t1, t2) for t1 in CAND_T[:4] for t2 in CAND_T[:4]]
    for combo in combos:
        tp = (r - sum((t * a[i] for t, i in zip(combo, free)), F(0))) / a[piv]
        ts = {piv: tp}
        for t, i in zip(combo, free):
            ts[i] = t
        x = [x0[k] + sum((ts[i] * dirs[i][k] for i in range(len(dirs))),
                         F(0)) for k in range(3)]
        outs.append(x)
        if len(outs) >= maxout:
            break
    return outs


def cycle_stress(Hed, lab_e, lab_b, CL, P, Pe):
    """The constant-screw circulation `+-CL` around the cycle as a `tau`
    dict over `H`-edge indices -- INCLUDING, when the cycle passes through
    the welded body `X`, the compensating flow along the companion edges
    (equilibrium at each companion vertex; transmissibility is not required
    there, which is exactly the weld).  Equilibrium is asserted body by
    body at the welded level and vertex by vertex along `P`."""
    eps = {lab_e[0][0]: 1}
    clen = len(lab_e)
    # contribution sign of edge r at welded body u: +1 at the head r[2]
    for i in range(clen):
        r, rn = lab_e[i], lab_e[(i + 1) % clen]
        u = lab_b[(i + 1) % clen]
        cu = 1 if r[2] == u else -1
        cn = 1 if rn[2] == u else -1
        if rn[0] not in eps:
            eps[rn[0]] = -eps[r[0]] * cu * cn
    tau = {r[0]: [F(eps[r[0]]) * x for x in CL] for r in lab_e}
    # welded equilibrium at every cycle body
    for u in lab_b:
        s = [F(0)] * 6
        for r in lab_e:
            if r[2] == u:
                s = [a + b for a, b in zip(s, tau[r[0]])]
            elif r[1] == u:
                s = [a - b for a, b in zip(s, tau[r[0]])]
        assert all(x == 0 for x in s), "cycle circulation out of equilibrium"
    # the companion flow: residual of the cycle edges at each P vertex ...
    resid = {v: [F(0)] * 6 for v in P}
    for r in lab_e:
        j, u, w, x, y = r
        for (vert, sgn) in ((y, 1), (x, -1)):
            if vert in resid:
                resid[vert] = [a + F(sgn) * b
                               for a, b in zip(resid[vert], tau[j])]
    # ... balanced sequentially along P (edge i contributes -s_i tau at P[i]
    # and +s_i tau at P[i+1], s_i the stored orientation)
    prev = None
    for i in range(len(P) - 1):
        (j, s) = Pe[i]
        inflow = [F(0)] * 6 if prev is None else \
            [F(Pe[i - 1][1]) * t for t in tau[Pe[i - 1][0]]]
        tau[j] = [F(s) * (a + b) for a, b in zip(inflow, resid[P[i]])]
        prev = j
    end = [F(Pe[-1][1]) * t for t in tau[Pe[-1][0]]]
    assert all(a + b == 0 for a, b in zip(end, resid[P[-1]])), \
        "companion flow does not close at c"
    return tau


def construct_at(d):
    """The (ANH-11)/(ANH-12) construction at one guarded seed.  Returns a
    (verdict, result-dict-or-None) pair."""
    Hed, VH, placed, nrm = d['Hed'], d['VH'], d['placed'], d['nrm']
    Pset, Pverts = d['Pset'], d['Pverts']
    hubs = set(d['hubsGp'])
    rows = hp_edge_rows(Hed, Pverts, Pset)
    if len(rows) == 5:
        return ('trivial: H/P is the bare 5-cycle, H/P - beta is EMPTY,'
                ' (ANH-R1) holds at every chart point', None)
    branches = hp_branches(Hed, Pverts, Pset)
    b5 = [p for p in branches if len(p) - 1 == 5]
    # prefer a length-5 branch (H/P - beta count 0: (ANH-R1)'s exact
    # statement); fall back to the longest branches (still a Tay-independent
    # set gone dependent -- the matroid-drop witness, not (ANH-R1) verbatim)
    pool = b5 if b5 else sorted(branches, key=lambda p: -len(p))[:3]
    best = None
    g = girth([(r[1], r[2]) for r in rows])
    budget = {'stratum': 16}    # stratum_at calls are the expensive scan cost
    for beta in pool:
        bset = branch_edge_ix(Hed, beta)
        for clen in (6, 7, 8):
            if clen < (g or 6):
                continue
            for (es, bodies) in hp_cycles(rows, clen, avoid=bset, cap=40):
                for rot in range(clen):
                    for flip in (False, True):
                        idx = [(rot + (clen - 1 - i if flip else i)) % clen
                               for i in range(clen)]
                        lab_b = [bodies[t] for t in idx]
                        lab_e, ok = [], True
                        for i in range(clen):
                            u, w = lab_b[i], lab_b[(i + 1) % clen]
                            cand = [r for r in es
                                    if {r[1], r[2]} == {u, w}]
                            if len(cand) != 1:
                                ok = False
                                break
                            lab_e.append(cand[0])
                        if not ok:
                            continue
                        if lab_b[0] == 'X*' or lab_b[3] == 'X*':
                            continue
                        res = try_plan(d, lab_e, lab_b, beta, bset, budget)
                        if res is not None:
                            score = (res['guard'],
                                     res['stratum'] is not None,
                                     (res['stratum'] or (0, 0))[1] == 1)
                            if best is None or score > best[0]:
                                best = (score, res)
                            if all(score):
                                return ('witness', certify(d, best[1]))
    if best is not None:
        return ('witness', certify(d, best[1]))
    return ('no construction reached a legal point', None)


def assign_movers(lab_e, lab_b, placed, CL, Pverts, hubs):
    """The condition edges of a labeled `c`-cycle (everything not incident to
    an anchor body), each assigned a movable endpoint; a mover may take up to
    two conditions.  Returns `[(mover, [(other end, cond edge), ...])]` in
    cycle order, or None."""
    clen = len(lab_b)
    A0, A3 = lab_b[0], lab_b[3]
    conds = [lab_e[1]] + [lab_e[i] for i in range(4, clen - 1)]
    plans, order = {}, []
    for ce in conds:
        j, u, w, x, y = ce
        Cj = wedge2(hat(placed[x]), hat(placed[y]))
        if all(v == 0 for v in Cj):
            return None
        if klein(CL, Cj) == 0:
            continue                              # already meets L
        movers = [z for z in (x, y)
                  if z not in Pverts and z not in hubs
                  and z not in (A0, A3)
                  and len(plans.get(z, ())) < 2]
        # prefer a fresh mover over doubling one up
        movers.sort(key=lambda z: (len(plans.get(z, ())), str(z)))
        if not movers:
            return None
        z = movers[0]
        other = y if z == x else x
        if z not in plans:
            order.append(z)
        plans.setdefault(z, []).append((other, ce))
    return [(z, plans[z]) for z in order]


def try_plan(d, lab_e, lab_b, beta, bset, budget):
    """Solve the linear conditions for one labeling; return the best legal
    candidate (guard-accepted and on the hard stratum when reachable) as an
    UNcertified witness dict, else None.  `certify` runs the stress solves."""
    Hed, placed, nrm = d['Hed'], d['placed'], d['nrm']
    Gp, hubs = d['Gp'], set(d['hubsGp'])
    A0, A3 = lab_b[0], lab_b[3]
    A0h, A3h = hat(placed[A0]), hat(placed[A3])
    if rank([A0h, A3h]) < 2:
        return None
    CL = wedge2(A0h, A3h)
    plans = assign_movers(lab_e, lab_b, placed, CL, d['Pverts'], hubs)
    if plans is None:
        return None
    # solve mover by mover in assignment order, RE-DERIVING each functional
    # at the partially-updated placement (a later condition's fixed end may
    # itself have moved); the final meets-L re-check is the ground truth
    combos = [dict()]
    for (z, jobs) in plans:
        svd = single_vertex_dirs(Gp, placed, nrm, z, hubs)
        if not svd:
            return None
        dirs = [dd[z] for dd in svd]
        nxt = []
        for combo in combos:
            cur = dict(placed)
            cur.update(combo)
            sols = None
            for (other, ce) in jobs:
                ph = hat(cur[other])
                if rank([A0h, A3h, ph]) < 3:
                    continue                      # `other` on L: automatic
                n, c = plane_functional(A0h, A3h, ph)
                if sols is None:
                    sols = solve_on_moves(n, c, cur[z], dirs)
                else:
                    sols = [x for x in sols if dot(n, x) + c == 0]
            if sols is None:
                sols = [list(cur[z])]
            for x in sols[:4]:
                cc = dict(combo)
                cc[z] = x
                nxt.append(cc)
        combos = nxt[:24]
        if not combos:
            return None
    # collect legal candidates; prefer guard-accepted, then hard stratum
    legal = []
    for combo in combos[:24]:
        new = dict(placed)
        new.update(combo)
        okc = True
        for r in lab_e:
            C = wedge2(hat(new[r[3]]), hat(new[r[4]]))
            if all(v == 0 for v in C) or klein(CL, C) != 0:
                okc = False
                break
        if not okc:
            continue
        vw, _info = verify_pencil_witness(Gp, new)
        if not vw:
            continue
        legal.append((combo, new, star_generic(Gp, new)))
    if not legal:
        return None
    ranked = []
    for (combo, new, guard) in legal:
        st = None
        if guard and budget['stratum'] > 0:
            budget['stratum'] -= 1
            st = stratum_at(d['edges'], Gp, new, d['a'], d['b'])
        ranked.append(((guard, st is not None, (st or (0, 0))[1] == 1),
                       combo, new, guard, st))
    ranked.sort(key=lambda t: t[0], reverse=True)
    _score, combo, new, guard, st = ranked[0]
    return {'moved': dict(combo), 'anchors': (A0, A3), 'CL': CL,
            'lab_e': lab_e, 'lab_b': lab_b,
            'beta_len': len(beta) - 1, 'bset': bset,
            'clen': len(lab_b), 'guard': guard, 'stratum': st, 'new': new}


def certify(d, res):
    """The expensive half, run once on the chosen witness: the constructed
    stress is certified equation by equation, matched against an independent
    full solve, and the reduced (`H/P - beta`) space is rebuilt from
    scratch."""
    Hed, VH, new = d['Hed'], d['VH'], res['new']
    if res['stratum'] is None:
        res['stratum'] = stratum_at(d['edges'], d['Gp'], new,
                                    d['a'], d['b'])
    tau = cycle_stress(Hed, res['lab_e'], res['lab_b'], res['CL'],
                       d['P'], d['Pe'])
    Cnew = [wedge2(hat(new[x]), hat(new[y])) for (x, y) in Hed]
    for jj, t in tau.items():
        if jj not in d['Pset']:
            assert klein(t, Cnew[jj]) == 0, "not transmissible on the cycle"
    taus2, _C2 = stress_space(Hed, VH, new, d['Pset'])
    dimS = len(taus2)
    flat = [F(0)] * (6 * len(Hed))
    for jj, t in tau.items():
        flat[6 * jj:6 * jj + 6] = t
    kerflat = [[x for t in range(len(Hed)) for x in tt[t]] for tt in taus2]
    assert in_span(flat, span_basis(kerflat)), \
        "constructed stress not in the solved stress space"
    dred = stress_dim_without(Hed, VH, new, d['Pset'], res['bset'])
    assert dred >= 1, "H/P - beta not dependent at the witness"
    supp_drop = None
    if dimS == 1:
        supp = {jj for jj in range(len(Hed)) if jj not in d['Pset']
                and any(x != 0 for x in taus2[0][jj])}
        supp_drop = (len(supp), len(Hed) - len(d['Pset']))
    res.update({'dimS': dimS, 'dimS_red': dred, 'supp_drop': supp_drop})
    return res


def mode_bad():
    print("== (ANH-11)/(ANH-12) the bad locus of (ANH-R1) is inhabited ==")
    print("   Mechanism ((ANH-11)): six hinge lines of a 6-cycle Z in")
    print("   H/P - beta all meeting one line L lie in the special linear")
    print("   complex of axis L, so C(L) is a self-stress supported on Z --")
    print("   a Tay-isostatic 6-cycle gone dependent -- and H/P - beta is")
    print("   DEPENDENT.  Anchoring L at two opposite cycle bodies makes 4")
    print("   incidences automatic and the other 2 LINEAR in one movable far")
    print("   vertex each: the point is reached exactly, by two legal")
    print("   single-vertex pencil-chart moves ((ANH-12)).  Consequence: no")
    print("   counting / matroid / placement-blind argument can deliver")
    print("   (ANH-R1) -- the tau-side analogue of section (K-out) (OC-3).\n")
    nwit = ntriv = nfail = nguard = nhard = 0
    for (name, E, v) in habitats4() + swept_probes(6):
        ds = prepared(E, v, 1)
        if not ds:
            print(f"   {name:<34}: no guarded seed")
            continue
        d = ds[0]
        if d['k'] != 4:
            print(f"   {name:<34}: k = {d['k']}, skipped")
            continue
        verdict, res = construct_at(d)
        if res is None:
            if verdict.startswith('trivial'):
                ntriv += 1
                # assert the trivial case IS what it claims
                rows = hp_edge_rows(d['Hed'], d['Pverts'], d['Pset'])
                assert len(rows) == 5
                bl = branch_lengths([(r[1], r[2]) for r in rows])
                assert bl == [5]
                print(f"   {name:<34}: {verdict}")
            else:
                nfail += 1
                print(f"   {name:<34}: NOT constructed ({verdict})")
            continue
        nwit += 1
        nguard += 1 if res['guard'] else 0
        hard = res['stratum'] is not None and res['stratum'][1] == 1
        nhard += 1 if hard else 0
        st = ('target rank, dim R_a = ' + str(res['stratum'][1])
              if res['stratum'] else 'OFF target rank')
        drop = ''
        if res['supp_drop']:
            drop = (f"; supp DROPS {res['supp_drop'][1]} ->"
                    f" {res['supp_drop'][0]} with H/P still pencil-rigid")
        kind = ('(ANH-R1) EXACT (beta length 5, count 0)'
                if res['beta_len'] == 5 else
                f"matroid-drop form (beta length {res['beta_len']})")
        print(f"   {name:<34}: WITNESS seed {d['seed']},"
              f" {res['clen']}-cycle, anchors"
              f" {res['anchors']}, moved {sorted(res['moved'], key=str)},"
              f" {kind};"
              f" dim S(H/P) = {res['dimS']},"
              f" dim S(H/P - beta) = {res['dimS_red']} >= 1;"
              f" guard {'ACCEPTED' if res['guard'] else 'rejected'};"
              f" {st}{drop}")
        for z in sorted(res['moved'], key=str):
            print(f"        moved {z} -> {res['moved'][z]}")
    print(f"\nBAD OK: exact rational bad points at {nwit} shapes"
          f" ({nguard} guard-accepted, {nhard} at target rank on the hard"
          f" stratum), the trivial theta(3,4,5) case proven"
          f" ({ntriv}), {nfail} not constructed.  At every witness"
          " H/P - beta is DEPENDENT at a verified legal pencil-chart point"
          " (verify_pencil_witness green), so (ANH-R1) is irreducibly a"
          " generic-point statement: its bad locus meets the honest chart.")


# ---------------- mode: combinatorial availability ---------------------------

def comb_row(E, label, tally):
    """Per (shape, split, companion): does the construction's combinatorial
    precondition hold?  (length-5 branch + edge-disjoint 6-cycle + a labeling
    with real anchors and a movable vertex per condition edge)."""
    nb_all = neighbors(E)
    for v in sorted(nb_all, key=str):
        sd = split_data(E, v)
        if sd is None:
            continue
        a, b, c, Gp, Hed = sd
        nbGp = neighbors(Gp)
        hubs = {u for u in nbGp if len(nbGp[u]) >= 3}
        for P in companions4(Hed, b, c):
            tally['triples'] += 1
            Pe = path_edges(Hed, P)
            Pset = {j for (j, s) in Pe}
            Pverts = set(P)
            rows = hp_edge_rows(Hed, Pverts, Pset)
            branches = hp_branches(Hed, Pverts, Pset)
            b5 = [p for p in branches if len(p) - 1 == 5]
            if len(rows) == 5:
                tally['trivial'] += 1
                continue
            if not b5:
                tally['no_l5'] += 1
                continue
            tally['l5'] += 1
            found = False
            for beta in b5:
                if found:
                    break
                bset = branch_edge_ix(Hed, beta)
                for (es, bodies) in hp_six_cycles(rows, avoid=bset, cap=40):
                    if found:
                        break
                    for rot in range(6):
                        for flip in (False, True):
                            idx = [(rot + (5 - i if flip else i)) % 6
                                   for i in range(6)]
                            lab_b = [bodies[t] for t in idx]
                            A0, A3 = lab_b[0], lab_b[3]
                            if A0 == 'X*' or A3 == 'X*':
                                continue
                            lab_e, ok = [], True
                            for i in range(6):
                                u, w = lab_b[i], lab_b[(i + 1) % 6]
                                cand = [r for r in es
                                        if {r[1], r[2]} == {u, w}]
                                if len(cand) != 1:
                                    ok = False
                                    break
                                lab_e.append(cand[0])
                            if not ok:
                                continue
                            good, used = True, set()
                            for ce in (lab_e[1], lab_e[4]):
                                j, u, w, x, y = ce
                                mv = [z for z in (x, y) if z not in Pverts
                                      and z not in hubs
                                      and z not in (A0, A3)
                                      and z not in used
                                      and sum(1 for t in nbGp.get(z, ())
                                              if t in hubs) <= 2]
                                if not mv:
                                    good = False
                                    break
                                used.add(mv[0])
                            if good:
                                found = True
                                break
                        if found:
                            break
            if found:
                tally['eligible'] += 1
            else:
                tally['cycle_blocked'] += 1


def mode_comb():
    print("== construction availability over the census pool"
          " (combinatorial; no placements) ==")
    print("   Per (shape, split, length-4 companion) triple: a length-5")
    print("   branch beta of H/P, a 6-cycle edge-disjoint from it, and a")
    print("   labeling with both anchors real and a movable (non-hub, <= 2")
    print("   hub-neighbour) far vertex per condition edge.\n")
    tally = {'triples': 0, 'trivial': 0, 'no_l5': 0, 'l5': 0,
             'eligible': 0, 'cycle_blocked': 0}
    for label, E in named_inventory():
        comb_row(E, label, tally)
    named = dict(tally)
    print(f"   named inventory: {named['triples']} triples,"
          f" eligible {named['eligible']}")
    for desc, shapes in sweep_shapes():
        for label, E in shapes:
            comb_row(E, label, tally)
    print(f"   + systematic sweep: totals below")
    print(f"\nCOMB OK: {tally['triples']} triples;"
          f" {tally['l5']} carry a length-5 branch of H/P"
          f" (+{tally['trivial']} trivial theta(3,4,5) triples,"
          f" {tally['no_l5']} with no length-5 branch);"
          f" the (ANH-12) construction is combinatorially available at"
          f" {tally['eligible']} of the {tally['l5']}"
          f" ({tally['cycle_blocked']} blocked: no suitable disjoint"
          " 6-cycle/labeling).  Availability != success: the two linear"
          " solves and the guards are geometric, measured in --bad.")


# ---------------- mode: validate ---------------------------------------------

def mode_validate():
    print("== (shrink-val) the machinery ==")
    # (1) hp_edge_rows agrees with the canonical contracted_edges
    for name, E, v in habitats4()[:2]:
        d = prepared(E, v, 1)[0]
        rows = hp_edge_rows(d['Hed'], d['Pverts'], d['Pset'])
        assert [(u, w) for (j, u, w, x, y) in rows] == \
            contracted_edges(d['Hed'], d['Pverts'], d['Pset']), \
            "hp_edge_rows disagrees with contracted_edges"
    print("   (1) hp_edge_rows == contracted_edges at 2 habitats")
    # (2) the trivial theta(3,4,5) case
    name, E, v = habitats4()[0]
    assert name.startswith('theta(3,4,5)')
    d = prepared(E, v, 1)[0]
    rows = hp_edge_rows(d['Hed'], d['Pverts'], d['Pset'])
    assert len(rows) == 5 and branch_lengths(
        [(r[1], r[2]) for r in rows]) == [5]
    print("   (2) theta(3,4,5): H/P the bare 5-cycle, H/P - beta empty --"
          " (ANH-R1) trivially true at every chart point there")
    # (3) census machinery reproduces the annih --supp verdict at two
    #     habitats: dim 1, full support, branch cross-check both ways
    for name, E, v in habitats4()[:2]:
        d = prepared(E, v, 1)[0]
        dimS, branches, zeros, taus = branch_report(d)
        assert dimS == 1 and not zeros, f"{name}: annih --supp disagrees"
        for path in branches[:2]:
            bset = branch_edge_ix(d['Hed'], path)
            assert stress_dim_without(d['Hed'], d['VH'], d['placed'],
                                      d['Pset'], bset) == 0
    print("   (3) census machinery reproduces annih --supp at 2 habitats"
          " (dim S_pen = 1, every branch stressed, reduced rebuilds"
          " independent)")
    # (4) plane_functional is the determinant, exactly
    A0h, A3h, ph = hat([F(1), F(0), F(0)]), hat([F(0), F(1), F(0)]), \
        hat([F(0), F(0), F(1)])
    n, c = plane_functional(A0h, A3h, ph)
    for x in ([F(2), F(3), F(5)], [F(-1), F(7), F(1, 2)]):
        assert dot(n, x) + c == det4([A0h, A3h, ph, hat(x)])
    sols = solve_on_moves(n, c, [F(2), F(3), F(5)],
                          [[F(1), F(0), F(0)], [F(0), F(1), F(0)]])
    for x in sols:
        assert dot(n, x) + c == 0
    print("   (4) plane_functional == det4 and solve_on_moves lands on the"
          " plane, exactly")
    # (5) the common-transversal fact on synthetic data: six lines through
    #     six distinct points of the z-axis, generic directions: all meet L,
    #     the six Klein forms vanish, the stars have rank 5, and C(L) spans
    #     the co-kernel
    from repin import hodge_star
    Lp, Lq = [F(0), F(0), F(0)], [F(0), F(0), F(1)]
    CLs = wedge2(hat(Lp), hat(Lq))
    qs = [[F(1), F(2), F(3)], [F(2), F(-1), F(5)], [F(-3), F(1), F(1)],
          [F(1), F(1), F(-2)], [F(5), F(3), F(2)], [F(-2), F(7), F(1)]]
    lines = [wedge2(hat([F(0), F(0), F(i)]),
                    hat([qs[i][0], qs[i][1], F(i) + qs[i][2]]))
             for i in range(6)]
    assert all(klein(CLs, C) == 0 for C in lines)
    stars = [hodge_star(C) for C in lines]
    assert rank(stars) == 5
    ker = nullspace(stars)
    assert len(ker) == 1 and rank([ker[0], CLs]) == 1
    print("   (5) six lines meeting a common line lie in its special linear"
          " complex: rank 5, co-kernel = <C(L)>")
    # (6) the cycle finder: NT21's H/P has girth-6 cycles found, all simple
    name, E, v = habitats4()[1]
    d = prepared(E, v, 1)[0]
    rows = hp_edge_rows(d['Hed'], d['Pverts'], d['Pset'])
    g = girth([(r[1], r[2]) for r in rows])
    cyc = hp_six_cycles(rows, cap=50)
    for es, bodies in cyc:
        assert len({r[0] for r in es}) == 6 and len(set(bodies)) == 6
    assert (g == 6) == bool(cyc), "6-cycle finder disagrees with girth"
    print(f"   (6) cycle finder: girth(H/P) = {g} at {name},"
          f" {len(cyc)} simple 6-cycles, all verified simple")
    print("\nVAL OK: contraction bookkeeping, the trivial case, the census"
          " cross-machinery, the exact linear solver, the special-complex"
          " fact and the cycle finder all check exactly.")


# ---------------- main --------------------------------------------------------

def main():
    modes = {'--census': mode_census, '--bad': mode_bad,
             '--comb': mode_comb, '--validate': mode_validate}
    args = [a for a in sys.argv[1:] if a in modes]
    if not args:
        print(__doc__)
        return
    for a in args:
        modes[a]()
        print()


if __name__ == '__main__':
    main()
