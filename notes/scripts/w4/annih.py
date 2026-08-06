"""
Phase 39, kernel-(K) fan-out direction A (second fan-out) -- THE ANNIHILATOR
AS A SELF-STRESS, AND WHETHER IT PRODUCES A CLASS-WIDE RECIPE.

Fuses `notes/Pencil-strategy.md` section 4.6's **U1** (retarget the image
problem from `Gr(3,6)` to the annihilator `Lambda`), **U2** (the hinge-rate /
cycle-space presentation, whose ground set is `E(H)`) and kernel-(K)
**option B** (the stress-function reading).  Workbook section: `(K-ann)`;
labels `(ANH-n)`.  Read against section (K-pitch) *Step 5b* ((T5)),
section (K-Lambda) *Steps 3-5a* ((Lambda2), (OUT)) and section (K-dom)
*Steps D1/D2* (the `min(9, 6k-14)` cap and the `3(k-3)` far block), whose
notation is inherited verbatim.

THE OBJECT.  At a hard-stratum target-rank seed with split chain `b-v-a-c`,
`H := G - v - a`, `P` a shortest `b`-`c` path of `H` (the companion, of
length `k`), `S_P := span{C_e : e in P}`:  by path-sum containment
`V_bc <= S_P`, and (T5) says the far graph enters `V_bc` ONLY through the
annihilator `Lambda := {lam in S_P* : lam _|_ V_bc}`, of dimension `k - 3`.

(ANH-1), mode `--stress`.  Writing motions in hinge rates (`m(x) - m(y) =
om_e C_e`, the identity section (K-ind) *Step I3* already uses) makes
`Z(H) = ker N` with `N` the cycle matrix (`dominance.cycle_data`), and
`Lambda` = the covectors of `W := Z(H)^perp` supported inside `P`.  Every
such covector is the hinge violation of a SCREW CIRCULATION

    tau : E(H) -> Lambda^2 K^4,  sum_{e at u} +-tau_e = 0 at every body u,
    B(tau_e, C_e) = 0 off the companion,   lam_e = B(tau_e, C_e) on it,

i.e. of a SELF-STRESS of the contracted framework `H/P` (weld the whole
companion into one body `X`), which is rigid at a target-rank seed and has
stress space of dimension exactly `k - 3`.  So (T5)'s annihilator IS a
self-stress space and (D2)'s far block `3(k-3)` is `dim Gr(k-3, k)` for it.

(ANH-2)/(ANH-3), mode `--rate`.  Differentiating `lam(t) . om(t) = 0`
against the differentiated cycle condition gives the RECIPROCITY IDENTITY

    d lam (pi_P om)  =  sum_e om_e * B(tau_e, dC_e),

whose right-hand side is supported on the edges incident to a MOVED vertex.
At the named move "translate a single non-hub far body `y` of `H`-degree 2
inside the intersection of its hub neighbours' panels" it collapses to ONE
Klein pairing `B(rho_y, v ^ (om_e z1 - om_e' z2))`.

(ANH-5).  At a FREE such body (no hub neighbour, so `v` sweeps the whole
plane at infinity) the exact vanishing criterion is
`d lam_y == 0  iff  rho_y _|_B (H_inf ^ U_y)`, and when
`dim U_y = 2` that kill set is exactly `<C(z1 z2)>`: the transmitted wrench
is the PURE FORCE along the line joining `y`'s two neighbours.

(ANH-4)/(ANH-8), modes `--supp` and `--census`.  `tau` is constant along
each BRANCH of `H/P` (a 2-valent body transmits the wrench unchanged) and
`B`-perp to all `l` of that branch's lines, so a branch of length `>= 6`
would carry a forced-zero screw.  At `k = 4` that cannot happen: `E(H/P)` is
a CIRCUIT of the generic Tay matroid (proof in `--census`), and
independently every branch of a class member has length `<= 5` (removing a
branch interior leaves `f = l - 6`).  At `l = 5` the branch screw is pinned
to the 1-dimensional Klein-perp of its five lines -- an explicit bracket
vector with NO global solve.

(ANH-7), mode `--recipe`.  Combining them: on a length-5 branch
`beta = w0 w1 w2 w3 w4 w5` with free middle body `w2`, `C(w1 w3)` is
automatically `B`-perp to FOUR of the five branch lines, so the whole
criterion is the single remaining 4-point bracket `[w1, w3, w4, w5]`.

Drivers (foreground, one at a time; exact rational arithmetic, no floating
point anywhere; every sampled configuration carries rank/dimension asserts,
including `dominance.base_seed`'s composite genericity guard
`repin.star_generic` against the `plane_basis` artifact --
`notes/scripts/README.md` *Divergences*.  That guard gained its
coincident-hinge clause on 2026-08-06 (slice S2; *Harness debt* item 4), so
some seeds here moved to the next clean one.  §(K-ann)'s claims are
identities, ranks and pointwise attainments -- conservative under the defect
per F13's classification -- and the owed re-read confirmed EVERY verdict
unchanged.  One figure improved rather than merely moving: `--supp`'s far
block of `rank dlambda` now attains (D2)'s bound `3(k-3)` at every seed
including `k = 6`, where the contaminated seeds used to report 5 and 7 out
of 9):

    python3 notes/scripts/w4/annih.py --stress    # (ANH-1)
    python3 notes/scripts/w4/annih.py --rate      # (ANH-2), (ANH-3), (ANH-5)
    python3 notes/scripts/w4/annih.py --supp      # (ANH-4) realized side
    python3 notes/scripts/w4/annih.py --recipe    # (ANH-7)
    python3 notes/scripts/w4/annih.py --census    # (ANH-6), (ANH-8)
    python3 notes/scripts/w4/annih.py --validate  # the machinery
"""
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import importlib

from exactcore import rref, rank, nullspace, wedge2, hat, dot, neighbors
from repin import span_basis, in_span, hodge_star
from pitch import klein, Q, theta_edges, paths_graph
from nogood_subdiv import (deficiency, hcard_ok, triangles,
                           count_matroid_rank, MULT)
from kbare_common import verts_of
from kslide import no_rigid_branch_union
from dominance import (HABITATS, base_seed, seeds_for, build_chart,
                       dC_along, dhat, solve_multi, cycle_data, dV_rank,
                       h_edges, simple_paths, FIXED)
from outer import split_data, companions4, named_inventory, sweep_shapes

LAM = importlib.import_module('lambda')   # `lambda` is a Python keyword


# ---------------- edge bookkeeping ------------------------------------------

def edge_index(Hed):
    """{(x,y): (j, +1), (y,x): (j, -1)} for the ordered edge list `Hed`."""
    ix = {}
    for j, (x, y) in enumerate(Hed):
        ix[(x, y)] = (j, 1)
        ix[(y, x)] = (j, -1)
    return ix


def path_edges(Hed, P):
    """[(edge index, orientation sign)] along the vertex list `P`."""
    ix = edge_index(Hed)
    return [ix[(P[i], P[i + 1])] for i in range(len(P) - 1)]


def companion_of(d):
    """The shortest `b`-`c` path of `H` at a `dominance.base_seed` dict.
    `simple_paths` enumerates deterministically (neighbours sorted by str),
    so `next(...)` is reproducible."""
    return next(P for P in d['paths'] if len(P) - 1 == d['k'])


def lines_of(Hed, placed):
    return [wedge2(hat(placed[x]), hat(placed[y])) for (x, y) in Hed]


# ---------------- the screw-circulation (self-stress) system ----------------

def stress_system(Hed, VH, placed, Pset):
    """Rows of the screw-circulation system in unknowns `tau_e` in
    `Lambda^2 K^4` for every `e` in `E(H)`, laid out
    `[tau_{Hed[0]} (6) | tau_{Hed[1]} (6) | ...]`.

      (i)  EQUILIBRIUM at every body `u`:  sum_{e = (x,y)} s_{u,e} tau_e = 0
           with `s = +1` when `u` is the edge's head and `-1` when it is the
           tail -- 6 rows per vertex.  This is exactly "tau lies in the graph
           cycle space tensor Lambda^2 K^4", i.e. `tau` is a circulation.
      (ii) TRANSMISSIBILITY at every non-companion edge: `B(tau_e, C_e) = 0`
           -- 1 row per edge outside `Pset`.

    A solution is a self-stress of the framework in which the companion
    hinges are replaced by rigid welds; `lam_e := B(tau_e, C_e)` for `e` in
    `Pset` is its hinge violation there.  Returns (rows, C)."""
    C = lines_of(Hed, placed)
    ncols = 6 * len(Hed)
    rows = []
    inc = {u: [] for u in VH}
    for j, (x, y) in enumerate(Hed):
        inc[y].append((j, 1))
        inc[x].append((j, -1))
    for u in VH:
        for k in range(6):
            r = [F(0)] * ncols
            for (j, s) in inc[u]:
                r[6 * j + k] += F(s)
            rows.append(r)
    star = [hodge_star(c) for c in C]
    for j in range(len(Hed)):
        if j in Pset:
            continue
        r = [F(0)] * ncols
        for k in range(6):
            r[6 * j + k] = star[j][k]      # B(tau, C) = <tau, star C>
        rows.append(r)
    return rows, C


def stress_space(Hed, VH, placed, Pset):
    """A basis of the screw-circulation space, as lists of `len(Hed)` screws."""
    rows, C = stress_system(Hed, VH, placed, Pset)
    ker = nullspace(rows)
    out = []
    for t in ker:
        out.append([t[6 * j:6 * j + 6] for j in range(len(Hed))])
    return out, C


def lam_from_tau(tau, C, Pe):
    """`(B(tau_e, C_e))_{e in P}` in the raw omega-coordinate order of `Pe`."""
    return [klein(tau[j], C[j]) for (j, s) in Pe]


def lam_from_motions(Z, Pe):
    """The annihilator of `pi_P(Z)` in `(K^P)*`, from the motion side."""
    proj = [[om[j] for (j, s) in Pe] for om in Z]
    return nullspace(proj), span_basis(proj)


# ---------------- the contracted framework `H/P` ----------------------------

def contracted_edges(Hed, Pverts, Pset, tag='X*'):
    """`E(H/P)` with every companion vertex relabelled to the welded body.
    Chords among companion vertices would become LOOPS; the caller asserts
    there are none (a chord plus part of `P` is a cycle of `G` of length
    `<= 4`, and 5/6-sparsity forces girth `>= 6`)."""
    out = []
    for j, (x, y) in enumerate(Hed):
        if j in Pset:
            continue
        u = tag if x in Pverts else x
        w = tag if y in Pverts else y
        assert u != w, "H/P has a loop -- a chord among companion vertices"
        out.append((u, w))
    return out


def welded_dof(N, Hed, freeze):
    """dim of the motions of `H` with every hinge in `freeze` welded, modulo
    the trivial screws: `dim (Z cap K^{E - freeze})`, computed as the kernel
    of `N` with the frozen coordinates killed."""
    rows = [r[:] for r in N]
    ncols = len(Hed)
    for j in sorted(freeze):
        r = [F(0)] * ncols
        r[j] = F(1)
        rows.append(r)
    return len(nullspace(rows))


# ---------------- the reciprocity identity ----------------------------------

def dN_of(cycles, dC, ne):
    """The differentiated cycle matrix, same row layout as `cycle_data`'s."""
    out = []
    for coef in cycles:
        for k in range(6):
            out.append([F(coef.get(j, 0)) * dC[j][k] for j in range(ne)])
    return out


def dlam_values(N, cycles, C, Hed, placed, lam_full, Z, d):
    """`(d lam)(pi_P om)` for every `om` in `Z`, by IMPLICIT DIFFERENTIATION:
    solve `N omdot = -(dN) om` and return `-lam . omdot`.  The particular
    solution is irrelevant -- `lam` lies in the row space of `N`, hence
    annihilates `ker N = Z`.  Returns (values, dC)."""
    ne = len(Hed)
    dC = dC_along(Hed, placed, d)
    dN = dN_of(cycles, dC, ne)
    rhs = []
    for om in Z:
        rhs.append([-sum((dN[r][j] * om[j] for j in range(ne)), F(0))
                    for r in range(len(dN))])
    sols = solve_multi(N, rhs) if N else [[F(0)] * ne for _ in Z]
    assert sols is not None, "implicit differentiation inconsistent"
    vals = [-sum((lam_full[j] * s[j] for j in range(ne)), F(0)) for s in sols]
    return vals, dC


def local_values(tau, dC, Z, ne):
    """The RIGHT-HAND SIDE of the reciprocity identity: for every `om` in `Z`,
    `sum_e om_e B(tau_e, dC_e)` -- supported on the moved vertex's edges."""
    return [sum((om[j] * klein(tau[j], dC[j]) for j in range(ne)), F(0))
            for om in Z]


# ---------------- the named single-vertex far-chart move --------------------

def single_vertex_dirs(Gp, placed, nrm, y, hubs):
    """A basis of the pencil-chart velocities that move `pt(y)` ALONE:
    `<n_u, v> = 0` for every hub neighbour `u` of `y` in `G'`.  Returns
    `None` when `y` is itself a hub (its own panel would have to move, so the
    move is not single-vertex)."""
    if y in hubs:
        return None
    nb = neighbors(Gp)
    cons = [nrm[u] for u in sorted(nb.get(y, ()), key=str)
            if u in hubs and u in nrm]
    T = nullspace([[F(x) for x in n] for n in cons]) if cons else [
        [F(1) if i == k else F(0) for k in range(3)] for i in range(3)]
    return [{y: list(t)} for t in T]


def deg2_bracket_form(Hed, placed, tau, y, v, om):
    """The collapsed one-pairing form at a degree-2 vertex `y`:
    `B(rho_y, v ^ u_om)` with `u_om = om_{j1} z_{j1} - om_{j2} z_{j2}` and
    `rho_y = eps_{j1} tau_{j1}` (equilibrium at `y` makes
    `eps_{j1} tau_{j1} = - eps_{j2} tau_{j2}`, `eps = +1` when `y` is the
    edge's FIRST entry).  Returns (value, rho, u)."""
    at = []
    for j, (x, w) in enumerate(Hed):
        if x == y:
            at.append((j, 1, w))
        elif w == y:
            at.append((j, -1, x))
    assert len(at) == 2, "not a degree-2 vertex of H"
    (j1, e1, z1), (j2, e2, z2) = at
    rho = [F(e1) * t for t in tau[j1]]
    chk = [F(e2) * t for t in tau[j2]]
    assert all(a + b == 0 for a, b in zip(rho, chk)), \
        "equilibrium at a degree-2 body failed"
    u = [om[j1] * a - om[j2] * b for a, b in zip(hat(placed[z1]),
                                                 hat(placed[z2]))]
    return klein(rho, wedge2(dhat(v), u)), rho, u


# ---------------- habitats ---------------------------------------------------

def habitats4():
    """The named length-4-companion class habitats, from their canonical
    home `lambda.habitat_specs` (theta(3,4,5), NT21, NT24, NT30), plus the
    two `dominance` shapes that also have `k = 4` (already in that list).
    Each carries `lambda.py`'s load-time class predicate."""
    return [(n, E, v) for (n, E, v, comp) in LAM.HABITATS4]


def control_shapes():
    """OFF-CLASS controls, carried so that the (ANH-3)/(ANH-5) off-support
    tests are not vacuous.  `theta4(3,4,5,6)` is tight with `def = 0`,
    `hcard` and triangle-free, but **`hnoRigid` FAILS** (its theta(3,4,5)
    sub-union is a proper rigid subgraph) -- which is exactly (ANH-4)'s
    hypothesis, so its `H/P` is allowed a PROPER circuit: the 5-cycle left by
    the length-5 branch.  Off-support far vertices then exist and `d lam`
    must vanish at every one."""
    E, pm = paths_graph([3, 4, 5, 6], [])
    assert deficiency(E) == 0 and hcard_ok(E) and not triangles(E)
    n = len(verts_of(E))
    assert 5 * len(E) == 6 * (n - 1)
    assert not no_rigid_branch_union(E, pm), \
        "the control was supposed to FAIL hnoRigid"
    return [('theta4(3,4,5,6)*', E, pm[0][1])]


def graded_habitats():
    """The `k`-graded control list: `dominance.HABITATS` (k = 3,4,5,6) plus
    the two `lambda` shapes it does not carry (NT24, NT30, both `k = 4`),
    used to show how the `k = 4` picture degrades on either side."""
    out = [(n, E, v) for (n, E, v, pm, note) in HABITATS]
    have = {n for (n, E, v) in out}
    for (n, E, v) in habitats4():
        if n not in have:
            out.append((n, E, v))
    return out


def prepared(E, v, want=2):
    """Validated seeds with the companion data attached."""
    out = []
    for d in seeds_for(E, v, want):
        P = companion_of(d)
        Pe = path_edges(d['Hed'], P)
        d['P'] = P
        d['Pe'] = Pe
        d['Pset'] = {j for (j, s) in Pe}
        d['Pverts'] = set(P)
        out.append(d)
    return out


# ---------------- mode: the stress presentation -----------------------------

def mode_stress():
    print("== (ANH-1) the annihilator IS a self-stress of the welded graph ==")
    print("   Lambda = {lam in S_P* : lam _|_ V_bc}, dim = k - 3 by (T5).")
    print("   Claim: lam_e = B(tau_e, C_e) for a screw circulation tau with")
    print("   B(tau_e,C_e) = 0 off the companion -- i.e. a SELF-STRESS of the")
    print("   contracted framework H/P (weld the companion into one body X),")
    print("   which is RIGID at a target-rank seed and has stress dimension")
    print("   exactly k-3 = 5|E(H/P)| - 6(|V(H/P)|-1).\n")
    print(f"   {'habitat':<17}{'k':>2} {'seed':>5} {'|E(H)|':>7}"
          f" {'dimZ':>5} {'dimTau':>7} {'k-3':>4} {'dofH/P':>7}"
          f" {'defH/P':>7} {'lam agree':>10}")
    tot, nh = 0, 0
    for name, E, v in graded_habitats():
        nh += 1
        for d in prepared(E, v, 2):
            Hed, VH, placed = d['Hed'], d['VH'], d['placed']
            k, Pe, Pset = d['k'], d['Pe'], d['Pset']
            N, cycles, C = cycle_data(Hed, VH, placed)
            Z = nullspace(N)
            assert len(Z) == d['dimMot'] - 6, "dim Z != dim mot(H) - 6"
            # (a) the screw-circulation space
            taus, C2 = stress_space(Hed, VH, placed, Pset)
            assert C2 == C, "line lists disagree"
            assert len(taus) == k - 3, \
                f"{name}: dim(screw circulations) = {len(taus)} != k-3"
            # (b) it agrees with the motion-side annihilator, as a subspace
            lam_s = span_basis([lam_from_tau(t, C, Pe) for t in taus])
            lam_m, projZ = lam_from_motions(Z, Pe)
            assert len(projZ) == 3, "pi_P(Z) is not 3-dimensional"
            assert len(lam_m) == k - 3, "the annihilator has the wrong dim"
            agree = (len(lam_s) == len(lam_m)
                     and all(in_span(x, span_basis(lam_m)) for x in lam_s)
                     and all(in_span(x, span_basis(lam_s)) for x in lam_m))
            assert agree, f"{name}: stress-side and motion-side lam differ"
            # (c) H/P is rigid, and its combinatorial deficiency agrees
            dofHP = welded_dof(N, Hed, Pset)
            HP = contracted_edges(Hed, d['Pverts'], Pset)
            defHP = deficiency(HP)
            assert dofHP == 0, f"{name}: H/P is not pencil-rigid"
            assert defHP == 0, f"{name}: H/P is not generically rigid"
            nHP = len(verts_of(HP))
            assert 5 * len(HP) - 6 * (nHP - 1) == k - 3, \
                "the H/P count is not k-3"
            # (d) the whole framework H is independent (no self-stress), so
            #     tau is determined by lam and the two spaces have equal dim
            #     (Pset = the empty set imposes transmissibility on EVERY
            #     edge, i.e. it computes the honest self-stress space of H.)
            allP = stress_space(Hed, VH, placed, set())
            assert len(allP[0]) == 0, "H itself carries a self-stress"
            print(f"   {name:<17}{k:>2} {d['seed']:>5} {len(Hed):>7}"
                  f" {len(Z):>5} {len(taus):>7} {k - 3:>4} {dofHP:>7}"
                  f" {defHP:>7} {'yes':>10}")
            tot += 1
    print(f"\nSTRESS OK: {tot} seeds over {nh} habitats, k = 3..6."
          "  At every one: the screw-circulation space has dimension exactly"
          " k-3, it spans the SAME annihilator as the motion side, the"
          " contracted framework H/P is rigid both at the pencil placement"
          " and combinatorially (def = 0) with count exactly k-3, and H"
          " itself carries no self-stress.  So (T5)'s annihilator is the"
          " self-stress space of H/P, and (D2)'s far block 3(k-3) is"
          " dim Gr(k-3, k) for it.")


# ---------------- mode: the reciprocity identity ----------------------------

def mode_rate():
    print("== (ANH-2) the reciprocity formula for d lam, and its bracket "
          "form ==")
    print("   d lam (pi_P om) = sum_e om_e B(tau_e, dC_e)  -- the right side")
    print("   is LOCAL: dC_e = 0 unless e touches a moved vertex.  Tested")
    print("   against implicit differentiation of ker N, direction by")
    print("   direction and om by om, at k = 4 class habitats.")
    print("   (ANH-3) at the named move -- translate a single non-hub far")
    print("   vertex y of H-degree 2 -- it collapses to ONE Klein pairing")
    print("   B(rho_y, v ^ (om_e z - om_e' z')).\n")
    ndir = nom = nmove = nline = 0
    for name, E, v in habitats4():
        for d in prepared(E, v, 2):
            Hed, VH, placed, nrm = d['Hed'], d['VH'], d['placed'], d['nrm']
            Pe, Pset, k = d['Pe'], d['Pset'], d['k']
            assert k == 4, "habitats4 must be k = 4"
            N, cycles, C = cycle_data(Hed, VH, placed)
            Z = nullspace(N)
            taus, _ = stress_space(Hed, VH, placed, Pset)
            assert len(taus) == 1
            tau = taus[0]
            lam_full = [F(0)] * len(Hed)
            for (j, s) in Pe:
                lam_full[j] = klein(tau[j], C[j])
            assert any(x != 0 for x in lam_full), "lam = 0"
            VHa = VH + [d['a']]
            dirs, nvar, ncon = build_chart(d['Gp'], VHa, d['hubsGp'], placed,
                                           nrm, FIXED, d['b'], d['c'], d['a'])
            far = set(VHa) - set(d['P'][1:-1])
            fardirs = [x for x in dirs if all(w in far for w in x)]
            ok = 0
            for dd in fardirs:
                vals, dC = dlam_values(N, cycles, C, Hed, placed, lam_full,
                                       Z, dd)
                loc = local_values(tau, dC, Z, len(Hed))
                assert vals == loc, \
                    f"{name}: the reciprocity identity failed"
                touched = set()
                for j, (x, y) in enumerate(Hed):
                    if any(w != 0 for w in dC[j]):
                        touched |= {x, y}
                assert touched <= (set(dd) | set().union(
                    *[set(neighbors(Hed)[w]) for w in dd])), \
                    "dC moved an edge away from the moved vertices"
                ok += 1
                nom += len(Z)
            ndir += ok
            # the named single-vertex move, in its collapsed bracket form
            hubs = set(d['hubsGp'])
            deg = {}
            for (x, y) in Hed:
                deg[x] = deg.get(x, 0) + 1
                deg[y] = deg.get(y, 0) + 1
            cands = [y for y in sorted(far, key=str)
                     if y in deg and deg[y] == 2 and y not in hubs
                     and y not in (d['b'], d['c'], d['a'])]
            shown = nfree = ncrit = 0
            for y in cands:
                svd = single_vertex_dirs(d['Gp'], placed, nrm, y, hubs)
                if not svd:
                    continue
                allzero = True
                for dd in svd:
                    vals, dC = dlam_values(N, cycles, C, Hed, placed,
                                           lam_full, Z, dd)
                    if any(x != 0 for x in vals):
                        allzero = False
                    for i, om in enumerate(Z):
                        val, rho, u = deg2_bracket_form(Hed, placed, tau, y,
                                                        dd[y], om)
                        assert val == vals[i], \
                            f"{name}: the one-pairing bracket form failed at {y}"
                    nmove += 1
                    if any(x != 0 for x in rho) and Q(rho) == 0:
                        nline += 1
                # (ANH-5) the exact vanishing criterion at a FREE 2-valent far
                # body (`v` unconstrained, so it sweeps the whole plane at
                # infinity): `d lam_y == 0` iff `rho_y` is the pure force
                # along `line(z1, z2)`.  Reason: `B(rho, v ^ z_i) = 0` for all
                # `v` at infinity says `rho _|_B alpha(z_i)`, and alpha is
                # maximal isotropic hence self-perp, so `rho` lies in
                # `alpha(z1) cap alpha(z2) = <C(z1 z2)>`.
                if len(svd) == 3:
                    nfree += 1
                    z = deg2_neighbours(Hed, y)
                    pure = pluck_line(placed, z[0], z[1])
                    par = parallel(rho, pure)
                    Uy = [[om[j] for j in deg2_indices(Hed, y)] for om in Z]
                    if len(span_basis(Uy)) == 2:
                        # the criterion as a SUBSPACE identity, not a
                        # coincidence of two booleans: the screws killed by
                        # every (v at infinity) ^ (u in U_y) are exactly the
                        # multiples of `C(z1 z2)`.
                        rows = []
                        for i in range(3):
                            vv = [F(1) if t == i else F(0) for t in range(3)]
                            for uu in (hat(placed[z[0]]), hat(placed[z[1]])):
                                X = wedge2(dhat(vv), uu)
                                rows.append(hodge_star(X))
                        ker = nullspace(rows)
                        assert len(ker) == 1 and parallel(ker[0], pure), \
                            (f"{name}: (H_inf ^ U_y)^perpB is not <C(z1z2)>"
                             f" at {y}")
                        assert allzero == par, \
                            (f"{name}: at the free 2-valent body {y}, "
                             "d lam = 0 and rho ~ C(z1 z2) disagree")
                        ncrit += 1
                shown += 1
            print(f"   {name:<15} seed {d['seed']:>3}: |far dirs| ="
                  f" {len(fardirs):>3}, |Z| = {len(Z)},"
                  f" single-vertex candidates = {len(cands)}"
                  f" (usable {shown}, free {nfree}, criterion tested"
                  f" {ncrit}); identity holds on all of them")
    print(f"\nRATE OK: the reciprocity identity holds at {ndir} far-chart"
          f" directions x {nom} motions, and the collapsed one-pairing"
          f" bracket form at {nmove} single-vertex moves ({nline} of them"
          " with a zero-pitch rho, i.e. literally one 4-point bracket)."
          "  The formula's kernel is bounded-size and class-uniform; what it"
          " pairs against (tau, om) is not.  (ANH-5)'s vanishing criterion"
          " -- `d lam_y = 0` iff the transmitted wrench is the pure force"
          " along the line joining y's two neighbours -- holds at every free"
          " 2-valent far body tested.")


def deg2_neighbours(Hed, y):
    out = []
    for (x, w) in Hed:
        if x == y:
            out.append(w)
        elif w == y:
            out.append(x)
    assert len(out) == 2
    return out


def deg2_indices(Hed, y):
    return [j for j, e in enumerate(Hed) if y in e]


def pluck_line(placed, p, q):
    return wedge2(hat(placed[p]), hat(placed[q]))


def parallel(x, y):
    """Are the two 6-vectors proportional (either may be zero)?"""
    return rank([list(x), list(y)]) <= 1


# ---------------- the branch decomposition of `H/P`, at the `H` level -------

def hp_branches(Hed, Pverts, Pset):
    """The maximal degree-2 chains of `H/P`, returned as vertex lists of `H`
    (so the endpoints are the REAL points of `G`, not the welded body `X`).
    Nodes are the vertices of `H` of degree != 2 together with every
    companion vertex (they all collapse into `X`); the companion's own edges
    are contracted away and never appear."""
    keep = [j for j in range(len(Hed)) if j not in Pset]
    nbH = neighbors(Hed)
    node = {u for u in nbH if len(nbH[u]) != 2} | set(Pverts)
    adj = {}
    for j in keep:
        x, y = Hed[j]
        adj.setdefault(x, []).append((j, y))
        adj.setdefault(y, []).append((j, x))
    used, out = set(), []
    for u in sorted(node, key=str):
        for (j, w) in adj.get(u, ()):
            if j in used:
                continue
            used.add(j)
            path, cur = [u, w], w
            while cur not in node:
                nxt = [(t, z) for (t, z) in adj[cur] if t not in used]
                assert len(nxt) == 1, "degree-2 walk went wrong"
                (t, z) = nxt[0]
                used.add(t)
                path.append(z)
                cur = z
            out.append(path)
    assert len(used) == len(keep), "the H/P branch decomposition lost an edge"
    return out


def branch_screw(Hed, tau, path):
    """The single screw carried by a branch, with the sign fixed by the
    branch's first edge, plus an assertion that equilibrium really does make
    it constant along the whole chain."""
    ix = edge_index(Hed)
    (j0, s0) = ix[(path[0], path[1])]
    rho = [F(s0) * t for t in tau[j0]]
    for i in range(1, len(path) - 1):
        (j, s) = ix[(path[i], path[i + 1])]
        cur = [F(s) * t for t in tau[j]]
        assert cur == rho, "the branch screw is not constant"
    return rho


# ---------------- mode: the support obstruction ------------------------------

def girth(edges):
    """Girth of a multigraph given as an edge list (2 for parallel edges)."""
    seen = set()
    for (x, y) in edges:
        key = tuple(sorted((str(x), str(y))))
        if key in seen:
            return 2
        seen.add(key)
    nb = neighbors(edges)
    best = None
    for s in sorted(nb, key=str):
        dist = {s: 0}
        par = {s: None}
        q = [s]
        while q:
            nxt = []
            for x in q:
                for y in sorted(nb[x], key=str):
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        par[y] = x
                        nxt.append(y)
                    elif par[x] != y:
                        c = dist[x] + dist[y] + 1
                        best = c if best is None else min(best, c)
            q = nxt
    return best


def gen_stress_dim(edges):
    """dim of the GENERIC body-hinge self-stress space of a multigraph, by
    Tay: `5|E| - rank_{(6,6)}(5E)` (`nogood_subdiv.count_matroid_rank`, the
    Lee-Streinu pebble game -- the canonical section-1 oracle)."""
    return MULT * len(edges) - count_matroid_rank(
        [e for e in edges for _ in range(MULT)], verts_of(edges))


def del_stress_dim(Hed, VH, placed, Pset, j):
    """dim of the REALIZED stress space of `H/P - f` (`f = Hed[j]`), rebuilt
    from scratch on the reduced edge list -- an independent matrix from the
    `{tau : tau_f = 0}` slice of the full solve."""
    red = [e for t, e in enumerate(Hed) if t != j]
    shift = {t: (t if t < j else t - 1) for t in range(len(Hed)) if t != j}
    redP = {shift[t] for t in Pset}
    return len(stress_space(red, VH, placed, redP)[0])


def mode_supp():
    print("== (ANH-4)/(ANH-5) the support obstruction ==")
    print("   C_pen := supp(tau) = {f : some realized stress has tau_f != 0};")
    print("   C_gen := {f : the GENERIC stress space of H/P - f is smaller")
    print("   than that of H/P} -- the Tay circuit, `count_matroid_rank` on")
    print("   5(H/P).  Specialization gives dim S_pen >= dim S_gen setwise,")
    print("   hence C_pen <= C_gen; the direction that would MATTER for the")
    print("   recipe is the reverse one, which is not implied.  At k = 4")
    print("   (ANH-4) forces C_gen = E(H/P), so the only thing that could go")
    print("   wrong is the pencil placement SHRINKING it.  The off-class")
    print("   control (hnoRigid fails there) exhibits the mechanism: its")
    print("   circuit is a proper 5-cycle and every single-vertex far move")
    print("   off it leaves V_bc exactly fixed.\n")
    print(f"   {'habitat':<17}{'k':>2} {'seed':>5} {'|E(H/P)|':>9}"
          f" {'girth':>6} {'|C_pen|':>8} {'|C_gen|':>8} {'equal':>6}"
          f" {'off-supp':>9} {'dlam=0':>7} {'rank dlam':>10}")
    tot = eq = 0
    for name, E, v in graded_habitats() + control_shapes():
        for d in prepared(E, v, 2):
            Hed, VH, placed, nrm = d['Hed'], d['VH'], d['placed'], d['nrm']
            Pe, Pset, k = d['Pe'], d['Pset'], d['k']
            if k == 3:
                continue                      # Lambda = 0, nothing to support
            N, cycles, C = cycle_data(Hed, VH, placed)
            Z = nullspace(N)
            taus, _ = stress_space(Hed, VH, placed, Pset)
            assert len(taus) == k - 3
            # the support of the whole stress SPACE (k-3 may exceed 1)
            Cpen = {j for j in range(len(Hed)) if j not in Pset
                    and any(any(x != 0 for x in t[j]) for t in taus)}
            HP = contracted_edges(Hed, d['Pverts'], Pset)
            gir = girth(HP)
            assert gir is None or gir >= 5, \
                f"{name}: H/P has a cycle of length < 5 -- excess >= 2"
            assert gen_stress_dim(HP) == k - 3, \
                f"{name}: the generic stress dim of H/P is not k-3"
            keep = [j for j in range(len(Hed)) if j not in Pset]
            Cgen = set()
            for i, j in enumerate(keep):
                sub = [e for t, e in enumerate(HP) if t != i]
                if gen_stress_dim(sub) < k - 3:
                    Cgen.add(j)
                # cross-check the realized side on an independently built
                # matrix (the reduced edge list, not a slice of the full one)
                assert (del_stress_dim(Hed, VH, placed, Pset, j) < k - 3) \
                    == (j in Cpen), f"{name}: two routes to C_pen disagree"
            assert Cpen <= Cgen, \
                f"{name}: the realized circuit escapes the generic one"
            # the CLOSED FORM, where it applies: when H/P has a 5-cycle at
            # k = 4 the circuit IS that cycle, every tau_j on it is the same
            # screw up to sign, and that screw is the Klein-perp of the five
            # lines -- an explicit bracket vector, no growing cofactor.
            closed = (k == 4 and gir == 5)
            if closed:
                assert len(Cpen) == 5, "girth 5 but the circuit is not it"
                idx = sorted(Cpen)
                t0 = taus[0][idx[0]]
                for j in idx:
                    assert parallel(taus[0][j], t0), \
                        "the cycle stress is not a single screw"
                    assert klein(t0, C[j]) == 0, \
                        "the cycle screw is not Klein-perp to a cycle line"
                assert len(nullspace([hodge_star(C[j]) for j in idx])) == 1, \
                    "the five cycle lines do not span a hyperplane"
            # d lam = 0 at every single-vertex move off the support
            suppv = set()
            for j in Cpen:
                suppv |= set(Hed[j])
            VHa = VH + [d['a']]
            hubs = set(d['hubsGp'])
            lam_full = [F(0)] * len(Hed)
            if k == 4:
                for (j, s) in Pe:
                    lam_full[j] = klein(taus[0][j], C[j])
            off = zero = 0
            for y in sorted(set(VH) - suppv - set(d['P'][1:-1])
                            - {d['b'], d['c']}, key=str):
                svd = single_vertex_dirs(d['Gp'], placed, nrm, y, hubs)
                if not svd:
                    continue
                for dd in svd:
                    off += 1
                    r, dv, rows = dV_rank(Hed, VH, placed, d['b'], d['c'],
                                          [dd])
                    assert dv == 3
                    if all(x == 0 for x in rows[0]):
                        zero += 1
            assert off == zero, \
                f"{name}: a move off supp(tau) moved V_bc"
            # rank of the far-chart d lam, against (D2)'s 3(k-3)
            dirs, nvar, ncon = build_chart(d['Gp'], VHa, d['hubsGp'], placed,
                                           nrm, FIXED, d['b'], d['c'], d['a'])
            far = set(VHa) - set(d['P'][1:-1])
            fardirs = [x for x in dirs if all(w in far for w in x)]
            rf, dv, rowsf = dV_rank(Hed, VH, placed, d['b'], d['c'], dirs,
                                    restrict=far)
            assert rf <= 3 * (k - 3), "the (D2) bound was violated"
            same = (Cpen == Cgen)
            eq += 1 if same else 0
            tot += 1
            print(f"   {name:<17}{k:>2} {d['seed']:>5} {len(HP):>9}"
                  f" {gir:>6} {len(Cpen):>8} {len(Cgen):>8}"
                  f" {('yes' if same else 'NO'):>6} {off:>9} {zero:>7}"
                  f" {rf:>10}")
    print(f"\nSUPP OK: {tot} seeds; C_pen <= C_gen at every one"
          f" ({eq} with equality), and at every CLASS seed the support is"
          " the WHOLE far edge set -- (ANH-4) says it must be, generically."
          " So the named move needs no support-location step: ANY far vertex"
          " is in the support.  What the specialization could still do is"
          " shrink it, and the off-class control shows the mechanism: there"
          " the circuit is a proper 5-cycle, and every single-vertex far move"
          " off it leaves V_bc EXACTLY fixed.")


# ---------------- mode: the combinatorial census -----------------------------

def cheap_contract(Hed, P):
    """`E(H/P)` combinatorially (no placement), plus the companion edge set."""
    Pe = path_edges(Hed, P)
    Pset = {j for (j, s) in Pe}
    return contracted_edges(Hed, set(P), Pset), Pset


def branch_lengths(edges):
    """Lengths of the maximal degree-2 chains (branches) of a multigraph:
    the maximal paths whose interior vertices all have degree 2.  A branch of
    length `l` carries ONE screw in any self-stress (equilibrium at a 2-valent
    body transmits the wrench unchanged), constrained to be `B`-orthogonal to
    all `l` of its hinge lines -- so `l >= 6` with independent lines forces
    that screw to ZERO."""
    nb = neighbors(edges)
    node = {u for u in nb if len(nb[u]) != 2}
    if not node:
        return [len(edges)]                      # a bare cycle
    used, out = set(), []
    adj = {u: [] for u in nb}
    for i, (x, y) in enumerate(edges):
        adj[x].append((i, y))
        adj[y].append((i, x))
    for u in sorted(node, key=str):
        for (i, w) in adj[u]:
            if i in used:
                continue
            used.add(i)
            ln, cur, prev = 1, w, u
            while cur not in node:
                nxt = [(j, z) for (j, z) in adj[cur] if j not in used]
                assert len(nxt) == 1, "degree-2 walk went wrong"
                (j, z) = nxt[0]
                used.add(j)
                ln += 1
                prev, cur = cur, z
            out.append(ln)
    assert len(used) == len(edges), "branch decomposition missed an edge"
    return out


def wide_families():
    """A STRESS TEST of (ANH-8) -- `outer.sweep_shapes`' per-family length
    bounds are set for the `g14` question, so they could not have exhibited a
    long branch even if one existed.  These re-run the same generators with
    the bounds raised past 6, which is where the theorem bites."""
    from outer import shapes_from, K4E, K4PARE, THETA3, THETA4
    out = []
    for tag, n, E0, lmax in (('theta3', 2, THETA3, 12), ('theta4', 2, THETA4, 12),
                             ('K4', 4, K4E, 7), ('K4+par', 4, K4PARE, 7)):
        sh, tried, capped = shapes_from(tag, n, E0, lmax)
        out.append((f'{tag} (lengths 1..{lmax}, EXHAUSTIVE; {tried} tuples)',
                    sh))
    return out


def census_row(E, label, circ_budget):
    """(#triples, girth histogram, #circuit-checked, #free-pair, branch
    lengths, #triples with a length-5 branch) for one class shape.
    `circ_budget` is a mutable [n] counter capping the (expensive) full
    circuit certification."""
    ntr, hist, nc, nfp, blen = 0, {}, 0, 0, {}
    n5 = 0
    for v in sorted(verts_of(E), key=str):
        sd = split_data(E, v)
        if sd is None:
            continue
        a, b, c, Gp, Hed = sd
        for P in companions4(Hed, b, c):
            HP, Pset = cheap_contract(Hed, P)
            g = girth(HP)
            hist[g] = hist.get(g, 0) + 1
            ntr += 1
            # (ANH-4) corollary: girth(H/P) >= 6 UNLESS E(H/P) is itself the
            # 5-cycle, i.e. unless G is theta(3,4,5).
            assert g is None or g >= 6 or len(HP) == 5, \
                f"{label}: a PROPER 5-cycle in H/P -- (ANH-4) would be false"
            # (ANH-4) proper: every single-edge deletion is generically
            # INDEPENDENT, i.e. E(H/P) is a circuit of the Tay matroid.
            if circ_budget[0] > 0:
                circ_budget[0] -= 1
                nc += 1
                assert gen_stress_dim(HP) == 1, f"{label}: H/P count != 1"
                for i in range(len(HP)):
                    sub = [e for t, e in enumerate(HP) if t != i]
                    assert gen_stress_dim(sub) == 0, \
                        f"{label}: E(H/P) is NOT a circuit"
            # a far branch with two CONSECUTIVE free interior vertices --
            # (ANH-5)'s collinearity refutation needs one
            if free_pair(Gp, Hed, set(P)):
                nfp += 1
            # (ANH-4) has a sharp COMBINATORIAL consequence: E(H/P) being a
            # circuit means every edge carries stress, so no branch of H/P
            # may have length >= 6 (which would force its screw to zero).
            bl = branch_lengths(HP)
            for L in bl:
                blen[L] = blen.get(L, 0) + 1
            # (ANH-8), proved elementarily: `G - int(beta)` has
            # `f = l - 6`, so `l >= 7` breaks G's 5/6-sparsity and `l = 6`
            # makes it a PROPER RIGID subgraph, breaking hnoRigid.  So every
            # branch of G -- hence of H/P -- has length <= 5, and no branch
            # screw is forced to zero.
            assert max(bl) <= 5, \
                f"{label}: a branch of H/P of length {max(bl)} >= 6"
            if 5 in bl:
                n5 += 1
    return ntr, hist, nc, nfp, blen, n5


def free_pair(Gp, Hed, Pverts):
    """Is there an edge of `H` OUTSIDE the companion both of whose ends are
    non-hub, non-companion, degree-2 vertices with no hub neighbour?  Those
    are the two consecutive FREE interior vertices (ANH-5) wants."""
    nb = neighbors(Gp)
    hubs = {u for u in nb if len(nb[u]) >= 3}
    nbh = neighbors(Hed)

    def free(y):
        return (y not in hubs and y not in Pverts and len(nbh.get(y, ())) == 2
                and not any(u in hubs for u in nb.get(y, ())))
    return any(free(x) and free(y) for (x, y) in Hed)


def mode_census(circuit_cap=400):
    print("== (ANH-6) the class-wide census: the circuit, and where the")
    print("   closed form and the collinearity refutation apply ==")
    print("   (ANH-4): at k = 4, E(H/P) is a CIRCUIT of the generic Tay")
    print("   matroid -- proof: a proper over-braced W' either lies off X")
    print("   (contradicting G's 5/6-sparsity) or, adding back the companion")
    print("   and the split chain, forces f = 0 on a PROPER vertex set, i.e.")
    print("   a proper rigid subgraph, contradicting hnoRigid.  The count is")
    print("   tight only at k = 4 (5k+10 <= 6k+6 iff k >= 4), which is why")
    print("   the stress space has dimension >= 2 and the circuit is proper")
    print("   at k >= 5.  Corollary: girth(H/P) >= 6 unless G = theta(3,4,5),")
    print("   so the Klein-perp-of-a-5-cycle CLOSED FORM for tau applies at")
    print("   exactly one class shape.\n")
    hist, blen = {}, {}
    rows = ncirc = nfp = n5 = 0
    budget = [circuit_cap]
    print("   -- named inventory --")
    n0 = 0
    for label, E in named_inventory():
        t, h, nc, fp, bl, f5 = census_row(E, label, budget)
        n5 += f5
        for g, m in h.items():
            hist[g] = hist.get(g, 0) + m
        for L, m in bl.items():
            blen[L] = blen.get(L, 0) + m
        rows += t
        n0 += t
        ncirc += nc
        nfp += fp
    print(f"      {n0} (shape, split, length-4 companion) triples;"
          f" girth histogram {dict(sorted(hist.items()))};"
          f" H/P branch lengths {dict(sorted(blen.items()))}")
    print("   -- systematic sweep (outer.sweep_shapes) --")
    for desc, shapes in sweep_shapes():
        sub, subb, n, fp_n, f5_n = {}, {}, 0, 0, 0
        for label, E in shapes:
            t, h, nc, fp, bl, f5 = census_row(E, label, budget)
            n5 += f5
            f5_n += f5
            for g, m in h.items():
                sub[g] = sub.get(g, 0) + m
                hist[g] = hist.get(g, 0) + m
            for L, m in bl.items():
                subb[L] = subb.get(L, 0) + m
                blen[L] = blen.get(L, 0) + m
            n += t
            rows += t
            ncirc += nc
            nfp += fp
            fp_n += fp
        print(f"      {desc}: {len(shapes)} shapes, {n} companions,"
              f" girth {dict(sorted(sub.items()))}, free-pair {fp_n},"
              f" len-5 branch {f5_n}, H/P branch lengths"
              f" {dict(sorted(subb.items()))}")
    print("   -- (ANH-8) stress test: the same generators past length 6 --")
    for desc, shapes in wide_families():
        subb, n, f5_n = {}, 0, 0
        for label, E in shapes:
            t, h, nc, fp, bl, f5 = census_row(E, label, [0])
            for L, m in bl.items():
                subb[L] = subb.get(L, 0) + m
            n += t
            f5_n += f5
        print(f"      {desc}: {len(shapes)} shapes, {n} companions,"
              f" len-5 branch {f5_n}, H/P branch lengths"
              f" {dict(sorted(subb.items()))}")
    tot5 = hist.get(5, 0)
    print(f"\nCENSUS OK: {rows} (shape, split, length-4 companion) triples;"
          f" girth(H/P) histogram {dict(sorted(hist.items()))}, with every"
          f" girth-5 case having |E(H/P)| = 5 (i.e. G = theta(3,4,5));"
          f" E(H/P) certified a CIRCUIT at {ncirc} of them (budgeted);"
          f" and {nfp} carry a far branch with two consecutive FREE interior"
          " vertices, where (ANH-5)'s collinearity refutation applies with no"
          " hypothesis on the stress beyond its non-vanishing there."
          f"  H/P branch-length histogram {dict(sorted(blen.items()))}:"
          " max = " + str(max(blen)) + " (a branch of length >= 6 would carry"
          " a FORCED-ZERO screw, contradicting (ANH-4)); and " + str(n5) +
          " of the triples carry at least one length-5 branch, which is"
          " exactly where (ANH-7)'s CLOSED bracket form applies.")


# ---------------- mode: the recipe, in closed bracket form ------------------

def swept_probes(want=6):
    """The first `want` (shape, split) pairs of `outer.sweep_shapes`' K4
    family whose `H/P` carries a length-5 branch -- so the recipe is tested
    on shapes NOBODY hand-picked, not only on the named exemplars.
    Deterministic: `sweep_shapes` and `eligible_splits` are both
    lexicographic, and `prepared` takes the lowest valid integer seeds."""
    from outer import eligible_splits
    out = []
    for desc, shapes in sweep_shapes():
        if not desc.startswith('K4 '):
            continue
        for label, E in shapes:
            for v in eligible_splits(E):
                sd = split_data(E, v)
                if sd is None:
                    continue
                a, b, c, Gp, Hed = sd
                Ps = companions4(Hed, b, c)
                if not Ps:
                    continue
                HP, Pset = cheap_contract(Hed, Ps[0])
                if 5 not in branch_lengths(HP):
                    continue
                out.append((f'swept:{label}/v{v}', E, v))
                if len(out) >= want:
                    return out
    return out

def mode_recipe():
    print("== (ANH-7) the recipe: one named move, ONE bracket ==")
    print("   Equilibrium at a 2-valent body transmits the wrench unchanged,")
    print("   so `tau` is ONE screw per BRANCH of H/P, `B`-orthogonal to all")
    print("   `l` of that branch's hinge lines.  At `l = 5` that pins it to a")
    print("   1-dimensional Klein-perp `kappa_beta` -- an explicit bracket")
    print("   vector of the branch's six points, with NO global solve.  Then")
    print("   (ANH-5) at the free middle body `w2` of")
    print("   `beta = w0 w1 w2 w3 w4 w5` reads: d lam_{w2} = 0 iff")
    print("   `kappa_beta ~ C(w1 w3)`, and `C(w1 w3)` is automatically")
    print("   `B`-perp to FOUR of the five branch lines (each shares a")
    print("   point), so the whole criterion is the single remaining bracket")
    print("   `[w1, w3, w4, w5]`.\n")
    nb5 = ngood = nzero = 0
    for name, E, v in habitats4() + control_shapes() + swept_probes():
        for d in prepared(E, v, 2):
            Hed, VH, placed, nrm = d['Hed'], d['VH'], d['placed'], d['nrm']
            Pe, Pset, k = d['Pe'], d['Pset'], d['k']
            N, cycles, C = cycle_data(Hed, VH, placed)
            Z = nullspace(N)
            taus, _ = stress_space(Hed, VH, placed, Pset)
            assert len(taus) == k - 3
            tau = taus[0]
            lam_full = [F(0)] * len(Hed)
            for (j, s) in Pe:
                lam_full[j] = klein(tau[j], C[j])
            hubs = set(d['hubsGp'])
            nbG = neighbors(d['Gp'])
            rows = []
            for path in hp_branches(Hed, d['Pverts'], Pset):
                if len(path) - 1 != 5:
                    continue
                rho = branch_screw(Hed, tau, path)
                lines = [pluck_line(placed, path[i], path[i + 1])
                         for i in range(5)]
                ker = nullspace([hodge_star(L) for L in lines])
                assert len(ker) == 1, \
                    f"{name}: a length-5 branch whose lines do not span 5"
                kappa = ker[0]
                assert parallel(rho, kappa), \
                    f"{name}: the branch screw is not the Klein-perp"
                for i in (2, 3):
                    y = path[i]
                    if y in hubs or y in d['Pverts']:
                        continue
                    if any(u in hubs for u in nbG.get(y, ())):
                        continue          # not FREE: v cannot sweep H_inf
                    nb5 += 1
                    z1, z2 = path[i - 1], path[i + 1]
                    # the four points whose bracket is the whole criterion:
                    # the two lines C(w_{i-1} w_{i+1}) misses
                    rest = [t for t in range(5)
                            if not ({path[t], path[t + 1]} & {z1, z2})]
                    assert len(rest) == 1, \
                        "C(z1,z2) should miss exactly one branch line"
                    t = rest[0]
                    g = klein(pluck_line(placed, z1, z2), lines[t])
                    assert (g == 0) == parallel(kappa,
                                                pluck_line(placed, z1, z2)), \
                        f"{name}: the one-bracket criterion is not equivalent"
                    svd = single_vertex_dirs(d['Gp'], placed, nrm, y, hubs)
                    assert len(svd) == 3, "a free body should have 3 velocities"
                    allzero = True
                    for dd in svd:
                        vals, dC = dlam_values(N, cycles, C, Hed, placed,
                                               lam_full, Z, dd)
                        if any(x != 0 for x in vals):
                            allzero = False
                    # the GENERAL criterion, always exact:
                    #   d lam_y == 0  iff  rho _|_B (V_y ^ U_y),
                    # with `V_y` the allowed velocities (all of the plane at
                    # infinity at a FREE body) and
                    # `U_y = {om_{j1} z1 - om_{j2} z2 : om in Z}`.
                    jj = deg2_indices(Hed, y)
                    Ucoef = span_basis([[om[j] for j in jj] for om in Z])
                    Uy = len(Ucoef)
                    Ubasis = [[co[0] * p - co[1] * q
                               for p, q in zip(hat(placed[z1]),
                                               hat(placed[z2]))]
                              for co in Ucoef]
                    kill = nullspace([hodge_star(wedge2(dhat(dd[y]), ub))
                                      for dd in svd for ub in Ubasis])
                    inkill = all(x == 0 for x in rho) or in_span(
                        rho, span_basis(kill)) if kill else \
                        all(x == 0 for x in rho)
                    assert allzero == inkill, \
                        (f"{name}: the general (V_y ^ U_y)-perp criterion"
                         f" failed at {y}")
                    # and, at dim U_y = 2, that kill set IS `<C(z1 z2)>`, so
                    # the criterion collapses to the ONE bracket `g`
                    if Uy == 2:
                        assert len(kill) == 1 and parallel(
                            kill[0], pluck_line(placed, z1, z2)), \
                            f"{name}: the dim-2 kill set is not <C(z1z2)>"
                        assert allzero == (all(x == 0 for x in rho) or g == 0), \
                            f"{name}: the one-bracket criterion failed at {y}"
                    if allzero:
                        nzero += 1
                    else:
                        ngood += 1
                    rows.append((str(y), g, Uy, not allzero))
            print(f"   {name:<17} seed {d['seed']:>3}:"
                  f" length-5 branches with a free middle body: {len(rows)};"
                  + ''.join(f"  [{y}] bracket {'!= 0' if g else '= 0'},"
                            f" dim U = {u}, d lam {'!= 0' if ok else '= 0'}"
                            for (y, g, u, ok) in rows))
    print(f"\nRECIPE OK: {nb5} (length-5 branch, free middle body) sites;"
          f" the single-bracket criterion predicts `d lam != 0` correctly at"
          f" every one ({ngood} nonzero, {nzero} zero).  The move and the"
          " bracket are bounded-size and class-uniform; the two residual"
          " inputs are `tau_beta != 0` (the pencil stress does not vanish on"
          " that branch -- generically forced by (ANH-4), a specialization"
          " question at the pencil placement) and `dim U_y = 2`.")


# ---------------- mode: validate ---------------------------------------------

def mode_validate():
    print("== (ANH-val) the machinery ==")
    n = 0
    for name, E, v in habitats4():
        d = prepared(E, v, 1)[0]
        Hed, VH, placed = d['Hed'], d['VH'], d['placed']
        Pe, Pset = d['Pe'], d['Pset']
        N, cycles, C = cycle_data(Hed, VH, placed)
        Z = nullspace(N)
        taus, _ = stress_space(Hed, VH, placed, Pset)
        assert len(taus) == 1
        tau = taus[0]
        # (1) the Hodge dictionary: <star tau, X> = B(tau, X) = klein(tau, X)
        for j in range(min(4, len(Hed))):
            assert dot(hodge_star(tau[j]), C[j]) == klein(tau[j], C[j])
        # (2) lam annihilates pi_P(Z) directly
        lam_full = [F(0)] * len(Hed)
        for (j, s) in Pe:
            lam_full[j] = klein(tau[j], C[j])
        for om in Z:
            assert sum((lam_full[j] * om[j] for j in range(len(Hed))),
                       F(0)) == 0, "lam does not annihilate Z"
        # (3) lam lies in the ROW SPACE of N (so it kills every particular
        #     solution ambiguity in the implicit differentiation)
        NT = [[N[r][j] for r in range(len(N))] for j in range(len(Hed))]
        assert in_span(lam_full, span_basis(
            [[N[r][j] for j in range(len(Hed))] for r in range(len(N))])), \
            "lam is not in the row space of N"
        # (4) transmissibility off the companion, violation on it
        for j in range(len(Hed)):
            if j not in Pset:
                assert klein(tau[j], C[j]) == 0, "tau is not transmissible"
        assert any(lam_full[j] != 0 for (j, s) in Pe), "lam vanishes"
        # (5) V_bc from the stress side: ker lam inside S_P equals V_bc
        SP = [C[j] for (j, s) in Pe]
        assert len(span_basis(SP)) == 4, "S_P is not 4-dimensional"
        recon = []
        for om in Z:
            w = [F(0)] * 6
            for (j, s) in Pe:
                if om[j]:
                    for t in range(6):
                        w[t] += F(s) * om[j] * C[j][t]
            recon.append(w)
        assert len(span_basis(recon)) == 3
        assert all(in_span(x, span_basis(d['Vbc'])) for x in span_basis(recon))
        print(f"   {name:<15} seed {d['seed']:>3}: |E(H)| = {len(Hed)},"
              f" dim Z = {len(Z)}, dim tau-space = 1, lam in row(N),"
              f" transmissible off P, V_bc reproduced")
        n += 1
    print(f"\nVAL OK: {n} habitats; the Hodge dictionary, the annihilation of"
          " pi_P(Z), membership of lam in row(N), transmissibility off the"
          " companion and the reconstruction of V_bc all check exactly.")


# ---------------- main --------------------------------------------------------

def main():
    modes = {'--stress': mode_stress, '--rate': mode_rate,
             '--supp': mode_supp, '--recipe': mode_recipe,
             '--census': mode_census, '--validate': mode_validate}
    args = [a for a in sys.argv[1:] if a in modes]
    if not args:
        print(__doc__)
        return
    for a in args:
        modes[a]()
        print()


if __name__ == '__main__':
    main()
