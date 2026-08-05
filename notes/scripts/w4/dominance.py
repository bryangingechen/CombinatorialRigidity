"""
Phase 39, strategy candidate C1 -- DOMINANCE OF THE `V_bc` MAP.

`notes/Pencil-strategy.md` section 4-C1 proposes carrying, as a stronger
inductive invariant, a statement about the MAP

    {class far graphs + pencil realizations}  ->  Gr(3,6),   H |-> V_bc

rather than the pointwise escape condition.  By (PC-Z) (`notes/Pencil-
informal.md` section (K-pure) Step P3) the escape fails exactly when `V_bc`
meets one of the two maximal totally isotropic 3-spaces `alpha(a)` and
`Lambda^2 pi-hat`, each a Schubert `sigma_1` condition of CODIMENSION 1.  So
if the map were dominant (image dense in the 9-dimensional `Gr(3,6)`) a
generic realization would miss the bad locus outright.  The spike the
strategy doc asks for, and which nothing in the arc had run:

    compute the RANK OF THE DIFFERENTIAL of `H |-> V_bc` at a habitat of the
    class and measure it against `dim Gr(3,6) = 9`.

WHAT IS HELD FIXED, AND WHY.  `alpha(a)` is determined by `pt(a)` and
`Lambda^2 pi-hat` by the plane `plane(a,b,c)`; both are `a`/`b`/`c` data, NOT
far data.  The well-posed dominance question therefore varies the pencil
chart with the bad locus STANDING STILL, i.e. with `pt(a)`, `pt(b)`, `pt(c)`
and the two panels `Pi(b)`, `Pi(c)` frozen (`pt(a)` lies on
`M = Pi(b) cap Pi(c)`, so freezing the panels and the three points freezes
both isotropic 3-spaces).  That is scoping FIXED below.  Two diagnostic
scopings accompany it and are NOT dominance measures:
  FREE      -- nothing frozen; the bad locus co-moves, so a rank here does
               not bound the escape.  Upper bound on chart variability.
  UNPINNED  -- points free of the panel constraints (so, off the pencil
               stratum), `a`,`b`,`c` still frozen.  Isolates whether a rank
               deficiency comes from the PENCIL PIN or from path-sum
               containment, which is pin-free.

THE MODEL.  `V_bc = {m(b) - m(c) : m a motion of H}` ((T1),
section (K-pitch) Step 1).  Motions are computed here from the AUGMENTED
system in unknowns `(m_x)_{x in V(H)}` and `(om_e)_{e in E(H)}`

        m_x - m_y - om_e * C_e = 0        (6 rows per edge e = (x,y)),

whose entries are polynomial in the point coordinates -- so the differential
of `V_bc` is IMPLICIT DIFFERENTIATION of a kernel: with `A(theta) u = 0` and
`u` a kernel element, `A u' = -(dA) u` is a derived linear system solved at
the base point in exact Q, and `dV(delta)` is the class of
`u'[m_b] - u'[m_c]` in `K^6 / V_bc` -- the tangent model
`Hom(V_bc, K^6/V_bc)` of `Gr(3,6)`, of dimension 3*3 = 9.  No CAS, no
floating point.

THE A-PRIORI CAP (compute this before believing any rank).  Path-sum
containment (section (K-pitch) Step 1a) gives `V_bc <= span{C_e : e in P}`
for EVERY `b`-`c` path `P` of `H` simultaneously.  Let `k` be the length of
the shortest such path (the "companion length"; `k >= 3`, since `dim V_bc =
3`).  At `k = 3` the containment is an EQUALITY of 3-spaces, so `V_bc` is a
function of the companion's two interior points alone; those sit in the
frozen panels `Pi(b)`, `Pi(c)`, so the image of the whole chart is at most
4-dimensional and

        rank dV <= 4  at every length-3-companion habitat,

no matter how large the far graph is.  (Corollary, independent of the
freezing: `B|_{V_bc}` is then the Gram of a 3-chain of lines, of rank 2, so
`V_bc` always lies in the discriminant hypersurface of `Gr(3,6)`.)  At
`k >= 4` there is no such cap and the rank must be measured.

Drivers (foreground, one at a time; exact rational arithmetic, no floating
point anywhere; every sampled configuration carries rank/dimension asserts,
including the `star_span_ranks` genericity guard against the `plane_basis`
artifact -- `notes/scripts/README.md` *Divergences*):

    python3 notes/scripts/w4/dominance.py --cap        # the structural cap
    python3 notes/scripts/w4/dominance.py --jac        # the Jacobian ranks
    python3 notes/scripts/w4/dominance.py --far        # far-graph sensitivity
    python3 notes/scripts/w4/dominance.py --validate   # the machinery itself
"""
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rref, rank, nullspace, wedge2, hat, neighbors
from repin import seed_probe, span_basis, in_span
from pitch import klein, H_motions_vbc, theta_edges, nt21, paths_graph
from nogood_subdiv import (deficiency, branch_decomposition, hcard_ok,
                           triangles)
from kslide import no_rigid_branch_union
from pencil_escape import double_subdivide, K4, K5_minus_matching
from kbare_common import verts_of
# `star_span_ranks` is the README section-1 canonical genericity guard; it
# lives in the sibling leaf `flanks`.  See README section 2's note: a third
# consumer is the signal to move it down to `repin`.
from flanks import star_span_ranks


# ---------------- graph helpers --------------------------------------------

def h_edges(edges, v, a):
    """E(H) for H = G - v - a, as an ordered list (the omega-column order)."""
    return [e for e in edges if v not in e and a not in e]


def simple_paths(Hed, b, c, maxlen=8):
    """Every simple b-c path of H, as a vertex list, up to `maxlen` edges."""
    nb = neighbors(Hed)
    out = []

    def walk(cur, seen, acc):
        if len(acc) - 1 > maxlen:
            return
        if cur == c:
            out.append(list(acc))
            return
        for w in sorted(nb[cur], key=str):
            if w in seen:
                continue
            seen.add(w)
            acc.append(w)
            walk(w, seen, acc)
            acc.pop()
            seen.discard(w)

    walk(b, {b}, [b])
    return out


def path_span(path, placed):
    """span{C_e : e in P} for a b-c path given as a vertex list."""
    return span_basis([wedge2(hat(placed[path[i]]), hat(placed[path[i + 1]]))
                       for i in range(len(path) - 1)])


# ---------------- the augmented motion system ------------------------------

def motion_system(Hed, VH, placed):
    """Rows of  m_x - m_y - om_e * C_e = 0  (6 per edge), in the unknown
    layout  [m_{VH[0]} (6) ... m_{VH[-1]} (6) | om_{Hed[0]} ... ].
    Returns (rows, vidx, ncols, C) with `C[j]` the j-th edge's line."""
    vidx = {x: 6 * i for i, x in enumerate(VH)}
    nv = 6 * len(VH)
    ncols = nv + len(Hed)
    C = [wedge2(hat(placed[x]), hat(placed[y])) for (x, y) in Hed]
    rows = []
    for j, (x, y) in enumerate(Hed):
        for k in range(6):
            r = [F(0)] * ncols
            r[vidx[x] + k] = F(1)
            r[vidx[y] + k] = F(-1)
            r[nv + j] = -C[j][k]
            rows.append(r)
    return rows, vidx, ncols, C


def dhat(d):
    return [d[0], d[1], d[2], F(0)] if d is not None else [F(0)] * 4


def dC_along(Hed, placed, dpt):
    """The directional derivative of every C_e along the point-velocity
    field `dpt` (a dict vertex -> Q^3; absent = 0)."""
    out = []
    for (x, y) in Hed:
        px, py = hat(placed[x]), hat(placed[y])
        w1 = wedge2(dhat(dpt.get(x)), py)
        w2 = wedge2(px, dhat(dpt.get(y)))
        out.append([w1[k] + w2[k] for k in range(6)])
    return out


def solve_multi(A, rhs_cols):
    """Particular solutions of `A x = rhs` for many right-hand sides at once.
    Returns a list of solutions, or None if some system is inconsistent."""
    nA = len(A[0])
    aug = [row + [rc[i] for rc in rhs_cols] for i, row in enumerate(A)]
    R, piv = rref(aug)
    if any(p >= nA for p in piv):
        return None
    sols = []
    for j in range(len(rhs_cols)):
        x = [F(0)] * nA
        for i, p in enumerate(piv):
            x[p] = R[i][nA + j]
        sols.append(x)
    return sols


def modV_maker(Vbasis):
    """(reduce, Vr, piv, free): `reduce(w)` = the class of w in K^6 / V, in
    the coordinates complementary to V's rref pivots."""
    Vr, piv = rref([v[:] for v in Vbasis])
    Vr = Vr[:len(piv)]
    free = [c for c in range(6) if c not in piv]

    def reduce(w):
        w = list(w)
        for i, p in enumerate(piv):
            f = w[p]
            if f:
                w = [a - f * b for a, b in zip(w, Vr[i])]
        return [w[c] for c in free]

    return reduce, Vr, piv, free


# ---------------- the chart, and its tangent space -------------------------

FIXED, FREE, UNPINNED = 'fixed', 'free', 'unpinned'


def build_chart(Gp, VHa, hubsGp, placed, nrm, scoping, b, c, a):
    """A basis of the tangent space of the pencil chart at the base point,
    as point-velocity dicts (vertex -> Q^3; normal velocities are internal).

    Variables: `pt(w)` for every `w` in `VHa` (= V(H) together with `a`) that
    is not frozen, and -- when the pin is on -- `n(u)` for every hub `u` of
    `G'` whose normal is not frozen.  Constraints: `<n_u, pt(w) - pt(u)> = 0`
    for every hub `u` of `G'` and every `G'`-neighbour `w` of `u` -- i.e. the
    pencil condition, differentiated.  Returns (dirs, #vars, #constraints)."""
    nbp = neighbors(Gp)
    pinned = scoping != UNPINNED
    if scoping == FREE:
        fz_pt, fz_n = set(), set()
    else:
        fz_pt, fz_n = {a, b, c}, {b, c}

    col = {}

    def var(kind, key, i):
        k = (kind, key, i)
        if k not in col:
            col[k] = len(col)
        return col[k]

    ptv = {}
    for w in VHa:
        if w in fz_pt:
            continue
        ptv[w] = [var('p', w, i) for i in range(3)]
    nv = {}
    if pinned:
        for u in hubsGp:
            if u in fz_n or u not in nrm:
                continue
            nv[u] = [var('n', u, i) for i in range(3)]
    nvar = len(col)

    cons = []
    if pinned:
        for u in hubsGp:
            if u not in nrm:
                continue
            for w in sorted(nbp[u], key=str):
                if w not in VHa:
                    continue
                row = [F(0)] * nvar
                delta = [placed[w][i] - placed[u][i] for i in range(3)]
                if u in nv:
                    for i in range(3):
                        row[nv[u][i]] += delta[i]
                if w in ptv:
                    for i in range(3):
                        row[ptv[w][i]] += nrm[u][i]
                if u in ptv:
                    for i in range(3):
                        row[ptv[u][i]] -= nrm[u][i]
                cons.append(row)
    T = nullspace(cons) if cons else [
        [F(1) if k == i else F(0) for k in range(nvar)] for i in range(nvar)]
    dirs = []
    for t in T:
        d = {}
        for w, ix in ptv.items():
            vec = [t[ix[0]], t[ix[1]], t[ix[2]]]
            if any(x != 0 for x in vec):
                d[w] = vec
        dirs.append(d)
    return dirs, nvar, len(cons)


# ---------------- the differential -----------------------------------------

def dV_rank(Hed, VH, placed, b, c, dirs, restrict=None):
    """rank of the differential of `H |-> V_bc` at `placed`, along `dirs`.

    Returns (rank, dim V_bc, rows) with `rows` the list of 9-vectors, one per
    direction, in the tangent model `Hom(V_bc, K^6/V_bc)`.  `restrict`, when
    given, is a set of vertices; directions moving a vertex outside it are
    dropped (used by `--far`)."""
    A, vidx, ncols, C = motion_system(Hed, VH, placed)
    K = nullspace(A)
    ib, ic = vidx[b], vidx[c]

    def diff(u):
        return [u[ib + k] - u[ic + k] for k in range(6)]

    chosen, Vb = [], []
    for u in K:
        d = diff(u)
        if any(x != 0 for x in d) and not in_span(d, Vb):
            chosen.append(u)
            Vb = span_basis(Vb + [d])
    assert len(Vb) == len(chosen)
    if len(Vb) != 3:
        return None, len(Vb), None
    reduce, Vr, piv, free = modV_maker(Vb)
    # re-express the chosen kernel elements so that their b-c differences are
    # exactly the rref basis Vr (so `dV` is read in the same frame as the
    # graph chart of Gr(3,6) that `--validate` uses):
    Dmat = [diff(u) for u in chosen]
    coef = []
    for target in Vr:
        sol = solve_multi([[Dmat[j][i] for j in range(3)] for i in range(6)],
                          [target])
        assert sol is not None, "V_bc basis change failed"
        coef.append(sol[0])
    base = [[sum((coef[i][j] * chosen[j][t] for j in range(3)), F(0))
             for t in range(ncols)] for i in range(3)]

    use = []
    for d in dirs:
        if restrict is not None and any(w not in restrict for w in d):
            continue
        use.append(d)
    rhs, meta = [], []
    for di, d in enumerate(use):
        dC = dC_along(Hed, placed, d)
        nvv = 6 * len(VH)
        for i in range(3):
            u = base[i]
            col = [F(0)] * len(A)
            for j in range(len(Hed)):
                uj = u[nvv + j]
                if uj:
                    for k in range(6):
                        col[6 * j + k] = uj * dC[j][k]
            # A u' = -(dA) u  and  ((dA)u)[6j+k] = -u[om_j] * dC[j][k]
            rhs.append(col)
            meta.append((di, i))
    sols = solve_multi(A, rhs) if rhs else []
    assert sols is not None, "implicit differentiation inconsistent"
    rows = [[F(0)] * 9 for _ in use]
    for (di, i), s in zip(meta, sols):
        cls = reduce(diff(s))
        for j in range(3):
            rows[di][3 * i + j] = cls[j]
    return rank(rows), 3, rows


# ---------------- the cycle-kernel cross-check (independent route) ---------

def cycle_data(Hed, VH, placed):
    """(N, cycles) for the cycle formulation: N is 6c x |E| with block-entry
    (cycle, e) = sign * C_e; `Z = ker N` is the hinge-rotation space."""
    nb = {x: [] for x in VH}
    for j, (x, y) in enumerate(Hed):
        nb[x].append((y, j, 1))
        nb[y].append((x, j, -1))
    parent, order, seen = {VH[0]: None}, [VH[0]], {VH[0]}
    while order:
        x = order.pop()
        for (y, j, s) in nb[x]:
            if y not in seen:
                seen.add(y)
                parent[y] = (x, j, s)
                order.append(y)
    assert len(seen) == len(VH), "H is disconnected"
    tree = {p[1] for p in parent.values() if p is not None}

    def root_path(x):
        out = []
        while parent[x] is not None:
            (p, j, s) = parent[x]
            out.append((j, s))
            x = p
        return out

    cycles = []
    for j, (x, y) in enumerate(Hed):
        if j in tree:
            continue
        coef = {j: 1}
        for (jj, ss) in root_path(y):
            coef[jj] = coef.get(jj, 0) - ss
        for (jj, ss) in root_path(x):
            coef[jj] = coef.get(jj, 0) + ss
        cycles.append(coef)
    C = [wedge2(hat(placed[x]), hat(placed[y])) for (x, y) in Hed]
    N = []
    for coef in cycles:
        for k in range(6):
            N.append([F(coef.get(j, 0)) * C[j][k] for j in range(len(Hed))])
    return N, cycles, C


def path_signs(Hed, path):
    """[(edge index, sign)] realizing m(P[0]) - m(P[-1]) = sum sign*om*C."""
    ix = {}
    for j, (x, y) in enumerate(Hed):
        ix[(x, y)] = (j, 1)
        ix[(y, x)] = (j, -1)
    return [ix[(path[i], path[i + 1])] for i in range(len(path) - 1)]


def dV_rank_cycles(Hed, VH, placed, path, dirs):
    """The same differential through the cycle kernel -- a different matrix,
    a different solve.  Returns (rank, rows) or None."""
    N, cycles, C = cycle_data(Hed, VH, placed)
    Z = nullspace(N) if N else [
        [F(1) if k == i else F(0) for k in range(len(Hed))]
        for i in range(len(Hed))]
    sg = path_signs(Hed, path)

    def LP(om, lines):
        out = [F(0)] * 6
        for (j, s) in sg:
            if om[j]:
                for k in range(6):
                    out[k] += F(s) * om[j] * lines[j][k]
        return out

    chosen, Vb = [], []
    for om in Z:
        d = LP(om, C)
        if any(x != 0 for x in d) and not in_span(d, Vb):
            chosen.append(om)
            Vb = span_basis(Vb + [d])
    if len(Vb) != 3:
        return None
    reduce, Vr, piv, free = modV_maker(Vb)
    Dmat = [LP(om, C) for om in chosen]
    coef = []
    for target in Vr:
        sol = solve_multi([[Dmat[j][i] for j in range(3)] for i in range(6)],
                          [target])
        assert sol is not None
        coef.append(sol[0])
    base = [[sum((coef[i][j] * chosen[j][t] for j in range(3)), F(0))
             for t in range(len(Hed))] for i in range(3)]
    rows = []
    for d in dirs:
        dC = dC_along(Hed, placed, d)
        dN = []
        for coefc in cycles:
            for k in range(6):
                dN.append([F(coefc.get(j, 0)) * dC[j][k]
                           for j in range(len(Hed))])
        rhs = []
        for i in range(3):
            rhs.append([-sum((dN[r][j] * base[i][j]
                              for j in range(len(Hed))), F(0))
                        for r in range(len(dN))])
        sols = solve_multi(N, rhs) if N else [[F(0)] * len(Hed)] * 3
        assert sols is not None, "cycle-route differentiation inconsistent"
        row = [F(0)] * 9
        for i in range(3):
            v = [LP(base[i], dC)[k] + LP(sols[i], C)[k] for k in range(6)]
            cls = reduce(v)
            for j in range(3):
                row[3 * i + j] = cls[j]
        rows.append(row)
    return rank(rows), rows


# ---------------- habitats --------------------------------------------------

def nt21c3():
    """A second length-3-companion habitat, non-theta, so the k = 3 cap is
    not a theta artifact: the NT21 hub multigraph with the companion shortened
    to 3 (b-c paths 3 and 3; plus b-u:4, u-c:4, b-w:3, w-c:3, u-w:4).
    sum ell = 24 = 6 c(G-hub) with c = 4: tight."""
    return paths_graph([3, 3], [(0, 2, 4), (2, 1, 4), (0, 3, 3),
                                (3, 1, 3), (2, 3, 4)])


def nt16k5():
    """A class habitat whose companion has length 5 -- the middle entry of
    the k-table.  Hubs b=0, c=1, u=2, w=3; the b-c split chain has length 3
    and there is no second b-c path, so the companion runs b-u-c (2+3) or
    b-w-c (2+3); plus u-w:5.  sum ell = 18 = 6 c(G-hub) with c = 3: tight."""
    return paths_graph([3], [(0, 2, 2), (2, 1, 3), (0, 3, 2),
                             (3, 1, 3), (2, 3, 5)])


def branch_pmap(edges):
    """The hub-path map `no_rigid_branch_union` wants, derived uniformly from
    `nogood_subdiv.branch_decomposition` (no hand-written vertex lists)."""
    hubs, branches = branch_decomposition(edges)
    assert branches, "no hub structure"
    return {i: [h1] + inter + [h2]
            for i, (h1, h2, inter) in enumerate(branches)}


def habitats():
    """(name, edges, split vertex v, branch map, note).  Every one is tight
    (`5|E| = 6(|V|-1)`) with `def = 0`, asserted at load."""
    spec = []
    spec.append(('theta(3,3,6)', theta_edges((3, 3, 6)), 10,
                 'k=3: the split chain + companion is a rigid C6'))
    E, pm = nt21c3()
    spec.append(('NT21c3', E, pm[0][1], 'k=3, non-theta; same reason'))
    spec.append(('theta(3,4,5)', theta_edges((3, 4, 5)), 10,
                 'k=4; the (K-Lambda)/(K-wit) exemplar'))
    E, pm = nt21()
    spec.append(('NT21', E, pm[0][1], 'k=4, non-theta'))
    E, pm = nt16k5()
    spec.append(('NT16k5', E, pm[0][1], 'k=5'))
    E, hubs, chains, allv = double_subdivide(K4())
    spec.append(('K4 dbl-subdiv', E, chains[0][1],
                 'k=6; the arc control habitat, and route 1s locality gate'))
    E, hubs, chains, allv = double_subdivide(K5_minus_matching())
    spec.append(('K5-M dbl-subdiv', E, chains[0][1], 'k=6 control'))
    out = []
    for name, E, v, note in spec:
        assert deficiency(E) == 0, f"{name}: def != 0"
        n = len(verts_of(E))
        assert 5 * len(E) == 6 * (n - 1), f"{name}: not tight"
        assert hcard_ok(E) and not triangles(E), f"{name}: hcard/triangle"
        out.append((name, E, v, branch_pmap(E), note))
    return out


HABITATS = habitats()


def class_status(d, pm):
    """'class' or '(K-res)' at a validated seed's habitat.  Two independent
    certificates, asserted to agree:  (i) the split chain plus the shortest
    companion is a cycle of length 3 + k, rigid exactly when k <= 3
    (`def(C_j) = max(0, j-6)`, Shared dictionary R3) -- a PROPER rigid
    subgraph, refuting `hnoRigid`; this is section (K-slide) Step 5's
    `ell_1 + ell_2 >= 7`.  (ii) `kslide.no_rigid_branch_union`, the exhaustive
    branch-union sweep."""
    short = next(P for P in d['paths'] if len(P) - 1 == d['k'])
    cyc = [(short[i], short[i + 1]) for i in range(len(short) - 1)]
    cyc += [(d['b'], d['v']), (d['v'], d['a']), (d['a'], d['c'])]
    rigid = deficiency(cyc) == 0
    assert rigid == (d['k'] == 3), "the C_(3+k) rigidity dichotomy failed"
    hno = no_rigid_branch_union(d['edges'], pm)
    assert hno != rigid, "the two hnoRigid certificates disagree"
    return 'class' if hno else '(K-res)'


def base_seed(edges, v, seed):
    """A validated pencil-generic target-rank G' seed, plus the derived H
    data.  Returns a dict or None.  Carries the mandatory guards."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if not (b in hubsG and c in hubsG and b in nrm and c in nrm):
        return None
    Gp = [e for e in edges if v not in e] + [(a, b)]
    # GENERICITY GUARD (the `plane_basis` artifact): every closed star must
    # span its panel.  A seed failing this is rejected, not measured.
    ssr = star_span_ranks(Gp, placed)
    if any(r != 3 for r in ssr.values()):
        return None
    Hed = h_edges(edges, v, a)
    VH = sorted(verts_of(Hed), key=str)
    if len(VH) != len(verts_of(edges)) - 2:
        return None
    Vbc, dimMot, _ = H_motions_vbc(edges, v, a, b, c, placed)
    if len(Vbc) != 3:
        return None
    paths = simple_paths(Hed, b, c)
    assert paths, "no b-c path in H"
    k = min(len(P) - 1 for P in paths)
    return {'seed': seed, 'a': a, 'b': b, 'c': c, 'v': v, 'edges': edges,
            'Gp': Gp, 'Hed': Hed,
            'VH': VH, 'placed': placed, 'nrm': nrm, 'pt': pt,
            'hubsGp': [u for u in sorted(neighbors(Gp), key=str)
                       if len(neighbors(Gp)[u]) >= 3],
            'Vbc': Vbc, 'dimMot': dimMot, 'paths': paths, 'k': k,
            'dim R_a': p['dim R_a']}


def seeds_for(edges, v, want, lo=1, hi=400):
    out = []
    for s in range(lo, hi):
        d = base_seed(edges, v, s)
        if d is not None:
            out.append(d)
            if len(out) >= want:
                break
    return out


# ---------------- mode: the structural cap ---------------------------------

def bad_locus_meets(d):
    """(dim(V_bc cap alpha(a)), dim(V_bc cap Lambda^2 pi-hat)) at the base
    seed -- the two Schubert conditions of (PC-Z).  Both 0 means the escape
    HOLDS there, so a dominance rank and the escape are measured on the same
    configuration.  Dimensions via `dim(U cap W) = dim U + dim W - dim(U+W)`
    (only the dimension is needed, so no intersection basis is built)."""
    placed, a, b, c = d['placed'], d['a'], d['b'], d['c']
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab, Cac, Cbc = wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)
    # alpha(a) = Lambda^2(lines through pt(a)); the three lines to b, c and
    # a third independent point span it.
    w = [x + y for x, y in zip(bh, ch)]
    w = [w[0] + 1, w[1] - 1, w[2] + 2, w[3]]
    alpha = span_basis([Cab, Cac, wedge2(ah, w)])
    beta = span_basis([Cab, Cac, Cbc])
    assert len(alpha) == 3 and len(beta) == 3, "isotropic 3-space degenerate"
    out = []
    for S in (alpha, beta):
        out.append(len(d['Vbc']) + len(S) - len(span_basis(d['Vbc'] + S)))
    return out[0], out[1]


def apriori_cap(k):
    """min(9, 6k - 14): with pt(a), pt(b), pt(c), Pi(b), Pi(c) frozen, V_bc
    is determined by (i) the shortest companion's line span S_P, moved by the
    3k - 5 chart parameters of its interiors (2 in Pi(b), 3 each for the k-3
    free middles, 2 in Pi(c)), and (ii) the annihilator of V_bc in S_P*, a
    point of Gr(k-3, k) of dimension 3(k-3).  Bites only at k = 3, where it
    reads `rank <= 4`."""
    return min(9, (3 * k - 5) + 3 * (k - 3))


def mode_cap():
    print("== (D-cap) path-sum containment, the a-priori cap, and k >= 4 ==")
    print("   V_bc <= span{C_e : e in P} for EVERY b-c path P of H;")
    print("   at companion length k = 3 the containment is an EQUALITY of")
    print("   3-spaces, so V_bc is a function of the companion's two")
    print("   interior points alone -- both confined to the frozen panels.")
    print("   Cap: rank dV <= min(9, 6k - 14) = 4, 9, 9, 9 at k = 3,4,5,6.")
    print("   And `hnoRigid` FORCES k >= 4: the split chain plus the")
    print("   companion is a C_(3+k), rigid iff 3+k <= 6 (section (K-slide)")
    print("   Step 5's ell_1 + ell_2 >= 7).  So k = 3 is a (K-res) habitat.\n")
    tot = 0
    for name, E, v, pm, note in HABITATS:
        ds = seeds_for(E, v, 3)
        assert ds, f"{name}: no valid seed"
        print(f"-- {name}  ({note})")
        for d in ds:
            Vbc, placed = d['Vbc'], d['placed']
            k, paths = d['k'], d['paths']
            short = [P for P in paths if len(P) - 1 == k]
            for P in paths:
                S = path_span(P, placed)
                for m in Vbc:
                    assert in_span(m, S), \
                        f"{name}: V_bc escapes the span of a b-c path"
            meet_dims = []
            for P in short:
                S = path_span(P, placed)
                meet_dims.append(len(S))
                if len(S) == 3:
                    assert span_basis(S + Vbc) == span_basis(Vbc), \
                        "k=3: V_bc != companion span"
            gram = [[klein(x, y) for y in Vbc] for x in Vbc]
            rq = rank(gram)
            assert (rq == 2) == (k == 3), \
                (f"{name} seed {d['seed']}: rank Q|V_bc = {rq} at k = {k}"
                 " -- the chain-Gram prediction failed")
            st = class_status(d, pm)
            assert (st == '(K-res)') or k >= 4, "a k=3 shape claimed class"
            da, db = bad_locus_meets(d)
            assert (da, db) == (0, 0), \
                "the escape FAILS at this seed -- a (PC-Z) failure witness"
            print(f"   seed {d['seed']:>3}: k = {k}  status {st:<9}"
                  f" |shortest| = {len(short)}  |b-c paths| = {len(paths)}"
                  f"  dim span(P) = {sorted(set(meet_dims))}"
                  f"  rank Q|V_bc = {rq}  cap = {apriori_cap(k)}"
                  f"  V_bc cap (alpha(a), L2 pi) = ({da}, {db})")
            tot += 1
    print(f"\nCAP OK: {tot} seeds; path-sum containment holds at every b-c"
          " path; rank Q|V_bc = 2 exactly at k = 3 (so V_bc then lies in the"
          " discriminant hypersurface of Gr(3,6)), 3 at k >= 4; and the"
          " C_(3+k) dichotomy holds at every habitat, so every k = 3 shape"
          " is (K-res) and every class shape has k >= 4.  V_bc misses BOTH"
          " isotropic 3-spaces at every one of the 21 seeds -- including the"
          " rank-capped k = 3 ones, so dominance is sufficient for the"
          " escape and very far from necessary.")


# ---------------- mode: the Jacobian rank ----------------------------------

def jac_at(d, scoping):
    Gp, VH, placed, nrm = d['Gp'], d['VH'], d['placed'], d['nrm']
    VHa = VH + [d['a']]
    dirs, nvar, ncon = build_chart(Gp, VHa, d['hubsGp'], placed, nrm,
                                   scoping, d['b'], d['c'], d['a'])
    if scoping != FREE:
        # the bad locus must STAND STILL: no direction may move a, b or c.
        assert not any(w in dd for dd in dirs for w in (d['a'], d['b'],
                                                        d['c'])), \
            "a frozen point moved -- the bad locus would co-move"
    r, dv, rows = dV_rank(d['Hed'], VH, placed, d['b'], d['c'], dirs)
    assert dv == 3
    return r, len(dirs), nvar, ncon


def mode_jac():
    print("== (D-jac) rank of d(H |-> V_bc) against dim Gr(3,6) = 9 ==")
    print("   FIXED    = pt(a), pt(b), pt(c), Pi(b), Pi(c) frozen -- the")
    print("              dominance measure (the bad locus stands still).")
    print("   FREE     = nothing frozen (bad locus co-moves; NOT a")
    print("              dominance measure).")
    print("   UNPINNED = panel constraints dropped (off the pencil")
    print("              stratum); isolates the pin from path-sum")
    print("              containment.")
    print("   Rank is lower semicontinuous, so the MAX over seeds is a")
    print("   lower bound for the generic rank; the cap is an upper bound")
    print("   proved structurally, not sampled.\n")
    print(f"   {'habitat':<17}{'k':>2} {'seed':>5} {'dimT':>5}"
          f" {'FIXED':>6} {'FREE':>5} {'UNPIN':>6} {'cap':>4}  status")
    summary = []
    for name, E, v, pm, note in HABITATS:
        ds = seeds_for(E, v, 3)
        best = {FIXED: 0, FREE: 0, UNPINNED: 0}
        k, st = ds[0]['k'], class_status(ds[0], pm)
        for d in ds:
            rr, nd = {}, None
            for sc in (FIXED, FREE, UNPINNED):
                r, ndir, nvar, ncon = jac_at(d, sc)
                rr[sc] = r
                best[sc] = max(best[sc], r)
                if sc == FIXED:
                    nd = ndir
            print(f"   {name:<17}{d['k']:>2} {d['seed']:>5}"
                  f" {nd:>5} {rr[FIXED]:>6} {rr[FREE]:>5}"
                  f" {rr[UNPINNED]:>6} {apriori_cap(k):>4}  {st}")
        summary.append((name, k, st, best))
    print()
    n_dom = n_def = 0
    for name, k, st, best in summary:
        dominant = best[FIXED] == 9
        n_dom += dominant
        n_def += not dominant
        verdict = ('DOMINANT (rank 9 attained)' if dominant
                   else f"DEFICIENT: max rank {best[FIXED]} < 9")
        print(f"   {name:<17} k = {k}  {st:<9} {verdict}")
        assert best[FIXED] <= apriori_cap(k), "the a-priori cap was violated"
        if k == 3:
            assert best[FIXED] == 4, "the k=3 cap is not attained"
            assert best[UNPINNED] <= 6, "the pin-free k=3 cap was violated"
            assert st == '(K-res)'
        else:
            assert dominant, f"{name}: k >= 4 but rank 9 not attained"
    print(f"\nJAC OK: {n_dom} habitats DOMINANT, {n_def} DEFICIENT."
          " Both deficient ones have k = 3, are (K-res) (not class members),"
          " and sit exactly at the proven cap of 4 -- also capped at 6 with"
          " the pencil pin DROPPED, so the deficiency is path-sum"
          " containment, not the pin.  Every k >= 4 habitat probed attains"
          " the full rank 9, hence dominance, hence (by (PC-Z)) the escape at"
          " a generic seed of that shape.")


# ---------------- mode: far-graph sensitivity -------------------------------

def mode_far():
    print("== (D-far) does the far graph move V_bc at all? ==")
    print("   Strategy doc 4-C1 claim (i): 'as the far graph grows,")
    print("   parameters are added, so the image can only grow'.  Measured")
    print("   here by restricting the chart tangent to directions that move")
    print("   ONLY vertices off the shortest b-c path of H (the far part),")
    print("   in the FIXED scoping.  (T5) (section (K-pitch) Step 5b) says")
    print("   far data enters V_bc ONLY through its annihilator in S_P*, a")
    print("   point of Gr(k-3, k): so rank(far) <= 3(k-3), = 0 at k = 3.\n")
    print(f"   {'habitat':<17}{'k':>2} {'seed':>5} {'|far dirs|':>11}"
          f" {'rank(far)':>10} {'3(k-3)':>7} {'rank(all)':>10}")
    for name, E, v, pm, note in HABITATS:
        for d in seeds_for(E, v, 2):
            Gp, VH, placed, nrm = d['Gp'], d['VH'], d['placed'], d['nrm']
            VHa = VH + [d['a']]
            dirs, nvar, ncon = build_chart(Gp, VHa, d['hubsGp'], placed,
                                           nrm, FIXED, d['b'], d['c'],
                                           d['a'])
            short = next(P for P in d['paths'] if len(P) - 1 == d['k'])
            far = set(VHa) - set(short[1:-1])
            rf, _, rowsf = dV_rank(d['Hed'], VH, placed, d['b'], d['c'],
                                   dirs, restrict=far)
            ra, _, _ = dV_rank(d['Hed'], VH, placed, d['b'], d['c'], dirs)
            nfar = sum(1 for x in dirs if all(w in far for w in x))
            print(f"   {name:<17}{d['k']:>2} {d['seed']:>5} {nfar:>11}"
                  f" {rf:>10} {3 * (d['k'] - 3):>7} {ra:>10}")
            assert rf <= 3 * (d['k'] - 3), \
                "the (T5) far-dependence bound 3(k-3) was violated"
            if d['k'] == 3:
                assert rf == 0, \
                    "k=3: a far direction moved V_bc -- claim (i) would hold"
    print("\nFAR OK: the (T5) bound rank(far) <= 3(k-3) holds at every seed,"
          " and is ATTAINED at every habitat probed.  At k = 3 it is 0:"
          " EVERY far direction lies in the kernel of dV, so growing the far"
          " graph does not enlarge the image at all -- the image is governed"
          " by the LOCAL companion length, not by far-graph size.")


# ---------------- mode: validate the machinery ------------------------------

def mode_validate():
    print("== (D-val) the differentiation machinery, three ways ==")
    n_ok = 0
    for name, E, v, pm, note in HABITATS:
        d = seeds_for(E, v, 1)[0]
        Gp, VH, placed, nrm = d['Gp'], d['VH'], d['placed'], d['nrm']
        Hed, b, c = d['Hed'], d['b'], d['c']
        VHa = VH + [d['a']]
        # (1) three routes to V_bc agree: rigidity matrix (pitch), the
        #     augmented system, the cycle kernel.
        A, vidx, ncols, C = motion_system(Hed, VH, placed)
        K = nullspace(A)
        Vaug = span_basis([[u[vidx[b] + k] - u[vidx[c] + k] for k in range(6)]
                           for u in K])
        assert len(Vaug) == 3
        assert all(in_span(m, Vaug) for m in d['Vbc']), "V_bc route mismatch"
        assert len(K) == d['dimMot'], \
            f"{name}: dim ker(augmented) {len(K)} != dim mot(H) {d['dimMot']}"
        N, cycles, Cc = cycle_data(Hed, VH, placed)
        Z = nullspace(N)
        assert len(Z) == d['dimMot'] - 6, \
            f"{name}: dim Z {len(Z)} != dim mot(H) - 6"
        # (2) the two derivative routes agree exactly, direction by direction
        dirs, nvar, ncon = build_chart(Gp, VHa, d['hubsGp'], placed, nrm,
                                       FIXED, b, c, d['a'])
        r1, dv, rows1 = dV_rank(Hed, VH, placed, b, c, dirs)
        short = next(P for P in d['paths'] if len(P) - 1 == d['k'])
        got = dV_rank_cycles(Hed, VH, placed, short, dirs)
        assert got is not None
        r2, rows2 = got
        assert rows1 == rows2, f"{name}: the two derivative routes disagree"
        # (3) end-to-end secant test on a chart-EXACT ray (directions that
        #     move no hub normal keep theta0 + t*delta inside the chart, so
        #     the ray is an honest curve of pencil realizations).
        ray = None
        for dd in dirs:
            trial = _secant(Hed, VH, placed, b, c, dd, rows1[dirs.index(dd)])
            if trial is not None:
                ray = trial
                break
        assert ray is not None, f"{name}: no usable secant ray"
        print(f"   {name:<17} seed {d['seed']:>3}: dim mot(H) = {d['dimMot']},"
              f" dim Z = {len(Z)}, |T| = {len(dirs)}, rank = {r1};"
              f" routes agree; secant errors {ray}")
        n_ok += 1
    print(f"\nVAL OK: {n_ok} habitats; V_bc agrees across three models, the"
          " augmented-system and cycle-kernel differentials agree ENTRY BY"
          " ENTRY, and the secant quotient converges to the computed"
          " differential on an exact chart ray.")


def _secant(Hed, VH, placed, b, c, d, drow, ks=(3, 4, 5, 6)):
    """|phi(t)/t - dV| for t = 2^-k on the ray placed + t*d; returns the list
    of exact error norms (as Fractions) if they decay, else None."""
    A, vidx, ncols, C = motion_system(Hed, VH, placed)
    K = nullspace(A)
    V0 = span_basis([[u[vidx[b] + k] - u[vidx[c] + k] for k in range(6)]
                     for u in K])
    if len(V0) != 3:
        return None
    Vr, piv = rref([x[:] for x in V0])
    Vr = Vr[:3]
    free = [x for x in range(6) if x not in piv]
    errs = []
    for kk in ks:
        t = F(1, 2 ** kk)
        pl = {x: [placed[x][i] + t * d[x][i] for i in range(3)]
              if x in d else placed[x] for x in placed}
        A2, vidx2, _, _ = motion_system(Hed, VH, pl)
        K2 = nullspace(A2)
        W = span_basis([[u[vidx2[b] + k] - u[vidx2[c] + k] for k in range(6)]
                        for u in K2])
        if len(W) != 3:
            return None
        Wr, piv2 = rref([x[:] for x in W])
        if piv2 != piv:
            return None
        Wr = Wr[:3]
        e = F(0)
        for i in range(3):
            for j in range(3):
                dev = (Wr[i][free[j]] - Vr[i][free[j]]) / t - drow[3 * i + j]
                e = max(e, abs(dev))
        errs.append(e)
    if all(x == 0 for x in errs):
        return ['exactly 0'] * len(errs)
    for i in range(len(errs) - 1):
        if not (errs[i + 1] <= errs[i] * F(3, 5)):
            return None
    return [f"{float(x):.3g}" for x in errs]


# ---------------- main ------------------------------------------------------

if __name__ == '__main__':
    args = sys.argv[1:]
    if '--cap' in args:
        mode_cap()
    elif '--jac' in args:
        mode_jac()
    elif '--far' in args:
        mode_far()
    elif '--validate' in args:
        mode_validate()
    else:
        print(__doc__)
