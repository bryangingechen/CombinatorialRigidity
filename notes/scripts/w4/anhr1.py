"""
Phase 39, kernel-(K) THIRD fan-out direction Q -- (ANH-R1) AS A PURE
CONDITION: the reduced object `H/P - beta`, its branch-core normal form, and
the finite list of PENCIL-CHART LOCAL TYPES the class realizes.

Workbook section: `(K-ann)`, continuation Steps A14+; labels `(ANH-13)+` (the
reserved direction-Q namespace, `notes/Pencil-labels.md` 2026-08-06 G/Q/O
table).  Read against section (K-ann) *Steps A7/A10-A13* ((ANH-7), (ANH-9)
one-point decidability, (ANH-10) the census, (ANH-11)/(ANH-12) the inhabited
bad locus) and `notes/Pencil-strategy.md` sections 5.3/5.4 (the symbolic
layer's local-frame budget).

THE OBJECT.  At a `k = 4` class (shape, split, companion) triple with a
length-5 branch `beta` of `H/P`, the graph `H/P - beta` (drop beta's five
edges AND its four interior bodies) has body-hinge count exactly

    5|E'| - 6(|V'| - 1) = 0,

so it is generically isostatic ((ANH-4)) and (ANH-R1) says it stays
independent at the pencil placement.  Two structural facts turn that into a
SMALL symbolic object, and this driver's job is to extract it:

  (ANH-13) BRANCH-CORE NORMAL FORM.  By (ANH-6) a self-stress is one screw per
       branch, `B`-perpendicular to all the branch's hinge lines, with
       equilibrium at the nodes.  So the `5|E'| x 6(|V'|-1)` rigidity matrix
       reduces to a SQUARE `6(n-1) x 6(n-1)` matrix in the branch screws
       (`n` = number of nodes = bodies of degree != 2).  At cycle rank 1 the
       core is a bare cycle, `n = 0`, and the whole pure condition is the
       6x6 PLUECKER DETERMINANT of the cycle's hinge lines.
  (ANH-14) LOCAL TYPE.  The determinant sees only the points of the reduced
       object's bodies and the panels constraining them, so each triple
       presents one of finitely many LOCAL TYPES: per point, whether it is a
       hub (carries a panel), how many hub-neighbour panels confine it, and
       whether it is a companion vertex of the welded body `X`.

Modes:

    python3 notes/scripts/w4/anhr1.py --types     # (ANH-13)(ii)/(ANH-14): local types
    python3 notes/scripts/w4/anhr1.py --reduce    # (ANH-13)(ii) vs the full solve
    python3 notes/scripts/w4/anhr1.py --size      # (ANH-13)(i)/(iii), (ANH-14)(b)
    python3 notes/scripts/w4/anhr1.py --frame     # (ANH-14)(a)/(b) at the census sites
    python3 notes/scripts/w4/anhr1.py --witness   # (ANH-15)(c): the (ANH-12) bad points
    python3 notes/scripts/w4/anhr1.py --validate  # the machinery

The symbolic half is `notes/scripts/m2/anhr1.m2` (blocks (ANH-Q0)-(ANH-Q4)):
the closed forms, the irreducibility, and the two bad-locus mechanisms.

Exact rational arithmetic; no floating point; NO new rng -- every placement
arrives through `dominance.base_seed`'s composite guard `repin.star_generic`
via `annih.prepared`.  Imports `annih` / `shrink` / `outer` READ-ONLY.
"""
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, wedge2, hat, neighbors
from repin import hodge_star
from kbare_common import verts_of
from annih import (prepared, hp_branches, habitats4, swept_probes,
                   path_edges)
from outer import split_data, companions4
from shrink import hp_edge_rows, branch_edge_ix, census_pool, stress_dim_without


# ---------------- the reduced object `H/P - beta` ---------------------------

def reduced_rows(rows, drop, beta, tag='X*'):
    """`E(H/P) - beta` as `(j, u, w, x, y)` rows.  Dropping the branch's five
    edges leaves its four INTERIOR bodies isolated, and an isolated body
    makes the reduced framework disconnected (hence dependent for trivial
    reasons), so they go with the edges; the branch's two END bodies are
    nodes of `H/P` and survive.  Returns (rows, bodies)."""
    keep = [r for r in rows if r[0] not in drop]
    gone = {w for w in beta[1:-1]}
    bodies = set()
    for r in rows:
        for u in (r[1], r[2]):
            bodies.add(u)
    bodies -= gone
    live = set()
    for r in keep:
        live.add(r[1])
        live.add(r[2])
    assert live <= bodies, "a surviving edge meets a deleted interior body"
    assert not (bodies - live) - {tag}, \
        "an isolated body other than the welded X survived"
    return keep, bodies


def core_decompose(rows):
    """Branch-core normal form of a body-hinge multigraph given as
    `(j, u, w, x, y)` rows: nodes are the bodies of degree != 2; each branch
    is a maximal degree-2 chain, returned as the list of its rows in order,
    together with its two end nodes.  A component with NO node (a bare cycle)
    is returned as a branch whose two ends are both `None`.
    Returns (nodes, branches) with `branches` a list of
    `(end0, end1, [rows in order])`."""
    deg, adj = {}, {}
    for r in rows:
        for u in (r[1], r[2]):
            deg[u] = deg.get(u, 0) + 1
        adj.setdefault(r[1], []).append((r, r[2]))
        adj.setdefault(r[2], []).append((r, r[1]))
    for u in adj:
        adj[u].sort(key=lambda t: t[0][0])
    nodes = sorted([u for u in deg if deg[u] != 2], key=str)
    used, branches = set(), []
    for u in nodes:
        for (r, w) in adj[u]:
            if r[0] in used:
                continue
            used.add(r[0])
            chain, cur, prev = [r], w, u
            while cur not in deg or deg[cur] == 2:
                nxt = [(t, z) for (t, z) in adj[cur] if t[0] not in used]
                if not nxt:
                    break
                assert len(nxt) == 1, "degree-2 walk went wrong"
                (t, z) = nxt[0]
                used.add(t[0])
                chain.append(t)
                prev, cur = cur, z
            branches.append((u, cur, chain))
    # bare cycles: components all of whose bodies have degree 2
    for r0 in rows:
        if r0[0] in used:
            continue
        used.add(r0[0])
        chain, start = [r0], r0[1]
        cur, prev = r0[2], r0[1]
        while cur != start:
            nxt = [(t, z) for (t, z) in adj[cur] if t[0] not in used]
            assert len(nxt) == 1, "bare-cycle walk went wrong"
            (t, z) = nxt[0]
            used.add(t[0])
            chain.append(t)
            prev, cur = cur, z
        branches.append((None, None, chain))
    assert len(used) == len(rows), "the core decomposition lost an edge"
    return nodes, branches


def count_excess(rows, bodies):
    """`5|E| - 6(|V| - 1)` for the reduced body-hinge multigraph."""
    return 5 * len(rows) - 6 * (len(bodies) - 1)


# ---------------- the pure condition, in branch-screw coordinates -----------

def core_matrix(rows, nodes, branches, placed):
    """The SQUARE branch-screw matrix of (ANH-13)(ii).

    Unknowns: for every branch `j`, its screw `S_j` in `K^6` -- 6 columns
    each.  Rows:
      (i)  TRANSMISSIBILITY, one per hinge line of the branch:
           `B(S_j, C_e) = 0`;
      (ii) EQUILIBRIUM at every node but one (the last is dependent):
           `sum_{j at u} +- S_j = 0`, 6 rows per node.
    A bare cycle contributes only rows of type (i).

    The matrix is square exactly when the count of `count_excess` is 0:
    `sum_j l_j = |E|` rows of type (i) and `6(n-1)` of type (ii), against
    `6m` columns, and `|E| + 6(n-1) = 6m` iff `5|E| = 6(|V|-1)` for a
    connected multigraph whose branch lengths are its edge counts."""
    m = len(branches)
    ncols = 6 * m
    out = []
    for jb, (e0, e1, chain) in enumerate(branches):
        for r in chain:
            C = wedge2(hat(placed[r[3]]), hat(placed[r[4]]))
            s = hodge_star(C)
            row = [F(0)] * ncols
            for t in range(6):
                row[6 * jb + t] = s[t]
            out.append(row)
    if nodes:
        for u in nodes[:-1]:
            sign = {}
            for jb, (e0, e1, chain) in enumerate(branches):
                if e0 == u:
                    sign[jb] = sign.get(jb, 0) + 1
                if e1 == u:
                    sign[jb] = sign.get(jb, 0) - 1
            for t in range(6):
                row = [F(0)] * ncols
                for jb, sg in sign.items():
                    row[6 * jb + t] = F(sg)
                out.append(row)
    return out


# ---------------- the pencil-chart local type -------------------------------

def chart_roles(d):
    """`{vertex: (is_hub, #hub-neighbours, is_companion)}` on the split graph
    `G'`, i.e. exactly what confines the vertex's point in the pencil chart:
    a hub carries its own panel, and every hub neighbour's panel contains the
    point."""
    Gp, hubs, Pv = d['Gp'], set(d['hubsGp']), d['Pverts']
    nb = neighbors(Gp)
    out = {}
    for x in nb:
        hn = sum(1 for w in nb[x] if w in hubs)
        out[x] = (x in hubs, hn, x in Pv)
    return out


def type_signature(rows, nodes, branches, roles, tag='X*'):
    """A canonical, shape-independent signature of the reduced object's LOCAL
    TYPE: the cyclic/branch structure together with, per hinge line, the
    confinement role of its two real endpoints.

    Role letters, per endpoint vertex:
        H<r>  a hub whose point carries a panel, with `r` hub neighbours
        f<r>  a non-hub confined by `r` hub-neighbour panels (r = 0,1,2)
    A companion vertex (a point of the welded body `X`) is marked with a
    leading `*`."""
    def role(x):
        is_hub, hn, is_comp = roles[x]
        s = ('H%d' % hn) if is_hub else ('f%d' % hn)
        return ('*' + s) if is_comp else s

    parts = []
    for (e0, e1, chain) in branches:
        seg = '+'.join('%s.%s' % (role(r[3]), role(r[4])) for r in chain)
        kind = 'cyc' if e0 is None else 'br'
        parts.append('%s[%s]' % (kind, seg))
    ndesc = 'n%d' % len(nodes)
    return '%s;%s' % (ndesc, '|'.join(sorted(parts)))


def local_points(rows):
    """The real points of `G'` the reduced object's hinge lines use -- the
    only chart coordinates its pure condition can depend on."""
    out = set()
    for r in rows:
        out.add(r[3])
        out.add(r[4])
    return out


def panel_incidences(d, pts):
    """Per hub `u` of `G'`, the LOCAL points confined to its panel `Pi(u)`:
    `pt(u)` itself when `u` is local, plus every local `G'`-neighbour of `u`.

    A panel with `<= 3` local incidences imposes NO condition on the local
    points -- three points always span a plane, and the panel (and `pt(u)`
    when `u` is not local) can then be chosen afterwards.  A panel with `>= 4`
    local incidences forces those points COPLANAR, a genuine equation of the
    local chart."""
    Gp, hubs = d['Gp'], set(d['hubsGp'])
    nb = neighbors(Gp)
    out = {}
    for u in hubs:
        inc = {w for w in nb[u] if w in pts}
        if u in pts:
            inc.add(u)
        out[u] = inc
    return out


def forced_coplanarities(d, pts):
    """The panels that DO constrain the local chart (>= 4 local incidences)."""
    inc = panel_incidences(d, pts)
    return {u: s for u, s in inc.items() if len(s) >= 4}


def chain_normal_form(chain, roles):
    """The point chain of a sequence of hinge lines, walked in order: for
    consecutive lines, the shared endpoint is the common BODY's point, and
    the walk is `p0 - p1 - ... `.  A break (no shared endpoint) happens
    exactly at the welded body `X`, whose two lines hang off two DIFFERENT
    companion vertices; it is printed as ` // `.  Returns the printable
    normal form and the ordered list of distinct points."""

    def rl(x):
        is_hub, hn, is_comp = roles[x]
        return ('%s%s%d' % ('*' if is_comp else '', 'H' if is_hub else 'f', hn))

    parts, pts = [], []
    n = len(chain)
    for i, r in enumerate(chain):
        nxt = chain[(i + 1) % n]
        sh = {r[3], r[4]} & {nxt[3], nxt[4]}
        pr = chain[(i - 1) % n]
        shp = {r[3], r[4]} & {pr[3], pr[4]}
        head = sorted({r[3], r[4]} - sh, key=str)
        tail = sorted(sh, key=str)
        if i == 0:
            first = head[0] if head else sorted({r[3], r[4]}, key=str)[0]
            parts.append(rl(first))
            pts.append(first)
        if tail:
            parts.append('-' + rl(tail[0]))
            pts.append(tail[0])
        else:
            rest = sorted({r[3], r[4]} - shp, key=str)
            e = rest[0] if rest else r[4]
            parts.append('-' + rl(e) + ' // ')
            pts.append(e)
    return ''.join(parts), pts


def shared_points(rows):
    """The multiset of real points the reduced object's hinge lines use, with
    how many lines each carries -- the datum that decides how many free
    coordinates the local chart has."""
    cnt = {}
    for r in rows:
        for x in (r[3], r[4]):
            cnt[x] = cnt.get(x, 0) + 1
    return cnt


# ---------------- per-triple extraction --------------------------------------

def triple_rows(d):
    """Everything this driver needs at one prepared seed."""
    Hed, Pverts, Pset = d['Hed'], d['Pverts'], d['Pset']
    rows = hp_edge_rows(Hed, Pverts, Pset)
    branches = hp_branches(Hed, Pverts, Pset)
    return rows, branches


def long_branches(branches, ell=5):
    return [p for p in branches if len(p) - 1 == ell]


def analyse(d, beta):
    """The reduced object at one (seed, length-5 branch) site."""
    Hed = d['Hed']
    rows, _ = triple_rows(d)
    drop = branch_edge_ix(Hed, beta)
    red, bodies = reduced_rows(rows, drop, beta)
    exc = count_excess(red, bodies)
    nodes, branches = core_decompose(red)
    roles = chart_roles(d)
    sig = type_signature(red, nodes, branches, roles)
    return {'rows': red, 'bodies': bodies, 'excess': exc, 'nodes': nodes,
            'branches': branches, 'roles': roles, 'sig': sig,
            'drop': drop, 'beta': beta,
            'pts': shared_points(red)}


# ---------------- mode: the type census --------------------------------------

def pool():
    """The (ANH-10) census pool, unchanged (`shrink.census_pool`)."""
    return census_pool()


def mode_types():
    print("== (ANH-13)/(ANH-14) the reduced object `H/P - beta` and its local types ==")
    print("   beta a length-5 branch of H/P; `H/P - beta` drops its 5 edges")
    print("   and its 4 interior bodies.  Excess = 5|E'| - 6(|V'|-1) must be")
    print("   0 (the count (ANH-R1) is about).  `c` = cycle rank, `n` = core")
    print("   nodes, `sq` = the branch-screw matrix's side 6m = |E'| + 6(n-1).\n")
    print(f"   {'triple':<34}{'|E(H/P)|':>9}{'sites':>6}{'exc':>5}"
          f"{'c':>3}{'n':>3}{'m':>3}{'sq':>4}  type")
    sigs, nsite, ntrip = {}, 0, 0
    for (label, E, v) in pool():
        ds = prepared(E, v, 1)
        if not ds:
            print(f"   {label:<34} (no guarded seed)")
            continue
        d = ds[0]
        rows, branches = triple_rows(d)
        longs = long_branches(branches)
        ntrip += 1
        if not longs:
            print(f"   {label:<34}{len(rows):>9}{0:>6}"
                  "     -- no length-5 branch")
            continue
        for beta in longs:
            a = analyse(d, beta)
            nsite += 1
            c = len(a['rows']) - len(a['bodies']) + 1
            m = len(a['branches'])
            sq = 6 * m
            assert sq == len(a['rows']) + 6 * max(len(a['nodes']) - 1, 0), \
                "the branch-screw matrix is not square"
            sigs.setdefault(a['sig'], []).append(label)
            print(f"   {label:<34}{len(rows):>9}{len(longs):>6}"
                  f"{a['excess']:>5}{c:>3}{len(a['nodes']):>3}{m:>3}{sq:>4}"
                  f"  {a['sig'][:60]}")
    print(f"\n   triples with a guarded seed: {ntrip}; length-5-branch"
          f" sites: {nsite}; DISTINCT LOCAL TYPES: {len(sigs)}")
    for s in sorted(sigs):
        print(f"     [{len(sigs[s]):>2} sites]  {s}")
    return 0


def mode_reduce():
    """(ANH-13)(ii) verified: the branch-screw matrix has the SAME corank as the
    full `H/P - beta` stress space rebuilt from scratch, at every site."""
    print("== (ANH-13)(ii) the branch-core normal form, against the full solve ==")
    print("   claim: dim(self-stresses of H/P - beta) = corank of the square")
    print("   6m x 6m branch-screw matrix, at every guarded seed.\n")
    print(f"   {'triple':<34}{'sq':>4}{'corank':>7}{'full':>6}{'ok':>4}")
    nok, nsite = 0, 0
    for (label, E, v) in pool():
        ds = prepared(E, v, 1)
        if not ds:
            continue
        d = ds[0]
        rows, branches = triple_rows(d)
        for beta in long_branches(branches):
            a = analyse(d, beta)
            M = core_matrix(a['rows'], a['nodes'], a['branches'], d['placed'])
            sq = 6 * len(a['branches'])
            assert all(len(r) == sq for r in M) and len(M) == sq, \
                "branch-screw matrix not square"
            cork = sq - rank(M)
            full = stress_dim_without(d['Hed'], d['VH'], d['placed'],
                                      d['Pset'], a['drop'])
            ok = (cork == full)
            nok += int(ok)
            nsite += 1
            print(f"   {label:<34}{sq:>4}{cork:>7}{full:>6}{'yes' if ok else 'NO':>4}")
            assert ok, "branch-core reduction disagrees with the full solve"
    print(f"\n   branch-core normal form correct at {nok}/{nsite} sites")
    return 0


def panel_incidences_raw(Gp, hubs, pts):
    """`panel_incidences` on raw `(Gp, hubs)` -- placement-free, so it runs
    over the whole census pool and not only over placed seeds."""
    nb = neighbors(Gp)
    out = {}
    for u in hubs:
        inc = {w for w in nb[u] if w in pts}
        if u in pts:
            inc.add(u)
        out[u] = inc
    return out


def size_row_full(Hed, P, Gp):
    """Placement-free size + local-frame data at one triple, on the REAL
    contracted rows (so the local points are `G'` vertices, not body names).
    Per length-5 branch: `(c', n, m, order, #forced coplanarities)`."""
    Pe = path_edges(Hed, P)
    Pset = {j for (j, s) in Pe}
    Pverts = set(P)
    rows = hp_edge_rows(Hed, Pverts, Pset)
    bodies = set()
    for r in rows:
        bodies.add(r[1])
        bodies.add(r[2])
    cHP = len(rows) - len(bodies) + 1
    nb = neighbors(Gp)
    hubs = {u for u in nb if len(nb[u]) >= 3}
    nodes, branches = core_decompose(rows)
    out = []
    for (e0, e1, chain) in branches:
        if len(chain) != 5:
            continue
        if e0 is None:
            out.append((0, 0, 0, 0, 0))
            continue
        drop = {r[0] for r in chain}
        interior = set()
        for r in chain:
            for u in (r[1], r[2]):
                interior.add(u)
        interior -= {e0, e1}
        keep = [r for r in rows if r[0] not in drop]
        bod = bodies - interior
        c2 = len(keep) - len(bod) + 1
        nd, br = core_decompose(keep)
        order = 6 if not nd else 6 * (len(nd) - 1)
        pts = local_points(keep)
        inc = panel_incidences_raw(Gp, hubs, pts)
        forced = sum(1 for u in inc if len(inc[u]) >= 4)
        out.append((c2, len(nd), len(br), order, forced))
    return cHP, out


def mode_size():
    """The SIZE LAW, placement-free, over the full (ANH-9) triple pool."""
    from outer import named_inventory as NI, sweep_shapes as SW
    print("== (ANH-13) the size law: how big is the pure condition? ==")
    print("   `H/P - beta` is connected with |V'| = 5c'+1, |E'| = 6c' where")
    print("   c' = c(H/P) - 1 = c(G) - 2, so its pure condition is a")
    print("   determinant whose order GROWS with the shape.  Reduced order:")
    print("   6 (the Pluecker determinant of a bare 6-cycle) at c' = 1, and")
    print("   6(n-1) in the branch screws at c' >= 2, n = #nodes.\n")
    tally, ctal, ntri, n5 = {}, {}, 0, 0
    ntal, fother, nbare, nfree = {}, {}, 0, 0
    fams = [('named', NI())] + [(desc, sh) for (desc, sh) in SW()]
    for desc, shapes in fams:
        loc = {}
        for label, E in shapes:
            for v in sorted(verts_of(E), key=str):
                sd = split_data(E, v)
                if sd is None:
                    continue
                a, b, c, Gp, Hed = sd
                for P in companions4(Hed, b, c):
                    ntri += 1
                    cHP, ents = size_row_full(Hed, P, Gp)
                    if ents:
                        n5 += 1
                    for (c2, n, m, side, forced) in ents:
                        ctal[c2] = ctal.get(c2, 0) + 1
                        ntal[n] = ntal.get(n, 0) + 1
                        tally[side] = tally.get(side, 0) + 1
                        loc[side] = loc.get(side, 0) + 1
                        assert c2 == cHP - 1 or c2 == 0, \
                            "c(H/P - beta) != c(H/P) - 1"
                        if n == 0 and c2 == 1:
                            nbare += 1
                            nfree += 1 if forced == 0 else 0
                            assert forced == 0, \
                                "a panel constrains a bare-cycle local frame"
                        else:
                            fother[forced] = fother.get(forced, 0) + 1
        print(f"   {desc[:56]:<58} reduced orders {dict(sorted(loc.items()))}")
    print(f"\n   {ntri} (shape, split, length-4 companion) triples;"
          f" {n5} with a length-5 branch")
    print(f"   c(H/P - beta) histogram : {dict(sorted(ctal.items()))}")
    print(f"   core-node   n histogram : {dict(sorted(ntal.items()))}")
    print(f"   reduced order histogram : {dict(sorted(tally.items()))}")
    tot = sum(tally.values())
    b6 = tally.get(6, 0)
    bare = ntal.get(0, 0) - ctal.get(0, 0)
    print(f"   reduced order 6 sites   : {b6}/{tot}"
          f" = {100.0 * b6 / tot:.1f}% of length-5-branch sites")
    print(f"   BARE-CYCLE sites (c'=1) : {bare}/{tot}"
          f" = {100.0 * bare / tot:.1f}% -- the M2-feasible stratum,"
          " where the pure condition is the 6x6 Pluecker determinant")
    print(f"   degree of C in the point coordinates = 12c' :"
          f" {dict(sorted({12 * k: v for k, v in ctal.items()}.items()))}")
    print(f"   bare-cycle local frames with NO panel forcing a coplanarity:"
          f" {nfree}/{nbare}")
    print(f"   forced-coplanarity histogram at the OTHER sites:"
          f" {dict(sorted(fother.items()))}")
    return 0


def mode_frame():
    """The LOCAL FRAME of every bare-cycle site: its point chain, and the
    panels that do or do not constrain it."""
    print("== (ANH-14) the local frame of a bare-cycle `H/P - beta` ==")
    print("   A panel of G' constrains the local points only when it carries")
    print("   >= 4 of them (three points always span a plane).  Where none")
    print("   does, the local chart is the FULL configuration space of the")
    print("   chain's points and the pure condition is the UNIVERSAL one.\n")
    nsite, nfree = 0, 0
    for (label, E, v) in pool():
        ds = prepared(E, v, 1)
        if not ds:
            continue
        d = ds[0]
        rows, branches = triple_rows(d)
        for beta in long_branches(branches):
            a = analyse(d, beta)
            if a['nodes'] or not a['branches']:
                continue
            nsite += 1
            chain = a['branches'][0][2]
            nf, pts = chain_normal_form(chain, a['roles'])
            loc = local_points(a['rows'])
            forced = forced_coplanarities(d, loc)
            nfree += int(not forced)
            print(f"   {label}")
            print(f"      chain  {nf}   ({len(set(pts))} distinct points,"
                  f" {len(loc)} local)")
            inc = panel_incidences(d, loc)
            hist = {}
            for u, s in inc.items():
                hist[len(s)] = hist.get(len(s), 0) + 1
            print(f"      panel local-incidence histogram {dict(sorted(hist.items()))}"
                  f"   forced coplanarities: {len(forced)}")
            assert not forced, "a panel constrains the local chart here"
    print(f"\n   bare-cycle sites: {nsite}; with an UNCONSTRAINED local chart:"
          f" {nfree}/{nsite}")
    return 0


def analyse_at(d, drop, placed=None):
    """The reduced object for an explicit set `drop` of dropped `H`-edge
    indices (the form `shrink.construct_at` hands back), rather than for a
    branch path.  Interiors are the bodies all of whose `H/P` edges are
    dropped."""
    rows, _ = triple_rows(d)
    inc = {}
    for r in rows:
        for u in (r[1], r[2]):
            inc.setdefault(u, []).append(r[0])
    gone = {u for u, js in inc.items() if all(j in drop for j in js)}
    keep = [r for r in rows if r[0] not in drop]
    bodies = set(inc) - gone
    nodes, branches = core_decompose(keep)
    exc = count_excess(keep, bodies)
    return {'rows': keep, 'bodies': bodies, 'nodes': nodes,
            'branches': branches, 'excess': exc, 'drop': drop}


def mode_witness():
    """CONSISTENCY with (ANH-12): the pure condition must VANISH at every
    constructed bad point.  Re-runs `shrink.construct_at` (read-only) and
    evaluates THIS driver's branch-screw matrix at the witness."""
    from shrink import construct_at
    print("== (ANH-15) consistency: C(H/P - beta) at the (ANH-12) witnesses ==")
    print("   The bad points of section (K-ann) Steps A11-A12 must lie in the")
    print("   pure condition's zero locus.  Checked in THIS driver's object")
    print("   (the branch-screw matrix), independently of how the witness was")
    print("   built.  At an (ANH-R1)-EXACT witness (beta length 5) the matrix")
    print("   is square and the check is `det = 0`; at a matroid-drop witness")
    print("   (beta length 4) the object has count -1 and is reported only.\n")
    nex, nsing, ntriv, nother = 0, 0, 0, 0
    for (name, E, v) in habitats4() + swept_probes(6):
        ds = prepared(E, v, 1)
        if not ds or ds[0]['k'] != 4:
            continue
        d = ds[0]
        verdict, res = construct_at(d)
        if res is None:
            ntriv += 1
            print(f"   {name:<34}: {verdict[:52]}")
            continue
        a = analyse_at(d, set(res['bset']))
        M = core_matrix(a['rows'], a['nodes'], a['branches'], res['new'])
        sq = 6 * len(a['branches'])
        cork = sq - rank(M)
        square = (len(M) == sq)
        tag = 'EXACT' if a['excess'] == 0 else f"drop-form (exc {a['excess']})"
        print(f"   {name:<34}: {tag:<20} order {sq:>3},"
              f" corank {cork} at the witness")
        if a['excess'] == 0:
            nex += 1
            assert square, "count 0 but the branch-screw matrix is not square"
            assert cork >= 1, "the pure condition does NOT vanish at the witness"
            nsing += 1
        else:
            nother += 1
    print(f"\n   (ANH-R1)-exact witnesses: {nex}; pure condition VANISHES at"
          f" {nsing}/{nex}; matroid-drop witnesses reported: {nother};"
          f" trivial theta(3,4,5) cases: {ntriv}")
    return 0


def mode_validate():
    print("== machinery ==")
    ok = 0
    # the core decomposition on a synthetic bare 6-cycle
    rows = [(i, 'b%d' % i, 'b%d' % ((i + 1) % 6), 'p%d' % i, 'p%d' % ((i + 1) % 6))
            for i in range(6)]
    nodes, branches = core_decompose(rows)
    assert nodes == [] and len(branches) == 1 and len(branches[0][2]) == 6
    print("   OK  bare 6-cycle: 0 nodes, 1 branch of 6 lines")
    ok += 1
    bodies = {'b%d' % i for i in range(6)}
    assert count_excess(rows, bodies) == 0
    print("   OK  bare 6-cycle has body-hinge count 0")
    ok += 1
    # a theta core: two nodes, three branches
    th = []
    j = 0
    for (arm, ln) in enumerate([4, 4, 4]):
        prev = 'A'
        for i in range(ln - 1):
            cur = 'a%d_%d' % (arm, i)
            th.append((j, prev, cur, 'q%d' % j, 'q%d' % (j + 1))); j += 1
            prev = cur
        th.append((j, prev, 'B', 'q%d' % j, 'q%d' % (j + 1))); j += 1
    nodes, branches = core_decompose(th)
    assert nodes == ['A', 'B'] and len(branches) == 3
    print("   OK  theta core: 2 nodes, 3 branches")
    ok += 1
    bodies = set()
    for r in th:
        bodies.add(r[1]); bodies.add(r[2])
    assert count_excess(th, bodies) == 0, count_excess(th, bodies)
    print("   OK  theta(4,4,4) core has body-hinge count 0")
    ok += 1
    print(f"\n   {ok} machinery checks OK")
    return 0


MODES = {'--types': mode_types, '--reduce': mode_reduce,
         '--size': mode_size, '--frame': mode_frame,
         '--witness': mode_witness, '--validate': mode_validate}


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in MODES:
        print("usage: anhr1.py [%s]" % ' | '.join(sorted(MODES)))
        return 2
    return MODES[sys.argv[1]]()


if __name__ == '__main__':
    sys.exit(main())
