"""
Phase 39 (K-slide-comb) -- the combinatorial residue of the tetrahedral
collapse: what is uniform (a base-packing theorem) and what is not (the
colouring premise).

Sibling of `kslidecl.py`, which set up the collapse and left the purely
combinatorial residue (K-slide-comb) open (workbook section (K-slide-cl)
Step C5).  This script settles that residue.  Three independent findings,
one driver each:

  --pack     (C6) THE UNIFORM CORE.  Drop the geometry's per-edge menu and
             ask only for the packing: assign to each hub edge P of
             `G* - e0` a set A_P of 6 - ell_P of the six labels so that
             three label classes are spanning trees of `G* - e0` and three
             are 2-component forests separating b from c.  This is a
             matroid-union / base-packing question (three bases of
             M(G*)/e0 plus three bases of M(G*)\\e0, edge P used 6 - ell_P
             times), and Edmonds' min-max hypothesis for it is EXACTLY
             5/6-sparsity of the subdivision -- so it holds at every class
             shape.  The driver checks the min-max inequality over every
             F subset E(G* - e0) AND builds an explicit packing.

  --k5       THE COLOURING FLANK (refutation).  `G* = K5` carries tight +
             hnoRigid length assignments -- exhibited exactly -- and
             chi(K5) = 5, so no proper 4-colouring of `G*` exists and the
             collapse decoration cannot even be started.  (K-slide-comb)
             as stated is therefore FALSE class-wide.

  --acyclic  THE ACYCLICITY FLANK (the necessary condition is stronger
             than proper colouring).  Every menu contains L_{phi u, phi w},
             so class E_{L_ij} contains ALL edges coloured {i, j}: the
             colouring must be ACYCLIC (every bicoloured subgraph a
             forest), not merely proper.  3-degeneracy gives greedy proper
             4-colourings and says nothing about acyclic ones.  The driver
             computes chi and the acyclic-4-colourability of every
             candidate `G*` in a bounded sweep and reports the shapes where
             a proper 4-colouring exists but no acyclic one does.

  --flanks   The three refutation flanks side by side, in increasing depth
             (no colouring / no acyclic colouring / colouring but no menu
             assignment), each with the stage-by-stage diagnosis and the
             per-class menu capacity ("starvation") bound.

  --k4full   Exhaustive over the whole `G* = K4` stratum, and
  --sweep     bounded (seeded) sweep over |V*| <= 5: compare the
             unrestricted packing (always solvable, --pack) against the
             menu-constrained search (`kslidecl.search_assignments`), so
             the loss is attributable to the menu alone.

  --battery  Control: the seven (K-slide) battery members must all come out
             menu-solvable (they do), so a negative verdict elsewhere is not
             a harness artifact.

Drivers (foreground, one at a time; exact integer/rational arithmetic
inherited from the imported harness, rank asserts on every object):
    python3 notes/scripts/w4/kslidecomb.py --pack
    python3 notes/scripts/w4/kslidecomb.py --k5
    python3 notes/scripts/w4/kslidecomb.py --acyclic
    python3 notes/scripts/w4/kslidecomb.py --flanks
    python3 notes/scripts/w4/kslidecomb.py --k4full
    python3 notes/scripts/w4/kslidecomb.py --sweep
    python3 notes/scripts/w4/kslidecomb.py --battery
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (_HERE, os.path.join(_HERE, '..', 'kbare'),
           os.path.join(_HERE, '..', 'escape')):
    sys.path.insert(0, _p)

from nogood_subdiv import deficiency
from pitch import paths_graph
from kbare_common import verts_of
from kslide import no_rigid_branch_union
from kslidecl import (PAIRS, opp, options_for, proper_colorings,
                      search_assignments, uf_find)


# ---------------- shapes ------------------------------------------------------

def shape_data(specs):
    """`specs[0]` is the split edge e0 = (0, 1, 3); the rest are the other
    hub paths.  Returns (edges, pmap) of the subdivision."""
    assert specs[0][0] == 0 and specs[0][1] == 1 and specs[0][2] == 3, \
        "specs[0] must be the length-3 split edge (0, 1, 3)"
    return paths_graph([3], specs[1:])


def shape_ok(specs):
    """Class membership as the (K-slide) battery certifies it: the
    subdivision is tight (def = 0, which with the count 5|E| = 6(|V|-1)
    forces 5/6-sparsity of every subgraph) and hnoRigid at branch
    granularity."""
    edges, pmap = shape_data(specs)
    nV = len(verts_of(edges))
    if 5 * len(edges) != 6 * (nV - 1):
        return None
    if deficiency(edges) != 0:
        return None
    if not no_rigid_branch_union(edges, pmap):
        return None
    return nV


def hub_graph(specs):
    n = len({h for (h1, h2, _L) in specs for h in (h1, h2)})
    return n, [(h1, h2) for (h1, h2, _L) in specs]


# ---------------- colouring invariants ---------------------------------------

def colorings(n, edges, k=4, acyclic=False):
    """Generate proper k-colourings of the simple graph (n, edges), fixing
    phi(0) = 0 and (if 0-1 is an edge) phi(1) = 1 to kill the colour
    symmetry.  `acyclic=True` additionally requires every bicoloured
    subgraph to be a forest (an ACYCLIC colouring)."""
    adj = {v: set() for v in range(n)}
    for u, w in edges:
        adj[u].add(w)
        adj[w].add(u)
    phi = {}

    def bicolored_ok(v):
        """After colouring v, no bicoloured cycle can close through v: check
        every pair (phi v, c) class for a cycle by union-find on the
        already-coloured part."""
        for c in range(k):
            if c == phi[v]:
                continue
            sel = [(u, w) for (u, w) in edges
                   if u in phi and w in phi
                   and {phi[u], phi[w]} == {phi[v], c}]
            par = {}

            def find(x):
                while par.setdefault(x, x) != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x
            for (u, w) in sel:
                ru, rw = find(u), find(w)
                if ru == rw:
                    return False
                par[ru] = rw
        return True

    def rec(v):
        if v == n:
            yield dict(phi)
            return
        top = k if v > 1 else min(v + 1, k)
        for c in range(top):
            if any(phi.get(u) == c for u in adj[v] if u in phi):
                continue
            phi[v] = c
            if not acyclic or bicolored_ok(v):
                yield from rec(v + 1)
            del phi[v]
    yield from rec(0)


def has_coloring(n, edges, k=4, acyclic=False, split=None):
    """Is there a proper (resp. acyclic) k-colouring?  `split=(b, c)` adds
    the requirement phi(b) != phi(c) (used when e0 is NOT in `edges`)."""
    for phi in colorings(n, edges, k, acyclic):
        if split is None or phi[split[0]] != phi[split[1]]:
            return phi
    return None


def chrom(n, edges, cap=6):
    for k in range(1, cap + 1):
        if has_coloring(n, edges, k) is not None:
            return k
    return None


# ---------------- (C6): the unrestricted base packing ------------------------

def comp_rank(n, F):
    """Rank of edge set F in the graphic matroid on n vertices: |V| minus
    the number of connected components of (range(n), F)."""
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (u, w) in F:
        ru, rw = find(u), find(w)
        if ru != rw:
            par[ru] = rw
    return n - len({find(x) for x in range(n)})


def same_comp(n, F, b, c):
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (u, w) in F:
        ru, rw = find(u), find(w)
        if ru != rw:
            par[ru] = rw
    return find(b) == find(c)


def packing_minmax(specs, verbose=False):
    """Edmonds' matroid-union hypothesis for the 6-fold packing, checked
    over every F subset E(G* - e0):

        sum_{P in F} (6 - ell_P)  <=  3 r_{M/e0}(F) + 3 r_{M\\e0}(F)

    with r_{M\\e0}(F) = n - comp(F) and r_{M/e0}(F) = that minus [b, c in
    the same component of F].  Returns (ok, worst_slack, tight_witnesses).
    The proof that this always holds on the class: apply 5/6-sparsity of
    the subdivision to each component of F (case b !~ c) resp. to
    F0 + e0 for the component F0 containing both b and c (case b ~ c,
    where e0 supplies exactly the missing 6 - 3 = 3).
    """
    n, _ = hub_graph(specs)
    rest = specs[1:]
    worst = None
    tight = []
    for r in range(len(rest) + 1):
        for sub in itertools.combinations(range(len(rest)), r):
            F = [(rest[i][0], rest[i][1]) for i in sub]
            lhs = sum(6 - rest[i][2] for i in sub)
            rk = comp_rank(n, F)
            rq = rk - (1 if same_comp(n, F, 0, 1) else 0)
            rhs = 3 * rq + 3 * rk
            slack = rhs - lhs
            if worst is None or slack < worst:
                worst = slack
            if slack == 0 and r > 0:
                tight.append(tuple(sub))
    if verbose:
        print(f"    min-max slack min = {worst}, "
              f"{len(tight)} tight subsets")
    return worst >= 0, worst, tight


def _uf_new(n):
    return list(range(n))


def _uf_find(par, x):
    while par[x] != x:
        par[x] = par[par[x]]
        x = par[x]
    return x


def search_unrestricted(specs, seps=None):
    """Build an UNRESTRICTED packing: assign to each edge of `G* - e0` a set
    of 6 - ell_P labels so that the three labels in `seps` carry a
    2-component forest separating b = 0 from c = 1 and the other three
    carry a spanning tree.  Menus are ignored -- this is exactly the
    matroid-union certificate of (C6), constructed.  Returns a classmap or
    None."""
    n, _ = hub_graph(specs)
    rest = specs[1:]
    if seps is None:
        # any triple containing an opposite pair works; the label names are
        # ours to choose, so (W4)'s opposite-pair condition is free.
        seps = [PAIRS[0], opp(PAIRS[0]), PAIRS[1]]
    seps = [frozenset(s) for s in seps]
    assert len(seps) == 3 and sum(1 for s in seps if opp(s) in seps) == 2, \
        "separator triple must contain exactly one opposite pair"
    cap = {p: (n - 2 if p in seps else n - 1) for p in PAIRS}
    assert sum(cap.values()) == sum(6 - L for (_a, _b, L) in rest), \
        "capacity/row-count mismatch (shape not tight?)"
    order = sorted(range(len(rest)), key=lambda i: -(6 - rest[i][2]))
    ufs = {p: _uf_new(n) for p in PAIRS}
    used = {p: 0 for p in PAIRS}
    out = {p: [] for p in PAIRS}

    def rec(k):
        if k == len(order):
            for p in PAIRS:
                if used[p] != cap[p]:
                    return False
                sep = _uf_find(ufs[p], 0) != _uf_find(ufs[p], 1)
                if sep != (p in seps):
                    return False
            return True
        i = order[k]
        h1, h2, L = rest[i]
        need = 6 - L
        avail = [p for p in PAIRS
                 if used[p] < cap[p]
                 and _uf_find(ufs[p], h1) != _uf_find(ufs[p], h2)]
        for choice in itertools.combinations(avail, need):
            undo = []
            for p in choice:
                r1, r2 = _uf_find(ufs[p], h1), _uf_find(ufs[p], h2)
                undo.append((p, r1, ufs[p][r1]))
                ufs[p][r1] = r2
                used[p] += 1
                out[p].append((h1, h2))
            if rec(k + 1):
                return True
            for (p, r1, old) in reversed(undo):
                ufs[p][r1] = old
                used[p] -= 1
                out[p].pop()
        return False

    if rec(0):
        return {p: list(out[p]) for p in PAIRS}, seps
    return None


# ---------------- members -----------------------------------------------------

# the seven (K-slide) battery members, in `kslidecl` spec form
from kslidecl import MEMBERS as CL_MEMBERS       # noqa: E402

# K5 length assignments certified tight + hnoRigid by --k5 (e0 = (0, 1, 3));
# edge order (0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4).
# The first row is the cleanest exemplar: only lengths 3 and 4 (four 3's on
# the edges at b = 0, six 4's elsewhere).  84 all-{3,4} assignments qualify;
# the last two rows show the flank is not an artifact of that pattern.
K5_LENS = [
    (3, 3, 3, 3, 4, 4, 4, 4, 4, 4),
    (3, 3, 3, 4, 3, 4, 4, 4, 4, 4),
    (3, 3, 3, 4, 4, 4, 4, 4, 4, 3),
    (3, 2, 2, 2, 3, 4, 5, 5, 5, 5),
    (3, 1, 1, 2, 5, 5, 4, 5, 5, 5),
]

K5_EDGES = [(i, j) for i in range(5) for j in range(i + 1, 5)]


def k5_specs(lens):
    out = [(0, 1, lens[0])]
    out += [(a, b, L) for (a, b), L in zip(K5_EDGES[1:], lens[1:])]
    return out


# candidate hub graphs for the sweeps: simple, connected, min degree >= 3
def candidate_graphs(nmax=6):
    for n in range(4, nmax + 1):
        allpairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        seen = set()
        for mask in range(1 << len(allpairs)):
            edges = [allpairs[i] for i in range(len(allpairs))
                     if mask >> i & 1]
            if len(edges) < (3 * n + 1) // 2:
                continue
            deg = [0] * n
            for u, w in edges:
                deg[u] += 1
                deg[w] += 1
            if min(deg) < 3:
                continue
            # connected
            seenv, st = {0}, [0]
            adj = {v: [] for v in range(n)}
            for u, w in edges:
                adj[u].append(w)
                adj[w].append(u)
            while st:
                v = st.pop()
                for u in adj[v]:
                    if u not in seenv:
                        seenv.add(u)
                        st.append(u)
            if len(seenv) != n:
                continue
            key = canon(n, edges)
            if key in seen:
                continue
            seen.add(key)
            yield n, edges


def canon(n, edges):
    best = None
    es = {frozenset(e) for e in edges}
    for perm in itertools.permutations(range(n)):
        key = tuple(sorted(tuple(sorted((perm[u], perm[w])))
                           for (u, w) in es))
        if best is None or key < best:
            best = key
    return best


# ---------------- drivers -----------------------------------------------------

def driver_pack():
    print("== (C6) the unrestricted 6-fold base packing ==")
    print("   claim: at every class shape, dropping the per-edge MENU makes")
    print("   the assignment problem always solvable -- it is a matroid")
    print("   union / base packing whose Edmonds min-max hypothesis is")
    print("   exactly 5/6-sparsity of the subdivision.\n")
    members = [(name, specs) for (name, specs) in CL_MEMBERS.values()]
    members += [(f"K5 lens {lens}", k5_specs(lens)) for lens in K5_LENS[:2]]
    allok = True
    for name, specs in members:
        nV = shape_ok(specs)
        n, _ = hub_graph(specs)
        assert nV is not None, f"{name}: not a class shape"
        ok, worst, tight = packing_minmax(specs)
        res = search_unrestricted(specs)
        assert ok, f"{name}: min-max FAILS (slack {worst})"
        assert res is not None, f"{name}: min-max holds but no packing built"
        classmap, seps = res
        sizes = sorted(len(classmap[p]) for p in PAIRS)
        assert sizes == sorted([n - 2] * 3 + [n - 1] * 3), sizes
        print(f"  {name}: |V*|={n} |V|={nV}  min-max slack >= {worst}  "
              f"({len(tight)} tight F)  packing built, class sizes {sizes}")
        allok = allok and ok
    print("\n  (C6) verified on every probed shape: min-max slack >= 0 and an")
    print("  explicit packing (3 spanning trees of G*-e0 + 3 two-component")
    print("  forests separating b|c, opposite pair among the separators).")
    assert allok


def check_properness_forced():
    """Why a PROPER colouring is forced for any tetrahedral-collapse
    decoration, not just for the (C2) dictionary: if pt(u) = pt(w) on an edge
    of length ell, the ell chain lines span fewer than ell dimensions, so the
    edge contributes more than 6 - ell rows and (W1)'s absolute row bound
    6|V_H| - 5|E_H| is unreachable.  Machine-checked at every length with
    generic interiors and generic panels."""
    import random
    from fractions import Fraction as Fr
    from kslidecl import TET, rnd3, dir_line
    from pencil_escape import wedge2, hat
    from repin import span_basis
    from kslidecl import cross3
    rng = random.Random(4242)
    p = list(TET[1])

    def gen():
        return [Fr(rng.randint(-9, 9)) for _ in range(3)]

    def pencil():
        return dir_line(p, cross3(rnd3(rng), rnd3(rng)))

    out = []
    for L in (1, 2, 3, 4, 5):
        # the (S2) limit chain of a hub path with pt(u) = pt(w) = p
        if L == 1:
            out.append((L, 'the hub-hub hinge u ^ w is 0 (undefined)'))
            continue
        if L == 2:
            x1 = gen()
            chain = [wedge2(hat(p), hat(x1)), wedge2(hat(x1), hat(p))]
        elif L == 3:
            out.append((L, 'the chord u ^ w is 0 (undefined)'))
            continue
        elif L == 4:
            x2 = gen()
            chain = [pencil(), wedge2(hat(p), hat(x2)),
                     wedge2(hat(x2), hat(p)), pencil()]
        else:
            x2, x3 = gen(), gen()
            chain = [pencil(), wedge2(hat(p), hat(x2)),
                     wedge2(hat(x2), hat(x3)), wedge2(hat(x3), hat(p)),
                     pencil()]
        d = len(span_basis(chain))
        assert d < L, f"length {L}: span {d} did not drop"
        out.append((L, f'chain span {d} < {L}: {L - d} extra row(s)'))
    for (L, msg) in out:
        print(f"    length {L}: {msg}")
    return out


def driver_k5():
    print("== the colouring flank: chi(G*) = 5 occurs in the class ==")
    print("  first: why properness is forced for ANY tetrahedral decoration")
    check_properness_forced()
    print("  => pt is injective on every G*-edge, i.e. phi is a PROPER")
    print("     4-colouring -- independent of the (C2) dictionary.\n")
    K5n = 5
    ch = chrom(K5n, K5_EDGES)
    print(f"  chi(K5) = {ch}  (so no proper 4-colouring of G* exists)")
    assert ch == 5
    good = 0
    for lens in K5_LENS:
        specs = k5_specs(lens)
        nV = shape_ok(specs)
        assert nV is not None, f"K5 {lens}: not tight+hnoRigid"
        assert sum(lens) == 6 * (10 - 5 + 1)
        # the collapse cannot start: no proper 4-colouring, so
        # search_assignments has no colouring to iterate over
        found = list(itertools.islice(search_assignments(specs), 1))
        assert not found, "unexpected assignment at a 5-chromatic shape"
        # and the unrestricted packing DOES exist (C6)
        res = search_unrestricted(specs)
        assert res is not None
        ok, worst, _t = packing_minmax(specs)
        assert ok
        print(f"  K5 lengths {lens}: |V| = {nV}, def = 0, hnoRigid = True, "
              f"e0 = (0,1,3)")
        print(f"      collapse assignments found: 0 (no proper 4-colouring)"
              f"   |   unrestricted packing: EXISTS (min-max slack "
              f">= {worst})")
        good += 1
    print(f"\n  {good}/{len(K5_LENS)} exhibited K5 shapes are class members")
    print("  => (K-slide-comb) as stated is FALSE class-wide: the obstruction")
    print("     is the colouring premise, not the packing.")
    print("  Brooks: chi(G*) >= 5 forces G* = K5 or Delta(G*) >= 5, so the")
    print("  5-chromatic flank is exactly characterised.")


def driver_acyclic():
    print("== the acyclicity flank ==")
    print("  every menu contains L_{phi u, phi w}, so class E_{L_ij} contains")
    print("  ALL edges coloured {i,j}: phi must be an ACYCLIC 4-colouring.")
    print("  (3-degeneracy gives proper greedy 4-colourings only.)\n")
    # menu check: L_ij is in every option, at every length 1..5
    for L in (1, 2, 3, 4, 5):
        for i, j in ((1, 2), (2, 4), (3, 1)):
            for _lab, cls in options_for(L, i, j):
                assert frozenset((i, j)) in cls, (L, i, j)
    print("  menu check: L_{ij} in A_P for every length 1..5 and every")
    print("  colour pair -- OK (so F_ij subset E_{L_ij} is forced)\n")
    rows = []
    for n, edges in candidate_graphs(6):
        ch = chrom(n, edges)
        ac4 = has_coloring(n, edges, 4, acyclic=True) is not None
        rows.append((n, len(edges), ch, ac4, edges))
    print(f"  {len(rows)} candidate hub graphs (simple, connected, "
          f"min deg >= 3, |V*| <= 6)")
    print("  |V*| |E*| chi acyclic-4?")
    gap = []
    for (n, m, ch, ac4, edges) in rows:
        flag = '' if (ch > 4 or ac4) else '   <-- proper 4 but NO acyclic 4'
        if flag:
            gap.append((n, m, edges))
        print(f"   {n}    {m}   {ch}   {ac4}{flag}")
    print(f"\n  shapes with chi <= 4 but no acyclic 4-colouring: {len(gap)}")
    for (n, m, edges) in gap:
        print(f"     |V*|={n} |E*|={m}: {edges}")
    return gap


def relabel(n, edges, lens, k):
    """Normalise so that e0 = edges[k] has ends 0 (= b) and 1 (= c) and sits
    first in the spec list, as `kslidecl` requires."""
    h1, h2 = edges[k]
    perm = {h1: 0, h2: 1}
    nxt = 2
    for x in range(n):
        if x not in perm:
            perm[x] = nxt
            nxt += 1
    rel = [(perm[a], perm[b], L) for (a, b), L in zip(edges, lens)]
    return [rel[k]] + [rel[i] for i in range(len(edges)) if i != k]


def split_acyclic(n, edges, k):
    """The colouring premise, exactly as the collapse needs it: phi proper on
    all of `G*` (so phi(b) != phi(c)) AND every bicoloured subgraph of
    `G* - e0` a forest (forced, since L_{phi u, phi v} lies in every menu).
    Returns a witness or None."""
    rest = [e for i, e in enumerate(edges) if i != k]
    b, c = edges[k]
    for phi in colorings(n, edges, 4, acyclic=False):
        if phi[b] == phi[c]:
            continue
        ok = True
        for (p, q) in itertools.combinations(range(4), 2):
            par = {}

            def find(x):
                while par.setdefault(x, x) != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x
            for (u, w) in rest:
                if {phi[u], phi[w]} != {p, q}:
                    continue
                ru, rw = find(u), find(w)
                if ru == rw:
                    ok = False
                    break
                par[ru] = rw
            if not ok:
                break
        if ok:
            return phi
    return None


def starvation_bound(specs, phi):
    """Per-class capacity under the menus, at a fixed colouring: how many
    edges of `G* - e0` could possibly carry the label L_pq at all.

    An edge coloured {i,j} of length ell can carry L_pq only if
      * {p,q} = {i,j}                            (mandatory, every length), or
      * |{p,q} cap {i,j}| = 1 and ell in {1,2,3} (a free menu choice), or
      * {p,q} = opp({i,j}) and ell in {2,4}      (the pt-mode / length-4 slot).
    A length-5 edge can carry ONLY its own label; a length-4 edge only its own
    and the opposite one.  Class L_pq needs n-2 (separating) or n-1 (spanning
    tree) members, so `cap_pq < n-2` for any pq is an outright obstruction."""
    n, _ = hub_graph(specs)
    cap = {p: 0 for p in PAIRS}
    for (h1, h2, L) in specs[1:]:
        ij = frozenset((phi[h1], phi[h2]))
        for p in PAIRS:
            k = len(p & ij)
            if k == 2 or (k == 1 and L in (1, 2, 3)) or (k == 0 and L in (2, 4)):
                cap[p] += 1
    return cap, n


def diagnose(specs, stage_report=True):
    """Stage-by-stage count of how far the menu-constrained search gets.
    Stages: all-forest leaves -> excess 3+z -> three separating classes ->
    an opposite pair among them -> panel budget -> local compatibility."""
    hubs = sorted({h for (h1, h2, _L) in specs for h in (h1, h2)})
    edges_ns = specs[1:]
    st = {'colourings': 0, 'forest': 0, 'excess': 0, 'seps': 0, 'opp': 0,
          'panel': 0, 'compat': 0}
    for phi in proper_colorings(specs, hubs):
        st['colourings'] += 1
        opts = [options_for(L, phi[h1], phi[h2]) for (h1, h2, L) in edges_ns]
        ufs0 = {p: {h: h for h in hubs} for p in PAIRS}

        def rec(idx, ufs, labels):
            if idx == len(edges_ns):
                st['forest'] += 1
                z = sum(1 for (h1, h2, L), lab in zip(edges_ns, labels)
                        if L == 2 and lab[0] == 'mp')
                excess, seps = [], []
                for p in PAIRS:
                    roots = {uf_find(ufs[p], h) for h in hubs}
                    excess.append(len(roots) - 1)
                    if uf_find(ufs[p], 0) != uf_find(ufs[p], 1):
                        seps.append(p)
                if sum(excess) != 3 + z:
                    return
                st['excess'] += 1
                if z == 0 and (sorted(excess) != [0, 0, 0, 1, 1, 1]
                               or len(seps) != 3):
                    return
                if z > 0 and not 3 <= len(seps) <= 3 + z:
                    return
                st['seps'] += 1
                if sum(1 for p in seps if opp(p) in seps) < 2:
                    return
                st['opp'] += 1
                req = {h: set() for h in hubs}
                for (h1, h2, L), lab in zip(edges_ns, labels):
                    if L == 1:
                        req[h1].add(phi[h2])
                        req[h2].add(phi[h1])
                    elif L == 2 and lab[0] == 'pt':
                        req[h1].add(lab[1])
                        req[h2].add(lab[1])
                if any(len(s) > 2 for s in req.values()):
                    return
                st['panel'] += 1
                for (h1, h2, L) in edges_ns:
                    if L == 3:
                        if phi[h2] in req[h1] or phi[h1] in req[h2]:
                            return
                    elif L == 4:
                        comp = {1, 2, 3, 4} - {phi[h1], phi[h2]}
                        if not comp - (req[h1] | req[h2]):
                            return
                st['compat'] += 1
                return
            (h1, h2, _L) = edges_ns[idx]
            for lab, cls in opts[idx]:
                new = {p: dict(ufs[p]) for p in cls}
                ok = True
                for p in cls:
                    r1, r2 = uf_find(new[p], h1), uf_find(new[p], h2)
                    if r1 == r2:
                        ok = False
                        break
                    new[p][r1] = r2
                if not ok:
                    continue
                merged = dict(ufs)
                merged.update(new)
                rec(idx + 1, merged, labels + [lab])
        rec(0, ufs0, [])
    if stage_report:
        print("      stages: " + "  ".join(f"{k}={v}" for k, v in st.items()))
    return st


# the three named flank exemplars (all lengths in {3, 4}, so `G` is
# triangle-free with all closed hub-neighbourhoods singletons -- the
# `hcard`/`htf` conditions the (K) consumer carries are satisfied)
FLANKS = [
    ('K5 (chi = 5)',
     [(i, j) for i in range(5) for j in range(i + 1, 5)],
     (3, 3, 3, 3, 4, 4, 4, 4, 4, 4), 0),
    ('6v11e (chi = 4, no acyclic 4-colouring)',
     [(0, 1), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
      (2, 5), (3, 4)],
     (3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4), 0),
    ('K222 octahedron (chi = 3, acyclic 4-colouring EXISTS)',
     [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4),
      (2, 5), (3, 4), (3, 5)],
     (3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4), 0),
]


def driver_flanks():
    print("== the three refutation flanks, in increasing depth ==")
    for (name, edges, lens, k) in FLANKS:
        n = len({v for e in edges for v in e})
        specs = relabel(n, edges, lens, k)
        nV = shape_ok(specs)
        assert nV is not None, f"{name}: not a class shape"
        ch = chrom(n, edges)
        sa = split_acyclic(n, edges, k)
        res = search_unrestricted(specs)
        assert res is not None, f"(C6) fails at {name}"
        print(f"\n  {name}")
        print(f"    G*: |V*|={n} |E*|={len(edges)} lengths={lens} "
              f"e0={edges[k]}  ->  |V|={nV}, def=0, hnoRigid, min ell >= 3")
        print(f"    chi(G*) = {ch};  colouring premise (proper on G*, "
              f"acyclic off e0): {'SATISFIABLE' if sa else 'UNSATISFIABLE'}")
        if sa is None:
            print("    => the collapse cannot be decorated at all")
        else:
            cap, nn = starvation_bound(specs, {v: sa[v] + 1 for v in range(n)})
            worst = min(cap.values())
            print(f"    witness phi = {[sa[v] for v in range(n)]};  "
                  f"menu capacities per class = "
                  f"{sorted(cap.values())} vs required >= {nn - 2}"
                  f"  (starved: {worst < nn - 2})")
            st = diagnose(specs)
            assert st['compat'] == 0, "expected no menu assignment"
            print("    => a colouring exists but NO menu assignment makes all"
                  " six classes forests")
        print("    unrestricted packing (C6): EXISTS")
    print("\n  All three flanks are class members by the same criterion the")
    print("  (K-slide) battery uses (def = 0, hnoRigid, both split ends hubs,")
    print("  parallel-free) and all satisfy the hcard/triangle-free")
    print("  conditions the (K) consumer carries.  (K-slide-comb) is FALSE.")


def driver_k4full():
    """Exhaustive over the whole G* = K4 stratum: every length assignment in
    {1..5}^6 with Sum ell = 18, e0 = the first length-3 edge."""
    print("== exhaustive K4 stratum: menu-constrained vs unrestricted ==")
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    tot = solv = colfail = 0
    solv_ms, unsolv_ms = set(), set()
    for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
        if sum(lens) != 18 or 3 not in lens:
            continue
        k = lens.index(3)
        specs = relabel(4, K4, lens, k)
        if shape_ok(specs) is None:
            continue
        tot += 1
        assert search_unrestricted(specs) is not None, \
            f"(C6) FAILS at K4 {lens}"
        hit = list(itertools.islice(search_assignments(specs), 1))
        if hit:
            solv += 1
            solv_ms.add(tuple(sorted(lens)))
        else:
            unsolv_ms.add(tuple(sorted(lens)))
            if split_acyclic(4, K4, k) is None:
                colfail += 1
    print(f"  class shapes (G* = K4, e0 = first length-3 edge): {tot}")
    print(f"  unrestricted packing solvable:  {tot}   ((C6), 100%)")
    print(f"  menu-constrained solvable:      {solv}")
    print(f"  menu-unsolvable:                {tot - solv}"
          f"   (of which {colfail} already fail the colouring premise)")
    print(f"  length multisets that solve somewhere:     {len(solv_ms)}")
    print(f"  length multisets that fail somewhere:      {len(unsolv_ms)}")
    print("  the ONLY all-lengths->=3 K4 shape is (3,3,3,3,3,3) (tightness"
          " forces it) and it solves; every failure carries an ell <= 2 edge.")


def driver_sweep(seed=20260805, tries=400, keep=12):
    print("== bounded class sweep: menu-constrained vs unrestricted ==")
    print(f"   seeded sample (seed {seed}); per hub graph: all-{{3,4}} length")
    print(f"   assignments exhaustively, plus <= {tries} random draws from")
    print(f"   {{1..5}} keeping the first {keep} class shapes.\n")
    import random
    tot = solv = unsolv_col = unsolv_menu = 0
    by_graph = []
    for n, edges in candidate_graphs(5):
        m = len(edges)
        target = 6 * (m - n + 1)
        if not (m <= target <= 5 * m):
            continue
        ch = chrom(n, edges)
        rng = random.Random(seed + 7 * m + n)
        cands = [lens for lens in itertools.product((3, 4), repeat=m)
                 if sum(lens) == target]
        for _ in range(tries):
            lens = tuple(rng.randint(1, 5) for _ in range(m))
            if sum(lens) == target:
                cands.append(lens)
        gt = gs = 0
        for lens in cands:
            if 3 not in lens:
                continue
            k = lens.index(3)
            specs = relabel(n, edges, lens, k)
            if shape_ok(specs) is None:
                continue
            tot += 1
            gt += 1
            assert search_unrestricted(specs) is not None, \
                f"(C6) FAILS at {edges} {lens}"
            hit = list(itertools.islice(search_assignments(specs), 1))
            if hit:
                solv += 1
                gs += 1
            elif ch is not None and ch > 4:
                unsolv_col += 1
            else:
                unsolv_menu += 1
            if gt >= keep:
                break
        by_graph.append((n, m, ch, gt, gs))
    print("  |V*| |E*| chi  shapes  menu-solvable")
    for (n, m, ch, gt, gs) in by_graph:
        print(f"   {n}    {m}   {ch}    {gt:4d}     {gs:4d}")
    print(f"\n  class shapes probed:              {tot}")
    print(f"  unrestricted packing solvable:    {tot}  ((C6), 100%)")
    print(f"  menu-constrained solvable:        {solv}")
    print(f"  unsolvable, no proper 4-colouring:{unsolv_col}")
    print(f"  unsolvable though 4-colourable:   {unsolv_menu}")


def driver_dict4():
    """(C2)'s length-4 entry is NOT forced: exhibit, exactly, a length-4
    decoration whose reciprocal space is <L_ij, L_ik> instead of the
    dictionary's <L_ij, L_opp(ij)>.

    Construction: put the free middle x2 at a generic point of the face plane
    pi(i, j, k) and take P_w = Panel(w) cap pi(i, j, k) (a pencil line at E_j
    inside that plane), while P_u stays generic in Panel(u).  Then L_ij and
    L_ik both meet all four chain lines -- L_ij and L_ik pass through E_i so
    they meet P_u and E_i v x2 automatically, and both lie in pi(i, j, k)
    together with x2 v E_j and P_w -- while the four chain lines still span a
    4-space (only three of them lie in the plane)."""
    import random
    from fractions import Fraction as Fr
    from kslidecl import (TET, plane_normal, pencil_line, tl, rnd3, add3,
                          sub3)
    from pitch import klein
    from pencil_escape import wedge2, hat
    from repin import span_basis
    print("== (C2) length-4: the entry is not forced ==")
    rng = random.Random(20260805)
    ok = 0
    for (i, j) in ((1, 2), (2, 3), (4, 1)):
        for k in sorted({1, 2, 3, 4} - {i, j}):
            pn = plane_normal(i, j, k)
            pu, pw = TET[i], TET[j]
            # x2 generic in the face plane pi(i, j, k)
            al, be = Fr(rng.randint(1, 9)), Fr(rng.randint(1, 9))
            x2 = add3(add3(pu, sub3(pw, pu), al), sub3(TET[k], pu), be)
            # panels: generic, and not the face plane itself (guard)
            nw, nu = rnd3(rng), rnd3(rng)
            for nrm_ in (nw, nu):
                assert len(span_basis([list(nrm_), list(pn)])) == 2, \
                    "panel coincides with the face plane"
            nrm = {'u': nu, 'w': nw}
            phi = {'u': i, 'w': j}
            for (end, other) in (('w', i), ('u', j)):
                # the plane-confined pencil line sits at `end`; the OTHER end
                # keeps a generic one, so the surviving extra basis line is
                # L_{other, k}
                if end == 'w':
                    Pin = pencil_line('w', phi, nrm, pn)
                    Pfree = pencil_line('u', phi, nrm, rnd3(rng))
                    chain = [Pfree, wedge2(hat(pu), hat(x2)),
                             wedge2(hat(x2), hat(pw)), Pin]
                else:
                    Pin = pencil_line('u', phi, nrm, pn)
                    Pfree = pencil_line('w', phi, nrm, rnd3(rng))
                    chain = [Pin, wedge2(hat(pu), hat(x2)),
                             wedge2(hat(x2), hat(pw)), Pfree]
                assert len(span_basis(chain)) == 4, "chain span not 4"
                got = [p for p in PAIRS
                       if all(klein(tl(p), C) == 0 for C in chain)]
                want = [frozenset((i, j)), frozenset((other, k))]
                assert sorted(map(sorted, got)) == sorted(map(sorted, want)), \
                    f"A_P = {[sorted(p) for p in got]}, wanted {want}"
                print(f"  colours ({i},{j}), k = {k}, plane pencil at "
                      f"{end}: chain span 4, A_P = "
                      f"{{{i}{j}, {other}{k}}} -- exact")
                ok += 1
    print(f"\n  {ok}/{ok} witnesses: at length 4 the reciprocal space can be")
    print("  ANY <L_ij, L_ix> with x in the complement, not only the")
    print("  dictionary's <L_ij, L_opp(ij)>.  (C2)'s \"forced\" is wrong, and")
    print("  the repaired menu is the natural route out of the starvation")
    print("  failures (route (C7) in the workbook).")


def driver_relaxed():
    """Re-run the menu search with the REPAIRED length-4 menu (validated
    geometrically by --dict4): does the extra freedom rescue the flanks?"""
    import kslidecl

    base = kslidecl.options_for

    def options_relaxed(L, i, j):
        if L != 4:
            return base(L, i, j)
        ij = frozenset((i, j))
        comp = sorted({1, 2, 3, 4} - {i, j})
        out = [(('opp',), [ij, opp(ij)])]
        for x in comp:
            out.append((('u', x), [ij, frozenset((i, x))]))
            out.append((('w', x), [ij, frozenset((j, x))]))
        return out

    orig = base
    kslidecl.options_for = options_relaxed
    try:
        print("== the repaired length-4 menu: which flanks does it rescue? ==")
        for (name, edges, lens, k) in FLANKS:
            n = len({v for e in edges for v in e})
            specs = relabel(n, edges, lens, k)
            hit = list(itertools.islice(search_assignments(specs), 1))
            print(f"  {name}: menu-solvable with repaired length-4 menu = "
                  f"{bool(hit)}")
        K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
        tot = solv = 0
        for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
            if sum(lens) != 18 or 3 not in lens:
                continue
            kk = lens.index(3)
            specs = relabel(4, K4, lens, kk)
            if shape_ok(specs) is None:
                continue
            tot += 1
            if list(itertools.islice(search_assignments(specs), 1)):
                solv += 1
        print(f"\n  exhaustive K4 stratum with the repaired menu: "
              f"{solv}/{tot} solvable")
        print("  (the pure dictionary gave 439/877)")
    finally:
        kslidecl.options_for = orig


def main():
    if '--pack' in sys.argv:
        driver_pack()
    elif '--k5' in sys.argv:
        driver_k5()
    elif '--acyclic' in sys.argv:
        driver_acyclic()
    elif '--flanks' in sys.argv:
        driver_flanks()
    elif '--k4full' in sys.argv:
        driver_k4full()
    elif '--dict4' in sys.argv:
        driver_dict4()
    elif '--relaxed' in sys.argv:
        driver_relaxed()
    elif '--sweep' in sys.argv:
        driver_sweep()
    elif '--battery' in sys.argv:
        print("== control: the seven (K-slide) battery members ==")
        for _key, (name, specs) in CL_MEMBERS.items():
            assert shape_ok(specs) is not None, name
            assert search_unrestricted(specs) is not None, name
            hit = list(itertools.islice(search_assignments(specs), 1))
            print(f"  {name}: class shape, (C6) packing EXISTS, "
                  f"menu-solvable = {bool(hit)}")
            assert hit, f"{name}: battery member should be menu-solvable"
        print("  7/7 -- the harness reproduces `kslidecl`'s solved battery.")
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
