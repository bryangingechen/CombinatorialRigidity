"""
Phase 39 W4 — the WIDENED kernels: probing (K) outside the `hnoRigid` habitat.

W4 routes 1/3 send RESIDUAL graphs (which HAVE a proper rigid subgraph) to the
split arm.  The split arm's carried kernel `hK` (`Molecule/Pencil/Escape.lean`,
`pencilPair_of_splitOff_of_habitat`) takes `hnoRigid : forall H, not
H.IsProperRigidSubgraph G 3` as an antecedent, so those routes need a
`noRigid`-free restatement.  This script measures what that costs, at the
concrete residuals `W19` (`nogood_subdiv.py`) and `S29` (`saferes.py`) and over
the whole `saferes.py --prime` pool.

Everything here is exact rational arithmetic (`fractions.Fraction`), reusing
`../escape/pencil_escape.py`'s rigidity-matrix machinery.  The one new piece of
geometry is `place_pencil_general`, which handles HUB-HUB adjacency (`escape/`'s
`place_pencil` samples every hub plane independently, which is only valid for
the double-subdivision families where no two hubs are adjacent; every residual
has hub edges).

Quantities (dictionary; `f(W) = 5|E(W)| - 6(|W|-1)`, `index(G) = f(V(G))`):

  corank(H)  = 5|E(H)| - rank(H-rows) = index(H) + def(H) at a target-rank seed
  s0         = corank of the SHARED rows, i.e. of `G - v`; the (K) non-constancy
               recon's "pure shared-row stresses".  Its item 3 derives `s0 = 0`
               from `hnoRigid` (a count circuit inside `G - v` would induce a
               proper rigid subgraph).
  dim R_a    = corank(G') - s0.  Identity proved by the counts and re-checked
               here: dim R_a = 5 + def(G') - def(G - v).
               `dim R_a >= 2` is the recon's AUTOMATIC-escape stratum.

Drivers:
    python3 notes/scripts/w4/widened.py --validate   # machinery vs the N9 record
    python3 notes/scripts/w4/widened.py --witness    # W19 and S29, exact-Q
    python3 notes/scripts/w4/widened.py --pool       # the 255-residual sweep
    python3 notes/scripts/w4/widened.py --sample     # escape rate, stratified
    python3 notes/scripts/w4/widened.py --ebound     # the (E) re-route probe
"""
import itertools
import os
import random
import sys
from fractions import Fraction as F
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (_HERE, os.path.join(_HERE, '..', 'kbare'),
           os.path.join(_HERE, '..', 'escape')):
    sys.path.insert(0, _p)

from kbare_common import verts_of, neighbors, degrees, is_2ec
import nogood_subdiv as ns
from nogood_subdiv import (deficiency, is_simple, hub_set, triangles,
                           branch_decomposition, rigid_vertex_sets,
                           induced_edges, count_matroid_rank, family_g, MULT)
from saferes import (w29, split_usable, family_core_ring, random_short, BR_CAP)
from pencil_escape import (build_rigidity, rank, left_nullspace, nullspace,
                           wedge2, hat, dot, rvec3, rquat, double_subdivide)
from localtest import in_plane_point, meet_line


# ---------------- combinatorics -------------------------------------------

def f_of(edges, W=None):
    if W is None:
        W = verts_of(edges)
    return 5 * len(induced_edges(edges, W)) - 6 * (len(W) - 1)


def count_indep(edges):
    """Is the 5-fold fiber of `edges` independent in the (6,6) count matroid?
    This is exactly the property `edgeBound_of_noRigid_of_degree_two`
    (`Induction/ReducibleVertex.lean:1270`) extracts from `hnoRigid` for the
    v-avoiding edge set, and exactly the property the (K) non-constancy recon's
    item 3 needs for `s0 = 0`."""
    if not edges:
        return True
    big = [e for e in edges for _ in range(MULT)]
    return count_matroid_rank(big, verts_of(edges)) == 5 * len(edges)


def count_corank(edges, verts=None):
    """5|E| - rank_{(6,6)}(5E) = index + def on the spanned vertex set."""
    if not edges:
        return 0
    if verts is None:
        verts = verts_of(edges)
    big = [e for e in edges for _ in range(MULT)]
    return 5 * len(edges) - count_matroid_rank(big, verts)


def removeV(edges, v):
    return [e for e in edges if v not in e]


def two_connected(edges):
    """No cut vertex.  The (K) non-constancy recon's item 4 DERIVES this from
    `hnoRigid` (a block of index >= 1 contains a circuit, hence a vertex-proper
    rigid subgraph); at a residual that derivation is unavailable, so the
    property is measured here instead."""
    V = list(verts_of(edges))
    if len(V) < 3:
        return False
    for v in V:
        rest = set(V) - {v}
        nb = neighbors(removeV(edges, v))
        seen, stack = set(), [next(iter(rest))]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(nb.get(x, ()))
        if seen != rest:
            return False
    return True


def splitOff(edges, v, a, b):
    return removeV(edges, v) + [(a, b)]


def orient(edges, v):
    """(a, b, c) for the split at the degree-2 vertex `v`: `a` is a degree-2
    neighbour (the `hsafe` end, whose star is re-hinged), `b` the other
    neighbour, `c` = a's other neighbour.  None if `v` is not usable."""
    nb = neighbors(edges)
    deg = degrees(edges)
    if deg[v] != 2:
        return None
    a, b = sorted(nb[v], key=str)
    if deg[a] != 2:
        a, b = b, a
    if deg[a] != 2:
        return None
    c = [x for x in nb[a] if x != v]
    if len(c) != 1:
        return None
    return a, b, c[0]


def split_report(edges, v):
    """Purely combinatorial diagnostics at the split `v` (no geometry)."""
    o = orient(edges, v)
    if o is None:
        return None
    a, b, c = o
    Gv, Gp = removeV(edges, v), splitOff(edges, v, a, b)
    dG, dGv, dGp = deficiency(edges), deficiency(Gv), deficiency(Gp)
    s0 = count_corank(Gv)
    corGp = count_corank(Gp)
    deg = degrees(edges)
    return {'v': v, 'a': a, 'b': b, 'c': c,
            'deg b': deg[b], 'deg c': deg[c],
            'def G': dG, 'def G-v': dGv, 'def Gp': dGp,
            's0': s0, 'corank Gp': corGp, 'dim R_a': corGp - s0,
            'dim R_a (identity)': 5 + dGp - dGv,
            'E(G-v) count-independent': s0 == 0}


# ---------------- pencil-generic placement (hub-hub aware) ----------------

def place_pencil_general(edges, rng):
    """Exact-Q pencil-generic placement of `edges`, HANDLING HUB-HUB EDGES.

    Model (same as `escape/pencil_escape.py`): a body of degree >= 3 (a "hub")
    must have its closed star coplanar; degree-<= 2 bodies are unconstrained
    (two hinge lines through one point are automatically coplanar).  So:
      * hub points are sampled freely;
      * the normal n(h) is constrained to be perpendicular to (pt u - pt h) for
        every HUB neighbour u of h -- <= 2 constraints when `hcard` holds, so
        the normal space is >= 1-dimensional -- and is sampled inside it;
      * a non-hub is placed on the intersection of its hub neighbours' planes
        (free space / a plane / a line).
    Returns None on a degenerate sample (checked: every hub star coplanar,
    every edge's two endpoints distinct)."""
    nb = neighbors(edges)
    V = sorted(nb, key=str)
    deg = {v: len(nb[v]) for v in V}
    hubs = [v for v in V if deg[v] >= 3]
    hubset = set(hubs)
    pt = {h: rvec3(rng) for h in hubs}
    nrm = {}
    for h in hubs:
        cons = [[pt[u][i] - pt[h][i] for i in range(3)]
                for u in sorted(nb[h], key=str) if u in hubset]
        basis = nullspace(cons) if cons else None
        if basis is None:
            nrm[h] = rvec3(rng)
        else:
            if not basis:
                return None                  # 3 independent hub neighbours
            co = [rquat(rng) for _ in basis]
            nrm[h] = [sum((k * bb[i] for k, bb in zip(co, basis)), F(0))
                      for i in range(3)]
        if all(x == 0 for x in nrm[h]):
            return None
    placed = dict(pt)
    for s in V:
        if s in hubset:
            continue
        hn = sorted((t for t in nb[s] if t in hubset), key=str)
        if len(hn) >= 2:
            p0, d = meet_line(pt[hn[0]], nrm[hn[0]], pt[hn[1]], nrm[hn[1]])
            if all(x == 0 for x in d):
                return None
            t = rquat(rng)
            placed[s] = [p0[i] + t * d[i] for i in range(3)]
        elif len(hn) == 1:
            placed[s] = in_plane_point(pt[hn[0]], nrm[hn[0]], rng)
        else:
            placed[s] = rvec3(rng)
    for h in hubs:                            # pencil condition
        for u in nb[h]:
            if dot(nrm[h], [placed[u][i] - pt[h][i] for i in range(3)]) != 0:
                return None
    for (u, w) in edges:                      # nonzero hinge extensors
        if placed[u] == placed[w]:
            return None
    return placed, pt, nrm, hubs, nb


def rank_at(edges, placed):
    V = sorted(set(itertools.chain.from_iterable(edges)), key=str)
    rows, er, C, idx, n = build_rigidity({'edges': edges, 'V': V, 'pt': placed})
    return rank(rows), rows, er, idx, len(V)


def pencil_rank_max(edges, seeds):
    """Max exact-Q rank over `seeds` pencil-generic placements, and the count
    target `6(|V|-1) - def`."""
    n = len(verts_of(edges))
    tgt = 6 * (n - 1) - deficiency(edges)
    best, ok = -1, 0
    for s in seeds:
        out = place_pencil_general(edges, random.Random(s))
        if out is None:
            continue
        ok += 1
        best = max(best, rank_at(edges, out[0])[0])
    return best, tgt, ok


# ---------------- the escape probe at one split ---------------------------

def escape_probe(edges, v, seeds=range(300, 340), nplace=6, maxok=8,
                 verbose=True):
    """The route's own step, measured at the split `v` of `edges`.

    For each pencil-generic seed of `G' = G - v + ab` that ATTAINS
    `target(G')`, read off the (K) non-constancy recon's diagnostics
    (corank / s0 / dim R_a / dim S / the `R_a subseteq S^perp` test, plus the
    three candidate indicators M1/M2/M3), then RE-INSERT `v` — the only
    freedom the pencil model has is `pt(v)`, confined to `Pi(b)` when `b` is a
    `G`-hub and free otherwise — and record whether SOME placement reaches
    `target(G)`.  A seed with no such placement is an escape FAILURE at that
    seed; kernel (K) only needs one escaping seed, so the reported statistic is
    the **escape rate over target-rank `G'` seeds**."""
    o = orient(edges, v)
    if o is None:
        return None
    a, b, c = o
    Gv, Gp = removeV(edges, v), splitOff(edges, v, a, b)
    nG = len(verts_of(edges))
    tgtG = 6 * (nG - 1) - deficiency(edges)
    tgtGp = 6 * (nG - 2) - deficiency(Gp)
    hubsG = hub_set(edges)
    out = {'v': v, 'a': a, 'b': b, 'c': c, 'b hub': b in hubsG,
           'c hub': c in hubsG, 'target G': tgtG, 'target Gp': tgtGp,
           'seeds ok': 0, 'seeds escaping': 0, 'placements attaining': 0,
           'placements tried': 0, 'online fail': 0, 'online total': 0,
           'M2 predicts escape': 0, 'S-criterion predicts escape': 0}
    for s in seeds:
        pl = place_pencil_general(Gp, random.Random(s))
        if pl is None:
            continue
        placed, pt, nrm, hubs, nb = pl
        rkp, rows, er, idx, _ = rank_at(Gp, placed)
        if rkp != tgtGp:
            continue
        out['seeds ok'] += 1
        out.setdefault('corank Gp', 5 * len(Gp) - rkp)
        out.setdefault('s0', 5 * len(Gv) - rank_at(Gv, placed)[0])
        e_ab = next(e for e in er if set(e) == {a, b})
        base_a = 6 * idx[a]
        Ra = []
        for lam in left_nullspace(rows):
            r = [F(0)] * 6
            for ri in er[e_ab]:
                for k in range(6):
                    r[k] += lam[ri] * rows[ri][base_a + k]
            Ra.append(r)
        ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
        L2a = [wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)]
        pen = {}
        for end, eh in ((b, bh), (c, ch)):
            if end in hubsG and end in nrm:            # the hub's own pencil
                pen[end] = [wedge2(eh, hat(placed[u])) for u in nb[end]]
            else:                                      # a free body: all lines
                pen[end] = [wedge2(eh, [F(1) if k == i else F(0)
                                        for k in range(4)]) for i in range(4)]
        S = L2a + pen[b] + pen[c]
        out.setdefault('dim R_a', rank(Ra))
        out.setdefault('dim S', rank(S))
        M1 = any(any(dot(r, w) != 0 for w in L2a) for r in Ra)
        M2 = any(any(dot(r, w) != 0 for w in pen[b]) for r in Ra)
        M3 = any(any(dot(r, w) != 0 for w in pen[c]) for r in Ra)
        out.setdefault('M1/M2/M3 (first seed)', (M1, M2, M3))
        Scrit = not all(all(dot(r, w) == 0 for w in S) for r in Ra)
        # re-insert v: pt(v) in Pi(b) when b is a G-hub, free otherwise
        esc = False
        for j in range(nplace):
            rg = random.Random(90000 + 97 * s + j)
            pv = (in_plane_point(pt[b], nrm[b], rg) if b in hubsG and b in nrm
                  else rvec3(rg))
            if pv in (placed[a], placed[b]):
                continue
            pl2 = dict(placed)
            pl2[v] = pv
            out['placements tried'] += 1
            hit = rank_at(edges, pl2)[0] == tgtG
            out['placements attaining'] += hit
            esc = esc or hit
        out['seeds escaping'] += esc
        out['M2 predicts escape'] += (M2 == esc)
        out['S-criterion predicts escape'] += (Scrit == esc)
        # the def-equal caveat's locus: pt(v) ON line(pt a, pt b)
        for j in range(2):
            rg = random.Random(70000 + 97 * s + j)
            t = rquat(rg)
            if t in (0, 1):
                continue
            pl2 = dict(placed)
            pl2[v] = [placed[a][i] + t * (placed[b][i] - placed[a][i])
                      for i in range(3)]
            if b in hubsG and b in nrm:
                if dot(nrm[b], [pl2[v][i] - pt[b][i] for i in range(3)]) != 0:
                    continue                  # the line is not inside Pi(b)
            out['online total'] += 1
            out['online fail'] += (rank_at(edges, pl2)[0] != tgtG)
        if out['seeds ok'] >= maxok:
            break
    if verbose:
        print(f"    {out}")
    return out


# ---------------- pools ----------------------------------------------------

def W19():
    return family_g(4, (0, 0, 2), (4, 4, 4))


def prime_pool():
    """The pool `saferes.py --prime` builds (both scripts' families)."""
    pool = []
    for lengths in product(range(0, 6), repeat=3):
        if list(lengths) != sorted(lengths):
            continue
        for m in (3, 4, 5, 6):
            for attach in sorted({tuple(sorted(t))
                                  for t in product(range(m), repeat=3)}):
                pool.append(ns.family_g(m, attach, lengths))
    for m in (3, 4, 5, 6):
        for q in (3, 4):
            for attach in sorted({tuple(sorted(t))
                                  for t in product(range(m), repeat=q)}):
                for ring_extra in range(0, q + 1):
                    for outer in (0, 1, 2):
                        for spoke in (0, 1, 2):
                            pool.append(family_core_ring(m, attach, ring_extra,
                                                         outer, spoke))
    rng = random.Random(99991)
    for _ in range(700):
        E = random_short(rng, rng.randint(4, 10), rng.randint(0, 5), 0, 3)
        if E is not None:
            pool.append(E)
    return pool


def residuals(pool):
    for E in pool:
        if not is_simple(E) or not is_2ec(E):
            continue
        _, br = branch_decomposition(E)
        if br is None or len(br) > BR_CAP:
            continue
        st, info = ns.classify(E)
        if not st.endswith('CANDIDATE'):
            continue
        yield E, info


# ---------------- drivers --------------------------------------------------

def validate():
    """Cross-check the new machinery against the landed N9 record."""
    print("== place_pencil_general reproduces `escape/n9.py`'s controls ==")
    import n9
    theta = n9.theta_edges()
    rk, tgt, ok = pencil_rank_max(theta, range(400, 406))
    print(f"  theta(4,4,3): pencil rank {rk} / target {tgt} "
          f"(index {f_of(theta)}, {ok} valid seeds)")
    assert rk == tgt
    r = escape_probe(theta, 30, seeds=range(410, 440), verbose=False)
    print(f"  theta(4,4,3) split at v=30: corank(Gp)={r.get('corank Gp')}"
          f" s0={r.get('s0')} dim R_a={r.get('dim R_a')} dim S={r.get('dim S')}"
          f" M1/M2/M3={r.get('M1/M2/M3 (first seed)')}"
          f" -> escaping seeds {r['seeds escaping']}/{r['seeds ok']},"
          f" placements {r['placements attaining']}/{r['placements tried']}")
    assert r['s0'] == 0 and r['dim R_a'] == 2          # the N9a record
    assert r['seeds escaping'] == r['seeds ok'] and r['seeds ok'] > 0

    print("== the tight both-ends-hubs control (dbl-subdivided K4) ==")
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    print(f"  |V|={len(allv)} |E|={len(E)} index={f_of(E)} def={deficiency(E)}")
    u, x, y, w = chains[0]
    r = escape_probe(E, x, seeds=range(440, 480), maxok=12, verbose=False)
    print(f"  split at v={x}: corank(Gp)={r.get('corank Gp')} "
          f"s0={r.get('s0')} dim R_a={r.get('dim R_a')} dim S={r.get('dim S')} "
          f"-> escaping seeds {r['seeds escaping']}/{r['seeds ok']}; "
          f"placements {r['placements attaining']}/{r['placements tried']}; "
          f"on-line failures {r['online fail']}/{r['online total']}; "
          f"M2 predicts escape {r['M2 predicts escape']}/{r['seeds ok']}, "
          f"S-criterion {r['S-criterion predicts escape']}/{r['seeds ok']}")
    assert r['s0'] == 0 and r['dim R_a'] == 1
    print("== the dim R_a identity (5 + def(G') - def(G-v)) on the pool ==")
    bad = 0
    seen = 0
    for E, _ in residuals(prime_pool()):
        for (v, _, _) in split_usable(E)[0]:
            d = split_report(E, v)
            if d is None:
                continue
            seen += 1
            if d['dim R_a'] != d['dim R_a (identity)']:
                bad += 1
    print(f"  checked {seen} (residual, split-usable v) pairs; mismatches {bad}")
    assert bad == 0
    print("VALIDATION OK")


def witness():
    for name, G in (('W19', W19()), ('S29', w29())):
        V = verts_of(G)
        print(f"== {name}: |V|={len(V)} |E|={len(G)} index={f_of(G)} "
              f"def={deficiency(G)}")
        rig = rigid_vertex_sets(G)
        print(f"  proper rigid vertex sets {rig}, f(W) = "
              f"{[f_of(G, W) for W in rig]} (count-DEPENDENT iff f > 0)")
        rk, tgt, ok = pencil_rank_max(G, range(2000, 2010))
        print(f"  PENCIL at G: max pencil-generic rank {rk} / target {tgt} "
              f"({ok} valid seeds) -> "
              f"{'ATTAINS (hK conclusion true here)' if rk == tgt else 'SHORT'}")
        usable, tf = split_usable(G)
        print(f"  triangle-free={tf}; {len(usable)} split-usable vertices")
        done = set()
        for (v, _, _) in usable:
            d = split_report(G, v)
            key = (d['deg b'], d['deg c'], d['s0'], d['corank Gp'])
            if key in done:
                continue
            done.add(key)
            print(f"  -- split at v={v}: a={d['a']} b={d['b']}(deg {d['deg b']})"
                  f" c={d['c']}(deg {d['deg c']})")
            print(f"     def(G-v)={d['def G-v']} def(Gp)={d['def Gp']} "
                  f"s0={d['s0']} corank(Gp)={d['corank Gp']} "
                  f"dim R_a={d['dim R_a']}  E(G-v) count-independent: "
                  f"{d['E(G-v) count-independent']}")
            escape_probe(G, v, seeds=range(3000, 3020))


def pool():
    from collections import Counter
    pl = list(residuals(prime_pool()))
    print(f"  residual inhabitants: {len(pl)}")
    idx = Counter()
    dRa = Counter()
    s0h = Counter()
    per = Counter()
    cross = Counter()
    rigid_cross = Counter()
    indep_ok = 0
    tight_only = 0
    ndefzero = 0
    n2conn = 0
    ndep_def = 0
    for E, info in pl:
        idx[f_of(E)] += 1
        n2conn += two_connected(E)
        rig = rigid_vertex_sets(E)
        tight_only += all(f_of(E, W) <= 0 for W in rig)
        dG = deficiency(E)
        ndefzero += (dG == 0)
        ndep_def += (dG > 0 and not count_indep(E))
        best = None
        for (v, _, _) in split_usable(E)[0]:
            d = split_report(E, v)
            if d is None:
                continue
            dRa[d['dim R_a']] += 1
            s0h[d['s0']] += 1
            cross[(dG, d['dim R_a'])] += 1
            if dG == 0:
                rigid_cross[(f_of(E), d['dim R_a'])] += 1
            best = d['dim R_a'] if best is None else max(best, d['dim R_a'])
            indep_ok += d['E(G-v) count-independent']
        per[best] += 1
    print(f"  index(G) histogram:                 {dict(sorted(idx.items()))}")
    print(f"  s0 over (residual, usable v):       {dict(sorted(s0h.items()))}")
    print(f"  dim R_a over the same pairs:        {dict(sorted(dRa.items()))}")
    print(f"  per-residual MAX dim R_a:           {dict(sorted(per.items()))}")
    print(f"  pairs with E(G-v) count-independent (the (K) recon's s0 = 0 "
          f"step): {indep_ok} / {sum(dRa.values())}")
    print(f"  residuals whose every rigid subgraph is count-TIGHT (f <= 0): "
          f"{tight_only}")
    print(f"  cross-tab (def(G), dim R_a) over pairs: "
          f"{dict(sorted(cross.items()))}")
    print(f"  RIGID residuals (def(G) = 0): {ndefzero}; their (index, dim R_a) "
          f"pairs: {dict(sorted(rigid_cross.items()))}")
    print(f"  2-connected (the (K) recon item 4 CONCLUSION, whose noRigid proof "
          f"is unavailable here): {n2conn} / {len(pl)}")
    print(f"  def(G) > 0 AND E(G) count-dependent (a combination the pinned "
          f"(K-bare) count dichotomy excludes): {ndep_def} / {len(pl)}")


def sample(maxv=22, per_stratum=3):
    """Escape rate over a stratified sample of (residual, split-usable v)
    pairs, exact-Q.  A pair "escapes at a seed" when SOME admissible `pt(v)`
    re-insertion reaches `target(G)` from that target-rank `G'` seed; kernel
    (K) needs one escaping seed."""
    from collections import Counter, defaultdict
    buckets = defaultdict(list)
    for E, _ in residuals(prime_pool()):
        if len(verts_of(E)) > maxv:
            continue
        for (v, _, _) in split_usable(E)[0]:
            d = split_report(E, v)
            if d is None:
                continue
            buckets[(d['def G'], d['dim R_a'])].append((E, v))
    tot = Counter()
    esc = Counter()
    plc = Counter()
    plt = Counter()
    for key in sorted(buckets):
        rng = random.Random(4242)
        picks = buckets[key]
        rng.shuffle(picks)
        for (E, v) in picks[:per_stratum]:
            r = escape_probe(E, v, seeds=range(5000, 5030), nplace=4, maxok=4,
                             verbose=False)
            tot[key] += r['seeds ok']
            esc[key] += r['seeds escaping']
            plc[key] += r['placements attaining']
            plt[key] += r['placements tried']
        print(f"  (def G = {key[0]}, dim R_a = {key[1]}): "
              f"{len(buckets[key])} pairs in the pool, "
              f"{min(per_stratum, len(picks))} probed -> escaping seeds "
              f"{esc[key]}/{tot[key]}, attaining placements "
              f"{plc[key]}/{plt[key]}")
    print(f"  TOTAL: escaping seeds {sum(esc.values())}/{sum(tot.values())}, "
          f"attaining placements {sum(plc.values())}/{sum(plt.values())}")


def ebound():
    """The (E) re-route probe.  `edgeBound_of_noRigid_of_degree_two` consumes
    `hnoRigid` ONLY to make the v-avoiding edge fiber count-independent, and
    then concludes `f(V(G)) <= 4` -- a statement about `G`, not about `v`.  So
    (E) follows at a residual as soon as SOME degree-2 vertex `v0` has
    `E(G - v0)` count-independent, whether or not `v0` is split-usable."""
    pl = list(residuals(prime_pool()))
    good = bad = 0
    worst = []
    for E, _ in pl:
        deg = degrees(E)
        hit = [v for v in verts_of(E) if deg[v] == 2 and count_indep(removeV(E, v))]
        if hit:
            good += 1
        else:
            bad += 1
            worst.append(E)
        assert f_of(E) <= 4, E
    print(f"  residual inhabitants: {len(pl)}")
    print(f"  ... with SOME degree-2 v0 making E(G - v0) count-independent "
          f"(so the landed edge-bound argument yields (E) verbatim): {good}")
    print(f"  ... with NO such vertex (the genuinely open remainder):      {bad}")
    for E in worst[:3]:
        print(f"    OPEN: |V|={len(verts_of(E))} f(V)={f_of(E)} {E}")
    # the same question restricted to SPLIT-USABLE vertices, for contrast
    both = 0
    for E, _ in pl:
        if any(count_indep(removeV(E, v)) for (v, _, _) in split_usable(E)[0]):
            both += 1
    print(f"  ... with a SPLIT-USABLE such vertex (would give s0 = 0 too): "
          f"{both}")
    for name, G in (('W19', W19()), ('S29', w29())):
        deg = degrees(G)
        hit = sorted(v for v in verts_of(G)
                     if deg[v] == 2 and count_indep(removeV(G, v)))
        us = sorted(v for (v, _, _) in split_usable(G)[0])
        print(f"  {name}: (E)-witness vertices {hit} (the CORE's degree-2 "
              f"vertices); overlap with the split-usable set "
              f"{sorted(set(hit) & set(us))}")


def main():
    if '--validate' in sys.argv:
        validate()
    elif '--witness' in sys.argv:
        print("== the widened kernels at W19 and S29 (exact-Q) ==")
        witness()
    elif '--pool' in sys.argv:
        print("== widened-kernel invariants over the residual pool ==")
        pool()
    elif '--sample' in sys.argv:
        print("== escape rate over a stratified sample of residual splits ==")
        sample()
    elif '--ebound' in sys.argv:
        print("== (E) via the landed edge bound at a NON-split vertex ==")
        ebound()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
