#!/usr/bin/env python3
"""WTRI (Phase 39, direction 58) — the (T) theorem's side conditions, audited on
the family a certified sweep can NEVER produce.

`notes/Pencil-W4-informal.md` §(SAFE-RES) *Steps TF1-TF6*.

WHAT THIS SCRIPT IS FOR, AND WHAT IT IS *NOT* FOR
-------------------------------------------------
(T) — *a feasible residual `G` is triangle-free* — is now a THEOREM ((TF-5)), proved
from two LANDED feasibility transfers (`PencilNondegFeasible.mono` and
`pencilNondegFeasible_induce_of_pendant_deg3`) and verified as a composition by a
compiler-checked spike.  Numerics did not and could not decide it: the sweep's own
feasibility certificate is L6b, which *requires* triangle-freeness, so a
triangle-carrying residual is invisible to a certified search by construction.  That
blind spot is not a cap and no amount of searching removes it.

So this driver deliberately does NOT hunt for a triangle-carrying residual.  It does
three things numerics *can* do here:

  --validate  the mechanical facts the proof leans on, on every graph the generators
              produce: (R5)-pendancy, the `2EC => deg(hub) >= 4` step, and the
              contraction-equals-deletion identity `G/Delta = G - x - y` (the Lean
              obligation (O4) of *Step TF6*), plus the consistency of the new
              one-plane certificate (TF-6) with BOTH landed necessary conditions.

  --audit     the (T) proof's configuration hypotheses on the BLIND-SPOT family
              itself: simple, 2EC, triangle-CARRYING graphs that pass every landed
              *necessary* test (hcard + no two-hub triangle) and therefore can never
              be certified either way by a landed lemma.  Every such graph must, by
              (TF-2)/(TF-3)/(TF-4), present the pendant-triangle configuration the
              two landed transfers consume.  A single failure would refute (T).

  --regress   whether the NEW sufficient certificate (TF-6) dissolves anything the
              project has recorded.  This is the one direction the L6b blind spot
              forbids the existing sweep from probing: enlarging the certified-
              feasible set can only *remove* residual inhabitants, so W19 and S29 —
              the `hnoGood'`-vacuity and (SAFE-RES) counterexamples — are at risk
              until measured.

Reproduce: python3 notes/scripts/w4/wtri.py --validate | --audit | --regress
"""

import random
import sys
from itertools import combinations, product

from nogood_subdiv import (contraction, degrees, hcard_ok, hub_set,
                           induced_edges, is_2ec, is_simple, neighbors,
                           provably_feasible, provably_infeasible,
                           rigid_vertex_sets, triangles, verts_of, family_d,
                           family_e, family_g, classify)
import saferes as SR


# ---------------- the new one-plane certificate (TF-6) --------------------

def closed_hub_nbhd(edges, v):
    """`G.closedHubNbhd v` = the pencil hubs among `v` itself and its neighbours."""
    nb = neighbors(edges)
    hubs = hub_set(edges)
    s = {w for w in nb.get(v, ()) if w in hubs}
    if v in hubs:
        s.add(v)
    return s


def oneplane_feasible(edges):
    """(TF-6): every closed hub-neighbourhood has <= 1 member -- equivalently the
    hubs are pairwise at distance >= 3.  Then ONE common panel `tau` and points in
    general position inside it satisfy all four `IsNondegPencilRealization`
    conjuncts, over any field with `|K| >= |V(G)|` (so over any infinite field).
    NOTE: this is a *sufficient* condition proved informally in *Step TF6*; it is not
    a landed Lean lemma, and it is NOT used by the (T) proof."""
    if not is_simple(edges):
        return False
    return all(len(closed_hub_nbhd(edges, v)) <= 1 for v in verts_of(edges))


# ---------------- pendant-triangle anatomy --------------------------------

def pendant_data(edges, t):
    """For a triangle `t` (a 3-set of vertices), return `(hub, [deg-2 pair])` when it
    is pendant in the (R5) sense -- exactly one vertex of degree >= 3 -- else None."""
    deg = degrees(edges)
    hubs = [v for v in t if deg[v] >= 3]
    if len(hubs) != 1:
        return None
    z = hubs[0]
    return z, sorted((t - {z}), key=str)


def contraction_is_deletion(edges, t):
    """The Lean obligation (O4) of *Step TF6*, combinatorial half:
    `G.rigidContract (G[Delta]) z = G.induce (V(G) \\ {x, y})`."""
    d = pendant_data(edges, t)
    if d is None:
        return None
    z, (x, y) = d
    lhs = {tuple(sorted((u, w), key=str)) for (u, w) in contraction(edges, t)}
    W = [v for v in verts_of(edges) if v not in (x, y)]
    rhs = {tuple(sorted((u, w), key=str)) for (u, w) in induced_edges(edges, W)}
    # `contraction` renames the collapsed class to 'v*'; the identity is up to that
    # single renaming z -> 'v*'.
    rhs = {tuple(sorted(('v*' if u == z else u, 'v*' if w == z else w), key=str))
           for (u, w) in rhs}
    return lhs == rhs


def pendant_deg3_config(edges, t):
    """(TF-4): after deleting ONE of the triangle's two degree-2 vertices, does the
    LANDED `pencilNondegFeasible_induce_of_pendant_deg3` configuration hold?
    Requires `deg z = 4` in `G`; returns None when it does not apply."""
    d = pendant_data(edges, t)
    if d is None:
        return None
    z, (x, y) = d
    deg = degrees(edges)
    if deg[z] != 4:
        return None
    H1 = induced_edges(edges, [v for v in verts_of(edges) if v != x])
    dH1 = degrees(H1)
    nbH1 = neighbors(H1)
    V1 = {v for v in verts_of(edges) if v not in (x, y)}
    crossing = [e for e in H1 if (e[0] in V1) != (e[1] in V1)]
    outside = set(nbH1[z]) - {y}
    return (dH1[z] == 3                      # hdeg
            and dH1[y] == 1                  # y is pendant in H1
            and len(crossing) == 1           # hcut : ncard <= 1
            and len(outside) == 2            # w1 != w2
            and is_simple(H1))               # hSimple


def mono_demotion_ok(edges, t):
    """(TF-3): at `deg z >= 5` the LANDED `PencilNondegFeasible.mono` applies to
    `G.induce (V \\ {x,y})` outright -- every `G`-hub of the subgraph stays a hub."""
    d = pendant_data(edges, t)
    if d is None:
        return None
    z, (x, y) = d
    deg = degrees(edges)
    if deg[z] < 5:
        return None
    W = [v for v in verts_of(edges) if v not in (x, y)]
    H = induced_edges(edges, W)
    dH = degrees(H)
    hubs = hub_set(edges)
    return all(dH.get(v, 0) >= 3 for v in W if v in hubs)


# ---------------- generators: the blind-spot family -----------------------

def cycle(m, tag='c'):
    return [(f'{tag}{i}', f'{tag}{(i + 1) % m}') for i in range(m)]


def attach_triangle(edges, v, tag):
    return edges + [(v, f'x{tag}'), (v, f'y{tag}'), (f'x{tag}', f'y{tag}')]


def subdivide(edges, k):
    """Subdivide EVERY edge `k` times (k >= 0)."""
    if k == 0:
        return list(edges)
    out = []
    for i, (u, w) in enumerate(edges):
        prev = u
        for j in range(k):
            nxt = f's{i}_{j}'
            out.append((prev, nxt))
            prev = nxt
        out.append((prev, w))
    return out


def blindspot_pool(seed=20260901):
    """Simple, 2EC, TRIANGLE-CARRYING graphs that pass every landed NECESSARY test
    (`hcard` and no two-hub triangle), i.e. exactly the graphs whose feasibility no
    landed lemma decides in either direction.  Built by hanging pendant triangles on
    subdivided cores -- the only way to get a triangle past (R5) at all."""
    pool, rng = [], random.Random(seed)
    cores = []
    for m in range(3, 9):
        cores.append(cycle(m))
    for m in (3, 4, 5):
        for L in (0, 1, 2):
            cores.append(family_d(m, (0, 1), L))
            cores.append(family_e(L + 2, 2, 1))
    for m in (4, 5):
        for lengths in ((2, 2, 2), (3, 3, 3), (4, 4, 4)):
            cores.append(family_g(m, (0, 0, 2), lengths))
    for _ in range(240):
        nh = rng.randint(3, 7)
        base = cycle(nh, 'r')
        for _ in range(rng.randint(0, 3)):
            a, b = rng.sample(range(nh), 2)
            base.append((f'r{a}', f'r{b}'))
        cores.append(subdivide(base, rng.randint(0, 3)))
    for core in cores:
        V = sorted(verts_of(core), key=str)
        if not V:
            continue
        for k in (1, 2):
            for anchors in combinations(range(len(V)), k):
                E = list(core)
                for j, a in enumerate(anchors):
                    E = attach_triangle(E, V[a], f'{j}')
                pool.append(E)
        # the bowtie shape: two petals at the SAME vertex
        for a in range(min(len(V), 3)):
            E = attach_triangle(attach_triangle(list(core), V[a], '0'), V[a], '1')
            pool.append(E)
    out, seen = [], set()
    for E in pool:
        key = tuple(sorted((tuple(sorted(e, key=str)) for e in E), key=str))
        if key in seen:
            continue
        seen.add(key)
        if not is_simple(E) or not is_2ec(E):
            continue
        if len(verts_of(E)) < 3:
            continue
        if not triangles(E):
            continue
        if provably_infeasible(E) is not None:   # landed-refuted: not the blind spot
            continue
        out.append(E)
    return out


# ---------------- modes ---------------------------------------------------

def validate():
    print("== --validate: the mechanical facts *Steps TF2-TF4* lean on ==")
    pool = blindspot_pool()
    n_tri = n_pend = n_deg4up = n_ident = 0
    bad = []
    for E in pool:
        for t in triangles(E):
            n_tri += 1
            d = pendant_data(E, t)
            if d is None:
                bad.append(('not-pendant', E, t))
                continue
            n_pend += 1
            z, _ = d
            if degrees(E)[z] < 4:
                bad.append(('hub-degree-lt-4', E, t))
                continue
            n_deg4up += 1
            if contraction_is_deletion(E, t) is not True:
                bad.append(('contract-ne-delete', E, t))
                continue
            n_ident += 1
    print(f"  blind-spot instances generated:                     {len(pool)}")
    print(f"  triangles examined (the DENOMINATOR below):         {n_tri}")
    print(f"  ... pendant, i.e. exactly one hub [(R5)]:           {n_pend}")
    print(f"  ... hub degree >= 4 [2EC, *Step TF2*]:              {n_deg4up}")
    print(f"  ... G/Delta == G - x - y [(O4), *Step TF6*]:        {n_ident}")
    print("== one-plane certificate (TF-6) vs the two landed NECESSARY conditions ==")
    n_op = n_ok = 0
    for E in pool:
        if not oneplane_feasible(E):
            continue
        n_op += 1
        if hcard_ok(E) and provably_infeasible(E) is None:
            n_ok += 1
        else:
            bad.append(('oneplane-vs-landed', E, None))
    print(f"  instances the one-plane criterion certifies:         {n_op}")
    print(f"  ... consistent with hcard AND no-two-hub-triangle:   {n_ok}")
    print(f"  FAILURES: {len(bad)}")
    for tag, E, t in bad[:5]:
        print(f"   {tag}: t={t} E={sorted(E, key=str)}")
    return not bad


def audit():
    print("== --audit: the (T) proof's configuration on the BLIND-SPOT family ==")
    print("   (simple, 2EC, triangle-CARRYING, hcard, no two-hub triangle -- no")
    print("    landed lemma decides feasibility in either direction here)")
    pool = blindspot_pool()
    n_tri = n_simple_c = n_deg4 = n_deg4_ok = n_deg5 = n_deg5_ok = 0
    bad = []
    for E in pool:
        deg = degrees(E)
        for t in triangles(E):
            n_tri += 1
            d = pendant_data(E, t)
            if d is None:
                bad.append(('not-pendant', E, t))
                continue
            z, (x, y) = d
            c = contraction(E, t)
            if is_simple(c):
                n_simple_c += 1
            else:
                bad.append(('contraction-not-simple', E, t))
            if deg[z] == 4:
                n_deg4 += 1
                if pendant_deg3_config(E, t) is True:
                    n_deg4_ok += 1
                else:
                    bad.append(('pendant-deg3-config', E, t))
            else:
                n_deg5 += 1
                if mono_demotion_ok(E, t) is True:
                    n_deg5_ok += 1
                else:
                    bad.append(('mono-demotion', E, t))
    print(f"  blind-spot instances:                               {len(pool)}")
    print(f"  pendant triangles examined (the DENOMINATOR):        {n_tri}")
    print(f"  ... contraction G/Delta simple:                     {n_simple_c}")
    print(f"  hub degree == 4  [route: the landed deg-3 steering]: {n_deg4}")
    print(f"  ... pendant-deg-3 config holds in G - x:            {n_deg4_ok}")
    print(f"  hub degree >= 5  [route: PencilNondegFeasible.mono]: {n_deg5}")
    print(f"  ... every demoted G-hub stays a hub:                {n_deg5_ok}")
    print(f"  FAILURES (any one would REFUTE (T)): {len(bad)}")
    for tag, E, t in bad[:5]:
        print(f"   {tag}: t={t} E={sorted(E, key=str)}")
    print("  CAP/BLIND-SPOT DISCLOSURE: this is an audit of the theorem's")
    print("  hypotheses, not a search for a counterexample.  A residual carrying a")
    print("  triangle cannot appear in ANY certified sweep (L6b requires")
    print("  triangle-freeness), so emptiness here is not evidence for (T) and")
    print("  fullness is not proof; the proof is *Steps TF2-TF5*.")
    return not bad


def recorded_pool():
    """The pool `saferes.py --prime` sweeps -- its generator list, reproduced here so
    the regression runs over the residual inhabitants the project has actually
    RECORDED (all triangle-free), not over this script's blind-spot family.

    Duplicated from `saferes.prime()`, which builds its pool inline and returns
    nothing -- recorded as harness debt in `notes/scripts/README.md` *Harness debt*.
    If that debt is ever paid, the accessor below is used instead."""
    import nogood_subdiv as ns
    if hasattr(SR, 'prime_pool'):
        return SR.prime_pool()
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
                            pool.append(SR.family_core_ring(m, attach, ring_extra,
                                                            outer, spoke))
    rng = random.Random(99991)
    for _ in range(700):
        E = SR.random_short(rng, rng.randint(4, 10), rng.randint(0, 5), 0, 3)
        if E is not None:
            pool.append(E)
    out = []
    for E in pool:
        if not is_simple(E) or not is_2ec(E):
            continue
        _, br = SR.branch_decomposition(E)
        if br is None or len(br) > SR.BR_CAP:
            continue
        st, _ = classify(E)
        if st.endswith('CANDIDATE'):
            out.append(E)
    return out


def regress():
    print("== --regress: does the NEW one-plane certificate (TF-6) dissolve")
    print("   anything the project has RECORDED? ==")
    W19 = family_g(4, (0, 0, 2), (4, 4, 4))
    S29 = SR.w29()
    dissolved_named = 0
    for name, E in (('W19', W19), ('S29', S29)):
        st, _ = classify(E)
        print(f"  {name}: landed classify = {st}; one-plane(G) = "
              f"{oneplane_feasible(E)}")
        for W in rigid_vertex_sets(E):
            c = contraction(E, W)
            new_cert = (is_simple(c) and not provably_feasible(c)
                        and oneplane_feasible(c))
            dissolved_named += new_cert
            print(f"    proper rigid W={W}: simple={is_simple(c)} "
                  f"L6b/L7c-3-feasible={provably_feasible(c)} "
                  f"one-plane={oneplane_feasible(c)} "
                  f"landed-infeasible={provably_infeasible(c)}")
    pool = recorded_pool()
    changed, n_tri = 0, 0
    for E in pool:
        if triangles(E):
            n_tri += 1
        for W in rigid_vertex_sets(E):
            c = contraction(E, W)
            if is_simple(c) and not provably_feasible(c) and oneplane_feasible(c):
                changed += 1
                print(f"    DISSOLVED: |V|={len(verts_of(E))} at W={W}")
                break
    print(f"  recorded residual inhabitants re-classified:        {len(pool)}")
    print(f"  ... of which triangle-CARRYING [(T) predicts 0]:    {n_tri}")
    print(f"  ... dissolved by the new (TF-6) certificate:        {changed}")
    print(f"  W19 / S29 contractions newly certified:             {dissolved_named}")
    print("  DENOMINATOR NOTE: the recorded 255/255 (SAFE-RES') figure is over")
    print("  TRIANGLE-FREE certified inhabitants only.  It was never evidence for")
    print("  (T) and (T) does not touch it; what it now inherits is a THEOREM")
    print("  (TF-5) in place of an open gap.  The L6b blind spot is NOT a cap:")
    print("  no sweep, at any size, can exhibit a triangle-carrying residual.")
    return changed == 0 and dissolved_named == 0 and n_tri == 0


def main():
    modes = {'--validate': validate, '--audit': audit, '--regress': regress}
    args = [a for a in sys.argv[1:] if a in modes] or list(modes)
    ok = True
    for a in args:
        ok = modes[a]() and ok
        print()
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")


if __name__ == '__main__':
    main()
