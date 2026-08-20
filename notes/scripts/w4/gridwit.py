"""§(K-grid) fan-out direction G driver — (GR-4)/(GR-6), the tight-stratum
residual attacked as an argument.

A `w4/` leaf beside `grid.py`, importing it READ-ONLY (README §2).  Run from
the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --formula    # (GR-7)/(GR-8): the interpolation factorization + the unified bound family, pool-exact
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --treetriple # (GR-9)/(GR-10): the tree-triple certificate hunt over the full census pool
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --wide       # cheap kill (ii): generic dim Z vs max(bounds) on a widened colouring pool
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --validate   # all three

Argument state: `notes/Pencil-informal-grid.md` §(K-grid) Steps G8–G13 /
labels (GR-7)–(GR-11) (fan-out direction G, landed 2026-08-06).

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--formula   (GR-7): at every legal both-forest colouring-block of the 5-shape
            pool,  dim Z = a + (M − 3h) + dim W  exactly, where a = Σ_X
            dim(cut ∩ K^X), M = Σ_X dim H_X, h = cycle rank of the contracted
            multigraph, and W = the space of cycle-space-valued polynomials
            Ψ(t) = φ0 + tφ1 + t²φ2 with Ψ(t_X) ⊥ H_X for every class X —
            computed as the kernel of an independent m × 3h matrix; and
            (GR-8): for every sub-multigraph C-witness (all class unions, all
            node-induced subgraphs),  dim W ≥ g(C) = 3·dim C − Σ_X r_X(C),
            with the structured maximum reproducing max((a),(b),(c)) exactly
            on the pool (any strict excess is printed as a FINDING, not an
            error: it would repair (GR-4)'s stated family).

--treetriple (GR-9): whenever a filter-passing colouring's classes partition,
            in BOTH blocks, into three groups whose pairwise unions are
            spanning trees of the contracted multigraph, the configuration
            reaches the Tay target at a seeded rational parameter draw
            (asserted — this is the certificate theorem's testable
            consequence); and (GR-10), the measured half: at how many of the
            907 censused tight class shapes does such a colouring exist?

--wide      cheap kill (ii): a colouring-block anywhere with generic dim Z
            strictly above max((a),(b),(c)) — hunted over a widened pool that
            includes NON-filter-passing legal colourings; every candidate
            overshoot is re-tested at 8 extra parameter draws and then
            searched for a (GR-8) structured witness before being reported.

Exact ℚ throughout (fractions.Fraction; ℚ(i) only inside closure's rank
probes).  The rngs are seeded per mode and the seeds printed.  No `set` is
printed.  σ-fixed configurations are CONSTRUCTED existence witnesses; nothing
here is quoted as a rate over sampled placements, so `repin.star_generic`
gating does not bind any figure below ((AC-9): σ-fixed points are never
composite-guard generic; rank attainment at one exact rational point
certifies the generic chart rank by lower semicontinuity).
"""
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank                                            # noqa: E402
from kbare_common import verts_of                                     # noqa: E402
import closure                                                        # noqa: E402
from closure import colourings, combinatorial_filter, cycle_rank      # noqa: E402
import grid                                                           # noqa: E402
from grid import (TRIES_SEED, block_data, census_shapes,              # noqa: E402
                  class_union_bounds, dim_Z, dim_Z_generic,
                  dn_sparsity_bound, fundamental_cycles, rank_at_params,
                  spline_pool)

WIT_SEED = 20260806


# ----------------------------------------------------- (GR-7): dim W etc. --

def dim_W(bd, sval=None):
    """dim of the interpolation space W = {Ψ = φ0 + tφ1 + t²φ2, φ_p in the
    cycle space of the contracted multigraph : Ψ(t_X) ⊥ H_X for all X}.

    Conditions are one row per edge e (the spanning set {πδ_e} of H_X):
    Σ_p s_{X(e)}^p · φ_{p,e} = 0, with φ_p = Σ_i λ_{p,i} z_i over the
    fundamental-cycle basis.  m rows × 3h unknowns; INDEPENDENT of grid.dim_Z
    (that one is a 3h-row × m-column kernel over the edge space)."""
    m = len(bd['E'])
    s = bd['s'] if sval is None else sval
    zb = fundamental_cycles(bd['nodes'], bd['ced'])
    h = len(zb)
    assert h == bd['h']
    if h == 0:
        return 0
    rows = []
    for k in range(m):
        row = []
        for p in range(3):
            sp = s[bd['cls'][k]] ** p
            for z in zb:
                row.append(F(z.get(k, 0)) * sp)
        rows.append(row)
    return 3 * h - rank(rows)


def a_and_M(bd, edges, allverts):
    """a = Σ_X dim(cut(H₊) ∩ K^X) = Σ_X (|X| − dim H_X), and M = Σ_X dim H_X
    = m − a.  dim H_X computed as in grid.class_union_bounds (comp of the
    FULL graph minus the class edges)."""
    by_cls = {}
    for k in range(len(bd['E'])):
        by_cls.setdefault(bd['cls'][k], []).append(bd['E'][k])
    eset = list(edges)
    a = 0
    for c in sorted(by_cls):
        Fe = set(by_cls[c])
        rest = [e for e in eset if e not in Fe]
        dh = len(Fe) - (grid.comp_count(allverts, rest) - 1)
        a += len(Fe) - dh
    return a, len(bd['E']) - a


def subgraph_g(bd, edge_idx):
    """g(C) = 3·dim C − Σ_X r_X(C) for C = the FULL cycle space of the
    sub-multigraph on the given contracted-edge indices (all nodes kept:
    isolated nodes do not change the cycle space).  r_X(C) = cr(F) − cr(F∖X):
    the kernel of the restriction-to-X map is the cycle space of F minus X's
    edges.  Pure cycle_rank arithmetic — no matrices."""
    nodes = bd['nodes']
    Fed = [bd['ced'][k] for k in edge_idx]
    crF = cycle_rank(nodes, Fed)
    if crF == 0:
        return 0
    tot = 3 * crF
    cls_here = sorted({bd['cls'][k] for k in edge_idx})
    for c in cls_here:
        Fmx = [bd['ced'][k] for k in edge_idx if bd['cls'][k] != c]
        tot -= crF - cycle_rank(nodes, Fmx)
    return tot


def structured_beta(bd, subset_cap=16):
    """max g(C) over the two structured witness families of (GR-8):
    (i) class unions (edge subgraphs on all nodes), (ii) node-induced
    subgraphs.  Returns (best, partial)."""
    m = len(bd['E'])
    cids = sorted(set(bd['cls']))
    L = len(cids)
    best = 0
    partial = L > subset_cap or len(bd['nodes']) > subset_cap
    # (i) class unions
    csubs = ([itertools.combinations(cids, r) for r in range(1, L + 1)]
             if L <= subset_cap else
             [itertools.combinations(cids, r) for r in (1, 2, L)])
    for it in csubs:
        for cs in it:
            csset = set(cs)
            idx = [k for k in range(m) if bd['cls'][k] in csset]
            best = max(best, subgraph_g(bd, idx))
    # (ii) node-induced subgraphs
    nodes = bd['nodes']
    if len(nodes) <= subset_cap:
        nsubs = [itertools.combinations(nodes, r)
                 for r in range(2, len(nodes) + 1)]
    else:
        nsubs = [itertools.combinations(nodes, r) for r in (2, 3)]
    for it in nsubs:
        for S in it:
            ss = set(S)
            idx = [k for k in range(m)
                   if bd['ced'][k][0] in ss and bd['ced'][k][1] in ss]
            if idx:
                best = max(best, subgraph_g(bd, idx))
    return best, partial


def leg_formula():
    """[GRW-1] (GR-7) + (GR-8) on the 5-shape pool (the 688 blocks)."""
    print("[GRW-1] (GR-7) factorization + (GR-8) unified bounds, 5-shape pool")
    rng = random.Random(WIT_SEED + 1)
    blocks = ident = 0
    beta_eq = beta_gt = 0
    for name, edges in spline_pool():
        allverts = sorted(verts_of(edges), key=str)
        cols, _ = colourings(edges)
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                m = len(bd['E'])
                a, M = a_and_M(bd, edges, allverts)
                h = bd['h']
                # (GR-7) at the construction labels AND at a random draw
                for sv in (None,
                           {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                            for c in set(bd['cls'])}):
                    z = dim_Z(bd, sval=sv)
                    w = dim_W(bd, sval=sv)
                    assert z == a + (M - 3 * h) + w, \
                        f"{name}: (GR-7) fails ({z} != {a}+{M - 3 * h}+{w})"
                    ident += 1
                # (GR-8): structured β-max vs the (GR-3) bounds, generically
                zg = dim_Z_generic(bd, rng)
                beta, part1 = structured_beta(bd)
                b_cls, b_cnt, part2 = class_union_bounds(edges, allverts, bd)
                b_dn, part3 = dn_sparsity_bound(bd)
                lo_old = max(b_cls, b_cnt, b_dn, 0)
                lo_beta = max(a, a + (M - 3 * h) + beta, 0)
                assert zg >= lo_beta, \
                    f"{name}: proven (GR-8) bound exceeds generic dim Z"
                assert lo_beta >= lo_old or part1, \
                    f"{name}: structured β fails to subsume (GR-3) " \
                    f"({lo_beta} < {lo_old})"
                if lo_beta == lo_old:
                    beta_eq += 1
                else:
                    beta_gt += 1
                    print(f"  FINDING {name}: structured β = {lo_beta} > "
                          f"max((a),(b),(c)) = {lo_old}, generic dim Z = {zg}")
                blocks += 1
    print(f"  colouring-blocks: {blocks}; (GR-7) identity exact "
          f"{ident}/{ident} (construction + random labels)")
    print(f"  (GR-8) structured max == max((a),(b),(c)): {beta_eq}; "
          f"strictly above: {beta_gt}")
    print("  (dim W from the m × 3h interpolation matrix — independent of")
    print("   grid.dim_Z's 3h × m edge-space kernel)")
    print()


# ------------------------------- (GR-9)/(GR-10): the tree-triple hunt -----

# `tree_triple` MOVED DOWN to `grid` on 2026-08-20 (the harness move-down
# round, slice 2): three consumers -- this module, `gridcol`, `packmm` (and
# `oschu`'s local import) -- past README §2 rule 2's trigger.  Re-exported
# here, so every `from gridwit import tree_triple` keeps working and this
# module's own (GR-9)/(GR-10) figures are unchanged.
from grid import tree_triple                                          # noqa: E402,F401


def leg_treetriple(cap_probe=48, col_cap=1 << 16):
    """[GRW-2] the certificate hunt: (GR-9) asserted, (GR-10) measured."""
    print(f"[GRW-2] tree-triple certificates over the census pool "
          f"(seed {WIT_SEED}, probe cap {cap_probe}/shape)")
    tot = certified = 0
    capped_shapes = 0
    first_hist = {}
    misses = []
    groups_count = {}
    for label, edges in census_shapes():
        grp = ('theta' if label.startswith('theta') else
               'K4-stratum' if label.startswith('K4') else
               'V5-sweep' if label.startswith('V5') else 'V6-sweep')
        groups_count[grp] = groups_count.get(grp, 0) + 1
        tot += 1
        allverts = sorted(verts_of(edges), key=str)
        target = 6 * (len(allverts) - 1)
        cols, odd = colourings(edges, cap=col_cap)
        assert not odd and cols is not None
        probed = 0
        hit = None
        any_cap = False
        for col in cols:
            if combinatorial_filter(edges, allverts, col):
                continue
            if probed >= cap_probe:
                break
            probed += 1
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            certs = []
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                tt, capped = tree_triple(bd)
                any_cap = any_cap or capped
                if tt is None:
                    break
                n_c = bd['n_c']
                for i in range(3):
                    pair = tt[i] + tt[(i + 1) % 3]
                    assert len(pair) == n_c - 1 and \
                        cycle_rank(bd['nodes'], pair) == 0, \
                        f"{label}: pair-union is not a spanning tree"
                certs.append(tt)
            if len(certs) == 2:
                # (GR-9): the certificate FORCES the Tay target at a
                # generic draw; verify at seeded rational draws.
                rng = random.Random(WIT_SEED * 17 + len(allverts))
                got = False
                for _ in range(3):
                    r = rank_at_params(edges, allverts, col, rng)
                    if r == target:
                        got = True
                        break
                assert got, f"{label}: certified colouring missed the " \
                    "target at 3 rational draws -- (GR-9) is FALSE or a bug"
                hit = probed
                break
        if hit is not None:
            certified += 1
            first_hist[hit] = first_hist.get(hit, 0) + 1
        else:
            if any_cap:
                capped_shapes += 1
            misses.append((label, len(allverts), len(edges), probed,
                           any_cap))
    print(f"  shapes censused : {tot}")
    for grp in sorted(groups_count):
        print(f"    {grp:12s}: {groups_count[grp]}")
    print(f"  BOTH-block tree-triple certificate found : {certified}/{tot}")
    hist = ', '.join(f"{k}:{v}" for k, v in sorted(first_hist.items()))
    print(f"  first-certified colouring histogram: {hist}")
    if misses:
        print(f"  shapes with NO certificate within caps: {len(misses)} "
              f"(of which DFS-capped: {capped_shapes})")
        for (label, nv, ne, probed, cap) in misses[:20]:
            print(f"    MISS {label}  |V|={nv} |E|={ne} probed={probed}"
                  f"{' (capped)' if cap else ''}")
    else:
        print("  every censused tight class shape carries a filter-passing")
        print("  colouring with tree-triple certificates in BOTH blocks:")
        print("  at each such shape, generic target rank is PROVEN (GR-9),")
        print("  not merely measured -- the (GR-10) statement holds on the")
        print("  whole census pool.")
    print()


# ------------------------------------------ cheap kill (ii): --wide -------

def structured_beta_which(bd, subset_cap=16):
    """As structured_beta, but also report WHICH family attains the max:
    'union', 'induced', 'both' (or '-' when best = 0)."""
    m = len(bd['E'])
    cids = sorted(set(bd['cls']))
    L = len(cids)
    best_u = best_i = 0
    if L <= subset_cap:
        for r in range(1, L + 1):
            for cs in itertools.combinations(cids, r):
                csset = set(cs)
                idx = [k for k in range(m) if bd['cls'][k] in csset]
                best_u = max(best_u, subgraph_g(bd, idx))
    nodes = bd['nodes']
    if len(nodes) <= subset_cap:
        for r in range(2, len(nodes) + 1):
            for S in itertools.combinations(nodes, r):
                ss = set(S)
                idx = [k for k in range(m)
                       if bd['ced'][k][0] in ss and bd['ced'][k][1] in ss]
                if idx:
                    best_i = max(best_i, subgraph_g(bd, idx))
    best = max(best_u, best_i)
    which = ('-' if best == 0 else
             'both' if best_u == best_i == best else
             'union' if best_u == best else 'induced')
    return best, which


def exemplar_detail(label, edges, allverts, bd, lo):
    """Print the smallest attaining witness sub-multigraph of the unified
    family at one overshoot block: its class multiset, cycle rank, and
    per-class restriction ranks — the mechanism, exhibited.  `lo` is the
    Z-level (GR-3) max; a witness must satisfy a + (M−3h) + g(C) > lo."""
    m = len(bd['E'])
    a, M = a_and_M(bd, edges, allverts)
    thresh = lo - a - (M - 3 * bd['h'])       # need g(C) > thresh
    cids = sorted(set(bd['cls']))
    best = None
    for r in range(1, len(cids) + 1):
        for cs in itertools.combinations(cids, r):
            csset = set(cs)
            idx = [k for k in range(m) if bd['cls'][k] in csset]
            g = subgraph_g(bd, idx)
            if g > thresh and (best is None or len(idx) < best[0]):
                best = (len(idx), 'union', sorted(cs), idx, g)
    for r in range(2, len(bd['nodes']) + 1):
        for S in itertools.combinations(bd['nodes'], r):
            ss = set(S)
            idx = [k for k in range(m)
                   if bd['ced'][k][0] in ss and bd['ced'][k][1] in ss]
            if idx:
                g = subgraph_g(bd, idx)
                if g > thresh and (best is None or len(idx) < best[0]):
                    best = (len(idx), 'induced', sorted(ss), idx, g)
    assert best is not None, f"{label}: no unified witness above (GR-3)"
    ne, fam, spec, idx, g = best
    Fed = [bd['ced'][k] for k in idx]
    crF = cycle_rank(bd['nodes'], Fed)
    parts = []
    for c in sorted({bd['cls'][k] for k in idx}):
        Fmx = [bd['ced'][k] for k in idx if bd['cls'][k] != c]
        parts.append(f"class {c}: {sum(1 for k in idx if bd['cls'][k] == c)}"
                     f" edges, r_X = {crF - cycle_rank(bd['nodes'], Fmx)}")
    print(f"    EXEMPLAR {label}: smallest {fam} witness on {spec}, "
          f"|F| = {ne} contracted edges, dim C = {crF}, "
          f"g(C) = 3*{crF} - Σr_X = {g}; dim Z bound "
          f"a + (M-3h) + g = {a} + {M - 3 * bd['h']} + {g} > {lo}")
    for p in parts:
        print(f"      {p}")


def leg_wide(col_cap=1 << 16, per_shape=12, stride=6):
    """[GRW-3] generic dim Z vs max((a),(b),(c)) on a widened pool that
    includes NON-filter-passing legal both-forest colourings."""
    print(f"[GRW-3] (GR-4) overshoot hunt, widened pool "
          f"(seed {WIT_SEED}, {per_shape} colourings/shape, "
          f"K4 stride {stride})")
    rng = random.Random(WIT_SEED + 5)
    k4_seen = 0
    shapes = blocks = agree = 0
    expl = unexpl = 0
    fam_count = {}
    witnesses = []
    exemplar_todo = None
    for label, edges in census_shapes():
        if label.startswith('K4'):
            k4_seen += 1
            if k4_seen % stride:
                continue
        allverts = sorted(verts_of(edges), key=str)
        cols, odd = colourings(edges, cap=col_cap)
        assert not odd and cols is not None
        legal = []
        for col in cols:
            EA = [e for e in edges if col[e] == 'A']
            EB = [e for e in edges if col[e] == 'B']
            if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
                continue
            if closure.build_fixed_config(edges, allverts, col) is None:
                continue
            legal.append(col)
        if not legal:
            continue
        shapes += 1
        if len(legal) > per_shape:
            legal = ([legal[i] for i in
                      sorted(rng.sample(range(len(legal)), per_shape))])
        for col in legal:
            fpass = combinatorial_filter(edges, allverts, col) is None
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                zg = dim_Z_generic(bd, rng)
                b_cls, b_cnt, p1 = class_union_bounds(edges, allverts, bd)
                b_dn, p2 = dn_sparsity_bound(bd)
                lo = max(b_cls, b_cnt, b_dn, 0)
                assert zg >= lo, f"{label}: proven bound above generic dim Z"
                blocks += 1
                if zg == lo:
                    agree += 1
                    continue
                # candidate overshoot: confirm at 8 extra draws, then hunt
                # a structured (GR-8) witness
                zg2 = min(zg, dim_Z_generic(bd, rng, draws=8))
                if zg2 == lo:
                    agree += 1
                    continue
                a, M = a_and_M(bd, edges, allverts)
                beta, which = structured_beta_which(bd)
                lo_beta = max(a, a + (M - 3 * bd['h']) + beta, 0)
                assert zg2 >= lo_beta, \
                    f"{label}: proven (GR-8) bound above generic dim Z"
                if zg2 == lo_beta:
                    expl += 1
                    fam_count[which] = fam_count.get(which, 0) + 1
                    if exemplar_todo is None:
                        exemplar_todo = (label, edges, allverts, bd, lo)
                else:
                    unexpl += 1
                witnesses.append((label, mine, fpass, zg2, lo, lo_beta))
    print(f"  shapes probed: {shapes}; colouring-blocks: {blocks}")
    print(f"  generic dim Z == max((a),(b),(c)): {agree}/{blocks}")
    if witnesses:
        n_fp = sum(1 for w in witnesses if w[2])
        print(f"  OVERSHOOT witnesses: {len(witnesses)} "
              f"(filter-passing colourings among them: {n_fp})")
        print(f"    explained EXACTLY by the unified family (GR-8): {expl}")
        print(f"    NOT explained by (GR-8) [new mechanism]     : {unexpl}")
        fams = ', '.join(f"{k}:{v}" for k, v in sorted(fam_count.items()))
        print(f"    attaining family: {fams}")
        print("  first rows (label, block, filter-passing, generic dim Z, "
              "max-(GR-3), (GR-8)-β):")
        for row in witnesses[:12]:
            print(f"    {row}")
        if exemplar_todo is not None:
            exemplar_detail(*exemplar_todo)
        print("  ⟹ cheap kill (ii) FIRES: (GR-4) as stated is refuted on")
        print("    the widened pool; every explained row is repaired by the")
        print("    unified sub-multigraph family (GR-8).")
    else:
        print("  NO overshoot: the (GR-3) families stay exact at generic")
        print("  labels on the widened pool -- cheap kill (ii) comes back")
        print("  empty; (GR-4)'s ≤ direction survives the widening.")
    print()


def main():
    ap = argparse.ArgumentParser()
    for f in ('formula', 'treetriple', 'wide', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    run = a.validate or not any([a.formula, a.treetriple, a.wide])
    if run or a.formula:
        leg_formula()
    if run or a.treetriple:
        leg_treetriple()
    if run or a.wide:
        leg_wide()
    print("OK")


if __name__ == '__main__':
    main()
