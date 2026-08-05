"""
Gate (1): bare pencil rank at the infeasible gadgets.

For each gadget G: exact deficiency def(G~), target = 6(|V|-1) - def, habitat
certification (simple, 2EC, max f(W) over proper |W|>=2 subsets < 0 iff
no-proper-rigid), feasibility status (max closedHubNbhd ncard), a fully
generic baseline rank (cross-checks def via the landed molecular_conjecture:
generic molecular rank = target), and N exact-Q pencil-stratum samples.

Certification logic: rank <= target holds for EVERY realization (partition
bound, see kbare_common docstring), and rank_modp <= rank_Q; hence
rank_modp == target certifies exact rational attainment.  One exact-Q
Fraction-arithmetic rank is additionally run per gadget on the first
attaining sample.

Reproduce:  cd scratchpad/kbare && python3 gate1.py
"""
import random, sys, time
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from kbare_common import *

def sample_spider_pencil(edges, meta, rng):
    """Exact-Q pencil configuration for a (possibly split-shortened) spider
    with center: center closed star coplanar; each hub's closed star coplanar;
    all other vertices free."""
    hubs = meta['hubs']
    z = meta['center']
    nb = neighbors(edges)
    pt = {}
    nz3 = rnonzero3(rng)
    pt[z] = rvec3(rng)
    for h in hubs:
        pt[h] = point_in_plane3(pt[z], nz3, rng)
    for h in hubs:
        n4 = normal4_through([hat(pt[h]), hat(pt[z])], rng)
        for u in nb[h]:
            if u not in pt:
                pt[u] = point_on_affine_plane4(n4, rng)
    for v in verts_of(edges):
        if v not in pt:
            pt[v] = rvec3(rng)
    return pt

def sample_dang_pencil(edges, meta, rng):
    """Exact-Q pencil configuration for the 17-vertex dangerous gadget:
    a's closed star {a,x,y,v} coplanar; hub planes at x, y (through p_a) and
    b (through p_v); arc-neighbours inside; interiors free."""
    nb = neighbors(edges)
    pt = {}
    na3 = rnonzero3(rng)
    pt['a'] = rvec3(rng)
    for u in ('x', 'y', 'v'):
        pt[u] = point_in_plane3(pt['a'], na3, rng)
    for h in ('x', 'y'):
        n4 = normal4_through([hat(pt[h]), hat(pt['a'])], rng)
        for u in nb[h]:
            if u not in pt:
                pt[u] = point_on_affine_plane4(n4, rng)
    pt['b'] = rvec3(rng)
    n4 = normal4_through([hat(pt['b']), hat(pt['v'])], rng)
    for u in nb['b']:
        if u not in pt:
            pt[u] = point_on_affine_plane4(n4, rng)
    for v in verts_of(edges):
        if v not in pt:
            pt[v] = rvec3(rng)
    return pt

def sample_all_coplanar(edges, rng):
    """Deep stratum: every point in one plane (context datum, not the claim)."""
    n3 = rnonzero3(rng)
    p0 = rvec3(rng)
    pt = {}
    for v in verts_of(edges):
        pt[v] = point_in_plane3(p0, n3, rng)
    return pt

def report_graph(name, edges):
    verts = verts_of(edges)
    deg = degrees(edges)
    hubn = closed_hub_nbhds(edges)
    maxhub = max(hubn.values())
    infeas_wit = sorted([v for v, c in hubn.items() if c >= 4], key=str)
    d, info = exact_deficiency(edges)
    target = 6 * (len(verts) - 1) - d
    print(f"\n===== {name} =====")
    print(f"  |V|={len(verts)} |E|={len(edges)} simple=True "
          f"2EC={is_2ec(edges)} min_deg={min(deg.values())} "
          f"max_deg={max(deg.values())}")
    print(f"  max closedHubNbhd = {maxhub} "
          f"({'INFEASIBLE (>=4 witness: ' + ','.join(infeas_wit) + ')' if maxhub >= 4 else 'feasible-eligible (<=3 everywhere)'})")
    print(f"  no-proper-rigid cert: max f(W) over proper |W|>=2 = "
          f"{info['maxf_proper_ge2']} (need <0), f(V)={info['f_full']}, "
          f"#zero-f proper={info['zero_f_proper_count']}, "
          f"#positive-f subsets={info['n_positive_f_subsets']}")
    print(f"  exact deficiency = {d} (def_finest={info['def_finest']}, "
          f"packing_gain={info['packing_gain']})  =>  TARGET = {target} "
          f"(rows available = {5 * len(edges)})")
    return d, target

def run_gadget(name, edges, sampler, meta, nsamples=12, seed0=42,
               exact_confirm=True):
    d, target = report_graph(name, edges)
    # generic (unconstrained) baseline: cross-checks def via molecular_conjecture
    rng = random.Random(seed0 * 7919 + 1)
    while True:
        try:
            ptg = {v: rvec3(rng) for v in verts_of(edges)}
            rkg, nrows, nv = pencil_rank(edges, ptg)
            break
        except AssertionError:
            continue
    print(f"  generic baseline rank (mod p) = {rkg} "
          f"({'== target: def cross-check OK' if rkg == target else 'MISMATCH vs target — investigate'})")
    best = -1
    attained = None
    for s in range(nsamples):
        rng = random.Random(seed0 + s)
        try:
            pt = sampler(edges, meta, rng)
        except (AssertionError, RuntimeError) as e:
            print(f"  sample {s}: sampler degenerate ({e}); skipped")
            continue
        ok, nrm = verify_pencil_witness(edges, pt)
        if not ok:
            print(f"  sample {s}: NOT a pencil witness: {nrm}; skipped")
            continue
        rk, nrows, nv = pencil_rank(edges, pt)
        tag = "TARGET ATTAINED" if rk == target else f"short by {target - rk}"
        print(f"  pencil sample {s}: witness OK, rank(mod p) = {rk} / {target}  [{tag}]")
        if rk > best:
            best, attained = rk, (pt if rk == target else attained)
        if attained is None and rk == target:
            attained = pt
    # deep stratum context: all-coplanar
    rng = random.Random(seed0 * 31 + 5)
    try:
        ptc = sample_all_coplanar(edges, rng)
        okc, _ = verify_pencil_witness(edges, ptc)
        rkc, _, _ = pencil_rank(edges, ptc)
        print(f"  all-coplanar (deep stratum, context): witness={okc} rank={rkc} / {target}")
    except AssertionError:
        print("  all-coplanar: coincident sample, skipped")
    if attained is not None and exact_confirm:
        t0 = time.time()
        rkx, nrows, nv = pencil_rank(edges, attained, exact=True)
        print(f"  exact-Q Fraction rank of attaining sample = {rkx} / {target} "
              f"({'CONFIRMED' if rkx == target else 'DISAGREES WITH MOD-P — investigate'}) "
              f"[{time.time() - t0:.1f}s]")
    print(f"  >>> best pencil rank = {best} / target {target} "
          f"({'ATTAINED' if best == target else 'NOT ATTAINED'})")
    return best == target

if __name__ == '__main__':
    results = {}
    # 1. the 19-vertex L6a theta counterexample: infeasible habitat
    e666, m666 = spider(6, 6, 6)
    results['theta(6,6,6)+center, 19v'] = run_gadget(
        "theta(6,6,6)+center  (19-vertex L6a counterexample; INFEASIBLE habitat)",
        e666, sample_spider_pencil, m666)

    # 2. its safe split (the G' of gate 2): spider with arcs (5,6,6)
    interior = m666['arcs']['ab']
    mid = interior[len(interior) // 2]
    nbm = sorted(neighbors(e666)[mid], key=str)
    e_split = split_off(e666, mid, nbm[0], nbm[1])
    results["theta(6,6,6) safe-split G' (18v)"] = run_gadget(
        f"theta(6,6,6) safe-split at {mid} (G', arcs (5,6,6), 18v; INFEASIBLE)",
        e_split, sample_spider_pencil, m666)

    # 3. G'_dang = spider(5,5,5)+center (16v; the dangerous split's infeasible G')
    e555, m555 = spider(5, 5, 5)
    results["spider(5,5,5)+center = G'_dang, 16v"] = run_gadget(
        "spider(5,5,5)+center  (= G'_dang, the 17-vertex gadget's dangerous "
        "split; INFEASIBLE, borderline-tight)",
        e555, sample_spider_pencil, m555)

    # 4. the 17-vertex dangerous gadget itself (feasible baseline)
    edang, mdang = dangerous_gadget(5)
    results['dangerous gadget, 17v (feasible)'] = run_gadget(
        "dangerous gadget (17v; FEASIBLE, hub-tight at a)",
        edang, sample_dang_pencil, mdang)

    print("\n===== GATE 1 SUMMARY =====")
    for k, v in results.items():
        print(f"  {k}: {'ATTAINED' if v else 'NOT ATTAINED'}")
