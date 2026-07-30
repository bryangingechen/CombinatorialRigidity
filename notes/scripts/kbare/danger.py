"""
(K-bare) extension-route recon: the count-DEPENDENT infeasible danger zone.

Motivation (design doc, "(K-bare) extension-route recon" subsection): every
gadget of the landed (K-bare) numerics gate (gate1/gate2/stress_extra) is
count-INDEPENDENT — its pencil target equals 5|E| (nullity 0 at target), so
the gate never sampled the stratum where stress obstructions to the
extension live.  The count dichotomy (the KT-4.5(ii) shape,
`indep_edgeSet_mulTilde_of_noRigid_of_pos`, ReducibleVertex.lean:515: a
count-dependent edge set contains a circuit, which `hnoRigid` forces to be
SPANNING, so def(G) = 0) confines the dependent part of the (K-bare) habitat
to: rigid (def 0), index := 5|E| - 6(|V|-1) >= 1, infeasible.  Its splitOff
G' then carries corank index+1 >= 2 at target-rank seeds — beyond even
(K-tight)'s corank-1 setting.

DZ gadget (constructed for this recon): K3,3 skeleton on parts
{h0, u1, u2} | {h1, h2, h3}, each skeleton edge subdivided into a path;
lengths h0: (1,1,1) — so h0 is a hub adjacent to three hubs,
closedHubNbhd(h0) = {h0,h1,h2,h3}, ncard 4 => provably infeasible
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
Motive.lean:412, contrapositive) — u1: (2,4,4), u2: (4,2,4).
|V| = 20, |E| = 23, f(V) = 115 - 114 = +1 (count-DEPENDENT, index 1),
def = 0 (exact), every proper |W|>=2 subset has f(W) < 0 (the
no-proper-rigid certificate), simple, 2EC, degree-2 vertices present:
a genuine hbareSplit habitat member with a spanning circuit.

Probes:
  0. count-status audit of the previously-tried gate gadgets (expected:
     all count-independent — the evidence gap this script fills).
  1. habitat certification of DZ (as above, all exact).
  2. gate-1-style bare pencil target attainment at DZ (target 114 = 6*19,
     115 rows: corank 1 at target — G itself carries a stress).
  3a. safe split at a length-4 arc interior (both ends deg 2) -> G' (19v,
     22e, index 2, def 0, target 108 = 6*18, 110 rows: corank 2 at target);
     gate-2-style extension probes from target-rank G' seeds (several p_v
     choices per seed, incl. the on-line(a,b) degenerate direction),
     reporting each seed's exact corank.
  3b. the KT-faithful HUB-end split (a = hub u1, b deg-2; hsafe holds via
     the non-hub end b): p_v is confined to the hub's star plane (which
     contains line(a,b)); in-plane generic placements probed instead of
     free ones.

Certification logic as in kbare_common: rank <= target holds for every
realization (partition bound), rank_modp <= rank_Q, hence
rank_modp == target certifies exact attainment; one exact-Q Fraction rank
is additionally run on an attaining sample per stage.

Reproduce:  cd notes/scripts/kbare && python3 danger.py
"""
import random, time
from fractions import Fraction as F
from kbare_common import *
from gate1 import report_graph
from gate2 import line_of_two_planes

# ---------------- the DZ gadget ----------------

DZ_LENGTHS = {('h0', 'h1'): 1, ('h0', 'h2'): 1, ('h0', 'h3'): 1,
              ('u1', 'h1'): 2, ('u1', 'h2'): 4, ('u1', 'h3'): 4,
              ('u2', 'h1'): 4, ('u2', 'h2'): 2, ('u2', 'h3'): 4}

def dz_gadget():
    edges = []
    for (x, y), l in DZ_LENGTHS.items():
        prev = x
        for i in range(1, l):
            w = f'{x}{y}_{i}'
            edges.append((prev, w))
            prev = w
        edges.append((prev, y))
    return edges

# ---------------- a general hub-plane pencil sampler ----------------

def sample_dz_pencil(edges, rng):
    """Exact-Q pencil configuration for the DZ topology (works for its splits
    too — driven by adjacency to hubs): h0's closed star {h0,h1,h2,h3} in a
    common plane; every other hub gets its own star plane (through h0's point
    where adjacent); interiors adjacent to one hub go on that hub's plane,
    adjacent to two hubs on the planes' intersection line; the rest free."""
    deg = degrees(edges)
    nb = neighbors(edges)
    hubs = [v for v in verts_of(edges) if deg[v] >= 3]
    pt = {}
    # h0 and its (hub) neighbours in a common plane
    n0 = rnonzero3(rng)
    pt['h0'] = rvec3(rng)
    for h in sorted(nb['h0'], key=str):
        pt[h] = point_in_plane3(pt['h0'], n0, rng)
    # remaining hub points free
    for h in hubs:
        if h not in pt:
            pt[h] = rvec3(rng)
    # per-hub star plane through the already-placed closed-star members
    plane = {}
    for h in hubs:
        anchors = [hat(pt[h])] + [hat(pt[w]) for w in sorted(nb[h], key=str)
                                  if w in pt]
        plane[h] = normal4_through(anchors, rng)
    # interiors: on their adjacent hubs' planes / intersection line / free
    for v in verts_of(edges):
        if v in pt:
            continue
        adj_hubs = sorted([w for w in nb[v] if w in plane], key=str)
        if len(adj_hubs) == 0:
            pt[v] = rvec3(rng)
        elif len(adj_hubs) == 1:
            pt[v] = point_on_affine_plane4(plane[adj_hubs[0]], rng)
        else:
            pv = line_of_two_planes(plane[adj_hubs[0]], plane[adj_hubs[1]], rng)
            if pv is None:
                raise RuntimeError(f"parallel hub planes at {v}")
            pt[v] = pv
    return pt

# ---------------- probe 0: count status of the earlier gate gadgets ----------------

def count_status(name, edges):
    verts = verts_of(edges)
    d, info = exact_deficiency(edges)
    m = len(edges)
    n = len(verts)
    f_full = 5 * m - 6 * (n - 1)
    target = 6 * (n - 1) - d
    indep = (5 * m == target)  # independent <=> nullity 0 at target
    print(f"  {name}: |V|={n} |E|={m} f(V)={f_full} def={d} target={target} "
          f"rows={5*m} => {'count-INDEPENDENT (corank 0 at target)' if indep else f'count-DEPENDENT (corank {5*m - target} at target)'}")
    return indep

# ---------------- probe 2/3 drivers ----------------

def run_attainment(name, edges, nsamples=10, seed0=4200, exact_confirm=True):
    d, target = report_graph(name, edges)
    nrows_total = 5 * len(edges)
    best, attained = -1, None
    for s in range(nsamples):
        rng = random.Random(seed0 + s)
        try:
            pt = sample_dz_pencil(edges, rng)
        except (AssertionError, RuntimeError) as e:
            print(f"  sample {s}: sampler degenerate ({e}); skipped")
            continue
        ok, _ = verify_pencil_witness(edges, pt)
        if not ok:
            print(f"  sample {s}: NOT a pencil witness; skipped")
            continue
        rk, nrows, _ = pencil_rank(edges, pt)
        tag = "TARGET ATTAINED" if rk == target else f"short by {target - rk}"
        print(f"  pencil sample {s}: witness OK, rank(mod p) = {rk} / {target} "
              f"(corank {nrows - rk})  [{tag}]")
        if rk > best:
            best = rk
        if attained is None and rk == target:
            attained = pt
    if attained is not None and exact_confirm:
        t0 = time.time()
        rkx, _, _ = pencil_rank(edges, attained, exact=True)
        print(f"  exact-Q Fraction rank of attaining sample = {rkx} / {target} "
              f"({'CONFIRMED' if rkx == target else 'DISAGREES WITH MOD-P — investigate'}) "
              f"[{time.time() - t0:.1f}s]")
    print(f"  >>> best pencil rank = {best} / target {target} "
          f"({'ATTAINED' if best == target else 'NOT ATTAINED'})")
    return best == target, attained

def run_extension(edges_G, v, nseeds=8, seed0=7100):
    a0, b0 = sorted(neighbors(edges_G)[v], key=str)
    dv = degrees(edges_G)
    hub_ends = [x for x in (a0, b0) if dv[x] >= 3]
    print(f"\n===== DZ extension probe: split at v={v} (deg {dv[v]}), "
          f"neighbours a={a0} (deg {dv[a0]}), b={b0} (deg {dv[b0]})"
          f"{' — HUB end(s): ' + ','.join(hub_ends) if hub_ends else ' — both ends non-hub'} =====")
    edges_Gp = split_off(edges_G, v, a0, b0)
    dG, _ = exact_deficiency(edges_G)
    dGp, infop = exact_deficiency(edges_Gp)
    tG = 6 * (len(verts_of(edges_G)) - 1) - dG
    tGp = 6 * (len(verts_of(edges_Gp)) - 1) - dGp
    corank_Gp = 5 * len(edges_Gp) - tGp
    print(f"  def(G)={dG} target(G)={tG} rows={5*len(edges_G)};  "
          f"def(G')={dGp} target(G')={tGp} rows={5*len(edges_Gp)} "
          f"=> corank(G' at target) = {corank_Gp}")
    print(f"  G' no-proper-rigid cert: max f(W) proper = {infop['maxf_proper_ge2']}; "
          f"G' max closedHubNbhd = {max(closed_hub_nbhds(edges_Gp).values())}")
    n_ok = n_seed = 0
    fail_log = []
    exact_done = False
    for s in range(nseeds):
        rng = random.Random(seed0 + s)
        try:
            ptp = sample_dz_pencil(edges_Gp, rng)
            ok, _ = verify_pencil_witness(edges_Gp, ptp)
            assert ok
            rows_p, _ = build_rigidity(edges_Gp, ptp)
            rkp = rank_modp(rows_p)
        except (AssertionError, RuntimeError):
            print(f"  seed {s}: G' sample degenerate, skipped")
            continue
        if rkp != tGp:
            print(f"  seed {s}: G' sample rank {rkp} != target {tGp}, skipped")
            continue
        n_seed += 1
        pa, pb = ptp[a0], ptp[b0]
        mid_ab = [(pa[i] + pb[i]) / 2 for i in range(3)]
        t = F(rng.randint(2, 9), rng.randint(1, 3))
        on_line = [pa[i] + t * (pb[i] - pa[i]) for i in range(3)]
        if hub_ends:
            # p_v must keep every hub end's star coplanar: it is confined to
            # the plane through the hub and its G-neighbours other than v
            # (all already placed in the G' seed).  With one hub end (hsafe)
            # that is a 2-dim placement plane containing line(a,b).
            nbG = neighbors(edges_G)
            anchors = []
            for h in hub_ends:
                anchors.append(hat(ptp[h]))
                anchors += [hat(ptp[w]) for w in sorted(nbG[h], key=str) if w != v]
            ns = nullspace(anchors)
            if not ns or all(ns[0][i] == 0 for i in range(3)):
                print(f"  seed {s}: hub-end placement plane degenerate, skipped")
                n_seed -= 1
                continue
            n_pl = ns[0]
            choices = [(f"in-plane{j}", point_on_affine_plane4(n_pl, rng))
                       for j in range(4)]
        else:
            choices = [(f"random{j}", rvec3(rng)) for j in range(4)]
        choices += [("midpoint(a,b)", mid_ab), ("on line(a,b)", on_line)]
        res = []
        for label, pv in choices:
            pt = dict(ptp)
            pt[v] = pv
            try:
                ok2, _ = verify_pencil_witness(edges_G, pt)
            except AssertionError:
                ok2 = False
            if not ok2:
                res.append((label, None))
                continue
            try:
                rk, _, _ = pencil_rank(edges_G, pt)
            except AssertionError:
                res.append((label, None))
                continue
            res.append((label, rk))
            if rk == tG and not exact_done:
                rkx, _, _ = pencil_rank(edges_G, pt, exact=True)
                print(f"  [exact-Q confirm of one attaining extension: {rkx} / {tG} "
                      f"({'CONFIRMED' if rkx == tG else 'DISAGREES'})]")
                exact_done = True
        succ = [lbl for lbl, rk in res if rk == tG]
        fails = [(lbl, rk) for lbl, rk in res if rk != tG]
        print(f"  seed {s}: G' at target {tGp} (corank {corank_Gp}); extension -> "
              f"target {tG}: {len(succ)}/{len(res)} attain"
              f"{'' if not fails else '  FAILS: ' + str(fails)}")
        if len(succ) == len(res):
            n_ok += 1
        else:
            fail_log.append((s, fails))
    print(f"  >>> {n_ok}/{n_seed} seeds: EVERY tested p_v extension attains target(G)")
    if fail_log:
        print(f"  >>> non-attaining choices: {fail_log}")
    return n_ok, n_seed, fail_log

if __name__ == '__main__':
    from gate1 import sample_spider_pencil  # noqa: F401 (context import)
    from kbare_common import spider, dangerous_gadget

    print("===== PROBE 0: count status of the previously-tried gate gadgets =====")
    e666, m666 = spider(6, 6, 6)
    count_status("theta(6,6,6)+center (19v)", e666)
    interior = m666['arcs']['ab']
    mid = interior[len(interior) // 2]
    nbm = sorted(neighbors(e666)[mid], key=str)
    count_status("theta(6,6,6) safe-split G' (18v)", split_off(e666, mid, nbm[0], nbm[1]))
    e555, _ = spider(5, 5, 5)
    count_status("spider(5,5,5)+center = G'_dang (16v)", e555)
    edang, _ = dangerous_gadget(5)
    count_status("dangerous gadget (17v)", edang)
    for l1, l2, l3 in [(7, 7, 7), (6, 6, 7), (6, 7, 7)]:
        e, _ = spider(l1, l2, l3)
        count_status(f"theta({l1},{l2},{l3})+center", e)

    print("\n===== PROBE 1+2: the DZ gadget (count-dependent infeasible habitat) =====")
    edz = dz_gadget()
    okG, _ = run_attainment(
        "DZ = subdivided K3,3, apex h0 (20v, 23e; count-DEPENDENT index 1; "
        "INFEASIBLE habitat)", edz)

    # probe 3a: safe split at a length-4 arc interior (both neighbours deg 2)
    a, b, c = run_extension(edz, 'u1h2_2')
    # probe 3b: the KT-faithful hub-end split (a = hub u1, b = deg-2; hsafe
    # holds via the non-hub end b; p_v confined to u1's star plane)
    a2, b2, c2 = run_extension(edz, 'u1h2_1', seed0=8200)

    print("\n===== DANGER-ZONE SUMMARY =====")
    print(f"  DZ bare target attainment: {'ATTAINED' if okG else 'NOT ATTAINED'}")
    print(f"  DZ corank-2 extension (non-hub ends): {a}/{b} seeds all-choices attain"
          f"{'' if not c else f'; non-attaining: {c}'}")
    print(f"  DZ corank-2 extension (hub end): {a2}/{b2} seeds all-choices attain"
          f"{'' if not c2 else f'; non-attaining: {c2}'}")
