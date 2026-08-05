"""
Gate (2): extension probes from (forced-degenerate) target-rank G'-seeds.

Shape of hbareSplit (Phase39-design.md, residue (ii)): G infeasible habitat,
v deg-2 with neighbours a0, b0 (safe: at least one non-hub),
G' = G.splitOff v a0 b0; given a bare G'-realization at G''s target, produce
a bare G-realization at G's target.  The natural discharge route EXTENDS the
G'-realization: keep all points, re-insert p_v, re-impose the pencil
constraints (at a safe split all changed vertices are deg <= 2, so no new
coplanarity constraint: any p_v gives a pencil witness; the only question is
rank).

Tests:
  A. G = theta(6,6,6)+center (19v, INFEASIBLE), safe split at ab3.
  B. G = spider(5,5,5)+center (16v, INFEASIBLE = G'_dang), safe split at ab2.
  C. (context) dangerous direction: G = 17v dangerous gadget, split at v
     (both neighbours a, b hubs).  Re-inserting v CHANGES two hub stars, so
     p_v is constrained to the intersection line of the two new star planes.

Per seed: sample G' pencil realization, assert its own target rank, then try
several p_v choices (random, midpoint of p_a0 p_b0, on line(a0,b0), in the
center plane) and report rank_G vs target_G.

Reproduce:  cd scratchpad/kbare && python3 gate2.py
"""
import random
from fractions import Fraction as F
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from kbare_common import *
from gate1 import sample_spider_pencil

# canonical home `exactcore.cross3` (2026-08-05).
from exactcore import cross3   # noqa: E402,F401

def line_of_two_planes(n1, n2, rng, tries=60):
    """Random affine point p in Q^3 with n1.hat(p) = 0 = n2.hat(p)."""
    d = cross3(n1[:3], n2[:3])
    # particular solution: solve the 2x2 in two coords, zero the third
    for free in range(3):
        cols = [k for k in range(3) if k != free]
        A = [[n1[cols[0]], n1[cols[1]]], [n2[cols[0]], n2[cols[1]]]]
        det = A[0][0]*A[1][1] - A[0][1]*A[1][0]
        if det != 0:
            p0 = [F(0)]*3
            s0 = ( A[1][1]*(-n1[3]) - A[0][1]*(-n2[3])) / det
            s1 = (-A[1][0]*(-n1[3]) + A[0][0]*(-n2[3])) / det
            p0[cols[0]] = s0; p0[cols[1]] = s1
            break
    else:
        return None
    if all(x == 0 for x in d):
        return p0
    t = F(rng.randint(-20, 20), rng.randint(1, 5))
    return [p0[i] + t*d[i] for i in range(3)]

def try_extension(edges_G, target_G, pt_base, v, choices):
    """choices: list of (label, p_v).  Returns list of (label, ok_witness, rank)."""
    out = []
    for label, pv in choices:
        if pv is None:
            out.append((label, False, None)); continue
        pt = dict(pt_base); pt[v] = pv
        try:
            ok, _ = verify_pencil_witness(edges_G, pt)
        except AssertionError:
            ok = False
        if not ok:
            out.append((label, False, None)); continue
        try:
            rk, _, _ = pencil_rank(edges_G, pt)
        except AssertionError:
            out.append((label, False, None)); continue
        out.append((label, True, rk))
    return out

def run_safe_split(name, edges_G, meta, arc_tag, nseeds=8, seed0=500):
    print(f"\n===== GATE 2 (safe split): {name} =====")
    interior = meta['arcs'][arc_tag]
    mid = interior[len(interior)//2]
    a0, b0 = sorted(neighbors(edges_G)[mid], key=str)
    print(f"  split vertex v={mid} (deg 2), neighbours a0={a0}, b0={b0} "
          f"(degrees {degrees(edges_G)[a0]}, {degrees(edges_G)[b0]} — safe)")
    edges_Gp = split_off(edges_G, mid, a0, b0)
    dG, _ = exact_deficiency(edges_G)
    dGp, _ = exact_deficiency(edges_Gp)
    tG = 6*(len(verts_of(edges_G))-1) - dG
    tGp = 6*(len(verts_of(edges_Gp))-1) - dGp
    print(f"  def(G)={dG} target(G)={tG};  def(G')={dGp} target(G')={tGp} "
          f"(splitOff bound: def(G') in {{def(G), def(G)-1}}: "
          f"{dGp in (dG, dG-1)})")
    hubn = closed_hub_nbhds(edges_Gp)
    print(f"  G' max closedHubNbhd = {max(hubn.values())} "
          f"({'INFEASIBLE — seed realizations are forced-degenerate' if max(hubn.values()) >= 4 else 'feasible-eligible'})")
    n_ok = n_seed = 0
    fail_log = []
    for s in range(nseeds):
        rng = random.Random(seed0 + s)
        try:
            ptp = sample_spider_pencil(edges_Gp, meta, rng)
            ok, _ = verify_pencil_witness(edges_Gp, ptp)
            assert ok
            rkp, _, _ = pencil_rank(edges_Gp, ptp)
        except (AssertionError, RuntimeError):
            print(f"  seed {s}: G' sample degenerate, skipped"); continue
        if rkp != tGp:
            print(f"  seed {s}: G' sample rank {rkp} != target {tGp}, skipped"); continue
        n_seed += 1
        pa, pb = ptp[a0], ptp[b0]
        mid_ab = [(pa[i]+pb[i])/2 for i in range(3)]
        t = F(rng.randint(2, 9), rng.randint(1, 3))
        on_line = [pa[i] + t*(pb[i]-pa[i]) for i in range(3)]
        choices = [(f"random{j}", rvec3(rng)) for j in range(4)]
        choices += [("midpoint(a0,b0)", mid_ab), ("on line(a0,b0)", on_line)]
        # extra degeneration: p_v in the center-star plane
        z = meta['center']
        nz = nullspace([hat(ptp[z])] + [hat(ptp[h]) for h in meta['hubs']])
        if nz and any(nz[0][i] != 0 for i in range(3)):
            choices.append(("in center plane", point_on_affine_plane4(nz[0], rng)))
        res = try_extension(edges_G, tG, ptp, mid, choices)
        succ = [lbl for lbl, ok2, rk in res if ok2 and rk == tG]
        fails = [(lbl, rk) for lbl, ok2, rk in res if not ok2 or rk != tG]
        print(f"  seed {s}: G' at target {tGp}; extension -> G target {tG}: "
              f"{len(succ)}/{len(res)} choices attain "
              f"{'(all)' if not fails else 'FAILS: ' + str(fails)}")
        if len(succ) == len(res):
            n_ok += 1
        else:
            fail_log.append((s, fails))
    print(f"  >>> {n_ok}/{n_seed} seeds: EVERY tested p_v extension attains target(G)")
    if fail_log:
        print(f"  >>> failures: {fail_log}")
    return n_ok, n_seed, fail_log

def run_dangerous_context(nseeds=6, seed0=900):
    print("\n===== GATE 2 (context, dangerous direction): 17v gadget at v =====")
    edges_G, metaG = dangerous_gadget(5)
    edges_Gp = split_off(edges_G, 'v', 'a', 'b')
    meta_p = {'hubs': ['x', 'y', 'b'], 'center': 'a',
              'arcs': {}}  # arcs unused by sampler
    dG, _ = exact_deficiency(edges_G); dGp, _ = exact_deficiency(edges_Gp)
    tG = 6*16 - dG; tGp = 6*15 - dGp
    print(f"  def(G)={dG} target(G)={tG}; def(G')={dGp} target(G')={tGp}; "
          f"G' max closedHubNbhd={max(closed_hub_nbhds(edges_Gp).values())} (INFEASIBLE)")
    nbG = neighbors(edges_G)
    n_ok = n_seed = 0
    for s in range(nseeds):
        rng = random.Random(seed0 + s)
        try:
            ptp = sample_spider_pencil(edges_Gp, meta_p, rng)
            ok, _ = verify_pencil_witness(edges_Gp, ptp)
            assert ok
            rkp, _, _ = pencil_rank(edges_Gp, ptp)
        except (AssertionError, RuntimeError):
            print(f"  seed {s}: G' sample degenerate, skipped"); continue
        if rkp != tGp:
            print(f"  seed {s}: G' rank {rkp} != {tGp}, skipped"); continue
        n_seed += 1
        # p_v constrained: a's new star {a,x,y,v} and b's new star {b,v,arcnbrs}
        n_a = nullspace([hat(ptp['a']), hat(ptp['x']), hat(ptp['y'])])
        b_arc_nbrs = [u for u in nbG['b'] if u != 'v']
        n_b = nullspace([hat(ptp['b'])] + [hat(ptp[u]) for u in b_arc_nbrs])
        if not n_a or not n_b:
            print(f"  seed {s}: star planes not determined, skipped"); continue
        results = []
        for j in range(4):
            pv = line_of_two_planes(n_a[0], n_b[0], rng)
            res = try_extension(edges_G, tG, ptp, 'v', [(f"line pt {j}", pv)])
            results += res
        succ = [lbl for lbl, ok2, rk in results if ok2 and rk == tG]
        print(f"  seed {s}: G' at target {tGp}; constrained extension to G "
              f"(target {tG}): {len(succ)}/{len(results)} line-points attain "
              f"{[(lbl, rk) for lbl, ok2, rk in results]}")
        if succ:
            n_ok += 1
    print(f"  >>> {n_ok}/{n_seed} seeds: SOME constrained p_v attains target(G)")
    return n_ok, n_seed

if __name__ == '__main__':
    e666, m666 = spider(6, 6, 6)
    a = run_safe_split("theta(6,6,6)+center (19v, INFEASIBLE)", e666, m666, 'ab')
    e555, m555 = spider(5, 5, 5)
    b = run_safe_split("spider(5,5,5)+center (16v, INFEASIBLE = G'_dang)",
                       e555, m555, 'ab')
    c = run_dangerous_context()
    print("\n===== GATE 2 SUMMARY =====")
    print(f"  A theta(6,6,6) safe split: {a[0]}/{a[1]} seeds all-choices attain")
    print(f"  B spider(5,5,5) safe split: {b[0]}/{b[1]} seeds all-choices attain")
    print(f"  C dangerous-direction context: {c[0]}/{c[1]} seeds some constrained p_v attains")
