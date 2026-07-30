"""
Supplementary stress probes for the (K-bare) numerics gate (run after
gate1.py / gate2.py; both must pass first).

  1. Gate-2A artifact check: the single seed-5 'on line(a0,b0)' failure in
     gate2.py test A is the t=1 coincidence p_v = p_b0 (rejected by the
     witness checker, NOT a rank failure); genuine collinear p_v attains 105.
  2. spider(4,5,5) (the G'' of gate-2 test B) deficiency cross-check via
     generic baseline (landed molecular_conjecture: generic rank = target).
  3. Family sweep: theta(7,7,7), theta(6,6,7), theta(6,7,7) gate-1 style.
  4. Deeper-degenerate G' seeds (center Z + hubs A,B,C COLLINEAR): still at
     G'-target for the theta split, and extension still attains; for
     spider(4,5,5) such seeds fall below target (excluded by hbareSplit's
     antecedent, which demands a target-rank G' realization).

Reproduce:  cd scratchpad/kbare && python3 stress_extra.py
"""
import random
from fractions import Fraction as F
from kbare_common import *
from gate1 import sample_spider_pencil

def sample_spider_pencil_collinear_hubs(edges, meta, rng):
    hubs = meta['hubs']; z = meta['center']
    nb = neighbors(edges)
    pt = {}
    pz = rvec3(rng); d = rnonzero3(rng)
    pt[z] = pz
    for h in hubs:
        t = F(rng.randint(1, 12), rng.randint(1, 4)) * (1 if rng.random() < .5 else -1)
        pt[h] = [pz[i] + t * d[i] for i in range(3)]
    for h in hubs:
        n4 = normal4_through([hat(pt[h]), hat(pt[z])], rng)
        for u in nb[h]:
            if u not in pt:
                pt[u] = point_on_affine_plane4(n4, rng)
    for v in verts_of(edges):
        if v not in pt:
            pt[v] = rvec3(rng)
    return pt

if __name__ == '__main__':
    # --- 1. seed-5 artifact ---
    e666, m666 = spider(6, 6, 6)
    interior = m666['arcs']['ab']; mid = interior[len(interior) // 2]
    a0, b0 = sorted(neighbors(e666)[mid], key=str)
    eGp = split_off(e666, mid, a0, b0)
    rng = random.Random(505)
    ptp = sample_spider_pencil(eGp, m666, rng)
    pa, pb = ptp[a0], ptp[b0]
    t = F(rng.randint(2, 9), rng.randint(1, 3))
    onl = [pa[i] + t * (pb[i] - pa[i]) for i in range(3)]
    print(f"[1] gate2-A seed 5 artifact: t={t}, p_v==p_b0: {onl == pb}")
    for tv in [F(5, 7), F(13, 4), F(-3, 2)]:
        pv = [pa[i] + tv * (pb[i] - pa[i]) for i in range(3)]
        pt = dict(ptp); pt[mid] = pv
        ok, _ = verify_pencil_witness(e666, pt)
        rk, _, _ = pencil_rank(e666, pt)
        print(f"    genuine collinear t={tv}: witness={ok} rank={rk}/105")

    # --- 2. spider(4,5,5) def cross-check ---
    e555, m555 = spider(5, 5, 5)
    i5 = m555['arcs']['ab']; mid5 = i5[len(i5) // 2]
    c0, c1 = sorted(neighbors(e555)[mid5], key=str)
    eG2 = split_off(e555, mid5, c0, c1)
    d2, info2 = exact_deficiency(eG2)
    rng = random.Random(31337)
    ptg = {v: rvec3(rng) for v in verts_of(eG2)}
    rkg, _, _ = pencil_rank(eG2, ptg)
    tgt2 = 6 * (len(verts_of(eG2)) - 1) - d2
    print(f"\n[2] spider(4,5,5): exact def={d2} ({info2}); generic baseline "
          f"rank={rkg} vs target={tgt2} ({'OK' if rkg == tgt2 else 'MISMATCH'})")

    # --- 3. family sweep ---
    print("\n[3] theta family sweep:")
    for arcs in [(7, 7, 7), (6, 6, 7), (6, 7, 7)]:
        e, m = spider(*arcs)
        d, info = exact_deficiency(e)
        tgt = 6 * (len(verts_of(e)) - 1) - d
        hub = max(closed_hub_nbhds(e).values())
        best = -1; n_att = 0; n_tot = 0
        for s in range(6):
            rng = random.Random(1234 + s)
            try:
                pt = sample_spider_pencil(e, m, rng)
                ok, _ = verify_pencil_witness(e, pt); assert ok
                rk, _, _ = pencil_rank(e, pt)
            except (AssertionError, RuntimeError):
                continue
            n_tot += 1; best = max(best, rk); n_att += (rk == tgt)
        print(f"    theta{arcs}: |V|={len(verts_of(e))} def={d} hubNbhdMax={hub} "
              f"maxf_proper={info['maxf_proper_ge2']} target={tgt} "
              f"attained {n_att}/{n_tot} best={best}")

    # --- 4. deeper-degenerate seeds ---
    print("\n[4] collinear-hub G' seeds, theta(6,6,6) safe split:")
    for s in range(6):
        rng = random.Random(7000 + s)
        try:
            ptp = sample_spider_pencil_collinear_hubs(eGp, m666, rng)
            ok, _ = verify_pencil_witness(eGp, ptp); assert ok
            rkp, _, _ = pencil_rank(eGp, ptp)
        except (AssertionError, RuntimeError):
            print(f"    seed {s}: degenerate sample"); continue
        if rkp != 100:
            print(f"    seed {s}: G' rank {rkp} != 100 (below target; invalid antecedent)")
            continue
        succ = tot = 0
        for j in range(5):
            pv = rvec3(rng)
            pt = dict(ptp); pt[mid] = pv
            try:
                ok, _ = verify_pencil_witness(e666, pt); assert ok
                rk, _, _ = pencil_rank(e666, pt)
            except AssertionError:
                continue
            tot += 1; succ += (rk == 105)
        print(f"    seed {s}: G' AT target 100 (collinear hubs); extension attains: {succ}/{tot}")
    print("    collinear-hub G'' seeds, spider(5,5,5) safe split:")
    for s in range(6):
        rng = random.Random(8000 + s)
        try:
            ptp = sample_spider_pencil_collinear_hubs(eG2, m555, rng)
            ok, _ = verify_pencil_witness(eG2, ptp); assert ok
            rkp, _, _ = pencil_rank(eG2, ptp)
        except (AssertionError, RuntimeError):
            print(f"    seed {s}: degenerate sample"); continue
        print(f"    seed {s}: G'' rank {rkp} vs target 84 "
              f"({'valid seed' if rkp == 84 else 'below target; excluded by antecedent'})")
