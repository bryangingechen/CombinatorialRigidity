"""
(K-bare) option-C numerics extensions (user-adjudicated 2026-07-30,
"C: cheap numerics extensions + A"): the three evidence-only probes named in
the design doc's "(K-bare) extension-route recon" adjudication block.
Evidence-only — none of this can close the `hbareSplit` leaf.

  C1 (adversarial seeds): deeper-degenerate corank-2 `G'` seeds at the DZ
     gadget (a la stress_extra.py), split at v = u1h2_2 (a = u1h2_1,
     b = u1h2_3).  Forced degenerations, each accepted only if the seed still
     verifies as a pencil witness at G''s target 108:
       D1: pt(b) moved to line(pt(u1), pt(a)) [intersected with b's hub plane
           pi(h2)] — the chain line passes through the far hub point u1;
       D2: pt(a) moved to line(pt(h2), pt(b)) [intersected with pi(u1)] —
           symmetric, through h2;
       D3: apex star collinear — h1, h2, h3 sampled on a LINE inside h0's
           star plane (deeper stratum for the apex normal);
       D4: all six hub points sampled in ONE global plane (hub-coplanar
           stratum; star planes stay individual).
     Then the usual extension choices (randoms + midpoint + on-line).
     Off-line failures, if any, are re-checked exact-Q before being reported.

  C2 (index >= 2 danger-gadget existence): search the structured family
     "subdivided cubic skeleton + apex hub h0 with three length-1 edges"
     for f(V) = +2 members with no proper f(W) >= 0 — i.e. corank-3 split
     seeds.  Length bound at index 2: every skeleton edge <= 3 (from the
     drop-one-edge subsets), so K3,3 is arithmetically excluded (the
     apex-to-u theta needs Sum >= 10 over three edges <= 3 each on the
     OTHER side too — checked, not assumed).  Skeletons probed: K3,3 (6v),
     cube Q3 (8v), Wagner V8 (8v), Petersen (10v).  Skeleton-level check:
     enumerate all CLOSED whole-path sub-multigraphs (closure: a length-1
     edge between two included hubs is forced in; max f over vertex subsets
     is attained on such sets — dangling paths, partial segments, isolated
     hubs and disconnected unions all strictly lower f).  Any hit on an
     8v skeleton is additionally certified by the full exact 2^|V|
     `exact_deficiency` table and probed gate-1/gate-2 style (bare
     attainment at corank 2, extension from corank-3 G' seeds).

  C3 (failure-locus mapping at corank 2): at fixed target-rank DZ G' seeds,
     is the extension failure set exactly line(pt a, pt b)?  Probes: many
     points ON the line (expect target-1), many random off-line points and
     off-line points on planes THROUGH the line (expect target), both split
     shapes (free placement at the non-hub split; in-plane placement at the
     hub-end split).  Any off-line failure is re-checked exact-Q.

Certification logic as in kbare_common (mod-p rank == target certifies
attainment; a mod-p shortfall is only reported as a true failure after an
exact-Q recheck agrees).

Reproduce:  cd notes/scripts/kbare && python3 optc.py c1|c2|c3
"""
import random, sys, time
from fractions import Fraction as F
from itertools import product
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from kbare_common import *
from gate2 import line_of_two_planes
from danger import dz_gadget, sample_dz_pencil

# ---------------- shared helpers ----------------

def line_meets_plane(p0, p1, n4, want_ne=None):
    """Point q = p0 + t (p1 - p0) with n4 . hat(q) = 0, exact.  Returns q or
    None (line parallel to plane / q coincides with want_ne)."""
    d = [p1[i] - p0[i] for i in range(3)]
    denom = sum(n4[i] * d[i] for i in range(3))
    if denom == 0:
        return None
    num = -(n4[3] + sum(n4[i] * p0[i] for i in range(3)))
    t = num / denom
    q = [p0[i] + t * d[i] for i in range(3)]
    if want_ne is not None and q == want_ne:
        return None
    return q

def ext_rank(edges_G, ptp, v, pv, exact=False):
    """Extension rank with pt[v] := pv; returns (witness_ok, rank or None)."""
    pt = dict(ptp)
    pt[v] = pv
    try:
        ok, _ = verify_pencil_witness(edges_G, pt)
    except AssertionError:
        return False, None
    if not ok:
        return False, None
    try:
        rk, _, _ = pencil_rank(edges_G, pt, exact=exact)
    except AssertionError:
        return False, None
    return True, rk

def seed_at_target(edges_Gp, sampler_edges_arg, rng, tGp):
    """Sample a G' pencil seed; return pt or None if degenerate/off-target."""
    try:
        ptp = sample_dz_pencil(sampler_edges_arg, rng)
        ok, _ = verify_pencil_witness(edges_Gp, ptp)
        assert ok
        rkp, _, _ = pencil_rank(edges_Gp, ptp)
    except (AssertionError, RuntimeError):
        return None
    return ptp if rkp == tGp else None

# ---------------- C1: adversarial degenerate G' seeds ----------------

def sample_dz_pencil_variant(edges, rng, apex_collinear=False, hub_coplanar=False):
    """sample_dz_pencil with forced deeper degenerations at sampling time."""
    deg = degrees(edges)
    nb = neighbors(edges)
    hubs = [v for v in verts_of(edges) if deg[v] >= 3]
    pt = {}
    n0 = rnonzero3(rng)
    pt['h0'] = rvec3(rng)
    if hub_coplanar:
        for h in hubs:
            if h != 'h0':
                pt[h] = point_in_plane3(pt['h0'], n0, rng)
    if apex_collinear:
        b1, _ = plane_basis(n0)
        for j, h in enumerate(sorted(nb['h0'], key=str)):
            s = rint(rng, 1, 9) + F(j)
            pt[h] = [pt['h0'][i] + s * b1[i] for i in range(3)]
    else:
        for h in sorted(nb['h0'], key=str):
            if h not in pt:
                pt[h] = point_in_plane3(pt['h0'], n0, rng)
    for h in hubs:
        if h not in pt:
            pt[h] = rvec3(rng)
    plane = {}
    for h in hubs:
        anchors = [hat(pt[h])] + [hat(pt[w]) for w in sorted(nb[h], key=str)
                                  if w in pt]
        plane[h] = normal4_through(anchors, rng)
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
    return pt, plane

def run_c1(nseeds=6, seed0=11000):
    edges_G = dz_gadget()
    v, a0, b0 = 'u1h2_2', 'u1h2_1', 'u1h2_3'
    edges_Gp = split_off(edges_G, v, a0, b0)
    dG, _ = exact_deficiency(edges_G)
    dGp, _ = exact_deficiency(edges_Gp)
    tG = 6 * (len(verts_of(edges_G)) - 1) - dG
    tGp = 6 * (len(verts_of(edges_Gp)) - 1) - dGp
    print(f"===== C1: adversarial degenerate G' seeds (DZ split at {v}; "
          f"target(G')={tGp}, corank {5*len(edges_Gp)-tGp}; target(G)={tG}) =====")
    summary = {}
    for tag in ('D1', 'D2', 'D3', 'D4'):
        n_valid = n_allok = 0
        offline_fails = []
        for s in range(nseeds):
            rng = random.Random(seed0 + 100 * ('D1D2D3D4'.index(tag) // 2) + s)
            try:
                if tag == 'D3':
                    ptp, plane = sample_dz_pencil_variant(edges_Gp, rng,
                                                          apex_collinear=True)
                elif tag == 'D4':
                    ptp, plane = sample_dz_pencil_variant(edges_Gp, rng,
                                                          hub_coplanar=True)
                else:
                    ptp, plane = sample_dz_pencil_variant(edges_Gp, rng)
                # D1/D2: post-adjust the chain points into deeper position
                if tag == 'D1':
                    q = line_meets_plane(ptp[a0], ptp['u1'], plane['h2'],
                                         want_ne=ptp[a0])
                    if q is None:
                        continue
                    ptp[b0] = q
                if tag == 'D2':
                    q = line_meets_plane(ptp[b0], ptp['h2'], plane['u1'],
                                         want_ne=ptp[b0])
                    if q is None:
                        continue
                    ptp[a0] = q
                ok, _ = verify_pencil_witness(edges_Gp, ptp)
                assert ok
                rkp, _, _ = pencil_rank(edges_Gp, ptp)
            except (AssertionError, RuntimeError):
                continue
            if rkp != tGp:
                print(f"  {tag} seed {s}: degenerate seed fell BELOW target' "
                      f"({rkp}/{tGp}) — outside (K-bare-ext)'s antecedent, skipped")
                continue
            n_valid += 1
            pa, pb = ptp[a0], ptp[b0]
            t = F(rng.randint(2, 9), rng.randint(1, 3))
            choices = [(f"random{j}", rvec3(rng)) for j in range(3)]
            choices += [("midpoint", [(pa[i] + pb[i]) / 2 for i in range(3)]),
                        ("on-line", [pa[i] + t * (pb[i] - pa[i]) for i in range(3)])]
            res = []
            for lbl, pv in choices:
                okw, rk = ext_rank(edges_G, ptp, v, pv)
                if lbl.startswith(('random',)) and okw and rk is not None and rk != tG:
                    okx, rkx = ext_rank(edges_G, ptp, v, pv, exact=True)
                    rk = rkx
                    if rkx != tG:
                        offline_fails.append((tag, s, lbl, rkx))
                res.append((lbl, rk if okw else None))
            succ_off = [1 for lbl, rk in res if lbl.startswith('random') and rk == tG]
            line_rks = [rk for lbl, rk in res if not lbl.startswith('random')]
            print(f"  {tag} seed {s}: G' AT target' (corank {5*len(edges_Gp)-tGp}); "
                  f"off-line {len(succ_off)}/3 attain {tG}; on-line/mid ranks {line_rks}")
            if len(succ_off) == 3:
                n_allok += 1
        summary[tag] = (n_allok, n_valid, offline_fails)
    print("\n  C1 SUMMARY (per degeneration: seeds-with-all-off-line-attaining / "
          "valid target'-rank seeds):")
    for tag, (ok, tot, fails) in summary.items():
        print(f"    {tag}: {ok}/{tot}"
              f"{'' if not fails else '  EXACT-Q-CONFIRMED OFF-LINE FAILURES: ' + str(fails)}")
    return summary

# ---------------- C2: index-2 danger-gadget search ----------------

SKELETONS = {
    'K3,3 (6v)': ([(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
                   (2, 3), (2, 4), (2, 5)], 0),
    'cube Q3 (8v)': ([(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7),
                      (7, 4), (0, 4), (1, 5), (2, 6), (3, 7)], 0),
    'Wagner V8 (8v)': ([(i, (i + 1) % 8) for i in range(8)]
                       + [(i, i + 4) for i in range(4)], 0),
    'Petersen (10v)': ([(i, (i + 1) % 5) for i in range(5)]
                       + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
                       + [(i, i + 5) for i in range(5)], 0),
}

def skeleton_check(skel, apex, lengths):
    """All closed whole-path proper sub-multigraphs must have f <= -1.
    lengths: dict edge->l.  Returns (ok, worst)."""
    k = len(skel)
    full = (1 << k) - 1
    worst = None
    for S in range(1, full):  # proper edge subsets only
        hubs = set()
        sl = 0
        for i in range(k):
            if S >> i & 1:
                hubs.add(skel[i][0])
                hubs.add(skel[i][1])
                sl += lengths[skel[i]]
        if len(hubs) < 2:
            continue
        # closure: length-1 edges between included hubs must be in S
        closed = True
        for i in range(k):
            if not (S >> i & 1) and lengths[skel[i]] == 1 \
                    and skel[i][0] in hubs and skel[i][1] in hubs:
                closed = False
                break
        if not closed:
            continue
        kp = bin(S).count('1')
        f = 6 * (kp - len(hubs) + 1) - sl
        if worst is None or f > worst:
            worst = f
        if f >= 0:
            return False, worst
    return True, worst

def build_from_skeleton(skel, lengths):
    edges = []
    for (x, y) in skel:
        l = lengths[(x, y)]
        prev = f's{x}'
        for i in range(1, l):
            w = f'p{x}_{y}_{i}'
            edges.append((prev, w))
            prev = w
        edges.append((prev, f's{y}'))
    return edges

def run_c2():
    print("===== C2: index-2 danger-gadget existence search "
          "(subdivided cubic skeleton + apex, per-edge length <= 3) =====")
    hits = []
    for name, (skel, apex) in SKELETONS.items():
        H = len(set(x for e in skel for x in e))
        target_sum = 3 * H + 4  # f(V) = 3H + 6 - Sum(l) = +2
        apex_edges = [e for e in skel if apex in e]
        other = [e for e in skel if apex not in e]
        need = target_sum - len(apex_edges)  # apex edges pinned at length 1
        n_assign = n_pass = 0
        example = None
        for ls in product((1, 2, 3), repeat=len(other)):
            if sum(ls) != need:
                continue
            n_assign += 1
            lengths = {e: 1 for e in apex_edges}
            lengths.update(dict(zip(other, ls)))
            ok, worst = skeleton_check(skel, apex, lengths)
            if ok:
                n_pass += 1
                if example is None:
                    example = dict(lengths)
        print(f"  {name}: |skel E|={len(skel)} Sum(l)={target_sum} "
              f"(apex edges = 1,1,1): {n_assign} candidate assignments, "
              f"{n_pass} pass the proper-subgraph check"
              f"{' — HIT' if n_pass else ' — EXCLUDED in this family'}")
        if example:
            hits.append((name, skel, example))
    for name, skel, lengths in hits:
        edges = build_from_skeleton(skel, lengths)
        n = len(verts_of(edges))
        print(f"\n  certifying hit on {name}: lengths="
              f"{ {e: l for e, l in sorted(lengths.items())} } |V|={n} |E|={len(edges)}")
        if n <= 26:
            d, info = exact_deficiency(edges)
            hubn = closed_hub_nbhds(edges)
            print(f"    exact: def={d} f(V)={5*len(edges)-6*(n-1)} "
                  f"maxf(proper)={info['maxf_proper_ge2']} 2EC={is_2ec(edges)} "
                  f"max closedHubNbhd={max(hubn.values())} "
                  f"({'INFEASIBLE' if max(hubn.values()) >= 4 else 'feasible-eligible'})")
        else:
            print("    (|V| > 26: full exact 2^|V| certification skipped; "
                  "skeleton-level certificate only)")
    if not hits:
        print("\n  C2 SUMMARY: no index-2 member found in the probed family "
              "(K3,3/cube/Wagner/Petersen skeletons, apex (1,1,1), lengths <= 3).")
    return hits

def run_c2_gate(hits, nsamples=4, nseeds=4, seed0=13000):
    """Mini gate on the first certified index-2 hit: bare attainment at G
    (corank 2) + extension from corank-3 G' seeds."""
    for name, skel, lengths in hits:
        edges_G = build_from_skeleton(skel, lengths)
        n = len(verts_of(edges_G))
        if n > 26:
            continue
        d, _ = exact_deficiency(edges_G)
        tG = 6 * (n - 1) - d
        print(f"\n  mini-gate on {name} hit: target(G)={tG}, rows={5*len(edges_G)} "
              f"(corank {5*len(edges_G)-tG} at target)")
        # rename apex vertex to 'h0' for the sampler
        ren = {f's{x}': (f'h0' if x == 0 else f's{x}') for x in
               set(v for e in skel for v in e)}
        edges_G = [(ren.get(u, u), ren.get(w, w)) for (u, w) in edges_G]
        best = -1
        for s in range(nsamples):
            rng = random.Random(seed0 + s)
            try:
                pt = sample_dz_pencil(edges_G, rng)
                ok, _ = verify_pencil_witness(edges_G, pt)
                assert ok
                rk, _, _ = pencil_rank(edges_G, pt)
            except (AssertionError, RuntimeError):
                print(f"    bare sample {s}: degenerate, skipped")
                continue
            print(f"    bare pencil sample {s}: rank {rk} / {tG} "
                  f"[{'ATTAINED' if rk == tG else 'short by ' + str(tG - rk)}]")
            best = max(best, rk)
        # split at a length-3 path's first interior: the safe pair is
        # (v, second interior), so a = the skeleton hub end (KT-faithful
        # hub-end shape: p_v confined to the hub's star plane), b = deg-2.
        deg = degrees(edges_G)
        nb = neighbors(edges_G)
        v = next(x for x in verts_of(edges_G) if deg[x] == 2
                 and any(deg[w] == 2 for w in nb[x])
                 and any(deg[w] >= 3 for w in nb[x]))
        a0, b0 = sorted(nb[v], key=str)
        hub_end = next(x for x in (a0, b0) if deg[x] >= 3)
        edges_Gp = split_off(edges_G, v, a0, b0)
        dGp, _ = exact_deficiency(edges_Gp)
        tGp = 6 * (n - 2) - dGp
        print(f"    split at {v} (hub end {hub_end}): target(G')={tGp}, "
              f"rows={5*len(edges_Gp)} => corank {5*len(edges_Gp)-tGp} at target'")
        n_ok = n_seed = 0
        for s in range(nseeds):
            rng = random.Random(seed0 + 50 + s)
            ptp = seed_at_target(edges_Gp, edges_Gp, rng, tGp)
            if ptp is None:
                print(f"    seed {s}: G' sample degenerate/off-target, skipped")
                continue
            # placement plane: through the hub end and its G-neighbours != v
            anchors = [hat(ptp[hub_end])] + [hat(ptp[w]) for w in
                                             sorted(nb[hub_end], key=str) if w != v]
            ns = nullspace(anchors)
            if not ns or all(ns[0][i] == 0 for i in range(3)):
                print(f"    seed {s}: hub-end placement plane degenerate, skipped")
                continue
            n_seed += 1
            pa, pb = ptp[a0], ptp[b0]
            t = F(rng.randint(2, 9), rng.randint(1, 3))
            res = []
            for j in range(3):
                pv = point_on_affine_plane4(ns[0], rng)
                okw, rk = ext_rank(edges_G, ptp, v, pv)
                if okw and rk is not None and rk != tG:
                    okx, rk = ext_rank(edges_G, ptp, v, pv, exact=True)
                res.append((f'in-plane{j}', rk if okw else None))
            okw, rk = ext_rank(edges_G, ptp, v,
                               [pa[i] + t * (pb[i] - pa[i]) for i in range(3)])
            res.append(('on-line', rk if okw else None))
            succ = [1 for lbl, rk in res if lbl.startswith('in-plane') and rk == tG]
            print(f"    seed {s}: corank-{5*len(edges_Gp)-tGp} G' seed; extension: "
                  f"off-line in-plane {len(succ)}/3 attain {tG}; results {res}")
            if len(succ) == 3:
                n_ok += 1
        print(f"    >>> {n_ok}/{n_seed} corank-3 seeds: all off-line in-plane "
              f"choices attain")

# ---------------- C3: failure-locus mapping at corank 2 ----------------

def run_c3(seed0=15000):
    edges_G = dz_gadget()
    results = []
    for (v, tag) in [('u1h2_2', 'non-hub ends'), ('u1h2_1', 'hub end (a = u1)')]:
        a0, b0 = sorted(neighbors(edges_G)[v], key=str)
        edges_Gp = split_off(edges_G, v, a0, b0)
        dG, _ = exact_deficiency(edges_G)
        dGp, _ = exact_deficiency(edges_Gp)
        tG = 6 * (len(verts_of(edges_G)) - 1) - dG
        tGp = 6 * (len(verts_of(edges_Gp)) - 1) - dGp
        print(f"\n===== C3: failure-locus map, split at {v} ({tag}); "
              f"corank {5*len(edges_Gp)-tGp} G' seeds =====")
        hubs_end = [x for x in (a0, b0) if degrees(edges_G)[x] >= 3]
        rng = random.Random(seed0)
        ptp = None
        for s in range(12):
            ptp = seed_at_target(edges_Gp, edges_Gp, random.Random(seed0 + s), tGp)
            if ptp is not None:
                break
        assert ptp is not None, "no target-rank G' seed found"
        pa, pb = ptp[a0], ptp[b0]
        dline = [pb[i] - pa[i] for i in range(3)]
        # placement domain: free space, or the hub end's star plane
        n_pl = None
        if hubs_end:
            nbG = neighbors(edges_G)
            h = hubs_end[0]
            anchors = [hat(ptp[h])] + [hat(ptp[w]) for w in sorted(nbG[h], key=str)
                                       if w != v]
            ns = nullspace(anchors)
            assert ns and any(ns[0][i] != 0 for i in range(3))
            n_pl = ns[0]
        # (i) ON the line: expect exactly target-1
        on_line_rks = {}
        ts = [F(x, y) for x, y in [(-7, 1), (-3, 1), (-3, 2), (-1, 2), (1, 3),
                                   (2, 3), (3, 2), (2, 1), (4, 1), (7, 2),
                                   (5, 1), (8, 1), (-5, 3), (9, 4), (11, 3)]]
        n_exact_line = 0
        for t in ts:
            pv = [pa[i] + t * dline[i] for i in range(3)]
            okw, rk = ext_rank(edges_G, ptp, v, pv)
            if okw and rk is not None and rk < tG and n_exact_line < 3:
                okx, rkx = ext_rank(edges_G, ptp, v, pv, exact=True)
                if rkx != rk:
                    rk = rkx
                n_exact_line += 1
            on_line_rks[str(t)] = rk if okw else None
        line_vals = set(rk for rk in on_line_rks.values() if rk is not None)
        n_line_ok = sum(1 for rk in on_line_rks.values() if rk is not None)
        print(f"  ON line(a,b): {n_line_ok}/{len(ts)} valid witnesses; "
              f"rank values {sorted(line_vals)} (target {tG}; first 3 exact-Q-checked)")
        # (ii) random off-line
        n_off, off_fails = 0, []
        N_OFF = 80
        for j in range(N_OFF):
            pv = rvec3(rng) if n_pl is None else point_on_affine_plane4(n_pl, rng)
            # skip accidental on-line points
            cross_chk = [pv[i] - pa[i] for i in range(3)]
            onl = all(cross_chk[i] * dline[j2] == cross_chk[j2] * dline[i]
                      for i in range(3) for j2 in range(3))
            if onl:
                continue
            okw, rk = ext_rank(edges_G, ptp, v, pv)
            if not okw:
                continue
            n_off += 1
            if rk != tG:
                okx, rkx = ext_rank(edges_G, ptp, v, pv, exact=True)
                if rkx != tG:
                    off_fails.append((str(pv), rkx))
        dom = 'free 3-space' if n_pl is None else "the hub end's star plane"
        print(f"  OFF line, random in {dom}: {n_off} valid placements, "
              f"{len(off_fails)} exact-Q-confirmed failures"
              f"{'' if not off_fails else ': ' + str(off_fails)}")
        # (iii) off-line on planes THROUGH the line (free-placement shape only)
        plane_fails = []
        n_pl_pts = 0
        if n_pl is None:
            for pl in range(2):
                d2 = rnonzero3(rng)
                for (snum, tnum) in [(-2, 1), (-1, 1), (-1, 2), (0, 1), (1, 2),
                                     (1, 1), (2, 1), (3, 1), (0, 2), (2, 3)]:
                    s_, t_ = F(snum), F(tnum, 1)
                    if t_ == 0:
                        continue
                    pv = [pa[i] + s_ * dline[i] + t_ * d2[i] for i in range(3)]
                    okw, rk = ext_rank(edges_G, ptp, v, pv)
                    if not okw:
                        continue
                    n_pl_pts += 1
                    if rk != tG:
                        okx, rkx = ext_rank(edges_G, ptp, v, pv, exact=True)
                        if rkx != tG:
                            plane_fails.append((pl, str((s_, t_)), rkx))
            print(f"  OFF line, on 2 random planes THROUGH the line: {n_pl_pts} "
                  f"valid placements, {len(plane_fails)} exact-Q-confirmed failures"
                  f"{'' if not plane_fails else ': ' + str(plane_fails)}")
        results.append((tag, sorted(line_vals), len(off_fails) + len(plane_fails)))
    print("\n  C3 SUMMARY:")
    for tag, lv, nf in results:
        print(f"    {tag}: on-line ranks {lv}; off-line failures {nf}")
    return results

if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t0 = time.time()
    if which in ('c1', 'all'):
        run_c1()
    if which in ('c2', 'all'):
        hits = run_c2()
        if hits:
            run_c2_gate(hits)
    if which in ('c3', 'all'):
        run_c3()
    print(f"\n[optc {which}: {time.time() - t0:.0f}s]")
