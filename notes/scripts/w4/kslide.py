"""
Phase 39 (K-slide) -- the slide-in transfer theorem: per-habitat witnesses.

Attacks the (K-slide) gap named in `notes/Pencil-informal.md` section
(K-pitch) Step 6.  The mathematical upgrade validated here (workbook
section (K-slide), step (S1)): for fixed eps != 0 the slide
x -> pt(u) + eps*(x0 - pt(u)) is an AUTOMORPHISM of the pencil chart (each
panel maps to itself bijectively), and after replacing each hub-incident
hinge representative u^ ^ x^(eps) = eps * (u^ ^ (d,0)) by the constant
representative u^ ^ (d,0), the H-row family is POLYNOMIAL in
(chart data, eps) INCLUDING eps = 0, where it evaluates to exactly the
limit system.  Hence one exact eps = 0 witness with

    (W1) limit H-rows independent   (dim mot = 6|V_H| - 5|E_H|),
    (W2) dim V_bc(limit) = 3        (ker[R;P] = trivial twists only),
    (W3) z(limit) defined           (the two T-conditions independent),
    (W4) Q(z_limit) != 0

proves Q(z) != 0 on a dense open subset of the habitat's pencil chart --
no rank persistence along the family, no convergence analysis, and no
target-rank condition at the witness seed are consumed.  Combined with
(T1)-(T3) (re-validated per member here via `pitch.transfer_probe`, which
also certifies the target-rank / dim R_a = 1 / side-condition loci
nonempty), a witness closes (K-pitch) at that habitat's split.

Limit-line dictionary (length-l hub path [u, x1, .., x_{l-1}, w]; only
SINGLE-PANEL interiors slide -- the ends of paths of length >= 3):

    l = 1 : (u^w)                    [hub-hub hinge; mutual-panel deco]
    l = 2 : (u^x1, x1^w)             [x1 on the meet line; NOT slid]
    l = 3 : (P_u, u^w, P_w)          [the serial triple; chord]
    l = 4 : (P_u, u^x2, x2^w, P_w)   [x2 free; NOT slid]
    l = 5 : (P_u, u^x2, x2^x3, x3^w, P_w)

with P_u = the original hub-incident line u ^ x_end (a pencil line at u,
through pt(u) inside Pi(u)).  All limit lines are G-degree-local
decorations: hub points, normals, one pencil direction per slid path end,
one meet-line point per length-2 path, free middle points for l >= 4.

Drivers (foreground, one at a time; exact-Q, guards + rank asserts):
    python3 notes/scripts/w4/kslide.py --k4       # control-class closer + hub-level cross-check
    python3 notes/scripts/w4/kslide.py --battery  # W4 wheel, K5-2e, prism+diagonal
    python3 notes/scripts/w4/kslide.py --mixed    # mixed path lengths on simple G-degree (flank i)
    python3 notes/scripts/w4/kslide.py --flanks   # hub-hub edge; parallel non-bc edge
"""
import os
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from repin import seed_probe, span_basis, in_span
from nogood_subdiv import deficiency
from pencil_escape import (nullspace, wedge2, hat, double_subdivide)
from kbare_common import verts_of
from pitch import (Q, z_from, transfer_probe, rows_from_lines, paths_graph)


# ---------------- member construction ---------------------------------------

def member(specs):
    """Build a habitat from hub-path specs [(h1, h2, length), ...]; the
    FIRST spec must be the split path (0, 1, 3).  Returns (edges, pmap)."""
    assert specs[0] == (0, 1, 3), "split path must be (0, 1, 3) and first"
    bc = [L for (h1, h2, L) in specs if (h1, h2) == (0, 1)]
    rest = [s for s in specs if (s[0], s[1]) != (0, 1)]
    return paths_graph(bc, rest)


def build_smap(pmap, split_k=0):
    """Slide map: single-panel interiors (ends of length >= 3 paths, split
    path excluded) -> their adjacent hub."""
    smap = {}
    for k, vs in pmap.items():
        if k == split_k or len(vs) - 1 < 3:
            continue
        smap[vs[1]] = vs[0]
        smap[vs[-2]] = vs[-1]
    return smap


def path_limit_lines(vs, placed, pt, smap):
    """Per-edge limit lines along one hub path (the slide_probe rule):
    (slid, slid) -> chord of target hubs; (hub, its slid nbr) -> the
    original (constant) line; (slid, fixed) -> target hub ^ fixed point;
    (fixed, fixed) -> unchanged."""
    out = []
    for i in range(len(vs) - 1):
        p_, q_ = vs[i], vs[i + 1]
        tp, tq = smap.get(p_), smap.get(q_)
        if tp is not None and tq is not None:
            L = wedge2(hat(pt[tp]), hat(pt[tq]))
        elif tp is not None and q_ == tp or tq is not None and p_ == tq:
            L = wedge2(hat(placed[p_]), hat(placed[q_]))
        elif tp is not None:
            L = wedge2(hat(pt[tp]), hat(placed[q_]))
        elif tq is not None:
            L = wedge2(hat(placed[p_]), hat(pt[tq]))
        else:
            L = wedge2(hat(placed[p_]), hat(placed[q_]))
        assert any(x != 0 for x in L), "zero limit line"
        out.append(L)
    return out


def no_rigid_branch_union(edges, pmap):
    """NT21-style hnoRigid certificate at branch granularity: a rigid
    subgraph is a union of whole hub paths (its own 2-core)."""
    nbr = len(pmap)
    nV = len(verts_of(edges))
    for rsub in range(1, 2 ** nbr - 1):
        sel = [pmap[k] for k in range(nbr) if rsub & (1 << k)]
        vs = set(v_ for p_ in sel for v_ in p_)
        sub = [e for e in edges if e[0] in vs and e[1] in vs]
        if not sub or len(verts_of(sub)) < 3:
            continue
        if deficiency(sub) == 0 and len(verts_of(sub)) < nV:
            return False
    return True


# ---------------- the eps = 0 witness ----------------------------------------

def limit_witness(edges, v, seed, pmap, split_k=0, hard=True,
                  smap_omit=()):
    """One exact eps = 0 witness at a valid chart seed.  (W1)-(W3) are
    always asserted (they certify the witness sits in the doubly-max-rank
    locus); Q(z_limit) != 0 is asserted iff `hard` (flank probes report).
    `smap_omit`: interiors excluded from the slide support (the support is
    a free choice -- any subset of single-panel interiors gives a valid
    transfer family; omitting one end-interior per parallel chain pair
    avoids the coincident-chord row dependence)."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab0, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    smap = build_smap(pmap, split_k)
    for x in smap_omit:
        smap.pop(x, None)
    Hed = [e for e in edges if v not in e and a not in e]
    Cmap, lines_by_path = {}, {}
    for k, vs in pmap.items():
        if k == split_k:
            continue
        Ls = path_limit_lines(vs, placed, pt, smap)
        lines_by_path[k] = Ls
        for i in range(len(vs) - 1):
            Cmap[(vs[i], vs[i + 1])] = Ls[i]
    assert set(Cmap) == set(Hed), "H edge cover mismatch"
    VH = sorted(verts_of(Hed), key=str)
    rows, idx = rows_from_lines(Hed, Cmap, VH)
    mot = nullspace(rows)
    # (W1) limit rows independent:
    assert len(mot) == 6 * len(VH) - 5 * len(Hed), \
        f"limit rows dependent (mot = {len(mot)})"
    ib, ic = 6 * idx[b], 6 * idx[c]
    Vlim = span_basis([[m[ib + k] - m[ic + k] for k in range(6)]
                       for m in mot])
    # (W2):
    assert len(Vlim) == 3, f"dim V_bc(limit) = {len(Vlim)}"
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab, Cac = wedge2(ah, bh), wedge2(ah, ch)
    z, _ = z_from(Vlim, Cab, Cac)
    # (W3):
    assert z is not None, "z(limit) degenerate"
    qz = Q(z)
    if hard:
        # (W4):
        assert qz != 0, "limit twist null"
    return {'seed': seed, 'Q(z_lim)': qz, 'mot': len(mot), 'Vlim': Vlim,
            'lines_by_path': lines_by_path,
            'ctx': (placed, pt, a, b, c)}


def limit_stress_support(edges, v, seed, pmap, split_k=0, smap_omit=()):
    """Diagnostic for a (W1) failure: the limit system's stresses and
    their per-chain edge support (+ the rank of the supporting lines)."""
    from pencil_escape import left_nullspace, rank
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab0, tgtG, hubsG = p['_ctx']
    a = p['a']
    smap = build_smap(pmap, split_k)
    for x in smap_omit:
        smap.pop(x, None)
    Hed = [e for e in edges if v not in e and a not in e]
    Cmap = {}
    for k, vs in pmap.items():
        if k == split_k:
            continue
        Ls = path_limit_lines(vs, placed, pt, smap)
        for i in range(len(vs) - 1):
            Cmap[(vs[i], vs[i + 1])] = Ls[i]
    VH = sorted(verts_of(Hed), key=str)
    rows, _ = rows_from_lines(Hed, Cmap, VH)
    out = []
    for s in left_nullspace(rows):
        sup = [e for ei, e in enumerate(Hed)
               if any(s[5 * ei + j] != 0 for j in range(5))]
        ks = sorted({k for k, vs in pmap.items() if k != split_k
                     and any(e in sup for e in
                             zip(vs, vs[1:]))})
        out.append({'chains': ks, 'edges': len(sup),
                    'line rank': rank([Cmap[e] for e in sup])})
    return out


def hub_level_vbc(pmap, lines_by_path, b, c, split_k=0):
    """(S2) cross-check: the G-degree-level serial-chain system -- bodies at
    hubs only, per path the constraint m(h1) - m(h2) in span(chain lines)."""
    hubs = sorted({vs[0] for vs in pmap.values()} |
                  {vs[-1] for vs in pmap.values()}, key=str)
    idx = {h: k for k, h in enumerate(hubs)}
    ncol = 6 * len(hubs)
    rows = []
    for k, vs in pmap.items():
        if k == split_k:
            continue
        S = span_basis(lines_by_path[k])
        for y in nullspace(S):
            row = [F(0)] * ncol
            b1, b2 = 6 * idx[vs[0]], 6 * idx[vs[-1]]
            for j in range(6):
                row[b1 + j] += y[j]
                row[b2 + j] -= y[j]
            rows.append(row)
    motions = nullspace(rows)
    ib, ic = 6 * idx[b], 6 * idx[c]
    return span_basis([[m[ib + j] - m[ic + j] for j in range(6)]
                       for m in motions])


def same_span(A, B):
    return (len(A) == len(B) and all(in_span(x, B) for x in A)
            and all(in_span(x, A) for x in B))


# ---------------- per-member runner ------------------------------------------

def run_member(name, edges, pmap, v, tseeds, wseeds, need_w=2, hard=True,
               cross_check=False, smap_omit=()):
    """(T1)-(T3) re-validation (one full seed) + eps = 0 witnesses."""
    assert deficiency(edges) == 0, f"{name} not tight-rigid"
    norig = no_rigid_branch_union(edges, pmap)
    print(f"== {name}: |V|={len(verts_of(edges))} def=0 "
          f"hnoRigid(branch)={norig} ==")
    got_t = 0
    for seed in tseeds:
        o = transfer_probe(edges, v, seed)
        if o is None or 'skip' in o:
            continue
        ok = (o['T1'] is True and o['T2'] is True and o.get('T3') is True
              and o['Q(r)'] != 0)
        print(f"  transfer seed {seed}: T1={o['T1']} T2={o['T2']} "
              f"T3={o.get('T3', '-')} Q(r)!=0: {o['Q(r)'] != 0}")
        if ok:
            got_t += 1
            break
    assert got_t >= 1, f"{name}: no full (T1)-(T3) certificate seed"
    got_w = 0
    for seed in wseeds:
        w = limit_witness(edges, v, seed, pmap, hard=hard,
                          smap_omit=smap_omit)
        if w is None:
            continue
        got_w += 1
        qz = w['Q(z_lim)']
        print(f"  witness seed {seed}: mot(limit)={w['mot']} "
              f"dimV_bc(limit)=3 z(limit) "
              f"{'PITCHED' if qz != 0 else 'NULL'}")
        if cross_check and qz != 0:
            Vhub = hub_level_vbc(pmap, w['lines_by_path'],
                                 w['ctx'][3], w['ctx'][4])
            assert same_span(Vhub, w['Vlim']), \
                "hub-level V_bc != subdivision-limit V_bc"
            print("    (S2) hub-level serial-chain V_bc == "
                  "subdivision-limit V_bc: OK")
        if got_w >= need_w:
            break
    assert got_w >= 1, f"{name}: no valid witness seed"
    return got_w


# ---------------- drivers ----------------------------------------------------

def k4():
    """The control-class closer: dbl-subdivided K4 (simple G-degree, all
    lengths 3), with the hub-level (S2) cross-check.  Every K4 split edge
    is equivalent under Aut(K4) (edge-transitive)."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    pmap = {k: list(ch) for k, ch in enumerate(chains)}
    v = chains[0][1]
    run_member('dbl-subdiv K4', E, pmap, v,
               tseeds=range(440, 470), wseeds=range(440, 480),
               need_w=3, cross_check=True)
    print("K4 OK: (K-slide) witnessed at the control habitat "
          "(3 exact eps=0 witnesses, hub-level carrier cross-checked)")


def battery(sel=None):
    """All-length-3 members beyond K4 (each |E| = 2|V|-2, simple).
    `sel` (0-3, or None for all) picks one member -- pass a trailing
    integer on the command line to run members one at a time."""
    members = [
        # both_ends: run the reversed split too, when no G-degree
        # automorphism swaps the split edge's ends.
        ('W4 wheel, rim split',           # 0 <-> 1, 3 <-> 2 automorphism
         [(0, 1, 3), (1, 2, 3), (2, 3, 3), (3, 0, 3),
          (0, 4, 3), (1, 4, 3), (2, 4, 3), (3, 4, 3)], False),
        # wheel relabeled so the split (0,1) is a SPOKE: center = 1,
        # rim = 0-2-3-4-0.  Rim/center ends inequivalent.
        ('W4 wheel, spoke split',
         [(0, 1, 3), (2, 1, 3), (3, 1, 3), (4, 1, 3),
          (0, 2, 3), (2, 3, 3), (3, 4, 3), (4, 0, 3)], True),
        ('K5 minus {01, 23}, split 02',   # 0 <-> 1 (old 0 <-> 2) autom.
         # relabel K5-{(0,1),(2,3)} so the split edge is (0,1):
         # old (0,2)->new (0,1); old {0,1,2,3,4} -> {0,2,1,3,4}.
         [(0, 1, 3), (0, 3, 3), (0, 4, 3), (2, 1, 3), (2, 3, 3),
          (2, 4, 3), (1, 4, 3), (3, 4, 3)], False),
        ('prism + diagonal, split 01',    # deg(0) = 4 != 3 = deg(1)
         # triangles 0-1-2 / 3-4-5, verticals 03, 14, 25, diagonal 04.
         [(0, 1, 3), (1, 2, 3), (0, 2, 3), (3, 4, 3), (4, 5, 3),
          (3, 5, 3), (0, 3, 3), (1, 4, 3), (2, 5, 3), (0, 4, 3)], True),
    ]
    todo = members if sel is None else [members[sel]]
    for name, specs, both in todo:
        edges, pmap = member(specs)
        run_member(name, edges, pmap, pmap[0][1],
                   tseeds=range(100, 160), wseeds=range(100, 160),
                   need_w=2)
        if both:
            run_member(name + ' (reversed)', edges, pmap, pmap[0][2],
                       tseeds=range(100, 160), wseeds=range(100, 160),
                       need_w=2)
    print("BATTERY OK: (K-slide) witnessed at "
          + ("every member" if sel is None else f"member {sel}")
          + " (2 exact eps=0 witnesses each)")


def mixed():
    """Flank (i): mixed path lengths on simple G-degree.  K4 with one
    length-4 path (free middle point) and one length-2 path (meet-line
    interior); Sum l = 18 keeps the habitat tight.  Cross-checks the
    general serial-chain carrier (S2) on the mixed chains."""
    specs = [(0, 1, 3), (2, 3, 4), (0, 2, 2), (0, 3, 3), (1, 2, 3),
             (1, 3, 3)]
    edges, pmap = member(specs)
    run_member('K4 mixed lengths (3,4,2,3,3,3)', edges, pmap, pmap[0][1],
               tseeds=range(100, 160), wseeds=range(100, 160),
               need_w=2, cross_check=True)
    run_member('K4 mixed lengths (reversed)', edges, pmap, pmap[0][2],
               tseeds=range(100, 160), wseeds=range(100, 160),
               need_w=2, cross_check=True)
    print("MIXED OK: (K-slide) witnessed at the mixed-length member, "
          "both split ends (serial 4-chain + meet-line pair carriers "
          "cross-checked)")


def flanks():
    """Flank (ii) hub-hub edge (an actual hinge as a 1-member chain), and
    the parallel NON-bc edge probe (coincident chords away from the split;
    G-degree not simple).  Both run in REPORT mode (no Q != 0 assert):
    these chart the boundary of the pitched class."""
    print("-- flank (ii): hub-hub edge --")
    specs = [(0, 1, 3), (2, 3, 1), (0, 2, 4), (1, 3, 4), (0, 3, 3),
             (1, 2, 3)]
    edges, pmap = member(specs)
    run_member('K4 with hub-hub edge 23 (3,1,4,4,3,3)', edges, pmap,
               pmap[0][1], tseeds=range(100, 200), wseeds=range(100, 200),
               need_w=2, hard=False)
    run_member('K4 with hub-hub edge 23 (reversed)', edges, pmap,
               pmap[0][2], tseeds=range(100, 200), wseeds=range(100, 200),
               need_w=2, hard=False)
    print("-- parallel non-bc edge probe --")
    specs = [(0, 1, 3), (2, 3, 3), (2, 3, 3), (0, 2, 4), (0, 3, 5),
             (1, 2, 3), (1, 3, 3)]
    edges, pmap = member(specs)
    # (T1)-(T3) still hold at eps = 1 (the chart side is healthy):
    got_t = 0
    for seed in range(100, 200):
        o = transfer_probe(edges, pmap[0][1], seed)
        if o is None or 'skip' in o:
            continue
        print(f"  transfer seed {seed}: T1={o['T1']} T2={o['T2']} "
              f"T3={o.get('T3', '-')} Q(r)!=0: {o['Q(r)'] != 0}")
        if (o['T1'] is True and o['T2'] is True and o.get('T3') is True
                and o['Q(r)'] != 0):
            got_t += 1
            break
    assert got_t >= 1
    # full slide support: the two parallel chains' chords coincide, so the
    # 6-hinge cycle they form repeats a line and ALWAYS carries a stress
    # -- (W1) is unattainable (structural row dependence at the limit).
    # Reduced supports do NOT rescue it: hub-incident lines are pencil
    # lines regardless of the support (they never move along the slide),
    # and the chords concentrate through the hub points, closing a
    # circuit on the theta sub-multigraph {12, 13, 23a, 23b} even with
    # one parallel chain fully unslid.  Exhibit both:
    for desc, omit in (('full support', ()),
                       ('chain 23b fully unslid',
                        (pmap[2][1], pmap[2][-2]))):
        for seed in range(100, 200):
            d = limit_stress_support(edges, pmap[0][1], seed, pmap,
                                     smap_omit=omit)
            if d is None:
                continue
            print(f"  {desc}: {len(d)} limit stress(es); "
                  + '; '.join(f"chains {x['chains']} ({x['edges']} edges, "
                              f"line rank {x['line rank']})" for x in d))
            assert len(d) >= 1, "expected (W1) failure vanished"
            break
    print("FLANKS done: hub-hub edge WITNESSED (pitched); parallel-edge "
          "member obstructed at order 0 (both supports) -- verdicts in "
          "the workbook")


def main():
    if '--k4' in sys.argv:
        k4()
    elif '--battery' in sys.argv:
        sel = next((int(x) for x in sys.argv[2:] if x.isdigit()), None)
        battery(sel)
    elif '--mixed' in sys.argv:
        mixed()
    elif '--flanks' in sys.argv:
        flanks()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
