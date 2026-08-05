"""
Phase 39, kernel-(K) fan-out direction C -- the PURE CONDITION of the slide-in
limit carrier, un-specialized.

The question this driver settles (workbook draft section (K-pure)): can the
class-uniform escape be settled by showing the pure condition of the limit
carrier is not identically zero on the decoration variety, instead of
exhibiting a decoration where it survives (the tetrahedral collapse of
`notes/Pencil-informal.md` section (K-slide-cl), whose four hub positions cap
chi(G*) at 4)?

Answer: NO -- and the obstruction is not a hardness, it is a MISMATCH of
invariants.  White-Whiteley 1987's pure condition is a RANK certificate: by
its Cor. 2.7 it detects exactly k-isostaticity, which for the limit carrier is
(W1) & (W2).  The class-uniform escape needs (W1)-(W4), and (W4) -- the
reciprocal twist's pitch Q(z) != 0 -- is not a rank condition at all: it asks
whether a distinguished kernel vector is off the KLEIN QUADRIC.  At every
uncovered flank of section (K-slide-comb) Step D5 the rank half is FINE and it
is (W4) (or, once, (W2)) that fails identically.  So a non-vanishing theorem
for the pure condition, however un-specialized, would not settle the escape.

The driver's five modes, each testing one headline sentence:

  --chord    (PC1)/(PC2)/(PC3): a PROVEN obstruction theorem.  For every G*
             edge whose limit chain has all its lines meeting the chord
             pt(u) ^ pt(w) -- exactly the ell <= 2 edges, the ell = 3 edges
             with at least one end slid, and the ell = 4 edges with both ends
             slid -- the chord itself is a legal "bar" of the limit system
             (chord in R_P^B = S_P^{perp B}).  Chord bars in equilibrium are
             precisely a PROJECTIVE BAR-AND-JOINT SELF-STRESS of the hub-point
             framework of those edges.  If such a stress exists using e0 = bc,
             then V_bc is inside C_bc^{perp B}; since <C_ab, C_ac, C_bc> is the
             (totally isotropic) Lambda^2 of plane(a,b,c), z then lies in that
             plane's Lambda^2 and Q(z) = 0 -- at EVERY decoration.  Ends with a
             CENSUS: exhaustively over the 23 candidate hub graphs with
             |V*| <= 6, the full-support obstruction can bite only at the
             Maxwell-overbraced ones (|E*| >= 3|V*| - 5), the smallest being K5.
  --flanks   full-support (W1)-(W4) verdicts at the three structural flanks of
             section (K-slide-comb), all five exhibited K5 shapes, menu-blocked
             K4 shapes, and the pitched controls.  The chord predictor of
             --chord is asserted against each verdict.
  --support  the slide support is a free parameter ((S1) remark (iii)).  A
             support that drops enough edges out of the chord-obstructed set
             RESCUES flanks the full support loses -- exhibited at the K5
             5-chromatic flank (the gap map's hardest uncovered shape).
  --pure     the invariant mismatch, measured: shapes where (W1) & (W2) hold at
             every sampled decoration (so the pure condition is NOT identically
             zero) yet Q(z) = 0 at every one; plus the free-bar contrast that
             shows WW87 Thm 2.18 cannot transfer to the decoration variety.
  --parallel the parallel-G*-edge row of the gap map, corrected: at
             theta(3,4,5) (W1) and (W2) HOLD -- the order-0 obstruction there
             is (W4) via --chord, not the (S5) row dependence, which is a
             separate mechanism firing only at short parallel pairs; and inside
             the tight + hnoRigid class every parallel pair has
             ell_1 + ell_2 >= 7, because a shorter one is a rigid C_k, k <= 6.

Conventions (notes/scripts/README.md section 4): exact Q throughout
(`fractions.Fraction`, no floating point); every sampled object carries a
rank/dimension assert; all randomness is seeded from printed literals; run with
PYTHONHASHSEED=0 when comparing runs.  Decorations are NOT hand-rolled: every
limit system here is built by `kslide.path_limit_lines` from an honest pencil
chart seed produced by `repin.seed_probe`, which is what (S1) consumes -- a
hand-sampled "generic decoration" need not be chart-realizable and would not
transfer.

Reproduce (from the repo root, one at a time; times measured 2026-08-05 on one
machine and INDICATIVE only -- the |V| = 31/36 shapes cost ~4 s per chart seed):
    PYTHONHASHSEED=0 python3 notes/scripts/w4/pure.py --chord      # ~5 min
    PYTHONHASHSEED=0 python3 notes/scripts/w4/pure.py --flanks     # ~11 min
    PYTHONHASHSEED=0 python3 notes/scripts/w4/pure.py --support    # ~13 min
    PYTHONHASHSEED=0 python3 notes/scripts/w4/pure.py --pure       # ~4 min
    PYTHONHASHSEED=0 python3 notes/scripts/w4/pure.py --parallel   # ~1 min
"""
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, dot, perp_basis
from pencil_escape import nullspace, wedge2, hat
from kbare_common import verts_of
from nogood_subdiv import deficiency
from repin import seed_probe, span_basis, in_span, lambda2_through, hodge_star
from pitch import Q, klein, rows_from_lines, transfer_probe, z_from
from kslide import member, build_smap, path_limit_lines, no_rigid_branch_union
from kslidecomb import (shape_ok, k5_specs, K5_LENS, FLANKS, relabel,
                        packing_minmax, search_unrestricted)

RNG_SEED = 20260805          # the only literal randomness seed in this file


# ---------------- the limit carrier at one chart seed -------------------------

def limit_data(edges, pmap, v, seed, split_k=0, omit=()):
    """The slide-in limit carrier at one honest pencil-chart seed, with the
    full (W1)-(W4) diagnosis and the chord bookkeeping.

    `omit` = interiors dropped from the slide support (the support is free,
    (S1)(iii)).  Returns None at an invalid / non-target-rank seed.  Nothing
    is asserted about (W1)-(W4) here -- the point of the mode drivers is to
    RECORD which of them fails -- but every sampled object's dimension is.
    """
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra, Cab0, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    smap = build_smap(pmap, split_k)
    for x in omit:
        smap.pop(x, None)
    Hed = [e for e in edges if v not in e and a not in e]
    Cmap, chains, chain_vs = {}, {}, {}
    for k, vs in pmap.items():
        if k == split_k:
            continue
        Ls = path_limit_lines(vs, placed, pt, smap)
        chains[k] = (vs[0], vs[-1], Ls)
        chain_vs[k] = list(vs)
        for i in range(len(vs) - 1):
            Cmap[(vs[i], vs[i + 1])] = Ls[i]
    assert set(Cmap) == set(Hed), "H edge cover mismatch"
    VH = sorted(verts_of(Hed), key=str)
    rows, idx = rows_from_lines(Hed, Cmap, VH)
    mot = nullspace(rows)
    tgt = 6 * len(VH) - 5 * len(Hed)
    ib, ic = 6 * idx[b], 6 * idx[c]
    V = span_basis([[m[ib + k] - m[ic + k] for k in range(6)] for m in mot])
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    Cab, Cac, Cbc = wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)
    for nm, L in (('C_ab', Cab), ('C_ac', Cac), ('C_bc', Cbc)):
        assert any(x != 0 for x in L), f"degenerate {nm}"
    # Lambda^2 of plane(a, b, c): 3-dimensional and TOTALLY ISOTROPIC.
    tri = span_basis([Cab, Cac, Cbc])
    assert len(tri) == 3, f"a, b, c collinear at seed {seed} (dim = {len(tri)})"
    assert all(klein(x, y) == 0 for x in tri for y in tri), \
        "Lambda^2(plane abc) not isotropic -- Klein convention broken"
    d = {'seed': seed, 'mot': len(mot), 'tgt mot': tgt, 'dim V_bc': len(V),
         'W1': len(mot) == tgt, 'W2': len(V) == 3,
         'V_bc perp C_bc': all(klein(m, Cbc) == 0 for m in V),
         '_pt': pt, '_placed': placed, '_abc': (a, b, c), '_nrm': nrm,
         '_lines': (Cab, Cac, Cbc, tri), '_chains': chains,
         '_chain_vs': chain_vs,
         '_sys': (Hed, Cmap, VH, rows, idx), '_V': V, '_smap': smap}
    Ac = span_basis(lambda2_through(ch))
    Ab = span_basis(lambda2_through(bh))
    assert len(Ac) == 3 and len(Ab) == 3, "alpha-space not 3-dimensional"
    d['V_bc = alpha(c)'] = len(V) == 3 and all(in_span(x, Ac) for x in V)
    d['V_bc = alpha(b)'] = len(V) == 3 and all(in_span(x, Ab) for x in V)
    d['C_bc in V_bc'] = len(V) > 0 and in_span(Cbc, V)
    # (PC-Z): T = <C_ab, C_ac> sits in exactly two maximal isotropic 3-spaces,
    # Lambda^2(plane abc) = tri and alpha(pt a); z spans V_bc cap T^{perp B},
    # and both isotropic spaces lie in T^{perp B}.  So (W4) holds iff V_bc
    # misses BOTH of them.  Asserted below against the computed Q(z).
    Aa = span_basis(lambda2_through(ah))
    assert len(Aa) == 3, "alpha(pt a) not 3-dimensional"
    assert all(in_span(x, tri) for x in span_basis([Cab, Cac])), "T not in tri"
    assert all(in_span(x, Aa) for x in span_basis([Cab, Cac])), "T not in alpha(a)"
    if len(V) == 3:
        d['dim V_bc cap Lambda2(abc)'] = 6 - rank(V + tri)
        d['dim V_bc cap alpha(a)'] = 6 - rank(V + Aa)
        z, co = z_from(V, Cab, Cac)
        d['W3'] = z is not None
        if z is not None:
            d['Q(z)'] = Q(z)
            d['W4'] = Q(z) != 0
            d['z in Lambda2(abc)'] = in_span(z, tri)
            d['z in alpha(a)'] = in_span(z, Aa)
            assert d['z in Lambda2(abc)'] == (d['dim V_bc cap Lambda2(abc)'] > 0)
            assert d['z in alpha(a)'] == (d['dim V_bc cap alpha(a)'] > 0)
            assert (Q(z) == 0) == (d['z in Lambda2(abc)']
                                  or d['z in alpha(a)']), \
                "(PC-Z) reformulation of (W4) FAILS at this seed"
            # pencil(pt c; plane abc) = alpha(c) cap T^{perp B}, 2-dimensional
            pen = span_basis([Cac, Cbc])
            assert len(pen) == 2, "pencil(pt c; plane abc) not 2-dimensional"
            d['z in pencil(c; abc)'] = in_span(z, pen)
    return d


def verdict(d):
    """A one-token verdict string for a limit_data dict."""
    if not d['W1']:
        return f"W1 FAILS (mot = {d['mot']} > {d['tgt mot']})"
    if not d['W2']:
        return f"W2 FAILS (dim V_bc = {d['dim V_bc']})"
    if not d['W3']:
        return "W3 FAILS (z undefined)"
    return "PITCHED (W1-W4)" if d['W4'] else "W4 FAILS (Q(z) = 0)"


# ---------------- (PC1)-(PC3): the chord obstruction --------------------------

def chord_set(d):
    """The G*-edges whose limit chain lines ALL meet the chord pt(u) ^ pt(w),
    i.e. those P with chord in R_P^B = S_P^{perp B}.  Measured, not inferred
    from the length/support rule -- the rule is asserted separately."""
    pt = d['_pt']
    out = {}
    for k, (u, w, Ls) in d['_chains'].items():
        S = span_basis(Ls)
        assert len(S) == len(Ls), \
            f"chain lines of G*-edge {u}-{w} dependent (dim {len(S)} of {len(Ls)})"
        chord = wedge2(hat(pt[u]), hat(pt[w]))
        assert any(x != 0 for x in chord), f"zero chord at {u}-{w}"
        out[k] = (u, w, len(Ls), all(klein(chord, s) == 0 for s in S), chord)
    return out


def chord_rule(d, pmap, split_k=0):
    """(PC1) as a combinatorial rule: chord in R_P^B iff ell <= 2, or ell = 3
    with >= 1 end slid, or ell = 4 with both ends slid.  ell = 5 never."""
    smap = d['_smap']
    pred = {}
    for k, vs in pmap.items():
        if k == split_k:
            continue
        L = len(vs) - 1
        slid_u, slid_w = vs[1] in smap, vs[-2] in smap
        if L <= 2:
            pred[k] = True
        elif L == 3:
            pred[k] = slid_u or slid_w
        elif L == 4:
            pred[k] = slid_u and slid_w
        else:
            pred[k] = False
    return pred


def chord_stress(d, cs):
    """The chord-bar system: solve for lambda on the chord-obstructed G*-edges
    PLUS the split edge e0 = bc, with equilibrium `sum_{P at h} lambda_P
    (h^ ^ other^) = 0` at every hub.  This is exactly the PROJECTIVE
    bar-and-joint self-stress space of the hub-point framework on those edges
    together with bc (`h^ ^ (sum lambda_P other^) = 0` iff the weighted sum of
    the neighbours is a multiple of h itself).

    Multigraph-safe: edges are indexed by position, never by their end pair.
    Returns (dim of the stress space, [(chain key, u, w, lambda)] for the
    chord-obstructed edges or None, lambda_{e0})."""
    pt, (a, b, c) = d['_pt'], d['_abc']
    obs = [(k, cs[k][0], cs[k][1]) for k in sorted(cs) if cs[k][3]]
    ed = [(u, w) for (_k, u, w) in obs] + [(b, c)]     # e0 = the extra bar
    hubset = sorted({x for e in ed for x in e}, key=str)
    ncol = len(ed)
    rows = []
    for h in hubset:
        blk = [[F(0)] * ncol for _ in range(6)]
        for j, (u, w) in enumerate(ed):
            if h == u:
                L = wedge2(hat(pt[u]), hat(pt[w]))
            elif h == w:
                L = wedge2(hat(pt[w]), hat(pt[u]))
            else:
                continue
            for t in range(6):
                blk[t][j] += L[t]
        rows.extend(blk)
    ker = nullspace(rows)
    pick = next((y for y in ker if y[ncol - 1] != 0), None)
    if pick is None:
        return len(ker), None, None
    lam = [(k, u, w, pick[j]) for j, (k, u, w) in enumerate(obs)]
    return len(ker), lam, pick[ncol - 1]


def bar_stress_dim(pts, edges):
    """The dimension of the PROJECTIVE bar-and-joint self-stress space of the
    framework `(edges, pts)` in 3-space: the lambda with
    `sum_{P at h} lambda_P (h^ ^ o^) = 0` at every vertex, which by (PC2) is
    `sum_{P at h} lambda_P (o_P - h) = 0` affinely.  Multigraph-safe (edges are
    indexed by position)."""
    hubset = sorted({x for e in edges for x in e}, key=str)
    ncol = len(edges)
    rows = []
    for h in hubset:
        blk = [[F(0)] * ncol for _ in range(6)]
        for j, (u, w) in enumerate(edges):
            if h == u:
                L = wedge2(hat(pts[u]), hat(pts[w]))
            elif h == w:
                L = wedge2(hat(pts[w]), hat(pts[u]))
            else:
                continue
            assert any(t != 0 for t in L), f"coincident points on bar {u}-{w}"
            for t in range(6):
                blk[t][j] += L[t]
        rows.extend(blk)
    return len(nullspace(rows))


def verify_chord_stress(d, cs, lam, e0lam):
    """Assemble the chord stress as an explicit ROW COMBINATION of the limit
    system's actual rows and assert that its covector is a nonzero multiple of
    `m |-> B(m(b) - m(c), C_bc)`; hence V_bc is inside C_bc^{perp B}, hence (by
    (PC3)) z is in the isotropic Lambda^2(plane abc) and Q(z) = 0.

    Convention care: the limit rows pair EUCLIDEANLY with the twists
    (`rows_from_lines` uses `perp_basis`), so the legal per-edge coefficient
    space is `S_P^{perp Eucl} = star(S_P^{perp B})`; the chord contributes
    `star(chord)`.  Equilibrium is unchanged (star is invertible and linear)."""
    Hed, Cmap, VH, rows, idx = d['_sys']
    pt, (a, b, c) = d['_pt'], d['_abc']
    Cab, Cac, Cbc, tri = d['_lines']
    cov = [F(0)] * (6 * len(VH))
    for (k, u, w, lv) in lam:
        if lv == 0:
            continue
        y = hodge_star(wedge2(hat(pt[u]), hat(pt[w])))
        assert any(t != 0 for t in y), "zero starred chord"
        vs = d['_chains'][k][2]
        chain = d['_chain_vs'][k]
        assert len(chain) - 1 == len(vs), "chain / line count mismatch"
        for i in range(len(chain) - 1):
            e = (chain[i], chain[i + 1])
            assert dot(y, Cmap[e]) == 0, \
                "starred chord is not a legal row coefficient on this chain"
            assert len(perp_basis(Cmap[e])) == 5, "hinge perp not 5-dimensional"
            for t in range(6):
                cov[6 * idx[chain[i]] + t] += lv * y[t]
                cov[6 * idx[chain[i + 1]] + t] -= lv * y[t]
    # the residual covector must be a nonzero multiple of the b-vs-c pairing
    # against star(C_bc)
    tgt = [F(0)] * (6 * len(VH))
    sc = hodge_star(Cbc)
    for t in range(6):
        tgt[6 * idx[b] + t] += sc[t]
        tgt[6 * idx[c] + t] -= sc[t]
    nz = next((j for j in range(len(tgt)) if tgt[j] != 0), None)
    assert nz is not None
    mu = cov[nz] / tgt[nz]
    assert mu != 0, "chord stress produced a zero b-vs-c load"
    assert cov == [mu * x for x in tgt], \
        "chord-stress covector is not a multiple of the C_bc load"
    assert all(klein(m, Cbc) == 0 for m in d['_V']), \
        "chord stress exists but V_bc is not inside C_bc^{perp B}"
    if d['W1'] and d['W2'] and d.get('W3'):
        assert d['z in Lambda2(abc)'], "z not in Lambda^2(plane abc)"
        assert d['Q(z)'] == 0, "z in an isotropic 3-space yet Q(z) != 0"
    return True


# ---------------- the shape pool ----------------------------------------------

def theta345():
    return [(0, 1, 3), (0, 1, 4), (0, 1, 5)]


def p21():
    """The (K-res)-shaped parallel member of section (K-slide) (S5): G* =
    K4 - 02 with 23 doubled, lengths (3; 3,3; 4,5,3,3).  Its parallel pair is
    a rigid C6, so it is NOT hnoRigid -- a (K-res) residual, not a tight class
    member."""
    return [(0, 1, 3), (2, 3, 3), (2, 3, 3), (0, 2, 4), (0, 3, 5),
            (1, 2, 3), (1, 3, 3)]


def dbl_k4():
    return [(0, 1, 3), (0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3), (2, 3, 3)]


def k4_mixed():
    return [(0, 1, 3), (2, 3, 4), (0, 2, 2), (0, 3, 3), (1, 2, 3), (1, 3, 3)]


def flank_specs(i):
    name, edges, lens, k = FLANKS[i]
    n = len({x for e in edges for x in e})
    return name, relabel(n, edges, lens, k)


def menu_blocked_k4(count=3):
    """A few of the 438 exhaustive K4 shapes whose collapse assignment problem
    is menu-blocked although the colouring premise holds (section
    (K-slide-comb) verdict (iv)).  Chosen deterministically: the first `count`
    in lexicographic length order that are class shapes with a length >= 4."""
    import itertools
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    out = []
    for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
        if sum(lens) != 18 or 3 not in lens or max(lens) < 4:
            continue
        k = lens.index(3)
        specs = relabel(4, K4, lens, k)
        if shape_ok(specs) is None:
            continue
        out.append((f"K4 lens {lens}", specs))
        if len(out) >= count:
            break
    return out


def certify(name, specs, need_hnorigid=True):
    """Class membership exactly as the (K-slide) battery certifies it."""
    edges, pmap = member(specs)
    nV = len(verts_of(edges))
    assert 5 * len(edges) == 6 * (nV - 1), f"{name}: not tight-count"
    assert deficiency(edges) == 0, f"{name}: def != 0"
    hn = no_rigid_branch_union(edges, pmap)
    if need_hnorigid:
        assert hn, f"{name}: hnoRigid fails"
    return edges, pmap, nV, hn


# ---------------- mode: --chord -----------------------------------------------

def mode_chord():
    print("== (PC1)/(PC2)/(PC3): the chord obstruction, a proven theorem ==")
    print("   (PC1) chord(u,w) in R_P^B  <=>  ell <= 2, or ell = 3 with >= 1")
    print("         end slid, or ell = 4 with both ends slid; never ell = 5.")
    print("   (PC2) chord bars in equilibrium = a projective bar-and-joint")
    print("         self-stress of the hub-point framework; one using e0")
    print("         forces V_bc inside C_bc^{perp B}.")
    print("   (PC3) <C_ab, C_ac, C_bc> = Lambda^2(plane abc) is 3-dim and")
    print("         totally isotropic, so z lands in it and Q(z) = 0.\n")
    cases = [('theta(3,4,5)', theta345(), True),
             ('K5 flank ' + str(K5_LENS[0]), k5_specs(K5_LENS[0]), True),
             ('K5 flank ' + str(K5_LENS[1]), k5_specs(K5_LENS[1]), True),
             ('K5 pitched ' + str(K5_LENS[3]), k5_specs(K5_LENS[3]), True),
             ('dbl-subdiv K4 (control)', dbl_k4(), True),
             (flank_specs(2)[0][:34], flank_specs(2)[1], True)]
    nrule = nchord = 0
    for (name, specs, hn) in cases:
        edges, pmap, nV, hnr = certify(name, specs, hn)
        print(f"-- {name}: |V| = {nV}, def = 0, hnoRigid = {hnr}")
        got = 0
        for seed in range(101, 121):
            d = limit_data(edges, pmap, pmap[0][1], seed)
            if d is None:
                continue
            cs = chord_set(d)
            pred = chord_rule(d, pmap)
            for k in cs:
                assert cs[k][3] == pred[k], \
                    f"{name}: (PC1) rule wrong at G*-edge {cs[k][0]}-{cs[k][1]}"
                nrule += 1
            nstr, lam, e0lam = chord_stress(d, cs)
            obs = [f"{cs[k][0]}-{cs[k][1]}(l{cs[k][2]})"
                   for k in sorted(cs) if cs[k][3]]
            print(f"   seed {seed}: chord-obstructed edges "
                  f"[{', '.join(obs)}]; chord-stress space dim {nstr}; "
                  f"uses e0: {lam is not None}")
            print(f"      V_bc perp C_bc: {d['V_bc perp C_bc']}"
                  f"   ->  {verdict(d)}")
            if lam is not None:
                verify_chord_stress(d, cs, lam, e0lam)
                nchord += 1
                assert d['V_bc perp C_bc']
                assert not d.get('W4', False), \
                    "chord stress present yet (W4) holds"
            else:
                assert not d['V_bc perp C_bc'] or not d['W1'], \
                    "V_bc perp C_bc with no chord stress -- (PC2) incomplete"
            got += 1
            if got >= 2:
                break
        assert got >= 1, f"{name}: no valid seed"
    print(f"\n  (PC1) rule verified on {nrule} G*-edge instances; (PC2)+(PC3)")
    print(f"  certified end-to-end at {nchord} chord-stressed decorations.\n")
    chord_census()
    print("CHORD OK")


def chord_census():
    """Where the FULL-support chord obstruction can bite, exhaustively over the
    23 candidate hub graphs with |V*| <= 6 (simple, connected, min degree >= 3
    -- `kslidecomb.candidate_graphs`).  At the full support and all lengths
    <= 4 the chord-obstructed set is all of E(G*) minus e0, so the obstruction
    needs G* itself to be R_3-DEPENDENT.  Claim tested: among these, dependence
    holds exactly for |E*| >= 3|V*| - 5, i.e. exactly the Maxwell-overbraced
    ones -- and the first such simple hub graph is G* = K5."""
    from kslidecomb import candidate_graphs
    from kbare_common import rvec3
    print("  -- census: which hub graphs can be chord-obstructed at all? --")
    print(f"     hub points drawn from random.Random({RNG_SEED}) "
          f"(kbare_common.rvec3, exact Q)")
    rng = random.Random(RNG_SEED)
    dep, indep = [], []
    for n, edges in candidate_graphs(6):
        pts = {v: rvec3(rng) for v in range(n)}
        # degeneracy guard: the point set must affinely span 3-space
        aff = [[pts[v][t] - pts[0][t] for t in range(3)] for v in range(1, n)]
        assert rank(aff) == 3, "sampled hub points are not 3-spanning"
        sd = bar_stress_dim(pts, edges)
        maxwell = len(edges) > 3 * n - 6
        assert (sd > 0) == maxwell, \
            (f"|V*|={n} |E*|={len(edges)}: stress dim {sd} but Maxwell "
             f"overbraced = {maxwell}")
        (dep if sd > 0 else indep).append((n, len(edges), sd))
    print(f"     {len(dep) + len(indep)} candidate hub graphs; "
          f"{len(dep)} R_3-DEPENDENT, {len(indep)} independent")
    for (n, m, sd) in dep:
        print(f"       |V*|={n} |E*|={m}: stress dim {sd}   "
              f"(3|V*|-6 = {3 * n - 6})")
    print("     => at |V*| <= 6, simple G* with every length <= 4, the")
    print("        full-support chord obstruction can only bite at these; the")
    print("        smallest is K5 (|E*| = 10 > 9), which is exactly the")
    print("        5-chromatic flank Brooks characterises.  K222 (12 = 3n-6)")
    print("        and the 6v11e flank (11) are NOT chord-obstructed -- their")
    print("        (W4)/(W2) failures are a different, open mechanism.")


# ---------------- mode: --flanks ----------------------------------------------

def mode_flanks():
    print("== full-support (W1)-(W4) at the (K-slide-comb) Step-D5 flanks ==")
    print("   every shape is re-certified (tight count, def = 0, hnoRigid);")
    print("   the chord predictor of --chord is asserted against each verdict.")
    cases = [('CONTROL dbl-subdiv K4', dbl_k4()),
             ('CONTROL K4 mixed (3,4,2,3,3,3)', k4_mixed())]
    cases += [(f'K5 5-chromatic flank {lens}', k5_specs(lens))
              for lens in K5_LENS]
    cases += [(flank_specs(1)[0][:40], flank_specs(1)[1]),
              (flank_specs(2)[0][:40], flank_specs(2)[1])]
    cases += menu_blocked_k4(3)
    cases += [('theta(3,4,5) (parallel G*)', theta345())]
    summary = []
    for (name, specs) in cases:
        edges, pmap, nV, hnr = certify(name, specs)
        assert hnr
        tally, chordflag, extra = {}, set(), set()
        for seed in range(101, 112):
            d = limit_data(edges, pmap, pmap[0][1], seed)
            if d is None:
                continue
            cs = chord_set(d)
            nstr, lam, e0lam = chord_stress(d, cs)
            chordflag.add(lam is not None)
            if lam is not None:
                verify_chord_stress(d, cs, lam, e0lam)
            if d['C_bc in V_bc']:
                extra.add('C_bc itself in V_bc')
            if d.get('z in Lambda2(abc)'):
                extra.add('V_bc meets Lambda2(plane abc)')
            if d.get('z in alpha(a)'):
                extra.add('V_bc meets alpha(pt a)')
            vd = verdict(d)
            tally[vd] = tally.get(vd, 0) + 1
        assert tally, f"{name}: no valid seed"
        line = '; '.join(f"{k} x{n}" for k, n in sorted(tally.items()))
        cf = ('yes' if chordflag == {True} else
              'no' if chordflag == {False} else 'mixed')
        print(f"  {name}: |V| = {nV}  chord-stress: {cf}"
              + (f"   [{'; '.join(sorted(extra))}]" if extra else ""))
        print(f"      {line}")
        summary.append((name, cf, sorted(tally)))
    print("\n  Reading: every 'W4 FAILS' / 'W3 FAILS' row with chord-stress")
    print("  'yes' is EXPLAINED and PROVEN identical by (PC2)+(PC3).  The rows")
    print("  with chord-stress 'no' that still fail (W4)/(W2) are a SECOND,")
    print("  unidentified mechanism -- an honest residual gap of this pass.")
    for (name, cf, vs) in summary:
        if cf == 'no' and any('FAIL' in v for v in vs):
            print(f"      residual-mechanism shape: {name}  {vs}")
    print("FLANKS OK")


# ---------------- mode: --support ---------------------------------------------

def hub_side_interiors(pmap, hub, split_k=0):
    """The slid interiors adjacent to `hub` (the ends of its length >= 3
    paths) -- the natural knob for shrinking the slide support at one hub."""
    out = []
    for k, vs in pmap.items():
        if k == split_k or len(vs) - 1 < 3:
            continue
        if vs[0] == hub:
            out.append(vs[1])
        if vs[-1] == hub:
            out.append(vs[-2])
    return tuple(out)


def all_slid(pmap, split_k=0):
    return tuple(build_smap(pmap, split_k).keys())


def mode_support():
    print("== the slide support is the lever ((S1) remark (iii)) ==")
    print("   support menu tried, in order: full; drop the slide at c; at b; at")
    print("   both; and (the far extreme) no slide anywhere -- which IS the")
    print("   eps = 1 chart, where the chord-obstructed set is only the ell <= 2")
    print("   edges.  A support whose chord-obstructed set no longer spans e0")
    print("   escapes (PC2), and then (W1)-(W4) can hold.")
    print("   RESCUE CRITERION: >= 1 seed with (W1)-(W4) -- that is exactly what")
    print("   (S1) consumes (ONE exact limit witness), not a majority.\n")
    cases = [('K5 5-chromatic flank ' + str(K5_LENS[0]), k5_specs(K5_LENS[0])),
             ('K5 flank ' + str(K5_LENS[1]), k5_specs(K5_LENS[1])),
             ('K5 flank ' + str(K5_LENS[2]), k5_specs(K5_LENS[2])),
             (flank_specs(1)[0][:40], flank_specs(1)[1]),
             (flank_specs(2)[0][:40], flank_specs(2)[1]),
             ('theta(3,4,5)', theta345())]
    rescued, stuck = [], []
    for (name, specs) in cases:
        edges, pmap, nV, hnr = certify(name, specs)
        b, c = pmap[0][0], pmap[0][-1]
        menu = [('full support', ()),
                ('no slide at c', hub_side_interiors(pmap, c)),
                ('no slide at b', hub_side_interiors(pmap, b)),
                ('no slide at b or c',
                 hub_side_interiors(pmap, b) + hub_side_interiors(pmap, c)),
                ('CHART (no slide anywhere; (S1) is VACUOUS here)',
                 all_slid(pmap))]
        print(f"-- {name}: |V| = {nV}")
        won = None
        for (mname, omit) in menu:
            got, tally, cf, pitched = 0, {}, set(), 0
            for seed in range(101, 112):
                d = limit_data(edges, pmap, pmap[0][1], seed, omit=omit)
                if d is None:
                    continue
                cs = chord_set(d)
                nstr, lam, e0lam = chord_stress(d, cs)
                cf.add(lam is not None)
                if lam is not None:
                    verify_chord_stress(d, cs, lam, e0lam)
                vd = verdict(d)
                tally[vd] = tally.get(vd, 0) + 1
                pitched += 1 if 'PITCHED' in vd else 0
                got += 1
                if got >= 3:
                    break
            if not got:
                print(f"   {mname}: no valid seed")
                continue
            line = '; '.join(f"{k} x{n}" for k, n in sorted(tally.items()))
            print(f"   {mname} (|omit| = {len(omit)}): chord-stress "
                  f"{'yes' if cf == {True} else 'no' if cf == {False} else 'mixed'}"
                  f"  ->  {line}")
            if won is None and pitched >= 1:
                won = (mname, pitched, got)
        if won and not won[0].startswith('CHART'):
            print(f"   => RESCUED by '{won[0]}': {won[1]}/{won[2]} sampled seeds")
            print("      give a full (W1)-(W4) witness, and (S1) needs ONE, so")
            print("      the SLIDE DEVICE closes this split at this shape.")
            rescued.append((name, won[0]))
        else:
            if won:
                print("   => the slide device FAILS at every probed nonempty")
                print(f"      support; only the CHART (Sigma = empty) is pitched"
                      f" ({won[1]}/{won[2]} seeds), and there (S1) is VACUOUS.")
                stuck.append(name + '  [chart only]')
            else:
                print("   => NOT pitched anywhere in this 5-support menu.")
                stuck.append(name)
            print("      Chart transfer certificate ((T1)-(T3) + Q(r) != 0,")
            print("      which is what the (K-pitch) Step-0 one-witness")
            print("      argument consumes -- it also checks dim R_a = 1 and")
            print("      the (T2) side conditions, which (W1)-(W4) do not):")
            ok = 0
            for seed in range(101, 112):
                o = transfer_probe(edges, pmap[0][1], seed)
                if o is None or 'skip' in o:
                    continue
                good = (o['T1'] is True and o['T2'] is True
                        and o.get('T3') is True and o['Q(r)'] != 0)
                print(f"        transfer seed {seed}: T1={o['T1']} T2={o['T2']} "
                      f"T3={o.get('T3', '-')} Q(r)!=0: {o['Q(r)'] != 0}")
                if good:
                    ok += 1
                    break
            print(f"        => {ok} full certificate(s); with ok >= 1 the SPLIT")
            print("           closes by Step-0 logic even though the slide")
            print("           device does not reach this shape.")
    print(f"\n  slide device rescued by a reduced (nonempty) support: "
          f"{len(rescued)} of {len(cases)} shapes")
    for (n, w) in rescued:
        print(f"      {n}  <- {w}")
    if stuck:
        print("  slide device NOT rescued at any probed nonempty support:")
        for n in stuck:
            print(f"      {n}")
    print("SUPPORT OK")


# ---------------- mode: --pure ------------------------------------------------

def free_bar_control(specs, rng, split_k=0):
    """The FREE-bar contrast for WW87 Thm 2.18: keep the multiplicity
    structure of the limit carrier (G*-edge P carries 6 - ell_P rows) but draw
    the row screws GENERICALLY instead of from R_P.  Thm 2.18 predicts
    independence exactly when the 6-fold base packing exists -- (C6) says it
    always does on the class.  Returns (rows wanted, rank achieved)."""
    hubs = sorted({h for (h1, h2, _L) in specs for h in (h1, h2)})
    hi = {h: k for k, h in enumerate(hubs)}
    ncol = 6 * len(hubs)
    rows = []
    for i, (h1, h2, L) in enumerate(specs):
        if i == split_k:
            continue
        for _ in range(6 - L):
            y = [F(rng.randint(-40, 40)) for _ in range(6)]
            while all(t == 0 for t in y):
                y = [F(rng.randint(-40, 40)) for _ in range(6)]
            row = [F(0)] * ncol
            for t in range(6):
                row[6 * hi[h1] + t] += y[t]
                row[6 * hi[h2] + t] -= y[t]
            rows.append(row)
    return len(rows), rank(rows)


def mode_pure():
    print("== the invariant mismatch: the pure condition is the wrong test ==")
    print("   WW87 Prop. 2.6 / Cor. 2.7: the pure condition is a RANK")
    print("   certificate -- nonzero at a realization iff k-isostatic.  For")
    print("   the limit carrier that is exactly (W1) & (W2).  The escape needs")
    print("   (W4) too, and (W4) asks whether one kernel vector is OFF the")
    print("   Klein quadric.  Below: class shapes where the rank half holds at")
    print("   every sampled decoration -- so the pure condition is NOT")
    print("   identically zero on the decoration variety -- and (W4) fails at")
    print("   every one of them.\n")
    cases = [('theta(3,4,5)', theta345()),
             ('K5 5-chromatic flank ' + str(K5_LENS[1]), k5_specs(K5_LENS[1])),
             ('K5 5-chromatic flank ' + str(K5_LENS[2]), k5_specs(K5_LENS[2])),
             (flank_specs(2)[0][:34], flank_specs(2)[1])]
    for (name, specs) in cases:
        edges, pmap, nV, hnr = certify(name, specs)
        n12 = nq0 = tot = 0
        for seed in range(101, 115):
            d = limit_data(edges, pmap, pmap[0][1], seed)
            if d is None:
                continue
            tot += 1
            if d['W1'] and d['W2']:
                n12 += 1
                assert d.get('W3') is False or d.get('Q(z)') == 0, \
                    f"{name}: expected (W4) failure, got {verdict(d)}"
                nq0 += 1
        print(f"  {name}: |V| = {nV}, {tot} valid seeds; (W1) & (W2) hold at "
              f"{n12}/{tot}")
        print(f"      => pure condition NONZERO there; pitch Q(z) = 0 at "
              f"{nq0}/{n12} of those")
        assert n12 >= 1 and nq0 == n12
    print("\n  So a proof of 'the pure condition is not identically zero on the")
    print("  decoration variety' would leave the escape UNSETTLED at every one")
    print("  of these class shapes.  Direction C's target is insufficient.\n")
    print("== and Thm 2.18 cannot transfer anyway: free bars vs decoration ==")
    print("   the decoration variety is a PROPER subvariety of the body-bar")
    print("   realization space; Thm 2.18's 'packing => nonzero' is a")
    print("   statement about the generic point of the latter.")
    rng = random.Random(RNG_SEED)
    print(f"   (free-bar screws drawn from random.Random({RNG_SEED}))")
    for (name, specs, hn) in (('theta(3,4,5)', theta345(), True),
                              ('P21 (K-res, parallel (3,3))', p21(), False),
                              ('K5 flank ' + str(K5_LENS[0]),
                               k5_specs(K5_LENS[0]), True)):
        edges, pmap, nV, hnr = certify(name, specs, need_hnorigid=hn)
        ok, worst, _t = packing_minmax(specs)
        assert ok, f"{name}: (C6) min-max fails"
        assert search_unrestricted(specs) is not None, \
            f"{name}: (C6) explicit packing missing"
        want, got = free_bar_control(specs, rng)
        assert want == 6 * len({h for (h1, h2, _L) in specs
                                for h in (h1, h2)}) - 9, \
            f"{name}: row count {want} != 6n - 9"
        print(f"   {name}: hnoRigid = {hnr}; (C6) packing EXISTS "
              f"(min-max slack >= {worst}); free bars: rank {got}/{want} "
              f"{'INDEPENDENT' if got == want else 'DEPENDENT'}")
        assert got == want, f"{name}: free bars dependent -- (C6) violated?"
    print("   and at P21 the DECORATION-variety rows are dependent at every")
    print("   support ((S5), reproduced by `kslide.py --flanks`): same graph,")
    print("   same multiplicities, (C6) satisfied, yet the pure condition of")
    print("   the constrained family vanishes identically.  Thm 2.18's")
    print("   combinatorial criterion does NOT transfer.")
    print("PURE OK")


# ---------------- mode: --parallel --------------------------------------------

def mode_parallel():
    print("== the parallel-G*-edge row of the gap map, corrected ==")
    print("   (S5) proves a (W1) failure for two parallel LENGTH-3 chains (a")
    print("   6-hinge cycle repeating the chord).  That is not what happens at")
    print("   theta(3,4,5): there (W1) and (W2) HOLD and the obstruction is")
    print("   (W4), via the chord stress of --chord.\n")
    edges, pmap, nV, hnr = certify('theta(3,4,5)', theta345())
    print(f"  theta(3,4,5): |V| = {nV}, def = 0, hnoRigid = {hnr}, "
          f"G* = 2 hubs with 3 parallel edges")
    got = 0
    for seed in range(101, 118):
        d = limit_data(edges, pmap, pmap[0][1], seed)
        if d is None:
            continue
        cs = chord_set(d)
        nstr, lam, e0lam = chord_stress(d, cs)
        assert d['W1'], "theta(3,4,5): unexpected (W1) failure"
        assert d['W2'], "theta(3,4,5): unexpected (W2) failure"
        assert lam is not None, "theta(3,4,5): no chord stress"
        verify_chord_stress(d, cs, lam, e0lam)
        # the surviving parallel pair in G* - e0 is (4, 5): its chain spans
        # sum to all of Lambda^2, so there is NO cycle stress -- the (S5)
        # mechanism is absent, only the chord mechanism fires.
        Ss = [span_basis(Ls) for (_u, _w, Ls) in d['_chains'].values()]
        assert len(Ss) == 2
        tot = span_basis(Ss[0] + Ss[1])
        assert len(tot) == 6, f"parallel chain spans sum to {len(tot)} != 6"
        got += 1
        if got == 1:
            print(f"   seed {seed}: (W1) OK (mot = {d['mot']}), (W2) OK "
                  f"(dim V_bc = 3), chord stress dim {nstr} uses e0,")
            print(f"      V_bc perp C_bc = {d['V_bc perp C_bc']}, "
                  f"z in Lambda^2(abc) = {d['z in Lambda2(abc)']}, "
                  f"Q(z) = {d['Q(z)']}  ->  {verdict(d)}")
            print("      remaining parallel pair (4,5): chain spans sum to "
                  "dim 6, so NO (S5) cycle stress")
    assert got >= 5, "too few valid theta seeds"
    print(f"   {got}/{got} seeds: (W1) & (W2) hold, (W4) fails by chord stress")
    print("\n  And (S5)'s PROVEN mechanism -- two parallel LENGTH-3 chains,")
    print("  whose shared chord makes a 6-hinge cycle of line rank 5 -- cannot")
    print("  occur inside the tight + hnoRigid class at all: a parallel pair of")
    print("  lengths (l1, l2) is a cycle C_{l1+l2} of G, and C_k is rigid for")
    print("  k <= 6 (R3), hence a proper rigid subgraph -- so hnoRigid forces")
    print("  l1 + l2 >= 7, and (3,3) is out.")
    for k in range(3, 9):
        cyc = [(i, (i + 1) % k) for i in range(k)]
        dk = deficiency(cyc)
        print(f"      C_{k}: def = {dk}  ({'RIGID' if dk == 0 else 'flexible'})")
        assert (dk == 0) == (k <= 6), f"C_{k} rigidity != (k <= 6)"
    print("      => the (3,3) pair of P21 makes it a rigid C6, i.e. a (K-res)")
    print("         residual, NOT a tight hnoRigid class member.")
    print("PARALLEL OK")


def main():
    if '--chord' in sys.argv:
        mode_chord()
    elif '--flanks' in sys.argv:
        mode_flanks()
    elif '--support' in sys.argv:
        mode_support()
    elif '--pure' in sys.argv:
        mode_pure()
    elif '--parallel' in sys.argv:
        mode_parallel()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
