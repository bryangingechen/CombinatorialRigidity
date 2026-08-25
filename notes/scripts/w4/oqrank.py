"""
Phase 39, section (K-out) CONTINUATION (direction OQRANK, ordinal 32) --
(a_1)'s one-determinant residue `rank(Q|_D) = 3` ((OC-33), *Step O29*)
attacked at sigma-fixed GRID points via the QQ(i) star-eigen-block leg that
*Step O29*'s own route paragraph names and could not run (its harness was
QQ-only; exact QQ(i) `exactcore.Gauss` is base-layer since 2026-08-20).

WHAT THE DRIVER TESTS, sentence by sentence (dispatch-log F11).

  (OC-40) THE FORCED (1,2) SPLIT.  At a sigma-fixed grid configuration the
    relative twist space `D = {m(b) - m(c) : m in Mot(H)}` is
    star-invariant (section (K-clos) (AC-2)/(AC-4)'s decoupling applied to
    `Mot(H)`), so `D = D_X (+) D_Y` inside the two star-eigenspaces
    (section (K-frame) (FR-2)(iii)), the blocks B-orthogonal with
    `B|_D = <.,.>|_{D_X} (+) (-<.,.>|_{D_Y})`.  At a TARGET-RANK grid chart
    point of the whole graph `G`, alternation at the degree-2 interiors
    forces `col(vb) = col(ac) =: X != col(va) =: Y`, the three hinge lines
    are ruling lines `C(vb) = A(s_b)`, `C(ac) = A(s_c)`, `C(va) = B(u_0)`,
    and (OC-31)(iii)'s direct sum `D (+) <C(ac), C(va), C(vb)> = K^6`
    splits per family into

        D_X (+) <A(s_b), A(s_c)> = W_X     and     D_Y (+) <B(u_0)> = W_Y,

    forcing `dim D_X = 1`, `dim D_Y = 2` -- and, for free, `s_b != s_c`,
    `u_b != u_c` (so (Lambda-0d) holds at every target-rank grid point) and
    `b !~ c` in the Y-forest of `H`.  ASSERTED per instance: isotropy,
    conjugacy, hcard, the (GR-5) closed-hub-neighbourhood LI hypothesis,
    target rank of the FULL QQ(i) matrix, sigma = 0, dim D = 3, star D = D,
    the (1,2) dims with the 1-dim block in family `col(vb)`, cross-block
    B-orthogonality, the direct sum, and (Lambda-0d).

  (OC-41) THE PER-BLOCK CRITERION.  With `g` spanning `D_X`:

        rank(Q|_D) = [Q(g) != 0] + rank(Gram_B(D_Y)),

    so `rank(Q|_D) = 3  <=>  Q(g) != 0  AND  det Gram_B(D_Y) != 0`.
    Geometric readings (the Veronese dictionary, (FR-2)): `Q(g) = 0` iff
    `g` IS a ruling line of family X; `Gram(D_Y)` singular iff `D_Y` is a
    TANGENT plane of the Y-conic, i.e. all its lines-at-infinity share a
    ruling-B "root".  ASSERTED per instance as the displayed equality
    (both sides computed independently), plus synthetic must-reject
    controls in `--controls` (a planted ruling and a planted conic
    generator, each driving rank(Q|_D) <= 2 through the SAME criterion).

  (OC-42) THE WALL.  A `b`-`c` path of `H` through Y-edges plus X-edges
    of a SINGLE class `i` confines every achievable X-flow value to
    `<A(s_i)>`, so at a target-rank grid point `D_X = <A(s_i)>`, on the
    conic: rank(Q|_D) = 2 at EVERY parameter draw of that colouring.
    ASSERTED per standing point: wall predicate ==> Q(g) = 0 and `g` on a
    component line; the Y-side predicate vacuous at target rank.

  (OC-43) THE CENSUS (a HUNT).  One representative per isomorphism class
    of section (K-out)'s length-4-companion population
    (`oschu.out_classes()`, the same 174-class key), at the SAME pinned
    (shape, split) as POOL-OC2.  Per class: hunt over the first <= 6
    filter-passing colourings carrying both-block tree-triples
    ((GR-9)/(GR-10)) x <= 4 seeded parameter draws each, for a standing
    target-rank grid point with rank(Q|_D) = 3; every standing point on
    the way runs every assertion above and records `rank(Q|_D)`, the wall
    predicate, dimK, the ruling test, and the SUPPORT diagnostics: is `g`
    proportional to a component ruling line of `H`'s X-forest (the
    structural danger case), inside the span of TWO of them (the secant
    case -- nondegenerate for EVERY parameter draw), or off both; and is
    `D_Y` the span of two component ruling lines of `H`'s Y-forest
    (secant plane -- unconditional), or not.  The FIRST standing point is
    the naive route's own point and is histogrammed separately; a
    colouring whose wall predicate fires is abandoned after one standing
    draw (its persistence is the (OC-42) theorem), a rank-2 colouring
    without the wall is re-drawn to its full draw budget (persistence
    measured, not assumed).

POOL: POOL-OQ2 (this driver's own; disjoint from every earlier pool of the
section; POOL-OS / POOL-OG / POOL-OQ / POOL-OR / POOL-OC2 are OSCHU's and
are neither re-run nor extended here; the landed 570/570 and 174/174
figures are CITED, never recomputed).  Each hit is a WITNESS, never a
rate; sigma-fixed points are never composite-guard generic ((AC-9)), and
no figure here is evidence about a generic chart point ((OC-7)).

MODES (foreground, one at a time, from the repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --controls
    PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --range 0 30    # then 30 60,
    #   60 90, 90 115, 115 140, 140 160, 160 174 -- the foreground chunked
    #   census over the single global (|V|, label) class order; per-class
    #   seeds are keyed by the GLOBAL index, so chunking moves no figure
    PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --census1       # parity halves
    PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --census2       #   (same figures)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --validate     # controls + 6 classes

IMPORTS (read-only; nothing existing is modified): `oschu`
(`out_classes`, the class key and pinned splits), `grid` (`block_data`,
`colourings`, `combinatorial_filter`, `build_fixed_config_params`),
`gridwit` (`tree_triple`), `closure` (`build_fixed_config`, `extensors`,
`star_sign`, `components`, ruling lines, `Gauss`), `outer` (`split_data`),
`hybrid_gates` (`build_rigidity_extensors`), `pitch` (`klein`, `Q`),
`repin` (`hodge_star`, `span_basis`), `kbare_common`, `nogood_subdiv`,
`exactcore`.

HARNESS DEBT, recorded not paid (this pass may not modify a landed file):
  * `oschu.out_classes` / `oschu.shape_key` gain a SECOND consumer with
    this pass -- section-2 rule 2's move-down trigger, a NEW unpaid item.
  * `gridwit.tree_triple` gains a THIRD consumer (grid, oschu, this pass)
    -- the same trigger, RE-DATED.
"""
import random
import sys
import time
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import dot, nullspace, rank, wedge2                 # noqa: E402
from kbare_common import verts_of                # noqa: E402
from nogood_subdiv import hcard_ok                                 # noqa: E402
from pitch import Q, klein                                         # noqa: E402
from repin import hodge_star, span_basis                           # noqa: E402
from hybrid_gates import build_rigidity_extensors                  # noqa: E402
import closure                                                     # noqa: E402
from grid import (block_data, build_fixed_config_params,           # noqa: E402
                  colourings, combinatorial_filter)
from gridwit import tree_triple                                    # noqa: E402
import outer                                                       # noqa: E402
from oschu import out_classes                                      # noqa: E402

PARAM_SEED = 20260825          # printed; per-class rng = Random(PARAM_SEED*100+ci)
COL_CAP = 1 << 16              # colouring enumeration cap (disclosed on hit)
PROBE_CAP = 48                 # filter-passing colourings probed per shape
DRAW_CAP = 4                   # parameter draws per colouring


def find_edge(E, x, y):
    for e in E:
        if (e[0] == x and e[1] == y) or (e[0] == y and e[1] == x):
            return e
    return None


def gram(B):
    return [[klein(x, y) for y in B] for x in B]


def gram_rank(B):
    G = gram(B)
    return rank([list(r) for r in G]) if B else 0


def cert_colourings(E, allverts, cap):
    """LAZY generator of the first `cap` filter-passing admissible
    colourings carrying both-block tree-triple certificates, in enumeration
    order.  Same hunt as `oschu.certify_shape` (whose class-predicate
    asserts already ran over this population at the (OC-34) landing and are
    not repeated here), but YIELDS the colourings -- lazily, because most
    classes hit at the first one and a tree-triple hunt is the expensive
    step.  Yields (colouring, probed-so-far)."""
    cols, odd = colourings(E, cap=COL_CAP)
    assert not odd and cols is not None, "odd-cycle obstruction / cap"
    probed, found = 0, 0
    for col in cols:
        if combinatorial_filter(E, allverts, col):
            continue
        if probed >= PROBE_CAP or found >= cap:
            return
        probed += 1
        if closure.build_fixed_config(E, allverts, col) is None:
            continue
        ok = True
        for mine in ('A', 'B'):
            tt, _capped = tree_triple(block_data(E, allverts, col, mine))
            if tt is None:
                ok = False
                break
        if ok:
            found += 1
            yield col, probed


def ruling_lines_of_H(Hed, VH, col, pt, fam):
    """One hinge extensor per `fam`-component of `H` that carries an edge:
    the component's ruling line (every edge of one component lies on the
    SAME ruling line -- (FR-3)(i); asserted)."""
    Ef = [e for e in Hed if col[e] == fam]
    comp = closure.components(VH, Ef)
    lines = {}
    for e in Ef:
        cid = comp[e[0]]
        L = wedge2(pt[e[0]], pt[e[1]])
        if cid in lines:
            assert rank([lines[cid], L]) == 1, \
                "two edges of one component off a common ruling line"
        else:
            lines[cid] = L
    return list(lines.values())


def single_class_paths(Hed, VH, col, fam, b, c):
    """The classes `i` of `H`'s `fam`-forest such that `b` and `c` are
    joined inside (class-i edges) + (other-family edges) alone -- the
    (OC-42) WALL predicate: such a path confines every achievable
    `fam`-block flow value to the single conic point `A(s_i)`, so the
    block generator lies ON the conic at EVERY parameter draw."""
    Ef = [e for e in Hed if col[e] == fam]
    Eo = [e for e in Hed if col[e] != fam]
    comp = closure.components(VH, Ef)
    out = []
    for cid in sorted({comp[e[0]] for e in Ef}):
        sub = Eo + [e for e in Ef if comp[e[0]] == cid]
        if closure.components(VH, sub)[b] == closure.components(VH, sub)[c]:
            out.append(cid)
    return out


def point_at(E, allverts, target, v, a, b, c, Hed, col, pt, X, Ycol):
    """Every (OC-40)/(OC-41) assertion and measurement at ONE standing
    target-rank grid point.  Returns the result dict."""
    if True:
        VH = sorted(verts_of(Hed), key=str)
        rowsH = build_rigidity_extensors(
            VH, closure.extensors(Hed, pt))
        assert 5 * len(Hed) == rank(rowsH), "sigma != 0 at target rank"
        mot = nullspace(rowsH)
        idx = {u: k for k, u in enumerate(VH)}
        D = span_basis([[m[6 * idx[b] + k] - m[6 * idx[c] + k]
                         for k in range(6)] for m in mot])
        assert len(D) == 3, "dim D != 3"
        # (OC-40): star-invariance, the (1,2) split, block families.
        sD = [hodge_star(d) for d in D]
        assert rank(list(D) + sD) == 3, "D is not star-invariant"
        Dp = span_basis([[d[k] + s[k] for k in range(6)]
                         for d, s in zip(D, sD)])
        Dm = span_basis([[d[k] - s[k] for k in range(6)]
                         for d, s in zip(D, sD)])
        assert len(Dp) + len(Dm) == 3, "blocks do not sum to D"
        Cvb = wedge2(pt[v], pt[b])
        Cac = wedge2(pt[a], pt[c])
        Cva = wedge2(pt[v], pt[a])
        sgn = closure.star_sign(Cvb)
        assert sgn is not None and sgn == closure.star_sign(Cac), \
            "C(vb), C(ac) not same-family ruling lines"
        assert closure.star_sign(Cva) == -sgn, "C(va) not opposite family"
        DX, DY = (Dp, Dm) if sgn == +1 else (Dm, Dp)
        assert len(DX) == 1 and len(DY) == 2, "the (1,2) split failed"
        # (Lambda-0d) for free, and the per-family direct sums.
        assert dot(pt[b], pt[c]) != 0, "(Lambda-0d) fails at a grid point"
        assert rank(list(D) + [Cac, Cva, Cvb]) == 6, \
            "(OC-31)(iii) direct sum fails"
        assert rank(DX + [Cvb, Cac]) == 3, "X-family direct sum fails"
        assert rank(DY + [Cva]) == 3, "Y-family direct sum fails"
        # cross-block B-orthogonality.
        assert all(klein(x, y) == 0 for x in Dp for y in Dm), \
            "blocks not B-orthogonal"
        # (OC-41): the criterion, both sides computed independently.
        g0 = DX[0]
        qg = Q(g0)
        rQD = gram_rank(D)
        rY = gram_rank(DY)
        assert rQD == (1 if qg != 0 else 0) + rY, \
            "(OC-41) criterion identity fails"
        # dimK <= 2 at the grid point ((OC-31), re-verified in homogeneous
        # QQ(i) coordinates: M^ = pt(b)^perp cap pt(c)^perp, W = <b, c>).
        Mhat = nullspace([pt[b], pt[c]])
        assert len(Mhat) == 2, "meet cone not 2-dimensional"
        MW = [wedge2(m, w) for m in Mhat for w in (pt[b], pt[c])]
        assert rank(MW) == 4, "M^ ^ W not 4-dimensional"
        dimK = 3 + 4 - rank(list(D) + MW)
        assert dimK <= 2, "(OC-31) dimK >= 3 at a target-rank point"
        # support diagnostics (value-level, canonical).
        LX = ruling_lines_of_H(Hed, VH, col, pt, X)
        LY = ruling_lines_of_H(Hed, VH, col, pt, Ycol)
        on_line = any(rank([g0, L]) == 1 for L in LX)
        secantX = any(rank([g0, LX[i], LX[j]]) == 2
                      for i in range(len(LX)) for j in range(i + 1, len(LX)))
        secantY = any(rank(DY + [LY[i], LY[j]]) == 2
                      for i in range(len(LY)) for j in range(i + 1, len(LY)))
        if on_line:
            assert qg == 0, "g on a ruling line yet Q(g) != 0"
        # the (OC-42) WALL predicate, both families.  X-side: a single-class
        # b-c path FORCES g onto that class's ruling line (asserted).
        # Y-side: a single-class path would force dim D_Y <= 1, so target
        # rank makes the predicate VACUOUS there (asserted).
        wallX = single_class_paths(Hed, VH, col, X, b, c)
        assert not single_class_paths(Hed, VH, col, Ycol, b, c), \
            "single-class Y-path at a target-rank point (dim D_Y = 2?!)"
        if wallX:
            assert qg == 0 and on_line, \
                "(OC-42) wall predicate holds yet g is off the conic"
        # is the (OC-31)(b) ruling K = M^ ^ w actually IN D at a bad point?
        # K = D cap (M^ ^ W); a ruling M^ ^ w inside D forces dimK = 2 with
        # K totally isotropic, so test: dimK = 2 and Gram_B(K) = 0.
        ruling_in_D = False
        if dimK == 2:
            # K via intersection: solve for D-combinations inside M^ ^ W
            rows = [[Dv[t] for Dv in D] + [m[t] for m in MW]
                    for t in range(6)]
            ker = nullspace(rows)
            Kbasis = span_basis(
                [[sum(kv[i] * D[i][t] for i in range(3)) for t in range(6)]
                 for kv in ker])
            assert len(Kbasis) == dimK, "K basis dimension mismatch"
            ruling_in_D = gram_rank(Kbasis) == 0
        return dict(rQD=rQD, qg_nonzero=(qg != 0), rY=rY, dimK=dimK,
                    ruling=ruling_in_D, wallX=bool(wallX),
                    suppX=('line' if on_line else
                           'secant' if secantX else 'off'),
                    suppY=('secant' if secantY else 'off'),
                    nLX=len(LX), nLY=len(LY))


CERT_CAP = 6                   # certificate colourings tried per class


def class_point(lab, E, v, ci):
    """Hunt, over the first CERT_CAP certificate colourings x DRAW_CAP
    seeded draws each, for a target-rank grid point with rank(Q|_D) = 3;
    run every (OC-40)/(OC-41) assertion at every standing target-rank point
    met on the way.  Returns a result dict (hit or miss) with the full
    per-colouring diagnostics -- in particular the outcome at the FIRST
    standing point, which is the naive route's own point."""
    allverts = sorted(verts_of(E), key=str)
    target = 6 * (len(allverts) - 1)
    a, b, c, Gp, Hed = outer.split_data(E, v)
    evb, eva, eac = (find_edge(E, v, b), find_edge(E, v, a),
                     find_edge(E, a, c))
    assert hcard_ok(E), "hcard fails"
    deg, nb = {}, {}
    for (x, y) in E:
        deg[x] = deg.get(x, 0) + 1
        deg[y] = deg.get(y, 0) + 1
        nb.setdefault(x, []).append(y)
        nb.setdefault(y, []).append(x)
    rng = random.Random(PARAM_SEED * 100 + ci)
    diag, first, probed, ncols = [], None, 0, 0
    for cj, (col, probed) in enumerate(cert_colourings(E, allverts,
                                                       CERT_CAP)):
        ncols += 1
        X, Ycol = col[evb], col[eva]
        # (OC-40) alternation: col(vb) = col(ac) != col(va), forced by
        # admissibility at the degree-2 interiors v and a.
        assert col[eac] == X and Ycol != X, "alternation violated at v / a"
        EA = [e for e in E if col[e] == 'A']
        EB = [e for e in E if col[e] == 'B']
        compA = closure.components(allverts, EA)
        compB = closure.components(allverts, EB)
        reasons = {'coincide': 0, 'li': 0, 'offtarget': 0}
        ranks_here = []
        for draw in range(DRAW_CAP):
            pA = {cid: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
                  for cid in sorted(set(compA.values()))}
            pB = {cid: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
                  for cid in sorted(set(compB.values()))}
            built = build_fixed_config_params(E, allverts, col, pA, pB)
            if built is None:
                reasons['coincide'] += 1
                continue
            pt, _, _ = built
            # sigma-fixed grid sanity: isotropy and conjugacy, exact.
            for u in allverts:
                assert dot(pt[u], pt[u]) == 0, "body off the fixed quadric"
            for (u, w) in E:
                assert dot(pt[u], pt[w]) == 0, "bodies not conjugate"
            # (GR-5) hypotheses: closed-hub-neighbourhood LI at every body
            # (bodies-distinct is build's own None-check; hcard above).
            li_ok = True
            for u in allverts:
                S = [w for w in ([u] + sorted(nb.get(u, []), key=str))
                     if deg.get(w, 0) >= 3]
                pts = [pt[w] for w in S]
                if pts and rank(pts) != len(pts):
                    li_ok = False
                    break
            if not li_ok:
                reasons['li'] += 1
                continue
            ext = closure.extensors(E, pt)
            if rank(build_rigidity_extensors(allverts, ext)) != target:
                reasons['offtarget'] += 1
                continue
            # ---- a standing target-rank grid chart point.
            r = point_at(E, allverts, target, v, a, b, c, Hed, col, pt,
                         X, Ycol)
            ranks_here.append((r['rQD'], r['qg_nonzero'], r['rY'],
                               r['wallX']))
            if first is None:
                first = dict(r)
                first.update(cj=cj, draw=draw)
            if r['rQD'] == 3:
                r.update(cj=cj, draw=draw, probed=probed, diag=diag,
                         first=first)
                return r
            if r['wallX']:
                break            # structurally walled colouring: move on
        diag.append((cj, reasons, ranks_here))
    if ncols == 0:
        return dict(miss='no certificate colouring', probed=probed, diag=[])
    return dict(miss=f'no rank-3 grid point under caps '
                     f'({ncols} colourings x {DRAW_CAP} draws)',
                probed=probed, diag=diag, first=first)


def census(part, cap=None, lo=None, hi=None):
    cls = out_classes()
    cls.sort(key=lambda r: (len(verts_of(r[1])), str(r[0])))
    if lo is not None:
        mine = [(i, r) for i, r in enumerate(cls) if lo <= i < hi]
        tag = f"chunk [{lo}, {hi}) of the (|V|, label) order"
    else:
        mine = [(i, r) for i, r in enumerate(cls) if i % 2 == (part - 1)]
        tag = f"part {part} of 2"
    if cap is not None:
        mine = mine[:cap]
    print(f"== (OC-43): rank(Q|_D) at certificate GRID points of every "
          f"isomorphism class, POOL-OQ2 {tag} ==")
    print(f"   population: `oschu.out_classes()` -- {len(cls)} classes, the "
          f"(OC-34) key, at the SAME\n   pinned (shape, split) as POOL-OC2; "
          f"hunt over the first {CERT_CAP} filter-passing colourings\n   "
          f"with both-block tree-triple certificates (probe cap "
          f"{PROBE_CAP}, colouring cap 2^16)\n   x {DRAW_CAP} seeded "
          f"parameter draws each; parameter seed {PARAM_SEED} (per-class "
          f"rng\n   {PARAM_SEED}*100+ci).  This part: {len(mine)} classes.")
    print("   Each hit is a WITNESS, never a rate; sigma-fixed points are "
          "never composite-guard\n   generic ((AC-9)); POOL-OC2's landed "
          "174/174 is cited, not re-run.\n")
    t0, hist, fhist, miss, moved = time.time(), {}, {}, [], []
    for ci, (lab, E, v, k) in mine:
        r = class_point(lab, E, v, ci)
        f = r.get('first')
        if f is not None:
            fkey = (f['rQD'], f['qg_nonzero'], f['rY'], f['dimK'],
                    f['ruling'], f['wallX'], f['suppX'], f['suppY'])
            fhist[fkey] = fhist.get(fkey, 0) + 1
        if 'miss' in r:
            miss.append((lab, r['miss'], r['probed']))
            print(f"   MISS {lab:40s} {r['miss']} (probed {r['probed']})")
            for row in r['diag']:
                print(f"        col {row[0]}: reject reasons {row[1]}, "
                      f"standing-point (rQD, Q(g)!=0, rY): {row[2]}")
            continue
        key = (r['rQD'], r['qg_nonzero'], r['rY'], r['dimK'],
               r['wallX'], r['suppX'], r['suppY'])
        hist[key] = hist.get(key, 0) + 1
        if r['cj'] > 0 or r['draw'] > 0:
            moved.append((lab, r['cj'], r['draw'],
                          (f['rQD'], f['suppX'], f['wallX']) if f else None,
                          r['diag']))
    print(f"\n   classes probed: {len(mine)};  rank-3 witnesses: "
          f"{len(mine) - len(miss)};  misses: {len(miss)}"
          f"   [{time.time() - t0:.0f} s]")
    print("   HIT rows (rank(Q|_D), Q(g)!=0, rank Gram(D_Y), dimK, wallX, "
          "suppX, suppY) -> count:")
    for kk in sorted(hist, key=str):
        print(f"       {kk} : {hist[kk]}")
    print("\n   the NAIVE route's own point (first standing target-rank "
          "point, first certificate\n   colouring): (rQD, Q(g)!=0, rY, "
          "dimK, ruling M^^w in D, wallX, suppX, suppY) -> count:")
    for kk in sorted(fhist, key=str):
        print(f"       {kk} : {fhist[kk]}")
    if moved:
        print(f"\n   classes where the FIRST standing point was NOT the "
              f"hit ({len(moved)}):")
        for lab, cj, dr, fr, dg in moved:
            print(f"       {lab:40s} hit at colouring {cj} draw {dr}; "
                  f"first point gave {fr}")
            for row in dg:
                print(f"           col {row[0]}: reject reasons {row[1]}, "
                      f"standing (rQD, Q(g)!=0, rY, wallX): {row[2]}")
    print("\n   asserted per standing point: isotropy/conjugacy; hcard + "
          "the (GR-5) LI hypothesis;\n   FULL QQ(i) target rank; sigma = "
          "0; dim D = 3; star D = D; the (1,2) split with the\n   1-dim "
          "block in family col(vb); (Lambda-0d); (OC-31)(iii) + both "
          "per-family direct\n   sums; cross-block B-orthogonality; the "
          "(OC-41) criterion identity; dimK <= 2;\n   and Q(g) = 0 "
          "whenever g lies on a component ruling line.")
    print("   A `rank(Q|_D) = 3` row is, with (OC-33)(ii), an individual "
          "PROOF that input (a)\n   holds at that (shape, split), at that "
          "exact QQ(i) point.")
    if not miss:
        print("\nCENSUS PART OK.")
    else:
        print(f"\nCENSUS PART: {len(miss)} MISSES -- see rows above.")


def controls():
    """Must-reject witnesses for the (OC-41) criterion: synthetic 3-spaces
    with a PLANTED degeneracy in one block, each detected by the same
    criterion identity that the census asserts (README section 4
    convention 6: a guard observed only passing is untested)."""
    print("== (OC-41) controls: planted per-block degeneracies ==")
    print(f"   seed {PARAM_SEED} (synthetic ruling parameters)\n")
    rng = random.Random(PARAM_SEED)

    def rnd_params(n, taken):
        out = []
        while len(out) < n:
            s = F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
            if s not in taken and s not in out:
                out.append(s)
        return out

    def A(s):
        return closure.ruling_A_line((1, s))

    def Bl(u):
        return closure.ruling_B_line((1, u))

    def scaled(V, ws):
        return [sum((w * x for w, x in zip(ws, col)),
                    start=ws[0] * 0) for col in zip(*V)]

    # control 1: X-block generator ON the conic (a ruling line) -- the
    # structural danger case.  D = <A(s1)> (+) <B(u1), B(u2)>.
    s1, = rnd_params(1, [])
    u1, u2 = rnd_params(2, [])
    D1 = [A(s1), Bl(u1), Bl(u2)]
    g1 = D1[0]
    assert Q(g1) == 0 and gram_rank(D1) == 0 + gram_rank([Bl(u1), Bl(u2)]) \
        and gram_rank(D1) == 2, "control 1 failed"
    print("   control 1 (g a ruling line):        rank(Q|_D) = 2 = 0 + 2, "
          "detected  OK")
    # control 2: Y-block a TANGENT plane -- span{B(u1), B'(u1)}.  B(u) is
    # QUADRATIC in u, so the central difference with step 1 is the exact
    # derivative: B'(u1) = (B(u1+1) - B(u1-1)) / 2.
    dB = [(x - y) / 2 for x, y in zip(Bl(u1 + 1), Bl(u1 - 1))]
    s2, = rnd_params(1, [s1])
    g2 = [x + y for x, y in zip(A(s1), A(s2))]        # off-conic generator
    D2 = [g2, Bl(u1), dB]
    assert Q(g2) != 0, "control 2 generator degenerate"
    rY2 = gram_rank([Bl(u1), dB])
    assert rY2 == 1 and gram_rank(D2) == 1 + rY2 == 2, "control 2 failed"
    print("   control 2 (D_Y tangent plane):      rank(Q|_D) = 2 = 1 + 1, "
          "detected  OK")
    # control 3: both blocks clean -- the criterion's PASS shape, secant
    # cases in both families (nondegenerate for EVERY parameter choice).
    u3, = rnd_params(1, [u1, u2])
    D3 = [g2, Bl(u1), Bl(u3)]
    assert gram_rank(D3) == 3 == 1 + 2, "control 3 failed"
    print("   control 3 (secant/secant, clean):   rank(Q|_D) = 3 = 1 + 2  "
          "OK")
    # control 4: a planted RULING M^ ^ w inside D forces rank <= 2 through
    # the criterion: D = <A(s1), A(s2)> (+) <B(u1)> has the X-block secant
    # (rank 2) and the Y-block a single conic point (rank 0) -- the (1,2)
    # split does NOT hold for this synthetic D (it is (2,1)), so it tests
    # the block identity off the census's split shape as well.
    D4 = [A(s1), A(s2), Bl(u1)]
    assert gram_rank(D4) == gram_rank([A(s1), A(s2)]) + \
        gram_rank([Bl(u1)]) == 2, "control 4 failed"
    print("   control 4 ((2,1) split, Y planted): rank(Q|_D) = 2 = 2 + 0  "
          "OK")
    print("\nCONTROLS OK.")


def main():
    modes = {'--census1': lambda: census(1), '--census2': lambda: census(2),
             '--controls': controls,
             '--validate': lambda: (controls(), census(1, cap=3),
                                    census(2, cap=3))}
    if len(sys.argv) == 4 and sys.argv[1] == '--range':
        # the SIGZ-precedent foreground split: deterministic chunks of the
        # single global (|V|, label) order; per-class seeds are keyed by the
        # GLOBAL index, so chunk boundaries cannot move any figure.
        census(None, lo=int(sys.argv[2]), hi=int(sys.argv[3]))
        return 0
    if len(sys.argv) != 2 or sys.argv[1] not in modes:
        print("usage: oqrank.py --controls | --census1 | --census2 | "
              "--range A B | --validate")
        return 1
    modes[sys.argv[1]]()
    return 0


if __name__ == '__main__':
    sys.exit(main())
