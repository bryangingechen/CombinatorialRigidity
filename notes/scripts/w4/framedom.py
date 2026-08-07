"""
Phase 39, kernel-(K) FOURTH fan-out direction J -- the shared CHART-TO-FRAME
DOMINANCE residue ((K-out) (OC-16) / (K-ann) (ANH-14)), attacked with the
sigma-fixed grid witnesses of (K-grid) (GR-5)/(GR-9), transported to the
SPLIT graph `G' = G - v + ab`.

Workbook section: `(K-frame)`, labels `(FR-1)+` (the reserved direction-J
namespace, `notes/Pencil-labels.md` 2026-08-06 E/J table).  Read against
section (K-grid) *Step G13* (the candidate lemma shape), section (K-ann)
*Steps A14-A17* ((ANH-13)/(ANH-14): the bare-cycle stratum's universal
degree-12 polynomial `C`), section (K-out) *Steps O11-O12*
((OC-13)/(OC-15)/(OC-16): the bad line `C0`, the path-span form of `R1` on
the `ell_min = 5` stratum), and section (K-clos) (AC-2)/(AC-9).

THE TRANSPORT FACT this driver rides (novel here; (FR-2)/(FR-3)).  At a
sigma-fixed grid configuration EVERY hinge line is a RULING LINE of the
fixed quadric (adjacent bodies are conjugate, and a line through two
conjugate points of a quadric lies on it).  The two ruling families span
COMPLEMENTARY 3-spaces W_A (+) W_B = Lambda^2 K^4, each family a Veronese
conic in its own 3-space; so ANY 6x6 hinge-line determinant at a grid point
-- in particular BOTH bad divisors, (ANH-14)'s `C` and (OC-16)'s `Delta` --
is nonzero IFF its six edges are coloured 3-3 between the rulings with the
three lines in each family pairwise distinct.  Line identity is
combinatorial: two same-family edges lie on the same ruling line iff their
endpoints lie in the same component of that family's edge set.

Modes (run from the repo root, PYTHONHASHSEED=0):

    python3 notes/scripts/w4/framedom.py --rulings   # (FR-2)+(FR-3) measured: the decomposition + the Vandermonde determinant law
    python3 notes/scripts/w4/framedom.py --pattern   # (FR-4) combinatorial half: pattern-availability over ALL 1904 bare-cycle sites
    python3 notes/scripts/w4/framedom.py --transport # (FR-4) exact half: built grid certificates, C != 0 exactly, both directions
    python3 notes/scripts/w4/framedom.py --outer     # (FR-5): the (OC-16) side at theta(3,4,5) -- Delta, lambda_1, target rank, dim R_a
    python3 notes/scripts/w4/framedom.py --validate  # machinery pins (incl. the framedom.m2 cross-language instance)

WHICH MODE TESTS WHICH SENTENCE (F11).

--rulings   (FR-2): rank W_A = rank W_B = 3, W_A (+) W_B = K^6, any 3
            distinct same-family lines independent, any 4 dependent; and
            (FR-3)'s determinant law det6[A(s1),A(s2),A(s3),B(u1),B(u2),
            B(u3)] = c * Vdm(s) * Vdm(u) with one constant c, asserted over
            seeded draws (the function-field identity is framedom.m2's
            (FR-M1); this mode is its measured shadow).
--pattern   (FR-4) availability: at how many of the 1904 bare-cycle sites of
            the full (ANH-9) triple pool does an admissible colouring of G'
            exist whose grid point satisfies the (FR-3) criterion on the
            site's six frame edges PLUS the placement-free legality tests
            (all bodies distinct, closedHubNbhd sets not collinear)?  Also
            asserts the site census reproduces (ANH-13)'s 1904.
--transport (FR-4) certificate: at the census-pool bare-cycle sites and a
            deterministic slice of sweep sites, the pattern colouring's
            BUILT grid point passes every exact legality gate
            (verify_pencil_witness, closedHubNbhd ranks, isotropy/conjugacy)
            and has C != 0 EXACTLY (rank 6 and det6 != 0, two routes); and
            the criterion is IFF: at a criterion-violating colouring of the
            same site the built determinant VANISHES (negative control).
--outer     (FR-5): at theta(3,4,5) (the ell_min = 5 stratum's inhabitant),
            per admissible colouring of G' and per companion end: the exact
            values of Delta = det6[chain5, C(h,a)], the outer line's
            membership C_out in span(chain5) (= lambda_i = 0 there, by
            (OC-15)'s pointwise containment + the dimension pinch), the
            combinatorial predictions for both, and outer.stratum_at's
            (target rank, dim R_a) at the dehomogenized QQ(i) placement --
            the measured answer to "are grid points on the hard stratum".
--validate  machinery: grid_point isotropy + the (AC-2) conjugacy law,
            hinge-line-proportional-to-ruling-line, det6 vs exactcore.rank
            cross-check, and the FIXED rational instance det6 value that
            framedom.m2's (FR-M0) pins from the M2 side.

Exact arithmetic throughout: QQ (fractions.Fraction) and QQ(i)
(closure.Gauss); no floating point.  Seeded rngs only, seeds printed.
sigma-fixed grid configurations are CONSTRUCTED existence witnesses;
nothing here is quoted as a rate over sampled placements, and NO
composite-guard genericity is claimed anywhere ((AC-9): sigma-fixed points
are never `repin.star_generic`-generic -- every certificate below goes
through exact rank at the constructed point + lower semicontinuity on the
chart).  Imports `gridwit` (via its canonical layer `grid`/`closure`),
`outerwide`, `anhr1`, `shrink` READ-ONLY; nothing existing is modified.
"""
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, wedge2, dot                               # noqa: E402
from kbare_common import verts_of, is_2ec, verify_pencil_witness      # noqa: E402
from nogood_subdiv import hcard_ok                                    # noqa: E402
import closure                                                        # noqa: E402
from closure import (colourings, components, grid_point,              # noqa: E402
                     ruling_A_line, ruling_B_line, g)
from grid import build_fixed_config_params, proportional              # noqa: E402
from repin import span_basis                                          # noqa: E402
from outer import (split_data, companions4, stratum_at,               # noqa: E402
                   named_inventory, sweep_shapes)
from annih import habitats4, path_edges                               # noqa: E402
from shrink import hp_edge_rows, census_pool                          # noqa: E402
from anhr1 import core_decompose                                      # noqa: E402
from outerwide import companion_sets, chain_to_weld                   # noqa: E402

FR_SEED = 20260807


# ---------------- small exact devices (owned by this driver) ---------------

def det6(M):
    """6x6 determinant by permutation expansion (exact; QQ or QQ(i) entries).
    An arc-specific device: no 6x6 determinant primitive exists in the
    harness (`pitch.det4` is 4x4); nonzero-ness is always cross-checked
    against the canonical `exactcore.rank`."""
    assert len(M) == 6 and all(len(r) == 6 for r in M)
    tot = 0
    for perm in itertools.permutations(range(6)):
        sgn, seen = 1, list(perm)
        for i in range(6):
            while seen[i] != i:
                j = seen[i]
                seen[i], seen[j] = seen[j], seen[i]
                sgn = -sgn
        term = M[0][perm[0]]
        for i in range(1, 6):
            term = term * M[i][perm[i]]
        tot = term * sgn + tot
    return tot


def chn_sets(edges):
    """closedHubNbhd v AS A SET, per `Motive.lean:82` (the canonical
    `kbare_common.closed_hub_nbhds` returns only the CARDINALITIES, which is
    why this set-valued variant lives here).  {w : deg w >= 3 and
    (w = v or w ~ v)}."""
    from exactcore import neighbors
    nb = neighbors(edges)
    deg = {u: len(nb[u]) for u in nb}
    out = {}
    for v in sorted(nb, key=str):
        s = set()
        if deg.get(v, 0) >= 3:
            s.add(v)
        for w in nb[v]:
            if deg.get(w, 0) >= 3:
                s.add(w)
        out[v] = s
    return out


def ckey(col, e):
    """Normalize an (u, w) pair to the tuple orientation `col` is keyed by."""
    return e if e in col else (e[1], e[0])


def line_ids(col, compA, compB, edges6):
    """(family, ruling-line id) per edge.  Two same-family edges lie on the
    SAME ruling line iff their endpoints share that family's component (the
    family parameter is constant on components and injective across them)."""
    out = []
    for e0 in edges6:
        e = ckey(col, e0)
        f = col[e]
        out.append((f, (compA if f == 'A' else compB)[e[0]]))
    return out


def crit_33(ids):
    """(FR-3)'s combinatorial criterion: 3-3 family split, three distinct
    lines per family."""
    A = [i for f, i in ids if f == 'A']
    B = [i for f, i in ids if f == 'B']
    return len(A) == 3 and len(B) == 3 and \
        len(set(A)) == 3 and len(set(B)) == 3


def legality_free(col, compA, compB, allverts, chn):
    """The placement-free legality tests a pattern colouring must ALSO pass
    for its generic-parameter grid point to satisfy (GR-5)-at-G's
    hypotheses: (i) all bodies distinct -- (cA, cB) pairs injective; (ii) at
    every body the closedHubNbhd point set is linearly independent -- for
    grid points, 3 distinct quadric points are dependent iff collinear iff
    all on one ruling line iff they share a family component."""
    pairs = {(compA[v], compB[v]) for v in allverts}
    if len(pairs) != len(allverts):
        return False
    for v in sorted(chn, key=str):
        S = sorted(chn[v], key=str)
        if len(S) == 3:
            if len({compA[w] for w in S}) == 1 or \
               len({compB[w] for w in S}) == 1:
                return False
    return True


def draw_params(compA, compB, rng, tries=24):
    """Injective-per-family random Fraction parameters (seeded)."""
    for _ in range(tries):
        pA = {c: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
              for c in sorted(set(compA.values()))}
        pB = {c: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
              for c in sorted(set(compB.values()))}
        if len(set(pA.values())) == len(pA) and \
           len(set(pB.values())) == len(pB):
            return pA, pB
    raise AssertionError("could not draw injective ruling parameters")


def build_at(GpE, allverts, col, rng, want_affine=True, tries=12):
    """Grid config at `col` with seeded injective parameters; retries until
    all bodies are distinct and (when `want_affine`) no point is at
    infinity.  Returns (pt, pA, pB) or None."""
    for _ in range(tries):
        EA = [e for e in GpE if col[e] == 'A']
        EB = [e for e in GpE if col[e] == 'B']
        compA = components(allverts, EA)
        compB = components(allverts, EB)
        pA, pB = draw_params(compA, compB, rng)
        built = build_fixed_config_params(GpE, allverts, col, pA, pB)
        if built is None:
            continue
        pt, _, _ = built
        if want_affine and any(pt[v][3] == 0 for v in allverts):
            continue
        return pt, pA, pB
    return None


def config_asserts(GpE, allverts, pt):
    """The mandatory degeneracy guards on a built config (README section 4
    convention 1): isotropy at every body, conjugacy at every edge, every
    hinge line nonzero, all bodies pairwise distinct as projective points."""
    for v in allverts:
        assert dot(pt[v], pt[v]) == 0, "grid point off the quadric"
    for (u, w) in GpE:
        assert dot(pt[u], pt[w]) == 0, "adjacent bodies not conjugate"
        L = wedge2(pt[u], pt[w])
        assert any(x != 0 for x in L), "zero hinge line"
    pts = [pt[v] for v in allverts]
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            assert not proportional(pts[i], pts[j]), "coincident bodies"


def dehom3(p):
    assert p[3] != 0
    return [p[0] / p[3], p[1] / p[3], p[2] / p[3]]


# ---------------- the site census (bare-cycle sites of the (ANH-9) pool) ---

def bare_sites(Hed, b, c):
    """Per length-4 companion of (b, c): the length-5 branches beta of H/P
    whose reduced object H/P - beta is a BARE CYCLE, each with the six
    G'-edges of that cycle in cyclic order.  Returns
    [(P, k_branch, [six edge tuples])]; also counts the non-bare length-5
    sites so the census can be pinned against (ANH-13)'s histogram."""
    out, other5 = [], 0
    for P in companions4(Hed, b, c):
        Pe = path_edges(Hed, P)
        Pset = {j for (j, s) in Pe}
        Pverts = set(P)
        rows = hp_edge_rows(Hed, Pverts, Pset)
        nodes, branches = core_decompose(rows)
        for kb, (e0, e1, chain) in enumerate(branches):
            if len(chain) != 5 or e0 is None:
                continue
            drop = {r[0] for r in chain}
            keep = [r for r in rows if r[0] not in drop]
            nd, br = core_decompose(keep)
            if nd or len(br) != 1:
                other5 += 1
                continue
            cyc = br[0][2]
            assert len(cyc) == 6, "bare cycle is not a 6-cycle"
            out.append((P, kb, [Hed[r[0]] for r in cyc]))
    return out, other5


def pool_splits():
    """The (ANH-9) triple pool's (label, E, v, split-data) stream, in the
    same deterministic order as `anhr1.mode_size` (named inventory first,
    then the sweep families)."""
    fams = [('named', named_inventory())] + \
        [(desc, sh) for (desc, sh) in sweep_shapes()]
    for desc, shapes in fams:
        for label, E in shapes:
            for v in sorted(verts_of(E), key=str):
                sd = split_data(E, v)
                if sd is None:
                    continue
                yield desc, label, v, E, sd


# ---------------- mode: --rulings ((FR-2), (FR-3) measured) ----------------

def mode_rulings():
    print("== (FR-2)/(FR-3) the ruling decomposition and the determinant law ==")
    print(f"   seed {FR_SEED} (mode rng)")
    rng = random.Random(FR_SEED)
    svals = [F(rng.randint(1, 10 ** 4), rng.randint(1, 97)) for _ in range(8)]
    while len(set(svals)) != 8:
        svals = [F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
                 for _ in range(8)]
    A = [ruling_A_line((1, s)) for s in svals]
    B = [ruling_B_line((1, s)) for s in svals]
    assert rank(A) == 3 and rank(B) == 3
    assert rank(A + B) == 6
    print("   rank(8 A-lines) = 3, rank(8 B-lines) = 3, rank(A+B) = 6   OK")
    for trip in itertools.combinations(range(8), 3):
        assert rank([A[i] for i in trip]) == 3
        assert rank([B[i] for i in trip]) == 3
    print("   every 3 distinct same-family lines independent (56+56)     OK")
    for quad in itertools.combinations(range(8), 4):
        assert rank([A[i] for i in quad]) == 3
    print("   every 4 same-family lines dependent (70)                   OK")
    # the +/- Hodge eigenspaces vs the ruling spans, reported as a pin
    # ((AC-4)'s star-eigen decoupling):
    from repin import hodge_star
    rA_plus = rank([[x[k] + hodge_star(x)[k] for k in range(6)] for x in A[:3]])
    rA_minus = rank([[x[k] - hodge_star(x)[k] for k in range(6)] for x in A[:3]])
    rB_plus = rank([[x[k] + hodge_star(x)[k] for k in range(6)] for x in B[:3]])
    rB_minus = rank([[x[k] - hodge_star(x)[k] for k in range(6)] for x in B[:3]])
    print(f"   star-eigen content: W_A -> rank(x+*x)={rA_plus},"
          f" rank(x-*x)={rA_minus}; W_B -> {rB_plus},{rB_minus}"
          f" (reported; (AC-4))")
    # (FR-3) measured: det6 = c * Vdm(s) * Vdm(u), one constant c
    cconst = None
    for t in range(20):
        ss = sorted(rng.sample(range(2, 400), 3))
        uu = sorted(rng.sample(range(2, 400), 3))
        s1, s2, s3 = (F(x) for x in ss)
        u1, u2, u3 = (F(x) for x in uu)
        M = [ruling_A_line((1, s1)), ruling_A_line((1, s2)),
             ruling_A_line((1, s3)), ruling_B_line((1, u1)),
             ruling_B_line((1, u2)), ruling_B_line((1, u3))]
        d = det6(M)
        vdm = (s1 - s2) * (s1 - s3) * (s2 - s3) * \
              (u1 - u2) * (u1 - u3) * (u2 - u3)
        assert vdm != 0
        cc = d / vdm
        if cconst is None:
            cconst = cc
            print(f"   determinant-law constant c = {cc}")
        assert cc == cconst, "determinant law broke"
    print("   det6[A(s1..s3), B(u1..u3)] = c * Vdm(s) * Vdm(u) at 20 draws OK")
    # degenerate patterns
    M = [ruling_A_line((1, F(k))) for k in (2, 3, 5, 7)] + \
        [ruling_B_line((1, F(k))) for k in (2, 3)]
    assert det6(M) == 0 and rank(M) < 6
    M = [ruling_A_line((1, F(2)))] * 2 + [ruling_A_line((1, F(3)))] + \
        [ruling_B_line((1, F(k))) for k in (2, 3, 5)]
    assert det6(M) == 0
    print("   4-2 split and repeated-line determinants vanish             OK")
    print("PASSED")
    return 0


# ---------------- mode: --pattern ((FR-4) combinatorial half) --------------

def mode_pattern(col_cap=8192):
    print("== (FR-4) pattern-availability over the bare-cycle site pool ==")
    print("   per site: does an admissible colouring of G' = G - v + ab")
    print("   exist whose grid point satisfies the (FR-3) criterion on the")
    print("   site's six frame edges AND the placement-free legality tests?")
    print(f"   colouring cap per split: {col_cap}\n")
    tot, hit, capped_splits, miss = 0, 0, 0, []
    tot_other5 = 0
    nsplits, nsplits_sites = 0, 0
    hyp_fail = []
    for desc, label, v, E, sd in pool_splits():
        a, b, c, Gp, Hed = sd
        nsplits += 1
        sites, other5 = bare_sites(Hed, b, c)
        tot_other5 += other5
        if not sites:
            continue
        nsplits_sites += 1
        if not (hcard_ok(Gp) and is_2ec(Gp)):
            hyp_fail.append((label, v))
        allverts = sorted(verts_of(Gp), key=str)
        chn = chn_sets(Gp)
        cols, odd = colourings(Gp, cap=col_cap)
        assert not odd, f"{label}: G' has a bare odd cycle component"
        if cols is None:
            capped_splits += 1
            tot += len(sites)
            miss.extend((label, v, 'CAPPED') for _ in sites)
            continue
        unresolved = list(range(len(sites)))
        found = [False] * len(sites)
        for col in cols:
            if not unresolved:
                break
            EA = [e for e in Gp if col[e] == 'A']
            EB = [e for e in Gp if col[e] == 'B']
            compA = components(allverts, EA)
            compB = components(allverts, EB)
            if not legality_free(col, compA, compB, allverts, chn):
                continue
            still = []
            for k in unresolved:
                ids = line_ids(col, compA, compB, sites[k][2])
                if crit_33(ids):
                    found[k] = True
                else:
                    still.append(k)
            unresolved = still
        tot += len(sites)
        hit += sum(1 for f in found if f)
        for k in unresolved:
            miss.append((label, v, f'P#{sites[k][1]}'))
    print(f"   splits scanned: {nsplits}; with bare-cycle sites: {nsplits_sites}")
    print(f"   bare-cycle sites: {tot} (non-bare length-5 sites seen: {tot_other5})")
    assert tot == 1904, "site census does not reproduce (ANH-13)'s 1904"
    print("   site census == (ANH-13)'s 1904                              OK")
    print(f"   G' hypothesis failures (hcard/2ec): {len(hyp_fail)}")
    print(f"   capped splits: {capped_splits}")
    print(f"\n   PATTERN-AVAILABLE SITES: {hit} / {tot}"
          f" = {100.0 * hit / tot:.1f}%")
    if miss:
        print(f"   misses ({len(miss)}), first 12:")
        for row in miss[:12]:
            print(f"     {row}")
    else:
        print("   NO misses: every bare-cycle site of the pool admits a"
              " pattern colouring")
    print("PASSED")
    return 0


# ---------------- mode: --transport ((FR-4) exact certificates) ------------

def site_certificate(label, v, E, sd, site, rng, verbose=True):
    """Build the pattern colouring's grid point at one bare-cycle site and
    run every exact gate.  Returns 'cert' / 'no-pattern' / 'build-fail'."""
    a, b, c, Gp, Hed = sd
    P, kb, edges6 = site
    allverts = sorted(verts_of(Gp), key=str)
    chn = chn_sets(Gp)
    assert hcard_ok(Gp), f"{label}: hcard fails at G'"
    assert is_2ec(Gp), f"{label}: G' not 2-edge-connected"
    cols, odd = colourings(Gp, cap=8192)
    assert cols is not None and not odd
    pat_col, neg_col = None, None
    for col in cols:
        EA = [e for e in Gp if col[e] == 'A']
        EB = [e for e in Gp if col[e] == 'B']
        compA = components(allverts, EA)
        compB = components(allverts, EB)
        ok_leg = legality_free(col, compA, compB, allverts, chn)
        ok_crit = crit_33(line_ids(col, compA, compB, edges6))
        if pat_col is None and ok_leg and ok_crit:
            pat_col = col
        if neg_col is None and ok_leg and not ok_crit:
            neg_col = col
        if pat_col is not None and neg_col is not None:
            break
    if pat_col is None:
        return 'no-pattern'
    got = build_at(Gp, allverts, pat_col, rng)
    if got is None:
        return 'build-fail'
    pt, pA, pB = got
    config_asserts(Gp, allverts, pt)
    # (GR-5)-at-G' hypothesis, exact: closedHubNbhd point sets independent
    for u in allverts:
        S = sorted(chn[u], key=str)
        if S:
            assert rank([pt[w] for w in S]) == len(S), \
                "closedHubNbhd points dependent"
    # legality as a pencil-panel realization, exact (QQ(i) affine)
    placed = {u: dehom3(pt[u]) for u in allverts}
    okw, _ = verify_pencil_witness(Gp, placed)
    assert okw, "verify_pencil_witness rejected the grid point"
    # C != 0 exactly, two routes
    lines = [wedge2(pt[e[0]], pt[e[1]]) for e in edges6]
    assert rank(lines) == 6, "criterion held but C = 0"
    assert det6(lines) != 0, "rank/det6 cross-check failed"
    # negative control at the same site
    negnote = 'no-neg-colouring'
    if neg_col is not None:
        gotn = build_at(Gp, allverts, neg_col, rng)
        if gotn is not None:
            ptn, _, _ = gotn
            linesn = [wedge2(ptn[e[0]], ptn[e[1]]) for e in edges6]
            assert rank(linesn) < 6, "criterion failed but C != 0"
            assert det6(linesn) == 0
            negnote = 'neg-control C=0 OK'
    if verbose:
        print(f"   {label:<28} v={str(v):<4} P#{kb}  C != 0 exact,"
              f" witness green, {negnote}")
    return 'cert'


def mode_transport(sweep_slice=24):
    print("== (FR-4) exact grid certificates at bare-cycle sites ==")
    print(f"   seed {FR_SEED} (mode rng); census pool first, then the first"
          f" {sweep_slice} sweep sites\n")
    rng = random.Random(FR_SEED)
    ncert, nnopat, nbuild = 0, 0, 0
    seen = set()
    print("   -- census pool (the 6 (ANH-10) bare-cycle sites live here) --")
    for (nm, E, v) in census_pool():
        sd = split_data(E, v)
        assert sd is not None
        a, b, c, Gp, Hed = sd
        sites, _ = bare_sites(Hed, b, c)
        for site in sites:
            r = site_certificate(nm, v, E, sd, site, rng)
            ncert += (r == 'cert')
            nnopat += (r == 'no-pattern')
            nbuild += (r == 'build-fail')
        seen.add((nm, str(v)))
    print(f"   census-pool sites certified: {ncert}"
          f" (no-pattern {nnopat}, build-fail {nbuild})")
    print("\n   -- sweep slice --")
    ns = 0
    for desc, label, v, E, sd in pool_splits():
        if ns >= sweep_slice:
            break
        a, b, c, Gp, Hed = sd
        sites, _ = bare_sites(Hed, b, c)
        for site in sites:
            if ns >= sweep_slice:
                break
            r = site_certificate(label, v, E, sd, site, rng)
            ncert += (r == 'cert')
            nnopat += (r == 'no-pattern')
            nbuild += (r == 'build-fail')
            ns += 1
    print(f"\n   TOTAL exact certificates: {ncert}"
          f" (no-pattern {nnopat}, build-fail {nbuild})")
    assert nbuild == 0, "a pattern colouring failed to build"
    print("PASSED")
    return 0


# ---------------- mode: --outer ((FR-5), the (OC-16) side) -----------------

def mode_outer():
    print("== (FR-5) the (OC-16) side at theta(3,4,5): grid points vs the"
          " bad line, the outer line, and the stratum ==")
    print(f"   seed {FR_SEED} (mode rng)")
    print("   Delta = det6[5 chain hinge lines, C(h,a)]; L_h subset R_h iff")
    print("   Delta = 0 ((OC-16)); lambda = 0 iff C_out in R_h = span(chain)")
    print("   ((OC-1) + (OC-15)'s pointwise containment + the pinch")
    print("   dim span = 5 >= dim R_h -- proof-level, see the draft).\n")
    rng = random.Random(FR_SEED)
    hits = [h for h in habitats4() if 'theta' in h[0]]
    assert len(hits) == 1
    name, E, v = hits[0]
    sd = split_data(E, v)
    a, b, c, Gp, Hed = sd
    allverts = sorted(verts_of(Gp), key=str)
    chn = chn_sets(Gp)
    from exactcore import neighbors as NBS
    nbG = NBS(E)
    cols, odd = colourings(Gp, cap=8192)
    assert cols is not None and not odd
    print(f"   {name}: split v={v}, a={a}, b={b}, c={c};"
          f" {len(cols)} admissible colourings of G'")
    Ps = companions4(Hed, b, c)
    assert len(Ps) == 1
    P = Ps[0]
    X, Y = companion_sets(P)
    ends = []
    for (h, x_out, W) in ((b, P[1], X), (c, P[3], Y)):
        assert len(nbG[h]) == 3, "end is not a degree-3 hub"
        ell, path = chain_to_weld(Hed, W, h, x_out)
        assert ell == 5, "not on the ell_min = 5 stratum"
        ends.append((h, x_out, path))
    full_pkg = {b: 0, c: 0}
    per_col = []
    for ci, col in enumerate(cols):
        EA = [e for e in Gp if col[e] == 'A']
        EB = [e for e in Gp if col[e] == 'B']
        compA = components(allverts, EA)
        compB = components(allverts, EB)
        if not legality_free(col, compA, compB, allverts, chn):
            per_col.append((ci, 'illegal', None))
            continue
        got = build_at(Gp, allverts, col, rng)
        assert got is not None
        pt, _, _ = got
        config_asserts(Gp, allverts, pt)
        placed = {u: dehom3(pt[u]) for u in allverts}
        okw, _ = verify_pencil_witness(Gp, placed)
        assert okw
        st = stratum_at(E, Gp, placed, a, b)
        row = {'stratum': st}
        for (h, x_out, path) in ends:
            ch_edges = list(zip(path, path[1:]))
            ids_chain = line_ids(col, compA, compB, ch_edges)
            ids6 = ids_chain + line_ids(col, compA, compB, [(a, h)])
            ido = line_ids(col, compA, compB, [(h, x_out)])[0]
            chain_lines = [wedge2(pt[e[0]], pt[e[1]]) for e in ch_edges]
            rksp = rank(chain_lines)
            Dlines = chain_lines + [wedge2(pt[a], pt[h])]
            rkD = rank(Dlines)
            dD = det6(Dlines)
            C_out = wedge2(pt[h], pt[x_out])
            memb = (rank(chain_lines + [C_out]) == rksp)
            # combinatorial predictions: (FR-3) applied to Delta; span
            # membership of the outer line -- >= 3 distinct same-family
            # chain lines span that family's whole 3-space, <= 2 distinct
            # conic points contain a further conic point iff it is one of
            # them (a conic meets a line in <= 2 points)
            pred_D = crit_33(ids6)
            same = [t for t in ids_chain if t[0] == ido[0]]
            pred_memb = (len(set(same)) >= 3) or (ido in set(same))
            assert (dD != 0) == (rkD == 6)
            assert pred_D == (dD != 0), "Delta criterion mismatch"
            assert pred_memb == memb, "outer-line span criterion mismatch"
            row[h] = (rksp, dD != 0, not memb)
            if st is not None and st[1] == 1 and dD != 0 and not memb:
                full_pkg[h] += 1
        if st is not None and st[1] == 1 and \
                (row[b][1] or row[c][1]):
            full_pkg['oc8'] = full_pkg.get('oc8', 0) + 1
        per_col.append((ci, 'ok', row))
    print("\n   col  stratum(rank,dimRa)   b-end (rk5,D!=0,lam!=0)   c-end")
    for ci, tag, row in per_col:
        if tag != 'ok':
            print(f"   {ci:>3}  {tag}")
            continue
        st = row['stratum']
        stx = f"({st[0]},{st[1]})" if st is not None else "off-target"
        print(f"   {ci:>3}  {stx:<18} {str(row[b]):<24} {str(row[c])}")
    print(f"\n   (OC-8)-LITERAL WITNESSES (target rank, dim R_a = 1, and"
          f" Delta != 0 at SOME end,")
    print(f"   i.e. L_b not in R_1 or L_c not in R_4):"
          f" {full_pkg.get('oc8', 0)} of {len(cols)} colourings")
    print(f"   STRICT availability packages (additionally lambda != 0 at"
          f" that same point):")
    print(f"     b-end: {full_pkg[b]} colourings; c-end: {full_pkg[c]}")
    print("   (every Delta/lambda verdict above is asserted equal to its")
    print("   combinatorial prediction -- the (FR-3) criterion and the")
    print("   minority-side rule -- so the witness recipe is combinatorial)")
    print("PASSED")
    return 0


# ---------------- mode: --validate ------------------------------------------

def mode_validate():
    print("== machinery pins ==")
    rng = random.Random(FR_SEED)
    print(f"   seed {FR_SEED} (mode rng)")
    # grid_point conventions ((AC-2))
    for _ in range(6):
        s, sp = F(rng.randint(2, 500)), F(rng.randint(2, 500))
        u, up = F(rng.randint(2, 500)), F(rng.randint(2, 500))
        p = grid_point((1, s), (1, u))
        q = grid_point((1, sp), (1, up))
        assert dot(p, p) == 0
        assert dot(p, q) == 2 * (g(s) - g(sp)) * (g(u) - g(up))
    print("   isotropy + the (AC-2) conjugacy law (6 draws)               OK")
    # hinge line of a same-parameter pair IS the ruling line
    p = grid_point((1, F(7)), (1, F(3)))
    q = grid_point((1, F(7)), (1, F(11)))
    assert proportional(wedge2(p, q), ruling_A_line((1, F(7))))
    p2 = grid_point((1, F(5)), (1, F(3)))
    assert proportional(wedge2(p, p2), ruling_B_line((1, F(3))))
    print("   hinge line of a conjugate pair = the shared ruling line     OK")
    # det6 vs exactcore.rank cross-check on random QQ matrices
    for _ in range(4):
        M = [[F(rng.randint(-9, 9)) for _ in range(6)] for _ in range(6)]
        assert (det6(M) != 0) == (rank(M) == 6)
    print("   det6 nonzero-ness == exactcore.rank == 6 (4 draws)          OK")
    # THE CROSS-LANGUAGE INSTANCE PIN (framedom.m2 (FR-M0) asserts the same
    # value from its own re-derivation of grid_point/wedge2 in M2):
    M = [ruling_A_line((1, F(k))) for k in (2, 3, 5)] + \
        [ruling_B_line((1, F(k))) for k in (2, 3, 5)]
    d = det6(M)
    print(f"   pinned instance det6[A(2),A(3),A(5),B(2),B(3),B(5)] = {d}")
    vdm = F((2 - 3) * (2 - 5) * (3 - 5)) ** 2
    print(f"   / Vdm(2,3,5)^2 = {d / vdm}  (the determinant-law constant c)")
    assert d == g(4608), "pinned instance moved"
    print("   pinned value 4608 (= c * 36, c = 128)                       OK")
    print("PASSED")
    return 0


# ---------------- main -------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rulings', action='store_true')
    ap.add_argument('--pattern', action='store_true')
    ap.add_argument('--transport', action='store_true')
    ap.add_argument('--outer', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.rulings:
        return mode_rulings()
    if args.pattern:
        return mode_pattern()
    if args.transport:
        return mode_transport()
    if args.outer:
        return mode_outer()
    if args.validate:
        return mode_validate()
    ap.print_help()
    return 1


if __name__ == '__main__':
    sys.exit(main())
