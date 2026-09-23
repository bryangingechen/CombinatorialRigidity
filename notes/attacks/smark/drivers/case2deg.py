#!/usr/bin/env python3
"""
case2deg.py -- (star_2) on the single-relation stratum q_u = q_{u'} of a Case-2 hub graph (helper, 2026-09-23).

Builds on case2geo.py (imported, not modified) and case2m2.CASES.  Setting: hub graph Gamma on the marked set Z with
connectors; Big = {c : deg_Gamma c >= 3}; U_c = {q_x : x in Big cap N[c]} as a POINT set, k_c = |Big cap N[c]| <= 3,
r_c = rank_q(U_c).  Big points: exact random integers in [-30, 30] for Big' := Big with u' identified with u
(q_{u'} := q_u), in general position (every set of <= 4 distinct points independent) -- so the coincidence is the ONLY
relation.  Everything downstream (U_c, U_A, P_A, I(l), X_A) is a set of POINT labels in Big'.

Tower (S21(ii)): level 1 the big points, level 2 the planes pi_c in P(U_c^perp) (dim 3 - r_c), level 3 the other
points p_y in the intersection of the planes over E_y (marked non-big y: E_y = N[y]; connector between a, b: {a, b}).
J2 = sum_c (k_c - r_c);  J3 = sum_{y not big} (s_y - rk_y), rk_y read off the pattern (distinct classes at y, minus 1
if three distinct classes at y are on one line).  Pattern (C, L, I) as in S22(i) / case2geo, on points.
Merge codimension M_q = sum_c (3 - r_c) - sum_A (3 - rank_q U_A) (class realisable only if rank_q U_A <= 3);
rho = Jacobian rank (mod 2^61 - 1, <= the Q-rank) of the collinearity minors and extra-incidence equations in
coordinates on prod_A P(U_A^perp) at an exactly verified realisation over Q (case2geo.compute_rho).
codim_T Sigma = lev1 + M_q + rho with lev1 = 3 (the level-1 codimension of {q_u = q_{u'}}), and

        slack := lev1 + M_q + rho - J2 - J3 - 1 = K + M_q + rho - J3,   K := lev1 - J2 - 1.

Every pattern counts (the stratum is already non-generic).  --generic: lev1 = 0, no coincidence, only patterns with
J3 >= 1 (exactly case2geo's check; the sanity control).  Also recorded per pattern: the class discount
D = sum_A [def_q(U_A) - sum_{c in A} def_q(U_c)] with def_q(U) = |U as labels| - rank_q(U) (so D = M_lab - M_q), and
"sees both" = some class has both u and u' among its labels U_A^lab.

SOUND SHORTCUTS (all patterns not realised have slack >= N + 1, N = --slack-cap, default 1; N = 0 is case2geo's regime):
 (S1) partition level: J3 <= J3_max := Jfix + #{hyperedges with three distinct classes}, so slack >= K + M_q - J3_max
      for every line structure; if that is >= N + 1 nothing of the partition is enumerated.
 (S2) per line structure the lower bound lb := K + M_q - J3 (rho >= 0), refined by (S3)-(S4); a structure is
      realised only if lb + rho_lb <= N.
 (S3) rank argument, extras: the Jacobian row of an extra x in X_A is the constant functional n_A . q_x on U_A^perp,
      in the class's own coordinate block; the extras' rows have rank sum_A |X_A| because U_A cup X_A = P_A is <= 3
      points in general position.  Lines: a line all of whose classes' planes are distinct and collinear on lambda has
      a nonzero row (in the block of a class A with U_A^perp not inside lambda^perp, i.e. lambda not inside span U_A)
      unless every class on it satisfies lambda inside span(U_A): for |U_A| <= 2 this means |U_A| = 2 and lambda =
      line(U_A), and a class with |U_A| = 3 has no perturbation directions.  Hence a line is "auto" (rho-free) iff its
      classes contain a common pair (which is then I(l)) -- with |Big'| <= 3 exactly case2geo's rho = 0 criterion --
      and every non-auto line has a nonzero row at EVERY point of the stratum.  (|Big'| > 3 forces --realise-all.)
 (S4) matching bound: the rows of a line lie in the blocks of its classes, so pairwise class-disjoint non-auto lines
      have rows with disjoint supports: rho >= nu := the maximum number of pairwise disjoint non-auto lines.  Hence
      rho_lb := max(sum_A |X_A|, nu), valid at every point.  nu is monotone under adding lines and J3 is bounded by
      the triples still coverable, so the line enumeration prunes a branch as soon as K + M_q - J3_reachable + nu >= N + 1.
 (S5) sequential codimension (S22(i), valid globally): placing the classes in any order, class A's fibre lies in
      P(W_A^perp), W_A := span(P_A cup determined lines through A) (a line is determined once two of its classes are
      placed), so codim S_P >= LC := sum_A (dim W_A - |U_A|) for EVERY order; dim W_A = |P_A| (no determined line),
      2 + [P_A not inside I(l)] (one), 3 (two or more).  The I-independent minimum over I is used inside the line
      enumeration (0 / max(0, 2 - |U_A|) / 3 - |U_A|), the exact I-dependent value at the I level; the order is chosen
      greedily plus a few random orders (any order is sound).  LC is monotone under adding lines, so it prunes like nu.
      rho_lb := max(sum_A |X_A|, nu, LC).
 (S6) pruned partition search (|Z| >= 10 by default, --full-partitions disables): classes are built element by element;
      the merge cost of the assigned elements is monotone under further assignment (adding c to a class costs
      3 - r_c + rank(U_A cup U_c) - rank(U_A) >= 0), and J3_max = T3 + C1 with T3 := #{y : s_y = 3} and C1 := #{y : E_y
      inside one class} <= #{y : the assigned members of E_y lie in <= 1 class}; a partial assignment with
      K + M_q(partial) - T3 - C1_upper >= N + 1 (or a class of rank 4) is cut.  Only the visited partitions are counted.
 (R2) extras arise only through the lines' I(l) (case2geo's enumeration; S22(i) (R2)): an extra on a class lying on
      none of the class's lines adds one constant independent Jacobian row and no jump, so that pattern's slack is the
      reduced pattern's slack + 1 at the same line configuration; never the minimum.  With |Big'| = 1 the only such
      extra is q_u on a class with U_A = empty (D4: the class {r}).
The empty line structure of a partition is the lineless pattern: rho = 0, slack = K + M_q - Jfix exactly (if it
exists: no three classes sharing a pair of points, no two classes with the same three points); its values are
tabulated for EVERY partition (histograms by D and "sees both") and combined with the realised minima.

Family filters (statistics over the REALISED patterns, i.e. those with slack possibly <= N): --fam SPEC, repeatable, SPEC a
';'-joined conjunction of flat=y1,y2 (all listed non-big vertices flat: three distinct classes at y on one line),
singleton (the flat vertices are singleton classes), merge=a,b (a, b in one class), extra=a:x (the class of a has the
point q_x as an extra), badpair (some class {y1, y2}: non-adjacent non-big vertices with exactly one common neighbour,
both flat).  --probe realises ONE
hand-specified pattern exactly and prints M_q, rho, J3, D, LC and slack:
    --probe 'merge=u,v;line=u,w1,w2:u'        (merge=<vertices in one class>; line=<one member per class>:<I points>; extra=<vertex>:<point>)

--collinear A B D (scratch extension, 2026-09-23): the stratum where q_A, q_B, q_D are distinct and COLLINEAR on a line
lambda0 and there is no other relation: draw_collinear sets q_D := s q_A + t q_B (s, t nonzero in [-5, 5]), the other big
points random, and re-draws until rank S = min(4, |S| - [{A,B,D} inside S]) for EVERY subset S of size <= 5 (asserted).
lev1 = 2 (codim of three collinear points), J2 = sum_c (k_c - r_c) (= 1 per star centre c with A, B, D in N[c]; the stars
are listed), K = lev1 - J2 - 1.  Point sets are FLATS of this matroid: U_A is replaced by its closure cl(U_A) (pi_A contains
all of it automatically, so no incidence cost), I(l) ranges over the flats of rank <= 2 (empty, a point, a rank-2 flat --
{A,B,D} = lambda0 is one), P_A = cl(U_A cup the I(l)) of rank <= 3, X_A = P_A - cl(U_A) (enumerate_I_flat, the closure
rules restated with ranks); realisations are verified to carry exactly the flats P_A.  M_q is rank-based as before.
Shortcuts in this mode (all KEPT, each restated with ranks and sound without general position):
 (S1), (S2), (S6): unchanged -- they use only M_q (rank-based), J3 (combinatorial) and rank monotonicity (rank 4 cut).
 (S3) extras: the extras' rows of class A are the functionals n -> n . q_x on U_A^perp, of rank exactly
      rank(P_A) - rank(U_A); blocks of distinct classes are disjoint, so rho >= sum_A (rank P_A - rank U_A) (not sum |X_A|).
      Lines: the row of a line in the block of A is zero iff U_A^perp inside lambda^perp iff lambda inside span(U_A), so a line
      is declared "possibly auto" iff every class of rank <= 2 on it has rank exactly 2 and all those rank-2 flats coincide
      (conservative: auto-declared lines get no credit); otherwise some block row is nonzero at every point.  This is valid
      for any number of big points, so the |Big'| > 3 --realise-all fallback is not applied in this mode.
 (S4) matching bound: unchanged, with the rank-form auto criterion.
 (S5) sequential codimension: |U_A| -> rank U_A, |P_A| -> rank P_A (dim W_A is a dimension of a span; the argument never
      used general position otherwise); the I-independent version uses the ranks as usize.
 (R2): unchanged (an extra outside every line of its class adds >= rank-difference >= 1 constant rows in its own block and
      no jump; enumerate_I_flat, like case2geo's, only produces extras through the I(l) and the flat closure).
--probe is not supported in this mode.  Reported additionally: COST - J3 := M_q + rho - J3 = slack - K, minimum over all
patterns and over those with a class whose LABELS U_A contain all three of A, B, D ("sees" group).

    cd <repo>; timeout 900 python3 -u notes/attacks/smark/drivers/case2deg.py --graph D3 --pair u v --budget 600
    timeout 900 python3 -u notes/attacks/smark/drivers/case2deg.py --graph D3 --generic --budget 300      # sanity control vs case2geo
"""
import sys, os, time, math, itertools, random, argparse
from collections import defaultdict

REPO = os.environ.get("CR_REPO", os.getcwd())
DRV = os.path.join(REPO, "notes", "attacks", "smark", "drivers")
if not os.path.isfile(os.path.join(DRV, "case2geo.py")):
    sys.exit("run from the repository root (or set CR_REPO): case2geo.py not found under notes/attacks/smark/drivers")
sys.path.insert(0, DRV)
import case2geo as G                     # noqa: E402
import starcheck as SC                   # noqa: E402
from case2m2 import CASES                # noqa: E402

rank_exact = SC.rank_exact
pc = lambda x: bin(x).count("1")

# --------------------------------------------------------------------------- pruned line-structure enumeration
def max_disjoint(sets):
    """maximum number of pairwise disjoint members of a small list of frozensets (exact, recursive)."""
    if not sets: return 0
    s0 = sets[0]; rest = sets[1:]
    without = max_disjoint(rest)
    with_ = 1 + max_disjoint([t for t in rest if not (t & s0)])
    return max(without, with_)

def lc_bound(q, lines, costfn, rng, tries=6):
    """sequential codimension bound (S5): max over a greedy order and `tries` random orders of sum_A costfn(A, placed);
    any order is a sound lower bound, so the max is."""
    lines = list(lines)
    if not lines: return 0
    def run(order):
        placed = set(); tot = 0
        for A in order: tot += costfn(A, placed); placed.add(A)
        return tot
    # greedy: take the most expensive class now; when everything is free, take the class that determines most lines
    placed = set(); tot = 0
    while len(placed) < q:
        rem = [A for A in range(q) if A not in placed]
        costs = {A: costfn(A, placed) for A in rem}
        mx = max(costs.values())
        if mx > 0: A = max(rem, key=lambda a: (costs[a], sum(1 for L in lines if a in L)))
        else: A = max(rem, key=lambda a: (sum(1 for L in lines if a in L and len(L & placed) == 1), sum(1 for L in lines if a in L)))
        tot += costs[A]; placed.add(A)
    best = tot
    for _ in range(tries):
        o = list(range(q)); rng.shuffle(o); best = max(best, run(o))
    return best

def lc_lines_only(q, lines, usize, rng):
    """I-independent sequential bound: cost 0 / max(0, 2 - |U_A|) / 3 - |U_A| for 0 / 1 / >= 2 determined lines."""
    def costfn(A, placed):
        det = sum(1 for L in lines if A in L and len((L - {A}) & placed) >= 2)
        return 0 if det == 0 else (max(0, 2 - usize[A]) if det == 1 else 3 - usize[A])
    return lc_bound(q, lines, costfn, rng, tries=2)

def lc_pattern(q, lines, I, UA, F, rng, rk=len):
    """exact-shape sequential bound LC(P): |X_A| / 2 + [P_A not inside I(l)] - |U_A| / 3 - |U_A|.
    rk: the rank function on point sets (len in general position; the exact rank in --collinear mode, where
    |X_A| becomes rank P_A - rank U_A and |U_A| becomes rank U_A)."""
    def costfn(A, placed):
        det = [S for L, S in zip(lines, I) if A in L and len((L - {A}) & placed) >= 2]
        if not det: return rk(F[A]) - rk(UA[A])
        if len(det) == 1: return 2 + (0 if F[A] <= det[0] else 1) - rk(UA[A])
        return 3 - rk(UA[A])
    return lc_bound(q, lines, costfn, rng)

def pls_iter_bounded(q, triples, base_lb, N, is_auto, include_empty, use_nu=True, usize=None, rng=None, early_cut=False):
    """Partial linear spaces on classes 0..q-1 (lines of size >= 3, pairwise meeting in <= 1 class).  Yields
    (lines, ncov, nu): ncov = number of the given triples covered by a line (J3 = Jfix + ncov), nu = maximum number of
    pairwise disjoint non-auto lines (is_auto(cand) says whether a candidate line is auto, S3).  A non-empty
    structure is yielded iff base_lb - ncov + nu <= N (slack may be <= N); the empty structure iff include_empty.
    nu here is max(matching bound S4, I-independent sequential bound S5) when usize is given.
    Sound pruning (S4/S5): candidates covering a triple are ordered first; at a node the coverable triples are the covered
    ones plus those of the still-available compatible covering candidates (OR-ed without checking their mutual
    compatibility: an over-estimate), and nu is non-decreasing, so a branch is cut when
    base_lb - #coverable + nu >= N + 1.  use_nu=False drops nu from both tests (--realise-all)."""
    if base_lb - len(triples) >= N + 1:              # nothing non-empty can qualify (S1); the caller does not get here
        if include_empty: yield (), 0, 0
        return
    cands = [frozenset(s) for k in range(3, q + 1) for s in itertools.combinations(range(q), k)]
    tri = [frozenset(t) for t in triples]
    cov = [sum(1 << i for i, t in enumerate(tri) if t <= c) for c in cands]
    order = sorted(range(len(cands)), key=lambda j: (cov[j] == 0, j))
    cands = [cands[j] for j in order]; cov = [cov[j] for j in order]
    n = len(cands); m = sum(1 for x in cov if x)
    auto = [is_auto(c) for c in cands]
    masks = [sum(1 << x for x in c) for c in cands]
    rows = {}
    def row(i):                                  # bitmask over j of the candidates compatible with candidate i
        rr = rows.get(i)
        if rr is None:
            mi = masks[i]; rr = 0
            for j in range(n):
                t = mi & masks[j]
                if t & (t - 1) == 0: rr |= 1 << j
            rows[i] = rr
        return rr
    def rec(start, chosen, covered):
        # (scratch copy) pot is computed first and the matching bound tested before the costlier sequential bound:
        # pot contains covered, so a cut by base_lb - pc(pot) + nu >= N + 1 also excludes the yield; same output.
        ok = (1 << n) - 1
        for i in chosen: ok &= row(i)
        pot = covered
        for j in range(start, m):
            if (cov[j] & ~covered) and (ok >> j) & 1: pot |= cov[j]
        nu = max_disjoint([cands[i] for i in chosen if not auto[i]]) if (use_nu and chosen) else 0
        if early_cut and chosen and base_lb - pc(pot) + nu >= N + 1: return   # --collinear only (generic/pair: original rng stream)
        if use_nu and chosen and usize is not None:
            nu = max(nu, lc_lines_only(q, [cands[i] for i in chosen], usize, rng))
        if chosen:
            if base_lb - pc(covered) + nu <= N: yield tuple(cands[i] for i in chosen), pc(covered), nu
        elif include_empty:
            yield (), 0, 0
        if base_lb - pc(pot) + nu >= N + 1: return
        for j in range(start, n):
            if (ok >> j) & 1:
                chosen.append(j)
                yield from rec(j + 1, chosen, covered | cov[j])
                chosen.pop()
    yield from rec(0, [], 0)

# --------------------------------------------------------------------------- pruned partition search (S6)
def partitions_pruned(Zs, Upt, r, rank_pts, Y, T3, K, N, deadline, stats):
    """DFS over the set partitions of Zs; cuts a partial assignment when K + M_q(partial) - T3 - C1_upper >= N + 1 or a
    class has rank 4 (docstring S6).  Yields partitions as lists of tuples (same shape as starcheck.set_partitions)."""
    n = len(Zs)
    hyper_of = {z: [i for i, (_, E) in enumerate(Y) if z in E] for z in Zs}
    blocks = []; bpts = []; M = [0]
    touched = [set() for _ in Y]
    def c1_upper(): return sum(1 for t in touched if len(t) <= 1)
    def rec(i):
        if i == n:
            yield [tuple(b) for b in blocks]; return
        if (stats["nodes"] & 4095) == 0 and time.time() > deadline: stats["capped"] = True; return
        z = Zs[i]
        for bi in range(len(blocks)):
            newpts = bpts[bi] | Upt[z]
            rk_new = rank_pts(newpts)
            if rk_new > 3: stats["rank4"] += 1; continue
            dM = 3 - r[z] + rk_new - rank_pts(bpts[bi])
            blocks[bi].append(z); old = bpts[bi]; bpts[bi] = newpts; M[0] += dM
            added = [yi for yi in hyper_of[z] if bi not in touched[yi]]
            for yi in added: touched[yi].add(bi)
            stats["nodes"] += 1
            if K + M[0] - T3 - c1_upper() <= N: yield from rec(i + 1)
            else: stats["pruned"] += 1
            for yi in added: touched[yi].discard(bi)
            blocks[bi].pop(); bpts[bi] = old; M[0] -= dM
        blocks.append([z]); bpts.append(Upt[z]); bi = len(blocks) - 1
        for yi in hyper_of[z]: touched[yi].add(bi)
        stats["nodes"] += 1
        if K + M[0] - T3 - c1_upper() <= N: yield from rec(i + 1)
        else: stats["pruned"] += 1
        for yi in hyper_of[z]: touched[yi].discard(bi)
        blocks.pop(); bpts.pop()
    yield from rec(0)

# --------------------------------------------------------------------------- flat-aware I enumeration (--collinear)
def enumerate_I_flat(UA, lines, Big, rank, cl, flats2):
    """case2geo.enumerate_I with the matroid of the big points in place of general position: UA[A] closed flats,
    I(l) ranges over the flats of rank <= 2 (the big points on a geometric line), P_A = F[A] := cl(U_A cup I(l) ...)
    of rank <= 3, and the closure rules restated with ranks: two classes on l meet exactly in I(l); two lines with
    the same rank-2 flat coincide; two classes with the same rank-3 flat have the same plane; >= 3 classes whose P
    contain a rank-2 flat P lie on one line of the structure, and a line with I(l) = P contains all of them."""
    q = len(UA); lines = list(lines)
    small = [frozenset()] + [frozenset([x]) for x in Big] + list(flats2)
    opts = []
    for L in lines:
        base = set()
        for B, C in itertools.combinations(sorted(L), 2):
            base |= UA[B] & UA[C]
        base = cl(base)
        if rank(base) > 2: return [], 0
        o = [S for S in small if base <= S and all(rank(UA[A] | S) <= 3 for A in L)]
        if not o: return [], 0
        opts.append(o)
    valid = []; pruned = 0
    # backtracking over the lines (the two monotone rules -- rank P_A <= 3 and P_B cap P_C = I(l) on the lines already
    # assigned -- can only fail more as further lines add points, so a violated partial assignment is cut; the cut
    # completions are not counted in `pruned`)
    def partial_ok(Fp, done):
        if any(rank(Fp[A]) > 3 for A in range(q)): return False
        for L, S in done:
            for B, C in itertools.combinations(sorted(L), 2):
                if (Fp[B] & Fp[C]) != S: return False
        return True
    def gen(i, Fp, chosen):
        if i == len(lines): yield tuple(chosen); return
        for S in opts[i]:
            Fn = list(Fp)
            for A in lines[i]: Fn[A] = cl(Fn[A] | S)
            chosen.append(S)
            if partial_ok(Fn, list(zip(lines, chosen))): yield from gen(i + 1, Fn, chosen)
            chosen.pop()
    for I in gen(0, [frozenset(u) for u in UA], []):
        F = [set(UA[A]) for A in range(q)]
        for L, S in zip(lines, I):
            for A in L: F[A] |= S
        F = [cl(f) for f in F]
        if any(rank(f) > 3 for f in F): pruned += 1; continue
        ok = True
        for L, S in zip(lines, I):
            for B, C in itertools.combinations(sorted(L), 2):
                if (F[B] & F[C]) != S: ok = False; break
            if not ok: break
        if ok:
            for (L1, S1), (L2, S2) in itertools.combinations(zip(lines, I), 2):
                if rank(S1) == 2 and S1 == S2: ok = False; break
        if ok:
            for A, B in itertools.combinations(range(q), 2):
                if rank(F[A]) == 3 and F[A] == F[B]: ok = False; break
        if ok:
            for P in flats2:
                SP = [A for A in range(q) if P <= F[A]]
                if len(SP) >= 3 and not any(set(SP) <= L for L in lines): ok = False; break
                for L, S in zip(lines, I):
                    if S == P and not set(SP) <= L: ok = False; break
                if not ok: break
        if not ok: pruned += 1; continue
        X = tuple(frozenset(F[A] - UA[A]) for A in range(q))
        valid.append((tuple(I), X, tuple(frozenset(f) for f in F)))
    return valid, pruned

# --------------------------------------------------------------------------- descriptions
def fmt_set(S): return "{" + ",".join(S) + "}"

def canon(part, lines, I, X, auts, rep):
    """canonical (under the automorphisms fixing the pair) tuple: classes, lines with I, extras per class."""
    best = None
    for s in auts:
        blocks = [tuple(sorted(s[z] for z in b)) for b in part]
        cl = tuple(sorted(blocks))
        ls = tuple(sorted((tuple(sorted(blocks[c] for c in L)), tuple(sorted(rep[s[x]] for x in S))) for L, S in zip(lines, I)))
        xs = tuple(sorted((blocks[A], tuple(sorted(rep[s[x]] for x in X[A]))) for A in range(len(part)) if X[A]))
        key = (cl, ls, xs)
        if best is None or key < best: best = key
    return best

def desc_of(key):
    cl, ls, xs = key
    s = "classes " + " ".join(fmt_set(b) for b in cl if len(b) >= 2)
    if not any(len(b) >= 2 for b in cl): s = "classes all singletons"
    s += " ; lines " + ("; ".join("[" + " | ".join(fmt_set(b) for b in L) + "] I=" + fmt_set(S) for L, S in ls) or "(none)")
    if xs: s += " ; extras " + ", ".join(f"X({fmt_set(b)})={fmt_set(x)}" for b, x in xs)
    return s

# --------------------------------------------------------------------------- families and probes
def family_predicates(specs, Z, adj, Big, rep):
    """each spec 'merge=a,b;flat=y1,y2;singleton;extra=a:x;badpair' -> (description, predicate on (part, lines, I, X, Y))."""
    def cls_of(part):
        return {z: i for i, b in enumerate(part) for z in b}
    def flat(y, part, lines, Y):
        Ey = next((E for yy, E in Y if yy == y), None)
        if Ey is None or len(Ey) != 3: return False
        c = cls_of(part); C = frozenset(c[z] for z in Ey)
        return len(C) == 3 and any(C <= L for L in lines)
    out = []
    for spec in specs or []:
        conds = []; desc = []; singleton = "singleton" in [t.strip() for t in spec.split(";")]
        for item in spec.split(";"):
            item = item.strip()
            if not item or item == "singleton": continue
            key, _, val = item.partition("=")
            if key == "flat":
                ys = val.split(","); desc.append(f"flat {ys}" + (" as singleton classes" if singleton else ""))
                conds.append(lambda part, lines, I, X, Y, ys=ys, sg=singleton: all(flat(y, part, lines, Y) for y in ys) and
                             (not sg or all(len(part[cls_of(part)[y]]) == 1 for y in ys)))
            elif key == "merge":
                a, b = val.split(","); desc.append(f"[{a}] = [{b}]")
                conds.append(lambda part, lines, I, X, Y, a=a, b=b: cls_of(part)[a] == cls_of(part)[b])
            elif key == "extra":
                a, x = val.split(":"); desc.append(f"q_{x} extra on the class of {a}")
                conds.append(lambda part, lines, I, X, Y, a=a, x=x: rep[x] in X[cls_of(part)[a]])
            elif key == "badpair":
                desc.append("some class {y1,y2}: non-adjacent non-big, one common neighbour, both flat")
                def f_bad(part, lines, I, X, Y):
                    for b in part:
                        if len(b) != 2: continue
                        y1, y2 = b
                        if y1 in Big or y2 in Big or y2 in adj[y1] or len(adj[y1] & adj[y2]) != 1: continue
                        if flat(y1, part, lines, Y) and flat(y2, part, lines, Y): return True
                    return False
                conds.append(f_bad)
            else: sys.exit(f"unknown family key {key}")
        out.append((" AND ".join(desc), lambda part, lines, I, X, Y, conds=conds: all(c(part, lines, I, X, Y) for c in conds)))
    return out

def probe(spec, name, tag, Z, adj, Big, BigP, rep, Ulab, Upt, r, k, K, J2, Y, Ynames, ident, qpts, idx, rank_pts, args, lcrng):
    """realise one hand-specified pattern exactly and print its numbers."""
    merges = []; plines = []; extras = []
    for item in spec.split(";"):
        item = item.strip()
        if not item: continue
        key, val = item.split("=", 1)
        if key == "merge": merges.append(val.split(","))
        elif key == "line":
            mem, Ipts = val.split(":") if ":" in val else (val, "")
            plines.append((mem.split(","), [x for x in Ipts.split(",") if x]))
        elif key == "extra":
            a, x = val.split(":"); extras.append((a, x))
    blocks = []; seen = set()
    for m in merges:
        blocks.append(tuple(m)); seen |= set(m)
    for z in Z:
        if z not in seen: blocks.append((z,))
    part = blocks; q = len(part); cls = {z: i for i, b in enumerate(part) for z in b}
    UA = [frozenset().union(*(Upt[c] for c in b)) for b in part]
    UAlab = [frozenset().union(*(Ulab[c] for c in b)) for b in part]
    rkA = [rank_pts(uA) for uA in UA]
    print(f"PROBE {name} [{tag}]: classes {[list(b) for b in part]}")
    if any(x > 3 for x in rkA): print("  unrealisable: a class needs a plane through 4 independent points"); return None
    M = sum(3 - r[c] for c in Z) - sum(3 - x for x in rkA)
    u, u2 = (None, None) if "GENERIC" in tag else tag.replace("q_", "").split(" = ")
    defA = [0 if u is None else int(u in lab and u2 in lab) for lab in UAlab]
    D = sum(defA) - J2; sees = any(defA)
    lines = [frozenset(cls[m] for m in mem) for mem, _ in plines]
    I = [frozenset(rep[x] for x in Ipts) for _, Ipts in plines]
    F = [set(uA) for uA in UA]
    for L, S in zip(lines, I):
        for A in L: F[A] |= S
    for a, x in extras: F[cls[a]].add(rep[x])
    F = [frozenset(f) for f in F]; X = [F[A] - UA[A] for A in range(q)]
    # consistency (S22(i)): two classes on a line share exactly I(l); |I| <= 2; |P_A| <= 3
    ok = all(len(f) <= 3 for f in F) and all(len(S) <= 2 for S in I)
    for L, S in zip(lines, I):
        for B, C in itertools.combinations(sorted(L), 2):
            if F[B] & F[C] != S: ok = False
    if not ok: print("  pattern violates the consistency rules (P_B cap P_C = I(l), |I| <= 2, |P_A| <= 3)"); return None
    hc = [(len(Ey), frozenset(cls[z] for z in Ey)) for _, Ey in Y]
    jumps = tuple(s - (1 if len(C) == 1 else (2 if len(C) == 2 or any(C <= L for L in lines) else 3)) for s, C in hc)
    J3 = sum(jumps)
    lc = lc_pattern(q, lines, I, UA, F, lcrng) if lines else sum(len(x) for x in X)
    nu = max_disjoint([L for L in lines if len(frozenset.intersection(*(UA[A] for A in L))) < 2])
    info = G.compute_rho(q, lines, UA, X, F, BigP, qpts, args.seed, args.order_cap, args.nsucc, q <= 6, time.time() + args.budget)
    print(f"  M_q={M} J2={J2} J3={J3} jumps={ {Ynames(y, ident): j for (y, _), j in zip(Y, jumps) if j} } D={D} sees_both={sees}  bounds: LC={lc} nu={nu} sum|X|={sum(len(x) for x in X)}")
    if info["status"] != "ok":
        print(f"  NOT REALISED ({info.get('reason', 'orders exhausted')}, {info['tried']} orders); slack >= K + M_q + max(LC, nu) - J3 = {K + M + max(lc, nu) - J3}"); return None
    rho = info["rho_min"]; slack = K + M + rho - J3
    print(f"  realised: rho={rho} (min over {info['nsucc']} realisations, max {info['rho_max']});  slack = K + M_q + rho - J3 = {K} + {M} + {rho} - {J3} = {slack}")
    print("  normals: " + ", ".join(f"{list(part[A])}:{info['pts'][A]}" for A in range(q)))
    return dict(slack=slack, M=M, rho=rho, J3=J3, D=D)

# --------------------------------------------------------------------------- the check
def draw_collinear(BigP, trip, seed):
    """exact integer big points with q_D = s q_A + t q_B (s, t nonzero integers), the others random in [-30, 30];
    redrawn until the collinearity of trip is the ONLY relation: rank S = min(4, |S| - [trip inside S]) for every
    subset S of size <= 5."""
    A, B, D = trip
    rng = random.Random(f"{seed}:collinear:{','.join(trip)}")
    nz = [x for x in range(-5, 6) if x]
    while True:
        pts = {x: [rng.randint(-30, 30) for _ in range(4)] for x in BigP}
        s_, t_ = rng.choice(nz), rng.choice(nz)
        pts[D] = [s_ * a + t_ * b for a, b in zip(pts[A], pts[B])]
        ok = all(rank_exact([pts[x] for x in S]) == min(4, len(S) - (1 if set(trip) <= set(S) else 0))
                 for kk in range(1, min(5, len(BigP)) + 1) for S in itertools.combinations(BigP, kk))
        if ok: return [pts[x] for x in BigP], (s_, t_)

def analyse(name, pair, args, coll=None):
    t0 = time.time(); deadline = t0 + args.budget
    if name in G.HAND: Z, E, conn, comment = G.HAND[name]
    else: Z, E, conn, comment = CASES[name]
    generic = pair is None and coll is None
    tag = "GENERIC (control)" if generic else (f"q_{coll[0]}, q_{coll[1]}, q_{coll[2]} collinear" if coll else f"q_{pair[0]} = q_{pair[1]}")
    print(f"\n=== {name}  [{tag}] ===  {comment}")
    adj = G.build_graph(Z, E, conn)
    deg = {z: len(adj[z]) for z in Z}
    Big = sorted(z for z in Z if deg[z] >= 3)
    print(f"|Z|={len(Z)} |E(Gamma)|={len(E)} connectors={len(conn)} girth={G.girth(Z, E, conn)}  Big={Big}" +
          (f"  (isolated marked vertices: {[z for z in Z if deg[z] == 0]})" if any(deg[z] == 0 for z in Z) else ""))
    if generic or coll:
        u = u2 = None; rep = {x: x for x in Big}; BigP = list(Big); adjacent = False
        if coll and (len(set(coll)) != 3 or any(x not in Big for x in coll)):
            print(f"SKIPPED: {coll} is not a triple of distinct big vertices"); return None
    else:
        u, u2 = pair
        if u not in Big or u2 not in Big or u == u2: print(f"SKIPPED: pair {pair} is not a pair of distinct big vertices"); return None
        rep = {x: x for x in Big}; rep[u2] = u; BigP = [x for x in Big if x != u2]
        adjacent = u2 in adj[u]
        dist = {u: 0}; frontier = [u]
        while frontier and u2 not in dist:
            nf = []
            for x in frontier:
                for w in adj[x]:
                    if w not in dist: dist[w] = dist[x] + 1; nf.append(w)
            frontier = nf
        print(f"pair ({u}, {u2}): Gamma-distance {dist.get(u2, 'inf')}" + ("  ** ADJACENT: the stratum lies OUTSIDE the adjacent-distinct locus (adjacent marked points must be distinct) **" if adjacent else ""))
    Ulab = {c: frozenset(x for x in Big if x == c or x in adj[c]) for c in Z}
    Upt = {c: frozenset(rep[x] for x in Ulab[c]) for c in Z}
    k = {c: len(Ulab[c]) for c in Z}
    if max(k.values()) > 3:
        print(f"SKIPPED: k_c > 3 at {[c for c in Z if k[c] > 3]}"); return None
    if len(BigP) > 3 and not args.realise_all and not coll:
        print("NOTE: |Big'| > 3: the auto-line criterion assumes |Big'| <= 3; forcing --realise-all"); args.realise_all = True
    if coll:
        qpts, st = draw_collinear(BigP, coll, args.seed)
    else:
        qpts = G.draw_points(len(BigP), args.seed)
    idx = {x: i for i, x in enumerate(BigP)}
    _rk = {}
    def rank_pts(S):
        S = frozenset(S)
        if S not in _rk: _rk[S] = rank_exact([qpts[idx[x]] for x in S]) if S else 0
        return _rk[S]
    _cl = {}
    def cl(S):
        S = frozenset(S)
        if S not in _cl:
            rS = rank_pts(S); _cl[S] = frozenset(x for x in BigP if x in S or rank_pts(S | {x}) == rS)
        return _cl[S]
    flats2 = sorted({cl(P) for P in itertools.combinations(BigP, 2)}, key=sorted)
    if coll:
        print("big points: " + ", ".join(f"q_{x}={qpts[idx[x]]}" for x in Big) + f"   (q_{coll[2]} := {st[0]} q_{coll[0]} + {st[1]} q_{coll[1]})")
        rel_ok = all(rank_pts(S) == min(4, len(S) - (1 if set(coll) <= set(S) else 0))
                     for kk in range(1, min(5, len(BigP)) + 1) for S in itertools.combinations(BigP, kk))
        print(f"relation check (every subset S of size <= 5: rank S = min(4, |S| - [{{{','.join(coll)}}} inside S])): {rel_ok};"
              f"  the only relation is the collinearity of q_{coll[0]}, q_{coll[1]}, q_{coll[2]};  rank-2 flats: {[sorted(f) for f in flats2]}")
    else:
        print("big points: " + ", ".join(f"q_{x}={qpts[idx[rep[x]]]}" for x in Big) + (f"   (q_{u2} := q_{u})" if not generic else ""))
        rel_ok = all(rank_pts(S) == len(S) for kk in range(2, min(4, len(BigP)) + 1) for S in itertools.combinations(BigP, kk))
        print(f"general position of the {len(BigP)} distinct points (all <=4-subsets independent): {rel_ok}" +
              ("" if generic else f";  the only relation among {{q_x : x in Big}} is q_{u} = q_{u2}"))
    assert rel_ok
    r = {c: rank_pts(Upt[c]) for c in Z}
    J2 = sum(k[c] - r[c] for c in Z)
    lev1 = 0 if generic else (2 if coll else 3)
    if coll:
        stars = [c for c in Z if set(coll) <= Ulab[c]]
        print(f"STAR check: centres c with {{{','.join(coll)}}} inside N_Gamma[c]: {stars or 'none'} ({'STAR' if stars else 'star-free'} triple)")
    K = lev1 - J2 - 1
    print("k_c / r_c: " + ", ".join(f"{c}:{k[c]}/{r[c]}" for c in Z) + f"   J2 = {J2}   lev1 = {lev1}   K = lev1 - J2 - 1 = {K}")
    print(f"slack = K + M_q + rho - J3 = {K} + M_q + rho - J3;  the trivial (all-singleton, lineless) pattern has slack {K}" +
          (" -- NEGATIVE" if K < 0 and not generic else (" (the generic stratum itself, excluded)" if generic else "")))
    Y = [(y, tuple(sorted(adj[y] | {y}))) for y in Z if y not in Big and deg[y] >= 1]
    Y += [(("conn", a, b), (a, b)) for a, b in conn]
    assert all(len(Ey) <= 3 for _, Ey in Y), "some s_y > 3"
    ident = {z: z for z in Z}
    def Ynames(y, s): return f"conn({','.join(sorted((s[y[1]], s[y[2]])))})" if isinstance(y, tuple) else s[y]
    print("non-big hyperedges: " + ", ".join(f"E_{Ynames(y, ident)}={list(Ey)}" for y, Ey in Y) + f";  J3_max over all patterns <= {sum(len(Ey) - 1 for _, Ey in Y)}")
    auts = [s for s in G.automorphisms(Z, adj, conn) if generic or (coll and {s[x] for x in coll} == set(coll)) or (not coll and {s[u], s[u2]} == {u, u2})]
    print(f"|Aut(Gamma, connectors{'' if generic else ', fixing the pair setwise'})| = {len(auts)}")
    N = args.slack_cap
    Zs = list(Z)
    lcrng = random.Random(f"{args.seed}:lc")
    fams = family_predicates(args.fam, Z, adj, Big, rep)
    if args.probe is not None:
        if coll: sys.exit("--probe is not supported in --collinear mode")
        return probe(args.probe, name, tag, Z, adj, Big, BigP, rep, Ulab, Upt, r, k, K, J2, Y, Ynames, ident, qpts, idx, rank_pts, args, lcrng)
    # ---- pass 1
    cnt = defaultdict(int)
    lineless = defaultdict(int)          # (slack, D>=1, sees) -> count over partitions (exact: rho = 0)
    ll_best = {"all": None, "D": None, "sees": None}; ll_attain = {"all": defaultdict(int), "D": defaultdict(int), "sees": defaultdict(int)}
    lineless_forced = 0
    cands = []                            # (lb, part, UA, lines, J3, jumps, I, X, F, M, D, sees, nu)
    nCL = 0; nCL_counted = 0; nCL_unknown = 0; nCLI = 0; nCLI_pruned = 0; nCLI_rank = 0
    capped = False
    T3 = sum(1 for _, Ey in Y if len(Ey) == 3)
    pstats = {"nodes": 0, "pruned": 0, "rank4": 0, "capped": False}
    prune_parts = (len(Zs) >= 10 and not args.full_partitions)
    part_iter = partitions_pruned(Zs, Upt, r, rank_pts, Y, T3, K, N, deadline, pstats) if prune_parts else SC.set_partitions(Zs)
    for part in part_iter:
        if time.time() > deadline: capped = True; break
        cnt["partitions"] += 1
        q = len(part); cls = {z: i for i, b in enumerate(part) for z in b}
        UA = [frozenset().union(*(Upt[c] for c in b)) for b in part]
        UAlab = [frozenset().union(*(Ulab[c] for c in b)) for b in part]
        rkA = [rank_pts(uA) for uA in UA]
        if any(x > 3 for x in rkA): cnt["partitions with rank_q(U_A) = 4 (unrealisable)"] += 1; continue
        if coll: UA = [cl(uA) for uA in UA]          # the flat spanned: pi_A contains all of it automatically
        M = sum(3 - r[c] for c in Zs) - sum(3 - x for x in rkA)
        if coll: defA = [int(set(coll) <= lab) for lab in UAlab]     # = |U_A^lab| - rank U_A (rank <= 3 here)
        else: defA = [0 if generic else int(u in lab and u2 in lab) for lab in UAlab]
        D = sum(defA) - J2; sees = any(defA)
        hc = [(len(Ey), frozenset(cls[z] for z in Ey)) for _, Ey in Y]
        Jfix = sum(s - (1 if len(C) == 1 else 2) for s, C in hc if len(C) <= 2)
        trip = [C for s, C in hc if len(C) == 3]
        J3max = Jfix + len(trip)
        def jumps_of(lines):
            return tuple(s - (1 if len(C) == 1 else (2 if len(C) == 2 or any(C <= L for L in lines) else 3)) for s, C in hc)
        pairs_cnt = defaultdict(int)
        for uA in UA:
            for P in itertools.combinations(sorted(uA), 2): pairs_cnt[P] += 1
        fixed = [uA for uA in UA if len(uA) == 3]
        forced = any(v >= 3 for v in pairs_cnt.values()) or len(fixed) != len(set(fixed))
        if coll:
            fl_cnt = defaultdict(int)
            for uA in UA:
                for P in flats2:
                    if P <= uA: fl_cnt[P] += 1
            fixed = [uA for uA, x in zip(UA, rkA) if x == 3]
            forced = any(v >= 3 for v in fl_cnt.values()) or len(fixed) != len(set(fixed))
        if forced: lineless_forced += 1
        elif generic and (q == len(Zs) or Jfix == 0): pass     # the generic stratum / J3 = 0 lineless patterns (not checked in generic mode)
        else:
            sl = K + M - Jfix
            lineless[(sl, D >= 1, sees)] += 1
            for grp, cond in (("all", True), ("D", D >= 1), ("sees", sees)):
                if not cond: continue
                if ll_best[grp] is None or sl < ll_best[grp]: ll_best[grp] = sl; ll_attain[grp].clear()
                if sl == ll_best[grp]: ll_attain[grp][min(tuple(sorted(tuple(sorted(s[z] for z in b)) for b in part)) for s in auts)] += 1
        def is_auto(L):
            if coll:            # rank form of S3: "possibly rho-free" iff no class of rank <= 1 and <= 1 distinct rank-2 flat
                low = [A for A in L if rkA[A] <= 2]
                return all(rkA[A] == 2 for A in low) and len({UA[A] for A in low}) <= 1
            return len(frozenset.intersection(*(UA[A] for A in L))) >= 2
        if generic and J3max == 0:
            cnt["partitions with J3 == 0 identically (generic mode: nothing to check)"] += 1
            if q in G.PLS_COUNT: nCL_counted += G.PLS_COUNT[q]
            else: nCL_unknown += 1
            continue
        lb_part = K + M - J3max
        if lb_part >= N + 1:
            cnt[f"partitions with K + M_q - J3_max >= {N + 1} (every pattern slack >= {N + 1}; not enumerated)"] += 1
            if D >= 1: cnt[f"partitions with K + M_q - J3_max >= {N + 1}, of which D >= 1"] += 1
            if sees: cnt[f"partitions with K + M_q - J3_max >= {N + 1}, of which sees both"] += 1
            if q in G.PLS_COUNT: nCL_counted += G.PLS_COUNT[q]
            else: nCL_unknown += 1
            continue
        cnt["partitions enumerated"] += 1
        include_empty = (K + M - Jfix <= N) and not (generic and Jfix == 0) and not forced
        usize = list(rkA) if coll else [len(uA) for uA in UA]
        for lines, ncov, nu in pls_iter_bounded(q, trip, K + M - Jfix, N, is_auto, include_empty, use_nu=not args.realise_all, usize=usize, rng=lcrng, early_cut=bool(coll)):
            nCL += 1
            if (nCL & 1023) == 0 and time.time() > deadline: capped = True; break
            jumps = jumps_of(lines); J3 = sum(jumps)
            assert J3 == Jfix + ncov
            if generic and J3 == 0: cnt["(C,L) enumerated with J3 == 0 (generic mode: skipped)"] += 1; continue
            lb = K + M - J3
            Ilist, pruned = enumerate_I_flat(UA, lines, BigP, rank_pts, cl, flats2) if coll else G.enumerate_I(UA, lines, BigP)
            nCLI += len(Ilist) + pruned; nCLI_pruned += pruned
            if not Ilist:
                cnt["(C,L) with every I unrealisable by a closure rule or none meeting the basic constraints"] += 1; continue
            for I, X, F in Ilist:
                xr = sum(rank_pts(F[A]) - rkA[A] for A in range(q)) if coll else sum(len(x) for x in X)
                rho_lb = max(xr, nu)
                if lb + rho_lb <= N and not args.realise_all:
                    rho_lb = max(rho_lb, lc_pattern(q, lines, I, UA, F, lcrng, rk=rank_pts if coll else len))
                if lb + rho_lb >= N + 1 and not args.realise_all:
                    nCLI_rank += 1; continue
                cands.append((lb, part, UA, lines, J3, jumps, I, X, F, M, D, sees, rho_lb))
        if capped: break
    t1 = time.time() - t0
    if pstats["capped"]: capped = True
    print(f"pass 1 ({t1:.1f}s){' CAPPED' if capped else ''}: partitions {'visited' if prune_parts else 'enumerated'}={cnt['partitions']}" +
          (f" of Bell({len(Zs)}) (pruned partition search S6: {pstats['nodes']} nodes, {pstats['pruned']} cut with every completion at slack >= {N + 1}, {pstats['rank4']} rank-4 merges skipped;"
           f" the lineless histogram and the D >= 1 / sees-both lineless minima below cover the VISITED partitions only, the others have lineless slack >= {N + 1})" if prune_parts else ""))
    for key in sorted(cnt):
        if key != "partitions": print(f"  {key}: {cnt[key]}")
    print(f"  (C,L) line structures enumerated (slack possibly <= {N}): {nCL}; counted as slack >= {N + 1} without enumeration (S1): {nCL_counted}" +
          (f" (+ {nCL_unknown} partition(s) with q >= 9, #PLS not tabulated)" if nCL_unknown else "") +
          f"; pruned inside enumerated partitions (S2-S5, slack >= {N + 1}): uncounted")
    print(f"  (C,L,I) assignments: {nCLI} (of which unrealisable by closure rules {nCLI_pruned}); slack >= {N + 1} by the rank argument (S3-S5), not realised: {nCLI_rank}; to realise: {len(cands)}")
    ll_all = sorted(lineless.items())
    print(f"  lineless patterns (rho = 0, slack = K + M_q - Jfix exactly), all partitions: " +
          ", ".join(f"slack {s}: {sum(v for (ss, _, _), v in ll_all if ss == s)}" for s in sorted({s for (s, _, _), _ in ll_all})) +
          (f"; {lineless_forced} partition(s) whose lineless pattern does not exist (forced line / coincident fixed planes)" if lineless_forced else ""))
    print(f"    restricted to D >= 1: " + (", ".join(f"slack {s}: {v}" for s, v in sorted(((s, sum(vv for (ss, d, _), vv in ll_all if ss == s and d)) for s in {s for (s, d, _), _ in ll_all if d}))) or "none"))
    print(f"    restricted to sees-both: " + (", ".join(f"slack {s}: {v}" for s, v in sorted(((s, sum(vv for (ss, _, b), vv in ll_all if ss == s and b)) for s in {s for (s, _, b), _ in ll_all if b}))) or "none"))
    # ---- pass 2
    cands.sort(key=lambda t: (t[0], len(t[1])))
    memo = {}; stats = defaultdict(int)
    hist = defaultdict(int); best = {"all": None, "D": None, "sees": None}; attain = {"all": defaultdict(list), "D": defaultdict(list), "sees": defaultdict(list)}
    ex = {}; neg = []; false_alarms = 0; unreal_hist = defaultdict(int); unreal_ex = []
    n_done = 0
    fam_stats = [{"n": 0, "best": None, "attain": defaultdict(list), "ex": {}} for _ in fams]
    for lb, part, UA, lines, J3, jumps, I, X, F, M, D, sees, rho_lb in cands:
        if time.time() > deadline: break
        n_done += 1
        q = len(part)
        key = (tuple(tuple(sorted(x)) for x in UA), tuple(tuple(sorted(x)) for x in X), G.lines_key(lines))
        info = memo.get(key)
        if info is None:
            info = G.compute_rho(q, lines, UA, X, F, BigP, qpts, args.seed, args.order_cap, args.nsucc, q <= 6, deadline)
            memo[key] = info
        if info["status"] != "ok":
            stats["not realised"] += 1
            unreal_hist[(q, len(lines), tuple(sorted(len(L) for L in lines)), tuple(sorted(len(S) for S in I)), info.get("reason", "orders exhausted"))] += 1
            if len(unreal_ex) < 4: unreal_ex.append((part, G.lines_key(lines), [sorted(S) for S in I], J3, M, lb, info.get("reason", "orders exhausted")))
            continue
        stats["realised"] += 1
        rho = info["rho_min"]; slack = K + M + rho - J3
        assert rho >= rho_lb, "rank/sequential bound violated"
        if slack < 0:
            persists = True
            for s in range(1, 6):
                i2 = G.compute_rho(q, lines, UA, X, F, BigP, qpts, args.seed + s, args.order_cap, args.nsucc, q <= 6, deadline)
                if i2["status"] == "ok" and K + M + i2["rho_min"] - J3 >= 0:
                    persists = False; rho = i2["rho_min"]; slack = K + M + rho - J3; break
            if persists: neg.append((part, lines, I, X, J3, jumps, M, rho, D, info))
            else: false_alarms += 1
        hist[slack] += 1
        ck = canon(part, lines, I, X, auts, rep)
        rec = (M, rho, J3, D, sees, {Ynames(y, ident): j for (y, _), j in zip(Y, jumps) if j})
        for grp, cond in (("all", True), ("D", D >= 1), ("sees", sees)):
            if not cond: continue
            if best[grp] is None or slack < best[grp]: best[grp] = slack
            attain[grp][(slack, ck)].append(1)
        ex.setdefault((slack, ck), rec)
        for (fd, fp), fs in zip(fams, fam_stats):
            if fp(part, lines, I, X, Y):
                fs["n"] += 1
                if fs["best"] is None or slack < fs["best"]: fs["best"] = slack
                fs["attain"][(slack, ck)].append(1); fs["ex"].setdefault((slack, ck), rec)
    proc_capped = n_done < len(cands)
    anycap = capped or proc_capped
    t2 = time.time() - t0
    print(f"pass 2: realised {stats['realised']}, not realised {stats['not realised']} (patterns processed {n_done}/{len(cands)}{' CAPPED' if proc_capped else ''}); special-point false alarms resolved by reseeding: {false_alarms}")
    if hist: print("  slack histogram over realised: " + ", ".join(f"{s}: {hist[s]}" for s in sorted(hist)))
    final = {}
    for grp, label in (("all", "ALL patterns"), ("D", "patterns with D >= 1"), ("sees", "patterns with a class whose labels contain all three" if coll else "patterns that see both")):
        b = best[grp]; lb_ll = ll_best[grp]
        cands_min = [x for x in (b, lb_ll) if x is not None]
        if not cands_min:
            print(f"  minimum slack over {label}: no such pattern realised and no such lineless pattern" + ("" if anycap else f"; every such pattern has slack >= {N + 1} (S1-S4)"))
            final[grp] = None; continue
        mn = min(cands_min); final[grp] = mn
        exact = (mn <= N) and not anycap
        print(f"  minimum slack over {label}: {mn}" + ("  (EXACT: every non-realised pattern has slack >= %d)" % (N + 1) if exact else
              (f"  (= the S1-S4 lower bound {N + 1} for the non-realised patterns: exact value, attaining set possibly incomplete)" if (mn == N + 1 and not anycap) else
               ("  (CAPPED run: minimum over the processed patterns only)" if anycap else f"  (non-realised patterns have slack >= {N + 1})"))))
        if b is not None and b == mn:
            items = sorted(((ck, len(v)) for (s, ck), v in attain[grp].items() if s == b), key=lambda t: (-t[1], t[0]))
            print(f"    realised patterns attaining it: {sum(n for _, n in items)}, {len(items)} shape(s) up to the automorphisms fixing the pair:")
            for ck, n in items:
                M, rho, J3, D, sees, jd = ex[(b, ck)]
                print(f"    x{n:<4} M_q={M} rho={rho} J3={J3} D={D} sees_both={sees} jumps={jd}  {desc_of(ck)}")
        if lb_ll is not None and lb_ll == mn:
            items = sorted(ll_attain[grp].items(), key=lambda t: (-t[1], t[0]))
            print(f"    lineless patterns attaining it (exact, rho = 0; realised above only when slack <= {N}): {sum(ll_attain[grp].values())} partition(s), {len(items)} shape(s):")
            for ck, n in items[:12]:
                print(f"    x{n:<4} " + ("classes " + " ".join(fmt_set(bb) for bb in ck if len(bb) >= 2) if any(len(bb) >= 2 for bb in ck) else "classes all singletons") + " ; lines (none)")
            if len(items) > 12: print(f"    ... {len(items) - 12} more shape(s)")
    for (fd, fp), fs in zip(fams, fam_stats):
        print(f"  FAMILY [{fd}]: realised patterns in the family: {fs['n']}" +
              (f"; minimum slack among them: {fs['best']}" if fs['n'] else "") +
              (f" (family members not realised have slack >= {N + 1} by S1-S5)" if not anycap else " (CAPPED: processed subset)"))
        if fs["n"]:
            items = sorted(((ck, len(v)) for (sl, ck), v in fs["attain"].items() if sl == fs["best"]), key=lambda t: (-t[1], t[0]))
            for ck, n in items[:8]:
                M, rho, J3, D, sees, jd = fs["ex"][(fs["best"], ck)]
                print(f"    x{n:<4} M_q={M} rho={rho} J3={J3} D={D} sees_both={sees} jumps={jd}  {desc_of(ck)}")
            if len(items) > 8: print(f"    ... {len(items) - 8} more shape(s)")
    if unreal_hist:
        print("  not realised, by (q, #lines, line sizes, |I| per line, reason): " + ", ".join(f"{kk}: {v}" for kk, v in sorted(unreal_hist.items(), key=str)))
        for part, lk, I, J3, M, lb, reason in unreal_ex:
            print(f"    e.g. classes={part} lines={lk} I={I} J3={J3} M_q={M} lb={lb} {reason}")
    if neg:
        print("NEGATIVE SLACK (persisting over 6 seeds) -- FULL DETAIL:")
        for part, lines, I, X, J3, jumps, M, rho, D, info in neg:
            print(f"  classes={part}\n  lines={[sorted(L) for L in lines]} I={[sorted(S) for S in I]} X={[sorted(x) for x in X]}")
            print(f"  J2={J2} J3={J3} jumps={ {Ynames(y, ident): j for (y, _), j in zip(Y, jumps) if j} } M_q={M} rho={rho} D={D} slack={K + M + rho - J3}")
            print(f"  big points: " + ", ".join(f"q_{x}={qpts[idx[rep[x]]]}" for x in Big))
            print(f"  realisation (plane normals per class): " + ", ".join(f"{part[A]}:{info['pts'][A]}" for A in range(len(part))))
    verdict = "NEGATIVE SLACK FOUND" if neg else ("PASS" if not anycap else "PASS on processed subset (CAPPED)")
    if stats["not realised"]: verdict += f" [{stats['not realised']} not realised, unverified]"
    if adjacent: verdict += " [adjacent pair: stratum outside the adjacent-distinct locus]"
    print(f"VERDICT ({name}, {tag}): {verdict}   ({t2:.1f}s)")
    if coll:
        fa, fs_ = final.get("all"), final.get("sees")
        print(f"COST - J3 := M_q + rho - J3 = slack - K (K = {K}): minimum over all patterns {None if fa is None else fa - K}"
              f";  over patterns with a class whose labels contain all of {{{','.join(coll)}}}: {None if fs_ is None else fs_ - K}"
              f"   (patterns not realised have cost - J3 >= {N + 1 - K})")
    return dict(name=name, tag=tag, J2=J2, K=K, nCL=nCL, nCLI=nCLI, torealise=len(cands), realised=stats["realised"], unreal=stats["not realised"],
                final=final, neg=len(neg), time=t2, capped=anycap, verdict=verdict, N=N)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", required=True, help="case2m2 key or case2geo HAND key")
    ap.add_argument("--pair", nargs=2, metavar=("U", "U2"), help="the two big vertices with q_U = q_U2")
    ap.add_argument("--generic", action="store_true", help="no coincidence; case2geo's check (patterns with J3 >= 1)")
    ap.add_argument("--collinear", nargs=3, metavar=("A", "B", "D"), help="stratum: q_A, q_B, q_D distinct and collinear, no other relation")
    ap.add_argument("--budget", type=float, default=600.0, help="seconds for this graph")
    ap.add_argument("--seed", type=int, default=G.BASE_SEED)
    ap.add_argument("--order-cap", type=int, default=120)
    ap.add_argument("--nsucc", type=int, default=3)
    ap.add_argument("--slack-cap", type=int, default=1, help="realise every pattern whose lower bound allows slack <= N; the rest have slack >= N + 1")
    ap.add_argument("--realise-all", action="store_true", help="realise every enumerated (C,L,I) (disables S3-S5 at the I level and nu/LC in the enumeration)")
    ap.add_argument("--full-partitions", action="store_true", help="disable the pruned partition search (S6) even for |Z| >= 10")
    ap.add_argument("--fam", action="append", help="family spec (repeatable): 'merge=a,b;flat=y1,y2;singleton;extra=a:x;badpair'")
    ap.add_argument("--probe", help="realise one pattern: 'merge=u,v;line=u,w1,w2:u;extra=a:u'")
    args = ap.parse_args()
    if not args.generic and not args.pair and not args.collinear: sys.exit("--pair U U2, --collinear A B D or --generic required")
    print(f"case2deg.py  seed {args.seed}  budget {args.budget:.0f}s  order_cap {args.order_cap}  nsucc {args.nsucc}  slack_cap {args.slack_cap}"
          f"  realise_all={args.realise_all}  realisations exact over Q, rho mod 2^61-1;  command: {' '.join(sys.argv)}")
    res = analyse(args.graph, None if (args.generic or args.collinear) else tuple(args.pair), args,
                  coll=None if args.generic or not args.collinear else tuple(args.collinear))
    if res and args.probe is None:
        f = res["final"]
        print(f"\nSUMMARY {res['name']} [{res['tag']}]: J2={res['J2']} K={res['K']} (C,L)={res['nCL']} (C,L,I)={res['nCLI']} to_realise={res['torealise']} realised={res['realised']} "
              f"unreal={res['unreal']} min_slack={f['all']} min_slack_D>=1={f['D']} min_slack_sees={f['sees']} neg={res['neg']} {res['time']:.1f}s {res['verdict']}")

if __name__ == "__main__":
    main()
