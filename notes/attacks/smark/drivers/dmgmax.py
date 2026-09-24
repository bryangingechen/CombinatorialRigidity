#!/usr/bin/env python3
"""dmgmax.py -- the maximum of S34(ii)'s ledger damage over ALL patterns of a big-point stratum (smark session 14, S39).

Pure combinatorics plus exact ranks of the big points: no realisation, no Jacobian.  For a hub graph Gamma
(case2m2.CASES, case2geo.HAND or GRAPHS below; marked set Z, Big = {deg_Gamma >= 3}, U_c = Big cap N[c] as LABELS,
k_c <= 3) and a point matroid on the labels drawn exactly by case2deg's --relations SPEC (same syntax, same seed rule),
it enumerates every set partition of Z whose classes have rank U_A <= 3 and every set F of flat vertices, and evaluates

    Dmg = sum_A (-T_A)^+ + k3 + sum_C (D_C - cost_C)^+ + k6/2                                    (S34(ii))

term by term as the workbook defines it:
  * class term, A a nontrivial class:  -T_A = (3 - rk U_A) + J^nb_A + (Delta_A + DeltaM_A)/2 - sum_{c in A} eps_c
    (S34(i) as written in S36), eps_c = 3 - r_c - [c in F], J^nb_A = sum over non-big y (marked or connector) of
    (|E_y cap A| - 1)^+, E_y = N_Gamma[y] (marked y) or {a, b} (connector);
    Delta_A = #{(w, b)}: w a flat singleton, N(w) = {a0, b}, a0 in A cap Big, b in Big - A, b in U_A      (normal charge);
    here and below 'w a flat singleton' with N(w) = {x, y} means a beta = 2 one: x, y big at DISTINCT points (S33:
    beta_w := rk U_w; a flat between two parallel labels has beta = 1 and forces no incidence, S26(ii));
    DeltaM_A = #{(w, y)}: w a flat singleton, N(w) = {x, y}, x in A cap Big, y in cl(U_A) - U_A        (M-natural charge);
  * k3 = #{O3 paths p - w1 - w2 - p'}: p != p' parallel labels in ONE class, w1, w2 flat singletons;
  * extras overflow, C a U-class (any class that is not a flat singleton): D_C = 1/2 #{(y, w)}: w a flat singleton,
    N(w) = {x, y}, x in C cap Big, y not in cl(U_C) (an extra of C served by w);
  * k6 = #{(w, x, y)}: w a flat singleton, N(w) = {x, y}, [x] = {x}, y in cl(U_x) - U_x  (free singleton incidence).

RELAXATIONS -- each can only raise the maximum, so the printed maximum is an UPPER BOUND on the maximum of S34(ii)'s Dmg
over realisable patterns, and 'max Dmg <= s + 1/2' on a stratum proves S34(iv) there (S32(iii): Dmg < s + 1 suffices):
  (a) flatness: y in F needs only y non-big, deg_Gamma y = 2, and [y], [a], [b] pairwise distinct (N(y) = {a, b}); no
      line structure is checked (a realisable pattern's flat set is among these);
  (b) incidence sets: P_A := cl(U_A cup {the big points forced onto pi_A by flats}) -- a flat y puts each big neighbour's
      point on all three planes of its line (S22(ii)(a)) -- a SUBSET of the true P_A; patterns with rk P_A >= 4 dropped;
  (c) cost_C >= rk P_C - rk U_C with that smaller P_C (the true sequential cost is rk W_C - rk U_C, W_C >= P_C);
  (d) k3 counts O3 paths, not lines carrying one (S33(i) charges one per line).
The class term, D_C and k6 are exact given (partition, F).  Arithmetic in half-units (Dmg2 = 2 Dmg, an integer).

Budget: s = c1 - J2 - 1 with c1 = sum of the relations' codimensions (3 / 2 / 1; exact for case2deg's constructions) and
J2 = sum_c (k_c - r_c); S34(iv)'s bound 'sum over touched components of b_R, minus 1/2' is compared as 'sum over ALL
components', which equals s + 1 (S32(ii)) -- the weaker check; on a one-component stratum they coincide.

    cd <repo>; timeout 120 python3 notes/attacks/smark/drivers/dmgmax.py --graph E13 --relations "v=u"
    timeout 3000 python3 -u notes/attacks/smark/drivers/dmgmax.py --graph E55 --relations "v=u;a=u+b"    # the test cluster
"""
import sys, os, time, itertools, argparse
from collections import defaultdict, Counter

REPO = os.environ.get("CR_REPO", os.getcwd())
DRV = os.path.join(REPO, "notes", "attacks", "smark", "drivers")
if not os.path.isfile(os.path.join(DRV, "case2deg.py")):
    sys.exit("run from the repository root (or set CR_REPO): case2deg.py not found under notes/attacks/smark/drivers")
sys.path.insert(0, DRV)
import case2geo as G                     # noqa: E402
import case2deg as CD                    # noqa: E402
from case2m2 import CASES                # noqa: E402

GRAPHS = {}   # graphs defined for this driver (none yet); same format as case2m2.CASES: (Z, edges, connectors, comment)


def set_partitions_pruned(n, ok_add):
    """restricted growth strings over 0..n-1; ok_add(classes_masks, j, v) says whether v may join class j (rank prune).
    Yields the list of class bitmasks."""
    classes = []
    def rec(v):
        if v == n:
            yield classes
            return
        bit = 1 << v
        for j in range(len(classes)):
            if ok_add(classes[j] | bit):
                classes[j] |= bit
                yield from rec(v + 1)
                classes[j] &= ~bit
        classes.append(bit)
        yield from rec(v + 1)
        classes.pop()
    yield from rec(0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", required=True)
    ap.add_argument("--relations", required=True, help="case2deg --relations syntax, e.g. 'v=u;a=u+b'")
    ap.add_argument("--seed", type=int, default=G.BASE_SEED)
    ap.add_argument("--show", type=int, default=3, help="maximising patterns printed")
    a = ap.parse_args()
    t0 = time.time()
    name = a.graph
    Z, E, conn, comment = (GRAPHS.get(name) or G.HAND.get(name) or CASES.get(name) or sys.exit(f"unknown graph {name}"))
    Z = list(Z); n = len(Z); vi = {z: i for i, z in enumerate(Z)}
    adj = G.build_graph(Z, E, conn)
    deg = {z: len(adj[z]) for z in Z}
    Big = sorted(z for z in Z if deg[z] >= 3)
    print(f"=== {name} [relations {a.relations}] ===  {comment}")
    print(f"|Z|={n} |E(Gamma)|={len(E)} connectors={len(conn)} girth={G.girth(Z, E, conn)} Big={Big}")
    rels = CD.parse_relations(a.relations, Big)
    rep, BigP, qd, coefs = CD.draw_relations(Big, rels, a.seed, "draw1")
    _, _, qd2, _ = CD.draw_relations(Big, rels, a.seed + 1, "draw2")
    bi = {x: i for i, x in enumerate(Big)}
    def pts_of(mask, q):
        return [q[rep[x]] for x in Big if mask >> bi[x] & 1]
    _rk = {}
    def rk(mask):
        if mask not in _rk:
            _rk[mask] = CD.rank_exact(pts_of(mask, qd)) if mask else 0
        return _rk[mask]
    # the matroid on labels, checked against an independent draw (all subsets of the labels of size <= 5)
    mism = [S for kk in range(1, min(5, len(Big)) + 1) for S in itertools.combinations(Big, kk)
            if rk(sum(1 << bi[x] for x in S)) != CD.rank_exact([qd2[rep[x]] for x in S])]
    assert not mism, f"matroid differs between draws: {mism}"
    _cl = {}
    def cl(mask):
        if mask not in _cl:
            r = rk(mask); _cl[mask] = mask | sum(1 << bi[x] for x in Big if rk(mask | 1 << bi[x]) == r)
        return _cl[mask]
    Ul = [sum(1 << bi[x] for x in Big if x == z or x in adj[z]) for z in Z]      # U_c as a label bitmask
    k = [bin(m).count("1") for m in Ul]
    if max(k) > 3: sys.exit(f"k_c > 3 at {[Z[i] for i in range(n) if k[i] > 3]}: outside the three-level tower")
    r = [rk(m) for m in Ul]
    J2 = sum(k[i] - r[i] for i in range(n))
    c1 = sum({1: 3, 2: 2, 3: 1}[len(ss)] for _, ss in rels)
    s = c1 - J2 - 1
    # relation components: circuits of size <= 4 among the labels
    circ = [S for kk in range(2, 5) for S in itertools.combinations(Big, kk)
            if rk(sum(1 << bi[x] for x in S)) == kk - 1 and all(rk(sum(1 << bi[x] for x in T)) == len(T) for T in itertools.combinations(S, kk - 1))]
    comp = {x: {x} for x in Big}
    for S in circ:
        m = set().union(*(comp[x] for x in S))
        for x in m: comp[x] = m
    comps = sorted({frozenset(v) for v in comp.values() if any(set(S) <= v for S in circ)}, key=sorted)
    print("labels -> points: " + ", ".join(f"{x}->{rep[x]}" for x in Big) + f";  circuits of size <= 4: {[''.join(S) for S in circ]};  components: {[sorted(R) for R in comps]}")
    print(f"c1 = {c1}  J2 = {J2}  s = c1 - J2 - 1 = {s};  S34(iv) via S32(iii): Dmg <= s + 1/2 = {s + 0.5}")
    isbig = [Z[i] in bi for i in range(n)]
    nb = [[vi[w] for w in adj[z]] for z in Z]
    # non-big hyperedges for J^nb
    Yedges = [sum(1 << vi[w] for w in adj[z] | {z}) for z in Z if deg[z] >= 1 and z not in bi]
    Yedges += [(1 << vi[x]) | (1 << vi[y]) for x, y in conn]
    cand = [i for i in range(n) if not isbig[i] and deg[Z[i]] == 2]
    # O3 candidate paths: p - w1 - w2 - p' with p != p' parallel labels, w1, w2 candidates
    o3 = []
    for p in Big:
        for p2 in Big:
            if p < p2 and rep[p] == rep[p2]:
                for w1 in adj[p]:
                    for w2 in adj[w1]:
                        if w2 != p and p2 in adj[w2] and vi[w1] in cand and vi[w2] in cand:
                            o3.append((vi[p], vi[w1], vi[w2], vi[p2]))
    print(f"flat candidates: {[Z[i] for i in cand]};  O3 candidate paths: {[tuple(Z[j] for j in P) for P in o3]}")
    lab = [1 << bi[Z[i]] if isbig[i] else 0 for i in range(n)]
    # per-class-mask cache: (UA, rkUA, clUA, Jnb, sum3r, bigmask)
    cache = {}
    def cdata(A):
        d = cache.get(A)
        if d is None:
            UA = 0; s3 = 0; bm = 0
            for i in range(n):
                if A >> i & 1:
                    UA |= Ul[i]; s3 += 3 - r[i]; bm |= lab[i]
            Jnb = sum(max(0, bin(Y & A).count("1") - 1) for Y in Yedges)
            d = (UA, rk(UA), cl(UA), Jnb, s3, bm)
            cache[A] = d
        return d
    def ok_add(A):
        return cdata(A)[1] <= 3
    best = -1; nbest = 0; shown = []; hist = Counter(); npart = 0; npat = 0; ndrop = 0
    termmax = Counter(); clsdmg = {}; mixes = Counter()
    for classes in set_partitions_pruned(n, ok_add):
        npart += 1
        cls = [0] * n
        for j, A in enumerate(classes):
            for i in range(n):
                if A >> i & 1: cls[i] = j
        single = [bin(A).count("1") == 1 for A in classes]
        fc = [y for y in cand if cls[y] != cls[nb[y][0]] and cls[y] != cls[nb[y][1]] and cls[nb[y][0]] != cls[nb[y][1]]]
        CD_ = [cdata(A) for A in classes]
        for fm in range(1 << len(fc)):
            F = [fc[t] for t in range(len(fc)) if fm >> t & 1]
            Fset = set(F)
            forced = [0] * len(classes)
            for y in F:
                x0, x1 = nb[y]
                if isbig[x0]: forced[cls[x1]] |= lab[x0]
                if isbig[x1]: forced[cls[x0]] |= lab[x1]
            PA = [cl(CD_[j][0] | forced[j]) for j in range(len(classes))]
            if any(rk(P) > 3 for P in PA):
                ndrop += 1; continue
            npat += 1
            dlt = [0] * len(classes); dM = [0] * len(classes); Dh = [0] * len(classes); k6 = 0
            for w in F:
                if not single[cls[w]]: continue
                x0, x1 = nb[w]
                if not (isbig[x0] and isbig[x1]) or rk(lab[x0] | lab[x1]) < 2: continue     # beta_w = rk U_w = 2 only (S33)
                for x, y in ((x0, x1), (x1, x0)):
                    j = cls[x]; UA, _, clUA, _, _, _ = CD_[j]; ly = lab[y]
                    if single[j]:
                        assert not UA & ly, "normal incidence on a singleton: a triangle"
                        if clUA & ly: k6 += 1
                        else: Dh[j] += 1
                    else:
                        if UA & ly: dlt[j] += 1
                        elif clUA & ly: dM[j] += 1
                        else: Dh[j] += 1
            cterm = 0; oterm = 0; per = []
            for j, A in enumerate(classes):
                UA, rkU, clUA, Jnb, s3, bm = CD_[j]
                isflatsing = single[j] and (A.bit_length() - 1) in Fset
                if not single[j]:
                    fA = sum(1 for i in F if A >> i & 1)
                    neg2 = 2 * (3 - rkU) + 2 * Jnb + dlt[j] + dM[j] - 2 * (s3 - fA)
                    if neg2 > 0:
                        cterm += neg2; per.append(("class", j, neg2))
                        if neg2 > clsdmg.get(A, 0): clsdmg[A] = neg2
                if not isflatsing and Dh[j]:
                    ov2 = Dh[j] - 2 * (rk(PA[j]) - rkU)
                    if ov2 > 0: oterm += ov2; per.append(("overflow", j, ov2))
            k3 = sum(1 for (p, w1, w2, p2) in o3 if cls[p] == cls[p2] and w1 in Fset and w2 in Fset and single[cls[w1]] and single[cls[w2]])
            D2 = cterm + 2 * k3 + oterm + k6
            hist[D2] += 1
            for key, v in (("class", cterm), ("k3", 2 * k3), ("overflow", oterm), ("k6", k6)):
                if v > termmax[key]: termmax[key] = v
            if D2 > best:
                best = D2; nbest = 0; shown = []; mixes = Counter()
            if D2 == best:
                nbest += 1; mixes[(cterm, 2 * k3, oterm, k6)] += 1
                if len(shown) < a.show:
                    desc = " | ".join("{" + ",".join(Z[i] for i in range(n) if A >> i & 1) + "}" for A in classes if bin(A).count("1") > 1)
                    shown.append(f"nontrivial classes: {desc or '-'};  flats: {[Z[i] for i in F]};  class={cterm/2} k3={k3} overflow={oterm/2} k6/2={k6/2};  "
                                 f"units: {[(t, '{' + ','.join(Z[i] for i in range(n) if classes[j] >> i & 1) + '}', v / 2) for t, j, v in per]}")
    el = time.time() - t0
    print(f"partitions (rank U_A <= 3): {npart};  patterns (partition, F) evaluated: {npat};  dropped (some rk P_A >= 4): {ndrop};  {el:.1f}s")
    print("histogram of Dmg over patterns: " + ", ".join(f"{d/2}: {c}" for d, c in sorted(hist.items())))
    print("max of each term over patterns: " + ", ".join(f"{kk}={v/2}" for kk, v in termmax.items()))
    top = sorted(clsdmg.items(), key=lambda kv: -kv[1])[:12]
    print("classes with positive class term (max over patterns): " + (", ".join("{" + ",".join(Z[i] for i in range(n) if A >> i & 1) + f"}}:{v/2}" for A, v in top) or "none"))
    print(f"MAX Dmg = {best/2}  (attained by {nbest} patterns);  bound s + 1/2 = {s + 0.5}  ->  {'PASS: S34(iv) holds on this stratum' if best <= 2 * s + 1 else '** EXCEEDS: inspect the maximisers (upper bound; relaxations (a)-(d)) **'}")
    print("maximisers by (class, k3, overflow, k6/2): " + ", ".join(f"({c/2}, {k/2}, {o/2}, {x/2}): {m}" for (c, k, o, x), m in sorted(mixes.items())))
    for t in shown: print("  max: " + t)


if __name__ == "__main__":
    main()
