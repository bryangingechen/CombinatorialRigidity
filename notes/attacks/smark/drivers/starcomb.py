#!/usr/bin/env python3
"""
starcomb.py -- combinatorial check of the S19 proof of (*) in Case 1 (workbook attack-smark.md S19, O7d).

(*):  for every j >= 1,  codim_B { J >= j } >= j + 1,  B = (P^3*)^Z,
      J(pi) = sum_y ( s_y - rank{ n_c : c in E_y } ),  E_y = N[y] cap Z,  s_y <= 3 (Case 1).

S19 proves (*) through the SEQUENTIAL codimension of a rank pattern P = (classes, lines):
      cost(P) = 3(|Z| - q) + LC(P),   LC = max over placement orders of sum_C min(2 d_C, 3),
d_C = number of lines through class C already determined (>= 2 earlier classes) when C is placed.
cost(P) is a sound lower bound on the codimension of P's exact stratum (relaxation + sequential
fibre count; starcheck.py lower-bounds the same codimension by a Jacobian rank instead).
The theorem is  cost(P) >= J(P) + 1  for every pattern with J >= 1, and the proof is a chain of
four inequalities.  This driver checks the CHAIN, link by link, on every pattern of every graph:

  (1) class surplus:  for each nontrivial class A,  sigma_A - F_A >= [A not a bad pair],
      sigma_A := 3(|A|-1) - J_A,  J_A = 2 e(A) + |Y_A|,  F_A = # flat members of A,
      bad pair := |A| = 2, non-adjacent, one common neighbour, both members flat;
      and the habitat-count bound |Y_A| <= 1.5(|A|-1) - 1.25 e(A).
  (2) per-line surplus on the REDUCED line (classes {[y],[a],[b]} of the flat y on it):
      surplus_l := f_l + 2 u_l - 4 >= 0,  = 0 only for type (3):  f = 2, u = 1, the two flat
      singletons adjacent, U = {A} with A nontrivial and not bad.
  (3) loss:  LC(reduced) - F_sing >= sum_{u_l <= 2} surplus_l + 2 [some u_l >= 3].
  (4) cost(reduced) - J >= S + sum_{u_l <= 2} surplus_l + 2 [some u_l >= 3]  >= 1.
plus the headline  cost(full) >= J + 1  (LC by exact DP over all orders, full line set),
and the structural facts used:  a flat vertex is flat on exactly one line; a flat singleton is
on exactly one reduced line and is never another line's neighbour class.

Population: starcheck.py's nine graphs (imported) and random habitat sides -- hub skeleton of
max degree <= 2 with edges subdivided into paths of length 1..5, pendant paths for hub degree,
optional extra marked degree-2 vertices (modelling w, v' of H') -- each verified to have
girth >= 7, unmarked degree <= 2, <= 2 marked neighbours per marked vertex, and the habitat
count 5 e(S) <= 6(|S| - 1) on EVERY nonempty vertex subset S (exact, via the 2-core's chains).

Run from the repository root:
    timeout 900 python3 notes/attacks/smark/drivers/starcomb.py [--seed 20260923] [--graphs 40] [--maxZ 7]

Caps, disclosed: |Z| <= maxZ (default 7: Bell(7) = 877 partitions x all partial linear spaces);
random sides with |V| <= 24; total 600 s.  A PASS is a check of the four links on these graphs,
not a proof; the proof is workbook S19.  Exact integer arithmetic throughout (no geometry).
"""
import sys, os, time, itertools, random, argparse
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from starcheck import set_partitions, PLS, Graph, hub_path, hub_cycle, two_paths_joined, theta, sub_K4, sub_K33  # noqa: E402

T0 = time.time()
TOTAL_CAP = 600.0

def elapsed(): return time.time() - T0

# --------------------------------------------------------------------------- habitat checks
def girth(G):
    return G.girth()

def habitat_count_ok(G):
    """max over nonempty S of 5 e(S) - 6(|S|-1), exactly.  Deleting a vertex of degree <= 1 from S
    raises the excess (by 6 - 5d), so the maximum is attained on S with min induced degree >= 2,
    i.e. inside the 2-core, and a degree-2 core vertex enters S only with both neighbours: S is a
    set T of branch vertices (core degree >= 3) plus whole chains between members of T, a chain of
    length L contributing 6 - L.  Exhaustive over T (<= 2^{#branch})."""
    core = {v: set(G.adj[v]) for v in G.adj}
    changed = True
    while changed:
        changed = False
        for v in list(core):
            if len(core[v]) <= 1:
                for w in core[v]: core[w].discard(v)
                del core[v]; changed = True
    if not core: return True, 0
    branch = [v for v in core if len(core[v]) >= 3]
    if not branch:                                     # core is a disjoint union of cycles
        n = len(core); return (6 - n <= 0 and n >= 7), 6 - n
    bidx = {v: i for i, v in enumerate(branch)}
    chains = []                                        # (i, j, L) between branch vertices
    seen = set()
    for b in branch:
        for w in core[b]:
            if (b, w) in seen: continue
            prev, cur, L = b, w, 1
            path = [(b, w)]
            while cur not in bidx:
                nxt = next(x for x in core[cur] if x != prev)
                prev, cur = cur, nxt; L += 1; path.append((prev, cur))
            seen.add((b, w)); seen.add((cur, prev))
            chains.append((bidx[b], bidx[cur], L))
    worst = 0
    for T in range(1, 1 << len(branch)):
        k = bin(T).count("1")
        exc = -6 * (k - 1) + sum(6 - L for i, j, L in chains if (T >> i & 1) and (T >> j & 1) and L <= 6)
        if exc > worst: worst = exc
        if exc > 0: return False, exc
    return True, worst

def hyperedges(G, Z):
    Zs = set(Z)
    return {y: frozenset((set(G.adj[y]) | {y}) & Zs) for y in G.adj}

def check_side(G, Z):
    """the hypotheses S19 uses; returns (ok, reason)."""
    g = girth(G)
    if g is not None and g < 7: return False, f"girth {g}"
    Zs = set(Z)
    for v in G.adj:
        if v not in Zs and len(G.adj[v]) > 2: return False, f"unmarked {v} has degree {len(G.adj[v])}"
        if v in Zs and len(G.adj[v] & Zs) > 2: return False, f"marked {v} has {len(G.adj[v] & Zs)} marked nbrs (Case 2)"
    ok, exc = habitat_count_ok(G)
    if not ok: return False, f"habitat count fails (excess {exc})"
    return True, "ok"

# --------------------------------------------------------------------------- random habitat sides
def random_side(rng, maxZ, maxV=24, tries=400):
    """hub skeleton of max degree <= 2 on k hubs, edges subdivided into paths of length 1..5,
    pendant paths to reach degree >= 3, optional extra marked degree-2 vertices."""
    for _ in range(tries):
        k = rng.randint(3, maxZ)
        hubs = [f"z{i}" for i in range(k)]
        G = Graph()
        for h in hubs: G.adj.setdefault(h, set())
        # skeleton: random paths/cycles on hubs (max degree 2), plus extra skeleton edges as paths >= 3
        order = hubs[:]; rng.shuffle(order)
        deg = {h: 0 for h in hubs}
        skel = []
        for i in range(k - 1):
            if rng.random() < 0.7:
                skel.append((order[i], order[i + 1], rng.choice([1, 1, 2, 3, 4])))
        if k >= 7 and rng.random() < 0.3:
            skel.append((order[-1], order[0], rng.choice([1, 2, 3])))
        for _ in range(rng.randint(0, 3)):
            a, b = rng.sample(hubs, 2)
            skel.append((a, b, rng.choice([2, 3, 4, 5])))
        cnt = 0; bad = False
        for a, b, L in skel:
            if L == 1:
                if deg[a] >= 2 or deg[b] >= 2 or b in G.adj[a]: continue
                G.add_edge(a, b); deg[a] += 1; deg[b] += 1
            else:
                cnt += 1
                end = G.add_path(a, L - 1, f"p{cnt}_");
                if b in G.adj[end] or end == b: bad = True; break
                G.add_edge(end, b)
        if bad: continue
        # pendant paths so every hub has degree >= 3 (length 2 keeps |V| small)
        for h in hubs:
            while len(G.adj[h]) < 3:
                cnt += 1; G.add_path(h, 2, f"q{cnt}_")
        # extra marked degree-2 vertices (w, v' of H'): at most 2, chosen among degree-2 vertices
        Z = hubs[:]
        deg2 = [v for v in G.adj if len(G.adj[v]) == 2]
        for v in rng.sample(deg2, min(len(deg2), rng.choice([0, 0, 1, 2]))):
            if len(Z) < maxZ: Z.append(v)
        if len(G.adj) > maxV: continue
        ok, why = check_side(G, Z)
        if not ok: continue
        E = hyperedges(G, Z)
        if all(len(e) <= 1 for e in E.values()): continue          # J == 0 identically, vacuous
        return G, sorted(Z, key=str)
    return None, None

# --------------------------------------------------------------------------- the check
def lc_dp(q, lines):
    """max over placement orders of sum_C min(2 d_C, 3)  (d_C = # determined lines through C)."""
    lines = [frozenset(L) for L in lines]
    full = (1 << q) - 1
    best = [None] * (1 << q); best[0] = 0
    for mask in range(1 << q):
        if best[mask] is None: continue
        for C in range(q):
            if mask >> C & 1: continue
            d = 0
            for L in lines:
                if C in L and bin(mask & sum(1 << x for x in L)).count("1") >= 2: d += 1
            c = 0 if d == 0 else min(2 * d, 3)
            nm = mask | (1 << C)
            if best[nm] is None or best[mask] + c > best[nm]: best[nm] = best[mask] + c
    return best[full]

def check_graph(name, G, Z, report):
    V = sorted(G.adj); Zs = set(Z); nZ = len(Z)
    E = hyperedges(G, Z)
    gam = {z: G.adj[z] & Zs for z in Z}                        # hub graph Gamma
    connectors = [y for y in V if y not in Zs and len(G.adj[y]) == 2 and G.adj[y] <= Zs]
    hyper = [(y, E[y]) for y in V if len(E[y]) >= 2]
    stats = dict(name=name, nZ=nZ, nV=len(V), patterns=0, withJ=0, min_full=None, min_red=None,
                 tight_full=0, tight_red=0, violations=[], link_fail=[], type3=0, bad=0, lossy=0)
    for part in set_partitions(Z):
        q = len(part)
        cls = {z: i for i, b in enumerate(part) for z in b}
        blocks = [frozenset(b) for b in part]
        for lines in PLS(q):
            stats["patterns"] += 1
            lines = [frozenset(L) for L in lines]
            # ---- J
            J = 0
            for y, e in hyper:
                C = frozenset(cls[z] for z in e); k = len(C)
                r = 1 if k == 1 else (2 if k == 2 else (2 if any(C <= L for L in lines) else 3))
                J += len(e) - r
            if J == 0: continue
            stats["withJ"] += 1
            # ---- headline: full sequential cost
            cost_full = 3 * (nZ - q) + lc_dp(q, lines)
            slack_full = cost_full - J - 1
            if stats["min_full"] is None or slack_full < stats["min_full"]: stats["min_full"] = slack_full
            if slack_full == 0: stats["tight_full"] += 1
            if slack_full < 0: stats["violations"].append(("full", part, lines, J, cost_full))
            # ---- flat vertices (three distinct collinear classes) and their unique line
            flat = {}
            for y in Z:
                nb = gam[y]
                if len(nb) != 2: continue
                a, b = sorted(nb, key=str)
                C = frozenset((cls[y], cls[a], cls[b]))
                if len(C) < 3: continue
                Ls = [L for L in lines if C <= L]
                if not Ls: continue
                if len(Ls) != 1: stats["link_fail"].append(("flat on >1 line", part, lines, y)); continue
                flat[y] = Ls[0]
            # ---- link (1): class surplus
            S = 0
            badset = set()
            for i, A in enumerate(blocks):
                m = len(A)
                if m == 1: continue
                eA = sum(len(gam[a] & A) for a in A) // 2
                YA = [y for y in V if y not in A and (y in Zs or y in connectors) and len(G.adj[y] & A) >= 2]
                JA = 2 * eA + len(YA)
                sigma = 3 * (m - 1) - JA
                FA = sum(1 for a in A if a in flat)
                bad = (m == 2 and eA == 0 and len(YA) == 1 and FA == 2)
                if bad: badset.add(i); stats["bad"] += 1
                if 4 * len(YA) > 6 * (m - 1) - 5 * eA:
                    stats["link_fail"].append(("|Y_A| bound", part, A, eA, len(YA)))
                if sigma - FA < (0 if bad else 1):
                    stats["link_fail"].append(("class surplus", part, lines, tuple(sorted(A, key=str)), sigma, FA, bad))
                S += sigma - FA
            F_sing = sum(1 for y in flat if len(blocks[cls[y]]) == 1)
            # ---- link (2): reduced lines
            red = {}
            for y, L in flat.items():
                a, b = gam[y]
                red.setdefault(L, set()).update({cls[y], cls[a], cls[b]})
            flat_single = {cls[y] for y in flat if len(blocks[cls[y]]) == 1}
            # structural: a flat singleton class is on exactly one reduced line
            for c in flat_single:
                on = [L for L, R in red.items() if c in R]
                if len(on) != 1: stats["link_fail"].append(("flat singleton on != 1 reduced line", part, lines, c))
            surplus_le2 = 0; any_u3 = False
            for L, R in red.items():
                f = len(R & flat_single); u = len(R) - f
                s = f + 2 * u - 4
                if s < 0: stats["link_fail"].append(("negative line surplus", part, lines, tuple(R)))
                if s == 0:
                    stats["type3"] += 1
                    ys = [y for y in flat if flat[y] == L and cls[y] in flat_single]
                    U = [c for c in R if c not in flat_single]
                    ok3 = (f == 2 and u == 1 and len(ys) == 2 and ys[1] in gam[ys[0]]
                           and len(blocks[U[0]]) >= 2 and U[0] not in badset)
                    if not ok3: stats["link_fail"].append(("surplus 0 but not type (3)", part, lines, tuple(R)))
                if u >= 3: any_u3 = True
                else: surplus_le2 += s
            LC_red = lc_dp(q, list(red.values())) if red else 0
            bound = surplus_le2 + (2 if any_u3 else 0)
            # ---- link (3)
            if LC_red - F_sing < bound:
                stats["link_fail"].append(("loss link", part, lines, LC_red, F_sing, bound))
            # ---- link (4)
            cost_red = 3 * (nZ - q) + LC_red
            if cost_red - J < S + bound:
                stats["link_fail"].append(("final link", part, lines, cost_red, J, S, bound))
            slack_red = cost_red - J - 1
            if stats["min_red"] is None or slack_red < stats["min_red"]: stats["min_red"] = slack_red
            if slack_red == 0: stats["tight_red"] += 1
            if slack_red < 0: stats["violations"].append(("reduced", part, lines, J, cost_red))
            if elapsed() > TOTAL_CAP: return stats, False
    return stats, True

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260923)
    ap.add_argument("--graphs", type=int, default=40)
    ap.add_argument("--maxZ", type=int, default=7)
    args = ap.parse_args()
    print(f"starcomb.py  seed {args.seed}  random sides {args.graphs}  |Z| <= {args.maxZ}  cap {TOTAL_CAP:.0f}s")
    for q in range(1, args.maxZ + 1): print(f"#PLS({q})={len(PLS(q))}", end="  ")
    print()
    pop = [(f"starcheck hub path k={k}", *hub_path(k)) for k in (3, 4, 5, 6)]
    pop += [("starcheck two hub paths joined", *two_paths_joined()), ("starcheck theta+hub", *theta()),
            ("starcheck sub K4", *sub_K4()), ("starcheck sub K33", *sub_K33()),
            ("starcheck hub cycle C7", *hub_cycle(7))]
    rng = random.Random(args.seed)
    nrand = 0; attempts = 0
    while nrand < args.graphs and attempts < 10 * args.graphs:
        attempts += 1
        G, Z = random_side(rng, args.maxZ)
        if G is None: continue
        nrand += 1
        pop.append((f"random side #{nrand}", G, Z))
    print(f"population: 9 starcheck graphs + {nrand} random habitat sides (all verified: girth>=7, count on all subsets, Case 1)")
    allok = True; complete = True
    tot_withJ = 0; tot_pat = 0; tight_full_total = 0; tight_red_total = 0; t3 = 0; nbad = 0
    gmin_full = None; gmin_red = None
    for name, G, Z in pop:
        ok, why = check_side(G, Z)
        if not ok:
            print(f"  {name}: SKIPPED ({why})"); continue
        E = hyperedges(G, Z)
        if all(len(e) <= 1 for e in E.values()):
            print(f"  {name}: |Z|={len(Z)} |V|={len(G.adj)} vacuous (J == 0)"); continue
        stats, fin = check_graph(name, G, Z, None)
        complete &= fin
        tot_pat += stats["patterns"]; tot_withJ += stats["withJ"]
        tight_full_total += stats["tight_full"]; tight_red_total += stats["tight_red"]
        t3 += stats["type3"]; nbad += stats["bad"]
        if stats["min_full"] is not None:
            gmin_full = stats["min_full"] if gmin_full is None else min(gmin_full, stats["min_full"])
            gmin_red = stats["min_red"] if gmin_red is None else min(gmin_red, stats["min_red"])
        v = len(stats["violations"]); lf = len(stats["link_fail"])
        flag = "OK" if (v == 0 and lf == 0) else "FAIL"
        if flag == "FAIL": allok = False
        print(f"  {name}: |Z|={stats['nZ']} |V|={stats['nV']} patterns={stats['patterns']} J>=1: {stats['withJ']} "
              f"min slack full/reduced = {stats['min_full']}/{stats['min_red']} tight full/reduced = {stats['tight_full']}/{stats['tight_red']} "
              f"type3 lines={stats['type3']} bad pairs={stats['bad']} {flag}{'' if fin else ' (CAP HIT)'}")
        for x in stats["violations"][:3]: print("     VIOLATION:", x)
        for x in stats["link_fail"][:3]: print("     LINK FAIL:", x)
    print("\n=== SUMMARY ===")
    print(f"patterns enumerated {tot_pat}, with J >= 1: {tot_withJ}; min slack (cost - J - 1): full {gmin_full}, reduced {gmin_red}; "
          f"tight patterns: full {tight_full_total}, reduced {tight_red_total}; type-(3) reduced lines seen {t3}; bad pairs seen {nbad}")
    print(f"VERDICT: {'PASS' if allok else 'FAIL'}{'' if complete else ' (INCOMPLETE: cap hit)'}   total time {elapsed():.1f}s")
    return 0 if (allok and complete) else 1

if __name__ == "__main__":
    sys.exit(main())
