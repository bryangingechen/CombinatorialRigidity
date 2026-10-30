#!/usr/bin/env python3
"""NONDEG workbook S37: a control of S35-S36 ((W) at every W0-ear) beyond nine bodies.

    PYTHONHASHSEED=0 python3 notes/attacks/nondeg/drivers/wsweep.py --pop struct --count 400 --seed 1
    PYTHONHASHSEED=0 python3 notes/attacks/nondeg/drivers/wsweep.py --pop geng --n 10 --res 0 1 2 3 --mod 1000 --seed 1

Populations.
  struct -- seeded structured graphs aimed at S35 (b), the one step where the outside of W0 enters.
            A base W0 is a graph on 5, 7, 9 or 11 bodies with 3(|W0| - 1)/2 edges (geng -c -d2,
            nauty 2.9; a W0 with a W0-ear has s(W0) = 0) that is itself a minimal planar-rigid set (s(W0) <= 0, s(Z) >= 1 for every Z strictly inside with |Z| >= 2), meets
            the hub conditions, and has a W0-ear (x of degree two, non-adjacent neighbours of degree
            at least three).  One to MAX_ATT attachments are added at bodies p, p', p'' of W0 - {x}
            (never at x, which keeps degree two); the base size is drawn uniformly, then the base;
            each attachment is of one of the kinds
              K2k  -- k = 1, 2, 3 new bodies, each adjacent to p and p' (a K_{2,k} on two W0 bodies;
                      k = 3 is a second planar-rigid set sharing two hubs with W0);
              hub  -- a new hub u adjacent to p, p' and to j = 1, 2 new bodies t_i, each adjacent to u
                      and p'' (an outside hub with two points of X, S35 (b)'s second case);
              copy -- a copy of a base, two of its non-adjacent bodies identified with p, p' (a second
                      minimal planar-rigid set sharing two bodies with W0);
              path -- a path of 2 or 3 new bodies from p to p' (an outside ear).
            Kept when simple, two-edge-connected, with the hub conditions; at most MAX_N bodies.  The
            W0 tested is the base (s-minimal in G, as G[W0] is the base), with all its W0-ears.
  geng   -- every graph of `geng -c -d2 n res/mod` for the listed res classes that is route B's case
            (ii) (as oneear.py), with every s-minimal W0 (oneear.minimal_rigid_sets) and its W0-ears.

Per graph: one point r0 of the polar steer family at d = 3 (nondeg.steer3), checked C2-same exactly
(else redrawn up to DEG_REDRAWS times, then "draws degenerate", no claim: a graph the steer never
makes nondegenerate is likely infeasible, which S36 does not cover).  Per W0-ear (x, a, b), X = W0 - {x}, over the picture q0 of r0:
  W     -- dim L_{G[X]}(q0|X); S36 says 4 at a general r0, and 4 is the least possible (S29 (3)),
           so a 4 is an exact certificate of (W) at this ear (S29: (W) is open, one point suffices);
  col   -- the number of triples of X whose picture points are collinear; S35 says the picture of X
           at a general r0 is a general picture of G[X], so 0 (a nonzero count at one draw is either
           a draw accident or a counterexample to S35; the driver redraws once to tell them apart);
  ear   -- free/COSTLY as oneear.ear_cell (dim L_G(q0) against dim L_H(q0|H)); S36 says free;
  case  -- which of S35 (b)'s cases occur at the ear: pseudo-hubs (hubs of G of degree two in G[X]),
           bodies v of X with one outside hub u in H_G[v], H_G[v] = {v, w, u}, u with two points of X
           ("b1"), and bodies with two outside hubs ("b2").
Measured: each W/ear/col value is read at one draw (W and dim L from above).  W = 4 certifies;
W > 4 at a draw certifies nothing and is redrawn once.  Exit status 1 if some ear has W > 4 or
col > 0 at both draws.  Sampler support: as nondeg.py (strata's Sampler, COORD); fenced constants
MAX_N, MAX_ATT, BASE_N (the default --base-n), DEG_REDRAWS here.
"""
import argparse
import os
import random
import subprocess
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import oneear as oe  # noqa: E402  -- read-only reuse
import nondeg as nd  # noqa: E402

st = nd.st
MAX_N = 16
MAX_ATT = 3
DEG_REDRAWS = 2
BASE_N = (5, 7, 9, 11)


# ---------------- populations ----------------

def s2(edges, Y):
    k = len(Y)
    e = sum(1 for u, v in edges if u in Y and v in Y)
    return 3 * (k - 1) - 2 * e


def is_minimal_rigid(n, edges):
    """s(V) <= 0 and s(Z) >= 1 for every Z strictly inside V with |Z| >= 2 (bitmask DP on e(Z))."""
    nbm = [0] * n
    for u, v in edges:
        nbm[u] |= 1 << v
        nbm[v] |= 1 << u
    full = (1 << n) - 1
    e = [0] * (1 << n)
    for Z in range(1, 1 << n):
        v = (Z & -Z).bit_length() - 1
        e[Z] = e[Z & (Z - 1)] + bin(nbm[v] & Z).count("1")
        k = bin(Z).count("1")
        if 2 <= k and 3 * (k - 1) - 2 * e[Z] <= 0 and Z != full:
            return False
    return 3 * (n - 1) - 2 * e[full] <= 0


def hub_ok(n, edges):
    _, _, H = nd.hub_sets(n, edges)
    return all(len(H[v]) <= 3 for v in range(n)) and not nd.two_hub_triangle(n, edges)


def w0_ears(n, edges, W):
    """x in W of degree two in G whose neighbours are hubs of G (in W, non-adjacent)."""
    nb, hubs, _ = nd.hub_sets(n, edges)
    out = []
    for x in sorted(W):
        if len(nb[x]) == 2:
            a, b = sorted(nb[x])
            if a in hubs and b in hubs and a in W and b in W and b not in nb[a]:
                out.append((x, a, b))
    return out


def bases(sizes=BASE_N):
    """By size: a W0 with a W0-ear has s(W0) = 0 (S29 (1): s(W0 - x) = s(W0) + 1 >= 1, and
    s(W0) <= 0), so |W0| is odd with 3(|W0| - 1)/2 edges; geng with that edge count."""
    out = {}
    for m in sizes:
        e = 3 * (m - 1) // 2
        txt = subprocess.run(["geng", "-c", "-d2", "-q", str(m), f"{e}:{e}"], capture_output=True,
                             text=True, timeout=3600, check=True).stdout.split()
        for g6 in txt:
            n, edges = oe.graph6(g6)
            if is_minimal_rigid(n, edges) and hub_ok(n, edges) and w0_ears(n, edges, set(range(n))):
                out.setdefault(m, []).append((n, edges))
    return out


KINDS = ("K2k", "hub", "copy", "path")


def attach(R, n, edges, W, x, base_list, kinds=KINDS):
    """One attachment at bodies of W - {x}; returns (n, edges, kind)."""
    pool = sorted(W - {x})
    p, p2 = R.sample(pool, 2)
    kind = R.choice(list(kinds))
    E = list(edges)
    if kind == "K2k":
        k = R.choice((1, 2, 3))
        for _ in range(k):
            E += [(p, n), (p2, n)]
            n += 1
        return n, E, f"K2{k}"
    if kind == "hub":
        rest = [v for v in pool if v not in (p, p2)]
        if not rest:
            return n, E, "none"
        p3 = R.choice(rest)
        u = n
        n += 1
        E += [(u, p), (u, p2)]
        for _ in range(R.choice((1, 2))):
            E += [(u, n), (n, p3)]
            n += 1
        return n, E, "hub"
    if kind == "copy":
        bn, be = R.choice(base_list)
        nbb = nd.nbhd(bn, be)
        pairs = [(i, j) for i, j in combinations(range(bn), 2) if j not in nbb[i]]
        if not pairs:
            return n, E, "none"
        i, j = R.choice(pairs)
        ix = {}
        for v in range(bn):
            if v == i:
                ix[v] = p
            elif v == j:
                ix[v] = p2
            else:
                ix[v] = n
                n += 1
        E += [(ix[u], ix[v]) for u, v in be]
        return n, E, "copy"
    k = R.choice((2, 3))
    prev = p
    for _ in range(k):
        E.append((prev, n))
        prev = n
        n += 1
    E.append((prev, p2))
    return n, E, f"path{k}"


def struct_population(count, seed, sizes=BASE_N, kinds=KINDS):
    by_size = bases(sizes)
    base_list = [g for m in sorted(by_size) for g in by_size[m]]
    R = random.Random(seed)
    out, tried = {}, 0
    while len(out) < count and tried < 50 * count:
        tried += 1
        bn, be = R.choice(by_size[R.choice(sorted(by_size))])
        x, a, b = R.choice(w0_ears(bn, be, set(range(bn))))
        W = set(range(bn))
        n, E, done = bn, list(be), []
        for _ in range(R.randint(1, MAX_ATT)):
            n2, E2, kind = attach(R, n, E, W, x, base_list, kinds)
            if n2 > MAX_N:
                break
            n, E = n2, E2
            done.append(kind)
        if n == bn or not st.simple(E) or not oe.two_edge_connected(n, E) or not hub_ok(n, E):
            continue
        out[f"s{len(out)}"] = (n, E, frozenset(W), "+".join(done))
    return out, {m: len(v) for m, v in sorted(by_size.items())}, tried


def geng_population(n, res, mod):
    out = {}
    for r in res:
        txt = subprocess.run(["geng", "-c", "-d2", "-q", str(n), f"{r}/{mod}"], capture_output=True,
                             text=True, timeout=3600, check=True).stdout.split()
        for i, s in enumerate(txt):
            m, edges = oe.graph6(s)
            out[f"g{n}-{r}-{i}"] = (m, edges, None, "")
    return out


def tries_word(k):
    return f"{k} tries"


# ---------------- per ear ----------------

def col_triples(q0, X):
    c = 0
    for u, v, w in combinations(sorted(X), 3):
        M = [[q0[t][0], q0[t][1], 1] for t in (u, v, w)]
        if st.rank(M) < 3:
            c += 1
    return c


def cases(n, edges, W, x):
    nb, hubs, H = nd.hub_sets(n, edges)
    X = W - {x}
    pseudo = sum(1 for v in X if v in hubs and len(nb[v] & X) == 2)
    b1 = b2 = 0
    for v in X:
        O = [u for u in H[v] if u not in W]
        if len(O) == 2:
            b2 += 1
        if len(O) == 1 and len(H[v]) == 3 and len(nb[O[0]] & X) == 2:
            b1 += 1
    return pseudo, b1, b2


def draw(s, n, edges):
    q0, z1 = nd.steer3(s, n, edges)
    _, b, Pi, _ = nd.steer_cell(s, n, edges, 3, q0, z1)
    st.need(nd.candidates(n, edges, b, Pi, 4)["C2same"], "steer draw not C2-same")
    return q0, z1


def ear_values(n, edges, q0, z1, W, ear):
    x, a, b = ear
    mask = sum(1 << v for v in W)
    lx = oe.dim_LX(n, edges, q0, x, mask)
    col = col_triples(q0, W - {x})
    nbh, _, _ = nd.hub_sets(n, edges)
    common = sorted((nbh[a] & nbh[b]) - {x})
    lg, lh, _, _ = oe.ear_cell(n, edges, q0, z1, (x, a, b, common, [mask]))
    return lx, col, lg == lh


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pop", choices=["struct", "geng"], default="struct")
    ap.add_argument("--count", type=int, default=400)
    ap.add_argument("--n", type=int, default=10)
    ap.add_argument("--res", type=int, nargs="+", default=[0])
    ap.add_argument("--mod", type=int, default=1000)
    ap.add_argument("--base-n", type=int, nargs="+", default=list(BASE_N))
    ap.add_argument("--kinds", nargs="+", choices=KINDS, default=list(KINDS))
    a = ap.parse_args()
    s = st.Sampler(a.seed)
    if a.pop == "struct":
        G, nb_, tried = struct_population(a.count, a.seed, tuple(a.base_n), tuple(a.kinds))
        print(f"# wsweep.py --pop struct --count {a.count} --base-n {' '.join(map(str, a.base_n))} "
              f"--kinds {' '.join(a.kinds)} seed {a.seed}; COORD {st.COORD}, MAX_N {MAX_N}, "
              f"MAX_ATT {MAX_ATT}; bases by size {nb_}, {tries_word(tried)}")
    else:
        G = geng_population(a.n, a.res, a.mod)
        print(f"# wsweep.py --pop geng --n {a.n} --res {' '.join(map(str, a.res))} --mod {a.mod} "
              f"seed {a.seed}; COORD {st.COORD}; {len(G)} graphs")
    t = {"graphs": 0, "kept": 0, "degenerate": 0, "ears": 0, "W4": 0, "Wbig": 0, "col0": 0,
         "colpos": 0, "free": 0, "costly": 0, "pseudo": 0, "b1": 0, "b2": 0, "redraw": 0}
    bad = 0
    sizes = {}
    for name, (n, edges, W, kinds) in G.items():
        t["graphs"] += 1
        if W is None:
            if n < 4 or not st.simple(edges) or not hub_ok(n, edges):
                continue
            if not oe.two_edge_connected(n, edges) or oe.min_s2(n, edges) > 0:
                continue
            Ws = [frozenset(v for v in range(n) if (m >> v) & 1)
                  for m in oe.minimal_rigid_sets(n, edges)]
        else:
            Ws = [W]
        ears = [(Wi, e) for Wi in Ws for e in w0_ears(n, edges, Wi)]
        if not ears:
            continue
        t["kept"] += 1
        sizes[n] = sizes.get(n, 0) + 1
        q0 = None
        for attempt in range(1 + DEG_REDRAWS):
            try:
                q0, z1 = draw(s, n, edges)
                break
            except st.Degenerate as ex:
                why = ex
        if q0 is None:
            t["degenerate"] += 1
            print(f"{name:12s} n={n} e={len(edges)} {kinds:16s} {1 + DEG_REDRAWS} draws degenerate, "
                  f"no conclusion: {why}")
            continue
        t["redraw"] += attempt
        cells = []
        for Wi, ear in ears:
            t["ears"] += 1
            ps, b1, b2 = cases(n, edges, Wi, ear[0])
            t["pseudo"] += ps > 0
            t["b1"] += b1 > 0
            t["b2"] += b2 > 0
            try:
                lx, col, free = ear_values(n, edges, q0, z1, Wi, ear)
            except st.Degenerate as ex:
                cells.append(f"x{ear[0]}:degenerate({ex})")
                continue
            if lx > 4 or col > 0:
                t["redraw"] += 1
                try:
                    q1, z2 = draw(s, n, edges)
                    lx, col, free = ear_values(n, edges, q1, z2, Wi, ear)
                except st.Degenerate:
                    pass
            t["W4"] += lx == 4
            t["Wbig"] += lx > 4
            t["col0"] += col == 0
            t["colpos"] += col > 0
            t["free"] += free
            t["costly"] += not free
            bad += lx > 4 or col > 0
            cells.append(f"x{ear[0]}|W{len(Wi)}:W{lx}c{col}{'f' if free else 'C'}"
                         + (f"[p{ps}b{b1}{b2}]" if ps or b1 or b2 else ""))
        print(f"{name:12s} n={n} e={len(edges)} {kinds:16s} " + " ".join(cells), flush=True)
    print("# sizes " + ", ".join(f"n={k}: {v}" for k, v in sorted(sizes.items())))
    print("# " + ", ".join(f"{k} {v}" for k, v in t.items()))
    print(f"# ears with W > 4 or a collinear triple at both draws: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
