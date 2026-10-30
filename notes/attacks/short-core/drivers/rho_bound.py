#!/usr/bin/env python3
"""Exact control for SHORT-CORE workbook S28-S31: the P^2 gluing lemma, the Case 1/2 dichotomy,
Lambda^2 P injective on rho in Case 1, and r = 3 at the danger cells (k <= 2d - 4).

    python3 notes/attacks/short-core/drivers/rho_bound.py --seed 1 --trials 40 --dims 4,5

Population (connected simple graphs F on n = 6..9 bodies, family by trial mod 4):
  0  p2_path.py's `draw_graph` (random tree plus extra edges, or a triangle strip with a flexible
     pendant cycle), with n drawn in 6..9 here (5..8 there);
  1  a cycle (two internally disjoint 0-1 paths) or a theta (three), every path of length >= 3;
  2  two rigid triangle strips (s1, s2 >= 3 bodies, i ~ i+1, i ~ i+2) joined by one edge or by two
     vertex-disjoint paths, the connector type rotating through CONNECTORS;
  3  a random sparse graph: a random spanning tree plus 0..3 extra edges.
A picture q in [-C, C]^2 per body (C = 40), q^_v = (q_v, 1); a graph with a zero P^2 hinge is
skipped.  The P^2 point-join framework has hinges q^_u x q^_v (Lambda^2 Q^3 by the cross product)
and motion space Z(F).  For each pair a, b non-adjacent with no common neighbour: Z0 = {mu in Z(F) :
mu_a = mu_b}, r = dim Z(F) - dim Z0, def(F/ab) = max val_F(P) over the set partitions P of V(F)
not separating a, b (enumerated, n <= 9; val_F(P) = 3(|P| - 1) - 2 d_F(P)).  Every such P
attaining def(F/ab) is classed by X, its part holding a, b: Case 1 if a, b lie in one component of
F[X], Case 2 otherwise.  A pair is `case1` (every maximiser Case 1), `case2` (every one Case 2) or
`mixed` (both occur: cycles C_6, trees with dist(a, b) = 3, the theta (3, 3, 3), ...).
P^d (d in --dims): m = d - 2 heights, b_v = (q_v, z^1_v, ..., z^m_v, 1) in Q^(d+1), two height
regimes per graph and d: H1, each z^i a combination of a basis of L_1(q) (p2_path.py's
`lifting_space`, coefficients in [-9, 9], 0 read as 1); H2, each z^i_v an integer in [-C, C].
The P^d motions S (S_u - S_v in Q b_u^b_v on each edge) are computed as edge flows (`flow_motions`,
cross-checked against `motions` on the P^2 framework of every graph), rho = {S(b) - S(a)} in
Lambda^2 Q^(d+1), and Lambda^2 P keeps the coordinates 0, 1, d of each point (forgets the heights).
Checks, exit status 1 on any failure:
  [G]     guard: dim Z(F) = 3 + def_3(F) (else the graph is skipped) and dim Z0 = 3 + def(F/ab)
          (else the pair is skipped; counted as `g_pairs_failed`).  dim Z >= 3 + def and
          dim Z0 >= 3 + def(F/ab) at every picture, so a draw meeting [G] certifies the generic
          P^2 values at that graph (S28's equality, hence r = def(F) - def(F/ab)).
  [B]     r <= 2 implies every maximiser is Case 1 (S29);
  [B2]    every Case-2 maximiser has r = 3, F[X] with exactly two components, and every mu in Z(F)
          constant on each (S29);
  [C]     at case1 and mixed pairs, both regimes, each d: dim rho = dim Lambda^2 P(rho) (injective)
          and dim rho <= r (S30);
  [S26ii] at every guarded pair: Lambda^2 P(rho) lies in {mu_b - mu_a : mu in Z(F)};
  [X]     internal: flow_motions agrees with motions on P^2 (dim and the space rho^(2)), and
          Lambda^2 P sends each P^d hinge to its P^2 hinge.
  control: at case2 pairs the distribution of (dim rho, dim rho & ker Lambda^2 P) per d and regime,
          showing [C] can fail outside its hypothesis; the pair counts per (family, r) and per class;
          and `rho_eq_sep_bridges`, the (pair, d, regime) frames at which dim rho is the number of
          bridges of F separating a, b, i.e. how far [C] is exercised beyond bridge hinges.
[C] and [S26ii] are checked at one drawn configuration per (graph, d, regime), not certified generic.
Nothing here is a census: the population is the graphs and pictures this seed draws.
Control for workbook S28-S31.  The script has no ear parameter k: S31 (the danger cells
k <= 2d - 4 have r = 3) enters only through [B] and [B2], r <= 2 forcing Case 1 and Case 2 forcing
r = 3.  Run time about 2 s per seed at --trials 40.
"""
import argparse
import os
import random
import sys
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, os.pardir, os.pardir, "scripts"))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, cross3  # noqa: E402

C = 40
CONNECTORS = [(1,), (2, 3), (1, 1), (2, 2), (1, 2), (1, 3)]


def plucker_pairs(d):
    return list(combinations(range(d + 1), 2))


def wedge(p, r, pl):
    return [p[i] * r[j] - p[j] * r[i] for i, j in pl]


def lam2P(vec, pl, d):
    """Lambda^2 P, P keeping coordinates 0, 1, d; output in cross3's basis of Lambda^2 Q^3."""
    return [vec[pl.index((1, d))], -vec[pl.index((0, d))], vec[pl.index((0, 1))]]


# ---- copied from p2_path.py (draw_graph: n range 6..9 here) ----

def set_partitions(n):
    def go(i, assign, k):
        if i == n:
            yield list(assign), k
            return
        for b in range(k + 1):
            assign.append(b)
            yield from go(i + 1, assign, max(k, b + 1))
            assign.pop()
    yield from go(0, [], 0)


def part_val(edges, assign, k):
    return 3 * (k - 1) - 2 * sum(1 for u, v in edges if assign[u] != assign[v])


def deficiency3(n, edges):
    return max(part_val(edges, a, k) for a, k in set_partitions(n))


def motions(n, edges, hinges):
    """Basis of {S : S_u - S_v in span(h_uv)}, S_v in Q^D, D = len(h)."""
    D = len(hinges[0])
    rows = []
    for (u, v), h in zip(edges, hinges):
        assert any(h), "zero hinge"
        for r in nullspace([h]):
            row = [F(0)] * (D * n)
            for j in range(D):
                row[D * u + j] += r[j]
                row[D * v + j] -= r[j]
            rows.append(row)
    return nullspace(rows), D


def comps(vs, edges):
    vs = set(vs)
    adj = {v: set() for v in vs}
    for u, v in edges:
        if u in vs and v in vs:
            adj[u].add(v)
            adj[v].add(u)
    seen, out = set(), []
    for s in vs:
        if s in seen:
            continue
        stack, c = [s], set()
        while stack:
            x = stack.pop()
            if x in c:
                continue
            c.add(x)
            stack.extend(adj[x] - c)
        seen |= c
        out.append(c)
    return out


def draw_graph(R, trial):
    n = R.randint(6, 9)
    if trial % 4 == 3:
        # a triangle strip on s bodies, a flexible pendant cycle on the rest
        s = R.randint(4, n - 1)
        E = {(i, i + 1) for i in range(s - 1)} | {(i, i + 2) for i in range(s - 2)}
        rest = list(range(s, n))
        cyc = [R.randrange(s)] + rest
        E |= {tuple(sorted((cyc[i], cyc[(i + 1) % len(cyc)]))) for i in range(len(cyc))
              if cyc[i] != cyc[(i + 1) % len(cyc)]}
        E |= {tuple(sorted((rest[-1], R.randrange(s))))} if rest else set()
    else:
        perm = list(range(n))
        R.shuffle(perm)
        E = {tuple(sorted((perm[i], perm[R.randrange(i)]))) for i in range(1, n)}
        extra = R.randint(1, n if trial % 2 else n // 2 + 1)
        while extra:
            u, v = R.sample(range(n), 2)
            if tuple(sorted((u, v))) not in E:
                E.add(tuple(sorted((u, v))))
                extra -= 1
    return n, sorted(E)


def lifting_space(n, edges, qh):
    """L_1(q) from its definition: unknowns (lam_u in Q^3, z_v), z_v = lam_u . q^_v on N[u]."""
    nb = {v: {v} for v in range(n)}
    for u, v in edges:
        nb[u].add(v)
        nb[v].add(u)
    rows = []
    for u in range(n):
        for v in nb[u]:
            row = [F(0)] * (4 * n)
            for j in range(3):
                row[3 * u + j] = -qh[v][j]
            row[3 * n + v] = F(1)
            rows.append(row)
    return [b[3 * n:] for b in nullspace(rows)], nb


def comb(R, basis, m):
    out = [F(0)] * m
    for b in basis:
        c = R.randint(-9, 9) or 1
        out = [x + c * y for x, y in zip(out, b)]
    return out


# ---- the other families ----

def chain_edges(chain):
    return {tuple(sorted((chain[i], chain[i + 1]))) for i in range(len(chain) - 1)}


def strip_edges(vs):
    vs = list(vs)
    return ({tuple(sorted((vs[i], vs[i + 1]))) for i in range(len(vs) - 1)}
            | {tuple(sorted((vs[i], vs[i + 2]))) for i in range(len(vs) - 2)})


def draw_theta(R, idx):
    """Internally disjoint 0-1 paths of lengths >= 3: two (a cycle) or three (a theta)."""
    if idx % 2 == 0:
        n = R.randint(6, 9)
        l1 = R.randint(3, n - 3)
        lens = [l1, n - l1]
    else:
        lens = R.choice([[3, 3, 3], [3, 3, 4]])
    E, nxt = set(), 2
    for L in lens:
        chain = [0] + list(range(nxt, nxt + L - 1)) + [1]
        nxt += L - 1
        E |= chain_edges(chain)
    return nxt, sorted(E)


def draw_strips(R, idx):
    """Two triangle strips joined by one edge or by two vertex-disjoint paths (CONNECTORS)."""
    conn = CONNECTORS[idx % len(CONNECTORS)]
    room = 9 - sum(L - 1 for L in conn)
    s1 = R.randint(3, room - 3)
    s2 = R.randint(3, room - s1)
    A, B = list(range(s1)), list(range(s1, s1 + s2))
    E = strip_edges(A) | strip_edges(B)
    xs, ys = R.sample(A, len(conn)), R.sample(B, len(conn))
    nxt = s1 + s2
    for L, x, y in zip(conn, xs, ys):
        E |= chain_edges([x] + list(range(nxt, nxt + L - 1)) + [y])
        nxt += L - 1
    return nxt, sorted(E)


def draw_sparse(R):
    n = R.randint(6, 9)
    perm = list(range(n))
    R.shuffle(perm)
    E = {tuple(sorted((perm[i], perm[R.randrange(i)]))) for i in range(1, n)}
    extra = R.randint(0, 3)
    while extra and len(E) < n * (n - 1) // 2:
        u, v = R.sample(range(n), 2)
        if tuple(sorted((u, v))) not in E:
            E.add(tuple(sorted((u, v))))
            extra -= 1
    return n, sorted(E)


FAMILIES = ["draw_graph", "theta", "strips", "sparse"]


def draw(R, t):
    fam = t % 4
    if fam == 0:
        n, E = draw_graph(R, t // 4)
    elif fam == 1:
        n, E = draw_theta(R, t // 4)
    elif fam == 2:
        n, E = draw_strips(R, t // 4)
    else:
        n, E = draw_sparse(R)
    return FAMILIES[fam], n, E


# ---- motions as edge flows ----

def flow_motions(n, edges, hinges):
    """Motions modulo constants as edge flows: S_u - S_v = t_e h_e on e = (u, v), S_0 = 0.
    Returns (N, coef): N a basis of the admissible t in Q^E, and S_v = sum_e coef[v][e] t_e h_e.
    So dim Z = D + len(N) (F connected)."""
    D, m = len(hinges[0]), len(edges)
    inc = {v: [] for v in range(n)}
    for e, (u, v) in enumerate(edges):
        inc[u].append(e)
        inc[v].append(e)
    coef = {0: [0] * m}
    order, tree = [0], set()
    for x in order:
        for e in inc[x]:
            u, v = edges[e]
            y = v if u == x else u
            if y in coef:
                continue
            c = coef[x][:]
            c[e] += -1 if u == x else 1  # S_y = S_x - t h if e = (x, y), S_x + t h if e = (y, x)
            coef[y] = c
            tree.add(e)
            order.append(y)
    assert len(coef) == n, "disconnected graph"
    rows = []
    for e, (u, v) in enumerate(edges):
        if e in tree:
            continue
        for j in range(D):
            rows.append([F(coef[u][f] - coef[v][f] - (f == e)) * hinges[f][j] for f in range(m)])
    if rows:
        N = nullspace(rows)
    else:
        N = [[F(int(f == g)) for f in range(m)] for g in range(m)]
    return N, coef


def rel(N, coef, hinges, a, b):
    """{S(b) - S(a)} spanned over the flow basis N."""
    D = len(hinges[0])
    diff = [coef[b][f] - coef[a][f] for f in range(len(hinges))]
    out = []
    for t in N:
        vec = [F(0)] * D
        for f, c in enumerate(diff):
            if c and t[f]:
                w = c * t[f]
                vec = [x + w * y for x, y in zip(vec, hinges[f])]
        out.append(vec)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--trials", type=int, default=40)
    ap.add_argument("--dims", type=str, default="4,5")
    args = ap.parse_args()
    dims = [int(x) for x in args.dims.split(",")]
    R = random.Random(args.seed)
    bad = 0
    tally = dict(graphs=0, zero_hinge_skipped=0, g_graph_failed=0, eligible_pairs=0,
                 g_pairs_failed=0, guarded_pairs=0, b_checked=0, b2_maximisers=0,
                 c_checks=0, c_checks_rho_nonzero=0, c_checks_mixed=0, s26ii_checks=0,
                 rho_eq_sep_bridges=0, h1_affine_only=0)
    fam_pairs, r_count, cls_count, r_by_cls = Counter(), Counter(), Counter(), Counter()
    c_dist, ctrl_dist = Counter(), Counter()

    def fail(msg):
        nonlocal bad
        bad += 1
        print("FAILED:", msg)

    for t in range(args.trials):
        fam, n, E = draw(R, t)
        q = [[F(R.randint(-C, C)), F(R.randint(-C, C))] for _ in range(n)]
        qh = [[x, y, F(1)] for x, y in q]
        h2 = [cross3(qh[u], qh[v]) for u, v in E]
        if not all(any(h) for h in h2):
            tally["zero_hinge_skipped"] += 1
            continue
        assert len(comps(range(n), E)) == 1
        tally["graphs"] += 1
        Z, _ = motions(n, E, h2)
        N2, coef2 = flow_motions(n, E, h2)
        if len(Z) != 3 + len(N2):
            fail(f"[X] trial {t}: dim motions {len(Z)} != 3 + flow {len(N2)}")
        parts = [(tuple(a), k, part_val(E, a, k)) for a, k in set_partitions(n)]
        dF = max(v for _, _, v in parts)
        # P^d frameworks: one draw per d and regime
        L1, nb = lifting_space(n, E, qh)
        tally["h1_affine_only"] += rank(L1) == 3  # L1 lists z-projections, zeros included
        frames = {}
        for d in dims:
            pl, m = plucker_pairs(d), d - 2
            for reg in ("H1", "H2"):
                if reg == "H1":
                    zs = [comb(R, L1, n) for _ in range(m)]
                else:
                    zs = [[F(R.randint(-C, C)) for _ in range(n)] for _ in range(m)]
                pts = [[q[v][0], q[v][1]] + [z[v] for z in zs] + [F(1)] for v in range(n)]
                hd = [wedge(pts[u], pts[v], pl) for u, v in E]
                for (u, v), h, g in zip(E, hd, h2):
                    if lam2P(h, pl, d) != g:
                        fail(f"[X] trial {t}: Lambda^2 P(b_u^b_v) != q^_u x q^_v at {(u, v)}")
                N, coef = flow_motions(n, E, hd)
                frames[d, reg] = (pl, hd, N, coef)
        if len(Z) != 3 + dF:
            tally["g_graph_failed"] += 1
            continue
        adjacent = set(E)
        lam = lambda S, v: S[3 * v:3 * v + 3]  # noqa: E731
        for a, b in combinations(range(n), 2):
            if (a, b) in adjacent or (nb[a] - {a}) & (nb[b] - {b}):
                continue
            tally["eligible_pairs"] += 1
            rho2 = [[x - y for x, y in zip(lam(S, b), lam(S, a))] for S in Z]
            r = rank(rho2)
            rho2f = rel(N2, coef2, h2, a, b)
            if rank(rho2f) != r or rank(rho2f + rho2) != r:
                fail(f"[X] trial {t}: flow rho^(2) != motions rho^(2) at {(a, b)}")
            dab = max(v for asg, _, v in parts if asg[a] == asg[b])
            if len(Z) - r != 3 + dab:
                tally["g_pairs_failed"] += 1
                continue
            tally["guarded_pairs"] += 1
            fam_pairs[fam, r] += 1
            sep = sum(1 for e in E if not any(a in c and b in c
                                              for c in comps(range(n), [f for f in E if f != e])))
            r_count[r] += 1
            cases = set()
            for asg, _, v in parts:
                if asg[a] != asg[b] or v != dab:
                    continue
                X = {w for w in range(n) if asg[w] == asg[a]}
                cs = comps(X, E)
                if any(a in c and b in c for c in cs):
                    cases.add(1)
                    continue
                cases.add(2)
                tally["b2_maximisers"] += 1
                const = all(lam(S, w) == lam(S, min(c)) for c in cs for w in c for S in Z)
                if not (r == 3 and len(cs) == 2 and const):
                    fail(f"[B2] trial {t}, n={n}, E={E}, a={a}, b={b}, X={sorted(X)}: r={r}, "
                         f"{len(cs)} components, constant={const}")
            cls = {frozenset({1}): "case1", frozenset({2}): "case2"}.get(frozenset(cases), "mixed")
            cls_count[cls] += 1
            r_by_cls[r, cls] += 1
            if r <= 2:
                tally["b_checked"] += 1
                if cls != "case1":
                    fail(f"[B] trial {t}, n={n}, E={E}, a={a}, b={b}: r={r}, class {cls}")
            for (d, reg), (pl, hd, N, coef) in frames.items():
                rho = rel(N, coef, hd, a, b)
                prho = [lam2P(x, pl, d) for x in rho]
                dr, dp = rank(rho), rank(prho)
                tally["s26ii_checks"] += 1
                tally["rho_eq_sep_bridges"] += dr == sep
                if rank(rho2 + prho) != r:
                    fail(f"[S26ii] trial {t}, d={d}, {reg}, n={n}, E={E}, a={a}, b={b}")
                if cls == "case2":
                    ctrl_dist[d, reg, r, dr, dr - dp] += 1
                    continue
                tally["c_checks"] += 1
                tally["c_checks_rho_nonzero"] += dr > 0
                tally["c_checks_mixed"] += cls == "mixed"
                c_dist[d, reg, cls, r, dr, dr - dp] += 1
                if dr != dp or dr > r:
                    fail(f"[C] trial {t}, d={d}, {reg}, class {cls}, n={n}, E={E}, a={a}, b={b}: "
                         f"r={r}, dim rho={dr}, dim P(rho)={dp}")
    print("seed", args.seed, "trials", args.trials, "dims", args.dims)
    for k, v in tally.items():
        print(f"  {k}: {v}")
    print("  guarded pairs per (family, r):", dict(sorted(fam_pairs.items())))
    print("  guarded pairs per r:", {k: r_count[k] for k in range(4)})
    print("  guarded pairs per class:", {k: cls_count[k] for k in ("case1", "mixed", "case2")})
    print("  (r, class):", dict(sorted(r_by_cls.items())))
    missing = [k for k in range(4) if not r_count[k]]
    if missing:
        print("  WARNING: no guarded pair with r in", missing)
    print("  [C] (d, regime, class, r, dim rho, dim rho&ker):")
    for k, v in sorted(c_dist.items()):
        print(f"    {k}: {v}")
    print("  control, case2 (d, regime, r, dim rho, dim rho&ker):")
    for k, v in sorted(ctrl_dist.items()):
        print(f"    {k}: {v}")
    print("OK" if bad == 0 else f"FAILED: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
