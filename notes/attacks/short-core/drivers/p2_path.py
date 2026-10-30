#!/usr/bin/env python3
"""Exact controls for SHORT-CORE workbook S14 and S16 (and S9 (iii)), d = 4.

    python3 notes/attacks/short-core/drivers/p2_path.py --seed 1 --trials 60

Each trial draws a connected simple graph F on n = 5..8 bodies (a random spanning tree plus
random extra edges, density varied per trial, or a triangle strip with a flexible pendant), and
an integer picture q in [-C, C]^2 per body, q^_v = (q_v, 1).  In exact Q it checks:
  [P2]  the P^2 point-join framework (hinges q^_u x q^_v) at q: dim Z(F) = 3 + def_3(F), the
        generic value (a draw meeting it certifies it, since dim Z >= 3 + def_3 always);
  [S14] for every non-adjacent pair a, b with S(a) = S(b) on Z(F), and F' = F + ab meeting
        dim Z(F') = 3 + def_3(F') at the draw (S14's hypothesis, checked, not assumed):
        def_3(F') >= def_3(F); every F'-optimal partition has a, b in one part X, F[X]
        connected, every motion constant on X; and a, b in one component of F[H], H the rigid
        class of a;
  [S9]  P^4 configuration b_v = (q_v, z1_v, z2_v, 1), z1, z2 random in L_1(q) (computed from
        its definition: closed neighbourhoods lift to planes), for every pair a, b with at
        least two neighbours each: kappa = dim(Pi_a & Pi_b) = 3 - min(2, dim rho2);
  [S16] at those pairs with kappa = 3, and a ~ b or F' at its generic rank: rho, the relative
        screws of the P^4 framework (hinges b_u ^ b_v in Lambda^2 Q^5), lies in Lambda^2 Pi_a.
        `s16_nontrivial` counts the checked pairs at which F itself is not P^2-rigid.
  control: at the pairs with kappa <= 2, how often rho is not in Lambda^2 Pi_a (the test can fail).
The deficiency is by enumerating set partitions (independent of `strata.py`'s DP).
Population: the graphs and pictures this seed draws, n <= 8; nothing here is a census.  Each
figure is one draw per graph; [S14] and [S16] are guarded by S14's exact hypothesis at the draw.
Exit status 1 on any failed check.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F
from itertools import combinations

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, os.pardir, os.pardir, "scripts"))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, cross3  # noqa: E402

C = 40
PL5 = list(combinations(range(5), 2))


def wedge5(p, r):
    return [p[i] * r[j] - p[j] * r[i] for i, j in PL5]


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
    n = R.randint(5, 8)
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--trials", type=int, default=60)
    args = ap.parse_args()
    R = random.Random(args.seed)
    bad = 0
    tally = dict(graphs=0, p2_generic=0, rel_rigid_pairs=0, s14_guarded=0, s14_nontrivial=0,
                 s9_pairs=0, kappa3=0, s16_checked=0, s16_nontrivial=0, s16_rho_nonzero=0,
                 ctrl_kappa_le2=0, ctrl_rho_outside=0)
    for t in range(args.trials):
        n, E = draw_graph(R, t)
        q = [[F(R.randint(-C, C)), F(R.randint(-C, C))] for _ in range(n)]
        qh = [[x, y, F(1)] for x, y in q]
        h2 = [cross3(qh[u], qh[v]) for u, v in E]
        if not all(any(h) for h in h2):
            continue
        tally["graphs"] += 1
        Z, _ = motions(n, E, h2)
        dF = deficiency3(n, E)
        gen = len(Z) == 3 + dF
        tally["p2_generic"] += gen
        lam = lambda S, v: S[3 * v:3 * v + 3]  # noqa: E731
        adjacent = set(E)
        # [S14]
        for a, b in combinations(range(n), 2):
            rho2 = [[x - y for x, y in zip(lam(S, b), lam(S, a))] for S in Z]
            if rank(rho2) != 0 or (a, b) in adjacent:
                continue
            tally["rel_rigid_pairs"] += 1
            E1 = E + [(a, b)]
            h1 = cross3(qh[a], qh[b])
            Z1, _ = motions(n, E1, h2 + [h1])
            d1 = deficiency3(n, E1)
            if len(Z1) != 3 + d1:
                continue
            tally["s14_guarded"] += 1
            H = {v for v in range(n) if all(lam(S, v) == lam(S, a) for S in Z)}
            tally["s14_nontrivial"] += len(H) < n
            ok = d1 >= dF
            ok &= any(a in c and b in c for c in comps(H, E))
            for assign, k in set_partitions(n):
                if part_val(E1, assign, k) != d1:
                    continue
                X = {v for v in range(n) if assign[v] == assign[a]}
                ok &= b in X and len(comps(X, E)) == 1 and X <= H
            if not ok:
                bad += 1
                print(f"S14 FAILED: trial {t}, n={n}, E={E}, a={a}, b={b}")
        # [S9], [S16]
        L1, nb = lifting_space(n, E, qh)
        z1, z2 = comb(R, L1, n), comb(R, L1, n)
        pts = [[q[v][0], q[v][1], z1[v], z2[v], F(1)] for v in range(n)]
        h4 = [wedge5(pts[u], pts[v]) for u, v in E]
        Z4, _ = motions(n, E, h4)
        for a, b in combinations(range(n), 2):
            if len(nb[a]) < 3 or len(nb[b]) < 3:
                continue
            PA, PB = [pts[v] for v in nb[a]], [pts[v] for v in nb[b]]
            if rank(PA) != 3 or rank(PB) != 3:
                continue
            tally["s9_pairs"] += 1
            kappa = 6 - rank(PA + PB)
            rho2 = [[x - y for x, y in zip(lam(S, b), lam(S, a))] for S in Z]
            if kappa != 3 - min(2, rank(rho2)):
                bad += 1
                print(f"S9(iii) FAILED: trial {t}, E={E}, a={a}, b={b}, kappa={kappa}")
            if kappa != 3:
                # control: the containment test is not vacuous off kappa = 3
                rho = [[x - y for x, y in zip(S[10 * b:10 * b + 10], S[10 * a:10 * a + 10])]
                       for S in Z4]
                lam2 = [wedge5(u, w) for u, w in combinations(PA, 2)]
                tally["ctrl_kappa_le2"] += 1
                tally["ctrl_rho_outside"] += rank(lam2 + rho) != rank(lam2)
                continue
            tally["kappa3"] += 1
            if (a, b) not in adjacent:
                Z1, _ = motions(n, E + [(a, b)], h2 + [cross3(qh[a], qh[b])])
                if len(Z1) != 3 + deficiency3(n, E + [(a, b)]):
                    continue
            tally["s16_checked"] += 1
            tally["s16_nontrivial"] += len(Z) > 3
            rho = [[x - y for x, y in zip(S[10 * b:10 * b + 10], S[10 * a:10 * a + 10])]
                   for S in Z4]
            basis = [r for r in PA]
            lam2 = [wedge5(u, w) for u, w in combinations(basis, 2)]
            tally["s16_rho_nonzero"] += rank(rho) > 0
            if rank(lam2 + rho) != rank(lam2):
                bad += 1
                print(f"S16 FAILED: trial {t}, E={E}, a={a}, b={b}, dim rho={rank(rho)}")
    print("seed", args.seed, "trials", args.trials)
    for k, v in tally.items():
        print(f"  {k}: {v}")
    print("OK" if bad == 0 else f"FAILED: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
