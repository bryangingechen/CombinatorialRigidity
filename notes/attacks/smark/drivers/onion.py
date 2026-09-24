#!/usr/bin/env python3
"""onion.py -- O7e-c cores: the onion depths S_i, girth, the strict count, and the 3-degeneracy of the onion order
(smark session 14, workbook S40).  Exact integers, stdlib only, no randomness.

S_0 := Z (every vertex of the core is taken marked -- the worst case for the count is the same), S_{i+1} := {v in S_i :
deg_{Gamma[S_i]} v >= 3}; S_1 = Big, S_2 = {k_c >= 4}.  Depth D := max{i : S_i nonempty}.  The onion order (S40(i)):
for j = D, D-1, ..., 0 place the points p_v (j odd) or the planes pi_v (j even) of v in S_j - S_{j+2}; finally the points
of V - S_1.  The driver counts, for every element, its incident elements placed earlier (p_y ~ pi_c iff y in N[c]) and
reports the maximum (3-degenerate iff <= 3).

Strict count (S19(viii) / S35(i)): for every connected subgraph with an edge, 5|E| <= 6|V| - 7.  Checked EXACTLY over
unions of whole branch paths (a partial path never helps: a pendant vertex adds 5 - 6 < 0), by enumerating every subset of
the branch paths, keeping the connected ones: min slack := min (6|V| - 7 - 5|E|).

    timeout 600 python3 notes/attacks/smark/drivers/onion.py k4core 6      # depth 2 (review 5's core, k4core.py)
    timeout 600 python3 notes/attacks/smark/drivers/onion.py tree2 5       # depth 3: a cubic tree of radius 2, six paths
"""
import sys, random
from fractions import Fraction
from collections import deque


def nullspace(rows, n=4):
    """exact basis of {x in Q^n : r . x = 0 for every r in rows}."""
    M = [[Fraction(x) for x in r] for r in rows]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * n; v[f] = Fraction(1)
        for i, c in enumerate(piv): v[c] = -M[i][f]
        basis.append(v)
    return basis, r


def k4core(L):
    """centre c, unit spokes c - x_i, rim paths x_i - x_j of length L (k4core.py's family)."""
    E = [("c", f"x{i}") for i in range(3)]
    for i in range(3):
        j = (i + 1) % 3
        prev = f"x{i}"
        for t in range(1, L):
            v = f"r{i}{j}_{t}"; E.append((prev, v)); prev = v
        E.append((prev, f"x{j}"))
    return E


def tree2(L):
    """cubic tree of radius 2 -- c; x0, x1, x2; y_i0, y_i1 under x_i -- with six paths of length L joining the y's across
    different parents in a 6-cycle pattern y00-y11, y10-y21, y20-y01, y01... (each y has exactly two path ends)."""
    E = [("c", f"x{i}") for i in range(3)] + [(f"x{i}", f"y{i}{k}") for i in range(3) for k in range(2)]
    ys = ["y00", "y11", "y20", "y01", "y10", "y21"]          # cyclic order: consecutive y's have different parents
    for t in range(6):
        a, b = ys[t], ys[(t + 1) % 6]
        prev = a
        for s in range(1, L):
            v = f"p{t}_{s}"; E.append((prev, v)); prev = v
        E.append((prev, b))
    return E


def main():
    fam, L = sys.argv[1], int(sys.argv[2])
    E = {"k4core": k4core, "tree2": tree2}[fam](L)
    adj = {}
    for a, b in E:
        adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    V = sorted(adj)
    # girth
    g = None
    for s in V:
        dist = {s: 0}; par = {s: None}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if w not in dist: dist[w] = dist[u] + 1; par[w] = u; dq.append(w)
                elif par[u] != w:
                    c = dist[u] + dist[w] + 1
                    g = c if g is None or c < g else g
    # onion depths
    S = [set(V)]
    while S[-1]:
        S.append({v for v in S[-1] if len(adj[v] & S[-1]) >= 3})
    D = len(S) - 2
    print(f"{fam} L={L}: |V|={len(V)} |E|={len(E)} girth={g} depth D={D}; " +
          "; ".join(f"|S_{i}|={len(S[i])}" + (f" {sorted(S[i])}" if 0 < i and len(S[i]) <= 10 else "") for i in range(1, D + 1)))
    # the onion order and its degeneracy
    lev = {}
    order = []
    for j in range(D, -1, -1):
        layer = sorted(S[j] - (S[j + 2] if j + 2 < len(S) else set()))
        kind = "pt" if j % 2 else "pl"
        order += [(kind, v) for v in layer]
    order += [("pt", v) for v in sorted(set(V) - S[1])]
    assert len({e for e in order}) == 2 * len(V), "every vertex gets one point and one plane"
    pos = {e: t for t, e in enumerate(order)}
    worst = 0; hist = {}
    for (kind, v) in order:
        other = "pl" if kind == "pt" else "pt"
        earlier = sum(1 for w in adj[v] | {v} if pos[(other, w)] < pos[(kind, v)])
        hist[earlier] = hist.get(earlier, 0) + 1; worst = max(worst, earlier)
    # a witness of the generic stratum: place every element at a random rational point of the linear space its earlier
    # incident elements allow, and check that those earlier elements are independent (rank = their number) at every step
    rng = random.Random(20260923); vec = {}; bad = []
    for (kind, v) in order:
        other = "pl" if kind == "pt" else "pt"
        prev = [vec[(other, w)] for w in sorted(adj[v] | {v}) if (other, w) in vec]
        basis, rk = nullspace(prev)
        if rk != len(prev): bad.append((kind, v, len(prev), rk))
        vec[(kind, v)] = [sum(rng.randint(-9, 9) * b[i] for b in basis) for i in range(4)]
        if not any(vec[(kind, v)]): bad.append((kind, v, "zero"))
    print(f"generic-stratum witness (seed 20260923, coefficients in [-9, 9]): {'every step independent -> the generic stratum is NONEMPTY' if not bad else 'DEPENDENT at ' + str(bad[:5])}")
    print(f"onion order: {len(order)} elements; earlier-neighbour counts {dict(sorted(hist.items()))}; max {worst} -> "
          f"{'3-DEGENERATE' if worst <= 3 else 'NOT 3-degenerate'}")
    # the strict count over unions of whole branch paths
    B = [v for v in V if len(adj[v]) != 2]
    paths = []; seen = set()
    for b in B:
        for w in adj[b]:
            if (b, w) in seen: continue
            p = [b, w]
            while len(adj[p[-1]]) == 2:
                nxt = next(x for x in adj[p[-1]] if x != p[-2]); p.append(nxt)
            seen.add((p[-1], p[-2])); seen.add((b, w))
            paths.append(p)
    print(f"branch vertices {len(B)}, branch paths {len(paths)} (lengths {sorted(len(p) - 1 for p in paths)})")
    best = None; arg = None
    for m in range(1, 1 << len(paths)):
        use = [paths[t] for t in range(len(paths)) if m >> t & 1]
        vs = set(); es = 0
        for p in use: vs |= set(p); es += len(p) - 1
        # connectivity
        start = next(iter(vs)); comp = {start}; dq = deque([start])
        while dq:
            u = dq.popleft()
            for p in use:
                if u in (p[0], p[-1]) or u in p:
                    for x in p:
                        if x not in comp: comp.add(x); dq.append(x)
        if comp != vs: continue
        sl = 6 * len(vs) - 7 - 5 * es
        if best is None or sl < best: best = sl; arg = [(p[0], p[-1], len(p) - 1) for p in use]
    print(f"strict count: min slack 6|V| - 7 - 5|E| over connected unions of branch paths = {best} -> "
          f"{'LEGAL' if best >= 0 else 'VIOLATED'};  attained by {arg}")


if __name__ == "__main__":
    main()
