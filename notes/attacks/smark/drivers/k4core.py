"""O7e-c shape check (workbook S38(iv), review 5): the subdivided K4 whose centre
`c` has three spokes of length 1 to `x1, x2, x3` and whose rim paths `x_i -- x_j`
have length `L` (default 6).  In the 2-core every vertex of degree >= 3 is big, so
`k_c = |Big ∩ N[c]| = 4`: an O7e-c instance.  Prints |V|, |E|, the girth, and the
minimum over all connected vertex subsets S (|S| >= 2, >= 1 edge) of the strict
habitat slack 6|S| - 7 - 5|E(S)| (S19(viii) / S35(i)); induced subgraphs suffice,
since dropping edges only raises the slack.  Exhaustive over all 2^|V| subsets,
exact integers, stdlib only, no randomness.

    timeout 600 python3 notes/attacks/smark/drivers/k4core.py [L]
"""
import itertools, sys
from collections import deque

def build(L):
    adj = {}
    def edge(a, b):
        adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    X = ['x1', 'x2', 'x3']
    for x in X: edge('c', x)
    for i, (a, b) in enumerate(itertools.combinations(X, 2)):
        path = [a] + [f'p{i}_{j}' for j in range(L - 1)] + [b]
        for u, v in zip(path, path[1:]): edge(u, v)
    return adj

def girth(adj):
    best = None
    for s in adj:
        dist, par, q = {s: 0}, {s: None}, deque([s])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v], par[v] = dist[u] + 1, u; q.append(v)
                elif par[u] != v:
                    g = dist[u] + dist[v] + 1
                    best = g if best is None else min(best, g)
    return best

def connected(S, adj):
    S = set(S); s = next(iter(S)); seen = {s}; q = [s]
    while q:
        u = q.pop()
        for v in adj[u]:
            if v in S and v not in seen: seen.add(v); q.append(v)
    return len(seen) == len(S)

def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    adj = build(L); nodes = sorted(adj); n = len(nodes)
    E = sum(len(v) for v in adj.values()) // 2
    worst = None
    for mask in range(1, 1 << n):
        S = [nodes[i] for i in range(n) if mask >> i & 1]
        if len(S) < 2: continue
        Sset = set(S)
        e = sum(1 for u in S for v in adj[u] if v in Sset) // 2
        if e == 0 or not connected(S, adj): continue
        s = 6 * len(S) - 7 - 5 * e
        if worst is None or s < worst[0]: worst = (s, len(S), e)
    degs = sorted(len(adj[v]) for v in nodes)
    print(f"L={L}: |V|={n} |E|={E} girth={girth(adj)} max degree={degs[-1]} "
          f"k_c(centre)={1 + sum(1 for x in adj['c'] if len(adj[x]) >= 3)}")
    print(f"min strict slack 6|S|-7-5|E(S)| over connected S: {worst[0]} "
          f"(at |S|={worst[1]}, |E(S)|={worst[2]}) -> {'LEGAL' if worst[0] >= 0 else 'VIOLATED'}")

main()
