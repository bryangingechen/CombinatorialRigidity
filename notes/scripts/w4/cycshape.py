#!/usr/bin/env python3
"""cycshape.py -- §(K-main) Step MC21, the second reading of 2026-09-25 (ported from the reader's scratch):
the shape (cycle length L, arcs d1,d2, pendant lengths p,p') of each Case II-cyclic class
quotient printed by findcyc.py (read on stdin). Deterministic, pure combinatorics."""
import sys, ast, re
from collections import deque
for line in sys.stdin:
    m = re.search(r"A (\d+) B (\d+) QE (\[.*?\]) cells", line)
    if not m:
        continue
    A, B, QE = int(m.group(1)), int(m.group(2)), ast.literal_eval(m.group(3))
    adj = {}
    for i, j in QE:
        adj.setdefault(i, set()).add(j); adj.setdefault(j, set()).add(i)
    n = len(adj); e = len(QE)
    # 2-core
    deg = {v: len(adj[v]) for v in adj}; core = set(adj)
    q = deque(v for v in adj if deg[v] == 1)
    while q:
        v = q.popleft()
        if v not in core: continue
        core.discard(v)
        for w in adj[v]:
            if w in core:
                deg[w] -= 1
                if deg[w] == 1: q.append(w)
    def dist_to_core(s):
        seen = {s: 0}; dq = deque([s])
        while dq:
            v = dq.popleft()
            if v in core: return seen[v], v
            for w in adj[v]:
                if w not in seen: seen[w] = seen[v] + 1; dq.append(w)
    p, ca = dist_to_core(A); pp, cb = dist_to_core(B)
    # arcs between ca, cb on the cycle (unicyclic)
    def cdist(s, t, banned=None):
        seen = {s: 0}; dq = deque([s])
        while dq:
            v = dq.popleft()
            if v == t: return seen[v]
            for w in adj[v]:
                if w in core and w not in seen and (banned is None or (v, w) != banned):
                    seen[w] = seen[v] + 1; dq.append(w)
    L = len(core); d1 = cdist(ca, cb); d2 = L - d1
    print(f"n_cls={n} e={e} cyc={e-n+1} L={L} arcs={tuple(sorted((d1,d2)))} p+p'={p+pp} (p={p}, p'={pp}) line={line.split()[0]}:y{line.split()[2]}")
