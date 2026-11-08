#!/usr/bin/env python3
"""Cross-check flatprobe.deficiency_table (DP) against brute-force set partitions, D = 3 and 6,
on every induced subgraph of every graph of `geng -c -d2 -q n` (n given), and on the witnesses.

Written by the flatness reader of 2026-11-07 (`notes/Phase43a.md`, its item); banked in Phase
43a with this paragraph and without its hand-rolled `sys.path` line (a sibling import resolves
from the script's own directory), otherwise as run. Invocations: `notes/scripts/README.md`
section 3, `natural/`.
"""
import subprocess
import sys

import flatprobe as F


def partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def brute(adj, W, D):
    best = None
    for P in partitions(W):
        lab = {v: i for i, part in enumerate(P) for v in part}
        cross = sum(1 for u in W for v in adj[u] if v in lab and u < v and lab[u] != lab[v])
        val = D * (len(P) - 1) - (D - 1) * cross
        best = val if best is None else max(best, val)
    return best


def check(n, adj):
    bad = 0
    for D in (3, 6):
        tab = F.deficiency_table(n, adj, D)
        for S in range(1, 1 << n):
            W = [v for v in range(n) if S >> v & 1]
            if tab[S] != brute(adj, W, D):
                bad += 1
    return bad


tot = mism = 0
for nn in sys.argv[1:]:
    out = subprocess.run(["geng", "-c", "-d2", "-q", nn], capture_output=True, text=True).stdout
    for line in out.splitlines():
        n, adj = F.decode_g6(line)
        tot += 1
        mism += check(n, adj)
for name, (n, E) in F.WITNESSES.items():
    if n <= 7:
        _, adj = F.from_edges(n, E)
        tot += 1
        mism += check(n, adj)
        print(name, "def2(G) brute", brute(adj, list(range(n)), 3), "def3(G) brute", brute(adj, list(range(n)), 6))
n, E = F.WITNESSES["doubled_triangle"]
_, adj = F.from_edges(n, E)
print("doubled_triangle def2(G) brute", brute(adj, list(range(n)), 3))
print(f"graphs {tot}; (subset, D) mismatches {mism}")
