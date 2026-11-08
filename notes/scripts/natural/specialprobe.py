#!/usr/bin/env python3
"""Phase 43a, flatness at special main pictures (read-only scratch probe, exact Fractions).

Population: `geng -c -d2 -q n` for the given n. For every planar-rigid set W and every v in W
with exactly two neighbours a, b in G[W] and at least one neighbour outside W, put q_v on the
line through q_a and q_b (so q is not admissible for G[W]) at random otherwise. Keep q when it is
admissible for G and main for G (dim L_G(q) = 3 + def2(G), the least value by
lem:pencil-lifting-space-deficiency). Check: is every z in L_G(q) affine on W?

Written by the flatness reader of 2026-11-07 (`notes/Phase43a.md`, its item); banked in Phase
43a with this paragraph and without its hand-rolled `sys.path` line (a sibling import resolves
from the script's own directory), otherwise as run. Invocations: `notes/scripts/README.md`
section 3, `natural/`.
"""
import random
import subprocess
import sys
from fractions import Fraction as Fr

import flatprobe as F


def affine_on(z, q, W):
    """Is z|W = alpha x + beta y + gamma for one triple?"""
    rows = [[Fr(q[w][0]), Fr(q[w][1]), Fr(1), -z[w]] for w in W]
    return F.rank([r[:3] for r in rows]) == F.rank(rows)


def main():
    rng = random.Random(4343)
    for nn in sys.argv[1:]:
        out = subprocess.run(["geng", "-c", "-d2", "-q", nn], capture_output=True, text=True).stdout
        cases = mainspecial = flat = 0
        for line in out.splitlines():
            n, adj = F.decode_g6(line)
            full = (1 << n) - 1
            d2 = F.deficiency_table(n, adj, 3)
            for S in range(1, full + 1):
                if bin(S).count("1") < 2 or d2[S] != 0:
                    continue
                W = [v for v in range(n) if S >> v & 1]
                for v in W:
                    inW = [w for w in adj[v] if S >> w & 1]
                    if len(inW) != 2 or len(adj[v]) == 2:
                        continue
                    cases += 1
                    for _ in range(5):
                        q = [(Fr(rng.randint(-60, 60)), Fr(rng.randint(-60, 60))) for _ in range(n)]
                        a, b = inW
                        t = Fr(rng.randint(2, 9), rng.randint(2, 9) + 10)
                        q[v] = (q[a][0] + t * (q[b][0] - q[a][0]), q[a][1] + t * (q[b][1] - q[a][1]))
                        if not F.admissible(n, adj, q):
                            continue
                        sols = F.lifting_solutions(n, adj, q)
                        if len(sols) != 3 + d2[full]:
                            continue
                        mainspecial += 1
                        flat += all(affine_on(s[:n], q, W) for s in sols)
                        break
        print(f"n={nn}: (W, v) cases {cases}; special main pictures found {mainspecial}; "
              f"W affine at all of L_G(q) {flat}")


if __name__ == "__main__":
    main()
