#!/usr/bin/env python3
"""As specialprobe.py, at n given; also counts the special main pictures at which the bodies of W
do NOT all have one plane (h_w differ across W for some z in L_G(q)).

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
from specialprobe import affine_on


def main():
    rng = random.Random(4343)
    for nn in sys.argv[1:]:
        out = subprocess.run(["geng", "-c", "-d2", "-q", nn], capture_output=True, text=True).stdout
        found = flat = onepanel = 0
        example = None
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
                        found += 1
                        flat += all(affine_on(s[:n], q, W) for s in sols)
                        same = all(len({F.h_of(s, n, w) for w in W}) == 1 for s in sols)
                        onepanel += same
                        if not same and example is None:
                            example = (line, W, v)
                        break
        print(f"n={nn}: special main pictures {found}; W's points coplanar {flat}; "
              f"W one plane at every body {onepanel}; first exception {example}")


if __name__ == "__main__":
    main()
