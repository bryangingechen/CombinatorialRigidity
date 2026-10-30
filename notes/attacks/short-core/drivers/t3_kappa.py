#!/usr/bin/env python3
"""SHORT-CORE workbook S16's control on T3's danger cells: kappa = dim(Pi_a & Pi_b) per cell.

    python3 notes/attacks/short-core/drivers/t3_kappa.py --seed 1 [--dims 4]

The cells are `strata.py`'s (`short_danger`, seed-independent: Strata Result 24's 72 at d = 4).
At each, stage 1 of `short_cell` is redrawn from this seed: a picture q, heights from
`pd_pencil` on L_G''(q), and the planes Pi_a, Pi_b of a and b in G'' (`plane_of`).  Reported per
cell: kappa, and the numbers of neighbours of a and of b in V1.  S16 predicts kappa <= 2 at every
danger cell at d = 4.  kappa is upper semicontinuous (the planes meet in more only on a closed
set), so a draw with kappa <= 2 certifies kappa <= 2 at general base data; a draw with kappa = 3
would be a bound only, and is redrawn up to three times before it is reported.  `strata.py` is
imported read-only.  Exit status 1 if a cell keeps kappa = 3.
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, os.pardir, os.pardir, "scripts", "strata"))
import strata  # noqa: E402
from strata import (Degenerate, Sampler, SHORT_FAMS, body_guard, lifting_space,  # noqa: E402
                    pd_pencil, plane_of, rank, short_danger)


def stage1_kappa(s, spec, d):
    k = spec.k
    n1, E1, _, _ = spec.base()
    n2, E2, _, _, a, b = spec.graph(k - 1)
    q2 = [s.vec(2) for _ in range(n2)]
    b2, H2 = pd_pencil(s, n2, E2, d, q2, lifting_space(n2, E2, q2))
    body_guard(n2, E2, H2)
    PA, PB = plane_of(b2, E2, a), plane_of(b2, E2, b)
    strata.need(len(PA) == 3 and len(PB) == 3, "the planes of a, b in G''")
    deg1 = lambda v: sum(1 for e in E1 if v in e)  # noqa: E731
    return len(PA) + len(PB) - rank(PA + PB), deg1(a), deg1(b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--dims", type=int, nargs="+", default=[4])
    args = ap.parse_args()
    s = Sampler(args.seed)
    bad, hist = 0, {}
    for d in args.dims:
        D = (d + 1) * d // 2
        for fam in SHORT_FAMS:
            for k in range(3, D - 1):
                for spec in short_danger(fam, d, k):
                    kap = None
                    for _ in range(4):
                        try:
                            kap, da, db = stage1_kappa(s, spec, d)
                        except Degenerate:
                            continue
                        if kap < 3:
                            break
                    if kap is None:
                        print(f"{fam:5}{spec.label():18}{d:>2}{k:>3}  degenerate at every draw")
                        bad += 1
                        continue
                    hist[(d, kap)] = hist.get((d, kap), 0) + 1
                    bad += d == 4 and kap == 3
                    print(f"{fam:5}{spec.label():18}{d:>2}{k:>3}  kappa {kap}  "
                          f"deg_V1(a) {da}  deg_V1(b) {db}")
    print("cells by (d, kappa): " + ", ".join(f"{key}: {v}" for key, v in sorted(hist.items())))
    print("OK" if bad == 0 else f"FAILED: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
