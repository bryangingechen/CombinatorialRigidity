#!/usr/bin/env python3
"""SHORT-CORE workbook S54: the exact control for S52 and S53 (the need question N, brief section 6).

    PYTHONHASHSEED=0 python3 notes/attacks/short-core/drivers/need_n.py [--dims 3,4,5,6,7,8] [--lmax 4,5]

No point is drawn and nothing is seeded here: every figure is exact integer combinatorics through
strata.py's T5 functions (read-only), so the output does not vary with any seed.

Population.  strata.py's T5 cores (`COV_CORES`: th3, th4, hub, same, k4, w4, prism, k33, cube,
petersen; every core body of degree >= 3, each 2-connected), every core edge a path of 1..LMAX
edges, by `cov_population(name, d, auts, LMAX)` unchanged: every length vector up to the core's
automorphisms where LMAX^E <= COV_EXHAUST (4096), else the first COV_PER (60) of COV_TRIES (3000)
box draws seeded by (core, d, LMAX) alone; kept if simple, sparse (no planar-rigid set) and
def_3 >= d - 2 (T5's content range, a superset of 42c's def_3 >= C(d, 2) - 2, which is reported).
Such a graph is 2-connected, not a cycle and sparse: past rows 1-5 but for def_3 = def_D, which
the driver ignores (S53 does not use it).  LMAX = 4 gives chains of k <= 3 bodies (S53 (a)'s
hypothesis); LMAX = 5 adds k = 4 (S53 (b)'s free rows).  Then Petersen with every edge a path of
L edges, L = 2..6, at each d.  Caps: the cores (10, at most 10 bodies and 15 edges), LMAX, and
the draw caps above for cores with LMAX^E > 4096.

Per cell and dimension d (D = C(d+1, 2)):
  rows  `cov_cell`'s rows at D; free as brief section 6 reads `cov_tag`, with the `short` rows at
        k >= 4 free (S35): flat, core, long, ear, split, short at k >= 4, one at d = 4 with no
        shared neighbour.  K3 marks a `short` row at k = 3 (SHORT-CORE's k = 3 row).
  S52   at every chain with k >= 2 and s_D(V1) <= 0 (s_D counted directly on the expanded G[V1],
        and checked against S53's formula sum_{j != i} L_j - D(e - nc)): a core at D whose W
        avoids the chain's interior (`core_avoiding`, cov_core's tests with that path kept out).
Asserted (exit 1 otherwise): the formula; S52 at every such chain, every d; S53 (a) at D >= 12
(s_D(V1) <= -4 and a core avoiding the chain, at every chain with k in {2, 3} of a cell whose
chains all have k <= 3); S53 (b) at d >= 5 (every cell with a K3 row has a free row other than
it).  Reported: at d = 4 the cells whose only non-free rows include K3 (T5's need witnesses).
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir, os.pardir, os.pardir, "scripts", "strata"))
import strata as st  # noqa: E402  -- read-only reuse


def free(row, k, sh, d):
    """Brief section 6's free rows: cov_tag's GEN, with short rows at k >= 4 free (S35)."""
    if row == "short" and k >= 4:
        return True
    return st.cov_tag(row, k, sh, d) == "GEN"


def s_D(n, E, D):
    return D * (n - 1) - (D - 1) * len(E)


def core_avoiding(nc, paths, D, d3, i):
    """`cov_core`'s search and tests, over the W that leave out path i's interior."""
    nW = nc + sum(L - 1 for _, _, L in paths)
    for U, S, size in st.core_sets(nc, paths, D, twos=True):
        if size == nW or i in S:
            continue
        if any(sum(1 for u, v, L in paths if L == 1 and z in (u, v) and (U >> (u + v - z)) & 1) >= 2
               for z in range(nc) if not (U >> z) & 1):
            continue
        sub = st.core_induce(nc, paths, U, S)
        if (st.core_def(*sub, D) == 0
                and st.core_def(*sub, 3) + st.core_def(*st.core_contract(nc, paths, U, S), 3) <= d3):
            return U, S
    return None


def cell(nc, paths, d, tally):
    """One graph at d: its rows, S52 per chain, S53's assertions.  Returns the mismatch count."""
    D, bad = (d + 1) * d // 2, 0
    c = st.cov_cell(nc, paths, d)
    e = len(paths)
    ks = [L - 1 for _, _, L in paths if L >= 2]
    for i, (a, b, L) in enumerate(paths):
        if L < 3:
            continue
        G1 = paths[:i] + paths[i + 1:]
        n1, E1 = st.core_expand(nc, G1)
        sv = s_D(n1, E1, D)
        bad += sv != sum(LL for _, _, LL in G1) - D * (e - nc)
        if D >= 12 and max(ks) <= 3:
            bad += sv > -4
        if sv <= 0:
            tally["s52"] += 1
            if core_avoiding(nc, paths, D, c["d3"], i) is None:
                bad += 1
                print(f"  S52 FAILS: d = {d}, paths {paths}, chain {i}")
    rows = c["rows"]
    k3 = any(r == "short" and k == 3 for r, k, _ in rows)
    has_free = any(free(r, k, sh, d) for r, k, sh in rows)
    tally["cells"] += 1
    tally["range42c"] += c["d3"] >= d * (d - 1) // 2 - 2
    tally["k3"] += k3
    tally["core"] += c["core"] is not None
    if k3 and not has_free:
        tally["needK3"] += 1
        bad += d >= 5
    return bad, c, k3, has_free


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", default="3,4,5,6,7,8")
    ap.add_argument("--lmax", default="4,5")
    args = ap.parse_args()
    dims = [int(x) for x in args.dims.split(",")]
    lmaxes = [int(x) for x in args.lmax.split(",")]
    print("S54: S52 and S53 on T5's cores (see the docstring for population and caps)")
    bad, auts = 0, {}
    for lmax in lmaxes:
        for d in dims:
            D = (d + 1) * d // 2
            tally = dict.fromkeys(("cells", "range42c", "k3", "core", "needK3", "s52"), 0)
            for name, (nc, ce) in st.COV_CORES.items():
                if name not in auts:
                    auts[name] = st.core_auts(nc, ce)
                for ls, paths in st.cov_population(name, d, auts[name], lmax):
                    b, c, k3, hf = cell(nc, paths, d, tally)
                    bad += b
                    if k3 and not hf:
                        print(f"  d = {d}: {st.cov_label(name, ls)} needs a K3 row; rows "
                              f"{st.cov_rowtext(c)}")
            print(f"LMAX {lmax}, d = {d} (D = {D}): {tally['cells']} graphs, {tally['range42c']} in "
                  f"42c's range; {tally['k3']} with a K3 row, {tally['needK3']} of them with no "
                  f"other free row; {tally['core']} with a core at D; S52 checked at "
                  f"{tally['s52']} chains")
    print("Petersen, every edge a path of L edges: d, L, def_3, def_D, core, rows")
    nc, ce = st.PETERSEN
    for d in dims:
        for L in range(2, 7):
            paths = [(u, v, L) for u, v in ce]
            tally = dict.fromkeys(("cells", "range42c", "k3", "core", "needK3", "s52"), 0)
            b, c, k3, hf = cell(nc, paths, d, tally)
            bad += b
            print(f"  d = {d} L = {L}: {c['d3']:>3} {c['dG']:>3} "
                  f"{'core' if c['core'] is not None else '-':>5}  "
                  f"{'NEEDS K3  ' if k3 and not hf else ''}{st.cov_rowtext(c)}")
    print(f"mismatches (asserted): {bad}")
    if bad:
        sys.exit(1)
    print("OK")


if __name__ == "__main__":
    main()
