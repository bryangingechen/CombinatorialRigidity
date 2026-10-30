#!/usr/bin/env python3
"""oneclass.py -- ONE-CLASS: the coverage's one-body class (Phase 42a, 2026-10-29).

The lemma (`notes/Strata.md` Result 27; `notes/Phase42-design.md` section
2.3): let G be sparse (s_3(X) >= 1 for every X of two or more bodies), of
minimum degree two, with no two bodies of degree two adjacent, and let D >= 6.
If def_6(G) > 0, then a set W of least s_3 among the sets of two or more bodies
with def_D(G[W]) = 0 is a core at D: W is proper, no body outside W is
adjacent to two bodies of W, and def_3(G[W]) + def_3(G/G[W]) <= def_3(G)
(clause (7) of def:pencil-x0-reduces read at D, as `strata.cov_core` reads
it).  So a graph past the coverage's first five rows whose chains all have one
interior body has a core at D or def_6(G) = 0, and in the second case Phase
40's P^3 witness embeds in every P^d (Result 15).

Checked exactly on subdivisions of cores (2-connected, of minimum degree 3)
with every core edge a path of one or two edges, simple and sparse, so no two
bodies of degree two are adjacent.  Per cell and per D in `DS`:
  - W, a set of least s_3 among those with def_D(G[W]) = 0 (a proper one
    where one ties with V(G)), is a core whenever it is proper, and is proper
    whenever def_6(G) > 0 (the lemma);
  - W is proper exactly when `strata.cov_core` finds a core (so G has a core
    at D iff a set of least s_3 among those of def_D zero can be taken
    proper; the proof's second half);
  - where the cell has n <= BODY_CAP bodies, W's three conditions again on
    the bodies, by the 3^n DP `strata.deficiency`.
Reported: the cells, those with def_6 > 0, and the (cell, D) pairs with no
core, all with def_6 = 0, by def_3.  Exact combinatorics: no point is drawn,
and --cores' draws are seeded by the core alone.

  python3 notes/scripts/strata/oneclass.py --cores
      T5's ten cores (`strata.COV_CORES`, multigraphs among them): every
      length vector in {1, 2}^E up to the core's automorphisms, or COV_PER of
      COV_TRIES draws past COV_EXHAUST vectors (Petersen).  No cell has
      def_6 > 0: that needs a quotient with fewer than 6/5 edges per part
      past the first, so a ring of rigid blobs.
  python3 notes/scripts/strata/oneclass.py --necklaces
      Such rings (`NECKLACES`): diamonds and K4 - e joined in a cycle, every
      varying length in {1, 2}; here the lemma's hypothesis holds.
  geng -C -d3 -q n 0:12 | python3 notes/scripts/strata/oneclass.py --g6 -
      the cores nauty's `geng` (external) lists, graph6 on stdin or in a
      file, each the same way.

Verdict: the last line is `OK: every target met`, or `FAILED: ...` with exit
status 1.
"""
import argparse
import os
import random
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import strata as S  # noqa: E402  -- the sibling driver, run from this directory

DS = (6, 10, 15, 21)
BODY_CAP = 9


def g6(line):
    """A graph6 line: (n, edges)."""
    s = line.strip()
    n = ord(s[0]) - 63
    bits = [((ord(ch) - 63) >> (5 - i)) & 1 for ch in s[1:] for i in range(6)]
    pairs = [(i, j) for j in range(1, n) for i in range(j)]
    return n, [p for p, b in zip(pairs, bits) if b]


def population(nc, ce, tag):
    """Every length vector in {1, 2}^E up to the core's automorphisms (or
    COV_PER of COV_TRIES draws seeded by `tag` past COV_EXHAUST), keeping the
    simple, sparse ones."""
    auts = S.core_auts(nc, ce)
    if 2 ** len(ce) <= S.COV_EXHAUST:
        vecs, cap = product((1, 2), repeat=len(ce)), None
    else:
        R = random.Random(4000000 + tag)
        vecs = (tuple(R.randint(1, 2) for _ in ce) for _ in range(S.COV_TRIES))
        cap = S.COV_PER
    out, seen = [], set()
    for ls in vecs:
        key = min(tuple(sorted((min(p[u], p[v]), max(p[u], p[v]), L)
                               for (u, v), L in zip(ce, ls))) for p in auts)
        if key in seen:
            continue
        seen.add(key)
        paths = [(u, v, L) for (u, v), L in zip(ce, ls)]
        ones = [frozenset((u, v)) for u, v, L in paths if L == 1]
        if len(ones) == len(set(ones)) and S.core_sparse(nc, paths):
            out.append((ls, paths))
            if cap and len(out) == cap:
                break
    return out


def least_rigid(nc, paths, D):
    """(s_3, U, S) of a set W = U + its 2-paths with def_D(G[W]) = 0 and s_3
    least, a proper one first on a tie.  Every set of def_D zero has the shape
    `strata.core_sets` enumerates, and one of least s_3 contains every 2-path
    of U (its body would lower s_3 by one, keeping def_D zero), so
    twos=True loses nothing."""
    nW = S.core_expand(nc, paths)[0]
    cands = []
    for U, Sp, size in S.core_sets(nc, paths, D, twos=True):
        e = (sum(1 for u, v, L in paths if L == 1 and (U >> u) & 1 and (U >> v) & 1)
             + sum(paths[j][2] for j in Sp))
        cands.append((3 * (size - 1) - 2 * e, size == nW, U, Sp))
    for s3, _, U, Sp in sorted(cands, key=lambda t: t[:3]):
        if S.core_def(*S.core_induce(nc, paths, U, Sp), D) == 0:
            return s3, U, Sp
    return None


def is_core(nc, paths, U, Sp, D, d3):
    """`strata.cov_core`'s three conditions at W = U + Sp, by `core_def`."""
    if any(sum(1 for u, v, L in paths if L == 1 and z in (u, v) and (U >> (u + v - z)) & 1) >= 2
           for z in range(nc) if not (U >> z) & 1):
        return False
    return (S.core_def(*S.core_induce(nc, paths, U, Sp), D) == 0
            and S.core_def(*S.core_induce(nc, paths, U, Sp), 3)
            + S.core_def(*S.core_contract(nc, paths, U, Sp), 3) <= d3)


def is_core_bodies(nc, paths, U, Sp, D, d3):
    """The same on the bodies, by the 3^n DP (`strata.cov_check`'s check)."""
    n, E = S.core_expand(nc, paths)
    W, pos = {u for u in range(nc) if (U >> u) & 1}, nc
    for j, (u, v, L) in enumerate(paths):
        W |= set(range(pos, pos + L - 1)) if j in Sp else set()
        pos += L - 1
    iw = {v: i for i, v in enumerate(sorted(W))}
    EW = [(iw[u], iw[v]) for u, v in E if u in W and v in W]
    r = min(W)
    ic = {v: i for i, v in enumerate(v for v in range(n) if v not in W or v == r)}
    ic.update(dict.fromkeys(W, ic[r]))
    EC = [(ic[u], ic[v]) for u, v in E if not (u in W and v in W)]
    out = [len({w for e in E if x in e for w in e} & W) for x in range(n) if x not in W]
    return (2 <= len(W) < n and S.deficiency(len(W), EW, D) == 0 and max(out) <= 1
            and S.deficiency(len(W), EW, 3) + S.deficiency(n - len(W) + 1, EC, 3) <= d3
            and d3 == S.deficiency(n, E, 3))


# A blob of a necklace: (core bodies, core edges with their fixed lengths, or
# None where the length varies over {1, 2}, the two attachment bodies).  The
# diamond is two 2-paths between its attachments; K4 - e (the edge between its
# attachments missing) needs a subdivision in each triangle to be sparse.
BLOBS = {"dia": (2, [(0, 1, 2), (0, 1, 2)], (0, 1)),
         "k4e": (4, [(0, 2, None), (0, 3, None), (1, 2, None), (1, 3, None), (2, 3, None)],
                 (0, 1))}
NECKLACES = (("dia",) * 4, ("dia",) * 5, ("k4e", "dia", "dia", "dia"))


def necklace(blobs):
    """Every necklace on the blobs `blobs` in this cyclic order: each blob's
    second attachment joined to the next blob's first by a path of one or two
    edges, every varying length in {1, 2}; simple and sparse.  A quotient by
    the blobs and the connectors' bodies has fewer than 6/5 edges per part
    past the first when there are enough of them, so def_6(G) > 0 there."""
    nc, ce, att = 0, [], []
    for b in blobs:
        m, es, (s, t) = BLOBS[b]
        ce += [(nc + u, nc + v, L) for u, v, L in es]
        att.append((nc + s, nc + t))
        nc += m
    ce += [(att[i][1], att[(i + 1) % len(att)][0], None) for i in range(len(att))]
    free = [j for j, (_, _, L) in enumerate(ce) if L is None]
    out = []
    for ls in product((1, 2), repeat=len(free)):
        fill = dict(zip(free, ls))
        paths = [(u, v, fill.get(j, L)) for j, (u, v, L) in enumerate(ce)]
        ones = [frozenset((u, v)) for u, v, L in paths if L == 1]
        if len(ones) == len(set(ones)) and S.core_sparse(nc, paths):
            out.append((ls, paths))
    return nc, out


def run(groups):
    """Check every cell of every group (name, core bodies, cells); print the
    tallies; return the mismatches."""
    bad, cells, pos6, body = 0, 0, 0, 0
    nocore = {D: {} for D in DS}
    for name, nc, pop in groups:
        for ls, paths in pop:
            cells += 1
            d6, d3 = S.core_def(nc, paths, 6), S.core_def(nc, paths, 3)
            pos6 += d6 > 0
            n = S.core_expand(nc, paths)[0]
            for D in DS:
                lr = least_rigid(nc, paths, D)
                size = None
                if lr is not None:
                    _, U, Sp = lr
                    size = bin(U).count("1") + sum(paths[j][2] - 1 for j in Sp)
                proper = size is not None and size < n
                found = S.cov_core(nc, paths, D, d3) is not None
                if d6 > 0 and not proper:
                    bad += 1
                    print(f"  LEMMA FAILS: {name} {''.join(map(str, ls))} at D = {D}")
                if proper != found:
                    bad += 1
                    print(f"  W proper {proper}, cov_core {found}: {name} "
                          f"{''.join(map(str, ls))} at D = {D}")
                if proper:
                    if not is_core(nc, paths, U, Sp, D, d3):
                        bad += 1
                        print(f"  W NOT A CORE: {name} {''.join(map(str, ls))} at D = {D}")
                    if n <= BODY_CAP:
                        body += 1
                        bad += not is_core_bodies(nc, paths, U, Sp, D, d3)
                else:
                    nocore[D][d3] = nocore[D].get(d3, 0) + 1
                    bad += d6 != 0
    print(f"cells (simple, sparse, every core path of 1-2 edges): {cells}; "
          f"with def_6 > 0: {pos6}; W checked on the bodies (n <= {BODY_CAP}): {body}")
    for D in DS:
        h = nocore[D]
        print(f"  D = {D}: cells with no core {sum(h.values())}, every one with def_6 = 0; "
              f"by def_3: " + ", ".join(f"{k}: {h[k]}" for k in sorted(h)))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cores", action="store_true")
    ap.add_argument("--necklaces", action="store_true")
    ap.add_argument("--g6", metavar="FILE")
    args = ap.parse_args()
    if not (args.cores or args.necklaces or args.g6):
        ap.error("choose --cores, --necklaces or --g6 FILE")
    print("ONE-CLASS (Phase 42a; Phase42-design.md section 2.3, Strata.md Result 27): "
          "a sparse graph of minimum degree two with no two bodies of degree two "
          "adjacent and def_6 > 0 has a core at every D >= 6, a set of least s_3 "
          f"among those of def_D zero; checked at D = {', '.join(map(str, DS))}.")
    bad = 0
    if args.cores:
        print("population: T5's ten cores, " + ", ".join(S.COV_CORES))
        bad += run([(name, nc, population(nc, ce, tag))
                    for tag, (name, (nc, ce)) in enumerate(S.COV_CORES.items())])
    if args.necklaces:
        print("population: necklaces " + "; ".join("-".join(b) for b in NECKLACES)
              + " (every connector and free blob length in {1, 2}, not up to symmetry)")
        bad += run([("necklace " + "-".join(b),) + necklace(b) for b in NECKLACES])
    if args.g6:
        f = sys.stdin if args.g6 == "-" else open(args.g6)
        lines = [line for line in f if line.strip() and not line.startswith(">")]
        print(f"population: {len(lines)} cores in graph6")
        groups = []
        for tag, line in enumerate(lines):
            nc, ce = g6(line)
            groups.append((line.strip(), nc, population(nc, ce, tag)))
        bad += run(groups)
    print(f"mismatches (asserted): {bad}")
    if bad:
        print(f"FAILED: {bad} mismatch(es)")
        sys.exit(1)
    print("OK: every target met")


if __name__ == "__main__":
    main()
