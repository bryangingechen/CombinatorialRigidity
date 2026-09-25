"""zbridged.py -- §(K-main) Step MC19, the second reading of 2026-09-25 ((MC-158)): the populations Step MC19's
other drivers do not reach.

Every Step MC19 driver draws from SIMPLE 2EC graphs (maincomp.two_ec_graphs, zstuck/zrand filtered by
is_2ec), so no bridge ever occurs and the lollipop step (MC-127)(c) is never exercised ("No lollipop
step occurred").  (MC-123) is stated for every finite simple graph; (MC-129)/(MC-130)/(MC-133) for
every graph satisfying (H) (connected, min degree >= 2), bridges allowed.  This script checks:

  Part 1  (MC-123) (<=) on EVERY connected simple graph on 2..N1 vertices (any degrees, so degree-1
          vertices and trees included): F1 and F2 => a hub-plane-chart draw satisfying all four
          IsNondegPencilRealization conjuncts with explicit normals (zcore.nondeg).  A draw that
          passes is an exhibited witness (exact arithmetic), i.e. PencilNondegFeasible over Q.
          Also (=>) consistency: at graphs failing F1 or F2 no draw may pass (the landed Lean
          theorems say none exists; a pass would contradict them).
  Part 2  on every connected simple NON-2EC graph with min degree >= 2 on 3..N2 vertices that is
          feasible: (MC-129)'s lemma and (MC-130)'s reduction bookkeeping (zlemma.reduce_to_base,
          which asserts the lemma, feasibility, (H) and shrinking at every step), with the step
          kinds counted; then a direct certificate of (MC-133)(ii)'s conclusion over Q: one of <= 3
          seeded draws nondegenerate with rank mod 2^61-1 equal to 6(|V|-1) - def3 (rank_p is a lower
          bound for the Q-rank and the Q-rank is <= the target, so equality certifies).
          Also (MC-125)(ii)'s corollary (e3check's test) on the same population.

Exact (integers / Fractions; pebble-game deficiencies).  Seeded: draws use random.Random(f'readerA:...') (the seed strings keep the second reader's
scratch name, so the landed figures reproduce byte for byte).
Part 3  zrand.build's sampler without its is_2ec filter (non-2EC (H) feasible samples): the same
          lemma asserts and direct certificates.
Run from the repository root:  PYTHONHASHSEED=0 python3 notes/scripts/w4/zbridged.py [--n1 8] [--n2 8] [--p3 N --seed S]
"""
import argparse
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zcore import (F1, F2, zdraw, complete_normals, nondeg, rank_p, target, def2, hubs_of,  # noqa: E402
                   verts_of)
from zsurvey import is_Aprime, rigid_pair  # noqa: E402
from zlemma import reduce_to_base  # noqa: E402
from maincomp import connected_graphs, decode  # noqa: E402
from kbare_common import is_2ec  # noqa: E402
from exactcore import neighbors  # noqa: E402


def certify_nondeg(E, tag, draws=5):
    for d in range(draws):
        r = zdraw(E, random.Random(f'readerA:{tag}:{d}'))
        if r is None:
            continue
        n, pt = r
        ok, _ = nondeg(E, complete_normals(E, n, pt), pt)
        if ok:
            return True, (n, pt)
    return False, None


def part1(nmax):
    lev = connected_graphs(nmax)
    tot = feas = cert = infeas = infeas_pass = 0
    fails = []
    for n in range(2, nmax + 1):
        for code in lev[n]:
            E = decode(n, code)
            tot += 1
            if F1(E) and F2(E):
                feas += 1
                ok, _ = certify_nondeg(E, f'p1:{n}:{code}')
                cert += ok
                if not ok:
                    fails.append(E)
            else:
                infeas += 1
                # zdraw needs every |closedHubNbhd| <= 3 to produce a point at all; try only then
                if F1(E):
                    ok, _ = certify_nondeg(E, f'p1x:{n}:{code}', draws=2)
                    infeas_pass += ok
    print(f'Part 1 (MC-123): connected simple graphs on 2..{nmax} vertices: {tot}; F1&F2: {feas}, '
          f'nondegenerate witness exhibited at {cert}; F1-but-not-F2 or not-F1: {infeas}, '
          f'draws passing all four conjuncts there: {infeas_pass} (must be 0)')
    for E in fails:
        print('   NO WITNESS FOUND', E)


def part2(nmax):
    lev = connected_graphs(nmax)
    pop = n_feas = n_rigid = n_cert = 0
    kinds = {}
    n_na = n_na_ok = 0
    misses = []
    for n in range(3, nmax + 1):
        for code in lev[n]:
            E = decode(n, code)
            nb = neighbors(E)
            if any(len(nb[v]) < 2 for v in nb) or is_2ec(E):
                continue
            pop += 1
            if not (F1(E) and F2(E)):
                continue
            n_feas += 1
            tr = []
            reduce_to_base(E, tr)
            if len(tr) > 1:
                n_rigid += 1
            for t in tr:
                kinds[t] = kinds.get(t, 0) + 1
            tgt = target(E)
            got = False
            for d in range(3):
                r = zdraw(E, random.Random(f'readerA:p2:{n}:{code}:{d}'))
                nn, pt = r
                ok, _ = nondeg(E, complete_normals(E, nn, pt), pt)
                if ok and rank_p(E, pt) == tgt:
                    got = True
                    break
            n_cert += got
            if not got:
                misses.append(E)
            if not is_Aprime(E):
                n_na += 1
                V = verts_of(E)
                H = sorted(hubs_of(E), key=str)
                s = 3 * len(V) - 3 - 2 * len(E)
                hp = [(u, w) for i, u in enumerate(H) for w in H[i + 1:] if rigid_pair(E, u, w)]
                if def2(E) == s and not hp:
                    n_na_ok += 1
                else:
                    print('   (MC-125)(ii) corollary FAILS at', E, def2(E), s, hp)
    print(f'Part 2: connected simple non-2EC graphs, min degree >= 2, 3..{nmax} vertices: {pop}; feasible '
          f'{n_feas}, {n_rigid} with a def2-rigid subgraph; every one reduced to a base graph '
          f'(zlemma asserts); steps used {kinds}')
    print(f'Part 2: nondegenerate attaining draw (HasGenericPencilRealization over Q, exhibited) at '
          f'{n_cert}/{n_feas}; (MC-125)(ii) corollary at feasible non-A-prime: {n_na_ok}/{n_na}')
    for E in misses:
        print('   NOT CERTIFIED (a lower bound only)', E)


def part3(draws, seed, maxv):
    """zrand.build's sampler (hub skeleton + random 1..3-chains, closed or open), WITHOUT its is_2ec
    filter: keep the samples satisfying (H), F1, F2 and NOT 2EC.  Sampler support: zrand.build only."""
    from zrand import build
    from zears import satisfies_H, key
    rng = random.Random(seed)
    seen = set()
    n = n_rigid = n_cert = 0
    kinds = {}
    for i in range(draws):
        E = build(rng, rng.randint(3, 6))
        if not E or len(verts_of(E)) > maxv or not satisfies_H(E) or is_2ec(E) or not (F1(E) and F2(E)):
            continue
        k_ = key(E)
        if k_ in seen:
            continue
        seen.add(k_)
        n += 1
        tr = []
        reduce_to_base(E, tr)
        n_rigid += len(tr) > 1
        for t in tr:
            kinds[t] = kinds.get(t, 0) + 1
        tgt = target(E)
        got = False
        for d in range(3):
            nn, pt = zdraw(E, random.Random(f'readerA:p3:{seed}:{i}:{d}'))
            ok, _ = nondeg(E, complete_normals(E, nn, pt), pt)
            if ok and rank_p(E, pt) == tgt:
                got = True
                break
        n_cert += got
        if not got:
            print('   NOT CERTIFIED (a lower bound only)', E)
    print(f'Part 3 (seed {seed}, {draws} zrand.build draws, |V| <= {maxv}, distinct, non-2EC, (H), F1&F2): '
          f'{n}; {n_rigid} with a def2-rigid subgraph; steps used {kinds}; nondegenerate attaining draw '
          f'exhibited at {n_cert}/{n}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n1', type=int, default=7)
    ap.add_argument('--n2', type=int, default=8)
    ap.add_argument('--p3', type=int, default=0, help='Part 3 draws (0: skip)')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--maxv', type=int, default=14)
    a = ap.parse_args()
    t = time.time()
    part1(a.n1)
    print(f'  [{time.time() - t:.0f} s]')
    t = time.time()
    part2(a.n2)
    print(f'  [{time.time() - t:.0f} s]')
    if a.p3:
        t = time.time()
        part3(a.p3, a.seed, a.maxv)
        print(f'  [{time.time() - t:.0f} s]')


if __name__ == '__main__':
    main()
