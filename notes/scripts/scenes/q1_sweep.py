"""Q1 sweep: the combinatorial identity on many graphs, any degrees.

Checks, for every simple graph tested:
  (1) defvb == def2                      (the face-merging lemma)
  (2) 4n - rcount == 3 + def2            (Whiteley count matroid rank on S_G)
  (3) dim of scenes == 3 + def2 at a random rational picture (subset only),
      and == dim L(q) when every closed neighbourhood has >= 3 members.
Also counts the graphs where some partition attaining defvb has a vertex
with two neighbours in another part (so the merge step is really used).
"""
import itertools
import random
import sys

from q1_count import (Rat, count_rank, deficiencies, from_edges, lifting_dim,
                      random_picture, scene_dim, set_partitions, two_k4_at_vertex)


def vb_witness_needs_merge(g, dvb):
    """Is there a partition attaining defvb with a vertex having >= 2
    neighbours in a foreign part?"""
    n, E, adj = g
    for lab, k in set_partitions(n):
        vb = sum(len({lab[x] for x in adj[w]} - {lab[w]}) for w in range(n))
        if 3 * (k - 1) - vb == dvb:
            for w in range(n):
                cnt = {}
                for x in adj[w]:
                    if lab[x] != lab[w]:
                        cnt[lab[x]] = cnt.get(lab[x], 0) + 1
                if any(c >= 2 for c in cnt.values()):
                    return True
    return False


def check(g, rng, with_dim):
    n, E, adj = g
    d2, dvb = deficiencies(g)
    rc = count_rank(g)
    ok = (dvb == d2) and (4 * n - rc == 3 + d2)
    sd = ld = None
    if with_dim and n >= 1:
        pic = random_picture(g, Rat, rng) if all(len(a) >= 2 for a in adj) else None
        if pic is None:
            # pictures need only distinct adjacent points here; use a parabola-ish
            # random picture (no three collinear with high probability)
            while True:
                pic = [(Rat.rand(rng), Rat.rand(rng)) for _ in range(n)]
                if all(pic[u] != pic[v] for u, v in E):
                    break
        sd, _ = scene_dim(g, pic, Rat)
        ok &= (sd == 3 + d2)
        if all(len(a) >= 2 for a in adj):
            ld = lifting_dim(g, pic, Rat)
            ok &= (ld == sd)
    return ok, d2, dvb, rc, sd, ld


def main():
    rng = random.Random(1109)
    total = bad = 0
    merge_used = 0
    # (A) every labelled simple graph on n <= 6 vertices
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2))
        cnt = 0
        for mask in range(1 << len(pairs)):
            edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
            g = from_edges(n, edges)
            ok, d2, dvb, rc, _, _ = check(g, rng, with_dim=False)
            total += 1
            cnt += 1
            if not ok:
                bad += 1
                print("MISMATCH", n, edges, d2, dvb, rc)
        print(f"n={n}: all {cnt} labelled simple graphs checked (identities (1),(2))")
        sys.stdout.flush()
    # (B) random graphs n = 7..10, mixed densities, with dimension checks
    dimchecked = 0
    for n in range(7, 11):
        trials = 120 if n <= 8 else 40
        for t in range(trials):
            p = rng.choice([0.2, 0.3, 0.4, 0.5, 0.7])
            edges = [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]
            g = from_edges(n, edges)
            with_dim = (t % 4 == 0)
            ok, d2, dvb, rc, sd, ld = check(g, rng, with_dim)
            total += 1
            dimchecked += with_dim
            if n <= 8 and vb_witness_needs_merge(g, dvb):
                merge_used += 1
            if not ok:
                bad += 1
                print("MISMATCH", n, edges, d2, dvb, rc, sd, ld)
        print(f"n={n}: {trials} random graphs checked")
        sys.stdout.flush()
    # (C) a hand-made case where an optimal vertex-boundary partition has a
    # vertex with two neighbours in another part: two K4s and a hub w of
    # degree 4 adjacent to two vertices of each.
    hub = from_edges(9, [(a, b) for a, b in itertools.combinations(range(4), 2)] +
                     [(a, b) for a, b in itertools.combinations(range(4, 8), 2)] +
                     [(8, 0), (8, 1), (8, 4), (8, 5)])
    ok, d2, dvb, rc, sd, ld = check(hub, rng, True)
    print("two K4 + degree-4 hub:", dict(ok=ok, def2=d2, defvb=dvb,
                                         four_n_minus_rcount=36 - rc, scenes=sd, dimL=ld,
                                         merge_needed=vb_witness_needs_merge(hub, dvb)))
    total += 1
    bad += (not ok)
    print(f"\ntotal graphs {total}, mismatches {bad}, dimension checks {dimchecked + 1}, "
          f"random n<=8 graphs with an optimal vertex-boundary partition needing the merge: {merge_used}")


if __name__ == "__main__":
    main()
