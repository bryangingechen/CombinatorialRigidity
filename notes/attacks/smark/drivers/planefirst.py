"""planefirst.py -- combinatorial controls for the plane-first fibration of X̄(H)
(workbook S17).  Pure combinatorics, no randomness except the seeded census
subdivision lengths; every figure is exact.

For a side H with terminals u, v:  Z := {deg ≥ 3} ∪ {u, v} (the hubs of G lying in
H′, terminals included, S16(iv));  E_y := N[y] ∩ Z the hyperedge of vertex y;
s_y := |E_y|.  Checks, per side:
  * s_max and the hub-graph max degree (Case 1 of S17 ⟺ s_max ≤ 3 ⟺ hub graph has
    max degree ≤ 2 ⟺ PencilNondegFeasible, S16(v));
  * the girth-7 overlap facts: |E_y ∩ E_y'| ≤ 2, with equality only for adjacent
    y, y' ∈ Z and E_y ∩ E_y' = {y, y'};
  * Lemma P: J_A := Σ_y (|E_y ∩ A| − 1)⁺ ≤ 3|A| − 4 for every A ⊆ Z, 2 ≤ |A| ≤ CAP_A;
  * Lemma L: J_line(L) := #{y : E_y ⊆ L, |E_y| = 3} ≤ 2(|L| − 2) − 1 for every
    L ⊆ Z, 3 ≤ |L| ≤ CAP_L;
  * the habitat count 5|E(K)| ≤ 6(|V(K)| − 1) on the side itself (report only: the
    side is a proper subgraph of G, so it must hold when the side comes from a
    habitat member; the library sides are not all habitat members).
Population: the 23 sideprof sides, the 13 census skeletons with every edge
subdivided into 3 (and a seeded sample of length tuples in {2,3,4} with girth ≥ 7),
the adversarial `sk4` sides, and the two hub-graph configurations from the
session-7 recovery note (K4 and K_{3,3} subdivided into length-3 branches).
Run from the repository root:
  timeout 600 python3 notes/attacks/smark/drivers/planefirst.py
"""
import itertools
import os
import random
import sys
from collections import defaultdict, deque

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'scripts'))
import sideprof as SP          # noqa: E402
import census as CE            # noqa: E402
import adversarial as AD       # noqa: E402

CAP_A = 6
CAP_L = 6


def nbrs(edges):
    nb = defaultdict(set)
    for a, b in edges:
        nb[a].add(b)
        nb[b].add(a)
    return nb


def girth(edges):
    nb = nbrs(edges)
    best = None
    for s in nb:
        dist = {s: 0}
        par = {s: None}
        q = deque([s])
        while q:
            x = q.popleft()
            for y in nb[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    par[y] = x
                    q.append(y)
                elif par[x] != y:
                    c = dist[x] + dist[y] + 1
                    if best is None or c < best:
                        best = c
    return best  # None = acyclic


def hyperedges(edges, u, v):
    nb = nbrs(edges)
    Z = {x for x in nb if len(nb[x]) >= 3} | {u, v}
    E = {y: (nb[y] | {y}) & Z for y in nb}
    return Z, E, nb


def check_side(name, edges, u, v):
    Z, E, nb = hyperedges(edges, u, v)
    V = list(nb)
    s_max = max(len(E[y]) for y in V)
    hubdeg = max(len(nb[z] & Z) for z in Z) if Z else 0
    g = girth(edges)
    count_ok = 5 * len(edges) <= 6 * (len(V) - 1)
    # overlap facts
    overlap_bad = []
    for y, y2 in itertools.combinations(V, 2):
        I = E[y] & E[y2]
        if len(I) > 2:
            overlap_bad.append((y, y2, sorted(map(str, I))))
        elif len(I) == 2:
            if not (y in Z and y2 in Z and y2 in nb[y] and I == {y, y2}):
                overlap_bad.append((y, y2, sorted(map(str, I))))
    # Lemma P
    worstP = None
    for k in range(2, min(CAP_A, len(Z)) + 1):
        for A in itertools.combinations(sorted(Z, key=str), k):
            A = set(A)
            JA = sum(max(0, len(E[y] & A) - 1) for y in V)
            slack = 3 * k - 4 - JA
            if worstP is None or slack < worstP[0]:
                worstP = (slack, k, JA, sorted(map(str, A)))
    # Lemma L
    worstL = None
    for k in range(3, min(CAP_L, len(Z)) + 1):
        for L in itertools.combinations(sorted(Z, key=str), k):
            L = set(L)
            JL = sum(1 for y in V if len(E[y]) == 3 and E[y] <= L)
            slack = 2 * (k - 2) - 1 - JL
            if worstL is None or slack < worstL[0]:
                worstL = (slack, k, JL, sorted(map(str, L)))
    return dict(name=name, nV=len(V), nE=len(edges), girth=g, nZ=len(Z),
                s_max=s_max, hubdeg=hubdeg, count_ok=count_ok,
                overlap_bad=overlap_bad, worstP=worstP, worstL=worstL)


def fmt(r):
    g = 'acyclic' if r['girth'] is None else r['girth']
    wp = r['worstP']
    wl = r['worstL']
    return (f"{r['name']:<16} |V|={r['nV']:>3} |E|={r['nE']:>3} girth={g!s:>7} "
            f"|Z|={r['nZ']:>2} s_max={r['s_max']} hubdeg={r['hubdeg']} "
            f"count={'ok ' if r['count_ok'] else 'BAD'} "
            f"P_slack={wp[0] if wp else '-':>2} L_slack={wl[0] if wl else '-':>2} "
            f"overlap={'ok' if not r['overlap_bad'] else 'BAD ' + str(r['overlap_bad'][:2])}")


def main():
    rng = random.Random(20260923)
    rows = []
    # sideprof library
    for nm in SP.ORDER + SP.ORDER2:
        rows.append(check_side(nm, SP.SIDES[nm](), 'u', 'v'))
    # census skeletons, all edges subdivided into 3, and a seeded length sample
    for nm in CE.ORDER:
        skel, u, v = CE.SKEL[nm]
        rows.append(check_side(nm + '/3', CE.subdiv_lengths(skel, [3] * len(skel)), u, v))
        got = 0
        tries = 0
        while got < 3 and tries < 200:
            tries += 1
            lens = [rng.choice([2, 3, 4]) for _ in skel]
            e = CE.subdiv_lengths(skel, lens)
            gg = girth(e)
            if gg is not None and gg < 7:
                continue
            got += 1
            rows.append(check_side(nm + '/' + ''.join(map(str, lens)), e, u, v))
    # adjacent-hub population: skeleton subdivisions with lengths in {1,2,3,4}
    # (length 1 = a hub-hub edge), kept when girth >= 7; 4 per skeleton
    for nm in CE.ORDER:
        skel, u, v = CE.SKEL[nm]
        got, tries = 0, 0
        while got < 4 and tries < 4000:
            tries += 1
            lens = [rng.choice([1, 1, 2, 3, 4]) for _ in skel]
            if 1 not in lens:
                continue
            e = CE.subdiv_lengths(skel, lens)
            gg = girth(e)
            if gg is not None and gg < 7:
                continue
            got += 1
            rows.append(check_side(nm + '/' + ''.join(map(str, lens)), e, u, v))
    # hub paths and a hub cycle with pendant paths of length 3 (hubs adjacent in a row)
    def pend(x, k, tag):
        chain = [x] + [f'{tag}{x}_{i}' for i in range(1, k + 1)]
        return list(zip(chain[:-1], chain[1:]))
    for k in (3, 4, 5, 6):
        zs = [f'z{i}' for i in range(k)]
        e = list(zip(zs[:-1], zs[1:]))
        for i, z in enumerate(zs):
            e += pend(z, 3, 'a')
            if i in (0, k - 1):
                e += pend(z, 3, 'b')
        rows.append(check_side(f'hubpath{k}', e, zs[0], zs[-1]))
    zs = [f'c{i}' for i in range(7)]
    e = list(zip(zs, zs[1:] + zs[:1]))
    for z in zs:
        e += pend(z, 3, 'a')
    rows.append(check_side('hubcycle7', e, zs[0], zs[3]))
    # adversarial K4 sides
    for lens in [(4, 2, 3, 4, 2, 3), (4, 2, 3, 4, 2, 2), (3, 3, 3, 3, 3, 3)]:
        rows.append(check_side('sk4' + ''.join(map(str, lens)), AD.sk4_lengths(lens), 'u', 'v'))
    for r in rows:
        print(fmt(r))
    bad = [r for r in rows if r['overlap_bad'] and r['girth'] is not None and r['girth'] >= 7]
    minP = min((r['worstP'][0] for r in rows if r['worstP'] and (r['girth'] is None or r['girth'] >= 7)), default=None)
    minL = min((r['worstL'][0] for r in rows if r['worstL'] and (r['girth'] is None or r['girth'] >= 7)), default=None)
    print(f"ROWS: {len(rows)}  girth≥7 rows: {sum(1 for r in rows if r['girth'] is None or r['girth'] >= 7)}")
    print(f"overlap violations on girth≥7 rows: {len(bad)}")
    print(f"min Lemma-P slack (3|A|−4 − J_A) on girth≥7 rows, |A| ≤ {CAP_A}: {minP}")
    print(f"min Lemma-L slack (2(|L|−2)−1 − J_line) on girth≥7 rows, |L| ≤ {CAP_L}: {minL}")
    print(f"Case-1 rows (s_max ≤ 3): {sum(1 for r in rows if r['s_max'] <= 3)} / {len(rows)}")


if __name__ == '__main__':
    main()
