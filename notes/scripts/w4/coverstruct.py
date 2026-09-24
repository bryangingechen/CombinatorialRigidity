#!/usr/bin/env python3
"""
coverstruct.py -- the structural half of the coverage theorem (workbook §(K-main), Step MC16,
(MC-75)-(MC-89); W4-reopen P1, the third 2026-09-24 session's Track A). Purely combinatorial: no
geometry, no randomness. Every quantity is a deficiency (a count-matroid rank, exact integers).

Definitions (Step MC16):
  (S)     2 e(X) <= 3|X| - 4 for every X with |X| >= 2  <=>  2G is (3,4)-sparse.
  class S G 2-connected, min degree >= 2, not a cycle, not a theta graph, (S).
  chain   maximal path a - x1 - ... - xk - b of degree-2 vertices between hubs.
  delta   def3(G') - def3(G'/ab),  delta2 = def2(G') - def2(G'/ab),  G' = G - chain.
  usable  (mod JJ)  k >= 3;  k = 2 and (delta = 0 or (a !~ b and delta2 >= 2));
          k = 1 and (delta = 0 or delta >= 5).

Modes (repository root, PYTHONHASHSEED=0):
  --necklaces        the stuck families of (MC-83), (MC-84): 0 usable chains; controls usable.
  --exh N            the identities (MC-77)-(MC-80) asserted on the class-S members of exh N.
  --witness N [--smax S --cores K4,dC4]
                     class-S subdivisions of small cores on <= N vertices; asserts (MC-77)-(MC-80).
  --hunt FILE|-      graph6 lines (from FILE, or stdin for '-'): for each class-S member, is there a
                     usable chain; at each member with none, (MC-80) is ASSERTED.
  --additivity [--witness N --smax S --cores ...]
                     (MC-87): simple quotient and additivity asserted at every (MC-80) core.
  --pairs N          (MC-88): delta2 = 1 => delta <= 1 (and delta2 = 0 => delta = 0) at every pair
                     of every connected simple graph on <= N vertices; prints the (delta2, delta) histogram.
  --beads FILE|- --tmax T
                     the framing search behind (MC-84) (internally stuck rigid beads).
The --hunt/--beads populations come from nauty's geng (external, deterministic; nauty 2.9.3 was
used), e.g.  geng -C -d2 -t -q 14 0:19 | python3 notes/scripts/w4/coverstruct.py --hunt -
These are checks of proved identities at witnesses, plus the exhaustive stuck-graph count of (MC-83).
"""
import argparse
import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from maincomp import def_k, two_ec_graphs  # noqa: E402
from nogood_subdiv import count_matroid_rank, branch_decomposition  # noqa: E402
from splitext import contract as merge_pair  # noqa: E402


# ---------------------------------------------------------------- basics

def comps(E, V):
    nb = {v: set() for v in V}
    for u, w in E:
        nb[u].add(w)
        nb[w].add(u)
    seen, out = set(), []
    for s in V:
        if s in seen:
            continue
        c, st = {s}, [s]
        while st:
            u = st.pop()
            for y in nb[u]:
                if y not in c:
                    c.add(y)
                    st.append(y)
        seen |= c
        out.append(c)
    return out


def two_connected(E, V):
    if len(comps(E, V)) != 1:
        return False
    for v in V:
        V2 = [u for u in V if u != v]
        E2 = [e for e in E if v not in e]
        if len(comps(E2, V2)) != 1:
            return False
    return True


def cond_S(E, V):
    """(S) <=> the doubled edge set is independent in the (3,4)-count matroid."""
    big = [e for e in E for _ in range(2)]
    return count_matroid_rank(big, V, k=3, ell=4) == len(big)


def d2(E, V):
    return def_k(E, 3, V)


def d3(E, V):
    return def_k(E, 6, V)


def induced(E, W):
    W = set(W)
    return [e for e in E if e[0] in W and e[1] in W]


def is_cycle(E, V):
    nb = neighbors(E)
    return all(len(nb[v]) == 2 for v in V) and len(comps(E, V)) == 1


def is_theta(E, V):
    nb = neighbors(E)
    degs = sorted(len(nb[v]) for v in V)
    return degs.count(3) == 2 and degs.count(2) == len(V) - 2


def in_class_S(E, V):
    nb = neighbors(E)
    return (min(len(nb[v]) for v in V) >= 2 and two_connected(E, V)
            and not is_cycle(E, V) and not is_theta(E, V) and cond_S(E, V))


def rigid_sets_all(E, V):
    """Every W subseteq V, |W| >= 2, with def3(G[W]) = 0 (brute force; small n only).
    A rigid set has min degree >= 2 in G[W], used as a filter."""
    out = []
    for r in range(3, len(V) + 1):
        for W in combinations(V, r):
            ie = induced(E, W)
            if 5 * len(ie) < 6 * (len(W) - 1):
                continue
            nb = {v: 0 for v in W}
            for u, w in ie:
                nb[u] += 1
                nb[w] += 1
            if min(nb.values()) < 2:
                continue
            if d3(ie, list(W)) == 0:
                out.append(frozenset(W))
    return out


def simple_quotient(E, W):
    W = set(W)
    cnt = {}
    for u, w in E:
        if (u in W) != (w in W):
            o = w if u in W else u
            cnt[o] = cnt.get(o, 0) + 1
    return all(c <= 1 for c in cnt.values())


def chains(E):
    hubs, br = branch_decomposition(E)
    return [(a, b, I) for (a, b, I) in (br or []) if I]


def chain_data(E, V, a, b, I):
    nb = neighbors(E)
    Ws = set(I)
    Ep = [e for e in E if e[0] not in Ws and e[1] not in Ws]
    Vp = [v for v in V if v not in Ws]
    mp = merge_pair(Ep, a, b)
    Vm = [v for v in Vp if v != b]
    dl = d3(Ep, Vp) - d3(mp, Vm)
    dl2 = d2(Ep, Vp) - d2(mp, Vm)
    adj = b in nb[a]
    k = len(I)
    if k >= 3:
        use = True
    elif k == 2:
        use = dl == 0 or (not adj and dl2 >= 2)
    else:
        use = dl == 0 or dl >= 5
    return dict(k=k, a=a, b=b, adj=adj, delta=dl, delta2=dl2, usable=use, I=I)


# ---------------------------------------------------------------- necklaces

def necklace(units):
    """Unit cycle.  units: string over {'s', 'Q', 'A', 'T'}:
       s  a single vertex;
       Q  a C4 a-p-c-r-a attached at the OPPOSITE vertices a (in) and c (out);
       A  a C4 a-p-q-b-a attached at the ADJACENT vertices a (in) and b (out);
       T  theta(2,3,4) with hubs h, h' and paths h-y-h', h-t1-w-h', h-v-t2-v'-h', attached
          at t1 (in) and t2 (out) -- Step MC16 (MC-84); local labels t1, v, v', y, w, t2, h, h'
          = 0..7, so the bead is graph6 G?`e`o with t1 = 0, t2 = 5.
    Consecutive units are joined by one edge (out of unit i to in of unit i+1)."""
    E, ins, outs, nxt = [], [], [], 0
    for u in units:
        if u == 's':
            v = nxt
            nxt += 1
            ins.append(v)
            outs.append(v)
        elif u == 'Q':
            a, p, c, r = nxt, nxt + 1, nxt + 2, nxt + 3
            nxt += 4
            E += [(a, p), (p, c), (c, r), (r, a)]
            ins.append(a)
            outs.append(c)
        elif u == 'A':
            a, p, q, b = nxt, nxt + 1, nxt + 2, nxt + 3
            nxt += 4
            E += [(a, p), (p, q), (q, b), (b, a)]
            ins.append(a)
            outs.append(b)
        elif u == 'T':
            t1, v, v2, y, w, t2, h, h2 = range(nxt, nxt + 8)
            nxt += 8
            E += [(h, y), (y, h2), (h, t1), (t1, w), (w, h2), (h, v), (v, t2), (t2, v2), (v2, h2)]
            ins.append(t1)
            outs.append(t2)
        else:
            raise ValueError(u)
    L = len(units)
    for i in range(L):
        E.append((outs[i], ins[(i + 1) % L]))
    return E, list(range(nxt))


def report(name, E, V, brute_rigid=True):
    nb = neighbors(E)
    tri = any(nb[u] & nb[w] for u, w in E)
    ok = in_class_S(E, V)
    D2, D3 = d2(E, V), d3(E, V)
    print(f'{name}: n={len(V)} m={len(E)} classS={ok} triangle={tri} def2={D2} def3={D3}')
    cd = [chain_data(E, V, a, b, I) for (a, b, I) in chains(E)]
    nuse = sum(c['usable'] for c in cd)
    for c in cd:
        print(f'   chain k={c["k"]} ends {c["a"]},{c["b"]}{" a~b" if c["adj"] else ""}'
              f' delta={c["delta"]} delta2={c["delta2"]} '
              f'{"USABLE" if c["usable"] else "blocked"}')
    print(f'   usable chains: {nuse} / {len(cd)}')
    if brute_rigid and len(V) <= 24:
        pass
    return cd


def run_necklaces():
    fams = [
        ('Q s Q s Q  (u=5)', 'QsQsQ'),
        ('Q Q Q Q s  (u=5)', 'QQQQs'),
        ('Q Q Q Q Q  (u=5)', 'QQQQQ'),
        ('Q s Q s Q s (u=6)', 'QsQsQs'),
        ('A s A s A s (u=6)', 'AsAsAs'),
        ('A A A A A A (u=6)', 'AAAAAA'),
        ('A A A A A A A (u=7)', 'AAAAAAA'),
        ('Q Q Q Q Q Q (u=6)', 'QQQQQQ'),
        # controls: shapes outside the window, where (MC-83) predicts a usable chain
        ('control Q s Q s (u=4)', 'QsQs'),
        ('control A A A A A (u=5)', 'AAAAA'),
        ('Q Q Q Q Q Q Q (u=7, non-rigid)', 'QQQQQQQ'),
        ('control Q s Q s Q s s (u=7)', 'QsQsQss'),
        # (MC-84): the 4-cycle-free theta(2,3,4) necklaces
        ('T s T s T s (u=6)', 'TsTsTs'),
        ('T T T T T T (u=6)', 'TTTTTT'),
        ('T T T T T T T (u=7, non-rigid)', 'TTTTTTT'),
    ]
    size = {'s': 1, 'Q': 4, 'A': 4, 'T': 8}
    named = {'QsQsQ', 'AsAsAs', 'TsTsTs'}      # the graphs run through x0arms.py --tree
    for name, u in fams:
        E, V = necklace(u)
        cd = report(name, E, V)
        if 'T' in u:
            print(f'   4-cycle present: {has_c4(E)}')
            assert not has_c4(E)
        if u in named:
            from maincomp import canon
            print(f'   canonical name x{len(V)}_{canon(len(V), E)}')
        # the CONTRACT candidates of (MC-83)/(MC-84): the first bead is a proper rigid set with
        # simple quotient, and ADDITIVITY def2(G) = def2(H) + def2(G/H) holds there ((MC-87));
        # all ASSERTED.
        i = next((j for j, t in enumerate(u) if t != 's'), None)
        if i is not None:
            start = sum(size[t] for t in u[:i])
            W = list(range(start, start + size[u[i]]))
            H = induced(E, W)
            dG, dH, dQ = d2(E, V), d2(H, W), quotient_def2(E, W)
            assert d3(H, W) == 0 and simple_quotient(E, W) and dH < dG and dG == dH + dQ
            print(f'   bead {W}: rigid, G/H simple, def2(G) = def2(H) + def2(G/H): '
                  f'{dG} = {dH} + {dQ}')
        del cd


# ---------------------------------------------------------------- exh checks

def maximal_rigid_containing(rig, S):
    cands = [W for W in rig if S <= W]
    return max(cands, key=len) if cands else None


def run_exh(nmax):
    """On every S-member of the exhaustive simple 2EC list on <= nmax vertices, ASSERT:
       (MC-77) maximal rigid sets are disjoint, with simple quotients when proper;
       (MC-78) tight sets are edges or lie in one maximal def3-rigid set;
       (MC-79)(iii) k=2: delta2 = 1 implies a ~ b or delta = 0;
       (MC-79)(ii) k=1: delta >= 5 iff x lies in no def3-rigid subgraph (G included);
       (MC-80) theorem S: a usable chain, or a proper rigid W with G/H simple and
             def2(G[W]) < def2(G)."""
    nS = nstuck = nrig = 0
    for name, E in two_ec_graphs(nmax):
        V = verts_of(E)
        if not in_class_S(E, V):
            continue
        nS += 1
        rig = rigid_sets_all(E, V)       # includes V itself when G is rigid
        rigid_G = frozenset(V) in rig
        nrig += rigid_G
        # maximal rigid sets (MC-77): vertex-disjoint, simple quotients when proper
        maxl = [W for W in rig if not any(W < W2 for W2 in rig)]
        for W1, W2 in combinations(maxl, 2):
            assert not (W1 & W2), (name, 'maximal rigid sets meet')
        for W in maxl:
            if len(W) < len(V):
                assert simple_quotient(E, W), (name, 'maximal rigid set, quotient not simple')
        # (MC-78)
        for r in range(3, len(V) + 1):
            for X in combinations(V, r):
                ie = induced(E, X)
                if 2 * len(ie) == 3 * len(X) - 4:
                    assert any(set(X) <= W for W in maxl), (name, 'tight set not in a rigid set', X)
        cd = [chain_data(E, V, a, b, I) for (a, b, I) in chains(E)]
        for c in cd:
            if c['k'] == 2 and c['delta2'] == 1:
                assert c['adj'] or c['delta'] == 0, (name, c)
            if c['k'] == 1:
                inrig = any(c['I'][0] in W for W in rig)
                assert (c['delta'] >= 5) == (not inrig), (name, c, inrig)
                assert not c['adj'] and c['delta2'] >= 2, (name, c)
        if not any(c['usable'] for c in cd):
            nstuck += 1
            ok = [W for W in rig if len(W) < len(V) and simple_quotient(E, W)
                  and d2(induced(E, W), list(W)) < d2(E, V)]
            assert ok, (name, 'theorem S fails')
            print(f'  no usable chain: {name}, CONTRACT candidates {len(ok)}')
    print(f'exh{nmax}: {nS} members of class S ({nrig} rigid); every assert held; '
          f'{nstuck} with no usable chain')


CORES = {
    'K4': [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
    'dC4': [(0, 1), (0, 1), (2, 3), (2, 3), (1, 2), (3, 0)],
    'K33': [(a, b) for a in range(3) for b in range(3, 6)],
    'prism': [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)],
    'dC6': [(0, 1), (0, 1), (2, 3), (2, 3), (4, 5), (4, 5), (1, 2), (3, 4), (5, 0)],
}


def subdivide(core, s):
    N = 1 + max(max(e) for e in core)
    E, nxt = [], N
    for (u, w), k in zip(core, s):
        path = [u] + list(range(nxt, nxt + k)) + [w]
        nxt += k
        E += list(zip(path, path[1:]))
    return E, list(range(nxt))


def witness_set(nmax, smax=2, cores=None):
    """Every subdivision of the CORES with 0..smax new vertices per core edge, on at
    most nmax vertices, simple, deduplicated by canonical form; the class-S members."""
    from itertools import product
    from maincomp import canon
    seen, out = set(), []
    for cname, core in CORES.items():
        if cores and cname not in cores:
            continue
        N = 1 + max(max(e) for e in core)
        for s in product(range(smax + 1), repeat=len(core)):
            if N + sum(s) > nmax:
                continue
            E, V = subdivide(core, s)
            if len({frozenset(e) for e in E}) != len(E):
                continue
            key = canon(len(V), E)
            if (len(V), key) in seen:
                continue
            seen.add((len(V), key))
            if in_class_S(E, V):
                out.append((f'{cname}{"".join(map(str, s))}', E, V))
    return out


def run_witness(nmax, smax=2, cores=None):
    """The (MC-77)..(MC-80) asserts of run_exh on witness_set(nmax, smax, cores)."""
    nS = nrig = nstuck = 0
    for name, E, V in witness_set(nmax, smax, cores):
        nS += 1
        rig = rigid_sets_all(E, V)
        rigid_G = frozenset(V) in rig
        nrig += rigid_G
        maxl = [W for W in rig if not any(W < W2 for W2 in rig)]
        for W1, W2 in combinations(maxl, 2):
            assert not (W1 & W2), (name, 'maximal rigid sets meet')
        for W in maxl:
            if len(W) < len(V):
                assert simple_quotient(E, W), (name, 'quotient not simple')
        for r in range(3, len(V) + 1):
            for X in combinations(V, r):
                ie = induced(E, X)
                if 2 * len(ie) == 3 * len(X) - 4:
                    assert any(set(X) <= W for W in maxl), (name, 'tight set', X)
        cd = [chain_data(E, V, a, b, I) for (a, b, I) in chains(E)]
        for c in cd:
            if c['k'] == 2 and c['delta2'] == 1:
                assert c['adj'] or c['delta'] == 0, (name, c)
            if c['k'] == 2 and c['adj']:
                assert c['delta'] <= 1, (name, c)
            if c['k'] == 1:
                inrig = any(c['I'][0] in W for W in rig)
                assert (c['delta'] >= 5) == (not inrig), (name, c, inrig)
                assert not c['adj'] and c['delta2'] >= 2, (name, c)
        if not any(c['usable'] for c in cd):
            nstuck += 1
            ok = [W for W in rig if len(W) < len(V) and simple_quotient(E, W)
                  and d2(induced(E, W), list(W)) < d2(E, V)]
            assert ok, (name, 'theorem S fails')
            cells = sorted((c['k'], c['delta']) for c in cd)
            print(f'  no usable chain: {name} n={len(V)} m={len(E)} def2={d2(E, V)} '
                  f'def3={d3(E, V)} (k, delta) = {cells}; CONTRACT candidates {len(ok)}')
    print(f'witness set (n <= {nmax}, smax {smax}, cores {cores or "all"}): {nS} class-S members ({nrig} rigid); every assert '
          f'held; {nstuck} with no usable chain')


def g6decode(line):
    """graph6 -> (edges, vertices)."""
    data = [ord(c) - 63 for c in line.strip()]
    n = data[0]
    bits = []
    for d in data[1:]:
        bits += [(d >> (5 - i)) & 1 for i in range(6)]
    E, k = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                E.append((i, j))
            k += 1
    return E, list(range(n))


def has_c4(E):
    nb = neighbors(E)
    V = sorted(nb)
    for u, w in combinations(V, 2):
        if len(nb[u] & nb[w]) >= 2:
            return True
    return False


def run_hunt(path):
    """Read graph6 lines (geng output) from `path`; for every class-S member decide whether
    it has a usable chain (early exit, chains by decreasing k), and at every member with
    none ASSERT theorem S and report whether it contains a 4-cycle."""
    tot = nS = nstuck = nstuck_noc4 = 0
    for line in (sys.stdin if path == '-' else open(path)):
        if not line.strip():
            continue
        tot += 1
        E, V = g6decode(line)
        if not in_class_S(E, V):
            continue
        nS += 1
        ch = sorted(chains(E), key=lambda t: -len(t[2]))
        stuck = True
        cells = []
        for (a, b, I) in ch:
            if len(I) >= 3:
                stuck = False
                break
            c = chain_data(E, V, a, b, I)
            if c['usable']:
                stuck = False
                break
            assert (c['k'] == 1 and 1 <= c['delta'] <= 4) or (c['k'] == 2 and c['adj']
                                                              and c['delta'] == 1), c
            cells.append((c['k'], c['delta']))
        if not stuck:
            continue
        nstuck += 1
        rig = rigid_sets_all(E, V)
        ok = [W for W in rig if len(W) < len(V) and simple_quotient(E, W)
              and d2(induced(E, W), list(W)) < d2(E, V)]
        assert ok, (line, 'theorem S fails')
        c4 = has_c4(E)
        nstuck_noc4 += not c4
        print(f'  no usable chain: {line.strip()} n={len(V)} m={len(E)} def2={d2(E, V)} '
              f'def3={d3(E, V)} cells={sorted(cells)} C4={"Y" if c4 else "N"} '
              f'min|W|={min(len(W) for W in ok)}')
    print(f'{"stdin" if path == "-" else path}: {tot} graphs, {nS} in class S, {nstuck} with no usable chain '
          f'(theorem S asserted at each), {nstuck_noc4} of them without a 4-cycle')


def min_frame(E, V):
    """For a def3-rigid graph B: the least number t of attachment vertices T making B
    INTERNALLY STUCK -- every degree-2 vertex y outside T has B - y non-rigid and no
    degree-2 neighbour outside T.  Returns (t, T) or (None, None) if B is not rigid."""
    nb = neighbors(E)
    deg2 = [v for v in V if len(nb[v]) == 2]
    R0 = set()
    for y in deg2:
        Vy = [v for v in V if v != y]
        Ey = [e for e in E if y not in e]
        if d3(Ey, Vy) == 0:
            R0.add(y)
    rest = [v for v in deg2 if v not in R0]
    restset = set(rest)
    cover_edges = [(u, w) for u, w in E if u in restset and w in restset]
    best = None
    for r in range(0, len(rest) + 1):
        for T in combinations(rest, r):
            Ts = set(T)
            if all(u in Ts or w in Ts for u, w in cover_edges):
                best = R0 | Ts
                break
        if best is not None:
            break
    return len(best), best


def run_beads(path, tmax):
    """Read graph6 (connected, min degree 2, girth >= 5 candidates); for every (S)-graph
    that is def3-rigid, the least attachment count t making it internally stuck.  An
    internally stuck bead with t <= 2 on two distinct vertices would give, as seven beads in
    a unit cycle, a class-S graph with no usable chain and no 4-cycle."""
    from collections import Counter
    hist, tot, nrig = Counter(), 0, 0
    for line in (sys.stdin if path == '-' else open(path)):
        if not line.strip():
            continue
        tot += 1
        E, V = g6decode(line)
        if not cond_S(E, V) or d3(E, V) != 0:
            continue
        nrig += 1
        t, T = min_frame(E, V)
        hist[t] += 1
        if t <= tmax:
            print(f'  internally stuck with t={t}: {line.strip()} n={len(V)} m={len(E)} T={sorted(T)}')
    print(f'{"stdin" if path == "-" else path}: {tot} graphs, {nrig} rigid (S)-graphs; least t histogram {dict(sorted(hist.items()))}')


def quotient_def2(E, W):
    """def2 of G/G[W] (W contracted to one vertex 'v*'; multigraph allowed)."""
    Ws = set(W)
    Q = [('v*' if u in Ws else u, 'v*' if w in Ws else w) for (u, w) in E
         if not (u in Ws and w in Ws)]
    VQ = sorted({x for e in Q for x in e}, key=str)
    return d2(Q, VQ)


def theorem_s_cores(E, V):
    """The cores of (MC-80): G non-rigid -> every proper maximal rigid set of G; G rigid -> for
    every chain C with G - C not rigid, every non-singleton maximal rigid set of G - C."""
    rig = rigid_sets_all(E, V)
    if frozenset(V) not in rig:
        return 'nonrigid', [W for W in rig if not any(W < W2 for W2 in rig)]
    out = []
    for (a, b, I) in chains(E):
        Ws = set(I)
        Ep = [e for e in E if e[0] not in Ws and e[1] not in Ws]
        Vp = [v for v in V if v not in Ws]
        if d3(Ep, Vp) == 0:
            continue
        rp = rigid_sets_all(Ep, Vp)
        out += [W for W in rp if not any(W < W2 for W2 in rp)]
    return 'rigid', out


def run_additivity(nmax, smax, cores):
    """At every core of (MC-80) of every class-S member of witness_set(nmax, smax, cores), ASSERT
    (MC-87): G/H simple, def2(H) < def2(G) when the core comes from a chain that is blocked, and
    ADDITIVITY def2(G) = def2(H) + def2(G/H)."""
    nG = nW = 0
    for name, E, V in witness_set(nmax, smax, cores):
        kind, Ws = theorem_s_cores(E, V)
        D2 = d2(E, V)
        for W in Ws:
            nW += 1
            H = induced(E, W)
            assert simple_quotient(E, W), (name, W)
            dH, dQ = d2(H, list(W)), quotient_def2(E, W)
            assert D2 == dH + dQ, (name, kind, sorted(W), D2, dH, dQ)
        nG += 1
    print(f'additivity at the (MC-80) cores, witness set (n <= {nmax}, smax {smax}, cores '
          f'{cores or "all"}): {nG} class-S members, {nW} cores, every assert held')


def run_pairs(nmax):
    """(MC-88): delta2 = 1 implies delta <= 1, and delta2 = 0 implies delta = 0, at every pair
    a != b of every connected simple graph on <= nmax vertices (maincomp.connected_graphs),
    ASSERTED; the (delta2, delta) histogram is printed."""
    from collections import Counter
    from maincomp import connected_graphs, decode
    hist = Counter()
    lev = connected_graphs(nmax)
    for n in range(2, nmax + 1):
        for code in lev[n]:
            E = decode(n, code)
            V = list(range(n))
            f2, f3 = d2(E, V), d3(E, V)
            for a, b in combinations(V, 2):
                mp = merge_pair(E, a, b)
                Vm = [v for v in V if v != b]
                dl2 = f2 - d2(mp, Vm)
                dl = f3 - d3(mp, Vm)
                hist[(dl2, dl)] += 1
                assert dl2 != 1 or dl <= 1, (n, code, a, b, dl2, dl)
                assert dl2 != 0 or dl == 0, (n, code, a, b, dl2, dl)
    print(f'pairs on connected graphs <= {nmax} vertices: (delta2, delta) histogram '
          f'{dict(sorted(hist.items()))}; every assert held')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pairs', type=int, default=0)
    ap.add_argument('--additivity', action='store_true')
    ap.add_argument('--beads', default='')
    ap.add_argument('--tmax', type=int, default=2)
    ap.add_argument('--hunt', default='')
    ap.add_argument('--necklaces', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--witness', type=int, default=0)
    ap.add_argument('--smax', type=int, default=2)
    ap.add_argument('--cores', default='')
    a = ap.parse_args()
    if a.necklaces:
        run_necklaces()
    if a.exh:
        run_exh(a.exh)
    if a.hunt:
        run_hunt(a.hunt)
    if a.beads:
        run_beads(a.beads, a.tmax)
    if a.pairs:
        run_pairs(a.pairs)
    if a.additivity:
        run_additivity(a.witness or 14, a.smax, a.cores.split(',') if a.cores else None)
    elif a.witness:
        run_witness(a.witness, a.smax, a.cores.split(',') if a.cores else None)


if __name__ == '__main__':
    main()
