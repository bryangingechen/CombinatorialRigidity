#!/usr/bin/env python3
"""
contractcheck.py -- Track C driver (W4-reopen P1, certificate half).

Tests (MC-68)/(MC-69) of §(K-main) Step MC15: for a proper rigid W with G/H simple,
  (i)  core-free  <=>  def2(G) = def2(H) + def2(G/H)   (the ADDITIVITY count),
  (ii) no jump    <=   additivity,
modulo Jackson-Jordan, against `coreshrink.run_member` (relaxed variant),
which certifies (i) exactly at one picture (q in U(G), q|W in U(H)) and reads
(ii) exactly (jet order 0).  Also checks the combinatorial reformulation
(MC-67)(c): additivity <=> in the FINEST def2-optimal partition of G/H, every
component of (T u W; E(G[T]) u E(T, W)), T = (v*'s part) - v*, meets at
most one def2-rigid class of H (brute-force partitions, small graphs).

Modes (repository root, PYTHONHASHSEED=0):
  --named          x7_1716440 (both simple-quotient W), x8_60101824 (its
                   5-cycle W), W19 and R20 (core C4 / C5).
  --extra          a constructed pair (K4pend) with def2(H) <= def2(G) but
                   additivity failing.
  --maximal N      (MC-70) at every maximal proper rigid W, n <= N.
  --hunt N         every simple 2EC graph on <= N vertices with def2(G) >= 1,
                   every proper rigid W with G/H simple (x0arms.rigid_sets,
                   complete for n <= 14): tallies additivity against
                   def2(H) <= def2(G) and the (MC-67)(c) reformulation; runs
                   coreshrink on up to --runs instances per class.
Seeded (20260924); coreshrink's own sampler (its docstring).
"""
import argparse
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402
from exactcore import neighbors  # noqa: E402
from kbare_common import verts_of  # noqa: E402
from maincomp import def_k, decode, two_ec_graphs  # noqa: E402
from nogood_subdiv import contraction, is_simple  # noqa: E402
import coreshrink as CS  # noqa: E402
import x0arms as XA  # noqa: E402

SEED = 20260924


def induced(E, W):
    return [e for e in E if e[0] in W and e[1] in W]


def counts(E, W):
    H = induced(E, W)
    Eq = contraction(E, sorted(W, key=str))
    return def_k(E, 3), def_k(H, 3, sorted(W, key=str)), def_k(Eq, 3)


def partitions(V):
    if not V:
        yield []
        return
    first, rest = V[0], V[1:]
    for p in partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def val(E, P):
    lab = {v: i for i, part in enumerate(P) for v in part}
    d = sum(1 for (u, w) in E if lab[u] != lab[w])
    return 3 * (len(P) - 1) - 2 * d


def finest_optimal(E, V):
    best, opt = None, []
    for P in partitions(list(V)):
        x = val(E, P)
        if best is None or x > best:
            best, opt = x, [P]
        elif x == best:
            opt.append(P)
    # the meet of all optimal partitions (the optimal set is a sublattice)
    lab = {v: tuple(next(i for i, part in enumerate(P) if v in part) for P in opt) for v in V}
    cls = {}
    for v in V:
        cls.setdefault(lab[v], []).append(v)
    fin = list(cls.values())
    assert val(E, fin) == best, 'meet of optimal partitions is not optimal'
    return fin, best


def rigid_classes(E, W):
    """def2-rigid classes of H = G[W]: v ~ w iff delta2(v, w) = 0 in H."""
    H = induced(E, W)
    Ws = sorted(W, key=str)
    d = def_k(H, 3, Ws)
    from splitext import contract as merge_pair
    cls = {}
    for v in Ws:
        cls[v] = frozenset([v] + [w for w in Ws if w != v and
                                  d - def_k(merge_pair(H, v, w), 3, [x for x in Ws if x != w]) == 0])
    return cls


def criterion(E, W):
    """(MC-67)(c): the finest def2-optimal partition S of G/H; T = v*'s part - v*;
    every component of (T u W, E(G[T]) u E(T, W)) meets <= 1 rigid class of H."""
    Eq = contraction(E, sorted(W, key=str))
    Vq = verts_of(Eq)
    S, _ = finest_optimal(Eq, Vq)
    star = next(part for part in S if 'v*' in part)
    T = set(star) - {'v*'}
    cls = rigid_classes(E, W)
    Ws = set(W)
    comp_edges = [e for e in E if (e[0] in T and e[1] in T) or
                  (e[0] in T and e[1] in Ws) or (e[1] in T and e[0] in Ws)]
    nb = neighbors(comp_edges)
    seen = set()
    for s in T:
        if s in seen:
            continue
        comp, st = {s}, [s]
        while st:
            u = st.pop()
            for y in nb.get(u, ()):
                if y not in comp:
                    comp.add(y)
                    st.append(y)
        seen |= comp
        touched = {cls[c] for c in comp if c in Ws}
        if len(touched) > 1:
            return False, len(T)
    return True, len(T)


def run(name, E, W, tag):
    rng = random.Random(f'{SEED}:cc:{tag}')
    ts = (F(1, 10), F(1, 10**4))
    for _ in range(5):
        verdict, line, pat, feats = CS.run_member(name, E, sorted(W, key=str), rng, 30,
                                                  'relaxed', ts, {})
        if verdict != 'REDRAW':
            break
    cf = feats['(i) core-free, certified: proj_W L_G(q) = L_H(q|W), q in U(G), q|W in U(H)']
    nj = feats['(ii) no jump: dim ker M0 = dim ker M(t)']
    return bool(cf), bool(nj), verdict, line


def named():
    cases = [('x7_1716440', decode(7, 1716440), [{2, 5, 6}, {0, 1, 3, 4}])]
    E8 = decode(*XA.key_of([(4, 0), (0, 5), (5, 2), (2, 7), (7, 3), (3, 6), (6, 1), (1, 4),
                            (4, 7), (5, 6)]))
    rig, _ = XA.rigid_sets(E8)
    nb = neighbors(E8)
    W8 = [set(W) for W in rig if not any(len(nb[u] & W) >= 2 for u in set(verts_of(E8)) - W)]
    cases.append((XA.name_of(XA.key_of(E8)), E8, W8))
    from widened import W19
    from rpool import R20
    for nm, E, m in (('W19', W19(), 4), ('R20', R20(), 5)):
        cases.append((nm, E, [{f'c{i}' for i in range(m)}]))
    for nm, E, Ws in cases:
        for W in Ws:
            dG, dH, dQ = counts(E, W)
            add = dG == dH + dQ
            crit = criterion(E, W) if len(verts_of(E)) - len(W) + 1 <= 9 else ('n/a', None)
            cf, nj, verdict, line = run(nm, E, W, f'{nm}:{sorted(map(str, W))}')
            print(f'{nm} W={sorted(map(str, W))} def2(G)={dG} def2(H)={dH} def2(G/H)={dQ} '
                  f'additive={int(add)} (MC-67)(c)={crit} | coreshrink: (i)={int(cf)} (ii)={int(nj)} '
                  f'{verdict}')


def hunt(N, runs):
    tally = Counter()
    todo = {}
    for name, E in two_ec_graphs(N):
        if def_k(E, 3) < 1:
            continue
        V = verts_of(E)
        nb = neighbors(E)
        rig, complete = XA.rigid_sets(E)
        assert complete
        for W in rig:
            W = set(W)
            if any(len(nb[u] & W) >= 2 for u in set(V) - W):
                continue
            dG, dH, dQ = counts(E, W)
            assert dG <= dH + dQ, 'the combinatorial inequality fails'
            add = dG == dH + dQ
            crit, _ = criterion(E, W)
            assert crit == add, ('(MC-67)(c) reformulation disagrees', name, sorted(W))
            key = ('additive' if add else 'NOT additive',
                   'def2(H)=0' if dH == 0 else 'def2(H)<=def2(G)' if dH <= dG else 'def2(H)>def2(G)')
            tally[key] += 1
            todo.setdefault(key, []).append((name, E, W))
    print(f'simple 2EC graphs on <= {N} vertices with def2(G) >= 1; proper rigid W, G/H simple:')
    for k, v in sorted(tally.items()):
        print(f'  {k}: {v} (G, W) pairs')
    print('  (MC-67)(c) reformulation agreed with the count at every pair (asserted)')
    for key in sorted(todo):
        sample = todo[key][:runs]
        res = Counter()
        for (name, E, W) in sample:
            cf, nj, verdict, line = run(name, E, W, f'{name}:{sorted(W)}')
            res[(int(cf), int(nj))] += 1
            if (key[0] == 'additive') != cf:
                print('   DISAGREE', key, line)
        print(f'  coreshrink on the first {len(sample)} of {key}: ((i), (ii)) -> {dict(res)}')


def extra():
    """A constructed pair where additivity FAILS although def2(H) <= def2(G):
    core C4 = c0 c1 c2 c3; a triangle u1 u2 u3 with u_i joined to c_(i-1) (so
    G/H contains K4 on v*, u1, u2, u3); a pendant C4 u1 p1 p2 p3 at u1 (adds 1
    to def2(G) and to def2(G/H)).  (MC-68)(a) predicts (i) fails."""
    E = [('c0', 'c1'), ('c1', 'c2'), ('c2', 'c3'), ('c3', 'c0'),
         ('u1', 'u2'), ('u2', 'u3'), ('u3', 'u1'),
         ('u1', 'c0'), ('u2', 'c1'), ('u3', 'c2'),
         ('u1', 'p1'), ('p1', 'p2'), ('p2', 'p3'), ('p3', 'u1')]
    W = {'c0', 'c1', 'c2', 'c3'}
    from kbare_common import is_2ec
    assert is_2ec(E) and is_simple(contraction(E, sorted(W)))
    assert def_k(induced(E, W), 6) == 0
    dG, dH, dQ = counts(E, W)
    add = dG == dH + dQ
    for tag in ('d0', 'd1', 'd2'):
        cf, nj, verdict, line = run('K4pend', E, W, f'K4pend:{tag}')
        print(f'K4pend[{tag}] W=C4 def2(G)={dG} def2(H)={dH} def2(G/H)={dQ} additive={int(add)} '
              f'| coreshrink: (i)={int(cf)} (ii)={int(nj)} {verdict}')
        print('   ', line)


def maximal(N):
    """(MC-70): at a MAXIMAL proper rigid W (maximal among all proper rigid sets)
    with G/H simple, additivity holds unless the trivial partition is the unique
    def2-optimal partition of G/H; then additivity <=> def2(G) = def2(H).
    Every simple 2EC graph on <= N vertices (all def2), asserted per pair."""
    tally = Counter()
    for name, E in two_ec_graphs(N):
        V = verts_of(E)
        nb = neighbors(E)
        rig, complete = XA.rigid_sets(E)
        assert complete
        sets = [frozenset(W) for W in rig]
        mx = [W for W in sets if not any(W < X for X in sets)]
        for W in mx:
            if any(len(nb[u] & W) >= 2 for u in set(V) - W):
                tally['maximal W, G/H not simple'] += 1
                continue
            dG, dH, dQ = counts(E, W)
            add = dG == dH + dQ
            Eq = contraction(E, sorted(W, key=str))
            S, best = finest_optimal(Eq, verts_of(Eq))
            trivial = len(S) == 1
            if not trivial:
                assert add, ('(MC-70) fails', name, sorted(W))
            else:
                assert dQ == 0 and def_k(E, 6) == 0
                assert add == (dG == dH)
            tally[('G/H finest optimal partition trivial' if trivial else 'nontrivial',
                   'additive' if add else 'NOT additive', f'def2(G)={"0" if dG == 0 else ">0"}')] += 1
    print(f'maximal proper rigid W, simple 2EC graphs on <= {N} vertices:')
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--maximal', type=int, default=0)
    ap.add_argument('--extra', action='store_true')
    ap.add_argument('--named', action='store_true')
    ap.add_argument('--hunt', type=int, default=0)
    ap.add_argument('--runs', type=int, default=4)
    a = ap.parse_args()
    if a.named:
        named()
    if a.extra:
        extra()
    if a.maximal:
        maximal(a.maximal)
    if a.hunt:
        hunt(a.hunt, a.runs)


if __name__ == '__main__':
    main()
