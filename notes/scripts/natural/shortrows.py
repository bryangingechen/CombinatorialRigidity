#!/usr/bin/env python3
"""PENCIL-NATURAL recon, track R2 (N3/N4): which d = 3 coverage steps apply.

For a simple graph G this decides, from the definitions in
`blueprint/src/chapter/main-component.tex` (sec:main-component-coverage,
def:pencil-x0-reduces) and `deficiency.tex` (def:D-deficiency,
def:deficiency-merged), which clauses of X0Reduces apply, and reports the
graphs of the class

    C = { simple, connected, min degree >= 2, G - v connected for every v,
          some body of degree >= 3, def_2(G) != def_3(G),
          no planar-rigid set (equivalently sparse) }

-- the graphs on which the first five rows of the d = 3 table fail -- on which
no chain has k >= 3 interior bodies and no additive core exists: the graphs
where ONLY the short-chain steps (open-ear-one, open-ear-two,
open-ear-two-orbit, splitoff) can apply.

Deficiency: def_D(G) = D(n-1) - rank of the (D,D)-count matroid on (D-1)G
(Tutte / Nash-Williams), by `nogood_subdiv.count_matroid_rank` (Lee-Streinu
pebble game, parametric in (k, l)).  Planar: D = 3; d = 3: D = 6; d = 4:
D = 10.  The merged deficiency def_D(G; a, b) is def_D of G with a and b
identified (loops dropped): partitions of G with a, b in one part are the
partitions of the identified multigraph, with the same |P| and d(P).
`--validate` cross-checks both against brute-force partition maxima and,
at D = 6, against `kbare_common.exact_deficiency`.

Exact integer arithmetic throughout; no randomness (no seed needed).

Populations (each run prints its own population line):
  --g6         simple graphs in graph6 on stdin (e.g. from nauty geng).
  --hub NAME   every subdivision of a named hub multigraph with 0..MAXK
               interior bodies per hub edge (labelled patterns, deduplicated
               up to graph isomorphism by an exact canonical form).

Usage (repo root):
  python3 notes/scripts/natural/shortrows.py --validate
  for n in $(seq 5 13); do geng -C -t -d2 -q $n $n:$(( (3*n-4)/2 )); done \
      | python3 notes/scripts/natural/shortrows.py --g6
  python3 notes/scripts/natural/shortrows.py --hub K4 --maxk 2
"""
import os
import sys
from itertools import combinations, permutations, product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
from nogood_subdiv import count_matroid_rank  # noqa: E402
from kbare_common import exact_deficiency  # noqa: E402


# ---------------------------------------------------------------- deficiency

def defD(verts, edges, D):
    """max_P D(|P|-1) - (D-1) d(P) over partitions of `verts`."""
    verts = list(verts)
    n = len(verts)
    if n <= 1:
        return 0
    big = [e for e in edges if e[0] != e[1] for _ in range(D - 1)]
    return D * (n - 1) - count_matroid_rank(big, verts, k=D, ell=D)


def merged(verts, edges, a, b, D):
    """def_D(G; a, b): partitions with a and b in one part."""
    vs = [v for v in verts if v != b]
    es = []
    for u, w in edges:
        u2 = a if u == b else u
        w2 = a if w == b else w
        if u2 != w2:
            es.append((u2, w2))
    return defD(vs, es, D)


def gap(verts, edges):
    """g(H) = def_2(H) - def_3(H), the rank the heights must recover."""
    return defD(verts, edges, 3) - defD(verts, edges, 6)


def suppress(verts, edges, x, u, w):
    """G with x removed and the edge uw added (the splitting-off G_x^{uw})."""
    vs = [v for v in verts if v != x]
    es = [e for e in edges if x not in e] + [(u, w)]
    return vs, es


def induced(edges, W):
    W = set(W)
    return [e for e in edges if e[0] in W and e[1] in W]


def s_val(nW, eW, D):
    """Singleton value s_D = D(|W|-1) - (D-1) e(W)."""
    return D * (nW - 1) - (D - 1) * eW


# --------------------------------------------------------------- brute force

def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def brute_def(verts, edges, D, together=None):
    best = None
    for P in set_partitions(list(verts)):
        lab = {}
        for i, part in enumerate(P):
            for v in part:
                lab[v] = i
        if together is not None and lab[together[0]] != lab[together[1]]:
            continue
        d = sum(1 for u, w in edges if lab[u] != lab[w])
        val = D * (len(P) - 1) - (D - 1) * d
        if best is None or val > best:
            best = val
    return best


# -------------------------------------------------------------------- graphs

def nbrs_of(n, edges):
    nb = [set() for _ in range(n)]
    for u, w in edges:
        nb[u].add(w)
        nb[w].add(u)
    return nb


def connected(vs, nb):
    vs = set(vs)
    if not vs:
        return True
    start = next(iter(vs))
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y in nb[x]:
            if y in vs and y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == len(vs)


def chains_of(n, nb):
    """Branches of a graph with a body of degree >= 3: (a, [x1..xk], b),
    k >= 0, ends of degree >= 3, interior of degree 2."""
    hubs = [v for v in range(n) if len(nb[v]) >= 3]
    hubset = set(hubs)
    seen = set()
    out = []
    for h in hubs:
        for f in sorted(nb[h]):
            if (h, f) in seen:
                continue
            path = []
            prev, cur = h, f
            seen.add((prev, cur))
            seen.add((cur, prev))
            while cur not in hubset:
                path.append(cur)
                nxt = [y for y in nb[cur] if y != prev]
                prev, cur = cur, nxt[0]
                seen.add((prev, cur))
                seen.add((cur, prev))
            out.append((h, path, cur))
    return out


def parse_g6(line):
    line = line.strip()
    data = [ord(c) - 63 for c in line]
    if data[0] < 63:
        n, data = data[0], data[1:]
    else:
        raise ValueError('graph6 n >= 63 unsupported')
    bits = []
    for x in data:
        for i in range(5, -1, -1):
            bits.append((x >> i) & 1)
    edges = []
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


# ------------------------------------------------------------ classification

def analyse(n, edges, want_rows=True):
    """Return None if G is outside the class C, else a dict."""
    V = list(range(n))
    nb = nbrs_of(n, edges)
    if any(len(nb[v]) < 2 for v in V):
        return None
    if not connected(V, nb):
        return None
    if all(len(nb[v]) == 2 for v in V):
        return None                                  # a cycle: row 3
    for v in V:
        if not connected([u for u in V if u != v], nb):
            return None                              # rows 1-2
    br = chains_of(n, nb)
    for a, xs, b in br:
        assert a != b, 'closed branch in a 2-connected non-cycle'
    # branch-union closures: every set with min degree >= 2 in G[W]
    closures = {}
    for mask in range(1, 1 << len(br)):
        W = set()
        for i, (a, xs, b) in enumerate(br):
            if mask >> i & 1:
                W.add(a)
                W.add(b)
                W.update(xs)
        W = frozenset(W)
        if W not in closures:
            closures[W] = len(induced(edges, W))
    # sparse <=> no planar-rigid set (lem:deficiency-sparse and converse)
    for W, eW in closures.items():
        if len(W) >= 2 and s_val(len(W), eW, 3) <= 0:
            return None                              # row 5 (or row 4)
    d2 = defD(V, edges, 3)
    d3 = defD(V, edges, 6)
    if d2 == d3:
        return None                                  # row 4
    res = {'n': n, 'm': len(edges), 'd2': d2, 'd3': d3,
           'chains': [], 'cores': [], 'rows': set()}
    ks = sorted(len(xs) for a, xs, b in br if xs)
    res['ks'] = ks
    # --- the core clause (7), second alternative (first is planar-rigid)
    for W, eW in closures.items():
        if len(W) < 2 or len(W) == n:
            continue
        if s_val(len(W), eW, 6) > 0:
            continue
        iw = induced(edges, W)
        if defD(W, iw, 6) != 0:
            continue
        if any(len(nb[v] & W) >= 2 for v in V if v not in W):
            continue
        r = min(W)
        cv = [v for v in V if v not in W] + [r]
        ce = []
        for u, w in edges:
            if u in W and w in W:
                continue
            ce.append((r if u in W else u, r if w in W else w))
        if defD(W, iw, 3) + defD(cv, ce, 3) <= d2:
            res['cores'].append(sorted(W))
            # additivity of the gap at a core (N4): equality in the planar
            # inequality (subadditivity) and def_3(G/W) = def_3(G)
            assert defD(W, iw, 3) + defD(cv, ce, 3) == d2
            assert defD(cv, ce, 6) == d3 and defD(W, iw, 6) == 0
            if 'gaps' not in res:
                g0 = d2 - d3
                res['gaps'] = {'core': (gap(sorted(W), iw) - g0,
                                        gap(cv, ce) - g0)}
    # --- the chain clauses (5), (6)
    for a, xs, b in br:
        k = len(xs)
        if k == 0:
            continue
        V1 = [v for v in V if v not in xs]
        E1 = induced(edges, V1)
        adj = b in nb[a]
        c = {'a': a, 'b': b, 'xs': xs, 'k': k, 'adj': adj, 'rows': set()}
        if k >= 3:
            c['rows'].add('long')
        else:
            e3 = defD(V1, E1, 6)
            m3 = merged(V1, E1, a, b, 6)
            e2 = defD(V1, E1, 3)
            m2 = merged(V1, E1, a, b, 3)
            c.update(d3V1=e3, m3V1=m3, d2V1=e2, m2V1=m2)
            if k == 2:
                if e3 <= d3:
                    c['rows'].add('two')             # thm:...-open-ear-two
                if not adj and m2 + 2 <= e2:
                    c['rows'].add('two_orbit')       # ...-open-ear-two-orbit
                if m3 == e3:
                    c['rows'].add('two_tab')         # the table's condition
            if k == 1:
                if not adj and e3 <= d3 and m2 + 2 <= e2:
                    c['rows'].add('one')             # ...-open-ear-one
                if not adj and m3 + 5 <= e3:
                    c['rows'].add('split')           # ...-splitoff
                if m3 == e3:
                    c['rows'].add('one_tab')
                if m3 + 5 <= e3:
                    c['rows'].add('split_tab')
        g0 = d2 - d3
        gl = res.setdefault('gaps', {})
        if 'core' in gl and len(gl) == 1 and False:
            pass
        for row in sorted(c['rows'] & set(STEP_ROWS)):
            key = row if row != 'long' else ('long5' if k >= 5 else
                                              'long%d' % k)
            if key in gl:
                continue
            if row in ('one', 'two') or key == 'long5':
                gl[key] = (gap(V1, E1) - g0,)
            elif row == 'two_orbit':
                vs, es = suppress(V, edges, xs[1], xs[0], b)
                gl[key] = (gap(V1, E1) - g0, gap(vs, es) - g0)
            elif row == 'split':
                vs, es = suppress(V, edges, xs[0], a, b)
                gl[key] = (gap(vs, es) - g0,)
            else:
                vs, es = suppress(V, edges, xs[1], xs[0], xs[2])
                gl[key] = (gap(V1, E1) - g0, gap(vs, es) - g0)
        res['chains'].append(c)
        res['rows'] |= c['rows']
    if res['cores']:
        res['rows'].add('core')
    # the predictions of the restructured Theorem S (N3), checked per graph:
    # (P1) a k = 2 chain with non-adjacent ends where open-ear-two-orbit fails
    #      forces a core (a rigid Z in V_1 holding a, b; core avoiding x_1);
    # (P2) a k = 2 chain with adjacent ends and def_3(G) > 0 forces a core;
    # (P3) the split-off applies only where def_3(G) > 0;
    # (P4) every chain k = 1 and def_3(G) > 0 forces a core.
    viol = []
    for c in res['chains']:
        if c['k'] == 2 and not c['adj'] and 'two_orbit' not in c['rows'] \
                and not res['cores']:
            viol.append('P1')
        if c['k'] == 2 and c['adj'] and d3 > 0 and not res['cores']:
            viol.append('P2')
        if 'split' in c['rows'] and d3 == 0:
            viol.append('P3')
    if ks and max(ks) == 1 and d3 > 0 and not res['cores']:
        viol.append('P4')
    res['viol'] = viol
    return res


STEP_ROWS = ('long', 'core', 'two', 'two_orbit', 'one', 'split')


def summarize(results, label, show=8):
    tot = len(results)
    resid = [r for r in results if not ({'long', 'core'} & r['rows'])]
    print(f'[{label}] class C members: {tot}; residual (no k>=3 chain, '
          f'no additive core): {len(resid)}')
    nostep = [r for r in resid if not (set(STEP_ROWS) & r['rows'])]
    print(f'  residual members with NO applicable clause (would refute '
          f'thm:pencil-x0-coverage): {len(nostep)}')
    combos = {}
    for r in resid:
        key = tuple(s for s in ('two', 'two_orbit', 'one', 'split')
                    if s in r['rows'])
        combos.setdefault(key, []).append(r)
    for key in sorted(combos, key=lambda k: (len(k), k)):
        rs = combos[key]
        # the rows in the table's order, so the line is independent of the hash seed
        shown = '{' + ', '.join(repr(k) for k in key) + '}'
        print(f'  short rows applicable = {shown}: {len(rs)}')
        for r in rs[:show]:
            print('     ', fmt(r))
    pv = {}
    for r in results:
        for v in r['viol']:
            pv[v] = pv.get(v, 0) + 1
    print(f'  violations of the restructured-Theorem-S predictions P1-P4: '
          f'{pv or 0}')
    # sole-step counts over the whole class (all clauses, not only residual)
    sole = {}
    for r in results:
        S = set(STEP_ROWS) & r['rows']
        if len(S) == 1:
            sole[next(iter(S))] = sole.get(next(iter(S)), 0) + 1
    print(f'  class members with exactly one applicable step, by step: '
          f'{dict(sorted(sole.items()))}')
    need = [r for r in results
            if not ({'long', 'core', 'two_orbit', 'one'} & r['rows'])]
    print(f'  class members with no step once open-ear-two and splitoff are '
          f'dropped: {len(need)}')
    for r in need[:show]:
        print('     ', fmt(r))
    if '--gap' in sys.argv:
        tab = {}
        for r in results:
            for key, dl in r.get('gaps', {}).items():
                tab.setdefault(key, {})
                tab[key][dl] = tab[key].get(dl, 0) + 1
        print('  gap change g(smaller) - g(G) per step, over the class '
              '(first instance of each step per graph; tuple = smaller '
              'graphs in the order of the table): ')
        for key in sorted(tab):
            print(f'    {key}: {dict(sorted(tab[key].items()))}')
    # the d >= 4 exception shape
    exc = [r for r in resid if r['ks'] and max(r['ks']) == 1 and r['d3'] == 0]
    print(f'  residual with every chain k = 1 and def_3 = 0 '
          f'(the d>=4 exception shape): {len(exc)}')
    return resid


def fmt(r):
    return (f"n={r['n']} m={r['m']} def2={r['d2']} def3={r['d3']} "
            f"gap={r['d2'] - r['d3']} ks={r['ks']} "
            f"chains=[" + '; '.join(
                f"{c['a']}-{''.join(str(x) + '-' for x in c['xs'])}{c['b']}"
                f"{'(adj)' if c['adj'] else ''}:{','.join(sorted(c['rows'])) or '-'}"
                for c in r['chains']) + ']')


# ------------------------------------------------------------ hub multigraphs

HUBS = {
    'theta3': (2, [(0, 1)] * 3),
    'theta4': (2, [(0, 1)] * 4),
    'theta5': (2, [(0, 1)] * 5),
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K4+': (4, [(0, 1), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'C4dbl': (4, [(0, 1), (0, 1), (1, 2), (1, 2), (2, 3), (2, 3),
                  (3, 0), (3, 0)]),
    'tri2': (3, [(0, 1), (0, 1), (1, 2), (1, 2), (0, 2), (0, 2)]),
    'tri21': (3, [(0, 1), (0, 1), (1, 2), (1, 2), (0, 2)]),
    'K33': (6, [(i, j) for i in range(3) for j in range(3, 6)]),
    'prism': (6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                  (0, 3), (1, 4), (2, 5)]),
    'W4': (5, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 0), (4, 1), (4, 2),
               (4, 3)]),
    'K5': (5, [(i, j) for i in range(5) for j in range(i + 1, 5)]),
    'K5-e': (5, [(i, j) for i in range(5) for j in range(i + 1, 5)
                 if (i, j) != (0, 1)]),
    'cube': (8, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7),
                 (7, 4), (0, 4), (1, 5), (2, 6), (3, 7)]),
}


def subdivide(h, hub_edges, ks):
    n = h
    edges = []
    for (u, w), k in zip(hub_edges, ks):
        prev = u
        for _ in range(k):
            edges.append((prev, n))
            prev = n
            n += 1
        edges.append((prev, w))
    return n, edges


def canon(n, edges):
    """Exact canonical form of a small graph: refine by degree, then
    brute-force permutations within the classes of hubs (bodies of degree
    >= 3 determine the graph together with the labelled hub multigraph)."""
    nb = nbrs_of(n, edges)
    hubs = [v for v in range(n) if len(nb[v]) >= 3]
    br = chains_of(n, nb)
    best = None
    for perm in permutations(range(len(hubs))):
        pos = {hubs[i]: perm[i] for i in range(len(hubs))}
        key = sorted((min(pos[a], pos[b]), max(pos[a], pos[b]), len(xs))
                     for a, xs, b in br)
        key = tuple(key)
        if best is None or key < best:
            best = key
    return (len(hubs), best)


def hub_population(name, maxk):
    """Every labelling of the hub edges by 0..maxk interior bodies whose
    subdivision is simple, up to the automorphisms of the hub multigraph
    (an isomorphism of two such subdivisions maps hubs to hubs and branches
    to branches, so this is isomorphism of the subdivisions)."""
    h, he = HUBS[name]
    target = sorted(tuple(sorted(e)) for e in he)
    auts = []
    for perm in permutations(range(h)):
        img = sorted(tuple(sorted((perm[u], perm[w]))) for u, w in he)
        if img == target:
            auts.append(perm)
    seen = set()
    out = []
    raw = 0
    for ks in product(range(maxk + 1), repeat=len(he)):
        n, edges = subdivide(h, he, ks)
        if len(set(frozenset(e) for e in edges)) < len(edges):
            continue                                  # not simple
        raw += 1
        key = min(tuple(sorted((min(p[u], p[w]), max(p[u], p[w]), k)
                               for (u, w), k in zip(he, ks)))
                  for p in auts)
        if key in seen:
            continue
        seen.add(key)
        out.append((n, edges, ks))
    return out, raw


# ----------------------------------------------------------------- validate

def validate():
    import random
    rng = random.Random(20261107)
    cnt = 0
    for trial in range(300):
        n = rng.randint(3, 8)
        p = rng.choice([0.3, 0.45, 0.6])
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)
                 if rng.random() < p]
        if not edges:
            continue
        V = list(range(n))
        for D in (3, 6, 10):
            assert defD(V, edges, D) == brute_def(V, edges, D), (n, edges, D)
            a, b = rng.sample(V, 2)
            assert merged(V, edges, a, b, D) == brute_def(
                V, edges, D, together=(a, b)), (n, edges, D, a, b)
        if len(set(v for e in edges for v in e)) == n:
            assert defD(V, edges, 6) == exact_deficiency(edges)[0]
        cnt += 1
    print(f'validate: {cnt} random graphs (seed 20261107, n in [3,8]): '
          f'pebble-game def_D and merged def_D agree with brute-force '
          f'partition maxima at D = 3, 6, 10, and def_6 with '
          f'kbare_common.exact_deficiency: OK')


def main(argv):
    if '--validate' in argv:
        validate()
        return
    show = 8
    if '--show' in argv:
        show = int(argv[argv.index('--show') + 1])
    if '--g6' in argv:
        results = []
        nread = 0
        byn = {}
        for line in sys.stdin:
            if not line.strip() or line.startswith('>'):
                continue
            n, edges = parse_g6(line)
            nread += 1
            r = analyse(n, edges)
            if r is not None:
                results.append(r)
                byn[n] = byn.get(n, 0) + 1
        print(f'population: {nread} graph6 graphs read from stdin; '
              f'class C members by n: {dict(sorted(byn.items()))}')
        summarize(results, 'g6', show)
        return
    if '--hub' in argv:
        names = argv[argv.index('--hub') + 1].split(',')
        maxk = 2
        if '--maxk' in argv:
            maxk = int(argv[argv.index('--maxk') + 1])
        for name in names:
            pop, raw = hub_population(name, maxk)
            results = []
            for n, edges, ks in pop:
                r = analyse(n, edges)
                if r is not None:
                    r['ks_pattern'] = ks
                    results.append(r)
            print(f'population: hub multigraph {name} {HUBS[name]}, every '
                  f'labelling with 0..{maxk} interior bodies per hub edge: '
                  f'{raw} simple labelled patterns, {len(pop)} up to '
                  f'isomorphism; class C members: {len(results)}')
            summarize(results, name, show)
        return
    print(__doc__)


if __name__ == '__main__':
    main(sys.argv[1:])
