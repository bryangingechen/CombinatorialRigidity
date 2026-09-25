#!/usr/bin/env python3
"""
mc15check.py -- §(K-main) Step MC15, the second reading of 2026-09-25 ((MC-161)): independent checks of
claims (MC-62)-(MC-67) (ported from the second reader's scratch; SEED unchanged, so the figures reproduce).  Stdlib only; shares NO code with notes/scripts/w4/*.
Exact rational arithmetic (fractions.Fraction); every random choice comes from
random.Random(<string seed>) (sha512 seeding: independent of PYTHONHASHSEED).

Objects (flex form, K-main Step MC15 *Notation*):
  F(G, q) = {P : V -> K^3 : (P_u - P_w).p^_u = (P_u - P_w).p^_w = 0 per edge uw},
  p^_v = (x_v, y_v, 1);  U_ab = {P_a - P_b};  val(P) = 3(|P|-1) - 2 d(P);
  def2 = max val (brute force over set partitions);  delta2 = def2(G) - def2(G/ab).
  classes: maximal vertex sets S, |S| >= 2, with def2(G[S]) = 0 (brute force), plus
  singletons.

A picture q is CERTIFIED for G when dim F(G, q) = 3 + def2(G) (the least possible
value, (MC-4)(b)); there dim U(q) <= min(delta2, 3) without citation and dim U is
lower semicontinuous, so an observed equality certifies the generic value; "U not
inside p^_b-perp" at a certified q is open, so it certifies the generic value;
"U inside p^_b-perp" at every certified draw is draw-level only.

Modes:
  --exh N        every connected simple graph on 2..N vertices (iso classes, own
                 canonical form, counts asserted against OEIS A001349), every
                 pair: (MC-62), (MC-63)(a),(b), (MC-64) incl. the Case-1/Case-2
                 split of the "only if".
  --allgraphs N  the same over EVERY simple graph on 2..N vertices (disconnected
                 and degree <= 1 included; counts asserted against OEIS A000088).
  --mc66 N       (MC-66) at every maximal def2-rigid R (|R| >= 3, R != V) of every
                 connected simple graph on <= N vertices, every ordered pair.
  --blowup S     S seeded blow-ups: a tight base graph (C4 or a tight 6- or 8-vertex
                 graph) with each vertex replaced by a rigid blob (K1, K3, K4, K_{2,3}),
                 base edges attached at random blob vertices.  (MC-64) at delta2 = 1
                 with nontrivial classes (its Case 2 contracts several classes, i.e.
                 (MC-66) iterated), and (MC-66) blob by blob.
  --tight n S    S seeded random tight graphs on n vertices (2|E| = 3n - 4, every
                 |Y| >= 2 has 2e(Y) <= 3|Y| - 4): (MC-65) at every non-adjacent
                 ordered pair.
  --mc67 N M     (MC-67)(a),(b),(c) by brute force: every connected simple graph on
                 <= N vertices and M seeded random connected multigraphs on <= 6
                 vertices, EVERY W with 1 <= |W| <= |V| - 1 (no rigidity, no
                 simplicity of G/H assumed).
"""
import itertools
import random
import sys
import time
from collections import Counter
from fractions import Fraction as Fr

SEED = 'readerD-20260925'
DRAWS = 4
SCALE = 30

# ---------------------------------------------------------------- linear algebra


def rref_null(rows, n):
    """Exact nullspace basis of the row list (length-n rows)."""
    M = [list(r) for r in rows if any(r)]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                Mr = M[r]
                M[i] = [x - f * y for x, y in zip(M[i], Mr)]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(n) if c not in set(piv)]
    basis = []
    for fc in free:
        v = [Fr(0)] * n
        v[fc] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis


def rank(rows):
    if not rows:
        return 0
    n = len(rows[0])
    return n - len(rref_null(rows, n))


def dot(u, v):
    return sum(x * y for x, y in zip(u, v))


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def hat(qv):
    return (Fr(qv[0]), Fr(qv[1]), Fr(1))

# ---------------------------------------------------------------- graphs


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


_PCACHE = {}


def partitions_labels(n):
    """All set partitions of range(n) as label tuples."""
    if n not in _PCACHE:
        out = []
        for P in set_partitions(range(n)):
            lab = [0] * n
            for i, blk in enumerate(P):
                for v in blk:
                    lab[v] = i
            out.append((len(P), tuple(lab)))
        _PCACHE[n] = out
    return _PCACHE[n]


def vals(V, E, k=3, l=2):
    """[(labels-by-vertex dict, val)] over all partitions of V; E a multiset list."""
    idx = {v: i for i, v in enumerate(V)}
    out = []
    for m, lab in partitions_labels(len(V)):
        d = sum(1 for (u, w) in E if lab[idx[u]] != lab[idx[w]])
        out.append((lab, k * (m - 1) - l * d))
    return idx, out


def defk(V, E, k=3, l=2):
    if len(V) == 0:
        return 0
    return max(x for _, x in vals(V, E, k, l)[1])


def induced(E, S):
    S = set(S)
    return [e for e in E if e[0] in S and e[1] in S]


def is_rigid(E, S):
    """|S| >= 2 and def2(G[S]) = 0 (brute force, with the two cheap prunings)."""
    S = sorted(S)
    if len(S) < 2:
        return False
    ES = induced(E, S)
    if 2 * len(ES) < 3 * len(S) - 3:
        return False
    deg = Counter()
    for u, w in ES:
        deg[u] += 1
        deg[w] += 1
    if any(deg[v] <= 1 for v in S):
        return False
    return defk(S, ES) == 0


def classes(V, E):
    """Maximal rigid sets (brute force over all subsets) plus singletons."""
    rig = [frozenset(S) for r in range(2, len(V) + 1) for S in itertools.combinations(V, r)
           if is_rigid(E, S)]
    maxl = [S for S in rig if not any(S < T for T in rig)]
    for S, T in itertools.combinations(maxl, 2):
        assert not (S & T), ('(MC-63)(a): maximal rigid sets intersect', S, T)
    cover = set().union(*maxl) if maxl else set()
    cls = list(maxl) + [frozenset([v]) for v in V if v not in cover]
    return cls


def canon(n, adj):
    """Canonical form of a simple graph on range(n), adj = list of bitmasks: colour
    refinement, then every colour-respecting permutation, lexicographically least
    upper-triangle bit string."""
    col = [bin(adj[v]).count('1') for v in range(n)]
    for _ in range(n):
        sig = [(col[v], tuple(sorted(col[w] for w in range(n) if adj[v] >> w & 1))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    groups = {}
    for v in range(n):
        groups.setdefault(col[v], []).append(v)
    order = sorted(groups)
    best = None
    for perms in itertools.product(*[itertools.permutations(groups[c]) for c in order]):
        seq = [v for p in perms for v in p]      # new label i -> old vertex seq[i]
        bits = tuple(1 if adj[seq[i]] >> seq[j] & 1 else 0 for i in range(n) for j in range(i + 1, n))
        if best is None or bits < best:
            best = bits
    return best


def graphs_upto(N, connected=True):
    """Iso classes of simple graphs on n = 1..N vertices, by vertex augmentation."""
    levels = {1: [((), 1)]}
    out = {1: [[]]}
    cur = {canon(1, [0]): [0]}
    for n in range(2, N + 1):
        nxt = {}
        for key, adj in cur.items():
            for mask in range(1 << (n - 1)):
                a2 = list(adj) + [mask]
                for v in range(n - 1):
                    if mask >> v & 1:
                        a2[v] |= 1 << (n - 1)
                c = canon(n, a2)
                if c not in nxt:
                    nxt[c] = a2
        cur = nxt
        lst = []
        for c, adj in cur.items():
            E = [(u, w) for u in range(n) for w in range(u + 1, n) if adj[u] >> w & 1]
            if connected and not is_connected(n, E):
                continue
            lst.append(E)
        out[n] = lst
    return out


def is_connected(n, E):
    if n == 0:
        return True
    nb = {v: set() for v in range(n)}
    for u, w in E:
        nb[u].add(w)
        nb[w].add(u)
    seen = {0}
    st = [0]
    while st:
        v = st.pop()
        for w in nb[v]:
            if w not in seen:
                seen.add(w)
                st.append(w)
    return len(seen) == n


def nbrs(V, E):
    nb = {v: set() for v in V}
    for u, w in E:
        nb[u].add(w)
        nb[w].add(u)
    return nb


def contract_set(V, E, R, star):
    """G/R (multigraph; loops dropped); R -> star."""
    R = set(R)
    V2 = [v for v in V if v not in R] + [star]
    E2 = []
    for u, w in E:
        u2 = star if u in R else u
        w2 = star if w in R else w
        if u2 != w2:
            E2.append((u2, w2))
    return V2, E2

# ---------------------------------------------------------------- flexes


def sample_q(rng, V, E):
    while True:
        q = {v: (rng.randint(-SCALE, SCALE), rng.randint(-SCALE, SCALE)) for v in V}
        if all(q[u] != q[w] for u, w in E) and len(set(q.values())) == len(V):
            return q


def flex_basis(V, E, q):
    idx = {v: i for i, v in enumerate(V)}
    n = 3 * len(V)
    rows = []
    for u, w in E:
        for pt in (q[u], q[w]):
            h = hat(pt)
            r = [Fr(0)] * n
            for k in range(3):
                r[3 * idx[u] + k] += h[k]
                r[3 * idx[w] + k] -= h[k]
            rows.append(r)
    return rref_null(rows, n), idx


def certified_draws(V, E, d2, tag, draws=DRAWS):
    """Up to `draws` certified pictures (dim F = 3 + def2); returns [(q, basis, idx)]."""
    out = []
    for t in range(draws):
        rng = random.Random(f'{SEED}:{tag}:{t}')
        q = sample_q(rng, V, E)
        B, idx = flex_basis(V, E, q)
        assert len(B) >= 3 + d2, ('(MC-4)(b) violated', tag)
        if len(B) == 3 + d2:
            out.append((q, B, idx))
    return out


def U_of(B, idx, a, b):
    ia, ib = 3 * idx[a], 3 * idx[b]
    return [[v[ia + k] - v[ib + k] for k in range(3)] for v in B]


def U_obs(draws, a, b):
    """(max dim U, p_b off pi_a at some draw, p_a off pi_b at some draw,
    max dim (U cap K l_ab))."""
    dU = 0
    boff = aoff = False
    for q, B, idx in draws:
        U = U_of(B, idx, a, b)
        dU = max(dU, rank(U))
        hb, ha = hat(q[b]), hat(q[a])
        boff = boff or any(dot(u, hb) for u in U)
        aoff = aoff or any(dot(u, ha) for u in U)
    return dU, boff, aoff


def U_cap_lab(q, B, idx, a, b):
    """dim(U cap K l_ab) = dim U - rank of U modulo l_ab."""
    U = U_of(B, idx, a, b)
    lab = cross(hat(q[a]), hat(q[b]))
    return rank(U) + 1 - rank(U + [list(lab)]) if rank(U) else 0

# ---------------------------------------------------------------- per-graph analysis


class Info:
    def __init__(self, V, E):
        self.V, self.E = V, E
        self.idx, self.vl = vals(V, E)
        self.f = max(x for _, x in self.vl)
        self.cls = classes(V, E)
        self.cof = {v: C for C in self.cls for v in C}
        self.nb = nbrs(V, E)

    def g(self, a, b):
        ia, ib = self.idx[a], self.idx[b]
        return max(x for lab, x in self.vl if lab[ia] == lab[ib])

    def delta2(self, a, b):
        return self.f - self.g(a, b)

    def gamma(self):
        """(MC-63)(a)'s Gamma: class-contracted graph (multigraph list)."""
        cl = self.cls
        ci = {v: i for i, C in enumerate(cl) for v in C}
        GE = [(ci[u], ci[w]) for u, w in self.E if ci[u] != ci[w]]
        return list(range(len(cl))), GE, ci


def check_mc63a(info, tally):
    VG, GE, ci = info.gamma()
    ms = Counter(tuple(sorted(e)) for e in GE)
    assert all(c == 1 for c in ms.values()), ('(MC-63)(a): Gamma not simple', info.E)
    for r in range(2, len(VG) + 1):
        for Y in itertools.combinations(VG, r):
            Ys = set(Y)
            e = sum(1 for u, w in GE if u in Ys and w in Ys)
            assert 2 * e <= 3 * r - 4, ('(MC-63)(a): bound fails', info.E, Y)
    # class partition optimal and coarsest optimal
    lab_cls = tuple(ci[v] for v in info.V)
    vcls = 3 * (len(info.cls) - 1) - 2 * len(GE)
    assert vcls == info.f, ('(MC-63)(a): class partition not optimal', info.E)
    for lab, x in info.vl:
        if x == info.f:   # every optimal partition refines the class partition
            blocks = {}
            for v in info.V:
                blocks.setdefault(lab[info.idx[v]], set()).add(ci[v])
            assert all(len(s) == 1 for s in blocks.values()), ('(MC-63)(a): optimal not refining', info.E)
    # delta2 formula
    for a, b in itertools.combinations(info.V, 2):
        A, B = ci[a], ci[b]
        best = None
        others = [x for x in VG if x not in (A, B)]
        for r in range(len(others) + 1):
            for Y in itertools.combinations(others, r):
                X = set(Y) | {A, B}
                e = sum(1 for u, w in GE if u in X and w in X)
                loss = 3 * (len(X) - 1) - 2 * e
                best = loss if best is None else min(best, loss)
        d2 = info.delta2(a, b)
        assert d2 == best, ('(MC-63)(a): delta2 formula', info.E, a, b, d2, best)
        assert (d2 == 0) == (A == B)
        if b in info.nb[a] or any({ci[u], ci[w]} == {A, B} for u, w in info.E):
            assert d2 <= 1, ('(MC-63)(a): adjacent classes with delta2 >= 2', info.E, a, b)
        tally['(MC-63)(a) pairs checked'] += 1


def orbit_pred(info, a, b):
    d2 = info.delta2(a, b)
    adj = b in info.nb[a]
    if adj:
        return min(d2, 1), ('iv' if d2 == 0 else 'iii'), d2, None
    if d2 == 0:
        return 0, 'iv', d2, None
    if d2 >= 2:
        return min(d2, 3), 'i', d2, None
    A, B = info.cof[a], info.cof[b]
    b_on = any(w in A for w in info.nb[b])      # p_b in pi_a predicted
    a_on = any(w in B for w in info.nb[a])
    assert not (a_on and b_on), '(MC-64): both incidences predicted'
    # "only if" case split for the b-incidence
    AB_edge = any((u in A and w in B) or (u in B and w in A) for u, w in info.E)
    nontriv = any(len(C) >= 2 for C in info.cls)
    case = 'b_on(if)' if b_on else ('Case1' if AB_edge else ('Case2-contract' if nontriv else 'Case2-trivial'))
    return 1, ('ii' if (a_on or b_on) else 'i'), d2, (b_on, a_on, case)


def orbit_obs(dU, boff, aoff):
    if dU == 0:
        return 'iv'
    if boff and aoff:
        return 'i'
    if boff or aoff:
        return 'ii'
    return 'iii'


def analyse_graph(V, E, tag, tally, bad, want63b=True):
    info = Info(V, E)
    check_mc63a(info, tally)
    dr = certified_draws(V, E, info.f, tag)
    if not dr:
        tally['graphs with no certified picture'] += 1
        return
    for a, b in itertools.combinations(V, 2):
        pdU, porb, d2, extra = orbit_pred(info, a, b)
        dU, boff, aoff = U_obs(dr, a, b)
        oorb = orbit_obs(dU, boff, aoff)
        adj = b in info.nb[a]
        # (MC-62): certified upper bound, so equality certifies
        assert dU <= pdU, ('(MC-62) upper bound violated at a certified picture', E, a, b)
        key = ('adj' if adj else 'nonadj', f'd2={min(d2, 3)}')
        if dU == pdU:
            tally[('(MC-62) certified', key)] += 1
        else:
            tally[('(MC-62) NOT certified (draw below)', key)] += 1
            bad.append(('MC-62', tag, E, a, b, dU, pdU))
        if oorb == porb:
            tally[('(MC-64) orbit match', porb, key)] += 1
        else:
            tally[('(MC-64) orbit MISMATCH', porb, oorb, key)] += 1
            bad.append(('MC-64', tag, E, a, b, porb, oorb, extra))
        if extra is not None:
            for (x, y, on_pred, off_obs) in ((a, b, extra[0], boff), (b, a, extra[1], aoff)):
                # re-derive the case for the ordered pair (x, y): incidence p_y in pi_x
                X, Y = info.cof[x], info.cof[y]
                on = any(w in X for w in info.nb[y])
                ABe = any((u in X and w in Y) or (u in Y and w in X) for u, w in E)
                nontriv = any(len(C) >= 2 for C in info.cls)
                case = 'if' if on else ('Case1' if ABe else ('Case2-contract' if nontriv else 'Case2-trivial'))
                tally[('(MC-64) d2=1 ordered pair', case,
                       'certified off' if off_obs else 'on at every draw')] += 1
        if want63b and not adj and dU == pdU:
            # (MC-63)(b): dim(U cap K l_ab) = [delta2 >= 3], at a picture where both
            # F(G') and F(G'+ab) are certified
            Eab = E + [(a, b)]
            f_ab = defk(V, Eab)
            for q, B, idx in dr:
                Bab, _ = flex_basis(V, Eab, q)
                if len(Bab) != 3 + f_ab:
                    continue
                if rank(U_of(B, idx, a, b)) != pdU:
                    continue
                c = U_cap_lab(q, B, idx, a, b)
                ok = (c == (1 if d2 >= 3 else 0))
                tally[('(MC-63)(b)', f'd2={min(d2, 3)}', 'ok' if ok else 'FAIL')] += 1
                if not ok:
                    bad.append(('MC-63b', tag, E, a, b, c, d2))
                break
            else:
                tally[('(MC-63)(b)', 'no doubly-certified picture')] += 1


def mode_exh(N, connected=True):
    t0 = time.time()
    G = graphs_upto(N, connected)
    counts = [len(G[n]) for n in range(1, N + 1)]
    ref = [1, 1, 2, 6, 21, 112, 853, 11117] if connected else [1, 2, 4, 11, 34, 156, 1044, 12346]
    assert counts == ref[:N], ('iso-class counts', counts)
    print(f"{'connected' if connected else 'all'} simple graphs on 1..{N} vertices: {counts} (OEIS asserted)")
    tally, bad = Counter(), []
    for n in range(2, N + 1):
        for gi, E in enumerate(G[n]):
            analyse_graph(list(range(n)), E, f"{'c' if connected else 'a'}{n}:{gi}", tally, bad)
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  failures / uncertified: {len(bad)}')
    for x in bad[:25]:
        print('   ', x)
    print(f'  [{time.time() - t0:.1f} s]')

# ---------------------------------------------------------------- (MC-66)


def incidence(draws, x, y):
    """'off' if U_xy not inside p^_y-perp at some certified draw, else 'on'."""
    for q, B, idx in draws:
        hy = hat(q[y])
        if any(dot(u, hy) for u in U_of(B, idx, x, y)):
            return 'off'
    return 'on'


def mc66_instance(V, E, R, tag, tally, bad, info=None):
    info = info or Info(V, E)
    star = ('*', tag)
    V2, E2 = contract_set(V, E, R, star)
    ms = Counter(tuple(sorted(map(str, e))) for e in E2)
    assert all(c == 1 for c in ms.values()), ('(MC-66): G/R not simple at a maximal R', E, R)
    f2 = defk(V2, E2)
    assert f2 == info.f, ('(MC-66): def2 not kept by contraction', E, R)
    dr1 = certified_draws(V, E, info.f, tag + ':G')
    dr2 = certified_draws(V2, E2, f2, tag + ':GR')
    if not dr1 or not dr2:
        tally['(MC-66) no certified picture'] += 1
        return
    idx2, vl2 = vals(V2, E2)
    nb2 = nbrs(V2, E2)
    img = {v: (star if v in R else v) for v in V}
    for x, y in itertools.permutations(V, 2):
        if x in R and y in R:
            continue
        xb, yb = img[x], img[y]
        d2 = info.delta2(x, y)
        g2 = max(val for lab, val in vl2 if lab[idx2[xb]] == lab[idx2[yb]])
        assert f2 - g2 == d2, ('(MC-66)/(MC-64): delta2 not kept', E, R, x, y)
        i1 = incidence(dr1, x, y)
        if yb in nb2[xb]:
            tally[('(MC-66) images adjacent (vacuous)', f'G:{i1}')] += 1
            continue
        i2 = incidence(dr2, xb, yb)
        tally[('(MC-66)', f'd2={min(d2, 3)}', f'G:{i1}', f'G/R:{i2}')] += 1
        if i1 == 'on' and i2 == 'off':
            bad.append(('MC-66 candidate', tag, E, sorted(R), x, y))


def mode_mc66(N):
    t0 = time.time()
    G = graphs_upto(N, True)
    tally, bad = Counter(), []
    for n in range(4, N + 1):
        for gi, E in enumerate(G[n]):
            V = list(range(n))
            info = Info(V, E)
            for C in info.cls:
                if len(C) >= 3 and len(C) < n:
                    mc66_instance(V, E, set(C), f'm{n}:{gi}:{sorted(C)}', tally, bad, info)
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  (MC-66) candidate counterexamples (G on at every draw, G/R certified off): {len(bad)}')
    for x in bad[:20]:
        print('   ', x)
    print(f'  [{time.time() - t0:.1f} s]')

# ---------------------------------------------------------------- tight graphs, blow-ups


def is_tight(n, E):
    if 2 * len(E) != 3 * n - 4:
        return False
    for r in range(2, n):
        for Y in itertools.combinations(range(n), r):
            Ys = set(Y)
            if 2 * sum(1 for u, w in E if u in Ys and w in Ys) > 3 * r - 4:
                return False
    return True


def random_tight(n, rng, cap=200000):
    m = (3 * n - 4) // 2
    allp = [(u, w) for u in range(n) for w in range(u + 1, n)]
    for _ in range(cap):
        E = rng.sample(allp, m)
        deg = Counter()
        for u, w in E:
            deg[u] += 1
            deg[w] += 1
        if any(deg[v] < 2 for v in range(n)):
            continue
        if is_tight(n, E):
            return sorted(E)
    return None


def mode_tight(n, S):
    t0 = time.time()
    tally, bad = Counter(), []
    rng = random.Random(f'{SEED}:tight:{n}')
    seen = set()
    for s in range(S):
        E = random_tight(n, rng)
        if E is None:
            tally['generation cap hit'] += 1
            continue
        adj = [0] * n
        for u, w in E:
            adj[u] |= 1 << w
            adj[w] |= 1 << u
        c = canon(n, adj) if n <= 10 else tuple(E)
        tally['iso-new' if c not in seen else 'iso-repeat'] += 1
        seen.add(c)
        V = list(range(n))
        dr = certified_draws(V, E, 1, f'tight{n}:{s}', draws=2)
        if not dr:
            tally['no certified picture'] += 1
            continue
        nb = nbrs(V, E)
        for a, b in itertools.permutations(V, 2):
            if b in nb[a]:
                continue
            inc = incidence(dr, a, b)
            dU = max(rank(U_of(B, idx, a, b)) for q, B, idx in dr)
            tally[('(MC-65)', f'dimU={dU}', f'p_b {inc} pi_a')] += 1
            if inc == 'on':
                bad.append((n, s, E, a, b))
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  (MC-65) candidates (p_b on pi_a at every certified draw): {len(bad)}')
    for x in bad[:10]:
        print('   ', x)
    print(f'  distinct iso classes among the sample: {len(seen)}  [{time.time() - t0:.1f} s]')


BLOBS = {
    'K1': (1, []),
    'K3': (3, [(0, 1), (1, 2), (0, 2)]),
    'K4': (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K23': (5, [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]),
}


def blowup(base_n, base_E, rng):
    names = [rng.choice(['K1', 'K3', 'K3', 'K4', 'K23']) for _ in range(base_n)]
    V, E, blob, off = [], [], [], 0
    for i, nm in enumerate(names):
        k, bE = BLOBS[nm]
        vs = list(range(off, off + k))
        V += vs
        E += [(off + u, off + w) for u, w in bE]
        blob.append(vs)
        off += k
    for u, w in base_E:
        E.append((rng.choice(blob[u]), rng.choice(blob[w])))
    return V, E, blob, names


def mode_blowup(S):
    t0 = time.time()
    for nm, (k, bE) in BLOBS.items():
        if k >= 2:
            assert is_rigid(bE, range(k)), nm
    rng = random.Random(f'{SEED}:blowup')
    bases = [(4, [(0, 1), (1, 2), (2, 3), (0, 3)])]
    for n in (6, 8):
        r2 = random.Random(f'{SEED}:bases:{n}')
        for _ in range(2 if n == 6 else 2):
            bases.append((n, random_tight(n, r2)))
    for bn, bE in bases:
        assert is_tight(bn, bE)
    tally, bad = Counter(), []
    for s in range(S):
        bn, bE = bases[s % len(bases)]
        V, E, blob, names = blowup(bn, bE, rng)
        f = 3 * (bn - 1) - 2 * len(bE)          # val of the blob partition = 1
        assert f == 1
        dr = certified_draws(V, E, f, f'blow:{s}', draws=2)
        tag = f'blow{s}:{bn}:{"-".join(names)}'
        if not dr:
            tally['no certified picture'] += 1
            continue
        tally[('blow-up instances', f'|V|={len(V)}')] += 1
        cof = {v: i for i, vs in enumerate(blob) for v in vs}
        nb = nbrs(V, E)
        ntriv = sum(1 for vs in blob if len(vs) >= 3)
        for a, b in itertools.permutations(V, 2):
            A, B = cof[a], cof[b]
            if A == B or b in nb[a]:
                continue
            # delta2 = 1: the blob partition with the tight base V merged is a partition
            # with a ~ b of value f - 1 = 0, so g >= 0, delta2 <= 1; a certified dim U = 1
            # then forces delta2 >= 1.
            dU = max(rank(U_of(Bs, idx, a, b)) for q, Bs, idx in dr)
            if dU != 1:
                bad.append(('blowup dim U != 1', tag, a, b, dU))
                continue
            on = any(cof[w] == A for w in nb[b])
            ABe = any((cof[u], cof[w]) in ((A, B), (B, A)) for u, w in E)
            case = 'if' if on else ('Case1' if ABe else f'Case2-contract({ntriv} blobs)')
            inc = incidence(dr, a, b)
            tally[('(MC-64) blow-up d2=1', case, f'p_b {inc} pi_a')] += 1
            if (on and inc == 'off') or ((not on) and inc == 'on'):
                bad.append(('MC-64 blowup', tag, E, a, b, case, inc))
        # (MC-66) at each nontrivial blob
        if len(V) <= 16:
            info = None
            for i, vs in enumerate(blob):
                if len(vs) >= 3:
                    mc66_blow(V, E, set(vs), blob, tag + f':R{i}', tally, bad)
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  failures: {len(bad)}')
    for x in bad[:20]:
        print('   ', x)
    print(f'  [{time.time() - t0:.1f} s]')


def mc66_blow(V, E, R, blob, tag, tally, bad):
    """(MC-66) at one blob R of a blow-up (def2 = 1 on both sides by the blob
    partition bound + certification)."""
    star = ('*', tag)
    V2, E2 = contract_set(V, E, R, star)
    dr1 = certified_draws(V, E, 1, tag + ':G', draws=2)
    dr2 = certified_draws(V2, E2, 1, tag + ':GR', draws=2)
    if not dr1 or not dr2:
        tally['(MC-66) blow-up: no certified picture'] += 1
        return
    nb2 = nbrs(V2, E2)
    img = {v: (star if v in R else v) for v in V}
    cof = {v: i for i, vs in enumerate(blob) for v in vs}
    for x, y in itertools.permutations(V, 2):
        if (x in R and y in R) or cof[x] == cof[y]:
            continue
        xb, yb = img[x], img[y]
        if yb in nb2[xb]:
            continue
        i1, i2 = incidence(dr1, x, y), incidence(dr2, xb, yb)
        tally[('(MC-66) blow-up', f'G:{i1}', f'G/R:{i2}')] += 1
        if i1 == 'on' and i2 == 'off':
            bad.append(('MC-66 blowup candidate', tag, x, y))

# ---------------------------------------------------------------- (MC-67)


def finest_coarsest(V, E):
    idx, vl = vals(V, E)
    f = max(x for _, x in vl)
    opt = [lab for lab, x in vl if x == f]
    return idx, vl, f, opt


def meet_join(l1, l2):
    n = len(l1)
    meet = [(l1[i], l2[i]) for i in range(n)]
    # join: union-find over i ~ j if same block in either
    par = list(range(n))

    def fd(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for lab in (l1, l2):
        first = {}
        for i in range(n):
            if lab[i] in first:
                par[fd(i)] = fd(first[lab[i]])
            else:
                first[lab[i]] = i
    join = [fd(i) for i in range(n)]
    return norm(meet), norm(join)


def norm(lab):
    m = {}
    return tuple(m.setdefault(x, len(m)) for x in lab)


def check_mc67(V, E, tag, tally, bad, simple):
    n = len(V)
    idx, vl, f, opt = finest_coarsest(V, E)
    optset = set(norm(l) for l in opt)
    # (a) sublattice
    for l1, l2 in itertools.combinations(list(optset)[:40], 2):
        m, j = meet_join(l1, l2)
        if m not in optset or j not in optset:
            bad.append(('MC-67a sublattice', tag, E))
    # coarsest = class partition
    cls = classes(V, E)
    ci = {v: i for i, C in enumerate(cls) for v in C}
    lab_cls = norm(tuple(ci[v] for v in V))
    refines = all(len({lab_cls[i] for i in range(n) if l[i] == blk}) == 1
                  for l in optset for blk in set(l))
    if lab_cls not in optset or not refines:
        bad.append(('MC-67a coarsest != class partition', tag, E))
    tally['(MC-67)(a) graphs'] += 1
    f3 = defk(V, E, 6, 5)
    for r in range(1, n):
        for W in itertools.combinations(V, r):
            Ws = set(W)
            H = induced(E, Ws)
            star = ('*',)
            V2, E2 = contract_set(V, E, Ws, star)
            dH = defk(list(W), H)
            idx2, vl2, dQ, opt2 = finest_coarsest(V2, E2)
            # (b)
            if f > dH + dQ:
                bad.append(('MC-67b def2', tag, E, W))
            if f3 > defk(list(W), H, 6, 5) + defk(V2, E2, 6, 5):
                bad.append(('MC-67b def3', tag, E, W))
            # (c): finest optimal partition of G/H
            fin = None
            for l in opt2:
                if fin is None or len(set(l)) > len(set(fin)):
                    fin = l
            sstar = fin[idx2[star]]
            T = {v for v in V2 if v != star and fin[idx2[v]] == sstar}
            Hcls = classes(list(W), H)
            hci = {v: i for i, C in enumerate(Hcls) for v in C}
            # Phi: vertices T u W, edges of G inside T or between T and W
            par = {v: v for v in T | Ws}

            def fd(x):
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x
            for u, w in E:
                inT_u, inT_w = u in T, w in T
                if (inT_u and inT_w) or (inT_u and w in Ws) or (inT_w and u in Ws):
                    par[fd(u)] = fd(w)
            comp_cls = {}
            for v in Ws:
                comp_cls.setdefault(fd(v), set()).add(hci[v])
            cond = all(len(s) <= 1 for s in comp_cls.values())
            additive = (f == dH + dQ)
            tally[('(MC-67)(c)', 'simple G' if simple else 'multigraph G',
                   'additive' if additive else 'not additive',
                   'cond' if cond else 'no cond', 'T empty' if not T else 'T nonempty')] += 1
            if additive != cond:
                bad.append(('MC-67c', tag, E, W, additive, cond))


def random_multigraph(rng, n):
    while True:
        m = rng.randint(n - 1, 2 * n + 1)
        E = []
        for _ in range(m):
            u, w = rng.sample(range(n), 2)
            E.append((min(u, w), max(u, w)))
        if is_connected(n, E):
            return E


def mode_mc67(N, M):
    t0 = time.time()
    G = graphs_upto(N, True)
    tally, bad = Counter(), []
    for n in range(2, N + 1):
        for gi, E in enumerate(G[n]):
            check_mc67(list(range(n)), E, f's{n}:{gi}', tally, bad, True)
    rng = random.Random(f'{SEED}:multi')
    for s in range(M):
        n = rng.randint(3, 6)
        E = random_multigraph(rng, n)
        check_mc67(list(range(n)), E, f'mg{s}', tally, bad, False)
    for k, v in sorted(tally.items(), key=str):
        print(f'  {k}: {v}')
    print(f'  (MC-67) failures: {len(bad)}')
    for x in bad[:20]:
        print('   ', x)
    print(f'  [{time.time() - t0:.1f} s]')


def main(argv):
    if not argv:
        print(__doc__)
        return
    mode = argv[0]
    if mode == '--exh':
        mode_exh(int(argv[1]), True)
    elif mode == '--allgraphs':
        mode_exh(int(argv[1]), False)
    elif mode == '--mc66':
        mode_mc66(int(argv[1]))
    elif mode == '--blowup':
        mode_blowup(int(argv[1]))
    elif mode == '--tight':
        mode_tight(int(argv[1]), int(argv[2]))
    elif mode == '--mc67':
        mode_mc67(int(argv[1]), int(argv[2]))
    else:
        print(__doc__)


if __name__ == '__main__':
    main(sys.argv[1:])
