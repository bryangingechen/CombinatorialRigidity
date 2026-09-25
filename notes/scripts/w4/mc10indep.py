#!/usr/bin/env python3
"""
mc10indep.py -- (§(K-main) Step MC10's second reading, 2026-09-25; ported from the reader's scratch) reader F's independent re-check of
K-main Steps MC1-MC6 and MC10 (the seed strings keep the reader's name).

Stdlib only; exact rational arithmetic (fractions.Fraction) throughout; no code shared with
notes/scripts/.  Seeded with string seeds 'readerF:<mode>:<i>'.  Run:

    python3 notes/scripts/w4/mc10indep.py all          # every test below
    python3 indep.py <name>       # one of: mc3 mc4 mc5 mc6 mc16 mc17 mc18 mc19 caps links crit

Populations (all built here):
  * random simple connected graphs with min degree >= 2 on 4..7 vertices (edge prob. p drawn
    per graph from {0.35, 0.5, 0.7}), plus named graphs (K4, K_{2,3}, C4, C5, theta(2,2,3), W5,
    prism, K_{3,3});
  * planar pictures q: integer coordinates in [-S, S], S drawn from {2, 3, 30} so that small
    scales hit jump strata (dim L(q) > 3 + def2) and admissibility boundaries often;
  * flag frames for the orbits (i), (ii) [p_b in pi_a], (ii') [p_a in pi_b], (iii), (iv): a
    canonical frame pushed through a random integer projective transformation T (det != 0).
Every figure printed is exact; "generic" values of spans are certified by an exhibited draw
reaching the trivial maximum (lower semicontinuity), intersections by span-guarded draws.
"""
import itertools
import random
import sys
from fractions import Fraction as Fr

# ------------------------------------------------------------------ exact linear algebra

def rref(M):
    M = [list(map(Fr, r)) for r in M]
    piv = []
    r = 0
    ncol = len(M[0]) if M else 0
    for c in range(ncol):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return M[:r], piv


def rank(M):
    if not M or not M[0]:
        return 0
    return len(rref(M)[1])


def nullspace(M, ncol):
    """basis of {x in Q^ncol : M x = 0}"""
    if not M:
        return [[Fr(int(i == j)) for j in range(ncol)] for i in range(ncol)]
    R, piv = rref(M)
    free = [c for c in range(ncol) if c not in piv]
    out = []
    for f in free:
        v = [Fr(0)] * ncol
        v[f] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -R[i][f]
        out.append(v)
    return out


def dim_sum(A, B):
    return rank(A + B) if (A or B) else 0


def dim_cap(A, B):
    """dim(span A cap span B)"""
    return rank(A) + rank(B) - dim_sum(A, B)


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


PLK = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def wedge(P, Q):
    return [P[i] * Q[j] - P[j] * Q[i] for (i, j) in PLK]


# ------------------------------------------------------------------ graphs

def nbrs(V, E):
    nb = {v: set() for v in V}
    for u, w in E:
        nb[u].add(w)
        nb[w].add(u)
    return nb


def connected(V, E):
    nb = nbrs(V, E)
    seen = {V[0]}
    st = [V[0]]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == len(V)


def satisfies_H(V, E):
    nb = nbrs(V, E)
    return connected(V, E) and all(len(nb[v]) >= 2 for v in V) and len(set(map(frozenset, E))) == len(E)


def rand_graph(rng, nmin=4, nmax=7):
    while True:
        n = rng.randint(nmin, nmax)
        p = rng.choice([0.35, 0.5, 0.7])
        V = list(range(n))
        E = [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]
        if satisfies_H(V, E):
            return V, E


NAMED = {
    'K4': (list(range(4)), [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    'K23': (list(range(5)), [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]),
    'C4': (list(range(4)), [(0, 1), (1, 2), (2, 3), (3, 0)]),
    'C5': (list(range(5)), [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    'th223': (list(range(6)), [(0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 5), (5, 1)]),
    'W5': (list(range(6)), [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] + [(5, i) for i in range(5)]),
    'prism': (list(range(6)), [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]),
    'K33': (list(range(6)), [(i, j) for i in range(3) for j in range(3, 6)]),
}


def set_partitions(V):
    V = list(V)
    n = len(V)

    def rec(i, lab, m):
        if i == n:
            yield list(lab)
            return
        for c in range(m + 1):
            lab.append(c)
            yield from rec(i + 1, lab, max(m, c + 1))
            lab.pop()
    yield from rec(0, [], 0)


def deficiency(V, E, D, together=None):
    """max_P D(|P|-1) - (D-1) d(P); `together=(a,b)` restricts to partitions with a, b in one part."""
    idx = {v: i for i, v in enumerate(V)}
    best = None
    for lab in set_partitions(V):
        if together and lab[idx[together[0]]] != lab[idx[together[1]]]:
            continue
        parts = max(lab) + 1
        d = sum(1 for u, w in E if lab[idx[u]] != lab[idx[w]])
        val = D * (parts - 1) - (D - 1) * d
        if best is None or val > best:
            best = val
    return best


def deficiency_dp(V, E, D, together=None):
    """same quantity as `deficiency`, by subset DP: val(P) = -D - (D-1)|E| + sum_parts [D + (D-1) e(S)]."""
    n = len(V)
    idx = {v: i for i, v in enumerate(V)}
    em = [(1 << idx[u]) | (1 << idx[w]) for u, w in E]
    full = (1 << n) - 1
    eS = [0] * (1 << n)
    for S in range(1 << n):
        eS[S] = sum(1 for m in em if m & S == m)
    ta = tb = None
    if together:
        ta, tb = 1 << idx[together[0]], 1 << idx[together[1]]
    best = [None] * (1 << n)
    best[0] = 0
    for mask in range(1, 1 << n):
        low = mask & -mask
        rest = mask ^ low
        sub = rest
        bv = None
        while True:
            S = sub | low
            ok = True
            if ta is not None and (bool(S & ta) != bool(S & tb)) and ((mask & ta) and (mask & tb)):
                ok = False
            if ta is not None and (bool(mask & ta) != bool(mask & tb)):
                ok = False
            if ok and best[mask ^ S] is not None:
                val = D + (D - 1) * eS[S] + best[mask ^ S]
                if bv is None or val > bv:
                    bv = val
            if sub == 0:
                break
            sub = (sub - 1) & rest
        best[mask] = bv
    return -D - (D - 1) * len(E) + best[full]


# ------------------------------------------------------------------ pictures, L(q), F(q), R

def admissible(V, E, q):
    nb = nbrs(V, E)
    if any(q[u] == q[w] for u, w in E):
        return False
    for v in V:
        N = [v] + sorted(nb[v])
        if len(N) >= 3 and rank([[1, q[w][0], q[w][1]] for w in N]) < 3:
            return False
    return True


def rand_q(rng, V, E, S):
    for _ in range(10000):
        q = {v: (Fr(rng.randint(-S, S)), Fr(rng.randint(-S, S))) for v in V}
        if admissible(V, E, q):
            return q
    return None


def L_space(V, E, q):
    nb = nbrs(V, E)
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for v in V:
        N = [v] + sorted(nb[v])
        A = [[Fr(1), q[w][0], q[w][1]] for w in N]
        At = [list(c) for c in zip(*A)]
        for c in nullspace(At, len(N)):
            r = [Fr(0)] * len(V)
            for w, cw in zip(N, c):
                r[idx[w]] += cw
            rows.append(r)
    return nullspace(rows, len(V))


def F_dim(V, E, q):
    """dim of F(q) = {(h_v) : (h_u - h_w)(q_u) = (h_u - h_w)(q_w) = 0 on edges}, straight from the definition."""
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for u, w in E:
        for pnt in (q[u], q[w]):
            r = [Fr(0)] * (3 * len(V))
            ph = [pnt[0], pnt[1], Fr(1)]
            for t in range(3):
                r[3 * idx[u] + t] += ph[t]
                r[3 * idx[w] + t] -= ph[t]
            rows.append(r)
    return 3 * len(V) - rank(rows)


def hat4(pnt):
    return [Fr(pnt[0]), Fr(pnt[1]), Fr(pnt[2]), Fr(1)]


def R_rows(V, E, P):
    """5 rows per hinge: a basis of C_e^perp (standard dot product) at u, minus at w."""
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for u, w in E:
        C = wedge(P[u], P[w])
        assert any(C), 'coincident adjacent points'
        for b in nullspace([C], 6):
            r = [Fr(0)] * (6 * len(V))
            for t in range(6):
                r[6 * idx[u] + t] += b[t]
                r[6 * idx[w] + t] -= b[t]
            rows.append(r)
    return rows


def conf(V, q, z):
    return {v: hat4((q[v][0], q[v][1], z[i])) for i, v in enumerate(V)}


def interp(V, E, q, z):
    nb = nbrs(V, E)
    idx = {v: i for i, v in enumerate(V)}
    out = {}
    for v in V:
        N = [v] + sorted(nb[v])
        for tri in itertools.combinations(N, 3):
            T = [[q[w][0], q[w][1], Fr(1)] for w in tri]
            if rank(T) == 3:
                break
        R, _ = rref([T[i] + [z[idx[tri[i]]]] for i in range(3)])
        h = [R[0][3], R[1][3], R[2][3]]
        for w in N:
            assert h[0] * q[w][0] + h[1] * q[w][1] + h[2] == z[idx[w]], 'z not in L(q)'
        out[v] = h
    return out


# ------------------------------------------------------------------ tests

def t_mc3(n=40):
    """(MC-3): the explicit Plucker formula, and rank A = |E| + rank R."""
    rng = random.Random('readerF:mc3')
    bad = 0
    for i in range(n):
        xu, yu, zu, xv, yv, zv = [Fr(rng.randint(-20, 20)) for _ in range(6)]
        C = wedge([xu, yu, zu, 1], [xv, yv, zv, 1])
        form = [xu * yv - yu * xv + 0, xu * zv - zu * xv, xu - xv, yu * zv - zu * yv, yu - yv, zu - zv]
        bad += C != form
    # rank A = |E| + rank R at random pencil points of random graphs
    for i in range(12):
        V, E = rand_graph(rng, 4, 6)
        q = rand_q(rng, V, E, 30)
        L = L_space(V, E, q)
        cf = [rng.randint(-5, 5) for _ in L]
        z = [sum(c * b[j] for c, b in zip(cf, L)) for j in range(len(V))]
        P = conf(V, q, z)
        idx = {v: j for j, v in enumerate(V)}
        A = []
        for ei, (u, w) in enumerate(E):
            C = wedge(P[u], P[w])
            for k in range(6):
                r = [Fr(0)] * (6 * len(V) + len(E))
                r[6 * idx[u] + k] += 1
                r[6 * idx[w] + k] -= 1
                r[6 * len(V) + ei] = -C[k]
                A.append(r)
        bad += rank(A) != len(E) + rank(R_rows(V, E, P))
    print(f'mc3: Plucker formula 40/40 and rank A = |E| + rank R 12/12 -> {"OK" if not bad else "FAIL %d" % bad}')
    return bad


def t_mc4(n=150):
    """(MC-4)(a): rank R(q,0) = 6|V| - 3 - dim L(q) at EVERY admissible q (incl. jump strata);
    Step MC4's F(q) = L(q) in dimension; (b) dim L >= 3 + def2; (MC-5)(i) def3 <= def2."""
    rng = random.Random('readerF:mc4')
    bad = 0
    jumps = 0
    tested = 0
    pops = [NAMED[k] for k in NAMED] + [rand_graph(rng) for _ in range(n)]
    for (V, E) in pops:
        d2 = deficiency(V, E, 3)
        d3 = deficiency(V, E, 6)
        if d3 > d2:
            bad += 1
            print('  (MC-5)(i) FAILS', V, E)
        for S in (2, 3, 30):
            q = rand_q(rng, V, E, S)
            if q is None:
                continue
            tested += 1
            dL = len(L_space(V, E, q))
            dF = F_dim(V, E, q)
            rk0 = rank(R_rows(V, E, conf(V, q, [0] * len(V))))
            if dL > 3 + d2:
                jumps += 1
            if rk0 != 6 * len(V) - 3 - dL or dF != dL or dL < 3 + d2:
                bad += 1
                print('  (MC-4) FAILS', V, E, q, rk0, dL, dF, d2)
    # the K_{2,3} collinear stratum, forced
    V, E = NAMED['K23']
    q = {0: (Fr(0), Fr(5)), 1: (Fr(1), Fr(-4)), 2: (Fr(-1), Fr(0)), 3: (Fr(0), Fr(0)), 4: (Fr(2), Fr(0))}
    assert admissible(V, E, q)
    dL = len(L_space(V, E, q))
    rk0 = rank(R_rows(V, E, conf(V, q, [0] * 5)))
    ok = dL == 4 and rk0 == 30 - 3 - 4 and F_dim(V, E, q) == 4
    bad += not ok
    print(f'mc4: {tested} (graph, q) pairs over {len(pops)} graphs, {jumps} at jump strata (dim L > 3 + def2): '
          f'(a), F = L, (b), (MC-5)(i) {"all hold" if not bad else "FAIL"}; K23 collinear stratum dim L = {dL}, '
          f'flat rank {rk0} {"OK" if ok else "FAIL"}')
    return bad


def cycle_basis(V, E):
    idx = {v: i for i, v in enumerate(V)}
    inc = [[Fr(0)] * len(E) for _ in V]
    for ei, (u, w) in enumerate(E):
        inc[idx[u]][ei] += 1        # e = (u, w) leaves u
        inc[idx[w]][ei] -= 1
    return nullspace(inc, len(E))


def beta_mat(V, E, cyc, k, Hs):
    """rows: h in Hs; cols: (cycle c, i) ; entry sum_e c_e det(e_i, k_w, h_u - h_w)."""
    M = []
    for h in Hs:
        row = []
        for c in cyc:
            for i in range(3):
                ei = [Fr(int(t == i)) for t in range(3)]
                s = Fr(0)
                for j, (u, w) in enumerate(E):
                    if c[j]:
                        s += c[j] * det3(ei, k[w], [a - b for a, b in zip(h[u], h[w])])
                row.append(s)
        M.append(row)
    return M


def aug(V, E, P):
    idx = {v: i for i, v in enumerate(V)}
    A = []
    for ei, (u, w) in enumerate(E):
        C = wedge(P[u], P[w])
        for k in range(6):
            r = [Fr(0)] * (6 * len(V) + len(E))
            r[6 * idx[u] + k] += 1
            r[6 * idx[w] + k] -= 1
            r[6 * len(V) + ei] = -C[k]
            A.append(r)
    return A


def t_mc6(n=25):
    """(MC-6): beta symmetric on ALL basis pairs, zero on the three trivial liftings, and
    rank beta(Psi z, .) == exact-Q Schur gain rank(S0^T A1(z) K0) <= rank R(q,z) - rank R(q,0)."""
    rng = random.Random('readerF:mc6')
    bad = 0
    eq_actual = 0
    tot = 0
    pops = [NAMED[k] for k in ('K23', 'C5', 'th223', 'K33', 'prism')] + [rand_graph(rng, 4, 6) for _ in range(n)]
    for (V, E) in pops:
        q = rand_q(rng, V, E, rng.choice([3, 30]))
        L = L_space(V, E, q)
        cf = [rng.randint(-9, 9) for _ in L]
        z = [sum(c * b[j] for c, b in zip(cf, L)) for j in range(len(V))]
        Hs = [interp(V, E, q, b) for b in L]
        k = interp(V, E, q, z)
        cyc = cycle_basis(V, E)
        # symmetry, all pairs
        for i in range(len(Hs)):
            for j in range(i, len(Hs)):
                if beta_mat(V, E, cyc, Hs[i], [Hs[j]]) != beta_mat(V, E, cyc, Hs[j], [Hs[i]]):
                    bad += 1
        for triv in ([Fr(1)] * len(V), [q[v][0] for v in V], [q[v][1] for v in V]):
            t = interp(V, E, q, triv)
            if any(x != 0 for x in beta_mat(V, E, cyc, k, [t])[0]) or any(
                    x != 0 for x in beta_mat(V, E, cyc, t, [k])[0]):
                bad += 1
        rb = rank(beta_mat(V, E, cyc, k, Hs))
        A0 = aug(V, E, conf(V, q, [0] * len(V)))
        A = aug(V, E, conf(V, q, z))
        A1 = [[x - y for x, y in zip(r, s)] for r, s in zip(A, A0)]
        K0 = nullspace(A0, len(A0[0]))
        S0 = nullspace([list(c) for c in zip(*A0)], len(A0))
        A1K = [[sum(A1[i][jj] * kk[jj] for jj in range(len(kk))) for kk in K0] for i in range(len(A1))]
        Sch = [[sum(s[i] * A1K[i][c] for i in range(len(A1))) for c in range(len(K0))] for s in S0]
        gs = rank(Sch)
        actual = rank(R_rows(V, E, conf(V, q, z))) - rank(R_rows(V, E, conf(V, q, [0] * len(V))))
        tot += 1
        if rb != gs or gs > actual:
            bad += 1
            print('  (MC-6) FAILS', V, E, rb, gs, actual)
        eq_actual += gs == actual
    print(f'mc6: {tot} (graph, q, z): beta symmetric on all basis pairs, zero on 1, x, y; rank beta = exact Schur gain '
          f'<= actual gain {"everywhere" if not bad else "FAIL"}; gain = actual at {eq_actual}/{tot}')
    return bad


def add_ear(V, E, a, b, k):
    n = max(V) + 1
    xs = list(range(n, n + k))
    path = [a] + xs + [b]
    E2 = E + [(path[i], path[i + 1]) for i in range(len(path) - 1)]
    return V + xs, E2, xs


HIST17 = {}


def sparse_graph(rng, nmax=7):
    """a cycle plus random ears (open ears of length >= 0 allowed if simple): many degree-2 vertices,
    so def3 > 0 and delta > 0 occur."""
    while True:
        m = rng.randint(3, min(nmax, 7))
        V = list(range(m))
        E = [(i, (i + 1) % m) for i in range(m)]
        for _ in range(rng.randint(0, 2)):
            if len(V) >= nmax:
                break
            a, b = rng.sample(V, 2)
            k = rng.randint(0, nmax - len(V))
            if k == 0 and (frozenset((a, b)) in set(map(frozenset, E))):
                continue
            V, E, _ = add_ear(V, E, a, b, k)
        if satisfies_H(V, E):
            return V, E


def t_mc17(n=400):
    """(MC-17): def3(G' + ear_k) against the formula, brute force."""
    rng = random.Random('readerF:mc17')
    bad = 0
    cnt = 0
    for _ in range(n):
        V, E = sparse_graph(rng, 6) if rng.random() < 0.7 else rand_graph(rng, 4, 5)
        a, b = rng.sample(V, 2)
        closed = rng.random() < 0.3
        if closed:
            b = a
        k = rng.randint(2 if closed else 1, 6)
        V2, E2, xs = add_ear(V, E, a, b, k)
        if len(V2) > 10:
            continue
        f = deficiency(V, E, 6)
        g = deficiency(V, E, 6, together=(a, b)) if not closed else f
        dl = f - g
        want = (f + max(0, k - 5)) if closed else (f + k - 5 if k >= 5 else f - min(dl, 5 - k))
        got = deficiency(V2, E2, 6)
        cnt += 1
        HIST17[(closed, k, dl)] = HIST17.get((closed, k, dl), 0) + 1
        if got != want or not (0 <= dl <= 6):
            bad += 1
            print('  (MC-17) FAILS', V, E, a, b, k, got, want)
    print(f'mc17: {cnt} random (G\', ear) with |V(G)| <= 10: formula {"holds" if not bad else "FAILS"}; '
          f'(closed, k, delta) counts {dict(sorted(HIST17.items()))}')
    return bad


def t_mc16(n=40):
    """(MC-16) at arbitrary configurations (random points, small scale to force degeneracies)
    and at X0 points; and r <= delta where G' attains."""
    rng = random.Random('readerF:mc16')
    bad = 0
    cnt = 0
    degen = 0
    rle = 0
    for it in range(n):
        V, E = rand_graph(rng, 4, 6)
        a, b = rng.sample(V, 2)
        closed = rng.random() < 0.3
        if closed:
            b = a
        k = rng.randint(2 if closed else 1, 6)
        V2, E2, xs = add_ear(V, E, a, b, k)
        for mode in ('arbitrary', 'X0'):
            if mode == 'arbitrary':
                S = rng.choice([1, 2])
                while True:
                    P = {v: [Fr(rng.randint(-S, S)) for _ in range(3)] + [Fr(1)] for v in V2}
                    if all(P[u] != P[w] for u, w in E2):
                        break
            else:
                q = rand_q(rng, V2, E2, 30)
                L = L_space(V2, E2, q)
                cf = [rng.randint(-9, 9) for _ in L]
                z = [sum(c * bb[j] for c, bb in zip(cf, L)) for j in range(len(V2))]
                P = conf(V2, q, z)
            RG = R_rows(V2, E2, P)
            Rp = R_rows(V, E, {v: P[v] for v in V})
            MG = 6 * len(V2) - rank(RG)
            Mp_basis = nullspace(Rp, 6 * len(V))
            idx = {v: i for i, v in enumerate(V)}
            rho = [[X[6 * idx[b] + t] - X[6 * idx[a] + t] for t in range(6)] for X in Mp_basis]
            r = rank(rho)
            path = [a] + xs + [b]
            Lam = [wedge(P[path[i]], P[path[i + 1]]) for i in range(len(path) - 1)]
            lam = rank(Lam)
            degen += lam < min(k + 1, 6)
            Mp = len(Mp_basis)
            if closed:
                want = Mp + (k + 1) - lam
            else:
                want = Mp - r + dim_cap(rho, Lam) + (k + 1) - lam
            cnt += 1
            if MG != want:
                bad += 1
                print('  (MC-16) FAILS', V, E, a, b, k, mode, MG, want)
            if mode == 'X0' and not closed:
                f = deficiency(V, E, 6)
                if Mp == 6 + f:
                    g = deficiency(V, E, 6, together=(a, b))
                    rle += 1
                    if r > f - g:
                        bad += 1
                        print('  r > delta at an attaining G\'', V, E, a, b, r, f - g)
    print(f'mc16: {cnt} configurations ({degen} span-deficient): dimension formula {"holds" if not bad else "FAILS"}; '
          f'r <= delta at {rle} attaining open-ear X0 draws')
    return bad


def t_mc18(n=160):
    """(MC-18): dim L_G(q) = dim L_G'(q') + k - 2 (k >= 2 / closed); k = 1: the q_x-functionals
    z' -> (h_a - h_b)(q_x) span a space of dimension dim U (so dominance iff dim U != 1)."""
    rng = random.Random('readerF:mc18')
    bad = 0
    cnt = 0
    u1 = 0
    tri = 0
    for it in range(n):
        V, E = sparse_graph(rng, 7) if rng.random() < 0.6 else rand_graph(rng, 4, 6)
        a, b = rng.sample(V, 2)
        closed = rng.random() < 0.25
        k = 1 if (not closed and rng.random() < 0.5) else rng.randint(2, 4)
        if closed:
            b = a
        V2, E2, xs = add_ear(V, E, a, b, k)
        q = rand_q(rng, V2, E2, 30)
        qp = {v: q[v] for v in V}
        if not admissible(V, E, qp):
            continue
        Lp = L_space(V, E, qp)
        LG = L_space(V2, E2, q)
        cnt += 1
        if k >= 2:
            if len(LG) != len(Lp) + k - 2:
                bad += 1
                print('  (MC-18)(a) FAILS', V, E, a, b, k)
            continue
        Hs = [interp(V, E, qp, bb) for bb in Lp]
        U = [[x - y for x, y in zip(h[a], h[b])] for h in Hs]
        dU = rank(U)
        # functionals at 6 random q_x
        fun = []
        for _ in range(6):
            qx = [Fr(rng.randint(-50, 50)), Fr(rng.randint(-50, 50)), Fr(1)]
            fun.append([sum(u[t] * qx[t] for t in range(3)) for u in U])
        if rank(fun) != dU:
            bad += 1
        # dim L_G at this q:  dim L_G' - [functional at q_x nonzero]
        x = xs[0]
        qx = [q[x][0], q[x][1], Fr(1)]
        fx = [sum(u[t] * qx[t] for t in range(3)) for u in U]
        if len(LG) != len(Lp) - (1 if any(fx) else 0):
            bad += 1
            print('  (MC-18)(b) dim L FAILS', V, E, a, b)
        u1 += dU == 1
        tri += dU == 1 and (a, b) in [tuple(e) for e in E] + [(w, u) for (u, w) in E]
    # the two named dim U = 1 instances
    V, E = NAMED['C4']        # a = 0, b = 2 opposite
    q = rand_q(rng, V, E, 30)
    Hs = [interp(V, E, q, bb) for bb in L_space(V, E, q)]
    U = [[x - y for x, y in zip(h[0], h[2])] for h in Hs]
    ok = rank(U) == 1
    lcd = cross([q[1][0], q[1][1], Fr(1)], [q[3][0], q[3][1], Fr(1)])
    ok = ok and all(rank([u, lcd]) <= 1 for u in U)
    bad += not ok
    print(f'mc18: {cnt} (G\', ear, q): (a) and (b) {"hold" if not bad else "FAIL"}; dim U = 1 seen {u1} times '
          f'({tri} adjacent); C4 opposite pair: U = K l_cd {"OK" if ok else "FAIL"}')
    return bad


# ------------------------------------------------------------------ flag frames

def e(i):
    return [Fr(int(t == i)) for t in range(4)]


def vadd(*vs):
    return [sum(c) for c in zip(*vs)]


CANON = {  # p_a, spanning vectors of pi_a, p_b, spanning vectors of pi_b
    'i':   (e(0), [e(0), e(1), e(2)], e(3), [e(1), e(2), e(3)]),
    'ii':  (e(0), [e(0), e(2), e(3)], e(3), [e(1), e(2), e(3)]),      # p_b in pi_a
    "ii'": (e(0), [e(0), e(1), e(2)], e(3), [e(0), e(1), e(3)]),      # p_a in pi_b
    'iii': (e(0), [e(0), e(1), e(3)], e(3), [e(0), e(2), e(3)]),
    'iv':  (e(0), [e(0), e(1), e(3)], e(3), [e(0), e(1), e(3)]),
}


def rand_T(rng):
    while True:
        T = [[Fr(rng.randint(-3, 3)) for _ in range(4)] for _ in range(4)]
        if rank(T) == 4:
            return T


def app(T, v):
    return [sum(T[i][j] * v[j] for j in range(4)) for i in range(4)]


def frame(name, T):
    pa, A, pb, B = CANON[name]
    return app(T, pa), [app(T, v) for v in A], app(T, pb), [app(T, v) for v in B]


def orbit_of(pa, A, pb, B):
    """classify a flag pair from its data, as a check of the frames"""
    in_b = rank(B + [pa]) == 3        # p_a in pi_b
    in_a = rank(A + [pb]) == 3        # p_b in pi_a
    same = rank(A + B) == 3
    if same:
        return 'iv'
    if in_a and in_b:
        return 'iii'
    if in_a:
        return 'ii'
    if in_b:
        return "ii'"
    return 'i'


def rand_in(rng, span, S=9):
    return vadd(*[[c * x for x in v] for c, v in zip([Fr(rng.randint(-S, S)) for _ in span], span)])


def meet_basis(A, B):
    """basis of span A cap span B in K^4"""
    # x = sum a_i A_i = sum b_j B_j
    M = [[A[i][t] for i in range(len(A))] + [-B[j][t] for j in range(len(B))] for t in range(4)]
    out = []
    for s in nullspace(M, len(A) + len(B)):
        out.append(vadd(*[[s[i] * x for x in A[i]] for i in range(len(A))]))
    R, _ = rref(out)
    return R


def placement(rng, fr, k, closed=False):
    pa, A, pb, B = fr
    if closed:
        pts = [pa, rand_in(rng, A)] + [[Fr(rng.randint(-9, 9)) for _ in range(4)] for _ in range(k - 2)] + [rand_in(rng, A), pa]
        return pts
    if k == 1:
        return [pa, rand_in(rng, meet_basis(A, B)), pb]
    return [pa, rand_in(rng, A)] + [[Fr(rng.randint(-9, 9)) for _ in range(4)] for _ in range(k - 2)] + [rand_in(rng, B), pb]


def lines_of(pts):
    return [wedge(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def t_mc19():
    """(MC-19): generic spans per orbit, k = 1..8 open, k = 2..8 closed, polygons n = 3..9;
    each certified by a draw at the trivial maximum (max over 8 draws)."""
    rng = random.Random('readerF:mc19')
    bad = 0
    rows = []
    for name in CANON:
        T = rand_T(rng)
        fr = frame(name, T)
        assert orbit_of(*fr) == name, (name, orbit_of(*fr))
        for k in range(1, 9):
            best = max(rank(lines_of(placement(rng, fr, k))) for _ in range(8))
            want = 1 if (k == 1 and name == 'iii') else min(k + 1, 6)
            if k == 1 and name == 'iii':
                # every placement: both lines equal m, so lambda = 1 exactly (hand); check 8 draws
                allone = all(rank(lines_of(placement(rng, fr, 1))) == 1 for _ in range(8))
                bad += not allone
            bad += best != want
            rows.append((name, k, best, want))
        for k in range(2, 9):
            best = max(rank(lines_of(placement(rng, fr, k, closed=True))) for _ in range(8))
            bad += best != min(k + 1, 6)
    for nn in range(3, 10):
        best = 0
        for _ in range(8):
            pts = [[Fr(rng.randint(-9, 9)) for _ in range(4)] for _ in range(nn)]
            best = max(best, rank(lines_of(pts + [pts[0]])))
        bad += best != min(nn, 6)
    print(f'mc19: open ears k = 1..8 in orbits i, ii, ii\', iii, iv; closed ears k = 2..8; polygons n = 3..9: '
          f'{"every generic span as claimed" if not bad else "FAIL %d" % bad}')
    return bad


def t_caps(T=30):
    """cap_k = intersection of Lambda over span-generic placements, per orbit, k = 1..4, closed k = 2..4.
    Then the hand values for the nonzero cells are checked as lower bounds (contained in every Lambda)."""
    rng = random.Random('readerF:caps')
    bad = 0
    table = {}
    for name in CANON:
        Tm = rand_T(rng)
        fr = frame(name, Tm)
        pa, A, pb, B = fr
        for k in range(1, 5):
            lam0 = 1 if (k == 1 and name == 'iii') else k + 1
            perps = []
            got = rej = 0
            spans = []
            while got < T:
                Lm = lines_of(placement(rng, fr, k))
                if rank(Lm) != lam0:
                    rej += 1
                    continue
                got += 1
                spans.append(Lm)
                perps += nullspace(Lm, 6)
            cap = nullspace(perps, 6)
            table[(name, k)] = (len(cap), rej)
        # hand lower bounds
        m = meet_basis(A, B) if rank(A + B) == 4 else None
        hand = {}
        if name in ('ii', "ii'", 'iii'):
            hand[1] = [wedge(m[0], m[1])]
        if name == 'iv':
            hand[2] = [wedge(A[0], A[1]), wedge(A[0], A[2]), wedge(A[1], A[2])]
        for kk, H in hand.items():
            lamk = 1 if (kk == 1 and name == 'iii') else kk + 1
            seen = 0
            while seen < 10:
                Lm = lines_of(placement(rng, fr, kk))
                if rank(Lm) != lamk:          # the hand claim is about span-generic placements
                    continue
                seen += 1
                if dim_cap(H, Lm) != len(H):
                    bad += 1
            if table[(name, kk)][0] != len(H):
                bad += 1
        for kk in range(1, 5):
            if kk not in hand and table[(name, kk)][0] != 0:
                bad += 1
    for name in CANON:
        print(f'caps {name:<4} ' + '; '.join(f'k={k}: dim cap {table[(name, k)][0]} ({table[(name, k)][1]} rejected)'
                                           for k in range(1, 5)))
    print(f'caps: nonzero exactly at (ii) and (ii\') k=1 [<m>], (iii) k=1 [<m>], (iv) k=2 [Lambda^2 pi]; '
          f'hand subspaces lie in every Lambda: {"OK" if not bad else "FAIL %d" % bad}')
    return bad


def gen_dim(rng, fr, k, rho, lam0, draws=6):
    """generic dim(rho cap Lambda_k) certified if it reaches the lower bound; else the min seen."""
    best = None
    for _ in range(draws * 3):
        Lm = lines_of(placement(rng, fr, k))
        if rank(Lm) != lam0:
            continue
        d = dim_cap(rho, Lm)
        best = d if best is None else min(best, d)
        if best == max(0, rank(rho) + lam0 - 6):
            break
    return best


def structured_rho(rng, fr):
    pa, A, pb, B = fr
    # Pen(p_a, pi_a): lines through p_a in pi_a
    pena = [wedge(pa, v) for v in A if rank([pa, v]) == 2]
    penb = [wedge(pb, v) for v in B if rank([pb, v]) == 2]
    stara = [wedge(pa, e(i)) for i in range(4) if rank([pa, e(i)]) == 2]
    starb = [wedge(pb, e(i)) for i in range(4) if rank([pb, e(i)]) == 2]
    planea = [wedge(A[i], A[j]) for i in range(3) for j in range(i + 1, 3)]
    planeb = [wedge(B[i], B[j]) for i in range(3) for j in range(i + 1, 3)]
    nline = [wedge(pa, pb)]
    fams = [pena, penb, stara, starb, planea, planeb, nline]
    if rank(A + B) == 4:
        m = meet_basis(A, B)
        fams.append([wedge(m[0], m[1])])
    rnd = [[Fr(rng.randint(-5, 5)) for _ in range(6)] for _ in range(3)]
    fams.append(rnd)
    rho = []
    for fam in rng.sample(fams, rng.randint(1, 3)):
        if fam:
            rho += rng.sample(fam, rng.randint(1, len(fam)))
    if rng.random() < 0.5:
        rho += [[Fr(rng.randint(-5, 5)) for _ in range(6)]]
    R, _ = rref(rho)
    return R


IIIL = [0, 0]


def t_links(n=1500):
    """(MC-26): (P1) => (P2) at r >= 4 and (P2) => (P3) at r >= 3, on structured rho, orbits with
    lambda_1 = 2 (i, ii, ii', iv) for the first link, all orbits for the second."""
    rng = random.Random('readerF:links')
    bad = 0
    n12 = n23 = 0
    frames = {name: frame(name, rand_T(rng)) for name in CANON}
    for it in range(n):
        name = rng.choice(list(CANON))
        fr = frames[name]
        rho = structured_rho(rng, fr)
        r = len(rho)
        if r == 0:
            continue
        g = {}
        for k in (1, 2, 3):
            lam0 = 1 if (k == 1 and name == 'iii') else k + 1
            g[k] = gen_dim(rng, fr, k, rho, lam0)
        P = {k: g[k] == max(0, r + k - 5) for k in (1, 2, 3)}
        if name == 'iii' and r >= 4 and P[1]:
            IIIL[0] += 1
            IIIL[1] += not P[2]
        if name != 'iii' and r >= 4 and P[1]:
            n12 += 1
            if not P[2]:
                bad += 1
                print('  link 1->2 FAILS?', name, r, g)
        if r >= 3 and P[2]:
            n23 += 1
            if not P[3]:
                bad += 1
                print('  link 2->3 FAILS?', name, r, g)
    print(f'links: (P1)=>(P2) tested at {n12} structured (orbit, rho) with r >= 4, (P2)=>(P3) at {n23} with r >= 3: '
          f'{"no violation" if not bad else "VIOLATIONS %d" % bad}; outside scope, orbit (iii) first link: '
          f'{IIIL[0]} tested, {IIIL[1]} with (P1) but not (P2)')
    return bad


def t_crit(n=500):
    """(MC-27)'s exact k = 1 criterion in orbit (i), against the generic value of dim(rho cap Lambda_1)."""
    rng = random.Random('readerF:crit')
    fr = frame('i', rand_T(rng))
    pa, A, pb, B = fr
    m = meet_basis(A, B)
    nn = [pa, pb]
    W4 = [wedge(x, y) for x in m for y in nn]
    assert rank(W4) == 4
    bad = 0
    stats = {}
    for it in range(n):
        # rho: random subspace biased towards W4 and its rulings
        pieces = []
        c = rng.random()
        if c < 0.3:
            y0 = [Fr(rng.randint(-3, 3)) * a + Fr(rng.randint(-3, 3)) * b for a, b in zip(pa, pb)]
            if any(y0):
                pieces += [wedge(m[0], y0), wedge(m[1], y0)]
        elif c < 0.6:
            pieces += rng.sample(W4, rng.randint(1, 4))
        elif c < 0.8:
            x0 = [Fr(rng.randint(-3, 3)) * a + Fr(rng.randint(-3, 3)) * b for a, b in zip(m[0], m[1])]
            if any(x0):
                pieces += [wedge(x0, pa), wedge(x0, pb)]
        for _ in range(rng.randint(0, 3)):
            if rng.random() < 0.5:
                pieces.append([sum(Fr(rng.randint(-2, 2)) * w[t] for w in W4) for t in range(6)])
            else:
                pieces.append([Fr(rng.randint(-3, 3)) for _ in range(6)])
        if not pieces:
            continue
        rho, _ = rref(pieces)
        r = len(rho)
        if r == 6 or r == 0:
            continue
        gd = gen_dim(rng, fr, 1, rho, 2, draws=10)
        fails = gd != max(0, r - 4)
        rho4 = dim_cap(rho, W4)
        # rho contains m^ (x) y0 for some y0 in n ?
        # solve s,t: m_i ^ (s pa + t pb) in rho for i = 0, 1
        comp = nullspace(rho, 6)          # rho^perp (dot); v in rho iff v . c = 0 for all c in comp
        Mx = []
        for mi in m:
            for cvec in comp:
                Mx.append([sum(a * b for a, b in zip(wedge(mi, pa), cvec)),
                           sum(a * b for a, b in zip(wedge(mi, pb), cvec))])
        ruled = (rank(Mx) < 2) if Mx else True
        crit = (r <= 4 and (rho4 >= 3 or ruled)) or (r == 5 and rho4 == 4)
        key = (r, crit, fails)
        stats[key] = stats.get(key, 0) + 1
        if crit != fails:
            bad += 1
            print('  criterion disagrees', r, rho4, ruled, gd)
    print(f'crit: (MC-27) k = 1 orbit (i) criterion vs generic value at {sum(stats.values())} structured rho: '
          f'{"agree everywhere" if not bad else "DISAGREE %d" % bad}; (r, crit, fails) counts {dict(sorted(stats.items()))}')
    return bad


def t_mc17d(n=45):
    """(MC-17) where delta > 0 can occur: sparse G' on 7-8 vertices (def3(G') >= 1), open ears k = 1..3."""
    rng = random.Random('readerF:mc17d')
    bad = 0
    hist = {}
    cnt = 0
    while cnt < n:
        V, E = sparse_graph(rng, 8)
        if len(V) < 7:
            continue
        f = deficiency(V, E, 6)
        if f == 0:
            continue
        a, b = rng.sample(V, 2)
        k = rng.randint(1, 10 - len(V))
        V2, E2, xs = add_ear(V, E, a, b, k)
        g = deficiency(V, E, 6, together=(a, b))
        dl = f - g
        want = f + k - 5 if k >= 5 else f - min(dl, 5 - k)
        got = deficiency(V2, E2, 6)
        cnt += 1
        hist[(k, dl)] = hist.get((k, dl), 0) + 1
        if got != want:
            bad += 1
            print('  (MC-17) FAILS', V, E, a, b, k, got, want)
    print(f'mc17d: {cnt} (G\' sparse, def3(G\') >= 1, open ear k <= 3): formula {"holds" if not bad else "FAILS"}; '
          f'(k, delta) counts {dict(sorted(hist.items()))}')
    return bad


def t_dp(n=120):
    rng = random.Random('readerF:dp')
    bad = 0
    for _ in range(n):
        V, E = sparse_graph(rng, 7) if rng.random() < 0.6 else rand_graph(rng, 4, 7)
        a, b = rng.sample(V, 2)
        for D in (3, 6):
            if deficiency(V, E, D) != deficiency_dp(V, E, D):
                bad += 1
            if deficiency(V, E, D, (a, b)) != deficiency_dp(V, E, D, (a, b)):
                bad += 1
    print(f'dp: subset-DP deficiency = brute force (D = 3, 6; free and a~b-together) at {n} graphs: {"OK" if not bad else "FAIL %d" % bad}')
    return bad


def t_mc17e(n=150):
    """(MC-17) with larger delta: sparse G' on 7..10 vertices, open ears k = 1..6, closed k = 2..6, |V(G)| <= 13 (subset DP)."""
    rng = random.Random('readerF:mc17e')
    bad = 0
    hist = {}
    cnt = 0
    while cnt < n:
        V, E = sparse_graph(rng, 10)
        if len(V) < 7:
            continue
        f = deficiency_dp(V, E, 6)
        closed = rng.random() < 0.2
        a, b = rng.sample(V, 2)
        if closed:
            b = a
        k = rng.randint(2 if closed else 1, min(6, 13 - len(V)))
        V2, E2, xs = add_ear(V, E, a, b, k)
        g = f if closed else deficiency_dp(V, E, 6, together=(a, b))
        dl = f - g
        want = (f + max(0, k - 5)) if closed else (f + k - 5 if k >= 5 else f - min(dl, 5 - k))
        got = deficiency_dp(V2, E2, 6)
        cnt += 1
        hist[(closed, k, dl)] = hist.get((closed, k, dl), 0) + 1
        if got != want:
            bad += 1
            print('  (MC-17) FAILS', V, E, a, b, k, got, want)
    print(f'mc17e: {cnt} (G\' sparse on 7..10 vertices, ear): formula {"holds" if not bad else "FAILS"}; '
          f'(closed, k, delta) counts {dict(sorted(hist.items()))}')
    return bad


def t_mc17c():
    """(MC-17) at G' = C_n, n = 7..11, every pair a, b (up to rotation), open ears k = 1..(13 - n), and theta-like G'."""
    bad = 0
    hist = {}
    cnt = 0
    for n in range(7, 12):
        V = list(range(n))
        E = [(i, (i + 1) % n) for i in range(n)]
        f = deficiency_dp(V, E, 6)
        for bb in range(1, n // 2 + 1):
            a, b = 0, bb
            g = deficiency_dp(V, E, 6, together=(a, b))
            dl = f - g
            for k in range(1, 14 - n):
                V2, E2, xs = add_ear(V, E, a, b, k)
                want = f + k - 5 if k >= 5 else f - min(dl, 5 - k)
                got = deficiency_dp(V2, E2, 6)
                cnt += 1
                hist[(k, dl)] = hist.get((k, dl), 0) + 1
                if got != want:
                    bad += 1
                    print('  (MC-17) FAILS at C_%d' % n, a, b, k, got, want)
    print(f'mc17c: {cnt} (C_n, pair, open ear): formula {"holds" if not bad else "FAILS"}; (k, delta) counts {dict(sorted(hist.items()))}')
    return bad


TESTS = {'mc3': t_mc3, 'mc4': t_mc4, 'mc6': t_mc6, 'mc16': t_mc16, 'mc17': t_mc17, 'mc17d': t_mc17d, 'dp': t_dp, 'mc17e': t_mc17e, 'mc17c': t_mc17c,
         'mc18': t_mc18, 'mc19': t_mc19, 'caps': t_caps, 'links': t_links, 'crit': t_crit}


def main():
    which = sys.argv[1:] or ['all']
    bad = 0
    for name, fn in TESTS.items():
        if 'all' in which or name in which:
            bad += fn()
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
