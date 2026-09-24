"""zcore.py -- §(K-main) Step MC19 (Track E) shared core: the hub-plane chart Z(G) of pencil configurations.

A pencil configuration with adjacent points distinct is (hub normals n_h, points p_v) in K^4 with
p_v . n_h = 0 whenever h is a hub in N[v]  (h in closedHubNbhd v); non-hub normals are any nonzero
vector orthogonal to the <= 3 points of N[v] (always exists).  The rank depends on the points only
(hinge line p_u ^ p_w).

Exact arithmetic: integers / Fractions; ranks mod P61 = 2^61 - 1 are LOWER bounds for the Q-rank of
an integer matrix, and the Q-rank is <= 6(|V|-1) - def3, so rank_p == target is a certificate.
"""
import os
import sys
from fractions import Fraction as F
from math import lcm, gcd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
import scriptpath  # noqa: F401,E402

from exactcore import rank as rank_q, nullspace, wedge2, neighbors  # noqa: E402
from kbare_common import rank_modp, verts_of  # noqa: E402
from nogood_subdiv import deficiency as def3  # noqa: E402
from maincomp import def_k  # noqa: E402


def def2(edges, verts=None):
    return def_k(edges, 3, verts)


def target(edges):
    V = verts_of(edges)
    return 6 * (len(V) - 1) - def3(edges)


def hubs_of(edges):
    nb = neighbors(edges)
    return {v for v in nb if len(nb[v]) >= 3}


def chn(edges):
    """closedHubNbhd v for every v (hubs among N[v])."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    return {v: sorted([w for w in set(nb[v]) | {v} if w in H], key=str) for v in nb}


def F1(edges):
    return all(len(s) <= 3 for s in chn(edges).values())


def triangles(edges):
    nb = neighbors(edges)
    out = set()
    for u, w in edges:
        for x in set(nb[u]) & set(nb[w]):
            out.add(frozenset((u, w, x)))
    return out


def F2(edges):
    H = hubs_of(edges)
    return all(len(t & H) <= 1 for t in triangles(edges))


def intvec(v):
    m = lcm(*[F(x).denominator for x in v])
    w = [int(F(x) * m) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    return [x // g for x in w] if g else w


def perp_rows(C):
    """integer basis of C^perp in Z^6 (5 vectors), C integer and nonzero."""
    k = next(i for i in range(6) if C[i] != 0)
    out = []
    for j in range(6):
        if j == k:
            continue
        r = [0] * 6
        r[j] = C[k]
        r[k] = -C[j]
        out.append(r)
    return out


def rigidity_rows(edges, pt):
    V = verts_of(edges)
    idx = {v: i for i, v in enumerate(V)}
    rows = []
    for (u, w) in edges:
        C = wedge2(pt[u], pt[w])
        assert any(C), ('coincident adjacent points', u, w)
        for r in perp_rows(C):
            row = [0] * (6 * len(V))
            for k in range(6):
                row[6 * idx[u] + k] += r[k]
                row[6 * idx[w] + k] -= r[k]
            rows.append(row)
    return rows


def rank_p(edges, pt):
    return rank_modp(rigidity_rows(edges, pt))


def rank_exact(edges, pt):
    return rank_q([[F(x) for x in r] for r in rigidity_rows(edges, pt)])


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def nondeg(edges, normal, pt):
    """All four conjuncts of IsNondegPencilRealization, with EXPLICIT normals (hub and non-hub).
    Returns (True, None) or (False, reason)."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    C = chn(edges)
    for v in nb:
        if not any(pt[v]) or not any(normal[v]):
            return False, ('zero', v)
        for w in list(nb[v]) + [v]:
            if dot(pt[w], normal[v]) != 0:
                return False, ('incidence', v, w)
    for (u, w) in edges:
        if rank_q([[F(x) for x in pt[u]], [F(x) for x in pt[w]]]) != 2:
            return False, ('conjunct 2', (u, w))
    for v in nb:
        S = C[v]
        if S and rank_q([[F(x) for x in normal[w]] for w in S]) != len(S):
            return False, ('conjunct 3', v, S)
    for v in nb:
        if v not in H:
            S = [v] + list(nb[v])
            if rank_q([[F(x) for x in pt[w]] for w in S]) != len(S):
                return False, ('conjunct 4', v)
    return True, None


def complete_normals(edges, hubnormal, pt):
    """non-hub normals: an integer vector orthogonal to the points of N[v]."""
    nb = neighbors(edges)
    H = hubs_of(edges)
    normal = dict(hubnormal)
    for v in nb:
        if v in H:
            continue
        ns = nullspace([[F(x) for x in pt[w]] for w in [v] + list(nb[v])])
        assert ns
        normal[v] = intvec(ns[0])
    return normal


def zdraw(edges, rng, S=30, tries=200):
    """One point of the hub-plane chart: random integer hub normals (redrawn until conjunct 3
    holds), each point a random integer combination of a basis of its flat
    F_v = cap_{h in chn(v)} n_h^perp.  Returns (normal, pt) or None."""
    nb = neighbors(edges)
    H = sorted(hubs_of(edges), key=str)
    C = chn(edges)
    for _ in range(tries):
        n = {h: [rng.randint(-S, S) for _ in range(4)] for h in H}
        if any(C[v] and rank_q([[F(x) for x in n[w]] for w in C[v]]) != len(C[v]) for v in nb):
            continue
        pt = {}
        for v in nb:
            if C[v]:
                B = nullspace([[F(x) for x in n[w]] for w in C[v]])
            else:
                B = [[F(int(i == j)) for j in range(4)] for i in range(4)]
            c = [rng.randint(-S, S) for _ in B]
            pt[v] = intvec([sum(ci * b[k] for ci, b in zip(c, B)) for k in range(4)])
        if any(not any(pt[v]) for v in nb):
            continue
        return n, pt
    return None
