#!/usr/bin/env python3
"""Phase 43a, the flatness reading (N6): read-only probe, exact Fraction arithmetic.

Population: every connected simple graph with minimum degree >= 2 on n bodies
(`geng -c -d2 -q n`), for the n given on the command line; plus named witnesses.

At one seeded random integer picture q per graph (resampled until admissible and
JJ-general, i.e. dim L(q) = 3 + def2(G)), the probe computes a basis of the
solutions (z, h) of the lifting system M(q) and checks:

 (A) JJ:   dim L(q) = 3 + def2(G).
 (F) flat: for every planar-rigid W (|W| >= 2, def2(G[W]) = 0), h_v is the same
           affine function at every v in W, for every basis solution
           (so every z in L(q) is affine on W and all of W has one plane).
 (C) classes: for u != v, [h_u = h_v on all of L(q)] iff [u, v lie in a common
           planar-rigid set].
 (D) degenerate: at a random z in L(q), the configuration (normals ~ (a, b, -1, c)
           from h_v, points (x, y, z, 1)) fails a condition of
           IsNondegPencilRealization whenever some planar-rigid W holds two
           members of one closed hub-neighbourhood ("bad pair").
 (K) count: a planar-rigid W with no bad pair is G = triangle, or one hub with
           pendant triangles (its other bodies of degree two in G).

Written by the flatness reader of 2026-11-07 (`notes/Phase43a.md`, its item); banked in Phase
43a with this paragraph, otherwise as run. Invocations: `notes/scripts/README.md` section 3,
`natural/`.
"""
import random
import subprocess
import sys
from fractions import Fraction as Fr
from itertools import combinations

# ---------------------------------------------------------------- linear algebra


def rref(rows, ncols):
    """Reduced row echelon form over Q; returns (rows, pivot columns)."""
    m = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(m)):
            if m[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        inv = 1 / m[r][c]
        m[r] = [x * inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
        if r == len(m):
            break
    return m[:r], piv


def nullspace(rows, ncols):
    red, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * ncols
        v[f] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -red[i][f]
        basis.append(v)
    return basis


def rank(rows):
    if not rows:
        return 0
    return len(rref(rows, len(rows[0]))[1])


def det(m):
    n = len(m)
    m = [list(map(Fr, r)) for r in m]
    d = Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if m[i][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for i in range(c + 1, n):
            f = m[i][c] / m[c][c]
            m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return d


def cross4(y1, y2, y3):
    """n with n . t = det[y1, y2, y3, t]."""
    out = []
    for i in range(4):
        e = [0] * 4
        e[i] = 1
        out.append(det([y1, y2, y3, e]))
    return out


# ---------------------------------------------------------------- graphs


def decode_g6(s):
    s = s.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - k)) & 1 for k in range(6))
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return n, adj


def edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def deficiency_table(n, adj, D):
    """def_D(G[S]) for every nonempty bitmask S, by a DP over partitions:
    max_P sum_i g(P_i) with g(X) = D + (D-1) e(X); def = F(S) - (D-1) e(S) - D."""
    N = 1 << n
    nbmask = [sum(1 << w for w in adj[v]) for v in range(n)]
    e = [0] * N
    for S in range(1, N):
        low = (S & -S).bit_length() - 1
        rest = S & ~(1 << low)
        e[S] = e[rest] + bin(nbmask[low] & rest).count("1")
    g = [D + (D - 1) * e[S] for S in range(N)]
    F = [0] * N
    for S in range(1, N):
        lowbit = S & -S
        rest = S ^ lowbit
        best = None
        sub = rest
        while True:
            X = sub | lowbit
            val = g[X] + F[S ^ X]
            if best is None or val > best:
                best = val
            if sub == 0:
                break
            sub = (sub - 1) & rest
        F[S] = best
    return [None] + [F[S] - (D - 1) * e[S] - D for S in range(1, N)]


def closed_nbhd(adj, v):
    return {v} | adj[v]


def is_hub(adj, v):
    return len(adj[v]) >= 3


def closed_hub_nbhd(adj, v):
    return {w for w in closed_nbhd(adj, v) if is_hub(adj, w)}


# ---------------------------------------------------------------- pictures


def admissible(n, adj, q):
    for u, v in edges_of(n, adj):
        if q[u] == q[v]:
            return False
    for v in range(n):
        N = sorted(closed_nbhd(adj, v))
        if not any(det([[q[a][0], q[a][1], 1], [q[b][0], q[b][1], 1], [q[c][0], q[c][1], 1]]) != 0
                   for a, b, c in combinations(N, 3)):
            return False
    return True


def lifting_solutions(n, adj, q):
    """Basis of solutions (z, h) of M(q): unknowns z_0..z_{n-1}, h_v (3 each)."""
    ncols = 4 * n
    rows = []
    for v in range(n):
        for w in closed_nbhd(adj, v):
            r = [Fr(0)] * ncols
            r[w] += 1
            r[n + 3 * v + 0] -= q[w][0]
            r[n + 3 * v + 1] -= q[w][1]
            r[n + 3 * v + 2] -= 1
            rows.append(r)
    return nullspace(rows, ncols)


def h_of(sol, n, v):
    return tuple(sol[n + 3 * v: n + 3 * v + 3])


def nondegenerate(n, adj, q, sol):
    """IsNondegPencilRealization's conditions at the configuration of `sol`.
    Returns the list of failed condition names (empty = nondegenerate)."""
    z = sol[:n]
    pts = [[Fr(q[v][0]), Fr(q[v][1]), z[v], Fr(1)] for v in range(n)]
    nor = []
    for v in range(n):
        a, b, c = h_of(sol, n, v)
        nor.append([a, b, Fr(-1), c])
    fails = []
    # pencil realization: four incidences at each edge (automatic, checked anyway)
    for u, v in edges_of(n, adj):
        for P, Nv in ((pts[u], nor[u]), (pts[u], nor[v]), (pts[v], nor[u]), (pts[v], nor[v])):
            if sum(x * y for x, y in zip(P, Nv)) != 0:
                fails.append("incidence")
        if rank([pts[u], pts[v]]) < 2:
            fails.append("adjacent")
    for v in range(n):
        S = sorted(closed_hub_nbhd(adj, v))
        if S and rank([nor[w] for w in S]) < len(S):
            fails.append("hubnormals")
        if not is_hub(adj, v):
            N = sorted(closed_nbhd(adj, v))
            if rank([pts[w] for w in N]) < len(N):
                fails.append("nonhubpoints")
    return sorted(set(fails))


def config_rank(n, adj, q, z):
    """Rank of the body-hinge framework with hinges p_u v p_v (Pluecker), = rank of (q, z)."""
    pts = [[Fr(q[v][0]), Fr(q[v][1]), z[v], Fr(1)] for v in range(n)]
    E = edges_of(n, adj)
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    m = len(E)
    ncols = 6 * n + m
    rows = []
    for k, (u, v) in enumerate(E):
        a, b = pts[u], pts[v]
        L = [a[i] * b[j] - a[j] * b[i] for i, j in pairs]
        for c in range(6):
            r = [Fr(0)] * ncols
            r[6 * u + c] += 1
            r[6 * v + c] -= 1
            r[6 * n + k] -= L[c]
            rows.append(r)
    nullity = ncols - rank(rows)
    return 6 * n - nullity


# ---------------------------------------------------------------- the checks


def analyse(n, adj, rng, label, want_rank=False):
    full = (1 << n) - 1
    d2 = deficiency_table(n, adj, 3)
    rigid = [S for S in range(1, full + 1) if bin(S).count("1") >= 2 and d2[S] == 0]
    tries = 0
    while True:
        tries += 1
        q = [(rng.randint(-60, 60), rng.randint(-60, 60)) for _ in range(n)]
        if not admissible(n, adj, q):
            continue
        sols = lifting_solutions(n, adj, q)
        if len(sols) == 3 + d2[full]:
            break
        if tries > 50:
            raise RuntimeError("no JJ-general picture found for " + label)
    res = {"label": label, "n": n, "def2": d2[full], "dimL": len(sols), "tries": tries}
    # (F) flatness
    flat_ok = True
    for S in rigid:
        W = [v for v in range(n) if S >> v & 1]
        for sol in sols:
            hs = {h_of(sol, n, v) for v in W}
            if len(hs) != 1:
                flat_ok = False
    res["flat"] = flat_ok
    res["nrigid"] = len(rigid)
    # (C) classes
    cls_ok = True
    for u, v in combinations(range(n), 2):
        same = all(h_of(s, n, u) == h_of(s, n, v) for s in sols)
        common = any((S >> u & 1) and (S >> v & 1) for S in rigid)
        if same != common:
            cls_ok = False
    res["classes"] = cls_ok
    # (D) degeneracy at a random height
    coeffs = [rng.randint(-40, 40) for _ in sols]
    sol = [sum(Fr(c) * s[i] for c, s in zip(coeffs, sols)) for i in range(4 * n)]
    fails = nondegenerate(n, adj, q, sol)
    res["fails"] = fails
    bad = False
    for S in rigid:
        for v in range(n):
            if len([w for w in closed_hub_nbhd(adj, v) if S >> w & 1]) >= 2:
                bad = True
    res["bad"] = bad
    res["hubnbhd_gt3"] = any(len(closed_hub_nbhd(adj, v)) > 3 for v in range(n))
    # (K) the count: planar-rigid W without a bad pair
    k_ok = True
    for S in rigid:
        W = {v for v in range(n) if S >> v & 1}
        if any(len(closed_hub_nbhd(adj, v) & W) >= 2 for v in range(n)):
            continue
        hubs = [v for v in W if is_hub(adj, v)]
        if not hubs:
            ok = (n == 3 and len(W) == 3)
        elif len(hubs) == 1:
            r = hubs[0]
            ok = all((not is_hub(adj, w)) and r in adj[w]
                     and len(adj[w] - {r}) == 1 and (adj[w] - {r}) <= W
                     for w in W - {r})
        else:
            ok = False
        if not ok:
            k_ok = False
    res["count"] = k_ok
    if want_rank:
        d3 = deficiency_table(n, adj, 6)
        res["rank"] = config_rank(n, adj, q, sol[:n])
        res["target"] = 6 * (n - 1) - d3[full]
        # dimension d = 4: two heights, the planes Pi_v
        c2 = [rng.randint(-40, 40) for _ in sols]
        z2 = [sum(Fr(c) * s[i] for c, s in zip(c2, sols)) for i in range(n)]
        b = [[Fr(q[v][0]), Fr(q[v][1]), sol[v], z2[v], Fr(1)] for v in range(n)]
        pis_ok = all(rank([b[w] for w in closed_nbhd(adj, v)]) == 3 for v in range(n))
        flat4 = all(rank([b[w] for w in range(n) if S >> w & 1]) == 3 for S in rigid)
        res["d4_planes_dim3"] = pis_ok
        res["d4_flat"] = flat4
    return res


def doubled_triangle_feasible(rng):
    """An explicit nondegenerate pencil realization of the doubled triangle."""
    # hubs a=0, b=1, c=2; x1=3, x2=4 (a-b); y1=5, y2=6 (b-c); z1=7, z2=8 (c-a)
    edges = [(0, 3), (3, 1), (0, 4), (4, 1), (1, 5), (5, 2), (1, 6), (6, 2), (2, 7), (7, 0), (2, 8), (8, 0)]
    n, adj = from_edges(9, edges)
    R = lambda: [Fr(rng.randint(-30, 30)) for _ in range(4)]
    nor = [None] * 9
    pts = [None] * 9
    for h in range(3):
        nor[h] = R()
    for h in range(3):
        B = nullspace([nor[h]], 4)
        cf = [Fr(rng.randint(-30, 30)) for _ in range(3)]
        pts[h] = [sum(cf[k] * B[k][i] for k in range(3)) for i in range(4)]
    for (h1, h2), mids in (((0, 1), (3, 4)), ((1, 2), (5, 6)), ((2, 0), (7, 8))):
        B = nullspace([nor[h1], nor[h2]], 4)
        for t, x in enumerate(mids):
            pts[x] = [B[0][i] + (t + 1) * B[1][i] for i in range(4)]
            nor[x] = cross4(pts[x], pts[h1], pts[h2])
    fails = []
    for u, v in edges_of(n, adj):
        for P, Nv in ((pts[u], nor[u]), (pts[u], nor[v]), (pts[v], nor[u]), (pts[v], nor[v])):
            if sum(x * y for x, y in zip(P, Nv)) != 0:
                fails.append("incidence")
        if rank([pts[u], pts[v]]) < 2:
            fails.append("adjacent")
    for v in range(n):
        if all(x == 0 for x in nor[v]) or all(x == 0 for x in pts[v]):
            fails.append("zero")
        S = sorted(closed_hub_nbhd(adj, v))
        if S and rank([nor[w] for w in S]) < len(S):
            fails.append("hubnormals")
        if not is_hub(adj, v):
            N = sorted(closed_nbhd(adj, v))
            if rank([pts[w] for w in N]) < len(N):
                fails.append("nonhubpoints")
    return sorted(set(fails))


WITNESSES = {
    "K23": (5, [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]),
    "doubled_triangle": (9, [(0, 3), (3, 1), (0, 4), (4, 1), (1, 5), (5, 2), (1, 6), (6, 2),
                             (2, 7), (7, 0), (2, 8), (8, 0)]),
    "bowtie": (5, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]),
    "triangle": (3, [(0, 1), (1, 2), (2, 0)]),
    "C5_pendant_triangle": (7, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 0)]),
}


def main():
    rng = random.Random(43)
    if sys.argv[1:] == ["witnesses"]:
        for name, (n, E) in WITNESSES.items():
            _, adj = from_edges(n, E)
            print(analyse(n, adj, rng, name, want_rank=True))
        print("doubled_triangle explicit realization fails:", doubled_triangle_feasible(rng))
        return
    for nn in sys.argv[1:]:
        out = subprocess.run(["geng", "-c", "-d2", "-q", nn], capture_output=True, text=True).stdout
        tot = flat = cls = cnt = 0
        bad = bad_deg = 0
        nobad = nobad_deg = nobad_deg_gt3 = 0
        nobad_deg_other = []
        withrigid = withrigid_nondeg = 0
        for line in out.splitlines():
            n, adj = decode_g6(line)
            r = analyse(n, adj, rng, line)
            tot += 1
            flat += r["flat"]
            cls += r["classes"]
            cnt += r["count"]
            if r["nrigid"]:
                withrigid += 1
                withrigid_nondeg += not r["fails"]
            if r["bad"]:
                bad += 1
                bad_deg += bool(r["fails"])
            else:
                nobad += 1
                if r["fails"]:
                    nobad_deg += 1
                    if r["hubnbhd_gt3"]:
                        nobad_deg_gt3 += 1
                    else:
                        nobad_deg_other.append((line, r["fails"]))
        print(f"n={nn}: graphs {tot}; (F) flat ok {flat}; (C) classes ok {cls}; (K) count ok {cnt}; "
              f"with a planar-rigid set {withrigid}, of them nondegenerate {withrigid_nondeg}; "
              f"bad pair {bad}, degenerate {bad_deg}; no bad pair {nobad}, degenerate {nobad_deg} "
              f"(closed hub-nbhd > 3: {nobad_deg_gt3}; other: {len(nobad_deg_other)})")
        for line, f in nobad_deg_other[:10]:
            print("   other:", line, f)


if __name__ == "__main__":
    main()
