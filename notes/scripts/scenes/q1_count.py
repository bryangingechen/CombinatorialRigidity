"""Q1 (PENCIL-SCENES): Whiteley 1989's count on S_G against 3 + def_2(G).

S_G: points V, one face N[v] per body v; point w on face v iff w in N[v].
Exact arithmetic only (fractions.Fraction; GF(p) and GF(2^16) for the
characteristic checks).  Reports, per graph:

  n, |E|, |I| = 2|E| + |V|
  def2   = max_P [3(|P|-1) - 2 d_G(P)]                       (KT/JJ deficiency, D = 3)
  defvb  = max_P [3(|P|-1) - sum_{B in P} |N(B) \\ B|]        (face-disjoint partitions of I)
  rcount = rank of Whiteley's count matroid on I (greedy, exact oracle)
  dimL   = dim L(q) at random rational pictures (scene matrix kernel), also
           over GF(1000003) and GF(2^16)
and checks 4|V| - rcount == 3 + def2 == dimL.
"""
import itertools
import random
import sys
from fractions import Fraction

# ---------------------------------------------------------------- graphs


def from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    E = sorted({(min(u, v), max(u, v)) for u, v in edges})
    return n, E, adj


def cycle(n):
    return from_edges(n, [(i, (i + 1) % n) for i in range(n)])


def complete(n):
    return from_edges(n, list(itertools.combinations(range(n), 2)))


def kbip(a, b):
    return from_edges(a + b, [(i, a + j) for i in range(a) for j in range(b)])


def theta(*lens):
    """Two poles 0, 1 joined by internally disjoint paths of the given lengths."""
    edges, nxt = [], 2
    for L in lens:
        prev = 0
        for _ in range(L - 1):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
        edges.append((prev, 1))
    return from_edges(nxt, edges)


def prism():
    return from_edges(6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
                          (0, 3), (1, 4), (2, 5)])


def bowtie():
    return from_edges(5, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)])


def wheel(k):
    return from_edges(k + 1, [(i, (i + 1) % k) for i in range(k)] +
                      [(i, k) for i in range(k)])


def cube():
    return from_edges(8, [(i, j) for i in range(8) for j in range(i + 1, 8)
                          if bin(i ^ j).count('1') == 1])


def petersen():
    out = [(i, (i + 1) % 5) for i in range(5)]
    inn = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    spk = [(i, 5 + i) for i in range(5)]
    return from_edges(10, out + inn + spk)


def two_k4_at_vertex():
    k = list(itertools.combinations(range(4), 2))
    k2 = [(0 if a == 0 else a + 3, 0 if b == 0 else b + 3) for a, b in k]
    return from_edges(7, k + k2)


def octahedron():
    return from_edges(6, [(i, j) for i in range(6) for j in range(i + 1, 6)
                          if j != i + 3])


def k4_subdivided():
    return from_edges(5, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (4, 3)])


def random_graph(n, p, rng):
    while True:
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)
                 if rng.random() < p]
        g = from_edges(n, edges)
        if all(len(a) >= 2 for a in g[2]):
            return g


# ------------------------------------------------------------- partitions


def set_partitions(n):
    """Restricted growth strings: labels[i] in 0..max(labels[:i])+1."""
    labels = [0] * n

    def rec(i, m):
        if i == n:
            yield labels, m + 1
            return
        for c in range(m + 2):
            labels[i] = c
            yield from rec(i + 1, max(m, c))

    if n == 0:
        yield [], 0
        return
    labels[0] = 0
    yield from rec(1, 0)


def deficiencies(g):
    """(def2, defvb) by enumerating the partitions of V."""
    n, E, adj = g
    best2 = bestvb = None
    for lab, k in set_partitions(n):
        dP = sum(1 for u, v in E if lab[u] != lab[v])
        val2 = 3 * (k - 1) - 2 * dP
        # sum over parts B of |N(B) \ B| = sum over w of #foreign parts adjacent to w
        vb = sum(len({lab[x] for x in adj[w]} - {lab[w]}) for w in range(n))
        valvb = 3 * (k - 1) - vb
        best2 = val2 if best2 is None else max(best2, val2)
        bestvb = valvb if bestvb is None else max(bestvb, valvb)
    return best2, bestvb


# ------------------------------------------------ the count matroid's rank


def incidences(g):
    n, E, adj = g
    return [(w, v) for v in range(n) for w in sorted(adj[v] | {v})]


def count_rank(g, order=None):
    """Greedy rank of the matroid {F : |X| <= |A(X)| + 3|B(X)| - 3, all
    nonempty X subset F} on the incidences of S_G.

    Oracle (exact): F is independent iff for every nonempty face set B',
    sum_a max(0, c_a(B') - 1) <= 3(|B'| - 1), where c_a(B') counts the
    incidences of F with point a and face in B'.  Adding (a, v) raises the
    left side at B' (containing v) by one exactly when c_a(B') >= 1.
    """
    n = g[0]
    inc = incidences(g)
    if order is not None:
        inc = [inc[i] for i in order]
    M = 1 << n
    lhs = [0] * M
    cap = [3 * (bin(m).count('1') - 1) for m in range(M)]
    c = [[0] * M for _ in range(n)]
    rank = 0
    for a, v in inc:
        bit = 1 << v
        ca = c[a]
        ok = True
        for m in range(M):
            if m & bit and ca[m] >= 1 and lhs[m] + 1 > cap[m]:
                ok = False
                break
        if not ok:
            continue
        rank += 1
        for m in range(M):
            if m & bit:
                if ca[m] >= 1:
                    lhs[m] += 1
                ca[m] += 1
    return rank


# --------------------------------------------------------- linear algebra


class Rat:
    zero, one = Fraction(0), Fraction(1)

    @staticmethod
    def inv(a):
        return 1 / a

    @staticmethod
    def neg(a):
        return -a

    @staticmethod
    def rand(rng):
        return Fraction(rng.randint(-10**6, 10**6))


class GFp:
    def __init__(self, p):
        self.p, self.zero, self.one = p, 0, 1

    def inv(self, a):
        return pow(a, self.p - 2, self.p)

    def neg(self, a):
        return (-a) % self.p

    def rand(self, rng):
        return rng.randrange(self.p)


def _deg(x):
    return x.bit_length() - 1


def _pmod(a, f):
    df = _deg(f)
    while a and _deg(a) >= df:
        a ^= f << (_deg(a) - df)
    return a


class GF2k:
    """GF(2^16) = GF(2)[t]/(f); f is checked irreducible at construction."""

    def __init__(self, f=0x1002D):
        self.f, self.k = f, _deg(f)
        for d in range(1, self.k // 2 + 1):
            for h in range(1 << d, 1 << (d + 1)):
                assert _pmod(f, h) != 0, "reducible"
        self.zero, self.one = 0, 1

    def mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a >> self.k:
                a ^= self.f
        return r

    def inv(self, a):
        # a^(2^k - 2)
        r, e, base = 1, (1 << self.k) - 2, a
        while e:
            if e & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            e >>= 1
        return r

    def neg(self, a):
        return a

    def rand(self, rng):
        return rng.randrange(1 << self.k)


def rank(rows, F):
    """Row rank by Gaussian elimination over the field F."""
    if isinstance(F, GF2k):
        mul, add = F.mul, (lambda a, b: a ^ b)
    elif isinstance(F, GFp):
        p = F.p
        mul, add = (lambda a, b: a * b % p), (lambda a, b: (a + b) % p)
    else:
        mul, add = (lambda a, b: a * b), (lambda a, b: a + b)
    rows = [list(r) for r in rows]
    r = 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        piv = next((i for i in range(r, len(rows)) if rows[i][col] != F.zero), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = F.inv(rows[r][col])
        prow = [mul(iv, x) for x in rows[r]]
        rows[r] = prow
        for i in range(len(rows)):
            if i != r and rows[i][col] != F.zero:
                f = F.neg(rows[i][col])
                rows[i] = [add(x, mul(f, y)) for x, y in zip(rows[i], prow)]
        r += 1
    return r


def det3(F, p, q, s):
    """det of the homogeneous points (x, y, 1) of p, q, s; only zero-test used."""
    if isinstance(F, GF2k):
        mul, sub = F.mul, (lambda a, b: a ^ b)
    elif isinstance(F, GFp):
        mul, sub = (lambda a, b: a * b % F.p), (lambda a, b: (a - b) % F.p)
    else:
        mul, sub = (lambda a, b: a * b), (lambda a, b: a - b)
    ax, ay = sub(q[0], p[0]), sub(q[1], p[1])
    bx, by = sub(s[0], p[0]), sub(s[1], p[1])
    return sub(mul(ax, by), mul(ay, bx))


def admissible(g, pic, F):
    n, E, adj = g
    if any(pic[u] == pic[v] for u, v in E):
        return False
    for v in range(n):
        N = sorted(adj[v] | {v})
        if all(det3(F, pic[a], pic[b], pic[c]) == F.zero
               for a, b, c in itertools.combinations(N, 3)):
            return False
    return True


def scene_dim(g, pic, F):
    """dim of Whiteley's space of scenes over pic: unknowns z_w (n) and a
    plane (a_v, b_v, c_v) per face; one row z_w - x_w a_v - y_w b_v - c_v
    per incidence (Whiteley 1989 Def. 3.1, with r = -(a, b, c))."""
    n = g[0]
    rows = []
    for w, v in incidences(g):
        row = [F.zero] * (4 * n)
        row[w] = F.one
        row[n + 3 * v] = F.neg(pic[w][0])
        row[n + 3 * v + 1] = F.neg(pic[w][1])
        row[n + 3 * v + 2] = F.neg(F.one)
        rows.append(row)
    return 4 * n - rank(rows, F), rank(rows, F)


def lifting_dim(g, pic, F):
    """dim L(q) directly: heights z with z|N[v] affine for each v.  For each
    v pick three non-collinear members of N[v]; each further member w gives
    the row of the 4x4 determinant (cofactors along the z column)."""
    if isinstance(F, GF2k):
        mul, add, sub = F.mul, (lambda a, b: a ^ b), (lambda a, b: a ^ b)
    elif isinstance(F, GFp):
        mul = lambda a, b: a * b % F.p
        add = lambda a, b: (a + b) % F.p
        sub = lambda a, b: (a - b) % F.p
    else:
        mul, add, sub = (lambda a, b: a * b), (lambda a, b: a + b), (lambda a, b: a - b)

    def d3(P, Q, R):  # det [[Px,Qx,Rx],[Py,Qy,Ry],[1,1,1]]
        return det3(F, P, Q, R)

    n, E, adj = g
    rows = []
    for v in range(n):
        N = sorted(adj[v] | {v})
        tri = next(t for t in itertools.combinations(N, 3)
                   if d3(pic[t[0]], pic[t[1]], pic[t[2]]) != F.zero)
        for w in N:
            if w in tri:
                continue
            pts = list(tri) + [w]
            # z_w * d(tri) - z_t0 d(t1,t2,w) + z_t1 d(t0,t2,w) - z_t2 d(t0,t1,w) = 0
            row = [F.zero] * n
            a, b, c = tri
            row[w] = add(row[w], d3(pic[a], pic[b], pic[c]))
            row[a] = sub(row[a], d3(pic[b], pic[c], pic[w]))
            row[b] = add(row[b], d3(pic[a], pic[c], pic[w]))
            row[c] = sub(row[c], d3(pic[a], pic[b], pic[w]))
            rows.append(row)
    return n - (rank(rows, F) if rows else 0)


def random_picture(g, F, rng):
    while True:
        pic = [(F.rand(rng), F.rand(rng)) for _ in range(g[0])]
        if admissible(g, pic, F):
            return pic


# ------------------------------------------------------------------ main


def named_graphs(rng):
    gs = [("C4", cycle(4)), ("C5", cycle(5)), ("C6", cycle(6)),
          ("K4", complete(4)), ("K5", complete(5)),
          ("K2,3 = theta(2,2,2)", kbip(2, 3)), ("K2,4", kbip(2, 4)),
          ("K3,3", kbip(3, 3)),
          ("diamond = theta(1,2,2)", theta(1, 2, 2)),
          ("theta(1,2,3)", theta(1, 2, 3)), ("theta(1,3,3)", theta(1, 3, 3)),
          ("theta(2,2,3)", theta(2, 2, 3)), ("theta(2,3,3)", theta(2, 3, 3)),
          ("theta(3,3,3)", theta(3, 3, 3)), ("theta(2,2,2,2)", theta(2, 2, 2, 2)),
          ("prism", prism()), ("bowtie", bowtie()), ("wheel W5", wheel(5)),
          ("K4, one edge subdivided", k4_subdivided()),
          ("two K4 at a vertex", two_k4_at_vertex()),
          ("octahedron", octahedron()), ("cube Q3", cube()),
          ("Petersen", petersen())]
    for i, (n, p) in enumerate([(6, .45), (7, .4), (7, .5), (8, .35), (8, .45),
                                (9, .3), (9, .4)]):
        g = random_graph(n, p, rng)
        gs.append((f"random{i + 1} n={n} E={g[1]}", g))
    return gs


def main():
    rng = random.Random(20261109)
    fields = [("Q", Rat), ("GF(1000003)", GFp(1000003)), ("GF(2^16)", GF2k())]
    print("| graph | n | E | I | def2 | defvb | 4n - rcount | 3 + def2 | dim L, Q (3 pictures) | dim L, GF(1000003) | dim L, GF(2^16) | agree |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    allok = True
    for name, g in named_graphs(rng):
        n, E, adj = g
        d2, dvb = deficiencies(g)
        rc = count_rank(g)
        rc2 = count_rank(g, order=rng.sample(range(2 * len(E) + n), 2 * len(E) + n))
        assert rc == rc2, (name, rc, rc2)
        dims = {}
        for fname, F in fields:
            ds = []
            for _ in range(3 if fname == "Q" else 2):
                pic = random_picture(g, F, rng)
                sd, _ = scene_dim(g, pic, F)
                ld = lifting_dim(g, pic, F)
                assert sd == ld, (name, fname, sd, ld)
                ds.append(sd)
            dims[fname] = ds
        target = 3 + d2
        ok = (4 * n - rc == target and dvb == d2 and
              all(min(ds) == target for ds in dims.values()))
        allok &= ok
        if "E=" in name:
            name = name.split(" E=")[0] + " E=" + str(E).replace(" ", "")
        print(f"| {name} | {n} | {len(E)} | {2 * len(E) + n} | {d2} | {dvb} | {4 * n - rc} | {target} | "
              f"{','.join(map(str, dims['Q']))} | {','.join(map(str, dims['GF(1000003)']))} | "
              f"{','.join(map(str, dims['GF(2^16)']))} | {'yes' if ok else 'NO'} |")
        sys.stdout.flush()
    print("\nall agree:", allok)


if __name__ == "__main__":
    main()
