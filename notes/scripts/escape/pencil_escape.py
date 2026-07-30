"""
W5-L7 escape-certificate recon: exact-Q numerics across Case-III chain habitats.

Model (d=3, D=6): molecular / G^2 body-hinge over Q.
  - config: pt : V -> Q^3
  - pencil (= molecular AND panel) stratum: every body of degree >= 3 has its
    closed star coplanar (center + neighbours in one affine plane).
  - hinge extensor for edge uv = hat(u) ^ hat(v) in Lambda^2 R^4 = R^6,
    hat(c) = (c, 1).
  - rigidity matrix R: 5 rows per edge = basis of C_e^perp (Euclidean dot on R^6),
    placed +w in u-block, -w in v-block (each block 6 columns). Shape 5|E| x 6|V|.
  - rank(R) = 6|V| - dim(motions); rigid => 6(|V|-1).

Split: Case III removes an interior degree-2 vertex v of a chain b-v-a-c
  (v,a interior deg-2; b,c hub ends deg>=3), forming G' = G^{ab}_v = G - v + ab.
  a becomes deg-2 in G' (edges ab fresh, ac old).  Redundancy: 5|E(G')| = 6(|V(G')|-1)+1,
  so nullity 1 at full rank; left-null vector lambda unique up to scale.
  r := a-block of sum_j lambda_{(ab)j} * (row (ab,j)) ; KT (6.44): r = -(a-block over ac).
  Escape M1 works  <=>  r . Lambda^2 Pihat(a) != 0  <=>  r . (bhat ^ chat) != 0.
"""
from fractions import Fraction as F
import random, itertools

# ---------- exact-Q linear algebra ----------

def rref(M):
    """Reduced row echelon form (list of list of Fraction). Returns (R, pivots)."""
    M = [row[:] for row in M]
    if not M:
        return M, []
    rows = len(M); cols = len(M[0])
    pivots = []
    r = 0
    for c in range(cols):
        # find pivot in column c at or below row r
        piv = None
        for i in range(r, rows):
            if M[i][c] != 0:
                piv = i; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = F(1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    return M, pivots

def rank(M):
    if not M: return 0
    _, p = rref(M)
    return len(p)

def nullspace(M):
    """Basis of {x : M x = 0} (right null space), as list of column-vectors."""
    if not M:
        return []
    cols = len(M[0])
    R, piv = rref(M)
    pivset = set(piv)
    free = [c for c in range(cols) if c not in pivset]
    basis = []
    for fcol in free:
        vec = [F(0)] * cols
        vec[fcol] = F(1)
        for ri, pc in enumerate(piv):
            vec[pc] = -R[ri][fcol]
        basis.append(vec)
    return basis

def left_nullspace(M):
    """Basis of {y : y^T M = 0} = nullspace of M^T."""
    if not M: return []
    rows = len(M); cols = len(M[0])
    MT = [[M[i][j] for i in range(rows)] for j in range(cols)]
    return nullspace(MT)

def dot(u, v):
    return sum((a * b for a, b in zip(u, v)), F(0))

# ---------- Plucker / exterior ----------

# index order for Lambda^2 of R^4 (basis e0,e1,e2,e3):
PL = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

def wedge2(P, Q):
    """P,Q in Q^4 -> P^Q in R^6 (Plucker coords, order PL)."""
    return [P[i]*Q[j] - P[j]*Q[i] for (i,j) in PL]

def hat(c):
    """homogenize a Q^3 point -> Q^4 as (x,y,z,1)."""
    return [c[0], c[1], c[2], F(1)]

def perp_basis(v):
    """basis of {w in R^6 : w . v = 0} (5-dim if v != 0)."""
    return nullspace([v])  # 1 x 6 matrix

# ---------- graph construction ----------

def double_subdivide(base_edges):
    """base_edges: list of (u,w) with integer base-vertex labels.
    Returns (edges, hubs, chains):
      each base edge u-w becomes u - x - y - w (x,y fresh).
      hubs = base vertices; chains = list of (u, x, y, w)."""
    verts = set()
    for u, w in base_edges:
        verts.add(u); verts.add(w)
    nxt = max(verts) + 1
    edges = []
    chains = []
    for (u, w) in base_edges:
        x = nxt; y = nxt + 1; nxt += 2
        edges += [(u, x), (x, y), (y, w)]
        chains.append((u, x, y, w))
    hubs = sorted(verts)
    allverts = sorted(set(itertools.chain.from_iterable(edges)))
    return edges, hubs, chains, allverts

def neighbors(edges, allverts):
    nb = {v: set() for v in allverts}
    for u, w in edges:
        nb[u].add(w); nb[w].add(u)
    return nb

# ---------- random exact-Q sampling ----------

def rquat(rng, lo=-9, hi=9, dens=6):
    return F(rng.randint(lo, hi), rng.randint(1, dens))

def rvec3(rng):
    return [rquat(rng) for _ in range(3)]

def sample_pencil_split(base_edges, split_chain_index, rng):
    """Build G' = G^{ab}_v from double-subdivided base, sample a pencil-generic
    exact-Q realization, and return everything needed for the escape test.

    Returns dict with edges', pts, and labels a,b,c (b = hub adjacent to split v)."""
    edges, hubs, chains, allverts = double_subdivide(base_edges)
    # choose split chain: u - x - y - w ; split v=x (deg2, adj hub u); a=y, b=u, c=w
    (u, x, y, w) = chains[split_chain_index]
    b, c, a, v = u, w, y, x
    # G' = G - v + edge(b, a)   [b=u, a=y]  (fresh edge ab connects u and y)
    edges2 = []
    for (p, q) in edges:
        if p == v or q == v:
            continue
        edges2.append((p, q))
    edges2.append((b, a))  # fresh ab   (= u - y)
    Vp = sorted(set(itertools.chain.from_iterable(edges2)))
    nb = neighbors(edges2, Vp)

    # sample planes at hubs (all base vertices are hubs, deg>=3 in the subdivision)
    pt = {}
    normal = {}
    for h in hubs:
        pt[h] = rvec3(rng)
        # plane through pt[h] with random normal
        normal[h] = rvec3(rng)

    def in_plane_point(h, rng):
        """random point on plane {p : normal[h].(p-pt[h])=0}."""
        n = normal[h]
        # pick two directions spanning the plane
        # find two independent vectors orthogonal to n
        basis = []
        for e in ([F(1),F(0),F(0)],[F(0),F(1),F(0)],[F(0),F(0),F(1)]):
            # project out n
            proj = dot(e, n) / dot(n, n) if dot(n,n)!=0 else F(0)
            d = [e[i] - proj*n[i] for i in range(3)]
            if any(di != 0 for di in d):
                basis.append(d)
            if len(basis) == 2:
                break
        s = rquat(rng); t = rquat(rng)
        return [pt[h][i] + s*basis[0][i] + t*basis[1][i] for i in range(3)]

    def line_meet_point(h1, h2, rng):
        """random point on the meet line Pi(h1) ^ Pi(h2)."""
        n1, n2 = normal[h1], normal[h2]
        # direction = n1 x n2
        d = [n1[1]*n2[2]-n1[2]*n2[1], n1[2]*n2[0]-n1[0]*n2[2], n1[0]*n2[1]-n1[1]*n2[0]]
        # find a base point on both planes: solve n1.p = n1.pt[h1], n2.p = n2.pt[h2]
        c1 = dot(n1, pt[h1]); c2 = dot(n2, pt[h2])
        # 2 eqns, 3 unknowns; set p = alpha*e_k form -- use least structure:
        # parametrize p = p0 + t d ; find p0 by solving the 2x2 in the two coords
        # with largest |d|-complement. Just solve linear system [n1;n2] p = [c1;c2],
        # min-norm-ish via picking a free coordinate = 0 where possible.
        for freecoord in range(3):
            cols = [k for k in range(3) if k != freecoord]
            A = [[n1[cols[0]], n1[cols[1]]],
                 [n2[cols[0]], n2[cols[1]]]]
            det = A[0][0]*A[1][1] - A[0][1]*A[1][0]
            if det != 0:
                p0 = [F(0),F(0),F(0)]
                rhs0 = c1; rhs1 = c2
                inv = [[A[1][1]/det, -A[0][1]/det],[-A[1][0]/det, A[0][0]/det]]
                s0 = inv[0][0]*rhs0 + inv[0][1]*rhs1
                s1 = inv[1][0]*rhs0 + inv[1][1]*rhs1
                p0[cols[0]] = s0; p0[cols[1]] = s1
                break
        t = rquat(rng)
        return [p0[i] + t*d[i] for i in range(3)]

    # place all vertices
    placed = {}
    for h in hubs:
        placed[h] = pt[h]
    # subdivision vertices: each is adjacent to exactly one hub, except a (adj two hubs b,c)
    for s in Vp:
        if s in hubs:
            continue
        hub_nbrs = [t for t in nb[s] if t in hubs]
        if s == a:
            placed[a] = line_meet_point(b, c, rng)
        elif len(hub_nbrs) == 1:
            placed[s] = in_plane_point(hub_nbrs[0], rng)
        elif len(hub_nbrs) == 0:
            # interior of a longer chain (not present in double-subdivision after split
            # except possibly): place generically (free deg-2 vertex)
            placed[s] = rvec3(rng)
        else:
            # adjacent to 2 hubs but not the split 'a': place on their meet line
            placed[s] = line_meet_point(hub_nbrs[0], hub_nbrs[1], rng)

    return {
        'edges': edges2, 'V': Vp, 'pt': placed, 'nb': nb,
        'a': a, 'b': b, 'c': c, 'v': v, 'hubs': hubs,
    }

# ---------- rigidity matrix + escape ----------

def build_rigidity(data):
    edges = data['edges']; V = data['V']; pt = data['pt']
    idx = {v: k for k, v in enumerate(V)}
    n = len(V)
    ncol = 6 * n
    rows = []
    edge_rows = {}   # edge -> list of global row indices
    C = {}           # edge -> hinge extensor (6-vector)
    for e in edges:
        (uu, ww) = e
        Ce = wedge2(hat(pt[uu]), hat(pt[ww]))
        C[e] = Ce
        wb = perp_basis(Ce)  # 5 vectors of length 6
        ridx = []
        for w in wb:
            row = [F(0)] * ncol
            base_u = 6 * idx[uu]; base_w = 6 * idx[ww]
            for k in range(6):
                row[base_u + k] += w[k]
                row[base_w + k] -= w[k]
            ridx.append(len(rows))
            rows.append(row)
        edge_rows[e] = ridx
    return rows, edge_rows, C, idx, n

def escape_test(data):
    rows, edge_rows, C, idx, n = build_rigidity(data)
    R = rows
    rk = rank(R)
    target = 6 * (n - 1)
    ln = left_nullspace(R)      # basis of {y : y^T R = 0}
    nullity = len(ln)
    result = {'rank': rk, 'target': target, 'nullity': nullity, 'nrows': len(R), 'nverts': n}
    if nullity != 1 or rk != target:
        result['ok'] = False
        return result
    result['ok'] = True
    lam = ln[0]   # length = #rows
    a, b, c = data['a'], data['b'], data['c']
    pt = data['pt']
    # edge ab (fresh) and ac (old). find them:
    def find_edge(p, q):
        for e in edge_rows:
            if set(e) == {p, q}:
                return e
        return None
    e_ab = find_edge(a, b); e_ac = find_edge(a, c)
    # r = a-block of sum_j lambda_{(ab)j} row(ab,j)
    # row(ab,j) has +w on the 'first' endpoint of the stored edge tuple, - on second.
    # a-block = +w if a is first endpoint else -w.
    def ablock_r(e):
        (uu, ww) = e
        sgn = F(1) if uu == a else F(-1)
        acc = [F(0)] * 6
        for ri in edge_rows[e]:
            coef = lam[ri]
            row = R[ri]
            base_a = 6 * idx[a]
            for k in range(6):
                acc[k] += coef * row[base_a + k]
        return acc
    r_ab = ablock_r(e_ab)
    r_ac = ablock_r(e_ac)
    # KT (6.44) check: r_ab + r_ac == 0 (a-column block of lambda^T R = 0)
    result['eq644'] = all(x == 0 for x in [r_ab[k] + r_ac[k] for k in range(6)])
    r = r_ab
    result['r_zero'] = all(x == 0 for x in r)
    # planes
    ahat = hat(pt[a]); bhat = hat(pt[b]); chat = hat(pt[c])
    Cab = wedge2(ahat, bhat); Cac = wedge2(ahat, chat); Cbc = wedge2(bhat, chat)
    # sanity: r . Cab == 0, r . Cac == 0
    result['r_perp_Cab'] = dot(r, Cab) == 0
    result['r_perp_Cac'] = dot(r, Cac) == 0
    # escape M1: r . Lambda^2 Pihat(a) != 0  <=>  r . Cbc != 0 (given the two above)
    result['r_dot_Cbc'] = dot(r, Cbc)
    result['M1_works'] = dot(r, Cbc) != 0
    # dim S = dim(Lambda^2 Pihat(a) + pencil(b) + pencil(c))
    L2a = span_L2(ahat, bhat, chat)                       # 3-dim
    penb = pencil_space(bhat, data, b)                    # 2-dim
    penc = pencil_space(chat, data, c)                    # 2-dim
    Smat = L2a + penb + penc
    result['dimS'] = rank(Smat)
    result['dim_L2a'] = rank(L2a)
    result['dim_penb'] = rank(penb)
    result['dim_penc'] = rank(penc)
    # M2 works: r not perp pencil(b) ; M3 works: r not perp pencil(c)
    result['M2_works'] = any(dot(r, w) != 0 for w in penb)
    result['M3_works'] = any(dot(r, w) != 0 for w in penc)
    # total-failure test: r in S^perp ?  (r perp all of S)
    result['r_in_Sperp'] = all(dot(r, w) == 0 for w in Smat)
    return result

def span_L2(*hats):
    """Lambda^2 of span(hats) : all pairwise wedges."""
    out = []
    for i in range(len(hats)):
        for j in range(i+1, len(hats)):
            out.append(wedge2(hats[i], hats[j]))
    return out

def pencil_space(centerhat, data, hub):
    """pencil(hub) = centerhat ^ Pihat(hub), spanned by centerhat ^ (neighbour hats)."""
    pt = data['pt']; nb = data['nb']
    out = []
    for u in nb[hub]:
        out.append(wedge2(centerhat, hat(pt[u])))
    return out
