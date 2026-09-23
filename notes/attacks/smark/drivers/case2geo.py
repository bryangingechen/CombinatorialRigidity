#!/usr/bin/env python3
"""
case2geo.py -- Case-2 geometric control:  on small Case-2 hub graphs, does every rank pattern
with jump J3 >= 1 have codimension >= J3 + 1 in the constrained plane space A_q?

Setting (helper spec, 2026-09-23).  Graph H' with marked set Z, Gamma = H'[Z], Big = {u : deg_Gamma(u) >= 3},
U_c = Big cap N_Gamma[c], k_c = |U_c| <= 3.  One exact random point q_u in P^3 per big u (general position).
Plane normals n_c in U_c^perp;  A_q = prod_c P(U_c^perp), dim sum_c (3 - k_c).
Pattern (C, L, I): set partition C of Z (class A has n_A in U_A^perp, U_A = union of U_c, |U_A| <= 3);
partial linear space L on the classes (lines of >= 3 classes, pairwise meeting in <= 1);  I(l) subset of Big,
|I(l)| <= 2, the big points ON the geometric line of l.  X_A = union_{l ni A} I(l) minus U_A are extra incidences.
Codim bound (sound):  M + rho,  M = sum_c (3 - k_c) - sum_A (3 - |U_A|),  rho = rank of the Jacobian of
(collinearity minors of each line, incidence equations n_A . q_u = 0 for u in X_A) w.r.t. coordinates on the
subspaces U_A^perp, at an exactly verified realisation.  Jump J3 = sum over non-big y (marked non-big with
E_y = N_Gamma[y], connectors with E_y = {a, b}) of s_y - rk_y, rk_y read off the pattern.
Check: slack := (M + rho) - (J3 + 1) >= 0 for every realised pattern with J3 >= 1.

Arithmetic: realisations, their verification and all subspace intersections are exact over Q (Python ints /
Fractions); rho is computed mod 2^61 - 1 (<= the Q-rank, so M + rho stays a sound lower bound), as starcheck.py does.

Sound partition-level pruning (each partition's J3 ranges in [J3_min, J3_max], lines only cover triples):
  * J3_max = 0            -> J3 == 0 for every line structure: nothing to check.
  * M >= J3_max + 2       -> slack >= 1 for every (L, I): counted, lines not enumerated.
  * M == J3_max + 1       -> slack = rho + (J3_max - J3) >= 0; slack 0 needs rho = 0, which (|Big| <= 3, see
                             rho_zero_possible) forces every line to consist of classes with |U_A| >= 2 sharing a
                             common pair = I(l), and X == empty.  Only those line structures are enumerated
                             (census), the rest are slack >= 1.
  * M <= J3_max           -> every line structure enumerated; need = J3 + 1 - M;  need <= -1: slack >= 1;
                             need == 0: slack = rho, census as above;  need >= 1: realise every I, compute rho.
--realise-all disables the rho-criterion shortcut (every need >= 0 pattern realised) as a cross-check.

Run from the repository root (the drivers directory is located from this file; CR_REPO overrides):
    timeout 900 python3 notes/attacks/smark/drivers/case2geo.py --graph T6 --budget 800
"""
import sys, os, time, math, itertools, random, argparse
from fractions import Fraction
from collections import deque, defaultdict

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get("CR_REPO", os.path.abspath(os.path.join(_HERE, "..", "..", "..", "..")))
sys.path.insert(0, os.path.join(REPO, "notes", "attacks", "smark", "drivers"))
import starcheck as SC                      # rank_exact, rank_mod, nullspace_exact, to_int_vec, proportional, set_partitions
from case2m2 import CASES                    # the ten Case-2 hub graphs (+ controls)

BASE_SEED = 20260923
P_MOD = (1 << 61) - 1
PLS_COUNT = {1: 1, 2: 1, 3: 2, 4: 6, 5: 32, 6: 353, 7: 8390, 8: 433039}   # partial linear spaces on q labelled points

rank_exact, rank_mod, to_int_vec, proportional = SC.rank_exact, SC.rank_mod, SC.to_int_vec, SC.proportional

def nullspace(rows, n=4):
    """integer basis of {x in Q^n : r . x = 0 for all rows r}."""
    if not rows:
        return [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    return [to_int_vec(v) for v in SC.nullspace_exact([list(r) for r in rows])]

def dot(a, b): return sum(x * y for x, y in zip(a, b))

# --------------------------------------------------------------------------- big points
def draw_points(nbig, seed):
    rng = random.Random(f"{seed}:bigpoints")
    while True:
        pts = [[rng.randint(-30, 30) for _ in range(4)] for _ in range(nbig)]
        if any(not any(p) for p in pts): continue
        ok = all(rank_exact(list(S)) == len(S) for k in range(2, min(4, nbig) + 1) for S in itertools.combinations(pts, k))
        if ok: return pts

# --------------------------------------------------------------------------- line structures
def pls_iter(q, allowed=None):
    """all partial linear spaces (sets of lines of size >= 3, pairwise meeting in <= 1) whose lines use only
    `allowed` classes; yields tuples of frozensets, the empty structure first."""
    pool = list(range(q)) if allowed is None else sorted(allowed)
    cands = [frozenset(s) for k in range(3, len(pool) + 1) for s in itertools.combinations(pool, k)]
    n = len(cands)
    compat = [[len(cands[i] & cands[j]) <= 1 for j in range(n)] for i in range(n)]
    def rec(start, chosen):
        yield tuple(cands[i] for i in chosen)
        for j in range(start, n):
            if all(compat[j][i] for i in chosen):
                chosen.append(j)
                yield from rec(j + 1, chosen)
                chosen.pop()
    yield from rec(0, [])

def lines_key(lines): return tuple(sorted(tuple(sorted(L)) for L in lines))

# --------------------------------------------------------------------------- I-assignments
def enumerate_I(UA, lines, Big, require_auto=False):
    """all I: lines -> subsets of Big (|I| <= 2) with the spec's constraints and the closure rules.
    Returns (valid, pruned) where valid = list of (I tuple, X tuple, F tuple) and pruned = number of
    assignments meeting the spec's basic constraints but unrealisable by a closure rule.
    require_auto: only assignments with every |I(l)| == 2 and X == empty (the rho = 0 candidates)."""
    q = len(UA); lines = list(lines)
    opts = []
    for L in lines:
        base = set()
        for B, C in itertools.combinations(sorted(L), 2):
            base |= UA[B] & UA[C]
        if len(base) > 2: return [], 0
        o = []
        for r in range(len(base), 3):
            for S in itertools.combinations(Big, r):
                S = frozenset(S)
                if not base <= S: continue
                if any(len(UA[A] | S) > 3 for A in L): continue
                if require_auto and (len(S) != 2 or any(not S <= UA[A] for A in L)): continue
                o.append(S)
        if not o: return [], 0
        opts.append(o)
    valid = []; pruned = 0
    pairs = [frozenset(P) for P in itertools.combinations(Big, 2)]
    for I in itertools.product(*opts):
        F = [set(UA[A]) for A in range(q)]
        for L, S in zip(lines, I):
            for A in L: F[A] |= S
        if any(len(f) > 3 for f in F): pruned += 1; continue
        ok = True
        for L, S in zip(lines, I):                       # closure: two classes on l sharing a point put it on l
            for B, C in itertools.combinations(sorted(L), 2):
                if not (F[B] & F[C]) <= S: ok = False; break
            if not ok: break
        if ok:
            for (L1, S1), (L2, S2) in itertools.combinations(zip(lines, I), 2):
                if len(S1) == 2 and S1 == S2: ok = False; break      # two lines through the same two points
        if ok:
            for A, B in itertools.combinations(range(q), 2):
                if len(F[A]) == 3 and F[A] == F[B]: ok = False; break  # two classes with the same forced plane
        if ok:
            for P in pairs:                                            # planes through the line P are collinear
                SP = [A for A in range(q) if P <= F[A]]
                if len(SP) >= 3 and not any(set(SP) <= L for L in lines): ok = False; break
                for L, S in zip(lines, I):
                    if S == P and not set(SP) <= L: ok = False; break
                if not ok: break
        if not ok: pruned += 1; continue
        X = tuple(frozenset(F[A] - UA[A]) for A in range(q))
        if require_auto and any(X): pruned += 0; continue            # (not counted as pruned: only filtered)
        valid.append((tuple(I), X, tuple(frozenset(f) for f in F)))
    return valid, pruned

# --------------------------------------------------------------------------- realisation
def rand_in_span(basis, rng, avoid):
    for _ in range(60):
        co = [rng.randint(-30, 30) for _ in basis]
        v = [sum(c * b[i] for c, b in zip(co, basis)) for i in range(4)]
        if any(v) and not any(proportional(v, w) for w in avoid):
            return v
    return None

def realise(q, lines, Fpts, Wbasis, order, rng):
    """Fpts[A]: list of big points class A must contain; Wbasis[A]: integer basis of their perp.
    Sequential placement; returns normals or None."""
    pts = [None] * q
    for c in order:
        placed = [w for w in pts if w is not None]
        det = []
        for L in lines:
            if c in L:
                on = [pts[d] for d in L if d != c and pts[d] is not None]
                if len(on) >= 2: det.append(on[:2])
        if not det:
            v = rand_in_span(Wbasis[c], rng, placed)
        else:
            rows = [list(p) for p in Fpts[c]]
            for on in det:
                rows += nullspace([on[0], on[1]])              # n in span(on) <=> n perp span(on)^perp
            V = nullspace(rows)
            if len(V) == 0: return None
            if len(V) >= 2:
                if len(det) >= 2: return None                 # two determined lines coincide
                v = rand_in_span(V, rng, placed)
            else:
                v = V[0]
                if not any(v) or any(proportional(v, u) for u in placed): return None
        if v is None: return None
        pts[c] = v
    return pts

def verify(q, lines, pts, Fset, Big, qpts):
    """pts carries EXACTLY the pattern: classes distinct, lines collinear, other triples rank 3,
    n_A . q_u = 0 iff u in F_A."""
    for a, b in itertools.combinations(range(q), 2):
        if rank_exact([pts[a], pts[b]]) != 2: return False
    for L in lines:
        if rank_exact([pts[c] for c in L]) != 2: return False
    for tri in itertools.combinations(range(q), 3):
        s = frozenset(tri)
        in_line = any(s <= L for L in lines)
        r = rank_exact([pts[c] for c in tri])
        if in_line and r != 2: return False
        if (not in_line) and r != 3: return False
    for A in range(q):
        for ui, u in enumerate(Big):
            if (dot(pts[A], qpts[ui]) == 0) != (u in Fset[A]): return False
    return True

def jac_rank(q, lines, pts, Bbasis, Xpts):
    """rank mod p of the Jacobian of all 3x3 collinearity minors and the incidence equations n_A . q_u = 0
    (u in X_A), in the coordinates t_A with n_A = sum_j t_{A,j} b_{A,j}, b_{A,.} a basis of U_A^perp."""
    offs = [0]
    for A in range(q): offs.append(offs[-1] + len(Bbasis[A]))
    ncol = offs[-1]; rows = []
    for A in range(q):
        for p in Xpts[A]:
            row = [0] * ncol
            for j, b in enumerate(Bbasis[A]): row[offs[A] + j] = dot(b, p)
            rows.append(row)
    for L in lines:
        Ls = sorted(L)
        for C in itertools.combinations(Ls, 3):
            for R in itertools.combinations(range(4), 3):
                grad = {}
                for ri, i in enumerate(R):
                    Rm = [x for x in R if x != i]
                    for ci, c in enumerate(C):
                        Cm = [x for x in C if x != c]
                        d2 = pts[Cm[0]][Rm[0]] * pts[Cm[1]][Rm[1]] - pts[Cm[1]][Rm[0]] * pts[Cm[0]][Rm[1]]
                        grad[(c, i)] = (-1) ** (ri + ci) * d2
                row = [0] * ncol
                for c in C:
                    for j, b in enumerate(Bbasis[c]):
                        row[offs[c] + j] = sum(grad.get((c, i), 0) * b[i] for i in range(4))
                rows.append(row)
    return rank_mod(rows) if rows else 0

def greedy_order(q, lines, dimW, rng):
    placed = set(); order = []
    while len(order) < q:
        rem = [c for c in range(q) if c not in placed]
        def ndet(c):
            return sum(1 for L in lines if c in L and sum(1 for d in L if d != c and d in placed) >= 2)
        sc = {c: ndet(c) for c in rem}
        constrained = [c for c in rem if dimW[c] <= 2 and sc[c] == 0]
        if constrained:
            m = min(dimW[c] for c in constrained); pool = [c for c in constrained if dimW[c] == m]
        else:
            ones = [c for c in rem if sc[c] == 1]; zeros = [c for c in rem if sc[c] == 0]
            pool = ones or zeros or rem
        c = rng.choice(pool); order.append(c); placed.add(c)
    return order

def compute_rho(q, lines, UA, X, F, Big, qpts, seed, order_cap, nsucc, exhaustive, deadline):
    """realise the pattern (classes with point sets F = U cup X) and return rho statistics."""
    bidx = {u: i for i, u in enumerate(Big)}
    Fpts = [[qpts[bidx[u]] for u in sorted(F[A])] for A in range(q)]
    Xpts = [[qpts[bidx[u]] for u in sorted(X[A])] for A in range(q)]
    Upts = [[qpts[bidx[u]] for u in sorted(UA[A])] for A in range(q)]
    Wbasis = [nullspace(Fpts[A]) for A in range(q)]
    Bbasis = [nullspace(Upts[A]) for A in range(q)]
    dimW = [len(w) for w in Wbasis]
    if any(d == 0 for d in dimW): return dict(status="unrealised", tried=0, orders=[], reason="empty subspace")
    key = (tuple(tuple(sorted(u)) for u in UA), tuple(tuple(sorted(x)) for x in X), lines_key(lines))
    rng = random.Random(f"{seed}:{key}")
    results = []; tried_orders = set(); tried = [0]
    def attempt(order):
        tried[0] += 1
        for _ in range(2):
            pts = realise(q, lines, Fpts, Wbasis, order, rng)
            if pts is None: continue
            if verify(q, lines, pts, F, Big, qpts):
                results.append((jac_rank(q, lines, pts, Bbasis, Xpts), tuple(order), pts)); return True
        return False
    for _ in range(8):
        if len(results) >= nsucc: break
        o = greedy_order(q, lines, dimW, rng); t = tuple(o)
        if t in tried_orders: continue
        tried_orders.add(t); attempt(o)
    fact = math.factorial(q)
    while len(results) < nsucc and tried[0] < order_cap and len(tried_orders) < fact:
        o = list(range(q)); rng.shuffle(o); t = tuple(o)
        if t in tried_orders: continue
        tried_orders.add(t); attempt(o)
    if not results and exhaustive:
        for perm in itertools.permutations(range(q)):
            if perm in tried_orders: continue
            tried_orders.add(perm)
            if attempt(list(perm)): break
            if time.time() > deadline: break
    if not results:
        return dict(status="unrealised", tried=tried[0], orders=[])
    rhos = [r for r, _, _ in results]
    i = rhos.index(min(rhos))
    return dict(status="ok", rho_min=min(rhos), rho_max=max(rhos), nsucc=len(results), tried=tried[0],
                orders=[o for _, o, _ in results], pts=results[i][2])

# --------------------------------------------------------------------------- graphs
def build_graph(Z, edges, conn):
    adj = {z: set() for z in Z}
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    return adj

def girth(Z, edges, conn):
    adj = {z: set() for z in Z}
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    for i, (a, b) in enumerate(conn):
        y = f"_conn{i}"; adj[y] = {a, b}; adj[a].add(y); adj[b].add(y)
    best = None
    for s in adj:
        dist = {s: 0}; parent = {s: None}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; parent[w] = u; dq.append(w)
                elif parent[u] != w:
                    c = dist[u] + dist[w] + 1
                    if best is None or c < best: best = c
    return best

def automorphisms(Z, adj, conn):
    """all permutations of Z preserving Gamma-adjacency and the connector pair multiset (backtracking)."""
    Z = list(Z); n = len(Z); connset = sorted(tuple(sorted(p)) for p in conn)
    cdeg = defaultdict(int)
    for a, b in conn: cdeg[a] += 1; cdeg[b] += 1
    sig = {z: (len(adj[z]), cdeg[z]) for z in Z}
    auts = []
    def rec(i, m, used):
        if i == n:
            if sorted(tuple(sorted((m[a], m[b]))) for a, b in conn) == connset: auts.append(dict(m))
            return
        z = Z[i]
        for w in Z:
            if w in used or sig[w] != sig[z]: continue
            if any(((v in adj[z]) != (m[v] in adj[w])) for v in m): continue
            m[z] = w; used.add(w); rec(i + 1, m, used); del m[z]; used.discard(w)
    rec(0, {}, set())
    return auts

HAND = {
    "H1": (["u", "c1", "c2", "c3", "d1", "d2", "d3"],
           [("u", "c1"), ("u", "c2"), ("u", "c3"), ("c1", "d1"), ("c2", "d2"), ("c3", "d3")], [],
           "big u with three marked neighbours c_i, each with one further marked neighbour d_i (subdivided star)"),
    "H2": (["a", "b", "w", "a1", "a2", "b1", "b2"],
           [("a", "w"), ("b", "w"), ("a", "a1"), ("a", "a2"), ("b", "b1"), ("b", "b2")], [],
           "two non-adjacent big a, b with common marked neighbour w, two further marked neighbours each; NO connector"
           " (a1-b1 connector would close a 6-cycle a1-a-w-b-b1-y)"),
    "H2c": (["a", "b", "w", "a1", "a2", "b1", "b2"],
            [("a", "w"), ("b", "w"), ("a", "a1"), ("a", "a2"), ("b", "b1"), ("b", "b2")], [("a1", "b1")],
            "H2 plus the connector a1-b1: girth 6, OUTSIDE the girth >= 7 habitat (run for information only)"),
    "H3": (["a", "b", "a1", "a2", "b1", "b2"],
           [("a", "b"), ("a", "a1"), ("a", "a2"), ("b", "b1"), ("b", "b2")], [],
           "two adjacent big a ~ b, two further marked neighbours each (isomorphic to case2m2 T2)"),
}

# --------------------------------------------------------------------------- the check
def canon_pattern(part, lines, I, jumps, auts, Ynames):
    """canonical (under Aut) string of a pattern: classes, lines with I, positive jumps."""
    best = None
    for s in auts:
        cl = sorted(tuple(sorted(s[z] for z in b)) for b in part)
        idx = {}
        for i, b in enumerate(part):
            idx[i] = tuple(sorted(s[z] for z in b))
        ls = sorted((tuple(sorted(idx[c] for c in L)), tuple(sorted(s[u] for u in S))) for L, S in zip(lines, I))
        js = sorted((Ynames(y, s), j) for y, j in jumps if j)
        rep = (tuple(cl), tuple(ls), tuple(js))
        if best is None or rep < best: best = rep
    cl, ls, js = best
    cs = " ".join("{" + ",".join(b) + "}" for b in cl)
    lss = "; ".join("[" + " | ".join("{" + ",".join(b) + "}" for b in L) + "] I={" + ",".join(S) + "}" for L, S in ls) or "(no lines)"
    jss = ", ".join(f"{y}:+{j}" for y, j in js)
    return f"classes {cs} ; lines {lss} ; jumps {jss}"

def check_graph(name, Z, edges, conn, comment, args):
    t_start = time.time(); deadline = t_start + args.budget
    print(f"\n=== {name} ===  {comment}")
    adj = build_graph(Z, edges, conn)
    deg = {z: len(adj[z]) for z in Z}
    Big = sorted(z for z in Z if deg[z] >= 3)
    U = {c: frozenset(u for u in Big if u == c or u in adj[c]) for c in Z}
    k = {c: len(U[c]) for c in Z}
    g = girth(Z, edges, conn)
    print(f"|Z|={len(Z)} |E(Gamma)|={len(edges)} connectors={len(conn)} girth(Gamma+connectors)={'inf' if g is None else g}")
    print(f"Big (deg_Gamma >= 3) = {Big}  |Big|={len(Big)}")
    print("k_c: " + ", ".join(f"{c}:{k[c]}" for c in Z))
    if max(k.values()) > 3:
        print(f"SKIPPED: k_c > 3 at {[c for c in Z if k[c] > 3]}")
        return dict(name=name, verdict="SKIPPED (k_c > 3)", Z=len(Z), Big=len(Big), k=k, time=time.time() - t_start)
    if len(Big) > 3:
        print("NOTE: |Big| > 3; the rho = 0 criterion assumes |Big| <= 3, forcing --realise-all")
        args.realise_all = True
    Y = [(y, tuple(sorted(adj[y] | {y}))) for y in Z if y not in Big and deg[y] >= 1]
    Y += [(("conn", a, b), (a, b)) for a, b in conn]
    assert all(len(E) <= 3 for _, E in Y), "some s_y > 3"
    def Ynames(y, s):
        return f"conn({','.join(sorted((s[y[1]], s[y[2]])))})" if isinstance(y, tuple) else s[y]
    print("non-big hyperedges: " + ", ".join(f"E_{Ynames(y, {z: z for z in Z})}={list(E)}" for y, E in Y))
    qpts = draw_points(len(Big), args.seed)
    print("big points q_u: " + ", ".join(f"{u}={p}" for u, p in zip(Big, qpts)))
    dimA = sum(3 - k[c] for c in Z)
    print(f"dim A_q = {dimA};  J3_max over all patterns <= {sum(len(E) - 1 for _, E in Y)}")
    auts = automorphisms(Z, adj, conn)
    print(f"|Aut(Gamma, connectors)| = {len(auts)}")
    Zs = list(Z); nZ = len(Z)
    # ---- pass 1: partitions
    cnt = defaultdict(int)
    cands = []                 # need >= 1: (need, part, UA, lines, J3, jumps, Ilist, M)
    census_cands = []          # need == 0 with rho = 0 possible: (part, UA, lines, J3, jumps, Ilist, M)
    npat_CL = 0                # (C, L) patterns: enumerated, or counted through PLS_COUNT[q] (q >= 8 shortcut)
    npat_CL_unknown = 0        # partitions whose #PLS(q) is not tabulated (q >= 9)
    nJ = 0                     # enumerated (C, L) with J3 >= 1
    nJ_lo = nJ_hi = 0          # bracket for the non-enumerated partitions (q >= 8 shortcut)
    npat_CLI = 0               # (C, L, I) assignments enumerated (spec's basic constraints)
    npat_CLI_pruned = 0        # of those, unrealisable by a closure rule
    enum_capped = False
    for part in SC.set_partitions(Zs):
        if time.time() > deadline: enum_capped = True; break
        cnt["partitions"] += 1
        q = len(part); cls = {z: i for i, b in enumerate(part) for z in b}
        UA = [frozenset().union(*(U[c] for c in b)) for b in part]
        if any(len(u) > 3 for u in UA): cnt["partitions with |U_A| >= 4 (unrealisable)"] += 1; continue
        M = sum(3 - k[c] for c in Zs) - sum(3 - len(u) for u in UA)
        hc = [(len(E), frozenset(cls[z] for z in E)) for _, E in Y]
        Jfix = sum(s - (1 if len(C) == 1 else 2) for s, C in hc if len(C) <= 2)
        trip = [C for s, C in hc if len(C) == 3]
        J3_max = Jfix + len(trip); J3_min = Jfix
        def jumps_of(lines):
            out = []
            for s, C in hc:
                r = 1 if len(C) == 1 else (2 if len(C) == 2 or any(C <= L for L in lines) else 3)
                out.append(s - r)
            return tuple(out)
        if J3_max == 0:
            cnt["partitions with J3 == 0 identically"] += 1
            if q in PLS_COUNT: npat_CL += PLS_COUNT[q]
            else: npat_CL_unknown += 1
            continue
        tier = ("M <= J3_max (need >= 1 possible)" if M <= J3_max else
                "M == J3_max + 1 (slack >= 0 automatic; census)" if M == J3_max + 1 else
                "M >= J3_max + 2 (slack >= 1 automatic)")
        cnt[f"partitions with {tier}"] += 1
        full_enum = (M <= J3_max) or args.realise_all or q <= 7
        if not full_enum:
            # q >= 8 shortcut: count through PLS_COUNT, census by restricted enumeration when M == J3_max + 1
            if q in PLS_COUNT: npat_CL += PLS_COUNT[q]; nJ_hi += PLS_COUNT[q]; nJ_lo += PLS_COUNT[q] if J3_min >= 1 else 0
            else: npat_CL_unknown += 1
            cnt[f"  of which q >= 8, lines not enumerated ({'census by restricted enumeration' if M == J3_max + 1 else 'nothing to do'})"] += 1
            if M == J3_max + 1:
                allowed = [A for A in range(q) if len(UA[A]) >= 2]
                for lines in pls_iter(q, allowed):
                    jumps = jumps_of(lines); J3 = sum(jumps)
                    if J3 != J3_max: continue
                    Ilist, _ = enumerate_I(UA, lines, Big, require_auto=True)
                    if Ilist: census_cands.append((part, UA, lines, J3, jumps, Ilist, M))
            continue
        for lines in pls_iter(q):
            if (npat_CL & 1023) == 0 and time.time() > deadline: enum_capped = True; break
            npat_CL += 1
            jumps = jumps_of(lines); J3 = sum(jumps)
            if J3 == 0: cnt["(C,L) with J3 == 0"] += 1; continue
            nJ += 1
            need = J3 + 1 - M
            if need <= -1: cnt["(C,L) with J3 >= 1 and M >= J3 + 2 (slack >= 1, I not enumerated)"] += 1; continue
            Ilist, pruned = enumerate_I(UA, lines, Big)
            npat_CLI += len(Ilist) + pruned; npat_CLI_pruned += pruned
            if not Ilist:
                cnt["(C,L) with need >= 0 and every I unrealisable by a closure rule" if pruned else
                    "(C,L) with need >= 0 and no I meeting the spec's basic constraints (unrealisable)"] += 1
                continue
            if need == 0 and not args.realise_all:
                auto = [t for t in Ilist if not any(t[1]) and all(len(S) == 2 for S in t[0])]
                cnt["(C,L,I) with need == 0 and rho >= 1 forced (slack >= 1 by the rank argument, not realised)"] += len(Ilist) - len(auto)
                if auto: census_cands.append((part, UA, lines, J3, jumps, auto, M))
                continue
            cands.append((need, part, UA, lines, J3, jumps, Ilist, M))
        if enum_capped: break
    t_enum = time.time() - t_start
    print(f"pass 1 ({t_enum:.1f}s){' CAPPED' if enum_capped else ''}: partitions={cnt['partitions']}")
    for key in sorted(cnt):
        if key != "partitions": print(f"  {key}: {cnt[key]}")
    print(f"  (C,L) patterns counted: {npat_CL}" + (f"  (+ {npat_CL_unknown} partition(s) with q >= 9 whose #PLS is not tabulated)" if npat_CL_unknown else ""))
    print(f"  (C,L) with J3 >= 1: {nJ} among the enumerated" + (f" + between {nJ_lo} and {nJ_hi} among the q >= 8 shortcut partitions" if nJ_hi else ""))
    print(f"  (C,L,I) assignments enumerated (spec's basic constraints): {npat_CLI}; of these unrealisable by closure rules: {npat_CLI_pruned}")
    n_need = sum(len(t[6]) for t in cands); n_cens = sum(len(t[5]) for t in census_cands)
    print(f"  (C,L,I) needing rho (need >= 1{' or 0' if args.realise_all else ''}): {n_need};  census candidates (need == 0, rho = 0 possible): {n_cens}")
    # ---- pass 2: realise
    cands.sort(key=lambda t: (-t[0], len(t[1])))
    memo = {}
    stats = defaultdict(int); min_slack = None; neg = []; tight = defaultdict(list); tight_ex = {}
    unreal_examples = []; false_alarms = 0; unreal_hist = defaultdict(int)
    def run_one(part, UA, lines, J3, jumps, I, X, F, M, need, exhaustive_ok):
        nonlocal min_slack, false_alarms
        q = len(part)
        key = (tuple(tuple(sorted(u)) for u in UA), tuple(tuple(sorted(x)) for x in X), lines_key(lines))
        info = memo.get(key)
        if info is None:
            info = compute_rho(q, lines, UA, X, F, Big, qpts, args.seed, args.order_cap, args.nsucc,
                               exhaustive_ok and q <= 6, deadline)
            memo[key] = info
        if info["status"] != "ok":
            stats["not realised"] += 1
            unreal_hist[(q, len(lines), tuple(sorted(len(L) for L in lines)), tuple(sorted(len(S) for S in I)))] += 1
            if len(unreal_examples) < 6: unreal_examples.append((part, lines_key(lines), I, J3, M, info.get("reason", "")))
            return
        stats["realised"] += 1
        rho = info["rho_min"]; slack = M + rho - (J3 + 1)
        if slack < 0:
            persists = True
            for s in range(1, 6):
                i2 = compute_rho(q, lines, UA, X, F, Big, qpts, args.seed + s, args.order_cap, args.nsucc, q <= 6, deadline)
                if i2["status"] == "ok" and M + i2["rho_min"] - (J3 + 1) >= 0:
                    persists = False; rho = i2["rho_min"]; slack = M + rho - (J3 + 1); break
            if persists: neg.append((part, lines, I, X, J3, jumps, M, rho, info))
            else: false_alarms += 1
        if min_slack is None or slack < min_slack: min_slack = slack
        if slack == 0:
            desc = canon_pattern(part, lines, I, list(zip([y for y, _ in Y], jumps)), auts, Ynames)
            tight[desc].append(1)
            if desc not in tight_ex: tight_ex[desc] = (M, rho, J3)
        stats[f"slack {slack}" if slack <= 2 else "slack >= 3"] += 1
    n_done = 0
    for need, part, UA, lines, J3, jumps, Ilist, M in cands:
        if time.time() > deadline: break
        for I, X, F in Ilist:
            run_one(part, UA, lines, J3, jumps, I, X, F, M, need, True); n_done += 1
    proc_capped = n_done < n_need
    n_cdone = 0
    for part, UA, lines, J3, jumps, Ilist, M in census_cands:
        if time.time() > deadline: break
        for I, X, F in Ilist:
            run_one(part, UA, lines, J3, jumps, I, X, F, M, 0, True); n_cdone += 1
    cens_capped = n_cdone < n_cens
    t_total = time.time() - t_start
    print(f"pass 2: realised {stats['realised']}, not realised {stats['not realised']}"
          f" (need-patterns processed {n_done}/{n_need}{' CAPPED' if proc_capped else ''};"
          f" census candidates processed {n_cdone}/{n_cens}{' CAPPED' if cens_capped else ''});"
          f" special-point false alarms resolved by reseeding: {false_alarms}")
    print("  slack histogram over realised: " + ", ".join(f"{kk}: {stats[kk]}" for kk in sorted(stats) if kk.startswith("slack")))
    print(f"  minimum slack over realised patterns: {min_slack}")
    if unreal_hist:
        print("  not realised, by (q, #lines, line sizes, |I| per line): " +
              ", ".join(f"{k}: {v}" for k, v in sorted(unreal_hist.items())))
    for part, lk, I, J3, M, reason in unreal_examples:
        print(f"  not realised e.g.: classes={part} lines={lk} I={[sorted(S) for S in I]} J3={J3} M={M} {reason}")
    if tight:
        print(f"slack-0 shapes (canonical under Aut; {sum(len(v) for v in tight.values())} patterns, {len(tight)} shapes):")
        for desc, v in sorted(tight.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            M, rho, J3 = tight_ex[desc]
            print(f"  x{len(v):<4} M={M} rho={rho} J3={J3}  {desc}")
    if neg:
        print("NEGATIVE SLACK (persisting over 6 seeds) -- FULL:")
        for part, lines, I, X, J3, jumps, M, rho, info in neg:
            print(f"  classes={part}")
            print(f"  lines={[sorted(L) for L in lines]} I={[sorted(S) for S in I]} X={[sorted(x) for x in X]}")
            print(f"  J3={J3} jumps={dict((Ynames(y, {z: z for z in Z}), j) for (y, _), j in zip(Y, jumps) if j)} M={M} rho={rho} slack={M + rho - J3 - 1}")
            print(f"  big points: " + ", ".join(f"{u}={p}" for u, p in zip(Big, qpts)))
            print(f"  realisation (normals per class): " + ", ".join(f"{part[A]}:{info['pts'][A]}" for A in range(len(part))))
    verdict = "NEGATIVE SLACK FOUND" if neg else ("PASS" if not (enum_capped or proc_capped or cens_capped) else "PASS on processed subset (capped)")
    if stats["not realised"]: verdict += f" [{stats['not realised']} not realised, unverified]"
    print(f"VERDICT: {verdict}   ({t_total:.1f}s)")
    return dict(name=name, verdict=verdict, Z=len(Z), Big=len(Big), k=k, npat_CL=npat_CL, npat_CLI=npat_CLI,
                nJ=nJ, nJ_lo=nJ_lo, nJ_hi=nJ_hi, realised=stats["realised"], unreal=stats["not realised"],
                min_slack=min_slack, neg=len(neg), tight=sum(len(v) for v in tight.values()), shapes=len(tight),
                time=t_total, capped=(enum_capped or proc_capped or cens_capped))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", action="append", help="graph name (case2m2 key or H1/H2/H2c/H3); default: the standard list")
    ap.add_argument("--budget", type=float, default=900.0, help="seconds per graph")
    ap.add_argument("--seed", type=int, default=BASE_SEED)
    ap.add_argument("--order-cap", type=int, default=120)
    ap.add_argument("--nsucc", type=int, default=3)
    ap.add_argument("--realise-all", action="store_true", help="realise every need >= 0 pattern (cross-check of the rho criterion)")
    args = ap.parse_args()
    print(f"case2geo.py  seed {args.seed}  budget/graph {args.budget:.0f}s  order_cap {args.order_cap}  nsucc {args.nsucc}"
          f"  realise_all={args.realise_all}  realisations exact over Q, rho mod 2^61-1")
    default = ["C1", "C1c", "T1", "T1c", "T3", "T2", "H3", "T6", "T7", "H1", "H2", "H2c", "T10", "T11", "T8", "T9"]
    names = args.graph or default
    res = []
    for nm in names:
        if nm in HAND: Z, E, conn, comment = HAND[nm]
        elif nm in CASES: Z, E, conn, comment = CASES[nm]
        else: print(f"unknown graph {nm}"); continue
        res.append(check_graph(nm, Z, E, conn, comment, args))
    print("\n=== SUMMARY ===")
    for r in res:
        if "min_slack" in r:
            print(f"  {r['name']:5} |Z|={r['Z']} |Big|={r['Big']} (C,L)={r['npat_CL']} J3>=1:{r['nJ']}{'+[%d,%d]' % (r['nJ_lo'], r['nJ_hi']) if r['nJ_hi'] else ''} (C,L,I)={r['npat_CLI']}"
                  f" realised={r['realised']} unreal={r['unreal']} min_slack={r['min_slack']} neg={r['neg']}"
                  f" tight={r['tight']}/{r['shapes']} shapes  {r['time']:.1f}s  {r['verdict']}")
        else:
            print(f"  {r['name']:5} |Z|={r['Z']} |Big|={r['Big']} {r['verdict']}")

if __name__ == "__main__":
    main()
