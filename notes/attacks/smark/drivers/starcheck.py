#!/usr/bin/env python3
"""
starcheck.py -- sound pattern-enumeration check of statement (*):

  For every j >= 1,  codim { n in B=(P^3)^Z : J(n) >= j } >= j + 1,
  where  J(n) = sum_y ( s_y - rank{ n_c : c in E_y } ),  E_y = N[y] cap Z,  s_y = |E_y| <= 3.

Method.  The rank pattern of a configuration is (i) a set partition of Z into classes
(equal normals) and (ii) a partial linear space on the classes (which class-triples are
collinear; lines have size >= 3 and meet pairwise in <= 1 class).  J is computed
combinatorially from the pattern.  For each pattern with J >= 1 the codimension of its
locus is lower-bounded SOUNDLY by
      3(|Z| - q) + rho,
where q = number of classes and rho = rank of the Jacobian of all 3x3 minors of the
collinearity constraints at an exact random realisation of the pattern.  Tangent-space
dimension >= local dimension, so rho <= codim at ANY point; rho is computed modulo a
61-bit prime, which is <= the rational rank, hence still a sound lower bound.
Check:  3(|Z|-q) + rho >= J + 1.   Patterns with 3(|Z|-q) > J+1 pass with rho = 0.

Realisation: classes are placed sequentially in an order; a class on exactly one
already-determined line gets a random point of that line; on >= 2 determined lines it is
their intersection (fail if skew); otherwise a random integer point in [-30,30]^4.
The realisation is verified exactly (Fractions) to carry EXACTLY the pattern (all
required equalities/non-equalities and collinearities/non-collinearities).
A pattern that no tried order realises is reported "not realised (cap)" and excluded.
On an apparent violation, 5 fresh seeds are tried; it is reported only if it persists.

Control for workbook attack-smark.md S17(iv) (O7d), written by a helper agent in the
2026-09-23 recovery session and landed by it; run from the repository root:

    timeout 900 python3 notes/attacks/smark/drivers/starcheck.py

Caps, disclosed: |Z| <= 7 on the nine built-in test graphs; realisation coordinates in
[-30, 30]; per line-structure up to 120 placement orders (greedy + random), then 720
exhaustive orders for q <= 6; total 600 s.  A PASS is a check on these graphs over Q, not
a proof of (*).
"""
import sys, time, math, itertools, random
from fractions import Fraction
from collections import deque

T0 = time.time()
TOTAL_CAP = 600.0          # seconds, whole run
BASE_SEED = 20260923
P_MOD = (1 << 61) - 1

def elapsed(): return time.time() - T0
def time_left(): return TOTAL_CAP - elapsed()

# --------------------------------------------------------------------------- linear algebra
def rank_exact(rows):
    M = [[Fraction(x) for x in r] for r in rows]
    if not M: return 0
    n = len(M[0]); m = len(M); r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c] != 0), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        prow = M[r]; pv = prow[c]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c] / pv
                M[i] = [a - f * b for a, b in zip(M[i], prow)]
        r += 1
        if r == m: break
    return r

def rank_mod(rows, p=P_MOD):
    """rank over F_p of an integer matrix; <= rank over Q (sound lower bound)."""
    M = [[x % p for x in r] for r in rows]
    if not M: return 0
    n = len(M[0]); m = len(M); r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c]), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        prow = [(x * inv) % p for x in M[r]]; M[r] = prow
        for i in range(m):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], prow)]
        r += 1
        if r == m: break
    return r

def nullspace_exact(M):
    M = [[Fraction(x) for x in r] for r in M]
    m = len(M); n = len(M[0]); pivcols = []; r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c] != 0), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]; M[r] = [a / pv for a in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        pivcols.append(c); r += 1
        if r == m: break
    free = [c for c in range(n) if c not in pivcols]
    basis = []
    for fc in free:
        x = [Fraction(0)] * n; x[fc] = Fraction(1)
        for i, pc in enumerate(pivcols): x[pc] = -M[i][fc]
        basis.append(x)
    return basis

def to_int_vec(v):
    v = [Fraction(x) for x in v]
    L = 1
    for x in v: L = L * x.denominator // math.gcd(L, x.denominator)
    w = [int(x * L) for x in v]
    g = 0
    for x in w: g = math.gcd(g, abs(x))
    if g > 1: w = [x // g for x in w]
    return w

def proportional(u, v):
    return rank_exact([u, v]) < 2

# --------------------------------------------------------------------------- patterns
def set_partitions(elems):
    n = len(elems)
    def rec(i, blocks):
        if i == n:
            yield [tuple(b) for b in blocks]; return
        for b in blocks:
            b.append(elems[i]); yield from rec(i + 1, blocks); b.pop()
        blocks.append([elems[i]]); yield from rec(i + 1, blocks); blocks.pop()
    yield from rec(0, [])

_PLS = {}
def PLS(q):
    """all partial linear spaces on {0..q-1}: sets of lines (size>=3), pairwise meeting in <=1."""
    if q not in _PLS:
        cands = [frozenset(s) for k in range(3, q + 1) for s in itertools.combinations(range(q), k)]
        n = len(cands)
        compat = [[len(cands[i] & cands[j]) <= 1 for j in range(n)] for i in range(n)]
        out = []
        def rec(start, chosen):
            out.append(tuple(cands[i] for i in chosen))
            for j in range(start, n):
                if all(compat[j][i] for i in chosen):
                    chosen.append(j); rec(j + 1, chosen); chosen.pop()
        rec(0, [])
        _PLS[q] = out
    return _PLS[q]

def lines_key(lines):
    return tuple(sorted(tuple(sorted(L)) for L in lines))

# --------------------------------------------------------------------------- realisation
def rand_vec(rng, avoid):
    for _ in range(50):
        v = [rng.randint(-30, 30) for _ in range(4)]
        if any(v) and not any(proportional(v, w) for w in avoid):
            return v
    return None

def realise(q, lines, order, rng):
    pts = [None] * q
    for c in order:
        placed = [w for w in pts if w is not None]
        det = []
        for L in lines:
            if c in L:
                on = [pts[d] for d in L if d != c and pts[d] is not None]
                if len(on) >= 2: det.append(on)
        if not det:
            v = rand_vec(rng, placed)
            if v is None: return None
        elif len(det) == 1:
            p1, p2 = det[0][0], det[0][1]
            v = None
            for _ in range(50):
                a, b = rng.randint(-30, 30), rng.randint(-30, 30)
                if a == 0 and b == 0: continue
                w = [a * x + b * y for x, y in zip(p1, p2)]
                if any(w) and not any(proportional(w, u) for u in placed):
                    v = w; break
            if v is None: return None
        else:
            base = det[0]; v = None
            for other in det[1:]:
                ns = nullspace_exact([[base[0][i], base[1][i], -other[0][i], -other[1][i]] for i in range(4)])
                if len(ns) != 1: return None            # skew (0) or coincident (2) lines
                a, b = ns[0][0], ns[0][1]
                w = to_int_vec([a * x + b * y for x, y in zip(base[0], base[1])])
                if not any(w): return None
                if v is None: v = w
                elif proportional(v, w) is False: return None
            if any(proportional(v, u) for u in placed): return None
        pts[c] = v
    return pts

def verify(q, lines, pts):
    """pts carries EXACTLY the pattern: classes distinct, lines collinear, other triples rank 3."""
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
    return True

def jac_rank(q, lines, pts):
    """rank (mod p) of the Jacobian of all 3x3 minors of the 4 x |L| matrices, one per line."""
    rows = []
    for L in lines:
        Ls = sorted(L)
        for C in itertools.combinations(Ls, 3):
            for R in itertools.combinations(range(4), 3):
                grad = [0] * (4 * q)
                for ri, i in enumerate(R):
                    Rm = [x for x in R if x != i]
                    for ci, c in enumerate(C):
                        Cm = [x for x in C if x != c]
                        d2 = pts[Cm[0]][Rm[0]] * pts[Cm[1]][Rm[1]] - pts[Cm[1]][Rm[0]] * pts[Cm[0]][Rm[1]]
                        grad[4 * c + i] = (-1) ** (ri + ci) * d2
                rows.append(grad)
    return rank_mod(rows)

def greedy_order(q, lines, rng):
    placed = set(); order = []
    while len(order) < q:
        rem = [c for c in range(q) if c not in placed]
        def ndet(c):
            return sum(1 for L in lines if c in L and sum(1 for d in L if d != c and d in placed) >= 2)
        sc = [(c, ndet(c)) for c in rem]
        ones = [c for c, k in sc if k == 1]; zeros = [c for c, k in sc if k == 0]
        c = rng.choice(ones) if ones else (rng.choice(zeros) if zeros else rng.choice(rem))
        order.append(c); placed.add(c)
    return order

def compute_rho(q, lines, seed, order_cap, nsucc, exhaustive):
    key = lines_key(lines)
    rng = random.Random(f"{seed}:{q}:{key}")
    if not lines:
        return dict(status="ok", rho_min=0, rho_max=0, nsucc=1, tried=0, orders=[])
    results = []; tried_orders = set(); tried = [0]
    def attempt(order):
        tried[0] += 1
        for _ in range(2):                     # one retry for accidental coincidences
            pts = realise(q, lines, order, rng)
            if pts is None: continue
            if verify(q, lines, pts):
                results.append((jac_rank(q, lines, pts), tuple(order))); return True
        return False
    for _ in range(8):
        if len(results) >= nsucc: break
        o = greedy_order(q, lines, rng); t = tuple(o)
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
            if time_left() < 3: break
    if not results:
        return dict(status="unrealised", tried=tried[0], orders=[])
    rhos = [r for r, _ in results]
    return dict(status="ok", rho_min=min(rhos), rho_max=max(rhos), nsucc=len(results),
                tried=tried[0], orders=[o for _, o in results])

# --------------------------------------------------------------------------- graphs
class Graph:
    def __init__(self): self.adj = {}
    def add_edge(self, u, v):
        assert u != v
        self.adj.setdefault(u, set()).add(v); self.adj.setdefault(v, set()).add(u)
    def add_path(self, start, length, prefix):
        prev = start
        for i in range(length):
            v = f"{prefix}{i+1}"; self.add_edge(prev, v); prev = v
        return prev
    def girth(self):
        best = None
        for s in self.adj:
            dist = {s: 0}; parent = {s: None}; dq = deque([s])
            while dq:
                u = dq.popleft()
                for w in self.adj[u]:
                    if w not in dist:
                        dist[w] = dist[u] + 1; parent[w] = u; dq.append(w)
                    elif parent[u] != w:
                        c = dist[u] + dist[w] + 1
                        if best is None or c < best: best = c
        return best

def hub_path(k):
    G = Graph(); hubs = [f"z{i}" for i in range(1, k + 1)]
    for i in range(k - 1): G.add_edge(hubs[i], hubs[i + 1])
    for i, h in enumerate(hubs):
        for j in range(2 if i in (0, k - 1) else 1): G.add_path(h, 3, f"{h}p{j}_")
    return G, hubs

def hub_cycle(k=7):
    G = Graph(); hubs = [f"h{i}" for i in range(k)]
    for i in range(k): G.add_edge(hubs[i], hubs[(i + 1) % k])
    for h in hubs: G.add_path(h, 3, f"{h}p_")
    return G, hubs

def two_paths_joined():
    G = Graph(); zs = ["z1", "z2", "z3"]; ws = ["w1", "w2", "w3"]
    for P in (zs, ws):
        G.add_edge(P[0], P[1]); G.add_edge(P[1], P[2])
        for h in (P[0], P[2]):
            for j in range(2): G.add_path(h, 3, f"{h}p{j}_")
    end = G.add_path("z2", 3, "c"); G.add_edge(end, "w2")     # z2-c1-c2-c3-w2 : length 4
    return G, zs + ws

def theta():
    G = Graph()
    for nm in "abc":
        end = G.add_path("u", 3, nm); G.add_edge(end, "v")       # u-x1-x2-x3-v : length 4
    G.add_path("a2", 3, "m")                                       # pendant makes a2 a hub
    return G, ["u", "v", "a2"]

def subdivided(edges, hubs):
    G = Graph()
    for a, b in edges:
        end = G.add_path(a, 2, f"s_{a}{b}_"); G.add_edge(end, b)  # a-s1-s2-b : length 3
    return G, hubs

def sub_K4():
    V = list("abcd"); return subdivided(list(itertools.combinations(V, 2)), V)
def sub_K33():
    A = ["a1", "a2", "a3"]; B = ["b1", "b2", "b3"]
    return subdivided([(a, b) for a in A for b in B], A + B)

# --------------------------------------------------------------------------- the check
def check_graph(name, G, hubs, budget, order_cap, nsucc, exhaustive):
    t_start = time.time(); deadline = t_start + budget
    print(f"\n=== {name} ===")
    V = sorted(G.adj); nE = sum(len(a) for a in G.adj.values()) // 2
    g = G.girth()
    print(f"|V|={len(V)} |E|={nE} girth={'inf (acyclic)' if g is None else g}")
    assert g is None or g >= 7, "girth < 7"
    Z = sorted(v for v in V if len(G.adj[v]) >= 3)
    assert set(Z) == set(hubs), (Z, hubs)
    Zs = set(Z); nZ = len(Z)
    E = {y: tuple(sorted((set(G.adj[y]) | {y}) & Zs)) for y in V}
    assert all(len(e) <= 3 for e in E.values()), "some s_y > 3"
    hyper = [(y, E[y]) for y in V if len(E[y]) >= 2]
    print(f"Z (hubs), |Z|={nZ}: {Z}")
    print("hyperedges with s_y >= 2:" + ("" if hyper else "  (none)"))
    for y, e in hyper: print(f"  E_{y} = {list(e)}   (s={len(e)})")
    # girth-7 overlap facts
    ok = True; ys = [y for y in V if E[y]]
    for y1, y2 in itertools.combinations(ys, 2):
        I = set(E[y1]) & set(E[y2])
        if len(I) > 2: ok = False; print(f"  OVERLAP FAIL |E∩E'|>2: {y1},{y2}: {I}")
        elif len(I) == 2:
            if not (y1 in Zs and y2 in Zs and y2 in G.adj[y1] and I == {y1, y2}):
                ok = False; print(f"  OVERLAP FAIL: {y1},{y2}: {I}")
    print(f"overlap facts (|E_y∩E_y'|<=2, =2 only for adjacent marked y~y' with E∩E'={{y,y'}}): {'OK' if ok else 'FAIL'}")
    maxJ = sum(len(e) - 1 for _, e in hyper)
    if maxJ == 0:
        print("all s_y <= 1  ==>  J == 0 identically; (*) is vacuous for this graph.")
        print("VERDICT: VACUOUS (nothing to check)")
        return "VACUOUS"
    # pass 1: enumerate patterns, compute J
    n_part = n_pat = n_patJ = n_triv = 0
    cands = []
    for part in set_partitions(Z):
        n_part += 1; q = len(part)
        cls = {z: i for i, b in enumerate(part) for z in b}
        hc = [(len(e), frozenset(cls[z] for z in e)) for _, e in hyper]
        for lines in PLS(q):
            n_pat += 1
            jumps = []
            for s, C in hc:
                k = len(C)
                r = 1 if k == 1 else (2 if k == 2 else (2 if any(C <= L for L in lines) else 3))
                jumps.append(s - r)
            J = sum(jumps)
            if J == 0: continue
            n_patJ += 1
            need = J + 1 - 3 * (nZ - q)             # need rho >= need
            if need < 0: n_triv += 1; continue      # deficit <= -1 already with rho = 0
            cands.append((need, q, lines, tuple(jumps), part))
    print(f"partitions={n_part}  patterns={n_pat}  patterns with J>=1: {n_patJ}  "
          f"trivially OK (3(|Z|-q) > J+1): {n_triv}  need rho: {len(cands)}")
    # pass 2: most demanding first
    cands.sort(key=lambda t: (-t[0], t[1]))
    memo = {}
    n_done = n_real = n_unreal = 0
    max_def = None; tight = []; violations = []; false_alarms = 0
    unreal_examples = []
    for need, q, lines, jumps, part in cands:
        if time.time() > deadline or time_left() < 2:
            break
        key = (q, lines_key(lines))
        info = memo.get(key)
        if info is None:
            info = compute_rho(q, lines, BASE_SEED, order_cap, nsucc, exhaustive)
            memo[key] = info
        n_done += 1
        J = sum(jumps)
        if info["status"] == "unrealised":
            n_unreal += 1
            if len(unreal_examples) < 3: unreal_examples.append((part, lines_key(lines), J))
            continue
        n_real += 1
        rho = info["rho_min"]
        deficit = need - rho                          # (J+1) - (3(|Z|-q)+rho); must be <= 0
        if deficit > 0:
            persists = True
            for s in range(1, 6):
                i2 = compute_rho(q, lines, BASE_SEED + s, order_cap, nsucc, exhaustive)
                if i2["status"] == "ok" and need - i2["rho_min"] <= 0:
                    persists = False; rho = i2["rho_min"]; deficit = need - rho; break
            if persists:
                violations.append((part, lines_key(lines), J, jumps, rho, info["rho_max"], deficit))
            else:
                false_alarms += 1
        if max_def is None or deficit > max_def: max_def = deficit
        if deficit == 0 and len(tight) < 4: tight.append((part, lines_key(lines), J, jumps, rho))
    full = (n_done == len(cands))
    print(f"processed {n_done}/{len(cands)} rho-needing patterns ({'FULL' if full else 'PARTIAL, time cap'});"
          f" distinct line-structures realised: {sum(1 for v in memo.values() if v['status']=='ok')},"
          f" not realised: {sum(1 for v in memo.values() if v['status']!='ok')}")
    print(f"realised patterns checked: {n_real}; patterns not realised (cap, excluded): {n_unreal}; "
          f"special-point false alarms resolved by reseeding: {false_alarms}")
    for part, lk, J in unreal_examples:
        print(f"  not realised e.g.: classes={part} lines={lk} J={J}")
    if max_def is not None:
        print(f"max over realised patterns of (J+1) - (3(|Z|-q)+rho) = {max_def}   (must be <= 0;"
              f" the {n_triv} trivially-OK patterns have it <= -1)")
    print(f"tight patterns (deficit 0), examples (up to 4):")
    hy = [y for y, _ in hyper]
    for part, lk, J, jumps, rho in tight:
        q = len(part)
        print(f"  classes={part} lines={lk} q={q} J={J} rho={rho} codim>= {3*(nZ-q)+rho}")
        print(f"    per-hyperedge jumps: " + ", ".join(f"E_{y}:{j}" for y, j in zip(hy, jumps) if j))
    if violations:
        print("VIOLATIONS (persisting over 6 seeds):")
        for part, lk, J, jumps, rho, rmax, d in violations:
            q = len(part)
            print(f"  classes={part} lines={lk} q={q} J={J} rho_min={rho} rho_max={rmax} "
                  f"codim>= {3*(nZ-q)+rho} < J+1={J+1}  deficit={d}")
            print(f"    per-hyperedge jumps: " + ", ".join(f"E_{y}:{j}" for y, j in zip(hy, jumps) if j))
        verdict = "VIOLATION"
    else:
        verdict = "PASS" if full else "PASS on processed subset (time cap)"
        if n_unreal: verdict += f" [{n_unreal} pattern(s) not realised, unverified]"
    print(f"VERDICT: {verdict}   ({time.time()-t_start:.1f}s)")
    return verdict

# --------------------------------------------------------------------------- sanity of rho
def sanity():
    print("=== rho sanity (expected codims of standard line configurations) ===")
    tests = [
        ("one line of 3 (codim 2)", 3, [{0, 1, 2}]),
        ("one line of 4 (codim 4)", 4, [{0, 1, 2, 3}]),
        ("one line of 5 (codim 6)", 5, [{0, 1, 2, 3, 4}]),
        ("two disjoint 3-lines (codim 4)", 6, [{0, 1, 2}, {3, 4, 5}]),
        ("two 3-lines sharing a point (codim 4)", 5, [{0, 1, 2}, {0, 3, 4}]),
        ("triangle, 3 lines (codim 6)", 6, [{0, 1, 2}, {0, 3, 4}, {1, 3, 5}]),
        ("complete quadrilateral, 4 lines (codim 7)", 6, [{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]),
        ("complete quadrangle, 6 lines on 7 pts (codim ?)", 7,
         [{0, 1, 4}, {2, 3, 4}, {0, 2, 5}, {1, 3, 5}, {0, 3, 6}, {1, 2, 6}]),
        ("Fano plane (unrealisable over Q)", 7,
         [{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]),
    ]
    for nm, q, lines in tests:
        lines = [frozenset(L) for L in lines]
        info = compute_rho(q, lines, BASE_SEED, order_cap=200, nsucc=3, exhaustive=(q <= 6))
        if info["status"] == "ok":
            print(f"  {nm}: rho_min={info['rho_min']} rho_max={info['rho_max']} (succ {info['nsucc']}, tried {info['tried']})")
        else:
            print(f"  {nm}: not realised (tried {info['tried']} orders)")

def main():
    print(f"starcheck.py  total cap {TOTAL_CAP:.0f}s  base seed {BASE_SEED}  rho computed mod 2^61-1 (<= Q-rank, sound)")
    sanity()
    for q in range(1, 8): print(f"#PLS({q}) = {len(PLS(q))}", end="  ")
    print()
    results = []
    small = [(f"1. hub path k={k}", *hub_path(k)) for k in (3, 4, 5, 6)]
    small += [("3. two hub paths joined by non-hub path of length 4", *two_paths_joined()),
              ("4. theta (paths 4,4,4) with extra hub", *theta()),
              ("5. subdivided K4 (edges -> paths of length 3)", *sub_K4()),
              ("6. subdivided K_{3,3} (edges -> paths of length 3)", *sub_K33())]
    for name, G, hubs in small:
        budget = min(120.0, max(5.0, time_left() - 60.0))
        results.append((name, check_graph(name, G, hubs, budget, order_cap=120, nsucc=3, exhaustive=True)))
    name = "2. hub cycle C_7 (|Z|=7)"; G, hubs = hub_cycle(7)
    budget = max(5.0, time_left() - 5.0)
    results.append((name, check_graph(name, G, hubs, budget, order_cap=60, nsucc=1, exhaustive=False)))
    print("\n=== SUMMARY ===")
    for nm, v in results: print(f"  {nm}: {v}")
    print(f"total time {elapsed():.1f}s")

if __name__ == "__main__":
    main()
