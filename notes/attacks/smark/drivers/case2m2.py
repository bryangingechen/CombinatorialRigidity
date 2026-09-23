#!/usr/bin/env python3
"""case2m2.py -- geometric control for O7e (smark session 9, workbook S21).

Builds the *reduced* closed incidence variety X(Gamma, conn) of a habitat side and asks Macaulay2 for its
minimal primes.  Reduced structure (S21): marked vertices Z carry a flag (p_c, pi_c), p_c in pi_c; for every
hub-hub edge c ~ d: p_d in pi_c and p_c in pi_d; for every connector (unmarked y with N(y) = {a, b} in Z) a
point p_y in pi_a and pi_b.  Unmarked vertices on longer paths add constant-dimension free fibres and are
dropped (they cannot change the component count).  The flag of the first marked vertex is fixed and the other
blocks use standard charts; both steps are faithful for component counts (docstring of m2_script).  Arithmetic: exact,
over ZZ/32003 (a char-p control of a characteristic-free statement; caps in README).

Expected dimension (S16(iv)/S21): 5|Z| - 2|E(Gamma)| + #conn, minus 5 for the fixed flag.  PASS = one minimal prime, of that dimension.

    timeout 900 python3 notes/attacks/smark/drivers/case2m2.py            # all named cases
    timeout 300 python3 notes/attacks/smark/drivers/case2m2.py --case T1  # one case
"""
import sys, subprocess, random, argparse, tempfile, os, time

# name: (Z, Gamma edges, connectors as (a, b) pairs, comment)
def star(center, leaves):
    return [(center, l) for l in leaves]

CASES = {
    # negative controls (outside the habitat: short cycles) -- expected to FAIL
    "N3": (["a", "b", "c"], [("a", "b"), ("b", "c"), ("a", "c")], [], "NEGATIVE control: hub triangle (girth 3)"),
    "N4": (["a", "b", "c", "d"], [("a", "b"), ("b", "c"), ("c", "d"), ("a", "d")], [], "NEGATIVE control: hub 4-cycle"),
    "NK4": (["a", "b", "c", "d"], [(x, y) for i, x in enumerate("abcd") for y in "abcd"[i + 1:]], [], "NEGATIVE control: K4 of hubs"),
    # Case 1 sanity: hub path with a connector-free structure
    "C1": (["a", "b", "c"], [("a", "b"), ("b", "c")], [], "Case-1 hub path P3 (control)"),
    "C1c": (["a", "b", "c", "d"], [("a", "b"), ("c", "d")], [("b", "c")], "Case-1: two hub edges joined by a connector"),
    # Case 2
    "T1": (["z", "a", "b", "c"], star("z", "abc"), [], "K_{1,3}: the starcomb --case2 6 side, reduced"),
    "T1c": (["z", "a", "b", "c", "d"], star("z", "abc"), [("c", "d")], "K_{1,3} plus a connector from a leaf to a far hub"),
    "T3": (["z", "a", "b", "c", "d"], star("z", "abcd"), [], "K_{1,4}: one hub with four hub neighbours (s = 5)"),
    "T2": (["u", "v", "a", "b", "c", "d"], [("u", "v")] + star("u", "ab") + star("v", "cd"), [],
           "double star: two ADJACENT big hubs, each with two further hub neighbours"),
    "T6": (["u", "x", "v", "a", "b", "c", "d"], star("x", "uv") + star("u", "ab") + star("v", "cd"), [],
           "two big hubs at distance 2 through a hub x (k_x = 2)"),
    "T7": (["u", "v", "a", "b", "c", "d", "e"], star("u", "abe") + star("v", "cde"), [],
           "two big hubs sharing a hub neighbour e (k_e = 2, e is non-big)"),
    "T8": (["u", "v", "w", "a", "b", "c", "d", "e", "f"], [("u", "v"), ("v", "w")] + star("u", "ab") + star("v", "c") + star("w", "de") , [],
           "path of three big hubs u - v - w (k_v = 3)"),
    "T9": (["c", "z1", "z2", "z3", "a1", "b1", "a2", "b2", "a3", "b3"],
           star("c", ["z1", "z2", "z3"]) + star("z1", ["a1", "b1"]) + star("z2", ["a2", "b2"]) + star("z3", ["a3", "b3"]), [],
           "spider: big c with three big neighbours (k_c = 4) -- the three-level order fails here"),
    "T10": ([f"c{i}" for i in range(1, 8)] + ["x"], [(f"c{i}", f"c{i % 7 + 1}") for i in range(1, 8)] + [("c1", "x")], [],
            "hub 7-cycle with a pendant hub: one big vertex on a cycle"),
    "T11": ([f"c{i}" for i in range(1, 7)] + ["x", "y"], [(f"c{i}", f"c{i + 1}") for i in range(1, 6)] + [("c1", "x"), ("c4", "y")],
            [("c1", "c6")], "hub path closed by a connector into an 8-cycle, two big vertices c1, c4 on it"),
    # session 11 (O7e-b control): two big hubs at Gamma-distance >= 3, so no plane sees both -- the
    # single-relation stratum q_u = q_v of state.md *Where it breaks* lives inside these varieties.
    "D3": (["u", "p", "r", "v", "a", "b", "c", "d"], [("u", "p"), ("p", "r"), ("r", "v")] + star("u", "ab") + star("v", "cd"), [],
           "two big hubs u, v at distance 3 (path u-p-r-v), two leaves each"),
    "D3c": (["u", "p", "r", "v", "a", "b", "c", "d"], [("u", "p"), ("p", "r"), ("r", "v")] + star("u", "ab") + star("v", "cd"), [("a", "c")],
            "D3 plus a connector a-c closing a 7-cycle through both big hubs"),
    "D4": (["u", "p", "r", "s", "v", "a", "b", "c", "d"], [("u", "p"), ("p", "r"), ("r", "s"), ("s", "v")] + star("u", "ab") + star("v", "cd"), [],
           "two big hubs u, v at distance 4 (path u-p-r-s-v), two leaves each"),
    # session 11 (S25(vi)): graphs carrying the damage shapes of the single-coincidence ledger --
    # O3 = u-w1-w2-v (two degree-2 hubs), O1 = u-c-z-c2-v (a bad-pair candidate), O5 = u-w-a-w2-v (a big).
    "E13": (["u", "v", "w1", "w2", "c", "z", "c2", "x", "y"],
            [("u", "w1"), ("w1", "w2"), ("w2", "v"), ("u", "c"), ("c", "z"), ("z", "c2"), ("c2", "v"), ("u", "x"), ("v", "y")], [],
            "O3 + O1: big u, v joined by a 3-path and a 4-path, one leaf each (girth 7)"),
    "E15": (["u", "v", "c", "z", "c2", "w", "a", "w2", "la", "x", "y"],
            [("u", "c"), ("c", "z"), ("z", "c2"), ("c2", "v"), ("u", "w"), ("w", "a"), ("a", "w2"), ("w2", "v"), ("a", "la"), ("u", "x"), ("v", "y")], [],
            "O1 + O5: big u, v joined by a 4-path and a 4-path through a third big hub a (girth 8)"),
    "E55": (["u", "v", "w", "a", "w2", "w3", "b", "w4", "la", "lb", "x", "y"],
            [("u", "w"), ("w", "a"), ("a", "w2"), ("w2", "v"), ("u", "w3"), ("w3", "b"), ("b", "w4"), ("w4", "v"), ("a", "la"), ("b", "lb"), ("u", "x"), ("v", "y")], [],
            "O5 + O5: big u, v joined by two 4-paths through big hubs a, b (girth 8)"),
    # S27(i): the O6 shape (a length-3 u-v path through a big vertex r and a flat singleton p) -- D3 with a leaf at r.
    "D3r": (["u", "p", "r", "v", "a", "b", "c", "d", "lr"], [("u", "p"), ("p", "r"), ("r", "v")] + star("u", "ab") + star("v", "cd") + [("r", "lr")], [],
            "D3 with r made big by a leaf: u-p-r-v is an O6 path (S25(ii)(L6))"),
}

def m2_script(Z, E, conn, seed):
    """Gauge-fixed standard charts.  X is PGL_4-invariant and PGL_4 is connected, so every component is
    invariant.  Fix the flag of the first marked vertex a: p_a = e0, pi_a = {x3 = 0}; X = PGL_4 x_Stab F with
    Stab (a parabolic) connected, so components of X <-> components of the fibre F.  Charts for the other
    blocks: points x0 = 1, normals n3 = 1.  Each Stab-invariant closed subset of P^3 ({p_a}, pi_a, P^3) meets
    {x0 != 0}; of P^3* ({pi_a}, planes through p_a, P^3*) meets {n3 != 0}; so every component of F meets the
    product of charts.  Dimension reported is dim F = expected - 5.  (seed unused: the charts are canonical.)"""
    a0 = Z[0]
    blocks = []
    for c in Z: blocks += ["p" + c, "n" + c]
    for i, _ in enumerate(conn): blocks.append(f"q{i}")
    coord, allv = {}, []
    for b in blocks:
        if b == "p" + a0: coord[b] = ["1", "0", "0", "0"]; continue
        if b == "n" + a0: coord[b] = ["0", "0", "0", "1"]; continue
        t = [f"{b}t{j}" for j in range(1, 4)]; allv += t
        coord[b] = ["1"] + t if b[0] in "pq" else t + ["1"]
    def dot(x, y):
        terms = []
        for u, v in zip(coord[x], coord[y]):
            if u == "0" or v == "0": continue
            terms.append(u if v == "1" else v if u == "1" else f"{u}*{v}")
        return " + ".join(terms) if terms else "0"
    gens = []
    for c in Z: gens.append(dot("p" + c, "n" + c))
    for c, d in E:
        gens.append(dot("p" + d, "n" + c)); gens.append(dot("p" + c, "n" + d))
    for i, (x, y) in enumerate(conn):
        gens.append(dot(f"q{i}", "n" + x)); gens.append(dot(f"q{i}", "n" + y))
    gens = [g for g in gens if g != "0"]
    s = f"R = ZZ/32003[{', '.join(allv)}];\n"
    s += "I = ideal(" + ",\n  ".join(gens) + ");\n"
    s += 'print("DIMI " | toString(dim I));\n'
    s += "P = minimalPrimes I;\n"
    s += 'print("NPRIMES " | toString(#P));\n'
    s += 'scan(P, Q -> print("DIM " | toString(dim Q)));\n'
    s += "exit 0\n"
    return s

def m2_script_reduced(Z, E, conn, seed, timed=False):
    """The SAME chart variety as m2_script, with the two linear-in-one-variable incidences of every spanning-tree
    edge solved exactly (session 11, S27(iv)).  Root the tree at Z[0] (flag fixed as in m2_script).  For a vertex c
    with tree parent d: p_c = (1, x1, x2, X3) with X3 := -(n_d0 + n_d1 x1 + n_d2 x2) (p_c in pi_d; the chart n_d3 = 1
    makes this exact), and n_c = (N0, y1, y2, 1) with N0 := -(y1 x1 + y2 x2 + X3) (p_c in pi_c; the chart p_c0 = 1
    makes this exact); the tree edge leaves ONE equation n_c . p_d = 0.  A non-tree edge keeps its two bilinear
    equations; a connector q between x, y is (1, q1, q2, Q3) with Q3 from q in pi_x and one equation q in pi_y.
    Variables 4 per non-root vertex + 2 per connector (m2_script: 6 and 3); equations |E| + #conn + #(non-tree
    edges) (m2_script: 2|E| + 2#conn).  Isomorphic to m2_script's chart variety, so the expected dimension and the
    faithfulness argument are unchanged."""
    from collections import deque
    a0 = Z[0]
    adj = {c: [] for c in Z}
    for c, d in E: adj[c].append(d); adj[d].append(c)
    parent, order, seen = {}, [a0], {a0}
    dq = deque([a0])
    while dq:
        d = dq.popleft()
        for c in adj[d]:
            if c not in seen: seen.add(c); parent[c] = d; order.append(c); dq.append(c)
    assert len(order) == len(Z), "hub graph must be connected"
    tree_edges = {frozenset((c, parent[c])) for c in parent}
    allv, P, N = [], {}, {}
    P[a0] = ["1", "0", "0", "0"]; N[a0] = ["0", "0", "0", "1"]
    def dot(x, y):
        terms = [f"({u})*({v})" for u, v in zip(x, y) if u != "0" and v != "0"]
        return " + ".join(terms) if terms else "0"
    gens = []
    for c in order[1:]:
        d = parent[c]
        x1, x2, y1, y2 = f"p{c}t1", f"p{c}t2", f"n{c}t1", f"n{c}t2"
        allv += [x1, x2, y1, y2]
        nd = N[d]
        X3 = f"-(({nd[0]}) + ({nd[1]})*{x1} + ({nd[2]})*{x2})"
        P[c] = ["1", x1, x2, X3]
        N0 = f"-({y1}*{x1} + {y2}*{x2} + ({X3}))"
        N[c] = [N0, y1, y2, "1"]
        gens.append(dot(N[c], P[d]))                       # p_d in pi_c
    for c, d in E:
        if frozenset((c, d)) in tree_edges: continue
        gens.append(dot(N[c], P[d])); gens.append(dot(N[d], P[c]))
    for i, (x, y) in enumerate(conn):
        q1, q2 = f"q{i}t1", f"q{i}t2"; allv += [q1, q2]
        nx = N[x]
        Q3 = f"-(({nx[0]}) + ({nx[1]})*{q1} + ({nx[2]})*{q2})"
        gens.append(dot(N[y], ["1", q1, q2, Q3]))
    gens = [g for g in gens if g != "0"]
    s = f"R = ZZ/32003[{', '.join(allv)}];\n"
    s += "I = ideal(" + ",\n  ".join(gens) + ");\n"
    et = "elapsedTime " if timed else ""
    if timed:
        s += 'elapsedTime G = gb I;\nprint("GBDONE " | toString(numgens source gens G));\n'
    s += f'{et}print("DIMI " | toString(dim I));\n'
    s += f"{et}P = minimalPrimes I;\n"
    s += 'print("NPRIMES " | toString(#P));\n'
    s += 'scan(P, Q -> print("DIM " | toString(dim Q)));\n'
    s += "exit 0\n"
    return s

def m2_script_jumpdims(Z, E, conn, seed):
    """Irreducibility as a dimension test, no primary decomposition (session 11, S27(v)).  The tower's generic
    stratum G -- every point set U_c independent (r_c = k_c) and every non-big hyperedge's planes independent
    (rk_y = s_y) -- is an open dense irreducible subset of the main component (a tower of projective bundles over an
    open subset of (P^3)^Big), so every other component of X lies in the union of the JUMP loci and has dimension
    >= expdim by Krull; hence X is irreducible iff dim(X cap {rank drop at h}) <= expdim - 1 for every hyperedge h.
    Each such locus is I plus the s x s minors of the s coordinate vectors of h (points of U_c for a marked c with
    k_c >= 2; normals at a non-big marked y with s_y = |N_Gamma[y]| >= 2; the two normals of a connector).  Prints
    "JUMP <h> <s> <dim>" per hyperedge in the reduced chart coordinates of m2_script_reduced (expdim - 5 there), and
    "MAXJUMP <max>".  PASS iff MAXJUMP <= expected - 1."""
    from collections import deque
    from itertools import combinations
    a0 = Z[0]
    adj = {c: [] for c in Z}
    for c, d in E: adj[c].append(d); adj[d].append(c)
    deg = {c: len(adj[c]) for c in Z}
    big = {c for c in Z if deg[c] >= 3}
    parent, order, seen = {}, [a0], {a0}
    dq = deque([a0])
    while dq:
        d = dq.popleft()
        for c in adj[d]:
            if c not in seen: seen.add(c); parent[c] = d; order.append(c); dq.append(c)
    tree_edges = {frozenset((c, parent[c])) for c in parent}
    allv, P, N = [], {}, {}
    P[a0] = ["1", "0", "0", "0"]; N[a0] = ["0", "0", "0", "1"]
    def dot(x, y):
        terms = [f"({u})*({v})" for u, v in zip(x, y) if u != "0" and v != "0"]
        return " + ".join(terms) if terms else "0"
    gens = []
    for c in order[1:]:
        d = parent[c]
        x1, x2, y1, y2 = f"p{c}t1", f"p{c}t2", f"n{c}t1", f"n{c}t2"
        allv += [x1, x2, y1, y2]
        nd = N[d]
        X3 = f"-(({nd[0]}) + ({nd[1]})*{x1} + ({nd[2]})*{x2})"
        P[c] = ["1", x1, x2, X3]
        N[c] = [f"-({y1}*{x1} + {y2}*{x2} + ({X3}))", y1, y2, "1"]
        gens.append(dot(N[c], P[d]))
    for c, d in E:
        if frozenset((c, d)) in tree_edges: continue
        gens.append(dot(N[c], P[d])); gens.append(dot(N[d], P[c]))
    Q = {}
    for i, (x, y) in enumerate(conn):
        q1, q2 = f"q{i}t1", f"q{i}t2"; allv += [q1, q2]
        nx = N[x]
        Q[i] = ["1", q1, q2, f"-(({nx[0]}) + ({nx[1]})*{q1} + ({nx[2]})*{q2})"]
        gens.append(dot(N[y], Q[i]))
    gens = [g for g in gens if g != "0"]
    # hyperedges: (name, list of coordinate vectors)
    hyper = []
    for c in Z:
        U = [u for u in [c] + adj[c] if u in big]
        if len(U) >= 2: hyper.append((f"pts_{c}", [P[u] for u in U]))
    for y in Z:
        if y in big: continue
        Ey = [y] + adj[y]
        if len(Ey) >= 2: hyper.append((f"pl_{y}", [N[c] for c in Ey]))
    for i, (x, y) in enumerate(conn):
        hyper.append((f"conn{i}_{x}{y}", [N[x], N[y]]))
    s = f"R = ZZ/32003[{', '.join(allv)}];\n"
    s += "I = ideal(" + ",\n  ".join(gens) + ");\n"
    s += 'stderr << "DIMI " << dim I << endl;\n'
    s += "jmax = -1;\n"
    for name, vecs in hyper:
        rows = ", ".join("{" + ", ".join(v) + "}" for v in vecs)
        k = len(vecs)
        s += f"MM = matrix {{{rows}}};\n"
        s += f"JJ = I + minors({k}, MM);\n"
        s += f'jdim = dim JJ; stderr << "JUMP {name} {k} " << jdim << endl; jmax = max(jmax, jdim);\n'
    s += 'stderr << "MAXJUMP " << jmax << endl;\n'
    s += "exit 0\n"
    return s

def m2_script_jumpdims_full(Z, E, conn, seed, elim_conn=True):
    """As m2_script_jumpdims but in m2_script's original chart coordinates (points (1, t1, t2, t3), normals
    (t1, t2, t3, 1), the root flag fixed): the minors stay of degree <= 3, where the reduced coordinates nest the
    tree substitutions and blow the degrees up (T10 timed out at 360 s reduced).
    Connectors (elim_conn, default): a connector y between a, b is a point on the line pi_a cap pi_b, so X(Gamma +
    connectors) is a tower of P(pi_a cap pi_b)-bundles over X(Gamma) with fibre dimension 1 + [pi_a = pi_b].  A
    component over a locus L cap {S degenerate} (L a hyperedge jump locus or all of X(Gamma), S a set of connectors
    with pi_a = pi_b) has dimension dim(L cap D_S) + #conn + |S|, which reaches expdim(Gamma) + #conn iff
    dim(L cap D_S) >= expdim(Gamma) - |S|; so irreducibility of X(Gamma + conn) <=> (i) every hyperedge jump locus
    of X(Gamma) has dim <= expdim(Gamma) - 1 and (ii) every nonempty connector set S has dim D_S <= expdim(Gamma) -
    1 - |S| (with (ii), the joint loci L cap D_S are bounded by D_S).  The connector points are dropped from the
    ideal and (ii) is printed as "CONN <S> <size> <dim> <bound>"; PASS needs every JUMP <= expdim' - 1 and every
    CONN <= its bound.  With elim_conn=False the connector points stay and their planes form an ordinary hyperedge
    (T11 and D3c then time out at 600 s on the dimension of the full ideal)."""
    a0 = Z[0]
    adj = {c: [] for c in Z}
    for c, d in E: adj[c].append(d); adj[d].append(c)
    big = {c for c in Z if len(adj[c]) >= 3}
    blocks = []
    for c in Z: blocks += ["p" + c, "n" + c]
    if not elim_conn:
        for i, _ in enumerate(conn): blocks.append(f"q{i}")
    coord, allv = {}, []
    for b in blocks:
        if b == "p" + a0: coord[b] = ["1", "0", "0", "0"]; continue
        if b == "n" + a0: coord[b] = ["0", "0", "0", "1"]; continue
        t = [f"{b}t{j}" for j in range(1, 4)]; allv += t
        coord[b] = ["1"] + t if b[0] in "pq" else t + ["1"]
    def dot(x, y):
        terms = []
        for u, v in zip(coord[x], coord[y]):
            if u == "0" or v == "0": continue
            terms.append(u if v == "1" else v if u == "1" else f"{u}*{v}")
        return " + ".join(terms) if terms else "0"
    gens = []
    for c in Z: gens.append(dot("p" + c, "n" + c))
    for c, d in E: gens.append(dot("p" + d, "n" + c)); gens.append(dot("p" + c, "n" + d))
    if not elim_conn:
        for i, (x, y) in enumerate(conn): gens.append(dot(f"q{i}", "n" + x)); gens.append(dot(f"q{i}", "n" + y))
    gens = [g for g in gens if g != "0"]
    hyper = []
    for c in Z:
        U = [u for u in [c] + adj[c] if u in big]
        if len(U) >= 2: hyper.append((f"pts_{c}", [coord["p" + u] for u in U]))
    for y in Z:
        if y in big: continue
        Ey = [y] + adj[y]
        if len(Ey) >= 2: hyper.append((f"pl_{y}", [coord["n" + c] for c in Ey]))
    if not elim_conn:
        for i, (x, y) in enumerate(conn): hyper.append((f"conn{i}_{x}{y}", [coord["n" + x], coord["n" + y]]))
    s = f"R = ZZ/32003[{', '.join(allv)}];\n"
    s += "I = ideal(" + ",\n  ".join(gens) + ");\n"
    s += 'stderr << "DIMI " << dim I << endl;\n'
    s += "jmax = -1;\n"
    for name, vecs in hyper:
        rows = ", ".join("{" + ", ".join(v) + "}" for v in vecs)
        k = len(vecs)
        s += f"MM = matrix {{{rows}}};\nJJ = I + minors({k}, MM);\n"
        s += f'jdim = dim JJ; stderr << "JUMP {name} {k} " << jdim << endl; jmax = max(jmax, jdim);\n'
    s += 'stderr << "MAXJUMP " << jmax << endl;\n'
    if elim_conn and conn:
        from itertools import combinations
        expd = 5 * len(Z) - 2 * len(E) - 5
        for r in range(1, len(conn) + 1):
            for Sset in combinations(range(len(conn)), r):
                s += "JJ = I"
                for i in Sset:
                    x, y = conn[i]
                    rows = "{" + ", ".join(coord["n" + x]) + "}, {" + ", ".join(coord["n" + y]) + "}"
                    s += f" + minors(2, matrix {{{rows}}})"
                s += ";\n"
                label = "+".join(f"{conn[i][0]}{conn[i][1]}" for i in Sset)
                s += f'stderr << "CONN {label} {r} " << dim JJ << " {expd - 1 - r}" << endl;\n'
    s += "exit 0\n"
    return s

def run_jumpdims(key, tmo, full=True):
    Z, E, conn, comment = CASES[key]
    expected = 5 * len(Z) - 2 * len(E) + len(conn) - 5
    src = (m2_script_jumpdims_full if full else m2_script_jumpdims)(Z, E, conn, 0)
    with tempfile.NamedTemporaryFile("w", suffix=".m2", delete=False) as f:
        f.write(src); path = f.name
    t0 = time.time()
    try:
        out = subprocess.run(["M2", "--script", path], capture_output=True, text=True, timeout=tmo)
        txt = out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        os.unlink(path); print(f"{key:4s} TIMEOUT after {tmo}s  ({comment})"); return None
    os.unlink(path)
    jumps = [l for l in txt.splitlines() if l.startswith("JUMP")]
    conns = [l for l in txt.splitlines() if l.startswith("CONN")]
    mx = [l for l in txt.splitlines() if l.startswith("MAXJUMP")]
    dimi = [l for l in txt.splitlines() if l.startswith("DIMI")]
    if not mx:
        print(f"{key:4s} ERROR\n{txt[-2000:]}"); return False
    expd = 5 * len(Z) - 2 * len(E) - 5 if full else expected   # connector points eliminated in the full test
    m = int(mx[0].split()[1])
    conn_ok = all(int(l.split()[3]) <= int(l.split()[4]) for l in conns) and (not full or len(conns) == 2 ** len(conn) - 1)
    ok = (m <= expd - 1) and dimi and int(dimi[0].split()[1]) == expd and conn_ok
    print(f"{key:4s} {'PASS' if ok else 'FAIL'}  |Z|={len(Z)} |E|={len(E)} conn={len(conn)}  {dimi[0] if dimi else ''} expected {expd}"
          f"{' (connector points eliminated; full expected ' + str(expected) + ')' if full and conn else ''}; "
          f"max jump-locus dim {m} (need <= {expd - 1}); {len(jumps)} hyperedges, {len(conns)} connector sets  [{time.time() - t0:.1f}s]  ({comment})")
    for l in jumps + conns: print("      " + l)
    return ok

def run_case(key, seed, tmo, reduced=False, timed=False):
    Z, E, conn, comment = CASES[key]
    expected = 5 * len(Z) - 2 * len(E) + len(conn) - 5   # fibre over the fixed flag
    src = m2_script_reduced(Z, E, conn, seed, timed) if reduced else m2_script(Z, E, conn, seed)
    with tempfile.NamedTemporaryFile("w", suffix=".m2", delete=False) as f:
        f.write(src); path = f.name
    t0 = time.time()
    try:
        out = subprocess.run(["M2", "--script", path], capture_output=True, text=True, timeout=tmo)
        txt = out.stdout + out.stderr
    except subprocess.TimeoutExpired:
        os.unlink(path)
        print(f"{key:4s} TIMEOUT after {tmo}s  ({comment})"); return None
    os.unlink(path)
    if timed:
        for l in txt.splitlines():
            if l.startswith(("GBDONE", "DIMI")) or "seconds" in l: print(f"{key:4s} {l}")
    np = [l for l in txt.splitlines() if l.startswith("NPRIMES")]
    dims = [int(l.split()[1]) for l in txt.splitlines() if l.startswith("DIM ")]
    if not np:
        print(f"{key:4s} ERROR\n{txt[-2000:]}"); return False
    n = int(np[0].split()[1])
    ok = (n == 1 and dims == [expected])
    print(f"{key:4s} {'PASS' if ok else 'FAIL'}  |Z|={len(Z)} |E|={len(E)} conn={len(conn)}  expected dim {expected}; "
          f"minimal primes {n}, dims {sorted(dims, reverse=True)}  [{time.time() - t0:.1f}s]  ({comment})")
    return ok

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", action="append")
    ap.add_argument("--seed", type=int, default=20260923)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--reduced", action="store_true", help="spanning-tree-eliminated chart variety (S27(iv)); same components")
    ap.add_argument("--timed", action="store_true", help="with --reduced: print elapsed times of gb / dim / minimalPrimes")
    ap.add_argument("--jumpdims", action="store_true", help="irreducibility as a dimension test on the jump loci (S27(v)); no minimalPrimes")
    a = ap.parse_args()
    keys = a.case or list(CASES)
    if a.jumpdims:
        res = [run_jumpdims(k, a.timeout) for k in keys]
    else:
        res = [run_case(k, a.seed, a.timeout, a.reduced, a.timed) for k in keys]
    bad = [k for k, r in zip(keys, res) if r is False and not k.startswith("N")]
    negpass = [k for k, r in zip(keys, res) if r is True and k.startswith("N")]
    if negpass: print("NOTE: negative controls that passed (irreducible despite short cycles):", negpass)
    print("SUMMARY:", "all PASS" if not bad and None not in res else f"FAIL {bad}; timeouts {[k for k, r in zip(keys, res) if r is None]}")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
