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

def run_case(key, seed, tmo):
    Z, E, conn, comment = CASES[key]
    expected = 5 * len(Z) - 2 * len(E) + len(conn) - 5   # fibre over the fixed flag
    src = m2_script(Z, E, conn, seed)
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
    a = ap.parse_args()
    keys = a.case or list(CASES)
    res = [run_case(k, a.seed, a.timeout) for k in keys]
    bad = [k for k, r in zip(keys, res) if r is False and not k.startswith("N")]
    negpass = [k for k, r in zip(keys, res) if r is True and k.startswith("N")]
    if negpass: print("NOTE: negative controls that passed (irreducible despite short cycles):", negpass)
    print("SUMMARY:", "all PASS" if not bad and None not in res else f"FAIL {bad}; timeouts {[k for k, r in zip(keys, res) if r is None]}")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
