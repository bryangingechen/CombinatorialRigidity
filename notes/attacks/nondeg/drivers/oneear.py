#!/usr/bin/env python3
"""NONDEG workbook S30: the good ears of route B's case (ii), and which are costly in P^d.

    python3 notes/attacks/nondeg/drivers/oneear.py --pop brief --seed 1
    python3 notes/attacks/nondeg/drivers/oneear.py --pop d4 --seed 1
    python3 notes/attacks/nondeg/drivers/oneear.py --pop geng --n 5 6 7 8 --seed 1

Population.  `brief`: nondeg.py's graphs(); `d4`: strata's GRAPHS4, simple graphs only; `geng`:
every connected graph on n vertices with minimum degree two (`geng -c -d2 -q n`, nauty 2.9),
one representative per isomorphism class.  Kept: simple, two-edge-connected, at least four bodies,
the hub conditions of `lem:pencil-feasible-hub-conditions` (every |H[v]| <= 3, no triangle with two
hubs), and a planar-rigid set (some Y, |Y| >= 2, with s_2(Y) = 3(|Y|-1) - 2e(Y) <= 0; equivalent
by `lem:deficiency-sparse`, as the good-ear lemma's proof uses).  That is route B's case (ii).

Per graph G:
  * the reduction choices of `lem:pencil-rigid-good-ear`: pendant triangles (adjacent x1, x2 of
    degree two with a common neighbour of degree >= 4) and good ears (x of degree two, both
    neighbours a, b hubs, def_6(G - x) <= def_6(G)), each ear classed E0/E1/E2 by the number of
    common neighbours of a, b in H = G - x (workbook S24), and marked `w` when x, a, b lie in one
    minimal planar-rigid set W0 (the lemma's proof finds its ear in such a set), with
    `[X..]` listing dim L_{G[X]}(q0|X), X = W0 - x, for each such W0 (S29's criterion (W): 4);
    the tally's X4 counts the W0-ears where every listed value is 4;
  * one point r0 of the polar steer family at d = 3 (nondeg.py's `steer3`), checked C2-same
    exactly (else the graph is reported "draw degenerate" and nothing more is claimed);
  * at each good ear, over the picture q0 of r0: dim L_G(q0) and dim L_H(q0|H).  Restriction
    identifies L_G(q0) with the kernel of mu on L_H (S24 (3)), so the ear is FREE (mu = 0 at this
    draw) iff the two dimensions agree, COSTLY iff L_G is one smaller.  For a costly ear, the rank
    of kappa (S30): z -> (h_a(z) - h_b(z)) restricted to the line l = {h_a(z1) = h_b(z1)} through
    q_x, read at q_x and one more point of l (and at q_y for E1, where it must vanish);
  * the verdict: `free` if a pendant triangle or a free ear exists, else `forced`;
  * def_D(G) at d = 3..6 (D = 6, 10, 15, 21).  At a forced graph, at every d in 4..6 with
    def_(d-1)(G) > def_d(G) (S27: only there is (B') needed), one configuration over q0 with all
    d - 2 heights redrawn in L_G(q0) (nondeg.py's `steer_cell`; S13's form of the lift family,
    workbook S18's remark), its rank against t_d(G), and C2-same checked.  `=` is an exact certificate of Generic_d(G) under C2-same (an exhibited
    realization at the deficiency rank); `<` certifies nothing.

Measured, not certified: FREE/COSTLY and rank kappa are read at one draw; each dimension is upper
semicontinuous, so a draw reads it from above, and "free at the draw" is evidence about the
general point, not a proof.  Sampler support: as nondeg.py (strata's Sampler, COORD).  Exit status
1 if a guard fails in a way the run cannot classify (an E1 kappa not vanishing at q_y).
"""
import argparse
import os
import subprocess
import sys
from fractions import Fraction as F
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import nondeg as nd  # noqa: E402  -- read-only reuse (also imports strata)

st = nd.st
DIMS_RANK = (4, 5, 6)


# ---------------- populations ----------------

def graph6(line):
    n = ord(line[0]) - 63
    bits = []
    for c in line[1:]:
        v = ord(c) - 63
        bits += [(v >> (5 - i)) & 1 for i in range(6)]
    edges, k = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def geng_graphs(n):
    out = subprocess.run(["geng", "-c", "-d2", "-q", str(n)], capture_output=True, text=True,
                         timeout=600, check=True).stdout.split()
    return {f"g{n}-{i}": graph6(s) for i, s in enumerate(out)}


def population(a):
    if a.pop == "geng":
        G = {}
        for n in a.n:
            G.update(geng_graphs(n))
        return G
    return nd.population(a.pop)


# ---------------- graph predicates ----------------

def connected(n, edges, skip=None):
    nb = {v: [] for v in range(n)}
    for i, (u, v) in enumerate(edges):
        if i != skip:
            nb[u].append(v)
            nb[v].append(u)
    seen, stack = {0}, [0]
    while stack:
        for w in nb[stack.pop()]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n


def two_edge_connected(n, edges):
    return connected(n, edges) and all(connected(n, edges, skip=i) for i in range(len(edges)))


def min_s2(n, edges):
    best = None
    for Y in range(1, 1 << n):
        k = bin(Y).count("1")
        if k < 2:
            continue
        e = sum(1 for u, v in edges if (Y >> u) & 1 and (Y >> v) & 1)
        s = 3 * (k - 1) - 2 * e
        best = s if best is None else min(best, s)
    return best


def minimal_rigid_sets(n, edges):
    """The minimal planar-rigid sets W (s_2(W) <= 0, |W| >= 2, s_2(Z) >= 1 for every Z strictly
    inside W with |Z| >= 2), as bitmasks: the sets the good-ear lemma's proof starts from."""
    s2 = {}
    for Y in range(1, 1 << n):
        k = bin(Y).count("1")
        if k >= 2:
            e = sum(1 for u, v in edges if (Y >> u) & 1 and (Y >> v) & 1)
            s2[Y] = 3 * (k - 1) - 2 * e
    out = []
    for W, sw in s2.items():
        if sw > 0:
            continue
        Z, ok = (W - 1) & W, True
        while Z:
            if Z in s2 and s2[Z] <= 0:
                ok = False
                break
            Z = (Z - 1) & W
        if ok:
            out.append(W)
    return out


def delete(n, edges, gone):
    keep = [v for v in range(n) if v not in gone]
    ix = {v: i for i, v in enumerate(keep)}
    return len(keep), [(ix[u], ix[v]) for u, v in edges if u in ix and v in ix], ix


def choices(n, edges):
    nb, hubs, _ = nd.hub_sets(n, edges)
    d6 = st.deficiency(n, edges, 6)
    mins = minimal_rigid_sets(n, edges)
    ears, tris = [], []
    for x in range(n):
        if len(nb[x]) != 2:
            continue
        a, b = sorted(nb[x])
        if a in hubs and b in hubs:
            m, E, _ = delete(n, edges, {x})
            if st.deficiency(m, E, 6) <= d6:
                common = sorted((nb[a] & nb[b]) - {x})
                ws = [W for W in mins if all((W >> v) & 1 for v in (x, a, b))]
                ears.append((x, a, b, common, ws))
    for x1, x2 in combinations(range(n), 2):
        if len(nb[x1]) == 2 and len(nb[x2]) == 2 and x2 in nb[x1]:
            c = (nb[x1] - {x2}).pop()
            if c in nb[x2] and len(nb[c]) >= 4:
                tris.append((x1, x2, c))
    return ears, tris


# ---------------- the ear at a drawn picture ----------------

def affine_fit(q, z, N):
    """The affine function alpha x + beta y + gamma agreeing with z on three members of N whose
    picture points are not collinear (the plane of the body, at height z)."""
    for t in combinations(N, 3):
        A = [[q[w][0], q[w][1], F(1)] for w in t]
        if st.rank(A) == 3:
            sol = st.nullspace([row + [-z[w]] for row, w in zip(A, t)])
            st.need(len(sol) == 1 and sol[0][3] != 0, "affine fit")
            return [c / sol[0][3] for c in sol[0][:3]]
    raise st.Degenerate("closed neighbourhood collinear")


def dim_LX(n, edges, q0, x, W):
    """dim L_{G[X]}(q0|X), X = W - {x}: the lifting space of the induced subgraph at the restricted
    picture (workbook S29's criterion (W) asks it to be 4 = 3 + def_2(G[X]))."""
    m, E, ix = delete(n, edges, {v for v in range(n) if not (W >> v) & 1} | {x})
    qX = [None] * m
    for v, i in ix.items():
        qX[i] = q0[v]
    return len(st.lifting_space(m, E, qX))


def ev(f, p):
    return f[0] * p[0] + f[1] * p[1] + f[2]


def ear_cell(n, edges, q0, z1, ear):
    x, a, b, common, _ = ear
    LG = st.lifting_space(n, edges, q0)
    m, E, ix = delete(n, edges, {x})
    qH = [None] * m
    for v, i in ix.items():
        qH[i] = q0[v]
    LH = st.lifting_space(m, E, qH)
    nbH = nd.nbhd(m, E)
    Na, Nb = sorted(nbH[ix[a]] | {ix[a]}), sorted(nbH[ix[b]] | {ix[b]})
    z1H = [z1[v] for v in sorted(ix, key=ix.get)]
    g = [p - r for p, r in zip(affine_fit(qH, z1H, Na), affine_fit(qH, z1H, Nb))]
    qx = q0[x]
    st.need(ev(g, qx) == 0, "the drawn x is off the line where the planes of a, b meet")
    q2 = (qx[0] - g[1], qx[1] + g[0])  # a second point of that line
    kap = []
    for z in LH:
        k = [p - r for p, r in zip(affine_fit(qH, z, Na), affine_fit(qH, z, Nb))]
        kap.append([ev(k, qx), ev(k, q2)] + [ev(k, q0[y]) for y in common])
    rk = st.rank([row[:2] for row in kap]) if kap else 0
    e1ok = all(row[2] == 0 for row in kap) if len(common) == 1 else True
    return len(LG), len(LH), rk, e1ok


# ---------------- main ----------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--pop", choices=["brief", "d4", "geng"], default="brief")
    ap.add_argument("--n", type=int, nargs="+", default=[5, 6, 7, 8])
    a = ap.parse_args()
    s = st.Sampler(a.seed)
    print(f"# oneear.py --pop {a.pop}{' --n ' + ' '.join(map(str, a.n)) if a.pop == 'geng' else ''}"
          f" seed {a.seed}; COORD {st.COORD}")
    G = population(a)
    tally = {"kept": 0, "degenerate": 0, "free": 0, "forced": 0, "ears": 0, "E0": 0, "E1": 0,
             "E2": 0, "W0-ears": 0, "costly": 0, "costly W0-ears": 0, "X4": 0,
             "cells": 0, "attain": 0}
    bad = 0
    for name in G:
        n, edges = G[name]
        if n < 4 or not st.simple(edges):
            continue
        _, _, H = nd.hub_sets(n, edges)
        if any(len(H[v]) > 3 for v in range(n)) or nd.two_hub_triangle(n, edges):
            continue
        if not two_edge_connected(n, edges) or min_s2(n, edges) > 0:
            continue
        tally["kept"] += 1
        ears, tris = choices(n, edges)
        try:
            q0, z1 = nd.steer3(s, n, edges)
            _, b, Pi, _ = nd.steer_cell(s, n, edges, 3, q0, z1)
            st.need(nd.candidates(n, edges, b, Pi, 4)["C2same"], "steer draw not C2-same")
        except st.Degenerate as ex:
            tally["degenerate"] += 1
            print(f"{name:10s} n={n} e={len(edges)}  draw degenerate, no conclusion: {ex}")
            continue
        cells, free = [], bool(tris)
        for ear in ears:
            cls = f"E{min(len(ear[3]), 2)}" + ("w" if ear[4] else "")
            tally["ears"] += 1
            tally[cls[:2]] += 1
            tally["W0-ears"] += bool(ear[4])
            try:
                lg, lh, rk, e1ok = ear_cell(n, edges, q0, z1, ear)
            except st.Degenerate as ex:
                cells.append(f"x{ear[0]}:{cls}:degenerate({ex})")
                continue
            bad += not e1ok
            lx = ""
            if ear[4]:
                try:
                    lx = "[X" + ",".join(str(dim_LX(n, edges, q0, ear[0], W)) for W in ear[4]) + "]"
                except st.Degenerate:
                    lx = "[X?]"
                tally["X4"] += lx.startswith("[X4") and all(c in "4," for c in lx[2:-1])
            if lg == lh:
                free = True
                cells.append(f"x{ear[0]}:{cls}:free({lg}){lx}")
            else:
                tally["costly"] += 1
                tally["costly W0-ears"] += bool(ear[4])
                cells.append(f"x{ear[0]}:{cls}:COSTLY({lg}<{lh},k{rk})" + ("" if e1ok else "!E1"))
        df = {d: st.deficiency(n, edges, (d + 1) * d // 2) for d in (3,) + DIMS_RANK}
        verdict = "free" if free else "forced"
        tally[verdict] += 1
        line = (f"{name:10s} n={n} e={len(edges)} def={[df[d] for d in sorted(df)]} "
                f"PT={len(tris)} {verdict:6s} " + " ".join(cells))
        if not free:
            for d in DIMS_RANK:
                if df[d - 1] > df[d]:
                    D = (d + 1) * d // 2
                    t = D * (n - 1) - df[d]
                    _, bd, Pd, hinges = nd.steer_cell(s, n, edges, d, q0, z1)
                    ok = nd.candidates(n, edges, bd, Pd, d + 1)["C2same"]
                    r = st.motion_rank(n, edges, hinges)
                    st.need(r <= t, "rank above the deficiency rank")
                    tally["cells"] += 1
                    tally["attain"] += r == t and ok
                    line += f" | d={d}: {r}/{t}{'=' if r == t else '<'}{'' if ok else ' notC2'}"
        print(line, flush=True)
    print("# " + ", ".join(f"{k} {v}" for k, v in tally.items()))
    print(f"# E1 guard failures: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
