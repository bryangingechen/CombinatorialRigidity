#!/usr/bin/env python3
"""foldcheck.py -- Track J, the folded-ring point of (J-4), computed exactly.
For a Case II-tree instance (G' = path of classes R0..R_delta, G'' = G' + ab the closed ring), at a
random picture q certified in U(G'') (dim L = 3 + def2):
  * the folded flex P: constant sigma_j on each class, sigma_j - sigma_{j-1} = t_j l_j across bridge j,
    sigma_0 - sigma_delta = t_ab l_ba, with sum t_e l_e = 0 (a random solution);
  * ASSERT z_f := Phi(P) lies in L_{G''}(q);
  * at z_f: rank of the bridge lines L_1..L_delta and of L_1..L_delta, n; which L_j meet n;
  * delta = 3: the same at z = 0 (the flat point).
Exact Q.  PYTHONHASHSEED=0, seed 20260924, repository root."""
import os, sys, random
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts'))
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts', 'w4'))
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'trackB'))
import scriptpath  # noqa
from fractions import Fraction as F
from exactcore import nullspace, wedge2, dot
from kbare_common import verts_of
from maincomp import sample_q, lifting_space, lifting_constraints, def_k
from repin import hodge_star
import chordprobe as cp
import ringprobe as rp
import earcover as ec


def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]


def run(label, E, a, b, rng):
    V = verts_of(E)
    cls, of, QE = ec.classes_of(E, V)
    A, B = of[a], of[b]
    # order the path of classes from A to B
    adj = {}
    for (i, j) in QE:
        adj.setdefault(i, []).append(j)
        adj.setdefault(j, []).append(i)
    order, prev, cur = [A], None, A
    while cur != B:
        nxt = [x for x in adj[cur] if x != prev][0]
        prev, cur = cur, nxt
        order.append(cur)
    assert len(order) == len(cls), 'not a path of classes'
    pos = {c: k for k, c in enumerate(order)}
    bridges = {}
    for (u, w) in E:
        i, j = of[u], of[w]
        if i != j:
            if pos[i] > pos[j]:
                u, w, i, j = w, u, j, i
            bridges[pos[j]] = (u, w)             # bridge j: u in R_{j-1}, w in R_j
    d = len(order) - 1
    Ec = E + [(a, b)]
    for _ in range(20):
        q = sample_q(rng, V, Ec, 30)
        if len(lifting_space(Ec, V, q)) == 3 + def_k(Ec, 3):
            break
    hat = {v: [q[v][0], q[v][1], F(1)] for v in V}
    ls = [cross(hat[bridges[j][0]], hat[bridges[j][1]]) for j in range(1, d + 1)]
    lab = cross(hat[b], hat[a])                  # sigma_0 - sigma_d across b -> a
    # solve sum_j t_j l_j + t_ab l_ab = 0
    M = [[ls[j][k] for j in range(d)] + [lab[k]] for k in range(3)]
    N = nullspace(M)
    coef = [rng.randint(-9, 9) or 1 for _ in N]
    t = [sum(c * nv[i] for c, nv in zip(coef, N)) for i in range(d + 1)]
    assert all(x != 0 for x in t), t
    sig = [[F(0)] * 3]
    for j in range(1, d + 1):
        sig.append([s + t[j - 1] * l for s, l in zip(sig[-1], ls[j - 1])])
    assert all(s + t[d] * l == s0 for s, l, s0 in zip(sig[d], lab, sig[0]))
    z = [dot(sig[pos[of[v]]], hat[v]) for v in V]
    rows = lifting_constraints(Ec, V, q)
    assert all(sum(r[i] * z[i] for i in range(len(V))) == 0 for r in rows), 'z_f not in L_G\'\''
    iv = {v: i for i, v in enumerate(V)}
    P = {v: [q[v][0], q[v][1], z[iv[v]], F(1)] for v in V}
    L = [wedge2(P[bridges[j][0]], P[bridges[j][1]]) for j in range(1, d + 1)]
    n = wedge2(P[a], P[b])
    meets = [dot(hodge_star(n), x) == 0 for x in L]
    out = dict(label=label, delta=d, rank_L=cp.dim(L), rank_Ln=cp.dim(L + [n]), meets_n=meets)
    if d == 3:
        P0 = {v: [q[v][0], q[v][1], F(0), F(1)] for v in V}
        L0 = [wedge2(P0[bridges[j][0]], P0[bridges[j][1]]) for j in range(1, d + 1)]
        out['flat_rank_L'] = cp.dim(L0)
    return out


for (label, E, a, b, blobs) in rp.instances():
    if not label.startswith('T'):
        continue
    print(run(label, E, a, b, random.Random(f'{rp.SEED}:fold:{label}')))
