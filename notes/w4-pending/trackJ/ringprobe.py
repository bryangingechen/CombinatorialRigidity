#!/usr/bin/env python3
"""
ringprobe.py -- Track J (W4-reopen P1, cell (MC-51)(c): k = 1, delta2 = 3, delta in {3, 4}).

Built instances G = G' + (a - y - b) from a CLASS GRAPH: each class is a small rigid blob (C4, C5,
C6) or a singleton; class-graph edges become single bridge edges between chosen blob vertices.
Per instance, exact over Q except the mod-(2^61-1) attainment screens (certificates only):
  * combinatorics: delta, delta2, the def3-classes of G' recomputed from scratch (asserted to be the
    built blobs), the minimisers of c over class sets through A, B, and the (J-1) case split:
    CASE I if some locally minimal Y (c(Y) <= 4, minimal among its subsets through A, B) has
    union(Y) + y != V(G); CASE II otherwise;  whether G is in S (2-connected, (S), not cycle/theta);
  * the chord point (Track B's): q certified in U(G') and U(G'+ab), z0 random in L_{G'+ab}(q) at
    which G'+ab attains;
  * CLASS LEVEL at z0 (bodies = classes, hinges = bridge lines p_u ^ p_v): whether the class-level
    G' is independent (rank 5|E_Gamma|), whether the welded class-level G'/AB is rigid, dim of the
    class-level relative space rhoG(z0), dim(rhoG(z0) cap n^perp);
  * VERTEX LEVEL at z0: a'(z0), r(z0), dim(rho(z0) cap n^perp) (Track B's quantities);
  * rhobar(z1) (Track B's series limit) for two random z1: its dimension, whether it EQUALS
    rhoG(z0) (the constancy that (J-3) uses), dim(rhobar cap n^perp);
  * ground truth: X0(G) attains at one certified draw (mod p rank = target certifies).
Reading: at z0, "independent", "welded rigid", "dim(rhoG cap n^perp) = 3" are open conditions, so a
draw showing them certifies them at the generic chord point; a draw failing them only bounds.
PYTHONHASHSEED=0, seed 20260924, run from the repository root.
    python3 ringprobe.py
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts'))
sys.path.insert(0, os.path.join(os.getcwd(), 'notes', 'scripts', 'w4'))
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'trackB'))
import scriptpath  # noqa: F401,E402
from fractions import Fraction as F  # noqa: E402
from exactcore import nullspace, wedge2  # noqa: E402
from kbare_common import build_rigidity, verts_of, rank_modp  # noqa: E402
from maincomp import sample_q, lifting_space, _interp, def_k, aug_matrix  # noqa: E402
from earstep import contract  # noqa: E402
import chordprobe as cp  # noqa: E402
import classes as cl  # noqa: E402

SEED = 20260924

BLOBS = {'v': (1, []), 'C4': (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
         'C5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
         'C6': (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])}


def build(types, gedges, a_at, b_at):
    """types[i] in BLOBS; gedges = [(i, si, j, sj)] bridge from blob i vertex si to blob j vertex sj;
    a = blob a_at[0] vertex a_at[1], likewise b.  Returns (G' edges, a, b, blob vertex sets)."""
    E, blobs = [], []
    for i, t in enumerate(types):
        n, ee = BLOBS[t]
        blobs.append([f'{i}.{k}' for k in range(n)])
        E += [(f'{i}.{u}', f'{i}.{w}') for (u, w) in ee]
    for (i, si, j, sj) in gedges:
        E.append((f'{i}.{si}', f'{j}.{sj}'))
    return E, f'{a_at[0]}.{a_at[1]}', f'{b_at[0]}.{b_at[1]}', blobs


def bh_matrix(nb, hinges, lines):
    """class-level body-hinge rows: for hinge (i, j) with line L, the 5 functionals killing L,
    applied to X_j - X_i."""
    rows = []
    for (i, j), L in zip(hinges, lines):
        for f in nullspace([L]):
            r = [F(0)] * (6 * nb)
            for k in range(6):
                r[6 * j + k] += f[k]
                r[6 * i + k] -= f[k]
            rows.append(r)
    return rows


def classify(E, a, b, y='y'):
    """(J-1) case split and S-membership, from scratch."""
    V = verts_of(E)
    Vp = [v for v in V]
    cls, of, QE = cl.class_quotient(E, Vp)
    A, B = of[a], of[b]
    others = [i for i in range(len(cls)) if i not in (A, B)]
    cvals = {}
    for k in range(len(others) + 1):
        for S in itertools.combinations(others, k):
            Y = frozenset((A, B) + S)
            cvals[Y] = cl.cval(Y, QE)[0]
    delta = min(cvals.values())
    locmin = []
    for Y, c in cvals.items():
        if c <= 4 and all(cvals[Z] >= c for Z in cvals if Z <= Y):
            locmin.append(Y)
    full = frozenset(range(len(cls)))
    caseI = any(Y != full for Y in locmin)
    mins = [Y for Y, c in cvals.items() if c == delta]
    tree = any(cl.cval(Y, QE)[1] == len(Y) - 1 for Y in mins)
    G = E + [(a, y), (y, b)]
    VG = verts_of(G)
    inS = cl.two_connected(G, VG) and cl.is_S(G, VG)
    return dict(cls=cls, of=of, QE=QE, delta=delta, caseI=caseI, tree=tree, inS=inS,
                nmin=len(mins), nloc=len(locmin))


def probe(label, E, a, b, blobs, rng, nz1=2):
    V = verts_of(E)
    nV = len(V)
    f, f2 = def_k(E, 6), def_k(E, 3)
    vs = [v for v in V if v != b]
    Eab = contract(E, a, b)
    delta, delta2 = f - def_k(Eab, 6, vs), f2 - def_k(Eab, 3, vs)
    info = classify(E, a, b)
    got_cls = sorted(sorted(c) for c in info['cls'] if len(c) > 1)
    want = sorted(sorted(bl) for bl in blobs if len(bl) > 1)
    assert got_cls == want, (label, got_cls, want)
    assert info['delta'] == delta
    Ec = E + [(a, b)]
    tgt_c = 6 * (nV - 1) - def_k(Ec, 6)
    d2c = def_k(Ec, 3)
    got = None
    for _ in range(10):
        try:
            q = sample_q(rng, V, Ec, 30)
            L = lifting_space(E, V, q)
            Lc = lifting_space(Ec, V, q)
        except (AssertionError, RuntimeError):
            continue
        if len(L) != 3 + f2 or len(Lc) != 3 + d2c:
            continue
        co = [rng.randint(-30, 30) for _ in Lc]
        z = [sum(c * bb[t] for c, bb in zip(co, Lc)) for t in range(nV)]
        pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
        if rank_modp(build_rigidity(Ec, pt)[0]) == tgt_c:
            got = (q, L, z, pt)
            break
    rec = dict(label=label, n=nV + 1, delta=delta, delta2=delta2, case='I' if info['caseI'] else 'II',
               tree=info['tree'], inS=info['inS'], ncls=len(info['cls']))
    if got is None:
        rec['status'] = 'no chord point'
        return rec
    q, L, z, pt = got
    ia, ib = V.index(a), V.index(b)
    pa, pb = cp.hom(q[a], z[ia]), cp.hom(q[b], z[ib])
    n = wedge2(pa, pb)
    nperp = cp.kperp([n])
    h0 = _interp(E, V, q, z)
    rec['caseA'] = tuple(h0[a]) != tuple(h0[b])
    # vertex level
    M = nullspace(build_rigidity(E, pt)[0])
    rho = cp.rel(M, V, a, b)
    rec['ap'] = len(M) - 6 - f
    rec['r'] = cp.dim(rho)
    rec['rn'] = cp.cap(rho, nperp)
    # class level
    of, QE, cls = info['of'], info['QE'], info['cls']
    hinges, lines = [], []
    for (u, w) in E:
        i, j = of[u], of[w]
        if i != j:
            hinges.append((i, j))
            lines.append(wedge2(cp.hom(q[u], z[V.index(u)]), cp.hom(q[w], z[V.index(w)])))
    nb = len(cls)
    R = bh_matrix(nb, hinges, lines)
    MG = nullspace(R) if R else []
    A, B = of[a], of[b]
    rec['cl_indep'] = (cp.dim(R) == len(R)) if R else True
    rhoG = [[X[6 * B + k] - X[6 * A + k] for k in range(6)] for X in MG]
    rec['cl_r'] = cp.dim(rhoG)
    weld = R + [[F(int(c == 6 * A + k)) - F(int(c == 6 * B + k)) for c in range(6 * nb)] for k in range(6)]
    rec['cl_weld_rigid'] = (len(nullspace(weld)) == 6)
    rec['cl_rn'] = cp.cap(rhoG, nperp)
    rec['cl_contains_rho'] = cp.cap(rho, rhoG) == cp.dim(rho)
    # rhobar
    A0 = aug_matrix(E, V, pt)
    lims = []
    for _ in range(nz1):
        c1 = [rng.randint(-30, 30) for _ in L]
        z1 = [sum(cc * bb[s] for cc, bb in zip(c1, L)) for s in range(nV)]
        pt1 = {v: (q[v][0], q[v][1], z[t] + z1[t]) for t, v in enumerate(V)}
        A01 = aug_matrix(E, V, pt1)
        A1 = [[x - y for x, y in zip(r1, r0)] for r1, r0 in zip(A01, A0)]
        Mbar, kk = cp.series_limit(A0, A1, 6 * nV, 6 + f)
        if Mbar is None:
            lims.append('none')
            continue
        rbar = cp.rel(Mbar, V, a, b)
        eq = cp.dim(rbar) == cp.dim(rhoG) == cp.cap(rbar, rhoG)
        lims.append((cp.dim(rbar), eq, cp.cap(rbar, nperp)))
    rec['lims'] = lims
    rec['truth'] = cp.truth_G(E, a, b, rng)
    rec['status'] = 'ok'
    return rec


# ------------------------------------------------------------------ instances
def ring(types, a_v=0, b_v=0, att=None):
    """a ring of classes types[0..m-1] (A = 0, B = m-1) joined consecutively; entry at vertex 2
    and exit at vertex 0 of every blob unless att overrides {i: (entry, exit)}; a = 0.a_v,
    b = (m-1).b_v.  Returns a path of classes (the tree case): G' = path, G = path + y."""
    m = len(types)
    att = att or {}
    ge = []
    for i in range(m - 1):
        ex = att.get(i, (None, 2))[1] if types[i] != 'v' else 0
        en = att.get(i + 1, (0, None))[0] if types[i + 1] != 'v' else 0
        ge.append((i, ex, i + 1, en))
    return build(types, ge, (0, a_v), (m - 1, b_v))


def cyc(types, ia, ib, att=None):
    """a CYCLE of classes types[0..L-1]; A = class ia, B = class ib; blob entry vertex 0, exit
    vertex 2 (opposite on C4) unless att overrides; a, b = vertex 1 of their blob (or 0 if
    singleton)."""
    Lc = len(types)
    att = att or {}
    ge = []
    for i in range(Lc):
        j = (i + 1) % Lc
        ex = att.get(i, (0, 2))[1] if types[i] != 'v' else 0
        en = att.get(j, (0, 2))[0] if types[j] != 'v' else 0
        ge.append((i, ex, j, en))
    av = 1 if types[ia] != 'v' else 0
    bv = 1 if types[ib] != 'v' else 0
    return build(types, ge, (ia, av), (ib, bv))


def instances():
    out = []
    # CASE II tree: G' = path of classes, blobs at the ends (a, b must be hubs)
    out.append(('T3:C4-v-v-C4', *ring(['C4', 'v', 'v', 'C4'], a_v=1, b_v=1)))
    out.append(('T4:C4-v-v-v-C4', *ring(['C4', 'v', 'v', 'v', 'C4'], a_v=1, b_v=1)))
    out.append(('T4:C4-C4-v-C4-C4', *ring(['C4', 'C4', 'v', 'C4', 'C4'], a_v=1, b_v=1)))
    out.append(('T4:C5-v-C4-v-C4', *ring(['C5', 'v', 'C4', 'v', 'C4'], a_v=1, b_v=1)))
    out.append(('T3:C4-C4-C4-C4', *ring(['C4', 'C4', 'C4', 'C4'], a_v=1, b_v=1)))
    # a at the bridge vertex (u1 = a): then a has degree 3 via the C4 and y only if bridge at a...
    out.append(('T4:C4a-v-v-v-C4b', *ring(['C4', 'v', 'v', 'v', 'C4'], a_v=2, b_v=0)))
    # CASE II cyclic: C10 of classes, A, B antipodal (5, 5), delta = 4
    out.append(('Y4:C10(v)', *cyc(['v'] * 10, 0, 5)))
    out.append(('Y4:C10+C4@2', *cyc(['v', 'v', 'C4', 'v', 'v', 'v', 'v', 'v', 'v', 'v'], 0, 5)))
    out.append(('Y4:C10+C4@A', *cyc(['C4', 'v', 'v', 'v', 'v', 'v', 'v', 'v', 'v', 'v'], 0, 5)))
    out.append(('Y4:C10+C4@A,B', *cyc(['C4', 'v', 'v', 'v', 'v', 'C4', 'v', 'v', 'v', 'v'], 0, 5)))
    out.append(('Y4:C10+C4x3', *cyc(['C4', 'v', 'C4', 'v', 'v', 'C4', 'v', 'v', 'C4', 'v'], 0, 5)))
    # C9 of classes, A, B at (4, 5), delta = 3
    out.append(('Y3:C9(v)', *cyc(['v'] * 9, 0, 4)))
    out.append(('Y3:C9+C4@2', *cyc(['v', 'v', 'C4', 'v', 'v', 'v', 'v', 'v', 'v'], 0, 4)))
    out.append(('Y3:C9+C4@A,B', *cyc(['C4', 'v', 'v', 'v', 'C4', 'v', 'v', 'v', 'v'], 0, 4)))
    # CASE I examples: C9 of classes with A, B at distance 3 (a path minimiser, delta = 3)
    out.append(('I3:C9d3+C4', *cyc(['C4', 'v', 'v', 'C4', 'v', 'v', 'C4', 'v', 'v'], 0, 3)))
    return out


def main():
    print(f'# ringprobe.py seed={SEED}')
    for (label, E, a, b, blobs) in instances():
        if not cp.satisfies_H(E):
            print(label, 'G\' fails (H)')
            continue
        nb = cp.nbrs(E)
        if len(nb[a]) < 2 or len(nb[b]) < 2 or b in nb[a]:
            print(label, 'bad a, b')
            continue
        rng = random.Random(f'{SEED}:{label}')
        rec = probe(label, E, a, b, blobs, rng)
        print(rec, flush=True)


if __name__ == '__main__':
    main()
