#!/usr/bin/env python3
"""
chordprobe.py -- §(K-main) Step MC18 (W4-reopen P1, the third 2026-09-24 session's Track B; the k = 1 open-ear cell (MC-51)(c)):
targeted exact probes at the chord point of Step MC13 (MC-49)/(MC-50).

Run from the repository root (it imports the harness from notes/scripts).

Per instance (G', a, b), a !~ b, G = G' + (a - y - b):
  * delta = def3(G') - def3(G'/ab), delta2 = def2(G') - def2(G'/ab);
  * q certified in U(G') and U(G'+ab) (dim L = 3 + def2 for both), exact;
    at q: dim U and the rank of the two incidence functionals phi1, phi2
    on L_{G'}(q) (flag genericity = rank 2);
  * z0 a random point of L_{G'+ab}(q) at which G'+ab attains (mod p
    certificate, then exact motion spaces);
  * at z0: a'(z0) = dim M_{G'}(z0) - 6 - f, r(z0), whether pi_a = pi_b
    (case B) or not (case A), dim(rho(z0) cap n^perp), whether rho(z0) is
    inside n^perp ("bar along n implied"), and in case B dim(rho(z0) cap
    Lambda^2 pi);
  * the DELTA-dimensional limit rhobar(z1) = lim_{s->0} rho(z0 + s z1) for
    random z1 in L_{G'}(q) (exact: the kernel of A(z0) + s A1(z1) over
    K[[s]], truncated until its x0-projection has dimension 6 + f), and the
    Track-B bound  (6 + f) - delta + min_t dim(rhobar cap Pen(y0(t), sigma(t)))
    with sigma(t) the first-order limit plane of (MC-108);
  * ground truth: X0(G) at one q_G certified in U(G) and a random z in L_G,
    rank mod 2^61-1 against 6(|V|-1) - def3(G) (equality certifies).
Exact Q throughout except the two mod-p attainment certificates.
Seeded: PYTHONHASHSEED=0, random.Random(f'{SEED}:{label}').

READING THE FIGURES (semicontinuity).  All per-draw quantities are at ONE
chord point.  dim M_{G'}(z0), hence a'(z0) and r(z0) = delta + a'(z0), is
upper semicontinuous: a draw OVER-estimates the generic a' (apredraw.py
re-measures at several draws; a draw with a' = 0 certifies generic a' = 0
because a' >= 0).  Where the draw has a' = 0, "dim(rho cap n^perp) = 3" is
an open condition on the open set r(z0) = delta, so it certifies the chord
criterion (MC-112) at that instance.  "case B" (pi_a = pi_b at the draw) is a
closed condition: a draw with pi_a != pi_b certifies case A.
Modes: --thetas S | --habitats [--stride] | --subdiv BASE | --exh N [--nmin]
| --random K (random sparse G', see randmain).
"""
import argparse
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # canonical harness path bootstrap
import scriptpath  # noqa: F401,E402

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact, nullspace, wedge2, dot  # noqa: E402
from kbare_common import build_rigidity, verts_of, rank_modp  # noqa: E402
from maincomp import sample_q, lifting_space, _interp, def_k, aug_matrix  # noqa: E402
from earstep import contract  # noqa: E402
from repin import hodge_star  # noqa: E402
from nogood_subdiv import is_simple  # noqa: E402

SEED = 20260924
E4 = [[F(int(i == j)) for j in range(4)] for i in range(4)]


def dim(vs):
    vs = [v for v in vs if any(x != 0 for x in v)]
    return rank_exact(vs) if vs else 0


def cap(A, B):
    return dim(A) + dim(B) - dim(list(A) + list(B))


def kperp(vs):
    """Klein-orthogonal complement in Lambda^2 K^4."""
    return nullspace([hodge_star(v) for v in vs]) if vs else [r[:] for r in
                                                                [[F(int(i == j)) for j in range(6)] for i in range(6)]]


def hom(q, z):
    return [q[0], q[1], z, F(1)]


def ev(h, qq):
    return h[0] * qq[0] + h[1] * qq[1] + h[2]


def normal(h):
    return [h[0], h[1], F(-1), h[2]]


def nbrs(E):
    nb = {}
    for (u, w) in E:
        nb.setdefault(u, set()).add(w)
        nb.setdefault(w, set()).add(u)
    return nb


def connected(E):
    nb = nbrs(E)
    V = list(nb)
    seen, st = {V[0]}, [V[0]]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == len(V)


def satisfies_H(E):
    nb = nbrs(E)
    return is_simple(E) and connected(E) and min(len(s) for s in nb.values()) >= 2


def rel(M, V, a, b):
    ia, ib = V.index(a), V.index(b)
    return [[X[6 * ib + t] - X[6 * ia + t] for t in range(6)] for X in M]


def lambda2_plane(nrm):
    P = nullspace([nrm])
    return [wedge2(P[i], P[j]) for i in range(3) for j in range(i + 1, 3)]


def series_limit(A0, A1, ncols_m, want, kmax=6):
    """x0-projections (first ncols_m coordinates) of the K[[s]]-kernel of
    A0 + s A1, truncated at order k, until the dimension drops to `want`."""
    R, C = len(A0), len(A0[0])
    Z = [[F(0)] * C for _ in range(R)]
    for k in range(kmax + 1):
        big = []
        for i in range(k + 1):              # block row i: A1 x_{i-1} + A0 x_i
            for rr in range(R):
                row = []
                for j in range(k + 1):
                    blk = A0 if j == i else (A1 if j == i - 1 else Z)
                    row.extend(blk[rr])
                big.append(row)
        K = nullspace(big)
        proj = [v[:ncols_m] for v in K]
        d = dim(proj)
        if d <= want:
            basis = []
            for v in proj:
                if dim(basis + [v]) > len(basis):
                    basis.append(v)
            return basis, k
    return None, kmax


def pen(y, v):
    """Pen(y, <y, n, v>) is spanned by n and y ^ v; returned: the two lines."""
    return wedge2(y, v)


def chord_instance(label, E, a, b, rng, nz1=2, want_truth=True):
    V = verts_of(E)
    nV = len(V)
    f = def_k(E, 6)
    f2 = def_k(E, 3)
    vs = [v for v in V if v != b]
    Eab = contract(E, a, b)
    delta = f - def_k(Eab, 6, vs)
    delta2 = f2 - def_k(Eab, 3, vs)
    Ec = E + [(a, b)]
    tgt_c = 6 * (nV - 1) - def_k(Ec, 6)
    d2c = def_k(Ec, 3)
    nb = nbrs(E)
    common = bool(nb[a] & nb[b])
    got = None
    for _ in range(8):
        try:
            q = sample_q(rng, V, Ec, 30)
            L = lifting_space(E, V, q)
            Lc = lifting_space(Ec, V, q)
        except (AssertionError, RuntimeError):
            continue
        if len(L) != 3 + f2 or len(Lc) != 3 + d2c:
            continue
        coeff = [rng.randint(-30, 30) for _ in Lc]
        z = [sum(c * bb[t] for c, bb in zip(coeff, Lc)) for t in range(nV)]
        pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
        if rank_modp(build_rigidity(Ec, pt)[0]) == tgt_c:
            got = (q, L, Lc, z, pt)
            break
    if got is None:
        return dict(label=label, delta=delta, delta2=delta2, status='no certified chord point')
    q, L, Lc, z, pt = got
    ia, ib = V.index(a), V.index(b)
    Hs = [_interp(E, V, q, bb) for bb in L]
    dU = dim([[x - y for x, y in zip(hh[a], hh[b])] for hh in Hs])
    fg = dim([[bb[ib] - ev(hh[a], q[b]), bb[ia] - ev(hh[b], q[a])] for bb, hh in zip(L, Hs)])
    M = nullspace(build_rigidity(E, pt)[0])
    rho = rel(M, V, a, b)
    r = dim(rho)
    ap = len(M) - 6 - f
    pa, pb = hom(q[a], z[ia]), hom(q[b], z[ib])
    n = wedge2(pa, pb)
    cn = cap(rho, [n])
    nperp = kperp([n])
    rn = cap(rho, nperp)
    bar = all(dot(x, hodge_star(n)) == 0 for x in rho)
    h0 = _interp(E, V, q, z)
    caseB = tuple(h0[a]) == tuple(h0[b])
    rec = dict(label=label, n=nV, delta=delta, delta2=delta2, f=f, dU=dU, fg=fg,
               common=common, ap=ap, r=r, cn=cn, rn=rn, bar=bar, caseB=caseB,
               status='ok')
    if delta <= 5:
        assert cn == 0 and r == delta + ap, ('chord identity', label)
    if caseB:
        rec['rho_pi'] = cap(rho, lambda2_plane(normal(h0[a])))
    # the delta-dimensional limit rhobar(z1) and the Track-B bound
    A0 = aug_matrix(E, V, pt)
    best = None
    lims = []
    for _ in range(nz1):
        c1 = [rng.randint(-30, 30) for _ in L]
        z1 = [sum(cc * bb[s] for cc, bb in zip(c1, L)) for s in range(nV)]
        pt1 = {v: (q[v][0], q[v][1], z[t] + z1[t]) for t, v in enumerate(V)}
        A01 = aug_matrix(E, V, pt1)
        A1 = [[x - y for x, y in zip(r1, r0)] for r1, r0 in zip(A01, A0)]
        Mbar, kk = series_limit(A0, A1, 6 * nV, 6 + f)
        if Mbar is None:
            lims.append(('no limit', None))
            continue
        rbar = rel(Mbar, V, a, b)
        drb = dim(rbar)
        # phi1(z1), phi2(z1): the incidence functionals in direction z1
        h1 = _interp(E, V, q, z1)
        ph1 = z1[ib] - ev(h1[a], q[b])
        ph2 = z1[ia] - ev(h1[b], q[a])
        # (MC-108): sigma(t) = ker((1-t) phi2 alpha - t phi1 beta), alpha/beta
        # the plane functionals of pi_a, pi_b at z0 (x,y,z,w) -> z - h(x,y) w
        alpha = [-h0[a][0], -h0[a][1], F(1), -h0[a][2]]
        beta = [-h0[b][0], -h0[b][1], F(1), -h0[b][2]]
        kmin = None
        if not caseB:
            for tnum in (1, 2, 3, 5):
                t = F(tnum, 7)
                y0 = [(1 - t) * x + t * w for x, w in zip(pa, pb)]
                gam = [(1 - t) * ph2 * x - t * ph1 * w for x, w in zip(alpha, beta)]
                if all(x == 0 for x in gam):
                    continue
                # a point v of sigma(t) off n: solve gam . v = 0, v not in <pa, pb>
                S = nullspace([gam])
                v = next(s for s in S if dim([pa, pb, s]) == 3)
                P = [n, wedge2(y0, v)]
                assert dim(P) == 2
                c = cap(rbar, P)
                kmin = c if kmin is None else min(kmin, c)
        lims.append((drb, cap(rbar, nperp), kk, kmin))
        if kmin is not None:
            best = kmin if best is None else min(best, kmin)
    rec['lims'] = lims
    rec['best'] = best
    if want_truth:
        rec['truth'] = truth_G(E, a, b, rng)
    return rec


def truth_G(E, a, b, rng, tries=4):
    G = E + [(a, 'y'), ('y', b)]
    V = verts_of(G)
    nV = len(V)
    d2 = def_k(G, 3)
    tgt = 6 * (nV - 1) - def_k(G, 6)
    best = None
    for _ in range(tries):
        try:
            q = sample_q(rng, V, G, 30)
            L = lifting_space(G, V, q)
        except (AssertionError, RuntimeError):
            continue
        if len(L) != 3 + d2:
            continue
        coeff = [rng.randint(-30, 30) for _ in L]
        z = [sum(c * bb[t] for c, bb in zip(coeff, L)) for t in range(nV)]
        pt = {v: (q[v][0], q[v][1], z[t]) for t, v in enumerate(V)}
        rk = rank_modp(build_rigidity(G, pt)[0])
        best = rk if best is None else max(best, rk)
        if rk == tgt:
            return 'ATTAINS'
    return f'short {best}/{tgt}' if best is not None else 'no certified q'


# ------------------------------------------------------------ populations

def k1_chains(E):
    """(a, b, y): y of degree 2 with neighbours a, b of degree >= 3, a !~ b."""
    nb = nbrs(E)
    adj = {frozenset(e) for e in E}
    out = []
    for y in sorted(nb, key=str):
        if len(nb[y]) != 2:
            continue
        a, b = sorted(nb[y], key=str)
        if len(nb[a]) >= 3 and len(nb[b]) >= 3 and frozenset((a, b)) not in adj:
            out.append((a, b, y))
    return out


def from_members(pop):
    out = []
    for name, E in pop:
        if not is_simple(E):
            continue
        for (a, b, y) in k1_chains(E):
            Gp = [(u, w) for (u, w) in E if y not in (u, w)]
            out.append((f'{name}:{a}-{b}', Gp, a, b))
    return out


def subdivide(base, lens):
    E, nxt = [], 1000
    for (u, w), L in zip(base, lens):
        prev = u
        for _ in range(L - 1):
            E.append((prev, nxt))
            prev = nxt
            nxt += 1
        E.append((prev, w))
    return E


BASES = {
    'K4': [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
    'K33': [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)],
    'prism': [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)],
    'W4': [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4), (4, 1)],
}


def subdiv_pop(base, maxlen, nsample, rng, maxn):
    B = BASES[base]
    out, seen = [], set()
    tries = 0
    while len(out) < nsample and tries < 50 * nsample:
        tries += 1
        lens = tuple(rng.randint(1, maxlen) for _ in B)
        if 2 not in lens or lens in seen:
            continue
        E = subdivide(B, lens)
        if len(verts_of(E)) > maxn or not is_simple(E):
            continue
        seen.add(lens)
        out.append((f'{base}:' + ''.join(map(str, lens)), E))
    return out


def run(insts, title, args):
    t0 = time.time()
    hist = {}
    for (label, E, a, b) in insts:
        if not satisfies_H(E):
            continue
        rng = random.Random(f'{SEED}:{label}')
        rec = chord_instance(label, E, a, b, rng, nz1=args.nz1, want_truth=not args.notruth)
        if rec['status'] != 'ok':
            key = ('--', rec['delta'], rec['status'])
        else:
            key = (rec['delta'], rec['delta2'], rec['dU'], 'B' if rec['caseB'] else 'A', rec['ap'],
                   rec['r'], rec['rn'], rec['bar'], rec.get('rho_pi'), rec['best'],
                   rec.get('truth'))
        hist.setdefault(key, []).append(label)
        if args.verbose:
            print(rec, flush=True)
    print(f'-- {title}: key = (delta, delta2, dim U, case, a\'(z0), r(z0), dim(rho cap n^perp), '
          'rho in n^perp, [case B] dim(rho cap L2 pi), min dim(rhobar cap limit pencil), truth)')
    for key in sorted(hist, key=str):
        ex = hist[key][:3]
        print(f'   {key}: {len(hist[key])}   e.g. {ex}')
    print(f'{title}: {sum(len(v) for v in hist.values())} instances; {time.time() - t0:.1f} s')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--thetas', type=int, default=0)
    ap.add_argument('--habitats', action='store_true')
    ap.add_argument('--stride', type=int, default=1)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--subdiv', default='')
    ap.add_argument('--maxlen', type=int, default=4)
    ap.add_argument('--nsample', type=int, default=20)
    ap.add_argument('--maxn', type=int, default=16)
    ap.add_argument('--nz1', type=int, default=2)
    ap.add_argument('--notruth', action='store_true')
    ap.add_argument('--mindelta', type=int, default=0)
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--nmin', type=int, default=3)
    args = ap.parse_args()
    print(f'# chordprobe.py seed={SEED}')
    if args.thetas:
        from maincomp import thetas
        insts = from_members(thetas(args.thetas))
        run(insts, f'thetas <= {args.thetas}', args)
    if args.habitats:
        from maincomp import habitats
        pop = habitats()[::args.stride]
        if args.limit:
            pop = pop[:args.limit]
        run(from_members(pop), f'habitats stride {args.stride} ({len(pop)} members)', args)
    if args.exh:
        from maincomp import two_ec_graphs
        pop = [(nm, E) for nm, E in two_ec_graphs(args.exh, args.nmin)]
        run(from_members(pop), f'exh {args.nmin}..{args.exh} ({len(pop)} graphs)', args)
    if args.subdiv:
        rng = random.Random(f'{SEED}:subdiv:{args.subdiv}:{args.maxlen}')
        pop = subdiv_pop(args.subdiv, args.maxlen, args.nsample, rng, args.maxn)
        insts = from_members(pop)
        if args.mindelta:
            keep = []
            for (label, E, a, b) in insts:
                V = verts_of(E)
                vs = [v for v in V if v != b]
                if def_k(E, 6) - def_k(contract(E, a, b), 6, vs) >= args.mindelta:
                    keep.append((label, E, a, b))
            insts = keep
        run(insts, f'subdiv {args.subdiv} maxlen {args.maxlen} ({len(pop)} graphs)', args)


if __name__ == '__main__' and '--random' not in sys.argv:
    main()


# ------------------------------------------------------------ random sparse G'
# (appended 2026-09-24 for the Case-A a'(z0) hunt; `python3 chordprobe.py`'s
#  main() is not changed -- use `--random` via randmain below)

def random_Gp(rng, n, extra):
    """A random connected simple graph on n vertices, min degree >= 2: a random
    Hamilton cycle plus `extra` random chords (sampler support: uniform
    permutation, uniform non-edges)."""
    perm = list(range(n))
    rng.shuffle(perm)
    E = {frozenset((perm[i], perm[(i + 1) % n])) for i in range(n)}
    tries = 0
    while len(E) < n + extra and tries < 1000:
        tries += 1
        u, w = rng.sample(range(n), 2)
        E.add(frozenset((u, w)))
    return sorted(tuple(sorted(e)) for e in E)


def randmain(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument('--random', type=int, default=30)
    ap.add_argument('--nmin', type=int, default=9)
    ap.add_argument('--nmax', type=int, default=13)
    ap.add_argument('--extra', type=int, default=2)
    ap.add_argument('--mindelta', type=int, default=1)
    ap.add_argument('--mind2', type=int, default=3)
    ap.add_argument('--nz1', type=int, default=0)
    ap.add_argument('--verbose', action='store_true')
    ap.add_argument('--notruth', action='store_true')
    args = ap.parse_args(argv)
    rng = random.Random(f'{SEED}:random:{args.nmin}:{args.nmax}:{args.extra}')
    insts = []
    g = 0
    while g < args.random:
        n = rng.randint(args.nmin, args.nmax)
        E = random_Gp(rng, n, rng.randint(0, args.extra))
        if not satisfies_H(E):
            continue
        g += 1
        nb = nbrs(E)
        V = verts_of(E)
        f, f2 = def_k(E, 6), def_k(E, 3)
        for a, b in itertools.combinations(V, 2):
            if b in nb[a] or nb[a] & nb[b]:
                continue
            vs = [v for v in V if v != b]
            Eab = contract(E, a, b)
            d = f - def_k(Eab, 6, vs)
            d2 = f2 - def_k(Eab, 3, vs)
            if d >= args.mindelta and d2 >= args.mind2:
                insts.append((f'r{g}n{n}:{a}-{b}', E, a, b))
    run(insts, f'random G\' ({args.random} graphs, n {args.nmin}..{args.nmax}, '
               f'delta >= {args.mindelta}, delta2 >= {args.mind2})', args)


if __name__ == '__main__' and '--random' in sys.argv:
    print(f'# chordprobe.py seed={SEED}')
    randmain(sys.argv[1:])
