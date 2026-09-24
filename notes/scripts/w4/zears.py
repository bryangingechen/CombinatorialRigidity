"""zears.py -- §(K-main) Step MC19 (Track E): the reach of the Z-ear induction on the A-prime graphs.

A feasible graph G (F1 and F2) that is not a cycle has a maximal chain (ear) a - x1 - ... - xk - b
between hubs.  Removing its interior gives G' (feasible).  The Z-ear transfer (writeup (MC-126)):
Y := closure(Z(G') x placements) equals Z(G) as soon as Y's generic point satisfies conjunct 3 for
G; then the rank question on Z(G) is Step MC10/MC13's ear question at Z(G')'s generic point, with
dominance automatic.  A graph is Z-COVERED if it is not A-prime (then Z = X0 and the base is
(MC-10)(a) at it, assumed), or some ear removal gives a Z-covered G' with the step's cell closed:

  closed ear (a = b), open k >= 5          unconditional                      (MC-20)
  open k = 4                               antecedent G'+ear2 Z-covered        (MC-24),(MC-25)
  open k = 3                               antecedent G'+ear2 Z-covered        (MC-45)
  open k = 2                               orbit (i)/(ii) at Z(G'), a !~ b,
                                           antecedent G'+ear1 Z-covered        (MC-46)
  open k = 1                               delta = 0, orbit != (iii)           (MC-54)

Per step, certified at ONE seeded exact draw (each is an open condition on an irreducible family, so
one witness proves the generic statement): conjunct 3 (all four conjuncts) for G at a point of Y;
the flag orbit at Z(G').  delta = def3(G') - def3(G'/ab) is exact (pebble game).  The A-prime test
is (MC-14)'s combinatorial one (mod Jackson--Jordan); a non-A-prime base is also certified
nondegenerate on X0 by maincomp's sampler.

    PYTHONHASHSEED=0 python3 zears.py --exh 8
"""
import argparse
import random
from fractions import Fraction as F

from zcore import (F1, F2, chn, hubs_of, def3, zdraw, complete_normals, nondeg, intvec,
                   verts_of, dot, rank_p, target)
from zsurvey import is_Aprime
from exactcore import neighbors, nullspace, rank as rank_q
from maincomp import two_ec_graphs, canon, probe
from flanks import nondeg_conjuncts
from nogood_subdiv import branch_decomposition

SEED = 20260924
RANKS = []   # (graph key, rank at the certified Y-draw == target) -- a cross-check of (MC-126)


def relabel(E):
    V = verts_of(E)
    idx = {v: i for i, v in enumerate(V)}
    return len(V), [(idx[u], idx[w]) for u, w in E]


def key(E):
    n, E2 = relabel(E)
    return (n, canon(n, E2))


def satisfies_H(E):
    V = verts_of(E)
    nb = neighbors(E)
    if any(len(nb[v]) < 2 for v in V):
        return False
    seen, st = {V[0]}, [V[0]]
    while st:
        v = st.pop()
        for w in nb[v]:
            if w not in seen:
                seen.add(w)
                st.append(w)
    return len(seen) == len(V)


def is_cycle(E):
    nb = neighbors(E)
    return all(len(nb[v]) == 2 for v in nb)


def plane_of(E, normal_hub, pt, v):
    """G's plane at v: the hub normal if v is a hub, else the normal of N[v]'s points."""
    if v in normal_hub:
        return normal_hub[v]
    nb = neighbors(E)
    ns = nullspace([[F(x) for x in pt[w]] for w in [v] + list(nb[v])])
    assert len(ns) == 1, ('non-hub star degenerate', v)
    return intvec(ns[0])


def orbit(E, n, pt, a, b):
    na, nb_ = plane_of(E, n, pt, a), plane_of(E, n, pt, b)
    if rank_q([[F(x) for x in na], [F(x) for x in nb_]]) < 2:
        return 'iv'
    i1 = dot(pt[a], nb_) == 0
    i2 = dot(pt[b], na) == 0
    return {0: 'i', 1: 'ii', 2: 'iii'}[i1 + i2]


def ear_edges(a, b, names):
    path = [a] + names + [b]
    return [(path[i], path[i + 1]) for i in range(len(path) - 1)]


def place_and_check(E, Ep, a, b, xs, rng, S=30, tries=6):
    """Draw a point of Z(G'), place the ear, check all four conjuncts for G = E.  Also return the flag
    orbit at the Z(G') draw."""
    last = None
    for t in range(tries):
        r = zdraw(Ep, rng, S)
        if r is None:
            continue
        n, pt = r
        orb = orbit(Ep, n, pt, a, b)
        last = orb
        na, nb_ = plane_of(Ep, n, pt, a), plane_of(Ep, n, pt, b)
        pt = dict(pt)
        k = len(xs)

        def rnd_in(rows):
            B = nullspace([[F(x) for x in r_] for r_ in rows]) if rows else \
                [[F(int(i == j)) for j in range(4)] for i in range(4)]
            c = [rng.randint(-S, S) for _ in B]
            return intvec([sum(ci * bb[m] for ci, bb in zip(c, B)) for m in range(4)])
        if k == 1:
            pt[xs[0]] = rnd_in([na, nb_])
        else:
            pt[xs[0]] = rnd_in([na])
            pt[xs[-1]] = rnd_in([nb_])
            for x in xs[1:-1]:
                pt[x] = rnd_in([])
        if any(not any(pt[x]) for x in xs):
            continue
        # G's hub normals: G'-hub normals, plus the G'-plane of any new hub
        Hn = {}
        HG = hubs_of(E)
        for h in HG:
            Hn[h] = n[h] if h in n else plane_of(Ep, n, pt, h)
        normal = complete_normals(E, Hn, pt)
        ok, why = nondeg(E, normal, pt)
        if ok:
            RANKS.append((key(E), rank_p(E, pt) == target(E)))
            return True, orb
    return False, last


def delta(Ep, a, b):
    Em = [(a if u == b else u, a if w == b else w) for u, w in Ep]
    return def3(Ep) - def3(Em)


class Cover:
    def __init__(self, verbose=False):
        self.memo = {}
        self.verbose = verbose

    def base_certified(self, E, name):
        """non-A-prime: certify X0's generic point nondegenerate at one maincomp draw."""
        for t in range(4):
            rng = random.Random(f'{SEED}:base:{name}:{t}')
            try:
                r = probe(E, rng, 30)
            except Exception:
                continue
            ok, info = nondeg_conjuncts(E, r['pt'])
            if ok:
                return True
        return False

    def covered(self, E, name='G', depth=0):
        k_ = key(E)
        if k_ in self.memo:
            return self.memo[k_]
        self.memo[k_] = (False, 'in progress')
        res = self._covered(E, name, depth)
        self.memo[k_] = res
        return res

    def _covered(self, E, name, depth):
        if not (F1(E) and F2(E)):
            return (False, 'infeasible')
        if is_cycle(E):
            return (True, 'BASE cycle')
        if not is_Aprime(E):
            return (True, 'BASE non-A-prime' + ('' if self.base_certified(E, name) else ' (X0-nondeg NOT certified)'))
        hubs, branches = branch_decomposition(E)
        fails = []
        for (a, b, interior) in branches:
            k = len(interior)
            if k == 0:
                continue
            Ep = [e for e in E if not (set(e) & set(interior))]
            if not satisfies_H(Ep):
                fails.append((a, b, k, 'G-ear fails (H)'))
                continue
            rng = random.Random(f'{SEED}:{name}:{a}:{b}:{k}')
            ok3, orb = place_and_check(E, Ep, a, b, interior, rng)
            if not ok3:
                fails.append((a, b, k, f'conj3 at Y not certified (orbit {orb})'))
                continue
            sub = self.covered(Ep, name + "'", depth + 1)
            if not sub[0]:
                fails.append((a, b, k, "G' not covered: " + str(sub[1])[:60]))
                continue
            if a == b or k >= 5:
                return (True, f'EAR k={k} {"closed" if a == b else "open"} -> ' + sub[1][:40])
            nbE = neighbors(Ep)
            adj = b in nbE[a]
            if k in (3, 4):
                ante = Ep + ear_edges(a, b, [('y', 1), ('y', 2)])
                s2 = self.covered(ante, name + '+e2', depth + 1)
                if s2[0]:
                    return (True, f'EAR k={k} (antecedent ear2 covered)')
                fails.append((a, b, k, 'antecedent ear2 not covered'))
                continue
            if k == 2:
                if adj or orb not in ('i', 'ii'):
                    fails.append((a, b, k, f'k=2 cell: adj={adj} orbit={orb}'))
                    continue
                ante = Ep + ear_edges(a, b, [('y', 1)])
                s1 = self.covered(ante, name + '+e1', depth + 1)
                if s1[0]:
                    return (True, f'EAR k=2 orbit {orb} (antecedent ear1 covered)')
                fails.append((a, b, k, 'antecedent ear1 not covered'))
                continue
            if k == 1:
                d = delta(Ep, a, b)
                if d == 0 and orb != 'iii':
                    return (True, f'EAR k=1 delta=0 orbit {orb} -> ' + sub[1][:40])
                fails.append((a, b, k, f'k=1 cell: delta={d} orbit={orb}'))
        return (False, fails)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--exh', type=int, default=8)
    a = ap.parse_args()
    C = Cover()
    tot = 0
    cov = 0
    steps = {}
    for name, E in two_ec_graphs(a.exh):
        if not (F1(E) and F2(E)) or not is_Aprime(E):
            continue
        tot += 1
        ok, info = C.covered(E, name)
        if ok:
            cov += 1
            s = info.split(' ->')[0].split(' (')[0]
            steps[s] = steps.get(s, 0) + 1
            print(f'  {name}: covered, first step {info}')
        else:
            print(f'  {name}: NOT covered; per ear: {info}')
    print(f'exh{a.exh}: A-prime {tot}, Z-ear covered {cov}; first steps {steps}')
    good = sum(1 for _, r in RANKS if r)
    print(f'cross-check: rank at the certified Y-draw equals the target at {good}/{len(RANKS)} ear placements tried')


if __name__ == '__main__':
    main()
