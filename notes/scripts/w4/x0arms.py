#!/usr/bin/env python3
"""
x0arms.py -- which graphs the X0 induction reaches (W4 reopened, P1 step 4;
workbook §(K-main) Step MC14, claims (MC-52)-(MC-61)).

The motive (§(K-main) (MC-10)(a)): "the generic point of the main component
X0(G) attains 6(|V|-1) - def3(G)", for G satisfying (H) (finite, simple,
connected, minimum degree >= 2).  A graph G is COVERED if some landed step
applies at G and every smaller graph the step consumes is covered.  Every step
consumes graphs with fewer vertices, so "covered" is a least fixed point on
|V| and does not depend on the order in which steps are tried.  The order
below is only the order in which the FIRST covering step is reported.

The steps (what each consumes; whether its applicability is structural or
needs a per-graph certificate):
  BASE      G a cycle.  (MC-21)(a)'s base.  Structural.  Consumes nothing.
  THETA     G a theta graph (exactly two vertices of degree 3, the others of
            degree 2, 2-edge-connected).
            (MC-21)(b).  Structural.  Consumes nothing.
  CUT       a cut vertex z and a split G = G1 u_z G2 with deg_{Gi}(z) >= 2.
            (MC-52).  Structural.  Consumes G1, G2.
  BRIDGE    a maximal chain (possibly one edge) all of whose edges are
            bridges; G - interior = G1 + G2.  (MC-53).  Structural.
            Consumes G1, G2.
  EAR       a maximal chain with k interior vertices, ends a, b, G' = G -
            interior satisfying (H):  closed (a = b) or open with k >= 5
            ((MC-20); consumes G');  open k = 4 ((MC-24)/(MC-25); consumes G'
            and the gadget G' + ear_2);  open k = 2, 3 only under `--ear23`
            (Step MC13): consumes G' and G' + ear_{k-1}.  `--ear23 landed` is
            the landed cells: k = 3 in every orbit ((MC-45)); k = 2 when
            X0(G')'s generic flag pair is in orbit (i), CERTIFIED at one q with
            dim L(q) = 3 + def2(G') (exact Q; both incidence functionals
            nonzero on F(G', q)), and dim U >= 2 at that q (a lower bound for
            the generic dim U, so a certificate of dim U != 1: (MC-46), whose
            orbit (ii) half the driver does not certify, and (MC-18)(b)'s
            dominance of the 1-ear gadget).  `--ear23 landed+u1` also admits
            k = 2 at dim U = 1 in orbit (i): the OPEN cell (MC-51)(a), kept only
            as a sensitivity check.  Every evaluated
            (k, orbit, dim U) cell is tallied in the certificates line.
            Open k = 1 ((MC-27) is OPEN at r >= 1): only at delta = 0, where
            r <= delta forces rho = 0 so (R_1) and (P_1) are empty, and (MC-22)
            closes the step given dominance and lambda = 2 -- certified by dim U
            >= 2 at one q in U(G') (a lower bound for the generic dim U, so
            dim U != 1, and dim U >= 2 excludes orbit (iii)).  (MC-54).
            Consumes G'.  `--ear1 none` drops it.
  SPLITOFF  a degree-2 x with non-adjacent neighbours a, b and delta =
            def3(G-x) - def3((G-x)/ab) >= 5.  (MC-31).  Structural, plus
            Jackson-Jordan at G'' = G.splitOff x a b (see `--jj`).  Consumes G''.
  FLAT      def2(G) = def3(G).  (MC-5)(ii) plus Jackson-Jordan at G (see
            `--jj`).  Consumes nothing.
  CONTRACT  G 2-edge-connected, W a proper rigid vertex set (def3(G[W]) = 0)
            with G/H simple, and (MC-39)'s (i) core-free and (ii) no-jump
            CERTIFIED at one exact picture (`coreshrink.run_member`, relaxed
            variant: q in U(G), q|W in U(H) and q(t) in U certified).
            Consumes H = G[W] and G/H.
Jackson-Jordan (`--jj`): `cert` (default) exhibits, per graph, one admissible q
with dim L(q) = 3 + def2 (up to 3 draws, exact Q); that q is in U, so ell0 =
3 + def2 there and the step needs no citation.  `cite` accepts the equality
as the cited theorem (characteristic 0; (MC-33) beyond).

Modes (run from the repository root; seed 20260924; writes nothing):

    python3 notes/scripts/w4/x0arms.py --lemmas
    python3 notes/scripts/w4/x0arms.py --exh N [--ear23 {none,landed,landed+u1}] [--list]
    python3 notes/scripts/w4/x0arms.py --pool NAME[,NAME] [--ear23 ...] [--stride K]
    python3 notes/scripts/w4/x0arms.py --necklace KMAX [--ear23 ...]
    python3 notes/scripts/w4/x0arms.py --round1 [--ear23 ...]
    python3 notes/scripts/w4/x0arms.py --tree NAME[,NAME] [--depth D]
  common: [--ear1 {delta0,none}] [--jj {cert,cite}] [--contract {cert,cert-core,struct,off}]
          [--cert-nmax N] [--show S]

`--lemmas` checks the cut-vertex, bridge-path and leaf lemmas ((MC-52), (MC-53),
(MC-54)) at 2 drawn points of B(G) per glued instance: the deficiency counts
(def3 and def2 additive; + (k+1) along a bridge path of k interior vertices;
+ 1 at a leaf), dim L_G(q) against the pieces (- 3; - 2, - 1, + (k-2) for
k = 0, 1, >= 2; equal at a leaf), both restriction maps surjective, and the
rank identity rank_G = rank_1 + rank_2 (+ 5(k+1); + 5 at a leaf), mod p (the
identity is field-free, so it holds mod p exactly).  All ASSERTED.
`--exh N`: every simple 2EC graph on 3..N vertices (`maincomp.two_ec_graphs`),
EXHAUSTIVE.  Per n, the count by first covering step; then every uncovered
graph with n, m, def2, def3, whether a proper rigid set exists, whether a
degree-2 vertex exists, the number of 2-edge-cuts, its chains, and what
blocks each applicable step.  `--pool NAME`: maincomp's populations (members
kept iff simple and 2EC); per member covered or not, and for an uncovered one
the TERMINAL uncovered graphs its steps reach (graphs where a step applies but
a consumed graph is uncovered are followed; a graph with no applicable step,
or whose steps fail only a certificate, is terminal).  `--necklace KMAX`: the
K4 necklaces N(k), k = 3..KMAX (k copies of K4 in a cycle, bead i's vertex 1
joined to bead i+1's vertex 0); def2 = k - 3 and def3 = max(0, k - 6)
ASSERTED, every bead's contraction simple ASSERTED; coverage; and an X0
attaining certificate per k (`maincomp.census`, 1 draw + 4 retries, rank mod
2^61-1: a certificate when equal to the target).  `--round1`: the 48 graphs on
<= 8 vertices that the hybrid recon's scratch classifier (2026-09-24,
not retained) left with no applicable arm (`ROUND1_REST`, canonical names),
tallied by first covering step.  `--tree NAME`: the covering tree of a
canonical name `x<n>_<code>` (`maincomp`'s naming), or what blocks it; `--depth
0` prints the root line only.  `--show S` (pools): list S uncovered members.
A graph's SPLITOFF assert: def3 rises by exactly 1 when delta >= 5 ((MC-29)(a)).

`--contract`: `cert` (default) requires (i)/(ii) certified, for graphs with at
most `--cert-nmax` vertices (default 40; a larger graph's CONTRACT is reported
uncertified and not used); `cert-core` also allows, after every W has failed
that, (MC-39)'s last sentence (CONTRACT*): (ii) certified and the core rigid
(mod-p rank 6(|W|-1)) at the sampled points p(t) of B(G), q(t) in U certified
-- consuming G/H only.  That certificate is a rank check on G's own framework,
of the census's kind, so it is reported apart; `struct` accepts CONTRACT
wherever a W with G/H simple exists and H, G/H are covered (reported as
CONTRACT?, NOT a proof); `off` drops the step.  Rigid-set enumeration: complete by vertex subsets when
n <= 14, else complete by branch unions (`nogood_subdiv.rigid_vertex_sets`)
when there are <= 16 branches, else a SUFFICIENT search (closures of the
vertex sets of cycles of length <= 6 under adding a vertex with two
neighbours inside, or a path of <= 5 interior vertices with both ends inside;
every set asserted rigid by the pebble game) -- counted and printed as
`rigid-search incomplete` wherever it is used.

Sampler support (HARNESS.md *Evidence*): JJ and orbit pictures `q` uniform on
[-30, 30]^{2|V|} integers (`maincomp.sample_q`), rejected until admissible, up
to 3 per graph, seeded by the canonical code; CONTRACT's pictures are
`coreshrink`'s (its docstring).  Fenced constants: scale 30, 3 JJ draws, 5
CONTRACT redraws.  Every certificate is exact (Q) or a mod-p rank equal to
its target.  A graph reported uncovered is uncovered BY THESE STEPS UNDER
THESE CERTIFICATES: a failed certificate is "not exhibited under the cap",
never a refutation.  Deterministic at PYTHONHASHSEED=0 apart from the
`-- ... N s` timing lines.
"""
import argparse
import os
import random
import sys
import time
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from fractions import Fraction as F  # noqa: E402

from exactcore import rank as rank_exact, neighbors  # noqa: E402
from kbare_common import (verts_of, is_2ec, split_off, rank_modp,  # noqa: E402
                          build_rigidity, verify_pencil_witness)
from maincomp import (def_k, lifting_space, sample_q, canon, decode,  # noqa: E402
                      two_ec_graphs, census)
from nogood_subdiv import (rigid_vertex_sets, contraction, is_simple,  # noqa: E402
                           branch_decomposition, deficiency as def3_pebble)
from splitext import flex_space, contract as merge_pair  # noqa: E402

SEED = 20260924
SCALE = 30
JJ_DRAWS = 3
ORDER = ('BASE', 'THETA', 'CUT', 'BRIDGE', 'EAR-closed', 'EAR-k5+', 'EAR-k4',
         'EAR-k3', 'EAR-k2', 'SPLITOFF', 'FLAT', 'EAR-k1', 'CONTRACT', 'CONTRACT*', 'CONTRACT?')
# the k = 2, 3 open-ear cells, per `--ear23` value: (k, orbit, dim U) -> applies
EAR23 = {'none': None,
         'landed': lambda k, orb, dU: k == 3 or (orb == 'i' and dU >= 2),
         'landed+u1': lambda k, orb, dU: k == 3 or orb == 'i'}


# ---------------------------------------------------------------- graphs

def relabel(E):
    V = verts_of(E)
    idx = {v: i for i, v in enumerate(V)}
    return len(V), [(idx[u], idx[w]) for (u, w) in E]


def key_of(E):
    n, R = relabel(E)
    return (n, canon(n, R))


def name_of(key):
    return f'x{key[0]}_{key[1]}'


def graph(key):
    return decode(*key)


def components(E, V=None):
    nb = neighbors(E)
    V = sorted(nb, key=str) if V is None else V
    seen, out = set(), []
    for s in V:
        if s in seen:
            continue
        comp, st = {s}, [s]
        while st:
            u = st.pop()
            for y in nb.get(u, ()):
                if y not in comp:
                    comp.add(y)
                    st.append(y)
        seen |= comp
        out.append(comp)
    return out


def induced(E, W):
    Ws = set(W)
    return [e for e in E if e[0] in Ws and e[1] in Ws]


def is_cycle(E):
    nb = neighbors(E)
    return all(len(s) == 2 for s in nb.values()) and len(components(E)) == 1


def is_theta(E):
    nb = neighbors(E)
    deg = Counter(len(s) for s in nb.values())
    return deg[3] == 2 and deg[2] == len(nb) - 2 and is_2ec(E)


def satisfies_h(key):
    """(H) for a canonical key: simple (by construction), connected, min degree >= 2."""
    E = graph(key)
    nb = neighbors(E)
    return len(nb) == key[0] and min(len(s) for s in nb.values()) >= 2 and len(components(E)) == 1


def two_edge_cuts(E):
    V = verts_of(E)
    c = 0
    for i in range(len(E)):
        for j in range(i + 1, len(E)):
            rest = [e for k, e in enumerate(E) if k != i and k != j]
            c += len(components(rest, V)) > 1
    return c


def ear_edges(a, b, k, fresh):
    """An open a-b path with k fresh interior vertices fresh, fresh+1, ..."""
    path = [a] + [fresh + i for i in range(k)] + [b]
    return list(zip(path, path[1:]))


# ---------------------------------------------------------------- rigid sets

def cycle_sets(E, L=6):
    """Vertex sets of the cycles of length <= L (bounded DFS)."""
    nb = neighbors(E)
    V = sorted(nb)
    out = set()
    for s in V:
        stack = [(s, [s])]
        while stack:
            u, path = stack.pop()
            for w in nb[u]:
                if w == s and len(path) >= 3:
                    out.add(frozenset(path))
                elif w > s and w not in path and len(path) < L:
                    stack.append((w, path + [w]))
    return out


def rigid_sets(E):
    """(proper rigid vertex sets, complete?)."""
    V = verts_of(E)
    n = len(V)
    nb = neighbors(E)
    hubs, br = branch_decomposition(E)
    if br is None:
        return [], True
    out = set()

    def test(W):
        if len(W) < 3 or len(W) >= n:
            return False
        ie = induced(E, W)
        dg = Counter()
        for u, w in ie:
            dg[u] += 1
            dg[w] += 1
        if any(dg[v] < 2 for v in W) or 5 * len(ie) < 6 * (len(W) - 1):
            return False
        return def3_pebble(ie, sorted(W, key=str)) == 0
    if n <= 14:
        for mask in range(1, 1 << n):
            W = frozenset(V[i] for i in range(n) if mask >> i & 1)
            if test(W):
                out.add(W)
        return sorted(out, key=lambda W: (-len(W), sorted(map(str, W)))), True
    if len(br) <= 16:
        out = {frozenset(W) for W in rigid_vertex_sets(E)}
        return sorted(out, key=lambda W: (-len(W), sorted(map(str, W)))), True
    todo = [W for W in cycle_sets(E) if test(W)]
    seen = set(todo)
    while todo:
        W = todo.pop()
        grow = [W | {v} for v in V if v not in W and len(nb[v] & W) >= 2]
        for a in W:                              # paths leaving W and returning
            stack = [(w, [w]) for w in nb[a] if w not in W]
            while stack:
                u, path = stack.pop()
                for w in nb[u]:
                    if w in W and (w != a or len(path) >= 2):
                        grow.append(W | set(path))
                    elif w not in W and w not in path and len(path) < 5:
                        stack.append((w, path + [w]))
        for X in grow:
            X = frozenset(X)
            if X not in seen and test(X):
                seen.add(X)
                todo.append(X)
    return sorted(seen, key=lambda W: (-len(W), sorted(map(str, W)))), False


# ---------------------------------------------------------------- certificates

class Coverage:
    def __init__(self, a):
        self.a = a
        self.memo = {}          # key -> (step, [child keys]) or None
        self.why = {}           # key -> [(step, status, detail)]
        self.info = {}
        self.jjm = {}
        self.ctm = {}
        self.stats = Counter()

    def ginfo(self, key):
        if key not in self.info:
            E = graph(key)
            self.info[key] = {'d2': def_k(E, 3), 'd3': def_k(E, 6)}
        return self.info[key]

    def jj(self, key):
        """Some admissible q with dim L(q) = 3 + def2 (so q in U), or None."""
        if self.a.jj == 'cite':
            return 'cited'
        if key in self.jjm:
            return self.jjm[key]
        E = graph(key)
        V = verts_of(E)
        d2 = self.ginfo(key)['d2']
        res = None
        for t in range(JJ_DRAWS):
            rng = random.Random(f'{SEED}:jj:{name_of(key)}:{t}')
            q = sample_q(rng, V, E, SCALE)
            dL = len(lifting_space(E, V, q))
            assert dL >= 3 + d2, ('(MC-4)(b) fails', name_of(key))
            if dL == 3 + d2:
                res = q
                break
        self.stats['jj certified' if res else 'jj not exhibited'] += 1
        self.jjm[key] = res
        return res

    def orbit(self, Ep, a, b, tag):
        """(orbit, dim U) of X0(G')'s flag pair (a, b) at a certified q in U(G'),
        exact; (None, None) if no q certified in JJ_DRAWS draws."""
        V = verts_of(Ep)
        d2 = def_k(Ep, 3)
        for t in range(JJ_DRAWS):
            rng = random.Random(f'{SEED}:orb:{tag}:{t}')
            q = sample_q(rng, V, Ep, SCALE)
            if len(lifting_space(Ep, V, q)) != 3 + d2:
                continue
            Fb = flex_space(Ep, V, q)
            assert len(Fb) == 3 + d2, 'F(q) != L(q) in dimension (Step MC4)'
            ia, ib = 3 * V.index(a), 3 * V.index(b)
            U = [[v[ia + j] - v[ib + j] for j in range(3)] for v in Fb]
            dU = rank_exact(U) if U else 0
            ha = (q[a][0], q[a][1], F(1))
            hb = (q[b][0], q[b][1], F(1))
            pb_off = any(sum(x * y for x, y in zip(u, hb)) for u in U)   # p_b not in pi_a
            pa_off = any(sum(x * y for x, y in zip(u, ha)) for u in U)   # p_a not in pi_b
            orb = ('iv' if dU == 0 else 'i' if (pa_off and pb_off)
                   else 'ii' if (pa_off or pb_off) else 'iii')
            return orb, dU
        return None, None

    def contract_run(self, E, W, tag):
        """One coreshrink run (relaxed) at (G, W), memoized: (verdict, feats)."""
        if (tag, W) in self.ctm:
            return self.ctm[(tag, W)]
        import coreshrink as CS
        rng = random.Random(f'{SEED}:ct:{tag}')
        ts = (F(1, 10), F(1, 10**4))
        st = {}
        res = None
        for _ in range(5):
            verdict, line, pat, feats = CS.run_member(tag, E, sorted(W, key=str), rng, SCALE,
                                                      'relaxed', ts, st)
            if verdict != 'REDRAW':
                res = (verdict, feats)
                break
        self.ctm[(tag, W)] = res
        return res

    def contract_cert(self, E, W, tag, variant):
        """`variant` 'i': (MC-39) with (i) and (ii) certified.  'core': (MC-39)'s
        last sentence -- (ii) certified and the core rigid at the sampled points
        of B(G) (q(t) in U certified), in place of (i) and X0(H)."""
        r = self.contract_run(E, W, tag)
        if r is None:
            return False, 'five degenerate draws'
        verdict, feats = r
        cf = int(feats['(i) core-free, certified: proj_W L_G(q) = L_H(q|W), q in U(G), q|W in U(H)'])
        nj = int(feats['(ii) no jump: dim ker M0 = dim ker M(t)'])
        certU = 'U-uncertified' not in verdict
        if variant == 'i':
            ok = cf and nj and certU
        else:
            ok = nj and certU and 'core-flexible' not in verdict
        dH, dG = def_k(induced(E, W), 3), def_k(E, 3)
        rel = '= 0' if dH == 0 else '<= def2(G)' if dH <= dG else '> def2(G)'
        self.stats[f'contract{"" if variant == "i" else "*"} {"certified" if ok else "cert failed"} '
                   f'[def2(H) {rel}, cfree={cf}, nojump={nj}]'] += 1
        return bool(ok), ('certified' if ok else
                          f'def2(H)={dH} def2(G)={dG} cfree={cf} nojump={nj} {verdict}')

    # ------------------------------------------------------------ the steps

    def moves(self, key):
        """Yield (step, children, cert) with cert a thunk -> (ok, detail) or None."""
        E = graph(key)
        n = key[0]
        V = list(range(n))
        nb = neighbors(E)
        if is_cycle(E):
            yield 'BASE', [], None
            return
        if is_theta(E):
            yield 'THETA', [], None
        # CUT: a cut vertex z, one component of G - z against the rest
        seen = set()
        for z in V:
            rest = [e for e in E if z not in e]
            comps = components(rest, [v for v in V if v != z])
            if len(comps) < 2:
                continue
            for C in comps:
                E1 = induced(E, C | {z})
                E2 = induced(E, set(V) - C)
                if sum(1 for w in nb[z] if w in C) < 2 or sum(1 for w in nb[z] if w not in C) < 2:
                    continue
                ch = tuple(sorted((key_of(E1), key_of(E2))))
                if ch not in seen:
                    seen.add(ch)
                    yield 'CUT', list(ch), None
        hubs, br = branch_decomposition(E)
        # BRIDGE: a maximal chain of bridges between two hubs
        seen = set()
        for (h1, h2, I) in br:
            if h1 == h2:
                continue
            Ws = set(I)
            rest = [e for e in E if e[0] not in Ws and e[1] not in Ws and
                    not (not I and {e[0], e[1]} == {h1, h2})]
            comps = components(rest, [v for v in V if v not in Ws])
            if len(comps) < 2:
                continue
            assert len(comps) == 2
            ch = tuple(sorted(key_of(induced(rest, C)) for C in comps))
            if ch not in seen:
                seen.add(ch)
                yield 'BRIDGE', list(ch), None
        # EAR
        mode = EAR23[self.a.ear23]
        for bi, (h1, h2, I) in enumerate(br):
            k = len(I)
            if k == 0:
                continue
            Ws = set(I)
            Ep = [e for e in E if e[0] not in Ws and e[1] not in Ws]
            if h1 == h2:
                if len(neighbors(Ep).get(h1, ())) >= 2:
                    yield 'EAR-closed', [key_of(Ep)], None
                continue
            if len(components(Ep)) > 1:
                continue                                   # a bridge path: BRIDGE
            if k >= 5:
                yield 'EAR-k5+', [key_of(Ep)], None
            elif k == 4:
                yield 'EAR-k4', [key_of(Ep), key_of(Ep + ear_edges(h1, h2, 2, n))], None
            elif k in (2, 3) and mode is not None:
                def cert(Ep=Ep, h1=h1, h2=h2, k=k, bi=bi):
                    orb, dU = self.orbit(Ep, h1, h2, f'{name_of(key)}:{bi}')
                    if orb is None:
                        return False, 'no certified q in U(G\')'
                    ok = mode(k, orb, dU)
                    self.stats[f'EAR-k{k} cell (orbit {orb}, dim U {dU}) '
                               f'{"accepted" if ok else "rejected"}'] += 1
                    return ok, f'orbit {orb}, dim U = {dU}'
                yield f'EAR-k{k}', [key_of(Ep), key_of(Ep + ear_edges(h1, h2, k - 1, n))], cert
        # SPLITOFF
        for x in V:
            if len(nb[x]) != 2:
                continue
            a, b = sorted(nb[x])
            if b in nb[a]:
                continue
            Ep = [e for e in E if x not in e]
            vs = [v for v in V if v != x and v != b]
            dlt = def_k(Ep, 6, [v for v in V if v != x]) - def_k(merge_pair(Ep, a, b), 6, vs)
            if dlt < 5:
                continue
            Epp = split_off(E, x, a, b)
            assert def_k(E, 6) - def_k(Epp, 6) == 1, '(MC-29)(a): def3 must rise by [delta >= 5]'
            kp = key_of(Epp)

            def cert(kp=kp):
                return (self.jj(kp) is not None), 'JJ at G\'\''
            yield 'SPLITOFF', [kp], cert
        # FLAT
        gi = self.ginfo(key)
        if gi['d2'] == gi['d3']:
            yield 'FLAT', [], lambda: ((self.jj(key) is not None), 'JJ at G')
        # EAR-k1 at delta = 0 (after FLAT: its certificate costs a flex space)
        if self.a.ear1 == 'delta0':
            for bi, (h1, h2, I) in enumerate(br):
                if len(I) != 1 or h1 == h2:
                    continue
                Ws = set(I)
                Ep = [e for e in E if e[0] not in Ws and e[1] not in Ws]
                if len(components(Ep)) > 1:
                    continue
                dlt = (def_k(Ep, 6, [v for v in V if v not in Ws])
                       - def_k(merge_pair(Ep, h1, h2), 6, [v for v in V if v not in Ws and v != h2]))
                if dlt != 0:
                    continue

                def cert(Ep=Ep, h1=h1, h2=h2, bi=bi):
                    orb, dU = self.orbit(Ep, h1, h2, f'{name_of(key)}:{bi}')
                    if orb is None:
                        return False, 'no certified q in U(G\')'
                    ok = dU >= 2
                    self.stats[f'EAR-k1 delta=0 cell (orbit {orb}, dim U {dU}) '
                               f'{"accepted" if ok else "rejected"}'] += 1
                    return ok, f'delta 0, orbit {orb}, dim U = {dU}'
                yield 'EAR-k1', [key_of(Ep)], cert
        # CONTRACT
        if self.a.contract == 'off' or not is_2ec(E):
            return
        rig, complete = rigid_sets(E)
        if not complete:
            self.stats['rigid-search incomplete'] += 1
        simple = [W for W in rig if not any(len(nb[u] & W) >= 2 for u in set(V) - W)]
        for W in simple:
            ch = [key_of(induced(E, W)), key_of(contraction(E, sorted(W)))]
            tag = f'{name_of(key)}:' + ''.join(map(str, sorted(W)))
            if self.a.contract == 'struct':
                yield 'CONTRACT?', ch, None
            elif n > self.a.cert_nmax:
                yield 'CONTRACT?', ch, lambda: (False, f'n > --cert-nmax {self.a.cert_nmax}')
            else:
                yield 'CONTRACT', ch, (lambda W=W, tag=tag: self.contract_cert(E, W, tag, 'i'))
        if self.a.contract == 'cert-core' and n <= self.a.cert_nmax:
            for W in simple:
                tag = f'{name_of(key)}:' + ''.join(map(str, sorted(W)))
                yield ('CONTRACT*', [key_of(contraction(E, sorted(W)))],
                       (lambda W=W, tag=tag: self.contract_cert(E, W, tag, 'core')))

    def covered(self, key):
        if key in self.memo:
            return self.memo[key] is not None
        why = []
        res = None
        for step, ch, cert in self.moves(key):
            assert all(c[0] < key[0] and satisfies_h(c) for c in ch), \
                ('a step consumed a graph that is not smaller or fails (H)', step)
            bad = [c for c in ch if not self.covered(c)]
            if bad:
                why.append((step, 'child', bad))
                continue
            if cert is not None:
                ok, det = cert()
                if not ok:
                    why.append((step, 'cert', det))
                    continue
            if step == 'CONTRACT?' and self.a.contract != 'struct':
                why.append((step, 'cert', 'uncertified'))
                continue
            res = (step, ch)
            break
        self.memo[key] = res
        self.why[key] = why
        return res is not None

    def terminals(self, key, acc, seen):
        """Terminal uncovered graphs reached from an uncovered `key`."""
        if key in seen or self.covered(key):
            return
        seen.add(key)
        follow = [c for (st, s, d) in self.why[key] if s == 'child' for c in d]
        if not follow:
            acc.add(key)
        for c in follow:
            self.terminals(c, acc, seen)


# ---------------------------------------------------------------- reporting

def certline(cov):
    return ', '.join(f'{k} {v}' for k, v in sorted(cov.stats.items())) or 'none used'


def split_deltas(E):
    """delta = def3(G - x) - def3((G - x)/ab) at every degree-2 x with a !~ b."""
    nb = neighbors(E)
    V = verts_of(E)
    out = []
    for x in V:
        if len(nb[x]) != 2:
            continue
        a, b = sorted(nb[x])
        if b in nb[a]:
            continue
        Ep = [e for e in E if x not in e]
        out.append(def_k(Ep, 6, [v for v in V if v != x])
                   - def_k(merge_pair(Ep, a, b), 6, [v for v in V if v not in (x, b)]))
    return sorted(out)


def describe(cov, key):
    E = graph(key)
    gi = cov.ginfo(key)
    nb = neighbors(E)
    rig, complete = rigid_sets(E)
    hubs, br = branch_decomposition(E)
    ch = []
    for (h1, h2, I) in (br or []):
        if I:
            ch.append(f'{len(I)}{"c" if h1 == h2 else "a" if h2 in nb[h1] else ""}')
    blocks = []
    for st, s, d in cov.why.get(key, []):
        blocks.append(f'{st}:' + (','.join(name_of(c) for c in d) if s == 'child' else d))
    return (f'{name_of(key)} n={key[0]} m={len(E)} def2={gi["d2"]} def3={gi["d3"]} '
            f'rigidset={"Y" if rig else "N"}{"" if complete else "?"} '
            f'deg2={"Y" if any(len(s) == 2 for s in nb.values()) else "N"} '
            f'mindeg={min(len(s) for s in nb.values())} 2cuts={two_edge_cuts(E)} '
            f'chains=[{" ".join(sorted(ch)) or "-"}] splitoff-delta={split_deltas(E) or "-"} | '
            + ('; '.join(blocks) or 'no step applies'))


def run_exh(a, cov):
    t0 = time.time()
    tally = Counter()
    gap = Counter()
    unc = []
    napp0 = 0
    for name, E in two_ec_graphs(a.exh):
        key = key_of(E)
        assert name_of(key) == name
        ok = cov.covered(key)
        step = cov.memo[key][0] if ok else 'UNCOVERED'
        tally[(key[0], step)] += 1
        gi = cov.ginfo(key)
        if gi['d2'] > gi['d3']:
            gap[step] += 1
        if not ok:
            unc.append(key)
            napp0 += not cov.why[key]
    steps = [s for s in ORDER if any(tally[(n, s)] for n in range(3, a.exh + 1))] + ['UNCOVERED']
    print(f'-- exh {a.exh} (ear23={a.ear23}, ear1={a.ear1}, jj={a.jj}, contract={a.contract}): '
          f'first covering step, per n')
    for n in range(3, a.exh + 1):
        print(f'   n={n}: ' + ', '.join(f'{s} {tally[(n, s)]}' for s in steps))
    tot = {s: sum(tally[(n, s)] for n in range(3, a.exh + 1)) for s in steps}
    print('   total: ' + ', '.join(f'{s} {tot[s]}' for s in steps)
          + f'  ({sum(tot.values())} graphs)')
    print(f'   of which def2 > def3 (FLAT cannot apply): ' + ', '.join(
        f'{s} {gap[s]}' for s in steps if gap[s]) + f'  ({sum(gap.values())} graphs)')
    print(f'   uncovered with NO applicable step at all (the hybrid recon\'s REST reading): {napp0}')
    print(f'   certificates: ' + certline(cov))
    if unc:
        print(f'   the {len(unc)} uncovered graphs:')
        for key in unc:
            print('     ' + describe(cov, key))
            if a.list:
                print('       edges', graph(key))
    print(f'-- exh {a.exh}: {time.time() - t0:.0f} s')
    return unc


def run_pool(a, cov, pname):
    import maincomp
    t0 = time.time()
    pop = maincomp.POOLS[pname]()
    pop = pop[::a.stride] if a.stride > 1 else pop
    first = Counter()
    unc = []
    term_all = Counter()
    for nm, E in pop:
        if not (is_simple(E) and is_2ec(E)):
            continue
        key = key_of(E)
        if cov.covered(key):
            first[cov.memo[key][0]] += 1
            continue
        acc = set()
        cov.terminals(key, acc, set())
        unc.append((nm, key, acc))
        for t in acc:
            term_all[t] += 1
    cap = f' [every {a.stride}th member]' if a.stride > 1 else ''
    ncov = sum(first.values())
    print(f'-- pool {pname}{cap} (ear23={a.ear23}, ear1={a.ear1}, jj={a.jj}, contract={a.contract}): '
          f'{ncov + len(unc)} simple 2EC members; covered {ncov} ('
          + ', '.join(f'{s} {first[s]}' for s in ORDER if first[s]) + f'); uncovered {len(unc)}')
    if unc:
        prof = Counter()
        for t in term_all:
            E = graph(t)
            gi = cov.ginfo(t)
            rig, complete = rigid_sets(E)
            _, br = branch_decomposition(E)
            prof[(f'{"no step applies" if not cov.why[t] else "some step fails"}, '
                  f'{"no " if not rig else ""}proper rigid set{"" if complete else "?"}, '
                  f'max chain k = {max((len(I) for _, _, I in br), default=0)}, '
                  f'def3 = {gi["d3"]}, delta <= 4 at every degree-2 vertex: '
                  f'{"yes" if max(split_deltas(E) or [0]) <= 4 else "no"}')] += 1
        print(f'   {len(term_all)} distinct terminal uncovered graphs reached; by structure: '
              + '; '.join(f'{v} x [{k}]' for k, v in sorted(prof.items())))
        print(f'   the most frequent (members reaching it):')
        for t, c in sorted(term_all.items(), key=lambda kv: (-kv[1], kv[0]))[:12]:
            print(f'     {c:>4}  ' + describe(cov, t))
        for nm, key, acc in unc[:a.show]:
            print(f'   uncovered member {nm} ({name_of(key)}): terminals '
                  + ', '.join(name_of(t) for t in sorted(acc)[:8]) + (' ...' if len(acc) > 8 else ''))
    print(f'   certificates: ' + certline(cov))
    print(f'-- pool {pname}: {time.time() - t0:.0f} s')


def run_tree(a, cov, names):
    """The covering tree (or the blocked steps) of named canonical graphs."""
    def show(key, d):
        if d > a.depth:
            return
        ok = cov.covered(key)
        gi = cov.ginfo(key)
        r = cov.memo[key]
        print('   ' + '  ' * d + f'{name_of(key)} n={key[0]} m={len(graph(key))} def2={gi["d2"]} '
              f'def3={gi["d3"]}: ' + (r[0] if ok else 'UNCOVERED'))
        if ok:
            for c in r[1]:
                show(c, d + 1)
        elif d < a.depth:
            print('   ' + '  ' * d + '  ' + describe(cov, key))
    for nm in names:
        n, code = nm[1:].split('_')
        key = (int(n), int(code))
        assert key_of(graph(key)) == key, ('not a canonical name', nm)
        print(f'-- tree {nm} (ear23={a.ear23}, ear1={a.ear1}, jj={a.jj}, contract={a.contract}):')
        show(key, 0)


def necklace(k):
    E = []
    for i in range(k):
        B = [4 * i + j for j in range(4)]
        E += [(B[x], B[y]) for x in range(4) for y in range(x + 1, 4)]
        E.append((B[1], 4 * ((i + 1) % k)))
    return E


def run_necklace(a, cov):
    t0 = time.time()
    for k in range(3, a.necklace + 1):
        E = necklace(k)
        d2, d3 = def_k(E, 3), def_k(E, 6)
        assert (d2, d3) == (k - 3, max(0, k - 6)), ('necklace deficiencies', k, d2, d3)
        nb = neighbors(E)
        for i in range(k):
            W = set(range(4 * i, 4 * i + 4))
            assert def3_pebble(induced(E, W), sorted(W)) == 0
            assert not any(len(nb[u] & W) >= 2 for u in set(range(4 * k)) - W), 'bead G/H not simple'
        key = key_of(E)
        ok = cov.covered(key)
        r = census(f'neck{k}', E, SEED, draws=1, retry=4, want_nondeg=False)
        acc = set()
        if not ok:
            cov.terminals(key, acc, set())
        print(f'N({k}): n={4 * k} m={len(E)} def2={d2} def3={d3} '
              f'covered={cov.memo[key][0] if ok else "NO"}; X0 {"ATTAINS" if r["attains"] else "SHORT"} '
              f'rank={r["rank"]}/{r["target"]} JJ={"Y" if r["JJ"] else "N"} draws={r["draws"]}'
              + (f'; terminals ' + ', '.join(name_of(t) for t in sorted(acc)[:6]) if acc else ''))
        for t in sorted(acc)[:6]:
            print('     ' + describe(cov, t))
    print(f'   certificates: ' + certline(cov))
    print(f'-- necklace {a.necklace}: {time.time() - t0:.0f} s')


def run_flatcore(a):
    """(MC-59)(c): at a proper def2-rigid core W with G/H simple, the t = 0 system of
    coreshrink's family has dim ker M0 = dim L_{G/H}(q') exactly, whenever the rescaled
    core picture delta has dim L_H(delta) = 3; and def2(G) = def2(G/H).  So (ii) holds
    iff dim L_G(q(t)) = dim L_{G/H}(q'), which Jackson-Jordan at G and G/H gives."""
    import coreshrink as CS
    t0 = time.time()
    rng = random.Random(f'{SEED}:flatcore')
    ts = (F(1, 10), F(1, 10**4))
    pop = two_ec_graphs(a.flatcore) + [(f'N({k})', necklace(k)) for k in range(3, 7)]
    ngr = tot = skip = both = 0
    for nm, E in pop:
        V = verts_of(E)
        nb = neighbors(E)
        rig, complete = rigid_sets(E)
        cores = [W for W in rig if def_k(induced(E, W), 3) == 0
                 and not any(len(nb[u] & W) >= 2 for u in set(V) - W)]
        if not cores or not is_2ec(E):
            continue
        ngr += 1
        W = cores[0]                                    # the largest (cap: one per graph)
        Ws = sorted(W, key=str)
        EH = induced(E, W)
        Eq = contraction(E, Ws)
        assert def_k(E, 3) == def_k(Eq, 3), ('def2(G) != def2(G/H) at a def2-rigid core', nm)
        r = CS.recipe(E, Ws, rng, SCALE, 'relaxed', ts)
        dl = r['dl']
        if not CS.admissible(EH, dl) or len(lifting_space(EH, verts_of(EH), dl)) != 3:
            skip += 1
            continue
        qq = dict(r['q'])
        qq['v*'] = (F(0), F(0))
        dQ = len(lifting_space(Eq, verts_of(Eq), qq))
        assert r['dimK0'] == dQ, ('dim ker M0 != dim L_{G/H}(q\')', nm, r['dimK0'], dQ)
        qt = {v: (r['pts'][ts[0]][v][0], r['pts'][ts[0]][v][1]) for v in V}
        dL = len(lifting_space(E, V, qt))
        assert dL == r['d'], ('dim ker M(t) != dim L_G(q(t))', nm)
        tot += 1
        if dL == 3 + def_k(E, 3) and dQ == 3 + def_k(Eq, 3):
            both += 1
            assert r['jet'] == 0, ('a jump at a def2-rigid core with JJ exhibited at G and G/H', nm)
    print(f'--flatcore {a.flatcore}: {ngr} graphs (simple 2EC on <= {a.flatcore} vertices, and '
          f'N(3..6)) with a proper def2-rigid W, G/H simple; the largest such W per graph (a cap). '
          f'dim ker M0 = dim L_G/H(q\') asserted at {tot}/{tot} ({skip} skipped: delta not in U(H)); '
          f'JJ exhibited at G and G/H at {both}, and no jump (ii) at {both}/{both}: OK')
    print(f'-- flatcore: {time.time() - t0:.0f} s')


# The 48 graphs on <= 8 vertices that the hybrid recon's scratch classifier
# (2026-09-24; its step set: cycles, cut vertex / bridge / leaf,
# subdivision, its own ear rule, the flat point; not retained) left with no
# applicable arm.  Named by canonical code; `--round1` re-covers them.
ROUND1_REST = (
    'x6_26977 x6_29315 x7_1714691 x7_1855507 x7_1990787 x7_1992707 x7_1993219 '
    'x8_60101824 x8_63740928 x8_93131968 x8_93195456 x8_188936193 x8_194076675 '
    'x8_206091009 x8_210052544 x8_218500544 x8_218706241 x8_218761354 x8_218769729 '
    'x8_218775571 x8_218777697 x8_218910851 x8_227099666 x8_228082195 x8_239509761 '
    'x8_244066307 x8_244646403 x8_244662787 x8_244916739 x8_252840201 x8_253235219 '
    'x8_253362195 x8_253370499 x8_253372419 x8_253372931 x8_253378579 x8_253513859 '
    'x8_261628035 x8_261693443 x8_261693955 x8_261883907 x8_261898259 x8_261900291 '
    'x8_261906563 x8_261947395 x8_261963779 x8_261971971 x8_261972483').split()


def run_round1(a, cov):
    t0 = time.time()
    assert len(ROUND1_REST) == 48
    tally = Counter()
    for nm in ROUND1_REST:
        n, code = nm[1:].split('_')
        key = (int(n), int(code))
        assert key_of(graph(key)) == key and is_2ec(graph(key)), ('not a canonical 2EC name', nm)
        ok = cov.covered(key)
        tally[cov.memo[key][0] if ok else 'UNCOVERED'] += 1
        if not ok:
            print('   uncovered: ' + describe(cov, key))
    print(f'-- the hybrid recon\'s 48 no-arm graphs (ear23={a.ear23}, ear1={a.ear1}, jj={a.jj}, contract={a.contract}), '
          'first covering step: ' + ', '.join(f'{s} {tally[s]}' for s in ORDER + ('UNCOVERED',)
                                               if tally[s]))
    print(f'-- round1: {time.time() - t0:.0f} s')


# ---------------------------------------------------------------- --lemmas

def point(E, V, q, rng):
    L = lifting_space(E, V, q)
    c = [rng.randint(-SCALE, SCALE) for _ in L]
    z = [sum(ci * b[i] for ci, b in zip(c, L)) for i in range(len(V))]
    return L, {v: (q[v][0], q[v][1], z[i]) for i, v in enumerate(V)}


def proj_rank(L, V, sub):
    idx = [V.index(v) for v in sub]
    return rank_exact([[b[i] for i in idx] for b in L]) if L else 0


def check_glue(tag, G, pieces, extra_d, dL_shift, extra_rank, rng):
    """G is glued from `pieces`; assert the counts and, at 2 points, the
    dimension, surjectivity and rank identities."""
    d3 = def_k(G, 6)
    d2 = def_k(G, 3)
    assert d3 == sum(def_k(P, 6) for P in pieces) + extra_d, (tag, 'def3 count')
    assert d2 == sum(def_k(P, 3) for P in pieces) + extra_d, (tag, 'def2 count')
    V = verts_of(G)
    tgt = 6 * (len(V) - 1) - d3
    assert tgt == sum(6 * (len(verts_of(P)) - 1) - def_k(P, 6) for P in pieces) + extra_rank, \
        (tag, 'targets')
    done = 0
    for _ in range(20):
        if done == 2:
            break
        q = sample_q(rng, V, G, SCALE)
        Vs = [verts_of(P) for P in pieces]
        if not all(all(len(neighbors(P)[v]) < 2 or
                       rank_exact([[F(1), q[w][0], q[w][1]] for w in [v] + sorted(neighbors(P)[v])]) == 3
                       for v in Vp) for P, Vp in zip(pieces, Vs)):
            continue                                   # a piece is not admissible at q|
        done += 1
        L, pt = point(G, V, q, rng)
        ok, info = verify_pencil_witness(G, pt)
        assert ok, (tag, info)
        Ls = [lifting_space(P, Vp, {v: q[v] for v in Vp}) for P, Vp in zip(pieces, Vs)]
        assert len(L) == sum(len(x) for x in Ls) + dL_shift, (tag, 'dim L', len(L), [len(x) for x in Ls])
        for Vp, Lp in zip(Vs, Ls):
            assert proj_rank(L, V, Vp) == len(Lp), (tag, 'restriction not surjective')
        r = rank_modp(build_rigidity(G, pt)[0])
        rs = [rank_modp(build_rigidity(P, {v: pt[v] for v in Vp})[0]) for P, Vp in zip(pieces, Vs)]
        assert r == sum(rs) + extra_rank, (tag, 'rank identity', r, rs)
    assert done == 2, (tag, 'fewer than 2 admissible points in 20 draws')
    return 1


def lemmas():
    from pitch import theta_edges
    C = lambda k: [(i, (i + 1) % k) for i in range(k)]          # noqa: E731
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    K33 = [(a, b) for a in range(3) for b in range(3, 6)]
    base = [('C4', C(4)), ('C5', C(5)), ('K4', K4), ('K33', K33),
            ('th122', theta_edges([1, 2, 2])), ('th223', theta_edges([2, 2, 3]))]
    rng = random.Random(f'{SEED}:lemmas')
    ncut = nbr = nleaf = 0
    for i, (n1, G1) in enumerate(base):
        for n2, G2 in base[i:]:
            A = [(('A', u), ('A', w)) for u, w in G1]
            B = [(('B', u), ('B', w)) for u, w in G2]
            zA, zB = verts_of(A)[0], verts_of(B)[-1]
            Bz = [tuple(zA if x == zB else x for x in e) for e in B]
            ncut += check_glue(f'cut {n1}.{n2}', A + Bz, [A, Bz], 0, -3, 0, rng)
            for k in range(4):
                path = [zA] + [('P', j) for j in range(k)] + [zB]
                G = A + B + list(zip(path, path[1:]))
                shift = {0: -2, 1: -1}.get(k, k - 2)
                nbr += check_glue(f'bridge{k} {n1}.{n2}', G, [A, B], k + 1, shift, 5 * (k + 1), rng)
        # the leaf lemma: a pendant vertex at a hub-to-be u (deg_G(u) >= 3)
        A = [(('A', u), ('A', w)) for u, w in G1]
        G = A + [(verts_of(A)[0], 'leaf')]
        d3, d3p = def_k(G, 6), def_k(A, 6)
        assert d3 == d3p + 1 and def_k(G, 3) == def_k(A, 3) + 1, ('leaf counts', n1)
        V, VA = verts_of(G), verts_of(A)
        q = sample_q(rng, V, G, SCALE)
        L, pt = point(G, V, q, rng)
        LA = lifting_space(A, VA, {v: q[v] for v in VA})
        assert len(L) == len(LA) and proj_rank(L, V, VA) == len(LA), ('leaf L', n1)
        r = rank_modp(build_rigidity(G, pt)[0])
        rA = rank_modp(build_rigidity(A, {v: pt[v] for v in VA})[0])
        assert r == rA + 5, ('leaf rank', n1, r, rA)
        nleaf += 1
    print(f'--lemmas: cut-vertex {ncut}/{ncut}, bridge path (k = 0..3) {nbr}/{nbr}, leaf '
          f'{nleaf}/{nleaf} glued instances, 2 points each (leaf: 1); every count, dimension, '
          f'surjectivity and rank identity asserted: OK')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lemmas', action='store_true')
    ap.add_argument('--exh', type=int, default=0)
    ap.add_argument('--pool', type=str, default='')
    ap.add_argument('--necklace', type=int, default=0)
    ap.add_argument('--ear23', choices=sorted(EAR23), default='none')
    ap.add_argument('--ear1', choices=('delta0', 'none'), default='delta0')
    ap.add_argument('--jj', choices=('cert', 'cite'), default='cert')
    ap.add_argument('--contract', choices=('cert', 'cert-core', 'struct', 'off'), default='cert')
    ap.add_argument('--cert-nmax', type=int, default=40)
    ap.add_argument('--stride', type=int, default=1)
    ap.add_argument('--show', type=int, default=5)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--tree', type=str, default='')
    ap.add_argument('--depth', type=int, default=99)
    ap.add_argument('--round1', action='store_true')
    ap.add_argument('--flatcore', type=int, default=0)
    a = ap.parse_args()
    print(f'x0arms.py seed {SEED}')
    if not (a.lemmas or a.exh or a.pool or a.necklace or a.tree or a.round1 or a.flatcore):
        ap.error('name a mode')
    if a.lemmas:
        t0 = time.time()
        lemmas()
        print(f'-- lemmas: {time.time() - t0:.0f} s')
    if a.flatcore:
        run_flatcore(a)
    # a fresh memo per mode and per pool, so each block's certificate counts
    # do not depend on what else is on the command line
    if a.exh:
        run_exh(a, Coverage(a))
    for p in [p for p in a.pool.split(',') if p]:
        run_pool(a, Coverage(a), p)
    if a.necklace:
        run_necklace(a, Coverage(a))
    if a.tree:
        run_tree(a, Coverage(a), a.tree.split(','))
    if a.round1:
        run_round1(a, Coverage(a))


if __name__ == '__main__':
    main()
